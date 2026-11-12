#!/usr/bin/env python3
"""Reproduce CAPD1 transport tests without modifying certificate inputs."""
import argparse
import hashlib
import io
import lzma
import json
import math
from pathlib import Path
import random
import struct
import tempfile
import sys

sys.dont_write_bytecode = True
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--kernel", type=Path,
    default=Path(__file__).resolve().parents[1] / "finite" / "kernel")
args = parser.parse_args()
sys.path.insert(0, str(args.kernel.resolve()))
import codec


def json_digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"),
                                    allow_nan=False).encode()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def expect_rejection(data):
    try:
        codec.receive(io.BytesIO(data))
    except (ValueError, UnicodeError, EOFError):
        return
    raise RuntimeError("Malformed input was accepted")


def main():
    rng = random.Random(20260918)
    floats = [-0.0, 0.0, 1.0, -1.0, math.ulp(0.0), -math.ulp(0.0),
              float.fromhex("0x1.fffffffffffffp+1023")]
    while len(floats) < 4096:
        f = struct.unpack("<d", rng.getrandbits(64).to_bytes(8, "little"))[0]
        if math.isfinite(f):
            floats.append(f)
    values = [None, True, False, 0, -1, 1 << 300, -(1 << 300), "λ\nα", {}, [],
              [0, 0.0, False, -0.0], {"array": floats, "degree": 20},
              [[1.0, -0.0], [math.ulp(0.0), 2.0]],
              [[[1.0], [2.0]], [[3.0], [4.0]]],
              {"rectangular": [[1.0], [2.0, 3.0]], "list": ["x", None]},
              {"z": -0.0, "a": {"y": 1.0, "x": 1}}]
    with tempfile.TemporaryDirectory() as folder:
        for i, value in enumerate(values):
            path = Path(folder) / str(i)
            expected = codec.semantic_sha256(value)
            info = codec.dump(value, path)
            result = codec.load(path, expected)
            require(info["semantic_sha256"] == expected, "Encoded semantic hash mismatch")
            require(codec.semantic_sha256(result) == expected, "Decoded semantic hash mismatch")
            require(json_digest(result) == json_digest(value), "Canonical JSON mismatch")
            if type(value) is dict and "array" in value:
                require([struct.pack("<d", x) for x in value["array"]] == [
                    struct.pack("<d", x) for x in result["array"]], "Float bits changed")
        resource_checks = [
            ([1.0] * 10, codec.Limits(max_elements=5)),
            ([1.0] * 10, codec.Limits(max_bytes=8)),
            ([[[1.0]]], codec.Limits(max_depth=2)),
            ("abc", codec.Limits(max_string_bytes=2)),
        ]
        for value, limits in resource_checks:
            path = Path(folder) / "resource"
            codec.dump(value, path)
            try:
                codec.load(path, limits=limits)
            except ValueError:
                pass
            else:
                raise RuntimeError("Resource bound was ignored")
        raw = codec.MAGIC + b"n"
        invalid_containers = [
            lzma.compress(raw) + b"trailing",
            lzma.compress(raw) + lzma.compress(raw),
            lzma.compress(raw)[:-3],
            lzma.compress(raw + b"n"),
            lzma.compress(raw, preset=9),
            lzma.compress(raw, check=lzma.CHECK_NONE),
            lzma.compress(raw, check=lzma.CHECK_CRC32),
        ]
        for data in invalid_containers:
            path = Path(folder) / "invalid_container"
            path.write_bytes(data)
            try:
                codec.load(path)
            except (ValueError, lzma.LZMAError):
                pass
            else:
                raise RuntimeError("Invalid/oversized XZ container was accepted")
    bad = [b"", b"?", b"i\x80\x00", b"a\x00", b"a\x01\x00", b"a\x09",
           b"d" + struct.pack("<d", float("inf")), b"s\x01\xff",
           b"o\x02s\x01xns\x01xn", b"o\x01in", b"l\x01",
           b"a\x01\x01" + struct.pack("<d", float("nan"))]
    for data in bad:
        expect_rejection(data)
    print(json.dumps({"schema_version": "eight-point-codec-tests-v1", "status": "PASS",
           "test_script": "tools/test_codec.py",
           "test_source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           "decoder": "finite/kernel/codec.py",
           "decoder_sha256": hashlib.sha256(Path(codec.__file__).read_bytes()).hexdigest(),
           "certificate_inputs_modified": False, "valid_examples": len(values),
           "finite_random_and_edge_float_bits": len(floats),
           "malformed_examples_rejected": len(bad),
           "resource_limits_checked": len(resource_checks),
           "invalid_or_oversized_xz_containers_rejected": len(invalid_containers)}))


if __name__ == "__main__":
    main()
