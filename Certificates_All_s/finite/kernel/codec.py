#!/usr/bin/env python3
"""CAPD1: deterministic, lossless JSON-value codec with exact binary64 arrays.

The compressor is transport only. Decoding never rounds a witness number.
"""
from array import array
from dataclasses import dataclass
import hashlib
import lzma
import math
import os
import struct
import sys

MAGIC = b"CAPD1\x00"
MAX_ELEMENTS = 100_000_000


@dataclass(frozen=True)
class Limits:
    """All limits are caller-selected upper bounds, independent of input data."""
    max_bytes: int = 256_000_000
    max_elements: int = 32_000_000
    max_depth: int = 64
    max_string_bytes: int = 1_000_000


RECIPE_LIMITS = Limits(max_bytes=32_000_000, max_elements=4_000_000,
                       max_depth=32, max_string_bytes=16_384)


class Budget:
    def __init__(self, limits):
        self.limits = limits
        self.remaining_elements = limits.max_elements

    def consume(self, count):
        require(0 <= count <= self.remaining_elements, "Decoded element budget exceeded")
        self.remaining_elements -= count


class BoundedReader:
    def __init__(self, stream, limit):
        self.stream = stream
        self.remaining_bytes = limit

    def read(self, count):
        require(0 <= count <= self.remaining_bytes, "Decoded byte budget exceeded")
        data = self.stream.read(count)
        self.remaining_bytes -= len(data)
        return data


class XZReader:
    """One checked XZ stream, with bounded dictionary and output allocations."""
    def __init__(self, stream):
        self.stream = stream
        self.decoder = lzma.LZMADecompressor(format=lzma.FORMAT_XZ,
                                            memlimit=64 * 1024 * 1024)

    def read(self, count):
        require(count >= 0, "Unbounded reads are forbidden")
        output = bytearray()
        while len(output) < count:
            if self.decoder.eof:
                require(self.decoder.check == lzma.CHECK_CRC64, "XZ requires CRC64")
                require(not self.decoder.unused_data and self.stream.read(1) == b"",
                        "Trailing compressed data")
                break
            if self.decoder.needs_input:
                data = self.stream.read(64 * 1024)
                require(bool(data), "Truncated XZ stream")
            else:
                data = b""
            output.extend(self.decoder.decompress(data, max_length=count - len(output)))
        return bytes(output)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def nat(value):
    require(type(value) is int and value >= 0, "Invalid natural number")
    out = bytearray()
    while value >= 128:
        out.append((value & 127) | 128)
        value >>= 7
    out.append(value)
    return bytes(out)


def exact_read(stream, size):
    require(0 <= size <= 8 * MAX_ELEMENTS, "Oversized data block")
    data = stream.read(size)
    require(len(data) == size, "Truncated CAPD1 input")
    return data


def read_nat(stream):
    value = shift = 0
    while True:
        b = exact_read(stream, 1)[0]
        value |= (b & 127) << shift
        if b < 128:
            require(shift == 0 or b != 0, "Noncanonical natural number")
            return value
        shift += 7
        require(shift <= 4096, "Oversized integer")


def float_shape(value):
    """Identify rectangular, nonempty arrays whose leaves are all floats."""
    if type(value) is not list or not value:
        return None
    if type(value[0]) is float:
        return (len(value),) if all(type(x) is float for x in value) else None
    if type(value[0]) is not list:
        return None
    sub = float_shape(value[0])
    if sub is None or any(float_shape(x) != sub for x in value[1:]):
        return None
    return (len(value),) + sub


def flattened(value, rank):
    if rank == 1:
        yield from value
    else:
        for part in value:
            yield from flattened(part, rank - 1)


def emit(value, write):
    kind = type(value)
    if value is None:
        write(b"n")
    elif kind is bool:
        write(b"t" if value else b"f")
    elif kind is int:
        write(b"i" + nat(2 * value if value >= 0 else -2 * value - 1))
    elif kind is float:
        require(math.isfinite(value), "Nonfinite witness number")
        write(b"d" + struct.pack("<d", value))
    elif kind is str:
        data = value.encode("utf-8")
        write(b"s" + nat(len(data)))
        write(data)
    elif kind is list:
        shape = float_shape(value)
        if shape is None:
            write(b"l" + nat(len(value)))
            for item in value:
                emit(item, write)
        else:
            require(len(shape) <= 8, "Excessive array rank")
            floats = array("d", flattened(value, len(shape)))
            require(len(floats) <= MAX_ELEMENTS, "Oversized array")
            require(all(math.isfinite(x) for x in floats), "Nonfinite array number")
            if sys.byteorder != "little":
                floats.byteswap()
            data = floats.tobytes()
            write(b"a" + nat(len(shape)) + b"".join(nat(x) for x in shape))
            for plane in range(8):
                write(data[plane::8])
    elif kind is dict:
        require(all(type(k) is str for k in value), "Object keys must be strings")
        write(b"o" + nat(len(value)))
        for key in sorted(value):
            emit(key, write)
            emit(value[key], write)
    else:
        raise ValueError("Unsupported JSON type")


def reshape(values, shape):
    iterator = iter(values)
    def build(axis):
        if axis == len(shape) - 1:
            return [next(iterator) for _ in range(shape[axis])]
        return [build(axis + 1) for _ in range(shape[axis])]
    return build(0)


def receive(stream, depth=0, budget=None):
    if budget is None:
        budget = Budget(Limits())
    require(depth <= budget.limits.max_depth, "Excessive nesting")
    budget.consume(1)
    tag = exact_read(stream, 1)
    if tag == b"n":
        return None
    if tag == b"t":
        return True
    if tag == b"f":
        return False
    if tag == b"i":
        number = read_nat(stream)
        return number // 2 if number % 2 == 0 else -(number // 2) - 1
    if tag == b"d":
        value = struct.unpack("<d", exact_read(stream, 8))[0]
        require(math.isfinite(value), "Nonfinite scalar")
        return value
    if tag == b"s":
        count = read_nat(stream)
        require(count <= budget.limits.max_string_bytes, "Oversized string")
        return exact_read(stream, count).decode("utf-8")
    if tag in (b"l", b"o"):
        count = read_nat(stream)
        require(count <= budget.remaining_elements, "Oversized container")
        if tag == b"l":
            return [receive(stream, depth + 1, budget) for _ in range(count)]
        out = {}
        previous = None
        for _ in range(count):
            key = receive(stream, depth + 1, budget)
            require(type(key) is str, "Invalid object key")
            require(previous is None or previous < key, "Unsorted or duplicate key")
            out[key] = receive(stream, depth + 1, budget)
            previous = key
        return out
    if tag == b"a":
        rank = read_nat(stream)
        require(1 <= rank <= 8, "Invalid array rank")
        shape = tuple(read_nat(stream) for _ in range(rank))
        count = math.prod(shape)
        require(all(x > 0 for x in shape), "Empty numeric array")
        require(count <= MAX_ELEMENTS, "Oversized array")
        require(depth + rank <= budget.limits.max_depth, "Excessive array nesting")
        budget.consume(count + sum(math.prod(shape[:i]) for i in range(1, rank)))
        data = bytearray(count * 8)
        for plane in range(8):
            data[plane::8] = exact_read(stream, count)
        values = array("d")
        values.frombytes(data)
        if sys.byteorder != "little":
            values.byteswap()
        require(all(math.isfinite(x) for x in values), "Nonfinite array")
        return reshape(values, shape)
    raise ValueError("Unknown CAPD1 tag")


def semantic_sha256(value):
    """Hash canonical types, keys, array shapes, integers and float bits."""
    digest = hashlib.sha256(MAGIC)
    emit(value, digest.update)
    return digest.hexdigest()


def dump(value, path, preset=6):
    digest = hashlib.sha256()
    size = 0
    with lzma.open(path, "wb", format=lzma.FORMAT_XZ, check=lzma.CHECK_CRC64,
                   preset=preset) as stream:
        def write(data):
            nonlocal size
            digest.update(data)
            size += len(data)
            stream.write(data)
        write(MAGIC)
        emit(value, write)
    return {"semantic_sha256": digest.hexdigest(), "uncompressed_codec_bytes": size}


def load(path, expected_semantic_sha256=None, *, limits=Limits()):
    with open(path, "rb") as source:
        require(os.fstat(source.fileno()).st_size <= limits.max_bytes + 1_000_000,
                "Compressed file exceeds byte budget")
        stream = XZReader(source)
        bounded = BoundedReader(stream, limits.max_bytes)
        require(exact_read(bounded, len(MAGIC)) == MAGIC, "Wrong CAPD1 magic")
        value = receive(bounded, budget=Budget(limits))
        require(stream.read(1) == b"", "Trailing CAPD1 bytes")
    if expected_semantic_sha256 is not None:
        require(semantic_sha256(value) == expected_semantic_sha256,
                "Decoded semantic hash mismatch")
    return value
