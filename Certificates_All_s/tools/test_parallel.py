#!/usr/bin/env python3
"""Small source-bound comparison of serial/vector and fork/vector arithmetic.

This is an integration test, not a cell certificate. It uses only the compact
asset shipped with the package and never modifies the checker sources.
"""
import argparse
from fractions import Fraction
import hashlib
import json
import multiprocessing
import os
from pathlib import Path
import platform
import sys
import time

if not __debug__ or sys.flags.optimize:
    raise RuntimeError("Run Python without -O")
sys.dont_write_bytecode = True


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def snapshot(package):
    paths = sorted((package / "finite/kernel").glob("*.py"))
    paths += [package / "finite/replay.py", package / "finite/verify_cell.py"]
    return {str(path.relative_to(package)): digest(path) for path in paths}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package", type=Path,
                        default=Path(__file__).resolve().parents[1])
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--workers", type=int, default=2, choices=range(1, 7))
    parser.add_argument("--degree", type=int, default=12, choices=[12, 14, 16, 18, 20])
    parser.add_argument("--order", type=int, default=4, choices=range(4, 9))
    parser.add_argument("--rows", type=int, default=12)
    parser.add_argument("--chunk", type=int, default=4, choices=range(1, 65))
    args = parser.parse_args()
    package = args.package.resolve()
    if args.output.exists():
        raise RuntimeError("Use a new output report path")
    if "fork" not in multiprocessing.get_all_start_methods():
        raise RuntimeError("This optional parallel integration test requires fork")
    before = snapshot(package)
    tool_before = digest(__file__)
    manifest_path = package / "finite/cells.json"
    manifest_hash = digest(manifest_path)
    manifest = json.loads(manifest_path.read_text())
    cell = next(c for c in manifest["cells"] if c["degree"] == args.degree)
    if not args.workers * args.chunk <= args.rows <= 24:
        raise ValueError("Use enough rows for all workers and at most 24 test rows")
    center = cell["center"]
    halfwidth = str(min(Fraction(cell["halfwidth"]), Fraction(1, 1000)))
    os.environ.update(OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1",
                      N8_DEG_HALF=str(args.degree // 2), N8_TAYLOR_ORDER=str(args.order),
                      N8_ROW_CHUNK=str(args.chunk), N8_ROW_WORKERS="1",
                      N8_TARGET_BALANCE=cell["balance"])
    sys.path.insert(0, str(package / "finite"))
    sys.path.insert(0, str(package / "finite/kernel"))
    import numpy as np
    import mpmath as mp
    from threadpoolctl import threadpool_limits, threadpool_info
    from replay import dimensions, witness_audit
    from interval_arithmetic import I
    from ipoly import IP
    import codec
    import recipe
    import structure
    import build_models as build
    from verify_interval import correction_models_streamed
    import parallel_chunks

    asset = cell["witness"]
    source = (package / asset["path"]).resolve()
    if not source.is_relative_to((package / "certificates/finite").resolve()):
        raise RuntimeError("Witness path leaves the compact asset directory")
    if digest(source) != asset["compressed_sha256"]:
        raise RuntimeError("Compact witness byte hash mismatch")

    def clone(model):
        return IP([I(c.lo, c.hi) for c in model.c],
                  I(model.e.lo, model.e.hi), model.mp0)

    def same(a, b):
        if len(a.c) != len(b.c):
            return False
        return all(x.shape == y.shape and
                   np.array_equal(x.view(np.uint64), y.view(np.uint64))
                   for u, v in zip(a.c + [a.e], b.c + [b.e])
                   for x, y in [(u.lo, v.lo), (u.hi, v.hi)])

    def model_hash(model):
        value = hashlib.sha256()
        for part in model.c + [model.e]:
            for array in (part.lo, part.hi):
                value.update(str(array.shape).encode("ascii"))
                value.update(array.astype("<f8", copy=False).tobytes(order="C"))
        return value.hexdigest()

    started = time.monotonic()
    mp.mp.dps = 100
    with threadpool_limits(limits=1):
        record = codec.load(source, asset["semantic_sha256"], limits=codec.RECIPE_LIMITS)
        record, expansion = recipe.expand_record(record, structure)
        witness_audit(record, cell, dimensions(cell))
        _, _, _, rec, data, bases, target = build.build(center, halfwidth, record, cell["profile"])
        indices, slices = structure.vectorization_layout([base.mp0 for base in bases])
        rows = np.asarray(rec["rows"][:args.rows])
        C = I(np.asarray(rec["right_inverse"])[:, :args.rows])
        center_vector = np.asarray(rec["svec_center"])
        target_model = IP.fromMT(target).slice(list(rows), [0])
        block = structure.D
        inputs = ([data[block]], [bases[block]], rows, [indices[block]],
                  [slices[block]], C, center_vector)
        begun = time.monotonic()
        serial = correction_models_streamed(*inputs, clone(target_model))
        serial_seconds = time.monotonic() - begun
        begun = time.monotonic()
        parallel = parallel_chunks.correction_models_parallel(
            *inputs, clone(target_model), workers=args.workers,
            allow_test_degree=args.degree not in (18, 20))
        parallel_seconds = time.monotonic() - begun
        if not all(same(a, b) for a, b in zip(serial, parallel)):
            raise ArithmeticError("Serial/fork interval endpoint bit mismatch")
        worker_pids = {entry["pid"] for entry in parallel_chunks.LAST_DIAGNOSTICS}
        if len(worker_pids) != args.workers:
            raise ArithmeticError("Test did not exercise every requested worker")
        vector_module = sys.modules.get("vector_dyadic")
        if vector_module is None or Path(vector_module.__file__).resolve() != package / "finite/kernel/vector_dyadic.py":
            raise RuntimeError("The package vector endpoint backend was not loaded")
        pools = [{key: value for key, value in pool.items() if key != "filepath"}
                 for pool in threadpool_info()]
    if snapshot(package) != before or digest(__file__) != tool_before:
        raise RuntimeError("Test or finite checker sources changed during execution")
    if digest(manifest_path) != manifest_hash or digest(source) != asset["compressed_sha256"]:
        raise RuntimeError("Manifest or witness changed during execution")
    report = {
        "status": "PASS_COMBINED_VECTOR_FORK_EQUIVALENCE",
        "scope": f"D{args.degree}/order{args.order}/M0/{args.rows} rows/chunk{args.chunk} at center{center}, halfwidth{halfwidth}; integration test, not a cell certificate",
        "cell": cell["id"], "degree": args.degree, "order": args.order,
        "rows": args.rows, "chunk": args.chunk,
        "distinct_worker_count": len(worker_pids),
        "workers": args.workers, "serial_seconds": serial_seconds,
        "parallel_seconds": parallel_seconds,
        "elapsed_seconds": time.monotonic() - started,
        "coefficient_endpoint_bits_identical": True,
        "remainder_endpoint_bits_identical": True,
        "serial_model_sha256": [model_hash(x) for x in serial],
        "parallel_model_sha256": [model_hash(x) for x in parallel],
        "source_sha256": before, "test_sha256": tool_before,
        "manifest_sha256": manifest_hash,
        "witness_compressed_sha256": asset["compressed_sha256"],
        "witness_semantic_sha256": asset["semantic_sha256"],
        "proposal_expansion": expansion,
        "python": platform.python_version(), "platform": platform.platform(),
        "threadpools": pools, "worker_diagnostics": parallel_chunks.LAST_DIAGNOSTICS,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False) + "\n")
    print(json.dumps(report, sort_keys=True, allow_nan=False), flush=True)


if __name__ == "__main__":
    main()
