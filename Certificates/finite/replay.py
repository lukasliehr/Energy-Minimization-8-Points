#!/usr/bin/env python3
"""Replay declarative eight-point finite certificates with one fixed checker.

The manifest supplies exact cell parameters, witness hashes and checker hashes.
This runner derives and audits the mathematical dimensions independently. It
does not read historical run state, acceptance records or another verifier.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
import hashlib
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys
import time


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def read_json(path):
    def invalid(value):
        raise ValueError("Nonfinite JSON constant: " + value)

    return json.loads(Path(path).read_text(), parse_constant=invalid)


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, allow_nan=False) + "\n")


def digest(path):
    value = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            value.update(block)
    return value.hexdigest()


def rational(value):
    require(isinstance(value, str), "Exact parameters must be rational strings")
    return Fraction(value)


def finite(value):
    return type(value) in (int, float) and math.isfinite(value)


def vector(value, length):
    return (
        isinstance(value, list)
        and len(value) == length
        and all(finite(x) for x in value)
    )


def matrix(value, rows, columns):
    import numpy as np
    if isinstance(value, np.ndarray):
        return value.shape == (rows, columns) and value.dtype == np.float64 and bool(np.isfinite(value).all())
    return (
        isinstance(value, list)
        and len(value) == rows
        and all(vector(row, columns) for row in value)
    )


def exact_union(cells):
    intervals = []
    for cell in cells:
        center, width = rational(cell["center"]), rational(cell["halfwidth"])
        lower, upper = max(Fraction(0), center - width), center + width
        require(lower <= upper, "Cell has no nonnegative points")
        intervals.append((lower, upper))
    merged = []
    for lower, upper in sorted(intervals):
        if merged and lower <= merged[-1][1]:
            merged[-1][1] = max(merged[-1][1], upper)
        else:
            merged.append([lower, upper])
    return [[str(x) for x in pair] for pair in merged]


def dimensions(cell):
    degree, order = cell["degree"], cell["order"]
    require(
        type(degree) is int and degree in range(12, 21, 2),
        "Unsupported polynomial degree",
    )
    require(type(order) is int and 4 <= order <= 20, "Unsupported Taylor order")
    half = degree // 2
    orders = list(range(half, 0, -1)) + [
        math.comb(k + 3, 3) - 21 for k in [half, half - 1, half - 2]
    ]
    coefficients = sum(
        1
        for i in range(degree + 1)
        for j in range(i, degree + 1)
        for k in range(j, degree + 1)
        if i + j + k <= degree
    )
    return {
        "orders": orders,
        "coefficient_rows": coefficients,
        "retained_rows": coefficients - 2,
        "svec_dimension": sum(n * (n + 1) // 2 for n in orders),
    }


def parameters(cell):
    center, width = rational(cell["center"]), rational(cell["halfwidth"])
    require(width > 0 and center + width >= 0, "Invalid closed cell")
    profile, balance = cell["profile"], cell["balance"]
    require(
        profile in ["original", "far4", "far6", "general"], "Unknown Hermite profile"
    )
    require(balance in ["unit", "riesz"], "Unknown target multiplier")
    if profile != "general":
        require(cell["degree"] == 12, "Legacy profiles require degree twelve")
    if balance == "riesz":
        require(
            center > 0 and center - width > 0, "Riesz balance requires a positive cell"
        )
    mode = (
        "entire"
        if center - width <= 0 <= center + width
        or -4 < center - width <= center + width < 4
        else "quotient"
    )
    return {
        "potential_evaluation": mode,
        "target_multiplier": (
            "1" if balance == "unit" else "(s/center)*(3/2)^((s-center)/2)"
        ),
    }


def witness_audit(data, cell, dims):
    degree = cell["degree"]
    half = degree // 2
    require(data.get("degree") == degree, "Witness degree mismatch")
    orders = dims["orders"]
    records = data["basis_records"]
    require(
        [r["name"] for r in records]
        == [f"F{k}" for k in range(half)] + ["M0", "M1", "Mdet"],
        "Wrong block order",
    )
    require([len(r["free"]) for r in records] == orders, "Wrong reduced matrix orders")
    require(
        all(matrix(r["change_of_basis"], n, n) for r, n in zip(records, orders)),
        "Basis changes must be finite square matrices",
    )
    preconditioners = data["PSD_preconditioners"]
    require(
        len(preconditioners) == len(orders)
        and all(matrix(p, n, n) for p, n in zip(preconditioners, orders)),
        "PSD preconditioners must be finite square matrices",
    )
    n, retained = dims["svec_dimension"], dims["retained_rows"]
    require(
        vector(data["svec_center"], n) and matrix(data["right_inverse"], n, retained),
        "Correction arrays have wrong shape or nonfinite entries",
    )
    left = data.get("left_preconditioner")
    require(
        left is None or matrix(left, retained, retained), "Invalid left preconditioner"
    )
    rows = data["rows"]
    require(
        isinstance(rows, list)
        and len(rows) == retained
        and len(set(rows)) == retained
        and all(type(i) is int and 0 <= i < dims["coefficient_rows"] for i in rows),
        "Invalid retained coefficient rows",
    )
    # A witness is an approximate inverse/Gram proposal, reusable on another
    # cell. Optional search center/order annotations impose no premise: the
    # fresh uniform checker always reconstructs the manifest's actual cell.
    if cell["profile"] == "general":
        tags = data["auxiliary_nodes"]
        require(
            isinstance(tags, list)
            and len(tags) == half - 4
            and all(t in ["A", "B", "C", "D"] for t in tags),
            "Invalid auxiliary nodes",
        )
    else:
        tags = {"original": [], "far4": ["B", "D"], "far6": ["B", "B"]}[cell["profile"]]
    multiplicities = {t: 2 + 2 * tags.count(t) for t in "ABCD"}
    multiplicities["minus_one"] = 5 if cell["profile"] == "original" else 1
    require(sum(multiplicities.values()) == degree + 1, "Wrong interpolation dimension")
    return {
        "auxiliary_nodes": tags,
        "hermite_multiplicities": multiplicities,
        "left_preconditioned": left is not None,
    }


def report_audit(path, cell, dims, metadata):
    report = read_json(path)
    require(report.get("passed") is True, "Verifier did not report passed=true")
    expected = {
        "degree": cell["degree"],
        "order": cell["order"],
        "minorant": cell["profile"],
        "coefficient_rows": dims["coefficient_rows"],
        "selected_rows": dims["retained_rows"],
        "svec_dimension": dims["svec_dimension"],
        "coefficient_mode": "streamed",
        **parameters(cell),
        **metadata,
    }
    for key, value in expected.items():
        require(report.get(key) == value, "Report mismatch: " + key)
    for key in ["center", "halfwidth"]:
        require(rational(report[key]) == rational(cell[key]), "Report cell drift")
    errors = report["PSD_uniform_errors"]
    require(
        isinstance(errors, list)
        and len(errors) == len(dims["orders"])
        and all(finite(x) and 0 <= x < 1 for x in errors),
        "Invalid strict PSD bounds",
    )
    for key in ["F0_basis_change_inverse_error", "right_inverse_uniform_residual"]:
        require(
            finite(report[key]) and 0 <= report[key] < 1,
            "Invalid strict inverse bound: " + key,
        )
    for key in [
        "inverse_polynomial_norm_upper",
        "solution_residual_upper",
        "solution_error_upper",
    ]:
        require(
            finite(report[key]) and report[key] >= 0, "Invalid correction bound: " + key
        )
    match = re.fullmatch(
        r"\[\s*([^,\[\]]+)\s*,\s*([^,\[\]]+)\s*\]", report["root"]["a_enclosure"]
    )
    require(match is not None, "Unrecognized exact root enclosure")
    lower, upper = map(Fraction, match.groups())
    require(0 < lower <= upper < Fraction(1, 3), "Root is outside the physical range")
    exclusions = report["forbidden_triples"]
    require(
        len(exclusions) == 3
        and {tuple(x["type"]) for x in exclusions} == {(0, 0, 0), (0, 0, 2), (0, 0, 3)},
        "Wrong forbidden equality triples",
    )
    require(
        all(
            finite(x["absolute_lower_bound"])
            and x["absolute_lower_bound"] > 0
            and type(x["component"]) is int
            and 0 <= x["component"] < dims["orders"][cell["degree"] // 2]
            for x in exclusions
        ),
        "Invalid strict equality exclusion",
    )
    return {
        "maximum_PSD_uniform_error": max(errors),
        "right_inverse_uniform_residual": report["right_inverse_uniform_residual"],
        "physical_height": [str(lower), str(upper)],
    }


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def source_hashes():
    return {str(p.relative_to(HERE)): digest(p)
            for p in sorted(HERE.rglob('*.py'))}


def clean_environment():
    env = dict(os.environ)
    for name in list(env):
        if name.startswith('N8_') or name in ('PYTHONOPTIMIZE', 'PYTHONPATH'):
            env.pop(name)
    env.update(PYTHONDONTWRITEBYTECODE='1', OPENBLAS_NUM_THREADS='1',
               OMP_NUM_THREADS='1', MKL_NUM_THREADS='1', BLIS_NUM_THREADS='1',
               NUMEXPR_NUM_THREADS='1', N8_COEFFICIENT_MODE='streamed',
               N8_ROW_CHUNK='32', N8_EXACT_MM_BITS='112',
               N8_EXACT_SCALAR_BITS='384', N8_ROW_WORKERS='6')
    return env


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--jobs', type=int, choices=range(1, 65), default=4)
    parser.add_argument('--cell', action='append', default=[])
    args = parser.parse_args()
    require(__debug__ and sys.flags.optimize == 0, 'Run Python without -O')
    manifest_path = HERE / 'cells.json'
    manifest_hash = digest(manifest_path)
    manifest = read_json(manifest_path)
    require(manifest['schema_version'] == 'eight-point-cells-v2', 'Unknown manifest schema')
    cells = manifest['cells']
    require(len(cells) == 111, 'Incomplete cell registry')
    ids = [c['id'] for c in cells]
    require(len(set(ids)) == len(ids) and all(isinstance(i, str) and
            re.fullmatch('[A-Za-z0-9_-]+', i) for i in ids), 'Invalid cell identifiers')
    for cell in cells:
        dimensions(cell)
        parameters(cell)
    require(exact_union(cells) == manifest['expected_closed_nonnegative_union']
            == [['0', '124']], 'Wrong exact finite union')
    if args.cell:
        require(len(set(args.cell)) == len(args.cell) and set(args.cell) <= set(ids),
                'Invalid pilot selection')
        cells = [c for c in cells if c['id'] in args.cell]
    sources = source_hashes()
    require(sources == manifest['checker_sha256'], 'Checker source binding mismatch')
    run = args.output.resolve()
    run.mkdir(parents=True, exist_ok=False)
    env = clean_environment()
    write_json(run / 'INPUTS.json', {'manifest_sha256': manifest_hash,
               'checker_sha256': sources, 'cells': cells,
               'matrix_bits': 112, 'scalar_bits': 384, 'row_workers': 6, 'python': sys.version})

    def replay(cell):
        folder = run / cell['id']
        folder.mkdir()
        asset = cell['witness']
        source = (ROOT / asset['path']).resolve()
        require(source.is_relative_to((ROOT / 'certificates/finite').resolve()),
                'Witness path outside certificate directory')
        require(asset['compression'] == 'capd1-xz', 'Unsupported encoding')
        require(digest(source) == asset['compressed_sha256'], 'Witness hash mismatch')
        spec = folder / 'CELL.json'
        write_json(spec, cell)
        report = folder / 'verified.json'
        log = folder / 'verify.log'
        with log.open('w') as stream:
            process = subprocess.run([sys.executable, '-B', '-u',
                str(HERE / 'verify_cell.py'), str(spec), str(report)],
                env=env, stdout=stream, stderr=subprocess.STDOUT)
        require(process.returncode == 0, 'Arithmetic verifier failed: ' + str(log))
        expanded = read_json(folder / 'EXPANSION.json')
        dims = dimensions(cell)
        bounds = report_audit(report, cell, dims, expanded['metadata'])
        require(expanded['source_sha256'] == asset['compressed_sha256']
                and expanded['semantic_sha256'] == asset['semantic_sha256'],
                'Worker input mismatch')
        require(read_json(spec) == cell and digest(source) == asset['compressed_sha256']
                and source_hashes() == sources, 'Inputs changed during replay')
        result = {'id': cell['id'], 'status': 'PASS', 'cell': cell,
                  'dimensions': dims, 'metadata': expanded['metadata'], 'bounds': bounds,
                  'report_file': str(report.relative_to(run)), 'report_sha256': digest(report),
                  'expansion_file': str((folder / 'EXPANSION.json').relative_to(run)),
                  'expansion_sha256': digest(folder / 'EXPANSION.json')}
        write_json(folder / 'AUDIT.json', result)
        print('PASS', cell['id'], bounds['maximum_PSD_uniform_error'], flush=True)
        return result

    def safe(cell):
        try:
            return replay(cell)
        except Exception as exc:
            print('FAIL', cell['id'], repr(exc), flush=True)
            return {'id': cell['id'], 'status': 'FAIL', 'cell': cell, 'error': repr(exc)}

    started = time.monotonic()
    # Start the most expensive cells first to avoid a long final serial tail.
    scheduled = sorted(cells, key=lambda c: (c['degree'], c['order']), reverse=True)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(safe, scheduled))
    results.sort(key=lambda r: ids.index(r['id']))
    unchanged = digest(manifest_path) == manifest_hash and source_hashes() == sources
    passed = unchanged and all(r['status'] == 'PASS' for r in results)
    union = exact_union([r['cell'] for r in results if r['status'] == 'PASS'])
    if not args.cell:
        passed = passed and union == [['0', '124']]
    status = ('PASS_PILOT_REPLAY' if args.cell else 'PASS_COMPLETE_FINITE_REPLAY') if passed else 'INCOMPLETE'
    summary = {'status': status, 'arithmetic': 'exact-integer-enclosures',
               'manifest_sha256': manifest_hash, 'checker_sha256': sources,
               'inputs_unchanged': unchanged, 'closed_nonnegative_union': union,
               'results': results, 'elapsed_seconds': time.monotonic() - started,
               'scope': 'Exact computational obligations on the stated exponent intervals. Not Lean verified.'}
    write_json(run / 'SUMMARY.json', summary)
    print(status, union, flush=True)
    require(passed, 'Replay incomplete')


if __name__ == '__main__':
    main()
