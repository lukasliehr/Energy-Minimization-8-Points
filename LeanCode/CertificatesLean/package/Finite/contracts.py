"""Structural and acceptance contracts for the analytically reduced finite proof.

The required positivity and coefficient-correction contracts are retained.
The forbidden-triangle acceptance gate is removed by the analytic equality
theorem using the first and third vertex moments. Historical stronger
reports remain admissible without making their redundant fields premises.
"""
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import re


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
    # The reduced equality theorem needs only vertex moments 1 and 3.
    # Older stronger reports may contain forbidden_triples; those fields
    # are no longer read or accepted as mathematical prerequisites.
    return {
        "maximum_PSD_uniform_error": max(errors),
        "right_inverse_uniform_residual": report["right_inverse_uniform_residual"],
        "physical_height": [str(lower), str(upper)],
    }
