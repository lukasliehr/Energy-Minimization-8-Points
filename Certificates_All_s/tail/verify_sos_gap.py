"""Exact quartic SOS certificate for a stronger global packing separation.

The only numerical inputs are proposed rational matrices. Their positivity
and the exact coefficient identity are established here by integer arithmetic
and outward Fraction intervals. No optimizer is imported.
"""

from pathlib import Path
import json, hashlib, itertools, sys, time

sys.dont_write_bytecode = True
from exact_geometry import *

if not __debug__:
    raise SystemExit("Run without -O")
t0 = time.time()
wp = Path(sys.argv[1])
rec = json.loads(wp.read_text())
assert rec["kind"] == "quartic_annulus_packing_gap"
b = F(rec["b"])
rho = F(rec["rho"])
h0 = F(rec["higher"])
den = rec["denominator"]
assert rho == F(3, 10) and h0 == F(11, 50) and 0 < b < F(3, 100)
assert type(den) is int and den > 0
g = geometry(rec["pivots"])
n = 13
mon1 = [()] + [(i,) for i in range(n)]
mon2 = mon1 + list(itertools.combinations_with_replacement(range(n), 2))
mons = (
    mon2
    + list(itertools.combinations_with_replacement(range(n), 3))
    + list(itertools.combinations_with_replacement(range(n), 4))
)
idx = {m: i for i, m in enumerate(mons)}
a = g["a"]
h = a * rho * rho / (4 * (1 - rho * rho)) + sqrt(2 * (1 - a * a)) * rho / (
    1 + sqrt(1 - rho * rho)
)
assert h.hi < h0
ineq = []
for e in range(16):
    pol = {(): I(b)}
    for i in range(n):
        pol[i,] = rho * g["R"][e][i]
    for i in range(n):
        for j in range(i, n):
            pol[i, j] = (
                rho
                * rho
                * (g["M"][e][i][j] + h0 * g["T"][e][i][j])
                * (1 if i == j else 2)
            )
    ineq.append(pol)
ineq += [
    {(): I(1), **{(i, i): I(-1) for i in range(n)}},
    {(): I(-(1 - rho * rho / 4)), **{(i, i): I(1) for i in range(n)}},
]
assert len(rec["matrices"]) == 19


def imul(A, B):
    return [[sum(x * y for x, y in zip(ar, bc)) for bc in zip(*B)] for ar in A]


def gram_poly(nums, mon):
    pol = {}
    for i, u in enumerate(mon):
        for j, v in enumerate(mon):
            key = tuple(sorted(u + v))
            pol[key] = pol.get(key, 0) + nums[i][j]
    return {k: F(v, den) for k, v in pol.items()}


def check_matrix(m, dim):
    nums = m["gram_numerators"]
    P = m["preconditioner_numerators"]
    assert len(nums) == dim and len(P) == dim
    assert all(
        len(r) == dim and all(type(x) is int for x in r) for A in [nums, P] for r in A
    )
    assert all(nums[i][j] == nums[j][i] for i in range(dim) for j in range(dim))
    PP = imul(imul(P, nums), list(map(list, zip(*P))))
    den3 = den**3
    defect = F(
        max(
            sum(abs(PP[i][j] - (den3 if i == j else 0)) for j in range(dim))
            for i in range(dim)
        ),
        den3,
    )
    assert defect < F(1, 100)
    rn = F(max(sum(abs(x) for x in r) for r in P), den)
    cn = F(max(sum(abs(P[i][j]) for i in range(dim)) for j in range(dim)), den)
    return nums, defect, rn, cn


validated = []
for i, m in enumerate(rec["matrices"]):
    validated.append(check_matrix(m, len(mon2) if i == 0 else len(mon1)))
target = [I(0) for _ in mons]
target[0] = I(-1)
for (nums, _, _, _), pol in zip(validated[1:], ineq):
    sigma = gram_poly(nums, mon1)
    for u, c in sigma.items():
        for v, d in pol.items():
            target[idx[tuple(sorted(u + v))]] -= c * d
q0, defect, rn, cn = validated[0]
qpoly = gram_poly(q0, mon2)
residual = [target[i] - qpoly.get(m, 0) for i, m in enumerate(mons)]
counts = [0 for m in mons]
for u in mon2:
    for v in mon2:
        counts[idx[tuple(sorted(u + v))]] += 1
assert all(c > 0 for c in counts)
entry_bound = max(max(abs(r.lo), abs(r.hi)) / c for r, c in zip(residual, counts))
correction = rn * cn * len(mon2) * entry_bound
assert defect + correction < 1
assert b < (2 * (F(3, 10) - a)).lo
out = {
    "status": "PASS_GLOBAL_PACKING_GAP_SUBLEMMA_ONLY",
    "constants": {
        "gap": str(b),
        "orbit_radius": str(rho),
        "higher_remainder": str(h0),
        "sphere_norm_squared_lower": str(1 - rho * rho / 4),
    },
    "dimensions": {
        "variables": 13,
        "free_sos_matrix": len(mon2),
        "nonnegative_multipliers": 18,
        "multiplier_matrix": len(mon1),
        "coefficient_identity_count": len(mons),
    },
    "positive_gram_congruence_defects": [str(z[1]) for z in validated],
    "free_matrix_coefficient_correction_entry_bound": str(entry_bound),
    "free_matrix_congruence_correction_bound": str(correction),
    "free_matrix_total_defect": str(defect + correction),
    "conclusion": "Every configuration with product Euclidean distance at least 3/10 from the packing congruence orbit has some squared pair distance < tau-gap. Uses the accepted contact-minimal packing classification for the exterior interior alternative.",
    "witness_sha256": hashlib.sha256(wp.read_bytes()).hexdigest(),
    "source_sha256": {
        p.name: hashlib.sha256(p.read_bytes()).hexdigest()
        for p in [Path(__file__), Path(__file__).with_name("exact_geometry.py"), HELPER]
    },
    "runtime_seconds_diagnostic": time.time() - t0,
}
outpath = wp.with_suffix(".verified.json")
outpath.write_text(json.dumps(out, indent=2) + "\n")
print(
    out["status"],
    "b",
    str(b),
    "total_defect",
    str(defect + correction),
    "seconds",
    time.time() - t0,
    flush=True,
)
