"""Exact interval verification of a nonlinear contact variance sublemma.
No floating point, optimizer, or accepted exponent coverage change.
"""

from pathlib import Path
import json, hashlib, itertools, sys, time

sys.dont_write_bytecode = True
from exact_geometry import *

if not __debug__:
    raise SystemExit("Run without -O")
t0 = time.time()
here = Path(__file__).parent
wp = here / "variance_witness.json"
rec = json.loads(wp.read_text())
g = geometry(rec["pivots"])
n = 13
mu0 = F(rec["mu0"])
B = F(rec["tensor_bound"])
den = rec["denominator"]
nums = rec["U_numerators"]
assert mu0 == F(37, 10) and B == F(528, 25) and type(den) is int and den > 0
assert len(nums) == n and all(
    len(x) == n and all(len(y) == n and all(type(z) is int for z in y) for y in x)
    for x in nums
)
assert all(
    nums[i][j][k] == nums[i][k][j] == nums[j][i][k] == nums[k][j][i]
    for i in range(n)
    for j in range(n)
    for k in range(n)
)
U = [[[F(nums[i][j][k], den) for k in range(n)] for j in range(n)] for i in range(n)]
A = [[g["G"][i][j] - (mu0 if i == j else 0) for j in range(n)] for i in range(n)]
apiv = ldl(A)
AI = inv(A)
GU = [
    [
        F(
            sum(nums[i][j][k] * nums[l][j][k] for j in range(n) for k in range(n)),
            den**2,
        )
        for l in range(n)
    ]
    for i in range(n)
]
BA = [[B * AI[i][j] - GU[i][j] for j in range(n)] for i in range(n)]
bpiv = ldl(BA)
coeff = {key: I(0) for key in itertools.combinations_with_replacement(range(n), 3)}
for i in range(n):
    for j in range(n):
        for k in range(n):
            actual = 2 * sum(
                (g["w"][e] * g["R"][e][i] * g["M"][e][j][k] for e in range(16)), I(0)
            )
            reconstructed = sum((A[i][l] * U[l][j][k] for l in range(n)), I(0))
            coeff[tuple(sorted((i, j, k)))] += actual - reconstructed
error = sum(max(abs(x.lo), abs(x.hi)) for x in coeff.values())
epsilon = F(1, 10000000)
assert error < epsilon
rho = F(3, 10)
h0 = F(11, 50)
a = g["a"]
W = g["W"]
h = a * rho * rho / (4 * (1 - rho * rho)) + sqrt(2 * (1 - a * a)) * rho / (
    1 + sqrt(1 - rho * rho)
)
assert h.hi < h0
# Recheck the small original spectral/error ingredients directly in this basis.
weighted_mu = F(59546, 15625)
weighted_piv = ldl(
    [
        [g["G"][i][j] - (weighted_mu if i == j else 0) for j in range(n)]
        for i in range(n)
    ]
)
G_unweighted = mm(tr(g["R"]), g["R"])
unweighted_piv = ldl(
    [[G_unweighted[i][j] - (3 if i == j else 0) for j in range(n)] for i in range(n)]
)
Mbar = [
    [
        sum((g["w"][e] * g["M"][e][i][j] / g["W"] for e in range(16)), I(0))
        for j in range(n)
    ]
    for i in range(n)
]
centered = [
    [[g["M"][e][i][j] - Mbar[i][j] for j in range(n)] for i in range(n)]
    for e in range(16)
]
squares = [mm(M, M) for M in centered]
error_piv = ldl(
    [
        [
            I(4 if i == j else 0)
            - sum((g["w"][e] * squares[e][i][j] for e in range(16)), I(0))
            for j in range(n)
        ]
        for i in range(n)
    ]
)
out = {
    "status": "PASS_VARIANCE_SUBLEMMA_ONLY",
    "constants": {
        "mu0": str(mu0),
        "tensor_bound": str(B),
        "quartic_penalty": str(B / 4),
        "cubic_residual_allowance": str(epsilon),
        "radius": str(rho),
        "higher_remainder": str(h0),
        "weighted_spectral_lower": str(weighted_mu),
        "unweighted_spectral_lower": "3",
        "centered_quadratic_norm_bound": "2",
    },
    "verified_cubic_residual_upper": str(error),
    "weighted_spectral_pivots": [ser(x) for x in weighted_piv],
    "unweighted_spectral_pivots": [ser(x) for x in unweighted_piv],
    "centered_quadratic_pivots": [ser(x) for x in error_piv],
    "A_positive_pivots": [ser(x) for x in apiv],
    "tensor_positive_pivots": [ser(x) for x in bpiv],
    "derivation": "For q in V, r<=3/10, centered contact-difference norm >= sqrt((37/10)*r^2-(132/25)*r^4-10^(-7)*r^3)-(11/50)*sqrt(W/4)*r^2, whenever the radicand is nonnegative.",
    "witness_sha256": hashlib.sha256(wp.read_bytes()).hexdigest(),
    "source_sha256": {
        p.name: hashlib.sha256(p.read_bytes()).hexdigest()
        for p in [Path(__file__), here / "exact_geometry.py", HELPER]
    },
    "runtime_seconds_diagnostic": time.time() - t0,
}
(here / "verify_variance.json").write_text(json.dumps(out, indent=2) + "\n")
print(out["status"], "residual", str(error), "seconds", time.time() - t0, flush=True)
