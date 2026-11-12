"""Exact small Fourier/tensor certificate for a whole-ball signed-mean bound.
No optimizer, numerical linear algebra, network, or global-tail coverage claim.
"""

from pathlib import Path
from fractions import Fraction as F
from itertools import combinations_with_replacement, permutations
import sys, json, hashlib, importlib.util, time

if not __debug__:
    raise SystemExit("Run without -O")
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
helper = ROOT / "rational_intervals.py"
pins = {
    "rational_intervals.py": "077134414d464f6e9017b734ce80342497b216dfb354e1feb8ac7b04577163a6"
}
for name, digest in pins.items():
    assert sha(ROOT / name) == digest
spec = importlib.util.spec_from_file_location("wholeball_intervals", helper)
iv = importlib.util.module_from_spec(spec)
spec.loader.exec_module(iv)
I, sqrt, ser = iv.I, iv.sqrt_interval, iv.serialize
start = time.perf_counter()
checks = {}
values = {}


def ck(name, test):
    if name in checks:
        raise RuntimeError("Repeated check")
    checks[name] = bool(test)
    if not test:
        raise ArithmeticError(name)


def dot(x, y):
    return sum((a * b for a, b in zip(x, y)), I(0))


rt = sqrt(2)
a = (2 * rt - 1) / 7
h = sqrt(a)
r = sqrt(1 - a)
kap = 1 + 1 / rt
W = 16 + 4 * rt
lam0 = F(413, 100)
tensor_bound = F(3)
B_bound = F(4)
D_bound = F(231, 100)
cs = [I(1), rt / 2, I(0), -rt / 2, I(-1), -rt / 2, I(0), rt / 2]
sn = [I(0), rt / 2, I(1), rt / 2, I(0), -rt / 2, I(-1), -rt / 2]
sg = [(-1) ** i for i in range(8)]
P = [[r * cs[i], r * sn[i], sg[i] * h] for i in range(8)]
fr = [[[-sn[i], cs[i], I(0)], [-h * cs[i], -h * sn[i], sg[i] * r]] for i in range(8)]
K = [[a * 2 * (kap + 1) if i == j else I(0) for j in range(8)] for i in range(8)]
for i in range(8):
    for j in range(8):
        if (i - j) % 8 in (1, 7):
            K[i][j] = I(-1)
        if (i - j) % 8 in (2, 6):
            K[i][j] = -kap
B = [
    [K[i][j] * dot(fr[i][k], P[j]) for j in range(8)]
    for i in range(8)
    for k in range(2)
]
# Explicit orthonormal real eigenbasis of the block-circulant Htt.
# Columns indexed by frequency, eigenvalue sign, and cosine/sine phase.
V = []
eig = []
labels = []
fiber_values = []
for k in range(5):
    co = cs[k]
    si = sn[k]
    co2 = cs[(2 * k) % 8]
    si2 = sn[(2 * k) % 8]
    tt = rt - rt * co
    mm = rt + (2 - (2 + rt) * a) * co - 2 * (1 + a) * co2
    bb = 2 * h * (rt * si / 2 + kap * si2)
    ek = 2 * r * (rt * si / 2 + kap * si2)
    fk = 2 * h * r * ((1 + rt / 2) * co - kap * co2)
    dk = 2 * a * (kap + 1 - co - kap * co2)
    ck("B_mode_" + str(k), (ek * ek + fk * fk).hi < B_bound * B_bound)
    ck("D_mode_" + str(k), dk.hi < D_bound)
    fiber_values.append({"k": k, "B_squared": ser(ek * ek + fk * fk), "D": ser(dk)})
    if k in (0, 4):
        for coordinate, ev in [(0, tt), (1, mm)]:
            vec = [I(0) for _ in range(16)]
            for j in range(8):
                vec[2 * j + coordinate] = cs[(k * j) % 8] / sqrt(8)
            V.append(vec)
            eig.append(ev)
            labels.append([k, coordinate])
    else:
        discr = sqrt((tt - mm) ** 2 + 4 * bb * bb)
        for sign in (-1, 1):
            ev = (tt + mm + sign * discr) / 2
            ec = [bb, ev - tt]
            norm = sqrt(ec[0] ** 2 + ec[1] ** 2)
            ck("eigenvector_normalizer_" + str(k) + "_" + str(sign), norm.lo > 0)
            ec = [x / norm for x in ec]
            for phase in (0, 1):
                vec = []
                for j in range(8):
                    c, s = cs[(k * j) % 8], sn[(k * j) % 8]
                    uv = [-s / 2, c / 2] if phase == 0 else [c / 2, s / 2]
                    vec.extend([ec[0] * uv[0], ec[1] * uv[1]])
                V.append(vec)
                eig.append(ev)
                labels.append([k, sign, phase])
ck("sixteen_basis_vectors", len(V) == 16)
gap = [I(lam0) - e for e in eig]
for i, g in enumerate(gap):
    ck("positive_gap_" + str(i), g.lo > 0)
rootgap = [sqrt(g) for g in gap]
# Diagnostic enclosure consistency; exact orthonormality follows analytically
# from trigonometric orthogonality and each real symmetric 2x2 eigenproblem.
orth = []
for i in range(16):
    for j in range(i, 16):
        z = dot(V[i], V[j]) - int(i == j)
        ck("orthogonality_enclosure_" + str(i) + "_" + str(j), z.lo <= 0 <= z.hi)
        orth.append(max(abs(z.lo), abs(z.hi)))
Bbar = [
    [sum((V[i][j] * B[j][n] for j in range(16)), I(0)) for n in range(8)]
    for i in range(16)
]
Q = [
    [
        [
            V[j][2 * n] * V[k][2 * n] + V[j][2 * n + 1] * V[k][2 * n + 1]
            for k in range(16)
        ]
        for j in range(16)
    ]
    for n in range(8)
]
# U_ijk=3*T_ijk/(gap_i+gap_j+gap_k); T is the fully symmetric
# coefficient tensor for C(q)=-q^T B (|q_i|^2)_i.
U = {}
for i, j, k in combinations_with_replacement(range(16), 3):
    num = -sum(
        (
            Bbar[i][n] * Q[n][j][k] + Bbar[j][n] * Q[n][i][k] + Bbar[k][n] * Q[n][i][j]
            for n in range(8)
        ),
        I(0),
    )
    u = num / (gap[i] + gap[j] + gap[k])
    for key in set(permutations((i, j, k))):
        U[key] = u
ck("complete_symmetric_tensor", len(U) == 16**3)
# N_i,jk=sqrt(gap_i)*U_ijk. Ordered (j,k) tensor coordinates use
# ordinary Euclidean norm; sum j<=k with weight2 off diagonal is exact.
Gram = [[I(0) for _ in range(16)] for _ in range(16)]
for i in range(16):
    for l in range(i, 16):
        z = sum(
            (
                (1 if j == k else 2) * U[i, j, k] * U[l, j, k]
                for j in range(16)
                for k in range(j, 16)
            ),
            I(0),
        )
        Gram[i][l] = Gram[l][i] = rootgap[i] * rootgap[l] * z
M = [
    [I(tensor_bound if i == j else 0) - Gram[i][j] for j in range(16)]
    for i in range(16)
]
pivots = []
for k in range(16):
    d = M[k][k]
    ck("tensor_Gram_LDL_" + str(k), d.lo > 0)
    pivots.append(ser(d))
    for i in range(k + 1, 16):
        for j in range(i, 16):
            M[i][j] = M[j][i] = M[i][j] - M[i][k] * M[j][k] / d
print("Exact tensor Gram passed", flush=True)
for name, R, eta in [("full_chart", F(3, 10), F(99, 500))]:
    den = (1 + sqrt(1 - I(R * R))) ** 2
    upper = (
        I(lam0) + tensor_bound * I(R * R) / 4 + (B_bound * R + D_bound) * I(R * R) / den
    )
    coefficient = upper / W
    ck(name + "_eta", coefficient.hi < eta)
    values[name] = {
        "radius": str(R),
        "mean_numerator_upper": ser(upper),
        "mean_eta": ser(coefficient),
        "rounded_eta": str(eta),
        "margin": ser(I(eta) - coefficient),
    }
for name, digest in pins.items():
    ck("unchanged_" + name, sha(ROOT / name) == digest)
report = {
    "status": "PASS_WHOLE_BALL_MEAN_SUBLEMMA_ONLY",
    "no_global_coverage_claim": True,
    "checks": checks,
    "number_of_checks": len(checks),
    "constants": {
        "lambda0": str(lam0),
        "tensor_norm_squared": str(tensor_bound),
        "B_norm_upper": str(B_bound),
        "D_eigen_upper": str(D_bound),
    },
    "values": values,
    "basis_labels": labels,
    "eigenvalue_enclosures": [ser(x) for x in eig],
    "tensor_Gram_LDL_pivots": pivots,
    "minimum_pivot_lower": str(min(F(z["lower_rational"]) for z in pivots)),
    "orthogonality_max_endpoint_width": str(max(orth)),
    "fiber_bounds": fiber_values,
    "source_sha256": sha(Path(__file__)),
    "dependencies_sha256": pins,
    "elapsed_seconds": time.perf_counter() - start,
}
out = Path(__file__).with_suffix(".json")
if out.exists():
    raise SystemExit("Refuse report overwrite")
out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(
    json.dumps(
        {
            "status": report["status"],
            "checks": len(checks),
            "seconds": report["elapsed_seconds"],
            "min_pivot": report["minimum_pivot_lower"],
            "values": values,
            "source_sha256": report["source_sha256"],
            "report_sha256": sha(out),
        },
        indent=2,
    )
)
