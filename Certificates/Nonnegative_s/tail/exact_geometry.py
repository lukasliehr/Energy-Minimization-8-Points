"""Exact outward interval geometry for new tail research certificates.

The graph chart, weights and frames are those of the frozen tail proof.
The basis is defined exactly by Gram-Schmidt, not by floating coordinates.
"""

from pathlib import Path
import importlib.util, hashlib
from fractions import Fraction as F

ROOT = Path(__file__).resolve().parent
HELPER = ROOT / "rational_intervals.py"
HELPER_SHA = "077134414d464f6e9017b734ce80342497b216dfb354e1feb8ac7b04577163a6"
assert hashlib.sha256(HELPER.read_bytes()).hexdigest() == HELPER_SHA
spec = importlib.util.spec_from_file_location("exact_tail_intervals", HELPER)
iv = importlib.util.module_from_spec(spec)
spec.loader.exec_module(iv)
I = iv.I
sqrt = iv.sqrt_interval
exp = iv.exp_interval
log = iv.log_interval
ser = iv.serialize


def dot(x, y):
    return sum((a * b for a, b in zip(x, y)), I(0))


def tr(A):
    return list(map(list, zip(*A)))


def mm(A, B):
    return [[dot(ar, bc) for bc in tr(B)] for ar in A]


def eye(n):
    return [[I(int(i == j)) for j in range(n)] for i in range(n)]


def inv(A):
    n = len(A)
    M = [row[:] + erow for row, erow in zip(A, eye(n))]
    for k in range(n):
        p = M[k][k]
        assert p.lo > 0
        M[k] = [x / p for x in M[k]]
        M[k][k] = I(1)
        for i in range(n):
            if i == k:
                continue
            f = M[i][k]
            M[i] = [x - f * y for x, y in zip(M[i], M[k])]
            M[i][k] = I(0)
    return [row[n:] for row in M]


def ldl(A):
    M = [r[:] for r in A]
    piv = []
    for k in range(len(A)):
        d = M[k][k]
        assert d.lo > 0, (k, ser(d))
        piv.append(d)
        for i in range(k + 1, len(A)):
            for j in range(i, len(A)):
                M[i][j] = M[j][i] = M[i][j] - M[i][k] * M[j][k] / d
    return piv


def geometry(pivots):
    rt = sqrt(2)
    a = (2 * rt - 1) / 7
    h = sqrt(a)
    r = sqrt(1 - a)
    kap = 1 + 1 / rt
    W = 8 * (kap + 1)
    cs = [I(1), rt / 2, I(0), -rt / 2, I(-1), -rt / 2, I(0), rt / 2]
    sn = [I(0), rt / 2, I(1), rt / 2, I(0), -rt / 2, I(-1), -rt / 2]
    sg = [(-1) ** i for i in range(8)]
    P = [[r * cs[i], r * sn[i], sg[i] * h] for i in range(8)]
    frames = [
        [[-sn[i], cs[i], I(0)], [-h * cs[i], -h * sn[i], sg[i] * r]] for i in range(8)
    ]

    def cross(x, y):
        return [
            x[1] * y[2] - x[2] * y[1],
            x[2] * y[0] - x[0] * y[2],
            x[0] * y[1] - x[1] * y[0],
        ]

    Z = [
        [dot(frames[i][k], cross(e, P[i])) for e in eye(3)]
        for i in range(8)
        for k in range(2)
    ]
    Prot = mm(mm(Z, inv(mm(tr(Z), Z))), tr(Z))
    Pi = [[I(int(i == j)) - Prot[i][j] for j in range(16)] for i in range(16)]
    cols = []
    assert (
        len(pivots) == 13
        and len(set(pivots)) == 13
        and all(0 <= i < 16 for i in pivots)
    )
    for j in pivots:
        v = [Pi[i][j] for i in range(16)]
        for u in cols:
            c = dot(u, v)
            v = [x - c * y for x, y in zip(v, u)]
        n = sqrt(dot(v, v))
        assert n.lo > 0
        cols.append([x / n for x in v])
    V = tr(cols)
    # Orthogonality and rotation consistency are diagnostics. The exact identities
    # follow from orthogonal projection and the defining Gram-Schmidt operations.
    for i in range(13):
        for j in range(13):
            e = dot(cols[i], cols[j]) - int(i == j)
            assert e.lo <= 0 <= e.hi and e.hi - e.lo < F(1, 10**35)
    for i in range(3):
        for j in range(13):
            e = dot(tr(Z)[i], cols[j])
            assert e.lo <= 0 <= e.hi and e.hi - e.lo < F(1, 10**35)
    edges = [(i, j) for i in range(8) for j in range(i + 1, 8) if j - i in [1, 2, 6, 7]]
    w = [kap if sg[i] == sg[j] else I(1) for i, j in edges]
    R0 = [[I(0) for _ in range(16)] for e in edges]
    M = []
    T = []
    for e, (i, j) in enumerate(edges):
        E = [[I(0) for _ in range(16)] for _ in range(16)]
        Inc = [[I(0) for _ in range(16)] for _ in range(16)]
        for k in range(2):
            R0[e][2 * i + k] = -2 * dot(P[j], frames[i][k])
            R0[e][2 * j + k] = -2 * dot(P[i], frames[j][k])
            E[2 * i + k][2 * i + k] = a
            E[2 * j + k][2 * j + k] = a
            Inc[2 * i + k][2 * i + k] = I(1)
            Inc[2 * j + k][2 * j + k] = I(1)
            for l in range(2):
                E[2 * i + k][2 * j + l] = E[2 * j + l][2 * i + k] = -dot(
                    frames[i][k], frames[j][l]
                )
        M.append(mm(mm(tr(V), E), V))
        T.append(mm(mm(tr(V), Inc), V))
    R = mm(R0, V)
    G = mm(tr(R), [[ww * x for x in row] for ww, row in zip(w, R)])
    return dict(
        rt=rt,
        a=a,
        tau=2 * (1 - a),
        kap=kap,
        W=W,
        P=P,
        frames=frames,
        Z=Z,
        Pi=Pi,
        V=V,
        edges=edges,
        w=w,
        R=R,
        M=M,
        T=T,
        G=G,
    )
