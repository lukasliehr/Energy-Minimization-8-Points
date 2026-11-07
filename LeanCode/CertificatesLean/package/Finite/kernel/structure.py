"""Exact three-point polynomial data and a high-precision residual enclosure.
No numerical optimization or fixed-exponent theorem is invoked by this module.
"""

import itertools, math, numpy as np, mpmath as mp

from exact_iv import iv
import os

N = 8
D = int(os.environ.get("N8_DEG_HALF", "7"))
assert 6 <= D <= 10
Z = (0, 0, 0)
ONE = {Z: 1}
V = [{tuple(int(i == j) for i in range(3)): 1} for j in range(3)]


def add(a, b, c=1):
    out = a.copy()
    for e, v in b.items():
        out[e] = out.get(e, 0) + c * v
    return {e: v for e, v in out.items() if v}


def scl(a, c):
    return {e: v * c for e, v in a.items() if v * c}


def mul(a, b):
    out = {}
    for e, v in a.items():
        for f, w in b.items():
            k = tuple(x + y for x, y in zip(e, f))
            out[k] = out.get(k, 0) + v * w
    return {e: v for e, v in out.items() if v}


def sym6(a):
    out = {}
    for p in itertools.permutations(range(3)):
        for e, v in a.items():
            k = tuple(e[j] for j in p)
            out[k] = out.get(k, 0) + v
    return {e: v for e, v in out.items() if v}


def subs_equal(a, axis):
    out = {}
    for e, v in a.items():
        k = tuple(e[0] + e[1] if j == axis else 0 for j in range(3))
        out[k] = out.get(k, 0) + v
    return {e: v for e, v in out.items() if v}


def monoms(d):
    return [e for e in itertools.product(range(d + 1), repeat=3) if sum(e) <= d]


EXPS = [e for e in monoms(2 * D) if tuple(sorted(e)) == e]
EINDEX = {e: j for j, e in enumerate(EXPS)}
TRIP_TYPES = [(3, 3, 0), (3, 1, 2), (3, 2, 0), (1, 0, 0), (2, 2, 0)]
TRIP_COUNTS = [8, 16, 16, 8, 8]
TRIP_ALL = sorted(set(p for tt in TRIP_TYPES for p in itertools.permutations(tt)))
PAIR_COUNTS = [8, 4, 8, 8]
assert len(EXPS) == len(set(EXPS)) and sum(TRIP_COUNTS) == 56 and len(TRIP_ALL) == 21


def raw_data():
    qbase = add(V[2], mul(V[0], V[1]), -1)
    aa = mul(add(ONE, mul(V[0], V[0]), -1), add(ONE, mul(V[1], V[1]), -1))
    Q = [ONE, qbase]
    for k in range(2, D + 1):
        Q.append(add(scl(mul(qbase, Q[-1]), 2), mul(aa, Q[-2]), -1))
    data = []
    for k in range(D):
        m = D - k + 1
        raw = np.zeros((len(EXPS), m, m), dtype=np.int64)
        S = [[None] * m for _ in range(m)]
        for i in range(m):
            for j in range(m):
                p = sym6(mul({(i, j, 0): 1}, Q[k]))
                S[i][j] = p
                r = scl(p, N - 2)
                for axis in range(3):
                    r = add(r, subs_equal(p, axis))
                r = scl(r, 7)
                if k == 0:
                    r = add(r, ONE, 6)
                for e, c in r.items():
                    if e in EINDEX:
                        raw[EINDEX[e], i, j] = c
        data.append({"name": f"F{k}", "k": k, "raw": raw, "den": 42, "S6": S})
    det = add(ONE, scl(mul(mul(V[0], V[1]), V[2]), 2))
    for v in V:
        det = add(det, mul(v, v), -1)
    gens = [
        ("M0", ONE, D),
        ("M1", add(ONE, mul(V[0], V[0]), -1), D - 1),
        ("Mdet", det, D - 2),
    ]
    for name, g, degree in gens:
        es = monoms(degree)
        m = len(es)
        raw = np.zeros((len(EXPS), m, m), dtype=np.int64)
        for i, e in enumerate(es):
            for j, f in enumerate(es):
                for t, c in g.items():
                    a = tuple(x + y + z for x, y, z in zip(e, f, t))
                    can = tuple(sorted(a))
                    stab = 6 // len(set(itertools.permutations(a)))
                    raw[EINDEX[can], i, j] += stab * c
        data.append({"name": name, "raw": raw, "den": 6, "monoms": es})
    return data


def vectorization_layout(bases):
    inds = []
    slices = []
    off = 0
    for base in bases:
        r = base.cols
        ii = [(i, j) for i in range(r) for j in range(i, r)]
        inds.append(ii)
        slices.append(slice(off, off + len(ii)))
        off += len(ii)
    return inds, slices


def residual_high_precision(data, bases, x, inds, slices, target, basis_records=None):
    out = iv.matrix(target)
    rt = iv.sqrt(2)
    for ib, (dat, base, ii, sl) in enumerate(zip(data, bases, inds, slices)):
        r = base.cols
        W = iv.matrix(r, r)
        for (i, j), v in zip(ii, x[sl]):
            W[i, j] = W[j, i] = iv.mpf(float(v)) / (1 if i == j else rt)
        print("High-precision residual block", dat["name"], flush=True)
        identity = all(
            float(z) == (1.0 if i == j else 0.0) for (i, j), z in zip(ii, x[sl])
        )
        if basis_records is not None and identity:
            # Free rows are fixed exact dyadic rows.  Their Gram product is evaluated
            # with integers, not rounded BLAS. All variable rows remain interval-valued.
            rec = basis_records[ib]
            free = rec["free"]
            active = [rec["pivot"]] if dat["name"].startswith("F") else rec["pivots"]
            jj = rec["change_of_basis"]
            rat = [[float(z).as_integer_ratio() for z in row] for row in jj]
            den = max(b for row in rat for _, b in row)
            if den & (den - 1):
                raise ArithmeticError("Non-dyadic witness")
            ints = np.array(
                [[a * (den // b) for a, b in row] for row in rat], dtype=object
            )
            exact = ints @ ints.T
            den2 = iv.mpf(den * den)
            J = iv.matrix([[iv.mpf(float(z)) for z in row] for row in jj])
            for i, f in enumerate(free):
                for j in range(r):
                    if base[f, j] != J[i, j]:
                        raise ArithmeticError("Free constant row mismatch")
            Ac = iv.matrix([[base[i, j] for j in range(r)] for i in active])
            AF = Ac * J.T
            AC = Ac * Ac.T
            M = iv.matrix(base.rows, base.rows)
            for i, f in enumerate(free):
                for j, g in enumerate(free):
                    M[f, g] = iv.mpf(int(exact[i, j])) / den2
            for i, f in enumerate(active):
                for j, g in enumerate(free):
                    M[f, g] = M[g, f] = AF[i, j]
                for j, g in enumerate(active):
                    M[f, g] = AC[i, j]
        else:
            M = base * W * base.T
        raw = dat["raw"]
        den = dat["den"]
        for ell in range(len(EXPS)):
            rr, cc = np.nonzero(raw[ell])
            val = iv.mpf(0)
            for i, j in zip(rr, cc):
                val += int(raw[ell, i, j]) * M[int(i), int(j)]
            out[ell] -= val / den
    return out
