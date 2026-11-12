import mpmath as mp, numpy as np
from taylor_models import TM, ORDER, iv, ab, radius
from interval_arithmetic import I, up
from fast_interval import mm, norm, absI


def toI(a):
    from exact_iv import PRECISION
    from exact_mm import float_bound
    lo = np.empty((a.rows, a.cols))
    hi = lo.copy()
    for i in range(a.rows):
        for j in range(a.cols):
            lo[i, j] = float_bound(a[i, j].lo, PRECISION, False)
            hi[i, j] = float_bound(a[i, j].hi, PRECISION, True)
    return I(lo, hi)


def mp_nonneg_interval(A):
    return iv.matrix(
        [
            [iv.mpf([0, float(A.hi[i, j])]) for j in range(A.lo.shape[1])]
            for i in range(A.lo.shape[0])
        ]
    )


def mabs(A):
    return iv.matrix([[ab(A[i, j]) for j in range(A.cols)] for i in range(A.rows)])


def inverse0(A):
    mid = mp.matrix(
        [[mp.mpf(A[i, j].mid) for j in range(A.cols)] for i in range(A.rows)]
    )
    cc = mp.inverse(mid)
    C = iv.matrix(
        [
            [iv.mpf(mp.nstr(cc[i, j], mp.mp.dps - 10)) for j in range(cc.cols)]
            for i in range(cc.rows)
        ]
    )
    R = iv.eye(A.rows) - C * A
    q = max(
        [sum([ab(R[i, j]) for j in range(R.cols)], iv.mpf(0)).b for i in range(R.rows)]
    )
    if not q < iv.mpf(".5"):
        raise ArithmeticError(("constant inverse error", q))
    cn = max(
        [sum([ab(C[i, j]) for j in range(C.cols)], iv.mpf(0)).b for i in range(C.rows)]
    )
    e = q * cn / (1 - q)
    return iv.matrix(
        [[C[i, j] + radius(e) for j in range(C.cols)] for i in range(C.rows)]
    )


class MT:
    def __init__(self, c, e=None):
        self.c = c
        assert len(c) == ORDER + 1
        self.e = iv.matrix(c[0].rows, c[0].cols) if e is None else e

    @classmethod
    def from_scalars(cls, T):
        m = len(T)
        n = len(T[0])
        cs = []
        for k in range(ORDER + 1):
            cs.append(
                iv.matrix(
                    [[TM.coerce(T[i][j]).c[k] for j in range(n)] for i in range(m)]
                )
            )
        return cls(
            cs, iv.matrix([[TM.coerce(T[i][j]).e for j in range(n)] for i in range(m)])
        )

    @classmethod
    def const(cls, M):
        return cls([M] + [iv.matrix(M.rows, M.cols) for _ in range(ORDER)])

    def slice(self, rows, cols):
        return MT(
            [iv.matrix([[c[i, j] for j in cols] for i in rows]) for c in self.c],
            iv.matrix([[self.e[i, j] for j in cols] for i in rows]),
        )

    def negative(self):
        return MT([-c for c in self.c], self.e)

    def bound_poly(self):
        R = I(np.zeros((self.c[0].rows, self.c[0].cols)))
        for c in self.c:
            R = R + absI(toI(c))
        return I(R.hi)

    def multiply(self, B):
        cs = []
        for k in range(ORDER + 1):
            cs.append(
                sum(
                    [self.c[i] * B.c[k - i] for i in range(k + 1)],
                    iv.matrix(self.c[0].rows, B.c[0].cols),
                )
            )
        aa = [absI(toI(c)) for c in self.c]
        bb = [absI(toI(c)) for c in B.c]
        tail = I(np.zeros((self.c[0].rows, B.c[0].cols)))
        for i in range(ORDER + 1):
            for j in range(ORDER + 1):
                if i + j > ORDER:
                    tail = tail + mm(aa[i], bb[j])
        ea = absI(toI(self.e))
        eb = absI(toI(B.e))
        tail = tail + mm(self.bound_poly(), eb) + mm(ea, B.bound_poly()) + mm(ea, eb)
        return MT(cs, mp_nonneg_interval(tail))

    def inverse(self):
        n = self.c[0].rows
        assert n == self.c[0].cols
        cs = [inverse0(self.c[0])]
        for k in range(1, ORDER + 1):
            z = sum([self.c[i] * cs[k - i] for i in range(1, k + 1)], iv.matrix(n, n))
            cs.append(-cs[0] * z)
        # The exact formal inverse cancels coefficients through ORDER identically.
        # Only the higher-degree tail and input remainder enter the residual.
        aa = [absI(toI(c)) for c in self.c]
        bb = [absI(toI(c)) for c in cs]
        tail = I(np.zeros((n, n)))
        for i in range(ORDER + 1):
            for j in range(ORDER + 1):
                if i + j > ORDER:
                    tail = tail + mm(aa[i], bb[j])
        P = MT(cs)
        tail = tail + mm(absI(toI(self.e)), P.bound_poly())
        q = norm(tail)
        if not q < 1:
            raise ArithmeticError(("matrix inverse residual", n, q))
        error = (I(q) / (1 - I(q)) * I(norm(P.bound_poly()))).hi.item()
        E = iv.matrix([[iv.mpf([0, float(error)]) for j in range(n)] for i in range(n)])
        return MT(cs, E)

    def scalar(self, i, j):
        return TM([c[i, j] for c in self.c], self.e[i, j])


def right_constant(B, J):
    cs = [b * J for b in B.c]
    err = mm(absI(toI(B.e)), absI(toI(J)))
    return MT(cs, mp_nonneg_interval(err))


def solve_model(A, F):
    """Solve a matrix Taylor model against a vector/matrix RHS.
 Formal coefficients cancel through ORDER; the equation residual bounds the tail.
 """
    R0 = inverse0(A.c[0])
    cs = [R0 * F.c[0]]
    for k in range(1, ORDER + 1):
        q = F.c[k] - sum(
            [A.c[i] * cs[k - i] for i in range(1, k + 1)],
            iv.matrix(A.c[0].rows, F.c[0].cols),
        )
        cs.append(R0 * q)
    H = MT(cs)
    tail = absI(toI(F.e))
    for i in range(1, ORDER + 1):
        sums = I(np.zeros((cs[0].rows, cs[0].cols)))
        for j in range(ORDER + 1 - i, ORDER + 1):
            sums = sums + absI(toI(cs[j]))
        tail = tail + mm(absI(toI(A.c[i])), sums)
    tail = tail + mm(absI(toI(A.e)), H.bound_poly())
    Inv = A.inverse()
    InvBound = Inv.bound_poly() + absI(toI(Inv.e))
    err = mm(InvBound, tail)
    return MT(cs, mp_nonneg_interval(err))
