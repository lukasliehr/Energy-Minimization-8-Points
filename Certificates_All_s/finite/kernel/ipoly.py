"""Matrix polynomial plus a uniform componentwise remainder, |t|<=1."""

import numpy as np, mpmath as mp
from interval_arithmetic import I
from fast_interval import mm, absI, norm
from matrix_models import toI, inverse0
from taylor_models import ORDER, iv
from exact_mm import prepared_right


def prepare_right(J, Jmp=None):
    """Reuse one privately copied constant factor through a polynomial product."""
    product = prepared_right(J)
    error_product = prepared_right(absI(J))

    def apply(model):
        c = [product(a) for a in model.c]
        mp0 = None
        if model.mp0 is not None and Jmp is not None:
            mp0 = model.mp0 * Jmp
            c[0] = toI(mp0)
        return IP(c, error_product(model.e), mp0)

    return apply


class IP:
    def __init__(self, c, e=None, mp0=None):
        self.c = c
        self.e = I(np.zeros_like(c[0].lo)) if e is None else absI(e)
        self.mp0 = mp0

    @classmethod
    def fromMT(cls, M):
        return cls([toI(c) for c in M.c], absI(toI(M.e)), M.c[0])

    @classmethod
    def const(cls, x):
        x = I.coerce(x)
        return cls([x] + [I(np.zeros_like(x.lo)) for _ in range(ORDER)])

    def bound(self):
        b = self.e
        for c in self.c:
            b = b + absI(c)
        return I(b.hi)

    def poly_bound(self):
        b = I(np.zeros_like(self.c[0].lo))
        for c in self.c:
            b = b + absI(c)
        return I(b.hi)

    def T(self):
        return IP(
            [c.T for c in self.c],
            self.e.T,
            self.mp0.T if self.mp0 is not None else None,
        )

    def negative(self):
        return IP(
            [-c for c in self.c], self.e, -self.mp0 if self.mp0 is not None else None
        )

    def add(self, B):
        mp0 = self.mp0 + B.mp0 if self.mp0 is not None and B.mp0 is not None else None
        c = [a + b for a, b in zip(self.c, B.c)]
        if mp0 is not None:
            c[0] = toI(mp0)
        return IP(c, self.e + B.e, mp0)

    def slice(self, rows, cols):
        key = np.ix_(rows, cols)
        mp0 = (
            iv.matrix([[self.mp0[i, j] for j in cols] for i in rows])
            if self.mp0 is not None
            else None
        )
        return IP([c[key] for c in self.c], self.e[key], mp0)

    def right(self, J, Jmp=None):
        return prepare_right(J, Jmp)(self)

    def multiply(self, B):
        shape = (self.c[0].lo.shape[0], B.c[0].lo.shape[1])
        zero = I(np.zeros(shape))
        c = []
        for k in range(ORDER + 1):
            v = zero
            for i in range(k + 1):
                v = v + mm(self.c[i], B.c[k - i])
            c.append(v)
        mp0 = None
        if self.mp0 is not None and B.mp0 is not None:
            mp0 = self.mp0 * B.mp0
            c[0] = toI(mp0)
        tail = zero
        for i in range(ORDER + 1):
            for j in range(ORDER + 1):
                if i + j > ORDER:
                    tail = tail + mm(absI(self.c[i]), absI(B.c[j]))
        tail = (
            tail
            + mm(self.poly_bound(), B.e)
            + mm(self.e, B.poly_bound())
            + mm(self.e, B.e)
        )
        return IP(c, tail, mp0)

    def inverse(self):
        n = self.c[0].lo.shape[0]
        if self.mp0 is not None:
            mp0 = inverse0(self.mp0)
            c = [toI(mp0)]
        else:
            mp0 = None
            C = I(np.linalg.inv((self.c[0].lo + self.c[0].hi) / 2))
            R = I(np.eye(n)) - mm(C, self.c[0])
            q = norm(R)
            if not q < 1:
                raise ArithmeticError(("inverse constant", q))
            ee = float((I(q) * I(norm(C)) / (1 - I(q))).hi)
            c = [C + I(-ee, ee)]
        for k in range(1, ORDER + 1):
            z = I(np.zeros((n, n)))
            for i in range(1, k + 1):
                z = z + mm(self.c[i], c[k - i])
            c.append(-mm(c[0], z))
        tail = I(np.zeros((n, n)))
        for i in range(ORDER + 1):
            for j in range(ORDER + 1):
                if i + j > ORDER:
                    tail = tail + mm(absI(self.c[i]), absI(c[j]))
        R = IP(c, mp0=mp0)
        tail = tail + mm(self.e, R.poly_bound())
        q = norm(tail)
        if not q < 1:
            raise ArithmeticError(("inverse series remainder", q))
        error = float((I(q) * I(norm(R.poly_bound())) / (1 - I(q))).hi)
        # The exact formal product has zero low-order residual.  The absolute
        # tail matrix B bounds its complete remaining residual.  Bound the
        # matrix Neumann series componentwise, retaining a valid finite upper
        # bound at every recurrence; no numerical inverse is trusted.
        B = I(tail.hi)
        u = float((I(q) / (1 - I(q))).hi)
        DD = I(np.full((n, n), u))
        for _ in range(12):
            DD = I((B + mm(B, DD)).hi)
        component = mm(R.poly_bound(), DD)
        R.e = I(np.minimum(component.hi, error))
        R.inverse_residual_upper = q
        return R
