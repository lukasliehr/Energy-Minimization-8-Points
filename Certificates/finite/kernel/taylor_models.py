"""Interval Taylor models on a real parameter t in [-1,1]."""

import mpmath as mp, math

from exact_iv import iv
import os

ORDER = int(os.environ.get("N8_TAYLOR_ORDER", "8"))
assert 4 <= ORDER <= 20


def ab(x):
    return abs(x).b


def radius(e):
    return iv.mpf([-e.b, e.b])


class TM:
    def __init__(self, c, error=0):
        self.c = [iv.mpf(x) for x in c] + [iv.mpf(0)] * (ORDER + 1 - len(c))
        assert len(self.c) == ORDER + 1
        self.e = iv.mpf(error).b

    @classmethod
    def const(cls, x):
        return cls([x])

    @staticmethod
    def coerce(x):
        return x if isinstance(x, TM) else TM.const(x)

    def bound(self):
        return sum([ab(c) for c in self.c], iv.mpf(0)) + self.e

    def interval(self):
        return self.c[0] + radius(sum([ab(c) for c in self.c[1:]], iv.mpf(0)) + self.e)

    def __neg__(self):
        return TM([-x for x in self.c], self.e)

    def __add__(self, b):
        b = TM.coerce(b)
        return TM([x + y for x, y in zip(self.c, b.c)], self.e + b.e)

    __radd__ = __add__

    def __sub__(self, b):
        return self + -TM.coerce(b)

    def __rsub__(self, b):
        return TM.coerce(b) + -self

    def __mul__(self, b):
        b = TM.coerce(b)
        c = [iv.mpf(0)] * (ORDER + 1)
        tail = iv.mpf(0)
        for i, x in enumerate(self.c):
            for j, y in enumerate(b.c):
                if i + j <= ORDER:
                    c[i + j] += x * y
                else:
                    tail += ab(x * y)
        tail += (
            self.e * sum([ab(c) for c in b.c], iv.mpf(0))
            + b.e * sum([ab(c) for c in self.c], iv.mpf(0))
            + self.e * b.e
        )
        return TM(c, tail)

    __rmul__ = __mul__

    def inverse(self):
        if 0 in self.interval():
            raise ArithmeticError("inverse interval contains zero")
        c = [1 / self.c[0]]
        for n in range(1, ORDER + 1):
            c.append(
                -sum([self.c[k] * c[n - k] for k in range(1, n + 1)], iv.mpf(0))
                / self.c[0]
            )
        P = TM(c)
        R = 1 - self * P
        q = R.bound()
        if not q.b < 1:
            raise ArithmeticError(("TM inverse residual", q))
        return TM(c, P.bound() * q / (1 - q))

    def __truediv__(self, b):
        if not isinstance(b, TM):
            b = iv.mpf(b)
            if 0 in b:
                raise ArithmeticError("division by interval containing zero")
            return TM([x / b for x in self.c], self.e / abs(b).a)
        return self * b.inverse()

    def __rtruediv__(self, b):
        return TM.coerce(b) * self.inverse()

    def __pow__(self, n):
        if isinstance(n, int) and n >= 0:
            r = TM.const(1)
            b = self
            while n:
                if n % 2:
                    r = r * b
                n //= 2
                if n:
                    b = b * b
            return r
        return (TM.coerce(n) * self.log()).exp()

    def exp(self):
        x0 = self.c[0]
        u = self - TM.const(x0)
        ub = u.bound()
        r = TM.const(1)
        term = TM.const(1)
        for k in range(1, ORDER + 1):
            term = term * u / k
            r = r + term
        r = r * iv.exp(x0)
        rem = iv.exp(x0 + ub) * ub ** (ORDER + 1) / math.factorial(ORDER + 1)
        r.e = (r.e + rem).b
        return r

    def log(self):
        x0 = self.c[0]
        if not x0.a > 0:
            raise ArithmeticError("log base nonpositive")
        u = (self - x0) / x0
        ub = u.bound()
        if not ub.b < 1:
            raise ArithmeticError(("log domain radius", ub))
        r = TM.const(iv.log(x0))
        term = TM.const(1)
        for k in range(1, ORDER + 1):
            term = term * u
            r = r + term * ((1 if k % 2 else -1) / iv.mpf(k))
        r.e = (r.e + ub ** (ORDER + 1) / ((ORDER + 1) * (1 - ub))).b
        return r

    def poly_only(self):
        return TM(self.c)


def potential_evaluation_mode(S):
    # Both formulas represent the same entire function of S. Near zero the
    # expm1(z)/z series avoids the large Taylor remainder of an inverse of S.
    # The cutoff is only an enclosure strategy, not a mathematical premise.
    si = S.interval()
    return "entire" if 0 in si or (si.a > -4 and si.b < 4) else "quotient"


def normalized_phi(S, T, k=0):
    d = 2 - 2 * T
    if k:
        pref = TM.const(1)
        for j in range(1, k):
            pref = pref * (S / 2 + j)
        return pref * ((-S / 2 - k) * d.log()).exp() * (2 ** (k - 1))
    ell = -d.log() / 2
    if potential_evaluation_mode(S) == "quotient":
        return ((S * ell).exp() - 1) / S
    z = S * ell
    zb = z.bound()
    r = TM.const(1)
    term = TM.const(1)
    terms = max(ORDER + 3, 32)
    for n in range(1, terms + 1):
        term = term * z / (n + 1)
        r = r + term
    r.e = (r.e + iv.exp(zb) * zb ** (terms + 1) / math.factorial(terms + 2)).b
    return ell * r


def family_equation(S, A):
    q = iv.sqrt(2)
    p = 1 + S / 2
    ds = [2 * (1 - A), 4 * (1 - A), A * (2 + q) + (2 - q), A * (2 - q) + (2 + q)]
    weights = [16, 16, -8 * (2 + q), -8 * (2 - q)]
    return sum([(-p * d.log()).exp() * w for w, d in zip(weights, ds)], TM.const(0))


def family_a_derivative(S, A):
    q = iv.sqrt(2)
    p = 1 + S / 2
    ds = [2 * (1 - A), 4 * (1 - A), A * (2 + q) + (2 - q), A * (2 - q) + (2 + q)]
    weights = [32, 64, 8 * (2 + q) ** 2, 8 * (2 - q) ** 2]
    return p * sum(
        [((-p - 1) * d.log()).exp() * w for w, d in zip(weights, ds)], TM.const(0)
    )


def candidate_model(center, halfwidth):
    c = iv.mpf(center)
    h = iv.mpf(halfwidth)
    S = TM([c, h])
    smp = mp.mpf(center)
    qq = mp.sqrt(2)
    pmp = 1 + smp / 2

    def f(a):
        d = [2 * (1 - a), 4 * (1 - a), 2 - qq + (2 + qq) * a, 2 + qq + (2 - qq) * a]
        return (
            16 * d[0] ** (-pmp)
            + 16 * d[1] ** (-pmp)
            - 8 * (2 + qq) * d[2] ** (-pmp)
            - 8 * (2 - qq) * d[3] ** (-pmp)
        )

    ac = mp.findroot(f, (mp.mpf(".27"), mp.mpf(".33")))
    A = TM.const(iv.mpf(mp.nstr(ac, mp.mp.dps - 10)))
    for _ in range(ORDER.bit_length() + 2):
        F = family_equation(S, A)
        Fa = family_a_derivative(S, A)
        A = (A - F / Fa).poly_only()
    F = family_equation(S, A)
    fb = F.bound()
    aq = A.interval()
    SI = S.interval()
    padding = iv.mpf("1e-6")
    for _ in range(12):
        U = aq + radius(padding)
        q = iv.sqrt(2)
        p = 1 + SI / 2
        ds = [2 * (1 - U), 4 * (1 - U), 2 - q + (2 + q) * U, 2 + q + (2 - q) * U]
        weights = [32, 64, 8 * (2 + q) ** 2, 8 * (2 - q) ** 2]
        Fa = p * sum([w * d ** (-p - 1) for w, d in zip(weights, ds)], iv.mpf(0))
        if not Fa.a > 0:
            raise ArithmeticError("No derivative lower bound")
        err = fb / Fa.a
        if err.b < padding.a:
            A.e = err.b
            return (
                S,
                A,
                {
                    "root_residual": str(fb),
                    "root_model_error": str(err),
                    "a_enclosure": str(A.interval()),
                },
            )
        padding = err * 2
    raise ArithmeticError("Root model did not validate")
