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
    return "entire-second-divided-difference"


def expm1_over_z(z):
    """Entire E(z)=(exp(z)-1)/z, with an explicit absolute tail."""
    z = TM.coerce(z)
    bound = z.bound()
    terms = max(ORDER + 3, 32)
    value = TM.const(1)
    term = TM.const(1)
    for n in range(1, terms + 1):
        term = term * z / (n + 1)
        value = value + term
    value.e = (value.e + iv.exp(bound) * bound ** (terms + 1)
               / math.factorial(terms + 2)).b
    return value


def exp_second_dd(a, b):
    """[0,a,b] exp, entire also at repeated nodes.
    Series: sum_{n>=0} sum_{j=0}^n a^j b^(n-j)/(n+2)!.
    The omitted absolute tail is <= exp(R) R^(M+1)/(M+2)!.
    """
    terms = max(ORDER + 3, 32)
    R = max(a.bound(), b.bound())
    value = TM.const(iv.mpf(1) / 2)
    power_a = TM.const(1)
    homogeneous = TM.const(1)
    for n in range(1, terms + 1):
        power_a = power_a * a
        homogeneous = b * homogeneous + power_a
        value = value + homogeneous / math.factorial(n + 2)
    value.e = (value.e + iv.exp(R) * R ** (terms + 1)
               / math.factorial(terms + 2)).b
    return value


def normalized_phi(Q, T, k=0):
    """Psi_q(t), the centroid-subtracted potential; q=(s+2)/2.
    Psi_q=(phi_{2q-2}(t)-phi_{2q-2}(-1)-4^(-q)(t+1))/q.
    All removable q=0 and q=1 singularities are evaluated by entire series.
    """
    d = 2 - 2 * T
    if k >= 2:
        pref = TM.const(2 ** (k - 1))
        for j in range(1, k - 1):
            pref = pref * (Q + j)
        return pref * ((1 - Q - k) * d.log()).exp()
    ell = iv.log(iv.mpf(4)) - d.log()
    scale = (-Q * iv.log(iv.mpf(4))).exp()
    if k == 1:
        return scale * ell * expm1_over_z(Q * ell)
    return 2 * scale * ell ** 2 * exp_second_dd(-ell, (Q - 1) * ell)


def family_equation(Q, A):
    """F(s,a)/q with its removable q=0 singularity filled in."""
    rt = iv.sqrt(2)
    ds = [2*(1-A), 4*(1-A), 2-rt+(2+rt)*A, 2+rt+(2-rt)*A]
    weights = [16, 16, -8*(2+rt), -8*(2-rt)]
    result = TM.const(0)
    for w, d in zip(weights, ds):
        logd = d.log()
        result = result - w * logd * expm1_over_z(-Q * logd)
    return result


def family_a_derivative(Q, A):
    rt = iv.sqrt(2)
    ds = [2*(1-A), 4*(1-A), 2-rt+(2+rt)*A, 2+rt+(2-rt)*A]
    weights = [32, 64, 8*(2+rt)**2, 8*(2-rt)**2]
    return sum([w*((-Q-1)*d.log()).exp() for w,d in zip(weights,ds)], TM.const(0))


def candidate_model(center, halfwidth):
    c, h = iv.mpf(center), iv.mpf(halfwidth)
    Q = TM([c, h])
    cq = mp.mpf(center)
    rt = mp.sqrt(2)
    def f(a):
        ds = [2*(1-a), 4*(1-a), 2-rt+(2+rt)*a, 2+rt+(2-rt)*a]
        weights = [16, 16, -8*(2+rt), -8*(2-rt)]
        if cq == 0:
            return -sum(w*mp.log(d) for w,d in zip(weights,ds))
        return sum(w*mp.expm1(-cq*mp.log(d))/cq for w,d in zip(weights,ds))
    ac = mp.findroot(f, (mp.mpf(".30"), mp.mpf(".33")))
    A = TM.const(iv.mpf(mp.nstr(ac, mp.mp.dps-10)))
    for _ in range(ORDER.bit_length()+2):
        A = (A-family_equation(Q,A)/family_a_derivative(Q,A)).poly_only()
    residual = family_equation(Q,A).bound()
    aq = A.interval()
    qi = Q.interval()
    padding = iv.mpf("1e-6")
    for _ in range(12):
        U = aq + radius(padding)
        rt = iv.sqrt(2)
        ds = [2*(1-U), 4*(1-U), 2-rt+(2+rt)*U, 2+rt+(2-rt)*U]
        weights = [32,64,8*(2+rt)**2,8*(2-rt)**2]
        derivative = sum([w*d**(-qi-1) for w,d in zip(weights,ds)],iv.mpf(0))
        if not derivative.a > 0:
            raise ArithmeticError("No derivative lower bound")
        error = residual/derivative.a
        if error.b < padding.a:
            A.e = error.b
            if not A.interval().a > 0 or not A.interval().b < iv.mpf(1)/3:
                raise ArithmeticError("Candidate root outside (0,1/3)")
            return Q,A,{"root_residual":str(residual),"root_model_error":str(error),
                        "a_enclosure":str(A.interval()),"parameter":"q=(s+2)/2"}
        padding = error*2
    raise ArithmeticError("Root model did not validate")
