"""Exact Q(sqrt(2))(a), using the replay's existing python-flint dependency.

This is an exploratory algebraic generator, not a numerical certificate.
All cancellation is exact polynomial gcd/division over the rationals.
"""
from fractions import Fraction
from flint import fmpq, fmpq_poly


def polynomial(value):
    if isinstance(value, fmpq_poly):
        return value
    if isinstance(value, Fraction):
        value = fmpq(value.numerator, value.denominator)
    if isinstance(value, float):
        raise ValueError('Use exact rational constants')
    return fmpq_poly([value])


def divide_exact(p, q):
    quotient, remainder = divmod(p, q)
    if remainder:
        raise ArithmeticError('Nonexact symbolic polynomial division')
    return quotient


def _monic_denominator(p, q, d):
    """Normalize only when the nonzero denominator is not already monic."""
    leading = d[len(d)-1]
    if leading == 1:
        # Preserve the constructor's independent polynomial objects as well as
        # its exact values; no coefficient division is required.
        return fmpq_poly(p), fmpq_poly(q), fmpq_poly(d)
    return p/leading, q/leading, d/leading


def _poly_product(p, q):
    """Exact zero and unit identities, preserving independent polynomial data."""
    if not p or not q:
        return fmpq_poly([])
    if p == 1:
        return fmpq_poly(q)
    if q == 1:
        return fmpq_poly(p)
    if p == -1:
        return -q
    if q == -1:
        return -p
    return p*q


class R:
    __slots__ = ('p', 'q', 'd')

    def __init__(self, p=0, q=0, d=1):
        if isinstance(p, R):
            self.p, self.q, self.d = p.p, p.q, p.d
            return
        p, q, d = polynomial(p), polynomial(q), polynomial(d)
        if not d:
            raise ZeroDivisionError('Zero rational-function denominator')
        if not p and not q:
            self.p, self.q, self.d = p, q, fmpq_poly([1])
            return
        # A nonzero constant denominator has no nonconstant common divisor.
        if len(d)>1:
            common = p.gcd(q).gcd(d)
            if len(common)>1:
                p, q, d = (divide_exact(v,common) for v in (p,q,d))
        self.p, self.q, self.d = _monic_denominator(p, q, d)

    @classmethod
    def _normalized(cls, p, q, d):
        """Internal identities whose inputs are already canonical triples."""
        out = object.__new__(cls)
        out.p, out.q, out.d = fmpq_poly(p), fmpq_poly(q), fmpq_poly(d)
        return out

    def __add__(self, other):
        other = R(other)
        if not self:
            return R._normalized(other.p,other.q,other.d)
        if not other:
            return R._normalized(self.p,self.q,self.d)
        if self.d == other.d:
            return R(self.p+other.p,self.q+other.q,self.d)
        return R(_poly_product(self.p,other.d)+_poly_product(other.p,self.d),
                 _poly_product(self.q,other.d)+_poly_product(other.q,self.d),
                 _poly_product(self.d,other.d))
    __radd__ = __add__

    def __neg__(self):
        return R._normalized(-self.p,-self.q,self.d)

    def __sub__(self, other):
        return self+-R(other)

    def __rsub__(self, other):
        return R(other)+-self

    def __mul__(self, other):
        other = R(other)
        if not self or not other:
            return R()
        if self.d == 1 and not self.q and self.p in (1,-1):
            return (R._normalized(other.p,other.q,other.d) if self.p == 1 else -other)
        if other.d == 1 and not other.q and other.p in (1,-1):
            return (R._normalized(self.p,self.q,self.d) if other.p == 1 else -self)
        return R(_poly_product(self.p,other.p)+2*_poly_product(self.q,other.q),
                 _poly_product(self.p,other.q)+_poly_product(self.q,other.p),
                 _poly_product(self.d,other.d))
    __rmul__ = __mul__

    def inverse(self):
        if not self.q:
            return R(self.d,0,self.p)
        return R(_poly_product(self.d,self.p),-_poly_product(self.d,self.q),
                 _poly_product(self.p,self.p)-2*_poly_product(self.q,self.q))

    def __truediv__(self, other):
        return self*R(other).inverse()

    def __rtruediv__(self, other):
        return R(other)*self.inverse()

    def __pow__(self, n):
        if n<0:
            return self.inverse()**(-n)
        value, base = R(1), self
        while n:
            if n&1:
                value *= base
            n//=2
            if n:
                base *= base
        return value

    def __bool__(self):
        return bool(self.p or self.q)

    def __eq__(self, other):
        other = R(other)
        return self.p==other.p and self.q==other.q and self.d==other.d

    def __repr__(self):
        return f'R(({self.p}) + sqrt(2)*({self.q}), denominator=({self.d}))'


VARIABLE = R(fmpq_poly([0,1]))
SQRT2 = R(0,1)
