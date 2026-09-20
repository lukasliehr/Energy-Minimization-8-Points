"""Outward dyadic intervals. Every bound is an integer calculation.

All endpoints are integer multiples of 2**(-BITS). No float, decimal, or
transcendental-library operation contributes to a certificate bound.
"""
from fractions import Fraction
from math import isqrt

BITS = 256
SCALE = 1 << BITS


def ceiling_div(a, b):
    return -((-a)//b)


class Interval:
    __slots__ = ('lo', 'hi')

    def __init__(self, lo, hi=None):
        self.lo = int(lo)
        self.hi = int(lo if hi is None else hi)
        if self.lo > self.hi:
            raise ArithmeticError('Invalid interval')

    @classmethod
    def rational(cls, q):
        q = Fraction(str(q))
        return cls(q.numerator*SCALE//q.denominator,
                   ceiling_div(q.numerator*SCALE, q.denominator))

    @classmethod
    def coerce(cls, value):
        return value if isinstance(value, cls) else cls.rational(value)

    def __add__(self, other):
        other = self.coerce(other)
        return Interval(self.lo+other.lo, self.hi+other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self+-self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other)+-self

    def __mul__(self, other):
        other = self.coerce(other)
        products = [self.lo*other.lo, self.lo*other.hi,
                    self.hi*other.lo, self.hi*other.hi]
        return Interval(min(products)//SCALE, ceiling_div(max(products), SCALE))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.coerce(other)
        if other.lo <= 0 <= other.hi:
            raise ZeroDivisionError('Interval contains zero')
        inverse = Interval(SCALE*SCALE//other.hi,
                           ceiling_div(SCALE*SCALE, other.lo))
        return self*inverse

    def __pow__(self, n):
        if n < 0:
            raise ValueError('Only nonnegative powers')
        result, base = Interval(SCALE), self
        while n:
            if n & 1:
                result *= base
            base *= base
            n //= 2
        return result

    def nonzero(self):
        return self.lo > 0 or self.hi < 0

    def magnitude(self):
        return max(abs(self.lo), abs(self.hi))

    def encode(self):
        return {'lower_numerator': str(self.lo), 'upper_numerator': str(self.hi),
                'denominator_power_of_two': BITS}


def root(n):
    lo = isqrt(n*SCALE*SCALE)
    hi = lo if lo*lo == n*SCALE*SCALE else lo+1
    if not (0 <= lo <= hi and lo*lo <= n*SCALE*SCALE <= hi*hi):
        raise ArithmeticError('Root enclosure failure')
    return Interval(lo, hi)


ROOTS = [Interval(SCALE), root(2), root(58), root(116)]


def field(x):
    return sum((Interval.rational(q)*r for q, r in zip(x.c, ROOTS)), Interval(0))


def log_between_one_and_four(x):
    if not SCALE <= x.lo <= x.hi <= 4*SCALE:
        raise ArithmeticError('Log input outside [1,4]')
    z = (x-1)/(x+1)
    if not 0 <= z.lo or z.hi*5 > 3*SCALE:
        raise ArithmeticError('Log transform outside [0,3/5]')
    count = 256
    power, square, total = z, z*z, Interval(0)
    for j in range(count):
        total += power/(2*j+1)
        power *= square
    # 0 <= remainder <= 2*z^(2m+1)/((2m+1)*(1-z^2)).
    bound = 2*Fraction(3, 5)**(2*count+1)/((2*count+1)*(1-Fraction(3, 5)**2))
    tail = Interval.rational(bound)
    return 2*total+Interval(0, tail.hi)


def transpose(a):
    return [list(row) for row in zip(*a)]


def multiply(a, b):
    if len(a[0]) != len(b):
        raise ArithmeticError('Matrix shape mismatch')
    return [[sum((x*b[k][j] for k, x in enumerate(row)), Interval(0))
             for j in range(len(b[0]))] for row in a]
