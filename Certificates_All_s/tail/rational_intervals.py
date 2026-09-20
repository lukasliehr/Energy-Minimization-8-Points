"""Exact interval primitives copied unchanged from the supplied certify_local_tail.py, before its theorem computation. No external dependencies."""
"""Certify the strengthened progress-4 LOCAL tail bound by rational intervals.

No floating-point arithmetic, external packages, network, or global packing-gap
assumption is used by this calculation. All divisions and rounding use integers.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json

PRECISION = 50
SCALE = 10**PRECISION
LOG_TERMS = 80
EXP_DEGREE = 40


def floor_grid(value, scale=SCALE):
    value = F(value)
    return F((value.numerator * scale) // value.denominator, scale)


def ceil_grid(value, scale=SCALE):
    value = F(value)
    return F(-((-value.numerator * scale) // value.denominator), scale)


class I:
    def __init__(self, lo=0, hi=None):
        if isinstance(lo, I) and hi is None:
            self.lo, self.hi = lo.lo, lo.hi
            return
        self.lo = F(lo)
        self.hi = self.lo if hi is None else F(hi)
        assert self.lo <= self.hi

    @classmethod
    def outward(cls, lo, hi):
        return cls(floor_grid(lo), ceil_grid(hi))

    def __add__(self, other):
        other = I(other)
        return I.outward(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -I(other)

    def __rsub__(self, other):
        return I(other) + -self

    def __mul__(self, other):
        other = I(other)
        products = [a*b for a in [self.lo, self.hi]
                    for b in [other.lo, other.hi]]
        return I.outward(min(products), max(products))

    __rmul__ = __mul__

    def reciprocal(self):
        assert self.lo > 0 or self.hi < 0, 'Interval division by zero'
        return I.outward(1/self.hi, 1/self.lo)

    def __truediv__(self, other):
        return self * I(other).reciprocal()

    def __rtruediv__(self, other):
        return I(other) * self.reciprocal()

    def __pow__(self, power):
        assert isinstance(power, int) and power >= 0
        result = I(1)
        base = self
        while power:
            if power % 2:
                result *= base
            power //= 2
            if power:
                base *= base
        return result


def sqrt_interval(value):
    value = I(value)
    assert value.lo >= 0

    def lower_root(x):
        # floor(sqrt(n/d)*SCALE) = isqrt(floor(n*SCALE^2/d)).
        return F(isqrt((x.numerator * SCALE*SCALE)//x.denominator), SCALE)

    return I(lower_root(value.lo), lower_root(value.hi) + F(1, SCALE))


def log_atanh_series(y):
    """Bound log(y), for exact rational 1<=y<=2, by positive atanh terms."""
    y = F(y)
    assert 1 <= y <= 2
    z = I((y-1)/(y+1))
    z2 = z*z
    power = z
    partial = I(0)
    for j in range(LOG_TERMS):
        partial += power / (2*j+1)
        power *= z2
    # The omitted positive series is bounded by
    # z^(2N+1)/[(2N+1)(1-z^2)], then multiplied by two.
    tail = power / ((2*LOG_TERMS+1)*(1-z2))
    return I.outward(2*partial.lo, 2*(partial.hi+tail.hi))


LOG_TWO = log_atanh_series(F(2))


def log_scalar(value):
    value = F(value)
    assert value > 0
    k = 0
    y = value
    while y < 1:
        y *= 2
        k -= 1
    while y >= 2:
        y /= 2
        k += 1
    return log_atanh_series(y) + k*LOG_TWO


def log_interval(value):
    value = I(value)
    assert value.lo > 0
    return I(log_scalar(value.lo).lo, log_scalar(value.hi).hi)


def exp_scalar(value):
    value = F(value)
    if value < 0:
        return exp_scalar(-value).reciprocal()
    y = value
    squarings = 0
    while y > F(1, 4):
        y /= 2
        squarings += 1
    yi = I(y)
    term = I(1)
    partial = I(1)
    for n in range(1, EXP_DEGREE+1):
        term = term*yi/n
        partial += term
    first_omitted = term*yi/(EXP_DEGREE+1)
    # Ratios following the first omitted term are at most y/(N+2).
    tail = first_omitted/(1-yi/(EXP_DEGREE+2))
    result = I.outward(partial.lo, partial.hi+tail.hi)
    for _ in range(squarings):
        result = result*result
    return result


def exp_interval(value):
    value = I(value)
    return I(exp_scalar(value.lo).lo, exp_scalar(value.hi).hi)


def maximum(*values):
    intervals = [I(value) for value in values]
    return I(max(v.lo for v in intervals), max(v.hi for v in intervals))


def decimal_endpoint(value, places=12):
    """Render an exact decimal-grid rational without passing through float."""
    scale = 10**places
    integer = value*scale
    assert integer.denominator == 1
    integer = integer.numerator
    sign = '-' if integer < 0 else ''
    integer = abs(integer)
    return f'{sign}{integer//scale}.{integer%scale:0{places}d}'


def serialize(value):
    value = I(value)
    return {
        'lower_rational': str(value.lo),
        'upper_rational': str(value.hi),
        'lower_decimal_outward': decimal_endpoint(floor_grid(value.lo, 10**12)),
        'upper_decimal_outward': decimal_endpoint(ceil_grid(value.hi, 10**12)),
    }

