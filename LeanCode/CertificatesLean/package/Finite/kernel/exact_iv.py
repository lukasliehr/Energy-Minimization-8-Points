"""Small fixed-dyadic interval context with integer-only proof arithmetic.

Elementary enclosures use integer floor/ceiling. sqrt uses isqrt. exp uses
range reduction, a positive Taylor series, and a geometric tail. log uses
power-of-two reduction and the atanh series with a geometric tail. mpmath is
never called by these operations. Its point arithmetic can remain a proposal
generator in the existing checker.
"""
from fractions import Fraction
from functools import lru_cache
from math import isqrt
import os

from flint import fmpz_mat

PRECISION = int(os.environ.get("N8_EXACT_SCALAR_BITS", "384"))
if not 192 <= PRECISION <= 2048:
    raise ValueError("Unsupported exact scalar precision")
SCALE = 1 << PRECISION
SCALE_MASK = SCALE - 1


def ceildiv(n, d):
    return -((-n) // d)


def _scaled_rational_bounds(numerator, denominator):
    """The same outward quotients, with exact dyadic factors cancelled first."""
    if denominator <= 0:
        raise ValueError("Expected positive rational denominator")
    if denominator & (denominator - 1) == 0:
        shift = PRECISION - (denominator.bit_length() - 1)
        if shift >= 0:
            value = numerator << shift
            return value, value
        return numerator >> -shift, -((-numerator) >> -shift)
    scaled = numerator << PRECISION
    return scaled // denominator, ceildiv(scaled, denominator)


def _integer_scale(lo, hi, scalar):
    """Multiply scaled interval endpoints by an exact integer, without rounding."""
    if scalar == 0:
        return D.raw(0)
    if scalar == 1:
        return D.raw(lo, hi)
    if scalar == -1:
        return D.raw(-hi, -lo)
    if lo == hi:
        return D.raw(lo * scalar)
    if scalar > 0:
        return D.raw(lo * scalar, hi * scalar)
    return D.raw(hi * scalar, lo * scalar)


def _product_extrema(alo, ahi, blo, bhi):
    """Exact extrema of the four endpoint products; no interval is widened."""
    if alo == ahi:
        if blo == bhi:
            value = alo * blo
            return value, value
        return (alo * blo, alo * bhi) if alo >= 0 else (alo * bhi, alo * blo)
    if blo == bhi:
        return (alo * blo, ahi * blo) if blo >= 0 else (ahi * blo, alo * blo)
    if alo >= 0:
        if blo >= 0:
            return alo * blo, ahi * bhi
        if bhi <= 0:
            return ahi * blo, alo * bhi
        return ahi * blo, ahi * bhi
    if ahi <= 0:
        if blo >= 0:
            return alo * bhi, ahi * blo
        if bhi <= 0:
            return ahi * bhi, alo * blo
        return alo * bhi, alo * blo
    if blo >= 0:
        return alo * bhi, ahi * bhi
    if bhi <= 0:
        return ahi * blo, alo * blo
    return min(alo * bhi, ahi * blo), max(alo * blo, ahi * bhi)


def _symmetric_product(alo, ahi, blo, bhi):
    """A symmetric factor gives a symmetric exact interval product."""
    if alo == -ahi:
        radius = ahi * max(abs(blo), abs(bhi))
    else:
        assert blo == -bhi
        radius = bhi * max(abs(alo), abs(ahi))
    upper = ceildiv(radius, SCALE)
    return D.raw(-upper, upper)


def _quotient_bounds(alo, ahi, blo, bhi):
    """The exact outward endpoint quotient, with no rounded reciprocal."""
    if blo <= 0 <= bhi:
        raise ZeroDivisionError("Interval contains zero")
    if bhi < 0:
        alo, ahi, blo, bhi = -ahi, -alo, -bhi, -blo
    if alo == ahi == 0:
        return 0, 0
    if blo == bhi and blo & SCALE_MASK == 0:
        divisor = blo >> PRECISION
        if divisor & (divisor - 1) == 0:
            shift = divisor.bit_length() - 1
            return alo >> shift, -((-ahi) >> shift)
        return alo // divisor, ceildiv(ahi, divisor)
    # The positive denominator is monotone in each numerator sign class.
    lower_denominator = bhi if alo >= 0 else blo
    upper_denominator = bhi if ahi <= 0 else blo
    return ((alo << PRECISION) // lower_denominator,
            ceildiv(ahi << PRECISION, upper_denominator))


class D:
    __slots__ = ("lo", "hi")

    def __init__(self, value=0):
        if isinstance(value, D):
            self.lo, self.hi = value.lo, value.hi
        elif type(value) is int or type(value) is bool:
            self.lo = self.hi = int(value) << PRECISION
        elif isinstance(value, (list, tuple)):
            if len(value) != 2:
                raise ValueError("An interval needs two endpoints")
            self.lo, self.hi = D(value[0]).lo, D(value[1]).hi
        elif hasattr(value, "_mpf_"):
            # Point proposals from mpmath are exact dyadics upon import.
            sign, man, exponent, bits = value._mpf_
            if bits < 0:
                raise ValueError("Nonfinite point proposal")
            if exponent >= 0:
                q = Fraction((-1 if sign else 1) * int(man) * (1 << exponent))
            else:
                q = Fraction((-1 if sign else 1) * int(man), 1 << -exponent)
            self.lo, self.hi = _scaled_rational_bounds(q.numerator, q.denominator)
        else:
            if hasattr(value, "item"):
                value = value.item()
            q = Fraction(value)
            self.lo, self.hi = _scaled_rational_bounds(q.numerator, q.denominator)
        if self.lo > self.hi:
            raise ValueError("Reversed dyadic interval")

    @classmethod
    def raw(cls, lo, hi=None):
        out = object.__new__(cls)
        out.lo, out.hi = int(lo), int(lo if hi is None else hi)
        if out.lo > out.hi:
            raise ValueError("Reversed raw dyadic interval")
        return out

    @property
    def a(self):
        return D.raw(self.lo)

    @property
    def b(self):
        return D.raw(self.hi)

    @property
    def mid(self):
        return D.raw((self.lo + self.hi) // 2)

    @property
    def _mpf_(self):
        if self.lo != self.hi:
            raise ValueError("Only exact point dyadics can enter point proposals")
        m = abs(self.lo)
        if not m:
            return (0, 0, 0, 0)
        zeros = (m & -m).bit_length() - 1
        m >>= zeros
        return (int(self.lo < 0), m, zeros - PRECISION, m.bit_length())

    def __float__(self):
        # Float conversion is for proposals/printing. Exact outward transfer to
        # the binary64 interval layer is supplied by integration.toI.
        from exact_mm import float_bound
        return float_bound((self.lo + self.hi) // 2, PRECISION, False)

    def __str__(self):
        return "[" + str(Fraction(self.lo, SCALE)) + ", " + str(Fraction(self.hi, SCALE)) + "]"

    __repr__ = __str__

    def __add__(self, other):
        try:
            b = D(other)
        except (TypeError, ValueError):
            return NotImplemented
        return D.raw(self.lo + b.lo, self.hi + b.hi)

    __radd__ = __add__

    def __neg__(self):
        return D.raw(-self.hi, -self.lo)

    def __sub__(self, b):
        try:
            return self + -D(b)
        except (TypeError, ValueError):
            return NotImplemented

    def __rsub__(self, b):
        return D(b) + -self

    def __mul__(self, other):
        try:
            b = D(other)
        except (TypeError, ValueError):
            return NotImplemented
        if self.lo == self.hi and self.lo & SCALE_MASK == 0:
            return _integer_scale(b.lo, b.hi, self.lo >> PRECISION)
        if b.lo == b.hi and b.lo & SCALE_MASK == 0:
            return _integer_scale(self.lo, self.hi, b.lo >> PRECISION)
        if self.lo == -self.hi or b.lo == -b.hi:
            return _symmetric_product(self.lo, self.hi, b.lo, b.hi)
        lower, upper = _product_extrema(self.lo, self.hi, b.lo, b.hi)
        return D.raw(lower // SCALE, ceildiv(upper, SCALE))

    __rmul__ = __mul__

    def reciprocal(self):
        if self.lo <= 0 <= self.hi:
            raise ZeroDivisionError("Interval contains zero")
        return D.raw(SCALE * SCALE // self.hi, ceildiv(SCALE * SCALE, self.lo))

    def __truediv__(self, b):
        b = D(b)
        return D.raw(*_quotient_bounds(self.lo, self.hi, b.lo, b.hi))

    def __rtruediv__(self, b):
        b = D(b)
        return D.raw(*_quotient_bounds(b.lo, b.hi, self.lo, self.hi))

    def __pow__(self, n):
        if isinstance(n, int):
            if n < 0:
                return (self ** -n).reciprocal()
            result, base = D(1), self
            while n:
                if n & 1:
                    result = result * base
                n >>= 1
                if n:
                    base = base * base
            return result
        return exp(D(n) * log(self))

    def __abs__(self):
        return D.raw(0 if self.lo <= 0 <= self.hi else min(abs(self.lo), abs(self.hi)),
                     max(abs(self.lo), abs(self.hi)))

    def __contains__(self, x):
        b = D(x)
        return self.lo <= b.lo and b.hi <= self.hi

    def __lt__(self, b):
        return self.hi < D(b).lo

    def __le__(self, b):
        return self.hi <= D(b).lo

    def __gt__(self, b):
        return self.lo > D(b).hi

    def __ge__(self, b):
        return self.lo >= D(b).hi

    def __eq__(self, b):
        try:
            b = D(b)
            return self.lo == b.lo and self.hi == b.hi
        except (TypeError, ValueError):
            return False

    def __bool__(self):
        return bool(self.lo or self.hi)


@lru_cache(maxsize=8192)
def _sqrt_point(n):
    if n < 0:
        raise ValueError("Negative square root")
    a = isqrt(n * SCALE)
    return D.raw(a, a if a * a == n * SCALE else a + 1)


def sqrt(x):
    x = D(x)
    return D.raw(_sqrt_point(x.lo).lo, _sqrt_point(x.hi).hi)


@lru_cache(maxsize=8192)
def _exp_point(n):
    if n < 0:
        return _exp_point(-n).reciprocal()
    if n == 0:
        return D(1)
    # Reduce to 0 <= y <= 1/8. Every intermediate is an outward interval.
    squarings = max(0, n.bit_length() - PRECISION + 3)
    y = D.raw(n) / (1 << squarings)
    if y.lo < 0 or y.hi > SCALE // 8:
        raise ArithmeticError("Invalid exponential range reduction")
    total, term = D(1), D(1)
    k = 0
    while True:
        k += 1
        term = term * y / k
        total += term
        if term.hi <= 2:
            break
        if k > PRECISION:
            raise ArithmeticError("Exponential series did not converge")
    nxt = term * y / (k + 1)
    ratio = y / (k + 2)
    if ratio.hi >= SCALE:
        raise ArithmeticError("Invalid exponential geometric ratio")
    # The omitted positive series is <= next_term/(1-ratio).
    tail = nxt / (1 - ratio)
    total = D.raw(total.lo, total.hi + tail.hi)
    for _ in range(squarings):
        total = total * total
    return total


def exp(x):
    x = D(x)
    return D.raw(_exp_point(x.lo).lo, _exp_point(x.hi).hi)


def _atanh_log(z):
    # z in [1,2]. u=(z-1)/(z+1), 0 <= u <= 1/3.
    if z.lo < SCALE or z.hi > 2 * SCALE:
        raise ArithmeticError("Invalid logarithm range reduction")
    u = (z - 1) / (z + 1)
    u2 = u * u
    if u.lo < 0 or u2.hi >= SCALE:
        raise ArithmeticError("Invalid logarithm geometric ratio")
    term, total, k = u, u, 0
    while True:
        k += 1
        term = term * u2
        add = term / (2 * k + 1)
        total += add
        if add.hi <= 2:
            break
        if k > PRECISION:
            raise ArithmeticError("Logarithm series did not converge")
    # Sum omitted u^(2j+1)/(2j+1) <= next power / next denominator / (1-u^2).
    tail = term * u2 / (2 * k + 3) / (1 - u2)
    return D.raw(2 * total.lo, 2 * (total.hi + tail.hi))


@lru_cache(maxsize=1)
def _log2():
    return _atanh_log(D(2))


@lru_cache(maxsize=8192)
def _log_point(n):
    if n <= 0:
        raise ValueError("Nonpositive logarithm")
    exponent = n.bit_length() - 1 - PRECISION
    z = D.raw(n) / (1 << exponent) if exponent >= 0 else D.raw(n) * (1 << -exponent)
    return _atanh_log(z) + exponent * _log2()


def log(x):
    x = D(x)
    return D.raw(_log_point(x.lo).lo, _log_point(x.hi).hi)


class Matrix:
    def __init__(self, rows, cols=None):
        if isinstance(rows, Matrix):
            self.rows, self.cols = rows.rows, rows.cols
            self.data = rows.data.copy()
        elif cols is None:
            seq = list(rows)
            if seq and not isinstance(seq[0], (list, tuple)):
                seq = [[x] for x in seq]
            self.rows, self.cols = len(seq), len(seq[0]) if seq else 0
            if any(len(row) != self.cols for row in seq):
                raise ValueError("Ragged interval matrix")
            self.data = [D(x) for row in seq for x in row]
        else:
            self.rows, self.cols = int(rows), int(cols)
            if self.rows < 0 or self.cols < 0:
                raise ValueError("Negative matrix dimensions")
            self.data = [D(0)] * (self.rows * self.cols)

    def __getitem__(self, key):
        if not isinstance(key, tuple):
            if self.cols != 1:
                raise IndexError("Only vectors have single-index access")
            key = (key, 0)
        i, j = map(int, key)
        if not 0 <= i < self.rows or not 0 <= j < self.cols:
            raise IndexError("Interval matrix index out of range")
        return self.data[i * self.cols + j]

    def __setitem__(self, key, value):
        if not isinstance(key, tuple):
            if self.cols != 1:
                raise IndexError("Only vectors have single-index assignment")
            key = (key, 0)
        i, j = map(int, key)
        if not 0 <= i < self.rows or not 0 <= j < self.cols:
            raise IndexError("Interval matrix index out of range")
        self.data[i * self.cols + j] = D(value)

    @property
    def T(self):
        return Matrix([[self[i,j] for i in range(self.rows)] for j in range(self.cols)])

    def __neg__(self):
        out = Matrix(self.rows, self.cols)
        out.data = [-x for x in self.data]
        return out

    def __add__(self, b):
        if not isinstance(b, Matrix):
            if b == 0:
                return Matrix(self)
            return NotImplemented
        if (self.rows, self.cols) != (b.rows, b.cols):
            raise ValueError("Matrix shape mismatch")
        out = Matrix(self.rows, self.cols)
        out.data = [x + y for x, y in zip(self.data, b.data)]
        return out

    __radd__ = __add__

    def __sub__(self, b):
        return self + -b

    def __mul__(self,b):
        if not isinstance(b,Matrix):
            out=Matrix(self.rows,self.cols);out.data=[x*b for x in self.data]
            return out
        if self.cols!=b.rows:raise ValueError('Matrix multiplication shape mismatch')
        def mr(a):
            mm=[x.lo+x.hi for x in a.data];rr=[x.hi-x.lo for x in a.data]
            return (fmpz_mat(a.rows,a.cols,mm),fmpz_mat(a.rows,a.cols,rr),
                    fmpz_mat(a.rows,a.cols,[abs(x)for x in mm]),any(rr),any(mm))
        ma,ra,aa,ar,am=mr(self);mb,rb,ab,br,bm=mr(b)
        c=ma*mb if am and bm else fmpz_mat(self.rows,b.cols)
        r=fmpz_mat(self.rows,b.cols)
        if am and br:r+=aa*rb
        if ar and bm:r+=ra*ab
        if ar and br:r+=ra*rb
        out=Matrix(self.rows,b.cols);den=4*SCALE
        out.data=[D.raw(int(c[i,j]-r[i,j])//den,ceildiv(int(c[i,j]+r[i,j]),den))
                  for i in range(self.rows)for j in range(b.cols)]
        return out

    __rmul__ = __mul__


class Context:
    dps = 100
    mpf = D
    matrix = Matrix
    sqrt = staticmethod(sqrt)
    exp = staticmethod(exp)
    log = staticmethod(log)

    @staticmethod
    def eye(n):
        return Matrix([[int(i == j) for j in range(n)] for i in range(n)])


iv = Context()
