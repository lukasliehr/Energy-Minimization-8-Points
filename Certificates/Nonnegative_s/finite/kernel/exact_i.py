"""Exact dyadic interval operations with binary64 used only as a storage format.

Arithmetic bounds use integers; directed endpoints are assembled from bits.
The numeric proposal code may still use floating-point arithmetic independently.
"""
import struct
import numpy as np
from vector_dyadic import add_bounds, mul_bounds


def rational_bound(n, d=1, upward=False):
    """Outward binary64 encoding of the exact rational n/d; reject overflow."""
    n, d = int(n), int(d)
    if d <= 0:
        raise ValueError("Positive denominator required")
    if not n:
        return 0.0
    if n < 0:
        return -rational_bound(-n, d, not upward)
    exponent = n.bit_length() - d.bit_length()
    if (n < d << exponent) if exponent >= 0 else (n << -exponent < d):
        exponent -= 1
    unit = max(exponent - 52, -1074)
    numerator, denominator = (n, d << unit) if unit >= 0 else (n << -unit, d)
    mantissa, remainder = divmod(numerator, denominator)
    if upward and remainder:
        mantissa += 1
    if not mantissa:
        return 0.0
    if mantissa >= 1 << 53:
        mantissa >>= 1
        unit += 1
    if unit == -1074 and mantissa < 1 << 52:
        bits = mantissa
    else:
        exponent = unit + 52
        if exponent > 1023:
            raise OverflowError("No finite directed binary64 endpoint")
        bits = ((exponent + 1023) << 52) | (mantissa - (1 << 52))
    return struct.unpack('>d', bits.to_bytes(8, 'big'))[0]


def adjacent(x, upward):
    a = np.array(x, dtype=np.float64, copy=True)
    if np.any(np.isnan(a)):
        raise ArithmeticError("NaN endpoint")
    bits = a.view(np.uint64)
    sign = bits >> np.uint64(63)
    zero = (bits & np.uint64(0x7fffffffffffffff)) == 0
    with np.errstate(over='ignore', invalid='ignore'):
        if upward:
            result = np.where(sign == 0, bits + np.uint64(1), bits - np.uint64(1))
            result = np.where(zero, np.uint64(1), result)
            result = np.where(a == np.inf, bits, result)
        else:
            result = np.where(sign == 0, bits - np.uint64(1), bits + np.uint64(1))
            result = np.where(zero, np.uint64(0x8000000000000001), result)
            result = np.where(a == -np.inf, bits, result)
    return np.asarray(result, dtype=np.uint64).view(np.float64)


def down(x):
    return adjacent(x, False)


def up(x):
    return adjacent(x, True)


def endpoint_array(value, upward):
    a = np.asarray(value)
    if a.dtype.kind in 'biu':
        result = np.empty(a.shape, dtype=np.float64)
        for i, x in enumerate(a.flat):
            result.flat[i] = rational_bound(int(x), 1, upward)
        return result
    if a.dtype.kind == 'f' and a.dtype.itemsize <= 8:
        result = np.array(a, dtype=np.float64, copy=True)
    elif a.dtype.kind == 'O':
        result = np.empty(a.shape, dtype=np.float64)
        for i, x in enumerate(a.flat):
            if hasattr(x, 'as_integer_ratio'):
                n, d = x.as_integer_ratio()
            elif hasattr(x, 'numerator') and hasattr(x, 'denominator'):
                n, d = x.numerator, x.denominator
            else:
                raise TypeError("Exact numeric input required")
            result.flat[i] = rational_bound(n, d, upward)
    else:
        raise TypeError("Unsupported endpoint type")
    if not np.all(np.isfinite(result)):
        raise ArithmeticError("Nonfinite endpoint")
    return result


def pair_common(lo, hi):
    ln, ld = float(lo).as_integer_ratio()
    hn, hd = float(hi).as_integer_ratio()
    denominator = max(ld, hd)
    return ln * (denominator // ld), hn * (denominator // hd), denominator


class I:
    __array_priority__ = 1000

    def __init__(self, lo, hi=None):
        if isinstance(lo, I) and hi is None:
            self.lo, self.hi = lo.lo.copy(), lo.hi.copy()
            return
        self.lo = endpoint_array(lo, False)
        self.hi = endpoint_array(lo if hi is None else hi, True)
        if self.lo.shape != self.hi.shape or np.any(self.lo > self.hi):
            raise ValueError("Invalid interval")

    @staticmethod
    def coerce(a):
        return a if isinstance(a, I) else I(a)

    def __add__(self, other):
        b = I.coerce(other)
        al, ah, bl, bh = np.broadcast_arrays(self.lo, self.hi, b.lo, b.hi)
        if al.size >= 256:
            return I(*add_bounds(al, ah, bl, bh))
        lo, hi = np.empty(al.shape), np.empty(al.shape)
        for j, (l1,h1,l2,h2) in enumerate(zip(al.flat,ah.flat,bl.flat,bh.flat)):
            for dst, x, y, direction in ((lo,l1,l2,False),(hi,h1,h2,True)):
                n1,d1 = float(x).as_integer_ratio()
                n2,d2 = float(y).as_integer_ratio()
                d = max(d1,d2)
                dst.flat[j] = rational_bound(n1*(d//d1)+n2*(d//d2),d,direction)
        return I(lo,hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi,-self.lo)

    def __sub__(self, other):
        return self + -I.coerce(other)

    def __rsub__(self, other):
        return I.coerce(other) + -self

    def __mul__(self, other):
        b = I.coerce(other)
        al, ah, bl, bh = np.broadcast_arrays(self.lo, self.hi, b.lo, b.hi)
        if al.size >= 256:
            return I(*mul_bounds(al, ah, bl, bh))
        lo, hi = np.empty(al.shape), np.empty(al.shape)
        for j, (l1,h1,l2,h2) in enumerate(zip(al.flat,ah.flat,bl.flat,bh.flat)):
            a1,a2,ad = pair_common(l1,h1)
            b1,b2,bd = pair_common(l2,h2)
            products = (a1*b1,a1*b2,a2*b1,a2*b2)
            lo.flat[j] = rational_bound(min(products),ad*bd,False)
            hi.flat[j] = rational_bound(max(products),ad*bd,True)
        return I(lo,hi)

    __rmul__ = __mul__

    def recip(self):
        if np.any((self.lo <= 0) & (self.hi >= 0)):
            raise ZeroDivisionError("Interval contains zero")
        lo, hi = np.empty(self.lo.shape), np.empty(self.lo.shape)
        for j, (left,right) in enumerate(zip(self.lo.flat,self.hi.flat)):
            for dst,x,direction in ((lo,right,False),(hi,left,True)):
                n,d = float(x).as_integer_ratio()
                dst.flat[j] = rational_bound(d if n>0 else -d,abs(n),direction)
        return I(lo,hi)

    def __truediv__(self, other):
        return self * I.coerce(other).recip()

    def __rtruediv__(self, other):
        return I.coerce(other) * self.recip()

    def __getitem__(self, key):
        return I(self.lo[key],self.hi[key])

    def __setitem__(self, key, other):
        b = I.coerce(other)
        self.lo[key],self.hi[key] = b.lo,b.hi

    @property
    def T(self):
        return I(self.lo.T,self.hi.T)

    def square(self):
        lo,hi = np.empty(self.lo.shape),np.empty(self.lo.shape)
        for j,(left,right) in enumerate(zip(self.lo.flat,self.hi.flat)):
            a,b,d = pair_common(left,right)
            lower = 0 if a<=0<=b else min(a*a,b*b)
            lo.flat[j] = rational_bound(lower,d*d,False)
            hi.flat[j] = rational_bound(max(a*a,b*b),d*d,True)
        return I(lo,hi)

    def sum(self, axis=None):
        if axis is None:
            lower,upper = self.lo.ravel()[None,:],self.hi.ravel()[None,:]
            shape = ()
        else:
            lower,upper = np.moveaxis(self.lo,axis,-1),np.moveaxis(self.hi,axis,-1)
            shape = lower.shape[:-1]
            lower,upper = lower.reshape(-1,lower.shape[-1]),upper.reshape(-1,upper.shape[-1])
        lo,hi = np.empty(shape),np.empty(shape)
        for j,(left,right) in enumerate(zip(lower,upper)):
            for dst,row,direction in ((lo,left,False),(hi,right,True)):
                pairs = [float(x).as_integer_ratio() for x in row]
                d = max((b for a,b in pairs),default=1)
                n = sum(a*(d//b) for a,b in pairs)
                dst.flat[j] = rational_bound(n,d,direction)
        return I(lo,hi)

    def __matmul__(self, other):
        from exact_mm import mm
        return mm(self,I.coerce(other))

    def magnitude(self):
        return np.maximum(np.abs(self.lo),np.abs(self.hi))


def sqrt_integer(value):
    """Outward enclosure of sqrt(nonnegative integer), using integer isqrt."""
    from math import isqrt
    value = int(value)
    if value < 0:
        raise ValueError("Negative square root")
    precision = 128
    lower = isqrt(value << (2*precision))
    upper = lower if lower*lower == value << (2*precision) else lower+1
    return I(rational_bound(lower,1<<precision,False),
             rational_bound(upper,1<<precision,True))
