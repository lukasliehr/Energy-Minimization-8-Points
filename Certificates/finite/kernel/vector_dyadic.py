"""Vectorized exact dyadic endpoint arithmetic.

Only integer/bit operations establish results. Float64 is an input/output
encoding. NumPy object operations dispatch to Python arbitrary-precision ints.
The public operations are add_bounds and mul_bounds on finite binary64 bounds.
"""
import numpy as np

FRAC = np.uint64((1 << 52)-1)
HIDDEN = np.uint64(1 << 52)
SIGN = np.uint64(1 << 63)
BIT_LENGTH = np.frompyfunc(int.bit_length, 1, 1)
CHUNK = 32768

def decode(x):
    """Return signed integer significand n and exponent e: x = n*2**e."""
    x = np.asarray(x, dtype=np.float64)
    words = x.view(np.uint64)
    field = ((words >> np.uint64(52)) & np.uint64(2047)).astype(np.int64)
    if np.any(field == 2047):
        raise ArithmeticError('Nonfinite dyadic input')
    mantissa = ((words & FRAC) | np.where(field != 0,HIDDEN,np.uint64(0))).astype(object)
    mantissa = np.where((words & SIGN) != 0,-mantissa,mantissa)
    exponent = np.where(field != 0,field-1075,-1074)
    return mantissa,exponent

def encode(n,e,upward):
    """Directed float64 encoding of exact dyadics n*2**e.

    Internal helper: all exponent/bit-length arithmetic must fit int64.
    Finite binary64 add/multiply callers have -2148 <= e <= 1942 and
    integer magnitude bit length at most 4196, which satisfy this bound.
    """
    n,e = np.broadcast_arrays(np.asarray(n,dtype=object),np.asarray(e,dtype=np.int64))
    negative = n < 0
    magnitude = np.asarray(np.abs(n),dtype=object)
    length = np.asarray(BIT_LENGTH(magnitude),dtype=np.int64)
    unit = np.maximum(length-1+e-52,-1074)
    shift = unit-e
    # Only the truncating shift needs arbitrary-precision arithmetic. Its
    # quotient has at most 53 bits, so subsequent rounding/carry is uint64.
    right_mask = shift >= 0
    quotient = np.empty(n.shape,dtype=object)
    remainder = np.zeros(n.shape,dtype=bool)
    right = shift[right_mask].astype(object)
    quotient[right_mask] = magnitude[right_mask] >> right
    remainder[right_mask] = (quotient[right_mask] << right) != magnitude[right_mask]
    quotient[~right_mask] = magnitude[~right_mask] << (-shift[~right_mask]).astype(object)
    q = quotient.astype(np.uint64)
    round_up_magnitude = np.logical_xor(bool(upward),negative)
    q = q + (round_up_magnitude & remainder).astype(np.uint64)
    carry = q >= np.uint64(1 << 53)
    q = q >> carry.astype(np.uint64)
    unit = unit + carry.astype(np.int64)
    nonzero = q != 0
    subnormal = nonzero & (unit == -1074) & (q < HIDDEN)
    normal = nonzero & ~subnormal
    if np.any(normal & (unit+52 > 1023)):
        raise OverflowError('No finite directed float64 endpoint')
    words = np.zeros(n.shape,dtype=np.uint64)
    words[subnormal] = q[subnormal]
    words[normal] = ((unit[normal]+1075).astype(np.uint64) << np.uint64(52)) | (q[normal]-HIDDEN)
    words |= negative.astype(np.uint64) << np.uint64(63)
    return words.view(np.float64)

def aligned(a,b):
    """Decode two arrays to a shared exponent at each broadcast position."""
    an,ae=decode(a);bn,be=decode(b)
    an,bn,ae,be=np.broadcast_arrays(an,bn,ae,be)
    # The exponent of a zero is immaterial; avoid unnecessarily long shifts.
    e=np.where(an==0,be,np.where(bn==0,ae,np.minimum(ae,be)))
    aa=an << np.maximum(ae-e,0).astype(object)
    bb=bn << np.maximum(be-e,0).astype(object)
    return aa,bb,e

def add_point(a,b,upward):
    aa,bb,e=aligned(a,b)
    return encode(aa+bb,e,upward)

def _add_bounds(al,ah,bl,bh):
    return add_point(al,bl,False),add_point(ah,bh,True)

def _mul_bounds(al,ah,bl,bh):
    al,ah,ae=aligned(al,ah)
    bl,bh,be=aligned(bl,bh)
    al,ah,bl,bh,ae,be=np.broadcast_arrays(al,ah,bl,bh,ae,be)
    lower=upper=al*bl
    for a,b in ((al,bh),(ah,bl),(ah,bh)):
        product=a*b
        lower=np.minimum(lower,product)
        upper=np.maximum(upper,product)
    return encode(lower,ae+be,False),encode(upper,ae+be,True)

def chunked(operation,al,ah,bl,bh):
    """Partition broadcast inputs into bounded-size exact operations."""
    operands=np.broadcast_arrays(al,ah,bl,bh)
    shape=operands[0].shape
    # Keep object ufuncs on arrays: scalar NumPy integer dispatch differs.
    if not shape:
        lo,hi=operation(*(x.reshape(1) for x in operands))
        return lo.reshape(()),hi.reshape(())
    if operands[0].size <= CHUNK:
        return operation(*operands)
    # flat slices copy only a bounded chunk even for broadcast/strided input.
    lo,hi=np.empty(shape),np.empty(shape)
    for start in range(0,lo.size,CHUNK):
        end=min(start+CHUNK,lo.size)
        ll,hh=operation(*(x.flat[start:end] for x in operands))
        lo.flat[start:end]=ll;hi.flat[start:end]=hh
    return lo,hi

def add_bounds(al,ah,bl,bh):
    return chunked(_add_bounds,al,ah,bl,bh)

def mul_bounds(al,ah,bl,bh):
    return chunked(_mul_bounds,al,ah,bl,bh)
