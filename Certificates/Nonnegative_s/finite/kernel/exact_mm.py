"""Exact integer enclosures for interval matrix products.

Input/output binary64 numbers are exact dyadic encodings. No floating-point
arithmetic, BLAS, IEEE rounding mode, or gamma error bound establishes any
matrix-product enclosure. FLINT integer multiplication is currently trusted;
the same finite integer statements are suitable for a Lean checker.

Scalar enclosures are implemented in exact_i.py and exact_iv.py.
"""

import math
import os
import struct
import time

import numpy as np
from flint import fmpz_mat
from interval_arithmetic import I

BITS = int(os.environ.get("N8_EXACT_MM_BITS", "112"))
if not 64 <= BITS <= 512:
    raise ValueError("Unsupported fixed-point precision")
STATS = {"calls": 0, "seconds": 0.0, "largest_shape": [0, 0, 0]}


def ceildiv(a, b):
    return -((-a) // b)


def scaled_integer(x, precision, upward):
    """Floor/ceil of the exact binary64 x times 2**precision."""
    n, d = float(x).as_integer_ratio()
    if precision >= 0:
        n <<= precision
    else:
        d <<= -precision
    return ceildiv(n, d) if upward else n // d


def float_bound(n, denominator_power, upward):
    """Directed conversion of n/2**denominator_power by integer bit assembly."""
    n = int(n)
    if n == 0:
        return 0.0
    if n < 0:
        return -float_bound(-n, denominator_power, not upward)
    exponent = n.bit_length() - 1 - denominator_power
    # The unit of a normal number is 2**(exponent-52); subnormals use 2**-1074.
    unit = max(exponent - 52, -1074)
    shift = denominator_power + unit
    if shift >= 0:
        mantissa = ceildiv(n, 1 << shift) if upward else n >> shift
    else:
        mantissa = n << -shift
    if mantissa == 0:
        return 0.0
    if mantissa >= 1 << 53:
        mantissa >>= 1
        unit += 1
    if unit == -1074 and mantissa < 1 << 52:
        encoded = mantissa
    else:
        exponent = unit + 52
        if exponent > 1023:
            raise OverflowError("Exact product cannot be enclosed by finite binary64")
        encoded = ((exponent + 1023) << 52) | (mantissa - (1 << 52))
    return struct.unpack(">d", encoded.to_bytes(8, "big"))[0]


def integer_midrad(A):
    """A is contained in (M + [-R,R])/2**p, entirely by integer division."""
    nrows, ncols = A.lo.shape
    # Selecting an existing finite endpoint is exact. Monotonicity of floor
    # log2 means its dyadic exponent is the same maximum the per-entry scan
    # produced, without retaining millions of endpoint-ratio tuples.
    largest = max(float(np.max(np.abs(A.lo))), float(np.max(np.abs(A.hi)))) if A.lo.size else 0.0
    n, d = largest.as_integer_ratio()
    max_exponent = n.bit_length() - d.bit_length() if n else 0
    p = BITS - max_exponent
    mid, rad, mag = [], [], []
    for left, right in zip(A.lo.flat, A.hi.flat):
        ln, ld = float(left).as_integer_ratio()
        hn, hd = float(right).as_integer_ratio()
        if p >= 0:
            lo, hi = (ln << p) // ld, ceildiv(hn << p, hd)
        else:
            lo, hi = ln // (ld << -p), ceildiv(hn, hd << -p)
        if lo > hi:
            raise ArithmeticError("Invalid quantized interval")
        mid.append(lo + hi)
        rad.append(hi - lo)
        mag.append(abs(lo + hi))
    return (fmpz_mat(nrows, ncols, mid), fmpz_mat(nrows, ncols, rad),
            fmpz_mat(nrows, ncols, mag), p + 1, any(rad))


def prepared_right(J):
    """Prepare a private, immutable right factor for repeated exact products.

    The copy prevents later caller-side interval slice assignments from
    invalidating the certified integer representation. The returned function
    accepts one left interval factor and has the same result as mm(A, J).
    """
    J = I.coerce(J)
    if J.lo.ndim != 2:
        raise ValueError("Prepared right factor must be a matrix")
    private = I(J.lo, J.hi)
    prepared = integer_midrad(private)
    def product(A):
        return mm(A, private, _mb=prepared)
    return product


def prepared_left(A):
    """Prepare a private, immutable left factor; see prepared_right."""
    A = I.coerce(A)
    if A.lo.ndim != 2:
        raise ValueError("Prepared left factor must be a matrix")
    private = I(A.lo, A.hi)
    prepared = integer_midrad(private)
    def product(B):
        return mm(private, B, _ma=prepared)
    return product


def mm(A, B, _ma=None, _mb=None):
    started = time.perf_counter()
    A, B = I.coerce(A), I.coerce(B)
    if A.lo.ndim < 2 or B.lo.ndim < 1:
        raise ValueError("Unsupported product dimensions")
    if A.lo.ndim > 2 and B.lo.ndim == 1:
        raise ValueError("Batched vector products are outside the certified API")
    if A.lo.ndim > 2 or B.lo.ndim > 2:
        # Match numpy.matmul's broadcast of leading batch axes. Array reshape
        # and broadcasting are indexing operations, not proof arithmetic.
        batch = np.broadcast_shapes(A.lo.shape[:-2], B.lo.shape[:-2])
        ashape, bshape = batch + A.lo.shape[-2:], batch + B.lo.shape[-2:]
        alo, ahi = np.broadcast_to(A.lo, ashape), np.broadcast_to(A.hi, ashape)
        blo, bhi = np.broadcast_to(B.lo, bshape), np.broadcast_to(B.hi, bshape)
        shape = batch + (A.lo.shape[-2], B.lo.shape[-1])
        lo, hi = np.empty(shape), np.empty(shape)
        # Reuse immutable integer representations within this one operation;
        # no cross-operation cache can become stale after slice assignments.
        ma = (integer_midrad(A) if _ma is None else _ma) if A.lo.ndim == 2 else None
        mb = (integer_midrad(B) if _mb is None else _mb) if B.lo.ndim == 2 else None
        for index in np.ndindex(batch):
            left = A if A.lo.ndim == 2 else I(alo[index], ahi[index])
            right = B if B.lo.ndim == 2 else I(blo[index], bhi[index])
            c = mm(left, right, _ma=ma, _mb=mb)
            lo[index], hi[index] = c.lo, c.hi
        return I(lo, hi)
    vector = B.lo.ndim == 1
    if vector:
        B = I(B.lo[:, None], B.hi[:, None])
    if A.lo.ndim != 2 or B.lo.ndim != 2 or A.lo.shape[1] != B.lo.shape[0]:
        raise ValueError("Bad product shape")
    ma, ra, aa, pa, ar = integer_midrad(A) if _ma is None else _ma
    mb, rb, ab, pb, br = integer_midrad(B) if _mb is None else _mb
    m, n, k = A.lo.shape[0], B.lo.shape[1], A.lo.shape[1]
    center = ma * mb
    radius = fmpz_mat(m, n)
    if br:
        radius += aa * rb
    if ar:
        radius += ra * ab
    if ar and br:
        radius += ra * rb
    lo, hi = np.empty((m, n)), np.empty((m, n))
    for i in range(m):
        for j in range(n):
            lo[i, j] = float_bound(center[i, j] - radius[i, j], pa + pb, False)
            hi[i, j] = float_bound(center[i, j] + radius[i, j], pa + pb, True)
    result = I(lo, hi)
    STATS["calls"] += 1
    STATS["seconds"] += time.perf_counter() - started
    shape = [m, k, n]
    if math.prod(shape) > math.prod(STATS["largest_shape"]):
        STATS["largest_shape"] = shape
    return result[:, 0] if vector else result
