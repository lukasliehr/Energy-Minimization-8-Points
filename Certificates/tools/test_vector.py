#!/usr/bin/env python3
"""Independent Fraction boundary checks for exact dyadic arrays."""
import argparse
from fractions import Fraction as F
import hashlib
import json
import math
from pathlib import Path
import random
import sys
sys.dont_write_bytecode = True
import numpy as np

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--kernel', type=Path,
                    default=Path(__file__).resolve().parents[1]/'finite/kernel')
parser.add_argument('--output', type=Path)
args = parser.parse_args()
if not __debug__:
    raise RuntimeError('Run without -O: assertions enforce these checks.')
sys.path.insert(0, str(args.kernel))
from exact_i import I, rational_bound
import vector_dyadic as v

rng = random.Random(67152639)
counts = {'encode_directions': 0, 'encode_overflow': 0,
          'interval_entries': 0, 'integrated_entries': 0}

def bits_equal(a, b):
    assert np.array_equal(np.asarray(a, dtype=np.float64).view(np.uint64),
                          np.asarray(b, dtype=np.float64).view(np.uint64))

def dyadic(n, e):
    return F(n << e) if e >= 0 else F(n, 1 << -e)

# Include carry at every relevant significand length, both signs, and
# subnormal/normal/overflow transition exponents. Add random long integers.
records = []
for length in [1, 2, 51, 52, 53, 54, 105, 106, 107, 500, 2100]:
    for n in [(1 << length)-1, 1 << length, (1 << length)+1]:
        for e in [-2200, -1076, -1075, -1074, -1023, -1022,
                  -53, -52, -1, 0, 1, 970, 971, 972, 1023]:
            records.extend([(n, e), (-n, e)])
records.extend([(0, -2148), (0, 0), (0, 1942)])
for _ in range(5000):
    n = rng.getrandbits(rng.randrange(1, 2150))
    records.append((n if rng.getrandbits(1) else -n,
                    rng.randrange(-2300, 1100)))

for upward in [False, True]:
    finite_n, finite_e, expected = [], [], []
    overflow_examples = []
    for n, e in records:
        q = dyadic(n, e)
        try:
            bound = rational_bound(q.numerator, q.denominator, upward)
        except OverflowError:
            overflow_examples.append((n, e))
            continue
        fq = F.from_float(bound)
        if upward:
            assert fq >= q
            if fq != q:
                prev = math.nextafter(bound, -math.inf)
                assert math.isinf(prev) or F.from_float(prev) < q
        else:
            assert fq <= q
            if fq != q:
                nxt = math.nextafter(bound, math.inf)
                assert math.isinf(nxt) or F.from_float(nxt) > q
        finite_n.append(n); finite_e.append(e); expected.append(bound)
    got = v.encode(finite_n, finite_e, upward)
    bits_equal(got, expected)
    counts['encode_directions'] += len(expected)
    for n, e in overflow_examples[::max(1, len(overflow_examples)//100)]:
        try:
            v.encode(n, e, upward)
        except OverflowError:
            counts['encode_overflow'] += 1
        else:
            raise AssertionError('Expected directed overflow rejection')

def reference(A, B, multiplication=False):
    """Independent scalar rational construction; no interval arithmetic calls."""
    B = I.coerce(B)
    al, ah, bl, bh = np.broadcast_arrays(A.lo, A.hi, B.lo, B.hi)
    lo, hi = np.empty(al.shape), np.empty(al.shape)
    for j, (a, b, c, d) in enumerate(zip(al.flat, ah.flat, bl.flat, bh.flat)):
        if multiplication:
            pairs = [float(x).as_integer_ratio() for x in (a, b, c, d)]
            da = max(pairs[0][1], pairs[1][1])
            db = max(pairs[2][1], pairs[3][1])
            aa, bb = [n*(da//q) for n, q in pairs[:2]]
            cc, dd = [n*(db//q) for n, q in pairs[2:]]
            products = [aa*cc, aa*dd, bb*cc, bb*dd]
            lo.flat[j] = rational_bound(min(products), da*db, False)
            hi.flat[j] = rational_bound(max(products), da*db, True)
        else:
            for dest, x, y, upward in [(lo, a, c, False), (hi, b, d, True)]:
                nx, dx = float(x).as_integer_ratio()
                ny, dy = float(y).as_integer_ratio()
                den = max(dx, dy)
                dest.flat[j] = rational_bound(nx*(den//dx)+ny*(den//dy), den, upward)
    return I(lo, hi)

def compare(A, B):
    for multiplication, operation in [(False, v.add_bounds), (True, v.mul_bounds)]:
        old = reference(A, B, multiplication)
        lo, hi = operation(A.lo, A.hi, B.lo, B.hi)
        bits_equal(lo, old.lo); bits_equal(hi, old.hi)
        integrated = A*B if multiplication else A+B
        bits_equal(integrated.lo, old.lo); bits_equal(integrated.hi, old.hi)
        counts['interval_entries'] += old.lo.size
        counts['integrated_entries'] += old.lo.size

edge = np.array([0., -0., 2.**-1074, -2.**-1074,
                 float.fromhex('0x0.fffffffffffffp-1022'),
                 2.**-1022, -2.**-1022, 1., -1.,
                 math.nextafter(1., 0.), math.nextafter(1., 2.)])
compare(I(edge[:, None]), I(edge[None, :]))
compare(I(0.), I(-0.))
compare(I(np.empty((0, 3))), I(1.))
nrng = np.random.default_rng(971)
for n in [v.CHUNK-1, v.CHUNK, v.CHUNK+1, 2*v.CHUNK+3]:
    vals = nrng.normal(size=(4, n))
    A = I(np.minimum(vals[0], vals[1]), np.maximum(vals[0], vals[1]))
    B = I(np.minimum(vals[2], vals[3]), np.maximum(vals[2], vals[3]))
    compare(A, B)
    compare(A, I(-0.25, 0.75))
vals = nrng.normal(size=(3, 257, 259))
A = I(np.minimum(vals[0], vals[1]), np.maximum(vals[0], vals[1]))
# Test genuinely strided stored endpoints and broadcast column vectors.
A.lo = A.lo.T[:, ::-1]; A.hi = A.hi.T[:, ::-1]
compare(A, I(vals[2, 0, :, None]))

# Exercise both integration branches and reverse operators around the threshold.
for n in [0, 1, 255, 256, 257, v.CHUNK+1]:
    A = I(nrng.normal(size=n)); B = I(-0.125, 0.25)
    for multiplication, got in [(False, A+B), (True, A*B)]:
        old = reference(A, B, multiplication)
        bits_equal(got.lo, old.lo); bits_equal(got.hi, old.hi)
        counts['integrated_entries'] += got.lo.size
    for multiplication, got in [(False, 1+A), (True, 2*A)]:
        old = reference(A, 2 if multiplication else 1, multiplication)
        bits_equal(got.lo, old.lo); bits_equal(got.hi, old.hi)
        counts['integrated_entries'] += got.lo.size

report = {'status': 'PASS_INDEPENDENT_VECTOR_BOUNDARIES', 'counts': counts,
          'source_sha256': {str(p.name): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in [Path(__file__), Path(v.__file__), args.kernel/'exact_i.py']},
          'scope': 'Independent arithmetic boundary tests, not a CAP replay.'}
if args.output is not None:
    args.output.write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report, indent=2))
