"""Check exact scalar identities and transcendental enclosures."""
from fractions import Fraction as Q
from pathlib import Path
import sys
if not __debug__:
    raise RuntimeError('Run without -O')
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'finite/kernel'))
import random
import mpmath as mp
from exact_iv import D, Matrix, PRECISION, SCALE, sqrt, exp, log

mp.mp.dps = 160
def rational_point(v):
    s, n, e, _ = v._mpf_
    return Q((-1 if s else 1) * int(n) * (1 << max(e,0)), 1 << max(-e,0))

def contains(x, v):
    q = rational_point(v)
    assert Q(x.lo, SCALE) <= q <= Q(x.hi, SCALE), (x, str(v))

count = 0
for txt in ["1/10000000000", "1/100", "1/2", "1", "2", "3", "7/3", "100", "10000000000"]:
    q = Q(txt)
    z = D(txt)
    x = mp.mpf(q.numerator) / q.denominator
    contains(sqrt(z), mp.sqrt(x))
    contains(log(z), mp.log(x))
    if q <= 100:
        contains(exp(z), mp.exp(x))
        contains(exp(-z), mp.exp(-x))
    count += 1
rng = random.Random(123)
for _ in range(100):
    q = Q(rng.randrange(1, 10000), 127)
    z = D(str(q))
    x = mp.mpf(q.numerator) / q.denominator
    contains(log(z), mp.log(x))
    contains(exp(z), mp.exp(x))
    contains(sqrt(z), mp.sqrt(x))
    assert 1 in z * z.reciprocal()
    count += 1
aa = [[Q(1,3),Q(-7,13)], [Q(2,7),Q(5,9)]]
bb = [[Q(-2,9),Q(2,3)], [Q(12,17),Q(-3,8)]]
a = Matrix([[str(z) for z in row] for row in aa])
b = Matrix([[str(z) for z in row] for row in bb])
c = a * b
for i in range(2):
    for j in range(2):
        q = sum(aa[i][k] * bb[k][j] for k in range(2))
        assert Q(c[i,j].lo, SCALE) <= q <= Q(c[i,j].hi, SCALE)
print("PASS exact scalar/transcendental context:", count, "inputs at", PRECISION, "bits")
