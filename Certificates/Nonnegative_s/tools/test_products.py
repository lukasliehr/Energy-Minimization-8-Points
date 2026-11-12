"""Check interval matrix products against exact rational arithmetic."""
from fractions import Fraction as Q
import math
import random
import sys
if not __debug__:
    raise RuntimeError('Run without -O')
sys.dont_write_bytecode = True
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "finite/kernel"))
import numpy as np
from interval_arithmetic import I
from exact_mm import float_bound, mm

rng = random.Random(20260918)
cases = 0
for _ in range(2000):
    n = rng.randrange(-(1 << 250), 1 << 250)
    power = rng.randrange(-700, 1300)
    q = Q(n, 1 << power) if power >= 0 else Q(n << -power)
    lo, hi = float_bound(n, power, False), float_bound(n, power, True)
    assert Q(lo) <= q <= Q(hi)
    assert Q(math.nextafter(lo, math.inf)) > q
    assert Q(math.nextafter(hi, -math.inf)) < q
    cases += 1
for n in [0, 1, -1, 1 << 52, -(1 << 52), (1 << 53) - 1]:
    for power in [0, 52, 1074, 1200]:
        q = Q(n, 1 << power)
        assert Q(float_bound(n, power, False)) <= q <= Q(float_bound(n, power, True))
        cases += 1
for dims in [(1, 1, 1), (4, 7, 3), (3, 4, 5)]:
    m, k, n = dims
    alo = np.array([[rng.uniform(-5, 5) for _ in range(k)] for _ in range(m)])
    ahi = alo + 1e-8
    blo = np.array([[rng.uniform(-5, 5) for _ in range(n)] for _ in range(k)])
    bhi = blo + 2e-8
    out = mm(I(alo, ahi), I(blo, bhi))
    for i in range(m):
        for j in range(n):
            lower = Q(0)
            upper = Q(0)
            for z in range(k):
                pp = [Q(x) * Q(y) for x in [alo[i,z], ahi[i,z]] for y in [blo[z,j], bhi[z,j]]]
                lower += min(pp)
                upper += max(pp)
            assert Q(out.lo[i,j]) <= lower <= upper <= Q(out.hi[i,j])
            cases += 1
    # Exercise both broadcast directions independently of the batched path.
    for left, right in [(I(np.stack([alo, alo]), np.stack([ahi, ahi])), I(blo, bhi)),
                        (I(alo, ahi), I(np.stack([blo, blo]), np.stack([bhi, bhi])))]:
        batched = mm(left, right)
        assert np.array_equal(batched.lo, np.stack([out.lo, out.lo]))
        assert np.array_equal(batched.hi, np.stack([out.hi, out.hi]))
        cases += 1
print("PASS exact matrix products / integer binary64 conversion:", cases, "oracle checks")
