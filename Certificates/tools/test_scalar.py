"""Independent exact-rational oracles for the dyadic scalar storage layer."""
from fractions import Fraction as F
from pathlib import Path
import sys
if not __debug__:
    raise RuntimeError('Run without -O')
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'finite/kernel'))
import json, math, random, time
import numpy as np
from exact_i import I, rational_bound, down, up, sqrt_integer

rng = random.Random(2026091802)
checks = 0
for _ in range(6000):
    n = rng.randrange(-(1<<80),1<<80)
    d = rng.randrange(1,1<<80)
    power = rng.randrange(-1000,900)
    if power >= 0:
        n <<= power
    else:
        d <<= -power
    value = F(n,d)
    lo,hi = rational_bound(n,d,False),rational_bound(n,d,True)
    assert F(lo) <= value <= F(hi)
    assert lo == hi or float(up(lo)) == hi, (n,d,lo,hi)
    checks += 2
for _ in range(3000):
    def number():
        return math.ldexp(rng.randrange(-1024,1025)/1024,rng.randrange(-1000,401))
    a,b = sorted([number(),number()])
    c,d = sorted([number(),number()])
    aa,bb = I(a,b),I(c,d)
    for result,lower,upper in (
        (aa+bb,F(a)+F(c),F(b)+F(d)),
        (aa-bb,F(a)-F(d),F(b)-F(c)),
        (aa*bb,min(F(x)*F(y) for x in [a,b] for y in [c,d]),
               max(F(x)*F(y) for x in [a,b] for y in [c,d])),
        (aa.square(),0 if a<=0<=b else min(F(a)**2,F(b)**2),max(F(a)**2,F(b)**2)),
    ):
        assert F(float(result.lo)) <= lower <= upper <= F(float(result.hi))
        checks += 1
    if not a<=0<=b:
        result=aa.recip()
        assert F(float(result.lo)) <= 1/F(b) <= 1/F(a) <= F(float(result.hi))
        checks += 1
for n in [0,1,2,3,4,8,10**20]:
    result=sqrt_integer(n)
    assert F(float(result.lo))**2 <= n <= F(float(result.hi))**2
    checks += 1
for value in [0.,-0.,2.0**-1074,-2.0**-1074,1.,-1.,np.inf,-np.inf]:
    assert float(up(value)) == float(np.nextafter(value,np.inf))
    assert float(down(value)) == float(np.nextafter(value,-np.inf))
    checks += 2
big=I(2**80+1)
assert F(float(big.lo)) <= 2**80+1 <= F(float(big.hi))
checks += 1
array=I(np.arange(60).reshape(3,4,5),np.arange(60).reshape(3,4,5)+1)
for axis in [None,0,1,2,-1]:
    result=array.sum(axis)
    assert np.array_equal(result.lo,np.arange(60).reshape(3,4,5).sum(axis=axis))
    assert np.array_equal(result.hi,(np.arange(60).reshape(3,4,5)+1).sum(axis=axis))
    checks += 1
t=time.perf_counter()
for _ in range(10):
    trial=(I(np.ones((100,100)))+I(.1))*I(-.25,.5)
timing=time.perf_counter()-t
result={'status':'PASS_EXACT_SCALAR_TESTS','exact_checks':checks,
        'benchmark_10_add_multiply_100x100_seconds':timing,
        'scope':'Independent finite tests, not a formal proof.'}
print(json.dumps(result,indent=2))
