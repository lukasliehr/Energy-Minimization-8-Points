"""Independent exact-rational adversarial checks of polynomial contracts."""
from fractions import Fraction as Q
import os
from pathlib import Path
import random
import sys
if not __debug__:
    raise RuntimeError('Run without -O')
sys.dont_write_bytecode = True

os.environ["N8_TAYLOR_ORDER"] = "4"
os.environ["N8_DEG_HALF"] = "6"
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'finite/kernel'))
import numpy as np
from interval_arithmetic import I
from exact_iv import D, Matrix
from exact_mm import mm
from ipoly import IP
from taylor_models import ORDER

rng = random.Random(872613)
checks = 0

def rejected(fn):
    global checks
    try:
        fn()
    except (ValueError, IndexError, TypeError, ArithmeticError):
        checks += 1
    else:
        raise AssertionError("Invalid input was accepted")

rejected(lambda: mm(I(np.ones((2, 3, 3))), I(np.ones(3))))
rejected(lambda: mm(I(3), I(np.ones((3, 3)))))
rejected(lambda: Matrix([[1, 2], [3]]))
rejected(lambda: Matrix(-1, 2))
rejected(lambda: Matrix(2, 2)[0, 2])
rejected(lambda: Matrix(2, 2)[-1, 0])
rejected(lambda: D([1, 2, 3]))
rejected(lambda: D([-1, 1]).reciprocal())

def evaluate_bounds(model, t):
    lo = [[Q(0) for _ in range(2)] for _ in range(2)]
    hi = [[Q(0) for _ in range(2)] for _ in range(2)]
    for k, c in enumerate(model.c):
        for i in range(2):
            for j in range(2):
                terms = [Q(float(c.lo[i,j])) * t**k, Q(float(c.hi[i,j])) * t**k]
                lo[i][j] += min(terms)
                hi[i][j] += max(terms)
    for i in range(2):
        for j in range(2):
            radius = Q(float(model.e.hi[i,j]))
            lo[i][j] -= radius
            hi[i][j] += radius
    return lo, hi

def member_value(model, t):
    out = [[Q(0) for _ in range(2)] for _ in range(2)]
    for k, c in enumerate(model.c):
        for i in range(2):
            for j in range(2):
                endpoint = c.lo[i,j] if rng.randrange(2) else c.hi[i,j]
                out[i][j] += Q(float(endpoint)) * t**k
    for i in range(2):
        for j in range(2):
            out[i][j] += rng.choice([-1,0,1]) * Q(float(model.e.hi[i,j]))
    return out

def assert_contains(model, t, actual):
    global checks
    lo, hi = evaluate_bounds(model, t)
    for i in range(2):
        for j in range(2):
            assert lo[i][j] <= actual[i][j] <= hi[i][j]
            checks += 1

for trial in range(20):
    def proposal():
        cc = []
        for k in range(ORDER + 1):
            lo = np.array([[rng.randrange(-10,11) / 32 for _ in range(2)] for _ in range(2)])
            cc.append(I(lo, lo + 1/256))
        return IP(cc, I(np.full((2,2), 1/128)))
    a, b = proposal(), proposal()
    c = a.multiply(b)
    for t in [Q(-1), Q(-7,9), Q(-1,16), Q(0), Q(2,13), Q(1)]:
        av, bv = member_value(a,t), member_value(b,t)
        cv = [[sum(av[i][k] * bv[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
        assert_contains(c, t, cv)

for trial in range(10):
    cc = [I(np.eye(2))]
    for k in range(1, ORDER + 1):
        lo = np.array([[rng.randrange(-5,6) / 512 for _ in range(2)] for _ in range(2)])
        cc.append(I(lo, lo + 1/8192))
    a = IP(cc, I(np.full((2,2),1/65536)))
    b = a.inverse()
    for t in [Q(-1), Q(-2,3), Q(0), Q(1,4), Q(1)]:
        v = member_value(a,t)
        determinant = v[0][0]*v[1][1]-v[0][1]*v[1][0]
        inv = [[v[1][1]/determinant, -v[0][1]/determinant],
               [-v[1][0]/determinant, v[0][0]/determinant]]
        assert_contains(b, t, inv)
print("PASS independent exact-rational polynomial and invalid-input contracts:", checks)
