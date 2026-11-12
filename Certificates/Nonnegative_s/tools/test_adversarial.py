#!/usr/bin/env python3
"""Independent small exact arithmetic audit.

Checks directed endpoint tightness against Fraction and transcendental bounds
against independently summed rational series. This is not a full proof replay.
"""
from fractions import Fraction as F
import argparse
import hashlib
import json
import math
from pathlib import Path
import random
import sys
sys.dont_write_bytecode = True
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--kernel',type=Path,default=Path(__file__).resolve().parents[1]/'finite/kernel')
parser.add_argument('--output',type=Path,help='Optional JSON report; stdout always contains the report.')
args=parser.parse_args()
if not __debug__:
    raise RuntimeError('Run without -O: assertions enforce independent tests.')
KERNEL=args.kernel.resolve()
sys.path.insert(0,str(KERNEL))
import exact_i as ei
import exact_iv as ev
import exact_mm as em
import numpy as np

rng=random.Random(81332019)
counts={'directed_rationals':0,'dyadic_bound_crosschecks':0,'matrix_entries':0,'exp':0,'log':0,'prepared_factor_cases':0,'formal_inverse_entries':0}
def directed(q):
    try:
        lo=ei.rational_bound(q.numerator,q.denominator,False)
        hi=ei.rational_bound(q.numerator,q.denominator,True)
    except OverflowError:
        assert abs(q)>F.from_float(float.fromhex('0x1.fffffffffffffp1023'))
        return
    assert F.from_float(lo)<=q<=F.from_float(hi)
    if F.from_float(lo)!=q:
        nxt=math.nextafter(lo,math.inf)
        assert math.isinf(nxt) or q<F.from_float(nxt)
    if F.from_float(hi)!=q:
        prev=math.nextafter(hi,-math.inf)
        assert math.isinf(prev) or F.from_float(prev)<q
    counts['directed_rationals']+=1

for e in [-2200,-1075,-1074,-1073,-1023,-1022,-53,-1,0,1,52,53,1022,1023,1024]:
    center=F(2)**e
    for shift in [F(0),F(1,2),F(1,2**54),-F(1,2**54)]:
        for sign in [-1,1]:directed(sign*center*(1+shift))
for _ in range(6000):
    n=rng.getrandbits(rng.randrange(1,2200))*(-1 if rng.getrandbits(1) else 1)
    d=rng.getrandbits(rng.randrange(1,2200))+1
    directed(F(n,d))
for _ in range(1000):
    n=rng.getrandbits(rng.randrange(1,800))*(-1 if rng.getrandbits(1) else 1)
    p=rng.randrange(-100,1800)
    q=F(n,1<<p) if p>=0 else F(n*(1<<-p))
    for upward in [False,True]:
        try:a=em.float_bound(n,p,upward)
        except OverflowError:
            assert abs(q)>F.from_float(float.fromhex('0x1.fffffffffffffp1023'))
            continue
        assert a==ei.rational_bound(q.numerator,q.denominator,upward)
        counts['dyadic_bound_crosschecks']+=1

def exp_ref(x):
    if x<0:
        a,b=exp_ref(-x)
        return 1/b,1/a
    term=total=F(1)
    for k in range(1,301):
        term=term*x/k
        total+=term
    nxt=term*x/301
    return total,total+nxt/(1-x/302)

def log_unit(x):
    u=(x-1)/(x+1)
    assert 0<=u<=F(1,3)
    term=total=u
    for k in range(1,351):
        term*=u*u
        total+=term/(2*k+1)
    tail=term*u*u/F(703)/(1-u*u)
    return 2*total,2*(total+tail)

log2=log_unit(F(2))
def log_ref(x):
    k=0
    while x<1:x*=2;k-=1
    while x>2:x/=2;k+=1
    a,b=log_unit(x)
    return (a+k*log2[0],b+k*log2[1]) if k>=0 else (a+k*log2[1],b+k*log2[0])

for x in [F(0),F(1),F(-1),F(1,8),F(1,8)+F(1,2**380),F(10),F(-10)]+[F(rng.randrange(-170,171),17) for _ in range(15)]:
    got=ev.exp(ev.D(x));lo,hi=exp_ref(x)
    assert F(got.lo,ev.SCALE)<=lo<=hi<=F(got.hi,ev.SCALE),(x,got)
    counts['exp']+=1
for x in [F(1),F(2),F(1,2),F(2)-F(1,2**380),F(2)**120,F(2)**-120]+[F(rng.randrange(1,200),71) for _ in range(20)]:
    got=ev.log(ev.D(x));lo,hi=log_ref(x)
    assert F(got.lo,ev.SCALE)<=lo<=hi<=F(got.hi,ev.SCALE),(x,got)
    counts['log']+=1
for _ in range(60):
    m,k,n=[rng.randrange(1,5) for j in range(3)]
    al=np.array([[math.ldexp(rng.randrange(-100,101),rng.randrange(-50,30)) for j in range(k)] for i in range(m)])
    bl=np.array([[math.ldexp(rng.randrange(-100,101),rng.randrange(-50,30)) for j in range(n)] for i in range(k)])
    ah=np.nextafter(al,math.inf);bh=np.nextafter(bl,math.inf)
    got=em.mm(ei.I(al,ah),ei.I(bl,bh))
    for i in range(m):
        for j in range(n):
            lower=upper=F(0)
            for t in range(k):
                products=[F.from_float(x)*F.from_float(y) for x in (al[i,t],ah[i,t]) for y in (bl[t,j],bh[t,j])]
                lower+=min(products);upper+=max(products)
            assert F.from_float(got.lo[i,j])<=lower<=upper<=F.from_float(got.hi[i,j])
            counts['matrix_entries']+=1
def same(a,b):
    assert np.array_equal(a.lo,b.lo) and np.array_equal(a.hi,b.hi)
for _ in range(30):
    A=ei.I(np.array([[rng.randrange(-10,11) for j in range(3)] for i in range(2)],dtype=float))
    B=ei.I(np.array([[rng.randrange(-10,11) for j in range(4)] for i in range(3)],dtype=float))
    original_A,original_B=ei.I(A),ei.I(B)
    right=em.prepared_right(B);left=em.prepared_left(A)
    A[0,0]=123456;B[0,0]=-23456
    same(right(original_A),em.mm(original_A,original_B))
    same(left(original_B),em.mm(original_A,original_B))
    batch=ei.I(np.stack([original_A.lo,original_A.lo*2]),np.stack([original_A.hi,original_A.hi*2]))
    same(right(batch),em.mm(batch,original_B))
    counts['prepared_factor_cases']+=3
from ipoly import IP
from taylor_models import ORDER
coeff=[np.array([[2.,0.],[0.,3.]]),np.array([[0.,.25],[.125,0.]]),np.array([[.03125,.015625],[-.015625,.0625]])]
coeff += [np.zeros((2,2)) for _ in range(ORDER+1-len(coeff))]
radius=np.full((2,2),2.**-30)
model=IP([ei.I(c) for c in coeff],ei.I(radius))
inverse=model.inverse()
for z in [F(-1),F(-1,2),F(0),F(1,2),F(1)]:
    point=[[sum(F.from_float(c[i,j])*z**k for k,c in enumerate(coeff))+F((1 if i==j else -1),2**31) for j in range(2)] for i in range(2)]
    det=point[0][0]*point[1][1]-point[0][1]*point[1][0]
    exact=[[point[1][1]/det,-point[0][1]/det],[-point[1][0]/det,point[0][0]/det]]
    for i in range(2):
        for j in range(2):
            lo=-F.from_float(inverse.e.hi[i,j]);hi=-lo
            for k,c in enumerate(inverse.c):
                a,b=F.from_float(c.lo[i,j])*z**k,F.from_float(c.hi[i,j])*z**k
                lo+=min(a,b);hi+=max(a,b)
            assert lo<=exact[i][j]<=hi
            counts['formal_inverse_entries']+=1
root=KERNEL
report={'status':'PASS_INDEPENDENT_SMALL_EXACT_CHECKS','counts':counts,
    'test_script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(root.glob('*.py'))},
    'scope':'Independent small arithmetic checks plus separately documented source reasoning. Not full CAP replay or formal verification.'}
if args.output is not None:
    args.output.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
