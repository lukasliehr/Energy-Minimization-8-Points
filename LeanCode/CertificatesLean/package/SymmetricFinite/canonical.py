"""Constant rational symmetry bases and exact polynomial coefficient maps.

The verifier constructs coefficient arrays from rational polynomial formulas.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import lcm


ZERO=(0,0,0)
ONE={ZERO:F(1)}
X=[{tuple(int(i==j) for i in range(3)):F(1)} for j in range(3)]


def add(p,q):
    out=dict(p)
    for e,c in q.items(): out[e]=out.get(e,F(0))+c
    return {e:c for e,c in out.items() if c}


def scale(c,p): return {e:c*v for e,v in p.items() if c*v}


def mul(p,q):
    out={}
    for e,c in p.items():
        for f,d in q.items():
            key=tuple(a+b for a,b in zip(e,f))
            out[key]=out.get(key,F(0))+c*d
    return {e:c for e,c in out.items() if c}


def power(p,n):
    out=ONE
    for _ in range(n): out=mul(out,p)
    return out


SIG=add(add(X[0],X[1]),X[2])
E2=add(add(mul(X[0],X[1]),mul(X[0],X[2])),mul(X[1],X[2]))
E3=mul(mul(X[0],X[1]),X[2])
DELTA=mul(mul(add(X[0],scale(-1,X[1])),add(X[0],scale(-1,X[2]))),add(X[1],scale(-1,X[2])))
P=[add(x,scale(-F(1,3),SIG)) for x in X]
PN=add(add(mul(P[0],P[0]),mul(P[1],P[1])),mul(P[2],P[2]))
Q=[add(mul(p,p),scale(-F(1,3),PN)) for p in P]
Z=add(X[1],X[2]);W=mul(X[1],X[2]);ODD=add(X[1],scale(-1,X[2]))


def monoms(d): return [e for e in product(range(d+1),repeat=3) if sum(e)<=d]


def invariant_tags(d):
    return sorted([(i,j,k) for i in range(d+1) for j in range(d//2+1)
                   for k in range(d//3+1) if i+2*j+3*k<=d],
                  key=lambda t:(t[0]+2*t[1]+3*t[2],t))


def invariant_polynomial(t):
    i,j,k=t
    return mul(mul(power(SIG,i),power(E2,j)),power(E3,k))


def parity_tags(d):
    return sorted([(i,j,k) for i in range(d+1) for j in range(d+1)
                   for k in range(d//2+1) if i+j+2*k<=d],
                  key=lambda t:(t[0]+t[1]+2*t[2],t))


def parity_polynomial(t):
    i,j,k=t
    return mul(mul(power(X[0],i),power(Z,j)),power(W,k))


def fraction(q): return F(int(q.numerator),int(q.denominator))


@lru_cache(None)
def basis(kind,d):
    if kind=='s3':
        tags0=invariant_tags(d);tags1=invariant_tags(d-3)
        tags2=[(0,*t) for t in invariant_tags(d-1)]+[(1,*t) for t in invariant_tags(d-2)]
        polys0=[invariant_polynomial(t) for t in tags0]
        polys1=[mul(DELTA,invariant_polynomial(t)) for t in tags1]
        polys2=[mul((P if t[0]==0 else Q)[0],invariant_polynomial(t[1:])) for t in tags2]
        polys3=[mul(add((P if t[0]==0 else Q)[1],scale(-1,(P if t[0]==0 else Q)[2])),
                    invariant_polynomial(t[1:])) for t in tags2]
        groups=[polys0,polys1,polys2,polys3]
        tags=[tags0,tags1,tags2,tags2]
        pivots=[[tags0.index((i,0,0)) for i in range(5)],
                [tags1.index((i,0,0)) for i in range(2)],
                [tags2.index((0,i,0,0)) for i in range(4)]+
                [tags2.index((1,i,0,0)) for i in range(3)]]
        pivots.append(pivots[2])
    elif kind=='s2':
        tags0=parity_tags(d);tags1=parity_tags(d-1)
        groups=[[parity_polynomial(t) for t in tags0],
                [mul(ODD,parity_polynomial(t)) for t in tags1]]
        tags=[tags0,tags1]
        pivots=[[tags0.index((i,j,0)) for i,n in enumerate([4,3,3,2]) for j in range(n)],
                [tags1.index((i,j,0)) for i,n in enumerate([3,3,2,1]) for j in range(n)]]
    else: raise ValueError('Unknown symmetry')
    es=monoms(d);polys=[p for g in groups for p in g]
    if len(polys)!=len(es): raise ArithmeticError('Wrong symmetry basis dimension')
    offsets=[];start=0
    for g in groups:
        offsets.append(start);start+=len(g)
    frees=[[i for i in range(len(g)) if i not in pp] for g,pp in zip(groups,pivots)]
    return dict(kind=kind,degree=d,monoms=es,groups=groups,tags=tags,pivots=pivots,
                frees=frees,offsets=offsets)


def raw_block(polys,other,weight,exps,name,standard=False):
    import numpy as np
    ei={e:i for i,e in enumerate(exps)};n=len(polys)
    entries={};den=1
    for i in range(n):
        for j in range(i,n):
            p=mul(polys[i],polys[j])
            if standard: p=add(p,scale(F(1,3),mul(other[i],other[j])))
            p=mul(p,weight)
            coeff={}
            for e,c in p.items():
                key=tuple(sorted(e))
                coeff[key]=coeff.get(key,F(0))+c
            # Sym averages coefficient across all distinct permutations.
            from math import factorial
            for key in coeff:
                counts=[key.count(z) for z in set(key)]
                orbit=6
                for c in counts: orbit//=factorial(c)
                coeff[key]/=orbit
                den=lcm(den,coeff[key].denominator)
            entries[i,j]=coeff
    raw=np.zeros((len(exps),n,n),dtype=np.int64)
    for (i,j),cs in entries.items():
        for e,c in cs.items(): raw[ei[e],i,j]=raw[ei[e],j,i]=int(c*den)
    if np.max(np.abs(raw))>=2**53: raise ArithmeticError('Large raw coefficient')
    return dict(name=name,raw=raw,den=den)


@lru_cache(None)
def raw_symmetry(kind,d,totaldegree):
    data=basis(kind,d)
    exps=[e for e in monoms(totaldegree) if tuple(sorted(e))==e]
    det=add(add(ONE,scale(2,E3)),scale(-1,add(add(mul(X[0],X[0]),mul(X[1],X[1])),mul(X[2],X[2]))))
    if kind=='s3':
        weight=ONE if d==totaldegree//2 else det
        g=data['groups']
        return [raw_block(g[0],None,weight,exps,'plus'),
                raw_block(g[1],None,weight,exps,'sign'),
                raw_block(g[2],g[3],weight,exps,'standard',True)]
    weight=add(ONE,scale(-1,mul(X[0],X[0])))
    return [raw_block(g,None,weight,exps,name) for g,name in zip(data['groups'],['even','odd'])]
