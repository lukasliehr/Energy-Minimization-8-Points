"""Analytic small interpolation kernels in fixed symmetry coordinates."""
from fractions import Fraction as F
from functools import lru_cache
from math import comb
import numpy as np
from rational_field import VARIABLE as A0,SQRT2,R
from canonical import basis,fraction


def add(p,q):
    out=dict(p)
    for e,c in q.items():out[e]=out.get(e,0)+c
    return {e:c for e,c in out.items() if c}


def mul(p,q):
    out={}
    for e,c in p.items():
        for f,d in q.items():
            ef=tuple(a+b for a,b in zip(e,f))
            out[ef]=out.get(ef,0)+c*d
    return {e:c for e,c in out.items() if c}


def scale(c,p):return {e:c*v for e,v in p.items() if c*v}


def univariate(nodes,values):
    result=[R(0) for _ in nodes]
    for i,x in enumerate(nodes):
        p=[R(1)];den=R(1)
        for j,y in enumerate(nodes):
            if i==j:continue
            q=[R(0)]*(len(p)+1)
            for k,c in enumerate(p):q[k]-=y*c;q[k+1]+=c
            p=q;den*=x-y
        for k,c in enumerate(p):result[k]+=values[i]*c/den
    return result


def sym_value(tag,x):
    i,j,k=tag;u,v,t=x
    return (u+v+t)**i*(u*v+u*t+v*t)**j*(u*v*t)**k


def parity_value(tag,x):
    i,j,k=tag;u,v,t=x
    return u**i*(v+t)**j*(v*t)**k


def standard_interpolate(Fs,Gs,sig,lam):
    f=univariate(sig[3:],[Fs[3],Fs[4]])
    g=univariate(sig[3:],[Gs[3],Gs[4]])
    H=lambda x:(x+A0)*(x+1)
    residual=[(Fs[i]+lam[i]*Gs[i]-(f[0]+f[1]*sig[i])-
               lam[i]*(g[0]+g[1]*sig[i]))/H(sig[i]) for i in range(3)]
    slope=(residual[1]-residual[2])/(sig[1]-sig[2])
    intercept=residual[1]-slope*sig[1]
    gamma=(residual[0]-intercept-slope*sig[0])*2/(A0-1)
    beta=slope+gamma/6;alpha=intercept-gamma*A0/2
    h=[A0,A0+1,R(1)]
    ff=f+[R(0),R(0)];gg=g+[R(0)]
    for k,c in enumerate(h):ff[k]+=alpha*c;ff[k+1]+=beta*c;gg[k]+=gamma*c
    return ff+gg


def parity_interpolate(values,points,order):
    output={};factor={(0,0,0):R(1)}
    for label in order:
        indices=[i for i,p in enumerate(points) if p[0]==label]
        u=NODE[label]
        zs=[sum(NODE[j] for j in points[i][1:]) for i in indices]
        vv=[]
        for i,z in zip(indices,zs):
            existing=sum(c*u**e[0]*z**e[1] for e,c in output.items())
            div=sum(c*u**e[0] for e,c in factor.items())
            vv.append((values[i]-existing)/div)
        p={(0,j,0):c for j,c in enumerate(univariate(zs,vv))}
        output=add(output,mul(factor,p))
        factor=mul(factor,{(1,0,0):R(1),(0,0,0):-u})
    return output


NODE=[A0,2*A0-1,-A0+(1-A0)*SQRT2/2,-A0-(1-A0)*SQRT2/2]
ORBT=[(0,0,1),(0,2,2),(0,3,3),(0,2,3),(1,2,3)]
ORB=[tuple(NODE[i] for i in p) for p in ORBT]
SIG=[sum(x) for x in ORB]
LAM=[(A0-1)/3,A0/2-SIG[1]/6,A0/2-SIG[2]/6]


@lru_cache(None)
def symbolic_kernels(kind,d):
    data=basis(kind,d);answers=[]
    for group,(tags,pivots,free) in enumerate(zip(data['tags'],data['pivots'],data['frees'])):
        if kind=='s3' and group==3:answers.append(answers[2]);continue
        matrix=[[R(int(i==f)) for f in free] for i in range(len(tags))]
        for j,f in enumerate(free):
            tag=tags[f]
            if kind=='s3':
                if group==0:coeff=univariate(SIG,[sym_value(tag,x) for x in ORB])
                elif group==1:coeff=univariate(SIG[3:],[sym_value(tag,x) for x in ORB[3:]])
                else:
                    values=[sym_value(tag[1:],x) for x in ORB]
                    zeros=[R(0)]*5
                    coeff=standard_interpolate(values if tag[0]==0 else zeros,
                                               values if tag[0]==1 else zeros,SIG,LAM)
            else:
                from interpolation import POINTS
                points=[p for p in POINTS if p[1]<=p[2] and (group==0 or p[1]!=p[2])]
                vals=[parity_value(tag,tuple(NODE[i] for i in p)) for p in points]
                poly=parity_interpolate(vals,points,[0,2,3,1] if group==0 else [2,3,0,1])
                coeff=[poly.get(tags[i],R(0)) for i in pivots]
            for i,c in zip(pivots,coeff):matrix[i][j]=-c
        answers.append(matrix)
    return answers


class Evaluator:
    """Exact recentering and factored scalar denominators, coherent TMs."""
    def __init__(self,A):
        from taylor_models import TM,iv,ORDER
        self.TM,self.iv,self.order=TM,iv,ORDER
        self.A=A;self.center=F.from_float(float(A.c[0]));self.sqrt2=iv.sqrt(2)
        self.powers=[TM.const(1)];self.U=A-TM.const(iv.mpf(self.center))
        self.poly_cache={};self.inverse_cache={};self.rational_cache={}

    def polynomial(self,p):
        key=tuple(fraction(c) for c in p)
        if key in self.poly_cache:return self.poly_cache[key]
        coeff=[]
        for j in range(len(key)):
            coeff.append(sum((key[k]*comb(k,j)*self.center**(k-j) for k in range(j,len(key))),F(0)))
        while len(self.powers)<len(key):self.powers.append(self.powers[-1]*self.U)
        c=[sum((self.iv.mpf(q)*self.powers[j].c[k] for j,q in enumerate(coeff)),self.iv.mpf(0)) for k in range(self.order+1)]
        error=sum((abs(self.iv.mpf(q)).b*self.powers[j].e for j,q in enumerate(coeff)),self.iv.mpf(0))
        out=self.TM(c,error);self.poly_cache[key]=out;return out

    def inverse(self,p):
        key=tuple(fraction(c) for c in p)
        if key in self.inverse_cache:return self.inverse_cache[key]
        unit,factors=p.factor()
        product=p*0+unit
        for factor,exponent in factors:product*=factor**exponent
        if product!=p:raise ArithmeticError('Exact scalar denominator factor identity failed')
        out=self.TM.const(self.iv.mpf(fraction(unit))).inverse()
        for factor,exponent in factors:out*=self.polynomial(factor).inverse()**exponent
        self.inverse_cache[key]=out;return out

    def rational(self,r):
        key=(tuple(r.p),tuple(r.q),tuple(r.d))
        if key not in self.rational_cache:
            if not r.p and not r.q:
                out=self.TM.const(0)
            elif len(r.p)<=1 and not r.q and len(r.d)==1:
                out=self.TM.const(self.iv.mpf(fraction(r.p[0] if r.p else 0))/
                                  self.iv.mpf(fraction(r.d[0])))
            else:
                numerator=self.polynomial(r.p)
                if r.q:
                    numerator=numerator+self.polynomial(r.q)*self.sqrt2
                out=numerator*self.inverse(r.d)
            self.rational_cache[key]=out
        return self.rational_cache[key]


def models(kind,d,A,evaluator=None):
    from matrix_models import MT
    from ipoly import IP
    data=basis(kind,d);ev=Evaluator(A) if evaluator is None else evaluator;out=[]
    if ev.A is not A:
        raise ValueError('Shared evaluator has a different height model')
    for group,matrix in enumerate(symbolic_kernels(kind,d)):
        if kind=='s3' and group==3:out.append(out[2]);continue
        if not data['frees'][group]:out.append(None);continue
        M=MT.from_scalars([[ev.rational(r) for r in row] for row in matrix])
        B=IP.fromMT(M)
        B.canonical_coefficients=M.c
        B.active_rows=data['pivots'][group]
        out.append(B)
    return out
