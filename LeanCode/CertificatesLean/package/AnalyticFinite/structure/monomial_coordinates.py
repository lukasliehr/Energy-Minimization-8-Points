"""Constructive monomial coordinates in the fixed S3 polynomial basis.
Only additions, products, and rational divisions by2,3,9 are used.
The proof is even/odd decomposition, symmetric polynomial recurrences,
and reduction by u^3-sigma*u^2+e2*u-e3.
"""
from fractions import Fraction as F
from functools import lru_cache
import canonical as c
ONE=c.ONE;SIG={(1,0,0):F(1)};E2={(0,1,0):F(1)};E3={(0,0,1):F(1)}

def ua(p,q):
 out=dict(p)
 for n,v in q.items():out[n]=c.add(out.get(n,{}),v)
 return {n:v for n,v in out.items() if v}
def us(a,p):return {n:c.scale(a,v) for n,v in p.items() if a and v}
def um(p,q):
 out={}
 for n,a in p.items():
  for m,b in q.items():out[n+m]=c.add(out.get(n+m,{}),c.mul(a,b))
 return {n:v for n,v in out.items() if v}
def up(p,n):
 out={0:ONE}
 for _ in range(n):out=um(out,p)
 return out
Z={0:SIG,1:c.scale(-1,ONE)};W={0:E2,1:c.scale(-1,SIG),2:ONE}
def symmetric_power(n):
 if n==0:return {0:c.scale(2,ONE)}
 if n==1:return Z
 return ua(um(Z,symmetric_power(n-1)),us(-1,um(W,symmetric_power(n-2))))
def divided_difference(n):
 if n==0:return {0:ONE}
 if n==1:return Z
 return ua(um(Z,divided_difference(n-1)),us(-1,um(W,divided_difference(n-2))))
def reduce(p):
 p=dict(p)
 for n in range(max(p,default=-1),2,-1):
  v=p.pop(n,{})
  for k,factor,sign in [(n-1,SIG,1),(n-2,E2,-1),(n-3,E3,1)]:p[k]=c.add(p.get(k,{}),c.scale(sign,c.mul(v,factor)))
 return [p.get(i,{}) for i in range(3)]
@lru_cache(None)
def components(e):
 a,b,d=e;power=abs(b-d);common=um({a:ONE},up(W,min(b,d)))
 L,M,N=reduce(us(F(1,2),um(common,symmetric_power(power))))
 trivial=c.add(c.add(L,c.scale(F(1,3),c.mul(SIG,M))),c.scale(F(1,3),c.mul(c.add(c.mul(SIG,SIG),c.scale(-2,E2)),N)))
 plusF=c.add(M,c.scale(F(2,3),c.mul(SIG,N)));plusG=N
 L,M,N=reduce({} if not power else us(F(1 if b>d else -1,2),um(common,divided_difference(power-1))))
 sign=c.scale(F(1,3),N)
 minusG=c.add(c.scale(-1,M),c.scale(-F(2,3),c.mul(SIG,N)))
 minusF=c.add(c.add(L,c.scale(-F(1,3),c.mul(SIG,minusG))),c.scale(-F(1,3),c.mul(E2,N)))
 return trivial,sign,plusF,plusG,minusF,minusG

def coordinates(e,desc):
 t,s,p,q,r,z=components(e)
 return [[t.get(tag,F(0)) for tag in desc['tags'][0]],
         [s.get(tag,F(0)) for tag in desc['tags'][1]],
         [(p if tag[0]==0 else q).get(tag[1:],F(0)) for tag in desc['tags'][2]],
         [(r if tag[0]==0 else z).get(tag[1:],F(0)) for tag in desc['tags'][3]]]
