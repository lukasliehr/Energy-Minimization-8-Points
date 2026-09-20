"""Exact rational polynomials and coefficient reconstruction.
Default arithmetic: Python Fraction. COULOMB_FAST=1 selects optional FLINT.
Neither backend uses floating-point coefficients.
"""
import os,itertools
from fractions import Fraction
FAST=os.environ.get('COULOMB_FAST')=='1'
if FAST:
 from flint import fmpq as Q,fmpq_poly
else:Q=Fraction

class P:
 __slots__=('c',)
 def __init__(self,x=0):
  if isinstance(x,P):self.c=x.c;return
  if not isinstance(x,(list,tuple)):x=[x]
  vals=[Q(str(v)) for v in x]
  if FAST:self.c=fmpq_poly(vals)
  else:
   while vals and not vals[-1]:vals.pop()
   self.c=tuple(vals)
 @classmethod
 def raw(cls,x):
  r=object.__new__(cls);r.c=x;return r
 def __bool__(self):return bool(self.c)
 def __eq__(self,x):return self.c==P(x).c
 def __neg__(self):return P.raw(-self.c) if FAST else P([-v for v in self.c])
 def __add__(self,x):
  x=P(x)
  if FAST:return P.raw(self.c+x.c)
  out=list(self.c)+[Q(0)]*max(0,len(x.c)-len(self.c))
  for i,v in enumerate(x.c):out[i]+=v
  return P(out)
 __radd__=__add__
 def __sub__(self,x):return self+-P(x)
 def __rsub__(self,x):return P(x)+-self
 def __mul__(self,x):
  x=P(x)
  if FAST:return P.raw(self.c*x.c)
  if not self or not x:return P(0)
  r=[Q(0)]*(len(self.c)+len(x.c)-1)
  for i,a in enumerate(self.c):
   for j,b in enumerate(x.c):r[i+j]+=a*b
  return P(r)
 __rmul__=__mul__
 def __truediv__(self,x):
  if isinstance(x,P):raise TypeError("Polynomial division is not used by the checker")
  return self*(Q(1)/Q(str(x)))
 def __pow__(self,n):
  r=P(1);a=self
  while n:
   if n&1:r=r*a
   a=a*a;n//=2
  return r
 def derivative(self):
  if FAST:return P.raw(self.c.derivative())
  return P([i*self.c[i] for i in range(1,len(self.c))])
 def values(self):return list(self.c)
 def encode(self):return [str(c) for c in self.values()] or ['0']
 def evaluate(self,x):
  r=x*0
  for c in reversed(self.values()):r=r*x+Fraction(str(c))
  return r

ZERO=(0,0,0)
PERMS=list(itertools.permutations(range(3)))
EXPS=[e for e in itertools.product(range(13),repeat=3) if tuple(sorted(e))==e and sum(e)<=12]
INDEX={e:i for i,e in enumerate(EXPS)}
TYPES=[(3,3,0),(3,1,2),(3,2,0),(1,0,0),(2,2,0)]
COUNTS=[8,16,16,8,8]

def add(p,q,scale=1):
 r=p.copy()
 for e,c in q.items():
  r[e]=r.get(e,0)+c*scale
  if not r[e]:del r[e]
 return r

def mul(p,q):
 r={}
 for e,c in p.items():
  for f,d in q.items():
   g=tuple(a+b for a,b in zip(e,f));r[g]=r.get(g,0)+c*d
 return {e:c for e,c in r.items() if c}

def sym(p):
 r={}
 for permutation in PERMS:
  for e,c in p.items():
   f=tuple(e[j] for j in permutation);r[f]=r.get(f,0)+c*Fraction(1,6)
 return {e:c for e,c in r.items() if c}

def raw_moment(k):
 one={ZERO:Fraction(1)}
 u,v,t=[{tuple(int(i==j) for i in range(3)):Fraction(1)} for j in range(3)]
 base=add(t,mul(u,v),-1);factor=mul(add(one,mul(u,u),-1),add(one,mul(v,v),-1))
 kernel=[one,base]
 for j in range(2,k+1):kernel.append(add({e:2*c for e,c in mul(base,kernel[-1]).items()},mul(factor,kernel[-2]),-1))
 m=7-k;out=[]
 for i in range(m):
  row=[]
  for j in range(m):
   sp=sym(mul({(i,j,0):Fraction(1)},kernel[k]));r={e:6*c for e,c in sp.items()}
   for axis in range(3):
    for e,c in sp.items():
     f=tuple(e[0]+e[1] if a==axis else 0 for a in range(3));r[f]=r.get(f,0)+c
   if k==0:r[ZERO]=r.get(ZERO,0)+Fraction(1,7)
   r={e:c for e,c in r.items() if c}
   if any(sum(e)>12 for e in r):raise ArithmeticError('Moment degree above 12')
   for e,c in r.items():
    if any(r.get(f,0)!=c for f in set(itertools.permutations(e))):
     raise ArithmeticError('Moment polynomial is not symmetric')
   row.append({e:c for e,c in r.items() if e in INDEX})
  out.append(row)
 if any(out[i][j]!=out[j][i] for i in range(m) for j in range(m)):
  raise ArithmeticError('Moment matrix is not symmetric')
 return out

def block_columns(b):
 cols=[]
 if b['kind']=='moment':
  N=[[P(c) for c in row] for row in b['basis']];r=len(N[0]);raw=raw_moment(b['k'])
  for i in range(r):
   for j in range(i,r):
    col={}
    for a in range(len(N)):
     for c in range(len(N)):
      v=N[a][i]*N[c][j]*(1 if i==j else 2)
      if v:
       for e,q in raw[a][c].items():col=add(col,{INDEX[e]:v},q)
    cols.append(col)
 else:
  for p in b['polys']:
   es=[tuple(e) for e,c in p]
   if len(set(es))!=len(es) or any(len(e)!=3 or any(type(j)!=int or j<0 for j in e) for e in es):
    raise ArithmeticError('Invalid or duplicate SOS exponent')
   if any(sum(e)>6-b['weight'] for e in es):raise ArithmeticError('SOS basis degree')
  polys=[{tuple(e):P(c) for e,c in p} for p in b['polys']]
  weight={ZERO:Fraction(1)}
  if b['weight']==1:weight[(2,0,0)]=Fraction(-1)
  elif b['weight']!=0:raise ArithmeticError('Unsupported weight')
  for i,p in enumerate(polys):
   for j in range(i,len(polys)):
    col={}
    for e,c in mul(weight,mul(p,polys[j])).items():
     can=tuple(sorted(e))
     if can not in INDEX:raise ArithmeticError('Degree above 12')
     orbit=len(set(itertools.permutations(e)))
     col=add(col,{INDEX[can]:c},Fraction(1 if i==j else 2,orbit))
    cols.append(col)
 return cols

def pairadd(x,y):return x[0]+y[0],x[1]+y[1]
def pairmul(x,y):return x[0]*y[0]+2*x[1]*y[1],x[0]*y[1]+x[1]*y[0]

def check_candidate_geometry(codes):
 """Verify the color table and pair/triangle multiplicities over Q[s,sqrt(2)]."""
 s=P([0,1]);z=(P(),P());one=(P(1),P());neg=(-P(1),P())
 halfq=(P(),P(Fraction(1,2)));minusq=(P(),P(Fraction(-1,2)))
 xy=[(one,z),(z,one),(neg,z),(z,neg),
     (halfq,halfq),(minusq,halfq),(minusq,minusq),(halfq,minusq)]
 nodes=[(P(1),P()),(s,P()),(2*s-1,P()),
        (-s,(1-s)*Fraction(1,2)),(-s,(s-1)*Fraction(1,2))]
 if len(codes)!=8 or any(len(row)!=8 for row in codes):raise ArithmeticError('Color table shape')
 for i,j in itertools.product(range(8),repeat=2):
  horizontal=pairadd(pairmul(xy[i][0],xy[j][0]),pairmul(xy[i][1],xy[j][1]))
  vertical=s*(1 if (i<4)==(j<4) else -1)
  gram=((1-s)*horizontal[0]+vertical,(1-s)*horizontal[1])
  if gram!=nodes[codes[i][j]]:raise ArithmeticError('Candidate Gram table')
 pairs=[sum(codes[i][j]==c for i,j in itertools.combinations(range(8),2)) for c in range(1,5)]
 counts={}
 for i,j,k in itertools.combinations(range(8),3):
  key=tuple(sorted([codes[i][j]-1,codes[i][k]-1,codes[j][k]-1]))
  counts[key]=counts.get(key,0)+1
 if pairs!=[8,4,8,8] or counts!={tuple(sorted(t)):n for t,n in zip(TYPES,COUNTS)}:
  raise ArithmeticError('Candidate contact multiplicities')

def annihilators():
 s=P([0,1]);nodes=[(s,P()),(2*s-1,P()),(-s,(1-s)*Fraction(1,2)),(-s,(s-1)*Fraction(1,2))]
 powers=[]
 for t in nodes:
  ps=[(P(1),P())]
  for i in range(12):ps.append(pairmul(ps[-1],t))
  powers.append(ps)
 L=[]
 for e in EXPS:
  val=(P(),P())
  for tt,n in zip(TYPES,COUNTS):
   for ex in set(itertools.permutations(e)):
    p=(P(1),P())
    for j,k in zip(tt,ex):p=pairmul(p,powers[j][k])
    val=pairadd(val,(6*n*p[0],6*n*p[1]))
  if val[1]:raise ArithmeticError('Nonrational annihilator')
  L.append(val[0])
 return L,[x.derivative() for x in L]

def check_annihilators(cols):
 L0,L1=annihilators()
 if L0[INDEX[ZERO]]!=336 or L1[INDEX[ZERO]]!=0 or L1[INDEX[(0,0,2)]]!=P([-1152,3456]):raise ArithmeticError('Completion identities')
 for j,col in enumerate(cols):
  for L in [L0,L1]:
   if sum((L[i]*c for i,c in col.items()),P()):raise ArithmeticError('Coefficient annihilator '+str(j))
 return L0,L1
