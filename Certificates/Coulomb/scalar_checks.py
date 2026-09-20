"""Integer interval checks for the root, squared minorant, and Gram uniqueness.
The exact divisibility of the squared-minorant polynomial follows from the
explicit interpolation formula; small remainders are
never accepted as zero. No Lean compilation is performed.
"""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
import itertools,json
from dyadic import I,SCALE,BITS
ROOT=Path(__file__).resolve().parent
LEFT=Q('0.3140893678892018673812332')
RIGHT=Q('0.3140893678892018673812333')

def require(p,m):
 if not p:raise ArithmeticError(m)

def family_derivative(s):
 q=I.rat(2).sqrt();dm=2-q+(2+q)*s;dp=2+q+(2-q)*s
 return (2*q+1)/((1-s)*(1-s).sqrt())-4*(2+q)/(dm*dm.sqrt())-4*(2-q)/(dp*dp.sqrt())

def constants():
 l=I.rat(LEFT);r=I.rat(RIGHT)
 require(0<LEFT<RIGHT<Q(1,3),'Root bracket range')
 require(family_derivative(l).hi<0<family_derivative(r).lo,'Root signs')
 a=I(l.lo,r.hi);q=I.rat(2).sqrt()
 nodes=[a,2*a-1,-a+(1-a)/q,-a-(1-a)/q]
 require(all(-SCALE<t.lo<=t.hi<SCALE for t in nodes),'Interior nodes')
 for i,j in itertools.product(range(4),repeat=2):
  require((nodes[i]+nodes[j]).nonzero(),'Opposite nodes')
  if i!=j:require((nodes[i]-nodes[j]).nonzero(),'Distinct nodes')
 return a,q,nodes

def add(p,q):
 r=[I(0)]*max(len(p),len(q))
 for i,x in enumerate(p):r[i]=r[i]+x
 for i,x in enumerate(q):r[i]=r[i]+x
 return r

def scale(p,s):return [s*x for x in p]
def mul(p,q):
 r=[I(0)]*(len(p)+len(q)-1)
 for i,a in enumerate(p):
  for j,b in enumerate(q):r[i+j]=r[i+j]+a*b
 return r

def evalpoly(p,x):
 r=I(0)
 for c in reversed(p):r=r*x+c
 return r

def deriv(p):return [i*p[i] for i in range(1,len(p))]

def hermite(nodes):
 # T4(t) = (1/2) sum_{j=0}^4 binom(2j,j) (t+1)^j / 8^j.
 T=[I(0)];power=[I.rat(1)]
 for j in range(5):
  T=add(T,scale(power,Q(comb(2*j,j),2*8**j)))
  power=mul(power,[I.rat(1),I.rat(1)])
 R=[I(0)]
 for i,t in enumerate(nodes):
  phi=1/(2-2*t).sqrt();s=t+1
  value=(phi-evalpoly(T,t))/s**5
  slope=(phi/(2-2*t)-evalpoly(deriv(T),t)-5*s**4*value)/s**5
  L=[I.rat(1)]
  for j,u in enumerate(nodes):
   if i!=j:L=scale(mul(L,[-u,I.rat(1)]),1/(t-u))
  ld=evalpoly(deriv(L),t)
  linear=add([value],scale([-t,I.rat(1)],slope-2*value*ld))
  R=add(R,mul(linear,mul(L,L)))
 return add(T,mul(power,R))

def squared_minorant(nodes,h):
 P=scale(mul([I.rat(2),I.rat(-2)],mul(h,h)),-1);P[0]=P[0]+1
 M=[I.rat(1)]
 for _ in range(5):M=mul(M,[I.rat(1),I.rat(1)])
 for t in nodes:
  M=mul(M,mul([-t,I.rat(1)],[-t,I.rat(1)]))
 quotient=[I(0)]*13
 # Monic division encloses quotient. Divisibility is an algebraic theorem.
 for k in range(12,-1,-1):
  quotient[k]=P[k+13]
  for j in range(14):P[k+j]=P[k+j]-quotient[k]*M[j]
 # Convert Q(2x-1) from powers to the degree-12 Bernstein basis on [0,1].
 shifted=[sum((quotient[j]*(comb(j,k)*(-1)**(j-k)*2**k) for j in range(k,13)),I(0)) for k in range(13)]
 bernstein=[sum((shifted[k]*Q(comb(i,k),comb(12,k)) for k in range(i+1)),I(0)) for i in range(13)]
 require(all(x.lo>0 for x in bernstein),'Minorant Bernstein coefficient positivity')
 return quotient,bernstein

CODES=[[0,1,2,1,3,4,4,3],[1,0,1,2,3,3,4,4],[2,1,0,1,4,3,3,4],
 [1,2,1,0,4,4,3,3],[3,3,4,4,0,1,2,1],[4,3,3,4,1,0,1,2],
 [4,4,3,3,2,1,0,1],[3,4,4,3,1,2,1,0]]

def gramdet(u,v,t):return 1+2*u*v*t-u*u-v*v-t*t

def gramres(u,v,t,a,b,c):
 return (1-t*t)*a*a+(1-v*v)*b*b+(1-u*u)*c*c+2*(v*t-u)*a*b+2*(u*t-v)*a*c+2*(u*v-t)*b*c-gramdet(u,v,t)

def uniqueness(nodes):
 excluded=compatible=0
 for indices in itertools.product(range(4),repeat=3):
  u,v,t=[nodes[j] for j in indices]
  require(gramdet(u,v,t).nonzero(),'Singular anchor Gram matrix')
  anchors=[(i,j,k) for i,j,k in itertools.permutations(range(8),3)
   if (CODES[i][j]-1,CODES[i][k]-1,CODES[j][k]-1)==indices]
  anchor=anchors[0] if anchors else None
  for abc in itertools.product(range(4),repeat=3):
   matches=[]
   if anchor:
    i,j,k=anchor
    matches=[w for w in range(8) if w not in anchor and
     (CODES[i][w]-1,CODES[j][w]-1,CODES[k][w]-1)==abc]
   if matches:compatible+=1
   else:
    require(gramres(u,v,t,*[nodes[j] for j in abc]).nonzero(),'Unclassified Gram extension')
    excluded+=1
 return {'anchor_cases':64,'extension_cases':4096,'compatible_extensions':compatible,'excluded_extensions':excluded}

def main():
 a,q,nodes=constants();h=hermite(nodes);quotient,bern=squared_minorant(nodes,h)
 report={'bits':BITS,'root_bracket':[str(LEFT),str(RIGHT)],
  'root_signs':[family_derivative(I.rat(LEFT)).encode(),family_derivative(I.rat(RIGHT)).encode()],
  'hermite_coefficients': [x.encode() for x in h],
  'squared_minorant_quotient':[x.encode() for x in quotient],
  'positive_Bernstein_coefficients':[x.encode() for x in bern],
  'minimum_Bernstein_lower_numerator':str(min(x.lo for x in bern)),
  'uniqueness':uniqueness(nodes),'all_checks_passed':True}
 (ROOT/'scalar_verification.json').write_text(json.dumps(report,indent=2)+'\n')
 print('PASS: rational root signs, 13 positive Bernstein coefficients, and 4096 Gram cases.')
 print('Minimum Bernstein lower bound >',str(Q(min(x.lo for x in bern),SCALE)))
 print(report['uniqueness'])

if __name__=='__main__':main()
