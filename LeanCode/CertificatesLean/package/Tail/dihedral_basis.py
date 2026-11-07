"""Explicit real Fourier polynomial bases for the proved D8 slice action.

All coefficients lie in Q(sqrt(2)). No Gram--Schmidt, eigenproblem,
linear solve, or nonzero-pivot test is used to construct these bases.
"""
from fractions import Fraction as F
from itertools import combinations_with_replacement

class K:
    __slots__ = ('a','b')
    def __init__(self,a=0,b=0):
        if isinstance(a,K): self.a,self.b=a.a,a.b
        else:self.a,self.b=F(a),F(b)
    def __add__(self,o):
        o=K(o);return K(self.a+o.a,self.b+o.b)
    __radd__=__add__
    def __neg__(self):return K(-self.a,-self.b)
    def __sub__(self,o):return self+-K(o)
    def __rsub__(self,o):return K(o)+-self
    def __mul__(self,o):
        o=K(o);return K(self.a*o.a+2*self.b*o.b,self.a*o.b+self.b*o.a)
    __rmul__=__mul__
    def __truediv__(self,o):
        o=K(o);n=o.a*o.a-2*o.b*o.b
        return self*K(o.a/n,-o.b/n)
    def __eq__(self,o):
        o=K(o);return self.a==o.a and self.b==o.b
    def __bool__(self):return bool(self.a or self.b)
    def __repr__(self):return f'K({self.a},{self.b})'

T=K(0,1)
ZERO=K()
ONE=K(1)

class C:
    __slots__=('re','im')
    def __init__(self,re=0,im=0):
        if isinstance(re,C):self.re,self.im=re.re,re.im
        else:self.re,self.im=K(re),K(im)
    def __add__(self,o):o=C(o);return C(self.re+o.re,self.im+o.im)
    __radd__=__add__
    def __mul__(self,o):o=C(o);return C(self.re*o.re-self.im*o.im,self.re*o.im+self.im*o.re)
    __rmul__=__mul__
    def conj(self):return C(self.re,-self.im)
    def __bool__(self):return bool(self.re or self.im)


def add_poly(out,mon,c):
    out[mon]=out.get(mon,C())+c
    if not out[mon]:del out[mon]


def multiply(p,q):
    out={}
    for u,x in p.items():
        for v,y in q.items():add_poly(out,tuple(sorted(u+v)),x*y)
    return out


def complex_variables():
    # Each entry: frequency, reflection sign, sparse complex linear form.
    v=[(0,1,{(0,):C(1)})]
    for k,phi,m in [(1,(2,1),(3,4)),(2,(6,5),(7,8)),(3,(9,10),None)]:
        v.append((k,1,{(phi[0],):C(T/2),(phi[1],):C(0,-T/2)}))
        if m:v.append((k,1,{(m[0],):C(T/2),(m[1],):C(0,T/2)}))
    v.extend([(4,-1,{(11,):C(1)}),(4,1,{(12,):C(1)})])
    for k,sign,p in list(v)[1:6][::-1]:
        v.append((8-k,sign,{m:x.conj() for m,x in p.items()}))
    conjugate=[]
    for k,sign,p in v:
        target={m:x.conj() for m,x in p.items()}
        for j,(_,_,q) in enumerate(v):
            if set(q)==set(target) and all(q[m].re==target[m].re and q[m].im==target[m].im for m in q):
                conjugate.append(j);break
        else:raise AssertionError('missing conjugate variable')
    return v,conjugate


def polynomial_basis(degree):
    """Blocks: (name, copies of equally sized lists of sparse polynomials).

    Within each nonreal frequency, copy0 is reflection-even and copy1
    reflection-odd. Every row is orthonormal for the monomial weights
    1 (degree0/1/diagonal square), sqrt2 (off-diagonal quadratic).
    """
    if degree not in (1,2):raise ValueError('degree1 or2 required')
    v,bar=complex_variables()
    keys=[()]+[(i,) for i in range(13)]
    if degree==2:keys+=list(combinations_with_replacement(range(13),2))
    done=set();blocks={name:[[],[]] if name in ('1','2','3') else [[]]
                      for name in ('0+','0-','4+','4-','1','2','3')}
    for key in keys:
        if key in done:continue
        conjugate=tuple(sorted(bar[i] for i in key));done.add(key);done.add(conjugate)
        frequency=sum(v[i][0] for i in key)%8
        if frequency>4:key,conjugate=conjugate,key;frequency=8-frequency
        sign=1;p={():C(1)}
        for i in key:sign*=v[i][1];p=multiply(p,v[i][2])
        if len(key)==2 and key[0]!=key[1]:p={m:x*T for m,x in p.items()}
        if frequency in (1,2,3):
            if sign==-1:p={m:C(0,1)*x for m,x in p.items()}
            for slot in (0,1):
                row={m:T*(x.re if slot==0 else x.im) for m,x in p.items()}
                blocks[str(frequency)][slot].append({m:x for m,x in row.items() if x})
        elif key==conjugate:
            if any(x.im for x in p.values()):raise AssertionError('nonreal self-conjugate monomial')
            blocks[str(frequency)+('+' if sign==1 else '-')][0].append({m:x.re for m,x in p.items() if x.re})
        else:
            for slot in (0,1):
                row={m:T*(x.re if slot==0 else x.im) for m,x in p.items()}
                parity=sign if slot==0 else -sign
                blocks[str(frequency)+('+' if parity==1 else '-')][0].append({m:x for m,x in row.items() if x})
    return [(name,copies) for name,copies in blocks.items() if copies[0]]


def linear_action(power=1,reflection=False):
    """The14x14 action on (1,z) of S^power F^reflection."""
    cs=[ONE,T/2,ZERO,-T/2,-ONE,-T/2,ZERO,T/2]
    sn=[ZERO,T/2,ONE,T/2,ZERO,-T/2,-ONE,-T/2]
    A=[[ZERO for _ in range(14)]for _ in range(14)]
    A[0][0]=A[1][1]=ONE
    for k,i,j,orientation in [(1,1,2,1),(1,3,4,1),(2,5,6,1),(2,7,8,1),(3,9,10,-1)]:
        c,s=cs[k*power%8],orientation*sn[k*power%8]
        A[i+1][i+1]=A[j+1][j+1]=c
        A[i+1][j+1]=-s;A[j+1][i+1]=s
    A[12][12]=A[13][13]=K((-1)**power)
    if reflection:
        signs=[1,1,-1,1,1,-1,-1,1,1,-1,1,-1,-1,1]
        A=[[x*signs[j] for j,x in enumerate(row)]for row in A]
    return A


