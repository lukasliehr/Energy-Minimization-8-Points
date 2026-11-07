"""Exact seventeen contact-jet coordinates and fifteen moment columns."""
from itertools import permutations

from rational_field import R, VARIABLE, SQRT2
from analytic_basis import moment_coefficients

ORBITS = ((0,0,1),(0,2,2),(0,3,3),(0,2,3),(1,2,3))
COUNTS = (8,8,8,16,16)


class Jet:
    __slots__ = ('v','g')
    def __init__(self,v=0,g=None):
        if isinstance(v,Jet):
            self.v,self.g=v.v,v.g
        else:
            self.v=R(v);self.g=tuple(R(x) for x in (g or (0,0,0)))
    def __add__(self,o):
        o=Jet(o);return Jet(self.v+o.v,[a+b for a,b in zip(self.g,o.g)])
    __radd__=__add__
    def __neg__(self):return Jet(-self.v,[-x for x in self.g])
    def __sub__(self,o):return self+-Jet(o)
    def __rsub__(self,o):return Jet(o)+-self
    def __mul__(self,o):
        o=Jet(o);return Jet(self.v*o.v,[a*o.v+self.v*b for a,b in zip(self.g,o.g)])
    __rmul__=__mul__
    def __truediv__(self,o):
        if isinstance(o,Jet):
            raise ValueError('Only constant division is needed')
        return self*R(o).inverse()
    def __pow__(self,n):
        if n<0:raise ValueError('Polynomial jets only')
        out=Jet(1);base=self
        while n:
            if n&1:out*=base
            base*=base;n//=2
        return out


def nodes(a):
    return (a,2*a-1,-a+(1-a)*SQRT2/2,-a-(1-a)*SQRT2/2)


def evaluate_poly(c,x):
    y=x*0
    for v in reversed(c):y=y*x+v
    return y


def moment_basis(a,d,k,p=None):
    pp=[evaluate_poly(moment_coefficients(k,i),a) for i in range(d-k+1)]
    if p is None:p=next(i for i,x in enumerate(pp) if x)
    if not pp[p]:
        raise ArithmeticError('Zero symbolic moment pivot')
    out=[]
    for i in range(d-k+1):
        if i==p:continue
        f=[R(0) for _ in pp];f[i]=R(1);f[p]=-pp[i]/pp[p];out.append((i,f))
    return out


def Q(k,u,v,t):
    if not k:return Jet(1)
    base=t-u*v
    if k==1:return base
    aa=(1-u*u)*(1-v*v);old,cur=Jet(1),base
    for _ in range(2,k+1):old,cur=cur,2*base*cur-aa*old
    return cur


def sym6(k,f,h,point):
    return sum((evaluate_poly(f,point[p[0]])*evaluate_poly(h,point[p[1]])*
                Q(k,point[p[0]],point[p[1]],point[p[2]])
                for p in permutations(range(3))),Jet(0))


def moment_polynomial_jet(k,f,h,point):
    out=sym6(k,f,h,point)
    out+=sum((sym6(k,f,h,(x,x,Jet(1)))/6 for x in point),Jet(0))
    if k==0:out+=evaluate_poly(f,Jet(1))*evaluate_poly(h,Jet(1))/7
    return out


def column(a,k,f,h):
    ns=nodes(a);out=[]
    for orbit in ORBITS:
        point=[Jet(ns[label],[int(j==i) for j in range(3)]) for i,label in enumerate(orbit)]
        z=moment_polynomial_jet(k,f,h,point);out.append(z.v)
        for label in sorted(set(orbit)):
            out.append(sum((z.g[j] for j in range(3) if orbit[j]==label),R()))
    if len(out)!=17:
        raise ArithmeticError('Wrong contact-jet dimension')
    return out
