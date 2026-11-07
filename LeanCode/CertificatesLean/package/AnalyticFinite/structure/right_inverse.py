"""Exact structural coefficient formulas underlying the normalized operator.

All small inverses are formed over Q(sqrt(2))(a); their nonvanishing is the
universal determinant theorem, not a parameter-wise numerical inverse gate.
"""
from fractions import Fraction as F
from functools import lru_cache
from rational_field import R,VARIABLE
from canonical import basis,invariant_tags
from .monomial_coordinates import components,coordinates
from .high_lift import symbolic_column,split_exponent,orbit_size
from .scalar_products import add,mul,scale,columns
from .jets import Jet,nodes,ORBITS,moment_basis,column
from .moment_columns import SELECT

SCALAR_PAIRS=((0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),
              (1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),
              (2,2),(2,3),(2,5),(2,6),(2,7),(3,3),(3,6),(3,7),(3,8),(3,9),(4,6),(4,8))
SCALAR_LABELS=tuple((0,i,j)for i,j in SCALAR_PAIRS)+((2,0,0),(2,0,7),(2,0,8),(2,1,8))
SCALAR_ROWS=tuple(t for t in reversed(invariant_tags(9)) if 6<=t[0]+2*t[1]+3*t[2] and t!=(0,0,2))
JET_ROWS=tuple(i for i in range(17)if i not in (13,16))


def inverse(matrix):
    """Exact field Gauss-Jordan arithmetic, with full cancellation after each step."""
    n=len(matrix);a=[list(row)+[R(int(i==j))for j in range(n)]for i,row in enumerate(matrix)]
    for i in range(n):
        row=next(j for j in range(i,n)if a[j][i])
        a[i],a[row]=a[row],a[i]
        z=a[i][i];a[i]=[v/z for v in a[i]]
        for j in range(n):
            if j!=i and a[j][i]:
                z=a[j][i];a[j]=[x-z*y for x,y in zip(a[j],a[i])]
    return [row[n:]for row in a]


def univar(f,axis):
    return {tuple(i if k==axis else 0 for k in range(3)):c for i,c in enumerate(f)if c}


def moment_polynomial(k,f,h):
    """Individual canonical coefficients of the exact moment polynomial R_k(f,h)."""
    from itertools import permutations
    one={(0,0,0):R(1)};ordinary={}
    for i,j,l in permutations(range(3)):
        p=mul(univar(f,i),univar(h,j))
        if k:
            if k!=1:
                raise ValueError('The structural moment lift uses only F0 and F1')
            q={tuple(int(z==l)for z in range(3)):R(1),
               tuple(int(z in (i,j))for z in range(3)):R(-1)}
            p=mul(p,q)
        ordinary=add(ordinary,p)
    diag={}
    for e,c in ordinary.items():
        for axis in range(3):
            power=tuple(e[0]+e[1] if j==axis else 0 for j in range(3))
            diag[power]=diag.get(power,R())+c/6
    ordinary=add(ordinary,diag)
    if k==0:ordinary=add(ordinary,{(0,0,0):sum(f,R())*sum(h,R())/7})
    return {e:c for e,c in ordinary.items()if tuple(sorted(e))==e}


def to_invariant(poly,zero=None):
    """Canonical ordinary coefficients to sigma,e2,e3 coefficients."""
    if zero is None:zero=R()
    out={}
    for e,c in poly.items():
        for tag,v in components(tuple(e))[0].items():
            out[tag]=out.get(tag,zero)+c*(orbit_size(e)*v)
    return out


@lru_cache(None)
def jet_matrix(tags):
    ns=nodes(VARIABLE);rows=[]
    for orbit in ORBITS:
        p=[Jet(ns[label],[int(j==i)for j in range(3)])for i,label in enumerate(orbit)]
        sig=p[0]+p[1]+p[2];e2=p[0]*p[1]+p[0]*p[2]+p[1]*p[2];e3=p[0]*p[1]*p[2]
        js=[sig**i*e2**j*e3**k for i,j,k in tags]
        rows.append([z.v for z in js])
        for label in sorted(set(orbit)):
            rows.append([sum((z.g[j]for j in range(3)if orbit[j]==label),R())for z in js])
    return rows


@lru_cache(None)
def low_data():
    lab,polys=columns(4,5)
    scalar=[polys[lab.index(label)]for label in SCALAR_LABELS]
    sm=[[p.get(tag,R())for p in scalar]for tag in SCALAR_ROWS]
    mb={k:dict(moment_basis(VARIABLE,6,k))for k in (0,1)}
    moments=[moment_polynomial(k,mb[k][i],mb[k][j])for k,i,j in SELECT]
    moment_inv=[to_invariant(p)for p in moments]
    cols=[column(VARIABLE,k,mb[k][i],mb[k][j])for k,i,j in SELECT]
    jm=[[v[i]for v in cols]for i in JET_ROWS]
    return dict(scalar_polynomials=scalar,scalar_matrix=sm,scalar_inverse=inverse(sm),
                moment_polynomials=moments,moment_invariants=moment_inv,moment_matrix=jm,
                moment_inverse=inverse(jm),moment_features=mb)


def _outer(out,name,v,w,c,ev,zero):
    """Add c*(v*w^T+w*v^T)/2 using only nonzero feature pairs."""
    if len(v)!=len(w):
        raise ValueError('Unequal symmetric outer-product dimensions')
    products={}
    for i,x in ((i,x) for i,x in enumerate(v) if x):
        for j,y in ((j,y) for j,y in enumerate(w) if y):
            a,b=sorted((i,j))
            value=x*y*(1 if i==j else F(1,2))
            products[a,b]=products.get((a,b),0)+value
    for (i,j),value in products.items():
        if value:
            key=(name,i,j)
            out[key]=out.get(key,zero)+c*ev(R(value))

def _high_gram(d,gamma,out,c,ev,zero):
    desc=basis('s3',d);aa,bb=split_exponent(gamma)
    a,b=coordinates(aa,desc),coordinates(bb,desc);factor=orbit_size(gamma)
    for group,name in ((0,'M0_plus'),(1,'M0_sign'),(2,'M0_standard')):
        va=[a[group][i]for i in desc['frees'][group]];vb=[b[group][i]for i in desc['frees'][group]]
        _outer(out,name,va,vb,c*F(factor,2 if group==2 else 1),ev,zero)
        if group==2:
            va=[a[3][i]for i in desc['frees'][3]];vb=[b[3][i]for i in desc['frees'][3]]
            _outer(out,name,va,vb,c*F(3*factor,2),ev,zero)
