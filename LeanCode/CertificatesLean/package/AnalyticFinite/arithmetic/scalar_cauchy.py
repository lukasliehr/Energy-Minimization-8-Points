"""Complete scalar Cauchy products with one rounding and signed tail hulls."""
from functools import lru_cache
from math import comb,lcm
from flint import fmpz_poly,fmpz_mat
from exact_iv import D,SCALE,ceildiv


@lru_cache(None)
def transform(degree):
    length=degree+1
    denominator=lcm(*(comb(degree,k) for k in range(length)))
    entries=[]
    for i in range(length):
        for k in range(length):
            numerator=sum((-1)**(k-j)*comb(i,j)*comb(degree-i,k-j)
                          for j in range(max(0,k-degree+i),min(i,k)+1))
            entries.append(numerator*(denominator//comb(degree,k)))
    return denominator,fmpz_mat(length,length,entries),fmpz_mat(length,length,[abs(x) for x in entries])


@lru_cache(None)
def paired_transform(degree):
    """One representative of each Bernstein row and its reflected partner."""
    denominator,T,absT=transform(degree)
    length=degree+1;rows=(length+1)//2;even=(length+1)//2;odd=length//2
    return (denominator,
            fmpz_mat(rows,even,[T[i,k] for i in range(rows) for k in range(0,length,2)]),
            fmpz_mat(rows,odd,[T[i,k] for i in range(rows) for k in range(1,length,2)]),
            fmpz_mat(rows,length,[absT[i,k] for i in range(rows) for k in range(length)]))


def tail_hull(mid,rad):
    """The full signed Bernstein hull, using exact even/odd reflection symmetry."""
    length=len(mid)
    if not length or len(rad)!=length or any(r<0 for r in rad):
        raise ValueError('Invalid complete scalar tail')
    den,even,odd,absolute=paired_transform(length-1)
    e=even*fmpz_mat((length+1)//2,1,mid[::2])
    o=odd*fmpz_mat(length//2,1,mid[1::2])
    radius=absolute*fmpz_mat(length,1,rad)
    hull=max(int(abs(e[i,0])+abs(o[i,0])+radius[i,0]) for i in range((length+1)//2))
    return den,hull


def product(left,right,order):
    if len(left)!=order+1 or len(right)!=order+1 or order<0:
        raise ValueError('Invalid scalar Cauchy dimensions')
    def prepare(values):
        if any(x.lo>x.hi for x in values):raise ValueError('Reversed scalar coefficient')
        m=[x.lo+x.hi for x in values];r=[x.hi-x.lo for x in values]
        return fmpz_poly(m),fmpz_poly(r),fmpz_poly([abs(x) for x in m])
    a,ra,aa=prepare(left);b,rb,ab=prepare(right)
    center=a*b;radius=aa*rb+ra*ab+ra*rb
    denominator=4*SCALE
    coefficients=[D.raw(int(center[k]-radius[k])//denominator,
                         ceildiv(int(center[k]+radius[k]),denominator)) for k in range(order+1)]
    length=max(len(center),len(radius))-order-1
    if length<=0:return coefficients,D.raw(0)
    mid=[int(center[k]) for k in range(order+1,order+1+length)]
    rad=[int(radius[k]) for k in range(order+1,order+1+length)]
    power=sum(abs(c)+r for c,r in zip(mid,rad))
    den,hull=tail_hull(mid,rad)
    upper=min(ceildiv(power,denominator),ceildiv(hull,denominator*den))
    return coefficients,D.raw(upper)
