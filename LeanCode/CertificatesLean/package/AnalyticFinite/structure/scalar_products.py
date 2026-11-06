"""Explicit invariant contact products for the universal 36-column lift."""
from fractions import Fraction as F
from rational_field import R,VARIABLE
from kernels import symbolic_kernels
from canonical import basis,invariant_tags


def add(p,q):
    out=dict(p)
    for e,c in q.items():out[e]=out.get(e,R())+c
    return {e:c for e,c in out.items() if c}
def scale(c,p):return {e:c*v for e,v in p.items() if c*v}
def mul(p,q):
    out={}
    for e,c in p.items():
        for f,d in q.items():
            ef=tuple(a+b for a,b in zip(e,f));out[ef]=out.get(ef,R())+c*d
    return {e:c for e,c in out.items() if c}


PN={(2,0,0):R(F(2,3)),(0,1,0):R(-2)}
EP={(0,0,1):R(1),(1,1,0):R(-F(1,3)),(3,0,0):R(F(2,27))}
DISC={(2,2,0):R(1),(0,3,0):R(-4),(3,0,1):R(-4),(0,0,2):R(-27),(1,1,1):R(18)}


def features(d):
    desc=basis('s3',d);B=symbolic_kernels('s3',d);out=[]
    for group in range(3):
        these=[]
        for j in range(len(desc['frees'][group])):
            if group<2:
                these.append({tag:B[group][i][j] for i,tag in enumerate(desc['tags'][group]) if B[group][i][j]})
            else:
                these.append(tuple({tag[1:]:B[group][i][j] for i,tag in enumerate(desc['tags'][group]) if tag[0]==which and B[group][i][j]}for which in (0,1)))
        out.append(these)
    return out


def product(group,f,g):
    if group==0:return mul(f,g)
    if group==1:return mul(DISC,mul(f,g))
    ff,fg=f;gf,gg=g
    return add(add(scale(F(2,3),mul(PN,mul(ff,gf))),
                   scale(2,mul(EP,add(mul(ff,gg),mul(fg,gf))))),
               scale(F(1,9),mul(mul(PN,PN),mul(fg,gg))))


def columns(d,e):
    first,second=features(d),features(e);labels=[];out=[]
    for group in range(3):
        for i,f in enumerate(first[group]):
            for j,g in enumerate(second[group]):
                if d==e and j<i:continue
                labels.append((group,i,j));out.append(product(group,f,g))
    return labels,out

