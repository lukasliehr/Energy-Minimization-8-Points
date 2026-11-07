"""Four-block structural correction using invariant leading products.

The high lift uses only trivial and standard contact kernels.  Every
leading monomial is assembled exactly before projection, so degree drops
as in the existing contact-product theorem.  No sign-block correction is
ever produced.
"""
from fractions import Fraction as F
from functools import lru_cache


def weight(tag):
    return tag[0]+2*tag[1]+3*tag[2]


def add_tag(a,b):
    return tuple(x+y for x,y in zip(a,b))


def split(tag,lo,hi,other_lo=None,other_hi=None):
    other_lo=lo if other_lo is None else other_lo
    other_hi=hi if other_hi is None else other_hi
    candidates=[]
    for i in range(tag[0]+1):
        for j in range(tag[1]+1):
            for k in range(tag[2]+1):
                a=(i,j,k);b=tuple(x-y for x,y in zip(tag,a))
                if lo<=weight(a)<=hi and other_lo<=weight(b)<=other_hi:
                    # Both lower limits correspond to total feature degree5.
                    # Thus this key balances actual feature degrees, including
                    # the degree1/2 standard covariant factors.
                    candidates.append((abs(weight(a)-lo-weight(b)+other_lo),a,b))
    if not candidates:
        return None
    _,a,b=min(candidates)
    return a,b


# The standard pairing is P_0 Q_0+(P_1-P_2)(Q_1-Q_2)/3.
STANDARD_LEADING={
    (0,0):{(2,0,0):F(4,9),(0,1,0):F(-4,3)},
    (0,1):{(3,0,0):F(4,27),(1,1,0):F(-2,3),(0,0,1):F(2)},
    (1,1):{(4,0,0):F(4,81),(2,1,0):F(-8,27),(0,2,0):F(4,9)},
}


@lru_cache(None)
def leading_representation(d,tag):
    """Return a sparse exact product representation of one invariant monomial.

    Labels (group,left,right) use group0 for invariant features and group2
    for standard features, whose first coordinate selects P or Q.
    Every feature has weighted degree between5 andd.
    """
    if d not in (6,7,8,9) or not 10<=weight(tag)<=2*d:
        raise ValueError('Unsupported invariant high monomial')
    parts=split(tag,5,d)
    if parts is not None:
        return {(0,*parts):F(1)}
    options=[((0,1,0),(0,0),5-1,d-1,5-1,d-1),
             ((0,0,1),(0,1),5-1,d-1,5-2,d-2),
             ((0,2,0),(1,1),5-2,d-2,5-2,d-2)]
    for pivot,types,lo,hi,other_lo,other_hi in options:
        remainder=tuple(x-y for x,y in zip(tag,pivot))
        if min(remainder)<0:
            continue
        parts=split(remainder,lo,hi,other_lo,other_hi)
        if parts is None:
            continue
        pair=STANDARD_LEADING[types]
        pivot_value=pair[pivot]
        result={(2,(types[0],*parts[0]),(types[1],*parts[1])):1/pivot_value}
        for other,coefficient in pair.items():
            if other==pivot:
                continue
            newtag=add_tag(remainder,other)
            assert (newtag[2],newtag[1])<(tag[2],tag[1])
            for label,value in leading_representation(d,newtag).items():
                result[label]=result.get(label,F(0))-coefficient*value/pivot_value
        return {label:value for label,value in result.items() if value}
    raise ArithmeticError('Invariant leading-product split failed: '+str((d,tag)))


def leading_product(label):
    group,a,b=label
    if group==0:
        return {add_tag(a,b):F(1)}
    types=tuple(sorted((a[0],b[0])))
    exponent=add_tag(a[1:],b[1:])
    return {add_tag(exponent,t):c for t,c in STANDARD_LEADING[types].items()}


@lru_cache(None)
def projected_feature(d,group,tag):
    """Exact canonical contact feature in invariant/covariant coordinates."""
    from canonical import basis
    from kernels import symbolic_kernels
    from rational_field import R
    desc=basis('s3',d)
    if group not in (0,2):
        raise ValueError('Only trivial and standard features are allowed')
    raw_index=desc['tags'][group].index(tag)
    index=desc['frees'][group].index(raw_index)
    matrix=symbolic_kernels('s3',d)[group]
    if group==0:
        return {t:matrix[i][index] for i,t in enumerate(desc['tags'][group])
                if matrix[i][index]}
    return tuple({t[1:]:matrix[i][index] for i,t in enumerate(desc['tags'][group])
                  if t[0]==kind and matrix[i][index]} for kind in (0,1))


@lru_cache(None)
def projected_column(d,tag):
    """The exact projected product equals its monomial plus lower degrees."""
    from rational_field import R
    from AnalyticFinite.structure.scalar_products import product,add,scale
    out={}
    for (group,left,right),coefficient in leading_representation(d,tag).items():
        out=add(out,scale(coefficient,product(group,
            projected_feature(d,group,left),projected_feature(d,group,right))))
    high={t:c for t,c in out.items() if weight(t)>=weight(tag)}
    if high!={tag:R(1)}:
        raise ArithmeticError('Projected invariant column has wrong leading part')
    return out


@lru_cache(None)
def gram_coordinates(d,tag):
    """Exact sparse upper-triangle Gram representation of one column."""
    from canonical import basis
    desc=basis('s3',d)
    out={}
    for (group,left,right),coefficient in leading_representation(d,tag).items():
        i=desc['frees'][group].index(desc['tags'][group].index(left))
        j=desc['frees'][group].index(desc['tags'][group].index(right))
        i,j=sorted((i,j))
        name='M0_plus' if group==0 else 'M0_standard'
        key=(name,i,j)
        out[key]=out.get(key,F(0))+coefficient*(1 if i==j else F(1,2))
    return {key:value for key,value in out.items() if value}


def apply_invariant(d,poly,evaluate,moment_pivots=None):
    """Compatible right inverse supported on four physical Gram blocks.

    Exact rational-center contraction and the full independent error box
    use this same linear extension. Compatibility is required only for the
    actual residual, as for the existing normalized operator.
    """
    from rational_field import R
    from canonical import basis,invariant_tags
    from AnalyticFinite.structure import right_inverse as old
    from AnalyticFinite.structure.normalized_operator import normalized_data
    if type(d) is not int or d not in (6,7,8,9):
        raise ValueError('Supported active half-degrees are6..9')
    zero=evaluate(R())
    out={}
    work=dict(poly)
    cache={}

    def ev(r):
        key=(tuple(r.p),tuple(r.q),tuple(r.d))
        if key not in cache:
            cache[key]=evaluate(r)
        return cache[key]

    high=sorted((tag for tag in invariant_tags(2*d) if weight(tag)>=10),
                key=lambda tag:(-weight(tag),tag))
    for tag in high:
        if tag not in work:
            continue
        value=work.pop(tag,zero)
        for key,coefficient in gram_coordinates(d,tag).items():
            out[key]=out.get(key,zero)+value*coefficient
        for lower,coefficient in projected_column(d,tag).items():
            if lower!=tag:
                work[lower]=work.get(lower,zero)-value*ev(coefficient)

    data=normalized_data()
    vector=[work.get(tag,zero) for tag in data['tags']]
    moment_coeff=[sum((ev(z)*x for z,x in zip(row,vector) if z),zero)
                  for row in data['jet_map']]
    scalar_coeff=[sum((ev(z)*x for z,x in zip(row,vector) if z),zero)
                  for row in data['scalar_map']]
    pivots={0:0,1:1} if moment_pivots is None else moment_pivots
    for value,(k,i,j) in zip(moment_coeff,old.SELECT):
        f=data['moment_features'][k][i]
        h=data['moment_features'][k][j]
        free=[q for q in range(d-k+1) if q!=pivots[k]]
        v=[f[q] if q<len(f) else R() for q in free]
        w=[h[q] if q<len(h) else R() for q in free]
        old._outer(out,'F'+str(k),v,w,value,ev,zero)

    desc=basis('s3',d)
    small,large=basis('s3',4),basis('s3',5)
    for value,(group,i,j) in zip(scalar_coeff,old.SCALAR_LABELS):
        ti=small['tags'][group][small['frees'][group][i]]
        tj=large['tags'][group][large['frees'][group][j]]
        ii=desc['frees'][group].index(desc['tags'][group].index(ti))
        jj=desc['frees'][group].index(desc['tags'][group].index(tj))
        name='M0_plus' if group==0 else 'M0_standard'
        a,b=sorted((ii,jj))
        key=(name,a,b)
        out[key]=out.get(key,zero)+value*(1 if a==b else F(1,2))
    return out


def apply(d,poly,evaluate,moment_pivots=None):
    """Ordinary-coordinate compatibility wrapper, retained as an exact oracle."""
    from rational_field import R
    from .right_inverse import to_invariant
    return apply_invariant(d,to_invariant(poly,evaluate(R())),evaluate,moment_pivots)
