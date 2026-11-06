"""Explicit D8-invariant polynomial coordinates through degree four.

The norm of a complex monomial t^alpha in the symmetric tensor metric
is alpha!/degree!. No matrix inverse or orthogonalization is needed.
"""
from itertools import combinations_with_replacement
from math import factorial
from fractions import Fraction as F
from collections import Counter
from dihedral_basis import K,C,T,ZERO,complex_variables,multiply


def reciprocal_multinomial(mon):
    value=1
    for n in Counter(mon).values():value*=factorial(n)
    return F(value,factorial(len(mon)))


def invariant_basis():
    variables,bar=complex_variables();done=set();out=[]
    for degree in range(5):
        for key in combinations_with_replacement(range(13),degree):
            if key in done:continue
            conjugate=tuple(sorted(bar[i]for i in key));done.add(key);done.add(conjugate)
            if sum(variables[i][0]for i in key)%8:continue
            sign=1;pol={():C(1)}
            for i in key:sign*=variables[i][1];pol=multiply(pol,variables[i][2])
            if key==conjugate:
                if sign==-1:continue
                if any(c.im for c in pol.values()):raise ArithmeticError('nonreal self-conjugate invariant')
                row={m:c.re for m,c in pol.items()if c.re}
            else:
                row={m:T*(c.re if sign==1 else c.im)for m,c in pol.items()}
                row={m:c for m,c in row.items()if c}
            out.append((row,reciprocal_multinomial(key)))
    return out


def extraction_map():
    basis=invariant_basis();out={}
    for j,(row,norm)in enumerate(basis):
        for mon,c in row.items():out.setdefault(mon,[]).append((j,c*reciprocal_multinomial(mon)/norm))
    return basis,out
