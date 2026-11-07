"""Exact three-point coefficient tensors in elementary symmetric coordinates.

The tensor row (i,j,k) is the coefficient of sigma**i*e2**j*e3**k.
Newton identities and the S2 Reynolds identity are applied over Q before
any interval enclosure.  No numerical or parameter-dependent inverse is
used in this change of polynomial coordinates.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import comb, lcm

import numpy as np

from AnalyticFinite.analytic_layout import invariant_tags, parity_tags

ZERO = (0, 0, 0)
ONE = {ZERO: 1}


def add(p, q, factor=1):
    result = dict(p)
    for tag, value in q.items():
        result[tag] = result.get(tag, 0) + factor*value
    return {tag: value for tag, value in result.items() if value}


def shift(p, tag, factor=1):
    return {tuple(a+b for a,b in zip(exponent,tag)): factor*value
            for exponent,value in p.items() if factor*value}


def mul(p, q):
    result = {}
    for tag, value in p.items():
        result = add(result, shift(q, tag, value))
    return result


@lru_cache(None)
def power_sum(n):
    """x**n+y**n+z**n by the characteristic cubic of x,y,z."""
    if type(n) is not int or n < 0:
        raise ValueError('Invalid Newton-sum index')
    if n == 0:
        return {ZERO: 3}
    if n == 1:
        return {(1,0,0): 1}
    if n == 2:
        return {(2,0,0): 1, (0,1,0): -2}
    return add(add(shift(power_sum(n-1),(1,0,0)),
                   shift(power_sum(n-2),(0,1,0)),-1),
               shift(power_sum(n-3),(0,0,1)))


@lru_cache(None)
def dual_power_sum(n):
    """(xy)**n+(xz)**n+(yz)**n, whose elementary data are e2,sigma*e3,e3²."""
    if type(n) is not int or n < 0:
        raise ValueError('Invalid dual Newton-sum index')
    if n == 0:
        return {ZERO: 3}
    if n == 1:
        return {(0,1,0): 1}
    if n == 2:
        return {(0,2,0): 1, (1,0,1): -2}
    return add(add(shift(dual_power_sum(n-1),(0,1,0)),
                   shift(dual_power_sum(n-2),(1,0,1)),-1),
               shift(dual_power_sum(n-3),(0,0,2)))


@lru_cache(None)
def reynolds(i,j,k):
    """Average of x**i*(y+z)**j*(yz)**k over the three singled-out axes."""
    if any(type(n) is not int or n < 0 for n in (i,j,k)):
        raise ValueError('Invalid parity monomial')
    result = {}
    for ell in range(j+1):
        a = i+ell
        if a >= k:
            term = shift(power_sum(a-k),(j-ell,0,k))
        else:
            term = shift(dual_power_sum(k-a),(j-ell,0,a))
        result = add(result,term,F((-1)**ell*comb(j,ell),3))
    return result


DISCRIMINANT = {(2,2,0): 1, (0,3,0): -4, (3,0,1): -4,
                (0,0,2): -27, (1,1,1): 18}
DETERMINANT = {ZERO: 1, (2,0,0): -1, (0,1,0): 2, (0,0,1): 2}
STANDARD_PAIR = {
    (0,0): {(2,0,0): F(4,9), (0,1,0): F(-4,3)},
    (0,1): {(3,0,0): F(4,27), (1,1,0): F(-2,3), (0,0,1): F(2)},
    (1,1): {(4,0,0): F(4,81), (2,1,0): F(-8,27), (0,2,0): F(4,9)},
}


def tensor(tags, product, exponents, name):
    """Encode exact symmetric matrix entries with a proved common denominator."""
    index = {tag: i for i,tag in enumerate(exponents)}
    entries, denominator = {}, 1
    for i,left in enumerate(tags):
        for j in range(i,len(tags)):
            entry = product(left,tags[j])
            if not set(entry).issubset(index):
                raise ArithmeticError('Invariant product exceeds the polynomial degree')
            entries[i,j] = entry
            for value in entry.values():
                denominator = lcm(denominator,F(value).denominator)
    raw = np.zeros((len(exponents),len(tags),len(tags)),dtype=np.int64)
    for (i,j), entry in entries.items():
        for tag,value in entry.items():
            exact = F(value)*denominator
            if exact.denominator != 1 or abs(exact.numerator) >= 2**53:
                raise ArithmeticError('Raw invariant coefficient is not an exact binary64 integer')
            raw[index[tag],i,j] = raw[index[tag],j,i] = exact.numerator
    return dict(name=name, raw=raw, den=denominator)


@lru_cache(None)
def raw_symmetry(kind, degree, totaldegree):
    if type(totaldegree) is not int or totaldegree not in (12,14,16,18):
        raise ValueError('Unsupported total polynomial degree')
    d = totaldegree//2
    exponents = invariant_tags(totaldegree)
    if kind == 's3':
        if degree not in (d,d-2):
            raise ValueError('Unsupported full-symmetry feature degree')
        weight = ONE if degree == d else DETERMINANT
        tags = [invariant_tags(degree), invariant_tags(degree-3),
                [(0,*t) for t in invariant_tags(degree-1)]
                +[(1,*t) for t in invariant_tags(degree-2)]]
        def product(group,left,right):
            if group == 2:
                polynomial = STANDARD_PAIR[tuple(sorted((left[0],right[0])))]
                tag = tuple(a+b for a,b in zip(left[1:],right[1:]))
            else:
                polynomial = ONE if group == 0 else DISCRIMINANT
                tag = tuple(a+b for a,b in zip(left,right))
            return shift(mul(polynomial,weight),tag)
        return [tensor(group,lambda a,b,g=g: product(g,a,b),exponents,name)
                for g,(group,name) in enumerate(zip(tags,('plus','sign','standard')))]
    if kind != 's2' or degree != d-1:
        raise ValueError('Unsupported parity feature degree')
    def product(group,left,right):
        i,j,k = (a+b for a,b in zip(left,right))
        def weighted(ii,jj,kk):
            return add(reynolds(ii,jj,kk),reynolds(ii+2,jj,kk),-1)
        if group == 0:
            return weighted(i,j,k)
        return add(weighted(i,j+2,k),weighted(i,j,k+1),-4)
    return [tensor(parity_tags(degree-g),lambda a,b,g=g: product(g,a,b),exponents,name)
            for g,name in enumerate(('even','odd'))]


@lru_cache(None)
def symmetrized_monomial(a,b,c):
    """Sum over all six permutations, including multiplicities."""
    a,b,c = sorted((a,b,c),reverse=True)
    a,b = a-c,b-c
    if b == 0:
        return shift(power_sum(a),(0,0,c),2)
    return shift(add(mul(power_sum(a),power_sum(b)),power_sum(a+b),-1),(0,0,c))


@lru_cache(None)
def moment_monomial(a,b,c):
    result = symmetrized_monomial(a,b,c)
    for degree in (a+b,a+c,b+c):
        result = add(result,power_sum(degree),F(1,3))
    return result


@lru_cache(None)
def moment_data(d):
    if type(d) is not int or d not in (6,7,8,9):
        raise ValueError('Unsupported moment feature degree')
    # These three-variable polynomials are small Chebyshev generators only;
    # all Reynolds sums and all output tensors are formed in invariants.
    qbase = {(0,0,1): 1, (1,1,0): -1}
    aa = {ZERO: 1, (2,0,0): -1, (0,2,0): -1, (2,2,0): 1}
    qs = [ONE,qbase]
    for k in range(2,d):
        qs.append(add(mul(qbase,qs[-1]),mul(aa,qs[-2]),F(-1,2)))
        qs[-1] = {tag: 2*value for tag,value in qs[-1].items()}
    exponents = invariant_tags(2*d)
    data = []
    for k in range(d):
        def product(i,j):
            result = {}
            for (a,b,c),value in qs[k].items():
                result = add(result,moment_monomial(a+i,b+j,c),value)
            if k == 0:
                result = add(result,ONE,F(1,7))
            return result
        dat = tensor(list(range(d-k+1)),product,exponents,'F'+str(k))
        dat['k'] = k
        data.append(dat)
    return data
