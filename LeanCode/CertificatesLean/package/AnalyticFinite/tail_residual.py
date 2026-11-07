"""Enclose the direct residual tail through canonical pivot rows only.

The proposed Gram polynomials are exact (zero uniform remainder), and the
free rows of each basis are the identity.  Consequently the free/free
product has zero tail, pivot/free is B_p W and pivot/pivot is B_p W B_p^T.
This is an arithmetic reorganization of the complete direct contraction.
"""
import numpy as np
from interval_arithmetic import I
from fast_interval import mm, absI


def coefficient_remainder(data, bases, grams, records, target_remainder):
    if not len(data) == len(bases) == len(grams) == len(records):
        raise ValueError('Mismatched block layout')
    tail = absI(target_remainder)
    for dat, B, W, record in zip(data, bases, grams, records):
        free = record['free']
        pivots = [record['pivot']] if dat['name'].startswith('F') else record['pivots']
        n = len(free)
        m = n + len(pivots)
        if sorted(free+pivots) != list(range(m)):
            raise ValueError('Invalid canonical pivot partition')
        if B.c[0].lo.shape != (m,n) or W.c[0].lo.shape != (n,n):
            raise ValueError('Invalid canonical matrix shape')
        if np.any(W.e.hi != 0):
            raise ValueError('Gram proposal is not an exact polynomial')
        if not np.array_equal(B.c[0].lo[free],np.eye(n)) or not np.array_equal(B.c[0].hi[free],np.eye(n)):
            raise ValueError('Nonidentity canonical free rows')
        if np.any(B.e.hi[free] != 0) or any(np.any(c.lo[free] != 0) or np.any(c.hi[free] != 0) for c in B.c[1:]):
            raise ValueError('Nonconstant canonical free rows')
        if any(not np.array_equal(c.lo,c.lo.T) or not np.array_equal(c.hi,c.hi.T) for c in W.c):
            raise ValueError('Nonsymmetric polynomial Gram')
        Bp = B.slice(pivots,list(range(n)))
        cross = Bp.multiply(W)
        principal = cross.multiply(Bp.T())
        e = I(np.zeros((m,m)))
        e[np.ix_(pivots,free)] = cross.e
        e[np.ix_(free,pivots)] = cross.e.T
        e[np.ix_(pivots,pivots)] = principal.e
        if np.max(np.abs(dat['raw'])) > 2**53:
            raise ArithmeticError('Raw integer cannot be represented exactly')
        raw = absI(I(dat['raw'].reshape((len(dat['raw']),-1))))
        vector = I(e.lo.reshape((-1,1)),e.hi.reshape((-1,1)))
        tail = tail + mm(raw,vector)/I(dat['den'])
    return tail
