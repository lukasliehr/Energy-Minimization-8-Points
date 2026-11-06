"""Exact PSD-only subdivision of a certified corrected Taylor family.

The remainder bound is retained unchanged. Equal dyadic subintervals
cover [-1,1] exactly. Floating Cholesky factors are only proposed dyadic
congruences; the strict interval norm test proves their validity.
"""
from fractions import Fraction as F
from math import comb
import numpy as np
from interval_arithmetic import I
from fast_interval import mm,absI,norm


def restricted_coefficients(coeff,parts,index):
    center=F(2*index+1-parts,parts);half=F(1,parts)
    out=[]
    for j in range(len(coeff)):
        c=I(np.zeros_like(coeff[0].lo))
        for k in range(j,len(coeff)):
            scalar=F(comb(k,j))*center**(k-j)*half**j
            c=c+I(scalar)*coeff[k]
        out.append(c)
    return out


def piece_bound(coeff,error,spectral_upper):
    mid=coeff[0].lo/2+coeff[0].hi/2
    try:
        proposal=np.linalg.inv(np.linalg.cholesky((mid+mid.T)/2))
    except np.linalg.LinAlgError:
        return float('inf')
    P=I(proposal)
    cc=[mm(mm(P,c),P.T) for c in coeff]
    cc[0]=cc[0]-I(np.eye(proposal.shape[0]))
    err=mm(mm(absI(P),error),absI(P).T)
    bound=err
    for c in cc:bound=bound+absI(c)
    spectral=I(norm(err))
    for c in cc:spectral=spectral+I(spectral_upper(c))
    return min(norm(bound),float(spectral.hi))


def certify(W,spectral_upper):
    for parts in [2,4,8]:
        errors=[piece_bound(restricted_coefficients(W.c,parts,i),W.e,spectral_upper)
                for i in range(parts)]
        if max(errors)<1:return max(errors),parts,errors
    raise ArithmeticError(('PSD subdivision failed',parts,errors))
