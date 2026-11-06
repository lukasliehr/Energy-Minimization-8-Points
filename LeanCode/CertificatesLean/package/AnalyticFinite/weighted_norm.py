"""Positive diagonal scaling for a symmetric correction's spectral bound.

If |C_ij| <= M_ij and every w_i>0, then every eigenvalue of C has
absolute value at most max_i sum_j M_ij*w_j/w_i. The weights below are
only choices of positive integers. Their construction is not a premise.
"""
from fractions import Fraction
from exact_iv import PRECISION, ceildiv


def weighted_bound(matrix, steps=12):
    if matrix.rows != matrix.cols or matrix.rows <= 0:
        raise ValueError('Expected a nonempty square matrix')
    n=matrix.rows
    upper=[[abs(matrix[i,j]).hi for j in range(n)] for i in range(n)]
    # Both transpose positions bound the same symmetric real entry.
    upper=[[min(upper[i][j],upper[j][i]) for j in range(n)] for i in range(n)]
    maximum=max(map(sum,upper))
    if maximum==0:
        return Fraction(0)
    w=[1<<16]*n
    best=maximum
    for _ in range(steps):
        image=[sum(a*b for a,b in zip(row,w)) for row in upper]
        best=min(best,max(ceildiv(y,x) for y,x in zip(image,w)))
        # Positive integer weights, damped to avoid period-two oscillation.
        proposal=[y+maximum*x for y,x in zip(image,w)]
        normalizer=max(proposal)
        w=[max(1,(x<<16)//normalizer) for x in proposal]
    return Fraction(best,1<<PRECISION)
