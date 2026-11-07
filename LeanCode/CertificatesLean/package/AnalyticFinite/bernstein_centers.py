"""Exact change of basis for the rational centers of a residual polynomial.

Only exact centers are transformed. Every original coefficient width,
center rounding error, discarded center and Taylor remainder is retained
separately in the unchanged independent input-error box.
"""
from fractions import Fraction
from math import comb


def power_to_bernstein(centers):
    """Return exact controls on t in [-1,1], at the original power degree.

    t**k = sum_i B_i^n((1+t)/2) * sum_{j<=min(k,i)}
           (-1)**(k-j) * 2**j * C(k,j) * C(i,j) / C(n,j).
    """
    if not centers:
        return []
    n = len(centers)-1
    width = len(centers[0])
    if any(len(row) != width for row in centers):
        raise ValueError('Ragged exact residual center array')
    from flint import fmpq, fmpq_mat
    matrix = fmpq_mat([[fmpq(Fraction(q).numerator, Fraction(q).denominator)
                       for q in row] for row in centers])
    transform = fmpq_mat(n+1,n+1)
    for i in range(n+1):
        for k in range(n+1):
            transform[i,k] = sum((fmpq((-1)**(k-j)*2**j*comb(k,j)*comb(i,j),comb(n,j))
                                 for j in range(min(k,i)+1)), fmpq(0))
    controls = transform*matrix
    return [[Fraction(int(controls[i,j].numerator),int(controls[i,j].denominator))
             for j in range(width)] for i in range(n+1)]
