"""Table-free, exact normalized numerators for the contact evaluation inverse.

The interpolation construction uses only orbit averages, scalar Lagrange
interpolation, two-by-two formulas and one three-by-three adjugate.  Exact
rational-function cancellation gives the small polynomials evaluated by
the coherent Taylor model.  No stored inverse coefficients are consumed.
"""
from functools import lru_cache
from interpolation import ContactInverse, POINTS
from rational_field import VARIABLE, SQRT2


def denominator(a):
    return (a*(a-1)**2*(5*a-1)*(17*a*a-10*a+1)*(7*a*a+2*a-1)
            *(13*a*a-6*a+1)*(599*a**4-292*a**3+2*a*a+12*a-1))


def encode_polynomial(value):
    if value.d != 1:
        raise ArithmeticError('Contact inverse numerator did not normalize to a polynomial')
    degree = max(len(value.p), len(value.q)) - 1
    if degree > 14:
        raise ArithmeticError('Unexpected contact inverse numerator degree')
    return [[int(value.p[k].numerator), int(value.p[k].denominator),
             int(value.q[k].numerator), int(value.q[k].denominator)]
            for k in range(max(1, degree+1))]


@lru_cache(maxsize=8)
def generated_pattern(monomials, points):
    if points != POINTS:
        raise ArithmeticError('Analytic inverse evaluation row order mismatch')
    inverse = ContactInverse(VARIABLE, SQRT2, monomials, points).inverse()
    delta = denominator(VARIABLE)
    numerators = [[encode_polynomial(entry*delta) for entry in row] for row in inverse]
    return dict(monomials=[list(e) for e in monomials], numerators=numerators)
