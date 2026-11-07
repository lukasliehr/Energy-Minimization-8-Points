"""Ordinary interval evaluation of the exact analytic correction operator.

The boxes enclose the compatible underlying residual, but need not
themselves satisfy compatibility. No Taylor model of the right inverse
is used by this helper.
"""
from fractions import Fraction
from flint import fmpq, fmpq_poly
from exact_iv import D, iv, PRECISION, SCALE, ceildiv
from .weighted_norm import weighted_bound


def rational_interval(value):
    """Exactly enclose a FLINT rational without redundant Python gcd work.

    For value=n/d and d>0 the existing fixed-dyadic interval is precisely
    [floor(SCALE*n/d),ceil(SCALE*n/d)]/SCALE.  Reduction of n/d cannot
    change either integer quotient, so no normalization is necessary.
    """
    numerator,denominator = int(value.numerator),int(value.denominator)
    if denominator <= 0:
        raise ValueError('Expected positive exact rational denominator')
    scaled = numerator*SCALE
    return D.raw(scaled//denominator,ceildiv(scaled,denominator))


HEIGHT_TRANSLATION_BITS = 32


class IntervalEvaluator:
    def __init__(self, lower, upper, center_bits=HEIGHT_TRANSLATION_BITS):
        if lower > upper:
            raise ValueError('Reversed height interval')
        center = (lower+upper)/2
        if center_bits is not None:
            if type(center_bits) is not int or not 1 <= center_bits <= PRECISION:
                raise ValueError('Invalid exact height-center precision')
            # Any exact center gives the identity p(a)=p(c+(a-c)).  A short
            # dyadic c avoids unnecessarily large translated coefficients.
            scale = 1 << center_bits
            numerator = (2*center.numerator*scale+center.denominator)//(2*center.denominator)
            center = Fraction(numerator,scale)
        self.center = center
        self.shift = fmpq_poly([fmpq(center.numerator, center.denominator), 1])
        self.variable = iv.mpf([lower, upper])-iv.mpf(center)
        self.sqrt2 = iv.sqrt(2)
        self.polynomials, self.inverses, self.rationals = {}, {}, {}

    def polynomial(self, polynomial):
        key = tuple(polynomial)
        if key not in self.polynomials:
            # Exact composition proves p(a)=p(center+(a-center)).
            shifted = polynomial(self.shift)
            result = iv.mpf(0)
            for coefficient in reversed(tuple(shifted)):
                result = result*self.variable+rational_interval(coefficient)
            self.polynomials[key] = result
        return self.polynomials[key]

    def inverse(self, polynomial):
        key = tuple(polynomial)
        if key not in self.inverses:
            unit, factors = polynomial.factor()
            reconstruction = polynomial*0+unit
            result = 1/rational_interval(unit)
            for factor, exponent in factors:
                reconstruction *= factor**exponent
                enclosure = self.polynomial(factor)
                if enclosure.lo <= 0 <= enclosure.hi:
                    raise ArithmeticError('Denominator factor enclosure contains zero')
                result *= enclosure**(-exponent)
            if reconstruction != polynomial:
                raise ArithmeticError('Incorrect exact denominator factorization')
            self.inverses[key] = result
        return self.inverses[key]

    def rational(self, value):
        key = (tuple(value.p), tuple(value.q), tuple(value.d))
        if key not in self.rationals:
            self.rationals[key] = (self.polynomial(value.p)
                                  + self.sqrt2*self.polynomial(value.q))*self.inverse(value.d)
        return self.rationals[key]


def uniform_correction_bound(entries, order, inverse):
    """Exact rational upper bound for a symmetric interval congruence."""
    matrix = iv.matrix(order, order)
    for (i, j), value in entries.items():
        matrix[i, j] = matrix[j, i] = value
    congruence = inverse*matrix*inverse.T
    return weighted_bound(congruence)
