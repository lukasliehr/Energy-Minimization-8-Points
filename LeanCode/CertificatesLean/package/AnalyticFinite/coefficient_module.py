"""Exact simultaneous coefficient contraction over Q(sqrt(2))(a).

The structural right inverse is linear in the residual.  Its finite
coefficient vector can therefore be carried through the construction once.
Every module value has one height denominator shared by all its entries;
no variable t, truncation, derivative, or right-inverse Taylor model occurs.
Only exact final scalar coefficients are returned for the existing bounds.
"""
from flint import fmpq_poly
from rational_field import R, divide_exact


class CoefficientModule:
    """A field scalar or a finite vector over the exact height field.

    Nonzero scalar addition to a vector and vector-vector multiplication
    are deliberately rejected: the supported expression is a linear map.
    """
    __slots__ = ('scalar', 'p', 'q', 'd')

    def __init__(self, scalar=0):
        if isinstance(scalar, CoefficientModule):
            self.scalar, self.p, self.q, self.d = scalar.scalar, scalar.p, scalar.q, scalar.d
        else:
            self.scalar = R(scalar)
            self.p = self.q = self.d = None

    @classmethod
    def vector(cls, values):
        values = [R(value) for value in values]
        if not values:
            raise ValueError('An exact coefficient module cannot be empty')
        denominator = fmpq_poly([1])
        for value in values:
            denominator *= divide_exact(value.d, denominator.gcd(value.d))
        multipliers = [divide_exact(denominator, value.d) for value in values]
        return cls._vector([v.p*m for v, m in zip(values, multipliers)],
                           [v.q*m for v, m in zip(values, multipliers)], denominator)

    @classmethod
    def _vector(cls, p, q, denominator):
        if not denominator:
            raise ZeroDivisionError('Zero common coefficient denominator')
        if len(p) != len(q) or not p:
            raise ValueError('Invalid coefficient module dimensions')
        common = denominator
        for value in p+q:
            common = common.gcd(value)
            if len(common) == 1:
                break
        if len(common) > 1:
            p = [divide_exact(value, common) for value in p]
            q = [divide_exact(value, common) for value in q]
            denominator = divide_exact(denominator, common)
        leading = denominator[len(denominator)-1]
        result = object.__new__(cls)
        result.scalar = None
        result.p = tuple(value/leading for value in p)
        result.q = tuple(value/leading for value in q)
        result.d = denominator/leading
        return result

    def coefficients(self, count=None):
        if self.scalar is not None:
            if self.scalar:
                raise ValueError('Expected a vector, received a nonzero field scalar')
            if count is None:
                raise ValueError('A zero scalar requires the coefficient count')
            return [R() for _ in range(count)]
        if count is not None and count != len(self.p):
            raise ValueError('Unexpected coefficient count')
        return [R(p, q, self.d) for p, q in zip(self.p, self.q)]

    def __bool__(self):
        return bool(self.scalar) if self.scalar is not None else any(self.p) or any(self.q)

    def __neg__(self):
        if self.scalar is not None:
            return CoefficientModule(-self.scalar)
        return self._vector([-p for p in self.p], [-q for q in self.q], self.d)

    def __add__(self, other):
        other = CoefficientModule(other)
        if self.scalar is not None and other.scalar is not None:
            return CoefficientModule(self.scalar+other.scalar)
        if self.scalar is not None:
            if self.scalar:
                raise TypeError('Nonzero field scalar cannot be added to a coefficient vector')
            return other
        if other.scalar is not None:
            if other.scalar:
                raise TypeError('Nonzero field scalar cannot be added to a coefficient vector')
            return self
        if len(self.p) != len(other.p):
            raise ValueError('Coefficient vector lengths differ')
        common = self.d.gcd(other.d)
        left = divide_exact(other.d, common)
        right = divide_exact(self.d, common)
        return self._vector([p*left+r*right for p, r in zip(self.p, other.p)],
                            [q*left+s*right for q, s in zip(self.q, other.q)],
                            self.d*left)

    __radd__ = __add__

    def __sub__(self, other):
        return self+-CoefficientModule(other)

    def __rsub__(self, other):
        return CoefficientModule(other)+-self

    def __mul__(self, other):
        other = CoefficientModule(other)
        if self.scalar is not None and other.scalar is not None:
            return CoefficientModule(self.scalar*other.scalar)
        if self.scalar is None and other.scalar is None:
            raise TypeError('The structural contraction must be linear in coefficient vectors')
        vector, scalar = (self, other.scalar) if self.scalar is None else (other, self.scalar)
        if not scalar:
            return CoefficientModule()
        return self._vector([p*scalar.p+2*q*scalar.q for p, q in zip(vector.p, vector.q)],
                            [p*scalar.q+q*scalar.p for p, q in zip(vector.p, vector.q)],
                            vector.d*scalar.d)

    __rmul__ = __mul__


def structural_simultaneous_corrections(apply, degree, exponents, centers, pivots):
    """Return exactly the maps D_a(c_k), with one structural application."""
    count = len(centers)
    if not count or any(len(row) != len(exponents) for row in centers):
        raise ValueError('Invalid rectangular coefficient array')
    polynomial = {}
    for j, exponent in enumerate(exponents):
        vector = [row[j] for row in centers]
        if any(vector):
            polynomial[tuple(exponent)] = CoefficientModule.vector(vector)
    packed = apply(degree, polynomial, CoefficientModule, pivots)
    result = [dict() for _ in range(count)]
    for coordinate, vector in packed.items():
        for k, value in enumerate(vector.coefficients(count)):
            if value:
                result[k][coordinate] = value
    return result


def simultaneous_corrections(apply, degree, exponents, centers, pivots, *, temporal=None):
    """Use the exact fixed map; retain the structural generator for fresh setup."""
    from .fixed_correction import simultaneous_corrections as integer_corrections
    return integer_corrections(apply,degree,exponents,centers,pivots,temporal=temporal)
