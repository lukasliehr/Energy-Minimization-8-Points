"""Data-free rational moment polynomials for the analytic finite reduction.

This module does not assert the corrected Grams are positive.  It replaces
only moment-entry expansion in the kernel construction.  The formulas and
the fixed pivot signs are proved in ../finite_analytic.tex.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import comb


def _add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def _mul(x, y):
    return (x[0] * y[0] + 2 * x[1] * y[1],
            x[0] * y[1] + x[1] * y[0])


def _power(x, n):
    result = (F(1), F(0))
    for _ in range(n):
        result = _mul(result, x)
    return result


ZERO = (F(0), F(0))
ONE = (F(1), F(0))


def _padd(x, y):
    return [_add(x[i] if i < len(x) else ZERO,
                 y[i] if i < len(y) else ZERO)
            for i in range(max(len(x), len(y)))]


def _pmul(x, y):
    result = [ZERO] * (len(x) + len(y) - 1)
    for i, a in enumerate(x):
        for j, b in enumerate(y):
            result[i + j] = _add(result[i + j], _mul(a, b))
    return result


def _ppower(x, n):
    result = [ONE]
    for _ in range(n):
        result = _pmul(result, x)
    return result


def _pscale(x, n):
    return [_mul(v, (F(n), F(0))) for v in x]


def _real_power(k, c, d):
    parity = k % 2
    result = [ZERO] * (k // 2 + 1)
    for j in range(0, k + 1, 2):
        coefficient = _mul(_power(c, k - j), _power(d, j))
        coefficient = _mul(coefficient, (F(comb(k, j) * (-1) ** (j // 2)), F(0)))
        power = (k - j - parity) // 2
        result[power] = _add(result[power], coefficient)
    return result


@lru_cache(None)
def moment_coefficients(k, i):
    """Return rational coefficients of P[k,i](a), in ascending order."""
    if type(k) is not int or type(i) is not int or k < 0 or i < 0:
        raise ValueError("Moment indices must be nonnegative integers")
    A = [ZERO, ONE]
    B = [(F(-1), F(0)), (F(2), F(0))]
    C = [(F(0), F(1, 2)), (F(-1), F(-1, 2))]
    D = [(F(0), F(-1, 2)), (F(-1), F(1, 2))]
    powers = [_ppower(node, i) for node in (A, B, C, D)]
    if k == 0:
        result = [ONE]
        for node, multiplicity in zip(powers, (2, 1, 2, 2)):
            result = _padd(result, _pscale(node, multiplicity))
    else:
        # The B vertex has tangent projection 2 sqrt(a) sqrt(1-a).
        result = _pmul(powers[1], [ZERO] * (k // 2) + [(F(2 ** k), F(0))])
        parameters = [
            (powers[0], (F(1), F(0)), (F(1), F(0))),
            (powers[2], (F(-1), F(-1, 2)), (F(0), F(1, 2))),
            (powers[3], (F(-1), F(1, 2)), (F(0), F(1, 2))),
        ]
        for node, c, d in parameters:
            result = _padd(result, _pscale(_pmul(node, _real_power(k, c, d)), 2))
    if any(irrational for _, irrational in result):
        raise ArithmeticError("Conjugate terms failed to cancel")
    coefficients = [rational for rational, _ in result]
    while len(coefficients) > 1 and coefficients[-1] == 0:
        coefficients.pop()
    return tuple(coefficients)


def evaluate_moment(A, k, i, constant):
    """Evaluate P[k,i] using coherent scalar-model operations.

    `constant(numerator, denominator)` must enclose that exact rational.
    For the existing Taylor kernel use
      lambda n, d: TM.const(iv.mpf(n) / d).
    """
    coefficients = moment_coefficients(k, i)
    result = constant(0, 1)
    for value in reversed(coefficients):
        result = result * A + constant(value.numerator, value.denominator)
    return result


def moment_kernel_row(A, k, pivot, free, constant):
    """The active row replacing -M[p,f]/M[p,p], one scalar denominator."""
    denominator = evaluate_moment(A, k, pivot, constant)
    inverse = constant(1, 1) / denominator
    return [-evaluate_moment(A, k, f, constant) * inverse for f in free]


SUPPORTED_PIVOTS = frozenset({(0, 0), (1, 3), (2, 2), (3, 1),
                             (4, 0), (5, 0), (1, 1), (2, 0),
                             (6, 0), (7, 0), (8, 0)})
