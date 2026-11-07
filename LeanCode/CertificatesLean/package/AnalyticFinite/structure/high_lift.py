"""Balanced contact-product lift with an exact unit high-degree coefficient."""
from fractions import Fraction as F
from functools import lru_cache
from math import factorial

from canonical import basis
from kernels import symbolic_kernels
from rational_field import R
from .monomial_coordinates import coordinates


def split_exponent(gamma):
    remaining = sum(gamma) // 2
    alpha = []
    for degree in gamma:
        value = min(degree, remaining)
        alpha.append(value)
        remaining -= value
    if remaining:
        raise ArithmeticError('Invalid exponent split')
    return tuple(alpha), tuple(g - a for g, a in zip(gamma, alpha))


def orbit_size(exponent):
    result = 6
    for value in set(exponent):
        result //= factorial(exponent.count(value))
    return result


@lru_cache(None)
def projected_monomial(d, exponent):
    """Sparse x^exponent-I_a(x^exponent), in ordinary monomials.

    The free coordinates of x^exponent in the constant symmetry basis are
    preserved, and its pivot coordinates are replaced by K_pivot,free*c.
    Consequently only the twenty-one pivot polynomials are changed.
    """
    if sum(exponent) > d:
        raise ValueError('Monomial exceeds the kernel degree')
    desc = basis('s3', d)
    coeffs = coordinates(exponent, desc)
    matrices = symbolic_kernels('s3', d)
    out = {tuple(exponent): R(1)}
    for group in range(4):
        free = desc['frees'][group]
        for pivot in desc['pivots'][group]:
            correction = -R(coeffs[group][pivot])
            for column, index in enumerate(free):
                if coeffs[group][index]:
                    correction += matrices[group][pivot][column] * coeffs[group][index]
            if not correction:
                continue
            for monomial, value in desc['groups'][group][pivot].items():
                out[monomial] = out.get(monomial, R()) + correction * value
    return {monomial: value for monomial, value in out.items() if value}


@lru_cache(None)
def symbolic_column(d, gamma):
    """Canonical coefficients of orbit(gamma)*Sym(f_alpha*f_beta)."""
    gamma = tuple(gamma)
    if tuple(sorted(gamma)) != gamma or not 10 <= sum(gamma) <= 2*d:
        raise ValueError('Expected a canonical high-degree monomial')
    alpha, beta = split_exponent(gamma)
    first = projected_monomial(d, alpha)
    second = projected_monomial(d, beta)
    raw = {}
    for x, value in first.items():
        for y, other in second.items():
            exponent = tuple(sorted(a + b for a, b in zip(x, y)))
            raw[exponent] = raw.get(exponent, R()) + value * other
    size = orbit_size(gamma)
    return {exponent: value * F(size, orbit_size(exponent))
            for exponent, value in raw.items() if value}

