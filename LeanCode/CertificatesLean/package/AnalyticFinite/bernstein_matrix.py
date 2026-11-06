"""Full polynomial matrix bounds with exact power-to-Bernstein contraction."""
from math import comb,lcm
from functools import lru_cache
import numpy as np
from flint import fmpz_mat
from exact_iv import D,iv,ceildiv
from matrix_models import toI
from interval_arithmetic import I


@lru_cache(maxsize=None)
def _bernstein_transform(degree):
    """Immutable exact linear maps shared by equal-degree matrix bounds."""
    length=degree+1
    denominator=lcm(*(comb(degree,k) for k in range(length)))
    transform=[]
    for i in range(length):
        for k in range(length):
            numerator=sum((-1)**(k-j)*comb(i,j)*comb(degree-i,k-j)
                          for j in range(max(0,k-degree+i),min(i,k)+1))
            transform.append(numerator*(denominator//comb(degree,k)))
    return (denominator,fmpz_mat(length,length,transform),
            fmpz_mat(length,length,[abs(x) for x in transform]))


def polynomial_bound(coefficients, shape=None):
    coefficients = list(coefficients)
    if coefficients:
        shape = (coefficients[0].rows, coefficients[0].cols)
        if any(((C.rows, C.cols) != shape for C in coefficients)):
            raise ValueError('Inconsistent polynomial matrix dimensions')
    if shape is None:
        raise ValueError('Missing empty polynomial shape')
    while coefficients and all((x.lo == x.hi == 0 for x in coefficients[-1].data)):
        coefficients.pop()
    if not coefficients:
        return I(np.zeros(shape))
    rows, cols = shape
    entries = rows * cols
    length = len(coefficients)
    if any((x.hi < x.lo for C in coefficients for x in C.data)):
        raise ValueError('Reversed polynomial coefficient interval')
    denominator, T, unused = _bernstein_transform(length - 1)
    columns = []
    ids = []
    where = {}
    for j in range(entries):
        key = tuple(((C.data[j].lo, C.data[j].hi) for C in coefficients))
        if key not in where:
            where[key] = len(columns)
            columns.append(key)
        ids.append(where[key])
    unique = len(columns)
    half = (length + 1) // 2
    mids = [[lo + hi for lo, hi in col] for col in columns]
    radii = [[hi - lo for lo, hi in col] for col in columns]
    even = [k for k in range(0, length, 2) if any((col[k] for col in mids))]
    odd = [k for k in range(1, length, 2) if any((col[k] for col in mids))]
    uncertain = [k for k in range(length) if any((col[k] for col in radii))]

    def product(indices, data, absolute=False):
        if not indices:
            return fmpz_mat(half, unique)
        left = fmpz_mat(half, len(indices), [abs(T[i, k]) if absolute else T[i, k] for i in range(half) for k in indices])
        right = fmpz_mat(len(indices), unique, [col[k] for k in indices for col in data])
        return left * right
    E = product(even, mids)
    O = product(odd, mids)
    R = product(uncertain, radii, True)
    values = []
    for j, col in enumerate(columns):
        power = sum((max(abs(lo), abs(hi)) for lo, hi in col))
        hull = max((ceildiv(int(abs(E[i, j]) + abs(O[i, j]) + R[i, j]), 2 * denominator) for i in range(half)))
        values.append(D.raw(min(power, hull)))
    bound = iv.matrix(rows, cols)
    bound.data = [values[j] for j in ids]
    return I(toI(bound).hi)
