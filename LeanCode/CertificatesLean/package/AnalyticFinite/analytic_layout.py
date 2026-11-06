"""Pure-stdlib layouts of the proved canonical contact kernels.

This module contains integer combinatorics only.  It neither imports the
numerical verifier nor trusts a witness to choose a polynomial basis.
"""
from math import comb

SUPPORTED_PIVOTS = frozenset({(0, 0), (1, 3), (2, 2), (3, 1),
                             (4, 0), (5, 0), (1, 1), (2, 0),
                             (6, 0), (7, 0), (8, 0)})


def invariant_tags(degree):
    return sorted([(i, j, k) for i in range(degree+1)
                   for j in range(degree//2+1) for k in range(degree//3+1)
                   if i+2*j+3*k <= degree], key=lambda t: (t[0]+2*t[1]+3*t[2], t))


def parity_tags(degree):
    return sorted([(i, j, k) for i in range(degree+1)
                   for j in range(degree+1) for k in range(degree//2+1)
                   if i+j+2*k <= degree], key=lambda t: (t[0]+t[1]+2*t[2], t))


def basis_layout(kind, degree):
    if type(degree) is not int or not 4 <= degree <= 9:
        raise ValueError('Canonical layout degree must be an integer from 4 to 9')
    if kind == 's3':
        t0 = invariant_tags(degree)
        t1 = invariant_tags(degree-3)
        t2 = [(0, *t) for t in invariant_tags(degree-1)]+[(1, *t) for t in invariant_tags(degree-2)]
        tags = [t0, t1, t2, t2[:]]
        pivots = [[t0.index((i, 0, 0)) for i in range(5)],
                  [t1.index((i, 0, 0)) for i in range(2)],
                  [t2.index((0, i, 0, 0)) for i in range(4)]+
                  [t2.index((1, i, 0, 0)) for i in range(3)]]
        pivots.append(pivots[2][:])
    elif kind == 's2':
        t0, t1 = parity_tags(degree), parity_tags(degree-1)
        tags = [t0, t1]
        pivots = [[t0.index((i, j, 0)) for i, n in enumerate([4, 3, 3, 2]) for j in range(n)],
                  [t1.index((i, j, 0)) for i, n in enumerate([3, 3, 2, 1]) for j in range(n)]]
    else:
        raise ValueError('Unknown canonical symmetry kind')
    offsets, start = [], 0
    for group in tags:
        offsets.append(start)
        start += len(group)
    if start != comb(degree+3, 3):
        raise ArithmeticError('Wrong full polynomial dimension')
    frees = [[i for i in range(len(group)) if i not in pp]
             for group, pp in zip(tags, pivots)]
    return dict(kind=kind, degree=degree, tags=tags, pivots=pivots, frees=frees,
                offsets=offsets, polynomial_dimension=start)


def _half_degree(degree):
    if type(degree) is not int or degree not in (12, 14, 16, 18):
        raise ValueError('Active polynomial degree must be 12, 14, 16 or 18')
    return degree//2


def _identity(order):
    return [[int(i == j) for j in range(order)] for i in range(order)]


def block_layout(degree, moment_pivots):
    """Generate the complete canonical basis_records; no witness J is read."""
    d = _half_degree(degree)
    if not isinstance(moment_pivots, list) or len(moment_pivots) != d:
        raise ValueError('Wrong moment-pivot list')
    result = []
    for k, pivot in enumerate(moment_pivots):
        if type(pivot) is not int or (k, pivot) not in SUPPORTED_PIVOTS or not 0 <= pivot <= d-k:
            raise ValueError('Moment pivot is not covered by the scalar sign theorem')
        free = [i for i in range(d-k+1) if i != pivot]
        result.append(dict(name='F'+str(k), pivot=pivot, free=free,
                           change_of_basis=_identity(len(free))))
    for prefix, kind, n, labels in [('M0', 's3', d, ['plus', 'sign', 'standard']),
                                     ('M1', 's2', d-1, ['even', 'odd']),
                                     ('Mdet', 's3', d-2, ['plus', 'sign', 'standard'])]:
        desc = basis_layout(kind, n)
        for group, label in enumerate(labels):
            free = desc['frees'][group]
            if not free:
                continue
            result.append(dict(name=prefix+'_'+label, pivots=desc['pivots'][group],
                               free=free, change_of_basis=_identity(len(free))))
    return result


def dimensions(degree):
    d = _half_degree(degree)
    defaults = [0 if k != 1 and k != 3 else 1 for k in range(d)]
    records = block_layout(degree, defaults)
    orders = [len(record['free']) for record in records]
    coefficient_rows = sum(1 for i in range(degree+1) for j in range(i, degree+1)
                           for k in range(j, degree+1) if i+j+k <= degree)
    return dict(block_names=[r['name'] for r in records], orders=orders,
                kernel_pivot_counts=[1 if 'pivot' in r else len(r['pivots']) for r in records],
                coefficient_rows=coefficient_rows, compatible_dimension=coefficient_rows-2,
                retained_rows=coefficient_rows-2,
                svec_dimension=sum(n*(n+1)//2 for n in orders))
