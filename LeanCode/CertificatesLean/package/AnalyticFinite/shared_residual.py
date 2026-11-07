"""One coherent coefficient calculation, with a separate analytic tail bound.

The canonical basis retains its original high precision Taylor coefficients.
Only pivot rows vary.  Compute each low Cauchy product once, then bound the
omitted terms using nonnegative suffix sums and all three remainder products.
No coefficient, mixed error term, or residual coordinate is discarded.
"""
import numpy as np
from taylor_models import iv, ORDER
from matrix_models import toI
from interval_arithmetic import I
from fast_interval import mm, absI
from .precise_residual import polynomial_matrix_product
from .exact_projection import project_raw, project_remainder
from .bernstein_matrix import polynomial_bound


def product_remainder(left, right, left_error, right_error):
    """Bound AB minus its exact formal Taylor polynomial of order ORDER."""
    if len(left) != ORDER+1 or len(right) != ORDER+1:
        raise ValueError('Wrong polynomial length')
    tail = I(np.zeros((left[0].lo.shape[0], right[0].lo.shape[1])))
    suffix = I(np.zeros_like(right[0].lo))
    for i in range(1, ORDER+1):
        coefficient = right[ORDER-i+1]
        if np.any(coefficient.lo != 0) or np.any(coefficient.hi != 0):
            suffix = suffix + absI(coefficient)
        # Multiplication by an identically zero formal coefficient or
        # zero suffix contributes exactly zero, with no rounding needed.
        if (np.any(suffix.lo != 0) or np.any(suffix.hi != 0)) and (
                np.any(left[i].lo != 0) or np.any(left[i].hi != 0)):
            tail = tail + mm(absI(left[i]), suffix)
    def bound(coefficients):
        total = I(np.zeros_like(coefficients[0].lo))
        for coefficient in coefficients:
            if np.any(coefficient.lo != 0) or np.any(coefficient.hi != 0):
                total = total + absI(coefficient)
        return I(total.hi)
    return (tail + mm(bound(left), right_error)
            + mm(left_error, bound(right)) + mm(left_error, right_error))


def coefficient_residual(data, bases, grams, records, gram_values, target, *, target_remainder=True):
    if not len(data) == len(bases) == len(grams) == len(records) == len(gram_values):
        raise ValueError('Mismatched block layout')
    residual = [iv.matrix(c) for c in target.c]
    tail = absI(toI(target.e)) if target_remainder else I(np.zeros((target.c[0].rows,1)))
    for dat, B, W, record, values in zip(data, bases, grams, records, gram_values):
        free = record['free']
        active = [record['pivot']] if dat['name'].startswith('F') else record['pivots']
        n, q = len(free), len(active)
        m = n+q
        if sorted(free+active) != list(range(m)):
            raise ValueError('Invalid canonical pivot partition')
        if B.c[0].lo.shape != (m,n) or W.c[0].lo.shape != (n,n):
            raise ValueError('Invalid canonical matrix shape')
        if np.any(W.e.hi != 0):
            raise ValueError('Gram proposal is not an exact polynomial')
        if not np.array_equal(B.c[0].lo[free],np.eye(n)) or not np.array_equal(B.c[0].hi[free],np.eye(n)):
            raise ValueError('Nonidentity canonical free rows')
        if np.any(B.e.hi[free] != 0) or any(np.any(c.lo[free] != 0) or np.any(c.hi[free] != 0) for c in B.c[1:]):
            raise ValueError('Nonconstant canonical free rows')
        if any(not np.array_equal(c.lo,c.lo.T) or not np.array_equal(c.hi,c.hi.T) for c in W.c):
            raise ValueError('Nonsymmetric polynomial Gram')
        if not hasattr(B, 'canonical_coefficients') or len(B.canonical_coefficients) != ORDER+1:
            raise ValueError('Missing coherent canonical coefficients')
        pc = [iv.matrix([[C[i,j] for j in range(n)] for i in active])
              for C in B.canonical_coefficients]
        wc = [iv.matrix([[iv.mpf(x) for x in row] for row in val]) for val in values]
        if len(wc) > ORDER+1:
            raise ValueError('Gram degree exceeds validation order')
        # W is an exact polynomial, so its analytic remainder is zero.
        # Compute every omitted Cauchy coefficient before taking magnitudes.
        bw_full = polynomial_matrix_product(pc, wc, ORDER+len(wc)-1)
        bw = bw_full[:ORDER+1]
        pp_full = polynomial_matrix_product(bw, [C.T for C in pc], 2*ORDER)
        pp = pp_full[:ORDER+1]
        pe = B.e[np.ix_(active, list(range(n)))]
        p_bound = polynomial_bound(pc)
        w_bound = polynomial_bound(wc)
        cross_error = polynomial_bound(bw_full[ORDER+1:], (q,n)) + mm(pe,w_bound)
        b_bound = polynomial_bound(bw)
        principal_error = (polynomial_bound(pp_full[ORDER+1:], (q,q))
            + mm(b_bound,pe.T) + mm(cross_error,p_bound.T) + mm(cross_error,pe.T))
        tail = tail + project_remainder(dat['raw'], dat['den'], free, active,
                                        cross_error, principal_error)
        projection = project_raw(dat['raw'], dat['den'], free, active, wc[:len(values)], bw, pp)
        for k,C in enumerate(projection):
            residual[k] = residual[k]-C
        print('Shared direct residual block',dat['name'],flush=True)
    return residual, tail
