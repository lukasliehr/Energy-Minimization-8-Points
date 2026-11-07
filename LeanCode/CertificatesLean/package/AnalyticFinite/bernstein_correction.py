"""Value-only analytic correction after exact rational-center contraction.

For r(t)=sum_k r_k*t**k+e(t), split each narrow coefficient box at an
exact rational center c_k.  Evaluate D_a(c_k) only after its full exact
Q(sqrt(2))(a) contraction.  All coefficient half-widths and the residual
remainder form one independent error box.  The exact center polynomial
is converted to its Bernstein controls before linear contraction.
Their positive partition of unity gives both an entrywise maximum
majorant and a maximum of whole-matrix quadratic-form bounds.

Only the first ``retained_count`` centers need exact contraction.  Every
later center is included by absolute value in the same componentwise error
box, because |t| <= 1.  No residual coefficient is discarded.

No Taylor model, derivative, or Taylor remainder of D is constructed.
"""
from fractions import Fraction
import time

from exact_iv import iv, PRECISION
from rational_field import R
from .coefficient_module import simultaneous_corrections
from .weighted_norm import weighted_bound
from .bernstein_centers import power_to_bernstein


RESIDUAL_CENTER_BITS = 128


def centered_correction_bounds(apply, degree, exponents, coefficients,
                               residual_errors, pivots, block_names,
                               block_orders, left_metrics, evaluator,
                               retained_count=None, center_bits=None):
    """Return four exact correction bounds and separate input-error bounds.

    ``coefficients[k][j,0]`` encloses the j-th fixed coefficient of r_k.
    ``residual_errors[j]`` is an exact nonnegative bound for e_j(t).
    ``left_metrics`` contains outward interval representations of the
    fixed dyadic triangular left metrics; their invertibility is proved
    by their power-of-two diagonal construction.
    """
    exponents = tuple(map(tuple, exponents))
    errors = list(map(Fraction, residual_errors))
    if len(errors) != len(exponents) or any(error < 0 for error in errors):
        raise ValueError('Invalid componentwise direct residual errors')
    if set(block_names) != set(left_metrics):
        raise ValueError('Incomplete fixed repair metrics')
    if not coefficients:
        raise ValueError('Empty direct residual coefficient array')
    if retained_count is None:
        retained_count = len(coefficients)
    if type(retained_count) is not int or not 0 <= retained_count <= len(coefficients):
        raise ValueError('Invalid retained residual coefficient count')
    if center_bits is not None and (type(center_bits) is not int or
                                   not 1 <= center_bits <= PRECISION):
        raise ValueError('Invalid exact dyadic center precision')
    scale = 1 << PRECISION
    totals = {name: iv.matrix(block_orders[name], block_orders[name]) for name in block_names}
    per_coefficient = []

    def transform(correction, exact):
        matrices = {name: iv.matrix(block_orders[name], block_orders[name]) for name in block_names}
        for (name, i, j), value in correction.items():
            if name not in matrices or not 0 <= i <= j < block_orders[name]:
                raise ValueError('Unexpected analytic repair coordinate')
            matrices[name][i, j] = matrices[name][j, i] = evaluator.rational(value) if exact else value
        return {name: left_metrics[name]*M*left_metrics[name].T
                for name, M in matrices.items()}

    def bound(M, n):
        return Fraction(max(sum((abs(M[i, j]) for j in range(n)), iv.mpf(0)).hi
                            for i in range(n)), scale)

    def accumulate(matrices, maximum=False):
        bounds = []
        for name in block_names:
            n, M = block_orders[name], matrices[name]
            bounds.append(weighted_bound(M))
            for i in range(n):
                for j in range(n):
                    value = abs(M[i, j])
                    if maximum:
                        totals[name][i,j] = iv.mpf(Fraction(max(totals[name][i,j].hi,value.hi),scale))
                    else:
                        totals[name][i,j] += value
        return bounds

    started = time.monotonic()
    centers = []
    for k, C in enumerate(coefficients):
        row = []
        for j, exponent in enumerate(exponents):
            value = C[j, 0]
            if value.lo > value.hi:
                raise ValueError('Reversed direct residual coefficient')
            midpoint = Fraction(value.lo+value.hi, 2*scale)
            center = midpoint
            if k < retained_count:
                if center_bits is not None:
                    center_scale = 1 << center_bits
                    numerator = ((value.lo+value.hi)*center_scale+scale)//(2*scale)
                    center = Fraction(numerator,center_scale)
                errors[j] += Fraction(value.hi-value.lo, 2*scale)+abs(midpoint-center)
                row.append(center)
            else:
                errors[j] += Fraction(value.hi-value.lo, 2*scale)+abs(midpoint)
        if k < retained_count:
            centers.append(row)
    nonzero_center_indices = [k for k,row in enumerate(centers) if any(row)]
    bernstein_degree = len(centers)-1
    centers = power_to_bernstein(centers)
    nonzero_control_indices = [k for k,row in enumerate(centers) if any(row)]
    centers = [centers[k] for k in nonzero_control_indices]
    contraction_started = time.monotonic()
    corrections = simultaneous_corrections(apply, degree, exponents, centers, pivots) if centers else []
    contraction_seconds = time.monotonic()-contraction_started
    evaluation_started = time.monotonic()
    for k, correction in enumerate(corrections):
        coefficient_bounds = accumulate(transform(correction, True), maximum=True)
        per_coefficient.append(coefficient_bounds)
        print('Exact-center Bernstein control', nonzero_control_indices[k],
              'maximum', max(map(float, coefficient_bounds)), flush=True)
    evaluation_seconds = time.monotonic()-evaluation_started
    error_started = time.monotonic()
    box = {exponent: iv.mpf([-error, error]) for exponent, error in zip(exponents, errors)}
    correction = apply(degree, box, evaluator.rational, pivots)
    error_bounds = accumulate(transform(correction, False))
    exact_bounds = [weighted_bound(totals[name]) for name in block_names]
    control_bounds = [max((row[j] for row in per_coefficient),default=Fraction(0))
                      for j in range(len(block_names))]
    exact_bounds = [min(bound,control+error) for bound,control,error
                    in zip(exact_bounds,control_bounds,error_bounds)]
    # The complete symmetric nonnegative majorant also dominates its
    # input-error contribution. Its weighted bound therefore bounds
    # that contribution independently of the separate row estimate.
    error_bounds = [min(error,total) for error,total in zip(error_bounds,exact_bounds)]
    return dict(bounds=exact_bounds, input_error_bounds=error_bounds,
                coefficient_bounds=per_coefficient, seconds=time.monotonic()-started,
                retained_coefficient_count=retained_count,
                absorbed_coefficient_count=len(coefficients)-retained_count,
                nonzero_center_indices=nonzero_center_indices,
                enclosure_basis='bernstein_convex_hull_with_full_independent_input_error',
                enclosure_degree=bernstein_degree,
                enclosure_control_count=bernstein_degree+1,
                nonzero_control_indices=nonzero_control_indices,
                exact_center_bits=center_bits,
                contraction_seconds=contraction_seconds,
                evaluation_seconds=evaluation_seconds,
                error_seconds=time.monotonic()-error_started)
