"""Exact Bernstein square factors with four analytic-repair floor margins.

The proposed Grams are positive by construction on the full closed cell.
Only the universal right inverse's four supported blocks need correction
bounds. No Gram positivity test, numerical inverse, or coefficient-map
matrix is constructed. Every polynomial coefficient is enclosed from its
exact rational factor products; no rounded expanded Gram is substituted.
"""
from fractions import Fraction
from math import comb
import re
import time

from flint import fmpq, fmpq_mat
import numpy as np
import mpmath as mp
from taylor_models import TM, iv, ORDER, reset_proof_model_counts, proof_model_counts
from interval_arithmetic import I
from fast_interval import norm
from matrix_models import toI
from ipoly import IP
import build_symmetric as build
from exact_iv import PRECISION
from exact_mm import float_bound, BITS as MATRIX_BITS
from . import analytic_contracts as contracts
from .analytic_layout import block_layout
from .shared_residual import coefficient_residual as shared_coefficients
from .structure.invariant_operator import apply_invariant as apply
from .interval_correction import IntervalEvaluator, uniform_correction_bound, HEIGHT_TRANSLATION_BITS
from .centered_correction import centered_correction_bounds, RESIDUAL_CENTER_BITS
from .bernstein_correction import centered_correction_bounds as bernstein_correction_bounds
from .integer_gram import exact_gram
from .short_metric import short_left_inverse
from .joint_correction import centered_correction_bounds as joint_correction_bounds
from .joint_contracts import report_metadata as joint_metadata
from .matrix_congruence import METRIC_CENTER_BITS


REPAIR_BLOCKS = ('F0', 'F1', 'M0_plus', 'M0_standard')


def power_two(exponent):
    return fmpq(2**exponent) if exponent >= 0 else fmpq(1, 2**(-exponent))


def exact_metric(block, bits):
    """Power-of-two diagonals make invertibility an algebraic fact."""
    n = block['order']
    K = fmpq_mat(n, n)
    for i in range(n):
        K[i, i] = power_two(block['K_diagonal_exponents'][i])
        for j in range(i):
            K[i, j] = fmpq(block['K_strict_lower'][i][j], 2**bits)
    return K


def exact_factor(rows, n, bits):
    return fmpq_mat([[fmpq(rows[i][j], 2**bits) if j <= i else fmpq(0)
                       for j in range(n)] for i in range(n)])


def to_iv(M):
    return iv.matrix([[iv.mpf(Fraction(int(M[i, j].numerator), int(M[i, j].denominator)))
                        for j in range(M.ncols())] for i in range(M.nrows())])


def bernstein_coefficient(i, k, degree):
    """Exact coefficient of t^k in binom(N,i)(1+t)^i(1-t)^(N-i)/2^N."""
    numerator = comb(degree, i)*sum((-1)**(k-j)*comb(i, j)*comb(degree-i, k-j)
                  for j in range(max(0, k-(degree-i)), min(i, k)+1))
    return fmpq(numerator, 2**degree)


def verify(cell, witness, validation_order):
    if ORDER != validation_order:
        raise ValueError('Wrong configured Taylor order')
    actual_parameters = dict(scalar_bits=PRECISION, matrix_bits=MATRIX_BITS,
        height_translation_bits=HEIGHT_TRANSLATION_BITS, residual_center_bits=RESIDUAL_CENTER_BITS,
        correction_metric_center_bits=METRIC_CENTER_BITS)
    if any(value != contracts.ARITHMETIC_METHODS[name] for name,value in actual_parameters.items()):
        raise ValueError('Wrong fixed certificate arithmetic parameters')
    reset_proof_model_counts()
    dims = contracts.dimensions(cell)
    meta = contracts.witness_audit(witness, cell, dims)
    degree = witness['bernstein_degree']
    contracts.validation_order(validation_order, degree)
    delta = power_two(witness['floor_exponent'])
    rational_delta = Fraction(int(delta.numerator), int(delta.denominator))
    records = block_layout(cell['degree'], witness['moment_pivots'])
    record = dict(degree=cell['degree'], auxiliary_nodes=witness['auxiliary_nodes'], basis_records=records)
    mp.mp.dps = 100
    started = time.time()
    S, A, root, record, data, bases, target = build.build(cell['center'], cell['halfwidth'], record, cell['profile'])
    values, grams, left_metrics = [], [], {}
    effective_floors = {}
    short_metric_records = []
    joint_policy = contracts.JOINT_CORRECTION_POLICY.get(cell['id'])
    exact_metrics = {}
    for block in witness['blocks']:
        K, coefficients = exact_gram(block, degree, witness['factor_bits'], witness['metric_bits'], delta)
        n = block['order']
        values.append([[[C[i, j] for j in range(n)] for i in range(n)] for C in coefficients])
        grams.append(IP([toI(C) for C in coefficients]+[I(np.zeros((n, n))) for _ in range(ORDER-degree)]))
        if block['name'] in REPAIR_BLOCKS:
            Z, theta, short_record = short_left_inverse(block, witness['metric_bits'], contracts.SHORT_METRIC_BITS)
            floor = rational_delta*(1-theta)
            effective_floors[block['name']] = floor
            short_metric_records.append(contracts.short_metric_record(block, rational_delta))
            left_metrics[block['name']] = to_iv(Z)
            if joint_policy is not None and block['name'] in joint_policy['exact_blocks']:
                exact_metrics[block['name']] = Z
        print('Exact physical Bernstein Gram', block['name'], flush=True)
    st = time.time()
    precise, repair_tail = shared_coefficients(data, bases, grams, records, values, target,
                                               target_remainder=joint_policy is None)
    from fast_interval import absI
    tail=repair_tail if joint_policy is None else repair_tail+absI(toI(target.e))
    polynomial = {tuple(e): TM([C[i, 0] for C in precise], iv.mpf(float(tail.hi[i, 0])))
                  for i, e in enumerate(build.COORDINATES)}
    residual_coordinate_upper = [str(Fraction(q.bound().hi, 1 << PRECISION)) for q in polynomial.values()]
    print('Uniform direct residual', float(max(map(Fraction, residual_coordinate_upper))), flush=True)
    residual_seconds = time.time()-st
    st = time.time()
    pivots = {k: witness['moment_pivots'][k] for k in (0, 1)}
    orders = dict(zip(dims['block_names'], dims['orders']))
    if set(left_metrics) != set(REPAIR_BLOCKS):
        raise ArithmeticError('Incomplete analytic repair metrics')

    def validate_coordinates(correction):
        for name, i, j in correction:
            if name not in REPAIR_BLOCKS or not 0 <= i <= j < orders[name]:
                raise RuntimeError('Unexpected analytic repair coordinate')

    # These boxes need not be compatible. The actual residual they enclose
    # is compatible, and the right-inverse identity is used only for it.
    match = re.fullmatch(r'\[\s*([^,\[\]]+)\s*,\s*([^,\[\]]+)\s*\]', root['a_enclosure'])
    if match is None:
        raise ValueError('Unrecognized exact height enclosure')
    lower, upper = map(Fraction, match.groups())
    evaluator = IntervalEvaluator(lower, upper)
    interval_bounds = None
    interval_failure = None
    # A branch choice is an evaluation policy, never an acceptance premise.
    # These four cells cheaply pass the uniform alternative; every other
    # cell directly uses the complete rational-center enclosure.
    if cell['id'] in contracts.UNIFORM_FIRST_CELLS and joint_policy is None:
        try:
            boxes = {exponent: iv.mpf([-Fraction(bound), Fraction(bound)])
                     for exponent, bound in zip(polynomial, residual_coordinate_upper)}
            interval_correction = apply(build.v.D, boxes, evaluator.rational, pivots)
            validate_coordinates(interval_correction)
            interval_bounds = []
            for name in REPAIR_BLOCKS:
                entries = {(i, j): value for (block, i, j), value in interval_correction.items() if block == name}
                interval_bounds.append(uniform_correction_bound(entries, orders[name], left_metrics[name]))
        except (ArithmeticError, ValueError) as error:
            interval_bounds = None
            interval_failure = str(error)
    interval_seconds = time.time()-st
    if (interval_bounds is not None and len(interval_bounds) == len(REPAIR_BLOCKS)
            and all(0 <= bound < effective_floors[name] for name,bound in zip(REPAIR_BLOCKS,interval_bounds))):
        mode = 'uniform_interval'
        exact_bounds = interval_bounds
        centered = None
        print('Ordinary interval correction accepted', flush=True)
    else:
        use_bernstein = cell['id'] in contracts.BERNSTEIN_CENTER_CELLS
        mode = ('rational_joint_bernstein_value' if joint_policy is not None else
                'rational_bernstein_value' if use_bernstein else 'rational_center_value')
        center_enclosure = (joint_correction_bounds if joint_policy is not None else
                            bernstein_correction_bounds if use_bernstein else centered_correction_bounds)
        joint_options = {} if joint_policy is None else dict(height_model=A,
            global_height=(lower,upper),depth=joint_policy['depth'],
            exact_metrics=exact_metrics or None,exact_blocks=joint_policy['exact_blocks'],
            structured_errors=target.remainder_generators)
        print('Ordinary interval correction insufficient; contracting exact rational centers', flush=True)
        centered = center_enclosure(apply, build.v.D, build.COORDINATES, precise,
            [Fraction(float(repair_tail.hi[i, 0])) for i in range(len(build.COORDINATES))],
            pivots, REPAIR_BLOCKS, orders, left_metrics, evaluator, center_bits=RESIDUAL_CENTER_BITS, **joint_options)
        exact_bounds = centered['bounds']
    correction_seconds = time.time()-st
    bounds, ratios = [], []
    for name, bound in zip(REPAIR_BLOCKS, exact_bounds):
        floor = effective_floors[name]
        if not 0 <= bound < floor:
            raise ArithmeticError('Analytic correction exceeds Bernstein floor: '+name)
        bounds.append(str(bound))
        ratios.append(str(bound/floor))
        print('Uniform correction/floor', name, float(bound/floor), flush=True)
    untouched = [name for name in dims['block_names'] if name not in REPAIR_BLOCKS]
    return dict(schema=contracts.REPORT_SCHEMA, method=contracts.METHOD, passed=True,
                **contracts.SCALAR_METHODS, **contracts.SCALAR_ZERO_COUNTS, **proof_model_counts(),
                **contracts.ARITHMETIC_METHODS,
                **contracts.COORDINATE_METHODS,
                uniform_correction_attempted=cell['id'] in contracts.UNIFORM_FIRST_CELLS and joint_policy is None,
                scalar_model_count_scope='proof_models_excluding_Newton_proposals',
                degree=cell['degree'], validation_order=ORDER, bernstein_degree=degree, proposal_order=degree,
                factor_bits=witness['factor_bits'], metric_bits=witness['metric_bits'],
                floor_exponent=witness['floor_exponent'], rational_floor=str(rational_delta),
                repair_metric_data=short_metric_records,
                effective_floor_lower=[str(effective_floors[name]) for name in REPAIR_BLOCKS],
                minorant=cell['profile'], center=cell['center'], halfwidth=cell['halfwidth'],
                coefficient_rows=dims['retained_rows'], compatible_dimension=dims['retained_rows'],
                full_polynomial_coefficient_dimension=dims['coefficient_rows'],
                Gram_coordinates=dims['svec_dimension'], block_names=dims['block_names'],
                block_orders=dims['orders'], kernel_pivot_counts=dims['kernel_pivot_counts'],
                analytic_Gram_blocks=len(dims['orders']), numerical_Gram_PSD_predicates=0, numerical_coefficient_inverse_predicates=0,
                full_coefficient_matrix_entries=0, F0_basis_inverse_predicates=0,
                analytic_right_inverse_theorem='thm:four-block-right-inverse',
                analytic_floor_theorem='sec:bernstein-factor-finite',
                floor_block_names=list(REPAIR_BLOCKS), floor_margin_predicates=len(REPAIR_BLOCKS),
                correction_bound_upper=bounds, floor_ratio_upper=ratios,
                correction_evaluation=mode,
                joint_correction_metadata=None if joint_policy is None else joint_metadata(centered,joint_policy),
                correction_remainder_upper=None,
                right_inverse_Taylor_evaluations=0, right_inverse_Taylor_remainders=0,
                numerical_root_residual_predicates=1, root_stationarity_residual_evaluations=0,
                root_quotient_evaluation=root['root_quotient_evaluation'],
                root_scalar_quotient_model_calls=root['root_scalar_quotient_model_calls'],
                centered_input_error_upper=None if centered is None else [str(q) for q in centered['input_error_bounds']],
                centered_enclosure_basis=None if centered is None else ('joint_t_height_bernstein_with_complete_structured_input_error' if joint_policy is not None else 'bernstein_convex_hull_with_full_independent_input_error' if mode=='rational_bernstein_value' else 'power_sum_with_full_independent_input_error'),
                centered_enclosure_degree=None if centered is None else ORDER,
                centered_enclosure_control_count=None if centered is None else (ORDER+1)*(1 if joint_policy is None else 1<<joint_policy['depth']),
                centered_enclosure_piece_count=None if centered is None else (1 if joint_policy is None else 1<<joint_policy['depth']),
                interval_attempt_bound_upper=None if interval_bounds is None else [str(q) for q in interval_bounds],
                interval_attempt_failure=interval_failure,
                correction_ratio_diagnostic=[float(Fraction(q)) for q in ratios],
                untouched_analytic_blocks=untouched,
                proposed_Gram_positivity_by_square_identity=True,
                coefficient_semantics='All expanded coefficients enclose the same exact rational factor products.',
                auxiliary_nodes=meta['auxiliary_nodes'], hermite_multiplicities=meta['hermite_multiplicities'],
                target_multiplier=record['_target_multiplier'], potential_evaluation=record['_potential_evaluation'],
                target_evaluation=record['_target_evaluation'],
                root=root,
                direct_residual_bound=max(float_bound(q.bound().hi, PRECISION, True) for q in polynomial.values()),
                direct_remainder_bound=norm(tail),
                residual_coordinate_exponents=[list(e) for e in polynomial],
                residual_coordinate_upper=residual_coordinate_upper,
                precise_constant_bound=max(float_bound(abs(precise[0][i, 0]).hi, PRECISION, True) for i in range(len(build.COORDINATES))),
                precise_coefficient_width=max(float_bound(x.hi-x.lo, PRECISION, True) for C in precise for x in C.data),
                residual_seconds=residual_seconds, analytic_correction_seconds=correction_seconds,
                interval_correction_seconds=interval_seconds,
                elapsed_seconds=time.time()-started,
                scope='Complete finite-cell identity repaired inside analytic Bernstein Gram floors; only four correction margins are numerical.')
