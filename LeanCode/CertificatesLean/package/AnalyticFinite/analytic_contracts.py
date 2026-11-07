"""Strict stdlib contracts for exact Bernstein square/floor certificates."""
from fractions import Fraction
import re

from contracts import parameters, rational, finite
from .af_io import require, read as read_json
from .analytic_layout import dimensions as layout_dimensions, block_layout, SUPPORTED_PIVOTS
from .correction_policy import JOINT_CORRECTION_POLICY
from .joint_contracts import validate_policy, audit_metadata as audit_joint_metadata

METHOD = 'bernstein_residual_exact'
WITNESS_SCHEMA = 'thomson-intrinsic-bernstein-gram-v1'
REPORT_SCHEMA = 'thomson-intrinsic-bernstein-report-v1'
SHORT_METRIC_BITS = 32
from .root_proposals import ROOT_INVARIANT_UPPER, root_proposal

FLOOR_BLOCKS = ['F0', 'F1', 'M0_plus', 'M0_standard']
validate_policy(JOINT_CORRECTION_POLICY,FLOOR_BLOCKS)
UNIFORM_FIRST_CELLS = ('base_C_07', 'base_B_11', 'base_C_05')
BERNSTEIN_CENTER_CELLS = ('base_B_04', 'base_B_26')
COORDINATE_METHODS = dict(residual_coordinate_system='sigma_e2_e3_mod_1_sigma_squared',
    raw_coefficient_evaluation='exact_Newton_Reynolds_invariant_tensors',
    residual_quotient_codimension=2,
    omitted_residual_coordinates=[[0,0,0],[2,0,0]],
    residual_quotient_theorem='thm:invariant-residual-quotient')
ARITHMETIC_METHODS = dict(
    root_model_policy='one_explicit_contraction_defect',
    scalar_Cauchy_product='integer_midpoint_radius_complete_signed_Bernstein_tail',
    target_remainder_contraction='shared_Hermite_degree_directions_on_joint_cells',
    scalar_bits=256,
    matrix_bits=112,
    gram_coefficient_evaluation='exact_common_denominator_integer_expansion',
    height_translation_bits=32,
    residual_center_bits=128,
    correction_metric_center_bits=128,
    correction_metric_congruence='short_dyadic_left_metric_exact_congruence',
    correction_metric_construction='descending_rounded_integer_rows',
    analytic_metric_floor_theorem='lem:short-dyadic-left-inverse',
    exact_metric_inverse_evaluations=0,
    metric_floor_loss_enclosures=0,
    rational_coefficient_enclosure='direct_integer_floor_ceiling',
    correction_center_policy='all_coefficients_with_exact_recentring_error',
    correction_norm='positive_integer_weighted_symmetric_row_bound',
    residual_tensor_contraction='symmetric_upper_triangle_integer_image',
    residual_remainder_contraction='zero_free_block_symmetric_integer_image',
    free_Gram_coefficient_support='exact_polynomial_degree',
    polynomial_product_remainder='complete_Cauchy_tail_Bernstein_hull',
    correction_center_enclosure='power_or_Bernstein_or_joint_height_with_full_structured_input_error',
    correction_joint_policy_catalogue=JOINT_CORRECTION_POLICY,
    correction_Bernstein_cells=list(BERNSTEIN_CENTER_CELLS),
    correction_strategy='catalogue_uniform_power_Bernstein_or_joint_height')
SCALAR_METHODS = dict(
    scalar_reciprocal_remainder='direct_residual_over_range',
    scalar_log_remainder='integrated_ode_defect_positive_range',
    scalar_exp_remainder='integrated_ode_defect',
    contact_jet_evaluation='shared_riesz_derivative_recurrence',
    hermite_gap_evaluation='ten_distinct_node_pairs',
    normalized_phi_entire_remainder='signed_exponential_majorant')
SCALAR_ZERO_COUNTS = dict(
    numerical_scalar_reciprocal_Neumann_predicates=0,
    numerical_scalar_log_radius_predicates=0,
    numerical_normalized_phi_entire_exponential_enclosures=0)
SCALAR_CALL_COUNTS = ('scalar_reciprocal_model_calls', 'scalar_log_model_calls',
    'normalized_phi_entire_model_calls', 'scalar_constant_reciprocal_model_calls',
    'scalar_exp_model_calls', 'scalar_direct_quotient_model_calls')


def dimensions(cell):
    require(type(cell['degree']) is int and cell['degree'] in (12, 14, 16, 18),
            'Unsupported degree')
    require(type(cell['order']) is int and 4 <= cell['order'] <= 20,
            'Invalid original proposal-order annotation')
    parameters(cell)
    return layout_dimensions(cell['degree'])


def validation_order(order, proposal_order):
    require(type(order) is int and 4 <= order <= 34 and order >= proposal_order,
            'Invalid validation Taylor order')


def typed_equal(x, y):
    if type(x) is not type(y):
        return False
    if isinstance(y, list):
        return len(x) == len(y) and all(typed_equal(a, b) for a, b in zip(x, y))
    if isinstance(y, dict):
        return x.keys() == y.keys() and all(typed_equal(x[k], v) for k, v in y.items())
    return x == y


def packed_triangle(rows, order, diagonal):
    return (isinstance(rows, list) and len(rows) == order
            and all(isinstance(row, list) and len(row) == i + int(diagonal)
                    and all(type(x) is int and abs(x).bit_length() <= 2048 for x in row)
                    for i, row in enumerate(rows)))


def short_metric_record(block, delta):
    n = block['order']; exponent = max(block['K_diagonal_exponents'])
    theta = Fraction(n-1)*Fraction(2)**(exponent-SHORT_METRIC_BITS-1)
    return dict(block=block['name'], order=n, dyadic_bits=SHORT_METRIC_BITS,
                maximum_diagonal_exponent=exponent, analytic_floor_loss=str(theta),
                effective_floor=str(delta*(1-theta)))


def witness_audit(data, cell, dims):
    fields = {'schema', 'degree', 'bernstein_degree', 'factor_bits', 'metric_bits',
              'floor_exponent', 'moment_pivots', 'auxiliary_nodes', 'blocks'}
    require(isinstance(data, dict) and set(data) == fields, 'Wrong Bernstein witness fields')
    require(data['schema'] == WITNESS_SCHEMA and type(data['degree']) is int
            and data['degree'] == cell['degree'], 'Wrong Bernstein witness schema/degree')
    n = data['bernstein_degree']
    require(type(n) is int and 1 <= n <= 32, 'Invalid Bernstein degree')
    for field, lower in [('factor_bits', 32), ('metric_bits', 32)]:
        require(type(data[field]) is int and lower <= data[field] <= 512,
                'Invalid dyadic denominator scale: ' + field)
    exponent = data['floor_exponent']
    require(type(exponent) is int and -64 <= exponent <= 0, 'Invalid positive dyadic floor')
    delta = Fraction(2) ** exponent
    pivots = data['moment_pivots']
    d = cell['degree'] // 2
    require(isinstance(pivots, list) and len(pivots) == d
            and all(type(p) is int and (k, p) in SUPPORTED_PIVOTS
                    for k, p in enumerate(pivots)), 'Invalid moment pivots')
    records = block_layout(cell['degree'], pivots)
    require([r['name'] for r in records] == dims['block_names']
            and [len(r['free']) for r in records] == dims['orders'], 'Analytic layout mismatch')
    blocks = data['blocks']
    require(isinstance(blocks, list) and len(blocks) == len(records), 'Wrong factor-block count')
    block_fields = {'name', 'order', 'K_strict_lower', 'K_diagonal_exponents', 'F'}
    for block, record, size in zip(blocks, records, dims['orders']):
        require(isinstance(block, dict) and set(block) == block_fields,
                'Wrong physical-factor block fields')
        require(block['name'] == record['name'] and type(block['order']) is int
                and block['order'] == size, 'Wrong factor-block layout')
        require(packed_triangle(block['K_strict_lower'], size, False), 'Malformed lower metric')
        diag = block['K_diagonal_exponents']
        require(isinstance(diag, list) and len(diag) == size
                and all(type(e) is int and -128 <= e <= 128 for e in diag),
                'Malformed positive power-of-two metric diagonal')
        factors = block['F']
        require(isinstance(factors, list) and len(factors) == n + 1
                and all(packed_triangle(f, size, True) for f in factors),
                'Malformed physical Bernstein factors')
    tags = data['auxiliary_nodes']
    if cell['profile'] == 'general':
        require(isinstance(tags, list) and len(tags) == d - 4
                and all(t in ['A', 'B', 'C', 'D'] for t in tags), 'Invalid auxiliary nodes')
    else:
        require(tags == {'original': [], 'far4': ['B', 'D'], 'far6': ['B', 'B']}[cell['profile']],
                'Legacy profile tags mismatch')
    mult = {t: 2 + 2 * tags.count(t) for t in 'ABCD'}
    mult['minus_one'] = 5 if cell['profile'] == 'original' else 1
    require(sum(mult.values()) == cell['degree'] + 1, 'Wrong Hermite dimension')
    touched = [name for name in dims['block_names'] if name in FLOOR_BLOCKS]
    require(touched == FLOOR_BLOCKS, 'Incomplete analytic correction layout')
    return dict(proposal_order=n, bernstein_degree=n, factor_bits=data['factor_bits'],
                metric_bits=data['metric_bits'], floor_exponent=exponent,
                rational_floor=str(delta), auxiliary_nodes=tags, hermite_multiplicities=mult,
                repair_metric_data=[short_metric_record(b,delta) for b in blocks if b['name'] in FLOOR_BLOCKS],
                factor_entries=(n + 1) * dims['svec_dimension'],
                metric_dyadic_entries=sum(q * (q - 1) // 2 for q in dims['orders']),
                metric_diagonal_exponents=sum(dims['orders']), floor_block_names=touched,
                untouched_analytic_blocks=[name for name in dims['block_names'] if name not in touched])


def exact_nonnegative_list(values, length, label):
    require(isinstance(values, list) and len(values) == length
            and all(isinstance(v, str) for v in values), 'Malformed exact ' + label)
    result = [Fraction(value) for value in values]
    require(all(value >= 0 for value in result), 'Negative ' + label)
    return result


def exact_interval(value, label):
    require(isinstance(value, str), 'Missing exact ' + label)
    match = re.fullmatch(r'\[\s*([^,\[\]]+)\s*,\s*([^,\[\]]+)\s*\]', value)
    require(match is not None, 'Malformed exact ' + label)
    lo, hi = map(Fraction, match.groups())
    require(lo <= hi, 'Reversed ' + label)
    return lo, hi


def analytic_root_audit(root, cell, order):
    from math import comb
    expected = dict(root_validation='global_contraction_polynomial_defect',
        analytic_root_theorem='lem:contraction-polynomial-defect',
        root_quotient_evaluation='direct_scalar_residual_over_q_min',
        root_scalar_quotient_model_calls=1, root_contraction_map_evaluations=1,
        root_proposal_polynomial_degree=order,
        numerical_root_residual_predicates=1, root_stationarity_residual_evaluations=0,
        numerical_root_existence_predicates=0, numerical_root_derivative_predicates=0,
        numerical_root_tube_predicates=0)
    require(isinstance(root, dict), 'Missing analytic root report')
    exact_keys = ('root_q_lower', 'root_contraction_bound', 'root_height_lipschitz_bound',
                  'root_invariant_upper', 'root_defect_coefficient_bound',
                  'root_defect_remainder_bound', 'root_fixed_point_defect_upper',
                  'root_contraction_error')
    interval_keys = ('root_composition_error', 'root_model_error',
                     'root_polynomial_enclosure', 'a_enclosure')
    require(set(root) == set(expected) | set(exact_keys) | set(interval_keys)
            | {'root_proposal_enclosure'}, 'Wrong contraction-defect root fields')
    for key, value in expected.items():
        require(typed_equal(root.get(key), value), 'Analytic root mismatch: ' + key)
    require(all(isinstance(root.get(key), str) for key in exact_keys),
            'Missing exact contraction-defect quantity')
    values = {key: Fraction(root[key]) for key in exact_keys}
    q_lower = 1+(Fraction(cell['center'])-Fraction(cell['halfwidth']))/2
    require(q_lower >= Fraction(1, 2) and values['root_q_lower'] == q_lower,
            'Incorrect contraction exponent domain')
    contraction = (Fraction(1, 10) if q_lower < 1 else
                   Fraction(1, 19) * Fraction(5, 12)**(q_lower.numerator//q_lower.denominator-1))
    lipschitz = Fraction(5, 17)/q_lower
    require(values['root_contraction_bound'] == contraction < 1
            and values['root_height_lipschitz_bound'] == lipschitz,
            'Incorrect analytic contraction or height Lipschitz factor')
    require(values['root_invariant_upper'] == ROOT_INVARIANT_UPPER > 0,
            'Unbound invariant interval endpoint')
    coefficients = root_proposal(cell['center'], cell['halfwidth'], order)
    require(len(coefficients) == order+1 and all(type(x) is int for x in coefficients),
            'Malformed bound root polynomial')
    controls = []
    for i in range(order+1):
        controls.append(sum(Fraction(coefficients[k], 2**256) *
            Fraction(sum((-1)**(k-j)*comb(i,j)*comb(order-i,k-j)
                         for j in range(max(0,k-order+i), min(i,k)+1)), comb(order,k))
            for k in range(order+1)))
    enclosure = root['root_proposal_enclosure']
    require(isinstance(enclosure, list) and len(enclosure) == 2
            and all(isinstance(x, str) for x in enclosure), 'Malformed polynomial domain')
    lo_v, hi_v = map(Fraction, enclosure)
    require(lo_v == min(controls) and hi_v == max(controls)
            and 0 <= lo_v <= hi_v <= ROOT_INVARIANT_UPPER,
            'Root polynomial leaves the proved invariant interval')
    cp = values['root_defect_coefficient_bound']; ce = values['root_defect_remainder_bound']
    defect = values['root_fixed_point_defect_upper']; correction = values['root_contraction_error']
    require(cp >= 0 and ce >= 0 and defect == cp+ce
            and correction == lipschitz*defect/(1-contraction),
            'Incorrect complete contraction-defect error')
    composition_lo, composition_hi = exact_interval(root['root_composition_error'],
                                                    'root composition error')
    error_lo, error_hi = exact_interval(root['root_model_error'], 'root model error')
    polynomial_lo, polynomial_hi = exact_interval(root['root_polynomial_enclosure'],
                                                  'root polynomial enclosure')
    lo, hi = exact_interval(root['a_enclosure'], 'physical height enclosure')
    require(0 <= composition_lo <= composition_hi
            and composition_hi+correction <= error_lo <= error_hi,
            'Root model omits composition or fixed-point error')
    require(lo <= polynomial_lo-error_hi and hi >= polynomial_hi+error_hi,
            'Height interval omits the proved model error')
    require(Fraction(13, 50) < lo <= hi < Fraction(1, 3),
            'Root outside analytic finite range')
    return lo, hi


def scalar_model_audit(report, cell):
    for key, value in {**SCALAR_METHODS, **SCALAR_ZERO_COUNTS}.items():
        require(typed_equal(report.get(key), value), 'Scalar arithmetic mismatch: '+key)
    counts = {key: report.get(key) for key in SCALAR_CALL_COUNTS}
    require(all(type(value) is int and 0 <= value <= 10**9 for value in counts.values()),
            'Malformed proof-model scalar call counts')
    require(counts['scalar_reciprocal_model_calls'] > 0
            and counts['scalar_log_model_calls'] > 0
            and counts['scalar_exp_model_calls'] > 0
            and counts['scalar_direct_quotient_model_calls'] > 0
            and counts['scalar_constant_reciprocal_model_calls'] <= counts['scalar_reciprocal_model_calls'],
            'Inconsistent proof-model scalar call counts')
    center, halfwidth = Fraction(cell['center']), Fraction(cell['halfwidth'])
    lower, upper = center-halfwidth, center+halfwidth
    mode = 'entire' if lower <= 0 <= upper or (-4 < lower and upper < 4) else 'quotient'
    require(report.get('potential_evaluation') == mode,
            'Normalized-potential branch disagrees with cell')
    target_mode = ('balanced_exponential_constant_cancelled'
                   if cell['balance'] == 'riesz' else
                   'positive_quotient_constant_cancelled' if lower > 0 and mode == 'quotient' else
                   'normalized_phi')
    require(report.get('target_evaluation') == target_mode,
            'Target evaluation formula disagrees with cell balance')
    if cell['balance'] == 'riesz':
        require(center > 0 and lower > 0, 'Balanced target requires a positive cell')
    require((counts['normalized_phi_entire_model_calls'] > 0)
            == (mode == 'entire' and target_mode == 'normalized_phi'),
            'Inconsistent entire-potential model count')
    require(report.get('scalar_model_count_scope') == 'proof_models_excluding_Newton_proposals',
            'Scalar operation counts include untrusted proposal construction')
    return counts


def report_audit(path, cell, dims, metadata, order):
    report = read_json(path)
    validation_order(order, metadata['proposal_order'])
    expected = dict(
        schema=REPORT_SCHEMA, method=METHOD, passed=True, degree=cell['degree'],
        validation_order=order, proposal_order=metadata['proposal_order'],
        bernstein_degree=metadata['bernstein_degree'], factor_bits=metadata['factor_bits'],
        metric_bits=metadata['metric_bits'], floor_exponent=metadata['floor_exponent'],
        rational_floor=metadata['rational_floor'], minorant=cell['profile'],
        repair_metric_data=metadata['repair_metric_data'],
        effective_floor_lower=[r['effective_floor'] for r in metadata['repair_metric_data']],
        coefficient_rows=dims['retained_rows'], compatible_dimension=dims['retained_rows'],
        full_polynomial_coefficient_dimension=dims['coefficient_rows'],
        Gram_coordinates=dims['svec_dimension'], block_names=dims['block_names'],
        block_orders=dims['orders'], kernel_pivot_counts=dims['kernel_pivot_counts'],
        numerical_coefficient_inverse_predicates=0, full_coefficient_matrix_entries=0,
        F0_basis_inverse_predicates=0, numerical_Gram_PSD_predicates=0,
        right_inverse_Taylor_evaluations=0, right_inverse_Taylor_remainders=0,
        numerical_root_residual_predicates=1, root_stationarity_residual_evaluations=0,
        floor_margin_predicates=4, floor_block_names=metadata['floor_block_names'],
        untouched_analytic_blocks=metadata['untouched_analytic_blocks'],
        analytic_Gram_blocks=len(dims['orders']),
        proposed_Gram_positivity_by_square_identity=True,
        analytic_right_inverse_theorem='thm:four-block-right-inverse',
        analytic_floor_theorem='sec:bernstein-factor-finite',
        auxiliary_nodes=metadata['auxiliary_nodes'],
        hermite_multiplicities=metadata['hermite_multiplicities'],
        **ARITHMETIC_METHODS, **COORDINATE_METHODS,
        uniform_correction_attempted=cell['id'] in UNIFORM_FIRST_CELLS and cell['id'] not in JOINT_CORRECTION_POLICY,
        **parameters(cell))
    for key, value in expected.items():
        require(typed_equal(report.get(key), value), 'Bernstein report mismatch: ' + key)
    for key in ['center', 'halfwidth']:
        require(rational(report[key]) == rational(cell[key]), 'Cell parameter drift')
    from .analytic_layout import invariant_tags
    tags = [list(tag) for tag in invariant_tags(cell['degree'])
            if list(tag) not in COORDINATE_METHODS['omitted_residual_coordinates']]
    require(typed_equal(report.get('residual_coordinate_exponents'), tags),
            'Incorrect retained invariant residual coordinates')
    exact_nonnegative_list(report.get('residual_coordinate_upper'), len(tags),
                           'retained invariant residual coordinates')
    delta = Fraction(metadata['rational_floor'])
    bounds = exact_nonnegative_list(report['correction_bound_upper'], 4, 'correction bounds')
    ratios = exact_nonnegative_list(report['floor_ratio_upper'], 4, 'floor ratios')
    evaluation = report.get('correction_evaluation')
    joint_policy = JOINT_CORRECTION_POLICY.get(cell['id'])
    expected_mode = ('rational_joint_bernstein_value' if joint_policy is not None else
                     'rational_bernstein_value' if cell['id'] in BERNSTEIN_CENTER_CELLS else 'rational_center_value')
    require(type(evaluation) is str and evaluation in ('uniform_interval', 'rational_center_value', 'rational_bernstein_value', 'rational_joint_bernstein_value'),
            'Unrecognized analytic correction enclosure')
    effective_floors = [Fraction(r['effective_floor']) for r in metadata['repair_metric_data']]
    require(all(0 <= bound < floor and ratio == bound / floor and ratio < 1
                for bound, ratio, floor in zip(bounds, ratios, effective_floors)), 'Analytic short-metric floor exceeded')
    require(report['correction_remainder_upper'] is None,
            'Value-only correction has no Taylor remainder of the right inverse')
    attempted = report['uniform_correction_attempted']
    if not attempted:
        require(evaluation == expected_mode
                and report.get('interval_attempt_bound_upper') is None
                and report.get('interval_attempt_failure') is None,
                'Skipped uniform alternative has unexpected bounds or failure')
    else:
        interval_bounds = report.get('interval_attempt_bound_upper')
        interval_failure = report.get('interval_attempt_failure')
        if interval_bounds is None:
            require(type(interval_failure) is str and bool(interval_failure),
                    'Unsuccessful uniform attempt lacks an explicit failure')
        else:
            interval_bounds = exact_nonnegative_list(interval_bounds, 4,
                                                     'uniform-attempt bounds')
            require(interval_failure is None, 'Completed uniform attempt reports failure')
        if evaluation == 'uniform_interval':
            require(interval_bounds == bounds, 'Uniform result differs from attempted enclosure')
    if evaluation == 'uniform_interval':
        require(report['centered_input_error_upper'] is None,
                'Uniform correction has no separate rational-center error')
    else:
        errors = exact_nonnegative_list(report['centered_input_error_upper'], 4,
                                       'rational-center input-error bounds')
        require(all(error <= bound for error, bound in zip(errors, bounds)),
                'Input error exceeds complete correction bound')
    if evaluation == 'uniform_interval':
        require(all(report.get(key) is None for key in
                    ('centered_enclosure_basis','centered_enclosure_degree','centered_enclosure_control_count','centered_enclosure_piece_count')),
                'Uniform correction has unexpected center-enclosure metadata')
    else:
        use_bernstein=cell['id'] in BERNSTEIN_CENTER_CELLS
        expected_basis=('joint_t_height_bernstein_with_complete_structured_input_error' if joint_policy is not None else
                        'bernstein_convex_hull_with_full_independent_input_error' if use_bernstein
                        else 'power_sum_with_full_independent_input_error')
        expected_pieces=1 if joint_policy is None else 1<<joint_policy['depth']
        require(evaluation == expected_mode
                and report.get('centered_enclosure_basis') == expected_basis
                and type(report.get('centered_enclosure_degree')) is int
                and report['centered_enclosure_degree'] == order
                and type(report.get('centered_enclosure_control_count')) is int
                and report['centered_enclosure_control_count'] == (order+1)*expected_pieces
                and type(report.get('centered_enclosure_piece_count')) is int
                and report['centered_enclosure_piece_count'] == expected_pieces,
                'Incorrect source-bound center-enclosure metadata')
    joint_counts = audit_joint_metadata(report,joint_policy,order,bounds,
        None if evaluation=='uniform_interval' else errors,typed_equal,exact_nonnegative_list,exact_interval)
    diagnostic = report['correction_ratio_diagnostic']
    require(isinstance(diagnostic, list) and len(diagnostic) == 4
            and all(finite(x) and x >= 0 for x in diagnostic), 'Malformed floor diagnostics')
    # Floats are diagnostic. Accepting comparisons use exact rational row bounds.
    for key in ['direct_residual_bound', 'direct_remainder_bound',
                'precise_constant_bound', 'precise_coefficient_width']:
        require(finite(report[key]) and report[key] >= 0, 'Invalid residual bound: ' + key)
    lo, hi = analytic_root_audit(report['root'], cell, order)
    require(typed_equal(report.get('root_quotient_evaluation'),
                        report['root']['root_quotient_evaluation'])
            and typed_equal(report.get('root_scalar_quotient_model_calls'),
                            report['root']['root_scalar_quotient_model_calls']),
            'Root quotient report counters disagree')
    scalar_counts = scalar_model_audit(report, cell)
    return dict(maximum_floor_ratio=str(max(ratios)), diagnostic_maximum_floor_ratio=float(max(ratios)),
                **SCALAR_METHODS, **SCALAR_ZERO_COUNTS, **scalar_counts,
                **ARITHMETIC_METHODS, **COORDINATE_METHODS, uniform_correction_attempted=attempted,
                scalar_model_count_scope='proof_models_excluding_Newton_proposals',
                correction_evaluation=evaluation, **joint_counts,
                right_inverse_Taylor_evaluations=0, right_inverse_Taylor_remainders=0,
                root_validation='global_contraction_polynomial_defect',
                root_quotient_evaluation=report['root']['root_quotient_evaluation'],
                root_scalar_quotient_model_calls=report['root']['root_scalar_quotient_model_calls'],
                numerical_root_residual_predicates=1,
                root_stationarity_residual_evaluations=0, numerical_root_existence_predicates=0,
                numerical_root_derivative_predicates=0, numerical_root_tube_predicates=0,
                physical_height=[str(lo), str(hi)], numerical_coefficient_inverse_predicates=0,
                numerical_Gram_PSD_predicates=0, full_coefficient_matrix_entries=0,
                residual_quotient_coordinates=dims['retained_rows'],
                full_polynomial_coefficient_dimension=dims['coefficient_rows'],
                Gram_coordinates=dims['svec_dimension'], PSD_blocks=0,
                analytic_Gram_blocks=len(dims['orders']), floor_margin_predicates=4,
                factor_entries=metadata['factor_entries'],
                metric_dyadic_entries=metadata['metric_dyadic_entries'],
                metric_diagonal_exponents=metadata['metric_diagonal_exponents'],
                validation_order=order, proposal_order=metadata['proposal_order'],
                bernstein_degree=metadata['bernstein_degree'])
