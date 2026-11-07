"""Strict stdlib audit of a complete source-bound analytic finite replay.

This reads existing receipts; it never claims to rerun their numerical
arithmetic.  Every accepting leaf is checked against the current exact square-factor
proposal, the complete current source inventory, and the report contract.
"""
from fractions import Fraction
import hashlib
import importlib
import json
from pathlib import Path
import re
import sys

from .af_io import read, require, sha

CELL_KEYS = {'id', 'degree', 'center', 'halfwidth', 'order', 'profile', 'balance'}
SOURCE_FOLDERS = ('Finite', 'SymmetricFinite', 'AnalyticFinite')
POLICY = 'first-success-in-immutable-validation-orders'


def safe_file(root, name):
    require(isinstance(name, str) and name and '\\' not in name, 'Invalid relative file name')
    p = Path(name)
    require(not p.is_absolute() and '..' not in p.parts and '.' not in p.parts
            and str(p) == name, 'Unsafe or noncanonical relative file name')
    out = root
    for part in p.parts:
        out = out/part
        require(not out.is_symlink(), 'Symlink in audited file path')
    require(out.resolve().is_relative_to(root) and out.is_file(), 'Missing or escaping audited file')
    return out.resolve()


def exact_union(cells):
    intervals = []
    for cell in cells:
        c, h = Fraction(cell['center']), Fraction(cell['halfwidth'])
        require(h > 0 and c+h >= 0, 'Invalid exponent interval')
        intervals.append((max(Fraction(0), c-h), c+h))
    out = []
    for lo, hi in sorted(intervals):
        if out and lo <= out[-1][1]:
            out[-1][1] = max(hi, out[-1][1])
        else:
            out.append([lo, hi])
    return [[str(x) for x in pair] for pair in out]


def nonnegative_interval(value, label):
    require(isinstance(value, str), 'Missing exact '+label)
    match = re.fullmatch(r'\[\s*([^,\[\]]+)\s*,\s*([^,\[\]]+)\s*\]', value)
    require(match is not None, 'Malformed exact '+label)
    lo, hi = map(Fraction, match.groups())
    require(0 <= lo <= hi, 'Invalid nonnegative '+label)


def audit(root, index_reference, bindings):
    """Return complete-30 metrics only after every current-source gate passes."""
    require(__debug__ and not sys.flags.optimize, 'Audit must run without -O')
    root = Path(root).resolve()
    require(root.is_dir() and isinstance(index_reference, dict) and isinstance(bindings, dict),
            'Invalid audit arguments')
    seen = {}

    def bound(base, name, digest):
        require(isinstance(digest, str) and re.fullmatch(r'[0-9a-f]{64}', digest), 'Invalid SHA256')
        p = safe_file(base, name)
        require(sha(p) == digest, 'Changed audited bytes: '+name)
        require(p not in seen or seen[p] == digest, 'Inconsistent repeated file binding')
        seen[p] = digest
        return p

    require(index_reference['path'] == 'AnalyticFinite/INDEX.json'
            and index_reference['source_bindings'] == 'AnalyticFinite/source_bindings.json',
            'Unexpected analytic index/source inventory location')
    index_path = bound(root, index_reference['path'], index_reference['sha256'])
    binding_path = bound(root, index_reference['source_bindings'], index_reference['source_bindings_sha256'])
    sources = {name: digest for name, digest in bindings.items()
               if name.endswith('.py') and name.split('/')[0] in SOURCE_FOLDERS}
    actual = {str(p.relative_to(root)) for folder in SOURCE_FOLDERS
              for p in (root/folder).rglob('*.py') if p.is_file()}
    require(set(sources) == actual and sources, 'Incomplete current analytic numerical source inventory')
    for name, digest in sources.items():
        bound(root, name, digest)
    source_record = read(binding_path)
    require(source_record.get('schema') == 'thomson-analytic-finite-source-bindings-v1'
            and source_record['files'] == sources, 'Analytic source-binding inventory disagreement')
    require(Path(__file__).resolve() == root/'AnalyticFinite/replay_audit.py',
            'Audit module is not from the audited package')
    require(sha(Path(__file__).resolve()) == sources['AnalyticFinite/replay_audit.py'],
            'Unbound audit implementation')

    # These two imported providers are stdlib-only; no numerical verification
    # or optional numerical dependency is loaded by this audit.
    sys.path[:0] = [str(root), str(root/'Finite'), str(root/'Finite/kernel')]
    legacy = importlib.import_module('contracts')
    codec = importlib.import_module('codec')
    contracts = importlib.import_module('AnalyticFinite.analytic_contracts')
    for module, name in [(legacy, 'Finite/contracts.py'), (codec, 'Finite/kernel/codec.py'),
                         (contracts, 'AnalyticFinite/analytic_contracts.py')]:
        require(Path(module.__file__).resolve() == root/name, 'Unexpected imported audit provider')

    index = read(index_path)
    require(index.get('schema') == 'thomson-analytic-finite-index-v1', 'Wrong analytic index schema')
    entries = index['cells']
    require(isinstance(entries, list) and len(entries) == 30, 'Expected exactly 30 analytic cells')
    ids, by_id = [], {}
    for entry in entries:
        cell = entry['cell']
        require(isinstance(cell, dict) and set(cell) == CELL_KEYS, 'Wrong cell metadata fields')
        name = cell['id']
        require(isinstance(name, str) and re.fullmatch(r'[A-Za-z0-9_-]+', name)
                and name not in by_id, 'Invalid or repeated analytic cell ID')
        contracts.dimensions(cell)
        orders = entry['validation_orders']
        require(isinstance(orders, list) and orders
                and all(type(n) is int and 4 <= n <= 34 for n in orders)
                and orders == sorted(set(orders)), 'Invalid immutable validation order list')
        require(entry['proposal'] == 'AnalyticFinite/cells/'+name+'.json', 'Noncanonical cell manifest location')
        ids.append(name)
        by_id[name] = entry
    require(exact_union([e['cell'] for e in entries]) == [['0', '97']], 'Incomplete finite exponent cover')

    require(set(contracts.JOINT_CORRECTION_POLICY)<=set(ids),'Joint policy contains absent cells')

    summary_path = bound(root, index_reference['replay_summary'], index_reference['replay_summary_sha256'])
    base = summary_path.parent
    require(summary_path.name == 'SUMMARY.json', 'Unexpected replay summary filename')
    summary = read(summary_path)
    require(summary.get('schema') == 'thomson-analytic-finite-replay-summary-v1'
            and summary.get('status') == 'PASS_COMPLETE_ANALYTIC_FINITE_REPLAY'
            and summary.get('inputs_unchanged') is True
            and summary.get('complete_30_cell_plan') is True
            and type(summary.get('count')) is int and summary['count'] == 30,
            'No complete current-source analytic replay')
    plan_path = bound(base, 'PLAN.json', summary['plan_sha256'])
    plan = read(plan_path)
    require(plan.get('schema') == 'thomson-analytic-finite-replay-plan-v1'
            and plan.get('complete_30_cell_plan') is True
            and plan.get('validation_policy') == POLICY
            and contracts.typed_equal(plan['cells'], entries), 'Analytic plan/index disagreement')
    require(plan['finite_sources'] == sources
            and plan['worker_sha256'] == sources['AnalyticFinite/replay_worker.py']
            and plan['dispatcher_sha256'] == sources['AnalyticFinite/replay.py']
            and plan['index_sha256'] == index_reference['sha256']
            and plan['source_bindings_sha256'] == index_reference['source_bindings_sha256'],
            'Analytic replay source or index drift')
    require(plan['expected_closed_nonnegative_union'] == summary['closed_nonnegative_union'] == [['0', '97']],
            'Analytic plan/summary coverage disagreement')
    results = summary['results']
    require(isinstance(results, list) and len(results) == 30
            and [item['id'] for item in results] == ids, 'Analytic result inventory/order disagreement')

    accepted_bounds, accepted_orders, manifests, witness_files = [], {}, [], set()
    polynomial_coordinates = 0
    for item in results:
        name = item['id']
        entry, cell = by_id[name], by_id[name]['cell']
        order = item['validation_order']
        require(item.get('status') == 'PASS' and item.get('method') == contracts.METHOD
                and contracts.typed_equal(item['cell'], cell)
                and type(order) is int and order in entry['validation_orders'],
                'Analytic result parameter/status disagreement')
        attempts = item['attempts']
        prefix = entry['validation_orders'][:entry['validation_orders'].index(order)+1]
        require(isinstance(attempts, list) and len(attempts) == len(prefix), 'Incomplete adaptive attempt prefix')
        for position, (attempt, attempted_order) in enumerate(zip(attempts, prefix)):
            last = position == len(prefix)-1
            require(type(attempt['validation_order']) is int and attempt['validation_order'] == attempted_order
                    and attempt['status'] == ('PASS' if last else 'FAIL'), 'Invalid adaptive attempt semantics')
            if last:
                require(type(attempt['exit_code']) is int and attempt['exit_code'] == 0, 'Accepting worker did not exit successfully')
            else:
                require((attempt['exit_code'] is None or type(attempt['exit_code']) is int)
                        and isinstance(attempt.get('error'), str), 'Malformed rejected attempt')
            log_name = 'logs/'+name+'_order'+str(attempted_order)+'.log'
            require(attempt['log'] == log_name, 'Noncanonical adaptive log location')
            bound(base, log_name, attempt['log_sha256'])

        manifest_path = safe_file(root, entry['proposal'])
        manifest_digest = sha(manifest_path)
        bound(root, entry['proposal'], manifest_digest)
        manifest = read(manifest_path)
        require(manifest.get('schema') == 'thomson-analytic-finite-cell-manifest-v1'
                and contracts.typed_equal(manifest['cell'], cell)
                and contracts.typed_equal(manifest['validation_orders'], entry['validation_orders']),
                'Cell manifest/index disagreement')
        asset = manifest['witness']
        require(asset['compression'] == 'capd1-xz', 'Wrong Bernstein witness encoding')
        witness = bound(root, asset['path'], asset['compressed_sha256'])
        require(witness.is_relative_to(root/'AnalyticFinite/witnesses'), 'Witness outside analytic witness directory')
        require(isinstance(asset['semantic_sha256'], str) and re.fullmatch(r'[0-9a-f]{64}', asset['semantic_sha256']),
                'Invalid witness semantic digest')
        raw = codec.load(witness, asset['semantic_sha256'], limits=codec.RECIPE_LIMITS)
        dims = contracts.dimensions(cell)
        metadata = contracts.witness_audit(raw, cell, dims)
        del raw
        for allowed in entry['validation_orders']:
            contracts.validation_order(allowed, metadata['proposal_order'])
        witness_files.add(witness)
        manifests.append(dict(cell=cell, validation_orders=entry['validation_orders'], proposal=entry['proposal'],
                              proposal_sha256=manifest_digest, witness=asset))

        result_name = name+'/order'+str(order)+'/RESULT.json'
        require(item['result'] == result_name, 'Noncanonical accepted leaf location')
        result_path = bound(base, result_name, item['result_sha256'])
        leaf = result_path.parent
        result = read(result_path)
        required = dict(schema='thomson-analytic-finite-cell-v1', status='PASS_FRESH_ANALYTIC_CELL',
                        cell=cell, method=contracts.METHOD, validation_order=order,
                        proposal_order=metadata['proposal_order'], dimensions=dims, metadata=metadata,
                        inputs_unchanged=True, worker_sha256=plan['worker_sha256'])
        require(all(contracts.typed_equal(result.get(k), v) for k, v in required.items()), 'Accepting leaf contract mismatch')
        expected_inputs = dict(sources)
        expected_inputs.update({'AnalyticFinite/INDEX.json': plan['index_sha256'],
                                'AnalyticFinite/source_bindings.json': plan['source_bindings_sha256'],
                                entry['proposal']: manifest_digest, asset['path']: asset['compressed_sha256']})
        require(result['source_sha256'] == expected_inputs, 'Accepting leaf input snapshot mismatch')
        files = result['files']
        require(isinstance(files, dict) and {'CELL.json', 'INPUTS.json', 'verified.json'} <= set(files)
                and 'RESULT.json' not in files, 'Incomplete accepting leaf outputs')
        require({p.name for p in leaf.iterdir() if p.is_file()} == set(files)|{'RESULT.json'}, 'Unbound accepting leaf file')
        for filename, digest in files.items():
            require(Path(filename).name == filename, 'Nested accepting leaf output')
            bound(leaf, filename, digest)
        require(contracts.typed_equal(read(leaf/'CELL.json'), cell), 'Accepting leaf cell drift')
        inputs = read(leaf/'INPUTS.json')
        expected_snapshot = dict(cell=cell, method=contracts.METHOD, validation_order=order,
                                 proposal_order=metadata['proposal_order'], files=expected_inputs,
                                 worker_sha256=plan['worker_sha256'])
        require(all(contracts.typed_equal(inputs.get(k), v) for k, v in expected_snapshot.items()), 'Leaf INPUTS disagreement')
        report = read(leaf/'verified.json')
        nonnegative_interval(report['root']['root_composition_error'], 'root composition error')
        nonnegative_interval(report['root']['root_model_error'], 'root model error')
        accepted = contracts.report_audit(leaf/'verified.json', cell, dims, metadata, order)
        require(contracts.typed_equal(accepted, item['bounds']) and contracts.typed_equal(accepted, result['bounds']),
                'Numerical acceptance bounds disagree with receipts')
        accepted_bounds.append(accepted)
        accepted_orders[name] = order
        polynomial_coordinates += (metadata['proposal_order']+1)*dims['svec_dimension']

    require(all(safe_file(root, str(p.relative_to(root))) == p and sha(p) == digest
                for p, digest in seen.items()),
            'Audited inputs or evidence changed during audit')
    final_inventory = {str(p.relative_to(root)) for folder in SOURCE_FOLDERS
                       for p in (root/folder).rglob('*.py') if p.is_file()}
    require(final_inventory == actual, 'Source inventory changed during audit')
    mapping = json.dumps(manifests, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()
    return dict(cells=30, cell_ids=ids, closed_nonnegative_union=[['0', '97']],
                **contracts.SCALAR_METHODS,
                **{key: sum(bound[key] for bound in accepted_bounds)
                   for key in (*contracts.SCALAR_ZERO_COUNTS, *contracts.SCALAR_CALL_COUNTS)},
                scalar_model_count_scope='proof_models_excluding_Newton_proposals',
                validation_orders=accepted_orders,
                maximum_floor_ratio=str(max(Fraction(b['maximum_floor_ratio']) for b in accepted_bounds)),
                diagnostic_maximum_floor_ratio=float(max(Fraction(b['maximum_floor_ratio']) for b in accepted_bounds)),
                numerical_Gram_PSD_predicates=0,
                correction_enclosure_methods={method: sum(b['correction_evaluation'] == method
                    for b in accepted_bounds) for method in ('uniform_interval', 'rational_center_value', 'rational_bernstein_value', 'rational_joint_bernstein_value')},
                joint_correction_arithmetic={key:sum(b[key] for b in accepted_bounds) for key in (
                    'joint_height_pieces','joint_Bernstein_controls','shared_target_remainder_generators','scalar_rational_evaluations',
                    'scalar_polynomial_evaluations','scalar_denominator_evaluations',
                    'exact_coefficient_congruences','sqrt2_polynomial_entries',
                    'congruence_tensor_images','congruence_tensor_entries',
                    'integer_polynomial_contractions','exact_height_numerator_coefficients',
                    'metric_difference_control_enclosures','metric_difference_piece_enclosures',
                    'metric_difference_matrix_products')},
                right_inverse_Taylor_evaluations=sum(b['right_inverse_Taylor_evaluations'] for b in accepted_bounds),
                right_inverse_Taylor_remainders=sum(b['right_inverse_Taylor_remainders'] for b in accepted_bounds),
                root_validation_methods={'global_contraction_polynomial_defect': sum(
                    b['root_validation'] == 'global_contraction_polynomial_defect' for b in accepted_bounds)},
                root_quotient_evaluation_methods={'direct_scalar_residual_over_q_min': sum(
                    b['root_quotient_evaluation'] == 'direct_scalar_residual_over_q_min' for b in accepted_bounds)},
                root_scalar_quotient_model_calls=sum(b['root_scalar_quotient_model_calls'] for b in accepted_bounds),
                numerical_root_residual_predicates=sum(b['numerical_root_residual_predicates'] for b in accepted_bounds),
                root_stationarity_residual_evaluations=sum(b['root_stationarity_residual_evaluations'] for b in accepted_bounds),
                numerical_root_existence_predicates=sum(b['numerical_root_existence_predicates'] for b in accepted_bounds),
                numerical_root_derivative_predicates=sum(b['numerical_root_derivative_predicates'] for b in accepted_bounds),
                numerical_root_tube_predicates=sum(b['numerical_root_tube_predicates'] for b in accepted_bounds),
                analytic_Gram_blocks=sum(b['analytic_Gram_blocks'] for b in accepted_bounds),
                floor_margin_predicates=sum(b['floor_margin_predicates'] for b in accepted_bounds),
                factor_entries=sum(b['factor_entries'] for b in accepted_bounds),
                metric_dyadic_entries=sum(b['metric_dyadic_entries'] for b in accepted_bounds),
                metric_diagonal_exponents=sum(b['metric_diagonal_exponents'] for b in accepted_bounds),
                numerical_coefficient_inverse_predicates=0, full_coefficient_matrix_entries=0,
                residual_quotient_coordinates=sum(b['residual_quotient_coordinates'] for b in accepted_bounds),
                full_polynomial_coefficient_dimension=sum(b['full_polynomial_coefficient_dimension'] for b in accepted_bounds),
                Gram_coordinates=sum(b['Gram_coordinates'] for b in accepted_bounds),
                expanded_polynomial_Gram_coordinates=polynomial_coordinates,
                PSD_blocks=sum(b['PSD_blocks'] for b in accepted_bounds),
                witness_bytes=sum(p.stat().st_size for p in witness_files),
                manifest_cell_mapping_sha256=hashlib.sha256(mapping).hexdigest())
