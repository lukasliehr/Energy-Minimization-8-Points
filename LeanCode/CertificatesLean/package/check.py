#!/usr/bin/env python3
"""Audit the reduced package and, by default, freshly replay its remaining tail stages.

Use --integrity-only to audit stored evidence without rerunning CAP arithmetic.
The 30 current analytic-residual finite acceptance reports are audited in both modes.  A current
finite replay is counted only after checking its complete source inventory,
cell semantics, output hashes and numerical acceptance report.  This command
never silently launches the full 30-cell finite computation.
"""
import argparse
from fractions import Fraction
import hashlib
import importlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
TAIL_CORE = {
    'Tail/dihedral_basis.py', 'Tail/invariant_basis.py', 'Tail/edge_basis.py',
    'Tail/exact_geometry.py',
    'Tail/verify_boundary.py', 'Tail/witness.json',
}
TAIL_STAGES = {
    'gnomonic_boundary': 'PASS_EXACT_QUADRATIC_FIELD_BOUNDARY',
}





def require(condition, message):
    if not condition:
        raise ValueError(message)



def read(path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, 'Duplicate JSON key: ' + key)
            result[key] = value
        return result

    def invalid(value):
        raise ValueError('Nonfinite JSON value: ' + value)

    return json.loads(Path(path).read_text(), object_pairs_hook=unique,
                      parse_constant=invalid)



def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            digest.update(block)
    return digest.hexdigest()



def inside(root, name):
    require(isinstance(name, str) and name, 'Input path must be a nonempty string')
    relative = Path(name)
    require(not relative.is_absolute() and '..' not in relative.parts,
            'Unsafe input path: ' + name)
    path = root / relative
    require(not path.is_symlink() and path.resolve().is_relative_to(root),
            'External input: ' + name)
    for parent in path.parents:
        if parent == root:
            break
        require(not parent.is_symlink(), 'Symlink in input path: ' + name)
    require(path.is_file(), 'Missing input: ' + str(path))
    return path



def bound(root, name, digest):
    require(isinstance(digest, str) and re.fullmatch(r'[0-9a-f]{64}', digest),
            'Malformed SHA256: ' + str(name))
    path = inside(root, name)
    require(sha(path) == digest, 'Hash mismatch: ' + str(path))
    return path



def references(value):
    """INDEX replay fields accept one {summary,sha256} or a list of them."""
    if value is None:
        return []
    result = value if isinstance(value, list) else [value]
    require(all(isinstance(item, dict) and 'summary' in item and 'sha256' in item
                for item in result), 'Replay references need summary and sha256')
    return result



def integrity(root):
    manifest = read(inside(root, 'MANIFEST.json'))
    require(manifest['schema'] in {
        'thomson-analytic-residual-manifest-v3'}, 'Manifest schema')
    files = manifest['files']
    require(isinstance(files, dict) and files, 'Empty manifest')
    for name, item in files.items():
        path = bound(root, name, item['sha256'])
        require(type(item['bytes']) is int and path.stat().st_size == item['bytes'],
                'Changed input size: ' + name)
    for name in ['INDEX.json', 'source_bindings.json', 'check.py']:
        require(name in files, 'Manifest omits required file: ' + name)
    for path in root.rglob('*'):
        require(not path.is_symlink(), 'Symlink in package: ' + str(path))
        require(path.suffix not in {'.lean', '.olean', '.ilean'},
                'Lean file in numerical-only package: ' + str(path))
    bindings = read(inside(root, 'source_bindings.json'))['files']
    require(isinstance(bindings, dict), 'Source bindings must be a mapping')
    for name, digest in bindings.items():
        bound(root, name, digest)
    source_paths = {path.name for path in root.glob('*.py') if path.is_file()} | {
        str(path.relative_to(root)) for folder in ['Finite', 'SymmetricFinite', 'AnalyticFinite', 'Tail']
        for path in (root / folder).rglob('*.py') if path.is_file()}
    bound_python = {name for name in bindings if name.endswith('.py')}
    require(source_paths == bound_python, 'Complete active Python source inventory mismatch')
    require(TAIL_CORE | {'Tail/replay.py'} <= set(bindings),
            'Missing reduced tail source/witness binding')
    require(all(name in files for name in bindings), 'Manifest omits a bound source')
    return manifest, bindings



def audit_boundary(report, bindings):
    require(report['status'] == TAIL_STAGES['gnomonic_boundary'], 'Boundary status')
    require(all(Fraction(report[key]) == Fraction(value) for key, value in {
        'gap': '33/1000', 'normalization_radius': '61/200',
        'annulus_lower': '3620/3721', 'higher': '33/2000'}.items()), 'Boundary constants')
    free = dict(zip(['0+', '0-', '4+', '4-', '1', '2', '3'], [12, 3, 7, 7, 12, 14, 12]))
    affine = dict(zip(['0+', '4+', '4-', '1', '2', '3'], [2, 1, 1, 2, 2, 1]))
    dimensions = {label + '/' + key: value for label, blocks in
                  [('free', free), ('upper', affine), ('lower', affine)]
                  for key, value in blocks.items()}
    dimensions.update({f'edge/{d}/{parity}': n for d in (1, 2)
                       for parity, n in [('+', 8), ('-', 6)]})
    exact_counts = dict(variables=13, coefficient_identity_count=174,
        full_polynomial_dimension=2380, factor_coordinates=539,
        contact_polynomials_constructed=2, edge_orbit_products=2, edge_orbit_multiplicity=8,
        basis_matrix_inversions=0, gram_schmidt_steps=0,
        Gram_positivity_predicates=0, preconditioner_coordinates=0,
        geometry_root_enclosures=0, outward_interval_operations=0, high_precision_root_bounds=0,
        quartic_pair_count_operations=0, lift_representation_counts=0)
    require(all(type(report[k]) is int and report[k] == v for k, v in exact_counts.items()) and
            report['block_dimensions'] == dimensions and
            all(type(v) is int for v in report['block_dimensions'].values()),
            'Boundary factored dihedral layout')
    require(report['slice_basis'] == 'rationalized-fourier-slice-v1' and
            report['polynomial_basis'] == 'analytic-real-fourier-dihedral-polynomial-v1' and
            report['edge_basis'] == 'explicit-stabilizer-parity-v1' and
            report['invariant_coefficient_basis'] == 'unitary-fourier-monomials-v1' and
            report['symmetry_group'] == 'D8_order_16', 'Boundary analytic bases')
    floor = Fraction(report['free_floor'])
    entry = Fraction(report['coefficient_correction_entry_bound'])
    spectral = Fraction(report['spectral_correction_bound'])
    require(floor == Fraction(1, 10**7) and 0 <= entry and
            spectral == 105 * entry and spectral < floor and
            Fraction(report['free_correction_ratio']) == spectral / floor,
            'Boundary invariant correction below the analytic positive floor')
    require(report['exact_coefficient_field'] == 'Q(sqrt2)', 'Boundary exact coefficient field')
    require(report['coefficient_lift']=='canonical_symmetric_monomial_split',
            'Canonical monomial coefficient lift')
    require(report['coefficient_majorant']=='quadratic_norm_identity',
            'Algebraic norm coefficient bound')
    pairs=report['exact_residual_coordinates']; bounds=report['invariant_coordinate_bounds']
    require(isinstance(pairs,list) and len(pairs)==174 and isinstance(bounds,list) and
            len(bounds)==174 and all(isinstance(v,list) and len(v)==2 and
            all(isinstance(c,str) for c in v) for v in pairs) and
            all(isinstance(v,str) for v in bounds),
            'Exact invariant coefficient inventory')
    for pair,value in zip(pairs,bounds):
        a,b=map(Fraction,pair)
        expected=abs(a*a-2*b*b)/(abs(a)+abs(b)) if a*b<0 else abs(a)+Fraction(3,2)*abs(b)
        require(Fraction(value)==expected,
                'Exact invariant coordinate majorant')
    require(report['source_sha256'] == {name: bindings['Tail/' + name] for name in {
        'verify_boundary.py', 'dihedral_basis.py', 'invariant_basis.py', 'edge_basis.py',
        'exact_geometry.py'}}, 'Boundary source bindings')
    require(report['witness_sha256'] == bindings['Tail/witness.json'], 'Boundary witness binding')



def audit_tail(root, summary_path, bindings):
    report = read(summary_path)
    require(report['schema'] == 'thomson-analytic-local-tail-replay-v3' and
            report['status'] == 'PASS_FRESH_REDUCED_TAIL_NUMERICS' and
            report['cutoff'] == 97 and report['inputs_unchanged'] is True and
            report['analytic_tail_proof_label'] == 'prop:tail97' and
            report['analytic_tail_parameter_lower'] == '97/2',
            'Reduced tail summary acceptance')
    expected_sources = {name: bindings[name] for name in TAIL_CORE}
    require(report['source_sha256'] == expected_sources and
            report['driver_sha256'] == bindings['Tail/replay.py'], 'Tail source inventory')
    inputs = read(inside(summary_path.parent, 'INPUTS.json'))
    require(inputs['schema'] == 'thomson-reduced-tail-inputs-v1' and
            inputs['files'] == expected_sources and
            inputs['driver_sha256'] == report['driver_sha256'], 'Tail INPUTS binding')
    require(report['tail_scalar_CAP_predicates'] == 0 and
            report['analytically_replaced_tail_scalar_predicates'] == 51 and
            report['local_tensor_scalar_predicates'] == 0 and
            report['local_tensor_systems'] == 0 and
            report['maximum_local_system_dimension'] == 0 and
            report['boundary_geometry_root_enclosures'] == 0 and
            report['boundary_outward_interval_operations'] == 0 and
            report['boundary_coefficient_field'] == 'Q(sqrt2)' and
            report['boundary_coefficient_lift'] == 'canonical_symmetric_monomial_split' and
            type(report['boundary_quartic_pair_count_operations']) is int and
            report['boundary_quartic_pair_count_operations'] == 0 and
            report['external_local_tensor_witness'] is False and
            report['historical_reports_used'] is False and report['lean_executed'] is False,
            'Reduced tail coverage')
    require([run['check'] for run in report['runs']] == list(TAIL_STAGES), 'Tail stage coverage')
    receipts, receipt_hashes = {}, {}
    for run in report['runs']:
        name = run['check']
        require(run['status'] == TAIL_STAGES[name] and type(run['exit_code']) is int
                and run['exit_code'] == 0 and run['report'] == name + '.json', 'Tail run status')
        path = bound(summary_path.parent, run['report'], run['report_sha256'])
        receipts[name] = read(path)
        receipt_hashes[run['report']] = run['report_sha256']
    audit_boundary(receipts['gnomonic_boundary'], bindings)
    # Also catch a source edited since the surrounding package integrity audit.
    for name, digest in expected_sources.items():
        bound(root, name, digest)
    bound(root, 'Tail/replay.py', report['driver_sha256'])
    return dict(stages=1, cutoff=97, analytic_tail_proof_label='prop:tail97',
                analytic_tail_parameter_lower='97/2',
                local_scalar_predicates=0, local_tensor_systems=0,
                residual_tail_scalar_CAP_predicates=0,
                analytically_replaced_tail_scalar_predicates=51,
                analytically_replaced_local_norm_predicates=11,
                boundary_factor_entries=539, boundary_maximum_factor_dimension=14,
                boundary_Gram_positivity_predicates=0, boundary_residual_coordinates=174,
                boundary_residual_margin_predicates=1,
                boundary_geometry_root_enclosures=0, boundary_outward_interval_operations=0,
                boundary_quartic_pair_count_operations=0,
                boundary_coefficient_field="Q(sqrt2)")



def audit_analytic_package(root, index, manifest, bindings, metadata_snapshot):
    """Audit only the new residual certificates and the exact-field reduced tail."""
    sys.path.insert(0, str(root))
    checker = importlib.import_module('AnalyticFinite.replay_audit')
    require(Path(checker.__file__).resolve() == root / 'AnalyticFinite/replay_audit.py',
            'Unexpected analytic replay audit module')
    reference = index['analytic_finite']
    finite = checker.audit(root, reference, bindings)
    require(finite['cells'] == 30 and finite['closed_nonnegative_union'] == [['0', '97']],
            'Analytic finite complete cover')
    require(index['finite_closed_union'] == [['0', '97']] and index['tail_lower'] == '97',
            'Analytic finite/tail join')
    proposal_index = read(bound(root, reference['path'], reference['sha256']))
    entries = index['finite_cells']
    require(len(entries) == 30 and len({e['cell']['id'] for e in entries}) == 30,
            'Root analytic cell inventory')
    expected = {e['cell']['id']: e for e in proposal_index['cells']}
    require({e['cell']['id'] for e in entries} == set(expected) == set(finite['cell_ids']),
            'Root/analytic cell identity disagreement')
    for entry in entries:
        cell = entry['cell']
        require(entry['method'] == 'bernstein_residual_exact' and
                cell == expected[cell['id']]['cell'] and
                entry['validation_order'] in expected[cell['id']]['validation_orders'] and
                entry['validation_order'] == finite['validation_orders'][cell['id']],
                'Root/analytic cell parameter disagreement')
        interval = [str(max(Fraction(0), Fraction(cell['center'])-Fraction(cell['halfwidth']))),
                    str(Fraction(cell['center'])+Fraction(cell['halfwidth']))]
        require(entry['closed_nonnegative_interval'] == interval, 'Root analytic interval drift')
    tail_refs = references(index['tail_replay'])
    require(len(tail_refs) == 1, 'One current reduced tail replay is required')
    tail_path = bound(root, tail_refs[0]['summary'], tail_refs[0]['sha256'])
    tail_result = audit_tail(root, tail_path, bindings)
    for name, digest in metadata_snapshot.items():
        bound(root, name, digest)
    return dict(
        status='PASS_REDUCED_PACKAGE_INTEGRITY', manifest_files=len(manifest['files']),
        package_inputs_sha256=metadata_snapshot,
        finite_basis_implementation='analytic_contact_jet_right_inverse',
        finite_cells=30, closed_finite_union=[['0', '97']], tail_lower='97',
        stored_finite_acceptance_reports_audited=30,
        stored_current_source_finite_replay_cells=sorted(finite['cell_ids']),
        stored_current_source_finite_replay_count=30,
        stored_current_source_finite_replay_covers_all_30=True,
        analytic_finite=finite, stored_reduced_tail=tail_result,
        maximum_floor_ratio=finite['maximum_floor_ratio'],
        numerical_Gram_PSD_predicates=0,
        finite_floor_margin_predicates=finite['floor_margin_predicates'],
        numerical_coefficient_inverse_predicates=0,
        numerical_F0_basis_inverse_predicates=0,
        fresh_tail_executed_by_this_command=False,
        fresh_finite_cells_executed_by_this_command=0,
        all_finite_arithmetic_freshly_reexecuted_by_this_command=False,
        lean_executed=False,
        scope='Exact coverage, exact Bernstein square-factor witness semantics, and current-source '
              'residual-only acceptance receipts. Universal contact-jet identities and '
              'the equality proof are analytic premises supplied by the paper.'), bindings




def audit_package(root=ROOT):
    require(__debug__ and not sys.flags.optimize, 'Run Python without -O')
    sys.dont_write_bytecode = True
    root = Path(root).resolve()
    metadata_snapshot = {name: sha(inside(root, name))
                         for name in ['MANIFEST.json', 'INDEX.json', 'source_bindings.json', 'ANALYTIC_PREMISES.json']}
    manifest, bindings = integrity(root)
    index = read(inside(root, 'INDEX.json'))
    require(index['schema'] == 'thomson-analytic-residual-certificates-v3', 'Index schema')
    ledger = index['analytic_premise_ledger']
    premise = read(bound(root, ledger['path'], ledger['sha256']))
    require(premise['schema'] == 'thomson-analytic-premise-ledger-v2' and
            premise['active_finite_route'] == 'bernstein_residual_exact' and
            premise['numerical_coefficient_inverse_predicates'] == 0 and
            premise['numerical_F0_basis_inverse_predicates'] == 0 and
            premise['numerical_Gram_PSD_predicates'] == 0 and
            type(premise['finite_floor_margin_predicates']) is int and
            premise['finite_floor_margin_predicates'] > 0,
            'Analytic premise ledger')
    result, bindings = audit_analytic_package(root, index, manifest, bindings, metadata_snapshot)
    finite = result['analytic_finite']
    require(premise['finite_floor_margin_predicates'] == finite['floor_margin_predicates'],
            'Analytic premise floor count disagrees with fully audited reports')
    count = len(index['finite_cells'])
    require(finite['root_validation_methods'] == {'global_contraction_polynomial_defect': count}
            and finite['root_quotient_evaluation_methods'] == {'direct_scalar_residual_over_q_min': count},
            'Active global-root construction disagreement')
    zero_fields = ('root_stationarity_residual_evaluations',
                   'numerical_root_existence_predicates', 'numerical_root_derivative_predicates',
                   'numerical_root_tube_predicates')
    require(all(type(finite.get(key)) is int and finite[key] == 0
                and type(premise.get(key)) is int and premise[key] == 0 for key in zero_fields),
            'Active root predicate ledger disagreement')
    require(type(finite.get('numerical_root_residual_predicates')) is int
            and finite['numerical_root_residual_predicates'] == count
            and type(premise.get('numerical_root_residual_predicates')) is int
            and premise['numerical_root_residual_predicates'] == count,
            'Incorrect number of contraction-defect root predicates')
    active_root = premise['active_root_construction']
    require(type(active_root.get('numerical_root_residual_predicates')) is int
            and active_root['numerical_root_residual_predicates'] == count,
            'Incorrect active contraction-defect predicate count')
    require(active_root['root_validation'] == 'global_contraction_polynomial_defect'
            and active_root['quotient_evaluation'] == 'direct_scalar_residual_over_q_min'
            and active_root['proof_label'] == 'lem:contraction-polynomial-defect'
            and active_root['quotient_proof_label'] == 'lem:direct-affine-quotient-model'
            and type(active_root['cells']) is int and active_root['cells'] == count
            and type(active_root['root_scalar_quotient_model_calls']) is int
            and active_root['root_scalar_quotient_model_calls'] == finite['root_scalar_quotient_model_calls']
            and all(type(active_root.get(key)) is int and active_root[key] == 0 for key in zero_fields),
            'Active root construction ledger disagreement')
    return result, bindings


def fresh_tail(root, output, bindings, metadata_snapshot):
    require(not output.exists(), 'Fresh replay output must not exist: ' + str(output))
    require(not output.is_relative_to(root), 'Place fresh output outside the immutable package')
    for name, digest in metadata_snapshot.items():
        bound(root, name, digest)
    environment = dict(os.environ)
    for key in list(environment):
        if key.startswith('N8_') or key in {'PYTHONOPTIMIZE', 'PYTHONPATH'}:
            environment.pop(key, None)
    environment['PYTHONDONTWRITEBYTECODE'] = '1'
    completed = subprocess.run([sys.executable, '-B', '-u', str(root / 'Tail/replay.py'),
                                '--output', str(output)], cwd=root, env=environment,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    require(completed.returncode == 0, 'Fresh tail replay failed:\n' + completed.stdout)
    result = audit_tail(root, output / 'SUMMARY.json', bindings)
    integrity(root)
    for name, digest in metadata_snapshot.items():
        bound(root, name, digest)
    return result



def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--integrity-only', action='store_true',
                        help='Audit stored reports and hashes; do not execute fresh CAP arithmetic')
    parser.add_argument('--output', type=Path,
                        help='Keep fresh tail replay in this new directory outside the package')
    args = parser.parse_args()
    require(not (args.integrity_only and args.output), '--output requires fresh replay mode')
    root = ROOT.resolve()
    result, bindings = audit_package(root)
    if not args.integrity_only:
        if args.output:
            output = args.output.resolve()
            result['fresh_tail'] = fresh_tail(root, output, bindings, result['package_inputs_sha256'])
            result['fresh_tail_output'] = str(output)
        else:
            with tempfile.TemporaryDirectory(prefix='thomson-reduced-tail-') as temporary:
                result['fresh_tail'] = fresh_tail(root, Path(temporary) / 'replay', bindings,
                                                 result['package_inputs_sha256'])
            result['fresh_tail_output'] = None
        result['status'] = 'PASS_REDUCED_PACKAGE_AND_FRESH_TAIL'
        result['fresh_tail_executed_by_this_command'] = True
        result['scope'] += ' The remaining boundary SOS stage was also freshly executed.'
    print(json.dumps(result, indent=2, allow_nan=False))



if __name__ == '__main__':
    main()
