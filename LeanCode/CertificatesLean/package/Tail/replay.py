#!/usr/bin/env python3
"""Replay the residual tail CAP after the analytic reductions.

The graph theorem, cube algebra, contact spectra, centered quadratic bound,
and annulus contraction are proved in the paper. The only replay stage
is the boundary SOS; all local tensor bounds are analytic.
All51 former residual scalar tests are replaced by proofs in the paper.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
CORE = [
    'Tail/dihedral_basis.py', 'Tail/invariant_basis.py', 'Tail/edge_basis.py',
    'Tail/exact_geometry.py',
    'Tail/verify_boundary.py', 'Tail/witness.json',
]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    def unique(items):
        result = {}
        for key, value in items:
            require(key not in result, 'Duplicate JSON key: '+key)
            result[key] = value
        return result
    def invalid(value):
        raise ValueError('Nonfinite JSON constant: '+value)
    return json.loads(Path(path).read_text(), object_pairs_hook=unique,
                      parse_constant=invalid)


def write(path, value):
    Path(path).write_text(json.dumps(value, indent=2, allow_nan=False)+'\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    require(__debug__ and not sys.flags.optimize, 'Run without -O')
    output = args.output.resolve()
    require(not output.exists(), 'Use a new output directory')
    bindings = {name: sha(ROOT/name) for name in CORE}
    driver_hash = sha(Path(__file__))
    output.mkdir(parents=True)
    env = dict(os.environ)
    env.pop('PYTHONOPTIMIZE', None)
    env.pop('PYTHONPATH', None)
    env.update(PYTHONDONTWRITEBYTECODE='1', OPENBLAS_NUM_THREADS='1',
               OMP_NUM_THREADS='1', MKL_NUM_THREADS='1')
    write(output/'INPUTS.json', dict(
        schema='thomson-reduced-tail-inputs-v1', files=bindings,
        driver_sha256=driver_hash, python=sys.version))
    runs = []
    started = time.monotonic()

    def run(label, script, status, *arguments):
        report = output/(label+'.json')
        command = [sys.executable, '-B', '-u', str(HERE/script),
                   *map(str, arguments), '--output', str(report)]
        before = time.monotonic()
        with (output/(label+'.log')).open('w') as log:
            result = subprocess.run(command, cwd=ROOT, env=env,
                                    stdout=log, stderr=subprocess.STDOUT)
        require(result.returncode == 0, label+' failed; see '+str(output/(label+'.log')))
        receipt = read(report)
        require(receipt['status'] == status, label+' status mismatch')
        runs.append(dict(check=label, status=status, exit_code=0,
                         seconds=time.monotonic()-before,
                         report=report.name, report_sha256=sha(report)))
        print(label+': PASS', flush=True)
        return report, receipt

    boundary, boundary_receipt = run('gnomonic_boundary', 'verify_boundary.py',
                      'PASS_EXACT_QUADRATIC_FIELD_BOUNDARY', HERE/'witness.json')
    require(boundary_receipt.get('coefficient_lift') == 'canonical_symmetric_monomial_split',
            'Boundary correction lift mismatch')
    require(type(boundary_receipt.get('quartic_pair_count_operations')) is int
            and boundary_receipt['quartic_pair_count_operations'] == 0,
            'Boundary representation-count arithmetic was not retired')
    require(all(sha(ROOT/name) == digest for name, digest in bindings.items()),
            'Inputs changed during replay')
    require(sha(Path(__file__)) == driver_hash, 'Driver changed during replay')
    summary = dict(
        schema='thomson-analytic-local-tail-replay-v3',
        status='PASS_FRESH_REDUCED_TAIL_NUMERICS', cutoff=97,
        analytic_tail_proof_label='prop:tail97', analytic_tail_parameter_lower='97/2',
        source_sha256=bindings, driver_sha256=driver_hash, inputs_unchanged=True,
        runs=runs, tail_scalar_CAP_predicates=0, analytically_replaced_tail_scalar_predicates=51,
        local_tensor_scalar_predicates=0,
        local_tensor_systems=0, maximum_local_system_dimension=0,
        boundary_geometry_root_enclosures=0, boundary_outward_interval_operations=0,
        boundary_coefficient_lift='canonical_symmetric_monomial_split',
        boundary_quartic_pair_count_operations=0,
        boundary_coefficient_field="Q(sqrt2)", external_local_tensor_witness=False, historical_reports_used=False,
        lean_executed=False, seconds=time.monotonic()-started,
        analytic_replacements=[
            'tail from s=97: explicit rational trial, circulation entry, annulus and convex-domain estimates (prop:tail97)',
            'spanning contact cube: all five degree cases',
            'cube algebra', 'weighted and unweighted contact spectra',
            'centered quadratic bound', 'six local annulus contractions',
            'whole-ball mean implication and all51 residual tail scalar inequalities',
            'pair-resolvent tensor identity replacing20 linear systems',
            'all11 local norm bounds by convexity, spectral moments and rectangle interpolation',
            'explicit Fourier boundary slice replaces projector inverse and13 Gram-Schmidt steps',
            'explicit square factors remove all boundary Gram positivity predicates;174 invariant residual coordinates and one floor bound remain',
            'canonical symmetric quartic lift removes105-squared product counts and2380 support/divisor checks',
            'diagonal Fourier rescaling places all geometry and residual coefficients exactly in Q(sqrt2); the algebraic norm identity replaces geometric root enclosures, precise root bounds, and interval propagation'],
        scope='Only the remaining boundary SOS CAP stage is replayed. '
              'The analytic implications and replacement proofs are in the paper.')
    write(output/'SUMMARY.json', summary)
    print(summary['status'], len(runs), 'CAP stages; no residual scalar CAP', flush=True)


if __name__ == '__main__':
    main()
