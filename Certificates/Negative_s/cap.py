#!/usr/bin/env python3
"""Complete replay of the compact negative-exponent extension.
Old reports are never inputs to the replay command.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent

def require(test: bool, message: str) -> None:
    if not test:
        raise RuntimeError(message)

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def write_json(path: Path, data: object) -> None:
    path.write_text(json.dumps(data, indent=2, allow_nan=False) + '\n')

def integrity() -> dict[str, str]:
    require(__debug__ and sys.flags.optimize == 0, 'Run ordinary Python without -O.')
    manifest = json.loads((HERE / 'MANIFEST.json').read_text())
    expected = manifest['files']
    require(isinstance(expected, dict) and expected, 'Empty integrity manifest.')
    for name, expected_sha in expected.items():
        path = (HERE / name).resolve()
        require(path.is_relative_to(HERE), 'Manifest path escapes package.')
        require(path.is_file() and sha(path) == expected_sha, f'Input mismatch: {name}')
    print(f'PASS_INPUT_INTEGRITY {len(expected)} files', flush=True)
    return expected

def registry() -> list[dict]:
    reg = json.loads((HERE / 'cells.json').read_text())
    require(reg['parameter'] == 'q=(s+2)/2', 'Unexpected parameter.')
    cells = [json.loads((HERE / name).read_text()) for name in reg['cells']]
    require(len({c['id'] for c in cells}) == len(cells), 'Repeated cell ID.')
    require(len(set(reg['cells'])) == len(cells), 'Repeated cell input.')
    for c, name in zip(cells, reg['cells']):
        c['_file'] = name
    verify_union(cells)
    return cells

def verify_union(cells: list[dict]) -> list[str]:
    intervals = sorted((Fraction(c['center']) - Fraction(c['halfwidth']),
                        Fraction(c['center']) + Fraction(c['halfwidth'])) for c in cells)
    require(bool(intervals) and intervals[0][0] == 0, 'Coverage must start at q=0.')
    right = Fraction(0)
    for lo, hi in intervals:
        require(0 <= lo < hi <= 1 and lo <= right, 'Gap or invalid interval.')
        right = max(right, hi)
    require(right == 1, 'Coverage must reach q=1.')
    return ['0', '1']

def collect_reports(cells: list[dict], output: Path) -> dict:
    summaries = []
    for cell in cells:
        folder = output / cell['id']
        report = json.loads((folder / 'verified.json').read_text())
        environment = json.loads((folder / 'ENVIRONMENT.json').read_text())
        inputs = json.loads((folder / 'INPUTS.json').read_text())
        recorded_cell = json.loads((folder / 'CELL.json').read_text())
        require(recorded_cell == {k:v for k,v in cell.items() if k != '_file'},
                f'Cell binding mismatch: {cell["id"]}')
        require(report.get('passed') is True and environment.get('inputs_unchanged') is True,
                f'Failed or incomplete cell: {cell["id"]}')
        for name, old_sha in inputs.items():
            # The retained machine-specific GMP binary is intentionally an output,
            # not a portable publication input. For a fresh replay it is present.
            path = (HERE / name).resolve()
            require(path.is_relative_to(HERE) and path.is_file() and sha(path) == old_sha,
                    f'Cell source or witness changed: {name}')
        require(report['center'] == cell['center'] and report['halfwidth'] == cell['halfwidth']
                and report['order'] == cell['order'] and report['degree'] == 12,
                'Report interval or structure mismatch.')
        require(report['target_multiplier'] == '1'
                and report['hermite_multiplicities'] == {'A':2,'B':2,'C':2,'D':2,'minus_one':5},
                'Unexpected minorant or multiplier.')
        errors = report['PSD_uniform_errors']
        require(len(errors) == 9 and all(0 <= x < 1 for x in errors), 'PSD check missing.')
        require(0 <= report['right_inverse_uniform_residual'] < 1
                and 0 <= report['F0_basis_change_inverse_error'] < 1, 'Inverse check missing.')
        exclusions = report['forbidden_triples']
        require([r['type'] for r in exclusions] == [[0,0,0],[0,0,2],[0,0,3]]
                and all(r['absolute_lower_bound'] > 0 for r in exclusions),
                'Equality exclusions missing.')
        c, h = Fraction(cell['center']), Fraction(cell['halfwidth'])
        summaries.append({'id':cell['id'], 'q_interval':[str(c-h),str(c+h)],
                          's_interval':[str(2*(c-h)-2),str(2*(c+h)-2)],
                          'max_PSD_uniform_error':max(errors),
                          'inverse_residual':report['right_inverse_uniform_residual'],
                          'solution_error':report['solution_error_upper'],
                          'minimum_forbidden_feature_bound':min(r['absolute_lower_bound'] for r in exclusions),
                          'elapsed_seconds':report['elapsed_seconds'],
                          'integer_backend':environment['integer_backend']})
    return {'auxiliary_parameter':'q=(s+2)/2', 'exact_auxiliary_union':verify_union(cells),
            'original_Riesz_range':'-2 < s <= 0', 'degree':12,
            'Taylor_orders':sorted({c['order'] for c in cells}), 'cells':summaries,
            'conclusion':'Unique optimized square antiprism for Psi_q on [0,1]; '
                         'centroid identity implies the normalized Riesz theorem for -2<s<=0. '
                         'The original Riesz energy at s=-2 is not uniquely minimized.'}

def replay(jobs: int, output: Path, backend: str) -> None:
    inputs = integrity()
    cells = registry()
    require(1 <= jobs <= 64, 'Jobs must lie between 1 and 64.')
    output = output.resolve()
    require(not output.exists(), 'Choose a new output directory; old reports cannot be reused.')
    output.mkdir(parents=True)
    # Compile the optional integer backend once before launching parallel workers.
    if backend == 'gmp':
        from verify_cell import prepare_backend
        prepare_backend('gmp')
    env = dict(os.environ)
    for name in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS',
                 'NUMEXPR_NUM_THREADS','BLIS_NUM_THREADS','VECLIB_MAXIMUM_THREADS'):
        env[name] = '1'
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    start = time.time()
    def one(cell: dict) -> tuple[str,int]:
        log = output / (cell['id'] + '.log')
        with log.open('wb') as stream:
            proc = subprocess.run([sys.executable, '-B', '-u', str(HERE/'verify_cell.py'),
                    str(HERE/cell['_file']),str(output/cell['id']),'--backend',backend],
                    stdout=stream,stderr=subprocess.STDOUT,env=env,check=False)
        return cell['id'], proc.returncode
    with ThreadPoolExecutor(max_workers=min(jobs,len(cells))) as pool:
        results = [pool.submit(one, c) for c in cells]
        failures = []
        for future in as_completed(results):
            cid, code = future.result()
            print(('PASS' if code == 0 else 'FAIL') + ' ' + cid, flush=True)
            if code:
                failures.append((cid,code))
    require(not failures, f'Cell failures: {failures}; see logs. No complete theorem certified.')
    summary = collect_reports(cells, output)
    require(all((HERE/name).is_file() and sha(HERE/name)==value for name,value in inputs.items()),
            'Package input changed during replay.')
    summary.update(status='PASS_COMPLETE_NEGATIVE_RIESZ_REPLAY',
                   fresh_subprocesses=True, source_inputs_unchanged=True,
                   elapsed_wall_seconds=time.time()-start)
    write_json(output/'SUMMARY.json',summary)
    print(summary['status'], flush=True)

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command',required=True)
    sub.add_parser('integrity',help='Check bound bytes, not mathematical inequalities.')
    p = sub.add_parser('replay',help='Recompute every cell, then verify exact interval coverage.')
    p.add_argument('--jobs',type=int,default=4)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--backend',choices=['flint','gmp'],default='flint')
    args = parser.parse_args()
    if args.command == 'integrity':
        integrity()
    else:
        replay(args.jobs,args.output,args.backend)

if __name__ == '__main__':
    main()
