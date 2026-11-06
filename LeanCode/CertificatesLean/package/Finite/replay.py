#!/usr/bin/env python3
"""Replay all current 88 finite certificates, or an explicit selected subset."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
import os
from pathlib import Path
import re
import subprocess
import sys
import time

from replay_worker import bound_path, read, require, sha, source_bindings, write


def union(cells):
    merged = []
    intervals = []
    for cell in cells:
        center, width = Fraction(cell['center']), Fraction(cell['halfwidth'])
        require(width > 0 and center + width >= 0, 'Invalid closed cell')
        intervals.append((max(Fraction(0), center-width), center+width))
    for left, right in sorted(intervals):
        if merged and left <= merged[-1][1]:
            merged[-1][1] = max(right, merged[-1][1])
        else:
            merged.append([left, right])
    return [[str(value) for value in pair] for pair in merged]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path,
                        default=Path(__file__).resolve().parent.parent,
                        help='Current Certificates directory')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('--cell', action='append', default=[])
    args = parser.parse_args()
    require(__debug__ and not sys.flags.optimize, 'Run Python without -O')
    require(1 <= args.jobs <= 128, 'Job count must be between1 and128')
    root, output = args.root.resolve(), args.output.resolve()
    require(not output.is_relative_to(root / 'Finite'),
            'Put replay output outside the mathematical source directory')
    bindings_path, sources = source_bindings(root)
    worker = root / 'Finite' / 'replay_worker.py'
    dispatcher = Path(__file__).resolve()
    require(sha(dispatcher) == sources['Finite/replay.py'],
            'Executing a different dispatcher than the bound current dispatcher')
    index_path = root / 'INDEX.json'
    entries = read(index_path)['finite_cells']
    require(isinstance(entries, list) and len(entries) == 88, 'Expected88 active cells')
    ids = [entry['cell']['id'] for entry in entries]
    require(len(set(ids)) == 88 and all(isinstance(name, str) and
            re.fullmatch(r'[A-Za-z0-9_-]+', name) for name in ids),
            'Invalid or duplicate active cells')
    require(union([entry['cell'] for entry in entries]) == [['0', '98']],
            'The current finite plan must cover exactly[0,98]')
    if args.cell:
        require(len(set(args.cell)) == len(args.cell) and set(args.cell) <= set(ids),
                'Invalid requested cell subset')
        entries = [entry for entry in entries if entry['cell']['id'] in args.cell]
    expected_union = union([entry['cell'] for entry in entries])
    output.mkdir(parents=True, exist_ok=False)
    (output / 'logs').mkdir()
    plan = dict(schema='thomson-active-finite-replay-plan-v1', cells=entries,
        expected_closed_nonnegative_union=expected_union, jobs=args.jobs,
        complete_88_cell_plan=not bool(args.cell), worker_sha256=sha(worker),
        dispatcher_sha256=sha(dispatcher), index_sha256=sha(index_path),
        source_bindings_sha256=sha(bindings_path), finite_sources=sources,
        python=sys.version)
    write(output / 'PLAN.json', plan)
    environment = dict(os.environ)
    for key in list(environment):
        if key.startswith('N8_') or key in ['PYTHONOPTIMIZE', 'PYTHONPATH']:
            environment.pop(key, None)
    environment.update(PYTHONDONTWRITEBYTECODE='1', OPENBLAS_NUM_THREADS='1',
        OMP_NUM_THREADS='1', MKL_NUM_THREADS='1', BLIS_NUM_THREADS='1',
        NUMEXPR_NUM_THREADS='1', VECLIB_MAXIMUM_THREADS='1')
    started = time.monotonic()

    def run(entry):
        name = entry['cell']['id']
        folder = output / name
        command = [sys.executable, '-B', '-u', str(worker), '--root', str(root),
                   '--cell', name, '--output', str(folder)]
        try:
            with (output / 'logs' / (name + '.log')).open('w') as log:
                result_code = subprocess.call(command, env=environment,
                    stdout=log, stderr=subprocess.STDOUT)
            require(result_code == 0, 'Worker exit code ' + str(result_code))
            result = read(folder / 'RESULT.json')
            require(result['status'] == 'PASS_FRESH_COMPLETE_CELL' and
                    result['cell'] == entry['cell'] and result['method'] == entry['method'],
                    'Worker result cell/method/status mismatch')
            for filename, digest in result['files'].items():
                require(sha(bound_path(folder, filename)) == digest,
                        'Worker output hash changed: ' + filename)
            require(result['worker_sha256'] == plan['worker_sha256'] and
                    result['inputs_unchanged'] is True, 'Worker provenance mismatch')
            require(result['source_sha256']['INDEX.json'] == plan['index_sha256'] and
                    result['source_sha256']['source_bindings.json'] == plan['source_bindings_sha256'],
                    'Worker did not use the dispatcher index/source binding')
            require(all(result['source_sha256'].get(path) == digest
                        for path, digest in sources.items()), 'Worker source mismatch')
            print('PASS', name, result['bounds'], flush=True)
            return dict(id=name, status='PASS', cell=entry['cell'], method=entry['method'],
                result=str((folder/'RESULT.json').relative_to(output)),
                result_sha256=sha(folder/'RESULT.json'), bounds=result['bounds'])
        except Exception as error:
            print('FAIL', name, repr(error), flush=True)
            return dict(id=name, status='FAIL', cell=entry['cell'], method=entry['method'],
                        error=repr(error))

    scheduled = sorted(entries,
        key=lambda entry: (entry['cell']['degree'], entry['cell']['order']), reverse=True)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(run, scheduled))
    results.sort(key=lambda result: ids.index(result['id']))
    actual_union = union([result['cell'] for result in results if result['status'] == 'PASS'])
    unchanged = (sha(worker) == plan['worker_sha256'] and
        sha(dispatcher) == plan['dispatcher_sha256'] and
        sha(index_path) == plan['index_sha256'] and
        sha(bindings_path) == plan['source_bindings_sha256'])
    try:
        unchanged = unchanged and source_bindings(root)[1] == sources
    except Exception:
        unchanged = False
    passed = (all(result['status'] == 'PASS' for result in results) and unchanged and
              actual_union == expected_union)
    status = ('PASS_COMPLETE_CURRENT_FINITE_REPLAY' if not args.cell else
              'PASS_SELECTED_COMPLETE_CELLS') if passed else 'INCOMPLETE'
    summary = dict(schema='thomson-active-finite-replay-summary-v1', status=status,
        count=len(entries), closed_nonnegative_union=actual_union, results=results,
        complete_88_cell_plan=not bool(args.cell), inputs_unchanged=unchanged,
        plan_sha256=sha(output/'PLAN.json'), seconds=time.monotonic()-started,
        scope='Fresh complete numerical obligations for every listed closed cell. '
              'Analytic soundness is supplied by the paper. No Lean execution.')
    write(output / 'SUMMARY.json', summary)
    print(status, actual_union, flush=True)
    if not passed:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
