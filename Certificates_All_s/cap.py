#!/usr/bin/env python3
"""Replay the complete eight-point proof, or inspect the published replay."""
import argparse
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def read(path):
    return json.loads(path.read_text())


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def integrity():
    for folder in (HERE / 'finite', HERE / 'tail'):
        require(not any(p.suffix in ('.pyc', '.pyo') for p in folder.rglob('*')),
                'Remove Python bytecode caches from finite/ and tail/ before replay')
    entries = read(HERE / 'MANIFEST.json')['files']
    for name, info in entries.items():
        path = (HERE / name).resolve()
        require(path.is_relative_to(HERE), 'Manifest path leaves package')
        require(path.is_file() and path.stat().st_size == info['bytes']
                and digest(path) == info['sha256'], 'Integrity failure: ' + name)
    print('PASS_FILE_INTEGRITY', len(entries), 'files', flush=True)


def replay(output, jobs):
    require(__debug__ and sys.flags.optimize == 0, 'Run Python without -O')
    integrity()
    sys.path.insert(0, str(HERE / 'finite'))
    from replay import clean_environment
    env = clean_environment()
    run = output.expanduser().resolve()
    run.mkdir(parents=True, exist_ok=False)
    started = time.monotonic()
    print('Fresh complete replay:', run, flush=True)
    subprocess.run([sys.executable, '-B', '-u', str(HERE / 'finite/replay.py'),
                    '--output', str(run / 'finite'), '--jobs', str(jobs)],
                   env=env, check=True)
    finite = read(run / 'finite/SUMMARY.json')
    require(finite['status'] == 'PASS_COMPLETE_FINITE_REPLAY'
            and finite['inputs_unchanged'] is True and len(finite['results']) == 111
            and all(r['status'] == 'PASS' for r in finite['results'])
            and finite['closed_nonnegative_union'] == [['0', '124']],
            'Incomplete finite proof')
    subprocess.run([sys.executable, '-B', '-u', str(HERE / 'tail/replay.py'),
                    '--output', str(run / 'tail')], env=env, check=True)
    tail = read(run / 'tail/REPLAY.json')
    require(tail['status'] == 'PASS_STANDALONE_REPLAY' and len(tail['runs']) == 5
            and all(r['exit_code'] == 0 for r in tail['runs']), 'Incomplete exact tail')
    for name, h in tail['source_sha256'].items():
        require(digest(HERE / 'tail' / name) == digest(run / 'tail' / name) == h,
                'Tail input binding mismatch')
    for name, h in tail['report_sha256'].items():
        require(digest(run / 'tail' / name) == h, 'Tail report binding mismatch')
    scalar = read(run / 'tail/verify_tail124.json')
    require(scalar['status'] == 'PASS_STANDALONE_GLOBAL_TAIL_124'
            and scalar['global_s_cutoff'] == 124 and scalar['global_p_cutoff'] == '62',
            'Wrong tail theorem')
    require(scalar['number_of_checks'] == len(scalar['checks']) == 403
            and all(v is True for v in scalar['checks'].values()), 'Incomplete tail checks')
    require(len(scalar['bootstrap']) == 4
            and all(len(b['comparisons']) == 79 for b in scalar['bootstrap']),
            'Incomplete annulus comparisons')
    for name, h in scalar['dependency_sha256'].items():
        path = Path(name)
        require(not path.is_absolute() and (run / 'tail' / path).resolve().is_relative_to(run / 'tail'),
                'Nonportable tail dependency')
        require(digest(run / 'tail' / path) == h, 'Tail dependency changed')
    require(Fraction(finite['closed_nonnegative_union'][0][1])
            >= Fraction(scalar['global_s_cutoff']), 'Gap between finite proof and tail')
    integrity()
    summary = {'status': 'PASS_COMPLETE_GLOBAL_REPLAY', 'point_count': 8, 'sphere': 'S^2',
        'all_real_s_nonnegative': True, 'logarithmic_at_zero': True,
        'finite_cell_count': 111, 'finite_closed_union': [['0', '124']], 'tail_lower': '124',
        'arithmetic': 'exact-integer-enclosures', 'lean_verified': False,
        'finite_summary_sha256': digest(run / 'finite/SUMMARY.json'),
        'tail_replay_sha256': digest(run / 'tail/REPLAY.json'),
        'package_manifest_sha256': digest(HERE / 'MANIFEST.json'),
        'elapsed_seconds': time.monotonic() - started,
        'scope': 'Fresh computational obligations for global optimality of the square antiprism for all nonnegative exponents.'}
    (run / 'SUMMARY.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    actions = parser.add_subparsers(dest='action', required=True)
    actions.add_parser('status', help='Read the published replay summary')
    actions.add_parser('integrity', help='Check all published file hashes')
    p = actions.add_parser('replay', help='Recompute every finite cell and the analytic tail')
    p.add_argument('--jobs', type=int, choices=range(1, 65), default=4)
    p.add_argument('--output', type=Path, required=True, help='New directory for fresh reports')
    args = parser.parse_args()
    if args.action == 'status':
        print(json.dumps(read(HERE / 'verification/SUMMARY.json'), indent=2))
    elif args.action == 'integrity':
        integrity()
    else:
        replay(args.output, args.jobs)


if __name__ == '__main__':
    main()
