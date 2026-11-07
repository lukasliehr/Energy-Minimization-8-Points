#!/usr/bin/env python3
"""Recompute one complete finite CAP from the current resolved index.

Moment and contact bases use the proved analytic formulas. Trace/factor
engines, coefficient correction and required positivity gates are retained.
The analytic odd-moment equality theorem removes forbidden-triangle gates.
"""
import argparse
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import re
import sys
import time


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(path):
    def pairs(items):
        value = {}
        for key, item in items:
            require(key not in value, 'Duplicate JSON key: ' + key)
            value[key] = item
        return value

    def invalid(value):
        raise ValueError('Nonfinite JSON constant: ' + value)

    return json.loads(Path(path).read_text(), object_pairs_hook=pairs,
                      parse_constant=invalid)


def write(path, value):
    Path(path).write_text(json.dumps(value, indent=2, allow_nan=False) + '\n')


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            digest.update(block)
    return digest.hexdigest()


def bound_path(root, relative):
    require(isinstance(relative, str), 'Path must be a string')
    path = Path(relative)
    require(not path.is_absolute() and '..' not in path.parts, 'Unsafe path')
    candidate = root / path
    require(not candidate.is_symlink(), 'Symlink is not a certificate input')
    resolved = candidate.resolve()
    require(resolved.is_relative_to(root), 'Path escapes certificate directory')
    return resolved


def source_bindings(root):
    """Bind all live finite Python source, including the portable runners."""
    manifest_path = root / 'source_bindings.json'
    manifest = read(manifest_path)
    bindings = manifest.get('files', manifest)
    require(isinstance(bindings, dict), 'Source bindings must be a mapping')
    finite = root / 'Finite'
    actual = {str(path.relative_to(root)): sha(path)
              for path in sorted(finite.rglob('*.py')) if path.is_file()}
    require(bool(actual), 'Empty finite source inventory')
    expected = {name: digest for name, digest in bindings.items()
                if isinstance(name, str) and name.startswith('Finite/')
                and name.endswith('.py')}
    require(actual == expected, 'Finite source inventory/hash mismatch')
    for name in actual:
        bound_path(root, name)
    required = ['Finite/contracts.py', 'Finite/trace_core.py',
                'Finite/factored_engine.py', 'Finite/low_inverse.py',
                'Finite/replay_worker.py', 'Finite/replay.py']
    require(all(name in actual for name in required), 'Missing active source')
    return manifest_path, actual


def indexed_entry(root, name):
    entries = read(root / 'INDEX.json')['finite_cells']
    require(isinstance(entries, list) and len(entries) == 88,
            'Expected the complete current 88-cell index')
    ids = [entry['cell']['id'] for entry in entries]
    require(len(set(ids)) == 88 and all(isinstance(item, str) and
            re.fullmatch(r'[A-Za-z0-9_-]+', item) for item in ids),
            'Invalid or duplicate cell identifiers')
    require(name in ids, 'Unknown requested cell')
    return entries[ids.index(name)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path,
                        default=Path(__file__).resolve().parent.parent,
                        help='Current Certificates directory')
    parser.add_argument('--cell', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    require(__debug__ and not sys.flags.optimize, 'Run Python without -O')
    sys.dont_write_bytecode = True
    root, output = args.root.resolve(), args.output.resolve()
    require(not output.is_relative_to(root / 'Finite'),
            'Put replay output outside the mathematical source directory')
    entry = indexed_entry(root, args.cell)
    cell, method = entry['cell'], entry['method']
    require(method in ['original_dense_checker', 'original_dense_new_interval',
                       'exact_trace_new_interval', 'direct_factored_short_inverse'],
            'Unsupported finite method')
    bindings_path, sources = source_bindings(root)
    index_path = root / 'INDEX.json'
    witness = bound_path(root, entry['witness_path'])
    require(witness.is_relative_to(root / 'Finite' / 'witnesses'),
            'Witness is outside Finite/witnesses')
    asset = cell['witness']
    require(asset['compression'] == 'capd1-xz', 'Unsupported witness encoding')
    for key in ['compressed_sha256', 'semantic_sha256']:
        require(isinstance(asset[key], str) and
                re.fullmatch(r'[0-9a-f]{64}', asset[key]), 'Malformed witness hash')
    require(sha(witness) == asset['compressed_sha256'], 'Witness hash mismatch')
    if 'path' in asset:
        require(bound_path(root / 'Finite', asset['path']) == witness,
                'The cell and entry name different witnesses')

    # These environment values must be set before the first kernel import.
    for key in list(os.environ):
        if key.startswith('N8_') or key in ['PYTHONPATH', 'PYTHONOPTIMIZE']:
            del os.environ[key]
    os.environ.update(PYTHONDONTWRITEBYTECODE='1', OPENBLAS_NUM_THREADS='1',
        OMP_NUM_THREADS='1', MKL_NUM_THREADS='1', BLIS_NUM_THREADS='1',
        NUMEXPR_NUM_THREADS='1', VECLIB_MAXIMUM_THREADS='1',
        N8_DEG_HALF=str(cell['degree'] // 2), N8_TAYLOR_ORDER=str(cell['order']),
        N8_TARGET_BALANCE=cell['balance'], N8_COEFFICIENT_MODE='streamed',
        N8_ROW_CHUNK='32', N8_ROW_WORKERS='1', N8_EXACT_MM_BITS='112',
        N8_EXACT_SCALAR_BITS='384')
    finite = root / 'Finite'
    sys.path.insert(0, str(finite))
    import contracts as replay
    require(Path(replay.__file__).resolve() == finite / 'contracts.py',
            'Unexpected replay audit module')
    dimensions = replay.dimensions(cell)
    replay.parameters(cell)
    inputs = dict(sources)
    for path in [index_path, bindings_path, witness]:
        inputs[str(path.relative_to(root))] = sha(path)
    worker_hash = sha(Path(__file__).resolve())
    require(worker_hash == sources['Finite/replay_worker.py'],
            'Executing a different worker than the bound current worker')
    output.mkdir(parents=True, exist_ok=False)
    write(output / 'CELL.json', cell)
    write(output / 'INPUTS.json', dict(cell=cell, method=method, files=inputs,
        worker_sha256=worker_hash, python=sys.version, row_workers=1,
        native_threads=1, numeric_versions={name: importlib.metadata.version(name)
            for name in ['numpy', 'mpmath', 'python-flint']}))

    sys.path.insert(0, str(finite / 'kernel'))
    import numpy as np
    import codec
    import recipe
    import structure
    import build_models
    import verify_interval
    raw = codec.load(witness, asset['semantic_sha256'], limits=codec.RECIPE_LIMITS)
    originals = (build_models.build, verify_interval.correction_models_streamed,
                 verify_interval.approximate_solve_model)
    engine = None
    started = time.monotonic()
    if method == 'direct_factored_short_inverse':
        from factored_engine import FactoredEngine
        from low_inverse import solve
        engine = FactoredEngine(output, raw, structure.raw_data(), len(structure.EXPS))
        record = dict(raw, right_inverse=engine.Cf, left_preconditioner=engine.left)
        metadata = replay.witness_audit(dict(record, right_inverse=engine.Cf.lo),
                                        cell, dimensions)
        require(metadata == replay.witness_audit(
            dict(record, right_inverse=engine.Cf.hi), cell, dimensions),
            'Both exact-factor endpoints must pass the structural audit')
        verify_interval.approximate_solve_model = lambda T, r: solve(T, r, output)
        expansion = dict(exact_C_definition='Cf=Aref_exact.T K; L=K.T; no additive UV',
                         source_sha256=sha(witness), semantic_sha256=asset['semantic_sha256'])
    else:
        record, expansion = recipe.expand_record(raw, structure)
        metadata = replay.witness_audit(record, cell, dimensions)
        saved = dict(right_inverse=np.asarray(record['right_inverse'], dtype=np.float64))
        if record.get('left_preconditioner') is not None:
            saved['left_preconditioner'] = np.asarray(record['left_preconditioner'], dtype=np.float64)
        np.savez(output / 'accepted_dyadic_proposal.npz', **saved)
        expansion.update(source_sha256=sha(witness), semantic_sha256=asset['semantic_sha256'],
            saved_proposal='accepted_dyadic_proposal.npz',
            saved_proposal_sha256=sha(output / 'accepted_dyadic_proposal.npz'))
        if method == 'exact_trace_new_interval':
            from trace_core import TraceEngine
            engine = TraceEngine(output, record['basis_records'])
    expansion['metadata'] = metadata
    write(output / 'EXPANSION.json', expansion)
    if engine is not None:
        build_models.build = engine.build_wrapper(originals[0])
        verify_interval.correction_models_streamed = engine.correction_models
    report_path = output / 'verified.json'
    try:
        verify_interval.verify(cell['center'], cell['halfwidth'], record=record,
                               out=report_path, minorant=cell['profile'])
    finally:
        (build_models.build, verify_interval.correction_models_streamed,
         verify_interval.approximate_solve_model) = originals
    bounds = replay.report_audit(report_path, cell, dimensions, metadata)
    if method == 'direct_factored_short_inverse':
        short = read(output / 'SHORT_INVERSE.json')
        require(short['chosen_degree'] == entry.get('inverse_degree', 1),
                'Inverse degree differs from the indexed short-inverse method')
        require(short['solution_polynomial_order'] == cell['order'],
                'Short-inverse solution order mismatch')
    require(read(output / 'CELL.json') == cell, 'Cell changed during computation')
    require(all(sha(bound_path(root, name)) == digest for name, digest in inputs.items()),
            'Source/input changed during computation')
    require(sha(Path(__file__).resolve()) == worker_hash, 'Worker changed during computation')
    require(source_bindings(root)[1] == sources, 'Finite source inventory changed')
    files = {path.name: sha(path) for path in output.iterdir() if path.is_file()}
    result = dict(schema='thomson-active-finite-cell-v1', status='PASS_FRESH_COMPLETE_CELL',
        cell=cell, method=method, bounds=bounds, dimensions=dimensions, metadata=metadata,
        seconds=time.monotonic()-started, inputs_unchanged=True, source_sha256=inputs,
        worker_sha256=worker_hash, files=files,
        scope='Complete ordinary exact-arithmetic CAP on the specified closed cell. '
              'No accepted report or Lean theorem is consumed as a proof input.')
    write(output / 'RESULT.json', result)
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()
