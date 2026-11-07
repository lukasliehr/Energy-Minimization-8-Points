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
    manifest_path=root/'SymmetricFinite/source_bindings.json'
    expected=read(manifest_path)['files']
    actual={str(path.relative_to(root)):sha(path)
        for folder in ['Finite','SymmetricFinite']
        for path in sorted((root/folder).rglob('*.py')) if path.is_file()}
    require(actual==expected,'Shared/reduced source inventory mismatch')
    for name in actual:bound_path(root,name)
    return manifest_path,actual


def indexed_entry(root,name):
    entries=read(root/'SymmetricFinite/INDEX.json')['cells']
    require(isinstance(entries,list) and len(entries)==88,'Expected88 exponent cells')
    ids=[e['cell']['id'] for e in entries]
    require(len(set(ids))==88 and all(isinstance(x,str) and re.fullmatch(r'[A-Za-z0-9_-]+',x) for x in ids),'Invalid cells')
    require(name in ids,'Unknown cell')
    entry=entries[ids.index(name)]
    manifest=read(bound_path(root,entry['proposal']))
    require(manifest['cell']==entry['cell'],'Proposal exponent parameters differ')
    return entry,manifest


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=Path(__file__).resolve().parent.parent)
    parser.add_argument('--cell',required=True);parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();require(__debug__ and not sys.flags.optimize,'Run without -O')
    sys.dont_write_bytecode=True
    root,output=args.root.resolve(),args.output.resolve()
    require(not output.is_relative_to(root/'Finite') and not output.is_relative_to(root/'SymmetricFinite'),'Output must be outside sources')
    entry,manifest=indexed_entry(root,args.cell);cell=entry['cell']
    binding_path,sources=source_bindings(root)
    require(sha(Path(__file__).resolve())==sources['SymmetricFinite/replay_worker.py'],'Wrong worker')
    asset=manifest['witness'];witness=bound_path(root,asset['path'])
    require(witness.is_relative_to(root/'SymmetricFinite/witnesses'),'Wrong witness directory')
    require(asset['compression']=='capd1-xz','Wrong witness codec')
    for key in ['compressed_sha256','semantic_sha256']:
        require(isinstance(asset[key],str) and re.fullmatch(r'[0-9a-f]{64}',asset[key]),'Bad witness hash')
    require(sha(witness)==asset['compressed_sha256'],'Witness hash mismatch')
    for key in list(os.environ):
        if key.startswith('N8_') or key in ['PYTHONPATH','PYTHONOPTIMIZE']:del os.environ[key]
    os.environ.update(PYTHONDONTWRITEBYTECODE='1',OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',
        MKL_NUM_THREADS='1',BLIS_NUM_THREADS='1',NUMEXPR_NUM_THREADS='1',VECLIB_MAXIMUM_THREADS='1',
        N8_DEG_HALF=str(cell['degree']//2),N8_TAYLOR_ORDER=str(cell['order']),N8_TARGET_BALANCE=cell['balance'],
        N8_COEFFICIENT_MODE='streamed',N8_ROW_CHUNK='32',N8_ROW_WORKERS='1',N8_EXACT_MM_BITS='112',N8_EXACT_SCALAR_BITS='384')
    sys.path.insert(0,str(root/'Finite'));sys.path.insert(0,str(root/'Finite/kernel'))
    sys.path.insert(0,str(root/'SymmetricFinite'))
    import symmetric_contracts as contracts
    import codec,verify_symmetric
    require(Path(contracts.__file__).resolve()==root/'SymmetricFinite/symmetric_contracts.py','Wrong contracts')
    dimensions=contracts.dimensions(cell);contracts.parameters(cell)
    inputs=dict(sources)
    for path in [root/'SymmetricFinite/INDEX.json',binding_path,bound_path(root,entry['proposal']),witness]:
        inputs[str(path.relative_to(root))]=sha(path)
    output.mkdir(parents=True,exist_ok=False)
    write(output/'CELL.json',cell)
    write(output/'INPUTS.json',dict(cell=cell,method='symmetric_dense_exact',files=inputs,
        worker_sha256=sources['SymmetricFinite/replay_worker.py'],python=sys.version,
        numeric_versions={name:importlib.metadata.version(name) for name in ['numpy','mpmath','python-flint']}))
    started=time.monotonic()
    record=codec.load(witness,asset['semantic_sha256'])
    metadata=contracts.witness_audit(record,cell,dimensions)
    from compact_recipe import expand
    record,expansion=expand(record)
    require(contracts.witness_audit(record,cell,dimensions)==metadata,'Compact metadata drift')
    write(output/'EXPANSION.json',expansion)
    report_path=output/'verified.json' 
    verify_symmetric.verify(cell['center'],cell['halfwidth'],record=record,out=report_path,minorant=cell['profile'])
    bounds=contracts.report_audit(report_path,cell,dimensions,metadata)
    require(all(sha(bound_path(root,name))==digest for name,digest in inputs.items()),'Inputs changed')
    require(source_bindings(root)[1]==sources,'Source inventory changed')
    files={path.name:sha(path) for path in output.iterdir() if path.is_file()}
    result=dict(schema='thomson-symmetric-finite-cell-v1',status='PASS_FRESH_SYMMETRIC_CELL',
        cell=cell,method='symmetric_dense_exact',dimensions=dimensions,metadata=metadata,bounds=bounds,
        seconds=time.monotonic()-started,inputs_unchanged=True,source_sha256=inputs,
        worker_sha256=sources['SymmetricFinite/replay_worker.py'],files=files,
        scope='Complete independent exact-arithmetic finite CAP in smaller analytic symmetry blocks. '
              'No original witness or accepted report is a verification input.')
    write(output/'RESULT.json',result)
    print('PASS_FRESH_SYMMETRIC_CELL',cell['id'],bounds,flush=True)


if __name__=='__main__':main()
