#!/usr/bin/env python3
"""Recompute one uniform Psi_q certificate. It is not a complete-range replay."""
import argparse, hashlib, json, os, subprocess, sys
from fractions import Fraction
from pathlib import Path
HERE = Path(__file__).resolve().parent

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def prepare_backend(name):
    if name == 'gmp':
        folder = HERE / 'portable_backend'
        binary = folder / 'gmp_matrix.so'
        if not binary.exists():
            subprocess.run(['g++','-O3','-std=c++17','-shared','-fPIC',
                str(folder/'gmp_matrix.cpp'),'-lgmpxx','-lgmp','-o',str(binary)],check=True)
        sys.path.insert(0, str(folder))
    import flint
    return flint

def run(cell_path, output, backend):
    require(__debug__ and sys.flags.optimize == 0, 'Run Python without -O')
    cell_path = cell_path.resolve()
    require(cell_path.is_relative_to(HERE), 'Cell must be inside this package')
    cell = json.loads(cell_path.read_text())
    c, h = Fraction(cell['center']), Fraction(cell['halfwidth'])
    require(0 <= c-h <= c+h <= 1 and h > 0, 'Cell must lie in q in [0,1]')
    require(cell['degree']==12 and cell['profile']=='original' and cell['balance']=='unit',
            'Unexpected certificate structure')
    require(type(cell['order']) is int and 4<=cell['order']<=20, 'Invalid Taylor order')
    for key in list(os.environ):
        if key.startswith('N8_'):
            del os.environ[key]
    os.environ.update(N8_DEG_HALF='6',N8_TAYLOR_ORDER=str(cell['order']),
        N8_TARGET_BALANCE='unit',N8_ROW_WORKERS='1',N8_COEFFICIENT_MODE='streamed',
        N8_EXACT_SCALAR_BITS='384',N8_EXACT_MM_BITS='112',N8_ROW_CHUNK='12')
    sys.path.insert(0, str(HERE/'kernel'))
    flint = prepare_backend(backend)
    import codec, structure, recipe
    from verify_interval import verify
    asset = cell['witness']
    path = (HERE/asset['path']).resolve()
    require(path.is_relative_to((HERE/'certificates').resolve()), 'Invalid witness path')
    require(digest(path)==asset['compressed_sha256'], 'Witness byte hash mismatch')
    files = [*sorted((HERE/'kernel').glob('*.py')), Path(__file__).resolve(), cell_path, path]
    if backend == 'gmp':
        files += [HERE/'portable_backend'/name for name in ('flint.py','gmp_matrix.cpp','gmp_matrix.so')]
    inputs = {str(f.relative_to(HERE)):digest(f) for f in files}
    output.mkdir(parents=True, exist_ok=False)
    def write(name, value):
        (output/name).write_text(json.dumps(value,indent=2,allow_nan=False)+'\n')
    write('INPUTS.json',inputs)
    write('CELL.json',cell)
    record = codec.load(path,asset['semantic_sha256'],limits=codec.RECIPE_LIMITS)
    record, expansion = recipe.expand_record(record,structure)
    write('EXPANSION.json',expansion)
    report = verify(cell['center'],cell['halfwidth'],record=record,
                    out=output/'verified.json',minorant=cell['profile'])
    require(report.get('passed') is True, 'Verifier did not pass')
    require(all(digest(HERE/name)==h for name,h in inputs.items()), 'Proof input changed during computation')
    import numpy,mpmath
    write('ENVIRONMENT.json',{'python':sys.version,'numpy':numpy.__version__,
        'mpmath':mpmath.__version__,'integer_backend':backend,
        'integer_backend_module':str(Path(flint.__file__).resolve()),
        'original_s_interval':[str(2*(c-h)-2),str(2*(c+h)-2)],
        'inputs_unchanged':True,'backend_version':getattr(flint,'__version__','portable GMP exact integer adapter')})
    print('PASS_SINGLE_PSI_CELL',str(c-h),str(c+h),flush=True)

if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('cell',type=Path)
    parser.add_argument('output',type=Path)
    parser.add_argument('--backend',choices=['flint','gmp'],default='flint')
    args=parser.parse_args()
    run(args.cell,args.output,args.backend)
