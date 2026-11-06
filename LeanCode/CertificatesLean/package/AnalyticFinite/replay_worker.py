#!/usr/bin/env python3
"""Rebuild one exact Bernstein square/floor certificate, without prior reports."""
import argparse,importlib.metadata,os,re,sys,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from AnalyticFinite.af_io import require,read,write,sha,bound_path,source_bindings,indexed_entry


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent.parent);ap.add_argument('--cell',required=True);ap.add_argument('--validation-order',type=int,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    require(__debug__ and not sys.flags.optimize,'Run without-O');sys.dont_write_bytecode=True
    root,out=args.root.resolve(),args.output.resolve()
    require(all(not out.is_relative_to(root/f)for f in('Finite','SymmetricFinite','AnalyticFinite')),'Output overlaps mathematical inputs')
    entry,manifest=indexed_entry(root,args.cell);cell=entry['cell'];order=args.validation_order
    require(order in entry['validation_orders'],'Validation order not in immutable plan')
    binding_path,sources=source_bindings(root);worker_key='AnalyticFinite/replay_worker.py'
    require(sha(Path(__file__).resolve())==sources[worker_key],'Wrong worker source')
    asset=manifest['witness'];witness=bound_path(root,asset['path'])
    require(witness.is_relative_to(root/'AnalyticFinite/witnesses')and asset['compression']=='capd1-xz','Wrong witness path/codec')
    require(all(isinstance(asset[k],str)and re.fullmatch(r'[0-9a-f]{64}',asset[k])for k in('compressed_sha256','semantic_sha256')),'Bad witness hash')
    require(sha(witness)==asset['compressed_sha256'],'Witness byte hash mismatch')
    for k in list(os.environ):
        if k.startswith('N8_')or k in('PYTHONPATH','PYTHONOPTIMIZE'):del os.environ[k]
    os.environ.update(PYTHONDONTWRITEBYTECODE='1',OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1',BLIS_NUM_THREADS='1',NUMEXPR_NUM_THREADS='1',VECLIB_MAXIMUM_THREADS='1',N8_DEG_HALF=str(cell['degree']//2),N8_TAYLOR_ORDER=str(order),N8_TARGET_BALANCE=cell['balance'],N8_EXACT_MM_BITS='112',N8_EXACT_SCALAR_BITS='256')
    # Resolve shared numerical modules explicitly; the analytic Taylor module
    # only enlarges the permitted finite order while retaining all formulas.
    sys.path[:0]=[str(root),str(root/'AnalyticFinite/arithmetic'),str(root/'SymmetricFinite'),str(root/'Finite/kernel'),str(root/'Finite')]
    from AnalyticFinite import analytic_contracts as contracts
    from AnalyticFinite import verify_analytic
    import codec,taylor_models
    require(Path(contracts.__file__).resolve()==root/'AnalyticFinite/analytic_contracts.py','Wrong contract module')
    require(Path(taylor_models.__file__).resolve()==root/'AnalyticFinite/arithmetic/taylor_models.py','Wrong Taylor model provider')
    dims=contracts.dimensions(cell);record=codec.load(witness,asset['semantic_sha256'],limits=codec.RECIPE_LIMITS)
    metadata=contracts.witness_audit(record,cell,dims);contracts.validation_order(order,metadata['proposal_order'])
    inputs=dict(sources)
    for p in(root/'AnalyticFinite/INDEX.json',binding_path,bound_path(root,entry['proposal']),witness):inputs[str(p.relative_to(root))]=sha(p)
    out.mkdir(parents=True,exist_ok=False);write(out/'CELL.json',cell)
    write(out/'INPUTS.json',dict(cell=cell,method=contracts.METHOD,validation_order=order,proposal_order=metadata['proposal_order'],files=inputs,worker_sha256=sources[worker_key],python=sys.version,numeric_versions={n:importlib.metadata.version(n)for n in('numpy','mpmath','python-flint')}))
    started=time.monotonic();report=verify_analytic.verify(cell,record,order);write(out/'verified.json',report)
    bounds=contracts.report_audit(out/'verified.json',cell,dims,metadata,order)
    require(all(sha(bound_path(root,n))==h for n,h in inputs.items()),'Input bytes changed')
    require(source_bindings(root)[1]==sources,'Source inventory changed')
    files={p.name:sha(p)for p in out.iterdir()if p.is_file()}
    result=dict(schema='thomson-analytic-finite-cell-v1',status='PASS_FRESH_ANALYTIC_CELL',cell=cell,method=contracts.METHOD,validation_order=order,proposal_order=metadata['proposal_order'],dimensions=dims,metadata=metadata,bounds=bounds,seconds=time.monotonic()-started,inputs_unchanged=True,source_sha256=inputs,worker_sha256=sources[worker_key],files=files,scope='Fresh Bernstein square/floor certificate using the universal analytic coefficient right inverse. Only four correction/floor inequalities are checked; Gram positivity follows analytically from exact square identities. No historical witness, report or numerical coefficient inverse is an input.')
    write(out/'RESULT.json',result);print('PASS_FRESH_ANALYTIC_CELL',cell['id'],bounds,flush=True)

if __name__=='__main__':main()
