#!/usr/bin/env python3
"""Source-bound adaptive Bernstein-factor replay of all30 cells or a subset."""
import argparse,os,re,subprocess,sys,time
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from AnalyticFinite.af_io import require,read,write,sha,bound_path,source_bindings,indexed_entry


def union(cells):
    intervals=[]
    for cell in cells:
        c,h=Fraction(cell['center']),Fraction(cell['halfwidth']);require(h>0 and c+h>=0,'Invalid cell')
        intervals.append((max(Fraction(0),c-h),c+h))
    merged=[]
    for lo,hi in sorted(intervals):
        if merged and lo<=merged[-1][1]:merged[-1][1]=max(hi,merged[-1][1])
        else:merged.append([lo,hi])
    return[[str(x)for x in p]for p in merged]


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent.parent);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--jobs',type=int,default=6);ap.add_argument('--cell',action='append',default=[]);args=ap.parse_args()
    require(__debug__ and not sys.flags.optimize,'Run without-O');require(1<=args.jobs<=32,'Invalid worker count')
    root,out=args.root.resolve(),args.output.resolve();require(all(not out.is_relative_to(root/f)for f in('Finite','SymmetricFinite','AnalyticFinite')),'Output overlaps mathematical inputs')
    bind,sources=source_bindings(root);worker=root/'AnalyticFinite/replay_worker.py';dispatcher=Path(__file__).resolve();index=root/'AnalyticFinite/INDEX.json'
    require(sha(dispatcher)==sources['AnalyticFinite/replay.py'],'Wrong dispatcher')
    all_entries=read(index)['cells'];require(len(all_entries)==30,'Expected30 indexed cells')
    ids=[e['cell']['id']for e in all_entries];require(len(set(ids))==30,'Duplicate cell IDs')
    require(union([e['cell']for e in all_entries])==[['0','97']],'Incomplete finite range')
    require(not args.cell or len(set(args.cell))==len(args.cell)and set(args.cell)<=set(ids),'Invalid selected cell subset')
    entries=[e for e in all_entries if not args.cell or e['cell']['id']in args.cell]
    for entry in entries:indexed_entry(root,entry['cell']['id'])
    expected=union([e['cell']for e in entries]);out.mkdir(parents=True,exist_ok=False);(out/'logs').mkdir()
    plan=dict(schema='thomson-analytic-finite-replay-plan-v1',cells=entries,expected_closed_nonnegative_union=expected,jobs=args.jobs,complete_30_cell_plan=not bool(args.cell),validation_policy='first-success-in-immutable-validation-orders',worker_sha256=sha(worker),dispatcher_sha256=sha(dispatcher),index_sha256=sha(index),source_bindings_sha256=sha(bind),finite_sources=sources,python=sys.version)
    write(out/'PLAN.json',plan);env=dict(os.environ)
    for k in list(env):
        if k.startswith('N8_')or k in('PYTHONPATH','PYTHONOPTIMIZE'):env.pop(k,None)
    env.update(PYTHONDONTWRITEBYTECODE='1',OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1',BLIS_NUM_THREADS='1',NUMEXPR_NUM_THREADS='1',VECLIB_MAXIMUM_THREADS='1');started=time.monotonic()
    def run(entry):
        name=entry['cell']['id'];attempts=[]
        for order in entry['validation_orders']:
            folder=out/name/('order'+str(order));folder.parent.mkdir(exist_ok=True);log=out/'logs'/(name+'_order'+str(order)+'.log')
            code=None
            try:
                with log.open('w')as stream:
                    code=subprocess.call([sys.executable,'-B','-u',str(worker),'--root',str(root),'--cell',name,'--validation-order',str(order),'--output',str(folder)],env=env,stdout=stream,stderr=subprocess.STDOUT)
                require(code==0,'Worker exit '+str(code));result=read(folder/'RESULT.json')
                require(result['schema']=='thomson-analytic-finite-cell-v1'and result['status']=='PASS_FRESH_ANALYTIC_CELL'and result['method']=='bernstein_residual_exact'and result['cell']==entry['cell']and type(result['validation_order'])is int and result['validation_order']==order,'Worker result mismatch')
                require(result['inputs_unchanged']is True and result['worker_sha256']==plan['worker_sha256'],'Worker provenance mismatch')
                for key,h in result['files'].items():require(sha(bound_path(folder,key))==h,'Output hash mismatch')
                for key,h in sources.items():require(result['source_sha256'].get(key)==h,'Worker source mismatch')
                require(result['source_sha256']['AnalyticFinite/INDEX.json']==plan['index_sha256']and result['source_sha256']['AnalyticFinite/source_bindings.json']==plan['source_bindings_sha256'],'Worker index mismatch')
                attempts.append(dict(validation_order=order,status='PASS',exit_code=code,log=str(log.relative_to(out)),log_sha256=sha(log)))
                print('PASS',name,'order',order,result['bounds'],flush=True)
                return dict(id=name,status='PASS',cell=entry['cell'],method='bernstein_residual_exact',validation_order=order,result=str((folder/'RESULT.json').relative_to(out)),result_sha256=sha(folder/'RESULT.json'),bounds=result['bounds'],attempts=attempts)
            except Exception as error:
                attempts.append(dict(validation_order=order,status='FAIL',exit_code=code,error=repr(error),log=str(log.relative_to(out)),log_sha256=sha(log)if log.exists()else None))
                print('RETRY',name,'order',order,repr(error),flush=True)
        return dict(id=name,status='FAIL',cell=entry['cell'],method='bernstein_residual_exact',attempts=attempts)
    schedule=sorted(entries,key=lambda e:(e['cell']['degree'],e['validation_orders'][0]),reverse=True)
    with ThreadPoolExecutor(max_workers=args.jobs)as pool:results=list(pool.map(run,schedule))
    results.sort(key=lambda e:ids.index(e['id']));actual=union([r['cell']for r in results if r['status']=='PASS'])
    unchanged=sha(worker)==plan['worker_sha256']and sha(dispatcher)==plan['dispatcher_sha256']and sha(index)==plan['index_sha256']and sha(bind)==plan['source_bindings_sha256']
    try:unchanged=unchanged and source_bindings(root)[1]==sources
    except Exception:unchanged=False
    passed=all(r['status']=='PASS'for r in results)and unchanged and actual==expected
    status=('PASS_COMPLETE_ANALYTIC_FINITE_REPLAY'if not args.cell else'PASS_SELECTED_ANALYTIC_CELLS')if passed else'INCOMPLETE'
    summary=dict(schema='thomson-analytic-finite-replay-summary-v1',status=status,count=len(entries),closed_nonnegative_union=actual,results=results,complete_30_cell_plan=not bool(args.cell),inputs_unchanged=unchanged,plan_sha256=sha(out/'PLAN.json'),seconds=time.monotonic()-started,scope='Fresh residual arithmetic and four exact correction/floor bounds for every listed cell. Analytic square identities replace all numerical Gram positivity predicates, and the analytic coefficient right inverse replaces all numerical correction-inverse predicates.')
    write(out/'SUMMARY.json',summary);print(status,actual,flush=True)
    return int(not passed)

if __name__=='__main__':raise SystemExit(main())
