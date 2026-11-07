#!/usr/bin/env python3
"""Propose compact witnesses from the small-basis reference family; no acceptance."""
import argparse,json,subprocess,sys,time
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--reference-root',type=Path,required=True);p.add_argument('--output-root',type=Path,required=True)
    p.add_argument('--jobs',type=int,default=6);p.add_argument('--cell',action='append',default=[])
    a=p.parse_args();root=a.output_root.resolve();source=a.reference_root.resolve()
    entries=json.loads((root/'SymmetricFinite/INDEX.json').read_text())['cells']
    if a.cell:entries=[e for e in entries if e['cell']['id'] in a.cell]
    logs=root.parent/'compact_proposal_logs';logs.mkdir(exist_ok=True)
    def run(e):
        name=e['cell']['id'];start=time.monotonic()
        with (logs/(name+'.log')).open('w') as log:
            code=subprocess.call([sys.executable,'-B','-u',str(root/'SymmetricFinite/propose_compact.py'),
                '--root',str(source),'--cell',name,'--output-root',str(root)],stdout=log,stderr=subprocess.STDOUT)
        print('PROPOSED_COMPACT' if code==0 else 'FAILED_COMPACT',name,round(time.monotonic()-start,1),flush=True)
        return code
    with ThreadPoolExecutor(max_workers=a.jobs) as pool:codes=list(pool.map(run,entries))
    if any(codes):raise SystemExit(1)


if __name__=='__main__':main()
