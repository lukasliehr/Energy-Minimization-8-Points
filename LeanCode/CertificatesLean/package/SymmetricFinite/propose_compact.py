#!/usr/bin/env python3
"""Untrusted compact-reference proposal experiment, independent full verification."""
import argparse,json,sys,os,time
from pathlib import Path


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cell',required=True)
    ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output-root',type=Path,required=True)
    args=ap.parse_args();root=args.root.resolve();out=args.output_root.resolve();(out/'SymmetricFinite/witnesses').mkdir(exist_ok=True);(out/'SymmetricFinite/cells').mkdir(exist_ok=True)
    idx=json.loads((root/'SymmetricFinite/INDEX.json').read_text())['cells']
    ent=next(e for e in idx if e['cell']['id']==args.cell);cell=ent['cell']
    for key in list(os.environ):
        if key.startswith('N8_'):del os.environ[key]
    os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1',
        N8_DEG_HALF=str(cell['degree']//2),N8_TAYLOR_ORDER=str(cell['order']),N8_TARGET_BALANCE=cell['balance'],
        N8_EXACT_MM_BITS='112',N8_EXACT_SCALAR_BITS='384',N8_COEFFICIENT_MODE='streamed',N8_ROW_CHUNK='32',N8_ROW_WORKERS='1')
    sys.path[:0]=[str(root/'SymmetricFinite'),str(root/'Finite'),str(root/'Finite/kernel')]
    import numpy as np,codec,build_symmetric as b,verify_symmetric as v
    asset=json.loads((root/ent['proposal']).read_text())['witness']
    rec=codec.load(root/asset['path'],asset['semantic_sha256'])
    started=time.monotonic();S,A,ri,rd,data,bases,target=b.build(cell['center'],cell['halfwidth'],rec,cell['profile'])
    rows=rec['rows'];blocks=[];refs=[]
    for dat,B,record in zip(data,bases,rec['basis_records']):
        bm=np.array([[float(B.mp0[i,j]) for j in range(B.mp0.cols)] for i in range(B.mp0.rows)])
        raw=dat['raw'][rows].astype(float)/dat['den']
        coeff=bm.T@(raw@bm);ii=np.triu_indices(bm.shape[1])
        factor=np.where(ii[0]==ii[1],1.,np.sqrt(2.))
        blocks.append(coeff[:,ii[0],ii[1]]*factor)
        refs.append(bm[B.active_rows,:].tolist())
    Aref=np.concatenate(blocks,axis=1)
    Q,RR=np.linalg.qr(Aref.T,mode='reduced');K=np.linalg.inv(RR)
    C=Aref.T@K;L=K.T
    print('COMPACT_PROPOSAL','center_inverse_error',np.linalg.norm(L@Aref@C-np.eye(K.shape[0]),np.inf),
          'norm_C',np.linalg.norm(C,np.inf),'condition_R',np.linalg.cond(RR),flush=True)
    recipe=dict(kind='symmetric_reference_active_coefficient_transpose_v1',reference_active_rows=refs,right_factor=K.tolist())
    compact=dict(rec);compact.pop('right_inverse');compact.pop('left_preconditioner',None);compact['correction_recipe']=recipe
    path=out/'SymmetricFinite/witnesses'/f"{cell['id']}.capd.xz"
    transport=codec.dump(compact,path)
    import hashlib
    asset=dict(path=str(path.relative_to(out)),compression='capd1-xz',
               compressed_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),**transport)
    manifest=dict(cell=cell,witness=asset)
    (out/'SymmetricFinite/cells'/f"{cell['id']}.json").write_text(json.dumps(manifest,indent=2)+'\n')
    print('EXPORTED_COMPACT',cell['id'],'bytes',path.stat().st_size,'seconds',time.monotonic()-started,flush=True)


if __name__=='__main__':main()
