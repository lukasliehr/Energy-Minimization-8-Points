"""Untrusted compact numerical proposal; its output is a fresh dyadic witness.

No exact-real identity C=Aref.T K is asserted or needed. The complete
interval correction/positivity proof checks the actual generated floats.
"""
import hashlib,math
import numpy as np


def expand(record):
    if 'correction_recipe' not in record:
        return record,dict(kind='stored_dyadic_matrix',generated=False)
    from build_symmetric import descriptors,v
    proposal=record['correction_recipe']
    if proposal['kind']!='symmetric_reference_active_coefficient_transpose_v1':
        raise ValueError('Unknown compact symmetry recipe')
    if 'right_inverse' in record or 'left_preconditioner' in record:
        raise ValueError('Compact recipe determines both correction matrices')
    data=v.raw_data()[:v.D]+[desc[-1] for desc in descriptors()]
    refs=proposal['reference_active_rows'];rows=record['rows']
    if len(data)!=len(refs) or len(data)!=len(record['basis_records']):
        raise ValueError('Wrong compact block count')
    blocks=[]
    for dat,rb,active_values in zip(data,record['basis_records'],refs):
        n=dat['raw'].shape[1];r=len(rb['free'])
        active=[rb['pivot']] if rb['name'].startswith('F') else rb['pivots']
        if sorted(rb['free']+active)!=list(range(n)):raise ValueError('Invalid compact basis partition')
        J=np.asarray(rb['change_of_basis'],dtype=np.float64)
        active_values=np.asarray(active_values,dtype=np.float64)
        if J.shape!=(r,r) or active_values.shape!=(len(active),r):raise ValueError('Invalid compact reference shape')
        B=np.empty((n,r));B[rb['free'],:]=J;B[active,:]=active_values
        if not np.isfinite(B).all():raise ValueError('Nonfinite compact reference')
        tensor=dat['raw'][rows].astype(float)/dat['den']
        M=B.T@(tensor@B);ii=np.triu_indices(r)
        factor=np.where(ii[0]==ii[1],1.,math.sqrt(2))
        blocks.append(M[:,ii[0],ii[1]]*factor)
    Aref=np.concatenate(blocks,axis=1)
    m=len(v.EXPS)-2;K=np.asarray(proposal['right_factor'],dtype=np.float64)
    if K.shape!=(m,m) or not np.isfinite(K).all():raise ValueError('Invalid compact right factor')
    C=Aref.T@K
    if not np.isfinite(C).all():raise ValueError('Nonfinite compact output')
    rec=dict(record);rec.pop('correction_recipe')
    rec.update(right_inverse=C.tolist(),left_preconditioner=K.T.tolist())
    digest=hashlib.sha256(C.astype('<f8',copy=False).tobytes(order='C')).hexdigest()
    return rec,dict(kind=proposal['kind'],generated=True,generated_C_shape=list(C.shape),
        generated_C_sha256_le_f64=digest,
        semantics='Untrusted numerical proposal; actual finite output entries denote exact dyadics.')
