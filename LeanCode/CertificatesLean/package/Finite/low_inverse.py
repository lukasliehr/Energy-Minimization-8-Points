"""A short polynomial inverse certificate with a full-order solution proposal.

The inverse polynomial is an arbitrary exact-dyadic witness. Its omitted
coefficients are zero by definition; ALL products above the model order enter
the explicit tail bound. Final corrected Grams are still checked by verify.
"""
import json
from pathlib import Path
import time

import numpy as np
from interval_arithmetic import I
from ipoly import IP
from fast_interval import mm,absI,norm
from taylor_models import ORDER
from trace_core import require


def short_product(T,P):
    degree=len(P)-1
    require(0<=degree<=ORDER,'short polynomial degree')
    require(len(T.c)==ORDER+1,'full source model order')
    n,inner=T.c[0].lo.shape
    require(all(c.lo.shape==T.c[0].lo.shape for c in T.c) and
            all(p.lo.shape==P[0].lo.shape and np.array_equal(p.lo,p.hi) for p in P) and
            P[0].lo.shape[0]==inner,'exact point polynomial dimensions')
    zero=I(np.zeros((n,P[0].lo.shape[1])))
    coefficients=[]
    for k in range(ORDER+1):
        z=zero
        for j in range(min(k,degree)+1):z=z+mm(T.c[k-j],P[j])
        coefficients.append(z)
    suffix=[None]*(degree+2)
    suffix[degree+1]=I(np.zeros_like(P[0].lo))
    for j in range(degree,-1,-1):suffix[j]=suffix[j+1]+absI(P[j])
    tail=mm(T.e,suffix[0])
    for i in range(ORDER-degree+1,ORDER+1):
        tail=tail+mm(absI(T.c[i]),suffix[ORDER+1-i])
    return IP(coefficients,tail)


def solve(T,r,output):
    output=Path(output);start=time.monotonic();cpu=time.process_time()
    np.savez(output/'fresh_T_and_r.npz',T_lo=np.stack([c.lo for c in T.c]),
             T_hi=np.stack([c.hi for c in T.c]),T_e_lo=T.e.lo,T_e_hi=T.e.hi,
             r_lo=np.stack([c.lo for c in r.c]),r_hi=np.stack([c.hi for c in r.c]),
             r_e_lo=r.e.lo,r_e_hi=r.e.hi)
    tt=[cc.lo/2+cc.hi/2 for cc in T.c]
    rr=[cc.lo/2+cc.hi/2 for cc in r.c]
    pi=[np.linalg.inv(tt[0])]
    zz=[pi[0]@rr[0]]
    # All these binary64 operations propose exact dyadic coefficients only.
    for k in range(1,ORDER+1):
        pi.append(-pi[0]@sum((tt[i]@pi[k-i] for i in range(1,k+1)),np.zeros_like(pi[0])))
        zz.append(pi[0]@(rr[k]-sum((tt[i]@zz[k-i] for i in range(1,k+1)),np.zeros_like(zz[0]))))
    identity=IP.const(I(np.eye(tt[0].shape[0])))
    candidates=sorted(set(d for d in [1,2,4,6,ORDER] if d<=ORDER))
    attempts=[];chosen=None
    for degree in candidates:
        ds=time.monotonic();dc=time.process_time()
        P=[I(c) for c in pi[:degree+1]]
        residual=identity.add(short_product(T,P).negative())
        q=norm(residual.bound())
        attempt=dict(degree=degree,residual_upper=q,passed=q<1,
                     seconds=time.monotonic()-ds,cpu_seconds=time.process_time()-dc,
                     retained_coefficient_matrix_products=(ORDER+1)*(degree+1)-degree*(degree+1)//2,
                     tail_matrix_products=degree+1)
        attempts.append(attempt)
        print('SHORT_INVERSE',json.dumps(attempt),flush=True)
        if q<1:
            chosen=(degree,P,residual,q)
            break
    require(chosen is not None,'all short inverse residual gates failed')
    degree,P,Res,q=chosen
    ZZ=IP([I(c) for c in zz])
    resid=r.add(short_product(T,ZZ.c).negative())
    B=Res.bound();rho=resid.bound()
    u=float((I(norm(rho))/(1-I(q))).hi)
    delta=I(np.full_like(rho.lo,u))
    for _ in range(12):delta=I((rho+mm(B,delta)).hi)
    Pbound=I(np.zeros_like(P[0].lo))
    for c in P:Pbound=Pbound+absI(c)
    component=I(mm(Pbound,delta).hi)
    scalar=float((I(norm(Pbound))/(1-I(q))*I(norm(rho))).hi)
    component=I(np.minimum(component.hi,scalar))
    result=IP(ZZ.c,component)
    result.inverse_residual_upper=q
    result.inverse_polynomial_norm_upper=norm(Pbound)
    result.solution_residual_upper=norm(rho)
    result.solution_error_upper=norm(component)
    report=dict(status='SHORT_INVERSE_AND_FULL_ORDER_SOLUTION_ENCLOSURE_VALIDATED',
                chosen_degree=degree,solution_polynomial_order=ORDER,attempts=attempts,
                inverse_residual_upper=q,inverse_polynomial_norm_upper=norm(Pbound),
                solution_residual_upper=norm(rho),solution_error_upper=norm(component),
                seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,
                scope='Inverse and solution enclosure only; complete acceptance still requires the final original Gram/equality gates.')
    (output/'SHORT_INVERSE.json').write_text(json.dumps(report,indent=2)+'\n')
    np.savez(output/'short_inverse_and_solution_proposals.npz',P=np.stack([c.lo for c in P]),
             Z=np.stack(zz),solution_error=component.hi)
    print('SHORT_SOLUTION',json.dumps(report),flush=True)
    return result
