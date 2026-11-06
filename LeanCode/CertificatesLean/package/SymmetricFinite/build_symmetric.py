"""Construct the exact symmetry-adapted finite certificate directly.

No original Gram witness, original evaluation inverse, or projection is a
verification input. The fixed dyadic matrices are independent proposals.
"""
import time,os
import numpy as np
import structure as v
from taylor_models import TM,ORDER,iv,candidate_model,normalized_phi,potential_evaluation_mode,shared_contact_jets
from matrix_models import MT,toI
from ipoly import IP
from interval_arithmetic import I
from analytic_basis import SUPPORTED_PIVOTS,moment_kernel_row
from hermite import hermite_coefficients
from canonical import basis
from invariant_raw import power_sum
from invariant_quotient import raw_symmetry, moment_data, coordinate_tags

COORDINATES = coordinate_tags(2*v.D)
from kernels import models,Evaluator


def descriptors():
    for name,kind,d in [('M0','s3',v.D),('M1','s2',v.D-1),('Mdet','s3',v.D-2)]:
        desc=basis(kind,d)
        for group,raw in enumerate(raw_symmetry(kind,d,2*v.D)):
            if desc['frees'][group]:
                yield name,kind,d,group,desc,dict(raw,name=name+'_'+raw['name'])


def transform(B,record):
    free=record['free'];n=len(free)
    jj=record['change_of_basis']
    if len(jj)!=n or any(len(row)!=n for row in jj):
        raise ArithmeticError('Invalid square basis change')
    if any(type(z) is not int or z != int(i==j)
           for i,row in enumerate(jj) for j,z in enumerate(row)):
        raise ArithmeticError('Canonical basis requires exact identity change')
    if isinstance(B,MT):
        coefficients=B.c
        B=IP.fromMT(B)
        B.canonical_coefficients=coefficients
    if not hasattr(B, 'canonical_coefficients'):
        raise ArithmeticError('Missing original canonical Taylor coefficients')
    for j,f in enumerate(free):
        B.c[0][f,:]=I(np.asarray(jj[j],dtype=float))
        for k in range(1,ORDER+1):B.c[k][f,:]=I(np.zeros(n))
        B.e[f,:]=I(np.zeros(n))
    B.active_rows=[record['pivot']] if record['name'].startswith('F') else record['pivots']
    return B


def build(center,width,record,minorant):
    if minorant not in ('general','original','far4','far6'):
        raise ValueError('Unknown Hermite profile')
    start=time.time();S,A,rootinfo=candidate_model(center,width)
    print('Root model',rootinfo,flush=True)
    rec=dict(record)
    descs=list(descriptors())
    # Moment polynomials are exactly the common production construction.
    data=moment_data(v.D)+[desc[-1] for desc in descs]
    if rec.get('degree')!=2*v.D or [r['name'] for r in rec['basis_records']]!=[d['name'] for d in data]:
        raise ArithmeticError('Invalid symmetric block order')
    height=A.interval()
    if not(height.a>(iv.mpf(13)/50).b and height.b<(iv.mpf(1)/3).a):
        raise ArithmeticError('Root outside analytic kernel domain')
    bases=[]
    for dat,r in zip(data[:v.D],rec['basis_records'][:v.D]):
        m=dat['raw'].shape[1];p=r['pivot'];free=r['free'];k=dat['k']
        if type(p) is not int or not 0<=p<m or free!=[i for i in range(m) if i!=p]:
            raise ArithmeticError('Invalid moment kernel partition')
        if (k,p) not in SUPPORTED_PIVOTS:raise ArithmeticError('Unsupported moment pivot')
        M=[[TM.const(int(i==f)) for f in free] for i in range(m)]
        M[p]=moment_kernel_row(A,k,p,free,lambda n,d:TM.const(iv.mpf(n)/d))
        bases.append(transform(MT.from_scalars(M),r))
    cache={}
    kernel_evaluator=Evaluator(A)
    for (name,kind,d,group,desc,dat),r in zip(descs,rec['basis_records'][v.D:]):
        if r['free']!=desc['frees'][group] or r['pivots']!=desc['pivots'][group]:
            raise ArithmeticError('Invalid analytic symmetry kernel partition')
        if (kind,d) not in cache:cache[kind,d]=models(kind,d,A,evaluator=kernel_evaluator)
        B=transform(cache[kind,d][group],r)
        bases.append(B)
        print('Symmetry basis',dat['name'],'shape',B.c[0].lo.shape,'error',float(np.max(B.e.hi)),flush=True)
    nodes=[A,2*A-1,-A+(1-A)/iv.sqrt(2),-A-(1-A)/iv.sqrt(2)]
    if minorant == "general":
        tags = rec["auxiliary_nodes"]
        if len(tags) != v.D - 4 or any(t not in ["A", "B", "C", "D"] for t in tags):
            raise ArithmeticError("Invalid higher degree profile")
        mult = [2 + 2 * tags.count(t) for t in "ABCD"]
        endpoint = 1
    else:
        if v.D != 6:
            raise ArithmeticError("Legacy profiles require degree12")
        tags = {"original": [], "far4": ["B", "D"], "far6": ["B", "B"]}[minorant]
        mult = [2 + 2 * tags.count(t) for t in "ABCD"]
        endpoint = 5 if minorant == "original" else 1
    rec["auxiliary_nodes"] = tags
    rec["_hermite_multiplicities"] = {**dict(zip("ABCD", mult)), "minus_one": endpoint}
    rec["_potential_evaluation"] = potential_evaluation_mode(S)
    if sum(mult) + endpoint != 2 * v.D + 1:
        raise ArithmeticError("Wrong interpolation dimension")
    balance_mode = os.environ.get("N8_TARGET_BALANCE", "unit")
    potential = normalized_phi
    if balance_mode == "unit":
        rec["_target_multiplier"] = "1"
        rec["_target_evaluation"] = "normalized_phi"
        if S.interval().a > 0 and rec["_potential_evaluation"] == "quotient":
            def potential(S, T, k=0):
                # phi_s(T)+1/s has the same nonconstant Hermite target.
                if k:
                    return normalized_phi(S, T, k)
                return ((-S / 2) * (2 - 2*T).log()).exp() / S
            rec["_target_evaluation"] = "positive_quotient_constant_cancelled"
    elif balance_mode == "riesz":
        cc = iv.mpf(center)
        if not cc.a > 0 or not S.interval().a > 0:
            raise ArithmeticError("Balanced target requires a positive cell")
        rho = iv.mpf(3) / 2
        constant = TM.const(iv.exp((-cc / 2) * iv.log(rho)) / cc)
        def potential(S, T, k=0):
            # This equals B(s)*phi_s(T) plus a T-independent constant.
            # The constant cancels in H[0]-energy/28 before any enclosure.
            # Derivatives are K*2^k*(s/2)_k*d^(-k)*(rho/d)^(s/2).
            d = 2 - 2 * T
            pref = TM.const(1)
            for j in range(k):
                pref = pref * (S + 2*j)
            exponent = (-S / 2) * (d / rho).log()
            if k:
                exponent = exponent - k * d.log()
            return constant * pref * exponent.exp()
        rec["_target_multiplier"] = "(s/center)*(3/2)^((s-center)/2)"
        rec["_target_evaluation"] = "balanced_exponential_constant_cancelled"
    else:
        raise ArithmeticError("Unknown target balance")
    potential = shared_contact_jets(S, potential, balanced=(balance_mode == 'riesz'))
    hc = hermite_coefficients(S, nodes, mult, endpoint, potential=potential)
    print("Hermite Taylor remainder", float(max(x.e.b for x in hc)), flush=True)
    target = []
    for tag in COORDINATES:
        n = tag[0]+2*tag[1]+3*tag[2]
        coefficient = power_sum(n).get(tag,0)
        val = hc[n]*coefficient/3 if coefficient else TM.const(0)
        target.append([val])
    # The balanced potential already gives exactly the balanced target.
    # The unit branch retains its original multiplier.
    if balance_mode == "unit":
        balance = TM.const(1)
        target = [[balance * row[0]] for row in target]
    print(
        "Built target models", balance_mode, "elapsed", time.time() - start, flush=True
    )
    result=MT.from_scalars(target)
    from fractions import Fraction
    from exact_iv import PRECISION
    result.remainder_generators=[]
    for n in range(2*v.D+1):
        row=[Fraction(power_sum(n).get(tag,0),3) for tag in COORDINATES]
        if any(row):
            result.remainder_generators.append((row,Fraction(hc[n].e.hi,1<<PRECISION)))
    return S, A, rootinfo, rec, data, bases, result

