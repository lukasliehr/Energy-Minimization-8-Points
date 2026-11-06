"""Direct exact-factor correction models, with a bound on the SAME Cf downstream.

No old rounded C, old acceptance report, or perturbation-transfer premise is used.
The fixed exact matrix is Cf=Aref_exact.T K. Only v2 without UV is supported here.
"""
from fractions import Fraction
import hashlib
import json
import time

import numpy as np
from flint import fmpz_mat

from interval_arithmetic import I, sqrt_integer
from exact_i import rational_bound
from ipoly import IP
from matrix_models import toI
from taylor_models import ORDER, iv
from trace_core import TraceEngine, check_partition, require


def integer_matrix(values):
    a=np.asarray(values,dtype=np.float64)
    require(a.ndim==2 and a.size>0 and np.isfinite(a).all(),'finite nonempty matrix')
    ratios=[[float(z).as_integer_ratio() for z in row] for row in a]
    denominator=max(d for row in ratios for _,d in row)
    require(denominator>0 and denominator&(denominator-1)==0,'dyadic denominator')
    return fmpz_mat([[n*(denominator//d) for n,d in row] for row in ratios]),denominator


class FactoredEngine(TraceEngine):
    def __init__(self,output,record,raw_data,coefficient_row_count):
        super().__init__(output,record['basis_records'])
        start=time.monotonic();cpu=time.process_time()
        require('right_inverse' not in record,'no dense C input permitted')
        proposal=record['correction_recipe']
        require(proposal['kind']=='reference_active_coefficient_transpose_v2',
                'this checker supports only the explicit v2 factor definition')
        require(proposal.get('additive_correction') is None,'UV factors unsupported in this checker')
        require('left_preconditioner' not in record,'v2 left preconditioner is defined by K.T')
        selected=record['rows']
        m=coefficient_row_count-2
        require(isinstance(selected,list) and len(selected)==m and len(set(selected))==m and
                all(type(i) is int and 0<=i<coefficient_row_count for i in selected),
                'complete retained row ordering')
        K=np.asarray(proposal['right_factor'],dtype=np.float64)
        require(K.shape==(m,m) and np.isfinite(K).all(),'right factor dimensions')
        Kz,kden=integer_matrix(K)
        require(len(raw_data)==len(self.records)==len(proposal['reference_active_rows']),
                'complete factor block coverage')
        require([r['name'] for r in self.records]==[d['name'] for d in raw_data],
                'factor block ordering')
        self.selected=list(selected)
        self.prepared=[]
        nvars=sum(len(r['free'])*(len(r['free'])+1)//2 for r in self.records)
        clo=np.empty((nvars,m));chi=np.empty_like(clo)
        off=0
        rt=sqrt_integer(2)
        setup=[]
        for dat,rb,stored in zip(raw_data,self.records,proposal['reference_active_rows']):
            bs=time.monotonic();bc=time.process_time()
            raw=dat['raw'];n=raw.shape[1];r=len(rb['free'])
            active=[rb['pivot']] if dat['name'].startswith('F') else list(rb['pivots'])
            require(raw.shape==(coefficient_row_count,n,n) and
                    np.array_equal(raw,np.swapaxes(raw,-1,-2)),'symmetric raw coefficient tensor')
            require(sorted(list(rb['free'])+active)==list(range(n)),
                    'complete reference free/active partition')
            require(len(active)==(1 if dat['name'].startswith('F') else 21),
                    'expected active dimension')
            J=np.asarray(rb['change_of_basis'],dtype=np.float64)
            A=np.asarray(stored,dtype=np.float64)
            require(J.shape==(r,r) and A.shape==(len(active),r) and
                    np.isfinite(J).all() and np.isfinite(A).all(),'reference basis dimensions')
            Bref=np.empty((n,r));Bref[rb['free'],:]=J;Bref[active,:]=A
            Bz,bden=integer_matrix(Bref)
            Jz,jden=integer_matrix(J)
            pairs=[(i,j) for i in range(r) for j in range(i,r)]
            sl=slice(off,off+len(pairs));off=sl.stop
            dden=bden*bden*kden*int(dat['den'])
            require(dden>0,'positive exact factor denominator')
            terms=[]
            for row in selected:
                rr,cc=np.nonzero(raw[row])
                terms.append([(int(i),int(j),int(raw[row,i,j])) for i,j in zip(rr,cc)])
            factor_lo=np.array([1.0 if i==j else float(rt.lo) for i,j in pairs])
            factor_hi=np.array([1.0 if i==j else float(rt.hi) for i,j in pairs])
            factor=I(factor_lo,factor_hi)
            matrices=[]
            digest=hashlib.sha256()
            digest.update(str(dden).encode()+b'\n')
            for col in range(m):
                rz=[[0]*n for _ in range(n)]
                for row,entries in enumerate(terms):
                    w=int(Kz[row,col])
                    if w:
                        for i,j,z in entries:rz[i][j]+=w*z
                Rz=fmpz_mat(rz)
                D=Bz.transpose()*Rz*Bz
                require(all(D[i,j]==D[j,i] for i in range(r) for j in range(r)),
                        'exact inverse-svec factor symmetry')
                matrices.append(D)
                lo=[];hi=[]
                for i,j in pairs:
                    z=int(D[i,j]);digest.update(str(z).encode()+b',')
                    lo.append(rational_bound(z,dden,False))
                    hi.append(rational_bound(z,dden,True))
                bounds=I(lo,hi)*factor
                clo[sl,col]=bounds.lo;chi[sl,col]=bounds.hi
                if col%40==0 or col==m-1:
                    print('FACTOR',dat['name'],col,m,'elapsed',time.monotonic()-start,flush=True)
            self.prepared.append(dict(name=dat['name'],raw=raw,den=int(dat['den']),
                                      Jz=Jz,jden=jden,matrices=matrices,dden=dden,
                                      pairs=pairs,slice=sl))
            setup.append(dict(block=dat['name'],seconds=time.monotonic()-bs,
                              cpu_seconds=time.process_time()-bc,columns=m,
                              rational_D_sha256=digest.hexdigest(),raw_dimension=n,
                              free_dimension=r,active_dimension=len(active)))
            (self.output/'FACTOR_SETUP_PROGRESS.json').write_text(json.dumps(setup,indent=2)+'\n')
        require(off==nvars and np.isfinite(clo).all() and np.isfinite(chi).all() and
                np.all(clo<=chi),'complete finite Cf enclosure')
        self.Cf=I(clo,chi)
        self.left=K.T.copy()
        self.factor_setup=dict(seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,
                               blocks=setup,shape=[nvars,m],
                               exact_definition='Cf=Aref_exact.T K, L=K.T; no UV',
                               enclosure_sha256=hashlib.sha256(clo.astype('<f8').tobytes()+
                                                             chi.astype('<f8').tobytes()).hexdigest())
        np.savez(self.output/'Cf_enclosure.npz',lo=clo,hi=chi)
        (self.output/'FACTOR_SETUP.json').write_text(json.dumps(self.factor_setup,indent=2)+'\n')

    def correction_models(self,data,bases,rows,inds,slices,C,w0,targetM):
        start=time.monotonic();cpu=time.process_time()
        selected=list(map(int,rows));m=len(selected)
        require(selected==self.selected,'physical row order must equal exact factor row order')
        require(len(data)==len(bases)==len(inds)==len(slices)==len(self.records)==
                len(self.captured)==len(self.prepared),'all-block correction coverage')
        require(C.lo.shape==self.Cf.lo.shape and np.array_equal(C.lo,self.Cf.lo) and
                np.array_equal(C.hi,self.Cf.hi),'downstream C must be this exact Cf enclosure')
        require(len(w0)==C.lo.shape[0] and np.isfinite(w0).all(),'nominal center dimensions')
        tc=[I(np.zeros((m,m))) for _ in range(ORDER+1)]
        te=I(np.zeros((m,m)));residual=targetM
        for dat,B,ii,sl,record,cap,p in zip(data,bases,inds,slices,self.records,self.captured,self.prepared):
            bs=time.monotonic();bc=time.process_time()
            require(dat['name']==p['name'] and int(dat['den'])==p['den'] and
                    np.array_equal(dat['raw'],p['raw']),'physical raw tensor equals factor definition')
            require(ii==p['pairs'] and sl.start==p['slice'].start and sl.stop==p['slice'].stop,
                    'inverse-svec index order and block slice')
            N,_,_=cap
            free,active,V=check_partition(N,B,record)
            for col in range(m+1):
                if col<m:
                    D=p['matrices'][col]
                    HZ=p['Jz']*D*p['Jz'].transpose()
                    hd=p['jden']*p['jden']*p['dden'];r=len(free)
                    Hmp=iv.matrix([[iv.mpf(Fraction(int(HZ[i,j]),hd)) for j in range(r)]
                                  for i in range(r)])
                    H=toI(Hmp)
                else:
                    H,Hmp=self.make_H(p['Jz'],p['jden'],w0[sl],ii)
                out=self.one_column(V,free,active,H,Hmp,dat,selected)
                if col<m:
                    for k in range(ORDER+1):tc[k][:,col:col+1]=tc[k][:,col:col+1]+out.c[k]
                    te[:,col:col+1]=te[:,col:col+1]+out.e
                else:residual=residual.add(out.negative())
                self.column_count+=1
                if col%20==0 or col==m:
                    progress=dict(block=dat['name'],column=col,columns_per_block=m+1,
                                  completed_block_columns=self.column_count,
                                  correction_seconds=time.monotonic()-start)
                    (self.output/'TRACE_PROGRESS.json').write_text(json.dumps(progress,indent=2)+'\n')
                    print('TRACE',json.dumps(progress),flush=True)
            self.stages.append(dict(block=dat['name'],seconds=time.monotonic()-bs,
                                    cpu_seconds=time.process_time()-bc,columns=m+1))
            (self.output/'TRACE_STAGES.json').write_text(json.dumps(self.stages,indent=2)+'\n')
        self.total_seconds=time.monotonic()-start
        self.total_cpu_seconds=time.process_time()-cpu
        return IP(tc,te),residual
