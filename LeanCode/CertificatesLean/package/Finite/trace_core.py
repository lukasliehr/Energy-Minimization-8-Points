"""Shared uniform trace engine, isolated from production sources.

The three helper bodies below are copied from the reviewed uniform_pilot.py.
Exact intervals and FLINT integer arithmetic are the same production primitives.
"""
from fractions import Fraction as F
import json,time
from pathlib import Path
import numpy as np
from flint import fmpz_mat
from ipoly import IP
from matrix_models import toI
from taylor_models import ORDER,iv
from interval_arithmetic import I
from exact_i import rational_bound
from fast_interval import mm,absI


def require(ok,message):
    if not ok:raise ValueError(message)

def check_partition(N, basis, record):
    free = list(record['free'])
    active = [record['pivot']] if record['name'].startswith('F') else list(record['pivots'])
    r, n = (len(free), N.c[0].lo.shape[0])
    require(sorted(free + active) == list(range(n)), 'free/active partition')
    require(N.c[0].lo.shape == (n, r), 'N shape')
    for row, f in enumerate(free):
        expected = np.array([int(row == j) for j in range(r)])
        require(np.array_equal(N.c[0].lo[f], expected) and np.array_equal(N.c[0].hi[f], expected), 'free identity constant')
        require(all((np.all(c.lo[f] == 0) and np.all(c.hi[f] == 0) for c in N.c[1:])), 'free higher coefficients zero')
        require(np.all(N.e.lo[f] == 0) and np.all(N.e.hi[f] == 0), 'free remainder zero')
    require(list(basis.active_rows) == active, 'active row source order')
    return (free, active, N.slice(active, list(range(r))))

def product_with_suffix_tail(A, B):
    shape = (A.c[0].lo.shape[0], B.c[0].lo.shape[1])
    zero = I(np.zeros(shape))
    coeff = []
    for k in range(ORDER + 1):
        z = zero
        for i in range(k + 1):
            z = z + mm(A.c[i], B.c[k - i])
        coeff.append(z)
    constant = A.mp0 * B.mp0 if A.mp0 is not None and B.mp0 is not None else None
    if constant is not None:
        coeff[0] = toI(constant)
    suffix = [None] * (ORDER + 2)
    suffix[ORDER + 1] = I(np.zeros_like(B.c[0].lo))
    for j in range(ORDER, -1, -1):
        suffix[j] = suffix[j + 1] + absI(B.c[j])
    tail = zero
    for i in range(1, ORDER + 1):
        tail = tail + mm(absI(A.c[i]), suffix[ORDER + 1 - i])
    tail = tail + mm(A.poly_bound(), B.e) + mm(A.e, B.poly_bound()) + mm(A.e, B.e)
    return IP(coeff, tail, constant)

def contract_sparse(Q, raw, rows, denominator, active=None):
    terms = []
    for row in rows:
        rr, cc = np.nonzero(np.triu(raw[row]))
        terms.append([(int(i), int(j), int(raw[row, i, j]) * (1 if i == j else 2)) for i, j in zip(rr, cc)])

    variable_terms=terms
    if active is not None:
        active_set=set(active)
        variable_terms=[[entry for entry in entries if entry[0] in active_set or entry[1] in active_set] for entries in terms]
        free=[i for i in range(Q.c[0].lo.shape[0]) if i not in active_set]
        ff=np.ix_(free,free)
        require(all(np.all(c.lo[ff]==0) and np.all(c.hi[ff]==0) for c in Q.c[1:]),
                'omitted free/free positive-order coefficients must be exactly zero')
        require(np.all(Q.e.lo[ff]==0) and np.all(Q.e.hi[ff]==0),
                'omitted free/free remainder must be exactly zero')

    def component(A, entries_by_row, errors=False):
        lo, hi = (np.zeros((len(rows), 1)), np.zeros((len(rows), 1)))
        for row, entries in enumerate(entries_by_row):
            values = []
            for i, j, w in entries:
                if errors:
                    w = abs(w)
                l, h = (float(A.lo[i, j]), float(A.hi[i, j]))
                if w < 0:
                    l, h = (h, l)
                an, ad = l.as_integer_ratio()
                bn, bd = h.as_integer_ratio()
                values.append((w, an, ad, bn, bd))
            d = max((max(ad, bd) for _, _, ad, _, bd in values), default=1)
            ln = sum((w * a * (d // ad) for w, a, ad, _, _ in values))
            hn = sum((w * b * (d // bd) for w, _, _, b, bd in values))
            lo[row, 0] = rational_bound(ln, d * denominator, False)
            hi[row, 0] = rational_bound(hn, d * denominator, True)
        return I(lo, hi)
    coeff = [None]+[component(a,variable_terms) for a in Q.c[1:]]
    error = component(Q.e, variable_terms, True)
    constant = iv.matrix([[sum((Q.mp0[i, j] * w for i, j, w in entries), iv.mpf(0)) / denominator] for entries in terms])
    coeff[0] = toI(constant)
    return (IP(coeff, error, constant), sum(map(len, terms)))


class TraceEngine:
    """Replace only the uniform A*C / A*w0 construction in verify_interval."""
    def __init__(self, output, records):
        self.output=Path(output)
        self.records=records
        self.captured=[]
        self.stages=[]
        self.column_count=0

    def build_wrapper(self, original_build):
        def build(*args,**kwargs):
            original_right=IP.right
            captured=[]
            def capture(model,J,Jmp=None):
                captured.append((model,I(J),Jmp))
                return original_right(model,J,Jmp)
            IP.right=capture
            try:
                result=original_build(*args,**kwargs)
            finally:
                IP.right=original_right
            require(len(captured)==len(self.records),'complete N capture')
            self.captured=captured
            return result
        return build

    @staticmethod
    def prepare_J(values):
        ratios=[[float(x).as_integer_ratio() for x in row] for row in values]
        denominator=max(d for row in ratios for _,d in row)
        require(denominator&(denominator-1)==0,'dyadic J')
        integers=fmpz_mat([[a*(denominator//d) for a,d in row] for row in ratios])
        return integers,denominator

    @staticmethod
    def make_H(Jz,jden,values,pairs):
        r=Jz.nrows()
        cr=[float(v).as_integer_ratio() for v in values]
        cd=max(d for _,d in cr)
        require(cd&(cd-1)==0,'dyadic C')
        diagonal=[[0]*r for _ in range(r)]
        off=[[0]*r for _ in range(r)]
        for (i,j),(a,d) in zip(pairs,cr):
            if i==j:diagonal[i][i]=a*(cd//d)
            else:off[i][j]=off[j][i]=a*(cd//d)
        Hz=[Jz*fmpz_mat(diagonal)*Jz.transpose(),Jz*fmpz_mat(off)*Jz.transpose()]
        den=jden*jden*cd
        require(all(h[i,j]==h[j,i] for h in Hz for i in range(r) for j in range(r)),
                'H exact channel symmetry')
        rt=iv.sqrt(2)
        Hmp=iv.matrix([[iv.mpf(F(int(Hz[0][i,j]),den))+
                        rt*iv.mpf(F(int(Hz[1][i,j]),2*den))
                        for j in range(r)] for i in range(r)])
        return toI(Hmp),Hmp

    @staticmethod
    def one_column(V,free,active,H,Hmp,dat,selected):
        P=V.right(H,Hmp)
        S=product_with_suffix_tail(P,V.T())
        n=len(free)+len(active)
        coeff=[I(np.zeros((n,n))) for _ in range(ORDER+1)]
        err=I(np.zeros((n,n)))
        qmp=iv.matrix(n,n)
        ff=np.ix_(free,free);af=np.ix_(active,free);fa=np.ix_(free,active);aa=np.ix_(active,active)
        coeff[0][ff]=H
        u,v=np.indices((len(active),len(active)))
        upper=(np.minimum(u,v),np.maximum(u,v))
        for k in range(ORDER+1):
            coeff[k][af]=P.c[k]
            coeff[k][fa]=P.c[k].T
            coeff[k][aa]=S.c[k][upper]
        err[af]=P.e;err[fa]=P.e.T;err[aa]=S.e[upper]
        for i,f in enumerate(free):
            for j,g in enumerate(free):qmp[f,g]=Hmp[i,j]
        for i,a in enumerate(active):
            for j,f in enumerate(free):qmp[a,f]=qmp[f,a]=P.mp0[i,j]
            for j,b in enumerate(active):qmp[a,b]=S.mp0[min(i,j),max(i,j)]
        return contract_sparse(IP(coeff,err,qmp),dat['raw'],selected,dat['den'],active)[0]

    def correction_models(self,data,bases,rows,inds,slices,C,w0,targetM):
        start=time.monotonic();cpu=time.process_time()
        selected=list(map(int,rows));m=len(selected)
        require(C.lo.shape==(sum(map(len,inds)),m) and np.array_equal(C.lo,C.hi),
                'fixed point correction matrix')
        tc=[I(np.zeros((m,m))) for _ in range(ORDER+1)]
        te=I(np.zeros((m,m)))
        residual=targetM
        for dat,B,ii,sl,record,cap in zip(data,bases,inds,slices,self.records,self.captured):
            block_start=time.monotonic();block_cpu=time.process_time()
            require(np.array_equal(dat['raw'],np.swapaxes(dat['raw'],-1,-2)),'raw symmetry')
            N,_,_=cap
            free,active,V=check_partition(N,B,record)
            Jz,jden=self.prepare_J(record['change_of_basis'])
            for col in range(m+1):
                values=C.lo[sl,col] if col<m else w0[sl]
                H,Hmp=self.make_H(Jz,jden,values,ii)
                out=self.one_column(V,free,active,H,Hmp,dat,selected)
                if col<m:
                    for k in range(ORDER+1):tc[k][:,col:col+1]=tc[k][:,col:col+1]+out.c[k]
                    te[:,col:col+1]=te[:,col:col+1]+out.e
                else:
                    residual=residual.add(out.negative())
                self.column_count+=1
                if col%20==0 or col==m:
                    progress=dict(block=dat['name'],column=col,columns_per_block=m+1,
                                  total_block_columns=self.column_count,
                                  correction_seconds=time.monotonic()-start,
                                  block_seconds=time.monotonic()-block_start)
                    (self.output/'TRACE_PROGRESS.json').write_text(json.dumps(progress,indent=2)+'\n')
                    print('TRACE',json.dumps(progress),flush=True)
            self.stages.append(dict(block=dat['name'],wall_seconds=time.monotonic()-block_start,
                                    cpu_seconds=time.process_time()-block_cpu,
                                    columns=m+1,raw_dimension=len(free)+len(active),
                                    active_dimension=len(active),free_dimension=len(free)))
            (self.output/'TRACE_STAGES.json').write_text(json.dumps(self.stages,indent=2)+'\n')
        self.total_seconds=time.monotonic()-start
        self.total_cpu_seconds=time.process_time()-cpu
        return IP(tc,te),residual
