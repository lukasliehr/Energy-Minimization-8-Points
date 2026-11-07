"""High precision coefficients of the same direct residual, with retained tail.

Only pivot rows of each canonical kernel basis vary. Exact fixed-dyadic
interval matrix products form pivot/free and pivot/pivot entries; free/free
entries are the proposed dyadics themselves. The separately established
uniform Taylor remainder is unchanged.
"""
from taylor_models import TM,iv,ORDER
from analytic_basis import moment_kernel_row
from kernels import Evaluator,symbolic_kernels
import numpy as np
from flint import fmpz_mat
from exact_iv import D, SCALE, ceildiv


def polynomial_matrix_product(left,right,order):
    if not left or not right or order<0:
        raise ValueError('Empty polynomial matrix product')
    m,n,p=left[0].rows,left[0].cols,right[0].cols
    if any((C.rows,C.cols)!=(m,n)for C in left)or any((C.rows,C.cols)!=(n,p)for C in right):
        raise ValueError('Inconsistent polynomial matrix dimensions')
    def prepare(poly):
        mids=[[int(x.lo+x.hi)for x in C.data]for C in poly[:order+1]]
        radii=[[int(x.hi-x.lo)for x in C.data]for C in poly[:order+1]]
        if any(r<0 for row in radii for r in row):raise ValueError('Reversed coefficient interval')
        while len(mids)>1 and not any(mids[-1])and not any(radii[-1]):
            mids.pop();radii.pop()
        return mids,radii,max((abs(x)for row in mids for x in row),default=0),max((x for row in radii for x in row),default=0)
    am,ar,amx,arx=prepare(left);bm,br,bmx,brx=prepare(right)
    terms=n*min(len(am),len(bm))
    center_bound=terms*amx*bmx
    radius_bound=terms*(amx*brx+arx*bmx+arx*brx)
    cbits=max(1,(2*center_bound).bit_length());rbits=max(1,(2*radius_bound).bit_length())
    cbase,rbase=1<<cbits,1<<rbits;chalf,rhalf=cbase//2,rbase//2
    def pack(poly,rows,cols,bits,absolute=False):
        values=[0]*(rows*cols)
        for row in reversed(poly):
            values=[(word<<bits)+(abs(x)if absolute else x)for word,x in zip(values,row)]
        return fmpz_mat(rows,cols,values)
    center=fmpz_mat(m,p);radius=fmpz_mat(m,p);center_products=0;radius_products=0;enc_c=0;enc_r=0
    if amx and bmx:
        center=pack(am,m,n,cbits)*pack(bm,n,p,cbits);center_products=1
        enc_c=len(am)*m*n+len(bm)*n*p
    ra=pack(ar,m,n,rbits)if arx and(bmx or brx)else None
    rb=pack(br,n,p,rbits)if brx and(amx or arx)else None
    if ra is not None:enc_r+=len(ar)*m*n
    if rb is not None:enc_r+=len(br)*n*p
    if amx and brx:
        radius+=pack(am,m,n,rbits,True)*rb;radius_products+=1;enc_r+=len(am)*m*n
    if arx and bmx:
        radius+=ra*pack(bm,n,p,rbits,True);radius_products+=1;enc_r+=len(bm)*n*p
    if arx and brx:radius+=ra*rb;radius_products+=1
    cw=[int(x)for x in center.entries()];rw=[int(x)for x in radius.entries()]
    out=[];den=4*SCALE
    for k in range(order+1):
        cm=[(x+chalf)%cbase-chalf for x in cw]
        rr=[(x+rhalf)%rbase-rhalf for x in rw]
        if any(x<0 for x in rr):raise ArithmeticError('Negative decoded radius')
        C=iv.matrix(m,p)
        C.data=[D.raw((x-r)//den,ceildiv(x+r,den))for x,r in zip(cm,rr)]
        out.append(C)
        cw=[(x-r)//cbase for x,r in zip(cw,cm)]
        rw=[(x-r)//rbase for x,r in zip(rw,rr)]
    return out


def coefficient_residual(data,records,A,gram_values,target):
    residual=[iv.matrix(c)for c in target.c]
    evaluator=Evaluator(A)
    for dat,record,values in zip(data,records,gram_values):
        free=record['free'];n=len(free);name=dat['name']
        if name.startswith('F'):
            active=[record['pivot']]
            p=[moment_kernel_row(A,dat['k'],active[0],free,lambda x,y:TM.const(iv.mpf(x)/y))]
        else:
            if name.startswith('M0_'):kind,base='s3','M0'
            elif name.startswith('Mdet_'):kind,base='s3','Mdet'
            else:kind,base='s2','M1'
            # Polynomial degree is part of each exact raw-data descriptor.
            import structure as structure
            d=structure.D-(0 if base=='M0'else 2 if base=='Mdet'else 1)
            group={'plus':0,'sign':1,'standard':2,'even':0,'odd':1}[name.split('_')[1]]
            active=record['pivots'];symbolic=symbolic_kernels(kind,d)[group]
            p=[[evaluator.rational(symbolic[i][j])for j in range(n)]for i in active]
        pc=[iv.matrix([[t.c[k]for t in row]for row in p])for k in range(ORDER+1)]
        wc=[iv.matrix([[iv.mpf(x)for x in row]for row in val])for val in values]
        wc+= [iv.matrix(n,n)for _ in range(ORDER+1-len(wc))]
        q=len(active)
        bw=polynomial_matrix_product(pc,wc,ORDER)
        pp=polynomial_matrix_product(bw,[C.T for C in pc],ORDER)
        free_at={i:j for j,i in enumerate(free)};pivot_at={i:j for j,i in enumerate(active)}
        # Each raw symmetric tensor gives the coefficient of trace(raw*K)/den.
        entries=[]
        for row,raw in enumerate(dat['raw']):
            ii,jj=np.nonzero(raw)
            entries.append([(int(i),int(j),int(raw[i,j]))for i,j in zip(ii,jj)])
        for k in range(ORDER+1):
            def entry(i,j):
                if i in free_at and j in free_at:return wc[k][free_at[i],free_at[j]]
                if i in pivot_at and j in free_at:return bw[k][pivot_at[i],free_at[j]]
                if i in free_at and j in pivot_at:return bw[k][pivot_at[j],free_at[i]]
                return pp[k][pivot_at[i],pivot_at[j]]
            for row,es in enumerate(entries):
                val=sum((c*entry(i,j)for i,j,c in es),iv.mpf(0))/dat['den']
                residual[k][row,0]-=val
        print('Precise direct residual block',name,flush=True)
    return residual
