"""Contracts for independent, symmetry-compressed finite certificates."""
import math
import contracts as legacy
from contracts import require,vector,parameters,rational,finite,read_json


def matrix(value,rows,columns):
    return isinstance(value,list) and len(value)==rows and all(vector(row,columns) for row in value)


def dimensions(cell):
    base=legacy.dimensions(cell)
    d=cell['degree']//2
    names=[f'F{k}' for k in range(d)];orders=list(range(d,0,-1));pivots=[1]*d
    def group(n,sym,prefix):
        m=math.comb(n+3,3);t=sum(n-2*j+1 for j in range(n//2+1));c=n//3+1
        if sym=='s3':
            sizes=[(m+3*t+2*c)//6-5,(m-3*t+2*c)//6-2,(m-c)//3-7]
            labels=['plus','sign','standard'];ps=[5,2,7]
        else:
            sizes=[(m+t)//2-12,(m-t)//2-9];labels=['even','odd'];ps=[12,9]
        for size,label,pivot in zip(sizes,labels,ps):
            require(size>=0,'Negative kernel multiplicity')
            if size:names.append(prefix+'_'+label);orders.append(size);pivots.append(pivot)
    group(d,'s3','M0');group(d-1,'s2','M1');group(d-2,'s3','Mdet')
    return dict(orders=orders,block_names=names,kernel_pivot_counts=pivots,
        coefficient_rows=base['coefficient_rows'],retained_rows=base['retained_rows'],
        svec_dimension=sum(n*(n+1)//2 for n in orders),
        legacy_svec_dimension=base['svec_dimension'])


def witness_audit(data,cell,dims):
    from canonical import basis
    require(data.get('schema')=='thomson-symmetric-gram-witness-v1','Wrong witness schema')
    require(data.get('degree')==cell['degree'],'Wrong witness degree')
    orders=dims['orders'];records=data['basis_records'];d=cell['degree']//2
    require([r['name'] for r in records]==dims['block_names'],'Wrong symmetric block order')
    require([len(r['free']) for r in records]==orders,'Wrong kernel orders')
    require(all(matrix(r['change_of_basis'],n,n) for r,n in zip(records,orders)),
            'Invalid dyadic basis changes')
    for k,r in enumerate(records[:d]):
        n=d-k+1;p=r['pivot']
        require(type(p) is int and 0<=p<n and r['free']==[j for j in range(n) if j!=p],
                'Invalid moment partition')
    idx=d
    for kind,n in [('s3',d),('s2',d-1),('s3',d-2)]:
        desc=basis(kind,n)
        for group in range(3 if kind=='s3' else 2):
            if not desc['frees'][group]:continue
            r=records[idx];idx+=1
            require(r['free']==desc['frees'][group] and r['pivots']==desc['pivots'][group],
                    'Kernel differs from proved scalar interpolation')
    ps=data['PSD_preconditioners']
    require(len(ps)==len(orders) and all(matrix(p,n,n) for p,n in zip(ps,orders)),
            'Invalid PSD preconditioners')
    n,m=dims['svec_dimension'],dims['retained_rows']
    require(vector(data['svec_center'],n),'Invalid Gram center')
    if 'correction_recipe' in data:
        recipe=data['correction_recipe']
        require('right_inverse' not in data and 'left_preconditioner' not in data,
                'Compact recipe determines the correction matrices')
        require(recipe.get('kind')=='symmetric_reference_active_coefficient_transpose_v1','Unknown compact recipe')
        require(matrix(recipe['right_factor'],m,m),'Invalid compact right factor')
        refs=recipe['reference_active_rows']
        require(isinstance(refs,list) and len(refs)==len(orders) and
                all(matrix(A,p,n) for A,p,n in zip(refs,dims['kernel_pivot_counts'],orders)),
                'Invalid compact active reference rows')
        left=True
    else:
        require(matrix(data['right_inverse'],n,m),'Invalid correction matrix')
        left=data.get('left_preconditioner')
        require(left is None or matrix(left,m,m),'Invalid left preconditioner')
    rows=data['rows']
    require(isinstance(rows,list) and len(rows)==m and len(set(rows))==m
        and all(type(j) is int and 0<=j<dims['coefficient_rows'] for j in rows),'Invalid selected rows')
    if cell['profile']=='general':
        tags=data['auxiliary_nodes']
        require(isinstance(tags,list) and len(tags)==d-4 and all(t in 'ABCD' and len(t)==1 for t in tags),'Invalid Hermite tags')
    else:tags={'original':[],'far4':['B','D'],'far6':['B','B']}[cell['profile']]
    mult={t:2+2*tags.count(t) for t in 'ABCD'}
    mult['minus_one']=5 if cell['profile']=='original' else 1
    require(sum(mult.values())==cell['degree']+1,'Wrong Hermite dimension')
    return dict(auxiliary_nodes=tags,hermite_multiplicities=mult,left_preconditioned=left is not None)


def report_audit(path,cell,dims,metadata):
    report=read_json(path)
    bounds=legacy.report_audit(path,cell,dims,metadata)
    require(report.get('analytic_symmetry_theorem')=='thm:active-symmetric-grams','Missing symmetry proof identifier')
    for key in ['block_names','block_orders','kernel_pivot_counts']:
        expected=dims['orders'] if key=='block_orders' else dims[key]
        require(report.get(key)==expected,'Wrong reduced report '+key)
    counts=report['PSD_subdivision_counts'];errors=report['PSD_subdivision_errors']
    require(len(counts)==len(dims['orders']) and len(errors)==len(counts),'Incomplete PSD subinterval coverage')
    for n,ee,bound in zip(counts,errors,report['PSD_uniform_errors']):
        require(type(n) is int and n in [1,2,4,8] and isinstance(ee,list) and len(ee)==n
                and all(finite(e) and 0<=e<1 for e in ee) and max(ee)==bound,
                'Invalid equal-dyadic PSD subinterval bounds')
    return bounds
