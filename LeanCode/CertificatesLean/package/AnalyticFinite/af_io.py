"""Strict stdlib IO and immutable source binding for analytic finite replays."""
import hashlib,json,re
from pathlib import Path


def require(condition,message):
    if not condition:raise ValueError(message)


def read(path):
    def pairs(items):
        out={}
        for k,v in items:
            require(k not in out,'Duplicate JSON key: '+k);out[k]=v
        return out
    def invalid(x):raise ValueError('Nonfinite JSON value: '+x)
    return json.loads(Path(path).read_text(),object_pairs_hook=pairs,parse_constant=invalid)


def write(path,value):Path(path).write_text(json.dumps(value,indent=2,allow_nan=False)+'\n')


def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb')as f:
        for b in iter(lambda:f.read(1<<20),b''):h.update(b)
    return h.hexdigest()


def bound_path(root,name):
    require(isinstance(name,str),'Path must be a string');p=Path(name)
    require(not p.is_absolute()and '..'not in p.parts,'Unsafe relative path')
    q=root/p;require(not q.is_symlink(),'Symlink input is forbidden');q=q.resolve()
    require(q.is_relative_to(root),'Input path escapes root');return q


def source_bindings(root):
    p=root/'AnalyticFinite/source_bindings.json';manifest=read(p)
    require(manifest.get('schema')=='thomson-analytic-finite-source-bindings-v1','Wrong source-binding schema')
    expected=manifest['files']
    actual={str(f.relative_to(root)):sha(f)for folder in('Finite','SymmetricFinite','AnalyticFinite')for f in sorted((root/folder).rglob('*.py'))if f.is_file()}
    require(actual==expected,'Numerical source inventory mismatch')
    for name in actual:bound_path(root,name)
    return p,actual


def indexed_entry(root,name):
    index=read(root/'AnalyticFinite/INDEX.json')
    require(index.get('schema')=='thomson-analytic-finite-index-v1','Wrong analytic index schema')
    entries=index['cells'];require(isinstance(entries,list)and len(entries)==30,'Expected30 finite cells')
    ids=[e['cell']['id']for e in entries]
    require(len(set(ids))==30 and all(isinstance(x,str)and re.fullmatch(r'[A-Za-z0-9_-]+',x)for x in ids),'Invalid cell IDs')
    require(name in ids,'Unknown cell');entry=entries[ids.index(name)];manifest=read(bound_path(root,entry['proposal']))
    require(manifest.get('schema')=='thomson-analytic-finite-cell-manifest-v1','Wrong cell manifest schema')
    require(manifest['cell']==entry['cell']and manifest['validation_orders']==entry['validation_orders'],'Manifest/index parameter drift')
    orders=entry['validation_orders'];require(isinstance(orders,list)and len(orders)>0 and orders==sorted(set(orders))and all(type(x)is int and 4<=x<=34 for x in orders),'Invalid allowed validation orders')
    return entry,manifest
