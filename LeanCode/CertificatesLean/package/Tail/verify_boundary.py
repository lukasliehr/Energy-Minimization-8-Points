"""Exact D8-reduced quartic boundary certificate.

The explicit Fourier/dihedral basis and invariant correction theorem are
proved in the accompanying paper. Gram positivity follows analytically from arbitrary square factors and a
fixed positive free floor. Geometry and residual coefficients use exact rational-pair arithmetic in Q(sqrt2). Only the invariant quartic residual bound is
a computational premise of this verifier.
"""
from pathlib import Path
import argparse,hashlib,json,sys,time
from math import comb
HERE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(HERE))
from fractions import Fraction as F
from exact_geometry import geometry
from dihedral_basis import K,polynomial_basis
from invariant_basis import extraction_map
from edge_basis import edge_features


def require(value,message):
    if not value:raise ValueError(message)


def read(path):
    def unique(items):
        out={}
        for key,value in items:
            require(key not in out,'duplicate JSON key');out[key]=value
        return out
    return json.loads(Path(path).read_text(),object_pairs_hook=unique,
                      parse_constant=lambda c:(_ for _ in ()).throw(ValueError(c)))


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def imul(A,B):return [[sum(x*y for x,y in zip(ar,bc))for bc in zip(*B)]for ar in A]


def unpack(record,n):
    require(type(record['dimension']) is int and record['dimension']==n,'factor dimension')
    nums=record['factor_lower']
    require(isinstance(nums,list) and len(nums)==n*(n+1)//2,'triangular factor length')
    require(all(type(x) is int for x in nums),'integer factor entries')
    L=[[0]*n for _ in range(n)];at=0
    for i in range(n):
        for j in range(i+1):L[i][j]=nums[at];at+=1
    return L


def gram_poly(Q,rows):
    out={}
    for i,p in enumerate(rows):
        for j,q in enumerate(rows):
            c=Q[i][j]
            if not c:continue
            for u,x in p.items():
                for v,y in q.items():
                    mon=tuple(sorted(u+v));out[mon]=out.get(mon,K())+c*x*y
    return {m:c for m,c in out.items() if c}


def add_poly(out,p):
    for mon,c in p.items():out[mon]=out.get(mon,K())+c


def validate(rec):
    require(rec['kind']=='quadratic_field_dihedral_factors_gnomonic_boundary','witness kind')
    require(rec['polynomial_basis']=='analytic-real-fourier-dihedral-polynomial-v1','polynomial basis')
    require(rec['edge_basis']=='explicit-stabilizer-parity-v1','edge basis')
    b=F(rec['b']);rho=F(rec['rho']);higher=F(rec['higher']);lower=F(rec['annulus_lower']);den=rec['denominator']
    require(b==F(33,1000) and rho==F(61,200) and higher==b/2 and lower==F(3620,3721),'gnomonic constants')
    require(rec['alignment_product']=='239/250' and rec['chord_localization_radius']=='3/10','geometry interpretation constants')
    require(type(den) is int and den>0,'positive integer denominator')
    alpha=F(rec['free_floor']);require(alpha==F(1,10**7),'fixed positive free floor')
    require(rec['slice_basis']=='rationalized-fourier-slice-v1','rationalized slice basis')
    g=geometry()
    # A degree<=4 monomial has a canonical split into two degree<=2
    # monomials.  The analytic symmetric lift needs no representation
    # counts or enumeration of the ordinary polynomial space.
    free_dimension=comb(15,2)
    polynomial_dimension=comb(17,4)
    bases={d:polynomial_basis(d)for d in (1,2)}
    expected=[(label+'/'+name,len(copies[0]))for label,d in [('free',2),('upper',1),('lower',1)]for name,copies in bases[d]]+[(f'edge/{d}/{parity}',len(rows))for d in (1,2)for parity,rows in edge_features(d)]
    require(isinstance(rec['blocks'],list) and len(rec['blocks'])==len(expected),'block count')
    Qs={}
    for record,(name,n) in zip(rec['blocks'],expected):
        require(record['name']==name,'block order/name')
        L=unpack(record,n)
        LL=imul(L,list(map(list,zip(*L))))
        floor=alpha if name.startswith('free/')else F(0)
        Qs[name]=[[K(F(LL[i][j],den*den)+(floor if i==j else 0))for j in range(n)]for i in range(n)]
    sums={}
    for label,d in [('free',2),('upper',1),('lower',1)]:
        pol={}
        for name,copies in bases[d]:
            for rows in copies:add_poly(pol,gram_poly(Qs[label+'/'+name],rows))
        sums[label]=pol
    edge_representatives={}
    for d in (1,2):
        pol={}
        for parity,rows in edge_features(d):add_poly(pol,gram_poly(Qs[f'edge/{d}/{parity}'],rows))
        edge_representatives[d]=pol
    invariants,extract=extraction_map()
    # Exact rational pairs throughout: K(a,b)=a+b*sqrt(2).
    residual=[K() for _ in invariants]
    for j,c in extract[()]:residual[j]-=c

    def subtract_product(p,q,multiplicity=1):
        for u,c in p.items():
            for v,d in q.items():
                for j,x in extract.get(tuple(sorted(u+v)),[]):
                    residual[j]-=multiplicity*c*d*x

    subtract_product(sums['free'],{():K(1)})
    subtract_product(sums['upper'],{():K(1),**{(i,i):-w for i,w in enumerate(g['weights'])}})
    subtract_product(sums['lower'],{():K(-lower),**{(i,i):w for i,w in enumerate(g['weights'])}})
    for e,edge in enumerate(g['edges']):
        pol={():K(b)}
        pol.update({(i,):rho*g['R'][e][i] for i in range(13)})
        pol.update({(i,j):rho*rho*(g['M'][e][i][j]+higher*g['T'][e][i][j])*(1 if i==j else 2)
                    for i in range(13) for j in range(i,13)})
        subtract_product(edge_representatives[edge[1]],pol,8)
    # Algebraic norm preserves cancellation without any precise root bound.
    # For opposite signs, |u-v*sqrt2|=|u|+sqrt2*|v| >= |u|+|v|.
    # Otherwise the elementary sqrt2<3/2 bound suffices.
    def majorant(c):
        u,v=c.a,c.b
        return abs(u*u-2*v*v)/(abs(u)+abs(v)) if u*v<0 else abs(u)+F(3,2)*abs(v)
    coordinate_bounds=[majorant(c) for c in residual]
    coefficient_bounds={}
    for bound,(row,norm)in zip(coordinate_bounds,invariants):
        for mon,c in row.items():
            # sqrt2<3/2 is proved once in the text; no sign test on K is needed.
            coefficient_bounds[mon]=coefficient_bounds.get(mon,F(0))+bound*(abs(c.a)+F(3,2)*abs(c.b))
    # Canonical symmetric lift: put each coefficient on its canonical
    # diagonal, or half on each of its two symmetric off-diagonal entries.
    # Every entry is bounded by this coefficient majorant.  Conversion to
    # the weighted monomial frame and orthogonal D8 averaging do not
    # increase the analytic free-matrix norm bound.
    entry=max(coefficient_bounds.values())
    spectral_correction=free_dimension*entry
    require(spectral_correction<alpha,'invariant residual below the analytic positive floor')
    return dict(status='PASS_EXACT_QUADRATIC_FIELD_BOUNDARY',gap=str(b),normalization_radius=str(rho),annulus_lower=str(lower),higher=str(higher),variables=13,slice_basis=rec['slice_basis'],polynomial_basis=rec['polynomial_basis'],edge_basis=rec['edge_basis'],symmetry_group='D8_order_16',contact_polynomials_constructed=2,edge_orbit_products=2,edge_orbit_multiplicity=8,basis_matrix_inversions=0,gram_schmidt_steps=0,coefficient_identity_count=len(invariants),full_polynomial_dimension=polynomial_dimension,invariant_coefficient_basis='unitary-fourier-monomials-v1',block_dimensions=dict(expected),factor_coordinates=sum(n*(n+1)//2 for _,n in expected),Gram_positivity_predicates=0,preconditioner_coordinates=0,free_floor=str(alpha),coefficient_correction_entry_bound=str(entry),spectral_correction_bound=str(spectral_correction),free_correction_ratio=str(spectral_correction/alpha),exact_coefficient_field='Q(sqrt2)',geometry_root_enclosures=0,outward_interval_operations=0,high_precision_root_bounds=0,coefficient_majorant='quadratic_norm_identity',coefficient_lift='canonical_symmetric_monomial_split',lift_representation_counts=0,quartic_pair_count_operations=0,exact_residual_coordinates=[[str(c.a),str(c.b)] for c in residual],invariant_coordinate_bounds=[str(v) for v in coordinate_bounds],global_localization_established_by_this_program=False,conclusion='No real y in the stated weighted annulus satisfies all16 gnomonic contact quadratics. Positivity follows analytically from the explicit square factors and fixed free floor; the coefficients are computed exactly in Q(sqrt2), and only their rational residual comparison remains computational. The geometric localization proof is separate.')


def main():
    parser=argparse.ArgumentParser();parser.add_argument('witness',type=Path);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    require(__debug__ and not sys.flags.optimize,'run without -O')
    start=time.monotonic();out=validate(read(args.witness))
    out.update(witness_sha256=sha(args.witness),source_sha256={p.name:sha(p)for p in [Path(__file__).resolve(),HERE/'dihedral_basis.py',HERE/'invariant_basis.py',HERE/'edge_basis.py',HERE/'exact_geometry.py']},seconds=time.monotonic()-start)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:out[k]for k in ['status','factor_coordinates','free_correction_ratio','seconds']},indent=2),flush=True)
if __name__=='__main__':main()
