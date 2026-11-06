"""Fixed rational correction tables with exact integer cell contractions.

Tables are derived afresh from the established structural map, never accepted
from a disk cache. A full-run dispatcher may compile them before forking cell
workers; inherited tables then have the same checked source and exact content.
All canonical output functions, physical denominator checks, and error radii
remain those of the existing correction pipeline.
"""
from fractions import Fraction as Q
from math import lcm
import time
from flint import fmpq_poly, fmpz, fmpz_mat
from rational_field import R, divide_exact

_PLANS = {}
_RECORDS = []


def _rational(value):
    if isinstance(value,float):
        raise ValueError('Correction centres must be exact rationals')
    return Q(value)


def _key(apply,degree,exponents,pivots):
    return (apply,degree,tuple(map(tuple,exponents)),tuple(sorted(pivots.items())))


def _integers(rows):
    denominator=1
    for row in rows:
        for value in row:denominator=lcm(denominator,value.denominator)
    matrix=fmpz_mat([[int(row[j]*denominator)for row in rows]
                     for j in range(len(rows[0]))])
    return matrix,denominator


def _decode(plan,values,denominator,count):
    result=[{}for _ in range(count)]
    for coordinate,d,scale,length,positions in plan['specs']:
        for k in range(count):
            coefficients=[0]*length
            for power,row in positions:coefficients[power]=values[row,k]
            value=R(fmpq_poly(coefficients),0,d*(scale*denominator))
            if value:result[k][coordinate]=value
    return result


def _witness_work(plan,values,denominator,results):
    """Exact finite work for validating retained reduced output functions.

    D = d*g is fixed for every repeated denominator pattern. Then the retained
    output r=p/d satisfies N=(scale*input_denominator)*p*g. This equality is
    checked here and can be checked using integer polynomial arithmetic in Lean.
    GCD maximality is never a premise. Count p*g products separately from the
    fixed denominator factor identities and constant coefficient scalings.
    """
    patterns={};products=0;constant_slots=0;identities=0;zero_outputs=0
    for coordinate,d,scale,length,positions in plan['specs']:
        for k,result in enumerate(results):
            r=result.get(coordinate)
            if r is None:
                if any(values[row,k]for _,row in positions):
                    raise ArithmeticError('Missing nonzero fixed correction output')
                zero_outputs+=1
                continue
            if r.q:raise ArithmeticError('Rational correction unexpectedly has sqrt2 part')
            key=(tuple(d),tuple(r.d))
            if key not in patterns:
                factor=divide_exact(d,r.d)
                if r.d*factor!=d:raise ArithmeticError('Wrong fixed denominator quotient')
                patterns[key]=factor
            factor=patterns[key]
            poly=r.p*factor*(scale*denominator)
            coeffs=[0]*length
            for power,row in positions:coeffs[power]=values[row,k]
            if poly!=fmpq_poly(coeffs):raise ArithmeticError('Wrong integer correction output identity')
            identities+=1;products+=len(r.p)*len(factor);constant_slots+=len(poly)
    return dict(output_product_identities=identities,zero_output_identities=zero_outputs,
                output_polynomial_classical_products=products,
                output_constant_coefficient_scalings=constant_slots,
                distinct_denominator_quotient_identities=len(patterns),
                denominator_identity_classical_products=sum(len(a)*len(v)for (_,a),v in patterns.items()),
                maximum_denominator_quotient_degree=max((len(x)-1 for x in patterns.values()),default=0))


def compiled_plan(apply,degree,exponents,pivots):
    """Derive one source-bound map; the result is treated as immutable."""
    key=_key(apply,degree,exponents,pivots)
    if key in _PLANS:return _PLANS[key]
    from .coefficient_module import structural_simultaneous_corrections
    from invariant_raw import power_sum
    start=time.monotonic();n=len(exponents)
    if not n or len(set(map(tuple,exponents)))!=n:
        raise ValueError('Invalid fixed correction coordinate inventory')
    columns=structural_simultaneous_corrections(apply,degree,exponents,
        [[Q(int(i==j))for j in range(n)]for i in range(n)],pivots)
    coordinates=sorted(set().union(*(c.keys()for c in columns)))
    flat=[];specs=[];nonzero=0;max_bits=0
    denominator_factors={}
    for coordinate in coordinates:
        values=[column.get(coordinate,R())for column in columns]
        if any(v.q for v in values):raise ArithmeticError('Fixed correction rational descent failed')
        denominator=fmpq_poly([1])
        for value in values:denominator*=divide_exact(value.d,denominator.gcd(value.d))
        numerator=[]
        for value in values:
            factor=divide_exact(denominator,value.d)
            if value.d*factor!=denominator:raise ArithmeticError('Invalid fixed operator denominator')
            numerator.append(value.p*factor)
            denominator_factors[(tuple(denominator),tuple(value.d))]=factor
        scale=fmpz(1)
        for value in numerator:scale=scale.lcm(value.denom())
        integer=[value.numer()*(scale//value.denom())for value in numerator]
        length=max(map(len,integer),default=0);positions=[]
        for power in range(length):
            row=[int(value[power])for value in integer]
            if any(row):
                positions.append((power,len(flat)));flat.append(row)
                nonzero+=sum(bool(q)for q in row)
                max_bits=max(max_bits,max(abs(q).bit_length()for q in row))
        # Verify every compiled column coefficient identity explicitly. There is
        # no reliance on a sampled comparison or on a preexisting table receipt.
        for value,whole in zip(numerator,integer):
            if fmpq_poly(whole)!=value*scale:
                raise ArithmeticError('Invalid integer operator coefficient clearing')
        specs.append((coordinate,denominator,int(scale),length,tuple(positions)))
    plan=dict(matrix=fmpz_mat(flat),specs=tuple(specs),
              nonzero_coefficients=nonzero,key=key)
    directions=tuple(tuple(Q(power_sum(k).get(tuple(e),0),3)for e in exponents)
                     for k in range(2*degree+1))
    directions=tuple(row for row in directions if any(row))
    if len(directions)!=2*degree:raise ArithmeticError('Incomplete fixed Hermite directions')
    integer,den=_integers(directions)
    images=plan['matrix']*integer
    shared=_decode(plan,images,den,len(directions))
    shared_work=_witness_work(plan,images,den,shared)
    plan['directions']=directions;plan['shared_images']=shared
    plan['record']=dict(degree=2*degree,input_coordinates=n,output_coordinates=len(specs),
        flat_numerator_rows=len(flat),nonzero_integer_coefficients=nonzero,
        dense_integer_coefficients=len(flat)*n,max_integer_coefficient_bits=max_bits,
        max_numerator_degree=max(s[3]-1 for s in specs),max_denominator_degree=max(len(s[1])-1 for s in specs),
        fixed_column_coefficient_identities=len(specs)*n,
        distinct_fixed_denominator_quotients=len(denominator_factors),
        shared_direction_count=len(directions),shared_direction_dense_products=len(flat)*n*len(directions),
        shared_direction_sparse_products=nonzero*len(directions),shared_direction_output_work=shared_work,
        setup_seconds=time.monotonic()-start)
    _PLANS[key]=plan
    _RECORDS.append(dict(event='fresh_fixed_plan',**plan['record']))
    return plan


def contract_numerators(plan,centers,temporal=None):
    """Return exact flat integer numerators, common input scale, and work counts."""
    matrix,den=_integers(centers);H=plan['matrix'];mode='direct'
    direct=plan['nonzero_coefficients']*len(centers)
    dense=H.nrows()*H.ncols()*len(centers);work=direct
    if temporal is not None:
        from .bernstein_centers import power_to_bernstein
        from .joint_correction import dyadic_pieces
        powers,depth=temporal
        powers=tuple(tuple(_rational(q)for q in row)for row in powers)
        active=[k for k,row in enumerate(powers)if any(row)]
        unit=[[Q(int(i==j))for j in range(len(powers))]for i in range(len(powers))]
        transform=[row for _,_,piece in dyadic_pieces(power_to_bernstein(unit),depth)for row in piece]
        expected=[row for _,_,piece in dyadic_pieces(power_to_bernstein(powers),depth)for row in piece]
        selected=[i for i,row in enumerate(expected)if any(row)]
        if tuple(tuple(row)for row in expected if any(row))!=centers:
            raise ArithmeticError('Incorrect temporal correction controls')
        T=[[transform[i][k]for k in active]for i in selected]
        factored=plan['nonzero_coefficients']*len(active)+H.nrows()*sum(bool(q)for row in T for q in row)
        if active and factored<direct:
            P,pden=_integers([powers[k]for k in active]);Ti,tden=_integers(T)
            values=(H*P)*Ti;den=pden*tden;mode='power_then_temporal';work=factored
            dense=H.nrows()*H.ncols()*len(active)+H.nrows()*len(active)*len(centers)
        else:values=H*matrix
    else:values=H*matrix
    return values,den,dict(association=mode,dense_integer_products=dense,
                            sparse_integer_products=work,input_common_denominator_bits=den.bit_length())


def simultaneous_corrections(apply,degree,exponents,centers,pivots,*,temporal=None):
    centers=tuple(tuple(_rational(q)for q in row)for row in centers)
    if not centers or any(len(row)!=len(exponents)for row in centers):
        raise ValueError('Invalid exact coefficient rectangle')
    start=time.monotonic();plan=compiled_plan(apply,degree,exponents,pivots)
    if centers==plan['directions']:
        _RECORDS.append(dict(event='shared_Hermite_images',degree=2*degree,rows=len(centers),seconds=time.monotonic()-start))
        return [dict(correction)for correction in plan['shared_images']]
    values,den,record=contract_numerators(plan,centers,temporal)
    result=_decode(plan,values,den,len(centers))
    witness=_witness_work(plan,values,den,result)
    _RECORDS.append(dict(event='integer_center_contraction',degree=2*degree,rows=len(centers),
                          seconds=time.monotonic()-start,**record,**witness))
    return result


def computation_records():
    return [dict(record)for record in _RECORDS]


def clear_computation_records():
    _RECORDS.clear()
