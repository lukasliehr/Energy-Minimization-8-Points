"""Joint exponent/height controls with complete structured residual errors.

Coefficient widths, center displacements and Gram remainders retain their
full coordinate box. Each Hermite remainder retains its complete bound on
its shared homogeneous power-sum direction. Every error is enclosed on
every closed piece; no right-inverse Taylor approximation is introduced.
"""
from fractions import Fraction as Q
import time

from exact_iv import iv, PRECISION
from AnalyticFinite.coefficient_module import simultaneous_corrections
from AnalyticFinite.bernstein_centers import power_to_bernstein
from AnalyticFinite.interval_correction import IntervalEvaluator
from AnalyticFinite.weighted_norm import weighted_bound


def split_controls(controls):
    """Exact de Casteljau restriction at the midpoint, in matching order."""
    if not controls:
        return [], []
    row = [list(q) for q in controls]
    left, right = [row[0]], [row[-1]]
    while len(row) > 1:
        row = [[(x+y)/2 for x,y in zip(a,b)] for a,b in zip(row,row[1:])]
        left.append(row[0]);right.append(row[-1])
    return left, right[::-1]


def dyadic_pieces(controls, depth):
    if type(depth) is not int or not 0 <= depth <= 8:
        raise ValueError('Invalid restriction depth')
    pieces = [(Q(-1), Q(1), controls)]
    for _ in range(depth):
        refined = []
        for lower, upper, values in pieces:
            left, right = split_controls(values)
            midpoint = (lower+upper)/2
            refined.extend(((lower,midpoint,left),(midpoint,upper,right)))
        pieces = refined
    return pieces


def height_ranges(model, depth, global_lower, global_upper):
    scale = 1 << PRECISION
    center = [[Q(q.lo+q.hi,2*scale)] for q in model.c]
    error = Q(model.e.hi,scale)+sum((Q(q.hi-q.lo,2*scale) for q in model.c),Q(0))
    controls = power_to_bernstein(center)
    answer=[]
    for lower,upper,piece in dyadic_pieces(controls,depth):
        lo=max(global_lower,min(row[0] for row in piece)-error)
        hi=min(global_upper,max(row[0] for row in piece)+error)
        if lo>hi:
            raise ArithmeticError('Disjoint proved height enclosures')
        answer.append((lower,upper,lo,hi))
    return answer


def centered_correction_bounds(apply, degree, exponents, coefficients,
                               residual_errors, pivots, block_names,
                               block_orders, left_metrics, evaluator,
                               retained_count=None, center_bits=None, *,
                               height_model, global_height, depth=2, exact_metrics=None,
                               exact_blocks=(), structured_errors=()):
    exponents=tuple(map(tuple,exponents))
    errors=list(map(Q,residual_errors))
    if len(errors)!=len(exponents) or any(q<0 for q in errors):
        raise ValueError('Invalid complete input errors')
    if set(block_names)!=set(left_metrics) or not coefficients:
        raise ValueError('Incomplete correction inputs')
    if retained_count is None:retained_count=len(coefficients)
    if type(retained_count) is not int or not 0<=retained_count<=len(coefficients):
        raise ValueError('Invalid retained count')
    if center_bits is not None and (type(center_bits) is not int or not 1<=center_bits<=PRECISION):
        raise ValueError('Invalid center precision')
    scale=1<<PRECISION;started=time.monotonic();centers=[]
    for k,C in enumerate(coefficients):
        row=[]
        for j in range(len(exponents)):
            value=C[j,0]
            if value.lo>value.hi:raise ValueError('Reversed coefficient')
            midpoint=Q(value.lo+value.hi,2*scale)
            center=midpoint
            if k<retained_count:
                if center_bits is not None:
                    center_scale=1<<center_bits
                    numerator=((value.lo+value.hi)*center_scale+scale)//(2*scale)
                    center=Q(numerator,center_scale)
                errors[j]+=Q(value.hi-value.lo,2*scale)+abs(midpoint-center)
                row.append(center)
            else:errors[j]+=Q(value.hi-value.lo,2*scale)+abs(midpoint)
        if k<retained_count:centers.append(row)
    nonzero_center_indices=[k for k,row in enumerate(centers) if any(row)]
    pieces=dyadic_pieces(power_to_bernstein(centers),depth)
    ranges=height_ranges(height_model,depth,*global_height)
    controls=[row for _,_,piece in pieces for row in piece]
    nonzero=[k for k,row in enumerate(controls) if any(row)]
    stamp=time.monotonic()
    compressed=simultaneous_corrections(apply,degree,exponents,[controls[k] for k in nonzero],pivots,
                                      temporal=(centers,depth)) if nonzero else []
    corrections=[{} for _ in controls]
    for k,correction in zip(nonzero,compressed):corrections[k]=correction
    generator_rows=[]
    generator_radii=[]
    for row,error in structured_errors:
        row=list(map(Q,row));error=Q(error)
        if len(row)!=len(exponents) or error<0:raise ValueError('Invalid correlated remainder')
        generator_rows.append(row);generator_radii.append(error)
    generator_corrections=simultaneous_corrections(apply,degree,exponents,generator_rows,pivots) if generator_rows else []
    contraction_seconds=time.monotonic()-stamp
    exact_blocks=tuple(exact_blocks)
    if len(set(exact_blocks))!=len(exact_blocks) or not set(exact_blocks)<=set(block_names):
        raise ValueError('Invalid exact congruence blocks')
    if bool(exact_blocks)!=(exact_metrics is not None):
        raise ValueError('Incomplete exact metric policy')
    if exact_metrics is not None:
        if set(exact_metrics)!=set(exact_blocks):raise ValueError('Wrong exact metric inventory')
    box={exponent:iv.mpf([-error,error]) for exponent,error in zip(exponents,errors)}
    piece_results=[];per_coefficient=[];evaluation_seconds=error_seconds=0.
    total_rationals=total_polynomials=total_inverses=0
    direct_counts=dict(shared_target_remainder_generators=len(generator_rows),exact_coefficient_congruences=0,sqrt2_polynomial_entries=0,
                       congruence_tensor_images=0,congruence_tensor_entries=0,
                       integer_polynomial_contractions=0,exact_height_numerator_coefficients=0,
                       metric_difference_control_enclosures=0,metric_difference_piece_enclosures=0,
                       metric_difference_matrix_products=0)
    metric_centers=[]
    if exact_blocks:
        from .matrix_congruence import metric_center
        metric_centers=[dict(block=name,**metric_center(exact_metrics[name])[-1]) for name in exact_blocks]
    for piece_number,((lower,upper,piece),(_,_,alo,ahi)) in enumerate(zip(pieces,ranges)):
        local=IntervalEvaluator(alo,ahi)
        totals={name:iv.matrix(block_orders[name],block_orders[name]) for name in block_names}
        piece_corrections=corrections[piece_number*retained_count:(piece_number+1)*retained_count]
        stamp=time.monotonic()
        evaluation_seconds+=time.monotonic()-stamp
        def transform(correction,exact):
            matrices={name:iv.matrix(block_orders[name],block_orders[name]) for name in block_names}
            for (name,i,j),value in correction.items():
                if name not in matrices or not 0<=i<=j<block_orders[name]:
                    raise ValueError('Unexpected analytic repair coordinate')
                if exact and name in exact_blocks:continue
                matrices[name][i,j]=matrices[name][j,i]=local.rational(value) if exact else value
            if exact and exact_blocks:
                from .matrix_congruence import exact_center_congruence_interval
                for name in exact_blocks:
                    matrices[name]=exact_center_congruence_interval(correction,name,block_orders[name],
                        exact_metrics[name],local,direct_counts)
            return {name:(M if exact and exact_metrics is not None and name in exact_blocks else
                          left_metrics[name]*M*left_metrics[name].T) for name,M in matrices.items()}
        def accumulate(matrices,maximum=False):
            bounds=[]
            for name in block_names:
                n,M=block_orders[name],matrices[name]
                bounds.append(weighted_bound(M))
                for i in range(n):
                    for j in range(n):
                        value=abs(M[i,j])
                        totals[name][i,j]=(iv.mpf(Q(max(totals[name][i,j].hi,value.hi),scale))
                                           if maximum else totals[name][i,j]+value)
            return bounds
        stamp=time.monotonic();control_bounds=[]
        for k in range(len(piece)):
            row=accumulate(transform(corrections[piece_number*retained_count+k],True),True)
            control_bounds.append(row);per_coefficient.append(row)
        evaluation_seconds+=time.monotonic()-stamp
        stamp=time.monotonic()
        error_correction=apply(degree,box,local.rational,pivots)
        for correction,error in zip(generator_corrections,generator_radii):
            interval=iv.mpf([-error,error])
            for key,value in correction.items():
                error_correction[key]=error_correction.get(key,iv.mpf(0))+local.rational(value)*interval
        error_bounds=accumulate(transform(error_correction,False))
        entrywise_bounds=[weighted_bound(totals[name]) for name in block_names]
        hull=[max((row[j] for row in control_bounds),default=Q(0)) for j in range(len(block_names))]
        bounds=[min(b,c+e) for b,c,e in zip(entrywise_bounds,hull,error_bounds)]
        error_bounds=[min(e,b) for e,b in zip(error_bounds,bounds)]
        error_seconds+=time.monotonic()-stamp
        piece_results.append(dict(t_interval=[str(lower),str(upper)],height_interval=[str(alo),str(ahi)],
                                  bounds=[str(q) for q in bounds],error_bounds=[str(q) for q in error_bounds],
                                  entrywise_bounds=[str(q) for q in entrywise_bounds],
                                  control_bounds=[str(q) for q in hull]))
        total_rationals+=len(local.rationals);total_polynomials+=len(local.polynomials);total_inverses+=len(local.inverses)
        print('Joint piece',piece_number,'t',[float(lower),float(upper)],'height',[float(alo),float(ahi)],
              'bounds',list(map(float,bounds)),'errors',list(map(float,error_bounds)),flush=True)
    bounds=[max(Q(piece['bounds'][j]) for piece in piece_results) for j in range(len(block_names))]
    errors=[max(Q(piece['error_bounds'][j]) for piece in piece_results) for j in range(len(block_names))]
    return dict(bounds=bounds,input_error_bounds=errors,coefficient_bounds=per_coefficient,
                seconds=time.monotonic()-started,retained_coefficient_count=retained_count,
                absorbed_coefficient_count=len(coefficients)-retained_count,
                nonzero_center_indices=nonzero_center_indices,exact_center_bits=center_bits,
                contraction_seconds=contraction_seconds,evaluation_seconds=evaluation_seconds,error_seconds=error_seconds,
                exact_congruence_blocks=list(exact_blocks),direct_congruence_counts=direct_counts,
                metric_centers=metric_centers,
                enclosure_basis='joint_t_height_bernstein_with_complete_structured_input_error',
                enclosure_degree=retained_count-1,enclosure_control_count=len(controls),
                enclosure_piece_count=len(pieces),distinct_rational_evaluations=total_rationals,
                distinct_polynomial_evaluations=total_polynomials,distinct_denominator_evaluations=total_inverses,
                pieces=piece_results)
