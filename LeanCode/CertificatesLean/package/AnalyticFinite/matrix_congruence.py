"""Cached exact symmetric images, with complete piecewise metric discrepancy.

The metric acts on fixed symmetric coordinate images once.  Sparse input polynomials are translated before contraction.
Nine rounded dyadic low rows and one complete nonnegative tail row
replace the full output polynomial.  Every high coefficient and rounding
error is retained.  Height-independent entries are reassembled before
Horner evaluation.  All three metric-discrepancy terms remain included.
"""
from flint import fmpq,fmpq_mat,fmpq_poly,fmpz_mat,fmpz
from rational_field import divide_exact
from exact_iv import D,iv,PRECISION
from AnalyticFinite.interval_correction import rational_interval
from AnalyticFinite.joint_contracts import HEIGHT_JET_DEGREE,HEIGHT_JET_BITS


_IMAGES={}


def _count(counts,key,value):
    if counts is not None:counts[key]=counts.get(key,0)+value


def integer_images(Z,coordinates,counts=None):
    n=Z.nrows()
    key=(n,tuple(Z[i,j] for i in range(n) for j in range(n)),coordinates)
    if key not in _IMAGES:
        U,denominator=Z.numer_denom()
        output=tuple((i,j) for i in range(n) for j in range(i,n))
        tensor=fmpz_mat([[U[i,u]*U[j,v]+(U[i,v]*U[j,u] if u!=v else 0)
                         for i,j in output] for u,v in coordinates])
        _IMAGES[key]=(tensor,denominator**2,output)
        _count(counts,'congruence_tensor_images',len(coordinates))
        _count(counts,'congruence_tensor_entries',len(coordinates)*len(output))
    return _IMAGES[key]


def _tail_bound(poly, cutoff, rho):
    """Upper bound for sum_{k>cutoff} p_k*x^k, for |x|<=rho."""
    value = fmpq(0)
    for coefficient in reversed(tuple(poly)[cutoff + 1:]):
        value = value * rho + abs(coefficient)
    return value * rho ** (cutoff + 1)

def exact_center_congruence_interval(correction, name, n, Z, evaluator, counts=None):
    if Z.nrows() != n or Z.ncols() != n:
        raise ValueError('Wrong exact metric dimensions')
    if type(HEIGHT_JET_DEGREE) is not int or HEIGHT_JET_DEGREE < 0:
        raise ValueError('Invalid exact height cutoff')
    if type(HEIGHT_JET_BITS) is not int or HEIGHT_JET_BITS < 0:
        raise ValueError('Invalid translated-jet precision')
    entries = {(i, j): r for (block, i, j), r in correction.items() if block == name and r}
    if not entries:
        return iv.matrix(n, n)
    if any((not 0 <= i <= j < n for i, j in entries)):
        raise ValueError('Invalid symmetric correction coordinate')
    denominator = fmpq_poly([1])
    for r in entries.values():
        denominator *= divide_exact(r.d, denominator.gcd(r.d))
    numerator = {}
    constants = {}
    for key, r in entries.items():
        if max(len(r.p), len(r.q), len(r.d)) <= 1:
            constants[key] = (r.p[0] / r.d[0], r.q[0] / r.d[0])
            continue
        factor = divide_exact(denominator, r.d)
        numerator[key] = (r.p * factor, r.q * factor if r.q else fmpq_poly())
    inverse = evaluator.inverse(denominator)
    coordinates = tuple(sorted(numerator))
    constant_coordinates = tuple(sorted(constants))
    if coordinates:
        tensor, metric_denominator, output = integer_images(Z, coordinates, counts)
    if constant_coordinates:
        constant_tensor, constant_metric_denominator, output = integer_images(Z, constant_coordinates, counts)
    raw_radius = max(abs(evaluator.variable.lo), abs(evaluator.variable.hi))
    rho = fmpq(1 << (raw_radius - 1).bit_length(), 1 << PRECISION) if raw_radius else fmpq(0)
    den_shift = denominator(evaluator.shift)
    den_tail = _tail_bound(den_shift, HEIGHT_JET_DEGREE, rho)
    components = []
    for part in (0, 1):
        length = max((len(pair[part]) for pair in numerator.values()), default=0)
        if counts is not None:
            _count(counts, 'exact_height_numerator_coefficients', length)
            if part:
                counts['sqrt2_polynomial_entries'] += sum((bool(r.q) for r in entries.values()))
        value = iv.matrix(n, n)
        constant_values = None
        low = None
        tail_values = None
        if constant_coordinates and any((constants[key][part] for key in constant_coordinates)):
            vector = fmpq_mat([[constants[key][part] for key in constant_coordinates]])
            cn, cd = vector.numer_denom()
            constant_values = cn * constant_tensor
            _count(counts, 'integer_polynomial_contractions', 1)
            constant_denominator = cd * constant_metric_denominator
        used = 0
        tails = []
        if length:
            common = fmpz(1)
            for pair in numerator.values():
                common = common.lcm(pair[part].denom())
            polys = [numerator[key][part].numer() * (common // numerator[key][part].denom()) for key in coordinates]
            shifted = [fmpq_poly(poly)(evaluator.shift) for poly in polys]
            common *= metric_denominator
            used = min(length, HEIGHT_JET_DEGREE + 1)
            scale = fmpz(1) << HEIGHT_JET_BITS
            low_exact = [[poly[k] / common for poly in shifted] for k in range(used)]

            def nearest(q):
                n, d = (q.numerator, q.denominator)
                return (2 * n * scale + d) // (2 * d)
            low_num = fmpz_mat([[nearest(q) for q in row] for row in low_exact])
            low_product = low_num * tensor
            low = fmpq_mat(low_product) / scale
            _count(counts, 'integer_polynomial_contractions', 1)
            tails = []
            for j, poly in enumerate(shifted):
                rounding = sum((rho ** k / (2 * scale) for k in range(used) if low_exact[k][j]))
                tails.append(_tail_bound(poly / common, HEIGHT_JET_DEGREE, rho) + rounding)

            def ceiling(q):
                return -(-q.numerator * scale // q.denominator)
            tn = fmpz_mat([[ceiling(q) for q in tails]])
            td = scale
            tt = tn * fmpz_mat(tensor.nrows(), tensor.ncols(), [abs(x) for x in tensor.entries()])
            _count(counts, 'integer_polynomial_contractions', 1)
            tail_values = [fmpq(tt[0, col], td) for col in range(len(output))]
        if length or constant_values is not None:
            target_length = max(used, min(len(den_shift), HEIGHT_JET_DEGREE + 1) if constant_values is not None else 0)
            for col, (i, j) in enumerate(output):
                terms = [low[k, col] if low is not None and k < used else fmpq(0) for k in range(target_length)]
                radius = tail_values[col] if tail_values is not None else fmpq(0)
                if constant_values is not None:
                    c = fmpq(constant_values[0, col], constant_denominator)
                    terms = [v + den_shift[k] * c for k, v in enumerate(terms)]
                    radius += den_tail * abs(c)
                bound = D.raw(0)
                for coefficient in reversed(terms):
                    bound = bound * evaluator.variable + rational_interval(coefficient)
                radius_raw = rational_interval(radius).hi
                bound += D.raw(-radius_raw, radius_raw)
                value[i, j] = value[j, i] = bound
        components.append(value)
    result = iv.matrix(n, n)
    for i in range(n):
        for j in range(i, n):
            value = (components[0][i, j] + evaluator.sqrt2 * components[1][i, j]) * inverse
            result[i, j] = result[j, i] = value
    return result


METRIC_CENTER_BITS=128
_METRICS={}


def metric_center(Z):
    """Exact short rational center and an outward enclosure of full Z-Zhat."""
    n=Z.nrows()
    if n<=0 or Z.ncols()!=n:raise ValueError('Expected nonempty square exact metric')
    key=(n,tuple(Z[i,j] for i in range(n) for j in range(n)))
    if key not in _METRICS:
        scale=1<<METRIC_CENTER_BITS
        center=fmpq_mat(n,n);center_interval=iv.matrix(n,n);difference=iv.matrix(n,n)
        nonzero=False;maximum_difference=fmpq(0)
        for i in range(n):
            for j in range(n):
                value=Z[i,j]
                numerator,denominator=int(value.numerator),int(value.denominator)
                rounded=(2*numerator*scale+denominator)//(2*denominator)
                center[i,j]=fmpq(rounded,scale)
                center_interval[i,j]=rational_interval(center[i,j])
                delta=value-center[i,j]
                difference[i,j]=rational_interval(delta)
                nonzero=nonzero or bool(delta)
                maximum_difference=max(maximum_difference,abs(delta))
        def sizes(matrix):
            return dict(max_numerator_bits=max(abs(int(matrix[i,j].numerator)).bit_length() for i in range(n) for j in range(n)),
                        max_denominator_bits=max(int(matrix[i,j].denominator).bit_length() for i in range(n) for j in range(n)))
        record=dict(order=n,center_bits=METRIC_CENTER_BITS,exact=sizes(Z),center=sizes(center),
                    nonzero_difference=nonzero,maximum_exact_difference=str(maximum_difference))
        _METRICS[key]=(center,center_interval,difference,nonzero,record)
    return _METRICS[key]


def piece_metric_difference(corrections,name,n,Z,evaluator,counts=None):
    """One complete discrepancy enclosure valid for every control on a piece.

    A shared entrywise interval hull contains each S_i(a), and therefore
    every convex combination with nonnegative Bernstein coefficients.
    The exact identity for Delta=Z-Zhat is evaluated on that complete hull.
    """
    center,center_interval,difference,nonzero,record=metric_center(Z)
    if not nonzero:return iv.matrix(n,n)
    matrix=iv.matrix(n,n);hulls={}
    for correction in corrections:
        for (block,i,j),r in correction.items():
            if block!=name:continue
            if not 0<=i<=j<n:raise ValueError('Invalid symmetric correction coordinate')
            value=evaluator.rational(r)
            if (i,j) in hulls:
                lo,hi,count=hulls[i,j]
                hulls[i,j]=(min(lo,value.lo),max(hi,value.hi),count+1)
            else:hulls[i,j]=(value.lo,value.hi,1)
    for (i,j),(lo,hi,count) in hulls.items():
        if count<len(corrections):lo,hi=min(lo,0),max(hi,0)
        matrix[i,j]=matrix[j,i]=D.raw(lo,hi)
    cross=difference*matrix*center_interval.T
    quadratic=difference*matrix*difference.T
    _count(counts,'metric_difference_control_enclosures',len(corrections))
    _count(counts,'metric_difference_piece_enclosures',1)
    _count(counts,'metric_difference_matrix_products',4)
    return cross+cross.T+quadratic


def congruence_interval(correction,name,n,Z,evaluator,counts=None):
    """Retain all three exact metric-center perturbation terms.

    For Delta=Z-Zhat, the identity is
    Z M Z^T=Zhat M Zhat^T+Delta M Zhat^T+Zhat M Delta^T+Delta M Delta^T.
    The original exact inverse metric Z and original positive Gram floor
    are unchanged. Only a computational center is rounded.
    """
    center,center_interval,difference,nonzero,record=metric_center(Z)
    nominal=exact_center_congruence_interval(correction,name,n,center,evaluator,counts)
    if not nonzero:return nominal
    matrix=iv.matrix(n,n)
    for (block,i,j),value in correction.items():
        if block==name:matrix[i,j]=matrix[j,i]=evaluator.rational(value)
    cross=difference*matrix*center_interval.T
    quadratic=difference*matrix*difference.T
    if counts is not None:
        counts['metric_difference_control_enclosures']=counts.get('metric_difference_control_enclosures',0)+1
        counts['metric_difference_matrix_products']=counts.get('metric_difference_matrix_products',0)+4
    return nominal+cross+cross.T+quadratic
