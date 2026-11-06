"""Exact sparse trace contraction; production candidate, with optional census.

All proof-relevant inputs and the single final outward rounding agree with
AnalyticFinite.exact_projection.project_raw.  No numerical tolerance is used.
"""
import numpy as np
from flint import fmpz_mat
from exact_iv import D, ceildiv
from taylor_models import iv


def project_raw(raw, denominator, free, pivots, wc, bw, pp, *, _audit=None):
    """Intersect symmetric entries, contract sparse endpoints, round once.

    Equal raw coefficients within one matrix position share their exact
    endpoint products.  A zero-width interval needs one endpoint product;
    coefficients 0 and +/-1 need no integer multiplication.  Absent high
    coefficients in the exact free/free polynomial are still exact zeros.
    """
    if type(denominator) is not int or denominator <= 0:
        raise ValueError('Invalid raw denominator')
    rows, m, other = raw.shape
    if m != other or sorted(free+pivots) != list(range(m)):
        raise ValueError('Invalid raw tensor partition')
    if not np.issubdtype(raw.dtype, np.integer):
        raise ValueError('Noninteger raw coefficient tensor')
    if not np.array_equal(raw, raw.swapaxes(1, 2)):
        raise ValueError('Nonsymmetric raw coefficient tensor')
    if np.any(raw > 2**53) or np.any(raw < -(2**53)):
        raise ArithmeticError('Raw integer exceeds the proved packing range')
    order = len(bw)
    if len(pp) != order or not 0 < len(wc) <= order:
        raise ValueError('Inconsistent coefficient lengths')
    n, q = len(free), len(pivots)
    for seq, shape in ((wc, (n,n)), (bw, (q,n)), (pp, (q,q))):
        if any((C.rows, C.cols) != shape for C in seq):
            raise ValueError('Invalid coefficient matrix shape')
    lower = [[0]*order for _ in range(rows)]
    upper = [[0]*order for _ in range(rows)]
    if _audit is not None:
        _audit.update(rows=rows, order=order, n=n, q=q, denominator=denominator,
                      groups=[])

    def accumulate(name, seq, positions, symmetric):
        stats = dict(name=name, length=len(seq), positions=len(positions),
                     original_dense_products=2*rows*len(positions)*len(seq),
                     sparse_nonzero_coefficients=0, distinct_position_coefficients=0,
                     sparse_endpoint_product_slots=0, shared_endpoint_product_slots=0,
                     zero_endpoint_products_skipped=0, unit_products_skipped=0,
                     integer_products=0, scatter_additions=0, exact_intervals=0,
                     interval_entries=0, max_raw_coefficient_bits=0,
                     max_endpoint_bits=0)
        for a, b, i, j, multiplicity in positions:
            endpoints = []
            for C in seq:
                x = C[a,b]
                lo, hi = x.lo, x.hi
                if symmetric and a != b:
                    y = C[b,a]
                    lo, hi = max(lo, y.lo), min(hi, y.hi)
                if lo > hi:
                    raise ArithmeticError('Disjoint symmetric coefficient enclosures')
                endpoints.append((lo,hi))
            # Convert to Python integers before multiplication.  The original
            # raw bound remains checked, but no narrow integer multiply occurs.
            grouped_rows = {}
            for row in np.flatnonzero(raw[:,i,j]):
                c = int(raw[row,i,j])*multiplicity
                grouped_rows.setdefault(c, []).append(int(row))
            if _audit is not None:
                nnz = sum(map(len,grouped_rows.values()))
                distinct = len(grouped_rows)
                endpoint_slots = sum(1 if lo == hi else 2 for lo,hi in endpoints)
                stats['sparse_nonzero_coefficients'] += nnz
                stats['distinct_position_coefficients'] += distinct
                stats['sparse_endpoint_product_slots'] += nnz*endpoint_slots
                stats['shared_endpoint_product_slots'] += distinct*endpoint_slots
                stats['scatter_additions'] += 2*nnz*len(seq)
                stats['exact_intervals'] += sum(lo == hi for lo,hi in endpoints)
                stats['interval_entries'] += len(endpoints)
                stats['max_raw_coefficient_bits'] = max(stats['max_raw_coefficient_bits'],
                    max((abs(c).bit_length() for c in grouped_rows), default=0))
                stats['max_endpoint_bits'] = max(stats['max_endpoint_bits'],
                    max((max(abs(lo).bit_length(),abs(hi).bit_length()) for lo,hi in endpoints), default=0))
            for c, target_rows in grouped_rows.items():
                values = []
                for lo, hi in endpoints:
                    if c == 1:
                        a0,b0 = lo,hi
                        if _audit is not None:
                            stats['unit_products_skipped'] += 1 if lo == hi else 2
                    elif c == -1:
                        a0,b0 = -hi,-lo
                        if _audit is not None:
                            stats['unit_products_skipped'] += 1 if lo == hi else 2
                    else:
                        x0 = c*lo if lo else 0
                        x1 = x0 if lo == hi else (c*hi if hi else 0)
                        a0,b0 = (x0,x1) if c > 0 else (x1,x0)
                        if _audit is not None:
                            products = int(lo != 0)+int(hi != lo and hi != 0)
                            stats['integer_products'] += products
                            stats['zero_endpoint_products_skipped'] += (1 if lo == hi else 2)-products
                    values.append((a0,b0))
                for row in target_rows:
                    lowrow, highrow = lower[row], upper[row]
                    for k,(a0,b0) in enumerate(values):
                        lowrow[k] += a0
                        highrow[k] += b0
        if _audit is not None:
            assert (stats['shared_endpoint_product_slots'] == stats['integer_products']
                    +stats['zero_endpoint_products_skipped']+stats['unit_products_skipped'])
            _audit['groups'].append(stats)

    accumulate('free', wc, [(a,b,free[a],free[b],1 if a == b else 2)
                           for a in range(n) for b in range(a,n)], True)
    accumulate('cross', bw, [(a,b,pivots[a],free[b],2)
                            for a in range(q) for b in range(n)], False)
    accumulate('pivot', pp, [(a,b,pivots[a],pivots[b],1 if a == b else 2)
                            for a in range(q) for b in range(a,q)], True)
    result = []
    for k in range(order):
        C = iv.matrix(rows,1)
        C.data = [D.raw(lower[i][k]//denominator,
                        ceildiv(upper[i][k],denominator)) for i in range(rows)]
        result.append(C)
    return result


def project_remainder(raw, denominator, free, pivots, cross_error, principal_error):
    """Bound the trace remainder using its exact zero free/free block.

    Cross entries occur twice.  The principal remainder is symmetric, so
    the smaller of its two independent nonnegative upper bounds is valid.
    Every binary64 error endpoint is read as an exact dyadic rational;
    integer contraction precedes the only outward rational conversion.
    """
    from exact_i import rational_bound
    from interval_arithmetic import I
    if type(denominator) is not int or denominator <= 0:
        raise ValueError('Invalid raw denominator')
    rows, m, other = raw.shape
    n, q = len(free), len(pivots)
    if m != other or sorted(free+pivots) != list(range(m)):
        raise ValueError('Invalid raw tensor partition')
    if not np.issubdtype(raw.dtype, np.integer):
        raise ValueError('Noninteger raw coefficient tensor')
    if not np.array_equal(raw, raw.swapaxes(1,2)):
        raise ValueError('Nonsymmetric raw coefficient tensor')
    if cross_error.hi.shape != (q,n) or principal_error.hi.shape != (q,q):
        raise ValueError('Invalid remainder shape')
    if (not np.all(np.isfinite(cross_error.hi)) or
            not np.all(np.isfinite(principal_error.hi)) or
            np.any(cross_error.hi < 0) or np.any(principal_error.hi < 0)):
        raise ValueError('Nonfinite or negative remainder bound')
    positions = [(pivots[a],free[b],2,float(cross_error.hi[a,b]))
                 for a in range(q) for b in range(n)]
    positions += [(pivots[a],pivots[b],1 if a == b else 2,
                   min(float(principal_error.hi[a,b]),float(principal_error.hi[b,a])))
                  for a in range(q) for b in range(a,q)]
    positions = [p for p in positions if p[3] != 0]
    if not positions:
        return I(np.zeros((rows,1)))
    ratios = [bound.as_integer_ratio() for i,j,multiplier,bound in positions]
    scale = max(d for num,d in ratios)
    assert all(scale % d == 0 for num,d in ratios)
    errors = fmpz_mat(len(positions),1,[num*(scale//d) for num,d in ratios])
    coefficients = fmpz_mat(rows,len(positions),
        [abs(int(raw[r,i,j]))*multiplier for r in range(rows)
         for i,j,multiplier,bound in positions])
    bounds = coefficients*errors
    upper = np.array([[rational_bound(int(bounds[r,0]),scale*denominator,True)]
                      for r in range(rows)])
    return I(upper)
