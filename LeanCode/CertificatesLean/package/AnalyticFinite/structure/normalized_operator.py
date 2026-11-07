"""The structural right inverse with its low map cancelled before enclosure.

On compatible residuals this is the same map as right_inverse.apply.  It
uses the two proved coefficient relations to recover the constant and
sigma-squared coefficients before composing the low map.  In particular it
does not select new columns, change the mathematical premise, or assert any
positivity bound.  The 15-jet and 36-product operations are composed over the
exact rational function field before their entries enter a scalar model.
"""
from fractions import Fraction as F
from functools import lru_cache

from . import right_inverse as old
from .right_inverse import R, basis, invariant_tags, SCALAR_ROWS, SCALAR_LABELS, JET_ROWS, SELECT
from canonical import monoms
from .jets import ORBITS, COUNTS
from rational_field import SQRT2


def matmul(a, b):
    if not a or not b or len(a[0]) != len(b):
        raise ValueError('Wrong exact matrix dimensions')
    columns = list(zip(*b))
    return [[sum((x*y for x, y in zip(row, col) if x and y), R())
             for col in columns] for row in a]


@lru_cache(None)
def normalized_data(compatible=True):
    """Generate C=M^-1 J R and T=S^-1(E R-P C), exactly cancelled.

    R lifts the 51 independent invariant coefficients to the full compatible
    53-vector.  With compatible=False, R is the identity for audit purposes.
    """
    data = old.low_data()
    full_tags = tuple(invariant_tags(9))
    J = old.jet_matrix(full_tags)
    if compatible:
        slopes = (R(1), R(2), -1-SQRT2/2, -1+SQRT2/2)
        L0, L1 = [R() for _ in full_tags], [R() for _ in full_tags]
        r = 0
        for orbit, count in zip(ORBITS, COUNTS):
            L0 = [v+count*z for v, z in zip(L0, J[r])]
            r += 1
            for label in sorted(set(orbit)):
                L1 = [v+count*slopes[label]*z for v, z in zip(L1, J[r])]
                r += 1
        const, quad = full_tags.index((0, 0, 0)), full_tags.index((2, 0, 0))
        if L0[const] != 56 or L1[const] != 0 or L1[quad] != 128*(3*old.VARIABLE-1):
            raise ArithmeticError('Unexpected two-relation normalization')
        keep = [i for i in range(len(full_tags)) if i not in (const, quad)]
        quad_recovery = [-L1[i]/L1[quad] for i in keep]
        const_recovery = [-(L0[i]+L0[quad]*z)/56
                          for i, z in zip(keep, quad_recovery)]
        JJ = [[row[i]+row[const]*c+row[quad]*q
               for i, c, q in zip(keep, const_recovery, quad_recovery)]
              for row in J]
        tags = tuple(full_tags[i] for i in keep)
    else:
        JJ, tags = J, full_tags
        const_recovery, quad_recovery = None, None
    jet_map = matmul(data['moment_inverse'], [JJ[i] for i in JET_ROWS])
    P = [[poly.get(tag, R()) for poly in data['moment_invariants']]
         for tag in SCALAR_ROWS]
    # Associate S^-1 P first: this is smaller and avoids building E-P C
    # with unnecessarily large intermediate denominators.
    SP = matmul(data['scalar_inverse'], P)
    SPC = matmul(SP, jet_map)
    positions = {tag: i for i, tag in enumerate(SCALAR_ROWS)}
    scalar_map = [[(row[positions[tag]] if tag in positions else R())-z
                   for tag, z in zip(tags, product)]
                  for row, product in zip(data['scalar_inverse'], SPC)]
    return dict(tags=tags, full_tags=full_tags,
                const_recovery=const_recovery, quad_recovery=quad_recovery,
                jet_map=jet_map, scalar_map=scalar_map,
                moment_features=data['moment_features'])


def apply(d, poly, evaluate, moment_pivots=None):
    """Same scalar-model API and exact map as right_inverse.apply."""
    if not 6 <= d <= 9:
        raise ValueError('Supported active half-degrees are 6..9')
    zero = evaluate(R())
    out = {}
    work = dict(poly)
    cache = {}

    def ev(r):
        key = (tuple(r.p), tuple(r.q), tuple(r.d))
        if key not in cache:
            cache[key] = evaluate(r)
        return cache[key]

    high = sorted((e for e in monoms(2*d)
                   if tuple(sorted(e)) == e and sum(e) >= 10),
                  key=lambda e: (-sum(e), e))
    for gamma in high:
        if gamma not in work:
            continue
        c = work.pop(gamma, zero)
        old._high_gram(d, gamma, out, c, ev, zero)
        for e, z in old.symbolic_column(d, gamma).items():
            if e != gamma:
                work[e] = work.get(e, zero)-c*ev(z)

    low = old.to_invariant(work, zero)
    data = normalized_data()
    vector = [low.get(tag, zero) for tag in data['tags']]
    moment_coeff = [sum((ev(z)*x for z, x in zip(row, vector) if z), zero)
                    for row in data['jet_map']]
    scalar_coeff = [sum((ev(z)*x for z, x in zip(row, vector) if z), zero)
                    for row in data['scalar_map']]
    pivots = {0: 0, 1: 1} if moment_pivots is None else moment_pivots

    for value, (k, i, j) in zip(moment_coeff, SELECT):
        f = data['moment_features'][k][i]
        h = data['moment_features'][k][j]
        free = [q for q in range(d-k+1) if q != pivots[k]]
        v = [f[q] if q < len(f) else R() for q in free]
        w = [h[q] if q < len(h) else R() for q in free]
        old._outer(out, 'F'+str(k), v, w, value, ev, zero)

    desc = basis('s3', d)
    small, large = basis('s3', 4), basis('s3', 5)
    for value, (group, i, j) in zip(scalar_coeff, SCALAR_LABELS):
        ti = small['tags'][group][small['frees'][group][i]]
        tj = large['tags'][group][large['frees'][group][j]]
        ii = desc['frees'][group].index(desc['tags'][group].index(ti))
        jj = desc['frees'][group].index(desc['tags'][group].index(tj))
        name = 'M0_plus' if group == 0 else 'M0_standard'
        a, b = sorted((ii, jj))
        key = (name, a, b)
        out[key] = out.get(key, zero)+value*(1 if a == b else F(1, 2))
    return out
