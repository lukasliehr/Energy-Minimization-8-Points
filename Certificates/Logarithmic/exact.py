"""Exact arithmetic in Q(sqrt(2), sqrt(58)) and sparse polynomials.

The default backend is Python Fraction. N8_FAST=1 selects FLINT rational
arithmetic for certificate generation or an optional faster cross-check.
"""
import itertools
import os
from fractions import Fraction

if os.environ.get('N8_FAST') == '1':
    from flint import fmpq as Rat
else:
    Rat = Fraction


class K:
    __slots__ = ('c',)

    def __init__(self, value=0):
        if isinstance(value, K):
            self.c = value.c
        elif isinstance(value, (list, tuple)):
            if len(value) != 4:
                raise ValueError('A field element has four rational coordinates')
            self.c = tuple(Rat(x) for x in value)
        else:
            self.c = (Rat(value), Rat(0), Rat(0), Rat(0))

    def __bool__(self):
        return any(self.c)

    def __eq__(self, other):
        return self.c == K(other).c

    def __add__(self, other):
        other = K(other)
        return K(tuple(x+y for x, y in zip(self.c, other.c)))

    __radd__ = __add__

    def __neg__(self):
        return K(tuple(-x for x in self.c))

    def __sub__(self, other):
        return self+-K(other)

    def __rsub__(self, other):
        return K(other)+-self

    def __mul__(self, other):
        other = K(other)
        out = [Rat(0) for _ in range(4)]
        for i, x in enumerate(self.c):
            if not x:
                continue
            for j, y in enumerate(other.c):
                if y:
                    common = i & j
                    out[i ^ j] += x*y*(2 if common & 1 else 1)*(58 if common & 2 else 1)
        return K(out)

    __rmul__ = __mul__

    def inverse(self):
        if not self:
            raise ZeroDivisionError
        if not any(self.c[1:]):
            return K(1/self.c[0])
        p = K(1)
        for flip in [1, 2, 3]:
            p *= K(tuple(-x if (i & flip) in (1, 2) else x
                         for i, x in enumerate(self.c)))
        norm = self*p
        if any(norm.c[1:]) or not norm.c[0]:
            raise ArithmeticError('Invalid field norm')
        return K(tuple(x/norm.c[0] for x in p.c))

    def __truediv__(self, other):
        return self*K(other).inverse()

    def __rtruediv__(self, other):
        return K(other)*self.inverse()

    def __pow__(self, n):
        if n < 0:
            return self.inverse()**(-n)
        r, a = K(1), self
        while n:
            if n & 1:
                r *= a
            a *= a
            n //= 2
        return r

    def encode(self):
        return [str(x) for x in self.c]

    def mp(self, mp):
        roots = [mp.mpf(1), mp.sqrt(2), mp.sqrt(58), mp.sqrt(116)]
        return sum(mp.mpf(str(x.numerator))/int(x.denominator)*r
                   for x, r in zip(self.c, roots))


SQ2 = K([0, 1, 0, 0])
SQ58 = K([0, 0, 1, 0])
A = (2*SQ58-13)/7
NODES = [A, 2*A-1, -A+(1-A)/SQ2, -A-(1-A)/SQ2]
TYPES = [(3, 3, 0), (3, 1, 2), (3, 2, 0), (1, 0, 0), (2, 2, 0)]
COUNTS = [8, 16, 16, 8, 8]
PAIRS = [8, 4, 8, 8]
TRIPLES = sorted(set(p for t in TYPES for p in itertools.permutations(t)))
PERMS = list(itertools.permutations(range(3)))
ZERO = (0, 0, 0)


def monomials(d):
    return [e for e in itertools.product(range(d+1), repeat=3) if sum(e) <= d]


EXPS = [e for e in monomials(12) if tuple(sorted(e)) == e]
INDEX = {e: i for i, e in enumerate(EXPS)}


def padd(p, q, scale=1):
    out = p.copy()
    for e, c in q.items():
        out[e] = out.get(e, K(0))+c*scale
        if not out[e]:
            del out[e]
    return out


def pmul(p, q):
    out = {}
    for e, c in p.items():
        for f, d in q.items():
            g = tuple(x+y for x, y in zip(e, f))
            out[g] = out.get(g, K(0))+c*d
    return {e: c for e, c in out.items() if c}


def permute(p, permutation):
    return {tuple(e[j] for j in permutation): c for e, c in p.items()}


def evaluate(p, xyz):
    powers = [[x**i for i in range(13)] for x in xyz]
    return sum((c*powers[0][e[0]]*powers[1][e[1]]*powers[2][e[2]]
                for e, c in p.items()), K(0))


def encode_poly(p):
    return [[list(e), c.encode()] for e, c in sorted(p.items())]


def decode_poly(p):
    return {tuple(e): K(c) for e, c in p}


def rref(matrix):
    a = [[K(x) for x in row] for row in matrix]
    pivots = []
    row = 0
    for column in range(len(a[0])):
        hit = next((i for i in range(row, len(a)) if a[i][column]), None)
        if hit is None:
            continue
        a[row], a[hit] = a[hit], a[row]
        inverse = a[row][column].inverse()
        a[row] = [x*inverse for x in a[row]]
        for i in range(len(a)):
            if i != row and a[i][column]:
                factor = a[i][column]
                a[i] = [x-factor*y for x, y in zip(a[i], a[row])]
        pivots.append(column)
        row += 1
        if row == len(a):
            break
    return a, pivots


def kernel_polynomials(polynomials):
    values = [[evaluate(p, [NODES[j] for j in t]) for p in polynomials] for t in TRIPLES]
    reduced, pivots = rref(values)
    free = [j for j in range(len(polynomials)) if j not in pivots]
    basis = []
    for j in free:
        p = polynomials[j].copy()
        for i, pivot in enumerate(pivots):
            p = padd(p, polynomials[pivot], -reduced[i][j])
        basis.append(p)
    return basis


def sos_coefficients(polynomials, generator):
    """Ordinary upper-triangle coordinates: off-diagonal entries contribute twice."""
    columns = []
    for i, p in enumerate(polynomials):
        for j in range(i, len(polynomials)):
            product = pmul(generator, pmul(p, polynomials[j]))
            out = {}
            for e, value in product.items():
                canonical = tuple(sorted(e))
                orbit_size = len(set(itertools.permutations(e)))
                out[canonical] = out.get(canonical, K(0))+value*(1 if i == j else 2)/orbit_size
            columns.append({INDEX[e]: c for e, c in out.items() if c})
    return columns


def moment_polynomials(k, order=6):
    one = {ZERO: K(1)}
    u, v, t = [{tuple(int(i == j) for i in range(3)): K(1)} for j in range(3)]
    qbase = padd(t, pmul(u, v), -1)
    factor = pmul(padd(one, pmul(u, u), -1), padd(one, pmul(v, v), -1))
    q = [one, qbase]
    for j in range(2, k+1):
        q.append(padd(pmul(qbase, q[-1]), pmul(factor, q[-2]), -K(1)/2))
        q[-1] = {e: 2*c for e, c in q[-1].items()}
    matrix = []
    for i in range(order+1-k):
        row = []
        for j in range(order+1-k):
            unsym = pmul({(i, j, 0): K(1)}, q[k])
            sym = {}
            for permutation in PERMS:
                sym = padd(sym, permute(unsym, permutation), K(1)/6)
            result = {e: 6*c for e, c in sym.items()}
            for axis in range(3):
                for e, c in sym.items():
                    f = tuple(e[0]+e[1] if a == axis else 0 for a in range(3))
                    result[f] = result.get(f, K(0))+c
            if k == 0:
                result[ZERO] = result.get(ZERO, K(0))+K(1)/7
            row.append({e: c for e, c in result.items() if c})
        matrix.append(row)
    return matrix


def moment_coefficients(k, basis):
    matrix = moment_polynomials(k, len(basis)+k-1)
    r = len(basis[0])
    columns = []
    for i in range(r):
        for j in range(i, r):
            out = {}
            for a in range(len(basis)):
                for b in range(len(basis)):
                    weight = basis[a][i]*basis[b][j]*(1 if i == j else 2)
                    if not weight:
                        continue
                    for e, c in matrix[a][b].items():
                        if e in INDEX:
                            row = INDEX[e]
                            out[row] = out.get(row, K(0))+weight*c
            columns.append({row: c for row, c in out.items() if c})
    return columns
