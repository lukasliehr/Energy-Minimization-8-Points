"""Contact evaluation inverse from scalar interpolation and a 3 by 3 quotient.

This module contains no numerical/algebraic witness table, matrix inversion,
or external dependencies.  The coefficient type is supplied by the caller:
it must support exact field arithmetic (or a validated arithmetic analogue).
All three old pivot patterns are handled without changing their coordinates.

The proof and the nonvanishing denominators are in construction.tex.  Runtime
generation over Q(sqrt(2))(a) can be used to cancel rational functions before
validated Taylor evaluation; directly passing Taylor models is optional.
"""
from itertools import permutations


ORBIT_TYPES = ((0, 0, 1), (0, 2, 2), (0, 3, 3), (0, 2, 3), (1, 2, 3))
POINTS = tuple(sorted({t for orbit in ORBIT_TYPES for t in permutations(orbit)}))


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def det3(M):
    return (M[0][0] * (M[1][1]*M[2][2] - M[1][2]*M[2][1])
            - M[0][1] * (M[1][0]*M[2][2] - M[1][2]*M[2][0])
            + M[0][2] * (M[1][0]*M[2][1] - M[1][1]*M[2][0]))


def adjugate3(M):
    return [[(-1)**(i+j) * (
        M[[k for k in range(3) if k != j][0]][[k for k in range(3) if k != i][0]]
        * M[[k for k in range(3) if k != j][1]][[k for k in range(3) if k != i][1]]
        - M[[k for k in range(3) if k != j][0]][[k for k in range(3) if k != i][1]]
        * M[[k for k in range(3) if k != j][1]][[k for k in range(3) if k != i][0]])
        for j in range(3)] for i in range(3)]


def univariate_product(p, q):
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i+j] += a * b
    return out


def poly_add(p, q):
    out = p.copy()
    for e, c in q.items():
        out[e] = out.get(e, 0) + c
    return out


def poly_scale(c, p):
    return {e: c*v for e, v in p.items()}


def poly_mul(p, q):
    out = {}
    for e, c in p.items():
        for f, d in q.items():
            ef = tuple(x+y for x, y in zip(e, f))
            out[ef] = out.get(ef, 0) + c*d
    return out


def poly_sum(ps):
    out = {}
    for p in ps:
        out = poly_add(out, p)
    return out


def poly_value(p, x):
    return sum(c * x[0]**e[0] * x[1]**e[1] * x[2]**e[2]
               for e, c in p.items())


class InvariantInterpolation:
    """Five scalar Lagrange interpolations, followed by one 2 by 2 formula.

    The output basis is (1, sigma, sigma^2, e2, sigma*e2).  Forming the
    Lagrange polynomials uses only differences of the five orbit nodes.
    """

    def __init__(self, sigmas, e2s):
        self.lagrange = []
        for i, s in enumerate(sigmas):
            p = [1]
            denominator = 1
            for j, t in enumerate(sigmas):
                if i != j:
                    p = univariate_product(p, [-t, 1])
                    denominator *= s-t
            self.lagrange.append([c / denominator for c in p])
        self.e = self.lagrange_coefficients(e2s)
        self.f = self.lagrange_coefficients([s*e for s, e in zip(sigmas, e2s)])
        self.denominator = self.e[3]*self.f[4] - self.e[4]*self.f[3]

    def lagrange_coefficients(self, values):
        return [sum(v*p[k] for v, p in zip(values, self.lagrange)) for k in range(5)]

    def __call__(self, values):
        h = self.lagrange_coefficients(values)
        r = (h[3]*self.f[4] - h[4]*self.f[3]) / self.denominator
        s = (self.e[3]*h[4] - self.e[4]*h[3]) / self.denominator
        return [h[k] - r*self.e[k] - s*self.f[k] for k in range(3)] + [r, s]


class ContactInverse:
    """An exact evaluation inverse in the original 21-monomial pivot basis."""

    def __init__(self, a, sqrt2, monomials, points=POINTS):
        self.a = a
        self.sqrt2 = sqrt2
        self.one = a*0 + 1
        self.monomials = tuple(tuple(e) for e in monomials)
        self.points = tuple(tuple(e) for e in points)
        if self.points != POINTS:
            raise ValueError("Unexpected ordered contact triples")
        if len(self.monomials) != 21 or len(set(self.monomials)) != 21:
            raise ValueError("Expected 21 distinct pivot monomials")
        if any(len(e) != 3 or min(e) < 0 or sum(e) > 4 for e in self.monomials):
            raise ValueError("Invalid pivot monomials")
        low = {e for e in self.monomials if sum(e) <= 3}
        all_low = {(i, j, k) for i in range(4) for j in range(4-i) for k in range(4-i-j)}
        missing = all_low - low
        cubes = {(3, 0, 0), (0, 3, 0), (0, 0, 3)}
        if len(low) != 18 or (1, 1, 1) not in missing or len(missing & cubes) != 1:
            raise ValueError("Unexpected degree-three pivot structure")
        self.missing_cube = next(iter(missing & cubes))
        self.high_indices = [i for i, e in enumerate(self.monomials) if sum(e) == 4]
        if len(self.high_indices) != 3:
            raise ValueError("Expected three quartic pivots")
        self.nodes = (a, 2*a-1, -a+(1-a)*sqrt2/2, -a-(1-a)*sqrt2/2)
        self.values = [tuple(self.nodes[i] for i in t) for t in self.points]

        # Geometric invariant and covariant polynomials, with field coefficients.
        one = {(0, 0, 0): self.one}
        x = [{tuple(int(i == j) for i in range(3)): self.one} for j in range(3)]
        sigma = poly_sum(x)
        e2 = poly_sum([poly_mul(x[i], x[j]) for i in range(3) for j in range(i+1, 3)])
        e3 = poly_mul(poly_mul(x[0], x[1]), x[2])
        self.basis = [one, sigma, poly_mul(sigma, sigma), e2, poly_mul(sigma, e2)]
        self.p = [poly_add(xx, poly_scale(-self.one/3, sigma)) for xx in x]
        psquares = [poly_mul(p, p) for p in self.p]
        pnorm = poly_sum(psquares)
        self.q = [poly_add(qq, poly_scale(-self.one/3, pnorm)) for qq in psquares]
        self.delta = poly_mul(poly_mul(poly_add(x[0], poly_scale(-1, x[1])),
                                      poly_add(x[0], poly_scale(-1, x[2]))),
                              poly_add(x[1], poly_scale(-1, x[2])))

        self.orbits = []
        for typ in ORBIT_TYPES:
            point_set = set(permutations(typ))
            indices = [i for i, p in enumerate(self.points) if p in point_set]
            rep = self.values[indices[0]]
            pvals = [tuple(poly_value(p, self.values[i]) for p in self.p) for i in indices]
            qvals = [tuple(poly_value(q, self.values[i]) for q in self.q) for i in indices]
            deltas = [poly_value(self.delta, self.values[i]) for i in indices]
            pp = dot(pvals[0], pvals[0])
            pq = dot(pvals[0], qvals[0])
            qq = dot(qvals[0], qvals[0])
            self.orbits.append({"indices": indices, "p": pvals, "q": qvals,
                                "delta": deltas, "pp": pp, "pq": pq, "qq": qq,
                                "gramdet": pp*qq-pq*pq,
                                "sigma": sum(rep), "e2": poly_value(e2, rep),
                                "lambda": pq/pp})
        self.sigmas = [o["sigma"] for o in self.orbits]
        self.interpolation = InvariantInterpolation(self.sigmas, [o["e2"] for o in self.orbits])

        # The two invariant cubic kernel polynomials.
        def kernel(p):
            data = [poly_value(p, self.values[o["indices"][0]]) for o in self.orbits]
            c = self.interpolation(data)
            return poly_add(p, poly_sum([poly_scale(-z, b) for z, b in zip(c, self.basis)]))
        self.kernel_cube = kernel(poly_mul(self.basis[2], sigma))
        self.kernel_product = kernel(e3)
        self.cubic_denominator = self.kernel_product[(1, 1, 1)]

        self.high_values = [[x[0]**self.monomials[i][0] * x[1]**self.monomials[i][1]
                             * x[2]**self.monomials[i][2] for x in self.values]
                            for i in self.high_indices]
        columns = [self.quotient(y) for y in self.high_values]
        self.quotient_matrix = [list(r) for r in zip(*columns)]
        self.quotient_denominator = det3(self.quotient_matrix)
        self.quotient_adjugate = adjugate3(self.quotient_matrix)

    def components(self, y):
        means, signs, cs, ds, hs = [], [], {}, {}, {}
        for k, o in enumerate(self.orbits):
            n = len(o["indices"])
            vals = [y[i] for i in o["indices"]]
            means.append(sum(vals) / n)
            yp = [sum(v*p[j] for v, p in zip(vals, o["p"])) / n for j in range(3)]
            if n == 6:
                yq = [sum(v*q[j] for v, q in zip(vals, o["q"])) / n for j in range(3)]
                cs[k] = [2*(o["qq"]*yp[j]-o["pq"]*yq[j])/o["gramdet"] for j in range(3)]
                ds[k] = [2*(o["pp"]*yq[j]-o["pq"]*yp[j])/o["gramdet"] for j in range(3)]
                signs.append(sum(v*d for v, d in zip(vals, o["delta"])) / (n*o["delta"][0]**2))
            else:
                hs[k] = [2*v/o["pp"] for v in yp]
        gdifference = self.sigmas[3]-self.sigmas[4]
        g1 = [(ds[3][j]-ds[4][j])/gdifference for j in range(3)]
        g0 = [ds[3][j]-self.sigmas[3]*g1[j] for j in range(3)]
        fvalues = []
        for k, o in enumerate(self.orbits):
            fvalues.append(cs[k] if k >= 3 else
                           [hs[k][j]-o["lambda"]*(g0[j]+self.sigmas[k]*g1[j]) for j in range(3)])
        fcoeff = [self.interpolation([f[j] for f in fvalues]) for j in range(3)]
        return means, signs, fcoeff, g0, g1

    def quotient(self, y):
        _, signs, fcoeff, _, _ = self.components(y)
        return [signs[0]-signs[1], fcoeff[0][4], fcoeff[1][4]]

    def reconstruct_low(self, y):
        means, signs, fcoeff, g0, g1 = self.components(y)
        polynomial = poly_sum([poly_scale(c, b) for c, b in
                               zip(self.interpolation(means), self.basis)])
        polynomial = poly_add(polynomial, poly_scale(signs[0], self.delta))
        for j in range(3):
            f = poly_sum([poly_scale(c, b) for c, b in zip(fcoeff[j][:4], self.basis[:4])])
            g = poly_add(poly_scale(g0[j], self.basis[0]), poly_scale(g1[j], self.basis[1]))
            polynomial = poly_add(polynomial, poly_add(poly_mul(f, self.p[j]), poly_mul(g, self.q[j])))
        polynomial = poly_add(polynomial, poly_scale(-polynomial.get(self.missing_cube, 0), self.kernel_cube))
        polynomial = poly_add(polynomial, poly_scale(-polynomial.get((1, 1, 1), 0)/self.cubic_denominator,
                                                     self.kernel_product))
        return polynomial

    def solve(self, y):
        if len(y) != 21:
            raise ValueError("Expected 21 contact values")
        y = [self.one*v for v in y]
        q = self.quotient(y)
        high = [dot(row, q)/self.quotient_denominator for row in self.quotient_adjugate]
        remaining = [v - sum(c*col[i] for c, col in zip(high, self.high_values)) for i, v in enumerate(y)]
        polynomial = self.reconstruct_low(remaining)
        result = [polynomial.get(e, 0) for e in self.monomials]
        for i, c in zip(self.high_indices, high):
            result[i] = c
        return result

    def inverse(self):
        columns = [self.solve([self.one*int(i == j) for i in range(21)]) for j in range(21)]
        return [list(r) for r in zip(*columns)]


def evaluation_inverse(a, sqrt2, monomials, points=POINTS):
    return ContactInverse(a, sqrt2, monomials, points).inverse()
