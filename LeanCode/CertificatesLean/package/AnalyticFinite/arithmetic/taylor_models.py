"""Interval Taylor models on t in [-1,1], order4..34.

Exponential and logarithm compositions use integrated ODE defects with
quadratic-cost formal recurrences. Other scalar formulas retain their
proved bounds. The physical root is checked by one explicit contraction defect,
using an immutable proposed dyadic polynomial. Its complete model remainders,
exact invariant-domain gate and contraction error are retained. Affine exponent quotients use their full scalar model residual.
No stationarity-residual, derivative or root-tube predicate is used.
The supplied polynomial is an untrusted witness; its fixed-point defect is checked.
"""

import math
from fractions import Fraction

from exact_iv import iv
import os

ORDER = int(os.environ.get("N8_TAYLOR_ORDER", "8"))
assert 4 <= ORDER <= 34

# Diagnostics count only arithmetic used to validate a model.  Newton
# iterations merely propose a polynomial and are explicitly suspended.
_PROOF_MODEL_COUNTS = {
    "scalar_reciprocal_model_calls": 0,
    "scalar_constant_reciprocal_model_calls": 0,
    "scalar_log_model_calls": 0,
    "scalar_exp_model_calls": 0,
    "scalar_direct_quotient_model_calls": 0,
    "normalized_phi_entire_model_calls": 0,
}
_COUNT_SUSPENSIONS = 0


def reset_proof_model_counts():
    for key in _PROOF_MODEL_COUNTS:
        _PROOF_MODEL_COUNTS[key] = 0


def proof_model_counts():
    return dict(_PROOF_MODEL_COUNTS)


def _count_model_operation(key):
    if _COUNT_SUSPENSIONS == 0:
        _PROOF_MODEL_COUNTS[key] += 1


def ab(x):
    return abs(x).b


def radius(e):
    return iv.mpf([-e.b, e.b])


class TM:
    def __init__(self, c, error=0):
        self.c = [iv.mpf(x) for x in c] + [iv.mpf(0)] * (ORDER + 1 - len(c))
        assert len(self.c) == ORDER + 1
        self.e = iv.mpf(error).b

    @classmethod
    def const(cls, x):
        return cls([x])

    @staticmethod
    def coerce(x):
        return x if isinstance(x, TM) else TM.const(x)

    def bound(self):
        return sum([ab(c) for c in self.c], iv.mpf(0)) + self.e

    def interval(self):
        return self.c[0] + radius(sum([ab(c) for c in self.c[1:]], iv.mpf(0)) + self.e)

    def __neg__(self):
        return TM([-x for x in self.c], self.e)

    def __add__(self, b):
        b = TM.coerce(b)
        return TM([x + y for x, y in zip(self.c, b.c)], self.e + b.e)

    __radd__ = __add__

    def __sub__(self, b):
        return self + -TM.coerce(b)

    def __rsub__(self, b):
        return TM.coerce(b) + -self

    def __mul__(self, b):
        b = TM.coerce(b)
        from scalar_cauchy import product
        c, tail = product(self.c,b.c,ORDER)
        tail += (
            self.e * sum([ab(c) for c in b.c], iv.mpf(0))
            + b.e * sum([ab(c) for c in self.c], iv.mpf(0))
            + self.e * b.e
        )
        return TM(c, tail)

    __rmul__ = __mul__

    def inverse(self):
        _count_model_operation("scalar_reciprocal_model_calls")
        enclosure = self.interval()
        if 0 in enclosure:
            raise ArithmeticError("inverse interval contains zero")
        if self.e.lo == self.e.hi == 0 and all(
            c.lo == c.hi == 0 for c in self.c[1:]
        ):
            # A constant coefficient may be an interval.  Reciprocal
            # enclosure then changes that coefficient only, with no
            # functional remainder and no dependency residual.
            _count_model_operation("scalar_constant_reciprocal_model_calls")
            return TM.const(1 / self.c[0])
        c = [1 / self.c[0]]
        for n in range(1, ORDER + 1):
            c.append(
                -sum([self.c[k] * c[n - k] for k in range(1, n + 1)], iv.mpf(0))
                / self.c[0]
            )
        P = TM(c)
        R = 1 - self * P
        # q^-1-P=(1-qP)/q.  The input interval already excludes zero;
        # no Neumann small-residual premise is needed.
        return TM(c, R.bound() / abs(enclosure).a)

    def __truediv__(self, b):
        if not isinstance(b, TM):
            b = iv.mpf(b)
            if 0 in b:
                raise ArithmeticError("division by interval containing zero")
            return TM([x / b for x in self.c], self.e / abs(b).a)
        return self * b.inverse()

    def __rtruediv__(self, b):
        return TM.coerce(b) * self.inverse()

    def __pow__(self, n):
        if isinstance(n, int) and n >= 0:
            r = TM.const(1)
            b = self
            while n:
                if n % 2:
                    r = r * b
                n //= 2
                if n:
                    b = b * b
            return r
        return (TM.coerce(n) * self.log()).exp()

    def exp(self):
        _count_model_operation("scalar_exp_model_calls")
        c = [iv.exp(self.c[0])]
        for n in range(1, ORDER + 1):
            c.append(sum((k * self.c[k] * c[n-k]
                          for k in range(1, n+1)), iv.mpf(0)) / n)
        integrated_defect = iv.mpf(0)
        for n in range(ORDER, 2*ORDER):
            defect = sum((k * self.c[k] * c[n-k+1]
                          for k in range(n-ORDER+1, ORDER+1)), iv.mpf(0))
            integrated_defect += ab(defect) / (n+1)
        variation = sum((ab(x) for x in self.c[1:]), iv.mpf(0))
        error = (iv.exp(variation) * integrated_defect
                 + iv.exp(self.c[0] + variation + self.e) * self.e)
        return TM(c, error)

    def log(self):
        _count_model_operation("scalar_log_model_calls")
        enclosure = self.interval()
        if not (self.c[0].a > 0 and enclosure.a > 0):
            raise ArithmeticError("log input range nonpositive")
        c = [iv.log(self.c[0])]
        for n in range(1, ORDER+1):
            known = sum((k * c[k] * self.c[n-k]
                         for k in range(1, n)), iv.mpf(0))
            c.append((n * self.c[n] - known) / (n * self.c[0]))
        integrated_defect = iv.mpf(0)
        for n in range(ORDER, 2*ORDER):
            defect = sum((k * c[k] * self.c[n-k+1]
                          for k in range(n-ORDER+1, ORDER+1)), iv.mpf(0))
            integrated_defect += ab(defect) / (n+1)
        return TM(c, (integrated_defect + self.e) / enclosure.a)

    def poly_only(self):
        return TM(self.c)


def direct_quotient(numerator, denominator):
    """Formal quotient coefficients, with the full scalar residual retained."""
    _count_model_operation("scalar_direct_quotient_model_calls")
    numerator, denominator = TM.coerce(numerator), TM.coerce(denominator)
    enclosure = denominator.interval()
    if 0 in enclosure:
        raise ArithmeticError("quotient interval contains zero")
    c = []
    for n in range(ORDER+1):
        known = sum((denominator.c[k] * c[n-k]
                     for k in range(1, n+1)), iv.mpf(0))
        c.append((numerator.c[n] - known) / denominator.c[0])
    polynomial = TM(c)
    residual = numerator - denominator * polynomial
    return TM(c, residual.bound() / abs(enclosure).a)


def shared_contact_jets(S, potential, *, balanced):
    """Evaluate contact values once and derive higher Riesz jets rationally."""
    cache = {}
    def shared(exponent, T, k=0):
        if exponent is not S:
            raise ValueError("Shared jets used with a different exponent model")
        if T not in cache:
            cache[T] = (2-2*T, [potential(S, T, 0)])
        distance, jets = cache[T]
        while len(jets) <= k:
            j = len(jets)-1
            if j == 0 and not balanced:
                jets.append(potential(S, T, 1))
            else:
                jets.append(direct_quotient((S+2*j)*jets[j], distance))
        return jets[k]
    return shared


def potential_evaluation_mode(S):
    # Both formulas represent the same entire function of S. Near zero the
    # expm1(z)/z series avoids the large Taylor remainder of an inverse of S.
    # The cutoff is only an enclosure strategy, not a mathematical premise.
    si = S.interval()
    return "entire" if 0 in si or (si.a > -4 and si.b < 4) else "quotient"


def normalized_phi(S, T, k=0):
    d = 2 - 2 * T
    if k:
        pref = TM.const(1)
        for j in range(1, k):
            pref = pref * (S / 2 + j)
        return pref * ((-S / 2 - k) * d.log()).exp() * (2 ** (k - 1))
    ell = -d.log() / 2
    if potential_evaluation_mode(S) == "quotient":
        return ((S * ell).exp() - 1) / S
    _count_model_operation("normalized_phi_entire_model_calls")
    z = S * ell
    zb = z.bound()
    r = TM.const(1)
    term = TM.const(1)
    terms = max(ORDER + 3, 32)
    for n in range(1, terms + 1):
        term = term * z / (n + 1)
        r = r + term
    # Psi(z)=integral_0^1 exp(u*z)du.  Its integral Taylor remainder
    # uses exp(max(z,0)), rather than exp(abs(z)).
    zupper = z.interval().b
    if zupper <= 0:
        tail_factor = iv.mpf(1)
    elif zupper <= iv.mpf("1/11").a:
        # exp(x)<=1/(1-x) for0<=x<1, hence exp(1/11)<=11/10.
        tail_factor = iv.mpf("11/10")
    else:
        raise ArithmeticError("Entire-potential rational tail range")
    r.e = (r.e + tail_factor * zb ** (terms + 1) / math.factorial(terms + 2)).b
    return ell * r



def candidate_model(center, halfwidth):
    from contraction_root import candidate_root
    return candidate_root(center, halfwidth)
