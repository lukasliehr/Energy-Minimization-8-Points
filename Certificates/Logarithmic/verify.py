"""Check the explicit N=8 certificate, using exact rationals and integer intervals.

Default: Python standard library only. Set N8_FAST=1 to cross-check the exact
algebra with optional python-flint. No optimizer or original CAP is imported.
"""
from pathlib import Path
import hashlib
import json
import math
import os
import sys
import time

import exact as e
from exact import K
import intervals as iv

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def generator(block):
    kind = block['old']
    if kind == 6:
        return {e.ZERO: K(1)}
    if kind == 7:
        return {e.ZERO: K(1), (2, 0, 0): K(-1)}
    require(kind == 8, 'Unknown SOS multiplier')
    return {e.ZERO: K(1), (1, 1, 1): K(2), (2, 0, 0): K(-1),
            (0, 2, 0): K(-1), (0, 0, 2): K(-1)}


def coefficients(block):
    if block['kind'] == 'moment':
        return e.moment_coefficients(block['k'], [[K(x) for x in row] for row in block['basis']])
    require(block['kind'] == 'sos', 'Unknown block kind')
    return e.sos_coefficients([e.decode_poly(p) for p in block['polys']], generator(block))


def verify_hermite(h):
    require(len(h) == 13 and all(len(row) == 5 for row in h), 'Hermite shape')
    conditions = [(x, k, i+1) for i, x in enumerate(e.NODES) for k in [0, 1]]
    conditions += [(K(-1), k, 0) for k in range(5)]
    for t, k, logindex in conditions:
        expected = [K(0) for _ in range(5)]
        if k:
            expected[0] = K(math.factorial(k-1))/(2*(1-t)**k)
        else:
            if logindex == 0:
                expected[1] = K(-1)
            elif logindex == 1:
                expected[2] = -K(1)/2
            elif logindex == 2:
                expected[1] = expected[2] = -K(1)/2
            else:
                expected[logindex] = -K(1)/2
        value = [sum((h[j][ell]*(math.factorial(j)//math.factorial(j-k))*t**(j-k)
                      for j in range(k, 13)), K(0)) for ell in range(5)]
        require(value == expected, 'Exact Hermite contact failed')
    target = [[K(0) for _ in range(5)] for _ in e.EXPS]
    target[0] = h[0].copy()
    for i, count in enumerate([4, 12, 8, 8]):
        target[0][i+1] += K(count)/56
    for i, ex in enumerate(e.EXPS):
        if ex != e.ZERO and ex[0] == ex[1] == 0:
            target[i] = [x/3 for x in h[ex[2]]]
    return target


def main():
    start = time.time()
    path = ROOT/'certificate.json'
    certificate = json.loads(path.read_text())
    require(certificate['format'] == 'N8-explicit-affine-log-v2', 'Format mismatch')
    require(certificate['field_basis'] == ['1', 'sqrt(2)', 'sqrt(58)', 'sqrt(116)'], 'Field basis')
    require(certificate['affine_basis'] == ['1', 'log(2)', 'log(2-2A)', 'log(2-2C)', 'log(2-2D)'], 'Affine basis')
    residual = verify_hermite([[K(x) for x in row] for row in certificate['hermite']])
    require(len(e.EXPS) == 102, 'Coefficient dimension')
    nodes = [iv.field(x) for x in e.NODES]
    for i, x in enumerate(nodes):
        require(-iv.SCALE < x.lo <= x.hi < iv.SCALE, 'Contact not interior')
        for j, y in enumerate(nodes):
            require((x+y).nonzero(), 'Opposite contacts not excluded')
            if i != j:
                require((x-y).nonzero(), 'Distinct contacts not established')
    logs = [iv.Interval(iv.SCALE), iv.log_between_one_and_four(iv.Interval.rational(2))]
    logs += [iv.log_between_one_and_four(2-2*nodes[j]) for j in [0, 2, 3]]
    bounds, total, seen = [], 0, set()
    unweighted = []
    f0 = None
    for block in certificate['blocks']:
        name = block['name']
        require(name not in seen, 'Duplicate block name')
        seen.add(name)
        n = len(block['preconditioner'])
        require(n > 0 and all(len(row) == n for row in block['preconditioner']), 'Preconditioner shape')
        if block['kind'] == 'moment':
            k = block['k']
            require(0 <= k <= 5 and len(block['basis']) == 7-k, 'Moment block size')
            require(all(len(row) == n for row in block['basis']), 'Moment basis shape')
            if k == 0:
                require(f0 is None, 'Duplicate F0')
                f0 = [[K(x) for x in row] for row in block['basis']]
        else:
            require(len(block['polys']) == n, 'Polynomial vector shape')
            limit = {6: 6, 7: 5, 8: 4}[block['old']]
            for p in block['polys']:
                require(len(p) == len(set(tuple(ex) for ex, _ in p)), 'Duplicate monomial')
                require(all(len(ex) == 3 and all(isinstance(i, int) and i >= 0 for i in ex)
                            and sum(ex) <= limit for ex, _ in p), 'Polynomial degree')
            if block['old'] == 6:
                require(all(e.permute(e.decode_poly(p), permutation) == e.decode_poly(p)
                            for p in block['polys'] for permutation in e.PERMS), 'Unweighted polynomials must be symmetric')
                unweighted.extend((name, j, e.decode_poly(p)) for j, p in enumerate(block['polys']))
            if block['old'] == 7:
                require(all(e.permute(e.decode_poly(p), (0, 2, 1)) == e.decode_poly(p)
                            for p in block['polys']), 'Weighted polynomials must be symmetric in v,t')
        columns = coefficients(block)
        require(len(columns) == len(block['matrix_upper']) == n*(n+1)//2, 'Matrix coordinate shape')
        W = [[iv.Interval(0) for _ in range(n)] for _ in range(n)]
        entry = 0
        for i in range(n):
            for j in range(i, n):
                values = block['matrix_upper'][entry]
                require(len(values) == 5 and all(len(x) == 4 for x in values), 'Affine coordinate shape')
                values = [K(x) for x in values]
                for row, coefficient in columns[entry].items():
                    for ell in range(5):
                        residual[row][ell] -= coefficient*values[ell]
                value = sum((iv.field(x)*log for x, log in zip(values, logs)), iv.Interval(0))
                W[i][j] = W[j][i] = value
                entry += 1
        P = [[iv.Interval.rational(x) for x in row] for row in block['preconditioner']]
        congruence = iv.multiply(iv.multiply(P, W), iv.transpose(P))
        error = max(sum((value-(1 if i == j else 0)).magnitude()
                        for j, value in enumerate(row)) for i, row in enumerate(congruence))
        require(2*error < iv.SCALE, 'Positive-definiteness certificate failed: '+name)
        bounds.append({'block': name, 'dimension': n,
                       'row_sum_error_upper_numerator': str(error),
                       'denominator_power_of_two': iv.BITS, 'less_than_one_half': True})
        total += len(columns)
        print('Verified block', name, n, flush=True)
    require(not any(x for row in residual for x in row), 'Full exact polynomial identity failed')
    # A particularly simple, explicit proof of the F0 rank needed for uniqueness.
    require(f0 is not None and len(f0) == 7 and len(f0[0]) == 6, 'F0 basis missing')
    require(all(f0[i+1][j] == int(i == j) for i in range(6) for j in range(6)), 'F0 free rows must be identity')
    moments = [K(1)+sum((count*x**i for count, x in zip([2, 1, 2, 2], e.NODES)), K(0)) for i in range(7)]
    require(moments[0] == 8 and moments[1] == 0, 'Candidate moment values')
    require(all(not sum((f0[i][j]*moments[i] for i in range(7)), K(0)) for j in range(6)), 'F0 null vector')
    forbidden = []
    for last in [0, 2, 3]:
        hit = None
        for name, j, p in unweighted:
            value = iv.field(e.evaluate(p, [e.NODES[0], e.NODES[0], e.NODES[last]]))
            if value.nonzero():
                hit = {'type': [0, 0, last], 'block': name, 'coordinate': j,
                       'enclosure': value.encode()}
                break
        require(hit is not None, 'Forbidden triangle not excluded')
        forbidden.append(hit)
    report = {'certificate_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
              'python': sys.version, 'exact_backend': 'flint' if os.environ.get('N8_FAST') == '1' else 'Fraction',
              'interval_precision_bits': iv.BITS, 'polynomial_identity_exact': True,
              'checked_coefficients': 102, 'formal_log_components_per_coefficient': 5,
              'hermite_contacts_exact': True, 'matrix_coordinates': total,
              'positive_definite_blocks': bounds, 'uniqueness_checks_passed': True,
              'forbidden_triangles': forbidden, 'log_enclosures': [x.encode() for x in logs[1:]],
              'elapsed_seconds': time.time()-start,
              'qualification': 'Standalone exact Python checks. The independent Lean proof is in ../../LeanCode/Logarithmic and ../../Showcase_WithProofs.lean; this report records Python execution only.'}
    name = 'verification_fast.json' if os.environ.get('N8_FAST') == '1' else 'verification.json'
    (ROOT/name).write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: 102 exact coefficients, 13 exact Hermite contacts, positivity, and uniqueness.', flush=True)
    print('Elapsed seconds:', report['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
