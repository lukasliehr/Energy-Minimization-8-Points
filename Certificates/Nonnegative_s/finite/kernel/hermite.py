"""Confluent Newton interpolation using outward Taylor models.
The returned coefficients enclose the exact polynomial, not a numerical solve.
"""

import math
from taylor_models import TM, normalized_phi


def hermite_coefficients(S, nodes, multiplicities, endpoint_multiplicity=1):
    if (
        type(endpoint_multiplicity) is not int
        or endpoint_multiplicity < 1
        or endpoint_multiplicity % 2 != 1
    ):
        raise ValueError("Endpoint multiplicity must be positive and odd")
    if (
        len(nodes) != 4
        or len(multiplicities) != 4
        or any(m < 2 or m % 2 for m in multiplicities)
    ):
        raise ValueError("Invalid interior contact multiplicities")
    # Consecutive repeated nodes are essential for the confluent recurrence.
    order = (0, 2, 1, 3, 4)
    allnodes = list(nodes) + [TM.const(-1)]
    mult = list(multiplicities) + [endpoint_multiplicity]
    tags = [j for j in order for _ in range(mult[j])]
    xx = [allnodes[j] for j in tags]
    values = {
        (j, k): normalized_phi(S, t, k) / math.factorial(k)
        for j, t in enumerate(allnodes)
        for k in range(mult[j])
    }
    table = []
    newton = []
    for i in range(len(xx)):
        row = [values[tags[i], 0]]
        for k in range(1, i + 1):
            if tags[i] == tags[i - k]:
                row.append(values[tags[i], k])
            else:
                row.append((row[-1] - table[-1][k - 1]) / (xx[i] - xx[i - k]))
        table.append(row)
        newton.append(row[-1])
    coeff = [newton[-1]]
    for k in range(len(xx) - 2, -1, -1):
        cc = (
            [-xx[k] * coeff[0]]
            + [coeff[i - 1] - xx[k] * coeff[i] for i in range(1, len(coeff))]
            + [coeff[-1]]
        )
        cc[0] = cc[0] + newton[k]
        coeff = cc
    return coeff
