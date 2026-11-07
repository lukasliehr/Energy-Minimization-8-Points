"""Residual coordinates modulo the analytically recovered 1 and sigma² rows.

The four-block linear extension annihilates these two coordinate vectors.
Actual residuals satisfy the two universal contact relations, on whose
kernel deletion of the two rows is injective.  Thus bounding only these
retained coordinates is sufficient for the complete correction identity.
"""
from functools import lru_cache

from AnalyticFinite.analytic_layout import invariant_tags
import invariant_raw

OMITTED = ((0,0,0),(2,0,0))


def coordinate_tags(totaldegree):
    if type(totaldegree) is not int or totaldegree not in (12,14,16,18):
        raise ValueError('Unsupported quotient polynomial degree')
    return [tag for tag in invariant_tags(totaldegree) if tag not in OMITTED]


def quotient_tensor(dat,totaldegree):
    tags = invariant_tags(totaldegree)
    if dat['raw'].ndim != 3 or dat['raw'].shape[0] != len(tags):
        raise ValueError('Wrong full invariant coefficient tensor')
    keep = [i for i,tag in enumerate(tags) if tag not in OMITTED]
    return dict(dat,raw=dat['raw'][keep])


@lru_cache(None)
def raw_symmetry(kind,degree,totaldegree):
    return [quotient_tensor(dat,totaldegree)
            for dat in invariant_raw.raw_symmetry(kind,degree,totaldegree)]


@lru_cache(None)
def moment_data(degree):
    return [quotient_tensor(dat,2*degree) for dat in invariant_raw.moment_data(degree)]
