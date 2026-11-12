"""Integer matrix products and exact interval infinity norms."""
import numpy as np
from interval_arithmetic import I
from exact_mm import mm


def absI(x):
    return I(I.coerce(x).magnitude())


def norm(x):
    return float(np.max(I(I.coerce(x).magnitude()).sum(axis=-1).hi))
