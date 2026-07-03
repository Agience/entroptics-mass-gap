"""
classic.py -- CLASSIC diagnostic (research/code/).

The mean plaquette <cos P>, the standard classic mean-action scalar. It is NOT an
entroptics read and NOT the same quantity as any entroptics read, so it never
appears next to one in research/data or research/figures. It is available only for
an EXACT same-quantity cross-check (see ../../CLAUDE.md): if a classic number and
an entroptics number claim to measure the same thing and disagree, one is wrong.

Derived from the action-density field the generator emits:
    phi(x) = sum_{mu<nu}(1 - cos P),  6 planes in 4D,  so  <cos P> = 1 - mean(phi)/6.
"""
from __future__ import annotations

import numpy as np

_N_PLANES = 6  # C(4,2) plaquette planes in 4 dimensions


def mean_plaquette(field):
    """<cos P> from the action-density field: 1 - mean(phi)/6."""
    return 1.0 - float(np.asarray(field, dtype=float).mean()) / _N_PLANES
