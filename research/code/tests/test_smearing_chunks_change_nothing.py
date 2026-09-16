"""Chunked smearing must produce the same links as whole-batch smearing.

`ape_smear` slices its batch over the configuration axis so that peak memory does not scale with `n`.
That is safe because smearing is per configuration -- the staple of configuration `k` reads only
configuration `k` -- and it is safe only for that reason. A slicing that accidentally crossed
configurations would still run, still produce plausible links, and quietly change the observable the
whole box series is read from.

The change was made because it had to be: the beta=2.5 campaign's L=16 job at `n = 384` completed
three hours of Monte Carlo, wrote the unsmeared level, and then died in `ape_smear` trying to allocate
1.50 GiB with 579 MiB free. One shard of six.

So the equivalence is asserted rather than assumed, at the extreme slicing -- one configuration per
chunk -- which is where a cross-configuration read would show up most clearly.
"""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np

REPO = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO / "research" / "code"))

import lattice_generator as G  # noqa: E402

#: DERIVED: a lattice small enough to smear on a CPU in a test and large enough to have staples at
#: all -- every spatial direction needs at least two sites for the unit shift not to be the identity.
SHAPE = (4, 4, 4, 8)
#: DERIVED: more than one configuration, or chunking has nothing to slice and the test is vacuous.
BATCH = 12
#: DERIVED: enough sweeps that the chunk boundary would have to hold across several, not just one.
SWEEPS = 6


def test_chunked_smearing_is_bit_identical_to_whole_batch():
    link = G.gauge_field(SHAPE, 2.4, group="su2", seed=7, therm=5,
                         device=None, batch=BATCH, method="heatbath")
    whole = np.asarray(G.ape_smear(link, SWEEPS, alpha=0.5, group="su2", device=None))

    saved = G.SMEAR_CHUNK_ELEMENTS
    try:
        # DERIVED: 1 element forces one configuration per chunk, the most sliced the code can be.
        # A whole-batch default would exercise the unchunked path and prove nothing about the other.
        G.SMEAR_CHUNK_ELEMENTS = 1
        chunked = np.asarray(G.ape_smear(link, SWEEPS, alpha=0.5, group="su2", device=None))
    finally:
        G.SMEAR_CHUNK_ELEMENTS = saved

    assert whole.shape == chunked.shape, (
        f"chunking changed the shape: {whole.shape} vs {chunked.shape}")
    assert np.array_equal(whole, chunked), (
        f"chunked smearing differs from whole-batch by up to "
        f"{float(np.max(np.abs(whole - chunked)))!r}. Smearing is per configuration, so any "
        f"difference means the slicing is reading across configurations and the smeared operator is "
        f"not the operator it is labelled")


def test_the_unchunked_path_is_still_reachable():
    """A batch under the target is processed whole, so the fast path is not dead code.

    If every batch were chunked, the loop would be doing per-configuration work for no reason on the
    small ensembles the rest of the suite uses.
    """
    per_config = 1
    for d in SHAPE:
        per_config *= d
    per_config *= 4 * 4                      # direction and quaternion axes
    assert G.SMEAR_CHUNK_ELEMENTS // max(1, per_config) >= BATCH, (
        f"a {BATCH}-configuration batch of {SHAPE} does not fit the chunk target "
        f"{G.SMEAR_CHUNK_ELEMENTS}, so the whole-batch path never runs and the target is too small "
        f"to be doing what it claims")
