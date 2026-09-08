"""Reads built on the Entroptics adapter that more than one measurement script needs.

Kept in one place for the same reason as lattice_scales: a read that two scripts state separately
can be corrected in one and left stale in the other, and the two artifacts would then disagree
without either looking wrong on its own.
"""
import glob
import os

import numpy as np

import entroptics_adapter as W


def delta(field):
    """Delta = connected_decay_rate of the merged-ensemble aperture, built by INCREMENTAL splice: one merged
    L^3 x L^3 covariance (memory-frugal). `W.run(list(field)).mass_gap` returns the identical value (verified
    bit-exact at L=8,12,16) but materialises all n per-config covariances first -- fine for small ensembles,
    but ~n*L^6 bytes, which OOMs by L~20; the incremental splice keeps only the running merge."""
    whole = W.Aperture(W._ordered(field[0], -1))
    for i in range(1, field.shape[0]):
        whole = whole.splice(W.Aperture(W._ordered(field[i], -1)), adjacent=False)
    return float(whole.connected_decay_rate)


def load_su2(hops, L, beta, ncap, dtype="float32"):
    """Every su2 shard for one (L, beta) across ALL hops, capped at ncap; None if absent.

    One copy of a loader that was stated four times: the two Sec 8.7 mhi scripts (float32, for
    memory) and the two Sec 9 grid certificates (float64). The dtype is a parameter because that
    difference is deliberate -- collapsing them onto one precision would silently change what the
    certificates compute, which is the opposite of the point.

    This POOLS across hops. Returning the first hop that matched would make a coupling's
    ensemble depend on the order of its caller's `HOPS` rather than on what the store holds: at
    L=16, beta=2.30 the callers variously saw 24 configs (densebeta first), 96 (phase1 first) or
    120 (`9_1_run_d2_certify`, which pools with its own loader) -- three different answers to "which
    configurations are this ensemble", for 120 planes that all exist. The thin read was visible in
    the evidence: in `9_4_dat_interior_mixing_grid.csv` the 24-config coupling carried a deg-3
    interpolant residual 3.9x every other coupling's, on the very grid whose purpose is a measured
    modulus of continuity in beta.

    Shards are taken hop by hop in the caller's `HOPS` order and sorted within each hop, so the
    concatenation -- and therefore which configurations survive the `ncap` cut -- is fixed by the
    hop list and the filenames, not by filesystem order.

    Slicing before the cast is how the float64 copies did it and is what the float32 copies did in
    the other order; an element-wise cast commutes with a slice, so both give identical values.

    A shard must be a density plane, `(n, L, L, L, T)`. The glob also matches the raw-link files in
    `configs_links_su2`, which carry the same name at rank 7 -- `(n, L, L, L, T, dir, group)` -- and
    concatenating those as if they were planes would read the wrong data product without saying so.
    No caller lists that directory today; the check is what keeps that true if one ever does.
    """
    fs = []
    for h in hops:
        fs += sorted(glob.glob(os.path.join(h, "su2_L%d_b%.2f.s*.npy" % (L, beta))))
    if not fs:
        return None
    arrs = []
    for f in fs:
        a = np.load(f)
        if a.ndim != 5:
            raise ValueError(
                "%s has rank %d %s, not the rank-5 density plane (n, L, L, L, T) this reads. "
                "Raw-link shards share the naming; they are a different data product and cannot "
                "be concatenated with planes." % (f, a.ndim, a.shape))
        arrs.append(a)
    return np.concatenate(arrs, 0)[:ncap].astype(dtype)
