"""Reads built on the Entroptics adapter that more than one measurement script needs.

Kept in one place for the same reason as lattice_scales: a read that two scripts state separately
can be corrected in one and left stale in the other, and the two artifacts would then disagree
without either looking wrong on its own.
"""
import glob
import math
import os

import numpy as np

import entroptics_adapter as W
import lattice_generator as G


def delta(field):
    """Delta = connected_decay_rate of the merged-ensemble aperture, built by INCREMENTAL splice: one merged
    L^3 x L^3 covariance (memory-frugal). `W.run(list(field)).mass_gap` returns the identical value (verified
    bit-exact at L=8,12,16) but materialises all n per-config covariances first -- fine for small ensembles,
    but ~n*L^6 bytes, which OOMs by L~20; the incremental splice keeps only the running merge."""
    whole = W.Aperture(W._ordered(field[0], -1))
    for i in range(1, field.shape[0]):
        whole = whole.splice(W.Aperture(W._ordered(field[i], -1)), adjacent=False)
    return float(whole.connected_decay_rate)


def load_su2(hops, L, beta, ncap, dtype="float32", group="su2"):
    """Every shard of `group` for one (L, beta) across ALL hops, capped at ncap; None if absent.

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
    # The GROUP is a parameter so the same loader serves su3. `delta()` is already
    # group-agnostic, so a second loader would only duplicate the rank check, the hop
    # ordering and the ncap-before-cast rule documented above -- three things that must not
    # drift apart. The default keeps every existing caller unchanged.
    fs = []
    for h in hops:
        fs += sorted(glob.glob(os.path.join(h, "%s_L%d_b%.2f.s*.npy" % (group, L, beta))))
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


def operator_history(shard):
    """`O(t)` of shape `(n, T)` from a stored shard, whichever form it is in.

    Two shard kinds reach this. A `--field operator` shard is ALREADY `(n, T)` -- the zero-momentum
    projection was done on the pod, before the links were discarded. A `--field density` shard is the
    action-density FIELD `(n, L, L, L, T)`, and its zero-momentum projection is the sum over the three
    spatial axes -- exactly what `lattice_generator.density_Ot` does to links, applied to the stored
    field instead.

    That equivalence is why a box series can be read from density shards that already exist without
    regenerating anything: the reduction is the same reduction. What it CANNOT recover is smearing,
    which acts on links, and the density shard is already past them.
    """
    a = np.asarray(shard)
    # DERIVED: 2 and 5 are the SHAPES the two shard kinds have -- `(n, T)` for an operator
    # reduction, `(n, L, L, L, T)` for a density field. Arity, not thresholds: the number of
    # axes says which object this is, and anything else is neither.
    if a.ndim == 2:
        return a.astype(np.float64)
    # DERIVED: 5 axes is the density field's shape, as above; the three summed are the spatial ones.
    if a.ndim == 5:
        return a.astype(np.float64).sum(axis=(1, 2, 3))
    raise ValueError(f"operator_history: expected (n,T) or (n,L,L,L,T), got {a.shape}")


# CHOSEN: `nlag=12` is how far to LOOK, not how far to trust. The usable range is found inside and
# is always shorter; looking further costs microseconds and can only reveal more, never admit more.
def configs_for_blocked_lag(O, blocks, need, nlag=12):
    """Ensemble size at which EVERY block reaches lag `need` -- the size a blocked read actually wants.

    WHY THIS EXISTS, and it cost a campaign. `lag_budget(O, blocks)` measures the FULL ensemble's
    correlator against the block-to-block spread, and `configs_for_lag` projects from it. But a read
    that validates per block -- `gap_of_box_operator.read_blocks` requires the pencil to validate in
    EVERY block -- needs each BLOCK's own correlator to reach `need`, and a block is `1/blocks` of the
    ensemble with correspondingly worse noise. The two numbers differ by about `blocks`, and quoting
    the first while gating on the second sizes a campaign short by exactly that factor.

    Measured on the beta = 2.5 box series: the full ensemble reached lags 3-7 at n = 384 while its
    four blocks reached 2-5, never all four at the 5 an order-2 pencil needs. The campaign was sized
    on the first column and gated on the second.

    Returns `None` when no block gives a slope to project from.
    """
    n = O.shape[0]
    per = n // blocks
    # DERIVED: 2 is where a connected correlator exists at all, as in `lag_budget`.
    if per < 2:
        return None
    wants = []
    for b in range(blocks):
        g = lag_budget(O[b * per:(b + 1) * per], blocks, nlag)
        # DERIVED: 2 lags is the arity of a decay RATE -- one lag is a value, not a slope.
        if not g or g[0] < 2:
            continue
        last, rate, s, Cc, _ = g
        w = configs_for_lag(last, rate, s, Cc, per, need)
        if w:
            wants.append(w)
    if not wants:
        return None
    # the WORST block, not the average: the read requires every block to validate, so the budget is
    # set by the block that needs the most.
    return int(max(wants)) * blocks


# CHOSEN: `nlag=12` is how far to LOOK, not how far to trust. The usable range is found inside and
# is always shorter; looking further costs microseconds and can only reveal more, never admit more.
def lag_budget(O, blocks, nlag=12):
    """`(last_usable_lag, decay_rate, sigma_there, C, sigma)` -- how far the correlator is signal.

    `blocks` is the caller's: the block structure is its reseeding design, and a shared read has
    no business having an opinion about it.

    WHY THE READ NEEDS THIS. The moment pencil of order `m` consumes `c_0 .. c_{2m+1}`. If the
    correlator is noise past lag 3, an order-2 pencil is reading noise in a third of its inputs, and
    it declines -- correctly, and without saying so. This measures the usable range directly.

    THE CRITERION IS A SPECTRAL FACT, not a cut. The correlator of a reflection-positive transfer
    matrix is a sum of decaying exponentials with nonnegative weights, so it is POSITIVE and
    DECREASING; and an estimate below its own block-to-block spread is not resolved. The usable range
    is the initial run satisfying all three, and the first lag failing any of them ends it. Testing
    only "above the spread" is not enough and gives a wrong answer on this data: at one box it admitted
    `C(8) = 0.046` arriving after `C(4) = 0.035` -- noise that happened to clear the spread.
    """
    n = O.shape[0]
    C = G.connected_correlator(O, nlag + 1)
    per = n // blocks
    # DERIVED: 2 is where a connected correlator exists at all, as in `read_blocks`.
    if per < 2:
        return None
    parts = np.array([G.connected_correlator(O[b * per:(b + 1) * per], nlag + 1)
                      for b in range(blocks)])
    sigma = parts.std(axis=0, ddof=1)
    last = 0
    for tau in range(1, nlag + 1):
        # DERIVED: `0` is positivity and `C[tau] >= C[tau-1]` is monotonicity -- both properties of
        # a sum of decaying exponentials with nonnegative weights, which is what a reflection-
        # positive transfer matrix produces. The third compares the estimate against its own
        # measured spread. None is a tolerance.
        if C[tau] <= 0 or C[tau] >= C[tau - 1] or abs(C[tau]) <= sigma[tau]:
            break
        last = tau
    # DERIVED: 2 lags is the arity of a decay RATE -- one lag is a value, not a slope.
    if last < 2:
        return last, float("nan"), float("nan"), C, sigma
    rate = math.log(abs(C[1]) / abs(C[last])) / (last - 1)
    return last, rate, float(sigma[last]), C, sigma


def configs_for_lag(last, rate, sigma_there, C, n, target):
    """The ensemble that would put lag `target` above the noise floor, or None if already there.

    The floor is statistical and falls as `1/sqrt(n)`, so reaching a lag `d` beyond the present one
    costs a factor `exp(2 * rate * d)` in configurations. That exponential is the whole difficulty:
    it is why quadrupling an ensemble buys less than one extra lag at these rates, and why comparing
    a 96-configuration read against its own 24-configuration quarters cannot tell a sample-limited
    read from a structurally limited one.
    """
    if target <= last:
        return None
    want = abs(C[last]) * math.exp(-rate * (target - last))
    return n * (sigma_there / want) ** 2


def pencil_rate(O, order):
    """`(rate, valid)` from the reflection-positive moment pencil on `O` of shape `(n, T)`.

    The transfer rate `-log lambda_1` read off the Hankel moment pencil of the connected correlator.
    Its estimator dimension is the moment ORDER, not the lattice volume, which is what makes it usable
    for a box series: growing the box leaves the pencil the same size and makes `O(t)` quieter, since
    `O` is a sum over `L^3` sites and self-averages.

    BOTH GATES ARE THE READ'S OWN VERDICTS, not numbers chosen here:

      * `rate` is `nan` unless the leading transfer eigenvalue lies in `(0, 1)`. A transfer operator
        cannot grow a correlation, so a value outside that range is not a rate at all -- a spectral
        fact, not a tolerance.
      * `isolation` is infinite exactly when the pencil separates a single mode. Where it is finite
        the modes crowd and the leading eigenvalue is a mixture; calibration found a 66% error in one
        such case.

    Calibrated in `certify/gap_of_maximal_correlation.test_pencil_planted`: on planted rates 0.30,
    0.50 and 0.80 the usable orders land within 0.11-0.51 of their own reseeding spread, and order 4
    invalidates itself rather than answering.

    DERIVED: `2*order + 1` lags is the pencil's ARITY, not a window. The order-`n` pencil is
    `(n+1) x (n+1)`, so `H0` needs `c_0..c_2n` and the shifted `H1` needs `c_1..c_(2n+1)`.
    """
    C = G.connected_correlator(O, 2 * order + 1)
    hs = W.hankel_spectrum(C, order)
    rate = hs.rate
    valid = (rate == rate) and math.isinf(hs.isolation)
    return float(rate), bool(valid)
