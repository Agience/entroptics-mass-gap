"""ym_crossover_confinement_of_grid.py -- the nominal-confidence data read against the finite-grid form of A1's
interior on the crossover (Lean `Interior.ym_crossover_confinement_of_grid_sharp`, through
`Interior.d2_le_of_analytic_grid` and `Certify.le_of_lipschitz_grid`). The data are SU(2) ensembles and the Lean
hypotheses are on `d2At 15` (the SU(3) correlation of one plaquette), so this is evidence for those hypotheses,
not a discharge of them.

What this emits:
  * DATA    : the whitened :F^2: second moment <d^2>(beta) across the dense SU(2) grid, bootstrap bars.
  * CERTIFICATE (drives the verdict): an empirical-Bernstein (Maurer-Pontil 2009) UPPER bound u(beta)
    on <d^2> at every measured beta, at NOMINAL 99.9% per beta -- no fit. Nominal because the Thm 4
    guarantee needs i.i.d. samples and a support width fixed in advance, and `eb` plugs in the
    sample range (see its docstring), so the guarantee does not strictly apply. The
    interior CLEARS iff every u(beta) < B_16 (the aperture threshold). A different quantity,
    the single-plaquette Kogut-Susskind gap, is enclosed in exact rationals by small_volume_enclosure.py
    for lambda in [0.16, 6.76] -- the image of beta in [0.8, 2.6], THIS grid's range; it does not bound
    <d^2> and does not discharge the Lean grid hypotheses on `d2At 15`. Above beta = 2.6 nothing here is
    rigorous; PAPER Sec 13 states that and names the uniform <d^2> bound as the input that carries
    it. This dense grid is the corroborating measured evidence.
  * DESCRIPTIVE (drives NOTHING): a fixed low-degree polynomial overlay, reported only as a smoothness
    diagnostic (residual vs noise, empirical |d<d^2>/dbeta|). It is NOT the certificate -- the earlier
    "f + L*delta < B_16 with a fitted L = max|f'| and a pass-selected degree" form is retired, since a
    fitted slope cannot stand in for the rigorous finite-volume modulus.

WRITTEN PRECISION. The persisted upper `eb_upper_999` is rounded UP at its written precision
(`bound_str`), never to nearest: a written bound is what a reader compares against a threshold, and
rounding it toward the claim can carry it across. The mean and the bootstrap error are not bounds
and are written to nearest.
  DERIVED: the rounding DIRECTION, from the side of the bound -- away from the claim it supports.
  CHOSEN: 6 decimals of display precision; every verdict is computed on the unrounded value.

The read is DIRECT-LAG (no FFT): the whitened correlation is short-range, so <d^2> needs only the small lags,
read per config ONCE through the library's periodic lag profile (`entroptics_adapter.decay`), then the
bootstrap resamples the cheap averaging.  Light on CPU.

    CONFIGS=/path/to/entroptics-lattice python ym_crossover_confinement_of_grid.py
(or set CONFIGS once for the machine in the git-ignored local config file at the repository root)
"""
from __future__ import annotations

import csv
import glob
import math
import os
import sys

from decimal import ROUND_CEILING, ROUND_FLOOR, Decimal

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # research/code
from aperture_reads import load_su2   # one copy of the su2 shard loader
import entroptics_adapter as W       # THE WRAPPER: the lag profile is the library's
import store_path                    # the ONE place the ensemble store is located
from aperture_ceiling import APERTURE_RHS, d2_ceiling   # the ceiling, derived in ONE place

KAPPA0 = 0.25 * math.log(3.0)
L = 16
# The <d^2> ceiling the aperture condition implies. DERIVED in `aperture_ceiling`, which is where it
# is written and the only place it is: B < C_MAX (N+1)^2 with C_MAX = arccos(3^{-1/4})^2/(2 pi)^2,
# the SHARP constant of `Complete.confinement_at_of_substrate_sharp`.
#
# `N + 1` is the LAG ARITY -- `Moment.Read N` indexes lags by `Fin (N + 1)` and sets
# theta_d = 2 pi d / (N + 1). A periodic extent of L sites admits lags d = 0..L-1, so N + 1 = L and
# N = L - 1. This read `(L + 1)^2`, i.e. N + 1 = L + 1, which is the arity of a lattice one site
# larger than the one measured. That inflated the ceiling by ((L+1)/L)^2 = 1.13 -- 3.67 where the
# extent gives 3.2480 -- and every unit of that inflation made the certificate EASIER to pass.
B16 = d2_ceiling(L)
MAXLAG = L // 2
# Store root from ``store_path``: CONFIGS, then the git-ignored local config file, then a refusal
# -- no machine path in this file. Empty rather than raising when unconfigured, because the smoke
# tests import this module and redirect HOPS at a synthetic store; the refusal below says which.
ROOT = store_path.store_root(required=False)
HOPS = store_path.collections("configs_densebeta", "configs_phase1",
                              "configs_betasweep", "configs_ladder",
                              "configs_links_su2_density")
rng = np.random.default_rng(0)


def load(beta, ncap=256):
    return load_su2(HOPS, L, beta, ncap, dtype="float64")


def per_config_profiles(arr):
    """rho_i(d), d=0..L/2, per config: the grand-mean-connected spatial autocorrelation, averaged over the
    3 spatial axes and every other site of the configuration. Bootstrap then resamples the averaging.

    THE LAG PROFILE IS THE LIBRARY'S: `entroptics_adapter.decay(..., periodic=True)`, once per
    configuration and spatial axis. What this function states is convention, and each piece is forced:

      * the record for one axis is that axis FIRST and every other site of the configuration as a
        channel, because `decay` reads its first axis as the ordered one and SUMS the rest as
        exchangeable channels; dividing by the channel count makes that sum the mean over sites.
      * `periodic=True`, because the lattice closes along every spatial axis: each lag is averaged over
        all L pairs, with no taper and no 1/(L - d).
      * `disconnected=` the GRAND mean over every configuration and site, the vacuum this profile is
        connected against. Omitting it would subtract each record's own mean, which is a different
        object at every lag (`lattice_generator.connected_correlator` states the algebra).

    DERIVED: the half-extent comes from the ARRAY's own spatial axis, not from the module-level L, so
    this reads an ensemble at any aperture. That matters because the one open hypothesis in the proof
    (`Complete.confinement_of_bounded_substrate`) quantifies over APERTURES -- testing it means
    reading the same functional at several L, and a reader pinned to one L cannot do that. The lag
    arity is the periodic extent; the half-extent is where the circle distance turns around. A lag
    beyond an axis's own extent is taken modulo it, as a periodic shift is.
    """
    arr = np.asarray(arr)
    level = float(arr.mean(dtype=np.float64))         # the grand-mean vacuum, accumulated in float64
    n = arr.shape[0]
    maxlag = arr.shape[1] // 2
    lags = np.arange(maxlag + 1)
    P = np.zeros((n, maxlag + 1))
    for i in range(n):
        # DERIVED: 0, 1, 2 are the three spatial axes of ONE configuration (axes 1..3 of `arr`); the
        # last axis is time and is read as sites, not as a lag direction.
        for ax in (0, 1, 2):
            rec = np.moveaxis(arr[i], ax, 0)
            rec = rec.reshape(rec.shape[0], -1)
            prof = np.asarray(W.decay(rec, periodic=True, disconnected=level)) / rec.shape[1]
            P[i] += prof[lags % prof.shape[0]]
    # DERIVED: the three spatial axes averaged.
    P /= 3.0
    return P


def d2_from_profiles(P):
    """The lag second moment the Lean consumes: `Complete.d2At`, the CIRCLE-distance moment over the
    full periodic extent.

    WHY NOT THE RAW INDEX. This summed `p[d] * d * d` over `d = 0..MAXLAG` -- half the extent, with
    the raw index -- and that is a different quantity from the one the theorem bounds. `cos` is even
    and 2-pi periodic, so the read only ever sees `min(d, L-d)`; and on a periodic lattice
    `rho(L-1) = rho(1)`, so weighting the far half by `d^2` makes the moment grow like `L^2` even at
    a FIXED correlation length. A hypothesis bounding that is satisfiable by no physical correlation,
    gapped or not.

    The full profile is the measured half profile mirrored -- exact, not an approximation: every
    interior distance appears twice round the circle, the two endpoints once. So

        num = 2 * sum_{d=1}^{m-1} p[d] d^2  +  p[m] m^2
        den = p[0] + 2 * sum_{d=1}^{m-1} p[d]  +  p[m]

    with `m` the half-extent. DERIVED: `m` is read off the profile's own width, so this function no
    longer depends on a module-level lattice size and the SU(3) reader can import it rather than
    keep a second copy.
    """
    rho = P.mean(0)
    rho = rho / rho[0]
    p = np.clip(rho, 0, None)
    m = P.shape[1] - 1
    num = 2.0 * sum(p[d] * d * d for d in range(1, m)) + p[m] * m * m
    den = p[0] + 2.0 * sum(p[d] for d in range(1, m)) + p[m]
    # DERIVED: a division guard. A profile whose clipped weights sum to zero has no moment to
    # report; nothing is compared to a chosen size.
    return float(num / den) if den > 0 else 0.0


# The per-beta table is persisted as well as printed. Sec 9 reads this dense-grid certificate
# against Lean `Interior.ym_crossover_confinement_of_grid_sharp` (nominal confidence, SU(2) data; it does
# not discharge that theorem's hypotheses), but the grid itself reached the paper only through
# this program's stdout, so nothing could check it and `regen_all --verify` could not see it
# drift. The 13-point grid in 9_1_dat_d2_certified.csv is a different, coarser scan.
OUT_CSV = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                       "data", "9_3_dat_crossover_grid.csv")


def betas_available():
    found = set()
    for h in HOPS:
        for f in glob.glob(f"{h}/su2_L{L}_b*.npy"):
            found.add(round(float(os.path.basename(f).split("_b")[1].split(".s")[0]), 2))
    return sorted(found)


def eb(x, delta, side, span=None):
    """One-sided empirical-Bernstein confidence bound on E[x] (Maurer-Pontil 2009, Thm 4, the
    sample-variance form); side=+1 upper, -1 lower.

    WHAT THE THEOREM GUARANTEES. For n i.i.d. samples whose support lies in an interval of width R
    fixed IN ADVANCE, with m the sample mean, v the sample variance and L = log(2/delta),

        E[x] <= m + sqrt(2 v L / n) + 7 R L / (3 (n - 1))

    holds with probability at least 1 - delta, and the lower bound is the same theorem applied to
    -x. Each side is ONE-SIDED at 1 - delta; the 2 inside the logarithm is the theorem's own union
    over its variance and Bernstein events within one side, and does not buy the second side. The
    theorem's conditions are exactly those two, the i.i.d. draw and the a-priori width R.

    WHAT THIS COMPUTES. The interval is the library's `empirical_bernstein`; this function chooses
    only its width. By default (span=None) R is the SAMPLE range max(x) - min(x), passed to the
    library as `span`; it understates the support whenever the extremes were not sampled, and the
    samples here are per-configuration values from a Markov chain, independent only as far as the
    chain decorrelated between stored configurations. So the Thm 4 guarantee does not strictly
    apply to this bound: it is the theorem's expression with its width taken from the data, and
    its confidence 1 - delta is nominal. Passing `span`, an a-priori width of the samples' support,
    restores the width condition (independence stays the caller's to justify); the library refuses
    a `span` narrower than the observed range, since the samples then show that premise false.

    Here x is the per-config profile value at one lag (a spatial average over ~3*16^4 site-pairs,
    so tightly concentrated; its per-lag sample range is O(0.005-0.03) and the linear term is
    sub-dominant to the variance term).

    This is the tree's only copy: data/9_1_run_d2_certify.py imports it rather than restating it, so
    the certificate behind Sec 9 cannot be corrected in one place and left stale in the other."""
    x = np.asarray(x, dtype=float)
    # DERIVED: 2 is where a sample variance exists. The library refuses fewer samples, and a
    # non-finite one; this function's answer there is a NaN bound, which `d2_upper` reads as "no
    # enclosure" rather than letting it fall through as a bound of 0.
    if x.size < 2 or not np.all(np.isfinite(x)):
        return math.nan
    r = W.empirical_bernstein(x, delta, span=float(x.max() - x.min()) if span is None else span)
    return r.mean + side * r.radius


def bound_str(x, places, side):
    """A bound `x` written to `places` decimals, rounded AWAY from the claim it supports: up for an
    upper bound (side=+1), down for a lower bound (side=-1) -- the side convention of `eb`.

    Rounding to nearest can move a written bound toward the claim: an upper of 0.68882 written to
    4 decimals reads 0.6888, which is no longer an upper. The rounding is of the float's EXACT
    binary value (`Decimal(float)` is exact), so the written string is never on the claim's side of
    the computed bound. A non-finite bound has no digits to round and is written as it is.

    One copy: data/9_1_run_d2_certify.py writes its uppers through this too."""
    x = float(x)
    if not math.isfinite(x):
        return f"{x:.{places}f}"
    # DERIVED: +1 and -1 are the two sides of a one-sided bound, the convention `eb` takes.
    if side not in (1, -1):
        raise ValueError(f"side must be +1 (upper) or -1 (lower), got {side!r}")
    # DERIVED: +1 is the upper side, whose claim is "the true value is at most this" -- so up.
    mode =ROUND_CEILING if side == 1 else ROUND_FLOOR
    return format(Decimal(x).quantize(Decimal(1).scaleb(-places), rounding=mode), "f")


def ratio_box_max(pmax, w, d2):
    """The exact maximum of f(p) = sum_i w_i d2_i p_i / (1 + sum_i w_i p_i) over the box
    0 <= p_i <= pmax_i, for weights w_i > 0, d2_i >= 0 and pmax_i >= 0. A pure function.

    THE MAXIMISER IS A THRESHOLD VERTEX. Write N(p) and D(p) for the numerator and denominator; D >= 1
    on the box, and f is continuous on a compact set, so its maximum f* is attained. For any lambda,

        g(lambda) = max over the box of N(p) - lambda D(p) = sum_i w_i (d2_i - lambda)^+ pmax_i - lambda,

    because N - lambda D is linear in p with coefficient w_i (d2_i - lambda) on p_i, so each p_i sits
    at pmax_i when that coefficient is positive and at 0 when it is negative. Since D > 0,
    f(p) <= lambda iff N(p) - lambda D(p) <= 0, so f* <= lambda iff g(lambda) <= 0. At lambda = f*:
    g(f*) <= 0 from that equivalence, and g(f*) >= N(p*) - f* D(p*) = 0 at a maximiser p*, so
    g(f*) = 0 -- and it is attained at p_i = pmax_i where d2_i > f*, p_i = 0 where d2_i < f*, either
    where d2_i = f* (coefficient zero). That point has N - f* D = 0, i.e. f = f*. It is the vertex
    "every lag whose d2 is at least some threshold c at pmax, the rest at 0". Every such vertex is in
    the box, so no vertex exceeds f*, and some vertex attains it:

        f* = max over the distinct values c of d2 (and the empty set, f = 0) of f(threshold vertex c).

    That is at most (number of distinct d2) + 1 evaluations, each exact up to float rounding; this
    evaluates all of them rather than searching for the root of g.

    The sign argument is also why the all-upper corner is the answer at small values: if its value t
    is at most min(d2), every coefficient d2_i - t is non-negative, so g(t) = N(pmax) - t D(pmax) = 0
    and f* = t.
    """
    pmax = [float(x) for x in pmax]
    w = [float(x) for x in w]
    d2 = [float(x) for x in d2]
    if not (len(pmax) == len(w) == len(d2)):
        raise ValueError("pmax, w and d2 must have one entry per lag")
    # DERIVED: the proof's premises, checked rather than assumed -- w_i > 0 and d2_i >= 0 and
    # 0 <= pmax_i < inf, which also refuses NaN (every comparison with NaN is False).
    if not all(x > 0 and x < math.inf for x in w):
        raise ValueError(f"weights must be positive and finite: {w}")
    # DERIVED: as above, the premises d2_i >= 0 and 0 <= pmax_i < inf.
    if not all(x >= 0 and x < math.inf for x in d2 + pmax):
        raise ValueError(f"d2 and pmax must be non-negative and finite: {d2}, {pmax}")
    # DERIVED: the empty-set vertex p = 0, where f = 0 / 1; it is in the box and bounds f* from below.
    best = 0.0
    for c in sorted(set(d2)):
        on = [i for i in range(len(d2)) if d2[i] >= c]
        num = sum(w[i] * d2[i] * pmax[i] for i in on)
        # DERIVED: 1 is rho(0)/rho(0), the lag-0 term of the denominator.
        den = 1.0 + sum(w[i] * pmax[i] for i in on)
        best = max(best, num / den)
    return best


def d2_upper(P, delta):
    """Upper bound on <d^2> at NOMINAL confidence 1 - delta per beta: a one-sided empirical-Bernstein
    bound per lag (`eb`), union-bounded over the K lags (delta/K each), propagated EXACTLY through
    the ratio functional by maximising it over the box those bounds license. The confidence is
    nominal for the reasons `eb` states -- the sample range stands in for the a-priori support
    width, and the configurations are treated as i.i.d. -- so the Maurer-Pontil guarantee does not
    strictly apply.

    THE BOX. The union bound buys K one-sided events: rho_0 >= lo_0 (lower side of lag 0) and
    rho_d <= hi_d for d = 1..m (upper side of every other lag). The read weights p_d =
    max(rho_d, 0)/rho_0 then satisfy 0 <= p_d <= pmax_d = max(hi_d, 0)/lo_0 whenever lo_0 > 0, for
    EVERY rho_0 >= lo_0 -- so rho_0 needs no scan: taking it at lo_0 is the enclosure of all of them,
    and scanning rho_0 over [lo_0, hi_0] could only shrink the box while spending an upper event on
    lag 0 that the union does not buy. The lower bounds lo_d on the other lags are outside the union
    too, which is why the lower face of the box is 0 and not lo_d/rho_0. When lo_0 <= 0 no finite
    enclosure exists and this returns inf.

    THE MAXIMUM. On that box the read is f(p) = sum w_d d^2 p_d / (1 + sum w_d p_d) with the
    circle-distance mirroring weights w_d, and `ratio_box_max` returns its exact maximum (the proof
    is in its docstring: the maximiser is the vertex with p_d = pmax_d for d^2 above the maximum and
    0 below it). While the all-upper corner value t is at most 1 = min d^2, every lag is above the
    maximum and the corner IS the maximum, so t is returned unchanged. Above 1 the lag-1 direction
    flips (lowering rho_1 raises the read) and the maximum sits at a vertex with the short lags at 0,
    strictly above t whenever pmax_1 > 0.

    The same certificate as data/9_1_run_d2_certify.py."""
    K = P.shape[1]; dp = delta / K
    # DERIVED: the read needs lag 0 and at least one lag beside it.
    if K < 2:
        raise ValueError(f"a profile needs lag 0 and at least one more lag; got {K} column(s)")
    lo0 = eb(P[:, 0], dp, -1)
    # DERIVED: a non-positive lower bound on rho(0) leaves the ratio p_d = rho_d/rho_0 unbounded.
    # Written `not lo0 > 0` so a NaN bound (a NaN sample, or a single configuration, whose sample
    # variance is NaN) also has no enclosure, instead of falling through as a bound of 0.
    if not lo0 > 0:
        return math.inf
    hi = [eb(P[:, d], dp, +1) for d in range(1, K)]
    # DERIVED: a NaN upper would pass through max(0.0, nan) as 0 -- the same silent zero -- and an
    # infinite one leaves the box unbounded; either way there is no finite enclosure.
    if not all(math.isfinite(h) for h in hi):
        return math.inf
    # pmax[i] is the certified upper corner of rho(lag i+1)/rho(0), for lags 1..m.
    pmax = [max(0.0, h / lo0) for h in hi]
    m = K - 1
    # DERIVED: the same circle-distance mirroring `d2_from_profiles` uses, so the BOUND is a bound on
    # the quantity the theorem consumes rather than on a truncated cousin of it. Every interior lag
    # appears twice round the periodic extent, the two endpoints once; rho(0)/rho(0) = 1 is the
    # leading term of the denominator.
    num = 2.0 * sum(pmax[d - 1] * d * d for d in range(1, m)) + pmax[m - 1] * m * m
    den = 1.0 + 2.0 * sum(pmax[d - 1] for d in range(1, m)) + pmax[m - 1]
    t = num / den
    # DERIVED: 1 is the smallest lag weight d^2 (d = 1). At or below it every coefficient d^2 - t is
    # non-negative, so the all-upper corner is the box maximum (`ratio_box_max`, last paragraph) and
    # t is returned bit for bit as computed.
    if t <= 1.0:
        return t
    # DERIVED: 2 and 1 are the mirroring multiplicities above -- interior lags twice, the endpoint once.
    w = [2.0] * (m - 1) + [1.0]
    return max(t, ratio_box_max(pmax, w, [float(d * d) for d in range(1, m + 1)]))


def main():
    print(f"kappa0 {KAPPA0:.4f}   aperture RHS 1-3^-1/4 = {APERTURE_RHS:.4f}   <d^2> threshold B_16 = {B16:.3f}\n")
    xs, ys, es, us, ns = [], [], [], [], []
    print(f"{'beta':>5} {'n':>4} | {'<d^2>':>7} {'+-boot':>7} {'eb99.9up':>9}")
    absent = []
    for b in betas_available():
        arr = load(b)
        if arr is None:
            absent.append(b)
            continue
        P = per_config_profiles(arr)
        n = P.shape[0]
        bs = W.bootstrap(P, d2_from_profiles, draws=200, rng=rng)   # continues the module `rng`
        u = d2_upper(P, 0.001)                     # nominal 99.9%-per-beta empirical-Bernstein upper
        xs.append(b); ys.append(float(np.mean(bs))); es.append(float(np.std(bs))); us.append(u)
        ns.append(n)
        print(f"{b:>5.2f} {n:>4} | {ys[-1]:>7.4f} {es[-1]:>7.4f} {u:>9.3f}")
    xs, ys, es, us = map(np.array, (xs, ys, es, us))
    if len(xs) < 4:
        print("\n(need >=4 beta points -- generation not synced yet?)"); return

    # ---- THE CERTIFICATE: an empirical-Bernstein upper bound at every measured beta ----
    # <d^2>(beta) <= u(beta) at NOMINAL per-beta probability 1 - 1e-3: the Maurer-Pontil guarantee
    # needs i.i.d. configurations and an a-priori support width, and `eb` plugs in the sample range,
    # so it does not strictly apply (see `eb`). No fit enters.
    # The interior clears iff every u(beta) sits under the aperture
    # threshold B16. No fitted curve, no fitted slope, no degree selection enters this verdict.
    umax = float(np.nanmax(us))
    clears = bool((us < B16).all())
    print(f"\n[certificate] max_beta  eb-99.9%-upper = {umax:.3f}  {'<' if clears else '>='}  B_16 = {B16:.3f}"
          f"   -> interior {'CLEARS' if clears else 'FAILS'}"
          + (f"  ({B16/umax:.0f}x margin)" if umax > 0 else ""))
    # NOT "forall beta". `small_volume_enclosure.py` certifies lambda in [0.16, 6.76], which is the
    # image of beta in [0.8, 2.6] under lambda = c*beta^2 -- the SAME range this grid measures, not a
    # larger one. The previous wording said the enclosure discharged every coupling, which would have
    # made the grid redundant rather than corroborating, and is not what the enclosure claims.
    print(f"   a different quantity is enclosed INTERVAL-rigorously ON THE CROSSOVER IMAGE by the")
    print(f"   single-plaquette enclosure (small_volume_enclosure.py, exact Sturm/Feshbach): beta in")
    print(f"   [0.8, 2.6] maps to lambda in [0.16, 6.76], exactly the range it certifies. Above")
    print(f"   beta = 2.6 nothing here is rigorous -- PAPER Sec 13 states that and names what carries")
    print(f"   it (the uniform <d^2> bound, which is an INPUT there and not a reading).")
    print(f"   This dense grid is corroborating measured evidence + the empirical modulus of")
    print(f"   continuity, not the rigorous step.")

    # ---- DESCRIPTIVE smoothness overlay (drives NO verdict): is <d^2>(beta) a smooth curve? ----
    # CHOSEN-BUT-DERIVABLE: 0.75 is beta_c = kappa_0/(2r) frozen as a literal -- same defect as
    # interior_mixing_of_analytic_grid.py L125. Should be computed from kappa_0 and r.
    # CHOSEN-BUT-DERIVABLE: 0.75 is beta_c = kappa_0/(2r) frozen as a literal -- same defect as
    # interior_mixing_of_analytic_grid.py. Should be computed, not written down.
    interior = xs >= 0.75
    xf, yf = xs[interior], ys[interior]
    deg = min(3, len(xf) - 1)                      # FIXED low degree; not selected to pass anything
    c = np.polyfit(xf, yf, deg)
    resid = float(np.max(np.abs(np.poly1d(c)(xf) - yf)))
    slope = float(np.abs(np.poly1d(c).deriv()(np.linspace(xf.min(), xf.max(), 500))).max())
    ni = float(np.mean(es[interior]))
    print(f"\n[descriptive] deg-{deg} interpolant over the interior: max residual {resid:.4f} vs boot err "
          f"{ni:.4f} ({'within noise, smooth' if resid < 3 * ni else 'exceeds noise'}); empirical "
          f"|d<d^2>/dbeta| ~ {slope:.3f}, far below the rigorous finite-volume modulus 1/4*(L/2)^2*2*N_p.")
    print(f"=> ym_crossover_confinement_of_grid: every beta's nominal-confidence upper "
          f"{'clears' if clears else 'does NOT clear'} B_16; descriptive smoothness above.")

    # Persist the measured grid. A beta whose shards are missing is a refusal, not a shorter grid:
    # the certificate is "every measured beta clears", so a silently smaller grid weakens the claim
    # while still reading as a pass.
    if absent:
        raise SystemExit(("shards missing for beta %s: refusing to write a partial crossover grid"
                          % ", ".join("%.2f" % b for b in absent))
                         + "\n" + store_path.hint())
    with open(OUT_CSV, "w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(["beta", "nconfigs", "d2_mean", "d2_boot_err", "eb_upper_999"])
        for b, n, y, e, u in zip(xs, ns, ys, es, us):
            # DERIVED: the upper is rounded UP (`bound_str`, side +1); the mean and the bootstrap
            # error are not bounds and stay to nearest. CHOSEN: 6 decimals, display only.
            w.writerow(["%.2f" % b, int(n), "%.6f" % y, "%.6f" % e, bound_str(u, 6, +1)])
    print("wrote %s (%d couplings)" % (OUT_CSV, len(xs)))


if __name__ == "__main__":
    main()
