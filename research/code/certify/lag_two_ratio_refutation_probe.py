"""REFUTATION PROBE for the lag-two ratio `rho(2) <= K * rho(0)`, at extent four or extent six.

`--extent` selects which obligation is probed, and the threshold comes from the Lean declaration
that owns THAT extent -- they are different numbers against different theorems:

    extent 4  `LagTwoBound.confines_of_lag_two_ratio`     K < lagTwoThreshold    ~ 0.018623
    extent 6  `LagTwoSix`, via `ClayAssembly.I1_lagTwo`   K < lagTwoThresholdSix ~ 0.033796

`K_BY_EXTENT` below carries both, and every row records the `K_claim` it was judged against, so a
stored result cannot be read against the wrong bar. The sections below describe the object at
extent four; at extent six the same construction runs on a 6^4 torus, where lag two is no longer
half the extent.

WHAT THIS CAN AND CANNOT DO. It can REFUTE. It cannot support. If the measured `rho(2)/rho(0)`
reaches or exceeds the threshold for its extent at any coupling, that extent's hypothesis is false
at that coupling and the route is dead. If it never does, NOTHING is established: the data failed to
refute over the couplings actually sampled, the Lean obligation is untouched, and no number from
here may enter a proof or be fitted to.

## The object, read off the Lean definitions

`MassGap/Complete.lean`:   wilsonCorrAt N beta = fun d => WilsonBridge.corrClay (N+1) beta d
`MassGap/WilsonBridge.lean`:
    corrClay n beta lag      = corrHyper (d:=4) 3 n 0 1 2 beta lag
    corrHyper Nc n mu nu tau = wilsonCorrConn (Nc:=Nc) (WilsonHypercubic.bd (d:=4) (n:=n))
                                 ((mu,nu), origin) beta ((mu,nu), siteAtHyper tau lag)
    wilsonCorrConn bd p0 beta p = <phi_p0 phi_p> - <phi_p0><phi_p>
    wilsonPlaqObs = wilsonDensity o wilsonHol,  wilsonDensity g = 1 - Re tr g / Nc

So, with `N = 3` (the row's aperture), `n = N+1 = 4`:

  * FOUR-dimensional periodic lattice, extent 4 in EVERY direction: a 4^4 torus.
  * Gauge group SU(3); `Nc = 3`.
  * phi_p = 1 - Re tr(U_p)/3 for the elementary plaquette holonomy
    U_mu(x) U_nu(x+mu) U_mu(x+nu)^dag U_nu(x)^dag.
  * BOTH plaquettes span the SAME plane (0,1). The lag runs along direction 2, transverse to it.
    This is ONE ORDERED PAIR of plaquettes, not a timeslice average and not a sum over planes.
  * CONNECTED: the disconnected product <phi><phi> is subtracted.
  * The lag index is `Fin 4`, so d = 0,1,2,3 and d = 2 is HALF the extent.

Translation averaging over x, and averaging over the twelve symmetry-equivalent channels (six
planes {mu,nu}, two transverse directions tau each), are exact identities of this expectation under
the lattice translation and axis symmetries the measure carries
(`WilsonHypercubic.axisSymmetry`), not a change of object. Each channel is also reported on its own
so that the identity can be checked rather than assumed, and the canonical Lean channel
(plane (0,1), lag along 2) is reported separately.

## THE COUPLING CONVENTION, which is not the generator's

`WilsonHypercubic.Plaq d n = (Fin d x Fin d) x Site d n` is an ORDERED direction pair, and
`System.action` sums `phi` over ALL of them. Degenerate pairs mu = nu retrace and contribute
`phi(1) = 0`; the pair (nu,mu) is the (mu,nu) loop INVERTED, and `Re tr g^-1 = Re tr g` on SU(N), so
it contributes the same `phi`. Hence

    S_Lean = 2 * sum_{mu<nu} (1 - Re tr U_p / 3)   and the weight is exp(-beta_Lean * S_Lean).

`lattice_generator._sun_sweep` / `_sun_cm_pass` use `dS = -(beta/N) Re tr(dU A)` with `A` the sum of
staples over `nu != mu`, forward and backward -- i.e. the STANDARD Wilson weight
`exp(+(beta/3) sum_{mu<nu} Re tr U_p)`. Matching exponents:

    beta_Lean = beta_generator / 2.

Both are reported on every row. The verdict is stated in the LEAN convention, because `0.018623` is
stated against `wilsonCorrAt 3 beta d`.

## Uncertainty

From REPRODUCIBILITY: several fully independent runs per coupling, each with its own master seed,
its own thermalisation and its own chains. The reported sigma is the standard error of the ratio
ACROSS those runs. No within-run formula is used anywhere.

## The disconnected subtraction is estimated without bias

`(sample mean)^2` estimates `<phi>^2` with an UPWARD bias equal to the variance of that mean --
`E[mbar^2] = <phi>^2 + Var(mbar)` -- so subtracting it biases `rho` DOWNWARD at every lag by
`Var(mbar)`, which is of the same order as `rho(2)` itself. The estimator used here is the
cross-chain product
`(  (sum_i m_i)^2 - sum_i m_i^2 ) / (B(B-1))` over INDEPENDENT chains i at a fixed snapshot, whose
expectation is exactly `<phi>^2`. The naive value is reported alongside so the size of the
difference is visible rather than assumed small.

## WHERE THE LAG PROFILE COMES FROM

`entroptics.reads.decay`, reached the way every read in this tree is reached -- through
`entroptics_adapter`, which is the one place the library version, the call convention and the
question of WHICH COPY answered are pinned. The record is the one the lag direction defines: that
direction is the ORDERED axis, of extent 4, and every other coordinate together with every Markov
chain is pooled as one exchangeable feature channel. Two arguments are what make the returned
profile the Lean object rather than a window statistic about it.

  * `periodic=True`. The lag is taken MODULO the extent, so every lag is averaged over all four
    ordered pairs and `C(d) == C(n-d)` holds in floating point by construction. That is what a
    `4^4` torus is, and `MomentShape.corrClay_neg` proves the target has it. There is no taper and
    no `1/(n-d)`: either would weight lag 2 differently from lag 0 and put a window choice back
    into a quantity the Lean statement has none in.
  * `disconnected=None`. The read removes NO level; the disconnected term is subtracted afterwards
    by the cross-chain estimator described above. `wilsonCorrConn`'s disconnected part is
    `<phi_p0><phi_p>`, a product of ENSEMBLE expectations, and the record's own mean is a
    different number -- a read that centred on it would return a different correlator at every
    lag, not a noisier estimate of this one.

    The TRUE `<phi>`, handed over as `disconnected=`, would be exactly right and unbiased. It is
    also not available: only estimates of it are, and a level is removed BEFORE the pairs are
    formed, so what an estimate `L` puts into the correlator is `2 L mbar - L^2` with `mbar` the
    record's own mean, and not `L^2`. At `L = mbar` that is the naive estimator to the last bit,
    carrying the full `-Var(mbar)` -- measured at `-0.98 Var(mbar)` on `rho(0)` and
    `-1.00 Var(mbar)` on `rho(1)` in 1.2e5 draws of a record of this shape, against `+0.01` and
    `+0.00` for the cross-chain route and for the true level. And `A(d) - disc` is not
    `disconnected=L` for any `L` the record offers: that would need `2 L mbar - L^2 = disc`,
    whose root `mbar -/+ sqrt(mbar^2 - disc)` is not a level of anything and is not real whenever
    the unbiased estimate exceeds the naive one. So the lag average is taken as a read and the
    disconnected term is estimated ACROSS CHAINS, which is a pairing no single level can express.

`decay` sums over feature channels (`sum_f C_f`), so the profile is divided by the channel count
to make it the translation-and-chain AVERAGE this expectation is. The adapter reads the two
keywords off the loaded function rather than off a version string, and the file that answered is
printed on every run, because a working tree and an installed wheel have carried the same string.

The `roll` calls in `plaq_field` are the neighbour SHIFTS the plaquette holonomy is made of --
`U_nu(x + mu)`, `U_mu(x + nu)` -- not a correlation. They build the field; nothing about which
distance, which normalisation, which window or which floor is decided there.

## Controls

  * `rho(d) = rho(n-d)` is PROVED in Lean (`MomentShape.corrClay_neg`) and it is ALSO an identity
    of the estimator, so agreement between `rho(1)` and `rho(3)` is arithmetic and not evidence:
    averaging over every translation already carries `phi(x) phi(x + 3e)` term by term onto
    `phi(x) phi(x - e)`, and the periodic read returns the mirrored half rather than recomputing
    it. Both are reported so that the identity is visible rather than implied.
  * At `beta = 0` the links are independent Haar and the two plaquettes at any `d >= 1` share no
    link, so `rho(d >= 1) = 0` EXACTLY. That is the null this instrument must read.
  * `rho(0) > 0` at every coupling is the positive control (`PlaqVariance.corrClay_zero_pos`).
  * The mean plaquette is reported so it can be held against the known SU(3) values.
  * The per-plane sum of the plaquette field is checked against `_sun_action` within
    `TOL_IDENTITY`, which is the empty band between the rounding the two summation orders can
    differ by and the smallest quantity this file reports. It is a CODE check, so it runs on the
    first run of each coupling in `scan` mode and not on every sample.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import time

# CHOSEN: one thread. The compute host is shared with other live sessions and numpy has taken 18 of
# 22 cores there before. The kernel is 3x3 matrix products over a 4^4 lattice, far below the size at
# which a threaded BLAS pays for itself, so several single-threaded coupling jobs in parallel use
# the box better than one threaded job -- and a job that takes one core cannot starve a neighbour.
# Set before numpy is imported, which is the only point at which it binds.
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS",
           "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")

try:
    os.nice(19)
except (AttributeError, OSError):
    pass

import numpy as np                                                       # noqa: E402

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import entroptics_adapter as EA                                          # noqa: E402
import lattice_generator as LG                                           # noqa: E402

#: DERIVED: the extent is `N+1` for `wilsonCorrAt N`, and row B5 is at `N = 3`. Four directions
#: because the Clay problem is four-dimensional; `corrClay` fixes `d := 4`.
#:
#: `--extent` rebinds this and `DIMS` before anything runs. Extent four remains the default so
#: every existing invocation returns what it returned before; extent SIX is the one
#: `ClayAssembly.ClayRemaining.I1_lagTwo` and `LagTwoSix.LagTwoRatioSix` are actually stated at, and
#: no Monte Carlo has ever been run there.
EXTENT = 4
DIMS = (EXTENT,) * 4
GROUP = "su3"
#: DERIVED: `WilsonBridge.corrClay` fixes `Nc = 3` -- the Clay problem's gauge group. Not a size
#: anyone here picked; it is the `3` in `corrHyper (d := 4) 3 n 0 1 2`.
NC = 3
#: CHOSEN: the residual tolerance of the identity check `sum_planes phi == _sun_action`. The two
#: routes add the same six plaquette densities in different orders, so they can differ only by
#: rounding, of order `len(PLANES) * eps ~ 1.3e-15`; the smallest quantity this file reports is
#: `rho(0) ~ 3e-6`, at the weakest coupling sampled. Any value between those two scales returns the
#: identical verdict, so what choosing it costs is nothing -- it is the width of an empty band, not
#: a cut placed in the data.
TOL_IDENTITY = 1e-10
#: DERIVED: the threshold `LagTwoBound.lagTwoThreshold_gt` puts the bound above. Not a tuning knob:
#: it is the number the hypothesis is stated against.
K_CLAIM = 0.018623

#: DERIVED: the extent-six threshold is `LagTwoSix.lagTwoThresholdSix = vSix^2 = 0.03379588...`,
#: a closed form, and `lagTwoThresholdSix_gt` machine-checks `0.0337 <` it.
#:
#: ROUNDED AWAY FROM THE CLAIM THIS FILE CAN MAKE. The only verdict a measurement is allowed to
#: reach here is REFUTATION -- `ratio > threshold` at every admissible `K` -- so the threshold is
#: rounded UP, to `0.03380 > 0.03379588...`. That makes refutation strictly HARDER to declare. The
#: Lean bound `0.0337` is rounded DOWN and would make it easier, which is why it is not used.
K_CLAIM_SIX = 0.03380

#: DERIVED: the threshold each extent's obligation is stated against, keyed by extent. Nothing is
#: interpolated: an extent absent from this table has no Lean threshold behind it and the probe
#: refuses rather than inventing one.
K_BY_EXTENT = {4: K_CLAIM, 6: K_CLAIM_SIX}

#: DERIVED: the six unordered planes of a four-dimensional lattice.
PLANES = [(mu, nu) for mu in range(4) for nu in range(mu + 1, 4)]
#: DERIVED: every (plane, transverse direction) pair. Twelve of them, all equivalent under the axis
#: symmetry; the Lean channel is ((0,1), 2).
CHANNELS = [(p, tau) for p in PLANES for tau in range(4) if tau not in p]
LEAN_CHANNEL = CHANNELS.index(((0, 1), 2))


def plaq_field(b, U):
    """phi_{mu nu}(x) = 1 - Re tr U_p / 3 for every unordered plane, shape (6, *batch, *dims).

    The holonomy is built with the same expression `_sun_action` uses, so the per-plane field sums
    to the generator's own action density (asserted by the caller).
    """
    out = []
    # NOT A READ: the loop is over the six PLANES of the lattice, not over separations, and the two
    # `roll` calls inside it are the neighbour shifts the plaquette holonomy is made of --
    # `U_nu(x + mu)` and `U_mu(x + nu)`. What comes out is the field phi, not a profile of it: no
    # distance, no normalisation, no window and no floor is decided here. The lag average over phi is
    # `EA.decay` in `_measure`, and that is the read.
    for (mu, nu) in PLANES:
        Umu = U[..., mu, :, :]
        Unu = U[..., nu, :, :]
        Up = (Umu @ b.roll(Unu, -1, LG._sax(mu, 2))
              @ LG._dag(b, b.roll(Umu, -1, LG._sax(nu, 2))) @ LG._dag(b, Unu))
        out.append(1.0 - b.real(b.trace(Up)) / NC)
    return np.stack(out, axis=0)


def _measure(phi):
    """Per-snapshot accumulators from phi of shape (6, B, *DIMS).

    Returns `A` of shape (len(CHANNELS), EXTENT) -- `<phi_p(x) phi_p(x + d e_tau)>` averaged over
    every translation and every chain, read through `EA.decay` -- and `m` of shape (6, B), the
    translation-averaged single plaquette, kept PER CHAIN because the disconnected estimator needs
    chains it can pair across.
    """
    # DERIVED: `phi` carries the plane on axis 0 and the chain on axis 1, so `2` is where its
    # spacetime axes begin and `1` is the offset from a lattice direction to that direction's axis
    # of `f`. Both are read off the shape the caller built; neither is a size anyone picked.
    sax = tuple(range(2, 2 + len(DIMS)))                     # the spacetime axes of phi
    m = phi.mean(axis=sax)                                   # (6, B)
    # The normalisation below counts the columns handed IN. `decay` would drop a fully non-finite
    # column before summing, which would leave the divisor one too large -- so the record is
    # required to be finite rather than assumed to be, and a field that is not says so here.
    if not np.isfinite(phi).all():
        raise SystemExit("the plaquette field is not finite; a dropped channel would leave the "
                         "read normalised by a column count that no longer matches")
    A = np.empty((len(CHANNELS), EXTENT))
    for ci, (plane, tau) in enumerate(CHANNELS):
        f = phi[PLANES.index(plane)]                         # (B, *DIMS)
        # DERIVED: the record this channel hands the read -- the lag direction as the ORDERED
        # axis, every other coordinate and every chain pooled as one exchangeable feature channel.
        # The chain axis sits at 0 of `f`, so lattice direction `tau` is axis `1 + tau`; it is
        # moved to `0` because that is where `decay` reads the ordered axis, and `-1` is numpy's
        # "whatever is left" and not a length. All three follow the array's shape.
        W = np.moveaxis(f, 1 + tau, 0).reshape(EXTENT, -1)
        # DERIVED: the divisor is this record's own column count. `decay` returns `sum_f C_f` over
        # feature channels; the expectation is an AVERAGE over sites and chains, so the sum is
        # divided by however many of them the record carries. Nothing is picked: change the chain
        # count or the extent and the divisor follows.
        A[ci] = EA.decay(W, periodic=True, disconnected=None) / W.shape[1]
    return A, m


def run_point(beta_gen, seed, *, chains, snaps, gap, therm, start="hot", check=False):
    """One independent run at generator coupling `beta_gen`. Returns the per-channel rho.

    `chains` INDEPENDENT Markov chains are evolved in parallel from one seed, thermalised for
    `therm` sweeps, then sampled `snaps` times with `gap` sweeps between samples. Chains are
    independent; snapshots within a chain are not, which is why the uncertainty is taken across
    RUNS and never from within one.
    """
    b = LG._Backend(None).seed(seed)
    init, sweep, action, dstep = LG._ops(GROUP, "heatbath")
    bt = (int(chains),)
    U = LG.cold_init(b, GROUP, DIMS, bt) if start == "cold" else init(b, DIMS, bt)
    for _ in range(therm):
        sweep(b, U, DIMS, beta_gen, dstep)

    Asum = np.zeros((len(CHANNELS), EXTENT))
    disc = np.zeros(len(PLANES))
    msum = np.zeros(len(PLANES))
    B = int(chains)
    for _s in range(snaps):
        for _ in range(gap):
            sweep(b, U, DIMS, beta_gen, dstep)
        phi = plaq_field(b, U)
        if check:
            ref = action(b, U)
            err = float(np.max(np.abs(phi.sum(axis=0) - ref)))
            if err > TOL_IDENTITY:
                raise SystemExit(f"plaquette field disagrees with _sun_action by {err:g}")
        A, m = _measure(phi)
        Asum += A
        # unbiased <phi>^2: products of DISTINCT independent chains only
        tot = m.sum(axis=1)
        disc += (tot * tot - (m * m).sum(axis=1)) / (B * (B - 1))
        msum += m.mean(axis=1)
    Asum /= snaps
    disc /= snaps
    msum /= snaps

    rho = np.empty((len(CHANNELS), EXTENT))
    rho_naive = np.empty((len(CHANNELS), EXTENT))
    naive_sq = msum ** 2                                     # the BIASED disconnected estimate
    for ci, (plane, _tau) in enumerate(CHANNELS):
        pi = PLANES.index(plane)
        rho[ci] = Asum[ci] - disc[pi]
        rho_naive[ci] = Asum[ci] - naive_sq[pi]
    return {
        "beta_gen": float(beta_gen),
        "beta_lean": float(beta_gen) / 2.0,
        "seed": int(seed),
        "start": start,
        "rho_chan": rho.tolist(),
        "rho_avg": rho.mean(axis=0).tolist(),
        "rho_lean_chan": rho[LEAN_CHANNEL].tolist(),
        "rho_naive_avg": rho_naive.mean(axis=0).tolist(),
        "phi_mean": float(msum.mean()),
        "plaq_mean": float(1.0 - msum.mean()),
    }


def _stats(vals):
    v = np.asarray(vals, dtype=float)
    n = len(v)
    mean = float(v.mean())
    # DERIVED: a sample standard deviation at `ddof=1` is undefined below two values, so the `1` is
    # the arity that estimator requires and not a cut on anything measured. It is a GUARD: nothing
    # about the data decides it, and no value of it can change a reported number.
    if n > 1:
        sd = float(v.std(ddof=1))
        return mean, sd / np.sqrt(n), sd
    return mean, float("nan"), float("nan")


def scan(betas, *, runs, chains, snaps, gap, therm):
    rows = []
    for beta in betas:
        t0 = time.time()
        pts = []
        for i in range(runs):
            # DERIVED: the plaquette-field identity check runs once per coupling rather than once
            # per run, because it verifies the CODE and not the sample. `0` names the first run; it
            # is an index, not a threshold, and nothing measured decides it.
            first_run = (i == 0)
            pts.append(run_point(beta, 100000 + 977 * i + int(round(beta * 1000)), chains=chains,
                                 snaps=snaps, gap=gap, therm=therm, check=first_run))
        rho = np.array([p["rho_avg"] for p in pts])                      # (runs, EXTENT)
        rho_lean = np.array([p["rho_lean_chan"] for p in pts])
        ratio2 = rho[:, 2] / rho[:, 0]
        ratio1 = rho[:, 1] / rho[:, 0]
        ratio3 = rho[:, 3] / rho[:, 0]
        ratio2_lean = rho_lean[:, 2] / rho_lean[:, 0]
        r2m, r2se, r2sd = _stats(ratio2)
        r1m, r1se, _ = _stats(ratio1)
        r3m, r3se, _ = _stats(ratio3)
        rlm, rlse, _ = _stats(ratio2_lean)
        rho0m, rho0se, _ = _stats(rho[:, 0])
        rho2m, rho2se, _ = _stats(rho[:, 2])
        # DERIVED: a division guard, not a cut. `0` is the denominator value at which the quotient
        # is undefined, and `r2se == r2se` is the NaN test `_stats` returns when a single run leaves
        # the across-run spread unestimable. Neither excludes any measurement.
        sigma_from_k = float((r2m - K_CLAIM) / r2se) if (r2se == r2se and r2se > 0) else None
        # DERIVED: a refutation needs the measured ratio ABOVE the threshold by more than the
        # across-run spread can explain. `3` standard errors is the width demanded before the word
        # is used; it is a GUARD on the verdict and makes refutation harder, never easier, and no
        # measured number depends on it.
        refutes = bool(r2se == r2se and r2se > 0 and (r2m - 3.0 * r2se) > K_CLAIM)
        row = {
            "extent": EXTENT, "K_claim": K_CLAIM, "refutes_at_3se": refutes,
            "beta_gen": float(beta), "beta_lean": float(beta) / 2.0,
            "runs": runs, "chains": chains, "snaps": snaps, "gap": gap, "therm": therm,
            "plaq_mean": float(np.mean([p["plaq_mean"] for p in pts])),
            "rho0": rho0m, "rho0_se": rho0se, "rho2": rho2m, "rho2_se": rho2se,
            "ratio2": r2m, "ratio2_se": r2se, "ratio2_sd": r2sd,
            "ratio1": r1m, "ratio1_se": r1se, "ratio3": r3m, "ratio3_se": r3se,
            "ratio2_leanchannel": rlm, "ratio2_leanchannel_se": rlse,
            "ratio2_naive": float(np.mean([p["rho_naive_avg"][2] / p["rho_naive_avg"][0]
                                           for p in pts])),
            "sigma_from_K": sigma_from_k,
            "per_run_ratio2": ratio2.tolist(),
            "rho_avg_runs": rho.tolist(),
            "secs": round(time.time() - t0, 1),
        }
        rows.append(row)
        print(json.dumps({"row": row}), flush=True)
    return rows


def main():
    global EXTENT, DIMS, K_CLAIM
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", default="scan", choices=("scan", "therm", "bench"))
    ap.add_argument("--betas", default="0,1,2,4,6,8,12,20,40,80")
    ap.add_argument("--runs", type=int, default=6)
    ap.add_argument("--chains", type=int, default=64)
    ap.add_argument("--snaps", type=int, default=16)
    ap.add_argument("--gap", type=int, default=4)
    ap.add_argument("--therm", type=int, default=300)
    ap.add_argument("--extent", type=int, default=EXTENT,
                    help="periodic extent in all four directions (4 or 6)")
    ap.add_argument("--out", default=None,
                    help="write the scan rows here as JSON; without it nothing is persisted")
    a = ap.parse_args()
    betas = [float(x) for x in a.betas.split(",")]

    if a.extent not in K_BY_EXTENT:
        raise SystemExit(f"extent {a.extent} has no Lean threshold behind it; "
                         f"known extents are {sorted(K_BY_EXTENT)}")
    # DERIVED: the generator's heat-bath checkerboard requires an even extent
    # (`lattice_generator._require_even_for_heatbath`); `2` is that parity and not a size.
    if a.extent % 2 != 0:
        raise SystemExit("the heat-bath checkerboard requires an even extent")
    EXTENT = int(a.extent)
    DIMS = (EXTENT,) * 4
    K_CLAIM = K_BY_EXTENT[EXTENT]

    # Which library answered, not which version claims to have. A working tree and an installed
    # wheel have reported the same version string, and only one of them has the read this file
    # calls, so the path is printed with every run and travels with the output.
    print(json.dumps({"reader": {"entroptics": EA.LIBRARY_FILE,
                                 "version": EA.LIBRARY_VERSION,
                                 "python": sys.executable},
                      "lattice": {"extent": EXTENT, "dims": list(DIMS), "group": GROUP,
                                  "K_claim": K_CLAIM}}), flush=True)

    if a.mode == "bench":
        t0 = time.time()
        p = run_point(betas[0], 1, chains=a.chains, snaps=a.snaps, gap=a.gap, therm=a.therm,
                      check=True)
        print(json.dumps({"bench": {"secs": round(time.time() - t0, 1), "point": p}}))
        return 0

    if a.mode == "therm":
        out = []
        for beta in betas:
            for start in ("hot", "cold"):
                for therm in (a.therm, 4 * a.therm):
                    p = run_point(beta, 4242, chains=a.chains, snaps=a.snaps, gap=a.gap,
                                  therm=therm, start=start)
                    rec = {"beta_gen": beta, "start": start, "therm": therm,
                           "plaq_mean": p["plaq_mean"],
                           "rho0": p["rho_avg"][0], "rho2": p["rho_avg"][2],
                           "ratio2": p["rho_avg"][2] / p["rho_avg"][0]}
                    out.append(rec)
                    print(json.dumps({"therm": rec}), flush=True)
        print(json.dumps({"therm_all": out}))
        return 0

    rows = scan(betas, runs=a.runs, chains=a.chains, snaps=a.snaps, gap=a.gap, therm=a.therm)
    print(json.dumps({"scan": rows}))
    if a.out:
        payload = {"extent": EXTENT, "dims": list(DIMS), "group": GROUP, "nc": NC,
                   "K_claim": K_CLAIM, "lean_channel": list(CHANNELS[LEAN_CHANNEL][0]),
                   "reader": EA.LIBRARY_FILE, "reader_version": EA.LIBRARY_VERSION,
                   "rows": rows}
        with open(a.out, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, indent=1, sort_keys=True)
        print(json.dumps({"wrote": a.out, "rows": len(rows)}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
