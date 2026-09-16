"""The Lean theorem, evaluated on the ensemble: a QUANTITATIVE bound on the gapless weight.

WHAT IS BEING CERTIFIED. `ZeroMode.zero_mode_lt_of_tension` (machine-checked, footprint = the three
foundational axioms) says that for a correlation split as `rho = c + g` with `c, g >= 0`,

    mu < kappa_0   =>   c * (N+1) < (3^(1/4) - 1) * sum_d g(d)

and crucially it says this at a SINGLE aperture. No limit, no extrapolation, no `forall large N`.
So one measured volume turns into a number: measure the tension and the gapped weight, and the
theorem hands back a ceiling on how much of the correlation can sit at `lambda = 1` -- the gapless
component. That is the first place in this program where the formalisation produces a quantity
rather than an implication.

WHY IT IS A TEST AND NOT A CALCULATION. `c` is also measured directly, as the antipodal lag: the
farthest point on the circle, the only lag the periodic geometry distinguishes, no threshold. So the
theorem's ceiling and the measurement are two independent routes to the same quantity, and they can
DISAGREE. If the measured `c` ever exceeded the bound, one of three things would be wrong -- the
theorem, the measurement, or the `rho = c + g` decomposition reflection positivity supplies. This
script checks that they do not, at every volume, and refuses if they do.

WHAT IT DOES NOT CLAIM. A bound on the gapless WEIGHT is not a mass gap. `c -> 0` says no mode sits
at `lambda = 1`; a positive decay RATE additionally needs the modes not to accumulate there, which on
a finite lattice follows from the transfer matrix being finite-dimensional and is not established
here. Nor is the aperture condition's being satisfied evidence of confinement: `mu` is small at these
volumes because the connected correlation is contact-scale, a resolution property, and the U(1)
control showed the same read does not separate a confining theory from a massless one. The theorem's
CONCLUSION is valid regardless of why its hypothesis holds; that conclusion is a ceiling on `c`.

DERIVED THROUGHOUT. `kappa_0 = (1/4) log 3` is proved in `Floor.lean`; `3^(1/4) - 1` is
`e^{kappa_0} - 1`, the same constant rearranged. `c` is the antipodal lag and `g = rho - c`. The lag
arity is the ensemble's own periodic extent. Nothing is fitted and no tolerance appears.
"""
from __future__ import annotations

import csv
import glob
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))

import store_path                                   # noqa: E402
import ym_crossover_confinement_of_grid as CG       # noqa: E402

BASE = store_path.store_root(required=False)
SUBS = ("configs_phase1", "configs_betasweep", "configs_ladder",
        "configs_paper83", "configs_densebeta")

#: DERIVED: the entropy floor proved in `Floor.lean`, and the same constant as `e^{kappa_0} - 1`.
KAPPA0 = 0.25 * math.log(3.0)
K_FLOOR = 3.0 ** 0.25 - 1.0

#: CHOSEN: configurations per volume, held EQUAL across volumes. It costs the width of the read, not
#: its direction -- but it must not vary with L, because the lag moment is inflated by noise and a
#: varying config count manufactures a volume trend. That confound produced a spurious slope once in
#: this program's history and is the reason this is one number rather than "whatever each L holds".
NCAP = 120

#: DERIVED: the coupling whose volume tower the released ensembles cover.
BETA = 2.30

#: DERIVED: the largest configuration count the STRONG-COUPLING tower holds at every volume it
#: shares with the physical one (beta=0.50 carries 64, 64, 96 at L=8, 12, 16). The control
#: compares two couplings, so the count must be equal on both sides and at every volume --
#: a varying count manufactures a range difference out of noise, which is the confound that
#: produced two false results in this program's history.
CTRL_NCAP = 64


def load(group, L, beta, cap):
    arrs, got = [], 0
    for sub in SUBS:
        for f in sorted(glob.glob(os.path.join(BASE or "", sub,
                                               "%s_L%d_b%.2f.s*.npy" % (group, L, beta)))):
            a = np.load(f, mmap_mode="r")
            take = min(a.shape[0], cap - got)
            # DERIVED: the cap is already met, so there is nothing left to take -- a loop
            # terminator, not a threshold on any measured quantity.
            if take <= 0:
                break
            arrs.append(np.asarray(a[:take], dtype=np.float32))
            got += take
        if got >= cap:
            break
    if not arrs:
        return None, 0
    return np.concatenate(arrs, 0), got


def read_profile(P, n):
    """`(mu, c, G)` from the connected half-extent profile.

    `c` is the antipodal lag -- the farthest separation the circle has, and the only one its
    geometry singles out. `g = rho - c` is what remains, and `G` normalises by the contact value so
    it is dimensionless and comparable across volumes. `mu = -log <cos theta>` is the tension the
    theorem's hypothesis is about, formed on the folded circle exactly as `Moment.Read` forms it.
    """
    rho = P.mean(0)
    r0 = rho[0]
    c = rho[-1]
    d = np.arange(n)
    circ = np.minimum(d, n - d)
    full = rho[np.minimum(circ, len(rho) - 1)]
    G = float((full - c).sum() / r0)
    # THE LEAN'S PRECONDITION IS NOT EXACTLY MET, AND THIS IS WHERE THAT SHOWS. `Moment.Read`
    # carries `hρ : ∀ d, 0 ≤ ρ d`, but the measured connected profile dips slightly negative at
    # lags near the antipode -- consistent with zero (the deepest dip is under 1σ at 10⁴
    # configurations) yet present in any finite sample. Clipping is the minimal repair that makes
    # the measured profile a legal `Read`, and it is not free: negative `ρ` near `d = n/2` sits
    # where `cos` is also negative, so those terms ADD to the first moment, and removing them
    # lowers `⟨cos θ⟩` and RAISES `μ`. Measured, that is the whole difference between this read and
    # `9_3_dat_substrate_of_aperture.csv`: unclipped, this pipeline reproduces that artifact's `mu`
    # to six decimals at matched configurations; clipped, it runs 3.5-10% higher.
    #
    # Both are reported. The bound itself is unaffected -- `G` is formed from the unclipped profile
    # and the hypothesis `μ < κ₀` holds by a factor of ~80 either way -- so the certificate's
    # conclusion does not rest on the choice. What rests on it is honesty about a precondition the
    # data satisfies only up to noise.
    p = np.clip(full, 0.0, None)
    tot = p.sum()
    # DERIVED: a nonpositive total weight has no probability vector and therefore no tension.
    # This is the absence of a read, not a cut applied to one.
    if tot <= 0:
        return float("nan"), float("nan"), float("nan"), float("nan")
    p = p / tot
    ca = float((p * np.cos(2.0 * np.pi * d / n)).sum())
    # DERIVED: the logarithm needs a positive argument. A nonpositive cosine average means the
    # tension is not defined (Lean's `cosAvg_gt_of_tension_lt_floor` carries the same proviso),
    # so it is reported as infinite rather than silently read as zero.
    mu = -math.log(ca) if ca > 0 else float("inf")
    # the same read WITHOUT the clip -- the quantity `9_3` publishes, carried so the
    # precondition repair is visible in the artifact rather than only in this comment
    # DERIVED: the same validity tests as the clipped read above -- a nonpositive total has no
    # probability vector, and the logarithm needs a positive argument. Neither thresholds a
    # measured quantity; both mark where the read is undefined.
    q = full / full.sum() if full.sum() > 0 else full
    ca_raw = float((q * np.cos(2.0 * np.pi * d / n)).sum())
    # DERIVED: the logarithm needs a positive argument; this marks where the read is undefined.
    mu_raw = -math.log(ca_raw) if ca_raw > 0 else float("inf")
    return mu, float(c / r0), G, mu_raw


def main() -> int:
    if not BASE:
        raise SystemExit("zero_mode_bound_of_measurement: no ensemble store configured.\n"
                         + store_path.hint())
    rows = []
    print("ZeroMode.zero_mode_lt_of_tension, evaluated on the ensemble (beta=%.2f, %d configs each)"
          % (BETA, NCAP))
    print("  mu < kappa0=%.5f  =>  c <= (3^(1/4)-1) * G / (N+1),  K = %.5f" % (KAPPA0, K_FLOOR))
    print()
    print("%4s %7s %10s %8s %10s %14s %14s %8s"
          % ("L", "ncfg", "mu", "mu<k0", "G", "bound on c", "measured c", "holds"))
    for L in (8, 12, 16, 20, 24, 28, 32):
        A, got = load("su2", L, BETA, NCAP)
        if A is None or got < NCAP:
            continue
        P = CG.per_config_profiles(A)
        del A
        mu, c, G, mu_raw = read_profile(P, L)
        if mu != mu:
            continue
        hyp = mu < KAPPA0
        bound = K_FLOOR * G / L
        # the theorem only speaks when its hypothesis holds; where it does, the measurement must obey
        holds = (not hyp) or (c < bound)
        print("%4d %7d %10.5f %8s %10.4f %14.5f %14.6f %8s"
              % (L, got, mu, "yes" if hyp else "NO", G, bound, c, "yes" if holds else "NO"))
        rows.append(dict(group="su2", beta="%.2f" % BETA, L=L, nconfigs=got,
                         mu="%.6f" % mu, mu_unclipped="%.6f" % mu_raw,
                         kappa0="%.6f" % KAPPA0,
                         hypothesis_holds=("1" if hyp else "0"),
                         sum_g="%.5f" % G, bound_on_c="%.6f" % bound,
                         measured_c="%.6f" % c,
                         theorem_respected=("1" if holds else "0")))
        if not holds:
            raise SystemExit(
                "zero_mode_bound_of_measurement: at L=%d the measured c=%.6f EXCEEDS the theorem's "
                "bound %.6f while the hypothesis mu=%.5f < kappa0 holds. That is a contradiction "
                "between a machine-checked theorem and the measurement, and it must be resolved "
                "rather than reported: either the read, the c+g split, or the ensemble is wrong."
                % (L, c, bound, mu))

    # ---- positive control: the regime where the answer is already known --------------------
    # Every other check here is a negative control or an internal consistency test. This one asks
    # whether the apparatus gives the CLASSICALLY KNOWN answer where one exists. At strong coupling
    # the plaquettes decouple, so the connected correlation collapses to a pure contact term and
    # `sum g` -> 1 exactly (all weight at lag zero, nothing beyond). At the physical coupling there
    # is genuine structure and `sum g` sits above 1. If the read cannot tell those apart it is not
    # measuring correlation range, and nothing else in this file would notice.
    #
    # Stated as a COMPARISON of two measured quantities, not a threshold: the strong-coupling
    # correlation must be shorter-ranged than the physical one, at matched volume and matched
    # statistics. No cut is chosen.
    ctrl = []
    for L in (8, 12, 16):
        a_s, n_s = load("su2", L, 0.50, CTRL_NCAP)
        a_p, n_p = load("su2", L, BETA, CTRL_NCAP)
        if a_s is None or a_p is None or n_s < CTRL_NCAP or n_p < CTRL_NCAP:
            continue
        gs = read_profile(CG.per_config_profiles(a_s), L)[2]
        gp = read_profile(CG.per_config_profiles(a_p), L)[2]
        del a_s, a_p
        ctrl.append((L, gs, gp))
    if ctrl:
        print()
        print("POSITIVE CONTROL -- strong coupling, where confinement is classical "
              "(Osterwalder-Seiler):")
        print("%4s %16s %16s %14s" % ("L", "sum g @0.50", "sum g @%.2f" % BETA, "shorter?"))
        for L, gs, gp in ctrl:
            print("%4d %16.4f %16.4f %14s" % (L, gs, gp, "yes" if gs < gp else "NO"))
        bad = [L for L, gs, gp in ctrl if not gs < gp]
        if bad:
            raise SystemExit(
                "zero_mode_bound_of_measurement: at L=%s the strong-coupling correlation is NOT "
                "shorter-ranged than the physical one. Strong coupling decouples the plaquettes, so "
                "this is the one place the answer is known independently -- a read that fails here is "
                "not measuring correlation range, and every other number in this file is suspect."
                % bad)
        print("   strong coupling gives sum g -> 1 (pure contact, trivially gapped), as it must.")

    if not rows:
        raise SystemExit("zero_mode_bound_of_measurement: no volume reached %d configurations; "
                         "refusing to write a table the comparison cannot support." % NCAP)

    Gs = [float(r["sum_g"]) for r in rows]
    print()
    print("sum g over the tower: %.4f to %.4f (spread %.2f%%) -- the aperture-free B the theorem needs"
          % (min(Gs), max(Gs), 100.0 * (max(Gs) / min(Gs) - 1.0)))
    print("the bound falls as 1/L at fixed G, which is the squeeze the theorem describes.")

    out = os.path.join(os.path.dirname(os.path.dirname(HERE)), "data",
                       "9_9_dat_zero_mode_bound.csv")
    with open(out, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)
    print("\nwrote %s (%d volumes)" % (os.path.basename(out), len(rows)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
