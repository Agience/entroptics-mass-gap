"""The confinement certificate on the DEFINITIONAL route: certify the read's cosine average.

WHAT THIS CERTIFIES. `Complete.confinement_at_of_cosAvg`:

    3^{-1/4} < <cos theta>_p   ==>   mu < kappa0 = (1/4) log 3

and `Complete.confinement_at_iff_cosAvg` proves those are the SAME statement, not one implying the
other. So this is not a weaker or a stronger reading of confinement at a given aperture and coupling
-- it is confinement at that aperture and coupling, restated in the quantity a measurement produces.

WHY NOT THE SECOND-MOMENT CERTIFICATE. `ym_crossover_confinement_of_grid` certifies a bound on the
lag second moment and feeds `Complete.confinement_of_substrate_bound`, which passes through
`1 - x^2/2 <= cos x`. That inequality is SUFFICIENT, not equivalent, and the moment it needs cannot
be certified as one scalar: it is a ratio whose numerator and denominator both mix every lag, so the
bound has to corner each lag ratio separately at delta/K and then square the far ones. Measured on
this same sweep the two costs are not comparable:

    inequality step (central d2 -> mu)         1.15x to 1.5x
    certifying d2 (central -> EB upper)        5x to 66x

The moment route stays -- it takes a hypothesis about the SUBSTRATE, holding at every aperture, and
returns the limit, which no measurement at one aperture can do. This route takes one aperture and
returns that aperture. They answer different questions.

THE STATISTIC. With p = rho/sum(rho) over the full periodic extent,

    <cos theta>_p = sum_d rho(d) cos(2 pi d / L) / sum_d rho(d) = S(2pi/L) / S(0)

Both S(0) and S(2pi/L) are means over configurations of a per-configuration quantity, so the whole
statistic takes THREE empirical-Bernstein bounds at delta/3 -- the numerator from below and the
denominator from both sides -- and the ratio is evaluated at the minimising corner of that box.
Against the moment route's bound-per-lag, that is a union over three rather than over the arity.

DERIVED THROUGHOUT. The comparison value 3^{-1/4} is exp(-kappa0) with kappa0 = (1/4) log 3 proved
in `Floor.lean` from a directed-cube path count -- it is the floor rewritten, not a tolerance. The
momentum 2pi/L is the lowest nonzero mode the periodic extent admits. The split of delta across the
two bounds is by count of bounds. No threshold, lag window, or fitted scale appears.
"""
from __future__ import annotations

import csv
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import ym_crossover_confinement_of_grid as CG  # the store reader and the EB bound

L = CG.L
KAPPA0 = 0.25 * math.log(3.0)          # Floor.lean: the derived entropy floor
COS_FLOOR = math.exp(-KAPPA0)          # = 3^{-1/4}, the floor rewritten as a cosine average


def per_config_terms(P):
    """Per configuration: (S(2pi/L), S(0)) of the full periodic profile.

    `P[i, d]` is configuration `i`'s correlation at lag `d` for `d = 0..L/2`. On a periodic extent
    rho(L-d) = rho(d) exactly, so the full profile is this one mirrored -- every interior lag twice,
    the two endpoints once. That mirroring is an identity of the geometry, not an extrapolation.
    """
    m = P.shape[1] - 1
    full = np.concatenate([P, P[:, 1:m][:, ::-1]], axis=1)     # lags 0..L-1
    assert full.shape[1] == 2 * m, (full.shape, m)
    w = np.cos(2.0 * np.pi * np.arange(2 * m) / (2 * m))
    return full @ w, full.sum(axis=1)


def cos_avg(P):
    """The central value of <cos theta>_p, on the ensemble-mean profile."""
    a, b = per_config_terms(P)
    return float(a.mean() / b.mean())


def cos_avg_lower(P, delta):
    """A certified lower bound on <cos theta>_p at confidence 1 - delta.

    The exact monotone minimum of `a / b` over the certified box, rather than one fixed corner.
    Three empirical-Bernstein bounds -- the numerator from below, the denominator from both sides --
    at delta/3 each, so the union bound is by COUNT OF BOUNDS and no confidence is reused.

    WHY THE SIGN TEST IS NOT DECORATION. `num_lo / den_hi` is the minimum only while the numerator's
    lower bound is nonnegative. Once it goes negative, dividing by the LARGER denominator makes it
    LESS negative -- an upper bound wearing a lower bound's name. The minimising corner is then
    `num_lo / den_lo`. On this sweep the numerator corner never goes negative, so the branch is
    inert here; it is written because a certificate that is only sound on the data it was written
    against is not a certificate.

    `den_lo > 0` is required rather than `den_hi > 0`: the ratio is a bound on a positive-denominator
    quantity only if the denominator is CERTIFIED positive, and `den_hi > 0` does not establish that.
    """
    a, b = per_config_terms(P)
    dp = delta / 3.0
    num_lo = CG.eb(a, dp, -1)
    den_lo = CG.eb(b, dp, -1)
    den_hi = CG.eb(b, dp, +1)
    # DERIVED: a sign test, not a threshold. The ratio bounds a positive-denominator quantity
    # only if the denominator is certified positive; zero is where that stops being true.
    if den_lo <= 0:
        return -math.inf
    # DERIVED: zero is where the minimising corner of a/b changes which denominator bound it
    # takes -- above it the larger denominator minimises, below it the smaller one does.
    return num_lo / den_hi if num_lo >= 0 else num_lo / den_lo


def mu_upper(P, delta):
    """The certified upper bound on the tension, mu = -log <cos theta>."""
    lo = cos_avg_lower(P, delta)
    # DERIVED: the domain of the logarithm. A nonpositive certified average bounds the tension
    # by nothing, which is what infinity reports.
    return math.inf if lo <= 0 else -math.log(lo)


def main() -> None:
    betas = CG.betas_available()
    if not betas:
        raise SystemExit(
            "ym_confinement_of_cos_average: the SU(2) sweep matched no configurations. Refusing to\n"
            "report a certificate with no ensemble behind it.")

    # DERIVED: one confidence per certificate reported, each a fixed power of ten so the reader can
    # see how the margin degrades as the demand tightens. No value is a pass/fail threshold -- the
    # verdict is the comparison to COS_FLOOR at each.
    deltas = [1e-6, 1e-12, 1e-30]

    print(f"SU(2) L={L}   kappa0 = (1/4)log3 = {KAPPA0:.6f}   floor on <cos> = 3^(-1/4) = {COS_FLOOR:.6f}")
    print(f"{'beta':>6} {'<cos> central':>14} {'mu central':>11} "
          + " ".join(f"{'mu<=@' + f'{d:g}':>14}" for d in deltas))

    rows = []
    for b in betas:
        arr = CG.load(b)
        if arr is None:
            continue
        P = CG.per_config_profiles(arr)
        c = cos_avg(P)
        # DERIVED: the domain of the logarithm, as in `mu_upper`.
        mu = -math.log(c) if c > 0 else math.inf
        ups = [mu_upper(P, d) for d in deltas]
        rows.append((b, c, mu, ups, P.shape[0]))
        print(f"{b:6.2f} {c:14.6f} {mu:11.6f} "
              + " ".join(f"{u:14.6f}" if math.isfinite(u) else f"{'vacuous':>14}" for u in ups))

    print()
    for i, d in enumerate(deltas):
        fails = [(f"{b:.2f}", ups[i]) for b, _, _, ups, _ in rows if not (ups[i] < KAPPA0)]
        worst = max((ups[i] for _, _, _, ups, _ in rows if math.isfinite(ups[i])), default=math.inf)
        # DERIVED: a division guard. A nonpositive worst-case tension is already below the floor,
        # so the margin it reports is unbounded.
        margin = KAPPA0 / worst if worst > 0 else math.inf
        verdict = "CONFINED at every coupling" if not fails else f"NOT certified at {fails}"
        print(f"delta={d:g}: worst certified mu = {worst:.6f}  vs kappa0 = {KAPPA0:.6f} "
              f"({margin:.1f}x margin) -- {verdict}")

    nmin = min(r[4] for r in rows)
    print(f"\n{len(rows)} couplings, >= {nmin} configurations each. The certified statement at each row is\n"
          f"`Complete.confinement_at_of_cosAvg`, whose hypothesis is exactly the column above.")

    # The artifact, so the paper quotes a table rather than restating a run's stdout. Written only
    # after the refusal above, so a run that matched no ensemble cannot overwrite a committed table
    # with an empty one and still exit 0.
    out = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                       "data", "9_2_dat_confinement_cos.csv")
    with open(out, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["beta", "nconfigs", "cos_avg_central", "mu_central"]
                   + [f"mu_upper_delta_{d:.0e}" for d in deltas]
                   + [f"confined_delta_{d:.0e}" for d in deltas]
                   + ["kappa0", "cos_floor"])
        for b, c, mu, ups, n in rows:
            w.writerow([f"{b:.2f}", n, f"{c:.6f}", f"{mu:.6f}"]
                       + [f"{u:.6f}" if math.isfinite(u) else "inf" for u in ups]
                       + ["yes" if u < KAPPA0 else "NO" for u in ups]
                       + [f"{KAPPA0:.6f}", f"{COS_FLOOR:.6f}"])
    print(f"wrote {os.path.relpath(out)}")


if __name__ == "__main__":
    main()
