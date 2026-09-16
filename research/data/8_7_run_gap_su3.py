"""The transfer gap on SU(3): the second gauge group for the identification test.

WHY. `junction_residuals_of_measurement` tests the step that carries `mu < kappa0` to a gap in the
ACTUAL modes, by holding the measured transfer gap against the measured margin:

    Delta  >=  kappa0 - mu

It passes at every point where both resolve -- but every one of those points is SU(2). A composite
that holds on one gauge group and has never been looked at on another is weaker evidence than it
looks, because nothing in it distinguishes a property of the argument from a property of SU(2).

WHAT THIS ADDS. The same `delta()` read the SU(2) points use, on the SU(3) ensembles the store
holds, at the (L, beta) where a tension is already measured -- so every new row is directly
comparable and none of it is a fresh choice. `delta()` was already group-agnostic; only the shard
loader was not, and it now takes the group as a parameter rather than gaining a second copy.

The jackknife is over the same config bins the SU(2) scan uses, so the error bar means the same
thing on both groups and the resolution rule can be applied to both without a second convention.

DERIVED: the couplings and volumes are whatever the store holds for SU(3), intersected with the
points that already carry a tension -- nothing is selected for being favourable. A point whose gap
does not resolve is reported as unresolved rather than dropped silently.
"""
import csv
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "code"))

import store_path
from aperture_reads import delta, load_su2   # the one gap read and the one shard loader
import entroptics_adapter as W   # the wrapper: resampling is the library's, not a local copy

BASE = store_path.store_root(required=False)
HOPS = [os.path.join(BASE, d) for d in ("configs_paper83", "configs_phase1")] if BASE else []

#: DERIVED: the (L, beta) SU(3) points that already carry a measured tension, so each new gap is
#: directly comparable to a margin. Read from the aperture scan rather than restated.
SCAN = os.path.join(HERE, "9_3_dat_substrate_of_aperture.csv")

#: CHOSEN: configurations per point. It costs read time and the width of the jackknife band, not
#: validity -- a cap set too low surfaces as a wider error bar, which the resolution rule then
#: excludes rather than mistaking for a result.
NCAP = 128

#: DERIVED: the jackknife bin count the SU(2) scan uses, so an error bar means the same thing on
#: both groups and one resolution rule applies to both.
NBINS = 8

#: DERIVED: the resolution rule Sec 8.7b states, the same tolerance
#: `certify/junction_residuals_of_measurement` applies when it decides which points can be
#: compared. Reported here so a reader sees which rows will survive that rule; the rule is
#: applied there, not here.
RESOLUTION_TOL = 0.25


def points():
    if not os.path.exists(SCAN):
        raise SystemExit(f"8_7_run_gap_su3: {os.path.basename(SCAN)} is not present. It names the "
                         f"points a gap here can be compared against; without it this would be "
                         f"measuring at couplings chosen here instead.")
    out = []
    with open(SCAN, newline="") as f:
        for r in csv.DictReader(f):
            # DERIVED: a nonpositive tension is a read on noise, with no margin to compare a gap to.
            if r["group"] == "su3" and float(r["mu"]) > 0:
                out.append((int(r["L"]), float(r["beta"])))
    return sorted(set(out))


def main() -> None:
    if not BASE:
        raise SystemExit("8_7_run_gap_su3: no ensemble store configured.\n" + store_path.hint())
    pts = points()
    if not pts:
        raise SystemExit("8_7_run_gap_su3: no SU(3) point carries a tension, so no gap here could "
                         "be compared against a margin. Refusing to measure into a vacuum.")

    print(f"SU(3) transfer gap at the {len(pts)} points that already carry a tension")
    print(f"{'L':>4} {'beta':>6} {'n':>5} {'Delta':>10} {'err':>9} {'err/val':>8} {'resolved':>9}")
    rows = []
    for L, beta in pts:
        field = load_su2(HOPS, L, beta, NCAP, group="su3")
        if field is None:
            print(f"{L:>4} {beta:>6.2f}   (no shards)")
            continue
        n = field.shape[0]
        # DERIVED: a jackknife needs at least as many configurations as bins.
        if n < NBINS:
            print(f"{L:>4} {beta:>6.2f} {n:>5}   (fewer configurations than jackknife bins)")
            continue
        # The LIBRARY's jackknife, binned the way the SU(2) scan bins. A local copy would
        # re-decide how the groups are formed and what the (G-1)/G factor applies to.
        D, D_se = W.jackknife(field, delta, n_bins=NBINS)
        D, D_se = float(D), float(D_se)
        # DERIVED: the domain of the division. A nonpositive gap has no relative error and is
        # reported as unresolved, which is what it is.
        rel = D_se / D if D > 0 else float("inf")
        rows.append((L, beta, n, D, D_se))
        print(f"{L:>4} {beta:>6.2f} {n:>5} {D:>10.4f} {D_se:>9.4f} {rel:>8.2f} "
              f"{'yes' if rel <= RESOLUTION_TOL else 'no':>9}")

    if not rows:
        raise SystemExit("8_7_run_gap_su3: no SU(3) point produced a gap; refusing to write an "
                         "empty table over a committed one.")

    out = os.path.join(HERE, "8_7_dat_gap_su3.csv")
    with open(out, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["group", "L", "beta", "nconfigs", "Delta", "Delta_err"])
        for L, beta, n, D, se in rows:
            w.writerow(["su3", L, f"{beta:.2f}", n, f"{D:.6f}", f"{se:.6f}"])
    print(f"\nwrote {os.path.basename(out)}  ({len(rows)} points)")


if __name__ == "__main__":
    main()
