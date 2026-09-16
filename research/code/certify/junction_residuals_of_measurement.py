"""The gapped identification, tested: does the measured margin lower-bound the measured transfer gap?

WHY THIS IS THE STEP THAT MATTERS. The flagship `ym_mass_gap_of_ratio` reaches its conclusion through
a model whose mass is DEFINED as exp(-(kappa0 - mu)). The correlator then decays exactly when
mu < kappa0, so that link restates its own hypothesis and carries no physics: it is a definitional
witness standing in for a transfer-matrix eigenvalue.

`ym_mass_gap_of_junction` removes the witness. It takes an ARBITRARY mode family and asks for two
residuals instead:

    hfe :  kappa0 - mu <= c        the centre-vortex free-energy junction
    hgap:  c <= Delta              the contraction rate lower-bounds the transfer gap

Their composite is one testable statement -- the measured MARGIN lower-bounds the measured TRANSFER
GAP:

    Delta  >=  kappa0 - mu

Both sides are measured in this tree and had never been held against each other. `Delta` is the
variational transfer gap of `8_7_dat_mhi_multicoupling.csv`, read from the gap correlator with no
model of the potential; `mu` is the tension of `9_3_dat_substrate_of_aperture.csv`, the same
functional the Lean consumes. Neither was produced with this comparison in mind.

WHAT THIS DOES AND DOES NOT ESTABLISH. It does not prove `hfe` or `hgap` -- they remain open, and the
contraction constant `c` between them is not measured here, only the composite they imply. What it
does is turn the identification step from an untested assumption into one with direct evidence, at
every coupling where both quantities resolve.

DERIVED THROUGHOUT. `kappa0 = (1/4)log3` is proved in `Floor.lean`. The resolution rule is the one
Sec 8.7b already states -- a gap is resolved when its own relative error is at or under the rule's
tolerance -- and unresolved points are EXCLUDED rather than counted, because a gap whose error
exceeds its value carries no information either way. The comparison is made at Delta - 2 sigma, so a
pass is a pass at the measurement's own uncertainty rather than at its central value.
"""
from __future__ import annotations

import csv
import math
import os

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(os.path.dirname(os.path.dirname(HERE)), "research", "data")
if not os.path.isdir(DATA):
    DATA = os.path.join(os.path.dirname(os.path.dirname(HERE)), "data")

KAPPA0 = 0.25 * math.log(3.0)

#: The resolution rule Sec 8.7b states: a mode is resolved when err/value is within this.
#: DERIVED from the paper's own variational rule, not chosen here -- the same tolerance
#: `test_paper_matches_artifacts._variational` applies when it selects the variational bound.
RESOLUTION_TOL = 0.25

#: DERIVED: two standard errors, the band the paper quotes every measured gap at. The comparison is
#: made at the LOW end of that band, so a pass survives the measurement's own uncertainty.
SIGMA = 2.0


def _rows(name):
    p = os.path.join(DATA, name)
    if not os.path.exists(p):
        raise SystemExit(f"junction_residuals_of_measurement: {name} is not present under {DATA}.\n"
                         f"Both artifacts are required; this script measures nothing itself and "
                         f"refuses to report a comparison with one side missing.")
    with open(p, newline="") as f:
        return list(csv.DictReader(f))


def main() -> None:
    # BOTH gap sources and BOTH groups. The SU(2) scan predates the SU(3) one and carries no
    # group column, so its rows are keyed as su2; the SU(3) file names its own group. A test
    # over only the half that existed first cannot tell a property of the argument from a
    # property of SU(2).
    delta = {}
    for r in _rows("8_7_dat_mhi_multicoupling.csv"):
        delta[("su2", int(r["L"]), "%.2f" % float(r["beta"]))] = (float(r["Delta"]),
                                                                 float(r["Delta_err"]))
    for r in _rows("8_7_dat_gap_su3.csv"):
        delta[(r["group"], int(r["L"]), "%.2f" % float(r["beta"]))] = (float(r["Delta"]),
                                                                       float(r["Delta_err"]))
    mu = {}
    for r in _rows("9_3_dat_substrate_of_aperture.csv"):
        mu[(r["group"], int(r["L"]), r["beta"])] = float(r["mu"])

    shared = sorted(set(delta) & set(mu))
    if not shared:
        raise SystemExit("junction_residuals_of_measurement: no (L, beta) carries both a transfer "
                         "gap and a tension, so the identification cannot be tested. Refusing to "
                         "report a verdict with nothing behind it.")

    print("THE GAPPED IDENTIFICATION, MEASURED")
    print("  hfe:  kappa0 - mu <= c      hgap:  c <= Delta      composite:  Delta >= kappa0 - mu")
    print(f"  kappa0 = (1/4)log3 = {KAPPA0:.6f}   (Floor.lean, derived)")
    print()
    print(f"{'group':>6} {'L':>4} {'beta':>6} {'mu':>10} {'margin':>10} {'Delta':>10} "
          f"{'err/val':>8} {'Delta-2s':>10} {'ratio':>8} {'holds':>7}")

    rows, unresolved = [], []
    for k in shared:
        d, e = delta[k]
        margin = KAPPA0 - mu[k]
        # DERIVED: a nonpositive gap has no sign to compare, and one whose error exceeds the
        # rule's share of it carries no information either way. Zero is the domain, not a cut.
        if d <= 0 or e / d > RESOLUTION_TOL:
            unresolved.append((k, d, e))
            continue
        lo = d - SIGMA * e
        holds = lo >= margin
        rows.append(dict(group=k[0], L=k[1], beta=k[2], mu=mu[k], margin=margin, delta=d,
                         err=e, lo=lo, holds=holds))
        print(f"{k[0]:>6} {k[1]:>4} {k[2]:>6} {mu[k]:>10.5f} {margin:>10.5f} {d:>10.4f} "
              f"{e / d:>8.2f} {lo:>10.4f} {lo / margin:>8.1f} {'yes' if holds else 'NO':>7}")

    print()
    if not rows:
        print("  NO POINT RESOLVES its transfer gap; the identification is untested on this "
              "evidence, which is not the same as untrue.")
    else:
        failed = [r for r in rows if not r["holds"]]
        tight = min(r["lo"] / r["margin"] for r in rows)
        if failed:
            print(f"  {len(failed)} of {len(rows)} resolved points FAIL Delta-2sigma >= margin: "
                  f"{[(r['group'], r['L'], r['beta']) for r in failed]}")
            print("  The composite of hfe and hgap is contradicted where it can be measured.")
        else:
            print(f"  ALL {len(rows)} resolved points satisfy Delta - {SIGMA:g}sigma >= kappa0 - mu")
            print(f"  tightest margin: the measured transfer gap exceeds the required one by "
                  f"{tight:.1f}x at its own lower error bar")
    if unresolved:
        print(f"  excluded, gap unresolved (err/val > {RESOLUTION_TOL}): "
              + ", ".join(f"{k[0]} L={k[1]} beta={k[2]} (Delta={d:.3f}+/-{e:.3f})"
                          for k, d, e in unresolved))

    out = os.path.join(DATA, "9_6_dat_junction_residuals.csv")
    with open(out, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["group", "L", "beta", "mu", "margin", "Delta", "Delta_err",
                    "Delta_minus_2sigma", "ratio", "holds", "kappa0"])
        for r in rows:
            w.writerow([r["group"], r["L"], r["beta"], f"{r['mu']:.6f}", f"{r['margin']:.6f}",
                        f"{r['delta']:.4f}", f"{r['err']:.4f}", f"{r['lo']:.4f}",
                        f"{r['lo'] / r['margin']:.3f}", "yes" if r["holds"] else "NO",
                        f"{KAPPA0:.6f}"])
    print(f"\nwrote {os.path.relpath(out)}  ({len(rows)} resolved points)")


if __name__ == "__main__":
    main()
