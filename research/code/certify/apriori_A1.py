"""The deterministic finish-line certificate: read the A1 CONJUNCTION with the exact tool.

A1 = `μ < κ₀` (the short-range tension below the entropy floor) AND a **finite aperture** (a resolved
long-range mode = a finite gap).  The exact, validated reads:

  * Δ = `mass_gap`  -- the window-invariant cosh rate of the connected zero-momentum correlator.
    REFERENCE-FREE, deterministic, validated bit-for-bit (`gap_of_maximal_correlation.py`).  This is the
    finite-aperture read: Δ>0 (finite ξ) ⟺ finite aperture / gap; Δ=0 ⟺ no resolved gap.
  * μ = `attenuation` and the exact criterion  μ<κ₀ ⟺ contrast < 3^{1/4}  (= e^{κ₀}); read against the
    pinned CONFINED reference (su2 β=0.50, deep confinement) -- the signal-free null.
  * K_signal = `confinement` -- the resolved-mode order parameter (low confined, high Coulomb).

Verdict per ensemble:
  SU(N) confined : μ<κ₀ (margin κ₀−μ>0)  AND  Δ>0 (finite ξ)     -> BOTH halves -> gapped.
  U(1) Coulomb   : μ<κ₀ (margin>0)        BUT  Δ=0 (no resolved mode) -> fails the aperture half -> gapless.

Run on the CPU pod (`HOP=/workspace/configs_phase1`), or against the whole store
(`CONFIGS=<store root>`, or CONFIGS set once for the machine in the git-ignored local config
file at the repository root).  Deterministic: no RNG in the reads."""
import csv
import glob
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # research/code (parent of certify/)
import entroptics_adapter as W          # THE WRAPPER
import console  # noqa: F401  -- UTF-8 stdout, so the read names print on any console
import store_path                    # the ONE place the ensemble store is located
assert os.path.abspath(W.__file__).endswith(os.path.join("code", "entroptics_adapter.py")), W.__file__

# The store root comes from ``store_path``: the ``CONFIGS`` environment variable, then the
# git-ignored local config file at the repository root, then a refusal. No built-in default: a
# literal path names one machine, and everywhere else it makes this print an empty verdict table
# and exit 0.
# ``HOP`` is UNCHANGED and still wins: a pod holding one copied-out collection needs no store
# setting at all. Resolution is deferred rather than raised at import (the smoke tests import
# this module on machines with no store); with neither set ``HOP`` is None and the read below
# refuses, naming which of the two is missing.
# Missing data is a refusal, just below: a verdict table is printed only for ensembles that were
# actually read.
HOP = os.environ.get("HOP") or store_path.collection("configs_phase1", required=False)
# The A1 table is persisted as well as printed. This is the finish-line certificate -- the A1
# conjunction read on real ensembles -- and it reached the paper only through stdout.
OUT_CSV = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                       "data", "9_5_dat_apriori_a1.csv")

KAPPA0 = 0.25 * math.log(3.0)                 # entropy floor ¼ln3 ≈ 0.2747
CRIT = 3.0 ** 0.25                            # exact contrast threshold e^{κ₀} ≈ 1.3161
NCAP = 256
ENSEMBLES = [("su2", 0.50, "confined (strong)"), ("su2", 2.30, "confined (scaling)"),
             ("su3", 6.00, "confined"), ("u1", 2.50, "Coulomb (foil)")]
LS = (8, 12, 16, 24, 32)
LREAD = 16                                    # the reference L for the μ / K_signal reads


def load(group, L, beta, ncap=NCAP):
    fs = sorted(glob.glob(f"{HOP}/{group}_L{L}_b{beta:.2f}.s*.npy"))
    if not fs:
        return None
    return np.asarray(np.concatenate([np.load(f) for f in fs], 0)[:ncap], dtype=np.float64)


def main() -> int:
    """Read the A1 conjunction on every ensemble and write the verdict table."""
    # ── pin the confined-vacuum reference (su2 β=0.50, deep confinement) ──
    ref = []
    for L in (8, 12, 16):
        a = load("su2", L, 0.50, ncap=48)
        if a is not None:
            ref += list(a)
    if not ref:
        raise SystemExit(
            f"apriori_A1: no su2 β=0.50 reference planes under {HOP or '<no store configured>'}.\n"
            "  Every read below is thresholded against that confined-vacuum floor, so with no\n"
            "  reference there is no certificate -- refusing, rather than printing an empty verdict\n"
            "  table and exiting 0, which is what this did before.\n"
            f"  {store_path.hint()}\n"
            "  A single loose collection directory can be read instead:  HOP=<dir>")
    W.pin_reference(ref)
    print(f"pinned confined reference: {len(ref)} su2 β0.50 planes\n")


    print(f"κ₀ = ¼ln3 = {KAPPA0:.4f}   exact criterion:  μ<κ₀  ⟺  contrast < 3^(1/4) = {CRIT:.4f}\n")
    print(f"{'group':>4} {'β':>5} {'L':>3} {'n':>4} | {'Δ(gap)':>7} {'ξ=1/Δ':>6} {'lags':>4} | "
          f"{'μ':>6} {'κ₀−μ':>6} {'contr':>6} {'μ<κ₀':>5} {'K_sig':>6}")

    verdict = {}
    rows = []          # the measured table; the artifact and the verdict come from THIS
    for group, beta, tag in ENSEMBLES:
        gaps = {}
        for L in LS:
            arr = load(group, L, beta)
            if arr is None:
                continue
            r = W.run(list(arr), time_axis=-1)
            Δ = r.mass_gap                                    # reference-free, exact
            gaps[L] = Δ
            rows.append(dict(group=group, beta=beta, L=L, nconfigs=int(arr.shape[0]), phase=tag,
                             Delta=float(Δ), xi=(1.0 / Δ if Δ > 0 else float("inf")),
                             mu="", kappa0_minus_mu="", contrast="", mu_below_kappa0="", K_signal=""))
            row = f"{group:>4} {beta:>5.2f} {L:>3} {arr.shape[0]:>4} | {Δ:>7.4f} " \
                  f"{(1.0/Δ if Δ>0 else float('inf')):>6.2f} {'':>4} |"
            if L == LREAD and ref:
                try:
                    mu = r.attenuation                        # μ (vs confined reference)
                    con = r.contrast
                    ks = r.confinement
                    below = "yes" if con < CRIT else "NO"
                    row = (f"{group:>4} {beta:>5.2f} {L:>3} {arr.shape[0]:>4} | {Δ:>7.4f} "
                           f"{(1.0/Δ if Δ>0 else float('inf')):>6.2f} {'':>4} | "
                           f"{mu:>6.3f} {KAPPA0-mu:>6.3f} {con:>6.3f} {below:>5} {ks:>6.3f}")
                    verdict[(group, beta)] = (mu, con, Δ, ks)
                    rows[-1].update(mu=float(mu), kappa0_minus_mu=float(KAPPA0 - mu),
                                    contrast=float(con), mu_below_kappa0=below, K_signal=float(ks))
                except Exception as e:
                    row += f"  (floor read skipped: {e})"
            print(row)
        # gap L-scaling summary line
        if gaps:
            gl = [round(gaps[L], 3) for L in LS if L in gaps]
            print(f"     └ Δ(L) = {gl}  ({'finite ξ, L-stable' if min(gaps.values())>0.3 else 'Δ→0 (gapless)'})")

    print("\n" + "=" * 74)
    print("A1 CONJUNCTION verdict (μ<κ₀  AND  finite gap Δ>0):")
    for (group, beta), (mu, con, Δ, ks) in verdict.items():
        half1 = con < CRIT                                    # μ<κ₀
        half2 = Δ > 0.3                                       # finite aperture (resolved gap)
        if half1 and half2:
            v = f"CONFINED + GAPPED  (μ<κ₀ ✓  Δ={Δ:.2f}>0 ✓)"
        elif half1 and not half2:
            v = f"COULOMB FOIL       (μ<κ₀ ✓  Δ={Δ:.2f}=0 ✗ finite-aperture half)"
        else:
            v = f"(μ<κ₀ {'✓' if half1 else '✗'}  Δ={Δ:.2f})"
        print(f"  {group} β={beta:.2f}:  {v}   [K_signal={ks:.3f}]")
    print("=" * 74)

    # The A1 conjunction is stated per ensemble at L = LREAD, so an ensemble with no floor read leaves
    # the table claiming less than it appears to. Missing VOLUMES are expected (not every group is
    # generated at every L); a missing ENSEMBLE is not.
    missing = [f"{g} b{b:.2f}" for g, b, _ in ENSEMBLES if (g, b) not in verdict]
    if missing:
        raise SystemExit("no floor read for %s: refusing to write a partial A1 table"
                         % ", ".join(missing))
    with open(OUT_CSV, "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=["group", "beta", "L", "nconfigs", "phase", "Delta", "xi",
                                           "mu", "kappa0_minus_mu", "contrast", "mu_below_kappa0",
                                           "K_signal"])
        w.writeheader()
        w.writerows(rows)
    print("wrote %s (%d rows, %d ensembles)" % (OUT_CSV, len(rows), len(verdict)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
