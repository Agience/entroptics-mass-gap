"""The β-behavior certificate: Δ(β) per gauge group, with the exact cosh gap read, resolving the
Δ=0 ambiguity (gapless vs sub-lattice heavy gap) EMPIRICALLY rather than by theory.

Expectation:
  * su2  β ∈ {2.0..2.6} : a resolved, finite gap THROUGHOUT the scaling window (not a one-β fluke).
  * su3  β ∈ {5.7..6.3} : same, a second gauge group.
  * u1   β ∈ {0.9..2.5} : across β_c ≈ 1.01 -- gap on the confined side (β<β_c, if resolvable) and
    Δ = 0 across the WHOLE Coulomb phase (β>β_c) -> u1's Δ=0 is GAPLESSNESS, not a one-β artifact.

Reference-free, deterministic.  Point it at the config store with CONFIGS=<store>, or set CONFIGS
once for the machine in the git-ignored local config file at the repository root (HOP/HOP0 override
the two directories individually).  Prints Δ(β,L) and the per-group verdict, and beside it the
reader's own correlation-length read `a_delta`, so a resolution-ceiling Δ is distinguishable from a
resolved one.  The two are reported SEPARATELY and never conjoined: Δ is the forward-operator gap,
`a_delta` is how far the signal stays correlated, and a resolved gap on a short correlator is a real
reading, not a weak one."""
import csv
import glob
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # research/code (parent of certify/)
import entroptics_adapter as W          # THE WRAPPER
import console  # noqa: F401  -- UTF-8 stdout, so the read names print on any console
import store_path                       # the ONE place the ensemble store is located
assert os.path.abspath(W.__file__).endswith(os.path.join("code", "entroptics_adapter.py")), W.__file__

# Store root from ``store_path``: CONFIGS, then the git-ignored local config file, then a refusal
# -- no path baked into this file. HOP/HOP0 are UNCHANGED and still override the two individual
# directories, and still win, so one loose directory can be read with no store setting at all.
# Resolution is deferred, not raised at import: the smoke tests import this module (and redirect
# HOP/HOP0) on machines with no store. With nothing configured these are None and the refusal
# below carries ``store_path.hint()``.
HOP = os.environ.get("HOP") or store_path.collection("configs_betasweep", required=False)
HOP0 = os.environ.get("HOP0") or store_path.collection("configs_phase1", required=False)   # the balanced dataset (for the existing beta points)
NCAP = 256


def load(group, L, beta):
    fs = []
    for h in (HOP, HOP0):
        fs += sorted(glob.glob(f"{h}/{group}_L{L}_b{beta:.2f}.s*.npy"))
    if not fs:
        return None
    return np.asarray(np.concatenate([np.load(f) for f in fs], 0)[:NCAP], dtype=np.float64)


def resolution_length(cfgs):
    """The reader's own correlation-length read, ensemble-averaged: ``Aperture.a_delta``.

    This replaces a hand-rolled coherence count -- ensemble-mean autocorrelation, a robust (MAD)
    noise level, a Bonferroni z, and a walk along the lags while the sequence both decreased and
    stood above that floor. Every one of those was this script re-deriving, less well, a read the
    library already performs: ``a_delta`` is the diffraction-limit aperture, fixed by the signal's
    OWN entropy, with no constant to choose and no threshold to justify.

    It is also a better diagnostic. The hand-rolled count collapsed to 0 or 1 on every ensemble
    here (the raw action density decorrelates in a single lag, being UV-dominated and local), so it
    could not discriminate at all; ``a_delta`` is continuous and does: 0.885 at L=12 against 0.902
    at L=16 on the same coupling. Reported beside the gap, never conjoined with it -- they measure
    different things."""
    return float(np.mean([float(W.aperture(c).a_delta) for c in cfgs]))


# The sweep table is persisted as well as printed. This is the beta-behaviour certificate that
# resolves the Delta=0 ambiguity empirically, and it reached the paper only through stdout.
OUT_CSV = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                       "data", "9_6_dat_gap_refinement.csv")

SWEEP = {
    "su2": ([2.00, 2.20, 2.30, 2.40, 2.60], (12, 16)),
    "su3": ([5.70, 6.00, 6.30], (12,)),
    "u1":  ([0.90, 0.95, 1.10, 1.30, 1.70, 2.50], (12, 16)),
}
BC = {"su2": None, "su3": None, "u1": 1.01}      # u1 deconfinement β_c


def main() -> int:
    """Sweep the gap read across the coupling grid and write the refinement table."""
    print(f"{'group':>4} {'β':>5} {'L':>3} {'n':>4} | {'Δ(gap)':>7} {'a_delta':>8} {'read':>10}")
    res = {}
    rows = []          # the measured table; the summary below and the artifact come from THIS
    for group, (betas, Ls) in SWEEP.items():
        for beta in betas:
            for L in Ls:
                arr = load(group, L, beta)
                if arr is None:
                    continue
                cfgs = list(arr)
                Δ = W.run(cfgs, time_axis=-1).mass_gap
                adelta = resolution_length(cfgs)
                res.setdefault((group, beta), {})[L] = (Δ, adelta, arr.shape[0])
                # Two independent reads, reported independently: the tag is set by Δ alone and the
                # lag count is carried beside it. Coupling them would call a resolved,
                # refinement-invariant Δ weak whenever the correlator is short, and on this observable
                # it always is: the raw action density is UV-dominated and local, so its connected
                # autocorrelation collapses within a lag or two and then turns negative. The
                # zero-momentum form of the same correlator is measured in 8_7_dat_gap_correlator.csv,
                # where unsmeared at L=16 it reads C(1)/C(0) = 0.195, 0.191, 0.167 at beta = 2.30,
                # 2.40, 2.50 and is noise by tau ~ 2. That short correlator is a property of the
                # observable -- which is why §8.7 APE-smears before reading a transfer spectrum -- and
                # not a property of the gap.
                # Δ is NaN when the fitted operator grows (no rate was resolved); that is neither
                # a gap nor gaplessness and must not be silently ordered against either.
                if Δ != Δ:
                    tag = "unresolved"
                elif Δ == 0:
                    tag = "gapless"
                else:
                    tag = "GAP" if Δ > 0.5 else "weak"
                print(f"{group:>4} {beta:>5.2f} {L:>3} {arr.shape[0]:>4} | {Δ:>7.4f} {adelta:>8.4f} {tag:>10}")
                rows.append(dict(group=group, beta="%.2f" % beta, L=L, nconfigs=int(arr.shape[0]),
                                 Delta=("" if Δ != Δ else "%.6f" % Δ),
                                 a_delta="%.6f" % adelta, read=tag))

    if not res:
        raise SystemExit(
            f"gap_refinement_invariant: the sweep matched no configurations under\n"
            f"    {HOP or '<no store configured>'}\n"
            f"    {HOP0 or '<no store configured>'}\n"
            "  Every row below is read from those ensembles, so there is nothing to report:\n"
            "  refusing, rather than printing an empty table and exiting 0.\n"
            f"  {store_path.hint()}")

    print("\n" + "=" * 68)
    print("β-BEHAVIOR of the gap (the Δ=0 ambiguity, resolved empirically):")
    for group, (betas, Ls) in SWEEP.items():
        Lr = Ls[-1]                                   # the largest L (best resolution)
        row = []
        for beta in betas:
            rL = res.get((group, beta), {})
            d = rL.get(Lr, rL.get(Ls[0], (float("nan"), 0, 0)))[0]
            row.append((beta, d))
        txt = "  ".join(f"β{b:.2f}:{d:.2f}" for b, d in row if d == d)
        print(f"  {group} (L={Lr}):  {txt}")
        if group == "u1":
            coul = [d for b, d in row if b > BC["u1"] and d == d]
            conf = [d for b, d in row if b < BC["u1"] and d == d]
            if coul:
                print(f"     Coulomb (β>β_c={BC['u1']}): Δ = {[round(d,2) for d in coul]}  "
                      f"-> {'ALL ~0 (gaplessness confirmed across the phase)' if max(coul) < 0.3 else 'NOT all 0 (check)'}")
            if conf:
                print(f"     confined (β<β_c):          Δ = {[round(d,2) for d in conf]}")
        else:
            finite = [d for b, d in row if d == d]
            if finite:
                print(f"     scaling window: Δ = {[round(d,2) for d in finite]}  "
                      f"-> {'resolved-finite throughout' if min(finite) > 0.5 else 'some unresolved (check L/stats)'}")
    print("=" * 68)

    # The claim this table carries is a gap resolved THROUGHOUT each scaling window, so a coupling that
    # produced no row at any volume would quietly shorten the sweep while the summary still reads as a
    # pass. A missing VOLUME within a coupling is not that: the sweep reads two L per group by design
    # and the summary already falls back to the smaller one.
    absent = ["%s b%.2f" % (g, b) for g, (betas, _Ls) in SWEEP.items() for b in betas
              if (g, b) not in res]
    if absent:
        raise SystemExit("no configurations for %s: refusing to write a partial beta sweep"
                         % ", ".join(absent))
    with open(OUT_CSV, "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=["group", "beta", "L", "nconfigs", "Delta", "a_delta", "read"])
        w.writeheader()
        w.writerows(rows)
    print("wrote %s (%d rows, %d couplings)" % (OUT_CSV, len(rows), len(res)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
