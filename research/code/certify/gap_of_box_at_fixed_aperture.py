"""Does the gap survive the box growing, with the APERTURE held fixed? (PAPER Sec 9, Sec 12)

THE QUESTION THIS ANSWERS. `ScreenedGap.gap_bound_box_independent` proves that the bound
`Delta_phys >= C / L_ap` does not mention the box: the box is carried as a parameter and never used,
so the thermodynamic limit is not a limit the bound has to survive -- it is one the bound never took.
That is a theorem about the FORM of the bound. It is not a measurement, and it leaves one empirical
question standing: whether the read that supplies `Delta` keeps supplying it when a fixed window
looks into an ever-larger system.

WHY THE TIME AXIS AND NOT THE SPATIAL ONE. `per_config_profiles` reads SPATIAL lags, and its lag
count is the spatial extent's half -- so on a bigger lattice it is a bigger aperture AND a bigger box
at once, and the two cannot be told apart. The wrapper's forward-operator read runs on the TIME axis
instead, whose extent `T` is a generation parameter independent of `L`. So an ensemble series at

    fixed beta  (one lattice spacing)      fixed T  (one aperture)      growing L  (the box)

moves the box and nothing else. That is the series this reads.

WHAT WOULD FALSIFY IT. If `Delta` fell as `L` grew, the gap the read reports would be an artifact of
the system being small rather than a property of the theory, and the aperture argument would be
resting on a finite-volume accident. The test is therefore not "is Delta positive" -- it is whether
Delta MOVES with the box by more than it moves for no reason at all.

THE REFERENCE, AND WHY IT IS NOT A NUMBER WRITTEN HERE. Each shard carries independent batched
chains, so splitting one into disjoint blocks gives several independent reads of the SAME physics at
the SAME box. The spread across those blocks is how far the answer moves for no physical reason. The
verdict compares the box-to-box variation against it: if growing the box moves Delta no more than
re-blocking does, the box is not what Delta is measuring. Both sides are measured; no window is
chosen.

FIRST, THOUGH: IS THE DECAY SAMPLED AT ALL? A rate `Delta` has correlation length `1 / Delta` in
lattice spacings, so `Delta < 1` says the decay takes more than one time step and `Delta >= 1` says it
finishes inside one. The `1` is the SAMPLING INTERVAL in its own units -- Nyquist, not a tolerance --
and the same condition the free-scalar calibration applies (`gap_of_maximal_correlation`, where a
sub-spacing mass is read 7% low at the widest window and 24% low at the narrowest). A box series read
below the sampling limit is not measuring the box; it is measuring the instrument.

So this reports the condition per box and passes NO verdict on a series that fails it. That is the
criterion working in the direction it is supposed to: a read that cannot resolve the decay returns no
verdict rather than a flattering one.

AND A SECOND CONFOUND, WHICH IS WORSE BECAUSE IT LOOKS LIKE PHYSICS. The aperture read forms a
covariance over the flattened SPATIAL sites and reads the dominant Koopman mode along time. Holding
`T` fixed holds the number of LAGS fixed; it does not hold the ESTIMATOR fixed. The covariance is
`L^3 x L^3` and the snapshot count is `n*T`, which does not depend on `L`. So growing the box grows
the dimension as `L^3` against a fixed sample size, and past `L^3 = n*T` the covariance is
rank-deficient.

Measured on this series: `dim/samples` = 0.17, 0.56, 1.33, 2.60 at L = 8, 12, 16, 20. The two boxes
that clear the Nyquist condition are exactly the two that are rank-deficient. The series therefore
varies the box AND the conditioning together and cannot separate them -- and the symptom is
seductive: `Delta*L` came out near-constant (12.4, 13.9, 14.6, 14.4), which reads like a gap
vanishing as `1/L` and is equally consistent with an estimator degrading as its dimension outgrows
its sample.

The condition is arity rather than a cut: a `d x d` covariance needs at least `d` samples to be
determined at all. `L^3 > n*T` is that statement, and the fix is to scale `n` with `L^3` -- which
makes the campaign cost grow as the volume, and is the price of asking this question properly.

AND THE FIX IS NOT THE COUPLING. The obvious move is a larger beta -- a finer lattice, a longer
correlation length in lattice units. Measured on the store's own SU(2) L=16, T=32 density ensembles
(24 configurations each, `aperture_reads.delta`), it does not work:

    beta   2.00     2.20     2.40     2.60
    Delta  1.0806   0.8308   0.9228   1.0422
    xi/a   0.93     1.20     1.08     0.96

xi sits at ONE lattice spacing across the whole available range and does not trend. That is a
property of the OPERATOR, not of the coupling: the action density is a local composite (~ :F^2:),
and its correlation length is the gluelump scale -- about one spacing by construction. No beta in the
confined window lengthens it, because it is not the coupling that sets it.

What lengthens it is suppressing the ultraviolet in the operator itself -- smearing, the standard
lattice construction, which `lattice_generator.py` supports (`--field operator --channel plaquette`).
That is the series this test needs, and generating it is the open step. The coupling is not the
lever, and saying so is the point of recording the sweep above rather than trying a bigger number.

    python gap_of_box_at_fixed_aperture.py
    CONFIGS=/path/to/store python gap_of_box_at_fixed_aperture.py

Reads `configs_box_su2_b2.40` -- the campaign generated for exactly this question. Writes
9_12_dat_gap_of_box.csv.
"""
from __future__ import annotations

import csv
import glob
import math
import os
import re
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # research/code

import aperture_reads as AR             # THE WRAPPER's aperture read (delta = connected decay rate)
import store_path                       # the ONE place the ensemble store is located

assert os.path.abspath(AR.__file__).endswith(os.path.join("code", "aperture_reads.py")), \
    f"wrong aperture_reads: {AR.__file__}"

HERE = os.path.dirname(os.path.abspath(__file__))
OUT_CSV = os.path.join(os.path.dirname(HERE), os.pardir, "data", "9_12_dat_gap_of_box.csv")
OUT_CSV = os.path.normpath(OUT_CSV)

#: The collection generated at fixed beta and fixed T with the box as the only free parameter.
COLLECTION = "configs_box_su2_b2.40"

#: DERIVED: the entropy floor kappa_0 = (1/4) log 3, the scale the tension is read against. Proved in
#: `Floor.lean`; quoted here as the reference the physical gap is stated relative to, not as a cut.
KAPPA0 = 0.25 * math.log(3.0)

#: DERIVED: a SAMPLE COUNT, not a cut. It sets how well the within-box spread is estimated, and no
#: verdict turns on its value -- the comparison below is between two measured spreads. Four disjoint
#: blocks of a 96-configuration shard leave 24 independent chains in each, which is a read.
BLOCKS = 4


def shards(root, collection=COLLECTION):
    """Every shard of the fixed-aperture box series, as {L: [paths]}, from the filenames."""
    out: dict[int, list[str]] = {}
    for f in sorted(glob.glob(os.path.join(root, collection, "su2_L*_b*.s*.npy"))):
        m = re.match(r"su2_L(\d+)_b([\d.]+)\.s(\d+)\.npy$", os.path.basename(f))
        if m:
            out.setdefault(int(m.group(1)), []).append(f)
    return out


def read_blocks(paths, blocks=BLOCKS):
    """Delta from `blocks` disjoint slices of the ensemble, plus the geometry they were read at.

    The slices are contiguous ranges of the configuration axis, which is the axis of independent
    batched chains -- so they are independent reads of the same physics, not resamples of one.
    """
    arr = np.concatenate([np.load(p, mmap_mode="r") for p in sorted(paths)], axis=0)
    n, T = arr.shape[0], arr.shape[-1]
    per = n // blocks
    # DERIVED: 2 is where a connected (mean-subtracted) read exists at all -- one configuration has
    # no ensemble to be connected against. Arity, not a sample-size cut.
    if per < 2:
        return None
    vals = [AR.delta(np.asarray(arr[b * per:(b + 1) * per], dtype=np.float64))
            for b in range(blocks)]
    return np.array(vals, dtype=float), n, T


def main() -> int:
    why = store_path.unavailable(COLLECTION)
    if why:
        print(why)
        return 0
    root = store_path.store_root()
    series = shards(root)
    if not series:
        print(f"no shards under {os.path.join(root, COLLECTION)}; the campaign has not landed yet")
        return 0

    print(f"store: {root}")
    print(f"collection: {COLLECTION}   (beta and T fixed; L is the box)")
    print(f"  {'L':>4} {'n':>5} {'T':>4} | {'Delta':>9} {'spread':>9} {'xi/a':>7} "
          f"{'sampled':>8} {'dim/smp':>8} {'det':>4}   blocks")

    rows = []
    for L in sorted(series):
        got = read_blocks(series[L])
        if got is None:
            print(f"  {L:>4}   too few configurations for {BLOCKS} blocks; skipped")
            continue
        vals, n, T = got
        mean, spread = float(vals.mean()), float(vals.max() - vals.min())
        # DERIVED: 1.0 is the lattice spacing in its own units. xi = 1/Delta exceeds one sampling
        # interval exactly when Delta < 1. Nyquist, not a tolerance.
        sampled = mean < 1.0
        # DERIVED: 0 is the domain of the reciprocal. A nonpositive rate has no correlation
        # length, and `inf` reports that rather than dividing.
        xi = (1.0 / mean) if mean > 0 else float("inf")
        # DERIVED: the covariance the read forms is L^3 x L^3 and the snapshots are n*T. A d x d
        # covariance needs at least d samples to be determined; the ratio is that statement, and
        # `> 1` is where the estimator stops being determined by its data. Arity, not a cut.
        dim_over_samples = (L ** 3) / (n * T)
        # DERIVED: 1.0 is where the dimension EQUALS the sample count -- the point a covariance
        # stops being determined by its data. Linear algebra, not a tolerance.
        determined = dim_over_samples <= 1.0
        rows.append(dict(L=L, n=n, T=T, delta=mean, spread=spread, xi=xi, sampled=sampled,
                         dim_over_samples=dim_over_samples, determined=determined,
                         t_delta=T * mean,
                         blocks=" ".join(f"{v:.4f}" for v in vals)))
        print(f"  {L:>4} {n:>5} {T:>4} | {mean:>9.5f} {spread:>9.5f} {xi:>7.2f} "
              f"{('yes' if sampled else 'NO'):>8} {dim_over_samples:>8.2f} "
              f"{('yes' if determined else 'NO'):>4}   " + " ".join(f"{v:.4f}" for v in vals))

    # DERIVED: 2 is where a comparison BETWEEN boxes exists. One box has no series.
    if len(rows) < 2:
        print("\nfewer than two box sizes; the series cannot be compared yet")
        return 0

    deltas = np.array([r["delta"] for r in rows])
    across_box = float(deltas.max() - deltas.min())
    within_box = max(r["spread"] for r in rows)
    Ts = {r["T"] for r in rows}
    boxes = [r["L"] for r in rows]

    print(f"\n  boxes read: {boxes}   aperture T: {sorted(Ts)}")
    # DERIVED: 1 is the arity of "the aperture is held fixed" -- the series must carry one T, or
    # it is not separating the box from the window at all.
    if len(Ts) != 1:
        print("  REFUSED: the series does not hold T fixed, so it does not separate box from "
              "aperture. Regenerate with one T.")
        return 1

    unsampled = [r["L"] for r in rows if not r["sampled"]]
    undetermined = [r["L"] for r in rows if not r["determined"]]
    print(f"  Delta across the box series : {across_box:.5f}")
    print(f"  Delta within one box (blocks): {within_box:.5f}   (the largest block spread)")
    # DERIVED: the comparison is between two measured spreads. A ratio at or below 1 says growing the
    # box moved the read no more than re-blocking the same box did; nothing here is a chosen window.
    ratio = across_box / within_box if within_box > 0 else float("inf")
    print(f"  ratio = {ratio:.2f}")
    # DERIVED: 1.0 below is the ratio at which the box-to-box variation EQUALS the within-box
    # reseeding spread. Both sides are measured here; the comparison introduces no scale.

    if undetermined:
        print(f"\n  NO VERDICT: at L = {undetermined} the read's covariance has more dimensions "
              f"({'/'.join(str(r['L'] ** 3) for r in rows if not r['determined'])}) than the "
              f"ensemble has snapshots ({rows[0]['n'] * rows[0]['T']}), so its dominant mode is "
              f"estimated from fewer samples than it has dimensions. Growing the box grows that "
              f"dimension as L^3 against a FIXED sample count, so this series varies the box and the "
              f"conditioning together and cannot separate them. Scale n with L^3.")
        stable = None
    elif unsampled:
        print(f"\n  NO VERDICT: at L = {unsampled} the correlation length is below one lattice "
              f"spacing, so the read is not sampling the decay and the box-to-box variation above "
              f"is the instrument, not the theory. Not fixable by a wider window (already {rows[0]['T']} "
              f"lags) nor by the coupling (measured flat at xi ~ 1 across beta 2.0-2.6, see the "
              f"module docstring): the action density's correlation length is the gluelump scale. "
              f"The series needs a SMEARED operator.")
        stable = None
    else:
        # DERIVED: the ratio at which the box-to-box variation EQUALS the within-box spread.
        stable = ratio <= 1.0
        print("  => " + ("PASS" if stable else "FAIL")
              + ": the gap "
              + ("does not move with the box by more than it moves for no reason"
                 if stable else "MOVES with the box beyond its own reproducibility"))

    os.makedirs(os.path.dirname(OUT_CSV), exist_ok=True)
    with open(OUT_CSV, "w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(["group", "L", "beta", "T", "n_configs", "blocks", "delta", "spread",
                    "xi_over_a", "decay_sampled", "dim_over_samples", "covariance_determined",
                    "T_times_delta", "L_times_delta", "kappa0", "block_values"])
        for r in rows:
            w.writerow(["su2", r["L"], "2.40", r["T"], r["n"], BLOCKS,
                        f"{r['delta']:.6f}", f"{r['spread']:.6f}", f"{r['xi']:.4f}",
                        "yes" if r["sampled"] else "no", f"{r['dim_over_samples']:.4f}",
                        "yes" if r["determined"] else "no", f"{r['t_delta']:.4f}",
                        f"{r['L'] * r['delta']:.4f}", f"{KAPPA0:.6f}", r["blocks"]])
    print(f"wrote {OUT_CSV}")
    # A series read below the sampling limit is not a failed measurement; it is an absent one, and
    # exiting nonzero would report the instrument's limit as a defect of the theory.
    return 0 if stable is not False else 1


if __name__ == "__main__":
    raise SystemExit(main())
