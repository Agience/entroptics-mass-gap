"""Does the gap survive the box growing, at fixed aperture? — read through the OPERATOR. (PAPER §9, §12)

THE QUESTION. `ScreenedGap.gap_bound_box_independent` proves the bound `Delta_phys >= C / L_ap` does
not mention the box: it is carried as a parameter and never used, so the thermodynamic limit is not a
limit the bound has to survive. That is a theorem about the FORM of the bound and leaves one empirical
question standing — whether the read that supplies `Delta` keeps supplying it when a fixed window
looks into an ever-larger system.

WHY THIS CERTIFICATE EXISTS ALONGSIDE `gap_of_box_at_fixed_aperture`. That one asks the same question
through the aperture splice, and it cannot answer it. The splice forms a covariance over the
flattened SPATIAL sites, so the estimator is `L^3 x L^3` while the snapshot count `n*T` does not
depend on `L`. Growing the box grows the dimension against a fixed sample, and past `L^3 = n*T` the
covariance is rank-deficient. Measured there: `dim/samples = 0.17, 0.56, 1.33, 2.60` at
`L = 8, 12, 16, 20` -- so the two boxes that cleared its Nyquist condition were exactly the two whose
covariance was undetermined, and the series varied the box and the conditioning together. Its
`Delta*L = 12.4, 13.9, 14.6, 14.4` looks like a gap vanishing as `1/L` and is equally consistent with
an estimator degrading. That certificate now refuses to interpret it, which is correct and is not an
answer.

THE OPERATOR ROUTE HAS NEITHER PROBLEM:

  * the zero-momentum operator `O(t) = sum_x phi(x,t)` is a time series, so the moment pencil's
    dimension is the ORDER, not the volume -- it does not move when `L` does;
  * the correlator `C(tau)` is estimated from `n*T` products, also independent of `L`;
  * and `O` is a sum over `L^3` sites, so a LARGER box makes it quieter. The box helps here.

So the conditioning diagnostic is printed for both reads side by side: this one should be flat in `L`,
and showing that it is, is part of the measurement rather than a claim about it.

WHERE THE DATA COMES FROM, AND WHAT IT CANNOT BE. A `--field operator` shard is already `(n, T)`. A
`--field density` shard is the action-density FIELD, and summing its three spatial axes IS the same
zero-momentum projection -- `aperture_reads.operator_history` does whichever applies. That is why the
unsmeared series costs no new generation: the reduction is the reduction. What it cannot recover is
SMEARING, which acts on links, and a density shard is already past them. So an unsmeared series
isolates the conditioning question, and the Nyquist question needs generated smeared shards.

    python gap_of_box_operator.py
    CONFIGS=/path/to/store COLLECTION=configs_box_su2_b2.40 python gap_of_box_operator.py

Writes 9_13_dat_gap_of_box_operator.csv.
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

import aperture_reads as AR             # the shared reads: operator_history, pencil_rate
import store_path                       # the ONE place the ensemble store is located

assert os.path.abspath(AR.__file__).endswith(os.path.join("code", "aperture_reads.py")), \
    f"wrong aperture_reads: {AR.__file__}"

HERE = os.path.dirname(os.path.abspath(__file__))
OUT_CSV = os.path.normpath(os.path.join(os.path.dirname(HERE), os.pardir, "data",
                                        "9_13_dat_gap_of_box_operator.csv"))

COLLECTION = os.environ.get("COLLECTION", "configs_box_su2_b2.40")

#: DERIVED: the entropy floor kappa_0 = (1/4) log 3, proved in `Floor.lean`. Quoted as the scale the
#: rate is stated against, not as a cut: no verdict here compares anything to it.
KAPPA0 = 0.25 * math.log(3.0)

#: DERIVED: a SAMPLE COUNT, not a cut -- it sets how well the reseeding spread is estimated, and the
#: verdict compares two measured spreads rather than either against a number.
BLOCKS = int(os.environ.get("BLOCKS", "4"))

#: DERIVED: the pencil orders OFFERED. The verdict asks that SOME order validate itself and agree,
#: not that a particular one does -- which order works is a property of the correlator, and the read
#: says so through its own `isolation` flag. Calibrated in `gap_of_maximal_correlation` stage B3.
ORDERS = (2, 3, 4)


def shards(root, collection=COLLECTION):
    """Every shard of the series, as `{smear: {L: [paths]}}`, from the filenames.

    Accepts both the plain `su2_L{L}_b{beta}.s{k}.npy` and the operator form carrying its channel and
    smearing, `su2_L{L}_b{beta}.{channel}.ape{N}.s{k}.npy`.

    THE SMEARING TAG IS PART OF THE KEY, and that is the whole point of it being in the name. A
    differently smeared plaquette is a DIFFERENT OBSERVABLE, with its own correlation length and its
    own decay rate; concatenating two levels along the configuration axis does not make a bigger
    ensemble, it makes a mixture, and a rate fitted to a mixture is a rate of nothing. An earlier
    version keyed on `L` alone -- it read this tag and discarded it -- and the read then invalidated
    itself at every order on every box, which is the correct behaviour of an estimator handed two
    things and asked for one.

    Unsmeared shards key under `0`, so a collection with no smearing still forms one series.
    """
    out: dict[int, dict[int, list[str]]] = {}
    for f in sorted(glob.glob(os.path.join(root, collection, "su2_L*_b*.s*.npy"))):
        m = re.match(r"su2_L(\d+)_b([\d.]+)(\.[a-z]+)?(\.ape(\d+))?\.s(\d+)\.npy$",
                     os.path.basename(f))
        if m:
            smear = int(m.group(5)) if m.group(5) else 0
            out.setdefault(smear, {}).setdefault(int(m.group(1)), []).append(f)
    return out


def read_blocks(paths, blocks=BLOCKS):
    """Per-block `(rate, valid)` at each offered order, plus the geometry.

    Blocks are contiguous slices of the configuration axis, which carries independent batched chains,
    so they are independent reads of the same physics rather than resamples of one.
    """
    O = np.concatenate([AR.operator_history(np.load(p, mmap_mode="r")) for p in sorted(paths)],
                       axis=0)
    n, T = O.shape
    per = n // blocks
    # DERIVED: 2 is where a connected (mean-subtracted) correlator exists at all.
    if per < 2:
        return None
    per_order = {}
    for order in ORDERS:
        vals = []
        for b in range(blocks):
            r, ok = AR.pencil_rate(O[b * per:(b + 1) * per], order)
            if ok:
                vals.append(r)
        per_order[order] = vals
    return per_order, n, T


def main() -> int:
    why = store_path.unavailable(COLLECTION)
    if why:
        print(why)
        return 0
    root = store_path.store_root()
    by_smear = shards(root)
    if not by_smear:
        print(f"no shards under {os.path.join(root, COLLECTION)}; nothing to read")
        return 0

    print(f"store: {root}")
    print(f"collection: {COLLECTION}   (beta and T fixed; L is the box)")
    # Each smearing level is its own series. Two levels that agree about the box are a stronger
    # statement than one level, and two that disagree say the answer is the operator's rather than
    # the box's -- which is exactly what a single level could not tell you.
    verdicts = {}
    for smear in sorted(by_smear):
        series = by_smear[smear]
        print(f"\n  === smearing: APE {smear} ===" if smear else "\n  === unsmeared ===")
        verdicts[smear] = _series(series, smear)
    # DERIVED: 1 is the arity of a COMPARISON between smearing levels -- one level is not a hedge.
    if len(verdicts) > 1:
        # A level "resolved" only if some box in it reached a verdict. `_series` now returns its
        # rows either way -- the declines are the measurement -- so a non-empty return no longer
        # means the level was read.
        resolved = {s: [r for r in v if r["resolved"]] for s, v in verdicts.items() if v}
        resolved = {s: v for s, v in resolved.items() if v}
        print(f"\n  ACROSS SMEARING LEVELS: {len(resolved)} of {len(verdicts)} levels resolved")
        # DERIVED: same arity -- two levels that resolved are what can agree or disagree.
        if len(resolved) > 1:
            print("  Delta per level, per box:")
            for s, v in sorted(resolved.items()):
                print(f"    APE {s:>3}: " + "  ".join(f"L={r['L']}:{r['delta']:.5f}" for r in v))
            print("  Two levels agreeing about the box is the hedge those levels were generated for;"
                  "\n  a disagreement says the answer belongs to the operator, not to the box.")

    all_rows = [r for v in verdicts.values() if v for r in v]
    if all_rows:
        write_csv(all_rows)
    # A series the read declined to interpret is an absent measurement, not a failed one; a level
    # that read the box as MOVING is a failure, and one such level fails the run.
    return 1 if any(r["stable"] is False for r in all_rows) else 0


def _series(series, smear):
    """One box series at one smearing level. Returns its rows, or None if it cannot be compared."""
    print(f"  {'L':>4} {'n':>5} {'T':>4} | {'order':>5} {'Delta':>9} {'spread':>8} {'xi/a':>6} "
          f"{'valid':>6} | {'pencil dim':>10} {'samples':>8} {'dim/smp':>8}")

    rows = []
    for L in sorted(series):
        got = read_blocks(series[L])
        if got is None:
            print(f"  {L:>4}   too few configurations for {BLOCKS} blocks; skipped")
            continue
        per_order, n, T = got
        # The order the series uses is the smallest that validated in EVERY block -- the read's own
        # verdict, taken at the lowest order that survives it, because a lower order is a smaller
        # pencil and therefore a better-determined one.
        usable = [o for o in ORDERS if len(per_order[o]) == BLOCKS]
        if not usable:
            best = max(ORDERS, key=lambda o: len(per_order[o]))
            print(f"  {L:>4} {n:>5} {T:>4} |   read invalidated itself in every order "
                  f"(best {best}: {len(per_order[best])}/{BLOCKS} blocks)")
            # Say WHY, with the number. An order-`m` pencil needs lags up to `2m+1`; if the
            # correlator is noise past lag 3 it is being fed noise, and the cost of fixing that is
            # an ensemble size rather than a different estimator.
            budget = AR.lag_budget(np.concatenate(
                [AR.operator_history(np.load(p, mmap_mode="r")) for p in sorted(series[L])], axis=0),
                BLOCKS)
            need = 2 * min(ORDERS) + 1
            # A DECLINE IS A MEASUREMENT, so it gets a row. Without one, the campaign's actual
            # result -- the correlator is signal for two or three lags, here is its decay, here is
            # the ensemble a verdict would need -- lived only in terminal output, and `regen_all`
            # listed an artifact the script could not produce.
            row = dict(smear=smear, L=L, n=n, T=T, order=None, delta=float("nan"),
                       spread=float("nan"), xi=float("nan"), sampled=False, pdim=None,
                       samples=n * T, blocks="", stable=None, resolved=False,
                       usable_lag=None, decay=float("nan"), needs_lag=need, needs_configs=None)
            if budget:
                last, rate, s, Cc, _ = budget
                row.update(usable_lag=last, decay=rate)
                print(f"  {'':>4} {'':>5} {'':>4} |   correlator is signal to lag {last} "
                      f"(decay {rate:.3f}); the order-{min(ORDERS)} pencil needs lag {need}")
                # DERIVED: 2 lags is the arity of a decay RATE -- one lag is a value, not a
                # slope, and the projection below needs a slope.
                # PER BLOCK, because that is what the read gates on. `read_blocks` requires the
                # pencil to validate in EVERY block, so the ensemble has to be large enough that each
                # BLOCK's correlator reaches `need` -- about `BLOCKS` times what the full ensemble
                # needs. Quoting the full-ensemble figure sized this campaign 24x short.
                if last >= 2:
                    O_all = np.concatenate(
                        [AR.operator_history(np.load(p, mmap_mode="r")) for p in sorted(series[L])],
                        axis=0)
                    want = AR.configs_for_blocked_lag(O_all, BLOCKS, need)
                    if want:
                        row["needs_configs"] = want
                        print(f"  {'':>4} {'':>5} {'':>4} |   every block reaching lag {need} needs "
                              f"about {want:,.0f} configurations here; this ensemble has {n}")
            rows.append(row)
            continue
        order = usable[0]
        vals = np.array(per_order[order], dtype=float)
        mean, spread = float(vals.mean()), float(vals.max() - vals.min())
        # DERIVED: 1.0 is the lattice spacing in its own units -- xi = 1/Delta exceeds one sampling
        # interval exactly when Delta < 1. Nyquist, not a tolerance.
        sampled = mean < 1.0
        # DERIVED: 0 is the domain of the reciprocal -- a nonpositive rate has no correlation
        # length, and `inf` reports that rather than dividing.
        xi = (1.0 / mean) if mean > 0 else float("inf")
        # The conditioning, printed so that "it does not grow with L" is shown rather than asserted.
        # DERIVED: the pencil is (order+1) x (order+1) and the correlator is estimated from n*T
        # products. Neither mentions L.
        pdim = order + 1
        samples = n * T
        budget = AR.lag_budget(np.concatenate(
            [AR.operator_history(np.load(q, mmap_mode="r")) for q in sorted(series[L])], axis=0),
            BLOCKS)
        rows.append(dict(smear=smear, L=L, n=n, T=T, order=order, delta=mean, spread=spread, xi=xi,
                         sampled=sampled, pdim=pdim, samples=samples, resolved=True, stable=None,
                         usable_lag=(budget[0] if budget else None),
                         decay=(budget[1] if budget else float("nan")),
                         needs_lag=2 * order + 1, needs_configs=None,
                         blocks=" ".join(f"{v:.4f}" for v in vals)))
        print(f"  {L:>4} {n:>5} {T:>4} | {order:>5} {mean:>9.5f} {spread:>8.5f} {xi:>6.2f} "
              f"{len(vals):>3}/{BLOCKS} | {pdim:>10} {samples:>8} {pdim / samples:>8.4f}")

    # Boxes that DECLINED carry rows too, because a decline is a measurement. Only the
    # resolved ones can be compared, so the comparison runs on those; the rest still travel
    # to the artifact, which is where the campaign's actual result belongs.
    got = [r for r in rows if r["resolved"]]
    # DERIVED: 2 is where a comparison BETWEEN boxes exists. One box is not a series.
    if len(got) < 2:
        print("  fewer than two box sizes resolved; this series cannot be compared")
        return rows

    Ts = {r["T"] for r in got}
    # DERIVED: 1 is the arity of "the aperture is held fixed" -- one T, or the series is not
    # separating the box from the window.
    if len(Ts) != 1:
        print(f"  REFUSED: the series carries T = {sorted(Ts)}; it does not hold the aperture fixed.")
        return rows

    deltas = np.array([r["delta"] for r in got])
    across_box = float(deltas.max() - deltas.min())
    within_box = max(r["spread"] for r in got)
    unsampled = [r["L"] for r in got if not r["sampled"]]

    print(f"\n  boxes read: {[r['L'] for r in got]}   aperture T: {sorted(Ts)}")
    print(f"  pencil dimension across the series: {sorted({r['pdim'] for r in got})}  "
          f"(samples {sorted({r['samples'] for r in got})}) — it does not grow with the box")
    print(f"  Delta*L across the series : {[round(r['L'] * r['delta'], 1) for r in got]}")
    print(f"  Delta across the box series : {across_box:.5f}")
    print(f"  Delta within one box (blocks): {within_box:.5f}   (the largest block spread)")
    # DERIVED: 0 is the guard against an exactly-zero spread (every block returning the identical
    # float); `inf` then correctly reports "outside the spread".
    ratio = across_box / within_box if within_box > 0 else float("inf")
    print(f"  ratio = {ratio:.2f}")

    if unsampled:
        print(f"\n  NO VERDICT on the box: at L = {unsampled} the correlation length is below one "
              f"lattice spacing, so the read is not sampling the decay there. The conditioning "
              f"confound is gone — the pencil dimension is flat in L above — but Nyquist is not, and "
              f"only a SMEARED operator lengthens the correlation length. Generate the smeared "
              f"series (`--smear`) and rerun.")
        stable = None
    else:
        # DERIVED: 1.0 is the ratio at which the box-to-box variation EQUALS the within-box reseeding
        # spread. Both sides measured here; the comparison introduces no scale.
        stable = ratio <= 1.0
        print("  => " + ("PASS" if stable else "FAIL") + ": the gap "
              + ("does not move with the box by more than it moves for no reason"
                 if stable else "MOVES with the box beyond its own reproducibility"))

    for r in got:
        r["stable"] = stable
    return rows


def write_csv(all_rows):
    """The whole series -- every smearing level -- as one table."""
    os.makedirs(os.path.dirname(OUT_CSV), exist_ok=True)
    with open(OUT_CSV, "w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(["group", "collection", "smear", "L", "T", "n_configs", "blocks", "resolved",
                    "usable_lag", "decay_rate", "needs_lag", "needs_configs", "pencil_order",
                    "pencil_dim", "samples", "delta", "spread", "xi_over_a", "decay_sampled",
                    "L_times_delta", "kappa0", "box_stable", "block_values"])

        def num(v, spec):
            """Blank for absent or not-a-number, so a decline reads as absent rather than as 0."""
            return "" if v is None or v != v else format(v, spec)

        for r in all_rows:
            w.writerow(["su2", COLLECTION, r["smear"], r["L"], r["T"], r["n"], BLOCKS,
                        "yes" if r["resolved"] else "no",
                        "" if r["usable_lag"] is None else r["usable_lag"],
                        num(r["decay"], ".6f"),
                        r["needs_lag"], num(r["needs_configs"], ".0f"),
                        "" if r["order"] is None else r["order"],
                        "" if r["pdim"] is None else r["pdim"], r["samples"],
                        num(r["delta"], ".6f"), num(r["spread"], ".6f"), num(r["xi"], ".4f"),
                        "yes" if r["sampled"] else "no",
                        num(r["L"] * r["delta"], ".4f"), f"{KAPPA0:.6f}",
                        {True: "yes", False: "no", None: ""}[r["stable"]], r["blocks"]])
    print(f"\nwrote {OUT_CSV}  ({len(all_rows)} row(s))")


if __name__ == "__main__":
    raise SystemExit(main())
