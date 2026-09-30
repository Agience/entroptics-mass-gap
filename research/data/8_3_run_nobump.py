"""
8_3_run_nobump.py -- K_signal across beta 0..5 for compact U(1) and SU(2) on FRESH Monte-Carlo
configurations (an exploratory path; the committed 8_3_dat_nobump.csv is 8_3_regen_from_store.py's).

K_signal (the entroptics resolved-mode read on raw configs) is read for both gauge groups, each
value with its same-marginal control: the same configurations with every plane's values permuted
within the plane (config i seeded by its index), and the paired difference.

K_signal needs a reference null pinned at the plane shape it reads, and this script pins none: run
as it stands, the first read raises. Pin a confined reference at the lattice's plane shape
(entroptics_adapter.pin_reference) before calling main().

Reads come through the single typed wrapper on RAW configs (no preprocessing).
Writes 8_3_dat_nobump.csv and 8_3_fig_nobump.png here.

    python 8_3_run_nobump.py --mode quick   # coarse, small lattice
    python 8_3_run_nobump.py --mode full    # dense 0..5, 8^3x16
"""
from __future__ import annotations

import argparse
import multiprocessing as mp
import os
import sys

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(_HERE, "..", "code")))

import entroptics_adapter as entroptics
import lattice_generator as generator
import table
import plot

DAT = os.path.join(_HERE, "8_3_dat_nobump.csv")
FIG = os.path.join(_HERE, "8_3_fig_nobump.png")
BETA_C = 1.01
COLS = ["group", "beta", "dims", "confinement", "confinement_err", "temporal_attenuation", "n",
        "confinement_shuffled", "confinement_shuffled_err", "confinement_minus_shuffled",
        "confinement_minus_shuffled_err"]
STYLE = {"u1": ("#b03030", r"compact U(1) $K_{\mathrm{signal}}$"),
         "su2": ("#1f4e8c", r"SU(2) $K_{\mathrm{signal}}$")}


def measure(group, beta, dims, *, seed, therm, gap, n, device=None):
    if device:                                             # batched-GPU generation, then CPU reads
        fb = generator.config_batch(dims, beta, group=group, seed=seed, therm=therm, n=n, device=device)
        fb = fb.detach().cpu().numpy()                     # small per-plane SVD reads are faster on CPU
        cfgs = [fb[i] for i in range(fb.shape[0])]
    else:
        cfgs = list(generator.stream(dims, beta, group=group, seed=seed, therm=therm, gap=gap, n=n))
    ks = np.array([entroptics.confinement(c) for c in cfgs], float)
    # the same-marginal control: every plane's values permuted within the plane, config i seeded i
    sh = np.array([entroptics.confinement(c, shuffle=i) for i, c in enumerate(cfgs)], float)
    d = ks - sh                                           # paired per configuration
    se = lambda v: float(v.std() / np.sqrt(len(v)))       # the estimator confinement_err uses
    r = entroptics.run(cfgs)
    return dict(group=group, beta=round(beta, 2), dims="x".join(map(str, dims)),
                confinement=float(ks.mean()), confinement_err=se(ks),
                temporal_attenuation=r.temporal_attenuation, n=len(cfgs),
                confinement_shuffled=float(sh.mean()), confinement_shuffled_err=se(sh),
                confinement_minus_shuffled=float(d.mean()), confinement_minus_shuffled_err=se(d))


def _measure_star(item):
    """Top-level (picklable) wrapper so a multiprocessing Pool can fan the per-(group,beta)
    chains across cores. Each item is one independent thermalised chain (its own seed)."""
    group, beta, dims, seed, therm, gap, n, device = item
    return measure(group, beta, dims, seed=seed, therm=therm, gap=gap, n=n, device=device)


def main():
    ap = argparse.ArgumentParser(description="No-bump: U(1) vs SU(2) confinement across 0..5.")
    ap.add_argument("--mode", choices=["quick", "full"], default="quick")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--n", type=int, default=None)
    ap.add_argument("--jobs", type=int, default=1, help="parallel worker processes over (group,beta)")
    ap.add_argument("--device", default=None, help="torch device for batched-GPU generation, e.g. cuda")
    args = ap.parse_args()

    if args.mode == "quick":
        dims, therm, gap = (6, 6, 6, 6), 120, 4
        betas = [round(b, 2) for b in np.arange(0.0, 5.01, 1.0)]
        n = args.n or 8
    else:
        dims, therm, gap = (8, 8, 8, 16), 200, 4
        betas = [round(b, 2) for b in np.arange(0.0, 5.01, 0.25)]
        n = args.n or 18

    print(f"lattice {dims}  therm={therm}  n={n}  gap={gap}  jobs={args.jobs}  device={args.device}")
    items = [(group, beta, dims, args.seed + i, therm, gap, n, args.device)
             for group in ("u1", "su2") for i, beta in enumerate(betas)]
    if args.device:                                        # GPU: serial over (group,beta), each a batched call
        rows = [_measure_star(it) for it in items]
    elif args.jobs > 1:                                    # CPU: multiprocess over (group,beta)
        with mp.Pool(args.jobs) as pool:
            rows = pool.map(_measure_star, items)
    else:
        rows = [_measure_star(it) for it in items]
    for r in rows:
        print(f"  {r['group']:>3} beta={r['beta']:5.2f}  confinement={r['confinement']:6.3f} "
              f"+/- {r['confinement_err']:.1e}")

    table.write(DAT, rows, COLS)

    series = []
    for group in ("u1", "su2"):
        g = [r for r in rows if r["group"] == group]
        color, label = STYLE[group]
        series.append({"y": [r["confinement"] for r in g],
                       "yerr": [r["confinement_err"] for r in g],
                       "label": label, "color": color})
    plot.line(FIG, betas, series,
              xlabel=r"$\beta$", ylabel=r"confinement  $K_{\mathrm{signal}}$",
              title=r"$K_{\mathrm{signal}}$ vs $\beta$, compact U(1) and SU(2), " + "x".join(map(str, dims)),
              vline=BETA_C, vline_label=r"compact U(1) $\beta_c\approx1.01$ (literature)")
    print("wrote", DAT, "and", FIG)


if __name__ == "__main__":
    main()
