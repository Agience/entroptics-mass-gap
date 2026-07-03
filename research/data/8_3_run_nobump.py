"""
8_3_run_nobump.py -- the no-bump: compact U(1) deconfines, SU(2) stays confined.

The confinement order parameter (K_signal, the entroptics resolved-mode read on
raw configs) is read across beta 0..5 for BOTH gauge groups:
  * compact U(1) (foil): flat and low in the confined phase, then DIVERGES upward
    across the deconfinement transition (beta_c ~ 1.01). It crosses.
  * SU(2): stays flat and bounded across the whole range. No deconfinement -- the
    NO-BUMP. This is the discriminator that separates the two theories, untuned.

Reads come through the single typed wrapper on RAW configs (no preprocessing).
Writes 8_3_dat_nobump.csv and 8_3_fig_nobump.png here.

    python 8_3_run_nobump.py --mode quick   # coarse, small lattice
    python 8_3_run_nobump.py --mode full    # dense 0..5, 8^3x16
"""
from __future__ import annotations

import argparse
import os
import sys

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(_HERE, "..", "code")))

import entroptics
import generator
import table
import plot

DAT = os.path.join(_HERE, "8_3_dat_nobump.csv")
FIG = os.path.join(_HERE, "8_3_fig_nobump.png")
BETA_C = 1.01
COLS = ["group", "beta", "dims", "confinement", "confinement_err", "temporal_dominance", "n"]
STYLE = {"u1": ("#b03030", "compact U(1) (foil): deconfines"),
         "su2": ("#1f4e8c", "SU(2): stays confined (no-bump)")}


def measure(group, beta, dims, *, seed, therm, gap, n):
    cfgs = list(generator.stream(dims, beta, group=group, seed=seed, therm=therm, gap=gap, n=n))
    ks = np.array([entroptics.aperture(c).screen().K_signal for c in cfgs], float)
    r = entroptics.run(cfgs)
    return dict(group=group, beta=round(beta, 2), dims="x".join(map(str, dims)),
                confinement=float(ks.mean()), confinement_err=float(ks.std() / np.sqrt(len(ks))),
                temporal_dominance=r.temporal_dominance, n=len(cfgs))


def main():
    ap = argparse.ArgumentParser(description="No-bump: U(1) vs SU(2) confinement across 0..5.")
    ap.add_argument("--mode", choices=["quick", "full"], default="quick")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--n", type=int, default=None)
    args = ap.parse_args()

    if args.mode == "quick":
        dims, therm, gap = (6, 6, 6, 6), 120, 4
        betas = [round(b, 2) for b in np.arange(0.0, 5.01, 1.0)]
        n = args.n or 8
    else:
        dims, therm, gap = (8, 8, 8, 16), 200, 4
        betas = [round(b, 2) for b in np.arange(0.0, 5.01, 0.25)]
        n = args.n or 18

    print(f"lattice {dims}  therm={therm}  n={n}  gap={gap}")
    rows = []
    for group in ("u1", "su2"):
        print(f"-- {group} --")
        for i, beta in enumerate(betas):
            r = measure(group, beta, dims, seed=args.seed + i, therm=therm, gap=gap, n=n)
            print(f"  {group:>3} beta={beta:5.2f}  confinement={r['confinement']:6.3f} "
                  f"+/- {r['confinement_err']:.1e}")
            rows.append(r)

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
              title=r"Sec 8.3: the no-bump -- U(1) deconfines, SU(2) stays confined",
              vline=BETA_C, vline_label=r"U(1) $\beta_c\approx1.01$")
    print("wrote", DAT, "and", FIG)


if __name__ == "__main__":
    main()
