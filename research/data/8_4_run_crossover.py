"""
8_4_run_crossover.py -- the compact-U(1) crossover across the full coupling (0..5).

The confinement order parameter (K_signal, the entroptics resolved-mode read) is
flat and near zero in the confined phase and rises sharply across the compact-U(1)
deconfinement transition (beta_c ~ 1.01). This is the abelian FOIL: it crosses.
The SU(N) no-bump (order parameter flat across the whole range) is the companion
contrast and needs the SU(2) generator.

Reads come through the single typed wrapper on RAW configs (no preprocessing):
    r = entroptics.run(configs)
    r.confinement          # K_signal, the order parameter (plotted)
    r.temporal_dominance   # leading temporal-mode contrast (recorded)
    r.mass_gap             # DMD slowest rate (recorded; free-scalar-calibrated instrument)

Writes 8_4_dat_crossover.csv and 8_4_fig_crossover.png here.

    python 8_4_run_crossover.py --mode quick   # coarse, small lattice
    python 8_4_run_crossover.py --mode full    # dense 0..5, 8^3x16
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

DAT = os.path.join(_HERE, "8_4_dat_crossover.csv")
FIG = os.path.join(_HERE, "8_4_fig_crossover.png")
BETA_C = 1.01
COLS = ["beta", "dims", "confinement", "confinement_err", "temporal_dominance", "mass_gap", "n"]


def measure(beta, dims, *, seed, therm, gap, n):
    cfgs = list(generator.stream(dims, beta, seed=seed, therm=therm, gap=gap, n=n))
    ks = np.array([entroptics.aperture(c).screen().K_signal for c in cfgs], float)  # per-config
    r = entroptics.run(cfgs)                                                          # ensemble reads
    return dict(beta=round(beta, 2), dims="x".join(map(str, dims)),
                confinement=float(ks.mean()), confinement_err=float(ks.std() / np.sqrt(len(ks))),
                temporal_dominance=r.temporal_dominance, mass_gap=r.mass_gap, n=len(cfgs))


def main():
    ap = argparse.ArgumentParser(description="Compact-U(1) crossover across 0..5.")
    ap.add_argument("--mode", choices=["quick", "full"], default="quick")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--n", type=int, default=None, help="configs per beta")
    args = ap.parse_args()

    if args.mode == "quick":
        dims, therm, gap = (6, 6, 6, 6), 120, 4
        betas = [round(b, 2) for b in np.arange(0.0, 5.01, 1.0)]
        n = args.n or 8
    else:
        dims, therm, gap = (8, 8, 8, 16), 250, 4
        betas = [round(b, 2) for b in np.arange(0.0, 5.01, 0.25)]
        n = args.n or 20

    print(f"lattice {dims}  therm={therm}  n={n}  gap={gap}")
    print(f"{'beta':>6} {'confine':>9} {'+/-':>8} {'temp_dom':>9} {'mass_gap':>9}")
    rows = []
    for i, beta in enumerate(betas):
        r = measure(beta, dims, seed=args.seed + i, therm=therm, gap=gap, n=n)
        print(f"{beta:6.2f} {r['confinement']:9.3f} {r['confinement_err']:8.1e} "
              f"{r['temporal_dominance']:9.4f} {r['mass_gap']:9.4f}")
        rows.append(r)

    table.write(DAT, rows, COLS)
    plot.line(FIG, [r["beta"] for r in rows],
              [{"y": [r["confinement"] for r in rows], "yerr": [r["confinement_err"] for r in rows],
                "label": r"confinement $K_{\mathrm{signal}}$ (entroptics)"}],
              xlabel=r"$\beta$", ylabel=r"resolved modes  $K_{\mathrm{signal}}$",
              title=r"Sec 8.4: compact U(1) crossover -- the foil deconfines at $\beta_c$",
              vline=BETA_C, vline_label=r"$\beta_c\approx1.01$",
              vspan=(min(r["beta"] for r in rows) - 0.05, BETA_C))
    print("wrote", DAT, "and", FIG)


if __name__ == "__main__":
    main()
