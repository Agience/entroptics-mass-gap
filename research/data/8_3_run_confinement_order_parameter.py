"""
8_3_run_confinement_order_parameter.py -- PAPER Sec 8.3: run (data + figure).

Generate compact-U(1) configs, read each through the single Aperture front door,
and write both the data table (8_3_dat_*.csv) and the figure (8_3_fig_*.png) here.

The read is one call on the raw config field:

    K_signal = entroptics.aperture(field).screen().K_signal

the SVD modes standing above the Marchenko-Pastur noise floor of the whitened
screen. Structureless noise in the confined phase (K_signal ~ 0); a coherent
long-range mode resolves in the Coulomb phase (K_signal rises across beta_c).
Entroptics read only; no classic diagnostic is stored or plotted.

    python 8_3_run_confinement_order_parameter.py --mode quick   # small U(1)
    python 8_3_run_confinement_order_parameter.py --mode full    # 8^3x16
"""
from __future__ import annotations

import argparse
import os
import sys

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))          # research/data
sys.path.insert(0, os.path.normpath(os.path.join(_HERE, "..", "code")))

import entroptics                      # the read (Aperture front door)
import generator                       # the config
import table                           # generic CSV writer
import plot                            # generic figure

DAT = os.path.join(_HERE, "8_3_dat_confinement_order_parameter.csv")
FIG = os.path.join(_HERE, "8_3_fig_confinement_order_parameter.png")
BETA_C = 1.01
COLS = ["beta", "dims", "K_signal", "K_signal_err", "phase", "n"]


def measure(beta, dims, *, seed, therm, meas, gap):
    Ks = [entroptics.aperture(f).screen().K_signal
          for f in generator.stream(dims, beta, seed=seed, therm=therm, gap=gap, n=meas)]
    Ks = np.asarray(Ks, float)
    n = max(1, len(Ks))
    return dict(beta=beta, dims="x".join(map(str, dims)),
                K_signal=float(Ks.mean()), K_signal_err=float(Ks.std() / np.sqrt(n)),
                phase="confined" if beta < BETA_C else "Coulomb", n=len(Ks))


def main():
    ap = argparse.ArgumentParser(description="PAPER Sec 8.3 (compact U(1)): data + figure.")
    ap.add_argument("--mode", choices=["quick", "full"], default="quick")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--meas", type=int, default=None)
    ap.add_argument("--therm", type=int, default=None)
    args = ap.parse_args()

    if args.mode == "quick":
        dims, therm, meas, gap = (6, 6, 6, 6), args.therm or 120, args.meas or 8, 4
        betas = [0.80, 1.20]
    else:
        dims, therm, meas, gap = (8, 8, 8, 16), args.therm or 250, args.meas or 40, 5
        betas = [0.80, 0.95, 1.05, 1.20]

    print(f"lattice {dims}  therm={therm}  meas={meas}  gap={gap}")
    print(f"{'beta':>6} {'K_signal':>9} {'+/-':>8}   phase")
    rows = []
    for i, beta in enumerate(betas):
        r = measure(beta, dims, seed=args.seed + i, therm=therm, meas=meas, gap=gap)
        print(f"{beta:6.2f} {r['K_signal']:9.3f} {r['K_signal_err']:8.1e}   {r['phase']}")
        rows.append(r)

    table.write(DAT, rows, COLS)
    plot.line(FIG, [r["beta"] for r in rows],
              [{"y": [r["K_signal"] for r in rows], "yerr": [r["K_signal_err"] for r in rows],
                "label": r"$K_{\mathrm{signal}}$  (entroptics read)"}],
              xlabel=r"$\beta$", ylabel=r"resolved modes  $K_{\mathrm{signal}}$",
              title=r"Sec 8.3: compact U(1) -- resolved modes rise across deconfinement",
              vline=BETA_C, vline_label=r"$\beta_c\approx1.01$",
              vspan=(min(betas) - 0.05, BETA_C))
    print("wrote", DAT, "and", FIG)


if __name__ == "__main__":
    main()
