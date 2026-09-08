"""
8_5_run_gap_calibration.py -- the instrument recovers a KNOWN gap (PAPER Sec 8.5).

Calibration against ground truth: a free scalar of mass m has an exact
time-correlation gap E0 = arccosh(1 + m^2/2). Fed raw configs, the entroptics gap
read `run(configs).mass_gap` recovers it. The gap read is the FORWARD operator
identification (library Aperture.connected_decay_rate = -log|mu_1| on the connected
Koopman/DMD spectrum): identify the linear operator from the trajectory and read its
dominant (slowest) mode rate -- borrowing the classical dynamical-systems machinery and
walking it FORWARD. Deterministic in the operator eigenvalues.

The read lands on E0, tightening to 0.2% at m=1.10 as the finite temporal extent
grows. This anchors the read as a gap instrument on the one field that carries its
gap directly, and shows it meets the classical picture at the seam.

Writes 8_5_dat_gap_calibration.csv and 8_5_fig_gap_calibration.png here.

    python 8_5_run_gap_calibration.py --mode quick   # few masses, small lattice
    python 8_5_run_gap_calibration.py --mode full    # denser, 8x8x64, 40 configs
"""
from __future__ import annotations

import argparse
import math
import os
import sys

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(_HERE, "..", "code")))

import entroptics_adapter as entroptics
import lattice_generator as generator
import table
import plot

DAT = os.path.join(_HERE, "8_5_dat_gap_calibration.csv")
FIG = os.path.join(_HERE, "8_5_fig_gap_calibration.png")
COLS = ["m", "E0", "mass_gap", "rel_err_pct", "dims", "n"]


def E0(m):
    return math.acosh(1 + m * m / 2)


def measure(m, dims, *, n):
    cfgs = [generator.free_scalar(dims, m, seed=s) for s in range(n)]
    mg = entroptics.run(cfgs).mass_gap    # the forward operator read (dominant Koopman/DMD mode rate)
    e0 = E0(m)
    return dict(m=round(m, 3), E0=round(e0, 4),
                mass_gap=round(mg, 4), rel_err_pct=round(100 * (mg - e0) / e0, 2),
                dims="x".join(map(str, dims)), n=n)


def main():
    ap = argparse.ArgumentParser(description="Free-scalar gap calibration (PAPER Sec 8.5).")
    ap.add_argument("--mode", choices=["quick", "full"], default="quick")
    ap.add_argument("--n", type=int, default=None)
    args = ap.parse_args()

    # `full` is the configuration the committed artifact is measured at; `quick` is a coarse smoke
    # run and writes to its own filename, so the two cannot be confused on disk. The committed table
    # is reproduced by `--mode full`, which is how research/regen_all.py invokes it.
    if args.mode == "quick":
        dims, masses, n = (8, 8, 48), [0.15, 0.40, 0.80], args.n or 24
        dat, fig = DAT.replace(".csv", "_quick.csv"), FIG.replace(".png", "_quick.png")
    else:
        dims, masses, n = (8, 8, 64), [0.20, 0.35, 0.50, 0.70, 0.90, 1.10], args.n or 40
        dat, fig = DAT, FIG

    print(f"lattice {dims}  n={n}")
    print(f"{'m':>6} {'E0':>8} {'mass_gap':>9} {'rel%':>7}")
    rows = []
    for m in masses:
        r = measure(m, dims, n=n)
        print(f"{r['m']:6.2f} {r['E0']:8.4f} {r['mass_gap']:9.4f} {r['rel_err_pct']:7.1f}")
        rows.append(r)

    table.write(dat, rows, COLS)
    E0s = [r["E0"] for r in rows]
    plot.line(fig, E0s,
              [{"y": [r["mass_gap"] for r in rows], "label": r"forward operator read $\mathtt{mass\_gap}=-\log|\mu_1|$"},
               {"y": E0s, "label": r"exact gap $E_0$ (y = x)", "color": "#888", "marker": "None"}],
              xlabel=r"true gap  $E_0 = \mathrm{arccosh}(1+m^2/2)$",
              ylabel=r"recovered gap  $\widehat{\Delta}$",
              title=r"Sec 8.5: the forward operator read recovers a known gap")
    print("wrote", DAT, "and", FIG)


if __name__ == "__main__":
    main()
