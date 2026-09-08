"""
8_3_run_su3_nobump.py -- N-invariance: SU(3) also stays confined (no-bump).

SU(3) confines at every beta, with a bulk crossover near beta ~ 5.7 but NO
deconfinement. Across its range (beta 5.0-7.0) the confinement order parameter
(K_signal, the entroptics resolved-mode read on raw configs) stays flat and
bounded -- the same no-bump SU(2) shows across 1-5. Together (with the U(1) foil
that crosses) this is the N-invariance leg: SU(2) and SU(3) give the same untuned
picture.

Reads through the single typed wrapper on RAW configs. Writes 8_3_dat_su3_nobump.csv
and 8_3_fig_su3_nobump.png here.

    python 8_3_run_su3_nobump.py --mode quick   # coarse, small lattice
    python 8_3_run_su3_nobump.py --mode full    # beta 5-7, 6^3x12
"""
from __future__ import annotations

import argparse
import os
import sys

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(_HERE, "..", "code")))

import entroptics_adapter as entroptics
import lattice_generator as generator
import table
import plot

DAT = os.path.join(_HERE, "8_3_dat_su3_nobump.csv")
FIG = os.path.join(_HERE, "8_3_fig_su3_nobump.png")
COLS = ["group", "beta", "dims", "confinement", "confinement_err", "n"]


def measure(beta, dims, *, seed, therm, gap, n, device=None):
    if device:                                             # batched-GPU generation, then CPU reads
        fb = generator.config_batch(dims, beta, group="su3", seed=seed, therm=therm, n=n, device=device)
        fb = fb.detach().cpu().numpy()
        cfgs = [fb[i] for i in range(fb.shape[0])]
    else:
        cfgs = list(generator.stream(dims, beta, group="su3", seed=seed, therm=therm, gap=gap, n=n))
    ks = np.array([entroptics.confinement(c) for c in cfgs], float)
    return dict(group="su3", beta=round(beta, 2), dims="x".join(map(str, dims)),
                confinement=float(ks.mean()),
                confinement_err=float(ks.std() / np.sqrt(len(ks))), n=len(cfgs))


def main():
    ap = argparse.ArgumentParser(description="SU(3) no-bump (N-invariance).")
    ap.add_argument("--mode", choices=["quick", "full"], default="quick")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--n", type=int, default=None)
    ap.add_argument("--device", default=None, help="torch device for batched-GPU generation, e.g. cuda")
    args = ap.parse_args()

    # gap = decorrelation sweeps between yielded configs, set from the measured integrated
    # autocorrelation time of the marginal-entropy read: SU(3) at beta~6 has tau_int(H) ~ 7
    # sweeps, so gap >= 2*tau_int ~ 14 to keep the ensemble draws effectively independent
    # (the empirical-Bernstein certificate assumes independence). therm > the ~90-sweep H plateau.
    if args.mode == "quick":
        dims, therm, gap = (4, 4, 4, 8), 120, 6
        betas = [5.0, 6.0, 7.0]
        n = args.n or 6
    else:
        dims, therm, gap = (6, 6, 6, 12), 200, 15
        betas = [round(b, 2) for b in np.arange(5.0, 7.01, 0.25)]
        n = args.n or 12

    print(f"SU(3) lattice {dims}  therm={therm}  n={n}")
    print(f"{'beta':>6} {'confine':>9} {'+/-':>8}")
    rows = []
    for i, beta in enumerate(betas):
        r = measure(beta, dims, seed=args.seed + i, therm=therm, gap=gap, n=n, device=args.device)
        print(f"{beta:6.2f} {r['confinement']:9.3f} {r['confinement_err']:8.1e}")
        rows.append(r)

    table.write(DAT, rows, COLS)
    plot.line(FIG, [r["beta"] for r in rows],
              [{"y": [r["confinement"] for r in rows], "yerr": [r["confinement_err"] for r in rows],
                "label": r"SU(3) confinement $K_{\mathrm{signal}}$", "color": "#2e7d32"}],
              xlabel=r"$\beta$", ylabel=r"confinement  $K_{\mathrm{signal}}$",
              title=r"Sec 8.3: SU(3) no-bump -- stays confined across the crossover (N-invariance)")
    print("wrote", DAT, "and", FIG)


if __name__ == "__main__":
    main()
