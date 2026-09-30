"""
8_3_run_su3_nobump.py -- SU(3) K_signal across beta 5.0-7.0 on FRESH Monte-Carlo configurations
(an exploratory path; 8_3_regen_su3_from_store.py is the store-reading sweep).

K_signal (the entroptics resolved-mode read on raw configs) is read at each coupling with its
same-marginal control: the same configurations with every plane's values permuted within the plane
(config i seeded by its index), and the paired difference.

K_signal needs a reference null pinned at the plane shape it reads, and this script pins none: run
as it stands, the first read raises. Pin a confined reference at the lattice's plane shape
(entroptics_adapter.pin_reference) before calling main().

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
COLS = ["group", "beta", "dims", "confinement", "confinement_err", "n",
        "confinement_shuffled", "confinement_shuffled_err", "confinement_minus_shuffled",
        "confinement_minus_shuffled_err"]


def measure(beta, dims, *, seed, therm, gap, n, device=None):
    if device:                                             # batched-GPU generation, then CPU reads
        fb = generator.config_batch(dims, beta, group="su3", seed=seed, therm=therm, n=n, device=device)
        fb = fb.detach().cpu().numpy()
        cfgs = [fb[i] for i in range(fb.shape[0])]
    else:
        cfgs = list(generator.stream(dims, beta, group="su3", seed=seed, therm=therm, gap=gap, n=n))
    ks = np.array([entroptics.confinement(c) for c in cfgs], float)
    # the same-marginal control: every plane's values permuted within the plane, config i seeded i
    sh = np.array([entroptics.confinement(c, shuffle=i) for i, c in enumerate(cfgs)], float)
    d = ks - sh                                           # paired per configuration
    se = lambda v: float(v.std() / np.sqrt(len(v)))       # the estimator confinement_err uses
    return dict(group="su3", beta=round(beta, 2), dims="x".join(map(str, dims)),
                confinement=float(ks.mean()), confinement_err=se(ks), n=len(cfgs),
                confinement_shuffled=float(sh.mean()), confinement_shuffled_err=se(sh),
                confinement_minus_shuffled=float(d.mean()), confinement_minus_shuffled_err=se(d))


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
                "label": r"SU(3) $K_{\mathrm{signal}}$", "color": "#2e7d32"}],
              xlabel=r"$\beta$", ylabel=r"$K_{\mathrm{signal}}$ (plane mean)",
              title=r"SU(3) $K_{\mathrm{signal}}$ vs $\beta$, " + "x".join(map(str, dims)))
    print("wrote", DAT, "and", FIG)


if __name__ == "__main__":
    main()
