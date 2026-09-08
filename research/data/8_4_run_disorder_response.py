"""
8_4_run_disorder_response.py -- PAPER Sec 8.4: the disorder-response face (full Entroptic).

The SAME aperture, read as the Shannon entropy H = H_T + H_F of the config's power
marginals ([E Sec 2]) plane-averaged over intact spatial planes, gives the free-energy
curvature -dH/dbeta. No histogram, no bins: H is a direct Aperture read.

    H(beta) = mean_configs  entroptics.marginal_entropy(field)      # plane-averaged H_T + H_F

As a coherent long-range mode orders the field the marginals concentrate and H drops;
the drop is a SHARP spike in -dH/dbeta for compact U(1) at its deconfinement transition
(beta_c ~ 1.01), and a BROAD, gentle response for SU(2) across its crossover -- the same
instrument, sharp for the foil and smooth for the non-abelian theory. Reads come through
the single typed wrapper on RAW configs. Writes 8_4_dat_disorder_response.csv and
8_4_fig_disorder_response.png here.

    python 8_4_run_disorder_response.py --mode quick   # coarse, small lattice
    python 8_4_run_disorder_response.py --mode full    # dense, 8^3x16
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

DAT = os.path.join(_HERE, "8_4_dat_disorder_response.csv")
FIG = os.path.join(_HERE, "8_4_fig_disorder_response.png")
BETA_C = 1.01
COLS = ["group", "beta", "dims", "H", "H_err", "n"]
STYLE = {"u1": ("#b03030", "compact U(1) (foil): sharp spike at the transition"),
         "su2": ("#1f4e8c", "SU(2): broad, gentle crossover response")}


def measure(group, beta, dims, *, seed, therm, gap, n, device=None):
    if device:                                             # batched-GPU generation, then CPU reads
        fb = generator.config_batch(dims, beta, group=group, seed=seed, therm=therm, n=n, device=device)
        fb = fb.detach().cpu().numpy()
        cfgs = [fb[i] for i in range(fb.shape[0])]
    else:
        cfgs = list(generator.stream(dims, beta, group=group, seed=seed, therm=therm, gap=gap, n=n))
    H = np.array([entroptics.marginal_entropy(c) for c in cfgs], float)
    return dict(group=group, beta=round(beta, 3), dims="x".join(map(str, dims)),
                H=float(H.mean()), H_err=float(H.std() / np.sqrt(len(H))), n=len(cfgs))


def main():
    ap = argparse.ArgumentParser(description="Sec 8.4 disorder response -dH/dbeta (U(1) vs SU(2)).")
    ap.add_argument("--mode", choices=["quick", "full"], default="quick")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--n", type=int, default=None)
    ap.add_argument("--device", default=None, help="torch device for batched-GPU generation, e.g. cuda")
    args = ap.parse_args()

    if args.mode == "quick":
        dims, therm, gap = (6, 6, 6, 6), 120, 4
        betas = {"u1": np.arange(0.5, 2.01, 0.25), "su2": np.arange(1.5, 3.51, 0.25)}
        n = args.n or 8
    else:
        dims, therm, gap = (8, 8, 8, 16), 200, 4
        betas = {"u1": np.arange(0.5, 2.01, 0.10), "su2": np.arange(1.5, 3.51, 0.15)}
        n = args.n or 16

    print(f"lattice {dims}  therm={therm}  n={n}  gap={gap}")
    rows, curves = [], {}
    for group in ("u1", "su2"):
        bs = [round(float(b), 3) for b in betas[group]]
        Hs, Herr = [], []
        print(f"-- {group} --")
        for i, beta in enumerate(bs):
            r = measure(group, beta, dims, seed=args.seed + i, therm=therm, gap=gap, n=n, device=args.device)
            print(f"  {group:>3} beta={beta:5.2f}  H={r['H']:7.4f} +/- {r['H_err']:.4f}")
            rows.append(r); Hs.append(r["H"]); Herr.append(r["H_err"])
        b = np.array(bs); H = np.array(Hs)
        dHdb = -np.gradient(H, b)                       # free-energy curvature -dH/dbeta
        curves[group] = (b, dHdb, float(np.nanmax(dHdb)))

    table.write(DAT, rows, COLS)

    # plot.line shares one x-axis, so interpolate both curves onto a common beta grid.
    xu, du, _ = curves["u1"]; xs, ds, _ = curves["su2"]
    xall = np.unique(np.concatenate([xu, xs]))
    du_i = np.interp(xall, xu, du, left=np.nan, right=np.nan)
    ds_i = np.interp(xall, xs, ds, left=np.nan, right=np.nan)
    plot.line(FIG, list(xall),
              [{"y": list(du_i), "label": STYLE["u1"][1], "color": STYLE["u1"][0]},
               {"y": list(ds_i), "label": STYLE["su2"][1], "color": STYLE["su2"][0]}],
              xlabel=r"$\beta$", ylabel=r"disorder response  $-dH/d\beta$",
              title=r"Sec 8.4: $-dH/d\beta$ -- sharp U(1) transition vs broad SU(2) crossover",
              vline=BETA_C, vline_label=r"U(1) $\beta_c\approx1.01$")

    su, ss = curves["u1"][2], curves["su2"][2]
    print(f"\nsharpness (peak -dH/dbeta):  U(1)={su:.3f}   SU(2)={ss:.3f}   ratio={su/max(1e-9,ss):.1f}x")
    print("wrote", DAT, "and", FIG)


if __name__ == "__main__":
    main()
