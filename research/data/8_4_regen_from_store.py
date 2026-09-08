"""8_4_regen_from_store.py -- regenerate the Sec 8.4 disorder-response CSV and figure from the
config store, deterministic, through the WRAPPER.

Reads the plane-averaged Shannon marginal entropy H = H_T + H_F per config (no floor, no
pinning) for the U(1) and SU(2) sweeps (L8, 8^3x16), then forms the free-energy curvature
-dH/dbeta by finite differences: a sharp spike for U(1) at beta_c ~ 1.01, a broad low response
for SU(2). Writes 8_4_dat_disorder_response.csv (the H sweep) and 8_4_fig_disorder_response.png
(the -dH/dbeta curves) here.

    CONFIGS=/path/to/entroptics-lattice python 8_4_regen_from_store.py
(or set CONFIGS once for the machine in the git-ignored local config file at the repository root)
"""
from __future__ import annotations
import glob, os, sys
import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(_HERE, "..", "code")))
import entroptics_adapter as W
import store_path                # the ONE place the ensemble store is located
import table

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

# Store root from ``store_path``: the CONFIGS environment variable, then the git-ignored local
# config file at the repository root, then a refusal. There is deliberately no default: a literal
# path names one machine, and everywhere else it makes the sweep find nothing and still exit 0. Unconfigured resolves to None/[] rather than raising, so
# importing this file still works with no data release present; the refusal below is where it
# becomes loud, and ``store_path.hint()`` says which of the two cases it is.
ROOT = store_path.store_root(required=False)
HOPS = store_path.collections("configs_paper83", "configs_phase1", "configs_links_su2_density")
DAT = os.path.join(_HERE, "8_4_dat_disorder_response.csv")
FIG = os.path.join(_HERE, "8_4_fig_disorder_response.png")
COLS = ["group", "beta", "dims", "H", "H_err", "n"]
BETA_C = 1.01       # U(1) deconfinement (sharp)
BETA_X_SU2 = 2.2    # SU(2) bulk crossover (broad; no deconfinement)

U1 = [0.40, 0.50, 0.60, 0.70, 0.80, 0.90, 0.95, 1.00, 1.05, 1.10, 1.20, 1.30, 1.50, 1.70]
SU2 = [0.50, 0.60, 0.80, 1.00, 1.20, 1.40, 1.60, 1.80, 2.00, 2.20, 2.30, 2.40, 2.60, 2.80]


def load(group, L, beta, ncap=128):
    for h in HOPS:
        fs = sorted(glob.glob(f"{h}/{group}_L{L}_b{beta:.2f}.s*.npy"))
        if fs:
            return np.asarray(np.concatenate([np.load(f) for f in fs], 0)[:ncap], dtype=np.float64)
    return None


def sweep(group, L, betas):
    rows = []
    for beta in betas:
        arr = load(group, L, beta)
        if arr is None:
            continue
        H = np.array([float(W.marginal_entropy(arr[i], -1)) for i in range(arr.shape[0])], float)
        rows.append(dict(group=group, beta=round(beta, 2), dims=f"{L}x{L}x{L}x16",
                         H=float(H.mean()), H_err=float(H.std() / np.sqrt(len(H))), n=int(arr.shape[0])))
    return rows


def deriv(rows):
    """(-dH/dbeta, beta_mid) by central-ish finite differences over consecutive betas."""
    b = [r["beta"] for r in rows]
    h = [r["H"] for r in rows]
    xs, ys = [], []
    for i in range(len(rows) - 1):
        xs.append(0.5 * (b[i] + b[i + 1]))
        ys.append(-(h[i + 1] - h[i]) / (b[i + 1] - b[i]))
    return xs, ys


def main():
    rows = sweep("u1", 8, U1) + sweep("su2", 8, SU2)

    # Validate before writing, so a short sweep -- a missing store subset, say -- is reported
    # against the group it is missing from and the committed table is left intact.
    for group in ("u1", "su2"):
        got = [r for r in rows if r["group"] == group]
        if len(got) < 2:
            raise SystemExit(
                f"8_4_regen_from_store: {group} matched {len(got)} configuration set(s) under"
                f" {HOPS}; the disorder response is a beta-derivative and needs at least two."
                f" Refusing rather than writing a partial table over the committed one."
                f"\n{store_path.hint()}")
    table.write(DAT, rows, COLS)
    fig, ax = plt.subplots(figsize=(6.4, 4.2))
    ax.axvline(BETA_C, color="#888", ls="--", lw=1, label=r"U(1) $\beta_c\approx1.01$ (deconfinement)")
    ax.axvline(BETA_X_SU2, color="#1f4e8c", ls=":", lw=1.2, alpha=0.7,
               label=r"SU(2) bulk crossover $\approx2.2$ (no deconfinement)")
    for group, color, label in (("u1", "#b03030", "compact U(1) (foil): sharp spike"),
                                ("su2", "#1f4e8c", "SU(2): broad, gentle response")):
        g = [r for r in rows if r["group"] == group]
        xs, ys = deriv(g)
        ax.plot(xs, ys, marker="o", color=color, lw=1.8, label=label)
        peak = max(ys)
        print(f"  {group}: peak -dH/dbeta = {peak:.3f}")
    ax.set_xlabel(r"$\beta$")
    ax.set_ylabel(r"disorder response  $-dH/d\beta$")
    ax.set_title(r"Sec 8.4: disorder response -- U(1) spike vs SU(2) crossover")
    ax.legend(loc="best", fontsize=8)
    fig.tight_layout()
    fig.savefig(FIG, dpi=150)
    plt.close(fig)
    print("wrote", DAT, "and", FIG)


if __name__ == "__main__":
    main()
