"""8_3_regen_from_store.py -- regenerate the Sec 8.3 no-bump CSV and figure from the config
store, deterministic, through the WRAPPER.

Pins the confined-vacuum null (su2 b0.50), then reads confinement per config for the U(1) and
SU(2) sweeps (L8, 8^3x16). U(1) steps up across beta_c ~ 1.01 (deconfinement); SU(2) stays
flat and low (the no-bump). Writes 8_3_dat_nobump.csv and 8_3_fig_nobump.png here.

    CONFIGS=/path/to/entroptics-lattice python 8_3_regen_from_store.py
(or set CONFIGS once for the machine in the git-ignored local config file at the repository root)

SU(3) has a single beta (6.0) in the store, so its sweep figure is not regenerated here.
"""
from __future__ import annotations
import glob, math, os, sys
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
DAT = os.path.join(_HERE, "8_3_dat_nobump.csv")
FIG = os.path.join(_HERE, "8_3_fig_nobump.png")
COLS = ["group", "beta", "dims", "confinement", "confinement_err", "mu", "n"]
BETA_C = 1.01       # U(1) deconfinement (sharp)
BETA_X_SU2 = 2.2    # SU(2) bulk crossover (broad; NO deconfinement -- K stays flat through it)

U1 = [0.40, 0.50, 0.60, 0.70, 0.80, 0.90, 0.95, 1.00, 1.05, 1.10, 1.20, 1.30, 1.50, 1.70, 2.50]
SU2 = [0.50, 0.60, 0.80, 1.00, 1.20, 1.40, 1.60, 1.80, 2.00, 2.20, 2.30, 2.40, 2.60, 2.80]


def load(group, L, beta, ncap=128):
    for h in HOPS:
        fs = sorted(glob.glob(f"{h}/{group}_L{L}_b{beta:.2f}.s*.npy"))
        if fs:
            return np.asarray(np.concatenate([np.load(f) for f in fs], 0)[:ncap], dtype=np.float64)
    return None


def pin():
    ref = []
    for L in (8, 12, 16):
        a = load("su2", L, 0.50, ncap=48)
        if a is not None:
            ref += list(a)
    if not ref:
        raise SystemExit(f"no su2 b0.50 reference under {ROOT or '<no store configured>'}\n"
                         f"{store_path.hint()}")
    W.pin_reference(ref)
    return len(ref)


def sweep(group, L, betas):
    rows = []
    for beta in betas:
        arr = load(group, L, beta)
        if arr is None:
            continue
        ks = np.array([float(W.confinement(arr[i], -1)) for i in range(arr.shape[0])], float)
        r = W.run(list(arr), time_axis=-1)
        rows.append(dict(group=group, beta=round(beta, 2), dims=f"{L}x{L}x{L}x16",
                         confinement=round(float(ks.mean()), 4),
                         confinement_err=round(float(ks.std() / np.sqrt(len(ks))), 4),
                         mu=round(float(r.attenuation), 4), n=int(arr.shape[0])))
    return rows


def main():
    n = pin()
    print(f"pinned confined-vacuum null: {n} su2 b0.50 configs")
    rows = sweep("u1", 8, U1) + sweep("su2", 8, SU2)
    for r in rows:
        print(f"  {r['group']:>3} b{r['beta']:5.2f}  confinement={r['confinement']:.3f} +/- {r['confinement_err']:.3f}  n={r['n']}")
    # Refuse BEFORE writing. These read the frozen store and simply skip any coupling
    # they cannot find, so a store that is incomplete (or pointed at the wrong root)
    # produced a HEADER-only csv over the committed artifact and still exited 0 --
    # reporting success for a table with nothing in it.
    if len(rows) < 29:
        raise SystemExit(
            f"8_3_regen_from_store: read {len(rows)} of 29 couplings for the U(1) and SU(2) beta sweeps"
            f" under {HOPS}. Refusing to overwrite the committed artifact with a partial"
            f" table.\n{store_path.hint()}")

    table.write(DAT, rows, COLS)

    fig, ax = plt.subplots(figsize=(6.4, 4.2))
    ax.axvline(BETA_C, color="#888", ls="--", lw=1, label=r"U(1) $\beta_c\approx1.01$ (deconfinement)")
    ax.axvline(BETA_X_SU2, color="#1f4e8c", ls=":", lw=1.2, alpha=0.7,
               label=r"SU(2) bulk crossover $\approx2.2$ (no deconfinement)")
    for group, color, label in (("u1", "#b03030", "compact U(1) (foil): deconfines"),
                                ("su2", "#1f4e8c", "SU(2): stays confined (no-bump)")):
        g = [r for r in rows if r["group"] == group]
        ax.errorbar([r["beta"] for r in g], [r["confinement"] for r in g],
                    yerr=[r["confinement_err"] for r in g], marker="o", color=color, lw=1.8,
                    capsize=3, label=label)
    ax.set_xlabel(r"$\beta$")
    ax.set_ylabel(r"confinement  $K_{\mathrm{signal}}$")
    ax.set_title(r"Sec 8.3: the no-bump -- U(1) deconfines, SU(2) stays confined")
    ax.legend(loc="best", fontsize=8)
    fig.tight_layout()
    fig.savefig(FIG, dpi=150)
    plt.close(fig)
    print("wrote", DAT, "and", FIG)


if __name__ == "__main__":
    main()
