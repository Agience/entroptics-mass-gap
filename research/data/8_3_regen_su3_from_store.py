"""8_3_regen_su3_from_store.py -- regenerate the Sec 8.3 SU(3) no-bump CSV and figure from the
config store (collection configs_paper83), deterministic, through the WRAPPER.

Pins the confined-vacuum null (su2 b0.50), then reads K_signal per SU(3) 6^3x12 config across
beta=5.0..7.0. Pure SU(3) stays confined at every coupling: K_signal flat and low (the no-bump).
Writes 8_3_dat_su3_nobump.csv and 8_3_fig_su3_nobump.png here.

    CONFIGS=/path/to/entroptics-lattice python 8_3_regen_su3_from_store.py
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
DAT = os.path.join(_HERE, "8_3_dat_su3_nobump.csv")
FIG = os.path.join(_HERE, "8_3_fig_su3_nobump.png")
COLS = ["group", "beta", "dims", "confinement", "confinement_err", "n"]
BETAS = [5.00, 5.25, 5.50, 5.75, 6.00, 6.25, 6.50, 6.75, 7.00]


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


def main():
    n = pin()
    print(f"pinned confined-vacuum null: {n} su2 b0.50 configs")
    rows = []
    for b in BETAS:
        arr = load("su3", 6, b)
        if arr is None:
            print(f"  su3 b{b:.2f}: (absent)")
            continue
        ks = np.array([float(W.confinement(arr[i], -1)) for i in range(arr.shape[0])], float)
        rows.append(dict(group="su3", beta=round(b, 2), dims="6x6x6x12",
                         confinement=round(float(ks.mean()), 4),
                         confinement_err=round(float(ks.std() / np.sqrt(len(ks))), 4), n=int(arr.shape[0])))
        print(f"  su3 b{b:.2f}: K_signal={ks.mean():.4f} +/- {ks.std()/np.sqrt(len(ks)):.4f}  n={arr.shape[0]}")
    # Refuse BEFORE writing. These read the frozen store and simply skip any coupling
    # they cannot find, so a store that is incomplete (or pointed at the wrong root)
    # produced a HEADER-only csv over the committed artifact and still exited 0 --
    # reporting success for a table with nothing in it.
    if len(rows) < 9:
        raise SystemExit(
            f"8_3_regen_su3_from_store: read {len(rows)} of 9 couplings for the SU(3) beta sweep"
            f" under {HOPS}. Refusing to overwrite the committed artifact with a partial"
            f" table.\n{store_path.hint()}")

    table.write(DAT, rows, COLS)

    fig, ax = plt.subplots(figsize=(6.4, 4.2))
    ax.axvline(5.7, color="#2e7d32", ls=":", lw=1.2, alpha=0.7,
               label=r"SU(3) bulk crossover $\approx5.7$ (no deconfinement)")
    ax.errorbar([r["beta"] for r in rows], [r["confinement"] for r in rows],
                yerr=[r["confinement_err"] for r in rows], marker="^", color="#2e7d32", lw=1.8,
                capsize=3, label=r"SU(3) $6^3\times12$: stays confined (no-bump)")
    ax.set_ylim(0.0, 0.20)
    ax.set_xlabel(r"$\beta$")
    ax.set_ylabel(r"confinement  $K_{\mathrm{signal}}$")
    ax.set_title(r"Sec 8.3: the SU(3) no-bump -- flat and low across $\beta=5$-$7$")
    ax.legend(loc="best", fontsize=9)
    fig.tight_layout()
    fig.savefig(FIG, dpi=150)
    plt.close(fig)
    print("wrote", DAT, "and", FIG)


if __name__ == "__main__":
    main()
