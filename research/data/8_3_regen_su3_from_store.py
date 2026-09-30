"""8_3_regen_su3_from_store.py -- regenerate the SU(3) K_signal CSV and figure from the
config store (collection configs_paper83), deterministic, through the WRAPPER.

Pins the confined-vacuum null (su2 b0.50) at the plane shape it reads -- 6x6, from L=6 -- then
reads K_signal per SU(3) 6^3x12 config across beta=5.0..7.0, each with its same-marginal control
(every plane's values permuted within the plane, config i seeded by its index, against the same
floor) and the paired difference. Writes 8_3_dat_su3_nobump.csv and 8_3_fig_su3_nobump.png here.

THE STORE HOLDS NO su2 b0.50 ENSEMBLE AT L=6, so there is no 6x6 confined-vacuum calibration and
this script REFUSES before reading. The floor is calibrated per plane shape: an 8x8 floor applied
to 6x6 planes reads the shape (every SU(3) coupling read 0.0000, shuffled or not), so no other
shape's reference is substituted. It runs once su2_L6_b0.50 is in the store.

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
COLS = ["group", "beta", "dims", "confinement", "confinement_err", "n",
        "confinement_shuffled", "confinement_shuffled_err", "confinement_minus_shuffled",
        "confinement_minus_shuffled_err"]
BETAS = [5.00, 5.25, 5.50, 5.75, 6.00, 6.25, 6.50, 6.75, 7.00]
# DERIVED: the spatial extent of the store's SU(3) ensembles (configs_paper83/su3_L6_*, manifest
# L=6); it fixes their plane shape, 6x6, and so the shape the reference must be pinned at.
L_SU3 = 6


def load(group, L, beta, ncap=128):
    for h in HOPS:
        fs = sorted(glob.glob(f"{h}/{group}_L{L}_b{beta:.2f}.s*.npy"))
        if fs:
            return np.asarray(np.concatenate([np.load(f) for f in fs], 0)[:ncap], dtype=np.float64)
    return None


def pin():
    """Pin the su2 b0.50 confined vacuum at the plane shape the SU(3) ensembles have (6x6, L=6).
    Refuses when the store has none: another L's planes would calibrate another shape's floor."""
    ref = load("su2", L_SU3, 0.50, ncap=48)
    if ref is None:
        raise SystemExit(
            f"8_3_regen_su3_from_store: no su2 L{L_SU3} b0.50 reference under "
            f"{ROOT or '<no store configured>'}. The SU(3) planes are {L_SU3}x{L_SU3} and the "
            f"floor is calibrated per plane shape, so without a confined vacuum at that shape there "
            f"is no floor to read K_signal against. Refusing; the committed artifact is not "
            f"overwritten.\n{store_path.hint()}")
    W.pin_reference(list(ref))
    return len(ref)


def main():
    n = pin()
    print(f"pinned confined-vacuum null: {n} su2 L{L_SU3} b0.50 configs, plane shapes {W.pinned_shapes()}")
    rows = []
    for b in BETAS:
        arr = load("su3", L_SU3, b)
        if arr is None:
            print(f"  su3 b{b:.2f}: (absent)")
            continue
        nc = arr.shape[0]
        ks = np.array([float(W.confinement(arr[i], -1)) for i in range(nc)], float)
        sh = np.array([float(W.confinement(arr[i], -1, shuffle=i)) for i in range(nc)], float)
        d = ks - sh                                   # paired per configuration
        se = lambda v: round(float(v.std() / np.sqrt(nc)), 4)   # the estimator confinement_err uses
        rows.append(dict(group="su3", beta=round(b, 2), dims="6x6x6x12",
                         confinement=round(float(ks.mean()), 4), confinement_err=se(ks), n=int(nc),
                         confinement_shuffled=round(float(sh.mean()), 4),
                         confinement_shuffled_err=se(sh),
                         confinement_minus_shuffled=round(float(d.mean()), 4),
                         confinement_minus_shuffled_err=se(d)))
        print(f"  su3 b{b:.2f}: K_signal={ks.mean():.4f} +/- {se(ks):.4f}  shuffled={sh.mean():.4f}  "
              f"real-shuffled={d.mean():+.4f} +/- {se(d):.4f}  n={nc}")
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
               label=r"SU(3) bulk crossover $\approx5.7$ (literature)")
    b = [r["beta"] for r in rows]
    ax.errorbar(b, [r["confinement"] for r in rows], yerr=[r["confinement_err"] for r in rows],
                marker="^", color="#2e7d32", lw=1.8, capsize=3,
                label=r"SU(3) $6^3\times12$: $K_{\mathrm{signal}}$")
    ax.errorbar(b, [r["confinement_shuffled"] for r in rows],
                yerr=[r["confinement_shuffled_err"] for r in rows], marker="^", mfc="none",
                ls="--", color="#2e7d32", lw=1.2, capsize=2, label="SU(3): within-plane shuffled")
    ax.set_xlabel(r"$\beta$")
    ax.set_ylabel(r"$K_{\mathrm{signal}}$ (plane mean)")
    ax.set_title(r"SU(3) $K_{\mathrm{signal}}$ vs $\beta$, $6^3\times12$, 6$\times$6 planes, "
                 r"su2 $\beta$=0.50 floor at 6$\times$6", fontsize=10)
    ax.legend(loc="best", fontsize=8)
    fig.tight_layout()
    fig.savefig(FIG, dpi=150)
    plt.close(fig)
    print("wrote", DAT, "and", FIG)


if __name__ == "__main__":
    main()
