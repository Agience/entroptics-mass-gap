"""8_3_regen_from_store.py -- regenerate the Sec 8.3 U(1) and SU(2) K_signal sweeps (CSV and
figure) from the config store, deterministic, through the WRAPPER.

Pins the confined-vacuum null (su2 b0.50) at the plane shape it reads (8x8, from L=8), then reads
K_signal (the ``confinement`` column) per config for the compact-U(1) and SU(2) sweeps (L8,
8^3x16). Each value is written with its same-marginal control: the same configurations read with
every plane's values permuted within the plane (``confinement(..., shuffle=i)``, config i seeded
by its index) against the same floor, and the per-configuration difference with its paired
standard error. Writes 8_3_dat_nobump.csv and 8_3_fig_nobump.png here.

    CONFIGS=/path/to/entroptics-lattice python 8_3_regen_from_store.py
(or set CONFIGS once for the machine in the git-ignored local config file at the repository root)

The SU(3) 6^3x12 sweep is 8_3_regen_su3_from_store.py's.
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
COLS = ["group", "beta", "dims", "confinement", "confinement_err", "mu", "n",
        "confinement_shuffled", "confinement_shuffled_err", "confinement_minus_shuffled",
        "confinement_minus_shuffled_err"]
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
    """Pin the su2 b0.50 confined vacuum at the one plane shape these sweeps read (8x8, from L=8).
    The pin is calibrated per plane shape, so a reference at another L would calibrate a shape
    these sweeps never read."""
    ref = load("su2", 8, 0.50, ncap=48)
    if ref is None:
        raise SystemExit(f"no su2 L8 b0.50 reference under {ROOT or '<no store configured>'}\n"
                         f"{store_path.hint()}")
    W.pin_reference(list(ref))
    return len(ref)


def sweep(group, L, betas):
    rows = []
    for beta in betas:
        arr = load(group, L, beta)
        if arr is None:
            continue
        n = arr.shape[0]
        ks = np.array([float(W.confinement(arr[i], -1)) for i in range(n)], float)
        sh = np.array([float(W.confinement(arr[i], -1, shuffle=i)) for i in range(n)], float)
        d = ks - sh                                   # paired per configuration
        se = lambda v: round(float(v.std() / np.sqrt(n)), 4)   # the estimator confinement_err uses
        r = W.run(list(arr), time_axis=-1)
        rows.append(dict(group=group, beta=round(beta, 2), dims=f"{L}x{L}x{L}x16",
                         confinement=round(float(ks.mean()), 4), confinement_err=se(ks),
                         mu=round(float(r.attenuation), 4), n=int(n),
                         confinement_shuffled=round(float(sh.mean()), 4),
                         confinement_shuffled_err=se(sh),
                         confinement_minus_shuffled=round(float(d.mean()), 4),
                         confinement_minus_shuffled_err=se(d)))
    return rows


def main():
    n = pin()
    print(f"pinned confined-vacuum null: {n} su2 L8 b0.50 configs, plane shapes {W.pinned_shapes()}")
    rows = sweep("u1", 8, U1) + sweep("su2", 8, SU2)
    for r in rows:
        print(f"  {r['group']:>3} b{r['beta']:5.2f}  confinement={r['confinement']:.4f} +/- "
              f"{r['confinement_err']:.4f}  shuffled={r['confinement_shuffled']:.4f}  "
              f"real-shuffled={r['confinement_minus_shuffled']:+.4f} +/- "
              f"{r['confinement_minus_shuffled_err']:.4f}  n={r['n']}")
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

    fig, (ax, axd) = plt.subplots(1, 2, figsize=(12.0, 4.4))
    for a in (ax, axd):
        a.axvline(BETA_C, color="#888", ls="--", lw=1,
                  label=r"compact U(1) $\beta_c\approx1.01$ (literature)")
        a.axvline(BETA_X_SU2, color="#1f4e8c", ls=":", lw=1.2, alpha=0.7,
                  label=r"SU(2) bulk crossover $\approx2.2$ (literature)")
    for group, color, name in (("u1", "#b03030", "compact U(1)"), ("su2", "#1f4e8c", "SU(2)")):
        g = [r for r in rows if r["group"] == group]
        b = [r["beta"] for r in g]
        ax.errorbar(b, [r["confinement"] for r in g], yerr=[r["confinement_err"] for r in g],
                    marker="o", color=color, lw=1.8, capsize=3, label=f"{name}: $K_{{\\mathrm{{signal}}}}$")
        ax.errorbar(b, [r["confinement_shuffled"] for r in g],
                    yerr=[r["confinement_shuffled_err"] for r in g], marker="o", mfc="none",
                    ls="--", color=color, lw=1.2, capsize=2, label=f"{name}: within-plane shuffled")
        axd.errorbar(b, [r["confinement_minus_shuffled"] for r in g],
                     yerr=[r["confinement_minus_shuffled_err"] for r in g], marker="o", color=color,
                     lw=1.8, capsize=3, label=f"{name}: real $-$ shuffled (paired)")
    axd.axhline(0.0, color="#444", lw=0.8)
    ax.set_xlabel(r"$\beta$")
    ax.set_ylabel(r"$K_{\mathrm{signal}}$ (plane mean)")
    ax.set_title(r"$K_{\mathrm{signal}}$ vs $\beta$, $8^3\times16$, 8$\times$8 planes, su2 $\beta$=0.50 floor",
                 fontsize=10)
    ax.legend(loc="best", fontsize=7)
    axd.set_xlabel(r"$\beta$")
    axd.set_ylabel(r"$K_{\mathrm{signal}} - K_{\mathrm{signal}}^{\mathrm{shuffled}}$")
    axd.set_title(r"$K_{\mathrm{signal}}$ minus its within-plane-shuffled read (same configurations)",
                  fontsize=10)
    axd.legend(loc="best", fontsize=7)
    fig.tight_layout()
    fig.savefig(FIG, dpi=150)
    plt.close(fig)
    print("wrote", DAT, "and", FIG)


if __name__ == "__main__":
    main()
