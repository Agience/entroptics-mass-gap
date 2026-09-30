"""8_3_run_ksignal_planescale.py -- K_signal of one SU(2) coupling at two plane sizes.

Reads K_signal on the SU(2) beta=2.30 ensembles at L=8 (8^3x16, 8x8 planes) and L=16 (16^3x32, 16x16
planes). The floor is the su2 b0.50 confined vacuum pinned PER PLANE SHAPE -- the L=8 reference for the
8x8 planes and the L=16 reference for the 16x16 planes -- so each row is read against a floor calibrated
at its own shape. (A single floor calibrated on 8x8 planes and applied to both is what made the 16x16 row
read 3.59, shuffled or not: the shape, not the field.) Each row carries its same-marginal control: every
plane's values permuted within the plane (config i seeded by its index) against the same floor, and the
paired difference. Writes 8_3_dat_ksignal_planescale.csv.

    CONFIGS=/path/to/entroptics-lattice python 8_3_run_ksignal_planescale.py
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

# Store root from ``store_path``: the CONFIGS environment variable, then the git-ignored local
# config file at the repository root, then a refusal. There is deliberately no default: a literal
# path names one machine, and everywhere else it makes the sweep find nothing and still exit 0. Unconfigured resolves to None/[] rather than raising, so
# importing this file still works with no data release present; the refusal below is where it
# becomes loud, and ``store_path.hint()`` says which of the two cases it is.
ROOT = store_path.store_root(required=False)
HOPS = store_path.collections("configs_paper83", "configs_phase1", "configs_links_su2_density")
DAT = os.path.join(_HERE, "8_3_dat_ksignal_planescale.csv")
COLS = ["group", "beta", "dims", "plane", "K_signal", "K_signal_err", "n",
        "K_signal_shuffled", "K_signal_shuffled_err", "K_signal_minus_shuffled",
        "K_signal_minus_shuffled_err"]
# DERIVED: the two lattice extents the store holds the SU(2) beta=2.30 ensemble at with a su2 b0.50
# reference at the same extent (configs_phase1: L=8 and L=16); they fix the two plane shapes read.
LS = (8, 16)


def load(group, L, beta, ncap=128):
    for h in HOPS:
        fs = sorted(glob.glob(f"{h}/{group}_L{L}_b{beta:.2f}.s*.npy"))
        if fs:
            return np.asarray(np.concatenate([np.load(f) for f in fs], 0)[:ncap], dtype=np.float64)
    return None


def pin():
    """Pin the su2 b0.50 confined vacuum at each plane shape read: L=8 (8x8) and L=16 (16x16), 48
    configurations each. Refuses if either is missing -- no shape borrows another's floor."""
    ref = []
    for L in LS:
        a = load("su2", L, 0.50, ncap=48)
        if a is None:
            raise SystemExit(f"no su2 L{L} b0.50 reference under {ROOT or '<no store configured>'}\n"
                             f"{store_path.hint()}")
        ref += list(a)
    W.pin_reference(ref)
    return len(ref)


def main():
    n = pin()
    print(f"pinned confined-vacuum null: {n} su2 b0.50 configs, plane shapes {W.pinned_shapes()}")
    rows = []
    for L in LS:
        arr = load("su2", L, 2.30)
        if arr is None:
            continue
        nc = arr.shape[0]
        ks = np.array([float(W.confinement(arr[i], -1)) for i in range(nc)], float)
        sh = np.array([float(W.confinement(arr[i], -1, shuffle=i)) for i in range(nc)], float)
        d = ks - sh                                   # paired per configuration
        se = lambda v: round(float(v.std() / np.sqrt(nc)), 4)   # the estimator K_signal_err uses
        rows.append(dict(group="su2", beta=round(2.30, 2), dims=f"{L}x{L}x{L}x{2 * L}", plane=f"{L}x{L}",
                         K_signal=round(float(ks.mean()), 4), K_signal_err=se(ks), n=int(nc),
                         K_signal_shuffled=round(float(sh.mean()), 4), K_signal_shuffled_err=se(sh),
                         K_signal_minus_shuffled=round(float(d.mean()), 4),
                         K_signal_minus_shuffled_err=se(d)))
        r = rows[-1]
        print(f"  su2 L{L} b2.30: K_signal={r['K_signal']:.4f} +/- {r['K_signal_err']:.4f}  "
              f"shuffled={r['K_signal_shuffled']:.4f}  real-shuffled={r['K_signal_minus_shuffled']:+.4f} "
              f"+/- {r['K_signal_minus_shuffled_err']:.4f}  n={r['n']}")
    table.write(DAT, rows, COLS)
    print("wrote", DAT)


if __name__ == "__main__":
    main()
