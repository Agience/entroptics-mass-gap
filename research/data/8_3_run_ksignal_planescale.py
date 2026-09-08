"""8_3_run_ksignal_planescale.py -- the plane-size scaling of the confinement order parameter K_signal.

K_signal is a per-plane resolved-mode count, so its absolute level scales with the plane area (~L^2) while the
phase discrimination (the no-bump) is a fixed-lattice-size statement. Pins the confined-vacuum null (su2 b0.50)
exactly as 8_3_regen_from_store.py, then reads K_signal on the SAME SU(2) beta=2.30 ensemble at L=8 (8^3) and
L=16 (16^3). Reproduces the paper's 0.08-on-8^3 / 0.67-on-16^3 (Sec 8.3). Writes 8_3_dat_ksignal_planescale.csv.

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
COLS = ["group", "beta", "dims", "plane", "K_signal", "K_signal_err", "n"]


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
    for L in (8, 16):
        arr = load("su2", L, 2.30)
        if arr is None:
            continue
        ks = np.array([float(W.confinement(arr[i], -1)) for i in range(arr.shape[0])], float)
        rows.append(dict(group="su2", beta=round(2.30, 2), dims=f"{L}x{L}x{L}x{2 * L}", plane=f"{L}x{L}",
                         K_signal=round(float(ks.mean()), 4),
                         K_signal_err=round(float(ks.std() / np.sqrt(len(ks))), 4), n=int(arr.shape[0])))
        print(f"  su2 L{L} b2.30: K_signal={rows[-1]['K_signal']:.4f} +/- {rows[-1]['K_signal_err']:.4f}  n={rows[-1]['n']}")
    table.write(DAT, rows, COLS)
    print("wrote", DAT)


if __name__ == "__main__":
    main()
