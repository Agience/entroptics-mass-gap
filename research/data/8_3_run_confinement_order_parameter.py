"""
8_3_run_confinement_order_parameter.py -- PAPER Sec 8.3: the compact-U(1) crossing table (data only).

Reads K_signal = entroptics.confinement(field) on the FROZEN store configs,
against the PINNED confined-vacuum null (su2 b0.50, [E] Def 8.2), plane-averaged over intact
spatial planes. This is the SAME data, pin, and read as the no-bump sweep (8_3_regen_from_store.py),
so the U(1) crossing table AGREES with the no-bump figure by construction and is reproducible from
the released dataset -- not a fresh Monte-Carlo draw.

Why the store, not fresh generation: right at the deconfinement transition (beta ~ beta_c ~ 1.01)
K_signal is thermalisation-dependent (critical slowing down -- the photon mode orders slowly, so K
keeps rising with Monte-Carlo time and does not converge at fixed sweeps). The frozen store configs
(compact U(1), L8, heatbath therm 50) are the reproducible ground truth the paper cites; a fresh draw
at a different thermalisation would not reproduce them. Reading the store pins the value to the
released data.

The pin is MANDATORY: the wrapper thresholds every K_signal against the calibrated confined-vacuum
floor, never the i.i.d.-Gaussian mp edge (PAPER Sec 8.1); an unpinned read raises.

    CONFIGS=/path/to/entroptics-lattice python 8_3_run_confinement_order_parameter.py
(or set CONFIGS once for the machine in the git-ignored local config file at the repository root)
"""
from __future__ import annotations

import glob
import os
import sys

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))          # research/data
sys.path.insert(0, os.path.normpath(os.path.join(_HERE, "..", "code")))

import entroptics_adapter as W                   # the read (Aperture front door) + null pin
import store_path                        # the ONE place the ensemble store is located
import table                             # generic CSV writer

# Store root from ``store_path``: the CONFIGS environment variable, then the git-ignored local
# config file at the repository root, then a refusal. There is deliberately no default: a literal
# path names one machine, and everywhere else it makes the sweep find nothing and still exit 0. Unconfigured resolves to None/[] rather than raising, so
# importing this file still works with no data release present; the refusal below is where it
# becomes loud, and ``store_path.hint()`` says which of the two cases it is.
ROOT = store_path.store_root(required=False)
HOPS = store_path.collections("configs_paper83", "configs_phase1", "configs_links_su2_density")
DAT = os.path.join(_HERE, "8_3_dat_confinement_order_parameter.csv")
COLS = ["beta", "dims", "K_signal", "K_signal_err", "phase", "n"]
BETA_C = 1.011                                              # compact U(1) deconfinement
# The store's U(1) L8 crossing grid -- fine (0.05) through the transition, coarser in the wings.
U1_BETAS = [0.40, 0.50, 0.60, 0.70, 0.80, 0.90, 0.95, 1.00, 1.05, 1.10,
            1.20, 1.30, 1.40, 1.50, 1.60, 1.70]


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
    print(f"{'beta':>6} {'K_signal':>9} {'+/-':>8}   phase   n")
    rows = []
    for beta in U1_BETAS:
        arr = load("u1", 8, beta)
        if arr is None:
            print(f"{beta:6.2f}   (missing in store, skipped)")
            continue
        ks = np.array([float(W.confinement(arr[i], -1)) for i in range(arr.shape[0])], float)
        m = float(ks.mean())
        rows.append(dict(beta=round(beta, 2), dims="8x8x8x16",
                         K_signal=round(m, 4),
                         K_signal_err=round(float(ks.std() / np.sqrt(len(ks))), 4),
                         phase="confined" if beta < BETA_C else "Coulomb", n=int(len(ks))))
        print(f"{beta:6.2f} {m:9.4f} {rows[-1]['K_signal_err']:8.4f}   "
              f"{rows[-1]['phase']:>8} {rows[-1]['n']}")

    # Refuse BEFORE writing. These read the frozen store and simply skip any coupling
    # they cannot find, so a store that is incomplete (or pointed at the wrong root)
    # produced a HEADER-only csv over the committed artifact and still exited 0 --
    # reporting success for a table with nothing in it.
    if len(rows) < 16:
        raise SystemExit(
            f"8_3_run_confinement_order_parameter: read {len(rows)} of 16 couplings for the compact-U(1) crossing table"
            f" under {HOPS}. Refusing to overwrite the committed artifact with a partial"
            f" table.\n{store_path.hint()}")

    table.write(DAT, rows, COLS)
    print("wrote", DAT)


if __name__ == "__main__":
    main()
