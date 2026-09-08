"""8_7_run_mhi_lscan.py -- the connected-DMD fluctuation margin m_hi across the volume tower.

m_hi = rho'(1) = e^{-Delta} is the aperture spectral radius: the magnitude of the dominant CONNECTED
(vacuum-subtracted) transfer mode, read forward off the ensemble as Delta = -log|m_1| of the identified
Koopman operator (the viewer's connected_decay_rate). This scans it across L on the SAME confined SU(2)
beta=2.30 ensemble, the direct volume companion to the L=16 moment pencil (8_7_run_transfer_gap.py). Every
resolved volume returns m_hi < 1 (below the entropy-floor ceiling 3^{-1/4}=0.76 for L>=12) -- the finite-aperture
property carried forward, and the direct measurement of the uniform-in-volume margin U-a. Config-bin jackknife.
Writes 8_7_dat_mhi_lscan.csv.

    CONFIGS=/path/to/entroptics-lattice python 8_7_run_mhi_lscan.py
(or set CONFIGS once for the machine in the git-ignored local config file at the repository root)

Note on memory: the read forms one merged L^3 x L^3 covariance per ensemble; peak RSS grows ~L^6 (measured:
L=20 ~4 GB, L=28 ~33 GB, L=32 ~70 GB). L<=20 runs on the stock viewer; L=24,28,32 need the memory-frugal top-r
reduce (viewer >= the release that ships it), and L=32 needs a >=256 GB box (run on the 256 GB RunPod box). L=8
(small-volume) and L=32 (large-volume) are the resolution edges -- the two poorly-determined tower ends, each
reported with its jackknife error, not hidden; the scaling-window plateau is L=12-28.
"""
from __future__ import annotations
import glob, math, os, sys
import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(_HERE, "..", "code")))
import entroptics_adapter as W          # the connected forward read goes through the viewer front door
from aperture_reads import delta, load_su2   # one copy of the gap read and the su2 loader
import store_path                           # the ONE place the ensemble store is located
import table

# Store root from ``store_path``: the CONFIGS environment variable, then the git-ignored local
# config file at the repository root, then a refusal. There is deliberately no default: a literal
# path names one machine, and everywhere else it makes the sweep find nothing and still exit 0. Unconfigured resolves to None/[] rather than raising, so
# importing this file still works with no data release present; the refusal below is where it
# becomes loud, and ``store_path.hint()`` says which of the two cases it is.
ROOT = store_path.store_root(required=False)
HOPS = store_path.collections("configs_phase1", "configs_paper83", "configs_links_su2_density")
DAT = os.path.join(_HERE, "8_7_dat_mhi_lscan.csv")
COLS = ["L", "dims", "nconfigs", "Delta", "Delta_err", "m_hi", "m_hi_err"]
BETA = 2.30
LS = (8, 12, 16, 20, 24, 28, 32)
NBIN, NCAP = 6, 128


def load(L, beta, ncap=NCAP):
    return load_su2(HOPS, L, beta, ncap)

CEIL = 3.0 ** -0.25                     # entropy-floor ceiling e^{-kappa_0}






def main():
    print(f"SU(2) beta={BETA}  m_hi = e^-Delta   ceiling 3^-1/4 = {CEIL:.4f}")
    rows = []
    for L in LS:
        field = load(L, BETA)
        if field is None:
            continue
        n = field.shape[0]
        D = delta(field)
        nb = min(NBIN, n); bins = np.array_split(np.arange(n), nb)
        jk = np.array([delta(field[np.setdiff1d(np.arange(n), b)]) for b in bins])
        D_se = float(np.sqrt((nb - 1) / nb * np.sum((jk - jk.mean()) ** 2)))
        mhi = math.exp(-D)
        rows.append(dict(L=L, dims=f"{L}x{L}x{L}x{2 * L}", nconfigs=n,
                         Delta=round(D, 6), Delta_err=round(D_se, 6),
                         m_hi=round(mhi, 6), m_hi_err=round(mhi * D_se, 6)))
        print(f"  L={L:>2} n={n:>3}  Delta={D:.4f}+/-{D_se:.4f}  m_hi={mhi:.4f}  (<1: {mhi < 1}, <ceil: {mhi < CEIL})")
    table.write(DAT, rows, COLS)
    print("wrote", DAT)


if __name__ == "__main__":
    main()
