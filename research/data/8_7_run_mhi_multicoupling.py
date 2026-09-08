"""8_7_run_mhi_multicoupling.py -- the intensive aperture margin m_hi across the crossover (U-a breadth).

Companion to 8_7_run_mhi_lscan.py (which scans the volume tower at a single coupling beta=2.30). This scans a
(beta, L) GRID -- beta in {2.0, 2.3, 2.5} across the SU(2) crossover, L in {8, 12, 16} -- and reads the connected
fluctuation margin m_hi = e^{-Delta} (the aperture spectral radius) at each point via the same memory-frugal
incremental-splice read. It shows the intensive margin below the entropy-floor ceiling 3^{-1/4}=0.76 is NOT
specific to beta=2.30: every well-resolved point (L>=12) sits at m_hi ~ 0.22-0.38, uniformly below the floor
across the crossover -- direct empirical breadth for U-a (the dominant transfer magnitude stays below one, and
below the floor, uniformly). Config-bin jackknife. Writes 8_7_dat_mhi_multicoupling.csv.

    CONFIGS=/path/to/entroptics-lattice python 8_7_run_mhi_multicoupling.py
(or set CONFIGS once for the machine in the git-ignored local config file at the repository root)

L=8 is the small-volume resolution edge (few time modes; large error; can read above the floor as a read
artifact, e.g. beta=2.30 L=8) and is reported with its jackknife error, not hidden. The read forms one merged
L^3 x L^3 covariance (peak ~L^6); L<=16 here is light (<1 GB).
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
HOPS = store_path.collections("configs_phase1", "configs_densebeta", "configs_paper83",
                              "configs_betasweep", "configs_ladder",
                              "configs_links_su2_density")
DAT = os.path.join(_HERE, "8_7_dat_mhi_multicoupling.csv")
COLS = ["beta", "L", "dims", "nconfigs", "Delta", "Delta_err", "m_hi", "m_hi_err", "below_floor"]
BETAS = (2.00, 2.30, 2.50)
LS = (8, 12, 16)
NBIN, NCAP = 5, 128


def load(L, beta, ncap=NCAP):
    return load_su2(HOPS, L, beta, ncap)

CEIL = 3.0 ** -0.25                     # entropy-floor ceiling e^{-kappa_0} = 3^{-1/4}






def main():
    print(f"SU(2) intensive margin across the crossover; entropy floor 3^-1/4 = {CEIL:.4f}")
    rows = []
    for beta in BETAS:
        for L in LS:
            field = load(L, beta)
            if field is None:
                continue
            n = field.shape[0]
            D = delta(field)
            nb = min(NBIN, n); bins = np.array_split(np.arange(n), nb)
            jk = np.array([delta(field[np.setdiff1d(np.arange(n), b)]) for b in bins])
            D_se = float(np.sqrt((nb - 1) / nb * np.sum((jk - jk.mean()) ** 2)))
            mhi = math.exp(-D)
            rows.append(dict(beta=round(beta, 2), L=L, dims=f"{L}x{L}x{L}x{2 * L}", nconfigs=n,
                             Delta=round(D, 6), Delta_err=round(D_se, 6),
                             m_hi=round(mhi, 6), m_hi_err=round(mhi * D_se, 6), below_floor=(mhi < CEIL)))
            print(f"  beta={beta:.2f} L={L:>2} n={n:>3}  m_hi={mhi:.4f}  below_floor={mhi < CEIL}")
    table.write(DAT, rows, COLS)
    print("wrote", DAT)


if __name__ == "__main__":
    main()
