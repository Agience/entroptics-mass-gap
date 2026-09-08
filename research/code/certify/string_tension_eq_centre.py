"""string_tension_eq_centre.py -- Reads 3 + 4 on the crossover, feeding CentreDominance.string_tension_eq_centre.

Regenerates SU(2) links deterministically (``DEV`` = numpy or cuda) and, from the SAME links per beta, reads:

  Input 3  rho'_coset(1)  -- the coset (centre-removed, sign(q0)*q) single-cut maximal correlation, e^{-Delta}
                            of the connected DMD dominant mode. The coset is perimeter/short-range: rho'_coset < 1.
  Input 4  sigma_Z/sigma  -- the Creutz string tension chi(R,R) of the maximal-centre-gauge Z2 projection over the
                            full SU(2) tension. Centre dominance: sigma_Z/sigma -> 1.

  rho'(1)(full) is reported as the interior-mixing cross-check (Input 1).

Env: L, N, THERM, METHOD, DEV, MCG (gauge-fix sweeps), RT (Creutz R=T), BETAS (comma list; default the grid).
Split BETAS across GPUs with CUDA_VISIBLE_DEVICES for a parallel grid.
"""
from __future__ import annotations

import csv
import math
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # research/code
import lattice_generator as G
import entroptics_adapter as W

# The per-beta table is persisted as well as printed: these are Inputs 3 and 4 behind Lean
# `CentreDominance.string_tension_eq_centre`, and they reached the paper only through stdout.
OUT_CSV = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                       "data", "9_7_dat_centre_dominance.csv")

L = int(os.environ.get("L", "16"))
N = int(os.environ.get("N", "48"))
THERM = int(os.environ.get("THERM", "60"))
METHOD = os.environ.get("METHOD", "heatbath")
# The generator takes device=None for numpy and a torch device string otherwise (_Backend), so
# the CPU choice is None, not the word "numpy".  An unset DEV probes for CUDA and selects numpy
# when it is absent.  An explicit DEV=cuda is honoured and raises if the device is missing, so an
# explicit request for hardware reports its absence rather than running slower somewhere else.


DEV = G.resolve_device(os.environ.get("DEV"))
MCG_ITERS = int(os.environ.get("MCG", "60"))
RT = int(os.environ.get("RT", "3"))
DIMS = (L, L, L, 2 * L)
THR_MARGIN = 3.0 ** (-0.25)
_bs = os.environ.get("BETAS", "")
BETAS = [float(x) for x in _bs.split(",")] if _bs else \
    [0.80, 1.00, 1.20, 1.40, 1.60, 1.80, 2.00, 2.20, 2.40, 2.60]


def rho1(field):
    d = float(W.run([field[i] for i in range(field.shape[0])], time_axis=-1).mass_gap)
    return math.exp(-d) if d > 0 else 1.0


def main():
    print(f"SU(2) L={L} N={N} therm={THERM} {METHOD} dev={DEV} MCG={MCG_ITERS} chi({RT},{RT}); "
          f"rho1 thr: gap<1, margin<{THR_MARGIN:.4f}", flush=True)
    print(f"{'beta':>5} | {'r1_coset':>9} | {'sig_full':>8} {'sig_Z':>7} {'Z/full':>7} | {'sec':>5}",
          flush=True)
    rows = []
    for b in BETAS:
        t0 = time.time()
        links = G.gauge_field(DIMS, b, group="su2", seed=0, therm=THERM, batch=N, method=METHOD, device=DEV)
        px = G.action_density(links, group="su2", project="coset", device=DEV)
        rx = rho1(px)                                                                    # Input 3: rho'_coset(1)
        Lg = G.maximal_centre_gauge(links, group="su2", iters=MCG_ITERS, device=DEV)     # Read 4: gauge-fix
        sf = G.creutz_sigma(links, RT, RT, group="su2", project="full", device=DEV)      # gauge-invariant
        sz = G.creutz_sigma(Lg, RT, RT, group="su2", project="centre", device=DEV)       # Z2 after MCG
        ratio = sz / sf if sf > 0 else float("nan")
        print(f"{b:>5.2f} | {rx:>9.4f} | {sf:>8.4f} {sz:>7.4f} {ratio:>7.3f} | {time.time()-t0:>5.0f}",
              flush=True)
        rows.append(dict(beta="%.2f" % b, nconfigs=int(N), L=int(L), rho1_coset="%.6f" % rx,
                         sigma_full="%.6f" % sf, sigma_Z="%.6f" % sz,
                         Z_over_full=("" if ratio != ratio else "%.6f" % ratio)))

    # Every beta is generated here rather than loaded, so a short table means a coupling failed
    # rather than that its shards are missing -- either way the centre-dominance ratio would be
    # claimed over fewer couplings than BETAS names.
    if len(rows) != len(BETAS):
        raise SystemExit("read %d of %d couplings: refusing to write a partial centre-dominance table"
                         % (len(rows), len(BETAS)))

    # A row survives the check above even when its ratio did not resolve: `sigma_full <= 0` leaves
    # Z_over_full empty, and at strong coupling that is the normal outcome -- a chi(R,R) Creutz ratio
    # needs Wilson loops the ensemble can actually resolve, and W ~ (beta/4)^area is beneath the noise
    # at small beta. So the table can come out full-length with its load-bearing column blank, which
    # reads as a complete certificate and is not one: sigma_Z/sigma is the whole claim.
    resolved = [r for r in rows if r["Z_over_full"] != ""]
    print("  centre-dominance ratio resolved at %d of %d couplings: %s"
          % (len(resolved), len(rows), ", ".join(r["beta"] for r in resolved) or "none"), flush=True)
    if not resolved:
        raise SystemExit(
            "no coupling resolved sigma_Z/sigma (every sigma_full <= 0 or nan): refusing to write a\n"
            "  centre-dominance table that carries no centre-dominance measurement. The Creutz ratio\n"
            "  needs loops this ensemble resolves -- raise N (configs) or THERM, or scan couplings\n"
            "  where W(R,R) sits above the noise.")
    with open(OUT_CSV, "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=["beta", "nconfigs", "L", "rho1_coset", "sigma_full",
                                           "sigma_Z", "Z_over_full"])
        w.writeheader()
        w.writerows(rows)
    print("wrote %s (%d couplings)" % (OUT_CSV, len(rows)))


if __name__ == "__main__":
    main()
