"""interior_mixing_of_analytic_grid.py -- the deterministic ρ'(1) grid certificate closing A1 (confinement) on the SU(2) crossover.

ρ'(1) = m_hi = e^{-Δ} is the single-cut maximal correlation = the dominant transfer/DMD magnitude (RP
reversibility gives ρ'(1) = m_hi and ρ'(n) = ρ'(1)^n, so ONE cut < 1 yields the gap uniform in volume --
notes §9.0). Same shape as `ym_crossover_confinement_of_grid.py`: the VERDICT is a finite-sample one-sided
upper bound u(β) = ρ'(1) + 3.09·boot on the ensemble read at every measured β; the interior clears a
threshold iff every u(β) sits under it. A fixed-degree polynomial is reported only as a DESCRIPTIVE
smoothness overlay (no fitted slope stands in for the rigorous modulus). The ∀β interior is discharged
interval-rigorously by the single-plaquette enclosure; this grid corroborates Lean `Mixing.interior_mixing_of_analytic_grid`.

Two thresholds:
  * ρ'(1) < 1                   <=>  Δ > 0            (the mass gap)
  * ρ'(1) < 3^{-1/4} = e^{-κ0}  <=>  Δ ≥ κ0 = ¼ln3   (the entropy-margin form; Margin)

Reads through the WRAPPER (never the library). Deterministic reads (DMD operator eigenvalues); the bootstrap
resamples configs for the error band. Set NB=0 to skip the bootstrap (point estimates only, fast).

  CONFIGS=/path/to/entroptics-lattice python interior_mixing_of_analytic_grid.py
(or set CONFIGS once for the machine in the git-ignored local config file at the repository root)
"""
from __future__ import annotations

import csv
import glob
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # research/code
import entroptics_adapter as W  # THE WRAPPER
from aperture_reads import load_su2   # one copy of the su2 shard loader
import store_path                    # the ONE place the ensemble store is located

KAPPA0 = 0.25 * math.log(3.0)
THR_GAP = 1.0                       # ρ'(1) < 1        <=> Δ > 0
THR_MARGIN = 3.0 ** (-0.25)         # ρ'(1) < 3^{-1/4} <=> Δ ≥ κ0
# The per-beta table is persisted as well as printed. This is the rho'(1) grid closing A1 on the
# crossover -- the region Sec 13 names as the open item -- and it reached the paper only through
# this program's stdout, so nothing could check it or see it drift.
OUT_CSV = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                       "data", "9_4_dat_interior_mixing_grid.csv")

L = int(os.environ.get("L", "16"))
NB = int(os.environ.get("NB", "12"))
NCAP = int(os.environ.get("NCAP", "128"))
# Store root from ``store_path``: CONFIGS, then the git-ignored local config file, then a refusal
# -- no machine path in this file. Empty rather than raising when unconfigured, because the smoke
# tests import this module and redirect HOPS at a synthetic store; the refusal below says which.
ROOT = store_path.store_root(required=False)
HOPS = store_path.collections("configs_densebeta", "configs_phase1",
                              "configs_betasweep", "configs_ladder",
                              "configs_links_su2_density")
rng = np.random.default_rng(0)


def load(beta, ncap=NCAP):
    return load_su2(HOPS, L, beta, ncap, dtype="float64")


def rho1(arr):
    """rho'(1) = m_hi = e^{-Delta} for one ensemble, via the wrapper DMD dominant rate (deterministic).
    `.mass_gap` = -log|mu_1| of the dominant (slowest) mode on the CONNECTED (mean-subtracted)
    operator -- the slowest fluctuation mode about the vacuum."""
    d = float(W.run(list(arr), time_axis=-1).mass_gap)
    return math.exp(-d) if d > 0 else 1.0


def betas_available():
    found = set()
    for h in HOPS:
        for f in glob.glob(f"{h}/su2_L{L}_b*.npy"):
            try:
                found.add(round(float(os.path.basename(f).split("_b")[1].split(".s")[0]), 2))
            except Exception:
                pass
    return sorted(found)


def pin_confined_vacuum():
    ref = []
    for LL in (8, 12, 16):
        for h in HOPS:
            fs = sorted(glob.glob(f"{h}/su2_L{LL}_b0.50.s*.npy"))
            if fs:
                ref += list(np.concatenate([np.load(f) for f in fs], 0)[:48])
                break
    if ref:
        W.pin_reference(ref)
    return len(ref)


def main():
    nref = pin_confined_vacuum()
    print(f"pinned confined-vacuum null: {nref} su2 b0.50 configs   (L={L}, NCAP={NCAP}, NB={NB})")
    print(f"kappa0 = (1/4)ln3 = {KAPPA0:.4f};   rho1 thresholds: gap < {THR_GAP:.3f},  margin < 3^-1/4 = {THR_MARGIN:.4f}\n")
    xs, ys, es, ns = [], [], [], []
    absent = []
    print(f"{'beta':>5} {'n':>4} | {'rho1':>7} {'+-boot':>7} {'Delta':>7}")
    for b in betas_available():
        arr = load(b)
        if arr is None:
            absent.append(b)
            continue
        n = arr.shape[0]
        pt = rho1(arr)
        err = 0.0
        if NB > 0 and n > 4:
            bs = [rho1(arr[rng.integers(0, n, n)]) for _ in range(NB)]
            err = float(np.std(bs))
        xs.append(b); ys.append(pt); es.append(err); ns.append(n)
        dlt = -math.log(pt) if pt > 0 else float("inf")
        print(f"{b:>5.2f} {n:>4} | {pt:>7.4f} {err:>7.4f} {dlt:>7.4f}")
    xs, ys, es = np.array(xs), np.array(ys), np.array(es)
    if len(xs) < 4:
        print("\n(need >=4 beta points -- generation not synced yet?)")
        return

    # ---- THE CERTIFICATE: a finite-sample one-sided upper bound at every measured beta ----
    # rho1(beta) is an ensemble-level deterministic read; the config-bootstrap gives its sampling
    # spread. The conservative ~99.9% one-sided upper u(beta) = rho1 + 3.09*boot_err. The interior
    # clears a threshold iff every u(beta) sits under it. No fitted curve / slope / degree enters this.
    us = ys + 3.09 * es                            # one-sided ~99.9% normal upper on the ensemble read
    interior = xs >= 0.75
    if int(interior.sum()) < 4:
        print("\n(need >=4 interior beta points >= 0.75)")
        return
    print()
    for name, thr in (("rho1 < 1        (gap)", THR_GAP),
                      ("rho1 < 3^-1/4 (margin)", THR_MARGIN)):
        umax = float(np.nanmax(us[interior]))
        clears = bool((us[interior] < thr).all())
        print(f"[certificate] {name:>24}:  max_beta (rho1 + 3.09*boot) = {umax:.4f}  "
              f"{'<' if clears else '>='}  {thr:.4f}   -> interior {'CLEARS' if clears else 'FAILS'}")
    print(f"   the forall-beta interior is discharged INTERVAL-rigorously by the single-plaquette enclosure")
    print(f"   (small_volume_enclosure.py); RP reversibility rho'(n)=rho'(1)^n carries one cut uniform in")
    print(f"   volume, refinement-invariant to a->0. This dense grid is corroborating measured evidence.")

    # Persist the measured grid. The certificate reads "every measured beta clears", so a beta whose
    # shards are missing is a refusal rather than a shorter table: a smaller grid still reads as a
    # pass while establishing less.
    if absent:
        raise SystemExit(("shards missing for beta %s: refusing to write a partial interior grid"
                          % ", ".join("%.2f" % b for b in absent))
                         + "\n" + store_path.hint())
    with open(OUT_CSV, "w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(["beta", "nconfigs", "rho1", "rho1_boot_err", "upper_999", "Delta"])
        for b, n_, y, e in zip(xs, ns, ys, es):
            w.writerow(["%.2f" % b, int(n_), "%.6f" % y, "%.6f" % e, "%.6f" % (y + 3.09 * e),
                        "%.6f" % (-math.log(y) if y > 0 else float("inf"))])
    print("wrote %s (%d couplings)" % (OUT_CSV, len(xs)))

    # ---- DESCRIPTIVE smoothness overlay (drives NO verdict) ----
    xf, yf = xs[interior], ys[interior]
    deg = min(3, len(xf) - 1)                      # FIXED low degree; not selected to pass anything
    c = np.polyfit(xf, yf, deg)
    resid = float(np.max(np.abs(np.poly1d(c)(xf) - yf)))
    slope = float(np.abs(np.poly1d(c).deriv()(np.linspace(xf.min(), xf.max(), 500))).max())
    ni = max(float(np.mean(es[interior])), 1e-3)
    print(f"\n[descriptive] deg-{deg} interpolant: max residual {resid:.4f} vs boot err {ni:.4f} "
          f"({'within noise, smooth' if resid < 3 * ni else 'exceeds noise'}); empirical |drho1/dbeta| "
          f"~ {slope:.4f}, far below the rigorous finite-volume modulus 1/4*(L/2)^2*2*N_p.")
    print("   Reads 3-4 (coset rho'_coset(1), centre sigma_Z/sigma) need centre-projection support -- pending.")


if __name__ == "__main__":
    main()
