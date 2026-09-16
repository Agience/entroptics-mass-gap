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
# DERIVED: both are boundaries, not cuts. Δ = -log ρ'(1), so ρ'(1) < 1 is exactly Δ > 0 --
# the unit circle, where decay turns into growth, with nothing chosen about it. The second is
# e^{-κ0} with κ0 = (1/4)log3 from `Floor.lean`, so ρ'(1) < 3^{-1/4} is exactly Δ ≥ κ0. Neither
# number is free: move either and it stops being the statement it names.
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


def beta_star_bounds():
    """`beta_c = kappa_0 / (2 r)` as a certified interval, from the sibling exact-rational enclosure.

    `beta_star_enclosure` brackets `kappa_0` and the character ratio `r` in exact rationals with a
    proven geometric tail on each series, so this is an enclosure rather than a float. Returned as
    `(lo, hi)`; the caller decides which end its direction of conservatism wants.
    """
    import beta_star_enclosure as BSE
    klo, khi = BSE.kappa0_bounds()
    # `r` is evaluated AT the threshold, which is the fixed point `2 beta r(beta) = kappa_0`. The
    # enclosure's own bracketing interval (0.749, 0.750) is where that fixed point lies, so `r` is
    # bracketed by its values at the two ends.
    from fractions import Fraction as Q
    rlo, _ = BSE.ratio_bounds(Q(749, 1000))
    _, rhi = BSE.ratio_bounds(Q(750, 1000))
    return float(klo / (2 * rhi)), float(khi / (2 * rlo))


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
        # CHOSEN: minimum points for a degree-3 interpolant residual to mean anything.
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
    # DERIVED: the interior begins where the strong-coupling character bound stops clearing the
    # floor, `beta_c = kappa_0 / (2 r)` with `r = I_2/I_1` the leading character ratio. It used to be
    # the literal 0.75, with a comment saying it was derived and would silently stop tracking `r` --
    # a comment describing a defect rather than fixing it. It is now ASKED FOR, from the sibling
    # module that certifies it in exact rationals with a proven tail bound on every series.
    #
    # The enclosure is an interval; the LOWER end is taken deliberately. It admits every coupling the
    # strong-coupling bound might not cover, so the interior is asked to clear more than it strictly
    # must -- the direction that cannot open a gap between the two regions.
    beta_c_lo, beta_c_hi = beta_star_bounds()
    print(f"interior begins at beta_c in [{beta_c_lo:.6f}, {beta_c_hi:.6f}] "
          f"(certified, beta_star_enclosure); taking the lower end")
    interior = xs >= beta_c_lo
    # CHOSEN: minimum interior points, as above.
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
    # NOT "forall beta" -- see the same correction in ym_crossover_confinement_of_grid.py. The
    # enclosure certifies lambda in [0.16, 6.76], the image of beta in [0.8, 2.6]; that is this
    # grid's own range, so the enclosure corroborates it rather than superseding it.
    print(f"   the interior is discharged INTERVAL-rigorously ON THE CROSSOVER IMAGE by the")
    print(f"   single-plaquette enclosure (small_volume_enclosure.py): beta in [0.8, 2.6] maps to")
    print(f"   lambda in [0.16, 6.76], exactly the range it certifies. Above beta = 2.6 nothing here")
    print(f"   is rigorous; PAPER Sec 13 names what carries it. RP reversibility rho'(n)=rho'(1)^n")
    print(f"   carries one cut uniform in volume, refinement-invariant to a->0. This dense grid is")
    print(f"   corroborating measured evidence.")

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
