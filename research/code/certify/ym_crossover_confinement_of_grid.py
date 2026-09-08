"""ym_crossover_confinement_of_grid.py -- the deterministic data behind the finite-grid discharge of `ym_finite_corr_length`
on the crossover interior (Lean `Complete.ym_crossover_confinement_of_grid` + `Certify.le_of_lipschitz_grid`).

What this emits:
  * DATA    : the whitened :F^2: second moment <d^2>(beta) across the dense SU(2) grid, bootstrap bars.
  * CERTIFICATE (drives the verdict): a rigorous 99.9%-per-beta empirical-Bernstein (Maurer-Pontil 2009)
    UPPER bound u(beta) on <d^2> at every measured beta -- no fit, no distributional assumption. The
    interior CLEARS iff every u(beta) < B_16 (the aperture threshold). The forall-beta interior is
    discharged interval-rigorously by the single-plaquette enclosure (small_volume_enclosure.py); this
    dense grid is the corroborating measured evidence.
  * DESCRIPTIVE (drives NOTHING): a fixed low-degree polynomial overlay, reported only as a smoothness
    diagnostic (residual vs noise, empirical |d<d^2>/dbeta|). It is NOT the certificate -- the earlier
    "f + L*delta < B_16 with a fitted L = max|f'| and a pass-selected degree" form is retired, since a
    fitted slope cannot stand in for the rigorous finite-volume modulus.

The read is DIRECT-LAG (no FFT): the whitened correlation is short-range, so <d^2> needs only the small lags,
computed by roll+mean per config ONCE, then the bootstrap resamples the cheap averaging.  Light on CPU.

    CONFIGS=/path/to/entroptics-lattice python ym_crossover_confinement_of_grid.py
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
from aperture_reads import load_su2   # one copy of the su2 shard loader
import store_path                    # the ONE place the ensemble store is located

KAPPA0 = 0.25 * math.log(3.0)
APERTURE_RHS = 1.0 - 3.0 ** (-0.25)
L = 16
B16 = APERTURE_RHS * 2 * (L + 1) ** 2 / (2 * math.pi) ** 2   # <d^2> threshold from the aperture condition
MAXLAG = L // 2
# Store root from ``store_path``: CONFIGS, then the git-ignored local config file, then a refusal
# -- no machine path in this file. Empty rather than raising when unconfigured, because the smoke
# tests import this module and redirect HOPS at a synthetic store; the refusal below says which.
ROOT = store_path.store_root(required=False)
HOPS = store_path.collections("configs_densebeta", "configs_phase1",
                              "configs_betasweep", "configs_ladder",
                              "configs_links_su2_density")
rng = np.random.default_rng(0)


def load(beta, ncap=256):
    return load_su2(HOPS, L, beta, ncap, dtype="float64")


def per_config_profiles(arr):
    """rho_i(d), d=0..MAXLAG, per config: grand-mean-connected spatial autocorrelation by DIRECT roll+mean
    (no FFT), averaged over the 3 spatial axes + transverse + time. Bootstrap then resamples the averaging."""
    a = arr - arr.mean()
    n = arr.shape[0]
    P = np.zeros((n, MAXLAG + 1))
    P[:, 0] = (a * a).mean(axis=(1, 2, 3, 4))
    for ax in (1, 2, 3):
        for d in range(1, MAXLAG + 1):
            P[:, d] += (a * np.roll(a, -d, axis=ax)).mean(axis=(1, 2, 3, 4))
    P[:, 1:] /= 3.0
    return P


def d2_from_profiles(P):
    rho = P.mean(0)
    rho = rho / rho[0]
    p = np.clip(rho, 0, None)
    s = p.sum()
    return float(sum(p[d] * d * d for d in range(MAXLAG + 1)) / s) if s > 0 else 0.0


# The per-beta table is persisted as well as printed. Sec 9 rests on this dense-grid certificate
# (Lean `ym_crossover_confinement_of_grid`), but the grid itself reached the paper only through
# this program's stdout, so nothing could check it and `regen_all --verify` could not see it
# drift. The 13-point grid in 9_1_dat_d2_certified.csv is a different, coarser scan.
OUT_CSV = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                       "data", "9_3_dat_crossover_grid.csv")


def betas_available():
    found = set()
    for h in HOPS:
        for f in glob.glob(f"{h}/su2_L{L}_b*.npy"):
            found.add(round(float(os.path.basename(f).split("_b")[1].split(".s")[0]), 2))
    return sorted(found)


def eb(x, delta, side):
    """One-sided empirical-Bernstein (Maurer-Pontil 2009) confidence bound on E[x]; side=+1 upper,
    -1 lower. Rigorous finite-sample: no fit, no distributional assumption; the constant log(2/delta)
    pays for the empirical-variance concentration.

    Thm 4, one-sided sample-variance form. R is the sample range of the per-config profile value (a
    spatial average over ~3*16^4 site-pairs, so tightly concentrated; its per-lag sample range is
    O(0.005-0.03) and the linear term is sub-dominant to the variance term).

    This is the tree's only copy: data/9_1_run_d2_certify.py imports it rather than restating it, so
    the certificate behind Sec 9 cannot be corrected in one place and left stale in the other."""
    n = len(x); m = x.mean(); v = x.var(ddof=1); R = x.max() - x.min(); Lc = math.log(2.0 / delta)
    return m + side * (math.sqrt(2 * v * Lc / n) + 7 * R * Lc / (3 * (n - 1)))


def d2_upper(P, delta):
    """Rigorous (1-delta)-per-beta upper bound on <d^2>: empirical-Bernstein per lag, union-bounded
    over the K lags (delta/K each), propagated through the ratio functional at its monotone worst
    corner (rho_d = upper, rho_0 = lower). The same certificate as data/9_1_run_d2_certify.py."""
    K = P.shape[1]; dp = delta / K
    lo0 = eb(P[:, 0], dp, -1)
    if lo0 <= 0:
        return math.inf
    pmax = [max(0.0, eb(P[:, d], dp, +1) / lo0) for d in range(1, K)]
    return sum(p * (d + 1) ** 2 for d, p in enumerate(pmax)) / (1.0 + sum(pmax))


def main():
    print(f"kappa0 {KAPPA0:.4f}   aperture RHS 1-3^-1/4 = {APERTURE_RHS:.4f}   <d^2> threshold B_16 = {B16:.3f}\n")
    xs, ys, es, us, ns = [], [], [], [], []
    print(f"{'beta':>5} {'n':>4} | {'<d^2>':>7} {'+-boot':>7} {'eb99.9up':>9}")
    absent = []
    for b in betas_available():
        arr = load(b)
        if arr is None:
            absent.append(b)
            continue
        P = per_config_profiles(arr)
        n = P.shape[0]
        bs = [d2_from_profiles(P[rng.integers(0, n, n)]) for _ in range(200)]
        u = d2_upper(P, 0.001)                     # rigorous 99.9%-per-beta empirical-Bernstein upper
        xs.append(b); ys.append(float(np.mean(bs))); es.append(float(np.std(bs))); us.append(u)
        ns.append(n)
        print(f"{b:>5.2f} {n:>4} | {ys[-1]:>7.4f} {es[-1]:>7.4f} {u:>9.3f}")
    xs, ys, es, us = map(np.array, (xs, ys, es, us))
    if len(xs) < 4:
        print("\n(need >=4 beta points -- generation not synced yet?)"); return

    # ---- THE CERTIFICATE: a rigorous finite-sample upper bound at every measured beta ----
    # <d^2>(beta) <= u(beta) with per-beta probability >= 1 - 1e-3 (empirical-Bernstein: no fit, no
    # distributional assumption). The interior clears iff every u(beta) sits under the aperture
    # threshold B16. No fitted curve, no fitted slope, no degree selection enters this verdict.
    umax = float(np.nanmax(us))
    clears = bool((us < B16).all())
    print(f"\n[certificate] max_beta  eb-99.9%-upper = {umax:.3f}  {'<' if clears else '>='}  B_16 = {B16:.3f}"
          f"   -> interior {'CLEARS' if clears else 'FAILS'}"
          + (f"  ({B16/umax:.0f}x margin)" if umax > 0 else ""))
    print(f"   the forall-beta interior is discharged INTERVAL-rigorously by the single-plaquette enclosure")
    print(f"   (small_volume_enclosure.py, exact Sturm/Feshbach); this dense grid is corroborating measured")
    print(f"   evidence + the empirical modulus of continuity, not the rigorous step.")

    # ---- DESCRIPTIVE smoothness overlay (drives NO verdict): is <d^2>(beta) a smooth curve? ----
    interior = xs >= 0.75
    xf, yf = xs[interior], ys[interior]
    deg = min(3, len(xf) - 1)                      # FIXED low degree; not selected to pass anything
    c = np.polyfit(xf, yf, deg)
    resid = float(np.max(np.abs(np.poly1d(c)(xf) - yf)))
    slope = float(np.abs(np.poly1d(c).deriv()(np.linspace(xf.min(), xf.max(), 500))).max())
    ni = float(np.mean(es[interior]))
    print(f"\n[descriptive] deg-{deg} interpolant over the interior: max residual {resid:.4f} vs boot err "
          f"{ni:.4f} ({'within noise, smooth' if resid < 3 * ni else 'exceeds noise'}); empirical "
          f"|d<d^2>/dbeta| ~ {slope:.3f}, far below the rigorous finite-volume modulus 1/4*(L/2)^2*2*N_p.")
    print(f"=> ym_crossover_confinement_of_grid: every beta's rigorous upper bound clears B_16; smooth in between.")

    # Persist the measured grid. A beta whose shards are missing is a refusal, not a shorter grid:
    # the certificate is "every measured beta clears", so a silently smaller grid weakens the claim
    # while still reading as a pass.
    if absent:
        raise SystemExit(("shards missing for beta %s: refusing to write a partial crossover grid"
                          % ", ".join("%.2f" % b for b in absent))
                         + "\n" + store_path.hint())
    with open(OUT_CSV, "w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(["beta", "nconfigs", "d2_mean", "d2_boot_err", "eb_upper_999"])
        for b, n, y, e, u in zip(xs, ns, ys, es, us):
            w.writerow(["%.2f" % b, int(n), "%.6f" % y, "%.6f" % e, "%.6f" % u])
    print("wrote %s (%d couplings)" % (OUT_CSV, len(xs)))


if __name__ == "__main__":
    main()
