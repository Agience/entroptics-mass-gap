"""9_1_run_d2_su3.py -- the SU(3) analog of 9_1_run_d2_bound.py (SU(2) L16).

Whitened :F^2: second moment <d^2>(beta) = sum_d p_d d^2 (squared correlation length in lattice units)
read on the pure-SU(3) beta-sweep from the store. Same read functional as the SU(2) figure: per-config
grand-mean-connected spatial autocorrelation by DIRECT roll+mean (no FFT), lags d=0..L/2, normalized to
p_d = clip(rho_d/rho_0, 0)/sum, then the second moment. Bootstrap +/-2sigma over configs. Deterministic,
cheap (L=6/8). Emits 9_1_dat_d2_su3.csv and 9_1_fig_d2_su3.png.
"""
import os, sys, glob, csv, math
import numpy as np
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "code"))   # research/code -- store_path
import store_path                                      # the ONE place the store is located

# The store root, from `store_path`: `CONFIGS`, then the git-ignored local config file, then a
# refusal. No default: a literal path names one machine, and everywhere else every load returns
# None. The guard before the CSV write below is what turns that into a refusal rather than an
# empty artifact.
BASE = store_path.store_root(required=False)
HOPS = ["configs_paper83", "configs_phase1"] if BASE else []
APERTURE_RHS = 1.0 - 3.0 ** (-0.25)   # 1 - 3^{-1/4}

# SU(3) L6 has the full sweep 5.0..7.0; L8 has the crossover cluster 5.5..6.0.
SERIES = [(6, [5.00, 5.25, 5.50, 5.75, 6.00, 6.25, 6.50, 6.75, 7.00]),
          (8, [5.50, 5.70, 5.90, 6.00])]


def load(L, b, ncap=128):
    for h in HOPS:
        fs = sorted(glob.glob(f"{BASE}/{h}/su3_L{L}_b{b:.2f}.s*.npy"))
        if fs:
            return np.asarray(np.concatenate([np.load(f) for f in fs], 0)[:ncap], dtype=np.float64)
    return None


def profiles(arr, maxlag):
    a = arr - arr.mean()
    n = arr.shape[0]
    P = np.zeros((n, maxlag + 1))
    P[:, 0] = (a * a).mean(axis=(1, 2, 3, 4))
    for ax in (1, 2, 3):
        for d in range(1, maxlag + 1):
            P[:, d] += (a * np.roll(a, -d, axis=ax)).mean(axis=(1, 2, 3, 4))
    P[:, 1:] /= 3.0
    return P


def d2(P, maxlag):
    rho = P.mean(0)
    rho = rho / rho[0]
    p = np.clip(rho, 0, None)
    s = p.sum()
    return float(sum(p[d] * d * d for d in range(maxlag + 1)) / s) if s > 0 else 0.0


rng = np.random.default_rng(0)
out = {}
for L, betas in SERIES:
    maxlag = L // 2
    ceil = APERTURE_RHS * 2 * (L + 1) ** 2 / (2 * math.pi) ** 2
    rows = []
    for b in betas:
        arr = load(L, b)
        if arr is None:
            continue
        P = profiles(arr, maxlag)
        n = P.shape[0]
        c = d2(P, maxlag)
        boot = [d2(P[rng.integers(0, n, n)], maxlag) for _ in range(400)]
        rows.append((b, c, float(np.std(boot)), n))
        print(f"su3 L{L} b{b:.2f}: <d^2>={c:.4f} +/- {float(np.std(boot)):.4f}  n={n}")
    out[L] = (rows, ceil)
    print(f"  aperture ceiling (L{L}) = {ceil:.3f}")

# Refuse BEFORE writing. Every row is read from the store, so a run that matched nothing has
# nothing to write: the header alone would overwrite the committed table with an empty one and
# still exit 0. That is the failure the sibling 9_1 scripts already refuse on.
if not any(rows for rows, _ in out.values()):
    raise SystemExit(
        f"9_1_run_d2_su3: the SU(3) sweep matched no configurations under {BASE or '<no store configured>'}. Refusing"
        f" to overwrite the committed table with an empty one.\n{store_path.hint()}")

# ---- CSV (both series) ----
with open(os.path.join(HERE, "9_1_dat_d2_su3.csv"), "w", newline="") as f:
    w = csv.writer(f)
    w.writerow(["L", "beta", "d2", "sigma", "nconfigs", "aperture_ceiling"])
    for L, (rows, ceil) in out.items():
        for b, c, s, n in rows:
            w.writerow([L, f"{b:.2f}", f"{c:.5f}", f"{s:.5f}", n, f"{ceil:.4f}"])

# ---- figure ----
plt.rcParams.update({"font.size": 11, "font.family": "DejaVu Sans", "axes.linewidth": 0.8})
fig, ax = plt.subplots(figsize=(7.6, 4.8))
colors = {6: "#1a202c", 8: "#2b6cb0"}
for L, (rows, ceil) in out.items():
    if not rows:
        continue
    B = np.array([r[0] for r in rows]); C = np.array([r[1] for r in rows]); S = np.array([r[2] for r in rows])
    ax.errorbar(B, C, yerr=2 * S, fmt="o", color=colors[L], ms=6, capsize=3, lw=1.2,
                label=rf"$SU(3)$ $L{{=}}{L}$  $\langle d^2\rangle(\beta)$ ($\pm2\sigma$)")
ceil6 = out[6][1]
ax.axhline(ceil6, color="#c53030", ls="--", lw=1.4)
ax.text(6.98, ceil6 * 1.02, rf"aperture ceiling {ceil6:.2f} ($L{{=}}6$)", color="#c53030",
        fontsize=9.5, ha="right", va="bottom")
ax.axvline(5.7, color="#718096", ls=":", lw=1.1)
ax.text(5.73, 0.30, r"bulk crossover $\approx5.7$", color="#718096", fontsize=9, rotation=90,
        va="bottom", ha="left")
ax.set_xlabel(r"coupling  $\beta$")
ax.set_ylabel(r"whitened :F$^2$: second moment  $\langle d^2\rangle$")
ax.set_title(r"$SU(3)$: whitened :F$^2$: second moment across the crossover (the no-bump)", fontsize=11)
ymax = max(ceil6 * 1.15, max(r[1] for L in out for r in out[L][0]) * 1.6)
ax.set_ylim(0, ymax)
ax.legend(loc="upper left", frameon=False, fontsize=9)
ax.grid(True, alpha=0.15, lw=0.6)
for s in ("top", "right"):
    ax.spines[s].set_visible(False)
fig.tight_layout()
fig.savefig(os.path.join(HERE, "9_1_fig_d2_su3.png"), dpi=150)
print("wrote 9_1_dat_d2_su3.csv + 9_1_fig_d2_su3.png")
