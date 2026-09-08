"""
9_1 -- The interior second-moment read <d^2>(beta) vs the finite-xi bound (PAPER Sec 9 / Sec 12).

Reads the whitened :F^2: correlation second moment <d^2>(beta) on the SU(2) L16 dense-beta grid via the
deterministic entroptics DIRECT-LAG read (code/certify/ym_crossover_confinement_of_grid.py -- per_config_profiles /
d2_from_profiles), with a bootstrap error per beta, fits a DESCRIPTIVE quadratic (evidence interpolation,
NOT the proof bound), and plots against the flat proof bound <d^2> <= 1 (`d2_le_bound`).

Emits 9_1_dat_d2_bound.csv and 9_1_fig_d2_bound.png.

Division of labour: the read is EVIDENCE for `d2_le_bound` (a finite correlation length); the flat
constant 1 is the proof's actual bound. The descriptive fit deliberately UNDERSHOOTS the noisy peak (it is a central
estimate) -- which is precisely why a least-squares fit cannot serve as the upper bound, and the flat constant
does. No GPU, no fit in the read itself: <d^2> is an exact function of each configuration.
"""
import os, sys, glob, csv
import numpy as np
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "code"))            # research/code -- store_path
sys.path.insert(0, os.path.join(HERE, "..", "code", "certify"))
import store_path                              # the ONE place the ensemble store is located
import ym_crossover_confinement_of_grid as CG  # canonical direct-lag read

# The store root, from `store_path`: `CONFIGS`, then the git-ignored local config file, then a
# refusal. This was a HARDCODED path with no override, and the store has since moved -- so every
# load returned None, the sweep skipped every beta, and this script wrote a HEADER-only csv over
# the committed artifact and exited 0. Then it was a hardcoded path WITH an override, which is
# the same bug for anyone who did not set the override. An empty read is a refusal now (below),
# and with nothing configured HOPS is empty so that refusal is what fires.
BASE = store_path.store_root(required=False)
HOPS = (["configs_densebeta", "configs_phase1", "configs_betasweep", "configs_ladder"]
        if BASE else [])
BETAS = [0.5, 0.8, 1.0, 1.2, 1.4, 1.6, 1.8, 2.0, 2.2, 2.3, 2.4, 2.5, 2.6]
NCAP, NBOOT, BOUND, BCYM = 256, 500, 1.0, 0.767   # BOUND = 1 (d2_le_bound); BCYM ~= beta_star
rng = np.random.default_rng(20260709)


def load_beta(b):
    fs = []
    for d in HOPS:
        fs += glob.glob(f"{BASE}/{d}/su2_L16_b{b:.2f}.s*.npy")
    return np.concatenate([np.load(f) for f in fs], 0)[:NCAP] if fs else None


B, M, S, N = [], [], [], []
for b in BETAS:
    a = load_beta(b)
    if a is None:
        continue
    P = CG.per_config_profiles(a)
    n = a.shape[0]
    boot = np.array([CG.d2_from_profiles(P[rng.integers(0, n, n)]) for _ in range(NBOOT)])
    B.append(b); M.append(CG.d2_from_profiles(P)); S.append(float(boot.std())); N.append(n)

if not B:
    raise SystemExit(
        f"{__file__}: the sweep matched no configurations under {BASE or '<no store configured>'}. Every row of the"
        f" artifact is read from them, so there is nothing to write. Refusing: writing the"
        f" header alone would overwrite the committed table with an empty one and still exit 0,"
        f" which is how this failure went unnoticed."
        f"\n{store_path.hint()}")

B, M, S = np.array(B), np.array(M), np.array(S)

# ---- CSV ----
with open(os.path.join(HERE, "9_1_dat_d2_bound.csv"), "w", newline="") as f:
    w = csv.writer(f)
    w.writerow(["beta", "d2", "sigma", "nconfigs"])
    for b, m, s, n in zip(B, M, S, N):
        w.writerow([f"{b:.2f}", f"{m:.5f}", f"{s:.5f}", n])

# ---- descriptive (evidence) fit + 95% band ----
wt = 1.0 / np.maximum(S, 1e-3) ** 2
xx = np.linspace(B.min(), B.max(), 300)
fit = np.poly1d(np.polyfit(B, M, 2, w=np.sqrt(wt)))
fb = []
for _ in range(1000):
    i = rng.integers(0, len(B), len(B))
    try:
        fb.append(np.poly1d(np.polyfit(B[i], M[i], 2, w=np.sqrt(wt[i])))(xx))
    except Exception:
        pass
lo, hi = np.percentile(np.array(fb), [2.5, 97.5], 0)
peak = M.max(); pk_b = B[np.argmax(M)]

# ---- figure (measured crossover shape; the bound/certificate live in 9_1_fig_d2_certified.png) ----
plt.rcParams.update({"font.size": 11, "font.family": "DejaVu Sans", "axes.linewidth": 0.8})
fig, ax = plt.subplots(figsize=(7.4, 4.7))
ACC, DATA, MUT = "#2b6cb0", "#1a202c", "#718096"
ax.axvspan(0.4, BCYM, color=MUT, alpha=0.06, zorder=0)
ax.text(0.585, 0.12, r"$\beta<\beta_\star$:" "\n" r"character bound", color=MUT, fontsize=8.2, va="center", ha="center")
ax.fill_between(xx, lo, hi, color=ACC, alpha=0.16, zorder=1, label=r"descriptive fit $\pm$95%")
ax.plot(xx, fit(xx), color=ACC, lw=1.8, zorder=3)
ax.errorbar(B, M, yerr=2 * S, fmt="o", ms=5, color=DATA, ecolor=DATA, elinewidth=1.1, capsize=2.5,
            zorder=4, label=r"entroptics read $\langle d^2\rangle(\beta)$  ($\pm2\sigma$)")
ax.annotate(f"peak {peak:.3f}", xy=(pk_b, peak), xytext=(2.1, 0.216), fontsize=9, color=DATA,
            ha="center", arrowprops=dict(arrowstyle="->", color=DATA, lw=0.8))
ax.text(1.2, 0.15, "measured $\\langle d^2\\rangle \\leq %.2f$ across the crossover;\n"
                   "rigorously certified $\\leq %.1f$ at 99.9%% (companion figure)" % (peak, BOUND),
        fontsize=8.6, color=MUT, style="italic", ha="center", va="center")
ax.set_xlabel(r"coupling  $\beta$")
ax.set_ylabel(r"whitened :F$^2$: second moment  $\langle d^2\rangle$")
ax.set_ylim(0, 0.235); ax.set_xlim(0.4, 2.7)
ax.set_title(r"SU(2) $L{=}16$: measured whitened :F$^2$: second moment across the crossover", fontsize=11)
ax.legend(loc="upper left", frameon=False, fontsize=9.5)
ax.grid(True, alpha=0.16, lw=0.6)
for s in ("top", "right"):
    ax.spines[s].set_visible(False)
fig.tight_layout()
fig.savefig(os.path.join(HERE, "9_1_fig_d2_bound.png"), dpi=150)
print("wrote 9_1_dat_d2_bound.csv + 9_1_fig_d2_bound.png; peak=%.3f n=%s" % (peak, list(N)))
