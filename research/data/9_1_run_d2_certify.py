"""
9_1 (certify) -- RIGOROUS finite-sample certificate for the interior read (PAPER Sec 9).

Where 9_1_run_d2_bound.py reports the MEASURED <d^2>(beta) with a bootstrap band (field-standard), this
companion produces a DEDUCTIVE-PROBABILITY bound: an empirical-Bernstein (Maurer-Pontil 2009) one-sided upper
confidence bound on each lag of the profile, union-bounded over the 9 lags (delta' = delta/9), propagated
through the read functional at its monotone worst-case corner (rho_d = hi_d, rho_0 = lo_0).

The moment route closes the gap for ANY B under the aperture ceiling

    B < 2 (1 - 3^{-1/4}) / (2 pi/(N+1))^2,

which on a periodic extent of L=16 sites -- lag arity N+1 = L, so N = 15 -- is 3.11. This reports the
certified upper against THAT ceiling, derived in `ym_crossover_confinement_of_grid` and imported here.

NO PROOF BOUND IS PINNED. A bound pinned under the ceiling was retired with the ceiling that
justified it, and the confinement claim no longer passes through any B at all: the
companion `ym_confinement_of_cos_average` certifies the read's cosine average directly, which is
EQUIVALENT to mu < kappa0 (`Complete.confinement_at_iff_cosAvg`) rather than sufficient for it. This
script's remaining job is the substrate quantity itself, reported against its derived ceiling.

Emits 9_1_dat_d2_certified.csv and 9_1_fig_d2_certified.png.
"""
import os, sys, glob, csv, math
import numpy as np
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "code"))            # research/code -- store_path
sys.path.insert(0, os.path.join(HERE, "..", "code", "certify"))
import store_path                              # the ONE place the ensemble store is located
import ym_crossover_confinement_of_grid as CG

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

# The confidence the certificate is REPORTED at. This is a choice, not a limit of the data: the
# empirical-Bernstein bound enters only through log(2/delta'), so asking for more confidence widens
# the upper rather than invalidating it. The columns span six orders of magnitude in delta so the
# reader can see how the certified quantity degrades as the demand tightens, rather than being shown
# one delta chosen after the fact.
DELTA = 1e-6           # 99.9999% per coupling
# The tightest confidence reported, carried as its own column so the paper's figure for it is read
# from the artifact rather than restated.
DELTA_CEIL = 1e-30
# DERIVED, and imported rather than restated: `CG.B16` is
# (1 - 3^{-1/4}) * 2 (N+1)^2 / (2 pi)^2 with N+1 the LAG ARITY = the periodic extent L. This was a
# literal, so the file carrying the correction and the file carrying the value could disagree.
CEIL = CG.B16
BCYM = 0.767


def load_beta(b):
    fs = []
    for d in HOPS:
        fs += glob.glob(f"{BASE}/{d}/su2_L16_b{b:.2f}.s*.npy")
    return np.concatenate([np.load(f) for f in fs], 0) if fs else None


# The empirical-Bernstein certificate lives in ym_crossover_confinement_of_grid (imported above as
# CG), which this script already uses for per_config_profiles and d2_from_profiles. Both files used
# to carry their own line-for-line identical copy of eb/d2_upper -- the same rigorous bound stated
# twice, so a correction to one would silently leave the other, and Sec 9, behind.
eb, d2_upper = CG.eb, CG.d2_upper


B, N, C, U99, U999, U6, U30 = [], [], [], [], [], [], []
for b in BETAS:
    a = load_beta(b)
    if a is None:
        continue
    P = CG.per_config_profiles(a); n = a.shape[0]
    B.append(b); N.append(n); C.append(CG.d2_from_profiles(P))
    U99.append(d2_upper(P, 0.01)); U999.append(d2_upper(P, 0.001))
    U6.append(d2_upper(P, DELTA)); U30.append(d2_upper(P, DELTA_CEIL))

if not B:
    raise SystemExit(
        f"{__file__}: the sweep matched no configurations under {BASE or '<no store configured>'}. Every row of the"
        f" artifact is read from them, so there is nothing to write. Refusing: writing the"
        f" header alone would overwrite the committed table with an empty one and still exit 0,"
        f" which is how this failure went unnoticed."
        f"\n{store_path.hint()}")

B, C, U99, U999, U6, U30 = map(np.array, (B, C, U99, U999, U6, U30))

# ---- CSV ----
with open(os.path.join(HERE, "9_1_dat_d2_certified.csv"), "w", newline="") as f:
    w = csv.writer(f)
    w.writerow(["beta", "nconfigs", "d2_central", "eb_upper_99", "eb_upper_99.9",
                "eb_upper_99.9999", f"under_ceiling_{CEIL:.2f}",
                f"ceiling_upper_delta_{DELTA_CEIL:.0e}"])
    for b, n, c, u9, u99, u6, u30 in zip(B, N, C, U99, U999, U6, U30):
        w.writerow([f"{b:.2f}", n, f"{c:.5f}", f"{u9:.4f}", f"{u99:.4f}", f"{u6:.4f}",
                    "yes" if u6 < CEIL else "NO", f"{u30:.4f}"])

allpass = bool((U6 < CEIL).all())
print("aperture ceiling (DERIVED, lag arity N+1 = L = %d) = %.4f" % (CG.L, CEIL))
print("max certified upper = %.4f at delta=%.0e" % (U6.max(), DELTA))
print("ALL %d beta certified under the ceiling at %.4f%% per beta: %s   joint over grid ~ %.6f" %
      (len(B), 100 * (1 - DELTA), allpass, (1 - DELTA) ** len(B)))
print("max upper at delta=%.0e = %.4f at beta=%.2f  (under the ceiling: %s)"
      % (DELTA_CEIL, U30.max(), B[int(U30.argmax())], bool((U30 < CEIL).all())))

# ---- figure (log-y: measured, certified caps, proof bound, aperture ceiling all visible) ----
plt.rcParams.update({"font.size": 11, "font.family": "DejaVu Sans", "axes.linewidth": 0.8})
fig, ax = plt.subplots(figsize=(7.6, 4.8))
ACC, DATA, BND, MUT = "#2b6cb0", "#1a202c", "#c53030", "#718096"
ax.set_yscale("log")
ax.axhspan(CEIL, 6, color=BND, alpha=0.06, zorder=0)
ax.axhline(CEIL, color=MUT, lw=1.3, ls=":", zorder=2)
ax.text(2.68, CEIL * 1.04, rf"aperture ceiling ${CEIL:.2f}$ (any $B$ below closes the gap)",
        color=MUT, fontsize=8.8, va="bottom", ha="right")
# measured -> certified span
for x, c, u in zip(B, C, U6):
    ax.plot([x, x], [c, u], color=ACC, lw=1.0, alpha=0.5, zorder=1)
ax.scatter(B, U6, marker="v", s=34, color=ACC, zorder=4,
           label=rf"rigorous ${100 * (1 - DELTA):.4f}\%$ upper (empirical-Bernstein)")
ax.scatter(B, C, marker="o", s=30, color=DATA, zorder=5, label=r"measured $\langle d^2\rangle(\beta)$ (central)")
ax.set_xlabel(r"coupling  $\beta$")
ax.set_ylabel(r"whitened :F$^2$: second moment  $\langle d^2\rangle$  (log)")
ax.set_ylim(0.004, 5.5); ax.set_xlim(0.4, 2.72)
ax.set_title(rf"SU(2) $L{{=}}16$: measured $\langle d^2\rangle$ and its rigorous "
             rf"${100 * (1 - DELTA):.4f}\%$ certificate",
             fontsize=10.5)
ax.legend(loc="lower right", frameon=False, fontsize=9)
ax.grid(True, which="both", alpha=0.14, lw=0.6)
for s in ("top", "right"):
    ax.spines[s].set_visible(False)
fig.tight_layout()
fig.savefig(os.path.join(HERE, "9_1_fig_d2_certified.png"), dpi=150)
print("wrote 9_1_dat_d2_certified.csv + 9_1_fig_d2_certified.png")
