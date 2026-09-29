"""
9_1 (certify) -- finite-sample empirical-Bernstein certificate for the interior read (PAPER Sec 9),
at NOMINAL confidence.

Where 9_1_run_d2_bound.py reports the MEASURED <d^2>(beta) with a bootstrap band (field-standard), this
companion produces a probability bound: an empirical-Bernstein (Maurer-Pontil 2009) one-sided upper
confidence bound on each lag of the profile, union-bounded over the 9 lags (delta' = delta/9), propagated
EXACTLY through the read functional: `CG.d2_upper` returns the read's maximum over the box those
bounds license, 0 <= rho_d/rho_0 <= hi_d/lo_0. That maximum is the all-upper corner while the
corner's value is at most 1, and above 1 a vertex with the short lags at 0 (the proof is in
`CG.ratio_box_max`). The confidence is nominal: Thm 4 needs i.i.d. samples and an a-priori support
width, and `CG.eb` plugs in the sample range, so the guarantee does not strictly apply.

The moment route closes the gap for ANY B under the aperture ceiling

    B < arccos(3^{-1/4})^2 (N+1)^2 / (2 pi)^2,

which on a periodic extent of L=16 sites -- lag arity N+1 = L, so N = 15 -- is 3.2480 (rounded down from 3.24805...; `CG.B16`, from
`aperture_ceiling.d2_ceiling`). This reports the upper against THAT ceiling, unrounded, imported
here rather than restated.

NO PROOF BOUND IS PINNED. A bound pinned under the ceiling was retired with the ceiling that
justified it, and the confinement claim no longer passes through any B at all: the
companion `ym_confinement_of_cos_average` certifies the read's cosine average directly, which is
EQUIVALENT to mu < kappa0 (`Complete.confinement_at_iff_cosAvg`) rather than sufficient for it. This
script's remaining job is the substrate quantity itself, reported against its derived ceiling.

WRITTEN PRECISION. Every UPPER bound in the csv is written rounded UP at its written precision
(`CG.bound_str`), never to nearest: a written upper is what a reader compares against the ceiling,
and rounding it down would move it toward the claim "upper < ceiling". A lower bound would be
written rounded down; this table writes none. The central value is not a bound and is written to
nearest, unchanged.
  DERIVED: the rounding DIRECTION, from the side of each bound -- away from the claim it supports.
  CHOSEN: 4 decimals for the uppers, 5 for the central value -- display precision only; every
  verdict (the `under_ceiling` column, the printed summary) is computed on the unrounded value.

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
import su2_l16_scan                            # the ONE place this scan's population is named
import ym_crossover_confinement_of_grid as CG

# The store root, from `store_path`: `CONFIGS`, then the git-ignored local config file, then a
# refusal. This was a HARDCODED path with no override, and the store has since moved -- so every
# load returned None, the sweep skipped every beta, and this script wrote a HEADER-only csv over
# the committed artifact and exited 0. Then it was a hardcoded path WITH an override, which is
# the same bug for anyone who did not set the override. An empty read is a refusal now (below),
# and with nothing configured HOPS is empty so that refusal is what fires.
BASE = store_path.store_root(required=False)
# The population is `su2_l16_scan`'s, shared with `9_1_run_d2_bound.py`. It must be: the certified
# upper bound is a statement ABOUT that script's central value, so two lists would certify one
# number and plot another -- which is exactly what happened before they were joined.
HOPS = su2_l16_scan.collections()
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
# DERIVED, and imported rather than restated: `CG.B16` is `aperture_ceiling.d2_ceiling(L)` =
# arccos(3^{-1/4})^2 (N+1)^2 / (2 pi)^2 with N+1 the LAG ARITY = the periodic extent L -- one copy,
# so the file carrying the value and the file deriving it cannot disagree.
CEIL = CG.B16
# CHOSEN: 4 decimals of display precision for the ceiling wherever it is WRITTEN (the csv heading,
# the figure label), rounded DOWN -- away from the claim "upper < ceiling" -- so a written upper
# under the written ceiling is under the ceiling. Every comparison uses the unrounded CEIL.
CEIL_SHOWN = math.floor(CEIL * 10 ** 4) / 10 ** 4
BCYM = 0.767


load_beta = su2_l16_scan.load_beta


# The empirical-Bernstein certificate lives in ym_crossover_confinement_of_grid (imported above as
# CG), which this script already uses for per_config_profiles and d2_from_profiles. One copy, so a
# correction to it reaches Sec 9 too. It is an empirical-Bernstein bound at nominal confidence;
# `CG.eb` states why the guarantee is nominal.
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
                "eb_upper_99.9999", f"under_ceiling_{CEIL_SHOWN:.4f}",
                f"ceiling_upper_delta_{DELTA_CEIL:.0e}"])
    # DERIVED: every upper is rounded UP (`CG.bound_str`, side +1); the central value is not a bound
    # and stays to nearest. CHOSEN: 4 decimals, display only -- the verdict uses the unrounded u6.
    up = lambda u: CG.bound_str(u, 4, +1)
    for b, n, c, u9, u99, u6, u30 in zip(B, N, C, U99, U999, U6, U30):
        w.writerow([f"{b:.2f}", n, f"{c:.5f}", up(u9), up(u99), up(u6),
                    "yes" if u6 < CEIL else "NO", up(u30)])

allpass = bool((U6 < CEIL).all())
print("aperture ceiling (DERIVED, lag arity N+1 = L = %d) = %.4f" % (CG.L, CEIL))
print("max certified upper = %.4f at delta=%.0e" % (U6.max(), DELTA))
print("ALL %d beta certified under the ceiling at %.4f%% per beta: %s   joint over grid ~ %.6f" %
      (len(B), 100 * (1 - DELTA), allpass, (1 - DELTA) ** len(B)))
print("max upper at delta=%.0e = %.4f at beta=%.2f  (under the ceiling: %s)"
      % (DELTA_CEIL, U30.max(), B[int(U30.argmax())], bool((U30 < CEIL).all())))

# ---- figure (log-y: measured, nominal-confidence uppers, aperture ceiling all visible) ----
plt.rcParams.update({"font.size": 11, "font.family": "DejaVu Sans", "axes.linewidth": 0.8})
fig, ax = plt.subplots(figsize=(7.6, 4.8))
ACC, DATA, BND, MUT = "#2b6cb0", "#1a202c", "#c53030", "#718096"
ax.set_yscale("log")
# Every coupling's upper is drawn; none is dropped. A finite upper at or above the ceiling is drawn
# in the ceiling's colour, and a coupling with NO finite upper (`CG.d2_upper` returns inf when the
# lower bound on rho(0) is not positive) is marked at the top edge. matplotlib silently skips a
# non-finite point on a log axis, so a missing upper is only visible through that explicit marker.
FIN = np.isfinite(U6)
OVER = FIN & (U6 >= CEIL)
UNDER = FIN & ~OVER
# CHOSEN: display range only, no verdict -- the top edge is 5.5 (room for the ceiling band and its
# label), raised to 1.15x the largest finite upper when that is higher, so no point is clipped.
YTOP = max(5.5, 1.15 * float(U6[FIN].max())) if FIN.any() else 5.5
ax.axhspan(CEIL, YTOP * 1.1, color=BND, alpha=0.06, zorder=0)
ax.axhline(CEIL, color=MUT, lw=1.3, ls=":", zorder=2)
ax.text(2.68, CEIL * 1.04, rf"aperture ceiling ${CEIL_SHOWN:.4f}$ (any $B$ below closes the gap)",
        color=MUT, fontsize=8.8, va="bottom", ha="right")
# measured -> upper span, to the top edge where the upper is not finite
for x, c, u in zip(B, C, U6):
    ax.plot([x, x], [c, u if np.isfinite(u) else YTOP], color=ACC, lw=1.0, alpha=0.5, zorder=1)
CONF = rf"${100 * (1 - DELTA):.4f}\%$"
if UNDER.any():
    ax.scatter(B[UNDER], U6[UNDER], marker="v", s=34, color=ACC, zorder=4,
               label=rf"{CONF} upper, nominal confidence (empirical-Bernstein, sample range as width)")
if OVER.any():
    ax.scatter(B[OVER], U6[OVER], marker="v", s=46, color=BND, zorder=4,
               label=rf"{CONF} upper at or above the ceiling")
if (~FIN).any():
    ax.scatter(B[~FIN], np.full(int((~FIN).sum()), YTOP), marker="^", s=46, color=BND, zorder=4,
               clip_on=False, label=r"no finite upper (lower bound on $\rho(0)$ not positive)")
ax.scatter(B, C, marker="o", s=30, color=DATA, zorder=5, label=r"measured $\langle d^2\rangle(\beta)$ (central)")
ax.set_xlabel(r"coupling  $\beta$")
ax.set_ylabel(r"whitened :F$^2$: second moment  $\langle d^2\rangle$  (log)")
ax.set_ylim(0.004, YTOP); ax.set_xlim(0.4, 2.72)
ax.set_title(rf"SU(2) $L{{=}}16$: measured $\langle d^2\rangle$ and its {CONF} upper "
             r"at nominal confidence",
             fontsize=10.5)
ax.legend(loc="lower right", frameon=False, fontsize=9)
ax.grid(True, which="both", alpha=0.14, lw=0.6)
for s in ("top", "right"):
    ax.spines[s].set_visible(False)
fig.tight_layout()
fig.savefig(os.path.join(HERE, "9_1_fig_d2_certified.png"), dpi=150)
print("wrote 9_1_dat_d2_certified.csv + 9_1_fig_d2_certified.png")
