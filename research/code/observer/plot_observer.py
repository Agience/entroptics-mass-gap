"""
plot_observer.py -- the figures research/data/obs_fig_*.png, the figures target of research/data/regen_all.py.

Every plotted number is read from a file under research/data/observer/ or copied from a recorded table
(the source is named at each table below). Diagrams (the observer, the bore) are drawn
from the paper's definitions; the one curve inside a diagram, the mode damping (1 - eta*lambda)^n, is the
exact small-field form of the step.

Run from anywhere:  python research/code/observer/plot_observer.py
Writes research/data/obs_fig_<name>.png.
"""
from __future__ import annotations

import json
import os

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.normpath(os.path.join(HERE, "..", "..", "data"))
OBS = os.path.join(DATA, "observer")

# categorical slots in fixed order (default validated palette, light mode)
C1, C2, C3, C4 = "#2a78d6", "#eb6834", "#1baf7a", "#eda100"
INK, MUTED, GRID = "#1f1f1e", "#6b6a63", "#d9d8d2"

plt.rcParams.update({
    "font.size": 9, "axes.edgecolor": MUTED, "axes.labelcolor": INK, "xtick.color": MUTED,
    "ytick.color": MUTED, "axes.grid": True, "grid.color": GRID, "grid.linewidth": 0.6,
    "axes.spines.top": False, "axes.spines.right": False, "legend.frameon": False,
    "lines.linewidth": 2.0, "lines.markersize": 6,
})


def save(fig, name):
    path = os.path.join(DATA, f"obs_fig_{name}.png")
    fig.savefig(path, dpi=160, bbox_inches="tight")
    plt.close(fig)
    print("wrote", path)


def load(name):
    with open(os.path.join(OBS, name)) as f:
        return json.load(f)


# --------------------------------------------------------------------------------------------------
# (a) the observer: one aperture of fixed physical size over three substrates, and the step's damping
# --------------------------------------------------------------------------------------------------
def fig_observer():
    fig = plt.figure(figsize=(10.5, 3.6))
    ell = 1.0                                     # the aperture's radius, physical units
    for i, (a, lab) in enumerate([(0.5, "spacing $a$"), (0.25, "spacing $a/2$"), (0.125, "spacing $a/4$")]):
        ax = fig.add_axes([0.02 + 0.215 * i, 0.08, 0.2, 0.8])
        xs = np.arange(-1.75, 1.75 + 1e-9, a)
        for x in xs:
            ax.plot([x, x], [xs[0], xs[-1]], color=GRID, lw=0.6, zorder=1)
            ax.plot([xs[0], xs[-1]], [x, x], color=GRID, lw=0.6, zorder=1)
        X, Y = np.meshgrid(xs, xs)
        inside = X ** 2 + Y ** 2 <= ell ** 2
        ax.scatter(X[~inside], Y[~inside], s=6, color=MUTED, zorder=2)
        ax.scatter(X[inside], Y[inside], s=8, color=C1, zorder=3)
        ax.add_patch(Circle((0, 0), ell, fill=False, ec=C2, lw=2, zorder=4))
        ax.set_xlim(-1.9, 1.9); ax.set_ylim(-1.9, 1.9); ax.set_aspect("equal"); ax.axis("off")
        ax.set_title(f"substrate at {lab}\n{int(inside.sum())} sites inside the aperture", fontsize=9, color=INK)
        # CHOSEN: the annotation goes on the first panel only (layout)
        if i == 0:
            ax.annotate("aperture of fixed\nphysical radius $\\ell$", xy=(0.0, -1.0), xytext=(0.0, -1.85),
                        fontsize=8, color=C2, ha="center", va="top",
                        arrowprops=dict(arrowstyle="-", color=C2, lw=1))
    ax = fig.add_axes([0.71, 0.18, 0.27, 0.66])
    c = 0.15
    eta = c / (1 + 6 * c)
    lam = np.linspace(0, 16, 400)
    for n, col in [(1, C1), (4, C2), (16, C3)]:
        ax.plot(lam, (1 - eta * lam) ** n, color=col, label=f"$n={n}$")
    ax.set_xlabel("curl-curl eigenvalue $\\lambda$ (short wavelength $\\to$)")
    ax.set_ylabel("mode factor $(1-\\eta\\lambda)^n$")
    ax.set_title("no mode grows: $|1-\\eta\\lambda|\\leq 1$ for $c<1/6$ ($c=0.15$)", fontsize=9, color=INK)
    ax.axhline(0, color=MUTED, lw=0.8); ax.set_ylim(-0.35, 1.05); ax.legend(fontsize=8)
    save(fig, "observer")


# --------------------------------------------------------------------------------------------------
# (b) the energy density's connected correlator at fixed physical separation
# --------------------------------------------------------------------------------------------------
def fig_correlator():
    # the observer's step at its own scale (w ~ 5.4); recorded table (multi-chain test), the paper's section 10 table.
    # Committed source of the beta 2.70 row: obs4_cube_agg_270.json ["correlator"]["at_beta250_times"]
    # (aggregate_obs4_cube.py; it reads 11.34, 9.17, 6.01, 3.66, 2.10 with the same errors).
    # Committed source of the beta 2.50 row: obs4_cube_agg_270.json ["correlator_beta250"]["rows"] (the same
    # script, on obs4_cube/scan_b250_4d_c0.15/ at n = 30, r0/a 6.12): 11.675 +- 0.485, 9.744 +- 0.463,
    # 6.296 +- 0.419, 3.506 +- 0.358, 1.765 +- 0.294; the typed values below agree to the last digit's rounding
    t = np.array([0.0, 0.16, 0.33, 0.49, 0.65])
    g250 = np.array([11.68, 9.74, 6.30, 3.51, 1.77]); e250 = np.array([0.49, 0.46, 0.42, 0.36, 0.29])
    g270 = np.array([11.34, 9.19, 6.05, 3.70, 2.14]); e270 = np.array([0.78, 0.69, 0.60, 0.56, 0.58])
    fig, axs = plt.subplots(1, 2, figsize=(10, 3.8))
    ax = axs[0]
    ax.errorbar(t - 0.006, g250, e250, color=C1, marker="o", capsize=3, label="$\\beta=2.50$, $a\\approx0.165\\,r_0$")
    ax.errorbar(t + 0.006, g270, e270, color=C2, marker="s", capsize=3,
                label="$\\beta=2.70$, $a\\approx0.084\\,r_0$, four chains")
    ax.set_xlabel("$t/r_0$"); ax.set_ylabel("$G(t)\\,r_0^5$")
    ax.set_title("the observer's energy density (its own scale)", fontsize=9, color=INK)
    ax.set_ylim(bottom=0); ax.legend(fontsize=8)
    # the spatial smearing at one physical radius: beta 2.30 and 2.50 from ed_agg_230_250.json
    # (beta 2.50 at both ends of its r0/a range), beta 2.70 recorded table (the paper's section 10 table)
    d = load("ed_agg_230_250.json")
    ax = axs[1]
    A = d["A"]
    # CHOSEN: the plotted range, t/r0 up to 1 (display only; the data are not cut)
    m = np.array(A["t"]) <= 1.0
    ax.errorbar(np.array(A["t"])[m], np.array(A["G"])[m], np.array(A["err"])[m], color=C3, marker="^",
                capsize=3, label="$\\beta=2.30$")
    for key, ls in [("B_lo", "-"), ("B_hi", "--")]:
        B = d[key]
        # CHOSEN: the plotted range, t/r0 up to 1, as above
        tb = np.array(B["t"]); mb = tb <= 1.0
        ax.errorbar(tb[mb], np.array(B["G"])[mb], np.array(B["err"])[mb], color=C1, marker="o", ls=ls,
                    capsize=3, label=f"$\\beta=2.50$, $r_0/a={B['r0a']}$")
    t70 = np.array([0.0, 0.32, 0.64])
    lo70 = np.array([5.22, 1.19, 0.28]); hi70 = np.array([6.47, 1.39, 0.34]); er70 = np.array([0.2, 0.17, 0.16])
    for j in range(3):
        ax.plot([t70[j] + 0.02] * 2, [lo70[j] - er70[j], hi70[j] + er70[j]], color=C2, lw=6, alpha=0.35,
                # CHOSEN: one legend entry, on the first bar (layout)
                solid_capstyle="butt", label="$\\beta=2.70$ (range over $r_0/a$, $\\pm$ error)" if j == 0 else None)
    ax.set_yscale("log"); ax.set_ylim(0.05, 10)
    ax.set_xlabel("$t/r_0$"); ax.set_ylabel("$G(t)\\,r_0^5$")
    ax.set_title("spatially smeared energy density, three spacings", fontsize=9, color=INK)
    ax.legend(fontsize=7.5)
    save(fig, "correlator")


# --------------------------------------------------------------------------------------------------
# (c) the cube-energy moments per p on the in-window step
# --------------------------------------------------------------------------------------------------
def fig_cube_moments():
    cm = load("cube_moments.json")
    b250 = [r for r in cm if r["dir"].endswith("su2_L32_b2.50")][0]
    p = np.array(b250["p"])
    m250 = np.array(b250["moment"]); e250 = np.array(b250["moment_err"])
    # four independent beta 2.70 chains, cube side 11, n = 105: recorded table.
    # Committed source:
    # obs4_cube_agg_270.json ["cube_first5"] (aggregate_obs4_cube.py, first five measurements per chain);
    # all ten committed measurements are its ["cube"] entry (roots 0.896 to 0.952, the paper's section 10)
    m270 = np.array([52.0, 5.73e3, 1.39e6, 5.53e8, 2.84e11, 1.68e14])
    e270 = np.array([0.8, 0.14e3, 0.04e6, 0.13e8, 0.13e11, 0.15e14])
    r250 = m250 ** (1 / (2 * p)); r270 = m270 ** (1 / (2 * p))
    # error of a root from the moment's error: d(m^(1/2p)) = m^(1/2p) * dm / (2p m)
    s250 = r250 * e250 / (2 * p * m250); s270 = r270 * e270 / (2 * p * m270)
    ratio = r270 / r250
    sratio = ratio * np.sqrt((s250 / r250) ** 2 + (s270 / r270) ** 2)
    fig, axs = plt.subplots(1, 2, figsize=(10, 3.6))
    ax = axs[0]
    ax.errorbar(p - 0.05, r250, s250, color=C1, marker="o", capsize=3, label="$\\beta=2.50$ (6-site cubes)")
    ax.errorbar(p + 0.05, r270, s270, color=C2, marker="s", capsize=3, label="$\\beta=2.70$ (11-site cubes, four chains)")
    ax.set_xlabel("$p$"); ax.set_ylabel("$\\langle\\mathcal{E}^{2p}\\rangle^{1/(2p)}$")
    ax.set_title("cube energy on cubes of side about $r_0$", fontsize=9, color=INK)
    ax.legend(fontsize=8)
    ax = axs[1]
    ax.axhline(1, color=MUTED, ls="--", lw=1)
    ax.errorbar(p, ratio, sratio, color=C1, marker="o", capsize=3)
    for pi, ri in zip(p, ratio):
        ax.annotate(f"{ri:.3f}", (pi, ri), textcoords="offset points", xytext=(0, 8), ha="center", fontsize=7.5,
                    color=INK)
    ax.set_xlabel("$p$"); ax.set_ylabel("root, $\\beta=2.70$ over $\\beta=2.50$")
    ax.set_title("every moment falls on the step (root $<1$)", fontsize=9, color=INK)
    ax.set_ylim(0.85, 1.03)
    save(fig, "cube_moments")


# --------------------------------------------------------------------------------------------------
# (d) the coarse block view's total-variation influence row against the coarse spacing
# --------------------------------------------------------------------------------------------------
def fig_influence():
    s1 = load("influence_summary.json")["rows"]
    s2 = load("influence_summary2.json")["rows"]

    # CHOSEN: c=0.15, the observer step coefficient the influence campaigns ran at (below the 1/6 bound)
    def rows(summary, beta, L, c=0.15):
        out = []
        for r in summary:
            if r["beta"] == beta and r["L"] == L and r["c"] == c and r["a_over_r0"]:
                out.append((float(np.mean(r["a_over_r0"])), r["row18_tv"], r["row18_tv_err"], r["k"]))
        return out

    fig, ax = plt.subplots(figsize=(6.6, 4.0))
    ax.axhline(1, color=MUTED, ls="--", lw=1)
    ax.text(0.09, 1.07, "Dobrushin's condition: row $<1$", fontsize=8, color=MUTED)
    # beta 2.30: 32^4 levels k = 0..2, the resolved k = 3 row (all 256 block origins; INFLUENCE-READ.md 6,
    # the paper's 7.8 table), 64^4 level k = 4
    # CHOSEN: the 32^4 levels k <= 2 from the summary; k = 3 is the recorded all-origin row appended next, in
    # place of the summary's 32^4 k = 3 entry. This picks which reading of k = 3 is plotted
    r230 = [x for x in rows(s1, 2.3, 32) if x[3] <= 2]
    r230.append((2.5649246553382494, 0.899, 0.013, 3))
    # DERIVED: level 4 comes from 64^4, since factor-2 blocking leaves a 32^4 lattice 2 coarse sites a side there
    r230 += [x for x in rows(s1, 2.3, 64) if x[3] == 4]
    r230.sort()
    ax.errorbar([x[0] for x in r230], [x[1] for x in r230], [x[2] for x in r230], color=C1, marker="o",
                capsize=3, label="$\\beta=2.30$")
    # CHOSEN: beta 2.50 plots the 32^4 levels k <= 3 and the 64^4 level 4 (2 coarse sites a side at k = 4 on 32^4)
    r250 =[x for x in rows(s1, 2.5, 32) if x[3] <= 3] + [x for x in rows(s2, 2.5, 64) if x[3] == 4]
    r250.sort()
    ax.errorbar([x[0] * 1.03 for x in r250], [x[1] for x in r250], [x[2] for x in r250], color=C2, marker="s",
                capsize=3, label="$\\beta=2.50$")
    r270 = sorted(rows(s1, 2.7, 64))
    ax.errorbar([x[0] * 0.97 for x in r270], [x[1] for x in r270], [x[2] for x in r270], color=C3, marker="^",
                capsize=3, label="$\\beta=2.70$")
    ax.annotate("$0.899\\pm0.013$\nat $2.56\\,r_0$", (2.565, 0.899), xytext=(1.1, 0.35), fontsize=8, color=INK,
                arrowprops=dict(arrowstyle="-", color=MUTED, lw=0.8))
    ax.set_xscale("log"); ax.set_yscale("log")
    ax.set_xlabel("coarse spacing (block size times $a$), units of $r_0$")
    ax.set_ylabel("total-variation influence row")
    ax.set_title("the coarse view's influence row falls with the coarse spacing", fontsize=9, color=INK)
    ax.set_ylim(0.25, 20); ax.legend(fontsize=8, loc="upper right")
    save(fig, "influence_row")


# --------------------------------------------------------------------------------------------------
# (e) one observer step: the global action ratio, and the dispersal of an isolated pixel
# --------------------------------------------------------------------------------------------------
def fig_step():
    # S(VU)/S(U), 6^4, two seeds per entry: recorded table (LD-AGENT-FINDINGS.md; the paper's 7.7 table)
    cs = np.array([0.05, 0.10, 0.15, 0.1666])
    haar = [0.852, 0.721, 0.621, 0.597]
    near01 = [0.456, 0.233, 0.137, 0.120]
    near10 = [0.855, 0.727, 0.630, 0.606]
    # pixel dispersal, flat 12^4 field, c = 0.15: recorded table (UV-B-FINDINGS.md; the paper's 7.7 table)
    n = np.array([8, 16, 32, 64])
    pix = {0.5: [5.6e-4, 6.9e-5, 8.6e-6, 8.6e-7], 3.0: [1.1e-2, 1.0e-3, 1.1e-4, 1.1e-5],
           3.1: [1.4e-2, 1.1e-3, 1.2e-4, 1.1e-5]}
    fig, axs = plt.subplots(1, 2, figsize=(10, 3.7))
    ax = axs[0]
    ax.axhline(1, color=MUTED, ls="--", lw=1)
    ax.plot(cs, haar, color=C1, marker="o", label="Haar start")
    ax.plot(cs, near10, color=C2, marker="s", label="near identity, $\\varepsilon=1.0$")
    ax.plot(cs, near01, color=C3, marker="^", label="near identity, $\\varepsilon=0.1$")
    ax.set_xlabel("step constant $c$ ($<1/6$)"); ax.set_ylabel("$S(VU)/S(U)$")
    ax.set_title("one step lowers the global action", fontsize=9, color=INK)
    ax.set_ylim(0, 1.08); ax.legend(fontsize=8, loc="lower left")
    ax = axs[1]
    for (th, ys), col, mk in zip(pix.items(), [C1, C2, C3], ["o", "s", "^"]):
        ax.plot(n, ys, color=col, marker=mk, label=f"$\\vartheta={th}$")
    ref = 1.1e-3 * (n / 16.0) ** -3
    ax.plot(n, ref, color=MUTED, ls=":", lw=1.5, label="$n^{-3}$ (linear rate)")
    ax.set_xscale("log", base=2); ax.set_yscale("log")
    ax.set_xlabel("smearing steps $n$"); ax.set_ylabel("total action of the smoothed pixel")
    ax.set_title("an isolated pixel disperses", fontsize=9, color=INK)
    ax.legend(fontsize=8)
    save(fig, "step")


# --------------------------------------------------------------------------------------------------
# the bore: confined flux against a free (Coulomb) spread -- a schematic
# --------------------------------------------------------------------------------------------------
def fig_bore():
    fig, axs = plt.subplots(1, 2, figsize=(10, 3.0))
    for ax in axs:
        ax.set_xlim(-3, 3); ax.set_ylim(-1.6, 1.6); ax.set_aspect("equal"); ax.axis("off")
    ax = axs[0]
    for th in np.linspace(-np.pi * 0.95, np.pi * 0.95, 15):
        s = np.linspace(0, 1, 200)
        # field lines of a dipole, drawn as arcs from +q to -q
        h = np.tan(th / 2) * 1.6
        x = -1.5 + 3 * s; y = h * 4 * s * (1 - s)
        ax.plot(x, y, color=C1, lw=1)
    ax.scatter([-1.5, 1.5], [0, 0], s=60, color=[C2, C2], zorder=5)
    ax.set_title("a free field spreads into the bulk: no bore, no gap", fontsize=9, color=INK)
    ax = axs[1]
    w = 0.28
    for yy in np.linspace(-w, w, 7):
        s = np.linspace(0, 1, 200)
        x = -1.5 + 3 * s
        y = yy * np.sqrt(np.clip(np.minimum(s, 1 - s) / 0.08, 0, 1))
        ax.plot(x, y, color=C1, lw=1)
    ax.scatter([-1.5, 1.5], [0, 0], s=60, color=[C2, C2], zorder=5)
    ax.annotate("", xy=(0.0, w + 0.02), xytext=(0.0, w + 0.7),
                arrowprops=dict(arrowstyle="->", color=INK, lw=1))
    ax.annotate("", xy=(0.0, -w - 0.02), xytext=(0.0, -w - 0.7),
                arrowprops=dict(arrowstyle="->", color=INK, lw=1))
    ax.text(0.12, w + 0.45, "width $\\sim 1/\\sqrt{\\sigma}$", fontsize=8.5, color=INK)
    ax.text(-0.9, -1.35, "energy per length $\\sigma$; lightest closed loop $\\Delta\\propto\\sqrt{\\sigma}$",
            fontsize=8.5, color=INK)
    ax.set_title("a self-interacting flux is constricted to a bore", fontsize=9, color=INK)
    save(fig, "bore")


if __name__ == "__main__":
    fig_observer()
    fig_correlator()
    fig_cube_moments()
    fig_influence()
    fig_step()
    fig_bore()
