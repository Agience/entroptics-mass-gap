"""Figures of the paper, from closed forms only.

Run from anywhere: ``python research/paper/figures/make_figures.py``. Writes PDF and PNG files next to this script.
No network, no data files: every curve is a closed form transcribed from the Lean definitions named beside it.

Couplings are the Lean convention ``beta = beta_W / 2`` (in-plane) and ``t = t_W / 2`` (mixed), section 1.7 (the convention of the formal statements).

Closed forms (all logarithms natural), checked against the Lean definitions:

- ``ell = 240 + 150 (N + 4) beta``                       StripGap.gapArea
- ``K = ceil(2 sqrt(2 N (beta + 1))) + 1``               StripGap.binCount
- ``L = 1 + 2 N^2 log K``                                StripWidth.bulkExp
- ``A_glue = 2 + 2 ell (2 L + 2 log ell + 26)``          StripWiden.glueArea, StripGapThm.areaG
- ``n0 = 2 + 2 ell (2 L + 41 + 6 log ell)``              StripWidth.seedSide
- ``w0 = ceil(log_4 A_glue)``                            StripGapThm.seedWindow
- ``t_low = e^{-4 beta} / (16192 (16 beta + 27))``       StripWidth.tLow   (strict: t < t_low, StripWidth.strip_width)
- ``t_poly = 1 / (16192 n0^2)``                          StripWidth.tPoly  (t <= t_poly)
- ``t_glue = 1 / (16192 A_glue)``                        StripWiden.tGlue  (t <= t_glue; gap StripGapThm.strip_gap)
- ``t_lift = 1 / (4048 4^{w0})``                         StripLift.tLift   (t <= t_lift; gap StripLift.lift_gap)
- ``t_quart = 1 / (524288 2^{w0})``                      CumulantStrip.tQuart (t <= t_quart; gap CumulantStrip.gap_quartic)
- ``t0 = 1/131072 = 2^{-17}``                            CumulantStrip.DA_le_quartic hypothesis
- ``t1 = e^{-88}/16``, ``t2 = e^{-128}/16``              StripGas.tOne, StripOsc.tTwo
- diagonal segment ``beta <= 1/500000``                  StripWidth.diag_small
- bootstrap ``D <= 1/1000 => D' <= 250 D^2``             DoublingSharp.rec_sharp
"""

from __future__ import annotations

import math
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch, Patch  # noqa: E402
from matplotlib.lines import Line2D  # noqa: E402

OUT = Path(__file__).resolve().parent

# ---------------------------------------------------------------- style

INK = "#0b0b0b"
INK2 = "#52514e"
MUTED = "#898781"
GRID = "#e1e0d9"
AXIS = "#c3c2b7"
BLUE = "#2a78d6"
BLUE_DARK = "#184f95"
BLUE_FILL = "#cde2fb"
BLUE_HATCH = "#6da7ec"
ORANGE = "#eb6834"
AQUA = "#1baf7a"
YELLOW = "#c98500"
VIOLET = "#6250d6"
OPEN_FILL = "#f6f5f2"

plt.rcParams.update(
    {
        "font.family": "STIXGeneral",
        "mathtext.fontset": "stix",
        "font.size": 9,
        "axes.labelsize": 9.5,
        "axes.titlesize": 10,
        "legend.fontsize": 8,
        "xtick.labelsize": 8.5,
        "ytick.labelsize": 8.5,
        "axes.edgecolor": AXIS,
        "axes.labelcolor": INK,
        "xtick.color": INK2,
        "ytick.color": INK2,
        "axes.linewidth": 0.8,
        "lines.linewidth": 1.5,
        "legend.frameon": False,
        "savefig.dpi": 200,
        "pdf.fonttype": 42,
        "hatch.linewidth": 0.6,
    }
)


def save(fig, name: str) -> None:
    for ext in ("pdf", "png"):
        fig.savefig(OUT / f"{name}.{ext}", bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)


# ---------------------------------------------------------------- closed forms


def ell(N, b):
    return 240.0 + 150.0 * (N + 4) * b


def binK(N, b):
    return np.ceil(2.0 * np.sqrt(2.0 * N * (b + 1.0))) + 1.0


def bulkL(N, b):
    return 1.0 + 2.0 * N * N * np.log(binK(N, b))


def a_glue(N, b):
    l = ell(N, b)
    return 2.0 + 2.0 * l * (2.0 * bulkL(N, b) + 2.0 * np.log(l) + 26.0)


def n0(N, b):
    l = ell(N, b)
    return 2.0 + 2.0 * l * (2.0 * bulkL(N, b) + 41.0 + 6.0 * np.log(l))


def w0(N, b):
    A = np.atleast_1d(a_glue(N, b)).astype(float)
    w = np.ceil(np.log(A) / np.log(4.0)).astype(int)
    # guard the ceiling at exact powers of 4: need 4^(w-1) < A <= 4^w
    w = np.where(4.0 ** w < A, w + 1, w)
    w = np.where(4.0 ** (w - 1) >= A, w - 1, w)
    return w if np.ndim(b) else int(w[0])


def t_low(b):
    return np.exp(-4.0 * b) / (16192.0 * (16.0 * b + 27.0))


def t_poly(N, b):
    return 1.0 / (16192.0 * n0(N, b) ** 2)


def t_glue(N, b):
    return 1.0 / (16192.0 * a_glue(N, b))


def t_lift(N, b):
    return 1.0 / (4048.0 * 4.0 ** w0(N, b))


def t_quart(N, b):
    return 1.0 / (524288.0 * 2.0 ** w0(N, b))


T0 = 2.0 ** -17
T1 = math.exp(-88) / 16
T2 = math.exp(-128) / 16
DIAG_SMALL = 1.0 / 500000


def check_reference_values() -> None:
    """Reference values of the coupling-plane and strip-width figures, N = 2."""

    # DERIVED: 5e-3 is half a unit in the third significant figure, the precision the
    # reference values below are quoted to.
    def close(x, y, rel=5e-3):
        assert abs(x - y) <= rel * abs(y), (x, y)

    # DERIVED: 9 and 13 are the starting windows w0 at beta = 1 and 100, from the closed forms.
    assert w0(2, 1.0) == 9 and w0(2, 100.0) == 13
    close(t_glue(2, 1.0), 3.70e-10)
    close(t_lift(2, 1.0), 9.42e-10)
    close(t_quart(2, 1.0), 3.73e-9)
    close(t_low(1.0), 2.63e-8)
    close(t_poly(2, 1.0), 8.77e-16)
    close(t_glue(2, 100.0), 3.09e-12)
    close(t_quart(2, 100.0), 2.33e-10)
    close(t_low(0.0), 2.29e-6)
    close(T0, 7.63e-6)
    close(T1, 3.78e-40)
    close(T2, 1.61e-57)
    bs = np.logspace(-9, math.log10(DIAG_SMALL), 200)
    assert np.all(bs < t_low(bs))  # StripWidth.diag_small: the small diagonal is inside the t_low strip
    bs = np.logspace(-7, 4, 2000)
    for N in (2, 3):
        # orderings proved in Lean: tPoly_le_tGlue, tGlue_le_tLift, tGlue_le_tQuart, tLift_le
        assert np.all(t_poly(N, bs) <= t_glue(N, bs))
        assert np.all(t_glue(N, bs) <= t_lift(N, bs) * (1 + 1e-12))
        assert np.all(t_glue(N, bs) <= t_quart(N, bs))
        assert np.all(t_lift(N, bs) <= 4 * t_glue(N, bs) * (1 + 1e-12))


# ---------------------------------------------------------------- figure 1: the coupling plane

BMIN, BMAX = 1e-7, 1e4
TMIN, TMAX = 1e-26, 1e4


def style_log_axes(ax):
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.tick_params(which="both", direction="out", length=3, width=0.6)
    ax.tick_params(which="minor", length=0)
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)


def fig_coupling_plane():
    b = np.logspace(math.log10(BMIN), math.log10(BMAX), 2000)
    fig, axes = plt.subplots(1, 2, figsize=(7.2, 4.1), sharey=True)
    for ax, N, G in zip(axes, (2, 3), ("SU(2)", "SU(3)")):
        lo, po, gl, li, qu = t_low(b), t_poly(N, b), t_glue(N, b), t_lift(N, b), t_quart(N, b)
        proved = np.maximum.reduce([lo, po, gl, li, qu])
        gapped = np.maximum.reduce([gl, li, qu])
        clip = lambda y: np.clip(y, TMIN, None)  # noqa: E731

        ax.fill_between(b, TMIN, TMAX, color=OPEN_FILL, lw=0, zorder=0)
        ax.fill_between(b, TMIN, clip(proved), color=BLUE_FILL, lw=0, zorder=1, step="post")
        ax.fill_between(b, TMIN, clip(gapped), facecolor="none", edgecolor=BLUE_HATCH, hatch="////",
                        lw=0, zorder=2, step="post")

        ax.plot(b, np.where(lo >= TMIN, lo, np.nan), color=ORANGE, ls="-", lw=1.4, zorder=4)
        ax.plot(b, clip(po), color=VIOLET, ls=":", lw=1.6, zorder=4)
        ax.plot(b, clip(gl), color=AQUA, ls="--", lw=1.4, zorder=4)
        ax.plot(b, clip(li), color=YELLOW, ls="-.", lw=1.2, zorder=4, drawstyle="steps-post")
        ax.plot(b, clip(qu), color=BLUE_DARK, ls="-", lw=1.8, zorder=5, drawstyle="steps-post")

        ax.plot(b, b, color=INK, lw=1.3, zorder=6)
        bd = b[b <= DIAG_SMALL]
        ax.plot(bd, bd, color=BLUE, lw=4.0, solid_capstyle="butt", zorder=7)

        ax.axhline(T0, color=MUTED, ls=(0, (4, 3)), lw=0.8, zorder=3)

        style_log_axes(ax)
        ax.set_xlim(BMIN, BMAX)
        ax.set_ylim(TMIN, TMAX)
        ax.set_xticks([1e-6, 1e-4, 1e-2, 1, 1e2, 1e4])
        ax.set_yticks([1e-24, 1e-20, 1e-16, 1e-12, 1e-8, 1e-4, 1])
        ax.set_xlabel(r"in-plane coupling $\beta$  ($\beta=\beta_W/2$)")
        ax.set_title(f"${G[:2]}({N})$", color=INK, pad=4)

        ax.text(3e2, 1e-2, "open", ha="center", va="center", color=INK2, fontsize=10, style="italic", zorder=8)
        ax.text(1.5e-7, T0 * 2.2, r"$2^{-17}$", color=MUTED, fontsize=7.5, va="bottom", zorder=8)
        ax.text(1.5e-7, 3e-23, "proved\nvanishing", color=BLUE_DARK, fontsize=8, va="bottom", zorder=8,
                bbox=dict(facecolor=BLUE_FILL, edgecolor="none", pad=1.0))
        ax.annotate("", xy=(6e-5, TMIN), xytext=(6e-5, 1e-23),
                    arrowprops=dict(arrowstyle="-|>", color=INK2, lw=0.8, mutation_scale=7), zorder=8)
        ax.text(9e-5, 2e-25, r"$t_1=e^{-88}/16$, $t_2=e^{-128}/16$", color=INK2, fontsize=7, va="bottom", zorder=8,
                bbox=dict(facecolor=BLUE_FILL, edgecolor="none", pad=1.0))

    axes[0].set_ylabel(r"mixed coupling $t$  ($t=t_W/2$)")

    handles = [
        Line2D([], [], color=ORANGE, ls="-", lw=1.4, label=r"$t_{\rm low}=e^{-4\beta}/(16192(16\beta+27))$"),
        Line2D([], [], color=VIOLET, ls=":", lw=1.6, label=r"$t_{\rm poly}=1/(16192\,n_0^2)$"),
        Line2D([], [], color=AQUA, ls="--", lw=1.4, label=r"$t_{\rm glue}=1/(16192\,A_{\rm glue})$"),
        Line2D([], [], color=YELLOW, ls="-.", lw=1.2, label=r"$t_{\rm lift}=1/(4048\cdot4^{w_0})$"),
        Line2D([], [], color=BLUE_DARK, ls="-", lw=1.8, label=r"$t_{\rm quart}=1/(2^{19}\cdot2^{w_0})$"),
        Patch(facecolor=BLUE_FILL, edgecolor="none", label="vanishing of the defect (proved)"),
        Patch(facecolor=BLUE_FILL, edgecolor=BLUE_HATCH, hatch="////", label=r"plus transfer gap at rate $\log 2/2^{w_0}$"),
        Line2D([], [], color=INK, lw=1.3, label=r"isotropic theory $t=\beta$"),
        Line2D([], [], color=BLUE, lw=4.0, label=r"diagonal, $\beta\leq 1/500000$ (proved)"),
        Line2D([], [], color=MUTED, ls=(0, (4, 3)), lw=0.8, label=r"$|t|\leq2^{-17}$: range of the quartic bound"),
    ]
    fig.legend(handles=handles, loc="lower center", ncol=2, bbox_to_anchor=(0.5, -0.27), handlelength=2.6,
               columnspacing=1.6, labelcolor=INK)
    fig.subplots_adjust(wspace=0.08)
    fig.canvas.draw()
    for ax in axes:  # label the diagonal along its on-screen slope
        p0, p1 = ax.transData.transform([(1e-3, 1e-3), (1e1, 1e1)])
        ang = math.degrees(math.atan2(p1[1] - p0[1], p1[0] - p0[0]))
        ax.text(1e-3, 1e-3 * 40, r"$t=\beta$", rotation=ang, rotation_mode="anchor", color=INK, fontsize=8.5,
                ha="center", va="bottom", zorder=8)
    save(fig, "fig_coupling_plane")


# ---------------------------------------------------------------- figure 2: the strip widths

def fig_strip_widths():
    b = np.logspace(-3, 4, 3000)
    fig, axes = plt.subplots(1, 2, figsize=(7.2, 3.3), sharey=True)
    for ax, N in zip(axes, (2, 3)):
        ax.plot(b, b, color=MUTED, lw=0.9, zorder=2)
        ax.plot(b, t_low(b), color=ORANGE, ls="-", lw=1.4, zorder=3)
        ax.plot(b, t_poly(N, b), color=VIOLET, ls=":", lw=1.6, zorder=3)
        ax.plot(b, t_glue(N, b), color=AQUA, ls="--", lw=1.4, zorder=3)
        ax.plot(b, t_quart(N, b), color=BLUE_DARK, ls="-", lw=1.8, zorder=4, drawstyle="steps-post")
        style_log_axes(ax)
        ax.grid(True, which="major", axis="y", color=GRID, lw=0.5, zorder=0)
        ax.set_xlim(1e-3, 1e4)
        ax.set_ylim(1e-24, 1e2)
        ax.set_xticks([1e-3, 1e-1, 10, 1e3])
        ax.set_yticks([1e-24, 1e-20, 1e-16, 1e-12, 1e-8, 1e-4, 1])
        ax.set_xlabel(r"in-plane coupling $\beta$  ($\beta=\beta_W/2$)")
        ax.set_title(f"$SU({N})$", color=INK, pad=4)
        # direct labels at the right end
        bR = 3e3
        ax.text(bR, t_quart(N, bR) * 6, r"$t_{\rm quart}$", color=INK, fontsize=8, ha="center", va="bottom")
        ax.text(bR, t_glue(N, bR) * 6, r"$t_{\rm glue}$", color=INK, fontsize=8, ha="center", va="bottom")
        ax.text(bR, t_poly(N, bR) * 6, r"$t_{\rm poly}$", color=INK, fontsize=8, ha="center", va="bottom")
        ax.text(4.0, 1e-20, r"$t_{\rm low}$", color=INK, fontsize=8, ha="right", va="center")
        ax.text(2e-3, 2e-3 * 8, r"$t=\beta$", color=MUTED, fontsize=8, rotation=0, ha="left", va="bottom")
    axes[0].set_ylabel(r"width $t(\beta)$  ($t=t_W/2$)")
    handles = [
        Line2D([], [], color=ORANGE, ls="-", lw=1.4, label=r"$t_{\rm low}$ (open boundary)"),
        Line2D([], [], color=VIOLET, ls=":", lw=1.6, label=r"$t_{\rm poly}$"),
        Line2D([], [], color=AQUA, ls="--", lw=1.4, label=r"$t_{\rm glue}$"),
        Line2D([], [], color=BLUE_DARK, ls="-", lw=1.8, label=r"$t_{\rm quart}$ (step in $w_0$)"),
        Line2D([], [], color=MUTED, lw=0.9, label=r"$t=\beta$"),
    ]
    fig.legend(handles=handles, loc="lower center", ncol=5, bbox_to_anchor=(0.5, -0.07), handlelength=2.4,
               columnspacing=1.4, labelcolor=INK)
    fig.subplots_adjust(wspace=0.08, bottom=0.2)
    save(fig, "fig_strip_widths")


# ---------------------------------------------------------------- figure 3: the proof route


# CHOSEN: 8.4 pt titles and 7.3 pt body text are typographic sizes for the printed figure; they
# change no plotted value.
def box(ax, x, y, w, h, title, body, kind, tfs=8.4, bfs=7.3):
    face, edge, ls = {
        "target": ("#ffffff", INK, "-"),
        "theorem": ("#ffffff", INK, "-"),
        "open": ("#fdf0ea", ORANGE, (0, (4, 2))),
        "proved": (BLUE_FILL, BLUE_DARK, "-"),
        "side": ("#eef4fc", BLUE_DARK, "-"),
    }[kind]
    lw = 1.4 if kind in ("target", "theorem") else 1.0
    ax.add_patch(FancyBboxPatch((x - w / 2, y - h / 2), w, h, boxstyle="round,pad=0.02,rounding_size=0.12",
                                facecolor=face, edgecolor=edge, lw=lw, ls=ls, zorder=2))
    tag = {"open": "open", "proved": "proved, used in the proof", "side": "proved"}.get(kind)
    top = y + h / 2 - 0.16
    ax.text(x, top, title, ha="center", va="top", fontsize=tfs, color=INK, weight="bold", zorder=3)
    if tag:
        top -= 0.36
        ax.text(x, top, tag, ha="center", va="top", fontsize=6.8, color=ORANGE if kind == "open" else BLUE_DARK,
                style="italic", zorder=3)
    ax.text(x, top - 0.36, body, ha="center", va="top", fontsize=bfs, color=INK2, zorder=3, linespacing=1.3)


# CHOSEN: `lpos=0.5` puts an arrow's label at its midpoint; layout only.
def arrow(ax, p, q, style="solid", label=None, lpos=0.5, loff=(0, 0), color=INK):
    ls = "-" if style == "solid" else (0, (3, 2))
    ax.add_patch(FancyArrowPatch(p, q, arrowstyle="-|>", mutation_scale=9, lw=0.9, color=color, ls=ls,
                                 shrinkA=1, shrinkB=1, zorder=1))
    if label:
        mx = p[0] + (q[0] - p[0]) * lpos + loff[0]
        my = p[1] + (q[1] - p[1]) * lpos + loff[1]
        ax.text(mx, my, label, fontsize=6.9, color=INK2, ha="center", va="center", style="italic", zorder=3,
                bbox=dict(facecolor="white", edgecolor="none", pad=0.8))


def fig_proof_route():
    fig, ax = plt.subplots(figsize=(9.0, 6.6))
    ax.set_xlim(0, 18)
    ax.set_ylim(0, 13.2)
    ax.axis("off")

    # row 1: target
    box(ax, 9.0, 12.2, 14.0, 1.5, r"CS($N$): the formalized target of section 4",
        "Osterwalder–Schrader axioms for the tensor and all gauge-invariant local composites on separated test\n"
        "functions; reconstructed Hamiltonian with a gap; asymptotic freedom; non-Gaussianity", "target")
    # row 2: theorem and the proved facts it uses
    box(ax, 7.0, 9.35, 8.6, 1.7, r"Theorem 1.1 ($N\geq 2$; section 4)",
        r"if (S) holds and, frequently as $u_0\to 0^+$, every coupling tower" "\n"
        r"at window coupling $u_0$ satisfies (M) and (E), then CS($N$) holds", "theorem")
    box(ax, 15.0, 9.35, 5.6, 2.85, "Facts along a tower (section 4.4)",
        r"towers at every $u_0$ near $0^+$, from (S);" "\n"
        r"transfer gap at rate $\log 2/2^k$ (the basin);" "\n"
        r"lower bound on the window reading; $g_\beta(0)>0$;" "\n"
        "abelian generator; reflection positivity;\nGibbs measure; traces separate", "proved", bfs=7.0)
    # row 3: the three open inputs
    iy, ih = 5.95, 2.3
    box(ax, 3.0, iy, 5.2, ih, "(M) mass band",
        "the window reading of the tensor\nmass stays in a band of ratio 2,\nat a level chosen per tower", "open")
    box(ax, 9.0, iy, 5.6, ih, "(S) the bridge",
        r"frequently as $\beta\to\infty$, $D_\beta(w)\to 0$;" "\n"
        r"equivalently some window has $D_\beta(w)\leq 1/1000$;" "\n"
        "the only input about the defect", "open")
    box(ax, 15.0, iy, 5.2, ih, "(E) existence clauses",
        "flow moments and range, mixing and ties,\nAF kernel, non-Gaussianity, Ward identity,\ncomposites and link, along every tower",
        "open")
    # row 4: supporting results
    sy, sh, sw = 1.55, 2.75, 2.7
    xs = (1.55, 4.53, 7.51, 10.49, 13.47, 16.45)
    sfs = 6.7
    box(ax, xs[0], sy, sw, sh, "Decoupled end",
        "section 7\n" r"$t=0$: product of" "\n" r"2D tori; $D\to 0$" "\n" r"at every $\beta\geq0$", "side", bfs=sfs)
    box(ax, xs[1], sy, sw, sh, "Anisotropic strip",
        "section 7\n" r"$0\leq t\leq t_{\rm proved}(\beta)$:" "\n" "vanishing and a size-\nuniform transfer gap", "side",
        bfs=sfs)
    box(ax, xs[2], sy, sw, sh, "Doubling bootstrap",
        "section 5\n" r"$D\leq\frac{1}{1000}\Rightarrow D'\leq 250\,D^2$;" "\n" "one window suffices;\ngap from the basin",
        "side", bfs=sfs)
    box(ax, xs[3], sy, sw, sh, "Separators",
        "section 9\n" r"tested on $U(1)$, $A_5$, $G_2$;" "\n" "each fails; filters a\nproof of (S) must pass", "side",
        bfs=sfs)
    box(ax, xs[4], sy, sw, sh, "Aperture count",
        "section 3\n" "the Rényi-" r"$\frac{1}{2}$" " count moves" "\n" "the moment clause of (E)\nonto two single-\nobserver bounds",
        "side", bfs=sfs)
    box(ax, xs[5], sy, sw, sh, "Box route",
        "section 8\n" r"box gaps at $SU(2)$, $SU(3)$;" "\n" r"concludes $\mathcal{C}(L)$," "\n" "not CS($N$); ultra-\nviolet step open",
        "side", bfs=sfs)

    top_in, bot_th = iy + ih / 2, 9.35 - 0.85
    arrow(ax, (7.0, 9.35 + 0.85), (7.0, 12.2 - 0.75))
    arrow(ax, (3.0, top_in), (4.6, bot_th))
    arrow(ax, (8.4, top_in), (7.6, bot_th))
    arrow(ax, (13.6, top_in), (10.4, bot_th))
    arrow(ax, (12.2, 9.35), (11.3, 9.35))

    s_top = sy + sh / 2
    arrow(ax, (xs[0] + sw / 2, sy), (xs[1] - sw / 2, sy))
    arrow(ax, (xs[2], s_top), (xs[2], iy - ih / 2), label="reduces (S)\nto one window", lpos=0.5)
    arrow(ax, (xs[1] + 0.6, s_top), (7.4, iy - ih / 2), style="dashed", label=r"stops short of $t=\beta$",
          lpos=0.5, loff=(-0.9, 0))
    arrow(ax, (xs[3] - 0.6, s_top), (10.8, iy - ih / 2), style="dashed", label="tests, not\nimplications",
          lpos=0.5, loff=(0.9, 0))
    arrow(ax, (xs[4] + 0.3, s_top), (14.6, iy - ih / 2), style="dashed", label="discharges\nnone of (E)",
          lpos=0.5, loff=(0.9, 0))

    handles = [
        Patch(facecolor="#fdf0ea", edgecolor=ORANGE, ls=(0, (4, 2)), label="open input"),
        Patch(facecolor=BLUE_FILL, edgecolor=BLUE_DARK, label="proved, used by Theorem 1.1"),
        Patch(facecolor="#eef4fc", edgecolor=BLUE_DARK, label="proved, supporting result"),
        Line2D([], [], color=INK, lw=0.9, label="implication"),
        Line2D([], [], color=INK, lw=0.9, ls=(0, (3, 2)), label="relation, not an implication"),
    ]
    fig.legend(handles=handles, loc="lower center", ncol=5, bbox_to_anchor=(0.5, 0.02), fontsize=7.4,
               handlelength=1.8, columnspacing=1.4, labelcolor=INK)
    save(fig, "fig_proof_route")


# ---------------------------------------------------------------- figure 4: the bootstrap


def fig_bootstrap():
    seed = 1e-3
    fig, ax = plt.subplots(figsize=(4.6, 4.4))
    lo, hi = 1e-14, 1e-1
    x = np.logspace(math.log10(lo), math.log10(hi), 400)
    ax.axvspan(lo, seed, color=BLUE_FILL, lw=0, zorder=0)
    ax.plot(x, x, color=MUTED, lw=0.9, zorder=2)
    inb = x <= seed
    ax.plot(x[inb], 250 * x[inb] ** 2, color=BLUE_DARK, lw=1.8, zorder=3)
    ax.plot(x[~inb], 250 * x[~inb] ** 2, color=BLUE_DARK, lw=1.0, ls=(0, (2, 2)), zorder=3)
    ax.plot(x[inb], x[inb] / 4, color=AQUA, lw=1.1, ls="--", zorder=2)

    # cobweb: (D, 250 D^2) -> diagonal -> next
    d = seed
    cx, cy = [d], [lo]
    pts = []
    for _ in range(4):
        nd = 250 * d * d
        pts.append((d, nd))
        cx += [d, nd]
        cy += [nd, nd]
        d = nd
    ax.plot(cx, cy, color=ORANGE, lw=1.1, zorder=4)
    for k, (px, py) in enumerate(pts):
        ax.plot([px], [py], "o", ms=4.5, color=ORANGE, mec="white", mew=0.8, zorder=5)
        # DERIVED: `0` is the first iterate, the starting window itself.
        lab = "$w_0$" if k == 0 else f"$w_0+{k}$"
        ax.text(px * 3.0, py / 3.0, lab, fontsize=7.5, color=INK, ha="left", va="top", zorder=6)

    ax.axvline(1 / 250, color=MUTED, lw=0.7, ls=(0, (1, 2)), zorder=1)
    ax.text(1 / 250 * 1.25, 3e-14, r"$1/250$", color=INK2, fontsize=7.5, rotation=90, va="bottom")
    ax.text(seed / 1.25, 3e-14, r"$1/1000$", color=INK2, fontsize=7.5, rotation=90, va="bottom", ha="right")
    ax.text(2.2e-2, 1e-9, "no bound proved", color=INK2, fontsize=7.3, ha="center", va="center", rotation=90,
            style="italic")
    ax.text(seed / 3, 3e-12, "basin\n" r"$D\leq 1/1000$", color=BLUE_DARK, fontsize=8, ha="right", va="bottom")

    style_log_axes(ax)
    ax.set_xlim(lo, hi)
    ax.set_ylim(lo, hi)
    ax.set_aspect("equal")
    ax.set_xticks([1e-14, 1e-11, 1e-8, 1e-5, 1e-2])
    ax.set_yticks([1e-14, 1e-11, 1e-8, 1e-5, 1e-2])
    ax.set_xlabel(r"defect at window $w$, $D_\beta(w)$")
    ax.set_ylabel(r"bound on the defect at window $w+1$")
    handles = [
        Line2D([], [], color=BLUE_DARK, lw=1.8, label=r"$D_\beta(w+1)\leq 250\,D_\beta(w)^2$"),
        Line2D([], [], color=AQUA, lw=1.1, ls="--", label=r"$250\,D_\beta(w)^2\leq D_\beta(w)/4$"),
        Line2D([], [], color=MUTED, lw=0.9, label="diagonal"),
        Line2D([], [], color=ORANGE, lw=1.1, marker="o", ms=4.5, mec="white",
               label=r"orbit from $D_\beta(w_0)=1/1000$"),
    ]
    ax.legend(handles=handles, loc="upper left", fontsize=7.3, labelcolor=INK, handlelength=2.2,
              facecolor="white", frameon=True, edgecolor="none", framealpha=0.95)
    save(fig, "fig_bootstrap")


if __name__ == "__main__":
    check_reference_values()
    fig_coupling_plane()
    fig_strip_widths()
    fig_proof_route()
    fig_bootstrap()
    print("written:", sorted(p.name for p in OUT.glob("fig_*")))
