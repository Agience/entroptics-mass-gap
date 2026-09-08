"""8_6_fig_probe.py -- the four deterministic transfer functions from 8_6_run_probe.py, one 2x2 figure.

Reads 8_6_dat_probe.csv (written by 8_6_run_probe.py) and draws the input->output laws, each an exact law to
machine precision (no Monte Carlo, no fit):
  P1  the gap read inverts the operator: read rate = input Delta (identity, residual ~1e-11)
  P2  the diffraction limit is the reciprocal correlation length: a_delta * rho = const (Abbe)
  P3  A1: the vortex tension crosses the counting floor kappa_0 = (1/4)ln3 exactly at contrast 3^(1/4)
  P4  A2: the read's hypercubic anisotropy is exactly zero (machine precision) once the grid resolves
      the field (a < a*), with the Nyquist law a*.k0 = const -- SO(4) exact below threshold.
No reads here: this only plots the CSV the probe already wrote.
"""
from __future__ import annotations

import csv
import math
import os

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from mpl_toolkits.axes_grid1.inset_locator import inset_axes

_HERE = os.path.dirname(os.path.abspath(__file__))
DAT = os.path.join(_HERE, "8_6_dat_probe.csv")
FIG = os.path.join(_HERE, "8_6_fig_probe.png")
K0 = 0.25 * math.log(3.0)
EPS = 2.220446049250313e-16                     # IEEE-754 double machine epsilon

BLUE, RED, GREEN, PURPLE, GREY = "#1f4e8c", "#b03030", "#2e7d32", "#6a3d9a", "#8a8a8a"


def load():
    rows = {}
    with open(DAT) as f:
        for r in csv.DictReader(f):
            rows.setdefault(r["probe"], []).append(r)
    return rows


def col(rs, k):
    return [float(r[k]) for r in rs if r.get(k) not in (None, "")]


def main():
    R = load()
    plt.rcParams.update({"font.size": 10, "axes.titlesize": 11.5, "axes.titleweight": "bold"})
    fig, ax = plt.subplots(2, 2, figsize=(12.5, 9.6))

    # -- P1  gap read inverts the operator (identity to ~1e-11) ------------------------------
    g = R["P1_gap"]
    x, y = col(g, "x"), col(g, "y")
    res = [abs(v) for v in col(g, "residual")]
    maxres = max(res) if res else float("nan")
    a1 = ax[0, 0]
    lim = max(x) * 1.04
    a1.plot([0, lim], [0, lim], "-", color=GREY, lw=1.4, zorder=1, label="identity  read $=\\Delta$")
    a1.plot(x, y, "o", color=BLUE, ms=7, zorder=3, label="DMD/Koopman gap read")
    a1.set_xlim(0, lim); a1.set_ylim(0, lim)
    a1.set_xlabel(r"input gap  $\Delta = -\log|\mu_1|$"); a1.set_ylabel(r"read gap  $\widehat{\Delta}$")
    a1.set_title("P1   the gap read inverts the operator")
    a1.legend(loc="upper left", frameon=False)
    a1.text(0.97, 0.06, f"max residual  {maxres:.0e} nats\n(reads the gap, not a fit)",
            transform=a1.transAxes, ha="right", va="bottom", fontsize=9,
            bbox=dict(boxstyle="round,pad=0.35", fc="#eef3fb", ec=BLUE, lw=0.8))

    # -- P2  Abbe: a_delta * rho = const (the aperture is 1/rho) -----------------------------
    g = R["P2_abbe"]
    rho, ad = col(g, "x"), col(g, "y")
    prod = [a * r for a, r in zip(ad, rho)]
    mean = sum(prod) / len(prod)
    spread = (sum((p - mean) ** 2 for p in prod) / len(prod)) ** 0.5 / mean   # coeff. of variation
    a2 = ax[0, 1]
    a2.plot(rho, prod, "o-", color=RED, ms=6, lw=1.6, label=r"$a_\delta \cdot \rho$")
    a2.axhline(mean, ls="--", color=GREY, lw=1.2, label=f"mean {mean:.3f}")
    a2.set_ylim(0, max(prod) * 1.6)
    a2.set_xlabel(r"correlation length  $\rho$  (lattice units)"); a2.set_ylabel(r"$a_\delta \cdot \rho$")
    a2.set_title(r"P2   the reciprocal-length law  ($a_\delta\,\rho=$ const)")
    a2.legend(loc="upper right", frameon=False)
    a2.text(0.03, 0.06, f"invariant to {spread:.1%} over a decade of $\\rho$",
            transform=a2.transAxes, ha="left", va="bottom", fontsize=9,
            bbox=dict(boxstyle="round,pad=0.35", fc="#fbeeee", ec=RED, lw=0.8))

    # -- P3  A1: mu < kappa_0  <=>  contrast < 3^(1/4)  (exact) ------------------------------
    g = R["P3_confinement"]
    con, mu = col(g, "contrast"), col(g, "mu")
    order = sorted(range(len(con)), key=lambda i: con[i])
    con = [con[i] for i in order]; mu = [mu[i] for i in order]
    a3 = ax[1, 0]
    a3.axvspan(0, math.exp(K0), color="#eef7ee", zorder=0)
    a3.plot(con, mu, "o-", color=GREEN, ms=6, lw=1.6, zorder=3, label=r"$\mu=\log(\lambda_1/\lambda_+)$")
    a3.axhline(K0, ls="--", color=RED, lw=1.4, label=r"floor $\kappa_0=\frac{1}{4}\ln 3$")
    a3.axvline(math.exp(K0), ls=":", color=RED, lw=1.4, label=r"$3^{1/4}$")
    a3.set_xlim(0, min(6, max(con) * 1.02)); a3.set_ylim(-0.05, max(mu) * 1.05 if mu else 1)
    a3.set_xlabel(r"leading-mode ratio  $\lambda_1/\lambda_+$  (mode / noise floor)")
    a3.set_ylabel(r"vortex tension  $\mu$  (nats)")
    a3.set_title(r"P3   A1: confinement as an eigenvalue bound")
    a3.legend(loc="upper right", bbox_to_anchor=(0.99, 0.44), fontsize=9,
              frameon=True, facecolor="white", framealpha=0.97, edgecolor="#888888", fancybox=True)
    a3.text(0.03, 0.94, "confined  $\\mu<\\kappa_0$\n$\\Leftrightarrow \\lambda_1/\\lambda_+ < 3^{1/4}$\n($e^{\\kappa_0}=3^{1/4}$ identically)",
            transform=a3.transAxes, ha="left", va="top", fontsize=9,
            bbox=dict(boxstyle="round,pad=0.35", fc="#eef7ee", ec=GREEN, lw=0.8))

    # -- P4  A2: hypercubic anisotropy is EXACTLY zero below the sampling threshold ----------
    g = R["P4b_restoration"]
    ppw, var = col(g, "x"), col(g, "y")
    o = sorted(range(len(ppw)), key=lambda i: ppw[i])
    ppw = [ppw[i] for i in o]; var = [max(var[i], EPS) for i in o]
    a4 = ax[1, 1]
    # threshold: first ppw where anisotropy reaches the machine floor
    thr = next((ppw[i] for i in range(len(ppw)) if var[i] <= 1e-10), None)
    if thr is not None:
        a4.axvspan(thr, max(ppw) * 1.02, color="#f0ecf7", zorder=0)
        a4.axvline(thr, color=PURPLE, ls="--", lw=1.3)
        a4.text(thr + 0.4, 3e-2, f"isotropic to\nmachine zero\n$a_\\delta(\\theta)$ const for\nppw $>{thr:.1f}$",
                fontsize=8.6, color=PURPLE, va="center")
    a4.axhline(EPS, color=GREY, ls=":", lw=1.1)
    a4.text(4.2, EPS * 1.6, "machine $\\epsilon$", fontsize=8, color=GREY, va="bottom")
    a4.semilogy(ppw, var, "o-", color=PURPLE, ms=5.5, lw=1.6, zorder=3)
    a4.set_xlim(min(ppw), max(ppw) * 1.02); a4.set_ylim(EPS * 0.4, 1.0)
    a4.set_xlabel(r"resolution  (points per correlation length,  $2\pi/a$)")
    a4.set_ylabel(r"read anisotropy  $\Delta a_\delta(\theta)/a_\delta$")
    a4.set_title(r"P4   A2: $SO(4)$ restored below the sampling threshold")

    # inset: Nyquist law a*.k0 = const
    if "P4d_nyquist" in R:
        d = R["P4d_nyquist"]
        k0, astar = col(d, "x"), col(d, "y")
        prodk = [a * k for a, k in zip(astar, k0)]
        cst = sum(prodk) / len(prodk)
        invk = [1.0 / k for k in k0]
        ins = inset_axes(a4, width="33%", height="30%", loc="lower left",
                         bbox_to_anchor=(0.06, 0.09, 1, 1), bbox_transform=a4.transAxes)
        xx = [0.0, max(invk) * 1.08]
        ins.plot(xx, [cst * x for x in xx], "-", color=RED, lw=1.3, zorder=1)   # a* = 0.364 / k0
        ins.plot(invk, astar, "o", color=PURPLE, ms=5, zorder=3)
        ins.set_xlim(0, max(invk) * 1.08); ins.set_ylim(0, max(astar) * 1.1)
        ins.set_title(f"$a^*\\!\\cdot k_0={cst:.3f}$ (Nyquist)", fontsize=8.5, pad=3)
        ins.set_xlabel(r"$1/k_0$", fontsize=8, labelpad=1); ins.set_ylabel(r"$a^*$", fontsize=8, labelpad=1)
        ins.tick_params(labelsize=7)

    for a in ax.ravel():
        a.grid(True, alpha=0.22)
    fig.suptitle("Deterministic system identification of the entroptics read:  four input-to-output laws to "
                 "machine precision, no Monte Carlo, no fit", fontsize=12.5, y=0.995)
    fig.tight_layout(rect=(0, 0, 1, 0.965))
    fig.savefig(FIG, dpi=140)
    print("wrote", FIG)


if __name__ == "__main__":
    main()
