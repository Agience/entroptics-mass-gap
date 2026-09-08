"""8.8 — the string tension by standard observables, drawn from the committed tables.

Three panels, because the tension is three claims, not one number:

  A  sigma(T) from the static potential. The T-dependence IS the excited-state systematic and is
     shown, not hidden: filled markers are the T resolved at 3 sigma, open markers the T where the
     Wilson-loop signal is exhausted, and the arrow marks the T the value is read at.
  B  The Creutz ratios chi(R,R) against 1/R^2 -- the route with NO model of V(R), since the static
     self-energy V0 cancels identically in the double difference. The dashed line is the
     one-parameter extrapolation chi = sigma + c/R^2; its intercept is an independent estimate of
     the same sigma, and it agrees with A.
  C  a^2 sigma against beta, with the two-loop lattice beta-function anchored at the lowest measured
     coupling -- a parameter-free SHAPE prediction that a physical tension must fall along.

Reads 8_8_dat_string_tension.csv and 8_8_dat_string_tension_curves.csv. Writes 8_8_fig_string_tension.png.
"""
import csv
import math
import os
import sys
sys.path.insert(0, os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "code")))
from lattice_scales import a_lambda   # one implementation of the two-loop a*Lambda_lat

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

_HERE = os.path.dirname(os.path.abspath(__file__))
SUM = os.path.join(_HERE, "8_8_dat_string_tension.csv")
CUR = os.path.join(_HERE, "8_8_dat_string_tension_curves.csv")
OUT = os.path.join(_HERE, "8_8_fig_string_tension.png")
PALETTE = ["#1f4e8c", "#b03030", "#2e7d32", "#8c6d1f"]


def _rows(path):
    if not os.path.exists(path):
        raise SystemExit(f"{os.path.basename(path)} is missing -- run its owner first; this script "
                         f"draws committed data and measures nothing")
    with open(path, newline="") as fh:
        return list(csv.DictReader(fh))


def _f(v):
    return float(v) if v not in ("", None) else float("nan")




def main():
    summ, cur = _rows(SUM), _rows(CUR)
    betas = sorted({float(r["beta"]) for r in summ})
    colors = {b: PALETTE[i % len(PALETTE)] for i, b in enumerate(betas)}
    fig, (axA, axB, axC) = plt.subplots(1, 3, figsize=(16.6, 4.9))

    # ---- A: sigma(T), the excited-state systematic ----------------------------------------------
    keep = []
    for b in betas:
        pts = sorted((r for r in cur if r["kind"] == "sigma_T" and float(r["beta"]) == b),
                     key=lambda r: int(r["x"]))
        xs = [int(r["x"]) for r in pts]
        ys = [_f(r["value"]) for r in pts]
        es = [_f(r["err"]) for r in pts]
        use = [r["used"] == "1" for r in pts]
        c = colors[b]
        axA.errorbar([x for x, u in zip(xs, use) if u], [y for y, u in zip(ys, use) if u],
                     yerr=[e for e, u in zip(es, use) if u], marker="o", ms=5, lw=1.4,
                     color=c, capsize=2, label=rf"$\beta={b:.2f}$")
        axA.errorbar([x for x, u in zip(xs, use) if not u], [y for y, u in zip(ys, use) if not u],
                     yerr=[e for e, u in zip(es, use) if not u], marker="o", ms=5, lw=0,
                     mfc="white", color=c, capsize=2)
        row = next(r for r in summ if float(r["beta"]) == b)
        y0 = _f(row["a2sigma_potential"])
        axA.annotate("read", xy=(int(row["t_read"]), y0), xycoords="data",
                     xytext=(0, 26), textcoords="offset points", ha="center", fontsize=8, color=c,
                     arrowprops=dict(arrowstyle="->", color=c, lw=1.3))
        keep += [(y, e) for y, e, u in zip(ys, es, use) if u]
    axA.set_xlabel("Euclidean time extent $T$ of the Wilson loop")
    axA.set_ylabel(r"$a^2\sigma$ from $V(R)=V_0+\sigma R-e/R$")
    axA.set_title("A. the $T$-systematic, shown (hollow / off-scale = not resolved at $3\\sigma$)")
    # Scale to the RESOLVED points. The rejected T is an order of magnitude noisier (T=4 carries
    # +/-0.038 on 0.062); letting it set the range hides the structure the panel exists to show.
    # It stays plotted and runs off the axis, which is the honest picture of "not resolved".
    if keep:
        axA.set_ylim(min(y - e for y, e in keep) * 0.88, max(y + e for y, e in keep) * 1.30)
    axA.legend(fontsize=8, frameon=False)
    axA.grid(alpha=0.25)

    # ---- B: Creutz ratios, the model-free route -------------------------------------------------
    for b in betas:
        pts = sorted((r for r in cur if r["kind"] == "chi_RR" and float(r["beta"]) == b),
                     key=lambda r: int(r["x"]))
        c = colors[b]
        for r in pts:
            y, e = _f(r["value"]), _f(r["err"])
            if y != y:
                continue
            axB.errorbar([1.0 / int(r["x"]) ** 2], [y], yerr=[e], marker="s", ms=5, color=c,
                         capsize=2, mfc=c if r["used"] == "1" else "white", lw=0)
        row = next(r for r in summ if float(r["beta"]) == b)
        s0 = _f(row["a2sigma_creutz"])
        used = [int(r["x"]) for r in pts if r["used"] == "1"]
        if s0 == s0 and used:
            xmax = 1.0 / min(used) ** 2
            ylo = next(_f(r["value"]) for r in pts if int(r["x"]) == max(used))
            slope = (ylo - s0) / (1.0 / max(used) ** 2)
            axB.plot([0, xmax], [s0, s0 + slope * xmax], ls="--", lw=1.2, color=c)
            axB.plot([0], [s0], marker="*", ms=13, color=c,
                     label=rf"$\beta={b:.2f}$: $a^2\sigma={s0:.4f}$")
    axB.set_xlabel(r"$1/R^2$")
    axB.set_ylabel(r"Creutz ratio $\chi(R,R)$")
    axB.set_title("B. no model of $V(R)$: $V_0$ cancels")
    kb = [(_f(r["value"]), _f(r["err"])) for r in cur
          if r["kind"] == "chi_RR" and r["used"] == "1" and _f(r["value"]) == _f(r["value"])]
    if kb:                       # chi(7,7) = -0.61 +/- 1.08 would otherwise own the whole axis
        axB.set_ylim(min(0.0, min(y - e for y, e in kb) * 0.9), max(y + e for y, e in kb) * 1.25)
    axB.set_xlim(left=-0.005)
    axB.legend(fontsize=8, frameon=False)
    axB.grid(alpha=0.25)

    # ---- C: does it scale? ----------------------------------------------------------------------
    xs = [float(r["beta"]) for r in summ]
    ys = [_f(r["a2sigma_potential"]) for r in summ]
    es = [math.hypot(_f(r["a2sigma_err"]), _f(r["a2sigma_syst"])) for r in summ]
    axC.errorbar(xs, ys, yerr=es, marker="o", ms=6, lw=0, color="#1f4e8c", capsize=3,
                 label=r"$V(R)$ fit (stat $\oplus$ syst)")
    axC.plot(xs, [_f(r["a2sigma_creutz"]) for r in summ], marker="*", ms=12, lw=0,
             color="#2e7d32", label="Creutz, model-free")
    if len(xs) >= 2:
        b0 = min(xs)
        s0 = ys[xs.index(b0)]
        grid = [b0 + i * (max(xs) - b0) / 60.0 for i in range(61)]
        axC.plot(grid, [s0 * (a_lambda(b) / a_lambda(b0)) ** 2 for b in grid], ls="--", lw=1.3,
                 color="#888", label=r"two-loop $a^2\Lambda^2$, anchored at $\beta_{\min}$")
        axC.set_yscale("log")
    else:
        axC.text(0.5, 0.08, "one coupling: the scaling test needs $L=16$ links at further $\\beta$",
                 transform=axC.transAxes, ha="center", fontsize=8, color="#b03030")
    axC.set_xlabel(r"$\beta=4/g^2$")
    axC.set_ylabel(r"$a^2\sigma$")
    axC.set_title("C. asymptotic scaling")
    axC.legend(fontsize=8, frameon=False)
    axC.grid(alpha=0.25, which="both")

    L, n = summ[0]["L"], summ[0]["ncfg"]
    fig.suptitle(f"SU(2) string tension from planar Wilson loops, $L={L}$, {n} configurations per "
                 f"coupling — no Entroptics read", fontsize=11)
    fig.tight_layout(rect=(0, 0.01, 1, 0.95))
    fig.savefig(OUT, dpi=150)
    print("wrote", OUT)


if __name__ == "__main__":
    main()
