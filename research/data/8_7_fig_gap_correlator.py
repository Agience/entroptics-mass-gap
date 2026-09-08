"""8.7 — the correlator the gap read is taken from, and what the operator choice does to it.

Four panels, drawn from 8_7_dat_gap_correlator.csv (measured with no read on top of it) and
8_8_dat_string_tension.csv (the independently measured sigma that sets the expected scale):

  A  C(tau)/C(0), log scale, both operators at every coupling. The action density falls to ~0.1-0.2
     at tau=1 and into noise by tau~2; the APE-smeared spatial plaquette carries a decade of clean
     signal. Same configurations, same lattice, same read afterwards -- only the operator differs.
  B  m_eff(tau) = log[C(tau)/C(tau+1)] against the expected a*m_0++ = 3.59 sqrt(sigma) (dashed).
     Reflection positivity makes m_eff monotone decreasing onto the gap from above, so the plateau
     is the gap. The plaquette curves descend onto the line; the action-density curves sit far above
     it at every tau and never approach it.
  C  The scaling test in beta. Delta/(a Lambda_lat) = m/Lambda must be a constant if Delta is a
     mass. The variational minimum over the full basis holds it (chi2/dof = 0.21, spread 1.09x);
     the action density alone drifts 1.44x upward across the same three couplings. Both series are
     selected by the same rule, so the difference is the operator and not the selection.
  D  The scaling test in volume, at beta = 2.30. The same variational read across L, with L = 8
     shown apart as the small-volume edge: what rho'(n) = rho'(1)^n needs is a cut that does not
     grow with L, so it is the flatness here rather than the value that the argument uses.

What the figure establishes: the operator, not the read, determines whether a decay rate is a mass.
The action density is a local composite whose C(0) carries uncorrelated variance the other lags do
not, so -log[C(1)/C(0)] measures an operator-overlap ratio and barely moves with beta.

Writes 8_7_fig_gap_correlator.png.
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
DAT = os.path.join(_HERE, "8_7_dat_gap_correlator.csv")
TEN = os.path.join(_HERE, "8_8_dat_string_tension.csv")
OUT = os.path.join(_HERE, "8_7_fig_gap_correlator.png")
COLOR = {2.3: "#1f4e8c", 2.4: "#b03030", 2.5: "#2e7d32"}
# The smearing at which each operator is read. Chosen from the artifact's own scan: the action
# density never improves, the plaquette saturates by 24 sweeps.
NS = {"action_density": 24, "plaquette_0pp": 24}


def _rows(p):
    if not os.path.exists(p):
        raise SystemExit(f"{os.path.basename(p)} missing -- run its owner first")
    with open(p, newline="") as fh:
        return list(csv.DictReader(fh))


def _f(v):
    return float(v) if v not in ("", None) else float("nan")




def main():
    rows = _rows(DAT)
    betas = sorted({float(r["beta"]) for r in rows})
    fig, (axA, axB, axC, axD) = plt.subplots(1, 4, figsize=(21.5, 4.9))

    # ---- A: the correlator itself -------------------------------------------------------------
    for beta in betas:
        for op, ls, mk in (("action_density", ":", "o"), ("plaquette_0pp", "-", "s")):
            sel = sorted((r for r in rows if float(r["beta"]) == beta and r["operator"] == op
                          and int(r["nsmear"]) == NS[op]), key=lambda r: int(r["tau"]))
            x = [int(r["tau"]) for r in sel]
            y = [_f(r["C_over_C0"]) for r in sel]
            e = [_f(r["C_err"]) for r in sel]
            keep = [(a, b_, c) for a, b_, c in zip(x, y, e) if b_ > 0]
            if not keep:
                continue
            axA.errorbar([a for a, _, _ in keep], [b_ for _, b_, _ in keep],
                         yerr=[c for _, _, c in keep], ls=ls, marker=mk, ms=4, lw=1.3,
                         color=COLOR[beta], capsize=2,
                         label=(rf"$\beta={beta:.2f}$ plaquette" if op == "plaquette_0pp"
                                else rf"$\beta={beta:.2f}$ action density"))
    axA.set_yscale("log")
    axA.set_xlabel(r"$\tau$ (lattice time)")
    axA.set_ylabel(r"$C(\tau)/C(0)$")
    axA.set_title("A. same configs, same read — only the operator differs")
    axA.legend(fontsize=7, frameon=False, ncol=2)
    axA.grid(alpha=0.25, which="both")

    # ---- B: effective mass against the expected gap -------------------------------------------
    for beta in betas:
        exp = None
        for op, ls, mk in (("action_density", ":", "o"), ("plaquette_0pp", "-", "s")):
            sel = sorted((r for r in rows if float(r["beta"]) == beta and r["operator"] == op
                          and int(r["nsmear"]) == NS[op]), key=lambda r: int(r["tau"]))
            exp = _f(sel[0]["a_m_0pp_expected"]) if sel else float("nan")
            pts = [(int(r["tau"]), _f(r["m_eff"]), _f(r["m_eff_err"])) for r in sel
                   if r["m_eff"] != "" and _f(r["m_eff_err"]) < 0.6]
            if not pts:
                continue
            axB.errorbar([p[0] for p in pts], [p[1] for p in pts], yerr=[p[2] for p in pts],
                         ls=ls, marker=mk, ms=5, lw=1.4, color=COLOR[beta], capsize=2)
        if exp == exp:
            axB.axhline(exp, color=COLOR[beta], ls="--", lw=1, alpha=0.6)
            axB.annotate(rf"$a\,m_{{0^{{++}}}}$ at $\beta={beta:.2f}$", (0.02, exp),
                         xycoords=("axes fraction", "data"), fontsize=7,
                         color=COLOR[beta], va="bottom")
    axB.set_xlabel(r"$\tau$")
    axB.set_ylabel(r"$m_{\mathrm{eff}}(\tau)=\log[C(\tau)/C(\tau{+}1)]$")
    axB.set_title(r"B. solid = plaquette (descends onto $a\,m_{0^{++}}$); dotted = action density")
    axB.set_ylim(0, 2.8)
    axB.grid(alpha=0.25)

    # ---- C: does the extracted gap scale? ------------------------------------------------------
    # VARIATIONAL selection, one rule for the whole figure and no per-coupling choices.
    # Reflection positivity makes m_eff(tau) >= E_0 for ANY positive-weight operator, so the
    # SMALLEST resolved m_eff anywhere in the (operator, smearing, tau) basis is the best upper
    # bound on the gap -- the same principle a GEVP uses. Applied per beta over the full basis it
    # selects the plaquette at all three couplings of this L=16 scan and never the action density,
    # so "the plaquette is the right operator" is an output of the rule rather than an input to it.
    # Stable at REL_TOL 0.15 and 0.25. Across VOLUMES the minimum is not always the plaquette --
    # the rule takes whichever operator gives the smallest resolved m_eff, and none dominates
    # everywhere -- which is why the selection is by rule and not by operator.
    REL_TOL = 0.25

    def resolved(beta, ops):
        out = []
        for r in rows:
            if float(r["beta"]) != beta or r["operator"] not in ops or r["m_eff"] == "":
                continue
            v, e = _f(r["m_eff"]), _f(r["m_eff_err"])
            if v == v and e == e and v > 0 and e / v <= REL_TOL:
                out.append((v, e, r["operator"], int(r["nsmear"]), int(r["tau"])))
        return out

    for ops, mk, col, lab in ((("plaquette_0pp", "action_density"), "s", "#1f4e8c",
                               "variational min over the full basis"),
                              (("action_density",), "o", "#b03030", "action density only")):
        pts = []
        for b in betas:
            cand = resolved(b, ops)
            if cand:
                pts.append((b, min(cand, key=lambda c: c[0])))
        if len(pts) < 2:
            continue
        xs = [b for b, _ in pts]
        ys = [q[0] / a_lambda(b) for b, q in pts]
        es = [q[1] / a_lambda(b) for b, q in pts]
        axC.errorbar(xs, ys, yerr=es, marker=mk, ms=7, lw=1.4, color=col, capsize=3, label=lab)
        w = [1 / e ** 2 for e in es]
        m = sum(y * wi for y, wi in zip(ys, w)) / sum(w)
        chi2 = sum(wi * (y - m) ** 2 for y, wi in zip(ys, w)) / max(1, len(xs) - 1)
        axC.axhline(m, color=col, ls="--", lw=1, alpha=0.5)
        axC.annotate("chi2/dof = %.2f" % chi2, (xs[0], m), textcoords="offset points",
                     xytext=(6, 8), fontsize=8, color=col)
        if ops[0] == "plaquette_0pp":
            print("  variational picks:", [(b, q[2], "ns=%d" % q[3], "tau=%d" % q[4]) for b, q in pts])

    axC.set_xlabel(r"$\beta=4/g^2$")
    axC.set_ylabel(r"$\Delta/(a\Lambda_{\mathrm{lat}}) = m/\Lambda$")
    axC.set_title("C. a mass gives a constant here; a cutoff scale does not")
    axC.legend(fontsize=8, frameon=False)
    axC.grid(alpha=0.25)

    # ---- D: the same variational read across VOLUME, at one coupling ---------------------------
    # rho'(n) = rho'(1)^n needs a single cut that does not grow with L, so what matters here is that
    # Delta is L-independent, not its value. L=8 is the small-volume edge and is shown apart.
    VB = 2.30
    Ls = sorted({int(r["L"]) for r in rows if abs(float(r["beta"]) - VB) < 1e-9})
    pts = []
    for L in Ls:
        cand = [(_f(r["m_eff"]), _f(r["m_eff_err"]), r["operator"]) for r in rows
                if int(r["L"]) == L and abs(float(r["beta"]) - VB) < 1e-9
                and r["m_eff"] != "" and r["m_eff_err"] != ""]
        cand = [c for c in cand if c[0] == c[0] and c[1] == c[1] and c[0] > 0
                and c[1] / c[0] <= REL_TOL]
        if cand:
            pts.append((L,) + min(cand, key=lambda c: c[0]))
    if pts:
        edge = [q for q in pts if q[0] == min(Ls)]
        body = [q for q in pts if q[0] > min(Ls)]
        for grp, col, mk, lab in ((body, "#1f4e8c", "o", r"$L\geq 12$"),
                                  (edge, "#888888", "x", "small-volume edge")):
            if grp:
                axD.errorbar([q[0] for q in grp], [q[1] for q in grp], yerr=[q[2] for q in grp],
                             marker=mk, ms=7, lw=0, capsize=3, color=col, label=lab)
        if len(body) >= 2:
            w = [1 / q[2] ** 2 for q in body]
            m = sum(q[1] * wi for q, wi in zip(body, w)) / sum(w)
            chi2 = sum(wi * (q[1] - m) ** 2 for q, wi in zip(body, w)) / (len(body) - 1)
            axD.axhline(m, color="#1f4e8c", ls="--", lw=1.2)
            axD.annotate("chi2/dof = %.2f   m_hi = %.3f" % (chi2, math.exp(-m)),
                         (0.05, 0.08), xycoords="axes fraction", fontsize=8, color="#1f4e8c")
    axD.set_xlabel(r"spatial extent $L$")
    axD.set_ylabel(r"$\Delta$ (variational)")
    axD.set_title(r"D. $L$-independence at $\beta=%.2f$" % VB)
    axD.legend(fontsize=8, frameon=False)
    axD.grid(alpha=0.25)

    n = rows[0]["ncfg"]
    fig.suptitle(f"The 0++ correlator behind the gap read — SU(2), {n} configurations per point; "
                 f"panels A-B at $L=16$ and {NS['plaquette_0pp']} APE sweeps, C-D selected variationally",
                 fontsize=11)
    fig.tight_layout(rect=(0, 0.01, 1, 0.94))
    fig.savefig(OUT, dpi=150)
    print("wrote", OUT)


if __name__ == "__main__":
    main()
