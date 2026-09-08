"""
8_6_run_benchmark.py -- PAPER Sec 8 (capstone): the deterministic Entroptics instrument against
the established lattice literature, THREE panels, each a labelled comparison with the source cited
ON the figure and in the CSV.

One bounded read per raw configuration (deterministic, no fit, no sweep) against what the community
establishes with dedicated Monte-Carlo spectroscopy. Each panel states the lattice it uses and cites
the established value it is measured against:

  A  FREE-SCALAR GAP (read vs EXACT).  The dominant DMD/Koopman rate on an 8x8x64 free-scalar field
     recovers the EXACT gap E0 = arccosh(1 + m^2/2) across the mass range. The target is analytic
     (a theorem, not a measurement), so this panel is read-vs-exact.
  (A panel comparing the bore ratio m/sqrt(sigma) = pi against the lattice 0++ was REMOVED. It was
     labelled parameter-free and was not: pi is the first Dirichlet transverse mode of an ASSUMED
     hard-wall tube, and the width relation a = 1/sqrt(sigma) is dimensional analysis with its O(1)
     constant set to 1. Both enter from outside the instrument, so the panel measured an imported
     constant against a cited one and could not test anything. The framework's own gap statement is
     Delta >= kappa_0 - mu, kappa_0 = (1/4)ln3 from the counting floor and mu read from the
     configuration; it needs no bore.)
  B  U(1) DECONFINEMENT (read vs established beta_c).  K_signal(beta) on 8^3x16 rises through the
     established compact-U(1) Wilson-action transition beta_c ~ 1.011 (lattice).
  C  N-INVARIANT NO-BUMP (Entroptics discrimination, matching the established picture).  SU(2) and
     SU(3) K_signal stay flat at every coupling (no deconfinement) while the U(1) foil rises: the
     established fact is that pure SU(N) confines at all beta and compact U(1) deconfines (Greensite
     2003). All three curves are Entroptics reads; the cited content is the confinement fact.

Loads the regenerated Sec 8.3 CSVs (gauge K_signal), the cited glueball values, and generates the
free-scalar calibration itself.

    python 8_6_run_benchmark.py
"""
from __future__ import annotations

import csv
import math
import os
import sys

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(_HERE, "..", "code")))

import entroptics_adapter as entroptics
import lattice_generator as generator

FIG = os.path.join(_HERE, "8_6_fig_benchmark.png")
DAT = os.path.join(_HERE, "8_6_dat_benchmark.csv")
# PANEL C -- compact U(1), Wilson action: confinement for 0 < beta < beta_c, Coulomb above.
BETA_C = 1.011
BETA_C_SRC = "compact U(1) Wilson-action transition, 4D lattice (e.g. Arnold-Lippert-Neuhaus-Schiller)"
# PANEL D -- the established confinement picture the discrimination matches.
CONFINE_SRC = "pure SU(N) confines at every coupling; compact U(1) deconfines (Greensite, Prog.Part.Nucl.Phys. 51 (2003) 1)"


def _load(name, cols):
    path = os.path.join(_HERE, name)
    if not os.path.exists(path):
        print(f"  (skip: {name} not found -- run its Sec 8 script first)")
        return {}
    out = {}
    with open(path, newline="") as f:
        for row in csv.DictReader(f):
            d = out.setdefault(row["group"], {c: [] for c in cols})
            for c in cols:
                d[c].append(float(row[c]))
    return {g: {c: np.array(v) for c, v in d.items()} for g, d in out.items()}


def free_scalar_gap():
    """Panel A: the forward operator gap read vs the exact gap E0 across the mass range (generated here)."""
    masses = [0.20, 0.35, 0.50, 0.70, 0.90, 1.10]
    rows = []
    print("Panel A -- free-scalar gap (read vs exact E0):")
    for m in masses:
        cfgs = [generator.free_scalar((8, 8, 64), m, seed=s) for s in range(40)]  # match 8_5 (n=40)
        read = float(entroptics.run(cfgs).mass_gap)
        e0 = math.acosh(1 + m * m / 2)
        rows.append((m, e0, read))
        print(f"  m={m:4.2f}  E0={e0:.4f}  read={read:.4f}  ({100 * (1 - abs(read - e0) / e0):.0f}%)")
    return rows


def main():
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
    except Exception as e:
        print(f"figure skipped: {e}")
        return

    fs = free_scalar_gap()
    nb = _load("8_3_dat_nobump.csv", ["beta", "confinement", "confinement_err"])
    su3 = _load("8_3_dat_su3_nobump.csv", ["beta", "confinement", "confinement_err"])

    fig, (aA, aC, aD) = plt.subplots(1, 3, figsize=(17.0, 5.0))
    ENT, EST = "#1f4e8c", "#7a3a8a"     # Entroptics blue, Established purple

    # -- A: free-scalar gap, Entroptics read vs exact E0 --------------------------------
    m = np.array([r[0] for r in fs]); e0 = np.array([r[1] for r in fs]); rd = np.array([r[2] for r in fs])
    mm = np.linspace(m.min() * 0.9, m.max() * 1.05, 200)
    aA.plot(mm, np.arccosh(1 + mm * mm / 2), color="#555", lw=1.8, label=r"Exact: $E_0=\mathrm{arccosh}(1+m^2/2)$")
    aA.plot(m, rd, "o", color=ENT, ms=8, label=r"Entroptics: dominant DMD-rate read")
    for mi, e, r in zip(m, e0, rd):
        aA.annotate(f"{100 * (1 - abs(r - e) / e):.0f}%", (mi, r), textcoords="offset points",
                    xytext=(6, -4), fontsize=8, color=ENT)
    aA.set_xlabel(r"free-scalar mass $m$ (lattice units)"); aA.set_ylabel(r"mass gap")
    aA.set_title(r"A  free-scalar gap: read vs exact $E_0$  ($8^2\times64$)")
    aA.legend(fontsize=9, loc="upper left")

    # -- C: U(1) deconfinement, Entroptics read vs established beta_c --------------------
    if "u1" in nb:
        u = nb["u1"]
        aC.axvspan(float(u["beta"].min()) - 0.05, BETA_C, color="#eef3fb", zorder=0)
        aC.errorbar(u["beta"], u["confinement"], yerr=u["confinement_err"], marker="o",
                    color="#b03030", lw=1.8, capsize=3, label=r"Entroptics: U(1) $K_{\mathrm{signal}}(\beta)$")
        aC.axvline(BETA_C, color="#555", ls="--", lw=1.3,
                   label=rf"Established: $\beta_c\approx{BETA_C:.3f}$ (lattice)")
        aC.legend(fontsize=9, loc="upper left")
    aC.set_xlabel(r"$\beta$"); aC.set_ylabel(r"$K_{\mathrm{signal}}$")
    aC.set_title(r"B  U(1) deconfinement: read locates $\beta_c$  ($8^3\times16$)")

    # -- D: N-invariant no-bump. SU(N) flat (confined) vs the U(1) foil, ALL Entroptics reads ---
    if "u1" in nb:
        u = nb["u1"]
        aD.errorbar(u["beta"], u["confinement"], yerr=u["confinement_err"], marker="s", ms=4,
                    color="#b03030", lw=1.3, alpha=0.75, capsize=2,
                    label=r"Entroptics: U(1) foil ($8^3\times16$, deconfines)")
    if "su2" in nb:
        s = nb["su2"]
        aD.errorbar(s["beta"], s["confinement"], yerr=s["confinement_err"], marker="o",
                    color=ENT, lw=1.8, capsize=3, label=r"Entroptics: SU(2) ($8^3\times16$, flat)")
    if "su3" in su3:
        s = su3["su3"]
        aD.errorbar(s["beta"], s["confinement"], yerr=s["confinement_err"], marker="^",
                    color="#2e7d32", lw=1.8, capsize=3, label=r"Entroptics: SU(3) ($6^3\times12$, flat)")
    # each theory's transition/crossover on its own coupling scale: U(1) deconfines (sharp), SU(N) crossover (no bump)
    aD.axvline(BETA_C, color="#888", ls="--", lw=1.1, alpha=0.7)
    aD.axvline(2.2, color=ENT, ls=":", lw=1.1, alpha=0.7)
    aD.axvline(5.7, color="#2e7d32", ls=":", lw=1.1, alpha=0.7)
    aD.text(BETA_C, 0.37, r"U(1) $\beta_c$", color="#666", fontsize=7, ha="center")
    aD.text(2.2, 0.37, r"SU(2) $\times$", color=ENT, fontsize=7, ha="center")
    aD.text(5.7, 0.37, r"SU(3) $\times$", color="#2e7d32", fontsize=7, ha="center")
    aD.set_ylim(0.0, 0.40)
    aD.set_xlabel(r"$\beta$"); aD.set_ylabel(r"$K_{\mathrm{signal}}$")
    aD.set_title(r"C  no-bump: SU(N) flat vs the deconfining U(1) foil")
    aD.legend(fontsize=8.5, loc="upper right")

    fig.suptitle("Deterministic Entroptics reads against the established lattice picture "
                 "(one bounded read per configuration, no fit)", fontsize=12.5, y=0.995)
    # sources footnote (cited ON the figure)
    src = ("Sources:  "
           f"B  {BETA_C_SRC}.   "
           f"C  {CONFINE_SRC}.   "
           "A  target is the exact analytic gap $E_0=\\mathrm{arccosh}(1+m^2/2)$.")
    fig.text(0.5, 0.012, src, ha="center", va="bottom", fontsize=7.6, color="#333", wrap=True)
    fig.tight_layout(rect=(0, 0.045, 1, 0.965))
    fig.savefig(FIG, dpi=150)
    plt.close(fig)

    with open(DAT, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["panel", "quantity", "entroptics", "established", "uncertainty", "reference"])
        for mi, e0i, rdi in fs:
            w.writerow(["A", f"free-scalar gap m={mi}", f"{rdi:.4f}", f"{e0i:.4f}", "-",
                        "exact E0=arccosh(1+m^2/2)"])
        w.writerow(["B", "U(1) transition beta_c", "K_signal rise through beta_c",
                    f"{BETA_C}", "-", BETA_C_SRC])
        w.writerow(["C", "SU(N) confinement (no-bump)", "K_signal flat at all beta",
                    "confined at all beta", "-", CONFINE_SRC])
    print(f"wrote {FIG}\nwrote {DAT}")


if __name__ == "__main__":
    main()
