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
  B  compact-U(1) K_signal(beta) on 8^3x16 (8x8 planes, su2 b0.50 floor pinned at 8x8), with its
     within-plane-shuffled control on the same configurations, beside the literature Wilson-action
     transition beta_c ~ 1.011.
  C  K_signal minus its within-plane-shuffled read (paired per configuration) for compact U(1) and
     SU(2) on 8^3x16, beside the literature confinement picture (pure SU(N) confines at every
     coupling, compact U(1) deconfines; Greensite 2003). The shuffle keeps each plane's one-point
     marginal and removes its arrangement, so this panel is the part of K_signal carried by spatial
     arrangement. SU(3) is not drawn: its planes are 6x6 and the store holds no confined-vacuum
     reference at that shape (see 8_3_regen_su3_from_store.py).

Loads the regenerated Sec 8.3 CSV 8_3_dat_nobump.csv and the free-scalar calibration artifact
8_5_dat_gap_calibration.csv; it computes no read itself.

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
    """Panel A: the free-scalar calibration, READ FROM the artifact that measures it.

    WHY NOT RECOMPUTED HERE. It used to be. Two scripts computed the same measurement from the same
    seeds and the suite had to assert that they agreed value for value -- a correspondence that can
    only ever be maintained by hand, and that silently states the same number twice as if it were
    two. The calibration belongs to 8_5_run_gap_calibration.py; this panel summarises it. Reading
    the artifact makes the agreement structural instead of asserted, and carries across the part
    the recomputation dropped: the reseeding spread, which is the only uncertainty either script
    measures.

    Returns (m, E0, read, spread) per mass, in the artifact's order.
    """
    path = os.path.join(_HERE, "8_5_dat_gap_calibration.csv")
    rows = []
    print("Panel A -- free-scalar gap (from 8_5_dat_gap_calibration.csv):")
    with open(path, newline="", encoding="utf-8-sig") as f:
        for r in csv.DictReader(f):
            m, e0 = float(r["m"]), float(r["E0"])
            read, spread = float(r["mass_gap"]), float(r["spread"])
            rows.append((m, e0, read, spread))
            print(f"  m={m:4.2f}  E0={e0:.4f}  read={read:.4f}  spread={spread:.4f} "
                  f"({100 * spread / e0:.1f}% of E0)")
    if not rows:
        raise SystemExit(f"{path} carries no rows; run 8_5_run_gap_calibration.py --mode full first")
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
    nb = _load("8_3_dat_nobump.csv", ["beta", "confinement", "confinement_err",
                                      "confinement_shuffled", "confinement_shuffled_err",
                                      "confinement_minus_shuffled", "confinement_minus_shuffled_err"])

    fig, (aA, aC, aD) = plt.subplots(1, 3, figsize=(17.0, 5.0))
    ENT, EST = "#1f4e8c", "#7a3a8a"     # Entroptics blue, Established purple

    # -- A: free-scalar gap, Entroptics read vs exact E0 --------------------------------
    m = np.array([r[0] for r in fs]); e0 = np.array([r[1] for r in fs]); rd = np.array([r[2] for r in fs])
    sp = np.array([r[3] for r in fs])
    mm = np.linspace(m.min() * 0.9, m.max() * 1.05, 200)
    aA.plot(mm, np.arccosh(1 + mm * mm / 2), color="#555", lw=1.8, label=r"Exact: $E_0=\mathrm{arccosh}(1+m^2/2)$")
    # DERIVED: the bar is the reseeding spread the calibration measured, drawn half either side of
    # the block mean so the bar's full extent is the spread itself. Nothing is scaled or chosen.
    aA.errorbar(m, rd, yerr=sp / 2, fmt="o", color=ENT, ms=8, capsize=3,
                label=r"Entroptics: dominant DMD-rate read (bars: reseeding spread)")
    for mi, e, s in zip(m, e0, sp):
        aA.annotate(f"±{50 * s / e:.0f}%", (mi, e), textcoords="offset points",
                    xytext=(6, -12), fontsize=8, color=ENT)
    aA.set_xlabel(r"free-scalar mass $m$ (lattice units)"); aA.set_ylabel(r"mass gap")
    aA.set_title(r"A  free-scalar gap: read vs exact $E_0$  ($8^2\times64$)")
    aA.legend(fontsize=9, loc="upper left")

    # -- B: compact-U(1) K_signal and its within-plane-shuffled control, beside beta_c ---------
    if "u1" in nb:
        u = nb["u1"]
        aC.errorbar(u["beta"], u["confinement"], yerr=u["confinement_err"], marker="o",
                    color="#b03030", lw=1.8, capsize=3, label=r"U(1) $K_{\mathrm{signal}}$")
        aC.errorbar(u["beta"], u["confinement_shuffled"], yerr=u["confinement_shuffled_err"],
                    marker="o", mfc="none", ls="--", color="#b03030", lw=1.2, capsize=2,
                    label=r"U(1) $K_{\mathrm{signal}}$, within-plane shuffled")
        aC.axvline(BETA_C, color="#555", ls="--", lw=1.3,
                   label=rf"literature: $\beta_c\approx{BETA_C:.3f}$")
        aC.legend(fontsize=9, loc="best")
    aC.set_xlabel(r"$\beta$"); aC.set_ylabel(r"$K_{\mathrm{signal}}$ (plane mean)")
    aC.set_title(r"B  compact U(1) $K_{\mathrm{signal}}$ and shuffled control ($8^3\times16$, 8$\times$8 planes)",
                 fontsize=10)

    # -- C: K_signal minus its shuffled read, compact U(1) and SU(2) ---------------------------
    for g, color, marker, name in (("u1", "#b03030", "s", "compact U(1)"),
                                   ("su2", ENT, "o", "SU(2)")):
        if g in nb:
            s = nb[g]
            aD.errorbar(s["beta"], s["confinement_minus_shuffled"],
                        yerr=s["confinement_minus_shuffled_err"], marker=marker, color=color,
                        lw=1.6, capsize=3, label=rf"{name} ($8^3\times16$)")
    aD.axhline(0.0, color="#444", lw=0.8)
    aD.axvline(BETA_C, color="#888", ls="--", lw=1.1, alpha=0.7,
               label=r"literature: U(1) $\beta_c$")
    aD.axvline(2.2, color=ENT, ls=":", lw=1.1, alpha=0.7,
               label=r"literature: SU(2) bulk crossover $\approx2.2$")
    aD.set_xlabel(r"$\beta$")
    aD.set_ylabel(r"$K_{\mathrm{signal}} - K_{\mathrm{signal}}^{\mathrm{shuffled}}$ (paired)")
    aD.set_title(r"C  $K_{\mathrm{signal}}$ minus within-plane-shuffled read, U(1) and SU(2)",
                 fontsize=10)
    aD.legend(fontsize=8.5, loc="best")

    fig.suptitle("Entroptics reads beside literature values: free-scalar gap (A); K_signal and its "
                 "same-marginal control on $8^3\\times16$ (B, C)", fontsize=12.5, y=0.995)
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
        for mi, e0i, rdi, spi in fs:
            # The uncertainty column is the calibration's own reseeding spread -- the reason this
            # panel reads the artifact rather than recomputing it.
            w.writerow(["A", f"free-scalar gap m={mi}", f"{rdi:.4f}", f"{e0i:.4f}", f"{spi:.4f}",
                        "exact E0=arccosh(1+m^2/2)"])
        w.writerow(["B", "U(1) transition beta_c",
                    "K_signal(beta) and within-plane-shuffled control, 8x8 planes (8_3_dat_nobump.csv)",
                    f"{BETA_C}", "-", BETA_C_SRC])
        w.writerow(["C", "U(1) and SU(2) K_signal minus shuffled",
                    "paired difference per coupling, 8x8 planes (8_3_dat_nobump.csv)",
                    "SU(N) confined at all beta; U(1) deconfines above beta_c", "-", CONFINE_SRC])
    print(f"wrote {FIG}\nwrote {DAT}")


if __name__ == "__main__":
    main()
