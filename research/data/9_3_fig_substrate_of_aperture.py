"""Figure for Sec 9's aperture scan: the hypothesis, its retired predecessor, and its consequence.

Three panels, one per prediction, all from 9_3_dat_substrate_of_aperture.csv -- no ensemble is read
here, so the figure cannot disagree with the table the paper quotes.

  LEFT   the theorem's quantity, <d^2> on the circle, against aperture. The hypothesis predicts it
         saturates; a constant B fitted by inverse variance is drawn through it.
  MIDDLE the RETIRED quantity, the raw lag index over the full extent, on the same ensembles, with
         an L^2 reference anchored at the smallest aperture. This is why the hypothesis had to be
         restated: no B bounds it.
  RIGHT  the coefficient the growth condition requires, c = <d^2>/(N+1)^2, against the derived
         ceiling c_max. The margin GROWS with the aperture, so the binding constraint is the
         smallest window.

DERIVED: every reference curve is anchored at the SMALLEST aperture plotted, so it is a prediction
for the larger ones rather than a fit through them. `c_max` is the growth condition solved for c.
The apertures and couplings are whatever the artifact holds.
"""
import csv
import math
import os
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
DAT = os.path.join(HERE, "9_3_dat_substrate_of_aperture.csv")

sys.path.insert(0, os.path.join(HERE, "..", "code", "certify"))
from aperture_ceiling import C_MAX   # the ceiling, derived in ONE place, and SHARP

if not os.path.exists(DAT):
    raise SystemExit(f"9_3_fig_substrate_of_aperture: {os.path.basename(DAT)} is not present. Run\n"
                     f"  code/certify/ym_substrate_bound_of_aperture.py\nfirst; this figure reads "
                     f"that artifact and invents nothing.")

rows = list(csv.DictReader(open(DAT, newline="")))
for r in rows:
    for k in ("d2_circle", "d2_sigma", "d2_raw", "mu"):
        r[k] = float(r[k])
    r["L"] = int(r["L"])

# DERIVED: the artifact's own signal criterion -- mu <= 0 is a read on noise, with no tension and a
# moment that is a ratio of two quantities consistent with zero.
sig = [r for r in rows if r["mu"] > 0]
if not sig:
    raise SystemExit("9_3_fig_substrate_of_aperture: no row carries a tension to read.")

groups = {}
for r in sig:
    groups.setdefault((r["group"], r["beta"]), []).append(r)
# DERIVED: one is the arity below which a coupling has no aperture DEPENDENCE to draw.
groups = {k: sorted(v, key=lambda r: r["L"]) for k, v in groups.items() if len(v) > 1}

# the coupling with the most apertures leads; it is the one the paper tabulates
lead = max(groups, key=lambda k: len(groups[k]))

plt.rcParams.update({"font.size": 10, "font.family": "DejaVu Sans", "axes.linewidth": 0.8})
fig, axes = plt.subplots(1, 3, figsize=(13.4, 4.3))
ACC, MUT, BAD, OK = "#2b6cb0", "#a0aec0", "#c53030", "#2f855a"

for key, v in sorted(groups.items()):
    L = np.array([r["L"] for r in v], float)
    lead_one = key == lead
    style = dict(color=ACC if lead_one else MUT, lw=1.6 if lead_one else 0.9,
                 zorder=3 if lead_one else 1, alpha=1.0 if lead_one else 0.55,
                 marker="o" if lead_one else ".", ms=5 if lead_one else 3)
    lab = rf"${key[0].upper()}$ $\beta{{=}}{key[1]}$" if lead_one else None

    axes[0].errorbar(L, [r["d2_circle"] for r in v],
                     yerr=[2 * r["d2_sigma"] for r in v], capsize=2, label=lab, **style)
    axes[1].plot(L, [r["d2_raw"] for r in v], label=lab, **style)
    axes[2].plot(L, [r["d2_circle"] / r["L"] ** 2 for r in v], label=lab, **style)

lv = groups[lead]
L0 = lv[0]["L"]

# LEFT: the constant the lead coupling's own reproducibility supports
w = np.array([1.0 / r["d2_sigma"] ** 2 for r in lv])
B = float((w * np.array([r["d2_circle"] for r in lv])).sum() / w.sum())
axes[0].axhline(B, color=OK, ls="--", lw=1.3, zorder=2)
axes[0].text(lv[-1]["L"], B * 1.06, rf"constant $B={B:.3f}$", color=OK, fontsize=9,
             ha="right", va="bottom")
axes[0].set_ylabel(r"$\langle d^2\rangle$  (circle distance, full extent)")
axes[0].set_title("the theorem's quantity: saturates", fontsize=10.5)
axes[0].set_ylim(0, max(r["d2_circle"] for r in sig) * 1.45)

# MIDDLE: the L^2 reference anchored at the smallest aperture, NOT fitted
raw0 = lv[0]["d2_raw"]
Lg = np.linspace(L0, lv[-1]["L"], 60)
axes[1].plot(Lg, raw0 * (Lg / L0) ** 2, color=BAD, ls=":", lw=1.5, zorder=2)
axes[1].text(lv[-1]["L"], raw0 * (lv[-1]["L"] / L0) ** 2 * 0.62,
             rf"$L^2$ anchored at $L{{=}}{L0}$", color=BAD, fontsize=9, ha="right", va="top")
axes[1].set_ylabel(r"$\langle d^2\rangle$  (raw index, full extent)")
axes[1].set_title("the retired quantity: unbounded", fontsize=10.5)
axes[1].set_yscale("log")

# RIGHT: the coefficient against its derived ceiling
axes[2].axhline(C_MAX, color=BAD, ls="--", lw=1.4, zorder=2)
axes[2].text(lv[-1]["L"], C_MAX * 1.12, rf"ceiling $c_{{\max}}={C_MAX:.4f}$", color=BAD,
             fontsize=9, ha="right", va="bottom")
cw = max(r["d2_circle"] / r["L"] ** 2 for r in sig)
axes[2].axhline(cw, color=OK, ls="-.", lw=1.2, zorder=2)
axes[2].text(lv[0]["L"], cw * 0.82, rf"one $c={cw:.1e}$ covers every aperture", color=OK,
             fontsize=9, ha="left", va="top")
axes[2].set_ylabel(r"required $c=\langle d^2\rangle/(N{+}1)^2$")
axes[2].set_title(r"the growth condition: margin widens as $1/L^2$", fontsize=10.5)
axes[2].set_yscale("log")

for ax in axes:
    ax.set_xlabel(r"aperture  $L$  (lag arity $N{+}1$)")
    ax.grid(True, alpha=0.15, lw=0.6)
    ax.legend(loc="best", frameon=False, fontsize=9)
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)

fig.suptitle(r"The substrate hypothesis across apertures — $L=6\ldots32$, "
             rf"{len(groups)} couplings at more than one aperture", fontsize=11.5, y=1.00)
fig.tight_layout()
out = os.path.join(HERE, "9_3_fig_substrate_of_aperture.png")
fig.savefig(out, dpi=150, bbox_inches="tight")
print(f"wrote {os.path.basename(out)}  "
      f"({len(groups)} couplings, apertures {sorted({r['L'] for r in sig})})")
