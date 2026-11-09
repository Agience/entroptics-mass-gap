"""The joint near row on compact U(1): the Perron root of the 2 x 2 block matrix of coarse links and cell energies.

Reads the committed per-read files in research/data/observer/u1/joint/ (copied unchanged from
the campaign's output; 24^4, observer step n = 8, eight chains per coupling) and runs no simulation.
For each coupling beta (0.8 confined, 1.2 Coulomb) and cell side b (4, 6, 8) the joint view's near row has four
blocks:

    links on links       A = a_*.json  row_xfit                (u1_coarse_read.py, total variation, cross-fit)
    links from energies  B = x_*.json  b_links_from_energy     (u1_joint_cross.py)
    energies from links  C = |x_*.json c_energy_from_links|    (u1_joint_cross.py)
    energies on energies D = d_*.json  reads.nn.inf xfit max   (cellview_w1.py, W1, near set, untruncated window,
                                                                cross-fit worst neighbourhood)

and the joint condition is the Perron root rho of [[A, B], [C, D]] below one. B C is the only place the two
off-diagonal blocks enter the root, so their units cancel. The same root with the plug-in suprema
(row_sup for A, the `upper` read for D) is recorded beside it as `rho_sup`; the plug-in supremum over realized
neighbourhoods reads high on finite samples, which is why the cross-fit is the primary read.

    python aggregate_u1_joint.py [OUT.json]     (default research/data/observer/u1/joint/joint_rho.json)
"""
import json
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
JOINT = os.path.normpath(os.path.join(HERE, "..", "..", "data", "observer", "u1", "joint"))
# DERIVED: the two couplings of the committed U(1) campaign (file names a_b{beta}_*), confined then Coulomb
BETAS = ("0.8", "1.2")
# DERIVED: the three cell sides of the committed reads (file names *_b{side}.json)
SIDES = (4, 6, 8)


def perron(M):
    """The largest real eigenvalue of a non-negative matrix (Perron-Frobenius)."""
    return float(max(np.linalg.eigvals(M).real))


def read(beta, side):
    def load(prefix):
        with open(os.path.join(JOINT, f"{prefix}_b{beta}_b{side}.json"), encoding="utf-8") as f:
            return json.load(f)

    a, x, d = load("a"), load("x"), load("d")
    near = d["reads"]["nn"]["inf"]["summary"]
    A, B, C = a["row_xfit"], x["b_links_from_energy"], abs(x["c_energy_from_links"])
    D = near["xfit"]["max"]
    A_sup, D_sup = a["row_sup"], near["upper"]["max"]
    return {"beta": float(beta), "side": side,
            "links_on_links": A, "links_from_energies": B, "energies_from_links": C, "energies_on_energies": D,
            "rho": perron(np.array([[A, B], [C, D]])),
            "links_on_links_sup": A_sup, "energies_on_energies_sup": D_sup,
            "rho_sup": perron(np.array([[A_sup, B], [C, D_sup]]))}


if __name__ == "__main__":
    # DERIVED: 1, argv[0] is the script, so one extra argument names the output
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(JOINT, "joint_rho.json")
    rows = [read(b, s) for b in BETAS for s in SIDES]
    res = {"producer": "research/code/observer/aggregate_u1_joint.py",
           "inputs": sorted(f for f in os.listdir(JOINT) if f.startswith(("a_", "x_", "d_"))),
           "rows": rows,
           "rho_max_by_beta": {b: max(r["rho"] for r in rows if r["beta"] == float(b)) for b in BETAS},
           "rho_min_by_beta": {b: min(r["rho"] for r in rows if r["beta"] == float(b)) for b in BETAS}}
    with open(out, "w", encoding="utf-8") as f:
        json.dump(res, f, indent=1)
    for r in rows:
        print(f"beta {r['beta']}  side {r['side']}  links on links {r['links_on_links']:.3f}"
              f"  energies on energies {r['energies_on_energies']:.3f}  rho {r['rho']:.3f}  (plug-in sup {r['rho_sup']:.3f})")
