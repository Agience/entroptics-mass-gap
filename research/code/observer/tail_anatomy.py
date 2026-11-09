"""What are the high-energy cubes? Anatomy of the top of the observer's cube-energy distribution.

Lean observer step (observer_step.step, c = 0.15; n = 8 at beta 2.30, 31 at beta 2.50) on chains 2 and 6 of
shards links_007 and links_027 of each 32^4 campaign. The site energy is e summed over the six planes, and
cubes of side b sites (3 at beta 2.30, 6 at beta 2.50) tile the lattice. For each cube: its energy, the share
carried by its hottest site (1/b^4 for a uniform lump, near 1 for a point defect), and the number of sites
with some plane at 1 - (1/2) tr P > 1. Prints the 20 highest cubes over the four configurations against the
median share over all cubes, the uniform share, and the fraction of all cubes holding a negative plaquette.

    python tail_anatomy.py ENS_ROOT
"""
import json
import os
import sys

import numpy as np

from cap_test import bg, oneminus
import observer_step as O

# CHOSEN: c = 0.15 < 1/6, the continuous observer step every Lean-step read used
C = 0.15
root = O.opt(1, "ens", str)
for bb, n, b in [("2.30", 8, 3), ("2.50", 31, 6)]:  # NOT A READ: the two spacings
    out = []
    for sh in ["links_007.npy", "links_027.npy"]:  # NOT A READ: two shards
        Q = np.load(os.path.join(root, f"su2_L32_b{bb}", sh), mmap_mode="r")
        for ch in (2, 6):  # NOT A READ: two chains
            q = np.asarray(Q[ch], dtype=np.float64)
            for _ in range(n):
                q = O.step(bg, q, C)
            e = oneminus(q)
            site = e.sum(0)
            L = site.shape[0]
            m = L // b
            s = site[:m * b, :m * b, :m * b, :m * b].reshape(m, b, m, b, m, b, m, b)
            cube = s.sum(axis=(1, 3, 5, 7)).ravel()
            smax = s.max(axis=(1, 3, 5, 7)).ravel()
            # DERIVED: 1 - (1/2) tr P > 1 exactly when (1/2) tr P < 0, a negative plaquette
            neg = (e.max(0) > 1)[:m * b, :m * b, :m * b, :m * b].reshape(m, b, m, b, m, b, m, b).sum(axis=(1, 3, 5, 7)).ravel()
            out.append(np.stack([cube, smax / cube, neg]))
    A = np.concatenate(out, axis=1)
    order = np.argsort(A[0])[::-1]
    top = A[:, order[:20]]
    # DERIVED: a cube holding at least one negative plaquette
    frac_with_neg = float((A[2] > 0).mean())
    print(json.dumps({"beta": bb, "b": b, "uniform_share": 1 / b ** 4, "all_median_share": float(np.median(A[1])),
                      "top20_cube": np.round(top[0], 2).tolist(), "top20_share": np.round(top[1], 4).tolist(),
                      "top20_neg_sites": top[2].astype(int).tolist(),
                      "all_frac_with_neg": frac_with_neg}), flush=True)
