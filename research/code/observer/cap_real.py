"""The observer's energy density on real configurations: mean, maximum and negative-plaquette fraction.

For one shard (links_020) of the 32^4 campaigns at beta 2.30 and 2.50, chains 0 and 4, this applies n steps of
the Lean observer step (observer_step.step, c = 0.15; n = 8 at beta 2.30, 30 at beta 2.50, n proportional to
(r0/a)^2) and prints, over all plaquettes of the six planes, e = 1 - (1/2) tr P:
  mean, max, frac_P_neg (fraction with e > 1, i.e. (1/2) tr P < 0),
  scaled_mean_r0 and scaled_max_r0: mean and max times (r0/a)^4 (r0/a = 3.119 at beta 2.30, 6.12 at beta 2.50).

    python cap_real.py ENS_ROOT        (ENS_ROOT holds su2_L32_b2.30/ and su2_L32_b2.50/)
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
for b, n, r0a in [("2.30", 8, 3.119), ("2.50", 30, 6.12)]:  # NOT A READ: the two spacings
    Q = np.load(os.path.join(root, f"su2_L32_b{b}", "links_020.npy"), mmap_mode="r")
    for ch in (0, 4):  # NOT A READ: two chains
        q = np.asarray(Q[ch], dtype=np.float64)
        for _ in range(n):
            q = O.step(bg, q, C)
        e = oneminus(q)
        # DERIVED: 1 - (1/2) tr P > 1 exactly when (1/2) tr P < 0, a negative plaquette
        frac_neg = float((e > 1).mean())
        print(json.dumps({"beta": b, "n": n, "chain": ch, "mean": float(e.mean()), "max": float(e.max()),
                          "frac_P_neg": frac_neg,
                          "scaled_mean_r0": float(e.mean() * r0a ** 4),
                          "scaled_max_r0": float(e.max() * r0a ** 4)}), flush=True)
