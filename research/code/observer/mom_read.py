"""Single-site even moments of the observer energy density in r0 units.

e = 1 - (1/2) tr P over the six planes after n steps of the Lean observer step (observer_step.step, c = 0.15;
n = 8 at beta 2.30, 30 at beta 2.50), on chain 1 of four shards (links_005, 015, 025, 035) of each 32^4
campaign. With d = e - <e> (mean over all four configurations together), per configuration
m_p = <d^{2p}> * (r0/a)^{8p}, p = 1, 2, 3 (r0/a = 3.119, 6.12). Prints the mean of m_p over the four
configurations and its standard error (std / 2). The input ObserverEnergyMoments asks is that these stay
bounded as a -> 0.

    python mom_read.py ENS_ROOT
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
    E = []
    for sh in ["links_005.npy", "links_015.npy", "links_025.npy", "links_035.npy"]:  # NOT A READ: four configurations
        Q = np.load(os.path.join(root, f"su2_L32_b{b}", sh), mmap_mode="r")
        q = np.asarray(Q[1], dtype=np.float64)
        for _ in range(n):
            q = O.step(bg, q, C)
        E.append(oneminus(q).ravel())
    E = np.stack(E)
    d = E - E.mean()
    for p in (1, 2, 3):  # NOT A READ: the three moments
        m = (d ** (2 * p)).mean(axis=1) * r0a ** (8 * p)
        print(json.dumps({"beta": b, "n": n, "p": p, "moment_r0": float(m.mean()),
                          "spread": float(m.std(ddof=1) / 2)}), flush=True)
