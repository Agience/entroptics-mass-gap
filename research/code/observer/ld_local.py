"""Local forms of the coarsening on L = 4 (periodic).

(1) same box: identity links on the box [0,2)^4 and its links, Haar outside -> raw energy of the box
    is zero, smoothed energy of the box after one step is not.
(2) enlarged box: maximise e'(0) / (raw energy of the plaquettes based in 0 + {-1..2}^4), which on
    L = 4 is the whole lattice, by L-BFGS over all links (numeric gradient).

    python ld_local.py c starts maxiter
"""
import json
import sys

import numpy as np
from scipy.optimize import minimize

from ld_mono import step, site_energy, haar, D

c, starts, maxiter = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
# CHOSEN: L = 4, the smallest lattice holding the box [0,2)^4 with a ring of neighbours; on it the
# enlarged box of (2) is the whole lattice
L = 4

# (1)
for s in range(3):
    rng = np.random.default_rng(300 + s)
    q = haar(rng, L)
    # identity on every link with base and end in [0,2]^4, so all plaquettes based in [0,2)^4 are 1
    for x in np.ndindex(3, 3, 3, 3):
        for mu in range(D):
            # DERIVED: the link from x in direction mu has both ends in [0,2]^4
            if x[mu] < 2:
                q[x + (mu,)] = np.array([1.0, 0, 0, 0])
    e0 = site_energy(q)
    e1 = site_energy(step(q, c))
    print(json.dumps({"test": "same_box", "c": c, "raw_box": float(e0[:2, :2, :2, :2].sum()),
                      "smoothed_box": float(e1[:2, :2, :2, :2].sum())}), flush=True)


# (2)
def build(v):
    v = v.reshape((L, L, L, L, D, 3))
    th = np.linalg.norm(v, axis=-1, keepdims=True)
    n = v / np.maximum(th, 1e-300)
    return np.concatenate([np.cos(th), np.sin(th) * n], axis=-1)


def obj(v):
    q = build(v)
    s0 = site_energy(q).sum()
    e1 = site_energy(step(q, c))[0, 0, 0, 0]
    return -(e1 / max(s0, 1e-12))


rng = np.random.default_rng(17)
for s in range(starts):
    v0 = rng.uniform(0.05, 1.5) * rng.standard_normal(L ** 4 * D * 3)
    # concentrate the start near the origin
    w = np.exp(-np.sum(np.minimum(np.indices((L,) * 4), L - np.indices((L,) * 4)) ** 2, axis=0) / 2.0)
    v0 = (v0.reshape((L, L, L, L, D, 3)) * w[..., None, None]).ravel()
    r = minimize(obj, v0, method="L-BFGS-B", options={"maxiter": maxiter})
    print(json.dumps({"test": "enlarged_site", "c": c, "start": s, "max_ratio": float(-r.fun),
                      "nit": int(r.nit)}), flush=True)
