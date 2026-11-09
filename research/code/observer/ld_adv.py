"""Adversarial search for S(V U) > S(U), V one observer step (simultaneous blockLink on every link).

Configurations of period P on an L = P lattice (P = 1 is translation invariant, run on L = 2 so that
the staples are well formed; the energy ratio is per-volume and does not depend on L for a periodic
configuration whose period divides L).  Links parametrised by Lie-algebra vectors; maximise
log S(VU) - log S(U) with scipy L-BFGS from many random starts (numeric gradient).

    python ld_adv.py P c starts scale
"""
import json
import sys

import numpy as np
from scipy.optimize import minimize

from ld_mono import step, site_energy, D

P, c, starts, scale = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
# DERIVED: the staples need L >= 2, and a period-P configuration tiles L = P
L = max(P, 2) if P > 1 else 2


def build(v):
    v = v.reshape((P, P, P, P, D, 3))
    th = np.linalg.norm(v, axis=-1, keepdims=True)
    n = v / np.maximum(th, 1e-300)
    q = np.concatenate([np.cos(th), np.sin(th) * n], axis=-1)
    reps = L // P
    return np.tile(q, (reps, reps, reps, reps, 1, 1))


def obj(v):
    q = build(v)
    s0 = site_energy(q).sum()
    s1 = site_energy(step(q, c)).sum()
    # DERIVED: a zero-action configuration is a fixed point of the step; its ratio is undefined, scored 0
    if s0 < 1e-12:
        return 0.0
    return -(np.log(s1) - np.log(s0))


best = None
rng = np.random.default_rng(11)
for s in range(starts):
    v0 = scale * rng.standard_normal(P ** 4 * D * 3) * (rng.uniform(0.2, 1.0))
    r = minimize(obj, v0, method="L-BFGS-B", options={"maxiter": 300})
    q = build(r.x)
    s0 = site_energy(q).sum()
    s1 = site_energy(step(q, c)).sum()
    row = {"P": P, "c": c, "start": s, "ratio": float(s1 / s0), "S0_per_plaq": float(s0 / (6 * L ** 4))}
    print(json.dumps(row), flush=True)
    if best is None or row["ratio"] > best["ratio"]:
        best = row
print(json.dumps({"best": best}), flush=True)
