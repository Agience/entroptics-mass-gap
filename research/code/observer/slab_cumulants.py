"""Cumulants of the observer's energy summed over a slab of fixed physical thickness, per physical volume.

Reads the per-shard zero-momentum slice sums S(t) that ed_read.py / ed_read_gpu.py / obs4_read_gpu.py write,
shape (chain, T). A slab of Dw consecutive slices (Dw / (r0/a) its thickness in r0) sums the readings over
(L/(r0/a))^3 x Dw/(r0/a) r0^4; the second and fourth cumulants of that sum, divided by its physical volume,
stay finite as a -> 0 when the smeared energy density has a continuum limit with bounded cube moments
(E's smeared form). The error is a delete-one jackknife over shards.

    python slab_cumulants.py SLICE_SUM_DIR L r0_over_a Dw
"""
import glob
import json
import sys

import numpy as np

d, L, r0a, Dw = sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
X = np.stack([np.load(f) for f in sorted(glob.glob(f"{d}/links_*_n*.npy"))])  # (shard, chain, T)
vphys = (L / r0a) ** 3 * Dw / r0a
slab = sum(np.roll(X, -j, axis=-1) for j in range(Dw))  # NOT A READ: the Dw slices of each slab


def cum(Y):
    dev = Y - Y.mean()
    k2 = (dev ** 2).mean()
    k4 = (dev ** 4).mean() - 3 * k2 ** 2
    return np.array([k2, k4]) / vphys


full = cum(slab)
n = len(slab)
jk = np.stack([cum(np.delete(slab, i, axis=0)) for i in range(n)])  # NOT A READ: jackknife over shards
err = np.sqrt((n - 1) / n * ((jk - full) ** 2).sum(0))
print(json.dumps({"dir": d, "L": L, "r0_over_a": r0a, "slab_slices": Dw, "slab_r0": Dw / r0a,
                  "vphys_r0^4": vphys, "nshards": n, "k2_per_V": [float(full[0]), float(err[0])],
                  "k4_per_V": [float(full[1]), float(err[1])]}, indent=1))
