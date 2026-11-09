"""The 0++ glueball operators of a campaign, per shard: zero-momentum spatial-plaquette slice sums at several APE
smearing levels.

Per configuration the spatial links are APE-smeared (lattice_generator.ape_smear, alpha 0.5, temporal links
untouched, so the transfer matrix is unchanged) cumulatively to each level n_1 < n_2 < ...; at each level the
operator is

    O_n(t) = sum_{x, y, z} sum_{spatial planes} (1/2) tr P(x, t),

the plaquette summed over the slice: zero momentum, invariant under the cubic group and under charge conjugation,
so it couples to the A1++ channel whose lightest state is the 0++ glueball (and to the vacuum, which glueball_agg.py
subtracts). Level 0 is checked against observer_step.slice_sums: O_0(t) = 3 L^3 - slice_sums(t).

Output per shard: <shard>_glue.npz with S (chain, level, T) float64 and levels.

    [OBS_DEVICE=cuda] python glueball_read.py CAMPAIGN_DIR n1,n2,... OUT_DIR [maxshards]
Reads SHA256SUMS (or verified.list); a shard whose output exists is skipped.
"""
import os
import sys
import time

import numpy as np

import observer_step as O
from lattice_generator import ape_smear


def slices(bg, q):
    """sum over the slice of (1/2) tr P over the three spatial planes, float64, shape (T,) for a batch of one."""
    tot = 0.0
    for mu in range(3):
        for nu in range(mu + 1, 3):  # NOT A READ: the three spatial planes
            p = O.halftr(bg, q, mu, nu)
            tot = tot + (p.double() if bg.torch else p.astype(np.float64))
    tot = tot[0]
    return bg.to_numpy(tot.sum(dim=(0, 1, 2)) if bg.torch else tot.sum(axis=(0, 1, 2)))


if __name__ == "__main__":
    camp, levels, out = sys.argv[1], [int(v) for v in sys.argv[2].split(",")], sys.argv[3]
    maxsh = O.opt(4, 10 ** 9)
    assert levels == sorted(levels)
    dev = os.environ.get("OBS_DEVICE", "cuda")
    bg = O.backend()
    os.makedirs(out, exist_ok=True)
    for name in O.shards(camp, maxsh, prefer_verified=False):
        dst = os.path.join(out, name.replace(".npy", "_glue.npz"))
        if os.path.exists(dst):
            continue
        t0 = time.time()
        links = np.load(os.path.join(camp, name), mmap_mode="r")
        rows = []
        for ch in range(links.shape[0]):  # NOT A READ: one chain at a time bounds the memory
            q = O.chain(bg, links, ch)
            L3 = int(np.prod(q.shape[1:4]))
            s0 = slices(bg, q)
            ref = 3 * L3 - O.slice_sums(bg, q[0], spatial=True)
            assert np.abs(s0 - ref).max() < 1e-6 * 3 * L3, "level-0 operator disagrees with observer_step.slice_sums"
            per, done = [], 0
            for n in levels:  # NOT A READ: cumulative smearing to each level
                q = ape_smear(q, n - done, alpha=0.5, device=(dev if bg.torch else None))
                done = n
                per.append(slices(bg, q))
            rows.append(np.stack(per))
            del q
        np.savez(dst + ".tmp.npz", S=np.stack(rows), levels=np.array(levels))
        os.replace(dst + ".tmp.npz", dst)
        print(name, f"{time.time() - t0:.0f}s", flush=True)
