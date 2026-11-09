"""Slice sums of the APE-smeared energy density, for its connected correlator (CPU, one process per shard).

The bounded observer O o V reads lattice-size loops, whose fluctuation vanishes with the spacing.
The candidate non-trivial field is the same smeared
field with its canonical factor a^-4: the action density E = a^-4 e, e = sum over the three spatial planes
of (1 - (1/2) tr P) on the links smeared by the generator's spatial APE (lattice_generator.ape_smear,
alpha 0.5; nsweep proportional to a^-2 keeps the radius physical). This writes, per shard, the
zero-momentum slice sums S(t) = sum_x e(x, t) (observer_step.slice_sums), shape (chain, T); ed_agg.py turns
them into the physical connected correlator G(t) = a^-5 <S(0) S(t)>_c / L^3 (= integral d^3x <E(x,t) E(0,0)>_c).

    python ed_read.py CAMPAIGN_DIR nsweep OUT_DIR [workers]
SU(N) links (complex) are smeared by observer_step.ape_sun and read as 1 - Re tr P / N per plane.
Reads every shard listed in the campaign's SHA256SUMS; a shard whose output exists is skipped.
"""
import os
import sys

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")

import numpy as np
from multiprocessing import Pool

import observer_step as O
import lattice_generator as G
from lattice_generator import _Backend

bg = _Backend(None)
camp, nsm, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]  # module level, so Pool workers see them


def one(name):
    dst = os.path.join(out, name.replace(".npy", f"_n{nsm}.npy"))
    if os.path.exists(dst):
        return name
    links = np.load(os.path.join(camp, name), mmap_mode="r")
    rows = []
    for ch in range(links.shape[0]):  # NOT A READ: one chain at a time bounds the memory
        if np.iscomplexobj(links):  # SU(N): observer_step.ape_sun, the same spatial APE with the SU(N) projection
            qs = O.ape_sun(bg, O.chain(bg, links, ch), nsm, 0.5)
        else:
            q = np.asarray(links[ch:ch + 1], dtype=np.float32)
            qs = G.ape_smear(q, nsm, alpha=0.5)
        rows.append(O.slice_sums(bg, qs[0]))
    np.save(dst + ".tmp.npy", np.stack(rows))
    os.replace(dst + ".tmp.npy", dst)
    return name


if __name__ == "__main__":
    workers = O.opt(4, 8)
    os.makedirs(out, exist_ok=True)
    with Pool(workers) as p:
        for n in p.imap_unordered(one, O.shards(camp, prefer_verified=False)):
            print(n, flush=True)
