"""GPU twin of ed_read.py: per shard, the zero-momentum slice sums S(t) = sum_x e(x, t) of the APE-smeared
spatial plaquette action density e = sum over the three spatial planes of (1 - (1/2) tr P)
(lattice_generator.ape_smear, alpha 0.5; observer_step.slice_sums), shape (chain, T), on CUDA in fp32.
One chain at a time bounds the memory. ed_agg.py reads the output unchanged.

    python ed_read_gpu.py CAMPAIGN_DIR nsweep OUT_DIR
Reads only shards listed in verified.list or SHA256SUMS; a shard whose output exists is skipped.
"""
import os
import sys

import numpy as np

import observer_step as O
import lattice_generator as G
from lattice_generator import _Backend

if __name__ == "__main__":
    camp, nsm, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    bg = _Backend("cuda", fp="32")
    os.makedirs(out, exist_ok=True)
    for name in O.shards(camp):
        dst = os.path.join(out, name.replace(".npy", f"_n{nsm}.npy"))
        if os.path.exists(dst):
            continue
        links = np.load(os.path.join(camp, name), mmap_mode="r")
        rows = []
        for ch in range(links.shape[0]):  # NOT A READ: one chain at a time bounds the memory
            q = bg.t.as_tensor(np.asarray(links[ch:ch + 1], dtype=np.float32), dtype=bg.f, device=bg.dev)
            qs = G.ape_smear(q, nsm, alpha=0.5, device="cuda")
            rows.append(O.slice_sums(bg, qs)[0])
            del q, qs
        np.save(dst + ".tmp.npy", np.stack(rows))
        os.replace(dst + ".tmp.npy", dst)
        print(name, flush=True)
