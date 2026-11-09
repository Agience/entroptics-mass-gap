"""The Lean observer's energy density, read with the Lean step itself.

ed_read_gpu.py smears with the generator's spatial APE (a stand-in). This applies the observer of
ObserverFlow.obsConfFlow, observer_step.step (BlockSU2.blockLink on the same lattice, ApeLattice.apeConf, all
four directions, U_mu(x) -> V/|V|, V = U_mu(x) + c * (six staples), every link from the old configuration),
n times, on CUDA in fp32; n proportional to a^-2 keeps the smearing radius physical. Output per shard as
ed_read.py: zero-momentum slice sums of the spatial-plaquette action density, shape (chain, T); ed_agg.py
reads it unchanged.

    python obs4_read_gpu.py CAMPAIGN_DIR c nsteps OUT_DIR [maxshards]
SU(2) or SU(N) links (observer_step's two layouts); `OBS_DEVICE=numpy` runs it on the CPU (observer_step.backend).
Reads only shards listed in verified.list or SHA256SUMS; a shard whose output exists is skipped.
"""
import os
import sys

import numpy as np

import observer_step as O

if __name__ == "__main__":
    camp, cw, nst, out = sys.argv[1], float(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    maxsh = O.opt(5, 10 ** 9)
    bg = O.backend()
    os.makedirs(out, exist_ok=True)
    for name in O.shards(camp, maxsh):
        dst = os.path.join(out, name.replace(".npy", f"_n{nst}.npy"))
        if os.path.exists(dst):
            continue
        links = np.load(os.path.join(camp, name), mmap_mode="r")
        rows = []
        for ch in range(links.shape[0]):  # NOT A READ: one chain at a time bounds the memory
            q = O.chain(bg, links, ch)
            for _ in range(nst):
                q = O.step(bg, q, cw)
            rows.append(O.slice_sums(bg, q)[0])
            del q
        np.save(dst + ".tmp.npy", np.stack(rows))
        os.replace(dst + ".tmp.npy", dst)
        print(name, flush=True)
