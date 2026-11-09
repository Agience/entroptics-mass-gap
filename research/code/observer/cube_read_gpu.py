"""E's remaining input, read: the observer's energy summed over cubes of fixed physical size.

ObserverEnergyBox.CubeMomentBound asks, for O in the plaquette class, that stateK((cubeSum a R (O o V_k))^{2p})
stay bounded in k: the a^-4 of the energy density cancels against the cell volume a^4, so the input is the
plain sum of the observer's readings over a physical cube. Here V_k is the Lean observer step
(observer_step.step: BlockSU2.blockLink on the same lattice, all four directions, c, n steps with n
proportional to a^-2), on CUDA in fp32; the density is observer_step.energy_density over the six planes,
O = sum of 1 - (1/2) tr P; and the cubes tile the lattice with side b sites (b proportional to r0/a, the
physical side fixed). Writes per shard the cube sums, shape (chain, ncubes); observer_summaries.py cube
reads their moments.

    python cube_read_gpu.py CAMPAIGN_DIR c nsteps b OUT_DIR [maxshards]
SU(2) or SU(N) links (observer_step's two layouts); `OBS_DEVICE=numpy` runs it on the CPU (observer_step.backend).
Reads only shards listed in verified.list or SHA256SUMS; a shard whose output exists is skipped.
"""
import os
import sys

import numpy as np

import observer_step as O


def cubes(e, b):
    L = e.shape[0]
    m = L // b
    e = e[:m * b, :m * b, :m * b, :m * b].reshape(m, b, m, b, m, b, m, b)
    e = e.sum(dim=(1, 3, 5, 7)) if hasattr(e, "cpu") else e.sum(axis=(1, 3, 5, 7))
    return np.asarray(e.reshape(-1).cpu().numpy() if hasattr(e, "cpu") else e.reshape(-1))


if __name__ == "__main__":
    camp, cw, nst, b, out = sys.argv[1], float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    maxsh = O.opt(6, 10 ** 9)
    bg = O.backend()
    os.makedirs(out, exist_ok=True)
    for name in O.shards(camp, maxsh):
        dst = os.path.join(out, name.replace(".npy", f"_n{nst}_b{b}.npy"))
        if os.path.exists(dst):
            continue
        links = np.load(os.path.join(camp, name), mmap_mode="r")
        rows = []
        for ch in range(links.shape[0]):  # NOT A READ: one chain at a time bounds the memory
            q = O.chain(bg, links, ch)
            for _ in range(nst):
                q = O.step(bg, q, cw)
            rows.append(cubes(O.energy_density(bg, q)[0], b))
            del q
        np.save(dst + ".tmp.npy", np.stack(rows))
        os.replace(dst + ".tmp.npy", dst)
        print(name, flush=True)
