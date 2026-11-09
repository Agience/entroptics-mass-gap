"""The observer's own scale: <e>(n) along the Lean step, from which n^2 <e>(n), the step analogue of the
gradient-flow t0, is read.

At each step n of the observer step (observer_step.step: BlockSU2.blockLink, all four directions, c), on CUDA
in fp32, e = sum over the six planes of (1 - (1/2) tr P), averaged over the lattice (chain 0 of each chosen
shard). n^2 <e>(n) is dimensionless in physical units once n is proportional to a^-2, so the step n* where it
crosses a fixed value scales as a^-2: sqrt(n*(beta1)/n*(beta2)) = a(beta2)/a(beta1), read from the plaquette
average alone, no potential and no fit (the crossing is the linear interpolation between the two bracketing
steps, taken downstream of this file). Writes per configuration the curve <e>(n), n = 0..nmax, for nconfigs
shards spread evenly over the campaign.

    python flowscale_gpu.py CAMPAIGN_DIR c nmax nconfigs > out.json
SU(2) or SU(N) links (e = sum of 1 - Re tr P / N); `OBS_DEVICE=numpy` runs it on the CPU.
Reads only shards listed in verified.list or SHA256SUMS.
"""
import json
import os
import sys

import numpy as np

import observer_step as O


def emean(bg, q):
    return sum(float(e.mean()) for e in O.planes(bg, q))


if __name__ == "__main__":
    camp, cw, nmax, ncf = sys.argv[1], float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    bg = O.backend()
    names = O.shards(camp)
    pick = [names[i * len(names) // ncf] for i in range(ncf)]  # NOT A READ: spread over the campaign
    curves = []
    for name in pick:
        links = np.load(os.path.join(camp, name), mmap_mode="r")
        q = O.chain(bg, links, 0)
        cur = [emean(bg, q)]
        for _ in range(nmax):
            q = O.step(bg, q, cw)
            cur.append(emean(bg, q))
        curves.append(cur)
        print(name, file=sys.stderr, flush=True)
    print(json.dumps({"campaign": camp, "c": cw, "nmax": nmax, "configs": pick, "e": curves}))
