"""The smeared observer: the spatial plaquette after n APE sweeps, read at fixed physical smearing radius.

A same-lattice smearing of fixed physical radius is a continuum-compatible observer (a block lattice
samples the field at discrete points; a smearing defines it at every point). The generator's spatial APE
(lattice_generator.ape_smear, alpha 0.5) diffuses the spatial links with radius proportional to sqrt(n) a,
so n a^2 fixed is a fixed physical radius: n quadruples per halving of the spacing. Read per shard (one
measurement of every chain), on CUDA (fp32):
  * u_s = <(1/2) tr P> over spatial plaquettes of the smeared configuration;
  * var_s, its variance over plaquettes (the width of the smeared field's distribution).
No parameter is fitted; the uncertainty is the standard error of the per-shard reads.

    python smear_read.py CAMPAIGN_DIR n [maxshards] > out.json
Reads only shards listed in verified.list or SHA256SUMS.
"""
import json
import os
import sys
import time

import numpy as np

import observer_step as O
import lattice_generator as G
from lattice_generator import _Backend


def spatial_plaq(b, q):
    vals = []
    for mu in range(3):
        for nu in range(mu + 1, 3):  # NOT A READ: the three spatial planes
            vals.append(O.halftr(b, q, mu, nu).double())
    t = b.t.stack(vals)
    return float(t.mean()), float(t.var())


if __name__ == "__main__":
    camp, nsw = sys.argv[1], int(sys.argv[2])
    maxsh = O.opt(3, 10 ** 9)
    b = _Backend("cuda", fp="32")
    per, t0 = [], time.time()
    for name in O.shards(camp, maxsh):
        q = b.t.as_tensor(np.load(os.path.join(camp, name)).astype(np.float32), dtype=b.f, device=b.dev)
        q = G.ape_smear(q, nsw, alpha=0.5, device="cuda")
        u, v = spatial_plaq(b, q)
        per.append({"shard": name, "u_s": u, "var_s": v})
        del q
        print(f"{name} u_s={u:.6f} var={v:.6f} ({time.time() - t0:.0f}s)", file=sys.stderr, flush=True)
    us = np.array([p["u_s"] for p in per])
    vs = np.array([p["var_s"] for p in per])
    print(json.dumps({"campaign": camp, "params": json.load(open(os.path.join(camp, "params.json"))),
                      "nsweep": nsw, "alpha": 0.5, "nshards": len(per),
                      "u_s": [float(us.mean()), float(us.std(ddof=1) / np.sqrt(len(us)))],
                      "var_s": [float(vs.mean()), float(vs.std(ddof=1) / np.sqrt(len(vs)))],
                      "per_shard": per}, indent=1))
