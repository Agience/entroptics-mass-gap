"""One chain of an SU(N) links campaign on the CPU (numpy), in the layout the observer reads take.

The update is the generator's: lattice_generator._sun_hb_sweep (a Cabibbo-Marinari heat-bath pass over the
SU(2) subgroups and four over-relaxation passes), checkerboard, fp64. Chain k starts hot (k even,
lattice_generator._sun_init) or cold (k odd, lattice_generator.cold_init), so the plaquette histories of
the two starts bracket thermalisation. Seed: lattice_generator.campaign_seed(seed0, beta, k).

Writes into OUT (the campaign directory):
  links_c{k}_m{j}.npy   (1, x, y, z, t, direction, N, N) complex64, after therm + (j+1)*gap updates;
  plaq_c{k}.npy          <Re tr P / N> over the lattice after every update, 0..therm+nmeas*gap (entry 0 the start);
  chain_c{k}.json        the chain's parameters, seed, start and per-update wall time.
params.json and SHA256SUMS are written per campaign by the launcher (sun_launch.sh).

    python sun_campaign.py OUT N L beta k therm nmeas gap seed0
"""
import json
import os
import sys
import time

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import lattice_generator as G  # noqa: E402

if __name__ == "__main__":
    out, N, L, beta, k = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5])
    therm, nmeas, gap, seed0 = (int(x) for x in sys.argv[6:10])
    seed = G.campaign_seed(seed0, beta, k)
    b = G._Backend(None).seed(seed)
    dims = (L, L, L, L)
    start = "cold" if k % 2 else "hot"
    U = G.cold_init(b, f"su{N}", dims, ()) if start == "cold" else G._sun_init(b, dims, (), N)
    os.makedirs(out, exist_ok=True)

    def plaq():
        return 1.0 - float(G._sun_action(b, U, N).mean()) / 6.0

    hist, t0 = [plaq()], time.time()
    meta = {"N": N, "dims": list(dims), "beta": beta, "chain": k, "start": start, "seed": seed,
            "therm": therm, "nmeas": nmeas, "gap": gap, "update": "lattice_generator._sun_hb_sweep (CM HB + 4 OR)"}
    for it in range(1, therm + nmeas * gap + 1):  # NOT A READ: the Markov chain
        G._sun_hb_sweep(b, U, dims, N, beta, None)
        hist.append(plaq())
        np.save(os.path.join(out, f"plaq_c{k}.npy"), np.array(hist))
        # DERIVED: a shard after thermalisation and every gap-th update thereafter (usage: therm, gap)
        if it > therm and (it - therm) % gap == 0:
            j = (it - therm) // gap - 1
            dst = os.path.join(out, f"links_c{k}_m{j:03d}.npy")
            np.save(dst + ".tmp.npy", U[None].astype(np.complex64))
            os.replace(dst + ".tmp.npy", dst)
        meta["updates"] = it
        meta["sec_per_update"] = (time.time() - t0) / it
        with open(os.path.join(out, f"chain_c{k}.json"), "w") as f:
            json.dump(meta, f)
        print(f"c{k} it={it} plaq={hist[-1]:.6f} {meta['sec_per_update']:.2f}s/upd", flush=True)
