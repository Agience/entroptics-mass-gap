"""An SU(2) links campaign on a GPU with lattice_generator's heat bath, in the layout of the 48^4 / 64^4 campaigns.

`chains` chains evolve together as a leading batch axis (`_su2_init` hot start, `_su2_hb_sweep`: checkerboard
heat bath plus over-relaxation), `therm` sweeps, then one shard every `gap` sweeps: links_{m:03d}.npy of shape
(chain, x, y, z, t, direction, quaternion) float32. params.json records the generator's sha256 (it must equal the
campaigns' c1c0b165...); SHA256SUMS is written over the shards at the end, and COMPLETE.

    OBS_FP=32 python gen_su2_links.py OUT_DIR L beta chains therm nmeas gap seed [device]
"""
import hashlib
import json
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, ".."))
import lattice_generator as LG  # noqa: E402

if __name__ == "__main__":
    out, L, beta, nch, therm, nmeas, gap, seed = (sys.argv[1], int(sys.argv[2]), float(sys.argv[3]),
                                                  int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]),
                                                  int(sys.argv[7]), int(sys.argv[8]))
    # DERIVED: 9 is [device]'s position in the usage line. CHOSEN: default cuda, the campaign hardware
    dev = sys.argv[9] if len(sys.argv) > 9 else "cuda"
    fp = os.environ.get("OBS_FP", "32")
    os.makedirs(out, exist_ok=True)
    gen = os.path.join(HERE, "..", "lattice_generator.py")
    gsha = hashlib.sha256(open(gen, "rb").read()).hexdigest()
    import torch
    params = {"group": "su2", "update": "heatbath (lattice_generator._su2_hb_sweep)", "dims": [L] * 4,
              "beta": beta, "chains": nch, "therm": therm, "nmeas": nmeas, "gap": gap, "seed": seed,
              "backend": dev, "fp": fp, "layout": "(chain, x, y, z, t, direction, quaternion) float32",
              "generator": os.path.abspath(gen), "generator_sha256": gsha, "torch": torch.__version__,
              "device": torch.cuda.get_device_name(0) if dev.startswith("cuda") else dev,
              "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    with open(os.path.join(out, "params.json"), "w") as f:
        json.dump(params, f, indent=2)
    b = LG._Backend(dev, fp=fp).seed(seed)
    init, sweep, _act, dstep = LG._ops("su2", "heatbath")
    sdims = (L, L, L, L)
    q = init(b, sdims, (nch,))
    t0 = time.time()
    for i in range(therm):
        sweep(b, q, sdims, beta, dstep)
        # CHOSEN: a progress line every 25 thermalisation sweeps; logging cadence only
        if i % 25 == 0:
            print(f"therm {i} t {time.time() - t0:.0f}s", flush=True)
    for m in range(nmeas):
        dst = os.path.join(out, f"links_{m:03d}.npy")
        for _ in range(gap):
            sweep(b, q, sdims, beta, dstep)
        np.save(dst + ".part.npy", q.detach().cpu().numpy().astype(np.float32))
        os.replace(dst + ".part.npy", dst)
        print(f"shard {m} t {time.time() - t0:.0f}s", flush=True)
    with open(os.path.join(out, "SHA256SUMS"), "w") as f:
        for m in range(nmeas):
            name = f"links_{m:03d}.npy"
            h = hashlib.sha256()
            with open(os.path.join(out, name), "rb") as g:
                for chunk in iter(lambda: g.read(1 << 24), b""):
                    h.update(chunk)
            f.write(f"{h.hexdigest()}  {name}\n")
    open(os.path.join(out, "COMPLETE"), "w").close()
