"""The observer's cell-energy field, read on an ensemble: the observer's energy density after
the Lean step, summed over the cells of a dyadic grid. numpy only.

Per configuration: n applications of observer_step.step (ObserverFlow.obsConfFlow's BlockSU2.blockLink on the
same lattice, coefficient c), then observer_step.energy_density (six planes, sum of 1 - (1/2) tr P), then the
sum over each cube of side b sites. A b dividing L tiles the periodic lattice exactly, so the cell grid is
periodic and every cell has its full set of neighbours. Writes one npz per shard with, for each b, the array
b{b} of shape (chain, m, m, m, m), m = L / b, in the (x, y, z, t) order of the configuration.

With LEAK_K set (e.g. "3,4"), the shard also holds the time-slice sums the leakage reads need
(leak_cell.py), each of shape (chain, T or T / 2^k):
  blk{k}  spatial energy 1 - (1/2) tr P summed over each slice of the configuration blocked k times (observer_step.block2
          at c), the coarse block observer of vis2_read.py;
  Ms      spatial energy summed over each fine slice after the n observer steps;
  Es      the six-plane energy density after the n observer steps summed over each fine slice (the
          zero-momentum sum of the cell energies of one slice).
With SAVE_E=1 the shard also holds E, the six-plane energy density itself (chain, L, L, L, L), float32, from
which cellview_w1.py reads cells of any side on a sliding grid.

    python cell_read.py CAMPAIGN_DIR c nsteps b1,b2,... OUT_DIR shard_lo shard_hi
Reads only shards listed in verified.list or SHA256SUMS; a shard whose output exists is skipped.

The torch path (OBS_DEVICE set to a torch device, e.g. cuda or cpu; OBS_FP 32 default) runs the block steps,
the observer steps, the energy densities, the cube sums and the slice sums on the device (chain_torch); the
npz holds the same keys in the same order, with the same shapes and dtypes (float64; E float32). Unset (or
OBS_DEVICE=numpy) runs the numpy path below.
"""
import os
import sys
import time

import numpy as np

import observer_step as O
from lattice_generator import _Backend


def cubes(e, b):
    L = e.shape[0]
    m = L // b
    assert m * b == L, "b must divide L"
    return e.reshape(m, b, m, b, m, b, m, b).sum(axis=(1, 3, 5, 7))


def cubes_torch(e, b):
    L = e.shape[0]
    m = L // b
    assert m * b == L, "b must divide L"
    return e.reshape(m, b, m, b, m, b, m, b).sum(dim=(1, 3, 5, 7))


torch_device = O.torch_device


def chain_torch(tb, q, cw, nst, bs, leak_k, save_e):
    """One chain on the torch path, q of shape (X, Y, Z, T, 4, 4) on the device: the numpy loop body's arrays,
    as numpy arrays keyed as in the npz, and the stepped links and density (for checks)."""
    r = {}
    if leak_k:
        qb = q
        for k in range(1, max(leak_k) + 1):
            qb = O.block2(tb, qb, cw)
            if k in leak_k:
                r[f"blk{k}"] = tb.to_numpy(O.energy_density(tb, qb, spatial=True).sum(dim=(0, 1, 2)))
        del qb
    for _ in range(nst):  # NOT A READ: the observer's n steps
        q = O.step(tb, q, cw)
    e = O.energy_density(tb, q)
    for b in bs:
        r[f"b{b}"] = tb.to_numpy(cubes_torch(e, b))
    if save_e:
        r["E"] = tb.to_numpy(e.float())
    if leak_k:
        r["Ms"] = tb.to_numpy(O.energy_density(tb, q, spatial=True).sum(dim=(0, 1, 2)))
        r["Es"] = tb.to_numpy(e.sum(dim=(0, 1, 2)))
    return r, q, e


def run_torch(camp, cw, nst, bs, out, names, leak_k, save_e):
    tb = O.backend()
    for name in names:
        dst = os.path.join(out, name.replace(".npy", f"_c{cw}_n{nst}.npz"))
        if os.path.exists(dst):
            continue
        t0 = time.time()
        links = np.load(os.path.join(camp, name), mmap_mode="r")
        res = {f"b{b}": [] for b in bs}
        for k in leak_k:
            res[f"blk{k}"] = []
        if leak_k:
            res["Ms"], res["Es"] = [], []
        if save_e:
            res["E"] = []
        for ch in range(links.shape[0]):  # NOT A READ: one chain at a time bounds the memory
            q = tb.t.as_tensor(np.array(links[ch], dtype=np.float32), dtype=tb.f, device=tb.dev)
            r, _, _ = chain_torch(tb, q, cw, nst, bs, leak_k, save_e)
            for key in res:
                res[key].append(r[key])
            del q, r
        np.savez(dst + ".tmp.npz", **{key: np.stack(v) for key, v in res.items()})
        os.replace(dst + ".tmp.npz", dst)
        print(name, f"{time.time() - t0:.0f}s", flush=True)


if __name__ == "__main__":
    camp, cw, nst = sys.argv[1], float(sys.argv[2]), int(sys.argv[3])
    bs = [int(x) for x in sys.argv[4].split(",")]
    out, lo, hi = sys.argv[5], int(sys.argv[6]), int(sys.argv[7])
    bg = _Backend(None)
    leak_k = [int(v) for v in os.environ.get("LEAK_K", "").split(",") if v]
    os.makedirs(out, exist_ok=True)
    names = O.shards(camp)[lo:hi]
    if torch_device():
        run_torch(camp, cw, nst, bs, out, names, leak_k, os.environ.get("SAVE_E") == "1")
        sys.exit(0)
    for name in names:
        dst = os.path.join(out, name.replace(".npy", f"_c{cw}_n{nst}.npz"))
        if os.path.exists(dst):
            continue
        t0 = time.time()
        links = np.load(os.path.join(camp, name), mmap_mode="r")
        res = {f"b{b}": [] for b in bs}
        for k in leak_k:
            res[f"blk{k}"] = []
        if leak_k:
            res["Ms"], res["Es"] = [], []
        save_e = os.environ.get("SAVE_E") == "1"
        if save_e:
            res["E"] = []
        for ch in range(links.shape[0]):  # NOT A READ: one chain at a time bounds the memory
            q = np.array(links[ch], dtype=np.float32)
            if leak_k:
                qb = q
                for k in range(1, max(leak_k) + 1):
                    qb = O.block2(bg, qb, cw)
                    if k in leak_k:
                        res[f"blk{k}"].append(O.energy_density(bg, qb, spatial=True).sum(axis=(0, 1, 2)))
                del qb
            for _ in range(nst):
                q = O.step(bg, q, cw)
            e = O.energy_density(bg, q)
            for b in bs:
                res[f"b{b}"].append(cubes(e, b))
            if save_e:
                res["E"].append(e.astype(np.float32))
            if leak_k:
                res["Ms"].append(O.energy_density(bg, q, spatial=True).sum(axis=(0, 1, 2)))
                res["Es"].append(e.sum(axis=(0, 1, 2)))
            del q, e
        np.savez(dst + ".tmp.npz", **{key: np.stack(v) for key, v in res.items()})
        os.replace(dst + ".tmp.npz", dst)
        print(name, f"{time.time() - t0:.0f}s", flush=True)
