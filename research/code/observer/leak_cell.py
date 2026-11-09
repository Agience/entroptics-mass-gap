"""The leakage inputs (rho_c^2, rho_r^2, eta and the leakage margin) at a coarse time step of
the cell size, from the slice sums cell_read.py saves with LEAK_K (numpy/scipy).

vis2_read.py's two-operator basis, with the observer the Lean step at the observer's own scale (the n steps of
the cell read) instead of APE smearing:
  blk{k}:  B = the block observer (block2 k times) slice sums, M = the stepped spatial energy summed over the
           2^k fine slices of each coarse slice; coarse step 2^k sites;
  cell{b}: B = the stepped six-plane energy summed over slabs of b fine slices (the zero-momentum sum of one
           time slab of cell energies, the cell view's coarse reader), M = the stepped spatial energy over the
           same slabs; coarse step b sites.
vis2_read.reads gives, per coarse separation D, rho_c^2(D), rho_r^2(D), eta(D), margin(D); errors are a
delete-one-shard jackknife.

    python leak_cell.py OUT.json b1,b2 shard1.npz shard2.npz ...
"""
import json
import sys

import numpy as np

from vis2_read import reads

if __name__ == "__main__":
    out, cellb, files = sys.argv[1], [int(v) for v in sys.argv[2].split(",") if v], sys.argv[3:]
    data = [np.load(f) for f in files]
    data = [(f, d) for f, d in zip(files, data) if "Ms" in d.files]
    ks = sorted(int(key[3:]) for key in data[0][1].files if key.startswith("blk"))
    rep = {"files": [f for f, _ in data], "variants": {}}
    for name, B, M in ([(f"blk{k}", lambda d, k=k: d[f"blk{k}"], 2 ** k) for k in ks]
                       + [(f"cell{b}", lambda d, b=b: d["Es"].reshape(d["Es"].shape[0], -1, b).sum(2), b)
                          for b in cellb]):
        X = np.stack([np.stack([B(d), d["Ms"].reshape(d["Ms"].shape[0], -1, M).sum(2)]) for _, d in data])
        ns, nop, nc, Tc = X.shape
        Dmax = Tc // 2
        rB, rS, C, LK = reads(X, nop, nc, Tc, Dmax)
        jk = [reads(np.delete(X, i, axis=0), nop, nc, Tc, Dmax)[3] for i in range(ns)]  # NOT A READ: jackknife
        err = np.sqrt((ns - 1) / ns * ((np.stack(jk) - LK) ** 2).sum(0))
        rep["variants"][name] = {"coarse_step_sites": M, "coarse_T": Tc, "nshards": ns, "chains": nc,
                                 "leak": LK.tolist(), "leak_err": err.tolist(),
                                 "leak_rows": ["rho_c^2(D)", "rho_r^2(D)", "eta(D)", "margin(D)"]}
        print(name, "D=1:", " ".join(f"{r}={LK[i, 1]:.4f}+-{err[i, 1]:.4f}" for i, r in
                                     enumerate(["rho_c2", "rho_r2", "eta", "margin"])), flush=True)
    json.dump(rep, open(out, "w"), indent=1)
