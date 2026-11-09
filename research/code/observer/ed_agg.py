"""Physical connected correlator of the smeared energy density, compared across spacings.

G(t) r0^5 = (r0/a)^5 <S(0) S(D)>_c / L^3 at t/r0 = D / (r0/a), from the slice sums of ed_read.py, ed_read_gpu.py or obs4_read_gpu.py (files links_*_n*.npy in each directory). The connected
part subtracts the ensemble mean (per spacing); the error is a jackknife over shards (over chains for
the per-chain shards of an SU(N) campaign, `blocks_of`). Non-triviality on the
continuum: G at fixed t/r0 > 0 approaches one non-zero value as a -> 0. The finer spacing is read at the
coarser one's physical times by log-linear interpolation between its two neighbouring lattice times (no
model is fitted); r0/a enters from the fit-free Sommer reads, each end of its range shown.

    python ed_agg.py DIR_A r0a_A DIR_B r0a_B_lo r0a_B_hi
"""
import glob
import json
import os
import sys

import numpy as np

from observer_step import chain_blocks


def load(d):
    fs = sorted(f for f in glob.glob(f"{d}/links_*_n*.npy") if "tmp" not in f)
    return np.stack([np.load(f) for f in fs]), blocks_of(fs)  # (shard, chain, T)


def corr(X):
    d = X - X.mean()
    T = X.shape[-1]
    L3 = T ** 3  # NOT A READ: the campaigns are hypercubic
    return np.array([(d * np.roll(d, -D, axis=-1)).mean() for D in range(T // 2 + 1)]) / L3


def blocks_of(files):
    """Jackknife blocks (lists of row indices) from shard file names: the shards of one chain of an SU(N)
    campaign (`links_c{k}_m{j}_...`) form one block, any other shard is its own (observer_step.chain_blocks)."""
    names = [os.path.basename(f) for f in files]
    pos = {n: i for i, n in enumerate(names)}
    return [[pos[n] for n in bl] for bl in chain_blocks(names)]


def jk(X, f, blocks=None):
    """Delete-one jackknife over the leading axis, or over `blocks` (lists of row indices) when given."""
    full = f(X)
    if blocks is None:
        blocks = list(range(X.shape[0]))
    reps = np.stack([f(np.delete(X, i, axis=0)) for i in blocks])
    n = len(blocks)
    return full, np.sqrt((n - 1) / n * ((reps - full) ** 2).sum(0))


def phys(X, r0a, blocks=None):
    c, e = jk(X, corr, blocks)
    return np.arange(len(c)) / r0a, c * r0a ** 5, e * r0a ** 5


if __name__ == "__main__":
    dA, rA, dB, rBlo, rBhi = sys.argv[1], float(sys.argv[2]), sys.argv[3], float(sys.argv[4]), float(sys.argv[5])
    (XA, bA), (XB, bB) = load(dA), load(dB)
    tA, gA, eA = phys(XA, rA, bA)
    out = {"A": {"dir": dA, "r0a": rA, "nshards": len(XA), "t": tA.tolist(), "G": gA.tolist(), "err": eA.tolist()}}
    for tag, rB in (("B_lo", rBlo), ("B_hi", rBhi)):
        tB, gB, eB = phys(XB, rB, bB)
        # DERIVED: the log-linear interpolation needs G > 0 at both neighbouring lattice times
        ok = (gB > 0)
        at = []
        for t, g, e in zip(tA, gA, eA):
            if t > tB[ok].max() or not ok[0]:
                at.append(None)
                continue
            i = min(np.searchsorted(tB, t), len(tB) - 1)
            i = max(i, 1)
            if not (ok[i] and ok[i - 1]):
                at.append(None)
                continue
            w = (t - tB[i - 1]) / (tB[i] - tB[i - 1])
            gi = np.exp((1 - w) * np.log(gB[i - 1]) + w * np.log(gB[i]))
            ei = (1 - w) * eB[i - 1] + w * eB[i]
            at.append([t, g, e, float(gi), float(ei), float(gi / g)])
        out[tag] = {"r0a": rB, "nshards": len(XB), "t": tB.tolist(), "G": gB.tolist(), "err": eB.tolist(),
                    "matched": at}
    print(json.dumps(out, indent=1))
    for tag in ("B_lo", "B_hi"):
        print(f"# {tag} r0/a={out[tag]['r0a']}: t/r0, G_A, err, G_B, err, G_B/G_A", file=sys.stderr)
        for row in out[tag]["matched"]:
            if row:
                print("  " + "  ".join(f"{v:.4g}" for v in row), file=sys.stderr)
