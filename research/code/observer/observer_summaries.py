"""Small summaries of the per-shard observer outputs, written to research/data/observer/.

  python observer_summaries.py slices DIR [DIR ...] > out.json
      For slice-sum directories (ed_read.py, ed_read_gpu.py, obs4_read_gpu.py; files links_*_n*.npy, each
      (chain, T)): the connected time-slice correlator in lattice units, G(D) = <S(0) S(D)>_c / L^3 with
      the ensemble mean subtracted (ed_agg.corr), and its delete-one-shard jackknife error (ed_agg.jk).
      ed_agg.py turns two of these into the physical comparison at fixed t/r0.

  python observer_summaries.py cube DIR [DIR ...] > out.json
      For cube-sum directories (cube_read_gpu.py; files links_*_n*_b*.npy, each (chain, ncubes)): the raw
      moments <X^{2p}>, p = 1..6, of the cube energy X over every cube of every chain and shard, with a
      delete-one-shard jackknife error; the per-p roots <X^{2p}>^{1/2p}; the mean, standard deviation,
      excess kurtosis and maximum of X; and P(X > mean + 6 sd).

The jackknife deletes one shard, or one chain for the per-chain shards of an SU(N) campaign
(ed_agg.blocks_of). No parameter is fitted. Every summary records its directory and shard count.
"""
import glob
import json
import os
import sys

import numpy as np

from ed_agg import blocks_of, corr, jk


def shard_files(d):
    return sorted(f for f in glob.glob(os.path.join(d, "links_*.npy")) if "tmp" not in f)


def slices(d):
    fs = shard_files(d)
    X = np.stack([np.load(f) for f in fs])  # (shard, chain, T)
    g, e = jk(X, corr, blocks_of(fs))
    return {"dir": d, "files": os.path.basename(fs[0]).split("_", 2)[-1], "nshards": len(fs),
            "nchains": X.shape[1], "T": X.shape[2], "G": g.tolist(), "err": e.tolist()}


def cube(d):
    fs = shard_files(d)
    X = np.stack([np.load(f).ravel() for f in fs])  # (shard, chains * ncubes)
    ps = np.arange(1, 7)

    def mom(Y):
        return np.array([(Y.astype(np.float64) ** (2 * p)).mean() for p in ps])  # NOT A READ: the six moments

    m, err = jk(X, mom, blocks_of(fs))
    x = X.ravel().astype(np.float64)
    mu, sd = x.mean(), x.std()
    return {"dir": d, "files": os.path.basename(fs[0]).split("_", 2)[-1], "nshards": len(fs),
            "ncubes": int(x.size), "p": ps.tolist(), "moment": m.tolist(), "moment_err": err.tolist(),
            "root": (m ** (1.0 / (2 * ps))).tolist(), "mean": mu, "sd": sd,
            "excess_kurtosis": float(((x - mu) ** 4).mean() / sd ** 4 - 3), "max": float(x.max()),
            "p_above_6sd": float((x > mu + 6 * sd).mean())}


if __name__ == "__main__":
    kind, dirs = sys.argv[1], sys.argv[2:]
    f = {"slices": slices, "cube": cube}[kind]
    print(json.dumps([f(d) for d in dirs], indent=1))
