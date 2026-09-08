"""store_run_thermalisation.py -- is every shipped ensemble an equilibrium sample?

    CONFIGS=/path/to/entroptics-lattice python store_run_thermalisation.py
(or set CONFIGS once for the machine in the git-ignored local config file at the repository root)

Writes store_dat_thermalisation.csv: for every ensemble in the data release, the mean action
density the shards carry, and the equilibrium value measured independently here.

The equilibrium reference is measured rather than taken from the generation parameters. `therm`
records the sweeps a campaign ran; the sweeps required grow with both beta and volume, so
adequacy is a property of each (group, L, beta) and is established per ensemble.

Why the mean action density
---------------------------
It is the observable these ensembles are FOR; it is intensive, so equilibrium does not drift
with volume and a flat-in-L reference is meaningful; and departure from equilibrium is one-sided
-- a chain sits ABOVE equilibrium, never below -- so an offset carries a direction that
distinguishes it from noise.

Heat-bath is used for the reference wherever the group offers it (SU(N)), because it reaches the
same distribution roughly 40x faster and that is what makes measuring every point affordable;
U(1) has only Metropolis and takes correspondingly longer chains. Convergence is checked from the
trace rather than assumed, and a point whose chain has not flattened is written out as
`equilibrium_not_converged` rather than given a value.
"""
from __future__ import annotations

import collections
import csv
import glob
import os
import re
import sys

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(_HERE, "..", "code")))
import lattice_generator as G                                              # noqa: E402
import store_path                                                          # noqa: E402
import table                                                               # noqa: E402

DAT = os.path.join(_HERE, "store_dat_thermalisation.csv")
COLS = ["group", "L", "T", "beta", "collection", "field", "n_configs", "stored_mean", "stored_sem",
        "equilibrium_mean", "equilibrium_sem", "offset", "sigma", "verdict",
        "eq_method", "eq_sweeps", "eq_n"]

DEVICE = os.environ.get("DEVICE", "cuda")
EQ_N = int(os.environ.get("EQ_N", "8"))            # parallel chains for the reference
EQ_SWEEPS = int(os.environ.get("EQ_SWEEPS", "120"))          # SU(N), heat-bath
EQ_SWEEPS_U1 = int(os.environ.get("EQ_SWEEPS_U1", "20000"))  # U(1), Metropolis only
EQ_EVERY = int(os.environ.get("EQ_EVERY", "20"))
TOL_SIGMA = float(os.environ.get("TOL_SIGMA", "3"))
CHUNK = int(os.environ.get("CHUNK", "4"))          # raw-link shards are ~470 MB before reduction


def _per_config_mean(a):
    return np.asarray(a).reshape(a.shape[0], -1).mean(axis=1)


def stored_means(root):
    """Per (group, L, T, beta, collection): the mean action density the release ships.

    Density shards are read; raw-link shards are REDUCED, because phi is an intrinsic reduction of
    the links and cannot be read off them.
    """
    acc = collections.defaultdict(list)
    for path in sorted(glob.glob(os.path.join(root, "configs_*", "*.npy"))):
        coll = os.path.basename(os.path.dirname(path))
        m = re.match(r"(u1|su2|su3)_L(\d+)_b([0-9.]+)\.s(\d+)\.npy$", os.path.basename(path))
        if not m:
            continue
        group, L, beta = m.group(1), int(m.group(2)), float(m.group(3))
        a = np.load(path, mmap_mode="r")
        if a.ndim == 5:
            T, field, per = a.shape[-1], "density", _per_config_mean(a)
        elif a.ndim == 7:
            T, field = a.shape[4], "links"
            parts = []
            for i in range(0, a.shape[0], CHUNK):
                q = np.asarray(a[i:i + CHUNK], dtype="float64")
                parts.append(_per_config_mean(np.asarray(
                    G.action_density(q, group=group, device=None))))
            per = np.concatenate(parts)
        else:
            continue
        acc[(group, L, T, beta, coll, field)].append(per)
        print(f"  read {coll}/{os.path.basename(path)} n={per.size} mean={per.mean():.5f}",
              flush=True)
    return acc


def equilibrium(group, L, T, beta):
    """(mean, sem, converged) from a chain run to a flat tail.

    The tail is extended backwards while each added measurement stays within 2 sigma of the
    running mean, so a chain that is still drifting cannot contribute a value.

    SU(N) uses heat-bath; U(1) has only Metropolis, which reaches the same distribution over a
    longer chain, so it gets `EQ_SWEEPS_U1` sweeps rather than `EQ_SWEEPS`.
    """
    method = "metropolis" if group == "u1" else "heatbath"
    sweeps = EQ_SWEEPS_U1 if group == "u1" else EQ_SWEEPS
    init, sweep, action, dstep = G._ops(group, method)
    dims = (L, L, L, T)
    b = G._Backend(DEVICE).seed(0)
    link = init(b, dims, G._batch_tuple(EQ_N))
    trace = []
    for s in range(1, sweeps + 1):
        sweep(b, link, dims, beta, dstep)
        if s % EQ_EVERY:
            continue
        phi = action(b, link)
        a = phi.detach().cpu().numpy() if hasattr(phi, "detach") else np.asarray(phi)
        per = _per_config_mean(a.reshape(EQ_N, -1))
        trace.append((float(per.mean()), float(per.std(ddof=1) / np.sqrt(EQ_N))))
    vals = [m for m, _ in trace]
    sems = [s for _, s in trace]
    use = 2
    while use < len(vals):
        mu = float(np.mean(vals[-use:]))
        if abs(vals[-(use + 1)] - mu) > 2 * max(float(np.mean(sems[-use:])), 1e-9):
            break
        use += 1
    mu = float(np.mean(vals[-use:]))
    sem = float(np.mean(sems[-use:]) / np.sqrt(use))
    return mu, sem, use >= 3


def main():
    root = store_path.store_root()
    print(f"store: {root}", flush=True)
    acc = stored_means(root)

    eq_cache = {}
    rows = []
    for (group, L, T, beta, coll, field), chunks in sorted(acc.items()):
        v = np.concatenate(chunks)
        mean = float(v.mean())
        sem = float(v.std(ddof=1) / np.sqrt(v.size))
        if (group, L, T, beta) not in eq_cache:
            print(f"  equilibrium {group} L={L} T={T} beta={beta} ...", flush=True)
            eq_cache[(group, L, T, beta)] = equilibrium(group, L, T, beta)
        eqm, eqsem, converged = eq_cache[(group, L, T, beta)]
        off = mean - eqm
        sigma = abs(off) / np.sqrt(sem ** 2 + eqsem ** 2)
        if not converged:
            verdict = "equilibrium_not_converged"
        elif sigma < TOL_SIGMA:
            verdict = "at_equilibrium"
        else:
            verdict = "under_thermalised" if off > 0 else "below_equilibrium"
        rows.append(dict(group=group, L=L, T=T, beta=beta, collection=coll, field=field,
                         n_configs=int(v.size), stored_mean=round(mean, 6),
                         stored_sem=round(sem, 6), equilibrium_mean=round(eqm, 6),
                         equilibrium_sem=round(eqsem, 6), offset=round(off, 6),
                         sigma=round(float(sigma), 1), verdict=verdict,
                         eq_method=("metropolis" if group == "u1" else "heatbath"),
                         eq_sweeps=(EQ_SWEEPS_U1 if group == "u1" else EQ_SWEEPS), eq_n=EQ_N))
        print(f"  {group:>3} L={L:>2} T={T:>2} b={beta:<5} {coll:<20} {mean:.5f} vs {eqm:.5f} "
              f"({sigma:.1f} sigma) {verdict}", flush=True)

    rows.sort(key=lambda r: (r["group"], r["L"], r["beta"], r["collection"]))
    table.write(DAT, rows, COLS)
    bad = [r for r in rows if r["verdict"] == "under_thermalised"]
    print(f"\nwrote {DAT}: {len(rows)} ensembles, {len(bad)} under-thermalised")


if __name__ == "__main__":
    main()
