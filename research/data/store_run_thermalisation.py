"""store_run_thermalisation.py -- is every shipped ensemble an equilibrium sample?

    CONFIGS=/path/to/entroptics-lattice python store_run_thermalisation.py
(or set CONFIGS once for the machine in the git-ignored local config file at the repository root)

Writes store_dat_thermalisation.csv: for every ensemble in the data release, the mean action
density the shards carry, and the equilibrium value measured independently here.

The equilibrium reference is measured rather than taken from the generation parameters. `therm`
records the sweeps a campaign ran; the sweeps required grow with both beta and volume, so
adequacy is a property of each (group, L, beta) and is established per ensemble.

Reading the store, once per shard that changed
----------------------------------------------
The stored mean is a per-shard number and the shards do not change: a release is fixed. But computing
them is the expensive half of this script -- the raw-link collection is 17 GB and its action density
has to be RECONSTRUCTED from the links, because phi is an intrinsic reduction of them. Doing that
from scratch on every run cost hours and produced the same numbers each time.

So each shard's per-configuration means are cached in a dot-file at the store root -- not under a
`configs_*` directory, so `make_manifest.py`'s discovery does not index it and it never enters a
release. The key is the shard's `(path, size, mtime)`: a build-system identity, not a cryptographic
one, chosen because hashing the store is the very cost this avoids (`make_manifest.py` takes tens of
minutes to do exactly that). Any ordinary rewrite moves the mtime, so the entry is simply not found
and the shard is re-read. The release's integrity record remains the manifest's SHA-256; this is a
speed device and nothing reads it as evidence.

Adding a collection re-runs nothing it need not
-----------------------------------------------
The reference chain is a deterministic function of `(group, L, T, beta)` and the chain settings
(`--reuse` below states the whole key). The store grows one campaign at a time, and a new campaign
is usually at couplings and volumes already measured -- so recomputing all 80 reference chains to
record three new shards is waste, and waste on a GPU. `--reuse` reads the committed artifact and
skips the chains whose key AND chain settings both already match, running only genuinely new keys.

It is a resume, not a cache of convenience: a row is reused only when `eq_method`, `eq_sweeps` and
`eq_n` in it equal the settings this run would use. Change any of those and every row is remeasured,
because the value would no longer be the one this script computes.

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

import argparse
import collections
import csv
import glob
import json
import math
import os
import time
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

# The device decision is `lattice_generator.resolve_device`, one copy shared with
# `string_tension_eq_centre` and `8_7_run_transfer_gap`: an unset request PROBES for CUDA and
# falls back to numpy, an explicit one is honoured and raises if the hardware is absent. This
# line used to read `os.environ.get("DEVICE", "cuda")` -- a third copy of the decision that
# disagreed with the other two, and that read the whole store before dying at the first
# equilibrium chain on a machine with no CUDA-linked torch.
DEVICE = G.resolve_device(os.environ.get("DEVICE"))
EQ_N = int(os.environ.get("EQ_N", "8"))            # parallel chains for the reference
EQ_SWEEPS = int(os.environ.get("EQ_SWEEPS", "120"))          # SU(N), heat-bath
EQ_SWEEPS_U1 = int(os.environ.get("EQ_SWEEPS_U1", "20000"))  # U(1), Metropolis only
EQ_EVERY = int(os.environ.get("EQ_EVERY", "20"))
# Replaced by `tolerance_sigma(n)`, which derives it from the ensemble count.
CHUNK = int(os.environ.get("CHUNK", "4"))          # raw-link shards are ~470 MB before reduction


def _per_config_mean(a):
    return np.asarray(a).reshape(a.shape[0], -1).mean(axis=1)


#: Per-shard means, keyed by `(relative path, size, mtime_ns)`. A dot-file at the store root, so
#: `make_manifest.py`'s `configs_*` discovery does not index it and it never ships.
CACHE_NAME = ".stored_means_cache.json"


def _shard_key(root, path):
    """The shard's identity for cache purposes: where it is, how big, and when it was last written.

    Not a digest, deliberately -- hashing the store is the cost this exists to avoid. Any ordinary
    rewrite changes the mtime, and a truncation or extension changes the size, so a changed shard
    misses the cache and is re-read.
    """
    st = os.stat(path)
    return f"{os.path.relpath(path, root).replace(os.sep, '/')}|{st.st_size}|{st.st_mtime_ns}"


def _load_cache(root):
    path = os.path.join(root, CACHE_NAME)
    if not os.path.exists(path):
        return {}
    try:
        with open(path, encoding="utf-8") as fh:
            return json.load(fh)
    except (json.JSONDecodeError, OSError) as e:
        # A damaged cache is not a reason to refuse: it is derived data and recomputing it is the
        # fallback. Said out loud, so a run that is slow for this reason says why.
        print(f"  cache unreadable ({type(e).__name__}); recomputing every shard", flush=True)
        return {}


def _save_cache(root, cache):
    path = os.path.join(root, CACHE_NAME)
    tmp = path + ".part"
    with open(tmp, "w", encoding="utf-8") as fh:
        json.dump(cache, fh)
    os.replace(tmp, path)          # atomic: an interrupted run leaves the previous cache intact


def stored_means(root):
    """Per (group, L, T, beta, collection): the mean action density the release ships.

    Density shards are read; raw-link shards are REDUCED, because phi is an intrinsic reduction of
    the links and cannot be read off them. Each shard's per-configuration means are cached against
    its `(path, size, mtime)`, so a re-run recomputes only what changed -- see the module docstring.
    """
    cache = _load_cache(root)
    hits = misses = 0
    acc = collections.defaultdict(list)
    for path in sorted(glob.glob(os.path.join(root, "configs_*", "*.npy"))):
        coll = os.path.basename(os.path.dirname(path))
        m = re.match(r"(u1|su2|su3)_L(\d+)_b([0-9.]+)\.s(\d+)\.npy$", os.path.basename(path))
        if not m:
            continue
        group, L, beta = m.group(1), int(m.group(2)), float(m.group(3))
        key = _shard_key(root, path)
        entry = cache.get(key)
        if entry is not None:
            T, field = int(entry["T"]), entry["field"]
            per = np.array(entry["per"], dtype=float)
            hits += 1
            note = "cached"
        else:
            a = np.load(path, mmap_mode="r")
            # DERIVED: the number of AXES says which object a shard is, as it does in
            # `aperture_reads.operator_history` -- 2 is the zero-momentum operator history `(n, T)`,
            # 5 the density field `(n, L, L, L, T)`, 7 the raw links. Arity, not a threshold.
            #
            # The operator branch is not a special case: a thermalisation read asks whether the
            # per-configuration value drifts along the chain, and for an operator shard that value is
            # the time mean of `O(t)`, which `_per_config_mean` already computes -- it flattens
            # everything after the configuration axis, and for `(n, T)` that is the time axis.
            if a.ndim == 2:
                T, field, per = a.shape[-1], "operator", _per_config_mean(a)
            # DERIVED: 5 axes is the density field `(n, L, L, L, T)`, as above.
            elif a.ndim == 5:
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
                # A shard whose shape matches nothing is SKIPPED, and a silent skip here is how an
                # ensemble ends up shipping with no thermalisation measurement while the suite stays
                # green. Say which, and say it where it is read.
                print(f"  SKIP (shape {a.shape} matches no known layout) "
                      f"{coll}/{os.path.basename(path)}", flush=True)
                continue
            cache[key] = {"T": int(T), "field": field, "per": [float(x) for x in per]}
            misses += 1
            note = "read"
        acc[(group, L, T, beta, coll, field)].append(per)
        print(f"  {note} {coll}/{os.path.basename(path)} n={per.size} mean={per.mean():.5f}",
              flush=True)
    if misses:
        _save_cache(root, cache)
    print(f"  shard means: {hits} cached, {misses} computed", flush=True)
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
    # CHOSEN: minimum independent blocks for a standard error to mean anything.
    return mu, sem, use >= 3


def tolerance_sigma(n_ensembles: int) -> float:
    """The largest |z| a set of `n_ensembles` at-equilibrium ensembles is expected to produce.

    DERIVED, NOT CHOSEN. Each ensemble contributes one standardised offset. If every one of them
    really is at equilibrium, those offsets are standard normal, and the EXPECTED LARGEST of `n`
    such draws is `sqrt(2 ln n)`. So an ensemble exceeding this is not explained by the fact that we
    looked at `n` of them, which is exactly the question the verdict asks.

    The tolerance therefore tracks how many ensembles the store ships: add ensembles and it widens,
    because a larger set produces a larger maximum by chance alone. A fixed number cannot do that. At
    the 87 ensembles currently measured it evaluates to 2.99, so no committed verdict changes --
    checked against the sigma column of the committed artifact before this replaced the chosen 3.0.
    """
    # DERIVED: a single ensemble has no multiple-comparison penalty, and log 1 = 0 would make the
    # tolerance vanish; the expected maximum of one draw is the draw itself, so fall back to the
    # one-sided unit deviation rather than zero.
    return math.sqrt(2.0 * math.log(n_ensembles)) if n_ensembles > 1 else 1.0


def previous_references():
    """Reference values from the committed artifact, keyed by `(group, L, T, beta)`.

    Only rows whose chain settings match the ones THIS run would use are offered: the reference is
    a function of the key and those settings, so a row measured under different ones is a different
    quantity and must not stand in for this one. Rows that did not converge are not offered either
    -- there is nothing to reuse.

    Returns `{}` when the artifact is absent, so a fresh clone measures everything.
    """
    if not os.path.exists(DAT):
        return {}
    out = {}
    with open(DAT, encoding="utf-8-sig", newline="") as fh:
        for r in csv.DictReader(fh):
            if r.get("verdict") == "equilibrium_not_converged":
                continue
            group = r["group"]
            want_method = "metropolis" if group == "u1" else "heatbath"
            want_sweeps = EQ_SWEEPS_U1 if group == "u1" else EQ_SWEEPS
            if (r.get("eq_method") != want_method
                    or int(r.get("eq_sweeps", -1)) != want_sweeps
                    or int(r.get("eq_n", -1)) != EQ_N):
                continue
            out[(group, int(r["L"]), int(r["T"]), float(r["beta"]))] = (
                float(r["equilibrium_mean"]), float(r["equilibrium_sem"]), True)
    return out


#: How a reference chain is named on disk, so the two phases agree without sharing a data structure.
def _refkey(group, L, T, beta) -> str:
    return f"{group}|{L}|{T}|{beta}"


def write_keys(path, acc, eq_cache):
    """Phase 1 (LOCAL, cheap): which reference chains are still missing.

    Reads the store, so it runs where the store is. It does no Monte Carlo -- it only names the work.
    """
    need = sorted({(g, L, T, b) for (g, L, T, b, _, _) in acc if (g, L, T, b) not in eq_cache})
    with open(path, "w", encoding="utf-8") as fh:
        json.dump([{"group": g, "L": L, "T": T, "beta": b} for g, L, T, b in need], fh, indent=1)
    print(f"wrote {path}: {len(need)} reference chain(s) still to compute", flush=True)
    return need


def run_references(keys_path, out_path):
    """Phase 2 (ANYWHERE): compute the reference chains named in `keys_path`.

    THIS IS THE PHASE THAT DOES NOT TOUCH THE STORE. `equilibrium` generates its own configurations,
    so by `remote_run`'s own rule it can be placed on a compute host or a GPU. Keeping it in the same
    pass as the store comparison is what pinned hours of single-core Monte Carlo to whichever machine
    happens to hold the ensembles.
    """
    keys = json.load(open(keys_path, encoding="utf-8"))
    out = {}
    if os.path.exists(out_path):
        out = json.load(open(out_path, encoding="utf-8"))
        print(f"resuming: {len(out)} chain(s) already in {out_path}", flush=True)
    for k in keys:
        name = _refkey(k["group"], k["L"], k["T"], k["beta"])
        if name in out:
            continue
        t0 = time.time()
        print(f"  chain {name} ...", flush=True)
        mu, sem, conv = equilibrium(k["group"], k["L"], k["T"], k["beta"])
        out[name] = [mu, sem, bool(conv)]
        # WRITTEN AFTER EVERY CHAIN, not at the end. A run that writes only on completion cannot be
        # observed, cannot be resumed, and discards everything if it is interrupted -- which is
        # exactly what made the previous seven-hour pass impossible to reason about.
        with open(out_path, "w", encoding="utf-8") as fh:
            json.dump(out, fh, indent=1, sort_keys=True)
        print(f"    {name}: mean={mu:.6f} sem={sem:.6f} converged={conv} ({time.time() - t0:.0f}s)",
              flush=True)
    print(f"wrote {out_path}: {len(out)} reference chain(s)", flush=True)


def load_references(path):
    """Phase 3's input: references computed elsewhere, keyed as `previous_references` keys them."""
    raw = json.load(open(path, encoding="utf-8"))
    out = {}
    for name, (mu, sem, conv) in raw.items():
        g, L, T, b = name.split("|")
        out[(g, int(L), int(T), float(b))] = (float(mu), float(sem), bool(conv))
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--reuse", action="store_true",
                    help="skip reference chains whose (group, L, T, beta) AND chain settings are "
                         "already in the committed artifact; measure only new keys")
    ap.add_argument("--emit-keys", default=None,
                    help="PHASE 1: write the reference chains still needed to this JSON and exit. "
                         "Reads the store; does no Monte Carlo.")
    ap.add_argument("--references", default=None,
                    help="PHASE 2: compute the chains named in this JSON (from --emit-keys) and "
                         "write them to --refs-out. Touches no store, so it runs anywhere.")
    ap.add_argument("--refs-out", default=None, help="where PHASE 2 writes its chains")
    ap.add_argument("--refs", default=None,
                    help="PHASE 3: use reference chains from this JSON instead of computing them")
    args = ap.parse_args()

    # PHASE 2 first: it needs neither the store nor anything else in this function.
    if args.references:
        if not args.refs_out:
            raise SystemExit("--references needs --refs-out to say where the chains go")
        run_references(args.references, args.refs_out)
        return

    root = store_path.store_root()
    print(f"store: {root}", flush=True)
    acc = stored_means(root)

    eq_cache = previous_references() if args.reuse else {}
    if eq_cache:
        print(f"reusing {len(eq_cache)} reference chain(s) from {os.path.basename(DAT)} "
              f"(same key, same chain settings)", flush=True)
    if args.refs:
        supplied = load_references(args.refs)
        eq_cache.update(supplied)
        print(f"loaded {len(supplied)} reference chain(s) from {args.refs}", flush=True)
    if args.emit_keys:
        write_keys(args.emit_keys, acc, eq_cache)
        return
    rows = []
    # DERIVED: the tolerance is the expected largest |z| across the ensembles being classified,
    # so it widens as the store grows rather than staying at a number picked once.
    tol = tolerance_sigma(len(acc))
    print(f"tolerance: sqrt(2 ln {len(acc)}) = {tol:.3f} sigma", flush=True)
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
        elif sigma < tol:
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
