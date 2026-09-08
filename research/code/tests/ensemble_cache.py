"""Disk cache for the deterministic Monte-Carlo ensembles the physics tests measure.

The generator is seeded, so `plaquette_per_config(...)` with the same arguments produces the same
numbers on every run -- and it costs 6^4 x n x therm sweeps to produce them each time.  Eight tests
in `test_generator_physics.py` were 98% of a 50-minute suite for that reason alone.  Nothing about
those numbers changes between runs, so they are computed once and kept.

What makes this safe to cache is the KEY, which covers everything the numbers depend on:

  * every generation argument (dims, beta, group, n, therm, seed, method), and
  * a fingerprint of `lattice_generator.py` itself, so any edit to the generator misses the cache
    and regenerates rather than re-serving numbers the current code would not produce, and
  * the numpy version and the `GEN_FP` / `GEN_NOR` knobs, which also move the arithmetic.

Keying on the generator's own content is what makes a hit safe: a cache keyed only on the call
arguments would serve results for a generator it had never run.

The cache is derived data and is git-ignored.  Delete the directory to force a cold run; point
`MASSGAP_ENSEMBLE_CACHE` elsewhere (a shared/persistent path) to keep it across checkouts.  Set
`MASSGAP_ENSEMBLE_CACHE=off` to disable it entirely and always regenerate.
"""
from __future__ import annotations

import hashlib
import os
from pathlib import Path

import numpy as np

_HERE = Path(__file__).resolve().parent
_GENERATOR = _HERE.parent / "lattice_generator.py"
_DEFAULT = _HERE / ".ensemble-cache"


def _cache_dir() -> Path | None:
    """The cache directory, or None when caching is switched off."""
    raw = os.environ.get("MASSGAP_ENSEMBLE_CACHE", "")
    if raw.strip().lower() in {"off", "0", "false", "none"}:
        return None
    return Path(raw) if raw.strip() else _DEFAULT


def _fingerprint() -> str:
    """Everything outside the call arguments that the generated numbers depend on."""
    src = _GENERATOR.read_bytes()
    env = "|".join(f"{k}={os.environ.get(k, '')}" for k in ("GEN_FP", "GEN_NOR"))
    return hashlib.sha256(src + f"|numpy{np.__version__}|{env}".encode()).hexdigest()


def cached(name: str, params: dict, produce):
    """Return ``produce()``, reading/writing a cache entry keyed by ``params`` + the fingerprint.

    ``produce`` is called only on a miss, so a cache hit and a cold run return the same array by
    construction -- there is no separate "cached path" that could drift from the real one.
    """
    d = _cache_dir()
    if d is None:
        return produce()
    key = hashlib.sha256(
        f"{name}|{sorted(params.items())}|{_fingerprint()}".encode()).hexdigest()[:32]
    path = d / f"{name}-{key}.npy"
    if path.exists():
        try:
            return np.load(path)
        except (OSError, ValueError):
            path.unlink(missing_ok=True)      # unreadable entry: regenerate rather than fail
    out = np.asarray(produce())
    d.mkdir(parents=True, exist_ok=True)
    # Write-then-rename, so a killed run leaves no half-written entry for the next one to load.
    # np.save is handed an open FILE, not a path: given a path not ending in .npy it appends the
    # extension itself, which silently wrote the temp file to a different name than the one being
    # renamed. A file object bypasses that entirely.
    tmp = path.with_name(path.name + ".tmp")
    with open(tmp, "wb") as fh:
        np.save(fh, out)
    os.replace(tmp, path)
    return out
