"""The thermalisation resume reuses a reference chain only when it is the SAME chain.

`store_run_thermalisation.py --reuse` skips re-measuring an equilibrium reference whose
`(group, L, T, beta)` is already in the committed artifact. That is sound because the reference is a
deterministic function of the key AND the chain settings -- and it is sound ONLY then. A resume that
reused a row measured with different sweeps, a different method, or a different number of parallel
chains would silently mix two quantities under one column, and every downstream verdict would inherit
the mixture with nothing to show for it.

So the interesting test is not that reuse works. It is that reuse REFUSES: each of the three settings
is perturbed in turn and the row must stop being offered. A resume that cannot be made to refuse is
not a resume, it is a cache.

The same script also caches each shard's per-configuration means, keyed by `(path, size, mtime)`,
because reconstructing the action density of a 17 GB raw-link collection is the expensive half of the
run and the shards do not change. That cache is tested the same way: a shard that has been rewritten
must MISS. A cache that returns a stale mean is worse than no cache, because the verdict it feeds is
a comparison against an independently measured equilibrium and would simply come out wrong.
"""
from __future__ import annotations

import csv
import importlib.util
import sys
from pathlib import Path

import pytest

DATA = Path(__file__).resolve().parents[2] / "data"
SCRIPT = DATA / "store_run_thermalisation.py"


def _module():
    if not SCRIPT.exists():
        pytest.skip(f"{SCRIPT.name} not present")
    spec = importlib.util.spec_from_file_location("store_run_thermalisation", SCRIPT)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


def _write(path, rows):
    """Write an artifact with exactly the columns `previous_references` reads."""
    cols = ["group", "L", "T", "beta", "collection", "field", "n_configs", "stored_mean",
            "stored_sem", "equilibrium_mean", "equilibrium_sem", "offset", "sigma", "verdict",
            "eq_method", "eq_sweeps", "eq_n"]
    with path.open("w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=cols)
        w.writeheader()
        for r in rows:
            w.writerow({c: r.get(c, "") for c in cols})


def _row(mod, **over):
    """One at-equilibrium SU(2) row carrying the settings this module would use."""
    r = dict(group="su2", L=16, T=32, beta=2.4, collection="configs_x", field="density",
             n_configs=48, stored_mean=2.2, stored_sem=0.001, equilibrium_mean=2.19,
             equilibrium_sem=0.002, offset=0.01, sigma=1.0, verdict="at_equilibrium",
             eq_method="heatbath", eq_sweeps=mod.EQ_SWEEPS, eq_n=mod.EQ_N)
    r.update(over)
    return r


# DERIVED: not a threshold -- the fixture's identity. These four values ARE the key
# (group, L, T, beta) that `_row` writes, so the assertions below look up the row they wrote.
# Nothing compares against them; changing them changes which synthetic row is used and nothing else.
KEY = ("su2", 16, 32, 2.4)


def test_a_matching_row_is_offered(tmp_path, monkeypatch):
    """The positive case, so the refusals below are not passing vacuously."""
    mod = _module()
    art = tmp_path / "store_dat_thermalisation.csv"
    _write(art, [_row(mod)])
    monkeypatch.setattr(mod, "DAT", str(art))
    refs = mod.previous_references()
    assert KEY in refs, f"a row with this module's own settings was not offered: {refs}"
    # The fourth element is HOW the reference was measured and the fifth is the bracket's half-gap.
    # A row written before the hot/cold bracket existed carries neither column: `hot_only` is what
    # its absence means -- a statement about the data, not a filler -- and the half-gap is NaN
    # because a single chain has no bracket, which is not the same as a bracket of width zero.
    mu, sem, usable, kind, half = refs[KEY]
    assert (mu, sem, usable, kind) == (2.19, 0.002, True, "hot_only")
    assert half != half, f"a hot-only row should carry no bracket width, got {half}"


@pytest.mark.parametrize("field,value", [
    ("eq_method", "metropolis"),
    ("eq_sweeps", 7),
    ("eq_n", 3),
])
def test_a_row_measured_under_different_settings_is_refused(tmp_path, monkeypatch, field, value):
    """Perturb one chain setting and the row must stop being offered.

    Each of these changes what `equilibrium()` would return, so the stored number is no longer the
    one this run is entitled to skip measuring.
    """
    mod = _module()
    art = tmp_path / "store_dat_thermalisation.csv"
    _write(art, [_row(mod, **{field: value})])
    monkeypatch.setattr(mod, "DAT", str(art))
    assert KEY not in mod.previous_references(), (
        f"a row whose {field} is {value!r} was offered for reuse; the reference is a function of "
        f"the chain settings, so reusing it would mix two quantities in one column")


def test_an_unconverged_row_is_refused(tmp_path, monkeypatch):
    """There is nothing to reuse in a chain that never flattened."""
    mod = _module()
    art = tmp_path / "store_dat_thermalisation.csv"
    _write(art, [_row(mod, verdict="equilibrium_not_converged")])
    monkeypatch.setattr(mod, "DAT", str(art))
    assert KEY not in mod.previous_references()


def test_a_missing_artifact_offers_nothing(tmp_path, monkeypatch):
    """A fresh clone measures everything rather than failing."""
    mod = _module()
    monkeypatch.setattr(mod, "DAT", str(tmp_path / "absent.csv"))
    assert mod.previous_references() == {}


def test_the_u1_branch_uses_the_u1_sweep_count(tmp_path, monkeypatch):
    """U(1) has only Metropolis and a much longer chain, so its rows carry different settings.

    Without this the `group`-dependent half of the settings check goes untested: a row could be
    offered because it matched the SU(N) settings while describing a U(1) chain.
    """
    mod = _module()
    art = tmp_path / "store_dat_thermalisation.csv"
    good = _row(mod, group="u1", L=8, T=16, beta=1.0,
                eq_method="metropolis", eq_sweeps=mod.EQ_SWEEPS_U1)
    bad = _row(mod, group="u1", L=8, T=16, beta=1.5,
               eq_method="heatbath", eq_sweeps=mod.EQ_SWEEPS)
    _write(art, [good, bad])
    monkeypatch.setattr(mod, "DAT", str(art))
    refs = mod.previous_references()
    assert ("u1", 8, 16, 1.0) in refs, "the correctly-measured U(1) row was not offered"
    assert ("u1", 8, 16, 1.5) not in refs, "a U(1) row carrying SU(N) chain settings was offered"


# ---------------------------------------------------------------------------------------------
# the per-shard means cache
# ---------------------------------------------------------------------------------------------

# DERIVED: fixture SHAPE, not a threshold. `n` and `T` are the synthetic shard's dimensions and
# nothing compares against them; they are small so the test is fast.
def _shard(path, n=3, T=4):
    """A tiny density shard of shape (n, 2, 2, 2, T), whose per-config means are 0, 1, 2, ..."""
    import numpy as np
    a = np.zeros((n, 2, 2, 2, T), dtype="float32")
    for i in range(n):
        a[i] = float(i)
    np.save(path, a)


def test_a_shard_is_read_once_and_cached(tmp_path):
    """The positive case: a second call over an unchanged store reads nothing."""
    mod = _module()
    coll = tmp_path / "configs_t"
    coll.mkdir()
    _shard(coll / "su2_L2_b2.40.s000.npy")

    first = mod.stored_means(str(tmp_path))
    assert (tmp_path / mod.CACHE_NAME).exists(), "no cache was written"
    second = mod.stored_means(str(tmp_path))

    (k1,), (k2,) = list(first), list(second)
    assert k1 == k2
    assert list(first[k1][0]) == list(second[k2][0]), "the cached means differ from the read ones"


def test_a_rewritten_shard_misses_the_cache(tmp_path):
    """The refusal: change the shard and the cached mean must not be returned.

    Without this the cache could key on the path alone and nothing would notice -- the run would be
    fast and the verdict would be a comparison against the previous release's numbers.
    """
    import numpy as np
    mod = _module()
    coll = tmp_path / "configs_t"
    coll.mkdir()
    shard = coll / "su2_L2_b2.40.s000.npy"
    _shard(shard)

    before = mod.stored_means(str(tmp_path))
    (k,) = list(before)
    # DERIVED: the fixture's own mean. `_shard` writes configurations 0, 1, 2, so their mean IS 1.
    assert float(np.mean(before[k][0])) == 1.0, before[k][0]

    # rewrite it with different content, and move the mtime so the key changes as it would in life
    a = np.full((3, 2, 2, 2, 4), 7.0, dtype="float32")
    np.save(shard, a)
    import os
    st = os.stat(shard)
    os.utime(shard, ns=(st.st_atime_ns + 10 ** 9, st.st_mtime_ns + 10 ** 9))

    after = mod.stored_means(str(tmp_path))
    (k2,) = list(after)
    # DERIVED: the value the rewrite just wrote. Not a tolerance -- an identity check.
    assert float(np.mean(after[k2][0])) == 7.0, (
        "a rewritten shard returned its previous mean; the cache key does not detect a rewrite")


def test_an_unreadable_cache_recomputes_rather_than_failing(tmp_path):
    """Derived data: a damaged cache costs time, never an answer."""
    mod = _module()
    coll = tmp_path / "configs_t"
    coll.mkdir()
    _shard(coll / "su2_L2_b2.40.s000.npy")
    (tmp_path / mod.CACHE_NAME).write_text("{not json", encoding="utf-8")

    out = mod.stored_means(str(tmp_path))
    (k,) = list(out)
    import numpy as np
    # DERIVED: the fixture's own mean, as above.
    assert float(np.mean(out[k][0])) == 1.0


def test_the_cache_is_invisible_to_the_manifest(tmp_path):
    """The cache must not enter a release.

    `make_manifest.py` indexes every `configs_*` directory holding shards; the cache sits at the
    store ROOT and is dot-prefixed, so it is outside that enumeration. Asserted rather than assumed,
    because "it is not in a configs_ directory" is a property of the name and names get changed.
    """
    mod = _module()
    assert mod.CACHE_NAME.startswith("."), mod.CACHE_NAME
    assert not mod.CACHE_NAME.startswith("configs_"), mod.CACHE_NAME
    assert not mod.CACHE_NAME.endswith(".npy"), mod.CACHE_NAME
