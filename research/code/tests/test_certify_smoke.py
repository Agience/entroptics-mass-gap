"""The certifications import, and the wiring they were refactored onto actually resolves.

These programs read configurations and several are bigmem or gpu, so the suite cannot run them. But
most guard their entry point behind `if __name__ == "__main__"`, which means importing them executes
their module level -- the constants, the imports, and the loader wiring -- without touching an
ensemble. That is precisely where a refactor breaks: an import that does not resolve, an `OUT_CSV`
built from the wrong number of `dirname` calls, or a default argument that references a name bound
further down the file (which compiles, and raises NameError on import).

The figure scripts run their work at import and are excluded here, covered by regen_all instead.
Four of the certifications are additionally driven end to end on synthetic stores, which is the
only place their emission and refusal paths execute at all: the real reads are bigmem or gpu.
"""
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[3]
CERT = REPO / "research" / "code" / "certify"
DATA = REPO / "research" / "data"

GUARDED = sorted(p.name for p in CERT.glob("*.py")
                 if 'if __name__ == "__main__":' in p.read_text(encoding="utf-8", errors="replace"))


def _load(name: str):
    path = CERT / name
    sys.path.insert(0, str(REPO / "research" / "code"))
    try:
        spec = importlib.util.spec_from_file_location("certify_" + path.stem, path)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        return mod
    finally:
        sys.path.pop(0)


def test_the_guarded_certifications_are_importable():
    """Sanity: this file is testing something. The set should not quietly become empty."""
    assert len(GUARDED) >= 6, f"only {len(GUARDED)} guarded certifications found: {GUARDED}"


@pytest.mark.parametrize("name", GUARDED)
def test_certification_module_level_runs(name):
    """Importing runs the module level: constants, imports and loader wiring all resolve.

    The import itself is the check -- anything unresolved raises during exec_module -- and the
    returned module is asserted so the test cannot pass on a loader that silently yields nothing.
    """
    mod = _load(name)
    assert mod is not None, f"{name} imported to nothing"


@pytest.mark.parametrize("name", GUARDED)
def test_declared_output_lands_in_the_data_directory(name):
    """A certification that declares OUT_CSV points it at research/data, not somewhere else.

    OUT_CSV is built by walking up from __file__; one dirname too few or too many puts the artifact
    outside the tree, where regen_all --verify would never see it and the committed copy would go
    stale without anything objecting.
    """
    mod = _load(name)
    out = getattr(mod, "OUT_CSV", None)
    if out is None:
        pytest.skip(f"{name} declares no OUT_CSV")
    p = Path(out)
    assert p.parent == DATA, f"{name} writes to {p.parent}, not {DATA}"
    assert p.suffix == ".csv", f"{name} declares a non-csv artifact: {p.name}"
    assert p.parent.is_dir(), f"{p.parent} does not exist"


@pytest.mark.parametrize("name", ["interior_mixing_of_analytic_grid.py",
                                  "ym_crossover_confinement_of_grid.py",
                                  "gap_of_margin.py"])
def test_loader_returns_none_for_an_absent_ensemble(name):
    """Each `load` reports absence rather than raising, which is what the sweeps rely on.

    The su2 loaders were collapsed onto `aperture_reads.load_su2`; this exercises that path for real
    (an absent coupling, so no configurations are read) instead of trusting that the wiring is right.
    """
    mod = _load(name)
    load = getattr(mod, "load", None)
    assert callable(load), f"{name} has no module-level load()"
    mod.HOPS = ["/definitely/not/a/config/store"]
    import inspect
    nargs = len([p for p in inspect.signature(load).parameters.values()
                 if p.default is inspect.Parameter.empty])
    got = load(*(("su2", 16, 9.99)[:nargs] if nargs == 3 else (9.99,)))
    assert got is None, f"{name}.load returned {type(got)} for an absent ensemble; expected None"


def test_the_crossover_grid_actually_writes_its_artifact(tmp_path):
    """Run ym_crossover_confinement_of_grid end to end on a synthetic store and read the CSV back.

    The emission paths added to the certifications have never executed: the programs they live in
    read real ensembles and are bigmem or gpu. This one's read is a direct roll-and-mean over lags
    -- no covariance -- so it runs in a moment on a small lattice, which makes the whole path
    exercisable: load, per-config profiles, bootstrap, the empirical-Bernstein upper, the verdict,
    and the write.

    The synthetic configurations are noise; nothing here checks a physical value. What is being
    checked is that the program writes the artifact it claims to, with the columns and the row count
    it claims. `OUT_CSV` and `HOPS` are redirected in-process, so the committed artifact is never
    touched and no fabricated CSV can be left in research/data.
    """
    import csv
    import numpy as np

    mod = _load("ym_crossover_confinement_of_grid.py")
    L, T, n = 6, 8, 8
    betas = [0.80, 1.00, 1.20, 1.40, 1.60]
    store = tmp_path / "configs_synthetic"
    store.mkdir()
    rs = np.random.default_rng(11)
    for b in betas:
        np.save(store / f"su2_L{L}_b{b:.2f}.s000.npy",
                rs.normal(size=(n, L, L, L, T)).astype("float64"))

    out = tmp_path / "13_dat_unused_name.csv"
    mod.L, mod.MAXLAG, mod.HOPS, mod.OUT_CSV = L, L // 2, [str(store)], str(out)
    mod.main()

    assert out.exists(), "main() reported success but wrote no artifact"
    with out.open(encoding="utf-8", newline="") as fh:
        rows = list(csv.DictReader(fh))
    assert [f for f in rows[0]] == ["beta", "nconfigs", "d2_mean", "d2_boot_err", "eb_upper_999"]
    assert len(rows) == len(betas), f"wrote {len(rows)} rows for {len(betas)} couplings"
    assert [r["beta"] for r in rows] == [f"{b:.2f}" for b in betas]
    assert all(int(r["nconfigs"]) == n for r in rows)
    assert all(float(r["eb_upper_999"]) >= float(r["d2_mean"]) for r in rows), \
        "an upper confidence bound came out below the central value"


def test_the_crossover_grid_refuses_a_partial_store(tmp_path):
    """A coupling whose shards are missing is a refusal, not a shorter grid.

    The certificate's claim is that EVERY measured beta clears, so a silently smaller grid would
    still read as a pass while establishing less. This drives that branch for real.
    """
    import numpy as np

    mod = _load("ym_crossover_confinement_of_grid.py")
    L, T, n = 6, 8, 8
    store = tmp_path / "configs_synthetic"
    store.mkdir()
    rs = np.random.default_rng(12)
    for b in (0.80, 1.00, 1.20, 1.40, 1.60):
        np.save(store / f"su2_L{L}_b{b:.2f}.s000.npy",
                rs.normal(size=(n, L, L, L, T)).astype("float64"))
    mod.L, mod.MAXLAG, mod.HOPS = L, L // 2, [str(store)]
    mod.OUT_CSV = str(tmp_path / "should_not_appear.csv")
    # A coupling the sweep expects whose shards are absent. Writing a corrupt file instead would
    # test something else: np.load raises EOFError there, loudly, before the refusal is reached.
    real = mod.betas_available
    mod.betas_available = lambda: sorted(real() + [1.80])

    out = tmp_path / "should_not_appear.csv"
    with pytest.raises(BaseException) as exc:
        mod.main()
    assert "partial" in str(exc.value).lower() or "1.80" in str(exc.value), \
        f"expected a refusal naming the missing coupling, got: {exc.value!r}"
    assert not out.exists(), "a partial grid was written despite the refusal"


def _synth_store(tmp_path, specs, L=8, T=10, n=6, seed=21):
    """A configuration store of noise, named the way the loaders expect."""
    import numpy as np
    store = tmp_path / "configs_synthetic"
    store.mkdir(exist_ok=True)
    rs = np.random.default_rng(seed)
    for group, beta in specs:
        np.save(store / f"{group}_L{L}_b{beta:.2f}.s000.npy",
                rs.normal(size=(n, L, L, L, T)).astype("float64"))
    return store


def test_gap_of_margin_writes_its_aperture_table(tmp_path):
    """Run gap_of_margin end to end on a synthetic store and read the aperture table back.

    The adapter read is a Koopman/DMD operator identification, which on a real L=16 ensemble is the
    bigmem job that was OOM-killed at 8 GB -- but on an 8^3 x 10 lattice it returns in milliseconds,
    so the emission path is exercisable here: pin the confined-vacuum null, read each ensemble, take
    the verdict from the measured rows, and write.

    Noise configurations; no physical value is checked. What is checked is that the program writes
    one row per ensemble with the declared columns, and that the pinned floor read runs at all.
    """
    import csv

    mod = _load("gap_of_margin.py")
    specs = [("su2", 0.50), ("su2", 2.30), ("su3", 6.00), ("u1", 2.50)]
    store = _synth_store(tmp_path, specs)
    out = tmp_path / "aperture.csv"
    mod.HOPS, mod.OUT_CSV = [str(store)], str(out)
    mod.ENSEMBLES = [("su2", 0.50, 8, "confined (strong)"), ("su2", 2.30, 8, "confined (scaling)"),
                     ("su3", 6.00, 8, "confined"), ("u1", 2.50, 8, "U(1) Coulomb   b>bc")]
    mod.main()

    assert out.exists(), "main() completed but wrote no aperture table"
    with out.open(encoding="utf-8", newline="") as fh:
        rows = list(csv.DictReader(fh))
    assert len(rows) == len(mod.ENSEMBLES), f"{len(rows)} rows for {len(mod.ENSEMBLES)} ensembles"
    for col in ("group", "beta", "L", "ncfg", "phase", "mu", "contrast", "c1", "delta", "m_hi",
                "aperture"):
        assert col in rows[0], f"the aperture table has no {col} column"
    assert {r["aperture"] for r in rows} <= {"finite", "INFINITE"}
    assert all(r["c1"] in ("PASS", "FAIL") for r in rows)


def test_gap_of_margin_refuses_when_an_ensemble_is_absent(tmp_path):
    """A missing ensemble is a refusal: the A1 table would otherwise claim less than it appears to."""
    mod = _load("gap_of_margin.py")
    specs = [("su2", 0.50), ("su2", 2.30)]
    store = _synth_store(tmp_path, specs, seed=22)
    out = tmp_path / "should_not_appear.csv"
    mod.HOPS, mod.OUT_CSV = [str(store)], str(out)
    mod.ENSEMBLES = [("su2", 0.50, 8, "confined (strong)"), ("su2", 2.30, 8, "confined (scaling)"),
                     ("u1", 9.99, 8, "U(1) Coulomb   b>bc")]      # the last has no shards
    with pytest.raises(BaseException) as exc:
        mod.main()
    assert "partial" in str(exc.value).lower(), f"expected a refusal, got: {exc.value!r}"
    assert not out.exists(), "a partial aperture table was written despite the refusal"


def test_interior_mixing_grid_writes_its_artifact(tmp_path):
    """Run interior_mixing_of_analytic_grid end to end: the rho'(1) grid closing A1 on the crossover.

    Same trick as the crossover grid: the read is instant on a small lattice, so the pin, the
    per-beta rho'(1), the one-sided upper and the write all execute. Noise configurations -- the
    check is the artifact's shape, not its physics.
    """
    import csv

    mod = _load("interior_mixing_of_analytic_grid.py")
    betas = [0.50, 0.80, 1.00, 1.20, 1.40, 1.60]          # 0.50 doubles as the pinned null
    store = _synth_store(tmp_path, [("su2", b) for b in betas], seed=23)
    out = tmp_path / "interior.csv"
    mod.L, mod.HOPS, mod.OUT_CSV = 8, [str(store)], str(out)
    mod.main()

    assert out.exists(), "main() completed but wrote no interior grid"
    with out.open(encoding="utf-8", newline="") as fh:
        rows = list(csv.DictReader(fh))
    assert [f for f in rows[0]] == ["beta", "nconfigs", "rho1", "rho1_boot_err", "upper_999", "Delta"]
    assert len(rows) == len(betas), f"wrote {len(rows)} rows for {len(betas)} couplings"
    assert all(float(r["upper_999"]) >= float(r["rho1"]) for r in rows), \
        "a one-sided upper came out below the central value"
    # Delta = -log(rho1), the relation the column is defined by. Both are stored to six decimals,
    # so recomputing Delta from the ROUNDED rho1 carries about 5e-7/rho -- a few times 1e-6 at the
    # values this read produces. The tolerance follows the stored precision, not the maths.
    import math
    for r in rows:
        rho = float(r["rho1"])
        if 0 < rho < 1:
            tol = 5e-7 / rho + 1e-6
            assert abs(float(r["Delta"]) - (-math.log(rho))) < tol, \
                f"Delta and rho1 disagree at beta={r['beta']} beyond six-decimal rounding"


def test_interior_mixing_grid_refuses_a_partial_store(tmp_path):
    """A coupling the sweep expects whose shards are absent is a refusal, not a shorter grid."""
    mod = _load("interior_mixing_of_analytic_grid.py")
    betas = [0.50, 0.80, 1.00, 1.20, 1.40, 1.60]
    store = _synth_store(tmp_path, [("su2", b) for b in betas], seed=24)
    out = tmp_path / "should_not_appear.csv"
    mod.L, mod.HOPS, mod.OUT_CSV = 8, [str(store)], str(out)
    real = mod.betas_available
    mod.betas_available = lambda: sorted(real() + [1.90])
    with pytest.raises(BaseException) as exc:
        mod.main()
    assert "partial" in str(exc.value).lower(), f"expected a refusal, got: {exc.value!r}"
    assert not out.exists(), "a partial interior grid was written despite the refusal"


def test_the_footprint_harness_clears_only_the_projects_own_build(tmp_path):
    """`lean_axiom_footprints` targets MassGap's build products and never a dependency's.

    It has to clear something before building: `#print axioms` is emitted while a module elaborates,
    so a warm .lake replays nothing and the table comes out empty. Clearing the project's own
    outputs is cheap; clearing a package's would cost a Mathlib rebuild measured in hours. This
    builds a fake tree -- project outputs, a same-prefixed decoy under .lake/packages, and an
    unrelated library -- and checks what the harness would remove.
    """
    mod = _load("lean_axiom_footprints.py")

    lean = tmp_path / "lean"
    proj = lean / ".lake" / "build" / "lib" / "lean"
    proj.mkdir(parents=True)
    (proj / "MassGap").mkdir()
    (proj / "MassGap" / "Complete.olean").write_text("x")
    for f in ("MassGap.olean", "MassGap.trace", "MassGap.ilean"):
        (proj / f).write_text("x")
    (proj / "Unrelated.olean").write_text("x")          # another library in the same directory
    pkg = lean / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib" / "lean"
    pkg.mkdir(parents=True)
    (pkg / "MassGapLookalike.olean").write_text("x")    # same prefix, must be untouched
    (pkg / "Mathlib.olean").write_text("x")

    mod.LEAN = str(lean)
    targets = [Path(t) for t in mod.project_build_outputs()]
    names = sorted(t.name for t in targets)
    assert names == ["MassGap", "MassGap.ilean", "MassGap.olean", "MassGap.trace"], names
    assert all(".lake" + __import__("os").sep + "packages" not in str(t) for t in targets), \
        "a dependency's build was targeted"

    mod.clear_project_build(dry_run=True)
    assert (proj / "MassGap.olean").exists(), "dry run removed something"

    mod.clear_project_build()
    assert not (proj / "MassGap").exists() and not (proj / "MassGap.olean").exists()
    assert (proj / "Unrelated.olean").exists(), "an unrelated library's build was removed"
    assert (pkg / "MassGapLookalike.olean").exists(), "a package's build was removed"
    assert (pkg / "Mathlib.olean").exists(), "Mathlib's build was removed"


def test_apriori_A1_writes_its_verdict_table(tmp_path):
    """Run apriori_A1 end to end on a synthetic store and read the A1 table back.

    This is the finish-line certificate and a bigmem job on real ensembles, so its emission path had
    never executed. On an 8^3 x 10 lattice the whole path runs in moments: pin the confined-vacuum
    reference, read each ensemble, take the conjunction from the measured rows, and write.

    Noise configurations; no physical value is checked. What is checked is that the program writes
    one row per ensemble with the declared columns, and that the reference pin and the floor read
    both run. `HOP` and `OUT_CSV` are redirected in-process, so the committed artifact is untouched.
    """
    import csv

    mod = _load("apriori_A1.py")
    specs = [("su2", 0.50), ("su2", 2.30), ("su3", 6.00), ("u1", 2.50)]
    store = _synth_store(tmp_path, specs)
    out = tmp_path / "apriori.csv"
    mod.HOP, mod.OUT_CSV = str(store), str(out)
    mod.LS, mod.LREAD = (8,), 8
    mod.main()

    assert out.exists(), "main() completed but wrote no A1 table"
    with out.open(encoding="utf-8", newline="") as fh:
        rows = list(csv.DictReader(fh))
    assert len(rows) == len(specs), f"{len(rows)} rows for {len(specs)} ensembles"
    for col in ("group", "beta", "L", "nconfigs", "phase", "Delta", "xi", "mu",
                "kappa0_minus_mu", "contrast", "mu_below_kappa0", "K_signal"):
        assert col in rows[0], f"the A1 table has no {col} column"
    assert {r["mu_below_kappa0"] for r in rows} <= {"yes", "NO"}
    assert all(r["mu"] != "" for r in rows), \
        "an ensemble reached the table with no floor read; the conjunction needs both halves"


def test_apriori_A1_refuses_without_the_confined_reference(tmp_path):
    """No su2 b0.50 planes is a refusal: every read is thresholded against that floor.

    Without the reference there is no certificate, and the failure mode worth preventing is an empty
    verdict table written with exit 0.
    """
    mod = _load("apriori_A1.py")
    store = _synth_store(tmp_path, [("su2", 2.30), ("u1", 2.50)])
    mod.HOP, mod.OUT_CSV = str(store), str(tmp_path / "unused.csv")
    mod.LS, mod.LREAD = (8,), 8
    with pytest.raises(SystemExit) as e:
        mod.main()
    assert "reference" in str(e.value).lower()
    assert not (tmp_path / "unused.csv").exists(), "refused but still wrote a table"


def test_gap_refinement_invariant_writes_its_beta_sweep(tmp_path):
    """Run gap_refinement_invariant end to end on a synthetic store and read the sweep back.

    The second bigmem certificate whose emission path had never run. `HOP0` points at an empty
    directory so the two-hop loader is exercised with one hop contributing nothing, which is the
    shape the real store has for most couplings.
    """
    import csv

    mod = _load("gap_refinement_invariant.py")
    specs = [("su2", 2.00), ("su2", 2.30), ("u1", 0.90), ("u1", 2.50)]
    store = _synth_store(tmp_path, specs)
    empty = tmp_path / "empty_hop"
    empty.mkdir()
    out = tmp_path / "refinement.csv"
    mod.HOP, mod.HOP0, mod.OUT_CSV = str(store), str(empty), str(out)
    mod.SWEEP = {"su2": ([2.00, 2.30], (8,)), "u1": ([0.90, 2.50], (8,))}
    mod.main()

    assert out.exists(), "main() completed but wrote no sweep table"
    with out.open(encoding="utf-8", newline="") as fh:
        rows = list(csv.DictReader(fh))
    assert [f for f in rows[0]] == ["group", "beta", "L", "nconfigs", "Delta", "a_delta", "read"]
    assert len(rows) == len(specs), f"{len(rows)} rows for {len(specs)} couplings"
    assert {(r["group"], r["beta"]) for r in rows} == {(g, "%.2f" % b) for g, b in specs}
    assert all(float(r["a_delta"]) >= 0 for r in rows), "a negative resolution length"


def test_gap_refinement_invariant_refuses_a_partial_sweep(tmp_path):
    """A coupling that produced no row at any volume is a refusal, not a shorter sweep.

    The claim the table carries is a gap resolved throughout each scaling window, so a silently
    shorter sweep would still read as a pass.
    """
    mod = _load("gap_refinement_invariant.py")
    store = _synth_store(tmp_path, [("su2", 2.00)])
    empty = tmp_path / "empty_hop"
    empty.mkdir()
    out = tmp_path / "unused.csv"
    mod.HOP, mod.HOP0, mod.OUT_CSV = str(store), str(empty), str(out)
    mod.SWEEP = {"su2": ([2.00, 2.30], (8,))}
    with pytest.raises(SystemExit) as e:
        mod.main()
    assert "su2 b2.30" in str(e.value)
    assert not out.exists(), "refused but still wrote a table"


@pytest.mark.parametrize("name", GUARDED)
def test_certification_imports_the_way_regen_all_invokes_it(name):
    """Module level resolves with only the certify directory on sys.path -- how it is really run.

    `_load` above puts research/code on sys.path before importing, which is what a test harness can
    do and what `regen_all` cannot: it runs `python -u <script>` with cwd set to the script's own
    directory, so sys.path[0] is certify/ and a sibling module in research/code is reachable only
    through the script's own `sys.path.insert`. A script missing that line imports fine under the
    fixture and dies on the pod, which is exactly what happened to
    `ym_crossover_confinement_of_grid` on its first real run.

    `runpy.run_path` with a run_name other than `__main__` executes the module level and stops
    before the guard, so this costs an import and touches no ensemble.
    """
    import subprocess
    import sys as _sys

    r = subprocess.run(
        [_sys.executable, "-c",
         "import runpy; runpy.run_path(%r, run_name='probe')" % name],
        cwd=CERT, capture_output=True, text=True, timeout=300)
    assert r.returncode == 0, (
        f"{name} does not import when run the way regen_all runs it "
        f"(cwd=certify, no injected sys.path):\n{r.stderr[-1500:]}")


def test_the_shared_su2_loader_pools_every_hop(tmp_path):
    """`load_su2` returns shards from ALL hops, not the first that matches.

    Returning at the first hop makes a coupling's ensemble depend on the ORDER of the caller's HOPS
    rather than on what the store holds, and the callers do not agree on that order. It produced
    three different answers to "which configurations are the SU(2) L=16 beta=2.30 ensemble" -- 24,
    96 and 120 planes, for 120 that all exist -- and the thinnest read carried a deg-3 interpolant
    residual 3.9x every other coupling's, on the grid whose whole purpose is a measured modulus of
    continuity in beta.
    """
    import numpy as np
    import sys as _sys
    _sys.path.insert(0, str(REPO / "research" / "code"))
    try:
        from aperture_reads import load_su2
    finally:
        _sys.path.pop(0)

    a, b = tmp_path / "hop_a", tmp_path / "hop_b"
    a.mkdir(); b.mkdir()
    rs = np.random.default_rng(5)
    np.save(a / "su2_L6_b2.30.s000.npy", rs.normal(size=(3, 6, 6, 6, 8)).astype("float32"))
    np.save(b / "su2_L6_b2.30.s000.npy", rs.normal(size=(5, 6, 6, 6, 8)).astype("float32"))

    got = load_su2([str(a), str(b)], 6, 2.30, 10_000)
    assert got is not None and got.shape[0] == 8, (
        f"load_su2 returned {None if got is None else got.shape[0]} configs from two hops holding "
        f"3 and 5; pooling means 8, first-hop-wins means 3")

    # order is the hop list, so which configs survive `ncap` is fixed by HOPS and the filenames
    assert load_su2([str(b), str(a)], 6, 2.30, 10_000).shape[0] == 8, "pooling must not depend on hop order"
    assert load_su2([str(a), str(b)], 6, 2.30, 4).shape[0] == 4, "ncap must still cap after pooling"
    assert load_su2([str(a), str(b)], 6, 9.99, 10) is None, "an absent coupling is still None"


def test_gap_of_margin_pools_every_hop(tmp_path):
    """gap_of_margin keeps its own loader; it must pool like the shared one.

    It was the last Sec 9 reader returning at the first matching hop, while its docstring already
    said it concatenated all shards. On today's store the two agree for all eight ensembles it
    reads, so this guards against drift rather than a live discrepancy.
    """
    import numpy as np

    mod = _load("gap_of_margin.py")
    a, b = tmp_path / "hop_a", tmp_path / "hop_b"
    a.mkdir(); b.mkdir()
    rs = np.random.default_rng(6)
    np.save(a / "su2_L6_b2.30.s000.npy", rs.normal(size=(3, 6, 6, 6, 8)).astype("float64"))
    np.save(b / "su2_L6_b2.30.s000.npy", rs.normal(size=(5, 6, 6, 6, 8)).astype("float64"))
    mod.HOPS = [str(a), str(b)]

    got = mod.load("su2", 6, 2.30, ncap=10_000)
    assert got is not None and got.shape[0] == 8, (
        f"gap_of_margin.load returned {None if got is None else got.shape[0]} configs from two hops "
        f"holding 3 and 5; pooling means 8")
    assert mod.load("su2", 6, 9.99, ncap=10) is None, "an absent coupling is still None"
