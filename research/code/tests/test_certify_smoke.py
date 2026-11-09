"""The certifications import, and the wiring they were refactored onto actually resolves.

These programs read configurations and several are bigmem or gpu, so the suite cannot run them. But
most guard their entry point behind `if __name__ == "__main__"`, which means importing them executes
their module level -- the constants, the imports, and the loader wiring -- without touching an
ensemble. That is precisely where a refactor breaks: an import that does not resolve, an `OUT_CSV`
built from the wrong number of `dirname` calls, or a default argument that references a name bound
further down the file (which compiles, and raises NameError on import).

The figure scripts run their work at import and are excluded here, covered by regen_all instead.
"""
from __future__ import annotations

import importlib.util
import os
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[3]
CERT = REPO / "research" / "code" / "certify"
DATA = REPO / "research" / "data"

GUARDED = sorted(p.name for p in CERT.glob("*.py")
                 if 'if __name__ == "__main__":' in p.read_text(encoding="utf-8", errors="replace"))


def _load(name: str):
    """Import a certification, leaving `sys.path` exactly as it was found.

    `pop(0)` removed whatever was at index 0 afterwards, not what was inserted. Eleven guarded
    modules insert their own directory at index 0 while executing, so the pop discarded the module's
    entry and left the test's `research/code` behind. Two consequences, and the second is a silent
    one: `sys.path` grew by one entry per load, and `research/code/certify` stayed importable for
    every later test in the file, so a test could pass only because an earlier load leaked a path.
    Saving and restoring the whole list makes each load independent of the ones before it.
    """
    path = CERT / name
    mine = str(REPO / "research" / "code")
    sys.path.insert(0, mine)
    try:
        spec = importlib.util.spec_from_file_location("certify_" + path.stem, path)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        return mod
    finally:
        # By value, not by position. A module's own insert stays: several of these import a sibling
        # lazily, inside a function, and need the entry they put there at import time to still be
        # present when that function runs. Wiping the list would break them for a different reason.
        try:
            sys.path.remove(mine)
        except ValueError:                                  # pragma: no cover - already gone
            pass


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

    The path is built by walking up from __file__; one dirname too few or too many puts the artifact
    outside the tree, where regen_all --verify would never see it and the committed copy would go
    stale without anything objecting.

    It looks at every upper-case string attribute ending in `.csv`, not only the name `OUT_CSV`: the
    name is not the property, and a script may call its path `OUT` or `OUT_EXACT`.

    The comparison is normalised. `Path(out).parent == DATA` is a string-ish compare on an
    unresolved path, so `…/certify/../../data` != `…/data` and a correct declaration would be
    reported wrong; both sides are resolved instead.
    """
    mod = _load(name)
    declared = {attr: getattr(mod, attr) for attr in dir(mod)
                if attr.isupper() and isinstance(getattr(mod, attr), str)
                and getattr(mod, attr).endswith(".csv")}
    if not declared:
        pytest.skip(f"{name} declares no .csv artifact path")
    for attr, out in sorted(declared.items()):
        p = Path(out)
        # `.resolve()` on both sides: the declaration is what is being checked, not its spelling.
        assert p.parent.resolve() == DATA.resolve(), \
            f"{name}.{attr} writes to {p.parent.resolve()}, not {DATA}"
        assert p.suffix == ".csv", f"{name}.{attr} declares a non-csv artifact: {p.name}"
        assert p.parent.is_dir(), f"{p.parent} does not exist"


def test_the_artifact_path_check_reaches_most_of_the_tree():
    """Positive control for the population, which no per-module assertion can see.

    A skip is a pass as far as a green run is concerned, and a check that skips 78% of its subjects
    reports the same word as one that checks them all. This pins the count, so narrowing the
    detection again shows up here rather than as a quieter suite.
    """
    found = 0
    for name in GUARDED:
        mod = _load(name)
        if any(a.isupper() and isinstance(getattr(mod, a), str)
               and getattr(mod, a).endswith(".csv") for a in dir(mod)):
            found += 1
    # DERIVED: 1 of the 8 guarded certifications (`lean_axiom_footprints.py`) declares a .csv
    # artifact path, measured by the loop above. The bar is set at the measured count so that losing
    # it is a failure rather than a quieter run.
    assert found >= 1, (
        f"only {found} of {len(GUARDED)} guarded certifications declare a .csv path the check can "
        "see; the measured count is 1")


def test_the_footprint_harness_clears_only_the_projects_own_build(tmp_path, monkeypatch):
    """`lean_axiom_footprints` targets MassGap's build products and never a dependency's.

    It has to clear something before building: `#print axioms` is emitted while a module elaborates,
    so a warm .lake replays nothing and the table comes out empty. Clearing the project's own
    outputs is cheap; clearing a package's would cost a Mathlib rebuild measured in hours. This
    builds a fake tree -- project outputs, a same-prefixed decoy under .lake/packages, and an
    unrelated library -- and checks what the harness would remove.
    """
    import lean_build as LB

    lean = tmp_path / "lean"
    proj = lean / ".lake" / "build" / "lib" / "lean"
    proj.mkdir(parents=True)
    (proj / "MassGap").mkdir()
    (proj / "MassGap" / "GNSHilbert.olean").write_text("x")
    for f in ("MassGap.olean", "MassGap.trace", "MassGap.ilean"):
        (proj / f).write_text("x")
    (proj / "Unrelated.olean").write_text("x")          # another library in the same directory
    pkg = lean / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib" / "lean"
    pkg.mkdir(parents=True)
    (pkg / "MassGapLookalike.olean").write_text("x")    # same prefix, must be untouched
    (pkg / "Mathlib.olean").write_text("x")

    # The live clear: `lean_build.clear_project_build` is what the footprint certificate calls.
    # Forced to its local branch, because the remote branch would clear a real build host.
    monkeypatch.setattr(LB, "LEAN", str(lean))
    monkeypatch.setattr(LB, "target", lambda: None)

    names = sorted(LB.clear_project_build(dry_run=True))
    assert names == ["MassGap", "MassGap.ilean", "MassGap.olean", "MassGap.trace"], names
    assert (proj / "MassGap.olean").exists(), "dry run removed something"

    LB.clear_project_build()
    assert not (proj / "MassGap").exists() and not (proj / "MassGap.olean").exists()
    assert (proj / "Unrelated.olean").exists(), "an unrelated library's build was removed"
    assert (pkg / "MassGapLookalike.olean").exists(), "a package's build was removed"
    assert (pkg / "Mathlib.olean").exists(), "Mathlib's build was removed"


@pytest.mark.parametrize("name", GUARDED)
def test_certification_imports_the_way_regen_all_invokes_it(name):
    """Module level resolves with only the certify directory on sys.path -- how it is really run.

    `_load` above puts research/code on sys.path before importing, which is what a test harness can
    do and what `regen_all` cannot: it runs `python -u <script>` with cwd set to the script's own
    directory, so sys.path[0] is certify/ and a sibling module in research/code is reachable only
    through the script's own `sys.path.insert`. A script missing that line imports fine under the
    fixture and dies when run as a script.

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
