"""Every shipped ensemble is an equilibrium sample.

`store_dat_thermalisation.csv` records, per ensemble, the mean action density the release carries
and the equilibrium value measured independently by a chain run to a flat plateau and bracketed
from both a hot and a cold start. These tests assert the two agree, and name the ensembles when
they do not.

The mean action density is the probe: it is the observable these ensembles are for, it is
intensive so equilibrium does not drift with volume, and departure from equilibrium is one-sided
-- a chain sits above equilibrium, never below -- so an offset carries a direction that
distinguishes it from noise.
"""
from __future__ import annotations

import csv
from pathlib import Path

import pytest

import store_path

ARTIFACT = Path(__file__).resolve().parents[2] / "data" / "store_dat_thermalisation.csv"

def rows():
    if not ARTIFACT.exists():
        pytest.skip(f"{ARTIFACT.name} not present")
    with ARTIFACT.open(encoding="utf-8") as fh:
        return list(csv.DictReader(fh))


def test_no_shipped_ensemble_is_under_thermalised():
    """No ensemble sits above equilibrium by more than the tolerance.

    The tolerance is not the knob: an ensemble that fails is regenerated with a therm measured
    for its own (group, L, beta), and the artifact remeasured.
    """
    bad = [r for r in rows() if r["verdict"] == "under_thermalised"]
    if bad:
        lines = "\n".join(
            f"    {r['collection']:<18} L={r['L']:<3} T={r['T']:<3} beta={r['beta']:<5} "
            f"n={r['n_configs']:<4} ships {float(r['stored_mean']):.5f}, "
            f"equilibrium {float(r['equilibrium_mean']):.5f}, "
            f"+{float(r['offset']):.5f} ({r['sigma']} sigma)"
            for r in sorted(bad, key=lambda r: -float(r["sigma"])))
        pytest.fail(
            f"{len(bad)} ensemble(s) sit above the measured equilibrium:\n\n{lines}\n\n"
            f"Regenerate each with a therm measured for its own (group, L, beta), then remeasure "
            f"{ARTIFACT.name}.")


#: The only two verdicts that mean "this ensemble may ship". Everything else fails, INCLUDING a
#: verdict this file has never heard of -- the gate is written as a whitelist precisely so that
#: adding a verdict to the producer cannot quietly add a passing case here. The two are not the same
#: evidence: `at_equilibrium` compares the level against an independently measured equilibrium, and
#: `no_drift` only says a chain's two halves agree, which a chain settled in the wrong place also
#: satisfies. `test_a_drift_verdict_is_never_counted_as_a_level_verdict` keeps them apart.
PASSING = {"at_equilibrium", "no_drift"}


def test_no_verdict_outside_the_passing_set_ships():
    """Any verdict that is not one of the two passing ones fails, by name.

    Written as a whitelist rather than a list of known-bad verdicts. The earlier gates enumerate
    `under_thermalised` and `equilibrium_not_converged`; a producer that grew a third failing
    verdict -- `drifting`, `drift_untestable`, `below_equilibrium` -- would have passed all of them
    while shipping the ensemble. This cannot: it fails on anything it was not told is acceptable.
    """
    bad = [r for r in rows() if r["verdict"] not in PASSING]
    assert not bad, (
        f"{len(bad)} ensemble(s) carry a verdict that is not one of {sorted(PASSING)}:\n  "
        + "\n  ".join(f"{r['collection']:<20} L={r['L']:<3} beta={r['beta']:<5} "
                      f"{r['verdict']} ({r['sigma']} sigma, test={r.get('test', '?')})"
                      for r in sorted(bad, key=lambda r: r["verdict"])))


def test_a_drift_verdict_is_never_counted_as_a_level_verdict():
    """The artifact says which test produced each verdict, and the two never mix.

    A drift verdict is weaker evidence: it asks whether a chain was still moving, not whether it
    settled in the right place. So a row may carry `no_drift` only if its `test` column says
    `halves_drift`, and `at_equilibrium` only if it says `level_vs_reference`. Without this, a count
    of "how many ensembles are verified at equilibrium" would silently include the weaker ones.
    """
    expected = {"at_equilibrium": "level_vs_reference", "below_equilibrium": "level_vs_reference",
                "under_thermalised": "level_vs_reference", "equilibrium_not_converged":
                "level_vs_reference", "no_drift": "halves_drift", "drifting": "halves_drift",
                "drift_untestable": "halves_drift"}
    assert rows() and "test" in rows()[0], \
        "the artifact carries no `test` column, so which test produced a verdict is unrecorded"
    wrong = [r for r in rows() if expected.get(r["verdict"]) != r["test"]]
    assert not wrong, (
        "these rows pair a verdict with the wrong test, so the weaker evidence is being read as "
        "the stronger:\n  "
        + "\n  ".join(f"{r['collection']} L={r['L']} beta={r['beta']}: "
                      f"{r['verdict']} via {r['test']}" for r in wrong))


def test_every_ensemble_has_a_verdict():
    """No row is left unresolved, so a point cannot pass by never having been measured."""
    unresolved = [r for r in rows() if r["verdict"] == "equilibrium_not_converged"]
    assert not unresolved, (
        "the reference chain for these points has not flattened, so their offsets are not "
        "readable -- rerun them with more sweeps: "
        + ", ".join(f"L={r['L']} beta={r['beta']}" for r in unresolved))


def test_artifact_covers_every_ensemble_the_store_ships():
    """The reference describes the current store.

    Every ensemble in the manifest carries a measurement, so none can pass the test above by
    never having been measured.
    """
    skip = store_path.unavailable("manifest.csv")
    if skip:
        pytest.skip(skip)
    manifest = Path(store_path.store_root()) / "manifest.csv"
    with manifest.open(encoding="utf-8") as fh:
        shipped = {(r["group"], r["collection"], int(r["L"]), int(r["T"]), float(r["beta"]))
                   for r in csv.DictReader(fh)}
    covered = {(r["group"], r["collection"], int(r["L"]), int(r["T"]), float(r["beta"]))
               for r in rows()}
    missing = shipped - covered
    assert not missing, (
        f"{len(missing)} ensemble(s) are in the store's manifest but carry no thermalisation "
        f"measurement: "
        + ", ".join(f"{g} {c} L={L} beta={b}" for g, c, L, _, b in sorted(missing)))
