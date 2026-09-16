"""`remote_run` must ship the whole tree it runs, and must never ship a run that needs the store.

Two failure modes, both silent:

  * a Python file under ``research/`` that `SOURCE_GLOBS` does not cover is never pushed, so a remote
    run imports whatever stale copy the host happens to hold -- and the output looks exactly like a
    correct run of a tree that does not exist here;
  * a script that READS the ensemble store, dispatched to a host that does not have it, reads an empty
    directory. `store_path` refuses when the store is absent, but a refusal on a compute host arrives
    as a failed run with a confusing message rather than as "this one runs locally".

Neither is caught by running the wrapper, because both produce a process that starts.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

CODE = Path(__file__).resolve().parents[1]
RESEARCH = CODE.parent
sys.path.insert(0, str(CODE))

import remote_run as RR  # noqa: E402


def _covered() -> set[Path]:
    out: set[Path] = set()
    for g in RR.SOURCE_GLOBS:
        out |= {p.resolve() for p in RESEARCH.glob(g)}
    return out


def test_every_python_file_under_research_is_shipped():
    """No Python file the tree carries is left behind by a push.

    Enumerated from disk rather than from a list, for the reason the store manifest is: a list of
    directories is an inventory and goes stale the next time one is added.
    """
    on_disk = {p.resolve() for p in RESEARCH.rglob("*.py")
               if "__pycache__" not in p.parts and ".lake" not in p.parts}
    missing = sorted(str(p.relative_to(RESEARCH)).replace("\\", "/") for p in on_disk - _covered())
    assert not missing, (
        f"{len(missing)} Python file(s) under research/ are not covered by remote_run.SOURCE_GLOBS, "
        f"so a remote run would use whatever the host already had: {missing}. Add the directory's "
        f"glob to SOURCE_GLOBS.")


def test_the_globs_ship_nothing_outside_the_tree():
    """Every covered path is inside `research/`, so a push cannot reach the rest of the workspace."""
    outside = [p for p in _covered() if RESEARCH not in p.parents and p.parent != RESEARCH]
    assert not outside, f"SOURCE_GLOBS reaches outside research/: {outside}"


def test_a_store_reading_script_runs_locally_even_with_a_host_configured(monkeypatch):
    """`needs_store=True` must not dispatch, whatever is configured.

    Asserted by watching which branch runs rather than by reading the code: the remote branch is
    replaced with something that fails loudly, so taking it cannot pass quietly.
    """
    monkeypatch.setattr(RR, "target", lambda: "someone@somewhere:22")

    def _boom(*a, **k):
        raise AssertionError("a store-reading script was dispatched to a compute host")

    monkeypatch.setattr(RR, "push_sources", _boom)
    monkeypatch.setattr(RR, "_ssh_argv", _boom)

    calls = {}

    def _fake_run(argv, **kw):
        calls["argv"] = argv
        calls["cwd"] = kw.get("cwd")

        class R:
            returncode = 0
            stdout = ""
            stderr = ""
        return R()

    monkeypatch.setattr(RR.subprocess, "run", _fake_run)
    RR.run("code/remote_run.py", needs_store=True)
    assert calls["argv"][0] == sys.executable, calls["argv"]
    assert Path(calls["cwd"]).resolve() == RESEARCH.resolve()


def test_a_missing_script_is_refused_rather_than_dispatched(monkeypatch):
    """A typo must not become a remote command line.

    Without this the wrapper would happily ssh `python no/such/file.py` and report the host's
    error, which reads as an environment problem rather than as a name that does not exist here.
    """
    monkeypatch.setattr(RR, "target", lambda: "someone@somewhere:22")
    with pytest.raises(SystemExit) as exc:
        RR.run("certify/definitely_not_a_script.py")
    assert "no such script" in str(exc.value).lower()


@pytest.mark.parametrize("spelling", ["certify/gap_of_maximal_correlation.py",
                                      "code/certify/gap_of_maximal_correlation.py"])
def test_both_spellings_of_a_certificate_resolve(spelling, monkeypatch):
    """Certificates live under `code/` and figure scripts under `data/`, so callers spell both ways."""
    monkeypatch.setattr(RR, "target", lambda: None)
    seen = {}

    def _fake_run(argv, **kw):
        seen["argv"] = argv

        class R:
            returncode = 0
            stdout = ""
            stderr = ""
        return R()

    monkeypatch.setattr(RR.subprocess, "run", _fake_run)
    RR.run(spelling)
    assert "code/certify/gap_of_maximal_correlation.py" in seen["argv"]


def test_describe_names_the_target_without_running_anything(monkeypatch):
    """`--describe` is what a caller prints before a long run; it must not touch the network."""
    monkeypatch.setattr(RR, "target", lambda: None)
    assert RR.describe() == "compute target: local"
    monkeypatch.setattr(RR, "target", lambda: "u@h:2222")
    monkeypatch.setattr(RR, "_cfg", lambda k, d=None: {"COMPUTE_DIR": "research",
                                                       "COMPUTE_PY": "py"}.get(k, d))
    assert "u@h:2222" in RR.describe()
