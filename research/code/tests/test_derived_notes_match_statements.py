"""A `DERIVED:`/`CHOSEN:` note must account for every literal its STATEMENT carries.

This exists because six consecutive adversarial audits of the odd-constant chain found the same
defect, and never once in the terms -- always in the note. Two shapes recur: the note justifies a
numeral that reaches the lemma only through a called definition and is absent from its own statement,
or the note omits a `0` that `hN : N != 0` and `0 <= beta` put there. `test_no_undeclared_constants`
checks that a literal HAS a note; nothing checked that the note and the literal AGREE.

ONLY ONE DIRECTION IS A FAILURE. A numeral cited but absent has benign causes -- a note may name `2p`
as a concept, or say outright that a numeral lives in the proof rather than the statement, which puts
it in backticks. Prose about an absence reintroduces the string, so that direction is reported to a
reader and never fails. The other direction has no benign cause.

BASELINE is a ratchet, not a target. It may only go DOWN.

⛔ A QUIET REPORT IS NOT A PROOF THAT THE NOTES ARE RIGHT. This compares digit-runs, not meanings: a
note calling the `2` a dimension when it is a plane conversion passes here. That half is a reader's.
"""
from __future__ import annotations

import os
import subprocess
import sys
import tempfile

import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
# research/code/tests -> research/code -> research -> repo root. Three levels, not two.
REPO = os.path.dirname(os.path.dirname(os.path.dirname(_HERE)))
TOOL = os.path.join(REPO, "research", "code", "certify", "lean_derived_literals.py")

# DERIVED: measured on 2026-09-21 by running the tool over research/lean/MassGap. Not a chosen
# tolerance -- it is the count that was there when the gate was written, and the only sanctioned
# direction is down.
BASELINE = 334


def _scan_count() -> int:
    out = subprocess.run(
        [sys.executable, TOOL, "scan"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        cwd=REPO)
    # DERIVED: `0` is the tool's success exit; any other value means the scan did not run.
    assert out.returncode == 0, f"scan failed:\n{out.stdout}\n{out.stderr}"
    last = out.stdout.strip().splitlines()[-1]
    # "N declaration(s) whose note omits a literal its statement carries."
    return int(last.split()[0])


def test_notes_omitting_a_statement_literal_do_not_increase():
    n = _scan_count()
    assert n <= BASELINE, (
        f"{n} declarations have a DERIVED/CHOSEN note that omits a literal their statement "
        f"carries, up from the {BASELINE} baseline. Run "
        f"`python research/code/certify/lean_derived_literals.py scan` to see them.")
    if n < BASELINE:
        pytest.fail(
            f"{n} such declarations, BELOW the baseline of {BASELINE} -- good. "
            f"Lower BASELINE to {n} so the improvement is locked in.",
            pytrace=False)


def test_the_detector_finds_a_known_omission():
    """PROOF THAT THE GATE CAN FIRE.

    A green run above means nothing unless an omission is detectable. Build one: a statement
    carrying `4` and `0` whose note mentions only the `4`.
    """
    sys.path.insert(0, os.path.join(REPO, "research", "code", "certify"))
    import importlib

    mod = importlib.import_module("lean_derived_literals")

    src = (
        "/-- A planted omission.\n\n"
        "DERIVED: `4` is the dimension. -/\n"
        "theorem planted (t : Fin 4) (hN : N ≠ 0) : True := trivial\n"
    )
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "Planted.lean")
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(src)
        import pathlib

        rows = list(mod.analyse(pathlib.Path(path)))

    # DERIVED: `1` is the number of declarations planted in the fixture above.
    assert len(rows) == 1, f"the detector did not see the planted declaration: {rows}"
    name, _fname, _off, missing, _spurious, present = rows[0]
    assert name == "planted"
    assert "0" in missing, f"the planted omission was not reported: missing={missing}"
    assert "4" not in missing, f"the mentioned literal was wrongly reported: missing={missing}"


def test_a_field_projection_is_not_a_literal():
    """`q.1.1` and `l.2` are projections. Counting them would drown the gate in noise, and it is
    the commonest numeral-shaped token in this tree."""
    sys.path.insert(0, os.path.join(REPO, "research", "code", "certify"))
    import importlib
    import pathlib

    mod = importlib.import_module("lean_derived_literals")

    src = (
        "/-- Projections only.\n\n"
        "DERIVED: no numeral. -/\n"
        "theorem projs (q : A) : q.1.1 = q.2 := rfl\n"
    )
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "Projs.lean")
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(src)
        rows = list(mod.analyse(pathlib.Path(path)))

    assert rows == [], f"a field projection was counted as a literal: {rows}"
