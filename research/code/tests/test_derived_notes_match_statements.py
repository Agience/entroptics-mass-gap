"""A `DERIVED:`/`CHOSEN:` note must account for every literal its statement carries.

This exists because six consecutive adversarial audits of the odd-constant chain found the same
defect, and never once in the terms -- always in the note. Two shapes recur: the note justifies a
numeral that reaches the lemma only through a called definition and is absent from its own statement,
or the note omits a `0` that `hN : N != 0` and `0 <= beta` put there. `test_no_undeclared_constants`
checks that a literal has a note; nothing checked that the note and the literal agree.

Only one direction is a failure. A numeral cited but absent has benign causes -- a note may name `2p`
as a concept, or say outright that a numeral lives in the proof rather than the statement, which puts
it in backticks. Prose about an absence reintroduces the string, so that direction is reported to a
reader and never fails. The other direction has no benign cause.

One exemption: the structural numerals `0`, `1`, `2` and `4`. The rule is that every number is
measured or structural, and only a measured number needs a label. These four are the index origin and
additive unit (so the `0` of `hN : N != 0` above is now structural), the multiplicative unit and
successor step, the square and the arity of a pair, and the spacetime dimension `Fin 4`: each is fixed
by the shape of the statement, not by a reading or a choice. The set and its reason live once, in
`research/code/certify/structural_numerals.py`, which `test_no_undeclared_lean_constants` also reads.
The exemption removes only those four from the failing direction; any other numeral in a statement
that the note does not cite still fails, and a cited-but-absent numeral is still reported.

BASELINE is a ratchet, not a target. It may only go down.

⛔ A quiet report is not a proof that the notes are right. This compares digit-runs, not meanings: a
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

# DERIVED: measured by running the tool over research/lean/MassGap. Not a chosen tolerance -- it is
# the count the tree carries, and the only sanctioned direction is down. It is 0.
#
# At zero the ratchet no longer guards against blindness. The `n < BASELINE` branch below cannot
# fire when BASELINE is 0, because a count is never negative -- so "checked both ways" stops being
# true at exactly the value where a scanner that stopped seeing anything would report success. What
# guards it instead is `test_the_detector_finds_a_known_omission`, which plants an omission and
# requires it to be reported, and `test_the_scanner_still_sees_the_tree` below, which requires the
# scan to have declarations to look at in the first place.
BASELINE = 0

#: DERIVED: the tree carries about 5,600 top-level declarations; `5000` is a floor well under that
#: and far above zero, so it detects a scanner that has stopped matching without tracking the
#: tree's exact size. Measured with `lean_derived_literals.DECL` over research/lean/MassGap.
_DECLARATION_FLOOR = 5000


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
    """Proof that the gate can fire.

    A green run above means nothing unless an omission is detectable. Build one: a statement
    carrying `5` and `3` whose note mentions only the `5`. Neither is structural, so the exemption
    cannot be what hides it; the structural `0` and `4` beside them must not be reported.
    """
    sys.path.insert(0, os.path.join(REPO, "research", "code", "certify"))
    import importlib

    mod = importlib.import_module("lean_derived_literals")

    src = (
        "/-- A planted omission.\n\n"
        "DERIVED: `5` is the window. -/\n"
        "theorem planted (s : Fin 4) (t : Fin 5) (hN : N ≠ 0) (h3 : N ≠ 3) : True := trivial\n"
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
    assert missing == ["3"], f"the planted omission was not reported alone: missing={missing}"


def test_structural_numerals_are_exempt_and_a_cited_absent_numeral_is_still_seen():
    """The exemption is exactly `0`, `1`, `2`, `4`, and it touches only the failing direction.

    A statement carrying only structural numerals, under a note that cites none, is clean. A note
    citing a numeral the statement does not carry is still reported as cited-but-absent.
    """
    sys.path.insert(0, os.path.join(REPO, "research", "code", "certify"))
    import importlib
    import pathlib

    mod = importlib.import_module("lean_derived_literals")
    assert mod.STRUCTURAL_NUMERALS == frozenset({"0", "1", "2", "4"})

    src = (
        "/-- Structural only.\n\n"
        "DERIVED: no measured numeral. -/\n"
        "theorem structural (s : Fin 4) (hN : N ≠ 0) (h : x ^ 2 = 1) : True := trivial\n\n"
        "/-- A wrong citation.\n\n"
        "DERIVED: `73` is the read. -/\n"
        "theorem wrong (s : Fin 4) : True := trivial\n"
    )
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "Exempt.lean")
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(src)
        rows = {r[0]: r for r in mod.analyse(pathlib.Path(path))}

    assert "structural" not in rows, f"a structural numeral was reported: {rows.get('structural')}"
    assert "wrong" in rows and rows["wrong"][4] == ["73"], (
        f"a cited numeral absent from the statement was not reported: {rows.get('wrong')}")


def test_the_scanner_still_sees_the_tree():
    """Proof that a zero count means clean and not blind.

    The ratchet above cannot distinguish "no declaration omits a literal" from "no declaration was
    scanned" once BASELINE reaches 0, because a count is never negative. This asserts the scanner
    matches the tree's declarations at all.

    It is the same defect class this repo has already hit twice: an ASCII-only name class made a
    gate report clean over a population it never looked at. So the guard is on the population, not
    on the finding.
    """
    sys.path.insert(0, os.path.join(REPO, "research", "code", "certify"))
    import importlib
    import pathlib

    mod = importlib.import_module("lean_derived_literals")
    lean = pathlib.Path(REPO) / "research" / "lean" / "MassGap"
    names = set()
    for p in sorted(lean.glob("*.lean")):
        for _kind, name in mod.DECL.findall(p.read_text(encoding="utf-8", errors="replace")):
            names.add(name)
    assert len(names) >= _DECLARATION_FLOOR, (
        f"the scanner matched only {len(names)} declarations, under the floor of "
        f"{_DECLARATION_FLOOR}. A zero offender count from this scan cannot be trusted: the "
        "scanner is not seeing the tree.")
    # The Greek-initial ones specifically, since an ASCII start class is how this broke before.
    for greek in ("Δ_shift", "Δ_corner0", "Φ_axis"):
        assert greek in names, f"{greek} is invisible to the scanner; its note is unchecked"


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
