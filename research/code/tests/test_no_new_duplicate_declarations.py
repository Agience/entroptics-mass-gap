"""The tree must not grow new copies of facts it already proves.

This exists because the instruction did not work. Prior-art searches get run when a task looks big
and skipped when a lemma looks small -- and a four-line helper is the MOST likely thing to already
exist, since it is what anyone would have needed. `State.map_sub` was written twice for exactly that
reason. A gate does not have a threshold below which it forgets.

BASELINE is a ratchet, not a target. It may only go DOWN. Deleting a duplicate and lowering the
number is a real improvement; raising it is how a gate becomes decoration.

⛔ A QUIET REPORT IS NOT A PROOF OF ABSENCE. The detector compares normalised STATEMENTS, so it
cannot see the same fact stated with different binder names or a permuted hypothesis order. It is the
cheap half. The expensive half is `lean_duplicate_declarations.py check NAME` before writing, and
reading.
"""
from __future__ import annotations

import os
import subprocess
import sys

import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
# research/code/tests -> research/code -> research -> repo root. Three levels, not two.
REPO = os.path.dirname(os.path.dirname(os.path.dirname(_HERE)))
TOOL = os.path.join(REPO, "research", "code", "certify",
                    "lean_duplicate_declarations.py")

# DERIVED: measured on 2026-09-21 by running the tool over research/lean/MassGap. Not a chosen
# tolerance -- it is the count that was there when the gate was written, and the only sanctioned
# direction is down.
BASELINE = 23


def _scan_count() -> int:
    out = subprocess.run(
        [sys.executable, TOOL, "scan"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        cwd=REPO)
    # DERIVED: `0` is the tool's success exit; any other value means the scan did not run.
    assert out.returncode == 0, f"scan failed:\n{out.stdout}\n{out.stderr}"
    first = out.stdout.strip().splitlines()[0]
    if first.startswith("no two distinct names"):
        return 0
    # "N statement(s) proved under more than one name:"
    return int(first.split()[0])


def test_duplicate_statements_do_not_increase():
    n = _scan_count()
    assert n <= BASELINE, (
        f"{n} statements are proved under more than one name, up from the {BASELINE} baseline. "
        f"Run `python research/code/certify/lean_duplicate_declarations.py scan` to see them, and "
        f"reuse the existing declaration instead of adding another.")
    if n < BASELINE:
        pytest.fail(
            f"{n} duplicate statements, BELOW the baseline of {BASELINE} -- good. "
            f"Lower BASELINE to {n} so the improvement is locked in.",
            pytrace=False)


def test_the_detector_finds_a_known_duplicate():
    """PROOF THE GATE CAN FIRE.

    A gate nobody has seen refuse is not known to refuse. `State.map_sub` is the case this was built
    for: it is declared DOTTED, so a name-only grep for `map_sub` reports nothing, which is part of
    why it was written twice. The query must find it by its last component.
    """
    out = subprocess.run(
        [sys.executable, TOOL, "check", "map_sub"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        cwd=REPO)
    # DERIVED: `1` is the tool's "already exists" exit, which is the refusal being demonstrated.
    assert out.returncode == 1, (
        "check exits 1 when a name already exists; it did not:\n" + out.stdout)
    assert "ALREADY EXISTS" in out.stdout
    assert "State.map_sub" in out.stdout, (
        "the dotted declaration was not matched by its last component:\n" + out.stdout)


def test_the_detector_passes_a_genuinely_new_name():
    out = subprocess.run(
        [sys.executable, TOOL, "check", "zzz_not_a_real_declaration_name"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        cwd=REPO)
    # DERIVED: `0` is the tool's success exit -- here, "nothing by that name is in the tree".
    assert out.returncode == 0, (
        "a name that does not exist must not be reported as existing:\n" + out.stdout)
