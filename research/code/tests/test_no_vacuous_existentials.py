"""A conclusion may not bind a rate it never uses, beyond the ones already recorded.

`VolumeRate.exists_pos_and_iff` machine-checks that `∃ κ : ℝ, 0 < κ ∧ Q` is equivalent to `Q`. A
bound variable absent from the body it binds carries no content, so such a conclusion states nothing
about a RATE however the docstring reads. `VolumeRate.lean`'s header gives the test in one line --
*check that deleting `∃ κ, 0 < κ ∧` changes the statement* -- and then says DO NOT REINTRODUCE THE
PATTERN.

THAT RULE WAS PROSE, AND PROSE DOES NOT RUN. A sweep on 2026-09-22 found six docstrings claiming
"a single rate `κ > 0`" over conclusions of exactly this shape, two of them contradicting their own
file headers, and the same claim had reached PAPER.md. The repair fixed the sentences; this gate
stops the shape coming back unremarked.

WHAT A FAILURE MEANS. Not that the theorem is wrong -- the statement is whatever it is. It means a
new conclusion has been written that appears to supply a rate and does not, so nothing downstream
may cite it for one. Either give the constant a role in the body, or add the line to the baseline
with the reason it is empty on purpose.

THE BASELINE RECORDS DEBT AND MAY ONLY SHRINK, the same contract `hand_rolled_reads_baseline.txt`
carries.
"""
from __future__ import annotations

import os
import sys

import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(_HERE), "certify"))

import lean_vacuous_existentials as V  # noqa: E402


def _keys():
    return {f"{fn}|{name}" for fn, _, name, _ in V.scan()}


def test_no_new_vacuous_existential_conclusions():
    found = _keys()
    baseline = V._baseline()
    new = sorted(found - baseline)
    assert not new, (
        f"{len(new)} conclusion(s) bind a positive real they never use, and are not in the "
        f"baseline:\n  " + "\n  ".join(new) + "\n\n"
        "`VolumeRate.exists_pos_and_iff` proves this shape equivalent to dropping the existential, "
        "so the conclusion supplies no rate. Give the constant a role in the body, or record it in "
        "`vacuous_existentials_baseline.txt` with the reason it is empty on purpose."
    )


def test_the_baseline_only_shrinks():
    """Every recorded line must still be a real hit; a stale line hides a repair."""
    found = _keys()
    baseline = V._baseline()
    stale = sorted(baseline - found)
    assert not stale, (
        "the baseline names conclusions that no longer bind an unused constant:\n  "
        + "\n  ".join(stale) + "\n\nRemove them -- the file records debt, and debt that is paid "
        "should leave it."
    )


def test_the_scanner_sees_the_shape_it_is_for():
    """Positive control: `VolumeRate.exists_pos_and_iff` IS the shape, so it must be found.

    A scanner that reported nothing would pass the ratchet forever. This pins it to the one
    declaration in the tree written to exhibit the pattern.
    """
    found = _keys()
    assert "VolumeRate.lean|exists_pos_and_iff" in found, (
        "the scanner no longer finds `exists_pos_and_iff`, which is the tree's own statement OF the "
        "vacuous shape. The scanner is broken, not the tree."
    )


@pytest.mark.parametrize("name", ["gap_rate_uniform_in_volume",
                                  "gap_rate_at_floor_uniform_in_volume",
                                  "product_volume_gap_rate"])
def test_the_rate_bearing_replacements_are_not_vacuous(name):
    """Negative control: the declarations that DO state a rate must not be flagged.

    If these ever appear, the replacement is no better than what it replaced.
    """
    found = _keys()
    assert f"VolumeRate.lean|{name}" not in found, (
        f"`{name}` is cited as the rate-bearing form, but its conclusion binds a constant it never "
        "uses. Then it states no rate either."
    )
