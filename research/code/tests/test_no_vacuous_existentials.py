"""A conclusion may not bind a rate it never uses, beyond the ones already recorded.

`∃ κ : ℝ, 0 < κ ∧ Q` is equivalent to `Q` when `κ` does not occur in `Q`. A bound variable absent
from the body it binds carries no content, so such a conclusion states nothing about a rate however
the docstring reads. The test is one line: check that deleting `∃ κ, 0 < κ ∧` changes the
statement. This gate makes that rule mechanical, so the shape cannot come back unremarked.

What a failure means. Not that the theorem is wrong -- the statement is whatever it is. It means a
new conclusion has been written that appears to supply a rate and does not, so nothing downstream
may cite it for one. Either give the constant a role in the body, or add the line to the baseline
with the reason it is empty on purpose.

The baseline records debt and may only shrink, the same contract `hand_rolled_reads_baseline.txt`
carries.
"""
from __future__ import annotations

import os
import re
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
        "This shape is equivalent to dropping the existential, so the conclusion supplies no rate. Give the constant a role in the body, or record it in "
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


#: Live declarations whose conclusions bind a positive real with `∃ … 0 < … ∧` and use it.
_LIVE_SHAPE = [("ApertureFixed.lean", "reading_cluster"),
               ("ApertureFixed.lean", "gapAt_of_readingRep"),
               ("ApertureInvariance.lean", "gapAt_of_apertureInvariant")]


def _live_statement(fn: str, name: str) -> str:
    with open(os.path.join(V.LEAN, fn), encoding="utf-8") as fh:
        text = fh.read()
    for n, _ln, stmt in V._statements(text):
        if n == name:
            return stmt
    return ""


@pytest.mark.parametrize("fn,name", _LIVE_SHAPE, ids=[n for _f, n in _LIVE_SHAPE])
def test_the_scanner_sees_the_shape_it_is_for(fn, name):
    """Positive control on the tree: a live declaration carrying the shape is read and matched.

    A scanner that read no declaration would pass the ratchet forever. This pins it to live
    declarations whose conclusions bind a positive real, so the scan is shown to reach them.
    """
    stmt = _live_statement(fn, name)
    assert stmt, f"the scan did not read `{name}` in {fn}; it is not reaching the tree"
    assert V._EX.search(stmt) is not None, (
        f"`{name}` binds a positive real, but the shape pattern does not match its statement. "
        "The scanner is broken, not the tree.")


#: Every spelling Lean gives the shape `∃ k, 0 < k ∧ …`, with a vacuous body. The scanner saw only
#: the first: `[A-Za-zα-ω]` stopped at lowercase Greek so `Δ` was not a binder name, and neither the
#: parenthesised multi-binder form nor the binder-predicate sugar `∃ b > 0,` matched at all. The
#: tree holds 2, 9 and 8 occurrences of the three unseen spellings inside statements, none of them
#: vacuous — so the ratchet read clean over a population it had never examined, and a vacuous
#: conclusion written any of those three ways would have entered unremarked.
_SPELLINGS = [
    ("typed lowercase Greek", "theorem probe : ∃ κ : ℝ, 0 < κ ∧ True := sorry"),
    ("typed UPPERCASE Greek", "theorem probe : ∃ Δ : ℝ, 0 < Δ ∧ True := sorry"),
    ("parenthesised, further binders following",
     "theorem probe : ∃ (c : ℝ) (N₀ : ℕ), 0 < c ∧ True := sorry"),
    ("binder-predicate sugar", "theorem probe : ∃ b > 0, True := sorry"),
]


@pytest.mark.parametrize("label,src", _SPELLINGS, ids=[s[0] for s in _SPELLINGS])
def test_every_spelling_of_the_shape_is_seen(label, src):
    """Positive control on the pattern, not on the tree.

    The controls below pin that the scanner still finds one named declaration. None of them could
    tell that a whole spelling had gone unscanned, because a spelling the pattern cannot see
    contributes nothing to the count either way.
    """
    hits = []
    for _name, _ln, stmt in V._statements(src):
        m = V._EX.search(stmt)
        if m is None:
            continue
        var = m.group("typed") or m.group("sugar")
        body = re.split(r":=", stmt[m.end():])[0]
        if not re.search(r"(?<![\w'])" + var + r"(?![\w'])", body):
            hits.append(var)
    assert hits, f"the {label} spelling of a vacuous positive-real binder is invisible to the scan"


#: Prefixes a Lean declaration may carry before its keyword. The scan anchored on the keyword at
#: column zero, so a declaration wearing one of these was not a declaration as far as it was
#: concerned and its conclusion was never read. `research/lean/MassGap` holds 25 of the first shape
#: and 98 of the second — 129 declarations invisible to a gate whose whole job is to read
#: conclusions.
_PREFIXES = ["", "private ", "protected ", "scoped ", "@[simp] ", "noncomputable "]


@pytest.mark.parametrize("prefix", _PREFIXES, ids=[p.strip() or "bare" for p in _PREFIXES])
def test_a_prefixed_declaration_is_still_a_declaration(prefix):
    """Positive control on the declaration scan, the half the shape controls cannot reach.

    A pattern that matched no declaration at all would leave `scan()` empty, and an empty scan
    satisfies the ratchet — it is `test_the_baseline_only_shrinks` that would fire, which names the
    wrong thing. This pins the scan itself, on each prefix separately.
    """
    src = f"{prefix}theorem probe_prefixed : ∃ κ : ℝ, 0 < κ ∧ True := sorry\n"
    names = [n for n, _ln, _s in V._statements(src)]
    assert names == ["probe_prefixed"], (
        f"a declaration written `{prefix}theorem …` is invisible to the scan; every conclusion "
        f"behind that prefix goes unread. Got {names}")


@pytest.mark.parametrize("src,matches", [
    ("theorem probe : ∃ n : ℕ, 0 < n ∧ True := sorry", False),    # a natural, not a real
    ("theorem probe : ∃ κ : ℝ, 0 < κ ∧ κ < 1 := sorry", True),    # a real, and the binder is used
])
def test_the_widened_pattern_does_not_over_report(src, matches):
    """Negative control. Widening the spellings must not widen what counts as vacuous.

    Each case states whether the pattern is expected to match at all, because "no match" and "matched
    and found the binder used" are different outcomes and a loop that simply skipped a non-match
    would report both as a pass without distinguishing them.
    """
    stmts = list(V._statements(src))
    # DERIVED: the number of declarations `src` plants -- one `theorem` line per case above.
    assert len(stmts) == 1, f"the statement splitter did not yield one declaration: {stmts}"
    m = V._EX.search(stmts[0][2])
    assert (m is not None) is matches, (
        f"`{src}`: pattern match was {m is not None}, expected {matches}")
    if m is None:
        return
    var = m.group("typed") or m.group("sugar")
    body = re.split(r":=", stmts[0][2][m.end():])[0]
    assert re.search(r"(?<![\w'])" + var + r"(?![\w'])", body), (
        f"`{src}` was classified as binding a constant it never uses")


@pytest.mark.parametrize("fn,name", _LIVE_SHAPE, ids=[n for _f, n in _LIVE_SHAPE])
def test_the_rate_bearing_declarations_are_not_vacuous(fn, name):
    """Negative control: live declarations that do use the bound real must not be flagged."""
    found = _keys()
    assert f"{fn}|{name}" not in found, (
        f"`{name}` binds a positive real and uses it, but the scanner flags it as vacuous."
    )
