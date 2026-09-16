"""A tail check must be handed the shift its certificate uses, never the module default.

THE DEFECT THIS PREVENTS. A certificate is an inertia claim AT A SHIFT. The cover's two walks
certify at shifts they compute per coupling -- the absolute walk at a bisected `M` running to about
0.84, the relative route at its own Sturm shift, which is NEGATIVE above lam ~ 2.6 and reaches about
-5. Both nonetheless asked the tail question at `MU_DEFAULT = 0.2747`, a shift neither uses. The
relative half was then asking whether an absolute certificate that does not exist there would survive
its tail, and answering yes.

Nothing caught it because every part was individually right: the pivots were exact, the walk ran, the
gap values did not overstate, and the predicate returned True. Only the JOIN was wrong -- the check
and the thing checked were parameterised differently.

WHY AN AST TEST AND NOT A GREP. The rule is about which expression reaches a particular ARGUMENT
POSITION, and a regex over call text cannot see argument positions through line breaks, keyword
arguments or renamings. It would also miss the case that matters most: someone adding a NEW call.
"""
from __future__ import annotations

import ast
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[3]
CERT = REPO / "research" / "code" / "certify" / "cell_pivot_certificate.py"

#: The functions whose shift argument must be the certificate's own, and where that argument sits.
#: Both take `(jmax, lam, shift, ...)`, so the shift is positional index 2.
SHIFT_ARG = {"tail_lifts": 2, "pivots_with_tail": 2}

#: The name that must never appear there. It is the DEFAULT shift -- fine as a CLI default and fine
#: as the absolute route's shift when that is what the certificate used, but a tail check that names
#: it directly is a check that did not ask what the certificate did.
FORBIDDEN = "MU_DEFAULT"


def _calls(tree):
    for node in ast.walk(tree):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            yield node


def test_no_tail_check_is_handed_the_default_shift():
    tree = ast.parse(CERT.read_text(encoding="utf-8"))
    checked, bad = 0, []
    for call in _calls(tree):
        pos = SHIFT_ARG.get(call.func.id)
        if pos is None:
            continue
        checked += 1
        if len(call.args) <= pos:
            bad.append((call.func.id, call.lineno, "fewer arguments than the shift position"))
            continue
        arg = call.args[pos]
        if isinstance(arg, ast.Name) and arg.id == FORBIDDEN:
            bad.append((call.func.id, call.lineno,
                        f"shift argument is `{FORBIDDEN}`, not the shift this certificate uses"))
    assert not bad, (
        "a tail check is parameterised by the default shift rather than the certifying one:\n"
        + "\n".join(f"  {CERT.name}:{ln}  {fn}(): {why}" for fn, ln, why in bad))
    # DERIVED: the two cover walks, the CSV writer and the emitter's guard are four call sites; a
    # scan that found fewer is not seeing the file and would pass vacuously.
    assert checked >= 4, (
        f"only {checked} tail-check call(s) found in {CERT.name}; the scan is not seeing the call "
        f"sites it is meant to police and would pass whatever they said")


def test_the_retired_predicate_is_gone():
    """`tail_is_safe` asked whether the pivot SIGNS agree, which is not what the theorem needs.

    It returned "safe" where both sequences carried three negatives -- agreement about a certificate
    that does not exist. It is replaced by `tail_lifts`, and the point of retiring rather than
    deprecating it is that two predicates answering almost the same question is how the wrong one
    gets called.
    """
    src = CERT.read_text(encoding="utf-8")
    tree = ast.parse(src)
    defined = {n.name for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)}
    assert "tail_is_safe" not in defined, (
        "`tail_is_safe` is back. It compares pivot SIGN PATTERNS; what a certificate needs is that "
        "the tail-inclusive sequence carries at most one negative, which is `tail_lifts`.")
    assert "tail_lifts" in defined, "`tail_lifts` is missing; the tail has no check at all"
    assert "certifying_shift" in defined, (
        "`certifying_shift` is missing -- it is the one place that knows which shift each route "
        "certifies at, and without it every caller re-derives that and one of them gets it wrong")


def test_the_guard_can_fail():
    """Prove the AST rule rejects the defect it describes, on a synthetic module.

    A guard that has only ever seen correct code has not been shown to reject anything.
    """
    good = "def f():\n    return tail_lifts(jmax, lam, shift)\n"
    bad = "def f():\n    return tail_lifts(jmax, lam, MU_DEFAULT)\n"

    def offenders(src):
        return [c for c in _calls(ast.parse(src))
                if SHIFT_ARG.get(c.func.id) is not None
                and len(c.args) > SHIFT_ARG[c.func.id]
                and isinstance(c.args[SHIFT_ARG[c.func.id]], ast.Name)
                and c.args[SHIFT_ARG[c.func.id]].id == FORBIDDEN]

    assert offenders(bad), "the rule does not flag a tail check handed the default shift"
    assert not offenders(good), "the rule flags a tail check handed a computed shift"
