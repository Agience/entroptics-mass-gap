"""`12(1 - 3^{-1/4})/8` is quoted in eight places and computed in none of them.

It is the coefficient of the resolved-mode count bound -- `#{resolved} <= 0.360246 W/(eps lam0^{k+1})`
-- and it appears as a decimal literal in `ZeroMode.lean` (five times), `ScreenedGap.lean`, and
PAPER.md (three times). Nothing recomputes it, so the eight copies agree only as long as nobody edits
one.

THEY HAVE DISAGREED. An earlier pass wrote `0.360248` into four files against `ZeroMode`'s correct
`0.360246`; the value is `0.3602464715...`, so the copies were wrong in the fifth decimal and every
one of them looked plausible. A constant quoted in eight places and derived in none is a constant
waiting to drift, and prose does not have a type checker.

This recomputes it from its formula and checks every quoted decimal in the tree rounds to it. It
cannot check a number nobody wrote down; it can check that the ones written down are the same number.
"""
from __future__ import annotations

import re
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]

#: DERIVED: the coefficient itself, from the two constants it is built out of -- the sum-of-squares
#: denominator `8` and the entropy floor `3^{-1/4}` composed with `cos x >= 1 - x^2/2`. Written as the
#: formula so this file cannot be the ninth copy of the decimal.
COEFFICIENT = 12 * (1 - 3.0 ** -0.25) / 8

#: DERIVED: `0.360` is the prefix every correct quotation of this constant shares, so it is what
#: locates them. Not a tolerance -- a quotation that does not start this way is a different number
#: and is not this constant misquoted.
PREFIX = "0.360"

#: The Lean tree is `research/lean`, not `lean` -- getting that wrong made this search find the
#: paper and none of the five Lean quotations, which is exactly the blind spot the companion
#: test below exists to catch, and did.
SEARCH = (("research/lean", "*.lean"), ("research", "*.md"), ("research/code", "*.py"))


def _quotations():
    """Every decimal in the tree that starts `0.360`, with where it came from."""
    out = []
    for sub, pattern in SEARCH:
        root = REPO / sub
        if not root.is_dir():
            continue
        for path in sorted(root.rglob(pattern)):
            if any(p in path.parts for p in (".lake", "__pycache__")):
                continue
            if path.name == Path(__file__).name:
                continue
            try:
                text = path.read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            for m in re.finditer(re.escape(PREFIX) + r"\d*", text):
                line = text[:m.start()].count("\n") + 1
                out.append((path.relative_to(REPO), line, m.group(0)))
    return out


def test_every_quotation_of_the_resolved_count_coefficient_is_the_coefficient():
    quotes = _quotations()
    assert quotes, (
        f"no decimal starting {PREFIX!r} found anywhere; the resolved-count coefficient is quoted in "
        f"ZeroMode.lean, ScreenedGap.lean and PAPER.md, so finding none means this search is broken "
        f"rather than the tree being clean")

    wrong = []
    for path, line, text in quotes:
        # compare at the precision the quotation itself claims, so `0.360246` is checked to six
        # places and `0.36` to two -- a shorter quotation is less precise, not less correct
        places = len(text.split(".")[1])
        if round(COEFFICIENT, places) != round(float(text), places):
            wrong.append(f"{path}:{line} quotes {text}, but 12(1-3^(-1/4))/8 = "
                         f"{COEFFICIENT:.{places}f}")
    assert not wrong, (
        "quotations of the resolved-count coefficient disagree with its formula:\n  "
        + "\n  ".join(wrong)
        + f"\n\nThe value is {COEFFICIENT!r}. It is quoted and never computed, so the copies agree "
          f"only until one is edited -- which has happened.")


def test_the_search_would_notice_a_wrong_quotation():
    """The locator finds enough places that a drifted copy cannot hide in an unsearched file."""
    quotes = _quotations()
    files = {q[0] for q in quotes}
    # DERIVED: 2 is the arity of "quoted in more than one file", which is the whole risk this guards.
    assert len(files) >= 2, (
        f"the coefficient was found in only {sorted(str(f) for f in files)}; it is quoted in Lean and "
        f"in the paper, so a search finding one of them is not searching the other")
