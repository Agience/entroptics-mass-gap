"""Find conclusions of the shape `exists k, 0 < k and Q` in which `k` never occurs in `Q`.

WHY THIS EXISTS. `VolumeRate.exists_pos_and_iff` machine-checks that `(exists k : R, 0 < k and Q)`
is equivalent to `Q`: a bound variable that does not occur in the body it binds carries no content.
So a conclusion of that shape states nothing about a RATE, however much the docstring says
"a single rate k > 0". `VolumeRate.lean` says so in its header and gives the test in one line --
"check that deleting `exists k, 0 < k and` changes the statement" -- and then says
DO NOT REINTRODUCE THE PATTERN.

That rule was stated in prose, and prose does not run. A sweep on 2026-09-22 found SIX docstrings
claiming a common rate over a conclusion of exactly this shape, including two that contradicted
their own file header. This makes the rule mechanical.

WHAT IS FLAGGED, and what is not. A hit is a statement whose conclusion binds a positive real and
never uses it. That is not automatically a defect -- three declarations in `VolumeRate` exist
precisely to EXHIBIT the shape and prove it vacuous, and a theorem may legitimately conclude an
existential whose witness is used only in its own positivity. What a hit means is: this conclusion
does not constrain the quantity it appears to, so no docstring, paper row or downstream citation may
describe it as supplying a rate, a margin or a uniformity.

THE BASELINE RECORDS DEBT, NOT PERMISSION, and may only shrink -- the same contract as
`hand_rolled_reads_baseline.txt`.

    python research/code/certify/lean_vacuous_existentials.py scan
"""
from __future__ import annotations

import io
import os
import re
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(os.path.dirname(_HERE)))
LEAN = os.path.join(REPO, "research", "lean", "MassGap")
BASELINE = os.path.join(REPO, "research", "code", "tests", "vacuous_existentials_baseline.txt")

#: A binder name. `[^\W\d]` rather than `[A-Za-zα-ω]`, which is the same ASCII-class defect one
#: alphabet along: it spells out the LOWERCASE Greek block and stops, so `∃ Δ : ℝ, 0 < Δ ∧ …` was
#: not the shape as far as this scanner was concerned. Two conclusions in the tree bind `Δ`.
_NAME = r"[^\W\d][\w₀-₉']*"

#: The shape: a conclusion that binds a positive real. Lean writes it three ways and the scanner
#: saw one of them, so the other two were never examined -- a gate reporting on a population it did
#: not scan, which is the failure this file exists to make impossible for the shape it hunts.
#:
#:   * TYPED, the form it did see:      `∃ κ : ℝ, 0 < κ ∧ …`
#:   * TYPED, parenthesised and with further binders following it, which it did not:
#:                                      `∃ (c : ℝ) (N₀ : ℕ), 0 < c ∧ …`   (9 in the tree)
#:   * Lean's BINDER-PREDICATE SUGAR, which it did not: `∃ b > 0, …`      (8 in the tree)
#:
#: The sugar elaborates to `∃ b, 0 < b ∧ …` -- the identical statement, and the one
#: `VolumeRate.exists_pos_and_iff` proves equivalent to dropping the existential. Widening found no
#: new vacuous conclusion, so the baseline does not move; what it removes is the blind spot, in
#: which a vacuous conclusion written `∃ b > 0,` would have passed the ratchet in silence.
_EX = re.compile(
    r"∃\s*\(?\s*(?P<typed>" + _NAME + r")\s*:\s*ℝ\s*\)?(?:\s*\([^()]*\))*\s*,\s*"
    r"0\s*<\s*(?P=typed)\s*∧"
    r"|∃\s*(?P<sugar>" + _NAME + r")\s*>\s*(?:\(\s*0\s*:\s*ℝ\s*\)|0)\s*,")

#: A declaration begins at column zero with one of these, and may carry an attribute or a
#: visibility modifier first. Without those two prefixes the scan did not see 129 declarations in
#: `research/lean/MassGap` at all -- 25 written `private theorem …` and the rest carrying an
#: `@[simp]`-style attribute on the SAME line as the keyword -- so whatever their conclusions bound
#: was never examined and the ratchet reported clean over them. Widening admits no new hit here,
#: which is what says the baseline is unaffected; what it removes is the blind spot.
_DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|scoped\s+|noncomputable\s+)*"
                   r"(?:theorem|lemma|def|abbrev|axiom|instance)\s+([\w.'₀-₉]+)")


def _statements(text: str):
    """Yield `(name, line_no, statement_text)` for every declaration, statement only.

    The statement is everything from the declaration keyword to the `:=` or `by` that opens the
    proof -- which is exactly the part a reader is entitled to believe.
    """
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        m = _DECL.match(lines[i])
        if not m:
            i += 1
            continue
        name = m.group(1)
        start = i
        buf = []
        while i < len(lines):
            ln = lines[i]
            buf.append(ln)
            # the proof opens at a top-level `:=` or a trailing `by`
            if re.search(r":=\s*$|:=\s*by\s*$|\bby\s*$|:=\s*\S", ln):
                break
            i += 1
        yield name, start + 1, "\n".join(buf)
        i += 1


def scan():
    hits = []
    for fn in sorted(os.listdir(LEAN)):
        if not fn.endswith(".lean"):
            continue
        path = os.path.join(LEAN, fn)
        with io.open(path, encoding="utf-8") as fh:
            text = fh.read()
        for name, lineno, stmt in _statements(text):
            m = _EX.search(stmt)
            if not m:
                continue
            var = m.group("typed") or m.group("sugar")
            body = stmt[m.end():]
            # strip the trailing proof opener so `:= by` cannot count as a use
            body = re.split(r":=", body)[0]
            if not re.search(r"(?<![\w'])" + re.escape(var) + r"(?![\w'])", body):
                hits.append((fn, lineno, name, var))
    return hits


def _baseline() -> set:
    if not os.path.exists(BASELINE):
        return set()
    out = set()
    with io.open(BASELINE, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if line and not line.startswith("#"):
                out.add(line)
    return out


def main() -> int:
    # Only when RUN. Rewrapping at import time breaks pytest capture, and this module is
    # imported by the gate test_no_vacuous_existentials.
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")
    hits = scan()
    base = _baseline()
    keys = {f"{fn}|{name}" for fn, _, name, _ in hits}
    new = sorted(keys - base)
    gone = sorted(base - keys)

    print(f"{len(hits)} conclusion(s) bind a positive real they never use.\n")
    for fn, lineno, name, var in hits:
        mark = " " if f"{fn}|{name}" in base else "NEW"
        print(f"  {mark:>3}  {fn}:{lineno}  {name}   (binds `{var}`, unused)")

    if gone:
        print("\nIn the baseline but no longer present (the baseline may shrink):")
        for g in gone:
            print(f"     {g}")
    if new:
        print("\nNOT in the baseline:")
        for n in new:
            print(f"     {n}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
