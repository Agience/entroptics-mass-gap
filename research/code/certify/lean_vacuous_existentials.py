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

#: The shape: an existential over a real, immediately followed by its own positivity and a
#: conjunction. `\w` covers the ASCII names; the Greek ones are spelled out because Python's `\w`
#: does match them but the intent is clearer named.
_EX = re.compile(r"∃\s*([A-Za-zα-ω][\w₀-₉']*)\s*:\s*ℝ\s*,\s*"
                 r"0\s*<\s*\1\s*∧")

#: A declaration begins at column zero with one of these.
_DECL = re.compile(r"^(?:theorem|lemma|noncomputable def|def|instance)\s+([\w.'₀-₉]+)")


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
            var = m.group(1)
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
