"""Every numeric literal in a Lean DEFINITION or AXIOM must be declared DERIVED or CHOSEN.

The companion `test_no_undeclared_constants.py` makes the canon executable for the Python. This does
it for the Lean, which is where the modelling commitments live: a chosen number in a definition looks
exactly like a derived one, and the Lean carried several that nothing in the tree objected to.

WHAT IT FOUND, AND WHAT HAPPENED TO THEM. The aperture was `def nCorrYM : Nat := 16`, so the whole
theory was stated at one window -- `wilsonCorr` itself was typed `Fin (nCorrYM + 1)`, and the tension
took no aperture argument at all. `d2_le_bound` asserted the lag moment below a chosen `B = 1` over a
chosen lag range, and its companion `ym_finite_aperture` was a `norm_num` check on those same two
numbers against each other. `rArgYM = 73/100` and `mHiYM = 1/5` were pinned read values. All are
retired: the aperture is a variable (`wilsonCorrAt`, `readYMAt`, `mu YMAt`, `d2At`, `ymModelAt`), the
bound is existential (`confinement_of_bounded_substrate`), and the non-vacuity witnesses quantify
their magnitude below the derived ceiling instead of naming one.

SCOPE. Every `.lean` under `research/lean`, excluding `.lake` build output. Within a file, only `def`,
`abbrev`, `axiom` and `instance` blocks are scanned -- never theorem or lemma proofs. A numeral inside
a proof term is almost always structural (an index, an arity, a `norm_num` witness) and carries no
modelling commitment; a numeral in a DEFINITION or an AXIOM STATEMENT is the model. Scanning proofs
would bury the real findings in thousands of indices, which is how a guard stops being read.

NO EXEMPTION LIST, AND NO DIRECTORY LIST. There is no set of "structural" values, because such a list
is itself a constant chosen to decide which constants matter. There is no curated set of files either,
for the same reason -- this scanned one directory and missed the tree root until the scope was widened.
Every literal in scope is reported, and the known ones live in a BASELINE of debt that may only shrink.

HOW TO SATISFY IT. Put `DERIVED:` or `CHOSEN:` in the declaration's doc comment (`/-- ... -/`) or in a
`--` comment immediately above it, saying what derives the number or what choosing it costs. Naming a
number as chosen is an acceptable outcome; hiding it is not.

GRANULARITY, STATED SO IT IS NOT OVERREAD. This guard is per-DECLARATION, where the Python one is
per-literal: a declaration whose doc comment carries a marker passes for every literal in it. So it
catches a declaration that justifies NOTHING, not one that justifies a number and quietly introduces a
second. Narrowing it further would need Lean's own elaborator to enumerate the numerals, which is the
right eventual fix; until then this is the weaker claim, and it is the claim being made.

VERIFIED TO FIRE. Probes run against a real module and reverted: an undeclared
`noncomputable def probeThreshold : Real := 0.37` is caught; the same definition with `CHOSEN:` in its
doc comment passes; a numeral inside a `theorem` is correctly out of scope; and prose inside a doc
comment beginning with a Lean keyword is NOT mistaken for a declaration. A guard that has never been
shown to fire is unverified however green it reads.
"""
from __future__ import annotations

import re
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[3]
# EVERY Lean source in the tree, not one directory. `MassGap.lean` (the aggregate) and
# `lakefile.lean` sit at the root and were never scanned; a directory list is the same chosen
# scope the Python guard just shed. `.lake` is dependency build output, not source.
LEAN = REPO / "research" / "lean"
BASELINE = Path(__file__).with_name("undeclared_lean_constants_baseline.txt")

# A declaration that carries a modelling commitment. `theorem`/`lemma`/`example` are deliberately out
# of scope -- see the module docstring.
_IN_SCOPE = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+|scoped\s+)*"
                       r"(def|abbrev|axiom|instance)\s+(\S+)")
# Anything that begins a new top-level item, ending the declaration currently being collected.
_ENDS = re.compile(r"^(?:@\[|/--|/-!|/-|--|noncomputable\s|private\s|protected\s|scoped\s|def\s|"
                   r"abbrev\s|axiom\s|instance\s|theorem\s|lemma\s|example\s|namespace\s|end\s|"
                   r"section\s|variable\s|open\s|import\s|#|structure\s|inductive\s|class\s)")
# A numeric literal as a standalone token: not part of an identifier (`G2`, `SU3`, `Fin`), not part of
# a name like `su2`. Lean numerals may be decimal or have a decimal point.
_NUM = re.compile(r"(?<![A-Za-z0-9_'.])(\d+(?:\.\d+)?)(?![A-Za-z0-9_'])")
_MARK = re.compile(r"\b(DERIVED|CHOSEN)\b")


def _comment_mask(lines: list[str]) -> list[bool]:
    """True where a line is inside a block comment (`/-- … -/`, `/-! … -/`, `/- … -/`).

    WHY THIS IS NEEDED. Lean's declaration keywords are ordinary English words, so a line of PROSE
    inside a doc comment can begin with `instance`, `def` or `axiom` and be matched as a declaration.
    That is not hypothetical: a docstring sentence beginning "instance cannot express the thing the
    read is about" was reported as an `instance` declaration carrying the numerals in the rest of the
    paragraph. Matching source lines with a regex cannot tell prose from code on its own; tracking
    which lines are inside a comment is what separates them.
    """
    mask, depth = [], 0
    for ln in lines:
        opened = depth > 0 or ln.lstrip().startswith(("/--", "/-!", "/-"))
        mask.append(opened)
        depth += ln.count("/-") - ln.count("-/")
        # DERIVED: nesting depth cannot go below zero; a stray `-/` closes nothing.
        depth = max(depth, 0)
    return mask


def _declarations(path: Path) -> list[tuple[int, str, str, str]]:
    """(line number, kind, name, source text) for every in-scope declaration, with the comment block
    immediately above it attached so a declaration's justification travels with it."""
    lines = path.read_text(encoding="utf-8", errors="replace").split("\n")
    in_comment = _comment_mask(lines)
    out = []
    i = 0
    while i < len(lines):
        m = None if in_comment[i] else _IN_SCOPE.match(lines[i])
        if not m:
            i += 1
            continue
        start = i
        body = [lines[i]]
        i += 1
        while i < len(lines) and not _ENDS.match(lines[i]):
            body.append(lines[i])
            i += 1
        # The preceding comment block: a `/-- ... -/` doc comment or contiguous `--` lines.
        j, doc = start - 1, []
        while j >= 0 and (lines[j].lstrip().startswith("--") or lines[j].strip() == ""
                          or "-/" in lines[j] or lines[j].lstrip().startswith("/-")):
            doc.insert(0, lines[j])
            if lines[j].lstrip().startswith("/-"):
                break
            j -= 1
        # A doc comment can span many lines; walk back to its opener.
        if doc and "-/" in doc[0] and not doc[0].lstrip().startswith("/-"):
            while j >= 0 and not lines[j].lstrip().startswith("/-"):
                doc.insert(0, lines[j])
                j -= 1
            if j >= 0:
                doc.insert(0, lines[j])
        out.append((start + 1, m.group(1), m.group(2), "\n".join(doc + body)))
    return out


def _undeclared(path: Path) -> list[tuple[int, str, str]]:
    hits = []
    for lineno, kind, name, text in _declarations(path):
        if _MARK.search(text):
            continue
        nums = sorted(set(_NUM.findall(text)))
        if nums:
            first = next(ln.strip() for ln in text.split("\n") if _IN_SCOPE.match(ln))
            hits.append((lineno, f"{kind} {name} uses {','.join(nums)}", first[:90]))
    return sorted(set(hits))


def _key(path: Path, hit: tuple[int, str, str]) -> str:
    """Path and what was found -- never the line NUMBER, so the baseline does not churn."""
    return f"{path.relative_to(REPO).as_posix()}|{hit[1].strip()}"


def test_no_undeclared_lean_constants():
    """Every numeric literal in a Lean definition or axiom carries a DERIVED/CHOSEN declaration."""
    files = sorted(p for p in LEAN.rglob("*.lean") if ".lake" not in p.parts)
    assert len(files) >= 20, (
        f"only {len(files)} Lean modules discovered; the scan is looking in the wrong place and "
        "would pass vacuously")
    known = set()
    if BASELINE.exists():
        known = {l.strip() for l in BASELINE.read_text(encoding="utf-8").splitlines()
                 if l.strip() and not l.startswith("#")}
    bad = {}
    for p in files:
        fresh = [h for h in _undeclared(p) if _key(p, h) not in known]
        if fresh:
            bad[p] = fresh
    if bad:
        out = []
        for p, hs in sorted(bad.items()):
            out.append(f"  {p.relative_to(REPO)}")
            for ln, what, ctx in hs:
                out.append(f"     L{ln:<5} {what:<52} {ctx}")
        pytest.fail(
            f"{sum(len(h) for h in bad.values())} Lean definition(s)/axiom(s) with an undeclared "
            "numeric literal.\nPut DERIVED: or CHOSEN: in the declaration's doc comment saying what "
            "derives the number or what choosing it costs.\n" + "\n".join(out))


def test_the_baseline_carries_no_retired_debt():
    """A baseline line that no longer describes an undeclared literal must be DELETED.

    The file says it "may only shrink". Nothing made that true: the guard reads the baseline purely
    as a set of things to forgive, so a declaration that later gained its DERIVED/CHOSEN note left
    its line behind forever. A stale line is not inert -- it silently pre-forgives the NEXT
    undeclared literal to appear in a declaration of that name, which is exactly the case the guard
    exists to catch. It also makes the count of remaining debt wrong, and that count is the only
    thing anyone reads to know whether the work is progressing.

    So the debt may shrink, but only by deletion, and this is what makes that a fact rather than a
    convention. Retiring a declaration's literals and deleting its line are one change, not two.
    """
    files = sorted(p for p in LEAN.rglob("*.lean") if ".lake" not in p.parts)
    live = {_key(p, h) for p in files for h in _undeclared(p)}
    if not BASELINE.exists():
        pytest.skip("no baseline file")
    known = [l.strip() for l in BASELINE.read_text(encoding="utf-8").splitlines()
             if l.strip() and not l.startswith("#")]
    assert known, "the baseline is empty; it should have been deleted along with its last line"
    stale = [k for k in known if k not in live]
    assert not stale, (
        f"{len(stale)} baseline line(s) no longer describe an undeclared literal and must be "
        f"deleted from {BASELINE.name}:\n  " + "\n  ".join(stale))
