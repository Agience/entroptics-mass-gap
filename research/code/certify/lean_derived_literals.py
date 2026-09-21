"""Compare a Lean declaration's DERIVED/CHOSEN note against the literals in its STATEMENT.

WHY THIS EXISTS. Six consecutive adversarial audits of the odd-constant chain found the same defect,
and it was never in the terms -- it was in the note. Two shapes recur:

  * the note justifies a numeral that occurs only in the PROOF (`2 * p - 1` reached the lemma through
    a called definition, not through its own statement);
  * the note omits a numeral that IS in the statement (`hN : N != 0` and `hbeta : 0 <= beta` each
    carry a `0`, and sibling lemmas in the same file cite them).

Both are invisible to the existing gates. `test_no_undeclared_constants.py` checks that a literal HAS
a note; nothing checked that the note and the literal AGREE.

WHAT IT DOES NOT DO. It compares multisets of digit-runs, not meanings. A note saying "the `2` is the
dimension" when the `2` is a plane conversion passes here and only a reader catches it. This gate
closes the mechanical half.

ONLY THE `missing` DIRECTION IS A FAILURE. A numeral cited but absent from the statement has benign
causes -- a note may name `2p` as a concept, or say outright that a numeral lives in the proof rather
than the statement, and saying so puts the numeral in backticks. That is the same trap as explaining
a deletion: the prose about an absence reintroduces the string. So `cited-but-absent` is reported for
a reader and never fails the gate; `in-the-statement-but-unmentioned` is the half no benign cause
explains.

    python research/code/certify/lean_derived_literals.py scan [MODULE ...]
    python research/code/certify/lean_derived_literals.py check NAME ...
"""
from __future__ import annotations

import pathlib
import re
import sys

REPO = pathlib.Path(__file__).resolve().parent.parent.parent.parent
LEAN = REPO / "research" / "lean" / "MassGap"

DECL = re.compile(
    r"^(?:noncomputable\s+)?(?:private\s+)?(theorem|lemma|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_'.]*)",
    re.M,
)

# A numeral that is genuinely a literal: not a field projection (`q.1`, `hi.2`) and not part of an
# identifier (`SU3`, `cA1`). Lean writes projections as `.1`/`.2`, which are the commonest false
# positives in this tree by a wide margin.
LITERAL = re.compile(r"(?<![.\w'])(\d+)")

NOTE = re.compile(r"\b(DERIVED|CHOSEN)\s*:")


def statement_of(text: str, start: int) -> str:
    """The signature only: from the declaration keyword to the token that opens the proof.

    `:=` and `by` both occur inside statements -- in named arguments (`(N := N)`) and in tactic
    blocks within a `have` -- so track bracket depth and take the first at depth zero.
    """
    depth = 0
    i = start
    n = len(text)
    while i < n:
        ch = text[i]
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        # DERIVED: `0` is top level -- the depth at which a `:=` or `by` belongs to the
        # declaration rather than to a nested binder or tactic block.
        elif depth == 0:
            if text.startswith(":=", i):
                return text[start:i]
            if text.startswith(" by\n", i) or text.startswith(" by ", i):
                return text[start:i]
        i += 1
    return text[start:i]


def docstring_before(text: str, start: int) -> str | None:
    """The `/-- ... -/` block immediately preceding the declaration, if any."""
    head = text[:start].rstrip()
    if not head.endswith("-/"):
        return None
    open_at = head.rfind("/--")
    if open_at == -1:
        return None
    return head[open_at:]


def strip_comments(s: str) -> str:
    return re.sub(r"--[^\n]*", "", s)


def cited_literals(doc: str) -> set[str]:
    """Digit runs appearing inside backticks anywhere from the first DERIVED/CHOSEN to the end."""
    m = NOTE.search(doc)
    if m is None:
        return set()
    tail = doc[m.start():]
    out: set[str] = set()
    for quoted in re.findall(r"`([^`]*)`", tail):
        out.update(re.findall(r"\d+", quoted))
    return out


def analyse(path: pathlib.Path):
    text = path.read_text(encoding="utf-8")
    for m in DECL.finditer(text):
        name = m.group(2)
        doc = docstring_before(text, m.start())
        if doc is None or NOTE.search(doc) is None:
            continue
        stmt = strip_comments(statement_of(text, m.start()))
        present = set(LITERAL.findall(stmt))
        cited = cited_literals(doc)
        missing = sorted(present - cited, key=int)
        spurious = sorted(cited - present, key=int)
        if missing or spurious:
            yield name, path.name, m.start(), missing, spurious, sorted(present, key=int)


def line_of(path: pathlib.Path, offset: int) -> int:
    return path.read_text(encoding="utf-8")[:offset].count("\n") + 1


def files(args: list[str]) -> list[pathlib.Path]:
    if args:
        return [LEAN / (a if a.endswith(".lean") else a + ".lean") for a in args]
    return sorted(LEAN.glob("*.lean"))


def cmd_scan(args: list[str]) -> int:
    rows = []
    for path in files(args):
        rows.extend(analyse(path))
    fails = [r for r in rows if r[3]]
    for name, fname, off, missing, spurious, present in rows:
        if not missing:
            continue
        ln = line_of(LEAN / fname, off)
        print(f"{fname}:{ln}  {name}")
        print(f"    in the STATEMENT, unmentioned by the note: {', '.join(missing)}")
        if spurious:
            print(f"    (also cited but absent, not a failure: {', '.join(spurious)})")
    print()
    print(f"{len(fails)} declaration(s) whose note omits a literal its statement carries.")
    return len(fails)


def cmd_check(args: list[str]) -> int:
    wanted = set(args)
    found = False
    for path in sorted(LEAN.glob("*.lean")):
        text = path.read_text(encoding="utf-8")
        for m in DECL.finditer(text):
            if m.group(2).split(".")[-1] not in wanted:
                continue
            found = True
            doc = docstring_before(text, m.start())
            stmt = strip_comments(statement_of(text, m.start()))
            present = sorted(set(LITERAL.findall(stmt)), key=int)
            cited = sorted(cited_literals(doc or ""), key=int)
            print(f"{path.name}:{line_of(path, m.start())}  {m.group(2)}")
            print(f"    statement literals: {', '.join(present) or '(none)'}")
            print(f"    note cites        : {', '.join(cited) or '(no DERIVED/CHOSEN note)'}")
    if not found:
        print("no such declaration")
    return 0


def main() -> int:
    # DERIVED: `2` because argv[0] is the program name, so fewer than two entries means no
    # subcommand was given.
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    if sys.argv[1] == "scan":
        cmd_scan(sys.argv[2:])
        return 0
    if sys.argv[1] == "check":
        return cmd_check(sys.argv[2:])
    print(__doc__)
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
