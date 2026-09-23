"""Find declarations the tree already proves, before another one is written.

The repeated failure this exists to stop is not a missing instruction. Prior-art sweeps get run when
a task looks big; they get skipped when a lemma looks small -- and a four-line helper is the MOST
likely thing to already exist, because it is what anyone would have needed. `State.map_sub` was
written twice for that reason, and `iunshift_ishift` lives in two import-isolated namespaces.

Two modes.

`check NAME...` is the pre-write query: given the names about to be added, report every existing
declaration with that name, in any namespace, plus near-misses on the same stem. Run it BEFORE
writing, which is the only time it is cheap.

`scan` is the gate: normalise every declaration's STATEMENT -- the text between the binders' colon
and the `:=` or `by` -- and report distinct names sharing one. Lean catches an exact clash inside a
namespace; it says nothing when the same fact is proved twice under two names, or once per
import-isolated copy of the lattice skeleton. That is the case this catches and the compiler cannot.

Normalisation is deliberately shallow: whitespace collapsed, nothing else. It will not see a
duplicate stated with different binder names, so a quiet report is not a proof of absence -- it is
the cheap half. The expensive half is still reading.
"""
from __future__ import annotations

import os
import re
import sys
from collections import defaultdict

_HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(os.path.dirname(_HERE)))
LEAN = os.path.join(REPO, "research", "lean", "MassGap")

# `theorem foo`, `lemma foo`, `def foo`, with the usual modifiers in front.
_DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive)\s+"
    # `[^\W\d]`: Lean identifiers are Unicode. An ASCII-only start class matched no Greek-initial
    # declaration, so `κ₀YM`, `μYMAt`, `ΔYM` and their kin were never entered into the table and a
    # second definition of one of them would not have been reported.
    r"([^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*)",
    re.M)
# A declaration may be written dotted -- `theorem State.map_sub` -- so a query for `map_sub` has to
# match the LAST component too. Missing that is what let `State.map_sub` be written twice while a
# name-only search reported nothing.


_OPEN = "([{⟨"
_CLOSE = ")]}⟩"


def _statement(tail: str) -> str:
    """The declaration's statement: everything up to the `:=` or `by` that starts its PROOF.

    ⛔ The first `:=` is the wrong place to stop. Lean writes named arguments the same way, so
    `(O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)` truncates the statement mid-binder
    and every theorem in that family collapses to one key. That produced 54 false duplicates and
    nothing else. Only a `:=` at bracket depth zero begins a proof.
    """
    depth = 0
    i = 0
    n = len(tail)
    while i < n:
        c = tail[i]
        if c in _OPEN:
            depth += 1
        elif c in _CLOSE:
            depth -= 1
            # DERIVED: `0` is the bracket depth the declaration opens at; below it the scan has run
            # past the end of this declaration. Not a tunable.
            if depth < 0:
                break
        # DERIVED: 0 is the bracket level a declaration opens at; a proof can
        # only start there.
        elif depth == 0:
            if tail.startswith(":=", i):
                break
            if tail.startswith(" by", i) and (i + 3 == n or tail[i + 3] in " \n"):
                break
        i += 1
    return " ".join(tail[:i].split())


def _files() -> list[str]:
    return sorted(
        os.path.join(LEAN, f) for f in os.listdir(LEAN) if f.endswith(".lean"))


def _declarations() -> list[tuple[str, str, int, str]]:
    """(name, kind, line, statement) for every declaration in the tree."""
    out: list[tuple[str, str, int, str]] = []
    for path in _files():
        with open(path, encoding="utf-8", errors="replace") as fh:
            text = fh.read()
        lines = text.splitlines()
        for m in _DECL.finditer(text):
            kind, name = m.group(1), m.group(2)
            line = text.count("\n", 0, m.start()) + 1
            out.append((name, kind, line, _statement(text[m.end():])))
        del lines
    return out


def check(names: list[str]) -> int:
    decls = _declarations()
    by_name: dict[str, list[tuple[str, int]]] = defaultdict(list)
    for name, _kind, line, _stmt in decls:
        by_name[name].append((name, line))
    # rebuild with the file, which the tuple above dropped
    by_name.clear()
    for path in _files():
        with open(path, encoding="utf-8", errors="replace") as fh:
            text = fh.read()
        for m in _DECL.finditer(text):
            line = text.count("\n", 0, m.start()) + 1
            by_name[m.group(2)].append((os.path.basename(path), line))

    def _last(n: str) -> str:
        return n.rsplit(".", 1)[-1]

    hits = 0
    for want in names:
        tail = _last(want)
        # match the full name OR the last component, so a query for `map_sub` finds `State.map_sub`
        exact = sorted({(f, ln, n) for n, v in by_name.items()
                        if n == want or _last(n) == tail
                        for f, ln in v})
        if exact:
            hits += 1
            print(f"\n  ALREADY EXISTS: {want}")
            for f, ln, n in exact:
                print(f"      {f}:{ln}  {n}")
        stem = tail.split("_")[0]
        near = sorted({n for n in by_name
                       if _last(n) != tail
                       and (_last(n).startswith(stem + "_") or tail in _last(n))})
        if near:
            # CHOSEN: 12 near-miss names per query. A display cap on a hint, not a decision -- the
            # exact match above is what the exit code reports. Raising it only lengthens the print.
            print(f"\n  near '{want}': " + ", ".join(near[:12])
                  # CHOSEN: 12 near-miss names. A display cap on a hint; the
                  # exit code reads the exact match above, so raising it only
                  # lengthens the print.
                  + (" ..." if len(near) > 12 else ""))
    if hits:
        print(f"\n{hits} of {len(names)} requested name(s) already exist. "
              "Reuse them, or pick a different statement.")
        return 1
    print(f"\nnone of the {len(names)} requested name(s) exist in {LEAN}.")
    print()
    print("⛔ THIS IS A NAME SEARCH AND CANNOT TELL YOU WHETHER THE FACT EXISTS.")
    print("   If it does, it is under the name its author chose -- which is not the one")
    print("   you were about to use. Before writing, grep the tree for the CONTENT: the")
    print("   operators and types of the statement you intend. `su3ReTr` duplicated")
    print("   `HaarVariance.reTr` and `reflClosure` duplicated `symCube`, each written")
    print("   after this exact line printed.")
    return 0


# CHOSEN: 40 groups printed. A display cap; the COUNT on the first line is what the gate reads, and
# it is not truncated.
def scan(limit: int = 40) -> int:
    # THEOREMS ONLY. For a theorem the signature IS the proposition, so two names sharing one are
    # proving the same fact. For a `def` the signature is only its type, and many distinct
    # definitions share a type -- `blkR`, `blkS`, `blkT` are all `(τ) (a) (m) : Finset (Link d n)`
    # and are three different sets. Including defs produced 117 hits that were almost all noise,
    # which is the fastest way to make a gate worth ignoring.
    by_stmt: dict[str, list[tuple[str, str, int]]] = defaultdict(list)
    for path in _files():
        with open(path, encoding="utf-8", errors="replace") as fh:
            text = fh.read()
        for m in _DECL.finditer(text):
            if m.group(1) not in {"theorem", "lemma"}:
                continue
            name = m.group(2)
            line = text.count("\n", 0, m.start()) + 1
            stmt = _statement(text[m.end():])
            # CHOSEN: 25 characters. Below it a statement is things like `: Prop` or `(n : ℕ) : ℝ`,
            # shared by dozens of unrelated declarations, and every such group is noise. Raising it
            # hides real duplicates; lowering it floods the report. Measured against the tree: at 25
            # the surviving groups are all genuine.
            if len(stmt) < 25:
                continue
            by_stmt[stmt].append((os.path.basename(path), name, line))

    # DERIVED: `1` is "one name" -- a statement proved under more than one name is the thing being
    # detected. Not a threshold.
    dupes = {s: v for s, v in by_stmt.items()
             # DERIVED: 1 is one name; more than one name on a statement IS
             # the detection.
             if len({n for _f, n, _l in v}) > 1}
    if not dupes:
        print("no two distinct names share a statement.")
        return 0
    print(f"{len(dupes)} statement(s) proved under more than one name:\n")
    for stmt, v in sorted(dupes.items(), key=lambda kv: -len(kv[1]))[:limit]:
        # CHOSEN: 110 characters of the statement per line, so a group fits a terminal. Display
        # only; the grouping key is the FULL statement.
        print("  " + (stmt[:110] + ("..." if len(stmt) > 110 else "")))
        for f, n, ln in sorted(v):
            print(f"      {f}:{ln}  {n}")
        print()
    return 0


def where(names: list[str]) -> int:
    """Where each name is declared, and the LAST of them.

    A Lean declaration must come after everything it names. Inserting a block anchored on the
    declaration it is ABOUT, rather than on the last one it USES, puts it before something it needs;
    Lean then reports an unknown identifier, or autoImplicit invents a variable and the error blames
    a missing import. Four builds were spent that way before this existed. Take the `LAST` line
    printed here and anchor below it.
    """
    by_name: dict[str, list[tuple[str, int]]] = defaultdict(list)
    for path in _files():
        with open(path, encoding="utf-8", errors="replace") as fh:
            text = fh.read()
        for m in _DECL.finditer(text):
            line = text.count("\n", 0, m.start()) + 1
            by_name[m.group(2)].append((os.path.basename(path), line))

    def _last(n: str) -> str:
        return n.rsplit(".", 1)[-1]

    found: list[tuple[str, str, int]] = []
    for want in names:
        tail = _last(want)
        hits = sorted({(f, ln, n) for n, v in by_name.items()
                       if n == want or _last(n) == tail
                       for f, ln in v})
        if not hits:
            print(f"  {want}: NOT FOUND")
            continue
        for f, ln, n in hits:
            print(f"  {want}: {f}:{ln}  {n}")
            found.append((f, n, ln))
    if not found:
        return 1
    # the anchor has to clear every one of them, per file
    per_file: dict[str, tuple[str, int]] = {}
    for f, n, ln in found:
        if f not in per_file or ln > per_file[f][1]:
            per_file[f] = (n, ln)
    print("\n  LAST per file (anchor BELOW these):")
    for f, (n, ln) in sorted(per_file.items()):
        print(f"      {f}:{ln}  {n}")
    return 0


def main() -> int:
    # Lean statements are full of unicode; a Windows console is cp1252 and would abort the report
    # partway through, which looks exactly like a crash in the analysis rather than in the printing.
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="backslashreplace")
    except Exception:
        pass
    argv = sys.argv[1:]
    if not argv or argv[0] not in {"check", "scan", "where"}:
        print(__doc__)
        print("usage: lean_duplicate_declarations.py check NAME [NAME...]")
        print("       lean_duplicate_declarations.py where NAME [NAME...]")
        print("       lean_duplicate_declarations.py scan")
        return 2
    if argv[0] == "where":
        # DERIVED: 2 is the subcommand plus one name -- the smallest well-formed invocation.
        if len(argv) < 2:
            print("where needs at least one NAME")
            return 2
        return where(argv[1:])
    if argv[0] == "scan":
        return scan()
    # DERIVED: `2` is the subcommand plus one name -- the smallest well-formed `check` invocation.
    if len(argv) < 2:
        print("check needs at least one NAME")
        return 2
    return check(argv[1:])


if __name__ == "__main__":
    raise SystemExit(main())
