"""Every Lean name a goal document cites, checked against the Lean sources.

The chain-of-record documents name declarations constantly, and a declaration that gets renamed
leaves the document pointing at nothing. That is worse than a stale claim: a stale claim can be
argued with, a dead citation cannot be checked at all. Three such names sat in `CLAY-GOAL.md` row 13
(`su3_transferData_T_ne_id`, `su3ReTr`, `su3ReTr_separating`) and two more in rows 12 and 17c
(`gapAt_of_finite_volume_pairing`), and every one was found by accident rather than by a check.

WHAT COUNTS AS A CITATION. A backticked token that looks like a Lean identifier -- it contains `_`
or a `.`, and is not a file name. That deliberately includes BARE names: the dead name in row 17c was
written without its module prefix, so a dotted-only filter would have missed it, which is exactly how
it survived the first sweep.

WHAT COUNTS AS DEAD, in two tiers. Tier one: the name's last component appears NOWHERE in the repo's
Lean sources or in `research/code`, as a whole word, in any position. Not "is not a declaration" --
structure fields, instance names, constructors and local abbreviations are all legitimately cited and
none of them parse as top-level declarations, so matching on presence is the right shape.

Tier two exists because presence alone was NOT enough. `RefinementLaw.refined_isGreatest` -- a
word-order swap of the real `isGreatest_refined` -- passed tier one, made live by the very docstring
that cited it. So a name present in the blob but absent once Lean COMMENTS ARE STRIPPED is reported
PROSE-ONLY: the repo talks about it and defines nothing by that name. A swapped, misremembered or
half-renamed Lean name lands here, and that is the commonest way to get one wrong.

Tier two is fatal for `DOCS` and advisory for `OPTIONAL_DOCS`. The working documents are held to
citing this repo, and a genuine external reference belongs in them as a path, not as a backticked
name; a parked thread is not held to that.

SCOPE LIMIT, stated so it is not mistaken for coverage: only LEAN comments are stripped. A Python
name occurring solely in a Python docstring still reads live, because stripping Python prose needs
`tokenize` and is a separate change with its own controls.

⛔ IT CANNOT TELL YOU A CLAIM IS TRUE. A live name proves the citation resolves, nothing more. The
declaration may say something else entirely than the document says it says.

⛔ AND IT CANNOT SEE MATHLIB, OR ANY DEPENDENCY. The corpus is this repo. A document may legitimately
cite a Mathlib lemma, and this reports it dead unless the tree happens to use it too — which is why
`CLAY-HANDOVER.md` reports `tendsto_pow_mul_geometric_of_norm_lt_one`, a real Mathlib lemma that no
proof here calls. So a hit means "this repo does not define the name", NOT "the name does not exist".
Triage before repairing; a `DOCS` entry that cites external results heavily will need a different
check, not an allowlist, because an allowlist is where dead names go to be forgotten.

Exit code 1 when any document cites a name this repo does not define.
"""
from __future__ import annotations

import os
import re
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(os.path.dirname(_HERE)))
LEAN = os.path.join(REPO, "research", "lean", "MassGap")
#: Where a document may live. The working files are in the repo; `_scratch/CURRENT` is kept in the
#: search path because a thread may still be parked there.
DOC_DIRS = [
    os.path.join(REPO, "research"),
    os.path.join(os.path.dirname(REPO), "_scratch", "CURRENT"),
]

#: Documents whose citations must resolve. A name here that is NOT found in any of `DOC_DIRS` FAILS
#: rather than being skipped: these are tracked files, so an absent one means a move left the gate
#: reading nothing, which is the one outcome a citation gate must not report as clean.
DOCS = ["CLAY-CHECKLIST.md", "CLAY-DETAIL.md"]

#: Documents to check if present and to pass over if not. A parked thread is allowed to disappear.
OPTIONAL_DOCS = ["CLAY-GOAL.md"]


def _locate(name: str) -> str | None:
    """The first directory in `DOC_DIRS` holding `name`, or `None`."""
    for d in DOC_DIRS:
        path = os.path.join(d, name)
        if os.path.exists(path):
            return path
    return None

# A backticked token that could be a Lean name. Tactics and prose words are excluded by the
# `_`-or-`.` requirement below, not here.
#
# `[^\W\d]` rather than `[A-Za-z_]`: LEAN IDENTIFIERS ARE UNICODE and many here begin with a Greek
# letter -- `κ₀YM`, `μYMAt_nonneg`, `θ`. An ASCII-only start class DROPPED every such citation
# before it was ever checked, so a document could cite a Greek name that does not exist and this
# gate would report it clean. `\d` is excluded so a bare numeral is not read as a name.
TOKEN = re.compile(r"`([^\W\d][\w.']*)`")

# Words that contain `_` or `.` but are not Lean names in this corpus.
NOT_A_NAME = {"a.e", "i.e", "e.g", "w.r.t"}


def source_blob() -> str:
    """Lean sources AND `research/code`.

    The documents cite pytest names and certify scripts as well as Lean declarations —
    `test_every_stated_named_axiom_count_matches_the_build` is a real citation and a real thing, and
    a Lean-only corpus reports it dead. Anything the repo defines counts as live.
    """
    parts = []
    for fn in sorted(os.listdir(LEAN)):
        if fn.endswith(".lean"):
            with open(os.path.join(LEAN, fn), encoding="utf-8", errors="replace") as fh:
                parts.append(fh.read())
    # the root module too, so `MassGap.<Module>` citations resolve
    root = os.path.join(os.path.dirname(LEAN), "MassGap.lean")
    if os.path.exists(root):
        with open(root, encoding="utf-8", errors="replace") as fh:
            parts.append(fh.read())
    code = os.path.join(REPO, "research", "code")
    for dirpath, _dirnames, filenames in os.walk(code):
        if "__pycache__" in dirpath:
            continue
        for fn in sorted(filenames):
            if fn.endswith(".py"):
                with open(os.path.join(dirpath, fn), encoding="utf-8",
                          errors="replace") as fh:
                    parts.append(fh.read())
                # A document may cite a test or script by its MODULE name, which never
                # appears inside the file. `test_docstring_names_resolve` is such a
                # citation, and reading contents alone reports it dead.
                parts.append(fn[:-3])
    return "\n".join(parts)


def strip_lean_comments(src: str) -> str:
    """`src` with Lean block and line comments removed.

    Lean 4 block comments NEST and `/--` opens one, so this scans with a depth counter rather than
    regexing: a non-nesting `/-.*?-/` would stop at the first `-/` and leave the tail of an outer
    comment in the code set, which is the direction that hides a dead name.
    """
    out: list[str] = []
    i, depth, n = 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1
            i += 2
        elif src.startswith("-/", i) and depth:
            depth -= 1
            i += 2
        elif depth:
            i += 1
        else:
            out.append(src[i])
            i += 1
    return re.sub(r"--[^\n]*", "", "".join(out))


def code_blob() -> str:
    """`source_blob()` with Lean comments stripped -- what the repo DEFINES, not what it discusses.

    Python is passed through unchanged; see the module docstring's scope limit.
    """
    parts = []
    for fn in sorted(os.listdir(LEAN)):
        if fn.endswith(".lean"):
            with open(os.path.join(LEAN, fn), encoding="utf-8", errors="replace") as fh:
                parts.append(strip_lean_comments(fh.read()))
    root = os.path.join(os.path.dirname(LEAN), "MassGap.lean")
    if os.path.exists(root):
        with open(root, encoding="utf-8", errors="replace") as fh:
            parts.append(strip_lean_comments(fh.read()))
    code = os.path.join(REPO, "research", "code")
    for dirpath, _dirnames, filenames in os.walk(code):
        if "__pycache__" in dirpath:
            continue
        for fn in sorted(filenames):
            if fn.endswith(".py"):
                with open(os.path.join(dirpath, fn), encoding="utf-8",
                          errors="replace") as fh:
                    parts.append(fh.read())
                parts.append(fn[:-3])
    return "\n".join(parts)


def live_words(blob: str) -> set[str]:
    """Every identifier the repo defines, Greek starts included.

    The ASCII-only start class this used to carry truncated `κ₀YM_pos` to `YM_pos` -- the scan
    began at the first ASCII letter and dropped everything before it. So a Greek-named declaration
    was never in the live set, and a citation of one was reported dead however real it was, while a
    BARE Greek citation was dropped by `TOKEN` and never checked at all. The two blind spots hid
    each other: the false negative was invisible because the false positive never fired.
    """
    return set(re.findall(r"[^\W\d][\w']*", blob))


def main() -> int:
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="backslashreplace")
    except Exception:
        pass

    if not os.path.isdir(LEAN):
        print(f"no Lean sources at {LEAN}")
        return 2
    blob = source_blob()
    words = live_words(blob)
    code_words = live_words(code_blob())
    modules = {fn[:-5] for fn in os.listdir(LEAN) if fn.endswith(".lean")}

    total = 0
    missing = [n for n in DOCS if _locate(n) is None]
    if missing:
        for n in missing:
            print(f"  REQUIRED DOCUMENT NOT FOUND: {n}")
        print(f"\n{len(missing)} required document(s) missing. A move that leaves this gate reading "
              f"nothing is the one outcome it must not report as clean; searched "
              f"{', '.join(DOC_DIRS)}.")
        return 1

    for name in DOCS + OPTIONAL_DOCS:
        path = _locate(name)
        if path is None:
            print(f"  (optional, absent: {name})")
            continue
        with open(path, encoding="utf-8", errors="replace") as fh:
            lines = fh.read().splitlines()
        dead: dict[str, list[int]] = {}
        prose: dict[str, list[int]] = {}
        for ln, line in enumerate(lines, 1):
            for tok in TOKEN.findall(line):
                if tok.lower() in NOT_A_NAME:
                    continue
                if "_" not in tok and "." not in tok:
                    continue
                if tok.endswith(".lean"):
                    continue
                last = tok.rsplit(".", 1)[-1]
                # a bare module name is a file, not a declaration
                if last in modules:
                    continue
                if last not in words:
                    dead.setdefault(tok, []).append(ln)
                elif last not in code_words:
                    prose.setdefault(tok, []).append(ln)
        if dead:
            print(f"\n{name}: {len(dead)} name(s) cited but absent from the Lean sources")
            for tok, lns in sorted(dead.items()):
                where = ", ".join(str(x) for x in lns[:6])
                print(f"    {tok}   (line {where})")
        if prose:
            verdict = "PROSE-ONLY" if name in DOCS else "prose-only (advisory)"
            print(f"\n{name}: {len(prose)} name(s) {verdict} -- the repo discusses them and "
                  "defines nothing by that name")
            for tok, lns in sorted(prose.items()):
                where = ", ".join(str(x) for x in lns[:6])
                print(f"    {tok}   (line {where})")
        if not dead and not prose:
            print(f"{name}: every cited name resolves.")
        total += len(dead) + (len(prose) if name in DOCS else 0)

    if total:
        print(f"\n{total} unresolved citation(s). A renamed declaration leaves the document "
              "pointing at nothing; repair the citation or delete the claim. A PROSE-ONLY name is "
              "usually a word-order swap of a real one -- read the declaration before renaming it "
              "back. If it names something outside this repo, write it as a path.")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
