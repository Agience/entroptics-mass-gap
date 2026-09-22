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

WHAT COUNTS AS DEAD. The name's last component appears NOWHERE in the repo's Lean sources or in `research/code`, as
a whole word, in any position. Not "is not a declaration" -- structure fields, instance names,
constructors and local abbreviations are all legitimately cited and none of them parse as top-level
declarations. Matching on mere presence under-reports (a name surviving only in a comment reads as
live) and that is the right trade: a gate that cries wolf gets ignored, and this one is meant to be
believed when it fires.

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
SCRATCH = os.path.join(os.path.dirname(REPO), "_scratch", "CURRENT")

DOCS = ["CLAY-GOAL.md"]

# A backticked token that could be a Lean name. Tactics and prose words are excluded by the
# `_`-or-`.` requirement below, not here.
TOKEN = re.compile(r"`([A-Za-z_][\w.']*)`")

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


def live_words(blob: str) -> set[str]:
    return set(re.findall(r"[A-Za-z_][\w']*", blob))


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
    modules = {fn[:-5] for fn in os.listdir(LEAN) if fn.endswith(".lean")}

    total = 0
    for name in DOCS:
        path = os.path.join(SCRATCH, name)
        if not os.path.exists(path):
            print(f"  (absent, skipped: {name})")
            continue
        with open(path, encoding="utf-8", errors="replace") as fh:
            lines = fh.read().splitlines()
        dead: dict[str, list[int]] = {}
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
        if dead:
            print(f"\n{name}: {len(dead)} name(s) cited but absent from the Lean sources")
            for tok, lns in sorted(dead.items()):
                where = ", ".join(str(x) for x in lns[:6])
                print(f"    {tok}   (line {where})")
        else:
            print(f"{name}: every cited name resolves.")
        total += len(dead)

    if total:
        print(f"\n{total} dead citation(s). A renamed declaration leaves the document pointing at "
              "nothing; repair the citation or delete the claim.")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
