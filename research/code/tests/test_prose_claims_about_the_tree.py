"""Docstring claims ABOUT THE TREE must still be true of the tree.

WHY THIS EXISTS. Three claims went stale in one session, each because work elsewhere falsified
prose that was correct when written:

  * `ClayAssembly`'s `I3` docstring said the real asymptotic-scaling statement "is not yet
    expressible here" and that `Running.lean` "is consumed by nothing". Adding
    `AsymptoticScaling` made both false, and nothing objected.
  * `CLAY-GOAL.md` said the stress tensor and the OPE "do not occur in 138 modules". The count was
    right when written and the tree had grown to 156.
  * The same document said `Running.lean` is imported by nothing, for the same reason as the first.

The pattern is that ADVANCING A ROW SILENTLY FALSIFIES THE PROSE OF WHATEVER MODULE DESCRIBED THE
GAP. A reader cannot tell a stale claim from a live one, and a stale claim about what the tree
LACKS is the most misleading kind: it is exactly what a reader consults to decide what to work on.

SCOPE, and why it is narrow. Only two claim shapes are checked, both of which are assertions about
the tree that the tree can answer:

  1. "X is consumed by nothing" / "nothing imports X" / "X is imported by nothing" -- the named
     module must have no importer.
  2. "in N modules" -- N must be the current module count.

Prose that merely MENTIONS a module is not a claim and is not checked. There is no attempt to parse
English; the two patterns are matched literally, and anything outside them is out of scope by
design. A guard that tried to judge arbitrary prose would fire spuriously and stop being read.

WHAT IT SCANS. Every `.lean` under `research/lean` excluding `.lake`, and the two planning documents
in `_scratch/CURRENT` when that directory is present -- it is a sibling repository, so its absence is
not a failure.

HOW TO SATISFY IT. Make the claim true, or delete it. A claim about what the tree lacks should be
deleted the day it stops being true, not annotated -- a retraction republishes the wrong statement.
"""
import pathlib
import re

import pytest

REPO = pathlib.Path(__file__).resolve().parents[3]
LEAN = REPO / "research" / "lean"
SCRATCH = REPO.parent / "_scratch" / "CURRENT"

#: Module named as unimported, in any of the three phrasings that have actually been used.
_UNIMPORTED = re.compile(
    r"`(?:MassGap\.)?(\w+)(?:\.lean)?`[^.]{0,160}?"
    r"(?:is consumed by nothing|consumed by NOTHING|is imported by nothing|nothing imports)",
    re.IGNORECASE | re.DOTALL,
)
#: The reverse order, "nothing imports `X`".
_UNIMPORTED_REV = re.compile(
    r"(?:nothing imports|is imported by nothing|is consumed by nothing)[^.]{0,80}?"
    r"`(?:MassGap\.)?(\w+)(?:\.lean)?`",
    re.IGNORECASE | re.DOTALL,
)
#: A self-referential module count.
_MODULE_COUNT = re.compile(r"\b(\d+)\s+modules\b")


def _lean_files():
    return sorted(p for p in LEAN.rglob("*.lean") if ".lake" not in p.parts)


def _module_names():
    return {p.stem for p in _lean_files() if p.parent.name == "MassGap"}


def _importers(module: str, files) -> list[str]:
    pat = re.compile(rf"^\s*import\s+MassGap\.{re.escape(module)}\s*$", re.MULTILINE)
    return [p.name for p in files if pat.search(p.read_text(encoding="utf-8"))]


def _scanned():
    out = list(_lean_files())
    # Only the LIVE pair. Superseded documents are historical records and their claims were true
    # when written; holding them to the current tree would be a category error.
    if SCRATCH.is_dir():
        out += [q for q in (SCRATCH / "CLAY-GOAL.md", SCRATCH / "CLAY-HANDOVER.md") if q.is_file()]
    return out


def test_no_module_is_called_unimported_while_being_imported():
    """A claim that a module is consumed by nothing must survive a check of the imports."""
    files = _lean_files()
    known = _module_names()
    # DERIVED: a floor on DISCOVERY, not on the tree -- see the note in
    # `test_module_counts_in_prose_are_current`.
    assert len(known) >= 20, (
        f"only {len(known)} Lean modules discovered; the scan is looking in the wrong place and "
        "would pass vacuously")
    bad = []
    for p in _scanned():
        text = p.read_text(encoding="utf-8")
        for rx in (_UNIMPORTED, _UNIMPORTED_REV):
            for m in rx.finditer(text):
                mod = m.group(1)
                if mod not in known:
                    continue
                users = _importers(mod, files)
                if users:
                    line = text[: m.start()].count("\n") + 1
                    bad.append(
                        f"  {p.name}:{line} claims `{mod}` is unimported, but it is imported by "
                        f"{', '.join(users)}")
    if bad:
        pytest.fail(
            "Prose claims a module is consumed by nothing while something consumes it.\n"
            "Make the claim true or delete it — a claim about what the tree LACKS is what a reader "
            "consults to decide what to work on.\n" + "\n".join(bad))


def test_module_counts_in_prose_are_current():
    """A self-referential 'in N modules' must be the current count."""
    actual = len(_module_names())
    # DERIVED: the bar is a floor on DISCOVERY, not on the tree. The tree has upwards of 150
    # modules, so any count near 20 means the glob resolved somewhere else and the scan would pass
    # by examining nothing. Set far below the true count so that growth never has to move it.
    assert actual >= 20, (
        f"only {actual} Lean modules discovered; the scan is looking in the wrong place")
    bad = []
    for p in _scanned():
        text = p.read_text(encoding="utf-8")
        for m in _MODULE_COUNT.finditer(text):
            claimed = int(m.group(1))
            if claimed != actual:
                line = text[: m.start()].count("\n") + 1
                bad.append(f"  {p.name}:{line} says {claimed} modules; there are {actual}")
    if bad:
        pytest.fail(
            f"Stale module count in prose. The tree has {actual} modules under research/lean/MassGap.\n"
            + "\n".join(bad))


def test_the_gate_can_actually_fail(tmp_path):
    """PROOF the guard is not vacuous: both checks fire on planted text.

    Without this a regex that never matches would pass forever and read as a clean bill.
    """
    files = _lean_files()
    known = _module_names()
    # pick a module that IS imported, so the claim below is genuinely false
    imported = next((m for m in sorted(known) if _importers(m, files)), None)
    assert imported is not None, "no module in the tree is imported; the planted claim would be true"

    planted = f"`MassGap.{imported}` is consumed by nothing."
    hit = _UNIMPORTED.search(planted) or _UNIMPORTED_REV.search(planted)
    assert hit is not None, "the unimported-claim pattern did not match its own example"
    assert hit.group(1) == imported
    assert _importers(imported, files), "the module chosen for the planted claim has no importer"

    bogus = len(known) + 1
    m = _MODULE_COUNT.search(f"the terms do not occur in {bogus} modules")
    assert m is not None, "the module-count pattern did not match its own example"
    assert int(m.group(1)) != len(known), "the planted count was not actually wrong"
