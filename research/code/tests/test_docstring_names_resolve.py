"""A `MassGap` declaration named in a doc comment must exist in the module it is attributed to.

WHY THIS EXISTS. A docstring that cites `Foo.bar` is making a checkable claim: that module `Foo`
declares `bar`. Those claims go wrong in two ways, and both happened in one session:

  * **Wrong namespace.** `TransferGaussian` cited `SliceTransfer.abs_transferKernel_le`; the lemma
    is in `SliceTransferSelfAdjoint`. The build does not care -- a doc comment is prose -- so
    nothing objected, and a reader following the reference finds nothing.
  * **Renamed or retired.** A declaration moves or goes away and every docstring that named it now
    points at nothing. The compiler checks proof terms, never prose.

This is the same class as `test_prose_claims_about_the_tree`: prose making an assertion about the
tree that the tree can answer. That one checks claims about what the tree LACKS; this one checks
claims about what it CONTAINS.

SCOPE, and why it is narrow. Only backticked tokens of the form `Module.rest` where `Module` is the
stem of an actual file under `research/lean/MassGap` are checked. That excludes Mathlib names
(`Finset.sum_congr`), local hypotheses (`hβ`), English in backticks, and bare names with no module
attribution -- none of which this can adjudicate. A guard that guessed would fire on prose and stop
being read.

`rest` may itself be dotted (`NegControl.su3_kernel_nonneg_iff`), because modules nest namespaces;
the check is on the LAST component.

TWO EXCLUSIONS, both false-positive classes the first run exposed. `Module.lean` is a FILE
reference, not a declaration citation, and is skipped. And the question asked is deliberately weak:
does the leaf name OCCUR in the cited module at all, not is it a top-level declaration. Structure
fields, constructors and names introduced inside a namespace are all legitimate to cite and none of
them is a top-level declaration; demanding more would report them. The weak question still catches
the defect this exists for -- a name attributed to a module that does not contain it -- which is
exactly how `SliceTransfer.abs_transferKernel_le` read while the lemma lived in
`SliceTransferSelfAdjoint`.

HOW TO SATISFY IT. Fix the reference, or drop the module prefix if the point is the bare name.
"""
import pathlib
import re

import pytest

TESTS_DIR = pathlib.Path(__file__).resolve().parent
REPO = pathlib.Path(__file__).resolve().parents[3]
LEAN = REPO / "research" / "lean" / "MassGap"

#: A backticked token that names a module-qualified declaration. The module part stays ASCII, since
#: module names are filenames; the DECLARATION part must not, because Lean identifiers are Unicode
#: and this tree's central ones are Greek — `Complete.κ₀YM_pos`, `Complete.μYMAt_nonneg`. An
#: ASCII-only class did not match those citations at all, so they were dropped before checking.
_CITE = re.compile(r"`([A-Z][A-Za-z0-9]*)\.([^\W\d][\w.']*)`")

#: A top-level declaration. Same reason for `[^\W\d]`: 29 declarations here begin with a Greek
#: letter, including `ΔYM`, `κ₀YM`, `μYM` and `μYMAt` — the mass gap, the entropy floor and the
#: tension, which is to say the objects the development is about.
_DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+|scoped\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|instance|axiom|class)\s+([^\W\d][\w.']*)",
    re.MULTILINE,
)

#: Doc comments only: `/-- ... -/` and `/-! ... -/`.
_DOC = re.compile(r"/-[-!](.*?)-/", re.DOTALL)

#: Module names that COLLIDE with a Mathlib namespace, where `Name.foo` in a docstring almost
#: always means Mathlib's `Name` and not the tree's module. `Measure` is the only one so far:
#: `Measure.pi`, `Measure.pi_eq`, `Measure.real` and `Measure.IsHaarMeasure.…` are all
#: `MeasureTheory.Measure`, while the tree also has a `Measure.lean`. Checking these would report
#: correct prose, so they are skipped — and listed, so the exemption is visible rather than implied.
_COLLIDES = {"Measure"}

#: Known miscitations, as a debt that may only SHRINK. Same discipline as
#: `test_no_undeclared_lean_constants`: the guard is useful from the day it is written rather than
#: after every historical reference is chased, and nothing new can be added without noticing.
_BASELINE = TESTS_DIR / "docstring_name_baseline.txt"


def _modules():
    return {p.stem: p for p in sorted(LEAN.glob("*.lean"))}


def _words(path: pathlib.Path) -> set[str]:
    """Every identifier-like token in the module, declarations and everything else.

    `[^\\W\\d][\\w']*` rather than `[A-Za-z0-9_']+`: an ASCII-only scan begins at the first ASCII
    letter INSIDE a Greek-initial name, so `κ₀YM_pos` entered this set as `YM_pos` and a citation
    of the real name was reported dead. Worse, `ΔYM`, `κ₀YM` and `μYM` all truncate to `YM`, so
    three distinct declarations collided on one token.
    """
    return set(re.findall(r"[^\W\d][\w']*", path.read_text(encoding="utf-8")))


def _declared(path: pathlib.Path) -> set[str]:
    """Top-level declarations only — used by the negative control, not by the check."""
    text = path.read_text(encoding="utf-8")
    names = set()
    for m in _DECL.finditer(text):
        full = m.group(1)
        names.add(full)
        names.add(full.split(".")[-1])
    return names


def _findings() -> dict[str, str]:
    """Every live miscitation, as `{baseline key: reported line}`.

    Split out of the test so the baseline can be checked against the same computation the gate
    forgives with, rather than against a second one that could drift from it.
    """
    mods = _modules()
    present = {name: _words(p) for name, p in mods.items()}
    out: dict[str, str] = {}
    for name, path in mods.items():
        text = path.read_text(encoding="utf-8")
        for doc in _DOC.finditer(text):
            for c in _CITE.finditer(doc.group(1)):
                mod, rest = c.group(1), c.group(2)
                if mod not in mods:
                    continue
                leaf = rest.split(".")[-1]
                if leaf == "lean":            # `Module.lean` is a file reference
                    continue
                if mod in _COLLIDES:          # a Mathlib namespace of the same name
                    continue
                if leaf not in present[mod]:
                    line = text[: doc.start() + c.start()].count("\n") + 1
                    out[f"{path.name} {mod}.{rest}"] = (
                        f"  {path.name}:{line} cites `{mod}.{rest}`, "
                        f"but `{leaf}` does not occur in `{mod}` at all")
    return out


def _known() -> set[str]:
    if not _BASELINE.exists():
        return set()
    return {l.strip() for l in _BASELINE.read_text(encoding="utf-8").splitlines()
            if l.strip() and not l.startswith("#")}


def test_docstring_declaration_names_resolve():
    mods = _modules()
    # DERIVED: the bar is a floor on DISCOVERY, not on the tree. The tree has upwards of 150
    # modules, so any count near 20 means the glob resolved somewhere else and the scan would pass
    # by examining nothing. Set far below the true count so that growth never has to move it.
    assert len(mods) >= 20, (
        f"only {len(mods)} Lean modules discovered; the scan is looking in the wrong place and "
        "would pass vacuously")
    known = _known()
    bad = [msg for key, msg in sorted(_findings().items()) if key not in known]
    if bad:
        pytest.fail(
            f"{len(bad)} doc-comment reference(s) name a declaration the cited module does not "
            "have.\nFix the reference or drop the module prefix — a reader following it finds "
            "nothing, and the compiler never checks prose.\n" + "\n".join(bad))


def test_the_baseline_carries_no_retired_debt():
    """A baseline line that no longer describes a live miscitation must be DELETED.

    The file says it may only shrink. Nothing made that true: the gate reads the baseline purely as
    a set of keys to forgive, so a reference that was repaired — or a docstring that was rewritten
    and dropped the citation entirely — left its line behind forever, silently PRE-FORGIVING the
    next miscitation of that same `file Module.name`. Eight of the seventeen lines were in that
    state when this check was added: every one had had its citing sentence removed, while the named
    declaration still does not exist, so any return of the reference would have been waved through.

    Retiring a miscitation and deleting its line are one change, not two. Same contract, and same
    reasoning, as `test_no_undeclared_lean_constants.test_the_baseline_carries_no_retired_debt`.
    """
    known = _known()
    if not known:
        pytest.skip("no baseline file")
    live = _findings()
    stale = sorted(k for k in known if k not in live)
    assert not stale, (
        f"{len(stale)} baseline line(s) no longer describe a live miscitation and must be deleted "
        f"from {_BASELINE.name}:\n  " + "\n  ".join(stale))


def test_a_stale_baseline_line_would_be_caught():
    """POSITIVE CONTROL for the check above: a key nothing produces is reported stale.

    Without this, a `_findings()` that returned everything would make the staleness check green on
    any baseline at all, which is the same defect one level up.
    """
    live = _findings()
    invented = "Nonexistent.lean Nowhere.no_such_declaration_at_all"
    assert invented not in live, "the planted key was accidentally a real finding"
    assert sorted(k for k in {invented} if k not in live) == [invented]


def test_the_gate_can_actually_fail():
    """PROOF the guard is not vacuous: it fires on a planted miscitation, and the parts work.

    Without this a regex that stopped matching would pass forever and read as a clean bill.
    """
    mods = _modules()
    # a real module with at least one declaration
    target = next((n for n in sorted(mods) if _declared(mods[n])), None)
    assert target is not None, "no module declares anything; the scan is broken"

    planted = f"`{target}.a_name_that_is_not_declared_anywhere`"
    m = _CITE.search(planted)
    assert m is not None, "the citation pattern did not match its own example"
    assert m.group(1) == target
    assert m.group(2) not in _words(mods[target]), "the planted name was accidentally real"

    # and a true citation is NOT reported
    real = sorted(_declared(mods[target]))[0]
    m2 = _CITE.search(f"`{target}.{real}`")
    assert m2 is not None and m2.group(2).split(".")[-1] in _words(mods[target])

    # the doc-comment extractor must actually find the module header
    body = mods[target].read_text(encoding="utf-8")
    assert _DOC.search(body) is not None, f"{target} has no doc comment; the extractor found none"
