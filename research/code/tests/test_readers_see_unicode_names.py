"""Every reader that harvests Lean declaration names must see the Unicode ones.

WHAT THIS IS FOR. Lean identifiers are Unicode, and the declarations this development is ABOUT
begin with a Greek letter: `ΔYM` the mass gap, `κ₀YM` the entropy floor, `μYM` and `μYMAt` the
tension, `μClampAt`, `βloYM`. Twenty-nine declarations in `research/lean/MassGap` start with a
character outside `[A-Za-z_]`.

A reader whose name class is ASCII-only fails on them in one of two ways, and the two hide each
other:

  * it DROPS the name -- a gate reports "every cited name resolves" having never checked any Greek
    citation;
  * it TRUNCATES the name -- a bare word scan begins at the first ASCII letter inside the name, so
    `κ₀YM_pos` is harvested as `YM_pos`, and a citation of the real name is reported dead. Worse,
    `ΔYM`, `κ₀YM` and `μYM` all truncate to `YM`, so three distinct declarations collide on one
    token.

`certify/lean_axiom_footprints.py` already carried this fix and its reason -- an ASCII class read
`exp_κ₀YM` as `exp_` -- and the repair had not been propagated to the four sibling readers. This
test is the propagation check: it asks each reader's own pattern whether it matches, so a reader
added later with the old class fails here rather than reporting a clean tree it never scanned.
"""
import importlib.util
import pathlib
import re

import pytest

REPO = pathlib.Path(__file__).resolve().parents[3]
CERTIFY = REPO / "research" / "code" / "certify"
TESTS = REPO / "research" / "code" / "tests"

#: Declarations that actually exist in the tree and begin with a non-ASCII character. Each is
#: load-bearing: the gap, the floor, the tension, the clamped tension, the low-coupling cut.
GREEK_DECLS = ["ΔYM", "κ₀YM", "μYM", "μYMAt", "μClampAt", "βloYM", "κ₀YM_pos", "μYMAt_nonneg"]


def _load(path: pathlib.Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _lean_snippet() -> str:
    """A synthetic module declaring the Greek names, so the check does not depend on the tree."""
    lines = ["namespace MassGap"]
    for n in GREEK_DECLS:
        lines.append(f"theorem {n} (x : ℝ) : x = x := rfl")
    lines.append("end MassGap")
    return "\n".join(lines) + "\n"


def test_the_derived_note_gate_sees_them():
    """`certify/lean_derived_literals.py` scans declarations for DERIVED/CHOSEN notes.

    A declaration it cannot see has never had its note checked, whatever the gate reports.
    """
    mod = _load(CERTIFY / "lean_derived_literals.py", "ldl_u")
    found = {name for _kind, name in mod.DECL.findall(_lean_snippet())}
    missing = [n for n in GREEK_DECLS if n not in found]
    assert not missing, f"invisible to the DERIVED gate: {missing}"


def test_the_duplicate_gate_sees_them():
    """`certify/lean_duplicate_declarations.py` tables declarations to find repeated statements.

    A name absent from the table cannot be reported as declared twice.
    """
    mod = _load(CERTIFY / "lean_duplicate_declarations.py", "ldd_u")
    found = {m[1] for m in mod._DECL.findall(_lean_snippet())}
    missing = [n for n in GREEK_DECLS if n not in found]
    assert not missing, f"invisible to the duplicate gate: {missing}"


def test_the_doc_citation_gate_sees_them():
    """`certify/doc_cites_live_declarations.py`, both halves.

    `TOKEN` harvests citations from the document and `live_words` harvests what the repo defines.
    Either being ASCII-only breaks the comparison, in opposite directions.
    """
    mod = _load(CERTIFY / "doc_cites_live_declarations.py", "dcld_u")
    live = mod.live_words(_lean_snippet())
    missing = [n for n in GREEK_DECLS if n not in live]
    assert not missing, f"absent from the live set: {missing}"

    doc = " ".join(f"`{n}`" for n in GREEK_DECLS)
    cited = set(mod.TOKEN.findall(doc))
    dropped = [n for n in GREEK_DECLS if n not in cited]
    assert not dropped, f"dropped from the citation scan: {dropped}"


def test_the_docstring_name_gate_sees_them():
    """`tests/test_docstring_names_resolve.py`: the declaration scan, the word scan and the cite."""
    mod = _load(TESTS / "test_docstring_names_resolve.py", "tdnr_u")
    found = set(mod._DECL.findall(_lean_snippet()))
    missing = [n for n in GREEK_DECLS if n not in found]
    assert not missing, f"invisible to the docstring-name gate: {missing}"

    doc = " ".join(f"`Complete.{n}`" for n in GREEK_DECLS)
    cited = {b for _a, b in mod._CITE.findall(doc)}
    dropped = [n for n in GREEK_DECLS if n not in cited]
    assert not dropped, f"module-qualified Greek citations dropped: {dropped}"


def test_the_paper_footprint_parser_sees_them():
    """`tests/test_paper_matches_lean.py` reads quoted `#print axioms` output from the paper.

    That output is MACHINE output, quoted as stronger evidence than prose, so a line the parser
    silently skips is the worst case: the paper's strongest-looking claim, unchecked.
    """
    mod = _load(TESTS / "test_paper_matches_lean.py", "tpml_u")
    quoted = "\n".join(
        f"'MassGap.{n}' depends on axioms: [propext, Classical.choice]" for n in GREEK_DECLS)
    found = {a.split(".")[-1] for a, _b in mod._QUOTED_FOOTPRINT.findall(quoted)}
    missing = [n for n in GREEK_DECLS if n not in found]
    assert not missing, f"footprint lines skipped by the paper gate: {missing}"


@pytest.mark.parametrize("name", GREEK_DECLS)
def test_the_check_is_not_vacuous(name):
    """POSITIVE CONTROL. The OLD class must genuinely fail on each of these names.

    Without this the tests above would pass against a name class that happens to be ASCII-only but
    is never exercised, and they would report the same thing whatever the readers did.
    """
    old = re.compile(r"[A-Za-z_][\w']*")
    m = old.fullmatch(name)
    assert m is None, (
        f"{name} is matched by the ASCII-only class, so it does not exercise the defect; "
        "replace it with a genuinely Greek-initial declaration")


def test_the_truncation_collision_is_real():
    """Three distinct declarations collapse to one token under a bare ASCII word scan.

    This is why the defect was silent: the live set contained `YM` and nothing noticed that it
    stood for the gap, the floor and the tension at once.
    """
    old = re.compile(r"[A-Za-z_][\w']*")
    shortened = {old.search(n).group(0) for n in ["ΔYM", "κ₀YM", "μYM"]}
    assert shortened == {"YM"}, f"expected a collision on YM, got {shortened}"
