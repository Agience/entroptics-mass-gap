"""The Lean the paper cites exists, and every axiom the Lean carries is accounted for in the paper.

The paper (`research/paper/mass-gap.md` and its `*.lean-map.md` tables) names Lean files and declarations throughout its status tables. Those names are prose: a
renamed theorem or a deleted file leaves the citation pointing at nothing, and nothing else notices.
These tests check both directions.

The axiom direction is the one that matters for the proof's accounting. A theorem's strength is its
axiom footprint, so an axiom introduced in the Lean tree and not named in the paper is a claim the
paper does not disclose. That is checked here rather than left to a reader running `#print axioms`.

These are filesystem and text facts, so no Lean build is required and the tests cost milliseconds.
"""
from __future__ import annotations

import ast
import csv
import re
import sys
import subprocess
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[3]
PAPER = REPO / "research" / "paper" / "mass-gap.md"
#: The paper's supplementary theorem-to-declaration tables and figure notes, which carry its Lean names.
COMPANIONS = REPO / "research" / "paper" / "v3"
LEAN = REPO / "research" / "lean"
DATA = REPO / "research" / "data"

#: Backticked names in the paper that are not Lean declarations: python identifiers, dtypes, store
#: directories, Lean keywords, and axioms supplied by Lean core rather than by this development.
NOT_LEAN = {
    "sorry", "propext", "float32", "configs_links_su2", "mp",
    # Lean tactics, not declarations. The paper names the tactic that discharges a step (§7 calls
    # `ym_finite_aperture` "a theorem (`norm_num`)"), and a tactic has no `theorem`/`def` line to
    # resolve to, so the resolver below would report it forever.
    "norm_num", "positivity", "linarith", "nlinarith", "decide", "simp", "rfl",
    # `admit` is the tactic twin of `sorry`; the papers name both when they state the tree has none.
    "admit",
    # Hypothesis binders, not declarations. The paper names the hypothesis a theorem takes
    # ("asking instead for `hfe` and `hgap`"), and a binder has no `theorem`/`def` line to
    # resolve to. `hfe` passed only because a python variable happens to share the name,
    # which is the accident this list exists to replace with a decision.
    "hfe", "hgap", "hdom", "hconf", "hread", "hmom", "hscale",
    # `hdual` is the scale-duality hypothesis binder named in the paper's comparison of two gap
    # routes, for the same reason `hfe` and `hgap` are named there.
    "hdual",
    # `hvan` is the vanishing-limit binder of `CompositeNondeg.not_compNondeg_of_vanish` (section 4 map).
    "hvan",
    # `hsym` is the symmetric-kernel binder of `KernelEigen.exists_eigen` (section 2 table).
    "hsym",
    # Section 11 shortens a family of names to their suffixes after the first full one
    # (`BoxLatticeGap.torusGap_su2_at`, `_su2_le`, `_su3_at`, `_su3_le`).
    "_su2_le", "_su3_at", "_su3_le",
    # Section 11 names the keyword and the tactic the sources do not use, the toolchain manager, the
    # Mathlib commit, and section 12 names resource classes and a Python package.
    "axiom", "native_decide", "elan", "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f",
    "bigmem", "cpu2h", "long", "torch",
}


def _lean_files() -> list[Path]:
    return [p for p in LEAN.rglob("*.lean") if ".lake" not in p.parts]


def _built_lean_files() -> list[Path]:
    """The Lean files `lake build` elaborates: MassGap.lean and its MassGap import closure.

    The default target is `lean_lib MassGap` with no globs, so a module the root does not import is
    never compiled and prints no footprint. That such a module exists at all is owned by
    test_provenance.test_every_lean_module_is_reachable_from_the_root; a footprint check that also
    counted it would report the same defect a second time, as a stale artifact.
    """
    imp = re.compile(r"^import MassGap\.([A-Za-z0-9_.]+)", re.M)
    root = LEAN / "MassGap.lean"
    stack = imp.findall(root.read_text(encoding="utf-8", errors="replace"))
    seen, out = set(), [root]
    while stack:
        m = stack.pop()
        p = LEAN.joinpath("MassGap", *m.split(".")).with_suffix(".lean")
        if m in seen or not p.exists():
            continue
        seen.add(m)
        out.append(p)
        stack += imp.findall(p.read_text(encoding="utf-8", errors="replace"))
    return out


def _paper() -> str:
    """The assembled paper and its companion files (`*.lean-map.md`)."""
    if not PAPER.exists():
        pytest.skip(f"{PAPER.name} not present")
    parts = [PAPER.read_text(encoding="utf-8")]
    # DERIVED: a section is `NN-name.md` (one dot); a companion `NN-name.lean-map.md` has two.
    parts += [q.read_text(encoding="utf-8") for q in sorted(COMPANIONS.glob("*.md")) if q.name.count(".") > 1]
    return "\n\n".join(parts)


def test_every_cited_lean_file_exists():
    """A `Foo.lean` named in the paper is a file in the Lean tree."""
    cited = sorted(set(re.findall(r"`([A-Za-z][A-Za-z0-9_]*\.lean)`", _paper())))
    assert cited, "the paper cites no Lean files; the reference format may have changed"
    have = {p.name for p in _lean_files()}
    missing = [f for f in cited if f not in have]
    assert not missing, f"the paper cites Lean files that do not exist: {missing}"


def _declared_axioms():
    """Every real `axiom` declaration in the tree, as `(name, file)`.

    Factored because two tests need it and a second copy of this loop is how the tree's other
    readers drifted apart. The comment mask is the whole point: Lean's keywords are English words,
    so a sentence inside a `/- -/` block that wraps onto "axiom above asserts…" reads as a
    declaration named `above` to a bare `^axiom\\s+` match. Four of six names collected that way
    were prose.
    """
    out = []
    for p in _lean_files():
        depth = 0
        for line in p.read_text(encoding="utf-8").split("\n"):
            # DERIVED: `0` is the nesting depth of a block comment, so `depth > 0` reads
            # "inside one". A count of open `/-` against closed `-/`, not a magnitude.
            in_comment = depth > 0 or line.lstrip().startswith(("/--", "/-!", "/-"))
            depth = max(depth + line.count("/-") - line.count("-/"), 0)
            if in_comment:
                continue
            m = re.match(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|scoped\s+)*"
                         r"axiom\s+([^\W\d][\w'.]*)", line)
            if m:
                out.append((m.group(1), p.name))
    return out


def test_the_stated_total_of_named_axioms_matches_the_tree():
    """The paper's global axiom claim, checked against the tree.

    Section 11 states "there is no `sorry`, no `axiom` declaration and no `native_decide`". That is the development's headline integrity claim. Without this test an axiom could be
    added and named in the paper, satisfying `test_every_lean_axiom_is_named_in_the_paper`, while
    the stated total stayed at none.

    The phrase not being found is a failure, not a skip: a check that goes quiet when the sentence
    is reworded reports the same thing as a check that passes.
    """
    flat = " ".join(_paper().split())
    m = re.search(r"[Nn]o `sorry`, no `axiom` declaration", flat)
    assert m, ("the paper's statement that the sources declare no axiom could not be found; the "
               "phrasing changed and this check would otherwise go silent on the headline claim")
    names = sorted({n for n, _ in _declared_axioms()})
    assert not names, (
        f"the paper states the sources declare no axiom; the tree declares {len(names)}: {names}")


def test_every_lean_axiom_is_named_in_the_paper():
    """Every `axiom` in the development is disclosed in the paper.

    An axiom is an unproved assumption the theorems above it inherit, so one that exists in the tree
    without appearing in the paper is an undisclosed input to the result.

    Two ways this read clean without checking anything, both now closed.

    * `^axiom\\s+…` matched prose. Lean's keywords are English words, and a sentence inside a `/- -/`
      block that happened to wrap so a line began "axiom above asserts…" was collected as a
      declaration named `above`. Four of the six names this gathered were comment prose — `above`,
      `footprint`, `and`, `cannot` — and each one is a common English word, so each passed
      disclosure trivially. With both real axiom declarations deleted from the tree the collection
      was still non-empty, `assert axioms` still passed, and the test reported every axiom
      disclosed while the tree contained none. The comment mask is what separates source from prose.
    * `name not in text` was a substring test. `os_reconstruction`, a retired axiom, counted as
      disclosed because the paper contains `os_reconstruction_wightman`. The check is on the name,
      so the name gets word boundaries.
    """
    # The tree declares no axiom, so an empty collection is its state, not a sign that the scan
    # missed the syntax. What guards the scan is the planted-text control
    # `test_the_axiom_scan_reads_source_and_not_prose`, which fails if a real declaration is not
    # collected, and the stated-total test, which pins the paper's count to this collection in both
    # directions. Here the scan must at least have read the sources.
    # CHOSEN: 20 files as the floor that separates "found the Lean tree" from "looking in the wrong place"; the tree holds 289, so the cut is far below its read.
    assert len(_lean_files()) >= 20, "the axiom scan read almost no Lean sources; it is looking in the wrong place"
    axioms = _declared_axioms()
    text = _paper()
    undisclosed = sorted({name for name, _ in axioms
                          if not re.search(rf"(?<![\w']){re.escape(name)}(?![\w'])", text)})
    assert not undisclosed, (
        f"axioms declared in Lean but not named in the paper: {undisclosed}. "
        f"An axiom the paper does not name is an undisclosed assumption.")


def test_the_axiom_scan_reads_source_and_not_prose():
    """Positive control for the two holes above, both demonstrated on planted text.

    The disclosure test cannot detect either of them itself: prose names pass disclosure because
    they are English words, and a substring match passes because the longer name really is there.
    """
    def collect(src: str) -> list[str]:
        out, depth = [], 0
        for line in src.split("\n"):
            # DERIVED: `0` is the nesting depth of a block comment, so `depth > 0` reads
            # "inside one". A count of open `/-` against closed `-/`, not a magnitude.
            in_comment = depth > 0 or line.lstrip().startswith(("/--", "/-!", "/-"))
            depth = max(depth + line.count("/-") - line.count("-/"), 0)
            if in_comment:
                continue
            m = re.match(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|scoped\s+)*"
                         r"axiom\s+([^\W\d][\w'.]*)", line)
            if m:
                out.append(m.group(1))
        return out

    prose = "/- A comment whose line wraps so that the next one begins with\naxiom above asserts x.\n-/\n"
    assert collect(prose) == [], (
        f"a sentence inside a block comment was read as an axiom declaration: {collect(prose)}")
    assert collect(prose + "axiom real_one : True\n") == ["real_one"], \
        "masking the comment also lost the declaration after it"

    # and the disclosure test is on the name, not on any string containing it
    paper = "the paper names `os_reconstruction_wightman` and nothing else"
    assert re.search(r"(?<![\w'])os_reconstruction(?![\w'])", paper) is None, \
        "a retired axiom still counts as disclosed by a longer name that contains it"
    assert re.search(r"(?<![\w'])os_reconstruction_wightman(?![\w'])", paper) is not None


def test_cited_lean_declarations_resolve():
    """Backticked snake_case names in the paper resolve to a declaration in Lean or Python.

    The paper cites theorems, certificates and scripts by bare name. This catches a rename on either
    side leaving the prose pointing at something that no longer exists.
    """
    text = _paper()
    cited = set(re.findall(r"`([a-z_][a-z0-9_]{3,})`", text)) - NOT_LEAN
    # DERIVED: the paper cites 157 such names today; the bar is a floor on discovery, set far below
    # that so growth never has to move it. Nothing else here could notice the citation pattern
    # ceasing to match: an empty `cited` gives an empty `candidates`, an empty `unresolved`, and
    # `assert not unresolved` reports a clean paper having examined no citation at all. Every
    # sibling scan in this suite carries such a floor; this one did not.
    assert len(cited) >= 100, (
        f"only {len(cited)} backticked declaration citations found in the paper; the citation "
        "pattern is not matching and this test would pass by checking nothing")
    lean_src = "\n".join(p.read_text(encoding="utf-8") for p in _lean_files())

    # Python names are collected as definitions, by parsing, rather than by searching the source
    # text. `name in py_src` accepted any occurrence anywhere -- including inside a comment or a
    # docstring. That is not a hypothetical looseness: a retired declaration stayed "resolvable"
    # purely because two test docstrings mentioned it while explaining that it had been retired, so
    # the prose describing a removal kept the guard from noticing the citation the removal orphaned.
    py_defs = set()
    for p in (REPO / "research").rglob("*.py"):
        if ".lake" in p.parts:
            continue
        py_defs.add(p.stem)
        try:
            tree = ast.parse(p.read_text(encoding="utf-8", errors="replace"))
        except SyntaxError:
            continue
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                py_defs.add(node.name)
            elif isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store):
                py_defs.add(node.id)

    # A third thing the paper legitimately cites in backticks: a label inside a committed artifact,
    # such as the `test` column value naming one family of rows. Those are not declarations in any
    # language, so resolving them against Lean and Python alone reported a real citation as dangling.
    # They are collected as whole cell values -- never as substrings of a cell -- so a label that
    # merely resembles part of some number or path still fails to resolve, and a renamed row family
    # still breaks the citation the way it should.
    data_labels = set()
    for csv_path in (REPO / "research" / "data").glob("*.csv"):
        try:
            with csv_path.open(newline="", encoding="utf-8") as fh:
                for row in csv.reader(fh):
                    for cell in row:
                        cell = cell.strip()
                        if cell and re.fullmatch(r"[^\W\d][\w]*", cell):
                            data_labels.add(cell)
        except OSError:
            continue

    def _declared(src, name):
        return re.search(
            rf"(^|\s)(axiom|theorem|lemma|def|abbrev|structure|class|instance|alias)\s+{re.escape(name)}\b"
            rf"|^\s+{re.escape(name)}\s*:", src, re.M)

    # A fourth thing the paper legitimately cites: a Mathlib declaration. The development rests on
    # Mathlib results by name (`geom_sum_eq`), and a citation to one is exactly as checkable as a
    # citation to our own -- the declaration either is in Mathlib or it is not. It is consulted only
    # for names that failed to resolve locally, so the cost is paid per dangling candidate rather than
    # per citation, and a Mathlib rename across a version bump shows up here as a failure rather than
    # as prose pointing at something gone.
    #
    # Where Mathlib is. Two places, and the test must not care which. A local checkout vendors it
    # under `research/.lake`; a machine that builds Lean remotely has it only on the builder. Looking
    # in one place made a local build tree load-bearing for a paper check, and deleting that tree
    # turned a live citation into a reported defect -- which is a wrong answer, not a stricter one.
    # When neither is reachable the Mathlib names are skipped rather than failed: a citation that
    # cannot be checked here is not a citation that is wrong.
    # `lake build` in research/lean puts the packages under research/lean/.lake; an older layout used research/.lake.
    mathlib = next((p for p in (REPO / "research" / "lean" / ".lake" / "packages" / "mathlib" / "Mathlib",
                                REPO / "research" / ".lake" / "packages" / "mathlib" / "Mathlib") if p.exists()),
                   REPO / "research" / "lean" / ".lake" / "packages" / "mathlib" / "Mathlib")

    def _in_mathlib_local(name):
        for path in mathlib.rglob("*.lean"):
            try:
                if name in (src := path.read_text(encoding="utf-8", errors="replace")) \
                        and _declared(src, name):
                    return True
            except OSError:
                continue
        return False

    def _mathlib_remote():
        """The configured Lean builder's Mathlib, or None. Same tree `lake build` compiles against."""
        try:
            sys.path.insert(0, str(REPO / "research" / "code"))
            import lean_build
            if not lean_build._cfg("LEAN_BUILD_HOST"):
                return None
            root = lean_build._cfg("LEAN_BUILD_DIR", "massgap-lean").rstrip("/")
            probe = f"test -d $HOME/{root}/.lake/packages/mathlib/Mathlib && echo yes"
            r = subprocess.run(lean_build._ssh_argv() + [probe],
                               capture_output=True, text=True, timeout=60)
            return f"$HOME/{root}/.lake/packages/mathlib/Mathlib" if "yes" in r.stdout else None
        except Exception:
            return None

    def _in_mathlib_remote(path, names):
        """Which of `names` Mathlib declares, in ONE remote pass rather than one per name."""
        if not names:
            return set()
        # The same declaration forms `_declared` accepts, as one alternation for ripgrep/grep.
        kinds = "axiom|theorem|lemma|def|abbrev|structure|class|instance|alias"
        alt = "|".join(re.escape(n) for n in names)
        cmd = (f"grep -rhoE '(^|[[:space:]])({kinds})[[:space:]]+({alt})([^A-Za-z0-9_]|$)' "
               f"{path} 2>/dev/null | grep -oE '({alt})' | sort -u")
        try:
            import lean_build
            r = subprocess.run(lean_build._ssh_argv() + [cmd],
                               capture_output=True, text=True, timeout=600)
            return {ln.strip() for ln in r.stdout.split(chr(10)) if ln.strip()}
        except Exception:
            return set()

    candidates = [name for name in sorted(cited)
                  if not (_declared(lean_src, name) or name in py_defs
                          or f"{name}.py" in text or name in data_labels)]

    if mathlib.is_dir():
        unresolved = [n for n in candidates if not _in_mathlib_local(n)]
    elif (remote := _mathlib_remote()):
        found = _in_mathlib_remote(remote, candidates)
        unresolved = [n for n in candidates if n not in found]
    elif candidates:
        pytest.skip(f"no Mathlib reachable (no vendored .lake, no configured Lean builder); "
                    f"cannot check {len(candidates)} possible Mathlib citation(s): {candidates}")
    else:
        unresolved = []

    assert not unresolved, f"the paper cites names that resolve nowhere: {unresolved}"


FOUNDATIONAL = {"propext", "Classical.choice", "Quot.sound"}

def test_printed_footprints_are_the_ones_the_paper_states():
    """§11's footprint claim is the one the build printed.

    §11.2 states that every declaration whose footprint is recorded depends on a subset of `propext`,
    `Classical.choice` and `Quot.sound`. `#print axioms` puts each declaration's real footprint in the
    build log, and `certify/lean_axiom_footprints.py` captures it in `13_dat_axiom_footprints.csv`.
    This reads that artifact: every printed footprint must lie inside the three foundational axioms.

    Skips when the artifact is absent -- producing it needs a Lean build, which is not a local job.
    """
    art = REPO / "research" / "data" / "13_dat_axiom_footprints.csv"
    if not art.exists():
        pytest.skip("13_dat_axiom_footprints.csv not regenerated yet "
                    "(needs `lake build` via certify/lean_axiom_footprints.py)")
    text = " ".join(_paper().split())
    assert re.search(r"every declaration whose footprint is recorded depends on a subset of "
                     r"`propext`, `Classical.choice` and `Quot.sound`", text), \
        "§11.2 no longer states the footprint of the recorded declarations"
    import csv
    got = {}
    with art.open(encoding="utf-8", newline="") as fh:
        for row in csv.DictReader(fh):
            # Axiom names keep their namespace: `Classical.choice` is one of the foundational three,
            # and stripping to the last component would turn it into `choice`.
            got[row["declaration"]] = {a for a in row["axioms"].split() if a.strip()}
    # DERIVED: one row per printed declaration; the Lean sources print thousands, so an artifact
    # with almost none was not produced by a build of this tree.
    assert len(got) >= 100, f"only {len(got)} footprints in the artifact; the scan would pass vacuously"
    named = {d: sorted(a - FOUNDATIONAL) for d, a in got.items() if a - FOUNDATIONAL}
    assert not named, (
        f"§11 states no declaration carries a named axiom, but {len(named)} printed footprints "
        "do: " + "; ".join(f"{d} -> {v}" for d, v in sorted(named.items())[:10]))


RETIRED_AXIOMS = {"d2_le_bound", "ym_character", "ym_asymfree",
                  "WightmanTheory", "os_reconstruction"}


def test_no_declaration_depends_on_a_retired_axiom():
    """The five retired axioms stay retired.

    `d2_le_bound` asserted the lag second moment is below a CHOSEN bound (`B = 1`) over a CHOSEN lag
    range, at a CHOSEN aperture, and its companion `ym_finite_aperture` was a `norm_num` check on
    those same numbers. `ym_character` and `ym_asymfree` were the two cited ends of a coupling
    interval that only needed ending because the aperture was frozen. All three were one route to
    `hconf`, and `Complete.confinement_of_bounded_substrate` reaches it from a single substrate
    statement with no number in it.

    `FullModel.WightmanTheory` was an opaque `Prop` and `FullModel.os_reconstruction` produced it
    from Euclidean data. Both were discharged by `rfl` from a `Unit` witness, so granting them
    conveyed nothing, and they were deleted rather than documented. The surviving reconstruction is
    `WightmanData.os_reconstruction_wightman`, which is stated against real data -- an `OSData` with a
    continuous bilinear form on a normed test space -- and is the one the Clay statement itself names
    as a route. It is not retired and must not be: matching here is on the exact axiom name, so
    `os_reconstruction_wightman` is not caught by the `os_reconstruction` entry.

    Nothing stops a future edit reintroducing one, and the footprint table would absorb it quietly
    among thousands of rows. This names them.
    """
    art = REPO / "research" / "data" / "13_dat_axiom_footprints.csv"
    if not art.exists():
        pytest.skip("13_dat_axiom_footprints.csv not regenerated yet")
    import csv
    with art.open(encoding="utf-8", newline="") as fh:
        rows = list(csv.DictReader(fh))
    assert len(rows) >= 100, (
        f"only {len(rows)} footprints in the artifact; the scan would pass vacuously")
    offenders = {}
    for r in rows:
        bad = RETIRED_AXIOMS & {a.split(".")[-1] for a in r["axioms"].split()}
        if bad:
            offenders[r["declaration"]] = sorted(bad)
    assert not offenders, (
        "declarations depend on retired axioms: "
        + "; ".join(f"{k} -> {v}" for k, v in sorted(offenders.items())))


def test_the_retired_axioms_are_not_declared_anywhere_in_lean():
    """The same guard at the source, so a retired axiom cannot reappear unused-but-present."""
    root = REPO / "research" / "lean" / "MassGap"
    files = sorted(root.glob("*.lean"))
    assert len(files) >= 20, "the Lean scan is looking in the wrong place"
    import re
    found = {}
    for p in files:
        for i, line in enumerate(p.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
            m = re.match(r"\s*axiom\s+([^\W\d][\w']*)", line)
            if m and m.group(1) in RETIRED_AXIOMS:
                found[f"{p.name}:{i}"] = m.group(1)
    assert not found, f"retired axioms redeclared: {found}"


#: A verbatim `#print axioms` line quoted in the paper, e.g.
#:   'EvenAperture.existence_and_gap_of_substrate_even'  depends on axioms: [propext, ...]
#: The paper quotes machine output here rather than describing it in prose, which reads as stronger
#: evidence than a prose claim -- so it needs to be checked at least as tightly.
_QUOTED_FOOTPRINT = re.compile(
    r"'([^\W\d][\w.']*)'\s+depends on axioms:\s*\[([^\]]*)\]")


def test_quoted_footprint_blocks_match_the_artifact():
    """A `#print axioms` line quoted verbatim in the paper must be what the build prints.

    A quoted `#print axioms` transcript reads as evidence rather than assertion, so a drifted one is
    worse than a stale sentence: a reader takes it for a transcript. the paper quotes none today; it
    states its footprint in §11 prose, which `test_the_stated_total_of_named_axioms_matches_the_tree`
    and `test_printed_footprints_are_the_ones_the_paper_states` check. When the paper quotes no
    transcript there is nothing here to compare, and the test passes. Pattern drift is still caught:
    if the phrase `depends on axioms` appears in the paper and the pattern matches none of it, the
    test fails.

    Matching is on the named axioms as a set. The three foundational ones are compared too, since a
    quoted transcript that omitted one would be a wrong transcript. Order inside the brackets is not
    significant and is not required to match -- `#print axioms` does not promise an order, and
    pinning one would fail on a Mathlib bump for no reason.

    A declaration the artifact does not carry is skipped rather than failed: the sibling
    `test_cited_lean_declarations_resolve` owns that check, and duplicating it here would report one
    defect twice.
    """
    text = _paper()
    quoted = list(_QUOTED_FOOTPRINT.finditer(text))
    if not quoted:
        assert 'depends on axioms' not in text, (
            'the paper contains `depends on axioms` but the transcript pattern matches none of it; '
            'the quoted block changed shape and this check would pass without reading it')
        return
    art = REPO / 'research' / 'data' / '13_dat_axiom_footprints.csv'
    if not art.exists():
        pytest.skip('13_dat_axiom_footprints.csv not regenerated yet')
    import csv
    printed = {}
    with art.open(encoding='utf-8', newline='') as fh:
        for row in csv.DictReader(fh):
            printed[row['declaration'].split('.')[-1]] = set(row['axioms'].split())

    bad = []
    for m in quoted:
        short = m.group(1).split('.')[-1]
        want = {a.strip() for a in m.group(2).split(',') if a.strip()}
        got = printed.get(short)
        if got is None:
            continue
        if want != got:
            bad.append(
                f"  '{m.group(1)}' quoted as {sorted(want)} but the build prints {sorted(got)}")
    if bad:
        pytest.fail(
            'A `#print axioms` line quoted verbatim in the paper is not what the build prints.\n'
            'This is transcribed machine output, so a reader reads it as a transcript. Re-quote it '
            'from a current build or delete the block.\n' + '\n'.join(bad))


def test_the_quoted_footprint_gate_can_actually_fail():
    """PROOF the pattern matches its own example and would notice a wrong transcript."""
    sample = ("'EvenAperture.existence_and_gap_of_substrate_even'  depends on axioms: "
              "[propext, Classical.choice, Quot.sound]")
    m = _QUOTED_FOOTPRINT.search(sample)
    assert m is not None, 'the quoted-footprint pattern did not match its own example'
    assert m.group(1).endswith('existence_and_gap_of_substrate_even')
    want = {a.strip() for a in m.group(2).split(',')}
    assert want == {'propext', 'Classical.choice', 'Quot.sound'}
    # and a transcript carrying a named axiom is a different set, so the comparison separates them
    assert want != want | {'wilson_reflection_positive_at'}, (
        'adding a named axiom did not change the set, so the check could not see it')


def test_the_development_is_sorry_free():
    """The paper's `sorry`-free claim, checked against the sources rather than trusted.

    §11 states it, and it is the claim a reader checks first. The word appears
    legitimately in comments that say there is none, so only code lines count.
    """
    import re

    offenders = []
    for p in sorted((REPO / "research" / "lean" / "MassGap").glob("*.lean")):
        in_block = False
        for i, line in enumerate(p.read_text(encoding="utf-8", errors="replace").split("\n"), 1):
            stripped = line.strip()
            if stripped.startswith("/-"):
                in_block = not stripped.endswith("-/")
                continue
            if in_block:
                if stripped.endswith("-/"):
                    in_block = False
                continue
            code = line.split("--")[0]
            if re.search(r"\b(sorry|admit)\b", code):
                offenders.append(f"{p.name}:{i}: {stripped[:70]}")
    assert not offenders, ("the paper claims the development is sorry-free, but:\n  "
                           + "\n  ".join(offenders))
