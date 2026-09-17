"""The Lean the paper cites exists, and every axiom the Lean carries is accounted for in the paper.

PAPER.md names Lean files and declarations throughout its status tables. Those names are prose: a
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
PAPER = REPO / "research" / "PAPER.md"
LEAN = REPO / "research" / "lean"
DATA = REPO / "research" / "data"

#: Backticked names in the paper that are not Lean declarations: python identifiers, dtypes, store
#: directories, Lean keywords, and axioms supplied by Lean core rather than by this development.
NOT_LEAN = {
    "sorry", "propext", "float32", "configs_links_su2", "mp",
    # Lean TACTICS, not declarations. The paper names the tactic that discharges a step (§7 calls
    # `ym_finite_aperture` "a theorem (`norm_num`)"), and a tactic has no `theorem`/`def` line to
    # resolve to, so the resolver below would report it forever.
    "norm_num", "positivity", "linarith", "nlinarith", "decide", "simp", "rfl",
    # HYPOTHESIS BINDERS, not declarations. The paper names the hypothesis a theorem takes
    # ("asking instead for `hfe` and `hgap`"), and a binder has no `theorem`/`def` line to
    # resolve to. `hfe` passed only because a python variable happens to share the name,
    # which is the accident this list exists to replace with a decision.
    "hfe", "hgap", "hdom", "hconf", "hread", "hmom", "hscale",
    # `hdual` is the scale-duality hypothesis of `VortexCount.junction_of_floor_count` and
    # `junction_of_physical_count` — a binder in both, named in the paper's comparison of the two
    # gap routes for the same reason `hfe` and `hgap` are named there.
    "hdual",
}


def _lean_files() -> list[Path]:
    return [p for p in LEAN.rglob("*.lean") if ".lake" not in p.parts]


def _paper() -> str:
    if not PAPER.exists():
        pytest.skip("PAPER.md not present")
    return PAPER.read_text(encoding="utf-8")


def test_every_cited_lean_file_exists():
    """A `Foo.lean` named in the paper is a file in the Lean tree."""
    cited = sorted(set(re.findall(r"`([A-Za-z][A-Za-z0-9_]*\.lean)`", _paper())))
    assert cited, "the paper cites no Lean files; the reference format may have changed"
    have = {p.name for p in _lean_files()}
    missing = [f for f in cited if f not in have]
    assert not missing, f"PAPER.md cites Lean files that do not exist: {missing}"


def test_every_lean_axiom_is_named_in_the_paper():
    """Every `axiom` in the development is disclosed in the paper.

    An axiom is an unproved assumption the theorems above it inherit, so one that exists in the tree
    without appearing in the paper is an undisclosed input to the result.
    """
    axioms = []
    for p in _lean_files():
        for line in p.read_text(encoding="utf-8").split("\n"):
            m = re.match(r"^axiom\s+([A-Za-z_][A-Za-z0-9_']*)", line)
            if m:
                axioms.append((m.group(1), p.name))
    assert axioms, "no axioms found; the declaration syntax may have changed"
    text = _paper()
    undisclosed = sorted({name for name, _ in axioms if name not in text})
    assert not undisclosed, (
        f"axioms declared in Lean but not named in PAPER.md: {undisclosed}. "
        f"An axiom the paper does not name is an undisclosed assumption.")


def test_cited_lean_declarations_resolve():
    """Backticked snake_case names in the paper resolve to a declaration in Lean or Python.

    The paper cites theorems, certificates and scripts by bare name. This catches a rename on either
    side leaving the prose pointing at something that no longer exists.
    """
    text = _paper()
    cited = set(re.findall(r"`([a-z_][a-z0-9_]{3,})`", text)) - NOT_LEAN
    lean_src = "\n".join(p.read_text(encoding="utf-8") for p in _lean_files())

    # Python names are collected as DEFINITIONS, by parsing, rather than by searching the source
    # text. `name in py_src` accepted any occurrence anywhere -- including inside a comment or a
    # docstring. That is not a hypothetical looseness: a retired declaration stayed "resolvable"
    # purely because two test docstrings mentioned it while EXPLAINING that it had been retired, so
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

    # A third thing the paper legitimately cites in backticks: a LABEL inside a committed artifact,
    # such as the `test` column value naming one family of rows. Those are not declarations in any
    # language, so resolving them against Lean and Python alone reported a real citation as dangling.
    # They are collected as whole CELL VALUES -- never as substrings of a cell -- so a label that
    # merely resembles part of some number or path still fails to resolve, and a renamed row family
    # still breaks the citation the way it should.
    data_labels = set()
    for csv_path in (REPO / "research" / "data").glob("*.csv"):
        try:
            with csv_path.open(newline="", encoding="utf-8") as fh:
                for row in csv.reader(fh):
                    for cell in row:
                        cell = cell.strip()
                        if cell and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", cell):
                            data_labels.add(cell)
        except OSError:
            continue

    def _declared(src, name):
        return re.search(
            rf"(^|\s)(axiom|theorem|lemma|def|abbrev|structure|class|instance)\s+{re.escape(name)}\b"
            rf"|^\s+{re.escape(name)}\s*:", src, re.M)

    # A fourth thing the paper legitimately cites: a MATHLIB declaration. The development rests on
    # Mathlib results by name (`geom_sum_eq`), and a citation to one is exactly as checkable as a
    # citation to our own -- the declaration either is in Mathlib or it is not. It is consulted only
    # for names that failed to resolve locally, so the cost is paid per dangling candidate rather than
    # per citation, and a Mathlib RENAME across a version bump shows up here as a failure rather than
    # as prose pointing at something gone.
    #
    # WHERE MATHLIB IS. Two places, and the test must not care which. A local checkout vendors it
    # under `research/.lake`; a machine that builds Lean remotely has it only on the builder. Looking
    # in one place made a local build tree load-bearing for a paper check, and deleting that tree
    # turned a live citation into a reported defect -- which is a wrong answer, not a stricter one.
    # When NEITHER is reachable the Mathlib names are skipped rather than failed: a citation that
    # cannot be checked here is not a citation that is wrong.
    mathlib = REPO / "research" / ".lake" / "packages" / "mathlib" / "Mathlib"

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
        kinds = "axiom|theorem|lemma|def|abbrev|structure|class|instance"
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

    assert not unresolved, f"PAPER.md cites names that resolve nowhere: {unresolved}"


# The theorems PAPER.md states an axiom footprint for, with the passage that states it. A footprint
# claim is only machine-checked if the declaration carries a `#print axioms`, which puts its real
# footprint in the build log on every build; without one the claim is prose. This list is curated
# rather than derived: the ledger's evidence cells name supporting machinery alongside the result
# (row 1372 alone lists fifteen LDL/Sturm lemmas), and no rule over the prose separates "the paper
# claims a footprint for this" from "the paper cites this as a step" without flagging both.
FOOTPRINT_CLAIMS = {
    "ym_mass_gap_of_substrate":         "Sec 13: footprint = three foundational + reflection positivity",
    "confinement_of_bounded_substrate": "Sec 13: the substrate bound gives confinement at every "
                                        "large enough aperture",
    "margin_tendsto_floor":             "Sec 13: the margin tends to the whole floor kappa_0",
    "tension_tendsto_zero_of_bounded_circ_moment":
                                        "Sec 13: the tension VANISHES as the window opens",
    "ym_mass_gap_spectral":             "Sec 13: three foundational + reflection positivity; the "
                                        "aperture margin is an explicit hypothesis, not a discharged witness",
    "ym_existence_and_gap_of_junction": "Sec 13 ledger: gap side conditional on the two residuals",
    "ym_wightman_of":                   "Sec 13 ledger: 'adds the OS->Wightman reconstruction (six in total)'",
    "gap_uniform_of_cell":              "Sec 13 ledger: 'proved (foundation-only)'",
    "gap_uniform_of_cell_intensive":    "Sec 13 ledger: 'proved (foundation-only)'",
    "cell_volume_bar_nonvacuous": "Sec 13 ledger: 'proved (foundation-only)'",
    "Hcell2_clears_floor":              "Sec 13 ledger: 'the machine-checked cell ceiling'",
    "muInf_lt_floor":                   "Sec 13 ledger: 'proved (muInf_lt_floor)'; cited in the footprint paragraph",
}


def _lean_scan():
    """(theorems declared, names carrying a #print axioms) across MassGap's own sources."""
    import re
    theorems, printed = {}, set()
    root = REPO / "research" / "lean" / "MassGap"
    for p in sorted(root.glob("*.lean")):
        for line in p.read_text(encoding="utf-8", errors="replace").split("\n"):
            m = re.match(r"\s*#print axioms\s+([A-Za-z_][A-Za-z0-9_.']*)", line)
            if m:
                printed.add(m.group(1).split(".")[-1])
            d = re.match(r"(?:private\s+|protected\s+)?theorem\s+([A-Za-z_][A-Za-z0-9_.']*)", line)
            if d:
                theorems.setdefault(d.group(1), p.name)
    return theorems, printed


def test_every_claimed_footprint_is_printed():
    """Each theorem the paper states a footprint for carries a `#print axioms`.

    Four of these did not. Sec 13 states the volume row as "proved (foundation-only)" for
    `gap_uniform_of_cell`, `gap_uniform_of_cell_intensive` and `cell_volume_bar_nonvacuous`, and
    calls `Hcell2_clears_floor` the machine-checked cell ceiling, while none of the four printed its
    footprint -- the neighbouring rows' claims were machine-checked and these were not. FreeField.lean
    had no `#print axioms` at all, though Sec 13 lists `muInf_lt_floor` as proved and cites it by name
    where the axiom footprint is discussed.
    """
    theorems, printed = _lean_scan()
    assert len(FOOTPRINT_CLAIMS) >= 10, (
        f"FOOTPRINT_CLAIMS holds {len(FOOTPRINT_CLAIMS)} entries; the paper states a footprint for "
        "at least ten declarations, and an emptied list would make this test pass while checking "
        "nothing")
    missing = {n: why for n, why in FOOTPRINT_CLAIMS.items() if n not in printed}
    assert not missing, (
        "the paper states an axiom footprint for these, but no `#print axioms` puts it in the build "
        "log, so the claim is prose: "
        + "; ".join(f"{n} ({why})" for n, why in sorted(missing.items())))


def test_footprint_claim_list_matches_the_paper_and_the_lean_tree():
    """Every name in FOOTPRINT_CLAIMS is still a MassGap theorem and still cited by the paper.

    Guards the list itself: a renamed theorem or a claim dropped from Sec 13 would otherwise leave an
    entry that passes vacuously while pinning nothing.
    """
    theorems, _ = _lean_scan()
    assert len(FOOTPRINT_CLAIMS) >= 10, (
        f"FOOTPRINT_CLAIMS holds {len(FOOTPRINT_CLAIMS)} entries; every assertion below runs inside "
        "the loop over it, so an emptied list would make this test vacuous")
    text = PAPER.read_text(encoding="utf-8")
    for n in sorted(FOOTPRINT_CLAIMS):
        assert n in theorems, f"{n} is no longer a theorem in MassGap; update FOOTPRINT_CLAIMS"
        assert f"`{n}`" in text or f".{n}`" in text, \
            f"the paper no longer cites {n}; update FOOTPRINT_CLAIMS"


FOUNDATIONAL = {"propext", "Classical.choice", "Quot.sound"}

# What Sec 13 says each footprint IS, beyond the three foundational axioms. Quoted from the paper:
#   ym_mass_gap_certified            "`#print axioms` returning the three foundational axioms
#                                     **plus `wilson_reflection_positive_at` alone**"
#   ym_crossover_confinement_of_grid "footprint three foundational + `wilson_reflection_positive_at`"
#   ym_mass_gap_grid_certified       "carries that same footprint, no `d2_le_bound`"
#   ym_existence_and_gap             "carries the four named axioms"
#   ym_wightman                      "adds the OS->Wightman reconstruction ..., six in total"
#   ym_mass_gap_spectral             three foundational + the four named (inherited via ym_confinement);
#                                    the aperture margin is an explicit hypothesis, not a discharged witness
#   the volume row                   "proved (foundation-only)"
NAMED_FOOTPRINTS = {
    "ym_mass_gap_of_substrate":         {"wilson_reflection_positive_at"},
    "confinement_of_bounded_substrate": {"wilson_reflection_positive_at"},
    "margin_tendsto_floor":             {"wilson_reflection_positive_at"},
    "tension_tendsto_zero_of_bounded_circ_moment": set(),
    "ym_existence_and_gap_of_junction": {"wilson_reflection_positive_at"},
    "ym_wightman_of":                   {"wilson_reflection_positive_at",
                                         "os_reconstruction", "WightmanTheory"},
    "ym_mass_gap_spectral":             {"wilson_reflection_positive_at"},
    "gap_uniform_of_cell":              set(),
    "gap_uniform_of_cell_intensive":    set(),
    "cell_volume_bar_nonvacuous": set(),
}


def test_printed_footprints_are_the_ones_the_paper_states():
    """The footprints Sec 13 states are the ones the build actually printed.

    `#print axioms` puts each declaration's real footprint in the build log, but the log is not kept,
    so until now the table in Sec 13 could only be compared against a build someone happened to have
    run. `certify/lean_axiom_footprints.py` captures it; this compares the two, set against set, so a
    footprint that grows an axiom is caught even if the count is unchanged.

    Skips until the artifact is regenerated -- that needs a Lean build, which is not a local job.
    """
    art = REPO / "research" / "data" / "13_dat_axiom_footprints.csv"
    if not art.exists():
        pytest.skip("13_dat_axiom_footprints.csv not regenerated yet "
                    "(needs `lake build` via certify/lean_axiom_footprints.py)")
    import csv
    got = {}
    with art.open(encoding="utf-8", newline="") as fh:
        for row in csv.DictReader(fh):
            # Axiom names keep their namespace: `Classical.choice` is one of the foundational three,
            # and stripping to the last component would turn it into `choice` and make it look like
            # an axiom the paper never named.
            got[row["declaration"].split(".")[-1]] = {a for a in row["axioms"].split() if a.strip()}

    def names(actual, wanted):
        """The members of `wanted` that `actual` contains, matching bare or namespaced."""
        return {w for w in wanted
                if any(a == w or a.endswith("." + w) for a in actual)}

    problems = []
    for decl, expected in sorted(NAMED_FOOTPRINTS.items()):
        if decl not in got:
            problems.append(f"{decl}: the build printed no footprint for it")
            continue
        actual = got[decl]
        accounted = FOUNDATIONAL | expected
        stray = {a for a in actual
                 if not any(a == w or a.endswith("." + w) for w in accounted)}
        absent = expected - names(actual, expected)
        if stray:
            problems.append(f"{decl}: depends on {sorted(stray)}, which the paper does not name")
        if absent:
            problems.append(f"{decl}: the paper names {sorted(absent)} but the build does not show "
                            "them -- the claim understates or the theorem changed")
    assert not problems, "Sec 13's footprint table disagrees with the build:\n  " + "\n  ".join(problems)


RETIRED_AXIOMS = {"d2_le_bound", "ym_character", "ym_asymfree"}


def test_no_declaration_depends_on_a_retired_axiom():
    """The three retired axioms stay retired.

    `d2_le_bound` asserted the lag second moment is below a CHOSEN bound (`B = 1`) over a CHOSEN lag
    range, at a CHOSEN aperture, and its companion `ym_finite_aperture` was a `norm_num` check on
    those same numbers. `ym_character` and `ym_asymfree` were the two cited ends of a coupling
    interval that only needed ending because the aperture was frozen. All three were one route to
    `hconf`, and `Complete.confinement_of_bounded_substrate` reaches it from a single substrate
    statement with no number in it.

    Nothing stops a future edit reintroducing one, and the footprint table would absorb it quietly
    among 185 rows. This names them.
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
            m = re.match(r"\s*axiom\s+([A-Za-z_][A-Za-z0-9_']*)", line)
            if m and m.group(1) in RETIRED_AXIOMS:
                found[f"{p.name}:{i}"] = m.group(1)
    assert not found, f"retired axioms redeclared: {found}"


def test_the_free_field_plateau_the_paper_quotes_is_the_one_lean_proves():
    """The weak-coupling plateau value is a literal inside a Lean theorem; the paper repeats it six times.

    `muInf_lt_floor` states `(0.0326 : R) < (1/4) * log 3` -- the below-floor fact that gives
    `ym_asymfree` its weak end. The paper quotes that constant in the abstract, in Sec 8.2, Sec 8.6,
    and twice in the Sec 13 ledger. Nothing tied the two together, so editing the numeral in either
    place would leave the paper attributing a value to a theorem that does not state it.

    Both halves are read from source: the numeral out of the Lean file, and every place the paper
    pairs a value with mu_infinity.
    """
    import re

    lean = (REPO / "research" / "lean" / "MassGap" / "FreeField.lean").read_text(encoding="utf-8")
    m = re.search(r"theorem\s+muInf_lt_floor\s*:\s*\(\s*([0-9.]+)\s*:", lean)
    assert m, "muInf_lt_floor no longer states a literal lower bound; update this test"
    proved = float(m.group(1))

    # the theorem must actually be the below-floor inequality it is cited as
    import math
    assert proved < 0.25 * math.log(3.0), \
        f"muInf_lt_floor states {proved}, which is NOT below kappa_0 = (1/4)ln3"

    BS = chr(92)
    text = PAPER.read_text(encoding="utf-8")
    # Every place the paper pairs a value with mu_infinity. The scan is "find mu_infinity, then
    # look ahead" rather than one regex with a no-digit gap: the paper writes mu_infty(8)=0.0326,
    # and a [^0-9] gap silently skips that form -- which is most of the occurrences.
    marker = BS + "mu_" + BS + "infty"
    val = re.compile(r"(\d\.\d{3,4})")
    quoted = []
    for m in re.finditer(re.escape(marker), text):
        w = val.search(text[m.end():m.end() + 45])
        if w:
            quoted.append((w.group(1), text[:m.start()].count(chr(10)) + 1))
    assert len(quoted) >= 3,         f"found {len(quoted)} mu_infinity values in the paper; it states at least 3"
    for q, line in quoted:
        assert abs(float(q) - proved) < 5e-5, (
            f"PAPER.md line {line} quotes mu_infinity = {q}, but "
            f"MassGap.FreeField.muInf_lt_floor proves {proved}; the paper is attributing a value "
            "to a theorem that does not state it")


def test_no_pinned_witness_magnitude_remains():
    """The non-vacuity witnesses quantify their magnitude instead of naming one.

    They used to exhibit a single number (`mHiYM = 1/5`) and a single family size (`nWitnessYM = 2`),
    both chosen. A witness has to be an instance, but it does not have to be a PARTICULAR instance:
    `spectral_bar_nonvacuous` and `cell_volume_bar_nonvacuous` now take any magnitude strictly
    positive and at or below the derived ceiling `3^(-1/4) = e^(-kappa_0)`, and any family size. This
    fails if a pinned magnitude comes back.
    """
    root = REPO / "research" / "lean" / "MassGap"
    files = sorted(root.glob("*.lean"))
    assert len(files) >= 20, "the Lean scan is looking in the wrong place"
    import re
    banned = ("mHiYM", "nWitnessYM", "mWitnessYM", "PWitnessYM")
    found = {}
    for p in files:
        for i, line in enumerate(p.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
            m = re.match(r"\s*(?:noncomputable\s+)?def\s+([A-Za-z_][A-Za-z0-9_']*)", line)
            if m and m.group(1) in banned:
                found[f"{p.name}:{i}"] = m.group(1)
    assert not found, f"a pinned witness magnitude was reintroduced: {found}"

    # And the replacements must still be there, quantified.
    text = "\n".join(p.read_text(encoding="utf-8", errors="replace") for p in files)
    for name in ("spectral_bar_nonvacuous", "cell_volume_bar_nonvacuous"):
        assert f"theorem {name}" in text, f"{name} is gone; the bar has no non-vacuity witness"


def test_the_development_is_sorry_free():
    """The paper's `sorry`-free claim, checked against the sources rather than trusted.

    Sec 1 and Sec 13 both state it, and it is the claim a reader checks first. The word appears
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



def test_every_aperture_ceiling_is_derived_from_the_lag_arity():
    """The <d^2> ceiling comes from `N + 1` = the number of lags, which is the periodic extent.

    `Moment.Read N` indexes lags by `Fin (N + 1)` and sets `theta_d = 2 pi d / (N + 1)`, so a
    periodic extent of `L` sites -- lags `d = 0..L-1` -- has `N + 1 = L`. Two scripts independently
    wrote `(L + 1) ** 2` instead, i.e. the arity of a lattice one site LARGER than the one measured.
    That inflated the ceiling by ((L+1)/L)^2 = 1.13 on L=16, and the inflation made the certificate
    easier to pass every time.

    An off-by-one that appears twice in separate files is not a slip, so this asserts the form rather
    than a value: any ceiling written with an extent other than the lag arity fails here, at any L.

    The derivation now lives in `certify/aperture_ceiling.py` and the scripts call `d2_ceiling`, so
    the trigger list covers both spellings -- the old inline constants AND the helper. Dropping the
    old names from the trigger without adding the new ones would leave this test matching nothing,
    which reads exactly like passing.
    """
    TRIGGERS = ("APERTURE_RHS", "APERTURE_ARC", "C_MAX", "d2_ceiling",
                "1.0 - 3.0 ** (-0.25)", "3.0 ** -0.25")
    bad = []
    for p in sorted((REPO / "research").rglob("*.py")):
        if "test_" in p.name:
            continue
        for i, line in enumerate(p.read_text(encoding="utf-8", errors="replace").split("\n"), 1):
            code = line.split("#")[0]
            if not any(t in code for t in TRIGGERS):
                continue
            # the ceiling is the only such use that squares an extent
            m = re.search(r"\(\s*(\w+)\s*([+-])\s*(\d+)\s*\)\s*\*\*\s*2", code)
            if m:
                bad.append(f"{p.relative_to(REPO)}:{i}: extent written as "
                           f"({m.group(1)} {m.group(2)} {m.group(3)})**2, but the lag arity is "
                           f"{m.group(1)} -- `Fin (N+1)` over a periodic extent of {m.group(1)} sites")
            # and the same off-by-one can now be written as an argument
            m = re.search(r"d2_ceiling\(\s*(\w+)\s*([+-])\s*(\d+)", code)
            if m:
                bad.append(f"{p.relative_to(REPO)}:{i}: d2_ceiling passed "
                           f"({m.group(1)} {m.group(2)} {m.group(3)}), but the lag arity is "
                           f"{m.group(1)} -- the extent, not one more than it")
    assert bad == [], ("an aperture ceiling is derived from the wrong lag arity:\n  "
                       + "\n  ".join(bad))
    assert len(TRIGGERS) and any(
        any(t in p.read_text(encoding="utf-8", errors="replace") for t in TRIGGERS)
        for p in (REPO / "research").rglob("*.py") if "test_" not in p.name), (
        "no file in the tree mentions the aperture ceiling at all, so this test just checked "
        "nothing -- the trigger list has gone stale against the code")


def test_the_aperture_ceiling_is_written_in_exactly_one_place():
    """The ceiling formula appears once, in `certify/aperture_ceiling.py`, and nowhere else.

    Nine files used to carry their own copy. Copies are how the off-by-one the sibling test catches
    reached two files at once, and how a sharpening reaches some call sites and not others -- the
    tree then quotes two different ceilings for the same quantity and nothing fails.

    Test files are exempt on purpose: `test_paper_matches_artifacts` derives the ceiling itself,
    because a test that imported the pipeline's constant would agree with it by construction and
    could not catch the pipeline drifting from the paper.
    """
    carriers = []
    for p in sorted((REPO / "research").rglob("*.py")):
        if "test_" in p.name:
            continue
        for i, line in enumerate(p.read_text(encoding="utf-8", errors="replace").split("\n"), 1):
            code = line.split("#")[0]
            if "math.acos(" in code:
                carriers.append(f"{p.relative_to(REPO).as_posix()}:{i}")
    # DERIVED: 1 is the arity of "one place". The whole point of this test is that the ceiling has a
    # single derivation site, so the count it compares against is the claim itself, not a threshold.
    assert len(carriers) == 1, (
        "the aperture ceiling should be derived in exactly one file "
        "(research/code/certify/aperture_ceiling.py), but it is written at:\n  "
        + "\n  ".join(carriers or ["nowhere -- the derivation has gone missing"]))
    assert carriers[0].startswith("research/code/certify/aperture_ceiling.py"), (
        f"the ceiling is derived in {carriers[0]}, not in certify/aperture_ceiling.py")


#: Words the paper uses for small counts, so a claim may be written either way.
COUNT_WORDS = {'no': 0, 'zero': 0, 'one': 1, 'two': 2, 'three': 3, 'four': 4, 'five': 5,
               'six': 6, 'seven': 7, 'eight': 8, 'nine': 9, 'ten': 10}

#: The axioms Lean supplies itself. Everything else is an input this development chose.
FOUNDATIONAL = {'propext', 'Classical.choice', 'Quot.sound'}


def test_every_stated_named_axiom_count_matches_the_build():
    """A "<count> named axiom(s)" claim beside a declaration equals what the build prints.

    The paper states footprints in prose, as a count of NAMED axioms -- those beyond the three
    Lean supplies. Two sibling tests read the same artifact but check different things: that a
    cited declaration carries a `#print axioms`, and that no retired axiom is declared. Neither
    compares the paper's stated footprint to the printed one, so a claim of four named axioms
    stood beside a declaration the build gives one, in two places.

    The footprint is the claim that separates proved from assumed, so a wrong one misreports the
    result's strength. This checks it in both directions: a paper understating its inputs and a
    paper overstating them both fail.

    Only claims whose declaration resolves in the artifact are checked; a count beside a name
    the build does not print is left to the sibling test that catches unprintable citations.
    """
    art = REPO / 'research' / 'data' / '13_dat_axiom_footprints.csv'
    if not art.exists():
        pytest.skip('13_dat_axiom_footprints.csv not regenerated yet')
    import csv
    named = {}
    with art.open(encoding='utf-8', newline='') as fh:
        for row in csv.DictReader(fh):
            axioms = set(row['axioms'].split())
            short = row['declaration'].split('.')[-1]
            named[short] = axioms - FOUNDATIONAL
    # DERIVED: the artifact must cover every declaration the Lean sources ASK to print, so the
    # sufficiency bar is that count rather than a round number. A short artifact -- a warm build
    # replays no info messages -- would otherwise let this pass while checking almost nothing.
    asked = sum(len(re.findall(r'^\s*#print axioms\s', p.read_text(encoding='utf-8', errors='replace'),
                               re.M))
                for p in _lean_files())
    assert len(named) >= asked, (
        f'the footprint artifact carries {len(named)} declarations but the Lean sources ask to '
        f'print {asked}; regenerate it from a cold build')

    text = _paper()
    flat = ' '.join(text.split())
    # a count of named axioms, and the declarations backticked in the run-up to it
    claim = re.compile(r'(?:the same )?([A-Za-z]+|\d+) named axiom')
    checked, bad = 0, []
    for m in claim.finditer(flat):
        tok = m.group(1).lower()
        want = COUNT_WORDS.get(tok)
        if want is None:
            if not tok.isdigit():
                continue
            want = int(tok)
        window = flat[max(0, m.start() - 320):m.start()]
        cands = [n for n in re.findall(r'`([A-Za-z_][A-Za-z0-9_.]*)`', window)
                 if n.split('.')[-1] in named]
        if not cands:
            continue
        # the nearest preceding declaration is the one the claim is about
        decl = cands[-1].split('.')[-1]
        checked += 1
        got = len(named[decl])
        if got != want:
            bad.append(f'the paper says {decl} carries {want} named axiom(s); the build prints '
                       f'{got} ({sorted(named[decl]) or "none"})')
    assert checked, ('no stated named-axiom count could be tied to a declaration; the phrasing '
                     'may have changed and this test would pass vacuously')
    assert not bad, ('a stated axiom footprint disagrees with the build:' + chr(10) + '  '
                     + (chr(10) + '  ').join(bad))


def test_zero_mode_route_named_in_paper_exists_in_lean():
    """Every theorem the second route names must actually exist in the tree.

    Matched on WORD BOUNDARIES, not substrings. A first attempt used `name in paper`, and renaming a
    cited theorem to `wilson_correlation_gap_THAT_DOES_NOT_EXIST` still passed -- the original is a
    prefix of the corruption. A guard that cannot fail the case it was written for is worse than
    none, because it reports a confidence it has not earned.
    """
    paper = PAPER.read_text(encoding="utf-8")
    lean = chr(10).join(
        p.read_text(encoding="utf-8") for p in sorted((LEAN / "MassGap").glob("*.lean")))
    for name in ("zero_mode_lt_of_tension", "no_zero_mode_of_tension_lt_floor",
                 "wilson_correlation_gap", "bd3_link_not_private",
                 "chain_hypotheses_satisfiable"):
        assert re.search(re.escape(name) + r"(?![A-Za-z0-9_])", paper), \
            f"the paper no longer names {name} (or names a corrupted variant of it)"
        assert re.search(r"theorem\s+" + re.escape(name) + r"(?![A-Za-z0-9_])", lean), \
            f"PAPER.md names `{name}` but no `theorem {name}` exists in lean/MassGap/"


def test_zero_mode_bound_numbers_match_the_artifact():
    """The quantitative bound the paper quotes is the one the certificate computes.

    The quoted values are READ OUT OF THE PAPER rather than restated here, and compared at the
    half-ulp of however many decimals the paper writes -- so this guard carries no tolerance of its
    own and cannot drift from the prose it checks.
    """
    import csv
    p = DATA / "9_9_dat_zero_mode_bound.csv"
    if not p.exists():
        pytest.skip("9_9_dat_zero_mode_bound.csv not present")
    rows = list(csv.DictReader(p.open()))
    paper = PAPER.read_text(encoding="utf-8")

    def ulp(written):
        # DERIVED: the half-ulp of the precision the PAPER chose to write, so the comparison is as
        # tight as the prose is and no tolerance is introduced here.
        dp = len(written.split(".")[1]) if "." in written else 0
        return 0.5 * 10.0 ** (-dp)

    m = re.search(r"puts the gapless weight under \$([0-9.]+)\$", paper)
    assert m, "the paper no longer states the gapless-weight bound"
    big = max(rows, key=lambda r: int(r["L"]))
    assert abs(float(big["bound_on_c"]) - float(m.group(1))) <= ulp(m.group(1)), \
        f"paper states {m.group(1)}; artifact gives {big['bound_on_c']} at L={big['L']}"

    m2 = re.search(r"flat to \$?([0-9.]+)\\%", paper)
    if m2:
        gs = [float(r["sum_g"]) for r in rows]
        spread = 100.0 * (max(gs) / min(gs) - 1.0)
        assert abs(spread - float(m2.group(1))) <= ulp(m2.group(1)), \
            f"paper states sum g flat to {m2.group(1)}%; artifact gives {spread:.2f}%"

    assert all(r["theorem_respected"] == "1" for r in rows), \
        "the artifact records a volume where the measurement contradicts the theorem"
