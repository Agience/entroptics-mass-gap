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

import re
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[3]
PAPER = REPO / "research" / "PAPER.md"
LEAN = REPO / "research" / "lean"

#: Backticked names in the paper that are not Lean declarations: python identifiers, dtypes, store
#: directories, Lean keywords, and axioms supplied by Lean core rather than by this development.
NOT_LEAN = {
    "sorry", "propext", "float32", "configs_links_su2", "mp",
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
    py_src = "\n".join(p.read_text(encoding="utf-8", errors="replace")
                       for p in (REPO / "research").rglob("*.py") if ".lake" not in p.parts)
    unresolved = []
    for name in sorted(cited):
        pat = re.compile(rf"(^|\s)(axiom|theorem|lemma|def|abbrev|structure|class)\s+{re.escape(name)}\b"
                         rf"|^\s+{re.escape(name)}\s*:", re.M)
        if pat.search(lean_src) or pat.search(py_src) or f"{name}.py" in text or name in py_src:
            continue
        unresolved.append(name)
    assert not unresolved, f"PAPER.md cites names that resolve nowhere: {unresolved}"


# The theorems PAPER.md states an axiom footprint for, with the passage that states it. A footprint
# claim is only machine-checked if the declaration carries a `#print axioms`, which puts its real
# footprint in the build log on every build; without one the claim is prose. This list is curated
# rather than derived: the ledger's evidence cells name supporting machinery alongside the result
# (row 1372 alone lists fifteen LDL/Sturm lemmas), and no rule over the prose separates "the paper
# claims a footprint for this" from "the paper cites this as a step" without flagging both.
FOOTPRINT_CLAIMS = {
    "ym_mass_gap_certified":            "Sec 13: footprint = three foundational + the named axioms",
    "ym_mass_gap_grid_certified":       "Sec 13: 'carries that same footprint, no d2_le_bound'",
    "ym_mass_gap_spectral":             "Sec 13: 'the three foundational axioms only'",
    "ym_crossover_confinement_of_grid": "Sec 13: 'footprint three foundational + wilson_reflection_positive'",
    "ym_existence_and_gap":             "Sec 13 ledger: 'footprint = the four named axioms'",
    "ym_wightman":                      "Sec 13 ledger: 'adds the OS->Wightman reconstruction (six in total)'",
    "gap_uniform_of_cell":              "Sec 13 ledger: 'proved (foundation-only)'",
    "gap_uniform_of_cell_intensive":    "Sec 13 ledger: 'proved (foundation-only)'",
    "ym_volume_gap_cell_grounded":      "Sec 13 ledger: 'proved (foundation-only)'",
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
    `gap_uniform_of_cell`, `gap_uniform_of_cell_intensive` and `ym_volume_gap_cell_grounded`, and
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
#                                     **plus `wilson_reflection_positive` alone**"
#   ym_crossover_confinement_of_grid "footprint three foundational + `wilson_reflection_positive`"
#   ym_mass_gap_grid_certified       "carries that same footprint, no `d2_le_bound`"
#   ym_existence_and_gap             "carries the four named axioms"
#   ym_wightman                      "adds the OS->Wightman reconstruction ..., six in total"
#   ym_mass_gap_spectral             "the three foundational axioms only"
#   the volume row                   "proved (foundation-only)"
NAMED_FOOTPRINTS = {
    "ym_mass_gap_certified":            {"wilson_reflection_positive"},
    "ym_crossover_confinement_of_grid": {"wilson_reflection_positive"},
    "ym_mass_gap_grid_certified":       {"wilson_reflection_positive"},
    "ym_existence_and_gap":             {"wilson_reflection_positive", "ym_character",
                                         "ym_asymfree", "d2_le_bound"},
    "ym_wightman":                      {"wilson_reflection_positive", "ym_character",
                                         "ym_asymfree", "d2_le_bound",
                                         "os_reconstruction", "WightmanTheory"},
    "ym_mass_gap_spectral":             set(),
    "gap_uniform_of_cell":              set(),
    "gap_uniform_of_cell_intensive":    set(),
    "ym_volume_gap_cell_grounded":      set(),
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


def test_the_grid_route_really_drops_d2_le_bound():
    """Sec 13's specific claim that the grid-routed flagship carries no `d2_le_bound`.

    This is the one that matters for the open items: `d2_le_bound` is a statistical bound, and the
    grid route is what the paper offers as the deterministic replacement. Checked on its own so the
    failure names it rather than appearing as one line in a table diff.
    """
    art = REPO / "research" / "data" / "13_dat_axiom_footprints.csv"
    if not art.exists():
        pytest.skip("13_dat_axiom_footprints.csv not regenerated yet")
    import csv
    with art.open(encoding="utf-8", newline="") as fh:
        rows = {r["declaration"].split(".")[-1]: r["axioms"] for r in csv.DictReader(fh)}
    for decl in ("ym_mass_gap_grid_certified", "ym_crossover_confinement_of_grid"):
        assert decl in rows, f"the build printed no footprint for {decl}"
        assert "d2_le_bound" not in rows[decl], \
            f"{decl} depends on d2_le_bound; Sec 13 says the grid route carries 'no d2_le_bound'"


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


def test_the_pinned_witness_value_is_the_one_lean_defines():
    """Sec 13's `mHiYM = 1/5` is the rational Lean actually defines, and the step it claims holds.

    `ym_mass_gap_spectral` is the flagship the paper says carries the three foundational axioms ONLY,
    and the reason it does is that its witness modes are pinned to a rational rather than a measured
    value: the Lean step is `1/5 <= 3^(-1/4)`. If that rational were edited in Complete.lean the
    paper would go on quoting the old one, and the claim that the footprint is foundation-only would
    be attached to a different number than the one proved.

    Both the value and the inequality are checked: a rational that no longer clears the ceiling would
    make the citation meaningless even if the paper and Lean still agreed on the digits.
    """
    import re
    from fractions import Fraction

    lean = (REPO / "research" / "lean" / "MassGap" / "Complete.lean").read_text(encoding="utf-8")
    m = re.search(r"def\s+mHiYM\s*:\s*(?:ℝ|Real)\s*:=\s*([0-9]+)\s*/\s*([0-9]+)", lean)
    assert m, "mHiYM is no longer defined as a rational literal in Complete.lean; update this test"
    defined = Fraction(int(m.group(1)), int(m.group(2)))

    ceiling = 3.0 ** -0.25
    assert float(defined) <= ceiling, (
        f"mHiYM = {defined} does not clear the aperture ceiling 3^(-1/4) = {ceiling:.4f}; "
        "the Lean step the paper cites would not hold")

    text = PAPER.read_text(encoding="utf-8")
    BS = chr(92)
    # Scoped to the passage that names mHiYM. Searching the whole paper for the rational would be
    # nearly vacuous: kappa_0 is written \tfrac14\ln3, so 1/4 is already present and a Lean
    # definition that drifted to 1/4 would still be "found".
    where = text.find("mHiYM")
    assert where != -1, "the paper no longer cites mHiYM; update this test"
    window = text[max(0, where - 400):where + 400]
    quoted = set()
    for mm in re.finditer(re.escape(BS + "tfrac") + r"(?:\{(\d+)\}\{(\d+)\}|(\d)(\d))", window):
        a, b, c, d = mm.groups()
        quoted.add(Fraction(int(a), int(b)) if a else Fraction(int(c), int(d)))
    assert quoted, "the passage naming mHiYM states no rational; update this test"
    assert defined in quoted, (
        f"Complete.lean defines mHiYM = {defined}, but the passage citing it states "
        f"{sorted(str(q) for q in quoted)} -- the paper is not quoting the pinned value")


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


def test_the_asymptotic_freedom_axiom_and_the_floor_theorem_pin_the_same_value():
    """`ym_asymfree` converges to the value `muInf_lt_floor` proves is below the floor.

    Sec 13 tells this as one story: the axiom gives the convergence mu_YM -> 0.0326, and the
    below-floor half is the theorem. That only holds together if both carry the SAME constant --
    an axiom converging to one value while the theorem clears a different one would leave the
    weak end unproved with nothing in the tree objecting, since neither file mentions the other.
    """
    import re

    lean_dir = REPO / "research" / "lean" / "MassGap"
    complete = (lean_dir / "Complete.lean").read_text(encoding="utf-8")
    freefield = (lean_dir / "FreeField.lean").read_text(encoding="utf-8")

    a = re.search(r"axiom\s+ym_asymfree\s*:.*?nhds\s*\(\s*([0-9.]+)\s*:", complete, re.S)
    assert a, "ym_asymfree no longer states a literal limit; update this test"
    t = re.search(r"theorem\s+muInf_lt_floor\s*:\s*\(\s*([0-9.]+)\s*:", freefield)
    assert t, "muInf_lt_floor no longer states a literal bound; update this test"

    limit, proved = float(a.group(1)), float(t.group(1))
    assert abs(limit - proved) < 1e-9, (
        f"ym_asymfree converges to {limit} but muInf_lt_floor proves {proved} is below the floor; "
        "Sec 13 presents these as the same value, so the weak end is not established")
