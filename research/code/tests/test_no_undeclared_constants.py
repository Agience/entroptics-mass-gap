"""Every numeric literal that DECIDES something must be declared DERIVED or CHOSEN.

The canon these repos run under is "no fit, no force, no constant" -- every threshold derived, never
chosen. That rule is stated in the papers and in the review correspondence, and it has been broken
repeatedly in ways nobody could see, because a chosen number in a comparison looks exactly like a
derived one. This test makes the rule executable.

WHAT IT CATCHES, and why each of these was worth catching:

  * `8_7_fig_mhi_lscan.variational_lscan(tol=0.25)` -- a relative-error cut deciding which `m_eff`
    values enter the variational read. Figure 14's "constant at chi2/dof = 0.04" holds ONLY for
    tol in [0.20, 0.30]; at 0.15 the constant fit is rejected at 3.7, at 0.40 at 2.1, and Delta
    itself moves 43% (1.49 -> 1.04) across the range. The cut decides the result.
  * `8_7_fig_gap_correlator.py` uses `m_eff_err < 0.6` for the SAME resolution question, off the
    SAME artifact -- two different chosen cuts for one question.
  * `8_7_fig_mhi_lscan.py`'s `(L >= 12) & (L <= 28)` scaling window -- the window the abstract's
    plateau claim is stated over, and the one that excludes the L=32 point that rejects the
    constant fit.
  * `gap_refinement_invariant.py`'s `max(coul) < 0.3` -- the gaplessness VERDICT of the negative
    control, decided by a chosen number.
  * `ym_crossover_confinement_of_grid.py`'s `xs >= 0.75` -- beta_c is DERIVED (kappa_0/(2r)) and
    then frozen as a literal, so it silently stops tracking `r`.

HOW TO SATISfy IT. Put `# DERIVED: <what derives it>` or `# CHOSEN: <why, and what it costs>` on the
literal's line or the line above. Naming a number as chosen is an acceptable outcome -- hiding it is
not (see the `a-threshold-hides-the-data-under-it` rule: "Where no derived reference exists, NAME the
number as chosen in the docstring rather than dressing it up"). Preferably, replace it: a comparison
between two quantities the same call already measures needs no literal at all.

NOTHING IS EXEMPT. There is no list of "structural" values -- such a list would itself be a set of
constants chosen to decide which constants matter. Arity checks and division guards are reported
like anything else and are DECLARED where they occur, which takes one line and leaves the reader
able to tell a guard from a cut.

WHAT IS IN SCOPE. Every `.py` under `research/` -- library, certificates and tests alike, since a
tolerance that decides a verdict is a threshold whatever file it lives in. Within a file: numeric
literals in comparisons, in function defaults, and BOUND TO NAMES at module or class level. The
last of these is the common case and was the longest-standing hole: `CUT = 0.37` followed by
`x > CUT` puts a Name in the comparison and a literal nowhere the earlier scan looked.
"""
from __future__ import annotations

import ast
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[3]
RESEARCH = REPO / "research"

# NO EXEMPTION LISTS. An earlier version of this guard carried three -- a set of "structural"
# values, a set of "deciding" argument names, and a set of context substrings -- and each was a
# constant chosen to decide which constants matter. That is the defect the guard exists to catch,
# committed by the guard itself: anything off the lists passed silently.
#
# Instead every numeric literal in a decision position is reported, and the judgement about which
# are structural is never made by the tool. Known-undeclared literals live in BASELINE, a dated
# record of debt rather than a rule about which values are acceptable: the guard fails on anything
# NEW, and the baseline is reviewable line by line.
BASELINE = Path(__file__).with_name("undeclared_constants_baseline.txt")


def _scripts() -> list[Path]:
    """EVERY Python file under `research/`. No directory list, no name-based exclusion.

    WHY NOT A CURATED LIST. This used to be three hand-written locations -- `data/`, `code/certify/`
    and one named file -- on the reasoning that those are what produce committed artifacts. That list
    was itself a chosen set deciding which constants matter, which is the defect this guard exists to
    catch, and it hid more than it saw: 195 undeclared deciding literals sat in the 22 files it never
    opened, against 91 in the 43 it did.

    The library and the tests are exactly where a hidden cut does damage. `entroptics_adapter.py`
    carries the read API the certificates call. The tests carry VERDICTS -- `assert |gaps/e0 - 1| <
    0.20` decides whether a free-field read is judged correct, and a tolerance that decides a verdict
    is a threshold whatever file it lives in. A guard that skips the place the verdict is written is
    not a guard.

    `__pycache__` and `.lake` are build output, not source, so they carry nothing to declare.
    """
    out = [p for p in sorted(RESEARCH.rglob("*.py"))
           if "__pycache__" not in p.parts and ".lake" not in p.parts]
    return out


def _declared(lines: list[str], lineno: int) -> bool:
    """Declared if DERIVED:/CHOSEN: appears on the literal's line, or anywhere in the contiguous
    comment block immediately above it.

    The block form matters: a justification worth reading is usually several lines, and requiring it
    to fit on one would push authors back towards a bare number with a terse label."""
    def marks(line: str) -> bool:
        """The marker must BEGIN the comment, so prose that merely uses the word does not count.

        `#:` (the attribute-documentation convention) is stripped alongside `#` and space, so a
        `#: CHOSEN: ...` note on a module constant counts the same as a plain `# CHOSEN: ...`."""
        return line.strip().lstrip("#: ").startswith(("DERIVED", "CHOSEN"))

    i = lineno - 1
    if 0 <= i < len(lines) and marks(lines[i]):
        return True
    i -= 1
    while 0 <= i < len(lines) and lines[i].lstrip().startswith("#"):
        if marks(lines[i]):
            return True
        i -= 1
    return False


def _key(path: Path, hit: tuple[int, str, str]) -> str:
    """Stable identity for one literal: path, what it is, and the source line -- never the line
    NUMBER, so the baseline does not churn when unrelated lines move. Whitespace-normalised on both
    sides so a trailing space cannot look like a new literal."""
    return f"{path.relative_to(REPO).as_posix()}|{hit[1].strip()}|{hit[2].strip()}"


def _undeclared(path: Path) -> list[tuple[int, str, str]]:
    src = path.read_text(encoding="utf-8", errors="replace")
    try:
        tree = ast.parse(src)
    except SyntaxError:
        return []
    lines = src.split("\n")
    hits: list[tuple[int, str, str]] = []

    def numeric(node) -> bool:
        """Any numeric literal. No value is exempt -- see the note on BASELINE."""
        return (isinstance(node, ast.Constant) and isinstance(node.value, (int, float))
                and not isinstance(node.value, bool))

    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.args.defaults:
            args = node.args.args[-len(node.args.defaults):]
            for a, d in zip(args, node.args.defaults):
                if numeric(d) and not _declared(lines, node.lineno):
                    hits.append((node.lineno, f"{a.arg}={d.value}", f"def {node.name}"))
        if isinstance(node, ast.Compare):
            ln = getattr(node, "lineno", 0)
            ctx = lines[ln - 1].strip() if 0 < ln <= len(lines) else ""
            for p in [node.left, *node.comparators]:
                if numeric(p) and not _declared(lines, ln):
                    hits.append((ln, f"compared against {p.value}", ctx[:80]))

    # NAMED constants. A threshold hoisted out of the comparison was invisible to the two checks
    # above: `CUT = 0.37` at module level, then `x > CUT`, puts a Name in the Compare and a Constant
    # nowhere the scan looked. That is how a threshold is normally written, so the guard was blind to
    # the common case while catching the inline one. Every module- or class-level binding of a
    # numeric literal -- singly, or in a tuple/list/set of them -- is reported.
    def numeric_payload(node) -> list:
        if numeric(node):
            return [node.value]
        if isinstance(node, (ast.Tuple, ast.List, ast.Set)):
            vals = [v for e in node.elts for v in numeric_payload(e)]
            return vals
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd)):
            return numeric_payload(node.operand)
        return []

    def named_constants(body) -> None:
        for node in body:
            targets = []
            if isinstance(node, ast.Assign):
                targets = [t for t in node.targets if isinstance(t, ast.Name)]
            elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
                targets = [node.target] if node.value is not None else []
            if not targets:
                if isinstance(node, ast.ClassDef):
                    named_constants(node.body)
                continue
            vals = numeric_payload(node.value)
            if vals and not _declared(lines, node.lineno):
                ln = node.lineno
                ctx = lines[ln - 1].strip() if 0 < ln <= len(lines) else ""
                names = ",".join(t.id for t in targets)
                shown = ",".join(str(v) for v in vals[:6]) + ("..." if len(vals) > 6 else "")
                hits.append((ln, f"named constant {names} = {shown}", ctx[:80]))

    named_constants(tree.body)
    return sorted(set(hits))


def test_no_undeclared_deciding_constants():
    """Every deciding numeric literal carries a DERIVED: or CHOSEN: declaration.

    This is the executable form of the canon. It does not forbid a chosen number -- it forbids an
    UNDECLARED one, so a reader can see at a glance which comparisons are measurements and which are
    cuts, and a new one cannot arrive unnoticed.
    """
    scripts = _scripts()
    assert len(scripts) >= 20, (
        f"only {len(scripts)} scripts discovered; the scan is looking in the wrong place and would "
        "pass vacuously")
    known = set()
    if BASELINE.exists():
        known = {l.strip() for l in BASELINE.read_text(encoding="utf-8").splitlines()
                 if l.strip() and not l.startswith("#")}
    bad = {}
    for p in scripts:
        fresh = [h for h in _undeclared(p) if _key(p, h) not in known]
        if fresh:
            bad[p] = fresh
    if bad:
        lines = []
        for p, h in sorted(bad.items()):
            lines.append(f"  {p.relative_to(REPO)}")
            for ln, what, ctx in h:
                lines.append(f"     L{ln:<5} {what:<26} {ctx}")
        pytest.fail(
            f"{sum(len(h) for h in bad.values())} deciding numeric literal(s) with no DERIVED:/"
            "CHOSEN: declaration.\nPut the declaration on the literal's line or the one above, or "
            "better, replace the literal with a comparison between two quantities the call already "
            "measures.\n" + "\n".join(lines))


def test_no_comment_is_indented_off_the_line_it_annotates():
    """A comment's indent matches the statement below it, across every Python file here.

    WHY THIS EXISTS. Inserting a declaration comment above a line, by string replacement,
    matched an eight-space-prefixed anchor against a TWELVE-space line three separate times in
    one session -- the anchor was a valid substring of the deeper line, so the comment landed
    mid-indent and dedented the statement out of its own block. Twice that produced a
    SyntaxError, which is loud. Once it produced VALID Python that ran a loop-body statement
    once after the loop instead of inside it, which is silent, and nothing in the suite would
    ever have noticed.

    A mismatched indent is not always wrong -- a comment may head a block or sit before a
    dedent -- so this flags only a comment indented DEEPER than the line it precedes, which is
    the shape the bad splice produces and which has no legitimate use.
    """
    bad = []
    for p in sorted((REPO / 'research').rglob('*.py')):
        if '.lake' in p.parts:
            continue
        lines = p.read_text(encoding='utf-8', errors='replace').split(chr(10))
        for i, line in enumerate(lines[:-1]):
            if not line.strip().startswith('#'):
                continue
            nxt = next((l for l in lines[i + 1:] if l.strip()), None)
            if nxt is None or nxt.strip().startswith('#'):
                continue
            ci = len(line) - len(line.lstrip())
            ni = len(nxt) - len(nxt.lstrip())
            # A wrapped TRAILING comment sits aligned under the '#' of the line above, so it is
            # legitimately deeper than the statement that follows. Recognised by that alignment
            # rather than exempted by path, so it cannot hide a splice at the same column.
            prev = lines[i - 1] if i else ''
            hashes = [k for k, ch in enumerate(prev) if ch == '#']
            if hashes and ci in hashes and prev.strip() and not prev.strip().startswith('#'):
                continue
            if ci > ni:
                bad.append(f'{p.relative_to(REPO)}:{i + 1}: comment at column {ci} annotates '
                           f'a line at column {ni} -- {line.strip()[:56]}')
    assert not bad, ('a comment is indented deeper than the statement it annotates, which is '
                     'what a bad string-replacement splice looks like:' + chr(10) + '  '
                     + (chr(10) + '  ').join(bad))
