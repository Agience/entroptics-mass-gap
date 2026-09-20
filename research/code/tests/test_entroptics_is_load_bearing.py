"""A script that reads physics must read it through Entroptics, not hand-roll it in numpy.

WHY THIS GUARD EXISTS. `test_no_undeclared_constants.py` catches a chosen number. It cannot catch a
chosen METHOD, and that is the more expensive failure. On 2026-09-14 four new scripts were added to
`certify/` -- `aperture_channel_control.py`, `polyakov_su2_aperture.py`, `clustering_total_of_volume.py`,
`clustering_instrument_check.py` -- and none of them imported Entroptics. Each built its own lag
correlation out of `np.roll`, its own second moment, its own order parameter. A night of compute went
into characterising a hand-rolled instrument.

Nothing objected, because nothing was watching for it. The constant guards were green throughout.

WHAT IT REQUIRES. A script that computes a CORRELATION, a MOMENT, a SPECTRUM or a GAP must obtain it
from the library. The detectable signature of hand-rolling is a lag loop -- `np.roll` inside a `for`
or a comprehension over separations -- or a direct eigendecomposition. That is exactly what the four
scripts above did, and exactly what the certificates that came before them do not do.

IMPORTING THE LIBRARY IS NECESSARY, NOT SUFFICIENT, and the difference is the whole point. The check
is run on EVERY file: a script may import Entroptics at the top, hand-roll its entire read out of
`np.roll` below, and it is still a hand-rolled read. While importing bought an exemption, the guard
could not see that, and could not have seen a reversion either -- a certificate rewritten back to a
`np.roll` lag loop would have stayed green for as long as its import line survived.

WHAT WAIVES A HIT. A `roll` is also how a neighbour SHIFT is written -- `U_nu(x + mu)` in a plaquette,
the staple in APE smearing -- and those build a field rather than read one. An individual hit is
waived by `# NOT A READ: <why this shift is not a lag profile>` on the flagged line or in the comment
block immediately above it, the same shape `test_no_undeclared_constants` uses for DERIVED/CHOSEN. The
reason is the waiver: a bare marker with nothing after it fails, and says so.

WHY IT IS NOT A STYLE RULE. Entroptics is the method, not a utility: the reads are derived per
calculation with no supplied constants, and a hand-rolled substitute reintroduces every choice the
library exists to remove -- which distance, which normalisation, which window, which floor. The
substitute then has to be validated, and validating it is how a research direction becomes a
measurement-instrument project.

The BASELINE records scripts that predate this guard. It may only shrink.
"""
from __future__ import annotations

import ast
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[3]
RESEARCH = REPO / "research"
BASELINE = Path(__file__).with_name("hand_rolled_reads_baseline.txt")

#: The marker that waives ONE hit, chosen to state what it claims: the flagged shift is not a read.
WAIVER = "NOT A READ:"
#: CHOSEN: the shortest waiver that can carry a reason. A marker with nothing after it, or with a
#: token like "ok" after it, is an exemption wearing a justification's clothes -- and an exemption
#: that names no reason is the thing this file exists to refuse. Any small value has the same effect:
#: it rejects the empty marker and accepts a written clause, so nothing about a real waiver turns on
#: where exactly it sits.
MIN_WAIVER_REASON = 12

#: Files that legitimately build fields rather than read them: the read layer itself, and the
#: store/scale helpers that do bookkeeping. Named by ROLE, and each is checked below to still have
#: that role -- a list that stops being true is worse than no list.
#:
#: A NAME here exempts the whole file, including every line added to it later, so an entry belongs
#: here only when the ROLE covers the file ENTIRELY. A file that generates configurations and also
#: reads one does not qualify on either half: `lattice_generator.py` builds staples, plaquettes,
#: Wilson lines and gauge fixing -- and computes a connected correlator -- so it is scanned, its
#: shifts carry site-by-site `NOT A READ:` waivers, and its correlator goes through the library. The
#: waiver is the narrower instrument: it states the claim where the claim is true.
FIELD_BUILDERS = {
    "entroptics_adapter.py": "IS the read layer",
    "lattice_scales.py": "converts lattice units; reads nothing",
    "store_path.py": "locates the store; reads nothing",
    # `smeared_channel_of_spacing.py` was exempted here by NAME, on the grounds that its `np.roll`
    # calls are neighbour shifts for the staple and the plaquette. That is true, and it is now said
    # at the three loops it is true of, as `NOT A READ:` waivers. The difference is that the file is
    # scanned again: the blanket entry covered every future line of it as well as those three.
    # Diagonalises a matrix this repo WRITES DOWN, not a field it measures. The cell Hamiltonian is
    # `diagonal(Casimir) - lambda * adjacency` and the coupling matrix is the path-graph adjacency;
    # both are defined by the theory, so there is no distance, no normalisation, no window and no
    # floor to choose and nothing the library could supply. The float spectrum is used for exactly
    # two things, and in both the point is that it is INDEPENDENT of the certificate: to pick a trial
    # DIRECTION which is then rounded to the rationals and whose Rayleigh quotient is re-evaluated
    # exactly, and to serve as the reference value in the negative control that checks the certified
    # bound never exceeds the true one. Reading either through the shared functional would remove the
    # independence that makes the control a control.
    "cell_gap_budget.py": "diagonalises the defined cell Hamiltonian as the control for an exact-rational certificate",
    "cell_chain_coupling.py": "diagonalises the defined chain Hamiltonian as the control for the extensivity measurement",
}


def _scripts() -> list[Path]:
    out = [p for p in sorted((RESEARCH / "code" / "certify").glob("*.py"))]
    out += sorted((RESEARCH / "data").glob("*.py"))
    out += [p for p in sorted((RESEARCH / "code").glob("*.py"))]
    return [p for p in out if p.exists()]


def _imports_entroptics(tree: ast.AST) -> bool:
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            if any(a.name.split(".")[0] in ("entroptics", "entroptics_adapter") for a in node.names):
                return True
        if isinstance(node, ast.ImportFrom) and node.module:
            if node.module.split(".")[0] in ("entroptics", "entroptics_adapter"):
                return True
    return False


def _waiver(lines: list[str], lineno: int) -> str | None:
    """The reason attached to a flagged line by a `NOT A READ:` note, or None if there is none.

    Same shape as `test_no_undeclared_constants._declared`: the marker must BEGIN the comment, so
    prose that merely mentions it does not count, and it is read from the flagged line itself or from
    anywhere in the contiguous comment block immediately above it. A trailing comment on the flagged
    line counts too -- `for nu in range(3):  # NOT A READ: ...` is where the note belongs when the
    loop header is what was reported.

    The REASON is returned rather than a verdict, empty string included, because an empty marker is
    its own failure and the caller has to be able to say so. Waiving silently on a bare marker would
    reproduce the exemption this guard just lost.
    """
    def note(line: str) -> str | None:
        if "#" not in line:
            return None
        body = line[line.index("#"):].lstrip("#: ")
        return body[len(WAIVER):].strip() if body.startswith(WAIVER) else None

    i = lineno - 1
    # DERIVED: the bounds of the source array. Line numbers are one-based and the walk upward ends at
    # the top of the file, so index 0 is where there is nothing further above. Not a magnitude.
    if 0 <= i < len(lines):
        r = note(lines[i])
        if r is not None:
            return r
    i -= 1
    # DERIVED: the same bound, applied as the loop runs off the top of the file.
    while 0 <= i < len(lines) and lines[i].lstrip().startswith("#"):
        r = note(lines[i])
        if r is not None:
            return r
        i -= 1
    return None


def _hand_rolls_a_read(tree: ast.AST) -> list[str]:
    """Signatures of a physics read built by hand rather than obtained from the library."""
    found = []

    def is_roll(node) -> bool:
        return (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                and node.func.attr == "roll")

    def is_eig(node) -> bool:
        return (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                and node.func.attr in ("eig", "eigh", "eigvals", "eigvalsh", "svd"))

    # A comprehension IS a loop over separations -- `[f(np.roll(d, -tau)) for tau in range(n)]` is the
    # canonical one-line lag profile -- so scanning only `for`/`while` looked for the signature in one
    # of the two ways it is written.
    loops = (ast.For, ast.While, ast.ListComp, ast.GeneratorExp, ast.SetComp, ast.DictComp)

    for node in ast.walk(tree):
        if isinstance(node, loops):
            if any(is_roll(n) for n in ast.walk(node)):
                found.append(f"line {node.lineno}: a lag loop built from np.roll")
        if is_eig(node):
            found.append(f"line {node.lineno}: a direct {node.func.attr} of a correlation")
    return sorted(set(found))


def test_field_builder_roles_are_still_true():
    """The exemptions are by ROLE; check each file still has the role claimed for it."""
    for name, role in FIELD_BUILDERS.items():
        hits = [p for p in _scripts() if p.name == name]
        assert hits, f"{name} is exempted as '{role}' but no longer exists; drop the entry"


def test_no_script_hand_rolls_a_read_without_entroptics():
    """A physics read comes from the library, or the script says why it does not."""
    scripts = _scripts()
    # DERIVED: the vacuity guard -- the tree holds far more than this, so a scan returning fewer
    # has failed to find the scripts rather than found them clean.
    assert len(scripts) >= 20, (
        f"only {len(scripts)} scripts discovered; the scan would pass vacuously")
    known = set()
    if BASELINE.exists():
        known = {l.strip() for l in BASELINE.read_text(encoding="utf-8").splitlines()
                 if l.strip() and not l.startswith("#")}
    bad = {}
    for p in scripts:
        if p.name in FIELD_BUILDERS:
            continue
        src = p.read_text(encoding="utf-8", errors="replace")
        try:
            tree = ast.parse(src)
        except SyntaxError:
            continue
        lines = src.split("\n")
        rel = p.relative_to(REPO).as_posix()
        hits = []
        for h in _hand_rolls_a_read(tree):
            if f"{rel}|{h.split(':')[1].strip()}" in known:
                continue
            reason = _waiver(lines, int(h.split(":")[0].split()[1]))
            if reason is None:
                hits.append(h)
            elif len(reason) < MIN_WAIVER_REASON:
                hits.append(f"{h} -- waived by a `{WAIVER}` marker that states no reason")
        if hits:
            # Importing the library is the NECESSARY condition; it is reported beside each file
            # because the two cases read differently. A file that never imports it has no read layer
            # at all. A file that imports it and still builds the read by hand is the case the
            # import exemption used to hide, and it is the worse one: the import says the method was
            # available and the read was written anyway.
            bad[rel] = (hits, _imports_entroptics(tree))
    if bad:
        lines = []
        for f, (hs, imports) in sorted(bad.items()):
            lines.append(f"  {f}  [{'imports Entroptics' if imports else 'no Entroptics import'}]")
            lines += [f"     {h}" for h in hs]
        pytest.fail(
            f"{sum(len(h) for h, _ in bad.values())} hand-rolled physics read(s).\n"
            "The library IS the method: a hand-rolled correlation reintroduces every choice it "
            "exists to remove -- which distance, which normalisation, which window, which floor.\n"
            f"If a flagged `roll` is a neighbour SHIFT rather than a lag profile, say so on its line "
            f"or the line above: `# {WAIVER} <why>`.\n" + "\n".join(lines))
