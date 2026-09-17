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
over separations -- or a direct eigendecomposition, in a file that never imports the read layer. That
is exactly what the four scripts above did, and exactly what the certificates that came before them do
not do.

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

#: Files that legitimately build fields rather than read them: the generator produces configurations,
#: and the store/scale helpers do bookkeeping. Named by ROLE, and each is checked below to still have
#: that role -- a list that stops being true is worse than no list.
FIELD_BUILDERS = {
    "lattice_generator.py": "generates configurations; it is the thing Entroptics reads",
    "entroptics_adapter.py": "IS the read layer",
    "lattice_scales.py": "converts lattice units; reads nothing",
    "store_path.py": "locates the store; reads nothing",
    # Builds a field from raw links -- APE smearing and the spatial plaquette -- and then
    # hands it to `ym_crossover_confinement_of_grid` for the SAME lag read the Lean
    # consumes. Its `np.roll` calls are neighbour SHIFTS for the staple and the plaquette,
    # not a correlation, so no read choice is reintroduced: which distance, which
    # normalisation and which window all still come from the one read.
    "smeared_channel_of_spacing.py": "builds the smeared operator; reads it with the shared functional",
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


def _hand_rolls_a_read(tree: ast.AST) -> list[str]:
    """Signatures of a physics read built by hand rather than obtained from the library."""
    found = []

    def is_roll(node) -> bool:
        return (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                and node.func.attr == "roll")

    def is_eig(node) -> bool:
        return (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                and node.func.attr in ("eig", "eigh", "eigvals", "eigvalsh", "svd"))

    for node in ast.walk(tree):
        if isinstance(node, (ast.For, ast.While)):
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
        try:
            tree = ast.parse(p.read_text(encoding="utf-8", errors="replace"))
        except SyntaxError:
            continue
        if _imports_entroptics(tree):
            continue
        hits = [h for h in _hand_rolls_a_read(tree)
                if f"{p.relative_to(REPO).as_posix()}|{h.split(':')[1].strip()}" not in known]
        if hits:
            bad[p.relative_to(REPO).as_posix()] = hits
    if bad:
        lines = []
        for f, hs in sorted(bad.items()):
            lines.append(f"  {f}")
            lines += [f"     {h}" for h in hs]
        pytest.fail(
            f"{sum(len(h) for h in bad.values())} hand-rolled physics read(s) in scripts that never "
            "import Entroptics.\nThe library IS the method: a hand-rolled correlation reintroduces "
            "every choice it exists to remove -- which distance, which normalisation, which window, "
            "which floor.\n" + "\n".join(lines))
