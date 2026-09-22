"""Does the RELATIVE coupling constant stay bounded as the cell count grows?

WHY THIS EXISTS. `cell_chain_coupling.py` measures `delta = ||B - A||`, the smallest constant
admissible in the ABSOLUTE form bound, and finds it linear in the bond count -- which is what closes
the norm-perturbation route (`CellCouple.coupling_form_extensive`,
`CellCouple.form_perturbation_reaches_finitely_many`). Its own docstring records that the TRUE gap of
`B` survives while `delta` grows, so the failure is the method's.

The Lean side now carries the alternative method. `CellCouple.relative_coupling_form_sum` and
`CellSpectrum.coupled_gap_of_relative_coupling_bound` charge the coupling against the unperturbed
operator's own form instead of against the global norm, and return the gap `(1 - c) * m` from

    -c * <x, A0 x>  <=  <x, V x>        on the vacuum-orthogonal subspace,  c < 1

with NO bond count anywhere. Nothing measured that `c`. This script does.

WHAT IS MEASURED. For each cell count,

    delta  = ||V||                                    -- the absolute constant, the known baseline
    c_rel  = max over x _|_ v0 of  -<x,Vx> / <x,A0x>  -- the relative constant, the new quantity
    gap(B) = E1 - E0 of the coupled operator          -- the physics, for reference

`A0 = A - E0(A)`, so `A0` is positive semidefinite with `A0 >= mu` on the vacuum-orthogonal
subspace. `c_rel` is then the smallest admissible `c`, obtained as `-lambda_min` of the symmetric
pencil `(V, A0)` restricted to that subspace -- an exact generalised eigenvalue, not a search.

WHAT THE ANSWER DECIDES. `CellCouple.shared_locals_force_shrinking_margin` proves the relative route
degenerates when several bonds are charged against the SAME local part. The two models here are
exactly that distinction, and `cell_chain_coupling.py` already names it:

  MODEL M (magnetic straddling plaquettes) -- each bond's term acts on its OWN factor. Distinct
    locals. The route should survive: `c_rel` bounded in the cell count.
  MODEL E (electric shared link) -- the cross term `n_c * n_c'` is a genuine two-cell operator that
    does not factor, which is the OVERLAPPING case. The route may degenerate here.

A bounded `c_rel` in model M and a growing one in model E would be the measured face of the Lean
control. A growing `c_rel` in BOTH would say the relative route buys nothing and the Lean machinery,
though correct, has no physical instance -- which is the outcome this script exists to be able to
report.

WHAT THIS IS NOT. It is a chain of cells, not the four-dimensional lattice, and the truncation is
small. It measures the SHAPE of the scaling in the cell count. The constant that matters physically
is model M's, whose absolute counterpart `adj_form_bound` proves; model E's units are the abelian
cross term written against the SU(2) Casimir, so its magnitude is not in one group's units (that
caveat is `cell_chain_coupling.py`'s own and is repeated here because it applies verbatim).

NEGATIVE CONTROLS, and they decide whether the run is readable at all:
  * coupling off -- `delta` and `c_rel` must both be 0, and `gap(B)` must equal `gap(A)`.
  * ONE bond only -- `c_rel` must NOT grow with the cell count. A harness that reports growth there
    is measuring the Hilbert-space dimension rather than the coupling.

    python research/code/remote_run.py certify/cell_relative_constant.py
    python research/code/remote_run.py certify/cell_relative_constant.py --quick
"""
from __future__ import annotations

import argparse
import os
import sys

import numpy as np
import scipy.linalg as sla

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cell_chain_coupling import model_E, model_M, op_norm  # noqa: E402

#: DERIVED: `1` is the threshold `coupled_gap_of_relative_coupling_bound` needs `c` to sit below for
#: the gap `(1 - c) * m` to be positive. It is forced by that theorem, not chosen here.
C_THRESHOLD = 1.0

#: DERIVED: two eigenvalues are what a gap is -- `E1 - E0` and no others.
K_LOW = 2


def relative_constant(A, V):
    """The smallest `c` with `-c * <x,A0x> <= <x,Vx>` on the vacuum-orthogonal subspace.

    Exact: the negated smallest generalised eigenvalue of the pencil `(V, A0)` restricted there.
    Returns `(c_rel, gap_A, gap_B)`.
    """
    Ad = A.toarray()
    Vd = V.toarray()
    wA, QA = np.linalg.eigh(Ad)
    v0 = QA[:, 0]
    A0 = Ad - wA[0] * np.eye(Ad.shape[0])

    # An orthonormal basis of v0's complement: drop the ground column of A's own eigenbasis.
    Q = QA[:, 1:]
    At = Q.T @ A0 @ Q
    Vt = Q.T @ Vd @ Q
    At = 0.5 * (At + At.T)
    Vt = 0.5 * (Vt + Vt.T)

    # DERIVED: a coupling with no stored entries is the zero operator, whose relative constant
    # is zero. `cell_chain_coupling.op_norm` states the same arithmetic for the same reason.
    if np.abs(Vt).max() == 0.0:
        c_rel = 0.0
    else:
        g = sla.eigh(Vt, At, eigvals_only=True)
        c_rel = float(max(0.0, -g[0]))

    wB = np.linalg.eigvalsh(Ad + Vd)
    return c_rel, float(wA[1] - wA[0]), float(wB[1] - wB[0])


def sweep(kind, d, lam, weight, cells, single_bond):
    rows = []
    for nc in cells:
        nb = nc - 1
        # DERIVED: `1` is the fewest bonds a chain can have and still be coupled; a one-cell
        # chain has none. `0` names the first bond, not a choice among them.
        bonds = [0] if (single_bond and nb >= 1) else list(range(nb))
        if kind == "M":
            A, V = model_M(nc, d, lam, bonds)
        else:
            A, V = model_E(nc, d, lam, bonds, weight)
        c_rel, gap_A, gap_B = relative_constant(A, V)
        rows.append((nc, len(bonds), A.shape[0], op_norm(V), c_rel, gap_A, gap_B))
    return rows


def show(title, rows):
    print(f"\n{title}")
    print(f"  {'cells':>5} {'bonds':>6} {'dim':>6} {'delta=||V||':>12} {'c_rel':>10} "
          f"{'gap(A)':>9} {'gap(B)':>9}")
    for nc, nb, dim, dl, cr, ga, gb in rows:
        print(f"  {nc:>5} {nb:>6} {dim:>6} {dl:>12.6f} {cr:>10.6f} {ga:>9.6f} {gb:>9.6f}")


def trend(rows):
    """Ratio of the last constant to the first, for both constants. >1 means growth."""
    # DERIVED: `2` is the fewest points a trend can be read from -- a ratio needs two ends.
    if len(rows) < 2:
        return None, None
    d0, dN = rows[0][3], rows[-1][3]
    c0, cN = rows[0][4], rows[-1][4]
    # DERIVED: the `0`s guard the division; a constant that starts at zero has no ratio, which
    # is reported as infinite rather than silently as one.
    return (dN / d0 if d0 > 0 else float("inf")), (cN / c0 if c0 > 0 else float("inf"))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--jmax", type=int, default=1, help="cell truncation; dim = 2*jmax+1")
    ap.add_argument("--lam", type=float, default=0.16, help="coupling; 0.16 is the binding end")
    ap.add_argument("--weight", type=float, default=-2.0, help="model E cross-term weight")
    ap.add_argument("--quick", action="store_true", help="smoke sizes only")
    #: A truncation smaller than the physical one. NOT a physical cell: it is here to reach more
    #: cells at the same cost, because the question is the SHAPE of the growth in the cell count.
    ap.add_argument("--d", type=int, default=0, help="override cell dimension (0 = 2*jmax+1)")
    ap.add_argument("--cm", type=int, default=4, help="largest cell count for model M")
    args = ap.parse_args()

    # DERIVED: `0` is the override's off value, not a dimension. The fallback `2*jmax+1` is the
    # character-basis count `Moment`/`CellEnclosure` use, carried from `cell_chain_coupling`.
    d = args.d if args.d > 0 else 2 * args.jmax + 1
    cells_M = [2, 3] if args.quick else list(range(2, args.cm + 1))
    cells_E = [2, 3, 4] if args.quick else [2, 3, 4, 5, 6, 7]

    print(f"cell truncation d = {d}   lambda = {args.lam}   model E weight = {args.weight}")
    print(f"c_rel is compared against {C_THRESHOLD}, the threshold "
          f"`coupled_gap_of_relative_coupling_bound` requires.")

    rM = sweep("M", d, args.lam, args.weight, cells_M, False)
    show("MODEL M -- magnetic straddling plaquettes (DISTINCT locals)", rM)
    rE = sweep("E", d, args.lam, args.weight, cells_E, False)
    show("MODEL E -- electric shared link (OVERLAPPING locals)", rE)

    print("\nNEGATIVE CONTROLS")
    off = sweep("M", d, 0.0, args.weight, cells_M, False)
    # CHOSEN: `1e-12` and `1e-9` are solver precision for a control that must read EXACTLY
    # zero and an EXACT equality of two gaps. They are floating-point slack on quantities whose
    # true values are `0`, not thresholds on smallness -- the control fails at any real value.
    ok_off = all(abs(r[3]) < 1e-12 and abs(r[4]) < 1e-12 and abs(r[5] - r[6]) < 1e-9 for r in off)
    print(f"  coupling off: delta = c_rel = 0 and gap(B) = gap(A)   -> "
          f"{'PASS' if ok_off else 'FAIL'}")

    one = sweep("M", d, args.lam, args.weight, cells_M, True)
    show("  one bond only (c_rel must not grow)", one)
    _, one_growth = trend(one)
    # CHOSEN: `1.05` is the slack allowed in the one-bond control. Adding cells enlarges the
    # vacuum-orthogonal subspace, so new superpositions can raise the maximised ratio slightly
    # even though the coupling is unchanged; what the control refuses is GROWTH WITH THE BOND
    # COUNT, and at one bond there is none to have.
    ok_one = one_growth is not None and one_growth < 1.05
    print(f"  one bond: c_rel growth factor {one_growth:.4f} -> {'PASS' if ok_one else 'FAIL'}")

    print("\nVERDICT")
    dM, cM = trend(rM)
    dE, cE = trend(rE)
    print(f"  model M: delta grows x{dM:.3f}, c_rel grows x{cM:.3f}")
    print(f"  model E: delta grows x{dE:.3f}, c_rel grows x{cE:.3f}")
    print(f"  model M c_rel max = {max(r[4] for r in rM):.6f}"
          f"  (below {C_THRESHOLD}: {max(r[4] for r in rM) < C_THRESHOLD})")
    print(f"  model E c_rel max = {max(r[4] for r in rE):.6f}"
          f"  (below {C_THRESHOLD}: {max(r[4] for r in rE) < C_THRESHOLD})")

    if not (ok_off and ok_one):
        print("\n  CONTROLS FAILED -- the sweep above is not readable.")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
