"""How the coupled-cell residual `delta` scales with the cell count -- the scalar the gap route needs.

WHAT `delta` IS. `CellSpectrum.gap_of_form_perturbation` reduces "the coupled transfer is gapped" to

    2*delta < mu     with     forall v, |<v,Bv> - <v,Av>| <= delta*<v,v>

where `A` is the DECOUPLED (product-of-cells) Hamiltonian and `B` the coupled one. `B - A` is
symmetric, so the smallest admissible `delta` is exactly the operator norm `||B - A||`. `mu` is the
decoupled gap, which for a product of cells is the SINGLE-cell gap -- intensive, and certified across
`lambda` in `[0.16, 6.76]` by `certify/cell_gap_budget.py`. The budget for `delta` is therefore a
fixed number, and this script measures whether `||B - A||` is one.

WHERE THE COUPLING COMES FROM. Kogut-Susskind is `sum_links E^2 - lambda * sum_plaquettes tr U_p`.
Partition the links into cells. The ELECTRIC term is one-link, so it is exactly decoupled by any such
partition. Two things are left, and both are measured here.

  MODEL M (magnetic, straddling plaquettes). A plaquette whose four links do not all lie in one cell
  has its `tr U_p` deleted from the decoupled `A` and restored in `B`. In the character basis
  `tr U_p` is the nearest-neighbour hopping on that plaquette's own flux -- `CellPerturb.Adj`, the
  same path-graph adjacency the single cell is built from. So each straddling plaquette contributes
  `lambda * ||Adj||`, and `adj_form_bound` already proves `||Adj|| <= 2`.

  MODEL E (electric shared link, in the plaquette/flux basis). A link carried by two neighbouring
  plaquettes has energy `(n_c - n_{c+1})^2`, whose cross term `-2 n_c n_{c+1}` is a genuine two-cell
  operator -- it does not factor, unlike model M's terms, so it probes the case where the bond terms
  overlap. READ ITS SCALE WITH CARE: the cross term is the abelian one, written against the SU(2)
  Casimir diagonal the cell already carries, so the two are not in one group's units. For SU(2) the
  shared-link Casimir is the recoupled spin's and carries 6j weights. What model E is for is the
  SHAPE of the scaling -- linear in the bond count, quadratic in the truncation -- not the constant.
  Model M is the one whose constant is proved (`adj_form_bound`).

Both are sums of LOCAL terms, one per bond of the cell adjacency graph, and the bond count grows with
the volume. The decisive second measurement is the TRUE gap of `B`: if the gap survives while `delta`
grows, the failure is the norm-perturbation METHOD's and not the physics'.

NEGATIVE CONTROLS, and they are the point of the run rather than decoration. With the coupling
switched off, `delta` must be `0` and `gap(B)` must equal `gap(A)` to solver precision. With the
coupling restricted to a SINGLE bond, `delta` must NOT grow with the cell count -- a harness that
reports growth there is measuring the Hilbert-space dimension, not the coupling.

    python cell_chain_coupling.py
    python cell_chain_coupling.py --jmax 2 --cells 6 --lam 0.16
"""
from __future__ import annotations

import argparse
import os
import sys

import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as spl

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

#: CHOSEN: the size above which the lowest eigenvalues are found by Lanczos rather than by a full
#: diagonalisation. It buys run time and nothing else -- both paths return the same eigenvalues, so
#: moving it changes how long the run takes and not what it reports.
DENSE_MAX = 2500


#: DERIVED: the SU(2) Casimir on the retained character states, `j(j+1)` at `i = 2j`, written exactly
#: as `CellEnclosure.Hcell` has it -- drifting from it would measure a different operator than the
#: one the certificate bounds.
def casimir(i: int) -> float:
    return i * (i + 2) / 4.0


def cell_matrix(d: int, lam: float):
    """One cell: Casimir diagonal, `-lam` on the nearest-neighbour band. `CellEnclosure.Hcell`."""
    return sp.diags([casimir(i) for i in range(d)]).tocsr() - lam * adjacency(d)


def electric_only(d: int):
    """A plaquette with its magnetic term deleted -- the decoupled part of a straddling plaquette."""
    return sp.diags([casimir(i) for i in range(d)]).tocsr()


def adjacency(d: int):
    """`CellPerturb.Adj`: the 0/1 path-graph adjacency, the whole `lambda`-dependence of a cell."""
    off = np.ones(d - 1)
    return sp.diags([off, off], [1, -1]).tocsr()


def embed(op, site: int, nsites: int, d: int):
    """`op` on one factor of a `d^nsites` product space, identity elsewhere."""
    out = sp.identity(1, format="csr")
    for s in range(nsites):
        out = sp.kron(out, op if s == site else sp.identity(d, format="csr"), format="csr")
    return out


def flux_diag(d: int, nsites: int, sites):
    """The flux operator `n` on each named site, as a vector of diagonal entries per site.

    Returned as a list of length-`d^nsites` vectors so that products `n_c * n_c'` can be formed
    without materialising a matrix.
    """
    out = []
    for s in sites:
        rep = d ** (nsites - 1 - s)
        blk = d ** s
        v = np.tile(np.repeat(np.arange(d, dtype=float), rep), blk)
        out.append(v)
    return out


# DERIVED: k = 2 is what a gap is -- `E_1 - E_0`, the two lowest eigenvalues and no others.
def low_spectrum(H, k: int = 2):
    """The `k` lowest eigenvalues. Dense below 1200, Lanczos above."""
    n = H.shape[0]
    if n <= DENSE_MAX:
        w = np.linalg.eigvalsh(H.toarray())
        return [float(x) for x in w[:k]]
    # `sigma` shifts to the bottom of the Gershgorin range, which makes shift-invert find the
    # LOWEST eigenvalues rather than the ones nearest zero. Not a tuning knob: it is where the
    # spectrum starts.
    lo = float(H.diagonal().min() - abs(H).sum(axis=1).max())
    w = spl.eigsh(H, k=k, sigma=lo, which="LM", return_eigenvectors=False)
    return sorted(float(x) for x in w)[:k]


def op_norm(V) -> float:
    """`||V||` for symmetric `V` -- the smallest admissible `delta`."""
    # DERIVED: a coupling with no stored entries is the zero operator, whose norm is zero. This is
    # the `coupling off` control's own arithmetic, not a threshold on smallness.
    if V.nnz == 0:
        return 0.0
    n = V.shape[0]
    if n <= DENSE_MAX:
        return float(np.abs(np.linalg.eigvalsh(V.toarray())).max())
    return float(np.abs(spl.eigsh(V, k=1, which="LM", return_eigenvectors=False)).max())


def model_M(nc: int, d: int, lam: float, bonds):
    """Magnetic straddling plaquettes: `nc` cells interleaved with `nc-1` straddling plaquettes.

    A straddling plaquette keeps its electric energy in the decoupled `A` -- the electric term is
    one-link and a link partition cannot split it -- and gets its `tr U_p` only in `B`.
    """
    nsites = nc + (nc - 1)
    straddle = [2 * b + 1 for b in range(nc - 1)]
    A = sp.csr_matrix((d ** nsites, d ** nsites))
    for s in range(nsites):
        # DERIVED: the layout is cells at even sites and straddling plaquettes at odd ones, so the
        # parity IS which kind of plaquette sits there. A straddling plaquette keeps only its
        # electric energy in the decoupled `A`.
        A = A + embed(cell_matrix(d, lam) if s % 2 == 0 else electric_only(d), s, nsites, d)
    V = sp.csr_matrix((d ** nsites, d ** nsites))
    for b in bonds:
        V = V - lam * embed(adjacency(d), straddle[b], nsites, d)
    return A, V


def model_E(nc: int, d: int, lam: float, bonds, weight: float):
    """Electric shared link: `nc` cells, cross term `weight * n_c * n_c'` across each bond."""
    A = sp.csr_matrix((d ** nc, d ** nc))
    for s in range(nc):
        A = A + embed(cell_matrix(d, lam), s, nc, d)
    n = flux_diag(d, nc, list(range(nc)))
    vals = np.zeros(d ** nc)
    for b in bonds:
        vals += weight * n[b] * n[b + 1]
    return A, sp.diags(vals).tocsr()


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--jmax", type=int, default=1, help="cell truncation; dim = 2*jmax+1")
    ap.add_argument("--lam", type=float, default=0.16, help="coupling; 0.16 is the binding end")
    ap.add_argument("--cells", type=int, default=5)
    # DERIVED: -2 is the cross term of `(n_c - n_c')^2`, the shared-link electric energy, in the same
    # units as the Casimir diagonal the cell already carries. It is the group's, not a knob.
    ap.add_argument("--weight", type=float, default=-2.0)
    # DERIVED: the certified single-cell gap over `lambda` in [0.16, 6.76], from
    # `certify/cell_gap_budget.py` at `jmax = 30` on a 661-anchor Lipschitz-4 envelope. The budget
    # `2*delta < mu` is stated against this number and against nothing else.
    ap.add_argument("--mu", type=float, default=0.778787)
    a = ap.parse_args()

    d = 2 * a.jmax + 1
    print(f"jmax={a.jmax} (dim {d})  lambda={a.lam}  cross-term weight={a.weight}  mu={a.mu}")
    print(f"||Adj|| measured = {op_norm(adjacency(d)):.6f}   "
          f"2*cos(pi/(dim+1)) = {2*np.cos(np.pi/(d+1)):.6f}   (adj_form_bound proves <= 2)")
    print()
    hdr = (f"{'model':>6} {'cells':>6} {'bonds':>6} {'dim':>8} {'delta':>10} {'delta/bond':>11} "
           f"{'gap(A)':>9} {'gap(B)':>9} {'2delta/mu':>10} {'2d<mu':>6}")

    for label, which in (("FULL CHAIN", "all"),
                         ("CONTROL: one bond only", "one"),
                         ("CONTROL: coupling off", "none")):
        print(f"--- {label}")
        print(hdr)
        for nc in range(2, a.cells + 1):
            allb = list(range(nc - 1))
            bonds = allb if which == "all" else (allb[:1] if which == "one" else [])
            for name, build in (("M", lambda b: model_M(nc, d, a.lam, b)),
                                ("E", lambda b: model_E(nc, d, a.lam, b, a.weight))):
                A, V = build(bonds)
                B = A + V
                delta = op_norm(V)
                wa, wb = low_spectrum(A), low_spectrum(B)
                gapa, gapb = wa[1] - wa[0], wb[1] - wb[0]
                per = delta / len(bonds) if bonds else float("nan")
                print(f"{name:>6} {nc:>6} {len(bonds):>6} {A.shape[0]:>8} {delta:>10.5f} "
                      f"{per:>11.5f} {gapa:>9.5f} {gapb:>9.5f} {2*delta/a.mu:>10.4f} "
                      f"{'yes' if 2 * delta < a.mu else 'NO':>6}")
        print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
