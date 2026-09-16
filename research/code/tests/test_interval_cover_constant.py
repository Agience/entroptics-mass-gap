"""The interval cover's Lipschitz constant is a DERIVATION, so it is checked against the spectrum.

`cell_pivot_certificate.LIPSCHITZ = 4` is what turns a finite set of certified couplings into a
continuous cover: a coupling certified at shift `M` covers a neighbourhood of radius
`(M - kappa_0)/4`, because the gap cannot move faster than that.

WHY THIS NEEDS A TEST. The constant comes from an argument -- `HcellR` is linear in `lam`, Weyl bounds
each eigenvalue's movement by `|dlam| * ||A||`, the path graph has `||A|| <= 2`, and the gap is a
difference of two eigenvalues -- and an argument is exactly the kind of thing that is wrong in a way
no exact arithmetic notices. The pivots would still be exact, the walk would still run, and the
neighbourhoods would simply be too wide: a cover that covers nothing, reported as a cover.

So the spectrum is measured directly and the rate compared against the constant. A measured rate at or
below the bound does not prove it; it fails to refute it, which is what a check can do. A rate ABOVE
the bound refutes it outright, and that is the case this exists to catch.
"""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pytest

REPO = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO / "research" / "code" / "certify"))


@pytest.fixture(scope="module")
def cert():
    import cell_pivot_certificate
    return cell_pivot_certificate


def _cell(dim_n: int, lam: float) -> np.ndarray:
    """The SU(2) cell dense: Casimir diagonal `i(i+2)/4`, off-diagonal `-lam`."""
    A = np.zeros((dim_n, dim_n))
    for i in range(dim_n):
        A[i, i] = i * (i + 2) / 4.0
    for i in range(dim_n - 1):
        A[i, i + 1] = A[i + 1, i] = -lam
    return A


def _gap(dim_n: int, lam: float) -> float:
    w = np.linalg.eigvalsh(_cell(dim_n, lam))
    return float(w[1] - w[0])


def test_path_graph_adjacency_norm_is_under_two(cert):
    """`||A|| <= 2` is the half of the derivation that is a fact about the graph, not the cell.

    The exact value is `2 cos(pi/(n+1))`, which is under 2 and approaches it. Checked against the
    computed norm so that "under 2" is verified rather than recalled.
    """
    for jmax in (2, 4, 8, 16):
        n = cert.dim(jmax)
        A = np.zeros((n, n))
        for i in range(n - 1):
            A[i, i + 1] = A[i + 1, i] = 1.0
        norm = float(np.linalg.norm(A, 2))
        exact = 2 * np.cos(np.pi / (n + 1))
        assert norm == pytest.approx(exact, rel=1e-9), (
            f"dim {n}: computed ||A|| = {norm}, but the path graph's norm is 2cos(pi/(n+1)) = {exact}")
        # DERIVED: 2 is the path graph's supremum norm over all sizes -- every row of the
        # adjacency sums to at most 2 (a path vertex has at most two neighbours), and the
        # exact norm 2cos(pi/(n+1)) approaches it from below. Arity, not a tolerance.
        assert norm < 2.0, f"dim {n}: ||A|| = {norm} is not under 2"


def test_the_gap_moves_slower_than_the_covers_constant(cert):
    """The gap's actual rate of change in the coupling stays under `LIPSCHITZ`.

    Measured over the crossover range at several truncations, by finite differences over real steps
    rather than only derivatives -- the cover uses finite neighbourhoods, so a finite step is the
    thing that must obey the bound.
    """
    bound = float(cert.LIPSCHITZ)
    worst, where = 0.0, None
    for jmax in (2, 4, 8):
        n = cert.dim(jmax)
        for lam in np.arange(0.16, 6.66, 0.05):
            for step in (0.01, 0.05, 0.1):
                rate = abs(_gap(n, lam + step) - _gap(n, lam)) / step
                if rate > worst:
                    worst, where = rate, (jmax, float(lam), step)
    assert worst <= bound, (
        f"the gap moves at {worst:.4f} per unit coupling at jmax={where[0]}, lam={where[1]:.3f}, "
        f"step={where[2]} -- above the cover's constant {bound}. Every neighbourhood the walk places "
        f"is then too wide, and `interval_cover` reports a cover that does not cover.")
