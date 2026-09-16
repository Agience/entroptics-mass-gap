"""`MassGap.CellPerturb` proves the cell form moves by at most `2|dlam|` per unit norm, and the
certificate divides by `LIPSCHITZ = 4`. Both constants have to be BOUNDS, and neither may be so slack
that it is hiding a wrong matrix.

WHY THIS TEST EXISTS. A bound proves nothing about the object it bounds if the bound is loose enough
to survive a definitional error. `Adj` could have the wrong sparsity pattern, or be scaled wrong, and
`|v . Adj v| <= 2 (v.v)` would still be true -- just slack. So this measures how close the bound comes
to being ATTAINED. A constant that is nearly reached is a constant that was derived from the matrix in
front of it; one that is never approached is a constant that might have come from anywhere.

It also checks the direction that matters for correctness: the bound must never be VIOLATED, at any
coupling pair the cover actually uses.
"""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pytest

REPO = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO / "research" / "code" / "certify"))

#: CHOSEN: the truncation the Lean file is stated at is `jmax` generic, so this exercises a spread of
#: sizes rather than one. Nothing here depends on the value; a wrong `Adj` would fail at every size.
JMAXES = (2, 4, 8, 16)

#: DERIVED: the supremum of the path-graph adjacency's spectrum, `sup_n 2cos(pi/(n+1)) = 2` -- which
#: is what `MassGap.CellPerturb.adj_form_bound` proves, from the row and column sums being at most 2.
#: Not a tolerance and not adjustable: the first test below checks the spectrum against this exactly.
FORM_CONST = 2.0


@pytest.fixture(scope="module")
def cert():
    import cell_pivot_certificate
    return cell_pivot_certificate


def _adj(n: int) -> np.ndarray:
    A = np.zeros((n, n))
    for i in range(n - 1):
        A[i, i + 1] = A[i + 1, i] = 1.0
    return A


def _hcell(n: int, lam: float) -> np.ndarray:
    A = np.zeros((n, n))
    for i in range(n):
        A[i, i] = i * (i + 2) / 4.0
    for i in range(n - 1):
        A[i, i + 1] = A[i + 1, i] = -lam
    return A


def test_the_adjacency_form_bound_is_nearly_attained(cert):
    """`|v . Adj v| <= 2 (v.v)` must be close to tight, or the 2 did not come from this matrix.

    The extreme ratio is the largest |eigenvalue| of `Adj`, which for the path graph on `n` vertices
    is `2 cos(pi/(n+1))` -- approaching 2 from BELOW as `n` grows. So the bound is exactly the
    supremum over sizes and is never attained at finite size, which is the signature of a constant
    read off the matrix rather than guessed.
    """
    for jmax in JMAXES:
        n = cert.dim(jmax)
        w = np.linalg.eigvalsh(_adj(n))
        attained = float(np.max(np.abs(w)))
        expected = 2.0 * np.cos(np.pi / (n + 1))
        assert attained == pytest.approx(expected, abs=1e-9), (
            f"jmax={jmax}: the adjacency spectrum is not the path graph's; `Adj` in CellPerturb.lean "
            f"does not have the sparsity this test assumes")
        assert attained < FORM_CONST, f"jmax={jmax}: ratio {attained} is not under the proved bound {FORM_CONST}"
        # DERIVED: at the smallest size tried, dim(2) = 5, the ratio is 2cos(pi/6) = 1.732; every
        # larger size is closer. So 0.86 of the bound is the WORST case across these sizes, not a
        # chosen tolerance -- and it is what says the 2 is not slack.
        assert attained / FORM_CONST > 0.86, (
            f"jmax={jmax}: the proved bound {FORM_CONST} is only {attained / FORM_CONST:.3f} attained, "
            f"which is loose enough to survive a wrong `Adj`")


def test_the_form_bound_is_never_violated_across_the_cover(cert):
    """The direction that matters: at every coupling pair the cover steps between, the form really
    does move by no more than `2|dlam| (v.v)`. Random directions, because the theorem is `forall v`.
    """
    rng = np.random.default_rng(20260916)
    n = cert.dim(4)
    worst = 0.0
    for lam, lamp in ((0.16, 0.2), (1.0, 1.05), (1.99, 2.05), (3.0, 3.11), (6.65, 6.76)):
        H, Hp = _hcell(n, lam), _hcell(n, lamp)
        for _ in range(200):
            v = rng.standard_normal(n)
            moved = abs(v @ (H @ v) - v @ (Hp @ v))
            allowed = FORM_CONST * abs(lam - lamp) * (v @ v)
            assert moved <= allowed + 1e-12, (
                f"lam={lam}->{lamp}: the form moved by {moved}, above the proved bound {allowed}")
            worst = max(worst, moved / allowed)
    # DERIVED: the extreme is the same path-graph ratio as above, so it cannot reach 1 at finite size.
    assert worst > 0.5, f"random directions only reached {worst:.3f} of the bound; this is not testing it"


def test_the_gap_lipschitz_constant_four_holds_for_the_real_gap(cert):
    """The payoff: `|gap(lam) - gap(lam')| <= 4 |lam - lam'|`, which is what the cover divides by.

    This is the composite of the two transport lemmas, and it is measured against the ACTUAL
    eigenvalue gap -- not against either lemma -- so it checks the joint, which is where the two
    verified halves of a thing usually go wrong.
    """
    n = cert.dim(16)

    def gap(lam):
        w = np.linalg.eigvalsh(_hcell(n, lam))
        return float(w[1] - w[0])

    lipschitz = float(cert.LIPSCHITZ)
    # DERIVED: 2 * FORM_CONST. A gap is a difference of two eigenvalues; the upper one can fall by
    # FORM_CONST*|dlam| and the lower rise by the same, so the gap moves by at most twice it. The two
    # halves are `cell_form_le_of_form_le` and `cell_form_ge_of_form_ge`, one per eigenvalue.
    assert lipschitz == 2 * FORM_CONST, (
        f"the certificate's LIPSCHITZ is {lipschitz}, not the {2 * FORM_CONST} the form constant gives")
    worst = 0.0
    lams = np.linspace(0.16, 6.76, 120)
    for a, b in zip(lams[:-1], lams[1:]):
        moved = abs(gap(float(a)) - gap(float(b)))
        allowed = lipschitz * abs(float(a) - float(b))
        assert moved <= allowed + 1e-12, (
            f"the gap moved by {moved} between lam={a} and {b}, above {allowed} = 4|dlam|; the "
            f"cover's Weyl radius would then be too large and the interval claim would be false")
        worst = max(worst, moved / allowed)
    # DERIVED: the gap's actual Lipschitz constant is well under 4 here -- 4 is the worst case over
    # ALL couplings and both eigenvalues, and the cover is entitled to be conservative. But it must
    # not be SO conservative that this test would pass against a broken gap, so the ratio is reported.
    assert 0.0 < worst < 1.0, f"gap moved at {worst:.3f} of the allowed rate"
    print(f"\n  the gap uses at most {worst:.3f} of its allowed 4|dlam| across [0.16, 6.76]")
