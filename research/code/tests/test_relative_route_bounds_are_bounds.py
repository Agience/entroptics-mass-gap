"""The relative route's two halves must bound the spectrum in the directions they claim.

The route certifies `gap >= t - E0_upper` from two separately-computed pieces:

  * `largest_sturm_shift` / `simple_sturm_shift` give `t`, asserted to be a LOWER bound on `E_1` --
    at most one eigenvalue lies below it, so the second-lowest is at or above it;
  * `e0_upper` gives an UPPER bound on `E_0`, from an exact Rayleigh quotient at a trial vector.

Both are certificates: exact rational arithmetic, no floating point in the bound. That makes them
immune to rounding and not immune to being the wrong inequality. A sign slip in either, or a trial
vector paired with the wrong matrix, produces a perfectly exact number pointing the wrong way, and the
certified "gap" would then be a difference of two bounds that do not bracket anything.

So each is checked against the actual spectrum, in the direction it claims. This cannot prove the
bounds; it can refute them, which is what the exact arithmetic cannot do for itself.
"""
from __future__ import annotations

import sys
from fractions import Fraction as Q
from pathlib import Path

import numpy as np
import pytest

REPO = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO / "research" / "code" / "certify"))

#: DERIVED: jmax = 2 is `dim 5`, the smallest truncation at which the relative route has something
#: to say -- it is where `RelTileDemo` works and where two eigenvalues first fall below the floor.
#: The bounds being bounds is a property of the construction, not of the truncation.
JMAX = 2
#: The couplings the relative route actually carries -- above roughly 2.1, where two pivots go
#: negative and the absolute statement is false.
COUPLINGS = ("2.50", "3.00", "4.00", "5.00", "6.00", "6.76")


@pytest.fixture(scope="module")
def cert():
    import cell_pivot_certificate
    return cell_pivot_certificate


def _spectrum(dim_n: int, lam: float) -> np.ndarray:
    A = np.zeros((dim_n, dim_n))
    for i in range(dim_n):
        A[i, i] = i * (i + 2) / 4.0
    for i in range(dim_n - 1):
        A[i, i + 1] = A[i + 1, i] = -lam
    return np.linalg.eigvalsh(A)


def test_the_sturm_shift_is_below_the_second_eigenvalue(cert):
    """`t <= E_1`. If it were above, the certified gap would overstate by however far."""
    n = cert.dim(JMAX)
    khi = cert.check_mu_above_floor(cert.MU_DEFAULT)[1]
    checked = 0
    for s in COUPLINGS:
        lam = Q(s)
        t, gap, note = cert.simple_sturm_shift(JMAX, lam, khi)
        if t is None:
            continue
        E = _spectrum(n, float(lam))
        checked += 1
        assert float(t) <= E[1] + 1e-9, (
            f"lam={s}: the shift {float(t)} is ABOVE E_1 = {E[1]}, so it is not a lower bound on the "
            f"second eigenvalue and the certified gap overstates by {float(t) - E[1]:.3e}")
    # DERIVED: 4 is enough couplings to span the relative route rather than probe one point of it.
    assert checked >= 4, f"only {checked} couplings produced a shift; the route was barely exercised"


def test_the_rayleigh_bound_is_above_the_ground_state(cert):
    """`E0_upper >= E_0`. If it were below, the certified gap would overstate by however far."""
    n = cert.dim(JMAX)
    checked = 0
    for s in COUPLINGS:
        lam = Q(s)
        v = cert.ground_state_trial(JMAX, lam)
        e0 = cert.e0_upper(JMAX, lam, v)
        E = _spectrum(n, float(lam))
        checked += 1
        assert float(e0) >= E[0] - 1e-9, (
            f"lam={s}: the Rayleigh bound {float(e0)} is BELOW E_0 = {E[0]}, so it is not an upper "
            f"bound on the ground state and the certified gap overstates by {E[0] - float(e0):.3e}")
    # DERIVED: 4 is enough couplings to span the relative route rather than probe one point of it.
    assert checked >= 4, f"only {checked} couplings were checked"


def test_the_certified_gap_does_not_exceed_the_true_gap(cert):
    """The two halves together: `t - E0_upper <= E_1 - E_0`, which is the whole claim."""
    n = cert.dim(JMAX)
    khi = cert.check_mu_above_floor(cert.MU_DEFAULT)[1]
    checked = 0
    for s in COUPLINGS:
        lam = Q(s)
        ok, e1, e0, gap, note = cert.certify_relative(JMAX, lam, khi)
        if not ok:
            continue
        E = _spectrum(n, float(lam))
        true_gap = E[1] - E[0]
        checked += 1
        assert float(gap) <= true_gap + 1e-9, (
            f"lam={s}: the certificate claims a gap of {float(gap)} but the cell's is {true_gap}; "
            f"the two bounds do not bracket the spectrum")
    # DERIVED: 4 is enough couplings to span the relative route rather than probe one point of it.
    assert checked >= 4, f"only {checked} couplings certified; the route was barely exercised"
