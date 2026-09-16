"""The entropy floor's enclosure must bracket the number it encloses.

`kappa_0 = (1/4) ln 3` is the constant the whole program is written around: every certificate asks
whether something clears it, the shift `MU_DEFAULT` is refused unless it exceeds the enclosure's upper
end, and `3^{-1/4} = exp(-kappa_0)` is the contraction the volume argument runs on.

`beta_star_enclosure.kappa0_bounds` computes it as exact rationals from a series with a proven tail
bound. That is the right construction and it is also self-referential: the series, the tail bound and
the enclosure all come from the same code, so an error in the series produces an enclosure that is
internally consistent, exactly rational, and around the wrong number. Nothing inside the computation
can notice.

So the enclosure is compared against the transcendental it claims to enclose, computed independently
through `math.log`. Floating point cannot certify anything; it can refute a bracket that has drifted,
which is the failure this exists for. The width is checked too -- an enclosure wide enough to contain
the truth trivially would pass the bracket test and be useless to every caller that divides by it.
"""
from __future__ import annotations

import math
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO / "research" / "code" / "certify"))

#: DERIVED: the enclosure is compared against double precision, so it can only be checked to about
#: 1e-15. Anything tighter would be testing the float, not the enclosure.
FLOAT_SLACK = 1e-15

#: CHOSEN: the widest enclosure still useful to its callers. `MU_DEFAULT - kappa_0` is about 4.7e-5,
#: so an enclosure wider than that would swallow the certificate's whole margin over the floor. This
#: is two orders below it, and the computed width is 3.4e-27 -- the check is nowhere near binding.
USEFUL_WIDTH = 1e-7


@pytest.fixture(scope="module")
def bse():
    import beta_star_enclosure
    return beta_star_enclosure


def test_the_enclosure_brackets_quarter_log_three(bse):
    lo, hi = bse.kappa0_bounds()
    true = math.log(3.0) / 4.0
    assert float(lo) <= true + FLOAT_SLACK, (
        f"the enclosure's lower end {float(lo)!r} is ABOVE (1/4)ln3 = {true!r}; every certificate "
        f"asking whether something clears the floor is then asking about the wrong number")
    assert float(hi) >= true - FLOAT_SLACK, (
        f"the enclosure's upper end {float(hi)!r} is BELOW (1/4)ln3 = {true!r}; `check_mu_above_floor` "
        f"would then accept a shift that does not clear the floor")


def test_the_enclosure_is_narrow_enough_to_be_useful(bse):
    lo, hi = bse.kappa0_bounds()
    width = float(hi - lo)
    # DERIVED: 0 is the arity of an interval -- `hi < lo` is not a wide enclosure, it is not an
    # enclosure at all, and a negative width would make every containment test vacuous.
    assert 0 <= width < USEFUL_WIDTH, (
        f"the enclosure is {width:.3e} wide; a bracket that contains the truth trivially passes the "
        f"bracket test and is useless to a caller that divides by it")


def test_the_derived_floor_matches_the_enclosure(bse):
    """`3^{-1/4} = exp(-kappa_0)`, the contraction the volume argument uses, agrees with it.

    The two are the same constant reached by different routes -- one through the rational enclosure,
    one through a power of 3 -- so a discrepancy means one of them is not what it is labelled.
    """
    lo, hi = bse.kappa0_bounds()
    from_enclosure_hi = math.exp(-float(lo))
    from_enclosure_lo = math.exp(-float(hi))
    direct = 3.0 ** -0.25
    assert from_enclosure_lo - FLOAT_SLACK <= direct <= from_enclosure_hi + FLOAT_SLACK, (
        f"3^(-1/4) = {direct!r} is not inside exp(-kappa_0) over the enclosure "
        f"[{from_enclosure_lo!r}, {from_enclosure_hi!r}]")


def test_the_default_shift_clears_the_enclosure(bse):
    """`MU_DEFAULT` exceeds the enclosure's UPPER end, which is what makes `gap >= mu` imply
    `gap > kappa_0` rather than merely `gap > some lower bound on kappa_0`."""
    sys.path.insert(0, str(REPO / "research" / "code" / "certify"))
    import cell_pivot_certificate as cert
    lo, hi = bse.kappa0_bounds()
    assert cert.MU_DEFAULT > hi, (
        f"MU_DEFAULT = {float(cert.MU_DEFAULT)!r} does not exceed the enclosure's upper end "
        f"{float(hi)!r}; a certificate at that shift would prove a gap that may sit below the floor")
