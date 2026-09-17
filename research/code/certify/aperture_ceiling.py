"""The aperture ceiling, derived ONCE.

Nine files used to carry their own copy of this constant. A copy is how the off-by-one that
`test_every_aperture_ceiling_is_derived_from_the_lag_arity` exists to catch got into two files at
once, so the derivation lives here and the scripts import it.

WHAT IT IS. `Complete.confinement_at_of_substrate_sharp` certifies confinement from

    substrateRatio N b  =  d2At N b / (N+1)^2  <  C_MAX

and `C_MAX` is `arccos(3^{-1/4})^2 / (2 pi)^2`. Both symbols are the development's own: `3^{-1/4}` is
`e^{-kappa0}` with `kappa0 = (1/4) log 3`, counted in `Floor.lean` off directed cube paths, and
`(2 pi)^2` is the aperture the lag angle is read through. No third quantity enters and nothing is
fitted, so there is no magnitude here to pin.

WHY arccos AND NOT THE OLDER FORM. This was `2 (1 - 3^{-1/4}) / (2 pi)^2 = 0.012167`, which comes
from `cos x >= 1 - x^2/2`. That inequality is the tangent to `t |-> cos(sqrt t)` AT THE ORIGIN, so it
is the right bound only for a read concentrated at zero lag, and everywhere else it gives away room.
`Sharp.cos_ge_tangent` takes the tangent at an arbitrary point; at `A = arccos(3^{-1/4})` -- the
threshold itself -- it is exact, and gives `0.012688`. `Sharp.cos_avg_ge_cos_rms` shows that bound is
ATTAINED, by the point mass at `theta = A`, so no argument reading the distribution only through its
second moment can raise it further. The ceiling below is therefore the sharp one, not a choice.

THE EXTENT IS THE LAG ARITY. `Moment.Read N` indexes lags by `Fin (N+1)` and sets
`theta_d = 2 pi d / (N+1)`, so a periodic extent of `L` sites -- lags `d = 0..L-1` -- has `N+1 = L`.
`d2_ceiling` takes that extent and squares it. Squaring one MORE than the lag arity describes a
lattice one site larger than the one measured, which inflates the ceiling and makes every certificate
easier to pass; `test_every_aperture_ceiling_is_derived_from_the_lag_arity` refuses that form.
"""
from __future__ import annotations

import math

#: The entropy floor read as a correlation: `e^{-kappa0}` with `kappa0 = (1/4) log 3`.
FLOOR = 3.0 ** -0.25

#: `1 - 3^{-1/4}`, the right-hand side the ORIGIN-tangent bound compares against. Kept because the
#: necessary-side bound `substrateRatio < (1 - 3^{-1/4})/8` (`Moment.substrate_lt_of_tension_lt_floor`)
#: is stated with it, and that bound is not superseded by the sharp one -- it runs the other way.
APERTURE_RHS = 1.0 - FLOOR

#: The lag angle at which the cosine average sits exactly on the floor, `arccos(e^{-kappa0})`.
APERTURE_ARC = math.acos(FLOOR)

#: The largest `substrateRatio = d2/(N+1)^2` that still certifies confinement. Sharp.
C_MAX = APERTURE_ARC ** 2 / (2 * math.pi) ** 2

#: The necessary-side ceiling: confinement IMPLIES `substrateRatio` is under this
#: (`Moment.Read.substrate_lt_of_tension_lt_floor`, the `8` being `(2/pi^2)(2 pi)^2`). The gap
#: between `C_MAX` and this is irreducible at second-moment order -- it is what the second moment
#: does not carry, not slack in the argument.
C_NECESSARY = APERTURE_RHS / 8.0


def d2_ceiling(extent: float) -> float:
    """The `<d^2>` ceiling at a periodic extent of `extent` sites.

    `extent` is the LAG ARITY `N+1`, i.e. the number of sites the lag index runs over -- not one
    more than it. See the module docstring.
    """
    return C_MAX * extent ** 2
