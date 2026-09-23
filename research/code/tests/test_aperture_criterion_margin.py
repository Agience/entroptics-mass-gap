"""Pin the aperture criterion's evaluated threshold, and prove the check is not vacuous.

`certify/aperture_criterion_margin.py` evaluates the hypothesis of `Complete.ym_mass_gap_of_ratio`
and compares it against the two bounds the read interface supplies. Those decimals are quoted in
`CLAY-ASSEMBLY-FROM-WHAT-EXISTS.md`, and nothing in Lean states them -- the declarations carry the
conditions symbolically -- so the script is their only producer and an unrun producer drifts.

SCOPE, because the numbers below look like thresholds and are not. Nothing in the proof chain reads
any of them. They are DISCLOSURES: evaluations of expressions the Lean statements already contain,
recorded so the document cannot quote a figure the arithmetic does not produce. The conclusion they
support is NEGATIVE about thresholds -- that the ratio route of `ym_mass_gap_of_ratio` is not
available -- and the route the chain does take,
`Complete.confinement_on_of_substrate_bound`, carries no threshold and no constant at all.
"""
import math

from certify import aperture_criterion_margin as M


def test_the_threshold_is_what_the_criterion_admits():
    """`(2*pi)^2 * c / 2 < 1 - 3^(-1/4)` rearranged, recomputed here rather than imported."""
    floor = 3.0 ** (-0.25)
    threshold = (1.0 - floor) * 2.0 / (2.0 * math.pi) ** 2
    assert M.FLOOR == floor
    assert M.THRESHOLD == threshold
    # DERIVED: the three values the document quotes, at the precision it quotes them. Each is an
    # evaluation of an expression the Lean statements already carry -- `3 ^ (-(1:R)/4)`, its
    # complement, and that complement rearranged through `(2*pi)^2 * c / 2`. Nothing decides on
    # them; the assertions stop the document drifting from the arithmetic.
    assert round(M.THRESHOLD, 6) == 0.012167
    # DERIVED: `1 - 3^(-1/4)`, evaluated. A disclosure, not a threshold anything reads.
    assert round(M.RHS, 6) == 0.240164
    # DERIVED: `3^(-1/4)` itself, evaluated. Likewise a disclosure.
    assert round(M.FLOOR, 6) == 0.759836


def test_both_interface_bounds_exceed_the_threshold():
    """The ordering that decides the route: neither interface bound meets the criterion."""
    assert M.THRESHOLD < M.FLAT < M.INTERFACE
    # DERIVED: the two ratios, each the quotient of a bound the read interface proves
    # (`substrateRatio_le_quarter`'s `1/4`, `flatRead_moment`'s `1/12`) by the evaluated threshold
    # above. Disclosures of how far short each route falls, read to two places as the document
    # reads them. The ORDERING asserted on the line above is the content; these are its size.
    assert round(M.INTERFACE / M.THRESHOLD, 2) == 20.55
    # DERIVED: `(1/12) / THRESHOLD`, evaluated. How far short the flat read falls; a disclosure.
    assert round(M.FLAT / M.THRESHOLD, 2) == 6.85


def test_the_comparison_is_not_vacuous():
    """POSITIVE CONTROL. A ratio genuinely below the threshold must pass the criterion.

    Without this, the two assertions above would be satisfied by a threshold of zero, which no
    ratio could ever meet -- the check would report the same thing whatever the arithmetic did.
    """
    # DERIVED: halving is any point strictly inside `(0, THRESHOLD)`; the factor is a witness for
    # an existential and no conclusion depends on which interior point is taken.
    c = M.THRESHOLD / 2.0
    assert (2.0 * math.pi) ** 2 * c / 2.0 < M.RHS, "a ratio below the threshold must satisfy it"
    # and the interface bound must genuinely fail it, which is what Lean proves in
    # `Substrate.quarter_ratio_fails_aperture_criterion`
    assert not ((2.0 * math.pi) ** 2 * M.INTERFACE / 2.0 < M.RHS)


def test_the_script_runs_and_asserts_its_own_orderings():
    # DERIVED: `0` is a process exit status, the success convention, not a measured quantity.
    assert M.main() == 0
