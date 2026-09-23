"""Evaluate the aperture criterion's threshold, and the two read-interface bounds against it.

WHAT THIS IS FOR. `Complete.ym_mass_gap_of_ratio` takes the condition

    (2 * pi) ^ 2 * c / 2 < 1 - 3 ^ (-1/4)

on a substrate-ratio bound `c`. Lean states the condition symbolically and never evaluates it, and
`Substrate.quarter_ratio_fails_aperture_criterion` proves only that `c = 1/4` fails it -- by
`nlinarith` from `pi > 3`, so no decimal appears there either. Any decimal quoted for the threshold
is therefore an evaluation, not something a declaration states, and this script is where it is made.

The comparison it reports is the one that decides which route the chain takes:

* the read interface gives `substrateRatio <= 1/4` (`Substrate.substrateRatio_le_quarter`), and that
  is SHARP -- `Substrate.antipodeRead_moment_eq_quarter_sq` exhibits a read attaining it;
* the flat read gives `(n^2 + 2) / 12`, so a ratio tending to `1/12`
  (`Substrate.flatRead_moment`);
* the criterion admits only `c` below the threshold computed here.

Both interface values exceed the threshold, which is why the chain does not go through
`ym_mass_gap_of_ratio` at all. It goes through `Complete.confinement_on_of_substrate_bound`, which
takes a uniform bound `d2At N beta <= B` and lets the aperture factor `(2 * pi / (N + 1)) ^ 2`
shrink -- `Moment.aperture_factor_tendsto_zero` clears any `B` whatever its size, so that route
carries no threshold and no constant.

Exit status is 0 when the arithmetic is self-consistent; it prints a table and asserts the two
orderings it claims.
"""
from __future__ import annotations

import math

# The floor, exactly as the Lean statements spell it: `(3 : R) ^ (-(1 : R) / 4)`.
FLOOR = 3.0 ** (-1.0 / 4.0)
RHS = 1.0 - FLOOR

# `(2*pi)^2 * c / 2 < RHS`  <=>  `c < RHS * 2 / (2*pi)^2`.
THRESHOLD = RHS * 2.0 / (2.0 * math.pi) ** 2

# What the read interface supplies.
INTERFACE = 1.0 / 4.0          # Substrate.substrateRatio_le_quarter -- sharp
FLAT = 1.0 / 12.0              # Substrate.flatRead_moment, in the aperture limit


def main() -> int:
    print("The aperture criterion of Complete.ym_mass_gap_of_ratio")
    print("    (2*pi)^2 * c / 2  <  1 - 3^(-1/4)")
    print()
    print(f"  3^(-1/4)                              {FLOOR:.6f}")
    print(f"  1 - 3^(-1/4)                          {RHS:.6f}")
    print(f"  admits c strictly below               {THRESHOLD:.6f}")
    print()
    print("Against what the read interface gives:")
    print(f"  substrateRatio <= 1/4 (sharp)         {INTERFACE:.6f}"
          f"   = {INTERFACE / THRESHOLD:.2f} x the threshold")
    print(f"  flat read, (n^2+2)/12 -> 1/12         {FLAT:.6f}"
          f"   = {FLAT / THRESHOLD:.2f} x the threshold")
    print()

    # The claims the document makes, asserted rather than eyeballed.
    assert THRESHOLD < FLAT < INTERFACE, "ordering of the three values changed"
    assert INTERFACE > THRESHOLD, "the interface bound would now satisfy the criterion"
    assert FLAT > THRESHOLD, "the flat read would now satisfy the criterion"

    print("Both exceed it, so no ratio bound available from the interface meets the criterion.")
    print("The chain takes Complete.confinement_on_of_substrate_bound instead, which asks for a")
    print("uniform bound on d2At and carries no threshold: Moment.aperture_factor_tendsto_zero")
    print("clears any B, because the aperture factor shrinks.")
    return 0


if __name__ == "__main__":
    # Only when run as a script: reassigning stdout at import time breaks pytest's capture, and
    # this module is imported by `tests/test_aperture_criterion_margin.py`.
    import io
    import sys

    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")
    raise SystemExit(main())
