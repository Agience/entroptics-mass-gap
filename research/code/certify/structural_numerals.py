"""The numerals the two Lean numeral ratchets treat as structural.

The rule is that every number in the development is measured or structural. A measured number needs a
label saying where it comes from (DERIVED, CHOSEN, COMPUTED or Inherited). A structural number does
not: it is fixed by the shape of the object being stated, not by any reading or choice, and asking
for a label on it buries the real constants under thousands of indices.

These four, and only these, are structural:

  * `0` -- the index origin, the additive unit, and the bound of a positivity or non-degeneracy
    hypothesis (`0 < m`, `N ≠ 0`).
  * `1` -- the multiplicative unit, the successor step, and the identity of a group.
  * `2` -- the square (`x ^ 2`, `‖·‖ ^ 2`) and the arity of a pair, a plaquette's two directions.
  * `4` -- the spacetime dimension, `Fin 4`; the development is stated on a four-dimensional
    lattice throughout, so the dimension is the object, not a parameter of it.

Every other numeral is a constant and must be labelled. The set lives here, once, and both
`lean_derived_literals.py` and `tests/test_no_undeclared_lean_constants.py` read it, so the two gates
cannot drift apart on what counts as structural.

Read by digit-run, so a decimal such as `0.5` is not covered: the exemption is for the four integers.
"""
from __future__ import annotations

STRUCTURAL_NUMERALS: frozenset[str] = frozenset({"0", "1", "2", "4"})
