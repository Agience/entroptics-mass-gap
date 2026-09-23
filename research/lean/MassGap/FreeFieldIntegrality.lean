import Mathlib
import MassGap.FreeFieldLagTwoSix

/-!
# MassGap.FreeFieldIntegrality — the extent-eight lattice momentum square is irrational

Four theorems about the lattice momentum square `p̂² = 2 − 2cos(2πk/n)` at extent `n = 8`, momentum
index `k = 1`. Their content is that this value is `2 − √2` and equals no integer.

## What that bears on

`FreeFieldLagTwo` and `FreeFieldLagTwoSix` carry the free-field momentum squares as natural-number
tables,

    hatSq4 : Fin 4 → ℕ := ![0, 2, 4, 2]
    hatSq6 : Fin 6 → ℕ := ![0, 1, 3, 4, 3, 1]

and their exact-rational arithmetic rests on the entries being naturals: `momSq` sums four of them,
`clearDen6 = 720720 = lcm{1,…,16}` clears every nonzero value, and `clearDen6_exact` checks the
division is exact over all `1296` momenta.

Extents four and six are the even extents whose lag cosines are rational — `1, 0, −1` and
`1, ½, −½, −1`. The entries at the next few extents lie in larger rings:

    extent  4:  0, 2, 4, 2                        ℕ
    extent  6:  0, 1, 3, 4, 3, 1                  ℕ
    extent  8:  0, 2−√2, 2, 2+√2, 4, …            ℤ[√2]
    extent 10:  0, (3−√5)/2, (5−√5)/2, …          ℤ[φ]
    extent 12:  0, 2−√3, 1, 2, 3, …               ℤ[√3]

`lcm{1,…,16}` is a fact about `ℕ`; `ℤ[√2]` carries no least common multiple to clear denominators
with, so a denominator argument there is a norm computation rather than a larger numeral.

The same cosines govern the criterion side: the extent-eight criterion coefficients `2c − √2` and
`5c + √2 + 1` are also outside `ℚ`, while `LagTwoEight` and `ConfinesEight` work because they need
`√2` only as a single algebraic constant, bracketed by `LagTwoEight.sqrt_two_bounds`.

## Scope

The theorems are about one momentum — `k = 1` at extent `8`. They say nothing about extents `10` or
`12`, nothing about `clearDen`, and nothing about any lag-two ratio.

Foundational footprint only (`#print axioms` on every declaration).
Build: `python research/code/lean_build.py build MassGap.FreeFieldIntegrality`.
-/

namespace MassGap.FreeFieldIntegrality

/-- `Real.sqrt 2` is irrational: a restatement of `Nat.prime_two.irrational_sqrt` at the radicand the
rest of the module uses.

DERIVED: `2` is the radicand, and is the only numeral in the statement. -/
theorem sqrt_two_irrational : Irrational (Real.sqrt 2) :=
  (Nat.prime_two.irrational_sqrt)

/-- No integer casts to `2 - Real.sqrt 2`.

The quantifier runs over all of `ℤ`, negatives included, and the inequality is between reals after the
cast. A consequence for the tables above: no `hatSq8 : Fin 8 → ℕ` can hold this value, since a natural
number casts to an integer.

DERIVED: `2` is the constant term of the momentum square `p̂² = 2 − 2cos(2πk/n)` and, here, also its
radicand. It is the only numeral in the statement; the extent and the momentum index enter through
`hatSq_eight_at_one`, not through this statement. -/
theorem two_sub_sqrt_two_not_integer : ∀ n : ℤ, (n : ℝ) ≠ 2 - Real.sqrt 2 := by
  intro n hn
  -- `√2 = 2 − n` would make `√2` rational
  have h2 : Real.sqrt 2 = 2 - (n : ℝ) := by linarith
  have hrat : ¬ Irrational (Real.sqrt 2) := by
    rw [h2]
    intro hirr
    exact hirr ⟨2 - (n : ℚ), by push_cast; ring⟩
  exact hrat sqrt_two_irrational

/-- The extent-eight momentum square at the first nonzero momentum, in closed form:
`2 - 2·cos(2π·1/8) = 2 - √2`.

Proved by reducing the argument to `π/4` and applying `Real.cos_pi_div_four`. This is what ties
`two_sub_sqrt_two_not_integer` to a lattice momentum rather than to an arbitrary surd.

DERIVED: `2` is the constant term and the coefficient in `p̂² = 2 − 2cos(2πk/n)` and the radicand on
the right, `1` is the momentum index `k`, and `8` is the extent `n`. -/
theorem hatSq_eight_at_one : 2 - 2 * Real.cos (2 * Real.pi * (1 : ℝ) / 8) = 2 - Real.sqrt 2 := by
  have h : 2 * Real.pi * (1 : ℝ) / 8 = Real.pi / 4 := by ring
  rw [h, Real.cos_pi_div_four]
  ring

/-- No integer equals the extent-eight momentum square at the first nonzero momentum:
`∀ n : ℤ, (n : ℝ) ≠ 2 - 2·cos(2π·1/8)`.

`hatSq_eight_at_one` composed with `two_sub_sqrt_two_not_integer`. The bound variable `n` ranges over
the integers; the extent appears as a literal inside the cosine, so the statement is about that one
extent and that one momentum index.

DERIVED: `2` is the constant term and the coefficient of `p̂² = 2 − 2cos(2πk/n)`, `1` is the momentum
index `k`, and `8` is the extent `n`. -/
theorem no_integer_hatSq_at_extent_eight :
    ∀ n : ℤ, (n : ℝ) ≠ 2 - 2 * Real.cos (2 * Real.pi * (1 : ℝ) / 8) := by
  intro n
  rw [hatSq_eight_at_one]
  exact two_sub_sqrt_two_not_integer n

#print axioms sqrt_two_irrational
#print axioms two_sub_sqrt_two_not_integer
#print axioms hatSq_eight_at_one
#print axioms no_integer_hatSq_at_extent_eight

end MassGap.FreeFieldIntegrality
