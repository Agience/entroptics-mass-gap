import Mathlib
import MassGap.FreeFieldLagTwoSix

/-!
# MassGap.FreeFieldIntegrality — WHY the exact free-field arm stops at extent six

`FreeFieldLagTwo` and `FreeFieldLagTwoSix` compute the free-field lag-two ratio EXACTLY, as a
rational, at extents four and six. Neither file says why it stops there, and the natural reading —
that extent eight is simply the next transcription — is FALSE. This file records the obstruction.

## The construction's one arithmetic demand

Both files begin the same way:

    hatSq4 : Fin 4 → ℕ := ![0, 2, 4, 2]
    hatSq6 : Fin 6 → ℕ := ![0, 1, 3, 4, 3, 1]

`hatSq` holds the lattice momentum square `p̂² = 2 − 2cos(2πk/n)` **as a natural number**, and
everything downstream depends on that: `momSq` sums four of them, `clearDen6 = 720720 = lcm{1,…,16}`
clears every nonzero value, and `clearDen6_exact` checks the division is exact over all `1296`
momenta. The whole exactness rests on `p̂²` being an integer.

## Where it fails, and it is not a technicality

    extent  4:  0, 2, 4, 2                        ℕ
    extent  6:  0, 1, 3, 4, 3, 1                  ℕ
    extent  8:  0, 2−√2, 2, 2+√2, 4, …            ℤ[√2]   ← not ℕ
    extent 10:  0, (3−√5)/2, (5−√5)/2, …          ℤ[φ]
    extent 12:  0, 2−√3, 1, 2, 3, …               ℤ[√3]

`two_sub_sqrt_two_not_integer` below proves the extent-eight entry is irrational, hence not a value
`hatSq8 : Fin 8 → ℕ` could hold. **Extents four and six are the only even extents at which the
construction is available at all**, because they are the only ones whose lag cosines are rational —
`1, 0, −1` and `1, ½, −½, −1`.

And `clearDen`'s role does not survive the move: `lcm{1,…,16}` is meaningful in `ℕ`, and `ℤ[√2]` has
no such least common multiple to clear the denominators with. Replacing it needs a norm argument, not
a bigger numeral.

## What this costs, in the one place it matters

`LagTwoEight` proves the extent-eight threshold `0.0354567` and `ConfinesEight` its criterion, and
the free-field ratio there is about `0.000493` — a margin of roughly `71.9×` against `65.6×` at
extent six. **That extra room is real and is NOT reachable by this method.** The extent-eight
threshold, criterion, sharpness and strong-coupling arm all transcribe cleanly, because they need
`√2` only as a single algebraic constant that `LagTwoEight.sqrt_two_bounds` brackets. The weak arm
does not, because `fsCorr` is a sum over `4096` momenta whose exactness is an integrality property of
every summand.

So the assembled two-arm route `FreeFieldLagTwoSix.confines_of_arms_six` stays at extent SIX, and the
extent-eight chain is the better bar with a strong arm and no exact weak arm. Getting the weak arm
there needs `ℤ[√2]` arithmetic with a norm-based denominator, or certified interval arithmetic —
different work, not more of the same.

Foundational footprint only (`#print axioms` on every declaration).
Build: `python research/code/lean_build.py build MassGap.FreeFieldIntegrality`.
-/

namespace MassGap.FreeFieldIntegrality

/-- **`√2` IS IRRATIONAL**, in the form the obstruction needs. -/
theorem sqrt_two_irrational : Irrational (Real.sqrt 2) :=
  (Nat.prime_two.irrational_sqrt)

/-- **THE EXTENT-EIGHT MOMENTUM SQUARE IS NOT AN INTEGER.**

`p̂² = 2 − 2cos(2πk/8)` at `k = 1` is `2 − 2·(√2/2) = 2 − √2`, and no integer equals it. So there is
no `hatSq8 : Fin 8 → ℕ` holding the extent-eight momentum squares, and the construction
`FreeFieldLagTwoSix` runs on is unavailable there — not harder, unavailable.

DERIVED: no numeral is chosen. `2` is the momentum-square's own constant, `8` is the extent, `1` is
the first nonzero momentum index, and `cos(2π/8) = cos(π/4) = √2/2` is exact. -/
theorem two_sub_sqrt_two_not_integer : ∀ n : ℤ, (n : ℝ) ≠ 2 - Real.sqrt 2 := by
  intro n hn
  -- `√2 = 2 − n` would make `√2` rational
  have h2 : Real.sqrt 2 = 2 - (n : ℝ) := by linarith
  have hrat : ¬ Irrational (Real.sqrt 2) := by
    rw [h2]
    intro hirr
    exact hirr ⟨2 - (n : ℚ), by push_cast; ring⟩
  exact hrat sqrt_two_irrational

/-- **AND THAT VALUE IS THE EXTENT-EIGHT MOMENTUM SQUARE**, stated so the previous theorem is about
the right quantity rather than an arbitrary surd. -/
theorem hatSq_eight_at_one : 2 - 2 * Real.cos (2 * Real.pi * (1 : ℝ) / 8) = 2 - Real.sqrt 2 := by
  have h : 2 * Real.pi * (1 : ℝ) / 8 = Real.pi / 4 := by ring
  rw [h, Real.cos_pi_div_four]
  ring

/-- **THE OBSTRUCTION, ASSEMBLED.** The extent-eight momentum square at the first nonzero momentum is
not an integer, so no `Fin 8 → ℕ` table holds it.

This is the exact-arithmetic counterpart of the fact `ConfinesEight` meets from the other side: the
extent-eight CRITERION coefficients are `2c − √2` and `5c + √2 + 1`, also outside `ℚ`. The lattice
momenta and the criterion cosines are the SAME cosines, so a single fact — that `cos(2π/8)` is
irrational where `cos(2π/4)` and `cos(2π/6)` are not — governs both. -/
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
