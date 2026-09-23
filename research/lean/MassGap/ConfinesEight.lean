import Mathlib
import MassGap.ConfinesSharp

/-!
# MassGap.ConfinesEight — `cosAvgEven` at extent eight, in closed form

The even aperture `ap8 : EvenAp` has `N = 7`, so the lag index runs over `Fin 8` and the lag angles
are `2πd/8`. This file evaluates `cosAvgEven ap8 β` (from `MassGap.ApertureRoute`) at that aperture
and turns the comparison `3^{-1/4} < cosAvgEven ap8 β` into a linear inequality among the
correlations `ρ(d) = wilsonCorrAt 7 (max β 0) d`.

## The eight lag cosines

    d       0     1       2   3        4    5        6   7
    cos     1    √2/2     0  −√2/2    −1   −√2/2     0   √2/2

`cos(2π·2/8) = cos(π/2) = 0`, so `ρ(2)` does not appear in the numerator. `ρ(1)` enters with weight
`√2`, not `1`.

## The two results

`sym_eight_one`, `sym_eight_two` and `sym_eight_three` fold the lag index by `d ↦ -d` in `Fin 8`
(`MomentShape.wilsonCorrAt_neg`), giving `ρ(7) = ρ(1)`, `ρ(6) = ρ(2)`, `ρ(5) = ρ(3)`. With that fold,
`cosAvgEven_extent_eight` reads

    cosAvgEven ap8 β = (ρ(0) + √2·ρ(1) − √2·ρ(3) − ρ(4)) / (ρ(0) + 2ρ(1) + 2ρ(2) + 2ρ(3) + ρ(4))

and `denom_pos_extent_eight` shows that denominator is strictly positive, from
`wilson_reflection_positive_at_even` at `N = 7`, `m = 4`. Clearing it gives
`confines_extent_eight_iff`:

    3^{-1/4} < cosAvgEven ap8 β  ↔  (2c−√2)ρ(1) + 2c·ρ(2) + (2c+√2)ρ(3) + (1+c)ρ(4) < (1−c)ρ(0)

with `c = 3^{-1/4}`. The statements hold for every real `β`; `max β 0` clamps the coupling, so
negative `β` is read at `0`. Nothing here asserts either side of the equivalence at any coupling.

Build: `python research/code/lean_build.py build MassGap.ConfinesEight`.
-/

namespace MassGap.ConfinesEight

-- `cosAvgEven` lives in `ApertureRoute`, `EvenAp` in `EvenAperture`; `ConfinesZero` supplies the
-- extent-four and extent-six companions these proofs are shaped after.
open MassGap MassGap.EvenAperture MassGap.ApertureRoute MassGap.ConfinesZero

/-- The `EvenAp` at extent eight: `N = 7`, `m = 4`, with `N + 1 = 2 * m` by `rfl` and the positivity
side condition by `norm_num`.

DERIVED: `7` is `N`, fixed by `N + 1 = 8`; `4` is `m` with `2 * m = 8`. Both are the shape
`wilson_reflection_positive_at_even` takes, as `ap4` and `ap6` are. -/
abbrev ap8 : EvenAp := ⟨7, 4, rfl, by norm_num⟩

/-! ### Circle symmetry at extent eight

Each of the three folds is `MomentShape.wilsonCorrAt_neg` at extent seven with the negation in
`Fin 8` computed by `decide`. They hold for every real `β` and carry no hypothesis. -/

/-- `ρ(7) = ρ(1)` at extent seven, where `ρ = wilsonCorrAt 7 (max β 0)`. From
`wilsonCorrAt_neg` at lag `1` with `-(1 : Fin 8) = 7`.

DERIVED: `7` is the aperture's `N`; `0` is the clamp floor in `max β 0`; the lags `7` and `1` are the
antipodal pair `d` and `-d` in `Fin 8`. -/
theorem sym_eight_one (β : ℝ) :
    MassGap.wilsonCorrAt 7 (max β 0) 7 = MassGap.wilsonCorrAt 7 (max β 0) 1 := by
  have h := MassGap.MomentShape.wilsonCorrAt_neg 7 (max β 0) (1 : Fin 8)
  have hneg : (-(1 : Fin 8)) = (7 : Fin 8) := by decide
  rwa [hneg] at h

/-- `ρ(6) = ρ(2)` at extent seven. From `wilsonCorrAt_neg` at lag `2` with `-(2 : Fin 8) = 6`.

DERIVED: `7` is the aperture's `N`; `0` is the clamp floor; the lags `6` and `2` are the antipodal
pair `d` and `-d` in `Fin 8`. -/
theorem sym_eight_two (β : ℝ) :
    MassGap.wilsonCorrAt 7 (max β 0) 6 = MassGap.wilsonCorrAt 7 (max β 0) 2 := by
  have h := MassGap.MomentShape.wilsonCorrAt_neg 7 (max β 0) (2 : Fin 8)
  have hneg : (-(2 : Fin 8)) = (6 : Fin 8) := by decide
  rwa [hneg] at h

/-- `ρ(5) = ρ(3)` at extent seven. From `wilsonCorrAt_neg` at lag `3` with `-(3 : Fin 8) = 5`.

DERIVED: `7` is the aperture's `N`; `0` is the clamp floor; the lags `5` and `3` are the antipodal
pair `d` and `-d` in `Fin 8`. -/
theorem sym_eight_three (β : ℝ) :
    MassGap.wilsonCorrAt 7 (max β 0) 5 = MassGap.wilsonCorrAt 7 (max β 0) 3 := by
  have h := MassGap.MomentShape.wilsonCorrAt_neg 7 (max β 0) (3 : Fin 8)
  have hneg : (-(3 : Fin 8)) = (5 : Fin 8) := by decide
  rwa [hneg] at h

/-! ### The eight lag cosines

Each states `cos (2π·d/8)` for one `d : {0,…,7}`. `cos(π/4) = √2/2` is `Real.cos_pi_div_four`; the
rest are reflections of it and of `cos(π/2) = 0` and `cos π = −1`, via `Real.cos_pi_sub`,
`Real.cos_add` and `Real.cos_sub`. In every one, the `2` and the `8` are the angle `2πd/8` at extent
eight, and the remaining numeral is the lag `d`. -/

/-- `cos (2π·0/8) = 1`.

DERIVED: `2` and `8` are the angle `2πd/8` at extent eight; `0` is the lag; `1` is `cos 0`. -/
theorem cos8_0 : Real.cos (2 * Real.pi * (0 : ℝ) / 8) = 1 := by norm_num

/-- `cos (2π·1/8) = cos (π/4) = √2/2`.

DERIVED: `2` and `8` are the angle `2πd/8`; `1` is the lag; the `√2` and the `2` dividing it are
`Real.cos_pi_div_four`'s own value. -/
theorem cos8_1 : Real.cos (2 * Real.pi * (1 : ℝ) / 8) = Real.sqrt 2 / 2 := by
  have h : 2 * Real.pi * (1 : ℝ) / 8 = Real.pi / 4 := by ring
  rw [h, Real.cos_pi_div_four]

/-- `cos (2π·2/8) = cos (π/2) = 0`. This vanishing is why `ρ(2)` is absent from the numerator of
`cosAvgEven_extent_eight`.

DERIVED: the first `2` and the `8` are the angle `2πd/8`; the second `2` is the lag; `0` is
`cos (π/2)`. -/
theorem cos8_2 : Real.cos (2 * Real.pi * (2 : ℝ) / 8) = 0 := by
  have h : 2 * Real.pi * (2 : ℝ) / 8 = Real.pi / 2 := by ring
  rw [h, Real.cos_pi_div_two]

/-- `cos (2π·3/8) = cos (π − π/4) = −√2/2`.

DERIVED: `2` and `8` are the angle `2πd/8`; `3` is the lag; the `√2` and the `2` dividing it are
`Real.cos_pi_div_four`'s value, negated by `Real.cos_pi_sub`. -/
theorem cos8_3 : Real.cos (2 * Real.pi * (3 : ℝ) / 8) = -(Real.sqrt 2 / 2) := by
  have h : 2 * Real.pi * (3 : ℝ) / 8 = Real.pi - Real.pi / 4 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_four]

/-- `cos (2π·4/8) = cos π = −1`.

DERIVED: `2` and `8` are the angle `2πd/8`; `4` is the lag, the antipode at extent eight; `1` is
`|cos π|`. -/
theorem cos8_4 : Real.cos (2 * Real.pi * (4 : ℝ) / 8) = -1 := by
  have h : 2 * Real.pi * (4 : ℝ) / 8 = Real.pi := by ring
  rw [h, Real.cos_pi]

/-- `cos (2π·5/8) = cos (π + π/4) = −√2/2`, the reflection of `cos8_3`.

DERIVED: `2` and `8` are the angle `2πd/8`; `5` is the lag; the `√2` and the `2` dividing it are
`Real.cos_pi_div_four`'s value, negated by `Real.cos_add` at `π`. -/
theorem cos8_5 : Real.cos (2 * Real.pi * (5 : ℝ) / 8) = -(Real.sqrt 2 / 2) := by
  have h : 2 * Real.pi * (5 : ℝ) / 8 = Real.pi + Real.pi / 4 := by ring
  rw [h, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_four]
  ring

/-- `cos (2π·6/8) = cos (π + π/2) = 0`, the reflection of `cos8_2`.

DERIVED: `2` and `8` are the angle `2πd/8`; `6` is the lag; `0` is `cos (π/2)` carried through
`Real.cos_add` at `π`. -/
theorem cos8_6 : Real.cos (2 * Real.pi * (6 : ℝ) / 8) = 0 := by
  have h : 2 * Real.pi * (6 : ℝ) / 8 = Real.pi + Real.pi / 2 := by ring
  rw [h, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two]
  ring

/-- `cos (2π·7/8) = cos (2π − π/4) = √2/2`, the reflection of `cos8_1`.

DERIVED: the leading `2` and the `8` are the angle `2πd/8`; `7` is the lag; the `√2` and the `2`
dividing it are `Real.cos_pi_div_four`'s value, carried through `Real.cos_sub` at `2π`. -/
theorem cos8_7 : Real.cos (2 * Real.pi * (7 : ℝ) / 8) = Real.sqrt 2 / 2 := by
  have h : 2 * Real.pi * (7 : ℝ) / 8 = 2 * Real.pi - Real.pi / 4 := by ring
  rw [h, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi, Real.cos_pi_div_four]
  ring

/-- `cosAvgEven ap8 β` in closed form. With `ρ = wilsonCorrAt 7 (max β 0)`,

    cosAvgEven ap8 β = (ρ(0) + √2·ρ(1) − √2·ρ(3) − ρ(4)) / (ρ(0) + 2ρ(1) + 2ρ(2) + 2ρ(3) + ρ(4)).

The proof unfolds `cosAvgEven` to a sum over `Fin 8`, substitutes `cos8_0`–`cos8_7`, folds the lag
index with `sym_eight_one`–`sym_eight_three`, and clears the common denominator. `ρ(2)` is absent
from the numerator because `cos8_2 = 0`. An identity, holding at every real `β` with no positivity
hypothesis; the denominator's positivity is a separate statement (`denom_pos_extent_eight`).

DERIVED: `7` is the aperture's `N`; `0` is the clamp floor in `max β 0`; the lags `0`, `1`, `2`, `3`,
`4` are the folded half of `Fin 8`; the `√2`s are `2 cos(π/4)` from `cos8_1` and `cos8_3`; the `2`s
multiplying `ρ(1)`, `ρ(2)`, `ρ(3)` are the fold multiplicities, each of those lags being hit twice in
`Fin 8` while `ρ(0)` and `ρ(4)` are hit once. -/
theorem cosAvgEven_extent_eight (β : ℝ) :
    cosAvgEven ap8 β
      = (MassGap.wilsonCorrAt 7 (max β 0) 0
            + Real.sqrt 2 * MassGap.wilsonCorrAt 7 (max β 0) 1
            - Real.sqrt 2 * MassGap.wilsonCorrAt 7 (max β 0) 3
            - MassGap.wilsonCorrAt 7 (max β 0) 4)
        / (MassGap.wilsonCorrAt 7 (max β 0) 0 + 2 * MassGap.wilsonCorrAt 7 (max β 0) 1
            + 2 * MassGap.wilsonCorrAt 7 (max β 0) 2 + 2 * MassGap.wilsonCorrAt 7 (max β 0) 3
            + MassGap.wilsonCorrAt 7 (max β 0) 4) := by
  have hexp : cosAvgEven ap8 β
      = ∑ d : Fin 8, (MassGap.wilsonCorrAt 7 (max β 0) d
          / (∑ d' : Fin 8, MassGap.wilsonCorrAt 7 (max β 0) d'))
        * Real.cos (2 * Real.pi * ((d : ℕ) : ℝ) / (((7 : ℕ) : ℝ) + 1)) := rfl
  rw [hexp]
  simp only [Fin.sum_univ_eight]
  have hd : ((7 : ℕ) : ℝ) + 1 = 8 := by norm_num
  have v0 : (((0 : Fin 8) : ℕ) : ℝ) = 0 := by norm_num
  have v1 : (((1 : Fin 8) : ℕ) : ℝ) = 1 := by norm_num
  have v2 : (((2 : Fin 8) : ℕ) : ℝ) = 2 := by norm_num
  have v3 : (((3 : Fin 8) : ℕ) : ℝ) = 3 := by norm_num
  have v4 : (((4 : Fin 8) : ℕ) : ℝ) = 4 := by norm_num
  have v5 : (((5 : Fin 8) : ℕ) : ℝ) = 5 := by norm_num
  have v6 : (((6 : Fin 8) : ℕ) : ℝ) = 6 := by norm_num
  have v7 : (((7 : Fin 8) : ℕ) : ℝ) = 7 := by norm_num
  rw [hd, v0, v1, v2, v3, v4, v5, v6, v7, cos8_0, cos8_1, cos8_2, cos8_3, cos8_4, cos8_5,
    cos8_6, cos8_7, sym_eight_one β, sym_eight_two β, sym_eight_three β]
  have hS : MassGap.wilsonCorrAt 7 (max β 0) 0 + MassGap.wilsonCorrAt 7 (max β 0) 1
        + MassGap.wilsonCorrAt 7 (max β 0) 2 + MassGap.wilsonCorrAt 7 (max β 0) 3
        + MassGap.wilsonCorrAt 7 (max β 0) 4 + MassGap.wilsonCorrAt 7 (max β 0) 3
        + MassGap.wilsonCorrAt 7 (max β 0) 2 + MassGap.wilsonCorrAt 7 (max β 0) 1
      = MassGap.wilsonCorrAt 7 (max β 0) 0 + 2 * MassGap.wilsonCorrAt 7 (max β 0) 1
        + 2 * MassGap.wilsonCorrAt 7 (max β 0) 2 + 2 * MassGap.wilsonCorrAt 7 (max β 0) 3
        + MassGap.wilsonCorrAt 7 (max β 0) 4 := by ring
  rw [hS]
  field_simp
  ring

/-- The folded lag sum at extent eight is strictly positive:
`0 < ρ(0) + 2ρ(1) + 2ρ(2) + 2ρ(3) + ρ(4)`. It is the second component of
`wilson_reflection_positive_at_even 7 4`, rewritten through `Fin.sum_univ_eight` and the three
symmetry folds. `max β 0` is what supplies that lemma's nonnegative-coupling side condition, so the
statement holds for every real `β`.

DERIVED: `0` on the left is the strict lower bound, and `0` in `max β 0` is the clamp floor; `7` is
the aperture's `N` and `4` the matching `m`; the lags `0`–`4` are the folded half of `Fin 8`; the
`2`s are the fold multiplicities. -/
theorem denom_pos_extent_eight (β : ℝ) :
    0 < MassGap.wilsonCorrAt 7 (max β 0) 0 + 2 * MassGap.wilsonCorrAt 7 (max β 0) 1
      + 2 * MassGap.wilsonCorrAt 7 (max β 0) 2 + 2 * MassGap.wilsonCorrAt 7 (max β 0) 3
      + MassGap.wilsonCorrAt 7 (max β 0) 4 := by
  have hrp := MassGap.wilson_reflection_positive_at_even 7 4 (by norm_num) (by norm_num)
    (le_max_right β (0 : ℝ))
  have hsum : (∑ d, MassGap.wilsonCorrAt 7 (max β 0) d)
      = MassGap.wilsonCorrAt 7 (max β 0) 0 + 2 * MassGap.wilsonCorrAt 7 (max β 0) 1
        + 2 * MassGap.wilsonCorrAt 7 (max β 0) 2 + 2 * MassGap.wilsonCorrAt 7 (max β 0) 3
        + MassGap.wilsonCorrAt 7 (max β 0) 4 := by
    rw [Fin.sum_univ_eight, sym_eight_one β, sym_eight_two β, sym_eight_three β]; ring
  rw [← hsum]
  exact hrp.2

/-- The extent-eight comparison as a linear inequality. With `c = 3^{-1/4}` and
`ρ = wilsonCorrAt 7 (max β 0)`,

    c < cosAvgEven ap8 β ↔ (2c−√2)ρ(1) + 2c·ρ(2) + (2c+√2)ρ(3) + (1+c)ρ(4) < (1−c)ρ(0).

`cosAvgEven_extent_eight` supplies the quotient and `denom_pos_extent_eight` licenses `lt_div_iff₀`.
An equivalence, for every real `β`: it restates the comparison, and does not establish either side at
any coupling.

DERIVED: `3`, `1` and `4` are the threshold `c = 3^{-1/4}`; `7` is the aperture's `N` and `0` in
`max β 0` the clamp floor; the lags `0`–`4` are the folded half of `Fin 8`; the `2`s multiplying `c`
come from clearing the denominator's fold multiplicities; the `√2`s are `2 cos(π/4)` from `cos8_1`
and `cos8_3`; the `1`s in `1 + c` and `1 - c` are `cos8_0` and `−cos8_4`, the two unfolded lags. -/
theorem confines_extent_eight_iff (β : ℝ) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven ap8 β
      ↔ (2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - Real.sqrt 2) * MassGap.wilsonCorrAt 7 (max β 0) 1
          + 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) * MassGap.wilsonCorrAt 7 (max β 0) 2
          + (2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) + Real.sqrt 2) * MassGap.wilsonCorrAt 7 (max β 0) 3
          + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * MassGap.wilsonCorrAt 7 (max β 0) 4
        < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * MassGap.wilsonCorrAt 7 (max β 0) 0 := by
  rw [cosAvgEven_extent_eight β, lt_div_iff₀ (denom_pos_extent_eight β)]
  constructor <;> intro h <;> nlinarith [h]

#print axioms ap8
#print axioms sym_eight_one
#print axioms sym_eight_two
#print axioms sym_eight_three
#print axioms cos8_0
#print axioms cos8_1
#print axioms cos8_2
#print axioms cos8_3
#print axioms cos8_4
#print axioms cos8_5
#print axioms cos8_6
#print axioms cos8_7
#print axioms cosAvgEven_extent_eight
#print axioms denom_pos_extent_eight
#print axioms confines_extent_eight_iff

end MassGap.ConfinesEight
