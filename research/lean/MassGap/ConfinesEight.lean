import Mathlib
import MassGap.ConfinesSharp

/-!
# MassGap.ConfinesEight — the confinement criterion at extent eight, where the relief peaks

`LagTwoEight` proves the extent-eight THRESHOLD and that it is the largest of the five even extents
tabulated in `LagTwoSix`'s header. What it could not do is reach `ApertureRoute`: `ConfinesSharp`
carries `confines_extent_four_iff` and `confines_extent_six_iff` and there was no extent-eight
counterpart, so the best aperture was a number without a criterion attached. This file supplies it.

## The closed form, and why extent eight is a different shape from six

At extent `2m` the lag angles are `2πd/(2m)`. The cosines are RATIONAL at extents four and six —
`1, 0, −1, 0` and `1, ½, −½, −1, −½, ½` — and at extent eight they are not:

    d       0     1       2   3        4    5        6   7
    cos     1    √2/2     0  −√2/2    −1   −√2/2     0   √2/2

Two consequences, and both matter for why the relief peaks here.

* `ρ(2)` DROPS OUT of the numerator entirely, because `cos(π/2) = 0` — exactly what `ρ(1)` does at
  extent four (`ConfinesZero.cosAvgEven_extent_four`). So the aperture that resolves more lags does
  not simply add terms; it moves which lag is invisible to the cosine average.
* `ρ(1)` enters with weight `√2` rather than `1`, and after clearing the denominator its criterion
  coefficient is `2c − √2 = 0.10545781`. That near-cancellation is small and POSITIVE, and
  `LagTwoEight.bEight_pos` is the fact: `2(c − cos(π/m))` turns negative at `m = 5`, so extent eight
  is the LAST extent at which the `ρ(1)` term still helps.

With circle symmetry folding `ρ(7) = ρ(1)`, `ρ(6) = ρ(2)`, `ρ(5) = ρ(3)`:

    cosAvgEven ap8 β = (ρ(0) + √2·ρ(1) − √2·ρ(3) − ρ(4)) / (ρ(0) + 2ρ(1) + 2ρ(2) + 2ρ(3) + ρ(4))

and clearing the denominator gives the criterion

    c < cosAvgEven ap8 β  ↔  (2c−√2)ρ(1) + 2c·ρ(2) + (2c+√2)ρ(3) + (1+c)ρ(4) < (1−c)ρ(0).

## The consistency check this file IS

`LagTwoEight` took its coefficients from the general formula stated in `LagTwoSix`'s header rather
than from `cosAvgEven` itself. The criterion above supplies them independently, and they agree:
`2c − √2` is `LagTwoEight.bEight` exactly, and the deep lags collected are
`2c + (2c + √2) + (1 + c) = 5c + √2 + 1`, which is `LagTwoEight.aEight` exactly. So the threshold
module rests on the criterion this file proves, and not on a tabulated formula.

## What this does NOT do

It does not discharge the criterion at any coupling — that is B5, and `NonnegArm.LawAbove` is the
remaining obligation at every extent. It states the hypothesis in the aperture-eight form, nothing
more.

Foundational footprint only (`#print axioms` on every declaration).
Build: `python research/code/lean_build.py build MassGap.ConfinesEight`.
-/

namespace MassGap.ConfinesEight

-- The same open list `ConfinesZero` itself carries, plus `ConfinesZero`. `cosAvgEven` lives in
-- `ApertureRoute` and `EvenAp` in `EvenAperture`; copying a proof's body without its opens is what
-- made this file fail twice.
open MassGap MassGap.EvenAperture MassGap.ApertureRoute MassGap.ConfinesZero

/-- The even aperture at extent eight.

DERIVED: `7` is `N` with `N + 1 = 8 = 2 * 4`, and `4` is `m`. Both are read off
`Complete.wilson_reflection_positive_at_even`'s hypotheses, as `ap4` and `ap6` are. -/
abbrev ap8 : EvenAp := ⟨7, 4, rfl, by norm_num⟩

/-! ### Circle symmetry at extent eight -/

theorem sym_eight_one (β : ℝ) :
    MassGap.wilsonCorrAt 7 (max β 0) 7 = MassGap.wilsonCorrAt 7 (max β 0) 1 := by
  have h := MassGap.MomentShape.wilsonCorrAt_neg 7 (max β 0) (1 : Fin 8)
  have hneg : (-(1 : Fin 8)) = (7 : Fin 8) := by decide
  rwa [hneg] at h

theorem sym_eight_two (β : ℝ) :
    MassGap.wilsonCorrAt 7 (max β 0) 6 = MassGap.wilsonCorrAt 7 (max β 0) 2 := by
  have h := MassGap.MomentShape.wilsonCorrAt_neg 7 (max β 0) (2 : Fin 8)
  have hneg : (-(2 : Fin 8)) = (6 : Fin 8) := by decide
  rwa [hneg] at h

theorem sym_eight_three (β : ℝ) :
    MassGap.wilsonCorrAt 7 (max β 0) 5 = MassGap.wilsonCorrAt 7 (max β 0) 3 := by
  have h := MassGap.MomentShape.wilsonCorrAt_neg 7 (max β 0) (3 : Fin 8)
  have hneg : (-(3 : Fin 8)) = (5 : Fin 8) := by decide
  rwa [hneg] at h

/-! ### The eight lag cosines

`cos(π/4) = √2/2` is `Real.cos_pi_div_four`; the other seven are reflections of it and of
`cos(π/2) = 0`, `cos π = −1`, taken through `Real.cos_pi_sub`, `Real.cos_add` and `Real.cos_sub`
exactly as `ConfinesZero.cosAvgEven_extent_six` takes its own. -/

theorem cos8_0 : Real.cos (2 * Real.pi * (0 : ℝ) / 8) = 1 := by norm_num

theorem cos8_1 : Real.cos (2 * Real.pi * (1 : ℝ) / 8) = Real.sqrt 2 / 2 := by
  have h : 2 * Real.pi * (1 : ℝ) / 8 = Real.pi / 4 := by ring
  rw [h, Real.cos_pi_div_four]

theorem cos8_2 : Real.cos (2 * Real.pi * (2 : ℝ) / 8) = 0 := by
  have h : 2 * Real.pi * (2 : ℝ) / 8 = Real.pi / 2 := by ring
  rw [h, Real.cos_pi_div_two]

theorem cos8_3 : Real.cos (2 * Real.pi * (3 : ℝ) / 8) = -(Real.sqrt 2 / 2) := by
  have h : 2 * Real.pi * (3 : ℝ) / 8 = Real.pi - Real.pi / 4 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_four]

theorem cos8_4 : Real.cos (2 * Real.pi * (4 : ℝ) / 8) = -1 := by
  have h : 2 * Real.pi * (4 : ℝ) / 8 = Real.pi := by ring
  rw [h, Real.cos_pi]

theorem cos8_5 : Real.cos (2 * Real.pi * (5 : ℝ) / 8) = -(Real.sqrt 2 / 2) := by
  have h : 2 * Real.pi * (5 : ℝ) / 8 = Real.pi + Real.pi / 4 := by ring
  rw [h, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_four]
  ring

theorem cos8_6 : Real.cos (2 * Real.pi * (6 : ℝ) / 8) = 0 := by
  have h : 2 * Real.pi * (6 : ℝ) / 8 = Real.pi + Real.pi / 2 := by ring
  rw [h, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two]
  ring

theorem cos8_7 : Real.cos (2 * Real.pi * (7 : ℝ) / 8) = Real.sqrt 2 / 2 := by
  have h : 2 * Real.pi * (7 : ℝ) / 8 = 2 * Real.pi - Real.pi / 4 := by ring
  rw [h, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi, Real.cos_pi_div_four]
  ring

/-- **THE CLOSED FORM AT EXTENT EIGHT.** With `ρ = wilsonCorrAt 7 (max β 0)`,

    cosAvgEven ap8 β = (ρ(0) + √2·ρ(1) − √2·ρ(3) − ρ(4)) / (ρ(0) + 2ρ(1) + 2ρ(2) + 2ρ(3) + ρ(4)).

`ρ(2)` is absent from the numerator because `cos(π/2) = 0`, which is the extent-eight analogue of
`ρ(1)`'s absence at extent four. -/
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

/-- **THE READ'S TOTAL MASS AT EXTENT EIGHT IS STRICTLY POSITIVE.** From
`Complete.wilson_reflection_positive_at_even` at `N = 7`, `m = 4`, exactly as
`ConfinesSharp.denom_pos_extent_six` does at `N = 5`, `m = 3`. -/
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

/-- **THE HYPOTHESIS AT EXTENT EIGHT, EXACTLY.** With `c = 3^{−1/4}` and
`ρ = wilsonCorrAt 7 (max β 0)`,

    c < cosAvgEven ap8 β ↔ (2c−√2)ρ(1) + 2c·ρ(2) + (2c+√2)ρ(3) + (1+c)ρ(4) < (1−c)ρ(0).

The coefficients are `LagTwoEight.bEight` on `ρ(1)` and, collected, `LagTwoEight.aEight` on the deep
lags — derived here from `cosAvgEven` rather than from the tabulated formula that module used. -/
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
