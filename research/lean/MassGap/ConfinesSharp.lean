import MassGap.ConfinesZero

/-!
# MassGap.ConfinesSharp — the floor criterion as a linear inequality, at extents four and six

Writes `c < cosAvgEven ap β` as a linear inequality in the correlation values, in both directions.
Throughout, `c` is `(3 : ℝ) ^ (-(1 : ℝ) / 4)` and `ρ` is `MassGap.wilsonCorrAt N (max β 0)`, whose
lag index type is `Fin (N + 1)`; `N = 3` gives the four lags of `ap4` and `N = 5` the six lags of
`ap6`.

## What is proved

* `sym_four`, `sym_six_one`, `sym_six_two` — circle symmetry at the individual lags, from
  `MomentShape.wilsonCorrAt_neg`: lag `3` equals lag `1` at four lags, and lags `5`, `4` equal lags
  `1`, `2` at six.
* `denom_pos_extent_four`, `denom_pos_extent_six` — the total mass, folded by those symmetries into
  `ρ(0) + 2ρ(1) + ρ(2)` and `ρ(0) + 2ρ(1) + 2ρ(2) + ρ(3)`, is strictly positive. This is the second
  clause of `Complete.wilson_reflection_positive_at_even`, and it is what licenses clearing the
  denominator of `cosAvgEven`.
* `confines_extent_four_iff` —

      c < cosAvgEven ap4 β   ↔   2c·ρ(1) + (1+c)·ρ(2) < (1−c)·ρ(0),

  an equivalence, so it decides the left side rather than implying it.
  `not_confines_extent_four_iff` is its contrapositive, with both sides negated and the order
  reversed.
* `confines_extent_six_iff` —

      c < cosAvgEven ap6 β ↔ (2c−1)·ρ(1) + (1+2c)·ρ(2) + (1+c)·ρ(3) < (1−c)·ρ(0).

  `two_c_sub_one_pos` proves `2c − 1 > 0`, so every coefficient on the left is positive at six lags
  as at four: the first lag enters with the same sign as the others, although
  `ConfinesZero.cosAvgEven_extent_six` gives it weight `+1` in the numerator. The weight `2` it also
  carries in the denominator is what reverses that sign on clearing.
* `shape_admits_failure`, `shape_admits_success` — two profiles satisfying `MomentShape.Shape 4 2`,
  with positive contact value and positive total mass, one on each side of the extent-four
  criterion. The flat profile `ρ ≡ 1` fails it; `wilsonCorrAt 3 0`, the ensemble's own profile at
  zero coupling, meets it. So `Shape 4 2` alone does not determine which side of the criterion a
  profile falls on.

## Scope

Every statement is about `cosAvgEven` and `wilsonCorrAt` at a given `β`, with `max β 0` clamping the
coupling to be nonnegative. The two `iff`s are restatements: they move the criterion from an average
to a linear inequality and establish nothing about the values `wilsonCorrAt` takes. `ρ` in
`shape_admits_failure` and `shape_admits_success` is existentially quantified, so those two are
statements about `Shape 4 2`, not about the ensemble.

DERIVED: no numeral in this file is a magnitude. `c = 3^{−1/4}` is `e^{−κ₀YM}` at `κ₀YM = ¼ log 3`,
carried in from `ApertureRoute.ConfinesAtAnAperture`, so its `3`, `1` and `4` are that constant's.
`3` and `5` are the `N` of `wilsonCorrAt N`, read off
`Complete.wilson_reflection_positive_at_even`'s hypotheses, and the lag literals `0, 1, 2, 3, 4, 5`
index `Fin (N + 1)`. The coefficients `1 ± c`, `2c`, `1 + 2c` and `2c − 1` are the lag cosines
`1, 0, −1` and `1, ½, −½, −1` combined with `c` by `field_simp` when the denominator is cleared.
-/

namespace MassGap.ConfinesSharp

open MassGap MassGap.EvenAperture MassGap.ApertureRoute MassGap.ConfinesZero

/-! ## 0. The two closed-form denominators are strictly positive -/

/-- `wilsonCorrAt 3 (max β 0) 3 = wilsonCorrAt 3 (max β 0) 1`. `MomentShape.wilsonCorrAt_neg` at the
lag `1`, rewritten through `-(1 : Fin 4) = 3`, which `decide` settles.

Holds at every real `β`; the coupling is clamped by `max β 0` and the symmetry does not depend on it.

DERIVED: `3` is the `N` of `wilsonCorrAt N`, so the lags form `Fin 4`. The lag literals `3` and `1`
are negatives of one another in `Fin 4`, which is what circle symmetry identifies; `0` is the lower
clamp on the coupling. -/
theorem sym_four (β : ℝ) :
    MassGap.wilsonCorrAt 3 (max β 0) 3 = MassGap.wilsonCorrAt 3 (max β 0) 1 := by
  have h := MassGap.MomentShape.wilsonCorrAt_neg 3 (max β 0) (1 : Fin 4)
  have hneg : (-(1 : Fin 4)) = (3 : Fin 4) := by decide
  rwa [hneg] at h

#print axioms sym_four

/-- `0 < ρ(0) + 2ρ(1) + ρ(2)` for `ρ = wilsonCorrAt 3 (max β 0)`, at every real `β`. The sum over
`Fin 4` is expanded by `Fin.sum_univ_four` and folded by `sym_four`, then the second clause of
`Complete.wilson_reflection_positive_at_even 3 2` supplies the positivity.

`max β 0` is what discharges that lemma's nonnegativity hypothesis, so the statement covers negative
`β` by clamping rather than by proving anything there.

DERIVED: `0` is the strict lower bound asserted and the lower clamp on the coupling. `3` is the `N`
of `wilsonCorrAt N`; the lag literals `0`, `1`, `2` index `Fin 4`. The coefficient `2` on `ρ(1)`
counts the two lags of `Fin 4` that circle symmetry identifies with lag `1`, namely `1` and `3`, so
it is a multiplicity and not a weight. -/
theorem denom_pos_extent_four (β : ℝ) :
    0 < MassGap.wilsonCorrAt 3 (max β 0) 0 + 2 * MassGap.wilsonCorrAt 3 (max β 0) 1
      + MassGap.wilsonCorrAt 3 (max β 0) 2 := by
  have hrp := MassGap.wilson_reflection_positive_at_even 3 2 (by norm_num) (by norm_num)
    (le_max_right β (0 : ℝ))
  have hsum : (∑ d, MassGap.wilsonCorrAt 3 (max β 0) d)
      = MassGap.wilsonCorrAt 3 (max β 0) 0 + 2 * MassGap.wilsonCorrAt 3 (max β 0) 1
        + MassGap.wilsonCorrAt 3 (max β 0) 2 := by
    rw [Fin.sum_univ_four, sym_four β]; ring
  rw [← hsum]
  exact hrp.2

#print axioms denom_pos_extent_four

/-- `wilsonCorrAt 5 (max β 0) 5 = wilsonCorrAt 5 (max β 0) 1`. `MomentShape.wilsonCorrAt_neg` at the
lag `1`, rewritten through `-(1 : Fin 6) = 5`.

DERIVED: `5` is the `N` of `wilsonCorrAt N`, so the lags form `Fin 6`. The lag literals `5` and `1`
are negatives of one another in `Fin 6`; `0` is the lower clamp on the coupling. -/
theorem sym_six_one (β : ℝ) :
    MassGap.wilsonCorrAt 5 (max β 0) 5 = MassGap.wilsonCorrAt 5 (max β 0) 1 := by
  have h := MassGap.MomentShape.wilsonCorrAt_neg 5 (max β 0) (1 : Fin 6)
  have hneg : (-(1 : Fin 6)) = (5 : Fin 6) := by decide
  rwa [hneg] at h

#print axioms sym_six_one

/-- `wilsonCorrAt 5 (max β 0) 4 = wilsonCorrAt 5 (max β 0) 2`. `MomentShape.wilsonCorrAt_neg` at the
lag `2`, rewritten through `-(2 : Fin 6) = 4`.

DERIVED: `5` is the `N` of `wilsonCorrAt N`, so the lags form `Fin 6`. The lag literals `4` and `2`
are negatives of one another in `Fin 6`; `0` is the lower clamp on the coupling. -/
theorem sym_six_two (β : ℝ) :
    MassGap.wilsonCorrAt 5 (max β 0) 4 = MassGap.wilsonCorrAt 5 (max β 0) 2 := by
  have h := MassGap.MomentShape.wilsonCorrAt_neg 5 (max β 0) (2 : Fin 6)
  have hneg : (-(2 : Fin 6)) = (4 : Fin 6) := by decide
  rwa [hneg] at h

#print axioms sym_six_two

/-- `0 < ρ(0) + 2ρ(1) + 2ρ(2) + ρ(3)` for `ρ = wilsonCorrAt 5 (max β 0)`, at every real `β`. The sum
over `Fin 6` is expanded by `Fin.sum_univ_six` and folded by `sym_six_one` and `sym_six_two`, then
the second clause of `Complete.wilson_reflection_positive_at_even 5 3` supplies the positivity.

DERIVED: `0` is the strict lower bound asserted and the lower clamp on the coupling. `5` is the `N`
of `wilsonCorrAt N`; the lag literals `0`, `1`, `2`, `3` index `Fin 6`. Each coefficient `2` counts
the two lags of `Fin 6` that circle symmetry identifies — `1` with `5`, and `2` with `4` — so both
are multiplicities; lags `0` and `3` are their own negatives and carry no coefficient. -/
theorem denom_pos_extent_six (β : ℝ) :
    0 < MassGap.wilsonCorrAt 5 (max β 0) 0 + 2 * MassGap.wilsonCorrAt 5 (max β 0) 1
      + 2 * MassGap.wilsonCorrAt 5 (max β 0) 2 + MassGap.wilsonCorrAt 5 (max β 0) 3 := by
  have hrp := MassGap.wilson_reflection_positive_at_even 5 3 (by norm_num) (by norm_num)
    (le_max_right β (0 : ℝ))
  have hsum : (∑ d, MassGap.wilsonCorrAt 5 (max β 0) d)
      = MassGap.wilsonCorrAt 5 (max β 0) 0 + 2 * MassGap.wilsonCorrAt 5 (max β 0) 1
        + 2 * MassGap.wilsonCorrAt 5 (max β 0) 2 + MassGap.wilsonCorrAt 5 (max β 0) 3 := by
    rw [Fin.sum_univ_six, sym_six_one β, sym_six_two β]; ring
  rw [← hsum]
  exact hrp.2

#print axioms denom_pos_extent_six

/-! ## 1. The exact criterion at extent four -/

/-- At every real `β`, with `c = 3^{−1/4}` and `ρ = wilsonCorrAt 3 (max β 0)`:

    c < cosAvgEven ap4 β   ↔   2c·ρ(1) + (1+c)·ρ(2) < (1−c)·ρ(0).

`ConfinesZero.cosAvgEven_extent_four` puts the average in closed form as a quotient, and
`denom_pos_extent_four` clears the denominator by `lt_div_iff₀`; both directions are then `nlinarith`
rearrangements.

An equivalence, so it decides the left-hand inequality rather than implying it. Nothing about
`wilsonCorrAt`'s values is used beyond the positivity of the total mass.

DERIVED: `3`, `1` and `4` in `(3 : ℝ) ^ (-(1 : ℝ) / 4)` spell `c`, the same constant at each of its
four occurrences. `3` in `wilsonCorrAt 3` is the `N`, so the lag literals `0`, `1`, `2` index
`Fin 4`; `0` is also the lower clamp on the coupling. The coefficients `2c`, `1 + c` and `1 − c` come
from combining the lag cosines `1, 0, −1` with `c` and the multiplicities of
`denom_pos_extent_four`; none is chosen. -/
theorem confines_extent_four_iff (β : ℝ) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven ap4 β
      ↔ 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) * MassGap.wilsonCorrAt 3 (max β 0) 1
          + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * MassGap.wilsonCorrAt 3 (max β 0) 2
        < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * MassGap.wilsonCorrAt 3 (max β 0) 0 := by
  rw [cosAvgEven_extent_four β, lt_div_iff₀ (denom_pos_extent_four β)]
  constructor <;> intro h <;> nlinarith [h]

#print axioms confines_extent_four_iff

/-- The negation of `confines_extent_four_iff`, with both sides turned by `not_lt`:

    cosAvgEven ap4 β ≤ c   ↔   (1−c)·ρ(0) ≤ 2c·ρ(1) + (1+c)·ρ(2).

Logically equivalent to `confines_extent_four_iff`; stated separately so the non-strict form is
available directly.

DERIVED: every numeral is `confines_extent_four_iff`'s, carried through the two negations unchanged
— `3`, `1` and `4` spelling `c`, the `3` of `wilsonCorrAt 3`, the lag literals `0`, `1`, `2` of
`Fin 4`, the clamp `0`, and the coefficients `2c`, `1 + c`, `1 − c`. -/
theorem not_confines_extent_four_iff (β : ℝ) :
    cosAvgEven ap4 β ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4)
      ↔ (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * MassGap.wilsonCorrAt 3 (max β 0) 0
        ≤ 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) * MassGap.wilsonCorrAt 3 (max β 0) 1
          + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * MassGap.wilsonCorrAt 3 (max β 0) 2 := by
  rw [← not_lt, ← not_lt, confines_extent_four_iff β]

#print axioms not_confines_extent_four_iff

/-! ## 2. The criterion at six lags

`ConfinesZero.cosAvgEven_extent_six` gives `ρ(1)` weight `+1` in the numerator. The same lag carries
weight `2` in the denominator, so after clearing it the coefficient of `ρ(1)` in the criterion is
`2c − 1`, which `two_c_sub_one_pos` shows is positive. -/

/-- `0 < 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1`. By contradiction: if `c ≤ 1/2` then `c² ≤ 1/4` and
`c⁴ ≤ 1/16`, while `c⁴ = 1/3` by `Real.rpow_natCast` and `Real.rpow_mul`; `1/3 ≤ 1/16` is false.

So `c` exceeds `1/2`, which is what makes the coefficient of `ρ(1)` in `confines_extent_six_iff`
positive.

DERIVED: nothing is chosen. `3`, `1` and `4` spell `c`; `2` and the subtracted `1` are the
coefficient and offset of the expression whose sign is asserted, and `0` is that sign. The
inequality is `c > 1/2`, which is `3 < 16` after raising both sides to the fourth power, so the
comparison is decided by the exponent `4` already present in `c`. -/
theorem two_c_sub_one_pos : 0 < 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1 := by
  have h : (1 : ℝ) / 2 < (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
    set x : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hx
    have hpos : (0 : ℝ) < x := Real.rpow_pos_of_pos (by norm_num) _
    have hq : x ^ (4 : ℕ) = 1 / 3 := by
      rw [hx, ← Real.rpow_natCast ((3 : ℝ) ^ (-(1 : ℝ) / 4)) 4,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
      norm_num
    by_contra hcon
    rw [not_lt] at hcon
    have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith [hpos, hcon]
    have hx4 : x ^ (4 : ℕ) ≤ 1 / 16 := by nlinarith [hx2, sq_nonneg x, sq_nonneg (x ^ 2)]
    rw [hq] at hx4
    norm_num at hx4
  linarith

#print axioms two_c_sub_one_pos

/-- At every real `β`, with `c = 3^{−1/4}` and `ρ = wilsonCorrAt 5 (max β 0)`:

    c < cosAvgEven ap6 β ↔ (2c−1)·ρ(1) + (1+2c)·ρ(2) + (1+c)·ρ(3) < (1−c)·ρ(0).

`ConfinesZero.cosAvgEven_extent_six` in closed form, with the denominator cleared by
`denom_pos_extent_six`; both directions are `nlinarith` rearrangements.

All three coefficients on the left are positive — the first by `two_c_sub_one_pos` — so each
non-contact lag enters with the same sign, and the additional lag that six resolves adds a term to
that side.

DERIVED: `3`, `1` and `4` in `(3 : ℝ) ^ (-(1 : ℝ) / 4)` spell `c`, the same constant at each of its
six occurrences. `5` in `wilsonCorrAt 5` is the `N`, so the lag literals `0`, `1`, `2`, `3` index
`Fin 6`; `0` is also the lower clamp on the coupling. The coefficients `2c − 1`, `1 + 2c`, `1 + c`
and `1 − c` come from combining the lag cosines `1, ½, −½, −1` with `c` and the multiplicities of
`denom_pos_extent_six`; none is chosen. -/
theorem confines_extent_six_iff (β : ℝ) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven ap6 β
      ↔ (2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1) * MassGap.wilsonCorrAt 5 (max β 0) 1
          + (1 + 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * MassGap.wilsonCorrAt 5 (max β 0) 2
          + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * MassGap.wilsonCorrAt 5 (max β 0) 3
        < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * MassGap.wilsonCorrAt 5 (max β 0) 0 := by
  rw [cosAvgEven_extent_six β, lt_div_iff₀ (denom_pos_extent_six β)]
  constructor <;> intro h <;> nlinarith [h]

#print axioms confines_extent_six_iff

/-! ## 3. `Shape 4 2` on both sides of the criterion

`MomentShape.Shape 4 2` bundles nonnegativity, circle symmetry and log-convexity of a profile
`Fin 4 → ℝ`, and `MomentShape.shape_wilsonCorrAt` establishes it of `wilsonCorrAt 3 β` for `0 ≤ β`.

The two theorems below exhibit profiles satisfying `Shape 4 2`, with positive contact value and
positive total mass, on each side of `confines_extent_four_iff`'s inequality. So that inequality is
not a consequence of `Shape 4 2` and those two positivity conditions, and neither is its negation. -/

/-- There is a `ρ : Fin 4 → ℝ` satisfying `MomentShape.Shape 4 2 ρ`, with `0 < ρ 0` and
`0 < ∑ d, ρ d`, for which the extent-four criterion `2c·ρ(1) + (1+c)·ρ(2) < (1−c)·ρ(0)` is FALSE.

The witness is the flat profile `ρ ≡ 1`: nonnegative, circle-symmetric by `rfl`, log-convex because
`1 ≤ 1`, with total mass `4`. There the criterion reads `1 + 3c < 1 − c`, which fails because `c` is
positive (`ConfinesZero.floor_pos`).

DERIVED: `4` in `Fin 4` and the first `4` of `Shape 4 2` are the number of lags; the `2` of
`Shape 4 2` is the half-extent, the reflection plane's position. `0` is the lag index of the contact
value and the strict lower bound asserted of it and of the total mass. The coefficients `2c`,
`1 + c`, `1 − c` and the lag literals `0`, `1`, `2` are `confines_extent_four_iff`'s, as are the
`3`, `1` and `4` spelling `c`. -/
theorem shape_admits_failure :
    ∃ ρ : Fin 4 → ℝ, MassGap.MomentShape.Shape 4 2 ρ ∧ 0 < ρ 0 ∧ 0 < ∑ d, ρ d ∧
      ¬ (2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) * ρ 1 + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * ρ 2
          < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * ρ 0) := by
  refine ⟨fun _ => (1 : ℝ), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro _; exact zero_le_one
  · intro _; rfl
  · intro _ _ _ _; norm_num
  · show (0 : ℝ) < 1; exact zero_lt_one
  · rw [Fin.sum_univ_four]; norm_num
  · have hc : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := MassGap.ConfinesZero.floor_pos
    show ¬ (2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) * 1 + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * 1
        < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * 1)
    rw [not_lt]; linarith

#print axioms shape_admits_failure

/-- There is a `ρ : Fin 4 → ℝ` satisfying `MomentShape.Shape 4 2 ρ`, with `0 < ρ 0` and
`0 < ∑ d, ρ d`, for which the extent-four criterion `2c·ρ(1) + (1+c)·ρ(2) < (1−c)·ρ(0)` HOLDS.

The witness is `wilsonCorrAt 3 0`, the ensemble's own profile at zero coupling, not an invented one.
`MomentShape.shape_wilsonCorrAt` gives its `Shape 4 2`,
`PowerTail.contact_value_pos_at_zero_coupling` its positive contact value, the second clause of
`Complete.wilson_reflection_positive_at_even` its positive total mass, and
`confines_extent_four_iff` applied to `ConfinesZero.confines_at_zero` the criterion, after
`max 0 0 = 0` is rewritten away.

Its contact value is a positive real fixed by the ensemble, and the statement does not say which.

DERIVED: `4` in `Fin 4` and the first `4` of `Shape 4 2` are the number of lags; the `2` of
`Shape 4 2` is the half-extent. `0` is the lag index of the contact value, the strict lower bound
asserted of it and of the total mass, and the coupling the witness is taken at. The coefficients and
the remaining lag literals are `confines_extent_four_iff`'s, as are the `3`, `1` and `4` spelling
`c`. -/
theorem shape_admits_success :
    ∃ ρ : Fin 4 → ℝ, MassGap.MomentShape.Shape 4 2 ρ ∧ 0 < ρ 0 ∧ 0 < ∑ d, ρ d ∧
      2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) * ρ 1 + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * ρ 2
        < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * ρ 0 := by
  have hm : max (0 : ℝ) 0 = 0 := max_self 0
  refine ⟨MassGap.wilsonCorrAt 3 0,
    MassGap.MomentShape.shape_wilsonCorrAt 3 2 rfl (by norm_num) (le_refl (0 : ℝ)), ?_, ?_, ?_⟩
  · exact MassGap.PowerTail.contact_value_pos_at_zero_coupling 3
  · exact (MassGap.wilson_reflection_positive_at_even 3 2 (by norm_num) (by norm_num)
      (le_refl (0 : ℝ))).2
  · have h := (confines_extent_four_iff 0).mp (MassGap.ConfinesZero.confines_at_zero ap4)
    rwa [hm] at h

#print axioms shape_admits_success

/-! ## 4. Footprints -/

section Audit
#print axioms sym_four
#print axioms denom_pos_extent_four
#print axioms sym_six_one
#print axioms sym_six_two
#print axioms denom_pos_extent_six
#print axioms confines_extent_four_iff
#print axioms not_confines_extent_four_iff
#print axioms two_c_sub_one_pos
#print axioms confines_extent_six_iff
#print axioms shape_admits_failure
#print axioms shape_admits_success
end Audit

end MassGap.ConfinesSharp
