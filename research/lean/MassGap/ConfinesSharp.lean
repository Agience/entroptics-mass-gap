import MassGap.ConfinesZero

/-!
# MassGap.ConfinesSharp — the EXACT criterion at the two smallest even apertures

`ConfinesZero.confines_extent_four_of_lag_two_small` is a SUFFICIENT condition: it spends
log-convexity to remove `ρ(1)` from the criterion, and what it leaves is a bound on `ρ(2)` alone.
That step is not reversible, so the lemma cannot be used to decide the hypothesis — a profile failing
its hypothesis may still clear the floor.

This file states the criterion with nothing spent. Clearing the floor at extent four is EQUIVALENT to
one linear inequality in the three numbers `ρ(0), ρ(1), ρ(2)`, and at extent six to one linear
inequality in four. Both directions, so the statements decide the hypothesis at those apertures
rather than merely implying it, and `not_confines_extent_four_iff` is exactly what a refutation would
have to exhibit.

## What is proved

* `denom_pos_extent_four`, `denom_pos_extent_six` — the read's total mass in closed form is strictly
  positive, from the second clause of `Complete.wilson_reflection_positive_at_even` together with the
  circle symmetry `MomentShape.wilsonCorrAt_neg`. This is what licenses clearing the denominator, and
  it is the only input beyond arithmetic.
* `confines_extent_four_iff` — with `c = 3^{−1/4}` and `ρ = wilsonCorrAt 3 (max β 0)`,

      c < cosAvgEven ap4 β   ↔   2c·ρ(1) + (1+c)·ρ(2) < (1−c)·ρ(0).

* `confines_extent_six_iff` — with `ρ = wilsonCorrAt 5 (max β 0)`,

      c < cosAvgEven ap6 β   ↔   (2c−1)·ρ(1) + (1+2c)·ρ(2) + (1+c)·ρ(3) < (1−c)·ρ(0).

  Note the sign: at extent six the first lag enters with `2c − 1`, which is POSITIVE
  (`two_c_sub_one_pos`), so `ρ(1)` still works against the hypothesis there — it is not the free
  helper the `+1` weight in `ConfinesZero.cosAvgEven_extent_six`'s numerator might suggest, because
  that weight is spent again in the denominator.
* `not_confines_extent_four_iff` — the contrapositive, as the refuter's target.
* `shape_admits_failure`, `shape_admits_success` — **the proved shape facts do not decide it.**
  `MomentShape.Shape 4 2` is exactly what `MomentShape.shape_wilsonCorrAt` establishes about the
  profile at this extent, and profiles satisfying it sit on BOTH sides of the criterion: the flat
  one fails it, the ensemble's own zero-coupling profile meets it. So no sharpening of the shape
  facts alone can close the hypothesis; what is open is about the VALUES.

## What this does NOT do

It proves nothing about the Wilson ensemble. `ρ` is unbounded here beyond nonnegativity and the total
mass; the criterion is a restatement, and the open content is entirely in the values.

DERIVED: no numeral in this file is a magnitude. `c = 3^{−1/4} = e^{−κ₀YM}` with `κ₀YM = ¼ log 3` is
counted off directed cube paths in `Floor.lean` and carried in from
`ApertureRoute.ConfinesAtAnAperture`; `3` and `5` are the extents of `ConfinesZero.ap4` and
`ConfinesZero.ap6`, read off `Complete.wilson_reflection_positive_at_even`'s hypotheses; the
coefficients `1 ± c`, `2c` and `2c − 1` are the lag cosines `1, 0, −1` and `1, ½, −½, −1` combined
with `c` by `field_simp`, not chosen.
-/

namespace MassGap.ConfinesSharp

open MassGap MassGap.EvenAperture MassGap.ApertureRoute MassGap.ConfinesZero

/-! ## 0. The two closed-form denominators are strictly positive -/

/-- Circle symmetry at extent four: lag `3` is lag `1`. `MomentShape.wilsonCorrAt_neg` at `-1 = 3`. -/
theorem sym_four (β : ℝ) :
    MassGap.wilsonCorrAt 3 (max β 0) 3 = MassGap.wilsonCorrAt 3 (max β 0) 1 := by
  have h := MassGap.MomentShape.wilsonCorrAt_neg 3 (max β 0) (1 : Fin 4)
  have hneg : (-(1 : Fin 4)) = (3 : Fin 4) := by decide
  rwa [hneg] at h

#print axioms sym_four

/-- **THE READ'S TOTAL MASS AT EXTENT FOUR IS STRICTLY POSITIVE**, in the closed form
`ρ(0) + 2ρ(1) + ρ(2)`. The second clause of the PROVED reflection positivity, with lag `3` folded
onto lag `1`. -/
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

/-- Circle symmetry at extent six: lag `5` is lag `1`. -/
theorem sym_six_one (β : ℝ) :
    MassGap.wilsonCorrAt 5 (max β 0) 5 = MassGap.wilsonCorrAt 5 (max β 0) 1 := by
  have h := MassGap.MomentShape.wilsonCorrAt_neg 5 (max β 0) (1 : Fin 6)
  have hneg : (-(1 : Fin 6)) = (5 : Fin 6) := by decide
  rwa [hneg] at h

#print axioms sym_six_one

/-- Circle symmetry at extent six: lag `4` is lag `2`. -/
theorem sym_six_two (β : ℝ) :
    MassGap.wilsonCorrAt 5 (max β 0) 4 = MassGap.wilsonCorrAt 5 (max β 0) 2 := by
  have h := MassGap.MomentShape.wilsonCorrAt_neg 5 (max β 0) (2 : Fin 6)
  have hneg : (-(2 : Fin 6)) = (4 : Fin 6) := by decide
  rwa [hneg] at h

#print axioms sym_six_two

/-- **THE READ'S TOTAL MASS AT EXTENT SIX IS STRICTLY POSITIVE**, in the closed form
`ρ(0) + 2ρ(1) + 2ρ(2) + ρ(3)`. -/
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

/-- **THE HYPOTHESIS AT EXTENT FOUR, EXACTLY.** Clearing the entropy floor is EQUIVALENT to one
linear inequality in `ρ(0), ρ(1), ρ(2)`:

    c < cosAvgEven ap4 β   ↔   2c·ρ(1) + (1+c)·ρ(2) < (1−c)·ρ(0),     c = 3^{−1/4}.

Nothing is spent: `ConfinesZero.cosAvgEven_extent_four` puts the average in closed form and the
denominator is strictly positive, so the inequality clears exactly.

**THIS IS STRICTLY SHARPER THAN `confines_extent_four_of_lag_two_small`**, which drops `ρ(1)` by
spending log-convexity `ρ(1)² ≤ ρ(0)ρ(2)` and lands on `(1+c)²ρ(2) < (1−c)²ρ(0)`. That step is one
directional, so that lemma cannot decide the hypothesis; this can. -/
theorem confines_extent_four_iff (β : ℝ) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven ap4 β
      ↔ 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) * MassGap.wilsonCorrAt 3 (max β 0) 1
          + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * MassGap.wilsonCorrAt 3 (max β 0) 2
        < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * MassGap.wilsonCorrAt 3 (max β 0) 0 := by
  rw [cosAvgEven_extent_four β, lt_div_iff₀ (denom_pos_extent_four β)]
  constructor <;> intro h <;> nlinarith [h]

#print axioms confines_extent_four_iff

/-- **WHAT A REFUTATION AT EXTENT FOUR HAS TO EXHIBIT.** The contrapositive of
`confines_extent_four_iff`: the cosine average fails the floor at a coupling exactly when the two
non-contact lags carry that much of the mass. Stated separately because it is the target, not a
by-product — a numerical claim that the hypothesis fails at extent four is precisely a claim that
this inequality holds at some `β`. -/
theorem not_confines_extent_four_iff (β : ℝ) :
    cosAvgEven ap4 β ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4)
      ↔ (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * MassGap.wilsonCorrAt 3 (max β 0) 0
        ≤ 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) * MassGap.wilsonCorrAt 3 (max β 0) 1
          + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * MassGap.wilsonCorrAt 3 (max β 0) 2 := by
  rw [← not_lt, ← not_lt, confines_extent_four_iff β]

#print axioms not_confines_extent_four_iff

/-! ## 2. The exact criterion at extent six

`ConfinesZero.cosAvgEven_extent_six` gives `ρ(1)` weight `+1` in the numerator, which invites the
reading that a larger aperture lets the first lag HELP. It does not: the same lag carries weight `2`
in the denominator, and after clearing it the coefficient of `ρ(1)` in the criterion is `2c − 1`,
which is positive. -/

/-- `2c − 1 > 0` at `c = 3^{−1/4}`: the first lag works AGAINST the hypothesis at extent six too.

DERIVED: nothing is chosen — this is `3^{−1/4} > ½`, i.e. `3 < 16`, after raising both sides to the
fourth power. -/
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

/-- **THE HYPOTHESIS AT EXTENT SIX, EXACTLY.** With `c = 3^{−1/4}` and `ρ = wilsonCorrAt 5 (max β 0)`,

    c < cosAvgEven ap6 β ↔ (2c−1)·ρ(1) + (1+2c)·ρ(2) + (1+c)·ρ(3) < (1−c)·ρ(0).

Every coefficient on the left is positive (`two_c_sub_one_pos` for the first), so at extent six as at
extent four the hypothesis is that the contact value outweighs every other lag — the extra lag the
larger aperture resolves adds a term rather than relieving one. -/
theorem confines_extent_six_iff (β : ℝ) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven ap6 β
      ↔ (2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1) * MassGap.wilsonCorrAt 5 (max β 0) 1
          + (1 + 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * MassGap.wilsonCorrAt 5 (max β 0) 2
          + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * MassGap.wilsonCorrAt 5 (max β 0) 3
        < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * MassGap.wilsonCorrAt 5 (max β 0) 0 := by
  rw [cosAvgEven_extent_six β, lt_div_iff₀ (denom_pos_extent_six β)]
  constructor <;> intro h <;> nlinarith [h]

#print axioms confines_extent_six_iff

/-! ## 3. THE PROVED SHAPE FACTS DO NOT DECIDE IT

`MomentShape.shape_wilsonCorrAt` is the whole of what the tree proves about the profile at extent
four for `0 ≤ β`: `MomentShape.Shape 4 2 (wilsonCorrAt 3 β)`, which bundles nonnegativity, circle
symmetry and log-convexity. Nothing else about the SHAPE is available at this extent — in
particular `WeakArm.wilsonCorrAt_le_at_zero` (`ρ(d) ≤ ρ(0)`) and
`MomentShape.corrClay_even_antitone` both carry `3 ≤ m`, which is extent six and above.

Other facts about the profile DO exist and are not shape facts: `Hankel.corrClay_hankel_psd_at_extent_four`
(which reduces to nonnegativity plus log-convexity, so it adds nothing here),
`StrongCoupling.wilsonCorrConn_abs_le_coreConst` (an absolute bound, but only where
`coreRate < 1`, which is the neighbourhood of zero coupling `ConfinesZero` already owns), and
`ConfinesZero.cosAvgEven_at_zero` with `continuous_cosAvgEven`. None of them decides the
criterion away from zero coupling.

The two theorems below exhibit profiles satisfying `Shape 4 2` on BOTH sides of
`confines_extent_four_iff`'s criterion. So the criterion is independent of everything the tree
proves about the shape, and what is open is genuinely about the VALUES the Wilson ensemble takes —
no sharpening of the shape facts alone can close it. -/

/-- **A `Shape`-admissible profile that FAILS the criterion**: the flat one. Nonnegative,
circle-symmetric and log-convex (`1 ≤ 1`), with strictly positive total mass — and
`2c·1 + (1+c)·1 = 1 + 3c` is nowhere below `1 − c`, since `c > 0`.

This is `Substrate.flatRead`'s profile, and it is the shape a correlation with NO decay has. -/
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

/-- **A `Shape`-admissible profile that MEETS the criterion**: the ensemble's OWN profile at zero
coupling. Together with `shape_admits_failure` this is the negative control — the proved shape facts
at extent four are consistent with both outcomes, so they cannot decide `ConfinesAtAnAperture`.

The witness is not invented. `MomentShape.shape_wilsonCorrAt` gives `Shape 4 2 (wilsonCorrAt 3 0)`,
`PowerTail.contact_value_pos_at_zero_coupling` gives the contact value, and the criterion is
`confines_extent_four_iff` applied to `ConfinesZero.confines_at_zero` — the raw profile is
concentrated at lag zero, vanishing at every other lag (`PowerTail.wilsonCorrAt_at_zero_coupling`),
which is why it clears. Its contact value is some positive number, not `1`. -/
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
