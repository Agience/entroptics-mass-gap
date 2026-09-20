import Mathlib
import MassGap.LagTwoBound
import MassGap.LagTwoSix
import MassGap.SlabQuadratic

/-!
# MassGap.LagTwoQuadratic — the extent-four lag-two threshold, relaxed by the quadratic arm

`LagTwoBound.lagTwoThreshold = ((1−c)/(1+c))² = 0.0186240` is obtained by substituting ONE shape fact
into `ConfinesSharp.confines_extent_four_iff`: log-convexity, `ρ(1) ≤ √(ρ(0)ρ(2))`. That is not the
strongest bound on `ρ(1)` this tree proves.

`SlabQuadratic.wilson_quadratic` gives `2ρ(1)² ≤ ρ(2)² + ρ(0)ρ(2)` at every real `β`, with no
hypothesis at all, and `SpectralFour.missing_inequalities_independent` shows it does not follow from
log-convexity and `ρ(2) ≤ ρ(1)` together. Substituting IT instead relaxes the threshold to

    lagTwoThresholdQuad = (1−c)² / (1 + 2c − c²) = 0.0296959

a factor `(1+c)²/(1+2c−c²) = 1.594495` on the bar B5 must clear at extent four. Nothing is fitted and
nothing is measured: both thresholds are closed forms in `c = 3^{−1/4}` and the relaxation is their
exact ratio.

## Why it is rational, where `lagTwoThresholdSix` needed a square root

Substituting `ρ(1) ≤ √((ρ(2)²+ρ(0)ρ(2))/2)` into the criterion and clearing the root gives, in
`t = ρ(2)/ρ(0)`,

    (1 + 2c − c²)·t² − 2·t + (1−c)²  >  0

whose discriminant is `1 − (1+2c−c²)(1−c)² = c²(2−c)²`, a PERFECT SQUARE. So the roots are rational in
`c`: the quadratic factors as `(1+2c−c²)·(t − T)·(t − 1)` with `T = (1−c)²/(1+2c−c²)`, and the second
root is exactly `1` because `(1+2c−c²) + (1−c)² = 2` is a `ring` identity. `root_sum_is_two` records
that identity, because it is what makes the factorisation exact rather than approximate.

`t = 1` is the flat profile, which is where `FreeFieldLagTwo.flat_profile_meets_every_uniform_fact`
already puts the coupling-uniform ceiling — so the two roots of this quadratic are the new threshold
and the known obstruction, and nothing between them is new information.

## What this does and does NOT do

* It **relaxes the obligation at extent four**, and narrows the gap to extent six from `1.81×`
  (`LagTwoSix.lagTwoThreshold_lt_lagTwoThresholdSix`) to `1.138×`
  (`lagTwoThresholdQuad_lt_lagTwoThresholdSix`). Extent six remains the weaker bar.
* It is **NOT proved sharp**, and is not claimed to be. `LagTwoSix.lagTwoThresholdSix_sharp` exhibits
  a profile at exactly its threshold; no such profile is exhibited here, so `lagTwoThresholdQuad` is
  a sufficient threshold and possibly not the best one. Saying otherwise would be the completeness
  claim this file exists to correct elsewhere.
* It does **not** close B5. The live route is weak coupling at extent six, which this does not touch,
  and the β axis is untouched at both extents.
* The hypothesis carried is `FourRepresentable`'s quadratic conjunct, so any consumer must have
  `SlabQuadratic.wilsonSpectral` in hand — which holds at every `β ≥ 0` for the genuine Wilson
  correlation, so the hypothesis is discharged rather than assumed.

Foundational footprint only (`#print axioms` on every declaration).
Build: `python research/code/lean_build.py build MassGap.LagTwoQuadratic`.
-/

namespace MassGap.LagTwoQuadratic

/-- **THE RELAXED EXTENT-FOUR THRESHOLD ON THE LAG-TWO RATIO**, in the same currency as
`LagTwoBound.lagTwoThreshold` — a bound on `ρ(2)/ρ(0)` rather than on its square root.

DERIVED: every literal is a coefficient of `ConfinesSharp.confines_extent_four_iff` after the
quadratic substitution, and none is chosen. `1 − c` and `1 + c` are the criterion's own; `1 + 2c − c²`
is what `(1+c)² − 2c²` collapses to when the root is cleared, the `2c²` being the quadratic's own
factor of two; the outer square is the criterion's, since it is stated on `ρ(1)²`. No numeral here is
a level and none is measured. -/
noncomputable def lagTwoThresholdQuad : ℝ :=
  (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2
    / (1 + 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2)

/-- The denominator is positive, from `floor_bounds` alone. -/
theorem den_pos :
    0 < 1 + 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 := by
  have hc := MassGap.LagTwoBound.floor_bounds
  nlinarith [hc.1, hc.2]

/-- **THE TWO ROOTS SUM TO `2 / (1+2c−c²)`, because the coefficients sum to `2`.** A `ring` identity,
and it is what makes the factorisation exact: the second root of the substituted quadratic is `1`,
the flat profile.

DERIVED: no numeral is chosen. The `2` is `(1+2c−c²) + (1−2c+c²)`, in which every `c` cancels. -/
theorem root_sum_is_two (c : ℝ) : (1 + 2 * c - c ^ 2) + (1 - c) ^ 2 = 2 := by ring

/-- **THE ROOT IDENTITY.** `(1+2c−c²)·lagTwoThresholdQuad = (1−c)²`, so the threshold is exactly the
substituted criterion's own smaller root and not a cut taken below it. -/
theorem threshold_root :
    (1 + 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2) * lagTwoThresholdQuad
      = (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 := by
  have hd : (1 + 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2) ≠ 0 := den_pos.ne'
  unfold lagTwoThresholdQuad
  rw [mul_comm, div_mul_cancel₀ _ hd]

/-- The threshold bracketed for a reader, between `0.02969` and `0.02970`. The decision is made by
the closed form; these rationals decide nothing, and each rounds AWAY from the claim it is used in —
the lower one below the true value where a lower bound is wanted, the upper one above it. -/
theorem lagTwoThresholdQuad_gt : 0.02969 < lagTwoThresholdQuad := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have hsq := MassGap.LagTwoBound.floor_sq_bounds
  have hd := den_pos
  unfold lagTwoThresholdQuad
  rw [lt_div_iff₀ hd]
  nlinarith [hc.1, hc.2, hsq.1, hsq.2]

theorem lagTwoThresholdQuad_lt : lagTwoThresholdQuad < 0.02970 := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have hsq := MassGap.LagTwoBound.floor_sq_bounds
  have hd := den_pos
  unfold lagTwoThresholdQuad
  rw [div_lt_iff₀ hd]
  nlinarith [hc.1, hc.2, hsq.1, hsq.2]

/-- **THE RELAXATION, STATED AS THE INEQUALITY IT IS.** The quadratic arm gives a strictly weaker bar
than log-convexity alone. -/
theorem lagTwoThreshold_lt_lagTwoThresholdQuad :
    MassGap.LagTwoBound.lagTwoThreshold < lagTwoThresholdQuad := by
  calc MassGap.LagTwoBound.lagTwoThreshold
      < 0.018625 := MassGap.LagTwoBound.lagTwoThreshold_lt
    _ < 0.02969 := by norm_num
    _ < lagTwoThresholdQuad := lagTwoThresholdQuad_gt

/-- **THE SUFFICIENCY.** A lag-two ratio below `lagTwoThresholdQuad` gives the exact extent-four
criterion, using the quadratic in place of log-convexity.

The proof is the factorisation and nothing else. Write `u = (1−c)ρ(0) − (1+c)ρ(2)`. The quadratic
gives `(2c·ρ(1))² = 4c²ρ(1)² ≤ 2c²(ρ(2)² + ρ(0)ρ(2))`, and

    u² − 2c²(ρ(2)² + ρ(0)ρ(2)) = ((1−c)²ρ(0) − (1+2c−c²)ρ(2))·(ρ(0) − ρ(2))

is a `ring` identity given `(1+2c−c²) + (1−c)² = 2`. Both factors are positive below the threshold, so
`u > 0` and `(2c·ρ(1))² < u²`, and a nonnegative number whose square is below a positive number's
square is below it. -/
theorem confines_extent_four_of_lag_two_ratio_quad
    {r₀ r₁ r₂ : ℝ} (h₀ : 0 < r₀) (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂)
    (hq : 2 * r₁ ^ 2 ≤ r₂ ^ 2 + r₀ * r₂)
    (hlt : r₂ < lagTwoThresholdQuad * r₀) :
    2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) * r₁ + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₂
      < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀ := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have hsqb := MassGap.LagTwoBound.floor_sq_bounds
  have hd := den_pos
  have hr := threshold_root
  set c : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hcdef
  -- clear the threshold out of the hypothesis, leaving a polynomial statement in `c`
  have hlt' : (1 + 2 * c - c ^ 2) * r₂ < (1 - c) ^ 2 * r₀ := by
    have := mul_lt_mul_of_pos_left hlt hd
    nlinarith [this, hr]
  -- The second root is `1`, so the ratio is below one and `ρ(2) < ρ(0)`. Dividing `hlt'` through by
  -- the leading coefficient is a NONLINEAR step, so the two products are supplied rather than
  -- searched for: `1.9 < 1+2c−c²` and `(1−c)² < 0.06` bracket the two coefficients apart, and the
  -- rest is linear in `r₀` and `r₂`.
  have ha : (1.9 : ℝ) < 1 + 2 * c - c ^ 2 := by nlinarith [hc.1, hc.2, hsqb.1, hsqb.2]
  have hk : (1 - c) ^ 2 < 0.06 := by nlinarith [hc.1, hc.2]
  have hstep : 1.9 * r₂ ≤ (1 + 2 * c - c ^ 2) * r₂ := mul_le_mul_of_nonneg_right ha.le h₂
  have hstep2 : (1 - c) ^ 2 * r₀ < 0.06 * r₀ := mul_lt_mul_of_pos_right hk h₀
  have hr20 : r₂ < r₀ := by linarith [hlt', hstep, hstep2, h₀]
  -- `u > 0`, which needs `(1−c)(1+c) < 1+2c−c²`, i.e. `0 < 2c`
  have hu : 0 < (1 - c) * r₀ - (1 + c) * r₂ := by nlinarith [hlt', hc.1, hc.2, h₀, h₂]
  -- the factorisation, both factors positive
  have hfac : 0 < ((1 - c) ^ 2 * r₀ - (1 + 2 * c - c ^ 2) * r₂) * (r₀ - r₂) :=
    mul_pos (sub_pos.mpr hlt') (sub_pos.mpr hr20)
  -- square comparison, then descend
  have hsq : (2 * c * r₁) ^ 2 < ((1 - c) * r₀ - (1 + c) * r₂) ^ 2 := by
    nlinarith [hq, hfac, hc.1, hc.2, sq_nonneg r₁, h₂, h₀]
  nlinarith [hsq, hu, h₁, hc.1, hc.2]

/-- **EXTENT SIX IS STILL THE WEAKER BAR, and by how much.** The relaxation narrows the gap from
`1.81×` to `1.138×` but does not close it, so the preference for extent six recorded in
`LagTwoSix` survives.

DERIVED: no numeral. Both sides are closed forms and the comparison is between them. -/
theorem lagTwoThresholdQuad_lt_lagTwoThresholdSix :
    lagTwoThresholdQuad < MassGap.LagTwoSix.lagTwoThresholdSix := by
  calc lagTwoThresholdQuad
      < 0.02970 := lagTwoThresholdQuad_lt
    _ < 0.0337 := by norm_num
    _ < MassGap.LagTwoSix.lagTwoThresholdSix := MassGap.LagTwoSix.lagTwoThresholdSix_gt

#print axioms lagTwoThresholdQuad
#print axioms den_pos
#print axioms root_sum_is_two
#print axioms threshold_root
#print axioms lagTwoThresholdQuad_gt
#print axioms lagTwoThresholdQuad_lt
#print axioms lagTwoThreshold_lt_lagTwoThresholdQuad
#print axioms confines_extent_four_of_lag_two_ratio_quad
#print axioms lagTwoThresholdQuad_lt_lagTwoThresholdSix

end MassGap.LagTwoQuadratic
