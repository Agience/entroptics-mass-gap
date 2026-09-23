import Mathlib
import MassGap.LagTwoBound
import MassGap.LagTwoSix
import MassGap.SlabQuadratic

/-!
# MassGap.LagTwoQuadratic — an extent-four lag-two threshold from the quadratic inequality

Throughout, `c` abbreviates the real number `(3 : ℝ) ^ (-(1 : ℝ) / 4)`, which is
`exp (-(1/4) * log 3)`, the exponential of the negated constant `Floor.floor_pos` bounds.

`ConfinesSharp.confines_extent_four_iff` states the extent-four criterion as
`2c·ρ(1) + (1+c)·ρ(2) < (1−c)·ρ(0)`. Bounding `ρ(1)` above turns that into a condition on
`ρ(2)/ρ(0)` alone. This module performs the substitution with the quadratic bound
`2ρ(1)² ≤ ρ(2)² + ρ(0)ρ(2)`, which `confines_extent_four_of_lag_two_ratio_quad` takes as its
hypothesis `hq`, and defines the resulting threshold

    lagTwoThresholdQuad = (1 − c)² / (1 + 2c − c²)

`lagTwoThresholdQuad_gt` and `lagTwoThresholdQuad_lt` bracket it strictly between `0.02969` and
`0.02970`. `lagTwoThreshold_lt_lagTwoThresholdQuad` proves it strictly exceeds
`LagTwoBound.lagTwoThreshold`, and `lagTwoThresholdQuad_lt_lagTwoThresholdSix` proves it is strictly
below `LagTwoSix.lagTwoThresholdSix`.

## Why the threshold is rational in `c`

Substituting `ρ(1) ≤ √((ρ(2)² + ρ(0)ρ(2))/2)` into the criterion and clearing the root gives, in
`t = ρ(2)/ρ(0)`,

    (1 + 2c − c²)·t² − 2·t + (1 − c)²  >  0

whose discriminant is `1 − (1+2c−c²)(1−c)² = c²(2−c)²`, a square. The quadratic therefore factors as
`(1+2c−c²)·(t − T)·(t − 1)` with `T = (1−c)²/(1+2c−c²)`, and the second root is exactly `1` because
the two coefficients sum to `2`. `root_sum_is_two` is that `ring` identity, and `threshold_root`
records that `lagTwoThresholdQuad` is exactly the smaller root rather than a value taken below it.

## Scope

`confines_extent_four_of_lag_two_ratio_quad` concludes the extent-four inequality for three reals
`r₀`, `r₁`, `r₂` under `0 < r₀`, `0 ≤ r₁`, `0 ≤ r₂`, the quadratic hypothesis `hq`, and
`r₂ < lagTwoThresholdQuad * r₀`. The three reals are arbitrary; nothing in the statement ties them to
a correlation function, a coupling or an extent, and `hq` is a hypothesis the caller supplies.

The threshold is proved sufficient. No profile attaining it is exhibited here, so the statements
below do not determine whether a smaller threshold would also do.

Build: `python research/code/lean_build.py build MassGap.LagTwoQuadratic`.
-/

namespace MassGap.LagTwoQuadratic

/-- The real number `(1 − c)² / (1 + 2c − c²)` at `c = (3 : ℝ) ^ (-(1 : ℝ) / 4)`, written out in
full. A bound on the ratio `ρ(2)/ρ(0)`, in the same currency as `LagTwoBound.lagTwoThreshold` rather
than on its square root.

A closed form: it is `noncomputable` because of the real power, and its value is fixed by the
definition with no parameter and no input.

DERIVED: every literal is a coefficient of `ConfinesSharp.confines_extent_four_iff` after the
quadratic substitution, and none is chosen. `3` is the base of the constant `c` and `-(1)/4` its
exponent, so the `1` and `4` of each of the three occurrences of `c` are that one exponent repeated;
`3` and `4` are the base and the reciprocal weight of the floor constant `(1/4) log 3` that `c`
exponentiates. `1 − c` is the criterion's right-hand coefficient and `1 + c` its coefficient on
`ρ(2)`; `1 + 2c − c²` is what `(1+c)² − 2c²` collapses to when the root is cleared, the `2c²` being
the quadratic hypothesis's own factor of two. The two exponents `2` are squares — the outer one is
the criterion's, since the substitution is made on `ρ(1)²`, and the inner one is the square of `c` in
the denominator. No numeral here is a measured level. -/
noncomputable def lagTwoThresholdQuad : ℝ :=
  (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2
    / (1 + 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2)

/-- `0 < 1 + 2c − c²` at `c = (3 : ℝ) ^ (-(1 : ℝ) / 4)`. `nlinarith` from the two-sided numeric
bracket `LagTwoBound.floor_bounds` on `c`, and nothing else.

This is the denominator of `lagTwoThresholdQuad`, so its non-vanishing is what makes that definition
well behaved and `threshold_root` available.

DERIVED: `0` is the sign asserted. `1` and `2` are the constant term and the coefficient of `c` in
the denominator, and the remaining `2` is the exponent squaring `c`; all three are
`lagTwoThresholdQuad`'s, carried unchanged. `3` and the exponent `-(1)/4` spell the constant `c`. -/
theorem den_pos :
    0 < 1 + 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 := by
  have hc := MassGap.LagTwoBound.floor_bounds
  nlinarith [hc.1, hc.2]

/-- For every real `c`, `(1 + 2c − c²) + (1 − c)² = 2`. A `ring` identity: expanding `(1 − c)²` gives
`1 − 2c + c²`, and both the linear and the quadratic terms cancel.

Stated for an arbitrary real `c`, not only for `3 ^ (-(1)/4)`. It is what makes the factorisation of
the substituted quadratic exact: the leading coefficient and the constant term sum to `2`, so `t = 1`
is a root, and the other root is their ratio.

DERIVED: `1` is the constant term of each of the two coefficients — the `1` of `1 + 2c − c²` and the
`1` of `(1 − c)` — and `2` is the coefficient of `c` in the first. The two exponents `2` are squares.
The `2` on the right is the sum of the two constant terms, so it is forced by the other literals and
is not a chosen value; every `c` cancels. -/
theorem root_sum_is_two (c : ℝ) : (1 + 2 * c - c ^ 2) + (1 - c) ^ 2 = 2 := by ring

/-- `(1 + 2c − c²) · lagTwoThresholdQuad = (1 − c)²` at `c = (3 : ℝ) ^ (-(1 : ℝ) / 4)`: the division
in the definition is cancelled using `den_pos.ne'`.

So `lagTwoThresholdQuad` is exactly the smaller root of the substituted quadratic, not a value chosen
below it. This equation is what the sufficiency proof uses to clear the threshold out of its
hypothesis and leave a polynomial statement in `c`.

DERIVED: `1` and `2` are the constant term and the coefficient of `c` in the denominator, and the two
exponents `2` are squares — one squaring `c` in the denominator, one squaring `1 − c` on the right.
All are `lagTwoThresholdQuad`'s, carried unchanged. `3` and the exponent `-(1)/4` spell `c`. -/
theorem threshold_root :
    (1 + 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2) * lagTwoThresholdQuad
      = (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 := by
  have hd : (1 + 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2) ≠ 0 := den_pos.ne'
  unfold lagTwoThresholdQuad
  rw [mul_comm, div_mul_cancel₀ _ hd]

/-- `0.02969 < lagTwoThresholdQuad`. Clears the division with `den_pos` and closes the polynomial
inequality by `nlinarith` from `LagTwoBound.floor_bounds` and `LagTwoBound.floor_sq_bounds`, the
numeric brackets on `c` and `c²`.

The lower half of a bracket for a reader. Every decision downstream is made from the closed form or
from this inequality, so the decimal is a stated bound and not a value the threshold is replaced by.

DERIVED: `0.02969` is a rational lower bound on the closed form, rounded down so that it lies below
the true value, which is the direction a lower bound requires. The remaining literals are
`lagTwoThresholdQuad`'s, unfolded by the proof. -/
theorem lagTwoThresholdQuad_gt : 0.02969 < lagTwoThresholdQuad := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have hsq := MassGap.LagTwoBound.floor_sq_bounds
  have hd := den_pos
  unfold lagTwoThresholdQuad
  rw [lt_div_iff₀ hd]
  nlinarith [hc.1, hc.2, hsq.1, hsq.2]

/-- `lagTwoThresholdQuad < 0.02970`, the upper half of the bracket. Same proof shape as
`lagTwoThresholdQuad_gt`, with the division cleared the other way.

DERIVED: `0.02970` is a rational upper bound on the closed form, rounded up so that it lies above the
true value, which is the direction an upper bound requires. The remaining literals are
`lagTwoThresholdQuad`'s, unfolded by the proof. -/
theorem lagTwoThresholdQuad_lt : lagTwoThresholdQuad < 0.02970 := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have hsq := MassGap.LagTwoBound.floor_sq_bounds
  have hd := den_pos
  unfold lagTwoThresholdQuad
  rw [div_lt_iff₀ hd]
  nlinarith [hc.1, hc.2, hsq.1, hsq.2]

/-- `LagTwoBound.lagTwoThreshold < lagTwoThresholdQuad`. A three-step `calc` through the decimal
brackets: `LagTwoBound.lagTwoThreshold_lt`, then `norm_num` on the two rationals, then
`lagTwoThresholdQuad_gt`.

Both sides are closed forms in `c`, and the comparison is between them; nothing is measured.

DERIVED: no numeral in the statement. The intermediate decimals `0.018625`, `0.02969` belong to the
bracketing theorems the `calc` cites, each of which carries its own note. -/
theorem lagTwoThreshold_lt_lagTwoThresholdQuad :
    MassGap.LagTwoBound.lagTwoThreshold < lagTwoThresholdQuad := by
  calc MassGap.LagTwoBound.lagTwoThreshold
      < 0.018625 := MassGap.LagTwoBound.lagTwoThreshold_lt
    _ < 0.02969 := by norm_num
    _ < lagTwoThresholdQuad := lagTwoThresholdQuad_gt

/-- For reals `r₀ > 0`, `r₁ ≥ 0`, `r₂ ≥ 0` satisfying the quadratic inequality
`2r₁² ≤ r₂² + r₀r₂` and `r₂ < lagTwoThresholdQuad * r₀`, the extent-four criterion holds:
`2c·r₁ + (1 + c)·r₂ < (1 − c)·r₀` at `c = (3 : ℝ) ^ (-(1 : ℝ) / 4)`.

The proof is the factorisation. `threshold_root` turns `hlt` into `(1 + 2c − c²)r₂ < (1 − c)²r₀`;
with `u = (1 − c)r₀ − (1 + c)r₂`, the quadratic hypothesis gives `(2c·r₁)² ≤ 2c²(r₂² + r₀r₂)`, and

    u² − 2c²(r₂² + r₀r₂) = ((1 − c)²r₀ − (1 + 2c − c²)r₂)·(r₀ − r₂)

is a `ring` identity given `root_sum_is_two`. Both factors are positive below the threshold, so
`u > 0` and `(2c·r₁)² < u²`, and a nonnegative number whose square is below a positive number's
square is itself below it. The two products `1.9 < 1 + 2c − c²` and `(1 − c)² < 0.06` are supplied to
`nlinarith` to separate the coefficients; they are bounds inside the proof and do not appear in the
statement.

Sufficiency only: the hypotheses imply the criterion. Nothing here says the criterion fails above the
threshold. `r₀`, `r₁`, `r₂` are arbitrary reals and the quadratic inequality is a hypothesis.

DERIVED: `0` is the strict lower bound on `r₀` and the lower bound on each of `r₁` and `r₂`. In `hq`,
`2` is the factor the quadratic inequality carries on `r₁²`, and the two exponents `2` are squares.
In the conclusion, `2` is the criterion's coefficient on `r₁` — it multiplies `c`, matching
`ConfinesSharp.confines_extent_four_iff` — and `1` is the constant term of the criterion's two
coefficients `1 + c` and `1 − c`. `3` and the exponent `-(1)/4`, appearing three times, spell the one
constant `c`. -/
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
  -- the leading coefficient is a nonlinear step, so the two products are supplied rather than
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

/-- `lagTwoThresholdQuad < LagTwoSix.lagTwoThresholdSix`. A `calc` through the decimal brackets:
`lagTwoThresholdQuad_lt`, `norm_num`, then `LagTwoSix.lagTwoThresholdSix_gt`.

So the extent-six threshold is the larger of the two numbers, strictly.

DERIVED: no numeral in the statement. Both sides are closed forms and the comparison is between them;
the intermediate decimals `0.02970`, `0.0337` belong to the bracketing theorems the `calc` cites. -/
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
