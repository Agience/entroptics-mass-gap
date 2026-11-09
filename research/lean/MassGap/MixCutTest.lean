import Mathlib
import MassGap.MixCut

/-!
# MassGap.MixCutTest — the slope of the mixed cut energy is a variance difference

`MixCut.MixCutBound N β` asks for a window-uniform upper bound on `mixCut N β t w = ⟨S_mix⟩_{2n} − 16 ⟨S_mix⟩_n`
(`n = 2^w`) over the segment `t ∈ [0, β]`. This module differentiates `mixCut` once more in the mixed coupling
and reduces `MixCutBound` to a window-uniform one-sided bound on the resulting variance difference, from the
decoupled end `MixCut.mixCut_zero`. Declarations are in `MassGap.MixCutTest`.

## 1. The second derivative (proved)

* `hasDerivAt_integral_mul_exp_lin`: `∂_x ∫ C e^{−(A + x B)} = −∫ C B e^{−(A + x B)}`, for continuous `A`, `B`,
  `C` on a compact space and a finite measure (the prefactor version of `MixCut.hasDerivAt_integral_exp_lin`).
* `mixSq N β β_⊥ n = ∫ S_mix² e^{−(β S_in + β_⊥ S_mix)}`, `varMix = mixSq / ZA − meanMix²`, the Gibbs variance
  `Var_n(S_mix)` of the mixed action at side `n`.
* `hasDerivAt_mixNum`: `∂_{β_⊥} mixNum = −mixSq`. `hasDerivAt_meanMix`: `∂_{β_⊥} ⟨S_mix⟩_n = −Var_n(S_mix)`.
* `hasDerivAt_mixCut`: `∂_{β_⊥} mixCut N β β_⊥ w = 16 Var_n(S_mix) − Var_{2n}(S_mix)`. The sign is fixed by
  `∂ ⟨S⟩ = −Var`: the slope is the small box's variance, copied `16` times, minus the large box's variance, so
  `∂²_{β_⊥} D = 16 Var_n − Var_{2n}`.

## 2. The reduction (proved, named input)

`VarGap N β`: some `K` with `16 Var_n(S_mix) − Var_{2n}(S_mix) ≤ K` at every window `w ≥ 1` and every
`t ∈ [0, β]`. `mixCutBound_of_varGap`: `VarGap N β ⇒ MixCut.MixCutBound N β`, with `M = |β| max K 0`, by the mean
value theorem from `mixCut_zero` at `t = 0`. `strongEnd_of_varGap`: frequently in `β`, the cited
`LayerSplit.TwoDCharacter N β` with `VarGap N β` gives `CouplingTower.StrongEnd N`.

DERIVED (module-wide): `16 = 2⁴` the copies; `2` the doubling and the square of the variance; `1` the least
window, the next window and the unit ball of the differentiation; `0` the decoupled end, the lower ends and the
floor of `max K 0`. Cited: `LayerSplit.TwoDCharacter N β`.

## What does not follow

`VarGap N β` is not proved at any `β > 0`, and it is a stronger input than `MixCutBound N β` (one direction
only). It is a specific-heat statement: with `c(L) = Var_L(S_mix)/L⁴`, it reads `c(n) − c(2n) ≤ K / (16 n⁴)`, a
mixed specific-heat density that does not fall between sides `n` and `2n` by more than an inverse volume. At
`t = 0` the layer gauge rotation of `MixCut` gives `Var_n(S_mix) = 16 n⁴ Var_Haar(φ)` on extent `n ≥ 3`, so the
variance difference is zero at windows `w ≥ 2` (`MixEqui.varMix_zero`, `MixEqui.varGap_zero`); the window `w = 1`
is not computed. Nothing here bounds the variances at any `t > 0`.
No hypothesis of the bridge is discharged; `LayerSplit.TwoDCharacter N β` stays a cited input.
-/

namespace MassGap.MixCutTest

open MeasureTheory Filter Topology Set MassGap MassGap.MixCut
open MassGap.CouplingTower (StrongEnd)

variable {N : ℕ}

/-! ## 1. Differentiation under the integral with a prefactor -/

/-- **`x ↦ ∫ C e^{−(A + x B)}` is differentiable** with derivative `−∫ C B e^{−(A + t B)}`, for continuous
`A`, `B`, `C` on a compact space and a finite measure. DERIVED: `1` the radius of the dominating ball; `0` the
floor of the bounds. -/
theorem hasDerivAt_integral_mul_exp_lin {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] {A B C : X → ℝ}
    (hA : Continuous A) (hB : Continuous B) (hC : Continuous C) (t : ℝ) :
    HasDerivAt (fun x => ∫ U, C U * Real.exp (-(A U + x * B U)) ∂μ)
      (-∫ U, C U * B U * Real.exp (-(A U + t * B U)) ∂μ) t := by
  obtain ⟨CA, hCA⟩ := isCompact_univ.exists_bound_of_continuousOn hA.continuousOn
  obtain ⟨CB, hCB⟩ := isCompact_univ.exists_bound_of_continuousOn hB.continuousOn
  obtain ⟨CC, hCC⟩ := isCompact_univ.exists_bound_of_continuousOn hC.continuousOn
  have hA' : ∀ U, |A U| ≤ CA := fun U => by simpa [Real.norm_eq_abs] using hCA U (mem_univ U)
  have hB' : ∀ U, |B U| ≤ max CB 0 := fun U =>
    (by simpa [Real.norm_eq_abs] using hCB U (mem_univ U) : |B U| ≤ CB).trans (le_max_left _ _)
  have hC' : ∀ U, |C U| ≤ max CC 0 := fun U =>
    (by simpa [Real.norm_eq_abs] using hCC U (mem_univ U) : |C U| ≤ CC).trans (le_max_left _ _)
  have hB0 : 0 ≤ max CB 0 := le_max_right _ _
  have hC0 : 0 ≤ max CC 0 := le_max_right _ _
  have hE : ∀ x : ℝ, Continuous fun U => Real.exp (-(A U + x * B U)) := fun x =>
    Real.continuous_exp.comp (hA.add (continuous_const.mul hB)).neg
  have hF : ∀ x : ℝ, Continuous fun U => C U * Real.exp (-(A U + x * B U)) := fun x => hC.mul (hE x)
  have hexp : ∀ (x : ℝ) (U : X), Real.exp (-(A U + x * B U)) ≤ Real.exp (CA + |x| * max CB 0) := by
    intro x U
    refine Real.exp_le_exp.mpr ?_
    have h1 : |x * B U| ≤ |x| * max CB 0 := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB' U) (abs_nonneg x)
    linarith [neg_abs_le (A U), neg_abs_le (x * B U), hA' U]
  have hint : Integrable (fun U => C U * Real.exp (-(A U + t * B U))) μ :=
    (hF t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbd : ∀ᵐ U ∂μ, ∀ x ∈ Metric.ball t 1,
      ‖C U * (-B U * Real.exp (-(A U + x * B U)))‖
        ≤ max CC 0 * (max CB 0 * Real.exp (CA + (|t| + 1) * max CB 0)) := by
    refine Eventually.of_forall fun U x hx => ?_
    rw [Metric.mem_ball, Real.dist_eq] at hx
    have hx' : |x| ≤ |t| + 1 := by linarith [abs_sub_abs_le_abs_sub x t]
    have he : Real.exp (-(A U + x * B U)) ≤ Real.exp (CA + (|t| + 1) * max CB 0) :=
      (hexp x U).trans (Real.exp_le_exp.mpr (by nlinarith))
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hC' U) (mul_le_mul (hB' U) he (Real.exp_pos _).le hB0)
      (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) hC0
  have hdiff : ∀ᵐ U ∂μ, ∀ x ∈ Metric.ball t 1,
      HasDerivAt (fun y => C U * Real.exp (-(A U + y * B U)))
        (C U * (-B U * Real.exp (-(A U + x * B U)))) x := by
    refine Eventually.of_forall fun U x _ => ?_
    have h := (((hasDerivAt_id' x).mul_const (B U)).const_add (A U)).neg.exp
    refine (h.const_mul (C U)).congr_deriv ?_
    simp only [Pi.neg_apply]
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (x : ℝ) U => C U * Real.exp (-(A U + x * B U)))
    (F' := fun (x : ℝ) U => C U * (-B U * Real.exp (-(A U + x * B U))))
    (x₀ := t) (bound := fun _ => max CC 0 * (max CB 0 * Real.exp (CA + (|t| + 1) * max CB 0)))
    (s := Metric.ball t 1) (Metric.ball_mem_nhds t one_pos)
    (Eventually.of_forall fun x => (hF x).aestronglyMeasurable) hint
    ((hC.mul (hB.neg.mul (hE t))).aestronglyMeasurable) hbd (integrable_const _) hdiff
  refine key.2.congr_deriv ?_
  rw [← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  simp only
  ring

/-! ## 2. The mixed variance and the slope of the cut energy -/

/-- The unnormalized second moment `∫ S_mix² e^{−(β S_in + β_⊥ S_mix)}`. DERIVED: `2` the square. -/
noncomputable def mixSq (N : ℕ) (β βp : ℝ) (n : ℕ) : ℝ :=
  ∫ U, smixR N n U * smixR N n U * Real.exp (-(β * sinR N n U + βp * smixR N n U)) ∂piH N n

/-- **The Gibbs variance of the mixed action** `Var_n(S_mix) = ⟨S_mix²⟩_n − ⟨S_mix⟩_n²`. DERIVED: `2` the
square. -/
noncomputable def varMix (N : ℕ) (β βp : ℝ) (n : ℕ) : ℝ :=
  mixSq N β βp n / AnisoTorus.ZA N β βp n - meanMix N β βp n ^ 2

/-- `∂_{β_⊥} mixNum = −mixSq`. No numeral. -/
theorem hasDerivAt_mixNum (β t : ℝ) (n : ℕ) :
    HasDerivAt (fun x => mixNum N β x n) (-mixSq N β t n) t :=
  hasDerivAt_integral_mul_exp_lin (piH N n) (A := fun U => β * sinR N n U)
    (continuous_const.mul (continuous_sinR n)) (continuous_smixR n) (continuous_smixR n) t

/-- **`∂_{β_⊥} ⟨S_mix⟩_n = −Var_n(S_mix)`.** DERIVED: `2` the square. -/
theorem hasDerivAt_meanMix (β t : ℝ) (n : ℕ) :
    HasDerivAt (fun x => meanMix N β x n) (-varMix N β t n) t := by
  have hZ := (ZA_pos (N := N) β t n).ne'
  have h := (hasDerivAt_mixNum (N := N) β t n).div (hasDerivAt_ZA (N := N) β t n) hZ
  refine h.congr_deriv ?_
  unfold varMix meanMix
  field_simp
  ring

/-- **The slope of the mixed cut energy is a variance difference**:
`∂_{β_⊥} mixCut N β β_⊥ w = 16 Var_n(S_mix) − Var_{2n}(S_mix)`, `n = 2^w`. DERIVED: `16 = 2⁴` the copies; `2` the
doubling; `1` the next window. -/
theorem hasDerivAt_mixCut (β t : ℝ) (w : ℕ) :
    HasDerivAt (fun x => mixCut N β x w)
      (16 * varMix N β t (2 ^ w) - varMix N β t (2 ^ (w + 1))) t := by
  have h1 := hasDerivAt_meanMix (N := N) β t (2 ^ w)
  have h2 := hasDerivAt_meanMix (N := N) β t (2 ^ (w + 1))
  have e : (fun x => mixCut N β x w)
      = fun x => meanMix N β x (2 ^ (w + 1)) - 16 * meanMix N β x (2 ^ w) := funext fun x => rfl
  rw [e]
  exact (h2.sub (h1.const_mul 16)).congr_deriv (by ring)

/-! ## 3. The reduction -/

/-- **`VarGap N β`, a named input (not proved)**: the variance difference `16 Var_n − Var_{2n}` of the mixed
action is bounded above, uniformly over the windows `w ≥ 1` and the segment `t ∈ [0, β]`. DERIVED: `16`, `2`,
`1` as in `hasDerivAt_mixCut`; `1` the least window; `0` the axis. -/
def VarGap (N : ℕ) (β : ℝ) : Prop :=
  ∃ K : ℝ, ∀ w : ℕ, 1 ≤ w → ∀ t : ℝ, 0 ≤ t → t ≤ β →
    16 * varMix N β t (2 ^ w) - varMix N β t (2 ^ (w + 1)) ≤ K

/-- **A bounded variance difference bounds the cut energy**: `VarGap N β ⇒ MixCutBound N β`, with
`M = |β| max K 0`, by the mean value theorem on `[0, t]` from `mixCut_zero`. DERIVED: `0` the decoupled end and
the floor of `max K 0`; `1` the least window. -/
theorem mixCutBound_of_varGap {β : ℝ} (h : VarGap N β) : MixCutBound N β := by
  obtain ⟨K, hK⟩ := h
  refine ⟨|β| * max K 0, fun w hw t ht0 htβ => ?_⟩
  have hM0 : 0 ≤ |β| * max K 0 := mul_nonneg (abs_nonneg _) (le_max_right _ _)
  rcases ht0.eq_or_lt with h0 | hpos
  · rw [← h0, mixCut_zero β hw]; exact hM0
  obtain ⟨τ, hτ, hτeq⟩ := exists_hasDerivAt_eq_slope (fun x => mixCut N β x w)
    (fun x => 16 * varMix N β x (2 ^ w) - varMix N β x (2 ^ (w + 1))) hpos
    (fun x _ => (hasDerivAt_mixCut β x w).continuousAt.continuousWithinAt)
    (fun x _ => hasDerivAt_mixCut β x w)
  have hKτ := (hK w hw τ hτ.1.le (hτ.2.le.trans htβ)).trans (le_max_left K 0)
  rw [hτeq, mixCut_zero β hw, sub_zero, sub_zero, div_le_iff₀ hpos] at hKτ
  have htb : t ≤ |β| := htβ.trans (le_abs_self β)
  calc mixCut N β t w ≤ max K 0 * t := hKτ
    _ ≤ max K 0 * |β| := mul_le_mul_of_nonneg_left htb (le_max_right _ _)
    _ = |β| * max K 0 := mul_comm _ _

/-- **Frequently `TwoDCharacter ∧ VarGap` gives the strong end**, through `mixCutBound_of_varGap` and
`MixCut.strongEnd_of_mixCutBound`. DERIVED: `0` the excluded side. -/
theorem strongEnd_of_varGap (hN : N ≠ 0)
    (h : ∃ᶠ β in atTop, LayerSplit.TwoDCharacter N β ∧ VarGap N β) : StrongEnd N :=
  strongEnd_of_mixCutBound hN (h.mono fun _ hβ => ⟨hβ.1, mixCutBound_of_varGap hβ.2⟩)

end MassGap.MixCutTest

#print axioms MassGap.MixCutTest.hasDerivAt_integral_mul_exp_lin
#print axioms MassGap.MixCutTest.hasDerivAt_mixNum
#print axioms MassGap.MixCutTest.hasDerivAt_meanMix
#print axioms MassGap.MixCutTest.hasDerivAt_mixCut
#print axioms MassGap.MixCutTest.mixCutBound_of_varGap
#print axioms MassGap.MixCutTest.strongEnd_of_varGap
