import Mathlib

/-!
# MassGap.EntropyTools — data processing and Pinsker's inequality for `klDiv`

This module imports Mathlib only. It proves two facts about the Kullback–Leibler divergence
`InformationTheory.klDiv` that Mathlib at the pin does not state.

1. **Data processing for pushforwards** (`klDiv_map_le`): for finite measures `P`, `Q` on any
   measurable space and any measurable `χ`, `klDiv (P.map χ) (Q.map χ) ≤ klDiv P Q`. No
   hypothesis on the spaces. The proof reads the density of the pushforward, pulled back along `χ`,
   as the conditional expectation of `dP/dQ` given `χ` (`MeasureTheory.toReal_rnDeriv_map`), and
   applies the conditional Jensen inequality (`ConvexOn.map_condExp_le`) to the convex function
   `klFun` on `[0, ∞)`; integrating the conditional expectation returns `∫ klFun (dP/dQ) dQ`.
2. **Pinsker's inequality in observable form** (`abs_integral_sub_le_sqrt_two_mul_klDiv`): for
   probability measures with `klDiv P Q` finite and every measurable `f` with `|f| ≤ 1`,
   `|∫ f dP − ∫ f dQ| ≤ √(2 · KL(P‖Q))`, `KL` in nats. The proof has three parts.
   * `three_mul_sq_le_klFun`: `3 (x − 1)² ≤ (2x + 4) · klFun x` for `x ≥ 0`. The difference has
     derivative `4 ((x + 1) log x − 2 (x − 1))`, whose sign is that of `x − 1` because
     `(x + 1) log x − 2 (x − 1)` has derivative `log x + 1/x − 1 ≥ 0` and vanishes at `1`.
   * `two_mul_le_klFun_add`: pointwise, for `t ≥ 0`, `|g| ≤ 1` and `c > 0`,
     `2c (t g − g) ≤ c² klFun t + (2t + 4)/3`, from the first part and `(c|t − 1| − w)² ≥ 0`,
     `w = (2t + 4)/3`.
   * integrating at `t = dP/dQ` (whose `Q`-integral is `1`, so `∫ (2t + 4)/3 dQ = 2`) gives
     `2c (∫ g dP − ∫ g dQ) ≤ c² KL + 2` for every `c > 0` (`two_mul_integral_sub_le`), and
     `sq_le_mul_of_forall_two_mul_le` turns that family into `(∫ g dP − ∫ g dQ)² ≤ 2 KL`.

## Scope

Both statements are proved with no hypothesis beyond those displayed. `MassGap.ChiForest`
discharges `ZoomForest.PinskerObs` and `ZoomForest.KLDataProcessing` from them.
-/

noncomputable section

namespace MassGap.EntropyTools

open MeasureTheory InformationTheory
open scoped ENNReal

/-! ## 1. Data processing for pushforwards -/

section DataProcessing

/-- **The data-processing inequality for pushforwards.** For finite measures `P`, `Q` on a
measurable space `δ` and a measurable `χ : δ → η`, `klDiv (P.map χ) (Q.map χ) ≤ klDiv P Q`.
Off absolute continuity or integrability of `llr P Q` the right side is `∞`. Otherwise the
pushforward density at `χ x` is `Q[dP/dQ | χ]` at `x` (`toReal_rnDeriv_map`), the conditional Jensen
inequality for `klFun` on `[0, ∞)` bounds `klFun` of it by `Q[klFun (dP/dQ) | χ]`, and the
conditional expectation integrates to `∫ klFun (dP/dQ) dQ`, which is `klDiv P Q`.

DERIVED: no numeral. -/
theorem klDiv_map_le {δ η : Type*} [mδ : MeasurableSpace δ] [mη : MeasurableSpace η]
    (P Q : Measure δ) [IsFiniteMeasure P] [IsFiniteMeasure Q] {χ : δ → η} (hχ : Measurable χ) :
    klDiv (P.map χ) (Q.map χ) ≤ klDiv P Q := by
  by_cases hac : P ≪ Q
  swap
  · rw [klDiv_of_not_ac hac]
    exact le_top
  by_cases hint : Integrable (llr P Q) P
  swap
  · rw [klDiv_of_not_integrable hint]
    exact le_top
  have hacm : P.map χ ≪ Q.map χ := hac.map hχ
  have hm : mη.comap χ ≤ mδ := hχ.comap_le
  have hcond := toReal_rnDeriv_map hac hχ
  have hkl_int : Integrable (fun x => klFun (P.rnDeriv Q x).toReal) Q :=
    (integrable_klFun_rnDeriv_iff hac).mpr hint
  have hjensen : ∀ᵐ x ∂Q, klFun ((Q[fun a => (P.rnDeriv Q a).toReal | mη.comap χ]) x)
      ≤ (Q[fun a => klFun (P.rnDeriv Q a).toReal | mη.comap χ]) x :=
    convexOn_klFun.map_condExp_le (μ := Q) (f := fun a => (P.rnDeriv Q a).toReal) hm
      (continuous_klFun.lowerSemicontinuous.lowerSemicontinuousOn _)
      (ae_of_all _ (fun x => Set.mem_Ici.mpr ENNReal.toReal_nonneg)) isClosed_Ici
      Measure.integrable_toReal_rnDeriv hkl_int
  have hnn : 0 ≤ᵐ[Q] Q[fun a => klFun (P.rnDeriv Q a).toReal | mη.comap χ] :=
    condExp_nonneg (m := mη.comap χ) (f := fun a => klFun (P.rnDeriv Q a).toReal)
      (ae_of_all _ (fun x => klFun_nonneg ENNReal.toReal_nonneg))
  calc klDiv (P.map χ) (Q.map χ)
      = ∫⁻ y, ENNReal.ofReal (klFun ((P.map χ).rnDeriv (Q.map χ) y).toReal) ∂(Q.map χ) :=
        klDiv_eq_lintegral_klFun_of_ac hacm
    _ = ∫⁻ x, ENNReal.ofReal (klFun ((P.map χ).rnDeriv (Q.map χ) (χ x)).toReal) ∂Q :=
        lintegral_map (by fun_prop) hχ
    _ = ∫⁻ x, ENNReal.ofReal
          (klFun ((Q[fun a => (P.rnDeriv Q a).toReal | mη.comap χ]) x)) ∂Q := by
        refine lintegral_congr_ae ?_
        filter_upwards [hcond] with x hx
        exact congrArg (fun t => ENNReal.ofReal (klFun t)) hx
    _ ≤ ∫⁻ x, ENNReal.ofReal
          ((Q[fun a => klFun (P.rnDeriv Q a).toReal | mη.comap χ]) x) ∂Q := by
        refine lintegral_mono_ae ?_
        filter_upwards [hjensen] with x hx
        exact ENNReal.ofReal_le_ofReal hx
    _ = ENNReal.ofReal
          (∫ x, (Q[fun a => klFun (P.rnDeriv Q a).toReal | mη.comap χ]) x ∂Q) :=
        (ofReal_integral_eq_lintegral_ofReal integrable_condExp hnn).symm
    _ = ENNReal.ofReal (∫ x, klFun (P.rnDeriv Q x).toReal ∂Q) := by
        rw [integral_condExp hm]
    _ = klDiv P Q := by
        rw [klDiv_eq_lintegral_klFun_of_ac hac]
        exact ofReal_integral_eq_lintegral_ofReal hkl_int
          (ae_of_all _ (fun x => klFun_nonneg ENNReal.toReal_nonneg))

#print axioms klDiv_map_le

end DataProcessing

/-! ## 2. Pinsker's inequality -/

section Pinsker

/-- **`(y + 1) log y − 2 (y − 1)` is monotone on `(0, ∞)`**: its derivative `log y + 1/y − 1` is
nonnegative there (`Real.one_sub_inv_le_log_of_pos`). It vanishes at `1`, so it is `≤ 0` on
`(0, 1]` (`log_shift_nonpos`) and `≥ 0` on `[1, ∞)` (`log_shift_nonneg`).

DERIVED: `1` is the shift and the zero of `log`; `2` is the coefficient that makes the function
vanish at `1`; `0` is the lower end of the domain. -/
theorem log_shift_monotoneOn :
    MonotoneOn (fun y : ℝ => (y + 1) * Real.log y - 2 * (y - 1)) (Set.Ioi 0) := by
  have hH : ∀ y : ℝ, 0 < y →
      HasDerivAt (fun y => (y + 1) * Real.log y - 2 * (y - 1)) (Real.log y + y⁻¹ - 1) y := by
    intro y hy
    exact ((((hasDerivAt_id' y).add_const 1).fun_mul (Real.hasDerivAt_log hy.ne')).fun_sub
      (((hasDerivAt_id' y).sub_const 1).const_mul 2)).congr_deriv
      (by rw [add_mul, mul_inv_cancel₀ hy.ne']; ring)
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun y => Real.log y + y⁻¹ - 1)
    (convex_Ioi 0) (fun y hy => (hH y (Set.mem_Ioi.mp hy)).continuousAt.continuousWithinAt)
    (fun y hy => ?_) (fun y hy => ?_)
  · rw [interior_Ioi] at hy
    exact (hH y (Set.mem_Ioi.mp hy)).hasDerivWithinAt
  · rw [interior_Ioi] at hy
    have h1 := Real.one_sub_inv_le_log_of_pos (Set.mem_Ioi.mp hy)
    show 0 ≤ Real.log y + y⁻¹ - 1
    linarith

#print axioms log_shift_monotoneOn

/-- For `x ≥ 1`, `(x + 1) log x − 2 (x − 1) ≥ 0`.

DERIVED: `1` is the zero of the function; `2` its coefficient; `0` the sign concluded. -/
theorem log_shift_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ (x + 1) * Real.log x - 2 * (x - 1) := by
  have h := log_shift_monotoneOn (Set.mem_Ioi.mpr one_pos) (Set.mem_Ioi.mpr (by linarith)) hx
  simp only [Real.log_one] at h
  linarith

#print axioms log_shift_nonneg

/-- For `0 < x ≤ 1`, `(x + 1) log x − 2 (x − 1) ≤ 0`.

DERIVED: `1` is the zero of the function; `2` its coefficient; `0` the lower end of `x` and the
sign concluded. -/
theorem log_shift_nonpos {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1) :
    (x + 1) * Real.log x - 2 * (x - 1) ≤ 0 := by
  have h := log_shift_monotoneOn (Set.mem_Ioi.mpr hx0) (Set.mem_Ioi.mpr one_pos) hx
  simp only [Real.log_one] at h
  linarith

#print axioms log_shift_nonpos

/-- **The pointwise inequality behind Pinsker's constant.** For `x ≥ 0`,
`3 (x − 1)² ≤ (2x + 4) · klFun x`, `klFun x = x log x + 1 − x`. The difference
`Φ x = (2x + 4) klFun x − 3 (x − 1)²` is continuous, vanishes at `1`, and on `(0, ∞)` has
derivative `4 ((x + 1) log x − 2 (x − 1))`, which is `≤ 0` on `(0, 1]` and `≥ 0` on `[1, ∞)`
(`log_shift_nonpos`, `log_shift_nonneg`); so `Φ` is antitone on `[0, 1]`, monotone on `[1, ∞)`,
and nonnegative.

DERIVED: `3`, `2`, `4` are the coefficients for which `∫ (2t + 4)/3 dQ = 2` at a density `t` of
mean one, the `2` of Pinsker's `√(2 KL)`; `1` is the minimum point of `klFun`; `0` the lower end of
`x` and of the interval. -/
theorem three_mul_sq_le_klFun {x : ℝ} (hx : 0 ≤ x) :
    3 * (x - 1) ^ 2 ≤ (2 * x + 4) * klFun x := by
  have hΦ : ∀ y : ℝ, 0 < y →
      HasDerivAt (fun y => (2 * y + 4) * klFun y - 3 * ((y - 1) * (y - 1)))
        (4 * ((y + 1) * Real.log y - 2 * (y - 1))) y := by
    intro y hy
    exact (((((hasDerivAt_id' y).const_mul 2).add_const 4).fun_mul
      (hasDerivAt_klFun hy.ne')).fun_sub
      ((((hasDerivAt_id' y).sub_const 1).fun_mul
        ((hasDerivAt_id' y).sub_const 1)).const_mul 3)).congr_deriv
      (by rw [klFun_apply]; ring)
  have hΦc : Continuous (fun y : ℝ => (2 * y + 4) * klFun y - 3 * ((y - 1) * (y - 1))) := by
    fun_prop
  rcases le_total x 1 with hx1 | hx1
  · have hanti : AntitoneOn (fun y : ℝ => (2 * y + 4) * klFun y - 3 * ((y - 1) * (y - 1)))
        (Set.Icc 0 1) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos
        (f' := fun y => 4 * ((y + 1) * Real.log y - 2 * (y - 1)))
        (convex_Icc 0 1) hΦc.continuousOn (fun y hy => ?_) (fun y hy => ?_)
      · rw [interior_Icc] at hy
        exact (hΦ y hy.1).hasDerivWithinAt
      · rw [interior_Icc] at hy
        have h := log_shift_nonpos hy.1 hy.2.le
        show 4 * ((y + 1) * Real.log y - 2 * (y - 1)) ≤ 0
        linarith
    have h := hanti ⟨hx, hx1⟩ ⟨zero_le_one, le_refl 1⟩ hx1
    simp only [klFun_one] at h
    linarith
  · have hmono : MonotoneOn (fun y : ℝ => (2 * y + 4) * klFun y - 3 * ((y - 1) * (y - 1)))
        (Set.Ici 1) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg
        (f' := fun y => 4 * ((y + 1) * Real.log y - 2 * (y - 1)))
        (convex_Ici 1) hΦc.continuousOn (fun y hy => ?_) (fun y hy => ?_)
      · rw [interior_Ici] at hy
        exact (hΦ y (zero_lt_one.trans (Set.mem_Ioi.mp hy))).hasDerivWithinAt
      · rw [interior_Ici] at hy
        have h := log_shift_nonneg (Set.mem_Ioi.mp hy).le
        show 0 ≤ 4 * ((y + 1) * Real.log y - 2 * (y - 1))
        linarith
    have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx1) hx1
    simp only [klFun_one] at h
    linarith

#print axioms three_mul_sq_le_klFun

/-- **Pinsker, pointwise.** For `t ≥ 0`, `|g| ≤ 1` and `c > 0`,
`2c (t g − g) ≤ c² klFun t + (2t + 4)/3`. With `w = (2t + 4)/3 > 0`: `(t − 1)² ≤ w klFun t`
(`three_mul_sq_le_klFun`), `(c |t − 1| − w)² ≥ 0` gives `2c |t − 1| w ≤ c² (t − 1)² + w²`, hence
`2c |t − 1| ≤ c² klFun t + w`, and `t g − g = g (t − 1) ≤ |t − 1|`.

DERIVED: `2`, `3`, `4` are `three_mul_sq_le_klFun`'s; `1` is the bound on `g` and the mean of a
density; `0` the lower end of `t` and `c`. -/
theorem two_mul_le_klFun_add {t g c : ℝ} (ht : 0 ≤ t) (hg : |g| ≤ 1) (hc : 0 < c) :
    2 * c * (t * g - g) ≤ c ^ 2 * klFun t + (2 * t + 4) / 3 := by
  have hk := three_mul_sq_le_klFun ht
  have hW : 0 < (2 * t + 4) / 3 := by linarith
  have h1 : (t - 1) ^ 2 ≤ (2 * t + 4) / 3 * klFun t := by linarith
  have e : (c * |t - 1| - (2 * t + 4) / 3) ^ 2
      = c ^ 2 * (t - 1) ^ 2 - 2 * c * |t - 1| * ((2 * t + 4) / 3) + ((2 * t + 4) / 3) ^ 2 := by
    rw [← sq_abs (t - 1)]
    ring
  have h2 : 2 * c * |t - 1| * ((2 * t + 4) / 3)
      ≤ c ^ 2 * (t - 1) ^ 2 + ((2 * t + 4) / 3) ^ 2 := by
    linarith [sq_nonneg (c * |t - 1| - (2 * t + 4) / 3)]
  have h3 : c ^ 2 * (t - 1) ^ 2 ≤ c ^ 2 * ((2 * t + 4) / 3 * klFun t) :=
    mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
  have h4 : 2 * c * |t - 1| * ((2 * t + 4) / 3)
      ≤ (c ^ 2 * klFun t + (2 * t + 4) / 3) * ((2 * t + 4) / 3) := by
    nlinarith [h2, h3]
  have h5 : 2 * c * |t - 1| ≤ c ^ 2 * klFun t + (2 * t + 4) / 3 :=
    le_of_mul_le_mul_right h4 hW
  have h6 : t * g - g ≤ |t - 1| := by
    have e' : t * g - g = g * (t - 1) := by ring
    rw [e']
    calc g * (t - 1) ≤ |g * (t - 1)| := le_abs_self _
      _ = |g| * |t - 1| := abs_mul _ _
      _ ≤ 1 * |t - 1| := mul_le_mul_of_nonneg_right hg (abs_nonneg _)
      _ = |t - 1| := one_mul _
  have h7 : 2 * c * (t * g - g) ≤ 2 * c * |t - 1| :=
    mul_le_mul_of_nonneg_left h6 (by linarith)
  linarith

#print axioms two_mul_le_klFun_add

/-- **Squares from a family of linear bounds.** If `0 ≤ X`, `0 ≤ A`, `0 ≤ B` and
`2 c X ≤ c² A + B` for every `c > 0`, then `X² ≤ A B`. At `A > 0` take `c = X / A`; at `A = 0`
and `X > 0` the choice `c = (B + 1)/X` gives `2B + 2 ≤ B`, which is false.

DERIVED: `2` is the cross term of `(c √A − √B)²`; `1` keeps `B + 1` positive; `0` is the lower end
of `X`, `A`, `B`, `c`. -/
theorem sq_le_mul_of_forall_two_mul_le {X A B : ℝ} (hX : 0 ≤ X) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ c : ℝ, 0 < c → 2 * c * X ≤ c ^ 2 * A + B) : X ^ 2 ≤ A * B := by
  rcases hX.eq_or_lt with hX0 | hXpos
  · rw [← hX0]
    nlinarith [mul_nonneg hA hB]
  rcases hA.eq_or_lt with hA0 | hApos
  · exfalso
    have hc : 0 < (B + 1) / X := div_pos (by linarith) hXpos
    have h1 := h _ hc
    have e1 : ((B + 1) / X) ^ 2 * A = 0 := by rw [← hA0, mul_zero]
    have e2 : 2 * ((B + 1) / X) * X = 2 * (B + 1) := by
      rw [mul_assoc, div_mul_cancel₀ _ hXpos.ne']
    linarith
  · have hc : 0 < X / A := div_pos hXpos hApos
    have hcA : X / A * A = X := div_mul_cancel₀ X hApos.ne'
    have h1 := h _ hc
    have e1 : (X / A) ^ 2 * A = X / A * X := by rw [sq, mul_assoc, hcA]
    have e2 : X / A * X ≤ B := by linarith
    have e3 : X ^ 2 = X / A * X * A := by rw [mul_right_comm, hcA, sq]
    rw [e3]
    calc X / A * X * A ≤ B * A := mul_le_mul_of_nonneg_right e2 hApos.le
      _ = A * B := mul_comm B A

#print axioms sq_le_mul_of_forall_two_mul_le

/-- **Pinsker, integrated, linear form.** For probability measures `P ≪ Q` with `llr P Q`
integrable, a measurable `g` with `|g| ≤ 1` and `c > 0`:
`2c (∫ g dP − ∫ g dQ) ≤ c² · KL(P‖Q) + 2`. `∫ g dP = ∫ (dP/dQ) g dQ`; integrate
`two_mul_le_klFun_add` at `t = dP/dQ`, whose `Q`-integral is `1`, and `∫ klFun (dP/dQ) dQ` is
`(klDiv P Q).toReal` (`toReal_klDiv_eq_integral_klFun`).

DERIVED: `2` on the right is `∫ (2t + 4)/3 dQ` at `∫ t dQ = 1`; `2`, `3`, `4` are
`two_mul_le_klFun_add`'s; `1` is the bound on `g` and the total mass; `0` the lower end of `c`. -/
theorem two_mul_integral_sub_le {δ : Type*} [MeasurableSpace δ] (P Q : Measure δ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hac : P ≪ Q)
    (hint : Integrable (llr P Q) P) {g : δ → ℝ} (hg : Measurable g) (hgb : ∀ x, |g x| ≤ 1)
    {c : ℝ} (hc : 0 < c) :
    2 * c * (∫ x, g x ∂P - ∫ x, g x ∂Q) ≤ c ^ 2 * (klDiv P Q).toReal + 2 := by
  have hgP : Integrable g P := Integrable.of_bound hg.aestronglyMeasurable 1
    (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; exact hgb x))
  have hgQ : Integrable g Q := Integrable.of_bound hg.aestronglyMeasurable 1
    (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; exact hgb x))
  have hrg : Integrable (fun x => (P.rnDeriv Q x).toReal * g x) Q :=
    (integrable_toReal_rnDeriv_mul_iff hac).mpr hgP
  have hr : Integrable (fun x => (P.rnDeriv Q x).toReal) Q := Measure.integrable_toReal_rnDeriv
  have hkl : Integrable (fun x => klFun (P.rnDeriv Q x).toReal) Q :=
    (integrable_klFun_rnDeriv_iff hac).mpr hint
  have hK : (klDiv P Q).toReal = ∫ x, klFun (P.rnDeriv Q x).toReal ∂Q :=
    toReal_klDiv_eq_integral_klFun hac
  have hr1 : ∫ x, (P.rnDeriv Q x).toReal ∂Q = 1 := by
    rw [Measure.integral_toReal_rnDeriv hac, probReal_univ]
  have hP : ∫ x, g x ∂P = ∫ x, (P.rnDeriv Q x).toReal * g x ∂Q :=
    (integral_toReal_rnDeriv_mul hac).symm
  have hdiff : ∫ x, g x ∂P - ∫ x, g x ∂Q
      = ∫ x, ((P.rnDeriv Q x).toReal * g x - g x) ∂Q := by
    rw [hP, integral_sub hrg hgQ]
  have iL : Integrable (fun x => 2 * c * ((P.rnDeriv Q x).toReal * g x - g x)) Q :=
    (hrg.sub hgQ).const_mul (2 * c)
  have hA : Integrable (fun x => c ^ 2 * klFun (P.rnDeriv Q x).toReal) Q := hkl.const_mul (c ^ 2)
  have hB2 : Integrable (fun x => 2 * (P.rnDeriv Q x).toReal) Q := hr.const_mul 2
  have hB : Integrable (fun x => (2 * (P.rnDeriv Q x).toReal + 4) / 3) Q :=
    (hB2.add (integrable_const 4)).div_const 3
  have iR : Integrable
      (fun x => c ^ 2 * klFun (P.rnDeriv Q x).toReal + (2 * (P.rnDeriv Q x).toReal + 4) / 3) Q :=
    hA.add hB
  have hmono : ∫ x, 2 * c * ((P.rnDeriv Q x).toReal * g x - g x) ∂Q
      ≤ ∫ x, (c ^ 2 * klFun (P.rnDeriv Q x).toReal + (2 * (P.rnDeriv Q x).toReal + 4) / 3) ∂Q :=
    integral_mono iL iR (fun x => two_mul_le_klFun_add ENNReal.toReal_nonneg (hgb x) hc)
  have hL : ∫ x, 2 * c * ((P.rnDeriv Q x).toReal * g x - g x) ∂Q
      = 2 * c * (∫ x, g x ∂P - ∫ x, g x ∂Q) := by
    rw [integral_const_mul, hdiff]
  have i1 : ∫ x, (c ^ 2 * klFun (P.rnDeriv Q x).toReal + (2 * (P.rnDeriv Q x).toReal + 4) / 3) ∂Q
      = ∫ x, c ^ 2 * klFun (P.rnDeriv Q x).toReal ∂Q
        + ∫ x, (2 * (P.rnDeriv Q x).toReal + 4) / 3 ∂Q := integral_add hA hB
  have i2 : ∫ x, c ^ 2 * klFun (P.rnDeriv Q x).toReal ∂Q = c ^ 2 * (klDiv P Q).toReal := by
    rw [integral_const_mul, ← hK]
  have i3 : ∫ x, (2 * (P.rnDeriv Q x).toReal + 4) / 3 ∂Q
      = (∫ x, (2 * (P.rnDeriv Q x).toReal + 4) ∂Q) / 3 := integral_div 3 _
  have i4 : ∫ x, (2 * (P.rnDeriv Q x).toReal + 4) ∂Q
      = ∫ x, 2 * (P.rnDeriv Q x).toReal ∂Q + ∫ _x, (4 : ℝ) ∂Q :=
    integral_add hB2 (integrable_const 4)
  have i5 : ∫ x, 2 * (P.rnDeriv Q x).toReal ∂Q = 2 * ∫ x, (P.rnDeriv Q x).toReal ∂Q :=
    integral_const_mul 2 _
  have i6 : ∫ _x, (4 : ℝ) ∂Q = 4 := by rw [integral_const, probReal_univ, one_smul]
  rw [hr1] at i5
  linarith

#print axioms two_mul_integral_sub_le

/-- **Pinsker's inequality in observable form.** For probability measures `P`, `Q` with
`klDiv P Q ≠ ∞` and a measurable `f` with `|f| ≤ 1`,
`|∫ f dP − ∫ f dQ| ≤ √(2 · (klDiv P Q).toReal)`: twice the total variation is at most
`√(2 KL)`, `KL` in nats (Pinsker 1964; Csiszár 1967; Kemperman 1969). `two_mul_integral_sub_le`
at `f` and at `−f` gives `2c (±X) ≤ c² KL + 2` for every `c > 0`, and
`sq_le_mul_of_forall_two_mul_le` gives `X² ≤ 2 KL`.

DERIVED: `2` is Pinsker's constant in the observable form, `∫ (2t + 4)/3 dQ` at a density of mean
one; `1` the bound on `f`; `0` the sign split. -/
theorem abs_integral_sub_le_sqrt_two_mul_klDiv {δ : Type*} [MeasurableSpace δ] (P Q : Measure δ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hkl : klDiv P Q ≠ ∞) {f : δ → ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
    |∫ x, f x ∂P - ∫ x, f x ∂Q| ≤ Real.sqrt (2 * (klDiv P Q).toReal) := by
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp hkl
  have hK0 : 0 ≤ (klDiv P Q).toReal := ENNReal.toReal_nonneg
  have h1 : ∀ c : ℝ, 0 < c →
      2 * c * (∫ x, f x ∂P - ∫ x, f x ∂Q) ≤ c ^ 2 * (klDiv P Q).toReal + 2 :=
    fun c hc => two_mul_integral_sub_le P Q hac hint hf hb hc
  have h2 : ∀ c : ℝ, 0 < c →
      2 * c * (-(∫ x, f x ∂P - ∫ x, f x ∂Q)) ≤ c ^ 2 * (klDiv P Q).toReal + 2 := by
    intro c hc
    have e : 2 * c * (∫ x, -f x ∂P - ∫ x, -f x ∂Q) ≤ c ^ 2 * (klDiv P Q).toReal + 2 :=
      two_mul_integral_sub_le P Q hac hint (g := fun x => -f x) hf.neg
        (fun x => (abs_neg (f x)).trans_le (hb x)) hc
    rw [integral_neg, integral_neg] at e
    linarith
  rcases le_total 0 (∫ x, f x ∂P - ∫ x, f x ∂Q) with hX | hX
  · have hsq := sq_le_mul_of_forall_two_mul_le hX hK0 zero_le_two h1
    exact Real.abs_le_sqrt (by linarith)
  · have hsq := sq_le_mul_of_forall_two_mul_le (neg_nonneg.mpr hX) hK0 zero_le_two h2
    exact Real.abs_le_sqrt (by nlinarith)

#print axioms abs_integral_sub_le_sqrt_two_mul_klDiv

end Pinsker

end MassGap.EntropyTools
