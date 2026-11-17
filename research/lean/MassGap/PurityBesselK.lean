import MassGap.PurityWilson
import MassGap.PurityFreeField

/-!
# MassGap.PurityBesselK — the modified Bessel function `K₁`, Appendix B of the purity paper

Appendix B of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford
and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`)
uses the integral representation [DLMF 10.32.9]
`K₁(u) = ∫₀^∞ e^{−u cosh v} cosh v dv = ∫₀^∞ e^{−u√(1+q²)} dq ≤ 1/u` (`q = sinh v`).
Mathlib has no modified Bessel functions; `K1` is defined here by the first integral.

* `K1`: `K₁(u) = ∫₀^∞ e^{−u cosh v} cosh v dv`; `K1_nonneg`.
* `mul_exp_neg_le`: `x e^{−ux} ≤ (2/u) e^{−ux/2}` at `u > 0`, the domination that makes the
  integrand integrable (`continuous_K1_integrand`, `integrableOn_K1`).
* `sqrt_one_add_sinh_sq`, `continuous_sqrt_integrand`, `exp_sqrt_le`, `integrableOn_sqrt`;
  `K1_eq_sqrt`: `K₁(u) = ∫₀^∞ e^{−u√(1+q²)} dq` at `u > 0`, by `q = sinh v`.
* `K1_le`: `K₁(u) ≤ 1/u` at `u > 0`, from `|q| ≤ √(1+q²)` and `∫₀^∞ e^{−uq} dq = 1/u`.
* `moment_gamma`: `∫₀^∞ u⁶ e^{−cu} du = 720/c⁷`; `moment_inner`: the inner integral
  `∫₀^∞ u⁶ e^{−u cosh v} cosh v du = 720/cosh⁶ v`; `moment_K1_sech`: `∫₀^∞ u⁶ K₁ = 6! ∫₀^∞ sech⁶`
  (Tonelli, `integral_integral_swap`).
* `one_sub_tanh_sq`, `hasDerivAt_tanh`, `tendsto_tanh_atTop`; `integral_sech6`:
  `∫₀^∞ sech⁶ = 8/15` by the antiderivative `t − 2t³/3 + t⁵/5`, `t = tanh v`;
  `integral_sech6_eq_poly`: `= ∫₀¹ (1 − z²)² dz` (`PurityFreeField.poly_integral`).
* `moment_K1`: `∫₀^∞ u⁶ K₁(u) du = 384` (`PurityFreeField.moment_value`);
  `integrableOn_moment_K1`.

DERIVED (module-wide): the `2` of `u/2` in `mul_exp_neg_le`, the split of `e^{−ux}` into two
equal halves.
-/

namespace MassGap.PurityBesselK

open Real MeasureTheory Set Filter Topology

/-- `K₁(u) = ∫₀^∞ e^{−u cosh v} cosh v dv`. -/
noncomputable def K1 (u : ℝ) : ℝ := ∫ v in Ioi 0, exp (-(u * cosh v)) * cosh v

theorem K1_nonneg (u : ℝ) : 0 ≤ K1 u :=
  setIntegral_nonneg measurableSet_Ioi fun v _ => mul_nonneg (exp_pos _).le (cosh_pos v).le

/-- `√(1 + sinh² v) = cosh v`. -/
theorem sqrt_one_add_sinh_sq (v : ℝ) : √(1 + sinh v ^ 2) = cosh v := by
  rw [← cosh_sq', sqrt_sq (cosh_pos v).le]

/-- `x e^{−ux} ≤ (2/u) e^{−ux/2}` at `u > 0`. -/
theorem mul_exp_neg_le {u : ℝ} (hu : 0 < u) (x : ℝ) :
    x * exp (-(u * x)) ≤ 2 / u * exp (-(u / 2 * x)) := by
  have hx : x ≤ 2 / u * exp (u / 2 * x) := by
    have h1 := add_one_le_exp (u / 2 * x)
    have h2 : 2 / u * (u / 2 * x + 1) = x + 2 / u := by field_simp
    have h3 : 0 < 2 / u := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h3.le]
  have e1 : exp (-(u * x)) = exp (-(u / 2 * x)) * exp (-(u / 2 * x)) := by
    rw [← exp_add]; congr 1; ring
  have e2 : exp (u / 2 * x) * exp (-(u / 2 * x)) = 1 := by
    rw [← exp_add, add_neg_cancel, exp_zero]
  have hp : 0 < exp (-(u / 2 * x)) := exp_pos _
  calc x * exp (-(u * x)) = x * exp (-(u / 2 * x)) * exp (-(u / 2 * x)) := by
        rw [e1, mul_assoc]
    _ ≤ 2 / u * exp (u / 2 * x) * exp (-(u / 2 * x)) * exp (-(u / 2 * x)) := by
        gcongr
    _ = 2 / u * exp (-(u / 2 * x)) := by rw [mul_assoc (2 / u), e2, mul_one]

theorem continuous_K1_integrand (u : ℝ) :
    Continuous fun v : ℝ => exp (-(u * cosh v)) * cosh v :=
  (continuous_exp.comp (continuous_const.mul continuous_cosh).neg).mul continuous_cosh

/-- `e^{−u cosh v} cosh v` is integrable on `[0, ∞)` at `u > 0`. -/
theorem integrableOn_K1 {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun v : ℝ => exp (-(u * cosh v)) * cosh v) (Ici 0) := by
  have hg : IntegrableOn (fun v : ℝ => 2 / u * exp (-(u / 2) * v)) (Ici 0) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).2
      (integrableOn_exp_mul_Ioi (by linarith : -(u / 2) < 0) 0)).const_mul _
  refine hg.mono' (continuous_K1_integrand u).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ici).2 (Eventually.of_forall fun v hv => ?_)
  have hv0 : (0 : ℝ) ≤ v := hv
  have hvc : v ≤ cosh v := (self_le_sinh_iff.2 hv0).trans (sinh_lt_cosh v).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (exp_pos _).le (cosh_pos v).le), mul_comm]
  calc cosh v * exp (-(u * cosh v)) ≤ 2 / u * exp (-(u / 2 * cosh v)) := mul_exp_neg_le hu _
    _ ≤ 2 / u * exp (-(u / 2) * v) := by
        gcongr
        rw [neg_mul, neg_le_neg_iff]
        exact mul_le_mul_of_nonneg_left hvc (by positivity)

theorem continuous_sqrt_integrand (u : ℝ) :
    Continuous fun q : ℝ => exp (-(u * √(1 + q ^ 2))) := by
  fun_prop

/-- `e^{−u√(1+q²)} ≤ e^{−u|q|}`. -/
theorem exp_sqrt_le {u : ℝ} (hu : 0 ≤ u) (q : ℝ) :
    exp (-(u * √(1 + q ^ 2))) ≤ exp (-(u * |q|)) := by
  have h : |q| ≤ √(1 + q ^ 2) := abs_le_sqrt (by linarith)
  exact exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left h hu))

/-- `e^{−u√(1+q²)}` is integrable on `[0, ∞)` at `u > 0`. -/
theorem integrableOn_sqrt {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun q : ℝ => exp (-(u * √(1 + q ^ 2)))) (Ici 0) := by
  have hg : IntegrableOn (fun q : ℝ => exp (-u * q)) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).2 (integrableOn_exp_mul_Ioi (by linarith) 0)
  refine hg.mono' (continuous_sqrt_integrand u).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ici).2 (Eventually.of_forall fun q hq => ?_)
  have hq0 : (0 : ℝ) ≤ q := hq
  rw [Real.norm_eq_abs, abs_of_nonneg (exp_pos _).le, neg_mul]
  simpa [abs_of_nonneg hq0] using exp_sqrt_le hu.le q

/-- `K₁(u) = ∫₀^∞ e^{−u√(1+q²)} dq` at `u > 0` (`q = sinh v`). -/
theorem K1_eq_sqrt {u : ℝ} (hu : 0 < u) :
    K1 u = ∫ q in Ioi 0, exp (-(u * √(1 + q ^ 2))) := by
  have hft : Tendsto sinh atTop atTop :=
    tendsto_atTop_mono' atTop ((eventually_ge_atTop 0).mono fun x hx => self_le_sinh_iff.2 hx)
      tendsto_id
  have himg : sinh '' Ici 0 = Ici 0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact sinh_nonneg_iff.2 hx
    · intro hy
      exact ⟨arsinh y, arsinh_nonneg_iff.2 hy, sinh_arsinh y⟩
  have h := integral_comp_mul_deriv_Ioi (f := sinh) (f' := cosh)
    (g := fun q => exp (-(u * √(1 + q ^ 2)))) (a := 0) continuous_sinh.continuousOn hft
    (fun x _ => (hasDerivAt_sinh x).hasDerivWithinAt)
    (continuous_sqrt_integrand u).continuousOn
    (by rw [himg]; exact integrableOn_sqrt hu)
    (by simpa only [Function.comp_def, sqrt_one_add_sinh_sq] using integrableOn_K1 hu)
  rw [sinh_zero] at h
  rw [K1, ← h]
  simp only [Function.comp_def, sqrt_one_add_sinh_sq]

/-- `K₁(u) ≤ 1/u` at `u > 0`. -/
theorem K1_le {u : ℝ} (hu : 0 < u) : K1 u ≤ 1 / u := by
  have he : ∫ q in Ioi (0 : ℝ), exp (-u * q) = 1 / u := by
    rw [integral_exp_mul_Ioi (by linarith) 0, mul_zero, exp_zero]
    field_simp
  rw [K1_eq_sqrt hu, ← he]
  refine setIntegral_mono_on ((integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).1 (integrableOn_sqrt hu))
    (integrableOn_exp_mul_Ioi (by linarith) 0) measurableSet_Ioi fun q hq => ?_
  have hq0 : (0 : ℝ) ≤ q := le_of_lt hq
  rw [neg_mul]
  simpa [abs_of_nonneg hq0] using exp_sqrt_le hu.le q

/-- `∫₀^∞ u⁶ e^{−cu} du = 6!/c⁷ = 720/c⁷` at `c > 0` (`Γ(7) = 6!`). -/
theorem moment_gamma {c : ℝ} (hc : 0 < c) :
    ∫ u in Ioi 0, u ^ 6 * exp (-(c * u)) = 720 / c ^ 7 := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := 7) (by norm_num) hc
  have h6 : (7 : ℝ) - 1 = ((6 : ℕ) : ℝ) := by norm_num
  have h7 : (7 : ℝ) = ((6 : ℕ) : ℝ) + 1 := by norm_num
  have hG : Gamma 7 = 720 := by
    rw [h7, Gamma_nat_eq_factorial]; norm_num [Nat.factorial]
  simp_rw [h6, rpow_natCast] at h
  rw [h, hG, show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, rpow_natCast, div_pow, one_pow]
  ring

/-- `1 − tanh² v = 1/cosh² v`. -/
theorem one_sub_tanh_sq (v : ℝ) : 1 - tanh v ^ 2 = 1 / cosh v ^ 2 := by
  rw [tanh_eq_sinh_div_cosh, div_pow, one_sub_div (pow_ne_zero 2 (cosh_pos v).ne'),
    cosh_sq_sub_sinh_sq]

/-- `tanh' = 1 − tanh²`. -/
theorem hasDerivAt_tanh (v : ℝ) : HasDerivAt tanh (1 - tanh v ^ 2) v := by
  have h := (hasDerivAt_sinh v).div (hasDerivAt_cosh v) (cosh_pos v).ne'
  have hf : sinh / cosh = tanh := funext fun x => by rw [Pi.div_apply, tanh_eq_sinh_div_cosh]
  rw [hf] at h
  rw [one_sub_tanh_sq]
  refine h.congr_deriv ?_
  rw [show cosh v * cosh v - sinh v * sinh v = 1 by linear_combination cosh_sq_sub_sinh_sq v]

/-- `tanh v → 1` as `v → ∞`. -/
theorem tendsto_tanh_atTop : Tendsto tanh atTop (𝓝 1) := by
  have h : Tendsto (fun x : ℝ => exp (2 * x) + 1) atTop atTop :=
    (tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop two_pos)).atTop_add tendsto_const_nhds
  have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub (h.inv_tendsto_atTop.const_mul 2)
  rw [mul_zero, sub_zero] at h2
  exact h2.congr fun x => by rw [PurityWilson.tanh_eq_one_sub, div_eq_mul_inv]; rfl

/-- `∫₀^∞ sech⁶ v dv = 8/15`, by the antiderivative `t − 2t³/3 + t⁵/5` at `t = tanh v`
(the substitution `z = tanh v`, `sech² = 1 − z²`). -/
theorem integral_sech6 : ∫ v in Ioi 0, 1 / cosh v ^ 6 = 8 / 15 := by
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun v => tanh v - 2 / 3 * tanh v ^ 3 + tanh v ^ 5 / 5)
      (1 / cosh x ^ 6) x := by
    intro x _
    have ht := hasDerivAt_tanh x
    refine ((ht.sub ((ht.pow 3).const_mul (2 / 3))).add ((ht.pow 5).div_const 5)).congr_deriv ?_
    have h3 : (1 - tanh x ^ 2) ^ 3 = 1 / cosh x ^ 6 := by
      rw [one_sub_tanh_sq]; field_simp
    rw [← h3]; push_cast; ring
  have hl : Tendsto (fun v => tanh v - 2 / 3 * tanh v ^ 3 + tanh v ^ 5 / 5) atTop (𝓝 (8 / 15)) := by
    rw [show (8 / 15 : ℝ) = 1 - 2 / 3 * 1 ^ 3 + 1 ^ 5 / 5 by norm_num]
    exact (tendsto_tanh_atTop.sub ((tendsto_tanh_atTop.pow 3).const_mul (2 / 3))).add
      ((tendsto_tanh_atTop.pow 5).div_const 5)
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd (fun x _ => by positivity) hl, tanh_zero]
  norm_num

/-- `∫₀^∞ sech⁶ = ∫₀¹ (1 − z²)² dz`. -/
theorem integral_sech6_eq_poly :
    ∫ v in Ioi 0, 1 / cosh v ^ 6 = ∫ z in (0 : ℝ)..1, (1 - z ^ 2) ^ 2 := by
  rw [integral_sech6, PurityFreeField.poly_integral]

/-- The inner `u`-integral of the Tonelli step: `∫₀^∞ u⁶ e^{−u cosh v} cosh v du = 720/cosh⁶ v`. -/
theorem moment_inner (v : ℝ) :
    ∫ u in Ioi 0, u ^ 6 * (exp (-(u * cosh v)) * cosh v) = 720 / cosh v ^ 6 := by
  have hc := cosh_pos v
  calc ∫ u in Ioi 0, u ^ 6 * (exp (-(u * cosh v)) * cosh v)
      = cosh v * ∫ u in Ioi 0, u ^ 6 * exp (-(cosh v * u)) := by
        rw [← integral_const_mul]; congr 1; ext u; rw [mul_comm u]; ring
    _ = 720 / cosh v ^ 6 := by rw [moment_gamma hc]; field_simp

/-- `∫₀^∞ u⁶ K₁(u) du = 6! ∫₀^∞ sech⁶ v dv` (Tonelli). -/
theorem moment_K1_sech :
    ∫ u in Ioi 0, u ^ 6 * K1 u = (Nat.factorial 6 : ℝ) * ∫ v in Ioi 0, 1 / cosh v ^ 6 := by
  set F : ℝ → ℝ → ℝ := fun u v => u ^ 6 * (exp (-(u * cosh v)) * cosh v) with hF
  have hs : ∫ v in Ioi 0, 720 / cosh v ^ 6 = 720 * (8 / 15) := by
    simp_rw [div_eq_mul_one_div (720 : ℝ)]
    rw [integral_const_mul, integral_sech6]
  have hint : Integrable (Function.uncurry F) ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    refine (integrable_prod_iff' ?_).2 ⟨Eventually.of_forall fun v => ?_, ?_⟩
    · exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
        p.1 ^ 6 * (exp (-(p.1 * cosh p.2)) * cosh p.2)).aestronglyMeasurable
    · refine Integrable.of_integral_ne_zero ?_
      simp only [Function.uncurry_apply_pair, hF]
      rw [moment_inner v]
      exact (div_pos (by norm_num) (pow_pos (cosh_pos v) 6)).ne'
    · have he : (fun v => ∫ u in Ioi 0, ‖Function.uncurry F (u, v)‖) = fun v => 720 / cosh v ^ 6 := by
        funext v
        rw [← moment_inner v]
        refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
        have hu0 : (0 : ℝ) < u := hu
        simp only [Function.uncurry_apply_pair, hF]
        exact Real.norm_of_nonneg (by positivity)
      rw [he]
      refine Integrable.of_integral_ne_zero ?_
      rw [hs]; norm_num
  have hK : ∫ u in Ioi 0, u ^ 6 * K1 u = ∫ u in Ioi 0, ∫ v in Ioi 0, F u v := by
    simp_rw [hF, K1, ← integral_const_mul]
  rw [hK, integral_integral_swap hint]
  simp_rw [hF, moment_inner]
  rw [hs, integral_sech6]
  norm_num [Nat.factorial]

/-- `∫₀^∞ u⁶ K₁(u) du = 6! · 8/15 = 384`. -/
theorem moment_K1 : ∫ u in Ioi 0, u ^ 6 * K1 u = 384 := by
  rw [moment_K1_sech, integral_sech6, PurityFreeField.moment_value]

/-- `u⁶ K₁(u)` is integrable on `(0, ∞)`. -/
theorem integrableOn_moment_K1 : IntegrableOn (fun u => u ^ 6 * K1 u) (Ioi 0) :=
  Integrable.of_integral_ne_zero (by rw [moment_K1]; norm_num)

end MassGap.PurityBesselK

#print axioms MassGap.PurityBesselK.K1_nonneg
#print axioms MassGap.PurityBesselK.sqrt_one_add_sinh_sq
#print axioms MassGap.PurityBesselK.mul_exp_neg_le
#print axioms MassGap.PurityBesselK.continuous_K1_integrand
#print axioms MassGap.PurityBesselK.integrableOn_K1
#print axioms MassGap.PurityBesselK.continuous_sqrt_integrand
#print axioms MassGap.PurityBesselK.exp_sqrt_le
#print axioms MassGap.PurityBesselK.integrableOn_sqrt
#print axioms MassGap.PurityBesselK.K1_eq_sqrt
#print axioms MassGap.PurityBesselK.K1_le
#print axioms MassGap.PurityBesselK.moment_gamma
#print axioms MassGap.PurityBesselK.one_sub_tanh_sq
#print axioms MassGap.PurityBesselK.hasDerivAt_tanh
#print axioms MassGap.PurityBesselK.tendsto_tanh_atTop
#print axioms MassGap.PurityBesselK.integral_sech6
#print axioms MassGap.PurityBesselK.integral_sech6_eq_poly
#print axioms MassGap.PurityBesselK.moment_inner
#print axioms MassGap.PurityBesselK.moment_K1_sech
#print axioms MassGap.PurityBesselK.moment_K1
#print axioms MassGap.PurityBesselK.integrableOn_moment_K1
