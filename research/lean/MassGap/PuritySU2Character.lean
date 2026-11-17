import Mathlib
import MassGap.PurityCharCoeff
import MassGap.SU2DiskLaw

/-!
# MassGap.PuritySU2Character — the SU(2) character coefficients in the Weyl variable

Appendix C of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford and
S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`)
uses `a_π ≥ 0`, `|a_π| ≤ a₀` and `a₀ > 0` for `k_b = exp (b g)`, `g = Re Tr / d`. For `G = SU(2)` a
class function depends on the eigenvalue angle `θ ∈ [0, π]`, `g = cos θ`, the spin-`n/2` character
is `χ_n = sin ((n+1) θ) / sin θ = U_n(cos θ)` with `d_n = n + 1`, and Haar measure on class functions
is `(2/π) sin² θ dθ`. In `x = cos θ` this is `(2/π)(1 − x²)` against the Chebyshev measure
`Polynomial.Chebyshev.measureT` (density `(1 − x²)^{-1/2}` on `[-1, 1]`). This module works in `x`:
`g = clamp x` (equal to `x` on `[-1, 1]`, which carries `measureT`) and the weighted characters
`chi n x = (2/π)(1 − x²) U_n(x)`, so that `∫ F(x) chi n x ∂measureT` is the Haar integral of
`F χ_n` for a class function `F`.

* `integral_comp_clamp`: `∫ f (clamp x) ∂measureT = ∫ f x ∂measureT`.
* `one_sub_sq_mul_eval_U`: `(1 − x²) U_n(x) = (T_n(x) − T_{n+2}(x)) / 2`.
* `integral_chi`: `∫ chi n ∂measureT = δ_{n,0}` (orthogonality against the trivial character),
  from `Polynomial.Chebyshev.integral_eval_T_real_measureT_zero` and `_of_ne_zero`.
* `fusion`: `x U_0 = ½ U_1` and `x U_{m+1} = ½ U_{m+2} + ½ U_m` (spin `½ ⊗ j = (j+½) ⊕ (j−½)`).
* `abs_eval_U_le`: `|U_n(y)| ≤ n + 1` for `|y| ≤ 1`, by `U_{m+1} = T_{m+1} + y U_m`, `|T| ≤ 1`.
* `abs_chi_le`: `|chi n x| ≤ n + 1`.
* `coeff_nonneg`: `a_n = (1/(n+1)) ∫ e^{b x} chi n ∂measureT ≥ 0` for `b ≥ 0`, by
  `PurityCharCoeff.charCoeff_exp_nonneg`.
* `abs_coeff_le`: `|a_n| ≤ a₀`, by `PurityCharCoeff.abs_charCoeff_le`.
* `coeff_zero_pos`: `a₀ > 0`.
* `integral_suTau`: the Weyl integration formula. For continuous `f` and `τ g = ½ Re Tr g`,
  `∫ f(τ g) dg = (2/π) ∫_{-1}^{1} f(t) √(1 − t²) dt` over `SU(2)` Haar measure, from
  `SU2DiskLaw.conv_eq_ellInt` at `V = 1`, `g = diag(i, −i)` (`integral_suTau_nonneg`).
* `integral_haar`: `∫ f(τ g) dg = ∫ weight · f ∂measureT`.
* `integral_haar_U`: `∫ U_n(τ g) dg = δ_{n,0}`.
* `coeff_eq_haar`: `a_n = (1/(n+1)) ∫ e^{b τ g} U_n(τ g) dg`.
* `weightSum n z = Σ_{k=0}^{n} z^{n−k} z^{−k}`, the sum of `z^w` over the weights `n, n − 2, …, −n`;
  `eval_U_weightSum`: `U_n((z + z⁻¹)/2) = weightSum n z` for `z ≠ 0`, by `weightSum_succ` and
  `U_{n+2} = 2x U_{n+1} − U_n`.
* `det_sub_eq`: `det (z·1 − g) = z² − Tr g · z + 1`; `suTau_eq_trace`: `τ g = ½ Tr g` in `ℂ`;
  `exists_eigenvalue`: `g` has an eigenvalue.
* `eval_U_suTau_eq_weightSum`: `U_n(τ g) = weightSum n z` at every eigenvalue `z` of `g ∈ SU(2)`.

`PuritySU2SymPower.symChar_eq_eval_U` identifies `weightSum n z` with the trace of `g` on
`Sym^n ℂ²`, so `U_n(τ g)` is the spin-`n/2` character and `coeff` is the paper's `a_π` at `G = SU(2)`.
-/

namespace MassGap.PuritySU2Character

open MeasureTheory Polynomial Polynomial.Chebyshev Real

/-- The clamp to `[-1, 1]`; the identity on the support of `measureT`. -/
noncomputable abbrev clamp : ℝ → ℝ := SU2DiskLaw.clamp1

theorem abs_clamp_le (x : ℝ) : |clamp x| ≤ 1 := abs_le.2 (SU2DiskLaw.clamp1_mem x)

/-- The Weyl density `(2/π)(1 − x²)` of `SU(2)` Haar measure relative to `measureT`. -/
noncomputable def weight (x : ℝ) : ℝ := 2 / π * (1 - clamp x ^ 2)

theorem continuous_weight : Continuous weight := by
  unfold weight
  exact continuous_const.mul (continuous_const.sub (SU2DiskLaw.continuous_clamp1.pow 2))

theorem weight_nonneg (x : ℝ) : 0 ≤ weight x :=
  mul_nonneg (by positivity)
    (sub_nonneg.2 ((sq_le_one_iff_abs_le_one _).2 (abs_clamp_le x)))

theorem weight_le_one (x : ℝ) : weight x ≤ 1 :=
  mul_le_one₀ ((div_le_one pi_pos).2 (by linarith [pi_gt_three]))
    (sub_nonneg.2 ((sq_le_one_iff_abs_le_one _).2 (abs_clamp_le x)))
    (by nlinarith [sq_nonneg (clamp x)])

/-- The weighted spin-`n/2` character `(2/π)(1 − x²) U_n(x)`. -/
noncomputable def chi (n : ℕ) (x : ℝ) : ℝ := weight x * (U ℝ n).eval (clamp x)

theorem continuous_chi (n : ℕ) : Continuous (chi n) :=
  continuous_weight.mul ((U ℝ n).continuous.comp SU2DiskLaw.continuous_clamp1)

/-- `measureT` is finite. -/
theorem isFiniteMeasure_measureT : IsFiniteMeasure measureT :=
  (integrable_const_iff.1 (integrable_measureT (f := fun _ => (1 : ℝ))
    continuousOn_const)).resolve_left one_ne_zero

attribute [local instance] isFiniteMeasure_measureT

/-- Composing with the clamp does not change a `measureT` integral. -/
theorem integral_comp_clamp (f : ℝ → ℝ) : ∫ x, f (clamp x) ∂measureT = ∫ x, f x ∂measureT := by
  rw [integral_measureT_eq_integral_cos, integral_measureT_eq_integral_cos]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [SU2DiskLaw.clamp1_of_mem ⟨neg_one_le_cos θ, cos_le_one θ⟩]

/-- `(1 − x²) U_n(x) = (T_n(x) − T_{n+2}(x)) / 2`. -/
theorem one_sub_sq_mul_eval_U (n : ℤ) (x : ℝ) :
    (1 - x ^ 2) * (U ℝ n).eval x = ((T ℝ n).eval x - (T ℝ (n + 2)).eval x) / 2 := by
  have h1 := congrArg (eval x) (one_sub_X_sq_mul_U_eq_pol_in_T ℝ n)
  have h2 := congrArg (eval x) (T_add_two ℝ n)
  simp only [eval_mul, eval_sub, eval_one, eval_pow, eval_X, eval_ofNat] at h1 h2
  linear_combination h1 - h2 / 2

/-- Orthogonality against the trivial character: `∫ chi n ∂measureT = δ_{n,0}`. -/
theorem integral_chi (n : ℕ) : ∫ x, chi n x ∂measureT = if n = 0 then 1 else 0 := by
  have hT : ∀ k : ℤ, Integrable (fun x => (T ℝ k).eval x) measureT := fun k =>
    integrable_measureT (T ℝ k).continuous.continuousOn
  have he : (fun x => chi n x) =
      fun x => (fun y => 2 / π * ((1 - y ^ 2) * (U ℝ n).eval y)) (clamp x) := by
    funext x
    simp only [chi, weight]
    ring
  rw [he, integral_comp_clamp (fun y => 2 / π * ((1 - y ^ 2) * (U ℝ n).eval y))]
  simp only [one_sub_sq_mul_eval_U]
  rw [integral_const_mul, integral_div, integral_sub (hT n) (hT (n + 2)),
    integral_eval_T_real_measureT_of_ne_zero (n := (n : ℤ) + 2) (by omega)]
  split_ifs with h
  · subst h
    simp only [Nat.cast_zero, integral_eval_T_real_measureT_zero, sub_zero]
    field_simp
  · rw [integral_eval_T_real_measureT_of_ne_zero (by exact_mod_cast h)]
    simp

/-- The fusion rule `x U_0 = ½ U_1`, `x U_{m+1} = ½ U_{m+2} + ½ U_m`, for the weighted characters. -/
theorem fusion (n : ℕ) : ∃ (s : Finset ℕ) (N : ℕ → ℝ), (∀ σ ∈ s, 0 ≤ N σ) ∧
    ∀ x, clamp x * chi n x = ∑ σ ∈ s, N σ * chi σ x := by
  rcases n with _ | m
  · refine ⟨{1}, fun _ => 1 / 2, fun _ _ => by norm_num, fun x => ?_⟩
    simp only [Finset.sum_singleton, chi, Nat.cast_zero, Nat.cast_one, U_zero, U_one, eval_one,
      eval_mul, eval_X, eval_ofNat]
    ring
  · refine ⟨{m + 2, m}, fun _ => 1 / 2, fun _ _ => by norm_num, fun x => ?_⟩
    rw [Finset.sum_pair (by omega)]
    have h := congrArg (eval (clamp x)) (U_add_two ℝ (m : ℤ))
    simp only [eval_mul, eval_sub, eval_X, eval_ofNat] at h
    simp only [chi]
    push_cast
    linear_combination (-weight x / 2) * h

/-- `|U_n(y)| ≤ n + 1` for `|y| ≤ 1`. -/
theorem abs_eval_U_le (n : ℕ) {y : ℝ} (hy : |y| ≤ 1) : |(U ℝ n).eval y| ≤ n + 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h := congrArg (eval y) (T_eq_U_sub_X_mul_U ℝ ((m : ℤ) + 1))
    simp only [eval_sub, eval_mul, eval_X, add_sub_cancel_right] at h
    have hT := abs_eval_T_real_le_one ((m : ℤ) + 1) hy
    have hyU : |y * (U ℝ m).eval y| ≤ m + 1 := by
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) hy).trans ih
    have hU : (U ℝ ((m + 1 : ℕ) : ℤ)).eval y = (T ℝ ((m : ℤ) + 1)).eval y + y * (U ℝ m).eval y := by
      push_cast
      linarith
    rw [hU]
    push_cast
    linarith [abs_add_le ((T ℝ ((m : ℤ) + 1)).eval y) (y * (U ℝ m).eval y)]

theorem abs_chi_le (n : ℕ) (x : ℝ) : |chi n x| ≤ n + 1 := by
  rw [chi, abs_mul, abs_of_nonneg (weight_nonneg x)]
  exact (mul_le_of_le_one_left (abs_nonneg _) (weight_le_one x)).trans
    (abs_eval_U_le n (abs_clamp_le x))

/-- The SU(2) character coefficient `a_n = (1/(n+1)) ∫ e^{b x} chi n ∂measureT`. -/
noncomputable def coeff (b : ℝ) (n : ℕ) : ℝ :=
  MKBound.charCoeff measureT chi (fun n => (n : ℝ) + 1) (fun x => Real.exp (b * clamp x)) n

/-- `a_n ≥ 0` for `b ≥ 0`. -/
theorem coeff_nonneg {b : ℝ} (hb : 0 ≤ b) (n : ℕ) : 0 ≤ coeff b n :=
  PurityCharCoeff.charCoeff_exp_nonneg SU2DiskLaw.continuous_clamp1.measurable abs_clamp_le
    (fun n => (continuous_chi n).measurable) (B := fun n => (n : ℝ) + 1) abs_chi_le fusion
    (fun n => by rw [integral_chi]; split_ifs <;> norm_num) hb _ (by positivity)

theorem coeff_zero_eq (b : ℝ) :
    coeff b 0 = ∫ x, Real.exp (b * clamp x) * weight x ∂measureT := by
  simp only [coeff, MKBound.charCoeff, chi, Nat.cast_zero, U_zero, eval_one, mul_one, zero_add,
    div_one]

/-- `|a_n| ≤ a₀`. -/
theorem abs_coeff_le (b : ℝ) (n : ℕ) : |coeff b n| ≤ coeff b 0 := by
  have hk : Integrable (fun x => Real.exp (b * clamp x) * weight x) measureT :=
    integrable_measureT
      (((continuous_const.mul SU2DiskLaw.continuous_clamp1).rexp).mul continuous_weight).continuousOn
  have h := PurityCharCoeff.abs_charCoeff_le (μ := measureT)
    (χ := fun (n : ℕ) x => (U ℝ n).eval (clamp x)) (d := fun n : ℕ => (n : ℝ) + 1) (j := n)
    (fun x => mul_nonneg (Real.exp_pos _).le (weight_nonneg x)) hk (by positivity)
    ((U ℝ n).continuous.comp SU2DiskLaw.continuous_clamp1).aestronglyMeasurable
    (fun x => abs_eval_U_le n (abs_clamp_le x))
  have e1 : coeff b n = MKBound.charCoeff measureT (fun (n : ℕ) x => (U ℝ n).eval (clamp x))
      (fun n : ℕ => (n : ℝ) + 1) (fun x => Real.exp (b * clamp x) * weight x) n := by
    simp only [coeff, MKBound.charCoeff]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [chi]
    ring
  rw [e1, coeff_zero_eq]
  exact h

/-- `a₀ > 0`. -/
theorem coeff_zero_pos (b : ℝ) : 0 < coeff b 0 := by
  rw [coeff_zero_eq, integral_measureT_eq_integral_cos]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (((continuous_const.mul (SU2DiskLaw.continuous_clamp1.comp continuous_cos)).rexp.mul
      (continuous_weight.comp continuous_cos)).intervalIntegrable _ _) (fun θ hθ => ?_) pi_pos
  have hs := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  refine mul_pos (Real.exp_pos _) ?_
  simp only [weight, SU2DiskLaw.clamp1_of_mem ⟨neg_one_le_cos θ, cos_le_one θ⟩]
  rw [← sin_sq]
  positivity

/-! ## The Weyl integration formula for `SU(2)` -/

open MassGap.SUN (SU)
open MassGap.CompactGauge (probHaar)
open MassGap.ChainCoarseSeed (suTau suTau_mem)

/-- For continuous `u ≥ 0`, `∫ u(τ g) dg = (2/π) ∫_{-1}^{1} u(t) √(1 − t²) dt`, from
`SU2DiskLaw.conv_eq_ellInt` with `V = 1` at `g = diag(i, −i)`. -/
theorem integral_suTau_nonneg (u : ℝ → ℝ) (hu : Continuous u) (hu0 : ∀ t, 0 ≤ u t) :
    ∫ g, u (suTau g) ∂probHaar (SU 2) = 2 / π * ∫ t in (-1)..1, u t * √(1 - t ^ 2) := by
  have hg : suTau (SU2DiskLaw.dmat (π / 2)) ∈ Set.Ioo (-1 : ℝ) 1 := by
    rw [SU2DiskLaw.suTau_dmat, cos_pi_div_two]; norm_num
  have h := SU2DiskLaw.conv_eq_ellInt u (fun _ => 1) hu continuous_const hu0
    (fun _ => zero_le_one) _ hg
  rw [SU2DiskLaw.suTau_dmat, cos_pi_div_two, arccos_zero, sin_pi_div_two, mul_one π] at h
  have hl : ElectricStep.conv (u ∘ suTau) ((fun _ => (1 : ℝ)) ∘ suTau) (SU2DiskLaw.dmat (π / 2))
      = ∫ g, u (suTau g) ∂probHaar (SU 2) := by
    unfold ElectricStep.conv
    simp only [Function.comp_apply, mul_one]
  have key : ConvolutionTransfer.ellInt (π / 2) (fun t y => u t * (fun _ => (1 : ℝ)) y)
      = 2 * ∫ t in (-1)..1, u t * √(1 - t ^ 2) := by
    unfold ConvolutionTransfer.ellInt
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [ConvolutionTransfer.ellLo, ConvolutionTransfer.ellHi, cos_pi_div_two,
      sin_pi_div_two, mul_zero, mul_one, zero_sub, zero_add, intervalIntegral.integral_const,
      smul_eq_mul]
    ring
  rw [← hl, h, key]
  ring

/-- **The Weyl integration formula for `SU(2)`.** For continuous `f`,
`∫ f(τ g) dg = (2/π) ∫_{-1}^{1} f(t) √(1 − t²) dt`. -/
theorem integral_suTau (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ g, f (suTau g) ∂probHaar (SU 2) = 2 / π * ∫ t in (-1)..1, f t * √(1 - t ^ 2) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hf.continuousOn
  set u : ℝ → ℝ := fun t => f (clamp t) + C with hudef
  have huc : Continuous u := (hf.comp SU2DiskLaw.continuous_clamp1).add continuous_const
  have hu0 : ∀ t, 0 ≤ u t := fun t => by
    have h := hC _ (SU2DiskLaw.clamp1_mem t)
    rw [Real.norm_eq_abs] at h
    simp only [hudef]
    linarith [neg_abs_le (f (clamp t))]
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨by norm_num, by norm_num⟩)
  have h1 := integral_suTau_nonneg u huc hu0
  have h2 := integral_suTau_nonneg (fun _ => C) continuous_const (fun _ => hC0)
  have hint : ∀ {F : SU 2 → ℝ}, Continuous F → Integrable F (probHaar (SU 2)) := fun {F} hF => by
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
    exact Integrable.of_bound hF.aestronglyMeasurable B (ae_of_all _ fun x => hB x (Set.mem_univ x))
  have eG : ∫ g, f (suTau g) ∂probHaar (SU 2)
      = ∫ g, u (suTau g) ∂probHaar (SU 2) - ∫ _g, C ∂probHaar (SU 2) := by
    rw [← integral_sub (hint (F := fun g => u (suTau g)) (huc.comp SU2DiskLaw.continuous_suTau))
      (hint (F := fun _ => C) continuous_const)]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    simp only [hudef, SU2DiskLaw.clamp1_of_mem (suTau_mem g)]
    ring
  have eI : ∫ t in (-1)..1, f t * √(1 - t ^ 2)
      = (∫ t in (-1)..1, u t * √(1 - t ^ 2)) - ∫ t in (-1)..1, C * √(1 - t ^ 2) := by
    have hs : Continuous fun t : ℝ => √(1 - t ^ 2) := by fun_prop
    rw [← intervalIntegral.integral_sub (f := fun t => u t * √(1 - t ^ 2))
      (g := fun t => C * √(1 - t ^ 2)) ((huc.mul hs).intervalIntegrable _ _)
      ((continuous_const.mul hs).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by norm_num)] at ht
    simp only [hudef, SU2DiskLaw.clamp1_of_mem ht]
    ring
  rw [eG, eI, h1, h2]
  ring

/-- **SU(2) Haar measure in the Weyl variable.** For continuous `f`,
`∫ f(τ g) dg = ∫ weight · f ∂measureT`, `τ g = ½ Re Tr g`. -/
theorem integral_haar (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ g, f (suTau g) ∂probHaar (SU 2) = ∫ x, weight x * f x ∂measureT := by
  rw [integral_suTau f hf, integral_measureT, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le (by norm_num)] at hx
  have h0 : (1 - x ^ 2) * √(1 - x ^ 2)⁻¹ = √(1 - x ^ 2) := by
    simp only [Real.sqrt_inv, ← div_eq_mul_inv, Real.div_sqrt]
  simp only [weight, SU2DiskLaw.clamp1_of_mem hx]
  linear_combination (-(2 / π * f x)) * h0

/-- `∫ U_n(τ g) dg = δ_{n,0}` on `SU(2)`. -/
theorem integral_haar_U (n : ℕ) :
    ∫ g, (U ℝ n).eval (suTau g) ∂probHaar (SU 2) = if n = 0 then 1 else 0 := by
  have e : ∫ g, (U ℝ n).eval (suTau g) ∂probHaar (SU 2)
      = ∫ g, (fun y => (U ℝ n).eval (clamp y)) (suTau g) ∂probHaar (SU 2) := by
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    simp only [SU2DiskLaw.clamp1_of_mem (suTau_mem g)]
  rw [e, integral_haar (fun y => (U ℝ n).eval (clamp y))
    ((U ℝ n).continuous.comp SU2DiskLaw.continuous_clamp1)]
  exact integral_chi n

/-- The coefficient as an `SU(2)` Haar integral:
`a_n = (1/(n+1)) ∫ e^{b τ g} U_n(τ g) dg`. -/
theorem coeff_eq_haar (b : ℝ) (n : ℕ) :
    coeff b n = (∫ g, Real.exp (b * suTau g) * (U ℝ n).eval (suTau g) ∂probHaar (SU 2))
      / ((n : ℝ) + 1) := by
  have e : ∫ g, Real.exp (b * suTau g) * (U ℝ n).eval (suTau g) ∂probHaar (SU 2)
      = ∫ g, (fun y => Real.exp (b * clamp y) * (U ℝ n).eval (clamp y)) (suTau g)
          ∂probHaar (SU 2) := by
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    simp only [SU2DiskLaw.clamp1_of_mem (suTau_mem g)]
  rw [e, integral_haar (fun y => Real.exp (b * clamp y) * (U ℝ n).eval (clamp y))
    (((continuous_const.mul SU2DiskLaw.continuous_clamp1).rexp).mul
    ((U ℝ n).continuous.comp SU2DiskLaw.continuous_clamp1))]
  simp only [coeff, MKBound.charCoeff, chi]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  ring

/-! ## `U_n(τ g)` as the spin-`n/2` weight sum -/

/-- The weight sum of the spin-`n/2` representation at `z`: `Σ_{k=0}^{n} z^{n−k} z^{−k}`, the sum of
`z^w` over the weights `w = n, n − 2, …, −n`. -/
noncomputable def weightSum (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), z ^ (n - k) * z⁻¹ ^ k

theorem weightSum_zero (z : ℂ) : weightSum 0 z = 1 := by simp [weightSum]

theorem weightSum_succ (n : ℕ) (z : ℂ) :
    weightSum (n + 1) z = z ^ (n + 1) + z⁻¹ * weightSum n z := by
  unfold weightSum
  rw [Finset.sum_range_succ', Finset.mul_sum, add_comm (z ^ (n + 1))]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.add_sub_add_right]
    ring
  · simp

/-- `U_n((z + z⁻¹)/2) = Σ_{k=0}^{n} z^{n−k} z^{−k}` for `z ≠ 0`. -/
theorem eval_U_weightSum {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    (U ℂ n).eval ((z + z⁻¹) / 2) = weightSum n z := by
  have key : ∀ m : ℕ, (U ℂ m).eval ((z + z⁻¹) / 2) = weightSum m z ∧
      (U ℂ (m + 1 : ℕ)).eval ((z + z⁻¹) / 2) = weightSum (m + 1) z := by
    intro m
    induction m with
    | zero =>
      refine ⟨by simp [weightSum_zero], ?_⟩
      rw [weightSum_succ, weightSum_zero]
      simp only [zero_add, Nat.cast_one, U_one, eval_mul, eval_ofNat, eval_X]
      ring
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      have e1 : ((m + 1 + 1 : ℕ) : ℤ) = (m : ℤ) + 2 := by push_cast; ring
      have e2 : (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [e1, U_add_two]
      simp only [eval_sub, eval_mul, eval_ofNat, eval_X]
      rw [e2, ih.2, ih.1, weightSum_succ (m + 1), weightSum_succ m]
      field_simp
      ring
  exact (key n).1

/-- `det (z·1 − g) = z² − Tr g · z + 1` on `SU(2)`. -/
theorem det_sub_eq (g : SU 2) (z : ℂ) :
    (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) - (g : Matrix (Fin 2) (Fin 2) ℂ)).det
      = z ^ 2 - Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) * z + 1 := by
  have hd : (g : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := (Matrix.mem_specialUnitaryGroup_iff.1 g.2).2
  rw [Matrix.det_fin_two] at hd ⊢
  rw [Matrix.trace_fin_two]
  simp
  linear_combination hd

/-- `τ g = ½ Tr g` in `ℂ`: the trace of `g ∈ SU(2)` is real. -/
theorem suTau_eq_trace (g : SU 2) :
    (suTau g : ℂ) = Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) / 2 := by
  have h := Complex.conj_eq_iff_re.1 (MassGap.SUN.su2_trace_real g)
  have hre : suTau g = (Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)).re / 2 := by
    simp only [ChainCoarseSeed.suTau, WilsonAction.wilsonDensity]
    push_cast
    ring
  rw [hre]
  push_cast
  rw [h]

/-- Every `g ∈ SU(2)` has an eigenvalue: `det (z·1 − g) = 0` for some `z`. -/
theorem exists_eigenvalue (g : SU 2) :
    ∃ z : ℂ, (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) - (g : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 := by
  obtain ⟨z, hz⟩ := exists_quadratic_eq_zero (K := ℂ) (a := 1)
    (b := -Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)) (c := 1) one_ne_zero
    (IsAlgClosed.exists_eq_mul_self _)
  exact ⟨z, by rw [det_sub_eq]; linear_combination hz⟩

/-- `U_n(τ g)` is the spin-`n/2` weight sum at an eigenvalue `z` of `g ∈ SU(2)`:
`U_n(τ g) = Σ_{k=0}^{n} z^{n−k} z^{−k}`. -/
theorem eval_U_suTau_eq_weightSum (g : SU 2) {z : ℂ}
    (hz : (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) - (g : Matrix (Fin 2) (Fin 2) ℂ)).det = 0)
    (n : ℕ) : (((U ℝ n).eval (suTau g) : ℝ) : ℂ) = weightSum n z := by
  rw [det_sub_eq] at hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  have hinv : z⁻¹ = Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) - z :=
    inv_eq_of_mul_eq_one_right (by linear_combination -hz)
  have ht : Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) = z + z⁻¹ := by
    rw [hinv]
    ring
  rw [complex_ofReal_eval_U, suTau_eq_trace, ht]
  exact eval_U_weightSum hz0 n

end MassGap.PuritySU2Character

#print axioms MassGap.PuritySU2Character.integral_comp_clamp
#print axioms MassGap.PuritySU2Character.one_sub_sq_mul_eval_U
#print axioms MassGap.PuritySU2Character.integral_chi
#print axioms MassGap.PuritySU2Character.fusion
#print axioms MassGap.PuritySU2Character.abs_eval_U_le
#print axioms MassGap.PuritySU2Character.abs_chi_le
#print axioms MassGap.PuritySU2Character.coeff_nonneg
#print axioms MassGap.PuritySU2Character.abs_coeff_le
#print axioms MassGap.PuritySU2Character.coeff_zero_pos
#print axioms MassGap.PuritySU2Character.integral_suTau_nonneg
#print axioms MassGap.PuritySU2Character.integral_suTau
#print axioms MassGap.PuritySU2Character.integral_haar
#print axioms MassGap.PuritySU2Character.integral_haar_U
#print axioms MassGap.PuritySU2Character.coeff_eq_haar
#print axioms MassGap.PuritySU2Character.weightSum_zero
#print axioms MassGap.PuritySU2Character.weightSum_succ
#print axioms MassGap.PuritySU2Character.eval_U_weightSum
#print axioms MassGap.PuritySU2Character.det_sub_eq
#print axioms MassGap.PuritySU2Character.suTau_eq_trace
#print axioms MassGap.PuritySU2Character.exists_eigenvalue
#print axioms MassGap.PuritySU2Character.eval_U_suTau_eq_weightSum
