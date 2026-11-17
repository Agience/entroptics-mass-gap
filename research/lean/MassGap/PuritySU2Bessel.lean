import MassGap.PuritySU2Character

/-!
# MassGap.PuritySU2Bessel — the SU(2) character coefficients as modified Bessel functions

The SU(2) Bessel form of Appendix C of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood,
T. Romanov, I. J. Sessford and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak
Coupling* (research draft, 15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit
8e01510, `Paper-2/Paper-2.pdf`): `a_j / a₀ = I_{2j+1}(b) / I₁(b)` for the spin-`j` coefficient,
here at `n = 2j` for `PuritySU2Character.coeff`.

* `besselI n b = (1/π) ∫₀^π e^{b cos θ} cos (nθ) dθ`, the modified Bessel function of the first
  kind of order `n ∈ ℕ` in its integral form (DLMF 10.32.3).
* `coeff_mul`: `(n + 1) a_n = I_n(b) − I_{n+2}(b)`, from `x = cos θ`, `T_n(cos θ) = cos (nθ)` and
  `(1 − x²) U_n = (T_n − T_{n+2})/2`.
* `mul_besselI_sub`: `b (I_n(b) − I_{n+2}(b)) = 2(n + 1) I_{n+1}(b)`, by
  `cos (nθ) − cos ((n+2)θ) = 2 sin θ sin ((n+1)θ)` and integration by parts.
* `coeff_eq_besselI`: `a_n = 2 I_{n+1}(b) / b` for `b ≠ 0`.
* `besselI_one_ne_zero`: `I₁(b) ≠ 0` for `b ≠ 0`.
* `coeff_div_coeff_zero`: `a_n / a₀ = I_{n+1}(b) / I₁(b)` for `b ≠ 0`.
-/

namespace MassGap.PuritySU2Bessel

open MeasureTheory Polynomial Polynomial.Chebyshev Real MassGap.PuritySU2Character

/-- The modified Bessel function of the first kind of order `n ∈ ℕ` (DLMF 10.32.3),
`I_n(b) = (1/π) ∫₀^π e^{b cos θ} cos (nθ) dθ`. -/
noncomputable def besselI (n : ℕ) (b : ℝ) : ℝ :=
  1 / π * ∫ θ in (0 : ℝ)..π, exp (b * cos θ) * cos (n * θ)

/-- `(n + 1) a_n = I_n(b) − I_{n+2}(b)`. -/
theorem coeff_mul (b : ℝ) (n : ℕ) :
    ((n : ℝ) + 1) * coeff b n = besselI n b - besselI (n + 2) b := by
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hi : ∀ m : ℕ, IntervalIntegrable (fun θ => exp (b * cos θ) * cos (m * θ)) volume 0 π :=
    fun m => (by fun_prop : Continuous fun θ => exp (b * cos θ) * cos (m * θ)).intervalIntegrable _ _
  calc ((n : ℝ) + 1) * coeff b n
      = ∫ θ in (0 : ℝ)..π, exp (b * clamp (cos θ)) * chi n (cos θ) := by
        simp only [PuritySU2Character.coeff, MKBound.charCoeff]
        rw [mul_div_cancel₀ _ hn, integral_measureT_eq_integral_cos]
    _ = ∫ θ in (0 : ℝ)..π, 1 / π * (exp (b * cos θ) * cos (n * θ)
          - exp (b * cos θ) * cos (((n + 2 : ℕ) : ℝ) * θ)) := by
        refine intervalIntegral.integral_congr fun θ _ => ?_
        have hc := SU2DiskLaw.clamp1_of_mem ⟨neg_one_le_cos θ, cos_le_one θ⟩
        have h := one_sub_sq_mul_eval_U n (cos θ)
        rw [T_real_cos, T_real_cos] at h
        simp only [chi, weight, clamp, hc]
        push_cast at h ⊢
        linear_combination (2 / π * exp (b * cos θ)) * h
    _ = besselI n b - besselI (n + 2) b := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hi n) (hi (n + 2)),
          besselI, besselI, mul_sub]

/-- `b (I_n(b) − I_{n+2}(b)) = 2(n + 1) I_{n+1}(b)`. -/
theorem mul_besselI_sub (n : ℕ) (b : ℝ) :
    b * (besselI n b - besselI (n + 2) b) = 2 * ((n : ℝ) + 1) * besselI (n + 1) b := by
  set c : ℝ := (n : ℝ) + 1 with hcdef
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := π)
    (u := fun θ => sin (c * θ)) (u' := fun θ => cos (c * θ) * (c * 1))
    (v := fun θ => exp (b * cos θ)) (v' := fun θ => exp (b * cos θ) * (b * -sin θ))
    (fun θ _ => ((hasDerivAt_id' θ).const_mul c).sin)
    (fun θ _ => ((hasDerivAt_cos θ).const_mul b).exp)
    ((by fun_prop : Continuous fun θ => cos (c * θ) * (c * 1)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun θ => exp (b * cos θ) * (b * -sin θ)).intervalIntegrable _ _)
  have hπ : sin (c * π) = 0 := by
    rw [hcdef]; exact_mod_cast sin_nat_mul_pi (n + 1)
  simp only [hπ, mul_zero, sin_zero, zero_mul, sub_zero, zero_sub] at hibp
  have hi : ∀ m : ℝ, IntervalIntegrable (fun θ => exp (b * cos θ) * cos (m * θ)) volume 0 π :=
    fun m => (by fun_prop : Continuous fun θ => exp (b * cos θ) * cos (m * θ)).intervalIntegrable _ _
  have key : b * ((∫ θ in (0 : ℝ)..π, exp (b * cos θ) * cos ((n : ℝ) * θ))
      - ∫ θ in (0 : ℝ)..π, exp (b * cos θ) * cos (((n + 2 : ℕ) : ℝ) * θ))
      = -2 * ∫ θ in (0 : ℝ)..π, sin (c * θ) * (exp (b * cos θ) * (b * -sin θ)) := by
    rw [← intervalIntegral.integral_sub (hi _) (hi _), ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have h1 : cos ((n : ℝ) * θ) = cos (c * θ - θ) := by rw [hcdef]; congr 1; ring
    have h2 : cos (((n + 2 : ℕ) : ℝ) * θ) = cos (c * θ + θ) := by
      rw [hcdef]; push_cast; congr 1; ring
    simp only [h1, h2, cos_sub, cos_add]
    ring
  have hJ : ∫ θ in (0 : ℝ)..π, cos (c * θ) * (c * 1) * exp (b * cos θ)
      = c * ∫ θ in (0 : ℝ)..π, exp (b * cos θ) * cos (((n + 1 : ℕ) : ℝ) * θ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hcdef]
    push_cast
    ring
  unfold besselI
  calc b * (1 / π * (∫ θ in (0 : ℝ)..π, exp (b * cos θ) * cos ((n : ℝ) * θ))
        - 1 / π * ∫ θ in (0 : ℝ)..π, exp (b * cos θ) * cos (((n + 2 : ℕ) : ℝ) * θ))
      = 1 / π * (b * ((∫ θ in (0 : ℝ)..π, exp (b * cos θ) * cos ((n : ℝ) * θ))
        - ∫ θ in (0 : ℝ)..π, exp (b * cos θ) * cos (((n + 2 : ℕ) : ℝ) * θ))) := by ring
    _ = 2 * c * (1 / π * ∫ θ in (0 : ℝ)..π, exp (b * cos θ) * cos (((n + 1 : ℕ) : ℝ) * θ)) := by
        rw [key, hibp, hJ]; ring

/-- `a_n = 2 I_{n+1}(b) / b` for `b ≠ 0`. -/
theorem coeff_eq_besselI {b : ℝ} (hb : b ≠ 0) (n : ℕ) :
    coeff b n = 2 * besselI (n + 1) b / b := by
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [eq_div_iff hb]
  apply mul_left_cancel₀ hn
  linear_combination b * coeff_mul b n + mul_besselI_sub n b

/-- `I₁(b) ≠ 0` for `b ≠ 0`: `a₀ = 2 I₁(b)/b > 0`. -/
theorem besselI_one_ne_zero {b : ℝ} (hb : b ≠ 0) : besselI 1 b ≠ 0 := by
  intro h
  have h0 := coeff_zero_pos b
  rw [coeff_eq_besselI hb 0] at h0
  norm_num [h] at h0

/-- The SU(2) Bessel form `a_n / a₀ = I_{n+1}(b) / I₁(b)` for `b ≠ 0`. -/
theorem coeff_div_coeff_zero {b : ℝ} (hb : b ≠ 0) (n : ℕ) :
    coeff b n / coeff b 0 = besselI (n + 1) b / besselI 1 b := by
  have h1 := besselI_one_ne_zero hb
  rw [coeff_eq_besselI hb, coeff_eq_besselI hb]
  norm_num
  field_simp

end MassGap.PuritySU2Bessel

#print axioms MassGap.PuritySU2Bessel.coeff_mul
#print axioms MassGap.PuritySU2Bessel.mul_besselI_sub
#print axioms MassGap.PuritySU2Bessel.coeff_eq_besselI
#print axioms MassGap.PuritySU2Bessel.besselI_one_ne_zero
#print axioms MassGap.PuritySU2Bessel.coeff_div_coeff_zero
