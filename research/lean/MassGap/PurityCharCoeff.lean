import Mathlib
import MassGap.MKBound
import MassGap.PurityKernelPositive

/-!
# MassGap.PurityCharCoeff — the temporal character coefficients are nonnegative and at most `a₀`

Appendix C of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford and
S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`)
writes `k_b = exp (b g)` with `g = Re Tr / d`, `a_π = (1/d_π) ∫ k_b χ_π` and `a₀ = ∫ k_b`, and uses
`a_π ≥ 0` (the expansion of `k_b` is a positive sum of characters) and `a_π ≤ a₀` (`|χ_π| ≤ d_π`).
On a finite measure space, with real character functions `χ_j`, `|g| ≤ 1`, `|χ_j| ≤ B_j`.
`χ_j` stands for `Re χ_π`: `k_b(g⁻¹) = k_b(g)` and inversion invariance of Haar measure give
`∫ k_b Im χ_π = 0`, so the paper's `a_π` is real and equals `charCoeff` at `Re χ_π`; the fusion rule
for `χ_π` passes to real parts since `g` and `N_σ` are real.


* `moment_nonneg`: fusion positivity, `g χ_j = Σ_{σ∈s} N_σ χ_σ` with `N_σ ≥ 0` for every `j`, and
  `∫ χ_σ ≥ 0` for every `σ` give `∫ g^n χ_j ≥ 0` for all `n`, by induction on `n`.
* `integral_exp_mul_nonneg_of_moment`: for `b ≥ 0` and `∫ gⁿ χ ≥ 0` at every `n`,
  `∫ e^{b g} χ ≥ 0`; the truncated exponential `PurityKernelPositive.expTrunc` expands into
  `Σ_{n<N} bⁿ/n! ∫ gⁿ χ ≥ 0`, and dominated convergence with bound `e^b B` passes to `N → ∞`.
* `integral_exp_mul_nonneg`: `∫ e^{b g} χ_j ≥ 0` under fusion positivity.
* `charCoeff_exp_nonneg`: `a_j = MKBound.charCoeff μ χ d (e^{b g}) j ≥ 0` for `d_j > 0`.
* `abs_charCoeff_le`: for `k ≥ 0` integrable and `|χ_j| ≤ d_j`, `|a_j| ≤ ∫ k`.
* `a0_pos`: `a₀ = ∫ e^{b g} > 0` on a nonzero finite measure.

The fusion rule for a compact group (the tensor product of the defining representation, or its
conjugate, with an irreducible is a direct sum of irreducibles) and `∫ χ_σ ≥ 0` (from orthogonality,
`∫ χ_σ = δ_{σ,0}`) enter as the hypotheses `hfus`, `h0` of `moment_nonneg`. `PurityRepCharacter` proves the moment
positivity for the characters `Re Tr σ` of every continuous representation of a compact gauge group
without them.
-/

namespace MassGap.PurityCharCoeff

open MeasureTheory Filter Topology MassGap.PurityKernelPositive

variable {G J : Type*} [MeasurableSpace G]

/-- The moments `gⁿ χ_j` are integrable for `|g| ≤ 1`, `|χ_j| ≤ B_j`. -/
theorem integrable_pow_mul {μ : Measure G} [IsFiniteMeasure μ] {g : G → ℝ} {χ : J → G → ℝ}
    (hg : Measurable g) (hgb : ∀ U, |g U| ≤ 1) (hχ : ∀ j, Measurable (χ j)) {B : J → ℝ}
    (hχb : ∀ j U, |χ j U| ≤ B j) (n : ℕ) (j : J) :
    Integrable (fun U => g U ^ n * χ j U) μ :=
  integrable_of_abs_bound ((hg.pow_const n).mul (hχ j)) fun U => by
    rw [abs_mul, abs_pow]
    exact (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) (hgb U))).trans
      (hχb j U)

/-- Fusion positivity gives nonnegative moments: if `g χ_j = Σ_{σ∈s} N_σ χ_σ` with `N_σ ≥ 0` for
every `j` and `∫ χ_σ ≥ 0` for every `σ`, then `∫ gⁿ χ_j ≥ 0`. -/
theorem moment_nonneg {μ : Measure G} [IsFiniteMeasure μ] {g : G → ℝ} {χ : J → G → ℝ}
    (hg : Measurable g) (hgb : ∀ U, |g U| ≤ 1) (hχ : ∀ j, Measurable (χ j)) {B : J → ℝ}
    (hχb : ∀ j U, |χ j U| ≤ B j)
    (hfus : ∀ j, ∃ (s : Finset J) (N : J → ℝ), (∀ σ ∈ s, 0 ≤ N σ) ∧
      ∀ U, g U * χ j U = ∑ σ ∈ s, N σ * χ σ U)
    (h0 : ∀ j, 0 ≤ ∫ U, χ j U ∂μ) (n : ℕ) (j : J) : 0 ≤ ∫ U, g U ^ n * χ j U ∂μ := by
  induction n generalizing j with
  | zero => simpa using h0 j
  | succ n ih =>
    obtain ⟨s, N, hN, hgχ⟩ := hfus j
    have he : (fun U => g U ^ (n + 1) * χ j U) =
        fun U => ∑ σ ∈ s, N σ * (g U ^ n * χ σ U) := by
      funext U
      rw [pow_succ, mul_assoc, hgχ, Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => by ring
    rw [he, integral_finsetSum _ fun σ _ =>
      (integrable_pow_mul hg hgb hχ hχb n σ).const_mul _]
    exact Finset.sum_nonneg fun σ hσ => by
      rw [integral_const_mul]
      exact mul_nonneg (hN σ hσ) (ih σ)

/-- `∫ e^{b g} χ ≥ 0` for `b ≥ 0` when every moment `∫ gⁿ χ` is nonnegative. -/
theorem integral_exp_mul_nonneg_of_moment {μ : Measure G} [IsFiniteMeasure μ] {g χ : G → ℝ}
    (hg : Measurable g) (hgb : ∀ U, |g U| ≤ 1) (hχ : Measurable χ) {B : ℝ}
    (hχb : ∀ U, |χ U| ≤ B) (hmom : ∀ n : ℕ, 0 ≤ ∫ U, g U ^ n * χ U ∂μ) {b : ℝ} (hb : 0 ≤ b) :
    0 ≤ ∫ U, Real.exp (b * g U) * χ U ∂μ := by
  have hint : ∀ n : ℕ, Integrable (fun U => g U ^ n * χ U) μ := fun n =>
    integrable_pow_mul (J := Unit) (χ := fun _ => χ) hg hgb (fun _ => hχ) (B := fun _ => B)
      (fun _ => hχb) n ()
  have hlim : Tendsto (fun N => ∫ U, expTrunc N (b * g U) * χ U ∂μ) atTop
      (𝓝 (∫ U, Real.exp (b * g U) * χ U ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Real.exp b * B)
      (fun N => (((continuous_expTrunc N).measurable.comp (hg.const_mul b)).mul
        hχ).aestronglyMeasurable) (integrable_const _)
      (fun N => Eventually.of_forall fun U => ?_)
      (Eventually.of_forall fun U => (tendsto_expTrunc _).mul_const _)
    have hbg : |b * g U| ≤ b := by
      rw [abs_mul, abs_of_nonneg hb]
      exact mul_le_of_le_one_right hb (hgb U)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul ((abs_expTrunc_le N _).trans (Real.exp_le_exp.2 hbg)) (hχb U)
      (abs_nonneg _) (Real.exp_pos _).le
  refine ge_of_tendsto' hlim fun N => ?_
  have he : (fun U => expTrunc N (b * g U) * χ U) =
      fun U => ∑ n ∈ Finset.range N, b ^ n / (n.factorial : ℝ) * (g U ^ n * χ U) := by
    funext U
    simp only [expTrunc, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by rw [mul_pow]; ring
  rw [he, integral_finsetSum _ fun n _ => (hint n).const_mul _]
  exact Finset.sum_nonneg fun n _ => by
    rw [integral_const_mul]
    exact mul_nonneg (by positivity) (hmom n)

/-- `∫ e^{b g} χ_j ≥ 0` for `b ≥ 0` under fusion positivity. -/
theorem integral_exp_mul_nonneg {μ : Measure G} [IsFiniteMeasure μ] {g : G → ℝ} {χ : J → G → ℝ}
    (hg : Measurable g) (hgb : ∀ U, |g U| ≤ 1) (hχ : ∀ j, Measurable (χ j)) {B : J → ℝ}
    (hχb : ∀ j U, |χ j U| ≤ B j)
    (hfus : ∀ j, ∃ (s : Finset J) (N : J → ℝ), (∀ σ ∈ s, 0 ≤ N σ) ∧
      ∀ U, g U * χ j U = ∑ σ ∈ s, N σ * χ σ U)
    (h0 : ∀ j, 0 ≤ ∫ U, χ j U ∂μ) {b : ℝ} (hb : 0 ≤ b) (j : J) :
    0 ≤ ∫ U, Real.exp (b * g U) * χ j U ∂μ :=
  integral_exp_mul_nonneg_of_moment hg hgb (hχ j) (hχb j)
    (fun n => moment_nonneg hg hgb hχ hχb hfus h0 n j) hb

/-- `a_j = (1/d_j) ∫ e^{b g} χ_j ≥ 0` for `b ≥ 0`, `d_j > 0` under fusion positivity. -/
theorem charCoeff_exp_nonneg {μ : Measure G} [IsFiniteMeasure μ] {g : G → ℝ} {χ : J → G → ℝ}
    (hg : Measurable g) (hgb : ∀ U, |g U| ≤ 1) (hχ : ∀ j, Measurable (χ j)) {B : J → ℝ}
    (hχb : ∀ j U, |χ j U| ≤ B j)
    (hfus : ∀ j, ∃ (s : Finset J) (N : J → ℝ), (∀ σ ∈ s, 0 ≤ N σ) ∧
      ∀ U, g U * χ j U = ∑ σ ∈ s, N σ * χ σ U)
    (h0 : ∀ j, 0 ≤ ∫ U, χ j U ∂μ) {b : ℝ} (hb : 0 ≤ b) (d : J → ℝ) {j : J} (hd : 0 < d j) :
    0 ≤ MKBound.charCoeff μ χ d (fun U => Real.exp (b * g U)) j :=
  div_nonneg (integral_exp_mul_nonneg hg hgb hχ hχb hfus h0 hb j) hd.le

/-- `|a_j| ≤ a₀`: for `k ≥ 0` integrable and `|χ_j| ≤ d_j`, `|(1/d_j) ∫ k χ_j| ≤ ∫ k`. -/
theorem abs_charCoeff_le {μ : Measure G} {k : G → ℝ} (hk0 : ∀ U, 0 ≤ k U) (hk : Integrable k μ)
    {χ : J → G → ℝ} {d : J → ℝ} {j : J} (hd : 0 < d j) (hχm : AEStronglyMeasurable (χ j) μ)
    (hχ : ∀ U, |χ j U| ≤ d j) : |MKBound.charCoeff μ χ d k j| ≤ ∫ U, k U ∂μ := by
  have hpt : ∀ U, |k U * χ j U| ≤ d j * k U := fun U => by
    rw [abs_mul, abs_of_nonneg (hk0 U), mul_comm (d j)]
    exact mul_le_mul_of_nonneg_left (hχ U) (hk0 U)
  have hkχ : Integrable (fun U => k U * χ j U) μ :=
    (hk.const_mul (d j)).mono' (hk.aestronglyMeasurable.mul hχm)
      (Eventually.of_forall fun U => by rw [Real.norm_eq_abs]; exact hpt U)
  unfold MKBound.charCoeff
  rw [abs_div, abs_of_pos hd, div_le_iff₀ hd]
  calc |∫ U, k U * χ j U ∂μ| ≤ ∫ U, |k U * χ j U| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ U, d j * k U ∂μ := integral_mono hkχ.abs (hk.const_mul _) hpt
    _ = (∫ U, k U ∂μ) * d j := by rw [integral_const_mul, mul_comm]

/-- `a₀ = ∫ e^{b g} > 0` on a nonzero finite measure for bounded measurable `g`. -/
theorem a0_pos {μ : Measure G} [IsFiniteMeasure μ] [NeZero μ] {g : G → ℝ}
    (hg : Measurable g) (hgb : ∀ U, |g U| ≤ 1) (b : ℝ) : 0 < ∫ U, Real.exp (b * g U) ∂μ :=
  MeasureTheory.integral_exp_pos (integrable_of_abs_bound
    (Real.measurable_exp.comp (hg.const_mul b)) (C := Real.exp |b|) fun U => by
      rw [abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg b) (hgb U))

end MassGap.PurityCharCoeff

#print axioms MassGap.PurityCharCoeff.integrable_pow_mul
#print axioms MassGap.PurityCharCoeff.moment_nonneg
#print axioms MassGap.PurityCharCoeff.integral_exp_mul_nonneg_of_moment
#print axioms MassGap.PurityCharCoeff.integral_exp_mul_nonneg
#print axioms MassGap.PurityCharCoeff.charCoeff_exp_nonneg
#print axioms MassGap.PurityCharCoeff.abs_charCoeff_le
#print axioms MassGap.PurityCharCoeff.a0_pos
