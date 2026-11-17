import Mathlib
import MassGap.KernelPower
import MassGap.DefectBound
import MassGap.PurityTrace
import MassGap.PurityRayleigh

/-!
# MassGap.PurityThermal — (6.2) and (6.3) of the purity paper for kernels, at even times

Proposition 6.1 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford
and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`).

`k` is a bounded, jointly measurable, symmetric kernel on a probability space with a bounded
eigenfunction `φ`, `∫ φ² = 1`, eigenvalue `c ≠ 0` and `|c| = ‖K‖`. `rem k c φ = k − c φ ⊗ φ` is the
deflated kernel and `R` its operator on `L²`. The time is `T = 2j`, `j ≥ 1`, and the trace at `T`
is `traceSeq μ k T = ‖K^j‖²_HS`.

* `hs_rem`, `hs_rem_ratio`: `‖rem‖²_HS = ‖K‖²_HS − c²`, so
  `‖rem‖²_HS / c² = ‖K‖²_HS/‖K‖² − 1`.
* `excited_le`: the operator form of (6.2). If `‖R‖ ≤ τ |c|`, the relative excited weight at `T`
  is at most `τ^{T−2} ‖rem‖²_HS / c²`. The spectral form `Σ r_j^T ≤ τ^{T−2} Σ r_j²` is
  `PurityTrace.tail_le`; here no spectral expansion is used, only `‖R^{j−1} S‖_HS ≤ ‖R‖^{j−1} ‖S‖_HS`
  (`KernelPower.hs_iter_le`).
* `trace_excess_le`, `defect_le`: with `‖K‖²_HS/‖K‖² − 1 ≤ U`, the normalized trace satisfies
  `‖K^j‖²_HS / ‖K‖^T − 1 ≤ τ^{T−2} U` and
  `ψ_T = 2 log ‖K^j‖²_HS − log ‖K^{2j}‖²_HS ≤ 2 log (1 + τ^{T−2} U)`. The normalization by
  `‖K‖^T` cancels in `ψ_T`.
* `trace_excess_dad`, `defect_dad`: (6.2) and (6.3) for the DAD kernel `k = D(x) A(x,y) D(y)` with
  `a ≤ A ≤ b`, `0 < a < b`, `τ = (b/a − 1)/(b/a + 1)`, and `‖R‖ ≤ τ ‖K‖`:
  `‖K^j‖²_HS/‖K‖^T − 1 ≤ τ^T/(1 − τ²)` and `ψ_T ≤ 2 log (1 + τ^T/(1 − τ²))`.

The hypothesis `‖R‖ ≤ τ |c|` is the eigenvalue-ratio bound (5.2) of Theorem 5.2 as an
operator-norm bound on the deflated operator: for compact self-adjoint `K` with simple top
eigenvalue `|c|` it is `|λ_j| ≤ τ λ₀` for every other eigenvalue. Positivity of `K` is not used at
even `T`. For symmetric `k`, `‖K^j‖²_HS` is the trace of `K^{2j}`; the identification of the
cyclic integral with the operator trace is not made here.
-/

namespace MassGap.PurityThermal

open MeasureTheory Real MassGap.SlabKernelOperator MassGap.KernelPower

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

section General

variable {k : X → X → ℝ} {C : ℝ} (hkm : Measurable (Function.uncurry k)) (hC0 : 0 ≤ C)
  (hkb : ∀ x y, |k x y| ≤ C) (hsym : ∀ x y, k x y = k y x)
  {φ : X → ℝ} (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z)
  (hnorm : |c| = ‖kernelCLM k C hkm hC0 hkb μ μ‖) (hc0 : c ≠ 0)
  {Cr : ℝ} (hrm : Measurable (Function.uncurry (rem k c φ))) (hCr0 : 0 ≤ Cr)
  (hrb : ∀ x y, |rem k c φ x y| ≤ Cr) {τ : ℝ}
  (hτ : ‖kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ‖ ≤ τ * |c|)

include hkm hkb hsym hφm hφb hφ1 heig in
/-- `‖rem‖²_HS = ‖K‖²_HS − c²`. -/
theorem hs_rem : hs μ (rem k c φ) = hs μ k - c ^ 2 := by
  have h : hs μ k = c ^ 2 + hs μ (rem k c φ) :=
    hs_iter_decomp (μ := μ) ⟨hkm, C, hkb⟩ hsym hφm hφb hφ1 heig 0
  linarith

include hkm hkb hsym hφm hφb hφ1 heig hnorm hc0 in
/-- `‖rem‖²_HS / c² = ‖K‖²_HS/‖K‖² − 1`. -/
theorem hs_rem_ratio :
    hs μ (rem k c φ) / |c| ^ 2 = hs μ k / ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ 2 - 1 := by
  rw [← hnorm, sq_abs, hs_rem hkm hkb hsym hφm hφb hφ1 heig, sub_div,
    div_self (pow_ne_zero 2 hc0)]

include hc0 hτ in
/-- **(6.2), operator form.** If `‖R‖ ≤ τ |c|`, the relative excited weight at `T = 2j` is at most
`τ^{T−2} ‖rem‖²_HS / c²`. -/
theorem excited_le (j : ℕ) (hj : 1 ≤ j) :
    excited μ k c φ j ≤ τ ^ (2 * (j - 1)) * (hs μ (rem k c φ) / |c| ^ 2) := by
  have hl : 0 < |c| := abs_pos.mpr hc0
  have h := hs_iter_le (μ := μ) hrm hCr0 hrb 0 (j - 1)
  rw [zero_add] at h
  change hs μ (iter μ (rem k c φ) (j - 1)) ≤ _ * hs μ (rem k c φ) at h
  have hp : ‖kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ‖ ^ (2 * (j - 1)) ≤ (τ * |c|) ^ (2 * (j - 1)) :=
    pow_le_pow_left₀ (norm_nonneg _) hτ _
  have h2 : hs μ (iter μ (rem k c φ) (j - 1)) ≤ (τ * |c|) ^ (2 * (j - 1)) * hs μ (rem k c φ) :=
    h.trans (mul_le_mul_of_nonneg_right hp (hs_nonneg _))
  have he : |c| ^ (2 * j) = |c| ^ (2 * (j - 1)) * |c| ^ 2 := by
    rw [← pow_add]; congr 1; omega
  unfold excited
  rw [div_le_iff₀ (pow_pos hl _), he]
  calc hs μ (iter μ (rem k c φ) (j - 1)) ≤ (τ * |c|) ^ (2 * (j - 1)) * hs μ (rem k c φ) := h2
    _ = τ ^ (2 * (j - 1)) * (hs μ (rem k c φ) / |c| ^ 2) * (|c| ^ (2 * (j - 1)) * |c| ^ 2) := by
        rw [mul_pow]; field_simp; try ring

include hkm hkb hsym hφm hφb hφ1 heig hnorm hc0 hτ in
/-- **(6.2) for the normalized trace.** With `‖K‖²_HS/‖K‖² − 1 ≤ U`,
`‖K^j‖²_HS / ‖K‖^T − 1 ≤ τ^{T−2} U` at `T = 2j`. -/
theorem trace_excess_le {U : ℝ} (hU : hs μ k / ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ 2 - 1 ≤ U)
    (j : ℕ) (hj : 1 ≤ j) :
    traceSeq μ k (2 * j) / ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ (2 * j) - 1
      ≤ τ ^ (2 * (j - 1)) * U := by
  have hf := powerFacts (μ := μ) hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hc0 j hj
  have hl : 0 < |c| := abs_pos.mpr hc0
  have hτ0 : 0 ≤ τ := (mul_nonneg_iff_of_pos_right hl).1 ((norm_nonneg _).trans hτ)
  have hb : traceSeq μ k (2 * j) / |c| ^ (2 * j) - 1 = excited μ k c φ j := by
    rw [hf.base, mul_div_cancel_left₀ _ (pow_pos hl _).ne']; ring
  rw [← hnorm, hb]
  have he := excited_le hc0 hrm hCr0 hrb hτ j hj
  rw [hs_rem_ratio hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hc0] at he
  exact he.trans (mul_le_mul_of_nonneg_left hU (pow_nonneg hτ0 _))

include hkm hkb hsym hφm hφb hφ1 heig hnorm hc0 hτ in
/-- **(6.3) for kernels.** With `‖K‖²_HS/‖K‖² − 1 ≤ U`,
`ψ_T = 2 log ‖K^j‖²_HS − log ‖K^{2j}‖²_HS ≤ 2 log (1 + τ^{T−2} U)` at `T = 2j`. -/
theorem defect_le {U : ℝ} (hU : hs μ k / ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ 2 - 1 ≤ U)
    (j : ℕ) (hj : 1 ≤ j) :
    DoublingPower.defect (traceSeq μ k) (2 * j) ≤ 2 * Real.log (1 + τ ^ (2 * (j - 1)) * U) := by
  have hf := powerFacts (μ := μ) hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hc0 j hj
  have hτ0 : 0 ≤ τ :=
    (mul_nonneg_iff_of_pos_right (abs_pos.mpr hc0)).1 ((norm_nonneg _).trans hτ)
  have he := excited_le hc0 hrm hCr0 hrb hτ j hj
  rw [hs_rem_ratio hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hc0] at he
  have he' := he.trans (mul_le_mul_of_nonneg_left hU (pow_nonneg hτ0 _))
  have hs0 := hf.s_nonneg
  refine (DefectBound.defect_le_two_log_one_add hf).trans ?_
  have hlog := Real.log_le_log (by linarith : (0 : ℝ) < 1 + excited μ k c φ j)
    (by linarith : 1 + excited μ k c φ j ≤ 1 + τ ^ (2 * (j - 1)) * U)
  linarith

end General

section DAD

variable {D : X → ℝ} (hD : Measurable D) {M : ℝ} (hDb : ∀ x, |D x| ≤ M)
  {A : X → X → ℝ} (hA : Measurable (Function.uncurry A)) {a b : ℝ} (ha : 0 < a) (hab' : a < b)
  (hab : ∀ x y, A x y ∈ Set.Icc a b)
  {k : X → X → ℝ} (hkdef : ∀ x y, k x y = D x * A x y * D y) {C : ℝ}
  (hkm : Measurable (Function.uncurry k)) (hC0 : 0 ≤ C) (hkb : ∀ x y, |k x y| ≤ C)
  (hS : 0 < ∫ x, D x ^ 2 ∂μ) (hsym : ∀ x y, k x y = k y x)
  {φ : X → ℝ} (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z)
  (hnorm : |c| = ‖kernelCLM k C hkm hC0 hkb μ μ‖) (hc0 : c ≠ 0)
  {Cr : ℝ} (hrm : Measurable (Function.uncurry (rem k c φ))) (hCr0 : 0 ≤ Cr)
  (hrb : ∀ x y, |rem k c φ x y| ≤ Cr)
  (hτ : ‖kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ‖ ≤ (b / a - 1) / (b / a + 1) * |c|)

/-- `τ^{T−2} · τ²/(1 − τ²) = τ^T/(1 − τ²)` at `T = 2j`, `j ≥ 1`. -/
theorem pow_tail (τ : ℝ) (j : ℕ) (hj : 1 ≤ j) :
    τ ^ (2 * (j - 1)) * (τ ^ 2 / (1 - τ ^ 2)) = τ ^ (2 * j) / (1 - τ ^ 2) := by
  have he : 2 * j = 2 * (j - 1) + 2 := by omega
  rw [he, pow_add, mul_div_assoc]

include hD hDb hA ha hab' hab hkdef hkm hkb hS hsym hφm hφb hφ1 heig hnorm hc0 hτ in
/-- **(6.2) for a DAD kernel.** `‖K^j‖²_HS/‖K‖^T − 1 ≤ τ^T/(1 − τ²)` at `T = 2j`, with
`τ = (b/a − 1)/(b/a + 1)`, and `‖R‖ ≤ τ ‖K‖`. -/
theorem trace_excess_dad (j : ℕ) (hj : 1 ≤ j) :
    let τ := (b / a - 1) / (b / a + 1)
    traceSeq μ k (2 * j) / ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ (2 * j) - 1
      ≤ τ ^ (2 * j) / (1 - τ ^ 2) := by
  intro τ
  have hU := PurityRayleigh.trace_ratio_le (μ := μ) hD hDb hA ha hab hkdef hkm hC0 hkb hS
  have hid : (b - a) ^ 2 / (4 * a * b) = τ ^ 2 / (1 - τ ^ 2) := PurityTrace.tau_identity ha hab'
  have hτ' : ‖kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ‖ ≤ τ * |c| := hτ
  rw [PurityRayleigh.traceSeq_two, hid] at hU
  have h := trace_excess_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hc0 hrm hCr0 hrb hτ' hU j hj
  rwa [pow_tail τ j hj] at h

include hD hDb hA ha hab' hab hkdef hkm hkb hS hsym hφm hφb hφ1 heig hnorm hc0 hτ in
/-- **(6.3) for a DAD kernel.** `ψ_T ≤ 2 log (1 + τ^T/(1 − τ²))` at `T = 2j`, with
`τ = (b/a − 1)/(b/a + 1)`, and `‖R‖ ≤ τ ‖K‖`. -/
theorem defect_dad (j : ℕ) (hj : 1 ≤ j) :
    let τ := (b / a - 1) / (b / a + 1)
    DoublingPower.defect (traceSeq μ k) (2 * j) ≤ 2 * Real.log (1 + τ ^ (2 * j) / (1 - τ ^ 2)) := by
  intro τ
  have hU := PurityRayleigh.trace_ratio_le (μ := μ) hD hDb hA ha hab hkdef hkm hC0 hkb hS
  have hid : (b - a) ^ 2 / (4 * a * b) = τ ^ 2 / (1 - τ ^ 2) := PurityTrace.tau_identity ha hab'
  have hτ' : ‖kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ‖ ≤ τ * |c| := hτ
  rw [PurityRayleigh.traceSeq_two, hid] at hU
  have h := defect_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hc0 hrm hCr0 hrb hτ' hU j hj
  rwa [pow_tail τ j hj] at h

end DAD

#print axioms hs_rem
#print axioms hs_rem_ratio
#print axioms excited_le
#print axioms trace_excess_le
#print axioms defect_le
#print axioms pow_tail
#print axioms trace_excess_dad
#print axioms defect_dad

end MassGap.PurityThermal
