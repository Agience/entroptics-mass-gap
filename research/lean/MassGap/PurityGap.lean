import Mathlib
import MassGap.KernelGap
import MassGap.PurityBound

/-!
# MassGap.PurityGap — the sharp purity bound as an operator gap

Theorem 2.2, (2.3), of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford
and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510), for the `L²` operator
`K` of a bounded measurable symmetric kernel with a normalized top eigenfunction (the setting of
`KernelGap`, which the Wilson transfer kernels satisfy).

* `norm_pow_le_sharp`: if the pressure defect at time `2j` is below `log 2`, then
  `‖K^j f‖ ≤ √(d (exp (−defect))) ‖K‖^j ‖f‖` for every `f` orthogonal to the vacuum: the excited
  spectrum at time `2j` is at most `d (P)` relative to the top, the paper's
  `(λ₁/λ₀)^T ≤ d(p)` at `T = 2j`.
-/

namespace MassGap.PurityGap

open MeasureTheory Real MassGap.SlabKernelOperator MassGap.KernelPower MassGap.KernelGap
  MassGap.PurityBound

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {k : X → X → ℝ} {C : ℝ} (hkm : Measurable (Function.uncurry k)) (hC0 : 0 ≤ C)
  (hkb : ∀ x y, |k x y| ≤ C) (hsym : ∀ x y, k x y = k y x)
  {φ : X → ℝ} (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z)
  (hnorm : |c| = ‖kernelCLM k C hkm hC0 hkb μ μ‖) (hc0 : c ≠ 0)

include hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hc0 in
/-- **Theorem 2.2, (2.3), as an operator gap.** -/
theorem norm_pow_le_sharp (j : ℕ) (hj : 1 ≤ j)
    (hd : DoublingPower.defect (traceSeq μ k) (2 * j) < log 2) (f : Lp ℝ 2 μ)
    (hf : inner ℝ f (vac (μ := μ) hφm hφb) = 0) :
    ‖((kernelCLM k C hkm hC0 hkb μ μ) ^ j) f‖ ≤
      √(d (exp (-DoublingPower.defect (traceSeq μ k) (2 * j)))) *
        ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ j * ‖f‖ := by
  set K := kernelCLM k C hkm hC0 hkb μ μ
  have hpf := powerFacts hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hc0 j hj
  have hsd := excited_le_sharp hpf hd
  set dd := d (exp (-DoublingPower.defect (traceSeq μ k) (2 * j)))
  have hsq := norm_opPow_sq_le (hkm := hkm) (hC0 := hC0) (hkb := hkb) (hsym := hsym)
    (hφm := hφm) (hφb := hφb) (hφ1 := hφ1) (heig := heig) j hj f hf
  have hl : 0 < |c| := abs_pos.mpr hc0
  have hex : hs μ (iter μ (rem k c φ) (j - 1)) = excited μ k c φ j * |c| ^ (2 * j) :=
    (div_mul_cancel₀ _ (pow_ne_zero _ hl.ne')).symm
  rw [hex, hnorm] at hsq
  have hs0 : 0 ≤ excited μ k c φ j := hpf.s_nonneg
  have hdd0 : 0 ≤ dd := le_trans hs0 hsd
  have h2 : ‖(K ^ j) f‖ ^ 2 ≤ (√dd * ‖K‖ ^ j * ‖f‖) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hdd0, ← pow_mul]
    calc ‖(K ^ j) f‖ ^ 2 ≤ excited μ k c φ j * ‖K‖ ^ (2 * j) * ‖f‖ ^ 2 := hsq
      _ ≤ dd * ‖K‖ ^ (j * 2) * ‖f‖ ^ 2 := by rw [mul_comm j 2]; gcongr
  have h3 := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h3

end MassGap.PurityGap

#print axioms MassGap.PurityGap.norm_pow_le_sharp
