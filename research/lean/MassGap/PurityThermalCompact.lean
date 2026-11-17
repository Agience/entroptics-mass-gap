import Mathlib
import MassGap.KernelPower
import MassGap.KernelEigen
import MassGap.JentzschKT
import MassGap.PurityContraction
import MassGap.PurityThermal

/-!
# MassGap.PurityThermalCompact — Theorem 5.2 as an operator bound, and (6.2), (6.3) on a compact space

Theorem 5.2 and Proposition 6.1 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov,
I. J. Sessford and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling*
(research draft, 15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510,
`Paper-2/Paper-2.pdf`).

`X` is a compact, second countable Borel space with a probability measure `μ`. The kernel is
`k(x, y) = D(x) A(x, y) D(y)` with `D` continuous, `0 < dl ≤ D ≤ du`, and `A` continuous, symmetric,
`0 < a ≤ A ≤ b`, `a < b`. `τ = (b/a − 1)/(b/a + 1) = (b − a)/(b + a)`.

* `orth`, `eigen_of_rem`, `ratio_ne` (any probability space): an eigenfunction `g` of the deflated
  kernel `rem k c φ` with nonzero eigenvalue `σ` is orthogonal to `φ`; an eigenfunction of
  `rem k c φ` orthogonal to `φ` is an eigenfunction of `k` with the same eigenvalue; if `∫ g² = 1`
  and `φ` has no zeros, `g/φ` is not constant.
* `kcont`, `ksymm`, `klow`: `k` is continuous, symmetric, and `k ≥ dl² a > 0`.
* `continuous_eigen`: a bounded measurable pointwise eigenfunction of `k` with nonzero eigenvalue is
  continuous.
* `norm_rem_le`: Theorem 5.2 in operator form. `‖K‖ > 0` is an eigenvalue with a continuous
  eigenfunction `φ ≥ m > 0`, `∫ φ² = 1` (Jentzsch, `JentzschKT.exists_pos_eigen`), and the deflated
  operator `R` of `rem k ‖K‖ φ = k − ‖K‖ φ ⊗ φ` satisfies `‖R‖ ≤ τ ‖K‖`. `‖R‖` is attained at an
  eigenfunction `g` of `R` (`KernelEigen.exists_eigen`); `g` is an eigenfunction of `k` with `g/φ`
  bounded and not constant, so (5.2) (`PurityContraction.eigen_le`) bounds its eigenvalue.
* `trace_excess_compact`, `defect_compact`: (6.2) and (6.3) at `T = 2j`, `j ≥ 1`, with no spectral
  hypotheses: `‖K^j‖²_HS/‖K‖^T − 1 ≤ τ^T/(1 − τ²)` and `ψ_T ≤ 2 log (1 + τ^T/(1 − τ²))`.
-/

namespace MassGap.PurityThermalCompact

open MeasureTheory Real MassGap.SlabKernelOperator MassGap.KernelPower

section Measurable

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {k : X → X → ℝ} (hk : Bdd k) (hsym : ∀ x y, k x y = k y x)
  {φ : X → ℝ} (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z)
  {g : X → ℝ} (hgm : Measurable g) {Bg : ℝ} (hgb : ∀ x, |g x| ≤ Bg)

include hk hsym hφm hφb hφ1 heig hgm hgb in
/-- An eigenfunction of the deflated kernel with nonzero eigenvalue is orthogonal to `φ`. -/
theorem orth {σ : ℝ} (hσ : σ ≠ 0) (hg : ∀ z, ∫ y, rem k c φ z y * g y ∂μ = σ * g z) :
    ∫ x, φ x * g x ∂μ = 0 := by
  have hr := hk.rem (c := c) hφm hφb
  obtain ⟨Cr, hCr⟩ := hr.bdd
  have h1 : σ * ∫ x, φ x * g x ∂μ = ∫ z, ∫ y, φ z * (rem k c φ z y * g y) ∂μ ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show σ * (φ z * g z) = ∫ y, φ z * (rem k c φ z y * g y) ∂μ
    rw [integral_const_mul, hg z]; ring
  have h2 : ∫ z, ∫ y, φ z * (rem k c φ z y * g y) ∂μ ∂μ
      = ∫ y, ∫ z, φ z * (rem k c φ z y * g y) ∂μ ∂μ :=
    swap_bdd (C := B * (Cr * Bg))
      ((hφm.comp measurable_fst).mul (hr.meas.mul (hgm.comp measurable_snd)))
      (fun z y => by
        rw [abs_mul, abs_mul]
        exact mul_le_mul (hφb z) (mul_le_mul (hCr z y) (hgb y) (abs_nonneg _)
          ((abs_nonneg _).trans (hCr z y))) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          ((abs_nonneg _).trans (hφb z)))
  have h3 : ∀ y, ∫ z, φ z * (rem k c φ z y * g y) ∂μ = 0 := by
    intro y
    have e : (fun z => φ z * (rem k c φ z y * g y)) = fun z => (φ z * rem k c φ z y) * g y := by
      funext z; ring
    rw [e, integral_mul_const, rem_col_orth hk hsym hφm hφb hφ1 heig y, zero_mul]
  rw [h2] at h1
  simp only [h3, integral_zero] at h1
  exact (mul_eq_zero.mp h1).resolve_left hσ

include hk hφm hφb hgm hgb in
/-- An eigenfunction of the deflated kernel orthogonal to `φ` is an eigenfunction of `k`. -/
theorem eigen_of_rem (horth : ∫ x, φ x * g x ∂μ = 0) {σ : ℝ}
    (hg : ∀ z, ∫ y, rem k c φ z y * g y ∂μ = σ * g z) (z : X) :
    ∫ y, k z y * g y ∂μ = σ * g z := by
  have hr := hk.rem (c := c) hφm hφb
  obtain ⟨Cr, hCr⟩ := hr.bdd
  have e : (fun y => k z y * g y) = fun y => rem k c φ z y * g y + (c * φ z) * (φ y * g y) := by
    funext y; unfold MassGap.KernelPower.rem; ring
  rw [e, integral_add, integral_const_mul, horth, hg z, mul_zero, add_zero]
  · exact integrable_mul_of_bdd (hr.meas.comp measurable_prodMk_left) hgm (hCr z) hgb
  · exact (integrable_mul_of_bdd hφm hgm hφb hgb).const_mul _

omit [IsProbabilityMeasure μ] in
/-- If `g ⊥ φ`, `∫ φ² = ∫ g² = 1` and `φ` has no zeros, `g/φ` is not constant. -/
theorem ratio_ne [IsProbabilityMeasure μ] (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) (hg1 : ∫ x, g x ^ 2 ∂μ = 1)
    (horth : ∫ x, φ x * g x ∂μ = 0) (hφ0 : ∀ x, φ x ≠ 0) :
    ∃ x x', g x / φ x ≠ g x' / φ x' := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · have h := measure_univ (μ := μ)
    rw [Set.univ_eq_empty_iff.mpr hX, measure_empty] at h
    exact absurd h zero_ne_one
  by_contra hcon
  push Not at hcon
  set κ := g x₀ / φ x₀
  have hgk : ∀ x, g x = κ * φ x := fun x => by
    rw [← (div_eq_iff (hφ0 x)).mp (hcon x x₀)]
  have hκ : κ = 0 := by
    have e : (fun x => φ x * g x) = fun x => κ * φ x ^ 2 := by funext x; rw [hgk x]; ring
    rw [e, integral_const_mul, hφ1, mul_one] at horth
    exact horth
  have e : (fun x => g x ^ 2) = fun _ => (0 : ℝ) := by funext x; rw [hgk x, hκ]; ring
  rw [e, integral_zero] at hg1
  exact zero_ne_one hg1

end Measurable

section Compact

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {D : X → ℝ} (hDc : Continuous D) {dl du : ℝ} (hdl : 0 < dl) (hDl : ∀ x, dl ≤ D x)
  (hDu : ∀ x, D x ≤ du)
  {A : X → X → ℝ} (hAc : Continuous (Function.uncurry A)) (hAsym : ∀ x y, A x y = A y x)
  {a b : ℝ} (ha : 0 < a) (hab' : a < b) (hAa : ∀ x y, a ≤ A x y) (hAb : ∀ x y, A x y ≤ b)
  {k : X → X → ℝ} (hkdef : ∀ x y, k x y = D x * A x y * D y)
  {C : ℝ} (hkm : Measurable (Function.uncurry k)) (hC0 : 0 ≤ C) (hkb : ∀ x y, |k x y| ≤ C)

omit [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
include hDc hAc hkdef in
theorem kcont : Continuous (Function.uncurry k) := by
  have e : Function.uncurry k = fun p : X × X => D p.1 * A p.1 p.2 * D p.2 := by
    funext p; exact hkdef p.1 p.2
  rw [e]
  exact ((hDc.comp continuous_fst).mul hAc).mul (hDc.comp continuous_snd)

omit [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [BorelSpace X] in
include hAsym hkdef in
theorem ksymm : ∀ x y, k x y = k y x := fun x y => by
  rw [hkdef, hkdef, hAsym]; ring

omit [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [BorelSpace X] in
include hdl hDl ha hAa hkdef in
theorem klow : ∀ x y, dl * a * dl ≤ k x y := fun x y => by
  rw [hkdef]
  have h1 := hDl x
  have h2 := hDl y
  have h3 := hAa x y
  exact mul_le_mul (mul_le_mul h1 h3 ha.le (hdl.le.trans h1)) h2 hdl.le
    (mul_pos (hdl.trans_le h1) (ha.trans_le h3)).le

omit [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [BorelSpace X] in
include ha in
/-- `τ = (b/a − 1)/(b/a + 1) = (b − a)/(b + a)`. -/
theorem tau_eq : (b / a - 1) / (b / a + 1) = (b - a) / (b + a) := by
  have := ha
  field_simp

include hDc hAc hkdef hC0 hkb in
/-- A bounded measurable pointwise eigenfunction of `k` with nonzero eigenvalue is continuous. -/
theorem continuous_eigen {φ : X → ℝ} (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B)
    {lam : ℝ} (hl : lam ≠ 0) (heig : ∀ z, ∫ y, k z y * φ y ∂μ = lam * φ z) : Continuous φ := by
  have hkc := kcont hDc hAc hkdef
  have hmem : MemLp φ 2 μ := MemLp.of_bound hφm.aestronglyMeasurable B
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hφb x)
  have hcont := KernelEigen.continuous_kernelFun hkc hC0 hkb (hmem.toLp φ)
  have e : φ = fun z => lam⁻¹ * kernelFun k μ ((hmem.toLp φ : Lp ℝ 2 μ) : X → ℝ) z := by
    funext z
    have h : kernelFun k μ ((hmem.toLp φ : Lp ℝ 2 μ) : X → ℝ) z = lam * φ z := by
      unfold kernelFun
      rw [← heig z]
      exact integral_congr_ae (by filter_upwards [hmem.coeFn_toLp] with y hy; rw [hy])
    rw [h, ← mul_assoc, inv_mul_cancel₀ hl, one_mul]
  rw [e]
  exact continuous_const.mul hcont

include hDc hdl hDl hDu hAc hAsym ha hab' hAa hAb hkdef in
/-- **Theorem 5.2 in operator form.** `‖K‖ > 0` is an eigenvalue of the DAD kernel with a
continuous eigenfunction `φ ≥ m > 0`, `|φ| ≤ C/‖K‖`, `∫ φ² = 1`, and the deflated operator of
`rem k ‖K‖ φ` has norm at most `τ ‖K‖`, `τ = (b/a − 1)/(b/a + 1)`. -/
theorem norm_rem_le :
    0 < ‖kernelCLM k C hkm hC0 hkb μ μ‖ ∧
      ∃ φ : X → ℝ, Continuous φ ∧ (∃ m, 0 < m ∧ ∀ x, m ≤ φ x) ∧
        (∀ x, |φ x| ≤ C / ‖kernelCLM k C hkm hC0 hkb μ μ‖) ∧ ∫ x, φ x ^ 2 ∂μ = 1 ∧
        (∀ z, ∫ y, k z y * φ y ∂μ = ‖kernelCLM k C hkm hC0 hkb μ μ‖ * φ z) ∧
        ∀ (Cr : ℝ) (hrm : Measurable (Function.uncurry (rem k ‖kernelCLM k C hkm hC0 hkb μ μ‖ φ)))
          (hCr0 : 0 ≤ Cr) (hrb : ∀ x y, |rem k ‖kernelCLM k C hkm hC0 hkb μ μ‖ φ x y| ≤ Cr),
          ‖kernelCLM (rem k ‖kernelCLM k C hkm hC0 hkb μ μ‖ φ) Cr hrm hCr0 hrb μ μ‖
            ≤ (b / a - 1) / (b / a + 1) * ‖kernelCLM k C hkm hC0 hkb μ μ‖ := by
  have hkc := kcont hDc hAc hkdef
  have hsym := ksymm hAsym hkdef
  obtain ⟨hpos, φ, hφm, hφb, ⟨m, hm, hφl⟩, hφ1, heig⟩ :=
    JentzschKT.exists_pos_eigen (μ := μ) hkc hC0 hkb hsym
      (mul_pos (mul_pos hdl ha) hdl) (klow hdl hDl ha hAa hkdef)
  set lam := ‖kernelCLM k C hkm hC0 hkb μ μ‖ with hlam
  have hφc : Continuous φ := continuous_eigen hDc hAc hkdef hC0 hkb hφm hφb hpos.ne' heig
  refine ⟨hpos, φ, hφc, ⟨m, hm, hφl⟩, hφb, hφ1, heig, fun Cr hrm hCr0 hrb => ?_⟩
  rw [tau_eq ha]
  have hτ0 : 0 ≤ (b - a) / (b + a) := div_nonneg (by linarith) (by linarith)
  rcases (norm_nonneg (kernelCLM (rem k lam φ) Cr hrm hCr0 hrb μ μ)).eq_or_lt with h0 | hRpos
  · rw [← h0]; exact mul_nonneg hτ0 hpos.le
  have hrc : Continuous (Function.uncurry (rem k lam φ)) := rem_cont hkc hφc
  have hrsym : ∀ x y, rem k lam φ x y = rem k lam φ y x := rem_symm hsym
  obtain ⟨g, hgm, ⟨Bg, hgb⟩, hg1, σ, hσ, hg⟩ :=
    KernelEigen.exists_eigen (μ := μ) hrc hCr0 hrb hrsym hRpos
  have hσ' : |σ| = ‖kernelCLM (rem k lam φ) Cr hrm hCr0 hrb μ μ‖ := hσ
  have hσ0 : σ ≠ 0 := by
    intro h; rw [h, abs_zero] at hσ'; linarith
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have horth := orth hk hsym hφm hφb hφ1 heig hgm hgb hσ0 hg
  have hKg := eigen_of_rem hk hφm hφb hgm hgb horth hg
  have hφ0 : ∀ x, φ x ≠ 0 := fun x => (hm.trans_le (hφl x)).ne'
  have hne := ratio_ne (μ := μ) hφ1 hg1 horth hφ0
  have hBg : 0 ≤ Bg := (abs_nonneg _).trans (hgb (hne.choose))
  have hbd : ∀ x, |g x / φ x| ≤ Bg / m := fun x => by
    have hφx : 0 < φ x := hm.trans_le (hφl x)
    rw [abs_div, abs_of_pos hφx, div_le_div_iff₀ hφx hm]
    have h1 := mul_le_mul_of_nonneg_right (hgb x) hm.le
    have h2 := mul_le_mul_of_nonneg_left (hφl x) hBg
    linarith
  have hle := PurityContraction.eigen_le (μ := μ) (IsProbabilityMeasure.ne_zero μ)
    (D := D) (h := φ) (ψ := g) (A := A) (m := -(Bg / m)) (M := Bg / m)
    hdl hDc.measurable hDl hDu hm hφm hφl (fun x => (le_abs_self _).trans (hφb x))
    ha hab'.le (fun x => hAc.measurable.comp measurable_prodMk_left) hAa hAb hgm
    (fun x => (abs_le.mp (hbd x)).1) (fun x => (abs_le.mp (hbd x)).2) hpos
    (fun x => by simpa only [hkdef] using heig x) (fun x => by simpa only [hkdef] using hKg x) hne
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos] at hle
  rw [← hσ']
  exact hle

include hDc hdl hDl hDu hAc hAsym ha hab' hAa hAb hkdef in
/-- **(6.2) on a compact space.** `‖K^j‖²_HS/‖K‖^T − 1 ≤ τ^T/(1 − τ²)` at `T = 2j`, `j ≥ 1`. -/
theorem trace_excess_compact (j : ℕ) (hj : 1 ≤ j) :
    let τ := (b / a - 1) / (b / a + 1)
    traceSeq μ k (2 * j) / ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ (2 * j) - 1
      ≤ τ ^ (2 * j) / (1 - τ ^ 2) := by
  obtain ⟨hpos, φ, hφc, -, hφb, hφ1, heig, hR⟩ :=
    norm_rem_le (μ := μ) hDc hdl hDl hDu hAc hAsym ha hab' hAa hAb hkdef hkm hC0 hkb
  set lam := ‖kernelCLM k C hkm hC0 hkb μ μ‖ with hlam
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr := hk.rem (c := lam) hφc.measurable hφb
  obtain ⟨Cr, hCr⟩ := hr.bdd
  have hrb : ∀ x y, |rem k lam φ x y| ≤ max Cr 0 := fun x y => (hCr x y).trans (le_max_left _ _)
  have hS : 0 < ∫ x, D x ^ 2 ∂μ := by
    have hint : Integrable (fun x => D x ^ 2) μ :=
      integrable_of_bdd (hDc.measurable.pow_const 2) (C := du ^ 2) (fun x => by
        rw [abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (hdl.le.trans (hDl x)) (hDu x) 2)
    have h := integral_mono (integrable_const (dl ^ 2)) hint
      (fun x => pow_le_pow_left₀ hdl.le (hDl x) 2)
    simp at h
    linarith [pow_pos hdl 2]
  exact PurityThermal.trace_excess_dad hDc.measurable
    (fun x => by rw [abs_of_pos (hdl.trans_le (hDl x))]; exact hDu x)
    hAc.measurable ha hab' (fun x y => ⟨hAa x y, hAb x y⟩) hkdef hkm hC0 hkb hS
    (ksymm hAsym hkdef) hφc.measurable hφb hφ1 heig (abs_of_pos hpos) hpos.ne'
    hr.meas (le_max_right _ _) hrb (by rw [abs_of_pos hpos]; exact hR _ _ _ _) j hj

include hDc hdl hDl hDu hAc hAsym ha hab' hAa hAb hkdef hkm hC0 hkb in
/-- **(6.3) on a compact space.** `ψ_T ≤ 2 log (1 + τ^T/(1 − τ²))` at `T = 2j`, `j ≥ 1`. -/
theorem defect_compact (j : ℕ) (hj : 1 ≤ j) :
    let τ := (b / a - 1) / (b / a + 1)
    DoublingPower.defect (traceSeq μ k) (2 * j) ≤ 2 * Real.log (1 + τ ^ (2 * j) / (1 - τ ^ 2)) := by
  obtain ⟨hpos, φ, hφc, -, hφb, hφ1, heig, hR⟩ :=
    norm_rem_le (μ := μ) hDc hdl hDl hDu hAc hAsym ha hab' hAa hAb hkdef hkm hC0 hkb
  set lam := ‖kernelCLM k C hkm hC0 hkb μ μ‖ with hlam
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr := hk.rem (c := lam) hφc.measurable hφb
  obtain ⟨Cr, hCr⟩ := hr.bdd
  have hrb : ∀ x y, |rem k lam φ x y| ≤ max Cr 0 := fun x y => (hCr x y).trans (le_max_left _ _)
  have hS : 0 < ∫ x, D x ^ 2 ∂μ := by
    have hint : Integrable (fun x => D x ^ 2) μ :=
      integrable_of_bdd (hDc.measurable.pow_const 2) (C := du ^ 2) (fun x => by
        rw [abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (hdl.le.trans (hDl x)) (hDu x) 2)
    have h := integral_mono (integrable_const (dl ^ 2)) hint
      (fun x => pow_le_pow_left₀ hdl.le (hDl x) 2)
    simp at h
    linarith [pow_pos hdl 2]
  exact PurityThermal.defect_dad hDc.measurable
    (fun x => by rw [abs_of_pos (hdl.trans_le (hDl x))]; exact hDu x)
    hAc.measurable ha hab' (fun x y => ⟨hAa x y, hAb x y⟩) hkdef hkm hC0 hkb hS
    (ksymm hAsym hkdef) hφc.measurable hφb hφ1 heig (abs_of_pos hpos) hpos.ne'
    hr.meas (le_max_right _ _) hrb (by rw [abs_of_pos hpos]; exact hR _ _ _ _) j hj

end Compact

#print axioms orth
#print axioms eigen_of_rem
#print axioms ratio_ne
#print axioms kcont
#print axioms ksymm
#print axioms klow
#print axioms tau_eq
#print axioms continuous_eigen
#print axioms norm_rem_le
#print axioms trace_excess_compact
#print axioms defect_compact

end MassGap.PurityThermalCompact
