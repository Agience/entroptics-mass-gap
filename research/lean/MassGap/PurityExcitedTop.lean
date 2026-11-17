import Mathlib
import MassGap.PurityLatticeGap
import MassGap.PurityThermalCompact

/-!
# MassGap.PurityExcitedTop — the largest excited eigenvalue

The largest excited eigenvalue `λ₁` of Theorem 5.4 of D. Bhattacharjee, U. Bhattacharya,
J. M. Lockwood, T. Romanov, I. J. Sessford and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills
Theory at Weak Coupling* (research draft, 15 November 2026, <https://github.com/anaxia-research/4Y-M>,
commit 8e01510, `Paper-2/Paper-2.pdf`). `λ₁` is the norm of the deflated operator
`R` of `rem k c φ = k − c φ ⊗ φ`: every excited eigenvalue `σ` has `|σ| ≤ ‖R‖`, and when `‖R‖ > 0` it is the
eigenvalue of an excited eigenfunction.

* `top` (compact second countable Borel space, probability measure, continuous bounded symmetric
  kernel, nonnegative form, `φ` a continuous bounded eigenfunction, `Kφ = c φ`, `∫ φ² = 1`): every bounded measurable eigenfunction `g ⊥ φ`, `∫ g² = 1`, has `|σ| ≤ ‖R‖`; if
  `‖R‖ > 0`, there is a bounded measurable `ψ ⊥ φ`, `∫ ψ² = 1`, with `Kψ = ‖R‖ ψ`.
* `lam1` (`RectTransferG.kTG`, `β > 0`, spatial extents at least `2`, nontrivial gauge group):
  `λ₀ = ‖K‖ > 0`, and there is `λ₁` with `0 ≤ λ₁ ≤ τ λ₀`, `τ = tanh(β tpMax (1 − q/d)/2)`, bounding every excited
  eigenvalue in absolute value and attained by an excited eigenfunction when `λ₁ > 0`.
-/

namespace MassGap.PurityExcitedTop

open MeasureTheory Real MassGap MassGap.SlabKernelOperator MassGap.KernelPower

section Abstract

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- **The largest excited eigenvalue is `‖R‖`.** Every excited eigenvalue has `|σ| ≤ ‖R‖`, and
`‖R‖ > 0` is attained by an excited eigenfunction. -/
theorem top {k : X → X → ℝ} (hkc : Continuous (Function.uncurry k)) {C : ℝ}
    (hkb : ∀ x y, |k x y| ≤ C) (hsym : ∀ x y, k x y = k y x)
    {φ : X → ℝ} (hφc : Continuous φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B)
    (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z)
    (hform : ∀ g : X → ℝ, Integrable g μ → 0 ≤ ∫ x, (∫ y, k x y * g y ∂μ) * g x ∂μ)
    {Cr : ℝ} (hrm : Measurable (Function.uncurry (rem k c φ))) (hCr0 : 0 ≤ Cr)
    (hrb : ∀ x y, |rem k c φ x y| ≤ Cr) :
    (∀ g : X → ℝ, Measurable g → ∀ Bg : ℝ, (∀ x, |g x| ≤ Bg) → ∫ x, g x ^ 2 ∂μ = 1 →
        ∫ x, φ x * g x ∂μ = 0 → ∀ σ : ℝ, (∀ z, ∫ y, k z y * g y ∂μ = σ * g z) →
        |σ| ≤ ‖kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ‖) ∧
      (0 < ‖kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ‖ →
        ∃ ψ : X → ℝ, Measurable ψ ∧ (∃ Bψ, ∀ x, |ψ x| ≤ Bψ) ∧ ∫ x, ψ x ^ 2 ∂μ = 1 ∧
          ∫ x, φ x * ψ x ∂μ = 0 ∧
          ∀ z, ∫ y, k z y * ψ y ∂μ = ‖kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ‖ * ψ z) := by
  have hk : Bdd k := ⟨hkc.measurable, C, hkb⟩
  have hφm := hφc.measurable
  refine ⟨fun g hgm Bg hgb hg1 horth σ hg =>
    PurityLatticeGap.abs_eigen_le_norm hrm hCr0 hrb hgm hgb hg1
      (PurityLatticeGap.rem_eigen hk hφm hφb hgm hgb horth hg c), fun hpos => ?_⟩
  obtain ⟨ψ, hψm, ⟨Bψ, hψb⟩, hψ1, σ, hσ, hψ⟩ :=
    KernelEigen.exists_eigen (μ := μ) (rem_cont hkc hφc) hCr0 hrb (rem_symm hsym) hpos
  have hσ' : |σ| = ‖kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ‖ := hσ
  have hσ0 : σ ≠ 0 := by intro h; rw [h, abs_zero] at hσ'; linarith
  have horth := PurityThermalCompact.orth hk hsym hφm hφb hφ1 heig hψm hψb hσ0 hψ
  have hK := PurityThermalCompact.eigen_of_rem hk hφm hφb hψm hψb horth hψ
  have h0 := PurityLatticeGap.eigen_nonneg_of_form (hform ψ (integrable_of_bdd hψm hψb)) hψ1 hK
  have he : σ = ‖kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ‖ := by rw [← hσ', abs_of_nonneg h0]
  exact ⟨ψ, hψm, ⟨Bψ, hψb⟩, hψ1, horth, fun z => by rw [hK z, he]⟩

end Abstract

section Wilson

open MassGap.CompactGauge MassGap.RectWilson MassGap.RectWilsonG MassGap.RectTransferG
  MassGap.GaugeGroup MassGap.PurityHaarProjection

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ}

/-- **`λ₁` of the Wilson transfer kernel.** With `λ₀ = ‖K‖ > 0` and its eigenfunction `φ ≥ m > 0`,
there is `λ₁` with `0 ≤ λ₁ ≤ τ λ₀`, `τ = tanh(β tpMax (1 − q/d)/2)`, such that every excited
eigenvalue has `|σ| ≤ λ₁`, and `λ₁ > 0` is the eigenvalue of an excited eigenfunction. -/
theorem lam1 [Nontrivial G] {β : ℝ} (hβ : 0 < β) (hT : ∀ j, 2 ≤ T j) :
    0 < ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
      (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖ ∧
    ∃ φ : (SpT μ T → G) → ℝ, Continuous φ ∧ (∃ m, 0 < m ∧ ∀ x, m ≤ φ x) ∧
      ∫ x, φ x ^ 2 ∂(hSG G μ T) = 1 ∧
      (∀ z, ∫ y, kTG G μ T β z y * φ y ∂(hSG G μ T) =
        ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
          (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖ * φ z) ∧
      ∃ l1 : ℝ, 0 ≤ l1 ∧
        l1 ≤ tanh (β * RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G) / 2) *
          ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
            (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖ ∧
        (∀ (g : (SpT μ T → G) → ℝ), Measurable g → ∀ (Bg : ℝ), (∀ x, |g x| ≤ Bg) →
          ∫ x, g x ^ 2 ∂(hSG G μ T) = 1 → ∫ x, φ x * g x ∂(hSG G μ T) = 0 →
          ∀ σ : ℝ, (∀ z, ∫ y, kTG G μ T β z y * g y ∂(hSG G μ T) = σ * g z) → |σ| ≤ l1) ∧
        (0 < l1 → ∃ ψ : (SpT μ T → G) → ℝ, Measurable ψ ∧ (∃ Bψ, ∀ x, |ψ x| ≤ Bψ) ∧
          ∫ x, ψ x ^ 2 ∂(hSG G μ T) = 1 ∧ ∫ x, φ x * ψ x ∂(hSG G μ T) = 0 ∧
          ∀ z, ∫ y, kTG G μ T β z y * ψ y ∂(hSG G μ T) = l1 * ψ z) := by
  obtain ⟨hpos, φ, hφc, hm, hφb, hφ1, heig, hR⟩ :=
    PurityRectWilsonFixed.norm_rem_le (G := G) (μ := μ) (T := T) hβ hT
  have hk : Bdd (kTG G μ T β) := ⟨(continuous_kTG β).measurable, 1, abs_kTG_le hβ.le⟩
  have hr := hk.rem (c := ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
    (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖) hφc.measurable hφb
  obtain ⟨Cr, hCr⟩ := hr.bdd
  have hCr0 : 0 ≤ Cr := (abs_nonneg _).trans (hCr (fun _ => 1) (fun _ => 1))
  obtain ⟨hall, hatt⟩ := top (μ := hSG G μ T) (continuous_kTG β) (abs_kTG_le hβ.le)
    (kTG_symm β) hφc hφb hφ1 heig
    (fun _ hg => PurityKernelPositive.kTG_quad_nonneg hβ.le hg) hr.meas hCr0 hCr
  exact ⟨hpos, φ, hφc, hm, hφ1, heig, _, norm_nonneg _, hR Cr hr.meas hCr0 hCr, hall, hatt⟩

end Wilson

end MassGap.PurityExcitedTop

#print axioms MassGap.PurityExcitedTop.top
#print axioms MassGap.PurityExcitedTop.lam1
