import Mathlib
import MassGap.KernelEigen
import MassGap.PurityKernelPositive
import MassGap.PurityRectWilsonFixed

/-!
# MassGap.PurityLatticeGap — the lattice energy gap of the Wilson transfer kernel

Theorem 5.2 (last sentence) and (5.6) in Theorem 5.4 of D. Bhattacharjee, U. Bhattacharya,
J. M. Lockwood, T. Romanov, I. J. Sessford and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills
Theory at Weak Coupling* (research draft, 15 November 2026, <https://github.com/anaxia-research/4Y-M>,
commit 8e01510, `Paper-2/Paper-2.pdf`), for the gauge-projected transfer kernel `RectTransferG.kTG`
of the rectangular torus over a nontrivial gauge group `G`, with `β > 0` and every spatial extent
at least `2`.

The top eigenvalue is `λ₀ = ‖K‖`, with eigenfunction `φ ≥ m > 0`
(`PurityRectWilsonFixed.norm_rem_le`). Every other eigenfunction `g` (bounded, measurable,
`∫ g² = 1`, `g ⊥ φ`) with eigenvalue `σ ≠ 0` has `0 < σ ≤ τ λ₀ < λ₀`,
`τ = tanh(β tpMax (1 − q/d)/2)`, so `λ₀` is simple and the energy `−log(σ/λ₀)` is at least `−log τ > 0`. Positivity `σ > 0` is the form bound
`PurityKernelPositive.kTG_quad_nonneg`; `σ ≤ τ λ₀` is `|σ| ≤ ‖R‖ ≤ τ λ₀` for the deflated operator.

* `abs_eigen_le_norm` (any probability space): a bounded measurable pointwise eigenfunction with
  `∫ g² = 1` of a bounded measurable kernel has `|σ| ≤ ‖K‖` for the `L²` operator.
* `eigen_nonneg_of_form`: if the form of `k` at `g` is nonnegative, `∫ g² = 1` and `g` is a
  pointwise eigenfunction, the eigenvalue is nonnegative.
* `rem_eigen`: an eigenfunction of `k` orthogonal to `φ` is an eigenfunction of `rem k c φ` with
  the same eigenvalue.
* `excited`: `0 < σ ≤ τ λ₀ < λ₀` and `−log τ ≤ −log(σ/λ₀)` for every excited eigenfunction of
  `kTG`.
* `gap_pos`: `−log τ > 0`.
* `tau_le`, `gap_uniform` (second inequality of (5.6)): `τ ≤ tanh(β tpMax/2)` and
  `0 < −log tanh(β tpMax/2) ≤ −log τ`, so every excited energy is at least `−log tanh(β tpMax/2)`.
-/

namespace MassGap.PurityLatticeGap

open MeasureTheory Real MassGap MassGap.SlabKernelOperator MassGap.KernelPower

section Abstract

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- A bounded measurable pointwise eigenfunction with `∫ g² = 1` has `|σ| ≤ ‖K‖`. -/
theorem abs_eigen_le_norm {h : X → X → ℝ} {C : ℝ} (hm : Measurable (Function.uncurry h))
    (hC0 : 0 ≤ C) (hb : ∀ x y, |h x y| ≤ C) {g : X → ℝ} (hgm : Measurable g) {Bg : ℝ}
    (hgb : ∀ x, |g x| ≤ Bg) (hg1 : ∫ x, g x ^ 2 ∂μ = 1) {σ : ℝ}
    (hg : ∀ z, ∫ y, h z y * g y ∂μ = σ * g z) :
    |σ| ≤ ‖kernelCLM h C hm hC0 hb μ μ‖ := by
  have hmem : MemLp g 2 μ := MemLp.of_bound hgm.aestronglyMeasurable Bg
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hgb x)
  have hf2 : ‖hmem.toLp g‖ ^ 2 = 1 := by
    rw [SlabTransferAdjoint.norm_sq_eq_integral, ← hg1]
    exact integral_congr_ae (by filter_upwards [hmem.coeFn_toLp] with x hx; rw [hx])
  have hf1 : ‖hmem.toLp g‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hf2
  have hRf : kernelCLM h C hm hC0 hb μ μ (hmem.toLp g) = σ • hmem.toLp g := by
    apply Lp.ext
    filter_upwards [coeFn_kernelCLM h C hm hC0 hb μ μ (hmem.toLp g),
      Lp.coeFn_smul σ (hmem.toLp g), hmem.coeFn_toLp] with z h1 h2 h3
    rw [h1, h2, Pi.smul_apply, smul_eq_mul, h3]
    unfold kernelFun
    rw [← hg z]
    exact integral_congr_ae (by filter_upwards [hmem.coeFn_toLp] with y hy; rw [hy])
  calc |σ| = ‖σ • hmem.toLp g‖ := by rw [norm_smul, hf1, mul_one, Real.norm_eq_abs]
    _ = ‖kernelCLM h C hm hC0 hb μ μ (hmem.toLp g)‖ := by rw [hRf]
    _ ≤ ‖kernelCLM h C hm hC0 hb μ μ‖ * ‖hmem.toLp g‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖kernelCLM h C hm hC0 hb μ μ‖ := by rw [hf1, mul_one]

omit [IsProbabilityMeasure μ] in
/-- A nonnegative form at a normalized pointwise eigenfunction gives a nonnegative eigenvalue. -/
theorem eigen_nonneg_of_form {k : X → X → ℝ} {g : X → ℝ}
    (hform : 0 ≤ ∫ x, (∫ y, k x y * g y ∂μ) * g x ∂μ) (hg1 : ∫ x, g x ^ 2 ∂μ = 1) {σ : ℝ}
    (hg : ∀ z, ∫ y, k z y * g y ∂μ = σ * g z) : 0 ≤ σ := by
  have e : (fun x => (∫ y, k x y * g y ∂μ) * g x) = fun x => σ * g x ^ 2 := by
    funext x; rw [hg x]; ring
  rw [e, integral_const_mul, hg1, mul_one] at hform
  exact hform

/-- An eigenfunction of `k` orthogonal to `φ` is an eigenfunction of `rem k c φ`. -/
theorem rem_eigen {k : X → X → ℝ} (hk : Bdd k) {φ : X → ℝ} (hφm : Measurable φ) {B : ℝ}
    (hφb : ∀ x, |φ x| ≤ B) {g : X → ℝ} (hgm : Measurable g) {Bg : ℝ} (hgb : ∀ x, |g x| ≤ Bg)
    (horth : ∫ x, φ x * g x ∂μ = 0) {σ : ℝ} (hg : ∀ z, ∫ y, k z y * g y ∂μ = σ * g z) (c : ℝ)
    (z : X) : ∫ y, rem k c φ z y * g y ∂μ = σ * g z := by
  obtain ⟨Ck, hCk⟩ := hk.bdd
  have e : (fun y => rem k c φ z y * g y) = fun y => k z y * g y - (c * φ z) * (φ y * g y) := by
    funext y; unfold MassGap.KernelPower.rem; ring
  rw [e, integral_sub, integral_const_mul, horth, hg z, mul_zero, sub_zero]
  · exact integrable_mul_of_bdd (hk.row z) hgm (hCk z) hgb
  · exact (integrable_mul_of_bdd hφm hgm hφb hgb).const_mul _

end Abstract

section Wilson

open MassGap.CompactGauge MassGap.RectWilson MassGap.RectWilsonG MassGap.RectTransferG
  MassGap.GaugeGroup MassGap.PurityHaarProjection

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ}

/-- `−log tanh(β tpMax (1 − q/d)/2) > 0` for a nontrivial gauge group, `β > 0` and spatial
extents at least `2`. -/
theorem gap_pos [Nontrivial G] {β : ℝ} (hβ : 0 < β) (hT : ∀ j, 2 ≤ T j) :
    0 < -log (tanh (β * RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G) / 2)) := by
  have hlt := PurityRectWilsonFixed.hlt (G := G) hβ hT
  exact PurityWilson.neg_log_tanh_pos (by linarith)

/-- (5.6), second inequality: `tanh(β tpMax (1 − q/d)/2) ≤ tanh(β tpMax/2)` for `β ≥ 0`. -/
theorem tau_le {β : ℝ} (hβ : 0 ≤ β) :
    tanh (β * RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G) / 2) ≤
      tanh (β * RectTransfer.tpMax μ T / 2) := by
  refine PurityWilson.tanh_mono ?_
  have hd : (0 : ℝ) < dim G := Nat.cast_pos.2 dim_pos
  have hq : 0 ≤ (fixedRank G : ℝ) / dim G := div_nonneg (Nat.cast_nonneg _) hd.le
  have ht : 0 ≤ β * RectTransfer.tpMax μ T := mul_nonneg hβ (by unfold RectTransfer.tpMax; positivity)
  nlinarith

/-- `0 < −log tanh(β tpMax/2) ≤ −log tanh(β tpMax (1 − q/d)/2)` for a nontrivial gauge group,
`β > 0` and spatial extents at least `2`. -/
theorem gap_uniform [Nontrivial G] {β : ℝ} (hβ : 0 < β) (hT : ∀ j, 2 ≤ T j) :
    0 < -log (tanh (β * RectTransfer.tpMax μ T / 2)) ∧
      -log (tanh (β * RectTransfer.tpMax μ T / 2)) ≤
        -log (tanh (β * RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G) / 2)) := by
  have hlt := PurityRectWilsonFixed.hlt (G := G) hβ hT
  have h2 := PurityRectWilson.tpMax_pos (μ := μ) fun j => (by have := hT j; omega : 0 < T j)
  refine ⟨PurityWilson.neg_log_tanh_pos (by positivity), ?_⟩
  have := log_le_log (PurityWilson.tanh_pos (by linarith)) (tau_le (G := G) (μ := μ) (T := T) hβ.le)
  linarith

/-- **The lattice energy gap of the Wilson transfer kernel.** `λ₀ = ‖K‖ > 0` has a continuous
eigenfunction `φ ≥ m > 0`, `∫ φ² = 1`, and every other eigenfunction `g` (bounded, measurable,
`∫ g² = 1`, `g ⊥ φ`) with eigenvalue `σ ≠ 0` has `0 < σ ≤ τ λ₀ < λ₀` (so `λ₀` is simple) and
energy `−log(σ/λ₀) ≥ −log τ`, `τ = tanh(β tpMax (1 − q/d)/2)`. -/
theorem excited [Nontrivial G] {β : ℝ} (hβ : 0 < β) (hT : ∀ j, 2 ≤ T j) :
    0 < ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ.le)
        (hSG G μ T) (hSG G μ T)‖ ∧
      ∃ φ : (SpT μ T → G) → ℝ, Continuous φ ∧ (∃ m, 0 < m ∧ ∀ x, m ≤ φ x) ∧
        ∫ x, φ x ^ 2 ∂(hSG G μ T) = 1 ∧
        (∀ z, ∫ y, kTG G μ T β z y * φ y ∂(hSG G μ T) =
          ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
            (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖ * φ z) ∧
        ∀ (g : (SpT μ T → G) → ℝ), Measurable g → ∀ (Bg : ℝ), (∀ x, |g x| ≤ Bg) →
          ∫ x, g x ^ 2 ∂(hSG G μ T) = 1 → ∫ x, φ x * g x ∂(hSG G μ T) = 0 →
          ∀ σ : ℝ, σ ≠ 0 → (∀ z, ∫ y, kTG G μ T β z y * g y ∂(hSG G μ T) = σ * g z) →
          0 < σ ∧
            σ ≤ tanh (β * RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G) / 2) *
              ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
                (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖ ∧
            σ < ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
                (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖ ∧
            -log (tanh (β * RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G) / 2)) ≤
              -log (σ / ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
                (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖) := by
  obtain ⟨hpos, φ, hφc, hm, hφb, hφ1, heig, hR⟩ :=
    PurityRectWilsonFixed.norm_rem_le (G := G) (μ := μ) (T := T) hβ hT
  refine ⟨hpos, φ, hφc, hm, hφ1, heig, fun g hgm Bg hgb hg1 horth σ hσ hg => ?_⟩
  have hint : Integrable g (hSG G μ T) := integrable_of_bdd hgm hgb
  have hσpos : 0 < σ :=
    lt_of_le_of_ne (eigen_nonneg_of_form (PurityKernelPositive.kTG_quad_nonneg hβ.le hint) hg1 hg)
      (Ne.symm hσ)
  have hk : Bdd (kTG G μ T β) := ⟨(continuous_kTG β).measurable, 1, abs_kTG_le hβ.le⟩
  have hφm := hφc.measurable
  have hr := hk.rem (c := ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
    (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖) hφm hφb
  obtain ⟨Cr, hCr⟩ := hr.bdd
  have hCr0 : 0 ≤ Cr := (abs_nonneg _).trans (hCr (fun _ => 1) (fun _ => 1))
  have h1 := abs_eigen_le_norm hr.meas hCr0 hCr hgm hgb hg1 (rem_eigen hk hφm hφb hgm hgb horth hg _)
  have hστ := (le_abs_self σ).trans (h1.trans (hR Cr hr.meas hCr0 hCr))
  refine ⟨hσpos, hστ, hστ.trans_lt ((mul_lt_iff_lt_one_left hpos).2
    (PurityWilson.tanh_lt_one _)), ?_⟩
  have hdiv : σ / ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
      (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖ ≤
      tanh (β * RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G) / 2) := by
    rw [div_le_iff₀ hpos]; exact hστ
  have := log_le_log (div_pos hσpos hpos) hdiv
  linarith

end Wilson

end MassGap.PurityLatticeGap

#print axioms MassGap.PurityLatticeGap.abs_eigen_le_norm
#print axioms MassGap.PurityLatticeGap.eigen_nonneg_of_form
#print axioms MassGap.PurityLatticeGap.rem_eigen
#print axioms MassGap.PurityLatticeGap.gap_pos
#print axioms MassGap.PurityLatticeGap.tau_le
#print axioms MassGap.PurityLatticeGap.gap_uniform
#print axioms MassGap.PurityLatticeGap.excited
