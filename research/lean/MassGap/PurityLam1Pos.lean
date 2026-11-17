import Mathlib
import MassGap.PurityExcitedTop
import MassGap.SliceKernelDefiniteG
import MassGap.PurityVacuumMean

/-!
# MassGap.PurityLam1Pos — the largest excited eigenvalue is positive

`λ₁ > 0` for the Wilson slice transfer kernel `RectTransferG.kTG`, every nontrivial compact gauge
group, in Theorems 5.2 and 5.4 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov,
I. J. Sessford and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling*
(research draft, 15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510,
`Paper-2/Paper-2.pdf`). `λ₁` is the norm of the deflated operator `R` of `rem k c φ = k − c φ ⊗ φ`
(`PurityExcitedTop`).

* `kernel_eq_of_norm_rem_eq_zero`, `form_eq_zero_of_norm_rem_eq_zero` (probability space): if
  `‖R‖ = 0`, then `∫ k(z, y) g(y) dy = c φ(z) ∫ φ g` almost everywhere for every bounded measurable
  `g`, and the form `∫ (∫ k(·, y) g(y) dy) g` vanishes on `g ⊥ φ`.
* `form_prod_eq`: the slice-kernel form over the product measure is the iterated form.
* `norm_rem_pos` (`β > 0`, spatial extents at least `2`, nontrivial `G`, any bounded measurable `φ`
  and any `c`): `‖R‖ > 0`. If `‖R‖ = 0`, the form vanishes on the gauge-invariant continuous
  `u = (∫ φ sp) − (∫ φ) sp` (or `u = 1` when `∫ φ = 0`), which is orthogonal to `φ`;
  `SliceKernelDefiniteG.sliceKernelG_form_eq_zero_iff` gives `u = 0`, so `sp ≡ sp(1) = 0`, against
  `∫ sp = n (1 − q/d) > 0` (`PurityVacuumMean.integral_spTG`, `PurityHaarProjection.fixedRank_lt`).
* `lam1_pos`: `PurityExcitedTop.lam1` with `0 < λ₁`, and `λ₁` the eigenvalue of an excited
  eigenfunction.
-/

namespace MassGap.PurityLam1Pos

open MeasureTheory Real MassGap MassGap.SlabKernelOperator MassGap.KernelPower

section Abstract

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- At `‖R‖ = 0`, `k` acts on a bounded measurable `g` as `c φ ⊗ φ`, almost everywhere. -/
theorem kernel_eq_of_norm_rem_eq_zero {k : X → X → ℝ} (hk : Bdd k) {c : ℝ} {φ : X → ℝ}
    (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B) {Cr : ℝ}
    (hrm : Measurable (Function.uncurry (rem k c φ))) (hCr0 : 0 ≤ Cr)
    (hrb : ∀ x y, |rem k c φ x y| ≤ Cr) (h0 : ‖kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ‖ = 0)
    {g : X → ℝ} (hgm : Measurable g) {Bg : ℝ} (hgb : ∀ x, |g x| ≤ Bg) :
    ∀ᵐ z ∂μ, ∫ y, k z y * g y ∂μ = c * φ z * ∫ y, φ y * g y ∂μ := by
  have hmem : MemLp g 2 μ := MemLp.of_bound hgm.aestronglyMeasurable Bg
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hgb x)
  have hR : kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ = 0 := norm_eq_zero.1 h0
  filter_upwards [coeFn_kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ (hmem.toLp g),
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)] with z h1 h2
  rw [hR, ContinuousLinearMap.zero_apply] at h1
  have e : kernelFun (rem k c φ) μ (hmem.toLp g : X → ℝ) z = ∫ y, rem k c φ z y * g y ∂μ := by
    unfold kernelFun
    exact integral_congr_ae (by filter_upwards [hmem.coeFn_toLp] with y hy; rw [hy])
  have hz : ∫ y, rem k c φ z y * g y ∂μ = 0 := by rw [← e, ← h1, h2]; rfl
  obtain ⟨Ck, hCk⟩ := hk.bdd
  have ex : (fun y => rem k c φ z y * g y) = fun y => k z y * g y - (c * φ z) * (φ y * g y) := by
    funext y; unfold MassGap.KernelPower.rem; ring
  rw [ex, integral_sub (integrable_mul_of_bdd (hk.row z) hgm (hCk z) hgb)
    ((integrable_mul_of_bdd hφm hgm hφb hgb).const_mul _), integral_const_mul, sub_eq_zero] at hz
  exact hz

/-- At `‖R‖ = 0` the form of `k` vanishes on every bounded measurable `g ⊥ φ`. -/
theorem form_eq_zero_of_norm_rem_eq_zero {k : X → X → ℝ} (hk : Bdd k) {c : ℝ} {φ : X → ℝ}
    (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B) {Cr : ℝ}
    (hrm : Measurable (Function.uncurry (rem k c φ))) (hCr0 : 0 ≤ Cr)
    (hrb : ∀ x y, |rem k c φ x y| ≤ Cr) (h0 : ‖kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ‖ = 0)
    {g : X → ℝ} (hgm : Measurable g) {Bg : ℝ} (hgb : ∀ x, |g x| ≤ Bg)
    (horth : ∫ y, φ y * g y ∂μ = 0) :
    ∫ z, (∫ y, k z y * g y ∂μ) * g z ∂μ = 0 := by
  refine integral_eq_zero_of_ae ?_
  filter_upwards [kernel_eq_of_norm_rem_eq_zero hk hφm hφb hrm hCr0 hrb h0 hgm hgb] with z hz
  rw [Pi.zero_apply, hz, horth, mul_zero, zero_mul]

end Abstract

section Wilson

open MassGap.CompactGauge MassGap.RectWilson MassGap.RectWilsonG MassGap.RectTransferG
  MassGap.GaugeGroup MassGap.PurityHaarProjection MassGap.SliceKernelDefiniteG
  MassGap.PurityVacuumMean

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ}

/-- The slice-kernel form over the product measure is the iterated form. -/
theorem form_prod_eq (β : ℝ) {u : (SpT μ T → G) → ℝ} (hu : Continuous u) :
    ∫ z, u z.1 * u z.2 * kTG G μ T β z.1 z.2 ∂((hSG G μ T).prod (hSG G μ T))
      = ∫ x, (∫ y, kTG G μ T β x y * u y ∂(hSG G μ T)) * u x ∂(hSG G μ T) := by
  have hc : Continuous fun z : (SpT μ T → G) × (SpT μ T → G) =>
      u z.1 * u z.2 * kTG G μ T β z.1 z.2 :=
    ((hu.comp continuous_fst).mul (hu.comp continuous_snd)).mul (continuous_kTG β)
  rw [integral_prod _ (KernelInjective.integrable_of_continuous hc)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only
  rw [← integral_mul_const]
  exact integral_congr_ae (ae_of_all _ fun y => by ring)

/-- **`λ₁ > 0`.** For `β > 0`, spatial extents at least `2` and a nontrivial gauge group, the
deflated operator `rem kTG c φ` has positive norm, for every bounded measurable `φ` and every `c`. -/
theorem norm_rem_pos [Nontrivial G] {β : ℝ} (hβ : 0 < β) (hT : ∀ j, 2 ≤ T j) {c : ℝ}
    {φ : (SpT μ T → G) → ℝ} (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B) {Cr : ℝ}
    (hrm : Measurable (Function.uncurry (rem (kTG G μ T β) c φ))) (hCr0 : 0 ≤ Cr)
    (hrb : ∀ x y, |rem (kTG G μ T β) c φ x y| ≤ Cr) :
    0 < ‖kernelCLM (rem (kTG G μ T β) c φ) Cr hrm hCr0 hrb (hSG G μ T) (hSG G μ T)‖ := by
  refine (norm_nonneg _).lt_of_ne' fun h0 => ?_
  have hk : Bdd (kTG G μ T β) := ⟨(continuous_kTG β).measurable, 1, abs_kTG_le hβ.le⟩
  have key : ∀ u : C(SpT μ T → G, ℝ), GaugeInvG ⇑u →
      ∫ x, φ x * u x ∂(hSG G μ T) = 0 → u = 0 := by
    intro u hinv horth
    obtain ⟨Bu, hBu⟩ := isCompact_univ.exists_bound_of_continuousOn u.continuous.continuousOn
    refine (sliceKernelG_form_eq_zero_iff hβ u hinv).1 ?_
    rw [form_prod_eq β u.continuous]
    exact form_eq_zero_of_norm_rem_eq_zero hk hφm hφb hrm hCr0 hrb h0 u.continuous.measurable
      (fun x => by simpa [Real.norm_eq_abs] using hBu x (Set.mem_univ x)) horth
  have hsc : Continuous fun V => spTG G μ T V := continuous_spG continuous_id
  obtain ⟨Bs, hBs⟩ := isCompact_univ.exists_bound_of_continuousOn hsc.continuousOn
  have hsb : ∀ V, |spTG G μ T V| ≤ Bs := fun V => by
    simpa [Real.norm_eq_abs] using hBs V (Set.mem_univ V)
  have hφi : Integrable φ (hSG G μ T) :=
    Integrable.of_bound hφm.aestronglyMeasurable B
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hφb x)
  have hφs : Integrable (fun x => φ x * spTG G μ T x) (hSG G μ T) :=
    integrable_mul_of_bdd hφm hsc.measurable hφb hsb
  generalize ha : ∫ x, φ x * spTG G μ T x ∂(hSG G μ T) = a
  generalize hb : ∫ x, φ x ∂(hSG G μ T) = b
  by_cases hb0 : b = 0
  · have h1 := key (ContinuousMap.const _ 1) (fun _ _ => rfl) (by
      simp only [ContinuousMap.const_apply, mul_one]
      rw [hb, hb0])
    exact one_ne_zero (DFunLike.congr_fun h1 1)
  · have hu := key ⟨fun V => a - b * spTG G μ T V, continuous_const.sub (continuous_const.mul hsc)⟩
      (fun A V => by
        show a - b * spTG G μ T (PurityKernelPositive.gaugeAct A V) = a - b * spTG G μ T V
        rw [sp_gaugeAct]) (by
        show ∫ x, φ x * (a - b * spTG G μ T x) ∂(hSG G μ T) = 0
        have e : (fun x => φ x * (a - b * spTG G μ T x))
            = fun x => a * φ x - b * (φ x * spTG G μ T x) := by
          funext x; ring
        rw [e, integral_sub (hφi.const_mul a) (hφs.const_mul b), integral_const_mul,
          integral_const_mul, hb, ha]
        ring)
    have h1 := DFunLike.congr_fun hu 1
    change a - b * spTG G μ T 1 = 0 at h1
    rw [spTG_one, mul_zero, sub_zero] at h1
    have hs0 : ∀ V, spTG G μ T V = 0 := fun V => by
      have h := DFunLike.congr_fun hu V
      change a - b * spTG G μ T V = 0 at h
      rw [h1, zero_sub, neg_eq_zero, mul_eq_zero] at h
      exact h.resolve_left hb0
    have hint := integral_spTG (G := G) hT
    simp only [hs0, integral_zero] at hint
    have hd : (0 : ℝ) < dim G := Nat.cast_pos.mpr dim_pos
    have hq : (fixedRank G : ℝ) / dim G < 1 := (div_lt_one hd).2 (Nat.cast_lt.2 fixedRank_lt)
    have hcard : 0 < Fintype.card (TT μ T) :=
      Fintype.card_pos_iff.2 ⟨fun j => ⟨0, by have := hT j; omega⟩⟩
    have hn : 0 < nPl μ T := by
      rw [nPl_eq]
      exact mul_pos (by norm_num) (Nat.cast_pos.2 hcard)
    exact (mul_pos hn (sub_pos.2 hq)).ne hint

/-- **`λ₁` of the Wilson transfer kernel is positive.** `PurityExcitedTop.lam1` with `0 < λ₁`:
`λ₀ = ‖K‖ > 0` with eigenfunction `φ ≥ m > 0`, and `0 < λ₁ ≤ τ λ₀`, `τ = tanh(β tpMax (1 − q/d)/2)`,
bounds every excited eigenvalue in absolute value and is the eigenvalue of an excited
eigenfunction. -/
theorem lam1_pos [Nontrivial G] {β : ℝ} (hβ : 0 < β) (hT : ∀ j, 2 ≤ T j) :
    0 < ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
      (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖ ∧
    ∃ φ : (SpT μ T → G) → ℝ, Continuous φ ∧ (∃ m, 0 < m ∧ ∀ x, m ≤ φ x) ∧
      ∫ x, φ x ^ 2 ∂(hSG G μ T) = 1 ∧
      (∀ z, ∫ y, kTG G μ T β z y * φ y ∂(hSG G μ T) =
        ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
          (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖ * φ z) ∧
      ∃ l1 : ℝ, 0 < l1 ∧
        l1 ≤ tanh (β * RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G) / 2) *
          ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
            (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖ ∧
        (∀ (g : (SpT μ T → G) → ℝ), Measurable g → ∀ (Bg : ℝ), (∀ x, |g x| ≤ Bg) →
          ∫ x, g x ^ 2 ∂(hSG G μ T) = 1 → ∫ x, φ x * g x ∂(hSG G μ T) = 0 →
          ∀ σ : ℝ, (∀ z, ∫ y, kTG G μ T β z y * g y ∂(hSG G μ T) = σ * g z) → |σ| ≤ l1) ∧
        ∃ ψ : (SpT μ T → G) → ℝ, Measurable ψ ∧ (∃ Bψ, ∀ x, |ψ x| ≤ Bψ) ∧
          ∫ x, ψ x ^ 2 ∂(hSG G μ T) = 1 ∧ ∫ x, φ x * ψ x ∂(hSG G μ T) = 0 ∧
          ∀ z, ∫ y, kTG G μ T β z y * ψ y ∂(hSG G μ T) = l1 * ψ z := by
  obtain ⟨hpos, φ, hφc, hm, hφb, hφ1, heig, hR⟩ :=
    PurityRectWilsonFixed.norm_rem_le (G := G) (μ := μ) (T := T) hβ hT
  have hk : Bdd (kTG G μ T β) := ⟨(continuous_kTG β).measurable, 1, abs_kTG_le hβ.le⟩
  have hr := hk.rem (c := ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
    (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖) hφc.measurable hφb
  obtain ⟨Cr, hCr⟩ := hr.bdd
  have hCr0 : 0 ≤ Cr := (abs_nonneg _).trans (hCr (fun _ => 1) (fun _ => 1))
  obtain ⟨hall, hatt⟩ := PurityExcitedTop.top (μ := hSG G μ T) (continuous_kTG β)
    (abs_kTG_le hβ.le) (kTG_symm β) hφc hφb hφ1 heig
    (fun _ hg => PurityKernelPositive.kTG_quad_nonneg hβ.le hg) hr.meas hCr0 hCr
  have hl := norm_rem_pos hβ hT hφc.measurable hφb hr.meas hCr0 hCr
  exact ⟨hpos, φ, hφc, hm, hφ1, heig, _, hl, hR Cr hr.meas hCr0 hCr, hall, hatt hl⟩

end Wilson

end MassGap.PurityLam1Pos

#print axioms MassGap.PurityLam1Pos.kernel_eq_of_norm_rem_eq_zero
#print axioms MassGap.PurityLam1Pos.form_eq_zero_of_norm_rem_eq_zero
#print axioms MassGap.PurityLam1Pos.form_prod_eq
#print axioms MassGap.PurityLam1Pos.norm_rem_pos
#print axioms MassGap.PurityLam1Pos.lam1_pos
