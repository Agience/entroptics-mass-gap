import Mathlib
import MassGap.KernelPower
import MassGap.PurityWilson
import MassGap.PurityThermalCompact

/-!
# MassGap.PurityWilsonCompact — the Wilson-type kernel in Theorem 5.2 and (6.2), (6.3)

Theorem 5.2, Lemma 5.3, Theorem 5.4 and Proposition 6.1 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood,
T. Romanov, I. J. Sessford and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak
Coupling* (research draft, 15 November 2026, <https://github.com/anaxia-research/4Y-M>,
commit 8e01510, `Paper-2/Paper-2.pdf`).

`X` is a compact, second countable Borel space with a probability measure `μ`, and `G` is a
compact Borel space with a probability measure `ν`. The kernel is the average
`A x y = ∫ exp (F x y g) dν(g)` of a jointly continuous exponent `F`, with
`cl ≤ ∫ F x y dν`, `F ≤ cu`, `cl < cu`, and a measure-preserving `σ : G ≃ᵐ G` with
`F y x g = F x y (σ g)`. `k x y = D(x) A(x, y) D(y)` with `D` continuous, `0 < dl ≤ D ≤ du`.

* `integrable_cont`: a continuous function on `G` is `ν`-integrable; `F_cont`, `expF_cont`:
  `F x y` and `exp ∘ F x y` are continuous on `G`.
* `A_cont`, `A_symm`: `A` is continuous and symmetric.
* `A_lower`, `A_upper`: (5.5), `exp cl ≤ A ≤ exp cu` (Jensen, and the pointwise bound).
* `norm_rem_le`, `trace_excess`, `defect`: Theorem 5.2 as `‖R‖ ≤ τ‖K‖`, (6.2) and (6.3) at
  `T = 2j`, `j ≥ 1`, with `τ = (exp cu − exp cl)/(exp cu + exp cl)`.
* `wilson_lt`, `wilson_norm_rem_le`, `wilson_trace_excess`, `wilson_defect`: the same at
  `cu = β·3L³`, `cl = β·3L³·q/d`, `0 < β`, `0 < L`, `0 < d`, `q < d`, where
  `τ = tanh(3βL³(1 − q/d)/2)` (`PurityWilson.wilson_ratio`).
* `tail_mono`, `wilson_defect_uniform`: for `0 ≤ q`, (6.3) with the uniform ratio
  `tanh(3βL³/2)` of Theorem 5.4.
-/

namespace MassGap.PurityWilsonCompact

open MeasureTheory Real MassGap.SlabKernelOperator MassGap.KernelPower

section Kernel

variable {G : Type*} [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G]
  [OpensMeasurableSpace G] {ν : Measure G} [IsProbabilityMeasure ν]

/-- A continuous function on the compact space `G` is `ν`-integrable. -/
theorem integrable_cont {f : G → ℝ} (hf : Continuous f) : Integrable f ν := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact integrable_of_bdd hf.measurable (C := B) fun g => by
    simpa [Real.norm_eq_abs] using hB g (Set.mem_univ g)

variable {X : Type*} [TopologicalSpace X] {F : X → X → G → ℝ}
  (hF : Continuous fun p : (X × X) × G => F p.1.1 p.1.2 p.2)
  {A : X → X → ℝ} (hAdef : ∀ x y, A x y = ∫ g, exp (F x y g) ∂ν)

include hF in
omit [CompactSpace G] [MeasurableSpace G] [OpensMeasurableSpace G] in
theorem F_cont (x y : X) : Continuous (F x y) :=
  hF.comp ((continuous_const (y := (x, y))).prodMk continuous_id)

include hF in
omit [CompactSpace G] [MeasurableSpace G] [OpensMeasurableSpace G] in
theorem expF_cont (x y : X) : Continuous fun g => exp (F x y g) :=
  continuous_exp.comp (F_cont hF x y)

include hF hAdef in
/-- `A` is jointly continuous. -/
theorem A_cont [CompactSpace X] [SecondCountableTopology X] : Continuous (Function.uncurry A) := by
  have e : Function.uncurry A = fun p : X × X => ∫ g, exp (F p.1 p.2 g) ∂ν :=
    funext fun p => hAdef p.1 p.2
  rw [e]
  obtain ⟨B, hB⟩ :=
    isCompact_univ.exists_bound_of_continuousOn (continuous_exp.comp hF).continuousOn
  refine continuous_of_dominated (bound := fun _ => B)
    (fun p => (expF_cont hF p.1 p.2).aestronglyMeasurable)
    (fun p => ae_of_all _ fun g => hB (p, g) (Set.mem_univ _)) (integrable_const B)
    (ae_of_all _ fun g => ?_)
  exact continuous_exp.comp (hF.comp (continuous_id.prodMk continuous_const))

omit [TopologicalSpace G] [CompactSpace G] [OpensMeasurableSpace G] [IsProbabilityMeasure ν]
  [TopologicalSpace X] in
include hAdef in
/-- `A` is symmetric when `F y x g = F x y (σ g)` for a measure-preserving `σ`. -/
theorem A_symm {σ : G ≃ᵐ G} (hσ : MeasurePreserving σ ν ν)
    (hFs : ∀ x y g, F y x g = F x y (σ g)) : ∀ x y, A x y = A y x := fun x y => by
  rw [hAdef x y, hAdef y x]
  calc ∫ g, exp (F x y g) ∂ν = ∫ g, exp (F x y (σ g)) ∂ν :=
        (hσ.integral_comp' (fun g => exp (F x y g))).symm
    _ = ∫ g, exp (F y x g) ∂ν := by
        congr 1
        funext g
        rw [hFs x y g]

include hF hAdef in
/-- (5.5), lower bound: `exp cl ≤ A` when `cl ≤ ∫ F x y dν` (Jensen). -/
theorem A_lower {cl : ℝ} (hcl : ∀ x y, cl ≤ ∫ g, F x y g ∂ν) : ∀ x y, exp cl ≤ A x y :=
  fun x y => by
    rw [hAdef]
    exact (exp_le_exp.2 (hcl x y)).trans
      (PurityWilson.kernel_lower (integrable_cont (F_cont hF x y))
        (integrable_cont (expF_cont hF x y)) rfl)

include hF hAdef in
/-- (5.5), upper bound: `A ≤ exp cu` when `F ≤ cu`. -/
theorem A_upper {cu : ℝ} (hcu : ∀ x y g, F x y g ≤ cu) : ∀ x y, A x y ≤ exp cu :=
  fun x y => by
    rw [hAdef]
    exact PurityWilson.kernel_upper (integrable_cont (expF_cont hF x y)) (hcu x y)

end Kernel

/-- `s^T/(1 − s²)` is monotone on `[0, 1)`. -/
theorem tail_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) (T : ℕ) :
    s ^ T / (1 - s ^ 2) ≤ t ^ T / (1 - t ^ 2) := by
  have h1 : 0 < 1 - t ^ 2 := by nlinarith
  have h2 : 1 - t ^ 2 ≤ 1 - s ^ 2 := by nlinarith
  calc s ^ T / (1 - s ^ 2) ≤ t ^ T / (1 - s ^ 2) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ hs hst T) (h1.trans_le h2).le
    _ ≤ t ^ T / (1 - t ^ 2) := div_le_div_of_nonneg_left (pow_nonneg (hs.trans hst) T) h1 h2

/-- `β·3L³·q/d < β·3L³` for `0 < β`, `0 < L`, `0 < d`, `q < d`. -/
theorem wilson_lt {β L q d : ℝ} (hβ : 0 < β) (hL : 0 < L) (hd : 0 < d) (hqd : q < d) :
    β * (3 * L ^ 3) * q / d < β * (3 * L ^ 3) := by
  have hM : 0 < β * (3 * L ^ 3) := by positivity
  have h1 : q / d < 1 := (div_lt_one hd).2 hqd
  calc β * (3 * L ^ 3) * q / d = β * (3 * L ^ 3) * (q / d) := by ring
    _ < β * (3 * L ^ 3) * 1 := mul_lt_mul_of_pos_left h1 hM
    _ = β * (3 * L ^ 3) := mul_one _

section Compact

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {G : Type*} [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {ν : Measure G} [IsProbabilityMeasure ν]
  {D : X → ℝ} (hDc : Continuous D) {dl du : ℝ} (hdl : 0 < dl) (hDl : ∀ x, dl ≤ D x)
  (hDu : ∀ x, D x ≤ du)
  {F : X → X → G → ℝ} (hF : Continuous fun p : (X × X) × G => F p.1.1 p.1.2 p.2)
  {σ : G ≃ᵐ G} (hσ : MeasurePreserving σ ν ν) (hFs : ∀ x y g, F y x g = F x y (σ g))
  {cl cu : ℝ} (hcl : ∀ x y, cl ≤ ∫ g, F x y g ∂ν) (hcu : ∀ x y g, F x y g ≤ cu) (hlt : cl < cu)
  {A : X → X → ℝ} (hAdef : ∀ x y, A x y = ∫ g, exp (F x y g) ∂ν)
  {k : X → X → ℝ} (hkdef : ∀ x y, k x y = D x * A x y * D y)
  {C : ℝ} (hkm : Measurable (Function.uncurry k)) (hC0 : 0 ≤ C) (hkb : ∀ x y, |k x y| ≤ C)

include hDc hdl hDl hDu hF hσ hFs hcl hcu hlt hAdef hkdef in
/-- **Theorem 5.2 for the averaged kernel.** `‖K‖ > 0` is an eigenvalue with a continuous
eigenfunction `φ ≥ m > 0`, and the deflated operator satisfies `‖R‖ ≤ τ‖K‖`,
`τ = (exp cu − exp cl)/(exp cu + exp cl)`. -/
theorem norm_rem_le :
    0 < ‖kernelCLM k C hkm hC0 hkb μ μ‖ ∧
      ∃ φ : X → ℝ, Continuous φ ∧ (∃ m, 0 < m ∧ ∀ x, m ≤ φ x) ∧
        (∀ x, |φ x| ≤ C / ‖kernelCLM k C hkm hC0 hkb μ μ‖) ∧ ∫ x, φ x ^ 2 ∂μ = 1 ∧
        (∀ z, ∫ y, k z y * φ y ∂μ = ‖kernelCLM k C hkm hC0 hkb μ μ‖ * φ z) ∧
        ∀ (Cr : ℝ) (hrm : Measurable (Function.uncurry (rem k ‖kernelCLM k C hkm hC0 hkb μ μ‖ φ)))
          (hCr0 : 0 ≤ Cr) (hrb : ∀ x y, |rem k ‖kernelCLM k C hkm hC0 hkb μ μ‖ φ x y| ≤ Cr),
          ‖kernelCLM (rem k ‖kernelCLM k C hkm hC0 hkb μ μ‖ φ) Cr hrm hCr0 hrb μ μ‖
            ≤ (exp cu - exp cl) / (exp cu + exp cl) * ‖kernelCLM k C hkm hC0 hkb μ μ‖ := by
  have h := PurityThermalCompact.norm_rem_le (μ := μ) hDc hdl hDl hDu (A_cont hF hAdef)
    (A_symm hAdef hσ hFs) (exp_pos cl) (exp_lt_exp.2 hlt) (A_lower hF hAdef hcl)
    (A_upper hF hAdef hcu) hkdef hkm hC0 hkb
  rwa [PurityThermalCompact.tau_eq (b := exp cu) (exp_pos cl)] at h

include hDc hdl hDl hDu hF hσ hFs hcl hcu hlt hAdef hkdef in
/-- **(6.2) for the averaged kernel**, `T = 2j`, `j ≥ 1`. -/
theorem trace_excess (j : ℕ) (hj : 1 ≤ j) :
    let τ := (exp cu - exp cl) / (exp cu + exp cl)
    traceSeq μ k (2 * j) / ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ (2 * j) - 1
      ≤ τ ^ (2 * j) / (1 - τ ^ 2) := by
  have h := PurityThermalCompact.trace_excess_compact (μ := μ) hDc hdl hDl hDu (A_cont hF hAdef)
    (A_symm hAdef hσ hFs) (exp_pos cl) (exp_lt_exp.2 hlt) (A_lower hF hAdef hcl)
    (A_upper hF hAdef hcu) hkdef hkm hC0 hkb j hj
  simp only at h ⊢
  rwa [PurityThermalCompact.tau_eq (b := exp cu) (exp_pos cl)] at h

include hDc hdl hDl hDu hF hσ hFs hcl hcu hlt hAdef hkdef hkm hC0 hkb in
/-- **(6.3) for the averaged kernel**, `ψ_T ≤ 2 log (1 + τ^T/(1 − τ²))`, `T = 2j`, `j ≥ 1`. -/
theorem defect (j : ℕ) (hj : 1 ≤ j) :
    let τ := (exp cu - exp cl) / (exp cu + exp cl)
    DoublingPower.defect (traceSeq μ k) (2 * j) ≤ 2 * Real.log (1 + τ ^ (2 * j) / (1 - τ ^ 2)) := by
  have h := PurityThermalCompact.defect_compact (μ := μ) hDc hdl hDl hDu (A_cont hF hAdef)
    (A_symm hAdef hσ hFs) (exp_pos cl) (exp_lt_exp.2 hlt) (A_lower hF hAdef hcl)
    (A_upper hF hAdef hcu) hkdef hkm hC0 hkb j hj
  simp only at h ⊢
  rwa [PurityThermalCompact.tau_eq (b := exp cu) (exp_pos cl)] at h

end Compact

section Wilson

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {G : Type*} [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {ν : Measure G} [IsProbabilityMeasure ν]
  {D : X → ℝ} (hDc : Continuous D) {dl du : ℝ} (hdl : 0 < dl) (hDl : ∀ x, dl ≤ D x)
  (hDu : ∀ x, D x ≤ du)
  {F : X → X → G → ℝ} (hF : Continuous fun p : (X × X) × G => F p.1.1 p.1.2 p.2)
  {σ : G ≃ᵐ G} (hσ : MeasurePreserving σ ν ν) (hFs : ∀ x y g, F y x g = F x y (σ g))
  {β L q d : ℝ} (hβ : 0 < β) (hL : 0 < L) (hd : 0 < d) (hqd : q < d)
  (hcl : ∀ x y, β * (3 * L ^ 3) * q / d ≤ ∫ g, F x y g ∂ν)
  (hcu : ∀ x y g, F x y g ≤ β * (3 * L ^ 3))
  {A : X → X → ℝ} (hAdef : ∀ x y, A x y = ∫ g, exp (F x y g) ∂ν)
  {k : X → X → ℝ} (hkdef : ∀ x y, k x y = D x * A x y * D y)
  {C : ℝ} (hkm : Measurable (Function.uncurry k)) (hC0 : 0 ≤ C) (hkb : ∀ x y, |k x y| ≤ C)

include hDc hdl hDl hDu hF hσ hFs hβ hL hd hqd hcl hcu hAdef hkdef in
/-- **Theorem 5.4, operator form.** For the Wilson-type kernel, `‖R‖ ≤ tanh(3βL³(1 − q/d)/2)‖K‖`. -/
theorem wilson_norm_rem_le :
    0 < ‖kernelCLM k C hkm hC0 hkb μ μ‖ ∧
      ∃ φ : X → ℝ, Continuous φ ∧ (∃ m, 0 < m ∧ ∀ x, m ≤ φ x) ∧
        (∀ x, |φ x| ≤ C / ‖kernelCLM k C hkm hC0 hkb μ μ‖) ∧ ∫ x, φ x ^ 2 ∂μ = 1 ∧
        (∀ z, ∫ y, k z y * φ y ∂μ = ‖kernelCLM k C hkm hC0 hkb μ μ‖ * φ z) ∧
        ∀ (Cr : ℝ) (hrm : Measurable (Function.uncurry (rem k ‖kernelCLM k C hkm hC0 hkb μ μ‖ φ)))
          (hCr0 : 0 ≤ Cr) (hrb : ∀ x y, |rem k ‖kernelCLM k C hkm hC0 hkb μ μ‖ φ x y| ≤ Cr),
          ‖kernelCLM (rem k ‖kernelCLM k C hkm hC0 hkb μ μ‖ φ) Cr hrm hCr0 hrb μ μ‖
            ≤ tanh (3 * β * L ^ 3 * (1 - q / d) / 2) * ‖kernelCLM k C hkm hC0 hkb μ μ‖ := by
  have h := norm_rem_le (μ := μ) hDc hdl hDl hDu hF hσ hFs hcl hcu (wilson_lt hβ hL hd hqd)
    hAdef hkdef hkm hC0 hkb
  rwa [PurityWilson.wilson_ratio β L q d hd.ne'] at h

include hDc hdl hDl hDu hF hσ hFs hβ hL hd hqd hcl hcu hAdef hkdef in
/-- **(6.2) for the Wilson-type kernel**, `τ = tanh(3βL³(1 − q/d)/2)`, `T = 2j`, `j ≥ 1`. -/
theorem wilson_trace_excess (j : ℕ) (hj : 1 ≤ j) :
    let τ := tanh (3 * β * L ^ 3 * (1 - q / d) / 2)
    traceSeq μ k (2 * j) / ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ (2 * j) - 1
      ≤ τ ^ (2 * j) / (1 - τ ^ 2) := by
  have h := trace_excess (μ := μ) hDc hdl hDl hDu hF hσ hFs hcl hcu (wilson_lt hβ hL hd hqd)
    hAdef hkdef hkm hC0 hkb j hj
  simp only at h ⊢
  rwa [PurityWilson.wilson_ratio β L q d hd.ne'] at h

include hDc hdl hDl hDu hF hσ hFs hβ hL hd hqd hcl hcu hAdef hkdef hkm hC0 hkb in
/-- **(6.3) for the Wilson-type kernel**, `ψ_T ≤ 2 log (1 + τ^T/(1 − τ²))`,
`τ = tanh(3βL³(1 − q/d)/2)`, `T = 2j`, `j ≥ 1`. -/
theorem wilson_defect (j : ℕ) (hj : 1 ≤ j) :
    let τ := tanh (3 * β * L ^ 3 * (1 - q / d) / 2)
    DoublingPower.defect (traceSeq μ k) (2 * j) ≤ 2 * Real.log (1 + τ ^ (2 * j) / (1 - τ ^ 2)) := by
  have h := defect (μ := μ) hDc hdl hDl hDu hF hσ hFs hcl hcu (wilson_lt hβ hL hd hqd)
    hAdef hkdef hkm hC0 hkb j hj
  simp only at h ⊢
  rwa [PurityWilson.wilson_ratio β L q d hd.ne'] at h

include hDc hdl hDl hDu hF hσ hFs hβ hL hd hqd hcl hcu hAdef hkdef hkm hC0 hkb in
/-- **(6.3) with the uniform ratio of Theorem 5.4.** For `0 ≤ q`,
`ψ_T ≤ 2 log (1 + t^T/(1 − t²))`, `t = tanh(3βL³/2)`, `T = 2j`, `j ≥ 1`. -/
theorem wilson_defect_uniform (hq : 0 ≤ q) (j : ℕ) (hj : 1 ≤ j) :
    let t := tanh (3 * β * L ^ 3 / 2)
    DoublingPower.defect (traceSeq μ k) (2 * j) ≤ 2 * Real.log (1 + t ^ (2 * j) / (1 - t ^ 2)) := by
  have h := wilson_defect (μ := μ) hDc hdl hDl hDu hF hσ hFs hβ hL hd hqd hcl hcu hAdef hkdef
    hkm hC0 hkb j hj
  simp only at h ⊢
  obtain ⟨hle, hlt1⟩ := PurityWilson.wilson_ratio_le (q := q) hβ.le hL.le hd hq
  have harg : 0 < 3 * β * L ^ 3 * (1 - q / d) / 2 := by
    have : q / d < 1 := (div_lt_one hd).2 hqd
    have : 0 < 1 - q / d := by linarith
    positivity
  have hτ0 := (PurityWilson.tanh_pos harg).le
  have hmono := tail_mono hτ0 hle hlt1 (2 * j)
  have hpos : 0 < 1 + tanh (3 * β * L ^ 3 * (1 - q / d) / 2) ^ (2 * j) /
      (1 - tanh (3 * β * L ^ 3 * (1 - q / d) / 2) ^ 2) := by
    have : 0 < 1 - tanh (3 * β * L ^ 3 * (1 - q / d) / 2) ^ 2 := by nlinarith
    positivity
  have hlog := Real.log_le_log hpos (add_le_add (le_refl 1) hmono)
  linarith

end Wilson

#print axioms integrable_cont
#print axioms F_cont
#print axioms expF_cont
#print axioms A_cont
#print axioms A_symm
#print axioms A_lower
#print axioms A_upper
#print axioms tail_mono
#print axioms wilson_lt
#print axioms norm_rem_le
#print axioms trace_excess
#print axioms defect
#print axioms wilson_norm_rem_le
#print axioms wilson_trace_excess
#print axioms wilson_defect
#print axioms wilson_defect_uniform

end MassGap.PurityWilsonCompact
