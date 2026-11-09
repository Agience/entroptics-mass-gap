import Mathlib
import MassGap.SlabTransferAdjoint

/-!
# MassGap.KernelEigen — a top eigenfunction for a continuous symmetric kernel on a compact space

`X` a compact topological space, second countable and Borel, with a probability measure `μ`; `k` a
jointly continuous symmetric kernel with `|k| ≤ C`; `K` its operator on `L²(μ)`
(`SlabKernelOperator.kernelCLM`). If `‖K‖ > 0`, there is a bounded measurable `φ` with
`∫ φ² = 1` and a real `c` with `|c| = ‖K‖` such that `∫ k(z,y) φ(y) dμ(y) = c φ(z)` at every `z`
(`exists_eigen`).

The proof: unit vectors `fₙ` with `|⟪K fₙ, fₙ⟫| → ‖K‖` (the Rayleigh supremum, Mathlib's
`norm_eq_iSup_rayleighQuotient`); `‖K²fₙ − ‖K‖² fₙ‖ → 0`; the functions `K fₙ` are uniformly
bounded and equicontinuous (uniform continuity of `k` on the compact `X × X`), so Arzelà–Ascoli
gives a subsequence along which `K fₙ` converges uniformly, hence in `L²`; then `fₙ` converges to a
unit `ψ` with `K²ψ = ‖K‖²ψ`, and either `Kψ + ‖K‖ψ` or `ψ` is an eigenvector of `K` with
eigenvalue `±‖K‖`. No compact-operator or spectral theorem is used.
-/

namespace MassGap.KernelEigen

open MeasureTheory Real Filter Topology MassGap.SlabKernelOperator
open scoped BoundedContinuousFunction

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {k : X → X → ℝ} (hkc : Continuous (Function.uncurry k)) {C : ℝ} (hC0 : 0 ≤ C)
  (hkb : ∀ x y, |k x y| ≤ C)

omit [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X] [BorelSpace X] in
theorem norm_sq_integral (g : Lp ℝ 2 μ) : ‖g‖ ^ 2 = ∫ x, (g : X → ℝ) x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [sq]

include hkc in
theorem kmeas : Measurable (Function.uncurry k) := hkc.measurable

include hkc in
/-- A uniform modulus of continuity in the first variable (tube lemma over the compact `X`). -/
theorem modulus {ε : ℝ} (hε : 0 < ε) (x₀ : X) : ∀ᶠ x in 𝓝 x₀, ∀ y, |k x y - k x₀ y| ≤ ε := by
  have h := (isCompact_univ (X := X)).eventually_forall_of_forall_eventually
    (x₀ := x₀) (P := fun x y => |k x y - k x₀ y| ≤ ε) (fun y _ => by
      have h1 := Metric.tendsto_nhds.mp (hkc.tendsto (x₀, y)) (ε / 2) (half_pos hε)
      have hc2 : Continuous fun z : X × X => Function.uncurry k (x₀, z.2) :=
        hkc.comp (continuous_const.prodMk continuous_snd)
      have h2 := Metric.tendsto_nhds.mp (hc2.tendsto (x₀, y)) (ε / 2) (half_pos hε)
      filter_upwards [h1, h2] with z hz1 hz2
      simp only [Function.uncurry, Real.dist_eq] at hz1 hz2
      have : |k z.1 z.2 - k x₀ z.2| ≤ |k z.1 z.2 - k x₀ y| + |k x₀ z.2 - k x₀ y| := by
        calc |k z.1 z.2 - k x₀ z.2| = |(k z.1 z.2 - k x₀ y) - (k x₀ z.2 - k x₀ y)| := by ring_nf
          _ ≤ _ := abs_sub _ _
      linarith)
  filter_upwards [h] with x hx y
  exact hx y (Set.mem_univ y)

include hkc hkb in
theorem kernelFun_sub_le {ε : ℝ} (hε : 0 ≤ ε) (f : Lp ℝ 2 μ) {x x₀ : X}
    (hb : ∀ y, |k x y - k x₀ y| ≤ ε) :
    |kernelFun k μ (f : X → ℝ) x - kernelFun k μ (f : X → ℝ) x₀| ≤ ε * ‖f‖ := by
  have hkm := kmeas hkc
  set D : X → X → ℝ := fun _ y => k x y - k x₀ y
  have hDm : Measurable (Function.uncurry D) :=
    ((hkm.comp (measurable_const.prodMk measurable_snd)).sub
      (hkm.comp (measurable_const.prodMk measurable_snd)))
  have hDb : ∀ a y, |D a y| ≤ ε := fun _ y => hb y
  have hf1 : Integrable (f : X → ℝ) μ := (Lp.memLp f).integrable one_le_two
  have e : kernelFun k μ (f : X → ℝ) x - kernelFun k μ (f : X → ℝ) x₀
      = kernelFun D μ (f : X → ℝ) x := by
    unfold kernelFun
    rw [← integral_sub (integrable_row_mul hkm hkb hf1 x) (integrable_row_mul hkm hkb hf1 x₀)]
    congr 1; funext y; simp only [D]; ring
  rw [e]
  exact abs_kernelFun_le hDm hε hDb f x

include hkc hC0 hkb in
theorem continuous_kernelFun (f : Lp ℝ 2 μ) : Continuous (kernelFun k μ (f : X → ℝ)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [modulus hkc (ε := ε / (‖f‖ + 1)) (by positivity) x₀] with x hx
  rw [Real.dist_eq]
  have h := kernelFun_sub_le hkc hkb (by positivity) f hx
  have : ε / (‖f‖ + 1) * ‖f‖ < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg f]
  linarith

/-- The image of `f` as a bounded continuous function. -/
noncomputable def imgBCF (f : Lp ℝ 2 μ) : X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨kernelFun k μ (f : X → ℝ), continuous_kernelFun hkc hC0 hkb f⟩

include hkc in
theorem toLp_imgBCF (f : Lp ℝ 2 μ) :
    BoundedContinuousFunction.toLp (E := ℝ) 2 μ ℝ (imgBCF hkc hC0 hkb f)
      = kernelCLM k C (kmeas hkc) hC0 hkb μ μ f := by
  apply Lp.ext
  filter_upwards [BoundedContinuousFunction.coeFn_toLp (E := ℝ) 2 μ ℝ (imgBCF hkc hC0 hkb f),
    coeFn_kernelCLM k C (kmeas hkc) hC0 hkb μ μ f] with x h1 h2
  rw [h1, h2]; rfl

include hkc hC0 hkb in
/-- Compactness: from a sequence in the unit ball, a subsequence whose images converge in `L²`. -/
theorem exists_subseq (f : ℕ → Lp ℝ 2 μ) (hf : ∀ n, ‖f n‖ ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : Lp ℝ 2 μ,
      Tendsto (fun i => kernelCLM k C (kmeas hkc) hC0 hkb μ μ (f (φ i))) atTop (𝓝 g) := by
  set G : ℕ → X →ᵇ ℝ := fun n => imgBCF hkc hC0 hkb (f n)
  set A : Set (X →ᵇ ℝ) := Set.range G
  have hin : ∀ (h : X →ᵇ ℝ) (x : X), h ∈ A → h x ∈ Set.Icc (-C) C := by
    rintro h x ⟨n, rfl⟩
    have := abs_kernelFun_le (kmeas hkc) hC0 hkb (f n) x
    have h2 : C * ‖f n‖ ≤ C := by nlinarith [hf n, norm_nonneg (f n)]
    exact abs_le.mp (this.trans h2)
  have heq : Equicontinuous ((↑) : A → X → ℝ) := by
    intro x₀
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    filter_upwards [modulus hkc (ε := ε / 2) (by positivity) x₀] with x hx
    rintro ⟨h, ⟨n, rfl⟩⟩
    have := kernelFun_sub_le hkc hkb (by positivity) (f n) hx
    have h2 : ε / 2 * ‖f n‖ ≤ ε / 2 := by nlinarith [hf n, norm_nonneg (f n)]
    change dist (kernelFun k μ (f n : X → ℝ) x₀) (kernelFun k μ (f n : X → ℝ) x) < ε
    rw [Real.dist_eq, abs_sub_comm]
    linarith
  have hcpt := BoundedContinuousFunction.arzela_ascoli (Set.Icc (-C) C) isCompact_Icc A hin heq
  obtain ⟨a, -, φ, hφ, hlim⟩ := hcpt.tendsto_subseq (fun n => subset_closure ⟨n, rfl⟩)
  refine ⟨φ, hφ, BoundedContinuousFunction.toLp (E := ℝ) 2 μ ℝ a, ?_⟩
  have := ((BoundedContinuousFunction.toLp (E := ℝ) 2 μ ℝ).continuous.tendsto a).comp hlim
  refine this.congr (fun i => ?_)
  simp only [Function.comp_apply, G]
  exact toLp_imgBCF hkc hC0 hkb (f (φ i))

include hkc hC0 hkb in
/-- An `L²` eigenvector at `±‖K‖`. -/
theorem exists_eigen_Lp (hsym : ∀ x y, k x y = k y x)
    (hpos : 0 < ‖kernelCLM k C (kmeas hkc) hC0 hkb μ μ‖) :
    ∃ ψ : Lp ℝ 2 μ, ‖ψ‖ = 1 ∧ ∃ c : ℝ, |c| = ‖kernelCLM k C (kmeas hkc) hC0 hkb μ μ‖ ∧
      kernelCLM k C (kmeas hkc) hC0 hkb μ μ ψ = c • ψ := by
  set K := kernelCLM k C (kmeas hkc) hC0 hkb μ μ with hK
  set lam := ‖K‖ with hlam
  have hsa : IsSelfAdjoint K := MassGap.SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm k C
    (kmeas hkc) hC0 hkb μ hsym
  have hS : (K : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ).IsSymmetric := hsa.isSymmetric
  have hsymm : ∀ u v, inner ℝ (K u) v = inner ℝ u (K v) := fun u v => hS u v
  -- maximizing unit vectors
  have hsup := ContinuousLinearMap.norm_eq_iSup_rayleighQuotient (T := K) hS
  have hchoose : ∀ n : ℕ, ∃ f : Lp ℝ 2 μ, ‖f‖ = 1 ∧
      lam - lam / (n + 2) < |inner ℝ (K f) f| := by
    intro n
    have hε : 0 < lam / (n + 2) := by positivity
    have hlt : lam - lam / (n + 2) < ⨆ x, |K.rayleighQuotient x| := by rw [← hsup]; linarith
    obtain ⟨x, hx⟩ := exists_lt_of_lt_ciSup hlt
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
      have : lam / ((n : ℝ) + 2) < lam := by
        rw [div_lt_iff₀ (by positivity)]; nlinarith
      linarith
    have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
    refine ⟨(‖x‖⁻¹ : ℝ) • x, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    · have hrs := K.rayleigh_smul x (c := (‖x‖⁻¹ : ℝ)) (inv_ne_zero hn)
      have hunit : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
      have hrq : K.rayleighQuotient ((‖x‖⁻¹ : ℝ) • x) = inner ℝ (K ((‖x‖⁻¹ : ℝ) • x)) ((‖x‖⁻¹ : ℝ) • x) := by
        rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
          hunit]
        simp
      rw [← hrq, hrs]
      exact hx
  choose f hf1 hfr using hchoose
  -- `‖K fₙ‖ → λ`
  have hKf_le : ∀ n, ‖K (f n)‖ ≤ lam := fun n => by
    have := K.le_opNorm (f n); rw [hf1 n, mul_one] at this; exact this
  have hKf_ge : ∀ n, |inner ℝ (K (f n)) (f n)| ≤ ‖K (f n)‖ := fun n => by
    have := abs_real_inner_le_norm (K (f n)) (f n); rw [hf1 n, mul_one] at this; exact this
  have hlow : Tendsto (fun n : ℕ => lam - lam / ((n : ℝ) + 2)) atTop (𝓝 lam) := by
    have : Tendsto (fun n : ℕ => lam / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa using tendsto_const_nhds.sub this
  have hKf : Tendsto (fun n => ‖K (f n)‖) atTop (𝓝 lam) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun n => ((hfr n).le.trans (hKf_ge n))) hKf_le
  -- `‖K² fₙ − λ² fₙ‖ → 0`
  set A := K.comp K with hA
  have hAf : ∀ n, ‖A (f n) - lam ^ 2 • f n‖ ^ 2 ≤ 2 * lam ^ 2 * (lam ^ 2 - ‖K (f n)‖ ^ 2) := by
    intro n
    have h1 : inner ℝ (A (f n)) (f n) = ‖K (f n)‖ ^ 2 := by
      simp only [hA, ContinuousLinearMap.comp_apply]
      rw [hsymm, real_inner_self_eq_norm_sq]
    have h2 : ‖A (f n)‖ ≤ lam ^ 2 := by
      calc ‖A (f n)‖ = ‖K (K (f n))‖ := rfl
        _ ≤ lam * ‖K (f n)‖ := K.le_opNorm _
        _ ≤ lam * lam := mul_le_mul_of_nonneg_left (hKf_le n) (norm_nonneg _)
        _ = lam ^ 2 := by ring
    have h3 : ‖A (f n) - lam ^ 2 • f n‖ ^ 2
        = ‖A (f n)‖ ^ 2 - 2 * lam ^ 2 * inner ℝ (A (f n)) (f n) + lam ^ 4 := by
      rw [@norm_sub_sq_real, norm_smul, hf1 n, inner_smul_right, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      ring
    rw [h3, h1]
    have : ‖A (f n)‖ ^ 2 ≤ lam ^ 4 := by
      have := pow_le_pow_left₀ (norm_nonneg _) h2 2; nlinarith
    nlinarith
  have hres : Tendsto (fun n => A (f n) - lam ^ 2 • f n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : Tendsto (fun n => Real.sqrt (2 * lam ^ 2 * (lam ^ 2 - ‖K (f n)‖ ^ 2))) atTop (𝓝 0) := by
      have : Tendsto (fun n => 2 * lam ^ 2 * (lam ^ 2 - ‖K (f n)‖ ^ 2)) atTop (𝓝 (2 * lam ^ 2 * (lam ^ 2 - lam ^ 2))) :=
        tendsto_const_nhds.mul (tendsto_const_nhds.sub (hKf.pow 2))
      have h2 := (Real.continuous_sqrt.tendsto _).comp this
      simp only [sub_self, mul_zero, Real.sqrt_zero, Function.comp_def] at h2
      exact h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun n => norm_nonneg _)
      (fun n => ?_)
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (hAf n)
  -- the subsequence
  obtain ⟨φ, hφ, g, hg⟩ := exists_subseq hkc hC0 hkb f (fun n => (hf1 n).le)
  have hAg : Tendsto (fun i => A (f (φ i))) atTop (𝓝 (K g)) := by
    have := (K.continuous.tendsto g).comp hg
    simpa [hA, Function.comp_def] using this
  have hl2 : 0 < lam ^ 2 := by positivity
  have hfconv : Tendsto (fun i => f (φ i)) atTop (𝓝 ((lam ^ 2)⁻¹ • K g)) := by
    have h1 : Tendsto (fun i => A (f (φ i)) - (A (f (φ i)) - lam ^ 2 • f (φ i))) atTop
        (𝓝 (K g - 0)) := hAg.sub (hres.comp hφ.tendsto_atTop)
    have h2 : Tendsto (fun i => (lam ^ 2)⁻¹ • (A (f (φ i)) - (A (f (φ i)) - lam ^ 2 • f (φ i))))
        atTop (𝓝 ((lam ^ 2)⁻¹ • (K g - 0))) := h1.const_smul _
    simp only [sub_sub_cancel, sub_zero, smul_smul, inv_mul_cancel₀ hl2.ne', one_smul] at h2
    exact h2
  set ψ := (lam ^ 2)⁻¹ • K g
  have hψ1 : ‖ψ‖ = 1 := by
    have := (continuous_norm.tendsto ψ).comp hfconv
    simp only [Function.comp_def, hf1] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hAψ : A ψ = lam ^ 2 • ψ := by
    have h1 : Tendsto (fun i => A (f (φ i))) atTop (𝓝 (A ψ)) :=
      (A.continuous.tendsto ψ).comp hfconv
    have h2 : Tendsto (fun i => A (f (φ i))) atTop (𝓝 (lam ^ 2 • ψ)) := by
      have := ((hres.comp hφ.tendsto_atTop).add (hfconv.const_smul (lam ^ 2)))
      simpa using this
    exact tendsto_nhds_unique h1 h2
  -- an eigenvector of `K`
  set u := K ψ + lam • ψ
  by_cases hu : u = 0
  · refine ⟨ψ, hψ1, -lam, by simp [abs_of_pos hpos], ?_⟩
    have : K ψ = -(lam • ψ) := eq_neg_of_add_eq_zero_left hu
    rw [this, neg_smul]
  · have hKu : K u = lam • u := by
      have e : K (K ψ) = lam ^ 2 • ψ := hAψ
      simp only [u, map_add, map_smul, e, smul_add, smul_smul]
      rw [show lam ^ 2 = lam * lam by ring, add_comm]
    have hun : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    refine ⟨‖u‖⁻¹ • u, ?_, lam, abs_of_pos hpos, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hun]
    · rw [map_smul, hKu, smul_comm]

include hkc hC0 hkb in
/-- A pointwise eigenfunction at `±‖K‖`. -/
theorem exists_eigen (hsym : ∀ x y, k x y = k y x)
    (hpos : 0 < ‖kernelCLM k C (kmeas hkc) hC0 hkb μ μ‖) :
    ∃ φ : X → ℝ, Measurable φ ∧ (∃ B, ∀ x, |φ x| ≤ B) ∧ ∫ x, φ x ^ 2 ∂μ = 1 ∧
      ∃ c : ℝ, |c| = ‖kernelCLM k C (kmeas hkc) hC0 hkb μ μ‖ ∧
        ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z := by
  obtain ⟨ψ, hψ1, c, hc, hKψ⟩ := exists_eigen_Lp hkc hC0 hkb hsym hpos
  have hc0 : c ≠ 0 := by intro h; rw [h, abs_zero] at hc; linarith
  set φ : X → ℝ := fun z => c⁻¹ * kernelFun k μ (ψ : X → ℝ) z
  have hφψ : φ =ᵐ[μ] (ψ : X → ℝ) := by
    filter_upwards [coeFn_kernelCLM k C (kmeas hkc) hC0 hkb μ μ ψ,
      Lp.coeFn_smul c ψ] with z h1 h2
    have h3 := congrArg (fun v : Lp ℝ 2 μ => (v : X → ℝ)) hKψ
    simp only [φ]
    rw [← h1]
    have : ((kernelCLM k C (kmeas hkc) hC0 hkb μ μ ψ : Lp ℝ 2 μ) : X → ℝ) z
        = ((c • ψ : Lp ℝ 2 μ) : X → ℝ) z := by rw [hKψ]
    rw [this, h2]; simp [hc0]
  refine ⟨φ, measurable_const.mul (stronglyMeasurable_kernelFun (kmeas hkc) ψ).measurable,
    ⟨|c|⁻¹ * (C * ‖ψ‖), fun x => ?_⟩, ?_, c, hc, fun z => ?_⟩
  · simp only [φ]; rw [abs_mul, abs_inv]
    exact mul_le_mul_of_nonneg_left (abs_kernelFun_le (kmeas hkc) hC0 hkb ψ x) (by positivity)
  · have : ∫ x, φ x ^ 2 ∂μ = ∫ x, (ψ : X → ℝ) x ^ 2 ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hφψ] with x hx; rw [hx]
    rw [this, ← MassGap.KernelEigen.norm_sq_integral, hψ1, one_pow]
  · have h1 : ∫ y, k z y * φ y ∂μ = kernelFun k μ (ψ : X → ℝ) z := by
      unfold kernelFun
      refine integral_congr_ae ?_
      filter_upwards [hφψ] with y hy; rw [hy]
    rw [h1]; simp only [φ]; field_simp

#print axioms exists_eigen_Lp
#print axioms exists_eigen

end MassGap.KernelEigen
