import Mathlib
import MassGap.KernelEigen
import MassGap.RectTransfer

/-!
# MassGap.JentzschKT — a strictly positive top eigenfunction for a positive symmetric kernel

`X` a compact, second countable Borel space with a probability measure `μ`; `k` a jointly continuous
symmetric kernel with `|k| ≤ C`; `K = SlabKernelOperator.kernelCLM k …` its operator on `L²(μ)`.

## 1. A nonnegative kernel does not lower the form on `|f|` (proved)

For `k ≥ 0` and `f ∈ L²(μ)`: `|kernelFun k μ f x| ≤ kernelFun k μ |f| x` at every `x`
(`abs_kernelFun_le_abs`) and `|⟪K f, f⟫| ≤ ⟪K |f|, |f|⟫` (`abs_inner_le_inner_abs`), with
`‖|f|‖ = ‖f‖` (`norm_abs_Lp`). So the supremum of `|⟪K f, f⟫|` over unit vectors, which is `‖K‖`
for a self-adjoint `K`, is approached by nonnegative unit vectors with `⟪K f, f⟫` itself (no absolute
value) close to `‖K‖`. No semidefiniteness of `K` is used.

## 2. Jentzsch for the top of the spectrum (proved)

* `exists_nonneg_top_Lp`: for `k ≥ 0` symmetric continuous with `‖K‖ > 0`, there is `ψ ∈ L²(μ)`,
  `‖ψ‖ = 1`, `ψ ≥ 0` almost everywhere, `K ψ = ‖K‖ ψ`. The proof: nonnegative unit vectors `gₙ`
  with `⟪K gₙ, gₙ⟫ → ‖K‖` (section 1) have `‖K gₙ − ‖K‖ gₙ‖² ≤ 2‖K‖² − 2‖K‖⟪K gₙ, gₙ⟫ → 0`;
  `KernelEigen.exists_subseq` (Arzelà–Ascoli) gives a subsequence along which `K gₙ` converges in
  `L²`, so `gₙ` converges to a unit `ψ` with `K ψ = ‖K‖ ψ`; the nonnegative cone of `L²` is closed
  (`Lp`'s `OrderClosedTopology`), so `ψ ≥ 0`.
* `exists_pos_eigen`: if moreover `c₀ ≤ k` with `c₀ > 0`, then `‖K‖ > 0` and there is a measurable
  `φ` with `|φ| ≤ C/‖K‖`, `φ ≥ c > 0` everywhere, `∫ φ² = 1` and `∫ k(z,y) φ(y) dμ(y) = ‖K‖ φ(z)` at
  every `z`. The lower bound: `φ = K ψ / ‖K‖ ≥ c₀ (∫ ψ) / ‖K‖`, and `∫ ψ > 0` because `ψ ≥ 0` has norm
  `1`.
* `inner_le_norm_K`, `inner_top`: `⟪K f, f⟫ ≤ ‖K‖ ‖f‖²` for every `f`, with equality at `ψ`: `‖K‖` is
  the top of the Rayleigh quotient of `K`, attained at a nonnegative vector.

## 3. The Wilson slice transfer (proved)

`exists_pos_eigen_kT`: for `RectTransfer.kT μ T N β` on `SpT μ T → SU N` with the product Haar
measure, at `N ≠ 0` and `β ≥ 0` (`kT_symm`, `continuous_kT`, `abs_kT_le`, `kT_lower`), the operator
norm `λ₀ = ‖K‖` is positive and is an eigenvalue with an eigenfunction `φ ≥ c > 0`.
`exists_nonneg_top_Lp_kT` is the `L²` form.

This identifies the top eigenvalue of one finite-volume slice transfer and its sign; it says nothing
about the second eigenvalue and proves no gap.

DERIVED (module-wide): `0` the sign of the kernel and of `ψ`; `1` the norm of the unit vectors;
`2` the `L²` exponent and the degree of the norm; `n + 2` the index shift that keeps the tolerance
`‖K‖/(n+2)` below `‖K‖` at `n = 0`.
-/

namespace MassGap.JentzschKT

open MeasureTheory Real Filter Topology MassGap.SlabKernelOperator MassGap.SlabTransferAdjoint

/-! ## 1. The form on `|f|` -/

section Abs

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {k : X → X → ℝ} (hk : Measurable (Function.uncurry k)) {C : ℝ} (hC0 : 0 ≤ C)
  (hkb : ∀ x y, |k x y| ≤ C)

omit [IsProbabilityMeasure μ] in
theorem kernelFun_abs (f : Lp ℝ 2 μ) (x : X) :
    kernelFun k μ ((|f| : Lp ℝ 2 μ) : X → ℝ) x = ∫ y, k x y * |(f : X → ℝ) y| ∂μ := by
  unfold kernelFun
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_abs f] with y hy
  rw [hy]

omit [IsProbabilityMeasure μ] in
/-- A nonnegative kernel: `|K f| ≤ K |f|` at every point. -/
theorem abs_kernelFun_le_abs (hk0 : ∀ x y, 0 ≤ k x y) (f : Lp ℝ 2 μ) (x : X) :
    |kernelFun k μ (f : X → ℝ) x| ≤ kernelFun k μ ((|f| : Lp ℝ 2 μ) : X → ℝ) x := by
  rw [kernelFun_abs]
  unfold kernelFun
  calc |∫ y, k x y * (f : X → ℝ) y ∂μ| ≤ ∫ y, |k x y * (f : X → ℝ) y| ∂μ :=
        abs_integral_le_integral_abs
    _ = ∫ y, k x y * |(f : X → ℝ) y| ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        show |k x y * (f : X → ℝ) y| = k x y * |(f : X → ℝ) y|
        rw [abs_mul, abs_of_nonneg (hk0 x y)]

include hk hC0 hkb in
theorem integrable_kernelFun_mul (f : Lp ℝ 2 μ) :
    Integrable (fun x => kernelFun k μ (f : X → ℝ) x * (f : X → ℝ) x) μ :=
  ((Lp.memLp f).integrable one_le_two).bdd_mul (c := C * ‖f‖)
    (stronglyMeasurable_kernelFun hk f).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using abs_kernelFun_le hk hC0 hkb f x)

/-- The form `⟪K f, g⟫` as an integral. -/
theorem inner_kernelCLM_eq (f g : Lp ℝ 2 μ) :
    (inner ℝ (kernelCLM k C hk hC0 hkb μ μ f) g : ℝ)
      = ∫ x, kernelFun k μ (f : X → ℝ) x * (g : X → ℝ) x ∂μ := by
  rw [real_inner_Lp]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_kernelCLM k C hk hC0 hkb μ μ f] with x hx
  rw [hx]

/-- `‖|f|‖ = ‖f‖` in `L²`. -/
theorem norm_abs_Lp (f : Lp ℝ 2 μ) : ‖(|f| : Lp ℝ 2 μ)‖ = ‖f‖ := by
  have h : ‖(|f| : Lp ℝ 2 μ)‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [MassGap.KernelEigen.norm_sq_integral, MassGap.KernelEigen.norm_sq_integral]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_abs f] with x hx
    rw [hx, sq_abs]
  rw [← Real.sqrt_sq (norm_nonneg (|f| : Lp ℝ 2 μ)), h, Real.sqrt_sq (norm_nonneg f)]

omit [IsProbabilityMeasure μ] in
theorem abs_Lp_nonneg (f : Lp ℝ 2 μ) : 0 ≤ᵐ[μ] ((|f| : Lp ℝ 2 μ) : X → ℝ) := by
  filter_upwards [Lp.coeFn_abs f] with x hx
  rw [hx]
  exact abs_nonneg _

include hk hC0 hkb in
/-- **A nonnegative kernel does not lower the form on `|f|`**: `|⟪K f, f⟫| ≤ ⟪K |f|, |f|⟫`. -/
theorem abs_inner_le_inner_abs (hk0 : ∀ x y, 0 ≤ k x y) (f : Lp ℝ 2 μ) :
    |(inner ℝ (kernelCLM k C hk hC0 hkb μ μ f) f : ℝ)|
      ≤ inner ℝ (kernelCLM k C hk hC0 hkb μ μ |f|) |f| := by
  rw [inner_kernelCLM_eq, inner_kernelCLM_eq]
  calc |∫ x, kernelFun k μ (f : X → ℝ) x * (f : X → ℝ) x ∂μ|
      ≤ ∫ x, |kernelFun k μ (f : X → ℝ) x * (f : X → ℝ) x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, kernelFun k μ ((|f| : Lp ℝ 2 μ) : X → ℝ) x * ((|f| : Lp ℝ 2 μ) : X → ℝ) x ∂μ := by
        refine integral_mono_ae (integrable_kernelFun_mul hk hC0 hkb f).abs
          (integrable_kernelFun_mul hk hC0 hkb |f|) ?_
        filter_upwards [Lp.coeFn_abs f] with x hx
        rw [abs_mul, hx]
        exact mul_le_mul_of_nonneg_right (abs_kernelFun_le_abs hk0 f x) (abs_nonneg _)

end Abs

/-! ## 2. Jentzsch for the top of the spectrum -/

section Jentzsch

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {k : X → X → ℝ} (hkc : Continuous (Function.uncurry k)) {C : ℝ} (hC0 : 0 ≤ C)
  (hkb : ∀ x y, |k x y| ≤ C)

open MassGap.KernelEigen in
include hkc hC0 hkb in
/-- **Jentzsch, `L²` form**: a nonnegative symmetric continuous kernel with `‖K‖ > 0` has a
nonnegative unit eigenvector at the eigenvalue `‖K‖`. -/
theorem exists_nonneg_top_Lp (hsym : ∀ x y, k x y = k y x) (hk0 : ∀ x y, 0 ≤ k x y)
    (hpos : 0 < ‖kernelCLM k C (kmeas hkc) hC0 hkb μ μ‖) :
    ∃ ψ : Lp ℝ 2 μ, ‖ψ‖ = 1 ∧ 0 ≤ᵐ[μ] (ψ : X → ℝ) ∧
      kernelCLM k C (kmeas hkc) hC0 hkb μ μ ψ = ‖kernelCLM k C (kmeas hkc) hC0 hkb μ μ‖ • ψ := by
  set K := kernelCLM k C (kmeas hkc) hC0 hkb μ μ with hK
  set lam := ‖K‖ with hlam
  have hsa : IsSelfAdjoint K := isSelfAdjoint_kernelCLM_of_symm k C (kmeas hkc) hC0 hkb μ hsym
  have hS : (K : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ).IsSymmetric := hsa.isSymmetric
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
      have hrq : K.rayleighQuotient ((‖x‖⁻¹ : ℝ) • x)
          = inner ℝ (K ((‖x‖⁻¹ : ℝ) • x)) ((‖x‖⁻¹ : ℝ) • x) := by
        rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
          hunit]
        simp
      rw [← hrq, hrs]
      exact hx
  choose f hf1 hfr using hchoose
  -- the nonnegative unit vectors `gₙ = |fₙ|`
  set g : ℕ → Lp ℝ 2 μ := fun n => |f n| with hg
  have hg1 : ∀ n, ‖g n‖ = 1 := fun n => by rw [hg, norm_abs_Lp, hf1 n]
  have hgnn : ∀ n, 0 ≤ g n := fun n => (Lp.coeFn_nonneg (g n)).1 (abs_Lp_nonneg (f n))
  have hgr : ∀ n, lam - lam / (n + 2) < inner ℝ (K (g n)) (g n) := fun n =>
    (hfr n).trans_le (abs_inner_le_inner_abs (kmeas hkc) hC0 hkb hk0 (f n))
  have hKg_le : ∀ n, ‖K (g n)‖ ≤ lam := fun n => by
    have := K.le_opNorm (g n); rw [hg1 n, mul_one] at this; exact this
  -- `‖K gₙ − λ gₙ‖² ≤ 2 λ² / (n + 2)`
  have hres_le : ∀ n, ‖K (g n) - lam • g n‖ ^ 2 ≤ 2 * lam * (lam / (n + 2)) := by
    intro n
    have h3 : ‖K (g n) - lam • g n‖ ^ 2
        = ‖K (g n)‖ ^ 2 - 2 * lam * inner ℝ (K (g n)) (g n) + lam ^ 2 := by
      rw [@norm_sub_sq_real, norm_smul, hg1 n, inner_smul_right, Real.norm_eq_abs,
        abs_of_pos hpos]
      ring
    rw [h3]
    have h4 : ‖K (g n)‖ ^ 2 ≤ lam ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hKg_le n) 2
    have h5 := hgr n
    nlinarith
  have htol : Tendsto (fun n : ℕ => 2 * lam * (lam / ((n : ℝ) + 2))) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => lam / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa using this.const_mul (2 * lam)
  have hres : Tendsto (fun n => K (g n) - lam • g n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : Tendsto (fun n : ℕ => Real.sqrt (2 * lam * (lam / ((n : ℝ) + 2)))) atTop (𝓝 0) := by
      have h2 := (Real.continuous_sqrt.tendsto _).comp htol
      simp only [Real.sqrt_zero, Function.comp_def] at h2
      exact h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun n => norm_nonneg _)
      (fun n => ?_)
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (hres_le n)
  -- the subsequence
  obtain ⟨φ, hφ, h, hh⟩ := exists_subseq hkc hC0 hkb g (fun n => (hg1 n).le)
  have hlam0 : lam ≠ 0 := hpos.ne'
  have hgconv : Tendsto (fun i => g (φ i)) atTop (𝓝 (lam⁻¹ • h)) := by
    have h1 : Tendsto (fun i => K (g (φ i)) - (K (g (φ i)) - lam • g (φ i))) atTop
        (𝓝 (h - 0)) := hh.sub (hres.comp hφ.tendsto_atTop)
    have h2 : Tendsto (fun i => lam⁻¹ • (K (g (φ i)) - (K (g (φ i)) - lam • g (φ i))))
        atTop (𝓝 (lam⁻¹ • (h - 0))) := h1.const_smul _
    simp only [sub_sub_cancel, sub_zero, smul_smul, inv_mul_cancel₀ hlam0, one_smul] at h2
    exact h2
  set ψ := lam⁻¹ • h
  have hψ1 : ‖ψ‖ = 1 := by
    have := (continuous_norm.tendsto ψ).comp hgconv
    simp only [Function.comp_def, hg1] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hKψ : K ψ = lam • ψ := by
    have h1 : Tendsto (fun i => K (g (φ i))) atTop (𝓝 (K ψ)) :=
      (K.continuous.tendsto ψ).comp hgconv
    have h2 : Tendsto (fun i => K (g (φ i))) atTop (𝓝 (lam • ψ)) := by
      have := ((hres.comp hφ.tendsto_atTop).add (hgconv.const_smul lam))
      simpa using this
    exact tendsto_nhds_unique h1 h2
  have hψnn : 0 ≤ ψ := ge_of_tendsto' hgconv fun i => hgnn (φ i)
  exact ⟨ψ, hψ1, (Lp.coeFn_nonneg ψ).2 hψnn, hKψ⟩

include hkc hC0 hkb in
/-- **`‖K‖` is the top of the Rayleigh quotient**: `⟪K f, f⟫ ≤ ‖K‖ ‖f‖²`. -/
theorem inner_le_norm_K (f : Lp ℝ 2 μ) :
    (inner ℝ (kernelCLM k C (MassGap.KernelEigen.kmeas hkc) hC0 hkb μ μ f) f : ℝ)
      ≤ ‖kernelCLM k C (MassGap.KernelEigen.kmeas hkc) hC0 hkb μ μ‖ * ‖f‖ ^ 2 := by
  calc _ ≤ ‖kernelCLM k C (MassGap.KernelEigen.kmeas hkc) hC0 hkb μ μ f‖ * ‖f‖ :=
        real_inner_le_norm _ _
    _ ≤ (‖kernelCLM k C (MassGap.KernelEigen.kmeas hkc) hC0 hkb μ μ‖ * ‖f‖) * ‖f‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = _ := by ring

omit [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X] [BorelSpace X]
  [IsProbabilityMeasure μ] in
/-- At an eigenvector of norm `1` the form is the eigenvalue. -/
theorem inner_top {K : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} {ψ : Lp ℝ 2 μ} {c : ℝ} (hψ : ‖ψ‖ = 1)
    (hK : K ψ = c • ψ) : (inner ℝ (K ψ) ψ : ℝ) = c := by
  rw [hK, real_inner_smul_left, real_inner_self_eq_norm_sq, hψ]; ring

open MassGap.KernelEigen in
include hkc hC0 hkb in
/-- **Jentzsch for a strictly positive symmetric kernel**: `λ₀ = ‖K‖ > 0` is an eigenvalue with an
eigenfunction `φ ≥ c > 0`, bounded by `C/λ₀`, measurable, with `∫ φ² = 1`, and
`∫ k(z,y) φ(y) dμ(y) = λ₀ φ(z)` at every `z`. -/
theorem exists_pos_eigen (hsym : ∀ x y, k x y = k y x) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hlow : ∀ x y, c₀ ≤ k x y) :
    0 < ‖kernelCLM k C (kmeas hkc) hC0 hkb μ μ‖ ∧
      ∃ φ : X → ℝ, Measurable φ ∧
        (∀ x, |φ x| ≤ C / ‖kernelCLM k C (kmeas hkc) hC0 hkb μ μ‖) ∧
        (∃ c, 0 < c ∧ ∀ x, c ≤ φ x) ∧ ∫ x, φ x ^ 2 ∂μ = 1 ∧
        ∀ z, ∫ y, k z y * φ y ∂μ = ‖kernelCLM k C (kmeas hkc) hC0 hkb μ μ‖ * φ z := by
  set K := kernelCLM k C (kmeas hkc) hC0 hkb μ μ with hK
  have hpos : 0 < ‖K‖ := norm_pos_iff.mpr (kernelCLM_ne_zero k C (kmeas hkc) hC0 hkb μ μ hc₀ hlow)
  have hk0 : ∀ x y, 0 ≤ k x y := fun x y => hc₀.le.trans (hlow x y)
  obtain ⟨ψ, hψ1, hψnn, hKψ⟩ := exists_nonneg_top_Lp hkc hC0 hkb hsym hk0 hpos
  set lam := ‖K‖ with hlam
  have hl0 : lam ≠ 0 := hpos.ne'
  set φ : X → ℝ := fun z => lam⁻¹ * kernelFun k μ (ψ : X → ℝ) z with hφdef
  have hφψ : φ =ᵐ[μ] (ψ : X → ℝ) := by
    filter_upwards [coeFn_kernelCLM k C (kmeas hkc) hC0 hkb μ μ ψ,
      Lp.coeFn_smul lam ψ] with z h1 h2
    simp only [φ]
    rw [← h1]
    have : ((K ψ : Lp ℝ 2 μ) : X → ℝ) z = ((lam • ψ : Lp ℝ 2 μ) : X → ℝ) z := by rw [hKψ]
    rw [this, h2]; simp [hl0]
  have hψi : Integrable (ψ : X → ℝ) μ := (Lp.memLp ψ).integrable one_le_two
  have hint_pos : 0 < ∫ x, (ψ : X → ℝ) x ∂μ := by
    refine lt_of_le_of_ne (integral_nonneg_of_ae hψnn) (fun h0 => ?_)
    have hz : (ψ : X → ℝ) =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg_ae hψnn hψi).1 h0.symm
    have hn : ‖ψ‖ ^ 2 = 0 := by
      rw [norm_sq_integral]
      have : ∫ x, (ψ : X → ℝ) x ^ 2 ∂μ = ∫ _x, (0 : ℝ) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hz] with x hx
        rw [hx]; simp
      rw [this]; simp
    rw [hψ1] at hn
    norm_num at hn
  have hlowK : ∀ z, c₀ * ∫ x, (ψ : X → ℝ) x ∂μ ≤ kernelFun k μ (ψ : X → ℝ) z := by
    intro z
    unfold kernelFun
    rw [← integral_const_mul]
    refine integral_mono_ae (hψi.const_mul c₀) (integrable_row_mul (kmeas hkc) hkb hψi z) ?_
    filter_upwards [hψnn] with y hy
    exact mul_le_mul_of_nonneg_right (hlow z y) hy
  refine ⟨hpos, φ, measurable_const.mul (stronglyMeasurable_kernelFun (kmeas hkc) ψ).measurable,
    fun x => ?_, ⟨lam⁻¹ * (c₀ * ∫ x, (ψ : X → ℝ) x ∂μ), by positivity, fun x => ?_⟩, ?_,
    fun z => ?_⟩
  · simp only [φ]; rw [abs_mul, abs_inv, abs_of_pos hpos, div_eq_inv_mul]
    have := abs_kernelFun_le (kmeas hkc) hC0 hkb ψ x
    rw [hψ1, mul_one] at this
    exact mul_le_mul_of_nonneg_left this (by positivity)
  · simp only [φ]
    exact mul_le_mul_of_nonneg_left (hlowK x) (by positivity)
  · have : ∫ x, φ x ^ 2 ∂μ = ∫ x, (ψ : X → ℝ) x ^ 2 ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hφψ] with x hx; rw [hx]
    rw [this, ← norm_sq_integral, hψ1, one_pow]
  · have h1 : ∫ y, k z y * φ y ∂μ = kernelFun k μ (ψ : X → ℝ) z := by
      unfold kernelFun
      refine integral_congr_ae ?_
      filter_upwards [hφψ] with y hy; rw [hy]
    rw [h1]; simp only [φ]; field_simp

end Jentzsch

/-! ## 3. The Wilson slice transfer -/

section Wilson

open MassGap.RectTransfer MassGap.RectWilson

variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ} {N : ℕ}

/-- **The top eigenvalue of the Wilson slice transfer, with a strictly positive eigenfunction**: at
`N ≠ 0`, `β ≥ 0`, `λ₀ = ‖K‖ > 0` for `K = kernelCLM (kT μ T N β)` on `L²` of the product Haar measure,
and some measurable `φ`, `0 < c ≤ φ ≤ 1/λ₀`, `∫ φ² = 1`, has `∫ kT(z,y) φ(y) dy = λ₀ φ(z)` at every
`z`. -/
theorem exists_pos_eigen_kT (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    0 < ‖kernelCLM (kT μ T N β) 1 (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
      (hS μ T N) (hS μ T N)‖ ∧
      ∃ φ : (SpT μ T → MassGap.SUN.SU N) → ℝ, Measurable φ ∧
        (∀ x, |φ x| ≤ 1 / ‖kernelCLM (kT μ T N β) 1 (continuous_kT β).measurable zero_le_one
          (abs_kT_le hN hβ) (hS μ T N) (hS μ T N)‖) ∧
        (∃ c, 0 < c ∧ ∀ x, c ≤ φ x) ∧ ∫ x, φ x ^ 2 ∂(hS μ T N) = 1 ∧
        ∀ z, ∫ y, kT μ T N β z y * φ y ∂(hS μ T N)
          = ‖kernelCLM (kT μ T N β) 1 (continuous_kT β).measurable zero_le_one
              (abs_kT_le hN hβ) (hS μ T N) (hS μ T N)‖ * φ z :=
  exists_pos_eigen (μ := hS μ T N) (continuous_kT β) zero_le_one (abs_kT_le hN hβ) (kT_symm β)
    (kTmin_pos β) (kT_lower hN hβ)

/-- The `L²` form: a nonnegative unit `ψ` with `K ψ = ‖K‖ ψ` for the Wilson slice transfer. -/
theorem exists_nonneg_top_Lp_kT (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    ∃ ψ : Lp ℝ 2 (hS μ T N), ‖ψ‖ = 1 ∧ 0 ≤ᵐ[hS μ T N] (ψ : (SpT μ T → MassGap.SUN.SU N) → ℝ) ∧
      kernelCLM (kT μ T N β) 1 (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
          (hS μ T N) (hS μ T N) ψ
        = ‖kernelCLM (kT μ T N β) 1 (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
            (hS μ T N) (hS μ T N)‖ • ψ :=
  exists_nonneg_top_Lp (μ := hS μ T N) (continuous_kT β) zero_le_one (abs_kT_le hN hβ) (kT_symm β)
    (fun x y => (kTmin_pos β).le.trans (kT_lower hN hβ x y))
    (norm_pos_iff.mpr (kernelCLM_ne_zero _ _ _ _ _ _ _ (kTmin_pos β) (kT_lower hN hβ)))

end Wilson

#print axioms abs_kernelFun_le_abs
#print axioms abs_inner_le_inner_abs
#print axioms norm_abs_Lp
#print axioms exists_nonneg_top_Lp
#print axioms inner_le_norm_K
#print axioms exists_pos_eigen
#print axioms exists_pos_eigen_kT
#print axioms exists_nonneg_top_Lp_kT

end MassGap.JentzschKT
