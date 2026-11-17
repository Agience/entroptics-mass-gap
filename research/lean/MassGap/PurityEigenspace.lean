import MassGap.PurityL2
import MassGap.PurityCharDecomp

/-!
# MassGap.PurityEigenspace — the `a`-eigenspace of convolution by a class function

Appendix C of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford and
S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`)
diagonalises convolution by the Wilson kernel on `L²(G)`: the irreducible representation `π`
contributes the eigenvalue `a_π` with its `d_π²` matrix coefficients. This module proves that
these coefficients exhaust each eigenspace. `k` is a continuous class function and `G` a compact
gauge group with normalised Haar measure.

* `integral_kernel_conj`: `∫ k(h) conj Tr(B τ(hg)) dh = a_τ conj Tr(B τ(g))` for unitary `τ`.
* `conv_trace`: `k ⋆ Tr(C τ(·)) = a_τ Tr(C τ(·))`.
* `integral_conj_conv`: `∫ conj c · (k ⋆ f) = e ∫ conj c · f` for integrable `f` and continuous
  `c` with `∫ k(h) conj c(hg) dh = e conj c(g)` (Fubini and left invariance).
* `integral_conj_eq_zero`, `inner_coeff_eq_zero`: an integrable (resp. `L²`) solution of
  `k ⋆ f = a f` is orthogonal to every coefficient of every continuous irreducible unitary `τ`
  of positive dimension with `a_τ ≠ a`.
* `conv_congr_ae`: `k ⋆ f` depends only on the almost-everywhere class of `f`.
* `coeffSpan G k a`: the closed span in `L²(G)` of the coefficients `g ↦ Tr(B r.τ(g))` of the
  `r : IrrRep G` with `a_{r.τ} = a`; `conv_toL2_coeff`, `toL2_coeff_mem_coeffSpan`: each
  coefficient of `r : IrrRep G` solves `k ⋆ f = a_{r.τ} f` almost everywhere and lies in
  `coeffSpan G k a_{r.τ}`; `inner_coeffSpan_eq_zero`:
  a coefficient of `τ` with `a_τ ≠ a` is orthogonal to `coeffSpan G k a`.
* `mem_coeffSpan`: every `f ∈ L²(G)` with `k ⋆ f = a f` almost everywhere lies in
  `coeffSpan G k a`; `eq_zero_of_eigen`: if no `r : IrrRep G` has `a_{r.τ} = a`, then `f = 0`.
-/

namespace MassGap.PurityEigenspace

open MeasureTheory MassGap MassGap.CompactGauge MassGap.GaugeGroup MassGap.PurityRepCharacter
  MassGap.PurityConvEigen MassGap.PurityReducible MassGap.PurityL2 MassGap.PurityCharDecomp

open scoped InnerProductSpace Matrix

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- For unitary `τ`, `conj Tr(B τ(x)) = Tr(Bᴴ τ(x⁻¹))`. -/
theorem conj_trace {τ : G →* Matrix κ κ ℂ} (hu : ∀ g, τ g ∈ Matrix.unitaryGroup κ ℂ)
    (B : Matrix κ κ ℂ) (x : G) :
    starRingEnd ℂ (Matrix.trace (B * τ x)) = Matrix.trace (Bᴴ * τ x⁻¹) := by
  rw [starRingEnd_apply, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    ← inv_eq_conjTranspose hu, Matrix.trace_mul_comm]

/-- `∫ k(h) conj Tr(B τ(hg)) dh = a_τ conj Tr(B τ(g))` for continuous irreducible unitary `τ`. -/
theorem integral_kernel_conj [Nonempty κ] {τ : G →* Matrix κ κ ℂ} (hτ : Continuous τ)
    (hu : ∀ g, τ g ∈ Matrix.unitaryGroup κ ℂ) (hirr : Irred τ) {k : G → ℂ} (hk : Continuous k)
    (hkc : ∀ x h, k (x * h * x⁻¹) = k h) (B : Matrix κ κ ℂ) (g : G) :
    ∫ h, k h * starRingEnd ℂ (Matrix.trace (B * τ (h * g))) ∂probHaar G =
      eigenval k τ * starRingEnd ℂ (Matrix.trace (B * τ g)) := by
  have hF : Continuous fun h => k h • τ h⁻¹ := hk.smul (hτ.comp continuous_inv)
  have hF' : Continuous fun h => (k h • τ h⁻¹) * (Bᴴ * τ g⁻¹) :=
    hF.matrix_mul continuous_const
  have hpt : ∀ h, k h * starRingEnd ℂ (Matrix.trace (B * τ (h * g))) =
      Matrix.trace ((k h • τ h⁻¹) * (Bᴴ * τ g⁻¹)) := fun h => by
    rw [conj_trace hu, mul_inv_rev, map_mul, ← Matrix.mul_assoc Bᴴ,
      Matrix.trace_mul_comm (Bᴴ * τ g⁻¹), Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp_rw [hpt]
  rw [← trace_mint hF', ← mint_mul_right hF (Bᴴ * τ g⁻¹), mint_kernel hτ hirr hk hkc,
    Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul, conj_trace hu]

/-- Convolution by `k` multiplies every trace coefficient `g ↦ Tr(C τ(g))` of a continuous
irreducible `τ` by `a_τ`. -/
theorem conv_trace [Nonempty κ] {τ : G →* Matrix κ κ ℂ} (hτ : Continuous τ) (hirr : Irred τ)
    {k : G → ℂ} (hk : Continuous k) (hkc : ∀ x h, k (x * h * x⁻¹) = k h) (C : Matrix κ κ ℂ) :
    conv k (fun g => Matrix.trace (C * τ g)) =
      eigenval k τ • fun g => Matrix.trace (C * τ g) := by
  have hsum : (fun g => Matrix.trace (C * τ g)) = ∑ p : κ × κ, C p.2 p.1 • coeff τ p := by
    funext g
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply,
      coeff, smul_eq_mul, Fintype.sum_prod_type]
    exact Finset.sum_comm
  have hmem : (fun g => Matrix.trace (C * τ g)) ∈ Submodule.span ℂ (Set.range (coeff τ)) := by
    rw [hsum]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  exact (conv_eigen_multiplicity hτ hirr hk hkc).1 _ hmem

/-- `∫ conj c · (k ⋆ f) = e ∫ conj c · f` for integrable `f` and continuous `c` with
`∫ k(h) conj c(hg) dh = e conj c(g)` for every `g`. -/
theorem integral_conj_conv {k c f : G → ℂ} {e : ℂ} (hk : Continuous k) (hc : Continuous c)
    (hf : Integrable f (probHaar G))
    (hkc : ∀ g, ∫ h, k h * starRingEnd ℂ (c (h * g)) ∂probHaar G = e * starRingEnd ℂ (c g)) :
    ∫ g, starRingEnd ℂ (c g) * conv k f g ∂probHaar G =
      e * ∫ g, starRingEnd ℂ (c g) * f g ∂probHaar G := by
  let J : G × G → ℂ := fun z => starRingEnd ℂ (c (z.1 * z.2)) * (k z.1 * f z.2)
  let I : G × G → ℂ := fun z => starRingEnd ℂ (c z.2) * (k z.1 * f (z.1⁻¹ * z.2))
  obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
  have hJc : Continuous fun z : G × G => starRingEnd ℂ (c (z.1 * z.2)) :=
    Complex.continuous_conj.comp (hc.comp continuous_mul)
  have hJ : Integrable J ((probHaar G).prod (probHaar G)) :=
    ((integrable_cont hk).mul_prod hf).bdd_mul hJc.aestronglyMeasurable
      (ae_of_all _ fun z => by
        rw [Complex.norm_conj]
        exact hC _ ⟨_, rfl⟩)
  have hφ := measurePreserving_prod_inv_mul (probHaar G) (probHaar G)
  have hIJ : I = fun z => J (z.1, z.1⁻¹ * z.2) := by
    funext z
    simp only [I, J, mul_inv_cancel_left]
  have hI : Integrable I ((probHaar G).prod (probHaar G)) := by
    rw [hIJ]
    exact hφ.integrable_comp_of_integrable hJ
  have h1 : ∫ z, I z ∂(probHaar G).prod (probHaar G) =
      ∫ g, starRingEnd ℂ (c g) * conv k f g ∂probHaar G := by
    rw [integral_prod_symm I hI]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    simp only [I, conv, integral_const_mul]
  have h2 : ∫ z, I z ∂(probHaar G).prod (probHaar G) =
      ∫ z, J z ∂(probHaar G).prod (probHaar G) := by
    rw [hIJ]
    conv_rhs => rw [← hφ.map_eq]
    exact (integral_map hφ.measurable.aemeasurable
      (by rw [hφ.map_eq]; exact hJ.aestronglyMeasurable)).symm
  have h3 : ∫ z, J z ∂(probHaar G).prod (probHaar G) =
      e * ∫ g, starRingEnd ℂ (c g) * f g ∂probHaar G := by
    rw [integral_prod_symm J hJ, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    have hJg : ∀ h, J (h, g) = f g * (k h * starRingEnd ℂ (c (h * g))) := fun h => by
      simp only [J]
      ring
    simp only [hJg, integral_const_mul, hkc]
    ring
  rw [← h1, h2, h3]

/-- An integrable solution of `k ⋆ f = a f` is orthogonal to every coefficient
`g ↦ Tr(B τ(g))` of a continuous irreducible unitary `τ` with `a_τ ≠ a`. -/
theorem integral_conj_eq_zero [Nonempty κ] {τ : G →* Matrix κ κ ℂ} (hτ : Continuous τ)
    (hu : ∀ g, τ g ∈ Matrix.unitaryGroup κ ℂ) (hirr : Irred τ) {k : G → ℂ} (hk : Continuous k)
    (hkc : ∀ x h, k (x * h * x⁻¹) = k h) (B : Matrix κ κ ℂ) {f : G → ℂ}
    (hfi : Integrable f (probHaar G)) {a : ℂ} (hf : conv k f =ᵐ[probHaar G] fun g => a * f g)
    (hne : eigenval k τ ≠ a) :
    ∫ g, starRingEnd ℂ (Matrix.trace (B * τ g)) * f g ∂probHaar G = 0 := by
  have h := integral_conj_conv hk (continuous_const.matrix_mul hτ).matrix_trace hfi
    (integral_kernel_conj hτ hu hirr hk hkc B)
  have h' : ∫ g, starRingEnd ℂ (Matrix.trace (B * τ g)) * conv k f g ∂probHaar G =
      a * ∫ g, starRingEnd ℂ (Matrix.trace (B * τ g)) * f g ∂probHaar G := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hf] with g hg
    rw [hg]
    ring
  have hz : (eigenval k τ - a) *
      ∫ g, starRingEnd ℂ (Matrix.trace (B * τ g)) * f g ∂probHaar G = 0 := by
    rw [sub_mul, ← h, h', sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

/-- `⟪c, f⟫ = ∫ conj c · f` in `L²(G)`. -/
theorem inner_toL2 (c : C(G, ℂ)) (f : Lp ℂ 2 (probHaar G)) :
    ⟪toL2 G c, f⟫_ℂ = ∫ g, starRingEnd ℂ (c g) * f g ∂probHaar G := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := probHaar G) (𝕜 := ℂ) c] with g hg
  simp only [toL2]
  rw [hg, RCLike.inner_apply']

/-- An `L²` solution of `k ⋆ f = a f` is orthogonal to every coefficient of a continuous
irreducible unitary `τ` with `a_τ ≠ a`. -/
theorem inner_coeff_eq_zero [Nonempty κ] {τ : G →* Matrix κ κ ℂ} (hτ : Continuous τ)
    (hu : ∀ g, τ g ∈ Matrix.unitaryGroup κ ℂ) (hirr : Irred τ) {k : G → ℂ} (hk : Continuous k)
    (hkc : ∀ x h, k (x * h * x⁻¹) = k h) (B : Matrix κ κ ℂ) (f : Lp ℂ 2 (probHaar G)) {a : ℂ}
    (hf : conv k f =ᵐ[probHaar G] fun g => a * f g) (hne : eigenval k τ ≠ a) :
    ⟪toL2 G ⟨fun g => Matrix.trace (B * τ g), (continuous_const.matrix_mul hτ).matrix_trace⟩,
      f⟫_ℂ = 0 := by
  rw [inner_toL2]
  exact integral_conj_eq_zero hτ hu hirr hk hkc B ((Lp.memLp f).integrable one_le_two) hf hne

/-- `k ⋆ f` depends only on the almost-everywhere class of `f`. -/
theorem conv_congr_ae (k : G → ℂ) {f f' : G → ℂ} (h : f =ᵐ[probHaar G] f') :
    conv k f = conv k f' := by
  funext g
  have hmp : MeasurePreserving (fun x : G => x⁻¹ * g) (probHaar G) (probHaar G) :=
    (measurePreserving_mul_right (probHaar G) g).comp (Measure.measurePreserving_inv (probHaar G))
  simp only [conv]
  refine integral_congr_ae ?_
  filter_upwards [hmp.quasiMeasurePreserving.ae_eq_comp h] with x hx
  exact congrArg (k x * ·) hx

/-- Each coefficient `g ↦ Tr(B r.τ(g))` of `r : IrrRep G` solves `k ⋆ f = a_{r.τ} f` almost
everywhere. -/
theorem conv_toL2_coeff (r : IrrRep G) {k : G → ℂ} (hk : Continuous k)
    (hkc : ∀ x h, k (x * h * x⁻¹) = k h) (B : Matrix r.κ r.κ ℂ) :
    conv k (toL2 G ⟨fun g => Matrix.trace (B * r.τ g),
        (continuous_const.matrix_mul r.cont).matrix_trace⟩ : G → ℂ) =ᵐ[probHaar G]
      fun g => eigenval k r.τ * (toL2 G ⟨fun g => Matrix.trace (B * r.τ g),
        (continuous_const.matrix_mul r.cont).matrix_trace⟩ : G → ℂ) g := by
  set c : C(G, ℂ) := ⟨fun g => Matrix.trace (B * r.τ g),
    (continuous_const.matrix_mul r.cont).matrix_trace⟩
  have hae := coeFn_toL2 c
  rw [conv_congr_ae k hae]
  filter_upwards [hae] with g hg
  rw [hg]
  exact congrFun (conv_trace r.cont r.irred hk hkc B) g

variable (G) in
/-- The closed span in `L²(G)` of the coefficients `g ↦ Tr(B r.τ(g))` of the `r : IrrRep G` with
`a_{r.τ} = a`. -/
noncomputable def coeffSpan (k : G → ℂ) (a : ℂ) : Submodule ℂ (Lp ℂ 2 (probHaar G)) :=
  (Submodule.span ℂ {v | ∃ r : IrrRep G, eigenval k r.τ = a ∧ ∃ B : Matrix r.κ r.κ ℂ,
    v = toL2 G ⟨fun g => Matrix.trace (B * r.τ g),
      (continuous_const.matrix_mul r.cont).matrix_trace⟩}).topologicalClosure

/-- Each coefficient of `r : IrrRep G` lies in `coeffSpan G k a_{r.τ}`. -/
theorem toL2_coeff_mem_coeffSpan (r : IrrRep G) (k : G → ℂ) (B : Matrix r.κ r.κ ℂ) :
    toL2 G ⟨fun g => Matrix.trace (B * r.τ g), (continuous_const.matrix_mul r.cont).matrix_trace⟩ ∈
      coeffSpan G k (eigenval k r.τ) :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨r, rfl, B, rfl⟩)

/-- Every coefficient of a continuous irreducible unitary `τ` with `a_τ ≠ a` is orthogonal to
`coeffSpan G k a`. -/
theorem inner_coeffSpan_eq_zero [Nonempty κ] {τ : G →* Matrix κ κ ℂ} (hτ : Continuous τ)
    (hu : ∀ g, τ g ∈ Matrix.unitaryGroup κ ℂ) (hirr : Irred τ) {k : G → ℂ} (hk : Continuous k)
    (hkc : ∀ x h, k (x * h * x⁻¹) = k h) (B : Matrix κ κ ℂ) {a : ℂ} (hne : eigenval k τ ≠ a)
    {w : Lp ℂ 2 (probHaar G)} (hw : w ∈ coeffSpan G k a) :
    ⟪toL2 G ⟨fun g => Matrix.trace (B * τ g), (continuous_const.matrix_mul hτ).matrix_trace⟩,
      w⟫_ℂ = 0 := by
  set v := toL2 G ⟨fun g => Matrix.trace (B * τ g), (continuous_const.matrix_mul hτ).matrix_trace⟩
  have hle : coeffSpan G k a ≤ (ℂ ∙ v)ᗮ := by
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_)
      (Submodule.isClosed_orthogonal _)
    rintro _ ⟨r, he, B', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_toL2]
    have hae := coeFn_toL2
      (⟨fun g => Matrix.trace (B' * r.τ g), (continuous_const.matrix_mul r.cont).matrix_trace⟩ :
        C(G, ℂ))
    rw [integral_congr_ae (hae.mono fun g hg => by rw [hg])]
    refine integral_conj_eq_zero hτ hu hirr hk hkc B
      (integrable_cont (continuous_const.matrix_mul r.cont).matrix_trace) ?_ (he ▸ hne)
    refine ae_of_all _ fun g => ?_
    exact congrFun (conv_trace r.cont r.irred hk hkc B') g
  exact (Submodule.mem_orthogonal_singleton_iff_inner_right).mp (hle hw)

/-- Every `f ∈ L²(G)` with `k ⋆ f = a f` almost everywhere lies in the closed span of the
coefficients of the `r : IrrRep G` with `a_{r.τ} = a`. -/
theorem mem_coeffSpan {k : G → ℂ} (hk : Continuous k) (hkc : ∀ x h, k (x * h * x⁻¹) = k h)
    {a : ℂ} (f : Lp ℂ 2 (probHaar G)) (hf : conv k f =ᵐ[probHaar G] fun g => a * f g) :
    f ∈ coeffSpan G k a := by
  set K := coeffSpan G k a
  haveI : CompleteSpace K := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hr : f - K.starProjection f ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal f
  have hr0 : f - K.starProjection f = 0 := by
    refine eq_zero_of_inner_coeff _ fun κ _ _ τ hτ hu hirr B => ?_
    rcases isEmpty_or_nonempty κ with hκ | hκ
    · have h0 : (⟨fun g => Matrix.trace (B * τ g), (continuous_const.matrix_mul hτ).matrix_trace⟩ :
          C(G, ℂ)) = 0 := by
        ext g
        simp [Matrix.trace]
      rw [h0, map_zero, inner_zero_left]
    by_cases he : eigenval k τ = a
    · refine Submodule.inner_right_of_mem_orthogonal
        (Submodule.le_topologicalClosure _ (Submodule.subset_span ?_)) hr
      rw [Set.mem_setOf_eq]
      exact ⟨{ κ := κ, ne := hκ, τ := τ, cont := hτ, unitary := hu, irred := hirr }, he, B, rfl⟩
    · rw [inner_sub_right, inner_coeff_eq_zero hτ hu hirr hk hkc B f hf he,
        inner_coeffSpan_eq_zero hτ hu hirr hk hkc B he (K.starProjection_apply_mem f), sub_zero]
  rw [sub_eq_zero.mp hr0]
  exact K.starProjection_apply_mem f

/-- If no `r : IrrRep G` has `a_{r.τ} = a`, the only
`f ∈ L²(G)` with `k ⋆ f = a f` almost everywhere is `0`. -/
theorem eq_zero_of_eigen {k : G → ℂ} (hk : Continuous k) (hkc : ∀ x h, k (x * h * x⁻¹) = k h)
    {a : ℂ} (ha : ∀ r : IrrRep G, eigenval k r.τ ≠ a)
    (f : Lp ℂ 2 (probHaar G)) (hf : conv k f =ᵐ[probHaar G] fun g => a * f g) : f = 0 := by
  have hle : coeffSpan G k a ≤ ⊥ := by
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) ?_
    · rintro _ ⟨r, he, -⟩
      exact absurd he (ha r)
    · rw [Submodule.bot_coe]
      exact isClosed_singleton
  exact (Submodule.mem_bot ℂ).mp (hle (mem_coeffSpan hk hkc f hf))

#print axioms integral_kernel_conj
#print axioms conv_trace
#print axioms integral_conj_conv
#print axioms integral_conj_eq_zero
#print axioms inner_coeff_eq_zero
#print axioms conv_congr_ae
#print axioms conv_toL2_coeff
#print axioms toL2_coeff_mem_coeffSpan
#print axioms inner_coeffSpan_eq_zero
#print axioms mem_coeffSpan
#print axioms eq_zero_of_eigen

end MassGap.PurityEigenspace
