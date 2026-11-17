import MassGap.PurityReducible

/-!
# MassGap.PurityL2 — irreducible coefficients are complete in `L²(G)`

Appendix C of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford and
S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`)
expands functions on a compact gauge group `G` in the matrix coefficients of its irreducible
representations. This module carries `PurityReducible.irredSpan_dense` from `C(G)` to
`L²(G, probHaar G)`.

* `continuous_of_mem_irredSpan`: every element of `irredSpan G` is continuous.
* `irredCM G`: the continuous maps whose underlying function lies in `irredSpan G`;
  `irredCM_dense`: it is dense in `C(G, ℂ)` for the uniform norm.
* `toL2`: the map `C(G, ℂ) → L²(G, probHaar G)`; `coeFn_toL2`: `toL2 G c = c` almost everywhere.
* `toL2_irredCM_dense`: the image of `irredCM G` is dense in `L²(G)`
  (`ContinuousMap.toLp_denseRange`; `probHaar G` is regular).
* `eq_zero_of_inner_irredCM`: an element of `L²(G)` orthogonal to the image of `irredCM G` is
  zero; `eq_zero_of_inner_coeff`: an element of `L²(G)` orthogonal to every coefficient
  `g ↦ Tr (B τ(g))` of every continuous irreducible unitary representation `τ` is zero.
-/

namespace MassGap.PurityL2

open MeasureTheory MassGap MassGap.CompactGauge MassGap.GaugeGroup MassGap.PurityConvEigen
  MassGap.PurityReducible

open scoped InnerProductSpace

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

omit [MeasurableSpace G] [GaugeGroup G] in
/-- Every element of `irredSpan G` is continuous. -/
theorem continuous_of_mem_irredSpan {f : G → ℂ} (hf : f ∈ irredSpan G) : Continuous f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨κ, _, _, τ, hτ, -, -, B, rfl⟩ := hx
    exact (continuous_const.matrix_mul hτ).matrix_trace
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact continuous_const.mul hx

variable (G) in
/-- The continuous maps whose underlying function lies in `irredSpan G`. -/
noncomputable def irredCM : Submodule ℂ C(G, ℂ) :=
  (irredSpan G).comap (ContinuousMap.coeFnLinearMap ℂ)

omit [MeasurableSpace G] [GaugeGroup G] in
theorem mem_irredCM {c : C(G, ℂ)} : c ∈ irredCM G ↔ (c : G → ℂ) ∈ irredSpan G := Iff.rfl

/-- `irredCM G` is dense in `C(G, ℂ)` for the uniform norm. -/
theorem irredCM_dense : Dense (irredCM G : Set C(G, ℂ)) := by
  refine Metric.dense_iff.mpr fun f ε hε => ?_
  obtain ⟨h, hmem, hfh⟩ := irredSpan_dense f (half_pos hε)
  refine ⟨⟨h, continuous_of_mem_irredSpan hmem⟩, ?_, hmem⟩
  rw [Metric.mem_ball, dist_comm]
  refine lt_of_le_of_lt ((ContinuousMap.dist_le (half_pos hε).le).mpr fun g => ?_) (half_lt_self hε)
  rw [dist_eq_norm]
  exact (hfh g).le

variable (G) in
/-- The map `C(G, ℂ) → L²(G, probHaar G)`. -/
noncomputable def toL2 : C(G, ℂ) →L[ℂ] Lp ℂ 2 (probHaar G) :=
  ContinuousMap.toLp (E := ℂ) 2 (probHaar G) ℂ

/-- `toL2 G c` agrees with `c` almost everywhere. -/
theorem coeFn_toL2 (c : C(G, ℂ)) : (toL2 G c : G → ℂ) =ᵐ[probHaar G] c :=
  (ContinuousMap.coeFn_toLp (p := 2) (μ := probHaar G) (𝕜 := ℂ) c).mono fun g hg => by
    rw [toL2, hg]

/-- The image of `irredCM G` is dense in `L²(G)`. -/
theorem toL2_irredCM_dense : Dense (toL2 G '' (irredCM G : Set C(G, ℂ))) :=
  (ContinuousMap.toLp_denseRange ℂ (probHaar G) ℂ (p := 2) (by norm_num)).dense_image
    (toL2 G).continuous irredCM_dense

/-- An element of `L²(G)` orthogonal to the image of `irredCM G` is zero. -/
theorem eq_zero_of_inner_irredCM (f : Lp ℂ 2 (probHaar G))
    (h : ∀ c ∈ irredCM G, ⟪toL2 G c, f⟫_ℂ = 0) : f = 0 := by
  have hcl : IsClosed {x : Lp ℂ 2 (probHaar G) | ⟪x, f⟫_ℂ = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hsub : toL2 G '' (irredCM G : Set C(G, ℂ)) ⊆ {x | ⟪x, f⟫_ℂ = 0} := by
    rintro _ ⟨c, hc, rfl⟩
    exact h c hc
  have hf : f ∈ closure (toL2 G '' (irredCM G : Set C(G, ℂ))) := by
    rw [toL2_irredCM_dense.closure_eq]
    exact Set.mem_univ f
  exact inner_self_eq_zero.mp (hcl.closure_subset_iff.mpr hsub hf)

/-- An element of `L²(G)` orthogonal to every coefficient `g ↦ Tr (B τ(g))` of every continuous
irreducible unitary representation `τ` is zero. -/
theorem eq_zero_of_inner_coeff (f : Lp ℂ 2 (probHaar G))
    (h : ∀ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (τ : G →* Matrix κ κ ℂ)
      (hτ : Continuous τ), (∀ g, τ g ∈ Matrix.unitaryGroup κ ℂ) → Irred τ →
      ∀ B : Matrix κ κ ℂ,
        ⟪toL2 G ⟨fun g => Matrix.trace (B * τ g),
          (continuous_const.matrix_mul hτ).matrix_trace⟩, f⟫_ℂ = 0) : f = 0 := by
  refine eq_zero_of_inner_irredCM f fun c hc => ?_
  have key : ∀ x ∈ irredSpan G, ∃ hx : Continuous x, ⟪toL2 G ⟨x, hx⟩, f⟫_ℂ = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨κ, k1, k2, τ, hτ, hu, hirr, B, rfl⟩ := hx
      exact ⟨_, h κ k1 k2 τ hτ hu hirr B⟩
    | zero =>
      refine ⟨continuous_const, ?_⟩
      have : (⟨0, continuous_const⟩ : C(G, ℂ)) = 0 := rfl
      rw [this, map_zero, inner_zero_left]
    | add x y _ _ hx hy =>
      obtain ⟨hxc, hx0⟩ := hx
      obtain ⟨hyc, hy0⟩ := hy
      refine ⟨hxc.add hyc, ?_⟩
      have : (⟨x + y, hxc.add hyc⟩ : C(G, ℂ)) = ⟨x, hxc⟩ + ⟨y, hyc⟩ := rfl
      rw [this, map_add, inner_add_left, hx0, hy0, add_zero]
    | smul a x _ hx =>
      obtain ⟨hxc, hx0⟩ := hx
      refine ⟨continuous_const.mul hxc, ?_⟩
      have : (⟨a • x, continuous_const.mul hxc⟩ : C(G, ℂ)) = a • ⟨x, hxc⟩ := rfl
      rw [this, map_smul, inner_smul_left, hx0, mul_zero]
  obtain ⟨_, h0⟩ := key _ hc
  exact h0

#print axioms continuous_of_mem_irredSpan
#print axioms irredCM_dense
#print axioms coeFn_toL2
#print axioms toL2_irredCM_dense
#print axioms eq_zero_of_inner_irredCM
#print axioms eq_zero_of_inner_coeff

end MassGap.PurityL2
