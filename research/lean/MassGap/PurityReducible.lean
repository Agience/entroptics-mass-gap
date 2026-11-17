import Mathlib
import MassGap.PurityConvEigen
import MassGap.PurityPeterWeyl

/-!
# MassGap.PurityReducible — unitary coefficients lie in the span of irreducible coefficients

Appendix C of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford and
S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`)
expands functions on a compact gauge group `G` in the matrix coefficients of its irreducible
representations. This module proves complete reducibility at the level of coefficients: every
coefficient `g ↦ Tr (A σ(g))` of a continuous unitary representation `σ` is a finite sum of
coefficients of continuous irreducible unitary representations.

* `inv_eq_star`, `inv_eq_conjTranspose`: for unitary `σ`, `σ(g⁻¹) = σ(g)ᴴ` (the hypothesis of
  `PurityConvEigen.orthogonality_unitary`).
* `blockRep`: the `p`-block of a representation whose matrices vanish between `p` and `¬p`;
  `blockRep_mem` (unitary), `trace_block`: `Tr (B τ(g))` is the sum of the two block traces.
* `conjHom`: `g ↦ U⋆ σ(g) U` for unitary `U`.
* `mint_mulVec_mem`: for continuous `F`, `(∫ F) x` lies in a subspace containing every `F(g) x`.
* `conjAvg_isHermitian`: `∫ σ(g) E σ(g)ᴴ dg` is Hermitian for Hermitian `E`.
* `exists_block`: a reducible unitary `σ` is conjugate by a unitary `U` to a representation
  whose entries vanish between the level sets of a real function `d` taking at least two
  values. In the proof `d` is the eigenvalue list of `∫ σ(g) v v⋆ σ(g)ᴴ dg` for a nonzero `v`
  in an invariant subspace `W ≠ ⊤`, a matrix that commutes with `σ`, has range in `W` and
  trace `‖v‖²`.
* `irredSpan G`: the span of the coefficients of continuous irreducible unitary
  representations; `coeff_mem_irredSpan`, `isCoeff_mem_irredSpan`: every unitary coefficient
  lies in it (induction on the dimension); `irredSpan_dense`: every continuous `f : G → ℂ` is
  uniformly within any `ε > 0` of an element of `irredSpan G`
  (with `PurityPeterWeyl.coeff_dense`).

The passage to `L²(G)` is `PurityL2.eq_zero_of_inner_coeff`.
-/

namespace MassGap.PurityReducible

open MeasureTheory Module MassGap MassGap.CompactGauge MassGap.GaugeGroup MassGap.PurityRepCharacter
  MassGap.PurityConvEigen MassGap.PurityPeterWeyl

open scoped Matrix ComplexOrder

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Unitary representations -/

theorem inv_eq_star {σ : G →* Matrix ι ι ℂ} (hu : ∀ g, σ g ∈ Matrix.unitaryGroup ι ℂ) (g : G) :
    σ g⁻¹ = star (σ g) := by
  calc σ g⁻¹ = σ g⁻¹ * (σ g * star (σ g)) := by
        rw [Matrix.mem_unitaryGroup_iff.mp (hu g), Matrix.mul_one]
    _ = star (σ g) := by rw [← Matrix.mul_assoc, inv_mul_rep, Matrix.one_mul]

theorem inv_eq_conjTranspose {σ : G →* Matrix ι ι ℂ}
    (hu : ∀ g, σ g ∈ Matrix.unitaryGroup ι ℂ) (g : G) : σ g⁻¹ = (σ g)ᴴ :=
  inv_eq_star hu g

/-! ## Blocks -/

section Block

variable (p : ι → Prop) [DecidablePred p]

omit [DecidableEq ι] in
theorem mul_apply_block {M N : Matrix ι ι ℂ} (hM : ∀ i j, (p i ↔ ¬ p j) → M i j = 0)
    (i j : {x // p x}) : (M * N) i j = ∑ k : {x // p x}, M i k * N k j := by
  have h0 : ∑ k : {x // ¬ p x}, M i k * N k j = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hM i k (by simp [i.2, k.2]), zero_mul]
  rw [Matrix.mul_apply, ← Fintype.sum_subtype_add_sum_subtype p, h0, add_zero]

/-- The `p`-block of a representation whose matrices vanish between `p` and `¬p`. -/
def blockRep (τ : G →* Matrix ι ι ℂ) (hb : ∀ g i j, (p i ↔ ¬ p j) → τ g i j = 0) :
    G →* Matrix {x // p x} {x // p x} ℂ where
  toFun g := (τ g).submatrix Subtype.val Subtype.val
  map_one' := by
    ext i j
    simp [Matrix.one_apply, Subtype.ext_iff]
  map_mul' g h := by
    ext i j
    rw [Matrix.submatrix_apply, map_mul, mul_apply_block p (hb g), Matrix.mul_apply]
    rfl

omit [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] in
theorem blockRep_apply (τ : G →* Matrix ι ι ℂ) (hb : ∀ g i j, (p i ↔ ¬ p j) → τ g i j = 0)
    (g : G) : blockRep p τ hb g = (τ g).submatrix Subtype.val Subtype.val := rfl

omit [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] in
theorem hb_not {τ : G →* Matrix ι ι ℂ} (hb : ∀ g i j, (p i ↔ ¬ p j) → τ g i j = 0) :
    ∀ g i j, (¬ p i ↔ ¬ ¬ p j) → τ g i j = 0 :=
  fun g i j h => hb g i j (by tauto)

omit [MeasurableSpace G] [GaugeGroup G] in
theorem continuous_blockRep {τ : G →* Matrix ι ι ℂ} (hτ : Continuous τ)
    (hb : ∀ g i j, (p i ↔ ¬ p j) → τ g i j = 0) : Continuous (blockRep p τ hb) :=
  hτ.matrix_submatrix _ _

theorem blockRep_mem {τ : G →* Matrix ι ι ℂ} (hu : ∀ g, τ g ∈ Matrix.unitaryGroup ι ℂ)
    (hb : ∀ g i j, (p i ↔ ¬ p j) → τ g i j = 0) (g : G) :
    blockRep p τ hb g ∈ Matrix.unitaryGroup {x // p x} ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h : star (blockRep p τ hb g) = blockRep p τ hb g⁻¹ := by
    rw [blockRep_apply, blockRep_apply, inv_eq_star hu, Matrix.star_eq_conjTranspose,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix]
  rw [h, ← map_mul, mul_inv_cancel, map_one]

omit [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] in
/-- `Tr (B τ(g))` splits over the two blocks. -/
theorem trace_block (τ : G →* Matrix ι ι ℂ) (hb : ∀ g i j, (p i ↔ ¬ p j) → τ g i j = 0)
    (B : Matrix ι ι ℂ) (g : G) :
    Matrix.trace (B * τ g) =
      Matrix.trace (B.submatrix Subtype.val Subtype.val * blockRep p τ hb g) +
        Matrix.trace (B.submatrix Subtype.val Subtype.val *
          blockRep (fun i => ¬ p i) τ (hb_not p hb) g) := by
  rw [Matrix.trace_mul_comm B, Matrix.trace_mul_comm (B.submatrix _ _),
    Matrix.trace_mul_comm (B.submatrix _ _)]
  simp only [Matrix.trace, Matrix.diag]
  rw [← Fintype.sum_subtype_add_sum_subtype p]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => (mul_apply_block p (hb g) i i).trans rfl
  · exact Finset.sum_congr rfl fun i _ =>
      (mul_apply_block (fun i => ¬ p i) (hb_not p hb g) i i).trans rfl

end Block

/-- `g ↦ U⋆ σ(g) U` for unitary `U`. -/
def conjHom (σ : G →* Matrix ι ι ℂ) (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    G →* Matrix ι ι ℂ where
  toFun g := star U * σ g * U
  map_one' := by rw [map_one, Matrix.mul_one, Matrix.mem_unitaryGroup_iff'.mp hU]
  map_mul' g h := by
    rw [map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U (star U), Matrix.mem_unitaryGroup_iff.mp hU, Matrix.one_mul]

omit [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] in
theorem conjHom_apply (σ : G →* Matrix ι ι ℂ) (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (g : G) : conjHom σ U hU g = star U * σ g * U := rfl

/-! ## A non-scalar commuting Hermitian matrix -/

omit [DecidableEq ι] in
theorem mint_mulVec_mem {F : G → Matrix ι ι ℂ} (hF : Continuous F) (W : Submodule ℂ (ι → ℂ))
    (x : ι → ℂ) (hW : ∀ g, F g *ᵥ x ∈ W) : mint F *ᵥ x ∈ W := by
  have hint : Integrable (fun g => F g *ᵥ x) (probHaar G) :=
    integrable_cont (hF.matrix_mulVec continuous_const)
  have heq : mint F *ᵥ x = ∫ g, F g *ᵥ x ∂probHaar G := by
    funext i
    rw [eval_integral (fun j => hint.eval j)]
    simp only [Matrix.mulVec, dotProduct, mint]
    rw [integral_finsetSum _ fun j _ => (integrable_cont (hF.matrix_elem i j)).mul_const (x j)]
    exact Finset.sum_congr rfl fun j _ => (integral_mul_const _ _).symm
  rw [heq]
  exact Convex.integral_mem (W.restrictScalars ℝ).convex W.closed_of_finiteDimensional
    (Filter.Eventually.of_forall hW) hint

theorem conjAvg_isHermitian {σ : G →* Matrix ι ι ℂ} (hu : ∀ g, σ g ∈ Matrix.unitaryGroup ι ℂ)
    {E : Matrix ι ι ℂ} (hE : E.IsHermitian) : (conjAvg σ E).IsHermitian := by
  have hh : ∀ g, (σ g * E * σ g⁻¹)ᴴ = σ g * E * σ g⁻¹ := fun g => by
    rw [inv_eq_conjTranspose hu g, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hE.eq, Matrix.mul_assoc]
  ext i j
  have hF : ∀ g, starRingEnd ℂ ((σ g * E * σ g⁻¹) j i) = (σ g * E * σ g⁻¹) i j := fun g => by
    rw [← RCLike.star_def, ← Matrix.conjTranspose_apply, hh g]
  rw [Matrix.conjTranspose_apply, RCLike.star_def]
  simp only [conjAvg, mint]
  rw [← integral_conj]
  simp_rw [hF]

theorem exists_block {σ : G →* Matrix ι ι ℂ} (hσ : Continuous σ)
    (hu : ∀ g, σ g ∈ Matrix.unitaryGroup ι ℂ) (hirr : ¬ Irred σ) :
    ∃ (U : Matrix ι ι ℂ) (d : ι → ℝ) (i₀ j₀ : ι), U ∈ Matrix.unitaryGroup ι ℂ ∧ d i₀ ≠ d j₀ ∧
      ∀ g i j, d i ≠ d j → (star U * σ g * U) i j = 0 := by
  unfold Irred at hirr
  push Not at hirr
  obtain ⟨W, hW, hbot, htop⟩ := hirr
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  set E : Matrix ι ι ℂ := Matrix.vecMulVec v (star v) with hEdef
  have hE : E.IsHermitian := by
    ext i j
    simp [hEdef, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, mul_comm]
  have hEv : ∀ y, E *ᵥ y = (star v ⬝ᵥ y) • v := fun y => by
    ext i
    simp only [hEdef, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply,
      smul_eq_mul, Finset.sum_mul, Pi.star_apply]
    exact Finset.sum_congr rfl fun j _ => by ring
  set H := conjAvg σ E with hHdef
  have hH : H.IsHermitian := conjAvg_isHermitian hu hE
  have hrange : ∀ x, H *ᵥ x ∈ W := fun x =>
    mint_mulVec_mem (continuous_conj hσ E) W x fun g => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hEv]
      exact hW g _ (W.smul_mem _ hvW)
  have htr : Matrix.trace H ≠ 0 := by
    rw [hHdef, trace_conjAvg hσ E]
    have : Matrix.trace E = star v ⬝ᵥ v := by
      simp only [hEdef, Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, dotProduct,
        Pi.star_apply]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [this]
    exact fun h => hv0 (dotProduct_star_self_eq_zero.mp h)
  obtain ⟨i₀, -⟩ := Function.ne_iff.mp hv0
  let U : Matrix ι ι ℂ := hH.eigenvectorUnitary
  have hU : U ∈ Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary.2
  have hUs : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hsU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  set D : Matrix ι ι ℂ := Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) with hDdef
  have hHU : H = U * D * star U := by
    have h := hH.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at h
  have hD : D = star U * H * U := by
    rw [hHU, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hsU, Matrix.one_mul, Matrix.mul_assoc,
      hsU, Matrix.mul_one]
  have hcancel : ∀ X : Matrix ι ι ℂ, U * (star U * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hUs, Matrix.one_mul]
  have hcomm : ∀ g, star U * σ g * U * D = D * (star U * σ g * U) := fun g => by
    rw [hD]
    simp only [Matrix.mul_assoc, hcancel]
    rw [← Matrix.mul_assoc (σ g) H U, ← conjAvg_comm hσ E g, Matrix.mul_assoc]
  have hj₀ : ∃ j₀, hH.eigenvalues i₀ ≠ hH.eigenvalues j₀ := by
    by_contra hall
    have hall' : ∀ j, hH.eigenvalues j = hH.eigenvalues i₀ := by
      intro j
      by_contra hj
      exact hall ⟨j, fun h => hj h.symm⟩
    set c : ℂ := (hH.eigenvalues i₀ : ℂ) with hc
    have hDc : D = c • (1 : Matrix ι ι ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hDdef, hc, hall' i]
      · simp [hDdef, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    have hHc : H = c • (1 : Matrix ι ι ℂ) := by
      rw [hHU, hDc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUs]
    have hc0 : c ≠ 0 := by
      intro h0
      apply htr
      rw [hHc, h0, zero_smul, Matrix.trace_zero]
    apply htop
    rw [eq_top_iff]
    intro x _
    have hx := hrange (c⁻¹ • x)
    rwa [hHc, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, mul_inv_cancel₀ hc0,
      one_smul] at hx
  obtain ⟨j₀, hne₀⟩ := hj₀
  refine ⟨U, hH.eigenvalues, i₀, j₀, hU, hne₀, ?_⟩
  intro g i j hij
  have h := congrFun (congrFun (hcomm g) i) j
  rw [hDdef, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  by_contra hne
  apply hij
  have h' : (RCLike.ofReal ∘ hH.eigenvalues) j = (RCLike.ofReal ∘ hH.eigenvalues) i :=
    mul_left_cancel₀ hne (h.trans (mul_comm _ _))
  exact (RCLike.ofReal_inj.mp h').symm

/-! ## The span of irreducible coefficients -/

variable (G) in
/-- The span of the coefficients `g ↦ Tr (B τ(g))` of continuous irreducible unitary
representations `τ`. -/
def irredSpan : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ {f | ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ)
    (τ : G →* Matrix κ κ ℂ), Continuous τ ∧ (∀ g, τ g ∈ Matrix.unitaryGroup κ ℂ) ∧ Irred τ ∧
      ∃ B : Matrix κ κ ℂ, f = fun g => Matrix.trace (B * τ g)}

theorem coeff_mem_irredSpan_aux (n : ℕ) :
    ∀ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι), Fintype.card ι = n →
      ∀ (σ : G →* Matrix ι ι ℂ), Continuous σ → (∀ g, σ g ∈ Matrix.unitaryGroup ι ℂ) →
        ∀ A : Matrix ι ι ℂ, (fun g => Matrix.trace (A * σ g)) ∈ irredSpan G := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ι i1 i2 hcard σ hσ hu A
  by_cases hirr : Irred σ
  · exact Submodule.subset_span ⟨ι, i1, i2, σ, hσ, hu, hirr, A, rfl⟩
  obtain ⟨U, d, i₀, j₀, hU, hne, hb⟩ := exists_block hσ hu hirr
  have hUs : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  set τ := conjHom σ U hU with hτdef
  have hτc : Continuous τ :=
    show Continuous fun g => star U * σ g * U from
      (continuous_const.matrix_mul hσ).matrix_mul continuous_const
  have hτu : ∀ g, τ g ∈ Matrix.unitaryGroup ι ℂ := fun g => by
    rw [hτdef, conjHom_apply]
    exact mul_mem (mul_mem (Unitary.star_mem hU) (hu g)) hU
  let p : ι → Prop := fun i => d i = d i₀
  have hbp : ∀ g i j, (p i ↔ ¬ p j) → τ g i j = 0 := fun g i j h =>
    hb g i j fun hij => by
      simp only [p] at h
      rw [hij] at h
      tauto
  set B := star U * A * U with hBdef
  have hA : (fun g => Matrix.trace (A * σ g)) = fun g => Matrix.trace (B * τ g) := by
    funext g
    rw [hτdef, conjHom_apply, hBdef]
    calc Matrix.trace (A * σ g) = Matrix.trace (A * σ g * (U * star U)) := by
          rw [hUs, Matrix.mul_one]
      _ = Matrix.trace (star U * (A * σ g * U)) := by
          rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = Matrix.trace (star U * A * U * (star U * σ g * U)) := by
          congr 1
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc U (star U), hUs, Matrix.one_mul]
  have hsplit : (fun g => Matrix.trace (B * τ g)) =
      (fun g => Matrix.trace (B.submatrix Subtype.val Subtype.val * blockRep p τ hbp g)) +
        fun g => Matrix.trace (B.submatrix Subtype.val Subtype.val *
          blockRep (fun i => ¬ p i) τ (hb_not p hbp) g) :=
    funext fun g => trace_block p τ hbp B g
  rw [hA, hsplit]
  refine add_mem (ih _ ?_ _ inferInstance inferInstance rfl _ (continuous_blockRep p hτc hbp)
    (blockRep_mem p hτu hbp) _) (ih _ ?_ _ inferInstance inferInstance rfl _
    (continuous_blockRep _ hτc _) (blockRep_mem _ hτu _) _)
  · rw [← hcard]
    exact Fintype.card_subtype_lt (x := j₀) fun h => hne h.symm
  · rw [← hcard]
    exact Fintype.card_subtype_lt (x := i₀) fun h => h rfl

/-- Every coefficient of a continuous unitary representation lies in `irredSpan G`. -/
theorem coeff_mem_irredSpan {σ : G →* Matrix ι ι ℂ} (hσ : Continuous σ)
    (hu : ∀ g, σ g ∈ Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    (fun g => Matrix.trace (A * σ g)) ∈ irredSpan G :=
  coeff_mem_irredSpan_aux _ ι inferInstance inferInstance rfl σ hσ hu A

theorem isCoeff_mem_irredSpan {f : G → ℂ} (hf : IsCoeff f) : f ∈ irredSpan G := by
  obtain ⟨κ, k1, k2, σ, A, hσ, hu, hfA⟩ := hf
  rw [show f = fun g => Matrix.trace (A * σ g) from funext hfA]
  exact coeff_mem_irredSpan hσ hu A

/-- Every continuous `f : G → ℂ` is uniformly within any `ε > 0` of `irredSpan G`. -/
theorem irredSpan_dense (f : C(G, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ h ∈ irredSpan G, ∀ g, ‖f g - h g‖ < ε := by
  obtain ⟨κ, k1, k2, σ, A, hσ, hu, hfA⟩ := coeff_dense f hε
  exact ⟨_, coeff_mem_irredSpan hσ hu A, hfA⟩

#print axioms inv_eq_star
#print axioms blockRep_mem
#print axioms trace_block
#print axioms conjHom
#print axioms mint_mulVec_mem
#print axioms conjAvg_isHermitian
#print axioms exists_block
#print axioms coeff_mem_irredSpan
#print axioms isCoeff_mem_irredSpan
#print axioms irredSpan_dense

end MassGap.PurityReducible
