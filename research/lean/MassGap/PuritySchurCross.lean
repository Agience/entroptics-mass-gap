import MassGap.PurityReducible

/-!
# MassGap.PuritySchurCross — orthogonality between inequivalent irreducible representations

Appendix C of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford and
S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`)
sums over the irreducible representations `π` of a compact gauge group `G`. This module proves
the orthogonality relations between two of them; `PurityConvEigen.orthogonality` is the case of
one representation.

* `rint`: the entrywise Haar integral of a rectangular-matrix-valued function.
* `Equivalent σ τ`: there is a nonzero `T` with `T σ(g) = τ(g) T` for every `g`; for irreducible
  `σ`, `τ` this is equivalence.
* `avg_intertwines`: `∫ τ(g) E σ(g⁻¹) dg` intertwines `σ` and `τ`.
* `bijective_of_intertwines`: a nonzero intertwiner between irreducible representations is a
  linear bijection; `card_eq_of_equivalent`, `trace_eq_of_equivalent`: equivalent irreducible
  representations have equal dimension and equal character.
* `integral_cross`: for inequivalent `σ`, `τ`, `∫ τ(g)ₐᵦ σ(g⁻¹)꜀ₑ dg = 0`;
  `integral_cross_unitary`: for unitary `σ`, `∫ τ(g)ₐᵦ conj σ(g)ₑ꜀ dg = 0`.
* `integral_trace_mul_conj`: `∫ χ_τ conj χ_σ dg` as a double sum of entry integrals.
* `integral_char_self`: `∫ |χ_σ|² dg = 1` for continuous irreducible unitary `σ` of positive dimension.
* `integral_char`: for continuous irreducible `σ`, `τ` with `σ` unitary of positive dimension,
  `∫ χ_τ conj χ_σ dg` is `1` if `σ` and `τ` are equivalent and `0` otherwise.
-/

namespace MassGap.PuritySchurCross

open MeasureTheory Module MassGap MassGap.CompactGauge MassGap.GaugeGroup
  MassGap.PurityRepCharacter MassGap.PurityConvEigen MassGap.PurityReducible

open scoped Matrix

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-! ## Entrywise Haar integrals of rectangular matrices -/

/-- `∫ F(g) dg`, entrywise. -/
noncomputable def rint (F : G → Matrix κ ι ℂ) : Matrix κ ι ℂ :=
  fun i j => ∫ g, F g i j ∂probHaar G

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem rint_mul_right {F : G → Matrix κ ι ℂ} (hF : Continuous F) (A : Matrix ι ι ℂ) :
    rint F * A = rint (fun g => F g * A) := by
  ext i j
  simp only [rint, Matrix.mul_apply]
  symm
  rw [integral_finsetSum _ fun l _ => (integrable_cont (hF.matrix_elem i l)).mul_const (A l j)]
  exact Finset.sum_congr rfl fun l _ => integral_mul_const _ _

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem rint_mul_left {F : G → Matrix κ ι ℂ} (hF : Continuous F) (A : Matrix κ κ ℂ) :
    A * rint F = rint (fun g => A * F g) := by
  ext i j
  simp only [rint, Matrix.mul_apply]
  symm
  rw [integral_finsetSum _ fun l _ => (integrable_cont (hF.matrix_elem l j)).const_mul (A i l)]
  exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem rint_left (F : G → Matrix κ ι ℂ) (x : G) : rint (fun h => F (x * h)) = rint F := by
  ext i j
  exact integral_mul_left_eq_self (fun h => F h i j) x

/-! ## Intertwiners -/

/-- Some nonzero `T` satisfies `T σ(g) = τ(g) T` for every `g`. For irreducible `σ`, `τ` this is
equivalence (`bijective_of_intertwines`). -/
def Equivalent (σ : G →* Matrix ι ι ℂ) (τ : G →* Matrix κ κ ℂ) : Prop :=
  ∃ T : Matrix κ ι ℂ, T ≠ 0 ∧ ∀ x, T * σ x = τ x * T

/-- `∫ τ(g) E σ(g⁻¹) dg` intertwines `σ` and `τ`. -/
theorem avg_intertwines {σ : G →* Matrix ι ι ℂ} {τ : G →* Matrix κ κ ℂ} (hσ : Continuous σ)
    (hτ : Continuous τ) (E : Matrix κ ι ℂ) (x : G) :
    rint (fun g => τ g * E * σ g⁻¹) * σ x = τ x * rint (fun g => τ g * E * σ g⁻¹) := by
  have hc : Continuous fun g => τ g * E * σ g⁻¹ :=
    (hτ.matrix_mul continuous_const).matrix_mul (hσ.comp continuous_inv)
  rw [rint_mul_right hc, rint_mul_left hc, ← rint_left (fun g => τ g * E * σ g⁻¹ * σ x) x]
  congr 1
  funext g
  simp only [map_mul, mul_inv_rev, Matrix.mul_assoc, inv_mul_rep, Matrix.mul_one]

omit [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] in
/-- A nonzero intertwiner between irreducible representations is a linear bijection. -/
theorem bijective_of_intertwines {σ : G →* Matrix ι ι ℂ} {τ : G →* Matrix κ κ ℂ}
    (hσi : Irred σ) (hτi : Irred τ) {T : Matrix κ ι ℂ} (hT0 : T ≠ 0)
    (hT : ∀ x, T * σ x = τ x * T) : Function.Bijective (Matrix.toLin' T) := by
  have hne : Matrix.toLin' T ≠ 0 := fun h =>
    hT0 (Matrix.toLin'.injective (h.trans (map_zero Matrix.toLin').symm))
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    refine (hσi _ fun g v hv => ?_).resolve_right fun h => hne ?_
    · rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hv ⊢
      rw [Matrix.mulVec_mulVec, hT g, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    · exact LinearMap.ker_eq_top.mp h
  · rw [← LinearMap.range_eq_top]
    refine (hτi _ fun g v hv => ?_).resolve_left fun h => hne (LinearMap.range_eq_bot.mp h)
    obtain ⟨w, rfl⟩ := hv
    refine ⟨σ g *ᵥ w, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hT g,
      ← Matrix.mulVec_mulVec]

omit [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] in
/-- Equivalent irreducible representations have equal dimension. -/
theorem card_eq_of_equivalent {σ : G →* Matrix ι ι ℂ} {τ : G →* Matrix κ κ ℂ}
    (hσi : Irred σ) (hτi : Irred τ) (h : Equivalent σ τ) : Fintype.card ι = Fintype.card κ := by
  obtain ⟨T, hT0, hT⟩ := h
  have e := LinearEquiv.ofBijective _ (bijective_of_intertwines hσi hτi hT0 hT)
  simpa [Module.finrank_fintype_fun_eq_card] using e.finrank_eq

omit [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] in
/-- Equivalent irreducible representations have equal character. -/
theorem trace_eq_of_equivalent {σ : G →* Matrix ι ι ℂ} {τ : G →* Matrix κ κ ℂ}
    (hσi : Irred σ) (hτi : Irred τ) (h : Equivalent σ τ) (x : G) :
    Matrix.trace (τ x) = Matrix.trace (σ x) := by
  obtain ⟨T, hT0, hT⟩ := h
  set e := LinearEquiv.ofBijective _ (bijective_of_intertwines hσi hτi hT0 hT)
  rw [← Matrix.trace_toLin'_eq (τ x), ← Matrix.trace_toLin'_eq (σ x),
    ← LinearMap.trace_conj' (Matrix.toLin' (σ x)) e]
  congr 1
  refine LinearMap.ext fun v => ?_
  obtain ⟨w, rfl⟩ := e.surjective v
  rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, e.symm_apply_apply]
  simp only [e, LinearEquiv.ofBijective_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hT x]

/-! ## Orthogonality -/

/-- For inequivalent `σ`, `τ`: `∫ τ(g)ₐᵦ σ(g⁻¹)꜀ₑ dg = 0`. -/
theorem integral_cross {σ : G →* Matrix ι ι ℂ} {τ : G →* Matrix κ κ ℂ} (hσ : Continuous σ)
    (hτ : Continuous τ) (h : ¬ Equivalent σ τ) (a b : κ) (c e : ι) :
    ∫ g, τ g a b * σ g⁻¹ c e ∂probHaar G = 0 := by
  have hT : rint (fun g => τ g * Matrix.single b c (1 : ℂ) * σ g⁻¹) = 0 := by
    by_contra hne
    exact h ⟨_, hne, avg_intertwines hσ hτ _⟩
  have h0 := congrFun (congrFun hT a) e
  have hentry : ∀ g : G, (τ g * Matrix.single b c (1 : ℂ) * σ g⁻¹ : Matrix κ ι ℂ) a e =
      τ g a b * σ g⁻¹ c e := fun g => by
    simp [Matrix.mul_apply, Matrix.single, Finset.sum_ite_eq, ite_and]
  simpa only [rint, hentry, Matrix.zero_apply] using h0

/-- For inequivalent `σ`, `τ` with `σ` unitary: `∫ τ(g)ₐᵦ conj σ(g)ₑ꜀ dg = 0`. -/
theorem integral_cross_unitary {σ : G →* Matrix ι ι ℂ} {τ : G →* Matrix κ κ ℂ}
    (hσ : Continuous σ) (hτ : Continuous τ) (hσu : ∀ g, σ g ∈ Matrix.unitaryGroup ι ℂ)
    (h : ¬ Equivalent σ τ) (a b : κ) (c e : ι) :
    ∫ g, τ g a b * starRingEnd ℂ (σ g e c) ∂probHaar G = 0 := by
  rw [← integral_cross hσ hτ h a b c e]
  congr 1
  funext g
  rw [inv_eq_conjTranspose hσu g, Matrix.conjTranspose_apply, RCLike.star_def]

/-- `∫ χ_τ conj χ_σ dg = Σₐ Σ꜀ ∫ τ(g)ₐₐ conj σ(g)꜀꜀ dg`. -/
theorem integral_trace_mul_conj {σ : G →* Matrix ι ι ℂ} {τ : G →* Matrix κ κ ℂ}
    (hσ : Continuous σ) (hτ : Continuous τ) :
    ∫ g, Matrix.trace (τ g) * starRingEnd ℂ (Matrix.trace (σ g)) ∂probHaar G =
      ∑ a, ∑ c, ∫ g, τ g a a * starRingEnd ℂ (σ g c c) ∂probHaar G := by
  have hterm : ∀ a c, Continuous fun g => τ g a a * starRingEnd ℂ (σ g c c) := fun a c =>
    (hτ.matrix_elem a a).mul (Complex.continuous_conj.comp (hσ.matrix_elem c c))
  simp only [Matrix.trace, Matrix.diag, map_sum]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun c _ => integrable_cont (hterm a c)]
  exact Finset.sum_congr rfl fun a _ =>
    integral_finsetSum _ fun c _ => integrable_cont (hterm a c)

/-- `∫ |χ_σ|² dg = 1` for a continuous irreducible unitary `σ` of positive dimension. -/
theorem integral_char_self [Nonempty ι] {σ : G →* Matrix ι ι ℂ} (hσ : Continuous σ)
    (hσi : Irred σ) (hσu : ∀ g, σ g ∈ Matrix.unitaryGroup ι ℂ) :
    ∫ g, Matrix.trace (σ g) * starRingEnd ℂ (Matrix.trace (σ g)) ∂probHaar G = 1 := by
  rw [integral_trace_mul_conj hσ hσ]
  simp_rw [orthogonality_unitary hσ hσi (inv_eq_conjTranspose hσu)]
  have hd : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [Prod.mk.injEq, Finset.sum_ite_eq, hd]

open Classical in
/-- Character orthonormality: for continuous irreducible `σ`, `τ` with `σ` unitary of positive
dimension, `∫ χ_τ conj χ_σ dg` is `1` if `σ` and `τ` are equivalent and `0` otherwise. -/
theorem integral_char [Nonempty ι] {σ : G →* Matrix ι ι ℂ} {τ : G →* Matrix κ κ ℂ}
    (hσ : Continuous σ) (hτ : Continuous τ) (hσi : Irred σ) (hτi : Irred τ)
    (hσu : ∀ g, σ g ∈ Matrix.unitaryGroup ι ℂ) :
    ∫ g, Matrix.trace (τ g) * starRingEnd ℂ (Matrix.trace (σ g)) ∂probHaar G =
      if Equivalent σ τ then 1 else 0 := by
  split_ifs with h
  · simp_rw [trace_eq_of_equivalent hσi hτi h]
    exact integral_char_self hσ hσi hσu
  · rw [integral_trace_mul_conj hσ hτ]
    simp [integral_cross_unitary hσ hτ hσu h]

#print axioms avg_intertwines
#print axioms bijective_of_intertwines
#print axioms card_eq_of_equivalent
#print axioms trace_eq_of_equivalent
#print axioms integral_cross
#print axioms integral_cross_unitary
#print axioms integral_trace_mul_conj
#print axioms integral_char_self
#print axioms integral_char

end MassGap.PuritySchurCross
