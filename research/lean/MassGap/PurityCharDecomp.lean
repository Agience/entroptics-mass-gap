import MassGap.PuritySchurCross

/-!
# MassGap.PurityCharDecomp — the character of a unitary representation decomposes into irreducibles

Appendix C of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford and
S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`)
sums over the irreducible representations `π` of a compact gauge group `G` with weights `d_π`.
This module decomposes the character of a continuous unitary representation `σ` into irreducible
characters and counts the multiplicities.

* `IrrRep G`: a continuous irreducible unitary representation of positive dimension.
* `char_decomp`: for continuous unitary `σ` there is a finite family `R` of `IrrRep G` with
  `Σ_j dim R_j = dim σ` and `Tr σ(g) = Σ_j Tr R_j(g)` for every `g`.
* `mult σ r = ∫ χ_σ conj χ_r dg`; `mult_eq`: it is `Σ_j [r ≃ R_j]` for any finite family `R` of
  `IrrRep G` with `χ_σ = Σ_j χ_{R_j}`.
* `finsum_dim_mult`: for a family `F` such that every `IrrRep G` is equivalent to exactly one
  `F i`, `Σᶠ_i dim (F i) · mult σ (F i) = dim σ`.
-/

namespace MassGap.PurityCharDecomp

open MeasureTheory MassGap MassGap.CompactGauge MassGap.GaugeGroup MassGap.PurityRepCharacter
  MassGap.PurityConvEigen MassGap.PurityReducible MassGap.PuritySchurCross

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

variable (G) in
/-- A continuous irreducible unitary representation of positive dimension. -/
structure IrrRep where
  κ : Type
  [fin : Fintype κ]
  [dec : DecidableEq κ]
  [ne : Nonempty κ]
  τ : G →* Matrix κ κ ℂ
  cont : Continuous τ
  unitary : ∀ g, τ g ∈ Matrix.unitaryGroup κ ℂ
  irred : Irred τ

attribute [instance] IrrRep.fin IrrRep.dec IrrRep.ne

theorem char_decomp_aux (n : ℕ) :
    ∀ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι), Fintype.card ι = n →
      ∀ (σ : G →* Matrix ι ι ℂ), Continuous σ → (∀ g, σ g ∈ Matrix.unitaryGroup ι ℂ) →
        ∃ (J : Type) (_ : Fintype J) (R : J → IrrRep G),
          ∑ j, Fintype.card (R j).κ = n ∧
            ∀ g, Matrix.trace (σ g) = ∑ j, Matrix.trace ((R j).τ g) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ι i1 i2 hcard σ hσ hu
  by_cases hirr : Irred σ
  · rcases isEmpty_or_nonempty ι with hι | hι
    · refine ⟨Empty, inferInstance, Empty.elim, ?_, fun g => ?_⟩
      · rw [← hcard, Fintype.card_eq_zero, Finset.univ_eq_empty, Finset.sum_empty]
      · simp [Matrix.trace]
    · refine ⟨Unit, inferInstance,
        fun _ => { κ := ι, τ := σ, cont := hσ, unitary := hu, irred := hirr }, ?_, fun g => ?_⟩
      · simp [hcard]
      · simp
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
  have htr : ∀ g, Matrix.trace (σ g) = Matrix.trace (τ g) := fun g => by
    rw [hτdef, conjHom_apply, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hUs,
      Matrix.mul_one]
  have hlt1 : Fintype.card {x // p x} < n := by
    rw [← hcard]
    exact Fintype.card_subtype_lt (x := j₀) fun h => hne h.symm
  have hlt2 : Fintype.card {x // ¬ p x} < n := by
    rw [← hcard]
    exact Fintype.card_subtype_lt (x := i₀) fun h => h rfl
  obtain ⟨J₁, f₁, R₁, h₁, e₁⟩ := ih _ hlt1 _ inferInstance inferInstance rfl _
    (continuous_blockRep p hτc hbp) (blockRep_mem p hτu hbp)
  obtain ⟨J₂, f₂, R₂, h₂, e₂⟩ := ih _ hlt2 _ inferInstance inferInstance rfl _
    (continuous_blockRep _ hτc (hb_not p hbp)) (blockRep_mem _ hτu (hb_not p hbp))
  refine ⟨J₁ ⊕ J₂, inferInstance, Sum.elim R₁ R₂, ?_, fun g => ?_⟩
  · rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have hc : Fintype.card {x // p x} + Fintype.card {x // ¬ p x} = n := by
      have := Fintype.card_subtype_le p
      rw [Fintype.card_subtype_compl, ← hcard]
      omega
    rw [← hc, ← h₁, ← h₂]
    convert rfl
  · rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [htr g, ← Matrix.one_mul (τ g), trace_block p τ hbp 1 g,
      Matrix.submatrix_one _ (Subtype.val_injective (p := p)),
      Matrix.submatrix_one _ (Subtype.val_injective (p := fun i => ¬ p i)), Matrix.one_mul,
      Matrix.one_mul, e₁ g, e₂ g]
    rfl

/-- The character of a continuous unitary representation is a sum of irreducible characters
whose dimensions add up to its dimension. -/
theorem char_decomp {ι : Type} [Fintype ι] [DecidableEq ι] {σ : G →* Matrix ι ι ℂ}
    (hσ : Continuous σ) (hu : ∀ g, σ g ∈ Matrix.unitaryGroup ι ℂ) :
    ∃ (J : Type) (_ : Fintype J) (R : J → IrrRep G),
      ∑ j, Fintype.card (R j).κ = Fintype.card ι ∧
        ∀ g, Matrix.trace (σ g) = ∑ j, Matrix.trace ((R j).τ g) :=
  char_decomp_aux _ ι inferInstance inferInstance rfl σ hσ hu

/-- The multiplicity `⟨χ_σ, χ_r⟩ = ∫ χ_σ conj χ_r dg`. -/
noncomputable def mult {ι : Type} [Fintype ι] [DecidableEq ι] (σ : G →* Matrix ι ι ℂ) (r : IrrRep G) : ℂ :=
  ∫ g, Matrix.trace (σ g) * starRingEnd ℂ (Matrix.trace (r.τ g)) ∂probHaar G

open Classical in
/-- `mult σ r` counts the members of a decomposition of `χ_σ` that are equivalent to `r`. -/
theorem mult_eq {ι : Type} [Fintype ι] [DecidableEq ι] {σ : G →* Matrix ι ι ℂ} {J : Type} [Fintype J]
    (R : J → IrrRep G) (e : ∀ g, Matrix.trace (σ g) = ∑ j, Matrix.trace ((R j).τ g))
    (r : IrrRep G) :
    mult σ r = ∑ j, if Equivalent r.τ (R j).τ then (1 : ℂ) else 0 := by
  have hterm : ∀ j, Continuous fun g =>
      Matrix.trace ((R j).τ g) * starRingEnd ℂ (Matrix.trace (r.τ g)) := fun j =>
    (R j).cont.matrix_trace.mul (Complex.continuous_conj.comp r.cont.matrix_trace)
  simp only [mult, e, Finset.sum_mul]
  rw [integral_finsetSum _ fun j _ => integrable_cont (hterm j)]
  exact Finset.sum_congr rfl fun j _ =>
    integral_char r.cont (R j).cont r.irred (R j).irred r.unitary

open Classical in
/-- For a family `F` such that every `IrrRep G` is equivalent to exactly one `F i`,
`Σᶠ_i dim (F i) · mult σ (F i) = dim σ`. -/
theorem finsum_dim_mult {ι : Type} [Fintype ι] [DecidableEq ι] {σ : G →* Matrix ι ι ℂ}
    (hσ : Continuous σ) (hu : ∀ g, σ g ∈ Matrix.unitaryGroup ι ℂ) {I : Type*}
    (F : I → IrrRep G) (hF : ∀ r : IrrRep G, ∃! i, Equivalent (F i).τ r.τ) :
    ∑ᶠ i, (Fintype.card (F i).κ : ℂ) * mult σ (F i) = Fintype.card ι := by
  obtain ⟨J, _, R, hdim, e⟩ := char_decomp hσ hu
  have hrow : ∀ i, (Fintype.card (F i).κ : ℂ) * mult σ (F i) =
      ∑ j, if Equivalent (F i).τ (R j).τ then (Fintype.card (R j).κ : ℂ) else 0 := fun i => by
    rw [mult_eq R e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rw [mul_one, card_eq_of_equivalent (F i).irred (R j).irred h]
    · rw [mul_zero]
  simp_rw [hrow]
  have hcol : ∀ j, ∑ᶠ i, (if Equivalent (F i).τ (R j).τ then (Fintype.card (R j).κ : ℂ) else 0) =
      Fintype.card (R j).κ := fun j => by
    obtain ⟨i₀, hi₀, huniq⟩ := hF (R j)
    rw [finsum_eq_single _ i₀ fun i hi => if_neg fun h => hi (huniq i h), if_pos hi₀]
  rw [finsum_sum_comm]
  · simp_rw [hcol]
    rw [← hdim, Nat.cast_sum]
  · intro j _
    obtain ⟨i₀, -, huniq⟩ := hF (R j)
    refine (Set.finite_singleton i₀).subset fun i hi => ?_
    by_contra hne
    exact hi (if_neg fun h => hne (huniq i h))

#print axioms char_decomp
#print axioms mult_eq
#print axioms finsum_dim_mult

end MassGap.PurityCharDecomp
