import Mathlib

/-!
# MassGap.LatticeGauge — Euclidean/permutation invariance of lattice-gauge correlations,
DERIVED from Haar-invariance (Residual A of the ledger, step A1)

This is the first increment of the **physical-fidelity lift**. In `WilsonInstance.lean` the
Osterwalder–Schrader invariances `os_euc`/`os_perm` are discharged by `rfl`: the reflected form
factors through an inert label that the `Perm (Fin 4)` actions leave fixed, so invariance holds for
*any* form reading that label — it is *modelled*, not *derived* from the gauge measure.

Here we build a genuine finite lattice gauge measure over a compact gauge group `G` (as a measurable
space with a left-invariant probability Haar measure `μ`) and **derive** the invariance of Gibbs
correlations from two real facts:

* the product Haar measure over links is preserved by relabelling links
  (`reindex_measurePreserving`, via `MeasureTheory.measurePreserving_piCongrLeft`); and
* the Wilson action is invariant under a lattice symmetry because that symmetry permutes plaquettes
  (`action_invariant`, from the `Symmetry.compat` datum — a checkable combinatorial property of a
  real lattice, *not* a physics axiom and *not* a `rfl` dodge on the correlation).

The payoff, `expect_invariant : ⟨O ∘ reindex⟩ = ⟨O⟩`, is the honest form of `os_euc`/`os_perm`.

Deliberately abstract over the gauge group: the derivation needs only a measurable space with a
probability measure and a symmetry that permutes links/plaquettes compatibly. Instantiating `G` at
`Matrix.specialUnitaryGroup n ℂ` (supplying its compactness/topology/Haar instances) is the separate
step A2; wiring `wilsonCorr` to `expect` and retiring the `rfl` invariances is step A3.

Foundational footprint only (`#print axioms` at the end). Build on the remote box:
`lake build MassGap.LatticeGauge`.
-/

namespace MassGap.LatticeGauge

open MeasureTheory

/-- A finite lattice gauge system over a measurable gauge group `G`: a finite set of links, a finite
set of plaquettes, a holonomy reading each plaquette's group element from a configuration, and a
plaquette action density `φ` (a class function of the holonomy). The holonomy is left abstract at
this step — any map satisfying the symmetry compatibility below yields the invariance; the concrete
"ordered product of link variables around the plaquette" is supplied when a real lattice is built. -/
structure System (G : Type) [MeasurableSpace G] where
  Link : Type
  [linkFin : Fintype Link]
  Plaq : Type
  [plaqFin : Fintype Plaq]
  hol : Plaq → (Link → G) → G
  φ : G → ℝ

attribute [instance] System.linkFin System.plaqFin

variable {G : Type} [MeasurableSpace G]

namespace System

/-- Configurations: a group element on each link. -/
abbrev Config (sys : System G) : Type := sys.Link → G

/-- The Wilson action: the plaquette action density summed over plaquettes. -/
noncomputable def action (sys : System G) (U : sys.Config) : ℝ :=
  ∑ p, sys.φ (sys.hol p U)

/-- The Boltzmann weight `e^{-β S}`. -/
noncomputable def boltz (sys : System G) (β : ℝ) (U : sys.Config) : ℝ :=
  Real.exp (-β * sys.action U)

/-- The product Haar measure over links (each link independently carries `μ`). -/
noncomputable def vol (sys : System G) (μ : Measure G) : Measure sys.Config :=
  Measure.pi (fun _ => μ)

/-- The unnormalised correlation numerator `∫ O · e^{-βS}`. -/
noncomputable def corrNum (sys : System G) (μ : Measure G) (β : ℝ) (O : sys.Config → ℝ) : ℝ :=
  ∫ U, O U * sys.boltz β U ∂(sys.vol μ)

/-- The partition function `Z = ∫ e^{-βS}`. -/
noncomputable def partition (sys : System G) (μ : Measure G) (β : ℝ) : ℝ :=
  ∫ U, sys.boltz β U ∂(sys.vol μ)

/-- The Gibbs expectation `⟨O⟩ = (∫ O e^{-βS}) / Z`. -/
noncomputable def expect (sys : System G) (μ : Measure G) (β : ℝ) (O : sys.Config → ℝ) : ℝ :=
  sys.corrNum μ β O / sys.partition μ β

/-- **The invariance mechanism, in general.** For ANY measure-preserving equivalence `T` of the
configuration space whose Boltzmann weight is invariant (`boltz β (T U) = boltz β U`), the Gibbs
expectation is invariant under transporting the observable: `⟨O ∘ T⟩ = ⟨O⟩`. This is the measure-
theoretic core shared by the geometric symmetry (`T = reindex`) and the gauge symmetry (`T = conj`);
the partition function is untouched, and the numerator is a measure-preserving change of variables. -/
theorem expect_invariant_of_mp (sys : System G) (μ : Measure G) (β : ℝ) (O : sys.Config → ℝ)
    (T : sys.Config ≃ᵐ sys.Config) (hT : MeasurePreserving T (sys.vol μ) (sys.vol μ))
    (hw : ∀ U, sys.boltz β (T U) = sys.boltz β U) :
    sys.expect μ β (fun U => O (T U)) = sys.expect μ β O := by
  have hcorr : sys.corrNum μ β (fun U => O (T U)) = sys.corrNum μ β O := by
    unfold System.corrNum
    calc ∫ U, O (T U) * sys.boltz β U ∂(sys.vol μ)
        = ∫ U, O (T U) * sys.boltz β (T U) ∂(sys.vol μ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
          simp only [hw]
      _ = ∫ U, O U * sys.boltz β U ∂(sys.vol μ) :=
          hT.integral_comp' (fun U => O U * sys.boltz β U)
  unfold System.expect
  rw [hcorr]

end System

/-- A geometric symmetry of a lattice gauge system: a permutation of the links together with the
induced permutation of the plaquettes, **compatible** with the holonomy — relabelling the links by
`onLink` sends the holonomy of a plaquette `p` to the holonomy of the permuted plaquette `onPlaq p`.
This is the honest content of "the symmetry permutes plaquettes": a finite, checkable combinatorial
property of a real lattice, carrying no physics axiom and no `rfl` on the correlation. -/
structure Symmetry (sys : System G) where
  onLink : Equiv.Perm sys.Link
  onPlaq : Equiv.Perm sys.Plaq
  compat : ∀ (p : sys.Plaq) (U : sys.Config),
    sys.hol p (fun l => U (onLink l)) = sys.hol (onPlaq p) U

namespace Symmetry

variable {sys : System G}

/-- The measurable relabelling of configurations induced by a link permutation `e`:
`reindex e U l = U (e l)`. Realised as the inverse of `MeasurableEquiv.piCongrLeft`, whose symmetric
apply reduces with no dependent cast (constant fibres). -/
noncomputable def reindex (e : Equiv.Perm sys.Link) : sys.Config ≃ᵐ sys.Config :=
  (MeasurableEquiv.piCongrLeft (fun _ : sys.Link => G) e).symm

@[simp] theorem reindex_apply (e : Equiv.Perm sys.Link) (U : sys.Config) (l : sys.Link) :
    reindex e U l = U (e l) := rfl

/-- Relabelling links preserves the product Haar measure (identical factors), from
`MeasureTheory.measurePreserving_piCongrLeft` and closure of measure-preservation under `symm`. -/
theorem reindex_measurePreserving (μ : Measure G) [IsProbabilityMeasure μ]
    (e : Equiv.Perm sys.Link) :
    MeasurePreserving (reindex (sys := sys) e) (sys.vol μ) (sys.vol μ) := by
  have h : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : sys.Link => G) e)
      (sys.vol μ) (sys.vol μ) := by
    have hmp := measurePreserving_piCongrLeft (μ := fun _ : sys.Link => μ) e
    simpa [System.vol] using hmp
  exact MeasurePreserving.symm (MeasurableEquiv.piCongrLeft (fun _ : sys.Link => G) e) h

/-- **The Wilson action is invariant under the symmetry** — DERIVED from `compat` by reindexing the
plaquette sum along `onPlaq`. -/
theorem action_invariant (sym : Symmetry sys) (U : sys.Config) :
    sys.action (reindex sym.onLink U) = sys.action U := by
  have hcfg : (reindex sym.onLink U) = (fun l => U (sym.onLink l)) :=
    funext (fun l => reindex_apply sym.onLink U l)
  have hp : ∀ p, sys.hol p (reindex sym.onLink U) = sys.hol (sym.onPlaq p) U := by
    intro p; rw [hcfg]; exact sym.compat p U
  calc sys.action (reindex sym.onLink U)
      = ∑ p, sys.φ (sys.hol (sym.onPlaq p) U) := by
        unfold System.action; exact Finset.sum_congr rfl (fun p _ => by rw [hp p])
    _ = ∑ p, sys.φ (sys.hol p U) := Equiv.sum_comp sym.onPlaq (fun p => sys.φ (sys.hol p U))
    _ = sys.action U := rfl

/-- The Boltzmann weight is invariant under the symmetry (from `action_invariant`). -/
theorem boltz_invariant (sym : Symmetry sys) (β : ℝ) (U : sys.Config) :
    sys.boltz β (reindex sym.onLink U) = sys.boltz β U := by
  unfold System.boltz; rw [action_invariant]

/-- **The correlation numerator is invariant under the symmetry** — DERIVED: the measure-preserving
change of variables `U ↦ reindex U` (Haar-invariance) composed with weight invariance. -/
theorem corrNum_invariant (sys : System G) (μ : Measure G) [IsProbabilityMeasure μ]
    (sym : Symmetry sys) (β : ℝ) (O : sys.Config → ℝ) :
    sys.corrNum μ β (fun U => O (reindex sym.onLink U)) = sys.corrNum μ β O := by
  have hmp := reindex_measurePreserving (sys := sys) μ sym.onLink
  unfold System.corrNum
  calc ∫ U, O (reindex sym.onLink U) * sys.boltz β U ∂(sys.vol μ)
      = ∫ U, O (reindex sym.onLink U) * sys.boltz β (reindex sym.onLink U) ∂(sys.vol μ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
        simp only [boltz_invariant]
    _ = ∫ U, O U * sys.boltz β U ∂(sys.vol μ) :=
        hmp.integral_comp' (fun U => O U * sys.boltz β U)

/-- **The Gibbs expectation is invariant under the symmetry** — `⟨O ∘ reindex⟩ = ⟨O⟩`. This is the
honest, DERIVED form of the Osterwalder–Schrader invariances `os_euc` / `os_perm`: not a `rfl`
through an inert label, but a consequence of Haar-invariance of the measure and plaquette-permutation
invariance of the action. -/
theorem expect_invariant (sys : System G) (μ : Measure G) [IsProbabilityMeasure μ]
    (sym : Symmetry sys) (β : ℝ) (O : sys.Config → ℝ) :
    sys.expect μ β (fun U => O (reindex sym.onLink U)) = sys.expect μ β O := by
  unfold System.expect
  rw [corrNum_invariant sys μ sym β O]

end Symmetry

#print axioms Symmetry.expect_invariant

end MassGap.LatticeGauge
