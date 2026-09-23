import Mathlib

/-!
# MassGap.LatticeGauge — invariance of Gibbs expectations under a lattice symmetry

A finite lattice gauge system over an abstract measurable gauge group, and a derivation that its
Gibbs expectations are unchanged when an observable is composed with a symmetry that permutes links
and plaquettes compatibly.

`System G` carries a finite link type, a finite plaquette type, a holonomy
`hol : Plaq → (Link → G) → G` and a plaquette density `φ : G → ℝ`. Built on those: `action` sums
`φ ∘ hol` over the plaquettes, `boltz β` is `exp (-β * action)`, `vol μ` is the product measure with
`μ` on every link, `corrNum` and `partition` are the two integrals, and `expect` is their quotient.

`Symmetry sys` is a permutation of links and a permutation of plaquettes with the compatibility
field `compat : hol p (fun l => U (onLink l)) = hol (onPlaq p) U`. That field is a combinatorial
property of a particular lattice, and everything below is what it buys.

The chain. `reindex_measurePreserving` — a product measure with identical factors is preserved by
relabelling the index, via `MeasureTheory.measurePreserving_piCongrLeft`. `action_invariant` —
reindex the plaquette sum along `onPlaq`, using `compat`. `boltz_invariant`, `corrNum_invariant` (a
measure-preserving change of variables) and `expect_invariant` follow, the last giving
`expect (O ∘ reindex onLink) = expect O`. `expect_invariant_of_mp` states the same mechanism for any
measure-preserving equivalence of configuration space whose Boltzmann weight it leaves fixed.

Scope. `G` is a measurable space and nothing more: no group structure, topology, compactness or
invariance of `μ` is used, and `μ` is required to be a probability measure only where the reindexing
 lemma needs it. The holonomy is a parameter — the ordered product of link variables around a
plaquette is one instantiation of it, not an assumption made here. `partition` is untouched by every
invariance proof, and none of them requires it to be nonzero, so `expect` is a quotient that may
divide by zero without affecting the equalities.

Foundational footprint only (`#print axioms` at the end).
-/

namespace MassGap.LatticeGauge

open MeasureTheory

/-- A finite lattice gauge system over a measurable gauge group `G`: a finite link type, a finite
plaquette type, a holonomy `hol` reading each plaquette's group element off a configuration, and a
plaquette action density `φ : G → ℝ`.

`hol` is a field, so any map at all may be supplied; the results below need only the compatibility
recorded in `Symmetry`. The ordered product of link variables around a plaquette is one choice of
`hol`. `φ` is an arbitrary real-valued function on `G` — being a class function is not imposed. -/
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

/-- For a measurable equivalence `T` of configuration space that preserves `vol μ` and leaves the
Boltzmann weight fixed, `expect (fun U => O (T U)) = expect O`.

The proof rewrites the numerator's integrand by `hw`, then applies `hT.integral_comp'`. The
denominator is not touched, so no integrability, positivity or nonvanishing of `partition` is
needed, and the observable `O` is an arbitrary real-valued function.

This is the mechanism `corrNum_invariant` and `expect_invariant` specialise to `T = reindex onLink`;
a gauge transformation acting on configurations would be another instance. -/
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

/-- A permutation `onLink` of the links, a permutation `onPlaq` of the plaquettes, and the field
`compat` tying them to the holonomy: relabelling a configuration's links by `onLink` sends the
holonomy at `p` to the holonomy at `onPlaq p`.

`compat` is a finite combinatorial condition on a given system; it is a field, not a consequence, so
the structure is inhabited exactly when such a pair of permutations exists. Both permutations are
arbitrary otherwise — no order, orientation or fixed-point condition is imposed. -/
structure Symmetry (sys : System G) where
  onLink : Equiv.Perm sys.Link
  onPlaq : Equiv.Perm sys.Plaq
  compat : ∀ (p : sys.Plaq) (U : sys.Config),
    sys.hol p (fun l => U (onLink l)) = sys.hol (onPlaq p) U

namespace Symmetry

variable {sys : System G}

/-- The measurable equivalence of configurations induced by a link permutation `e`, acting by
`reindex e U l = U (e l)`.

Built as the inverse of `MeasurableEquiv.piCongrLeft`. Because the fibres are constant — every link
carries the same `G` — its symmetric direction reduces without a dependent cast, which is what makes
`reindex_apply` hold by `rfl`. -/
noncomputable def reindex (e : Equiv.Perm sys.Link) : sys.Config ≃ᵐ sys.Config :=
  (MeasurableEquiv.piCongrLeft (fun _ : sys.Link => G) e).symm

@[simp] theorem reindex_apply (e : Equiv.Perm sys.Link) (U : sys.Config) (l : sys.Link) :
    reindex e U l = U (e l) := rfl

/-- `reindex e` preserves `vol μ` in both directions, for any link permutation `e` and any
probability measure `μ` on `G`.

From `MeasureTheory.measurePreserving_piCongrLeft` together with closure of measure preservation
under `symm`. The factors of the product are identical, which is why no invariance property of `μ`
itself is required; `IsProbabilityMeasure μ` is, because the product-measure lemma needs it. -/
theorem reindex_measurePreserving (μ : Measure G) [IsProbabilityMeasure μ]
    (e : Equiv.Perm sys.Link) :
    MeasurePreserving (reindex (sys := sys) e) (sys.vol μ) (sys.vol μ) := by
  have h : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : sys.Link => G) e)
      (sys.vol μ) (sys.vol μ) := by
    have hmp := measurePreserving_piCongrLeft (μ := fun _ : sys.Link => μ) e
    simpa [System.vol] using hmp
  exact MeasurePreserving.symm (MeasurableEquiv.piCongrLeft (fun _ : sys.Link => G) e) h

/-- `action (reindex sym.onLink U) = action U` for every configuration `U`.

Rewriting each summand by `sym.compat` turns the sum over plaquettes into the sum of the same terms
at `sym.onPlaq p`, and `Equiv.sum_comp` removes that permutation. No property of `φ` is used. -/
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

/-- `boltz β (reindex sym.onLink U) = boltz β U`, at every coupling `β` and configuration `U`.
Immediate from `action_invariant`, since `boltz` depends on `U` only through `action`. -/
theorem boltz_invariant (sym : Symmetry sys) (β : ℝ) (U : sys.Config) :
    sys.boltz β (reindex sym.onLink U) = sys.boltz β U := by
  unfold System.boltz; rw [action_invariant]

/-- `corrNum μ β (fun U => O (reindex sym.onLink U)) = corrNum μ β O`, for every observable `O`.

The integrand is rewritten by `boltz_invariant` so that the symmetry acts on both factors, then
`reindex_measurePreserving` supplies the change of variables. `O` is arbitrary and no integrability
hypothesis is imposed — Mathlib's integral is zero on non-integrable functions, and the rewriting
is pointwise. -/
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

/-- `expect μ β (fun U => O (reindex sym.onLink U)) = expect μ β O`.

`corrNum_invariant` rewrites the numerator; the denominator `partition μ β` does not depend on the
observable, so it is untouched and is not required to be nonzero. The equality therefore holds for
every system, symmetry, coupling and observable, resting only on `sym.compat` and on `μ` being a
probability measure. -/
theorem expect_invariant (sys : System G) (μ : Measure G) [IsProbabilityMeasure μ]
    (sym : Symmetry sys) (β : ℝ) (O : sys.Config → ℝ) :
    sys.expect μ β (fun U => O (reindex sym.onLink U)) = sys.expect μ β O := by
  unfold System.expect
  rw [corrNum_invariant sys μ sym β O]

end Symmetry

#print axioms Symmetry.expect_invariant

end MassGap.LatticeGauge
