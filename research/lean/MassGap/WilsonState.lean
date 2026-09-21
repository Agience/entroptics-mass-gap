import Mathlib
import MassGap.WilsonDLR
import MassGap.WilsonTransferReduction
import MassGap.HalfSpaceAlgebra

/-!
# MassGap.WilsonState — the infinite-volume Wilson measure, as a `State`

## The gap this fills

`WilsonDLR.exists_wilson_infinite_volume_gibbs_measure` produces a probability MEASURE `P` on
`IConf (SU N)` satisfying the DLR equation for the Wilson specification.
`WilsonTransferReduction.transferData_of_state_facts` consumes a `DLRLimit.State`. **The tree carried
only the other direction** — `DLRLimit.gibbsMeasure` takes a state to a measure — so the Wilson object
and the transfer machinery could not meet.

`stateOfMeasure` is the missing direction, and it is integration: `ν f = ∫ f dP`. On a compact
configuration space a continuous observable is bounded, and a probability measure is finite, so it is
integrable; the four `State` fields are then `integral_add`, `integral_smul`, `integral_nonneg` and
`measure_univ`.

## What this closes, and what it emphatically does not

**Closes:** the Wilson infinite-volume object is now a `State`, so
`transferData_of_state_facts` can be applied to it. The chain

    Wilson measure → State → TransferData → GNSHilbert.opT → OpTBridge.reconstruct_from_opT

has no missing link of type.

**Does not close:** `transferData_of_state_facts` still needs its three hypotheses, and
`wilsonStateAt` is not shown to satisfy ANY of them:

    IsReflectionInvariant (latticeReflection τ c) ν
    ReflPositiveOn (latticeReflection τ c) (halfSpaceAlg τ c) ν
    ∀ f, ν (ishiftObsL τ f) = ν f

and `reconstruct_from_opT` still needs the two spectral hypotheses, which are the mass gap.

**So this is the last piece of plumbing, not a step toward the gap.** Every remaining obligation is
now a statement about what the Wilson state DOES, none about what object it IS.

## ⚠ The limit is subsequential

`exists_wilson_infinite_volume_gibbs_measure` extracts along an ultrafilter refining `atTop`. Nothing
shows the net converges, nor that the result is independent of the frozen boundary. `wilsonStateAt`
inherits that: it is *a* state satisfying the DLR equation, not *the* infinite-volume state.
-/

namespace MassGap.WilsonState

open MeasureTheory MassGap.DLRLimit

/-! ## 1. A probability measure is a state -/

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A continuous observable on a compact space is integrable against a finite measure: it is
bounded by its own supremum norm, and the constant is integrable.

DERIVED: no numeral. -/
theorem integrable_of_continuousMap (P : Measure X) [IsFiniteMeasure P] (f : C(X, ℝ)) :
    Integrable (fun x => f x) P :=
  (integrable_const ‖f‖).mono' f.continuous.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm x))

#print axioms integrable_of_continuousMap

/-- **⭐ A PROBABILITY MEASURE IS A `State`.** `ν f = ∫ f dP`.

The four fields are `integral_add` (on the integrability above), `integral_smul`, `integral_nonneg`
and `measure_univ`. This is `DLRLimit.gibbsMeasure`'s missing converse.

DERIVED: the `1` is the total mass of a probability measure; `0` is the sign in positivity. -/
noncomputable def stateOfMeasure (P : Measure X) [IsProbabilityMeasure P] : State X where
  toFun f := ∫ x, f x ∂P
  map_add' f g := by
    show (∫ x, (f x + g x) ∂P) = _
    exact integral_add (integrable_of_continuousMap P f) (integrable_of_continuousMap P g)
  map_smul' c f := by
    show (∫ x, (c * f x) ∂P) = _
    exact integral_const_mul c (fun x => f x)
  nonneg' f hf := integral_nonneg hf
  one' := by
    show (∫ _x, (1 : ℝ) ∂P) = 1
    simp

@[simp] theorem stateOfMeasure_apply (P : Measure X) [IsProbabilityMeasure P] (f : C(X, ℝ)) :
    stateOfMeasure P f = ∫ x, f x ∂P := rfl

#print axioms stateOfMeasure

/-! ## 2. ⭐ The Wilson infinite-volume state -/

section Wilson

open MassGap.GibbsSpec

/-- **⭐ THE INFINITE-VOLUME WILSON STATE EXISTS**, at every real coupling.

`WilsonDLR.exists_wilson_infinite_volume_gibbs_measure` supplies the measure and `stateOfMeasure`
turns it into the object `WilsonTransferReduction.transferData_of_state_facts` consumes. The DLR
equation is carried through unchanged.

**⚠ It is not shown to be reflection-positive, reflection-invariant or translation-invariant**, and
those three are exactly what the transfer construction still needs. What this theorem removes is a
mismatch of TYPES, not any of those obligations.

DERIVED: no numeral. `N` and `β` are the caller's. -/
theorem exists_wilson_infinite_volume_state (N : ℕ) (hN : N ≠ 0) (β : ℝ) :
    ∃ ν : State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)),
      ∃ P : Measure (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)), ∃ _ : IsProbabilityMeasure P,
        ν = stateOfMeasure P ∧
        ∀ (Λ : Finset MassGap.GibbsSpec.ILink) (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)),
          (∫ U, MassGap.GibbsSpec.spec (MassGap.WilsonAction.wilsonDensity (N := N)) β Λ
              (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) (⇑f) U ∂P)
            = ∫ U, f U ∂P := by
  obtain ⟨P, hPprob, hdlr⟩ :=
    MassGap.WilsonDLR.exists_wilson_infinite_volume_gibbs_measure N hN β
  exact ⟨stateOfMeasure P, P, hPprob, rfl, hdlr⟩

#print axioms exists_wilson_infinite_volume_state

end Wilson


/-! ## 3. ⭐ The chain, across the two lattice skeletons -/

/-- **⭐ THE WILSON STATE FEEDS THE TRANSFER CONSTRUCTION.**

`WilsonDLR` is written against `GibbsSpec`'s copy of the lattice skeleton and
`WilsonTransferReduction` against `InfiniteLattice`'s. Both are `abbrev IConf (G) := ILink → G` over
the same `ISite`, so they are definitionally equal — **and this theorem is what checks that**, rather
than asserting it. Three modules in this tree each rebuild the skeleton independently; that the
chain crosses them is a fact about `abbrev` reducibility and is worth having machine-checked.

Given the three state facts, the Wilson infinite-volume state yields a full `Transfer.TransferData`
on the half-space algebra.

**⚠ The three facts are hypotheses and are supplied nowhere.** This composes types, not content.

DERIVED: `4` is the spacetime dimension; no other numeral. -/
noncomputable def wilsonTransferData {N : ℕ} (τ : Fin 4) (c : ℤ)
    (P : MeasureTheory.Measure (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    [MeasureTheory.IsProbabilityMeasure P]
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * c)) (stateOfMeasure P))
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * c))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg τ c) (stateOfMeasure P))
    (hnu : ∀ f, (stateOfMeasure P) (MassGap.ReflectionShift.ishiftObsL τ f) = (stateOfMeasure P) f) :
    MassGap.Transfer.TransferData ↥(MassGap.HalfSpaceAlgebra.halfSpaceAlg
      (G := MassGap.SUN.SU N) τ c) :=
  MassGap.WilsonTransferReduction.transferData_of_state_facts τ c (stateOfMeasure P) hinv hpos hnu

#print axioms wilsonTransferData

end MassGap.WilsonState
