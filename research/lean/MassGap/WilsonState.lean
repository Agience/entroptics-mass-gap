import Mathlib
import MassGap.WilsonDLR
import MassGap.WilsonTransferReduction
import MassGap.HalfSpaceAlgebra
import MassGap.ReflectionHalfSpace

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
`wilsonStateAt` is not shown to satisfy ANY of them.

⛔ A DIFFERENT state does satisfy two of them: the limit state of
`ReflectionHalfSpace.wilson_reflPositive_limit_exists` carries `ReflPositiveOn`, and
`reflection_facts_on_halfSpaceAlg` carries `IsReflectionInvariant` beside it. That state is a limit
of free-boundary states along an ultrafilter, not `wilsonStateAt`, so it does not discharge anything
here — but it means the list below is outstanding for THIS state, not for every state.

    IsReflectionInvariant (latticeReflection τ (2 * p)) ν
    ReflPositiveOn (latticeReflection τ (2 * p)) (halfSpaceAlg τ p) ν
    ∀ f, ν (ishiftObsL τ f) = ν f

⛔ The constant is `2 * p` where the algebra's plane is `p`, and not `c` with `c`:
`ReflectionHalfSpace`'s header shows that at `c ≠ 2p` the two half-spaces are not mirror images about
a common plane, so the `c`-with-`c` form asks for positivity of a pairing that is not the reflection
pairing.

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

/-! ## ⭐ The subtracted pairing vanishes at zero coupling

`WilsonTransferReduction.gapAt_iff_subtracted_pairing` reads `GapAt D r` as an inequality between two pairings,
the left one reflected about `2p-2` and the right about `2p`. At coupling ZERO the left one is
exactly zero for every half-space observable, because the reflection carries its support two full
steps clear of itself and the state factorises across the gap.

**Reflection invariance is not used.** The factorisation gives `ν(θG) · ν(G)`, and it is `ν(G)` that
vanishes — `G` is the observable with its own mean subtracted. Which of the two factors is the mean
matters, and it is the unreflected one. -/

/-- **⭐⭐ AT ZERO COUPLING THE SUBTRACTED PAIRING IS EXACTLY ZERO.**

This is the numerator of the gap inequality, at this coupling, for every observable of the
half-space algebra. Together with nonnegativity of the denominator it is `GapAt D 0`: at zero
coupling there is no dynamics, so the gap is not merely positive but infinite.

DERIVED: the `0` is the coupling; the `2` in `hφ2` is the proved upper end of the plaquette
density's range, as at `specCM`; `2 * p - 2` is the reflection constant
`gapAt_iff_subtracted_pairing` puts on the left of the gap inequality; the `1` is the unit
observable, carrying the mean that is subtracted; `4` is the dimension. -/
theorem refl_pairing_at_zero_eq_zero {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] {φ : G → ℝ}
    (hφc : Continuous φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (μ : Measure G) [IsProbabilityMeasure μ]
    {ν : MassGap.DLRLimit.State (MassGap.InfiniteLattice.IConf G)}
    (hν : MassGap.DLRLimit.IsDLR (MassGap.WilsonDLR.specCM hφc hφ0 hφ2 0 μ) ν)
    (τ : Fin 4) (p : ℤ) {F : C(MassGap.InfiniteLattice.IConf G, ℝ)}
    (hF : F ∈ MassGap.HalfSpaceAlgebra.halfSpaceAlg τ p) :
    ν (MassGap.LatticeReflection.ireflObs τ (2 * p - 2) (F - (ν F) • 1) * (F - (ν F) • 1)) = 0 := by
  classical
  obtain ⟨S, hSsub, hFloc⟩ := hF
  set c : ℝ := ν F with hc
  set Gsub : C(MassGap.InfiniteLattice.IConf G, ℝ) := F - c • 1 with hGsub
  -- the subtracted observable is local on the same support
  have hGloc : MassGap.InfiniteLattice.IsLocalOn S (⇑Gsub) := by
    intro U V h
    show F U - c * 1 = F V - c * 1
    rw [hFloc U V h]
  -- its reflection is local on the reflected support, which misses S
  have hRloc := MassGap.HalfSpaceAlgebra.isLocalOn_ireflObs τ (2 * p - 2) hGloc
  have hdisj := MassGap.HalfSpaceAlgebra.disjoint_image_ireflLink_posHalf τ p hSsub
  -- the mean of the subtracted observable is zero
  have hmean : ν Gsub = 0 := by
    have hsub := ν.map_sub F (c • 1)
    rw [← hGsub] at hsub
    rw [hsub, ν.map_smul, ν.map_one, mul_one, hc, sub_self]
  rw [MassGap.WilsonDLR.dlr_mul_at_zero hφc hφ0 hφ2 μ hν hdisj hRloc hGloc, hmean, mul_zero]

#print axioms refl_pairing_at_zero_eq_zero

/-- **⭐⭐⭐ AT ZERO COUPLING THE WILSON TRANSFER OPERATOR HAS `GapAt D 0`.**

`gapAt_iff_subtracted_pairing` at `r = 0` asks for `ν(θ_{2p-2} G · G) ≤ 0` with `G` the
mean-subtracted observable, and `refl_pairing_at_zero_eq_zero` computes that pairing to be exactly
`0`. So the gap condition holds at `r = 0`: no dynamics, and therefore not merely a positive gap but
an infinite one.

**THE `TransferData` IS THE GENUINE ONE**, `transferData_of_state_facts` at the Wilson
specification's own DLR state — not `TransferGap.diagTransfer`, which witnesses only that `GapAt`
is satisfiable by something.

**⚠ WHAT THIS STILL TAKES.** `hinv`, `hpos` and `hnu` are hypotheses here, exactly as in
`wilsonTransferData`, because `transferData_of_state_facts` cannot build `D` without them. So the
statement of obligation I at this coupling is sharp: **there is no analysis left between here and
the gap, only those three facts.** `hpos` is the hard one — it is reflection positivity at `2p`,
where the two supports MEET on the reflection plane, so the factorisation that proves the `2p-2`
pairing does not reach it.

DERIVED: the `0` in `specCM … 0 μ` is the coupling and the `0` in `GapAt … 0` is the gap ratio,
which is forced rather than chosen — the pairing it is compared against is zero. The `2` in `hφ2` is
the proved upper end of the plaquette density's range, as at `specCM`; `2 * p` is the reflection
constant of the half-space at `p`; `4` is the dimension. -/
theorem gapAt_zero_at_zero_coupling {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] {φ : G → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (μ : Measure G) [IsProbabilityMeasure μ]
    {ν : MassGap.DLRLimit.State (MassGap.InfiniteLattice.IConf G)}
    (hν : MassGap.DLRLimit.IsDLR (MassGap.WilsonDLR.specCM hφc hφ0 hφ2 0 μ) ν)
    (τ : Fin 4) (p : ℤ)
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg τ p) ν)
    (hnu : ∀ f, ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f) :
    MassGap.TransferGap.GapAt
      (MassGap.WilsonTransferReduction.transferData_of_state_facts τ p ν hinv hpos hnu) 0 := by
  rw [MassGap.WilsonTransferReduction.gapAt_iff_subtracted_pairing τ p ν hinv hpos hnu 0]
  intro F hF
  rw [refl_pairing_at_zero_eq_zero hφc hφ0 hφ2 μ hν τ p hF]
  simp

#print axioms gapAt_zero_at_zero_coupling


/-! ## ⭐ `hnu`, discharged at zero coupling

The shift is a bijection of the links, and `WilsonDLR.dlr_permCM_at_zero` says the zero-coupling
state is invariant under every one of those. So the third of
`transferData_of_state_facts`'s state facts is a theorem at this coupling rather than a hypothesis.

**The two `iunshift`s.** `GibbsSpec.iunshift` and `ReflectionShift.iunshift` are identical bodies in
isolated namespaces — `ReflectionHalfSpace.gibbs_iunshift_eq` proves them `rfl`-equal, and a lemma
about one is inert on the other. The two inverse laws below come from the two namespaces
deliberately. -/

/-- **THE SHIFT, AS A BIJECTION OF THE LINKS.** `ishiftLink` forward, `iunshiftLink` back.

DERIVED: `4` is the spacetime dimension. -/
def shiftLinkEquiv (τ : Fin 4) :
    MassGap.InfiniteLattice.ILink ≃ MassGap.InfiniteLattice.ILink where
  toFun := MassGap.InfiniteShift.ishiftLink τ
  invFun := MassGap.ReflectionShift.iunshiftLink τ
  left_inv l := by
    obtain ⟨m, x⟩ := l
    have h : MassGap.ReflectionShift.iunshift τ (MassGap.InfiniteLattice.ishift τ x) = x :=
      MassGap.GibbsSpec.iunshift_ishift τ x
    simp [MassGap.InfiniteShift.ishiftLink, MassGap.ReflectionShift.iunshiftLink, h]
  right_inv l := MassGap.ReflectionShift.ishiftLink_iunshiftLink τ l

#print axioms shiftLinkEquiv

/-- **⭐⭐ `hnu` AT ZERO COUPLING.** The DLR state is unmoved by the time shift, because it is
unmoved by every relabelling of the links.

DERIVED: the `0` is the coupling; the `2` is the proved upper end of the plaquette density's range,
as at `specCM`; `4` is the dimension. -/
theorem hnu_at_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (μ : Measure G) [IsProbabilityMeasure μ]
    {ν : MassGap.DLRLimit.State (MassGap.InfiniteLattice.IConf G)}
    (hν : MassGap.DLRLimit.IsDLR (MassGap.WilsonDLR.specCM hφc hφ0 hφ2 0 μ) ν) (τ : Fin 4) :
    ∀ f : C(MassGap.InfiniteLattice.IConf G, ℝ),
      ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f := by
  intro f
  have hcm : MassGap.ReflectionShift.ishiftObsL τ f
      = MassGap.WilsonDLR.permCM (shiftLinkEquiv τ) f := by
    ext U
    rfl
  rw [hcm]
  exact MassGap.WilsonDLR.dlr_permCM_at_zero hφc hφ0 hφ2 μ (shiftLinkEquiv τ) hν f

#print axioms hnu_at_zero

/-! ## ⭐ `hinv`, discharged at zero coupling

`ireflConf` relabels the links and INVERTS the group element on the `τ`-links. The relabelling is
`ReflectionHalfSpace.ireflPerm`, which already packages `ireflLink_involutive` as a permutation; the
inversion is a coordinatewise measure-preserving map as soon as the single-link measure is
inversion-invariant. So `WilsonDLR.dlr_twistCM_at_zero` applies, and the second of
`transferData_of_state_facts`'s state facts is a theorem at this coupling.

`Reflect.isInvInvariant_probHaar` is an instance, so at the Wilson measure the hypothesis
`[μ.IsInvInvariant]` discharges itself. -/

/-- **THE REFLECTION'S COORDINATE MAPS**: inversion on the `τ`-links, the identity elsewhere.

DERIVED: `4` is the spacetime dimension. -/
def ireflSigma {G : Type} [Group G] [MeasurableSpace G] [MeasurableInv G] (τ : Fin 4)
    (l : MassGap.InfiniteLattice.ILink) : G ≃ᵐ G :=
  if l.1 = τ then MeasurableEquiv.inv G else MeasurableEquiv.refl G

#print axioms ireflSigma

/-- **THE LATTICE REFLECTION IS A TWISTED RELABELLING.** Case split on the direction; each branch is
`ireflConf`'s own.

DERIVED: `4` is the spacetime dimension. -/
theorem ireflConf_eq_twistConf {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [MeasurableInv G] (τ : Fin 4) (c : ℤ)
    (U : MassGap.InfiniteLattice.IConf G) :
    MassGap.LatticeReflection.ireflConf τ c U
      = MassGap.WilsonDLR.twistConf (MassGap.ReflectionHalfSpace.ireflPerm τ c)
          (ireflSigma τ) U := by
  funext l
  by_cases h : l.1 = τ
  · simp [MassGap.LatticeReflection.ireflConf, MassGap.WilsonDLR.twistConf, ireflSigma, h]
  · simp [MassGap.LatticeReflection.ireflConf, MassGap.WilsonDLR.twistConf, ireflSigma, h]

#print axioms ireflConf_eq_twistConf

/-- **⭐⭐ `hinv` AT ZERO COUPLING.** The DLR state does not see the lattice reflection.

DERIVED: the `0` is the coupling; the `2` is the proved upper end of the plaquette density's range,
as at `specCM`; `4` is the dimension. -/
theorem hinv_at_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsInvInvariant]
    {ν : MassGap.DLRLimit.State (MassGap.InfiniteLattice.IConf G)}
    (hν : MassGap.DLRLimit.IsDLR (MassGap.WilsonDLR.specCM hφc hφ0 hφ2 0 μ) ν) (τ : Fin 4)
    (c : ℤ) :
    MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ c) ν := by
  have hσc : ∀ l, Continuous (ireflSigma (G := G) τ l) := by
    intro l
    by_cases h : l.1 = τ
    · simpa [ireflSigma, h] using (continuous_inv (G := G))
    · simp only [ireflSigma, if_neg h]
      exact continuous_id
  have hσ : ∀ l, MeasurePreserving (ireflSigma (G := G) τ l) μ μ := by
    intro l
    by_cases h : l.1 = τ
    · simpa [ireflSigma, h] using Measure.measurePreserving_inv μ
    · simp only [ireflSigma, if_neg h]
      exact MeasurePreserving.id μ
  intro f
  have hcm : MassGap.LatticeReflection.ireflObs τ c f
      = MassGap.WilsonDLR.twistCM (MassGap.ReflectionHalfSpace.ireflPerm τ c)
          (ireflSigma τ) hσc f := by
    ext U
    show f (MassGap.LatticeReflection.ireflConf τ c U)
      = f (MassGap.WilsonDLR.twistConf _ _ U)
    rw [ireflConf_eq_twistConf]
  show ν (MassGap.LatticeReflection.ireflObs τ c f) = ν f
  rw [hcm]
  exact MassGap.WilsonDLR.dlr_twistCM_at_zero hφc hφ0 hφ2 μ _ _ hσc hσ hν f

#print axioms hinv_at_zero

end MassGap.WilsonState
