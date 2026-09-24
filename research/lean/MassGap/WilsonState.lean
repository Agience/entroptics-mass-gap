import Mathlib
import MassGap.WilsonDLR
import MassGap.WilsonTransferReduction
import MassGap.HalfSpaceAlgebra
import MassGap.ReflectionHalfSpace

/-!
# MassGap.WilsonState — a probability measure as a `DLRLimit.State`, and what follows at zero coupling

## From measure to state

`stateOfMeasure P` is integration against `P`: `ν f = ∫ f dP`. On a compact configuration space a
continuous observable is bounded (`integrable_of_continuousMap`) and a probability measure is finite,
so the integral exists; the four `State` fields are then `integral_add`, `integral_const_mul`,
`integral_nonneg` and `measure_univ`. `DLRLimit.gibbsMeasure` goes the other way, from a state to a
measure.

`exists_wilson_infinite_volume_state` applies this to the measure
`WilsonDLR.exists_wilson_infinite_volume_gibbs_measure` produces, carrying the DLR equation through
unchanged. `wilsonTransferData` feeds such a state to
`WilsonTransferReduction.transferData_of_state_facts`, which additionally takes three facts about the
state as hypotheses:

    IsReflectionInvariant (latticeReflection τ (2 * c)) ν
    ReflPositiveOn (latticeReflection τ (2 * c)) (halfSpaceAlg τ c) ν
    ∀ f, ν (ishiftObsL τ f) = ν f

The reflection constant is `2 * c` where the half-space algebra's plane is `c`. At any other constant
the two half-spaces are not mirror images about a common plane, so the pairing that would be asked
about is not the reflection pairing.

`wilsonTransferData` also crosses two independently built copies of the lattice skeleton: `WilsonDLR`
is written against `GibbsSpec`'s and `WilsonTransferReduction` against `InfiniteLattice`'s. Both are
`abbrev IConf G := ILink → G` over the same `ISite`, so they are definitionally equal, and the
typechecking of that declaration is what records it.

## At zero coupling

Four results hold at the zero-coupling specification `WilsonDLR.specCM … 0 μ`:

* `refl_pairing_at_zero_eq_zero` — for every observable `F` of the half-space algebra, the pairing
  `ν (ireflObs τ (2 * p - 2) (F - ν F • 1) * (F - ν F • 1))` is exactly `0`. The reflection at
  `2 * p - 2` carries the support clear of itself, the state factorises across the gap
  (`WilsonDLR.dlr_mul_at_zero`), and the unreflected factor is the mean-subtracted observable, whose
  mean is zero. Reflection invariance is not used.
* `gapAt_zero_at_zero_coupling` — hence `GapAt D 0` for the `TransferData` built from that state, via
  `WilsonTransferReduction.gapAt_iff_subtracted_pairing` at `r = 0`.
* `hnu_at_zero` — the third state fact is a theorem here: the shift is a bijection of the links
  (`shiftLinkEquiv`) and `WilsonDLR.dlr_permCM_at_zero` makes the zero-coupling state invariant under
  every relabelling.
* `hinv_at_zero` — the first state fact is a theorem here: the lattice reflection is a twisted
  relabelling (`ireflConf_eq_twistConf`), and `WilsonDLR.dlr_twistCM_at_zero` applies once the
  single-link measure is inversion-invariant.

## Scope

`gapAt_zero_at_zero_coupling` takes `hinv`, `hpos` and `hnu` as hypotheses, because
`transferData_of_state_facts` needs them to build the data it is stated about; `hnu_at_zero` and
`hinv_at_zero` establish two of the three at this coupling but are not composed into it.
`ReflPositiveOn` at `2 * p` concerns supports that meet on the reflection plane, so the factorisation
behind `refl_pairing_at_zero_eq_zero` does not apply to it.

The infinite-volume measure is extracted along an ultrafilter refining `atTop`. Nothing here shows
the net converges or that the result is independent of the frozen boundary, so
`exists_wilson_infinite_volume_state` asserts the existence of a state satisfying the DLR equation,
not the uniqueness of one.

`GibbsSpec.iunshift` and `ReflectionShift.iunshift` are identical bodies in separate namespaces;
`ReflectionHalfSpace.gibbs_iunshift_eq` proves them equal by `rfl`, and a lemma about one does not
apply to the other. `shiftLinkEquiv`'s two inverse laws are taken one from each namespace.
-/

namespace MassGap.WilsonState

open MeasureTheory MassGap.DLRLimit

/-! ## 1. A probability measure is a state -/

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A continuous observable on a compact space is integrable against any finite measure.

The bound is the observable's own supremum norm, and a constant is integrable against a finite
measure. `X` is required to be a compact, second-countable Borel space by the section variables; `P`
need only be finite, not a probability measure.

DERIVED: the statement carries no numeral. -/
theorem integrable_of_continuousMap (P : Measure X) [IsFiniteMeasure P] (f : C(X, ℝ)) :
    Integrable (fun x => f x) P :=
  (integrable_const ‖f‖).mono' f.continuous.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm x))

#print axioms integrable_of_continuousMap

/-- A probability measure as a `DLRLimit.State`: `ν f = ∫ f dP` on continuous observables.

The four fields are `integral_add` (using `integrable_of_continuousMap`), `integral_const_mul`,
`integral_nonneg` and, for the unit, `measure_univ`. It runs in the other direction from
`DLRLimit.gibbsMeasure`, which takes a state to a measure.

Scope: `X` must be compact for the integrability, and `P` must be a probability measure for the unit
field.

DERIVED: the statement carries no numeral — the total mass and the positivity sign appear in the
fields, not in the type. -/
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

/-! ## 2. The Wilson infinite-volume state -/

section Wilson

open MassGap.GibbsSpec

/-- At every gauge order `N ≠ 0` and every real coupling `β`, there is a `DLRLimit.State` on
`IConf (SU N)` of the form `stateOfMeasure P` for a probability measure `P` that satisfies the DLR
equation for the Wilson specification at every finite link set `Λ` and every continuous observable.

`WilsonDLR.exists_wilson_infinite_volume_gibbs_measure` supplies `P` and its DLR property;
`stateOfMeasure` turns it into the type `WilsonTransferReduction.transferData_of_state_facts`
consumes.

Scope: the conclusion asserts existence, not uniqueness, and the measure is obtained as a limit along
an ultrafilter. Nothing in the statement says the state is reflection-positive,
reflection-invariant or translation-invariant.

DERIVED: `0` is the excluded gauge order in `hN : N ≠ 0`. It is the only numeral in the statement;
`N` and `β` are parameters. -/
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


/-! ## 3. The chain, across the two lattice skeletons -/

/-- A `Transfer.TransferData` on the half-space algebra `halfSpaceAlg τ c`, from a probability
measure `P` on `GibbsSpec.IConf (SU N)` together with three facts about `stateOfMeasure P`:
reflection invariance at `2 * c`, reflection positivity on the half-space algebra at the same
constant, and invariance under the shift `ishiftObsL τ`.

`WilsonTransferReduction.transferData_of_state_facts` applied to `stateOfMeasure P`. The declaration
also crosses two independently built copies of the lattice skeleton — `GibbsSpec`'s, which `P` is
stated over, and `InfiniteLattice`'s, which the reflection and shift are stated over. Both are
`abbrev IConf G := ILink → G` over the same site type, so they are definitionally equal and this
declaration typechecks.

Scope: `hinv`, `hpos` and `hnu` are hypotheses. Nothing here supplies them, and no property of `P`
beyond being a probability measure is used.

DERIVED: `4` is the spacetime dimension, the range of the direction index `τ : Fin 4`. `2` is the
factor in the reflection constant `2 * c`: the reflection that mirrors the half-space at plane `c`
onto its complement is the one about twice that plane. -/
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

/-! ## The subtracted pairing at zero coupling

`WilsonTransferReduction.gapAt_iff_subtracted_pairing` reads `GapAt D r` as an inequality between two
pairings, the left reflected about `2p - 2` and the right about `2p`. At zero coupling the left one
is exactly zero for every half-space observable: the reflection about `2p - 2` carries the support
two steps clear of itself and the state factorises across the gap.

Reflection invariance is not used. The factorisation gives `ν (θ G) * ν G`, and the factor that
vanishes is `ν G`, the mean of the mean-subtracted observable — the unreflected one. -/

/-- For a state `ν` satisfying the DLR equation of the zero-coupling specification, and any
observable `F` of the half-space algebra `halfSpaceAlg τ p`, the pairing
`ν (ireflObs τ (2 * p - 2) (F - ν F • 1) * (F - ν F • 1))` is exactly `0`.

The subtracted observable is local on the same support as `F`; its reflection about `2 * p - 2` is
local on the reflected support, which `disjoint_image_ireflLink_posHalf` shows is disjoint from it.
`WilsonDLR.dlr_mul_at_zero` then factorises the state across the gap into
`ν (reflected) * ν (subtracted)`, and the second factor is zero because the mean has been subtracted.

Scope: equality to `0`, at this coupling only, on this algebra. Reflection invariance of `ν` is not
a hypothesis and is not used. The reflection constant is `2 * p - 2`, not `2 * p`.

DERIVED: `0` is the coupling in `specCM … 0 μ`, the lower bound in `hφ0 : 0 ≤ φ g`, and the value of
the pairing. `2` is the upper end of the plaquette density's range in `hφ2 : φ g ≤ 2`, and the factor
and offset in the reflection constant `2 * p - 2`. `1` is the unit observable carrying the subtracted
mean. `4` is the spacetime dimension, the range of `τ : Fin 4`. -/
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

/-- **The two measures agree at zero coupling.** `stateFree` sums the action over `iplqAll Λ` — the
plaquettes with every link inside the box — and `GibbsSpec.spec` sums it over `boundaryPlaqs Λ`,
those with at least one link inside. `GibbsSpec.boundaryPlaqs_ne_plaqsIn` shows the two sets differ,
so the measures differ in general and nothing else in the tree relates them. At `β = 0` the action
drops out of both and each is the same Haar integral over the box.

Why this is the useful direction. `gapAt_of_finite_volume_connected` states its hypothesis with
`stateFree`, while the DLR machinery is stated with `spec` — including
`WilsonDLR.dlr_unique_at_zero`, the tree's only uniqueness result, and
`WilsonDLR.tendsto_specState_at_zero`, its only `atTop` limit. This identification is what lets those
speak about the free-boundary family, at the one coupling where they exist.

`ActionSplit.cvol ↑Λ μ` and `GibbsSpec.vol μ Λ` are both `Measure.pi (fun _ : ↑Λ => μ)`, and `cvol`
is a reducible abbreviation, so the two integrals are the same term.

DERIVED: the `0` is the coupling. The `2` is `stateFree`'s own bound on the class function `φ`,
transcribed from `ReflectionHalfSpace.stateFree`'s signature and consumed by nothing here. `Λ`, `ω`
and `f` are the caller's. -/
theorem stateFree_eq_spec_at_zero_coupling {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    MassGap.ReflectionHalfSpace.stateFree hφm hφ0 hφ2 0 Λ ω f
      = MassGap.GibbsSpec.spec φ 0 Λ (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) (⇑f) ω := by
  rw [MassGap.WilsonDLR.spec_at_zero φ Λ (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) (⇑f) ω]
  exact MassGap.ReflectionHalfSpace.specFree_at_zero_coupling (φ := φ) Λ ω _

#print axioms stateFree_eq_spec_at_zero_coupling

/-- `GapAt D 0` for the `TransferData` that `transferData_of_state_facts` builds from a
zero-coupling DLR state, given the three state facts `hinv`, `hpos` and `hnu`.

`WilsonTransferReduction.gapAt_iff_subtracted_pairing` at `r = 0` reduces the goal to
`ν (θ_{2p-2} G * G) ≤ 0` for the mean-subtracted `G`, and `refl_pairing_at_zero_eq_zero` evaluates
that pairing to `0`.

Scope. The data is the one `transferData_of_state_facts` produces at this state, not a constructed
witness such as `TransferGap.diagTransfer`. `hinv`, `hpos` and `hnu` are hypotheses, since the data
the conclusion is about cannot be formed without them; `hnu_at_zero` and `hinv_at_zero` below prove
two of them at this coupling but are not composed into this statement. `hpos` is reflection
positivity at `2 * p`, where the two supports meet on the reflection plane, so the disjoint-support
factorisation used above does not apply to it.

DERIVED: `0` is the coupling in `specCM … 0 μ`, the lower bound in `hφ0 : 0 ≤ φ g`, and the ratio in
`GapAt … 0`, which is forced by the pairing being zero. `2` is the upper end of the plaquette
density's range in `hφ2 : φ g ≤ 2`, and the factor in the reflection constant `2 * p`. `4` is the
spacetime dimension, the range of `τ : Fin 4`. -/
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


/-! ## `hnu` at zero coupling

The shift is a bijection of the links, and `WilsonDLR.dlr_permCM_at_zero` makes the zero-coupling
state invariant under every link relabelling, so the third of `transferData_of_state_facts`'s state
facts holds at this coupling.

`GibbsSpec.iunshift` and `ReflectionShift.iunshift` are identical bodies in separate namespaces;
`ReflectionHalfSpace.gibbs_iunshift_eq` proves them equal by `rfl`, and a lemma about one does not
apply to the other. The two inverse laws below are taken one from each namespace. -/

/-- The link shift as an `Equiv` of `InfiniteLattice.ILink`: `InfiniteShift.ishiftLink τ` forward,
`ReflectionShift.iunshiftLink τ` back.

The left inverse comes from `GibbsSpec.iunshift_ishift` and the right inverse from
`ReflectionShift.ishiftLink_iunshiftLink`, the two namespaces carrying separate copies of the same
map.

DERIVED: `4` is the spacetime dimension, the range of the direction index `τ : Fin 4`. It is the only
numeral in the statement. -/
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

/-- `ν (ishiftObsL τ f) = ν f` for every continuous observable `f`, when `ν` satisfies the DLR
equation of the zero-coupling specification.

`shiftLinkEquiv τ` presents the shift as a link permutation, and `WilsonDLR.dlr_permCM_at_zero` makes
the zero-coupling state invariant under every such permutation. This is the third of the state facts
`transferData_of_state_facts` takes.

Scope: at zero coupling only, and `G` additionally requires `T2Space` here.

DERIVED: `0` is the coupling in `specCM … 0 μ` and the lower bound in `hφ0 : 0 ≤ φ g`. `2` is the
upper end of the plaquette density's range in `hφ2 : φ g ≤ 2`. `4` is the spacetime dimension, the
range of `τ : Fin 4`. -/
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

/-! ## `hinv` at zero coupling

`ireflConf` relabels the links and inverts the group element on the `τ`-links. The relabelling is
`ReflectionHalfSpace.ireflPerm`, which packages `ireflLink_involutive` as a permutation; the
inversion is a coordinatewise measure-preserving map once the single-link measure is
inversion-invariant. `WilsonDLR.dlr_twistCM_at_zero` then applies, giving the first of
`transferData_of_state_facts`'s state facts at this coupling.

`Reflect.isInvInvariant_probHaar` is an instance, so at Haar measure the `[μ.IsInvInvariant]`
hypothesis is found by instance search. -/

/-- The reflection's coordinatewise maps: group inversion on the links in direction `τ`, the
identity on the rest. Each is a `MeasurableEquiv` of `G`.

DERIVED: `4` is the spacetime dimension, the range of the direction index `τ : Fin 4`. It is the only
numeral in the statement. -/
def ireflSigma {G : Type} [Group G] [MeasurableSpace G] [MeasurableInv G] (τ : Fin 4)
    (l : MassGap.InfiniteLattice.ILink) : G ≃ᵐ G :=
  if l.1 = τ then MeasurableEquiv.inv G else MeasurableEquiv.refl G

#print axioms ireflSigma

/-- `ireflConf τ c U = twistConf (ireflPerm τ c) (ireflSigma τ) U`: the lattice reflection is the
link relabelling `ireflPerm τ c` twisted by the coordinatewise maps `ireflSigma τ`.

Proved by case split on whether the link's direction is `τ`; each branch unfolds to `ireflConf`'s own
definition. The constant `c` is arbitrary.

DERIVED: `4` is the spacetime dimension, the range of the direction index `τ : Fin 4`. It is the only
numeral in the statement. -/
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

/-- `IsReflectionInvariant (latticeReflection τ c) ν` at every constant `c`, when `ν` satisfies the
DLR equation of the zero-coupling specification and the single-link measure is inversion-invariant.

`ireflConf_eq_twistConf` presents the reflection as a twisted relabelling, the coordinatewise maps
are continuous and measure-preserving (inversion on the `τ`-links, the identity elsewhere), and
`WilsonDLR.dlr_twistCM_at_zero` gives the invariance. This is the first of the state facts
`transferData_of_state_facts` takes.

Scope: at zero coupling only, at every `c` rather than only at the `2 * p` the transfer construction
uses, and with `[μ.IsInvInvariant]` and `T2Space G` required in addition to the surrounding
hypotheses.

DERIVED: `0` is the coupling in `specCM … 0 μ` and the lower bound in `hφ0 : 0 ≤ φ g`. `2` is the
upper end of the plaquette density's range in `hφ2 : φ g ≤ 2`. `4` is the spacetime dimension, the
range of `τ : Fin 4`. -/
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
