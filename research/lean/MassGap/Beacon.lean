import Mathlib
import MassGap.DLRLimit
import MassGap.PeriodicState
import MassGap.ContinuumSchwinger
import MassGap.ContinuumSep

noncomputable section

/-!
# MassGap.Beacon — a law is fixed by the signal a separating family of probes receives

## The picture

Plant a family of probes on the object and read, at every zoom level, the signal each probe
receives. If the probes separate points and are closed under products (a subalgebra of `C(X, ℝ)`),
two laws that deliver the same signal are the same law, and a family of laws whose signals settle
at every probe settles as a whole, to one limit, along the index filter itself. So every
perspective that receives the same signal is looking at the same object.

## Abstract layer (compact observer space `X`, states of `DLRLimit`)

* `SameSignalOn A ν₁ ν₂` and `state_eq_of_sameSignal`: agreement on a point-separating subalgebra
  gives equality of states (Stone–Weierstrass through `DLRLimit.State.eq_of_eqOn_subalgebra`).
* `BeaconConverges A l μ`: every probe response `μ i f`, `f ∈ A`, converges along `l`.
* `exists_unique_limit_of_beacon`: under `BeaconConverges` and separation, there is exactly one
  state `ν` with `μ i f → ν f` along `l` at every continuous `f` — along `l`, and not only along an
  ultrafilter. Existence runs `DLRLimit.exists_limit_state` at every ultrafilter below `l` and
  identifies all those limits through the probes; `Filter.tendsto_iff_ultrafilter` assembles them.
* `limits_eq_of_receiveSameSignal`: two families, on any index types and along any non-trivial
  filters, whose responses to every probe converge to the same number have the same limit state.
* `beacon_iff_tendsto`: under separation, `BeaconConverges` is equivalent to convergence of the
  states at every observable, so the hypothesis is exactly as strong as its conclusion.

## Measure layer

* `measureState μ`: the state `f ↦ ∫ f dμ` of a probability measure on a compact space.
* `measure_eq_of_integral_eqOn_subalgebra`: two probability measures on a compact pseudo-metrizable
  Borel space with equal integrals on a point-separating subalgebra of `C(X, ℝ)` are equal
  (`MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure`).
* `measure_eq_of_integral_eqOn_starSubalgebra_polish`: the Polish form, which is Mathlib's
  `MeasureTheory.ext_of_forall_mem_subalgebra_integral_eq_of_polish` at `𝕜 = ℝ`.
* `exists_unique_tendsto_probabilityMeasure_of_beacon`: on a compact metrizable space, probability
  measures whose integrals against every probe converge have exactly one weak limit
  (`MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`), built by
  Riesz–Markov–Kakutani (`DLRLimit.gibbsMeasure`) from the limit state.

## The tree

* Volume direction at fixed `β`: `VolumeBeacon hN β A` is `BeaconConverges` for the periodic Wilson
  states `PeriodicState.torusState hN (2k + 1) β` along `atTop`. Under it every ultrafilter limit of
  that family (`IsPeriodicLimit`) is `PeriodicState.periodicState hN β`
  (`eq_periodicState_of_volumeBeacon`), and the family converges to it along `atTop`
  (`tendsto_periodicState_atTop`): the choice `PeriodicState.periodicUltra` drops out.
* Coupling direction `β → ∞`: `ObserverBeacon hN π A` is `BeaconConverges` for the observer views
  `pushState (π k) (ContinuumSchwinger.stateK hN k)` at step `k`, through observer maps
  `π k : C(Cfg N, Y)` into a compact observer space; `observer_limit_unique` gives the one limit.
  `SchwingerBeacon hN ρ` is convergence along `atTop` of every renormalised lattice Schwinger
  function `ContinuumSchwinger.latSkR hN ρ k F` — the response to the physical probe `F`, whose test
  functions sit at fixed physical positions. `contSAlong σ ρ u F` is `ContinuumSchwinger.contS` with
  the per-step states `σ` and the ultrafilter `u` as parameters (`contS_eq_contSAlong`). Under
  `SchwingerBeacon` it does not depend on the ultrafilter `u ≤ atTop` at `σ = stateK hN`
  (`contSAlong_eq_contS_of_schwingerBeacon`); under
  `VolumeBeacon` at every step it does not depend on the per-step volume ultrafilters either
  (`contSAlong_eq_of_beacons`).
* Relative-entropy route: `NormTendsto l μ ν` (`|μ i f − ν f| ≤ ε ‖f‖` uniformly in `f`, eventually)
  implies convergence at every observable (`tendsto_of_normTendsto`), hence `BeaconConverges` for
  every probe family (`beacon_of_normTendsto`). For `μ i = measureState Pᵢ` and `ν = measureState P`,
  `|∫ f dPᵢ − ∫ f dP| ≤ 2 ‖f‖ · TV(Pᵢ, P)`, so total-variation convergence is `NormTendsto`, and
  Pinsker `TV ≤ √(KL / 2)` makes relative-entropy convergence sufficient. Mathlib at this pin has the
  relative entropy (`InformationTheory.klDiv`) and the total variation of a signed measure
  (`MeasureTheory.SignedMeasure.totalVariation`), and has neither Pinsker's inequality nor the bound
  of an integral by the total variation; so the chain from `klDiv` to `NormTendsto` is recorded here
  as a remark, and the formal statement starts at `NormTendsto`.

## The open inputs, stated

* `SchwingerBeacon hN ρ` — convergence of the probe responses of the Wilson measures along
  `β → ∞` (`β = dyBeta k`, `k → ∞`) at fixed physical probe placement; in state form the analogue
  is `ObserverBeacon hN π A`, for observer maps `π k` reading the lattice at a fixed physical
  resolution. Its quantifier runs over every family, coincident supports included; at a
  field-strength factor growing with the step such a family is expected to diverge
  (`ContinuumSchwinger.UniformBound`), so a non-degenerate limit is expected to meet only the form
  restricted to separated supports (`ContinuumSep.FamSep`).
* `VolumeBeacon hN β A` at each coupling `β = dyBeta k` — convergence of the periodic Wilson states
  along the extent, which makes each `stateK hN k` the unique periodic limit.

None of the three is proved here for any positive coupling; every uniqueness or
`atTop`-convergence theorem of the last section takes one of them, or its instance at one family, as
a hypothesis.
-/

namespace MassGap.Beacon

open MassGap MassGap.DLRLimit Filter
open scoped Topology BoundedContinuousFunction

/-! ## 1. Probes, signals, and uniqueness of the limit -/

section Abstract

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- `∀ f ∈ A, ν₁ f = ν₂ f`: the two states deliver the same response to every probe of `A`.

DERIVED: no numeral appears in the statement. -/
def SameSignalOn (A : Subalgebra ℝ C(X, ℝ)) (ν₁ ν₂ : State X) : Prop :=
  ∀ f ∈ A, ν₁ f = ν₂ f

#print axioms SameSignalOn

/-- **Same signal, same state.** Two states on `C(X, ℝ)`, `X` compact, that give the same response
to every probe of a point-separating subalgebra `A` are equal: `DLRLimit.State.eq_of_eqOn_subalgebra`
(Stone–Weierstrass, `ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints`) extends
the agreement to every continuous observable, and `DLRLimit.State.eq_of_apply_eq` turns it into
equality of states.

DERIVED: no numeral appears in the statement. -/
theorem state_eq_of_sameSignal (A : Subalgebra ℝ C(X, ℝ)) (hA : A.SeparatesPoints)
    {ν₁ ν₂ : State X} (h : SameSignalOn A ν₁ ν₂) : ν₁ = ν₂ :=
  State.eq_of_apply_eq (State.eq_of_eqOn_subalgebra A hA h)

#print axioms state_eq_of_sameSignal

/-- `∀ f ∈ A, ∃ a : ℝ, Tendsto (fun i => μ i f) l (𝓝 a)`: the response of the family `μ` to every
probe of `A` converges along `l`. The limiting number may depend on the probe; nothing about
observables outside `A` is asked.

DERIVED: no numeral appears in the statement. -/
def BeaconConverges {ι : Type*} (A : Subalgebra ℝ C(X, ℝ)) (l : Filter ι) (μ : ι → State X) :
    Prop :=
  ∀ f ∈ A, ∃ a : ℝ, Tendsto (fun i => μ i f) l (𝓝 a)

#print axioms BeaconConverges

/-- `∀ f ∈ A, ∃ a : ℝ, Tendsto (fun i => μ₁ i f) l₁ (𝓝 a) ∧ Tendsto (fun j => μ₂ j f) l₂ (𝓝 a)`:
the two families, read along their own filters, receive the same limiting signal at every probe of
`A`.

DERIVED: no numeral appears in the statement. -/
def ReceiveSameSignal {ι₁ ι₂ : Type*} (A : Subalgebra ℝ C(X, ℝ)) (l₁ : Filter ι₁)
    (μ₁ : ι₁ → State X) (l₂ : Filter ι₂) (μ₂ : ι₂ → State X) : Prop :=
  ∀ f ∈ A, ∃ a : ℝ, Tendsto (fun i => μ₁ i f) l₁ (𝓝 a) ∧ Tendsto (fun j => μ₂ j f) l₂ (𝓝 a)

#print axioms ReceiveSameSignal

/-- **Every perspective that receives the same signal sees the same state.** If `μ₁ i f → ν₁ f`
along `l₁` and `μ₂ j f → ν₂ f` along `l₂` at every continuous `f`, and the two families receive the
same limiting signal at every probe of a point-separating subalgebra `A`, then `ν₁ = ν₂`. At each
probe both limits equal the common signal by `tendsto_nhds_unique`, and `state_eq_of_sameSignal`
finishes.

The two index types and the two non-trivial filters are unrelated: the families may be two zoom
paths, two subsequences, or two ultrafilter refinements of one sequence.

DERIVED: no numeral appears in the statement. -/
theorem limits_eq_of_receiveSameSignal {ι₁ ι₂ : Type*} {l₁ : Filter ι₁} {l₂ : Filter ι₂}
    [l₁.NeBot] [l₂.NeBot] (A : Subalgebra ℝ C(X, ℝ)) (hA : A.SeparatesPoints)
    (μ₁ : ι₁ → State X) (μ₂ : ι₂ → State X) {ν₁ ν₂ : State X}
    (h₁ : ∀ f : C(X, ℝ), Tendsto (fun i => μ₁ i f) l₁ (𝓝 (ν₁ f)))
    (h₂ : ∀ f : C(X, ℝ), Tendsto (fun j => μ₂ j f) l₂ (𝓝 (ν₂ f)))
    (hsig : ReceiveSameSignal A l₁ μ₁ l₂ μ₂) : ν₁ = ν₂ := by
  refine state_eq_of_sameSignal A hA (fun f hf => ?_)
  obtain ⟨a, ha₁, ha₂⟩ := hsig f hf
  exact (tendsto_nhds_unique (h₁ f) ha₁).trans (tendsto_nhds_unique (h₂ f) ha₂).symm

#print axioms limits_eq_of_receiveSameSignal

/-- **Two refinements of one beacon family have one limit.** If `A` separates points and the family
`μ` satisfies `BeaconConverges A l μ`, then any two states that are limits of `μ` along non-trivial filters
`l₁ ≤ l` and `l₂ ≤ l` are equal. The probe responses along `l₁` and `l₂` inherit the limit along `l`
(`Filter.Tendsto.mono_left`), so the two refinements receive the same signal, and
`limits_eq_of_receiveSameSignal` applies.

DERIVED: no numeral appears in the statement. -/
theorem limits_eq_of_beacon {ι : Type*} {l l₁ l₂ : Filter ι} [l₁.NeBot] [l₂.NeBot]
    (A : Subalgebra ℝ C(X, ℝ)) (hA : A.SeparatesPoints) (μ : ι → State X)
    (hb : BeaconConverges A l μ) (hl₁ : l₁ ≤ l) (hl₂ : l₂ ≤ l) {ν₁ ν₂ : State X}
    (h₁ : ∀ f : C(X, ℝ), Tendsto (fun i => μ i f) l₁ (𝓝 (ν₁ f)))
    (h₂ : ∀ f : C(X, ℝ), Tendsto (fun i => μ i f) l₂ (𝓝 (ν₂ f))) : ν₁ = ν₂ := by
  refine limits_eq_of_receiveSameSignal A hA μ μ h₁ h₂ (fun f hf => ?_)
  obtain ⟨a, ha⟩ := hb f hf
  exact ⟨a, ha.mono_left hl₁, ha.mono_left hl₂⟩

#print axioms limits_eq_of_beacon

/-- **The beacon theorem: convergent probe responses give one limit state, along the filter
itself.** Let `X` be compact, `A ⊆ C(X, ℝ)` a point-separating subalgebra, `l` a non-trivial filter
on any index type, and `μ : ι → State X` a family whose response to every probe of `A` converges
along `l`. Then there is exactly one state `ν` with `μ i f → ν f` along `l` at every continuous `f`.

Existence: `DLRLimit.exists_limit_state` gives a state `ν` and an ultrafilter `u ≤ l` along which
`μ` converges to `ν`. For any ultrafilter `w ≤ l`, the same lemma at `w` returns an ultrafilter
below `w`, which is `w` (`Ultrafilter.unique`), and a limit `ν'` along `w`; `limits_eq_of_beacon`
makes `ν' = ν`. So `μ i f → ν f` along every ultrafilter below `l`, which is convergence along `l`
(`Filter.tendsto_iff_ultrafilter`). Uniqueness: a second limit along `l` is a limit along `u`, and
`tendsto_nhds_unique` identifies it with `ν` at every observable.

Compactness of `X` supplies what tightness supplies on a non-compact space: every state value
`μ i f` lies in `[-‖f‖, ‖f‖]` (`DLRLimit.State.mem_Icc`).

DERIVED: no numeral appears in the statement. -/
theorem exists_unique_limit_of_beacon {ι : Type*} {l : Filter ι} [l.NeBot]
    (A : Subalgebra ℝ C(X, ℝ)) (hA : A.SeparatesPoints) (μ : ι → State X)
    (hb : BeaconConverges A l μ) :
    ∃! ν : State X, ∀ f : C(X, ℝ), Tendsto (fun i => μ i f) l (𝓝 (ν f)) := by
  obtain ⟨u, ν, hle, htend⟩ := exists_limit_state l μ
  haveI : (u : Filter ι).NeBot := u.neBot'
  refine ⟨ν, fun f => ?_, fun ν' hν' => ?_⟩
  · rw [Filter.tendsto_iff_ultrafilter]
    intro w hw
    haveI : (w : Filter ι).NeBot := w.neBot'
    obtain ⟨w', ν', hle', htend'⟩ := exists_limit_state (X := X) (w : Filter ι) μ
    have hweq : (w' : Filter ι) = (w : Filter ι) := w.unique hle'
    have htendw : ∀ g : C(X, ℝ), Tendsto (fun i => μ i g) (w : Filter ι) (𝓝 (ν' g)) := by
      intro g
      have hg := htend' g
      rwa [hweq] at hg
    have hνν : ν' = ν := limits_eq_of_beacon A hA μ hb hw hle htendw htend
    rw [← hνν]
    exact htendw f
  · refine State.eq_of_apply_eq (fun f => ?_)
    exact tendsto_nhds_unique ((hν' f).mono_left hle) (htend f)

#print axioms exists_unique_limit_of_beacon

/-- **Beacon convergence is convergence.** Under separation, `BeaconConverges A l μ` holds exactly
when some state `ν` has `μ i f → ν f` along `l` at every continuous `f`. Forward:
`exists_unique_limit_of_beacon`. Backward: a probe is an observable, so its response converges to
`ν f`.

So the hypothesis `BeaconConverges` is no stronger than the convergence it yields; its content is
that it asks for convergence on the probes alone.

DERIVED: no numeral appears in the statement. -/
theorem beacon_iff_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    (A : Subalgebra ℝ C(X, ℝ)) (hA : A.SeparatesPoints) (μ : ι → State X) :
    BeaconConverges A l μ ↔
      ∃ ν : State X, ∀ f : C(X, ℝ), Tendsto (fun i => μ i f) l (𝓝 (ν f)) := by
  constructor
  · intro hb
    obtain ⟨ν, hν, -⟩ := exists_unique_limit_of_beacon A hA μ hb
    exact ⟨ν, hν⟩
  · rintro ⟨ν, hν⟩ f _
    exact ⟨ν f, hν f⟩

#print axioms beacon_iff_tendsto

/-- A constant family is a beacon family for every probe family: `BeaconConverges A l (fun _ => ν)`.
The witness that the predicate is satisfiable.

DERIVED: no numeral appears in the statement. -/
theorem beacon_const {ι : Type*} (A : Subalgebra ℝ C(X, ℝ)) (l : Filter ι) (ν : State X) :
    BeaconConverges A l (fun _ : ι => ν) :=
  fun f _ => ⟨ν f, tendsto_const_nhds⟩

#print axioms beacon_const

/-- `∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ f : C(X, ℝ), |μ i f - ν f| ≤ ε * ‖f‖`: the states converge in the
dual norm of `C(X, ℝ)`. For states of probability measures this is what total-variation convergence
gives, since `|∫ f dP - ∫ f dQ| ≤ 2 ‖f‖ · TV(P, Q)`.

DERIVED: `0` is the strict lower bound on `ε`. -/
def NormTendsto {ι : Type*} (l : Filter ι) (μ : ι → State X) (ν : State X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ f : C(X, ℝ), |μ i f - ν f| ≤ ε * ‖f‖

#print axioms NormTendsto

/-- **Norm convergence gives convergence at every observable.** Given `ε > 0` and `f`, the norm
bound at `ε / (‖f‖ + 1)` puts `μ i f` within `ε / (‖f‖ + 1) · ‖f‖ < ε` of `ν f` eventually
(`Metric.tendsto_nhds`).

DERIVED: `0` is the strict lower bound on `ε`; `1` is added to `‖f‖` in the proof so the divisor is
positive when `f = 0`. -/
theorem tendsto_of_normTendsto {ι : Type*} {l : Filter ι} {μ : ι → State X} {ν : State X}
    (h : NormTendsto l μ ν) : ∀ f : C(X, ℝ), Tendsto (fun i => μ i f) l (𝓝 (ν f)) := by
  intro f
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hpos : 0 < ‖f‖ + 1 := by positivity
  have hε' : 0 < ε / (‖f‖ + 1) := div_pos hε hpos
  filter_upwards [h _ hε'] with i hi
  rw [Real.dist_eq]
  have h1 := hi f
  have h2 : ε / (‖f‖ + 1) * ‖f‖ < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
    nlinarith [norm_nonneg f]
  linarith

#print axioms tendsto_of_normTendsto

/-- **Norm convergence is beacon convergence for every probe family.** `tendsto_of_normTendsto` at
each probe.

This is the implication from the relative-entropy formulation: relative-entropy convergence gives
total-variation convergence by Pinsker's inequality, total-variation convergence of probability
measures gives `NormTendsto` of their states, and this lemma gives `BeaconConverges`.

DERIVED: no numeral appears in the statement. -/
theorem beacon_of_normTendsto {ι : Type*} {l : Filter ι} {μ : ι → State X} {ν : State X}
    (A : Subalgebra ℝ C(X, ℝ)) (h : NormTendsto l μ ν) : BeaconConverges A l μ :=
  fun f _ => ⟨ν f, tendsto_of_normTendsto h f⟩

#print axioms beacon_of_normTendsto

end Abstract

/-! ## 2. The measure layer -/

section Measure

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]

/-- A continuous function on a compact space is integrable against a finite measure: it is the
bounded continuous function `BoundedContinuousFunction.mkOfCompact f`, and
`BoundedContinuousFunction.integrable` applies.

DERIVED: no numeral appears in the statement. -/
theorem integrable_of_compact [OpensMeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsFiniteMeasure μ] (f : C(X, ℝ)) : MeasureTheory.Integrable f μ :=
  (BoundedContinuousFunction.mkOfCompact f).integrable μ

#print axioms integrable_of_compact

/-- **The state of a probability measure**: `f ↦ ∫ x, f x ∂μ`. Additivity is
`MeasureTheory.integral_add` with `integrable_of_compact`, homogeneity
`MeasureTheory.integral_const_mul`, positivity `MeasureTheory.integral_nonneg`, and normalisation the
total mass one.

DERIVED: no numeral appears in the statement; the normalisation `1` is the total mass inside
`IsProbabilityMeasure`. -/
def measureState [OpensMeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] : State X where
  toFun f := ∫ x, f x ∂μ
  map_add' f g := by
    show ∫ x, (f x + g x) ∂μ = ∫ x, f x ∂μ + ∫ x, g x ∂μ
    exact MeasureTheory.integral_add (integrable_of_compact μ f) (integrable_of_compact μ g)
  map_smul' c f := by
    show ∫ x, c * f x ∂μ = c * ∫ x, f x ∂μ
    exact MeasureTheory.integral_const_mul c _
  nonneg' f hf := MeasureTheory.integral_nonneg (fun x => hf x)
  one' := by
    show ∫ _x, (1 : ℝ) ∂μ = 1
    simp

#print axioms measureState

/-- `measureState μ f = ∫ x, f x ∂μ`, by `rfl`.

DERIVED: no numeral appears in the statement. -/
theorem measureState_apply [OpensMeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (f : C(X, ℝ)) :
    measureState μ f = ∫ x, f x ∂μ := rfl

#print axioms measureState_apply

/-- **A probability measure is fixed by its integrals on a separating subalgebra** (compact form).
On a compact pseudo-metrizable Borel space, two probability measures whose integrals agree on a
point-separating subalgebra `A ⊆ C(X, ℝ)` are equal. `DLRLimit.State.eq_of_eqOn_subalgebra` on
their states `measureState μ`, `measureState ν` gives agreement at every continuous function, hence
at every bounded continuous function, and
`MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure` (through the `HasOuterApproxClosed`
instance of a pseudo-metrizable space) concludes.

DERIVED: no numeral appears in the statement. -/
theorem measure_eq_of_integral_eqOn_subalgebra [BorelSpace X]
    [TopologicalSpace.PseudoMetrizableSpace X] {μ ν : MeasureTheory.Measure X}
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν]
    (A : Subalgebra ℝ C(X, ℝ)) (hA : A.SeparatesPoints)
    (h : ∀ f ∈ A, ∫ x, f x ∂μ = ∫ x, f x ∂ν) : μ = ν := by
  have hall := State.eq_of_eqOn_subalgebra (ν₁ := measureState μ) (ν₂ := measureState ν) A hA
    (fun f hf => h f hf)
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact hall f.toContinuousMap

#print axioms measure_eq_of_integral_eqOn_subalgebra

/-- **The Polish form**, Mathlib's `MeasureTheory.ext_of_forall_mem_subalgebra_integral_eq_of_polish`
at `𝕜 = ℝ`: on a Polish Borel space, two finite measures whose integrals agree on a star subalgebra
`A` of bounded continuous functions that separates points (as a subalgebra of `C(E, ℝ)`) are equal.
No compactness enters; the separating family is required to consist of bounded functions.

DERIVED: no numeral appears in the statement. -/
theorem measure_eq_of_integral_eqOn_starSubalgebra_polish {E : Type*} [TopologicalSpace E]
    [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    {P P' : MeasureTheory.Measure E} [MeasureTheory.IsFiniteMeasure P]
    [MeasureTheory.IsFiniteMeasure P'] {A : StarSubalgebra ℝ (E →ᵇ ℝ)}
    (hA : (A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints)
    (heq : ∀ g ∈ A, ∫ x, (g : E → ℝ) x ∂P = ∫ x, (g : E → ℝ) x ∂P') : P = P' :=
  MeasureTheory.ext_of_forall_mem_subalgebra_integral_eq_of_polish hA heq

#print axioms measure_eq_of_integral_eqOn_starSubalgebra_polish

variable [T2Space X] [LocallyCompactSpace X] [BorelSpace X]

/-- The probability measure of a state: `DLRLimit.gibbsMeasure ν`, the Riesz–Markov–Kakutani
representative, packaged with `DLRLimit.instIsProbabilityMeasure`.

DERIVED: no numeral appears in the statement. -/
def probOfState (ν : State X) : MeasureTheory.ProbabilityMeasure X :=
  ⟨gibbsMeasure ν, inferInstance⟩

#print axioms probOfState

/-- `∫ x, f x ∂(probOfState ν) = ν f.toContinuousMap` at every bounded continuous `f`:
`DLRLimit.integral_gibbsMeasure` at the underlying continuous function.

DERIVED: no numeral appears in the statement. -/
theorem integral_probOfState (ν : State X) (f : X →ᵇ ℝ) :
    ∫ x, f x ∂(probOfState ν : MeasureTheory.Measure X) = ν f.toContinuousMap :=
  integral_gibbsMeasure ν f.toContinuousMap

#print axioms integral_probOfState

/-- **The beacon theorem for probability measures.** On a compact metrizable Borel space `X`, let
`A ⊆ C(X, ℝ)` be a point-separating subalgebra and `μs : ι → ProbabilityMeasure X` a family whose
integral against every probe of `A` converges along a non-trivial filter `l`. Then there is exactly
one probability measure `μ` with `μs → μ` along `l` in the topology of convergence in distribution.

The states `measureState (μs i)` satisfy `BeaconConverges`, so `exists_unique_limit_of_beacon` gives
a limit state `ν`; `probOfState ν` is its Riesz–Markov–Kakutani measure, and
`MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto` with `integral_probOfState`
turns convergence of the states into weak convergence. Uniqueness is `tendsto_nhds_unique` in the
Hausdorff space `ProbabilityMeasure X` (`MeasureTheory.ProbabilityMeasure.t2Space`).

Tightness needs no hypothesis: the space is compact.

DERIVED: no numeral appears in the statement. -/
theorem exists_unique_tendsto_probabilityMeasure_of_beacon
    [TopologicalSpace.PseudoMetrizableSpace X] {ι : Type*} {l : Filter ι} [l.NeBot]
    (A : Subalgebra ℝ C(X, ℝ)) (hA : A.SeparatesPoints)
    (μs : ι → MeasureTheory.ProbabilityMeasure X)
    (hb : ∀ f ∈ A, ∃ a : ℝ,
      Tendsto (fun i => ∫ x, f x ∂(μs i : MeasureTheory.Measure X)) l (𝓝 a)) :
    ∃! μ : MeasureTheory.ProbabilityMeasure X, Tendsto μs l (𝓝 μ) := by
  have hbσ : BeaconConverges A l (fun i => measureState (μs i : MeasureTheory.Measure X)) :=
    fun f hf => hb f hf
  obtain ⟨ν, hν, -⟩ := exists_unique_limit_of_beacon A hA _ hbσ
  have hμ : Tendsto μs l (𝓝 (probOfState ν)) := by
    rw [MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    rw [integral_probOfState]
    exact hν f.toContinuousMap
  exact ⟨probOfState ν, hμ, fun μ' hμ' => tendsto_nhds_unique hμ' hμ⟩

#print axioms exists_unique_tendsto_probabilityMeasure_of_beacon

end Measure

/-! ## 3. The tree: the periodic Wilson states and the continuum Schwinger functions -/

section Tree

variable {N : ℕ}

/-! ### Volume direction at a fixed coupling -/

/-- **The volume beacon at coupling `β`**: `BeaconConverges A atTop` for the periodic Wilson states
`PeriodicState.torusState hN (2k + 1) β`, the family `PeriodicState.periodicState` is a limit of.
Stated, not proved: it is the convergence of the periodic states along the extent, at the probes
of `A`.

DERIVED: `2 * k + 1` is `PeriodicState`'s extent index, the family `exists_periodic_limit` takes its
limit of; `0` is the excluded rank in `hN`. -/
def VolumeBeacon (hN : N ≠ 0) (β : ℝ)
    (A : Subalgebra ℝ C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) : Prop :=
  BeaconConverges A atTop (fun k : ℕ => PeriodicState.torusState hN (2 * k + 1) β)

#print axioms VolumeBeacon

/-- `∃ u : Ultrafilter ℕ, u ≤ atTop ∧ ∀ f, torusState hN (2k + 1) β f → ν f along u`: `ν` is a limit
of the periodic Wilson states along some ultrafilter finer than `atTop` — one of the states
`PeriodicState.exists_periodic_limit` could have returned.

DERIVED: `2 * k + 1` is `PeriodicState`'s extent index; `0` is the excluded rank in `hN`. -/
def IsPeriodicLimit (hN : N ≠ 0) (β : ℝ)
    (ν : State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))) : Prop :=
  ∃ u : Ultrafilter ℕ, (u : Filter ℕ) ≤ atTop ∧
    ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Tendsto (fun k : ℕ => PeriodicState.torusState hN (2 * k + 1) β f) (u : Filter ℕ)
        (𝓝 (ν f))

#print axioms IsPeriodicLimit

/-- `PeriodicState.periodicState hN β` is a periodic limit, along `PeriodicState.periodicUltra hN β`:
`PeriodicState.periodicUltra_le` and `PeriodicState.tendsto_periodicState`.

DERIVED: `0` is the excluded rank in `hN`. -/
theorem periodicState_isPeriodicLimit (hN : N ≠ 0) (β : ℝ) :
    IsPeriodicLimit hN β (PeriodicState.periodicState hN β) :=
  ⟨PeriodicState.periodicUltra hN β, PeriodicState.periodicUltra_le hN β,
    PeriodicState.tendsto_periodicState hN β⟩

#print axioms periodicState_isPeriodicLimit

/-- **Under the volume beacon, every periodic limit is `periodicState`.** If `VolumeBeacon hN β A`
holds for a point-separating `A`, every state that is a limit of the periodic Wilson states along an
ultrafilter finer than `atTop` equals `PeriodicState.periodicState hN β`: `limits_eq_of_beacon` with
`l = atTop`, `l₁` the given ultrafilter and `l₂ = periodicUltra hN β`. So `periodicState hN β` does
not depend on the ultrafilter `Classical.choose` selected.

DERIVED: `0` is the excluded rank in `hN`. -/
theorem eq_periodicState_of_volumeBeacon (hN : N ≠ 0) (β : ℝ)
    (A : Subalgebra ℝ C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hA : A.SeparatesPoints) (hv : VolumeBeacon hN β A)
    {ν : State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))} (hν : IsPeriodicLimit hN β ν) :
    ν = PeriodicState.periodicState hN β := by
  obtain ⟨u, hu, htu⟩ := hν
  haveI : (u : Filter ℕ).NeBot := u.neBot'
  haveI : ((PeriodicState.periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ).NeBot :=
    (PeriodicState.periodicUltra hN β).neBot'
  exact limits_eq_of_beacon (l := atTop) A hA
    (fun k : ℕ => PeriodicState.torusState hN (2 * k + 1) β) hv hu
    (PeriodicState.periodicUltra_le hN β) htu (PeriodicState.tendsto_periodicState hN β)

#print axioms eq_periodicState_of_volumeBeacon

/-- **Under the volume beacon, the periodic states converge to `periodicState` along `atTop`.**
`exists_unique_limit_of_beacon` gives an `atTop` limit `ν`; along `periodicUltra hN β ≤ atTop` it is
also the limit `periodicState hN β`, so the two agree at every observable by `tendsto_nhds_unique`.

DERIVED: `2 * k + 1` is `PeriodicState`'s extent index; `0` is the excluded rank in `hN`. -/
theorem tendsto_periodicState_atTop (hN : N ≠ 0) (β : ℝ)
    (A : Subalgebra ℝ C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hA : A.SeparatesPoints) (hv : VolumeBeacon hN β A) :
    ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Tendsto (fun k : ℕ => PeriodicState.torusState hN (2 * k + 1) β f) atTop
        (𝓝 (PeriodicState.periodicState hN β f)) := by
  obtain ⟨ν, hν, -⟩ := exists_unique_limit_of_beacon (l := atTop) A hA
    (fun k : ℕ => PeriodicState.torusState hN (2 * k + 1) β) hv
  haveI : ((PeriodicState.periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ).NeBot :=
    (PeriodicState.periodicUltra hN β).neBot'
  intro f
  have e : ν f = PeriodicState.periodicState hN β f :=
    tendsto_nhds_unique ((hν f).mono_left (PeriodicState.periodicUltra_le hN β))
      (PeriodicState.tendsto_periodicState hN β f)
  rw [← e]
  exact hν f

#print axioms tendsto_periodicState_atTop

/-- `(DLRLimit.localObsAlg (SU N)).SeparatesPoints`: the observables local on a finite link set
separate the configurations of `ℤ⁴`, `SU(N)` being compact Hausdorff
(`DLRLimit.localObsAlg_separatesPoints`, `DLRLimit.continuousMap_separatesPoints_of_t2`).

DERIVED: no numeral appears in the statement. -/
theorem localObs_separatesPoints (N : ℕ) :
    (localObsAlg (MassGap.SUN.SU N)).SeparatesPoints :=
  localObsAlg_separatesPoints (G := MassGap.SUN.SU N)
    (fun a b hab => continuousMap_separatesPoints_of_t2 _ a b hab)

#print axioms localObs_separatesPoints

/-- `eq_periodicState_of_volumeBeacon` at the local observables: if the response of the periodic
Wilson states to every local observable converges along the extent, every periodic limit is
`periodicState hN β`.

DERIVED: `0` is the excluded rank in `hN`. -/
theorem eq_periodicState_of_localBeacon (hN : N ≠ 0) (β : ℝ)
    (hv : VolumeBeacon hN β (localObsAlg (MassGap.SUN.SU N)))
    {ν : State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))} (hν : IsPeriodicLimit hN β ν) :
    ν = PeriodicState.periodicState hN β :=
  eq_periodicState_of_volumeBeacon hN β _ (localObs_separatesPoints N) hv hν

#print axioms eq_periodicState_of_localBeacon

/-! ### Coupling direction: observer views at a fixed physical resolution -/

/-- **The view of a state through an observer map** `π : C(X, Y)`: `g ↦ ν (g ∘ π)`, a state on
`C(Y, ℝ)`. Each field is the corresponding field of `ν` at `g.comp π`, the composition being
additive, homogeneous, positive and unital in `g` pointwise.

DERIVED: no numeral appears in the statement. -/
def pushState {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [CompactSpace Y] (π : C(X, Y)) (ν : State X) : State Y where
  toFun g := ν (g.comp π)
  map_add' f g := by
    show ν ((f + g).comp π) = ν (f.comp π) + ν (g.comp π)
    have h : (f + g).comp π = f.comp π + g.comp π := ContinuousMap.ext (fun _ => rfl)
    rw [h]
    exact ν.map_add _ _
  map_smul' c f := by
    show ν ((c • f).comp π) = c * ν (f.comp π)
    have h : (c • f).comp π = c • f.comp π := ContinuousMap.ext (fun _ => rfl)
    rw [h]
    exact ν.map_smul _ _
  nonneg' f hf := ν.nonneg _ (fun x => hf (π x))
  one' := by
    show ν ((1 : C(Y, ℝ)).comp π) = 1
    have h : (1 : C(Y, ℝ)).comp π = 1 := ContinuousMap.ext (fun _ => rfl)
    rw [h]
    exact ν.map_one

#print axioms pushState

/-- **The observer beacon**: `BeaconConverges A atTop` for the views
`pushState (π k) (ContinuumSchwinger.stateK hN k)`, where `stateK hN k` is the periodic Wilson state
at the coupling `dyBeta k` (running spacing `dySpacing N k`) and `π k : C(Cfg N, Y)` is the observer
map of step `k` into a compact observer space `Y`.

CHOSEN: the observer maps are a parameter. The physical reading is that `π k` reads the lattice at a
fixed physical resolution — at step `k`, blocks of `2^(k - m)` lattice spacings for a fixed physical
cell `dySpacing N m` — so that a probe `g ∈ A` sits at a fixed physical position at every step.
`π k = ContinuousMap.id` is the lattice-unit view.

DERIVED: `0` is the excluded rank in `hN`. -/
def ObserverBeacon {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] (hN : N ≠ 0)
    (π : ℕ → C(ContinuumSchwinger.Cfg N, Y)) (A : Subalgebra ℝ C(Y, ℝ)) : Prop :=
  BeaconConverges A atTop (fun k : ℕ => pushState (π k) (ContinuumSchwinger.stateK hN k))

#print axioms ObserverBeacon

/-- **One limit of the observer views along `β → ∞`.** Under `ObserverBeacon hN π A` with `A`
separating the points of `Y`, there is exactly one state `σ` on `C(Y, ℝ)` with
`pushState (π k) (stateK hN k) g → σ g` along `atTop` at every continuous `g`:
`exists_unique_limit_of_beacon`.

DERIVED: `0` is the excluded rank in `hN`. -/
theorem observer_limit_unique {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] (hN : N ≠ 0)
    (π : ℕ → C(ContinuumSchwinger.Cfg N, Y)) (A : Subalgebra ℝ C(Y, ℝ))
    (hA : A.SeparatesPoints) (hob : ObserverBeacon hN π A) :
    ∃! σ : State Y, ∀ g : C(Y, ℝ),
      Tendsto (fun k : ℕ => pushState (π k) (ContinuumSchwinger.stateK hN k) g) atTop
        (𝓝 (σ g)) :=
  exists_unique_limit_of_beacon (l := atTop) A hA
    (fun k : ℕ => pushState (π k) (ContinuumSchwinger.stateK hN k)) hob

#print axioms observer_limit_unique

/-- **Every ultrafilter sees the same observer limit.** Under `ObserverBeacon hN π A` with `A`
separating, a limit of the observer views along any ultrafilter `u ≤ atTop` equals their limit along
`atTop`: `limits_eq_of_beacon` with `l₁ = u`, `l₂ = atTop`.

DERIVED: `0` is the excluded rank in `hN`. -/
theorem observer_ultralimit_eq {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] (hN : N ≠ 0)
    (π : ℕ → C(ContinuumSchwinger.Cfg N, Y)) (A : Subalgebra ℝ C(Y, ℝ))
    (hA : A.SeparatesPoints) (hob : ObserverBeacon hN π A) (u : Ultrafilter ℕ)
    (hu : (u : Filter ℕ) ≤ atTop) {σ₁ σ₂ : State Y}
    (h₁ : ∀ g : C(Y, ℝ), Tendsto (fun k : ℕ => pushState (π k) (ContinuumSchwinger.stateK hN k) g)
      (u : Filter ℕ) (𝓝 (σ₁ g)))
    (h₂ : ∀ g : C(Y, ℝ), Tendsto (fun k : ℕ => pushState (π k) (ContinuumSchwinger.stateK hN k) g)
      atTop (𝓝 (σ₂ g))) :
    σ₁ = σ₂ := by
  haveI : (u : Filter ℕ).NeBot := u.neBot'
  exact limits_eq_of_beacon (l := atTop) A hA
    (fun k : ℕ => pushState (π k) (ContinuumSchwinger.stateK hN k)) hob hu le_rfl h₁ h₂

#print axioms observer_ultralimit_eq

/-! ### Coupling direction: the continuum Schwinger functions -/

/-- `ContinuumSchwinger.latSkR` with the per-step states as a parameter:
`∏ᵢ Z k Oᵢ · σ k (∏ᵢ smear aₖ (Oᵢ − c k Oᵢ) fᵢ)` at the spacing `aₖ = dySpacing N k`.

DERIVED: no numeral appears in the statement. -/
def latSkRWith (σ : ℕ → State (ContinuumSchwinger.Cfg N)) (ρ : ContinuumSchwinger.Renorm N)
    (k : ℕ) {ι : Type} [Fintype ι] (F : ι → ContinuumSchwinger.SField N) : ℝ :=
  ρ.pref k F * ContinuumSchwinger.latS (σ k) (ContinuumSchwinger.dySpacing N k)
    (fun i => ρ.field k (F i))

#print axioms latSkRWith

/-- `ContinuumSchwinger.contS` with the per-step states `σ` and the ultrafilter `u` as parameters:
`limUnder u (fun k => latSkRWith σ ρ k F)`.

DERIVED: no numeral appears in the statement. -/
def contSAlong (σ : ℕ → State (ContinuumSchwinger.Cfg N)) (ρ : ContinuumSchwinger.Renorm N)
    (u : Ultrafilter ℕ) {ι : Type} [Fintype ι] (F : ι → ContinuumSchwinger.SField N) : ℝ :=
  limUnder (u : Filter ℕ) (fun k => latSkRWith σ ρ k F)

#print axioms contSAlong

/-- `latSkR hN ρ k F = latSkRWith (stateK hN) ρ k F`: `ContinuumSchwinger.latSk_eq` rewrites the
spacing `aRun N (dyBeta k)` to `dySpacing N k`.

DERIVED: `0` is the excluded rank in `hN`. -/
theorem latSkR_eq_latSkRWith (hN : N ≠ 0) (ρ : ContinuumSchwinger.Renorm N) (k : ℕ) {ι : Type}
    [Fintype ι] (F : ι → ContinuumSchwinger.SField N) :
    ContinuumSchwinger.latSkR hN ρ k F = latSkRWith (ContinuumSchwinger.stateK hN) ρ k F := by
  show ρ.pref k F * ContinuumSchwinger.latSk hN k (fun i => ρ.field k (F i))
    = ρ.pref k F * ContinuumSchwinger.latS (ContinuumSchwinger.stateK hN k)
        (ContinuumSchwinger.dySpacing N k) (fun i => ρ.field k (F i))
  rw [ContinuumSchwinger.latSk_eq]

#print axioms latSkR_eq_latSkRWith

/-- `contS hN ρ F = contSAlong (stateK hN) ρ ultra F`: `contS` is `contSAlong` at the tree's two
choices, the periodic states `stateK hN` and the ultrafilter `ContinuumSchwinger.ultra`.

DERIVED: `0` is the excluded rank in `hN`. -/
theorem contS_eq_contSAlong (hN : N ≠ 0) (ρ : ContinuumSchwinger.Renorm N) {ι : Type}
    [Fintype ι] (F : ι → ContinuumSchwinger.SField N) :
    ContinuumSchwinger.contS hN ρ F
      = contSAlong (ContinuumSchwinger.stateK hN) ρ ContinuumSchwinger.ultra F := by
  have h : (fun k => ContinuumSchwinger.latSkR hN ρ k F)
      = (fun k => latSkRWith (ContinuumSchwinger.stateK hN) ρ k F) :=
    funext (fun k => latSkR_eq_latSkRWith hN ρ k F)
  unfold ContinuumSchwinger.contS contSAlong
  rw [h]

#print axioms contS_eq_contSAlong

/-- **The Schwinger beacon (the open dynamical input, Schwinger form).** For every finite family
`F` of smeared fields — local fields with test functions at fixed physical positions — the
renormalised lattice Schwinger function `latSkR hN ρ k F` converges along `atTop` in the step `k`,
that is along `β = dyBeta k → ∞` with the spacing `dySpacing N k → 0`. Stated, not proved.

The quantifier runs over every family, including `((O, f), (O, f))` with coincident supports. At a
field-strength factor `Z` growing with the step, which a non-degenerate limit of a local field needs,
that family reads `Z²` times the second moment of one smeared field and is expected to diverge
(`ContinuumSchwinger.UniformBound`); so at growing `Z` this predicate is expected to fail, and the
form expected to hold is the one restricted to separated supports (`ContinuumSep.FamSep`), which is
`ConstantPhysics.SignalConvergesSep` at `(dyBeta, dySpacing)`.

DERIVED: `0` is the excluded rank in `hN`. -/
def SchwingerBeacon (hN : N ≠ 0) (ρ : ContinuumSchwinger.Renorm N) : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → ContinuumSchwinger.SField N), ∃ L : ℝ,
    Tendsto (fun k => ContinuumSchwinger.latSkR hN ρ k F) atTop (𝓝 L)

#print axioms SchwingerBeacon

/-- **A convergent Schwinger sequence has one value along every ultrafilter.** If
`latSkR hN ρ k F → L` along `atTop`, then `contSAlong (stateK hN) ρ u F = L` for every ultrafilter
`u ≤ atTop`. Proof: `tendsto_nhds_limUnder` and `tendsto_nhds_unique` along `u`. The case
`u = ultra` is `contS_eq_of_tendsto`.

DERIVED: `0` is the excluded rank in `hN`. -/
theorem contSAlong_eq_of_tendsto (hN : N ≠ 0) (ρ : ContinuumSchwinger.Renorm N) {ι : Type}
    [Fintype ι] (F : ι → ContinuumSchwinger.SField N) {L : ℝ}
    (h : Tendsto (fun k => ContinuumSchwinger.latSkR hN ρ k F) atTop (𝓝 L))
    (u : Ultrafilter ℕ) (hu : (u : Filter ℕ) ≤ atTop) :
    contSAlong (ContinuumSchwinger.stateK hN) ρ u F = L := by
  haveI : (u : Filter ℕ).NeBot := u.neBot'
  have e : (fun k => latSkRWith (ContinuumSchwinger.stateK hN) ρ k F)
      = (fun k => ContinuumSchwinger.latSkR hN ρ k F) :=
    funext (fun k => (latSkR_eq_latSkRWith hN ρ k F).symm)
  have hw : Tendsto (fun k => latSkRWith (ContinuumSchwinger.stateK hN) ρ k F)
      (u : Filter ℕ) (𝓝 L) := by
    rw [e]
    exact h.mono_left hu
  have hlim : Tendsto (fun k => latSkRWith (ContinuumSchwinger.stateK hN) ρ k F) (u : Filter ℕ)
      (𝓝 (contSAlong (ContinuumSchwinger.stateK hN) ρ u F)) :=
    tendsto_nhds_limUnder ⟨L, hw⟩
  exact tendsto_nhds_unique hlim hw

#print axioms contSAlong_eq_of_tendsto

/-- `contS hN ρ F = L` whenever `latSkR hN ρ k F → L` along `atTop`: `contS_eq_contSAlong` and
`contSAlong_eq_of_tendsto` at `ContinuumSchwinger.ultra`.

DERIVED: `0` is the excluded rank in `hN`. -/
theorem contS_eq_of_tendsto (hN : N ≠ 0) (ρ : ContinuumSchwinger.Renorm N) {ι : Type}
    [Fintype ι] (F : ι → ContinuumSchwinger.SField N) {L : ℝ}
    (h : Tendsto (fun k => ContinuumSchwinger.latSkR hN ρ k F) atTop (𝓝 L)) :
    ContinuumSchwinger.contS hN ρ F = L := by
  rw [contS_eq_contSAlong]
  exact contSAlong_eq_of_tendsto hN ρ F h ContinuumSchwinger.ultra ContinuumSchwinger.ultra_le

#print axioms contS_eq_of_tendsto

/-- **Under the Schwinger beacon, `contS` does not depend on the ultrafilter.** For every family and
every ultrafilter `u ≤ atTop`, `contSAlong (stateK hN) ρ u F = contS hN ρ F`: both equal the `atTop`
limit (`contSAlong_eq_of_tendsto`, `contS_eq_of_tendsto`).

DERIVED: `0` is the excluded rank in `hN`. -/
theorem contSAlong_eq_contS_of_schwingerBeacon (hN : N ≠ 0) (ρ : ContinuumSchwinger.Renorm N)
    (hB : SchwingerBeacon hN ρ) {ι : Type} [Fintype ι] (F : ι → ContinuumSchwinger.SField N)
    (u : Ultrafilter ℕ) (hu : (u : Filter ℕ) ≤ atTop) :
    contSAlong (ContinuumSchwinger.stateK hN) ρ u F = ContinuumSchwinger.contS hN ρ F := by
  obtain ⟨L, hL⟩ := hB ι F
  rw [contSAlong_eq_of_tendsto hN ρ F hL u hu, contS_eq_of_tendsto hN ρ F hL]

#print axioms contSAlong_eq_contS_of_schwingerBeacon

/-- **Under the Schwinger beacon, the lattice Schwinger functions converge to `contS` along `atTop`**
— the conclusion of `ContinuumSchwinger.tendsto_contS` along `atTop` in place of `ultra`, and with no
`UniformBound` hypothesis. `SchwingerBeacon` asks convergence of every family, coincident supports
included, so at a growing field-strength factor it is expected to fail on the same coincident family
`((O, f), (O, f))` on which `UniformBound` is expected to fail.

DERIVED: `0` is the excluded rank in `hN`. -/
theorem tendsto_contS_atTop_of_schwingerBeacon (hN : N ≠ 0) (ρ : ContinuumSchwinger.Renorm N)
    (hB : SchwingerBeacon hN ρ) {ι : Type} [Fintype ι] (F : ι → ContinuumSchwinger.SField N) :
    Tendsto (fun k => ContinuumSchwinger.latSkR hN ρ k F) atTop
      (𝓝 (ContinuumSchwinger.contS hN ρ F)) := by
  obtain ⟨L, hL⟩ := hB ι F
  rw [contS_eq_of_tendsto hN ρ F hL]
  exact hL

#print axioms tendsto_contS_atTop_of_schwingerBeacon

/-- **Both ultrafilter choices drop out: the same forest.** Suppose the volume beacon holds at every
step's coupling `dyBeta k` for a point-separating `A`, and `latSkR hN ρ k F → L` along `atTop`. Then
for ANY choice `σ k` of periodic limit at each step (`IsPeriodicLimit`, a limit along any ultrafilter
finer than `atTop` in the extent) and ANY ultrafilter `u ≤ atTop` in the step,
`contSAlong σ ρ u F = L`. Each `σ k` is `stateK hN k` by `eq_periodicState_of_volumeBeacon`, and
`contSAlong_eq_of_tendsto` finishes.

So `contS hN ρ F`, built from `PeriodicState.periodicUltra` at every step and from
`ContinuumSchwinger.ultra`, is the value every other such choice produces.

DERIVED: `1` enters through `one_le_of_ne_zero`, the least colour count at which `dyBeta` is
defined; `0` is the excluded rank in `hN`. -/
theorem contSAlong_eq_of_beacons (hN : N ≠ 0) (ρ : ContinuumSchwinger.Renorm N)
    (A : Subalgebra ℝ C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hA : A.SeparatesPoints)
    (hvol : ∀ k : ℕ,
      VolumeBeacon hN (ContinuumSchwinger.dyBeta (ContinuumSchwinger.one_le_of_ne_zero hN) k) A)
    (σ : ℕ → State (ContinuumSchwinger.Cfg N))
    (hσ : ∀ k : ℕ,
      IsPeriodicLimit hN (ContinuumSchwinger.dyBeta (ContinuumSchwinger.one_le_of_ne_zero hN) k)
        (σ k))
    {ι : Type} [Fintype ι] (F : ι → ContinuumSchwinger.SField N) {L : ℝ}
    (h : Tendsto (fun k => ContinuumSchwinger.latSkR hN ρ k F) atTop (𝓝 L))
    (u : Ultrafilter ℕ) (hu : (u : Filter ℕ) ≤ atTop) :
    contSAlong σ ρ u F = L := by
  have hσeq : σ = ContinuumSchwinger.stateK hN :=
    funext (fun k => eq_periodicState_of_volumeBeacon hN _ A hA (hvol k) (hσ k))
  rw [hσeq]
  exact contSAlong_eq_of_tendsto hN ρ F h u hu

#print axioms contSAlong_eq_of_beacons

/-- **The beacon on separated supports.** For every `d > 0` and every family whose test-function supports
are pairwise `d`-separated (`ContinuumSep.FamSep`), the renormalised lattice Schwinger functions converge
along the couplings. This is `SchwingerBeacon` with the coincident configurations removed, the form
expected to hold at a growing field-strength factor.

DERIVED: `0` is the excluded colour count and the lower end of `d`. -/
def SchwingerBeaconSep (hN : N ≠ 0) (ρ : ContinuumSchwinger.Renorm N) : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → ContinuumSchwinger.SField N) (d : ℝ), 0 < d →
    ContinuumSep.FamSep d F →
      ∃ L : ℝ, Tendsto (fun k => ContinuumSchwinger.latSkR hN ρ k F) atTop (𝓝 L)

#print axioms SchwingerBeaconSep

/-- `SchwingerBeacon` gives its separated form. -/
theorem schwingerBeaconSep_of_schwingerBeacon (hN : N ≠ 0) (ρ : ContinuumSchwinger.Renorm N)
    (hB : SchwingerBeacon hN ρ) : SchwingerBeaconSep hN ρ :=
  fun ι _ F _ _ _ => hB ι F

#print axioms schwingerBeaconSep_of_schwingerBeacon

/-- **On separated families `contS` is the limit along the couplings.** Under `SchwingerBeaconSep`, every
`d`-separated family's renormalised lattice Schwinger functions converge along `atTop` to
`ContinuumSchwinger.contS`, whichever ultrafilter `contS` was read along.

DERIVED: `0` is the excluded colour count and the lower end of `d`. -/
theorem tendsto_contS_atTop_of_schwingerBeaconSep (hN : N ≠ 0) (ρ : ContinuumSchwinger.Renorm N)
    (hB : SchwingerBeaconSep hN ρ) {ι : Type} [Fintype ι] (F : ι → ContinuumSchwinger.SField N)
    {d : ℝ} (hd : 0 < d) (hF : ContinuumSep.FamSep d F) :
    Tendsto (fun k => ContinuumSchwinger.latSkR hN ρ k F) atTop
      (𝓝 (ContinuumSchwinger.contS hN ρ F)) := by
  obtain ⟨L, hL⟩ := hB ι F d hd hF
  rw [contS_eq_of_tendsto hN ρ F hL]
  exact hL

#print axioms tendsto_contS_atTop_of_schwingerBeaconSep

end Tree

end MassGap.Beacon
