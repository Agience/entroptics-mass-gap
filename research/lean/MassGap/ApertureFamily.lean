import MassGap.ApertureRoute

/-!
# MassGap.ApertureFamily — the flagship from an aperture chosen per coupling

`ApertureRoute.ConfinesAtAnAperture` is `∃ a : EvenAp, ∀ β, 3^(-1/4) < cosAvgEven a β`: one extent
serving every coupling. This module defines the quantifier-swapped

    ConfinesAtEachCoupling := ∀ β : ℝ, ∃ a : EvenAp, 3^(-1/4) < cosAvgEven a β

and rebuilds the same conclusion from it — gap, non-triviality, `SO(4)` invariance and the OS0–OS3
continuum clause — as `flagship_of_confinement_at_each_coupling`, with foundational axioms only.
`confinesAtEachCoupling_of_confinesAtAnAperture` is the implication from the unswapped hypothesis;
it is proved in one direction only.

## Why the swap goes through

`ApertureRoute.fullModelOfConfinement` consumes its hypothesis through `apertureOf hc = hc.choose`
and `.choose_spec`, with the `Classical.choose` outside the `∀ β`. Every field the construction has
to fill accepts a per-coupling aperture instead:

* `LatticeYM.μ : ℝ → ℝ` is a function of the coupling; `fun β => μEven (A β) β` is a value of that
  type as much as `μEven a` is.
* `LatticeYM.m : ℝ → Idx → ℂ` is likewise a function of `β`, and `ymModelEven`'s value for it is
  `exp(-(κ₀ − μ β))`, which reads the aperture only through `μ β`.
* `A1_YM M` is `Apriori.A1 M.μ M.κ₀`, that is `∀ β, M.μ β < M.κ₀`, pointwise in `β`.
* `LatticeYM.R`, and hence `A2_YM`, contains no aperture: `EvenAperture.A2_even`'s proof body does
  not mention its own argument, being `A2_continuum_of_congruence` on `freadYM ∘ Gram ∘ Fym`.
* `FullModel.measure` is a `LatticeYMFamily` given as a closed term —
  `OSFamily.osFamilyTension ApertureRoute.βFlag` here and in `ApertureRoute` — and
  `Measure.continuum_of_family` takes it as data.
* `LatticeYM.hfloor` is `le_refl _`. `LatticeYM.hread` is `‖m β k‖ ≤ exp(-(κ₀ − μ β))`, and at these
  field values `m` is that exponential cast to `ℂ`, so its proof is `Complex.norm_real` and
  `le_of_eq`, unchanged by any substitution for `μ` that leaves `m` its exponential.

`ApertureRoute.FlagshipAt`'s gap conjuncts are `∀ β, Tendsto … (nhds 0)` and `∀ β, μ β − κ < 0`,
both quantified over `β` outermost, and its measure conjunct does not mention `β`, so no conjunct
relates two couplings.

## Scope

Neither hypothesis gives a gap rate uniform in the coupling. `FlagshipAt` gives `0 < κ₀ − μ β` at
each `β` separately, and so does `mass_gap_rate_and_continuum_at_each_coupling`. `UniformSurplus`
states the uniform premise, and `uniform_gap_of_uniformSurplus` proves it sufficient for a
coupling-uniform geometric bound; no converse is proved.

`forall_exists_aperture_does_not_give_exists_forall` shows that over `EvenAp` and `ℝ` the
implication `(∀ β, ∃ a, P a β) → (∃ a, ∀ β, P a β)` fails for some predicate `P`. It is a statement
about the quantifier shape, not about `cosAvgEven`; no declaration in this tree settles whether the
converse holds for that predicate.

`ContactDominance.aperture_uniformity_does_not_give_coupling_uniformity` concerns a different
implication: there the swapped quantifier is a bound `B` on the moment and the aperture is universal
on both sides, whereas here the swapped quantifier is the aperture itself and no `B` occurs.

`MassGap.FlagshipScope`, not imported here, records what `FlagshipAt` delimits:
`flagship_for_bogus` proves the whole conclusion for an object with tension the constant `0` and
carrier types `Unit`, and `gap_summand_is_manufactured` shows the gap conjunct's sum is a one-mode
geometric sequence whose magnitude is the bound itself. The hypothesis
`ConfinesAtAnAperture` is a statement about `cosAvgEven` of `readEven`, hence about `wilsonCorrAt`
at an even aperture of at least four.

## Provenance

Sections 2, 3 and 5 transcribe `EvenAperture`'s and `ApertureRoute`'s field values and proof terms
with `apertureAt hc β` in place of the fixed `apertureOf hc`, introducing no numeral. Sections 4 and
6 have no antecedent in either module; the numerals `2n+3`, `n+2` and `a.1 + 1` occur in
`forall_exists_aperture_does_not_give_exists_forall`'s proof and are forced by `EvenAp`'s own
`N + 1 = 2m ∧ 2 ≤ m`. `#print axioms` follows every declaration.

DERIVED: `3`, `1` and `4` are `3 ^ (-(1 : ℝ) / 4) = e^(-κ₀YM)`, the entropy floor, carried from
`ConfinesAtAnAperture`; `0` is a sign condition, a limit point, or the level non-triviality compares
against; `1` is the single mode's weight in `ymModelFamily`.
-/

namespace MassGap.ApertureFamily

open Filter
open scoped Matrix
open MassGap.EvenAperture
open MassGap.ApertureRoute

/-! ## 1. The hypothesis, swapped -/

/-- At every coupling `β` there is some `a : EvenAp` — an even extent of at least four — at which
`cosAvgEven a β` exceeds the entropy floor `3 ^ (-(1 : ℝ) / 4) = e^(-κ₀YM)`. It is
`ApertureRoute.ConfinesAtAnAperture` with the two quantifiers exchanged, so the extent may vary with
the coupling.

The condition is on the cosine average rather than on the tension.
`ApertureRoute.unguarded_confinement_is_satisfiable_without_decay` shows the bare tension form is
satisfied by a read with no decay, because `Real.log` is even.

Nothing in this tree ties `β` to a lattice spacing: `LatticeYM`'s `β` is the coupling and
`FullModel` is not indexed by spacing, as `FullModel.mass_gap_rate_and_continuum`'s first caveat
records. The reading of a coupling-dependent `EvenAp` as a fixed physical aperture in lattice units
is not derived anywhere here.

DERIVED: `3`, `1` and `4` form `3 ^ (-(1 : ℝ) / 4)`, the entropy floor `e^(-κ₀YM)` with
`κ₀YM = ¼ log 3`, carried from `ConfinesAtAnAperture` unchanged. `EvenAp`'s own conditions are
likewise carried across the swap. -/
def ConfinesAtEachCoupling : Prop :=
  ∀ β : ℝ, ∃ a : EvenAp, (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β

#print axioms ConfinesAtEachCoupling

/-- The aperture the hypothesis supplies at `β`: `(hc β).choose`. It is `ApertureRoute.apertureOf`
with the `Classical.choose` inside the coupling binder, so the result is a function `ℝ → EvenAp`
rather than a single `EvenAp`.

DERIVED: no numeral appears in the statement. -/
noncomputable def apertureAt (hc : ConfinesAtEachCoupling) (β : ℝ) : EvenAp := (hc β).choose

#print axioms apertureAt

/-- `3 ^ (-(1 : ℝ) / 4) < cosAvgEven (apertureAt hc β) β`, which is `(hc β).choose_spec`: the
aperture chosen at `β` clears the floor at `β`.

DERIVED: `3`, `1` and `4` form the entropy floor `3 ^ (-(1 : ℝ) / 4) = e^(-κ₀YM)`. -/
theorem apertureAt_cosAvg (hc : ConfinesAtEachCoupling) (β : ℝ) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven (apertureAt hc β) β := (hc β).choose_spec

#print axioms apertureAt_cosAvg

/-- `ConfinesAtEachCoupling` is equivalent to the existence of an aperture function
`A : ℝ → EvenAp` with `3 ^ (-(1 : ℝ) / 4) < cosAvgEven (A β) β` at every `β`. Forward is
`apertureAt` with its specification, which is where the choice is spent; backward is projection.

DERIVED: `3`, `1` and `4` form the entropy floor `3 ^ (-(1 : ℝ) / 4) = e^(-κ₀YM)`. -/
theorem confinesAtEachCoupling_iff_apertureFunction :
    ConfinesAtEachCoupling
      ↔ ∃ A : ℝ → EvenAp, ∀ β : ℝ, (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven (A β) β :=
  ⟨fun hc => ⟨apertureAt hc, apertureAt_cosAvg hc⟩, fun ⟨A, hA⟩ β => ⟨A β, hA β⟩⟩

#print axioms confinesAtEachCoupling_iff_apertureFunction

/-- The tension along the aperture function: `fun β => μEven (apertureAt hc β) β`. This is the
`LatticeYM.μ` field of `ymModelFamily`, and the one place the quantifier swap appears in the model —
`ApertureRoute` has `μEven (apertureOf hc)`, a fixed extent applied to `β`.

DERIVED: no numeral appears in the statement. -/
noncomputable def tensionOf (hc : ConfinesAtEachCoupling) : ℝ → ℝ :=
  fun β => μEven (apertureAt hc β) β

#print axioms tensionOf

/-- `tensionOf hc β < κ₀YM` at every coupling. It is
`Moment.Read.tension_lt_floor_of_cosAvg` applied to `(hc β).choose_spec` inside the binder, the
direction that reads the logarithm only where its argument is positive. Since `Apriori.A1` is
pointwise in `β`, this discharges `A1_YM` for `ymModelFamily`.

DERIVED: no numeral appears in the statement. -/
theorem tensionOf_lt_floor (hc : ConfinesAtEachCoupling) (β : ℝ) :
    tensionOf hc β < MassGap.κ₀YM :=
  (readEven (apertureAt hc β) β).tension_lt_floor_of_cosAvg ((hc β).choose_spec)

#print axioms tensionOf_lt_floor

/-! ## 2. The model, the full model, and the realisation

`EvenAperture.ymModelEven` and `ApertureRoute.fullModelOfConfinement`, with `tensionOf hc` in place
of `μEven (apertureOf hc)` wherever that appears. -/

/-- A `LatticeYM` whose tension is read at each coupling's own extent:
`EvenAperture.ymModelEven` with `μEven a` replaced by `tensionOf hc`.

`Idx`, `Dir`, `s`, `P`, `R`, `κ₀`, `κ` and `hfloor` are `ymModelEven`'s unchanged; none mentions an
aperture. `m`, `μ` and `hread` are `ymModelEven`'s with the substitution, three occurrences in all.
`hread`'s proof is `Complex.norm_real` and `Real.norm_of_nonneg` on `m`'s exponential followed by
`le_of_eq`, which does not look inside the tension.

DERIVED: as in `ymModelEven`, `1` is the single mode's weight, forced by normalisation; no other
numeral occurs. -/
noncomputable def ymModelFamily (hc : ConfinesAtEachCoupling) : MassGap.LatticeYM where
  Idx := Unit
  Dir := MassGap.DYM
  s := fun _ => (Finset.univ : Finset Unit)
  P := fun _ _ => 1
  m := fun β _ => ((Real.exp (-(MassGap.κ₀YM - tensionOf hc β)) : ℝ) : ℂ)
  μ := tensionOf hc
  R := fun d => MassGap.freadYM ((MassGap.Fym d)ᵀ * MassGap.Fym d).charpoly
  κ₀ := MassGap.κ₀YM
  κ := MassGap.κ₀YM
  hfloor := le_refl _
  hread := by
    intro β _ _
    have h : ‖((Real.exp (-(MassGap.κ₀YM - tensionOf hc β)) : ℝ) : ℂ)‖
        = Real.exp (-(MassGap.κ₀YM - tensionOf hc β)) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact le_of_eq h

#print axioms ymModelFamily

/-- `A1_YM (ymModelFamily hc)`, which unfolds to `∀ β, tensionOf hc β < κ₀YM` and is
`tensionOf_lt_floor` unchanged. `Apriori.A1` quantifies over `β` and relates no two couplings.

DERIVED: no numeral appears in the statement. -/
theorem A1_family (hc : ConfinesAtEachCoupling) : MassGap.A1_YM (ymModelFamily hc) :=
  tensionOf_lt_floor hc

#print axioms A1_family

/-- `A2_YM (ymModelFamily hc)`, which is `EvenAperture.A2_even` at `apFour`. `A2_YM M` is `A2 M.R`,
and the `R` fields of `ymModelEven a` and `ymModelFamily hc` are the same term, so the instance at
any extent proves this one. `apFour` is supplied because `A2_even` takes an argument its proof body
does not mention; any `EvenAp` would serve.

DERIVED: no numeral appears in the statement. -/
theorem A2_family (hc : ConfinesAtEachCoupling) : MassGap.A2_YM (ymModelFamily hc) :=
  MassGap.EvenAperture.A2_even MassGap.EvenAperture.apFour

#print axioms A2_family

/-- A `FullModel` with `gap := ymModelFamily hc`, `h1` and `h2` from `A1_family` and `A2_family`,
and `measure := OSFamily.osFamilyTension ApertureRoute.βFlag` — the same closed term
`ApertureRoute.fullModelOfConfinement` carries, whose sequence index is the lattice extent.
`ApertureRoute`'s module docstring states what that clause gives.

DERIVED: no numeral appears in the statement; every constant belongs to the pieces assembled, and
`βFlag` carries its own note. -/
noncomputable def fullModelOfEachCoupling (hc : ConfinesAtEachCoupling) : MassGap.FullModel where
  gap := ymModelFamily hc
  h1 := A1_family hc
  h2 := A2_family hc
  measure := MassGap.OSFamily.osFamilyTension MassGap.ApertureRoute.βFlag

#print axioms fullModelOfEachCoupling

/-- `(fullModelOfEachCoupling hc).measure = OSFamily.osFamilyTension ApertureRoute.βFlag`, by
`rfl`: the measure field is the closed term `ApertureRoute` also uses, and the quantifier swap in
the gap-side hypothesis does not reach it.

DERIVED: no numeral appears in the statement. -/
theorem measure_is_osFamilyTension (hc : ConfinesAtEachCoupling) :
    (fullModelOfEachCoupling hc).measure
      = MassGap.OSFamily.osFamilyTension MassGap.ApertureRoute.βFlag := rfl

#print axioms measure_is_osFamilyTension

/-- A `WilsonRealization` pairing `WilsonModel.paramsTension` with `fullModelOfEachCoupling hc`,
the `hc` field being `paramsTension_irCutoff.symm`. It transcribes
`ApertureRoute.wilsonOfConfinement`.

`paramsTension` depends on an aperture of its own: its infrared cutoff `cW` contains
`rW ^ (kW + 1)`, and `WilsonModel.kW` is `Classical.choose`n — an aperture at which the witness read
`readW`, a geometric circle correlation rather than the Wilson ensemble, clears the entropy floor.
That aperture is a bare `ℕ` on the measure side; it is not an `EvenAp`, not `apertureAt hc β`, and
no field of this model reaches it, so `paramsTension` is reused unchanged.

DERIVED: no numeral appears in the statement; `3` is `SU(3)`'s rank, carried inside
`paramsTension`. -/
noncomputable def wilsonOfEachCoupling (hc : ConfinesAtEachCoupling) : MassGap.WilsonRealization where
  params := MassGap.WilsonModel.paramsTension
  model := fullModelOfEachCoupling hc
  hc := MassGap.WilsonModel.paramsTension_irCutoff.symm

#print axioms wilsonOfEachCoupling

/-! ## 3. The flagship, from the swapped hypothesis -/

/-- The flagship conclusion at this module's realisation: the mode sum tending to `0` at every
coupling, non-triviality `μ β − κ < 0`, direction-independence of `R`, and the OS0–OS3 subsequential
limit with its bound, nonnegativity and two invariances.

It is `ApertureRoute.FlagshipAt`'s statement clause for clause, about `wilsonOfEachCoupling hc`
rather than `wilsonOfConfinement hc`, so the two can be compared by reading.

DERIVED: every `0` in the statement is a limit point, the level non-triviality compares against, or
the lower bound asserted on `q`; `c` and `B` are the measure family's own fields. -/
def FlagshipAtEach (hc : ConfinesAtEachCoupling) : Prop :=
  ((∀ β, Tendsto (fun τ : ℕ => ‖∑ k ∈ (wilsonOfEachCoupling hc).model.gap.s β,
        (wilsonOfEachCoupling hc).model.gap.P β k
          * ((wilsonOfEachCoupling hc).model.gap.m β k) ^ τ‖) atTop (nhds 0)) ∧
      (∀ β, (wilsonOfEachCoupling hc).model.gap.μ β
          - (wilsonOfEachCoupling hc).model.gap.κ < 0) ∧
      (∀ d d', (wilsonOfEachCoupling hc).model.gap.R d
          = (wilsonOfEachCoupling hc).model.gap.R d')) ∧
    (∃ (q : (wilsonOfEachCoupling hc).model.measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ j, Tendsto (fun k => (wilsonOfEachCoupling hc).model.measure.Q j (φ k)) atTop (nhds (q j))) ∧
      (∀ j, |q j| ≤ (⌈(wilsonOfEachCoupling hc).model.measure.c⌉₊ : ℝ)
              * (wilsonOfEachCoupling hc).model.measure.B) ∧
      (∀ j, 0 ≤ q j) ∧
      (∀ g j, q ((wilsonOfEachCoupling hc).model.measure.actE g j) = q j) ∧
      (∀ σ j, q ((wilsonOfEachCoupling hc).model.measure.actP σ j) = q j))

#print axioms FlagshipAtEach

/-- `FlagshipAtEach hc` from `ConfinesAtEachCoupling` alone, the proof term being
`existence_and_gap_of_wilson (wilsonOfEachCoupling hc)`. No conjunct is dropped and no further
premise is taken.

`FlagshipAtEach` is not the same proposition as `ApertureRoute.FlagshipAt`: the two realisations'
`μ` fields are `μEven ((hc β).choose) β` and `μEven hc.choose β`, drawn by `Classical.choose` from
different propositions, so they are not definitionally equal. The clauses coincide and each is the
flagship at its own model.

DERIVED: no numeral appears in the statement; those in `FlagshipAtEach` are noted there. -/
theorem flagship_of_confinement_at_each_coupling (hc : ConfinesAtEachCoupling) : FlagshipAtEach hc :=
  MassGap.existence_and_gap_of_wilson (wilsonOfEachCoupling hc)

#print axioms flagship_of_confinement_at_each_coupling

/-- At each coupling `β`: `0 < κ₀ − μ β`, the geometric bound
`‖∑ k, P β k * m β k ^ τ‖ ≤ (∑ k, ‖P β k‖) * exp(-(κ₀ − μ β)) ^ τ` at every `τ`, and the OS0–OS3
subsequential limit. It is `MassGap.mass_gap_rate_and_continuum` at
`fullModelOfEachCoupling hc`.

The rate is the entropy surplus at that coupling's own extent; it is not claimed to be bounded away
from zero over `β`, which is what `UniformSurplus` would add.

DERIVED: `0` is the level the surplus exceeds and the lower bound asserted on `q`. -/
theorem mass_gap_rate_and_continuum_at_each_coupling
    (hc : ConfinesAtEachCoupling) (β : ℝ) :
    (0 < (fullModelOfEachCoupling hc).gap.κ₀ - (fullModelOfEachCoupling hc).gap.μ β ∧
      ∀ τ : ℕ, ‖∑ k ∈ (fullModelOfEachCoupling hc).gap.s β,
          (fullModelOfEachCoupling hc).gap.P β k * ((fullModelOfEachCoupling hc).gap.m β k) ^ τ‖
        ≤ (∑ k ∈ (fullModelOfEachCoupling hc).gap.s β,
              ‖(fullModelOfEachCoupling hc).gap.P β k‖)
            * Real.exp (-((fullModelOfEachCoupling hc).gap.κ₀
                - (fullModelOfEachCoupling hc).gap.μ β)) ^ τ) ∧
      (∃ (q : (fullModelOfEachCoupling hc).measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ j, Tendsto (fun k => (fullModelOfEachCoupling hc).measure.Q j (φ k)) atTop (nhds (q j))) ∧
        (∀ j, |q j| ≤ (⌈(fullModelOfEachCoupling hc).measure.c⌉₊ : ℝ)
                * (fullModelOfEachCoupling hc).measure.B) ∧
        (∀ j, 0 ≤ q j) ∧
        (∀ g j, q ((fullModelOfEachCoupling hc).measure.actE g j) = q j) ∧
        (∀ σ j, q ((fullModelOfEachCoupling hc).measure.actP σ j) = q j)) :=
  MassGap.mass_gap_rate_and_continuum (fullModelOfEachCoupling hc) β

#print axioms mass_gap_rate_and_continuum_at_each_coupling

/-! ## 4. The swapped hypothesis is WEAKER

One direction, and only one. -/

/-- `ConfinesAtEachCoupling` from `ConfinesAtAnAperture`: instantiate the single extent
`apertureOf hc` at every coupling, with `apertureOf_cosAvg` for the inequality. Only this direction
is proved.

DERIVED: no numeral appears in the statement. -/
theorem confinesAtEachCoupling_of_confinesAtAnAperture (hc : ConfinesAtAnAperture) :
    ConfinesAtEachCoupling :=
  fun β => ⟨apertureOf hc, apertureOf_cosAvg hc β⟩

#print axioms confinesAtEachCoupling_of_confinesAtAnAperture

/-- `FlagshipAtEach (confinesAtEachCoupling_of_confinesAtAnAperture hc)` from
`ConfinesAtAnAperture`, composing the two preceding results. Every conjunct the unswapped route
concludes is concluded here.

The conclusion is `FlagshipAtEach`, not `ApertureRoute.FlagshipAt`; the two realisations differ in
their `Classical.choose`n aperture, so the propositions differ while the clauses coincide.

DERIVED: no numeral appears in the statement. -/
theorem flagship_of_confinesAtAnAperture_via_family (hc : ConfinesAtAnAperture) :
    FlagshipAtEach (confinesAtEachCoupling_of_confinesAtAnAperture hc) :=
  flagship_of_confinement_at_each_coupling _

#print axioms flagship_of_confinesAtAnAperture_via_family

/-- The schema `∀ P : EvenAp → ℝ → Prop, (∀ β, ∃ a, P a β) → (∃ a, ∀ β, P a β)` is false. The
refuting predicate is `P a β := β ≤ (a.1 : ℝ)`: extents are unbounded, since `⟨2n+3, n+2, _, _⟩` is
an `EvenAp` for every `n` and `exists_nat_gt` puts one past any `β`, while a single extent fails at
`β = (a.1 : ℝ) + 1`.

The statement is about the quantifier shape over `EvenAp` and `ℝ`. It does not concern
`cosAvgEven`, and it does not settle whether `ConfinesAtEachCoupling` implies
`ConfinesAtAnAperture` for that particular predicate; no declaration in this tree settles that in
either direction.

DERIVED: no numeral appears in the statement. In the proof, `2n+3` is the odd extent whose successor
is `2(n+2)`, forced by `EvenAp`'s own `N + 1 = 2m` with `2 ≤ m`, and `a.1 + 1` is the smallest point
past a given extent. -/
theorem forall_exists_aperture_does_not_give_exists_forall :
    ¬ (∀ P : EvenAp → ℝ → Prop, (∀ β : ℝ, ∃ a : EvenAp, P a β) → (∃ a : EvenAp, ∀ β : ℝ, P a β)) := by
  intro hswap
  obtain ⟨a, ha⟩ := hswap (fun a β => β ≤ (a.1 : ℝ)) (fun β => by
    obtain ⟨n, hn⟩ := exists_nat_gt β
    refine ⟨⟨2 * n + 3, n + 2, by omega, by omega⟩, ?_⟩
    have hc : ((n : ℝ)) ≤ (((2 * n + 3 : ℕ) : ℝ)) := by push_cast; linarith
    exact le_trans hn.le hc)
  have := ha ((a.1 : ℝ) + 1)
  linarith

#print axioms forall_exists_aperture_does_not_give_exists_forall

/-! ## 5. The obligation, restated at each coupling

`NonnegArm.lawBelow_holds` plus `NonnegArm.substrate_even_of_two_arm` reduce the Clay statement to
`LawAbove b`. That composition is reused verbatim; the only change is where it lands. -/

/-- There is a `b > 0` such that `NonnegArm.LawAbove b` — the contact-relative quartic law on
`(b, ∞)` — yields some `hc : ConfinesAtEachCoupling` together with `FlagshipAtEach hc`.

`b` and the `[0, b]` arm come from `NonnegArm.lawBelow_holds`, which carries
`ContactFloor.contact_relative_unconditional`; `b` is that theorem's own cut and is not named here.
The two arms feed `NonnegArm.substrate_even_of_two_arm` and
`confinement_at_an_aperture_of_substrate`, and the result is weakened by
`confinesAtEachCoupling_of_confinesAtAnAperture`.

`LawAbove b` is the same sufficient input `ApertureRoute` takes; what differs is that the
intermediate conclusion here is one extent per coupling.

DERIVED: `0` is the positivity threshold on the cut `b`. -/
theorem confinement_at_each_coupling_of_law_above_cut :
    ∃ b : ℝ, 0 < b ∧ (MassGap.NonnegArm.LawAbove b →
      ∃ hc : ConfinesAtEachCoupling, FlagshipAtEach hc) := by
  obtain ⟨b, hbpos, hbelow⟩ := MassGap.NonnegArm.lawBelow_holds
  refine ⟨b, hbpos, fun habove => ?_⟩
  exact ⟨confinesAtEachCoupling_of_confinesAtAnAperture
      (confinement_at_an_aperture_of_substrate
        (MassGap.NonnegArm.substrate_even_of_two_arm b hbelow habove)),
    flagship_of_confinement_at_each_coupling _⟩

#print axioms confinement_at_each_coupling_of_law_above_cut

/-! ## 6. What NEITHER hypothesis gives: a coupling-uniform rate

The flagship's gap clause is `∀ β, Tendsto … (nhds 0)` — decay at each coupling, at a rate
`κ₀ − μ β` that is positive for each `β` and is not bounded away from zero over `β` by anything
proved. That is true of `ApertureRoute.FlagshipAt` as well, so it is not a cost of the swap; it is
named here because a reader looking for where the `∀ β` went will look in exactly this place.

`UniformSurplus` is the missing premise, as a Prop rather than as prose, and
`uniform_gap_of_uniformSurplus` proves it SUFFICIENT. That direction only: no converse is proved
here, so nothing says a coupling-uniform bound could not arrive some other way. What the proof does
show is that the premise is not merely sufficient by a detour — the rate it delivers is `Δ` itself,
the surplus's own constant, unweakened. -/

/-- A coupling-uniform entropy surplus for a tension function `μ`: there is a `Δ > 0` with
`Δ ≤ κ₀YM - μ β` at every `β`. The quantifier over `Δ` is outside the quantifier over `β`.

`Apriori.A1 μ κ₀` is `∀ β, μ β < κ₀`, which permits `μ β → κ₀` and hence a mode magnitude
`exp(-(κ₀ - μ β))` approaching `1`, so `A1` does not give this.

DERIVED: `0` is the positivity threshold on `Δ`; `Δ` is quantified, not chosen. -/
def UniformSurplus (μ : ℝ → ℝ) : Prop := ∃ Δ : ℝ, 0 < Δ ∧ ∀ β : ℝ, Δ ≤ MassGap.κ₀YM - μ β

#print axioms UniformSurplus

/-- From `UniformSurplus (tensionOf hc)`: one `Δ > 0` and one bound
`‖∑ k ∈ s β, P β k * m β k ^ τ‖ ≤ (∑ k ∈ s β, ‖P β k‖) * exp(-Δ) ^ τ` holding at every coupling and
every `τ`. It is `MassGap.geometric_bound_of_mode_bound` at the ratio `exp(-Δ)`, the surplus
entering only through `Real.exp_le_exp`, so the rate delivered is `Δ` itself.

Only this direction is proved; no converse is stated. The proof does not use the aperture function,
so the same statement over `ApertureRoute.fullModelOfConfinement`'s tension would need the same
premise.

DERIVED: `0` is the positivity threshold on `Δ`. -/
theorem uniform_gap_of_uniformSurplus (hc : ConfinesAtEachCoupling)
    (hu : UniformSurplus (tensionOf hc)) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ (β : ℝ) (τ : ℕ),
      ‖∑ k ∈ (ymModelFamily hc).s β, (ymModelFamily hc).P β k * ((ymModelFamily hc).m β k) ^ τ‖
        ≤ (∑ k ∈ (ymModelFamily hc).s β, ‖(ymModelFamily hc).P β k‖) * Real.exp (-Δ) ^ τ := by
  obtain ⟨Δ, hΔ, hb⟩ := hu
  refine ⟨Δ, hΔ, fun β τ => ?_⟩
  refine MassGap.geometric_bound_of_mode_bound _ _ _ _ (Real.exp_pos _).le (fun k _ => ?_) τ
  show ‖((Real.exp (-(MassGap.κ₀YM - tensionOf hc β)) : ℝ) : ℂ)‖ ≤ Real.exp (-Δ)
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (by linarith [hb β])

#print axioms uniform_gap_of_uniformSurplus

/-! ## 7. Footprints -/

section Audit
#print axioms ConfinesAtEachCoupling
#print axioms apertureAt
#print axioms apertureAt_cosAvg
#print axioms confinesAtEachCoupling_iff_apertureFunction
#print axioms tensionOf
#print axioms tensionOf_lt_floor
#print axioms ymModelFamily
#print axioms A1_family
#print axioms A2_family
#print axioms fullModelOfEachCoupling
#print axioms measure_is_osFamilyTension
#print axioms wilsonOfEachCoupling
#print axioms FlagshipAtEach
#print axioms flagship_of_confinement_at_each_coupling
#print axioms mass_gap_rate_and_continuum_at_each_coupling
#print axioms confinesAtEachCoupling_of_confinesAtAnAperture
#print axioms flagship_of_confinesAtAnAperture_via_family
#print axioms forall_exists_aperture_does_not_give_exists_forall
#print axioms confinement_at_each_coupling_of_law_above_cut
#print axioms UniformSurplus
#print axioms uniform_gap_of_uniformSurplus
end Audit

end MassGap.ApertureFamily
