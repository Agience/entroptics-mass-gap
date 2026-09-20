import MassGap.ApertureRoute

/-!
# MassGap.ApertureFamily — the flagship from confinement at EACH coupling

`ApertureRoute.ConfinesAtAnAperture` is `∃ a : EvenAp, ∀ β, 3^{−1/4} < cosAvgEven a β`: ONE extent
serving EVERY coupling. This file rebuilds the whole flagship from the quantifier-swapped

    ConfinesAtEachCoupling := ∀ β : ℝ, ∃ a : EvenAp, 3^{−1/4} < cosAvgEven a β

— a READ APERTURE CHOSEN PER COUPLING. The swap is a genuine weakening (`∀∃` from `∃∀`, one way
only), and the conclusion is unchanged: gap, non-triviality, `SO(4)` invariance and the tight OS0–OS3
continuum limit, `flagship_of_confinement_at_each_coupling`, foundational axioms only.

## WHERE THE `∀ β` STRENGTH WAS BEING SPENT: NOWHERE

`ApertureRoute.fullModelOfConfinement` consumes the hypothesis through `apertureOf hc = hc.choose`
and its `.choose_spec`, and nothing else. `Classical.choose` there sits OUTSIDE the `∀ β`, so the
construction fixes one extent before quantifying over the coupling. That placement is what makes the
`∃∀` order look load-bearing. It is not, and the reason is in the structure the model has to inhabit:

* `Model.LatticeYM.μ : ℝ → ℝ` is a FUNCTION OF THE COUPLING. Nothing requires it to factor as
  `μEven a` for a fixed `a`; `fun β => μEven (A β) β` is as good a field value.
* `Model.LatticeYM.m : ℝ → Idx → ℂ` is likewise a function of `β`, and `ymModelEven`'s value for it
  is `exp(-(κ₀ − μ β))` — it reads the aperture only through `μ β`.
* `Model.A1_YM M = Apriori.A1 M.μ M.κ₀ = ∀ β, M.μ β < M.κ₀`. POINTWISE IN `β`. There is no clause
  asking that the `β`s be served by one object.
* `Model.LatticeYM.R`, and therefore `A2_YM`, contains NO aperture at all. `EvenAperture.A2_even`'s
  proof body never mentions its own argument: it is `MassGap.A2_continuum_of_congruence` on
  `freadYM ∘ Gram ∘ Fym`, which is the same term at every extent.
* `FullModel.measure` is a `LatticeYMFamily` FIELD, given a CLOSED TERM in every construction in the
  tree — `OSFamily.osFamilyTension ApertureRoute.βFlag` here and in `ApertureRoute`,
  `WilsonModel.ymFamilyTension` in the older `EvenAperture` and `WilsonModel` constructions — and
  `Measure.continuum_of_family` takes the family as DATA and no hypothesis. The continuum half never
  saw the aperture.
* `LatticeYM.hfloor` is `le_refl _`, independent of everything. `LatticeYM.hread` does mention the
  tension — it is `‖m β k‖ ≤ exp(-(κ₀ − μ β))` — but at `ymModelEven`'s field values `m` is that
  exponential cast to `ℂ`, so the proof is `Complex.norm_real` and `le_of_eq`: aperture-blind in
  SHAPE, and it survives any substitution for `μ` that leaves `m` its exponential.

So the aperture is fixed before `β` only because `apertureOf` was written that way, not because any
consumer demands it. Pushing the choice inside the binder — `apertureAt hc β = (hc β).choose` — gives
a function `ℝ → EvenAp` and every field above accepts it unchanged.

## AND THE CONCLUSION IS POINTWISE TOO

`ApertureRoute.FlagshipAt`'s gap side is `∀ β, Tendsto … (nhds 0)` and `∀ β, μ β − κ < 0`: both
quantify over `β` OUTERMOST, with nothing shared between couplings. Its measure side mentions `β`
nowhere. So the weaker hypothesis lands on the same conclusion with nothing to reconcile across
couplings, which is the whole reason this file is short.

**What is NOT concluded, at either hypothesis.** A gap rate uniform in the coupling. `FlagshipAt`
gives `0 < κ₀ − μ β` at each `β` separately, and so does this file. `UniformSurplus` below names the
missing premise and `uniform_gap_of_uniformSurplus` proves it SUFFICIENT for a coupling-uniform
geometric bound. Only that direction is proved; no converse is stated anywhere, so nothing here says
the premise is necessary.

`ConfinesAtAnAperture` does not supply it either: it is an inequality at each `β` with no modulus, so
a single extent still leaves `μEven a β` free to approach `κ₀`. That is a reading of the two
statements, not a theorem — no declaration in the tree computes `μEven a β` as `β → ∞`. The point
stands either way that this is not a COST OF THE SWAP: the premise is equally absent from both.

## THE ORDERING BETWEEN THE TWO HYPOTHESES

`confinesAtEachCoupling_of_confinesAtAnAperture` is the implication, and it is one-way.
`forall_exists_aperture_does_not_give_exists_forall` machine-checks that the converse is not
SCHEMATICALLY valid over `EvenAp × ℝ`, by exhibiting a predicate on which it fails. That is a
statement about the quantifier shape, not about `cosAvgEven`: whether the converse happens to hold
for this particular predicate is left open, and no declaration in the tree settles it.

**This is a different swap from the one `ContactDominance` refutes.**
`ContactDominance.aperture_uniformity_does_not_give_coupling_uniformity` is about the MOMENT BOUND
that feeds the substrate hypothesis: it refutes `(∀ β, ∃ B, ∀ N, …) → (∃ B, ∀ N β, …)`, where the
swapped quantifier is the BOUND `B` and the aperture `N` is UNIVERSAL on both sides. Its counterexample
is `sepRead`, a family CONSTRUCTED to meet the two clauses `wilson_reflection_positive_at` asserts —
so the refutation is of the implication, not of anything about `wilsonCorrAt`. Here the swapped
quantifier is the APERTURE itself and there is no `B` at all. Neither result bears on the other, and
in particular `ContactDominance`'s counterexample does not obstruct anything below — nothing in this
file tries to recover a uniform object from pointwise ones.

## Provenance

Sections 2, 3 and 5 are `EvenAperture`'s and `ApertureRoute`'s field values and proof terms,
transcribed with `apertureAt hc β` in place of the fixed `apertureOf hc`, and introduce no numeral.
Sections 4 and 6 are new: `forall_exists_aperture_does_not_give_exists_forall` and
`uniform_gap_of_uniformSurplus` have no antecedent in either file, and the first introduces the
numerals `2n+3`, `n+2` and `a.1 + 1`, all forced by `EvenAp`'s own `N + 1 = 2m ∧ 2 ≤ m` and derived at
that declaration. `#print axioms` after every declaration.
-/

namespace MassGap.ApertureFamily

open Filter
open scoped Matrix
open MassGap.EvenAperture
open MassGap.ApertureRoute

/-! ## 1. The hypothesis, swapped -/

/-- **CONFINEMENT AT EACH COUPLING.** At every coupling there is SOME even extent of at least four at
which the read's cosine average clears the entropy floor `3^{−1/4} = e^{−κ₀}`.

`ApertureRoute.ConfinesAtAnAperture` with the two quantifiers exchanged. The extent may move with the
coupling.

MOTIVATION, NOT DERIVATION: a read aperture held at a fixed physical scale is a growing number of
lattice sites as the lattice refines, so a coupling-dependent `EvenAp` is what a fixed physical
aperture looks like in lattice units. Nothing in this tree ties `β` to a lattice spacing —
`LatticeYM`'s `β` is the coupling and `FullModel` is explicitly NOT indexed by spacing
(`FullModel.mass_gap_rate_and_continuum`'s first caveat) — so that reading motivates the definition
and does not derive it. What is derived is everything below the definition.

The guard is `ConfinesAtAnAperture`'s, unchanged and for its reason: the condition is on the COSINE
AVERAGE and not on the tension, because `Real.log` is even and the bare tension form is satisfied by
a read with no decay at all (`ApertureRoute.unguarded_confinement_is_satisfiable_without_decay`).

DERIVED: no numeral. `EvenAp` and `3^{−1/4}` are `ConfinesAtAnAperture`'s, carried across the swap. -/
def ConfinesAtEachCoupling : Prop :=
  ∀ β : ℝ, ∃ a : EvenAp, (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β

#print axioms ConfinesAtEachCoupling

/-- The aperture the hypothesis supplies AT `β`. `ApertureRoute.apertureOf` with the
`Classical.choose` moved INSIDE the coupling binder — the whole of the difference between the two
hypotheses, as a term. -/
noncomputable def apertureAt (hc : ConfinesAtEachCoupling) (β : ℝ) : EvenAp := (hc β).choose

#print axioms apertureAt

/-- That aperture's read clears the floor at that coupling. -/
theorem apertureAt_cosAvg (hc : ConfinesAtEachCoupling) (β : ℝ) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven (apertureAt hc β) β := (hc β).choose_spec

#print axioms apertureAt_cosAvg

/-- **The choice made visible.** The hypothesis is equivalent to the existence of an APERTURE
FUNCTION `ℝ → EvenAp` clearing the floor at every coupling. Forward is `Classical.choice` and nothing
else; backward is projection. Stated so that the one place the swap spends choice is a theorem rather
than a step buried in `apertureAt`. -/
theorem confinesAtEachCoupling_iff_apertureFunction :
    ConfinesAtEachCoupling
      ↔ ∃ A : ℝ → EvenAp, ∀ β : ℝ, (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven (A β) β :=
  ⟨fun hc => ⟨apertureAt hc, apertureAt_cosAvg hc⟩, fun ⟨A, hA⟩ β => ⟨A β, hA β⟩⟩

#print axioms confinesAtEachCoupling_iff_apertureFunction

/-- **The tension along the aperture function.** This is the `LatticeYM.μ` field below, and it is the
one place the swap shows up in the model: `ApertureRoute` has `μEven (apertureOf hc)`, a fixed extent
applied to `β`; here the extent is read at `β` too. -/
noncomputable def tensionOf (hc : ConfinesAtEachCoupling) : ℝ → ℝ :=
  fun β => μEven (apertureAt hc β) β

#print axioms tensionOf

/-- **And therefore confines, at every coupling.** `Moment.Read.tension_lt_floor_of_cosAvg` applied
inside the binder — the guarded direction, which reads the logarithm only where its argument is
positive. This is the `A1_YM` field of the model below, and `A1` is pointwise in `β`, so the
per-coupling aperture discharges it exactly as a fixed one would. -/
theorem tensionOf_lt_floor (hc : ConfinesAtEachCoupling) (β : ℝ) :
    tensionOf hc β < MassGap.κ₀YM :=
  (readEven (apertureAt hc β) β).tension_lt_floor_of_cosAvg ((hc β).choose_spec)

#print axioms tensionOf_lt_floor

/-! ## 2. The model, the full model, and the realisation

`EvenAperture.ymModelEven` and `ApertureRoute.fullModelOfConfinement`, with `tensionOf hc` in place
of `μEven (apertureOf hc)` wherever that appears. -/

/-- **THE LATTICE YANG–MILLS WITNESS ALONG AN APERTURE FUNCTION.** `EvenAperture.ymModelEven` with
the tension read at the coupling's own extent.

`Idx`, `Dir`, `s`, `P`, `R`, `κ₀`, `κ`, `hfloor` are `ymModelEven`'s, character for character: none of
them mentions the aperture. `m`, `μ` and `hread` are `ymModelEven`'s with `μEven a` replaced by
`tensionOf hc` — three occurrences, and the only substitution this file makes. `hread`'s proof is
unchanged in shape because it never looks inside the tension: `Complex.norm_real` and
`Real.norm_of_nonneg` on `m`'s exponential, then `le_of_eq`.

DERIVED: as in `ymModelEven`, the `1` is the single mode's weight, forced by normalisation; nothing
else here carries a numeral. -/
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

/-- **A1 along the aperture function.** `∀ β, μ β < κ₀`, which is `tensionOf_lt_floor` unchanged:
`Apriori.A1` quantifies over `β` and asks nothing of the relation between different `β`. -/
theorem A1_family (hc : ConfinesAtEachCoupling) : MassGap.A1_YM (ymModelFamily hc) :=
  tensionOf_lt_floor hc

#print axioms A1_family

/-- **A2 is untouched by the swap, because `R` never carried an aperture.**
`EvenAperture.A2_even`'s statement is `A2_YM (ymModelEven a)`, and `A2_YM M` is `A2 M.R`; the `R`
fields of `ymModelEven a` and of `ymModelFamily hc` are the SAME TERM, so the instance at any extent
is the instance here. `apFour` — extent four, `EvenAperture.evenAp_nonempty`'s witness — is supplied
only because `A2_even` takes an argument its proof body never mentions; any `EvenAp` would do, and
which one is chosen has no effect on the term proved. -/
theorem A2_family (hc : ConfinesAtEachCoupling) : MassGap.A2_YM (ymModelFamily hc) :=
  MassGap.EvenAperture.A2_even MassGap.EvenAperture.apFour

#print axioms A2_family

/-- **A FULL MODEL FROM CONFINEMENT AT EACH COUPLING.** `ApertureRoute.fullModelOfConfinement` with
the per-coupling aperture. The measure field is the same closed term it carries —
`OSFamily.osFamilyTension ApertureRoute.βFlag`, the unclamped connected `SU(3)` correlation whose
sequence index is the lattice EXTENT; `ApertureRoute`'s module docstring states what that clause means
and what it still lacks.

DERIVED: no numeral; every constant belongs to the pieces assembled, and `βFlag` carries its own
note. -/
noncomputable def fullModelOfEachCoupling (hc : ConfinesAtEachCoupling) : MassGap.FullModel where
  gap := ymModelFamily hc
  h1 := A1_family hc
  h2 := A2_family hc
  measure := MassGap.OSFamily.osFamilyTension MassGap.ApertureRoute.βFlag

#print axioms fullModelOfEachCoupling

/-- **The measure side takes no hypothesis, by `rfl`.** The same closed term `ApertureRoute` uses. The
swap in the GAP-side hypothesis does not reach this field, which is the claim; the field itself is not
`WilsonModel.ymFamilyTension` any more — both this file and `ApertureRoute` now carry
`OSFamily.osFamilyTension`, and `ApertureRoute`'s module docstring states what that clause means and
what it still lacks. -/
theorem measure_is_osFamilyTension (hc : ConfinesAtEachCoupling) :
    (fullModelOfEachCoupling hc).measure
      = MassGap.OSFamily.osFamilyTension MassGap.ApertureRoute.βFlag := rfl

#print axioms measure_is_osFamilyTension

/-- **AN `SU(3)` WILSON REALISATION FROM CONFINEMENT AT EACH COUPLING.**
`ApertureRoute.wilsonOfConfinement`'s transcription. `WilsonModel.paramsTension` is reused unchanged:
it reads its infrared cutoff off the witness read, `paramsTension.irCutoff = cW`.

`paramsTension` IS aperture-dependent, and it is worth saying so rather than repeating that it is
not: `cW` contains `rW ^ (kW + 1)`, and `WilsonModel.kW` is itself `Classical.choose`n — some aperture
at which the WITNESS read `readW` (a geometric circle correlation, not the Wilson ensemble) clears the
entropy floor. That aperture is a bare `ℕ` belonging to the measure side's own witness. It is not an
`EvenAp`, it is not `apertureAt hc β`, and no field of this file's model reaches it — which is why the
swap cannot move it, and why `paramsTension` is reusable here verbatim.

DERIVED: no numeral of this declaration's; `3` is `SU(3)`'s rank, carried from `paramsTension`. -/
noncomputable def wilsonOfEachCoupling (hc : ConfinesAtEachCoupling) : MassGap.WilsonRealization where
  params := MassGap.WilsonModel.paramsTension
  model := fullModelOfEachCoupling hc
  hc := MassGap.WilsonModel.paramsTension_irCutoff.symm

#print axioms wilsonOfEachCoupling

/-! ## 3. The flagship, from the swapped hypothesis -/

/-- The flagship's conclusion at this file's realisation: the mass gap (`C(τ) → 0`), non-triviality
(`μ − κ < 0`), `SO(4)` invariance (`R` direction-independent), and the tight OS0–OS3 continuum limit.

Clause for clause `ApertureRoute.FlagshipAt`, about `wilsonOfEachCoupling hc` instead of
`wilsonOfConfinement hc`, so the two conclusions can be compared by reading rather than by assertion.

DERIVED: no magnitude appears. Every `0` is a sign or a limit point, the `4` is the dimension inside
the NAME `SO(4)`, and `c`, `B` are the measure's own fields. -/
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

/-- **THE FLAGSHIP FROM CONFINEMENT AT EACH COUPLING — THE WHOLE OF IT.**

Existence, the mass gap, non-triviality, `SO(4)` invariance and the continuum measure, from
`∀ β, ∃ a : EvenAp, 3^{−1/4} < cosAvgEven a β` alone. No conjunct is dropped and no extra premise is
taken.

`FlagshipAtEach` is `ApertureRoute.FlagshipAt`'s statement clause for clause, about
`wilsonOfEachCoupling hc` instead of `wilsonOfConfinement hc`. It is NOT the same proposition and
claiming so would be false: the two realisations' `μ` fields are `μEven ((hc β).choose) β` and
`μEven hc.choose β`, drawn by `Classical.choose` from different propositions, and they are not
definitionally equal. What is the same is the content — each is the flagship at its own model —
exactly as `ApertureRoute` records for its own transcription of `EvenAperture`'s.

The proof term is `existence_and_gap_of_wilson` applied to this file's realisation and nothing else,
exactly as `flagship_of_confinement_at_an_aperture`'s is — so the statement is known to be the
flagship by type-checking rather than by assertion. -/
theorem flagship_of_confinement_at_each_coupling (hc : ConfinesAtEachCoupling) : FlagshipAtEach hc :=
  MassGap.existence_and_gap_of_wilson (wilsonOfEachCoupling hc)

#print axioms flagship_of_confinement_at_each_coupling

/-- **The gap WITH ITS RATE, and the continuum measure, at each coupling.** The rate is the entropy
surplus `κ₀ − μ β` at THAT coupling's extent. `ApertureRoute.mass_gap_rate_and_continuum_at_an_aperture`
from the swapped hypothesis. -/
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

/-- **THE OLD HYPOTHESIS GIVES THE NEW ONE.** Instantiate the single extent at every coupling. This
is the whole proof, and it is what puts the swap on the record as a WEAKENING rather than a variant
spelling. -/
theorem confinesAtEachCoupling_of_confinesAtAnAperture (hc : ConfinesAtAnAperture) :
    ConfinesAtEachCoupling :=
  fun β => ⟨apertureOf hc, apertureOf_cosAvg hc β⟩

#print axioms confinesAtEachCoupling_of_confinesAtAnAperture

/-- **The flagship from the aperture hypothesis, through the swapped one.** Composing the two results
above reaches the flagship from `ConfinesAtAnAperture` by way of `ConfinesAtEachCoupling`, which is
the check that the swap costs nothing: every clause the `∃∀` route concludes is concluded here too,
from strictly less.

It lands on `FlagshipAtEach`, not on `ApertureRoute.FlagshipAt`, and those are different
propositions — the realisations differ in their `Classical.choose`n aperture. The clauses are
identical and the models are both flagship models; it is the witness that differs. -/
theorem flagship_of_confinesAtAnAperture_via_family (hc : ConfinesAtAnAperture) :
    FlagshipAtEach (confinesAtEachCoupling_of_confinesAtAnAperture hc) :=
  flagship_of_confinement_at_each_coupling _

#print axioms flagship_of_confinesAtAnAperture_via_family

/-- **NO SCHEMATIC CONVERSE.** Over `EvenAp` and `ℝ` the implication `(∀ β, ∃ a, P a β) →
(∃ a, ∀ β, P a β)` fails, so nothing about the quantifier shape alone recovers
`ConfinesAtAnAperture` from `ConfinesAtEachCoupling`.

The witness is `P a β := β ≤ a.1`. Forward: extents are unbounded — `⟨2n+3, n+2, …⟩` is an `EvenAp`
for every `n`, and `exists_nat_gt` puts one past any `β`. Backward: a single extent fails at
`β = a.1 + 1`.

**This does not refute the converse FOR `cosAvgEven`.** It says the converse is not available from
the logic, so anyone wanting `ConfinesAtAnAperture` back must argue from the Wilson read itself. No
declaration in the tree does, in either direction.

DERIVED: no magnitude. `2n+3` is the odd extent whose successor is `2(n+2)`, forced by `EvenAp`'s own
`N + 1 = 2m` with `2 ≤ m`; `a.1 + 1` is the successor, the smallest point past a given extent. -/
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

/-- **THE OBLIGATION, AT EACH COUPLING.** There is a `b > 0` such that the contact-relative quartic
law on `(b, ∞)` alone yields confinement at a per-coupling even aperture, and with it the gap,
non-triviality, `SO(4)` invariance and the continuum measure.

The `[0, b]` arm is discharged inside the proof by `ContactFloor.contact_relative_unconditional`,
carried out of `NonnegArm.lawBelow_holds`; `b` is that theorem's own cut, not named and not chosen.

This proves nothing new about Yang–Mills — `LawAbove b` is the same sufficient input. What has
changed is the intermediate target: a route reaching confinement without the power law now has to
produce ONE extent PER COUPLING, not one extent for all of them. -/
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

/-- **A COUPLING-UNIFORM ENTROPY SURPLUS.** The tension stays a fixed distance below the floor at
every coupling, rather than merely below it at each coupling.

This is what `A1` does NOT say. `Apriori.A1 μ κ₀` is `∀ β, μ β < κ₀`, which permits `μ β → κ₀`, and
the model's mode magnitude `exp(−(κ₀ − μ β))` then approaches `1` — geometric decay at every coupling,
with no common ratio.

DERIVED: `Δ` is quantified, not chosen; `0 < Δ` is a sign. -/
def UniformSurplus (μ : ℝ → ℝ) : Prop := ∃ Δ : ℝ, 0 < Δ ∧ ∀ β : ℝ, Δ ≤ MassGap.κ₀YM - μ β

#print axioms UniformSurplus

/-- **THE COUPLING-UNIFORM GEOMETRIC BOUND, FROM THE UNIFORM SURPLUS AND NOT WITHOUT IT.** One rate
`Δ > 0` and one bound `‖C(τ)‖ ≤ (∑‖P‖)·e^{−Δτ}` holding at EVERY coupling.

`Model.geometric_bound_of_mode_bound` at the ratio `e^{−Δ}`; the hypothesis enters only through
`Real.exp_le_exp`, so the rate delivered IS the surplus's constant.

Stated over `ymModelFamily hc` because that is this file's model, but nothing in the proof uses the
aperture function: the same statement with `ApertureRoute.fullModelOfConfinement`'s tension needs the
same premise. The swap neither supplies nor costs it. -/
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
