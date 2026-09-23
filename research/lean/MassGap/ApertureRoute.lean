import MassGap.NonnegArm
import MassGap.OSFamily

/-!
# MassGap.ApertureRoute — the flagship assembled from confinement at one even aperture

`EvenAperture.existence_and_gap_of_substrate_even` consumes a moment bound quantified over every even
aperture, `∃ B, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B`. This file rebuilds the same conclusion from
a weaker hypothesis, `ConfinesAtAnAperture`, and records the one-way implication between the two.

## What the hypothesis is

`cosAvgEven a β` is `∑ d, (readEven a β).p d * cos ((readEven a β).θ d)`, and

    ConfinesAtAnAperture := ∃ a : EvenAp, ∀ β : ℝ, 3 ^ (-(1 : ℝ) / 4) < cosAvgEven a β

— one even extent at which the read's cosine average stays above `e ^ (-κ₀YM)` at every coupling,
with the aperture quantified outside the coupling quantifier.

The condition is on the cosine average and not on the tension. `Moment.Read.tension` is
`-Real.log (∑ d, p d * cos (θ d))` and `Real.log` takes the logarithm of the absolute value, so a
read with cosine average `-1` has tension `0`, which is below `κ₀YM`.
`unguarded_confinement_is_satisfiable_without_decay` exhibits exactly that on
`Substrate.antipodeRead`, whose mass sits at the antipode. `confines_iff_pos_and_tension_lt_floor`
shows the stated form is equivalent to the conjunction of `0 < cosAvgEven a β` with
`μEven a β < κ₀YM`, the positivity being the hypothesis
`Moment.Read.cosAvg_gt_of_tension_lt_floor` carries.

## What is built from it

`apertureOf hc` is the chosen extent and `apertureOf_confines` the tension bound at it.
`fullModelOfConfinement hc` is a `MassGap.FullModel` with gap side `ymModelEven (apertureOf hc)` and
measure side `OSFamily.osFamilyTension βFlag`; `wilsonOfConfinement hc` wraps it with
`WilsonModel.paramsTension`. `FlagshipAt hc` names the conclusion and
`flagship_of_confinement_at_an_aperture` proves it by `MassGap.existence_and_gap_of_wilson`.
`mass_gap_rate_and_continuum_at_an_aperture` is the rate form.

`confinement_at_an_aperture_of_substrate` derives `ConfinesAtAnAperture` from the substrate bound —
it is `EvenAperture.exists_confining_even_aperture`'s argument stopped one step earlier, at the
intermediate `3 ^ (-(1:ℝ)/4) < cosAvgEven a β` that `Moment.Read.tension_lt_floor_of_circ_moment`
establishes and then discards. `flagship_of_substrate_even_via_aperture` composes the two.
`unguarded_of_confinesAtAnAperture` gives the unguarded tension form from the guarded one.

## The measure side

`fullModelOfConfinement`'s measure field is `OSFamily.osFamilyTension βFlag`, and
`OSFamily.osFamilyTension_Q_eq` states its reflected form exactly:

    (osFamilyTension β).Q j a = WilsonBridge.corrClay (OSFamily.extent a) β (OSFamily.lagOf a j.2.2)

with `OSFamily.extent a = 2 * a + 2`, strictly monotone. So the sequence index is the extent of a
four-dimensional periodic `SU(3)` lattice, the coupling is held at `βFlag` across the sequence, and
the value is the connected Wilson plaquette correlation with no clamp. `0 ≤ q j` descends from
`ReflectionStrong.corrClay_nonneg_even_lag` and the bound `B = 4` from
`InfiniteVolume.wilsonCorrConn_abs_le_four`. `measure_Q_eq`, `measure_Na_tendsto` and `measure_c`
record the three fields at this file's model.

## Scope

* The implication runs one way. The substrate bound gives `ConfinesAtAnAperture`; a witness for
  `ConfinesAtAnAperture` constrains one extent and says nothing about any other, so no converse is
  stated.
* No declaration here establishes confinement at any aperture. `ConfinesAtAnAperture` is a hypothesis
  in every theorem that uses it.
* The continuum clause is a limit in the volume at fixed coupling: nothing sends the lattice spacing
  to zero, `β` is fixed at `βFlag`, and no asymptotic-scaling relation appears in this tree.
  `Measure.continuum_of_family` extracts a subsequence and a pointwise limit `q : J → ℝ` by
  Bolzano–Weierstrass on a countable product; there is no uniqueness, no measure on `ℝ⁴` and no
  reconstruction.
* The two invariance clauses are about components the reflected form does not read.
  `OSFamily.actEOS` multiplies `j.1` and `actPOS` multiplies `j.2.1`, while
  `OSFamily.Qos_depends_only_on_the_lag` shows the form reads `j` through `j.2.2` alone.
* The published bound `|q j| ≤ ⌈c⌉₊ * B` carries the factor `⌈WilsonModel.cW⌉₊`, which comes from
  `OSFamily.hcount_wOne` counting the single-mode spectrum `WilsonModel.wOne` against the circle read
  `WilsonModel.readW` at the `Classical.choose`n aperture `WilsonModel.kW`; nothing in that factor is
  about `SU(3)`, and `kW` is not bounded in this tree. `OSFamily.Qos_abs_le_four` gives
  `|Q j a| ≤ 4` at every member directly.
* `os_gap` comes from `Measure.familyOfSortedCount` applied to `hsorted` and `hcount`, both facts
  about `wOne`; the `SU(3)` lattice contributes `0 < Nmodes a`.
* The family is not known to be positive at every test configuration, as
  `GibbsPositive.ymFamilyGauge_Q_pos` is for the clamped family; `OSFamily.Qos_pos_at_lag_zero` gives
  strict positivity at lag zero, from `PlaqVariance.corrClay_zero_pos`.
* `Measure.LatticeYMFamily` has no field for OS2 as positive semidefiniteness over the half-space
  algebra, and none for OS4 clustering. The tree's Gram statements (`OSPositivity`,
  `ReflectionStrong.wilson_expect_gram_nonneg`) are at finite volume on the slab and are not composed
  with this family.
* `ymModelEven` has `Idx := Unit` and `m β _ := exp (-(κ₀ - μEven a β))` — one mode, with its
  magnitude equal to its own bound, so the `hread` field is `le_of_eq`. The mode count is structural
  in the model. `Complete.WilsonSpectral` is the corresponding statement about the ensemble;
  `SlabQuadratic.wilsonSpectral` proves it at `N = 3` for `0 ≤ β`, and
  `SpectralFour.fourRepresentable_const` shows the constant triple is representable, so that property
  carries no rate.
* The gap clause is about `ymModelEven`'s constructed spectrum and the continuum clause about `q`;
  the two are not composed, and `FullModel`'s own docstring records that `Δ` is a rate at one
  spacing.

## Provenance

Every declaration below is `EvenAperture`'s, transcribed against `ConfinesAtAnAperture` in place of
the substrate bound, and `#print axioms` follows each. The gap side reports the foundational three
and no named axiom, because `readEven` is built from `Complete.wilson_reflection_positive_at_even`.
-/

namespace MassGap.ApertureRoute

open Filter
open MassGap.EvenAperture

/-! ## 1. The hypothesis, named

`ConfinesAtAnAperture` is the `Prop` every theorem below consumes, in place of the substrate bound.
It is stated separately so the difference between the two is a declaration rather than a remark. -/

/-- `∑ d, (readEven a β).p d * Real.cos ((readEven a β).θ d)`: the cosine average of the clamped
even-aperture read, which is the scalar `Moment.Read.tension` takes the negative logarithm of. It is
`Complete.cosAvgYMAt` with `readEven` in place of `readYMAt`.

DERIVED: no numeral appears in the statement. -/
noncomputable def cosAvgEven (a : EvenAp) (β : ℝ) : ℝ :=
  ∑ d, (readEven a β).p d * Real.cos ((readEven a β).θ d)

#print axioms cosAvgEven

/-- The proposition `∃ a : EvenAp, ∀ β : ℝ, 3 ^ (-(1 : ℝ) / 4) < cosAvgEven a β`: there is an even
extent at which the read's cosine average stays strictly above `3 ^ (-(1:ℝ)/4) = exp (-κ₀YM)` at
every coupling. The aperture is quantified outside the coupling quantifier, so one extent must work
rather than all of them.

Scope, and it is why the condition is on the cosine average rather than on the tension:
`Moment.Read.tension` is `-Real.log (∑ d, p d * cos (θ d))`, and `Real.log` takes the logarithm of
the absolute value (`Real.log_abs`, `Real.log_neg_eq_log`), so a read with cosine average `-1` has
tension `0`, below `κ₀YM`, and satisfies `∀ β, μEven a β < κ₀YM`.
`Substrate.antipodeRead k` is such a read — all its mass at the antipode, where `θ = π` — and it is
the read `Substrate.antipodeRead_moment_eq_quarter_sq` and
`Substrate.rp_alone_leaves_moment_unbounded` are stated about.
`unguarded_confinement_is_satisfiable_without_decay` proves the three facts together below.

`confines_iff_pos_and_tension_lt_floor` shows this form is equivalent to
`0 < cosAvgEven a β ∧ μEven a β < κ₀YM`, the positivity being the hypothesis
`Moment.Read.cosAvg_gt_of_tension_lt_floor` carries. It is written as the single inequality because
that is also the intermediate `Moment.Read.tension_lt_floor_of_circ_moment`'s argument passes
through, so `confinement_at_an_aperture_of_substrate` reaches it directly.

DERIVED: `3` is the base of the floor `3 ^ (-(1:ℝ)/4)`, the directed cube-path branching count of
`Floor.lean`; `1` and `4` are the numerator and root of its exponent, matching `κ₀YM = (1/4) log 3`.
`EvenAp`'s own `4 ≤ N + 1` and `Even (N + 1)` are inside that type, read off
`Complete.wilson_reflection_positive_at_even`'s hypotheses. -/
def ConfinesAtAnAperture : Prop :=
  ∃ a : EvenAp, ∀ β : ℝ, (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β

#print axioms ConfinesAtAnAperture

/-- `hc.choose`: the `EvenAp` the hypothesis supplies. As in `EvenAperture.apertureEven`, no value is
named — the extent is whatever `Classical.choose` draws from the existential, so two proofs of
`ConfinesAtAnAperture` need not give the same one.

DERIVED: no numeral appears in the statement. -/
noncomputable def apertureOf (hc : ConfinesAtAnAperture) : EvenAp := hc.choose

#print axioms apertureOf

/-- `∀ β : ℝ, 3 ^ (-(1 : ℝ) / 4) < cosAvgEven (apertureOf hc) β`, which is `hc.choose_spec`: the
chosen aperture is one at which the cosine average clears the floor at every coupling.

DERIVED: `3` is the base of the floor, the directed cube-path branching count; `1` and `4` are the
numerator and root of its exponent. -/
theorem apertureOf_cosAvg (hc : ConfinesAtAnAperture) :
    ∀ β : ℝ, (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven (apertureOf hc) β := hc.choose_spec

#print axioms apertureOf_cosAvg

/-- `∀ β : ℝ, μEven (apertureOf hc) β < κ₀YM`: at the chosen aperture the tension is below the
floor at every coupling. It is `Moment.Read.tension_lt_floor_of_cosAvg` applied to
`apertureOf_cosAvg`, the direction that reads the logarithm only where its argument is positive.
This is the `A1_YM` field of `fullModelOfConfinement`.

DERIVED: no numeral appears in the statement; `κ₀YM` is a named constant. -/
theorem apertureOf_confines (hc : ConfinesAtAnAperture) :
    ∀ β : ℝ, μEven (apertureOf hc) β < MassGap.κ₀YM :=
  fun β => (readEven (apertureOf hc) β).tension_lt_floor_of_cosAvg (hc.choose_spec β)

#print axioms apertureOf_confines

/-- `3 ^ (-(1 : ℝ) / 4) < cosAvgEven a β ↔ (0 < cosAvgEven a β ∧ μEven a β < κ₀YM)` at every even
aperture and every coupling. Forward: `Real.rpow_pos_of_pos` gives `0 < 3 ^ (-(1:ℝ)/4)`, whence the
positivity, and `Moment.Read.tension_lt_floor_of_cosAvg` the tension bound. Backward:
`Moment.Read.cosAvg_gt_of_tension_lt_floor`, whose positivity hypothesis is the first conjunct.

So the two spellings carry the same content, and the difference from the tension bound alone is
exactly the positivity conjunct.

DERIVED: `3` is the base of the floor and `1`, `4` the numerator and root of its exponent; `0` is the
lower bound in the positivity conjunct, which is what makes the logarithm in `μEven` a logarithm of a
positive number. -/
theorem confines_iff_pos_and_tension_lt_floor (a : EvenAp) (β : ℝ) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β
      ↔ (0 < cosAvgEven a β ∧ μEven a β < MassGap.κ₀YM) := by
  constructor
  · intro h
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
    exact ⟨lt_trans h3 h, (readEven a β).tension_lt_floor_of_cosAvg h⟩
  · rintro ⟨hpos, htens⟩
    exact (readEven a β).cosAvg_gt_of_tension_lt_floor hpos htens

#print axioms confines_iff_pos_and_tension_lt_floor

/-! ## 2. The model, the full model, and the realisation

`EvenAperture.fullModelEven` and `EvenAperture.wilsonEven` with `apertureOf hc` in place of
`apertureEven h`, and `OSFamily.osFamilyTension βFlag` in place of `WilsonModel.ymFamilyTension` on
the measure side. `ymModelEven` and `A2_even` are reused unchanged; neither mentions the substrate
bound. -/

/-- The real `1`, used as the coupling at which the flagship's measure family is read.
`OSFamily.osFamilyTension` holds one coupling fixed across its sequence of extents, and a
`MassGap.FullModel` carries a single `LatticeYMFamily` with no coupling quantifier, so a value must
be named.

CHOSEN: `1`. Nothing concluded below depends on the value — `OSFamily.Qos_nonneg`,
`Qos_abs_le_four`, `Qos_actE` and `Qos_actP` are each `∀ β`, and `OSFamily.os_continuum_tension`
states the continuum clause at an arbitrary `β`. What the value fixes is which coupling's correlation
the limit `q` is a limit of. At `β = 0` the connected correlation vanishes at every nonzero lag
(`PowerTail.corrClay_at_zero_coupling`), so `q` would be zero away from lag zero; `1` is a value at
which no such collapse is proved. It is not claimed to be physically distinguished, and it lies in
the strong-coupling region rather than near the couplings a continuum study uses.

DERIVED: `1` is the chosen value itself. -/
noncomputable def βFlag : ℝ := 1

#print axioms βFlag

/-- A `MassGap.FullModel` with `gap := ymModelEven (apertureOf hc)`, `h1 := apertureOf_confines hc`,
`h2 := A2_even (apertureOf hc)` and `measure := OSFamily.osFamilyTension βFlag`.

It is `EvenAperture.fullModelEven` with the confinement witness supplying the aperture directly
rather than through `exists_confining_even_aperture`, and with the measure field changed. That change
makes the sequence index the lattice extent rather than the coupling, so the volume diverges along
it, and removes the clamp from the reflected form; `measure_Q_eq` states the resulting form.

DERIVED: no numeral appears in the statement. `βFlag` carries its own note and the remaining
constants belong to the assembled pieces. -/
noncomputable def fullModelOfConfinement (hc : ConfinesAtAnAperture) : MassGap.FullModel where
  gap := ymModelEven (apertureOf hc)
  h1 := apertureOf_confines hc
  h2 := A2_even (apertureOf hc)
  measure := MassGap.OSFamily.osFamilyTension βFlag

#print axioms fullModelOfConfinement

/-- `(fullModelOfConfinement hc).measure = OSFamily.osFamilyTension βFlag`, by `rfl`: the measure
field is a closed term and the hypothesis `hc` does not reach it. So the measure half of the
conclusion is the same whatever `hc` is.

DERIVED: no numeral appears in the statement. -/
theorem measure_is_osFamilyTension (hc : ConfinesAtAnAperture) :
    (fullModelOfConfinement hc).measure = MassGap.OSFamily.osFamilyTension βFlag := rfl

#print axioms measure_is_osFamilyTension

/-- `(fullModelOfConfinement hc).measure.Q j a = WilsonBridge.corrClay (OSFamily.extent a) βFlag (OSFamily.lagOf a j.2.2)`,
by `OSFamily.osFamilyTension_Q_eq`. The reflected form the continuum clause converges is the
connected Wilson plaquette correlation at extent `OSFamily.extent a` and coupling `βFlag`, with no
clamp, so the sequence index is the geometry.

DERIVED: no numeral appears in the statement; `OSFamily.extent` and `OSFamily.lagOf` carry their own,
and `.2.2` is projection notation. -/
theorem measure_Q_eq (hc : ConfinesAtAnAperture) (j : MassGap.OSFamily.JOS) (a : ℕ) :
    (fullModelOfConfinement hc).measure.Q j a
      = MassGap.WilsonBridge.corrClay (MassGap.OSFamily.extent a) βFlag
          (MassGap.OSFamily.lagOf a j.2.2) :=
  MassGap.OSFamily.osFamilyTension_Q_eq βFlag j a

#print axioms measure_Q_eq

/-- `Tendsto (fun a : ℕ => ((fullModelOfConfinement hc).measure.Na a : ℝ)) atTop atTop`, by
`OSFamily.Nmodes_tendsto_volume`: the family's mode-count field is the plaquette count of the
extent-`OSFamily.extent a` lattice, and it diverges.

Scope: `Na` is inert in the family's content — `WilsonModel.resolvedDim_wOne` returns `1` at every
positive count and `count_le_of_tension_uniform`'s bound contains no `Na` — so substituting
`WilsonGauge.NaG a = a + 1` would give the identical family. What makes the index a volume index is
`OSFamily.extent` inside the reflected form, which `measure_Q_eq` states.

DERIVED: no numeral appears in the statement. -/
theorem measure_Na_tendsto (hc : ConfinesAtAnAperture) :
    Tendsto (fun a : ℕ => (((fullModelOfConfinement hc).measure.Na a : ℕ) : ℝ)) atTop atTop :=
  MassGap.OSFamily.Nmodes_tendsto_volume

#print axioms measure_Na_tendsto

/-- `(fullModelOfConfinement hc).measure.c = WilsonModel.cW`, by `rfl`. This is what lets
`wilsonOfConfinement` reuse `WilsonModel.paramsTension` unchanged and discharge
`WilsonRealization.hc` with `WilsonModel.paramsTension_irCutoff`.

DERIVED: no numeral appears in the statement; `WilsonModel.cW` carries its own. -/
theorem measure_c (hc : ConfinesAtAnAperture) :
    (fullModelOfConfinement hc).measure.c = MassGap.WilsonModel.cW := rfl

#print axioms measure_c

/-- A `MassGap.WilsonRealization` with `params := WilsonModel.paramsTension`,
`model := fullModelOfConfinement hc` and `hc := WilsonModel.paramsTension_irCutoff.symm`. It is
`EvenAperture.wilsonEven` transcribed against this file's model.

Scope: `WilsonModel.paramsTension` reads its infrared cutoff off the witness read. That cutoff
contains an aperture — `kstar = 2 * π * cW`, and `cW` carries `rW ^ (kW + 1)` with `kW` a
`Classical.choose`n extent — but it is a bare `ℕ` on the measure side, fixed by the witness read and
unrelated to the `EvenAp` the gap side quantifies over.

DERIVED: no numeral appears in the statement; the rank `3` is inside `paramsTension`. -/
noncomputable def wilsonOfConfinement (hc : ConfinesAtAnAperture) : MassGap.WilsonRealization where
  params := MassGap.WilsonModel.paramsTension
  model := fullModelOfConfinement hc
  hc := MassGap.WilsonModel.paramsTension_irCutoff.symm

#print axioms wilsonOfConfinement

/-! ## 3. The conclusion, named and proved -/

/-- The conclusion at `wilsonOfConfinement hc`, as a `Prop`, conjoining two groups.

Gap side: the mode sum `‖∑ k ∈ gap.s β, gap.P β k * (gap.m β k) ^ τ‖` tends to `0` as `τ → atTop` at
every coupling; `gap.μ β - gap.κ < 0` at every coupling; and `gap.R` is constant in the direction.

Measure side: a limit `q` on `measure.J` and a strictly monotone `φ` with `measure.Q j (φ k) → q j`
at every `j`, with `|q j| ≤ ⌈measure.c⌉₊ * measure.B`, `0 ≤ q j`, and `q` invariant under
`measure.actE` and `measure.actP`.

Stated in the shape `NonnegArm.Flagship` uses, so `flagship_of_confinement_at_an_aperture` is
faithful by type-checking. It is not the same proposition as `NonnegArm.Flagship h`, whose measure is
`WilsonModel.ymFamilyTension` (`NonnegArm.measure_is_ymFamilyTension`, by `rfl`): the four
measure-half clauses here quantify over a different `J`, a different `Q`, a different `B`
(`OSFamily.osFamilyTension_B` is `4`, `WilsonModel.family_B` is `1`) and a different sequence
(extents rather than couplings). The gap-half clauses are unchanged.

DERIVED: `0` occurs three times — the limit point of the mode sum, the comparison point in
`gap.μ β - gap.κ < 0`, and the lower bound on each `q j`. No other numeral appears; `c` and `B` are
the measure's own fields, and the `4` of `SO(4)` is part of a name, not of the statement. -/
def FlagshipAt (hc : ConfinesAtAnAperture) : Prop :=
  ((∀ β, Tendsto (fun τ : ℕ => ‖∑ k ∈ (wilsonOfConfinement hc).model.gap.s β,
        (wilsonOfConfinement hc).model.gap.P β k
          * ((wilsonOfConfinement hc).model.gap.m β k) ^ τ‖) atTop (nhds 0)) ∧
      (∀ β, (wilsonOfConfinement hc).model.gap.μ β
          - (wilsonOfConfinement hc).model.gap.κ < 0) ∧
      (∀ d d', (wilsonOfConfinement hc).model.gap.R d
          = (wilsonOfConfinement hc).model.gap.R d')) ∧
    (∃ (q : (wilsonOfConfinement hc).model.measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ j, Tendsto (fun k => (wilsonOfConfinement hc).model.measure.Q j (φ k)) atTop (nhds (q j))) ∧
      (∀ j, |q j| ≤ (⌈(wilsonOfConfinement hc).model.measure.c⌉₊ : ℝ)
              * (wilsonOfConfinement hc).model.measure.B) ∧
      (∀ j, 0 ≤ q j) ∧
      (∀ g j, q ((wilsonOfConfinement hc).model.measure.actE g j) = q j) ∧
      (∀ σ j, q ((wilsonOfConfinement hc).model.measure.actP σ j) = q j))

#print axioms FlagshipAt

/-- `FlagshipAt hc` from `ConfinesAtAnAperture` alone, as
`MassGap.existence_and_gap_of_wilson (wilsonOfConfinement hc)`. No moment bound and no quantifier
over apertures appears in the hypothesis.

Scope: the hypothesis is the guarded form `∃ a : EvenAp, ∀ β, 3 ^ (-(1:ℝ)/4) < cosAvgEven a β`, not
`∀ β, μEven a β < κ₀YM`, which `unguarded_confinement_is_satisfiable_without_decay` shows is
satisfied by a read with cosine average `-1`.

DERIVED: no numeral appears in the statement; the constants are inside `ConfinesAtAnAperture` and
`FlagshipAt`. -/
theorem flagship_of_confinement_at_an_aperture (hc : ConfinesAtAnAperture) : FlagshipAt hc :=
  MassGap.existence_and_gap_of_wilson (wilsonOfConfinement hc)

#print axioms flagship_of_confinement_at_an_aperture

/-- `MassGap.mass_gap_rate_and_continuum` at `fullModelOfConfinement hc`: at each coupling `β`, the
surplus `0 < gap.κ₀ - gap.μ β`, the geometric bound
`‖∑ k ∈ gap.s β, gap.P β k * (gap.m β k) ^ τ‖ ≤ (∑ k ∈ gap.s β, ‖gap.P β k‖) * exp (-(gap.κ₀ - gap.μ β)) ^ τ`
at every `τ`, and the same measure-side conclusion as `FlagshipAt`.

The rate is the surplus `κ₀ - μ` at the chosen aperture, so it is a rate at one spacing.

DERIVED: `0` occurs twice — the strict lower bound on the surplus, and the lower bound on each
`q j`. -/
theorem mass_gap_rate_and_continuum_at_an_aperture (hc : ConfinesAtAnAperture) (β : ℝ) :
    (0 < (fullModelOfConfinement hc).gap.κ₀ - (fullModelOfConfinement hc).gap.μ β ∧
      ∀ τ : ℕ, ‖∑ k ∈ (fullModelOfConfinement hc).gap.s β,
          (fullModelOfConfinement hc).gap.P β k * ((fullModelOfConfinement hc).gap.m β k) ^ τ‖
        ≤ (∑ k ∈ (fullModelOfConfinement hc).gap.s β,
              ‖(fullModelOfConfinement hc).gap.P β k‖)
            * Real.exp (-((fullModelOfConfinement hc).gap.κ₀
                - (fullModelOfConfinement hc).gap.μ β)) ^ τ) ∧
      (∃ (q : (fullModelOfConfinement hc).measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ j, Tendsto (fun k => (fullModelOfConfinement hc).measure.Q j (φ k)) atTop (nhds (q j))) ∧
        (∀ j, |q j| ≤ (⌈(fullModelOfConfinement hc).measure.c⌉₊ : ℝ)
                * (fullModelOfConfinement hc).measure.B) ∧
        (∀ j, 0 ≤ q j) ∧
        (∀ g j, q ((fullModelOfConfinement hc).measure.actE g j) = q j) ∧
        (∀ σ j, q ((fullModelOfConfinement hc).measure.actP σ j) = q j)) :=
  MassGap.mass_gap_rate_and_continuum (fullModelOfConfinement hc) β

#print axioms mass_gap_rate_and_continuum_at_an_aperture

/-! ## 4. The substrate bound implies `ConfinesAtAnAperture`

One direction only; no converse is stated. -/

/-- `ConfinesAtAnAperture` from `∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B`.

The proof is `EvenAperture.exists_confining_even_aperture`'s with the conclusion taken one step
earlier. `Moment.aperture_factor_tendsto_zero` makes
`(2 * π / (N + 1)) ^ 2 * B / 2 < 1 - 3 ^ (-(1:ℝ)/4)` eventual in the extent,
`exists_evenAp_of_eventually` picks an aperture satisfying it, and `Moment.Read.cos_avg_ge_circ` —
the quadratic lower bound on the cosine average in terms of the circular second moment — closes it
there.

Scope: the substrate bound's aperture quantifier is spent choosing the aperture and is not used
again. No converse is stated: `ConfinesAtAnAperture` is about one extent and constrains no other.
The positivity guard is not an extra assumption — it is the intermediate this argument already
establishes on its way to the tension bound.

DERIVED: no numeral appears in the statement. The `2`, `1`, `3` and `4` of the window condition and
the floor live in the proof. -/
theorem confinement_at_an_aperture_of_substrate
    (h : ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B) : ConfinesAtAnAperture := by
  obtain ⟨B, hB⟩ := h
  have hev : ∀ᶠ N : ℕ in atTop,
      (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) :=
    (Moment.aperture_factor_tendsto_zero B).eventually_lt_const Moment.floor_rhs_pos
  obtain ⟨a, ha⟩ := exists_evenAp_of_eventually hev
  refine ⟨a, fun β => ?_⟩
  have hd2 : d2Even a β
      = ∑ d, (readEven a β).p d * (Moment.circLag d : ℝ) ^ 2 := rfl
  have hmul : (2 * Real.pi / ((a.1 : ℝ) + 1)) ^ 2
        * (∑ d, (readEven a β).p d * (Moment.circLag d : ℝ) ^ 2)
      ≤ (2 * Real.pi / ((a.1 : ℝ) + 1)) ^ 2 * B := by
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [← hd2]; exact hB a β
  have hge := (readEven a β).cos_avg_ge_circ
  show (3 : ℝ) ^ (-(1 : ℝ) / 4) < ∑ d, (readEven a β).p d * Real.cos ((readEven a β).θ d)
  linarith

#print axioms confinement_at_an_aperture_of_substrate

/-- `FlagshipAt (confinement_at_an_aperture_of_substrate h)`: the composition of
`confinement_at_an_aperture_of_substrate` with `flagship_of_confinement_at_an_aperture`, so the
substrate bound still yields the conclusion through the weaker intermediate.

DERIVED: no numeral appears in the statement. -/
theorem flagship_of_substrate_even_via_aperture
    (h : ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B) :
    FlagshipAt (confinement_at_an_aperture_of_substrate h) :=
  flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_substrate_even_via_aperture

/-! ### `FlagshipAt` and `NonnegArm.Flagship` are different propositions

`FlagshipAt (confinement_at_an_aperture_of_substrate h)` is not `NonnegArm.Flagship h`, for two
reasons. `ConfinesAtAnAperture` is an existential over `3 ^ (-(1:ℝ)/4) < cosAvgEven a β` rather than
over `μEven a β < κ₀YM`, so `apertureOf` draws its witness by `Classical.choose` from a different
proposition and the two constructions need not pick the same extent. And the measure field of
`fullModelOfConfinement` is `OSFamily.osFamilyTension βFlag` while `NonnegArm.wilsonEven`'s is
`WilsonModel.ymFamilyTension`, so the two differ in the measure half's `J`, `Q`, `B` and sequence.

`flagship_of_substrate_even_via_aperture` is the implication from the substrate bound to this file's
conclusion, as a theorem rather than an identity. -/

/-- `∃ a : EvenAp, ∀ β : ℝ, μEven a β < κ₀YM` from `ConfinesAtAnAperture`, witnessed by
`apertureOf hc` and `apertureOf_confines hc`: an aperture clearing the floor also has tension below
it.

Scope: one direction. The converse does not hold —
`unguarded_confinement_is_satisfiable_without_decay` exhibits a read satisfying the unguarded form
with cosine average `-1`.

DERIVED: no numeral appears in the statement; `κ₀YM` is a named constant. -/
theorem unguarded_of_confinesAtAnAperture (hc : ConfinesAtAnAperture) :
    ∃ a : EvenAp, ∀ β : ℝ, μEven a β < MassGap.κ₀YM :=
  ⟨apertureOf hc, apertureOf_confines hc⟩

#print axioms unguarded_of_confinesAtAnAperture

/-! ## 5. The same reduction, landing on `ConfinesAtAnAperture`

`NonnegArm.existence_and_gap_of_law_above_cut` reduces the conclusion to `NonnegArm.LawAbove b` — the
contact-relative quartic law above a cut — by discharging the `[0, b]` arm from
`ContactFloor.contact_relative_unconditional`. That composition is reused here with
`ConfinesAtAnAperture` as the intermediate. -/

/-- There exists `b > 0` such that `NonnegArm.LawAbove b` implies `∃ hc : ConfinesAtAnAperture, FlagshipAt hc`.

`b` comes from `NonnegArm.lawBelow_holds`, which also supplies the `[0, b]` arm from
`ContactFloor.contact_relative_unconditional`, so that arm is not a hypothesis. The two arms feed
`NonnegArm.substrate_even_of_two_arm`, then `confinement_at_an_aperture_of_substrate` and
`flagship_of_confinement_at_an_aperture`.

Scope: `LawAbove b` is the hypothesis, unchanged from `NonnegArm`'s reduction; `b` is that theorem's
own cut and is not named here. What differs is the intermediate, which is now confinement at one
extent rather than a moment bound at every extent.

DERIVED: `0` is the strict lower bound on the cut `b`. -/
theorem confinement_at_an_aperture_of_law_above_cut :
    ∃ b : ℝ, 0 < b ∧ (MassGap.NonnegArm.LawAbove b →
      ∃ hc : ConfinesAtAnAperture, FlagshipAt hc) := by
  obtain ⟨b, hbpos, hbelow⟩ := MassGap.NonnegArm.lawBelow_holds
  refine ⟨b, hbpos, fun habove => ?_⟩
  exact ⟨confinement_at_an_aperture_of_substrate
      (MassGap.NonnegArm.substrate_even_of_two_arm b hbelow habove),
    flagship_of_confinement_at_an_aperture _⟩

#print axioms confinement_at_an_aperture_of_law_above_cut

/-! ## 6. The type quantified over is inhabited

`ConfinesAtAnAperture` quantifies over `EvenAp`, which `EvenAperture.apFour` inhabits at extent four.
So the existential is not over an empty type. -/

/-- `Nonempty EvenAp`, restated from `EvenAperture.evenAp_nonempty` where the hypothesis is used. The
existential in `ConfinesAtAnAperture` therefore ranges over an inhabited type.

DERIVED: no numeral appears in the statement. -/
theorem evenAp_nonempty : Nonempty EvenAp := MassGap.EvenAperture.evenAp_nonempty

#print axioms evenAp_nonempty

/-! ## 6b. A read satisfying the unguarded form and failing the guarded one

`Substrate.antipodeRead k` places all its mass at the antipode, where `θ = π`, so its cosine average
is `-1` and its tension is `-Real.log |-1| = 0`, which is below `κ₀YM`. It is the read
`Substrate.antipodeRead_moment_eq_quarter_sq` and `Substrate.rp_alone_leaves_moment_unbounded` are
stated about.

The three theorems below compute its angle, its cosine average, and the three facts together: it
satisfies `μ < κ₀YM`, has cosine average `-1`, and does not clear `3 ^ (-(1:ℝ)/4)`. -/

/-- `(Substrate.antipodeRead k).θ (Substrate.antipode k) = Real.pi`. The angle is
`2 * π * (k + 1) / ((2 * k + 1) + 1)`, and the index of the antipode is `k + 1`, so the quotient is
exactly one half and the angle is `π`.

DERIVED: no numeral appears in the statement; `Real.pi` is a constant, and the extent arithmetic is
inside `Substrate.antipode` and `antipodeRead`. -/
theorem antipodeRead_theta_eq_pi (k : ℕ) :
    (MassGap.Substrate.antipodeRead k).θ (MassGap.Substrate.antipode k) = Real.pi := by
  have hv : ((MassGap.Substrate.antipode k : Fin (2 * k + 1 + 1)) : ℕ) = k + 1 := rfl
  show 2 * Real.pi * (((MassGap.Substrate.antipode k : Fin (2 * k + 1 + 1)) : ℕ) : ℝ)
      / (((2 * k + 1 : ℕ) : ℝ) + 1) = Real.pi
  rw [hv]
  have hne : ((k : ℝ) + 1) ≠ 0 := ne_of_gt (by positivity)
  push_cast
  field_simp
  ring

#print axioms antipodeRead_theta_eq_pi

/-- `∑ d, (Substrate.antipodeRead k).p d * Real.cos ((Substrate.antipodeRead k).θ d) = -1`. The
read's total mass is `1` (`Substrate.antipodeRead_sum`), so `p` equals `ρ`, which is the indicator of
the antipode; the sum collapses to `Real.cos π`, which is `-1`.

DERIVED: `1` is the value of the cosine average, negated — the cosine at angle `π`. -/
theorem antipodeRead_cosAvg_eq_neg_one (k : ℕ) :
    ∑ d, (MassGap.Substrate.antipodeRead k).p d
        * Real.cos ((MassGap.Substrate.antipodeRead k).θ d) = -1 := by
  have hsum := MassGap.Substrate.antipodeRead_sum k
  have hp : ∀ d, (MassGap.Substrate.antipodeRead k).p d
      = (MassGap.Substrate.antipodeRead k).ρ d := by
    intro d
    show (MassGap.Substrate.antipodeRead k).ρ d
        / (∑ d', (MassGap.Substrate.antipodeRead k).ρ d') = _
    rw [hsum, div_one]
  have hterm : ∀ d : Fin (2 * k + 1 + 1),
      (MassGap.Substrate.antipodeRead k).p d
          * Real.cos ((MassGap.Substrate.antipodeRead k).θ d)
        = if d = MassGap.Substrate.antipode k then
            Real.cos ((MassGap.Substrate.antipodeRead k).θ d) else 0 := by
    intro d
    rw [hp d]
    show (if d = MassGap.Substrate.antipode k then (1 : ℝ) else 0) * _ = _
    split <;> ring
  rw [Finset.sum_congr rfl (fun d _ => hterm d),
    Finset.sum_ite_eq' Finset.univ (MassGap.Substrate.antipode k)
      (fun d => Real.cos ((MassGap.Substrate.antipodeRead k).θ d))]
  simp only [Finset.mem_univ, if_true]
  rw [antipodeRead_theta_eq_pi k, Real.cos_pi]

#print axioms antipodeRead_cosAvg_eq_neg_one

/-- Three facts about `Substrate.antipodeRead k`, at every `k`: its tension is below `κ₀YM`; its
cosine average is `-1`; and it does not satisfy `3 ^ (-(1:ℝ)/4) < cosine average`.

The tension is `0` because `Real.log` takes the logarithm of the absolute value:
`-Real.log (-1) = -Real.log 1 = 0`, and `κ₀YM_pos` puts that below the floor. The third conjunct
follows from `Real.rpow_pos_of_pos`.

So the unguarded form `∀ β, μEven a β < κ₀YM` is satisfied by a read whose cosine average is `-1`,
while the form `ConfinesAtAnAperture` uses is not.

DERIVED: `1` occurs twice — as the value of the cosine average, negated, and as the numerator of the
floor's exponent `-(1:ℝ)/4`; `3` is the base of that floor and `4` its root. -/
theorem unguarded_confinement_is_satisfiable_without_decay (k : ℕ) :
    (MassGap.Substrate.antipodeRead k).tension < MassGap.κ₀YM
      ∧ ∑ d, (MassGap.Substrate.antipodeRead k).p d
          * Real.cos ((MassGap.Substrate.antipodeRead k).θ d) = -1
      ∧ ¬ ((3 : ℝ) ^ (-(1 : ℝ) / 4)
            < ∑ d, (MassGap.Substrate.antipodeRead k).p d
                * Real.cos ((MassGap.Substrate.antipodeRead k).θ d)) := by
  have hcos := antipodeRead_cosAvg_eq_neg_one k
  have h0 : (MassGap.Substrate.antipodeRead k).tension = 0 := by
    show - Real.log (∑ d, (MassGap.Substrate.antipodeRead k).p d
      * Real.cos ((MassGap.Substrate.antipodeRead k).θ d)) = 0
    rw [hcos, ← Real.log_abs]
    simp
  refine ⟨by rw [h0]; exact MassGap.κ₀YM_pos, hcos, ?_⟩
  rw [hcos]
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  exact not_lt.mpr (by linarith)

#print axioms unguarded_confinement_is_satisfiable_without_decay

/-! ## 7. Axiom footprints -/

section Audit
#print axioms ConfinesAtAnAperture
#print axioms apertureOf
#print axioms apertureOf_confines
#print axioms fullModelOfConfinement
#print axioms measure_is_osFamilyTension
#print axioms measure_Q_eq
#print axioms measure_Na_tendsto
#print axioms measure_c
#print axioms wilsonOfConfinement
#print axioms FlagshipAt
#print axioms flagship_of_confinement_at_an_aperture
#print axioms mass_gap_rate_and_continuum_at_an_aperture
#print axioms confinement_at_an_aperture_of_substrate
#print axioms flagship_of_substrate_even_via_aperture
#print axioms unguarded_of_confinesAtAnAperture
#print axioms confinement_at_an_aperture_of_law_above_cut
#print axioms evenAp_nonempty
#print axioms cosAvgEven
#print axioms confines_iff_pos_and_tension_lt_floor
#print axioms apertureOf_cosAvg
#print axioms antipodeRead_theta_eq_pi
#print axioms antipodeRead_cosAvg_eq_neg_one
#print axioms unguarded_confinement_is_satisfiable_without_decay
end Audit

end MassGap.ApertureRoute
