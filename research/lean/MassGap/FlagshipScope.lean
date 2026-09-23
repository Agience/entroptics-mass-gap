import MassGap.ApertureRoute

/-!
# MassGap.FlagshipScope — what each clause of `FlagshipAt` depends on

Machine-checked statements delimiting `ApertureRoute.flagship_of_confinement_at_an_aperture`.
`MassGap.lean` imports this module, so `#print axioms` covers its declarations and they are
recompiled whenever the theorems they describe change.

## What the declarations state

* `flagship_measure_half_needs_no_hypothesis` — the OS0–OS3 conjunct of the flagship, spelled
  through `wilsonOfConfinement hc`, is proved by `OSFamily.os_continuum_tension` at `βFlag`. `hc`
  occurs in the statement only through that spelling and is not used in the proof term.
* `R_is_the_same_term_at_every_aperture` — `(ymModelEven a).R = (ymModelEven a').R` by `rfl`, for
  any two even apertures.
* `so4_clause_unconditional` — `∀ d d', (ymModelEven a).R d = (ymModelEven a).R d'` at every
  aperture `a`, with no further hypothesis. It is `A2_even a`.
* `gap_summand_is_manufactured` — the gap conjunct's mode sum for `ymModelEven a` equals
  `(exp (-(κ₀YM - μEven a β)) : ℂ) ^ τ`. The index type is `Unit`, the weight is `1`, and the mode's
  magnitude is the bound itself, so the sum is a geometric sequence in `τ` determined by
  `κ₀YM - μEven a β` alone.
* `flagship_for_bogus` — the full flagship conclusion, both conjuncts, holds for `bogusWilson`, a
  `WilsonRealization` whose gap datum has tension identically `0` and whose carrier types are
  `Unit`.
* `Q_is_constant_in_the_test_configuration` — `WilsonModel.ymFamilyTension.Q j a` is independent of
  `j`.
* `osFamilyTension_Q_constant_on_the_acted_components` — `(OSFamily.osFamilyTension β).Q j a`
  depends on `j` only through `j.2.2`. `OSFamily.actEOS` acts on `j.1` and `actPOS` on `j.2.1`, so
  the `os_euc` and `os_perm` fields hold because those actions do not move the component `Q` reads.
* `osFamilyTension_lag_is_not_constant` — `OSFamily.lagOf 1 0 ≠ OSFamily.lagOf 1 1`, by `decide`.
  The lag map is therefore not constant. It is a statement about `lagOf`, not about any two
  correlation values.
* `ev_is_wOne` — `WilsonModel.ymFamilyTension.ev a n = WilsonModel.wOne n` by `rfl`, at every
  spacing index `a`.

DERIVED: `0` is the value `bogusYM`'s tension is set to, the limit point in the `Tendsto` clauses,
the level non-triviality compares against, the lower bound on the limit `q`, and a lag label; `1` is
`bogusYM`'s unit weight, a spacing index, and a lag label; `2` appears only as the product
projections `j.2.1` and `j.2.2`; `4` enters through `κ₀YM = ¼ log 3`, carried in by name from
`Floor.lean`, and through `Equiv.Perm (Fin 4)` in the families' group types.
-/

namespace MassGap.FlagshipScope

open Filter
open MassGap.EvenAperture
open MassGap.ApertureRoute

/-! ## 1. The measure conjunct of `FlagshipAt`

The theorem below states the OS0–OS3 conjunct for `wilsonOfConfinement hc`: a subsequence `φ` and a
pointwise limit `q` of the reflected forms, bounded by `⌈c⌉₊ * B`, nonnegative, and fixed by both
group actions. Its proof term is `OSFamily.os_continuum_tension βFlag`, a theorem of `OSFamily.lean`
that takes no confinement hypothesis, so `hc` enters the statement only through the spelling
`wilsonOfConfinement hc` and is not consumed. This holds for the measure field
`OSFamily.osFamilyTension βFlag` as it did for `WilsonModel.ymFamilyTension`.

DERIVED: `0` is the lower bound asserted on the limit `q`. -/
theorem flagship_measure_half_needs_no_hypothesis (hc : ConfinesAtAnAperture) :
    ∃ (q : (wilsonOfConfinement hc).model.measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ j, Tendsto (fun k => (wilsonOfConfinement hc).model.measure.Q j (φ k))
              atTop (nhds (q j))) ∧
      (∀ j, |q j| ≤ (⌈(wilsonOfConfinement hc).model.measure.c⌉₊ : ℝ)
              * (wilsonOfConfinement hc).model.measure.B) ∧
      (∀ j, 0 ≤ q j) ∧
      (∀ g j, q ((wilsonOfConfinement hc).model.measure.actE g j) = q j) ∧
      (∀ σ j, q ((wilsonOfConfinement hc).model.measure.actP σ j) = q j) :=
  MassGap.OSFamily.os_continuum_tension MassGap.ApertureRoute.βFlag

#print axioms flagship_measure_half_needs_no_hypothesis

/-! ## 2. The `SO(4)` clause does not depend on the aperture -/

/-- `(ymModelEven a).R = (ymModelEven a').R` for any two `a a' : EvenAp`, by `rfl`: the `R` field is
the same closed term at every even aperture and does not depend on `a`.

DERIVED: no numeral appears in the statement. -/
theorem R_is_the_same_term_at_every_aperture (a a' : EvenAp) :
    (ymModelEven a).R = (ymModelEven a').R := rfl

#print axioms R_is_the_same_term_at_every_aperture

/-- `∀ d d', (ymModelEven a).R d = (ymModelEven a).R d'` at every `a : EvenAp`. It is `A2_even a`,
which takes no hypothesis beyond the aperture, so the `SO(4)` conjunct of the flagship holds
independently of any confinement input.

DERIVED: no numeral appears in the statement. -/
theorem so4_clause_unconditional (a : EvenAp) :
    ∀ d d', (ymModelEven a).R d = (ymModelEven a).R d' := A2_even a

#print axioms so4_clause_unconditional

/-! ## 3. The "correlation" the gap clause is about is a manufactured geometric sequence -/

/-- The gap conjunct's mode sum for `ymModelEven a`, at coupling `β` and lag `τ`, equals
`((Real.exp (-(κ₀YM - μEven a β)) : ℝ) : ℂ) ^ τ`. Proved by unfolding: the index type is `Unit`, the
weight `P` is the constant `1`, and the mode magnitude `m` is `Real.exp (-(κ₀YM - μEven a β))`
itself.

So this sum is a geometric sequence whose ratio is fixed by `κ₀YM - μEven a β`; its decay is a
property of that difference and not of any correlation measured on a configuration.

DERIVED: no numeral appears in the statement. The unit weight `1` and the one-element index type
`Unit` are `ymModelEven`'s own fields and are reached by unfolding in the proof. -/
theorem gap_summand_is_manufactured (a : EvenAp) (β : ℝ) (τ : ℕ) :
    ∑ k ∈ (ymModelEven a).s β, (ymModelEven a).P β k * ((ymModelEven a).m β k) ^ τ
      = ((Real.exp (-(MassGap.κ₀YM - μEven a β)) : ℝ) : ℂ) ^ τ := by
  show ∑ _k : Unit, (1 : ℂ) * ((Real.exp (-(MassGap.κ₀YM - μEven a β)) : ℝ) : ℂ) ^ τ = _
  simp

#print axioms gap_summand_is_manufactured

/-! ## 4. A `LatticeYM` with constant tension

A `LatticeYM` with `ymModelEven`'s shape and the tension function set to the constant `0`. Its
`Idx` and `Dir` are both `Unit`; it refers to no gauge group, lattice, read or correlation.

CHOSEN: the tension `μ ≡ 0`, which is the non-confining value, so every clause the flagship
delivers for this object it delivers at zero tension. Any constant strictly below `κ₀YM` would serve;
`0` is the one that follows from `κ₀YM_pos` in a single step.

DERIVED: the remaining literals transcribe `ymModelEven`'s own fields. `P := 1` is its unit weight;
`R := 0` is a constant direction profile, which is all the `R d = R d'` clause reads; `Idx := Unit`
is its one-mode index type. `κ₀` and `κ` are both `κ₀YM = ¼ log 3`, carried in by name from
`Floor.lean`, where the `4` is counted off directed cube paths. No numeral here is a level anything
is compared against. -/
noncomputable def bogusYM : MassGap.LatticeYM where
  Idx := Unit
  Dir := Unit
  s := fun _ => (Finset.univ : Finset Unit)
  P := fun _ _ => 1
  m := fun _ _ => ((Real.exp (-(MassGap.κ₀YM - 0)) : ℝ) : ℂ)
  μ := fun _ => 0
  R := fun _ => 0
  κ₀ := MassGap.κ₀YM
  κ := MassGap.κ₀YM
  hfloor := le_refl _
  hread := by
    intro β _ _
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

theorem bogus_A1 : MassGap.A1_YM bogusYM := fun _ => MassGap.κ₀YM_pos

theorem bogus_A2 : MassGap.A2_YM bogusYM := fun _ _ => rfl

/-- A `FullModel` whose `gap` field is `bogusYM`, with `A1_YM` and `A2_YM` discharged by `bogus_A1`
and `bogus_A2`, and whose `measure` field is `OSFamily.osFamilyTension βFlag` — the same closed term
the other realisations use, since the measure field takes no confinement hypothesis. The two fields
are independent: nothing in `FullModel` relates the gap datum to the measure family.

DERIVED: no numeral literal occurs in the construction. The rank `3` reaches it inside
`OSFamily.osFamilyTension`, whose type carries `MassGap.NYM`, and is not set here. -/
noncomputable def bogusFull : MassGap.FullModel where
  gap := bogusYM
  h1 := bogus_A1
  h2 := bogus_A2
  measure := MassGap.OSFamily.osFamilyTension MassGap.ApertureRoute.βFlag

/-- A `WilsonRealization` pairing `bogusFull` with `WilsonModel.paramsTension` unchanged, so the
rank record `params.N = 3` is present on an object whose gap datum has no gauge content. `hc` is
`paramsTension_irCutoff.symm`. The rank is carried by the `params` field and is not read by the
flagship conclusion.

DERIVED: no numeral literal occurs in the construction. The `3` is `WilsonModel.paramsTension`'s own
`N`, reused without modification. -/
noncomputable def bogusWilson : MassGap.WilsonRealization where
  params := MassGap.WilsonModel.paramsTension
  model := bogusFull
  hc := MassGap.WilsonModel.paramsTension_irCutoff.symm

/-- The full flagship conclusion for `bogusWilson`: both conjuncts of
`existence_and_gap_of_wilson`, namely the mode sum tending to `0` at every coupling,
non-triviality `μ - κ < 0`, the `SO(4)` clause `R d = R d'`, and the OS0–OS3 subsequential limit
with its bound, nonnegativity and invariances. The proof is
`existence_and_gap_of_wilson bogusWilson`.

The gap datum here has tension identically `0`, carrier types `Unit`, and no gauge group, lattice or
correlation, so the conclusion's gap conjunct holds at zero tension.

DERIVED: `0` is the limit point in both `Tendsto` clauses, the level non-triviality compares
against, and the lower bound asserted on `q`. -/
theorem flagship_for_bogus :
    ((∀ β, Tendsto (fun τ : ℕ => ‖∑ k ∈ bogusWilson.model.gap.s β,
          bogusWilson.model.gap.P β k * (bogusWilson.model.gap.m β k) ^ τ‖) atTop (nhds 0)) ∧
        (∀ β, bogusWilson.model.gap.μ β - bogusWilson.model.gap.κ < 0) ∧
        (∀ d d', bogusWilson.model.gap.R d = bogusWilson.model.gap.R d')) ∧
      (∃ (q : bogusWilson.model.measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ j, Tendsto (fun k => bogusWilson.model.measure.Q j (φ k)) atTop (nhds (q j))) ∧
        (∀ j, |q j| ≤ (⌈bogusWilson.model.measure.c⌉₊ : ℝ) * bogusWilson.model.measure.B) ∧
        (∀ j, 0 ≤ q j) ∧
        (∀ g j, q (bogusWilson.model.measure.actE g j) = q j) ∧
        (∀ σ j, q (bogusWilson.model.measure.actP σ j) = q j)) :=
  MassGap.existence_and_gap_of_wilson bogusWilson

#print axioms flagship_for_bogus

/-! ## 5. Which component of the test configuration the reflected form reads

`ymFamilyTension.Q j a` is independent of `j` altogether, so its `os_euc` and `os_perm` fields hold
because the form is constant in the test configuration.

`OSFamily.osFamilyTension β` has reflected form
`WilsonBridge.corrClay (extent a) β (lagOf a j.2.2)`, which reads `j` through `j.2.2` alone. It is
not constant in `j`, since it varies with the lag. But `OSFamily.actEOS` multiplies `j.1` and
`actPOS` multiplies `j.2.1`, and neither changes `j.2.2`, so the two invariance fields hold because
the actions move components the form does not read. The two theorems below state each half.

DERIVED: `1` and `2` appear only as product projections `j.1`, `j.2.1` and `j.2.2`. -/
theorem Q_is_constant_in_the_test_configuration
    (j j' : MassGap.WilsonModel.ymFamilyTension.J) (a : ℕ) :
    MassGap.WilsonModel.ymFamilyTension.Q j a
      = MassGap.WilsonModel.ymFamilyTension.Q j' a := by
  show MassGap.WilsonGauge.QG j a = MassGap.WilsonGauge.QG j' a
  rw [MassGap.WilsonGauge.QG_eq, MassGap.WilsonGauge.QG_eq]

#print axioms Q_is_constant_in_the_test_configuration

/-- `(OSFamily.osFamilyTension β).Q j a = (OSFamily.osFamilyTension β).Q j' a` whenever
`j.2.2 = j'.2.2`: the reflected form depends on the test configuration only through its third
component. It is `OSFamily.Qos_depends_only_on_the_lag`.

Since `actEOS` changes only `j.1` and `actPOS` only `j.2.1`, the `os_euc` and `os_perm` fields of
`osFamilyTension` follow from this independence rather than from any invariance of the underlying
correlation.

DERIVED: `2` appears only as the product projections `j.2.2` and `j'.2.2`. -/
theorem osFamilyTension_Q_constant_on_the_acted_components (β : ℝ)
    (j j' : MassGap.OSFamily.JOS) (a : ℕ) (h : j.2.2 = j'.2.2) :
    (MassGap.OSFamily.osFamilyTension β).Q j a
      = (MassGap.OSFamily.osFamilyTension β).Q j' a :=
  MassGap.OSFamily.Qos_depends_only_on_the_lag β j j' a h

#print axioms osFamilyTension_Q_constant_on_the_acted_components

/-- `OSFamily.lagOf 1 0 ≠ OSFamily.lagOf 1 1`, by `decide`: at spacing index `1` the lag map sends
the labels `0` and `1` to different lags, so `lagOf` is not constant in its second argument.

This is a statement about `lagOf` alone. It does not assert that the two correlation values at those
lags differ, and it does not bear on
`osFamilyTension_Q_constant_on_the_acted_components`, whose hypothesis fixes the lag component.

DERIVED: the first `1` is the spacing index, at which `OSFamily.extent 1 = 4`; `0` and the remaining
`1` are the two labels compared. -/
theorem osFamilyTension_lag_is_not_constant :
    MassGap.OSFamily.lagOf 1 0 ≠ MassGap.OSFamily.lagOf 1 1 := by decide

#print axioms osFamilyTension_lag_is_not_constant

/-- `WilsonModel.ymFamilyTension.ev a n = WilsonModel.wOne n` by `rfl`: the family's eigenvalue
field is `wOne` at every spacing index `a`, so it does not vary with the spacing.

DERIVED: no numeral appears in the statement. -/
theorem ev_is_wOne (a n : ℕ) :
    MassGap.WilsonModel.ymFamilyTension.ev a n = MassGap.WilsonModel.wOne n := rfl

#print axioms ev_is_wOne

end MassGap.FlagshipScope
