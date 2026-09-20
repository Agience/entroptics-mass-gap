import MassGap.ApertureRoute

/-!
# MassGap.FlagshipScope — ADVERSARIAL SCRATCH MODULE (not imported by `MassGap.lean`)

Machine checks for an adversarial audit of
`ApertureRoute.flagship_of_confinement_at_an_aperture`. Nothing here is part of the development;
it exists to test whether that theorem's conclusion is a statement about the SU(3) Wilson
correlation. Delete freely.
-/

namespace MassGap.FlagshipScope

open Filter
open MassGap.EvenAperture
open MassGap.ApertureRoute

/-! ## 1. The measure half of `FlagshipAt` uses no hypothesis

The proof term below is `OSFamily.os_continuum_tension`, which is an UNCONDITIONAL theorem proved in
`OSFamily.lean` at an arbitrary coupling. `hc` appears in the statement only because the statement is
spelled through `wilsonOfConfinement hc`; it contributes nothing to the proof. The observation is
unchanged by the measure field moving from `WilsonModel.ymFamilyTension` to
`OSFamily.osFamilyTension βFlag`: it was never the family that carried the hypothesis. -/
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

/-- The `R` field is literally the same closed term at every aperture. -/
theorem R_is_the_same_term_at_every_aperture (a a' : EvenAp) :
    (ymModelEven a).R = (ymModelEven a').R := rfl

#print axioms R_is_the_same_term_at_every_aperture

/-- And the clause itself holds at every aperture with no hypothesis. -/
theorem so4_clause_unconditional (a : EvenAp) :
    ∀ d d', (ymModelEven a).R d = (ymModelEven a).R d' := A2_even a

#print axioms so4_clause_unconditional

/-! ## 3. The "correlation" the gap clause is about is a manufactured geometric sequence -/

/-- `∑_k P_k m_k^τ` for `ymModelEven` is exactly `exp(-(κ₀ - μ))^τ`. There is one mode, its weight
is `1`, and its magnitude is DEFINED as its own bound. -/
theorem gap_summand_is_manufactured (a : EvenAp) (β : ℝ) (τ : ℕ) :
    ∑ k ∈ (ymModelEven a).s β, (ymModelEven a).P β k * ((ymModelEven a).m β k) ^ τ
      = ((Real.exp (-(MassGap.κ₀YM - μEven a β)) : ℝ) : ℂ) ^ τ := by
  show ∑ _k : Unit, (1 : ℂ) * ((Real.exp (-(MassGap.κ₀YM - μEven a β)) : ℝ) : ℂ) ^ τ = _
  simp

#print axioms gap_summand_is_manufactured

/-! ## 4. THE VACUITY WITNESS

A `LatticeYM` with `ymModelEven`'s exact shape and the tension set to `0`. There is no read, no
correlation, no gauge group and no lattice anywhere in it.

CHOSEN: the tension `μ ≡ 0`. It is chosen to be the WORST case for the conclusion, not a convenient
one — zero tension is the NON-confining reading, so every clause the flagship delivers here it
delivers for a theory with no confinement at all. Any other constant below `κ₀YM` would witness the
same thing; `0` is picked because it is the value a reader can check against `κ₀YM_pos` in one step.

DERIVED: the remaining literals are the shape of `ymModelEven` (`Complete.lean:2007`,
`EvenAperture.lean:256`) transcribed rather than invented. `P := 1` is its unit weight; `R := 0` is
a constant direction profile, which is all the `R d = R d'` clause reads; `Idx := Unit` is its
one-mode index. The `4` the gate sees is inside `κ₀YM = ¼log3`, carried in by name and counted off
directed cube paths in `Floor.lean`. No numeral here is a level anything is compared against. -/
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

/-- The measure side is `OSFamily.osFamilyTension βFlag` verbatim — the same closed term the real
construction uses, because the measure side takes no hypothesis. That is the point of the witness: the
measure half is now the unclamped connected `SU(3)` correlation over a diverging volume, and the
flagship's conclusion STILL attaches to a gap side with no gauge content, because the two halves are
never composed.

DERIVED: the `3` is `MassGap.NYM`, the Clay gauge group `SU(3)`, reaching the statement through
`OSFamily.osFamilyTension`'s type rather than being chosen here. No level and no threshold. -/
noncomputable def bogusFull : MassGap.FullModel where
  gap := bogusYM
  h1 := bogus_A1
  h2 := bogus_A2
  measure := MassGap.OSFamily.osFamilyTension MassGap.ApertureRoute.βFlag

/-- And `paramsTension` verbatim, so the "SU(3)" label (`params.N = 3`) survives unchanged.

DERIVED: the `3` is not this declaration's. It is `WilsonModel.paramsTension`'s own `N`, reused
without modification, and that is the POINT of the witness rather than an incidental choice — the
rank record that says "SU(3)" survives intact on an object with no gauge group, which is what shows
the label is carried by `params` and never read by the conclusion. -/
noncomputable def bogusWilson : MassGap.WilsonRealization where
  params := MassGap.WilsonModel.paramsTension
  model := bogusFull
  hc := MassGap.WilsonModel.paramsTension_irCutoff.symm

/-- **THE WHOLE FLAGSHIP CONCLUSION, FOR AN OBJECT WITH NO GAUGE CONTENT.**

Mass gap, non-triviality (`μ - κ < 0`), `SO(4)` invariance and the OS0-OS3 continuum measure, for
a model whose tension is the constant `0`. -/
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

/-! ## 5. `ymFamilyTension`'s `Q` ignores its test configuration entirely

So OS1 (Euclidean invariance) and OS3 (permutation symmetry) of `ymFamilyTension` hold because the
reflected form is constant in `j`, not because the measure is invariant in any nontrivial sense.

THE FINDING SURVIVES THE MEASURE SWAP, and the second theorem below is the check. The flagship's
measure is now `OSFamily.osFamilyTension βFlag`, whose reflected form is
`WilsonBridge.corrClay (extent a) β (lagOf a j.2.2)` — which reads the test configuration through
`j.2.2` ALONE. `OSFamily.actEOS` multiplies `j.1` and `actPOS` multiplies `j.2.1`, and neither touches
`j.2.2`. So both group actions still move only components the reflected form is independent of, and
OS1 and OS3 still hold for that reason rather than because the measure is invariant in any nontrivial
sense. The new family is not constant in `j` — it varies with the lag — but the lag is exactly the
component these two clauses never move. -/
theorem Q_is_constant_in_the_test_configuration
    (j j' : MassGap.WilsonModel.ymFamilyTension.J) (a : ℕ) :
    MassGap.WilsonModel.ymFamilyTension.Q j a
      = MassGap.WilsonModel.ymFamilyTension.Q j' a := by
  show MassGap.WilsonGauge.QG j a = MassGap.WilsonGauge.QG j' a
  rw [MassGap.WilsonGauge.QG_eq, MassGap.WilsonGauge.QG_eq]

#print axioms Q_is_constant_in_the_test_configuration

/-- **AND THE FLAGSHIP'S MEASURE HAS THE SAME PROPERTY, on the components the actions move.** Two
test configurations agreeing on the lag give the same reflected form whatever their Euclidean and
permutation components are — and `actE`/`actP` change nothing but those components. So `os_euc` and
`os_perm` of `osFamilyTension` are as empty as `ymFamilyTension`'s.

DERIVED: no numeral. -/
theorem osFamilyTension_Q_constant_on_the_acted_components (β : ℝ)
    (j j' : MassGap.OSFamily.JOS) (a : ℕ) (h : j.2.2 = j'.2.2) :
    (MassGap.OSFamily.osFamilyTension β).Q j a
      = (MassGap.OSFamily.osFamilyTension β).Q j' a :=
  MassGap.OSFamily.Qos_depends_only_on_the_lag β j j' a h

#print axioms osFamilyTension_Q_constant_on_the_acted_components

/-- **What the swap DOES change on the `j` side, stated so it is not mistaken for more.** The lag
label reaches the correlation's SEPARATION, and the lag map is not constant. That is not a refutation
of the finding above — the actions never move the lag — and it does not show two correlations DIFFER,
which would be a statement about the `SU(3)` Gibbs measure that nothing here proves.

DERIVED: `1` is any index (`OSFamily.extent 1 = 4`); `0` and `1` are the two labels compared. -/
theorem osFamilyTension_lag_is_not_constant :
    MassGap.OSFamily.lagOf 1 0 ≠ MassGap.OSFamily.lagOf 1 1 := by decide

#print axioms osFamilyTension_lag_is_not_constant

/-- The family's spectrum `ev` is the fabricated constant read `wOne`, at every spacing index. -/
theorem ev_is_wOne (a n : ℕ) :
    MassGap.WilsonModel.ymFamilyTension.ev a n = MassGap.WilsonModel.wOne n := rfl

#print axioms ev_is_wOne

end MassGap.FlagshipScope
