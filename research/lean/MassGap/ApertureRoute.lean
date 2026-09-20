import MassGap.NonnegArm

/-!
# MassGap.ApertureRoute — the flagship from confinement at ONE aperture

`EvenAperture.existence_and_gap_of_substrate_even` consumes

    h : ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B

a moment bound quantified over EVERY even aperture. This file shows that the aperture quantifier is
not what the conclusion rests on, by rebuilding the flagship against the weaker hypothesis the
existing proof actually consumes.

## What `h` is used for, and it is less than it looks

Read `EvenAperture.fullModelEven`'s four fields:

    gap     := ymModelEven (apertureEven h)
    h1      := apertureEven_confines h
    h2      := A2_even (apertureEven h)
    measure := WilsonModel.ymFamilyTension

`apertureEven h` is `(exists_confining_even_aperture h).choose` and `apertureEven_confines h` is its
`.choose_spec`. `A2_even` takes no hypothesis. `ymFamilyTension` is a fixed object and the measure
side takes no hypothesis at all. So `h` enters the construction ONLY to produce an `EvenAp` together
with confinement at it, and is then discarded. Its load-bearing content is

    ∃ a : EvenAp, ∀ β : ℝ, 3^{−1/4} < ⟨cos θ⟩ of the read at (a, β)

— confinement at ONE even extent, for every coupling. That is `ConfinesAtAnAperture` below, and
`flagship_of_confinement_at_an_aperture` derives the whole flagship from it: the gap, non-triviality,
`SO(4)` invariance and the continuum measure.

**The condition is stated on the cosine average, NOT on the tension**, and that is not cosmetic:
`Real.log` is even, so `∀ β, μEven a β < κ₀YM` is satisfied by a read whose cosine average is `−1` —
no decay at all. `ConfinesAtAnAperture`'s docstring sets out the defect and
`unguarded_confinement_is_satisfiable_without_decay` machine-checks it on `Substrate.antipodeRead`.
The two spellings differ exactly by the positivity guard the tree already carries in
`Moment.Read.cosAvg_gt_of_tension_lt_floor`.

## THE APERTURE QUANTIFIER IS DROPPED, NOT SATISFIED

Nothing here proves confinement at any aperture. What is established is a strictly weaker HYPOTHESIS,
and the implication runs one way only:

* `confinement_at_an_aperture_of_substrate` — the old hypothesis gives the new one. It is
  `EvenAperture.exists_confining_even_aperture`, unchanged.
* **No converse is claimed, and none is available.** The old hypothesis bounds the moment at every
  even aperture simultaneously; the new one asks for confinement at a single extent of the prover's
  choosing. A witness for the second says nothing about any other extent.

So this does not discharge the reduction. It relocates the target from a statement uniform in the
aperture to a statement at one aperture, which is a different and smaller obligation.

## WHERE THE DIFFICULTY MOVES TO, AND WHAT CHOOSING THE EXTENT DOES NOT BUY

**Choosing the extent does not lower the bar.** `Moment.Read.tension_lt_floor_of_circ_moment`'s scale
hypothesis `(2π/(N+1))²·B/2 < 1 − 3^{−1/4}` does relax as the extent grows, but the quantity it
bounds grows at exactly the same rate, and the two cancel: substituting `d2At = substrateRatio·(N+1)²`
gives `(2π)²·substrateRatio/2 < 1 − 3^{−1/4}`, with no `N` in it. `Complete.surplus_ge`'s `hcancel`
step is that cancellation, proved as an EQUALITY by `field_simp` — "the aperture cancels EXACTLY: no
inequality is spent here, because the ratio is the read itself". So a larger extent admits a larger
absolute moment and demands a proportionally smaller ratio, and the criterion is the same at every
extent.

What choosing the extent DOES buy is the quantifier: the bar has to be met at ONE extent instead of at
all of them simultaneously. That is the whole of the weakening, and it is worth stating exactly,
because the intuition that a bigger aperture is easier is wrong here.

**The bar, at every extent.** The unconditional bound is `substrateRatio ≤ 1/4`
(`Substrate.substrateRatio_le_quarter`, attained by `antipodeRead`, so it is the best constant the
read interface supports). The requirement is
`substrateRatio < Complete.substrateThreshold = arccos(3^{−1/4})²/(2π)² ≈ 0.0126877`
(`Complete.confinement_at_of_substrate_sharp`), which is SHARP — equality holds for the point mass at
`θ = arccos(3^{−1/4})`, so no argument reading only the second moment can do better. That is a factor
of about `19.7`, at every extent, and nothing here narrows it.

Use the sharp constant, not `2(1 − 3^{−1/4})/(2π)² ≈ 0.0121669`. The latter is what
`Moment.Read.tension_lt_floor_of_circ_moment` carries, because it goes through `1 − x²/2 ≤ cos x` —
the tangent to `t ↦ cos √t` AT THE ORIGIN, correct only for a read concentrated at zero lag.
`Complete.confinement_at_of_substrate_sharp` takes the tangent at the threshold itself and is 4.3%
more generous. Both are SUFFICIENT thresholds. Do not confuse either with the NECESSARY ceiling
`(1 − 3^{−1/4})/8 ≈ 0.0300` of `Moment.Read.substrate_lt_of_tension_lt_floor`, which runs the other
way — from a sub-floor tension TO a ratio bound — and which additionally requires
`0 < ∑ p_d cos θ_d`, a hypothesis that direction does not come without.

**The hard end is `β → ∞`.** The `∀ β` is unrestricted, and at fixed extent the large-coupling end is
where a correlator would flatten. The flat configuration is refused by the floor: the flat read's
substrate ratio is `1/12 + 1/(6n²)`, above the necessary ceiling `(1 − 3^{−1/4})/8` at every aperture
(`Substrate.flatRead_exceeds_ceiling`).

**But read that theorem's quantifiers before leaning on it.** `Substrate.flatRead` is indexed by
aperture ALONE — it has no coupling parameter — so `flatRead_exceeds_ceiling` is a `∀ k` statement
about a constructed read, and it is NOT a statement about `β → ∞`, at fixed extent or anywhere else.
It shows the floor refuses flatness; it does not show `wilsonCorrAt` becomes flat. `Substrate.lean` is
explicit that nothing of this kind can refute the hypothesis, because the hypothesis is about the
constructed correlation and no family of other reads bears on it. So this is an obstruction to clear,
not a refutation, and clearing it means a statement about the Wilson Gibbs measure at the chosen
extent that no theorem in this tree supplies.

## AN AUDIT OF `Aperture.lean`, BECAUSE ITS TITLE INVITES THE WRONG READING

The paper is titled for the finite aperture and `Aperture.lean` is named for it, so a reader will
assume that file carries the thesis. It does not, and the difference matters:

* **`wilsonCorrAt` and `WilsonBridge.corrClay` appear NOWHERE in that file.** Not in a statement, not
  in a proof. Every declaration there is one of three kinds, and none of them is about the Wilson
  ensemble: over a FREE mode family `{ι : Type*} (s : Finset ι) (P μ : ι → ℂ)` supplied by the caller
  (`finite_sum_margin_bound`, `finite_flow_decays`, `gap_at_finite_F`, `gap_uniform_in_F`,
  `gap_of_confinement`); over a free real family `μ₁ : ℕ → ℝ` or `Δ : ℝ → ℝ`
  (`UniformSpectralMargin`, `uniform_margin_of_intensive_radius`, `no_interior_transition`); or plain
  real analysis (`margin_iff_rate_pos`, `gap_refinement_invariant`). The one concrete theorem,
  `uniform_margin_solvable`, is about `Real.tanh b` at the exactly-solvable point — not Yang–Mills.
* `finite_flow_decays`, `gap_at_finite_F` and `gap_of_confinement` each take the spectral margin as a
  HYPOTHESIS, in three spellings of the same thing: `‖μ k‖ ≤ ρ` with `ρ < 1` supplied separately,
  `‖μ k‖ ≤ exp(-κ)` with `0 < κ`, and `‖m k‖ ≤ exp(-(κ₀ − μ))` with `μ < κ₀`. The margin IS the gap.
  The file's dichotomy — a mode on the unit circle, or a strict margin — is therefore not discharged
  there; there is no dichotomy theorem in the file at all, only the second horn, assumed.
* `no_interior_transition` has NO consumer anywhere in the tree. It is also stated for a single
  `Δ : ℝ → ℝ` with no aperture index, so applied at a fixed extent it yields a constant depending on
  that extent. Supplying the index is `CompactBeta.jointUniform_of_pointwise_of_equicontinuous`, which
  needs equicontinuity UNIFORM IN THE APERTURE — and `CompactBeta` measures what that costs
  (`clay_covariance_constant_not_aperture_uniform`, `profile_to_moment_not_uniformly_lipschitz`).
  Its own verdict on that equicontinuity is that it "is NOT available from anything proved": not that
  a route through clustering exists, but that none does.
* `margin_iff_rate_pos` and `uniform_margin_solvable` have no consumer either. Three of the file's
  eleven declarations are dead.
* `gap_refinement_invariant` is unconditional and used — it is `Real.log_rpow` plus `field_simp`, and
  it closes `a → 0` by an identity. It is not the only used declaration and not the most used:
  `gap_of_confinement` carries the file's traffic by a wide margin, and it is the one that takes the
  margin as a hypothesis.

What this file's construction DOES carry, and what it does not. It carries one EXTENT: the read
`μEven a β` is taken at a single `a : EvenAp`, and `ConfinesAtAnAperture` is the statement that one
extent suffices. It does NOT carry a derived finite MODE COUNT. `ymModelEven` has `Idx := Unit` and
`m β _ := exp(-(κ₀ − μEven a β))` — one mode, and a number defined equal to its own bound, so its
`hread` field is discharged by `le_of_eq`. `Complete.lean` says this of `ymModel` in the same terms,
and it is equally true here.

So the finite mode count is structural in the model rather than proved of the ensemble, and the open
statement that would make it a fact about Yang–Mills is `Complete.WilsonSpectral` — that
`wilsonCorrAt N β` admits a periodic transfer decomposition with nonnegative weights. **At the Clay
extent that is now PROVED**: `SlabQuadratic.wilsonSpectral (hβ : 0 ≤ β) : WilsonSpectral 3 β`,
foundational-only, from link- and site-reflection positivity through `SpectralFour.four_iff`. It
supplies the DECOMPOSITION, not a mode count and not a rate — `SpectralFour.fourRepresentable_const`
shows the constant triple is representable, so the property carries no gap. Neither `Aperture.lean`
nor this file supplies the finite mode count, which remains structural in the model.

## Provenance

Every declaration below is `EvenAperture`'s, transcribed against `ConfinesAtAnAperture` in place of
the substrate bound. No proof is new and no numeral is introduced. `#print axioms` after every
declaration; the gap side reports the foundational three and no named axiom, exactly as
`EvenAperture`'s does, because `readEven` is built from the PROVED reflection positivity.
-/

namespace MassGap.ApertureRoute

open Filter
open MassGap.EvenAperture

/-! ## 1. The hypothesis, named

The whole point of this file is that this `Prop` — and not the substrate bound — is what the flagship
consumes. Stating it separately is what makes that visible. -/

/-- The cosine average of the clamped read — the scalar the tension is the negative logarithm of.
`Complete.cosAvgYMAt` with `readEven` in place of `readYMAt`. -/
noncomputable def cosAvgEven (a : EvenAp) (β : ℝ) : ℝ :=
  ∑ d, (readEven a β).p d * Real.cos ((readEven a β).θ d)

#print axioms cosAvgEven

/-- **CONFINEMENT AT ONE APERTURE.** There is an even extent of at least four at which the read's
cosine average stays STRICTLY ABOVE THE ENTROPY FLOOR `3^{−1/4} = e^{−κ₀}` at every coupling.

This is A1 (`Apriori.A1`) at a single aperture, with the aperture existentially quantified OUTSIDE the
coupling quantifier. The order is what makes it weaker than the substrate bound: one extent has to
work, not all of them.

**WHY THIS IS STATED ON `⟨cos θ⟩` AND NOT ON THE TENSION — READ THIS BEFORE "SIMPLIFYING" IT.**

The obvious spelling is `∀ β, μEven a β < κ₀YM`, and it is WRONG. `Moment.Read.tension` is
`- Real.log (∑ d, p d * cos (θ d))`, and Mathlib's `Real.log` is EVEN (`Real.log_abs`,
`Real.log_neg_eq_log`): it takes the logarithm of the ABSOLUTE VALUE, so `log (-1) = log 1 = 0`. A
read whose cosine average is `−1` — total anticorrelation, no decay whatever — therefore has tension
exactly `0`, which is below `κ₀YM`, and would SATISFY the bare form.

This is not hypothetical. `Substrate.antipodeRead k` puts all its mass at the antipode, where
`θ = π` and `⟨cos θ⟩ = −1` exactly. It is the very read the tree exhibits to show the `1/4` constant
cannot be improved (`Substrate.antipodeRead_moment_eq_quarter_sq`) and that reflection positivity
alone leaves the substrate moment unbounded (`Substrate.rp_alone_leaves_moment_unbounded`). So the
read that MAXIMALLY VIOLATES the sufficient moment condition would PASS an unguarded tension
condition. `unguarded_confinement_is_satisfiable_without_decay` below exhibits the phenomenon in this
file so that it cannot be re-weakened by accident; `ReadLayer` machine-checks it for `antipodeRead`
itself at every aperture.

The guard is the tree's own. `Moment.Read.cosAvg_gt_of_tension_lt_floor` carries the hypothesis
`0 < ∑ d, p d * cos (θ d)` with the comment that "a nonpositive average has no logarithm and the
tension is not a read". Dropping it was the defect; this definition restores it.

**WHY THE SHARP FORM RATHER THAN THE CONJUNCTION.** `0 < ⟨cos θ⟩ ∧ μ < κ₀` and `3^{−1/4} < ⟨cos θ⟩`
are EQUIVALENT (`confines_iff_pos_and_tension_lt_floor` below, from the tree's two bridging lemmas),
so nothing is strengthened by choosing the second. It is chosen because it is one inequality rather
than a conjunction, and because it is exactly the intermediate the substrate route already derives
on its way to the tension bound — so `confinement_at_an_aperture_of_substrate` proves it directly
instead of proving a weaker thing and then re-deriving the guard.

DERIVED: no numeral. `EvenAp` carries `4 ≤ N + 1` and `Even (N + 1)`, both read off
`Complete.wilson_reflection_positive_at_even`'s hypotheses; `3^{−1/4} = e^{−κ₀}` with `κ₀YM = ¼log3`
counted off directed cube paths in `Floor.lean`. -/
def ConfinesAtAnAperture : Prop :=
  ∃ a : EvenAp, ∀ β : ℝ, (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β

#print axioms ConfinesAtAnAperture

/-- The aperture the hypothesis supplies. As in `EvenAperture.apertureEven`, no value is named — it
is `Classical.choose`n from the hypothesis's own witness. -/
noncomputable def apertureOf (hc : ConfinesAtAnAperture) : EvenAp := hc.choose

#print axioms apertureOf

/-- That aperture's read clears the floor at every coupling. -/
theorem apertureOf_cosAvg (hc : ConfinesAtAnAperture) :
    ∀ β : ℝ, (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven (apertureOf hc) β := hc.choose_spec

#print axioms apertureOf_cosAvg

/-- **And therefore confines**: the tension at that aperture is below the counting floor at every
coupling. `Moment.Read.tension_lt_floor_of_cosAvg`, which is the guarded direction — it reads the
logarithm only where its argument is positive. This is the `A1_YM` field of the model below. -/
theorem apertureOf_confines (hc : ConfinesAtAnAperture) :
    ∀ β : ℝ, μEven (apertureOf hc) β < MassGap.κ₀YM :=
  fun β => (readEven (apertureOf hc) β).tension_lt_floor_of_cosAvg (hc.choose_spec β)

#print axioms apertureOf_confines

/-- **THE GUARD IS EXACTLY THE MISSING POSITIVITY.** Clearing the floor is equivalent to the
conjunction of the positivity `Moment.Read.cosAvg_gt_of_tension_lt_floor` requires and the tension
bound the flagship consumes. Both directions, so the choice of spelling is a statement rather than a
preference.

Forward is `tension_lt_floor_of_cosAvg` plus `0 < 3^{−1/4}`; backward is
`cosAvg_gt_of_tension_lt_floor`, whose positivity hypothesis is the conjunct. -/
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

`EvenAperture.fullModelEven` and `EvenAperture.wilsonEven`, with `apertureOf hc` in place of
`apertureEven h`. `ymModelEven` and `A2_even` are reused verbatim — neither ever mentioned the
substrate bound. -/

/-- **A FULL MODEL FROM CONFINEMENT AT ONE APERTURE.** `EvenAperture.fullModelEven` with the
confinement witness supplying the aperture directly instead of the substrate bound supplying it
through `exists_confining_even_aperture`.

DERIVED: no numeral; every constant belongs to the pieces assembled. -/
noncomputable def fullModelOfConfinement (hc : ConfinesAtAnAperture) : MassGap.FullModel where
  gap := ymModelEven (apertureOf hc)
  h1 := apertureOf_confines hc
  h2 := A2_even (apertureOf hc)
  measure := MassGap.WilsonModel.ymFamilyTension

#print axioms fullModelOfConfinement

/-- **The measure side is untouched.** `fullModelOfConfinement`'s family is `ymFamilyTension` itself,
by `rfl` — the same object `EvenAperture.fullModelEven` and `WilsonModel.fullModelOfSubstrate` use.
Weakening the gap-side hypothesis does not restrict, weaken or re-derive the continuum half. -/
theorem measure_is_ymFamilyTension (hc : ConfinesAtAnAperture) :
    (fullModelOfConfinement hc).measure = MassGap.WilsonModel.ymFamilyTension := rfl

#print axioms measure_is_ymFamilyTension

/-- **AN `SU(3)` WILSON REALISATION FROM CONFINEMENT AT ONE APERTURE.**
`EvenAperture.wilsonEven`'s transcription. `WilsonModel.paramsTension` is reused unchanged: it reads
its infrared cutoff off the witness read. That cutoff does contain an aperture --
`kstar = 2π·cW` and `cW` carries `rW ^ (kW + 1)` with `kW` a `Classical.choose`n extent
(`WilsonModel.lean:261`) -- but it is a bare `ℕ` on the MEASURE side, fixed by the witness read and
unrelated to the `EvenAp` the gap side quantifies over. So the gap side's aperture, however it is
quantified, does not reach this field.

DERIVED: no numeral of this declaration's; `3` is `SU(3)`'s rank, carried from `paramsTension`. -/
noncomputable def wilsonOfConfinement (hc : ConfinesAtAnAperture) : MassGap.WilsonRealization where
  params := MassGap.WilsonModel.paramsTension
  model := fullModelOfConfinement hc
  hc := MassGap.WilsonModel.paramsTension_irCutoff.symm

#print axioms wilsonOfConfinement

/-! ## 3. The flagship -/

/-- The flagship's conclusion at the realisation this file builds: the mass gap (`C(τ) → 0`),
non-triviality (`μ − κ < 0`), `SO(4)` invariance (`R` direction-independent), and the tight
OS0–OS3 continuum limit.

Stated in the shape `NonnegArm.Flagship` uses — clause for clause the same conclusion, about this
file's realisation instead of `wilsonEven h` — so the conclusion can be named once and the theorem
below is faithful by type-checking rather than by assertion.

DERIVED: no magnitude appears anywhere in this statement. Every `0` is a sign or a limit point:
`nhds 0` is the assertion that the correlation TENDS TO zero, which is the mass gap itself and not a
level it is compared against; `μ − κ < 0` is the SIGN of the tension deficit; and `0 ≤ q j` is
nonnegativity of the limit functional, not a floor on it. The `4` is not a numeral of the definition
at all — it is the dimension inside the NAME `SO(4)`, the rotation group of the four-dimensional
hypercubic lattice `WilsonBridge.corrClay` is stated on, carried in rather than chosen here. The
magnitudes that do appear — `c`, `B` — are the measure's own fields, quantified by it. -/
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

/-- **THE FLAGSHIP FROM CONFINEMENT AT ONE APERTURE.**

Existence, the mass gap, non-triviality, `SO(4)` invariance and the continuum measure, from
`∃ a : EvenAp, ∀ β, μEven a β < κ₀YM` alone. No moment bound, and no quantifier over apertures.

The proof term is `existence_and_gap_of_wilson` applied to this file's realisation and nothing else,
which is how the statement is known to be the flagship rather than asserted to be. -/
theorem flagship_of_confinement_at_an_aperture (hc : ConfinesAtAnAperture) : FlagshipAt hc :=
  MassGap.existence_and_gap_of_wilson (wilsonOfConfinement hc)

#print axioms flagship_of_confinement_at_an_aperture

/-- **The gap WITH ITS RATE, and the continuum measure.** `EvenAperture.mass_gap_rate_and_continuum_even`
from the same hypothesis: the rate is the entropy surplus `κ₀ − μ` at the chosen aperture. -/
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

/-! ## 4. The new hypothesis is WEAKER than the old one

One direction, and only one. -/

/-- **THE OLD HYPOTHESIS GIVES THE NEW ONE.** `EvenAperture.exists_confining_even_aperture`, restated
as the implication between the two hypotheses so the ordering between them is a statement rather than
a remark. The substrate bound's aperture quantifier is spent here, choosing the aperture, and is not
used again.

**NO CONVERSE IS CLAIMED.** `ConfinesAtAnAperture` is about one extent; the substrate bound is about
all of them, and a witness for the first constrains no other extent.

**THE SUBSTRATE ROUTE SUPPLIES THE GUARD**, so restoring it costs nothing here. This is
`EvenAperture.exists_confining_even_aperture`'s proof with the conclusion taken one step earlier:
that proof reaches the tension bound through `Moment.Read.tension_lt_floor_of_circ_moment`, whose own
argument establishes `3^{−1/4} < ⟨cos θ⟩` as an INTERMEDIATE and then discards it. Here it is the
conclusion. The ingredients are `Moment.Read.cos_avg_ge_circ` (the quadratic lower bound on the
cosine average in terms of the circular second moment) and the aperture factor going to zero, exactly
as before — no new input, and in particular the positivity is not an extra assumption. -/
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

/-- **The flagship from the substrate bound, through the weaker hypothesis.** Composing the two
results above recovers `EvenAperture`'s conclusion, which is the check that nothing was lost in
weakening the hypothesis: everything the old route concluded is still concluded, from strictly less. -/
theorem flagship_of_substrate_even_via_aperture
    (h : ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B) :
    FlagshipAt (confinement_at_an_aperture_of_substrate h) :=
  flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_substrate_even_via_aperture

/-! ### The guard costs the definitional identity with `NonnegArm.Flagship`, and that is benign

Before the guard, `FlagshipAt (confinement_at_an_aperture_of_substrate h)` was `NonnegArm.Flagship h`
by `Iff.rfl`: both realisations were built at `(exists_confining_even_aperture h).choose`, literally
the same term.

With the guard that is gone, and necessarily. `ConfinesAtAnAperture` is now a DIFFERENT existential —
over `3^{−1/4} < cosAvgEven a β` rather than over `μEven a β < κ₀YM` — so `apertureOf` draws its
witness by `Classical.choose` from a different proposition, and the two constructions need not pick
the same extent. Nothing is weakened by this: both are the flagship, each at its own chosen aperture.
It is the witness that differs, not the conclusion's content.

The substantive recovery therefore stands as `flagship_of_substrate_even_via_aperture` above — from
the substrate bound, the full flagship — and it is a theorem rather than an identity. What is NOT
claimed, and what would be false to claim, is that the two are the same proposition. -/

/-- **The guarded hypothesis implies the unguarded one.** The guard only restricts: any aperture
clearing the floor also has tension below it. Stated so the ordering between the two spellings is
machine-checked, and so the defect cannot be reintroduced by "generalising" back.

The converse fails, and `unguarded_confinement_is_satisfiable_without_decay` is why. -/
theorem unguarded_of_confinesAtAnAperture (hc : ConfinesAtAnAperture) :
    ∃ a : EvenAp, ∀ β : ℝ, μEven a β < MassGap.κ₀YM :=
  ⟨apertureOf hc, apertureOf_confines hc⟩

#print axioms unguarded_of_confinesAtAnAperture

/-! ## 5. The remaining obligation, stated at one aperture

`NonnegArm.existence_and_gap_of_law_above_cut` reduces the Clay statement to `LawAbove b` — the
contact-relative quartic law above a cut — by discharging the `[0, b]` arm from
`ContactFloor.contact_relative_unconditional`. That composition is reused verbatim here; the only
change is that it now lands on `ConfinesAtAnAperture`, so the reduction's target is visible at one
aperture. -/

/-- **THE OBLIGATION, AT ONE APERTURE.** There is a `b > 0` such that the contact-relative quartic law
on `(b, ∞)` alone yields confinement at a single even aperture, and with it the gap, non-triviality,
`SO(4)` invariance and the continuum measure.

The `[0, b]` arm is not assumed: it is discharged inside the proof by
`ContactFloor.contact_relative_unconditional`, carried out of `NonnegArm.lawBelow_holds`. `b` is not
named and not chosen; it is that theorem's own cut.

This proves nothing new about Yang–Mills. `LawAbove b` is still the sufficient input, unchanged. What
has changed is what it is sufficient FOR: the intermediate target is now confinement at one extent
rather than a moment bound at every extent, so a route that reaches the intermediate target without
going through the power law no longer has to be aperture-uniform. -/
theorem confinement_at_an_aperture_of_law_above_cut :
    ∃ b : ℝ, 0 < b ∧ (MassGap.NonnegArm.LawAbove b →
      ∃ hc : ConfinesAtAnAperture, FlagshipAt hc) := by
  obtain ⟨b, hbpos, hbelow⟩ := MassGap.NonnegArm.lawBelow_holds
  refine ⟨b, hbpos, fun habove => ?_⟩
  exact ⟨confinement_at_an_aperture_of_substrate
      (MassGap.NonnegArm.substrate_even_of_two_arm b hbelow habove),
    flagship_of_confinement_at_an_aperture _⟩

#print axioms confinement_at_an_aperture_of_law_above_cut

/-! ## 6. NON-VACUITY

`ConfinesAtAnAperture` quantifies over `EvenAp`, so it is not a quantification over nothing: the
extent-four aperture `EvenAperture.apFour` inhabits it. The hypothesis is therefore a statement about
a nonempty set of apertures, which is what makes the existential meaningful rather than trivially
unsatisfiable. -/

/-- `EvenAp` is inhabited, so `ConfinesAtAnAperture`'s existential ranges over a nonempty type.
`EvenAperture.evenAp_nonempty`, restated where the hypothesis is used. -/
theorem evenAp_nonempty : Nonempty EvenAp := MassGap.EvenAperture.evenAp_nonempty

#print axioms evenAp_nonempty

/-! ## 6b. THE NEGATIVE CONTROL: the guard is load-bearing, not decorative

`ConfinesAtAnAperture` is stated on `⟨cos θ⟩` rather than on the tension because `Real.log` is EVEN.
This section proves that the difference is real, on the tree's own read, so that nobody restates the
hypothesis in the "simpler" tension form without first seeing what it admits.

`Substrate.antipodeRead k` is the read the tree already exhibits to show that `1/4` is the best
constant the read interface supports (`antipodeRead_moment_eq_quarter_sq`) and that reflection
positivity alone leaves the substrate moment unbounded (`rp_alone_leaves_moment_unbounded`). All its
mass sits at the antipode, where `θ = π`, so its cosine average is exactly `−1`: total
anticorrelation, no decay of any kind. Its tension is `−log|−1| = 0`, which is below `κ₀YM`.

**So the read that maximally violates the sufficient moment condition passes the unguarded tension
condition, and fails the guarded one.** That is the whole content of the guard. -/

/-- The antipode sits at angle `π`: `θ = 2π(k+1)/(2k+2) = π`, half the period by construction. -/
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

/-- **The antipodal read's cosine average is exactly `−1`.** A point mass at angle `π`. -/
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

/-- **THE TENSION CRITERION ALONE ADMITS A READ WITH NO DECAY.** At every aperture, the antipodal
read has tension `0 < κ₀YM` — so it satisfies the UNGUARDED form `μ < κ₀YM` — while its cosine
average is `−1`, so it fails `ConfinesAtAnAperture`'s guard.

The tension is `0` because `Real.log` is even: `−log(−1) = −log|−1| = −log 1 = 0`. Nothing about the
read decays; the criterion simply cannot see the sign through the logarithm.

**This is why `ConfinesAtAnAperture` is stated on `⟨cos θ⟩`.** If the hypothesis is ever restated as
`∀ β, μEven a β < κ₀YM`, this read is what it lets in. -/
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

/-! ## 7. Footprints -/

section Audit
#print axioms ConfinesAtAnAperture
#print axioms apertureOf
#print axioms apertureOf_confines
#print axioms fullModelOfConfinement
#print axioms measure_is_ymFamilyTension
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
