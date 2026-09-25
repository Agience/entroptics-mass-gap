import MassGap.ShareEnvelope
import MassGap.EvenAperture
import MassGap.ContactFloor

/-!
# MassGap.NonnegArm — the contact-relative reduction with the coupling restricted to `0 ≤ β`

`ShareEnvelope.substrate_of_contact_relative_decay` takes its contact-relative quartic law over all
real `β`. This file restates the reduction with that law assumed only on `0 ≤ β`, and routes the
conclusion through the clamped read so the restriction is not lost.

## The clamp

`EvenAperture.readEven a β` reads the correlation at `max β 0`, so `d2Even a β` never evaluates the
model below zero; at `β < 0` it is the `β = 0` value (`d2Even_eq_at_zero`). The hypothesis of
`EvenAperture.existence_and_gap_of_substrate_even` is `∃ B, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B`,
and a law assumed on `0 ≤ β` supplies it, because the only coupling ever fed to the correlation is
`max β 0`. That is `substrate_of_contact_relative_decay_nonneg`.

`substrate_at_nonneg_of_contact_relative_decay_nonneg` is the alternative: the same hypothesis with
the conclusion carrying the side condition `0 ≤ β` on `d2At`. It is stated for the
record and is not used below; it mentions `d2At`, hence `readYMAt`, so its `#print axioms` differs
from the rest of the file's, which is why its audit line sits in its own section.

`nonneg_hypothesis_of_unrestricted` records that the unrestricted law implies the restricted one.
The converse is not stated.

## The two arms

`LawBelow b` and `LawAbove b` are the same quartic contact-relative law on `0 ≤ β ≤ b` and on
`b < β`. `lawBelow_holds` supplies the lower arm from
`ContactFloor.contact_relative_unconditional`. `substrate_even_of_two_arm` merges them: at the
clamped coupling one or the other applies, and `max C₁ C₂` serves both, which needs the contact
value's sign — `wilsonCorrAt_nonneg`, from `Complete.wilson_reflection_positive_at_even` on `EvenAp`
extents at nonnegative coupling.

`existence_and_gap_of_law_above_cut` is the composite: there is a `b > 0` for which `LawAbove b`
alone yields `Flagship`. The lower arm is discharged inside the proof rather than assumed.

## `Flagship`

`Flagship h` writes out the conclusion of `EvenAperture.existence_and_gap_of_substrate_even` as a
predicate on its hypothesis. `flagship_of_substrate_even` is that theorem applied, so the two
propositions agree by type-checking. `measure_is_ymFamilyTension` records by `rfl` that the measure
component is `WilsonModel.ymFamilyTension`, the same family
`WilsonModel.existence_and_gap_of_substrate` uses.

`#print axioms` after every declaration.
-/

namespace MassGap.NonnegArm

open Filter
open MassGap.EvenAperture

/-! ## 1. The clamped read, as the correlation

Two facts about `EvenAperture.readEven` that the rest of the file runs on. -/

/-- `(readEven a β).ρ d = wilsonCorrAt a.1 (max β 0) d`, by `rfl`: the clamped read's weights are the
Wilson correlation evaluated at the clamped coupling. The analogue of `ShareEnvelope.readYMAt_rho`
for `readEven`. It is what lets a hypothesis about `wilsonCorrAt` be fed to a theorem about a
`Moment.Read` without passing through `readYMAt`.

DERIVED: `1` in `Fin (a.1 + 1)` is the lag index's range, one more than the extent `a.1`; `0` in
`max β 0` is the clamp floor, the least coupling the read ever evaluates the correlation at. -/
theorem readEven_rho (a : EvenAp) (β : ℝ) (d : Fin (a.1 + 1)) :
    (readEven a β).ρ d = MassGap.wilsonCorrAt a.1 (max β 0) d := rfl

#print axioms readEven_rho

/-- `0 ≤ wilsonCorrAt a.1 β d` for an `EvenAp` aperture at nonnegative coupling. The first component
of `Complete.wilson_reflection_positive_at_even`, applied at the `m` and the two side conditions the
`EvenAp` structure carries in `a.2`. Used in `substrate_even_of_two_arm` to merge two constants into
their maximum, which needs the contact value's sign.

DERIVED: `0` in `hβ` is the least coupling reflection positivity is available at; `1` in
`Fin (a.1 + 1)` is the lag index's range; `0` in the conclusion is the lower bound on the
correlation. -/
theorem wilsonCorrAt_nonneg (a : EvenAp) {β : ℝ} (hβ : 0 ≤ β) (d : Fin (a.1 + 1)) :
    0 ≤ MassGap.wilsonCorrAt a.1 β d :=
  (MassGap.wilson_reflection_positive_at_even a.1 a.2.choose a.2.choose_spec.1 a.2.choose_spec.2
    hβ).1 d

#print axioms wilsonCorrAt_nonneg

/-! ## 2. The reduction, pointwise

`ShareEnvelope.circ_moment_le_of_contact_relative` is generic in the read. Fed `readEven a β` it
bounds `d2Even a β`, and the coupling it reads the correlation at is `max β 0`, which is nonnegative
whatever `β` is. -/

/-- `d2Even a β ≤ 2 · ∑' k, k² · quarticWeight m₀ C k`, at one aperture and one coupling, from the
contact-relative quartic law at the clamped coupling `max β 0`. `readEven_rho` rewrites the
hypothesis into the shape `ShareEnvelope.circ_moment_le_of_contact_relative` consumes. Because the
hypothesis is asked only at `max β 0`, a law holding on `0 ≤ β` suffices at every real `β`.

DERIVED: `0` in `hC` is the sign of the law's constant; `1` in `Fin (a.1 + 1)` is the lag index's
range; `0` in `max β 0` is the clamp floor; `0` in `wilsonCorrAt … 0` is the contact lag the law is
stated relative to; `4` is the law's decay exponent, `∑ k²·C/k^s` converging exactly when `s > 3`;
the `2` in the exponent `k ^ 2` is the moment's own order and the leading `2` is
`ShareEnvelope.circ_moment_le_of_contact_relative`'s two-sided fold of the circle. -/
theorem d2Even_le_of_contact_relative (a : EvenAp) (β : ℝ) (m₀ : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ d : Fin (a.1 + 1), m₀ ≤ Moment.circLag d →
      MassGap.wilsonCorrAt a.1 (max β 0) d
        ≤ C * MassGap.wilsonCorrAt a.1 (max β 0) 0 / (Moment.circLag d : ℝ) ^ 4) :
    d2Even a β
      ≤ 2 * ∑' k : ℕ, (k : ℝ) ^ 2 * MassGap.ShareEnvelope.quarticWeight m₀ C k := by
  show ∑ d, (readEven a β).p d * (Moment.circLag d : ℝ) ^ 2 ≤ _
  exact MassGap.ShareEnvelope.circ_moment_le_of_contact_relative (readEven a β) m₀ hC
    (fun d hd => by simpa only [readEven_rho] using h d hd)

#print axioms d2Even_le_of_contact_relative

/-- `∃ B, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B`, from the contact-relative quartic law assumed on
`0 ≤ β` only. The witness is `2 · ∑' k, k² · quarticWeight m₀ C k` and each instance is
`d2Even_le_of_contact_relative`, applied at `max β 0` with `le_max_right` discharging the
nonnegativity side condition. The conclusion is in the clamped form
`EvenAperture.existence_and_gap_of_substrate_even` consumes; no coupling below zero is ever fed to
the correlation.

DERIVED: `0` in `hC` is the sign of the constant and `0` in `h`'s `0 ≤ β` is the restricted domain;
`1` in `Fin (N + 1)` is the lag index's range; `0` in `wilsonCorrAt N β 0` is the contact lag; `4` is
the law's decay exponent. -/
theorem substrate_of_contact_relative_decay_nonneg (m₀ : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (N : ℕ) (β : ℝ), 0 ≤ β → ∀ d : Fin (N + 1), m₀ ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d
        ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4) :
    ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B :=
  ⟨2 * ∑' k : ℕ, (k : ℝ) ^ 2 * MassGap.ShareEnvelope.quarticWeight m₀ C k,
    fun a β => d2Even_le_of_contact_relative a β m₀ hC (h a.1 (max β 0) (le_max_right β 0))⟩

#print axioms substrate_of_contact_relative_decay_nonneg

/-- The same hypothesis with the conclusion stated on `d2At`, the moment of `readYMAt`, and carrying the side
condition: `∃ B, ∀ N β, 0 ≤ β → d2At N β ≤ B`. Proved directly from
`ShareEnvelope.circ_moment_le_of_contact_relative` at `readYMAt N β`, with the same witness.

`readYMAt` clamps at `max β 0`, so `d2At N β` at `β < 0` is `d2At N 0` and the side condition
excludes no content; it is kept so that the conclusion is stated on the hypothesis's own domain.
`WilsonModel.existence_and_gap_of_substrate` asks for the bound with no side condition on `β`. This
declaration mentions `d2At` and hence `readYMAt`, so its axiom footprint differs from the clamped
route's; nothing below uses it.

DERIVED: `0` in `hC` is the sign of the constant; the two `0 ≤ β`s are the restricted domain, in the
hypothesis and again in the conclusion; `1` in `Fin (N + 1)` is the lag index's range; `0` in
`wilsonCorrAt N β 0` is the contact lag; `4` is the law's decay exponent. -/
theorem substrate_at_nonneg_of_contact_relative_decay_nonneg (m₀ : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (N : ℕ) (β : ℝ), 0 ≤ β → ∀ d : Fin (N + 1), m₀ ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d
        ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4) :
    ∃ B : ℝ, ∀ (N : ℕ) (β : ℝ), 0 ≤ β → MassGap.d2At N β ≤ B :=
  ⟨2 * ∑' k : ℕ, (k : ℝ) ^ 2 * MassGap.ShareEnvelope.quarticWeight m₀ C k,
    fun N β hβ =>
      MassGap.ShareEnvelope.circ_moment_le_of_contact_relative (MassGap.readYMAt N β) m₀ hC
        (fun d hd => by
          simpa only [MassGap.ShareEnvelope.readYMAt_rho, max_eq_left hβ] using h N β hβ d hd)⟩

#print axioms substrate_at_nonneg_of_contact_relative_decay_nonneg

/-- The contact-relative quartic law stated for all real `β` implies the same law restricted to
`0 ≤ β`. The proof discards the `0 ≤ β` argument. The converse is not stated: the unrestricted form
constrains the correlation at `β < 0` and the restricted form does not.

DERIVED: `1` in both `Fin (N + 1)`s is the lag index's range; `0` in `0 ≤ β` is the restricted
domain the conclusion adds; the `0`s in `wilsonCorrAt N β 0` are the contact lag the law is relative
to; both `4`s are the law's decay exponent, identical on the two sides so the implication is by
weakening alone. -/
theorem nonneg_hypothesis_of_unrestricted (m₀ : ℕ) (C : ℝ)
    (h : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)), m₀ ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d
        ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4) :
    ∀ (N : ℕ) (β : ℝ), 0 ≤ β → ∀ d : Fin (N + 1), m₀ ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d
        ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4 :=
  fun N β _ d hd => h N β d hd

#print axioms nonneg_hypothesis_of_unrestricted

/-- `d2Even a β = d2Even a 0` for `β ≤ 0`: below zero the clamped moment is the `β = 0` moment.
Immediate from `EvenAperture.readEven_eq_at_zero`. So every statement about `d2Even` at negative
coupling is the `β = 0` statement relabelled, and none of them constrains the model there.

DERIVED: `0` in `hβ` is the clamp floor, and `0` on the right is the coupling the clamp maps
everything below it to. -/
theorem d2Even_eq_at_zero (a : EvenAp) {β : ℝ} (hβ : β ≤ 0) : d2Even a β = d2Even a 0 := by
  show ∑ d, (readEven a β).p d * (Moment.circLag d : ℝ) ^ 2 = _
  rw [readEven_eq_at_zero a hβ]
  rfl

#print axioms d2Even_eq_at_zero

/-! ## 3. The conclusion, written out

`Flagship h` is `EvenAperture.existence_and_gap_of_substrate_even`'s conclusion, written once so the
theorems below can be read. `flagship_of_substrate_even` is that theorem applied, so it type-checks
only if the two are the same proposition. -/

/-- The conclusion of `EvenAperture.existence_and_gap_of_substrate_even`, as a predicate on its
hypothesis. Its two components are

* the gap side: at every `β` the correlator norm tends to `0`, the tension deficit `μ β − κ` is
  negative, and `R` is constant across lag pairs;
* the measure side: a subsequence `φ` along which each `Q j` converges to a `q j`, with
  `|q j| ≤ ⌈c⌉₊ · B`, `0 ≤ q j`, and invariance of `q` under both group actions.

DERIVED: no magnitude appears in this statement. Every `0` is a sign or a limit point: `nhds 0` is
the limit the correlator norm reaches, not a level it is compared against; `μ β − κ < 0` is the sign
of the tension deficit; and `0 ≤ q j` is nonnegativity of the limit functional. `B` and `c` are the
hypothesis's and the measure's own, quantified there. -/
def Flagship (h : ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B) : Prop :=
  ((∀ β, Tendsto (fun τ : ℕ => ‖∑ k ∈ (wilsonEven h).model.gap.s β,
        (wilsonEven h).model.gap.P β k
          * ((wilsonEven h).model.gap.m β k) ^ τ‖) atTop (nhds 0)) ∧
      (∀ β, (wilsonEven h).model.gap.μ β - (wilsonEven h).model.gap.κ < 0) ∧
      (∀ d d', (wilsonEven h).model.gap.R d = (wilsonEven h).model.gap.R d')) ∧
    (∃ (q : (wilsonEven h).model.measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ j, Tendsto (fun k => (wilsonEven h).model.measure.Q j (φ k)) atTop (nhds (q j))) ∧
      (∀ j, |q j| ≤ (⌈(wilsonEven h).model.measure.c⌉₊ : ℝ) * (wilsonEven h).model.measure.B) ∧
      (∀ j, 0 ≤ q j) ∧
      (∀ g j, q ((wilsonEven h).model.measure.actE g j) = q j) ∧
      (∀ σ j, q ((wilsonEven h).model.measure.actP σ j) = q j))

#print axioms Flagship

/-- `Flagship h` holds for every `h`. The proof term is
`EvenAperture.existence_and_gap_of_substrate_even` applied to `h` and nothing else, so `Flagship` is
that theorem's conclusion by type-checking rather than by assertion.

DERIVED: no numeral. -/
theorem flagship_of_substrate_even (h : ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B) :
    Flagship h :=
  existence_and_gap_of_substrate_even h

#print axioms flagship_of_substrate_even

/-- `(wilsonEven h).model.measure = WilsonModel.ymFamilyTension`, by `rfl`: the measure component
of the clamped model is the same family `WilsonModel.existence_and_gap_of_substrate` uses. The
substrate bound `h` is consumed by the gap side, and this records that the measure side is unchanged
by the restriction.

DERIVED: no numeral. -/
theorem measure_is_ymFamilyTension (h : ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B) :
    (wilsonEven h).model.measure = MassGap.WilsonModel.ymFamilyTension := rfl

#print axioms measure_is_ymFamilyTension

/-- From the contact-relative quartic law assumed on `0 ≤ β` alone, both the clamped substrate bound
and `Flagship` of it. `substrate_of_contact_relative_decay_nonneg` supplies the bound and
`flagship_of_substrate_even` the conclusion; the result is packaged as a dependent pair so the
`Flagship` is stated about the bound just produced.

DERIVED: `0` in `hC` is the sign of the law's constant and `0` in `0 ≤ β` is its restricted domain;
`1` in `Fin (N + 1)` is the lag index's range; `0` in `wilsonCorrAt N β 0` is the contact lag; `4` is
the law's decay exponent. -/
theorem existence_and_gap_of_contact_relative_nonneg (m₀ : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (N : ℕ) (β : ℝ), 0 ≤ β → ∀ d : Fin (N + 1), m₀ ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d
        ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4) :
    ∃ hsub : (∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B), Flagship hsub :=
  ⟨substrate_of_contact_relative_decay_nonneg m₀ C hC h,
    flagship_of_substrate_even (substrate_of_contact_relative_decay_nonneg m₀ C hC h)⟩

#print axioms existence_and_gap_of_contact_relative_nonneg

/-! ## 4. Composing the two arms

`ContactFloor.contact_relative_unconditional` proves the law on `[0, b]` with its own constant; a
law on `(b, ∞)` comes with a different one. The two are merged into their maximum, which needs the
contact value's sign — `wilsonCorrAt_nonneg`, available on exactly the domain the clamp puts the
argument on. -/

/-- The contact-relative quartic law above the cut `b`: one nonnegative constant `C` serving every
extent, every coupling strictly above `b`, and every lag at circle distance at least one. Written in
the same shape as `LawBelow` so the two compose in `substrate_even_of_two_arm`.

DERIVED: the numerals are identical to `LawBelow`'s, which is what lets the two arms compose. The
exponent `4` is the convergence threshold: `∑ k²·C/k^s` converges exactly when `s > 3`, `4` is the
integer above it, and `ShareEnvelope.cubic_contact_relative_gives_no_bound` refutes `3`. The lag cut
`1` excludes the contact term and nothing else, `StrongArm.exists_geom_quartic_bound` showing a
geometric sequence dominates a quartic outright rather than eventually. `1` in `Fin (N + 1)` is the
lag index's range. The `0`s are the sign of `C` and the contact lag `wilsonCorrAt N β 0` the law is
stated relative to; `b` is the cut, quantified over, and `C` is existential. -/
def LawAbove (b : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)), b < β → 1 ≤ Moment.circLag d →
    MassGap.wilsonCorrAt N β d
      ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4

#print axioms LawAbove

/-- The same law on `0 ≤ β ≤ b`, written in the same shape as `LawAbove` so the two can be read side
by side and merged. `lawBelow_holds` supplies it for some `b > 0`.

DERIVED: the numerals are identical to `LawAbove`'s, which is what lets the two arms compose. The
exponent `4` is the convergence threshold: `∑ k²·C/k^s` converges exactly when `s > 3`, `4` is the
integer above it, and `ShareEnvelope.cubic_contact_relative_gives_no_bound` refutes `3`. The lag cut
`1` excludes the contact term and nothing else. `1` in `Fin (N + 1)` is the lag index's range. The
`0`s are the sign of `C`, the lower end of the coupling interval, and the contact lag
`wilsonCorrAt N β 0` the law is stated relative to. -/
def LawBelow (b : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)), 0 ≤ β → β ≤ b → 1 ≤ Moment.circLag d →
    MassGap.wilsonCorrAt N β d
      ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4

#print axioms LawBelow

/-- `∃ b, 0 < b ∧ LawBelow b`, with no hypothesis. It destructures
`ContactFloor.contact_relative_unconditional` and repackages its cut, constant and bound in
`LawBelow`'s shape; the discarded component is that lemma's own extra conclusion.

DERIVED: `0` is the strict positivity of the cut `b`, carried from
`ContactFloor.contact_relative_unconditional`. -/
theorem lawBelow_holds : ∃ b : ℝ, 0 < b ∧ LawBelow b := by
  obtain ⟨b, hb, _, C, hC, h⟩ := MassGap.ContactFloor.contact_relative_unconditional
  exact ⟨b, hb, C, hC, h⟩

#print axioms lawBelow_holds

/-- `LawBelow b` and `LawAbove b` together give `∃ B, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B`. At the
clamped coupling `max β 0` one of the two arms applies according to `max β 0 ≤ b`, and `max C₁ C₂`
serves both, which needs the contact value nonnegative — `wilsonCorrAt_nonneg` at `max β 0`. The
envelope is then `d2Even_le_of_contact_relative` at `m₀ = 1`.

DERIVED: no numeral. The `1` used as `m₀` and the constants `C₁`, `C₂` come from `LawBelow` and
`LawAbove`, which the statement names rather than unfolds. -/
theorem substrate_even_of_two_arm (b : ℝ) (hb : LawBelow b) (ha : LawAbove b) :
    ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B := by
  obtain ⟨C₁, hC₁, h₁⟩ := hb
  obtain ⟨C₂, hC₂, h₂⟩ := ha
  refine ⟨2 * ∑' k : ℕ, (k : ℝ) ^ 2
      * MassGap.ShareEnvelope.quarticWeight 1 (max C₁ C₂) k, fun a β => ?_⟩
  refine d2Even_le_of_contact_relative a β 1 (le_trans hC₁ (le_max_left _ _)) ?_
  intro d hd
  have hβ0 : (0 : ℝ) ≤ max β 0 := le_max_right β 0
  have hρ0 : 0 ≤ MassGap.wilsonCorrAt a.1 (max β 0) 0 := wilsonCorrAt_nonneg a hβ0 0
  have hL1 : (1 : ℝ) ≤ (Moment.circLag d : ℝ) := by exact_mod_cast hd
  have hL : (0 : ℝ) < (Moment.circLag d : ℝ) ^ 4 :=
    pow_pos (lt_of_lt_of_le zero_lt_one hL1) 4
  have step : ∀ C : ℝ, C ≤ max C₁ C₂ →
      C * MassGap.wilsonCorrAt a.1 (max β 0) 0 / (Moment.circLag d : ℝ) ^ 4
        ≤ max C₁ C₂ * MassGap.wilsonCorrAt a.1 (max β 0) 0 / (Moment.circLag d : ℝ) ^ 4 := by
    intro C hCm
    have hmul : C * MassGap.wilsonCorrAt a.1 (max β 0) 0
        ≤ max C₁ C₂ * MassGap.wilsonCorrAt a.1 (max β 0) 0 :=
      mul_le_mul_of_nonneg_right hCm hρ0
    have := mul_le_mul_of_nonneg_right hmul (le_of_lt (inv_pos.mpr hL))
    simpa only [div_eq_mul_inv] using this
  by_cases hcase : max β 0 ≤ b
  · exact le_trans (h₁ a.1 (max β 0) d hβ0 hcase hd) (step C₁ (le_max_left _ _))
  · exact le_trans (h₂ a.1 (max β 0) d (not_le.mp hcase) hd) (step C₂ (le_max_right _ _))

#print axioms substrate_even_of_two_arm

/-- There is a `b > 0` such that `LawAbove b` alone yields the clamped substrate bound together with
`Flagship` of it. The lower arm is supplied inside the proof by `lawBelow_holds` rather than assumed,
and no coupling below zero appears, the clamped read never evaluating the model there.

`b` is neither named nor chosen here: it is the cut `ContactFloor.contact_relative_unconditional`
produces, carried through `lawBelow_holds`.

DERIVED: `0` is the strict positivity of the cut `b`, inherited from `lawBelow_holds`. -/
theorem existence_and_gap_of_law_above_cut :
    ∃ b : ℝ, 0 < b ∧ (LawAbove b →
      ∃ hsub : (∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B), Flagship hsub) := by
  obtain ⟨b, hbpos, hbelow⟩ := lawBelow_holds
  refine ⟨b, hbpos, fun habove => ?_⟩
  exact ⟨substrate_even_of_two_arm b hbelow habove,
    flagship_of_substrate_even (substrate_even_of_two_arm b hbelow habove)⟩

#print axioms existence_and_gap_of_law_above_cut

/-! ## 5. Footprints -/

section Audit
#print axioms readEven_rho
#print axioms wilsonCorrAt_nonneg
#print axioms d2Even_le_of_contact_relative
#print axioms substrate_of_contact_relative_decay_nonneg
#print axioms nonneg_hypothesis_of_unrestricted
#print axioms d2Even_eq_at_zero
#print axioms Flagship
#print axioms flagship_of_substrate_even
#print axioms measure_is_ymFamilyTension
#print axioms existence_and_gap_of_contact_relative_nonneg
#print axioms LawAbove
#print axioms LawBelow
#print axioms lawBelow_holds
#print axioms substrate_even_of_two_arm
#print axioms existence_and_gap_of_law_above_cut
end Audit

section AuditBridge
-- Mentions `d2At`/`readYMAt`, so its footprint differs from the `readEven` route's. Audited separately
-- for that reason; it is not part of the chain above.
#print axioms substrate_at_nonneg_of_contact_relative_decay_nonneg
end AuditBridge

end MassGap.NonnegArm
