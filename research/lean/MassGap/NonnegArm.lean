import MassGap.ShareEnvelope
import MassGap.EvenAperture
import MassGap.ContactFloor

/-!
# MassGap.NonnegArm — the Clay reduction on the nonnegative half-line

`ShareEnvelope.substrate_of_contact_relative_decay` takes its contact-relative power law over
`∀ (N : ℕ) (β : ℝ)` — the coupling UNRESTRICTED — and `ContactFloor.contact_relative_unconditional`
proves that law on `0 ≤ β ≤ b` only. The open region of the reduction is therefore
`(-∞, 0) ∪ (b, ∞)`, and the left piece is not open in any useful sense: it is unprovable.
`CharacterExpansion.NegControl.su3_kernel_nonneg_iff` proves the Wilson cross kernel is
positive-semidefinite EXACTLY when `0 ≤ β`, so at negative coupling there is no reflection
positivity to have and no statement to prove.

This file removes that piece, and it costs nothing because the flagship already lives without it.

## Why the conclusion has to move too

A hypothesis quantified over `0 ≤ β` cannot produce `∃ B, ∀ N β, d2At N β ≤ B`: for `β < 0`,
`d2At N β` is a perfectly good real number built from `readYMAt N β`, about which a nonnegative-only
hypothesis says nothing at all. Two conclusions are available instead.

* **(a)** Restate the conclusion on the same domain: `∃ B, ∀ N β, 0 ≤ β → d2At N β ≤ B`. This is
  `substrate_at_nonneg_of_contact_relative_decay_nonneg` below. It is true, and it is useless on its
  own, because `WilsonModel.existence_and_gap_of_substrate` does not take it.
* **(b)** Route through the CLAMPED read. `EvenAperture.d2Even a β = d2At a.1 (max β 0)`, so the
  clamped moment never evaluates the model below zero — at `β < 0` it is the `β = 0` column
  relabelled (`EvenAperture.readEven_eq_at_zero`), which is exactly the price the flagship already
  pays and names. The hypothesis of `EvenAperture.existence_and_gap_of_substrate_even` is
  `∃ B, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B`, and a nonnegative-only power law DOES give that,
  because the only coupling ever fed to the correlation is `max β 0`.

(b) is what this file builds. It lands directly on the axiom-free flagship, and the composite is
foundational-only: the route never mentions `readYMAt`, so `wilson_reflection_positive_at` never
enters. The nonnegativity the merge step needs is supplied by the PROVED reflection positivity
`Complete.wilson_reflection_positive_at_even`, which is available precisely on `EvenAp` extents at
nonnegative coupling — the domain the clamp puts us on.

## The continuum half is NOT lost

The obvious trap is that `WilsonModel.existence_and_gap_of_substrate` takes the unrestricted
bounded-moment form for the CONTINUUM half, so a restatement that cannot feed it would buy a
narrower obligation at the cost of the continuum limit. It does not happen here, and the reason is
structural rather than lucky: the measure side takes NO hypothesis. `WilsonModel.ymFamilyTension` is
a fixed object and `WilsonModel.ym_continuum_tension` is foundational-only, so the substrate bound is
consumed entirely by the gap side. `fullModelEven` reuses `ymFamilyTension` verbatim
(`measure_is_ymFamilyTension`, by `rfl`), and the second component of
`existence_and_gap_of_substrate_even` is the same tightness-and-invariance statement about the same
family. Nothing about the continuum limit is weakened, restricted or dropped.

## What is left

`existence_and_gap_of_law_above_cut`: there is a `b > 0` such that `LawAbove b` — the quartic
contact-relative law on `(b, ∞)` alone — yields the gap, non-triviality, `SO(4)` invariance and the
continuum measure. The `[0, b]` arm is discharged INSIDE that theorem from
`ContactFloor.contact_relative_unconditional`; it is not assumed. So the open region is one interval
and the open obligation is one statement.

This proves nothing new about Yang–Mills. It deletes a region that was never provable and never
needed, and puts the reduction on the same half-line as the flagship it feeds.

`#print axioms` after every declaration.
-/

namespace MassGap.NonnegArm

open Filter
open MassGap.EvenAperture

/-! ## 1. The clamped read, as the correlation

Two facts about `EvenAperture.readEven` that the rest of the file runs on. Both are about objects
that carry no named axiom, so the chain below carries none either. -/

/-- **The clamped read's weights ARE the constructed Wilson correlation**, at the clamped coupling.
The analogue of `ShareEnvelope.readYMAt_rho` for `readEven`, and by `rfl` for the same reason.

This is the one lemma that lets a hypothesis about `wilsonCorrAt` be fed to a theorem about a
`Moment.Read` without going through `readYMAt` — which is where the axiom would enter. -/
theorem readEven_rho (a : EvenAp) (β : ℝ) (d : Fin (a.1 + 1)) :
    (readEven a β).ρ d = MassGap.wilsonCorrAt a.1 (max β 0) d := rfl

#print axioms readEven_rho

/-- **The correlation is nonnegative at an even aperture and nonnegative coupling** — from the PROVED
reflection positivity, not the axiom. Used only to merge two power laws with different constants into
one with their maximum, which needs the contact value's sign. -/
theorem wilsonCorrAt_nonneg (a : EvenAp) {β : ℝ} (hβ : 0 ≤ β) (d : Fin (a.1 + 1)) :
    0 ≤ MassGap.wilsonCorrAt a.1 β d :=
  (MassGap.wilson_reflection_positive_at_even a.1 a.2.choose a.2.choose_spec.1 a.2.choose_spec.2
    hβ).1 d

#print axioms wilsonCorrAt_nonneg

/-! ## 2. The reduction, pointwise

`ShareEnvelope.circ_moment_le_of_contact_relative` is generic in the read and carries no axiom. Fed
`readEven a β` it bounds `d2Even a β`, and the coupling it reads the correlation at is `max β 0`,
which is nonnegative whatever `β` is. That is the whole mechanism. -/

/-- **The clamped moment is bounded by the envelope total, at one aperture and one coupling.**

The hypothesis is the contact-relative quartic law AT THE CLAMPED COUPLING `max β 0` only, so a law
that holds on `0 ≤ β` suffices at every real `β`. The bound
`2·∑' k, k²·quarticWeight m₀ C k` is `ShareEnvelope.substrate_of_contact_relative_decay`'s own, and
nothing is fitted. -/
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

/-- **THE REDUCTION ON THE NONNEGATIVE HALF-LINE.**

`ShareEnvelope.substrate_of_contact_relative_decay` with the hypothesis quantified over `0 ≤ β` only,
and the conclusion stated in the clamped form the axiom-free flagship consumes. No coupling below
zero appears anywhere: the correlation is read at `max β 0` and nowhere else. -/
theorem substrate_of_contact_relative_decay_nonneg (m₀ : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (N : ℕ) (β : ℝ), 0 ≤ β → ∀ d : Fin (N + 1), m₀ ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d
        ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4) :
    ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B :=
  ⟨2 * ∑' k : ℕ, (k : ℝ) ^ 2 * MassGap.ShareEnvelope.quarticWeight m₀ C k,
    fun a β => d2Even_le_of_contact_relative a β m₀ hC (h a.1 (max β 0) (le_max_right β 0))⟩

#print axioms substrate_of_contact_relative_decay_nonneg

/-- **OPTION (a), for the record.** The same hypothesis with the conclusion restated on `0 ≤ β`
rather than clamped. It is true and it is a dead end: `WilsonModel.existence_and_gap_of_substrate`
takes `∃ B, ∀ N β, d2At N β ≤ B` with no side condition on `β`, and this does not imply it —
`d2At N β` at `β < 0` is untouched by any nonnegative-only hypothesis.

It mentions `d2At`, hence `readYMAt`, hence the named axiom; the clamped route above does not. -/
theorem substrate_at_nonneg_of_contact_relative_decay_nonneg (m₀ : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (N : ℕ) (β : ℝ), 0 ≤ β → ∀ d : Fin (N + 1), m₀ ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d
        ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4) :
    ∃ B : ℝ, ∀ (N : ℕ) (β : ℝ), 0 ≤ β → MassGap.d2At N β ≤ B :=
  ⟨2 * ∑' k : ℕ, (k : ℝ) ^ 2 * MassGap.ShareEnvelope.quarticWeight m₀ C k,
    fun N β hβ =>
      MassGap.ShareEnvelope.circ_moment_le_of_contact_relative (MassGap.readYMAt N β) m₀ hC
        (fun d hd => by
          simpa only [MassGap.ShareEnvelope.readYMAt_rho] using h N β hβ d hd)⟩

#print axioms substrate_at_nonneg_of_contact_relative_decay_nonneg

/-- **The nonnegative hypothesis is strictly weaker than the unrestricted one**, so nothing that
could be reduced before can fail to be reduced now. The converse is not available and is not claimed:
the unrestricted hypothesis says things at `β < 0` that this one does not. -/
theorem nonneg_hypothesis_of_unrestricted (m₀ : ℕ) (C : ℝ)
    (h : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)), m₀ ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d
        ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4) :
    ∀ (N : ℕ) (β : ℝ), 0 ≤ β → ∀ d : Fin (N + 1), m₀ ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d
        ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4 :=
  fun N β _ d hd => h N β d hd

#print axioms nonneg_hypothesis_of_unrestricted

/-- **THE PRICE, at the level of the moment.** Below zero the clamped moment is the `β = 0` moment.
So the nonnegative reduction claims nothing at negative coupling beyond the `β = 0` claim relabelled
— which is the flagship's existing price (`EvenAperture.readEven_eq_at_zero`,
`EvenAperture.μEven_eq_at_zero`), not a new one this file introduces. -/
theorem d2Even_eq_at_zero (a : EvenAp) {β : ℝ} (hβ : β ≤ 0) : d2Even a β = d2Even a 0 := by
  show ∑ d, (readEven a β).p d * (Moment.circLag d : ℝ) ^ 2 = _
  rw [readEven_eq_at_zero a hβ]
  rfl

#print axioms d2Even_eq_at_zero

/-! ## 3. Wiring it to the flagship

`Flagship h` is `EvenAperture.existence_and_gap_of_substrate_even`'s conclusion, written once so the
theorems below can be read. That it IS that conclusion is not asserted: `flagship_of_substrate_even`
is literally that theorem, and it type-checks only if the two are the same proposition. -/

/-- The conclusion of `EvenAperture.existence_and_gap_of_substrate_even`, as a predicate on its
hypothesis: the mass gap, non-triviality, `SO(4)` invariance, and the continuum measure with its
tightness, bound, positivity and both invariances.

DERIVED: no magnitude appears anywhere in this statement. Every `0` is a sign or a limit point:
`nhds 0` is the assertion that the correlation TENDS TO zero, which is the mass gap itself and not a
level it is compared against; `μ − κ < 0` is the SIGN of the tension deficit; and `0 ≤ q j` is
nonnegativity of the limit functional, not a floor on it. The `4` is not a numeral of the definition
at all — it is the dimension inside the NAME `SO(4)`, the rotation group of the four-dimensional
hypercubic lattice `WilsonBridge.corrClay` is stated on. The one magnitude in sight, `B`, is the
hypothesis's own and is existentially quantified there. -/
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

/-- **`Flagship` is the flagship.** The proof term is
`EvenAperture.existence_and_gap_of_substrate_even` and nothing else, so the abbreviation above is
faithful by type-checking rather than by assertion. -/
theorem flagship_of_substrate_even (h : ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B) :
    Flagship h :=
  existence_and_gap_of_substrate_even h

#print axioms flagship_of_substrate_even

/-- **THE CONTINUUM HALF IS THE SAME OBJECT.** The measure the clamped flagship delivers its
tightness and invariance statements about is `WilsonModel.ymFamilyTension` — by `rfl`, the very
family `WilsonModel.existence_and_gap_of_substrate` uses. So restricting the substrate hypothesis to
the clamped read costs the continuum limit nothing: the measure side never consumed that hypothesis.
-/
theorem measure_is_ymFamilyTension (h : ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B) :
    (wilsonEven h).model.measure = MassGap.WilsonModel.ymFamilyTension := rfl

#print axioms measure_is_ymFamilyTension

/-- **THE WHOLE STATEMENT, FROM A CONTACT-RELATIVE POWER LAW ON `0 ≤ β` ALONE.**

`ShareEnvelope.yang_mills_of_contact_relative_decay` with the coupling restricted to the physical
half-line and the flagship replaced by the axiom-free one. Gap, non-triviality, `SO(4)` invariance
and the continuum measure, from one inequality on the connected plaquette correlation at nonnegative
coupling. -/
theorem existence_and_gap_of_contact_relative_nonneg (m₀ : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (N : ℕ) (β : ℝ), 0 ≤ β → ∀ d : Fin (N + 1), m₀ ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d
        ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4) :
    ∃ hsub : (∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B), Flagship hsub :=
  ⟨substrate_of_contact_relative_decay_nonneg m₀ C hC h,
    flagship_of_substrate_even (substrate_of_contact_relative_decay_nonneg m₀ C hC h)⟩

#print axioms existence_and_gap_of_contact_relative_nonneg

/-! ## 4. Composing the two arms, and what is left

`ContactFloor.contact_relative_unconditional` proves the law on `[0, b]` with its own constant. An
obligation on `(b, ∞)` would come with a different one. Two constants are merged into their maximum,
which needs the contact value's sign — supplied by `wilsonCorrAt_nonneg`, i.e. by the PROVED
reflection positivity on exactly the domain the clamp puts us on. -/

/-- **THE REMAINING OBLIGATION.** The contact-relative quartic law above the cut: one constant, every
aperture, every coupling strictly above `b`, every lag at distance one or more.

Nothing else is open. The same statement on `[0, b]` is `ContactFloor.contact_relative_unconditional`
and is proved; below zero there is nothing to state, because the clamped read never evaluates the
model there.

DERIVED: the numerals are `LawBelow`'s below, kept identical so the two arms compose. The exponent
`4` is the threshold: `∑ k²·C/k^s` converges exactly when `s > 3`, so `4` is the integer above it,
and `ShareEnvelope.cubic_contact_relative_gives_no_bound` proves `3` itself FALSE. The lag cut `1`
excludes the contact term and nothing else, because `StrongArm.exists_geom_quartic_bound` shows a
geometric sequence dominates a quartic outright rather than eventually — there is no cut to name. The
`0`s are the sign of `C`, the contact lag `wilsonCorrAt N β 0` the law is stated RELATIVE to, and the
lower end of the physical coupling domain named in the prose — none of them a magnitude; `b` is the
cut, quantified over, and `C` is existential. -/
def LawAbove (b : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)), b < β → 1 ≤ Moment.circLag d →
    MassGap.wilsonCorrAt N β d
      ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4

#print axioms LawAbove

/-- The same statement on `[0, b]`, written in the same shape so the two arms can be read side by
side.

DERIVED: the numerals are `LawAbove`'s, kept identical so the two arms compose. The exponent `4` is
the threshold: `∑ k²·C/k^s` converges exactly when `s > 3`, so `4` is the integer above it, and
`ShareEnvelope.cubic_contact_relative_gives_no_bound` proves `3` itself FALSE. The lag cut `1`
excludes the contact term and nothing else, because `StrongArm.exists_geom_quartic_bound` shows a
geometric sequence dominates a quartic outright rather than eventually — there is no cut to name. The
`0`s are the lower end of the physical coupling domain and the sign of `C`, neither a magnitude. -/
def LawBelow (b : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)), 0 ≤ β → β ≤ b → 1 ≤ Moment.circLag d →
    MassGap.wilsonCorrAt N β d
      ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4

#print axioms LawBelow

/-- **The lower arm is PROVED** — `ContactFloor.contact_relative_unconditional`, restated in the
shape above. No hypothesis. -/
theorem lawBelow_holds : ∃ b : ℝ, 0 < b ∧ LawBelow b := by
  obtain ⟨b, hb, _, C, hC, h⟩ := MassGap.ContactFloor.contact_relative_unconditional
  exact ⟨b, hb, C, hC, h⟩

#print axioms lawBelow_holds

/-- **Both arms give the clamped substrate bound.** The merge: at the clamped coupling `max β 0`
either the lower arm or the upper applies, and `max C₁ C₂` serves both because the contact value is
nonnegative there. -/
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

/-- **THE OBLIGATION, REDUCED TO ONE INTERVAL.**

There is a `b > 0` such that the contact-relative quartic law on `(b, ∞)` ALONE yields the mass gap,
non-triviality, `SO(4)` invariance and the continuum measure. The `[0, b)` arm is not assumed: it is
discharged inside this proof by `ContactFloor.contact_relative_unconditional`. The negative arm does
not appear, because the clamped read never evaluates the model below zero.

`b` is not named and not chosen here; it is the cut
`ContactFloor.contact_relative_unconditional` produces, carried out of `lawBelow_holds`. -/
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
-- Mentions `d2At`/`readYMAt` by design, so it reports the named axiom. It is option (a), kept as the
-- record of what the unclamped restatement gives; it is not part of the chain above.
#print axioms substrate_at_nonneg_of_contact_relative_decay_nonneg
end AuditBridge

end MassGap.NonnegArm
