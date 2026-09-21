import MassGap.CompactBeta
import MassGap.EvenAperture
import MassGap.ClayAssembly
import MassGap.NonnegArm
import MassGap.ConfinesZero
import MassGap.MomentArms

/-!
# MassGap.SubstrateArms — the substrate bound from THREE arms, with the middle by COMPACTNESS

## What this changes

`EvenAperture.existence_and_gap_of_substrate_even` consumes `∃ B, ∀ a β, d2Even a β ≤ B` — the
substrate bound, uniform in BOTH the aperture and the coupling. The route to it on record runs
through `NonnegArm.substrate_even_of_two_arm`, which needs `LawAbove b`: a QUARTIC DECAY LAW
`ρ(d) ≤ C·ρ(0)/circLag(d)⁴` holding at every coupling above the cut, with ONE constant. That is the
hard estimate, and it is open.

**This file replaces the middle of that obligation with compactness.** Split `[0, ∞)` at two points:

    [0, b]     the strong-coupling arm
    [b, B]     COMPACT — `CompactBeta.d2At_jointUniform_on_Icc_of_uniform_lipschitz`
    [B, ∞)     the weak-coupling arm

and the middle then asks for two things that are not a decay law:

* a bound uniform in the APERTURE at EACH coupling separately (`hmid`), and
* one Lipschitz constant in the coupling, uniform in the aperture (`hlip`).

`hlip` is exactly `ClayAssembly.ClayRemaining.I2_clustering`, which until now **had no consumer
anywhere in the tree** — it was carried in the remaining-obligations structure and read by nothing.
This is what reads it.

## ⛔ What this does NOT do

It does not discharge the three arms. All three are hypotheses here, and the file proves an
implication, not the substrate bound.

What it does is change the SHAPE of what the middle interval needs. A decay law at every coupling in
`(b, B)` with one constant is a statement about the correlation's tail; an aperture-uniform bound at
each coupling plus equicontinuity is a statement about how the moment MOVES with the coupling. They
are different obligations, and `CompactBeta` proves the second suffices on a compact interval.

**Both hypotheses of the compactness step are load-bearing and `CompactBeta` exhibits both failures**
(`equicontinuity_is_load_bearing`, `compactness_is_load_bearing`), so neither can be dropped and the
interval really must be bounded — which is why the two arms are still needed at the ends.
-/

namespace MassGap.SubstrateArms

open MassGap.EvenAperture

/-- **⭐ THE SUBSTRATE BOUND FROM THREE ARMS.** The ends by whatever supplies them, the middle by
compactness.

`hmid` is weaker than a decay law: it asks for an aperture-uniform bound at EACH coupling of the
middle interval, one coupling at a time, with no relation between the constants. `hlip` supplies the
relation, and it is one constant for the whole family.

DERIVED: no numeral of its own. `b` and `B` are the caller's cut points, `L` the caller's Lipschitz
constant, and the `0` is the lower end of the physical coupling domain. -/
theorem substrate_even_of_three_arms
    (b B : ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ (N : ℕ) (x y : ℝ), |MassGap.d2At N x - MassGap.d2At N y| ≤ L * |x - y|)
    (hlow : ∃ B₁ : ℝ, ∀ (N : ℕ), ∀ β ∈ Set.Icc (0 : ℝ) b, MassGap.d2At N β ≤ B₁)
    (hmid : ∀ β ∈ Set.Icc b B, ∃ C : ℝ, ∀ N : ℕ, MassGap.d2At N β ≤ C)
    (hhigh : ∃ B₃ : ℝ, ∀ (N : ℕ), ∀ β : ℝ, B ≤ β → MassGap.d2At N β ≤ B₃) :
    ∃ Bd : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ Bd := by
  obtain ⟨B₁, h₁⟩ := hlow
  obtain ⟨B₂, h₂⟩ :=
    MassGap.CompactBeta.d2At_jointUniform_on_Icc_of_uniform_lipschitz b B L hL hlip hmid
  obtain ⟨B₃, h₃⟩ := hhigh
  refine ⟨max B₁ (max B₂ B₃), fun a β => ?_⟩
  rw [d2Even_eq]
  have hx0 : (0 : ℝ) ≤ max β 0 := le_max_right β 0
  by_cases h : max β 0 ≤ b
  · exact le_trans (h₁ a.1 (max β 0) ⟨hx0, h⟩) (le_max_left _ _)
  · by_cases h' : max β 0 ≤ B
    · exact le_trans (h₂ a.1 (max β 0) ⟨(not_le.mp h).le, h'⟩)
        (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact le_trans (h₃ a.1 (max β 0) ((not_le.mp h').le))
        (le_trans (le_max_right _ _) (le_max_right _ _))

#print axioms substrate_even_of_three_arms

/-- **⭐⭐ AND THE FLAGSHIP FROM THE SAME THREE ARMS**, through
`EvenAperture.existence_and_gap_of_substrate_even`.

So the middle interval's obligation has been moved off a decay law and onto a modulus of continuity,
all the way to the conclusion rather than only to the substrate bound.

DERIVED: no numeral of its own; the cut points and the Lipschitz constant are the caller's. -/
theorem substrate_of_three_arms_reaches_flagship
    (b B : ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ (N : ℕ) (x y : ℝ), |MassGap.d2At N x - MassGap.d2At N y| ≤ L * |x - y|)
    (hlow : ∃ B₁ : ℝ, ∀ (N : ℕ), ∀ β ∈ Set.Icc (0 : ℝ) b, MassGap.d2At N β ≤ B₁)
    (hmid : ∀ β ∈ Set.Icc b B, ∃ C : ℝ, ∀ N : ℕ, MassGap.d2At N β ≤ C)
    (hhigh : ∃ B₃ : ℝ, ∀ (N : ℕ), ∀ β : ℝ, B ≤ β → MassGap.d2At N β ≤ B₃) :
    ∃ h : (∃ Bd : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ Bd),
      (∀ β, Filter.Tendsto (fun τ => ‖∑ k ∈ (wilsonEven h).model.gap.s β,
          (wilsonEven h).model.gap.P β k
            * ((wilsonEven h).model.gap.m β k) ^ τ‖) Filter.atTop (nhds 0)) := by
  refine ⟨substrate_even_of_three_arms b B hL hlip hlow hmid hhigh, ?_⟩
  exact (existence_and_gap_of_substrate_even _).1.1

#print axioms substrate_of_three_arms_reaches_flagship

/-- **⭐⭐ AND THIS IS THE FIRST CONSUMER OF `ClayRemaining.I2_clustering`.**

`I2_clustering` has been carried in the remaining-obligations structure and read by NOTHING — the
flagship route went through `I1_lagTwo` alone. The root's own note already records the dependency
("I2 is upstream of I1, because B5's middle coupling range is the grid route"); what was missing was
a theorem that consumes it. This is that theorem.

It says: **given the clustering modulus, the middle coupling interval needs no decay law.** The two
ends still do.

DERIVED: no numeral of its own; `b` and `B` are the caller's cut points. -/
theorem substrate_even_of_clayRemaining_and_ends
    (R : MassGap.ClayAssembly.ClayRemaining) (b B : ℝ)
    (hlow : ∃ B₁ : ℝ, ∀ (N : ℕ), ∀ β ∈ Set.Icc (0 : ℝ) b, MassGap.d2At N β ≤ B₁)
    (hmid : ∀ β ∈ Set.Icc b B, ∃ C : ℝ, ∀ N : ℕ, MassGap.d2At N β ≤ C)
    (hhigh : ∃ B₃ : ℝ, ∀ (N : ℕ), ∀ β : ℝ, B ≤ β → MassGap.d2At N β ≤ B₃) :
    ∃ Bd : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ Bd := by
  obtain ⟨L, hL, hlip⟩ := R.I2_clustering
  exact substrate_even_of_three_arms b B hL hlip hlow hmid hhigh

#print axioms substrate_even_of_clayRemaining_and_ends

/-! ## ⭐ `d2At` is a ratio of continuous functions with a nonvanishing denominator -/

/-- **`d2At` IS THE RATIO OF TWO FINITE SUMS**, which is what makes every analytic statement about it
a statement about `wilsonCorrAt`.

DERIVED: the `2` is the moment's own exponent. -/
theorem d2At_eq_div (N : ℕ) (β : ℝ) :
    MassGap.d2At N β
      = (∑ d, MassGap.wilsonCorrAt N β d * (Moment.circLag d : ℝ) ^ 2)
          / (∑ d, MassGap.wilsonCorrAt N β d) := by
  show ∑ d, (MassGap.readYMAt N β).p d * (Moment.circLag d : ℝ) ^ 2 = _
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  simp only [Moment.Read.p, MassGap.ShareEnvelope.readYMAt_rho, div_mul_eq_mul_div]

#print axioms d2At_eq_div

/-- **⭐ `d2At` IS CONTINUOUS IN THE COUPLING**, at every aperture, with NO hypothesis.

This was missing from the tree, and its absence is why the modulus of continuity could read as
unknown territory. Every ingredient is unconditional and already proved: `wilsonCorrAt` is continuous
in `β` at every aperture and lag (`ConfinesZero.continuous_wilsonCorrAt`), and the normalising
denominator is bounded away from zero by `wilson_reflection_positive_at`'s SECOND clause at every
aperture and coupling.

**⛔ IT DOES NOT GIVE A LIPSCHITZ CONSTANT, let alone an aperture-uniform one.** Continuity at fixed
`N` is a much weaker statement than `I2_clustering`, which asks for ONE constant across all
apertures. What it does establish is that the object is analytically well behaved, so the remaining
obligation is about the SIZE of the modulus and not about its existence.

DERIVED: no numeral of its own. -/
theorem continuous_d2At (N : ℕ) : Continuous (fun β : ℝ => MassGap.d2At N β) := by
  have hnum : Continuous
      (fun β : ℝ => ∑ d, MassGap.wilsonCorrAt N β d * (Moment.circLag d : ℝ) ^ 2) :=
    continuous_finset_sum _ (fun d _ =>
      (MassGap.ConfinesZero.continuous_wilsonCorrAt N d).mul continuous_const)
  have hden : Continuous (fun β : ℝ => ∑ d, MassGap.wilsonCorrAt N β d) :=
    continuous_finset_sum _ (fun d _ => MassGap.ConfinesZero.continuous_wilsonCorrAt N d)
  have hne : ∀ β : ℝ, (∑ d, MassGap.wilsonCorrAt N β d) ≠ 0 :=
    fun β => ne_of_gt (MassGap.wilson_reflection_positive_at N β).2
  have heq : (fun β : ℝ => MassGap.d2At N β)
      = fun β : ℝ => (∑ d, MassGap.wilsonCorrAt N β d * (Moment.circLag d : ℝ) ^ 2)
          / (∑ d, MassGap.wilsonCorrAt N β d) := funext (fun β => d2At_eq_div N β)
  rw [heq]
  exact hnum.div hden hne

#print axioms continuous_d2At

/-- **AND SO IS THE EVEN-APERTURE MOMENT**, which is the one the flagship route reads.

DERIVED: no numeral of its own. -/
theorem continuous_d2Even (a : EvenAp) : Continuous (fun β : ℝ => d2Even a β) := by
  have h : (fun β : ℝ => d2Even a β) = fun β : ℝ => MassGap.d2At a.1 (max β 0) := by
    funext β; exact d2Even_eq a β
  rw [h]
  exact (continuous_d2At a.1).comp (continuous_id.max continuous_const)

#print axioms continuous_d2Even

/-! ## ⭐ The strong-coupling arm, DISCHARGED -/

/-- **⭐⭐ THE STRONG-COUPLING ARM IS NOT A HYPOTHESIS. IT IS A THEOREM.**

`ContactFloor.contact_relative_unconditional` gives the quartic contact-relative law
`ρ(d) ≤ C·ρ(0)/circLag(d)⁴` on a DERIVED `[0, b]`, at every aperture, with no hypothesis — the
`ContactFloor b` premise is discharged inside it by `contactFloor_holds`. Carrying that across
`ShareEnvelope.circ_moment_le_of_contact_relative` turns it into a bound on the circle second moment,
which is `d2At`.

**⛔ `b` IS EXISTENTIAL AND IS NOT CHOSEN HERE.** It is `contact_relative_unconditional`'s own, and
no numeral is ever named for it — the chain bottoms out in a continuity argument at `β = 0`. The only
property it carries out is `coreRate (16·4) b < 1`.

DERIVED: the `1` is the lag cut `m₀` (it excludes the contact lag and nothing else), the `2` is the
moment's own exponent, and the `0` is the lower end of the physical coupling domain. -/
theorem d2At_bounded_on_strong_arm :
    ∃ b : ℝ, 0 < b ∧
      ∃ B₁ : ℝ, ∀ (N : ℕ), ∀ β ∈ Set.Icc (0 : ℝ) b, MassGap.d2At N β ≤ B₁ := by
  obtain ⟨b, hbpos, _, C, hC, h⟩ := MassGap.ContactFloor.contact_relative_unconditional
  refine ⟨b, hbpos,
    2 * ∑' k : ℕ, (k : ℝ) ^ 2 * MassGap.ShareEnvelope.quarticWeight 1 C k,
    fun N β hβ => ?_⟩
  exact MassGap.ShareEnvelope.circ_moment_le_of_contact_relative (MassGap.readYMAt N β) 1 hC
    (fun d hd => by
      simpa only [MassGap.ShareEnvelope.readYMAt_rho] using h N β d hβ.1 hβ.2 hd)

#print axioms d2At_bounded_on_strong_arm

/-- The same, keyed off `NonnegArm.LawBelow` so it composes with the existing two-arm vocabulary.

DERIVED: as `d2At_bounded_on_strong_arm`. -/
theorem d2At_bounded_of_lawBelow {b : ℝ} (hb : MassGap.NonnegArm.LawBelow b) :
    ∃ B₁ : ℝ, ∀ (N : ℕ), ∀ β ∈ Set.Icc (0 : ℝ) b, MassGap.d2At N β ≤ B₁ := by
  obtain ⟨C, hC, h⟩ := hb
  exact ⟨2 * ∑' k : ℕ, (k : ℝ) ^ 2 * MassGap.ShareEnvelope.quarticWeight 1 C k,
    fun N β hβ =>
      MassGap.ShareEnvelope.circ_moment_le_of_contact_relative (MassGap.readYMAt N β) 1 hC
        (fun d hd => by
          simpa only [MassGap.ShareEnvelope.readYMAt_rho] using h N β d hβ.1 hβ.2 hd)⟩

#print axioms d2At_bounded_of_lawBelow

/-- **THE WEAK END ASKS STRICTLY LESS THAN THE OBLIGATION ALREADY ON THE BOOKS.** `hhigh` follows from
`NonnegArm.LawAbove` at any strictly smaller cut, so the three-arm route cannot be harder at that end
than `NonnegArm.substrate_even_of_two_arm` already is.

It does NOT discharge `hhigh`: `LawAbove` is itself open. What it records is the direction of the
implication.

DERIVED: as `d2At_bounded_on_strong_arm`. -/
theorem d2At_bounded_of_lawAbove {b B : ℝ} (hbB : b < B) (ha : MassGap.NonnegArm.LawAbove b) :
    ∃ B₃ : ℝ, ∀ (N : ℕ), ∀ β : ℝ, B ≤ β → MassGap.d2At N β ≤ B₃ := by
  obtain ⟨C, hC, h⟩ := ha
  exact ⟨2 * ∑' k : ℕ, (k : ℝ) ^ 2 * MassGap.ShareEnvelope.quarticWeight 1 C k,
    fun N β hβ =>
      MassGap.ShareEnvelope.circ_moment_le_of_contact_relative (MassGap.readYMAt N β) 1 hC
        (fun d hd => by
          simpa only [MassGap.ShareEnvelope.readYMAt_rho] using
            h N β d (lt_of_lt_of_le hbB hβ) hd)⟩

#print axioms d2At_bounded_of_lawAbove

/-- **⭐⭐ THE SUBSTRATE BOUND WITH THE STRONG ARM CLOSED.** Two hypotheses remain, not three, and the
cut `b` is returned rather than taken — it is `contact_relative_unconditional`'s own.

DERIVED: no numeral of its own. -/
theorem substrate_even_of_two_remaining_arms
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ (N : ℕ) (x y : ℝ), |MassGap.d2At N x - MassGap.d2At N y| ≤ L * |x - y|) :
    ∃ b : ℝ, 0 < b ∧ ∀ B : ℝ,
      (∀ β ∈ Set.Icc b B, ∃ C : ℝ, ∀ N : ℕ, MassGap.d2At N β ≤ C) →
      (∃ B₃ : ℝ, ∀ (N : ℕ), ∀ β : ℝ, B ≤ β → MassGap.d2At N β ≤ B₃) →
      ∃ Bd : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ Bd := by
  obtain ⟨b, hbpos, hlow⟩ := d2At_bounded_on_strong_arm
  exact ⟨b, hbpos, fun B hmid hhigh =>
    substrate_even_of_three_arms b B hL hlip hlow hmid hhigh⟩

#print axioms substrate_even_of_two_remaining_arms

/-- **⭐⭐ AND FROM `ClayRemaining` DIRECTLY.** Given the clustering modulus, what is left of the
substrate bound is the middle interval and the weak end — the strong end is gone.

DERIVED: no numeral of its own. -/
theorem substrate_even_of_clayRemaining_and_weak_end
    (R : MassGap.ClayAssembly.ClayRemaining) :
    ∃ b : ℝ, 0 < b ∧ ∀ B : ℝ,
      (∀ β ∈ Set.Icc b B, ∃ C : ℝ, ∀ N : ℕ, MassGap.d2At N β ≤ C) →
      (∃ B₃ : ℝ, ∀ (N : ℕ), ∀ β : ℝ, B ≤ β → MassGap.d2At N β ≤ B₃) →
      ∃ Bd : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ Bd := by
  obtain ⟨L, hL, hlip⟩ := R.I2_clustering
  exact substrate_even_of_two_remaining_arms hL hlip

#print axioms substrate_even_of_clayRemaining_and_weak_end

/-! ## ⭐⭐ The same route, AXIOM-FREE, on the even aperture -/

/-- **THE READ DOES NOT SEE A NEGATIVE COUPLING**, and saying so WITHOUT the bridge to `readYMAt` is
what keeps the chain axiom-free.

`readEven a β` is `readA (wilsonCorrAt a.1 (max β 0)) _`, and `max (max β 0) 0 = max β 0`, so the
clamp is `readA_congr` on the correlation alone.

**⛔ GOING VIA `d2Even_eq` WOULD LEAK THE AXIOM.** That lemma is the bridge to `d2At`, hence to
`readYMAt`, hence to `wilson_reflection_positive_at` — `EvenAperture`'s own docstring says the bridge
"mentions `readYMAt` and therefore reports the axiom; that is the point of stating it separately". -/
theorem readEven_clamp (a : EvenAp) (β : ℝ) : readEven a (max β 0) = readEven a β :=
  readA_congr (congrArg (MassGap.wilsonCorrAt a.1) (max_eq_left (le_max_right β 0)))

theorem d2Even_clamp (a : EvenAp) (β : ℝ) : d2Even a β = d2Even a (max β 0) := by
  show ∑ d, (readEven a β).p d * (Moment.circLag d : ℝ) ^ 2
    = ∑ d, (readEven a (max β 0)).p d * (Moment.circLag d : ℝ) ^ 2
  rw [readEven_clamp a β]

/-- **⭐⭐ THE STRONG ARM, AXIOM-FREE.** The same content as `d2At_bounded_on_strong_arm` on the even
aperture, where `NonnegArm.d2Even_le_of_contact_relative` lands directly and `readEven` carries no
named axiom.

DERIVED: the `1` is the lag cut `m₀`, the `2` is the moment's own exponent, and the `0` is the lower
end of the physical coupling domain. -/
theorem d2Even_bounded_on_strong_arm :
    ∃ b : ℝ, 0 < b ∧
      ∃ B₁ : ℝ, ∀ (a : EvenAp), ∀ β ∈ Set.Icc (0 : ℝ) b, d2Even a β ≤ B₁ := by
  obtain ⟨b, hbpos, _, C, hC, h⟩ := MassGap.ContactFloor.contact_relative_unconditional
  refine ⟨b, hbpos,
    2 * ∑' k : ℕ, (k : ℝ) ^ 2 * MassGap.ShareEnvelope.quarticWeight 1 C k,
    fun a β hβ => ?_⟩
  refine MassGap.NonnegArm.d2Even_le_of_contact_relative a β 1 hC (fun d hd => ?_)
  exact h a.1 (max β 0) d (le_max_right β 0) (by rw [max_eq_left hβ.1]; exact hβ.2) hd

#print axioms d2Even_bounded_on_strong_arm

/-- **⭐⭐ THE SUBSTRATE BOUND FROM THREE ARMS, AXIOM-FREE.**

`CompactBeta.jointUniform_on_Icc` is polymorphic in the index type, so the compactness step runs on
`EvenAp` unchanged. Everything here reads `d2Even`, hence `readEven`, hence the PROVED
`wilson_reflection_positive_at_even` rather than the named axiom.

DERIVED: no numeral of its own; `b` and `B` are the caller's cut points and the `0` is the lower end
of the coupling domain. -/
theorem substrate_even_of_three_even_arms
    (b B : ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ (a : EvenAp) (x y : ℝ), |d2Even a x - d2Even a y| ≤ L * |x - y|)
    (hlow : ∃ B₁ : ℝ, ∀ (a : EvenAp), ∀ β ∈ Set.Icc (0 : ℝ) b, d2Even a β ≤ B₁)
    (hmid : ∀ β ∈ Set.Icc b B, ∃ C : ℝ, ∀ a : EvenAp, d2Even a β ≤ C)
    (hhigh : ∃ B₃ : ℝ, ∀ (a : EvenAp), ∀ β : ℝ, B ≤ β → d2Even a β ≤ B₃) :
    ∃ Bd : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ Bd := by
  obtain ⟨B₁, h₁⟩ := hlow
  obtain ⟨B₂, h₂⟩ := MassGap.CompactBeta.jointUniform_on_Icc
    (fun (a : EvenAp) (β : ℝ) => d2Even a β) b B hmid
    (MassGap.CompactBeta.equicontinuousInBeta_of_uniform_lipschitz _ _ L hL hlip)
  obtain ⟨B₃, h₃⟩ := hhigh
  refine ⟨max B₁ (max B₂ B₃), fun a β => ?_⟩
  rw [d2Even_clamp a β]
  have hx0 : (0 : ℝ) ≤ max β 0 := le_max_right β 0
  by_cases h : max β 0 ≤ b
  · exact le_trans (h₁ a (max β 0) ⟨hx0, h⟩) (le_max_left _ _)
  · by_cases h' : max β 0 ≤ B
    · exact le_trans (h₂ a (max β 0) ⟨(not_le.mp h).le, h'⟩)
        (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact le_trans (h₃ a (max β 0) (not_le.mp h').le)
        (le_trans (le_max_right _ _) (le_max_right _ _))

#print axioms substrate_even_of_three_even_arms

/-- **⭐⭐ AND WITH THE STRONG ARM CLOSED, AXIOM-FREE.** Two hypotheses remain: the middle interval's
pointwise aperture-uniformity, and the weak end. The cut `b` is returned, not chosen.

DERIVED: no numeral of its own. -/
theorem substrate_even_of_two_remaining_even_arms
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ (a : EvenAp) (x y : ℝ), |d2Even a x - d2Even a y| ≤ L * |x - y|) :
    ∃ b : ℝ, 0 < b ∧ ∀ B : ℝ,
      (∀ β ∈ Set.Icc b B, ∃ C : ℝ, ∀ a : EvenAp, d2Even a β ≤ C) →
      (∃ B₃ : ℝ, ∀ (a : EvenAp), ∀ β : ℝ, B ≤ β → d2Even a β ≤ B₃) →
      ∃ Bd : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ Bd := by
  obtain ⟨b, hbpos, hlow⟩ := d2Even_bounded_on_strong_arm
  exact ⟨b, hbpos, fun B hmid hhigh =>
    substrate_even_of_three_even_arms b B hL hlip hlow hmid hhigh⟩

#print axioms substrate_even_of_two_remaining_even_arms

/-! ## ⭐⭐ The clustering modulus alone kills the strong arm AND the middle -/

/-- **⭐⭐ THE MODULUS IS ANCHORED AT A POINT WHERE THE MOMENT IS KNOWN EXACTLY.**

`MomentArms.d2Even_at_zero` proves `d2Even a 0 = 0` — at zero coupling the read is a point mass at
the contact lag, so the circle second moment vanishes. An aperture-uniform Lipschitz constant
therefore bounds the moment LINEARLY from that point, at every aperture at once:

    d2Even a β ≤ L · β   for every `a` and every `β ≥ 0`.

**This is not a new estimate.** It is the observation that the modulus has a known anchor, and the
tree already proved the anchor.

DERIVED: the `0` is the coupling at which the moment vanishes, and `L` is the caller's constant. -/
theorem d2Even_le_lipschitz_linear {L : ℝ}
    (hlip : ∀ (a : EvenAp) (x y : ℝ), |d2Even a x - d2Even a y| ≤ L * |x - y|)
    (a : EvenAp) {β : ℝ} (hβ : 0 ≤ β) : d2Even a β ≤ L * β := by
  have h0 : d2Even a 0 = 0 := MassGap.MomentArms.d2Even_at_zero a
  have h := hlip a β 0
  rw [h0, sub_zero, sub_zero, abs_of_nonneg hβ] at h
  exact le_trans (le_abs_self _) h

#print axioms d2Even_le_lipschitz_linear

/-- **⭐⭐⭐ THE SUBSTRATE BOUND FROM THE CLUSTERING MODULUS AND THE WEAK ARM ALONE.**

Both the strong arm and the middle interval are gone: `d2Even_le_lipschitz_linear` bounds the moment
by `L·β` on the whole of `[0, B]` at once, uniformly in the aperture. What survives is the weak end,
where `L·β` grows without bound and the linear bound says nothing.

So the obligation is **two things, not three**: the clustering modulus, and a bound above some cut.

DERIVED: the `0` is the lower end of the coupling domain; `B` and `L` are the caller's. -/
theorem substrate_even_of_clustering_and_weak_arm
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ (a : EvenAp) (x y : ℝ), |d2Even a x - d2Even a y| ≤ L * |x - y|)
    (B : ℝ)
    (hhigh : ∃ B₃ : ℝ, ∀ (a : EvenAp), ∀ β : ℝ, B ≤ β → d2Even a β ≤ B₃) :
    ∃ Bd : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ Bd := by
  obtain ⟨B₃, h₃⟩ := hhigh
  refine ⟨max (L * B) B₃, fun a β => ?_⟩
  rw [d2Even_clamp a β]
  have hx0 : (0 : ℝ) ≤ max β 0 := le_max_right β 0
  by_cases h : max β 0 ≤ B
  · exact le_trans (le_trans (d2Even_le_lipschitz_linear hlip a hx0)
      (mul_le_mul_of_nonneg_left h hL)) (le_max_left _ _)
  · exact le_trans (h₃ a (max β 0) (not_le.mp h).le) (le_max_right _ _)

#print axioms substrate_even_of_clustering_and_weak_arm

/-- `ClayRemaining.I2_clustering` is stated on `d2At`; this is the same content on `d2Even`.

It mentions `d2Even_eq`, the bridge to `d2At`, so it reports the named axiom — which costs nothing
here because `ClayRemaining` carries it anyway.

DERIVED: no numeral of its own; the `0` is the clamp. -/
theorem d2Even_lipschitz_of_clayRemaining (R : MassGap.ClayAssembly.ClayRemaining) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ (a : EvenAp) (x y : ℝ), |d2Even a x - d2Even a y| ≤ L * |x - y| := by
  obtain ⟨L, hL, h⟩ := R.I2_clustering
  refine ⟨L, hL, fun a x y => ?_⟩
  rw [d2Even_eq, d2Even_eq]
  exact le_trans (h a.1 (max x 0) (max y 0))
    (mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs x y 0) hL)

#print axioms d2Even_lipschitz_of_clayRemaining

/-- **⭐⭐⭐ AND SO, FROM `ClayRemaining`, THE SUBSTRATE BOUND NEEDS ONLY THE WEAK ARM.**

`I2_clustering` plus a bound above one cut. The strong arm and the whole middle interval are
consequences, not hypotheses.

DERIVED: no numeral of its own; `B` is the caller's cut. -/
theorem substrate_even_of_clayRemaining_and_weak_arm_only
    (R : MassGap.ClayAssembly.ClayRemaining) (B : ℝ)
    (hhigh : ∃ B₃ : ℝ, ∀ (a : EvenAp), ∀ β : ℝ, B ≤ β → d2Even a β ≤ B₃) :
    ∃ Bd : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ Bd := by
  obtain ⟨L, hL, hlip⟩ := d2Even_lipschitz_of_clayRemaining R
  exact substrate_even_of_clustering_and_weak_arm hL hlip B hhigh

#print axioms substrate_even_of_clayRemaining_and_weak_arm_only

/-! ## ⭐⭐ The modulus, reduced from the MOMENT to the CORRELATION -/

/-- **⭐⭐ A WEIGHTED AVERAGE'S VARIATION IS THE PROFILE'S VARIATION OVER THE TOTAL MASS.**

`d2Even` is a ratio `A/B` of finite sums of the profile, so for two reads

    A/B - A'/B' = (A - A')/B + (A'/B')·(B' - B)/B

which bounds the moment's variation by the profile's `L¹` variation — weighted by the lag weight in
the first term, unweighted in the second, both divided by the first read's own total mass.

**⛔ THIS IS PURE ALGEBRA ON NONNEGATIVE READS.** No analysis, no measure, no Yang–Mills. It is
stated on an arbitrary `Moment.Read` and an arbitrary nonnegative weight precisely so that what it
uses is visible: only `hρ` and `hpos`.

What it buys is that the clustering modulus stops being a statement about `d2Even` and becomes two
statements about the CORRELATION, which is where the Gibbs machinery lives. The denominator is then
bounded below, uniformly in the aperture, by `ContactFloor.contactFloor_holds` at every real cut.

DERIVED: no numeral of its own; `w` is the caller's weight. -/
theorem moment_diff_le_profile_diff {N : ℕ} (R S : Moment.Read N) (w : Fin (N + 1) → ℝ)
    (hw : ∀ d, 0 ≤ w d) :
    |(∑ d, R.p d * w d) - (∑ d, S.p d * w d)|
      ≤ (∑ d, |R.ρ d - S.ρ d| * w d) / (∑ d, R.ρ d)
        + (∑ d, S.p d * w d) * ((∑ d, |R.ρ d - S.ρ d|) / (∑ d, R.ρ d)) := by
  have habs : ∀ x y : ℝ, |x + y| ≤ |x| + |y| := by
    intro x y
    first
      | exact abs_add x y
      | exact abs_add_le x y
      | exact abs_add' x y
  have hsum_sub : ∀ f g : Fin (N + 1) → ℝ,
      (∑ d, f d) - (∑ d, g d) = ∑ d, (f d - g d) := by
    intro f g
    first
      | exact (Finset.sum_sub_distrib).symm
      | exact (Finset.sum_sub_distrib (s := Finset.univ)).symm
      | simp [Finset.sum_sub_distrib]
  have hBpos : 0 < ∑ d, R.ρ d := R.hpos
  have hB'pos : 0 < ∑ d, S.ρ d := S.hpos
  have hRp : (∑ d, R.p d * w d) = (∑ d, R.ρ d * w d) / (∑ d, R.ρ d) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun d _ => by
      simp only [Moment.Read.p, div_mul_eq_mul_div])
  have hSp : (∑ d, S.p d * w d) = (∑ d, S.ρ d * w d) / (∑ d, S.ρ d) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun d _ => by
      simp only [Moment.Read.p, div_mul_eq_mul_div])
  have hnumdiff : |(∑ d, R.ρ d * w d) - (∑ d, S.ρ d * w d)|
      ≤ ∑ d, |R.ρ d - S.ρ d| * w d := by
    rw [hsum_sub]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
    exact Finset.sum_congr rfl (fun d _ => by
      rw [← sub_mul, abs_mul, abs_of_nonneg (hw d)])
  have hdendiff : |(∑ d, S.ρ d) - (∑ d, R.ρ d)| ≤ ∑ d, |R.ρ d - S.ρ d| := by
    rw [abs_sub_comm, hsum_sub]
    exact Finset.abs_sum_le_sum_abs _ _
  have hSnn : 0 ≤ (∑ d, S.ρ d * w d) / (∑ d, S.ρ d) :=
    div_nonneg (Finset.sum_nonneg (fun d _ => mul_nonneg (S.hρ d) (hw d))) hB'pos.le
  rw [hRp, hSp]
  have hsplit : (∑ d, R.ρ d * w d) / (∑ d, R.ρ d) - (∑ d, S.ρ d * w d) / (∑ d, S.ρ d)
      = ((∑ d, R.ρ d * w d) - (∑ d, S.ρ d * w d)) / (∑ d, R.ρ d)
        + ((∑ d, S.ρ d * w d) / (∑ d, S.ρ d))
          * (((∑ d, S.ρ d) - (∑ d, R.ρ d)) / (∑ d, R.ρ d)) := by
    field_simp
    ring
  rw [hsplit]
  refine le_trans (habs _ _) (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos hBpos]
    gcongr
  · rw [abs_mul]
    refine mul_le_mul (le_of_eq (abs_of_nonneg hSnn)) ?_ (abs_nonneg _) hSnn
    rw [abs_div, abs_of_pos hBpos]
    gcongr

#print axioms moment_diff_le_profile_diff

/-! ## ⭐⭐ The substrate bound with the division performed -/

/-- `d2Even` as a ratio of two finite sums of the CORRELATION.

DERIVED: the `2` is the moment's own exponent; the `0` is the clamp. -/
theorem d2Even_eq_div (a : EvenAp) (β : ℝ) :
    d2Even a β
      = (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d * (Moment.circLag d : ℝ) ^ 2)
          / (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d) := by
  show ∑ d, (readEven a β).p d * (Moment.circLag d : ℝ) ^ 2 = _
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  simp only [Moment.Read.p, MassGap.NonnegArm.readEven_rho, div_mul_eq_mul_div]

#print axioms d2Even_eq_div

/-- The total mass is strictly positive at every aperture and coupling — the SECOND clause of the
reflection-positivity statement, which at even extent is a theorem rather than the named axiom. -/
theorem sum_wilsonCorrAt_pos (a : EvenAp) (β : ℝ) :
    0 < ∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d := by
  have h := (readEven a β).hpos
  simpa only [MassGap.NonnegArm.readEven_rho] using h

#print axioms sum_wilsonCorrAt_pos

/-- **⭐⭐ THE SUBSTRATE BOUND, WITH THE DIVISION PERFORMED.**

An EQUIVALENCE, not a weakening: `Den > 0` at every aperture and coupling, so `Num/Den ≤ B` and
`Num ≤ B·Den` say the same thing.

**⛔ THIS DOES NOT MAKE THE ESTIMATE EASIER**, and saying otherwise would be the mistake this
statement exists to avoid. What it does is remove the ratio, leaving two finite sums of
`wilsonCorrAt` — the form `WilsonAnalytic`'s covariance identity and `ContactFloor`'s floor both act
on. The obligation is the same one, stated where the Gibbs machinery can reach it.

DERIVED: the `2` is the moment's own exponent; the `0` is the clamp. -/
theorem substrate_even_iff_weighted_sum :
    (∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B)
      ↔ (∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ),
          (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d * (Moment.circLag d : ℝ) ^ 2)
            ≤ B * (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d)) := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, fun a β => ?_⟩
    have hpos := sum_wilsonCorrAt_pos a β
    have h := hB a β
    rw [d2Even_eq_div] at h
    first
      | rw [div_le_iff hpos] at h
      | rw [div_le_iff₀ hpos] at h
    exact h
  · rintro ⟨B, hB⟩
    refine ⟨B, fun a β => ?_⟩
    have hpos := sum_wilsonCorrAt_pos a β
    rw [d2Even_eq_div]
    first
      | rw [div_le_iff hpos]
      | rw [div_le_iff₀ hpos]
    exact hB a β

#print axioms substrate_even_iff_weighted_sum

end MassGap.SubstrateArms
