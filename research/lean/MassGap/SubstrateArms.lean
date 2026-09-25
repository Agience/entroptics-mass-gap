import MassGap.CompactBeta
import MassGap.EvenAperture
import MassGap.ClayAssembly
import MassGap.NonnegArm
import MassGap.ConfinesZero
import MassGap.MomentArms
import MassGap.WilsonInstance
import MassGap.AsymptoticScaling
import MassGap.GeometricProfile

/-!
# MassGap.SubstrateArms — substrate bounds from three coupling ranges

`EvenAperture.existence_and_gap_of_substrate_even` consumes `∃ B, ∀ a β, d2Even a β ≤ B`, a
substrate bound uniform in both the aperture and the coupling. `NonnegArm.substrate_even_of_two_arm`
reaches that from `LawAbove b`, a quartic decay law `ρ(d) ≤ C·ρ(0)/circLag(d)⁴` holding at every
coupling above the cut with one constant.

The theorems here split `[0, ∞)` at two points instead:

    [0, b]     the strong-coupling range
    [b, B]     `CompactBeta.d2At_jointUniform_on_Icc_of_uniform_lipschitz`
    [B, ∞)     the weak-coupling range

On the middle range the hypotheses are a bound uniform in the aperture at each coupling separately
(`hmid`), and one Lipschitz constant in the coupling, uniform in the aperture (`hlip`). `hlip` has
the shape of `ClayAssembly.ClayRemaining.I2_clustering`, and several theorems below take it from a
`ClayRemaining` record.

The three ranges enter as hypotheses, so the statements are implications. Both hypotheses of the
compactness step are used: `CompactBeta.equicontinuity_is_load_bearing` and
`CompactBeta.compactness_is_load_bearing` exhibit a failure for each, so the middle interval must be
bounded and the two end ranges are handled separately.
-/

namespace MassGap.SubstrateArms

open MassGap.EvenAperture

/-- A bound on `d2Even a β` uniform in the aperture `a : EvenAp` and the coupling `β`, from four
hypotheses covering `[0, b]`, `[b, B]` and `[B, ∞)`.

`hlip` asks for one Lipschitz constant `L` for `fun β => d2At N β`, holding at every aperture `N`
and every pair of couplings. `hlow` asks for a single constant bounding `d2At N β` on
`Set.Icc 0 b`, uniform in `N`. `hmid` asks, at each `β` of `Set.Icc b B` separately, for a bound
uniform in `N`, with no relation between the constants across `β`. `hhigh` asks for a single bound
for all `β ≥ B`, uniform in `N`.

The middle range is discharged by
`CompactBeta.d2At_jointUniform_on_Icc_of_uniform_lipschitz`, which turns `hmid`'s pointwise bounds
together with `hlip`'s equicontinuity into one constant over `Set.Icc b B`. The witness is the
maximum of the three constants, and `d2Even_eq` sends each `β` to `d2At a.1 (max β 0)`, which falls
in one of the three ranges.

DERIVED: the `0` in `hL : 0 ≤ L` is a sign condition on the Lipschitz constant; the `0` in
`Set.Icc (0 : ℝ) b` is the lower endpoint of the range `hlow` covers. `b`, `B` and `L` are the
caller's. -/
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

/-- The same four hypotheses, carried through `EvenAperture.existence_and_gap_of_substrate_even`.

The conclusion is a dependent pair: a proof `h` of the substrate bound
`∃ Bd, ∀ a β, d2Even a β ≤ Bd`, together with the statement that for every `β` the norm of the
mode sum of `wilsonEven h` tends to `0` along `Filter.atTop` in the lag `τ`.

`substrate_even_of_three_arms` supplies `h` from `hlip`, `hlow`, `hmid` and `hhigh`; the second
component is the first clause of `existence_and_gap_of_substrate_even`'s conclusion at that witness.

DERIVED: the `0` in `hL : 0 ≤ L` is a sign condition on the Lipschitz constant; the `0` in
`Set.Icc (0 : ℝ) b` is the lower endpoint of `hlow`'s range; the `0` in `nhds 0` is the limit the
mode sum tends to. -/
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

/-- The substrate bound with the Lipschitz data taken from a `ClayAssembly.ClayRemaining` record
rather than supplied directly.

`R.I2_clustering` yields a constant `L` with `0 ≤ L` and the aperture-uniform Lipschitz estimate on
`d2At`, which are exactly `substrate_even_of_three_arms`'s `hL` and `hlip`. `hlow`, `hmid` and
`hhigh` remain hypotheses, covering `Set.Icc 0 b`, each point of `Set.Icc b B`, and `[B, ∞)`.

DERIVED: the `0` in `Set.Icc (0 : ℝ) b` is the lower endpoint of `hlow`'s coupling range. `b` and
`B` are the caller's cut points. -/
theorem substrate_even_of_clayRemaining_and_ends
    (R : MassGap.ClayAssembly.ClayRemaining) (b B : ℝ)
    (hlow : ∃ B₁ : ℝ, ∀ (N : ℕ), ∀ β ∈ Set.Icc (0 : ℝ) b, MassGap.d2At N β ≤ B₁)
    (hmid : ∀ β ∈ Set.Icc b B, ∃ C : ℝ, ∀ N : ℕ, MassGap.d2At N β ≤ C)
    (hhigh : ∃ B₃ : ℝ, ∀ (N : ℕ), ∀ β : ℝ, B ≤ β → MassGap.d2At N β ≤ B₃) :
    ∃ Bd : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ Bd := by
  obtain ⟨L, hL, hlip⟩ := R.I2_clustering
  exact substrate_even_of_three_arms b B hL hlip hlow hmid hhigh

#print axioms substrate_even_of_clayRemaining_and_ends

/-! ## `d2At` as a ratio of continuous functions with a nonvanishing denominator -/

/-- `d2At N β` as a ratio of two finite sums of `wilsonCorrAt` at the clamped coupling `max β 0`: the
circle-lag second moment of the correlation over its total mass. The proof unfolds `Moment.Read.p` on
`readYMAt N β`, whose profile is `wilsonCorrAt N (max β 0)`, and distributes the division across the
sum.

DERIVED: the `2` is the exponent on the circle lag, the moment's own power; `0` is the clamp point in
`max β 0`. -/
theorem d2At_eq_div (N : ℕ) (β : ℝ) :
    MassGap.d2At N β
      = (∑ d, MassGap.wilsonCorrAt N (max β 0) d * (Moment.circLag d : ℝ) ^ 2)
          / (∑ d, MassGap.wilsonCorrAt N (max β 0) d) := by
  show ∑ d, (MassGap.readYMAt N β).p d * (Moment.circLag d : ℝ) ^ 2 = _
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  simp only [Moment.Read.p, MassGap.ShareEnvelope.readYMAt_rho, div_mul_eq_mul_div]

#print axioms d2At_eq_div

/-- `fun β => d2At N β` is continuous, at every aperture `N`, with no hypothesis.

Numerator and denominator of `d2At_eq_div` are finite sums of `wilsonCorrAt N (max · 0) d`, each
continuous in `β` by `ConfinesZero.continuous_wilsonCorrAt` composed with the continuity of
`fun β => max β 0`. The denominator is nonzero at every `β` by `(readYMAt N β).hpos`, the second
clause of `wilson_reflection_positive_at` at the nonnegative coupling `max β 0`, which gives
`0 < ∑ d, wilsonCorrAt N (max β 0) d`, so `Continuous.div` applies.

`N` is fixed in the statement, so this yields no Lipschitz constant and nothing uniform across
apertures; `ClayRemaining.I2_clustering` asks for one constant covering all of them.

DERIVED: no numeral appears in the statement. -/
theorem continuous_d2At (N : ℕ) : Continuous (fun β : ℝ => MassGap.d2At N β) := by
  have hmax : Continuous (fun β : ℝ => max β 0) := continuous_id.max continuous_const
  have hnum : Continuous
      (fun β : ℝ => ∑ d, MassGap.wilsonCorrAt N (max β 0) d * (Moment.circLag d : ℝ) ^ 2) :=
    continuous_finset_sum _ (fun d _ =>
      ((MassGap.ConfinesZero.continuous_wilsonCorrAt N d).comp hmax).mul continuous_const)
  have hden : Continuous (fun β : ℝ => ∑ d, MassGap.wilsonCorrAt N (max β 0) d) :=
    continuous_finset_sum _ (fun d _ =>
      (MassGap.ConfinesZero.continuous_wilsonCorrAt N d).comp hmax)
  have hne : ∀ β : ℝ, (∑ d, MassGap.wilsonCorrAt N (max β 0) d) ≠ 0 :=
    fun β => ne_of_gt (MassGap.readYMAt N β).hpos
  have heq : (fun β : ℝ => MassGap.d2At N β)
      = fun β : ℝ => (∑ d, MassGap.wilsonCorrAt N (max β 0) d * (Moment.circLag d : ℝ) ^ 2)
          / (∑ d, MassGap.wilsonCorrAt N (max β 0) d) := funext (fun β => d2At_eq_div N β)
  rw [heq]
  exact hnum.div hden hne

#print axioms continuous_d2At

/-- `fun β => d2Even a β` is continuous at every `a : EvenAp`. `d2Even_eq` rewrites it as
`d2At a.1 (max β 0)`, and `continuous_d2At` composes with the continuity of `fun β => max β 0`.

DERIVED: no numeral appears in the statement. -/
theorem continuous_d2Even (a : EvenAp) : Continuous (fun β : ℝ => d2Even a β) := by
  have h : (fun β : ℝ => d2Even a β) = fun β : ℝ => MassGap.d2At a.1 (max β 0) := by
    funext β; exact d2Even_eq a β
  rw [h]
  exact (continuous_d2At a.1).comp (continuous_id.max continuous_const)

#print axioms continuous_d2Even

/-! ## The strong-coupling range -/

/-- There is a cut `b > 0` and a constant `B₁` bounding `d2At N β` at every aperture `N` and every
`β ∈ Set.Icc 0 b`, with no hypothesis.

`ContactFloor.contact_relative_unconditional` supplies `b` together with the quartic
contact-relative estimate `ρ(d) ≤ C·ρ(0)/circLag(d)⁴` on that range at every aperture; its own
`ContactFloor b` premise is discharged internally by `contactFloor_holds`.
`ShareEnvelope.circ_moment_le_of_contact_relative` carries that estimate to the circle second
moment, which is `d2At`.

`b` is existential and no value is named for it: it is `contact_relative_unconditional`'s, reached
there by a continuity argument at `β = 0`, and the property carried out alongside it is
`coreRate (16·4) b < 1`.

DERIVED: the `0` in `0 < b` is a sign condition on the cut, and the `0` in `Set.Icc (0 : ℝ) b` is
the lower endpoint of the range. The `1` passed to `quarticWeight` as the lag cut and the `2` in the
tail sum's exponent occur in the proof term, not in the statement. -/
theorem d2At_bounded_on_strong_arm :
    ∃ b : ℝ, 0 < b ∧
      ∃ B₁ : ℝ, ∀ (N : ℕ), ∀ β ∈ Set.Icc (0 : ℝ) b, MassGap.d2At N β ≤ B₁ := by
  obtain ⟨b, hbpos, _, C, hC, h⟩ := MassGap.ContactFloor.contact_relative_unconditional
  refine ⟨b, hbpos,
    2 * ∑' k : ℕ, (k : ℝ) ^ 2 * MassGap.ShareEnvelope.quarticWeight 1 C k,
    fun N β hβ => ?_⟩
  exact MassGap.ShareEnvelope.circ_moment_le_of_contact_relative (MassGap.readYMAt N β) 1 hC
    (fun d hd => by
      simpa only [MassGap.ShareEnvelope.readYMAt_rho, max_eq_left hβ.1] using
        h N β d hβ.1 hβ.2 hd)

#print axioms d2At_bounded_on_strong_arm

/-- The same bound on `Set.Icc 0 b`, taking `NonnegArm.LawBelow b` as a hypothesis instead of
producing the cut, so that it composes with the two-arm vocabulary. `LawBelow b` unfolds to a
constant `C ≥ 0` and the quartic contact-relative estimate below the cut, and
`ShareEnvelope.circ_moment_le_of_contact_relative` turns that into the moment bound.

DERIVED: the `0` in `Set.Icc (0 : ℝ) b` is the lower endpoint of the coupling range. `b` is the
caller's. -/
theorem d2At_bounded_of_lawBelow {b : ℝ} (hb : MassGap.NonnegArm.LawBelow b) :
    ∃ B₁ : ℝ, ∀ (N : ℕ), ∀ β ∈ Set.Icc (0 : ℝ) b, MassGap.d2At N β ≤ B₁ := by
  obtain ⟨C, hC, h⟩ := hb
  exact ⟨2 * ∑' k : ℕ, (k : ℝ) ^ 2 * MassGap.ShareEnvelope.quarticWeight 1 C k,
    fun N β hβ =>
      MassGap.ShareEnvelope.circ_moment_le_of_contact_relative (MassGap.readYMAt N β) 1 hC
        (fun d hd => by
          simpa only [MassGap.ShareEnvelope.readYMAt_rho, max_eq_left hβ.1] using
            h N β d hβ.1 hβ.2 hd)⟩

#print axioms d2At_bounded_of_lawBelow

/-- `NonnegArm.LawAbove b` gives a constant `B₃` bounding `d2At N β` at every aperture `N` for all
`β ≥ B`, whenever `b < B`.

`LawAbove b` unfolds to a constant `C ≥ 0` and the quartic contact-relative estimate at every
coupling strictly above `b`; `hbB : b < B` places `Set.Ici B` inside that range, and
`ShareEnvelope.circ_moment_le_of_contact_relative` carries the estimate to the moment. This is the
shape `hhigh` takes in `substrate_even_of_three_arms`. `LawAbove` is a hypothesis here.

DERIVED: no numeral appears in the statement; the `1` naming `quarticWeight`'s lag cut and the `2`
in the tail sum's exponent occur in the proof term. -/
theorem d2At_bounded_of_lawAbove {b B : ℝ} (hbB : b < B) (ha : MassGap.NonnegArm.LawAbove b) :
    ∃ B₃ : ℝ, ∀ (N : ℕ), ∀ β : ℝ, B ≤ β → MassGap.d2At N β ≤ B₃ := by
  obtain ⟨C, hC, h⟩ := ha
  exact ⟨2 * ∑' k : ℕ, (k : ℝ) ^ 2 * MassGap.ShareEnvelope.quarticWeight 1 C k,
    fun N β hβ =>
      MassGap.ShareEnvelope.circ_moment_le_of_contact_relative (MassGap.readYMAt N β) 1 hC
        (fun d hd => by
          simpa only [MassGap.ShareEnvelope.readYMAt_rho] using
            h N (max β 0) d (lt_of_lt_of_le (lt_of_lt_of_le hbB hβ) (le_max_left β 0)) hd)⟩

#print axioms d2At_bounded_of_lawAbove

/-- The substrate bound with the strong-coupling range supplied internally by
`d2At_bounded_on_strong_arm`. The cut `b` is returned rather than taken, so it is
`ContactFloor.contact_relative_unconditional`'s.

`hL` and `hlip` give the aperture-uniform Lipschitz data. Inside the returned quantifier, for each
`B`, the caller still supplies the pointwise aperture-uniform bounds on `Set.Icc b B` and the bound
for `β ≥ B`; `substrate_even_of_three_arms` assembles the three.

DERIVED: the `0` in `hL : 0 ≤ L` is a sign condition on the Lipschitz constant, and the `0` in
`0 < b` is a sign condition on the returned cut. -/
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

/-- The same, with the Lipschitz data read off `ClayAssembly.ClayRemaining.I2_clustering` instead of
supplied. What remains inside the returned quantifier, for each `B`, is the pointwise
aperture-uniform bound on `Set.Icc b B` and the bound for `β ≥ B`.

DERIVED: the `0` in `0 < b` is a sign condition on the returned cut. -/
theorem substrate_even_of_clayRemaining_and_weak_end
    (R : MassGap.ClayAssembly.ClayRemaining) :
    ∃ b : ℝ, 0 < b ∧ ∀ B : ℝ,
      (∀ β ∈ Set.Icc b B, ∃ C : ℝ, ∀ N : ℕ, MassGap.d2At N β ≤ C) →
      (∃ B₃ : ℝ, ∀ (N : ℕ), ∀ β : ℝ, B ≤ β → MassGap.d2At N β ≤ B₃) →
      ∃ Bd : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ Bd := by
  obtain ⟨L, hL, hlip⟩ := R.I2_clustering
  exact substrate_even_of_two_remaining_arms hL hlip

#print axioms substrate_even_of_clayRemaining_and_weak_end

/-! ## The same route on the even aperture -/

/-- `readEven a (max β 0) = readEven a β`: clamping the coupling at zero leaves the even-aperture
read unchanged.

`readEven a β` is `readA (wilsonCorrAt a.1 (max β 0)) _`, and `max (max β 0) 0 = max β 0`, so both
sides are reads of the same correlation and `readA_congr` closes it. The proof mentions
`wilsonCorrAt` only, not `readYMAt`, so it does not report the named reflection-positivity axiom;
`d2Even_eq` is the bridge to `d2At` and does mention `readYMAt`.

DERIVED: the `0` is the clamp point, the lower end of the physical coupling range. -/
theorem readEven_clamp (a : EvenAp) (β : ℝ) : readEven a (max β 0) = readEven a β :=
  readA_congr (congrArg (MassGap.wilsonCorrAt a.1) (max_eq_left (le_max_right β 0)))

theorem d2Even_clamp (a : EvenAp) (β : ℝ) : d2Even a β = d2Even a (max β 0) := by
  show ∑ d, (readEven a β).p d * (Moment.circLag d : ℝ) ^ 2
    = ∑ d, (readEven a (max β 0)).p d * (Moment.circLag d : ℝ) ^ 2
  rw [readEven_clamp a β]

/-- The strong-range bound stated on `d2Even` over `EvenAp`, rather than on `d2At` at an arbitrary
aperture. `ContactFloor.contact_relative_unconditional` supplies the cut `b` and the quartic
contact-relative estimate, and `NonnegArm.d2Even_le_of_contact_relative` lands on `d2Even`
directly. The chain reads `readEven`, so it does not report the named axiom.

DERIVED: the `0` in `0 < b` is a sign condition on the returned cut, and the `0` in
`Set.Icc (0 : ℝ) b` is the lower endpoint of the range. The `1` passed to `quarticWeight` and the
`2` in the tail sum's exponent occur in the proof term only. -/
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

/-- The three-range substrate bound stated throughout on `d2Even` and `EvenAp`.

`hlip` asks for one Lipschitz constant in the coupling, uniform over `EvenAp`; `hlow`, `hmid` and
`hhigh` are the bound on `Set.Icc 0 b`, the pointwise bounds at each `β ∈ Set.Icc b B`, and the
bound for `β ≥ B`. `CompactBeta.jointUniform_on_Icc` is polymorphic in the index type, so the
compactness step runs on `EvenAp` unchanged, with
`CompactBeta.equicontinuousInBeta_of_uniform_lipschitz` converting `hlip`. The reduction to
`max β 0` uses `d2Even_clamp`, so the proof reads `d2Even`, hence `readEven`, hence
`wilson_reflection_positive_at_even` rather than the named axiom.

DERIVED: the `0` in `hL : 0 ≤ L` is a sign condition on the Lipschitz constant, and the `0` in
`Set.Icc (0 : ℝ) b` is the lower endpoint of `hlow`'s range. `b` and `B` are the caller's. -/
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

/-- The even-aperture substrate bound with the strong range supplied by
`d2Even_bounded_on_strong_arm`, whose cut `b` is what this returns. Inside the returned quantifier,
for each `B`, the caller supplies the pointwise aperture-uniform bound on `Set.Icc b B` and the
bound for `β ≥ B`.

DERIVED: the `0` in `hL : 0 ≤ L` is a sign condition on the Lipschitz constant, and the `0` in
`0 < b` is a sign condition on the returned cut. -/
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

/-! ## The clustering modulus over the strong and middle ranges -/

/-- An aperture-uniform Lipschitz constant bounds the even-aperture moment linearly above zero
coupling: `d2Even a β ≤ L * β` at every `a : EvenAp` and every `β ≥ 0`.

`MomentArms.d2Even_at_zero` gives `d2Even a 0 = 0` — at zero coupling the read is a point mass at
the contact lag, so the circle second moment vanishes. `hlip` at the pair `β, 0` then reads
`|d2Even a β| ≤ L * |β|`, and `hβ` strips both absolute values.

`hlip` and `L` are the caller's, and `L`'s nonnegativity is not among the hypotheses.

DERIVED: the `0` in `hβ : 0 ≤ β` is the sign condition on the coupling. The anchor `d2Even a 0 = 0`
enters through the proof and is not part of the statement. -/
theorem d2Even_le_lipschitz_linear {L : ℝ}
    (hlip : ∀ (a : EvenAp) (x y : ℝ), |d2Even a x - d2Even a y| ≤ L * |x - y|)
    (a : EvenAp) {β : ℝ} (hβ : 0 ≤ β) : d2Even a β ≤ L * β := by
  have h0 : d2Even a 0 = 0 := MassGap.MomentArms.d2Even_at_zero a
  have h := hlip a β 0
  rw [h0, sub_zero, sub_zero, abs_of_nonneg hβ] at h
  exact le_trans (le_abs_self _) h

#print axioms d2Even_le_lipschitz_linear

/-- The substrate bound from aperture-uniform Lipschitz data and a bound above one cut.

On `[0, B]`, `d2Even_le_lipschitz_linear` bounds `d2Even a β` by `L * β`, and `hL` carries that to
`L * B` at every aperture at once. Above `B`, `hhigh` supplies `B₃`. The witness is
`max (L * B) B₃`, with `d2Even_clamp` sending each `β` to the nonnegative `max β 0`.

`hhigh` is a hypothesis: the linear bound grows without limit in `β`, so it constrains nothing above
a cut. No separate hypothesis covers the middle range.

DERIVED: the `0` in `hL : 0 ≤ L` is a sign condition on the Lipschitz constant. `B` and `L` are the
caller's. -/
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

/-- `ClayAssembly.ClayRemaining.I2_clustering` is stated on `d2At` at an arbitrary aperture; this
restates the same constant on `d2Even` over `EvenAp`.

`d2Even_eq` rewrites both sides as `d2At a.1 (max · 0)`, and `abs_max_sub_max_le_abs` shows the
clamp is nonexpansive, so the same `L` serves. The proof uses `d2Even_eq`, the bridge to `d2At` and
hence to `readYMAt`, so it reports the named axiom; `ClayRemaining` carries that axiom already.

DERIVED: the `0` in `0 ≤ L` is a sign condition on the returned Lipschitz constant, inherited from
`I2_clustering`. The clamp `max x 0` is in the proof, not the statement. -/
theorem d2Even_lipschitz_of_clayRemaining (R : MassGap.ClayAssembly.ClayRemaining) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ (a : EvenAp) (x y : ℝ), |d2Even a x - d2Even a y| ≤ L * |x - y| := by
  obtain ⟨L, hL, h⟩ := R.I2_clustering
  refine ⟨L, hL, fun a x y => ?_⟩
  rw [d2Even_eq, d2Even_eq]
  exact le_trans (h a.1 (max x 0) (max y 0))
    (mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs x y 0) hL)

#print axioms d2Even_lipschitz_of_clayRemaining

/-- The substrate bound from a `ClayRemaining` record together with a bound above one cut.

`d2Even_lipschitz_of_clayRemaining` turns `R.I2_clustering` into the even-aperture Lipschitz data,
and `substrate_even_of_clustering_and_weak_arm` covers `[0, B]` linearly and `[B, ∞)` by `hhigh`.
Neither a strong-range nor a middle-range bound appears as a hypothesis.

DERIVED: no numeral appears in the statement. `B` is the caller's cut. -/
theorem substrate_even_of_clayRemaining_and_weak_arm_only
    (R : MassGap.ClayAssembly.ClayRemaining) (B : ℝ)
    (hhigh : ∃ B₃ : ℝ, ∀ (a : EvenAp), ∀ β : ℝ, B ≤ β → d2Even a β ≤ B₃) :
    ∃ Bd : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ Bd := by
  obtain ⟨L, hL, hlip⟩ := d2Even_lipschitz_of_clayRemaining R
  exact substrate_even_of_clustering_and_weak_arm hL hlip B hhigh

#print axioms substrate_even_of_clayRemaining_and_weak_arm_only

/-! ## The modulus reduced from the moment to the correlation -/

/-- The difference of two normalised weighted averages, bounded by the profiles' `L¹` difference
over the first read's total mass.

`Moment.Read.p` is `ρ d / ∑ ρ`, so each side is a ratio, and

    A/B - A'/B' = (A - A')/B + (A'/B')·(B' - B)/B

splits the difference into a weighted term and an unweighted term, both divided by `∑ d, R.ρ d`.
`Moment.Read.hpos` makes the two total masses positive, and `Moment.Read.hρ` together with `hw`
supplies the nonnegativity the comparison steps need.

The statement is over an arbitrary `Moment.Read N` and an arbitrary nonnegative weight `w`, so it
uses only `hρ` and `hpos`. Nothing about the Yang-Mills correlation enters. It converts a statement
about `d2Even` into two statements about the correlation, with the denominator available from
`ContactFloor.contactFloor_holds`.

DERIVED: the `1` in `Fin (N + 1)` is the index offset, the number of lags a read of aperture `N`
carries. The `0` in `hw : ∀ d, 0 ≤ w d` is a sign condition on the weight. `w` is the caller's. -/
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

/-- A Lipschitz constant for the raw lag second moment of `readYMAt N` on `Set.Icc a b`, produced
rather than assumed. This is the shape `ym_crossover_confinement_of_grid` takes as its `hlip`.

Four ingredients combine, and no derivative bound is used:

* `moment_diff_le_profile_diff` bounds this quantity for any nonnegative weight, by the profile
  differences over the profile sum;
* `ConfinesZero.lipschitz_wilsonCorrAt` bounds each profile difference by `K * |x - y|`, where
  `K = 48 * Fintype.card (WilsonHypercubic.Plaq 4 (N + 1))`;
* `ConfinesZero.exists_profile_sum_floor` bounds the denominator below by a positive `m` on the
  interval, which `Moment.Read.hpos` cannot do — it gives `0 < ∑ ρ` with no constant;
* `Moment.Read.p_sum` and `p_nonneg` make the weighted average at most the largest weight
  `W = (N : ℝ) ^ 2`.

The witness is `2 * ((N : ℝ) + 1) * K * W / m`. The constant is not uniform in the aperture: `K`
carries `Fintype.card Plaq` and `W` carries `N ^ 2`. `ym_crossover_confinement_of_grid` is applied
at the pinned aperture `nCorrYM = 16`, where `μYM_is_μYMAt` holds by `rfl`. A volume-uniform
argument would take a different route, `expect_lipschitz_local`, which carries a clustering
hypothesis.

DERIVED: the `0` in `ha : 0 ≤ a` is the sign condition on the left endpoint, and the `0` in `0 ≤ L`
is a sign condition on the returned constant. The `1` in `Fin (N + 1)` is the index offset, since
`readYMAt N` reads `N + 1` lags. The `2` in `(d : ℝ) ^ 2` is the lag moment's own power. The factor
`2` in the witness and the `48` in `K` appear in the proof only — the first from the two terms
`moment_diff_le_profile_diff` produces, the second from
`ConfinesZero.lipschitz_wilsonCorrConn`. -/
theorem exists_lipschitz_lag_moment {a b : ℝ} (ha : 0 ≤ a) (N : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |(∑ d : Fin (N + 1), (MassGap.readYMAt N x).p d * (d : ℝ) ^ 2)
        - (∑ d : Fin (N + 1), (MassGap.readYMAt N y).p d * (d : ℝ) ^ 2)| ≤ L * |x - y| := by
  classical
  obtain ⟨m, hm, hfloor⟩ := MassGap.ConfinesZero.exists_profile_sum_floor (a := a) (b := b) ha
  set K : ℝ := 48 * (Fintype.card (MassGap.WilsonHypercubic.Plaq 4 (N + 1)) : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  set W : ℝ := (N : ℝ) ^ 2 with hW
  have hW0 : 0 ≤ W := by positivity
  have hwle : ∀ d : Fin (N + 1), ((d : ℝ)) ^ 2 ≤ W := by
    intro d
    have hd : ((d : ℝ)) ≤ (N : ℝ) := by
      have := Nat.lt_succ_iff.mp d.isLt
      exact_mod_cast this
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
    nlinarith [hd, hd0]
  have hw0 : ∀ d : Fin (N + 1), (0 : ℝ) ≤ ((d : ℝ)) ^ 2 := fun d => by positivity
  refine ⟨2 * ((N : ℝ) + 1) * K * W / m, div_nonneg (by positivity) hm.le, ?_⟩
  intro x hx y hy
  -- `0 ≤ a` puts both couplings on the nonnegative range, where the read's clamp is inert.
  have hρx : (MassGap.readYMAt N x).ρ = MassGap.wilsonCorrAt N x := by
    rw [MassGap.readYMAt_rho_max, max_eq_left (le_trans ha hx.1)]
  have hρy : (MassGap.readYMAt N y).ρ = MassGap.wilsonCorrAt N y := by
    rw [MassGap.readYMAt_rho_max, max_eq_left (le_trans ha hy.1)]
  have hden : m ≤ ∑ d : Fin (N + 1), (MassGap.readYMAt N x).ρ d := by
    rw [hρx]; exact hfloor N x hx
  have hdenpos : (0 : ℝ) < ∑ d : Fin (N + 1), (MassGap.readYMAt N x).ρ d :=
    lt_of_lt_of_le hm hden
  have hxy : (0 : ℝ) ≤ |x - y| := abs_nonneg _
  -- each profile difference
  have hdiffle : ∀ d : Fin (N + 1),
      |(MassGap.readYMAt N x).ρ d - (MassGap.readYMAt N y).ρ d| ≤ K * |x - y| := by
    intro d
    rw [hρx, hρy]
    exact MassGap.ConfinesZero.lipschitz_wilsonCorrAt N d x y
  -- the weighted sum of differences
  have hnum1 : (∑ d : Fin (N + 1),
      |(MassGap.readYMAt N x).ρ d - (MassGap.readYMAt N y).ρ d| * (d : ℝ) ^ 2)
      ≤ ((N : ℝ) + 1) * (K * |x - y|) * W := by
    have hbd : ∀ d ∈ (Finset.univ : Finset (Fin (N + 1))),
        |(MassGap.readYMAt N x).ρ d - (MassGap.readYMAt N y).ρ d| * (d : ℝ) ^ 2
          ≤ (K * |x - y|) * W := by
      intro d _
      exact mul_le_mul (hdiffle d) (hwle d) (hw0 d) (by positivity)
    refine le_trans (Finset.sum_le_sum hbd) (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  -- the unweighted sum of differences
  have hnum2 : (∑ d : Fin (N + 1),
      |(MassGap.readYMAt N x).ρ d - (MassGap.readYMAt N y).ρ d|)
      ≤ ((N : ℝ) + 1) * (K * |x - y|) := by
    refine le_trans (Finset.sum_le_sum (fun d _ => hdiffle d)) ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [this]
  -- the weighted average is at most the largest weight
  have havg : (∑ d : Fin (N + 1), (MassGap.readYMAt N y).p d * (d : ℝ) ^ 2) ≤ W := by
    have hbd : ∀ d ∈ (Finset.univ : Finset (Fin (N + 1))),
        (MassGap.readYMAt N y).p d * (d : ℝ) ^ 2 ≤ (MassGap.readYMAt N y).p d * W :=
      fun d _ => mul_le_mul_of_nonneg_left (hwle d) ((MassGap.readYMAt N y).p_nonneg d)
    refine le_trans (Finset.sum_le_sum hbd) ?_
    rw [← Finset.sum_mul, (MassGap.readYMAt N y).p_sum, one_mul]
  refine le_trans (moment_diff_le_profile_diff _ _ _ hw0) ?_
  have hA : (∑ d : Fin (N + 1),
        |(MassGap.readYMAt N x).ρ d - (MassGap.readYMAt N y).ρ d| * (d : ℝ) ^ 2)
        / (∑ d : Fin (N + 1), (MassGap.readYMAt N x).ρ d)
      ≤ (((N : ℝ) + 1) * (K * |x - y|) * W) / m := by
    first
      | exact div_le_div (by positivity) hnum1 hm hden
      | exact div_le_div₀ (by positivity) hnum1 hm hden
      | exact div_le_div_of_le_left (by positivity) hm hden
  have hBnum : (∑ d : Fin (N + 1),
        |(MassGap.readYMAt N x).ρ d - (MassGap.readYMAt N y).ρ d|)
        / (∑ d : Fin (N + 1), (MassGap.readYMAt N x).ρ d)
      ≤ (((N : ℝ) + 1) * (K * |x - y|)) / m := by
    first
      | exact div_le_div (by positivity) hnum2 hm hden
      | exact div_le_div₀ (by positivity) hnum2 hm hden
      | exact div_le_div_of_le_left (by positivity) hm hden
  have hBpos : (0 : ℝ) ≤ ∑ d : Fin (N + 1), (MassGap.readYMAt N y).p d * (d : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun d _ => mul_nonneg ((MassGap.readYMAt N y).p_nonneg d) (hw0 d))
  have hB : (∑ d : Fin (N + 1), (MassGap.readYMAt N y).p d * (d : ℝ) ^ 2)
        * ((∑ d : Fin (N + 1),
            |(MassGap.readYMAt N x).ρ d - (MassGap.readYMAt N y).ρ d|)
          / (∑ d : Fin (N + 1), (MassGap.readYMAt N x).ρ d))
      ≤ W * ((((N : ℝ) + 1) * (K * |x - y|)) / m) := by
    refine mul_le_mul havg hBnum (by positivity) hW0
  have hsum := add_le_add hA hB
  refine le_trans hsum (le_of_eq ?_)
  have hm0 : m ≠ 0 := ne_of_gt hm
  field_simp
  ring

#print axioms exists_lipschitz_lag_moment

/-- `ym_crossover_confinement_of_grid` with its Lipschitz modulus supplied instead of assumed.

That theorem concludes `∀ β ∈ Set.Icc a b, μYM β < κ₀YM` from four inputs, one of which, `hlip`, is
a Lipschitz modulus for the lag second moment. `exists_lipschitz_lag_moment` at `nCorrYM` supplies
it, so the statement returns a constant `L` with `0 ≤ L` and an implication: if every `β` in
`Set.Icc a b` has some `γ` in the same interval within `δ` whose lag second moment is at most
`B - L * δ`, then `μYM β < κ₀YM` throughout the interval.

`haperture` stays a hypothesis; it is arithmetic in `B` once `B` is fixed, and fixing `B` belongs to
the grid data. `pcorrYM` matches `exists_lipschitz_lag_moment`'s `(readYMAt nCorrYM ·).p`
definitionally, since `readYM_is_readYMAt` is `rfl` and `pcorrYM β = (readYM β).p`.

The conclusion covers `Set.Icc a b` only. `ym_A1_of_grid` additionally takes `hstrong` and `hweak`.
`Apriori.apriori_A1_strong` is stated over an abstract `μ : ℝ → ℝ` and is not instantiated at `μYM`.
The `EvenAp` family requires `N` odd, and `nCorrYM = 16` is even, so it does not reach this read.

DERIVED: the `0` in `ha : 0 ≤ a` is the sign condition on the left endpoint, and the `0` in `0 ≤ L`
a sign condition on the returned constant. In `haperture`, `2 * Real.pi` is the full turn, the `1`
in `nCorrYM + 1` is the aperture's index offset, the outer `2` squares the aperture factor, the `2`
in `B / 2` is the halving carried by `Moment.Read.cos_avg_ge_circ`, and `1`, `3`, `1`, `4` are the
entropy floor's transfer read `3 ^ (-1/4) = e ^ (-κ₀)` subtracted from one. The `2` in `(d : ℝ) ^ 2`
is the lag moment's exponent. All are `ym_crossover_confinement_of_grid`'s, restated verbatim so the
caller discharges them by arithmetic. -/
theorem exists_lipschitz_interior_of_grid {a b B δ : ℝ} (ha : 0 ≤ a)
    (haperture : (2 * Real.pi / (MassGap.nCorrYM + 1)) ^ 2 * B / 2
      < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    ∃ L : ℝ, 0 ≤ L ∧
      ((∀ β ∈ Set.Icc a b, ∃ γ ∈ Set.Icc a b, |β - γ| ≤ δ ∧
          (∑ d, MassGap.pcorrYM γ d * (d : ℝ) ^ 2) ≤ B - L * δ)
        → ∀ β ∈ Set.Icc a b, MassGap.μYM β < MassGap.κ₀YM) := by
  obtain ⟨L, hL, hlip⟩ := exists_lipschitz_lag_moment ha MassGap.nCorrYM
  exact ⟨L, hL, fun hcover =>
    MassGap.ym_crossover_confinement_of_grid hL haperture hlip hcover⟩

#print axioms exists_lipschitz_interior_of_grid

/-- `A1_YM ymModel`, which unfolds to `∀ β, μYM β < κ₀YM`, from three coupling ranges with both cut
points free.

`hstrong` covers `β < blo`, `hinterior` covers `Set.Icc blo bhi`, and `hweak` covers `bhi ≤ β`. The
proof is a trichotomy on `β` against the two cuts and reads neither cut's value.

`ym_A1_of_grid` pins the lower cut at `βloYM = βcYM - 1`; here both cuts are the caller's variables,
so the interior interval can be matched to the grid data.

DERIVED: no numeral appears in the statement. The two cuts are the caller's. -/
theorem ym_A1_of_split {blo bhi : ℝ}
    (hstrong : ∀ β, β < blo → MassGap.μYM β < MassGap.κ₀YM)
    (hinterior : ∀ β ∈ Set.Icc blo bhi, MassGap.μYM β < MassGap.κ₀YM)
    (hweak : ∀ β, bhi ≤ β → MassGap.μYM β < MassGap.κ₀YM) :
    MassGap.A1_YM MassGap.ymModel := by
  show ∀ β, MassGap.μYM β < MassGap.κ₀YM
  intro β
  rcases lt_or_ge β blo with h | h
  · exact hstrong β h
  · rcases le_or_gt β bhi with h2 | h2
    · exact hinterior β ⟨h, h2⟩
    · exact hweak β (le_of_lt h2)

#print axioms ym_A1_of_split

/-- A definite weak-coupling cut, from a limit of `μYM` strictly below the floor.

`Apriori.apriori_A1_weak` turns `hL : L < κ₀YM` and `hlim` into `∀ᶠ β in atTop, μYM β < κ₀YM`, and
`Filter.eventually_atTop` restates that as a cut `bhi` with `∀ β, bhi ≤ β → μYM β < κ₀YM` — the
shape `ym_A1_of_split`'s `hweak` takes, which is available because that cut is a variable there.

`hlim` is a hypothesis; nothing in the tree produces it. `FreeField.muInf_lt_floor` is the
arithmetic `0.0326 < ¼ · log 3` and concerns no property of `μYM`, so it can discharge `hL` once a
limit value is in hand but not `hlim`.

DERIVED: no numeral appears in the statement. -/
theorem exists_bhi_of_weak_limit {L : ℝ} (hL : L < MassGap.κ₀YM)
    (hlim : Filter.Tendsto MassGap.μYM Filter.atTop (nhds L)) :
    ∃ bhi : ℝ, ∀ β, bhi ≤ β → MassGap.μYM β < MassGap.κ₀YM := by
  have h := MassGap.apriori_A1_weak hL hlim
  rw [Filter.eventually_atTop] at h
  exact h

#print axioms exists_bhi_of_weak_limit

/-- A definite weak-coupling cut, from an eventual inequality on the cosine average rather than a
limit.

`Filter.eventually_atTop` turns `h` into a cut `bhi` beyond which `3 ^ (-1/4) < cosAvgYMAt N β`, and
`Complete.confinement_at_of_cosAvg` converts each such inequality pointwise into
`μYMAt N β < κ₀YM`.

Where `exists_bhi_of_weak_limit` takes `Tendsto μYM atTop (nhds L)` with `L < κ₀YM`, this takes no
convergence, no limit value and no identification of a limiting profile. The conclusion has the
shape `ym_A1_of_split` and `WilsonInstance.gapModelOf_A1` consume either way.

DERIVED: `3`, `1` and `4` are the entropy floor's own, since `κ₀YM = ¼ · log 3` and its transfer
read is `3 ^ (-1/4) = e ^ (-κ₀)`. -/
theorem exists_bhi_of_eventual_cosAvg {N : ℕ}
    (h : ∀ᶠ β in Filter.atTop, (3 : ℝ) ^ (-(1 : ℝ) / 4) < MassGap.cosAvgYMAt N β) :
    ∃ bhi : ℝ, ∀ β, bhi ≤ β → MassGap.μYMAt N β < MassGap.κ₀YM := by
  rw [Filter.eventually_atTop] at h
  obtain ⟨bhi, hbhi⟩ := h
  exact ⟨bhi, fun β hβ => MassGap.confinement_at_of_cosAvg (hbhi β hβ)⟩

#print axioms exists_bhi_of_eventual_cosAvg

/-- A bound on the substrate moment, together with an arithmetic condition on that bound, puts the
cosine average strictly above the entropy floor.

`Moment.Read.cos_avg_ge_circ` is `1 - (2π/(N+1))² · ⟨d²⟩ / 2 ≤ ⟨cos θ⟩`. `hb` bounds `d2At N β`,
which is the circle second moment of `readYMAt N β` by definition, and `hscale` places the resulting
subtraction strictly above `3 ^ (-1/4)`; `linarith` closes the two together.

This is the inequality `Moment.Read.tension_lt_floor_of_circ_moment` runs on, stopped at the cosine
average instead of carried on to the tension, which is the form `exists_bhi_of_eventual_cosAvg`
consumes.

DERIVED: in `hscale`, `2 * Real.pi` is the full turn, the `1` in `(N : ℝ) + 1` is the aperture's
index offset, the outer `2` squares the aperture factor, the `2` in `B₃ / 2` is `cos_avg_ge_circ`'s
halving, and the leading `1` is what the floor is subtracted from. `3`, `1` and `4`, in `hscale` and
again in the conclusion, are the entropy floor's transfer read `3 ^ (-1/4) = e ^ (-κ₀)` with
`κ₀YM = ¼ · log 3`. -/
theorem cosAvg_gt_floor_of_substrate {N : ℕ} {B₃ β : ℝ}
    (hb : MassGap.d2At N β ≤ B₃)
    (hscale : (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B₃ / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < MassGap.cosAvgYMAt N β := by
  have hge := (MassGap.readYMAt N β).cos_avg_ge_circ
  have hA : (0 : ℝ) ≤ (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 := sq_nonneg _
  have hmono : (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * MassGap.d2At N β
      ≤ (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B₃ := mul_le_mul_of_nonneg_left hb hA
  show (3 : ℝ) ^ (-(1 : ℝ) / 4)
    < ∑ d, (MassGap.readYMAt N β).p d * Real.cos ((MassGap.readYMAt N β).θ d)
  have hd2 : MassGap.d2At N β
      = ∑ d, (MassGap.readYMAt N β).p d * (Moment.circLag d : ℝ) ^ 2 := rfl
  rw [hd2] at hmono
  linarith

#print axioms cosAvg_gt_floor_of_substrate

/-- **A UNIFORM COSINE FLOOR FROM THE SUBSTRATE BOUND.** An aperture-uniform bound on the lag moment
gives one `γ` strictly above the entropy floor `3^{−1/4}` and one aperture `N₀` past which the
measured cosine average stays at or above it, at every coupling in `S`.

`Moment.Read.cos_avg_ge_circ` floors the average by `1 − (2π/(N+1))²·⟨d²⟩/2`, and
`Moment.aperture_factor_tendsto_zero` sends the subtracted term to zero once `⟨d²⟩` is bounded, so
the average tends to `1`. This is the margin `cosAvg_gt_floor_of_substrate` does not carry: that
lemma gives the strict inequality at each aperture separately, which is confinement, while
`Complete.ym_physical_gap_uniform_exact` needs one constant serving every aperture at once.

DERIVED: `3`, `1` and `4` are the entropy floor read as a contrast, `3^{−1/4} = e^{−κ₀}` at
`κ₀ = ¼·log 3`, proved inline here as `VolumeRate.cell_ceiling_eq_exp_neg_floor` proves it. The `2`
dividing `1 + f` is the midpoint of the interval `(3^{−1/4}, 1)` the hypothesis leaves open — a
witness for an existential, the idiom `RatioGap.midpoint_is_strictly_better` records; any interior
point serves and none is tuned. `2 * Real.pi` is the full turn, the `1` in `(N : ℝ) + 1` is the
aperture's index offset, the outer `2` squares the aperture factor, and the `2` in `B / 2` is
`cos_avg_ge_circ`'s own halving. -/
theorem exists_uniform_cosAvg_floor_of_substrate {B : ℝ} {S : Set ℝ}
    (hB : ∀ N : ℕ, ∀ β ∈ S, MassGap.d2At N β ≤ B) :
    ∃ (γ : ℝ) (N₀ : ℕ), (3 : ℝ) ^ (-(1 : ℝ) / 4) < γ ∧
      ∀ (i : ℕ), ∀ β ∈ S, γ ≤ MassGap.cosAvgYMAt (N₀ + i) β := by
  set f : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hfdef
  -- `f = e^{−κ₀}`, so `f < 1` because the floor is positive.
  have h3 : f = Real.exp (-MassGap.κ₀YM) := by
    rw [hfdef, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    unfold MassGap.κ₀YM
    congr 1
    ring
  have hf1 : f < 1 := by
    rw [h3]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr MassGap.κ₀YM_pos)
  have hmidpos : (0 : ℝ) < 1 - (1 + f) / 2 := by linarith
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2 < 1 - (1 + f) / 2 :=
    (Moment.aperture_factor_tendsto_zero B).eventually_lt_const hmidpos
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨(1 + f) / 2, N₀, by linarith, ?_⟩
  intro i β hβ
  have hscale := hN₀ (N₀ + i) (Nat.le_add_right _ _)
  have hge := (MassGap.readYMAt (N₀ + i) β).cos_avg_ge_circ
  have hA : (0 : ℝ) ≤ (2 * Real.pi / (((N₀ + i : ℕ) : ℝ) + 1)) ^ 2 := sq_nonneg _
  have hmono : (2 * Real.pi / (((N₀ + i : ℕ) : ℝ) + 1)) ^ 2 * MassGap.d2At (N₀ + i) β
      ≤ (2 * Real.pi / (((N₀ + i : ℕ) : ℝ) + 1)) ^ 2 * B :=
    mul_le_mul_of_nonneg_left (hB (N₀ + i) β hβ) hA
  show (1 + f) / 2
    ≤ ∑ d, (MassGap.readYMAt (N₀ + i) β).p d * Real.cos ((MassGap.readYMAt (N₀ + i) β).θ d)
  have hd2 : MassGap.d2At (N₀ + i) β
      = ∑ d, (MassGap.readYMAt (N₀ + i) β).p d * (Moment.circLag d : ℝ) ^ 2 := rfl
  rw [hd2] at hmono
  linarith

#print axioms exists_uniform_cosAvg_floor_of_substrate

/-- **THE UNIFORM MARGIN.** An aperture-uniform bound on the lag moment gives one `c > 0` and one
aperture `N₀` with

    c  ≤  κ₀YM − μYMAt (N₀+i) β

at every refinement index `i` and every nonnegative coupling. One constant serves every aperture and
every coupling at once.

This is what `confinement_on_of_substrate_bound` leaves on the table. That theorem concludes the
strict inequality `μYMAt N β < κ₀YM` at each aperture separately, which is confinement and carries no
margin; a constant `c` below every surplus is a different statement and is what the continuum side
reads.

`c` is `κ₀YM + log γ` for the `γ` of `exists_uniform_cosAvg_floor_of_substrate`, positive because
`γ > 3^{−1/4} = e^{−κ₀YM}`. The surplus identity is `Complete.surplus_eq_log_cosAvg`.

DERIVED: `0` is the sign of `c` and the lower end of the coupling half-line. `3`, `1` and `4` are
the entropy floor `3^{−1/4}`, carried from `exists_uniform_cosAvg_floor_of_substrate` unchanged. -/
theorem exists_uniform_margin_of_substrate {B : ℝ}
    (hB : ∀ N : ℕ, ∀ β : ℝ, 0 ≤ β → MassGap.d2At N β ≤ B) :
    ∃ (c : ℝ) (N₀ : ℕ), 0 < c ∧
      ∀ (i : ℕ) (β : ℝ), 0 ≤ β → c ≤ MassGap.κ₀YM - MassGap.μYMAt (N₀ + i) β := by
  obtain ⟨γ, N₀, hγ, hcos⟩ :=
    exists_uniform_cosAvg_floor_of_substrate (B := B) (S := Set.Ici (0 : ℝ))
      (fun N β hβ => hB N β hβ)
  have h0 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have hγ0 : 0 < γ := lt_trans h0 hγ
  have hval : Real.log ((3 : ℝ) ^ (-(1 : ℝ) / 4)) = -MassGap.κ₀YM := by
    rw [Real.log_rpow (by norm_num)]
    unfold MassGap.κ₀YM
    ring
  have hCpos : 0 < MassGap.κ₀YM + Real.log γ := by
    have := Real.log_lt_log h0 hγ
    rw [hval] at this
    linarith
  refine ⟨MassGap.κ₀YM + Real.log γ, N₀, hCpos, ?_⟩
  intro i β hβ
  rw [MassGap.surplus_eq_log_cosAvg]
  have := Real.log_le_log hγ0 (hcos i β hβ)
  linarith

#print axioms exists_uniform_margin_of_substrate


/-- **THE SPACING-INDEPENDENT PHYSICAL GAP, FROM THE SUBSTRATE BOUND.** One positive `c`, and one
aperture `N₀`, such that at every screen extent `L > 0`, every refinement index `i` and every
nonnegative coupling,

    c / L  ≤  (κ₀YM − μYMAt (N₀+i) β) / (L / (N₀+i+1)).

The right-hand side is the lattice margin divided by the spacing that a screen of fixed physical
extent `L` carries at aperture `N₀+i`, so the bound is the margin in physical units and it does not
degrade as the spacing shrinks.

The content is `exists_uniform_margin_of_substrate`, which this is proved from. Since
`L / (N₀+i+1)` makes the quotient `(κ₀YM − μYMAt (N₀+i) β)·(N₀+i+1)/L` and `N₀+i+1 ≥ 1`, the step
from the margin to this form is one application of monotonicity. The form is here because it is what
`Complete.ym_physical_gap_uniform_exact` and `ScreenedGap.uniform_physical_gap` are stated in.

The screen spacing `L/(N₀+i+1)` is a convention fixing a physical extent and refining it.
`physical_gap_at_the_running_spacing` reads the lattice margin against the renormalisation-group
spacing instead: `AsymptoticScaling.aRun 3`, the two-loop running spacing of `SU(3)` at the Lean Wilson
coupling `β = 3/g²`, with `Λ = 1`.

This is `Complete.ym_physical_gap_uniform_exact` relativised to `Set.Ici 0`, which is the half-line
the substrate bound is available on and the one `WilsonInstance.gapModelOf_A1` reads; the surplus
identity is `Complete.surplus_eq_log_cosAvg`.

DERIVED: `0` is the sign of `c`, of `L`, and the lower end of the coupling half-line. `3`, `1` and
`4` are the entropy floor `3^{−1/4} = e^{−κ₀YM}`, carried from
`exists_uniform_cosAvg_floor_of_substrate`. The `1` in `((N₀ + i : ℕ) : ℝ) + 1` is the aperture's
index offset, which is also what makes that factor at least `1`. -/
theorem exists_physical_gap_uniform_of_substrate {B : ℝ}
    (hB : ∀ N : ℕ, ∀ β : ℝ, 0 ≤ β → MassGap.d2At N β ≤ B) :
    ∃ (c : ℝ) (N₀ : ℕ), 0 < c ∧
      ∀ (L : ℝ), 0 < L → ∀ (i : ℕ) (β : ℝ), 0 ≤ β →
        c / L ≤ (MassGap.κ₀YM - MassGap.μYMAt (N₀ + i) β)
          / (L / (((N₀ + i : ℕ) : ℝ) + 1)) := by
  obtain ⟨c, N₀, hCpos, hmargin⟩ := exists_uniform_margin_of_substrate (B := B) hB
  refine ⟨c, N₀, hCpos, ?_⟩
  intro L hL i β hβ
  have hstep : c ≤ MassGap.κ₀YM - MassGap.μYMAt (N₀ + i) β := hmargin i β hβ
  set n : ℝ := ((N₀ + i : ℕ) : ℝ) + 1 with hn
  have hnpos : (0 : ℝ) < n := by rw [hn]; positivity
  have hn1 : (1 : ℝ) ≤ n := by
    rw [hn]
    have : (0 : ℝ) ≤ ((N₀ + i : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hrewrite : (MassGap.κ₀YM - MassGap.μYMAt (N₀ + i) β) / (L / n)
      = (n / L) * (MassGap.κ₀YM - MassGap.μYMAt (N₀ + i) β) := by
    field_simp
  rw [hrewrite, div_le_iff₀ hL]
  have hflat : (n / L) * (MassGap.κ₀YM - MassGap.μYMAt (N₀ + i) β) * L
      = n * (MassGap.κ₀YM - MassGap.μYMAt (N₀ + i) β) := by
    field_simp
  rw [hflat]
  nlinarith

#print axioms exists_physical_gap_uniform_of_substrate



/-- `NonnegArm.LawAbove b` produces a constant `B₃` and, under an arithmetic condition on it, the
eventual inequality `∀ᶠ β in atTop, 3 ^ (-1/4) < cosAvgYMAt nCorrYM β`.

`d2At_bounded_of_lawAbove` turns `LawAbove b` into `d2At N β ≤ B₃` for every `β ≥ B` at every
aperture, and `cosAvg_gt_floor_of_substrate` converts that bound plus the arithmetic condition into
the inequality at each such `β`; `Filter.eventually_atTop` packages it at the cut `B`.

`LawAbove` is a hypothesis and the arithmetic condition is the antecedent of the returned
implication, so both are visible to the caller. The aperture is pinned at `nCorrYM = 16`, where the
factor `(2π/17)²` does not shrink, so the condition constrains `B₃`.

`LawAbove` is a quartic tail law relative to the contact term with one constant above a cut; it is a
named `Prop` with a matching `NonnegArm.LawBelow` and a two-arm composition
(`NonnegArm.substrate_even_of_two_arm`). Its exponent `4` is fixed in its own definition, not here:
`∑ k² · C / kˢ` converges exactly when `s > 3`, and
`ShareEnvelope.cubic_contact_relative_gives_no_bound` refutes `s = 3`.

DERIVED: `2 * Real.pi` is the full turn, the `1` in `(nCorrYM : ℝ) + 1` is the aperture's index
offset, the outer `2` squares the aperture factor, the `2` in `B₃ / 2` is
`Moment.Read.cos_avg_ge_circ`'s halving, the leading `1` is what the floor is subtracted from, and
`3`, `1`, `4` are the entropy floor's transfer read — in the antecedent and again in the
conclusion. -/
theorem exists_B3_eventual_cosAvg_of_lawAbove {b B : ℝ} (hbB : b < B)
    (ha : MassGap.NonnegArm.LawAbove b) :
    ∃ B₃ : ℝ,
      ((2 * Real.pi / ((MassGap.nCorrYM : ℝ) + 1)) ^ 2 * B₃ / 2
          < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)
        → ∀ᶠ β in Filter.atTop,
            (3 : ℝ) ^ (-(1 : ℝ) / 4) < MassGap.cosAvgYMAt MassGap.nCorrYM β) := by
  obtain ⟨B₃, hB₃⟩ := d2At_bounded_of_lawAbove hbB ha
  refine ⟨B₃, fun hscale => ?_⟩
  rw [Filter.eventually_atTop]
  exact ⟨B, fun β hβ => cosAvg_gt_floor_of_substrate (hB₃ MassGap.nCorrYM β hβ) hscale⟩

#print axioms exists_B3_eventual_cosAvg_of_lawAbove



/-- `A1_YM ymModel` from the two end ranges and a grid over the interior, with the Lipschitz
constant supplied rather than assumed.

The hypotheses are `hstrong`, confinement strictly below `a`; `hLw` and `hlim`, a limit of `μYM`
along `Filter.atTop` strictly below the floor; and `haperture`, arithmetic in `B` at `nCorrYM`. The
conclusion returns a cut `bhi` and a constant `L` with `0 ≤ L`, together with the implication that a
`δ`-grid of reads on `Set.Icc a bhi` clearing `B - L * δ` gives `A1_YM ymModel`.

`exists_bhi_of_weak_limit` supplies `bhi` and the weak range from `hLw` and `hlim`,
`exists_lipschitz_interior_of_grid` supplies `L` and the interior, and `ym_A1_of_split` joins the
three ranges. The Lipschitz constant is not among the hypotheses:
`exists_lipschitz_lag_moment` produces it from `ConfinesZero.lipschitz_wilsonCorrAt` and
`ConfinesZero.exists_profile_sum_floor`.

`hstrong` and `hlim` are hypotheses with no producer in the tree.
`Apriori.apriori_A1_strong` is stated over an abstract `μ : ℝ → ℝ` and is not instantiated at `μYM`,
and `FreeField.muInf_lt_floor` is the arithmetic `0.0326 < ¼ · log 3`, which concerns no property of
`μYM`.

DERIVED: the `0` in `ha : 0 ≤ a` is the sign condition on the left endpoint and the `0` in `0 ≤ L`
a sign condition on the returned constant. In `haperture`, `2 * Real.pi` is the full turn, the `1`
in `nCorrYM + 1` is the aperture's index offset, the outer `2` squares the aperture factor, the `2`
in `B / 2` is `Moment.Read.cos_avg_ge_circ`'s halving, and `1`, `3`, `1`, `4` are the entropy
floor's transfer read `3 ^ (-1/4) = e ^ (-κ₀)` with `κ₀YM = ¼ · log 3`. The `2` in `(d : ℝ) ^ 2` is
the lag moment's exponent. All are `ym_crossover_confinement_of_grid`'s, restated verbatim so the
caller discharges them by arithmetic. -/
theorem exists_L_ym_A1_of_grid_and_ends {a B δ Lw : ℝ} (ha : 0 ≤ a)
    (haperture : (2 * Real.pi / (MassGap.nCorrYM + 1)) ^ 2 * B / 2
      < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))
    (hstrong : ∀ β, β < a → MassGap.μYM β < MassGap.κ₀YM)
    (hLw : Lw < MassGap.κ₀YM)
    (hlim : Filter.Tendsto MassGap.μYM Filter.atTop (nhds Lw)) :
    ∃ bhi L : ℝ, 0 ≤ L ∧
      ((∀ β ∈ Set.Icc a bhi, ∃ γ ∈ Set.Icc a bhi, |β - γ| ≤ δ ∧
          (∑ d, MassGap.pcorrYM γ d * (d : ℝ) ^ 2) ≤ B - L * δ)
        → MassGap.A1_YM MassGap.ymModel) := by
  obtain ⟨bhi, hweak⟩ := exists_bhi_of_weak_limit hLw hlim
  obtain ⟨L, hL, hint⟩ :=
    exists_lipschitz_interior_of_grid (a := a) (b := bhi) (B := B) (δ := δ) ha haperture
  exact ⟨bhi, L, hL, fun hcover => ym_A1_of_split hstrong (hint hcover) hweak⟩

#print axioms exists_L_ym_A1_of_grid_and_ends

/-- The model conjunction for `ymModel`, from the same hypotheses as
`exists_L_ym_A1_of_grid_and_ends`.

`Model.mass_gap_of_model` takes `A1_YM ymModel` and `ym_A2`, the second already proved, and
concludes the three clauses restated here: at every `β` the norm of `ymModel`'s mode sum tends to
`0` along `Filter.atTop` in `τ`; at every `β`, `ymModel.μ β - ymModel.κ < 0`; and `ymModel.R` takes
the same value at any two directions.

`hstrong` and `hlim` are hypotheses with no producer in the tree.
`Apriori.apriori_A1_strong` is stated over an abstract `μ : ℝ → ℝ` with hypothesis `μ β ≤ 2βr` and
is not instantiated at `μYM`; `FreeField.muInf_lt_floor` is the arithmetic `0.0326 < ¼ · log 3` and
concerns no property of `μYM`. The Lipschitz constant is not a hypothesis:
`exists_lipschitz_lag_moment` supplies it from `ConfinesZero.lipschitz_wilsonCorrAt` and
`ConfinesZero.exists_profile_sum_floor`.

The conclusion is about `ymModel`, the lattice model, and concerns clustering, the tension against
the floor, and directional invariance.

DERIVED: the `0` in `ha : 0 ≤ a` and the `0` in `0 ≤ L` are sign conditions on the left endpoint and
the returned constant. In `haperture`, `2 * Real.pi` is the full turn, the `1` in `nCorrYM + 1` is
the aperture's index offset, the outer `2` squares the aperture factor, the `2` in `B / 2` is
`Moment.Read.cos_avg_ge_circ`'s halving, and `1`, `3`, `1`, `4` are the entropy floor's transfer
read. The `2` in `(d : ℝ) ^ 2` is the lag moment's exponent. In the conclusion the `0` in `nhds 0`
is the limit of the mode sum and the `0` in `μ β - κ < 0` is the strict sign. All are
`ym_crossover_confinement_of_grid`'s and `mass_gap_of_model`'s. -/
theorem exists_L_ym_mass_gap_of_grid_and_ends {a B δ Lw : ℝ} (ha : 0 ≤ a)
    (haperture : (2 * Real.pi / (MassGap.nCorrYM + 1)) ^ 2 * B / 2
      < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))
    (hstrong : ∀ β, β < a → MassGap.μYM β < MassGap.κ₀YM)
    (hLw : Lw < MassGap.κ₀YM)
    (hlim : Filter.Tendsto MassGap.μYM Filter.atTop (nhds Lw)) :
    ∃ bhi L : ℝ, 0 ≤ L ∧
      ((∀ β ∈ Set.Icc a bhi, ∃ γ ∈ Set.Icc a bhi, |β - γ| ≤ δ ∧
          (∑ d, MassGap.pcorrYM γ d * (d : ℝ) ^ 2) ≤ B - L * δ)
        → (∀ β, Filter.Tendsto
              (fun τ => ‖∑ k ∈ MassGap.ymModel.s β,
                MassGap.ymModel.P β k * (MassGap.ymModel.m β k) ^ τ‖)
              Filter.atTop (nhds 0))
            ∧ (∀ β, MassGap.ymModel.μ β - MassGap.ymModel.κ < 0)
            ∧ (∀ d d', MassGap.ymModel.R d = MassGap.ymModel.R d')) := by
  obtain ⟨bhi, L, hL, hA1⟩ :=
    exists_L_ym_A1_of_grid_and_ends (B := B) (δ := δ) ha haperture hstrong hLw hlim
  exact ⟨bhi, L, hL, fun hcover =>
    MassGap.mass_gap_of_model MassGap.ymModel (hA1 hcover) MassGap.ym_A2⟩

#print axioms exists_L_ym_mass_gap_of_grid_and_ends

/-- The raw lag second moment of `readYMAt N 0` is zero, at every aperture.

At zero coupling the profile is a point mass at lag `0` —
`ConfinesZero.profile_at_zero_coupling_eq_zero` annihilates every other lag — and the surviving term
carries the factor `(0 : ℝ) ^ 2 = 0`.

`MomentArms.d2At_at_zero` is the same fact at the circle weight. `circ_moment_le_lag_moment` runs
from the raw moment to the circle moment only, so the circle statement does not yield this one. The
raw weight is what `ym_crossover_confinement_of_grid`'s `hlip` and `exists_lipschitz_lag_moment` are
stated at.

DERIVED: the `1` in `Fin (N + 1)` is the index offset, the number of lags `readYMAt N` carries; the
`0` in `readYMAt N 0` is the coupling; the `2` is the lag moment's own exponent; the `0` on the
right is the value. -/
theorem lag_moment_at_zero (N : ℕ) :
    (∑ d : Fin (N + 1), (MassGap.readYMAt N 0).p d * (d : ℝ) ^ 2) = 0 := by
  refine Finset.sum_eq_zero (fun d _ => ?_)
  rcases eq_or_ne d 0 with rfl | hd
  · norm_num
  · have hp : (MassGap.readYMAt N 0).p d = 0 := by
      show (MassGap.readYMAt N 0).ρ d / _ = 0
      rw [MassGap.ConfinesZero.profile_at_zero_coupling_eq_zero N hd, zero_div]
    rw [hp, zero_mul]

#print axioms lag_moment_at_zero

/-- A cut `blo > 0` below which `μYM` stays strictly under the entropy floor on the nonnegative
couplings. No constant is supplied by the caller.

At the pinned aperture `nCorrYM`, four tree results chain:

* the raw lag moment is `0` at zero coupling (`lag_moment_at_zero`);
* it is `L`-Lipschitz on `Set.Icc 0 1` with `L` produced by `exists_lipschitz_lag_moment`, itself
  from `ConfinesZero.lipschitz_wilsonCorrAt` and `ConfinesZero.exists_profile_sum_floor`;
* so it is at most `L * β`, and `circ_moment_le_lag_moment` carries that to the circle moment;
* `Moment.Read.tension_lt_floor_of_circ_moment` turns a circle-moment bound plus the aperture
  condition into `tension < ¼ · log 3`, which is `κ₀YM` by definition.

The witness is `min 1 (c / (A * L + 1))`, where `A` is the aperture factor and `c = 1 - 3 ^ (-1/4)`
is positive by `ConfinesZero.floor_lt_one`; the `+ 1` keeps the quotient defined when `A * L = 0`.

The statement covers `0 ≤ β` only. `WilsonInstance.gapModelOf_A1` takes
`∀ β, 0 ≤ β → μYMAt N β < κ₀YM` at an arbitrary aperture, since `μClampAt` is `0` on the negative
branch, and the quantitative lemmas in the tree are gated at `0 ≤ β`.

DERIVED: the `0` in `0 < blo` is a sign condition on the returned cut and the `0` in `0 ≤ β` is the
sign condition on the coupling. Every other numeral — the aperture factor's `2` and `Real.pi`, the
floor's `3`, `1` and `4`, the interval endpoint `1`, and the `+ 1` guarding the denominator — occurs
in the proof term and not in the statement. -/
theorem exists_blo_ym_confines_on_Ico :
    ∃ blo : ℝ, 0 < blo ∧ ∀ β : ℝ, 0 ≤ β → β < blo → MassGap.μYM β < MassGap.κ₀YM := by
  obtain ⟨L, hL0, hlip⟩ :=
    exists_lipschitz_lag_moment (a := 0) (b := 1) le_rfl MassGap.nCorrYM
  set A : ℝ := (2 * Real.pi / ((MassGap.nCorrYM : ℝ) + 1)) ^ 2 with hAdef
  set c : ℝ := 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef, sub_pos]; exact MassGap.ConfinesZero.floor_lt_one
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hden : 0 < A * L + 1 := by positivity
  refine ⟨min 1 (c / (A * L + 1)), lt_min one_pos (div_pos hcpos hden), ?_⟩
  intro β hβ0 hβlt
  have hβ1 : β ≤ 1 := le_of_lt (lt_of_lt_of_le hβlt (min_le_left _ _))
  have hβc : β < c / (A * L + 1) := lt_of_lt_of_le hβlt (min_le_right _ _)
  have hlin : (∑ d : Fin (MassGap.nCorrYM + 1),
      (MassGap.readYMAt MassGap.nCorrYM β).p d * (d : ℝ) ^ 2) ≤ L * β := by
    have h := hlip β ⟨hβ0, hβ1⟩ 0 ⟨le_rfl, zero_le_one⟩
    rw [lag_moment_at_zero, sub_zero, sub_zero, abs_of_nonneg hβ0] at h
    exact le_trans (le_abs_self _) h
  have hB : (∑ d, (MassGap.readYM β).p d * (Moment.circLag d : ℝ) ^ 2) ≤ L * β :=
    le_trans (MassGap.circ_moment_le_lag_moment (MassGap.readYM β)) hlin
  have hscale : A * (L * β) / 2 < c := by
    have h1 : β * (A * L + 1) < c := by rwa [lt_div_iff₀ hden] at hβc
    nlinarith [hβ0, hcpos, mul_nonneg hA0 hL0]
  show (MassGap.readYM β).tension < 1 / 4 * Real.log 3
  exact (MassGap.readYM β).tension_lt_floor_of_circ_moment hB hscale

#print axioms exists_blo_ym_confines_on_Ico

/-- Confinement on the whole nonnegative coupling half-line at the pinned aperture, from the
eventual weak-coupling inequality `hweakev` and a grid over the interior.

| range | source |
|---|---|
| `[0, blo)` | `exists_blo_ym_confines_on_Ico` |
| `[blo, bhi]` | `exists_lipschitz_interior_of_grid`, under the grid in the antecedent |
| `[bhi, ∞)` | `exists_bhi_of_eventual_cosAvg` applied to `hweakev` |

`μYM = μYMAt nCorrYM` by `rfl`, so pieces stated about either discharge goals about the other. The
returned `blo`, `bhi` and `L` come from those three lemmas.

`hweakev` is a hypothesis, stated as an eventual inequality on the cosine average rather than a
limit. Nothing in the tree produces it: `FreeField.muInf_lt_floor` is the arithmetic
`0.0326 < ¼ · log 3` and concerns no property of `μYM`, and `FreeField`'s limit theorem is over the
lattice extent, for abstract sequences, concluding `nhds 0`.

DERIVED: the `0` in `0 < blo` is a sign condition on the lower cut, the `0` in `0 ≤ L` one on the
Lipschitz constant, and the `0` in `0 ≤ β` the sign condition on the coupling. In `haperture`,
`2 * Real.pi` is the full turn, the `1` in `nCorrYM + 1` is the aperture's index offset, the outer
`2` squares the aperture factor, the `2` in `B / 2` is `Moment.Read.cos_avg_ge_circ`'s halving, and
the leading `1` is what the floor is subtracted from. `3`, `1`, `4` in `haperture` and again in
`hweakev` are the entropy floor's transfer read `3 ^ (-1/4) = e ^ (-κ₀)`. The `2` in `(d : ℝ) ^ 2`
is the lag moment's exponent. -/
theorem exists_grid_confines_on_nonneg {B δ : ℝ}
    (haperture : (2 * Real.pi / (MassGap.nCorrYM + 1)) ^ 2 * B / 2
      < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))
    (hweakev : ∀ᶠ β in Filter.atTop,
      (3 : ℝ) ^ (-(1 : ℝ) / 4) < MassGap.cosAvgYMAt MassGap.nCorrYM β) :
    ∃ blo bhi L : ℝ, 0 < blo ∧ 0 ≤ L ∧
      ((∀ β ∈ Set.Icc blo bhi, ∃ γ ∈ Set.Icc blo bhi, |β - γ| ≤ δ ∧
          (∑ d, MassGap.pcorrYM γ d * (d : ℝ) ^ 2) ≤ B - L * δ)
        → ∀ β : ℝ, 0 ≤ β → MassGap.μYMAt MassGap.nCorrYM β < MassGap.κ₀YM) := by
  obtain ⟨blo, hblo, hstrong⟩ := exists_blo_ym_confines_on_Ico
  obtain ⟨bhi, hweak⟩ := exists_bhi_of_eventual_cosAvg (N := MassGap.nCorrYM) hweakev
  obtain ⟨L, hL, hint⟩ :=
    exists_lipschitz_interior_of_grid (a := blo) (b := bhi) (B := B) (δ := δ) hblo.le haperture
  refine ⟨blo, bhi, L, hblo, hL, fun hcover β hβ0 => ?_⟩
  rcases lt_or_ge β blo with h | h
  · exact hstrong β hβ0 h
  · rcases le_or_gt β bhi with h2 | h2
    · exact hint hcover β ⟨h, h2⟩
    · exact hweak β (le_of_lt h2)

#print axioms exists_grid_confines_on_nonneg

/-- The model conjunction for the clamped model `gapModelOf nCorrYM`, from the eventual
weak-coupling inequality and a grid over the interior.

`exists_grid_confines_on_nonneg` supplies `∀ β, 0 ≤ β → μYMAt nCorrYM β < κ₀YM` inside the arrow,
which is what `WilsonInstance.gapModelOf_A1` consumes: that theorem asks for the nonnegative
half-line only, at an arbitrary aperture, because `μClampAt` is `0` on the negative branch.
`gapModelOf_A2` is `ym_A2_at nCorrYM`, already proved, and `Model.mass_gap_of_model` is generic in
`M : LatticeYM`.

The caller supplies `hweakev`, which has no producer in the tree; `haperture`, arithmetic in `B` at
`nCorrYM`; the grid inside the arrow, finitely many deterministic reads; and `hdom`, `hfe`, `hgap`,
which are `gapModelOf`'s own mode-family inputs, passed through unchanged.

The conclusion is about `gapModelOf nCorrYM s Pw m Δ cf hdom hfe hgap`: at every `β` the norm of its
mode sum tends to `0` along `Filter.atTop`, its `μ β` stays strictly under its `κ`, and its `R`
agrees at any two directions.

DERIVED: the `0` in `0 < blo` is a sign condition on the lower cut and the `0` in `0 ≤ L` one on the
Lipschitz constant; the `0` in `nhds 0` is the limit of the mode sum and the `0` in `μ β - κ < 0`
the strict sign. In `haperture`, `2 * Real.pi` is the full turn, the `1` in `nCorrYM + 1` is the
aperture's index offset, the outer `2` squares the aperture factor, the `2` in `B / 2` is
`Moment.Read.cos_avg_ge_circ`'s halving, and the leading `1` is what the floor is subtracted from.
`3`, `1`, `4` in `haperture` and again in `hweakev` are the entropy floor's transfer read
`3 ^ (-1/4) = e ^ (-κ₀)` with `κ₀YM = ¼ · log 3`. The `2` in `(d : ℝ) ^ 2` is the lag moment's
exponent. All are `ym_crossover_confinement_of_grid`'s and `mass_gap_of_model`'s. -/
theorem exists_grid_mass_gap_clamped {B δ : ℝ} {Idx : Type}
    (haperture : (2 * Real.pi / (MassGap.nCorrYM + 1)) ^ 2 * B / 2
      < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))
    (hweakev : ∀ᶠ β in Filter.atTop,
      (3 : ℝ) ^ (-(1 : ℝ) / 4) < MassGap.cosAvgYMAt MassGap.nCorrYM β)
    (s : ℝ → Finset Idx) (Pw m : ℝ → Idx → ℂ) (Δ cf : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, MassGap.κ₀YM - MassGap.μClampAt MassGap.nCorrYM β ≤ cf β)
    (hgap : ∀ β, cf β ≤ Δ β) :
    ∃ blo bhi L : ℝ, 0 < blo ∧ 0 ≤ L ∧
      ((∀ β ∈ Set.Icc blo bhi, ∃ γ ∈ Set.Icc blo bhi, |β - γ| ≤ δ ∧
          (∑ d, MassGap.pcorrYM γ d * (d : ℝ) ^ 2) ≤ B - L * δ)
        → (∀ β, Filter.Tendsto
              (fun τ => ‖∑ k ∈ (MassGap.gapModelOf
                  MassGap.nCorrYM s Pw m Δ cf hdom hfe hgap).s β,
                (MassGap.gapModelOf
                  MassGap.nCorrYM s Pw m Δ cf hdom hfe hgap).P β k
                  * ((MassGap.gapModelOf
                  MassGap.nCorrYM s Pw m Δ cf hdom hfe hgap).m β k) ^ τ‖)
              Filter.atTop (nhds 0))
            ∧ (∀ β, (MassGap.gapModelOf
                  MassGap.nCorrYM s Pw m Δ cf hdom hfe hgap).μ β
                - (MassGap.gapModelOf
                  MassGap.nCorrYM s Pw m Δ cf hdom hfe hgap).κ < 0)
            ∧ (∀ d d', (MassGap.gapModelOf
                  MassGap.nCorrYM s Pw m Δ cf hdom hfe hgap).R d
                = (MassGap.gapModelOf
                  MassGap.nCorrYM s Pw m Δ cf hdom hfe hgap).R d')) := by
  obtain ⟨blo, bhi, L, hblo, hL, hconf⟩ :=
    exists_grid_confines_on_nonneg (B := B) (δ := δ) haperture hweakev
  refine ⟨blo, bhi, L, hblo, hL, fun hcover => ?_⟩
  exact MassGap.mass_gap_of_model _
    (MassGap.gapModelOf_A1 MassGap.nCorrYM (hconf hcover) s Pw m Δ cf
      hdom hfe hgap)
    (MassGap.gapModelOf_A2 MassGap.nCorrYM s Pw m Δ cf hdom hfe hgap)

#print axioms exists_grid_mass_gap_clamped

/-- Confinement on the nonnegative half-line with the weak range resting on `NonnegArm.LawAbove`
rather than on an eventual inequality.

`exists_B3_eventual_cosAvg_of_lawAbove` turns `LawAbove b` plus an arithmetic condition on the
constant `B₃` it returns into the inequality `exists_grid_confines_on_nonneg` takes as `hweakev`.
The ranges are:

| range | source |
|---|---|
| `[0, blo)` | `exists_blo_ym_confines_on_Ico` |
| `[blo, bhi]` | `exists_lipschitz_interior_of_grid`, under the grid in the antecedent |
| `[bhi, ∞)` | `LawAbove b` with the arithmetic condition on its constant |

`LawAbove` is a quartic tail law relative to the contact term with one constant above a cut, a named
`Prop` with a matching `NonnegArm.LawBelow` and the two-arm composition
`NonnegArm.substrate_even_of_two_arm`; its exponent is fixed by convergence of `∑ k² · C / kˢ` for
`s > 3`, with `ShareEnvelope.cubic_contact_relative_gives_no_bound` refuting `s = 3`.

`LawAbove` is a hypothesis with no producer. The aperture is pinned at `nCorrYM = 16`, so the factor
`(2π/17)²` does not shrink and both arithmetic conditions constrain their bounds; both appear as
explicit antecedents rather than side conditions inside a proof.

DERIVED: the `0` in `0 < blo` is a sign condition on the lower cut, the `0` in `0 ≤ L` one on the
Lipschitz constant, and the `0` in `0 ≤ β` the sign condition on the coupling. In `haperture` and in
the returned condition on `B₃`, `2 * Real.pi` is the full turn, the `1` in `nCorrYM + 1` is the
aperture's index offset, the outer `2` squares the aperture factor, the `2` in the division is
`Moment.Read.cos_avg_ge_circ`'s halving, the leading `1` is what the floor is subtracted from, and
`3`, `1`, `4` are the entropy floor's transfer read. The `2` in `(d : ℝ) ^ 2` is the lag moment's
exponent. -/
theorem exists_B3_confines_on_nonneg_of_lawAbove {b B Bgrid δ : ℝ} (hbB : b < B)
    (ha : MassGap.NonnegArm.LawAbove b)
    (haperture : (2 * Real.pi / (MassGap.nCorrYM + 1)) ^ 2 * Bgrid / 2
      < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    ∃ B₃ : ℝ,
      ((2 * Real.pi / ((MassGap.nCorrYM : ℝ) + 1)) ^ 2 * B₃ / 2
          < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)
        → ∃ blo bhi L : ℝ, 0 < blo ∧ 0 ≤ L ∧
            ((∀ β ∈ Set.Icc blo bhi, ∃ γ ∈ Set.Icc blo bhi, |β - γ| ≤ δ ∧
                (∑ d, MassGap.pcorrYM γ d * (d : ℝ) ^ 2) ≤ Bgrid - L * δ)
              → ∀ β : ℝ, 0 ≤ β → MassGap.μYMAt MassGap.nCorrYM β < MassGap.κ₀YM)) := by
  obtain ⟨B₃, hB₃⟩ := exists_B3_eventual_cosAvg_of_lawAbove hbB ha
  refine ⟨B₃, fun hfloor => ?_⟩
  exact exists_grid_confines_on_nonneg (B := Bgrid) (δ := δ) haperture (hB₃ hfloor)

#print axioms exists_B3_confines_on_nonneg_of_lawAbove

/-! ## The flat-profile no-go and `LawAbove`

`ClayAssembly.flat_profile_admits_no_uniform_quartic_constant` proves
`¬ ∃ C ≥ 0, ∀ m ≥ 1, 1 ≤ C / m⁴`. For a flat profile (`ρ d = ρ 0` at every lag)
`NonnegArm.LawAbove` demands exactly that, so a flat profile satisfies `LawAbove` for no constant.

That is a statement about the flat profile. What it rules out is an argument establishing `LawAbove`
without using the profile's decay, since such an argument would apply to the flat profile too. It
constrains the method, not the statement.

The pinned variant below asks for the law at one aperture, which is all the chain uses:
`ShareEnvelope.circ_moment_le_of_contact_relative` works one aperture at a time.
`lawAboveAt_of_lawAbove` shows the aperture-uniform law implies the pinned one. -/

/-- The quartic tail law at one fixed aperture: a constant `C ≥ 0` such that at every coupling above
`b` and every lag `d` with `1 ≤ Moment.circLag d`,
`wilsonCorrAt N β d ≤ C * wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4`.

This is `NonnegArm.LawAbove` with the aperture fixed rather than universally quantified; everything
else is identical, so `lawAboveAt_of_lawAbove` below is immediate.

DERIVED: the `0` in `0 ≤ C` is a sign condition on the constant. The `1` in `Fin (N + 1)` is the
index offset, the number of lags aperture `N` carries. The `1` in `1 ≤ Moment.circLag d` is the lag
cut, excluding the contact lag. The `0` in `wilsonCorrAt N β 0` is the contact lag the law is stated
relative to. The `4` is `LawAbove`'s exponent, fixed by convergence of `∑ k² · C / kˢ` for `s > 3`,
with `ShareEnvelope.cubic_contact_relative_gives_no_bound` refuting `s = 3`. All are `LawAbove`'s,
kept identical so the two compose. -/
def LawAboveAt (N : ℕ) (b : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (d : Fin (N + 1)), b < β → 1 ≤ Moment.circLag d →
    MassGap.wilsonCorrAt N β d
      ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4

/-- The aperture-uniform `NonnegArm.LawAbove b` implies `LawAboveAt N b` at every aperture `N`. The
proof instantiates the universal quantifier and keeps the same constant, so pinning weakens nothing
that was already available.

DERIVED: no numeral appears in the statement; both sides carry `LawAbove`'s inside their own
definitions. -/
theorem lawAboveAt_of_lawAbove (N : ℕ) {b : ℝ} (h : MassGap.NonnegArm.LawAbove b) :
    LawAboveAt N b := by
  obtain ⟨C, hC, hlaw⟩ := h
  exact ⟨C, hC, fun β d hβ hd => hlaw N β d hβ hd⟩

#print axioms lawAboveAt_of_lawAbove

/-- The substrate bound above a cut from the pinned law: `LawAboveAt N b` with `b < B` gives a
constant `B₃` bounding `d2At N β` for every `β ≥ B`.

The proof is `d2At_bounded_of_lawAbove`'s verbatim.
`ShareEnvelope.circ_moment_le_of_contact_relative` already works one aperture at a time, so the
universal quantifier over apertures was never used.

DERIVED: no numeral appears in the statement. The `2` from the two sides of the circle and the `1`
passed to `quarticWeight` as the lag cut occur in the proof term. -/
theorem d2At_bounded_of_lawAboveAt {N : ℕ} {b B : ℝ} (hbB : b < B) (ha : LawAboveAt N b) :
    ∃ B₃ : ℝ, ∀ β : ℝ, B ≤ β → MassGap.d2At N β ≤ B₃ := by
  obtain ⟨C, hC, h⟩ := ha
  exact ⟨2 * ∑' k : ℕ, (k : ℝ) ^ 2 * MassGap.ShareEnvelope.quarticWeight 1 C k,
    fun β hβ =>
      MassGap.ShareEnvelope.circ_moment_le_of_contact_relative (MassGap.readYMAt N β) 1 hC
        (fun d hd => by
          simpa only [MassGap.ShareEnvelope.readYMAt_rho] using
            h (max β 0) d (lt_of_lt_of_le (lt_of_lt_of_le hbB hβ) (le_max_left β 0)) hd)⟩

#print axioms d2At_bounded_of_lawAboveAt

/-- The weak-range eventual inequality from the pinned law.

`d2At_bounded_of_lawAboveAt` turns `LawAboveAt nCorrYM b` with `b < B` into `d2At nCorrYM β ≤ B₃`
for every `β ≥ B`, and `cosAvg_gt_floor_of_substrate` converts that bound plus the arithmetic
condition into `3 ^ (-1/4) < cosAvgYMAt nCorrYM β` at each such `β`; `Filter.eventually_atTop`
packages it at the cut `B`.

`exists_B3_eventual_cosAvg_of_lawAbove` asks for the aperture-uniform `NonnegArm.LawAbove`; this
asks for the law at `nCorrYM` alone, which is what the chain uses.

DERIVED: `2 * Real.pi` is the full turn, the `1` in `(nCorrYM : ℝ) + 1` is the aperture's index
offset, the outer `2` squares the aperture factor, the `2` in `B₃ / 2` is
`Moment.Read.cos_avg_ge_circ`'s halving, the leading `1` is what the floor is subtracted from, and
`3`, `1`, `4` are the entropy floor's transfer read `3 ^ (-1/4) = e ^ (-κ₀)` — in the antecedent and
again in the conclusion. -/
theorem exists_B3_eventual_cosAvg_of_lawAboveAt {b B : ℝ} (hbB : b < B)
    (ha : LawAboveAt MassGap.nCorrYM b) :
    ∃ B₃ : ℝ,
      ((2 * Real.pi / ((MassGap.nCorrYM : ℝ) + 1)) ^ 2 * B₃ / 2
          < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)
        → ∀ᶠ β in Filter.atTop,
            (3 : ℝ) ^ (-(1 : ℝ) / 4) < MassGap.cosAvgYMAt MassGap.nCorrYM β) := by
  obtain ⟨B₃, hB₃⟩ := d2At_bounded_of_lawAboveAt hbB ha
  refine ⟨B₃, fun hscale => ?_⟩
  rw [Filter.eventually_atTop]
  exact ⟨B, fun β hβ => cosAvg_gt_floor_of_substrate (hB₃ β hβ) hscale⟩

#print axioms exists_B3_eventual_cosAvg_of_lawAboveAt

/-- Confinement on the nonnegative half-line with the weak range resting on the pinned law
`LawAboveAt nCorrYM b`.

The same chain as `exists_B3_confines_on_nonneg_of_lawAbove`, with
`exists_B3_eventual_cosAvg_of_lawAboveAt` supplying the `hweakev` that
`exists_grid_confines_on_nonneg` takes. The pinned law is what the chain uses;
`lawAboveAt_of_lawAbove` derives it from the aperture-uniform `NonnegArm.LawAbove`.

`LawAboveAt` is a hypothesis with no producer, and both arithmetic conditions remain constraints at
the pinned aperture. The flat-profile no-go says a flat profile satisfies the law for no constant,
which bears on how the law may be proved rather than on whether it holds.

DERIVED: the `0` in `0 < blo` is a sign condition on the lower cut, the `0` in `0 ≤ L` one on the
Lipschitz constant, and the `0` in `0 ≤ β` the sign condition on the coupling. In `haperture` and in
the returned condition on `B₃`, `2 * Real.pi` is the full turn, the `1` in `nCorrYM + 1` is the
aperture's index offset, the outer `2` squares the aperture factor, the `2` in the division is
`Moment.Read.cos_avg_ge_circ`'s halving, the leading `1` is what the floor is subtracted from, and
`3`, `1`, `4` are the entropy floor's transfer read. The `2` in `(d : ℝ) ^ 2` is the lag moment's
exponent. -/
theorem exists_B3_confines_on_nonneg_of_lawAboveAt {b B Bgrid δ : ℝ} (hbB : b < B)
    (ha : LawAboveAt MassGap.nCorrYM b)
    (haperture : (2 * Real.pi / (MassGap.nCorrYM + 1)) ^ 2 * Bgrid / 2
      < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    ∃ B₃ : ℝ,
      ((2 * Real.pi / ((MassGap.nCorrYM : ℝ) + 1)) ^ 2 * B₃ / 2
          < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)
        → ∃ blo bhi L : ℝ, 0 < blo ∧ 0 ≤ L ∧
            ((∀ β ∈ Set.Icc blo bhi, ∃ γ ∈ Set.Icc blo bhi, |β - γ| ≤ δ ∧
                (∑ d, MassGap.pcorrYM γ d * (d : ℝ) ^ 2) ≤ Bgrid - L * δ)
              → ∀ β : ℝ, 0 ≤ β → MassGap.μYMAt MassGap.nCorrYM β < MassGap.κ₀YM)) := by
  obtain ⟨B₃, hB₃⟩ := exists_B3_eventual_cosAvg_of_lawAboveAt hbB ha
  refine ⟨B₃, fun hfloor => ?_⟩
  exact exists_grid_confines_on_nonneg (B := Bgrid) (δ := δ) haperture (hB₃ hfloor)

#print axioms exists_B3_confines_on_nonneg_of_lawAboveAt

/-- `NonnegArm.LawAbove b` with `b < B` gives confinement on `Set.Ici B` at every sufficiently large
aperture, with no arithmetic condition in the statement.

Two halves compose. `d2At_bounded_of_lawAbove` turns `LawAbove b` into
`∀ N β, B ≤ β → d2At N β ≤ B₃`, uniform in the aperture because `LawAbove` quantifies over `N`.
`Complete.confinement_on_of_substrate_bound` consumes that shape and concludes confinement at every
sufficiently wide aperture, discharging the aperture condition internally from
`Moment.aperture_factor_tendsto_zero`: the aperture factor `(2π/(N+1))²` tends to zero, so no bound
on the size of `B₃` is needed. The pinned-aperture routes carry such conditions — `B₃` small enough,
`Bgrid` small enough — because `N` is fixed there at `nCorrYM`.

`LawAbove` is a hypothesis with no producer.

DERIVED: no numeral appears in the statement. `B` is the caller's cut and `B₃` is
`d2At_bounded_of_lawAbove`'s; the aperture condition is discharged inside
`confinement_on_of_substrate_bound` and is not restated here. -/
theorem confines_at_wide_aperture_of_lawAbove {b B : ℝ} (hbB : b < B)
    (ha : MassGap.NonnegArm.LawAbove b) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ β ∈ Set.Ici B, MassGap.μYMAt N β < MassGap.κ₀YM := by
  obtain ⟨B₃, hB₃⟩ := d2At_bounded_of_lawAbove hbB ha
  exact MassGap.confinement_on_of_substrate_bound (B := B₃) (S := Set.Ici B)
    (fun N β hβ => hB₃ N β hβ)

#print axioms confines_at_wide_aperture_of_lawAbove

/-- `NonnegArm.LawBelow b` and `NonnegArm.LawAbove b` at the same cut bound `d2At N β` on the whole
nonnegative half-line, at every aperture `N`.

`NonnegArm.substrate_even_of_two_arm` merges the two laws but lands on `d2Even` at an `EvenAp`,
which the aperture argument cannot consume. Both laws are stated at general `N`, so merging them
directly avoids that restriction: at any `β ≥ 0` one law or the other applies, and `max C₁ C₂`
serves both because the contact value `wilsonCorrAt N β 0` is nonnegative.
`ShareEnvelope.circ_moment_le_of_contact_relative` carries the merged estimate to the moment.

DERIVED: the `0` in `0 ≤ β` is the sign condition on the coupling. The `2` from the two sides of the
circle, the `1` passed to `quarticWeight` as the lag cut, the contact lag `0`, and the `4` shared by
the two laws all occur in the proof term or inside the laws' own definitions, not in this
statement. -/
theorem substrate_bounded_of_two_arms {b : ℝ}
    (hbelow : MassGap.NonnegArm.LawBelow b) (habove : MassGap.NonnegArm.LawAbove b) :
    ∃ B : ℝ, ∀ (N : ℕ) (β : ℝ), 0 ≤ β → MassGap.d2At N β ≤ B := by
  obtain ⟨C₁, hC₁, h₁⟩ := hbelow
  obtain ⟨C₂, hC₂, h₂⟩ := habove
  refine ⟨2 * ∑' k : ℕ, (k : ℝ) ^ 2
      * MassGap.ShareEnvelope.quarticWeight 1 (max C₁ C₂) k, fun N β hβ0 => ?_⟩
  refine MassGap.ShareEnvelope.circ_moment_le_of_contact_relative (MassGap.readYMAt N β) 1
    (le_trans hC₁ (le_max_left _ _)) ?_
  intro d hd
  simp only [MassGap.ShareEnvelope.readYMAt_rho, max_eq_left hβ0]
  have hρ0 : 0 ≤ MassGap.wilsonCorrAt N β 0 := (MassGap.PlaqVariance.corrClay_zero_pos N β).le
  have hL1 : (1 : ℝ) ≤ (Moment.circLag d : ℝ) := by exact_mod_cast hd
  have hL : (0 : ℝ) < (Moment.circLag d : ℝ) ^ 4 := by positivity
  have hstep : ∀ C : ℝ, C ≤ max C₁ C₂ →
      C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4
        ≤ max C₁ C₂ * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4 := by
    intro C hCm
    have hnum : C * MassGap.wilsonCorrAt N β 0
        ≤ max C₁ C₂ * MassGap.wilsonCorrAt N β 0 :=
      mul_le_mul_of_nonneg_right hCm hρ0
    have := mul_le_mul_of_nonneg_right hnum (le_of_lt (inv_pos.mpr hL))
    simpa only [div_eq_mul_inv] using this
  rcases le_or_gt β b with hle | hgt
  · exact le_trans (h₁ N β d hβ0 hle hd) (hstep C₁ (le_max_left _ _))
  · exact le_trans (h₂ N β d hgt hd) (hstep C₂ (le_max_right _ _))

#print axioms substrate_bounded_of_two_arms

/-- Given that `NonnegArm.LawAbove` holds at every cut where `NonnegArm.LawBelow` does, there is an
aperture `N` at which `μYMAt N` stays strictly under the entropy floor on the whole nonnegative
half-line.

`NonnegArm.lawBelow_holds : ∃ b > 0, LawBelow b` is a theorem on the foundational axioms, so
`habove` applied at that cut gives both laws there. `substrate_bounded_of_two_arms` then bounds
`d2At` on `0 ≤ β` at every aperture, and `Complete.confinement_on_of_substrate_bound` turns that
aperture-uniform bound into confinement at every sufficiently wide aperture, discharging the
aperture condition internally from `Moment.aperture_factor_tendsto_zero`.
`Filter.Eventually.exists` names one such aperture.

The conclusion `∀ β, 0 ≤ β → μYMAt N β < κ₀YM` is what `WilsonInstance.gapModelOf_A1` consumes;
`μClampAt` is `0` on the negative branch, so nothing below zero is required. `habove` is the only
hypothesis: no grid, no arithmetic side condition and no pinned aperture enter. The quartic exponent
is fixed inside `LawAbove`, by convergence of `∑ k² · C / kˢ` for `s > 3` with
`ShareEnvelope.cubic_contact_relative_gives_no_bound` refuting `s = 3`.

DERIVED: the `0` in `0 ≤ β` is the sign condition on the coupling. Every other numeral lives inside
the lemmas composed here and none is restated. -/
theorem exists_aperture_A1_of_lawAbove
    (habove : ∀ b : ℝ, MassGap.NonnegArm.LawBelow b → MassGap.NonnegArm.LawAbove b) :
    ∃ N : ℕ, ∀ β : ℝ, 0 ≤ β → MassGap.μYMAt N β < MassGap.κ₀YM := by
  obtain ⟨b, _, hbelow⟩ := MassGap.NonnegArm.lawBelow_holds
  obtain ⟨B, hB⟩ := substrate_bounded_of_two_arms hbelow (habove b hbelow)
  have hev := MassGap.confinement_on_of_substrate_bound (B := B) (S := Set.Ici (0 : ℝ))
    (fun N β hβ => hB N β hβ)
  obtain ⟨N, hN⟩ := hev.exists
  exact ⟨N, fun β hβ0 => hN β hβ0⟩

#print axioms exists_aperture_A1_of_lawAbove

/-- **THE PHYSICAL GAP FROM THE SAME INPUT AS THE LATTICE GAP.** `NonnegArm.LawAbove` above the cut
`NonnegArm.lawBelow_holds` supplies gives one positive `c` and one aperture `N₀` with

    c / L  ≤  (κ₀YM − μYMAt (N₀+i) β) / (L / (N₀+i+1))

at every screen extent `L > 0`, every refinement index and every nonnegative coupling — the lattice
margin in physical units, not degrading as the spacing shrinks.

`exists_aperture_A1_of_lawAbove` runs the same two arms to A1's hypothesis. This runs them to the
physical gap, so one input serves the lattice chain and the continuum bound rather than the
continuum bound resting on a separate modulus. `Complete.ym_physical_gap_uniform_exact` and
`RefinementLaw.confinesAtAnAperture_of_uniform_cosAvg` state that bound from a supplied cosine
modulus `γ`; `exists_uniform_cosAvg_floor_of_substrate` is what produces one.

DERIVED: `0` is the sign of `c`, of `L`, and the lower end of the coupling half-line; the `1` in
`((N₀ + i : ℕ) : ℝ) + 1` is the aperture's index offset. Both are carried from
`exists_physical_gap_uniform_of_substrate` unchanged, and the cut `b` is `lawBelow_holds`'. -/
theorem exists_physical_gap_uniform_of_lawAbove
    (habove : ∀ b : ℝ, MassGap.NonnegArm.LawBelow b → MassGap.NonnegArm.LawAbove b) :
    ∃ (c : ℝ) (N₀ : ℕ), 0 < c ∧
      ∀ (L : ℝ), 0 < L → ∀ (i : ℕ) (β : ℝ), 0 ≤ β →
        c / L ≤ (MassGap.κ₀YM - MassGap.μYMAt (N₀ + i) β)
          / (L / (((N₀ + i : ℕ) : ℝ) + 1)) := by
  obtain ⟨b, _, hbelow⟩ := MassGap.NonnegArm.lawBelow_holds
  obtain ⟨B, hB⟩ := substrate_bounded_of_two_arms hbelow (habove b hbelow)
  exact exists_physical_gap_uniform_of_substrate (B := B) hB

#print axioms exists_physical_gap_uniform_of_lawAbove

/-- The model conjunction for `gapModelOf N`, at an aperture the theorem chooses, from `habove`
alone.

`exists_aperture_A1_of_lawAbove` supplies `gapModelOf_A1`'s hypothesis at one aperture `N`;
`gapModelOf_A2` is `ym_A2_at N`, already proved; and `Model.mass_gap_of_model` is generic in
`M : LatticeYM`. The conclusion is about `gapModelOf N s Pw m Δ cf hdom hfe hgap`: at every `β` the
norm of its mode sum tends to `0` along `Filter.atTop`, its `μ β` stays strictly under its `κ`, and
its `R` agrees at any two directions.

The hypotheses are `habove` — `LawAbove` at any cut where `LawBelow` holds — together with
`gapModelOf`'s own mode-family inputs `hdom`, and `hfe` and `hgap` under the returned aperture.
`LawBelow` is proved, the aperture is chosen by the theorem rather than pinned, and no grid or
arithmetic side condition enters.

DERIVED: the `0` in `nhds 0` is the limit of the mode sum and the `0` in `μ β - κ < 0` is the strict
sign; both are `mass_gap_of_model`'s conclusion restated here. -/
theorem exists_aperture_mass_gap_of_lawAbove {Idx : Type}
    (habove : ∀ b : ℝ, MassGap.NonnegArm.LawBelow b → MassGap.NonnegArm.LawAbove b)
    (s : ℝ → Finset Idx) (Pw m : ℝ → Idx → ℂ) (Δ cf : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β)) :
    ∃ N : ℕ,
      ∀ (hfe : ∀ β, MassGap.κ₀YM - MassGap.μClampAt N β ≤ cf β)
        (hgap : ∀ β, cf β ≤ Δ β),
        (∀ β, Filter.Tendsto
            (fun τ => ‖∑ k ∈ (MassGap.gapModelOf N s Pw m Δ cf hdom hfe hgap).s β,
              (MassGap.gapModelOf N s Pw m Δ cf hdom hfe hgap).P β k
                * ((MassGap.gapModelOf N s Pw m Δ cf hdom hfe hgap).m β k) ^ τ‖)
            Filter.atTop (nhds 0))
          ∧ (∀ β, (MassGap.gapModelOf N s Pw m Δ cf hdom hfe hgap).μ β
              - (MassGap.gapModelOf N s Pw m Δ cf hdom hfe hgap).κ < 0)
          ∧ (∀ d d', (MassGap.gapModelOf N s Pw m Δ cf hdom hfe hgap).R d
              = (MassGap.gapModelOf N s Pw m Δ cf hdom hfe hgap).R d') := by
  obtain ⟨N, hconf⟩ := exists_aperture_A1_of_lawAbove habove
  refine ⟨N, fun hfe hgap => ?_⟩
  exact MassGap.mass_gap_of_model _
    (MassGap.gapModelOf_A1 N hconf s Pw m Δ cf hdom hfe hgap)
    (MassGap.gapModelOf_A2 N s Pw m Δ cf hdom hfe hgap)

#print axioms exists_aperture_mass_gap_of_lawAbove

/-- **The uniform margin from `LawAbove`.** `exists_uniform_margin_of_substrate` composed with the
two arms, exactly as `exists_aperture_A1_of_lawAbove` composes them for Part I.

DERIVED: `0` is the sign of `c` and the lower end of the coupling half-line; the cut `b` is
`NonnegArm.lawBelow_holds`'. Both are carried from `exists_uniform_margin_of_substrate`. -/
theorem exists_uniform_margin_of_lawAbove
    (habove : ∀ b : ℝ, MassGap.NonnegArm.LawBelow b → MassGap.NonnegArm.LawAbove b) :
    ∃ (c : ℝ) (N₀ : ℕ), 0 < c ∧
      ∀ (i : ℕ) (β : ℝ), 0 ≤ β → c ≤ MassGap.κ₀YM - MassGap.μYMAt (N₀ + i) β := by
  obtain ⟨b, _, hbelow⟩ := MassGap.NonnegArm.lawBelow_holds
  obtain ⟨B, hB⟩ := substrate_bounded_of_two_arms hbelow (habove b hbelow)
  exact exists_uniform_margin_of_substrate (B := B) hB

#print axioms exists_uniform_margin_of_lawAbove

/-- **THE ASSEMBLY: Parts I and II from one hypothesis.**

The left conjunct is `exists_aperture_mass_gap_of_lawAbove` — an aperture at which the model
conjunction holds: the mode sum tends to zero in the separation, the tension stays strictly below
the entropy floor at every coupling, and the directional read is independent of direction. The
right conjunct is `exists_uniform_margin_of_lawAbove` — one positive constant below the surplus
`κ₀YM − μYMAt` at every aperture past `N₀` and every nonnegative coupling.

They take the SAME hypothesis. That was prose until this declaration; now Lean checks it, and if a
link is later weakened so the two stop sharing an input, this stops compiling.

Scope. Part III is deliberately not conjoined here. `WilsonOS.wilsonOSData` is unconditional — it
takes no `LawAbove`, no substrate bound and no coupling restriction — so joining it would suggest a
dependence that does not exist. `MassGap.WilsonOS.wilson_reconstructed_nontrivial` carries it
through the cited reconstruction on its own.

DERIVED: `0` is the strict upper bound the tension is compared against in the model conjunction, the
limit of the mode sum, the sign of `c`, and the lower end of the coupling half-line. Every numeral
is carried in from the two conjuncts unchanged; this declaration introduces none. -/
theorem lattice_gap_and_margin_of_lawAbove {Idx : Type}
    (habove : ∀ b : ℝ, MassGap.NonnegArm.LawBelow b → MassGap.NonnegArm.LawAbove b)
    (s : ℝ → Finset Idx) (Pw m : ℝ → Idx → ℂ) (Δ cf : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β)) :
    (∃ N : ℕ,
      ∀ (hfe : ∀ β, MassGap.κ₀YM - MassGap.μClampAt N β ≤ cf β)
        (hgap : ∀ β, cf β ≤ Δ β),
        (∀ β, Filter.Tendsto
            (fun τ => ‖∑ k ∈ (MassGap.gapModelOf N s Pw m Δ cf hdom hfe hgap).s β,
              (MassGap.gapModelOf N s Pw m Δ cf hdom hfe hgap).P β k
                * ((MassGap.gapModelOf N s Pw m Δ cf hdom hfe hgap).m β k) ^ τ‖)
            Filter.atTop (nhds 0))
          ∧ (∀ β, (MassGap.gapModelOf N s Pw m Δ cf hdom hfe hgap).μ β
              - (MassGap.gapModelOf N s Pw m Δ cf hdom hfe hgap).κ < 0)
          ∧ (∀ d d', (MassGap.gapModelOf N s Pw m Δ cf hdom hfe hgap).R d
              = (MassGap.gapModelOf N s Pw m Δ cf hdom hfe hgap).R d'))
    ∧ (∃ (c : ℝ) (N₀ : ℕ), 0 < c ∧
        ∀ (i : ℕ) (β : ℝ), 0 ≤ β → c ≤ MassGap.κ₀YM - MassGap.μYMAt (N₀ + i) β) :=
  ⟨exists_aperture_mass_gap_of_lawAbove habove s Pw m Δ cf hdom,
    exists_uniform_margin_of_lawAbove habove⟩

#print axioms lattice_gap_and_margin_of_lawAbove

/-- **THE CAPSTONE'S INNER QUANTIFIER IS NOT EMPTY**, and its mode family need not be.

`lattice_gap_and_margin_of_lawAbove`'s left conjunct reads `∃ N, ∀ hfe hgap, …`, with the mode
family the caller's. Two readings would make it say nothing: an empty `s β`, which turns the
clustering conclusion into a statement about an empty sum; and a `cf` no aperture admits, which
leaves the inner `∀` vacuous. `cf` is fixed before `N` is produced, so the second is not
hypothetical.

This exhibits data defeating both, at **every** aperture. One mode of magnitude `exp (-κ₀YM)`, with
`Δ` and `cf` the constant `κ₀YM`: `hdom` and `hgap` hold with equality, and `hfe` reduces to
`0 ≤ μClampAt N β`, which is `Complete.μYMAt_nonneg` on the physical branch and `0 ≤ 0` on the
clamped one. The mode's magnitude is below `1` (`Complete.κ₀YM_pos`), so the sum decays rather than
being empty.

DERIVED: `κ₀YM` is the entropy floor, `VortexCount.kappa0_is_the_surface_entropy_density`'s, used
here as the one scale already in the statement rather than as a chosen magnitude — any value with
`0 < Δ` and `κ₀YM - μClampAt ≤ cf ≤ Δ` would serve, and the floor is the one at hand. `1` is the
mode count and the singleton's element. `0` is the sign of the tension, the boundary of the physical
half-line inside `μClampAt`, and the value the clamped branch takes. -/
theorem capstone_data_exists (N : ℕ) :
    ∃ (s : ℝ → Finset Unit) (Pw m : ℝ → Unit → ℂ) (Δ cf : ℝ → ℝ),
      (∀ β, (s β).Nonempty)
      ∧ (∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
      ∧ (∀ β, ‖m β ()‖ < 1)
      ∧ (∀ β, MassGap.κ₀YM - MassGap.μClampAt N β ≤ cf β)
      ∧ (∀ β, cf β ≤ Δ β) := by
  classical
  refine ⟨fun _ => {()}, fun _ _ => 1,
    fun _ _ => ((Real.exp (-MassGap.κ₀YM) : ℝ) : ℂ),
    fun _ => MassGap.κ₀YM, fun _ => MassGap.κ₀YM, ?_, ?_, ?_, ?_, ?_⟩
  · intro β
    exact Finset.singleton_nonempty _
  · intro β k _
    -- `rw`, not `simp`: `simp` normalises `((Real.exp x : ℝ) : ℂ)` to `Complex.exp` and the
    -- `Complex.norm_real` step no longer applies.
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  · intro β
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr MassGap.κ₀YM_pos)
  · intro β
    have hclamp : 0 ≤ MassGap.μClampAt N β := by
      unfold MassGap.μClampAt
      by_cases h : (0 : ℝ) ≤ β
      · simp only [if_pos h]; exact MassGap.μYMAt_nonneg N β
      · simp [if_neg h]
    linarith
  · intro β
    exact le_refl _

#print axioms capstone_data_exists

/-- **THE MARGIN AT THE RUNNING SPACING.** One positive `c` and one aperture `N₀` such that at every
refinement index `i`, every nonnegative `β₁` and every target `a` strictly between `0` and
`AsymptoticScaling.aRun 3 β₁`, there is a coupling `β ≥ β₁` with

    aRun 3 β = a    and    c ≤ κ₀YM − μYMAt (N₀+i) β.

`aRun 3` is the two-loop running spacing of `SU(3)` at the Lean Wilson coupling `β = 3/g²`,
with `Λ = 1`; `SU(3)` is the gauge group of the ensemble `μYMAt` reads
(`wilsonCorrAt N β = WilsonBridge.corrClay (N + 1) β`, and `corrClay` is taken at colour count `3`).
`aRun`'s first argument is the colour count, so the spacing depends on the coupling alone; the
aperture `N₀+i` enters only through `μYMAt`.

`exists_physical_gap_uniform_of_lawAbove` reads the margin against the screen spacing `L/(N+1)`,
which is a convention fixing a physical extent and refining it. This reads it against the
two-loop running spacing instead: `AsymptoticScaling.exists_beta_aRun_eq` supplies a coupling at
which `aRun 3` equals the chosen target, and `β₁` is arbitrary, so that coupling can be demanded as
large as wanted — the branch asymptotic freedom lives on.

`c` depends on none of `i`, `a` or `β`. Because the margin holds at every `β ≥ 0`, the conjunct
`aRun 3 β = a` does not constrain it; the spacing only selects which coupling is quoted. Read as a
lattice-unit mass, a bound uniform in `β` is not a continuum statement: a mass bounded below cannot
satisfy `AsymptoticScalingAt` (`AsymptoticScaling.fixed_colours_pins_the_spacing`, and
`AsymptoticScaling.bounded_mass_fails_scaling`, which composes it with
`AsymptoticScaling.exists_beta_aRun_lt`).

DERIVED: `0` is the sign of `c`, the lower end of the coupling half-line in `hβ₁`, and the target's
sign in `ha`, carried from the two theorems composed here. `3` in `aRun 3` is the colour count of
`WilsonBridge.corrClay`'s ensemble, `SU(3)`, the gauge group whose correlation `μYMAt` reads; `3` in
`β = 3/g²` is `N` at that `N`, `g² = N/β` at the Lean coupling. -/
theorem physical_gap_at_the_running_spacing
    (habove : ∀ b : ℝ, MassGap.NonnegArm.LawBelow b → MassGap.NonnegArm.LawAbove b) :
    ∃ (c : ℝ) (N₀ : ℕ), 0 < c ∧
      ∀ (i : ℕ) (a β₁ : ℝ), 0 ≤ β₁ → 0 < a →
        a < MassGap.AsymptoticScaling.aRun 3 β₁ →
        ∃ β : ℝ, β₁ ≤ β ∧ MassGap.AsymptoticScaling.aRun 3 β = a ∧
          c ≤ MassGap.κ₀YM - MassGap.μYMAt (N₀ + i) β := by
  obtain ⟨c, M, hc, hmargin⟩ := exists_uniform_margin_of_lawAbove habove
  refine ⟨c, M, hc, ?_⟩
  intro i a β₁ hβ₁ ha hlt
  obtain ⟨β, hβge, hβeq⟩ :=
    MassGap.AsymptoticScaling.exists_beta_aRun_eq (N := 3) (by norm_num) ha hlt
  exact ⟨β, hβge, hβeq, hmargin i β (le_trans hβ₁ hβge)⟩

#print axioms physical_gap_at_the_running_spacing

/-- **THE ASSEMBLY, WITH THE RUNNING-SPACING CONJUNCT.** Parts I and II from one hypothesis,
including the reading against the renormalisation-group spacing.

Three conjuncts, one `habove`:

1. an aperture at which the model conjunction holds — the mode sum tends to zero in the separation,
   the tension stays strictly below the entropy floor at every coupling, the directional read is
   independent of direction (`exists_aperture_mass_gap_of_lawAbove`);
2. one positive `c` below the surplus `κ₀YM − μYMAt` at every aperture past `N₀` and every
   nonnegative coupling (`exists_uniform_margin_of_lawAbove`);
3. that same margin at a coupling realising any target the `SU(3)` two-loop spacing `aRun 3` (at the
   Wilson coupling, `Λ = 1`) reaches, arbitrarily far out (`physical_gap_at_the_running_spacing`).
   The margin already holds at every nonnegative coupling, so the spacing condition only selects
   which coupling is quoted.

`lattice_gap_and_margin_of_lawAbove` is this without the third conjunct; both are kept because the
two-conjunct form needs no `AsymptoticScaling` import to state.

The `N₀` of the second conjunct and of the third are each existential and need not agree — the
statement says each holds, not that one aperture serves both. `capstone_data_exists` is why the
first conjunct's inner quantifier is not empty.

Scope. Part III is not conjoined: `WilsonOS.wilsonOSData` is unconditional, taking no `LawAbove`, no
substrate bound and no coupling restriction, so joining it would suggest a dependence that does not
exist.

DERIVED: every numeral is carried in from the three conjuncts unchanged — `0` as the strict bound
the tension is compared against, the limit of the mode sum, the sign of `c` and the lower end of the
coupling half-line; `3` in `aRun 3` as the colour count of `WilsonBridge.corrClay`'s ensemble,
`SU(3)`, carried from `physical_gap_at_the_running_spacing`. This declaration introduces none. -/
theorem clay_assembly_of_lawAbove {Idx : Type}
    (habove : ∀ b : ℝ, MassGap.NonnegArm.LawBelow b → MassGap.NonnegArm.LawAbove b)
    (s : ℝ → Finset Idx) (Pw m : ℝ → Idx → ℂ) (Δ cf : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β)) :
    (∃ N : ℕ,
      ∀ (hfe : ∀ β, MassGap.κ₀YM - MassGap.μClampAt N β ≤ cf β)
        (hgap : ∀ β, cf β ≤ Δ β),
        (∀ β, Filter.Tendsto
            (fun τ => ‖∑ k ∈ (MassGap.gapModelOf N s Pw m Δ cf hdom hfe hgap).s β,
              (MassGap.gapModelOf N s Pw m Δ cf hdom hfe hgap).P β k
                * ((MassGap.gapModelOf N s Pw m Δ cf hdom hfe hgap).m β k) ^ τ‖)
            Filter.atTop (nhds 0))
          ∧ (∀ β, (MassGap.gapModelOf N s Pw m Δ cf hdom hfe hgap).μ β
              - (MassGap.gapModelOf N s Pw m Δ cf hdom hfe hgap).κ < 0)
          ∧ (∀ d d', (MassGap.gapModelOf N s Pw m Δ cf hdom hfe hgap).R d
              = (MassGap.gapModelOf N s Pw m Δ cf hdom hfe hgap).R d'))
    ∧ (∃ (c : ℝ) (N₀ : ℕ), 0 < c ∧
        ∀ (i : ℕ) (β : ℝ), 0 ≤ β → c ≤ MassGap.κ₀YM - MassGap.μYMAt (N₀ + i) β)
    ∧ (∃ (c : ℝ) (N₀ : ℕ), 0 < c ∧
        ∀ (i : ℕ) (a β₁ : ℝ), 0 ≤ β₁ → 0 < a →
          a < MassGap.AsymptoticScaling.aRun 3 β₁ →
          ∃ β : ℝ, β₁ ≤ β ∧ MassGap.AsymptoticScaling.aRun 3 β = a ∧
            c ≤ MassGap.κ₀YM - MassGap.μYMAt (N₀ + i) β) :=
  ⟨exists_aperture_mass_gap_of_lawAbove habove s Pw m Δ cf hdom,
    exists_uniform_margin_of_lawAbove habove,
    physical_gap_at_the_running_spacing habove⟩

#print axioms clay_assembly_of_lawAbove

/-- **A uniform substrate bound drives the substrate RATIO to zero**, so it eventually clears any
positive `c`.

`substrateRatio N β = d2At N β / (N+1)²` (`Complete.substrateRatio`), so a bound that does not grow
with the aperture is divided by something that does.

DERIVED: `0` is the sign of `c` and the lower end of the coupling half-line; `1` is the aperture's
index offset in `(N : ℝ) + 1`; `2` is the square in `substrateRatio`'s denominator. All are carried
from `Complete.substrateRatio_le_iff`. -/
theorem ratio_eventually_below_of_substrate_bound {B c : ℝ} (hc : 0 < c)
    (hB : ∀ N : ℕ, ∀ β : ℝ, 0 ≤ β → MassGap.d2At N β ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, 0 ≤ β → MassGap.substrateRatio N β ≤ c := by
  obtain ⟨M, hM⟩ := exists_nat_gt (B / c)
  refine Filter.eventually_atTop.mpr ⟨M, fun N hNM β hβ => ?_⟩
  rw [MassGap.substrateRatio_le_iff]
  have hMN : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNM
  have hdiv : B / c < ((N : ℝ) + 1) := by linarith
  rw [div_lt_iff₀ hc] at hdiv
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hsq : ((N : ℝ) + 1) ≤ ((N : ℝ) + 1) ^ 2 := by nlinarith
  have hstep : c * ((N : ℝ) + 1) ≤ c * ((N : ℝ) + 1) ^ 2 := by nlinarith
  have := hB N β hβ
  nlinarith [hdiv, hstep]

#print axioms ratio_eventually_below_of_substrate_bound

/-- **THE RATIO ROUTE IS THE WEAKER TARGET, and its side condition comes discharged.**

From `LawAbove` above `lawBelow_holds`' cut: a `c > 0` that already satisfies
`Complete.ym_mass_gap_of_ratio`'s arithmetic condition `(2π)²·c/2 < 1 − 3^{−1/4}`, together with
`substrateRatio N β ≤ c` at every sufficiently wide aperture and every nonnegative coupling.

Why it is worth stating. `confinement_on_of_substrate_bound` consumes a UNIFORM bound on `d2At`;
`ym_mass_gap_of_ratio` consumes a bound on `d2At / (N+1)²`. The first implies the second and not
conversely — a uniform bound sends the ratio to zero, while the ratio route still admits `d2At`
growing like `c·(N+1)²`. So anyone attacking the open input should aim at the ratio, which asks for
less, and this says so in the tree rather than in a note beside it.

The witness `c = (1 − 3^{−1/4})/(2π)²` makes the condition's left-hand side exactly half its right,
so the strict inequality is `Moment.floor_rhs_pos` and nothing is tuned.

DERIVED: `3`, `1` and `4` are the entropy floor `3^{−1/4} = e^{−κ₀}`; `2π` is one turn, and the
outer `2` squares it, both `ym_mass_gap_of_ratio`'s; the `2` dividing is that condition's own. `0` is
the sign of `c` and the lower end of the coupling half-line. The witness is the condition solved for
`c` at equality and halved, so it is read off the condition rather than chosen. -/
theorem ratio_hypothesis_of_lawAbove
    (habove : ∀ b : ℝ, MassGap.NonnegArm.LawBelow b → MassGap.NonnegArm.LawAbove b) :
    ∃ c : ℝ, 0 < c ∧ (2 * Real.pi) ^ 2 * c / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) ∧
      ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, 0 ≤ β → MassGap.substrateRatio N β ≤ c := by
  obtain ⟨b, _, hbelow⟩ := MassGap.NonnegArm.lawBelow_holds
  obtain ⟨B, hB⟩ := substrate_bounded_of_two_arms hbelow (habove b hbelow)
  have hrhs : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) := Moment.floor_rhs_pos
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
  refine ⟨(1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / (2 * Real.pi) ^ 2, by positivity, ?_, ?_⟩
  · have hcol : (2 * Real.pi) ^ 2 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / (2 * Real.pi) ^ 2) / 2
        = (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 2 := by
      field_simp
    rw [hcol]
    linarith
  · exact ratio_eventually_below_of_substrate_bound (by positivity) hB

#print axioms ratio_hypothesis_of_lawAbove

/-- The spectral reduction at ONE aperture and ONE coupling. The core of
`substrate_bound_on_of_uniform_spectral_rate`, stated per-point because that is what its proof uses:
the representation is read at the `(N, β)` being bounded and nowhere else.

Stating it this way is what lets the bound be asked for eventually in the aperture
(`confines_of_eventual_spectral_rate`) without handing one aperture's representation to another.

DERIVED: `2` multiplying `W` is `GeometricProfile.profile_geometric_of_periodic_spectral`'s, from the
two halves of the periodic pair; the outer `2` is `Moment.circ_moment_le_of_geometric`'s, from the
two lags at each circle distance; the exponent `2` is what a second moment is. `1` is the aperture's
index offset and the rates' strict bound. `0` is the sign of the rate and the weights. -/
theorem substrate_bound_at_of_uniform_spectral_rate {r W : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hW : 0 ≤ W) {N : ℕ} {β : ℝ}
    (hrep : ∃ (ι : Type) (s : Finset ι) (w m : ι → ℝ),
      (∀ k ∈ s, 0 ≤ w k) ∧ (∀ k ∈ s, 0 ≤ m k) ∧ (∀ k ∈ s, m k ≤ r) ∧
      (∑ k ∈ s, w k) ≤ W ∧
      (∀ d : Fin (N + 1), (MassGap.readYMAt N β).p d
        = ∑ k ∈ s, w k * ((m k) ^ ((d : ℕ)) + (m k) ^ (N + 1 - (d : ℕ))))) :
    MassGap.d2At N β ≤ 2 * (2 * W) * ∑' k : ℕ, (k : ℝ) ^ 2 * r ^ k := by
  obtain ⟨ι, s, w, m, hw, hm0, hmr, hsum, hrep⟩ := hrep
  -- the representation gives a geometric profile, with constant `2 * ∑ w`
  have hgeo : ∀ d : Fin (N + 1),
      (MassGap.readYMAt N β).p d ≤ (2 * W) * r ^ (Moment.circLag d) := by
    intro d
    have h := MassGap.GeometricProfile.profile_geometric_of_periodic_spectral
      (MassGap.readYMAt N β) s w m hr1 hw hm0 hmr hrep d
    have hrpow : (0 : ℝ) ≤ r ^ (Moment.circLag d) := pow_nonneg hr0 _
    have hmul : (2 * ∑ k ∈ s, w k) * r ^ (Moment.circLag d)
        ≤ (2 * W) * r ^ (Moment.circLag d) :=
      mul_le_mul_of_nonneg_right (by linarith) hrpow
    exact le_trans h hmul
  -- `circ_moment_le_of_geometric` is a standalone theorem taking the read explicitly, not a
  -- projection on it; called here the way `Complete.lean:602` calls it.
  have hmom := Moment.circ_moment_le_of_geometric (MassGap.readYMAt N β)
    (C := 2 * W) (r := r) (by linarith) hr0 hr1 hgeo
  have hd2 : MassGap.d2At N β
      = ∑ d, (MassGap.readYMAt N β).p d * (Moment.circLag d : ℝ) ^ 2 := rfl
  rw [hd2]
  exact hmom

#print axioms substrate_bound_at_of_uniform_spectral_rate

/-- **THE SUBSTRATE BOUND FROM A UNIFORM SPECTRAL RATE.** If at every aperture and every nonnegative
coupling the read `readYMAt N β` has a periodic spectral representation whose rates are all at most
`r < 1` and whose total weight is at most `W`, then

    d2At N β ≤ 2·(2W)·∑' k² rᵏ

at every `N` and every `β ≥ 0` — a bound containing neither the aperture nor the coupling.

This is the open input restated as a RATE. `NonnegArm.LawAbove` is a quartic tail law relative to the
contact term; this is a bound on the decay rate of the connected correlation's spectral modes, which
is what the Entroptics instrument computes directly — its `connected_decay_rate`, `-log |μ₁|` of
the connected read). Every step already existed and none had been composed:
`GeometricProfile.profile_geometric_of_periodic_spectral` turns the representation into a geometric
profile, and `Moment.circ_moment_le_of_geometric` turns that into a moment bound whose right-hand
side has no `N` in it.

The weight hypothesis is mild: `R.p` sums to one and each mode's own sum over the circle is at least
one, so `∑ w ≤ 1` follows from the representation. It is carried rather than derived, so the statement
does not depend on that reading.

**The representation must be off the vacuum, and that is not a technicality.**
`Transfer.one_le_of_eigenvalues_le` proves that a bound `∀ i, lam i ≤ r` read over the FULL transfer
spectrum forces `1 ≤ r`, because the vacuum is a unit eigenvector at eigenvalue one; and
`Spectral.PeriodicSpectralForm` carries no field excluding it. So instantiating `hspec` from a form
that contains the vacuum mode makes `hmr` unsatisfiable for any `r < 1`. What makes the hypothesis
about something is that `wilsonCorrAt` is the CONNECTED correlation — `WilsonBridge.wilsonCorrConn`
subtracts the product of the one-plaquette expectations, which is the vacuum's contribution — so its
modes are the non-vacuum ones. `TransferGap.GapAt` is stated on the vacuum complement for the same
reason.

`spectral_rate_representation_at_zero_coupling` exhibits an instance, so the shape is not empty.

DERIVED: `2` multiplying `W` is `profile_geometric_of_periodic_spectral`'s, from the two halves
`m^d` and `m^(N+1-d)` of the periodic pair; the outer `2` is `circ_moment_le_of_geometric`'s, from
the two lags at each circle distance. The exponent `2` is what a second moment is. `1` is the
aperture's index offset and the bound the rates are below. `0` is the sign of the rates, the weights
and the coupling. No constant is chosen: `B` is read off the two lemmas composed. -/
theorem substrate_bound_on_of_uniform_spectral_rate {r W : ℝ} {S : Set ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hW : 0 ≤ W)
    (hspec : ∀ (N : ℕ), ∀ β ∈ S,
      ∃ (ι : Type) (s : Finset ι) (w m : ι → ℝ),
        (∀ k ∈ s, 0 ≤ w k) ∧ (∀ k ∈ s, 0 ≤ m k) ∧ (∀ k ∈ s, m k ≤ r) ∧
        (∑ k ∈ s, w k) ≤ W ∧
        (∀ d : Fin (N + 1), (MassGap.readYMAt N β).p d
          = ∑ k ∈ s, w k * ((m k) ^ ((d : ℕ)) + (m k) ^ (N + 1 - (d : ℕ))))) :
    ∀ (N : ℕ), ∀ β ∈ S,
      MassGap.d2At N β ≤ 2 * (2 * W) * ∑' k : ℕ, (k : ℝ) ^ 2 * r ^ k :=
  fun N β hβ => substrate_bound_at_of_uniform_spectral_rate hr0 hr1 hW (hspec N β hβ)

#print axioms substrate_bound_on_of_uniform_spectral_rate

/-- The nonnegative half-line instance of `substrate_bound_on_of_uniform_spectral_rate`, kept
because `Set.Ici 0` is the domain every other arm in this file is stated on and the membership form
reads awkwardly beside them.

DERIVED: `0` is the lower end of the coupling half-line and the sign of the rate and the weight
bound; `1` is the rate's strict upper bound and the aperture's index offset; the `2`s are the
periodic pair, the two lags per circle distance and the second moment's exponent. All are the set
version's, carried unchanged. -/
theorem substrate_bound_of_uniform_spectral_rate {r W : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hW : 0 ≤ W)
    (hspec : ∀ (N : ℕ) (β : ℝ), 0 ≤ β →
      ∃ (ι : Type) (s : Finset ι) (w m : ι → ℝ),
        (∀ k ∈ s, 0 ≤ w k) ∧ (∀ k ∈ s, 0 ≤ m k) ∧ (∀ k ∈ s, m k ≤ r) ∧
        (∑ k ∈ s, w k) ≤ W ∧
        (∀ d : Fin (N + 1), (MassGap.readYMAt N β).p d
          = ∑ k ∈ s, w k * ((m k) ^ ((d : ℕ)) + (m k) ^ (N + 1 - (d : ℕ))))) :
    ∀ (N : ℕ) (β : ℝ), 0 ≤ β →
      MassGap.d2At N β ≤ 2 * (2 * W) * ∑' k : ℕ, (k : ℝ) ^ 2 * r ^ k :=
  fun N β hβ =>
    substrate_bound_on_of_uniform_spectral_rate (S := Set.Ici (0 : ℝ)) hr0 hr1 hW
      (fun N' β' hβ' => hspec N' β' hβ') N β hβ

#print axioms substrate_bound_of_uniform_spectral_rate

/-- **Confinement from a uniform spectral rate**, composing the bound above with
`Complete.confinement_on_of_substrate_bound`: at every sufficiently wide aperture the tension stays
strictly below the entropy floor at every nonnegative coupling.

So the whole chain of §1 runs from a rate, with no quartic law and no threshold.

DERIVED: every numeral is carried from `substrate_bound_of_uniform_spectral_rate` — the `2`s of the
periodic pair, the two lags per circle distance, and the second moment's exponent; `1` the rates'
strict bound and the aperture offset; `0` the signs. -/
theorem confines_of_uniform_spectral_rate {r W : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hW : 0 ≤ W)
    (hspec : ∀ (N : ℕ) (β : ℝ), 0 ≤ β →
      ∃ (ι : Type) (s : Finset ι) (w m : ι → ℝ),
        (∀ k ∈ s, 0 ≤ w k) ∧ (∀ k ∈ s, 0 ≤ m k) ∧ (∀ k ∈ s, m k ≤ r) ∧
        (∑ k ∈ s, w k) ≤ W ∧
        (∀ d : Fin (N + 1), (MassGap.readYMAt N β).p d
          = ∑ k ∈ s, w k * ((m k) ^ ((d : ℕ)) + (m k) ^ (N + 1 - (d : ℕ))))) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, 0 ≤ β → MassGap.μYMAt N β < MassGap.κ₀YM := by
  have hB := substrate_bound_of_uniform_spectral_rate hr0 hr1 hW hspec
  have hev := MassGap.confinement_on_of_substrate_bound
    (B := 2 * (2 * W) * ∑' k : ℕ, (k : ℝ) ^ 2 * r ^ k) (S := Set.Ici (0 : ℝ))
    (fun N β hβ => hB N β hβ)
  filter_upwards [hev] with N hN β hβ
  exact hN β hβ

#print axioms confines_of_uniform_spectral_rate

/-- **The spectral-rate representation, at zero coupling, with rate `0`.** At `β = 0` the read is a
point mass at the contact lag, and a single mode of rate `0` reproduces it exactly:
`0^0 + 0^(N+1) = 1` at `d = 0`, and `0 + 0` at every other lag.

So `substrate_bound_of_uniform_spectral_rate`'s hypothesis is satisfiable — at rate `0`, which is
below every admissible `r`. Without this the reduction could be about an empty shape, which is the
failure `Transfer.one_le_of_eigenvalues_le` describes for the full-spectrum reading.

`PowerTail.wilsonCorrAt_at_zero_coupling` kills every lag of nonzero circle distance and
`PowerTail.contact_value_pos_at_zero_coupling` keeps the denominator positive, so the normalised read
is exactly the indicator of the contact lag.

DERIVED: `0` is the coupling, the mode's rate, the contact lag, and the value at every other lag;
`1` is the mode's weight and the aperture's index offset. Both are the point mass's own description,
not magnitudes. -/
theorem spectral_rate_representation_at_zero_coupling (N : ℕ) :
    ∀ d : Fin (N + 1), (MassGap.readYMAt N 0).p d
      = ∑ _k ∈ ({0} : Finset (Fin 1)), (1 : ℝ)
        * (((0 : ℝ)) ^ ((d : ℕ)) + ((0 : ℝ)) ^ (N + 1 - (d : ℕ))) := by
  intro d
  -- At `β = 0` the read's clamp is inert (`Complete.readYMAt_rho_of_nonneg`).
  have hρ : ∀ e : Fin (N + 1), (MassGap.readYMAt N 0).ρ e = MassGap.wilsonCorrAt N 0 e :=
    MassGap.readYMAt_rho_of_nonneg N le_rfl
  have hpos : 0 < (MassGap.readYMAt N 0).ρ 0 := by
    rw [hρ]; exact MassGap.PowerTail.contact_value_pos_at_zero_coupling N
  have hsum : ∑ _k ∈ ({0} : Finset (Fin 1)), (1 : ℝ)
      * (((0 : ℝ)) ^ ((d : ℕ)) + ((0 : ℝ)) ^ (N + 1 - (d : ℕ)))
      = ((0 : ℝ)) ^ ((d : ℕ)) + ((0 : ℝ)) ^ (N + 1 - (d : ℕ)) := by
    simp
  rw [hsum]
  by_cases hd : (d : ℕ) = 0
  · -- the contact lag: the first power is `0 ^ 0 = 1`, the second is `0 ^ (N+1) = 0`
    have hd0 : d = (0 : Fin (N + 1)) := Fin.ext (by simpa using hd)
    subst hd0
    have hrhs : ((0 : ℝ)) ^ ((0 : Fin (N + 1)) : ℕ) + ((0 : ℝ)) ^ (N + 1 - ((0 : Fin (N + 1)) : ℕ))
        = 1 := by simp
    rw [hrhs]
    show (MassGap.readYMAt N 0).p 0 = 1
    -- the profile vanishes off the contact lag, so the total mass IS the contact value
    have hz : ∀ e : Fin (N + 1), e ≠ 0 → (MassGap.readYMAt N 0).ρ e = 0 := by
      intro e he
      have h1 : 1 ≤ Moment.circLag e := by
        have : (e : ℕ) ≠ 0 := fun h => he (Fin.ext (by simpa using h))
        have hlt := e.isLt
        simp only [Moment.circLag]
        omega
      rw [hρ]
      exact MassGap.PowerTail.wilsonCorrAt_at_zero_coupling N e h1
    have htot : (∑ e, (MassGap.readYMAt N 0).ρ e) = (MassGap.readYMAt N 0).ρ 0 := by
      refine Finset.sum_eq_single (0 : Fin (N + 1)) (fun e _ he => hz e he) (fun h => absurd
        (Finset.mem_univ (0 : Fin (N + 1))) h)
    show (MassGap.readYMAt N 0).ρ 0 / (∑ e, (MassGap.readYMAt N 0).ρ e) = 1
    rw [htot]
    exact div_self (ne_of_gt hpos)
  · -- every other lag: both powers are `0`, and the profile vanishes there
    have hd1 : 1 ≤ Moment.circLag d := by
      have hlt := d.isLt
      simp only [Moment.circLag]
      omega
    have hrhs : ((0 : ℝ)) ^ ((d : ℕ)) + ((0 : ℝ)) ^ (N + 1 - (d : ℕ)) = 0 := by
      have h1 : ((0 : ℝ)) ^ ((d : ℕ)) = 0 := zero_pow hd
      have h2 : ((0 : ℝ)) ^ (N + 1 - (d : ℕ)) = 0 := by
        have : N + 1 - (d : ℕ) ≠ 0 := by have := d.isLt; omega
        exact zero_pow this
      rw [h1, h2]; ring
    rw [hrhs]
    show (MassGap.readYMAt N 0).ρ d / (∑ e, (MassGap.readYMAt N 0).ρ e) = 0
    have hzd : (MassGap.readYMAt N 0).ρ d = 0 := by
      rw [hρ]
      exact MassGap.PowerTail.wilsonCorrAt_at_zero_coupling N d hd1
    rw [hzd]
    simp

#print axioms spectral_rate_representation_at_zero_coupling

/-- **The substrate bound from the tree's own `PeriodicSpectralForm`.**

`substrate_bound_of_uniform_spectral_rate` represents the NORMALISED read `R.p`;
`Spectral.PeriodicSpectralForm (N+1) (wilsonCorrAt N β)` represents the UNNORMALISED correlation.
They differ by the total mass, which `Moment.Read.hpos` keeps positive, so dividing each weight by
it carries one to the other. Without this the tree's spectral objects cannot reach the reduction.

`Complete.WilsonSpectral N β` is exactly `Nonempty (PeriodicSpectralForm (N+1) (wilsonCorrAt N β))`,
so whatever proves it — `SlabQuadratic.wilsonSpectral` at one aperture for every nonnegative
coupling, `Spectral2.wilsonSpectral_at_zero_coupling` at every aperture at zero coupling — feeds the
substrate bound through this, once a rate is supplied.

The rate bound is the whole content, and a form alone does not give it: `PeriodicSpectralForm`
carries `hlam1 : lam k ≤ 1` with no field excluding the vacuum mode, and
`Substrate.flatSpectral` exhibits the flat profile as a single mode at `lam = 1`, whose moment is
unbounded. `hlam` is what separates a gapped correlation from that one.

DERIVED: `2` multiplying `W` and the outer `2` are carried from
`substrate_bound_of_uniform_spectral_rate` — the periodic pair and the two lags per circle distance;
the exponent `2` is the second moment's. `1` is the aperture's index offset. `0` is the sign of the
rate, the weights and the coupling. Nothing is introduced here. -/
theorem substrate_bound_of_periodic_spectral_rate {r W : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hW : 0 ≤ W)
    (hform : ∀ (N : ℕ) (β : ℝ), 0 ≤ β →
      ∃ F : Spectral.PeriodicSpectralForm (N + 1) (MassGap.wilsonCorrAt N β),
        (∀ k, F.lam k ≤ r) ∧
        (∑ k, F.w k) / (∑ e, (MassGap.readYMAt N β).ρ e) ≤ W) :
    ∀ (N : ℕ) (β : ℝ), 0 ≤ β →
      MassGap.d2At N β ≤ 2 * (2 * W) * ∑' k : ℕ, (k : ℝ) ^ 2 * r ^ k := by
  refine substrate_bound_of_uniform_spectral_rate hr0 hr1 hW ?_
  intro N β hβ
  obtain ⟨F, hlam, hwt⟩ := hform N β hβ
  have hTpos : 0 < ∑ e, (MassGap.readYMAt N β).ρ e := (MassGap.readYMAt N β).hpos
  refine ⟨F.Idx, Finset.univ, (fun k => F.w k / (∑ e, (MassGap.readYMAt N β).ρ e)), F.lam,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact fun k _ => div_nonneg (F.hw k) (le_of_lt hTpos)
  · exact fun k _ => F.hlam0 k
  · exact fun k _ => hlam k
  · rw [← Finset.sum_div]; exact hwt
  · intro d
    -- at `0 ≤ β` the read's clamp is inert (`Complete.readYMAt_rho_of_nonneg`).
    have hrho : (MassGap.readYMAt N β).ρ d = MassGap.wilsonCorrAt N β d :=
      MassGap.readYMAt_rho_of_nonneg N hβ d
    show (MassGap.readYMAt N β).ρ d / (∑ e, (MassGap.readYMAt N β).ρ e) = _
    rw [hrho, F.hrep d, Finset.sum_div]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring

#print axioms substrate_bound_of_periodic_spectral_rate

/-- **Confinement from a periodic spectral form with a uniform rate.** The previous theorem composed
with `Complete.confinement_on_of_substrate_bound`: at every sufficiently wide aperture the tension
stays strictly below the entropy floor at every nonnegative coupling.

The whole chain of §1 now runs from a spectral rate on the tree's own `PeriodicSpectralForm`, with
no quartic law, no threshold and no supplied constant.

DERIVED: `0` is the sign of the rate, of the weight bound and of the coupling, and `1` is the rate's
strict upper bound and the aperture's index offset in `Fin (N + 1)` — all carried from
`substrate_bound_of_periodic_spectral_rate` unchanged. This declaration introduces no numeral. -/
theorem confines_of_periodic_spectral_rate {r W : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hW : 0 ≤ W)
    (hform : ∀ (N : ℕ) (β : ℝ), 0 ≤ β →
      ∃ F : Spectral.PeriodicSpectralForm (N + 1) (MassGap.wilsonCorrAt N β),
        (∀ k, F.lam k ≤ r) ∧
        (∑ k, F.w k) / (∑ e, (MassGap.readYMAt N β).ρ e) ≤ W) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, 0 ≤ β → MassGap.μYMAt N β < MassGap.κ₀YM := by
  have hB := substrate_bound_of_periodic_spectral_rate hr0 hr1 hW hform
  have hev := MassGap.confinement_on_of_substrate_bound
    (B := 2 * (2 * W) * ∑' k : ℕ, (k : ℝ) ^ 2 * r ^ k) (S := Set.Ici (0 : ℝ))
    (fun N β hβ => hB N β hβ)
  filter_upwards [hev] with N hN β hβ
  exact hN β hβ

#print axioms confines_of_periodic_spectral_rate

/-- **THE TWO ARMS, WITH A SPECTRAL RATE ABOVE THE CUT.**

`substrate_bounded_of_two_arms` pairs `NonnegArm.LawBelow b` with `NonnegArm.LawAbove b`.
`lawBelow_holds` proves the first outright, so only the arm above the cut is open — and it need not
be a quartic law. This pairs the proved arm with a spectral rate on `(b, ∞)`.

So the spectral route is asked for the couplings ABOVE the strong-coupling cut only, not for every
coupling at once. That is the same two-arm shape `NonnegArm.substrate_even_of_two_arm` uses, with a
different object on the open side.

The two branches reach the moment by different routes — a quartic-weight sum below the cut, a
geometric sum above it — so unlike `substrate_bounded_of_two_arms` they cannot be funnelled through
one lemma; each is bounded separately and the maximum serves both.

DERIVED: `1` is the lag cut excluding the contact term, `ShareEnvelope.circ_moment_le_of_contact_relative`'s
own, and the rate's strict upper bound, and the aperture's index offset. The `2`s are the quartic
weight's leading factor, the periodic pair, the two lags per circle distance, and the second moment's
exponent. `4` is the quartic law's exponent, `NonnegArm.LawBelow`'s. `0` is the sign of the rate, the
weight bound and the coupling. Every one is carried in from the arm it belongs to. -/
theorem substrate_bounded_of_below_arm_and_spectral_rate {b r W : ℝ}
    (hbelow : MassGap.NonnegArm.LawBelow b)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hW : 0 ≤ W)
    (hspec : ∀ (N : ℕ), ∀ β ∈ Set.Ioi b,
      ∃ (ι : Type) (s : Finset ι) (w m : ι → ℝ),
        (∀ k ∈ s, 0 ≤ w k) ∧ (∀ k ∈ s, 0 ≤ m k) ∧ (∀ k ∈ s, m k ≤ r) ∧
        (∑ k ∈ s, w k) ≤ W ∧
        (∀ d : Fin (N + 1), (MassGap.readYMAt N β).p d
          = ∑ k ∈ s, w k * ((m k) ^ ((d : ℕ)) + (m k) ^ (N + 1 - (d : ℕ))))) :
    ∃ B : ℝ, ∀ (N : ℕ) (β : ℝ), 0 ≤ β → MassGap.d2At N β ≤ B := by
  obtain ⟨C₁, hC₁, h₁⟩ := hbelow
  have hspecB := substrate_bound_on_of_uniform_spectral_rate (S := Set.Ioi b) hr0 hr1 hW hspec
  refine ⟨max (2 * ∑' k : ℕ, (k : ℝ) ^ 2 * MassGap.ShareEnvelope.quarticWeight 1 C₁ k)
      (2 * (2 * W) * ∑' k : ℕ, (k : ℝ) ^ 2 * r ^ k), fun N β hβ0 => ?_⟩
  rcases le_or_gt β b with hle | hgt
  · -- below the cut: the proved quartic arm, as `substrate_bounded_of_two_arms` uses it
    have hb : MassGap.d2At N β
        ≤ 2 * ∑' k : ℕ, (k : ℝ) ^ 2 * MassGap.ShareEnvelope.quarticWeight 1 C₁ k := by
      refine MassGap.ShareEnvelope.circ_moment_le_of_contact_relative
        (MassGap.readYMAt N β) 1 hC₁ ?_
      intro d hd
      simp only [MassGap.ShareEnvelope.readYMAt_rho, max_eq_left hβ0]
      exact h₁ N β d hβ0 hle hd
    exact le_trans hb (le_max_left _ _)
  · -- above the cut: the spectral rate
    exact le_trans (hspecB N β hgt) (le_max_right _ _)

#print axioms substrate_bounded_of_below_arm_and_spectral_rate

/-- **Confinement from the proved arm and a spectral rate above the cut.** The previous theorem
composed with `Complete.confinement_on_of_substrate_bound`.

This is the chain of §1 with its open half replaced: no quartic law above the cut, no threshold, and
the strong-coupling arm supplied by `NonnegArm.lawBelow_holds` rather than assumed.

DERIVED: every numeral is the previous theorem's — `0` the signs and the coupling half-line's lower
end, `1` the lag cut and the rate's strict bound and the aperture offset, the `2`s the quartic
weight, the periodic pair, the two lags per circle distance and the second moment's exponent, and `4`
the quartic exponent. This declaration introduces none. -/
theorem confines_of_below_arm_and_spectral_rate {b r W : ℝ}
    (hbelow : MassGap.NonnegArm.LawBelow b)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hW : 0 ≤ W)
    (hspec : ∀ (N : ℕ), ∀ β ∈ Set.Ioi b,
      ∃ (ι : Type) (s : Finset ι) (w m : ι → ℝ),
        (∀ k ∈ s, 0 ≤ w k) ∧ (∀ k ∈ s, 0 ≤ m k) ∧ (∀ k ∈ s, m k ≤ r) ∧
        (∑ k ∈ s, w k) ≤ W ∧
        (∀ d : Fin (N + 1), (MassGap.readYMAt N β).p d
          = ∑ k ∈ s, w k * ((m k) ^ ((d : ℕ)) + (m k) ^ (N + 1 - (d : ℕ))))) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, 0 ≤ β → MassGap.μYMAt N β < MassGap.κ₀YM := by
  obtain ⟨B, hB⟩ := substrate_bounded_of_below_arm_and_spectral_rate hbelow hr0 hr1 hW hspec
  have hev := MassGap.confinement_on_of_substrate_bound (B := B) (S := Set.Ici (0 : ℝ))
    (fun N β hβ => hB N β hβ)
  filter_upwards [hev] with N hN β hβ
  exact hN β hβ

#print axioms confines_of_below_arm_and_spectral_rate

/-- **The substrate bound is only needed at large apertures.**

`Complete.confinement_on_of_substrate_bound` asks for `d2At N β ≤ B` at EVERY aperture and concludes
confinement EVENTUALLY in the aperture. The conclusion is eventual because the aperture factor
`(2π/(N+1))²` must first shrink below the floor, and the proof reads the substrate bound only where
it has — so the hypothesis at small apertures is never used.

Weakening it costs one `filter_upwards` over two facts instead of one. It matters for the open
input: the small apertures are where the read is coarsest and a spectral representation hardest to
supply, and they are not needed.

DERIVED: `2 * Real.pi` is the full turn and the outer `2` squares the aperture factor, both
`Moment.aperture_factor_tendsto_zero`'s; the `2` dividing `B` is `Moment.Read.cos_avg_ge_circ`'s
halving; `1` in `(N : ℝ) + 1` is the aperture's index offset and the value the floor is subtracted
from; `3`, `1` and `4` are the entropy floor `3^{−1/4}`. Every one is carried from
`confinement_on_of_substrate_bound`, whose proof this mirrors. -/
theorem confinement_on_of_eventual_substrate_bound {B : ℝ} {S : Set ℝ}
    (hB : ∀ᶠ N : ℕ in Filter.atTop, ∀ β ∈ S, MassGap.d2At N β ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β ∈ S, MassGap.μYMAt N β < MassGap.κ₀YM := by
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) :=
    (Moment.aperture_factor_tendsto_zero B).eventually_lt_const Moment.floor_rhs_pos
  filter_upwards [hev, hB] with N hN hBN β hβ
  exact (MassGap.readYMAt N β).tension_lt_floor_of_circ_moment (hBN β hβ) hN

#print axioms confinement_on_of_eventual_substrate_bound

/-- **Confinement from a spectral rate supplied only at large apertures.**

The per-point reduction applied under a `filter_upwards`, then
`confinement_on_of_eventual_substrate_bound`. Per-point is what makes this sound: the representation
at one aperture is used to bound that aperture and no other.

Taken with `substrate_bounded_of_below_arm_and_spectral_rate`, the open input has three relaxations
against `NonnegArm.LawAbove` — it is a spectral RATE rather than a quartic tail law, it is asked only
ABOVE the strong-coupling cut, and it is asked only at SUFFICIENTLY WIDE apertures.

DERIVED: every numeral is carried from the two theorems composed — `0` the signs and the rate's lower
bound, `1` the rate's strict upper bound and the aperture's index offset, the `2`s the periodic pair,
the two lags per circle distance and the second moment's exponent. None is introduced here. -/
theorem confines_of_eventual_spectral_rate {r W : ℝ} {S : Set ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hW : 0 ≤ W)
    (hspec : ∀ᶠ N : ℕ in Filter.atTop, ∀ β ∈ S,
      ∃ (ι : Type) (s : Finset ι) (w m : ι → ℝ),
        (∀ k ∈ s, 0 ≤ w k) ∧ (∀ k ∈ s, 0 ≤ m k) ∧ (∀ k ∈ s, m k ≤ r) ∧
        (∑ k ∈ s, w k) ≤ W ∧
        (∀ d : Fin (N + 1), (MassGap.readYMAt N β).p d
          = ∑ k ∈ s, w k * ((m k) ^ ((d : ℕ)) + (m k) ^ (N + 1 - (d : ℕ))))) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β ∈ S, MassGap.μYMAt N β < MassGap.κ₀YM := by
  refine confinement_on_of_eventual_substrate_bound
    (B := 2 * (2 * W) * ∑' k : ℕ, (k : ℝ) ^ 2 * r ^ k) ?_
  filter_upwards [hspec] with N hN β hβ
  exact substrate_bound_at_of_uniform_spectral_rate hr0 hr1 hW (hN β hβ)

#print axioms confines_of_eventual_spectral_rate

/-- **THE ASSEMBLY FROM A SPECTRAL RATE ABOVE THE CUT** — the smallest input in this file.

One hypothesis: at every aperture and every coupling strictly above the cut that
`NonnegArm.lawBelow_holds` supplies, the read has a periodic spectral representation whose rates are
at most `r < 1` and whose total weight is at most `W`. From it, three conclusions:

1. confinement — the tension strictly below the entropy floor at every nonnegative coupling, at every
   sufficiently wide aperture;
2. one positive `c` below the surplus `κ₀YM − μYMAt` at every aperture past `N₀` and every `β ≥ 0`;
3. that margin divided by the spacing a screen of fixed physical extent carries, which is the form
   `Complete.ym_physical_gap_uniform_exact` and `ScreenedGap.uniform_physical_gap` are stated in.

`clay_assembly_of_lawAbove` is the same three from `LawAbove`, a quartic tail law at every coupling
above the cut. This asks for less in three ways: a RATE rather than a tail law, only ABOVE the cut,
and — through `confines_of_eventual_spectral_rate` — the aperture condition is eventual rather than
universal.

The cut is not a parameter: `lawBelow_holds` produces it, so the caller supplies only the rate and
never chooses `b`.

All three conclusions come from one substrate bound, and all three consumers already take it. That
is what routing through the substrate bound rather than through `LawAbove` bought.

DERIVED: `0` is the sign of the rate, the weight bound, `c`, and the lower end of the coupling
half-line; `1` is the rate's strict upper bound and the aperture's index offset; the `2`s are the
periodic pair, the two lags per circle distance, and the second moment's exponent; `4` is the quartic
exponent of the arm below the cut. Every one is carried in from the theorem it belongs to. -/
theorem clay_assembly_of_spectral_rate {r W : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hW : 0 ≤ W)
    (hspec : ∀ b : ℝ, MassGap.NonnegArm.LawBelow b → ∀ (N : ℕ), ∀ β ∈ Set.Ioi b,
      ∃ (ι : Type) (s : Finset ι) (w m : ι → ℝ),
        (∀ k ∈ s, 0 ≤ w k) ∧ (∀ k ∈ s, 0 ≤ m k) ∧ (∀ k ∈ s, m k ≤ r) ∧
        (∑ k ∈ s, w k) ≤ W ∧
        (∀ d : Fin (N + 1), (MassGap.readYMAt N β).p d
          = ∑ k ∈ s, w k * ((m k) ^ ((d : ℕ)) + (m k) ^ (N + 1 - (d : ℕ))))) :
    (∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, 0 ≤ β → MassGap.μYMAt N β < MassGap.κ₀YM)
    ∧ (∃ (c : ℝ) (N₀ : ℕ), 0 < c ∧
        ∀ (i : ℕ) (β : ℝ), 0 ≤ β → c ≤ MassGap.κ₀YM - MassGap.μYMAt (N₀ + i) β)
    ∧ (∃ (c : ℝ) (N₀ : ℕ), 0 < c ∧
        ∀ (L : ℝ), 0 < L → ∀ (i : ℕ) (β : ℝ), 0 ≤ β →
          c / L ≤ (MassGap.κ₀YM - MassGap.μYMAt (N₀ + i) β)
            / (L / (((N₀ + i : ℕ) : ℝ) + 1))) := by
  obtain ⟨b, _, hbelow⟩ := MassGap.NonnegArm.lawBelow_holds
  obtain ⟨B, hB⟩ :=
    substrate_bounded_of_below_arm_and_spectral_rate hbelow hr0 hr1 hW (hspec b hbelow)
  refine ⟨?_, exists_uniform_margin_of_substrate (B := B) hB,
    exists_physical_gap_uniform_of_substrate (B := B) hB⟩
  have hev := MassGap.confinement_on_of_substrate_bound (B := B) (S := Set.Ici (0 : ℝ))
    (fun N β hβ => hB N β hβ)
  filter_upwards [hev] with N hN β hβ
  exact hN β hβ

#print axioms clay_assembly_of_spectral_rate












/-- A geometric tail in the lag, uniform in the aperture and in the coupling above the cut, gives
`NonnegArm.LawAbove b`.

`hdecay` asks for `ρ d ≤ ρ 0 * r ^ circLag d` with `0 ≤ r` and `r < 1`, at every aperture `N`, every
`β > b`, and every lag past the contact lag. `StrongArm.exists_geom_quartic_bound` supplies a
constant `S` dominating `(m + 1) ^ 4 * r ^ m` at every `m` — a geometric sequence dominates a
quartic outright, not eventually. Multiplying `hdecay` through by `circLag d ^ 4` and dividing back
gives `LawAbove`'s conclusion with constant `S`.

`ClayAssembly.flat_profile_admits_no_uniform_quartic_constant` concerns the aperture rather than the
coupling: `circLag d ≤ (N+1)/2` grows without bound, so what the quartic law asserts is decay of the
whitened profile in the lag, uniform in the volume. That is the object
`Certify.gap_uniform_in_volume_of_intensive` takes as its intensive premise, and nothing in the tree
produces it. A flat profile has no such rate.

`hdecay` is a hypothesis.

DERIVED: the `0` in `hr0 : 0 ≤ r` and the `1` in `hr1 : r < 1` bound the contraction ratio. The `1`
in `Fin (N + 1)` is the index offset, the number of lags aperture `N` carries. The `1` in
`1 ≤ Moment.circLag d` is the lag cut, excluding the contact lag. The `0` in `wilsonCorrAt N β 0` is
the contact lag the decay is stated relative to. The exponent `4` is inside `LawAbove`'s own
definition and does not appear in this statement; `(L + 1) ^ 4` occurs in the proof. -/
theorem lawAbove_of_geometric_tail {b r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hdecay : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)), b < β → 1 ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d
        ≤ MassGap.wilsonCorrAt N β 0 * r ^ (Moment.circLag d)) :
    MassGap.NonnegArm.LawAbove b := by
  obtain ⟨S, hS0, hS⟩ := MassGap.StrongArm.exists_geom_quartic_bound hr0 hr1
  refine ⟨S, hS0, fun N β d hβ hd => ?_⟩
  set L : ℕ := Moment.circLag d with hLdef
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hd
  have hLpos : (0 : ℝ) < (L : ℝ) ^ 4 := by positivity
  -- the contact value is the plaquette-energy variance, positive at every coupling
  have hρ0 : 0 ≤ MassGap.wilsonCorrAt N β 0 := (MassGap.PlaqVariance.corrClay_zero_pos N β).le
  have hrL : (0 : ℝ) ≤ r ^ L := pow_nonneg hr0 L
  -- `L⁴·r^L ≤ (L+1)⁴·r^L ≤ S`
  have hmono : ((L : ℝ)) ^ 4 * r ^ L ≤ (((L : ℝ)) + 1) ^ 4 * r ^ L := by
    have h0 : (0 : ℝ) ≤ (L : ℝ) := by positivity
    have hsucc : (L : ℝ) ≤ (L : ℝ) + 1 := by linarith
    have hbase : ((L : ℝ)) ^ 4 ≤ (((L : ℝ)) + 1) ^ 4 := by gcongr
    exact mul_le_mul_of_nonneg_right hbase hrL
  have hquart : ((L : ℝ)) ^ 4 * r ^ L ≤ S := le_trans hmono (hS L)
  -- `ρ d · L⁴ ≤ ρ 0 · S`
  have hstep : MassGap.wilsonCorrAt N β d * ((L : ℝ)) ^ 4
      ≤ MassGap.wilsonCorrAt N β 0 * S := by
    have h1 := mul_le_mul_of_nonneg_right (hdecay N β d hβ hd) (le_of_lt hLpos)
    have h2 : MassGap.wilsonCorrAt N β 0 * r ^ L * ((L : ℝ)) ^ 4
        ≤ MassGap.wilsonCorrAt N β 0 * S := by
      have hmul := mul_le_mul_of_nonneg_left hquart hρ0
      calc MassGap.wilsonCorrAt N β 0 * r ^ L * ((L : ℝ)) ^ 4
          = MassGap.wilsonCorrAt N β 0 * (((L : ℝ)) ^ 4 * r ^ L) := by ring
        _ ≤ MassGap.wilsonCorrAt N β 0 * S := hmul
    exact le_trans h1 h2
  -- divide by `L⁴`
  have hinv := mul_le_mul_of_nonneg_right hstep (le_of_lt (inv_pos.mpr hLpos))
  have hleft : MassGap.wilsonCorrAt N β d * ((L : ℝ)) ^ 4 * (((L : ℝ)) ^ 4)⁻¹
      = MassGap.wilsonCorrAt N β d := by
    field_simp
  rw [hleft] at hinv
  simpa only [div_eq_mul_inv, mul_comm] using hinv

#print axioms lawAbove_of_geometric_tail














/-! ## The substrate bound with the division performed -/

/-- `d2Even a β` as a ratio of two finite sums of `wilsonCorrAt a.1 (max β 0)`: the circle-lag
second moment over the total mass. The proof unfolds `Moment.Read.p` on `readEven a β` through
`NonnegArm.readEven_rho`, so it stays on `wilsonCorrAt` and does not mention `readYMAt`.

DERIVED: the `0` in each `max β 0` is the clamp point, the lower end of the physical coupling range;
the `2` is the exponent on the circle lag, the moment's own power. The `1`
in `a.1` is the `EvenAp` projection to the extent index. -/
theorem d2Even_eq_div (a : EvenAp) (β : ℝ) :
    d2Even a β
      = (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d * (Moment.circLag d : ℝ) ^ 2)
          / (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d) := by
  show ∑ d, (readEven a β).p d * (Moment.circLag d : ℝ) ^ 2 = _
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  simp only [Moment.Read.p, MassGap.NonnegArm.readEven_rho, div_mul_eq_mul_div]

#print axioms d2Even_eq_div

/-- The total mass `∑ d, wilsonCorrAt a.1 (max β 0) d` is strictly positive at every even aperture
and every coupling. It is `Moment.Read.hpos` of `readEven a β`, transported along
`NonnegArm.readEven_rho`: the second clause of the reflection-positivity statement, which at even
extent is a theorem rather than the named axiom.

DERIVED: the `0` in `0 < ∑ …` is the strict sign of the total mass; the `0` in `max β 0` is the
clamp point, the lower end of the physical coupling range. The `1` in `a.1` is the `EvenAp`
projection to the extent index. -/
theorem sum_wilsonCorrAt_pos (a : EvenAp) (β : ℝ) :
    0 < ∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d := by
  have h := (readEven a β).hpos
  simpa only [MassGap.NonnegArm.readEven_rho] using h

#print axioms sum_wilsonCorrAt_pos

/-- The substrate bound on `d2Even` is equivalent to the same bound with the division cleared: the
weighted sum of `wilsonCorrAt` at most `B` times the total mass.

`sum_wilsonCorrAt_pos` makes the denominator strictly positive at every aperture and coupling, so
`div_le_iff` runs in both directions, with `d2Even_eq_div` supplying the ratio form. The two sides
carry the same content; what the right-hand side removes is the ratio, leaving two finite sums of
`wilsonCorrAt`, which is the form `WilsonAnalytic`'s covariance identity and `ContactFloor`'s floor
act on.

DERIVED: the `0` in each `max β 0` is the clamp point, the lower end of the physical coupling range;
the `2` is the exponent on the circle lag, the moment's own power. The `1`
in `a.1` is the `EvenAp` projection to the extent index. -/
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
