import Mathlib
import MassGap.SpectralBound
import MassGap.InfiniteVolume
import MassGap.WeakArm

/-!
# MassGap.TailRatio — the lag-two ratio `wilsonCorrAt 3 β 2 / wilsonCorrAt 3 β 0`

`LagTwoBound.confines_of_lag_two_ratio` reduces `ApertureRoute.ConfinesAtAnAperture` at the smallest
even aperture to `ρ 2 ≤ K * ρ 0` with `K < LagTwoBound.lagTwoThreshold`, where
`ρ d = wilsonCorrAt 3 β d`. This module names that quotient as `lagTwoRatio β`, establishes its
elementary properties, and relates three statements about it.

## Section 1: the ratio

`contact_pos` gives `0 < wilsonCorrAt 3 β 0` at every real `β` (it is the plaquette-energy variance,
`PlaqVariance.corrClay_zero_pos`), so `lagTwoRatio` is total on `ℝ`. `lag_two_nonneg` gives
`0 ≤ wilsonCorrAt 3 β 2` at every real `β`, hence `lagTwoRatio_nonneg`. `ratio_le_iff`,
`ratio_lt_iff` and `ratio_mul_contact` move between the quotient and the product form.
`lagTwoRatio_continuous` is continuity on all of `ℝ`, from
`ConfinesZero.continuous_wilsonCorrAt`. `lagTwoRatio_at_zero_coupling` gives `lagTwoRatio 0 = 0`:
the numerator vanishes at zero coupling by `PowerTail.wilsonCorrAt_at_zero_coupling`, admissible
since the circle distance at lag two is `2`, and the denominator does not.

## Sections 2-4: three statements about the ratio

`RatioBelowThreshold` is `∀ β ≥ 0, lagTwoRatio β < LagTwoBound.lagTwoThreshold`: pointwise in the
coupling, with no constant quantified over.

* `confines_of_ratio_below_threshold` — it implies `ApertureRoute.ConfinesAtAnAperture`, through
  `ConfinesZero.confines_extent_four_of_lag_two_small` at one coupling at a time and
  `LagTwoBound.lag_two_criterion_of_ratio` at `K = lagTwoRatio β`.
* `ratio_below_threshold_of_tail_ratio` — `SpectralBound.TailRatioAtEveryCut` implies it, splitting
  at the cut `LagTwoBound.exists_cut_lag_two_ratio` supplies at half the threshold. No converse is
  proved unconditionally.
* `confines_of_antitone_ratio` — antitonicity of `lagTwoRatio` on `[0, ∞)` implies
  `ConfinesAtAnAperture`, with `lagTwoRatio_at_zero_coupling` as the anchor and
  `LagTwoBound.lagTwoThreshold_pos` as the bar. Nothing here signs that monotonicity:
  `AreaLaw.clay_mean_action_strictAnti` signs `d⟨S⟩/dβ` because at `O = S` the covariance of
  `WilsonAnalytic.wilsonSystem_expect_hasDerivAt` is a variance, whereas `ρ 2` and `ρ 0` are each a
  difference `⟨φ₀ φ_d⟩ - ⟨φ₀⟩⟨φ_d⟩`, so the same identity returns a third cumulant.
  `WilsonAnalytic.cov_bound_extensive`'s constant counts plaquettes.
* `tail_ratio_of_ratio_below_threshold_of_limit` and
  `tail_ratio_iff_ratio_below_threshold_of_limit` — given a limit `L < lagTwoThreshold` at infinity,
  `RatioBelowThreshold` implies `TailRatioAtEveryCut`, so the two are equivalent. The limit is a
  hypothesis and is not proved.

## Section 5: what the extent-four facts decide about the triple

At extent four the half-extent is `m = 2`, so `LogConvex.corrClay_log_convex`'s admissible levels are
`0` and `1` and its only non-diagonal instance is `ρ 1 ^ 2 ≤ ρ 0 * ρ 2`, which bounds `ρ 2` from
below. `lag_three_eq_lag_one` reduces the profile to three numbers.

`TripleFacts r₀ r₁ r₂` collects the coupling-uniform facts: `0 < r₀`, `0 ≤ r₁`, `0 ≤ r₂`,
`r₁ ^ 2 ≤ r₀ * r₂`, and each of the three at most `4`. `triple_wilsonCorrAt` proves the Wilson triple
satisfies it at every `β ≥ 0`. `triple_amgm` shows `2 * r₁ ≤ r₀ + r₂` already follows, so the
`c = (1, -1)` Gram instance is not a further constraint. Then:

* `triple_raise` — raising `r₂` to any value up to `4` preserves every field, so the premise set is
  upward-closed in `r₂`.
* `no_lag_two_bound_from_triple` — for every real `K` there is a conforming triple with
  `K * r₀ < r₂`.
* `no_strict_lag_bound_with_contact` — adding `r₂ ≤ r₀` still admits no factor below one; the
  constant profile is the witness, as in `WeakArm.no_strict_lag_bound_from_shape`.
* `no_bound_at_the_threshold` — the same at `K = lagTwoThreshold`, which
  `LagTwoBound.lagTwoThreshold_lt` places below one.

## Scope

* The refutations in section 5 are against `TripleFacts`, not against the Wilson correlation. They
  say those facts do not decide `ρ 2 ≤ K * ρ 0` in either direction at this extent.
  `WeakArm.corrClay_le_at_zero` and `MomentShape.corrClay_even_antitone` both carry `3 ≤ m` and are
  unavailable here. `LinkGram.wilson_lag_two_le_lag_one` is a positivity that does bound `ρ 2` from
  above; under the link reflection the Gram on `span {F₁, F₂}` is `!![ρ 1, ρ 2; ρ 2, ρ 1]`, whose
  positivity is `ρ 1 ≥ |ρ 2|`.
* `ContactFloor.corrClay_zero_ge` gives an `exp (-128 * β)` floor under `ρ 0`. It is `β`-dependent,
  so it is not a field of a predicate on three numbers; against the uniform bound it gives a ceiling
  `4 * exp (128 * β)` on the ratio.
* `LagTwoBound.exists_cut_lag_two_ratio`'s hypothesis `0 < K` is load-bearing: at `K ≤ 0` the
  statement is false, since `ρ 2 ≥ 0` and `ρ 0 > 0`.
* No measured quantity appears in any statement or proof here. The decimals `0.018623` and
  `0.018625` appear only in doc comments, quoted from `LagTwoBound.lagTwoThreshold_gt` and
  `lagTwoThreshold_lt`; the closed form
  `lagTwoThreshold = ((1 - 3 ^ (-1/4)) / (1 + 3 ^ (-1/4))) ^ 2` is what decides.
-/

namespace MassGap.TailRatio

open MassGap MassGap.ApertureRoute

/-! ## 1. The ratio as a function of the coupling -/

/-- `0 < wilsonCorrAt 3 β 0` at every real `β`, via `StrongArm.wilsonCorrAt_eq_corrClay` and
`PlaqVariance.corrClay_zero_pos`. The contact value is the plaquette-energy variance; no sign
condition on the coupling enters.

DERIVED: `3` is the aperture whose extent `3 + 1` is four, the smallest even extent
`Complete.wilson_reflection_positive_at_even` admits; `0` is the contact lag index. -/
theorem contact_pos (β : ℝ) : 0 < MassGap.wilsonCorrAt 3 β 0 := by
  rw [MassGap.StrongArm.wilsonCorrAt_eq_corrClay]
  exact MassGap.PlaqVariance.corrClay_zero_pos 3 β

/-- `0 ≤ wilsonCorrAt 3 β 2` at every real `β`, via `StrongArm.wilsonCorrAt_eq_corrClay` and
`ReflectionStrong.corrClay_nonneg_even_lag`. Even lags carry no sign condition on the coupling.

DERIVED: `3` is the aperture, `2` its half-extent (`3 + 1 = 2 * 2`) and also the lag index, whose
parity `Even 2` is what the cited theorem reads; `0` is the lower bound asserted. -/
theorem lag_two_nonneg (β : ℝ) : 0 ≤ MassGap.wilsonCorrAt 3 β 2 := by
  rw [MassGap.StrongArm.wilsonCorrAt_eq_corrClay]
  exact MassGap.ReflectionStrong.corrClay_nonneg_even_lag 3 2 (by norm_num) (by norm_num) β
    (by decide)

/-- The lag-two ratio at extent four: `wilsonCorrAt 3 β 2 / wilsonCorrAt 3 β 0`. The denominator
never vanishes (`contact_pos`), so this is total on `ℝ`.

DERIVED: `3` is the aperture, `2` and `0` the two lag indices `LagTwoBound.confines_of_lag_two_ratio`
reads. No constant is introduced. -/
noncomputable def lagTwoRatio (β : ℝ) : ℝ :=
  MassGap.wilsonCorrAt 3 β 2 / MassGap.wilsonCorrAt 3 β 0

/-- The ratio bound and the product bound are the same statement, at every real coupling and every
constant.

DERIVED: `3` is the aperture, `2` and `0` the two lag indices. No constant is introduced. -/
theorem ratio_le_iff (β K : ℝ) :
    lagTwoRatio β ≤ K ↔
      MassGap.wilsonCorrAt 3 β 2 ≤ K * MassGap.wilsonCorrAt 3 β 0 := by
  unfold lagTwoRatio
  exact div_le_iff₀ (contact_pos β)

/-- The strict form of `ratio_le_iff`.

DERIVED: `3` is the aperture, `2` and `0` the two lag indices. No constant is introduced. -/
theorem ratio_lt_iff (β K : ℝ) :
    lagTwoRatio β < K ↔
      MassGap.wilsonCorrAt 3 β 2 < K * MassGap.wilsonCorrAt 3 β 0 := by
  unfold lagTwoRatio
  exact div_lt_iff₀ (contact_pos β)

/-- Clearing the denominator is an identity, not an estimate.

DERIVED: `3` is the aperture, `2` and `0` the two lag indices. No constant is introduced. -/
theorem ratio_mul_contact (β : ℝ) :
    lagTwoRatio β * MassGap.wilsonCorrAt 3 β 0 = MassGap.wilsonCorrAt 3 β 2 := by
  have h : MassGap.wilsonCorrAt 3 β 0 ≠ 0 := ne_of_gt (contact_pos β)
  unfold lagTwoRatio
  field_simp

/-- `0 ≤ lagTwoRatio β` at every real `β`, by `div_nonneg` on `lag_two_nonneg` and `contact_pos`.
Both inputs are unconditional in `β`.

DERIVED: the `0` of `0 ≤ …` is a sign; the aperture and lag indices are `lagTwoRatio`'s own. -/
theorem lagTwoRatio_nonneg (β : ℝ) : 0 ≤ lagTwoRatio β :=
  div_nonneg (lag_two_nonneg β) (contact_pos β).le

/-- `Continuous lagTwoRatio` on all of `ℝ`. Numerator and denominator are continuous by
`ConfinesZero.continuous_wilsonCorrAt`, which descends from
`WilsonAnalytic.wilsonSystem_expect_hasDerivAt` and places no condition on the coupling — its
hypotheses are `N ≠ 0`, measurability of the observable and a uniform bound on it, all discharged
for the plaquette observables. The denominator never vanishes (`contact_pos`).

DERIVED: no numeral occurs in the statement; the aperture and lag indices are inside
`lagTwoRatio`. -/
theorem lagTwoRatio_continuous : Continuous lagTwoRatio := by
  unfold lagTwoRatio
  exact (MassGap.ConfinesZero.continuous_wilsonCorrAt 3 2).div
    (MassGap.ConfinesZero.continuous_wilsonCorrAt 3 0)
    (fun β => ne_of_gt (contact_pos β))

/-- `lagTwoRatio 0 = 0`. At zero coupling the measure is bare product Haar, the two plaquettes at
circle distance two factorise, and the connected correlation vanishes by
`PowerTail.wilsonCorrAt_at_zero_coupling`, admissible because `LagTwoBound.circLag_two` gives circle
distance `2`. The denominator stays strictly positive by `contact_pos`, so the quotient is `0`
rather than indeterminate. This is the anchor `confines_of_antitone_ratio` uses.

DERIVED: the one numeral in the statement is `0`, appearing as the coupling and as the value of the
ratio there. The lag index `2` and the arity `1` that `wilsonCorrAt_at_zero_coupling` requires of the
circle distance are in the proof. -/
theorem lagTwoRatio_at_zero_coupling : lagTwoRatio 0 = 0 := by
  have hnum : MassGap.wilsonCorrAt 3 0 2 = 0 := by
    refine MassGap.PowerTail.wilsonCorrAt_at_zero_coupling 3 2 ?_
    rw [MassGap.LagTwoBound.circLag_two]
    norm_num
  unfold lagTwoRatio
  rw [hnum, zero_div]

/-! ## 2. The debt is pointwise: no constant has to be uniform in the coupling -/

/-- The proposition `∀ β, 0 ≤ β → lagTwoRatio β < LagTwoBound.lagTwoThreshold`. No constant is
quantified over: the inequality is read at one coupling at a time. A `Prop`; nothing in this module
proves it.

DERIVED: `0` is the sign of the coupling; `lagTwoThreshold` is `LagTwoBound`'s derived closed form
`((1 − 3^{−1/4})/(1 + 3^{−1/4}))²`, and no numeral of it is repeated here. -/
def RatioBelowThreshold : Prop :=
  ∀ β : ℝ, 0 ≤ β → lagTwoRatio β < MassGap.LagTwoBound.lagTwoThreshold

/-- `RatioBelowThreshold → ApertureRoute.ConfinesAtAnAperture`. The aperture supplied is
`ConfinesZero.ap4`; at each coupling, `ConfinesZero.confines_extent_four_of_lag_two_small` is applied
to `LagTwoBound.lag_two_criterion_of_ratio` at `K = lagTwoRatio (max β 0)`, which is admissible
because the hypothesis puts that ratio under the threshold and `ratio_mul_contact` reproduces the
numerator exactly.

Scope: `ConfinesAtAnAperture` fixes the aperture existentially and quantifies the coupling inside it,
so no constant uniform in `β` is required.

DERIVED: no numeral occurs in the statement. The clamp `max β 0` in the proof is
`EvenAperture.readEven`'s own, carried through `LagTwoBound.confines_of_lag_two_ratio`. -/
theorem confines_of_ratio_below_threshold (h : RatioBelowThreshold) :
    ApertureRoute.ConfinesAtAnAperture := by
  refine ⟨MassGap.ConfinesZero.ap4, fun β => ?_⟩
  refine MassGap.ConfinesZero.confines_extent_four_of_lag_two_small β ?_
  have hβ : (0 : ℝ) ≤ max β 0 := le_max_right β 0
  have hlt : lagTwoRatio (max β 0) < MassGap.LagTwoBound.lagTwoThreshold := h (max β 0) hβ
  have hle : MassGap.wilsonCorrAt 3 (max β 0) 2
      ≤ lagTwoRatio (max β 0) * MassGap.wilsonCorrAt 3 (max β 0) 0 :=
    le_of_eq (ratio_mul_contact (max β 0)).symm
  exact MassGap.LagTwoBound.lag_two_criterion_of_ratio hlt hle

/-- `SpectralBound.TailRatioAtEveryCut → RatioBelowThreshold`. Below the cut that
`LagTwoBound.exists_cut_lag_two_ratio` supplies at half the threshold, the ratio is bounded by that
half; at and above the cut, by the constant the hypothesis supplies there. Either way it is bounded
by something strictly under the threshold.

Scope: the implication runs one way. `tail_ratio_of_ratio_below_threshold_of_limit` proves a
converse under an additional limit hypothesis, so no separation between the two statements is
established.

DERIVED: no numeral occurs in the statement. The halving of the threshold in the proof is a device
for strictness; any constant strictly inside the threshold would serve. -/
theorem ratio_below_threshold_of_tail_ratio
    (h : MassGap.SpectralBound.TailRatioAtEveryCut) : RatioBelowThreshold := by
  intro β hβ0
  have hT : 0 < MassGap.LagTwoBound.lagTwoThreshold := MassGap.LagTwoBound.lagTwoThreshold_pos
  obtain ⟨b, hb, hlow⟩ :=
    MassGap.LagTwoBound.exists_cut_lag_two_ratio (MassGap.LagTwoBound.lagTwoThreshold / 2)
      (by linarith)
  obtain ⟨K, hK, hhigh⟩ := h b hb
  by_cases hc : β ≤ b
  · have hr := (ratio_le_iff β (MassGap.LagTwoBound.lagTwoThreshold / 2)).mpr (hlow β hβ0 hc)
    linarith
  · have hr := (ratio_le_iff β K).mpr (hhigh β (le_of_lt (not_le.mp hc)))
    linarith

/-! ## 3. A monotonicity in the coupling closes it outright -/

/-- If `lagTwoRatio` is antitone on `[0, ∞)` — `∀ x y, 0 ≤ x → x ≤ y → lagTwoRatio y ≤ lagTwoRatio x` —
then `ApertureRoute.ConfinesAtAnAperture`. The proof evaluates the hypothesis at `x = 0`, rewrites by
`lagTwoRatio_at_zero_coupling`, and compares with `LagTwoBound.lagTwoThreshold_pos`. No value is
supplied and no constant derived.

Scope: the antitonicity is a hypothesis. `AreaLaw.clay_mean_action_strictAnti` signs `d⟨S⟩/dβ`
because at `O = S` the covariance produced by `WilsonAnalytic.wilsonSystem_expect_hasDerivAt` is a
variance; `ρ 2` and `ρ 0` are each `⟨φ₀ φ_d⟩ - ⟨φ₀⟩⟨φ_d⟩`, so the same identity returns a third
cumulant, and `WilsonAnalytic.cov_bound_extensive`'s constant counts plaquettes.

DERIVED: `0` is the zero coupling, which is the anchor, and the sign bound on the domain. -/
theorem confines_of_antitone_ratio
    (h : ∀ x y : ℝ, 0 ≤ x → x ≤ y → lagTwoRatio y ≤ lagTwoRatio x) :
    ApertureRoute.ConfinesAtAnAperture := by
  refine confines_of_ratio_below_threshold (fun β hβ => ?_)
  have hmono := h 0 β le_rfl hβ
  rw [lagTwoRatio_at_zero_coupling] at hmono
  exact lt_of_le_of_lt hmono MassGap.LagTwoBound.lagTwoThreshold_pos

/-! ## 4. Under convergence at infinity the two obligations coincide -/

/-- Given `L < LagTwoBound.lagTwoThreshold`, a limit `lagTwoRatio → L` along `atTop`, and
`RatioBelowThreshold`, the conclusion is `SpectralBound.TailRatioAtEveryCut`. At a cut `b`, the
compact interval `[b, max b B]` carries a maximum of the continuous ratio
(`IsCompact.exists_isMaxOn` with `lagTwoRatio_continuous`), under the threshold by the pointwise
hypothesis; past `B` the limit hypothesis puts the ratio under the midpoint of `L` and the
threshold. The larger of the two constants is uniform on `[b, ∞)` and still strictly inside.

Scope: the limit `L` is a hypothesis and is not established here.

DERIVED: no numeral occurs in the statement. The midpoint `(L + threshold) / 2` in the proof is a
device for a value strictly between two given numbers; the constant produced is read off the
hypotheses. -/
theorem tail_ratio_of_ratio_below_threshold_of_limit
    (L : ℝ) (hL : L < MassGap.LagTwoBound.lagTwoThreshold)
    (hlim : Filter.Tendsto lagTwoRatio Filter.atTop (nhds L))
    (hpt : RatioBelowThreshold) :
    MassGap.SpectralBound.TailRatioAtEveryCut := by
  intro b hb
  have hLK₁ : L < (L + MassGap.LagTwoBound.lagTwoThreshold) / 2 := by linarith
  have hK₁T : (L + MassGap.LagTwoBound.lagTwoThreshold) / 2
      < MassGap.LagTwoBound.lagTwoThreshold := by linarith
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp (hlim.eventually_lt_const hLK₁)
  have hbc : b ≤ max b B := le_max_left b B
  obtain ⟨x₀, hx₀, hmax⟩ :=
    IsCompact.exists_isMaxOn isCompact_Icc (Set.nonempty_Icc.mpr hbc)
      lagTwoRatio_continuous.continuousOn
  have hx₀0 : (0 : ℝ) ≤ x₀ := le_trans hb.le hx₀.1
  have hK₂T : lagTwoRatio x₀ < MassGap.LagTwoBound.lagTwoThreshold := hpt x₀ hx₀0
  refine ⟨max ((L + MassGap.LagTwoBound.lagTwoThreshold) / 2) (lagTwoRatio x₀),
    max_lt hK₁T hK₂T, fun β hβ => ?_⟩
  rw [← ratio_le_iff]
  by_cases hc : β ≤ max b B
  · exact le_trans (isMaxOn_iff.mp hmax β ⟨hβ, hc⟩) (le_max_right _ _)
  · have hBβ : B ≤ β := le_trans (le_max_right b B) (le_of_lt (not_le.mp hc))
    exact le_trans (hB β hBβ).le (le_max_left _ _)

/-- `SpectralBound.TailRatioAtEveryCut ↔ RatioBelowThreshold`, given a limit `L` strictly under the
threshold. Forward is `ratio_below_threshold_of_tail_ratio`, which needs no limit; backward is
`tail_ratio_of_ratio_below_threshold_of_limit`.

Scope: the limit is a hypothesis of the equivalence, not a consequence. Nothing here says a limit is
necessary for the uniformity.

DERIVED: no numeral occurs in the statement. -/
theorem tail_ratio_iff_ratio_below_threshold_of_limit
    (L : ℝ) (hL : L < MassGap.LagTwoBound.lagTwoThreshold)
    (hlim : Filter.Tendsto lagTwoRatio Filter.atTop (nhds L)) :
    MassGap.SpectralBound.TailRatioAtEveryCut ↔ RatioBelowThreshold :=
  ⟨ratio_below_threshold_of_tail_ratio, tail_ratio_of_ratio_below_threshold_of_limit L hL hlim⟩

/-! ## 5. The no-go: reflection positivity at extent four is monotone the WRONG way

At extent four the half-extent is `m = 2`, so `LogConvex.corrClay_log_convex`'s admissible levels are
`0` and `1` and its only non-diagonal instance is `ρ(1)² ≤ ρ(0)·ρ(2)`. Nothing else the tree proves
at this extent without a coupling hypothesis constrains the triple, and the lag `3` is the lag `1`
(`lag_three_eq_lag_one`), so three numbers carry everything.
-/

/-- `wilsonCorrAt 3 β 3 = wilsonCorrAt 3 β 1` at every real `β`, from circle symmetry
`MomentShape.wilsonCorrAt_neg` with `-(1 : Fin 4) = 3` decided. So the extent-four profile is three
numbers rather than four.

DERIVED: `3` is the aperture and, separately, the lag index `−1` reduces to in `Fin 4`; `1` is the
lag it is identified with. Both are index arithmetic, machine-checked. -/
theorem lag_three_eq_lag_one (β : ℝ) :
    MassGap.wilsonCorrAt 3 β 3 = MassGap.wilsonCorrAt 3 β 1 := by
  have h := MassGap.MomentShape.wilsonCorrAt_neg 3 β (1 : Fin 4)
  have hneg : (-(1 : Fin 4)) = (3 : Fin 4) := by decide
  rwa [hneg] at h

/-- `wilsonCorrAt 3 β 1 ^ 2 ≤ wilsonCorrAt 3 β 0 * wilsonCorrAt 3 β 2` at every real `β`.
`LogConvex.corrClay_log_convex_at_extent_four` transcribed through
`StrongArm.wilsonCorrAt_eq_corrClay`, with the `Fin 4` index sums decided.

Scope: this bounds the lag-two value from below, not above.

DERIVED: `3` is the aperture; `0`, `1` and `2` are lag indices; the exponent `2` is the square
log-convexity puts on the middle lag. -/
theorem lag_one_sq_le (β : ℝ) :
    MassGap.wilsonCorrAt 3 β 1 ^ 2
      ≤ MassGap.wilsonCorrAt 3 β 0 * MassGap.wilsonCorrAt 3 β 2 := by
  have hh := MassGap.LogConvex.corrClay_log_convex_at_extent_four β
  have e1 : ((0 : Fin 4) + 1) = (1 : Fin 4) := by decide
  have e0 : ((0 : Fin 4) + 0) = (0 : Fin 4) := by decide
  have e2 : ((1 : Fin 4) + 1) = (2 : Fin 4) := by decide
  rw [e1, e0, e2] at hh
  simp only [MassGap.StrongArm.wilsonCorrAt_eq_corrClay]
  exact hh

/-- The coupling-uniform facts about the extent-four triple, as one `Prop`:
`0 < r₀ ∧ 0 ≤ r₁ ∧ 0 ≤ r₂ ∧ r₁ ^ 2 ≤ r₀ * r₂ ∧ r₀ ≤ 4 ∧ r₁ ≤ 4 ∧ r₂ ≤ 4`.

Conjunct by conjunct, with the theorem that supplies it at the Wilson triple:

* `0 < r₀` — `PlaqVariance.corrClay_zero_pos`, the plaquette-energy variance, good at every real `β`;
* `0 ≤ r₁` — `Complete.wilson_reflection_positive_at_even`, which is where `0 ≤ β` is consumed
  (the odd lag is the one that needs it);
* `0 ≤ r₂` — `ReflectionStrong.corrClay_nonneg_even_lag`, good at every real `β`;
* `r₁² ≤ r₀·r₂` — `LogConvex.corrClay_log_convex_at_extent_four`, good at every real `β`;
* `r₀, r₁, r₂ ≤ 4` — `InfiniteVolume.wilsonCorrAt_abs_le_four`, uniform in the extent.

The lag `3` is absent because it is the lag `1` (`lag_three_eq_lag_one`), and positivity of the total
mass is not a field because it follows from `0 < r₀` and the three nonnegativities.

DERIVED: `4` is `InfiniteVolume.wilsonCorrAt_abs_le_four`'s own constant — two plaquette densities
each in `[0,2]` against a contractive state — and is the only magnitude here; `2` is an exponent and
`0` a sign. -/
def TripleFacts (r₀ r₁ r₂ : ℝ) : Prop :=
  0 < r₀ ∧ 0 ≤ r₁ ∧ 0 ≤ r₂ ∧ r₁ ^ 2 ≤ r₀ * r₂ ∧ r₀ ≤ 4 ∧ r₁ ≤ 4 ∧ r₂ ≤ 4

/-- `TripleFacts (wilsonCorrAt 3 β 0) (wilsonCorrAt 3 β 1) (wilsonCorrAt 3 β 2)` at every `0 ≤ β`.
Each conjunct comes from the theorem listed at `TripleFacts`, with the three upper bounds from
`InfiniteVolume.wilsonCorrAt_abs_le_four` through `le_abs_self`.

DERIVED: `3` is the aperture and, in `wilson_reflection_positive_at_even 3 2`, `2` is its half-extent
(`3 + 1 = 2 * 2`); `0`, `1` and `2` are the three lag indices. Every numeral is an index. -/
theorem triple_wilsonCorrAt {β : ℝ} (hβ : 0 ≤ β) :
    TripleFacts (MassGap.wilsonCorrAt 3 β 0) (MassGap.wilsonCorrAt 3 β 1)
      (MassGap.wilsonCorrAt 3 β 2) := by
  have hrp := MassGap.wilson_reflection_positive_at_even 3 2 (by norm_num) (by norm_num) hβ
  refine ⟨contact_pos β, hrp.1 1, lag_two_nonneg β, lag_one_sq_le β, ?_, ?_, ?_⟩
  · exact le_trans (le_abs_self _) (MassGap.InfiniteVolume.wilsonCorrAt_abs_le_four 3 β 0)
  · exact le_trans (le_abs_self _) (MassGap.InfiniteVolume.wilsonCorrAt_abs_le_four 3 β 1)
  · exact le_trans (le_abs_self _) (MassGap.InfiniteVolume.wilsonCorrAt_abs_le_four 3 β 2)

/-- `TripleFacts r₀ r₁ r₂ → 2 * r₁ ≤ r₀ + r₂`, by arithmetic-geometric mean from the log-convexity
conjunct and the two nonnegativities. The conclusion is the nonnegativity of `cosAvgEven ap4`'s
denominator minus twice its middle term, and equivalently the `c = (1, -1)` instance of positive
semidefiniteness of `!![r₀, r₁; r₁, r₂]`, so `TripleFacts` omits no fourth Gram constraint.

DERIVED: `2` is the coefficient the `(1, −1)` Gram instance produces; no magnitude is chosen. -/
theorem triple_amgm {r₀ r₁ r₂ : ℝ} (h : TripleFacts r₀ r₁ r₂) : 2 * r₁ ≤ r₀ + r₂ := by
  obtain ⟨h0, h1, h2, hlc, _, _, _⟩ := h
  have hs : (0 : ℝ) ≤ r₀ + r₂ := by linarith
  have h4 : (2 * r₁) ^ 2 ≤ (r₀ + r₂) ^ 2 := by nlinarith [sq_nonneg (r₀ - r₂), hlc]
  nlinarith [h4, hs, h1]

/-- `TripleFacts r₀ r₁ r₂ → r₂ ≤ t → t ≤ 4 → TripleFacts r₀ r₁ t`: raising the lag-two value to
anything up to the uniform bound preserves every conjunct. Nonnegativity grows, log-convexity's
right-hand side grows because `r₀ > 0`, and the upper bound is the hypothesis `ht`.

Scope: the predicate is upward-closed in `r₂`, which is the quantity a lag-two ratio bound
constrains from above.

DERIVED: `4` is the same uniform bound as in `TripleFacts`, carried not chosen. -/
theorem triple_raise {r₀ r₁ r₂ t : ℝ} (h : TripleFacts r₀ r₁ r₂) (hle : r₂ ≤ t) (ht : t ≤ 4) :
    TripleFacts r₀ r₁ t := by
  obtain ⟨h0, h1, h2, hlc, hb0, hb1, _⟩ := h
  exact ⟨h0, h1, le_trans h2 hle,
    le_trans hlc (mul_le_mul_of_nonneg_left hle h0.le), hb0, hb1, ht⟩

/-- For every real `K` there is a triple satisfying `TripleFacts` with `K * r₀ < r₂`. The witness
sets the lag-two value at the uniform bound `4` and the other two at `1 / (|K| + 1)`, which is
positive, at most one, and small enough that `K` times it stays under `4`.

Scope. This refutes every constant, not merely those below the threshold. It is a statement about
`TripleFacts`, not about the Wilson correlation. At extent four the premise set does not even give
the factor one, because `WeakArm.corrClay_le_at_zero` and `MomentShape.corrClay_even_antitone` both
carry `3 ≤ m`; `WeakArm.no_strict_lag_bound_from_shape` is the corresponding statement at extent six
and above, against `MomentShape.Shape`.

DERIVED: no numeral occurs in the statement, which quantifies over `K` and asserts an existential.

CHOSEN: the witness scale `1 / (|K| + 1)` in the proof; any positive number below `4 / (|K| + 1)`
serves. The `4` it is measured against is `TripleFacts`' own uniform bound. -/
theorem no_lag_two_bound_from_triple (K : ℝ) :
    ∃ r₀ r₁ r₂ : ℝ, TripleFacts r₀ r₁ r₂ ∧ K * r₀ < r₂ := by
  have hA : (0 : ℝ) ≤ |K| := abs_nonneg K
  have hden : (0 : ℝ) < |K| + 1 := by linarith
  set ε : ℝ := 1 / (|K| + 1) with hεdef
  have hε : (0 : ℝ) < ε := by rw [hεdef]; exact div_pos one_pos hden
  have hε1 : ε ≤ 1 := by rw [hεdef, div_le_one hden]; linarith
  have hKε : K * ε < 4 := by
    have h1 : K * ε ≤ |K| * ε := mul_le_mul_of_nonneg_right (le_abs_self K) hε.le
    have h2 : |K| * ε = |K| / (|K| + 1) := by rw [hεdef]; ring
    have h3 : |K| / (|K| + 1) < 1 := by rw [div_lt_one hden]; linarith
    linarith
  refine ⟨ε, ε, 4, ⟨hε, hε.le, by norm_num, ?_, by linarith, by linarith, le_rfl⟩, hKε⟩
  nlinarith [hε, hε1]

/-- For every `K < 1` there is a triple satisfying `TripleFacts`, satisfying the contact bound
`r₂ ≤ r₀`, and with `K * r₀ < r₂`. The witness is the constant profile `(1, 1, 1)`, as in
`WeakArm.no_strict_lag_bound_from_shape`.

Scope: adding the contact bound to the premise set still admits no factor strictly below one. The
threshold `LagTwoBound.lagTwoThreshold` lies below `0.018625` by `LagTwoBound.lagTwoThreshold_lt`,
so it is among the factors this refutes.

DERIVED: `1` is the constant profile's value, a scale the statement is invariant under, and the
factor the no-go is against. -/
theorem no_strict_lag_bound_with_contact (K : ℝ) (hK : K < 1) :
    ∃ r₀ r₁ r₂ : ℝ, TripleFacts r₀ r₁ r₂ ∧ r₂ ≤ r₀ ∧ K * r₀ < r₂ :=
  ⟨1, 1, 1, ⟨one_pos, zero_le_one, zero_le_one, by norm_num, by norm_num, by norm_num,
    by norm_num⟩, le_rfl, by linarith⟩

/-- There is a triple satisfying `TripleFacts` and the contact bound `r₂ ≤ r₀` with
`LagTwoBound.lagTwoThreshold * r₀ < r₂`. `no_strict_lag_bound_with_contact` at
`K = lagTwoThreshold`, admissible because `LagTwoBound.lagTwoThreshold_lt` places the threshold
below `0.018625` and hence below one.

DERIVED: no numeral occurs in the statement; the threshold is a named constant and the bracketing
rational `0.018625` is `LagTwoBound.lagTwoThreshold_lt`'s, used in the proof only to show the
threshold is under one. -/
theorem no_bound_at_the_threshold :
    ∃ r₀ r₁ r₂ : ℝ, TripleFacts r₀ r₁ r₂ ∧ r₂ ≤ r₀ ∧
      MassGap.LagTwoBound.lagTwoThreshold * r₀ < r₂ := by
  refine no_strict_lag_bound_with_contact MassGap.LagTwoBound.lagTwoThreshold ?_
  have h := MassGap.LagTwoBound.lagTwoThreshold_lt
  linarith

section Audit
#print axioms contact_pos
#print axioms lag_two_nonneg
#print axioms lagTwoRatio
#print axioms ratio_le_iff
#print axioms ratio_lt_iff
#print axioms ratio_mul_contact
#print axioms lagTwoRatio_nonneg
#print axioms lagTwoRatio_continuous
#print axioms lagTwoRatio_at_zero_coupling
#print axioms RatioBelowThreshold
#print axioms confines_of_ratio_below_threshold
#print axioms ratio_below_threshold_of_tail_ratio
#print axioms confines_of_antitone_ratio
#print axioms tail_ratio_of_ratio_below_threshold_of_limit
#print axioms tail_ratio_iff_ratio_below_threshold_of_limit
#print axioms lag_three_eq_lag_one
#print axioms lag_one_sq_le
#print axioms TripleFacts
#print axioms triple_wilsonCorrAt
#print axioms triple_amgm
#print axioms triple_raise
#print axioms no_lag_two_bound_from_triple
#print axioms no_strict_lag_bound_with_contact
#print axioms no_bound_at_the_threshold
end Audit

end MassGap.TailRatio
