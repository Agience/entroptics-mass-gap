import Mathlib
import MassGap.SpectralBound
import MassGap.InfiniteVolume
import MassGap.WeakArm

/-!
# MassGap.TailRatio — the lag-two ratio at extent four: what the tail actually owes

`LagTwoBound.confines_of_lag_two_ratio` reduces Clay row B5 at the smallest even aperture to
`ρ(2) ≤ K·ρ(0)` with `K < LagTwoBound.lagTwoThreshold`, where `ρ(d) = wilsonCorrAt 3 β d`.
`LagTwoBound.exists_cut_lag_two_ratio` proves that on a derived `[0, b]` at any POSITIVE constant
(its `hK : 0 < K` is load-bearing — at `K <= 0` the statement is false, since `ρ(2) ≥ 0 < ρ(0)`), and
`SpectralBound.TailRatioAtEveryCut` names the remainder: one constant strictly below the threshold,
uniform on `[b, ∞)`, at every cut. This file puts the ratio itself in a variable and settles three
things about that remainder.

## 1. The remainder does not need a uniform constant — the debt is POINTWISE

`ApertureRoute.ConfinesAtAnAperture` is `∃ a : EvenAp, ∀ β, 3^{−1/4} < cosAvgEven a β`. The aperture
is existential, the coupling is universal INSIDE it, and the engine
`ConfinesZero.confines_extent_four_of_lag_two_small` consumes one coupling at a time. So no constant
has to be uniform in `β` at all. `confines_of_ratio_below_threshold` is that bridge in the ratio
variable:

    (∀ β ≥ 0, lagTwoRatio β < lagTwoThreshold)  →  ConfinesAtAnAperture

and `ratio_below_threshold_of_tail_ratio` proves `TailRatioAtEveryCut → RatioBelowThreshold`, so the
named remainder IMPLIES what B5 at this extent needs. `SpectralBound`'s own docstring says a weaker
request may also close it; this is a request of that shape — the `∃K` is gone, and the constant the
proof uses varies with the coupling. NO SEPARATION IS PROVED: no converse is established, and §4
below proves a CONDITIONAL converse, so the two are not known to differ on the actual correlation.
What is established is the implication and the removal of the quantifier, not a strict containment.

The threshold in `RatioBelowThreshold` is the one `LagTwoBound.lag_two_criterion_of_ratio` reads, and
`ConfinesZero`'s identity `((1−c)ρ₀ − (1+c)ρ₂)² − 4c²ρ₀ρ₂ = ((1−c)²ρ₀ − (1+c)²ρ₂)(ρ₀ − ρ₂)` has the
first of its two factors vanish there — the second vanishes at `ρ₀ = ρ₂`, which is a different
boundary and not the one the criterion is read against.

Nothing here proves the pointwise statement. What it does is delete the uniformity from the
obligation, which is what the cluster expansion could not supply
(`SpectralBound.expansion_domain_bounded`) and what a compactness argument cannot manufacture.

## 2. A monotonicity in `β` WOULD close it outright, and the anchor value is already proved

`lagTwoRatio_at_zero_coupling` is `lagTwoRatio 0 = 0`: the numerator vanishes at zero coupling
(`PowerTail.wilsonCorrAt_at_zero_coupling`, since `circLag 2 = 2 ≥ 1` at this extent) and the
denominator does not (`PlaqVariance.corrClay_zero_pos`). So the whole of B5 at extent four follows
from ONE monotonicity statement, with no value to supply and no constant to derive:

    (∀ x y, 0 ≤ x → x ≤ y → lagTwoRatio y ≤ lagTwoRatio x)  →  ConfinesAtAnAperture

That is `confines_of_antitone_ratio`. It answers the question `AreaLaw.clay_mean_action_strictAnti`
raises — whether the covariance identity `d⟨O⟩/dβ = −Cov_β(O,S)`
(`WilsonAnalytic.wilsonSystem_expect_hasDerivAt`) signs anything here — by saying exactly what would
have to be signed. It does NOT sign it, and the reason is structural rather than an absence of
effort: `clay_mean_action_strictAnti` works because at `O = S` the covariance IS a variance. Neither
`ρ(2)` nor `ρ(0)` is a single expectation — each is `⟨φ₀φ_d⟩ − ⟨φ₀⟩⟨φ_d⟩`, so its derivative is a
third cumulant of the Gibbs state, and no theorem in this tree signs a third cumulant. The
assumption-free Lipschitz route is separately closed by `WilsonAnalytic.cov_bound_extensive`, whose
constant counts plaquettes.

## 3. Reflection positivity at extent four cannot bound the ratio ABOVE — proved

This is the negative result, and it is against the route that looked most promising. At extent four
the half-extent is `m = 2`, so `LogConvex.corrClay_log_convex`'s admissible levels are `0` and `1`
and the only non-diagonal instance it has is

    ρ(1)² ≤ ρ(0)·ρ(2),

which bounds `ρ(2)` FROM BELOW. The same is true of the Gram matrix
`ReflectionStrong.wilson_expect_gram_nonneg` produces over the slab algebra: on the three numbers
`(ρ(0), ρ(1), ρ(2))` its content is the positive semidefiniteness of `!![ρ(0), ρ(1); ρ(1), ρ(2)]`,
and a PSD condition is monotone INCREASING in its lower-right entry.

`TripleFacts` collects the tree's β-FREE facts about the triple — those whose only hypothesis is
`0 ≤ β` and whose content carries no `β`-dependent constant — each field cited to its theorem. (The
tree also proves `ContactFloor.corrClay_zero_ge`, an `e^{−128β}` floor under `ρ(0)`; it is
β-dependent by construction and so cannot be a field of a predicate on three numbers. Read against
the uniform bound it gives a ceiling `4e^{128β}/D` on the ratio, which is not a bound of the shape B5
asks for.) and `triple_wilsonCorrAt` proves the Wilson correlation satisfies it.
Then:

* `triple_raise` — raising `ρ(2)` to anything up to the uniform bound `4` PRESERVES every field. The
  premise set is upward-closed in the very quantity B5 needs bounded above.
* `no_lag_two_bound_from_triple` — consequently, for EVERY real `K` there is a conforming triple with
  `K·ρ(0) < ρ(2)`. Not "no constant below the threshold": no constant at all.
* `no_strict_lag_bound_with_contact` — and adding the contact bound `ρ(2) ≤ ρ(0)` — which IS now
  available at this extent, since `SlabQuadratic.wilsonSpectral` gives `ρ(2) ≤ ρ(1) ≤ ρ(0)` at every `β ≥ 0`
  through `SpectralFour.fourRepresentable_le`, where `WeakArm.corrClay_le_at_zero` could not (`3 ≤ m`)
  — still admits no factor below one, so having it changes nothing here. The constant profile is the witness, as in
  `WeakArm.no_strict_lag_bound_from_shape`.

`triple_amgm` records that the remaining shape fact at this extent, `2ρ(1) ≤ ρ(0) + ρ(2)` — the
positivity of `cosAvgEven ap4`'s denominator minus twice its middle term — is already a consequence
of log-convexity, so it is not a fourth constraint being left out.

THE SCOPE OF THE NO-GO IS THE PREMISE SET, exactly as `WeakArm.no_strict_lag_bound_from_shape`'s is
`MomentShape.Shape` and `ShapeNoGo`'s is its own. Nothing here says `ρ(2) ≤ K·ρ(0)` is false of the
Wilson correlation; what is proved is that reflection positivity, log-convexity, the uniform bound
and contact positivity do not decide it, in either direction, at this extent. A route to the tail
must consume something those four do not contain. It need not avoid reflection positivity —
`LinkGram.wilson_lag_two_le_lag_one` IS such a positivity and it does bound `ρ(2)` from above —
but it must reach past the extent-four Gram, which cannot give a factor under one: under the link
reflection the Gram on `span{F₁, F₂}` is `[[ρ(1), ρ(2)], [ρ(2), ρ(1)]]`, and its positivity is exactly
`ρ(1) ≥ |ρ(2)|`.

## Where the tail stands after this file

The open statement is `RatioBelowThreshold`: a continuous function of the coupling, equal to `0` at
`β = 0` (`lagTwoRatio_at_zero_coupling`), nonnegative everywhere
(`lagTwoRatio_nonneg`), must stay strictly under `lagTwoThreshold` — bracketed between `0.018623`
and `0.018625` by `LagTwoBound.lagTwoThreshold_gt` and `lagTwoThreshold_lt`, and decided by the
closed form rather than by either rational — on `[0, ∞)`. It is
implied by `TailRatioAtEveryCut`, it implies B5 at extent four, and GIVEN a limit at infinity that is
itself strictly under the threshold the two are equivalent
(`tail_ratio_iff_ratio_below_threshold_of_limit`) — which is the rigorous form of
the large-`β` argument: a limit strictly below the threshold plus pointwise strictness gives the
uniform tail back, by compactness on the middle.

No measured quantity appears anywhere in this file, in a statement or in a proof. No constant is
fitted. The numerals are: lag indices (`0`, `1`, `2`, `3`), the aperture `3` and its half-extent `2`,
the uniform correlation bound `4` (`InfiniteVolume.wilsonCorrAt_abs_le_four`), and four arithmetic
devices, each noted at its own declaration — the halvings in `lagTwoThreshold / 2`
(`ratio_below_threshold_of_tail_ratio`) and `(L + threshold)/2`
(`tail_ratio_of_ratio_below_threshold_of_limit`), the witness scale `1/(|K| + 1)`
(`no_lag_two_bound_from_triple`, marked CHOSEN) and the constant profile's `1`
(`no_strict_lag_bound_with_contact`). The only decimals anywhere are `0.018623` and `0.018625` in
doc comments, quoted from `LagTwoBound.lagTwoThreshold_gt` and `lagTwoThreshold_lt`; neither appears
in a statement or a proof, and neither decides anything — the closed form does.

Foundational footprint only (`#print axioms` on every declaration, in the audit section).
The module is in the library root's import list, so repository-wide sweeps cover it.
Build: `python code/lean_build.py build MassGap.TailRatio`.
-/

namespace MassGap.TailRatio

open MassGap MassGap.ApertureRoute

/-! ## 1. The ratio as a function of the coupling -/

/-- **The contact value is strictly positive at every real coupling.** `wilsonCorrAt 3 β 0` is the
plaquette-energy variance (`PlaqVariance.corrClay_zero_pos`); nothing about the sign of the coupling
enters.

DERIVED: `3` is the aperture whose extent `3 + 1` is four, the smallest even extent
`Complete.wilson_reflection_positive_at_even` admits; `0` is the contact lag index. -/
theorem contact_pos (β : ℝ) : 0 < MassGap.wilsonCorrAt 3 β 0 := by
  rw [MassGap.StrongArm.wilsonCorrAt_eq_corrClay]
  exact MassGap.PlaqVariance.corrClay_zero_pos 3 β

/-- **The lag-two value is nonnegative at every real coupling.** The even lags' reflection
positivity carries no sign condition (`ReflectionStrong.corrClay_nonneg_even_lag`).

DERIVED: `3` is the aperture, `2` its half (`3 + 1 = 2 * 2`) and also the lag index; the parity
`Even 2` is the hypothesis that theorem reads. -/
theorem lag_two_nonneg (β : ℝ) : 0 ≤ MassGap.wilsonCorrAt 3 β 2 := by
  rw [MassGap.StrongArm.wilsonCorrAt_eq_corrClay]
  exact MassGap.ReflectionStrong.corrClay_nonneg_even_lag 3 2 (by norm_num) (by norm_num) β
    (by decide)

/-- **The lag-two ratio at extent four** — the single number Clay row B5 at the smallest even
aperture is a statement about. The denominator never vanishes (`contact_pos`), so this is total on
all of `ℝ`.

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

/-- **The ratio is nonnegative at every real coupling.** Both halves are unconditional in `β`.

DERIVED: the `0` of `0 ≤ …` is a sign; the aperture and lag indices are `lagTwoRatio`'s own. -/
theorem lagTwoRatio_nonneg (β : ℝ) : 0 ≤ lagTwoRatio β :=
  div_nonneg (lag_two_nonneg β) (contact_pos β).le

/-- **The ratio is continuous on all of `ℝ`.** `ConfinesZero.continuous_wilsonCorrAt` is the Wilson
Gibbs expectation's own continuity in the coupling, and it carries no hypothesis at all. It descends
from `WilsonAnalytic.wilsonSystem_expect_hasDerivAt`, which places NO condition on the coupling — its
hypotheses are `N ≠ 0`, measurability of the observable and a uniform bound on it, all discharged for
the plaquette observables. The denominator never vanishes (`contact_pos`).

DERIVED: `3` is the aperture, `2` and `0` the two lag indices. No constant is introduced. -/
theorem lagTwoRatio_continuous : Continuous lagTwoRatio := by
  unfold lagTwoRatio
  exact (MassGap.ConfinesZero.continuous_wilsonCorrAt 3 2).div
    (MassGap.ConfinesZero.continuous_wilsonCorrAt 3 0)
    (fun β => ne_of_gt (contact_pos β))

/-- **THE RATIO IS EXACTLY ZERO AT ZERO COUPLING.**

At `β = 0` the measure is bare product Haar, the two plaquettes at circle distance two factorise, and
the connected correlation vanishes (`PowerTail.wilsonCorrAt_at_zero_coupling`, admissible because
`LagTwoBound.circLag_two` says the circle distance is `2`). The denominator stays strictly positive
(`PlaqVariance.corrClay_zero_pos_at_zero_coupling`, through `contact_pos`), so the quotient is `0`
rather than indeterminate.

This is the anchor that makes `confines_of_antitone_ratio` free of any supplied value.

DERIVED: `0` is the zero coupling and the contact lag; `2` the lag index and its circle distance;
`1` is the arity `wilsonCorrAt_at_zero_coupling` asks the circle distance to reach. -/
theorem lagTwoRatio_at_zero_coupling : lagTwoRatio 0 = 0 := by
  have hnum : MassGap.wilsonCorrAt 3 0 2 = 0 := by
    refine MassGap.PowerTail.wilsonCorrAt_at_zero_coupling 3 2 ?_
    rw [MassGap.LagTwoBound.circLag_two]
    norm_num
  unfold lagTwoRatio
  rw [hnum, zero_div]

/-! ## 2. The debt is pointwise: no constant has to be uniform in the coupling -/

/-- **THE OPEN STATEMENT, IN THE RATIO VARIABLE.**

A continuous, nonnegative function of the coupling, equal to `0` at `β = 0`, staying strictly under
the derived `LagTwoBound.lagTwoThreshold` on the nonnegative half-line. No constant is quantified
over: the inequality is read at one coupling at a time.

DERIVED: `0` is the sign of the coupling; `lagTwoThreshold` is `LagTwoBound`'s derived closed form
`((1 − 3^{−1/4})/(1 + 3^{−1/4}))²`, and no numeral of it is repeated here. -/
def RatioBelowThreshold : Prop :=
  ∀ β : ℝ, 0 ≤ β → lagTwoRatio β < MassGap.LagTwoBound.lagTwoThreshold

/-- **AND IT IS SUFFICIENT FOR B5 AT THE SMALLEST EVEN APERTURE.**

`ApertureRoute.ConfinesAtAnAperture` fixes the aperture existentially and quantifies the coupling
inside, and `ConfinesZero.confines_extent_four_of_lag_two_small` consumes one coupling at a time. So
the hypothesis is discharged pointwise, through `LagTwoBound.lag_two_criterion_of_ratio` at the
constant `K = lagTwoRatio β`, which is admissible precisely because the ratio at that coupling is
under the threshold and reproduces the numerator exactly (`ratio_mul_contact`).

THIS IS WEAKER THAN `SpectralBound.TailRatioAtEveryCut`, AND THAT IS THE POINT — see
`ratio_below_threshold_of_tail_ratio`. The uniform constant the tail obligation asks for is not
something the criterion needs.

DERIVED: the clamp `max β 0` is `EvenAperture.readEven`'s own, carried through
`LagTwoBound.confines_of_lag_two_ratio`'s proof; `0` is the sign it clamps at. -/
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

/-- **THE NAMED TAIL OBLIGATION IMPLIES IT.**

Below the cut `LagTwoBound.exists_cut_lag_two_ratio` supplies at half the threshold; at and above the
cut the hypothesis at that same cut. Either way the ratio at the coupling in hand is bounded by a
constant strictly under the threshold, hence is itself strictly under it.

So `RatioBelowThreshold` sits between `LagTwoBound.confines_below_derived_cut` and
`SpectralBound.TailRatioAtEveryCut`: it is implied by the latter and implies B5 at this extent. NO
CONVERSE IS PROVED and no separation is claimed — `tail_ratio_of_ratio_below_threshold_of_limit`
proves a converse under one further hypothesis, so the two may well coincide on the actual
correlation. What the implication buys is the deletion of the `∃K`, not a strictly smaller request.

DERIVED: the `2` is `LagTwoBound.confines_below_derived_cut`'s own device for strictness — any
constant strictly inside the threshold serves — and `0` is a sign. -/
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

/-- **IF THE RATIO NEVER INCREASES WITH THE COUPLING, B5 AT EXTENT FOUR FOLLOWS.**

No value has to be supplied and no constant derived: the anchor is `lagTwoRatio 0 = 0`
(`lagTwoRatio_at_zero_coupling`), which is a theorem, and the threshold is strictly positive
(`LagTwoBound.lagTwoThreshold_pos`).

THIS IS WHAT A DERIVATIVE ARGUMENT WOULD HAVE TO SIGN, stated so that it can be checked against what
the tree has. `AreaLaw.clay_mean_action_strictAnti` signs `d⟨S⟩/dβ` because at `O = S` the covariance
`WilsonAnalytic.wilsonSystem_expect_hasDerivAt` produces is a variance. `ρ(2)` and `ρ(0)` are each a
difference `⟨φ₀φ_d⟩ − ⟨φ₀⟩⟨φ_d⟩` of three expectations, so the same identity returns a third cumulant
of the Gibbs state, which nothing in this tree signs; and the assumption-free Lipschitz route is
closed separately by `WilsonAnalytic.cov_bound_extensive`, whose constant is the plaquette count.
This theorem does not close that gap — it names it exactly.

DERIVED: `0` is the zero coupling, which is the anchor, and the sign bound on the domain. -/
theorem confines_of_antitone_ratio
    (h : ∀ x y : ℝ, 0 ≤ x → x ≤ y → lagTwoRatio y ≤ lagTwoRatio x) :
    ApertureRoute.ConfinesAtAnAperture := by
  refine confines_of_ratio_below_threshold (fun β hβ => ?_)
  have hmono := h 0 β le_rfl hβ
  rw [lagTwoRatio_at_zero_coupling] at hmono
  exact lt_of_le_of_lt hmono MassGap.LagTwoBound.lagTwoThreshold_pos

/-! ## 4. Under convergence at infinity the two obligations coincide -/

/-- **POINTWISE PLUS A LIMIT STRICTLY UNDER THE THRESHOLD GIVES THE UNIFORM TAIL BACK.**

The compact middle `[b, max b B]` carries a maximum of the continuous ratio
(`IsCompact.exists_isMaxOn` on `lagTwoRatio_continuous`), which is under the threshold by the
pointwise hypothesis; past `B` the limit hypothesis puts the ratio under the midpoint between the
limit and the threshold. The larger of the two constants is uniform on `[b, ∞)` and still strictly
inside.

This is the rigorous form of a large-coupling argument that produces a LIMITING VALUE for the ratio:
a limit alone does not close B5, and a limit together with pointwise strictness recovers the full
named obligation. The limit is a hypothesis here and is not proved.

DERIVED: `2` is the midpoint device `(L + threshold)/2`, chosen only to be strictly between two given
numbers, and `0` is a sign. Nothing is fitted: the constant produced is read off the hypotheses. -/
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

/-- **THE TWO OBLIGATIONS ARE THE SAME STATEMENT ONCE THE RATIO CONVERGES.**

Forward is `ratio_below_threshold_of_tail_ratio`, which needs no limit; backward is
`tail_ratio_of_ratio_below_threshold_of_limit`. So the uniformity `SpectralBound.TailRatioAtEveryCut`
asks for is FREE WHENEVER the ratio has a limit strictly under the threshold. Only that sufficiency
is proved: nothing here says a limit is NECESSARY for the uniformity, and no such converse is
claimed. Absent a limit, `RatioBelowThreshold` is the request with no constant in it, and the one to
aim at. -/
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

/-- **THE LAG THREE IS THE LAG ONE**, by circle symmetry (`MomentShape.wilsonCorrAt_neg`), so the
extent-four profile is three numbers rather than four.

DERIVED: `3` is the aperture and, separately, the lag index `−1` reduces to in `Fin 4`; `1` is the
lag it is identified with. Both are index arithmetic, machine-checked. -/
theorem lag_three_eq_lag_one (β : ℝ) :
    MassGap.wilsonCorrAt 3 β 3 = MassGap.wilsonCorrAt 3 β 1 := by
  have h := MassGap.MomentShape.wilsonCorrAt_neg 3 β (1 : Fin 4)
  have hneg : (-(1 : Fin 4)) = (3 : Fin 4) := by decide
  rwa [hneg] at h

/-- **LOG-CONVEXITY AT EXTENT FOUR, ON THE READ CORRELATION.**
`LogConvex.corrClay_log_convex_at_extent_four` transcribed through
`StrongArm.wilsonCorrAt_eq_corrClay`, with the `Fin 4` sums evaluated.

DERIVED: `0`, `1` and `2` are lag indices; `3` is the aperture. -/
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

/-- **WHAT THE TREE PROVES ABOUT THE EXTENT-FOUR TRIPLE, WITH NO HYPOTHESIS BUT THE SIGN OF THE
COUPLING.**

Field by field, with the theorem that supplies it:

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

/-- **THE WILSON CORRELATION'S OWN TRIPLE SATISFIES IT**, at every nonnegative coupling — so the
no-gos below are against a premise set that is actually available and not a weakened caricature of
one.

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

/-- **THE REMAINING SHAPE FACT AT THIS EXTENT IS ALREADY A CONSEQUENCE.**

`2r₁ ≤ r₀ + r₂` — equivalently the nonnegativity of `cosAvgEven ap4`'s denominator minus twice its
middle term, and equivalently the `c = (1, −1)` instance of positive semidefiniteness of
`!![r₀, r₁; r₁, r₂]` — follows from log-convexity and the two nonnegativities by arithmetic-geometric
mean. So `TripleFacts` is not omitting a fourth constraint that the Gram matrix would supply.

DERIVED: `2` is the coefficient the `(1, −1)` Gram instance produces; no magnitude is chosen. -/
theorem triple_amgm {r₀ r₁ r₂ : ℝ} (h : TripleFacts r₀ r₁ r₂) : 2 * r₁ ≤ r₀ + r₂ := by
  obtain ⟨h0, h1, h2, hlc, _, _, _⟩ := h
  have hs : (0 : ℝ) ≤ r₀ + r₂ := by linarith
  have h4 : (2 * r₁) ^ 2 ≤ (r₀ + r₂) ^ 2 := by nlinarith [sq_nonneg (r₀ - r₂), hlc]
  nlinarith [h4, hs, h1]

/-- **EVERY FIELD IS MONOTONE THE WRONG WAY IN THE LAG-TWO VALUE.**

Raising `r₂` to anything between it and the uniform bound `4` preserves nonnegativity (it grows),
log-convexity (the right-hand side grows, since `r₀ > 0`) and the bound (by hypothesis), and touches
nothing else. So the premise set is UPWARD-CLOSED in the very quantity B5 needs bounded above.

That is the structural reason reflection positivity cannot supply the tail at this extent: every
positivity of the reflection form is a statement that some quadratic form is nonnegative, and `r₂`
enters those forms as a diagonal entry with a nonnegative coefficient.

DERIVED: `4` is the same uniform bound as in `TripleFacts`, carried not chosen. -/
theorem triple_raise {r₀ r₁ r₂ t : ℝ} (h : TripleFacts r₀ r₁ r₂) (hle : r₂ ≤ t) (ht : t ≤ 4) :
    TripleFacts r₀ r₁ t := by
  obtain ⟨h0, h1, h2, hlc, hb0, hb1, _⟩ := h
  exact ⟨h0, h1, le_trans h2 hle,
    le_trans hlc (mul_le_mul_of_nonneg_left hle h0.le), hb0, hb1, ht⟩

/-- **NO CONSTANT AT ALL FOLLOWS FROM THE EXTENT-FOUR FACTS — NOT MERELY NONE BELOW THE THRESHOLD.**

For EVERY real `K` there is a triple satisfying `TripleFacts` with `K·r₀ < r₂`. The witness sets the
lag-two value at the uniform bound and the other two at `1/(|K| + 1)`, which is positive, at most
one, and small enough that `K` times it cannot reach the bound.

Compare `WeakArm.no_strict_lag_bound_from_shape`, which refutes every factor below ONE from
`MomentShape.Shape` at extent six and above. Here, at extent four, the premise set does not even
deliver the factor one, because `WeakArm.corrClay_le_at_zero` and
`MomentShape.corrClay_even_antitone` both carry `3 ≤ m` and neither is available — a scope limit
`ConfinesZero.confines_extent_four_of_lag_two_small` also records.

WHAT THIS DOES NOT SAY: nothing here asserts `ρ(2) ≤ K·ρ(0)` is false of the Wilson correlation. It
says the four facts above do not decide it. A route to `RatioBelowThreshold` must consume something
outside that set.

CHOSEN: `1/(|K| + 1)` is a witness scale, not a constant of the theory — any positive number under
`4/(|K| + 1)` serves, and the statement quantifies over `K` so no value is pinned. `4` is the tree's
uniform correlation bound. -/
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

/-- **AND ADDING THE CONTACT BOUND STILL ADMITS NO FACTOR BELOW ONE.**

`ρ(2) ≤ ρ(0)` is not available at extent four, but suppose it were. The constant profile satisfies
`TripleFacts`, satisfies that contact bound as well, and violates `r₂ ≤ K·r₀` for every `K < 1` — so
even the strengthened premise set is optimal at exactly the factor one, and the distance from there
down to `lagTwoThreshold` — which `LagTwoBound.lagTwoThreshold_lt` puts below `0.018625` — is not a
gap any positivity argument at this extent narrows.

The witness is `WeakArm.no_strict_lag_bound_from_shape`'s, at this extent and against this premise
set.

DERIVED: `1` is the constant profile's value, a scale the statement is invariant under, and the
factor the no-go is against. -/
theorem no_strict_lag_bound_with_contact (K : ℝ) (hK : K < 1) :
    ∃ r₀ r₁ r₂ : ℝ, TripleFacts r₀ r₁ r₂ ∧ r₂ ≤ r₀ ∧ K * r₀ < r₂ :=
  ⟨1, 1, 1, ⟨one_pos, zero_le_one, zero_le_one, by norm_num, by norm_num, by norm_num,
    by norm_num⟩, le_rfl, by linarith⟩

/-- **NON-VACUITY OF THE NO-GO AT THE ACTUAL TARGET.** The threshold B5 asks for is under one
(`LagTwoBound.lagTwoThreshold_lt` brackets it below `0.018625`), so
`no_strict_lag_bound_with_contact` applies at it: there is a conforming triple that fails the
criterion, at the very constant the criterion names.

DERIVED: `0.018625` is `LagTwoBound.lagTwoThreshold_lt`'s bracketing rational, quoted not recomputed,
and it decides nothing here beyond being under one. -/
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
