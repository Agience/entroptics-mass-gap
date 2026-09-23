import MassGap.ConfinesZero
import MassGap.ContactFloor

/-!
# MassGap.LagTwoBound — the lag-two ratio form of the extent-four confinement criterion

`ConfinesZero.confines_extent_four_of_lag_two_small` takes the criterion

    (1 + c)² ρ(2)  <  (1 − c)² ρ(0),        c = 3^{−1/4},  ρ = wilsonCorrAt 3 (max β 0)

to `ApertureRoute.ConfinesAtAnAperture` at `ConfinesZero.ap4`. This file restates that criterion as a
bound on the ratio `ρ(2)/ρ(0)`, locates the threshold on the real line, and proves the ratio bound on
a coupling interval.

## 1. The threshold

`floor_pow_four` is `(3 ^ (-1/4)) ^ 4 = 1/3` by `rpow` algebra. `floor_sq_bounds` and `floor_bounds`
bracket `3 ^ (-1/4)` and its square between explicit rationals. `lagTwoThreshold` is the closed form
`((1 - 3 ^ (-1/4)) / (1 + 3 ^ (-1/4))) ^ 2`, positive by `lagTwoThreshold_pos` and bracketed between
`0.018623` and `0.018625` by `lagTwoThreshold_gt` and `lagTwoThreshold_lt`.

## 2. The ratio form

`lag_two_criterion_of_ratio`: at any real `β`, a bound `ρ(2) ≤ K ρ(0)` with `K < lagTwoThreshold`
gives the strict criterion. The strictness comes from `PlaqVariance.corrClay_zero_pos`, which makes
`ρ(0)` strictly positive at every real coupling, so the ratio hypothesis may be non-strict.
`confines_of_lag_two_ratio` quantifies that over `β ≥ 0` and concludes
`ApertureRoute.ConfinesAtAnAperture`; the nonnegative half-line suffices because `readEven` clamps
at `max β 0`.

## 3. Size of the contact-relative constant

`circLag_two` evaluates `Moment.circLag (2 : Fin (3 + 1))` to `2` by `decide`. `le_coreConst` puts
`128 ≤ coreConst K β` below the rate-one threshold, and `contact_relative_constant_too_large`
combines it with `lagTwoThreshold_lt` to give `16 * lagTwoThreshold < coreConst (16 * 4) b`. That is
a comparison of two named quantities; it is not a statement about the existential in
`ContactFloor.contact_relative_unconditional`.

## 4. The ratio bound on an interval

`exists_cut_lag_two_ratio`: for every `K > 0` there is `b > 0` with `ρ(2) ≤ K ρ(0)` on `[0, b]`. The
numerator is `StrongCoupling.corrClay_abs_le_coreConst_mul_rate_pow` at `k = 1`, admissible because
`circLag 2 = 2`; the denominator is `ContactFloor.corrClay_zero_ge`. `confines_below_derived_cut`
feeds that to the criterion and gives `3 ^ (-1/4) < cosAvgEven ap4 β` for `β ≤ b`.

Scope: the aperture is fixed at `ConfinesZero.ap4`, extent four, throughout sections 2 to 4; the
correlation is `wilsonCorrAt 3`. `exists_cut_lag_two_ratio` and `confines_below_derived_cut` produce
the cut `b` existentially — no numeral is named for it, and no statement in this file covers
couplings above it. `lagTwoThreshold` is defined by a closed form; the decimal brackets report where
it sits and are not used to define it.
-/

namespace MassGap.LagTwoBound

open MassGap MassGap.ApertureRoute MassGap.StrongCoupling

/-! ## 1. The threshold `lagTwoThreshold`, and its position on the real line -/

/-- `((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ (4 : ℕ) = 1 / 3`. The natural-power is rewritten as an `rpow` by
`Real.rpow_natCast`, the exponents multiply by `Real.rpow_mul` (which needs `0 ≤ 3`), and
`(-(1)/4) * 4 = -1` leaves `3 ^ (-1) = 1/3`.

DERIVED: `3` is the base, the directed-path branching count carried by `ConfinesZero.floor_pos`, and
appears again as the denominator of the result; `1` is the numerator of the exponent `-(1)/4` and
again the numerator of `1/3`; `4` is the root taken in `3 ^ (-1/4)` and again the natural power that
undoes it. -/
theorem floor_pow_four : ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ (4 : ℕ) = 1 / 3 := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have h1 : ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ (4 : ℕ)
      = ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ (((4 : ℕ) : ℝ)) := (Real.rpow_natCast _ 4).symm
  have h2 : ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ (((4 : ℕ) : ℝ))
      = (3 : ℝ) ^ ((-(1 : ℝ) / 4) * ((4 : ℕ) : ℝ)) := (Real.rpow_mul h3 _ _).symm
  have h4 : (-(1 : ℝ) / 4) * ((4 : ℕ) : ℝ) = -(1 : ℝ) := by norm_num
  rw [h1, h2, h4, Real.rpow_neg h3, Real.rpow_one]
  norm_num

#print axioms floor_pow_four

/-- `0.5773501 < (3 ^ (-1/4)) ^ 2 < 0.5773505`. Setting `c := 3 ^ (-1/4)`, positivity comes from
`ConfinesZero.floor_pos` and `(c ^ 2) ^ 2 = 1/3` from `floor_pow_four`; `nlinarith` then pins `c ^ 2`
between the two rationals.

Scope: a two-sided bracket, not an evaluation — `c ^ 2` is `3 ^ (-1/2)`, irrational.

DERIVED: `0.5773501` and `0.5773505` are the reported bracket on `3 ^ (-1/2)`, chosen only to be
narrow enough for the brackets on `lagTwoThreshold` downstream; `3`, `1` and `4` are the base,
exponent numerator and root of `3 ^ (-1/4)`, appearing once in each conjunct; the exponent `2` is
the square, appearing once in each conjunct. -/
theorem floor_sq_bounds :
    0.5773501 < ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2
      ∧ ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 < 0.5773505 := by
  set c : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hcdef
  have hc0 : 0 < c := by rw [hcdef]; exact MassGap.ConfinesZero.floor_pos
  have h4 : c ^ (4 : ℕ) = 1 / 3 := by rw [hcdef]; exact floor_pow_four
  have hs0 : 0 < c ^ 2 := by positivity
  have hs2 : (c ^ 2) ^ 2 = 1 / 3 := by rw [← h4]; ring
  constructor
  · nlinarith [hs2, hs0]
  · nlinarith [hs2, hs0, sq_nonneg (c ^ 2 - 0.5773505)]

#print axioms floor_sq_bounds

/-- `0.759835 < 3 ^ (-1/4) < 0.759836`, obtained from `floor_sq_bounds` by `nlinarith` together with
positivity of `3 ^ (-1/4)` from `ConfinesZero.floor_pos`.

DERIVED: `0.759835` and `0.759836` are the reported bracket on `3 ^ (-1/4)`, at the width the
`lagTwoThreshold` brackets need; `3`, `1` and `4` are the base, exponent numerator and root of
`3 ^ (-1/4)`, appearing once in each conjunct. -/
theorem floor_bounds :
    0.759835 < (3 : ℝ) ^ (-(1 : ℝ) / 4) ∧ (3 : ℝ) ^ (-(1 : ℝ) / 4) < 0.759836 := by
  obtain ⟨hlo, hhi⟩ := floor_sq_bounds
  set c : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hcdef
  have hc0 : 0 < c := by rw [hcdef]; exact MassGap.ConfinesZero.floor_pos
  constructor
  · nlinarith [hlo, hc0]
  · nlinarith [hhi, hc0, sq_nonneg (c - 0.759836)]

#print axioms floor_bounds

/-- The real `((1 - 3 ^ (-(1:ℝ)/4)) / (1 + 3 ^ (-(1:ℝ)/4))) ^ 2`, the bound on the ratio
`ρ(2)/ρ(0)` under which `lag_two_criterion_of_ratio` delivers the extent-four criterion. Writing
`c = 3 ^ (-1/4)`, the criterion `(1 + c)² ρ(2) < (1 - c)² ρ(0)` is exactly `ρ(2)/ρ(0) < ((1-c)/(1+c))²`
once `ρ(0) > 0`, so this is the criterion's own threshold in ratio form.

Scope: a closed-form real, defined by the expression above. `lagTwoThreshold_gt` and
`lagTwoThreshold_lt` report where it lies; neither is used to define it.

DERIVED, term by term:

* `3` and `4` are the base and root of `c = 3 ^ (-1/4)`, the value `ConfinesZero.floor_pos` and
  `ConfinesZero.floor_lt_one` are stated about. They enter as `e^{-κ₀}` for `κ₀ = (1/4) log 3`: the
  directed cube-path count is `3^k`, and the per-area normalisation `((n-1) log 3)/(4n+2)` tends to
  `(1/4) log 3`.
* The two `1`s appearing as exponent numerators are the `-(1)/4` in each copy of `3 ^ (-1/4)`; the
  two `1`s appearing as summands are the `1 - c` and `1 + c` of the criterion's quadratic.
* `2` is the outer exponent: the criterion bounds `t = sqrt (ρ(2)/ρ(0))`, so the bound on the ratio
  is the root `(1-c)/(1+c)` squared. -/
noncomputable def lagTwoThreshold : ℝ :=
  ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4))) ^ 2

#print axioms lagTwoThreshold

theorem lagTwoThreshold_pos : 0 < lagTwoThreshold := by
  have hc0 : 0 < (3 : ℝ) ^ (-(1 : ℝ) / 4) := MassGap.ConfinesZero.floor_pos
  have hc1 : (3 : ℝ) ^ (-(1 : ℝ) / 4) < 1 := MassGap.ConfinesZero.floor_lt_one
  unfold lagTwoThreshold
  exact pow_pos (div_pos (by linarith) (by linarith)) 2

#print axioms lagTwoThreshold_pos

/-- `0.018623 < lagTwoThreshold`. The definition is unfolded, the square of the quotient split by
`div_pow`, and `nlinarith` closes it from the upper bracket of `floor_bounds` together with
positivity of `3 ^ (-1/4)`.

DERIVED: `0.018623` is the reported lower bracket on `lagTwoThreshold`; it is a report of where the
closed form sits, and the threshold used by `lag_two_criterion_of_ratio` is the closed form, not
this rational. -/
theorem lagTwoThreshold_gt : 0.018623 < lagTwoThreshold := by
  obtain ⟨hlo, hhi⟩ := floor_bounds
  have hc0 : 0 < (3 : ℝ) ^ (-(1 : ℝ) / 4) := MassGap.ConfinesZero.floor_pos
  unfold lagTwoThreshold
  set c : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hcdef
  have hden : (0 : ℝ) < (1 + c) ^ 2 := by nlinarith [hc0]
  rw [div_pow, lt_div_iff₀ hden]
  nlinarith [hhi, hc0, sq_nonneg (c - 0.759835)]

#print axioms lagTwoThreshold_gt

/-- `lagTwoThreshold < 0.018625`, the other half of the bracket, proved the same way from the lower
half of `floor_bounds`. Used by `contact_relative_constant_too_large` here, and by
`LagTwoQuadratic.lagTwoThreshold_lt_lagTwoThresholdQuad`,
`LagTwoSix.lagTwoThreshold_lt_lagTwoThresholdSix`,
`DiffractionNoGo.ceiling_admits_lag_two_above_threshold`,
`FreeFieldLagTwo.flat_profile_fails_the_threshold` and `TailRatio.no_bound_at_the_threshold`.

DERIVED: `0.018625` is the reported upper bracket on `lagTwoThreshold`. -/
theorem lagTwoThreshold_lt : lagTwoThreshold < 0.018625 := by
  obtain ⟨hlo, hhi⟩ := floor_bounds
  have hc0 : 0 < (3 : ℝ) ^ (-(1 : ℝ) / 4) := MassGap.ConfinesZero.floor_pos
  unfold lagTwoThreshold
  set c : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hcdef
  have hden : (0 : ℝ) < (1 + c) ^ 2 := by nlinarith [hc0]
  rw [div_pow, div_lt_iff₀ hden]
  nlinarith [hlo, hc0, mul_pos (sub_pos.2 hhi) hc0]

#print axioms lagTwoThreshold_lt

/-! ## 2. From a ratio bound to the criterion, and to `ConfinesAtAnAperture` -/

/-- At any real coupling `β`, if `K < lagTwoThreshold` and
`wilsonCorrAt 3 β 2 ≤ K * wilsonCorrAt 3 β 0`, then
`(1 + 3 ^ (-(1:ℝ)/4)) ^ 2 * wilsonCorrAt 3 β 2 < (1 - 3 ^ (-(1:ℝ)/4)) ^ 2 * wilsonCorrAt 3 β 0`.

The hypothesis on the ratio is non-strict and the conclusion is strict: the gap comes from
`PlaqVariance.corrClay_zero_pos`, which makes `wilsonCorrAt 3 β 0` strictly positive at every real
coupling, so multiplying the strict `K < lagTwoThreshold` by it stays strict. The final step cancels
`(1 + c) * ((1 - c)/(1 + c))` to `1 - c`, valid since `1 + c ≠ 0`.

Scope: `β` is unconstrained in sign — the correlation's positivity at lag zero holds at every real
coupling. The conclusion is the criterion at a single `β`, not `ConfinesAtAnAperture`.

DERIVED: `3` occurs five times — once as the aperture argument of each of the four `wilsonCorrAt`
calls, and once inside each of the two copies of `3 ^ (-(1:ℝ)/4)`, which is `c`; `1` occurs six
times — as the exponent numerator in each copy of `3 ^ (-(1:ℝ)/4)`, and as the summand in `1 + c` and
in `1 - c`; `4` occurs twice, as the root in each copy of `c`; `2` occurs four times — as the lag
index of `wilsonCorrAt 3 β 2` in hypothesis and conclusion, and as the exponent on `1 + c` and on
`1 - c`; `0` occurs twice, as the lag index of `wilsonCorrAt 3 β 0` in hypothesis and conclusion. -/
theorem lag_two_criterion_of_ratio {β K : ℝ} (hK : K < lagTwoThreshold)
    (h : MassGap.wilsonCorrAt 3 β 2 ≤ K * MassGap.wilsonCorrAt 3 β 0) :
    (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 * MassGap.wilsonCorrAt 3 β 2
      < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 * MassGap.wilsonCorrAt 3 β 0 := by
  have hρ0 : 0 < MassGap.wilsonCorrAt 3 β 0 := by
    rw [MassGap.StrongArm.wilsonCorrAt_eq_corrClay]
    exact MassGap.PlaqVariance.corrClay_zero_pos 3 β
  unfold lagTwoThreshold at hK
  set c : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hcdef
  have hc0 : 0 < c := by rw [hcdef]; exact MassGap.ConfinesZero.floor_pos
  have hne : (1 : ℝ) + c ≠ 0 := ne_of_gt (by linarith)
  have hsq : (0 : ℝ) < (1 + c) ^ 2 := by nlinarith [hc0]
  have hcancel : (1 + c) * ((1 - c) / (1 + c)) = 1 - c := by
    field_simp
  calc (1 + c) ^ 2 * MassGap.wilsonCorrAt 3 β 2
      ≤ (1 + c) ^ 2 * (K * MassGap.wilsonCorrAt 3 β 0) :=
        mul_le_mul_of_nonneg_left h hsq.le
    _ < (1 + c) ^ 2 * (((1 - c) / (1 + c)) ^ 2 * MassGap.wilsonCorrAt 3 β 0) :=
        mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right hK hρ0) hsq
    _ = ((1 + c) * ((1 - c) / (1 + c))) ^ 2 * MassGap.wilsonCorrAt 3 β 0 := by ring
    _ = (1 - c) ^ 2 * MassGap.wilsonCorrAt 3 β 0 := by rw [hcancel]

#print axioms lag_two_criterion_of_ratio

/-- If `K < lagTwoThreshold` and `wilsonCorrAt 3 β 2 ≤ K * wilsonCorrAt 3 β 0` at every `β ≥ 0`,
then `ApertureRoute.ConfinesAtAnAperture` holds. The witness aperture is `ConfinesZero.ap4`, and
each `β` is handled by `ConfinesZero.confines_extent_four_of_lag_two_small` fed with
`lag_two_criterion_of_ratio` at `max β 0`.

Scope: the hypothesis is only required on the nonnegative half-line, because `readEven` clamps its
argument at `max β 0`; the conclusion nonetheless quantifies over all real `β`. The aperture
produced is `ap4` specifically — extent four — not an arbitrary one.

DERIVED: `0` occurs twice, as the lower bound on `β` in the hypothesis and as the lag index of
`wilsonCorrAt 3 β 0`; `3` occurs twice, as the aperture argument of each `wilsonCorrAt`; `2` is the
lag index of `wilsonCorrAt 3 β 2`, the second lag the bound is about. -/
theorem confines_of_lag_two_ratio (K : ℝ) (hK : K < lagTwoThreshold)
    (h : ∀ β : ℝ, 0 ≤ β → MassGap.wilsonCorrAt 3 β 2 ≤ K * MassGap.wilsonCorrAt 3 β 0) :
    ApertureRoute.ConfinesAtAnAperture :=
  ⟨MassGap.ConfinesZero.ap4, fun β =>
    MassGap.ConfinesZero.confines_extent_four_of_lag_two_small β
      (lag_two_criterion_of_ratio hK (h (max β 0) (le_max_right β 0)))⟩

#print axioms confines_of_lag_two_ratio

/-! ## 3. The size of `coreConst`, against the threshold -/

/-- `Moment.circLag (2 : Fin (3 + 1)) = 2`, by `decide`. At extent four the circular distance from
lag `2` to the origin is `min 2 (4 - 2) = 2`, the maximum a lag can have at this extent.

DERIVED: the first `2` is the lag whose circular distance is taken; `3` and `1` are the extent
written as `3 + 1`, matching `wilsonCorrAt 3`'s aperture convention; the final `2` is the computed
circular distance. -/
theorem circLag_two : Moment.circLag (2 : Fin (3 + 1)) = 2 := by decide

#print axioms circLag_two

/-- For `0 ≤ β` and `coreRate K β < 1`, `128 ≤ coreConst K β`. `coreConst` unfolds to
`corePrefactor K β / (1 - coreRate K β)`; `le_corePrefactor` gives `128 ≤ corePrefactor K β`,
`coreRate_nonneg` gives `0 ≤ coreRate K β`, so the denominator lies in `(0, 1]` and dividing by it
cannot decrease the numerator.

Scope: `hr : coreRate K β < 1` is what makes the denominator positive; the bound fails to be stated
at all above the rate-one threshold. `K : ℕ` is an arbitrary degree.

DERIVED: `0` is the lower bound on `β`; `1` is the rate-one threshold, the point at which
`coreConst`'s denominator vanishes; `128` is `le_corePrefactor`'s own lower bound on
`corePrefactor`. -/
theorem le_coreConst (K : ℕ) {β : ℝ} (hβ : 0 ≤ β) (hr : coreRate K β < 1) :
    128 ≤ coreConst K β := by
  have hP : (128 : ℝ) ≤ corePrefactor K β := le_corePrefactor K hβ
  have hr0 : (0 : ℝ) ≤ coreRate K β := coreRate_nonneg K hβ
  have hden : (0 : ℝ) < 1 - coreRate K β := by linarith
  unfold coreConst
  rw [le_div_iff₀ hden]
  nlinarith [hP, hr0]

#print axioms le_coreConst

/-- For `0 ≤ b` and `coreRate (16 * 4) b < 1`, `16 * lagTwoThreshold < coreConst (16 * 4) b`. It
combines `lagTwoThreshold_lt` (`lagTwoThreshold < 0.018625`, so `16 * lagTwoThreshold < 0.298`) with
`le_coreConst` (`128 ≤ coreConst (16 * 4) b`) by `linarith`; the two sides differ by a factor of over
four hundred.

The factor `16` is `2 ^ 4`, the divisor a contact-relative bound of the form
`ρ(d) ≤ C ρ(0) / circLag d ^ 4` carries at `d = 2`, where `circLag_two` gives `circLag 2 = 2`.

Scope: this compares two named quantities, `16 * lagTwoThreshold` and `coreConst (16 * 4) b`. It is
not a statement about the existential constant in `ContactFloor.contact_relative_unconditional`, and
refutes nothing.

DERIVED: `0` is the lower bound on `b`; `1` is the rate-one threshold inherited from `le_coreConst`;
the leading `16` is `circLag 2 ^ 4 = 2 ^ 4`, the divisor in the contact-relative shape; the `16 * 4`
appearing twice is the degree argument of `coreRate` and `coreConst`, which is
`StrongCoupling.touchDeg_bd_le`'s degree against `WilsonAction.wilsonDensity_le_two` and is carried
through unchanged. -/
theorem contact_relative_constant_too_large {b : ℝ} (hb : 0 ≤ b)
    (hr : coreRate (16 * 4) b < 1) :
    16 * lagTwoThreshold < coreConst (16 * 4) b := by
  have h1 := lagTwoThreshold_lt
  have h2 : (128 : ℝ) ≤ coreConst (16 * 4) b := le_coreConst (16 * 4) hb hr
  linarith

#print axioms contact_relative_constant_too_large

/-! ## 4. The ratio bound on an interval `[0, b]`, and the criterion below the cut -/

/-- For every `K > 0` there exists `b > 0` such that `wilsonCorrAt 3 β 2 ≤ K * wilsonCorrAt 3 β 0`
for all `0 ≤ β ≤ b`.

The numerator is bounded by `StrongCoupling.corrClay_abs_le_coreConst_mul_rate_pow` at exponent
`k = 1`, admissible because `circLag_two` gives `circLag 2 = 2 > 1`, and made uniform on the interval
by `StrongArm.coreConst_mono_beta` and `StrongArm.coreRate_mono_beta` against the endpoint `b₀` of
`StrongArm.exists_strong_arm_cut`. The denominator is bounded below by
`ContactFloor.corrClay_zero_ge`, which gives `exp (-(128 * β)) * ρ(0)|_{β=0} ≤ ρ(0)`. The cut is
`min b₀ (ε/2)`, with `ε` produced by continuity of `β ↦ coreConst (16*4) b₀ * (coreRate (16*4) β *
exp (128 * β))` at `β = 0`, where that function vanishes while `K * ρ(0)|_{β=0}` is positive.

Scope: `b` is existential. No numeral is named for it, and none is available: `ρ(0)|_{β=0}` enters
only through `PlaqVariance.corrClay_zero_pos`, which gives positivity without a value. The bound
holds on `[0, b]` only; nothing is stated for larger couplings. `K` is a free parameter, so the
constant can be made as small as desired at the cost of a smaller `b`.

DERIVED: `0` occurs three times — the positivity threshold of `K`, the positivity threshold of the
cut `b`, and the lower endpoint of the interval `0 ≤ β`; a fourth `0` is the lag index of
`wilsonCorrAt 3 β 0`. `3` occurs twice, as the aperture argument of each `wilsonCorrAt`; `2` is the
lag index of `wilsonCorrAt 3 β 2`. The `16 * 4`, `128` and `1` in the proof are the degree, the
exponential floor rate and the power of the rate, all inherited from `StrongCoupling` and
`ContactFloor`; none appears in the statement. -/
theorem exists_cut_lag_two_ratio (K : ℝ) (hK : 0 < K) :
    ∃ b : ℝ, 0 < b ∧ ∀ β : ℝ, 0 ≤ β → β ≤ b →
      MassGap.wilsonCorrAt 3 β 2 ≤ K * MassGap.wilsonCorrAt 3 β 0 := by
  obtain ⟨b₀, hb₀, hr₀⟩ := MassGap.StrongArm.exists_strong_arm_cut
  set A : ℝ := coreConst (16 * 4) b₀ with hAdef
  have hA128 : (128 : ℝ) ≤ A := by rw [hAdef]; exact le_coreConst (16 * 4) hb₀.le hr₀
  have hA0 : 0 < A := by linarith
  set D : ℝ := MassGap.WilsonBridge.corrClay (3 + 1) 0 0 with hDdef
  have hD0 : 0 < D := by rw [hDdef]; exact MassGap.PlaqVariance.corrClay_zero_pos 3 0
  have hcont : Continuous
      (fun β : ℝ => A * (coreRate (16 * 4) β * Real.exp (128 * β))) := by
    have h1 : Continuous (fun β : ℝ => Real.exp (128 * β)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    exact continuous_const.mul ((continuous_coreRate (16 * 4)).mul h1)
  have hzero : A * (coreRate (16 * 4) 0 * Real.exp (128 * 0)) < K * D := by
    rw [coreRate_at_zero]
    have hz : A * (0 * Real.exp (128 * 0)) = 0 := by ring
    rw [hz]
    exact mul_pos hK hD0
  have htend : Filter.Tendsto (fun β : ℝ => A * (coreRate (16 * 4) β * Real.exp (128 * β)))
      (nhds 0) (nhds (A * (coreRate (16 * 4) 0 * Real.exp (128 * 0)))) :=
    hcont.continuousAt
  have hev : ∀ᶠ x in nhds (0 : ℝ),
      A * (coreRate (16 * 4) x * Real.exp (128 * x)) < K * D :=
    htend.eventually_lt_const hzero
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨min b₀ (ε / 2), lt_min hb₀ (by linarith), ?_⟩
  intro β hβ0 hβb
  have hβb₀ : β ≤ b₀ := le_trans hβb (min_le_left _ _)
  have hβε : β < ε := lt_of_le_of_lt (le_trans hβb (min_le_right _ _)) (by linarith)
  have hf : A * (coreRate (16 * 4) β * Real.exp (128 * β)) < K * D := by
    refine hball ?_
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hβ0]
    exact hβε
  have hrβ : coreRate (16 * 4) β ≤ coreRate (16 * 4) b₀ :=
    MassGap.StrongArm.coreRate_mono_beta (16 * 4) hβ0 hβb₀
  have hrβ1 : coreRate (16 * 4) β < 1 := lt_of_le_of_lt hrβ hr₀
  have hrnn : (0 : ℝ) ≤ coreRate (16 * 4) β := coreRate_nonneg (16 * 4) hβ0
  have hAβ : coreConst (16 * 4) β ≤ A := by
    rw [hAdef]; exact MassGap.StrongArm.coreConst_mono_beta (16 * 4) hβ0 hβb₀ hr₀
  have hbnd := corrClay_abs_le_coreConst_mul_rate_pow 3 hβ0 hrβ1 (2 : Fin (3 + 1)) 1
    (by rw [circLag_two]; norm_num)
  have hstep : MassGap.wilsonCorrAt 3 β 2 ≤ A * coreRate (16 * 4) β := by
    rw [MassGap.StrongArm.wilsonCorrAt_eq_corrClay]
    calc MassGap.WilsonBridge.corrClay (3 + 1) β 2
        ≤ |MassGap.WilsonBridge.corrClay (3 + 1) β 2| := le_abs_self _
      _ ≤ coreConst (16 * 4) β * coreRate (16 * 4) β ^ 1 := hbnd
      _ = coreConst (16 * 4) β * coreRate (16 * 4) β := by ring
      _ ≤ A * coreRate (16 * 4) β := mul_le_mul_of_nonneg_right hAβ hrnn
  have hfloor : Real.exp (-(128 * β)) * D ≤ MassGap.wilsonCorrAt 3 β 0 := by
    rw [MassGap.StrongArm.wilsonCorrAt_eq_corrClay, hDdef]
    exact MassGap.ContactFloor.corrClay_zero_ge 3 hβ0
  have hcancel : Real.exp (128 * β) * Real.exp (-(128 * β)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hkey : A * coreRate (16 * 4) β ≤ K * (Real.exp (-(128 * β)) * D) := by
    have hmul : (A * (coreRate (16 * 4) β * Real.exp (128 * β))) * Real.exp (-(128 * β))
        ≤ (K * D) * Real.exp (-(128 * β)) :=
      mul_le_mul_of_nonneg_right hf.le (Real.exp_pos _).le
    have hlhs : (A * (coreRate (16 * 4) β * Real.exp (128 * β))) * Real.exp (-(128 * β))
        = A * coreRate (16 * 4) β := by
      calc (A * (coreRate (16 * 4) β * Real.exp (128 * β))) * Real.exp (-(128 * β))
          = A * coreRate (16 * 4) β * (Real.exp (128 * β) * Real.exp (-(128 * β))) := by ring
        _ = A * coreRate (16 * 4) β := by rw [hcancel, mul_one]
    have hrhs : (K * D) * Real.exp (-(128 * β)) = K * (Real.exp (-(128 * β)) * D) := by ring
    rw [hlhs, hrhs] at hmul
    exact hmul
  have hlast : K * (Real.exp (-(128 * β)) * D) ≤ K * MassGap.wilsonCorrAt 3 β 0 :=
    mul_le_mul_of_nonneg_left hfloor hK.le
  linarith

#print axioms exists_cut_lag_two_ratio

/-- There exists `b > 0` with `3 ^ (-(1:ℝ)/4) < cosAvgEven ConfinesZero.ap4 β` for every `β ≤ b`.
The cut is the one `exists_cut_lag_two_ratio` produces at the ratio constant `lagTwoThreshold / 2`,
and each `β` is closed by `ConfinesZero.confines_extent_four_of_lag_two_small` fed with
`lag_two_criterion_of_ratio`.

The halving in the proof only supplies a constant strictly below `lagTwoThreshold`, as
`lag_two_criterion_of_ratio` requires; any such constant gives the same statement, and it does not
appear in the conclusion.

Scope: the conclusion is over `β ≤ b`, which includes the whole negative half-line because the
ratio hypothesis is read at `max β 0`. The aperture is `ConfinesZero.ap4`, extent four. Nothing is
stated for `β > b`.

DERIVED: `0` is the positivity threshold of the cut `b`; `3`, `1` and `4` are the base, exponent
numerator and root of `3 ^ (-(1:ℝ)/4)`, the floor the averaged cosine is compared against. -/
theorem confines_below_derived_cut :
    ∃ b : ℝ, 0 < b ∧ ∀ β : ℝ, β ≤ b →
      (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven MassGap.ConfinesZero.ap4 β := by
  have hT := lagTwoThreshold_pos
  obtain ⟨b, hb, h⟩ := exists_cut_lag_two_ratio (lagTwoThreshold / 2) (by linarith)
  refine ⟨b, hb, fun β hβ => ?_⟩
  refine MassGap.ConfinesZero.confines_extent_four_of_lag_two_small β ?_
  exact lag_two_criterion_of_ratio (by linarith)
    (h (max β 0) (le_max_right β 0) (max_le hβ hb.le))

#print axioms confines_below_derived_cut

end MassGap.LagTwoBound
