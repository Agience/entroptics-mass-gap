import Mathlib
import MassGap.LagTwoSix
import MassGap.ConfinesEight

/-!
# MassGap.LagTwoEight — the lag-two threshold at extent eight

The extent-eight counterparts of `LagTwoBound.lagTwoThreshold` and `LagTwoSix.lagTwoThresholdSix`, in
the same currency: a bound on `ρ(2)/ρ(0)` sufficient for the extent-eight confinement criterion.
`lagTwoThresholdSix_lt_lagTwoThresholdEight` compares the two thresholds.

## The criterion at even extent `2m`, reduced at `m = 4`

`ConfinesEight.confines_extent_eight_iff` is the `m = 4` case of

    ∑_{d=1}^{m−1} 2(c − cos(πd/m))·ρ(d) + (1+c)·ρ(m) < (1−c)·ρ(0),      c = 3^{−1/4}

At `m = 4` the cosines are `cos(π/4) = √2/2`, `cos(2π/4) = 0` and `cos(3π/4) = −√2/2`, so every
coefficient is exact in `c` and `√2`:

* on `ρ(1)`:  `2(c − √2/2) = 2c − √2`                                    — `bEight`
* on `ρ(2)`, `ρ(3)` and `ρ(4)` together, the deeper two bounded by `ρ(2)`:
  `2c + 2(c + √2/2) + (1 + c) = 5c + √2 + 1`                            — `aEight`

Substituting `ρ(1) = v` and every deeper lag at `ρ(2) = v²` on `LogConvex.corrClay_log_convex`'s cone
leaves one quadratic in `v = √(ρ(2)/ρ(0))`:

    aEight·v² + bEight·v = 1 − c

`vEight` is its positive root, `vEight_root` is the root identity, and `lagTwoThresholdEight` is
`vEight ^ 2`. `bEight_pos` records that the `ρ(1)` coefficient is positive at this extent; the
brackets `0.0354 < lagTwoThresholdEight < 0.0355` come from brackets on `c`
(`LagTwoBound.floor_bounds`) and on `√2` (`sqrt_two_bounds`), with `vEight` bracketed first and only
then squared.

## What follows

* the three log-convexity instances at half-extent four — `logConvex_eight_lag_one`,
  `logConvex_eight_lag_four`, `logConvex_eight_lag_three` — and the two orderings they give,
  `lag_four_le_lag_two` and `lag_three_le_lag_two_eight`, both at the clamped coupling `max β 0`;
* `confines_extent_eight_of_lag_two_ratio`, the sufficient condition at one coupling, and
  `LagTwoRatioEight`, the `Prop` collecting it over all nonnegative couplings, with
  `confines_of_lagTwoRatioEight` reducing `ApertureRoute.ConfinesAtAnAperture` to it at the witness
  `ConfinesEight.ap8`;
* `lagTwoThresholdEight_sharp`, which exhibits five reals satisfying the log-convexity inequalities
  at `r₂ = lagTwoThresholdEight * r₀` and refuting the criterion there, so no larger constant is
  carried by this reduction;
* `flat_profile_defeats_every_admissible_K`, which says no `K` below the threshold bounds a ratio of
  `1`;
* `exists_cut_lag_two_ratio_eight`, which proves the ratio bound for every `K > 0` on an interval
  `[0, b]` rather than on the whole half-line.

Foundational footprint only (`#print axioms` on every declaration).
Build: `python research/code/lean_build.py build MassGap.LagTwoEight`.
-/

namespace MassGap.LagTwoEight

/-- The `ρ(1)` coefficient of the extent-eight criterion: `2(c − cos(π/4)) = 2c − √2`, at
`c = 3 ^ (−1/4)`.

DERIVED: the leading `2` is the criterion's multiplicity on an interior lag; `3`, `1` and `4` are the
entropy floor `3 ^ (−1/4)` written out, base and exponent; the `2` under `Real.sqrt` is
`2 cos(π/4) = √2`. Nothing is chosen. -/
noncomputable def bEight : ℝ := 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - Real.sqrt 2

/-- The deep-lag coefficient at extent eight, with `ρ(2)`, `ρ(3)` and `ρ(4)` collected on the cone:
`2(c − cos(π/2)) + 2(c − cos(3π/4)) + (1 + c) = 2c + (2c + √2) + (1 + c) = 5c + √2 + 1`.

DERIVED: `5` is `2 + 2 + 1`, the three criterion coefficients on `c` collected, using `cos(π/2) = 0`;
`3`, `1` and `4` are the entropy floor `3 ^ (−1/4)`, base and exponent; the `2` under `Real.sqrt`
comes from `−2 cos(3π/4) = √2`; the trailing `1` is the constant part of the self-paired lag's
coefficient `1 + c`. No magnitude is chosen. -/
noncomputable def aEight : ℝ := 5 * (3 : ℝ) ^ (-(1 : ℝ) / 4) + Real.sqrt 2 + 1

theorem sqrt_two_bounds : 1.41421356 < Real.sqrt 2 ∧ Real.sqrt 2 < 1.41421357 := by
  constructor
  · nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  · nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

theorem aEight_pos : 0 < aEight := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have hs := sqrt_two_bounds
  unfold aEight
  linarith [hc.1, hs.1]

/-- `0 < bEight`: the `ρ(1)` coefficient is positive at extent eight, so the reduced quadratic has a
positive linear term. From `LagTwoBound.floor_bounds`' lower bracket on `c` against
`sqrt_two_bounds`' upper bracket on `√2`.

DERIVED: `0` is the sign condition on `bEight`. -/
theorem bEight_pos : 0 < bEight := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have hs := sqrt_two_bounds
  unfold bEight
  linarith [hc.1, hs.2]

/-- The discriminant of the reduced quadratic is positive:
`0 < bEight ^ 2 + 4 * aEight * (1 − c)`. `aEight_pos`, `bEight_pos` and `LagTwoBound.floor_bounds`
(which puts `c` below `1`) are the inputs.

DERIVED: `0` is the sign condition; `2` is the exponent on `bEight`; `4` is the quadratic formula's
coefficient; the standalone `1` is the left term of `1 − c`; `3`, `1` and `4` are the entropy floor
`3 ^ (−1/4)`, base and exponent. -/
theorem disc_pos :
    0 < bEight ^ 2 + 4 * aEight * (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have ha := aEight_pos
  have hb := bEight_pos
  nlinarith [hc.1, hc.2, ha, hb, sq_nonneg bEight]

/-- The positive root of the extent-eight reduced criterion `aEight·v² + bEight·v = 1 − c`, in
`v = √(ρ(2)/ρ(0))`, written by the quadratic formula as
`(√(bEight ^ 2 + 4·aEight·(1 − c)) − bEight) / (2·aEight)`.

DERIVED: `2` is the exponent on `bEight` under the root and, in the denominator, the `2a` of the
quadratic formula; `4` is that formula's `4ac`; the standalone `1` is the left term of `1 − c`; `3`,
`1` and `4` are the entropy floor `3 ^ (−1/4)`, base and exponent. -/
noncomputable def vEight : ℝ :=
  (Real.sqrt (bEight ^ 2 + 4 * aEight * (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))) - bEight) / (2 * aEight)

/-- The threshold on the lag-two ratio at extent eight: `vEight ^ 2`, because the reduced criterion
is a bound on `√(ρ(2)/ρ(0))` while the threshold is stated on the ratio itself. The extent-eight
counterpart of `LagTwoBound.lagTwoThreshold` and `LagTwoSix.lagTwoThresholdSix`.

DERIVED: `2` is the exponent of the squaring, and the only numeral in the body. -/
noncomputable def lagTwoThresholdEight : ℝ := vEight ^ 2

theorem vEight_pos : 0 < vEight := by
  have ha := aEight_pos
  have hd := disc_pos
  have hb := bEight_pos
  unfold vEight
  apply div_pos _ (by linarith)
  have hsq : bEight ^ 2 < bEight ^ 2 + 4 * aEight * (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) := by
    have hc := MassGap.LagTwoBound.floor_bounds
    nlinarith [ha, hc.2]
  have := Real.sqrt_lt_sqrt (sq_nonneg bEight) hsq
  rw [Real.sqrt_sq hb.le] at this
  linarith

/-- The root identity `aEight * vEight ^ 2 + bEight * vEight = 1 − c`: the threshold is the reduced
criterion's own root, taken at equality rather than at a cut below it. Proved by collapsing
`(D − b)² + 2b(D − b) = D² − b²` symbolically in `D` and then substituting
`Real.sq_sqrt disc_pos.le`.

DERIVED: `2` is the exponent on `vEight`; the standalone `1` is the left term of `1 − c`; `3`, `1`
and `4` are the entropy floor `3 ^ (−1/4)`, base and exponent. -/
theorem vEight_root :
    aEight * vEight ^ 2 + bEight * vEight = 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
  have ha := aEight_pos
  have hd := disc_pos
  have hane : (4 : ℝ) * aEight ≠ 0 := ne_of_gt (by linarith)
  have hsq : Real.sqrt (bEight ^ 2 + 4 * aEight * (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))) ^ 2
      = bEight ^ 2 + 4 * aEight * (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) :=
    Real.sq_sqrt hd.le
  -- The `(D − b)² + 2b(D − b) = D² − b²` collapse, taken symbolically in `D` and then closed by
  -- the discriminant identity, the shape `LagTwoSix.vSix_root` uses. Handing the whole goal to
  -- `nlinarith` instead leaves it to substitute `(√disc)²` inside a polynomial.
  have hkey : ∀ D : ℝ, aEight * ((D - bEight) / (2 * aEight)) ^ 2
        + bEight * ((D - bEight) / (2 * aEight))
      = (D ^ 2 - bEight ^ 2) / (4 * aEight) := by
    intro D
    have : aEight ≠ 0 := ne_of_gt ha
    field_simp
    ring
  rw [vEight, hkey, hsq, div_eq_iff hane]
  ring

/-! ### The brackets

`v` is bracketed first, from the closed form through `lt_div_iff₀` and `div_lt_iff₀`, and only then
squared. Every input is a bracket on `c` (`LagTwoBound.floor_bounds`) or on `√2`
(`sqrt_two_bounds`); reading the bracket off the root identity instead would leave `nlinarith` a
quadratic in the three unknowns `c`, `√2` and `v`. -/

/-- A rational lower bracket on the discriminant; `disc_lt` gives the matching upper bracket
`5.9801`. Every input is a bracket on `c` or on `√2`.

CHOSEN: `5.98` is the rational bracket, rounded down so the rounding cannot produce the inequality on
its own; `2` is the exponent on `bEight`, `4` is the quadratic formula's coefficient, the standalone
`1` is the left term of `1 − c`, and `3`, `1` and `4` are the entropy floor `3 ^ (−1/4)`, base and
exponent. -/
theorem disc_gt : 5.98 < bEight ^ 2 + 4 * aEight * (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have hs := sqrt_two_bounds
  unfold bEight aEight
  nlinarith [hc.1, hc.2, hs.1, hs.2]

theorem disc_lt : bEight ^ 2 + 4 * aEight * (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) < 5.9801 := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have hs := sqrt_two_bounds
  unfold bEight aEight
  nlinarith [hc.1, hc.2, hs.1, hs.2]

theorem sqrt_disc_gt :
    2.4454 < Real.sqrt (bEight ^ 2 + 4 * aEight * (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))) := by
  nlinarith [Real.sq_sqrt disc_pos.le, Real.sqrt_nonneg
    (bEight ^ 2 + 4 * aEight * (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))), disc_gt]

theorem sqrt_disc_lt :
    Real.sqrt (bEight ^ 2 + 4 * aEight * (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))) < 2.4455 := by
  nlinarith [Real.sq_sqrt disc_pos.le, Real.sqrt_nonneg
    (bEight ^ 2 + 4 * aEight * (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))), disc_lt]

/-- A rational lower bracket on `vEight`; `vEight_lt` gives the upper one, `0.18831`. Both are
rounded away from the claim `lagTwoThresholdSix < lagTwoThresholdEight`, so neither rounding can
produce that strict inequality on its own. The inputs are `sqrt_disc_gt` and upper brackets on
`bEight` and `aEight`.

CHOSEN: `0.1882` is a rational bracket below `vEight`, rounded down. -/
theorem vEight_gt : 0.1882 < vEight := by
  have ha := aEight_pos
  have hc := MassGap.LagTwoBound.floor_bounds
  have hs := sqrt_two_bounds
  unfold vEight
  rw [lt_div_iff₀ (by linarith : (0 : ℝ) < 2 * aEight)]
  have hb : bEight < 0.105459 := by
    unfold bEight; linarith [hc.2, hs.1]
  have haU : aEight < 6.2134 := by
    unfold aEight; linarith [hc.2, hs.2]
  nlinarith [sqrt_disc_gt, hb, haU, ha]

theorem vEight_lt : vEight < 0.18831 := by
  have ha := aEight_pos
  have hc := MassGap.LagTwoBound.floor_bounds
  have hs := sqrt_two_bounds
  unfold vEight
  rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * aEight)]
  have hb : 0.105456 < bEight := by
    unfold bEight; linarith [hc.1, hs.2]
  have haL : 6.2133 < aEight := by
    unfold aEight; linarith [hc.1, hs.1]
  nlinarith [sqrt_disc_lt, hb, haL, ha]

/-- The threshold bracketed for a reader; `lagTwoThresholdEight_lt` gives the upper end, `0.0355`.
The value is decided by the closed form `vEight ^ 2` through `vEight_gt` and `vEight_pos`; the
rationals decide nothing, and each rounds away from the claim it is used in.

CHOSEN: `0.0354` is a rational bracket below `lagTwoThresholdEight`, rounded down. -/
theorem lagTwoThresholdEight_gt : 0.0354 < lagTwoThresholdEight := by
  have hg := vEight_gt
  have hp := vEight_pos
  unfold lagTwoThresholdEight
  nlinarith [hg, hp]

theorem lagTwoThresholdEight_lt : lagTwoThresholdEight < 0.0355 := by
  have hl := vEight_lt
  have hp := vEight_pos
  unfold lagTwoThresholdEight
  nlinarith [hl, hp]

/-- Extent eight admits a larger lag-two constant than extent six:
`LagTwoSix.lagTwoThresholdSix < lagTwoThresholdEight`. The right-hand end comes from
`lagTwoThresholdEight_gt`. `LagTwoSix` publishes only a lower bracket on its own threshold, so the
upper one is derived here from `LagTwoSix.vSix_root`: both coefficients of that quadratic are
positive, so its left side is monotone in `vSix` and a value at `0.1839` already overshoots `1 − c`.

DERIVED: no numeral appears in the statement. -/
theorem lagTwoThresholdSix_lt_lagTwoThresholdEight :
    MassGap.LagTwoSix.lagTwoThresholdSix < lagTwoThresholdEight := by
  -- `LagTwoSix` publishes only a LOWER bracket (`lagTwoThresholdSix_gt`), so the upper one is taken
  -- here from `vSix_root` directly: both coefficients of that quadratic are positive, so it is
  -- monotone in `vSix` and a value at `0.1839` already overshoots `1 − c`.
  have hc := MassGap.LagTwoBound.floor_bounds
  have hroot := MassGap.LagTwoSix.vSix_root
  have hvp := MassGap.LagTwoSix.vSix_pos
  have hsix : MassGap.LagTwoSix.vSix < 0.1839 := by nlinarith [hroot, hvp, hc.1, hc.2]
  have hsix2 : MassGap.LagTwoSix.lagTwoThresholdSix < 0.0339 := by
    unfold MassGap.LagTwoSix.lagTwoThresholdSix
    nlinarith [hsix, hvp]
  calc MassGap.LagTwoSix.lagTwoThresholdSix
      < 0.0339 := hsix2
    _ < 0.0354 := by norm_num
    _ < lagTwoThresholdEight := lagTwoThresholdEight_gt

/-- `vEight < 1`, from `vEight_root` alone: `aEight` exceeds `6` and both terms of the left side are
nonnegative, so `vEight` cannot reach `1` without overshooting `1 − c`.

DERIVED: `1` is the upper bound on `vEight`. -/
theorem vEight_lt_one : vEight < 1 := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have hs := sqrt_two_bounds
  have hroot := vEight_root
  have hv0 := vEight_pos
  have hb := bEight_pos
  have ha : (6 : ℝ) < aEight := by unfold aEight; linarith [hc.1, hs.1]
  nlinarith [hroot, hv0, hb, ha, hc.1, hc.2]

/-- No constant above `lagTwoThresholdEight` is carried by this reduction.

The statement exhibits five reals `r₀ … r₄`, with `r₀` positive and the other four nonnegative, that
satisfy the three log-convexity inequalities `r₁ ^ 2 ≤ r₀ * r₂`, `r₂ ^ 2 ≤ r₀ * r₄` and
`r₃ ^ 2 ≤ r₂ * r₄`, sit at `r₂ = lagTwoThresholdEight * r₀` exactly, and do NOT satisfy the criterion's
strict inequality. The witness is `(1, vEight, vEight ^ 2, vEight ^ 2, vEight ^ 2)`: on it the
criterion's left side is `bEight·vEight + aEight·vEight²`, which `vEight_root` puts equal to `1 − c`,
the right side, so the strict `<` fails.

The criterion is written out in the statement with its own coefficients — `2c − √2` on `r₁`, `2c` on
`r₂`, `2c + √2` on `r₃`, `1 + c` on `r₄`, against `(1 − c) * r₀` — rather than invoked through
`ConfinesEight.confines_extent_eight_iff`. The five reals are constrained by nothing else: they are
not values of `wilsonCorrAt`, and the circle symmetry that would carry `r₅`, `r₆`, `r₇` is not part
of the statement. So this is sharpness against the three stated log-convexity inequalities, the same
scope `LagTwoSix.lagTwoThresholdSix_sharp` has.

DERIVED: `0` is the sign condition on each of the five components; the three exponents `2` are the
squares of the log-convexity inequalities; `2` also multiplies `c` in the coefficients of `r₁`, `r₂`
and `r₃`; `3`, `1` and `4` are the entropy floor `3 ^ (−1/4)`, base and exponent, at each of its five
occurrences; the `2` under `Real.sqrt` is `√2`; the standalone `1` is the constant part of `1 + c`
and of `1 − c`. -/
theorem lagTwoThresholdEight_sharp :
    ∃ r₀ r₁ r₂ r₃ r₄ : ℝ, 0 < r₀ ∧ 0 ≤ r₁ ∧ 0 ≤ r₂ ∧ 0 ≤ r₃ ∧ 0 ≤ r₄ ∧
      r₁ ^ 2 ≤ r₀ * r₂ ∧ r₂ ^ 2 ≤ r₀ * r₄ ∧ r₃ ^ 2 ≤ r₂ * r₄ ∧
      r₂ = lagTwoThresholdEight * r₀ ∧
      ¬ ((2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - Real.sqrt 2) * r₁
            + 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) * r₂
            + (2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) + Real.sqrt 2) * r₃
            + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₄
          < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀) := by
  have hv0 := vEight_pos
  have hv1 := vEight_lt_one
  have hroot := vEight_root
  have hs1 : vEight ^ 2 < 1 := by nlinarith [hv0, hv1]
  refine ⟨1, vEight, vEight ^ 2, vEight ^ 2, vEight ^ 2, one_pos, hv0.le, by positivity,
    by positivity, by positivity, ?_, ?_, le_of_eq (by ring), by rw [lagTwoThresholdEight]; ring, ?_⟩
  · nlinarith [hv0]
  · nlinarith [hs1, pow_pos hv0 2]
  · rw [not_lt]
    unfold aEight bEight at hroot
    nlinarith [hroot]

/-- `lagTwoThresholdEight < 1`, since it is `vEight ^ 2` and `vEight_lt_one` puts `vEight` below `1`,
with `vEight_pos` for the sign.

DERIVED: `1` is the upper bound on the threshold. -/
theorem lagTwoThresholdEight_lt_one : lagTwoThresholdEight < 1 := by
  have hv0 := vEight_pos
  have hv1 := vEight_lt_one
  unfold lagTwoThresholdEight
  nlinarith [hv0, hv1]

/-- No `K` below the threshold bounds a lag-two ratio of `1`.
For every real `K` with `K < lagTwoThresholdEight`, the inequality `(1 : ℝ) ≤ K * 1` is false —
immediately from `lagTwoThresholdEight_lt_one`. The two `1`s stand for a profile whose `ρ(2)` and
`ρ(0)` are equal, such as `TailRatio.no_strict_lag_bound_with_contact`'s constant profile, which also
meets this file's `lag_three_le_lag_two_eight` and `lag_four_le_lag_two` with equality. The statement
itself quantifies over `K` alone and mentions no correlation function, so that reading of the `1`s is
supplied from outside it.

DERIVED: `1` appears twice: as the ratio on the left of the bound, and as the `ρ(0)` the profile is
normalised to, so that `K * 1` is the bound `K` would have to meet. -/
theorem flat_profile_defeats_every_admissible_K :
    ∀ K : ℝ, K < lagTwoThresholdEight → ¬ ((1 : ℝ) ≤ K * 1) := by
  intro K hK hcon
  have := lagTwoThresholdEight_lt_one
  linarith

/-! ## The shape substitutions at half-extent four

`LogConvex.corrClay_log_convex` at `Nap = 7`, `m = 4` admits every pair `e₁, e₂ < 4`. Three instances
carry the reduction, and the third needs the second: `ρ(4) ≤ ρ(2)` comes from the pair `(1, 3)`
folded by `ρ(6) = ρ(2)`, and only then does `(1, 2)` give `ρ(3) ≤ ρ(2)`. The three instances are
stated at an arbitrary real coupling; the two orderings drawn from them clamp it at `max β 0`.

DERIVED: in `logConvex_eight_lag_one`, `7` is the extent index `N`, with `N + 1 = 8`; `2` is the
exponent of the square on the left and the lag index on the right; `1` and `0` are lag indices. -/

theorem logConvex_eight_lag_one (β : ℝ) :
    MassGap.wilsonCorrAt 7 β 1 ^ 2 ≤ MassGap.wilsonCorrAt 7 β 0 * MassGap.wilsonCorrAt 7 β 2 := by
  have hh := MassGap.LogConvex.corrClay_log_convex 7 4 (by norm_num) (by norm_num) β
    (e₁ := (0 : Fin 8)) (e₂ := (1 : Fin 8)) (by decide) (by decide)
  have e01 : ((0 : Fin 8) + (1 : Fin 8)) = (1 : Fin 8) := by decide
  have e00 : ((0 : Fin 8) + (0 : Fin 8)) = (0 : Fin 8) := by decide
  have e11 : ((1 : Fin 8) + (1 : Fin 8)) = (2 : Fin 8) := by decide
  rw [e01, e00, e11] at hh
  exact hh

theorem logConvex_eight_lag_four (β : ℝ) :
    MassGap.wilsonCorrAt 7 β 4 ^ 2 ≤ MassGap.wilsonCorrAt 7 β 2 * MassGap.wilsonCorrAt 7 β 6 := by
  have hh := MassGap.LogConvex.corrClay_log_convex 7 4 (by norm_num) (by norm_num) β
    (e₁ := (1 : Fin 8)) (e₂ := (3 : Fin 8)) (by decide) (by decide)
  have e13 : ((1 : Fin 8) + (3 : Fin 8)) = (4 : Fin 8) := by decide
  have e11 : ((1 : Fin 8) + (1 : Fin 8)) = (2 : Fin 8) := by decide
  have e33 : ((3 : Fin 8) + (3 : Fin 8)) = (6 : Fin 8) := by decide
  rw [e13, e11, e33] at hh
  exact hh

theorem logConvex_eight_lag_three (β : ℝ) :
    MassGap.wilsonCorrAt 7 β 3 ^ 2 ≤ MassGap.wilsonCorrAt 7 β 2 * MassGap.wilsonCorrAt 7 β 4 := by
  have hh := MassGap.LogConvex.corrClay_log_convex 7 4 (by norm_num) (by norm_num) β
    (e₁ := (1 : Fin 8)) (e₂ := (2 : Fin 8)) (by decide) (by decide)
  have e12 : ((1 : Fin 8) + (2 : Fin 8)) = (3 : Fin 8) := by decide
  have e11 : ((1 : Fin 8) + (1 : Fin 8)) = (2 : Fin 8) := by decide
  have e22 : ((2 : Fin 8) + (2 : Fin 8)) = (4 : Fin 8) := by decide
  rw [e12, e11, e22] at hh
  exact hh

/-- `ρ(4) ≤ ρ(2)` at extent eight, at the clamped coupling `max β 0`.
`logConvex_eight_lag_four` gives `ρ(4) ^ 2 ≤ ρ(2) * ρ(6)`, `ConfinesEight.sym_eight_two` folds `ρ(6)`
onto `ρ(2)`, and `wilson_reflection_positive_at_even` supplies the nonnegativity of the two values.
Both sides are read at `max β 0`, so the statement holds for every real `β` and says nothing about
the correlation at a negative coupling.

DERIVED: `7` is the extent index `N`, with `N + 1 = 8`; `0` is the clamp in `max β 0`; `4` and `2`
are lag indices. -/
theorem lag_four_le_lag_two (β : ℝ) :
    MassGap.wilsonCorrAt 7 (max β 0) 4 ≤ MassGap.wilsonCorrAt 7 (max β 0) 2 := by
  have hrp := MassGap.wilson_reflection_positive_at_even 7 4 (by norm_num) (by norm_num)
    (le_max_right β (0 : ℝ))
  have h4 := logConvex_eight_lag_four (max β 0)
  rw [MassGap.ConfinesEight.sym_eight_two β] at h4
  nlinarith [h4, hrp.1 4, hrp.1 2]

/-- `ρ(3) ≤ ρ(2)` at extent eight, at the clamped coupling, through `ρ(4) ≤ ρ(2)`.
`logConvex_eight_lag_three` gives `ρ(3) ^ 2 ≤ ρ(2) * ρ(4)`, `lag_four_le_lag_two` replaces `ρ(4)`,
and `wilson_reflection_positive_at_even` supplies nonnegativity at lags `2`, `3` and `4`.

DERIVED: `7` is the extent index `N`, with `N + 1 = 8`; `0` is the clamp in `max β 0`; `3` and `2`
are lag indices. -/
theorem lag_three_le_lag_two_eight (β : ℝ) :
    MassGap.wilsonCorrAt 7 (max β 0) 3 ≤ MassGap.wilsonCorrAt 7 (max β 0) 2 := by
  have hrp := MassGap.wilson_reflection_positive_at_even 7 4 (by norm_num) (by norm_num)
    (le_max_right β (0 : ℝ))
  have h3 := logConvex_eight_lag_three (max β 0)
  have h42 := lag_four_le_lag_two β
  nlinarith [h3, h42, hrp.1 3, hrp.1 2, hrp.1 4]

/-! ## The sufficient condition at extent eight -/

/-- A lag-two ratio below `lagTwoThresholdEight` clears the floor at extent eight.
From `K < lagTwoThresholdEight` and `ρ(2) ≤ K · ρ(0)` at the clamped coupling, the conclusion is
`3 ^ (−1/4) < ApertureRoute.cosAvgEven ConfinesEight.ap8 β`. The hypothesis is read at `max β 0`
while the conclusion is stated at `β` itself, which is unrestricted in sign. The extent-eight
counterpart of `LagTwoSix.confines_extent_six_of_lag_two_ratio`, consuming a weaker hypothesis by
`lagTwoThresholdSix_lt_lagTwoThresholdEight`.

`ConfinesEight.confines_extent_eight_iff` is an equivalence, so the criterion is rewritten rather
than weakened. The substitutions are `logConvex_eight_lag_one` for `ρ(1)`,
`lag_three_le_lag_two_eight` and `lag_four_le_lag_two` for the deep lags; the collapse
`2c·ρ(2) + (2c+√2)·ρ(3) + (1+c)·ρ(4) ≤ aEight·ρ(2)` is `aEight`'s own definition once `ρ(3)` and
`ρ(4)` are under `ρ(2)`. `PlaqVariance.corrClay_zero_pos` supplies `0 < ρ(0)` and
`wilson_reflection_positive_at_even` the nonnegativity of `ρ(1)` and `ρ(2)`.

DERIVED: `7` is the extent index `N`, with `N + 1 = 8`, and the `8` in `ConfinesEight.ap8` is part of
that aperture's name; `0` is the clamp in `max β 0` and the contact lag the ratio is taken relative
to; `2` is the lag the ratio is taken at; `3`, `1` and `4` are the entropy floor `3 ^ (−1/4)` on the
left of the conclusion, base and exponent. -/
theorem confines_extent_eight_of_lag_two_ratio {β K : ℝ} (hK : K < lagTwoThresholdEight)
    (h : MassGap.wilsonCorrAt 7 (max β 0) 2 ≤ K * MassGap.wilsonCorrAt 7 (max β 0) 0) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < MassGap.ApertureRoute.cosAvgEven MassGap.ConfinesEight.ap8 β := by
  rw [MassGap.ConfinesEight.confines_extent_eight_iff β]
  have hrp := MassGap.wilson_reflection_positive_at_even 7 4 (by norm_num) (by norm_num)
    (le_max_right β (0 : ℝ))
  have hc := MassGap.LagTwoBound.floor_bounds
  have hb := bEight_pos
  have ha := aEight_pos
  have hroot := vEight_root
  have hv0 := vEight_pos
  have hpos0 : 0 < MassGap.wilsonCorrAt 7 (max β 0) 0 :=
    MassGap.PlaqVariance.corrClay_zero_pos 7 (max β 0)
  have hlc := logConvex_eight_lag_one (max β 0)
  have h32 := lag_three_le_lag_two_eight β
  have h42 := lag_four_le_lag_two β
  have h1 := hrp.1 1
  have h2 := hrp.1 2
  set r0 : ℝ := MassGap.wilsonCorrAt 7 (max β 0) 0 with hr0
  set r1 : ℝ := MassGap.wilsonCorrAt 7 (max β 0) 1 with hr1
  set r2 : ℝ := MassGap.wilsonCorrAt 7 (max β 0) 2 with hr2
  set r3 : ℝ := MassGap.wilsonCorrAt 7 (max β 0) 3 with hr3
  set r4 : ℝ := MassGap.wilsonCorrAt 7 (max β 0) 4 with hr4
  have hr2lt : r2 < vEight ^ 2 * r0 := by
    have hKr : K * r0 < lagTwoThresholdEight * r0 := mul_lt_mul_of_pos_right hK hpos0
    rw [lagTwoThresholdEight] at hKr
    linarith
  have hstep : r0 * r2 < (vEight * r0) ^ 2 := by
    nlinarith [mul_pos hpos0 (sub_pos.2 hr2lt)]
  have hr1lt : r1 < vEight * r0 := by
    nlinarith [lt_of_le_of_lt hlc hstep, h1, mul_pos hv0 hpos0]
  -- the deep lags collapse onto `ρ(2)` with `aEight`'s own coefficient
  have hcollapse : bEight * r1 + 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) * r2
        + (2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) + Real.sqrt 2) * r3
        + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r4
      ≤ bEight * r1 + aEight * r2 := by
    unfold aEight
    nlinarith [h32, h42, hc.1, Real.sqrt_nonneg 2]
  have hstrict : bEight * r1 + aEight * r2 < bEight * (vEight * r0) + aEight * (vEight ^ 2 * r0) := by
    nlinarith [hr1lt, hr2lt, hb, ha]
  have hval : bEight * (vEight * r0) + aEight * (vEight ^ 2 * r0)
      = (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r0 := by nlinarith [hroot]
  unfold bEight at hcollapse hstrict hval
  linarith

/-- The lag-two obligation at extent eight: one real constant strictly below
`lagTwoThresholdEight` bounding `ρ(2)` by `K · ρ(0)` at every nonnegative coupling. The extent-eight
counterpart of `LagTwoSix.LagTwoRatioSix` — one aperture, one lag, no rate — and the bound the
comparison `lagTwoThresholdSix_lt_lagTwoThresholdEight` makes the largest of the even extents
compared here.

`confines_of_lagTwoRatioEight` consumes it. `exists_cut_lag_two_ratio_eight` gives the same bound,
for every `K > 0`, on an interval `[0, b]` rather than on all of `0 ≤ β`. Any profile whose lag-two
ratio reaches `1` meets no admissible `K`, by `flat_profile_defeats_every_admissible_K`, and the
constant profile of `TailRatio.no_strict_lag_bound_with_contact` is such a profile: it satisfies
nonnegativity, circle symmetry, log-convexity, `ρ(2) ≤ ρ(0)`, and this file's own
`lag_three_le_lag_two_eight` and `lag_four_le_lag_two` with equality.

The `0 ≤ β` guard costs the consumer nothing: `confines_of_lagTwoRatioEight` instantiates it at
`max β 0`.

DERIVED: `0` is the sign condition on the coupling in `0 ≤ β` and, in the last position, the contact
lag the ratio is taken relative to; `7` is the extent index `N` of `ConfinesEight.ap8`, with
`N + 1 = 8 = 2·4`; `2` is the lag the ratio is taken at. The only magnitude is
`lagTwoThresholdEight`, which is a closed form. Nothing here is chosen. -/
def LagTwoRatioEight : Prop :=
  ∃ K : ℝ, K < lagTwoThresholdEight ∧
    ∀ β : ℝ, 0 ≤ β → MassGap.wilsonCorrAt 7 β 2 ≤ K * MassGap.wilsonCorrAt 7 β 0

/-- `LagTwoRatioEight` gives `ApertureRoute.ConfinesAtAnAperture`, with `ConfinesEight.ap8` as the
witness. `ConfinesAtAnAperture` is existential over apertures, so confinement at one aperture
discharges it; `confines_extent_eight_of_lag_two_ratio` supplies that confinement at each coupling,
reading the hypothesis at `max β 0` through `le_max_right`.

DERIVED: no numeral appears in the statement. -/
theorem confines_of_lagTwoRatioEight (h : LagTwoRatioEight) :
    MassGap.ApertureRoute.ConfinesAtAnAperture := by
  obtain ⟨K, hK, hb⟩ := h
  exact ⟨MassGap.ConfinesEight.ap8, fun β =>
    confines_extent_eight_of_lag_two_ratio hK (hb (max β 0) (le_max_right β 0))⟩

/-! ## The strong-coupling arm at extent eight

The extent-eight transcription of `LagTwoBound.exists_cut_lag_two_ratio`. Both inputs are
aperture-generic — `StrongCoupling.corrClay_abs_le_coreConst_mul_rate_pow (N : ℕ)` and
`ContactFloor.corrClay_zero_ge (N : ℕ)` — so only `N` and the `circLag` fact change.

The conclusion is an interval and not the half-line: the cut `b` is where
`β ↦ coreConst·coreRate·e^{128β}` is still under `K·ρ(0)|₀`, and it is obtained from continuity of
that majorant at `0`, intersected with the `b₀` of `StrongArm.exists_strong_arm_cut` on which
`coreRate (16·4) β < 1`. -/

/-- `Moment.circLag (2 : Fin (7 + 1)) = 2`: the lag-two circle distance at extent eight is
`min 2 (8 − 2)`. Closed by `decide` on the finite index type.

DERIVED: `2` is the lag index inside `Fin (7 + 1)` and again the circle distance it evaluates to;
`7` and `1` are the extent index `N` and the offset that makes the index type `Fin 8`. -/
theorem circLag_two_eight : Moment.circLag (2 : Fin (7 + 1)) = 2 := by decide

/-- For every `K > 0` there is a `b > 0` such that the extent-eight lag-two ratio is under `K` on the
whole of `[0, b]`. The quantifier order is `∀ K, ∃ b`, so the cut depends on `K` and shrinks with it.

The transcription of `LagTwoBound.exists_cut_lag_two_ratio` at `N = 7`. The numerator is
`StrongCoupling.corrClay_abs_le_coreConst_mul_rate_pow` at power `k = 1`, admissible because
`circLag_two_eight` gives `circLag 2 = 2` at extent eight as at extent four; the denominator is
`ContactFloor.corrClay_zero_ge`'s `e^{−128β}·ρ(0)|₀ ≤ ρ(0)`. `StrongArm.exists_strong_arm_cut` fixes
a `b₀` with `coreRate (16 * 4) b₀ < 1`, and `b` is `min b₀ (ε / 2)` for an `ε` drawn from continuity
of the majorant at `0`. No numeral is named for `b`, and none could be: `ρ(0)|₀` enters through
`PlaqVariance.corrClay_zero_pos`, which is non-constructive. The touch degree `16 * 4`, the exponent
`128` and the power `1` occur in the proof and not in the statement.

DERIVED: `0` is the sign condition on `K`, the sign condition on `b`, the lower end of the interval
in `0 ≤ β`, and the contact lag in the last position; `7` is the extent index `N`, with `N + 1 = 8`;
`2` is the lag the ratio is taken at. Nothing is chosen. -/
theorem exists_cut_lag_two_ratio_eight (K : ℝ) (hK : 0 < K) :
    ∃ b : ℝ, 0 < b ∧ ∀ β : ℝ, 0 ≤ β → β ≤ b →
      MassGap.wilsonCorrAt 7 β 2 ≤ K * MassGap.wilsonCorrAt 7 β 0 := by
  obtain ⟨b₀, hb₀, hr₀⟩ := MassGap.StrongArm.exists_strong_arm_cut
  set A : ℝ := MassGap.StrongCoupling.coreConst (16 * 4) b₀ with hAdef
  have hA128 : (128 : ℝ) ≤ A := by
    rw [hAdef]; exact MassGap.LagTwoBound.le_coreConst (16 * 4) hb₀.le hr₀
  have hA0 : 0 < A := by linarith
  set D : ℝ := MassGap.WilsonBridge.corrClay (7 + 1) 0 0 with hDdef
  have hD0 : 0 < D := by rw [hDdef]; exact MassGap.PlaqVariance.corrClay_zero_pos 7 0
  have hcont : Continuous
      (fun β : ℝ => A * (MassGap.StrongCoupling.coreRate (16 * 4) β * Real.exp (128 * β))) := by
    have h1 : Continuous (fun β : ℝ => Real.exp (128 * β)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    exact continuous_const.mul ((MassGap.StrongCoupling.continuous_coreRate (16 * 4)).mul h1)
  have hzero : A * (MassGap.StrongCoupling.coreRate (16 * 4) 0 * Real.exp (128 * 0)) < K * D := by
    rw [MassGap.StrongCoupling.coreRate_at_zero]
    have hz : A * (0 * Real.exp (128 * 0)) = 0 := by ring
    rw [hz]
    exact mul_pos hK hD0
  have hev : ∀ᶠ x in nhds (0 : ℝ),
      A * (MassGap.StrongCoupling.coreRate (16 * 4) x * Real.exp (128 * x)) < K * D :=
    hcont.continuousAt.eventually_lt_const hzero
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨min b₀ (ε / 2), lt_min hb₀ (by linarith), ?_⟩
  intro β hβ0 hβb
  have hβb₀ : β ≤ b₀ := le_trans hβb (min_le_left _ _)
  have hβε : β < ε := lt_of_le_of_lt (le_trans hβb (min_le_right _ _)) (by linarith)
  have hf : A * (MassGap.StrongCoupling.coreRate (16 * 4) β * Real.exp (128 * β)) < K * D := by
    refine hball ?_
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hβ0]
    exact hβε
  have hrβ : MassGap.StrongCoupling.coreRate (16 * 4) β
      ≤ MassGap.StrongCoupling.coreRate (16 * 4) b₀ :=
    MassGap.StrongArm.coreRate_mono_beta (16 * 4) hβ0 hβb₀
  have hrβ1 : MassGap.StrongCoupling.coreRate (16 * 4) β < 1 := lt_of_le_of_lt hrβ hr₀
  have hrnn : (0 : ℝ) ≤ MassGap.StrongCoupling.coreRate (16 * 4) β :=
    MassGap.StrongCoupling.coreRate_nonneg (16 * 4) hβ0
  have hAβ : MassGap.StrongCoupling.coreConst (16 * 4) β ≤ A := by
    rw [hAdef]; exact MassGap.StrongArm.coreConst_mono_beta (16 * 4) hβ0 hβb₀ hr₀
  have hbnd := MassGap.StrongCoupling.corrClay_abs_le_coreConst_mul_rate_pow 7 hβ0 hrβ1
    (2 : Fin (7 + 1)) 1 (by rw [circLag_two_eight]; norm_num)
  have hstep : MassGap.wilsonCorrAt 7 β 2 ≤ A * MassGap.StrongCoupling.coreRate (16 * 4) β := by
    rw [MassGap.StrongArm.wilsonCorrAt_eq_corrClay]
    calc MassGap.WilsonBridge.corrClay (7 + 1) β 2
        ≤ |MassGap.WilsonBridge.corrClay (7 + 1) β 2| := le_abs_self _
      _ ≤ MassGap.StrongCoupling.coreConst (16 * 4) β
            * MassGap.StrongCoupling.coreRate (16 * 4) β ^ 1 := hbnd
      _ = MassGap.StrongCoupling.coreConst (16 * 4) β
            * MassGap.StrongCoupling.coreRate (16 * 4) β := by ring
      _ ≤ A * MassGap.StrongCoupling.coreRate (16 * 4) β := mul_le_mul_of_nonneg_right hAβ hrnn
  have hfloor : Real.exp (-(128 * β)) * D ≤ MassGap.wilsonCorrAt 7 β 0 := by
    rw [MassGap.StrongArm.wilsonCorrAt_eq_corrClay, hDdef]
    exact MassGap.ContactFloor.corrClay_zero_ge 7 hβ0
  have hcancel : Real.exp (128 * β) * Real.exp (-(128 * β)) = 1 := by
    rw [← Real.exp_add]; simp
  have hkey : A * MassGap.StrongCoupling.coreRate (16 * 4) β
      ≤ K * (Real.exp (-(128 * β)) * D) := by
    have hmul : (A * (MassGap.StrongCoupling.coreRate (16 * 4) β * Real.exp (128 * β)))
          * Real.exp (-(128 * β))
        ≤ (K * D) * Real.exp (-(128 * β)) :=
      mul_le_mul_of_nonneg_right hf.le (Real.exp_pos _).le
    have hlhs : (A * (MassGap.StrongCoupling.coreRate (16 * 4) β * Real.exp (128 * β)))
          * Real.exp (-(128 * β))
        = A * MassGap.StrongCoupling.coreRate (16 * 4) β := by
      calc (A * (MassGap.StrongCoupling.coreRate (16 * 4) β * Real.exp (128 * β)))
              * Real.exp (-(128 * β))
          = A * MassGap.StrongCoupling.coreRate (16 * 4) β
              * (Real.exp (128 * β) * Real.exp (-(128 * β))) := by ring
        _ = A * MassGap.StrongCoupling.coreRate (16 * 4) β := by rw [hcancel, mul_one]
    have hrhs : (K * D) * Real.exp (-(128 * β)) = K * (Real.exp (-(128 * β)) * D) := by ring
    linarith [hmul, hlhs.symm.le, hlhs.le, hrhs.le, hrhs.symm.le]
  calc MassGap.wilsonCorrAt 7 β 2
      ≤ A * MassGap.StrongCoupling.coreRate (16 * 4) β := hstep
    _ ≤ K * (Real.exp (-(128 * β)) * D) := hkey
    _ ≤ K * MassGap.wilsonCorrAt 7 β 0 := mul_le_mul_of_nonneg_left hfloor hK.le

/-- A constant admissible at extent six is admissible at extent eight: transitivity of `<` through
`lagTwoThresholdSix_lt_lagTwoThresholdEight`. The converse direction is not stated.

DERIVED: no numeral appears in the statement. -/
theorem admissible_at_eight_of_admissible_at_six {K : ℝ}
    (hK : K < MassGap.LagTwoSix.lagTwoThresholdSix) : K < lagTwoThresholdEight :=
  lt_trans hK lagTwoThresholdSix_lt_lagTwoThresholdEight

#print axioms vEight_lt_one
#print axioms lagTwoThresholdEight_lt_one
#print axioms flat_profile_defeats_every_admissible_K
#print axioms lagTwoThresholdEight_sharp
#print axioms logConvex_eight_lag_one
#print axioms logConvex_eight_lag_four
#print axioms logConvex_eight_lag_three
#print axioms lag_four_le_lag_two
#print axioms lag_three_le_lag_two_eight
#print axioms confines_extent_eight_of_lag_two_ratio
#print axioms LagTwoRatioEight
#print axioms circLag_two_eight
#print axioms exists_cut_lag_two_ratio_eight
#print axioms confines_of_lagTwoRatioEight
#print axioms admissible_at_eight_of_admissible_at_six

#print axioms bEight
#print axioms aEight
#print axioms sqrt_two_bounds
#print axioms aEight_pos
#print axioms bEight_pos
#print axioms disc_pos
#print axioms vEight
#print axioms lagTwoThresholdEight
#print axioms vEight_pos
#print axioms vEight_root
#print axioms disc_gt
#print axioms disc_lt
#print axioms sqrt_disc_gt
#print axioms sqrt_disc_lt
#print axioms vEight_gt
#print axioms vEight_lt
#print axioms lagTwoThresholdEight_gt
#print axioms lagTwoThresholdEight_lt
#print axioms lagTwoThresholdSix_lt_lagTwoThresholdEight

end MassGap.LagTwoEight
