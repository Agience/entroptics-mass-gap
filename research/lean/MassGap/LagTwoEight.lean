import Mathlib
import MassGap.LagTwoSix
import MassGap.ConfinesEight

/-!
# MassGap.LagTwoEight — the lag-two threshold at extent eight, where the relief PEAKS

`LagTwoSix`'s header states the trend across even extents and says where it turns:

>     extent  4 → 0.0186240      extent 10 → 0.0302593
>     extent  6 → 0.0337959      extent 12 → 0.0250940
>     extent  8 → 0.0354567
>
> **The relief peaks at extent eight and then reverses.** … Only the extent-four and extent-six
> entries are machine-checked, here and in `LagTwoBound`. The other three are stated as what the same
> construction yields, not as theorems.

This file machine-checks the peak entry. `lagTwoThresholdEight` is the extent-eight counterpart of
`LagTwoBound.lagTwoThreshold` and `LagTwoSix.lagTwoThresholdSix`, in the SAME currency — a bound on
`ρ(2)/ρ(0)` — and `lagTwoThresholdSix_lt_lagTwoThresholdEight` proves the peak claim itself, so that
the best aperture is a theorem rather than a table entry.

## The criterion at even extent `2m`, and its reduction at `m = 4`

`LagTwoSix`'s header gives the general form, which is `ConfinesSharp.confines_extent_four_iff` at
`m = 2` and `confines_extent_six_iff` at `m = 3`:

    ∑_{d=1}^{m−1} 2(c − cos(πd/m))·ρ(d) + (1+c)·ρ(m) < (1−c)·ρ(0),      c = 3^{−1/4}

At `m = 4` the cosines are `cos(π/4) = √2/2`, `cos(2π/4) = 0` and `cos(3π/4) = −√2/2`, so the
coefficients are EXACT in `c` and `√2` with no further transcendental content:

* on `ρ(1)`:  `2(c − √2/2) = 2c − √2`                                    — `bEight`
* on the deep lags together, each bounded by `ρ(2)` on the log-convexity cone:
  `2c + 2(c + √2/2) + (1 + c) = 5c + √2 + 1`                            — `aEight`

Reducing against `LogConvex.corrClay_log_convex`'s cone exactly as `LagTwoSix` does — `ρ(1) = v`,
every deeper lag at `ρ(2) = v²` — gives one quadratic in `v = √(ρ(2)/ρ(0))`:

    aEight·v² + bEight·v = 1 − c

`vEight` is its positive root and `lagTwoThresholdEight` is `vEight²`.

## Why extent eight and not further

`bEight = 2c − √2 = 0.10545781` is POSITIVE but small, and it is the last extent at which it is:
`2(c − cos(π/m))` falls with `m` and turns negative at `m = 5`. Meanwhile `aEight` grows
monotonically, `1.76 → 4.28 → 6.21 → 7.94 → 9.57` across extents `4, 6, 8, 10, 12`. Past `m = 4` the
growth of the deep-lag coefficient beats the shrinking of the `ρ(1)` term and the threshold falls
again.

**The sign change buys nothing**, which is why the reversal is real rather than an artifact of the
reduction. A negative coefficient on `ρ(1)` wants `ρ(1)` LARGE, and the cone bounds an odd lag only
from ABOVE — every right-hand lag `corrClay_log_convex` produces is `2e`, hence even — so `ρ(1) → 0`
stays admissible (`MomentShape.odd_scaling_admissible`) and dropping the term is the exact worst case.

## THE ROUTE THIS FILE COMPLETES, and it does not go through `LawAbove`

`ApertureRoute.ConfinesAtAnAperture` is `∃ a : EvenAp, ∀ β, c < cosAvgEven a β` — EXISTENTIAL over
apertures — so confinement at ONE aperture discharges it and thence the flagship through
`flagship_of_confinement_at_an_aperture`. That is the short route, and `confines_of_lagTwoRatioEight`
below carries it at the best aperture:

    LagTwoRatioEight  =  ∃ K < 0.0354567, ∀ β ≥ 0, ρ(2) ≤ K·ρ(0)     [extent eight only]
       ⟹ ConfinesAtAnAperture ⟹ the flagship

**`NonnegArm.LawAbove` is the remaining obligation on the TWO-ARM SUBSTRATE route, not on this one.**
Its constant must be uniform in EVERY aperture, at every lag, with a quartic rate; `LagTwoRatioEight`
is one aperture, one lag, no rate, and the largest bar of the five even extents. The two are not
comparable obligations and the shorter one is strictly weaker.

## What this does NOT claim

* It does **not** discharge `LagTwoRatioEight` at any coupling. That is B5, and it is open.
  **The SHAPE facts cannot close it either**, and that was checked rather than assumed: the constant
  profile conforms to every coupling-uniform fact — including this file's own
  `lag_three_le_lag_two_eight` and `lag_four_le_lag_two`, both with EQUALITY — and its lag-two ratio
  is exactly `1`, which `lagTwoThresholdEight_lt_one` puts above the threshold
  (`flat_profile_defeats_every_admissible_K`). So what closes `LagTwoRatioEight` must come from the
  DYNAMICS, exactly as `LagTwoSix` says of its own obligation.
* The obstruction above is NOT the one `ClayAssembly.flat_profile_admits_no_uniform_quartic_constant`
  raises against `LawAbove`. That one needs the aperture to GROW, forcing `C ≥ m⁴` at extent `2m`;
  this one is a single fixed violation at one aperture. Same witness, different arithmetic — and only
  the second applies to a single-aperture obligation.
* The extent-eight threshold IS proved sharp (`lagTwoThresholdEight_sharp`), but sharp means best
  possible from the LOG-CONVEXITY CONE, not best possible from everything the tree proves — the same
  scope `LagTwoSix.lagTwoThresholdSix_sharp` has.

Foundational footprint only (`#print axioms` on every declaration).
Build: `python research/code/lean_build.py build MassGap.LagTwoEight`.
-/

namespace MassGap.LagTwoEight

/-- The `ρ(1)` coefficient of the extent-eight criterion: `2(c − cos(π/4)) = 2c − √2`.

DERIVED: `2` is the criterion's own multiplicity, `cos(π/4) = √2/2` is exact, and `c = 3^{−1/4}` is
the entropy floor carried in by name from `Floor.lean`. Nothing is chosen. -/
noncomputable def bEight : ℝ := 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - Real.sqrt 2

/-- The deep-lag coefficient, all of `ρ(2)`, `ρ(3)` and `ρ(4)` collected on the cone:
`2(c − cos(π/2)) + 2(c − cos(3π/4)) + (1 + c) = 2c + (2c + √2) + (1 + c) = 5c + √2 + 1`.

DERIVED: every literal is a criterion coefficient at `m = 4`. `cos(π/2) = 0` and
`cos(3π/4) = −√2/2` are exact, the `1 + c` is the self-paired lag `ρ(m)`'s own coefficient, and the
`5` is `2 + 2 + 1` collected. No magnitude is chosen. -/
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

/-- `bEight` is POSITIVE, and this is the fact that makes extent eight the peak rather than one more
step down a monotone trend: at `m = 5` the same coefficient is negative. -/
theorem bEight_pos : 0 < bEight := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have hs := sqrt_two_bounds
  unfold bEight
  linarith [hc.1, hs.2]

/-- The discriminant `bEight² + 4·aEight·(1−c)`, positive. -/
theorem disc_pos :
    0 < bEight ^ 2 + 4 * aEight * (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have ha := aEight_pos
  have hb := bEight_pos
  nlinarith [hc.1, hc.2, ha, hb, sq_nonneg bEight]

/-- **The positive root of the extent-eight reduced criterion**, in `v = √(ρ(2)/ρ(0))`.

DERIVED: the quadratic formula applied to `aEight·v² + bEight·v = 1 − c`, with no numeral of its own
beyond the formula's `2` and `4`. -/
noncomputable def vEight : ℝ :=
  (Real.sqrt (bEight ^ 2 + 4 * aEight * (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))) - bEight) / (2 * aEight)

/-- **THE THRESHOLD ON THE LAG-TWO RATIO AT EXTENT EIGHT** — `vEight` squared, because the criterion
is a bound on `√(ρ(2)/ρ(0))` while the threshold is stated on the RATIO. The extent-eight counterpart
of `LagTwoBound.lagTwoThreshold` and `LagTwoSix.lagTwoThresholdSix`.

DERIVED: the `2` is the squaring and nothing else. -/
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

/-- **THE ROOT IDENTITY.** `aEight·vEight² + bEight·vEight = 1 − c`: the threshold is exactly the
reduced criterion's own root and not a cut taken below it. -/
theorem vEight_root :
    aEight * vEight ^ 2 + bEight * vEight = 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
  have ha := aEight_pos
  have hd := disc_pos
  have hane : (4 : ℝ) * aEight ≠ 0 := ne_of_gt (by linarith)
  have hsq : Real.sqrt (bEight ^ 2 + 4 * aEight * (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))) ^ 2
      = bEight ^ 2 + 4 * aEight * (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) :=
    Real.sq_sqrt hd.le
  -- The `(D − b)² + 2b(D − b) = D² − b²` collapse, done SYMBOLICALLY and then closed by the
  -- discriminant identity -- the shape `LagTwoSix.vSix_root` uses. Handing the whole thing to
  -- `nlinarith` instead leaves it to substitute `(√disc)²` inside a polynomial, and it does not.
  have hkey : ∀ D : ℝ, aEight * ((D - bEight) / (2 * aEight)) ^ 2
        + bEight * ((D - bEight) / (2 * aEight))
      = (D ^ 2 - bEight ^ 2) / (4 * aEight) := by
    intro D
    have : aEight ≠ 0 := ne_of_gt ha
    field_simp
    ring
  rw [vEight, hkey, hsq, div_eq_iff hane]
  ring

/-! ### The bracket, built the way `LagTwoSix` builds its own

`v` is bounded FIRST, from the closed form through `lt_div_iff₀`, and only then squared. Reading the
bracket off the root identity instead leaves `nlinarith` to solve a quadratic in three unknowns
(`c`, `√2`, `v`) and it does not. -/

/-- The discriminant, bracketed. Every input is a bracket on `c` or on `√2`. -/
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

/-- `vEight` bracketed. CHOSEN, and both rounded AWAY from the claim
`lagTwoThresholdSix < lagTwoThresholdEight`: `0.1882` is below `vEight = 0.18829961…` and `0.18831`
is above it, so neither rounding can manufacture the strict inequality. -/
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

/-- The threshold bracketed for a reader, between `0.0354` and `0.0355`. The decision is made by the
closed form; these rationals decide nothing, and each rounds AWAY from the claim it is used in. -/
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

/-- **THE PEAK, AS A THEOREM.** Extent eight relieves the lag-two obligation more than extent six
does. `LagTwoSix`'s header states the trend; this is the one comparison in it that decides which
aperture to prefer, and it is now machine-checked rather than tabulated. -/
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

/-- `vEight < 1`, from the root identity alone: `aEight·vEight² < 1 − c < 1` and `aEight > 6`. -/
theorem vEight_lt_one : vEight < 1 := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have hs := sqrt_two_bounds
  have hroot := vEight_root
  have hv0 := vEight_pos
  have hb := bEight_pos
  have ha : (6 : ℝ) < aEight := by unfold aEight; linarith [hc.1, hs.1]
  nlinarith [hroot, hv0, hb, ha, hc.1, hc.2]

/-- **THE THRESHOLD IS THE BEST ONE THE PROVED SHAPE FACTS CARRY AT EXTENT EIGHT** — it is not a cut
with margin left in it.

The profile `ρ = (1, vEight, vEight², vEight², vEight²)`, extended by circle symmetry to
`ρ(5) = ρ(3)`, `ρ(6) = ρ(2)`, `ρ(7) = ρ(1)`, satisfies the log-convexity instances available at
half-extent four and sits at `ρ(2) = lagTwoThresholdEight · ρ(0)` exactly, where `vEight_root` puts
the criterion at EQUALITY and hence not strictly below. So no constant above `lagTwoThresholdEight`
is carried by this reduction.

**The equality is exact and is the point.** On this profile the criterion's left side is
`bEight·vEight + aEight·vEight²`, which `vEight_root` says is `1 − c` — the right side — so the strict
`<` fails by nothing at all. The extent-six counterpart is `LagTwoSix.lagTwoThresholdSix_sharp` and
this is the same argument at `m = 4`.

DERIVED: no numeral. The five components are `1`, `vEight`, `vEight²`, `vEight²`, `vEight²`; the
exponent `2` is the square in the log-convexity statement and in `lagTwoThresholdEight = vEight ^ 2`.
The criterion's coefficients are `ConfinesEight.confines_extent_eight_iff`'s own. -/
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

/-- **THE THRESHOLD IS FAR UNDER ONE**, which is what makes the constant profile defeat it.
`lagTwoThresholdEight = vEight²` and `vEight < 1`. -/
theorem lagTwoThresholdEight_lt_one : lagTwoThresholdEight < 1 := by
  have hv0 := vEight_pos
  have hv1 := vEight_lt_one
  unfold lagTwoThresholdEight
  nlinarith [hv0, hv1]

/-- **THE CONSTANT PROFILE DEFEATS EVERY ADMISSIBLE `K`.** Its lag-two ratio is exactly `1` and the
threshold is under one, so no `K < lagTwoThresholdEight` can bound it.

This is `TailRatio.no_strict_lag_bound_with_contact`'s witness read against THIS extent's threshold.
The profile conforms to every coupling-uniform fact the tree proves — including this file's
`lag_three_le_lag_two_eight` and `lag_four_le_lag_two`, both with equality — so the shape facts
cannot close `LagTwoRatioEight` and what does must come from the dynamics. -/
theorem flat_profile_defeats_every_admissible_K :
    ∀ K : ℝ, K < lagTwoThresholdEight → ¬ ((1 : ℝ) ≤ K * 1) := by
  intro K hK hcon
  have := lagTwoThresholdEight_lt_one
  linarith

/-! ## The shape substitutions at half-extent four

`LogConvex.corrClay_log_convex` at `Nap = 7`, `m = 4` admits every pair `e₁, e₂ < 4`. Three instances
carry the reduction, and the third needs the second: `ρ(4) ≤ ρ(2)` comes from `(1,3)` folded by
`ρ(6) = ρ(2)`, and only then does `(1,2)` give `ρ(3) ≤ ρ(2)`. -/

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

/-- **THE ANTIPODAL LAG IS BELOW THE LAG-TWO VALUE AT EXTENT EIGHT**, `ρ(4) ≤ ρ(2)`. -/
theorem lag_four_le_lag_two (β : ℝ) :
    MassGap.wilsonCorrAt 7 (max β 0) 4 ≤ MassGap.wilsonCorrAt 7 (max β 0) 2 := by
  have hrp := MassGap.wilson_reflection_positive_at_even 7 4 (by norm_num) (by norm_num)
    (le_max_right β (0 : ℝ))
  have h4 := logConvex_eight_lag_four (max β 0)
  rw [MassGap.ConfinesEight.sym_eight_two β] at h4
  nlinarith [h4, hrp.1 4, hrp.1 2]

/-- **AND SO IS THE LAG-THREE VALUE**, `ρ(3) ≤ ρ(2)`, through `ρ(4) ≤ ρ(2)`. -/
theorem lag_three_le_lag_two_eight (β : ℝ) :
    MassGap.wilsonCorrAt 7 (max β 0) 3 ≤ MassGap.wilsonCorrAt 7 (max β 0) 2 := by
  have hrp := MassGap.wilson_reflection_positive_at_even 7 4 (by norm_num) (by norm_num)
    (le_max_right β (0 : ℝ))
  have h3 := logConvex_eight_lag_three (max β 0)
  have h42 := lag_four_le_lag_two β
  nlinarith [h3, h42, hrp.1 3, hrp.1 2, hrp.1 4]

/-! ## The sufficient condition at extent eight -/

/-- **A LAG-TWO RATIO BELOW `lagTwoThresholdEight` CLEARS THE FLOOR AT EXTENT EIGHT.**

The extent-eight counterpart of `LagTwoSix.confines_extent_six_of_lag_two_ratio`, consuming a
strictly weaker hypothesis by `lagTwoThresholdSix_lt_lagTwoThresholdEight`.

Nothing is spent that is not proved: `ConfinesEight.confines_extent_eight_iff` is an EQUIVALENCE, and
the three substitutions are `logConvex_eight_lag_one`, `lag_three_le_lag_two_eight` and
`lag_four_le_lag_two`. The collapse is `2c·ρ(2) + (2c+√2)ρ(3) + (1+c)ρ(4) ≤ aEight·ρ(2)`, which is
`aEight`'s own definition once `ρ(3)` and `ρ(4)` are under `ρ(2)`. -/
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

/-- **THE REMAINING OBLIGATION AT EXTENT EIGHT.** One real constant strictly below
`lagTwoThresholdEight`, bounding the lag-two ratio at every NONNEGATIVE coupling. The extent-eight
counterpart of `LagTwoSix.LagTwoRatioSix`, and the weakest form of B5 this tree carries: ONE aperture,
ONE lag, no rate, and the largest bar of the five even extents.

OPEN. Nothing in this tree proves it, and the shape facts cannot — the SAME no-go that applies at
extent six applies here, and it is worth being exact about why, because the obstructions to
`NonnegArm.LawAbove` and the obstruction to this are different arguments that happen to share a
witness.

`TailRatio.no_strict_lag_bound_with_contact`'s witness is the CONSTANT profile. It conforms to
nonnegativity, circle symmetry, log-convexity and `ρ(2) ≤ ρ(0)`, at extent eight exactly as at extent
six, and it also meets this file's own `lag_three_le_lag_two_eight` and `lag_four_le_lag_two` with
equality. Its lag-two ratio is exactly `1`, and `lagTwoThresholdEight_lt_one` puts the threshold far
under one — so every admissible `K` is defeated. **What closes `LagTwoRatioEight` must come from the
dynamics**, not from the shape.

That is NOT the flat-profile argument against `LawAbove`
(`ClayAssembly.flat_profile_admits_no_uniform_quartic_constant`), which turns on `C` having to exceed
`m⁴` at extent `2m` and so needs the aperture to grow. Here the refutation is a single fixed
violation at one aperture, `1 > 0.0354567`. Same profile, different arithmetic, and the second does
not depend on aperture-uniformity at all.

The negative half-line is free: `EvenAperture.readEven` clamps at `max β 0`, so the hypothesis is only
ever read at a nonnegative coupling.

DERIVED: `7` is `ConfinesEight.ap8`'s extent index `N`, with `N + 1 = 8 = 2·4`; `2` and `0` are lag
indices, the lag the ratio is taken at and the contact lag it is taken relative to. The only magnitude
is `lagTwoThresholdEight`, which is a closed form. Nothing here is chosen. -/
def LagTwoRatioEight : Prop :=
  ∃ K : ℝ, K < lagTwoThresholdEight ∧
    ∀ β : ℝ, 0 ≤ β → MassGap.wilsonCorrAt 7 β 2 ≤ K * MassGap.wilsonCorrAt 7 β 0

/-- **THE REDUCTION.** `LagTwoRatioEight` gives `ApertureRoute.ConfinesAtAnAperture` outright, with
`ConfinesEight.ap8` as the witness — and thence the flagship through
`ApertureRoute.flagship_of_confinement_at_an_aperture`.

`ConfinesAtAnAperture` is EXISTENTIAL over apertures, so confinement at ONE aperture discharges it.
That is why this route does not need `NonnegArm.LawAbove`, whose constant must be uniform in EVERY
aperture, at every lag, with a quartic rate. This hypothesis is one aperture, one lag, no rate. -/
theorem confines_of_lagTwoRatioEight (h : LagTwoRatioEight) :
    MassGap.ApertureRoute.ConfinesAtAnAperture := by
  obtain ⟨K, hK, hb⟩ := h
  exact ⟨MassGap.ConfinesEight.ap8, fun β =>
    confines_extent_eight_of_lag_two_ratio hK (hb (max β 0) (le_max_right β 0))⟩

/-! ## The strong-coupling arm at extent eight — the first DYNAMICAL brick

`flat_profile_defeats_every_admissible_K` says the shape facts cannot close `LagTwoRatioEight`. What
follows is what the dynamics do supply, and it is the extent-eight transcription of
`LagTwoBound.exists_cut_lag_two_ratio`. Both inputs it runs on are aperture-GENERIC —
`StrongCoupling.corrClay_abs_le_coreConst_mul_rate_pow (N : ℕ)` and
`ContactFloor.corrClay_zero_ge (N : ℕ)` — so only `N` and the `circLag` fact change.

**It reaches an interval and not the half-line.** The cut `b` is where
`β ↦ coreConst·coreRate·e^{128β}` is still under `K·ρ(0)|₀`, and `coreRate (16·4) β < 1` alone caps it
at `2.936e−5` (the same number the substrate route's split point has, and for the same reason: the
binding factor is the per-plaquette activity `e^{2β}−1`). So this is the first brick of
`LagTwoRatioEight`, not the whole of it — the obligation is `∀ β ≥ 0` and this is `β ∈ [0, b]`. -/

/-- `circLag (2 : Fin 8) = 2` — the lag-two circle distance at extent eight, `min 2 (8−2)`. -/
theorem circLag_two_eight : Moment.circLag (2 : Fin (7 + 1)) = 2 := by decide

/-- **THE STRONG-COUPLING CUT AT EXTENT EIGHT.** For EVERY `K > 0` there is an interval `[0, b]` on
which the extent-eight lag-two ratio is under `K`.

The transcription of `LagTwoBound.exists_cut_lag_two_ratio` at `N = 7`. The numerator is
`corrClay_abs_le_coreConst_mul_rate_pow` at `k = 1`, admissible because `circLag 2 = 2` at extent
eight as at extent four; the denominator is `ContactFloor.corrClay_zero_ge`'s
`e^{−128β}·ρ(0)|₀ ≤ ρ(0)`. No numeral is named for `b`, and none could be: `ρ(0)|₀` enters through
`PlaqVariance.corrClay_zero_pos`, which is non-constructive.

DERIVED: `16 * 4` is `StrongCoupling`'s touch degree at `dim = 4`, `128 = 2·64` is
`ContactFloor.corrClay_zero_ge`'s own exponent, `1` is the power `k` admitted by `circLag 2 = 2`, and
`2`, `0` are lag indices. Nothing is chosen. -/
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

/-- **A CONSTANT ADMISSIBLE AT EXTENT SIX IS ADMISSIBLE AT EXTENT EIGHT.** The direction check on
`lagTwoThresholdSix_lt_lagTwoThresholdEight`. -/
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
