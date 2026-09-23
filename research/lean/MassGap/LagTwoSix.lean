import MassGap.ConfinesSharp
import MassGap.LagTwoBound

/-!
# MassGap.LagTwoSix — the lag-two threshold at six lags

`ApertureRoute.ConfinesAtAnAperture` is existential in the aperture, and `EvenAperture.EvenAp` admits
every even extent at least four. This module works at six, where `wilsonCorrAt 5` has lag index type
`Fin 6`, and produces a threshold on the lag-two ratio `ρ(2)/ρ(0)` in the same currency as
`LagTwoBound.lagTwoThreshold` at four.

## The reduction

`ConfinesSharp.confines_extent_six_iff` states the criterion as

    (2c−1)·ρ(1) + (1+2c)·ρ(2) + (1+c)·ρ(3) < (1−c)·ρ(0),     c = 3^{−1/4},

with every coefficient positive (`ConfinesSharp.two_c_sub_one_pos` for the first), so each
non-contact lag needs an upper bound and none needs a lower one.

Two instances of `LogConvex.corrClay_log_convex` at half-extent `m = 3` supply those bounds.
`logConvex_six_lag_one` is `(e₁,e₂) = (0,1)`, giving `ρ(1)² ≤ ρ(0)ρ(2)`; `logConvex_six_lag_three` is
`(1,2)`, giving `ρ(3)² ≤ ρ(2)ρ(4)`, which `lag_three_le_lag_two` turns into `ρ(3) ≤ ρ(2)` using
`ConfinesSharp.sym_six_two` to fold lag `4` onto lag `2`. The second pair is unavailable at four,
where `m = 2` leaves `(0,1)` as the only non-diagonal choice.

Substituting both and writing `v = √(ρ(2)/ρ(0))` gives

    (2 + 3c)·v² + (2c − 1)·v − (1 − c) < 0,

whose positive root is `vSix` (`vSix_root`, `vSix_pos`, `vSix_lt_one`), and the threshold on the
ratio is `lagTwoThresholdSix = vSix ^ 2`.

## What is proved

* `lagTwoThresholdSix_gt` — the threshold exceeds `0.0337`, and
  `lagTwoThreshold_lt_lagTwoThresholdSix` composes that with `LagTwoBound.lagTwoThreshold_lt` to give
  the strict inequality between the two closed forms. `admissible_at_six_of_admissible_at_four` is
  the transitivity consequence.
* `confines_extent_six_of_lag_two_ratio` — a lag-two ratio bounded by any `K` strictly below the
  threshold gives the criterion at six lags.
* `lagTwoThresholdSix_sharp` — a profile satisfying every non-diagonal log-convexity instance
  available at half-extent three, sitting at exactly the threshold, and failing the criterion. So no
  larger constant is carried by this reduction and the strict `<` cannot be weakened to `≤`.
* `LagTwoRatioSix`, `confines_of_lagTwoRatioSix` — the hypothesis named as a `Prop`, and the
  reduction of `ApertureRoute.ConfinesAtAnAperture` to it with `ConfinesZero.ap6` as witness.
* `circLag_two_six`, `exists_cut_lag_two_ratio_six` — for every `K > 0` an interval `[0, b]` on which
  the lag-two ratio is under `K`.

## Scope

The comparison is between two constants. `wilsonCorrAt 3` and `wilsonCorrAt 5` are different
functions and no statement here relates their values, so nothing transports a bound from one extent
to the other; `admissible_at_six_of_admissible_at_four` compares admissible constants, not bounds.

No statement bounds `ρ(2)/ρ(0)` at either extent without a hypothesis. `LagTwoRatioSix` asks for one
`K < lagTwoThresholdSix` valid at every `β ≥ 0`; `exists_cut_lag_two_ratio_six` gives every `K > 0`
but only on an interval `[0, b]` whose `b` depends on `K`.

Build: `python research/code/lean_build.py build MassGap.LagTwoSix`.
-/

namespace MassGap.LagTwoSix

open MassGap MassGap.EvenAperture MassGap.ApertureRoute MassGap.ConfinesZero

/-! ## 1. The two log-convexity instances available at half-extent three

DERIVED throughout this section: `5` is the `N` of `wilsonCorrAt N`, with `N + 1 = 6 = 2 * 3`, which
is `ConfinesZero.ap6`'s extent; `3` is the half-extent `m`, read off
`LogConvex.corrClay_log_convex`'s hypothesis `Nap + 1 = 2 * m`; the lag literals `0, 1, 2, 3, 4` are
index values in `Fin 6`, not magnitudes; and each exponent `2` is the square of the log-convexity
inequality. -/

/-- `wilsonCorrAt 5 β 1 ^ 2 ≤ wilsonCorrAt 5 β 0 * wilsonCorrAt 5 β 2`, at every real `β`.
`LogConvex.corrClay_log_convex` at `N = 5`, `m = 3`, `(e₁, e₂) = (0, 1)`, with the three `Fin 6` sums
`0+1`, `0+0` and `1+1` evaluated by `decide`.

Both indices are below the half-extent `3`. This is the same pair that is the only non-diagonal one
available at four lags.

DERIVED: `5` is the `N` of `wilsonCorrAt N` and `3` the half-extent supplied to
`corrClay_log_convex`; the lag literals `0`, `1`, `2` index `Fin 6`, and the exponent `2` is the
square of the log-convexity inequality. -/
theorem logConvex_six_lag_one (β : ℝ) :
    MassGap.wilsonCorrAt 5 β 1 ^ 2
      ≤ MassGap.wilsonCorrAt 5 β 0 * MassGap.wilsonCorrAt 5 β 2 := by
  have hh := MassGap.LogConvex.corrClay_log_convex 5 3 (by norm_num) (by norm_num) β
    (e₁ := (0 : Fin 6)) (e₂ := (1 : Fin 6)) (by decide) (by decide)
  have e01 : ((0 : Fin 6) + (1 : Fin 6)) = (1 : Fin 6) := by decide
  have e00 : ((0 : Fin 6) + (0 : Fin 6)) = (0 : Fin 6) := by decide
  have e11 : ((1 : Fin 6) + (1 : Fin 6)) = (2 : Fin 6) := by decide
  rw [e01, e00, e11] at hh
  exact hh

/-- `wilsonCorrAt 5 β 3 ^ 2 ≤ wilsonCorrAt 5 β 2 * wilsonCorrAt 5 β 4`, at every real `β`.
`LogConvex.corrClay_log_convex` at `(e₁, e₂) = (1, 2)`, with `1+2`, `1+1` and `2+2` evaluated in
`Fin 6`.

Both indices are below the half-extent `3`. Unavailable at four lags, where `m = 2` and `e₂ = 2` is
not below it — which is the one input `lag_three_le_lag_two` has that the extent-four reduction does
not.

DERIVED: `5` is the `N` of `wilsonCorrAt N` and `3` the half-extent; the lag literals `2`, `3`, `4`
index `Fin 6`, and the exponent `2` is the square of the log-convexity inequality. -/
theorem logConvex_six_lag_three (β : ℝ) :
    MassGap.wilsonCorrAt 5 β 3 ^ 2
      ≤ MassGap.wilsonCorrAt 5 β 2 * MassGap.wilsonCorrAt 5 β 4 := by
  have hh := MassGap.LogConvex.corrClay_log_convex 5 3 (by norm_num) (by norm_num) β
    (e₁ := (1 : Fin 6)) (e₂ := (2 : Fin 6)) (by decide) (by decide)
  have e12 : ((1 : Fin 6) + (2 : Fin 6)) = (3 : Fin 6) := by decide
  have e11 : ((1 : Fin 6) + (1 : Fin 6)) = (2 : Fin 6) := by decide
  have e22 : ((2 : Fin 6) + (2 : Fin 6)) = (4 : Fin 6) := by decide
  rw [e12, e11, e22] at hh
  exact hh

/-- `wilsonCorrAt 5 (max β 0) 3 ≤ wilsonCorrAt 5 (max β 0) 2`, at every real `β`.
`logConvex_six_lag_three` with `ConfinesSharp.sym_six_two` folding lag `4` onto lag `2` reads
`ρ(3)² ≤ ρ(2)²`; both values are nonnegative by
`Complete.wilson_reflection_positive_at_even`, so `nlinarith` descends to the values themselves.

At six lags the antipodal lag is `3` and lag `2` is distinct from it, which is what makes this a
relation between two different values; at four lags the antipodal lag is lag `2` itself and there is
no analogue.

DERIVED: `5` is the `N` of `wilsonCorrAt N` and `3` the half-extent passed to
`wilson_reflection_positive_at_even`; `0` is the lower clamp on the coupling; the lag literals `2`
and `3` index `Fin 6`, `3` being the antipodal lag at six. -/
theorem lag_three_le_lag_two (β : ℝ) :
    MassGap.wilsonCorrAt 5 (max β 0) 3 ≤ MassGap.wilsonCorrAt 5 (max β 0) 2 := by
  have hrp := MassGap.wilson_reflection_positive_at_even 5 3 (by norm_num) (by norm_num)
    (le_max_right β (0 : ℝ))
  have h3 := logConvex_six_lag_three (max β 0)
  rw [MassGap.ConfinesSharp.sym_six_two β] at h3
  nlinarith [h3, hrp.1 3, hrp.1 2]

/-! ## 2. The extent-six threshold on the lag-two ratio

DERIVED, as `LagTwoBound.lagTwoThreshold`'s note is for extent four. Substituting
`ρ(1) ≤ √(ρ(0)ρ(2))` and `ρ(3) ≤ ρ(2)` into `ConfinesSharp.confines_extent_six_iff` and writing
`v = √(ρ(2)/ρ(0))` turns the criterion into

    (2 + 3c)·v² + (2c − 1)·v − (1 − c) < 0.

Its discriminant is `(2c−1)² + 4(2+3c)(1−c) = 9 − 8c²` — a `ring` identity, not a computed number —
so the positive root is `vSix` and the threshold on the RATIO `v²` is `vSix²`. Every numeral in the
two definitions below is one of those coefficients: `2c−1`, `1+2c` and `1+c` are
`ConfinesSharp.confines_extent_six_iff`'s own, `2 + 3c = (1+2c) + (1+c)` is the collapse `ρ(3) ≤ ρ(2)`
performs, `9` and `8` are the discriminant's, and the outer `2` in the denominator and the outer
square are the quadratic formula's. Nothing is chosen. -/

/-- The positive root of the reduced quadratic, in the variable `v = √(ρ(2)/ρ(0))`:

    vSix = (√(9 − 8c²) − (2c − 1)) / (2(2 + 3c)),   c = 3^{−1/4}.

A closed form with no parameter. `vSix_root` is the identity that makes it a root, `vSix_pos` and
`vSix_lt_one` bracket it.

DERIVED: every literal is a coefficient of `ConfinesSharp.confines_extent_six_iff` or of the
quadratic formula applied to it, and none is chosen. `2c − 1` is the criterion's own coefficient on
`ρ(1)`, and `2 + 3c = (1 + 2c) + (1 + c)` is what its coefficients on `ρ(2)` and `ρ(3)` collapse to
once `lag_three_le_lag_two` replaces `ρ(3)` by `ρ(2)`. `9` and `8` are the discriminant
`(2c−1)² + 4(2+3c)(1−c) = 9 − 8c²`, a `ring` identity rather than a computed number, and the
exponent `2` there squares `c`. The outer `2` in the denominator is the quadratic formula's. `3` is
the base of `c` and the exponent `-(1)/4` its exponent, so the `1` and `4` at each of `c`'s four
occurrences are that one exponent, carried in by name from the floor constant. -/
noncomputable def vSix : ℝ :=
  (Real.sqrt (9 - 8 * ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2) - (2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1))
    / (2 * (2 + 3 * (3 : ℝ) ^ (-(1 : ℝ) / 4)))

/-- `vSix ^ 2`: the threshold on the ratio `ρ(2)/ρ(0)` at six lags, in the same currency as
`LagTwoBound.lagTwoThreshold` at four.

Sufficient by `confines_extent_six_of_lag_two_ratio`. `lagTwoThresholdSix_sharp` exhibits a profile
meeting every log-convexity instance available at half-extent three, sitting at exactly this ratio,
and failing the criterion, so this reduction carries no larger constant.

DERIVED: `2` is the squaring, because `vSix` is the root in `v = √(ρ(2)/ρ(0))` while the criterion is
stated on the ratio. Every other constant is `vSix`'s. No numeral here is a measured level. -/
noncomputable def lagTwoThresholdSix : ℝ := vSix ^ 2

/-- `0 < 9 - 8c²` at `c = 3^{−1/4}`, so the discriminant has a real square root. `linarith` from the
upper half of `LagTwoBound.floor_sq_bounds`, the numeric bracket on `c²`.

DERIVED: `0` is the sign asserted. `9` and `8` are the discriminant's coefficients, `vSix`'s, and the
exponent `2` squares `c`; `3` and the exponent `-(1)/4` spell `c`. -/
theorem disc_pos : 0 < 9 - 8 * ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 := by
  have h := (MassGap.LagTwoBound.floor_sq_bounds).2
  linarith

/-- `√(9 - 8c²) ^ 2 = 9 - 8c²`. `Real.sq_sqrt` at `disc_pos.le`; the nonnegativity of the radicand is
what it needs.

The form `vSix_root` and `lagTwoThresholdSix_gt` consume, since they must clear the square root.

DERIVED: `9`, `8` and the exponent `2` squaring `c` are the discriminant's, `vSix`'s; the outer
exponent `2` undoes the square root. `3` and `-(1)/4` spell `c`. -/
theorem disc_sq : Real.sqrt (9 - 8 * ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2) ^ 2
    = 9 - 8 * ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 :=
  Real.sq_sqrt disc_pos.le

/-- `0 < vSix`. The denominator `2(2 + 3c)` is positive because `c` is, and the numerator
`√(9 − 8c²) − (2c − 1)` is positive because `9 − 8c² > (2c − 1)²`, which rearranges to
`8 + 4c − 12c² > 0` and follows from the numeric brackets `LagTwoBound.floor_bounds` and
`floor_sq_bounds`.

DERIVED: `0` is the sign asserted; it is the only numeral in the statement, every other constant
being `vSix`'s. -/
theorem vSix_pos : 0 < vSix := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have hsq := MassGap.LagTwoBound.floor_sq_bounds
  have hd := disc_sq
  set c : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hcdef
  set D : ℝ := Real.sqrt (9 - 8 * c ^ 2) with hDdef
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hden : (0 : ℝ) < 2 * (2 + 3 * c) := by linarith [hc.1]
  have hnum : 0 < D - (2 * c - 1) := by
    nlinarith [hd, hD0, hsq.1, hsq.2, hc.1, hc.2]
  rw [vSix]
  exact div_pos hnum hden

/-- `(2 + 3c)·vSix² + (2c − 1)·vSix = 1 − c` at `c = 3^{−1/4}`: `vSix` is exactly a root of the
reduced quadratic. Substituting the definition and clearing denominators reduces the left side to
`(D² − (2c−1)²) / (4(2+3c))` with `D = √(9 − 8c²)`; `disc_sq` replaces `D²`, and `ring` closes it.

Equality, not an inequality: the threshold is the quadratic's own root, not a value taken below it.
This is what `confines_extent_six_of_lag_two_ratio` uses to turn a ratio bound into the criterion.

DERIVED: `2 + 3c` and `2c − 1` are the reduced quadratic's coefficients, `vSix`'s, and `1 − c` is the
criterion's right-hand coefficient. The exponent `2` squares `vSix`. `3` and `-(1)/4` spell `c`. -/
theorem vSix_root :
    (2 + 3 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * vSix ^ 2
        + (2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1) * vSix
      = 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have hd := disc_sq
  set c : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hcdef
  set D : ℝ := Real.sqrt (9 - 8 * c ^ 2) with hDdef
  have hP : (0 : ℝ) < 2 + 3 * c := by linarith [hc.1]
  have hkey : (2 + 3 * c) * ((D - (2 * c - 1)) / (2 * (2 + 3 * c))) ^ 2
        + (2 * c - 1) * ((D - (2 * c - 1)) / (2 * (2 + 3 * c)))
      = (D ^ 2 - (2 * c - 1) ^ 2) / (4 * (2 + 3 * c)) := by
    field_simp
    ring
  rw [vSix, hkey, hd]
  rw [div_eq_iff (by linarith : (4 : ℝ) * (2 + 3 * c) ≠ 0)]
  ring

/-- `0.0337 < lagTwoThresholdSix`. The proof first brackets `0.1837 < vSix` by clearing the
denominator and applying `nlinarith` to `disc_sq` and the numeric brackets on `c` and `c²`, then
squares.

CHOSEN: `0.0337` is a rational lower bound on the closed form, rounded down so that it lies below
the true value — the direction a lower bound requires, and away from the claim
`lagTwoThreshold < lagTwoThresholdSix`, so the rounding cannot manufacture that strict inequality.
`0.1837`, the intermediate bound on `vSix`, is rounded down for the same reason and appears in the
proof only. Neither decides anything; the closed form does, and `vSix_root` is what makes it the
quadratic's root. -/
theorem lagTwoThresholdSix_gt : 0.0337 < lagTwoThresholdSix := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have hsq := MassGap.LagTwoBound.floor_sq_bounds
  have hd := disc_sq
  have hD0 : 0 ≤ Real.sqrt (9 - 8 * ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2) := Real.sqrt_nonneg _
  have hden : (0 : ℝ) < 2 * (2 + 3 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) := by linarith [hc.1]
  have hv : 0.1837 < vSix := by
    rw [vSix, lt_div_iff₀ hden]
    nlinarith [hd, hD0, hsq.2, hc.1, hc.2]
  have hv0 : (0 : ℝ) < vSix := by linarith
  rw [lagTwoThresholdSix]
  nlinarith [hv, hv0]

/-- `LagTwoBound.lagTwoThreshold < lagTwoThresholdSix`. A `calc` through the two decimal brackets:
`LagTwoBound.lagTwoThreshold_lt` puts the left side below `0.018625`, `norm_num` compares the two
rationals, and `lagTwoThresholdSix_gt` puts the right side above `0.0337`.

A comparison of two real constants. `wilsonCorrAt 3` and `wilsonCorrAt 5` are different functions and
no statement here relates their values, so this transports no bound from one extent to the other.

DERIVED: no numeral in the statement; both sides are closed forms. The intermediate decimals
`0.018625` and `0.0337` belong to the bracketing theorems the `calc` cites, each of which carries its
own note. -/
theorem lagTwoThreshold_lt_lagTwoThresholdSix :
    MassGap.LagTwoBound.lagTwoThreshold < lagTwoThresholdSix := by
  calc MassGap.LagTwoBound.lagTwoThreshold
      < 0.018625 := MassGap.LagTwoBound.lagTwoThreshold_lt
    _ < 0.0337 := by norm_num
    _ < lagTwoThresholdSix := lagTwoThresholdSix_gt

/-- `vSix < 1`. From `vSix_root` and `vSix_pos` by `nlinarith`: the identity forces
`(2 + 3c)·vSix² < 1 − c < 1` while `2 + 3c > 4`, so `vSix² < 1/4`.

Together with `vSix_pos` this brackets the root in `(0, 1)`, which is what
`lagTwoThresholdSix_sharp` needs to make its profile admissible.

DERIVED: `1` is the upper bound asserted; it is the only numeral in the statement, every other
constant being `vSix`'s. -/
theorem vSix_lt_one : vSix < 1 := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have hroot := vSix_root
  have hv0 := vSix_pos
  nlinarith [hroot, hv0, hc.1, hc.2]

/-- There are reals `r₀ > 0`, `r₁, r₂, r₃ ≥ 0` satisfying `r₁² ≤ r₀r₂`, `r₂² ≤ r₀r₂` and
`r₃² ≤ r₂²` — the three non-diagonal log-convexity instances available at half-extent three, read
through circle symmetry — with `r₂ = lagTwoThresholdSix · r₀` exactly, and for which the extent-six
criterion FAILS.

The witness is `(1, vSix, vSix², vSix²)`, extended by circle symmetry to `ρ(4) = ρ(2)` and
`ρ(5) = ρ(1)`. The first and third instances hold with equality, and `vSix_root` puts the criterion
at equality, hence not strictly below.

So no constant above `lagTwoThresholdSix` is carried by this reduction, and
`confines_extent_six_of_lag_two_ratio`'s strict `<` cannot be weakened to `≤`. The statement is about
four arbitrary reals meeting those inequalities; it says nothing about `wilsonCorrAt`.

DERIVED: `0` is the strict lower bound on `r₀` and the lower bound on each of `r₁`, `r₂`, `r₃`. The
exponents `2` are the squares of the log-convexity instances and of
`lagTwoThresholdSix = vSix ^ 2`. In the failed criterion, `2c − 1`, `1 + 2c`, `1 + c` and `1 − c` are
`ConfinesSharp.confines_extent_six_iff`'s coefficients, and `3` with the exponent `-(1)/4` spells
`c`. The witness's components are `1`, `vSix`, `vSix²`, `vSix²`; the leading `1` is the contact
value, free by homogeneity. -/
theorem lagTwoThresholdSix_sharp :
    ∃ r₀ r₁ r₂ r₃ : ℝ, 0 < r₀ ∧ 0 ≤ r₁ ∧ 0 ≤ r₂ ∧ 0 ≤ r₃ ∧
      r₁ ^ 2 ≤ r₀ * r₂ ∧ r₂ ^ 2 ≤ r₀ * r₂ ∧ r₃ ^ 2 ≤ r₂ ^ 2 ∧
      r₂ = lagTwoThresholdSix * r₀ ∧
      ¬ ((2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1) * r₁
            + (1 + 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₂
            + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₃
          < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀) := by
  have hv0 := vSix_pos
  have hv1 := vSix_lt_one
  have hroot := vSix_root
  have hs1 : vSix ^ 2 < 1 := by nlinarith [hv0, hv1]
  have hquad : (vSix ^ 2) ^ 2 ≤ 1 * vSix ^ 2 := by nlinarith [hs1, pow_pos hv0 2]
  refine ⟨1, vSix, vSix ^ 2, vSix ^ 2, one_pos, hv0.le, by positivity, by positivity, ?_, hquad,
    le_rfl, by rw [lagTwoThresholdSix]; ring, ?_⟩
  · nlinarith [hv0]
  · rw [not_lt]
    nlinarith [hroot]

/-! ## 3. The sufficient condition at extent six -/

/-- If `K < lagTwoThresholdSix` and `wilsonCorrAt 5 (max β 0) 2 ≤ K * wilsonCorrAt 5 (max β 0) 0`,
then `3^{−1/4} < cosAvgEven ap6 β`.

`ConfinesSharp.confines_extent_six_iff` turns the conclusion into the linear criterion. The ratio
bound gives `ρ(2) < vSix²·ρ(0)`; `logConvex_six_lag_one` then gives `ρ(1) < vSix·ρ(0)`, using
`PlaqVariance.corrClay_zero_pos` for `ρ(0) > 0`; `lag_three_le_lag_two` collapses the `ρ(3)` term
into the `ρ(2)` one; and `vSix_root` evaluates the resulting bound to exactly `(1 − c)·ρ(0)`.

Every step is an equivalence or a proved inequality: `confines_extent_six_iff` is an `iff`, and the
two substitutions are the log-convexity instances above.

DERIVED: `5` is the `N` of `wilsonCorrAt N`; `0` is the lower clamp on the coupling and the contact
lag; `2` is the lag whose ratio is bounded. `3` and the exponent `-(1)/4` spell the constant the
cosine average must clear. `K` is the caller's. -/
theorem confines_extent_six_of_lag_two_ratio {β K : ℝ} (hK : K < lagTwoThresholdSix)
    (h : MassGap.wilsonCorrAt 5 (max β 0) 2 ≤ K * MassGap.wilsonCorrAt 5 (max β 0) 0) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven ap6 β := by
  rw [MassGap.ConfinesSharp.confines_extent_six_iff β]
  have hrp := MassGap.wilson_reflection_positive_at_even 5 3 (by norm_num) (by norm_num)
    (le_max_right β (0 : ℝ))
  have hc := MassGap.LagTwoBound.floor_bounds
  have hq := MassGap.ConfinesSharp.two_c_sub_one_pos
  have hroot := vSix_root
  have hv0 := vSix_pos
  have hpos0 : 0 < MassGap.wilsonCorrAt 5 (max β 0) 0 :=
    MassGap.PlaqVariance.corrClay_zero_pos 5 (max β 0)
  have hlc := logConvex_six_lag_one (max β 0)
  have h32 := lag_three_le_lag_two β
  have h1 := hrp.1 1
  have h2 := hrp.1 2
  set c : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hcdef
  set r0 : ℝ := MassGap.wilsonCorrAt 5 (max β 0) 0 with hr0
  set r1 : ℝ := MassGap.wilsonCorrAt 5 (max β 0) 1 with hr1
  set r2 : ℝ := MassGap.wilsonCorrAt 5 (max β 0) 2 with hr2
  set r3 : ℝ := MassGap.wilsonCorrAt 5 (max β 0) 3 with hr3
  have hr2lt : r2 < vSix ^ 2 * r0 := by
    have hKr : K * r0 < lagTwoThresholdSix * r0 := mul_lt_mul_of_pos_right hK hpos0
    rw [lagTwoThresholdSix] at hKr
    linarith
  have hstep : r0 * r2 < (vSix * r0) ^ 2 := by
    nlinarith [mul_pos hpos0 (sub_pos.2 hr2lt)]
  have hr1lt : r1 < vSix * r0 := by
    nlinarith [lt_of_le_of_lt hlc hstep, h1, mul_pos hv0 hpos0]
  have hcollapse : (2 * c - 1) * r1 + (1 + 2 * c) * r2 + (1 + c) * r3
      ≤ (2 * c - 1) * r1 + (2 + 3 * c) * r2 := by
    nlinarith [h32, hc.1]
  have hstrict : (2 * c - 1) * r1 + (2 + 3 * c) * r2
      < (2 * c - 1) * (vSix * r0) + (2 + 3 * c) * (vSix ^ 2 * r0) := by
    nlinarith [hr1lt, hr2lt, hq, hc.1]
  have hval : (2 * c - 1) * (vSix * r0) + (2 + 3 * c) * (vSix ^ 2 * r0) = (1 - c) * r0 := by
    nlinarith [hroot]
  linarith

/-! ## 4. The reduction -/

/-- The `Prop`: there is a real `K` strictly below `lagTwoThresholdSix` with
`wilsonCorrAt 5 β 2 ≤ K * wilsonCorrAt 5 β 0` at every `β ≥ 0`.

One constant for the whole nonnegative half-line, not one per coupling. The negative half-line is
not quantified over, and `EvenAperture.readEven` clamps at `max β 0`, so nothing is lost by that.

`confines_of_lagTwoRatioSix` is what consumes it. No statement in this module establishes it.

DERIVED: `5` is the `N` of `wilsonCorrAt N`, `ConfinesZero.ap6`'s extent index; `2` and `0` are lag
indices in `Fin 6`, and `0` is also the lower bound on the coupling. The only magnitude is
`lagTwoThresholdSix`, which is a closed form. -/
def LagTwoRatioSix : Prop :=
  ∃ K : ℝ, K < lagTwoThresholdSix ∧
    ∀ β : ℝ, 0 ≤ β → MassGap.wilsonCorrAt 5 β 2 ≤ K * MassGap.wilsonCorrAt 5 β 0

/-- `LagTwoRatioSix → ApertureRoute.ConfinesAtAnAperture`, with `ConfinesZero.ap6` as the existential
witness. `confines_extent_six_of_lag_two_ratio` at every `β`, the hypothesis read at `max β 0` so the
clamp discharges its nonnegativity side condition.

DERIVED: no numeral. Every constant is `LagTwoRatioSix`'s or `confines_extent_six_of_lag_two_ratio`'s,
and the aperture witness is named rather than written out. -/
theorem confines_of_lagTwoRatioSix (h : LagTwoRatioSix) : ApertureRoute.ConfinesAtAnAperture := by
  obtain ⟨K, hK, hb⟩ := h
  exact ⟨MassGap.ConfinesZero.ap6, fun β =>
    confines_extent_six_of_lag_two_ratio hK (hb (max β 0) (le_max_right β 0))⟩

/-! ## The cut interval at six lags

`exists_cut_lag_two_ratio_six` is the six-lag counterpart of
`LagTwoBound.exists_cut_lag_two_ratio` and `LagTwoEight.exists_cut_lag_two_ratio_eight`.

The inputs are extent-generic — `PlaqVariance.corrClay_zero_pos`, `ContactFloor.corrClay_zero_ge` and
`StrongCoupling.corrClay_abs_le_coreConst_mul_rate_pow` are stated at every `N` — and the only
extent-sensitive step is `circLag (2 : Fin 6) = 2`, which `decide` settles.

What it gives is weaker than `LagTwoRatioSix`, which asks for a single `K < lagTwoThresholdSix`
valid at every `β ≥ 0`. This gives every `K > 0` on an interval `[0, b]` whose `b` depends on `K`. -/

/-- `Moment.circLag (2 : Fin (5 + 1)) = 2`, by `decide`: at six lags the circular distance of lag
`2` is `2`, since `2 ≤ 6 - 2`.

The one extent-sensitive input to `exists_cut_lag_two_ratio_six`; it is what admits the power `k = 1`
in `corrClay_abs_le_coreConst_mul_rate_pow`.

DERIVED: `5` is the `N` of `Fin (N + 1)` and `1` the `+1`, so the lag type has six elements. `2` is
the lag whose circular distance is taken, and the value `2` is that distance — they coincide because
`2` is at most half of six. -/
theorem circLag_two_six : Moment.circLag (2 : Fin (5 + 1)) = 2 := by decide

/-- For every `K > 0` there is a `b > 0` such that
`wilsonCorrAt 5 β 2 ≤ K * wilsonCorrAt 5 β 0` for every `β ∈ [0, b]`.

The numerator is bounded by `StrongCoupling.corrClay_abs_le_coreConst_mul_rate_pow` at the power
`k = 1`, admissible because `circLag_two_six`; the denominator below by
`ContactFloor.corrClay_zero_ge`'s `e^{−128β}·ρ(0)|₀ ≤ ρ(0)`. The two are compared by continuity of
`β ↦ A · coreRate β · e^{128β}` at `0`, where `coreRate 0 = 0`, so `b` is obtained from a
neighbourhood rather than written down.

`b` is not named and depends on `K`, shrinking with it. `ρ(0)|₀` enters through
`PlaqVariance.corrClay_zero_pos`, which is non-constructive, so no numeral for `b` is available.

DERIVED: `0` is the strict lower bound on `K` and on `b`, the lower endpoint of the interval, and the
contact lag. `5` is the `N` of `wilsonCorrAt N` and `2` the lag whose ratio is bounded. The
constants appearing in the proof are not the statement's: `16 * 4` is `StrongCoupling`'s touch degree
at `dim = 4`, `128 = 2 · 64` is `ContactFloor.corrClay_zero_ge`'s exponent, and `1` is the power `k`
admitted by `circLag_two_six`. -/
theorem exists_cut_lag_two_ratio_six (K : ℝ) (hK : 0 < K) :
    ∃ b : ℝ, 0 < b ∧ ∀ β : ℝ, 0 ≤ β → β ≤ b →
      MassGap.wilsonCorrAt 5 β 2 ≤ K * MassGap.wilsonCorrAt 5 β 0 := by
  obtain ⟨b₀, hb₀, hr₀⟩ := MassGap.StrongArm.exists_strong_arm_cut
  set A : ℝ := MassGap.StrongCoupling.coreConst (16 * 4) b₀ with hAdef
  have hA128 : (128 : ℝ) ≤ A := by
    rw [hAdef]; exact MassGap.LagTwoBound.le_coreConst (16 * 4) hb₀.le hr₀
  have hA0 : 0 < A := by linarith
  set D : ℝ := MassGap.WilsonBridge.corrClay (5 + 1) 0 0 with hDdef
  have hD0 : 0 < D := by rw [hDdef]; exact MassGap.PlaqVariance.corrClay_zero_pos 5 0
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
  have hbnd := MassGap.StrongCoupling.corrClay_abs_le_coreConst_mul_rate_pow 5 hβ0 hrβ1
    (2 : Fin (5 + 1)) 1 (by rw [circLag_two_six]; norm_num)
  have hstep : MassGap.wilsonCorrAt 5 β 2 ≤ A * MassGap.StrongCoupling.coreRate (16 * 4) β := by
    rw [MassGap.StrongArm.wilsonCorrAt_eq_corrClay]
    calc MassGap.WilsonBridge.corrClay (5 + 1) β 2
        ≤ |MassGap.WilsonBridge.corrClay (5 + 1) β 2| := le_abs_self _
      _ ≤ MassGap.StrongCoupling.coreConst (16 * 4) β
            * MassGap.StrongCoupling.coreRate (16 * 4) β ^ 1 := hbnd
      _ = MassGap.StrongCoupling.coreConst (16 * 4) β
            * MassGap.StrongCoupling.coreRate (16 * 4) β := by ring
      _ ≤ A * MassGap.StrongCoupling.coreRate (16 * 4) β := mul_le_mul_of_nonneg_right hAβ hrnn
  have hfloor : Real.exp (-(128 * β)) * D ≤ MassGap.wilsonCorrAt 5 β 0 := by
    rw [MassGap.StrongArm.wilsonCorrAt_eq_corrClay, hDdef]
    exact MassGap.ContactFloor.corrClay_zero_ge 5 hβ0
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
  calc MassGap.wilsonCorrAt 5 β 2
      ≤ A * MassGap.StrongCoupling.coreRate (16 * 4) β := hstep
    _ ≤ K * (Real.exp (-(128 * β)) * D) := hkey
    _ ≤ K * MassGap.wilsonCorrAt 5 β 0 := mul_le_mul_of_nonneg_left hfloor hK.le

#print axioms circLag_two_six
#print axioms exists_cut_lag_two_ratio_six

/-- `K < LagTwoBound.lagTwoThreshold → K < lagTwoThresholdSix`. Transitivity through
`lagTwoThreshold_lt_lagTwoThresholdSix`.

The direction check: the set of constants admissible at four lags is contained in the set admissible
at six. It relates the two admissible SETS, not the two correlations, and supplies no `K`.

DERIVED: no numeral. `K` is the caller's and both thresholds are closed forms. -/
theorem admissible_at_six_of_admissible_at_four {K : ℝ}
    (hK : K < MassGap.LagTwoBound.lagTwoThreshold) : K < lagTwoThresholdSix :=
  lt_trans hK lagTwoThreshold_lt_lagTwoThresholdSix

/-! ## 5. Footprints -/

section Audit
#print axioms logConvex_six_lag_one
#print axioms logConvex_six_lag_three
#print axioms lag_three_le_lag_two
#print axioms vSix
#print axioms lagTwoThresholdSix
#print axioms disc_pos
#print axioms disc_sq
#print axioms vSix_pos
#print axioms vSix_root
#print axioms vSix_lt_one
#print axioms lagTwoThresholdSix_sharp
#print axioms lagTwoThresholdSix_gt
#print axioms lagTwoThreshold_lt_lagTwoThresholdSix
#print axioms confines_extent_six_of_lag_two_ratio
#print axioms LagTwoRatioSix
#print axioms confines_of_lagTwoRatioSix
#print axioms admissible_at_six_of_admissible_at_four
end Audit

end MassGap.LagTwoSix
