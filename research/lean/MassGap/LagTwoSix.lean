import MassGap.ConfinesSharp
import MassGap.LagTwoBound

/-!
# MassGap.LagTwoSix — the lag-two obligation is STRICTLY WEAKER at extent six than at extent four

`ApertureRoute.ConfinesAtAnAperture` is EXISTENTIAL in the aperture: `∃ a : EvenAp, ∀ β, …`, and
`EvenAperture.EvenAp` admits every even extent at least four. Extent four has been used throughout
only because it is the smallest. This file asks what the SAME obligation costs at extent six and
answers it with a number.

## The comparison, in one currency

Both extents reduce, through log-convexity alone, to a bound on the LAG-TWO RATIO `ρ(2)/ρ(0)` — the
quantity `TailRatio.RatioBelowThreshold` and `PeriodicLagTwo.confines_of_periodic_rate` are already
stated in. The two thresholds are

* extent four, `LagTwoBound.lagTwoThreshold = ((1−c)/(1+c))²`, bracketed in `(0.018623, 0.018625)`;
* extent six, `lagTwoThresholdSix` below, bracketed by `lagTwoThresholdSix_gt` above `0.0337`.

`lagTwoThreshold_lt_lagTwoThresholdSix` is those two facts composed: **the extent-six threshold is
strictly larger**, by a factor of `0.03379588…/0.01862399… = 1.8146…`.

**WHAT IS AND IS NOT BEING COMPARED.** `wilsonCorrAt 3` and `wilsonCorrAt 5` are different functions
and nothing in this tree relates their values, so this is NOT a statement that an extent-four bound
transports to extent six. It compares the OBLIGATION each extent imposes, in one common currency: the
CONSTANT a lag-two ratio bound must beat. `admissible_at_six_of_admissible_at_four` is exactly that
much and no more — a constant admissible at extent four is admissible at extent six; the bound itself
still has to be proved of the extent-six correlation.

## Why extent six reduces at all

`ConfinesSharp.confines_extent_six_iff` puts the criterion at

    (2c−1)·ρ(1) + (1+2c)·ρ(2) + (1+c)·ρ(3) < (1−c)·ρ(0),     c = 3^{−1/4},

with every coefficient positive (`ConfinesSharp.two_c_sub_one_pos` for the first), so all three
non-contact lags need UPPER bounds and none needs a lower one. That matters: `LogConvex`'s
right-hand lags are all of the form `2e`, hence EVEN, so — as `MomentShape` records — nothing in that
premise set can lower-bound `ρ` at an ODD lag. A criterion needing a lower bound on `ρ(1)` would be
unreachable from the shape facts; this one does not need it.

At half-extent `m = 3` the two instances of `LogConvex.corrClay_log_convex` this file uses are
`(e₁,e₂) = (0,1)`, giving `ρ(1)² ≤ ρ(0)ρ(2)`, and `(e₁,e₂) = (1,2)`, giving `ρ(3)² ≤ ρ(2)ρ(4)` which
is `ρ(3) ≤ ρ(2)` once `ConfinesSharp.sym_six_two` folds lag `4` onto lag `2`. The second is not
available at extent four, where `m = 2` leaves `(0,1)` as the only non-diagonal pair. Substituting
both leaves

    (2c−1)·√(ρ(0)ρ(2)) + (2+3c)·ρ(2) < (1−c)·ρ(0),

one quadratic in `√(ρ(2)/ρ(0))` whose positive root is `vSix`.

## The trend, and where it turns — NOT MACHINE-CHECKED IN THIS FILE

Extent six is not the end of the line, and larger is not monotonically better. At even extent `2m`
the cosines are `cos(πd/m)`, circle symmetry folds `d` onto `2m − d`, and the criterion is

    ∑_{d=1}^{m−1} 2(c − cos(πd/m))·ρ(d) + (1+c)·ρ(m) < (1−c)·ρ(0),

which is `ConfinesSharp.confines_extent_four_iff` at `m = 2` and `confines_extent_six_iff` at
`m = 3`. Reducing it against `LogConvex.corrClay_log_convex`'s cone as above gives, on `ρ(2)/ρ(0)`:

    extent  4 → 0.0186240      extent 10 → 0.0302593
    extent  6 → 0.0337959      extent 12 → 0.0250940
    extent  8 → 0.0354567

**The relief peaks at extent eight and then reverses.** Two things move against each other: the
coefficient of `ρ(1)` is `2(c − cos(π/m))`, which falls with `m` and turns NEGATIVE at `m = 5`, while
the number of deep lags — each of which the cone bounds only by `ρ(2)`, linearly — grows with `m`.
Past `m = 4` the second wins. The sign change buys nothing FROM THE SHAPE FACTS, because a negative
coefficient wants `ρ(1)` LARGE and that cone can only bound `ρ` at an odd lag from above: every
right-hand lag `corrClay_log_convex` produces is `2e`, hence even, so `ρ(1) → 0` stays admissible
(`MomentShape.odd_scaling_admissible`, a theorem and general in the extent), and dropping that term is
the exact worst case rather than a concession.

That is premise-set-relative, not structural, and the distinction is worth keeping: a lower bound on
an odd lag DOES exist outside the cone. `LinkGram.wilson_lag_two_le_lag_one` proves `ρ(2) ≤ ρ(1)` of
the Wilson correlation at every `0 ≤ β`, from link-reflection positivity rather than from `Shape`. It
is hard-wired to extent four today. Were it generalized, the extent-ten entry above would move from
`0.0302593` to `0.0306390` — so the peak at extent eight survives that too, and the trend's direction
does not depend on the odd-lag no-go.

Only the extent-four and extent-six entries are machine-checked, here and in `LagTwoBound`. The other
three are stated as what the same construction yields, not as theorems.

## What this does NOT claim

It does not bound `ρ(2)/ρ(0)` at either extent. What is delivered is a REDUCTION with a strictly
larger threshold, and `LagTwoRatioSix` names the remaining obligation.

**AND THE EXTENT-FOUR NO-GO DOES NOT TRANSFER VERBATIM — the extent-six one is weaker.**
`TailRatio.no_lag_two_bound_from_triple` gives no bound AT ALL at extent four, and its witness is
`(r₀,r₁,r₂) = (ε,ε,4)` with `r₂ > r₀`. That witness is NOT admissible here: at half-extent three the
instance `(e₁,e₂) = (0,2)` reads `ρ(2)² ≤ ρ(0)ρ(4) = ρ(0)ρ(2)`, so `ρ(2) ≤ ρ(0)` IS derivable at
extent six where it is not at extent four. What survives is the constant profile,
`TailRatio.no_strict_lag_bound_with_contact`, which defeats every `K < 1`. So the correct statement at
extent six is that the shape facts carry `K = 1` and nothing under it — still far above
`lagTwoThresholdSix`, so `LagTwoRatioSix` is open for the same reason, but by the weaker of the two
no-gos.

It also does not carry the spectral decomposition across. `SlabQuadratic.wilsonSpectral` proves
`Complete.WilsonSpectral 3 β` at extent four and nothing in this tree proves it at extent six, so
`PeriodicLagTwo.confines_of_periodic_rate` has no extent-six counterpart yet. The relief proved here
is available to any route that bounds the lag-two ratio directly.

Foundational footprint only (`#print axioms` on every declaration, in the audit section).
The module is not in the library root's import list.
Build: `python research/code/lean_build.py build MassGap.LagTwoSix`.
-/

namespace MassGap.LagTwoSix

open MassGap MassGap.EvenAperture MassGap.ApertureRoute MassGap.ConfinesZero

/-! ## 1. The two log-convexity instances available at half-extent three

DERIVED throughout this section: `5` is `N` with `N + 1 = 6 = 2 * 3`, `ConfinesZero.ap6`'s own
extent; `3` is the half-extent `m`, read off `LogConvex.corrClay_log_convex`'s hypothesis
`Nap + 1 = 2 * m`; the lag indices `0, 1, 2, 3, 4` are index values, not magnitudes. -/

/-- **`ρ(1)² ≤ ρ(0)·ρ(2)` at extent six.** `LogConvex.corrClay_log_convex` at `(e₁, e₂) = (0, 1)`,
both below the half-extent `3`. This is the same pair that is the ONLY non-diagonal one at extent
four. -/
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

/-- **`ρ(3)² ≤ ρ(2)·ρ(4)` at extent six.** `LogConvex.corrClay_log_convex` at `(e₁, e₂) = (1, 2)`,
both below the half-extent `3`. NOT available at extent four: there `m = 2` and `e₂ = 2` is not
below it. -/
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

/-- **THE ANTIPODAL LAG IS BELOW THE LAG-TWO VALUE AT EXTENT SIX**, `ρ(3) ≤ ρ(2)`.

`logConvex_six_lag_three` with `ConfinesSharp.sym_six_two` folding lag `4` onto lag `2` reads
`ρ(3)² ≤ ρ(2)²`, and both are nonnegative by `Complete.wilson_reflection_positive_at_even`. This is
what removes the third lag from the criterion, and it has no extent-four analogue — at extent four
the antipodal lag IS lag two. -/
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

/-- The positive root of the reduced extent-six quadratic, in `v = √(ρ(2)/ρ(0))`.

DERIVED: every literal is a coefficient of `ConfinesSharp.confines_extent_six_iff` or of the
quadratic formula applied to it, and none is chosen. `2c−1`, `1+2c` and `1+c` are the criterion
own coefficients; `2 + 3c = (1+2c) + (1+c)` is the collapse `lag_three_le_lag_two` performs;
`9` and `8` are the discriminant `(2c−1)² + 4(2+3c)(1−c) = 9 − 8c²`, which is a `ring` identity
rather than a computed number; the outer `2` is the quadratic formula denominator; and the `4`
and `1` inside `3^(−1/4)` are the floor `c`, carried in by name from `Floor.lean`. -/
noncomputable def vSix : ℝ :=
  (Real.sqrt (9 - 8 * ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2) - (2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1))
    / (2 * (2 + 3 * (3 : ℝ) ^ (-(1 : ℝ) / 4)))

/-- **THE THRESHOLD ON THE LAG-TWO RATIO AT EXTENT SIX** — `vSix` squared, because the criterion is a
bound on `√(ρ(2)/ρ(0))`. The extent-six counterpart of `LagTwoBound.lagTwoThreshold`, in the SAME
currency.

Sufficient by `confines_extent_six_of_lag_two_ratio`, and BEST POSSIBLE by
`lagTwoThresholdSix_sharp`, which exhibits a profile meeting every extent-six log-convexity instance
at exactly this ratio and failing the criterion. So it is the threshold, not a margin.

DERIVED: the `2` is the squaring, because `vSix` is the root in `v = √(ρ(2)/ρ(0))` while the
criterion is stated on the RATIO. No numeral of this declaration is a level. -/
noncomputable def lagTwoThresholdSix : ℝ := vSix ^ 2

/-- `9 − 8c² > 0`, so the discriminant has a real square root. From `LagTwoBound.floor_sq_bounds`. -/
theorem disc_pos : 0 < 9 - 8 * ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 := by
  have h := (MassGap.LagTwoBound.floor_sq_bounds).2
  linarith

/-- The square root squared, as the root identity needs it. -/
theorem disc_sq : Real.sqrt (9 - 8 * ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2) ^ 2
    = 9 - 8 * ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 :=
  Real.sq_sqrt disc_pos.le

/-- `vSix > 0`: the numerator is positive because `9 − 8c² > (2c−1)²`, which is
`8 + 4c − 12c² > 0` at `c < 0.76`. -/
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

/-- **THE ROOT IDENTITY.** `(2+3c)·vSix² + (2c−1)·vSix = 1 − c`: `vSix` is exactly the positive root
of the reduced criterion, so the threshold is the criterion's own and not a cut. -/
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

/-- **THE THRESHOLD IS ABOVE `0.0337`.**

CHOSEN, both numerals, and both rounded DOWN — away from the claim
`lagTwoThreshold < lagTwoThresholdSix`, so neither rounding can manufacture the strict inequality:
`0.1837` is below `vSix = 0.18383656…` and `0.0337` is below `lagTwoThresholdSix = 0.03379588…`. They
decide nothing; the closed form does, and `vSix_root` is what makes it the criterion's own root. -/
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

/-- **THE RELIEF, MACHINE-CHECKED.** The extent-six threshold on the lag-two ratio is STRICTLY LARGER
than the extent-four one. `LagTwoBound.lagTwoThreshold_lt` puts the extent-four threshold below
`0.018625`; `lagTwoThresholdSix_gt` puts the extent-six one above `0.0337`.

This compares the two CONSTANTS, not the two correlations: `wilsonCorrAt 3` and `wilsonCorrAt 5` are
different functions and nothing here transports a bound from one to the other. What it says is that
the obligation does not change SHAPE with the aperture — it is a lag-two ratio bound at both — and
that the number it has to beat is larger at extent six. -/
theorem lagTwoThreshold_lt_lagTwoThresholdSix :
    MassGap.LagTwoBound.lagTwoThreshold < lagTwoThresholdSix := by
  calc MassGap.LagTwoBound.lagTwoThreshold
      < 0.018625 := MassGap.LagTwoBound.lagTwoThreshold_lt
    _ < 0.0337 := by norm_num
    _ < lagTwoThresholdSix := lagTwoThresholdSix_gt

/-- `vSix < 1`, from the root identity alone: `(2+3c)·vSix² < 1 − c < 1` and `2 + 3c > 4`. -/
theorem vSix_lt_one : vSix < 1 := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have hroot := vSix_root
  have hv0 := vSix_pos
  nlinarith [hroot, hv0, hc.1, hc.2]

/-- **THE THRESHOLD IS THE BEST ONE THE PROVED SHAPE FACTS CARRY AT EXTENT SIX** — it is not a cut
with margin left in it.

The profile `ρ = (1, vSix, vSix², vSix²)`, extended by circle symmetry to `ρ(4) = ρ(2)` and
`ρ(5) = ρ(1)`, satisfies EVERY non-diagonal instance of `LogConvex.corrClay_log_convex` available at
half-extent three — `(0,1)`, `(0,2)` and `(1,2)`, the first and third with EQUALITY — and it sits at
`ρ(2) = lagTwoThresholdSix · ρ(0)` exactly, where `vSix_root` puts the criterion at equality and hence
NOT strictly below. So no constant above `lagTwoThresholdSix` can be carried by this reduction, and
`confines_extent_six_of_lag_two_ratio`'s strict `<` cannot be weakened to `≤`.

This is the extent-six counterpart of `ConfinesSharp.shape_admits_failure`, sharpened from the flat
profile to the boundary one.

DERIVED: no numeral. The four components are `1`, `vSix`, `vSix²`, `vSix²`; the exponent `2` is the
square in the log-convexity statement and in `lagTwoThresholdSix = vSix ^ 2`. -/
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

/-- **A LAG-TWO RATIO BELOW `lagTwoThresholdSix` CLEARS THE FLOOR AT EXTENT SIX.**

The extent-six counterpart of `ConfinesZero.confines_extent_four_of_lag_two_small` composed with
`LagTwoBound.lag_two_criterion_of_ratio`, and strictly weaker in hypothesis by
`lagTwoThreshold_lt_lagTwoThresholdSix`.

Nothing is spent that is not proved: `ConfinesSharp.confines_extent_six_iff` is an equivalence, and
the two substitutions are `logConvex_six_lag_one` and `lag_three_le_lag_two`. -/
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

/-- **THE REMAINING OBLIGATION AT EXTENT SIX.** One real constant strictly below
`lagTwoThresholdSix`, bounding the lag-two ratio of the extent-six correlation at every NONNEGATIVE
coupling.

OPEN. Nothing in this tree proves it, and the shape facts cannot. The no-go that applies AT THIS
EXTENT is `TailRatio.no_strict_lag_bound_with_contact`, whose witness is the constant profile: it
conforms to nonnegativity, circle symmetry, log-convexity and `ρ(2) ≤ ρ(0)`, and it defeats every
`K < 1`. The stronger `no_lag_two_bound_from_triple` does NOT apply here — its witness has
`ρ(2) > ρ(0)`, which half-extent three rules out. Either way `lagTwoThresholdSix` is far under one, so
what closes `LagTwoRatioSix` must come from the dynamics.

The negative half-line is free: `EvenAperture.readEven` clamps at `max β 0`, so the hypothesis is
only ever read at a nonnegative coupling.

DERIVED: `5` is `ConfinesZero.ap6`'s extent index and `2`, `0` are lag indices. The only magnitude is
`lagTwoThresholdSix`, which is a closed form. -/
def LagTwoRatioSix : Prop :=
  ∃ K : ℝ, K < lagTwoThresholdSix ∧
    ∀ β : ℝ, 0 ≤ β → MassGap.wilsonCorrAt 5 β 2 ≤ K * MassGap.wilsonCorrAt 5 β 0

/-- **THE REDUCTION.** `LagTwoRatioSix` gives `ApertureRoute.ConfinesAtAnAperture` outright, with
`ConfinesZero.ap6` as the witness. The extent-six counterpart of
`LagTwoBound.confines_of_lag_two_ratio`, and it consumes a strictly weaker hypothesis. -/
theorem confines_of_lagTwoRatioSix (h : LagTwoRatioSix) : ApertureRoute.ConfinesAtAnAperture := by
  obtain ⟨K, hK, hb⟩ := h
  exact ⟨MassGap.ConfinesZero.ap6, fun β =>
    confines_extent_six_of_lag_two_ratio hK (hb (max β 0) (le_max_right β 0))⟩

/-- **A CONSTANT ADMISSIBLE AT EXTENT FOUR IS ADMISSIBLE AT EXTENT SIX.** The direction check on
`lagTwoThreshold_lt_lagTwoThresholdSix`: the relief cannot be pointing the wrong way, because the
extent-four admissible set is contained in the extent-six one. -/
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
