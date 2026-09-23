import Mathlib
import MassGap.LagTwoSix
import MassGap.FreeFieldLagTwo

/-!
# MassGap.FreeFieldLagTwoSix — the free-field lag-two ratio on the periodic `6⁴` torus

The extent-four construction of `FreeFieldLagTwo`, repeated at extent six.

## Section 1 — the exact propagator data

On the `6⁴` torus the momenta are `p_μ = π k_μ / 3`, so `p̂_μ² = 2 - 2 cos p_μ` takes only the
integer values `0, 1, 3, 4, 3, 1` (`hatSq6`), and the lag phase `cos (p₂ d)` is a half-integer,
carried doubled as `lagPhase6` so it stays in `ℤ`. That doubling is the same at every lag and
cancels in any ratio. `clearDen6 = 720720` is the least common multiple of `1 … 16`, the range of
nonzero values of `momSq6`, and `clearDen6_exact` decides that it clears every one of them across
all `6 ^ 4 = 1296` momenta. `fsCorr6 d` is the resulting exact integer `2 · V · 720720 · D d`, and
`fsCorr6_zero`, `fsCorr6_one`, `fsCorr6_two`, `fsCorr6_three` decide its values;
`fsCorr6_fold` decides the circle symmetry `fsCorr6 4 = fsCorr6 2` and `fsCorr6 5 = fsCorr6 1`.

## Section 2 — the ratio

`freeRatioSix = (fsCorr6 2 / fsCorr6 0) ^ 2`, and `freeRatioSix_eq` evaluates it to
`34515625 / 67215229081`, which `freeRatioSix_lt_freeRatio` proves is below
`FreeFieldLagTwo.freeRatio = 5329 / 3186225`. At extent four lag two is the antipodal lag and
collects the torus both ways round; at extent six it is an interior lag.

## Section 3 — the hypothesis and the effective bound

`EffectiveGaussianLagTwoSix ε` posits a coupling `B` beyond which one positive scale `R` gives
`wilsonCorrAt 5 β d ≤ (1 + ε) * (R * fsCorr6 d ^ 2)` at every one of the six lags, together with the
matching lower bound `(1 - ε) * (R * fsCorr6 0 ^ 2) ≤ wilsonCorrAt 5 β 0` at the contact lag only.
It is a hypothesis; no declaration in this module proves it. The upper bound ranges over all six
lags because, restricted to the two lags the conclusion names, a free scale can be chosen exactly
when the conclusion already holds — that is `FreeFieldLagTwo.two_lag_form_collapses`. The lower
bound is stated at the contact lag alone, where `PlaqVariance.corrClay_zero_pos` supplies
positivity; a two-sided sandwich at every lag would assert `wilsonCorrAt 5 β 2 > 0`, which is not
proved here.

`lagTwoConstantSix ε = ((1 + ε) / (1 - ε)) * (fsCorr6 2 / fsCorr6 0) ^ 2` is the constant the
hypothesis delivers; `epsMaxSix = 24 / 25` is the admissible relative error;
`inflationSix_le` bounds `(1 + ε) / (1 - ε)` by `49` there; and
`lagTwoConstantSix_lt_threshold` puts `lagTwoConstantSix ε` below
`LagTwoSix.lagTwoThresholdSix`, since `49 * (34515625 / 67215229081) = 0.0251622…` and
`LagTwoSix.lagTwoThresholdSix_gt` puts the threshold above `0.0337`. `effective_lag_two_bound_six`
assembles these into the lag-two bound above `B`.

Scope: `effective_lag_two_bound_six` eliminates the free scale `R` from the hypothesis; it does not
derive the hypothesis. The bound it produces starts at `B` and says nothing below it.
`MiddleIntervalLagTwoSix K B` states the missing range `0 ≤ β ≤ B`, and `confines_of_arms_six`
combines the two through `LagTwoSix.confines_of_lagTwoRatioSix`. Numerals cross-checked by
`research/code/certify/free_field_lag_two_ratio.py`.
-/

namespace MassGap.FreeFieldLagTwoSix

open Finset

/-! ## 1. The exact free-field propagator data on the periodic `6⁴` torus

DERIVED throughout: `6` is the periodic extent `wilsonCorrAt 5` runs on (`5 + 1 = 6`), `4` is the
dimension of the problem, and `0, 1, 2` name the plaquette plane and the lag direction as
`WilsonBridge.corrClay` fixes them. -/

/-- `p̂² = 2 - 2 cos (2πk/6)` at extent six, tabulated as a natural number on `Fin 6`.

DERIVED: evaluating `2 − 2cos(2πk/6)` at `k = 0 … 5` gives `0, 1, 3, 4, 3, 1`. Every entry is a value
of that expression. -/
def hatSq6 : Fin 6 → ℕ := ![0, 1, 3, 4, 3, 1]

/-- Twice the lag phase, `2 cos (2πkd/6)`, tabulated as an integer on `Fin 6 × Fin 6`. The doubling
is what makes the entries integral.

DERIVED: `2cos(2πm/6)` is `2, 1, −1, −2, −1, 1` at `m = 0 … 5`; the doubling is what makes the phase
an integer and it is the SAME at every lag, so it cancels in every ratio. The argument is `k·d`
reduced mod the extent, which is `Fin 6` multiplication. -/
def lagPhase6 (k d : Fin 6) : ℤ := ![2, 1, -1, -2, -1, 1] (k * d)

/-- The common denominator `720720`, the least common multiple of `1 … 16`.

DERIVED: `p̂²` is a sum of four values from `{0,1,3,4}`, so its nonzero values lie in `1 … 16`, and
`720720` is their least common multiple. `clearDen6_exact` checks it. -/
def clearDen6 : ℕ := 720720

/-- `p̂² = ∑_μ p̂_μ²` at the momentum `(a, b, c, e)`.

DERIVED: the `6` is `Fin 6`, the extent of the torus, so `a b c e` are momentum INDICES. There are
four of them because the problem is four-dimensional. -/
def momSq6 (a b c e : Fin 6) : ℕ := hatSq6 a + hatSq6 b + hatSq6 c + hatSq6 e

/-- The plaquette-plane numerator `p̂₀² + p̂₁²`.

DERIVED: the `6` is `Fin 6`, the extent, so `a` and `b` are momentum indices — two of them because a
plaquette spans a PLANE, the plane `0, 1` that `WilsonBridge.corrClay` fixes. -/
def planeNum6 (a b : Fin 6) : ℕ := hatSq6 a + hatSq6 b

/-- One momentum's contribution to `2·V·720720·D(d)`.

DERIVED: the `6` is `Fin 6`, the extent, so `d a b c e` are indices; the `720720` is `clearDen6`, the
lcm derived there; the `2` is the doubling `lagPhase6` carries to stay integral, lag-independent and
therefore cancelling; and the `0` is a GUARD on the zero momentum rather than a value, with
`zero_momentum_term_vanishes6` proving the other branch would return `0` there anyway. -/
def fsTerm6 (d a b c e : Fin 6) : ℤ :=
  if momSq6 a b c e = 0 then 0
  else lagPhase6 c d * (planeNum6 a b * (clearDen6 / momSq6 a b c e) : ℕ)

/-- The free-field field-strength correlation at lag `d` on the extent-six torus, as the exact
integer `2 · V · 720720 · D d`: the sum of `fsTerm6 d` over all four momentum indices.

DERIVED: the one numeral in the statement is the `6` of `Fin 6`, the extent of the torus, so `d` is
a lag index. The overall factor `2 · V · 720720` sits in `fsTerm6` and `clearDen6`, is the same at
every lag, and cancels in every ratio. -/
def fsCorr6 (d : Fin 6) : ℤ := ∑ a, ∑ b, ∑ c, ∑ e, fsTerm6 d a b c e

/-- `momSq6 a b c e * (clearDen6 / momSq6 a b c e) = clearDen6` whenever `momSq6 a b c e ≠ 0`: the
natural-number division in `fsTerm6` is exact. Proved by `decide` over all `6 ^ 4 = 1296` momenta.

DERIVED: `6` is the extent, as `Fin 6`, so `a b c e` are momentum indices; `0` is the excluded
value of `momSq6`, the zero momentum, where the division would not be exact. -/
theorem clearDen6_exact (a b c e : Fin 6) (h : momSq6 a b c e ≠ 0) :
    momSq6 a b c e * (clearDen6 / momSq6 a b c e) = clearDen6 := by
  revert h; revert a b c e; decide

/-- `planeNum6 a b = 0` whenever `momSq6 a b c e = 0`: at the zero momentum the plaquette-plane
numerator vanishes too. Proved by `decide` over all momenta. Together with the guard in `fsTerm6`
this means the excluded branch would have contributed zero anyway, so no zero-mode subtraction is
performed.

DERIVED: `6` is the extent, as `Fin 6`; the two `0`s are the vanishing of `momSq6` in the hypothesis
and of `planeNum6` in the conclusion. -/
theorem zero_momentum_term_vanishes6 (a b c e : Fin 6) (h : momSq6 a b c e = 0) :
    planeNum6 a b = 0 := by
  revert h; revert a b c e; decide

theorem fsCorr6_zero : fsCorr6 0 = 933332400 := by decide

theorem fsCorr6_one : fsCorr6 1 = 128163984 := by decide

theorem fsCorr6_two : fsCorr6 2 = 21150000 := by decide

theorem fsCorr6_three : fsCorr6 3 = 7678032 := by decide

/-- Circle symmetry of the correlation on the extent-six torus: `fsCorr6 4 = fsCorr6 2` and
`fsCorr6 5 = fsCorr6 1`, both by `decide`.

DERIVED: the four numerals `4, 2, 5, 1` are lag indices in `Fin 6`, paired by `d ↦ 6 - d`, which is
the reflection the torus identifies. -/
theorem fsCorr6_fold : fsCorr6 4 = fsCorr6 2 ∧ fsCorr6 5 = fsCorr6 1 := by
  constructor <;> decide

/-! ## 2. The ratio -/

/-- The free-field lag-two ratio at extent six, `(fsCorr6 2 / fsCorr6 0) ^ 2`, as a rational. The
common factor `2 · V · 720720` cancels between numerator and denominator, so the ratio is the one
`D 2 / D 0` would give.

DERIVED: `2` and `0` are LAGS — the lag the claim is about and the contact lag it is normalised
against — and the outer `2` is Wick's square. The values are `fsCorr6`'s, decided above. -/
def freeRatioSix : ℚ := ((fsCorr6 2 : ℚ) / (fsCorr6 0 : ℚ)) ^ 2

/-- `freeRatioSix = (5875/259259)² = 34515625/67215229081 = 0.000513509…` — `3.26×` below the
extent-four value, because lag two is an interior lag at extent six and the antipodal one at extent
four.

DERIVED: `2` and `0` are lag indices, selecting `fsCorr6 2 = 21150000` and
`fsCorr6 0 = 933332400`, both decided above; the outer `2` is Wick's square. `34515625` and
`67215229081` are the numerator and denominator of `(21150000 / 933332400) ^ 2` in lowest terms —
computed, not chosen. -/
theorem freeRatioSix_eq : freeRatioSix = 34515625 / 67215229081 := by
  rw [freeRatioSix, fsCorr6_two, fsCorr6_zero]; norm_num

theorem freeRatioSix_pos : 0 < freeRatioSix := by rw [freeRatioSix_eq]; norm_num

/-- `freeRatioSix < FreeFieldLagTwo.freeRatio`, as rationals: the extent-six free-field lag-two
ratio is below the extent-four one, by a factor of about `3.26`. Both sides are rewritten to their
decided values and compared by `norm_num`. The companion inequality on the thresholds is
`LagTwoSix.lagTwoThreshold_lt_lagTwoThresholdSix`.

DERIVED: no numeral occurs in the statement; both sides are named definitions. -/
theorem freeRatioSix_lt_freeRatio : freeRatioSix < MassGap.FreeFieldLagTwo.freeRatio := by
  rw [freeRatioSix_eq, MassGap.FreeFieldLagTwo.freeRatio_eq]; norm_num

/-! ## 3. The named open hypothesis, and the effective bound

DERIVED: `5` is the extent index with `5 + 1 = 6`, the extent `LagTwoSix` works at; `2` and `0` are
lag indices. `24/25` is the one CHOSEN numeral — see its note. -/

/-- The hypothesis this module's effective bound consumes. `EffectiveGaussianLagTwoSix ε` asserts
that there is a coupling `B` such that for every `β ≥ B` there is a scale `R` with `0 < R`,

* `wilsonCorrAt 5 β d ≤ (1 + ε) * (R * fsCorr6 d ^ 2)` at every one of the six lags `d : Fin 6`, and
* `(1 - ε) * (R * fsCorr6 0 ^ 2) ≤ wilsonCorrAt 5 β 0` at the contact lag.

A `Prop`, not a theorem; no declaration in this module or its imports establishes it.

Scope. The upper bound ranges over all six lags rather than the two the conclusion names: restricted
to those two, a free scale can be chosen exactly when the conclusion already holds, which is
`FreeFieldLagTwo.two_lag_form_collapses`. The lower bound is at the contact lag only, where
`PlaqVariance.corrClay_zero_pos` supplies positivity; a two-sided sandwich at every lag would assert
`wilsonCorrAt 5 β 2 > 0`. The scale `R` is existentially bound inside the quantifier over `β`, so it
may vary with the coupling.

DERIVED: no numeral is a magnitude. `5` is the APERTURE — `wilsonCorrAt 5` is the extent-six torus
(`5 + 1 = 6`) — and `6` is that extent, as `Fin 6`, the lags the upper bound ranges over. `0` is the
contact lag on the lower bound and the floor `0 < R` puts on the scale; the `1`s and the `2` are the
band `(1 ± ε)` and Wick's square. `ε`, `B` and `R` are all variables, which is what makes this a
hypothesis rather than a fitted statement. -/
def EffectiveGaussianLagTwoSix (ε : ℝ) : Prop :=
  ∃ B : ℝ, ∀ β : ℝ, B ≤ β → ∃ R : ℝ, 0 < R ∧
    (∀ d : Fin 6, MassGap.wilsonCorrAt 5 β d ≤ (1 + ε) * (R * ((fsCorr6 d : ℝ)) ^ 2)) ∧
    (1 - ε) * (R * ((fsCorr6 0 : ℝ)) ^ 2) ≤ MassGap.wilsonCorrAt 5 β 0

/-- The constant `((1 + ε) / (1 - ε)) * (fsCorr6 2 / fsCorr6 0) ^ 2` that
`effective_lag_two_bound_six` produces from `EffectiveGaussianLagTwoSix ε`: the band's width times
the free-field lag-two ratio.

DERIVED: the `1`s are the band `(1 ± ε)` `EffectiveGaussianLagTwoSix` states, so the first factor is
that hypothesis's own width and not a number this definition picks. The `2` and `0` are the two LAGS,
and the outer `2` is Wick's square; the value is `freeRatioSix`, decided above. -/
noncomputable def lagTwoConstantSix (ε : ℝ) : ℝ :=
  ((1 + ε) / (1 - ε)) * ((fsCorr6 2 : ℝ) / (fsCorr6 0 : ℝ)) ^ 2

/-- The admissible relative error at extent six, `24 / 25`, as a rational.

CHOSEN: `24 / 25` is picked, and rounded DOWN — away from the claim
`lagTwoConstantSix ε < lagTwoThresholdSix`, so the rounding cannot manufacture the inequality. The
exact supremum against `LagTwoSix.lagTwoThresholdSix_gt`'s bracket `0.0337` is `0.96998…`, where
`(1 + ε) / (1 - ε)` reaches `0.0337 / 0.000513509 = 65.62…`. At `24 / 25` the inflation factor is
`49`, so `1.34` of that margin is unspent and any `ε` below `0.96998` would serve. -/
def epsMaxSix : ℚ := 24 / 25

/-- `(1 + ε) / (1 - ε) ≤ 49` for every real `ε ≤ (epsMaxSix : ℝ)`. The hypothesis puts `1 - ε`
at or above `1 / 25`, which is positive, so `div_le_iff₀` applies and `linarith` closes.
Nonnegativity of `ε` is not assumed and is not needed.

DERIVED: `1` is the centre of the band `(1 ± ε)`, appearing in both numerator and denominator; `49`
is `(1 + 24 / 25) / (1 - 24 / 25)` evaluated at the endpoint `epsMaxSix`, so it is that chosen
error's own inflation factor and nothing else. -/
theorem inflationSix_le {ε : ℝ} (hε : ε ≤ (epsMaxSix : ℝ)) : (1 + ε) / (1 - ε) ≤ 49 := by
  have he : ε ≤ 24 / 25 := by rw [epsMaxSix] at hε; norm_num at hε; linarith
  have hden : (0 : ℝ) < 1 - ε := by linarith
  rw [div_le_iff₀ hden]
  linarith [he]

/-- `lagTwoConstantSix ε < LagTwoSix.lagTwoThresholdSix` for every `ε ≤ (epsMaxSix : ℝ)`. The proof
bounds the inflation factor by `49` with `inflationSix_le`, evaluates the squared ratio as
`34515625 / 67215229081`, so that `lagTwoConstantSix ε ≤ 49 * (34515625 / 67215229081) = 0.0251622…`,
and compares with `LagTwoSix.lagTwoThresholdSix_gt`, which places the threshold above `0.0337`.

DERIVED: no numeral occurs in the statement — both sides are named definitions, and `ε` is bounded
by the named `epsMaxSix`. The numerals above are the proof's. -/
theorem lagTwoConstantSix_lt_threshold {ε : ℝ} (hε : ε ≤ (epsMaxSix : ℝ)) :
    lagTwoConstantSix ε < MassGap.LagTwoSix.lagTwoThresholdSix := by
  have hinf := inflationSix_le hε
  have hsq : ((fsCorr6 2 : ℝ) / (fsCorr6 0 : ℝ)) ^ 2 = 34515625 / 67215229081 := by
    rw [fsCorr6_two, fsCorr6_zero]; norm_num
  have hstep : lagTwoConstantSix ε ≤ 49 * (34515625 / 67215229081) := by
    rw [lagTwoConstantSix, hsq]
    exact mul_le_mul_of_nonneg_right hinf (by norm_num)
  have hgt := MassGap.LagTwoSix.lagTwoThresholdSix_gt
  have hnum : (49 : ℝ) * (34515625 / 67215229081) < 0.0337 := by norm_num
  linarith

/-- The lag-two bound above a coupling, from the hypothesis. Given `0 ≤ ε`, `ε ≤ (epsMaxSix : ℝ)`
and `EffectiveGaussianLagTwoSix ε`, there is a `B` such that
`lagTwoConstantSix ε < LagTwoSix.lagTwoThresholdSix` and, for every `β ≥ B`,
`wilsonCorrAt 5 β 2 ≤ lagTwoConstantSix ε * wilsonCorrAt 5 β 0`. The proof takes the hypothesis's own
`B` and `R`, applies its upper bound at lag `2` and its lower bound at lag `0`, and cancels `R` and
`fsCorr6 0 ^ 2` through `lagTwoConstantSix`'s definition by `field_simp`.

Scope: `R` is eliminated rather than determined, and the bound holds only for `β ≥ B`; the range
below `B` is `MiddleIntervalLagTwoSix`.

DERIVED: `0` is the lower bound on `ε`, which is what makes `lagTwoConstantSix ε` nonnegative, and
the contact lag in `wilsonCorrAt 5 β 0`; `5` is the aperture, `wilsonCorrAt 5` being the extent-six
torus since `5 + 1 = 6`; `2` is the lag the bound is about. -/
theorem effective_lag_two_bound_six {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ (epsMaxSix : ℝ))
    (h : EffectiveGaussianLagTwoSix ε) :
    ∃ B : ℝ, lagTwoConstantSix ε < MassGap.LagTwoSix.lagTwoThresholdSix ∧
      ∀ β : ℝ, B ≤ β →
        MassGap.wilsonCorrAt 5 β 2 ≤ lagTwoConstantSix ε * MassGap.wilsonCorrAt 5 β 0 := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, lagTwoConstantSix_lt_threshold hε, fun β hβ => ?_⟩
  obtain ⟨R, hR, hall, hlower⟩ := hB β hβ
  have hupper := hall 2
  have he : ε ≤ 24 / 25 := by rw [epsMaxSix] at hε; norm_num at hε; linarith
  have hden : (0 : ℝ) < 1 - ε := by linarith
  have h0 : (fsCorr6 0 : ℝ) = 933332400 := by rw [fsCorr6_zero]; norm_num
  have h2 : (fsCorr6 2 : ℝ) = 21150000 := by rw [fsCorr6_two]; norm_num
  have hkey : lagTwoConstantSix ε * ((1 - ε) * (R * ((fsCorr6 0 : ℝ)) ^ 2))
      = (1 + ε) * (R * ((fsCorr6 2 : ℝ)) ^ 2) := by
    rw [lagTwoConstantSix, h0, h2]
    field_simp
  have hcnn : 0 ≤ lagTwoConstantSix ε := by
    rw [lagTwoConstantSix]
    exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (sq_nonneg _)
  calc MassGap.wilsonCorrAt 5 β 2
      ≤ (1 + ε) * (R * ((fsCorr6 2 : ℝ)) ^ 2) := hupper
    _ = lagTwoConstantSix ε * ((1 - ε) * (R * ((fsCorr6 0 : ℝ)) ^ 2)) := hkey.symm
    _ ≤ lagTwoConstantSix ε * MassGap.wilsonCorrAt 5 β 0 :=
        mul_le_mul_of_nonneg_left hlower hcnn

/-! ## 4. The complementary coupling range -/

/-- The complementary range, as a `Prop`: `MiddleIntervalLagTwoSix K B` asserts
`wilsonCorrAt 5 β 2 ≤ K * wilsonCorrAt 5 β 0` for every `β` with `0 ≤ β ≤ B`. Nothing in this module
proves it; `confines_of_arms_six` takes it as a hypothesis.

DERIVED: `5` is the APERTURE — `wilsonCorrAt 5` is the extent-six torus (`5 + 1 = 6`) — and `2` and
`0` are the LAGS the ratio relates. The `0` in `0 ≤ β` is the bottom of the coupling range, where the
half-line the weak arm does not reach begins; `K` and `B` are variables, not numbers. -/
def MiddleIntervalLagTwoSix (K B : ℝ) : Prop :=
  ∀ β : ℝ, 0 ≤ β → β ≤ B → MassGap.wilsonCorrAt 5 β 2 ≤ K * MassGap.wilsonCorrAt 5 β 0

/-- The two ranges combine. Given `ε ≤ (epsMaxSix : ℝ)`, a bound `hfar` holding for every `β ≥ B`
and `hmid : MiddleIntervalLagTwoSix (lagTwoConstantSix ε) B` covering `0 ≤ β ≤ B`, the conclusion is
`ApertureRoute.ConfinesAtAnAperture`. The proof supplies `lagTwoConstantSix ε` and
`lagTwoConstantSix_lt_threshold` to `LagTwoSix.confines_of_lagTwoRatioSix`, splitting on
`le_total β B` to choose between `hmid` and `hfar`.

Scope: `B` is shared between the two hypotheses and appears in both, so no gap is left between the
ranges. `hmid` is a hypothesis; nothing here proves it.

DERIVED: no numeral occurs in the statement. `B` and `ε` are variables, and both bounds are named
definitions. -/
theorem confines_of_arms_six {ε B : ℝ} (hε : ε ≤ (epsMaxSix : ℝ))
    (hfar : ∀ β : ℝ, B ≤ β →
      MassGap.wilsonCorrAt 5 β 2 ≤ lagTwoConstantSix ε * MassGap.wilsonCorrAt 5 β 0)
    (hmid : MiddleIntervalLagTwoSix (lagTwoConstantSix ε) B) :
    ApertureRoute.ConfinesAtAnAperture := by
  refine MassGap.LagTwoSix.confines_of_lagTwoRatioSix
    ⟨lagTwoConstantSix ε, lagTwoConstantSix_lt_threshold hε, fun β hβ => ?_⟩
  rcases le_total β B with hle | hge
  · exact hmid β hβ hle
  · exact hfar β hge

/-! ## 5. Footprints -/

section Audit
#print axioms hatSq6
#print axioms lagPhase6
#print axioms fsTerm6
#print axioms fsCorr6
#print axioms clearDen6_exact
#print axioms zero_momentum_term_vanishes6
#print axioms fsCorr6_zero
#print axioms fsCorr6_one
#print axioms fsCorr6_two
#print axioms fsCorr6_three
#print axioms fsCorr6_fold
#print axioms freeRatioSix
#print axioms freeRatioSix_eq
#print axioms freeRatioSix_pos
#print axioms freeRatioSix_lt_freeRatio
#print axioms EffectiveGaussianLagTwoSix
#print axioms lagTwoConstantSix
#print axioms epsMaxSix
#print axioms inflationSix_le
#print axioms lagTwoConstantSix_lt_threshold
#print axioms effective_lag_two_bound_six
#print axioms MiddleIntervalLagTwoSix
#print axioms confines_of_arms_six
end Audit

end MassGap.FreeFieldLagTwoSix
