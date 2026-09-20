import Mathlib
import MassGap.LagTwoSix
import MassGap.FreeFieldLagTwo

/-!
# MassGap.FreeFieldLagTwoSix — the same weak-coupling arm at extent six, where the room is 65×

`FreeFieldLagTwo` builds the effective weak-coupling lag-two bound at extent four, where the
free-field value `5329/3186225 = 0.0016725` sits `11.1×` under `LagTwoBound.lagTwoThreshold`. This
file does the same at extent six, and the room is not `11×` but `65×`.

## Why extent six is the better target, in two numbers

`LagTwoSix.lagTwoThresholdSix_gt` puts the extent-six threshold above `0.0337`, against `0.018623`
at extent four — `1.81×` more permissive, which `LagTwoSix` already proved. What that file did NOT
have is the other factor. The free-field ratio must be read at the extent's OWN correlation, and

    extent four:  ρ(2)/ρ(0) → 5329/3186225       = 0.00167251
    extent six:   ρ(2)/ρ(0) → 34515625/67215229081 = 0.00051351

— a further `3.26×` down, because at extent four lag two is the ANTIPODAL lag and collects the torus
both ways round, while at extent six it is an interior lag. The two factors compound:

    extent four margin  11.1×,   admissible relative error  ε ≤ 5/6  = 0.833
    extent six  margin  65.6×,   admissible relative error  ε ≤ 24/25 = 0.96

So the leading-order Gaussian calculation may be wrong by **96% relatively, at every lag, in the
worst direction at each**, and the extent-six obligation still closes, with `1.34×` of the room left
unspent. That is the strongest form of the point `FreeFieldLagTwo` makes at extent four.

What it is NOT is a derivation. As at extent four, the named hypothesis implies its conclusion by
elimination of the free scale `R`; what this file adds is the exact constant, proved, and the size of
the room around it. See `FreeFieldLagTwo`'s header.

## What is PROVED here

The same shape as `FreeFieldLagTwo`, at extent six. The extent-six momenta are `p_μ = πk_μ/3`, so
`p̂_μ² = 2 − 2cos p_μ` is `0, 1, 3, 4, 3, 1` — integers again — and the lag phase `cos(p₂d)` is a
HALF-integer, carried here doubled. That factor of two is the same at every lag and cancels in the
ratio; `clearDen6 = 720720` is the lcm of `1 … 16`, the values `p̂²` takes, and `clearDen6_exact`
checks it clears every one of them over all `1296` momenta. The four values are decided by the
kernel and reported in `fsCorr6_zero`, `fsCorr6_one`, `fsCorr6_two`, `fsCorr6_three`.

## What is ASSUMED, ONCE

`EffectiveGaussianLagTwoSix ε`, the extent-six twin of `FreeFieldLagTwo.EffectiveGaussianLagTwo`:
one scale, an upper bound at ALL SIX lags and a lower bound at the contact lag only. `FreeFieldLagTwo.two_lag_form_collapses` is the
reason its upper bound is not restricted to the two lags the conclusion names: restricted that way it
would be equivalent to its own conclusion. It is OPEN.

## What this does NOT do

As at extent four, the bound starts at `B`. `MiddleIntervalLagTwoSix` names the rest and
`confines_of_arms_six` assembles the two through `LagTwoSix.confines_of_lagTwoRatioSix`.

Foundational footprint on every declaration (`#print axioms`, §5).
The module is NOT in the library root's import list.
Build: `python research/code/lean_build.py build MassGap.FreeFieldLagTwoSix`.
Numerals produced and cross-checked by `research/code/certify/free_field_lag_two_ratio.py`.
-/

namespace MassGap.FreeFieldLagTwoSix

open Finset

/-! ## 1. The exact free-field propagator data on the periodic `6⁴` torus

DERIVED throughout: `6` is the periodic extent `wilsonCorrAt 5` runs on (`5 + 1 = 6`), `4` is the
dimension of the problem, and `0, 1, 2` name the plaquette plane and the lag direction as
`WilsonBridge.corrClay` fixes them. -/

/-- `p̂² = 2 − 2cos(2πk/6)` at extent six, as a natural number.

DERIVED: evaluating `2 − 2cos(2πk/6)` at `k = 0 … 5` gives `0, 1, 3, 4, 3, 1`. Every entry is a value
of that expression. -/
def hatSq6 : Fin 6 → ℕ := ![0, 1, 3, 4, 3, 1]

/-- **Twice** the lag phase, `2cos(2πkd/6)`, as an integer.

DERIVED: `2cos(2πm/6)` is `2, 1, −1, −2, −1, 1` at `m = 0 … 5`; the doubling is what makes the phase
an integer and it is the SAME at every lag, so it cancels in every ratio. The argument is `k·d`
reduced mod the extent, which is `Fin 6` multiplication. -/
def lagPhase6 (k d : Fin 6) : ℤ := ![2, 1, -1, -2, -1, 1] (k * d)

/-- **The common denominator.** `720720 = lcm{1,…,16}`.

DERIVED: `p̂²` is a sum of four values from `{0,1,3,4}`, so its nonzero values lie in `1 … 16`, and
`720720` is their least common multiple. `clearDen6_exact` checks it. -/
def clearDen6 : ℕ := 720720

/-- `p̂² = ∑_μ p̂_μ²` at the momentum `(a, b, c, e)`. -/
def momSq6 (a b c e : Fin 6) : ℕ := hatSq6 a + hatSq6 b + hatSq6 c + hatSq6 e

/-- The plaquette-plane numerator `p̂₀² + p̂₁²`. -/
def planeNum6 (a b : Fin 6) : ℕ := hatSq6 a + hatSq6 b

/-- One momentum's contribution to `2·V·720720·D(d)`. -/
def fsTerm6 (d a b c e : Fin 6) : ℤ :=
  if momSq6 a b c e = 0 then 0
  else lagPhase6 c d * (planeNum6 a b * (clearDen6 / momSq6 a b c e) : ℕ)

/-- **THE FREE-FIELD FIELD-STRENGTH CORRELATION AT LAG `d`, EXTENT SIX**, as the exact integer
`2·V·720720·D(d)`.

DERIVED: no numeral. The overall `2·V·720720` is lag-independent and cancels in every ratio. -/
def fsCorr6 (d : Fin 6) : ℤ := ∑ a, ∑ b, ∑ c, ∑ e, fsTerm6 d a b c e

/-- **`720720` clears every denominator**, over all `1296` momenta. -/
theorem clearDen6_exact (a b c e : Fin 6) (h : momSq6 a b c e ≠ 0) :
    momSq6 a b c e * (clearDen6 / momSq6 a b c e) = clearDen6 := by
  revert h; revert a b c e; decide

/-- **The zero momentum contributes nothing**, numerator and denominator alike, so no zero-mode
subtraction is performed and none is available to be got wrong. -/
theorem zero_momentum_term_vanishes6 (a b c e : Fin 6) (h : momSq6 a b c e = 0) :
    planeNum6 a b = 0 := by
  revert h; revert a b c e; decide

theorem fsCorr6_zero : fsCorr6 0 = 933332400 := by decide

theorem fsCorr6_one : fsCorr6 1 = 128163984 := by decide

theorem fsCorr6_two : fsCorr6 2 = 21150000 := by decide

theorem fsCorr6_three : fsCorr6 3 = 7678032 := by decide

/-- **CIRCLE SYMMETRY, MACHINE-CHECKED.** `D(4) = D(2)` and `D(5) = D(1)` on the extent-six torus. -/
theorem fsCorr6_fold : fsCorr6 4 = fsCorr6 2 ∧ fsCorr6 5 = fsCorr6 1 := by
  constructor <;> decide

/-! ## 2. The ratio -/

/-- **THE FREE-FIELD LAG-TWO RATIO AT EXTENT SIX**, `(D(2)/D(0))²`. -/
def freeRatioSix : ℚ := ((fsCorr6 2 : ℚ) / (fsCorr6 0 : ℚ)) ^ 2

/-- `freeRatioSix = (5875/259259)² = 34515625/67215229081 = 0.000513509…` — `3.26×` below the
extent-four value, because lag two is an interior lag at extent six and the antipodal one at extent
four.

DERIVED: the two numerals are `fsCorr6 2` and `fsCorr6 0`, both decided above; the `2` is Wick's
square. -/
theorem freeRatioSix_eq : freeRatioSix = 34515625 / 67215229081 := by
  rw [freeRatioSix, fsCorr6_two, fsCorr6_zero]; norm_num

theorem freeRatioSix_pos : 0 < freeRatioSix := by rw [freeRatioSix_eq]; norm_num

/-- **THE EXTENT-SIX FREE-FIELD RATIO IS BELOW THE EXTENT-FOUR ONE**, as rationals. The relief the
extent buys is therefore TWO factors, not one: `LagTwoSix.lagTwoThreshold_lt_lagTwoThresholdSix`
raises the bar by `1.81×`, and this lowers what has to clear it by `3.26×`. -/
theorem freeRatioSix_lt_freeRatio : freeRatioSix < MassGap.FreeFieldLagTwo.freeRatio := by
  rw [freeRatioSix_eq, MassGap.FreeFieldLagTwo.freeRatio_eq]; norm_num

/-! ## 3. The named open hypothesis, and the effective bound

DERIVED: `5` is the extent index with `5 + 1 = 6`, the extent `LagTwoSix` works at; `2` and `0` are
lag indices. `24/25` is the one CHOSEN numeral — see its note. -/

/-- **THE ONE OPEN HYPOTHESIS AT EXTENT SIX.** Beyond an explicit coupling `B` there is ONE positive
scale `R` with `ρ(d) ≤ (1+ε)·R·D(d)²` at EVERY lag and `ρ(0) ≥ (1−ε)·R·D(0)²` at the contact lag.

The upper bound ranges over all six lags for the reason `FreeFieldLagTwo.two_lag_form_collapses`
proves: restricted to the two lags the conclusion names, a free scale can always be chosen exactly
when the conclusion already holds, and the reduction would assume what it concludes.

It is ONE-SIDED everywhere but the contact lag, deliberately. A two-sided sandwich at every lag would
assert `ρ(2) > 0`, which nothing in this tree supports; only `ρ(0) > 0` is asserted, and
`PlaqVariance.corrClay_zero_pos` proves it.

OPEN. Nothing in this tree proves it, this file does not, and no measurement may be substituted for
it. And, as at extent four, the implication it feeds is an elimination of `R`, not a derivation:
what this file contributes is the exact constant and the size of the room around it. -/
def EffectiveGaussianLagTwoSix (ε : ℝ) : Prop :=
  ∃ B : ℝ, ∀ β : ℝ, B ≤ β → ∃ R : ℝ, 0 < R ∧
    (∀ d : Fin 6, MassGap.wilsonCorrAt 5 β d ≤ (1 + ε) * (R * ((fsCorr6 d : ℝ)) ^ 2)) ∧
    (1 - ε) * (R * ((fsCorr6 0 : ℝ)) ^ 2) ≤ MassGap.wilsonCorrAt 5 β 0

/-- **THE CONSTANT THE HYPOTHESIS DELIVERS AT EXTENT SIX.** -/
noncomputable def lagTwoConstantSix (ε : ℝ) : ℝ :=
  ((1 + ε) / (1 - ε)) * ((fsCorr6 2 : ℝ) / (fsCorr6 0 : ℝ)) ^ 2

/-- **THE ADMISSIBLE RELATIVE ERROR AT EXTENT SIX.**

CHOSEN, and rounded DOWN — away from the claim `lagTwoConstantSix ε < lagTwoThresholdSix`, so the
rounding cannot manufacture the inequality. The exact supremum against
`LagTwoSix.lagTwoThresholdSix_gt`'s bracket `0.0337` is `0.96998…`, where `(1+ε)/(1−ε)` reaches
`0.0337/0.000513509 = 65.62…`. `24/25` spends only `49` of that `65.6`, leaving `1.34×` unspent, and
any `ε` below `0.96998` would serve. -/
def epsMaxSix : ℚ := 24 / 25

/-- `(1+ε)/(1−ε) ≤ 49` for `ε ≤ 24/25`. Nonnegativity of `ε` is not needed — `ε ≤ 24/25` puts
`1 − ε` above `1/25`. -/
theorem inflationSix_le {ε : ℝ} (hε : ε ≤ (epsMaxSix : ℝ)) : (1 + ε) / (1 - ε) ≤ 49 := by
  have he : ε ≤ 24 / 25 := by rw [epsMaxSix] at hε; norm_num at hε; linarith
  have hden : (0 : ℝ) < 1 - ε := by linarith
  rw [div_le_iff₀ hden]
  linarith [he]

/-- **THE CONSTANT CLEARS THE EXTENT-SIX THRESHOLD** for every admissible `ε`.

`49 · (21150000/933332400)² = 1691265625/67215229081 = 0.0251622…`, and
`LagTwoSix.lagTwoThresholdSix_gt` puts the threshold above `0.0337`. -/
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

/-- **THE DELIVERABLE AT EXTENT SIX — an EFFECTIVE weak-coupling lag-two bound with an explicit
constant**, and `65.6×` of room rather than `11.1×`. -/
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

/-! ## 4. What is still missing, named -/

/-- **THE SECOND OPEN PIECE AT EXTENT SIX — the middle interval.** -/
def MiddleIntervalLagTwoSix (K B : ℝ) : Prop :=
  ∀ β : ℝ, 0 ≤ β → β ≤ B → MassGap.wilsonCorrAt 5 β 2 ≤ K * MassGap.wilsonCorrAt 5 β 0

/-- **THE TWO ARMS ASSEMBLE AT EXTENT SIX**, through `LagTwoSix.confines_of_lagTwoRatioSix`. The `B`
is shared and explicit, for the reason `FreeFieldLagTwo.confines_of_arms` records. -/
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
