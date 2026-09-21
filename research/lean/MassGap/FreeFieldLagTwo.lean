import Mathlib
import MassGap.LagTwoBound

/-!
# MassGap.FreeFieldLagTwo — the weak-coupling lag-two arm, reduced to ONE named open hypothesis

`LagTwoBound.LagTwoRatio` asks for `ρ(2) ≤ K·ρ(0)` at every `β ≥ 0` with `K < lagTwoThreshold`, and
`LagTwoBound.exists_cut_lag_two_ratio` supplies it on a derived interval `[0, b]` from the strong
side. This file builds the OTHER end: an EFFECTIVE weak-coupling form,

    ∃ B, ∀ β ≥ B,  wilsonCorrAt 3 β 2  ≤  K · wilsonCorrAt 3 β 0,     K < lagTwoThreshold,

with `K` an explicit rational and `B` whatever the one named hypothesis supplies. A bare
`Tendsto (fun β => ρ(2)/ρ(0)) atTop _` would not do: it gives no `B`, so it cannot meet an interval
coming the other way.

## What is PROVED here, with no hypothesis

**The free-field field-strength correlation on the periodic `4⁴` torus, exactly.** At extent four the
momenta are `p_μ = πk_μ/2`, so the lattice momentum square `p̂_μ² = 2 − 2cos p_μ` takes the INTEGER
values `0, 2, 4, 2` and the lag phase `cos(p₂d)` takes the values `0, ±1`. The Feynman-gauge
field-strength two-point function

    D(d) = (1/V) ∑_k cos(p₂ d) · (p̂₀² + p̂₁²) / p̂²

is therefore a finite sum of RATIONALS, not an analysis problem. `fsCorr` is `V·1680·D` as an
integer — `1680` is the least common multiple of the even numbers up to `16`, which are the only
values `p̂²` takes, and `clearDen_exact` machine-checks that it clears every one of them. The three
values are decided by the kernel:

    fsCorr 0 = 214200,   fsCorr 1 = 29640,   fsCorr 2 = 8760,   fsCorr 3 = fsCorr 1,

so `D(2)/D(0) = 73/1785` exactly and `freeRatio = (73/1785)² = 5329/3186225` (`freeRatio_eq`).

**No zero mode is subtracted, because none can contribute.** At `k = 0` the NUMERATOR `p̂₀² + p̂₁²`
vanishes with the denominator, so the `k = 0` term is `0` under any convention
(`zero_momentum_term_vanishes`). The usual `∑_{k≠0}` prescription for a gauge propagator is not a
choice being made here, and the gauge-fixing worry that attaches to it does not arise for this
observable.

**Gauge fixing does not arise for this observable, and not by a cancellation either.**
`fieldStrength_pure_gauge_orthogonal` proves that the field-strength vertex contracted with the
pure-gauge direction is zero AS A POLYNOMIAL IDENTITY in two free complex variables — it is the
antisymmetry of `F` in its indices, with no condition on the momenta at all. Every covariant gauge
differs from Feynman gauge by a term carrying that contraction, so `D(d)` is gauge-independent at
every momentum and the gauge choice is not an input to the numbers above.

## What is ASSUMED, ONCE

`EffectiveGaussianLagTwo ε` — that beyond some coupling `B` there is ONE positive scale `R` with
`ρ(d) ≤ (1+ε)·R·D(d)²` at EVERY lag and `ρ(0) ≥ (1−ε)·R·D(0)²` at the contact lag. That is the
effective form of "the `β → ∞` measure concentrates on the flat connections and Wick's theorem
applies". It is OPEN. Nothing in this tree proves it, nothing here proves it, and no measurement may
be substituted for it.

**AND THE IMPLICATION IT FEEDS IS AN UNWRAPPING, NOT A DERIVATION.** Eliminating the free `R` turns
the hypothesis into the family of bounds `ρ(d) ≤ ((1+ε)/(1−ε))·(D(d)/D(0))²·ρ(0)`, and the
conclusion is its `d = 2` member. `effective_lag_two_bound` therefore does no analytic work: it
carries the constant. What this file contributes is §§1–3 and §5b — the exact constant, the
gauge-independence of the object it is a constant OF, and the proof that no coupling-uniform
argument can produce any constant below one — together with the statement of the remaining
obligation in the currency a weak-coupling analysis actually produces: a relative error on a
remainder.

It IS strictly stronger than its conclusion (it bounds lags `1` and `3` as well), and it asserts no
positivity beyond `ρ(0) > 0`, which `PlaqVariance.corrClay_zero_pos` proves. Both of those are
deliberate: `two_lag_form_collapses` shows that the two-lag version would be equivalent to its own
conclusion, and an earlier two-sided-at-every-lag version additionally asserted `ρ(2) > 0`, which
nothing in this tree supports.

## The number that matters: how wrong the Gaussian remainder may be

`lagTwoConstant ε = ((1+ε)/(1−ε))·(73/1785)²` is what the hypothesis delivers, and
`lagTwoConstant_lt_threshold` proves it is below `lagTwoThreshold` for every `ε ≤ 5/6`. So the
leading-order calculation may be wrong by **83% relatively, at every lag, in the worst direction at
each**, and the extent-four obligation still closes. The free-field value is `11.13×` under the
threshold; `5/6` spends `11×` of that, leaving `1.2%`. `5/6` is a CAP, not a recommendation — the
theorem holds at every smaller `ε`, and a smaller `ε` is a stronger assumption, so nothing is gained
by not taking the largest one provable. `MassGap.FreeFieldLagTwoSix` runs the same argument at
extent six, where the room is `65.6×` and the cap is `24/25`.

That is the useful output: the margin does not remove the need for the leading term, it removes the
need for a SHARP remainder.

## What this does NOT do

It does not give `LagTwoBound.LagTwoRatio`, which is quantified over ALL `β ≥ 0`.
`MiddleIntervalLagTwo` names exactly what is missing — the same bound on `[0, B]` — and
`confines_of_arms` assembles the two into `ApertureRoute.ConfinesAtAnAperture`. Today the strong arm
reaches `b_Lean = 3.34933686e−18` — the figure `certify/lag_two_strong_arm_reach.py` prints, in the
Lean coupling convention, not the `b_std = 6.70e−18` of the standard one — and nothing covers the
interval between; that is a statement about the two arms, not about this file.

Foundational footprint on EVERY declaration, the assembly corollary included (`#print axioms`, §6):
a subset of `propext`, `Classical.choice`, `Quot.sound`, with no cited axiom anywhere. The purely
computational declarations print `propext` alone.

The module is in the library root's import list, so repository-wide sweeps cover it.
Build: `python research/code/lean_build.py build MassGap.FreeFieldLagTwo`.
Numerals produced and cross-checked by `research/code/certify/free_field_lag_two_ratio.py`.
-/

namespace MassGap.FreeFieldLagTwo

open Finset

/-! ## 1. The exact free-field propagator data on the periodic `4⁴` torus

DERIVED throughout this section: `4` is both the dimension of the Yang-Mills problem and the periodic
extent `wilsonCorrAt 3` runs on (`3 + 1 = 4`); the two coincide and neither is chosen here. The
indices `0, 1` name the plaquette plane and `2` the transverse direction the lag runs along, exactly
as `WilsonBridge.corrClay` fixes them — a naming freedom on a periodic lattice, not a magnitude. -/

/-- **The lattice momentum square** `p̂² = 2 − 2cos(2πk/4)` at extent four, as a natural number.

DERIVED: `2 − 2cos` is the momentum square of the nearest-neighbour lattice Laplacian and
`2πk/4` is the periodic momentum; evaluating gives `0, 2, 4, 2`. Every entry is a value of that
expression, and none is chosen. -/
def hatSq : Fin 4 → ℕ := ![0, 2, 4, 2]

/-- **The lag phase** `cos(2πkd/4)`, as an integer.

DERIVED: `cos(2πm/4)` is `1, 0, −1, 0` at `m = 0, 1, 2, 3`, and the argument is `k·d` reduced mod the
extent — which is what `Fin 4` multiplication is. No entry is chosen. -/
def lagPhase (k d : Fin 4) : ℤ := ![1, 0, -1, 0] (k * d)

/-- **The common denominator.** `1680 = lcm{2,4,6,8,10,12,14,16}`.

DERIVED: `p̂²` is a sum of four values from `{0,2,4}`, so its nonzero values are exactly the even
numbers from `2` to `16`, and `1680` is their least common multiple. `clearDen_exact` checks that it
divides every one of them, so this is a fact about the value set rather than a choice. -/
def clearDen : ℕ := 1680

/-- `p̂² = ∑_μ p̂_μ²` at the momentum `(a, b, c, e)`.

DERIVED: the `4` is `Fin 4`, the extent of the torus, so `a b c e` are momentum INDICES. There are
four of them because the problem is four-dimensional, and the sum runs over all of them because that
is what `∑_μ` means. -/
def momSq (a b c e : Fin 4) : ℕ := hatSq a + hatSq b + hatSq c + hatSq e

/-- The plaquette-plane numerator `p̂₀² + p̂₁²` — the transverse contraction of the field-strength
vertex with the Feynman-gauge propagator.

DERIVED: the `4` is `Fin 4`, the extent, so `a` and `b` are momentum indices. Two of them because a
plaquette spans a PLANE, and `WilsonBridge.corrClay` fixes that plane to be `0, 1`. -/
def planeNum (a b : Fin 4) : ℕ := hatSq a + hatSq b

/-- One momentum's contribution to `V·1680·D(d)`. The `k = 0` momentum is sent to `0`; it would be
`0` anyway (`zero_momentum_term_vanishes`).

DERIVED: the `4` is `Fin 4`, the extent, so `d a b c e` are indices. The `1680` is `clearDen`, the
lcm derived there, and the `0` is a GUARD on the zero momentum, not a value — it selects the branch,
and `zero_momentum_term_vanishes` proves the other branch would return `0` there in any case. -/
def fsTerm (d a b c e : Fin 4) : ℤ :=
  if momSq a b c e = 0 then 0
  else lagPhase c d * (planeNum a b * (clearDen / momSq a b c e) : ℕ)

/-- **THE FREE-FIELD FIELD-STRENGTH CORRELATION AT LAG `d`**, as the exact integer `V·1680·D(d)`.

DERIVED: no numeral. The sum runs over the four momentum components of the four-dimensional torus;
the overall `V·1680` is a lag-independent scale, so it cancels in every ratio this file forms. -/
def fsCorr (d : Fin 4) : ℤ := ∑ a, ∑ b, ∑ c, ∑ e, fsTerm d a b c e

/-- **`1680` really does clear every denominator.** At every momentum with `p̂² ≠ 0`,
`p̂² · (1680 / p̂²) = 1680`, so `fsCorr` is an exact rescaling of `D` and not a truncation. Decided
over all `256` momenta. -/
theorem clearDen_exact (a b c e : Fin 4) (h : momSq a b c e ≠ 0) :
    momSq a b c e * (clearDen / momSq a b c e) = clearDen := by
  revert h; revert a b c e; decide

/-- **The zero momentum contributes nothing, numerator and denominator alike.** Its plane numerator
`p̂₀² + p̂₁²` vanishes exactly where `p̂²` does, so no zero-mode subtraction is being performed and
none is available to be got wrong. -/
theorem zero_momentum_term_vanishes (a b c e : Fin 4) (h : momSq a b c e = 0) :
    planeNum a b = 0 := by
  revert h; revert a b c e; decide

/-! ### The three values, decided -/

/-- `V·1680·D(0) = 214200`, i.e. `D(0) = 255/512`. -/
theorem fsCorr_zero : fsCorr 0 = 214200 := by decide

/-- `V·1680·D(1) = 29640`, i.e. `D(1) = 247/3584`. -/
theorem fsCorr_one : fsCorr 1 = 29640 := by decide

/-- `V·1680·D(2) = 8760`, i.e. `D(2) = 73/3584`. -/
theorem fsCorr_two : fsCorr 2 = 8760 := by decide

/-- **CIRCLE SYMMETRY, MACHINE-CHECKED.** `D(3) = D(1)` on the extent-four torus, because lags `3`
and `1` are the same distance apart on a circle of circumference four. The lag-three constraint in
`EffectiveGaussianLagTwo` therefore costs nothing beyond the lag-one one. -/
theorem fsCorr_three : fsCorr 3 = fsCorr 1 := by decide

/-! ## 2. The ratio the Wilson observable inherits

By Wick, the connected plaquette correlation of a Gaussian fluctuation field is `R · D(d)²` with `R`
— the colour factor, the coupling normalisation and the lattice spacing together — INDEPENDENT of
the lag. `sq_ratio_of_square_law` is that cancellation, and it is all the Wick step contributes to a
RATIO. -/

/-- **THE FREE-FIELD LAG-TWO RATIO**, `(D(2)/D(0))²`, as a rational.

DERIVED: `2` and `0` are LAGS, not magnitudes — the lag the claim is about and the contact lag it is
normalised against, exactly the pair `LagTwoBound.LagTwoRatio` relates. The outer `2` is the square
Wick's theorem puts on the propagator. The value is `fsCorr`'s, decided above. -/
def freeRatio : ℚ := ((fsCorr 2 : ℚ) / (fsCorr 0 : ℚ)) ^ 2

/-- `freeRatio = (73/1785)² = 5329/3186225 = 0.00167251…`.

DERIVED: the two numerals are `fsCorr 2` and `fsCorr 0`, both decided above; the `2` is the square
Wick's theorem puts on the propagator. Nothing is chosen and nothing is measured. -/
theorem freeRatio_eq : freeRatio = 5329 / 3186225 := by
  rw [freeRatio, fsCorr_two, fsCorr_zero]; norm_num

theorem freeRatio_pos : 0 < freeRatio := by rw [freeRatio_eq]; norm_num

/-- **The lag-independent scale cancels.** If `ρ d = R · (G d)²` with `R > 0`, the lag-two ratio is
`(G 2 / G 0)²` and carries no `R`. This is the entirety of what the Gaussian reduction contributes
to a RATIO; the fourth-moment identity behind `ρ ∝ G²` is NOT proved here and is folded into
`EffectiveGaussianLagTwo`. -/
theorem sq_ratio_of_square_law {ρ G : ℕ → ℝ} {R : ℝ} (hR : 0 < R) (hG0 : G 0 ≠ 0)
    (h : ∀ d, ρ d = R * (G d) ^ 2) : ρ 2 / ρ 0 = (G 2 / G 0) ^ 2 := by
  rw [h 2, h 0, div_pow]
  field_simp

/-! ## 3. Gauge fixing does not arise for this observable

The propagator in §1 is written in Feynman gauge with the zero mode dropped, and the natural worry
is that a gauge-invariant observable has been read off a gauge-dependent object. It has not, and the
reason is stronger than a cancellation between terms. -/

/-- **THE FIELD STRENGTH IS ORTHOGONAL TO THE PURE-GAUGE DIRECTION, AS A POLYNOMIAL IDENTITY.**

A gauge transformation moves `A_μ(x)` by `ω(x+μ̂) − ω(x)`, whose momentum-space direction is
`g_μ = e^{ip_μ} − 1`; writing `a = e^{ip₀}` and `b = e^{ip₁}` that is `g₀ = a − 1`, `g₁ = b − 1`. The
vertex of the lattice field strength `F₀₁ = Δ₀A₁ − Δ₁A₀` is `v₀ = −(b − 1)`, `v₁ = a − 1`. Their
contraction is

    g₀·v₀ + g₁·v₁ = (a−1)·(−(b−1)) + (b−1)·(a−1) = 0,

by `ring` — an identity in two FREE complex variables, with no condition on `a` or `b` whatever. It
is the antisymmetry of `F` in its two indices and nothing else.

**WHAT THAT SETTLES.** A covariant gauge's propagator differs from Feynman gauge by a term
proportional to the longitudinal projector built from `g`, and every such term meets the vertex
through this contraction. So `D(d)` is the same in every covariant gauge at every momentum, and the
gauge choice is not an input to §1. The zero-mode prescription is likewise not an input
(`zero_momentum_term_vanishes`).

**AND THERE IS NOTHING HERE TO GUARD.** An earlier version of this file claimed the cancellation
depended on the lattice phases and offered a negative control for it. That was wrong: unit modulus
is never used, and no substitution into the gauge direction can make this contraction nonzero. The
guard that does have teeth is that the surviving TRANSVERSE part is not itself zero, which is
`fsCorr_zero_ne_zero`.

DERIVED: no numeral. Each `1` is the `1` of `e^{ip} − 1`. -/
theorem fieldStrength_pure_gauge_orthogonal (a b : ℂ) :
    (a - 1) * (-(b - 1)) + (b - 1) * (a - 1) = 0 := by ring

/-- **THE TRANSVERSE PART IS NOT ZERO.** Without this, §1 could be computing an identically
vanishing object and every ratio in it would be meaningless. -/
theorem fsCorr_zero_ne_zero : fsCorr 0 ≠ 0 := by rw [fsCorr_zero]; norm_num

/-! ## 4. The named open hypothesis, and the effective bound it buys

DERIVED in this section: `2` and `0` are lag indices; `3` is the extent index with `3 + 1 = 4`, the
extent `LagTwoBound` works at. `5/6` is the one CHOSEN numeral and it is chosen conservatively — see
its note. -/

/-- **THE ONE OPEN HYPOTHESIS — the effective Gaussian approximation at the two lags that matter.**

Beyond an explicit coupling `B` there is ONE positive scale `R` such that the connected correlation
is at most `(1+ε)·R·D(d)²` at EVERY lag, and at least `(1−ε)·R·D(0)²` at the contact lag. The scale
`R` absorbs the colour factor, the coupling normalisation and the lattice spacing; it is allowed to
depend on `β`, which is what makes this a statement about the RATIO and nothing else.

This is the effective form of three things at once: that the `β → ∞` measure concentrates on the
flat connections, that the fluctuation determinant makes the plaquette correlation the SQUARE of the
field-strength propagator by Wick, and that the `O(1/β)` remainder is uniform enough to survive
passing to the ratio. It is OPEN. Nothing in this tree proves it, this file does not, and no
measurement may be substituted for it.

**THE UPPER BOUND RANGES OVER EVERY LAG, AND THAT IS NOT DECORATION.** Restricted to the two lags
the conclusion names — upper at `2`, lower at `0` — this hypothesis is EQUIVALENT to the conclusion,
and the theorem below would be a tautology wearing a propagator: with `R` free and only two
constraints on it, `R` can be chosen exactly when the ratio bound already holds.
`two_lag_form_collapses` proves that equivalence, so the strengthening is machine-checked as
NECESSARY rather than asserted as prudent. Lag `3` costs nothing extra: `fsCorr 3 = fsCorr 1` by
circle symmetry (`fsCorr_three`).

**IT IS ONE-SIDED EVERYWHERE BUT THE CONTACT LAG, DELIBERATELY.** A two-sided sandwich at every lag
would assert `ρ(2) > 0` and `ρ(1) > 0`, which nothing in this tree supports and which — if the
connected correlation were a pure contact term — would be FALSE, making every conclusion drawn from
it empty. Only `ρ(0) > 0` is asserted here, and `PlaqVariance.corrClay_zero_pos` proves it. The
hypothesis remains strictly stronger than the conclusion, because it also bounds lags `1` and `3`.

**AND IT IMPLIES ITS CONCLUSION BY ELIMINATION OF `R`, NOT BY ANALYSIS.** See the header. The
theorem below carries the constant; it does not derive the bound.

DERIVED: nothing. `1 + ε` and `1 − ε` are the two ends of a symmetric relative error and `ε` is the
caller's. -/
def EffectiveGaussianLagTwo (ε : ℝ) : Prop :=
  ∃ B : ℝ, ∀ β : ℝ, B ≤ β → ∃ R : ℝ, 0 < R ∧
    (∀ d : Fin 4, MassGap.wilsonCorrAt 3 β d ≤ (1 + ε) * (R * ((fsCorr d : ℝ)) ^ 2)) ∧
    (1 - ε) * (R * ((fsCorr 0 : ℝ)) ^ 2) ≤ MassGap.wilsonCorrAt 3 β 0

/-- **THE CONSTANT THE HYPOTHESIS DELIVERS** — the free-field ratio inflated by the worst-case
relative error at each end.

DERIVED: `(1+ε)/(1−ε)` is the worst case of `(1+ε)·ρ_free(2)` over `(1−ε)·ρ_free(0)`, and the square
is Wick's. No numeral is chosen. -/
noncomputable def lagTwoConstant (ε : ℝ) : ℝ :=
  ((1 + ε) / (1 - ε)) * ((fsCorr 2 : ℝ) / (fsCorr 0 : ℝ)) ^ 2

/-- **THE ADMISSIBLE RELATIVE ERROR.**

CHOSEN, and rounded DOWN — away from the claim `lagTwoConstant ε < lagTwoThreshold`, so the rounding
cannot manufacture the inequality. The exact supremum against `LagTwoBound.lagTwoThreshold_gt`'s
bracket `0.018623` is `0.83518…`, where `(1+ε)/(1−ε)` reaches `0.018623/0.00167251 = 11.135…`.
`5/6` is the largest sixth below it and spends only `11` of that `11.135`. It decides nothing that
the closed form does not: `lagTwoConstant_lt_threshold` is proved from `freeRatio_eq` and
`lagTwoThreshold_gt`, and any `ε` below `0.83518` would serve. -/
def epsMax : ℚ := 5 / 6

/-- `(1+ε)/(1−ε) ≤ 11` for `ε ≤ 5/6`. Nonnegativity of `ε` is not needed here — `ε ≤ 5/6` alone
puts `1 − ε` above `1/6` — and is carried by the callers that do need it. -/
theorem inflation_le {ε : ℝ} (hε : ε ≤ (epsMax : ℝ)) : (1 + ε) / (1 - ε) ≤ 11 := by
  have he : ε ≤ 5 / 6 := by rw [epsMax] at hε; norm_num at hε; linarith
  have hden : (0 : ℝ) < 1 - ε := by linarith
  rw [div_le_iff₀ hden]
  linarith [he]

/-- **THE CONSTANT CLEARS THE EXTENT-FOUR THRESHOLD** for every admissible `ε`.

`11 · (8760/214200)² = 58619/3186225 = 0.0183977…`, and `LagTwoBound.lagTwoThreshold_gt` puts the
threshold above `0.018623`. -/
theorem lagTwoConstant_lt_threshold {ε : ℝ} (hε : ε ≤ (epsMax : ℝ)) :
    lagTwoConstant ε < MassGap.LagTwoBound.lagTwoThreshold := by
  have hinf := inflation_le hε
  have hsq : ((fsCorr 2 : ℝ) / (fsCorr 0 : ℝ)) ^ 2 = 5329 / 3186225 := by
    rw [fsCorr_two, fsCorr_zero]; norm_num
  have hnn : (0 : ℝ) ≤ ((fsCorr 2 : ℝ) / (fsCorr 0 : ℝ)) ^ 2 := sq_nonneg _
  have hstep : lagTwoConstant ε ≤ 11 * (5329 / 3186225) := by
    rw [lagTwoConstant, hsq]
    exact mul_le_mul_of_nonneg_right hinf (by norm_num)
  have hgt := MassGap.LagTwoBound.lagTwoThreshold_gt
  have : (11 : ℝ) * (5329 / 3186225) < 0.018623 := by norm_num
  linarith

/-- **THE TWO-LAG FORM WOULD BE THE CONCLUSION ITSELF.** With one free positive scale `R` and
constraints at exactly two lags, `R` can be chosen precisely when the ratio bound already holds. So
a version of `EffectiveGaussianLagTwo` restricted to lags `0` and `2` assumes what it concludes, and
the four-lag form is not a convenience. Kept as a theorem so the weaker statement cannot quietly
come back.

DERIVED: no numeral. `s0`, `s2` stand for the free-field values at the two lags and `r0`, `r2` for
the correlation's. -/
theorem two_lag_form_collapses {ε s0 s2 r0 r2 : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1) (hs0 : 0 < s0)
    (hs2 : 0 < s2) (hr0 : 0 < r0) :
    (∃ R : ℝ, 0 < R ∧ r2 ≤ (1 + ε) * (R * s2 ^ 2) ∧ (1 - ε) * (R * s0 ^ 2) ≤ r0)
      ↔ r2 ≤ ((1 + ε) / (1 - ε)) * (s2 / s0) ^ 2 * r0 := by
  have hden : (0 : ℝ) < 1 - ε := by linarith
  have hs0sq : (0 : ℝ) < s0 ^ 2 := by positivity
  have hs2sq : (0 : ℝ) < s2 ^ 2 := by positivity
  have h1e : (0 : ℝ) ≤ 1 + ε := by linarith
  have hcap : (0 : ℝ) < r0 / ((1 - ε) * s0 ^ 2) := by positivity
  have hval : (1 + ε) * ((r0 / ((1 - ε) * s0 ^ 2)) * s2 ^ 2)
      = ((1 + ε) / (1 - ε)) * (s2 / s0) ^ 2 * r0 := by
    field_simp
  have hfix : (1 - ε) * ((r0 / ((1 - ε) * s0 ^ 2)) * s0 ^ 2) = r0 := by
    field_simp
  constructor
  · rintro ⟨R, hR, hup, hlo⟩
    have hRle : R ≤ r0 / ((1 - ε) * s0 ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hlo]
    have hstep : (1 + ε) * (R * s2 ^ 2)
        ≤ (1 + ε) * ((r0 / ((1 - ε) * s0 ^ 2)) * s2 ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hRle hs2sq.le) h1e
    calc r2 ≤ (1 + ε) * (R * s2 ^ 2) := hup
      _ ≤ (1 + ε) * ((r0 / ((1 - ε) * s0 ^ 2)) * s2 ^ 2) := hstep
      _ = ((1 + ε) / (1 - ε)) * (s2 / s0) ^ 2 * r0 := hval
  · intro hb
    exact ⟨r0 / ((1 - ε) * s0 ^ 2), hcap, by rw [hval]; exact hb, hfix.le⟩

/-- **THE DELIVERABLE — an EFFECTIVE weak-coupling lag-two bound with an explicit constant.**

From the one open hypothesis at any admissible relative error, the lag-two ratio bound holds for
every `β ≥ B` with the EXPLICIT constant `lagTwoConstant ε`, proved strictly below
`LagTwoBound.lagTwoThreshold`. The `B` is the hypothesis's own, so it is as effective as the
hypothesis is — which is the point of stating the hypothesis effectively rather than as a limit. -/
theorem effective_lag_two_bound {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ (epsMax : ℝ))
    (h : EffectiveGaussianLagTwo ε) :
    ∃ B : ℝ, lagTwoConstant ε < MassGap.LagTwoBound.lagTwoThreshold ∧
      ∀ β : ℝ, B ≤ β →
        MassGap.wilsonCorrAt 3 β 2 ≤ lagTwoConstant ε * MassGap.wilsonCorrAt 3 β 0 := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, lagTwoConstant_lt_threshold hε, fun β hβ => ?_⟩
  obtain ⟨R, hR, hall, hlower⟩ := hB β hβ
  have hupper := hall 2
  have he : ε ≤ 5 / 6 := by rw [epsMax] at hε; norm_num at hε; linarith
  have hden : (0 : ℝ) < 1 - ε := by linarith
  have h0 : (fsCorr 0 : ℝ) = 214200 := by rw [fsCorr_zero]; norm_num
  have h2 : (fsCorr 2 : ℝ) = 8760 := by rw [fsCorr_two]; norm_num
  have hkey : lagTwoConstant ε * ((1 - ε) * (R * ((fsCorr 0 : ℝ)) ^ 2))
      = (1 + ε) * (R * ((fsCorr 2 : ℝ)) ^ 2) := by
    rw [lagTwoConstant, h0, h2]
    field_simp
  have hcnn : 0 ≤ lagTwoConstant ε := by
    rw [lagTwoConstant]
    exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (sq_nonneg _)
  calc MassGap.wilsonCorrAt 3 β 2
      ≤ (1 + ε) * (R * ((fsCorr 2 : ℝ)) ^ 2) := hupper
    _ = lagTwoConstant ε * ((1 - ε) * (R * ((fsCorr 0 : ℝ)) ^ 2)) := hkey.symm
    _ ≤ lagTwoConstant ε * MassGap.wilsonCorrAt 3 β 0 :=
        mul_le_mul_of_nonneg_left hlower hcnn

/-! ## 5. What is still missing, named

The bound above is effective but it starts at `B`. `LagTwoBound.LagTwoRatio` needs every `β ≥ 0`, so
exactly one interval is unaccounted for. -/

/-- **THE SECOND OPEN PIECE — the middle interval.** The same lag-two bound on `[0, B]`, which is
what `LagTwoBound.exists_cut_lag_two_ratio` supplies from the strong side but only out to a derived
cut. Naming it makes the remaining obligation exactly two propositions rather than a gap in prose.

DERIVED: no numeral here is a magnitude. `3` is the APERTURE — `wilsonCorrAt 3` is the extent-four
torus (`3 + 1 = 4`) this file's propagator data is computed on. `2` and `0` are the LAGS the ratio
relates. The `0` in `0 ≤ β` is the bottom of the coupling range, which is where the half-line the
weak arm does not reach begins; `B` is a variable and is deliberately not a number. -/
def MiddleIntervalLagTwo (K B : ℝ) : Prop :=
  ∀ β : ℝ, 0 ≤ β → β ≤ B → MassGap.wilsonCorrAt 3 β 2 ≤ K * MassGap.wilsonCorrAt 3 β 0

/-- **THE TWO ARMS ASSEMBLE.** The effective weak-coupling bound FROM `B` ON and the middle interval
UP TO THE SAME `B`, at the same constant, give the content of `LagTwoBound.LagTwoRatio` and hence
`ApertureRoute.ConfinesAtAnAperture`. Stated so that the join is a theorem and what is missing is a
hypothesis rather than a remark.

The `B` is shared and explicit on purpose. Quantifying the middle interval over EVERY `B` would have
made it the whole half-line and the weak arm redundant — the same failure mode
`two_lag_form_collapses` records one level down.

Its footprint is foundational: `LagTwoBound.confines_of_lag_two_ratio` reaches
`ConfinesZero.confines_extent_four_of_lag_two_small`, which does not consume
`Complete.wilson_reflection_positive_at`, so the assembly carries no cited axiom either. -/
theorem confines_of_arms {ε B : ℝ} (hε : ε ≤ (epsMax : ℝ))
    (hfar : ∀ β : ℝ, B ≤ β →
      MassGap.wilsonCorrAt 3 β 2 ≤ lagTwoConstant ε * MassGap.wilsonCorrAt 3 β 0)
    (hmid : MiddleIntervalLagTwo (lagTwoConstant ε) B) :
    ApertureRoute.ConfinesAtAnAperture := by
  refine MassGap.LagTwoBound.confines_of_lag_two_ratio (lagTwoConstant ε)
    (lagTwoConstant_lt_threshold hε) (fun β hβ => ?_)
  rcases le_total β B with hle | hge
  · exact hmid β hβ hle
  · exact hfar β hge

/-! ## 5b. Why the constant must come from the coupling, and not from positivity

The question this section answers is whether the factor-eleven room above the threshold lets a CRUDE
argument — one that never mentions `β` — reach it. It does not, and the reason is a single profile. -/

/-- **EVERY COUPLING-UNIFORM FACT THIS TREE PROVES OF THE EXTENT-FOUR CORRELATION IS SATISFIED BY THE
FLAT PROFILE, WHICH HAS RATIO EXACTLY ONE.**

The list is everything currently available at extent four that holds at every `β ≥ 0`:
nonnegativity and positive total mass (`Complete.wilson_reflection_positive_at_even`), circle
symmetry, log-convexity (`LogConvex.corrClay_log_convex`), contact dominance `ρ(2) ≤ ρ(0)`,
`LinkGram.wilson_lag_two_le_lag_one`'s `ρ(2) ≤ ρ(1)`, and `SlabQuadratic.wilson_quadratic`'s
`2ρ(1)² ≤ ρ(2)² + ρ(0)ρ(2)`. The last two are genuinely DYNAMICAL inputs, proved from reflection
positivity rather than from the shape cone, and the quadratic is INDEPENDENT of the rest —
`SpectralFour.missing_inequalities_independent` — so it has to be carried explicitly rather than
inferred.

`ρ ≡ 1` meets all seven, the quadratic with EQUALITY at `2 ≤ 2`, and defeats every `K < 1`. So no
combination of them — and no crude argument built only from them, however the pieces are assembled —
yields any constant below one, let alone one below `lagTwoThreshold ≈ 0.0186`. This sharpens
`TailRatio.no_strict_lag_bound_with_contact`, whose premise set stops before `LinkGram`'s bound, by
adding the two facts that were not in it.

That the quadratic is met with equality rather than slack is the reason this theorem survived the
quadratic landing after it was written: a profile meeting the binding constraint exactly is the
hardest case for a completeness claim, not the easiest.

**WHAT THAT MEANS FOR THE MARGIN.** The room between the free-field value and the threshold is a
factor of eleven, and it is entirely room for a REMAINDER. The leading term is not optional: the
lag-two ratio tends to a nonzero constant as `β → ∞`, so the bound must resolve a constant rather
than an order, and every coupling-uniform route resolves it only as far as one.

DERIVED: no numeral. `1` is the flat profile's constant value and the `2` is the square in
log-convexity. -/
theorem flat_profile_meets_every_uniform_fact :
    ∃ r : Fin 4 → ℝ,
      (∀ d, 0 ≤ r d) ∧ 0 < ∑ d, r d ∧
      r 3 = r 1 ∧
      r 1 ^ 2 ≤ r 0 * r 2 ∧
      r 2 ≤ r 0 ∧
      r 2 ≤ r 1 ∧
      2 * r 1 ^ 2 ≤ r 2 ^ 2 + r 0 * r 2 ∧
      ∀ K : ℝ, K < 1 → ¬ (r 2 ≤ K * r 0) := by
  refine ⟨fun _ => 1, fun _ => zero_le_one, ?_, rfl, by norm_num, le_rfl, le_rfl, by norm_num, ?_⟩
  · simp [Fin.sum_univ_four]
  · intro K hK h
    simp only [mul_one] at h
    linarith

/-- **AND THE FLAT PROFILE IS NOT NEAR THE TARGET.** It fails the criterion at the very constant the
route needs: `lagTwoThreshold · ρ(0) < ρ(2)` on it. So the distance from what coupling-uniform
positivity carries to what the route asks is not a margin to be tightened — it is the whole of the
`β`-dependence.

DERIVED: no numeral; `lagTwoThreshold` is a closed form and `LagTwoBound.lagTwoThreshold_lt` is what
places it under one. -/
theorem flat_profile_fails_the_threshold :
    ¬ ((1 : ℝ) ≤ MassGap.LagTwoBound.lagTwoThreshold * 1) := by
  have h := MassGap.LagTwoBound.lagTwoThreshold_lt
  intro hc
  rw [mul_one] at hc
  linarith

/-! ## 6. Footprints -/

section Audit
#print axioms hatSq
#print axioms lagPhase
#print axioms fsTerm
#print axioms fsCorr
#print axioms clearDen_exact
#print axioms zero_momentum_term_vanishes
#print axioms fsCorr_zero
#print axioms fsCorr_one
#print axioms fsCorr_two
#print axioms fsCorr_three
#print axioms freeRatio
#print axioms freeRatio_eq
#print axioms freeRatio_pos
#print axioms sq_ratio_of_square_law
#print axioms fieldStrength_pure_gauge_orthogonal
#print axioms fsCorr_zero_ne_zero
#print axioms EffectiveGaussianLagTwo
#print axioms two_lag_form_collapses
#print axioms lagTwoConstant
#print axioms epsMax
#print axioms inflation_le
#print axioms lagTwoConstant_lt_threshold
#print axioms effective_lag_two_bound
#print axioms MiddleIntervalLagTwo
#print axioms confines_of_arms
#print axioms flat_profile_meets_every_uniform_fact
#print axioms flat_profile_fails_the_threshold
end Audit

end MassGap.FreeFieldLagTwo
