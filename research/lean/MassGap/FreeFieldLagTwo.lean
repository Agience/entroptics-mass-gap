import Mathlib
import MassGap.LagTwoBound

/-!
# MassGap.FreeFieldLagTwo — an effective weak-coupling lag-two bound with an explicit constant

`LagTwoBound.confines_of_lag_two_ratio` asks for `ρ(2) ≤ K·ρ(0)` at every `β ≥ 0` with
`K < lagTwoThreshold`.
`effective_lag_two_bound` supplies the half of that from a coupling `B` upward,

    ∃ B, ∀ β ≥ B,  wilsonCorrAt 3 β 2  ≤  lagTwoConstant ε · wilsonCorrAt 3 β 0,

with `lagTwoConstant ε` an explicit rational multiple of `(1+ε)/(1−ε)` and `B` the one supplied by
the hypothesis `EffectiveGaussianLagTwo ε`. The bound is effective in `B`: it names the coupling
from which it holds, which a statement of the form `Tendsto (fun β => ρ(2)/ρ(0)) atTop _` would not.

## The free-field propagator data, computed

At extent four the momenta are `p_μ = πk_μ/2`, so the lattice momentum square `p̂_μ² = 2 − 2cos p_μ`
takes the integer values `0, 2, 4, 2` (`hatSq`) and the lag phase `cos(p₂d)` takes `1, 0, −1, 0`
(`lagPhase`). The Feynman-gauge field-strength two-point function

    D(d) = (1/V) ∑_k cos(p₂ d) · (p̂₀² + p̂₁²) / p̂²

is therefore a finite sum of rationals. `fsCorr d` is `V·1680·D(d)` as an integer, `1680`
(`clearDen`) being the least common multiple of the even numbers up to `16`, which are the only
nonzero values `p̂²` takes; `clearDen_exact` checks by `decide` that it clears every one. The values
are decided:

    fsCorr 0 = 214200,   fsCorr 1 = 29640,   fsCorr 2 = 8760,   fsCorr 3 = fsCorr 1,

so `D(2)/D(0) = 73/1785` and `freeRatio = (73/1785)² = 5329/3186225` (`freeRatio_eq`).

`zero_momentum_term_vanishes` shows the numerator `p̂₀² + p̂₁²` vanishes wherever `p̂²` does, so the
`k = 0` term is `0` whatever convention is used and no zero-mode subtraction is performed.

`fieldStrength_pure_gauge_orthogonal` is the identity `(a−1)(−(b−1)) + (b−1)(a−1) = 0` in two free
complex variables, the antisymmetry of `F` in its two indices, with no condition on `a` or `b`. A
covariant gauge's propagator differs from Feynman gauge by a term built from the longitudinal
projector, which meets the field-strength vertex through exactly that contraction, so `D(d)` is the
same in every covariant gauge. `fsCorr_zero_ne_zero` states that the surviving transverse part is
not zero.

## The hypothesis

`EffectiveGaussianLagTwo ε` states that beyond some coupling `B` there is one positive scale `R`
with `ρ(d) ≤ (1+ε)·R·D(d)²` at every lag and `(1−ε)·R·D(0)² ≤ ρ(0)` at the contact lag. `R` may
depend on `β`, so the content is about the ratio. Nothing in this module or this tree proves it.

The upper bound ranges over every lag rather than over lags `0` and `2` alone.
`two_lag_form_collapses` proves that the restricted version, with `R` free and constrained at only
two lags, is equivalent to the ratio bound it would be used to derive. Lag `3` costs nothing beyond
lag `1`, since `fsCorr_three` gives `fsCorr 3 = fsCorr 1`.

The hypothesis is one-sided except at the contact lag: only `ρ(0) > 0` is asserted, which
`PlaqVariance.corrClay_zero_pos` proves. A two-sided sandwich at every lag would additionally assert
`ρ(2) > 0` and `ρ(1) > 0`.

Eliminating `R` turns the hypothesis into `ρ(d) ≤ ((1+ε)/(1−ε))·(D(d)/D(0))²·ρ(0)`, and the
conclusion of `effective_lag_two_bound` is its `d = 2` member, so that theorem carries the constant
rather than deriving a bound.

## The admissible relative error

`lagTwoConstant ε = ((1+ε)/(1−ε))·(8760/214200)²`, and `lagTwoConstant_lt_threshold` proves it is
below `LagTwoBound.lagTwoThreshold` for every `ε ≤ 5/6` (`epsMax`). `inflation_le` bounds
`(1+ε)/(1−ε)` by `11` there, and `11 · (5329/3186225) = 58619/3186225 ≈ 0.0183977` sits below the
bracket `0.018623` that `LagTwoBound.lagTwoThreshold_gt` gives. The theorem holds at every smaller
`ε`, and a smaller `ε` is a stronger hypothesis. `MassGap.FreeFieldLagTwoSix` runs the same argument
at extent six with cap `24/25`.

## Scope

The conclusion covers `β ≥ B` only. `MiddleIntervalLagTwo K B` states the same bound on `[0, B]`,
and `confines_of_arms` joins the two at a shared `B` and a shared constant to give
`ApertureRoute.ConfinesAtAnAperture`. The `B` is shared: quantifying `MiddleIntervalLagTwo` over
every `B` would cover the whole half-line on its own.

§5b records what a coupling-uniform argument can reach:
`flat_profile_meets_every_uniform_fact` exhibits `r ≡ 1` on `Fin 4` satisfying nonnegativity,
positive total mass, circle symmetry `r 3 = r 1`, log-convexity `r 1 ^ 2 ≤ r 0 * r 2`, contact
dominance `r 2 ≤ r 0`, `r 2 ≤ r 1`, and the quadratic `2 * r 1 ^ 2 ≤ r 2 ^ 2 + r 0 * r 2` with
equality, while refuting `r 2 ≤ K * r 0` for every `K < 1`.
`flat_profile_fails_the_threshold` adds that this profile fails the criterion at
`lagTwoThreshold` itself.

Foundational footprint on every declaration, the assembly corollary included (`#print axioms`, §6):
a subset of `propext`, `Classical.choice`, `Quot.sound`, with no cited axiom. The purely
computational declarations print `propext` alone.

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

/-- The lattice momentum square `p̂² = 2 − 2cos(2πk/4)` at extent four, tabulated as a natural
number over `Fin 4`: `![0, 2, 4, 2]`.

DERIVED: `2 − 2cos` is the momentum square of the nearest-neighbour lattice Laplacian and `2πk/4`
the periodic momentum; evaluating at `k = 0, 1, 2, 3` gives the four entries. `4` is the extent.
Every entry is a value of that expression and none is chosen. -/
def hatSq : Fin 4 → ℕ := ![0, 2, 4, 2]

/-- The lag phase `cos(2πkd/4)` as an integer: `![1, 0, -1, 0]` evaluated at `k * d`, the product
taken in `Fin 4`, which is the reduction of `k·d` modulo the extent.

DERIVED: `cos(2πm/4)` is `1, 0, −1, 0` at `m = 0, 1, 2, 3`, so the four entries are values of that
expression; `4` is the extent. No entry is chosen. -/
def lagPhase (k d : Fin 4) : ℤ := ![1, 0, -1, 0] (k * d)

/-- The common denominator `1680`, used to clear every `p̂²` appearing in `fsTerm`.

DERIVED: `p̂²` is a sum of four entries of `hatSq`, each in `{0, 2, 4}`, so its nonzero values are
exactly the even numbers from `2` to `16`, and `1680` is their least common multiple.
`clearDen_exact` checks by `decide` that it is divisible by every one of them, so the value is a
fact about that value set rather than a choice. -/
def clearDen : ℕ := 1680

/-- `p̂² = ∑_μ p̂_μ²` at the momentum labelled `(a, b, c, e)`: the sum of the four `hatSq` entries.

DERIVED: `4` is `Fin 4`, the extent of the torus, so `a b c e` are momentum indices. There are four
of them because the problem is four-dimensional, and the sum runs over all of them because that is
what `∑_μ` means. -/
def momSq (a b c e : Fin 4) : ℕ := hatSq a + hatSq b + hatSq c + hatSq e

/-- The plaquette-plane numerator `p̂₀² + p̂₁²`, the transverse contraction of the field-strength
vertex with the Feynman-gauge propagator.

DERIVED: `4` is `Fin 4`, the extent, so `a` and `b` are momentum indices. There are two of them
because a plaquette spans a plane, and `WilsonBridge.corrClay` fixes that plane to be `0, 1`. -/
def planeNum (a b : Fin 4) : ℕ := hatSq a + hatSq b

/-- One momentum's contribution to `V·1680·D(d)`:
`lagPhase c d * (planeNum a b * (clearDen / momSq a b c e))`, with the branch `momSq = 0` sent to
`0`. `zero_momentum_term_vanishes` shows `planeNum a b` is `0` on that branch, so the other branch
would also give `0` there.

DERIVED: `4` is `Fin 4`, the extent, so `d a b c e` are indices; `clearDen` supplies the `1680`; the
`0` in the guard selects the branch and the `0` it returns is the value both branches give. -/
def fsTerm (d a b c e : Fin 4) : ℤ :=
  if momSq a b c e = 0 then 0
  else lagPhase c d * (planeNum a b * (clearDen / momSq a b c e) : ℕ)

/-- The free-field field-strength correlation at lag `d`, as the exact integer `V·1680·D(d)`: the
four-fold sum of `fsTerm d` over all momentum labels.

DERIVED: `4` is `Fin 4`, the extent, so `d` is a lag index. The sum runs over the four momentum
components of the four-dimensional torus; the overall factor `V·1680` is lag-independent and
cancels in every ratio formed below. -/
def fsCorr (d : Fin 4) : ℤ := ∑ a, ∑ b, ∑ c, ∑ e, fsTerm d a b c e

/-- `momSq a b c e * (clearDen / momSq a b c e) = clearDen` at every momentum with `momSq ≠ 0`, so
the natural-number division in `fsTerm` is exact and `fsCorr` is a rescaling of `D` rather than a
truncation. By `decide` over all `256` momentum labels.

DERIVED: `4` is the extent, so the arguments are momentum indices; `0` is the value the hypothesis
excludes. -/
theorem clearDen_exact (a b c e : Fin 4) (h : momSq a b c e ≠ 0) :
    momSq a b c e * (clearDen / momSq a b c e) = clearDen := by
  revert h; revert a b c e; decide

/-- `planeNum a b = 0` wherever `momSq a b c e = 0`: the plane numerator vanishes at every momentum
where the denominator does. By `decide`. The `momSq = 0` branch of `fsTerm` therefore returns the
same value the other branch would, and no zero-mode subtraction is being performed.

DERIVED: `4` is the extent, so the arguments are momentum indices; the two `0`s are the vanishing
denominator and the vanishing numerator. -/
theorem zero_momentum_term_vanishes (a b c e : Fin 4) (h : momSq a b c e = 0) :
    planeNum a b = 0 := by
  revert h; revert a b c e; decide

/-! ### The three values, decided -/

/-- `fsCorr 0 = 214200`, by `decide`: the contact value of `V·1680·D`, so `D(0) = 255/512`.

DERIVED: `0` is the contact lag; `214200` is the decided value of the sum. -/
theorem fsCorr_zero : fsCorr 0 = 214200 := by decide

/-- `fsCorr 1 = 29640`, by `decide`, so `D(1) = 247/3584`.

DERIVED: `1` is the lag; `29640` is the decided value of the sum. -/
theorem fsCorr_one : fsCorr 1 = 29640 := by decide

/-- `fsCorr 2 = 8760`, by `decide`, so `D(2) = 73/3584`.

DERIVED: `2` is the lag the ratio is about; `8760` is the decided value of the sum. -/
theorem fsCorr_two : fsCorr 2 = 8760 := by decide

/-- `fsCorr 3 = fsCorr 1`, by `decide`: lags `3` and `1` are the same circle distance apart on a
torus of extent four. The lag-three constraint in `EffectiveGaussianLagTwo` therefore adds nothing
beyond the lag-one one.

DERIVED: `3` and `1` are the two lags, which are equidistant on a circle of circumference four. -/
theorem fsCorr_three : fsCorr 3 = fsCorr 1 := by decide

/-! ## 2. The ratio the Wilson observable inherits

By Wick, the connected plaquette correlation of a Gaussian fluctuation field is `R · D(d)²` with `R`
— the colour factor, the coupling normalisation and the lattice spacing together — independent of
the lag. `sq_ratio_of_square_law` is that cancellation, and it is all the Wick step contributes to a
ratio. -/

/-- The free-field lag-two ratio `(D(2)/D(0))^2`, as a rational, formed from `fsCorr` so that the
common factor `V·1680` cancels.

DERIVED: `2` and `0` inside `fsCorr` are lags — the lag the claim is about and the contact lag it is
normalised against, the pair `LagTwoBound.confines_of_lag_two_ratio`'s hypothesis relates. The outer `2` is the square Wick's
 theorem puts on the propagator. The values are `fsCorr`'s, decided above. -/
def freeRatio : ℚ := ((fsCorr 2 : ℚ) / (fsCorr 0 : ℚ)) ^ 2

/-- `freeRatio = 5329 / 3186225`, which is `(73/1785)^2` and approximately `0.00167251`. From
`fsCorr_two` and `fsCorr_zero` by `norm_num`.

DERIVED: `5329 = 73^2` and `3186225 = 1785^2` are the squares of `fsCorr 2 / fsCorr 0` in lowest
terms, both values decided above. Nothing is chosen and nothing is measured. -/
theorem freeRatio_eq : freeRatio = 5329 / 3186225 := by
  rw [freeRatio, fsCorr_two, fsCorr_zero]; norm_num

theorem freeRatio_pos : 0 < freeRatio := by rw [freeRatio_eq]; norm_num

/-- If `ρ d = R * (G d) ^ 2` at every `d` with `0 < R` and `G 0 ≠ 0`, then `ρ 2 / ρ 0 = (G 2 / G 0) ^ 2`:
the lag-independent scale cancels out of the ratio.

The square law `ρ d = R * (G d) ^ 2` is a hypothesis; the fourth-moment identity that would produce
it is not proved here and is part of `EffectiveGaussianLagTwo`.

DERIVED: `0` is the positivity threshold on `R`, the contact lag, and the lag at which `G` is
required nonzero; `2` is the lag the ratio is about and the exponent Wick's theorem puts on the
propagator. -/
theorem sq_ratio_of_square_law {ρ G : ℕ → ℝ} {R : ℝ} (hR : 0 < R) (hG0 : G 0 ≠ 0)
    (h : ∀ d, ρ d = R * (G d) ^ 2) : ρ 2 / ρ 0 = (G 2 / G 0) ^ 2 := by
  rw [h 2, h 0, div_pow]
  field_simp

/-! ## 3. Gauge fixing does not arise for this observable

The propagator in §1 is written in Feynman gauge with the zero mode dropped, and the natural worry
is that a gauge-invariant observable has been read off a gauge-dependent object. It has not, and the
reason is stronger than a cancellation between terms. -/

/-- `(a - 1) * (-(b - 1)) + (b - 1) * (a - 1) = 0` for all `a b : ℂ`, by `ring`.

A gauge transformation moves `A_μ(x)` by `ω(x+μ̂) − ω(x)`, whose momentum-space direction is
`g_μ = e^{ip_μ} − 1`; with `a = e^{ip₀}` and `b = e^{ip₁}` that is `g₀ = a − 1`, `g₁ = b − 1`. The
vertex of the lattice field strength `F₀₁ = Δ₀A₁ − Δ₁A₀` is `v₀ = −(b − 1)`, `v₁ = a − 1`, and the
statement is `g₀·v₀ + g₁·v₁ = 0`.

The identity holds in two free complex variables, with no condition on `a` or `b`: unit modulus is
not used. It is the antisymmetry of `F` in its two indices. A covariant gauge's propagator differs
from Feynman gauge by a term proportional to the longitudinal projector built from `g`, and every
such term meets the vertex through this contraction, so `D(d)` is the same in every covariant gauge
at every momentum. That the surviving transverse part is not itself zero is
`fsCorr_zero_ne_zero`.

DERIVED: each `1` is the `1` of `e^{ip} − 1`; `0` is the value of the contraction. -/
theorem fieldStrength_pure_gauge_orthogonal (a b : ℂ) :
    (a - 1) * (-(b - 1)) + (b - 1) * (a - 1) = 0 := by ring

/-- `fsCorr 0 ≠ 0`, from `fsCorr_zero`. The object §1 computes is not identically zero, so the
ratios formed from it are well defined.

DERIVED: `0` is the contact lag and the value excluded. -/
theorem fsCorr_zero_ne_zero : fsCorr 0 ≠ 0 := by rw [fsCorr_zero]; norm_num

/-! ## 4. The named open hypothesis, and the effective bound it buys

DERIVED in this section: `2` and `0` are lag indices; `3` is the extent index with `3 + 1 = 4`, the
extent `LagTwoBound` works at. `5/6` is the one CHOSEN numeral and it is chosen conservatively — see
its note. -/

/-- The effective Gaussian hypothesis at relative error `ε`: there is a coupling `B` such that for
every `β ≥ B` there is one `R > 0` with

* `wilsonCorrAt 3 β d ≤ (1 + ε) * (R * (fsCorr d)^2)` at every lag `d : Fin 4`, and
* `(1 - ε) * (R * (fsCorr 0)^2) ≤ wilsonCorrAt 3 β 0` at the contact lag.

`R` is quantified inside the quantifier over `β`, so it may depend on the coupling; it absorbs the
colour factor, the coupling normalisation and the lattice spacing, and the content of the hypothesis
is about the ratio.

The upper bound ranges over every lag. `two_lag_form_collapses` proves that restricting it to lags
`0` and `2` alone makes the hypothesis equivalent to the ratio bound `effective_lag_two_bound`
derives from it, since `R` is free and would be constrained at only two lags. Lag `3` adds nothing
beyond lag `1`, by `fsCorr_three`.

The hypothesis is one-sided except at the contact lag: only `ρ(0) > 0` is implied, which
`PlaqVariance.corrClay_zero_pos` proves. A two-sided sandwich at every lag would also assert
`ρ(2) > 0` and `ρ(1) > 0`.

Nothing in this module or this tree proves the hypothesis.

DERIVED: `1 + ε` and `1 − ε` are the two ends of a symmetric relative error and `ε` is the caller's;
`0` is the positivity threshold on `R` and the contact lag; `2` is the exponent Wick's theorem puts
on the propagator; `3` is the aperture, whose lag type is `Fin (3 + 1) = Fin 4`; `4` is the extent
the lag ranges over. -/
def EffectiveGaussianLagTwo (ε : ℝ) : Prop :=
  ∃ B : ℝ, ∀ β : ℝ, B ≤ β → ∃ R : ℝ, 0 < R ∧
    (∀ d : Fin 4, MassGap.wilsonCorrAt 3 β d ≤ (1 + ε) * (R * ((fsCorr d : ℝ)) ^ 2)) ∧
    (1 - ε) * (R * ((fsCorr 0 : ℝ)) ^ 2) ≤ MassGap.wilsonCorrAt 3 β 0

/-- The constant the hypothesis delivers: `((1 + ε)/(1 - ε)) * ((fsCorr 2)/(fsCorr 0))^2`, the
free-field ratio inflated by the worst-case relative error at each end.

DERIVED: `(1 + ε)/(1 - ε)` is the worst case of `(1 + ε)·ρ_free(2)` over `(1 - ε)·ρ_free(0)`; `2`
and `0` inside `fsCorr` are lags and the outer `2` is Wick's square. No numeral is chosen. -/
noncomputable def lagTwoConstant (ε : ℝ) : ℝ :=
  ((1 + ε) / (1 - ε)) * ((fsCorr 2 : ℝ) / (fsCorr 0 : ℝ)) ^ 2

/-- The admissible relative error, `5 / 6`.

CHOSEN: the value `5 / 6`, rounded down — away from the claim `lagTwoConstant ε < lagTwoThreshold`, so the rounding
cannot manufacture the inequality. The supremum against `LagTwoBound.lagTwoThreshold_gt`'s bracket
`0.018623` is `0.83518…`, where `(1 + ε)/(1 - ε)` reaches `0.018623 / 0.00167251 = 11.135…`; `5 / 6`
is the largest sixth below it and uses `11` of that `11.135`. `lagTwoConstant_lt_threshold` is
proved from `freeRatio_eq` and `lagTwoThreshold_gt`, and any `ε` below `0.83518` would serve. -/
def epsMax : ℚ := 5 / 6

/-- `(1 + ε) / (1 - ε) ≤ 11` for `ε ≤ epsMax = 5 / 6`. Nonnegativity of `ε` is not required:
`ε ≤ 5 / 6` alone puts `1 - ε` at or above `1 / 6`, which is what `div_le_iff₀` needs. Callers that
need `0 ≤ ε` carry it separately.

DERIVED: the two `1`s are the ends of the symmetric relative error `1 ± ε`; `11` is the value
`(1 + ε)/(1 - ε)` attains at `ε = 5 / 6`, so the bound is exact at the cap. -/
theorem inflation_le {ε : ℝ} (hε : ε ≤ (epsMax : ℝ)) : (1 + ε) / (1 - ε) ≤ 11 := by
  have he : ε ≤ 5 / 6 := by rw [epsMax] at hε; norm_num at hε; linarith
  have hden : (0 : ℝ) < 1 - ε := by linarith
  rw [div_le_iff₀ hden]
  linarith [he]

/-- `lagTwoConstant ε < LagTwoBound.lagTwoThreshold` for every `ε ≤ epsMax`. `inflation_le` bounds
the inflation factor by `11`, `fsCorr_two` and `fsCorr_zero` make the squared ratio `5329 / 3186225`,
and `11 * (5329 / 3186225) = 58619 / 3186225 ≈ 0.0183977` falls below the bracket `0.018623` that
`LagTwoBound.lagTwoThreshold_gt` supplies.

DERIVED: no numeral appears in the statement; the `11`, `5329 / 3186225` and `0.018623` occur in the
proof and are `inflation_le`'s, `freeRatio_eq`'s and `lagTwoThreshold_gt`'s respectively. -/
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

/-- The two-lag form is equivalent to the ratio bound it would be used to derive. For `0 ≤ ε < 1`
and `s0, s2, r0` positive,

    (∃ R > 0, r2 ≤ (1 + ε) * (R * s2 ^ 2) ∧ (1 - ε) * (R * s0 ^ 2) ≤ r0)
      ↔ r2 ≤ ((1 + ε) / (1 - ε)) * (s2 / s0) ^ 2 * r0.

Forward, the lower constraint caps `R` at `r0 / ((1 - ε) * s0 ^ 2)`; backward, that cap is the
witness. So a version of `EffectiveGaussianLagTwo` restricted to lags `0` and `2` would assume its
own conclusion, which is why the hypothesis bounds every lag.

The statement is about four real numbers and refers to no lattice.

DERIVED: `0` is the positivity threshold on `ε`, `R`, `s0`, `s2` and `r0`; the `1`s are the ends of
the symmetric relative error `1 ± ε` and the upper bound on `ε`; the exponents `2` are squares.
`s0`, `s2` stand for the free-field values at the two lags and `r0`, `r2` for the correlation's. -/
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

/-- From `EffectiveGaussianLagTwo ε` with `0 ≤ ε ≤ epsMax`: there is a `B` with
`lagTwoConstant ε < LagTwoBound.lagTwoThreshold` and
`wilsonCorrAt 3 β 2 ≤ lagTwoConstant ε * wilsonCorrAt 3 β 0` for every `β ≥ B`.

`B` is the hypothesis's own, so the bound is effective exactly to the extent that the hypothesis is.
The proof eliminates the hypothesis's `R` between its upper bound at lag `2` and its lower bound at
lag `0`; it performs no analysis and carries the constant `lagTwoConstant_lt_threshold` supplies.
The conclusion covers `β ≥ B` only.

DERIVED: `0` is the lower bound on `ε` and the contact lag; `2` is the lag the ratio is about; `3`
is the aperture, whose lag type is `Fin (3 + 1)`. -/
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

/-! ## 5. The complementary interval, and the join

`effective_lag_two_bound` covers `β ≥ B`, while `LagTwoBound.confines_of_lag_two_ratio`'s hypothesis
is quantified over every `β ≥ 0`. `MiddleIntervalLagTwo` names the same bound on `[0, B]`, and `confines_of_arms` joins the
two at a shared `B` and a shared constant. -/

/-- The lag-two bound at constant `K` on the coupling interval `[0, B]`:
`wilsonCorrAt 3 β 2 ≤ K * wilsonCorrAt 3 β 0` for every `β` with `0 ≤ β ≤ B`.
`LagTwoBound.exists_cut_lag_two_ratio` supplies this from the strong side out to a derived cut.

DERIVED: no numeral here is a magnitude. `3` is the aperture — `wilsonCorrAt 3` is the extent-four
torus, `3 + 1 = 4`, this module's propagator data is computed on. `2` and `0` are the lags the ratio
relates; the `0` in `0 ≤ β` is the bottom of the coupling range. `K` and `B` are variables. -/
def MiddleIntervalLagTwo (K B : ℝ) : Prop :=
  ∀ β : ℝ, 0 ≤ β → β ≤ B → MassGap.wilsonCorrAt 3 β 2 ≤ K * MassGap.wilsonCorrAt 3 β 0

/-- The two intervals join. Given `ε ≤ epsMax`, the bound at constant `lagTwoConstant ε` from `B`
upward (`hfar`) and the same bound on `[0, B]` (`hmid`), the conclusion is
`ApertureRoute.ConfinesAtAnAperture`, through
`LagTwoBound.confines_of_lag_two_ratio` at that constant with
`lagTwoConstant_lt_threshold` for its strictness. The case split is `le_total β B`.

`B` is shared between the two hypotheses and appears in both: quantifying `hmid` over every `B`
would make it cover the half-line by itself.

The footprint is foundational: `LagTwoBound.confines_of_lag_two_ratio` reaches
`ConfinesZero.confines_extent_four_of_lag_two_small`, which does not consume
`Complete.wilson_reflection_positive_at`.

DERIVED: `3` is the aperture, whose lag type is `Fin (3 + 1)`; `2` is the lag the ratio is about and
`0` the contact lag. -/
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

/-! ## 5b. What a coupling-uniform argument can reach

The two theorems below exhibit a single profile satisfying every coupling-uniform fact this tree
proves of the extent-four correlation while refuting any ratio bound below one. -/

/-- There is an `r : Fin 4 → ℝ` satisfying seven coupling-uniform facts and refuting every ratio
bound below one. The witness is the constant profile `r ≡ 1`, and the seven conjuncts are:
nonnegativity `0 ≤ r d`; positive total mass `0 < ∑ d, r d` (both from
`Complete.wilson_reflection_positive_at_even`); circle symmetry `r 3 = r 1`; log-convexity
`r 1 ^ 2 ≤ r 0 * r 2` (`LogConvex.corrClay_log_convex`); contact dominance `r 2 ≤ r 0`;
`r 2 ≤ r 1` (`LinkGram.wilson_lag_two_le_lag_one`); and the quadratic
`2 * r 1 ^ 2 ≤ r 2 ^ 2 + r 0 * r 2` (`SlabQuadratic.wilson_quadratic`), which the flat profile meets
with equality. The eighth conjunct is `∀ K < 1, ¬ (r 2 ≤ K * r 0)`.

The last two facts in the list are proved from reflection positivity rather than from the shape
cone, and the quadratic does not follow from the others
(`SpectralFour.missing_inequalities_independent`), so it is carried explicitly.

Since one profile satisfies all seven, no consequence of them alone gives a ratio constant below
one. This extends `TailRatio.no_strict_lag_bound_with_contact`, whose premise set stops before
`LinkGram`'s bound, by the two facts that were not in it.

DERIVED: `4` is the extent the lag index ranges over; `0`, `1`, `2`, `3` are lag indices, and `0` is
also the sign asserted of each entry and the level the total mass exceeds; `1` is in addition the
flat profile's constant value and the level the refuted constant `K` falls below; the exponents `2`
are squares, from log-convexity and from the quadratic, and the coefficient `2` is the quadratic's
own, the term count in `y = F₀ + F₂` that `SlabQuadratic` records. -/
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

/-- `¬ ((1 : ℝ) ≤ LagTwoBound.lagTwoThreshold * 1)`: the flat profile of
`flat_profile_meets_every_uniform_fact` fails the lag-two criterion at the threshold itself, since
`LagTwoBound.lagTwoThreshold_lt` places the threshold below `1`.

DERIVED: the two `1`s are the flat profile's values at lags `2` and `0`;
`lagTwoThreshold` is a closed form and `LagTwoBound.lagTwoThreshold_lt` is what places it under
one. -/
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
