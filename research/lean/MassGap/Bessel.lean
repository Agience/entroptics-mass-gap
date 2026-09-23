import Mathlib

/-!
# MassGap.Bessel — the integer-order modified Bessel series and the ratio `I₂/I₁`

Mathlib carries no modified Bessel function `Iν`, so this module defines the integer-order power
series directly,

    I_n(x) = ∑_{k ≥ 0} (x/2)^(2k+n) / (k! (k+n)!),

as `besselI n x := ∑' k, besselTerm n x k`, and establishes:

* `besselI_summable` — the series is summable for `0 ≤ x`, by comparison with
  `(x/2)^n * ((x/2)^2)^k / k!`, whose sum is `(x/2)^n * exp ((x/2)^2)`.
* `besselI_pos` — `0 < besselI n x` for `0 < x`, since every term is positive.
* `ratio_pos` — `0 < besselI 2 x / besselI 1 x` for `0 < x`.
* `besselTerm_two_le_quarter`, `besselI_two_le_quarter`, `ratio_le_quarter` — a termwise bound and
  its sum, giving `besselI 2 x / besselI 1 x ≤ x / 4` for `0 < x`.
* `two_mul_ratio_lt_kappa0` and `strong_coupling_below_threshold` — the consequence of that ratio
  bound for `2 * β * (besselI 2 β / besselI 1 β)` against `(1 / 4) * Real.log 3`, under the
  hypothesis `β ^ 2 < (1 / 2) * Real.log 3`.

Scope: everything here is about the real power series as defined. No identification of `besselI`
with Mathlib's or with any analytic characterisation of `Iν` is made or used, and no theorem here
asserts a lower bound on the ratio beyond positivity. `strong_coupling_below_threshold` takes the
character bound `μ β ≤ 2 * β * (besselI 2 β / besselI 1 β)` as a hypothesis.
-/

namespace MassGap.Bessel

open scoped BigOperators Nat

/-- The `k`-th term of the integer-order modified Bessel series:
`(x / 2) ^ (2 * k + n) / (k! * (k + n)!)`, with the factorials cast to `ℝ`. Defined for every real
`x`, including negative ones, where odd powers make the term negative.

DERIVED: both numerals are `2`. The first is the halving of the argument in the series' own variable
`x / 2`; the second is the step of the exponent, which advances by two per term because the series
runs over even powers of `x / 2` offset by the order `n`. -/
noncomputable def besselTerm (n : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  (x / 2) ^ (2 * k + n) / ((k.factorial : ℝ) * ((k + n).factorial : ℝ))

/-- The modified Bessel function of the first kind at integer order `n`, as the `tsum` of
`besselTerm n x`. A `tsum`, so it is `0` by definition wherever the family is not summable;
`besselI_summable` supplies summability for `0 ≤ x`.

DERIVED: no numeral occurs; the numerals of the series live in `besselTerm`. -/
noncomputable def besselI (n : ℕ) (x : ℝ) : ℝ := ∑' k, besselTerm n x k

theorem besselTerm_nonneg (n : ℕ) (x : ℝ) (k : ℕ) (hx : 0 ≤ x) : 0 ≤ besselTerm n x k := by
  unfold besselTerm
  apply div_nonneg
  · exact pow_nonneg (by linarith) _
  · exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem besselTerm_pos (n : ℕ) (x : ℝ) (k : ℕ) (hx : 0 < x) : 0 < besselTerm n x k := by
  unfold besselTerm
  apply div_pos
  · exact pow_pos (by linarith) _
  · exact mul_pos (by exact_mod_cast k.factorial_pos) (by exact_mod_cast (k + n).factorial_pos)

/-- Termwise comparison with an exponential series. For `0 ≤ x`,
`besselTerm n x k ≤ (x / 2) ^ n * ((x / 2) ^ 2) ^ k / k!`. The proof splits the exponent
`2 * k + n` into `n` and `2 * k`, then applies `div_le_self`, using that `(k + n)!` is at least one
so dropping it only increases the quotient.

DERIVED: `0` is the sign hypothesis on `x`, needed because the bound relies on nonnegative powers;
the two `2`s are the halving `x / 2` and the even exponent step of the series, both inherited from
`besselTerm`. -/
theorem besselTerm_le (n : ℕ) (x : ℝ) (k : ℕ) (hx : 0 ≤ x) :
    besselTerm n x k ≤ (x / 2) ^ n * ((x / 2) ^ 2) ^ k / (k.factorial : ℝ) := by
  have hx2 : (0 : ℝ) ≤ x / 2 := by linarith
  have hnum : (x / 2) ^ (2 * k + n) = (x / 2) ^ n * ((x / 2) ^ 2) ^ k := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  unfold besselTerm
  rw [hnum, ← div_div]
  apply div_le_self
  · exact div_nonneg (mul_nonneg (pow_nonneg hx2 n) (pow_nonneg (sq_nonneg (x / 2)) k))
      (Nat.cast_nonneg _)
  · have h1 : (1 : ℕ) ≤ (k + n).factorial := (k + n).factorial_pos
    exact_mod_cast h1

theorem besselI_summable (n : ℕ) (x : ℝ) (hx : 0 ≤ x) : Summable (besselTerm n x) := by
  have hg : Summable (fun k => (x / 2) ^ n * ((x / 2) ^ 2) ^ k / (k.factorial : ℝ)) := by
    have h := (Real.summable_pow_div_factorial ((x / 2) ^ 2)).mul_left ((x / 2) ^ n)
    simpa [mul_div_assoc] using h
  exact Summable.of_nonneg_of_le (fun k => besselTerm_nonneg n x k hx)
    (fun k => besselTerm_le n x k hx) hg

/-- `0 < besselI n x` for every order `n` and every `0 < x`. The proof feeds `besselI_summable`,
termwise nonnegativity and strict positivity of the `k = 0` term to `Summable.tsum_pos`.

DERIVED: the one numeral is `0`, the strict lower bound on the argument and on the sum. The index
`0` that `Summable.tsum_pos` is applied at lives in the proof, not the statement. -/
theorem besselI_pos (n : ℕ) {x : ℝ} (hx : 0 < x) : 0 < besselI n x := by
  unfold besselI
  exact (besselI_summable n x hx.le).tsum_pos
    (fun k => besselTerm_nonneg n x k hx.le) 0 (besselTerm_pos n x 0 hx)

/-- `0 < besselI 2 x / besselI 1 x` for `0 < x`, by `div_pos` on two instances of `besselI_pos`.

DERIVED: `0` is the strict lower bound on the argument and on the ratio; `2` and `1` are the two
Bessel orders being compared, the ratio of the first two characters. None is a magnitude. -/
theorem ratio_pos {x : ℝ} (hx : 0 < x) : 0 < besselI 2 x / besselI 1 x :=
  div_pos (besselI_pos 2 hx) (besselI_pos 1 hx)

/-! ### An upper bound `x / 4` on the ratio, and the threshold it yields

The three results below bound `besselI 2 x / besselI 1 x` by `x / 4`, termwise and then summed, and
substitute that bound into `2 * β * (besselI 2 β / besselI 1 β)`. The resulting threshold is stated
as the inequality `β ^ 2 < (1 / 2) * Real.log 3` against the floor `(1 / 4) * Real.log 3`; no
numerical interval for the ratio is used. -/

/-- Termwise: `besselTerm 2 x k ≤ (x / 4) * besselTerm 1 x k` for `0 ≤ x` and every `k`. The proof
establishes the exact identity `besselTerm 2 x k = ((x / 2) / (k + 2)) * besselTerm 1 x k` — the
order-two term carries one extra factor `x / 2` in the numerator and one extra factor `k + 2` in the
denominator, from `(k + 2)! = (k + 2) * (k + 1)!` — and then bounds `(x / 2) / (k + 2)` by `x / 4`
using `k ≥ 0`.

DERIVED: `2` and `1` are the two Bessel orders compared, so their difference is what `(k + n)!`
advances by; `4` is the product of the `2` in the series' own `x / 2` with the smallest value of
`k + 2`, namely `2` at `k = 0`; `0` is the sign hypothesis on `x`, which is what lets the inequality
survive multiplication by the order-one term. No numeral is chosen. -/
theorem besselTerm_two_le_quarter (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    besselTerm 2 x k ≤ (x / 4) * besselTerm 1 x k := by
  have hx2 : (0 : ℝ) ≤ x / 2 := by linarith
  have hkf : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hf1 : (0 : ℝ) < ((k + 1).factorial : ℝ) := by exact_mod_cast (k + 1).factorial_pos
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hfac : (((k + 2).factorial : ℕ) : ℝ) = ((k : ℝ) + 2) * ((k + 1).factorial : ℝ) := by
    have : (k + 2).factorial = (k + 2) * (k + 1).factorial := Nat.factorial_succ (k + 1)
    rw [this]; push_cast; ring
  have key : besselTerm 2 x k = ((x / 2) / ((k : ℝ) + 2)) * besselTerm 1 x k := by
    unfold besselTerm
    rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, pow_succ, hfac]
    field_simp
  rw [key]
  refine mul_le_mul_of_nonneg_right ?_ (besselTerm_nonneg 1 x k hx)
  rw [div_le_iff₀ hk2]
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- `besselI 2 x ≤ (x / 4) * besselI 1 x` for `0 ≤ x`. The termwise bound
`besselTerm_two_le_quarter` summed with `Summable.tsum_le_tsum`, after pulling the scalar out with
`tsum_mul_left`; summability of both sides comes from `besselI_summable`.

DERIVED: `2` and `1` are the Bessel orders; `4` is the constant of `besselTerm_two_le_quarter`,
carried unchanged through the sum; `0` is the sign hypothesis on `x`, required by both the termwise
bound and the summability lemma. -/
theorem besselI_two_le_quarter (x : ℝ) (hx : 0 ≤ x) :
    besselI 2 x ≤ (x / 4) * besselI 1 x := by
  unfold besselI
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun k => besselTerm_two_le_quarter x hx k)
    (besselI_summable 2 x hx) ((besselI_summable 1 x hx).mul_left _)

/-- `besselI 2 x / besselI 1 x ≤ x / 4` for `0 < x`. Clearing the denominator with `div_le_iff₀`,
which needs `0 < besselI 1 x` from `besselI_pos`, reduces this to `besselI_two_le_quarter`. Strict
positivity of `x` is used only for that denominator; the underlying inequality holds at `0 ≤ x`.

DERIVED: `0` is the strict lower bound on `x`; `2` and `1` are the Bessel orders; `4` is the
constant of `besselI_two_le_quarter`, unchanged. -/
theorem ratio_le_quarter {x : ℝ} (hx : 0 < x) : besselI 2 x / besselI 1 x ≤ x / 4 := by
  rw [div_le_iff₀ (besselI_pos 1 hx)]
  exact besselI_two_le_quarter x hx.le

#print axioms besselTerm_two_le_quarter
#print axioms besselI_two_le_quarter
#print axioms ratio_le_quarter

/-- For `0 < β` with `β ^ 2 < (1 / 2) * Real.log 3`,
`2 * β * (besselI 2 β / besselI 1 β) < (1 / 4) * Real.log 3`. Substituting `ratio_le_quarter` gives
`2 * β * (β / 4) = β ^ 2 / 2`, and the hypothesis then places that below `(1 / 4) * Real.log 3`;
`nlinarith` closes it.

Scope: the implication runs one way. Nothing here states that the left-hand side equals any physical
tension, nor that the threshold is attained.

DERIVED: `0` is the strict lower bound on `β`; `2` and `1` inside `besselI` are the Bessel orders;
the leading `2` is the coefficient of the supplied character bound; the `2` in `β ^ 2` is the square produced by multiplying `β` into the bound `β / 4`; `1 / 2` is that coefficient
against the `4` of `ratio_le_quarter`, since `2 * (1 / 4) = 1 / 2`; `1 / 4` and `3` are the floor
`(1 / 4) * Real.log 3` as written in the conclusion. -/
theorem two_mul_ratio_lt_kappa0 {β : ℝ} (hβ : 0 < β)
    (hlt : β ^ 2 < (1 / 2) * Real.log 3) :
    2 * β * (besselI 2 β / besselI 1 β) < (1 / 4) * Real.log 3 := by
  have hr := ratio_le_quarter hβ
  have h1 : 2 * β * (besselI 2 β / besselI 1 β) ≤ 2 * β * (β / 4) :=
    mul_le_mul_of_nonneg_left hr (by linarith)
  nlinarith [h1, hlt]

/-- For an arbitrary `μ : ℝ → ℝ` and `0 ≤ β` with `β ^ 2 < (1 / 2) * Real.log 3`, the character
bound `hbound : μ β ≤ 2 * β * (besselI 2 β / besselI 1 β)` gives `μ β < (1 / 4) * Real.log 3`. The
proof splits on `β = 0`, where `hbound` collapses to `μ 0 ≤ 0` and `Real.log 3 > 0` finishes, and
`0 < β`, where it chains `hbound` with `two_mul_ratio_lt_kappa0`.

Scope: `μ` is any real function — nothing identifies it with a tension read. `hbound` is a
hypothesis and is not established here.

DERIVED: `0` is the lower bound on `β`; `2` and `1` inside `besselI` are the Bessel orders; the
leading `2` is the coefficient of `hbound` as the caller states it; the `2` in `β ^ 2` is the square arising when `β` multiplies the ratio bound; `1 / 2` is the threshold on
`β ^ 2` and `1 / 4` the floor coefficient, the two related by that same `2`; `3` is the argument of
the logarithm in both. -/
theorem strong_coupling_below_threshold {μ : ℝ → ℝ} {β : ℝ}
    (hβ : 0 ≤ β) (hlt : β ^ 2 < (1 / 2) * Real.log 3)
    (hbound : μ β ≤ 2 * β * (besselI 2 β / besselI 1 β)) :
    μ β < (1 / 4) * Real.log 3 := by
  rcases eq_or_lt_of_le hβ with rfl | hpos
  · have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
    simp only [mul_zero, zero_mul] at hbound
    linarith
  · exact lt_of_le_of_lt hbound (two_mul_ratio_lt_kappa0 hpos hlt)

#print axioms two_mul_ratio_lt_kappa0
#print axioms strong_coupling_below_threshold

end MassGap.Bessel
