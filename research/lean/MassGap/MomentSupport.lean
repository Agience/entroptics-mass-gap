import Mathlib

/-!
# Moment-support lemma for positive-weight exponential sums (PAPER §11/§13)

One theorem over an arbitrary index type: a finite nonnegative-weight exponential sum
`∑_{k ∈ s} w_k λ_k^τ` that is dominated by `M ρ^τ` at *every* `τ : ℕ` has every positively-weighted
base `λ_k` at or below `ρ`.

The intended reading is spectral: with `w_k = |⟨v, e_k⟩|²` the overlaps of a vector with a transfer
operator's eigenbasis and `λ_k` the eigenvalues, a geometric bound on the correlator `∑_k w_k λ_k^τ`
confines the eigenvalues the vector sees to `[0, ρ]`. Nothing in this file constructs a transfer
operator, a Hilbert space or a correlator: the weights, bases and bound are all hypotheses.

Scope: the sum is over a `Finset`, so the statement is finite-dimensional; the exponent `τ` ranges
over all of `ℕ`, and a bound holding only up to some finite `τ` does not satisfy the hypothesis.
The conclusion is conditional on `0 < w k` and says nothing about zero-weight indices.
-/

namespace MassGap

open Finset Filter

/-- Moment-support lemma. Over a `Finset s` in any index type, given weights `w` and bases `lam`
that are nonnegative on `s`, a real `ρ > 0`, a real `M`, and the hypothesis that
`∑ k ∈ s, w k * lam k ^ τ ≤ M * ρ ^ τ` holds for *every* `τ : ℕ`, each `k ∈ s` with `0 < w k`
satisfies `lam k ≤ ρ`.

Nonnegativity of the weights is what makes a single term a lower bound for the whole sum; dividing
the resulting `w k * lam k ^ τ ≤ M * ρ ^ τ` by `ρ ^ τ` bounds `w k * (lam k / ρ) ^ τ` by `M` at every
`τ`, which a ratio above `1` cannot sustain.

Scope: `M` is not assumed nonnegative and `ρ` is not assumed below `1`; the bound is required at all
natural `τ`, and indices with `w k = 0` are unconstrained.

DERIVED: `0` occurs four times, as the lower bound on the weights `w k`, the lower bound on the bases
`lam k`, the positivity threshold of `ρ`, and the positivity threshold on `w k` selecting which
indices the conclusion covers. No other numeral appears. -/
theorem le_of_positive_weight_decay {ι : Type*} (s : Finset ι) (w lam : ι → ℝ) (M ρ : ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hlam : ∀ k ∈ s, 0 ≤ lam k) (hρ : 0 < ρ)
    (hbound : ∀ τ : ℕ, (∑ k ∈ s, w k * lam k ^ τ) ≤ M * ρ ^ τ) :
    ∀ k ∈ s, 0 < w k → lam k ≤ ρ := by
  intro k hk hwk
  by_contra hcon
  rw [not_le] at hcon                               -- `hcon : ρ < lam k`
  -- Each single term is ≤ the whole (nonnegative) sum ≤ `M ρ^τ`.
  have key : ∀ τ : ℕ, w k * lam k ^ τ ≤ M * ρ ^ τ := fun τ =>
    le_trans (single_le_sum (fun i hi => mul_nonneg (hw i hi) (pow_nonneg (hlam i hi) τ)) hk) (hbound τ)
  set r := lam k / ρ with hrdef
  have hne : ρ ≠ 0 := ne_of_gt hρ
  have hr1 : 1 < r := by rw [hrdef]; rw [lt_div_iff₀ hρ, one_mul]; exact hcon
  have hrρ : r * ρ = lam k := by rw [hrdef]; field_simp
  -- `w k * r^τ ≤ M` for every `τ`: divide the moment bound by `ρ^τ > 0`.
  have hbdd : ∀ τ : ℕ, w k * r ^ τ ≤ M := by
    intro τ
    have hρτ : (0 : ℝ) < ρ ^ τ := pow_pos hρ τ
    have hlk : r ^ τ * ρ ^ τ = lam k ^ τ := by rw [← mul_pow, hrρ]
    have h1 : (w k * r ^ τ) * ρ ^ τ ≤ M * ρ ^ τ := by
      rw [mul_assoc, hlk]; exact key τ
    exact le_of_mul_le_mul_right h1 hρτ
  -- But `r > 1` makes `r^τ` unbounded, so `w k * r^τ` cannot stay `≤ M`.
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hr1).eventually_gt_atTop (M / w k)).exists
  rw [div_lt_iff₀ hwk] at hn                          -- `hn : M < r^n * w k`
  have hle := hbdd n                                   -- `hle : w k * r^n ≤ M`
  rw [mul_comm] at hle                                 -- `hle : r^n * w k ≤ M`
  linarith [hn, hle]

/-- Call-site form of `le_of_positive_weight_decay`, with the index `k`, its membership `hk` and its
positive weight `hwk` moved from the conclusion into the binders. Given the same nonnegativity,
`0 < ρ` and all-`τ` domination hypotheses, it concludes `lam k ≤ ρ` for that single `k`. The proof is
the lemma applied to its arguments, so this fixes the argument order a caller uses and adds no
content.

Scope: the conclusion is about one index. Bounding the whole family requires the weights `w k` to be
positive at every index of interest — an index the sum happens to miss, or one whose weight vanishes,
is not covered.

DERIVED: `0` occurs four times — the lower bounds on `w k` and `lam k`, the positivity threshold of
`ρ`, and, now as a binder, the positivity of the selected weight `w k`. No other numeral appears. -/
example {ι : Type*} (s : Finset ι) (w lam : ι → ℝ) (M ρ : ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hlam : ∀ k ∈ s, 0 ≤ lam k) (hρ : 0 < ρ)
    (hbound : ∀ τ : ℕ, (∑ k ∈ s, w k * lam k ^ τ) ≤ M * ρ ^ τ)
    (k : ι) (hk : k ∈ s) (hwk : 0 < w k) : lam k ≤ ρ :=
  le_of_positive_weight_decay s w lam M ρ hw hlam hρ hbound k hk hwk

end MassGap
