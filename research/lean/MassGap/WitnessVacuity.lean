import Mathlib

/-!
# MassGap.WitnessVacuity — two arithmetic facts about geometric correlator sums

This file imports `Mathlib` and nothing else. No `MassGap` module is in scope: no Wilson ensemble, no
`readA`, no entropy floor, no reflection positivity. Both theorems are therefore statements of real
and complex arithmetic, and neither mentions a gauge group.

Both concern the same shape, `‖∑_{k} P_k · m_k^τ‖` as `τ : ℕ` runs to infinity, at two explicit mode
families.

* `const_witness_conclusion_is_arithmetic` — at unit weights and the constant mode `1/5` over three
  modes, that norm equals `3 · (1/5)^τ` and tends to `0`. The statement also takes a real argument
  `_β`, which no part of the conclusion mentions.
* `aperture_hypothesis_is_load_bearing` — at a unit weight and the single mode `2`, the same norm
  equals `2^τ`, which tends to `atTop`; the limit `0` therefore fails. So the shape above does not
  tend to `0` for an arbitrary mode family, and any statement of it needs a hypothesis bounding the
  mode magnitudes.

Imported by `MassGap.lean`, so it is rebuilt with the rest of the tree.
-/

namespace MassGap.WitnessVacuity

open Filter

/-- For every real `_β`, the sequence `τ ↦ ‖∑_{k : Fin 3} 1 · ((1/5 : ℝ) : ℂ)^τ‖` converges to `0`
along `atTop`.

The proof rewrites the norm as `3 * (1/5)^τ` and applies the geometric limit for a ratio in `[0, 1)`.
The argument `_β` is bound but unused: no numeral, index or bound in the conclusion depends on it, so
the statement is the same limit for every real number.

CHOSEN: the mode family is explicit rather than quantified. `1/5` is the mode magnitude, `1` the
weight attached to each mode, and `3` the number of modes summed over via `Fin 3`; all three are
written into the statement rather than derived from anything. `0` is the limit point asserted. -/
theorem const_witness_conclusion_is_arithmetic (_β : ℝ) :
    Tendsto (fun τ : ℕ => ‖∑ _k : Fin 3, (1 : ℂ) * ((1 / 5 : ℝ) : ℂ) ^ τ‖) atTop (nhds 0) := by
  have h : ∀ τ : ℕ, ‖∑ _k : Fin 3, (1 : ℂ) * ((1 / 5 : ℝ) : ℂ) ^ τ‖ = 3 * (1 / 5 : ℝ) ^ τ := by
    intro τ
    simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    norm_num
  simp only [h]
  have hp : Tendsto (fun τ : ℕ => (1 / 5 : ℝ) ^ τ) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa using hp.const_mul (3 : ℝ)

/-- The sequence `τ ↦ ‖∑_{k : Fin 1} 1 · ((2 : ℝ) : ℂ)^τ‖` does not converge to `0` along `atTop`.

The proof rewrites the norm as `2^τ` and observes that a base above `1` tends to `atTop`, which no
sequence converging in a neighbourhood of `0` can do. This is the negative case for the shape in
`const_witness_conclusion_is_arithmetic`: a hypothesis constraining the mode magnitudes is needed for
that limit, since a single mode of magnitude `2` already defeats it.

CHOSEN: `2` is the mode magnitude, picked to exceed `1` so the power diverges; `1` is both the weight
and the number of modes, via `Fin 1`, so a single term carries the whole sum. `0` is the limit point
whose attainment is denied. -/
theorem aperture_hypothesis_is_load_bearing :
    ¬ Tendsto (fun τ : ℕ => ‖∑ _k : Fin 1, (1 : ℂ) * ((2 : ℝ) : ℂ) ^ τ‖) atTop (nhds 0) := by
  have h : ∀ τ : ℕ, ‖∑ _k : Fin 1, (1 : ℂ) * ((2 : ℝ) : ℂ) ^ τ‖ = 2 ^ τ := by
    intro τ
    simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
    rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  simp only [h]
  intro hcon
  have hdiv : Tendsto (fun τ : ℕ => (2 : ℝ) ^ τ) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  exact not_tendsto_nhds_of_tendsto_atTop hdiv 0 hcon

#print axioms const_witness_conclusion_is_arithmetic
#print axioms aperture_hypothesis_is_load_bearing

end MassGap.WitnessVacuity
