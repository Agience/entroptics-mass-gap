import Mathlib

/-!
# MassGap.WitnessVacuity — the constant witness carries no physics, machine-checked

This file exists so that a claim made in prose elsewhere is instead **checked**: that a theorem whose only
mode family is the constant `1/5` says nothing about Yang–Mills, however clean its axiom footprint reads.

It imports **`Mathlib` and nothing else**. No `MassGap` module is in scope: no Wilson ensemble, no `readA`,
no entropy floor, no reflection positivity. If this file compiles, the statements below are consequences of
arithmetic.

## What is checked

* `const_witness_conclusion_is_arithmetic` — the conclusion that the retired `ym_mass_gap_spectral` reached
  (`‖∑_k P_k m_k^τ‖ → 0` at `m ≡ 1/5`, `P ≡ 1`, three modes) is reproduced here verbatim in shape, with zero
  physics in scope. So the retired statement's content was `3·(1/5)^τ → 0`.
* `aperture_hypothesis_is_load_bearing` — the replacement `ym_mass_gap_spectral` quantifies over an arbitrary
  mode family and gates on `‖m_k‖ ≤ m_hi ≤ 3^{-1/4}`. That hypothesis is not decoration: drop it and the
  conclusion is false, witnessed here by a mode of magnitude `2`, whose correlator diverges.

Together these say the change made in P1 was a real one — the old statement was provable without the theory,
and the new statement is not provable without its hypothesis.

Imported by `MassGap.lean` so it is rebuilt with everything else. It proves nothing about `SU(N)`; that is the
point.
-/

namespace MassGap.WitnessVacuity

open Filter

/-- **The retired witness statement, reproduced from arithmetic alone.** This is the conclusion the old
`ym_mass_gap_spectral` reached, at the constant family it used (`m ≡ 1/5`, `P ≡ 1`, `Fin 3`). Nothing from the
Yang–Mills development is in scope in this file, so whatever that theorem's `#print axioms` reported, this is
all it established.

The coupling `_β` is spelled with an underscore because the linter is right that it is unused — as it was in
the original, where the mode family discarded it. -/
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

/-- **The aperture hypothesis is load-bearing — the conclusion fails without it.** A single mode of magnitude
`2` with unit weight: the correlator norm is `2^τ`, which tends to `atTop`, not to `0`. So the replacement
`ym_mass_gap_spectral` cannot drop `hmargin`/`haperture` — unlike the retired form, whose hypotheses were
discharged by the definition of its own mode family.

This is the negative case: it is what makes the new statement's hypotheses content rather than ceremony. -/
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
