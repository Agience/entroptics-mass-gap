import MassGap.PurityWilson

/-!
# MassGap.PurityCharacter — the scalar content of Proposition C.1 of the purity paper

Proposition C.1 (temporal spectrum comparison) of D. Bhattacharjee, U. Bhattacharya,
J. M. Lockwood, T. Romanov, I. J. Sessford and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills
Theory at Weak Coupling* (research draft, 15 November 2026, <https://github.com/anaxia-research/4Y-M>,
commit 8e01510, `Paper-2/Paper-2.pdf`).

`K = D C_b Π D` with `C_b` the tensor product over `M` spatial links of convolution by `k_b`,
`a_ρ ≥ 0` its character eigenvalues, `a₀ > 0` the trivial one, `J_s = ∫ e^{−V_s}` and
`E = e^{max V_s}`. The proof's operator inputs enter as hypotheses: the Rayleigh bound
`λ₀ ≥ a₀^M / J_s` and the min–max comparison `λ_f ≤ E ∏_l a_{f(l)}`; (C.1) with the trace on the
left and no eigenvalue-wise comparison is `PurityTemporalOperator.temporal_trace_tensor`. Eigenvalues of `C_b` are indexed
by `f : Fin M → ι` over a finite set `R` of representation labels, each label listed with its
multiplicity, so the bounds hold for every finite truncation of the representation sum.

* `ratio_le`, `trace_le`: `Σ (λ_i/λ₀)^T ≤ (E J)^T Σ (c_i/A)^T` from `λ_i ≤ E c_i`, `λ₀ ≥ A/J`.
* `tensor_sum`: `Σ_f (∏_l a_{f(l)} / a₀^M)^T = (Σ_ρ (a_ρ/a₀)^T)^M`.
* `temporal_comparison`: (C.1), `Σ_f (λ_f/λ₀)^T ≤ (E J_s)^T (Σ_ρ (a_ρ/a₀)^T)^M`.
* `vacuum_ge_one`: `∫ V dν = 0` gives `J = ∫ e^{−V} dν ≥ 1` (Jensen).
* `char_sum_ge_one`: the trivial label (`a_ρ = a₀`) makes the character sum at least `1`.
* `log_lower`: `J ≥ 1`, `S ≥ 1` give `log((e^{bP} J)^T S^M) ≥ bPT`, the lower bound on the
  right-hand side of (C.1) with `max V_s = b|P_s|`.

Not formalized here: the concrete operators `C_b` and `Π` on `L²(G^M)` and `C_b Π = Π C_b` from
gauge covariance; for a general compact group, the fusion rule `g Re χ_ρ = Σ_σ N_σ Re χ_σ` with
`N_σ ≥ 0`, `∫ Re χ_σ ≥ 0`, `|Re χ_ρ| ≤ d_ρ` and `∫ k_b Im χ_ρ = 0` (for SU(2), the fusion rule with
`N_σ ≥ 0` and `|χ_n| ≤ n + 1` are `PuritySU2Character.fusion` and `PuritySU2Character.abs_chi_le`;
`Re ∫ Tr σ ≥ 0` for every continuous representation is
`PurityRepCharacter.re_integral_trace_nonneg`; `|Re Tr U| ≤ d` for the defining representation is
`GaugeGroup.abs_re_trace_repM_le`; from the fusion rule and `∫ Re χ_σ ≥ 0`, `a_ρ ≥ 0` is
`PurityCharCoeff.charCoeff_exp_nonneg`, and for the characters `Re Tr σ` of continuous
representations of every compact gauge group, with no fusion rule, it is
`PurityRepCharacter.charCoeff_nonneg`; `|a_ρ| ≤ a₀` from `|χ_ρ| ≤ d_ρ` is
`PurityCharCoeff.abs_charCoeff_le`; `a₀ > 0` is `PurityCharCoeff.a0_pos`; `J_s ≥ 1` at SU(N) is
`PurityVacuumMean.vacuum_ge_one_SU`); `J_s > 0` for a general compact group;
absolute convergence of the representation sum and the limit from finite truncations to the full
sum; the test-vector inputs `C_b 1 = a₀^M 1`, `Π 1 = 1` and `‖D⁻¹1‖² = J_s` for the
concrete operators; the order estimate `|P_s| = 3V(s)`, `s_j ≳ T` giving order `bT⁴`. The SU(2)
Bessel form `a_j/a₀ = I_{2j+1}(b)/I₁(b)` is `PuritySU2Bessel.coeff_div_coeff_zero`.
For a continuous class function `k` (e.g. `k_b`), every `f ∈ L²(G)` with `k ⋆ f = a f` almost
everywhere lies in the closed span of the coefficients of the continuous irreducible unitary `ρ`
of positive dimension with `a_ρ = a` (`PurityEigenspace.mem_coeffSpan`). On one
slice of `RectWilsonG`, `∫ V_s dU = 0`, `J_s ≥ 1` and `max V_s = b|P_s|` are
`PurityVacuumMean`. In finite dimension, for `C ≥ 0`, a projection `P`
commuting with `C`, symmetric `D` with `‖D y‖² ≤ c ‖y‖²` and `K = D C P D`, `Tr (K/l)^T ≤ (c J)^T Tr (C/A)^T`
for `l ≥ A/J`, and the Rayleigh bound `λ₀(K) ≥ A/J` from a test vector `w` with `D w = u`, `P u = u`,
`C u = A u`, `‖w‖² ≤ J ‖u‖²`, the sorted eigenvalue bound `λ_j(K) ≤ c λ_j(C)`, and, for `C`
diagonal in a label basis, `Tr (K/l)^T ≤ (c J)^T (Σ_ι (a/a₀)^T)^M` (`temporal_trace_tensor`), are
`PurityTemporalOperator`.
-/

namespace MassGap.PurityCharacter

open MeasureTheory Real

/-- The comparison step: `λ ≤ E c` and `λ₀ ≥ A/J > 0` give `λ/λ₀ ≤ E J (c/A)`. -/
theorem ratio_le {lam lam0 c E J A : ℝ} (hA : 0 < A) (hJ : 0 < J) (hE : 0 ≤ E) (hc : 0 ≤ c)
    (h0 : A / J ≤ lam0) (hlc : lam ≤ E * c) : lam / lam0 ≤ E * J * (c / A) := by
  have hl0 : 0 < lam0 := (div_pos hA hJ).trans_le h0
  rw [div_le_iff₀ hl0]
  calc lam ≤ E * c := hlc
    _ = E * J * (c / A) * (A / J) := by field_simp
    _ ≤ E * J * (c / A) * lam0 :=
        mul_le_mul_of_nonneg_left h0 (mul_nonneg (mul_nonneg hE hJ.le) (div_nonneg hc hA.le))

/-- `Σ (λ_i/λ₀)^T ≤ (E J)^T Σ (c_i/A)^T`. -/
theorem trace_le {ι : Type*} (s : Finset ι) (lam c : ι → ℝ) {lam0 E J A : ℝ} (T : ℕ)
    (hA : 0 < A) (hJ : 0 < J) (hE : 0 ≤ E) (hl : ∀ i ∈ s, 0 ≤ lam i) (hc : ∀ i ∈ s, 0 ≤ c i)
    (h0 : A / J ≤ lam0) (hlc : ∀ i ∈ s, lam i ≤ E * c i) :
    ∑ i ∈ s, (lam i / lam0) ^ T ≤ (E * J) ^ T * ∑ i ∈ s, (c i / A) ^ T := by
  have hl0 : 0 < lam0 := (div_pos hA hJ).trans_le h0
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [← mul_pow]
  exact pow_le_pow_left₀ (div_nonneg (hl i hi) hl0.le)
    (ratio_le hA hJ hE (hc i hi) h0 (hlc i hi)) T

/-- The tensor-product character sum: `Σ_f (∏_l a_{f(l)} / a₀^M)^T = (Σ_ρ (a_ρ/a₀)^T)^M`. -/
theorem tensor_sum {ι : Type*} (R : Finset ι) (a : ι → ℝ) (a0 : ℝ) (M T : ℕ) :
    ∑ f ∈ Fintype.piFinset (fun _ : Fin M => R), ((∏ l, a (f l)) / a0 ^ M) ^ T =
      (∑ ρ ∈ R, (a ρ / a0) ^ T) ^ M := by
  have h : ∀ f : Fin M → ι, ((∏ l, a (f l)) / a0 ^ M) ^ T = ∏ l, (a (f l) / a0) ^ T := by
    intro f
    rw [Finset.prod_pow, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  simp_rw [h]
  rw [show (∑ ρ ∈ R, (a ρ / a0) ^ T) ^ M = ∏ _l : Fin M, ∑ ρ ∈ R, (a ρ / a0) ^ T by simp,
    Finset.prod_univ_sum]

/-- (C.1): `Σ_f (λ_f/λ₀)^T ≤ (E J)^T (Σ_ρ (a_ρ/a₀)^T)^M`, given `λ₀ ≥ a₀^M/J` and
`λ_f ≤ E ∏_l a_{f(l)}`. -/
theorem temporal_comparison {ι : Type*} {M : ℕ} (R : Finset ι) (a : ι → ℝ)
    (lam : (Fin M → ι) → ℝ) {a0 lam0 E J : ℝ} (T : ℕ) (ha0 : 0 < a0) (hJ : 0 < J) (hE : 0 ≤ E)
    (ha : ∀ ρ ∈ R, 0 ≤ a ρ) (hl : ∀ f ∈ Fintype.piFinset (fun _ : Fin M => R), 0 ≤ lam f)
    (h0 : a0 ^ M / J ≤ lam0)
    (hlc : ∀ f ∈ Fintype.piFinset (fun _ : Fin M => R), lam f ≤ E * ∏ l, a (f l)) :
    ∑ f ∈ Fintype.piFinset (fun _ : Fin M => R), (lam f / lam0) ^ T ≤
      (E * J) ^ T * (∑ ρ ∈ R, (a ρ / a0) ^ T) ^ M := by
  rw [← tensor_sum R a a0 M T]
  exact trace_le _ lam (fun f => ∏ l, a (f l)) T (pow_pos ha0 M) hJ hE hl
    (fun f hf => Finset.prod_nonneg fun l _ => ha (f l) (Fintype.mem_piFinset.1 hf l)) h0 hlc

/-- Jensen: `∫ V dν = 0` gives `∫ e^{−V} dν ≥ 1`. -/
theorem vacuum_ge_one {G : Type*} [MeasurableSpace G] {ν : Measure G} [IsProbabilityMeasure ν]
    {V : G → ℝ} (hV : Integrable V ν) (heV : Integrable (fun g => exp (-V g)) ν)
    (h0 : ∫ g, V g ∂ν = 0) : 1 ≤ ∫ g, exp (-V g) ∂ν := by
  have := PurityWilson.kernel_lower (F := fun g => -V g) (c := 0) hV.neg heV
    (by rw [integral_neg, h0, neg_zero])
  simpa using this

/-- The trivial label `ρ₀` with `a_{ρ₀} = a₀ ≠ 0` makes the character sum at least `1`. -/
theorem char_sum_ge_one {ι : Type*} (R : Finset ι) (a : ι → ℝ) {a0 : ℝ} {ρ0 : ι} (T : ℕ)
    (ha0 : 0 < a0) (ha : ∀ ρ ∈ R, 0 ≤ a ρ) (hρ0 : ρ0 ∈ R) (htriv : a ρ0 = a0) :
    1 ≤ ∑ ρ ∈ R, (a ρ / a0) ^ T := by
  have := Finset.single_le_sum (fun ρ hρ => pow_nonneg (div_nonneg (ha ρ hρ) ha0.le) T) hρ0
  rwa [htriv, div_self ha0.ne', one_pow] at this

/-- `J ≥ 1`, `S ≥ 1` give `log((e^{bP} J)^T S^M) ≥ bPT`. -/
theorem log_lower {b P J S : ℝ} {T M : ℕ} (hJ : 1 ≤ J) (hS : 1 ≤ S) :
    b * P * T ≤ log ((exp (b * P) * J) ^ T * S ^ M) := by
  have hJ0 : 0 < J := by linarith
  have hS0 : 0 < S := by linarith
  rw [log_mul (pow_ne_zero _ (mul_pos (exp_pos _) hJ0).ne') (pow_ne_zero _ hS0.ne'), log_pow,
    log_pow, log_mul (exp_pos _).ne' hJ0.ne', log_exp]
  have := log_nonneg hJ
  have := log_nonneg hS
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  nlinarith

end MassGap.PurityCharacter

#print axioms MassGap.PurityCharacter.ratio_le
#print axioms MassGap.PurityCharacter.trace_le
#print axioms MassGap.PurityCharacter.tensor_sum
#print axioms MassGap.PurityCharacter.temporal_comparison
#print axioms MassGap.PurityCharacter.vacuum_ge_one
#print axioms MassGap.PurityCharacter.char_sum_ge_one
#print axioms MassGap.PurityCharacter.log_lower
