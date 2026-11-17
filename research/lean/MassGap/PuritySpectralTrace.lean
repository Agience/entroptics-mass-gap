import Mathlib

/-!
# MassGap.PuritySpectralTrace — the spectral expansion of `Tr R^T`, on finite-dimensional spaces

The spectral expansion in the proofs of Proposition 6.1 and Theorem D.1 of D. Bhattacharjee,
U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford and S. Singha Roy, *Thermal Purity
Bounds for Yang–Mills Theory at Weak Coupling* (research draft, 15 November 2026,
<https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`), on a
finite-dimensional inner product space. `K` is symmetric with eigenvalues `λ_i` and eigenbasis `e_i`
(Mathlib's `eigenvalues`, `eigenvectorBasis`), and `R = λ_{i₀}⁻¹ K` for an index `i₀` with
`λ_{i₀} ≠ 0`.

* `pow_apply_eigenvectorBasis`: `K^k e_i = λ_i^k e_i`.
* `re_inner_pow_eq`: `re ⟪K^T x, x⟫ = Σ_i λ_i^T ‖⟪e_i, x⟫‖²`.
* `trace_pow_eq`, `re_trace_pow_eq`: `Tr K^k = Σ_i λ_i^k`; at `k = 2`, `Tr K² = Σ_i λ_i²`.
* `re_trace_pow_eq_of_basis`: `re Tr C^k = Σ_i μ_i^k` for any orthonormal basis with `C b_i = μ_i b_i`.
* `re_trace_smul_pow`: `re Tr (c K)^T = c^T re Tr K^T` for real `c`.
* `trace_ratio_eq`: `re Tr R^T = 1 + Σ_{i ≠ i₀} (λ_i/λ_{i₀})^T`.
* `one_le_trace_ratio_even`: `re Tr R^{2T} ≥ 1`.
* `one_le_trace_ratio`: for `K ≥ 0` and `λ_{i₀} > 0`, `re Tr R^T ≥ 1`, so `Tr R^T > 0`.
-/

namespace MassGap.PuritySpectralTrace

open LinearMap RCLike
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} (hn : Module.finrank 𝕜 E = n)

/-- `K^k e_i = λ_i^k e_i` in the eigenbasis of a symmetric `K`. -/
theorem pow_apply_eigenvectorBasis {K : E →ₗ[𝕜] E} (hK : K.IsSymmetric) (i : Fin n) (k : ℕ) :
    (K ^ k) (hK.eigenvectorBasis hn i) =
      ((hK.eigenvalues hn i ^ k : ℝ) : 𝕜) • hK.eigenvectorBasis hn i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, hK.apply_eigenvectorBasis, smul_smul]
    congr 1
    push_cast
    ring

/-- `re ⟪K^T x, x⟫ = Σ_i λ_i^T ‖⟪e_i, x⟫‖²` for symmetric `K`. -/
theorem re_inner_pow_eq {K : E →ₗ[𝕜] E} (hK : K.IsSymmetric) (x : E) (T : ℕ) :
    re ⟪(K ^ T) x, x⟫_𝕜 =
      ∑ i, hK.eigenvalues hn i ^ T * ‖⟪hK.eigenvectorBasis hn i, x⟫_𝕜‖ ^ 2 := by
  rw [← (hK.eigenvectorBasis hn).sum_inner_mul_inner ((K ^ T) x) x, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hK.pow T x, pow_apply_eigenvectorBasis hn hK, inner_smul_right,
    ← inner_conj_symm x (hK.eigenvectorBasis hn i), mul_assoc, RCLike.conj_mul, ← ofReal_pow,
    ← ofReal_mul, ofReal_re]

/-- The spectral expansion of the trace: `Tr K^k = Σ_i λ_i^k`. -/
theorem trace_pow_eq {K : E →ₗ[𝕜] E} (hK : K.IsSymmetric) (k : ℕ) :
    trace 𝕜 E (K ^ k) = ∑ i, ((hK.eigenvalues hn i ^ k : ℝ) : 𝕜) := by
  rw [trace_eq_sum_inner (K ^ k) (hK.eigenvectorBasis hn)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_apply_eigenvectorBasis hn hK, inner_smul_right, inner_self_eq_norm_sq_to_K,
    (hK.eigenvectorBasis hn).orthonormal.1 i]
  simp

/-- The real form: `re Tr K^k = Σ_i λ_i^k`. -/
theorem re_trace_pow_eq {K : E →ₗ[𝕜] E} (hK : K.IsSymmetric) (k : ℕ) :
    re (trace 𝕜 E (K ^ k)) = ∑ i, hK.eigenvalues hn i ^ k := by
  rw [trace_pow_eq hn hK, map_sum]
  simp only [ofReal_re]

omit [FiniteDimensional 𝕜 E] in
/-- The trace in any orthonormal eigenbasis: if `C b_i = μ_i b_i` for an orthonormal basis `b`,
then `re Tr C^k = Σ_i μ_i^k`. -/
theorem re_trace_pow_eq_of_basis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E)
    {C : E →ₗ[𝕜] E} {μ : ι → ℝ} (hb : ∀ i, C (b i) = (μ i : 𝕜) • b i) (k : ℕ) :
    re (trace 𝕜 E (C ^ k)) = ∑ i, μ i ^ k := by
  have hp : ∀ i, (C ^ k) (b i) = ((μ i ^ k : ℝ) : 𝕜) • b i := by
    intro i
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hb, smul_smul, ← ofReal_mul, pow_succ]
  rw [trace_eq_sum_inner (C ^ k) b, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hp, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
  simp

omit [FiniteDimensional 𝕜 E] in
/-- Scaling: `re Tr (c K)^T = c^T re Tr K^T` for real `c`. -/
theorem re_trace_smul_pow (K : E →ₗ[𝕜] E) (c : ℝ) (T : ℕ) :
    re (trace 𝕜 E (((c : 𝕜) • K) ^ T)) = c ^ T * re (trace 𝕜 E (K ^ T)) := by
  rw [smul_pow, map_smul, smul_eq_mul, ← ofReal_pow, re_ofReal_mul]

/-- The normalized expansion: for `λ_{i₀} ≠ 0` and `R = λ_{i₀}⁻¹ K`,
`re Tr R^T = 1 + Σ_{i ≠ i₀} (λ_i/λ_{i₀})^T`. -/
theorem trace_ratio_eq {K : E →ₗ[𝕜] E} (hK : K.IsSymmetric) (i₀ : Fin n)
    (h : hK.eigenvalues hn i₀ ≠ 0) (T : ℕ) :
    re (trace 𝕜 E (((((hK.eigenvalues hn i₀)⁻¹ : ℝ) : 𝕜) • K) ^ T)) =
      1 + ∑ i ∈ Finset.univ.erase i₀, (hK.eigenvalues hn i / hK.eigenvalues hn i₀) ^ T := by
  rw [re_trace_smul_pow, re_trace_pow_eq hn hK, Finset.mul_sum,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
  congr 1
  · rw [← mul_pow, inv_mul_cancel₀ h, one_pow]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_eq_inv_mul, mul_pow]

/-- Even powers: `re Tr R^{2T} ≥ 1`. -/
theorem one_le_trace_ratio_even {K : E →ₗ[𝕜] E} (hK : K.IsSymmetric) (i₀ : Fin n)
    (h : hK.eigenvalues hn i₀ ≠ 0) (T : ℕ) :
    1 ≤ re (trace 𝕜 E (((((hK.eigenvalues hn i₀)⁻¹ : ℝ) : 𝕜) • K) ^ (2 * T))) := by
  rw [trace_ratio_eq hn hK i₀ h]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => (even_two_mul T).pow_nonneg _)

/-- For `K ≥ 0` and `λ_{i₀} > 0`: `re Tr R^T ≥ 1`. -/
theorem one_le_trace_ratio {K : E →ₗ[𝕜] E} (hK : K.IsPositive) (i₀ : Fin n)
    (h : 0 < hK.isSymmetric.eigenvalues hn i₀) (T : ℕ) :
    1 ≤ re (trace 𝕜 E (((((hK.isSymmetric.eigenvalues hn i₀)⁻¹ : ℝ) : 𝕜) • K) ^ T)) := by
  rw [trace_ratio_eq hn hK.isSymmetric i₀ h.ne']
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ =>
    pow_nonneg (div_nonneg (hK.nonneg_eigenvalues hn i) h.le) _)

end MassGap.PuritySpectralTrace

#print axioms MassGap.PuritySpectralTrace.pow_apply_eigenvectorBasis
#print axioms MassGap.PuritySpectralTrace.re_inner_pow_eq
#print axioms MassGap.PuritySpectralTrace.trace_pow_eq
#print axioms MassGap.PuritySpectralTrace.re_trace_pow_eq
#print axioms MassGap.PuritySpectralTrace.re_trace_pow_eq_of_basis
#print axioms MassGap.PuritySpectralTrace.re_trace_smul_pow
#print axioms MassGap.PuritySpectralTrace.trace_ratio_eq
#print axioms MassGap.PuritySpectralTrace.one_le_trace_ratio_even
#print axioms MassGap.PuritySpectralTrace.one_le_trace_ratio
