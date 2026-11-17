import Mathlib

/-!
# MassGap.PurityStability — trace-norm stability of the purity, on finite-dimensional spaces

Proposition 3.1 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford and
S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510), for density operators
on a finite-dimensional inner product space: the setting of its finite matrix certificates.

For a symmetric `D` the trace norm is the sum of the absolute values of its eigenvalues (`tnorm`).

* `re_trace_mul_eq`: `re Tr(D X) = Σᵢ λᵢ re⟪bᵢ, X bᵢ⟫` in an eigenbasis of `D`.
* `abs_re_trace_mul_le`: `|re Tr(D X)| ≤ ‖D‖₁` when `|re⟪bᵢ, X bᵢ⟫| ≤ 1` on that eigenbasis.
* `purity_diff_le`: `|Tr ρ² − Tr σ²| ≤ ‖ρ − σ‖₁` for density operators `ρ, σ` (paper, (3.1)).

DERIVED (module-wide): `1` the trace of a density operator.
-/

namespace MassGap.PurityStability

open LinearMap RCLike
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} (hn : Module.finrank 𝕜 E = n)

/-- The trace norm of a symmetric operator: `Σᵢ |λᵢ|`. -/
noncomputable def tnorm {D : E →ₗ[𝕜] E} (hD : D.IsSymmetric) : ℝ := ∑ i, |hD.eigenvalues hn i|

/-- `re Tr(D X) = Σᵢ λᵢ re⟪bᵢ, X bᵢ⟫` in the eigenbasis `b` of a symmetric `D`. -/
theorem re_trace_mul_eq {D : E →ₗ[𝕜] E} (hD : D.IsSymmetric) (X : E →ₗ[𝕜] E) :
    re (trace 𝕜 E (D * X)) = ∑ i, hD.eigenvalues hn i *
      re ⟪hD.eigenvectorBasis hn i, X (hD.eigenvectorBasis hn i)⟫_𝕜 := by
  rw [trace_eq_sum_inner (D * X) (hD.eigenvectorBasis hn), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.End.mul_apply, ← hD, hD.apply_eigenvectorBasis, inner_smul_left, conj_ofReal,
    re_ofReal_mul]

/-- **Trace duality on an eigenbasis.** -/
theorem abs_re_trace_mul_le {D : E →ₗ[𝕜] E} (hD : D.IsSymmetric) (X : E →ₗ[𝕜] E)
    (hX : ∀ i, |re ⟪hD.eigenvectorBasis hn i, X (hD.eigenvectorBasis hn i)⟫_𝕜| ≤ 1) :
    |re (trace 𝕜 E (D * X))| ≤ tnorm hn hD := by
  rw [re_trace_mul_eq hn hD X, tnorm]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hX i)

omit [FiniteDimensional 𝕜 E] in
/-- The diagonal entries of a density operator in any orthonormal basis lie in `[0, 1]`. -/
theorem diag_mem {ρ : E →ₗ[𝕜] E} (hρ : ρ.IsPositive) (hρ1 : trace 𝕜 E ρ = 1)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    0 ≤ re ⟪b i, ρ (b i)⟫_𝕜 ∧ re ⟪b i, ρ (b i)⟫_𝕜 ≤ 1 := by
  have h0 : ∀ j, 0 ≤ re ⟪b j, ρ (b j)⟫_𝕜 := fun j => hρ.re_inner_nonneg_right (b j)
  refine ⟨h0 i, ?_⟩
  have hs : ∑ j, re ⟪b j, ρ (b j)⟫_𝕜 = 1 := by
    rw [← map_sum, ← trace_eq_sum_inner ρ b, hρ1, one_re]
  rw [← hs]
  exact Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)

/-- **Proposition 3.1.** For density operators, `|Tr ρ² − Tr σ²| ≤ ‖ρ − σ‖₁`. -/
theorem purity_diff_le {ρ σ : E →ₗ[𝕜] E} (hρ : ρ.IsPositive) (hσ : σ.IsPositive)
    (hρ1 : trace 𝕜 E ρ = 1) (hσ1 : trace 𝕜 E σ = 1) :
    |re (trace 𝕜 E (ρ * ρ)) - re (trace 𝕜 E (σ * σ))| ≤
      tnorm hn (hρ.isSymmetric.sub hσ.isSymmetric) := by
  have hD := hρ.isSymmetric.sub hσ.isSymmetric
  have hexp : (ρ - σ) * (ρ + σ - 1) = ρ * ρ - σ * σ + (ρ * σ - σ * ρ) - (ρ - σ) := by
    noncomm_ring
  have htr : trace 𝕜 E ((ρ - σ) * (ρ + σ - 1)) = trace 𝕜 E (ρ * ρ) - trace 𝕜 E (σ * σ) := by
    rw [hexp, map_sub, map_add, map_sub, map_sub, map_sub, LinearMap.trace_mul_comm (R := 𝕜) ρ σ,
      hρ1, hσ1]
    ring
  have key := abs_re_trace_mul_le hn hD (ρ + σ - 1) (fun i => by
    set b := hD.eigenvectorBasis hn
    have hρi := diag_mem hρ hρ1 b i
    have hσi := diag_mem hσ hσ1 b i
    have hb : re ⟪b i, b i⟫_𝕜 = 1 := by
      rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]; simp
    rw [LinearMap.sub_apply, LinearMap.add_apply, Module.End.one_apply, inner_sub_right,
      inner_add_right, map_sub, map_add, hb]
    rw [abs_le]; constructor <;> linarith [hρi.1, hρi.2, hσi.1, hσi.2])
  rw [htr, map_sub] at key
  exact key

/-- `Tr(D X) = Σᵢ λᵢ ⟪bᵢ, X bᵢ⟫` in the eigenbasis `b` of a symmetric `D`. -/
theorem trace_mul_eq_sum {D : E →ₗ[𝕜] E} (hD : D.IsSymmetric) (X : E →ₗ[𝕜] E) :
    trace 𝕜 E (D * X) = ∑ i, (hD.eigenvalues hn i : 𝕜) *
      ⟪hD.eigenvectorBasis hn i, X (hD.eigenvectorBasis hn i)⟫_𝕜 := by
  rw [trace_eq_sum_inner (D * X) (hD.eigenvectorBasis hn)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.End.mul_apply, ← hD, hD.apply_eigenvectorBasis, inner_smul_left, conj_ofReal]

section Sign

variable {D : E →ₗ[𝕜] E} (hD : D.IsSymmetric)

/-- The sign of the `i`-th eigenvalue, with `0 ↦ 1`. -/
noncomputable def sgn (i : Fin n) : ℝ := if 0 ≤ hD.eigenvalues hn i then 1 else -1

/-- The sign operator `S = Σᵢ sgn(λᵢ) |bᵢ⟩⟨bᵢ|` of a symmetric `D`. -/
noncomputable def sgnOp : E →ₗ[𝕜] E :=
  ∑ i, ((sgn hn hD i : ℝ) : 𝕜) •
    ((InnerProductSpace.rankOne 𝕜 (hD.eigenvectorBasis hn i) (hD.eigenvectorBasis hn i) :
      E →L[𝕜] E) : E →ₗ[𝕜] E)

theorem sgnOp_apply (v : E) :
    sgnOp hn hD v = ∑ i, ((sgn hn hD i : ℝ) : 𝕜) •
      (⟪hD.eigenvectorBasis hn i, v⟫_𝕜 • hD.eigenvectorBasis hn i) := by
  simp [sgnOp, LinearMap.coe_sum, Finset.sum_apply, InnerProductSpace.rankOne_apply]

theorem sgnOp_basis (j : Fin n) :
    sgnOp hn hD (hD.eigenvectorBasis hn j) =
      ((sgn hn hD j : ℝ) : 𝕜) • hD.eigenvectorBasis hn j := by
  rw [sgnOp_apply]
  have h := orthonormal_iff_ite.mp (hD.eigenvectorBasis hn).orthonormal
  simp [h, ite_smul, smul_ite, Finset.sum_ite_eq']

theorem abs_sgn (i : Fin n) : |sgn hn hD i| = 1 := by
  unfold sgn; split_ifs <;> simp

/-- `|⟪x, S y⟫| ≤ ‖x‖ ‖y‖`. -/
theorem norm_inner_sgnOp_le (x y : E) : ‖⟪x, sgnOp hn hD y⟫_𝕜‖ ≤ ‖x‖ * ‖y‖ := by
  set b := hD.eigenvectorBasis hn
  rw [sgnOp_apply, inner_sum]
  calc ‖∑ i, ⟪x, ((sgn hn hD i : ℝ) : 𝕜) • (⟪b i, y⟫_𝕜 • b i)⟫_𝕜‖
      ≤ ∑ i, ‖⟪x, b i⟫_𝕜‖ * ‖⟪b i, y⟫_𝕜‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [inner_smul_right, inner_smul_right, norm_mul, norm_mul, RCLike.norm_ofReal,
          abs_sgn, one_mul, mul_comm]
    _ ≤ √(∑ i, ‖⟪x, b i⟫_𝕜‖ ^ 2) * √(∑ i, ‖⟪b i, y⟫_𝕜‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = ‖x‖ * ‖y‖ := by
        rw [b.sum_sq_norm_inner_left, b.sum_sq_norm_inner_right, Real.sqrt_sq (norm_nonneg _),
          Real.sqrt_sq (norm_nonneg _)]

/-- **Trace duality is attained**: `re Tr(D S) = ‖D‖₁`. -/
theorem re_trace_mul_sgnOp : re (trace 𝕜 E (D * sgnOp hn hD)) = tnorm hn hD := by
  rw [re_trace_mul_eq hn hD, tnorm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sgnOp_basis, inner_smul_right, inner_self_eq_norm_sq_to_K,
    (hD.eigenvectorBasis hn).orthonormal.1 i]
  simp only [ofReal_one, one_pow, mul_one, ofReal_re]
  unfold sgn
  split_ifs with h
  · rw [mul_one, abs_of_nonneg h]
  · rw [abs_of_neg (not_le.mp h)]; ring

end Sign

section Truncation

omit [FiniteDimensional 𝕜 E] in
/-- A symmetric idempotent `P` has `‖P x‖² = re⟪x, P x⟫`. -/
theorem norm_sq_proj {P : E →ₗ[𝕜] E} (hPs : P.IsSymmetric) (hPP : P * P = P) (x : E) :
    ‖P x‖ ^ 2 = re ⟪x, P x⟫_𝕜 := by
  have hpp : P (P x) = P x := by rw [← Module.End.mul_apply, hPP]
  rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), hPs x (P x), hpp]

omit [FiniteDimensional 𝕜 E] in
theorem norm_proj_le {P : E →ₗ[𝕜] E} (hPs : P.IsSymmetric) (hPP : P * P = P) (x : E) :
    ‖P x‖ ≤ ‖x‖ := by
  have h1 := norm_sq_proj hPs hPP x
  have h2 : re ⟪x, P x⟫_𝕜 ≤ ‖x‖ * ‖P x‖ := (re_le_norm _).trans (norm_inner_le_norm _ _)
  by_contra hc
  have hc' := not_le.mp hc
  nlinarith [norm_nonneg x, norm_nonneg (P x), mul_lt_mul_of_pos_right hc'
    (lt_of_le_of_lt (norm_nonneg x) hc')]

omit [FiniteDimensional 𝕜 E] in
theorem compl_sym {P : E →ₗ[𝕜] E} (hPs : P.IsSymmetric) : (1 - P).IsSymmetric := by
  intro x y
  rw [LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply, Module.End.one_apply,
    inner_sub_left, inner_sub_right, hPs x y]

omit [FiniteDimensional 𝕜 E] in
theorem compl_idem {P : E →ₗ[𝕜] E} (hPP : P * P = P) : (1 - P) * (1 - P) = 1 - P := by
  calc (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
    _ = 1 - P := by rw [hPP]; abel

/-- The truncated state `σ = (1 − q)⁻¹ P ρ P`, `q = re Tr((1 − P) ρ)`. -/
noncomputable def trunc (ρ P : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  (((1 - re (trace 𝕜 E ((1 - P) * ρ)))⁻¹ : ℝ) : 𝕜) • (P * ρ * P)

omit [FiniteDimensional 𝕜 E] in
theorem trunc_sym {ρ P : E →ₗ[𝕜] E} (hρ : ρ.IsSymmetric) (hPs : P.IsSymmetric) :
    (ρ - trunc ρ P).IsSymmetric := by
  intro x y
  simp only [trunc, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, conj_ofReal]
  rw [hρ x y, hPs, hρ, hPs]

variable {ρ : E →ₗ[𝕜] E} (hρ : ρ.IsPositive)

theorem eig_re (k : Fin n) :
    re ⟪hρ.isSymmetric.eigenvectorBasis hn k, ρ (hρ.isSymmetric.eigenvectorBasis hn k)⟫_𝕜 =
      hρ.isSymmetric.eigenvalues hn k := by
  rw [hρ.isSymmetric.apply_eigenvectorBasis, inner_smul_right, inner_self_eq_norm_sq_to_K,
    (hρ.isSymmetric.eigenvectorBasis hn).orthonormal.1 k]
  simp

theorem eig_nonneg (k : Fin n) : 0 ≤ hρ.isSymmetric.eigenvalues hn k := by
  rw [← eig_re hn hρ k]; exact hρ.re_inner_nonneg_right _

theorem eig_sum (hρ1 : trace 𝕜 E ρ = 1) : ∑ k, hρ.isSymmetric.eigenvalues hn k = 1 := by
  rw [← hρ.isSymmetric.re_trace_eq_sum_eigenvalues hn, hρ1, one_re]

theorem norm_trace_mul_le (X : E →ₗ[𝕜] E) (f : Fin n → ℝ)
    (hf : ∀ k, ‖⟪hρ.isSymmetric.eigenvectorBasis hn k,
      X (hρ.isSymmetric.eigenvectorBasis hn k)⟫_𝕜‖ ≤ f k) :
    ‖trace 𝕜 E (ρ * X)‖ ≤ ∑ k, hρ.isSymmetric.eigenvalues hn k * f k := by
  rw [trace_mul_eq_sum hn hρ.isSymmetric X]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (eig_nonneg hn hρ k)]
  exact mul_le_mul_of_nonneg_left (hf k) (eig_nonneg hn hρ k)

/-- `Σₖ pₖ ‖P eₖ‖² = re Tr(P ρ)` for a symmetric idempotent `P`. -/
theorem sum_eig_norm_sq {P : E →ₗ[𝕜] E} (hPs : P.IsSymmetric) (hPP : P * P = P) :
    ∑ k, hρ.isSymmetric.eigenvalues hn k * ‖P (hρ.isSymmetric.eigenvectorBasis hn k)‖ ^ 2 =
      re (trace 𝕜 E (P * ρ)) := by
  rw [LinearMap.trace_mul_comm (R := 𝕜) P ρ, re_trace_mul_eq hn hρ.isSymmetric P]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_sq_proj hPs hPP]

/-- `Σₖ pₖ ‖P eₖ‖ ≤ √(re Tr(P ρ))` for a density operator. -/
theorem sum_eig_norm_le (hρ1 : trace 𝕜 E ρ = 1) {P : E →ₗ[𝕜] E} (hPs : P.IsSymmetric)
    (hPP : P * P = P) :
    ∑ k, hρ.isSymmetric.eigenvalues hn k * ‖P (hρ.isSymmetric.eigenvectorBasis hn k)‖ ≤
      √(re (trace 𝕜 E (P * ρ))) := by
  set p := hρ.isSymmetric.eigenvalues hn
  set e := hρ.isSymmetric.eigenvectorBasis hn
  have hp := eig_nonneg hn hρ
  have hcs : ∑ k, √(p k) * √(p k * ‖P (e k)‖ ^ 2) ≤
      √(∑ k, p k) * √(∑ k, p k * ‖P (e k)‖ ^ 2) :=
    Real.sum_sqrt_mul_sqrt_le Finset.univ hp (fun k => mul_nonneg (hp k) (sq_nonneg ‖P (e k)‖))
  have hterm : ∀ k, √(p k) * √(p k * ‖P (e k)‖ ^ 2) = p k * ‖P (e k)‖ := by
    intro k
    rw [Real.sqrt_mul (hp k), Real.sqrt_sq (norm_nonneg _), ← mul_assoc,
      Real.mul_self_sqrt (hp k)]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)] at hcs
  rw [eig_sum hn hρ hρ1, Real.sqrt_one, one_mul, sum_eig_norm_sq hn hρ hPs hPP] at hcs
  exact hcs

/-- **Proposition 3.2.** For a density operator `ρ` and a symmetric idempotent `P` with
`q = re Tr((1 − P) ρ) < 1`, the truncated state `σ = (1 − q)⁻¹ P ρ P` has
`‖ρ − σ‖₁ ≤ 2√q + q`. DERIVED: `2` the two off-diagonal blocks. -/
theorem truncation_le {P : E →ₗ[𝕜] E} (hρ1 : trace 𝕜 E ρ = 1) (hPs : P.IsSymmetric)
    (hPP : P * P = P) (hq : re (trace 𝕜 E ((1 - P) * ρ)) < 1) :
    tnorm hn (trunc_sym hρ.isSymmetric hPs) ≤
      2 * √(re (trace 𝕜 E ((1 - P) * ρ))) + re (trace 𝕜 E ((1 - P) * ρ)) := by
  set q := re (trace 𝕜 E ((1 - P) * ρ)) with hqdef
  have hD := trunc_sym hρ.isSymmetric hPs
  set S := sgnOp hn hD
  set e := hρ.isSymmetric.eigenvectorBasis hn
  set p := hρ.isSymmetric.eigenvalues hn
  have hp := eig_nonneg hn hρ
  have hQs := compl_sym hPs
  have hQQ := compl_idem hPP
  have he1 : ∀ k, ‖e k‖ = 1 := fun k => e.orthonormal.1 k
  -- q ≥ 0 and re Tr(P ρ) = 1 − q
  have hq0 : 0 ≤ q := by
    rw [hqdef, ← sum_eig_norm_sq hn hρ hQs hQQ]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hp k) (sq_nonneg _)
  have hPq : re (trace 𝕜 E (P * ρ)) = 1 - q := by
    have : trace 𝕜 E (P * ρ) = trace 𝕜 E ρ - trace 𝕜 E ((1 - P) * ρ) := by
      rw [sub_mul, one_mul, map_sub]; ring
    rw [this, map_sub, hρ1, one_re]
  -- the three traces, read on the eigenbasis of `ρ`
  have hsplit : ρ * S = (1 - P) * (ρ * S) + P * (ρ * ((1 - P) * S)) + P * (ρ * (P * S)) := by
    noncomm_ring
  have hT1 : ‖trace 𝕜 E ((1 - P) * (ρ * S))‖ ≤ √q := by
    rw [LinearMap.trace_mul_comm (R := 𝕜), mul_assoc]
    refine (norm_trace_mul_le hn hρ _ (fun k => ‖(1 - P) (e k)‖) fun k => ?_).trans
      (sum_eig_norm_le hn hρ hρ1 hQs hQQ)
    rw [Module.End.mul_apply]
    exact (norm_inner_sgnOp_le hn hD _ _).trans (by rw [he1, one_mul])
  have hT2 : ‖trace 𝕜 E (P * (ρ * ((1 - P) * S)))‖ ≤ √q := by
    rw [LinearMap.trace_mul_comm (R := 𝕜), mul_assoc, mul_assoc]
    refine (norm_trace_mul_le hn hρ _ (fun k => ‖(1 - P) (e k)‖) fun k => ?_).trans
      (sum_eig_norm_le hn hρ hρ1 hQs hQQ)
    rw [Module.End.mul_apply, Module.End.mul_apply, ← hQs]
    refine (norm_inner_sgnOp_le hn hD _ _).trans ?_
    exact mul_le_of_le_one_right (norm_nonneg _)
      ((norm_proj_le hPs hPP (e k)).trans (he1 k).le)
  have hT3 : ‖trace 𝕜 E (P * (ρ * (P * S)))‖ ≤ 1 - q := by
    rw [LinearMap.trace_mul_comm (R := 𝕜), mul_assoc, mul_assoc]
    refine (norm_trace_mul_le hn hρ _ (fun k => ‖P (e k)‖ ^ 2) fun k => ?_).trans
      (sum_eig_norm_sq hn hρ hPs hPP ▸ hPq ▸ le_rfl)
    rw [Module.End.mul_apply, Module.End.mul_apply, ← hPs, sq]
    exact norm_inner_sgnOp_le hn hD _ _
  -- assemble
  have hc1 : 1 ≤ (1 - q)⁻¹ := one_le_inv₀ (by linarith) |>.mpr (by linarith)
  have hre : tnorm hn hD = re (trace 𝕜 E ((1 - P) * (ρ * S))) +
      re (trace 𝕜 E (P * (ρ * ((1 - P) * S)))) +
      (1 - (1 - q)⁻¹) * re (trace 𝕜 E (P * (ρ * (P * S)))) := by
    rw [← re_trace_mul_sgnOp hn hD]
    have : (ρ - trunc ρ P) * S = ρ * S - (((1 - q)⁻¹ : ℝ) : 𝕜) • (P * (ρ * (P * S))) := by
      unfold trunc
      rw [← hqdef]
      simp only [sub_mul, smul_mul_assoc, mul_assoc]
    have htrS : trace 𝕜 E (ρ * S) = trace 𝕜 E ((1 - P) * (ρ * S)) +
        trace 𝕜 E (P * (ρ * ((1 - P) * S))) + trace 𝕜 E (P * (ρ * (P * S))) := by
      conv_lhs => rw [hsplit]
      rw [map_add, map_add]
    rw [this, map_sub, map_smul, smul_eq_mul, map_sub, re_ofReal_mul, htrS, map_add, map_add]
    ring
  have hA := (abs_re_le_norm (trace 𝕜 E ((1 - P) * (ρ * S)))).trans hT1
  have hB := (abs_re_le_norm (trace 𝕜 E (P * (ρ * ((1 - P) * S))))).trans hT2
  have hC := (abs_re_le_norm (trace 𝕜 E (P * (ρ * (P * S))))).trans hT3
  have h1q : (1:ℝ) - q ≠ 0 := (by linarith : (0:ℝ) < 1 - q).ne'
  have hqq : ((1 - q)⁻¹ - 1) * (1 - q) = q := by
    rw [sub_mul, inv_mul_cancel₀ h1q, one_mul]; ring
  have hCabs := abs_le.mp hC
  have hAabs := abs_le.mp hA
  have hBabs := abs_le.mp hB
  rw [show tnorm hn (trunc_sym hρ.isSymmetric hPs) = tnorm hn hD from rfl, hre]
  nlinarith [mul_le_mul_of_nonneg_left hCabs.1 (by linarith : (0:ℝ) ≤ (1 - q)⁻¹ - 1)]

end Truncation

end MassGap.PurityStability

#print axioms MassGap.PurityStability.re_trace_mul_eq
#print axioms MassGap.PurityStability.abs_re_trace_mul_le
#print axioms MassGap.PurityStability.diag_mem
#print axioms MassGap.PurityStability.purity_diff_le
#print axioms MassGap.PurityStability.trace_mul_eq_sum
#print axioms MassGap.PurityStability.sgnOp_apply
#print axioms MassGap.PurityStability.sgnOp_basis
#print axioms MassGap.PurityStability.abs_sgn
#print axioms MassGap.PurityStability.norm_inner_sgnOp_le
#print axioms MassGap.PurityStability.re_trace_mul_sgnOp
#print axioms MassGap.PurityStability.norm_sq_proj
#print axioms MassGap.PurityStability.norm_proj_le
#print axioms MassGap.PurityStability.compl_sym
#print axioms MassGap.PurityStability.compl_idem
#print axioms MassGap.PurityStability.trunc_sym
#print axioms MassGap.PurityStability.eig_re
#print axioms MassGap.PurityStability.eig_nonneg
#print axioms MassGap.PurityStability.eig_sum
#print axioms MassGap.PurityStability.norm_trace_mul_le
#print axioms MassGap.PurityStability.sum_eig_norm_sq
#print axioms MassGap.PurityStability.sum_eig_norm_le
#print axioms MassGap.PurityStability.truncation_le
