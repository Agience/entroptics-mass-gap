import MassGap.PurityStability

/-!
# MassGap.PurityKyFan — the variational bound of Theorem D.1, on finite-dimensional spaces

The variational bound in the proof of Theorem D.1 of D. Bhattacharjee, U. Bhattacharya,
J. M. Lockwood, T. Romanov, I. J. Sessford and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills
Theory at Weak Coupling* (research draft, 15 November 2026, <https://github.com/anaxia-research/4Y-M>,
commit 8e01510, `Paper-2/Paper-2.pdf`), on a finite-dimensional inner product space.

`K ≥ 0` has eigenvalues `λ₀ ≥ λ₁ ≥ …` (Mathlib's `eigenvalues`, antitone) and `P` is an orthogonal
projection (`P` symmetric, `P P = P`) with `re Tr P ≤ m`.

* `sum_mul_le_head`: weights `0 ≤ w_i ≤ 1` with `Σ w_i ≤ |h|`, and values with `α_i ≥ c ≥ 0` on `h`
  and `α_i ≤ c` off `h`, give `Σ α_i w_i ≤ Σ_{i ∈ h} α_i`.
* `diag_proj_mem`: `0 ≤ re⟪x, P x⟫ ≤ 1` for a unit vector `x`.
* `re_trace_sq_mul_eq`: `re Tr(K K P) = Σ_i λ_i² re⟪e_i, P e_i⟫` in an eigenbasis `e` of `K`.
* `variational_le`: `re Tr(P K²) ≤ Σ_{i < m} λ_i²`.
-/

namespace MassGap.PurityKyFan

open LinearMap RCLike
open scoped InnerProductSpace

/-- The threshold step: `Σ α_i w_i ≤ Σ_{i ∈ h} α_i` for weights `0 ≤ w_i ≤ 1` with `Σ w_i ≤ |h|`,
when `α_i ≥ c ≥ 0` on `h` and `α_i ≤ c` off `h`. -/
theorem sum_mul_le_head {ι : Type*} [Fintype ι] [DecidableEq ι] (h : Finset ι) (α w : ι → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hin : ∀ i ∈ h, c ≤ α i) (hout : ∀ i ∉ h, α i ≤ c)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) (hw : ∑ i, w i ≤ h.card) :
    ∑ i, α i * w i ≤ ∑ i ∈ h, α i := by
  have h1 : ∑ i ∈ h, α i * w i ≤ ∑ i ∈ h, (α i + (c * w i - c)) :=
    Finset.sum_le_sum fun i hi => by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (hin i hi)) (sub_nonpos.2 (hw1 i))]
  have h2 : ∑ i ∈ hᶜ, α i * w i ≤ ∑ i ∈ hᶜ, c * w i :=
    Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_right (hout i (Finset.mem_compl.1 hi)) (hw0 i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul] at h1 h2
  have hs := Finset.sum_add_sum_compl h fun i => α i * w i
  have hcw := mul_le_mul_of_nonneg_left hw hc
  rw [← Finset.sum_add_sum_compl h w, mul_add] at hcw
  linarith

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable [FiniteDimensional 𝕜 E] {n : ℕ} (hn : Module.finrank 𝕜 E = n)

omit [FiniteDimensional 𝕜 E] in
/-- The diagonal of an orthogonal projection at a unit vector lies in `[0, 1]`:
`re⟪x, P x⟫ = ‖P x‖²` and `‖P x‖ ≤ ‖x‖` (`PurityStability.norm_sq_proj`, `norm_proj_le`). -/
theorem diag_proj_mem {P : E →ₗ[𝕜] E} (hP : P.IsSymmetric) (hPP : P * P = P) {x : E}
    (hx : ‖x‖ = 1) : 0 ≤ re ⟪x, P x⟫_𝕜 ∧ re ⟪x, P x⟫_𝕜 ≤ 1 := by
  rw [← PurityStability.norm_sq_proj hP hPP x]
  have h := PurityStability.norm_proj_le hP hPP x
  rw [hx] at h
  exact ⟨sq_nonneg _, by nlinarith [norm_nonneg (P x)]⟩

/-- `re Tr(K K P) = Σ_i λ_i² re⟪e_i, P e_i⟫` in the eigenbasis `e` of a symmetric `K`. -/
theorem re_trace_sq_mul_eq {K : E →ₗ[𝕜] E} (hK : K.IsSymmetric) (P : E →ₗ[𝕜] E) :
    re (trace 𝕜 E (K * (K * P))) = ∑ i, hK.eigenvalues hn i ^ 2 *
      re ⟪hK.eigenvectorBasis hn i, P (hK.eigenvectorBasis hn i)⟫_𝕜 := by
  rw [PurityStability.re_trace_mul_eq hn hK]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.End.mul_apply, ← hK, hK.apply_eigenvectorBasis, inner_smul_left, conj_ofReal,
    re_ofReal_mul]
  ring

/-- The variational bound: for `K ≥ 0` and an orthogonal projection `P` with `re Tr P ≤ m`,
`re Tr(P K²) ≤ Σ_{i < m} λ_i²`. -/
theorem variational_le {K P : E →ₗ[𝕜] E} (hK : K.IsPositive) (hP : P.IsSymmetric)
    (hPP : P * P = P) {m : ℕ} (hm : re (trace 𝕜 E P) ≤ m) :
    re (trace 𝕜 E (P * (K * K))) ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m),
        hK.isSymmetric.eigenvalues hn i ^ 2 := by
  rw [LinearMap.trace_mul_comm, mul_assoc, re_trace_sq_mul_eq hn hK.isSymmetric P]
  set b := hK.isSymmetric.eigenvectorBasis hn
  set lam := hK.isSymmetric.eigenvalues hn
  have hw : ∀ i, 0 ≤ re ⟪b i, P (b i)⟫_𝕜 ∧ re ⟪b i, P (b i)⟫_𝕜 ≤ 1 := fun i =>
    diag_proj_mem hP hPP (b.orthonormal.1 i)
  have hsum : ∑ i, re ⟪b i, P (b i)⟫_𝕜 = re (trace 𝕜 E P) := by
    rw [trace_eq_sum_inner P b, map_sum]
  have hl0 : ∀ i, 0 ≤ lam i := hK.nonneg_eigenvalues hn
  have hanti : Antitone lam := hK.isSymmetric.eigenvalues_antitone hn
  have hcard : ∑ i, re ⟪b i, P (b i)⟫_𝕜 ≤
      ((Finset.univ.filter (fun i : Fin n => (i : ℕ) < m)).card : ℝ) := by
    rw [Fin.card_filter_val_lt, Nat.cast_min]
    refine le_min ?_ (hsum.trans_le hm)
    calc ∑ i, re ⟪b i, P (b i)⟫_𝕜 ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hw i).2
      _ = n := by simp
  by_cases hmn : m < n
  · refine sum_mul_le_head _ (fun i => lam i ^ 2) (fun i => re ⟪b i, P (b i)⟫_𝕜)
      (c := lam ⟨m, hmn⟩ ^ 2) (sq_nonneg _) ?_ ?_ (fun i => (hw i).1) (fun i => (hw i).2) hcard
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact pow_le_pow_left₀ (hl0 _) (hanti (Fin.le_iff_val_le_val.2 hi.le)) 2
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
      exact pow_le_pow_left₀ (hl0 _) (hanti (Fin.le_iff_val_le_val.2 hi)) 2
  · refine sum_mul_le_head _ (fun i => lam i ^ 2) (fun i => re ⟪b i, P (b i)⟫_𝕜)
      (c := 0) le_rfl (fun i _ => sq_nonneg _) ?_ (fun i => (hw i).1) (fun i => (hw i).2) hcard
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
    have := i.isLt
    omega

end MassGap.PurityKyFan

#print axioms MassGap.PurityKyFan.sum_mul_le_head
#print axioms MassGap.PurityKyFan.diag_proj_mem
#print axioms MassGap.PurityKyFan.re_trace_sq_mul_eq
#print axioms MassGap.PurityKyFan.variational_le
