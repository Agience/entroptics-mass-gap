import MassGap.PuritySpectralTrace

/-!
# MassGap.PurityWeyl — Weyl's inequality for sorted eigenvalues, on finite-dimensional spaces

The min–max step `λ_j ≤ μ_j + ε` in the proof of Theorem D.1 of D. Bhattacharjee,
U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford and S. Singha Roy, *Thermal Purity
Bounds for Yang–Mills Theory at Weak Coupling* (research draft, 15 November 2026,
<https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`), on a
finite-dimensional inner product space. `K` and `B` are symmetric with eigenvalues `λ_j`, `μ_j`
sorted in decreasing order (Mathlib's `eigenvalues`, `eigenvalues_antitone`) and eigenbases
`e_i`, `f_i`.

* `re_inner_eq_sum`: `re ⟪K x, x⟫ = Σ_i λ_i ‖⟪e_i, x⟫‖²`, the case `T = 1` of
  `PuritySpectralTrace.re_inner_pow_eq`.
* `head_le`: if `⟪e_i, x⟫ = 0` for `i > j`, then `λ_j ‖x‖² ≤ re ⟪K x, x⟫`.
* `le_tail`: if `⟪f_i, x⟫ = 0` for `i < j`, then `re ⟪B x, x⟫ ≤ μ_j ‖x‖²`.
* `inner_eq_zero_of_mem_span`: a vector in the span of `b_k`, `k ∈ s`, is orthogonal to `b_i`
  for `i ∉ s`.
* `exists_ne_zero_inter_map`: for orthonormal bases `b`, `c`, a linear map `D` and an index `j`
  there is `x ≠ 0` with `⟪b_i, x⟫ = 0` for `i > j` and `⟪c_i, D x⟫ = 0` for `i < j` (the `j`
  functionals `⟪c_i, D ·⟫` have a common zero on the `(j + 1)`-dimensional span of `b_0, …, b_j`).
  `exists_ne_zero_inter` is the case `D = id`.
* `eigenvalues_le_mul_add`: `re ⟪K x, x⟫ ≤ c re ⟪B x, x⟫ + ε ‖x‖²` for all `x` and `c ≥ 0` give
  `λ_j ≤ c μ_j + ε`; `eigenvalues_le_add` is the case `c = 1`.
* `form_le_of_norm_sub_le`: `‖(K − B) x‖ ≤ ε ‖x‖` for all `x` gives the form bound.
* `abs_eigenvalues_sub_le`: `‖(K − B) x‖ ≤ ε ‖x‖` for all `x` gives `|λ_j − μ_j| ≤ ε`.
-/

namespace MassGap.PurityWeyl

open LinearMap RCLike Module
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} (hn : Module.finrank 𝕜 E = n)

/-- The quadratic form in the eigenbasis: `re ⟪K x, x⟫ = Σ_i λ_i ‖⟪e_i, x⟫‖²`. -/
theorem re_inner_eq_sum {K : E →ₗ[𝕜] E} (hK : K.IsSymmetric) (x : E) :
    re ⟪K x, x⟫_𝕜 = ∑ i, hK.eigenvalues hn i * ‖⟪hK.eigenvectorBasis hn i, x⟫_𝕜‖ ^ 2 := by
  simpa only [pow_one] using PuritySpectralTrace.re_inner_pow_eq hn hK x 1

/-- The head bound: if `⟪e_i, x⟫ = 0` for `i > j`, then `λ_j ‖x‖² ≤ re ⟪K x, x⟫`. -/
theorem head_le {K : E →ₗ[𝕜] E} (hK : K.IsSymmetric) (j : Fin n) {x : E}
    (hx : ∀ i, j < i → ⟪hK.eigenvectorBasis hn i, x⟫_𝕜 = 0) :
    hK.eigenvalues hn j * ‖x‖ ^ 2 ≤ re ⟪K x, x⟫_𝕜 := by
  rw [re_inner_eq_sum hn hK, ← (hK.eigenvectorBasis hn).sum_sq_norm_inner_right x, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases le_or_gt i j with h | h
  · exact mul_le_mul_of_nonneg_right (hK.eigenvalues_antitone hn h) (sq_nonneg _)
  · simp [hx i h]

/-- The tail bound: if `⟪f_i, x⟫ = 0` for `i < j`, then `re ⟪B x, x⟫ ≤ μ_j ‖x‖²`. -/
theorem le_tail {B : E →ₗ[𝕜] E} (hB : B.IsSymmetric) (j : Fin n) {x : E}
    (hx : ∀ i, i < j → ⟪hB.eigenvectorBasis hn i, x⟫_𝕜 = 0) :
    re ⟪B x, x⟫_𝕜 ≤ hB.eigenvalues hn j * ‖x‖ ^ 2 := by
  rw [re_inner_eq_sum hn hB, ← (hB.eigenvectorBasis hn).sum_sq_norm_inner_right x, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases le_or_gt j i with h | h
  · exact mul_le_mul_of_nonneg_right (hB.eigenvalues_antitone hn h) (sq_nonneg _)
  · simp [hx i h]

omit [FiniteDimensional 𝕜 E] in
/-- A vector in the span of `b_k`, `k ∈ s`, is orthogonal to `b_i` for `i ∉ s`. -/
theorem inner_eq_zero_of_mem_span {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E)
    (s : Finset ι) {i : ι} (hi : i ∉ s) {y : E}
    (hy : y ∈ Submodule.span 𝕜 (Set.range fun k : s => b k)) : ⟪b i, y⟫_𝕜 = 0 := by
  have hle : Submodule.span 𝕜 (Set.range fun k : s => b k) ≤ LinearMap.ker (innerₛₗ 𝕜 (b i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, innerₛₗ_apply_apply]
    exact b.orthonormal.2 fun h => hi (by rw [h]; exact k.2)
  simpa using hle hy

/-- The dimension count through a linear map: for orthonormal bases `b`, `c`, a linear map `D` and
`j`, there is `x ≠ 0` with `⟪b_i, x⟫ = 0` for `i > j` and `⟪c_i, D x⟫ = 0` for `i < j`. -/
theorem exists_ne_zero_inter_map (b c : OrthonormalBasis (Fin n) 𝕜 E) (D : E →ₗ[𝕜] E) (j : Fin n) :
    ∃ x : E, x ≠ 0 ∧ (∀ i, j < i → ⟪b i, x⟫_𝕜 = 0) ∧ (∀ i, i < j → ⟪c i, D x⟫_𝕜 = 0) := by
  set V := Submodule.span 𝕜 (Set.range fun k : (Finset.Iic j) => b k)
  have hV : finrank 𝕜 V = j + 1 := by
    rw [show V = Submodule.span 𝕜 (Set.range ((⇑b) ∘ (Subtype.val : Finset.Iic j → Fin n)))
      from rfl, finrank_span_eq_card (b.orthonormal.linearIndependent.comp _ Subtype.val_injective),
      Fintype.card_coe, Fin.card_Iic]
  let f : V →ₗ[𝕜] (Fin j → 𝕜) :=
    (LinearMap.pi fun i : Fin j => innerₛₗ 𝕜 (c ⟨i, i.2.trans j.2⟩) ∘ₗ D) ∘ₗ V.subtype
  have hf : LinearMap.ker f ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by rw [Module.finrank_fin_fun, hV]; omega)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hf
  refine ⟨v, fun h => hv0 (Subtype.ext h), fun i hi => ?_, fun i hi => ?_⟩
  · exact inner_eq_zero_of_mem_span b _ (by simpa using hi) v.2
  · have := congrFun (LinearMap.mem_ker.1 hv) ⟨i, hi⟩
    simpa [f] using this

/-- The dimension count: for orthonormal bases `b`, `c` of an `n`-dimensional space and `j`, there
is `x ≠ 0` with `⟪b_i, x⟫ = 0` for `i > j` and `⟪c_i, x⟫ = 0` for `i < j`. -/
theorem exists_ne_zero_inter (b c : OrthonormalBasis (Fin n) 𝕜 E) (j : Fin n) :
    ∃ x : E, x ≠ 0 ∧ (∀ i, j < i → ⟪b i, x⟫_𝕜 = 0) ∧ (∀ i, i < j → ⟪c i, x⟫_𝕜 = 0) := by
  simpa using exists_ne_zero_inter_map b c LinearMap.id j

/-- Weyl's inequality with a factor: `re ⟪K x, x⟫ ≤ c re ⟪B x, x⟫ + ε ‖x‖²` for all `x` and `c ≥ 0`
give `λ_j ≤ c μ_j + ε`. -/
theorem eigenvalues_le_mul_add {K B : E →ₗ[𝕜] E} (hK : K.IsSymmetric) (hB : B.IsSymmetric)
    {c ε : ℝ} (hc : 0 ≤ c) (h : ∀ x, re ⟪K x, x⟫_𝕜 ≤ c * re ⟪B x, x⟫_𝕜 + ε * ‖x‖ ^ 2)
    (j : Fin n) : hK.eigenvalues hn j ≤ c * hB.eigenvalues hn j + ε := by
  obtain ⟨x, hx0, h1, h2⟩ :=
    exists_ne_zero_inter (hK.eigenvectorBasis hn) (hB.eigenvectorBasis hn) j
  have hpos : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.2 hx0) 2
  have hle : hK.eigenvalues hn j * ‖x‖ ^ 2 ≤ (c * hB.eigenvalues hn j + ε) * ‖x‖ ^ 2 := by
    nlinarith [head_le hn hK j h1, h x, mul_le_mul_of_nonneg_left (le_tail hn hB j h2) hc]
  exact le_of_mul_le_mul_right hle hpos

/-- Weyl's inequality: `re ⟪K x, x⟫ ≤ re ⟪B x, x⟫ + ε ‖x‖²` for all `x` gives `λ_j ≤ μ_j + ε`. -/
theorem eigenvalues_le_add {K B : E →ₗ[𝕜] E} (hK : K.IsSymmetric) (hB : B.IsSymmetric) {ε : ℝ}
    (h : ∀ x, re ⟪K x, x⟫_𝕜 ≤ re ⟪B x, x⟫_𝕜 + ε * ‖x‖ ^ 2) (j : Fin n) :
    hK.eigenvalues hn j ≤ hB.eigenvalues hn j + ε := by
  simpa using eigenvalues_le_mul_add hn hK hB zero_le_one (by simpa using h) j

omit [FiniteDimensional 𝕜 E] in
/-- The operator bound gives the form bound: `‖(K − B) x‖ ≤ ε ‖x‖` for all `x` gives
`re ⟪K x, x⟫ ≤ re ⟪B x, x⟫ + ε ‖x‖²`. -/
theorem form_le_of_norm_sub_le {K B : E →ₗ[𝕜] E} {ε : ℝ} (h : ∀ x, ‖(K - B) x‖ ≤ ε * ‖x‖)
    (x : E) : re ⟪K x, x⟫_𝕜 ≤ re ⟪B x, x⟫_𝕜 + ε * ‖x‖ ^ 2 := by
  have h1 : re ⟪K x, x⟫_𝕜 - re ⟪B x, x⟫_𝕜 = re ⟪(K - B) x, x⟫_𝕜 := by
    simp [inner_sub_left]
  have h2 := (re_le_norm ⟪(K - B) x, x⟫_𝕜).trans (norm_inner_le_norm _ _)
  have h3 := mul_le_mul_of_nonneg_right (h x) (norm_nonneg x)
  nlinarith

/-- Two-sided Weyl: `‖(K − B) x‖ ≤ ε ‖x‖` for all `x` gives `|λ_j − μ_j| ≤ ε`. -/
theorem abs_eigenvalues_sub_le {K B : E →ₗ[𝕜] E} (hK : K.IsSymmetric) (hB : B.IsSymmetric)
    {ε : ℝ} (h : ∀ x, ‖(K - B) x‖ ≤ ε * ‖x‖) (j : Fin n) :
    |hK.eigenvalues hn j - hB.eigenvalues hn j| ≤ ε := by
  have h' : ∀ x, ‖(B - K) x‖ ≤ ε * ‖x‖ := fun x => by
    rw [← norm_neg, ← LinearMap.neg_apply, neg_sub]
    exact h x
  have a := eigenvalues_le_add hn hK hB (form_le_of_norm_sub_le h) j
  have b := eigenvalues_le_add hn hB hK (form_le_of_norm_sub_le h') j
  rw [abs_le]
  constructor <;> linarith

end MassGap.PurityWeyl

#print axioms MassGap.PurityWeyl.re_inner_eq_sum
#print axioms MassGap.PurityWeyl.head_le
#print axioms MassGap.PurityWeyl.le_tail
#print axioms MassGap.PurityWeyl.inner_eq_zero_of_mem_span
#print axioms MassGap.PurityWeyl.exists_ne_zero_inter_map
#print axioms MassGap.PurityWeyl.exists_ne_zero_inter
#print axioms MassGap.PurityWeyl.eigenvalues_le_mul_add
#print axioms MassGap.PurityWeyl.eigenvalues_le_add
#print axioms MassGap.PurityWeyl.form_le_of_norm_sub_le
#print axioms MassGap.PurityWeyl.abs_eigenvalues_sub_le
