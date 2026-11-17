import MassGap.PurityTrace

/-!
# MassGap.PurityFiniteRank — the scalar content of Theorem D.1 of the purity paper

Theorem D.1 (finite-rank thermal certificate) of D. Bhattacharjee, U. Bhattacharya,
J. M. Lockwood, T. Romanov, I. J. Sessford and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills
Theory at Weak Coupling* (research draft, 15 November 2026, <https://github.com/anaxia-research/4Y-M>,
commit 8e01510, `Paper-2/Paper-2.pdf`).

`K ≥ 0` has eigenvalues `λ_j`, the rank-`m` approximant `B ≥ 0` has eigenvalues `μ_j`,
`‖K − B‖_HS ≤ ε` and `δ = μ₀ − ε > 0`. The proof's operator inputs enter as hypotheses: from
min–max, `λ₀ ≥ δ` and `0 ≤ λ_j ≤ μ_j + ε` for `1 ≤ j < m`; from the variational bound,
`Σ_{j ≥ m} λ_j² ≤ ε²`, which also gives `λ_j ≤ ε` for `j ≥ m`. The tail is taken over a finite set (`excited_le`) or as
a `tsum` over an arbitrary index type (`excited_tsum_le`).

* `mul_sq_le_pow`, `le_of_sq_le`: `S ≤ ε²` gives `ε^(T−2) S ≤ ε^T`; `0 ≤ x`, `x² ≤ ε²` give `x ≤ ε`.
* `tail_pow_le`: `0 ≤ ρ_k`, `Σ ρ_k² ≤ ε²`, `T ≥ 2` give `Σ ρ_k^T ≤ ε^T`.
* `head_le`: `Σ_{1 ≤ j < m} (λ_j/λ₀)^T ≤ Σ_{1 ≤ j < m} ((μ_j + ε)/δ)^T`; `div_pow_le`:
  `X ≤ ε^T` gives `X / λ₀^T ≤ (ε/δ)^T`.
* `excited_le`: (D.1) for `T ≥ 2`, with `s` indexing `1 ≤ j < m`,
  `Σ_{1 ≤ j < m} (λ_j/λ₀)^T + Σ_{k} (ρ_k/λ₀)^T ≤ Σ_{1 ≤ j < m} ((μ_j + ε)/δ)^T + (ε/δ)^T = d_T`.
* `tail_tsum_le`: `Σ' ρ_k² ≤ ε²` gives summability of `ρ_k^T` and `Σ' ρ_k^T ≤ ε^T`; `excited_tsum_le`: (D.1) with the tail as a `tsum`.
* `pressure_le`: with `0 < Tr R^T ≤ 1 + d_T` and `Tr R^{2T} ≥ 1`, `ψ_T ≤ 2 log(1 + d_T)`.
* `ratio_lt_one`, `ratio_le_root`: if the excited sum is at most `d_T < 1`, every excited ratio is
  `< 1`, and each is at most `d_T^{1/T}`.

Not formalized here: the operator facts behind the hypotheses (the operator norm is at most the
Hilbert–Schmidt norm, the min–max principle, `(I − P)B = 0` giving
`‖(I − P)K‖_HS = ‖(I − P)(K − B)‖_HS ≤ ε`, the variational bound `Tr(P K²) ≤ Σ_{j<m} λ_j²` and
`Tr K² = Σ_j λ_j²`); the spectral expansion `Tr R^T = 1 + Σ_{j ≥ 1} (λ_j/λ₀)^T` and from it
`Tr R^T > 0`, `Tr R^{2T} ≥ 1`; simplicity of the top eigenvalue from the excited ratios being `< 1`.
The matrix certificate (D.2) for `B = P_m K P_m`, the tail identity
`‖(I − P)K‖²_HS = Tr K² − Tr(P K²)` and the window test (D.3) are `MassGap.PurityTailIdentity`;
the variational bound in finite dimension is `MassGap.PurityKyFan`, and the spectral expansion and
`Tr K² = Σ_j λ_j²` in finite dimension are `MassGap.PuritySpectralTrace`, and the min–max step
`λ_j ≤ μ_j + ε` in finite dimension is `MassGap.PurityWeyl`.
-/

namespace MassGap.PurityFiniteRank

open Real

/-- `S ≤ ε²` and `T ≥ 2` give `ε^(T−2) S ≤ ε^T`. -/
theorem mul_sq_le_pow {S ε : ℝ} (hε : 0 ≤ ε) (hS : S ≤ ε ^ 2) {T : ℕ} (hT : 2 ≤ T) :
    ε ^ (T - 2) * S ≤ ε ^ T :=
  (mul_le_mul_of_nonneg_left hS (pow_nonneg hε _)).trans_eq
    (by rw [← pow_add, Nat.sub_add_cancel hT])

/-- A term with `0 ≤ x` and `x² ≤ ε²`, `0 ≤ ε`, is at most `ε`. -/
theorem le_of_sq_le {x ε : ℝ} (h0 : 0 ≤ x) (hε : 0 ≤ ε) (h : x ^ 2 ≤ ε ^ 2) : x ≤ ε :=
  (pow_le_pow_iff_left₀ h0 hε two_ne_zero).1 h

/-- The tail step over a finite set: `0 ≤ ρ_k`, `Σ ρ_k² ≤ ε²`, `T ≥ 2` give `Σ ρ_k^T ≤ ε^T`. -/
theorem tail_pow_le {κ : Type*} (t : Finset κ) (ρ : κ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hρ0 : ∀ k ∈ t, 0 ≤ ρ k) (hsq : ∑ k ∈ t, ρ k ^ 2 ≤ ε ^ 2)
    {T : ℕ} (hT : 2 ≤ T) : ∑ k ∈ t, ρ k ^ T ≤ ε ^ T := by
  have hρε : ∀ k ∈ t, ρ k ≤ ε := fun k hk => le_of_sq_le (hρ0 k hk) hε
    ((Finset.single_le_sum (fun j _ => sq_nonneg (ρ j)) hk).trans hsq)
  exact (PurityTrace.tail_le t ρ hρ0 hρε hT).trans (mul_sq_le_pow hε hsq hT)

/-- The head step: `0 ≤ λ_j ≤ μ_j + ε` and `0 < δ ≤ λ₀` give
`Σ_{1 ≤ j < m} (λ_j/λ₀)^T ≤ Σ_{1 ≤ j < m} ((μ_j + ε)/δ)^T`. -/
theorem head_le {ι : Type*} (s : Finset ι) (lam mu : ι → ℝ) {lam0 δ ε : ℝ} (hδ : 0 < δ)
    (h0 : δ ≤ lam0) (hl0 : ∀ j ∈ s, 0 ≤ lam j) (hlμ : ∀ j ∈ s, lam j ≤ mu j + ε) (T : ℕ) :
    ∑ j ∈ s, (lam j / lam0) ^ T ≤ ∑ j ∈ s, ((mu j + ε) / δ) ^ T := by
  have hl : 0 < lam0 := hδ.trans_le h0
  apply Finset.sum_le_sum
  intro j hj
  apply pow_le_pow_left₀ (div_nonneg (hl0 j hj) hl.le)
  calc lam j / lam0 ≤ lam j / δ := div_le_div_of_nonneg_left (hl0 j hj) hδ h0
    _ ≤ (mu j + ε) / δ := div_le_div_of_nonneg_right (hlμ j hj) hδ.le

/-- The tail normalization: `X ≤ ε^T` and `0 < δ ≤ λ₀` give `X / λ₀^T ≤ (ε/δ)^T`. -/
theorem div_pow_le {X lam0 δ ε : ℝ} (hδ : 0 < δ) (h0 : δ ≤ lam0) (hε : 0 ≤ ε) {T : ℕ}
    (hX : X ≤ ε ^ T) : X / lam0 ^ T ≤ (ε / δ) ^ T := by
  have hl : 0 < lam0 := hδ.trans_le h0
  rw [div_pow]
  calc X / lam0 ^ T ≤ ε ^ T / lam0 ^ T := div_le_div_of_nonneg_right hX (pow_nonneg hl.le _)
    _ ≤ ε ^ T / δ ^ T :=
        div_le_div_of_nonneg_left (pow_nonneg hε _) (pow_pos hδ _) (pow_le_pow_left₀ hδ.le h0 _)

/-- (D.1): the excited trace is at most
`d_T = Σ_{1 ≤ j < m} ((μ_j + ε)/δ)^T + (ε/δ)^T`. -/
theorem excited_le {ι κ : Type*} (s : Finset ι) (t : Finset κ) (lam mu : ι → ℝ) (ρ : κ → ℝ)
    {lam0 δ ε : ℝ} (hδ : 0 < δ) (h0 : δ ≤ lam0) (hε : 0 ≤ ε)
    (hl0 : ∀ j ∈ s, 0 ≤ lam j) (hlμ : ∀ j ∈ s, lam j ≤ mu j + ε)
    (hρ0 : ∀ k ∈ t, 0 ≤ ρ k) (hsq : ∑ k ∈ t, ρ k ^ 2 ≤ ε ^ 2) {T : ℕ} (hT : 2 ≤ T) :
    ∑ j ∈ s, (lam j / lam0) ^ T + ∑ k ∈ t, (ρ k / lam0) ^ T ≤
      ∑ j ∈ s, ((mu j + ε) / δ) ^ T + (ε / δ) ^ T := by
  have htail : ∑ k ∈ t, (ρ k / lam0) ^ T ≤ (ε / δ) ^ T := by
    simp_rw [div_pow]
    rw [← Finset.sum_div]
    exact (div_pow_le hδ h0 hε (tail_pow_le t ρ hε hρ0 hsq hT)).trans_eq (div_pow ε δ T)
  linarith [head_le s lam mu hδ h0 hl0 hlμ T]

/-- The tail as a `tsum`: `0 ≤ ρ_k`, `Σ' ρ_k² ≤ ε²` (summable), `T ≥ 2` give that `ρ_k^T` is
summable and `Σ' ρ_k^T ≤ ε^T`. -/
theorem tail_tsum_le {κ : Type*} (ρ : κ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hρ0 : ∀ k, 0 ≤ ρ k) (hs : Summable fun k => ρ k ^ 2)
    (hsq : ∑' k, ρ k ^ 2 ≤ ε ^ 2) {T : ℕ} (hT : 2 ≤ T) :
    Summable (fun k => ρ k ^ T) ∧ ∑' k, ρ k ^ T ≤ ε ^ T := by
  have hb : ∀ k, ρ k ^ T ≤ ε ^ (T - 2) * ρ k ^ 2 := fun k =>
    PurityTrace.pow_le_sq_mul (hρ0 k)
      (le_of_sq_le (hρ0 k) hε ((hs.le_tsum k fun j _ => sq_nonneg (ρ j)).trans hsq)) hT
  have hs' := hs.mul_left (ε ^ (T - 2))
  have hT' : Summable fun k => ρ k ^ T :=
    Summable.of_nonneg_of_le (fun k => pow_nonneg (hρ0 k) T) hb hs'
  refine ⟨hT', ?_⟩
  calc ∑' k, ρ k ^ T ≤ ∑' k, ε ^ (T - 2) * ρ k ^ 2 := hT'.tsum_le_tsum hb hs'
    _ = ε ^ (T - 2) * ∑' k, ρ k ^ 2 := tsum_mul_left
    _ ≤ ε ^ T := mul_sq_le_pow hε hsq hT

/-- (D.1) with the infinite tail as a `tsum`: the tail ratios `(ρ_k/λ₀)^T` are summable and the
excited trace is at most `d_T = Σ_{1 ≤ j < m} ((μ_j + ε)/δ)^T + (ε/δ)^T`. -/
theorem excited_tsum_le {ι κ : Type*} (s : Finset ι) (lam mu : ι → ℝ) (ρ : κ → ℝ)
    {lam0 δ ε : ℝ} (hδ : 0 < δ) (h0 : δ ≤ lam0) (hε : 0 ≤ ε)
    (hl0 : ∀ j ∈ s, 0 ≤ lam j) (hlμ : ∀ j ∈ s, lam j ≤ mu j + ε)
    (hρ0 : ∀ k, 0 ≤ ρ k) (hs : Summable fun k => ρ k ^ 2)
    (hsq : ∑' k, ρ k ^ 2 ≤ ε ^ 2) {T : ℕ} (hT : 2 ≤ T) :
    Summable (fun k => (ρ k / lam0) ^ T) ∧
      ∑ j ∈ s, (lam j / lam0) ^ T + ∑' k, (ρ k / lam0) ^ T ≤
        ∑ j ∈ s, ((mu j + ε) / δ) ^ T + (ε / δ) ^ T := by
  obtain ⟨hsum, hle⟩ := tail_tsum_le ρ hε hρ0 hs hsq hT
  simp_rw [div_pow]
  refine ⟨hsum.div_const _, ?_⟩
  rw [tsum_div_const]
  have := div_pow_le hδ h0 hε hle
  have := head_le s lam mu hδ h0 hl0 hlμ T
  simp_rw [div_pow] at *
  linarith

/-- The pressure bound: `0 < Tr R^T ≤ 1 + d_T` and `Tr R^{2T} ≥ 1` give `ψ_T ≤ 2 log(1 + d_T)`. -/
theorem pressure_le {X Y d : ℝ} (hX : 0 < X) (hXd : X ≤ 1 + d) (hY : 1 ≤ Y) :
    2 * log X - log Y ≤ 2 * log (1 + d) :=
  PurityTrace.psi_le hX hXd hY

/-- Simplicity: excited ratios `r_j ≥ 0` with `Σ r_j^T ≤ d < 1` are all `< 1`. -/
theorem ratio_lt_one {ι : Type*} (s : Finset ι) (r : ι → ℝ) {d : ℝ} {T : ℕ}
    (hr0 : ∀ j ∈ s, 0 ≤ r j) (hsum : ∑ j ∈ s, r j ^ T ≤ d) (hd : d < 1) :
    ∀ i ∈ s, r i < 1 := by
  intro i hi
  have hle : r i ^ T ≤ d :=
    (Finset.single_le_sum (fun j hj => pow_nonneg (hr0 j hj) T) hi).trans hsum
  by_contra h
  push Not at h
  have := one_le_pow₀ (n := T) h
  linarith

/-- Each excited ratio is at most `d^{1/T}` when `Σ r_j^T ≤ d`. -/
theorem ratio_le_root {ι : Type*} (s : Finset ι) (r : ι → ℝ) {d : ℝ} {T : ℕ} (hT : T ≠ 0)
    (hr0 : ∀ j ∈ s, 0 ≤ r j) (hsum : ∑ j ∈ s, r j ^ T ≤ d) :
    ∀ i ∈ s, r i ≤ d ^ ((T : ℝ)⁻¹) := by
  intro i hi
  have hle : r i ^ T ≤ d :=
    (Finset.single_le_sum (fun j hj => pow_nonneg (hr0 j hj) T) hi).trans hsum
  calc r i = (r i ^ T) ^ ((T : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast (hr0 i hi) hT).symm
    _ ≤ d ^ ((T : ℝ)⁻¹) :=
        Real.rpow_le_rpow (pow_nonneg (hr0 i hi) T) hle (by positivity)

end MassGap.PurityFiniteRank

#print axioms MassGap.PurityFiniteRank.mul_sq_le_pow
#print axioms MassGap.PurityFiniteRank.le_of_sq_le
#print axioms MassGap.PurityFiniteRank.tail_pow_le
#print axioms MassGap.PurityFiniteRank.head_le
#print axioms MassGap.PurityFiniteRank.div_pow_le
#print axioms MassGap.PurityFiniteRank.excited_le
#print axioms MassGap.PurityFiniteRank.tail_tsum_le
#print axioms MassGap.PurityFiniteRank.excited_tsum_le
#print axioms MassGap.PurityFiniteRank.pressure_le
#print axioms MassGap.PurityFiniteRank.ratio_lt_one
#print axioms MassGap.PurityFiniteRank.ratio_le_root
