import Mathlib
import MassGap.CellEnclosure
import MassGap.Mixing

/-!
# MassGap.CellSpectrum — spectral infrastructure for the single-cell gap (B1)

Eigenvalue bounds on the single-plaquette Hamiltonian `Hcell` toward the certified gap `≥ κ₀`, built from
Mathlib's PosDef / PosSemidef quadratic-form theory (`posDef_iff_eigenvalues_pos`,
`posSemidef_iff_dotProduct_mulVec`) rather than the eigenvalue-counting / min-max machinery Mathlib lacks.

Route:
* `E0 ≤ 0` — the ground energy is nonpositive: `⟨e₀, H e₀⟩ = H₀₀ = 0`, so `H` is not positive-definite.
* `E1 ≥ μ` — via "`H − μ` positive-semidefinite on the codim-1 subspace `e₀⊥` ⟹ at most one eigenvalue `< μ`"
  (the min-max count, being built).
* `gap = E1 − E0 ≥ μ − 0`, and for the relevant `λ` a diagonal-dominance bound gives `μ = κ₀`.
-/

namespace MassGap.CellEnclosure

open scoped Matrix

/-- The single-plaquette Hamiltonian over `ℝ` (for the spectral theory; `Hcell` itself is exact rationals). -/
noncomputable def HcellR (jmax : ℕ) (lam : ℚ) : Matrix (Fin (dim jmax)) (Fin (dim jmax)) ℝ :=
  (Hcell jmax lam).map (fun q => (q : ℝ))

/-- `HcellR` is Hermitian (real symmetric). -/
theorem HcellR_isHermitian (jmax : ℕ) (lam : ℚ) : (HcellR jmax lam).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, HcellR, Matrix.map_apply, star_trivial]
  have h := congrFun (congrFun (Hcell_transpose jmax lam) i) j
  simp only [Matrix.transpose_apply] at h
  exact_mod_cast h

/-- The `(0,0)` diagonal entry of `Hcell` is `0` (the `j = 0` state has zero Casimir). -/
theorem HcellR_zero_zero (jmax : ℕ) (lam : ℚ) :
    HcellR jmax lam ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ = 0 := by
  simp only [HcellR, Matrix.map_apply, Hcell, Matrix.of_apply, if_pos rfl]
  norm_num

/-- **The single-cell ground energy is `≤ 0`.** Some eigenvalue of `Hcell` is nonpositive: were all positive,
`Hcell` would be positive-definite, but the quadratic form at `e₀` is `H₀₀ = 0`, which contradicts the strict
positivity `PosDef` demands. -/
theorem cell_exists_eigenvalue_le_zero (jmax : ℕ) (lam : ℚ) :
    ∃ i, (HcellR_isHermitian jmax lam).eigenvalues i ≤ 0 := by
  by_contra h
  push_neg at h
  have hpd : (HcellR jmax lam).PosDef :=
    (Matrix.IsHermitian.posDef_iff_eigenvalues_pos (HcellR_isHermitian jmax lam)).mpr h
  have hne : (Finsupp.single (⟨0, Nat.succ_pos _⟩ : Fin (dim jmax)) (1 : ℝ)) ≠ 0 :=
    (Finsupp.single_ne_zero).mpr one_ne_zero
  have hq := hpd.2 hne
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp),
    star_one, one_mul, mul_one, HcellR_zero_zero] at hq
  exact lt_irrefl 0 hq

/-- The quadratic form of a Hermitian real matrix at its `i`-th eigenvector equals the `i`-th eigenvalue:
`⟨vᵢ, A vᵢ⟩ = λᵢ`. Direct from Mathlib's `eigenvalues_eq` (the `RCLike.re` is the identity over `ℝ`). -/
theorem eigen_quadForm {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) (i : Fin N) :
    star (⇑(hA.eigenvectorBasis i)) ⬝ᵥ (A *ᵥ ⇑(hA.eigenvectorBasis i)) = hA.eigenvalues i := by
  have h := hA.eigenvalues_eq i
  rw [h, RCLike.re_to_real]

/-- The eigenvectors are orthonormal in dotProduct form: `vᵢ · vⱼ = δᵢⱼ`. -/
theorem eigen_orthonormal {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) (i j : Fin N) :
    star (⇑(hA.eigenvectorBasis i)) ⬝ᵥ (⇑(hA.eigenvectorBasis j)) = if i = j then 1 else 0 := by
  have ho := hA.eigenvectorBasis.orthonormal
  rw [orthonormal_iff_ite] at ho
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
  exact ho i j

/-- Cross term: `⟨vᵢ, A vⱼ⟩ = λⱼ · δᵢⱼ` (zero off the diagonal), from `A vⱼ = λⱼ vⱼ` + orthonormality. -/
theorem eigen_crossForm {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) (i j : Fin N) :
    star (⇑(hA.eigenvectorBasis i)) ⬝ᵥ (A *ᵥ ⇑(hA.eigenvectorBasis j)) = if i = j then hA.eigenvalues j else 0 := by
  rw [hA.mulVec_eigenvectorBasis, dotProduct_smul, eigen_orthonormal, smul_eq_mul]
  by_cases h : i = j <;> simp [h]

-- star-free forms (over ℝ, `star` on the eigenvector functions is the identity)
theorem eigen_quadForm' {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) (i : Fin N) :
    ⇑(hA.eigenvectorBasis i) ⬝ᵥ (A *ᵥ ⇑(hA.eigenvectorBasis i)) = hA.eigenvalues i := by
  have h := eigen_quadForm hA i; rwa [star_trivial] at h

theorem eigen_orthonormal' {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) (i j : Fin N) :
    ⇑(hA.eigenvectorBasis i) ⬝ᵥ (⇑(hA.eigenvectorBasis j)) = if i = j then 1 else 0 := by
  have h := eigen_orthonormal hA i j; rwa [star_trivial] at h

theorem eigen_crossForm' {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) (i j : Fin N) :
    ⇑(hA.eigenvectorBasis i) ⬝ᵥ (A *ᵥ ⇑(hA.eigenvectorBasis j)) = if i = j then hA.eigenvalues j else 0 := by
  have h := eigen_crossForm hA i j; rwa [star_trivial] at h

/-- **Spectral core: a mode's contraction rate is at most its gap.** If the transfer eigenvalue at `i` is
`e^{−Δ}` (the slowest excited mode) and the Rayleigh quotient of `T` at that eigenvector is `≤ e^{−c}`
(a contraction at rate `c`), then `c ≤ Δ` — because the Rayleigh quotient of `T` at `vᵢ` is EXACTLY `e^{−Δ}`.
Foundation-only. -/
theorem gap_ge_of_mode_contraction {N : ℕ} {T : Matrix (Fin N) (Fin N) ℝ} (hT : T.IsHermitian)
    {Δ c : ℝ} {i : Fin N} (hΔ : hT.eigenvalues i = Real.exp (-Δ))
    (hcontr : ⇑(hT.eigenvectorBasis i) ⬝ᵥ (T *ᵥ ⇑(hT.eigenvectorBasis i))
              ≤ Real.exp (-c) * (⇑(hT.eigenvectorBasis i) ⬝ᵥ ⇑(hT.eigenvectorBasis i))) :
    c ≤ Δ := by
  rw [eigen_quadForm' hT i, hΔ, eigen_orthonormal' hT i i, if_pos rfl, mul_one] at hcontr
  have := Real.exp_le_exp.mp hcontr
  linarith

/-- **`c ≤ Δ` from a uniform contraction on the mean-zero sector — discharges `Margin.hgap` by PROOF.**
If `T` contracts every vector orthogonal to the vacuum `v_{j₀}` at rate `c` (`⟨f,Tf⟩ ≤ e^{−c}⟨f,f⟩`), then
the transfer gap `Δ` (from the slowest excited eigenvalue `e^{−Δ}` at `i ≠ j₀`) satisfies `c ≤ Δ`. So the
Margin input `hgap : c ≤ Δ` is NOT an independent open assumption: it follows from the mean-zero uniform
contraction that `ReachFreeze` supplies (the slowest excited eigenvector is itself mean-zero). The one
genuinely-open step-2 input is `hfe : κ−μ ≤ c` (the vortex free-energy identification). Foundation-only. -/
theorem gap_ge_of_uniform_contraction {N : ℕ} {T : Matrix (Fin N) (Fin N) ℝ} (hT : T.IsHermitian)
    {Δ c : ℝ} {i j₀ : Fin N} (hij : i ≠ j₀) (hΔ : hT.eigenvalues i = Real.exp (-Δ))
    (hcontr : ∀ f : Fin N → ℝ, ⇑(hT.eigenvectorBasis j₀) ⬝ᵥ f = 0 →
        f ⬝ᵥ (T *ᵥ f) ≤ Real.exp (-c) * (f ⬝ᵥ f)) :
    c ≤ Δ := by
  refine gap_ge_of_mode_contraction hT hΔ (hcontr _ ?_)
  rw [eigen_orthonormal' hT j₀ i, if_neg (Ne.symm hij)]

/-- The squared norm of `a·vᵢ + b·vⱼ` (i ≠ j) is `a² + b²`, by orthonormality. -/
theorem combo_norm {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) {i j : Fin N} (hij : i ≠ j)
    (a b : ℝ) :
    (a • ⇑(hA.eigenvectorBasis i) + b • ⇑(hA.eigenvectorBasis j)) ⬝ᵥ
      (a • ⇑(hA.eigenvectorBasis i) + b • ⇑(hA.eigenvectorBasis j)) = a ^ 2 + b ^ 2 := by
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    eigen_orthonormal', if_neg hij, if_neg (Ne.symm hij), if_true]
  ring

/-- The quadratic form of `A` at `a·vᵢ + b·vⱼ` (i ≠ j) is `a²λᵢ + b²λⱼ`, by orthogonality of the eigenvectors. -/
theorem combo_form {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) {i j : Fin N} (hij : i ≠ j)
    (a b : ℝ) :
    (a • ⇑(hA.eigenvectorBasis i) + b • ⇑(hA.eigenvectorBasis j)) ⬝ᵥ
      (A *ᵥ (a • ⇑(hA.eigenvectorBasis i) + b • ⇑(hA.eigenvectorBasis j))) =
    a ^ 2 * hA.eigenvalues i + b ^ 2 * hA.eigenvalues j := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, eigen_crossForm', if_neg hij,
    if_neg (Ne.symm hij), if_true]
  ring

/-- On the span of two distinct eigenvectors whose eigenvalues are `< μ`, the quadratic form is strictly
below `μ · ‖·‖²` (for any nonzero combination). -/
theorem combo_lt {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) {i j : Fin N} (hij : i ≠ j)
    {μ : ℝ} (hi : hA.eigenvalues i < μ) (hj : hA.eigenvalues j < μ) (a b : ℝ)
    (hx : a • ⇑(hA.eigenvectorBasis i) + b • ⇑(hA.eigenvectorBasis j) ≠ 0) :
    (a • ⇑(hA.eigenvectorBasis i) + b • ⇑(hA.eigenvectorBasis j)) ⬝ᵥ
      (A *ᵥ (a • ⇑(hA.eigenvectorBasis i) + b • ⇑(hA.eigenvectorBasis j))) <
    μ * ((a • ⇑(hA.eigenvectorBasis i) + b • ⇑(hA.eigenvectorBasis j)) ⬝ᵥ
      (a • ⇑(hA.eigenvectorBasis i) + b • ⇑(hA.eigenvectorBasis j))) := by
  rw [combo_form hA hij, combo_norm hA hij]
  have hab : a ^ 2 ≠ 0 ∨ b ^ 2 ≠ 0 := by
    rcases eq_or_ne a 0 with ha | ha
    · rcases eq_or_ne b 0 with hb | hb
      · exact absurd (by rw [ha, hb]; simp) hx
      · exact Or.inr (pow_ne_zero 2 hb)
    · exact Or.inl (pow_ne_zero 2 ha)
  rcases hab with h | h
  · have hpa : 0 < a ^ 2 := (sq_nonneg a).lt_of_ne (Ne.symm h)
    nlinarith [mul_pos hpa (sub_pos.mpr hi), mul_nonneg (sq_nonneg b) (sub_pos.mpr hj).le]
  · have hpb : 0 < b ^ 2 := (sq_nonneg b).lt_of_ne (Ne.symm h)
    nlinarith [mul_pos hpb (sub_pos.mpr hj), mul_nonneg (sq_nonneg a) (sub_pos.mpr hi).le]

/-- **Count lemma (min-max, one side).** If the quadratic form of a Hermitian matrix is `≥ μ·‖·‖²` on a
subspace `W` of corank at most 1 (`N ≤ finrank W + 1`), then at most one eigenvalue is `< μ`. Two low
eigenvectors span a 2-plane that must meet `W` (dimensions sum to `> N`), yielding a vector with the form both
`< μ‖·‖²` (`combo_lt`) and `≥ μ‖·‖²` (on `W`) — a contradiction. -/
theorem atMostOne_eigenvalue_lt {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) {μ : ℝ}
    (W : Submodule ℝ (Fin N → ℝ)) (hW : N ≤ Module.finrank ℝ W + 1)
    (hpos : ∀ x ∈ W, μ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)) :
    (Finset.univ.filter (fun i => hA.eigenvalues i < μ)).card ≤ 1 := by
  by_contra hc
  rw [not_le] at hc
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  -- the two eigenvectors are linearly independent — proved directly in `Fin N → ℝ` from the
  -- dotProduct orthonormality `eigen_orthonormal'` (dotting the relation with each eigenvector)
  have hpair : LinearIndependent ℝ ![⇑(hA.eigenvectorBasis i), ⇑(hA.eigenvectorBasis j)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have key_i : (⇑(hA.eigenvectorBasis i)) ⬝ᵥ
        (s • ⇑(hA.eigenvectorBasis i) + t • ⇑(hA.eigenvectorBasis j)) = s := by
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, eigen_orthonormal' hA i i,
        eigen_orthonormal' hA i j, if_pos rfl, if_neg hij, smul_eq_mul, smul_eq_mul,
        mul_one, mul_zero, add_zero]
    have key_j : (⇑(hA.eigenvectorBasis j)) ⬝ᵥ
        (s • ⇑(hA.eigenvectorBasis i) + t • ⇑(hA.eigenvectorBasis j)) = t := by
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, eigen_orthonormal' hA j i,
        eigen_orthonormal' hA j j, if_neg (Ne.symm hij), if_pos rfl, smul_eq_mul, smul_eq_mul,
        mul_zero, mul_one, zero_add]
    rw [hst, dotProduct_zero] at key_i key_j
    exact ⟨key_i.symm, key_j.symm⟩
  set U : Submodule ℝ (Fin N → ℝ) :=
    Submodule.span ℝ {⇑(hA.eigenvectorBasis i), ⇑(hA.eigenvectorBasis j)} with hU_def
  have hset : (Set.range ![⇑(hA.eigenvectorBasis i), ⇑(hA.eigenvectorBasis j)]) =
      ({⇑(hA.eigenvectorBasis i), ⇑(hA.eigenvectorBasis j)} : Set (Fin N → ℝ)) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, rfl⟩; fin_cases k <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  have hUdim : Module.finrank ℝ U = 2 := by
    rw [hU_def, ← hset, finrank_span_eq_card hpair, Fintype.card_fin]
  -- U ⊓ W is nonzero: finrank(U ⊓ W) ≥ finrank U + finrank W − N ≥ 2 + (N−1) − N = 1
  have hle : Module.finrank ℝ ↥(U ⊔ W) ≤ N := by
    calc Module.finrank ℝ ↥(U ⊔ W) ≤ Module.finrank ℝ (Fin N → ℝ) := Submodule.finrank_le _
      _ = N := Module.finrank_fin_fun (R := ℝ)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U W
  have hInterPos : 0 < Module.finrank ℝ ↥(U ⊓ W) := by omega
  have hne_bot : U ⊓ W ≠ ⊥ := by
    intro hbot; rw [hbot, finrank_bot] at hInterPos; exact lt_irrefl 0 hInterPos
  obtain ⟨x, hxmem, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
  obtain ⟨hxU, hxW⟩ := Submodule.mem_inf.mp hxmem
  rw [hU_def] at hxU
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hxU
  rw [← hab] at hx0 hxW
  have hlt := combo_lt hA hij hi hj a b hx0
  have hge := hpos _ hxW
  linarith

/-- **Spectral gap from a codim-1 form bound.** If the quadratic form of a Hermitian `A` is `≥ μ·‖·‖²`
(`μ > 0`) on a subspace of corank ≤ 1, and some eigenvalue `i₀` is `≤ 0` (a ground state at/below zero),
then EVERY other eigenvalue exceeds it by at least `μ`: the spectrum sits in `{λ_{i₀}} ∪ [λ_{i₀}+μ, ∞)`.
This is the count lemma (`atMostOne_eigenvalue_lt`) turned into the mass-gap spectral condition: at most one
eigenvalue is below `μ`, and it is the ground `λ_{i₀} ≤ 0`, so all others are `≥ μ ≥ λ_{i₀}+μ`. -/
theorem eigenvalues_gap_of_codim1_form {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    {μ : ℝ} (hμ : 0 < μ) (W : Submodule ℝ (Fin N → ℝ)) (hW : N ≤ Module.finrank ℝ W + 1)
    (hpos : ∀ x ∈ W, μ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x))
    {i₀ : Fin N} (hi₀ : hA.eigenvalues i₀ ≤ 0) {i : Fin N} (hi : i ≠ i₀) :
    hA.eigenvalues i₀ + μ ≤ hA.eigenvalues i := by
  by_contra h
  push_neg at h
  have hcard := atMostOne_eigenvalue_lt hA W hW hpos
  set S := Finset.univ.filter (fun k => hA.eigenvalues k < μ) with hS
  have hi0mem : i₀ ∈ S := by
    rw [hS]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; linarith
  have himem : i ∈ S := by
    rw [hS]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; linarith
  have h2 : 1 < S.card := Finset.one_lt_card.mpr ⟨i, himem, i₀, hi0mem, hi⟩
  omega

/-- A Hermitian real matrix with a zero diagonal entry has a nonpositive eigenvalue: the quadratic form
at that coordinate axis is `A k k = 0`, so `A` cannot be positive-definite. (Generalises the `Hcell`
ground-energy bound to any Hamiltonian with a zero-Casimir vacuum state.) -/
theorem exists_eigenvalue_le_zero_of_diag {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (k : Fin N) (hk : A k k = 0) : ∃ i, hA.eigenvalues i ≤ 0 := by
  by_contra h
  push_neg at h
  have hpd : A.PosDef := (Matrix.IsHermitian.posDef_iff_eigenvalues_pos hA).mpr h
  have hne : (Finsupp.single k (1 : ℝ)) ≠ 0 := (Finsupp.single_ne_zero).mpr one_ne_zero
  have hq := hpd.2 hne
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp),
    star_one, one_mul, mul_one, hk] at hq
  exact lt_irrefl 0 hq

open Matrix in
/-- **Variational (Rayleigh) upper bound on the least eigenvalue.** If a nonzero trial vector `ψ` has
Rayleigh quotient `≤ r` (`ψ⬝ᵥ(A*ᵥψ) ≤ r·(ψ⬝ᵥψ)`), then `A` has an eigenvalue `≤ r`. Generalizes
`exists_eigenvalue_le_zero_of_diag` (the case `r=0`, `ψ = eₖ` with `Aₖₖ=0`); supplies the tight `E₀`
upper bound (`λ_{i₀} ≤ t−μ`) that `gap_of_ldl_one_neg_pivot_rel` consumes in the large-λ regime.
Proof: if all eigenvalues exceeded `r`, then `A − r•I` would be `PosDef` (diagonal `λ−r ≻ 0` conjugated
by the eigenvector unitary), forcing `ψ⬝ᵥ((A−r•I)*ᵥψ) > 0`, i.e. Rayleigh `> r` — contradiction. -/
theorem exists_eigenvalue_le_of_form {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    {r : ℝ} {ψ : Fin N → ℝ} (hψ : ψ ≠ 0) (hle : ψ ⬝ᵥ (A *ᵥ ψ) ≤ r * (ψ ⬝ᵥ ψ)) :
    ∃ i, hA.eigenvalues i ≤ r := by
  by_contra h
  push_neg at h
  set D : Matrix (Fin N) (Fin N) ℝ := diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  have hDr : D - r • 1 = diagonal (fun i => hA.eigenvalues i - r) := by
    rw [hD]; ext i j
    rcases eq_or_ne i j with hij | hij
    · subst hij; simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
    · simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hij,
        Matrix.diagonal_apply_ne _ hij]
  have hdiagPD : (D - r • 1).PosDef := by
    rw [hDr, Matrix.posDef_diagonal_iff]; intro i; linarith [h i]
  have hst : A = (Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary) D := hA.spectral_theorem
  have hAeq : A - r • 1 = (Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary) (D - r • 1) := by
    rw [map_sub, map_smul, map_one, ← hst]
  have hUunit : IsUnit (↑hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) := Unitary.isUnit_coe
  have hAPD : (A - r • 1).PosDef := by
    rw [hAeq, Unitary.conjStarAlgAut_apply]
    exact (hUunit.posDef_star_right_conjugate_iff).mpr hdiagPD
  have hq := hAPD.dotProduct_mulVec_pos hψ
  have hquad : ψ ⬝ᵥ ((A - r • 1) *ᵥ ψ) = ψ ⬝ᵥ (A *ᵥ ψ) - r * (ψ ⬝ᵥ ψ) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
  simp only [star_trivial] at hq
  rw [hquad] at hq
  linarith

/-! ### The Sturm / LDLᵀ inertia engine for the eigenvalue enclosure

The `E₁` (second-eigenvalue) half of the exact-rational cell enclosure (`small_volume_enclosure.py`):
a completing-the-square factorization `A − μ•I = Lᵀ · diagonal p · L` with **exactly one** negative
pivot (Sylvester inertia = one eigenvalue below `μ`) forces the form `≥ μ‖·‖²` on the codimension-1
kernel `{x : (Lx)_m = 0}` — the negative term is killed — feeding `eigenvalues_gap_of_codim1_form`.
Together with `CellEnclosure.posSemidef_of_ldl` (zero negative pivots ⟹ `E₀ ≥ s`) and
`CellEnclosure.ldl_entry` (the pivots), this is the abstract Sturm gap engine. -/

section LDLSturm
open Matrix

/-- The LDLᵀ quadratic form: `x ⬝ᵥ ((Lᵀ · diagonal p · L) *ᵥ x) = ∑ₖ pₖ (Lx)ₖ²`. -/
theorem ldl_quadform {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) (p : Fin N → ℝ) (x : Fin N → ℝ) :
    x ⬝ᵥ ((Lᵀ * Matrix.diagonal p * L) *ᵥ x) = ∑ k, p k * (L *ᵥ x) k ^ 2 := by
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.mulVec_diagonal]; ring

/-- Form bound on the LDLᵀ kernel: `A − μ•I = Lᵀ diag p L` with pivots nonneg off `m` ⟹ on
`{x : (Lx)_m = 0}` the form of `A` is `≥ μ‖·‖²` (the single negative pivot is killed on the kernel). -/
theorem ldl_form_ge_on_kernel {N : ℕ} (A L : Matrix (Fin N) (Fin N) ℝ) (p : Fin N → ℝ) (m : Fin N)
    (μ : ℝ) (hp : ∀ k, k ≠ m → 0 ≤ p k)
    (hrec : A - μ • (1 : Matrix (Fin N) (Fin N) ℝ) = Lᵀ * Matrix.diagonal p * L)
    (x : Fin N → ℝ) (hx : (L *ᵥ x) m = 0) :
    μ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  have hsplit : x ⬝ᵥ ((A - μ • 1) *ᵥ x) = x ⬝ᵥ (A *ᵥ x) - μ * (x ⬝ᵥ x) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
  have hge : 0 ≤ ∑ k, p k * (L *ᵥ x) k ^ 2 := by
    apply Finset.sum_nonneg; intro k _
    by_cases hk : k = m
    · subst hk; rw [hx]; simp
    · exact mul_nonneg (hp k hk) (sq_nonneg _)
  have key : x ⬝ᵥ (A *ᵥ x) - μ * (x ⬝ᵥ x) = ∑ k, p k * (L *ᵥ x) k ^ 2 := by
    rw [← hsplit, hrec, ldl_quadform]
  linarith [key, hge]

/-- The LDLᵀ kernel `{x : (Lx)_m = 0}` as a codimension-≤1 subspace (kernel of a functional to `ℝ`). -/
def ldlKer {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) (m : Fin N) : Submodule ℝ (Fin N → ℝ) :=
  LinearMap.ker ((LinearMap.proj m).comp (Matrix.mulVecLin L))

lemma ldlKer_mem {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) (m : Fin N) (x : Fin N → ℝ) :
    x ∈ ldlKer L m ↔ (L *ᵥ x) m = 0 := by
  unfold ldlKer
  rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.proj_apply, Matrix.mulVecLin_apply]

lemma ldlKer_corank {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) (m : Fin N) :
    N ≤ Module.finrank ℝ (ldlKer L m) + 1 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker
    ((LinearMap.proj m).comp (Matrix.mulVecLin L))
  have hr1 : Module.finrank ℝ (LinearMap.range ((LinearMap.proj m).comp (Matrix.mulVecLin L))) ≤ 1 := by
    calc Module.finrank ℝ (LinearMap.range ((LinearMap.proj m).comp (Matrix.mulVecLin L)))
        ≤ Module.finrank ℝ ℝ := Submodule.finrank_le _
      _ = 1 := Module.finrank_self ℝ
  rw [Module.finrank_fin_fun (R := ℝ)] at hrn
  unfold ldlKer
  omega

/-- **E₁ gap from an LDLᵀ certificate with one negative pivot.** `A` Hermitian with a vacuum
eigenvalue `≤ 0` at `i₀`, and `A − μ•I = Lᵀ diag p L` with all pivots nonneg except possibly at `m`:
then every non-vacuum eigenvalue is `≥ λ_{i₀} + μ`. This is the `E₁ ≥ E₀ + μ` half of the Sturm/Feshbach
enclosure — the "one negative pivot ⟹ at most one eigenvalue below threshold" count, done by proof. -/
theorem gap_of_ldl_one_neg_pivot {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    {μ : ℝ} (hμ : 0 < μ) (L : Matrix (Fin N) (Fin N) ℝ) (p : Fin N → ℝ) (m : Fin N)
    (hp : ∀ k, k ≠ m → 0 ≤ p k)
    (hrec : A - μ • (1 : Matrix (Fin N) (Fin N) ℝ) = Lᵀ * Matrix.diagonal p * L)
    {i₀ : Fin N} (hi₀ : hA.eigenvalues i₀ ≤ 0) {i : Fin N} (hi : i ≠ i₀) :
    hA.eigenvalues i₀ + μ ≤ hA.eigenvalues i := by
  apply eigenvalues_gap_of_codim1_form hA hμ (ldlKer L m) (ldlKer_corank L m) _ hi₀ hi
  intro x hx
  rw [ldlKer_mem] at hx
  exact ldl_form_ge_on_kernel A L p m μ hp hrec x hx

/-- **Relative gap from an LDLᵀ certificate with one negative pivot.** `A` Hermitian, `A − t•I = Lᵀ diag p L`
with all pivots nonneg except at one index `m` (so at most one eigenvalue is below `t`), and a tight bound
`λ_{i₀} ≤ t − μ` (`μ>0`): then every OTHER eigenvalue is `≥ λ_{i₀}+μ`. Generalizes
`gap_of_ldl_one_neg_pivot` (the case `t=μ`, `λ_{i₀}≤0`) to the large-λ regime where BOTH `E₀,E₁` are
negative and the gap is relative — `t` is a Sturm shift with one eigenvalue below it, `t−μ` a tight `E₀`
upper bound (a trial state); the two together bracket the gap. -/
theorem gap_of_ldl_one_neg_pivot_rel {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    {t μ : ℝ} (hμ : 0 < μ) (L : Matrix (Fin N) (Fin N) ℝ) (p : Fin N → ℝ) (m : Fin N)
    (hp : ∀ k, k ≠ m → 0 ≤ p k)
    (hrec : A - t • (1 : Matrix (Fin N) (Fin N) ℝ) = Lᵀ * Matrix.diagonal p * L)
    {i₀ : Fin N} (hi₀ : hA.eigenvalues i₀ ≤ t - μ) {i : Fin N} (hi : i ≠ i₀) :
    hA.eigenvalues i₀ + μ ≤ hA.eigenvalues i := by
  have hform : ∀ x ∈ ldlKer L m, t * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
    intro x hx
    rw [ldlKer_mem] at hx
    exact ldl_form_ge_on_kernel A L p m t hp hrec x hx
  have hcard := atMostOne_eigenvalue_lt hA (ldlKer L m) (ldlKer_corank L m) hform
  have hi0lt : hA.eigenvalues i₀ < t := by linarith
  by_contra h
  push_neg at h
  have hilt : hA.eigenvalues i < t := by linarith
  set S := Finset.univ.filter (fun k => hA.eigenvalues k < t) with hS
  have hi0mem : i₀ ∈ S := by
    rw [hS]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi0lt
  have himem : i ∈ S := by
    rw [hS]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hilt
  have h2 : 1 < S.card := Finset.one_lt_card.mpr ⟨i, himem, i₀, hi0mem, hi⟩
  omega

/-- **Convexity of the codim-1 form bound for an affine family.** If a Hermitian form is `≥ c‖·‖²` on a
subspace `W` at both `A` and `B`, it is `≥ c‖·‖²` on `W` for every convex combination `(1−s)A+sB`. Since
the physical cell `H(λ) = D − λ·M` is affine in `λ`, this extends any codim-1 form bound over a whole
`λ`-interval from its two endpoints — the grid closure, with NO Weyl / min-max needed. -/
theorem form_ge_convex {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) {c : ℝ}
    (W : Submodule ℝ (Fin N → ℝ))
    (hA : ∀ x ∈ W, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x))
    (hB : ∀ x ∈ W, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∀ x ∈ W, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (((1 - s) • A + s • B) *ᵥ x) := by
  intro x hx
  have hAx := hA x hx; have hBx := hB x hx
  have hform : x ⬝ᵥ (((1 - s) • A + s • B) *ᵥ x)
      = (1 - s) * (x ⬝ᵥ (A *ᵥ x)) + s * (x ⬝ᵥ (B *ᵥ x)) := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  rw [hform]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - s) (sub_nonneg.mpr hAx),
    mul_nonneg hs0 (sub_nonneg.mpr hBx)]

/-- **Interval gap closure (absolute regime), the λ-grid step.** For an affine Hermitian family
`(1−s)A+sB` (= the cell `H(λ)` at `λ = (1−s)λ_lo + sλ_hi`), if the codim-1 form is `≥ μ` on `W` at BOTH
endpoints `A,B` and the family has a vacuum eigenvalue `≤ 0`, then every non-vacuum eigenvalue is
`≥ λ_{i₀}+μ` for EVERY `s∈[0,1]` — the whole `λ`-interval, from the two endpoint form-certificates. This
replaces the banked per-λ grid + Weyl: a finite set of endpoint checks covers the continuum. -/
theorem gap_on_interval {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) {μ : ℝ} (hμ : 0 < μ)
    (W : Submodule ℝ (Fin N → ℝ)) (hW : N ≤ Module.finrank ℝ W + 1)
    (hAf : ∀ x ∈ W, μ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x))
    (hBf : ∀ x ∈ W, μ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hH : ((1 - s) • A + s • B).IsHermitian)
    {i₀ : Fin N} (hi₀ : hH.eigenvalues i₀ ≤ 0) {i : Fin N} (hi : i ≠ i₀) :
    hH.eigenvalues i₀ + μ ≤ hH.eigenvalues i :=
  eigenvalues_gap_of_codim1_form hH hμ W hW
    (form_ge_convex A B W hAf hBf hs0 hs1) hi₀ hi

/-- Nearest-neighbour adjacency (the off-diagonal 1's of the tridiagonal cell). -/
def adjM (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0

/-- The physical SU(2) cell over REAL `λ`: `diagonal(Casimir) − λ·adjacency`, manifestly affine in `λ`
(so the codim-1 form bound is convex in `λ` — see `HcellRr_gap_on_interval`). -/
noncomputable def HcellRr (jmax : ℕ) (lam : ℝ) : Matrix (Fin (dim jmax)) (Fin (dim jmax)) ℝ :=
  Matrix.diagonal (fun i => (i.val * (i.val + 2) : ℝ) / 4) - lam • adjM (dim jmax)

/-- **Affine interpolation:** `H((1−s)a + s·b) = (1−s)•H(a) + s•H(b)`. -/
lemma HcellRr_affine (jmax : ℕ) (a b s : ℝ) :
    HcellRr jmax ((1 - s) * a + s * b) = (1 - s) • HcellRr jmax a + s • HcellRr jmax b := by
  simp only [HcellRr]; match_scalars <;> ring

lemma adjM_symm (n : ℕ) : (adjM n)ᵀ = adjM n := by
  ext i j; simp only [Matrix.transpose_apply, adjM, Matrix.of_apply]; exact if_congr or_comm rfl rfl

lemma HcellRr_isHermitian (jmax : ℕ) (lam : ℝ) : (HcellRr jmax lam).IsHermitian := by
  have hT : (HcellRr jmax lam)ᵀ = HcellRr jmax lam := by
    rw [HcellRr, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.diagonal_transpose, adjM_symm]
  ext i j; simp only [Matrix.conjTranspose_apply, star_trivial]; exact congrFun (congrFun hT i) j

/-- **Interval gap for the physical cell — the λ-grid step.** From the codim-1 form-certificate `≥ μ`
on `W` at BOTH endpoints `HcellRr a`, `HcellRr b` and a vacuum eigenvalue `≤ 0`, the gap `≥ μ` holds at
`HcellRr` for EVERY `λ = (1−s)a + s·b` in `[a,b]` — the whole interval from two endpoint certificates,
no Weyl. Tiling `[0.16,6.76]` with such intervals closes the continuous-λ cell gap. -/
theorem HcellRr_gap_on_interval (jmax : ℕ) (a b : ℝ) {μ : ℝ} (hμ : 0 < μ)
    (W : Submodule ℝ (Fin (dim jmax) → ℝ)) (hW : dim jmax ≤ Module.finrank ℝ W + 1)
    (hAf : ∀ x ∈ W, μ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (HcellRr jmax a *ᵥ x))
    (hBf : ∀ x ∈ W, μ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (HcellRr jmax b *ᵥ x))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {i₀ : Fin (dim jmax)} (hi₀ : (HcellRr_isHermitian jmax ((1 - s) * a + s * b)).eigenvalues i₀ ≤ 0)
    {i : Fin (dim jmax)} (hii : i ≠ i₀) :
    (HcellRr_isHermitian jmax ((1 - s) * a + s * b)).eigenvalues i₀ + μ
      ≤ (HcellRr_isHermitian jmax ((1 - s) * a + s * b)).eigenvalues i := by
  refine eigenvalues_gap_of_codim1_form (HcellRr_isHermitian jmax ((1 - s) * a + s * b)) hμ W hW ?_ hi₀ hii
  intro x hx
  rw [HcellRr_affine jmax a b s]
  exact form_ge_convex (HcellRr jmax a) (HcellRr jmax b) W hAf hBf hs0 hs1 x hx

/-- **Tridiagonal = LDLᵀ from the recurrence.** A symmetric tridiagonal `T` (diagonal `d`, off-diagonal
`c` between neighbours, zero elsewhere) equals `Lᵀ · diagonal p · L` whenever pivots `p` and multipliers
`e` satisfy the completing-the-square recurrence `dᵢ = pᵢ + eᵢ₊₁²pᵢ₊₁`, `cᵢ = eᵢ₊₁ pᵢ₊₁`. This is the
bridge from the abstract engine to a concrete cell: instantiate `T := Hcell jmax λ − s•I`, `d`, `c` from
the cell, then a pivot certificate `(p,e)` gives `E₀ ≥ s` (if `p ≥ 0`) or the `E₁` gap (one negative pivot). -/
theorem tridiag_ldl_of_recurrence {n : ℕ} (d c p e : Fin n → ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ)
    (hTdiag : ∀ i, T i i = d i)
    (hTsuper : ∀ i j, j.val = i.val + 1 → T i j = c i)
    (hTsub : ∀ i j, i.val = j.val + 1 → T i j = c j)
    (hTfar : ∀ i j, i ≠ j → i.val + 1 ≠ j.val → j.val + 1 ≠ i.val → T i j = 0)
    (hrecD : ∀ i, d i = p i + ∑ k, (if k.val = i.val + 1 then e k * (p k * e k) else 0))
    (hrecO : ∀ i j, j.val = i.val + 1 → c i = e j * p j) :
    T = (Lbi e)ᵀ * Matrix.diagonal p * (Lbi e) := by
  ext i j
  rw [ldl_entry]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_neg (show ¬ i.val = i.val + 1 by omega),
      if_neg (show ¬ i.val = i.val + 1 by omega), hTdiag, hrecD i]
    simp only [and_self]; ring
  · have hsum0 : (∑ k, if k.val = i.val + 1 ∧ k.val = j.val + 1 then e k * (p k * e k) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      rw [if_neg]; rintro ⟨h1, h2⟩; exact hij (Fin.ext (by omega))
    by_cases hsuper : j.val = i.val + 1
    · rw [if_neg hij, if_neg (show ¬ i.val = j.val + 1 by omega), if_pos hsuper,
        hsum0, hTsuper i j hsuper, hrecO i j hsuper]; ring
    · by_cases hsub : i.val = j.val + 1
      · rw [if_neg hij, if_pos hsub, if_neg (show ¬ j.val = i.val + 1 by omega),
          hsum0, hTsub i j hsub, hrecO j i hsub]; ring
      · rw [if_neg hij, if_neg (show ¬ i.val = j.val + 1 by omega),
          if_neg (show ¬ j.val = i.val + 1 by omega), hTfar i j hij
            (show i.val + 1 ≠ j.val by omega) (show j.val + 1 ≠ i.val by omega), hsum0]; ring

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedSimpArgs false in
/-- **End-to-end validation of the Sturm/LDLᵀ engine (non-vacuousness).** The 2-state SU(2) plaquette
cell `M = [[0,−1],[−1,¾]]` (`λ=1`) has spectral gap `≥ ½ (≥ κ₀)`, proved purely through the abstract
engine: the certificate `(p,e) = ((−9/2,¼),(0,−4))` factors `M − ½•I = Lᵀ diag p L` with exactly ONE
negative pivot (`p₀ = −9/2 < 0`, `p₁ = ¼ ≥ 0`), and `gap_of_ldl_one_neg_pivot` delivers the gap off the
vacuum (`M₀₀ = 0`). Demonstrates the full chain `tridiag_ldl_of_recurrence → gap_of_ldl_one_neg_pivot`
is correctly wired and satisfiable — the analogue of `knabe_gap_demo` for the cell engine. -/
theorem ldl_gap_demo (hM : (!![(0:ℝ), -1; -1, 3/4]).IsHermitian) :
    ∃ i₀, hM.eigenvalues i₀ ≤ 0 ∧ ∀ i, i ≠ i₀ → hM.eigenvalues i₀ + (1/2 : ℝ) ≤ hM.eigenvalues i := by
  set M : Matrix (Fin 2) (Fin 2) ℝ := !![(0:ℝ), -1; -1, 3/4] with hMdef
  set e : Fin 2 → ℝ := ![0, -4] with hedef
  set p : Fin 2 → ℝ := ![-9/2, 1/4] with hpdef
  have hM00 : M 0 0 = 0 := by rw [hMdef]; norm_num [Matrix.cons_val_zero]
  obtain ⟨i₀, hi₀⟩ := exists_eigenvalue_le_zero_of_diag hM 0 hM00
  refine ⟨i₀, hi₀, fun i hi => ?_⟩
  have hrec : M - (1/2 : ℝ) • 1 = (Lbi e)ᵀ * Matrix.diagonal p * (Lbi e) := by
    apply tridiag_ldl_of_recurrence ![(-1/2 : ℝ), 1/4] ![(-1 : ℝ), -1] p e
    · intro k; fin_cases k <;>
        simp [hMdef, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply] <;> norm_num
    · intro a b hab; fin_cases a <;> fin_cases b <;>
        simp_all [hMdef, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply] <;> norm_num
    · intro a b hab; fin_cases a <;> fin_cases b <;>
        simp_all [hMdef, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply] <;> norm_num
    · intro a b hne h1 h2; fin_cases a <;> fin_cases b <;> simp_all <;> omega
    · intro k; fin_cases k <;> simp [hpdef, hedef, Fin.sum_univ_two] <;> norm_num
    · intro a b hab; fin_cases a <;> fin_cases b <;> simp_all [hpdef, hedef] <;> norm_num
  exact gap_of_ldl_one_neg_pivot hM (by norm_num) (Lbi e) p 0
    (fun k hk => by fin_cases k <;> simp_all [hpdef] <;> norm_num) hrec hi₀ hi

end LDLSturm

/-! ### The physical SU(2) cell over ℝ, reduced to a pivot certificate

`HcellR jmax λ` is the single-plaquette Kogut–Susskind cell over ℝ (Casimir `i(i+2)/4` on the
diagonal, `−λ` off it) — the ℝ counterpart of the ℚ-valued `CellEnclosure.Hcell` used for the
exact-rational Sturm certificate. `HcellR_gap_of_certificate` reduces its spectral gap to producing a
completing-the-square pivot certificate `(p,e)`, discharging all the abstract engine plumbing. -/

lemma HcellR_sub_diag (jmax : ℕ) (lam : ℚ) (s : ℝ) (i : Fin (dim jmax)) :
    (HcellR jmax lam - s • 1) i i = (i.val * (i.val + 2)) / 4 - s := by
  have hHii : HcellR jmax lam i i = (i.val * (i.val + 2)) / 4 := by
    simp only [HcellR, Matrix.map_apply, Hcell, Matrix.of_apply, if_pos rfl]; push_cast; ring
  rw [Matrix.sub_apply, hHii, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]

lemma HcellR_sub_super (jmax : ℕ) (lam : ℚ) (s : ℝ) (i j : Fin (dim jmax)) (h : j.val = i.val + 1) :
    (HcellR jmax lam - s • 1) i j = -(lam : ℝ) := by
  have hij : i ≠ j := fun he => by rw [he] at h; omega
  have hHij : HcellR jmax lam i j = -(lam : ℝ) := by
    simp only [HcellR, Matrix.map_apply, Hcell, Matrix.of_apply, if_neg hij,
      if_pos (Or.inl h.symm), Rat.cast_neg]
  rw [Matrix.sub_apply, hHij, Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero, sub_zero]

lemma HcellR_sub_sub (jmax : ℕ) (lam : ℚ) (s : ℝ) (i j : Fin (dim jmax)) (h : i.val = j.val + 1) :
    (HcellR jmax lam - s • 1) i j = -(lam : ℝ) := by
  have hij : i ≠ j := fun he => by rw [he] at h; omega
  have hHij : HcellR jmax lam i j = -(lam : ℝ) := by
    simp only [HcellR, Matrix.map_apply, Hcell, Matrix.of_apply, if_neg hij,
      if_pos (Or.inr h.symm), Rat.cast_neg]
  rw [Matrix.sub_apply, hHij, Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero, sub_zero]

lemma HcellR_sub_far (jmax : ℕ) (lam : ℚ) (s : ℝ) (i j : Fin (dim jmax))
    (hij : i ≠ j) (h1 : i.val + 1 ≠ j.val) (h2 : j.val + 1 ≠ i.val) :
    (HcellR jmax lam - s • 1) i j = 0 := by
  have hHij : HcellR jmax lam i j = 0 := by
    simp only [HcellR, Matrix.map_apply, Hcell, Matrix.of_apply, if_neg hij,
      if_neg (not_or.mpr ⟨h1, h2⟩), Rat.cast_zero]
  rw [Matrix.sub_apply, hHij, Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero, sub_zero]

/-- **Physical cell gap from a pivot certificate.** For the SU(2) cell `HcellR jmax λ`, given a
completing-the-square certificate `(p,e)` for the shift `μ` — the recurrence `dᵢ−μ = pᵢ+eᵢ₊₁²pᵢ₊₁`
(`hrecD`), `−λ = eᵢ₊₁pᵢ₊₁` (`hrecO`) — with all pivots nonneg except at one index `m`, every
non-vacuum eigenvalue is `≥ λ_{i₀}+μ` (vacuum `HcellR 0 0 = 0`, `cell_exists_eigenvalue_le_zero`).
Reduces the physical cell gap to producing rational pivots — the remaining (numeric) certificate
work, no more abstract plumbing. -/
theorem HcellR_gap_of_certificate (jmax : ℕ) (lam : ℚ) (μ : ℝ) (hμ : 0 < μ)
    (p e : Fin (dim jmax) → ℝ) (m : Fin (dim jmax))
    (hp : ∀ k, k ≠ m → 0 ≤ p k)
    (hrecD : ∀ i : Fin (dim jmax),
      (i.val * (i.val + 2) : ℝ) / 4 - μ = p i + ∑ k, if k.val = i.val + 1 then e k * (p k * e k) else 0)
    (hrecO : ∀ i j : Fin (dim jmax), j.val = i.val + 1 → -(lam : ℝ) = e j * p j) :
    ∃ i₀, (HcellR_isHermitian jmax lam).eigenvalues i₀ ≤ 0 ∧
      ∀ i, i ≠ i₀ → (HcellR_isHermitian jmax lam).eigenvalues i₀ + μ
        ≤ (HcellR_isHermitian jmax lam).eigenvalues i := by
  obtain ⟨i₀, hi₀⟩ := cell_exists_eigenvalue_le_zero jmax lam
  refine ⟨i₀, hi₀, fun i hi => ?_⟩
  have hrec : HcellR jmax lam - μ • 1 = (Lbi e)ᵀ * Matrix.diagonal p * (Lbi e) :=
    tridiag_ldl_of_recurrence (fun i => (i.val * (i.val + 2) : ℝ) / 4 - μ) (fun _ => -(lam : ℝ)) p e _
      (fun i => HcellR_sub_diag jmax lam μ i)
      (fun i j h => HcellR_sub_super jmax lam μ i j h)
      (fun i j h => HcellR_sub_sub jmax lam μ i j h)
      (fun i j hij h1 h2 => HcellR_sub_far jmax lam μ i j hij h1 h2)
      hrecD hrecO
  exact gap_of_ldl_one_neg_pivot (HcellR_isHermitian jmax lam) hμ (Lbi e) p m hp hrec hi₀ hi

open Matrix in
/-- **Parametric reconstruction of the physical cell for general `jmax`.** Given that the backward
Sturm recurrence pivots `pivotSeq` (of the Casimir diagonal, shift `s`, coupling `λ`) are all nonzero,
`HcellR jmax λ − s•I` factors as `Lᵀ diag(pivotSeq) L` with the explicit recurrence pivots/multipliers.
This is the parametric counterpart of `HcellR_gap_of_certificate` — it supplies the certificate `(p,e)`
as *functions* of `(jmax,λ,s)`, reducing the physical cell gap to the pivot **sign analysis** (all
nonzero, and — for the gap — exactly one negative), the exact-rational Sturm computation. -/
theorem HcellR_reconstruction (jmax : ℕ) (lam : ℚ) (s : ℝ)
    (hnz : ∀ i, pivotSeq (fun i : Fin (dim jmax) => ((i.val : ℝ) * (i.val + 2)) / 4) s (lam:ℝ) i ≠ 0) :
    HcellR jmax lam - s • 1 =
      (Lbi (multSeq (fun i : Fin (dim jmax) => ((i.val : ℝ) * (i.val + 2)) / 4) s (lam:ℝ)))ᵀ *
        Matrix.diagonal (pivotSeq (fun i : Fin (dim jmax) => ((i.val : ℝ) * (i.val + 2)) / 4) s (lam:ℝ)) *
        (Lbi (multSeq (fun i : Fin (dim jmax) => ((i.val : ℝ) * (i.val + 2)) / 4) s (lam:ℝ))) := by
  apply tridiag_ldl_of_recurrence
    (fun i => ((i.val : ℝ) * (i.val + 2)) / 4 - s) (fun _ => -(lam:ℝ)) _ _ _
    (fun i => HcellR_sub_diag jmax lam s i)
    (fun i j h => HcellR_sub_super jmax lam s i j h)
    (fun i j h => HcellR_sub_sub jmax lam s i j h)
    (fun i j hij h1 h2 => HcellR_sub_far jmax lam s i j hij h1 h2)
    (pivotSeq_hrecD_sum _ s (lam:ℝ) hnz)
    (fun i j h => pivotSeq_hrecO _ s (lam:ℝ) hnz i j h)

/-- **Parametric physical-cell gap for general `jmax`, reduced to the pivot SIGN ANALYSIS.** For the
SU(2) cell `HcellR jmax λ`, if the backward Sturm pivots `pivotSeq` (Casimir diagonal, shift `μ`,
coupling `λ`) are all nonzero (`hnz`) with all but one index nonnegative (`hp`, the one-negative-pivot
Sturm condition), then every non-vacuum eigenvalue is `≥ λ_{i₀}+μ`. The certificate is supplied entirely
by the recurrence functions (`pivotSeq`/`multSeq` + the bridges); **the SOLE remaining content is the two
sign facts `hnz`/`hp` over the physical coupling range** — the exact-rational Sturm computation of
`small_volume_enclosure.py`. This is the precise terminal reduction of Step 5's cell gap. -/
theorem HcellR_gap_parametric (jmax : ℕ) (lam : ℚ) (μ : ℝ) (hμ : 0 < μ) (m : Fin (dim jmax))
    (hnz : ∀ i, pivotSeq (fun i : Fin (dim jmax) => ((i.val : ℝ) * (i.val + 2)) / 4) μ (lam:ℝ) i ≠ 0)
    (hp : ∀ k, k ≠ m →
      0 ≤ pivotSeq (fun i : Fin (dim jmax) => ((i.val : ℝ) * (i.val + 2)) / 4) μ (lam:ℝ) k) :
    ∃ i₀, (HcellR_isHermitian jmax lam).eigenvalues i₀ ≤ 0 ∧
      ∀ i, i ≠ i₀ → (HcellR_isHermitian jmax lam).eigenvalues i₀ + μ
        ≤ (HcellR_isHermitian jmax lam).eigenvalues i :=
  HcellR_gap_of_certificate jmax lam μ hμ
    (pivotSeq (fun i : Fin (dim jmax) => ((i.val : ℝ) * (i.val + 2)) / 4) μ (lam:ℝ))
    (multSeq (fun i : Fin (dim jmax) => ((i.val : ℝ) * (i.val + 2)) / 4) μ (lam:ℝ)) m hp
    (pivotSeq_hrecD_sum _ μ (lam:ℝ) hnz)
    (fun i j h => pivotSeq_hrecO _ μ (lam:ℝ) hnz i j h)

/-- **Fully parametric physical-cell gap demo (end-to-end validation of the parametric chain).** The
jmax=1 SU(2) cell at λ=1 has gap ≥ 1/2 (≥ κ₀), proved through `HcellR_gap_parametric` with the
certificate supplied ENTIRELY by the `pivotSeq` recurrence — `pivotSeq` evaluates (via its
`Fin.reverseInduction` computation rules) to `(19/10, −5/12, 3/2)`, one negative pivot at index 1 —
NOT hand-supplied. Confirms the parametric pivot construction produces a correct certificate. -/
theorem hcellR_gap_demo_param :
    ∃ i₀, (HcellR_isHermitian 1 1).eigenvalues i₀ ≤ 0 ∧
      ∀ i, i ≠ i₀ → (HcellR_isHermitian 1 1).eigenvalues i₀ + (1/2 : ℝ)
        ≤ (HcellR_isHermitian 1 1).eigenvalues i := by
  have pval : (pivotSeq (fun i : Fin (dim 1) => ((i.val : ℝ) * (i.val + 2)) / 4) (1/2) ((1:ℚ):ℝ) (0 : Fin 3) = 19/10)
      ∧ (pivotSeq (fun i : Fin (dim 1) => ((i.val : ℝ) * (i.val + 2)) / 4) (1/2) ((1:ℚ):ℝ) (1 : Fin 3) = -5/12)
      ∧ (pivotSeq (fun i : Fin (dim 1) => ((i.val : ℝ) * (i.val + 2)) / 4) (1/2) ((1:ℚ):ℝ) (2 : Fin 3) = 3/2) := by
    refine ⟨?_, ?_, ?_⟩
    · show pivotSeq _ (1/2) ((1:ℚ):ℝ) ((0 : Fin 2).castSucc) = 19/10
      rw [pivotSeq_castSucc, show ((0 : Fin 2).succ) = (1 : Fin 2).castSucc from rfl, pivotSeq_castSucc,
        show ((1 : Fin 2).succ) = Fin.last 2 from rfl, pivotSeq_last]
      norm_num [Fin.castSucc, Fin.last]
    · show pivotSeq _ (1/2) ((1:ℚ):ℝ) ((1 : Fin 2).castSucc) = -5/12
      rw [pivotSeq_castSucc, show ((1 : Fin 2).succ) = Fin.last 2 from rfl, pivotSeq_last]
      norm_num [Fin.castSucc, Fin.last]
    · show pivotSeq _ (1/2) ((1:ℚ):ℝ) (Fin.last 2) = 3/2
      rw [pivotSeq_last]; norm_num [Fin.last]
  obtain ⟨h0, h1, h2⟩ := pval
  refine HcellR_gap_parametric 1 1 (1/2) (by norm_num) 1 ?_ ?_
  · intro i; fin_cases i <;> simp_all <;> norm_num
  · intro k hk; fin_cases k <;> simp_all <;> norm_num

/-- **Concrete physical-cell gap via the certificate (non-vacuousness of `HcellR_gap_of_certificate`).**
The `jmax=1` SU(2) cell (3×3, `λ=1`, `H = [[0,−1,0],[−1,¾,−1],[0,−1,2]]`) has spectral gap `≥ ½ (≥ κ₀)`:
the forward-recurrence certificate `p=(19/10,−5/12,3/2)`, `e=(0,12/5,−2/3)` has exactly one negative
pivot (index 1) and satisfies the recurrence. Exercises the whole physical-cell reduction end to end. -/
theorem hcellR_gap_demo :
    ∃ i₀, (HcellR_isHermitian 1 1).eigenvalues i₀ ≤ 0 ∧
      ∀ i, i ≠ i₀ → (HcellR_isHermitian 1 1).eigenvalues i₀ + (1/2 : ℝ)
        ≤ (HcellR_isHermitian 1 1).eigenvalues i := by
  have hD : ∀ i : Fin (dim 1),
      (i.val * (i.val + 2) : ℝ) / 4 - (1/2) = ![19/10, -5/12, 3/2] i +
        ∑ k, if k.val = i.val + 1 then ![(0:ℝ), 12/5, -2/3] k *
          (![19/10, -5/12, 3/2] k * ![(0:ℝ), 12/5, -2/3] k) else 0 := by
    intro i; fin_cases i <;>
      simp only [dim, Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val, Fin.val_zero, Fin.val_one, Fin.val_two] <;> norm_num
  refine HcellR_gap_of_certificate 1 1 (1/2) (by norm_num)
    ![19/10, -5/12, 3/2] ![0, 12/5, -2/3] 1 ?_ hD ?_
  · intro k hk; fin_cases k <;> simp_all <;> norm_num
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all <;> norm_num

section RelGapDemo
open Matrix
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
/-- **Concrete RELATIVE-gap demo (large-λ regime, non-vacuousness of `gap_of_ldl_one_neg_pivot_rel`).**
The `jmax=2` SU(2) cell at `λ=3` (5×5) has TWO eigenvalues below `κ₀` (`E₀≈−3.73`, `E₁≈−0.53`) — the
ABSOLUTE lemma (`gap_of_ldl_one_neg_pivot`) fails — yet its gap `≥ κ₀`, proved through the relative
toolchain: the trial state `ψ=(3/4,1,3/4,1/4,0)` gives `E₀ ≤ −2−κ₀` (`exists_eigenvalue_le_of_form`,
`⟨ψ,Hψ⟩=−513/64 ≤ (−5/2)‖ψ‖²`, bridged via `κ₀≤½`), and the Sturm shift `t=−2` certificate `(p,e)`
(one negative pivot at index 1) gives `E₁ ≥ −2` (`gap_of_ldl_one_neg_pivot_rel`). The rational
certificate is machine-generated + exact-verified. An `HcellR jmax λ = !![…]`
bridge (`fin_cases` on entries) makes the concrete 5×5 forms compute over `Fin 5`. -/
theorem hcellR_rel_gap_demo :
    ∃ i₀, ∀ i, i ≠ i₀ →
      (HcellR_isHermitian 2 3).eigenvalues i₀ + κ₀YM ≤ (HcellR_isHermitian 2 3).eigenvalues i := by
  have hbridge : HcellR 2 3 = (!![(0:ℝ), -3, 0, 0, 0; -3, 3/4, -3, 0, 0; 0, -3, 2, -3, 0;
      0, 0, -3, 15/4, -3; 0, 0, 0, -3, 6] : Matrix (Fin 5) (Fin 5) ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [HcellR, Hcell, Matrix.map_apply, Matrix.of_apply] <;> norm_num
  have hψ0 : (![3/4, 1, 3/4, 1/4, 0] : Fin (dim 2) → ℝ) ≠ 0 := by
    intro hc; have h1 := congrFun hc 1
    simp [Matrix.cons_val_one, Matrix.head_cons] at h1
  have hE0 : ∃ i₀, (HcellR_isHermitian 2 3).eigenvalues i₀ ≤ -2 - κ₀YM := by
    refine exists_eigenvalue_le_of_form (HcellR_isHermitian 2 3) hψ0 ?_
    rw [hbridge]
    show (![3/4, 1, 3/4, 1/4, 0] : Fin 5 → ℝ) ⬝ᵥ
        ((!![(0:ℝ), -3, 0, 0, 0; -3, 3/4, -3, 0, 0; 0, -3, 2, -3, 0; 0, 0, -3, 15/4, -3;
             0, 0, 0, -3, 6]) *ᵥ ![3/4, 1, 3/4, 1/4, 0])
        ≤ (-2 - κ₀YM) * ((![3/4, 1, 3/4, 1/4, 0] : Fin 5 → ℝ) ⬝ᵥ ![3/4, 1, 3/4, 1/4, 0])
    simp [dotProduct, mulVec, Fin.sum_univ_five, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue]
    nlinarith [κ₀YM_le_half, κ₀YM_pos]
  obtain ⟨i₀, hi₀⟩ := hE0
  refine ⟨i₀, fun i hi => ?_⟩
  have hD : ∀ i : Fin (dim 2), (i.val * (i.val + 2) : ℝ) / 4 - (-2) =
      ![233/31, -31/19, 76/37, 37/8, 8] i + ∑ k, if k.val = i.val + 1 then
        ![(0:ℝ), 57/31, -111/76, -24/37, -3/8] k *
          (![233/31, -31/19, 76/37, 37/8, 8] k * ![(0:ℝ), 57/31, -111/76, -24/37, -3/8] k) else 0 := by
    intro i; fin_cases i <;>
      simp only [dim, Fin.sum_univ_five, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val, Fin.val_zero, Fin.val_one, Fin.val_two] <;> norm_num
  have hO : ∀ i j : Fin (dim 2), j.val = i.val + 1 →
      -((3:ℚ):ℝ) = ![(0:ℝ), 57/31, -111/76, -24/37, -3/8] j * ![233/31, -31/19, 76/37, 37/8, 8] j := by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all <;> norm_num
  have hrec : HcellR 2 3 - (-2 : ℝ) • 1 =
      (Lbi ![(0:ℝ), 57/31, -111/76, -24/37, -3/8])ᵀ *
        Matrix.diagonal ![233/31, -31/19, 76/37, 37/8, 8] * (Lbi ![(0:ℝ), 57/31, -111/76, -24/37, -3/8]) :=
    tridiag_ldl_of_recurrence (fun i => (i.val * (i.val + 2) : ℝ) / 4 - (-2)) (fun _ => -((3:ℚ):ℝ))
      ![233/31, -31/19, 76/37, 37/8, 8] ![(0:ℝ), 57/31, -111/76, -24/37, -3/8] _
      (fun i => HcellR_sub_diag 2 3 (-2) i)
      (fun i j h => HcellR_sub_super 2 3 (-2) i j h)
      (fun i j h => HcellR_sub_sub 2 3 (-2) i j h)
      (fun i j hij h1 h2 => HcellR_sub_far 2 3 (-2) i j hij h1 h2)
      hD hO
  have hp : ∀ k, k ≠ (1 : Fin (dim 2)) → 0 ≤ (![233/31, -31/19, 76/37, 37/8, 8] : Fin (dim 2) → ℝ) k := by
    intro k hk; fin_cases k <;> simp_all <;> norm_num
  exact gap_of_ldl_one_neg_pivot_rel (HcellR_isHermitian 2 3) κ₀YM_pos
    (Lbi ![(0:ℝ), 57/31, -111/76, -24/37, -3/8]) ![233/31, -31/19, 76/37, 37/8, 8] 1 hp hrec hi₀ hi

end RelGapDemo

/-! ### The physically dominant two-state gauge cell — a complete, all-λ, axiom-free gap

The minimal character truncation `j ∈ {0, ½}` of the single plaquette is `M(λ) = [[0, −λ], [−λ, ¾]]`.
Here the count-lemma pipeline closes for **every** `λ`: on the line `W = ℝ·e₁` the Rayleigh quotient is
`M₁₁ = ¾ ≥ κ₀`, and `M₀₀ = 0` gives a ground state `≤ 0`, so `eigenvalues_gap_of_codim1_form` forces the
other eigenvalue `≥ κ₀` above the ground — the cell gap `≥ κ₀`, hence `m_cell = e^{−gap} ≤ 3^{−1/4} < 1`. -/

/-- The two-state gauge cell `M(λ) = [[0, −λ], [−λ, ¾]]` (characters `j = 0, ½`). -/
noncomputable def Hcell2 (lam : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, -lam; -lam, 3/4]

theorem Hcell2_isHermitian (lam : ℝ) : (Hcell2 lam).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Hcell2, Matrix.conjTranspose_apply]

theorem Hcell2_zero_zero (lam : ℝ) : Hcell2 lam 0 0 = 0 := by simp [Hcell2]

/-- On the excited line `W = ℝ·e₁`, the cell's quadratic form is `¾·‖·‖² ≥ κ₀·‖·‖²`. -/
theorem Hcell2_form_on_line (lam : ℝ) (x : Fin 2 → ℝ)
    (hx : x ∈ Submodule.span ℝ {Pi.single (1 : Fin 2) (1 : ℝ)}) :
    κ₀YM * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Hcell2 lam *ᵥ x) := by
  rw [Submodule.mem_span_singleton] at hx
  obtain ⟨c, rfl⟩ := hx
  have hx0 : (c • Pi.single (1 : Fin 2) (1 : ℝ)) 0 = 0 := by
    rw [Pi.smul_apply, Pi.single_eq_of_ne (by decide), smul_zero]
  have hx1 : (c • Pi.single (1 : Fin 2) (1 : ℝ)) 1 = c := by
    rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  have hk : κ₀YM ≤ 3 / 4 := le_trans κ₀YM_le_half (by norm_num)
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, hx0, hx1, Hcell2,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply]
  nlinarith [sq_nonneg c, hk]

/-- **The two-state cell has a spectral gap `≥ κ₀`, for every coupling `λ`.** There is a ground index `i₀`
(eigenvalue `≤ 0`) such that the other eigenvalue exceeds it by at least `κ₀`. Complete and axiom-free —
it consumes only `eigenvalues_gap_of_codim1_form` and the explicit `¾`-line bound. -/
theorem Hcell2_gap (lam : ℝ) : ∃ i₀ : Fin 2, ∀ i : Fin 2, i ≠ i₀ →
    κ₀YM ≤ (Hcell2_isHermitian lam).eigenvalues i - (Hcell2_isHermitian lam).eigenvalues i₀ := by
  obtain ⟨i₀, hi₀⟩ :=
    exists_eigenvalue_le_zero_of_diag (Hcell2_isHermitian lam) 0 (Hcell2_zero_zero lam)
  refine ⟨i₀, fun i hi => ?_⟩
  set e : Fin 2 → ℝ := Pi.single 1 1 with he
  have hv : e ≠ 0 := by
    have hsame : e 1 = 1 := by rw [he]; simp
    intro hcontra
    rw [hcontra] at hsame
    simp at hsame
  have hWdim : Module.finrank ℝ (Submodule.span ℝ {e}) = 1 := finrank_span_singleton hv
  have hW : (2 : ℕ) ≤ Module.finrank ℝ (Submodule.span ℝ {e}) + 1 := by omega
  have hbound := eigenvalues_gap_of_codim1_form (Hcell2_isHermitian lam) κ₀YM_pos
    (Submodule.span ℝ {e}) hW (Hcell2_form_on_line lam) hi₀ hi
  linarith

/-- **The two-state cell magnitude clears the entropy floor, at every coupling.** `m_cell = e^{−gap} ≤
3^{−1/4} < 1` for all `λ` — the F-independent radius the volume argument consumes, here fully in Lean. -/
theorem Hcell2_clears_floor (lam : ℝ) : ∃ i₀ : Fin 2, ∀ i : Fin 2, i ≠ i₀ →
    Real.exp (-((Hcell2_isHermitian lam).eigenvalues i - (Hcell2_isHermitian lam).eigenvalues i₀))
      ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
  obtain ⟨i₀, h⟩ := Hcell2_gap lam
  exact ⟨i₀, fun i hi => cell_clears_floor (h i hi)⟩

/-! ### The three-state cell — the pipeline on a genuine multi-state KS truncation

`HcellR` at `jmax = 1` (characters `j = 0, ½, 1`) is `M₃(λ) = [[0,−λ,0],[−λ,¾,−λ],[0,−λ,2]]`. Here the
codim-1 subspace is the plane `W = span{e₁, e₂}`, on which the form is the `2×2` quadratic
`(¾)a² − 2λ·ab + 2b²`; it clears `κ₀‖·‖²` exactly when `λ² ≤ (¾−κ₀)(2−κ₀)` (the plane-form PSD threshold,
a genuine λ-window, not just `λ = 0`). With `M₃₀₀ = 0` giving a ground `≤ 0`, `eigenvalues_gap_of_codim1_form`
then yields the cell gap `≥ κ₀`, showing the count→gap method scales past the `2×2` case. -/

/-- Reusable: the span of two linearly independent vectors in `Fin N → ℝ` has dimension `2`. -/
theorem finrank_span_pair_eq_two {N : ℕ} {u v : Fin N → ℝ}
    (h : LinearIndependent ℝ ![u, v]) : Module.finrank ℝ (Submodule.span ℝ {u, v}) = 2 := by
  have hset : (Set.range ![u, v]) = ({u, v} : Set (Fin N → ℝ)) := by
    ext y
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, rfl⟩; fin_cases k <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  rw [← hset, finrank_span_eq_card h, Fintype.card_fin]

/-- The three-state gauge cell `M₃(λ)` (characters `j = 0, ½, 1`; Casimir `0, ¾, 2`). -/
noncomputable def Hcell3 (lam : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -lam, 0; -lam, 3 / 4, -lam; 0, -lam, 2]

theorem Hcell3_isHermitian (lam : ℝ) : (Hcell3 lam).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Hcell3, Matrix.conjTranspose_apply]

theorem Hcell3_zero_zero (lam : ℝ) : Hcell3 lam 0 0 = 0 := by simp [Hcell3]

/-- On the excited plane `W = span{e₁, e₂}`, the cell form clears `κ₀‖·‖²` when `λ² ≤ (¾−κ₀)(2−κ₀)`. -/
theorem Hcell3_form_on_plane (lam : ℝ) (hlam : lam ^ 2 ≤ (3 / 4 - κ₀YM) * (2 - κ₀YM))
    (x : Fin 3 → ℝ)
    (hx : x ∈ Submodule.span ℝ {Pi.single (1 : Fin 3) (1 : ℝ), Pi.single (2 : Fin 3) (1 : ℝ)}) :
    κ₀YM * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Hcell3 lam *ᵥ x) := by
  rw [Submodule.mem_span_pair] at hx
  obtain ⟨a, b, rfl⟩ := hx
  have c0 : (a • Pi.single (1 : Fin 3) (1 : ℝ) + b • Pi.single (2 : Fin 3) (1 : ℝ) : Fin 3 → ℝ) 0
      = 0 := by simp [Pi.single_apply]
  have c1 : (a • Pi.single (1 : Fin 3) (1 : ℝ) + b • Pi.single (2 : Fin 3) (1 : ℝ) : Fin 3 → ℝ) 1
      = a := by simp [Pi.single_apply]
  have c2 : (a • Pi.single (1 : Fin 3) (1 : ℝ) + b • Pi.single (2 : Fin 3) (1 : ℝ) : Fin 3 → ℝ) 2
      = b := by simp [Pi.single_apply]
  have hc : (0 : ℝ) < 3 / 4 - κ₀YM := by have := κ₀YM_le_half; linarith
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, c0, c1, c2, Hcell3, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  nlinarith [sq_nonneg ((3 / 4 - κ₀YM) * a - lam * b),
    mul_nonneg (sub_nonneg.mpr hlam) (sq_nonneg b), hc, sq_nonneg a, sq_nonneg b]

/-- **The three-state cell has a spectral gap `≥ κ₀`** whenever `λ² ≤ (¾−κ₀)(2−κ₀)`: some ground index `i₀`
(eigenvalue `≤ 0`) with every other eigenvalue at least `κ₀` above it. Axiom-free; the count→gap pipeline
on a real multi-state Kogut–Susskind truncation. -/
theorem Hcell3_gap (lam : ℝ) (hlam : lam ^ 2 ≤ (3 / 4 - κ₀YM) * (2 - κ₀YM)) :
    ∃ i₀ : Fin 3, ∀ i : Fin 3, i ≠ i₀ →
    κ₀YM ≤ (Hcell3_isHermitian lam).eigenvalues i - (Hcell3_isHermitian lam).eigenvalues i₀ := by
  obtain ⟨i₀, hi₀⟩ :=
    exists_eigenvalue_le_zero_of_diag (Hcell3_isHermitian lam) 0 (Hcell3_zero_zero lam)
  refine ⟨i₀, fun i hi => ?_⟩
  set e1 : Fin 3 → ℝ := Pi.single 1 1 with he1
  set e2 : Fin 3 → ℝ := Pi.single 2 1 with he2
  have hpair : LinearIndependent ℝ ![e1, e2] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [he1, he2] at hst
    have h1 := congrFun hst 1
    have h2 := congrFun hst 2
    simp [Pi.single_apply] at h1 h2
    exact ⟨h1, h2⟩
  have hdim : Module.finrank ℝ (Submodule.span ℝ {e1, e2}) = 2 := finrank_span_pair_eq_two hpair
  have hW : (3 : ℕ) ≤ Module.finrank ℝ (Submodule.span ℝ {e1, e2}) + 1 := by omega
  have hbound := eigenvalues_gap_of_codim1_form (Hcell3_isHermitian lam) κ₀YM_pos
    (Submodule.span ℝ {e1, e2}) hW (Hcell3_form_on_plane lam hlam) hi₀ hi
  linarith

/-- **The three-state cell magnitude clears the entropy floor** on its coupling window: `m_cell = e^{−gap}
≤ 3^{−1/4} < 1` whenever `λ² ≤ (¾−κ₀)(2−κ₀)`. -/
theorem Hcell3_clears_floor (lam : ℝ) (hlam : lam ^ 2 ≤ (3 / 4 - κ₀YM) * (2 - κ₀YM)) :
    ∃ i₀ : Fin 3, ∀ i : Fin 3, i ≠ i₀ →
    Real.exp (-((Hcell3_isHermitian lam).eigenvalues i - (Hcell3_isHermitian lam).eigenvalues i₀))
      ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
  obtain ⟨i₀, h⟩ := Hcell3_gap lam hlam
  exact ⟨i₀, fun i hi => cell_clears_floor (h i hi)⟩

/-! ### The volume-uniform gap from the single-cell ceiling

`gap_uniform_in_volume_of_intensive` (`Certify`) gives the F-uniform gap from `∀F, m_hi(F) ≤ r`, `r < 1`.
`Hcell2_clears_floor` supplies the value `r = 3^{−1/4} = e^{−κ₀}`. The intensive input `m_hi(F) ≤ 3^{−1/4}` is the
measured continuum read (`data/8_7_dat_mhi_lscan.csv`). -/

/-- The single-cell entropy-floor ceiling `3^{-1/4} = e^{-κ₀}` is strictly below one. -/
theorem cell_ceiling_lt_one : (3 : ℝ) ^ (-(1 : ℝ) / 4) < 1 := by
  apply Real.rpow_lt_one_of_one_lt_of_neg <;> norm_num

/-- **The volume-uniform gap with the radius from the machine-checked single-cell ceiling.** For any physical mode
family `(P, μ)` with dominant transfer magnitude `mHi F ≤ 3^{−1/4}` at every volume `F`, a single rate `κ > 0`
makes every volume's correlator forget. Composes the cell ceiling (`Hcell2_clears_floor`) with
`gap_uniform_in_volume_of_intensive`. The input `hint` (`m_hi(F) ≤ 3^{−1/4}`) is the measured continuum read.
Foundational axioms only. -/
theorem gap_uniform_of_cell_intensive {ι : Type*}
    (s : ℕ → Finset ι) (P μ : ℕ → ι → ℂ) (mHi : ℕ → ℝ)
    (hint : ∀ F, mHi F ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4))
    (hdom : ∀ F, ∀ k ∈ s F, ‖μ F k‖ ≤ mHi F) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ F,
      Filter.Tendsto (fun τ => ‖∑ k ∈ s F, P F k * (μ F k) ^ τ‖) Filter.atTop (nhds 0) :=
  gap_uniform_in_volume_of_intensive s P μ mHi ((3 : ℝ) ^ (-(1 : ℝ) / 4))
    (by positivity) cell_ceiling_lt_one hint hdom

/-! ### The read margin from the single-cell gap

`Margin.margin_of_contraction` gives the read margin `e^{−Δ} ≤ e^{−(κ₀−μ)}` when `Δ ≥ κ₀−μ`. `Hcell2_gap` gives
`Δ_cell ≥ κ₀`, so with `μ ≥ 0`, `Δ_cell ≥ κ₀ ≥ κ₀−μ` gives the single-cell read margin. -/

/-- **The read margin from a gap at least the floor.** The `Margin.margin_of_contraction` conclusion
`e^{−Δ} ≤ e^{−(κ₀−μ)}` from `κ₀ ≤ Δ` and `μ ≥ 0`. -/
theorem read_margin_of_gap_ge_floor {Δ μ : ℝ} (hμ : 0 ≤ μ) (hΔ : κ₀YM ≤ Δ) :
    Real.exp (-Δ) ≤ Real.exp (-(κ₀YM - μ)) :=
  Real.exp_le_exp.mpr (by linarith)

/-- **The single-cell read margin, via `Hcell2_gap`.** For every coupling `λ` and every `μ ≥ 0`, the two-state
cell's transfer magnitude `e^{−gap}` clears the free-energy-floor margin `e^{−(κ₀−μ)}` (the `hread` content
consumed by `Complete.gap_of_confinement`), with the gap supplied by `Hcell2_gap` (`Δ_cell ≥ κ₀`). -/
theorem Hcell2_read_margin (lam : ℝ) {μ : ℝ} (hμ : 0 ≤ μ) :
    ∃ i₀ : Fin 2, ∀ i : Fin 2, i ≠ i₀ →
    Real.exp (-((Hcell2_isHermitian lam).eigenvalues i - (Hcell2_isHermitian lam).eigenvalues i₀))
      ≤ Real.exp (-(κ₀YM - μ)) := by
  obtain ⟨i₀, h⟩ := Hcell2_gap lam
  exact ⟨i₀, fun i hi => read_margin_of_gap_ge_floor hμ (h i hi)⟩

/-! ### The volume-uniform gap from the single cell (S1 wired to `Hcell2`)

`Mixing.gap_of_maximal_correlation` (S1): reflection positivity makes the Euclidean-time transfer operator
self-adjoint, so `ρ'(n) = ρ'(1)^n`, and a single `ρ'(1) < 1` sends the correlator to zero over every separation
and every volume. `Hcell2_gap` supplies `ρ'(1) = e^{−Δ_cell} < 1` (`cell_lt_one`); `gap_uniform_of_cell` composes
them. The intensive input `m_hi(F) = ρ'(1)(F) ≤ 3^{−1/4}` is the measured continuum read
(`data/8_7_dat_mhi_lscan.csv`). -/

/-- **The volume-uniform gap from the single-cell magnitude (S1 wired to `Hcell2`).** For a reach-freeze excess
`σ` with `σ n ≤ σ 0 · ρ'(1)^n` at the machine-checked cell value `ρ'(1) = e^{−Δ_cell} < 1` (`Hcell2_gap` ⇒
`cell_lt_one`), the excess tends to zero. -/
theorem gap_uniform_of_cell {σ : ℕ → ℝ} {lam : ℝ} {i₀ i : Fin 2}
    (hgap : κ₀YM ≤ (Hcell2_isHermitian lam).eigenvalues i - (Hcell2_isHermitian lam).eigenvalues i₀)
    (hσnn : ∀ n, 0 ≤ σ n)
    (hsub : ∀ n, σ n ≤ σ 0 *
      (Real.exp (-((Hcell2_isHermitian lam).eigenvalues i - (Hcell2_isHermitian lam).eigenvalues i₀))) ^ n) :
    Filter.Tendsto σ Filter.atTop (nhds 0) :=
  gap_of_maximal_correlation (Real.exp_nonneg _) (cell_lt_one hgap) hσnn hsub

/-- **Capstone: the SU(N) witness volume-uniform gap, radius grounded in the machine-checked single cell.**
Instantiates `gap_uniform_of_cell_intensive` on the concrete YM transfer modes: the dominant magnitude
`mHiYM = 1/5` clears the single-plaquette ceiling `3^{−1/4}` that `Hcell2_clears_floor` proves machine-checked, so
a single rate `κ > 0` makes every volume's witness correlator forget — the U2 reduction, in one statement, on the
actual modes, with the radius supplied by the machine-checked cell. Foundational axioms only. The physical
intensivity `m_hi(F) ≤ 3^{−1/4}` is the measured input (see `data/8_7_dat_mhi_lscan.csv`). -/
theorem ym_volume_gap_cell_grounded (β : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ F : ℕ,
      Filter.Tendsto (fun τ => ‖∑ k, PModeYM β k * (mModeYM β k) ^ τ‖) Filter.atTop (nhds 0) := by
  have hpos : (0 : ℝ) ≤ mHiYM := by unfold mHiYM; norm_num
  have hceil : mHiYM ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
    have h := ym_aperture_margin 0 le_rfl (0 : Fin (nModeYM + 1))
    rwa [mModeYM, Complex.norm_of_nonneg hpos] at h
  exact gap_uniform_of_cell_intensive (fun _ => Finset.univ) (fun _ => PModeYM β)
    (fun _ => mModeYM β) (fun _ => mHiYM) (fun _ => hceil)
    (fun _ k _ => by rw [mModeYM]; exact le_of_eq (Complex.norm_of_nonneg hpos))

/-! ### The intensive margin is EXACT for a product of cells (steps 1+2, product model)

The physical intensive input `∀F, m_hi(F) ≤ 3^{−1/4}` (the hypothesis of `gap_uniform_of_cell_intensive`) is,
for the physical opaque `wilsonCorr`, a measured continuum read. For the DECOUPLED (product) transfer it is
instead PROVED here, foundation-only: the eigenvalues of an `F`-cell product are products `∏ λᵢ` of cell
eigenvalues, the vacuum is all-cells-at-`1`, and any sub-vacuum product carries a factor `≤ 3^{−1/4}` (the
machine-checked single-cell ceiling, `Hcell2_clears_floor`) with the rest `≤ 1`, so it is `≤ 3^{−1/4}` —
UNIFORMLY in the cell count `F`. Adding volume contributes vacuum factors `1`, not growth: the dominant
magnitude stays at the single-plaquette ceiling. This is the intensive-margin mechanism, proved for the product
structure; the physical coupled transfer's correction to the product is the genuine residual of steps 1+2. -/

/-- **Product bound.** A product of factors in `[0,1]` with at least one factor `≤ mc` (`0 ≤ mc`) is `≤ mc`. -/
theorem product_subvacuum_le {F : ℕ} (lam : Fin F → ℝ) {mc : ℝ} (hmc : 0 ≤ mc)
    (h01 : ∀ i, 0 ≤ lam i ∧ lam i ≤ 1) (j : Fin F) (hj : lam j ≤ mc) :
    ∏ i, lam i ≤ mc := by
  classical
  rw [← Finset.prod_erase_mul Finset.univ lam (Finset.mem_univ j)]
  have htail_le1 : ∏ i ∈ Finset.univ.erase j, lam i ≤ 1 :=
    Finset.prod_le_one (fun i _ => (h01 i).1) (fun i _ => (h01 i).2)
  calc (∏ i ∈ Finset.univ.erase j, lam i) * lam j
      ≤ 1 * mc := mul_le_mul htail_le1 hj (h01 j).1 (by norm_num)
    _ = mc := one_mul mc

/-- **The intensive margin holds for a product of cells at the single-cell ceiling, uniformly in `F`.** Any
sub-vacuum configuration of an `F`-cell product (some cell `j` at `λⱼ ≤ 3^{−1/4}`, all cells in `[0,1]`) has
product magnitude `≤ 3^{−1/4}`. So the intensive input `hint` of `gap_uniform_of_cell_intensive` is PROVED —
not measured — for the product model, foundation-only, at the machine-checked cell ceiling. -/
theorem product_margin_le_cell_ceiling {F : ℕ} (lam : Fin F → ℝ)
    (h01 : ∀ i, 0 ≤ lam i ∧ lam i ≤ 1) (j : Fin F) (hj : lam j ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    ∏ i, lam i ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4) :=
  product_subvacuum_le lam (by positivity) h01 j hj

/-- **Volume-uniform gap on the genuine product-of-cells spectrum — intensive margin DERIVED (not the
placeholder witness).** A mode family whose every active mode `μ F k` (for `k ∈ s F`) is a product
`∏ᵢ (fac F k i)` of per-cell magnitudes in `[0,1]` with at least one cell excited
(`fac F k j ≤ 3^{−1/4}`, the machine-checked single-cell ceiling `Hcell2_clears_floor`) has dominant
magnitude `≤ 3^{−1/4}` UNIFORMLY in the volume `F` (`product_subvacuum_le`), so one rate `κ > 0` makes every
volume's connected correlator forget. Unlike `ym_volume_gap_cell_grounded` (constant witness
`mModeYM ≡ 1/5`), the magnitude here is the actual product-of-cells spectrum and the intensive input of
`gap_uniform_of_cell_intensive` is PROVED, not measured/placeholder. Foundational axioms only. This is the
DECOUPLED transfer; the physical coupled-cell correction is the residual (steps 1+2 / step 3). -/
theorem product_volume_gap {ι : Type*} {ncell : ℕ → ℕ}
    (s : ℕ → Finset ι) (P μ : ℕ → ι → ℂ) (fac : ∀ F, ι → Fin (ncell F) → ℝ)
    (h01 : ∀ F, ∀ k ∈ s F, ∀ i, 0 ≤ fac F k i ∧ fac F k i ≤ 1)
    (hexc : ∀ F, ∀ k ∈ s F, ∃ j, fac F k j ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4))
    (hμ : ∀ F, ∀ k ∈ s F, μ F k = ((∏ i, fac F k i : ℝ) : ℂ)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ F,
      Filter.Tendsto (fun τ => ‖∑ k ∈ s F, P F k * (μ F k) ^ τ‖) Filter.atTop (nhds 0) := by
  refine gap_uniform_of_cell_intensive s P μ (fun _ => (3 : ℝ) ^ (-(1 : ℝ) / 4))
    (fun _ => le_refl _) (fun F k hk => ?_)
  rw [hμ F k hk, Complex.norm_of_nonneg (Finset.prod_nonneg (fun i _ => (h01 F k hk i).1))]
  obtain ⟨j, hj⟩ := hexc F k hk
  exact product_subvacuum_le (fac F k) (by positivity) (fun i => h01 F k hk i) j hj

/-- Per-cell factor of the extremal product: cell `0` at the machine-checked ceiling `3^{−1/4}`, the rest at
the vacuum `1` — the worst-case product of `diag(1, 3^{−1/4})` cells (`Hcell2_clears_floor`/`GappedExample`). -/
noncomputable def ceilFac (F : ℕ) (i : Fin (F + 1)) : ℝ :=
  if i = 0 then (3 : ℝ) ^ (-(1 : ℝ) / 4) else 1

theorem ceilFac_mem (F : ℕ) (i : Fin (F + 1)) : 0 ≤ ceilFac F i ∧ ceilFac F i ≤ 1 := by
  unfold ceilFac
  split
  · exact ⟨by positivity, le_of_lt cell_ceiling_lt_one⟩
  · exact ⟨by norm_num, le_refl 1⟩

/-- **`product_volume_gap` is non-vacuous — a concrete constructed product model.** The `F`-cell product where
one cell sits at the machine-checked single-cell ceiling `3^{−1/4}` and the rest at the vacuum `1` — the
extremal product of `diag(1, 3^{−1/4})` cells — has a volume-uniform gap, uniform in the cell count `F`.
A genuine constructed spectrum (not the `mModeYM ≡ 1/5` placeholder), foundational axioms only. -/
theorem product_volume_gap_concrete :
    ∃ κ : ℝ, 0 < κ ∧ ∀ F : ℕ, Filter.Tendsto
      (fun τ => ‖∑ _ : Unit, (1 : ℂ) * (((∏ i, ceilFac F i : ℝ)) : ℂ) ^ τ‖) Filter.atTop (nhds 0) :=
  product_volume_gap (ι := Unit) (ncell := fun F => F + 1) (fun _ => Finset.univ) (fun _ _ => 1)
    (fun F _ => (((∏ i, ceilFac F i : ℝ)) : ℂ)) (fun F _ i => ceilFac F i)
    (fun F _ _ i => ceilFac_mem F i) (fun F _ _ => ⟨0, by simp [ceilFac]⟩) (fun _ _ _ => rfl)

/-! ### (b) The interacting volume gap reduces to a coupling bound

The physical transfer is the decoupled product `H₀` PLUS an inter-cell coupling `V`. The corank-1 form
machinery (`eigenvalues_gap_of_codim1_form`) is dimension-general, so the coupled gap follows from a form
bound on `H = H₀ + V`. Splitting the form, the coupled gap `≥ κ₀` reduces to: the product form clears the
margin `κ₀ + c` on the excited subspace `W` (the single cell gives this — cell gap `≥ ¾ > κ₀`, margin up to
`¾ − κ₀`), and the coupling form is bounded below by `−c`. So the interacting volume gap is reduced to ONE
deterministic coupling bound. -/

/-- **The interacting-cell gap from a coupling bound (first step of the interacting construction).** For a
Hermitian volume Hamiltonian `H = H₀ + V` (`H₀` the decoupled product, `V` the inter-cell coupling), if on
the corank-1 excited subspace `W` the decoupled form clears the margin `κ₀ + c` (`hform0`) and the coupling
form is bounded below by `−c` (`hformV`), then with a vacuum ground (`hi₀`) the coupled spectral gap is
`≥ κ₀`: every excited eigenvalue is at least `κ₀` above the ground. The interacting volume gap is thereby
reduced to the single coupling bound `V`-form `≥ −c` at a margin `c` the cell gap supplies. Foundation-only
(composes `eigenvalues_gap_of_codim1_form`); the residual is the physical coupling bound. -/
theorem coupled_gap_of_coupling_bound {N : ℕ} (H₀ V : Matrix (Fin N) (Fin N) ℝ)
    (hH : (H₀ + V).IsHermitian) {c : ℝ}
    (W : Submodule ℝ (Fin N → ℝ)) (hW : N ≤ Module.finrank ℝ W + 1)
    (hform0 : ∀ x ∈ W, (κ₀YM + c) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (H₀ *ᵥ x))
    (hformV : ∀ x ∈ W, (-c) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (V *ᵥ x))
    (i₀ : Fin N) (hi₀ : hH.eigenvalues i₀ ≤ 0) :
    ∀ i : Fin N, i ≠ i₀ → κ₀YM ≤ hH.eigenvalues i - hH.eigenvalues i₀ := by
  intro i hi
  have hform : ∀ x ∈ W, κ₀YM * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((H₀ + V) *ᵥ x) := by
    intro x hx
    have hsplit : x ⬝ᵥ ((H₀ + V) *ᵥ x) = x ⬝ᵥ (H₀ *ᵥ x) + x ⬝ᵥ (V *ᵥ x) := by
      rw [Matrix.add_mulVec, dotProduct_add]
    have hkey : (κ₀YM + c) * (x ⬝ᵥ x) + (-c) * (x ⬝ᵥ x) = κ₀YM * (x ⬝ᵥ x) := by ring
    rw [hsplit]
    linarith [hform0 x hx, hformV x hx, hkey]
  have hbound := eigenvalues_gap_of_codim1_form hH κ₀YM_pos W hW hform hi₀ hi
  linarith

/-- **(b-i) The decoupled product form margin.** A diagonal Hamiltonian `D = diagonal d` with vacuum at
coordinate `i₀` (`x i₀ = 0` on the excited subspace) and every excited energy `d i ≥ m` (`i ≠ i₀`) clears the
form margin `m`: `m·(x ⬝ᵥ x) ≤ x ⬝ᵥ (D *ᵥ x)` for every `x` vanishing at `i₀`. For the decoupled `F`-cell
product the excited energies are the Casimir sums, `≥ ¾` for the two-state cell (`twoState_gap_clears_floor`),
so `m = ¾ = κ₀ + (¾ − κ₀)` — the margin `coupled_gap_of_coupling_bound` consumes. Foundation-only. -/
theorem diag_form_margin {N : ℕ} (d : Fin N → ℝ) (i₀ : Fin N) {m : ℝ}
    (hexc : ∀ i, i ≠ i₀ → m ≤ d i) (x : Fin N → ℝ) (hx : x i₀ = 0) :
    m * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Matrix.diagonal d *ᵥ x) := by
  simp only [dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Matrix.mulVec_diagonal]
  by_cases h : i = i₀
  · subst h; rw [hx]; simp
  · nlinarith [mul_self_nonneg (x i), hexc i h]

/-- **(b-ii) The inter-cell coupling form bound (Gershgorin / AM-GM).** A symmetric coupling matrix `V` with
bounded row sums, `∑ⱼ |V i j| ≤ c` for every row `i`, has form bounded below: `−c·(x ⬝ᵥ x) ≤ x ⬝ᵥ (V *ᵥ x)`.
So a coupling of bounded strength clears the `hformV` hypothesis of `coupled_gap_of_coupling_bound` with that
`c`; the interacting gap `≥ κ₀` then holds whenever `c ≤ ¾ − κ₀` (the cell Casimir margin, `diag_form_margin`).
Foundation-only (AM-GM `2|xᵢxⱼ| ≤ xᵢ²+xⱼ²`, symmetrised over the coupling matrix). -/
theorem coupling_form_lower {N : ℕ} (V : Matrix (Fin N) (Fin N) ℝ) {c : ℝ}
    (hsymm : ∀ i j, V i j = V j i) (hrow : ∀ i, ∑ j, |V i j| ≤ c) (x : Fin N → ℝ) :
    -c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (V *ᵥ x) := by
  have hxx : x ⬝ᵥ x = ∑ i, x i * x i := rfl
  have hVform : x ⬝ᵥ (V *ᵥ x) = ∑ i, ∑ j, V i j * (x i * x j) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hA : ∑ i, ∑ j, |V i j| * (x i * x i) ≤ c * (x ⬝ᵥ x) := by
    rw [hxx, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow i) (mul_self_nonneg (x i))
  have hB : ∑ i, ∑ j, |V i j| * (x j * x j) ≤ c * (x ⬝ᵥ x) := by
    rw [Finset.sum_comm, hxx, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← Finset.sum_mul]
    have hcol : ∑ i, |V i j| ≤ c := by
      have h : ∑ i, |V i j| = ∑ i, |V j i| := Finset.sum_congr rfl fun i _ => by rw [hsymm]
      rw [h]; exact hrow j
    exact mul_le_mul_of_nonneg_right hcol (mul_self_nonneg (x j))
  have key : ∑ i, ∑ j, -(|V i j| * (x i * x i + x j * x j) / 2) ≤ x ⬝ᵥ (V *ᵥ x) := by
    rw [hVform]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have hab : |x i * x j| ≤ (x i * x i + x j * x j) / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|x i| - |x j|), abs_nonneg (x i), abs_nonneg (x j),
        sq_abs (x i), sq_abs (x j)]
    have h1 : -(|V i j| * |x i * x j|) ≤ V i j * (x i * x j) := by
      have h := neg_abs_le (V i j * (x i * x j))
      rw [abs_mul] at h; exact h
    have h2 : |V i j| * |x i * x j| ≤ |V i j| * ((x i * x i + x j * x j) / 2) :=
      mul_le_mul_of_nonneg_left hab (abs_nonneg _)
    linarith
  have hexpand : ∑ i, ∑ j, -(|V i j| * (x i * x i + x j * x j) / 2)
      = -(1 / 2) * (∑ i, ∑ j, |V i j| * (x i * x i))
        + -(1 / 2) * (∑ i, ∑ j, |V i j| * (x j * x j)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hexpand] at key
  rw [neg_mul]
  linarith [key, hA, hB]

/-- **(b assembly) The interacting cell gap `≥ κ₀` for a bounded coupling — the first machine-checked
INTERACTING (coupled-cell) gap.** For `H = diagonal d + V`: Casimir energies `d` with vacuum `d i₀ = 0` and
excited `d i ≥ ¾` (`i ≠ i₀`), and a symmetric inter-cell coupling `V` with zero diagonal at the vacuum and
row sums `∑ⱼ |V i j| ≤ c` bounded by the cell margin `c ≤ ¾ − κ₀`. Then `H` has a ground `j₀` with every
other eigenvalue at least `κ₀` above — the spectral gap `≥ κ₀`, hence `ρ'(1) = e^{−gap} ≤ 3^{−1/4}`. Composes
`diag_form_margin` (b-i) + `coupling_form_lower` (b-ii) + `coupled_gap_of_coupling_bound`, foundation-only.
The residual is bounding the physical coupling row-sum `c` at every coupling `λ` (the quantitative confinement
content). -/
theorem interacting_cell_gap {N : ℕ} (d : Fin N → ℝ) (V : Matrix (Fin N) (Fin N) ℝ)
    (i₀ : Fin N) (hvac : d i₀ = 0) (hexc : ∀ i, i ≠ i₀ → (3 : ℝ) / 4 ≤ d i)
    (hVsymm : ∀ i j, V i j = V j i) (hVdiag : V i₀ i₀ = 0)
    {c : ℝ} (hc : c ≤ 3 / 4 - κ₀YM) (hVrow : ∀ i, ∑ j, |V i j| ≤ c)
    (hH : (Matrix.diagonal d + V).IsHermitian) :
    ∃ j₀ : Fin N, ∀ i : Fin N, i ≠ j₀ → κ₀YM ≤ hH.eigenvalues i - hH.eigenvalues j₀ := by
  have hground : (Matrix.diagonal d + V) i₀ i₀ = 0 := by
    simp [Matrix.add_apply, Matrix.diagonal_apply_eq, hvac, hVdiag]
  obtain ⟨j₀, hj₀⟩ := exists_eigenvalue_le_zero_of_diag hH i₀ hground
  refine ⟨j₀, fun i hi => ?_⟩
  set p : (Fin N → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj i₀ with hp
  have hsurj : Function.Surjective p :=
    fun r => ⟨Pi.single i₀ r, by simp [hp, LinearMap.proj_apply]⟩
  have hW : N ≤ Module.finrank ℝ (LinearMap.ker p) + 1 := by
    have hrn := p.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj] at hrn
    simp only [finrank_top, Module.finrank_self, Module.finrank_pi, Fintype.card_fin] at hrn
    omega
  have hform0 : ∀ x ∈ LinearMap.ker p, (κ₀YM + c) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Matrix.diagonal d *ᵥ x) := by
    intro x hx
    have hx0 : x i₀ = 0 := by
      have h := LinearMap.mem_ker.mp hx; rwa [hp, LinearMap.proj_apply] at h
    have hm := diag_form_margin d i₀ (m := 3 / 4) hexc x hx0
    have hxxnn : 0 ≤ x ⬝ᵥ x := by
      simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    nlinarith [hm, hxxnn, hc, mul_nonneg (by linarith : (0 : ℝ) ≤ 3 / 4 - κ₀YM - c) hxxnn]
  have hformV : ∀ x ∈ LinearMap.ker p, (-c) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (V *ᵥ x) :=
    fun x _ => coupling_form_lower V hVsymm hVrow x
  exact coupled_gap_of_coupling_bound (Matrix.diagonal d) V hH (LinearMap.ker p) hW hform0 hformV j₀ hj₀ i hi

/-- **Form bounds add — the decomposition tool toward an intensive coupling bound.** If two couplings each
have form bounded below, so does their sum: `−c₁·‖x‖² ≤ ⟨x,V₁x⟩` and `−c₂·‖x‖² ≤ ⟨x,V₂x⟩` give
`−(c₁+c₂)·‖x‖² ≤ ⟨x,(V₁+V₂)x⟩`. This lets a local coupling `V = ∑ₑ Vₑ` be bounded edge-by-edge; the
volume-uniform (intensive) bound then needs the per-edge cost to sum to an `F`-independent total, which — since
naive summation grows with the connectivity — is the frustration-free / spectral-gap content, not an elementary
form bound. Foundation-only. -/
theorem coupling_form_add {N : ℕ} (V₁ V₂ : Matrix (Fin N) (Fin N) ℝ) {c₁ c₂ : ℝ}
    (h1 : ∀ x : Fin N → ℝ, -c₁ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (V₁ *ᵥ x))
    (h2 : ∀ x : Fin N → ℝ, -c₂ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (V₂ *ᵥ x)) (x : Fin N → ℝ) :
    -(c₁ + c₂) * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((V₁ + V₂) *ᵥ x) := by
  rw [Matrix.add_mulVec, dotProduct_add, neg_add, add_mul]
  linarith [h1 x, h2 x]

/-! ### Endpoint certificates for the physical cell `HcellRr` (the λ-grid strong window)

The codim-1 form-certificate `form ≥ κ₀ on {x₀=0}` for the real-λ cell `HcellRr a = diagonal(Casimir) − a·adjM`,
supplied by `diag_form_margin` (excited Casimir `≥¾`) minus the coupling form `coupling_form_lower` (adjacency
row-sum `≤ 2`, so coupling form `≥ −2a`): `form ≥ ¾ − 2a ≥ κ₀` for `a ≤ (¾−κ₀)/2 ≈ 0.237`. Together with the
vacuum (`HcellRr 0 0 = 0`) and `HcellRr_gap_on_interval`, this closes the cell gap `≥ κ₀` over the whole strong
`λ`-window as a SINGLE interval — the first slice of the un-banked continuous-λ grid. -/

/-- `∑ⱼ [p j] ≤ 1` when the predicate `p` has at most one witness. -/
lemma sum_ite_le_one {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (hp : ∀ a b, p a → p b → a = b) : (∑ j, if p j then (1:ℝ) else 0) ≤ 1 := by
  rw [Finset.sum_boole]
  have hcard : (Finset.univ.filter p).card ≤ 1 := Finset.card_le_one.mpr
    (fun a ha b hb => hp a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2)
  calc ((Finset.univ.filter p).card : ℝ) ≤ ((1:ℕ):ℝ) := by exact_mod_cast hcard
    _ = 1 := by norm_num

/-- The adjacency has row sums `≤ 2` (each site has at most two nearest neighbours). -/
lemma adjM_row_sum_le {n : ℕ} (i : Fin n) : ∑ j, adjM n i j ≤ 2 := by
  have h1 : (∑ j : Fin n, if i.val + 1 = j.val then (1:ℝ) else 0) ≤ 1 :=
    sum_ite_le_one _ (fun a b ha hb => Fin.ext (by omega))
  have h2 : (∑ j : Fin n, if j.val + 1 = i.val then (1:ℝ) else 0) ≤ 1 :=
    sum_ite_le_one _ (fun a b ha hb => Fin.ext (by omega))
  have hle : ∀ j : Fin n, adjM n i j
      ≤ (if i.val + 1 = j.val then (1:ℝ) else 0) + (if j.val + 1 = i.val then 1 else 0) := by
    intro j; simp only [adjM, Matrix.of_apply]
    by_cases hh1 : i.val + 1 = j.val <;> by_cases hh2 : j.val + 1 = i.val <;>
      simp [hh1, hh2] <;> norm_num
  calc ∑ j, adjM n i j
      ≤ ∑ j, ((if i.val + 1 = j.val then (1:ℝ) else 0) + (if j.val + 1 = i.val then 1 else 0)) :=
        Finset.sum_le_sum (fun j _ => hle j)
    _ = (∑ j : Fin n, if i.val + 1 = j.val then (1:ℝ) else 0)
        + (∑ j : Fin n, if j.val + 1 = i.val then (1:ℝ) else 0) := Finset.sum_add_distrib
    _ ≤ 2 := by linarith

/-- The cell's vacuum: `HcellRr 0 0 = 0` (the `j=0` state has zero Casimir and no self-adjacency). -/
lemma HcellRr_zero_zero (jmax : ℕ) (lam : ℝ) :
    HcellRr jmax lam (0 : Fin (dim jmax)) (0 : Fin (dim jmax)) = 0 := by
  simp only [HcellRr, Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply, adjM,
    Matrix.of_apply, Fin.val_zero]; norm_num

/-- **Endpoint form-certificate (strong window):** for `2a ≤ ¾ − κ₀`, the form of `HcellRr a` is `≥ κ₀`
on `{x₀=0}` — excited Casimir `≥¾` (`diag_form_margin`) minus the coupling `≥ −2a` (`coupling_form_lower`,
adjacency row-sum `≤ 2`). This is the hypothesis `HcellRr_gap_on_interval` consumes at each grid endpoint. -/
theorem HcellRr_form_ge_strong (jmax : ℕ) {a : ℝ} (ha0 : 0 ≤ a) (ha : 2 * a ≤ 3 / 4 - κ₀YM)
    (x : Fin (dim jmax) → ℝ) (hx : x 0 = 0) :
    κ₀YM * (x ⬝ᵥ x) ≤ x ⬝ᵥ (HcellRr jmax a *ᵥ x) := by
  have hxx : 0 ≤ x ⬝ᵥ x := by rw [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hD : (3 / 4 : ℝ) * (x ⬝ᵥ x)
      ≤ x ⬝ᵥ (Matrix.diagonal (fun i : Fin (dim jmax) => (i.val * (i.val + 2) : ℝ) / 4) *ᵥ x) := by
    apply diag_form_margin _ (0 : Fin (dim jmax)) _ x hx
    intro i hi
    have hp : 1 ≤ i.val := by
      rcases Nat.eq_zero_or_pos i.val with h | h
      · exact absurd (Fin.ext (by simp [h])) hi
      · omega
    have hr : (1 : ℝ) ≤ (i.val : ℝ) := by exact_mod_cast hp
    nlinarith [hr]
  have hV : -(2 * a) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (((-a) • adjM (dim jmax)) *ᵥ x) := by
    apply coupling_form_lower ((-a) • adjM (dim jmax)) _ _ x
    · intro i j
      simp only [Matrix.smul_apply, smul_eq_mul, adjM, Matrix.of_apply]
      congr 1; exact if_congr or_comm rfl rfl
    · intro i
      have hcast : ∀ j : Fin (dim jmax), |((-a) • adjM (dim jmax)) i j| = a * adjM (dim jmax) i j := by
        intro j
        simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_neg, abs_of_nonneg ha0]
        rw [abs_of_nonneg]; simp only [adjM, Matrix.of_apply]; split_ifs <;> norm_num
      calc ∑ j, |((-a) • adjM (dim jmax)) i j| = ∑ j, a * adjM (dim jmax) i j :=
            Finset.sum_congr rfl fun j _ => hcast j
        _ = a * ∑ j, adjM (dim jmax) i j := by rw [Finset.mul_sum]
        _ ≤ a * 2 := mul_le_mul_of_nonneg_left (adjM_row_sum_le i) ha0
        _ = 2 * a := by ring
  have hsplit : x ⬝ᵥ (HcellRr jmax a *ᵥ x)
      = x ⬝ᵥ (Matrix.diagonal (fun i : Fin (dim jmax) => (i.val * (i.val + 2) : ℝ) / 4) *ᵥ x)
        + x ⬝ᵥ (((-a) • adjM (dim jmax)) *ᵥ x) := by
    rw [HcellRr, sub_eq_add_neg, ← neg_smul, Matrix.add_mulVec, dotProduct_add]
  rw [hsplit]
  nlinarith [hD, hV, mul_nonneg (by linarith : (0:ℝ) ≤ 3 / 4 - 2 * a - κ₀YM) hxx]

/-- The 0-th coordinate functional (ascribed to `ℝ` codomain, so it feeds rank-nullity). -/
def proj0 (jmax : ℕ) : (Fin (dim jmax) → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (0 : Fin (dim jmax))

/-- The codimension-1 subspace `{x : x₀ = 0}` for the strong-window certificate. -/
def W0 (jmax : ℕ) : Submodule ℝ (Fin (dim jmax) → ℝ) := LinearMap.ker (proj0 jmax)

lemma W0_mem (jmax : ℕ) (x : Fin (dim jmax) → ℝ) : x ∈ W0 jmax ↔ x 0 = 0 := by
  simp only [W0, proj0, LinearMap.mem_ker, LinearMap.proj_apply]

lemma W0_corank (jmax : ℕ) : dim jmax ≤ Module.finrank ℝ (W0 jmax) + 1 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (proj0 jmax)
  have hr1 : Module.finrank ℝ (LinearMap.range (proj0 jmax)) ≤ 1 := by
    calc Module.finrank ℝ (LinearMap.range (proj0 jmax))
        ≤ Module.finrank ℝ ℝ := Submodule.finrank_le _
      _ = 1 := Module.finrank_self ℝ
  rw [Module.finrank_fin_fun (R := ℝ)] at hrn
  unfold W0
  omega

/-- **★ Strong-window closure of the continuous-λ cell gap.** For `0 ≤ a ≤ b` with `2b ≤ ¾−κ₀`, the
physical SU(2) cell `HcellRr` has spectral gap `≥ κ₀` at EVERY real `λ = (1−s)a + s·b ∈ [a,b]` — a whole
continuum interval closed from just its two endpoint form-certificates (`HcellRr_form_ge_strong`) plus the
vacuum (`HcellRr_zero_zero`), via `HcellRr_gap_on_interval`. Since `(¾−κ₀)/2 ≈ 0.237 ⊇ [0.16, 0.237]`, this
closes the STRONG-COUPLING window of the physical range as ONE interval, fully foundational — the first real
slice of the un-banked continuous-λ grid (no Weyl, no per-λ sampling). -/
theorem HcellRr_gap_strong_window (jmax : ℕ) {a b : ℝ} (ha0 : 0 ≤ a) (hab : 2 * b ≤ 3 / 4 - κ₀YM)
    (hab' : a ≤ b) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∃ i₀, (HcellRr_isHermitian jmax ((1 - s) * a + s * b)).eigenvalues i₀ ≤ 0 ∧
      ∀ i, i ≠ i₀ → (HcellRr_isHermitian jmax ((1 - s) * a + s * b)).eigenvalues i₀ + κ₀YM
        ≤ (HcellRr_isHermitian jmax ((1 - s) * a + s * b)).eigenvalues i := by
  obtain ⟨i₀, hi₀⟩ := exists_eigenvalue_le_zero_of_diag
    (HcellRr_isHermitian jmax ((1 - s) * a + s * b)) 0 (HcellRr_zero_zero jmax ((1 - s) * a + s * b))
  refine ⟨i₀, hi₀, fun i hi => ?_⟩
  refine HcellRr_gap_on_interval jmax a b κ₀YM_pos (W0 jmax) (W0_corank jmax) ?_ ?_ hs0 hs1 hi₀ hi
  · intro x hx; exact HcellRr_form_ge_strong jmax ha0 (by linarith) x ((W0_mem jmax x).mp hx)
  · intro x hx
    exact HcellRr_form_ge_strong jmax (le_trans ha0 hab') hab x ((W0_mem jmax x).mp hx)

/-! ### Large-λ regime: relative interval gap closure

The strong-window closure `HcellRr_gap_strong_window` uses the fixed subspace `{x₀=0}` where the form is
`≥ κ₀`; that fails for `λ > (¾−κ₀)/2 ≈ 0.24` (both `E₀,E₁` go negative). The RELATIVE closure below tiles the
remaining physical range `[0.24, 6.76]`: on each subinterval fix a codim-1 `W` (the `ldlKer` at a reference
`λ`), verify the shifted form `≥ t` on `W` at BOTH endpoints (`form_ge_convex` extends it across), and bound
the single low eigenvalue `E₀ ≤ t−κ₀` with a trial state whose Rayleigh is affine in `λ` (`form_le_convex`,
checked at both endpoints). Four endpoint checks close the whole subinterval — no per-`λ` sampling, no Weyl. -/

/-- **Relative interval gap closure (large-λ regime).** For the affine family `(1−s)A+sB` (`= H(λ)`), if the
codim-1 form is `≥ t` on `W` at BOTH endpoints `A,B` (extended across `[a,b]` by `form_ge_convex`) and some
eigenvalue `i₀` is `≤ t−μ` (the tight E₀ bound), then every OTHER eigenvalue is `≥ λ_{i₀}+μ` for the whole
interval. Relative analogue of `gap_on_interval` (both `E₀,E₁` negative). Foundation-only. -/
theorem gap_on_interval_rel {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) {t μ : ℝ} (hμ : 0 < μ)
    (W : Submodule ℝ (Fin N → ℝ)) (hW : N ≤ Module.finrank ℝ W + 1)
    (hAf : ∀ x ∈ W, t * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x))
    (hBf : ∀ x ∈ W, t * (x ⬝ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hH : ((1 - s) • A + s • B).IsHermitian)
    {i₀ : Fin N} (hi₀ : hH.eigenvalues i₀ ≤ t - μ) {i : Fin N} (hi : i ≠ i₀) :
    hH.eigenvalues i₀ + μ ≤ hH.eigenvalues i := by
  have hcard := atMostOne_eigenvalue_lt hH W hW (form_ge_convex A B W hAf hBf hs0 hs1)
  have hi0lt : hH.eigenvalues i₀ < t := by linarith
  by_contra hcon
  push_neg at hcon
  have hilt : hH.eigenvalues i < t := by linarith
  set S := Finset.univ.filter (fun k => hH.eigenvalues k < t) with hS
  have hi0mem : i₀ ∈ S := by
    rw [hS]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi0lt
  have himem : i ∈ S := by
    rw [hS]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hilt
  have h2 : 1 < S.card := Finset.one_lt_card.mpr ⟨i, himem, i₀, hi0mem, hi⟩
  omega

/-- Single-vector convexity (`≤` direction) — the affine Rayleigh bound for the trial-state E₀. -/
lemma form_le_convex {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) (ψ : Fin N → ℝ) {c : ℝ}
    (hA : ψ ⬝ᵥ (A *ᵥ ψ) ≤ c) (hB : ψ ⬝ᵥ (B *ᵥ ψ) ≤ c)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ψ ⬝ᵥ (((1 - s) • A + s • B) *ᵥ ψ) ≤ c := by
  have hform : ψ ⬝ᵥ (((1 - s) • A + s • B) *ᵥ ψ)
      = (1 - s) * (ψ ⬝ᵥ (A *ᵥ ψ)) + s * (ψ ⬝ᵥ (B *ᵥ ψ)) := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  rw [hform]; nlinarith [hA, hB, hs0, hs1]

/-- **Relative interval gap for the physical cell (large-λ).** Given a codim-1 `W` with form `≥ t` at both
endpoints `HcellRr a`, `HcellRr b`, and a trial state `ψ` with Rayleigh `≤ (t−κ₀)‖ψ‖²` at both endpoints, the
gap `≥ κ₀` at `HcellRr` for EVERY `λ = (1−s)a+s·b ∈ [a,b]` — the large-λ analogue of
`HcellRr_gap_strong_window`, closing the interval from four endpoint checks. Foundation-only. -/
theorem HcellRr_gap_on_interval_rel (jmax : ℕ) (a b : ℝ) {t : ℝ}
    (W : Submodule ℝ (Fin (dim jmax) → ℝ)) (hW : dim jmax ≤ Module.finrank ℝ W + 1)
    (hAf : ∀ x ∈ W, t * (x ⬝ᵥ x) ≤ x ⬝ᵥ (HcellRr jmax a *ᵥ x))
    (hBf : ∀ x ∈ W, t * (x ⬝ᵥ x) ≤ x ⬝ᵥ (HcellRr jmax b *ᵥ x))
    (ψ : Fin (dim jmax) → ℝ) (hψ0 : ψ ≠ 0)
    (hψA : ψ ⬝ᵥ (HcellRr jmax a *ᵥ ψ) ≤ (t - κ₀YM) * (ψ ⬝ᵥ ψ))
    (hψB : ψ ⬝ᵥ (HcellRr jmax b *ᵥ ψ) ≤ (t - κ₀YM) * (ψ ⬝ᵥ ψ))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∃ i₀, ∀ i, i ≠ i₀ → (HcellRr_isHermitian jmax ((1 - s) * a + s * b)).eigenvalues i₀ + κ₀YM
      ≤ (HcellRr_isHermitian jmax ((1 - s) * a + s * b)).eigenvalues i := by
  have hRay : ψ ⬝ᵥ (HcellRr jmax ((1 - s) * a + s * b) *ᵥ ψ) ≤ (t - κ₀YM) * (ψ ⬝ᵥ ψ) := by
    rw [HcellRr_affine jmax a b s]
    exact form_le_convex (HcellRr jmax a) (HcellRr jmax b) ψ hψA hψB hs0 hs1
  obtain ⟨i₀, hi₀⟩ :=
    exists_eigenvalue_le_of_form (HcellRr_isHermitian jmax ((1 - s) * a + s * b)) hψ0 hRay
  refine ⟨i₀, fun i hi => ?_⟩
  have hform : ∀ x ∈ W, t * (x ⬝ᵥ x) ≤ x ⬝ᵥ (HcellRr jmax ((1 - s) * a + s * b) *ᵥ x) := by
    intro x hx; rw [HcellRr_affine jmax a b s]
    exact form_ge_convex (HcellRr jmax a) (HcellRr jmax b) W hAf hBf hs0 hs1 x hx
  have hcard := atMostOne_eigenvalue_lt (HcellRr_isHermitian jmax ((1 - s) * a + s * b)) W hW hform
  have hkpos := κ₀YM_pos
  have hi0lt : (HcellRr_isHermitian jmax ((1 - s) * a + s * b)).eigenvalues i₀ < t := by linarith
  by_contra hcon; push_neg at hcon
  have hilt : (HcellRr_isHermitian jmax ((1 - s) * a + s * b)).eigenvalues i < t := by linarith
  set S := Finset.univ.filter
    (fun k => (HcellRr_isHermitian jmax ((1 - s) * a + s * b)).eigenvalues k < t) with hS
  have hi0mem : i₀ ∈ S := by
    rw [hS]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi0lt
  have himem : i ∈ S := by
    rw [hS]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hilt
  have h2 : 1 < S.card := Finset.one_lt_card.mpr ⟨i, himem, i₀, hi0mem, hi⟩
  omega

/-- **Restricted-form PSD certificate.** If the `r×r` matrix `Bᵀ(A−t)B` is PSD, the form is `≥ t` on the
shared subspace `range B`. Valid for ANY `A`, so a FIXED `B` (fixed `W = range B`) certifies the form at BOTH
endpoints of a λ-interval — the missing shared-subspace ingredient the relative interval closure needs (the
per-λ `ldlKer` differs endpoint to endpoint; this one doesn't). Foundation-only. -/
theorem form_ge_on_range_of_psd {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (B : Matrix (Fin n) (Fin r) ℝ)
    (hpsd : (Bᵀ * (A - t • (1 : Matrix (Fin n) (Fin n) ℝ)) * B).PosSemidef) :
    ∀ x ∈ LinearMap.range (Matrix.mulVecLin B), t * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  rintro x ⟨y, rfl⟩
  simp only [Matrix.mulVecLin_apply]
  set M : Matrix (Fin n) (Fin n) ℝ := A - t • (1 : Matrix (Fin n) (Fin n) ℝ) with hM
  have key : (B *ᵥ y) ⬝ᵥ (M *ᵥ (B *ᵥ y)) = y ⬝ᵥ ((Bᵀ * M * B) *ᵥ y) := by
    conv_rhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  have hge : (0 : ℝ) ≤ y ⬝ᵥ ((Bᵀ * M * B) *ᵥ y) := by
    have := hpsd.re_dotProduct_nonneg y
    simpa [star_trivial, RCLike.re_to_real] using this
  have hexpand : (B *ᵥ y) ⬝ᵥ (M *ᵥ (B *ᵥ y))
      = (B *ᵥ y) ⬝ᵥ (A *ᵥ (B *ᵥ y)) - t * ((B *ᵥ y) ⬝ᵥ (B *ᵥ y)) := by
    rw [hM, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
  rw [key] at hexpand
  linarith [hge, hexpand]

/-- **Corank of `range B` from a left inverse.** If `C*B = 1` (so `B` has full column rank `r`), then
`n ≤ finrank (range B) + (n−r)`; for `r = n−1` this is the corank-1 bound the count lemma needs. The left
inverse `C` is a rational matrix checked by `norm_num` at instantiation. Foundation-only. -/
lemma range_corank_of_leftInv {n r : ℕ} (B : Matrix (Fin n) (Fin r) ℝ) (C : Matrix (Fin r) (Fin n) ℝ)
    (hCB : C * B = 1) (hr : n ≤ r + 1) :
    n ≤ Module.finrank ℝ (LinearMap.range (Matrix.mulVecLin B)) + 1 := by
  have hinj : Function.Injective (Matrix.mulVecLin B) := by
    intro y1 y2 h
    simp only [Matrix.mulVecLin_apply] at h
    have h2 : C *ᵥ (B *ᵥ y1) = C *ᵥ (B *ᵥ y2) := by rw [h]
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hCB, Matrix.one_mulVec,
      Matrix.one_mulVec] at h2
  have hrank : Module.finrank ℝ (LinearMap.range (Matrix.mulVecLin B)) = r := by
    rw [LinearMap.finrank_range_of_inj hinj]
    simp [Module.finrank_pi]
  omega

section RelTileDemo
/-! ### Concrete large-λ tile — non-vacuousness of the relative interval closure

Instantiates `HcellRr_gap_on_interval_rel` on a real large-λ sub-interval `[14/5, 16/5]` of the physical
jmax=2 cell, where BOTH `E₀,E₁ < 0` (the absolute strong-window bound fails). The shared subspace is
`W = range Bt = φ⊥` (`φ = (1,5/4,3/4,1/2,0)` ≈ the ground state); the shift is `t = −2`. Four endpoint
certificates close the whole interval: two restricted-form PSD (`psdTile_a/b'`, exact LDLᵀ of the 4×4
`Bᵀ(H+2)B`) and two trial-state Rayleigh (`rayTile_a/b'`, `ψ=(3/4,1,3/4,1/4,0)`). Certificate machine-
generated + exact-verified. Matrices carry a `Fin 5` type so the concrete products
reduce (the `dim 2` index otherwise blocks `Fin.sum_univ_five`); the `Fin (dim 2)` interface closes by defeq. -/

private noncomputable def BtTile : Matrix (Fin 5) (Fin 4) ℝ :=
  !![-5/4, -3/4, -1/2, 0; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
private noncomputable def CtTile : Matrix (Fin 4) (Fin 5) ℝ :=
  !![0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
private noncomputable def HaTile : Matrix (Fin 5) (Fin 5) ℝ :=
  !![(0:ℝ), -14/5, 0, 0, 0; -14/5, 3/4, -14/5, 0, 0; 0, -14/5, 2, -14/5, 0;
     0, 0, -14/5, 15/4, -14/5; 0, 0, 0, -14/5, 6]
private noncomputable def HbTile : Matrix (Fin 5) (Fin 5) ℝ :=
  !![(0:ℝ), -16/5, 0, 0, 0; -16/5, 3/4, -16/5, 0, 0; 0, -16/5, 2, -16/5, 0;
     0, 0, -16/5, 15/4, -16/5; 0, 0, 0, -16/5, 6]

private theorem bridgeTile_a : HcellRr 2 (14/5) = HaTile := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [HcellRr, adjM, HaTile, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
      Matrix.diagonal_apply] <;> norm_num
private theorem bridgeTile_b : HcellRr 2 (16/5) = HbTile := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [HcellRr, adjM, HbTile, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
      Matrix.diagonal_apply] <;> norm_num

private theorem hCBTile : CtTile * BtTile = 1 := by
  ext i j
  simp only [CtTile, BtTile, Matrix.mul_apply, Fin.sum_univ_five, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue]
  fin_cases i <;> fin_cases j <;> simp only [Matrix.one_apply, Fin.reduceEq, reduceIte] <;> norm_num

private theorem psdTile_a :
    (BtTileᵀ * (HaTile - (-2 : ℝ) • (1 : Matrix (Fin 5) (Fin 5) ℝ)) * BtTile).PosSemidef := by
  refine posSemidef_of_ldl _
    (!![(1:ℝ), 47/515, 106/515, 0; 0, 1, -23606/51683, 0; 0, 0, 1, -2894248/4814553; 0, 0, 0, 1])
    ![103/8, 51683/10300, 4814553/1033660, 152062648/24072765] ?_ ?_
  · intro i; fin_cases i <;> norm_num
  · ext i j
    simp only [HaTile, BtTile, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_five,
      Fin.sum_univ_four, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.cons_val, Matrix.diagonal_apply, Fin.isValue]
    fin_cases i <;> fin_cases j <;> simp only [Fin.reduceEq, reduceIte] <;> norm_num

private theorem psdTile_b :
    (BtTileᵀ * (HbTile - (-2 : ℝ) • (1 : Matrix (Fin 5) (Fin 5) ℝ)) * BtTile).PosSemidef := by
  refine posSemidef_of_ldl _
    (!![(1:ℝ), 43/555, 38/185, 0; 0, 1, -29646/55963, 0; 0, 0, 1, -3581632/4756577; 0, 0, 0, 1])
    ![111/8, 55963/11100, 4756577/1119260, 132956968/23782885] ?_ ?_
  · intro i; fin_cases i <;> norm_num
  · ext i j
    simp only [HbTile, BtTile, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_five,
      Fin.sum_univ_four, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.cons_val, Matrix.diagonal_apply, Fin.isValue]
    fin_cases i <;> fin_cases j <;> simp only [Fin.reduceEq, reduceIte] <;> norm_num

private theorem rayTile_a :
    (![3/4, 1, 3/4, 1/4, 0] : Fin 5 → ℝ) ⬝ᵥ (HaTile *ᵥ ![3/4, 1, 3/4, 1/4, 0])
      ≤ (-2 - κ₀YM) * ((![3/4, 1, 3/4, 1/4, 0] : Fin 5 → ℝ) ⬝ᵥ ![3/4, 1, 3/4, 1/4, 0]) := by
  simp only [HaTile, dotProduct, Matrix.mulVec, Fin.sum_univ_five, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue]
  nlinarith [κ₀YM_le_half, κ₀YM_pos]

private theorem rayTile_b :
    (![3/4, 1, 3/4, 1/4, 0] : Fin 5 → ℝ) ⬝ᵥ (HbTile *ᵥ ![3/4, 1, 3/4, 1/4, 0])
      ≤ (-2 - κ₀YM) * ((![3/4, 1, 3/4, 1/4, 0] : Fin 5 → ℝ) ⬝ᵥ ![3/4, 1, 3/4, 1/4, 0]) := by
  simp only [HbTile, dotProduct, Matrix.mulVec, Fin.sum_univ_five, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue]
  nlinarith [κ₀YM_le_half, κ₀YM_pos]

/-- **Concrete large-λ tile: gap ≥ κ₀ across `λ ∈ [14/5, 16/5]` (foundational, no Weyl).** Non-vacuousness of
`HcellRr_gap_on_interval_rel`: the physical jmax=2 SU(2) cell has spectral gap `≥ κ₀` at EVERY real
`λ ∈ [2.8, 3.2]` — a genuine slice of the large-λ regime where both `E₀,E₁ < 0` (the absolute strong-window
bound fails), closed as ONE interval from four endpoint certificates. -/
theorem hcellRr_rel_tile_demo {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∃ i₀, ∀ i, i ≠ i₀ →
      (HcellRr_isHermitian 2 ((1 - s) * (14/5) + s * (16/5))).eigenvalues i₀ + κ₀YM
        ≤ (HcellRr_isHermitian 2 ((1 - s) * (14/5) + s * (16/5))).eigenvalues i := by
  have hψ0 : (![3/4, 1, 3/4, 1/4, 0] : Fin (dim 2) → ℝ) ≠ 0 := by
    intro hc; have h1 := congrFun hc 1
    simp [Matrix.cons_val_one, Matrix.head_cons] at h1
  refine HcellRr_gap_on_interval_rel 2 (14/5) (16/5) (LinearMap.range (Matrix.mulVecLin BtTile))
    (range_corank_of_leftInv BtTile CtTile hCBTile (by norm_num)) ?_ ?_ ![3/4, 1, 3/4, 1/4, 0] hψ0
    (by rw [bridgeTile_a]; exact rayTile_a) (by rw [bridgeTile_b]; exact rayTile_b) hs0 hs1
  · exact form_ge_on_range_of_psd (HcellRr 2 (14/5)) (-2) BtTile (by rw [bridgeTile_a]; exact psdTile_a)
  · exact form_ge_on_range_of_psd (HcellRr 2 (16/5)) (-2) BtTile (by rw [bridgeTile_b]; exact psdTile_b)

end RelTileDemo

/-! ### (spectral-gap route A) Toward the volume-uniform interacting gap via a local-gap criterion

`interacting_cell_gap` is a fixed-size result; the volume-uniform gap needs an INTENSIVE argument. Route A
(Knabe): a finite-window gap above a threshold forces a positive bulk gap. Step 1 is the "output" side — the
operator inequality `H² ⪰ γ·H` is the spectral gap. -/

/-- **(route A, step 1) Operator inequality ⟹ spectral gap.** For a PSD Hermitian real matrix `A`
(`0 ≤ eigenvalues i`), the operator inequality `H² ⪰ γ·H` — in form terms `γ·⟨x,Ax⟩ ≤ ‖Ax‖²` for every `x` —
forces every eigenvalue to be `0` or `≥ γ`. With a frustration-free zero ground this is `spec ⊆ {0}∪[γ,∞)`, the
gap. The "output" of the Knabe local-gap criterion; the telescoping that supplies `H² ⪰ γH` from the local
window gaps is the research core (route A step 3). Foundation-only. -/
theorem gap_of_operator_sq_ge {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) {γ : ℝ}
    (hpsd : ∀ i, 0 ≤ hA.eigenvalues i)
    (hop : ∀ x : Fin N → ℝ, γ * (x ⬝ᵥ (A *ᵥ x)) ≤ (A *ᵥ x) ⬝ᵥ (A *ᵥ x)) :
    ∀ i, hA.eigenvalues i = 0 ∨ γ ≤ hA.eigenvalues i := by
  intro i
  have hx := hop (⇑(hA.eigenvectorBasis i))
  have hnorm : (⇑(hA.eigenvectorBasis i) : Fin N → ℝ) ⬝ᵥ (⇑(hA.eigenvectorBasis i)) = 1 := by
    rw [eigen_orthonormal' hA i i]; simp
  rw [eigen_quadForm' hA i, hA.mulVec_eigenvectorBasis, smul_dotProduct, dotProduct_smul, hnorm] at hx
  simp only [smul_eq_mul, mul_one] at hx
  rcases eq_or_lt_of_le (hpsd i) with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by nlinarith [hx, h])

open Matrix in
/-- **Converse of `gap_of_operator_sq_ge` — the window input to Knabe (foundational).** A frustration-free
(PSD, gapped) Hermitian operator satisfies the operator inequality `H² ⪰ γH`: if every eigenvalue is `0` or
`≥ γ` (and all `≥ 0`), then `γ (x·Hx) ≤ (Hx)·(Hx)` for every `x`. Proof: each eigenvalue satisfies `λ² ≥ γλ`,
so the diagonal `D² − γD` is PSD; conjugating by the eigenvector unitary (spectral theorem) makes `A*A − γ•A`
PSD, and `A` symmetric turns its quadratic form into `(Hx)·(Hx) − γ(x·Hx)`. Together with
`gap_of_operator_sq_ge` this is the equivalence `H²⪰γH ⟺ FF-gap ≥ γ` — the per-window fact Knabe's telescoping
consumes. Foundational (`propext, Classical.choice, Quot.sound`). -/
theorem operator_sq_ge_of_gap {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) {γ : ℝ}
    (hpsd : ∀ i, 0 ≤ hA.eigenvalues i)
    (hgap : ∀ i, hA.eigenvalues i = 0 ∨ γ ≤ hA.eigenvalues i) :
    ∀ x : Fin N → ℝ, γ * (x ⬝ᵥ (A *ᵥ x)) ≤ (A *ᵥ x) ⬝ᵥ (A *ᵥ x) := by
  classical
  set D : Matrix (Fin N) (Fin N) ℝ := diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  have hdiagPSD : (D * D - γ • D).PosSemidef := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_smul, diagonal_sub, Matrix.posSemidef_diagonal_iff]
    intro i
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    have he : (RCLike.ofReal (hA.eigenvalues i) : ℝ) = hA.eigenvalues i := by simp
    rw [he]
    rcases hgap i with h | h
    · rw [h]; simp
    · nlinarith [hpsd i, h]
  have hst : A = (Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary) D := hA.spectral_theorem
  have hMeq : A * A - γ • A = (Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary) (D * D - γ • D) := by
    rw [map_sub, map_mul, map_smul, ← hst]
  have hUunit : IsUnit (↑hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) := Unitary.isUnit_coe
  have hMpsd : (A * A - γ • A).PosSemidef := by
    rw [hMeq, Unitary.conjStarAlgAut_apply]
    exact (hUunit.posSemidef_star_right_conjugate_iff).mpr hdiagPSD
  have hsymm : Aᵀ = A := by
    ext i j
    have h := congrFun (congrFun hA i) j
    simpa [Matrix.conjTranspose_apply, star_trivial] using h
  have hadj : ∀ u v : Fin N → ℝ, (A *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (A *ᵥ v) := by
    intro u v
    rw [dotProduct_comm (A *ᵥ u) v, dotProduct_mulVec, ← mulVec_transpose, hsymm,
      dotProduct_comm (A *ᵥ v) u]
  intro x
  have h1 : x ⬝ᵥ ((A * A) *ᵥ x) = (A *ᵥ x) ⬝ᵥ (A *ᵥ x) := by
    rw [← mulVec_mulVec, ← hadj]
  have hquad : x ⬝ᵥ ((A * A - γ • A) *ᵥ x)
      = (A *ᵥ x) ⬝ᵥ (A *ᵥ x) - γ * (x ⬝ᵥ (A *ᵥ x)) := by
    rw [sub_mulVec, dotProduct_sub, h1, smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hnn : 0 ≤ x ⬝ᵥ ((A * A - γ • A) *ᵥ x) := by
    have h := hMpsd.re_dotProduct_nonneg x
    simpa [star_trivial, RCLike.re_to_real] using h
  linarith [hquad ▸ hnn]

#print axioms operator_sq_ge_of_gap

open Matrix in
/-- Adjoint identity for a symmetric matrix: `⟨Wu, v⟩ = ⟨u, Wv⟩` (dotProduct form). -/
theorem sadj {N : ℕ} {W : Matrix (Fin N) (Fin N) ℝ} (hW : W.IsHermitian) (u v : Fin N → ℝ) :
    (W *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (W *ᵥ v) := by
  have hsymm : Wᵀ = W := by
    ext i j; have h := congrFun (congrFun hW i) j
    simpa [Matrix.conjTranspose_apply, star_trivial] using h
  rw [dotProduct_comm (W *ᵥ u) v, dotProduct_mulVec, ← mulVec_transpose, hsymm,
    dotProduct_comm (W *ᵥ v) u]

open Matrix in
/-- **Knabe algebraic assembly (conditional; foundational).** Given the two window identities
`∑ₐ Wₐ = (n−1)·H` and `∑ₐ Wₐ² = (n−2)·H² + H`, and each window's operator inequality `Wₐ² ⪰ ε Wₐ` (from
`operator_sq_ge_of_gap`), summing over windows and collapsing both sides yields
`((n−1)ε − 1)(x·Hx) ≤ (n−2)(Hx·Hx)`; dividing by `n−2 > 0` + `gap_of_operator_sq_ge` gives bulk gap
`((n−1)ε−1)/(n−2)`. **Scope (honest):** `hsum1` always holds (each site in `n−1` windows). `hsum2` as written
holds only when NON-ADJACENT terms annihilate (`hⱼhₖ = 0` for `|j−k| ≥ 2`) — the idealized / blocked case; a
`m=2` check gives `∑ₐWₐ² = 2H + ∑_{|j−k|=1}hⱼhₖ` vs `H²+H = 2H + ∑_{j≠k}hⱼhₖ`, equal iff `∑_{|j−k|≥2}hⱼhₖ = 0`.
For a GENERIC nearest-neighbour frustration-free chain the true identity is `∑ₐWₐ² = ∑ᵢⱼ(n−1−|i−j|)₊ hᵢhⱼ`, and
the passage to `H²⪰γH` needs the operator Cauchy–Schwarz weighted-sum inequality (Knabe 1988 / Gosset–Mozgunov
2016) — the genuine remaining core, NOT a counting identity. This lemma is the exact assembly for the special
case and the correct skeleton for the general one. Foundational (`propext, Classical.choice, Quot.sound`). -/
theorem knabe_gap_of_window_identities {N : ℕ} {ι : Type*} [Fintype ι]
    {H : Matrix (Fin N) (Fin N) ℝ} (hHsymm : H.IsHermitian)
    {W : ι → Matrix (Fin N) (Fin N) ℝ} (hWsymm : ∀ a, (W a).IsHermitian) {ε : ℝ} {n : ℕ}
    (hsum1 : ∑ a, W a = ((n : ℝ) - 1) • H)
    (hsum2 : ∑ a, (W a) * (W a) = ((n : ℝ) - 2) • (H * H) + H)
    (hwin : ∀ a, ∀ x : Fin N → ℝ, ε * (x ⬝ᵥ (W a *ᵥ x)) ≤ (W a *ᵥ x) ⬝ᵥ (W a *ᵥ x)) :
    ∀ x : Fin N → ℝ,
      (((n : ℝ) - 1) * ε - 1) * (x ⬝ᵥ (H *ᵥ x)) ≤ ((n : ℝ) - 2) * ((H *ᵥ x) ⬝ᵥ (H *ᵥ x)) := by
  intro x
  have hHsq : x ⬝ᵥ ((H * H) *ᵥ x) = (H *ᵥ x) ⬝ᵥ (H *ᵥ x) := by
    rw [← mulVec_mulVec]; exact (sadj hHsymm x (H *ᵥ x)).symm
  have hkey : (∑ a, ε * (x ⬝ᵥ (W a *ᵥ x))) ≤ ∑ a, (W a *ᵥ x) ⬝ᵥ (W a *ᵥ x) :=
    Finset.sum_le_sum (fun a _ => hwin a x)
  have hL : (∑ a, ε * (x ⬝ᵥ (W a *ᵥ x))) = ε * ((n : ℝ) - 1) * (x ⬝ᵥ (H *ᵥ x)) := by
    rw [← Finset.mul_sum, ← dotProduct_sum, ← Matrix.sum_mulVec, hsum1, smul_mulVec,
      dotProduct_smul, smul_eq_mul]
    ring
  have hR : (∑ a, (W a *ᵥ x) ⬝ᵥ (W a *ᵥ x))
      = ((n : ℝ) - 2) * ((H *ᵥ x) ⬝ᵥ (H *ᵥ x)) + (x ⬝ᵥ (H *ᵥ x)) := by
    have hterm : ∀ a, (W a *ᵥ x) ⬝ᵥ (W a *ᵥ x) = x ⬝ᵥ ((W a * W a) *ᵥ x) := by
      intro a; rw [sadj (hWsymm a), mulVec_mulVec]
    rw [Finset.sum_congr rfl (fun a _ => hterm a), ← dotProduct_sum, ← Matrix.sum_mulVec, hsum2,
      add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul, hHsq]
  rw [hL, hR] at hkey
  nlinarith [hkey]

#print axioms knabe_gap_of_window_identities

/-! ### The CORRECT Knabe window identities on the periodic chain (`ZMod L`), foundational

These are the true combinatorial identities (no non-adjacent-vanishing assumption). `window_sum` is `hsum1`
(always holds). `window_sq_sum` is the honest `hsum2` in `Tδ` form: `∑ₐWₐ² = ∑ᵣ∑ₛ ∑_b h_b h_{b+(s−r)}`
(`= ∑_δ (m−|δ|)₊ Tδ`). The remaining passage `Tδ`-sum `⟹ H²⪰γH` is the Knabe/Gosset–Mozgunov operator
Cauchy–Schwarz step (the genuine research core), NOT covered here. -/

/-- Shift-invariance of a full cyclic sum: `∑ₐ h(a+c) = ∑ₐ h a`. -/
theorem cyc_shift_sum {N L : ℕ} [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ) (c : ZMod L) :
    (∑ a, h (a + c)) = ∑ a, h a :=
  Fintype.sum_equiv (Equiv.addRight c) (fun a => h (a + c)) h (fun _ => rfl)

/-- **Window-sum identity `hsum1` (always holds, foundational).** With `Wₐ = ∑_{r<m} h(a+r)` and `H = ∑ⱼ hⱼ`,
summing over all `L` windows gives `∑ₐ Wₐ = m·H` — each term lies in exactly `m` windows. -/
theorem window_sum {N L : ℕ} [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ) (m : ℕ) :
    (∑ a : ZMod L, ∑ r ∈ Finset.range m, h (a + (r : ZMod L))) = m • (∑ j, h j) := by
  rw [Finset.sum_comm]
  simp_rw [cyc_shift_sum]
  rw [Finset.sum_const, Finset.card_range]

/-- **Correct window-square identity `hsum2` (the `Tδ` form, foundational).**
`∑ₐ Wₐ² = ∑ᵣ ∑ₛ ∑_b h_b · h_{b+(s−r)}`, i.e. `∑_δ (m−|δ|)₊ Tδ` with `Tδ = ∑_b h_b h_{b+δ}` — the TRUE identity,
with NO assumption that non-adjacent products vanish (contrast the idealized `(n−2)H²+H`). Reaching `H²⪰γH`
from this is the Knabe/Gosset–Mozgunov operator Cauchy–Schwarz step. -/
theorem window_sq_sum {N L : ℕ} [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ) (m : ℕ) :
    (∑ a : ZMod L, (∑ r ∈ Finset.range m, h (a + (r : ZMod L))) *
        (∑ s ∈ Finset.range m, h (a + (s : ZMod L))))
      = ∑ r ∈ Finset.range m, ∑ s ∈ Finset.range m,
          ∑ b : ZMod L, h b * h (b + ((s : ZMod L) - (r : ZMod L))) := by
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  refine Fintype.sum_equiv (Equiv.addRight (r : ZMod L))
    (fun a => h (a + r) * h (a + s)) (fun b => h b * h (b + ((s : ZMod L) - r))) (fun a => ?_)
  simp only [Equiv.coe_addRight]
  congr 2
  ring

#print axioms window_sq_sum

/-- **Weighted (deformed) window-sum identity — discharges `hsum` (foundational).** For deformed windows
`Bₖ = ∑_{j<m} cⱼ • h(k+j)`, `∑ₖ Bₖ = (∑ⱼ cⱼ)•H` — each term carries total weight `∑ⱼ cⱼ`. Generalises
`window_sum` (all `cⱼ=1`). This is the GM `hsum` input with `c = ∑ⱼ cⱼ`. -/
theorem weighted_window_sum {N L : ℕ} [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ)
    (m : ℕ) (cc : ℕ → ℝ) :
    (∑ k : ZMod L, ∑ j ∈ Finset.range m, cc j • h (k + (j : ZMod L)))
      = (∑ j ∈ Finset.range m, cc j) • (∑ i, h i) := by
  rw [Finset.sum_comm, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.smul_sum, cyc_shift_sum]

#print axioms weighted_window_sum

/-- **Deformed window-square expansion — GM eq. 20 core (foundational).** For `Bₖ = ∑ⱼ cⱼ•h(k+j)`,
`∑ₖ Bₖ² = ∑ⱼ ∑ₛ (cⱼcₛ)•(∑_b h_b·h_{b+(s−j)})`. Generalises `window_sq_sum` (all `cⱼ=1`); the coefficient of
`Tδ = ∑_b h_b h_{b+δ}` is the autocorrelation `∑_{s−j=δ} cⱼcₛ`. This is the `∑ₖBₖ²` side of eq. 21 in `Tδ` form
— grouping its `Tδ` coefficients against `H²`'s (all-`1`) and cancelling `δ=0,±1` via the `α,β` choice is the
remaining eq.-21 algebra. -/
theorem weighted_window_sq_sum {N L : ℕ} [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ)
    (m : ℕ) (cc : ℕ → ℝ) :
    (∑ k : ZMod L, (∑ j ∈ Finset.range m, cc j • h (k + (j : ZMod L))) *
        (∑ s ∈ Finset.range m, cc s • h (k + (s : ZMod L))))
      = ∑ j ∈ Finset.range m, ∑ s ∈ Finset.range m,
          (cc j * cc s) • (∑ b : ZMod L, h b * h (b + ((s : ZMod L) - (j : ZMod L)))) := by
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  have hsmul : ∀ k : ZMod L, (cc j • h (k + (j : ZMod L))) * (cc s • h (k + (s : ZMod L)))
      = (cc j * cc s) • (h (k + (j : ZMod L)) * h (k + (s : ZMod L))) := by
    intro k; rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  simp_rw [hsmul]
  rw [← Finset.smul_sum]
  congr 1
  refine Fintype.sum_equiv (Equiv.addRight (j : ZMod L))
    (fun k => h (k + j) * h (k + s)) (fun b => h b * h (b + ((s : ZMod L) - j))) (fun k => ?_)
  simp only [Equiv.coe_addRight]
  congr 2
  ring

#print axioms weighted_window_sq_sum

/-- **`H²` in `Tδ` form — GM eq. 21's `H²` side (foundational).** `(∑_b h_b)² = ∑_δ ∑_b h_b·h_{b+δ}` — the full
square decomposes into pair-sums `Tδ = ∑_b h_b h_{b+δ}` over all cyclic offsets. With `weighted_window_sq_sum`
both sides of eq. 21 live in the common `Tδ` basis; matching `Tδ` coefficients (`H²`: all `1`; `∑Bₖ²`: the
autocorrelation `A_{|δ|}`) and cancelling `δ=0,±1` via `α,β` is the remaining eq.-21 algebra. -/
theorem chain_sq_expand {N L : ℕ} [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ) :
    (∑ b, h b) * (∑ b, h b) = ∑ δ : ZMod L, ∑ b : ZMod L, h b * h (b + δ) := by
  have step : (∑ b, h b) * (∑ b, h b) = ∑ b : ZMod L, ∑ δ : ZMod L, h b * h (b + δ) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    exact (Fintype.sum_equiv (Equiv.addLeft b) (fun δ => h b * h (b + δ)) (fun b' => h b * h b')
      (fun δ => by simp [Equiv.coe_addLeft])).symm
  rw [step, Finset.sum_comm]

#print axioms chain_sq_expand

/-- **Regroup a weighted sum by the fibers of an offset map (foundational).** For any weight `F`, offset map
`g : ι → ZMod L`, and matrix family `M`, `∑_p F p • M(g p) = ∑_δ (∑_{p: g p = δ} F p) • M δ`. This is the
structural core of GM eq. 21's coefficient cancellation: it turns the pair-indexed
`∑Bₖ² = ∑_{j,s}(cⱼcₛ)•T_{s−j}` into the `δ`-indexed form `∑_δ (∑_{s−j=δ} cⱼcₛ)•Tδ`, matching `H² = ∑_δ Tδ`.
The remaining eq.-21 work is then the scalar coefficient analysis (fiber sums `= A_{|δ|}`; cancel `δ=0,±1`). -/
theorem regroup_by_fiber {N L : ℕ} [NeZero L] {ι : Type*} (s : Finset ι)
    (F : ι → ℝ) (g : ι → ZMod L) (M : ZMod L → Matrix (Fin N) (Fin N) ℝ) :
    (∑ p ∈ s, F p • M (g p))
      = ∑ δ : ZMod L, (∑ p ∈ s.filter (fun p => g p = δ), F p) • M δ := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun p _ => Finset.mem_univ (g p)) (fun p => F p • M (g p))]
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [(Finset.mem_filter.mp hp).2]

#print axioms regroup_by_fiber

/-- **`∑ₖBₖ²` fully in the `δ`-indexed (`Tδ`) basis (foundational).** Feeding `weighted_window_sq_sum` through
`regroup_by_fiber`: `∑ₖBₖ² = ∑_δ (∑_{(j,s): s−j=δ} cⱼcₛ)•Tδ`. Now BOTH sides of eq. 21 are in the identical
`∑_δ (coef)•Tδ` form (`H² = ∑_δ 1•Tδ` by `chain_sq_expand`), so `H²+βH−α∑Bₖ² = ∑_δ (netcoef δ)•Tδ` term-by-term.
The remaining eq.-21 work is the scalar coefficient analysis: the fiber coefficient `∑_{s−j=δ}cⱼcₛ = A_{|δ|}`
(autocorrelation, `m>2n`) and `netcoef δ = 1+β[δ=0]−αA_{|δ|}` vanishing at `δ=0,±1`. -/
theorem weighted_window_sq_regrouped {N L : ℕ} [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ)
    (m : ℕ) (cc : ℕ → ℝ) :
    (∑ k : ZMod L, (∑ j ∈ Finset.range m, cc j • h (k + (j : ZMod L))) *
        (∑ s ∈ Finset.range m, cc s • h (k + (s : ZMod L))))
      = ∑ δ : ZMod L,
          (∑ p ∈ (Finset.range m ×ˢ Finset.range m).filter
              (fun p => (p.2 : ZMod L) - (p.1 : ZMod L) = δ), cc p.1 * cc p.2)
            • (∑ b : ZMod L, h b * h (b + δ)) := by
  rw [weighted_window_sq_sum, ← Finset.sum_product']
  exact regroup_by_fiber (Finset.range m ×ˢ Finset.range m) (fun p : ℕ × ℕ => cc p.1 * cc p.2)
    (fun p : ℕ × ℕ => (p.2 : ZMod L) - (p.1 : ZMod L)) (fun δ => ∑ b, h b * h (b + δ))

#print axioms weighted_window_sq_regrouped

/-- **Combine the three `Tδ`-sums into one net-coefficient sum (foundational).**
`(∑_δ T δ) + β•(T 0) − α•(∑_δ W δ•T δ) = ∑_δ (1 + β[δ=0] − α·W δ)•T δ`. With `T=Tδ`, `W δ = (fiber coef)`,
this collapses GM eq. 21's LHS to `∑_δ netcoef(δ)•Tδ`. -/
theorem combine_Tsum {N L : ℕ} [NeZero L] (T : ZMod L → Matrix (Fin N) (Fin N) ℝ)
    (W : ZMod L → ℝ) (α β : ℝ) :
    (∑ δ, T δ) + β • (T 0) - α • (∑ δ, (W δ) • T δ)
      = ∑ δ : ZMod L, ((1 : ℝ) + (if δ = 0 then β else 0) - α * W δ) • T δ := by
  rw [Finset.smul_sum]
  simp_rw [smul_smul, sub_smul, add_smul, one_smul, ite_smul, zero_smul]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ 0 (fun δ => β • T δ)]
  simp

#print axioms combine_Tsum

/-- **GM eq. 21 LHS collapsed to a single net-coefficient `Tδ`-sum (foundational).** The entire structural side
of eq. 21: `H² + β•H − α•∑ₖBₖ² = ∑_δ (1 + β[δ=0] − α·Wcoef δ)•Tδ`, where `Wcoef δ = ∑_{(j,s): s−j=δ} cⱼcₛ` is
the fiber (autocorrelation) coefficient. Assembles `chain_sq_expand` (`H²`), `weighted_window_sq_regrouped`
(`∑Bₖ²`), `H = T₀` (projectors), via `combine_Tsum`. What remains of eq. 21 is purely SCALAR: `Wcoef δ = A_{|δ|}`
(`m>2n`) and the net coefficient `1 + β[δ=0] − αA_{|δ|}` vanishing at `δ=0,±1` (via `α=1/A₁`, `β=α(A₀−A₁)`) and
`≥0` for `|δ|≥2` (autocorrelation) — then `psd_nonneg_smul_sum` + `Tdelta_posSemidef` give eq. 23. -/
theorem eq21_lhs {N L : ℕ} [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ)
    (hproj : ∀ b, h b * h b = h b) (m : ℕ) (cc : ℕ → ℝ) (α β : ℝ) :
    (∑ b, h b) * (∑ b, h b) + β • (∑ b, h b) - α • (∑ k : ZMod L,
        (∑ j ∈ Finset.range m, cc j • h (k + (j : ZMod L))) *
        (∑ s ∈ Finset.range m, cc s • h (k + (s : ZMod L))))
      = ∑ δ : ZMod L,
          ((1 : ℝ) + (if δ = 0 then β else 0)
            - α * (∑ p ∈ (Finset.range m ×ˢ Finset.range m).filter
                (fun p => (p.2 : ZMod L) - (p.1 : ZMod L) = δ), cc p.1 * cc p.2))
          • (∑ b : ZMod L, h b * h (b + δ)) := by
  have hH0 : (∑ b, h b) = ∑ b : ZMod L, h b * h (b + 0) := by
    simp only [add_zero]; exact Finset.sum_congr rfl (fun b _ => (hproj b).symm)
  rw [chain_sq_expand, weighted_window_sq_regrouped, hH0]
  exact combine_Tsum (fun δ => ∑ b : ZMod L, h b * h (b + δ))
    (fun δ => ∑ p ∈ (Finset.range m ×ˢ Finset.range m).filter
        (fun p => (p.2 : ZMod L) - (p.1 : ZMod L) = δ), cc p.1 * cc p.2) α β

#print axioms eq21_lhs

open Matrix in
/-- **GM eq. 23 as an operator inequality, modulo per-term PSD (foundational).** `H²+β•H−α•∑ₖBₖ² ⪰ 0` once each
net-coefficient term `(1+β[δ=0]−α·Wcoef δ)•Tδ` is PSD. Assembles `eq21_lhs` + `posSemidef_sum`. The hypothesis
`hterm` isolates exactly the remaining content: the coefficient vanishes at `δ=0,±1` (so those terms are `0`,
sidestepping that `T_{±1}` is not PSD) and is `≥0` for `|δ|≥2` with `Tδ⪰0` (`Tdelta_posSemidef`). With
`gm_gap_of_eq23` this delivers the GM bulk gap. -/
theorem eq23_of_terms {N L : ℕ} [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ)
    (hproj : ∀ b, h b * h b = h b) (m : ℕ) (cc : ℕ → ℝ) (α β : ℝ)
    (hterm : ∀ δ : ZMod L,
      (((1 : ℝ) + (if δ = 0 then β else 0)
        - α * (∑ p ∈ (Finset.range m ×ˢ Finset.range m).filter
            (fun p => (p.2 : ZMod L) - (p.1 : ZMod L) = δ), cc p.1 * cc p.2))
       • (∑ b : ZMod L, h b * h (b + δ))).PosSemidef) :
    ((∑ b, h b) * (∑ b, h b) + β • (∑ b, h b) - α • (∑ k : ZMod L,
        (∑ j ∈ Finset.range m, cc j • h (k + (j : ZMod L))) *
        (∑ s ∈ Finset.range m, cc s • h (k + (s : ZMod L))))).PosSemidef := by
  rw [eq21_lhs h hproj m cc α β]
  exact Matrix.posSemidef_sum Finset.univ (fun δ _ => hterm δ)

#print axioms eq23_of_terms

/-- **GM `α,β` cancellation (foundational).** With `α = A₁⁻¹` and `β = α(A₀−A₁)`, the net coefficients at `δ=0`
(`1 + β − αA₀`) and `δ=±1` (`1 − αA₁`) both vanish — the exact cancellation that zeroes eq. 21's `δ=0,±1`
terms (so `hterm` holds there without needing `T_{±1}` PSD). `A₀=∑cⱼ²`, `A₁=∑cⱼcⱼ₊₁`. -/
theorem gm_alpha_beta {A0 A1 : ℝ} (hA1 : A1 ≠ 0) :
    (1 : ℝ) + A1⁻¹ * (A0 - A1) - A1⁻¹ * A0 = 0 ∧ (1 : ℝ) - A1⁻¹ * A1 = 0 := by
  refine ⟨?_, ?_⟩ <;> field_simp <;> ring

#print axioms gm_alpha_beta

/-- **Fiber sum at offset `x` equals the autocorrelation `A_x = ∑_{j<m-x} cⱼcⱼ₊ₓ` (foundational).** For
`m + x ≤ L` (no wraparound), the pairs `(j,s)∈[0,m)²` with `(s:ZMod L)−(j:ZMod L)=(x:ZMod L)` are exactly the
shifted diagonal `s=j+x` (`j<m−x`) — the cast `ℕ→ZMod L` is injective on `[0,m+x)`. So the fiber coefficient
`Wcoef (x:ZMod L) = A_x`. Subsumes `δ=0` (`x=0`, `A₀=∑cⱼ²`) and `δ=1` (`x=1`, `A₁=∑cⱼcⱼ₊₁`), feeding
`gm_alpha_beta`; the general `x` is the far-offset case (with `A_x` nonincreasing by the Autocorrelation Lemma). -/
theorem fiber_sum_pos {L : ℕ} [NeZero L] (m x : ℕ) (hmx : m + x ≤ L) (cc : ℕ → ℝ) :
    (∑ p ∈ (Finset.range m ×ˢ Finset.range m).filter
        (fun p => (p.2 : ZMod L) - (p.1 : ZMod L) = (x : ZMod L)), cc p.1 * cc p.2)
      = ∑ j ∈ Finset.range (m - x), cc j * cc (j + x) := by
  rw [Finset.sum_filter, Finset.sum_product]
  have key : (∑ j ∈ Finset.range m, ∑ s ∈ Finset.range m,
        if (s : ZMod L) - (j : ZMod L) = (x : ZMod L) then cc j * cc s else 0)
      = ∑ j ∈ Finset.range m, if j + x ∈ Finset.range m then cc j * cc (j + x) else 0 := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjm : j < m := Finset.mem_range.mp hj
    have hjxL : j + x < L := by omega
    have hcond : (∑ s ∈ Finset.range m, if (s : ZMod L) - (j : ZMod L) = (x : ZMod L) then cc j * cc s else 0)
        = ∑ s ∈ Finset.range m, if s = j + x then cc j * cc s else 0 := by
      refine Finset.sum_congr rfl (fun s hs => ?_)
      have hsL : s < L := lt_of_lt_of_le (Finset.mem_range.mp hs) (by omega)
      refine if_congr ?_ rfl rfl
      rw [sub_eq_iff_eq_add, show (x : ZMod L) + (j : ZMod L) = ((j + x : ℕ) : ZMod L) by push_cast; ring]
      constructor
      · intro h
        have hv := congrArg ZMod.val h
        rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hsL, Nat.mod_eq_of_lt hjxL] at hv
      · intro h; rw [h]
    rw [hcond, Finset.sum_ite_eq' (Finset.range m) (j + x) (fun s => cc j * cc s)]
  rw [key, ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

#print axioms fiber_sum_pos

/-- **Fiber sum at offset `−x` also equals `A_x` (foundational).** By symmetry the `(s:ZMod L)−(j:ZMod L)=−x`
fiber is the shifted diagonal `j=s+x`, giving `∑_{s<m-x} c_{s+x}c_s = A_x`. With `fiber_sum_pos` this covers
every non-empty fiber `δ` (positive and negative integer offsets `|δ|<m`); all others are empty (`Wcoef δ=0`). -/
theorem fiber_sum_neg {L : ℕ} [NeZero L] (m x : ℕ) (hmx : m + x ≤ L) (cc : ℕ → ℝ) :
    (∑ p ∈ (Finset.range m ×ˢ Finset.range m).filter
        (fun p => (p.2 : ZMod L) - (p.1 : ZMod L) = -(x : ZMod L)), cc p.1 * cc p.2)
      = ∑ j ∈ Finset.range (m - x), cc (j + x) * cc j := by
  rw [Finset.sum_filter, Finset.sum_product, Finset.sum_comm]
  have key : (∑ s ∈ Finset.range m, ∑ j ∈ Finset.range m,
        if (s : ZMod L) - (j : ZMod L) = -(x : ZMod L) then cc j * cc s else 0)
      = ∑ s ∈ Finset.range m, if s + x ∈ Finset.range m then cc (s + x) * cc s else 0 := by
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hsm : s < m := Finset.mem_range.mp hs
    have hsxL : s + x < L := by omega
    have hcond : (∑ j ∈ Finset.range m, if (s : ZMod L) - (j : ZMod L) = -(x : ZMod L) then cc j * cc s else 0)
        = ∑ j ∈ Finset.range m, if j = s + x then cc j * cc s else 0 := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hjL : j < L := lt_of_lt_of_le (Finset.mem_range.mp hj) (by omega)
      refine if_congr ?_ rfl rfl
      constructor
      · intro h
        have hje : ((j : ℕ) : ZMod L) = ((s + x : ℕ) : ZMod L) := by push_cast; linear_combination -h
        have hv := congrArg ZMod.val hje
        rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hjL, Nat.mod_eq_of_lt hsxL] at hv
      · intro h; subst h; push_cast; ring
    rw [hcond, Finset.sum_ite_eq' (Finset.range m) (s + x) (fun j => cc j * cc s)]
  rw [key, ← Finset.sum_filter]
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

#print axioms fiber_sum_neg

/-- **Discharge `hterm` from nonneg coefficients + PSD-where-nonzero (foundational).** Each `aᵢ•Mᵢ ⪰ 0` when
`aᵢ≥0` everywhere and `Mᵢ⪰0` wherever `aᵢ≠0`. Separates the SCALAR part (`hnn`: net coefficients `≥0`) from the
PHYSICAL part (`hpsd`: `Tδ⪰0` where the coefficient is nonzero): the `δ=0,±1` terms have coefficient `0`
(`gm_alpha_beta`), so `Tδ` need not be PSD there (`T_{±1}` isn't). This is exactly the hypothesis `hterm` of
`eq23_of_terms`. -/
theorem hterm_of_nonneg_psd {N : ℕ} {ι : Type*} (a : ι → ℝ) (M : ι → Matrix (Fin N) (Fin N) ℝ)
    (hnn : ∀ i, 0 ≤ a i) (hpsd : ∀ i, a i ≠ 0 → (M i).PosSemidef) :
    ∀ i, (a i • M i).PosSemidef := by
  intro i
  by_cases h : a i = 0
  · rw [h, zero_smul]; exact ⟨Matrix.isHermitian_zero, fun x => by simp⟩
  · exact (hpsd i h).smul (hnn i)

#print axioms hterm_of_nonneg_psd

/-- **Empty fiber in the middle band (foundational).** For `δ.val ∈ [m, L−m]` (`2m ≤ L`), no pair
`(j,s)∈[0,m)²` has `(s:ZMod L)−(j:ZMod L)=δ` — the difference's val always lands in `[0,m)∪(L−m,L)`, so
`Wcoef δ = 0` there (`netcoef δ = 1 ≥ 0`, `Tδ` far-commuting). The middle-band case of `hnn`. -/
theorem fiber_empty {L : ℕ} [NeZero L] (m : ℕ) (hmL : 2 * m ≤ L) (δ : ZMod L)
    (hd1 : m ≤ δ.val) (hd2 : δ.val ≤ L - m) :
    (Finset.range m ×ˢ Finset.range m).filter (fun p => (p.2 : ZMod L) - (p.1 : ZMod L) = δ) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro p hp
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
  intro hcon
  have heq : (p.2 : ZMod L) = δ + (p.1 : ZMod L) := by rw [← hcon]; ring
  have hv := congrArg ZMod.val heq
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (show p.2 < L by omega), ZMod.val_add, ZMod.val_natCast,
    Nat.mod_eq_of_lt (show p.1 < L by omega), Nat.mod_eq_of_lt (show δ.val + p.1 < L by omega)] at hv
  omega

#print axioms fiber_empty

/-- **Net-coefficient nonnegativity for `cⱼ=1` (the `hnn` input; foundational).** With plain Knabe windows
(`cⱼ=1`), `α=β=(m−1)⁻¹`, the net coefficient `1 + β[δ=0] − α·Wcoef δ ≥ 0` for EVERY `δ` (`2m≤L`, `m≥2`). Proof
by casing `δ.val`: `0`→`Wcoef=m` (net `=0`); `[1,m)`→`Wcoef=m−δ.val` (`fiber_sum_pos`); `[m,L−m]`→`Wcoef=0`
(`fiber_empty`); `(L−m,L)`→`Wcoef=m−(L−δ.val)` (`fiber_sum_neg`); each `≤ m−1`, so `α·Wcoef ≤ 1`. This is the
SCALAR half of `hterm` — the Autocorrelation Lemma made trivial by `cⱼ=1` (`Aₓ=m−x`). -/
theorem hnn_c1 {L : ℕ} [NeZero L] (m : ℕ) (hm2 : 2 ≤ m) (hmL : 2 * m ≤ L) (δ : ZMod L) :
    0 ≤ 1 + (if δ = 0 then ((m : ℝ) - 1)⁻¹ else 0)
        - ((m : ℝ) - 1)⁻¹ * (∑ _p ∈ (Finset.range m ×ˢ Finset.range m).filter
            (fun p => (p.2 : ZMod L) - (p.1 : ZMod L) = δ), (1 : ℝ)) := by
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    linarith
  have hαpos : (0 : ℝ) ≤ ((m : ℝ) - 1)⁻¹ := le_of_lt (inv_pos.mpr hm1)
  have hδd : δ = ((δ.val : ℕ) : ZMod L) := (ZMod.natCast_rightInverse δ).symm
  have hvL : δ.val < L := ZMod.val_lt δ
  by_cases hδ0 : δ = 0
  · subst hδ0
    have hmx0 : m + 0 ≤ L := by omega
    have hfib := fiber_sum_pos m 0 hmx0 (fun _ => (1 : ℝ))
    simp only [Nat.cast_zero, mul_one, Nat.sub_zero] at hfib
    rw [if_pos rfl, hfib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have harith : ((m : ℝ) - 1)⁻¹ * (m : ℝ) = 1 + ((m : ℝ) - 1)⁻¹ := by field_simp; ring
    linarith
  · have hval : 0 < δ.val := by
      rcases Nat.eq_zero_or_pos δ.val with h | h
      · exact absurd (by rw [hδd, h]; simp) hδ0
      · exact h
    have hSle : (∑ _p ∈ (Finset.range m ×ˢ Finset.range m).filter
        (fun p => (p.2 : ZMod L) - (p.1 : ZMod L) = δ), (1 : ℝ)) ≤ (m : ℝ) - 1 := by
      rcases lt_or_ge δ.val m with hlt | hge
      · have hmxp : m + δ.val ≤ L := by omega
        have hfib := fiber_sum_pos m δ.val hmxp (fun _ => (1 : ℝ))
        simp only [mul_one] at hfib
        rw [← hδd] at hfib
        rw [hfib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        have hle : (m - δ.val : ℕ) ≤ m - 1 := by omega
        calc ((m - δ.val : ℕ) : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hle
          _ = (m : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      · rcases lt_or_ge δ.val (L - m + 1) with hmid | hbig
        · rw [fiber_empty m hmL δ hge (by omega), Finset.sum_empty]
          linarith
        · have hxL : δ.val ≤ L := le_of_lt hvL
          have hx : δ = -((L - δ.val : ℕ) : ZMod L) := by
            have hc : ((L - δ.val : ℕ) : ZMod L) = -δ := by
              rw [Nat.cast_sub hxL, ZMod.natCast_self, zero_sub, ← hδd]
            rw [hc, neg_neg]
          have hmxn : m + (L - δ.val) ≤ L := by omega
          have hfib := fiber_sum_neg m (L - δ.val) hmxn (fun _ => (1 : ℝ))
          simp only [mul_one] at hfib
          rw [← hx] at hfib
          rw [hfib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          have hle : (m - (L - δ.val) : ℕ) ≤ m - 1 := by omega
          calc ((m - (L - δ.val) : ℕ) : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hle
            _ = (m : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [if_neg hδ0]
    have hmul := mul_le_mul_of_nonneg_left hSle hαpos
    rw [inv_mul_cancel₀ hm1.ne'] at hmul
    linarith

#print axioms hnn_c1

/-- c=1 fiber sum at positive offset `x` = `m − x`. -/
theorem fiber_c1_pos {L : ℕ} [NeZero L] (m x : ℕ) (hmx : m + x ≤ L) :
    (∑ p ∈ (Finset.range m ×ˢ Finset.range m).filter
        (fun p => (p.2 : ZMod L) - (p.1 : ZMod L) = (x : ZMod L)),
      (fun _ => (1 : ℝ)) p.1 * (fun _ => (1 : ℝ)) p.2) = ((m - x : ℕ) : ℝ) := by
  rw [fiber_sum_pos m x hmx (fun _ => (1 : ℝ))]; simp

/-- c=1 fiber sum at negative offset `−x` = `m − x`. -/
theorem fiber_c1_neg {L : ℕ} [NeZero L] (m x : ℕ) (hmx : m + x ≤ L) :
    (∑ p ∈ (Finset.range m ×ˢ Finset.range m).filter
        (fun p => (p.2 : ZMod L) - (p.1 : ZMod L) = -(x : ZMod L)),
      (fun _ => (1 : ℝ)) p.1 * (fun _ => (1 : ℝ)) p.2) = ((m - x : ℕ) : ℝ) := by
  rw [fiber_sum_neg m x hmx (fun _ => (1 : ℝ))]; simp

/-- **The abstract GM/Knabe eq. 23 operator inequality, fully machine-checked (foundational).** For a
frustration-free nearest-neighbour projector chain (`h b` Hermitian idempotents on `ZMod L`), with the plain
Knabe windows `Bₖ = ∑_{j<m} h(k+j)` (`cⱼ=1`), `α=β=(m−1)⁻¹`, the operator inequality
`(∑h)² + α•(∑h) − α•(∑ₖBₖ²) ⪰ 0` holds — **given only the physical commuting structure** `hpsd`
(`Tδ=∑_b h_b h_{b+δ} ⪰ 0` for `δ∉{0,±1}`, i.e. disjoint bonds commute). Wires `eq23_of_terms` +
`hterm_of_nonneg_psd` + `hnn_c1` (scalar, DONE) + the `δ=0,±1` cancellations (`fiber_c1_pos/neg` + `field_simp`).
This closes the abstract GM reduction: the ONLY remaining input is `hpsd` (the binding to actual KS/Wilson bond
projectors), plus GM Lemma 4 to pass from eq. 23 to the gap (`gm_gap_of_eq23`). -/
theorem gm_eq23_c1 {N L : ℕ} [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ)
    (hproj : ∀ b, h b * h b = h b) (m : ℕ) (hm2 : 2 ≤ m) (hmL : 2 * m ≤ L)
    (hpsd : ∀ δ : ZMod L, δ ≠ 0 → δ ≠ 1 → δ ≠ -1 → (∑ b : ZMod L, h b * h (b + δ)).PosSemidef) :
    ((∑ b, h b) * (∑ b, h b) + ((m : ℝ) - 1)⁻¹ • (∑ b, h b)
      - ((m : ℝ) - 1)⁻¹ • (∑ k : ZMod L, (∑ j ∈ Finset.range m, (1 : ℝ) • h (k + (j : ZMod L)))
          * (∑ s ∈ Finset.range m, (1 : ℝ) • h (k + (s : ZMod L))))).PosSemidef := by
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    linarith
  have h1ne : (1 : ZMod L) ≠ 0 := by
    haveI : Fact (1 < L) := ⟨by omega⟩
    exact one_ne_zero
  refine eq23_of_terms h hproj m (fun _ => (1 : ℝ)) _ _ ?_
  apply hterm_of_nonneg_psd
  · intro δ; simpa using hnn_c1 m hm2 hmL δ
  · intro δ hne
    apply hpsd δ
    · rintro rfl
      apply hne
      rw [if_pos rfl, show ((0 : ZMod L)) = ((0 : ℕ) : ZMod L) by simp, fiber_c1_pos m 0 (by omega)]
      simp only [Nat.sub_zero]; field_simp; ring
    · rintro rfl
      apply hne
      rw [if_neg h1ne, show ((1 : ZMod L)) = ((1 : ℕ) : ZMod L) by simp, fiber_c1_pos m 1 (by omega)]
      rw [Nat.cast_sub (by omega : 1 ≤ m)]; field_simp; push_cast; ring
    · rintro rfl
      apply hne
      have hne1 : (-1 : ZMod L) ≠ 0 := by simpa using h1ne
      rw [if_neg hne1, show ((-1 : ZMod L)) = -((1 : ℕ) : ZMod L) by simp, fiber_c1_neg m 1 (by omega)]
      rw [Nat.cast_sub (by omega : 1 ≤ m)]; field_simp; push_cast; ring

#print axioms gm_eq23_c1

open Matrix in
/-- Quadratic form of a PSD matrix is nonneg (real), dotProduct form. -/
theorem psd_form_nonneg {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : M.PosSemidef) (x : Fin N → ℝ) :
    0 ≤ x ⬝ᵥ (M *ᵥ x) := by
  have := hM.re_dotProduct_nonneg x
  simpa [star_trivial, RCLike.re_to_real] using this

/-- Sum of Hermitian matrices is Hermitian. -/
theorem isHermitian_sum {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin N) (Fin N) ℝ)
    (hf : ∀ i ∈ s, (f i).IsHermitian) : (∑ i ∈ s, f i).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun i hi => (hf i hi).eq)

#print axioms psd_form_nonneg
#print axioms isHermitian_sum

open Matrix in
/-- **eq.-23 FORM inequality at any `x`, from the operator PSD (foundational).** Converts `gm_eq23_c1`'s
`(H²+α•H−α•∑ₖBₖ²)⪰0` into `α∑ₖ⟨Bₖx,Bₖx⟩ ≤ ⟨Hx,Hx⟩ + α⟨x,Hx⟩` — the `heq23` hypothesis of `gm_gap_of_eq23`. Via
`psd_form_nonneg` + the symmetric-adjoint expansion (`sadj`, `mulVec_mulVec`, `sum_mulVec`). -/
theorem eq23_form_of_psd {N : ℕ} {ι : Type*} [Fintype ι]
    {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {B : ι → Matrix (Fin N) (Fin N) ℝ} (hB : ∀ k, (B k).IsHermitian) {α : ℝ}
    (hpsd : (H * H + α • H - α • (∑ k, B k * B k)).PosSemidef) (x : Fin N → ℝ) :
    α * (∑ k, (B k *ᵥ x) ⬝ᵥ (B k *ᵥ x)) ≤ (H *ᵥ x) ⬝ᵥ (H *ᵥ x) + α * (x ⬝ᵥ (H *ᵥ x)) := by
  have hnn := psd_form_nonneg hpsd x
  have hHsq : x ⬝ᵥ ((H * H) *ᵥ x) = (H *ᵥ x) ⬝ᵥ (H *ᵥ x) := by
    rw [← mulVec_mulVec]; exact (sadj hH x (H *ᵥ x)).symm
  have hBsq : x ⬝ᵥ ((∑ k, B k * B k) *ᵥ x) = ∑ k, (B k *ᵥ x) ⬝ᵥ (B k *ᵥ x) := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← mulVec_mulVec]; exact (sadj (hB k) x (B k *ᵥ x)).symm
  rw [sub_mulVec, add_mulVec, dotProduct_sub, dotProduct_add, smul_mulVec, smul_mulVec,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, hHsq, hBsq] at hnn
  linarith

#print axioms eq23_form_of_psd

open Matrix in
/-- **Gosset–Mozgunov assembly — FAITHFUL state-level core reduction (foundational).** Following GM
(arXiv 1512.00088) exactly: for the low-energy eigenstate `ψ` of `H` (`Hψ = λψ`, `λ > 0` its gap), given
(i) the deformed-window sum `∑ₖ Bₖ = c•H` (`weighted_window_sum`, `c = ∑ⱼ cⱼ`), (ii) GM's **Lemma 4**
`⟨ψ|Bₖ²|ψ⟩ ≥ γ'⟨ψ|Bₖ|ψ⟩` (a STATE-level bound on `ψ`, `γ' = εₙ·(∑cⱼ)/(n−1)` — NOT the full operator inequality
`Bₖ²⪰γ'Bₖ`, which GM note does not hold simply), and (iii) **eq. 23** `α·∑ₖBₖ² ⪯ H² + β·H`, the eigenvalue
obeys `λ ≥ αγ'c − β`. Proof: expectation of eq. 23 in `ψ` — `⟨ψ|H²|ψ⟩=λ²`, `⟨ψ|H|ψ⟩=λ`, and Lemma 4 + the sum
bound the `∑Bₖ²` side by `αγ'cλ`; divide by `λ>0`. This **isolates eq. 23 as the SINGLE remaining research
input** (`hsum` = `weighted_window_sum` ✓, `hlem4` = GM Lemma 4). GM prove eq. 23 via their **1D Autocorrelation
Lemma**: eq. 21 is the EQUALITY `H² − α∑Bₖ² + βH = ∑_{d(i,j)≥2}(1 − α·A_{d(i,j)})hᵢhⱼ` (`A_d=∑ᵣcᵣcᵣ₊d`; the
`H`/nearest-neighbour terms cancel by the `α,β` choice), PSD because `hᵢhⱼ⪰0` (commuting projectors, `d≥2`) and
`1−α·A_d≥0` (`A_d ≤ A_1 = 1/α`, autocorrelation monotone). Foundational (`propext, Classical.choice, Quot.sound`). -/
theorem gm_gap_of_eq23 {N : ℕ} {ι : Type*} [Fintype ι]
    {H : Matrix (Fin N) (Fin N) ℝ} {B : ι → Matrix (Fin N) (Fin N) ℝ} {α β γ' c lam : ℝ}
    {ψ : Fin N → ℝ} (hψ : H *ᵥ ψ = lam • ψ) (hψ0 : ψ ⬝ᵥ ψ ≠ 0) (hlam : 0 < lam)
    (hsum : ∑ k, B k = c • H)
    (hlem4 : ∀ k, γ' * (ψ ⬝ᵥ (B k *ᵥ ψ)) ≤ (B k *ᵥ ψ) ⬝ᵥ (B k *ᵥ ψ))
    (heq23 : α * (∑ k, (B k *ᵥ ψ) ⬝ᵥ (B k *ᵥ ψ)) ≤ (H *ᵥ ψ) ⬝ᵥ (H *ᵥ ψ) + β * (ψ ⬝ᵥ (H *ᵥ ψ)))
    (hα : 0 ≤ α) :
    α * γ' * c - β ≤ lam := by
  have hself : (0 : ℝ) ≤ ψ ⬝ᵥ ψ := by
    show (0 : ℝ) ≤ ∑ i, ψ i * ψ i
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (ψ i))
  have hnn : 0 < ψ ⬝ᵥ ψ := lt_of_le_of_ne hself (Ne.symm hψ0)
  have hHψ : ψ ⬝ᵥ (H *ᵥ ψ) = lam * (ψ ⬝ᵥ ψ) := by rw [hψ, dotProduct_smul, smul_eq_mul]
  have hH2ψ : (H *ᵥ ψ) ⬝ᵥ (H *ᵥ ψ) = lam ^ 2 * (ψ ⬝ᵥ ψ) := by
    rw [hψ, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring
  have hL4 : γ' * c * (lam * (ψ ⬝ᵥ ψ)) ≤ ∑ k, (B k *ᵥ ψ) ⬝ᵥ (B k *ᵥ ψ) := by
    have h1 : γ' * (∑ k, ψ ⬝ᵥ (B k *ᵥ ψ)) ≤ ∑ k, (B k *ᵥ ψ) ⬝ᵥ (B k *ᵥ ψ) := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun k _ => hlem4 k)
    have h2 : (∑ k, ψ ⬝ᵥ (B k *ᵥ ψ)) = c * (ψ ⬝ᵥ (H *ᵥ ψ)) := by
      rw [← dotProduct_sum, ← Matrix.sum_mulVec, hsum, smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [h2, hHψ] at h1; nlinarith [h1]
  rw [hH2ψ, hHψ] at heq23
  have hpos : 0 < lam * (ψ ⬝ᵥ ψ) := mul_pos hlam hnn
  nlinarith [mul_le_mul_of_nonneg_left hL4 hα, heq23, hpos]

#print axioms gm_gap_of_eq23

open Matrix in
/-- **The abstract Knabe/Gosset–Mozgunov bulk gap for the plain-window chain — CAPSTONE (foundational).**
For a frustration-free nearest-neighbour projector chain (`h b` Hermitian idempotents on `ZMod L`, `2≤m`,
`2m≤L`), given (i) the commuting structure `hpsd` (`Tδ⪰0` for `δ∉{0,±1}`), (ii) a low-energy eigenstate `ψ`
of `H=∑h` (`Hψ=λψ`, `λ>0`), and (iii) GM's Lemma 4 `hlem4` on `ψ`, the eigenvalue obeys the Knabe finite-size
bound `λ ≥ (m−1)⁻¹·γ'·m − (m−1)⁻¹`. Assembles `gm_eq23_c1` (the abstract eq. 23 operator inequality) →
`eq23_form_of_psd` (form inequality at `ψ`) → `gm_gap_of_eq23` (gap), with `hsum=∑ₖBₖ=m•H`
(`weighted_window_sum`). This is the ENTIRE abstract Knabe/GM finite-size criterion, machine-checked and
axiom-free; the three physical inputs (`hpsd`, `ψ`, `hlem4`) are the sole remaining binding to the actual
Kogut–Susskind/Wilson bond projectors. -/
theorem gm_gap_c1 {N L : ℕ} [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ)
    (hherm : ∀ b, (h b).IsHermitian) (hproj : ∀ b, h b * h b = h b)
    (m : ℕ) (hm2 : 2 ≤ m) (hmL : 2 * m ≤ L)
    (hpsd : ∀ δ : ZMod L, δ ≠ 0 → δ ≠ 1 → δ ≠ -1 → (∑ b : ZMod L, h b * h (b + δ)).PosSemidef)
    {γ' lam : ℝ} {ψ : Fin N → ℝ}
    (hψ : (∑ b, h b) *ᵥ ψ = lam • ψ) (hψ0 : ψ ⬝ᵥ ψ ≠ 0) (hlam : 0 < lam)
    (hlem4 : ∀ k : ZMod L,
        γ' * (ψ ⬝ᵥ ((∑ j ∈ Finset.range m, (1 : ℝ) • h (k + (j : ZMod L))) *ᵥ ψ))
          ≤ ((∑ j ∈ Finset.range m, (1 : ℝ) • h (k + (j : ZMod L))) *ᵥ ψ)
              ⬝ᵥ ((∑ j ∈ Finset.range m, (1 : ℝ) • h (k + (j : ZMod L))) *ᵥ ψ)) :
    ((m : ℝ) - 1)⁻¹ * γ' * (m : ℝ) - ((m : ℝ) - 1)⁻¹ ≤ lam := by
  have hH : (∑ b, h b).IsHermitian := isHermitian_sum _ _ (fun b _ => hherm b)
  have hB : ∀ k : ZMod L, (∑ j ∈ Finset.range m, (1 : ℝ) • h (k + (j : ZMod L))).IsHermitian :=
    fun k => isHermitian_sum _ _ (fun j _ => by rw [one_smul]; exact hherm _)
  have heq23 := eq23_form_of_psd hH hB (gm_eq23_c1 h hproj m hm2 hmL hpsd) ψ
  have hsum : (∑ k : ZMod L, ∑ j ∈ Finset.range m, (1 : ℝ) • h (k + (j : ZMod L)))
      = (m : ℝ) • (∑ b, h b) := by
    have := weighted_window_sum h m (fun _ => (1 : ℝ))
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
  have hα : (0 : ℝ) ≤ ((m : ℝ) - 1)⁻¹ := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    exact inv_nonneg.mpr (by linarith)
  exact gm_gap_of_eq23 hψ hψ0 hlam hsum hlem4 heq23 hα

#print axioms gm_gap_c1

open Matrix in
/-- **`gm_gap_c1` is non-vacuous (foundational).** The commuting-projector chain `h b = diag(0,1)` on `ZMod (2m)`
satisfies all hypotheses of `gm_gap_c1`, with low-energy eigenstate `ψ=(0,1)` (`Hψ=(2m)ψ`); the theorem then
yields the Knabe bound `(m−1)⁻¹·m·m − (m−1)⁻¹ = m+1 ≤ 2m`. So the abstract Knabe/GM gap theorem is not vacuous —
its hypotheses are jointly satisfiable and deliver a genuine positive gap (cf. `GappedExample`). -/
theorem knabe_gap_demo (m : ℕ) (hm2 : 2 ≤ m) :
    ((m : ℝ) - 1)⁻¹ * (m : ℝ) * (m : ℝ) - ((m : ℝ) - 1)⁻¹ ≤ ((2 * m : ℕ) : ℝ) := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  set P : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal (fun i => if i = 1 then (1 : ℝ) else 0) with hPdef
  set ψ : Fin 2 → ℝ := fun i => if i = 1 then (1 : ℝ) else 0 with hψdef
  have hPψ : P *ᵥ ψ = ψ := by
    rw [hPdef]; funext i; rw [Matrix.mulVec_diagonal]; fin_cases i <;> simp [hψdef]
  have hPh : P.IsHermitian := by rw [hPdef]; exact Matrix.isHermitian_diagonal _
  have hPP : P * P = P := by
    rw [hPdef, Matrix.diagonal_mul_diagonal]; congr 1; funext i; fin_cases i <;> simp [hψdef]
  have hPpsd : P.PosSemidef := by
    rw [hPdef, Matrix.posSemidef_diagonal_iff]; intro i; fin_cases i <;> simp [hψdef]
  have hψψ : ψ ⬝ᵥ ψ = 1 := by rw [hψdef]; simp [dotProduct]
  have hHψ : (∑ _b : ZMod (2 * m), P) *ᵥ ψ = ((2 * m : ℕ) : ℝ) • ψ := by
    rw [Matrix.sum_mulVec]; simp_rw [hPψ]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, ← Nat.cast_smul_eq_nsmul ℝ]
  have hBψ : ∀ k : ZMod (2 * m),
      (∑ _j ∈ Finset.range m, (1 : ℝ) • P) *ᵥ ψ = (m : ℝ) • ψ := by
    intro k
    rw [Matrix.sum_mulVec]; simp_rw [smul_mulVec, hPψ, one_smul]
    rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ]
  have hlem4 : ∀ k : ZMod (2 * m),
      (m : ℝ) * (ψ ⬝ᵥ ((∑ _j ∈ Finset.range m, (1 : ℝ) • P) *ᵥ ψ))
        ≤ ((∑ _j ∈ Finset.range m, (1 : ℝ) • P) *ᵥ ψ) ⬝ᵥ ((∑ _j ∈ Finset.range m, (1 : ℝ) • P) *ᵥ ψ) := by
    intro k
    rw [hBψ k]; apply le_of_eq
    simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul, hψψ, mul_one]
  have hTpsd : ∀ δ : ZMod (2 * m), δ ≠ 0 → δ ≠ 1 → δ ≠ -1 →
      (∑ _b : ZMod (2 * m), P * P).PosSemidef := by
    intro δ _ _ _
    simp_rw [hPP]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, ← Nat.cast_smul_eq_nsmul ℝ]
    exact hPpsd.smul (by positivity)
  have hlam : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by
    have : 0 < 2 * m := by omega
    exact_mod_cast this
  exact gm_gap_c1 (fun _ : ZMod (2 * m) => P) (fun _ => hPh) (fun _ => hPP) m hm2 (by omega)
    hTpsd hHψ (by rw [hψψ]; norm_num) hlam hlem4

#print axioms knabe_gap_demo

/-- **Product of commuting projectors is PSD (foundational)** — the `d(i,j)≥2` terms of GM eq. 21. If `P,Q` are
symmetric idempotents (projectors) that commute, then `P*Q` is a symmetric idempotent, hence positive
semidefinite (`P*Q = (P*Q)ᴴ(P*Q)`). This is exactly why each far term `hᵢhⱼ ⪰ 0` in eq. 21's RHS. -/
theorem commuting_proj_mul_posSemidef {N : ℕ} {P Q : Matrix (Fin N) (Fin N) ℝ}
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hPi : P * P = P) (hQi : Q * Q = Q)
    (hPQ : P * Q = Q * P) : (P * Q).PosSemidef := by
  have hsymm : (P * Q).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, hP.eq, hQ.eq, ← hPQ]
  have hidem : (P * Q) * (P * Q) = P * Q := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q P Q, ← hPQ, Matrix.mul_assoc P Q Q, hQi, ← Matrix.mul_assoc P P Q, hPi]
  have hfac : P * Q = (P * Q)ᴴ * (P * Q) := by rw [hsymm.eq, hidem]
  rw [hfac]
  exact Matrix.posSemidef_conjTranspose_mul_self _

#print axioms commuting_proj_mul_posSemidef

/-- **`Tδ ⪰ 0` for far offsets (foundational).** `Tδ = ∑_b h_b·h_{b+δ}` is PSD when at offset `δ` every `h_b`
commutes with `h_{b+δ}` (disjoint bonds, `|δ|≥2`) and all `h_b` are projectors — each summand is a product of
commuting projectors (`commuting_proj_mul_posSemidef`), and a sum of PSD is PSD (`posSemidef_sum`). This is the
`d≥2` PSD input to GM eq. 21's RHS `∑_{|δ|≥2}(1−αA_{|δ|})Tδ ⪰ 0`. -/
theorem Tdelta_posSemidef {N L : ℕ} [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ) (δ : ZMod L)
    (hherm : ∀ b, (h b).IsHermitian) (hproj : ∀ b, h b * h b = h b)
    (hcomm : ∀ b, h b * h (b + δ) = h (b + δ) * h b) :
    (∑ b : ZMod L, h b * h (b + δ)).PosSemidef :=
  Matrix.posSemidef_sum Finset.univ
    (fun b _ => commuting_proj_mul_posSemidef (hherm b) (hherm (b + δ)) (hproj b) (hproj (b + δ)) (hcomm b))

#print axioms Tdelta_posSemidef

/-- **Nonneg-weighted sum of PSD is PSD (foundational).** `∑ᵢ aᵢ•Mᵢ ⪰ 0` when each `aᵢ ≥ 0` and `Mᵢ ⪰ 0`. With
`Tdelta_posSemidef` this gives GM eq. 21's RHS `∑_{|δ|≥2}(1−αA_{|δ|})•Tδ ⪰ 0` (the coefficients `1−αA_{|δ|}≥0`
by the autocorrelation lemma). Combined with the eq.-21 EQUALITY this yields eq. 23 `H²+βH ⪰ α∑Bₖ²`. -/
theorem psd_nonneg_smul_sum {N : ℕ} {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (M : ι → Matrix (Fin N) (Fin N) ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hM : ∀ i ∈ s, (M i).PosSemidef) :
    (∑ i ∈ s, a i • M i).PosSemidef :=
  Matrix.posSemidef_sum s (fun i hi => (hM i hi).smul (ha i hi))

#print axioms psd_nonneg_smul_sum

/-! ### (step 5) The general-`jmax` cell gap on the strong-coupling window, via `interacting_cell_gap`

The single-plaquette Kogut–Susskind cell truncated at `jmax` is the tridiagonal `diagonal(i(i+2)/4) + (−λ)·nn`.
`interacting_cell_gap` applies: the Casimir margin (`i(i+2)/4 ≥ ¾` for `i ≥ 1`) via `diag_form_margin`, the
electric coupling has row-sum `≤ 2λ` via `coupling_form_lower`, so the general-`jmax` cell gap is `≥ κ₀` for
`λ ≤ (¾−κ₀)/2` — extending `Hcell2`/`Hcell3` to every truncation on the strong-coupling window. -/

/-- Diagonal Casimir of the general-`jmax` cell. -/
noncomputable def cellDiag (jmax : ℕ) : Fin (2 * jmax + 1) → ℝ := fun i => (i.val : ℝ) * (i.val + 2) / 4

/-- Nearest-neighbour electric coupling `−λ` of the general-`jmax` cell. -/
noncomputable def cellOff (jmax : ℕ) (lam : ℝ) : Matrix (Fin (2 * jmax + 1)) (Fin (2 * jmax + 1)) ℝ :=
  Matrix.of fun i j => if i.val + 1 = j.val ∨ j.val + 1 = i.val then -lam else 0

theorem cellOff_symm (jmax : ℕ) (lam : ℝ) (i j : Fin (2 * jmax + 1)) :
    cellOff jmax lam i j = cellOff jmax lam j i := by
  simp only [cellOff, Matrix.of_apply]; congr 1; exact propext or_comm

theorem cellOff_rowsum (jmax : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) (i : Fin (2 * jmax + 1)) :
    ∑ j, |cellOff jmax lam i j| ≤ 2 * lam := by
  have habs : ∀ j, |cellOff jmax lam i j|
      = if i.val + 1 = j.val ∨ j.val + 1 = i.val then lam else 0 := by
    intro j
    simp only [cellOff, Matrix.of_apply]
    split
    · rw [abs_neg, abs_of_nonneg hlam]
    · exact abs_zero
  rw [Finset.sum_congr rfl (fun j _ => habs j), ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hlam
  have hle1 : ∀ P : Fin (2 * jmax + 1) → Prop, [DecidablePred P] →
      (∀ a b, P a → P b → a = b) → (Finset.univ.filter P).card ≤ 1 := by
    intro P _ hP
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    exact hP a b ha.2 hb.2
  have hsub : Finset.univ.filter (fun j : Fin (2 * jmax + 1) => i.val + 1 = j.val ∨ j.val + 1 = i.val)
      ⊆ Finset.univ.filter (fun j => i.val + 1 = j.val) ∪ Finset.univ.filter (fun j => j.val + 1 = i.val) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at *
    tauto
  have hcard : (Finset.univ.filter
      (fun j : Fin (2 * jmax + 1) => i.val + 1 = j.val ∨ j.val + 1 = i.val)).card ≤ 2 :=
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ + _ := Finset.card_union_le _ _
      _ ≤ 1 + 1 := by
          exact add_le_add (hle1 _ (fun a b ha hb => Fin.ext (ha.symm.trans hb)))
            (hle1 _ (fun a b ha hb => Fin.ext (by omega)))
      _ = 2 := rfl
  exact_mod_cast hcard

/-- **(step 5) The general-`jmax` single-cell gap `≥ κ₀` on the strong-coupling window.** The `jmax`-truncated
single-plaquette Kogut–Susskind cell `diagonal(i(i+2)/4) + (−λ)·nn` has spectral gap `≥ κ₀` — a ground with
every other eigenvalue `≥ κ₀` above — for every coupling `λ ≤ (¾−κ₀)/2`, at every truncation `jmax`. Extends
`Hcell2` (2-state) / `Hcell3` (3-state) to all `jmax` on the strong-coupling window, via `interacting_cell_gap`.
Foundation-only. (Full-λ is the Feshbach tail; strong coupling is where the cell picture is sharpest.) -/
theorem cell_general_gap (jmax : ℕ) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam : 2 * lam ≤ 3 / 4 - κ₀YM)
    (hH : (Matrix.diagonal (cellDiag jmax) + cellOff jmax lam).IsHermitian) :
    ∃ j₀ : Fin (2 * jmax + 1), ∀ i, i ≠ j₀ → κ₀YM ≤ hH.eigenvalues i - hH.eigenvalues j₀ := by
  refine interacting_cell_gap (cellDiag jmax) (cellOff jmax lam) 0 ?_ ?_ (cellOff_symm jmax lam) ?_
    (c := 2 * lam) hlam ?_ hH
  · simp [cellDiag]
  · intro i hi
    have h1 : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr fun h => hi (Fin.ext h)
    have h1r : (1 : ℝ) ≤ (i.val : ℝ) := by exact_mod_cast h1
    simp only [cellDiag]; nlinarith [h1r]
  · simp [cellOff]
  · exact cellOff_rowsum jmax lam hlam0

#print axioms cell_general_gap
#print axioms gap_of_operator_sq_ge
#print axioms coupling_form_add
#print axioms interacting_cell_gap
#print axioms diag_form_margin
#print axioms coupling_form_lower
#print axioms product_subvacuum_le
#print axioms product_margin_le_cell_ceiling
#print axioms product_volume_gap
#print axioms product_volume_gap_concrete
#print axioms coupled_gap_of_coupling_bound

-- Sec 13 states this row as proved foundation-only; printing the footprint is what makes that
-- claim machine-checked rather than prose.
#print axioms Hcell2_clears_floor
#print axioms gap_uniform_of_cell_intensive
#print axioms gap_uniform_of_cell
#print axioms ym_volume_gap_cell_grounded

end MassGap.CellEnclosure
