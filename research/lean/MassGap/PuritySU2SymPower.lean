import MassGap.PuritySU2Character

/-!
# The spin-`n/2` representation `Sym^n ℂ²` and its character

`Sym^n ℂ²` is the space of degree-`n` homogeneous polynomials in two variables; a matrix `A` acts by
the substitution `X_i ↦ Σ_j A i j X_j`.

* `act A`: the substitution algebra map; `act_mul`: `act (A B) = act B ∘ act A` (a right action;
  `g ↦ act g⁻¹` is the left representation); `act_one`.
* `sym n = span {X₀^{n−k} X₁^k}`, with `sym_eq`: `sym n` is the degree-`n` homogeneous submodule.
* `symBasis n`: the monomial basis `X₀^{n−k} X₁^k`, `k = 0, …, n`.
* `symLin n A : sym n →ₗ sym n`, the action; `symChar n A`: its trace.
* `symChar_eq`: `symChar n A = Σ_k coeff_{X₀^{n−k} X₁^k} (A · X₀^{n−k} X₁^k)`.
* `symChar_conj`: `symChar n (P⁻¹ A P) = symChar n A`.
* `symChar_of_lower_eq_zero`: for `T 1 0 = 0`, `symChar n T = Σ_k T₀₀^{n−k} T₁₁^k`.
* `symChar_eq_weightSum`: `symChar n g = weightSum n z` at every eigenvalue `z` of `g ∈ SU(2)`.
* `symChar_eq_eval_U`: `symChar n g = U_n(τ g)`: `U_n(τ g)` is the trace of `g` on `Sym^n ℂ²`.
-/

namespace MassGap.PuritySU2SymPower

open MvPolynomial Polynomial.Chebyshev MassGap.PuritySU2Character
open MassGap.SUN (SU)
open scoped Matrix
open MassGap.ChainCoarseSeed (suTau)

/-- Two-by-two complex matrices. -/
abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

/-- Polynomials in two variables `X 0`, `X 1`. -/
abbrev P2 := MvPolynomial (Fin 2) ℂ

/-- The substitution `X_i ↦ Σ_j A i j X_j`. -/
noncomputable def act (A : M2) : P2 →ₐ[ℂ] P2 := aeval fun i => ∑ j, A i j • X j

theorem act_X (A : M2) (i : Fin 2) : act A (X i) = ∑ j, A i j • X j := aeval_X _ _

theorem act_mul (A B : M2) : act (A * B) = (act B).comp (act A) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, act_X, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_smul,
    add_smul, smul_add, smul_smul]
  abel

theorem act_one : act 1 = AlgHom.id ℂ P2 := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [act_X, Fin.sum_univ_two]

/-- The exponent `X₀^{n−k} X₁^k`. -/
noncomputable def e (n : ℕ) (k : Fin (n + 1)) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (n - (k : ℕ)) + Finsupp.single 1 (k : ℕ)

theorem e_one (n : ℕ) (k : Fin (n + 1)) : e n k 1 = k := by simp [e]

theorem e_injective (n : ℕ) : Function.Injective (e n) := fun j k h =>
  Fin.ext (by simpa [e_one] using congrArg (fun d => d 1) h)

theorem degree_e (n : ℕ) (k : Fin (n + 1)) : (e n k).degree = n := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  simp [e]
  omega

/-- The monomial `X₀^{n−k} X₁^k`. -/
noncomputable def mono (n : ℕ) (k : Fin (n + 1)) : P2 := monomial (e n k) 1

theorem mono_eq (n : ℕ) (k : Fin (n + 1)) : mono n k = X 0 ^ (n - (k : ℕ)) * X 1 ^ (k : ℕ) := by
  rw [mono, e, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, mul_one]

theorem linearIndependent_mono (n : ℕ) : LinearIndependent ℂ (mono n) := by
  have h : mono n = (basisMonomials (Fin 2) ℂ) ∘ e n := by
    funext k
    simp [mono, coe_basisMonomials]
  rw [h]
  exact (basisMonomials (Fin 2) ℂ).linearIndependent.comp (e n) (e_injective n)

/-- `Sym^n ℂ²`: the span of the degree-`n` monomials. -/
noncomputable def sym (n : ℕ) : Submodule ℂ P2 := Submodule.span ℂ (Set.range (mono n))

theorem sym_le (n : ℕ) : sym n ≤ homogeneousSubmodule (Fin 2) ℂ n :=
  Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact (mem_homogeneousSubmodule n _).2 (isHomogeneous_monomial _ (degree_e n k)))

theorem le_sym (n : ℕ) : homogeneousSubmodule (Fin 2) ℂ n ≤ sym n := by
  intro p hp
  have hh := (mem_homogeneousSubmodule n p).1 hp
  rw [p.as_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hdeg : d.degree = n := by
    by_contra hne
    exact (mem_support_iff.1 hd) (hh.coeff_eq_zero hne)
  have h01 : d 0 + d 1 = n := by
    rw [← hdeg, Finsupp.degree_eq_sum, Fin.sum_univ_two]
  have hk : d 1 < n + 1 := by omega
  have hde : d = e n ⟨d 1, hk⟩ := by
    ext i
    fin_cases i <;> simp [e] <;> omega
  have hm : monomial d (coeff d p) = coeff d p • mono n ⟨d 1, hk⟩ := by
    rw [mono, ← hde, smul_monomial, smul_eq_mul, mul_one]
  rw [hm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem sym_eq (n : ℕ) : sym n = homogeneousSubmodule (Fin 2) ℂ n :=
  le_antisymm (sym_le n) (le_sym n)

/-- The monomial basis `X₀^{n−k} X₁^k`, `k = 0, …, n`, of `Sym^n ℂ²`. -/
noncomputable def symBasis (n : ℕ) : Module.Basis (Fin (n + 1)) ℂ (sym n) :=
  Module.Basis.span (linearIndependent_mono n)

theorem symBasis_coe (n : ℕ) (k : Fin (n + 1)) : (symBasis n k : P2) = mono n k := by
  exact congrArg Subtype.val (Module.Basis.span_apply (linearIndependent_mono n) k)

instance (n : ℕ) : Module.Finite ℂ (sym n) := Module.Finite.of_basis (symBasis n)

theorem act_mem (n : ℕ) (A : M2) {p : P2} (hp : p ∈ sym n) : act A p ∈ sym n := by
  rw [sym_eq] at hp ⊢
  have hg : ∀ i, (∑ j, A i j • X j : P2).IsHomogeneous 1 := fun i =>
    (mem_homogeneousSubmodule 1 _).1 (Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X ℂ j)))
  have h := ((mem_homogeneousSubmodule n p).1 hp).aeval (fun i => ∑ j, A i j • X j) hg
  rw [one_mul] at h
  exact (mem_homogeneousSubmodule n _).2 h

/-- The action of `A` on `Sym^n ℂ²`. -/
noncomputable def symLin (n : ℕ) (A : M2) : sym n →ₗ[ℂ] sym n :=
  (act A).toLinearMap.restrict fun _ hp => act_mem n A hp

theorem symLin_coe (n : ℕ) (A : M2) (p : sym n) : (symLin n A p : P2) = act A p := rfl

theorem symLin_mul (n : ℕ) (A B : M2) : symLin n (A * B) = symLin n B ∘ₗ symLin n A :=
  LinearMap.ext fun p => Subtype.ext (by simp [symLin_coe, act_mul])

theorem symLin_one (n : ℕ) : symLin n 1 = LinearMap.id :=
  LinearMap.ext fun p => Subtype.ext (by simp [symLin_coe, act_one])

/-- The character of `Sym^n ℂ²`: the trace of `A` on it. -/
noncomputable def symChar (n : ℕ) (A : M2) : ℂ := LinearMap.trace ℂ (sym n) (symLin n A)

/-- The `X₀^{n−k} X₁^k` coordinate in the monomial basis is the `X₀^{n−k} X₁^k` coefficient. -/
theorem symBasis_repr (n : ℕ) (p : sym n) (k : Fin (n + 1)) :
    (symBasis n).repr p k = coeff (e n k) (p : P2) := by
  have h := congrArg (fun u : sym n => coeff (e n k) (u : P2)) ((symBasis n).sum_repr p)
  simp only [Submodule.coe_sum, Submodule.coe_smul, symBasis_coe, mono, coeff_sum, coeff_smul,
    coeff_monomial, (e_injective n).eq_iff, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  exact h

theorem symChar_eq (n : ℕ) (A : M2) :
    symChar n A = ∑ k, coeff (e n k) (act A (mono n k)) := by
  rw [symChar, LinearMap.trace_eq_matrix_trace ℂ (symBasis n), Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, symBasis_repr, symLin_coe, symBasis_coe]

/-- The character is a class function: `symChar n (P⁻¹ A P) = symChar n A`. -/
theorem symChar_conj (n : ℕ) (A P : M2) (hP : IsUnit P.det) :
    symChar n (P⁻¹ * A * P) = symChar n A := by
  rw [symChar, symLin_mul, symLin_mul, LinearMap.trace_comp_comm', LinearMap.comp_assoc,
    ← symLin_mul, Matrix.mul_nonsing_inv P hP, symLin_one, LinearMap.comp_id, symChar]

/-- `(a X₀ + b X₁)^m = (a X₀)^m + X₁ q`. -/
theorem pow_split (a b : ℂ) (m : ℕ) :
    ∃ q : P2, (a • X 0 + b • X 1 : P2) ^ m = (a • X 0) ^ m + X 1 * q := by
  obtain ⟨r, hr⟩ := sub_dvd_pow_sub_pow (a • X 0 + b • X 1 : P2) (a • X 0) m
  refine ⟨b • r, ?_⟩
  rw [← sub_eq_iff_eq_add', hr, add_sub_cancel_left, smul_mul_assoc, mul_smul_comm]

/-- The `X₀^{n−k} X₁^k` coefficient of `X₁^{k+1} r` is zero. -/
theorem coeff_e_X1_pow_mul (n : ℕ) (k : Fin (n + 1)) (r : P2) :
    coeff (e n k) (X 1 ^ ((k : ℕ) + 1) * r) = 0 := by
  rw [X_pow_eq_monomial, coeff_monomial_mul', if_neg]
  intro h
  have h1 := h 1
  simp [e_one] at h1

/-- The `X₀^{n−k} X₁^k` diagonal entry of an upper-triangular `T` (`T 1 0 = 0`): `T₀₀^{n−k} T₁₁^k`. -/
theorem coeff_act_mono (n : ℕ) (T : M2) (hT : T 1 0 = 0) (k : Fin (n + 1)) :
    coeff (e n k) (act T (mono n k)) = T 0 0 ^ (n - (k : ℕ)) * T 1 1 ^ (k : ℕ) := by
  have h0 : act T (X 0) = T 0 0 • X 0 + T 0 1 • X 1 := by rw [act_X, Fin.sum_univ_two]
  have h1 : act T (X 1) = T 1 1 • X 1 := by rw [act_X, Fin.sum_univ_two, hT, zero_smul, zero_add]
  obtain ⟨q, hq⟩ := pow_split (T 0 0) (T 0 1) (n - (k : ℕ))
  rw [mono_eq, map_mul, map_pow, map_pow, h0, h1, hq, add_mul, coeff_add]
  have hA : (T 0 0 • X 0 : P2) ^ (n - (k : ℕ)) * (T 1 1 • X 1) ^ (k : ℕ)
      = (T 0 0 ^ (n - (k : ℕ)) * T 1 1 ^ (k : ℕ)) • mono n k := by
    rw [smul_pow, smul_pow, smul_mul_smul_comm, mono_eq]
  have hB : X 1 * q * (T 1 1 • X 1 : P2) ^ (k : ℕ)
      = X 1 ^ ((k : ℕ) + 1) * (C (T 1 1) ^ (k : ℕ) * q) := by
    rw [smul_eq_C_mul]
    ring
  rw [hA, hB, coeff_e_X1_pow_mul, add_zero, coeff_smul, mono, coeff_monomial, if_pos rfl,
    smul_eq_mul, mul_one]

/-- For `T 1 0 = 0`: `symChar n T = Σ_{k=0}^{n} T₀₀^{n−k} T₁₁^k`. -/
theorem symChar_of_lower_eq_zero (n : ℕ) (T : M2) (hT : T 1 0 = 0) :
    symChar n T = ∑ k ∈ Finset.range (n + 1), T 0 0 ^ (n - k) * T 1 1 ^ k := by
  rw [symChar_eq, ← Fin.sum_univ_eq_sum_range (fun k => T 0 0 ^ (n - k) * T 1 1 ^ k)]
  exact Finset.sum_congr rfl fun k _ => coeff_act_mono n T hT k

/-- `symChar n g = weightSum n z` at every eigenvalue `z` of `g ∈ SU(2)`. -/
theorem symChar_eq_weightSum (n : ℕ) (g : SU 2) {z : ℂ}
    (hz : (z • (1 : M2) - (g : M2)).det = 0) : symChar n (g : M2) = weightSum n z := by
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hz
  have hgv : (g : M2) *ᵥ v = z • v := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv.symm
  let P : M2 := !![v 0, -star (v 1); v 1, star (v 0)]
  have hdetP : P.det = ((Complex.normSq (v 0) + Complex.normSq (v 1) : ℝ) : ℂ) := by
    simp only [P, Matrix.det_fin_two_of, Complex.star_def, Complex.ofReal_add, ← Complex.mul_conj]
    ring
  have hne : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv0 (funext fun i => by fin_cases i <;> simp [h.1, h.2])
  have hpos : 0 < Complex.normSq (v 0) + Complex.normSq (v 1) := by
    rcases hne with h | h
    · exact add_pos_of_pos_of_nonneg (Complex.normSq_pos.2 h) (Complex.normSq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (Complex.normSq_pos.2 h)
  have hu : IsUnit P.det := by
    rw [hdetP]
    exact isUnit_iff_ne_zero.2 (Complex.ofReal_ne_zero.2 hpos.ne')
  have hPe : P *ᵥ Pi.single 0 1 = v := by
    funext i
    fin_cases i <;> simp [P, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  set T : M2 := P⁻¹ * (g : M2) * P with hTdef
  have hTe : T *ᵥ Pi.single 0 1 = z • Pi.single 0 1 := by
    rw [hTdef, ← Matrix.mulVec_mulVec, hPe, ← Matrix.mulVec_mulVec, hgv, Matrix.mulVec_smul,
      ← hPe, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P hu, Matrix.one_mulVec]
  have hT00 : T 0 0 = z := by
    have := congrFun hTe 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hT10 : T 1 0 = 0 := by
    have := congrFun hTe 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hdg : (g : M2).det = 1 := (Matrix.mem_specialUnitaryGroup_iff.1 g.2).2
  have hPP : P⁻¹.det * P.det = 1 := by
    rw [← Matrix.det_mul, Matrix.nonsing_inv_mul P hu, Matrix.det_one]
  have hdetT : T.det = 1 := by
    rw [hTdef, Matrix.det_mul, Matrix.det_mul]
    linear_combination (g : M2).det * hPP + hdg
  have hT11 : T 1 1 = z⁻¹ := by
    rw [Matrix.det_fin_two, hT00, hT10, mul_zero, sub_zero] at hdetT
    exact eq_inv_of_mul_eq_one_right hdetT
  rw [← symChar_conj n (g : M2) P hu, ← hTdef, symChar_of_lower_eq_zero n T hT10, hT00, hT11,
    weightSum]

/-- `U_n(τ g)` is the trace of `g ∈ SU(2)` on `Sym^n ℂ²`, the spin-`n/2` character. -/
theorem symChar_eq_eval_U (n : ℕ) (g : SU 2) :
    symChar n (g : M2) = (((U ℝ n).eval (suTau g) : ℝ) : ℂ) := by
  obtain ⟨z, hz⟩ := exists_eigenvalue g
  rw [symChar_eq_weightSum n g hz, eval_U_suTau_eq_weightSum g hz n]

end MassGap.PuritySU2SymPower

#print axioms MassGap.PuritySU2SymPower.act_mul
#print axioms MassGap.PuritySU2SymPower.sym_eq
#print axioms MassGap.PuritySU2SymPower.symChar_eq
#print axioms MassGap.PuritySU2SymPower.symChar_conj
#print axioms MassGap.PuritySU2SymPower.symChar_of_lower_eq_zero
#print axioms MassGap.PuritySU2SymPower.symChar_eq_weightSum
#print axioms MassGap.PuritySU2SymPower.symChar_eq_eval_U
