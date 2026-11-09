import Mathlib
import MassGap.SUN

/-!
# MassGap.SU2Quat — the quaternion form of `SU(2)`, and normalisation back into the group

A block step of a gauge field sums products of links and normalises the sum back into the group. The
normalisation must be continuous for the blocked field to be an observer of the continuum theory
(`ContinuumFlow.Flow` asks for continuous fields). For `SU(2)` it is: real combinations of `SU(2)`
matrices have the quaternion form `[[a, b], [−b̄, ā]]`, on which `V⋆V = det V · 1` with
`det V = |a|² + |b|²` real and non-negative, so `V / √(det V)` lies in `SU(2)` wherever `det V > 0`.

* `IsQuat V`: the quaternion form. `isQuat_of_mem` (every `SU(2)` matrix has it), closure under sums
  (`IsQuat.add`), real scaling (`IsQuat.smul_real`), products (`IsQuat.mul`) and the adjoint
  (`IsQuat.adj`).
* `IsQuat.det_eq`: `det V = |a|² + |b|²`; `IsQuat.star_mul_self`, `IsQuat.mul_star_self`: `V⋆V = V V⋆ = det V · 1`.
* `IsQuat.normalise_mem`: for `det V ≠ 0`, `(√(re det V))⁻¹ • V ∈ SU(2)`.
-/

namespace MassGap.SU2Quat

open Matrix Complex

/-- **The quaternion form** of a `2 × 2` complex matrix: `V₁₁ = conj V₀₀` and `V₁₀ = −conj V₀₁`.

DERIVED: `0`, `1` are the matrix indices. -/
def IsQuat (V : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  V 1 1 = starRingEnd ℂ (V 0 0) ∧ V 1 0 = -starRingEnd ℂ (V 0 1)

/-- **Every `SU(2)` matrix has the quaternion form.** `U U⋆ = 1` and `det U = 1` give `U⋆ = adj U`,
whose entries are `U₁₁, −U₀₁, −U₁₀, U₀₀`.

DERIVED: `0`, `1` are the matrix indices and the determinant. -/
theorem isQuat_of_mem {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    IsQuat U := by
  rw [Matrix.mem_specialUnitaryGroup_iff] at hU
  obtain ⟨hu, hdet⟩ := hU
  rw [Matrix.mem_unitaryGroup_iff] at hu
  have hsu : star U * U = 1 := Matrix.mul_eq_one_comm.mp hu
  have hadj : adjugate U = star U := by
    calc adjugate U = (star U * U) * adjugate U := by rw [hsu, one_mul]
      _ = star U * (U * adjugate U) := by rw [Matrix.mul_assoc]
      _ = star U := by rw [Matrix.mul_adjugate, hdet, one_smul, Matrix.mul_one]
  have h00 := congrFun (congrFun hadj 0) 0
  have h01 := congrFun (congrFun hadj 0) 1
  rw [Matrix.adjugate_fin_two] at h00 h01
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.star_apply, RCLike.star_def] at h00 h01
  refine ⟨h00, ?_⟩
  have h01' := congrArg (starRingEnd ℂ) h01
  simp only [map_neg, Complex.conj_conj] at h01'
  rw [← h01']

#print axioms isQuat_of_mem

/-- DERIVED: no numeral. -/
theorem IsQuat.add {V W : Matrix (Fin 2) (Fin 2) ℂ} (hV : IsQuat V) (hW : IsQuat W) :
    IsQuat (V + W) := by
  obtain ⟨h1, h2⟩ := hV
  obtain ⟨k1, k2⟩ := hW
  refine ⟨?_, ?_⟩ <;> simp only [Matrix.add_apply, map_add, h1, h2, k1, k2, neg_add]

#print axioms IsQuat.add

/-- DERIVED: no numeral. -/
theorem IsQuat.smul_real {V : Matrix (Fin 2) (Fin 2) ℂ} (hV : IsQuat V) (t : ℝ) :
    IsQuat ((t : ℂ) • V) := by
  obtain ⟨h1, h2⟩ := hV
  refine ⟨?_, ?_⟩ <;> simp only [Matrix.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, h1, h2,
    mul_neg]

#print axioms IsQuat.smul_real

/-- DERIVED: `0`, `1` are the matrix indices. -/
theorem IsQuat.mul {V W : Matrix (Fin 2) (Fin 2) ℂ} (hV : IsQuat V) (hW : IsQuat W) :
    IsQuat (V * W) := by
  obtain ⟨h1, h2⟩ := hV
  obtain ⟨k1, k2⟩ := hW
  refine ⟨?_, ?_⟩ <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, h1, h2, k1, k2, map_neg,
      Complex.conj_conj] <;> ring

#print axioms IsQuat.mul

/-- DERIVED: `0`, `1` are the matrix indices. -/
theorem IsQuat.adj {V : Matrix (Fin 2) (Fin 2) ℂ} (hV : IsQuat V) : IsQuat (star V) := by
  obtain ⟨h1, h2⟩ := hV
  refine ⟨?_, ?_⟩ <;>
    simp only [Matrix.star_apply, RCLike.star_def, h1, h2, map_neg, Complex.conj_conj, neg_neg]

#print axioms IsQuat.adj

/-- **The determinant of the quaternion form**: `det V = |a|² + |b|²`, real and non-negative.

DERIVED: `0`, `1` are the matrix indices. -/
theorem IsQuat.det_eq {V : Matrix (Fin 2) (Fin 2) ℂ} (hV : IsQuat V) :
    V.det = ((Complex.normSq (V 0 0) + Complex.normSq (V 0 1) : ℝ) : ℂ) := by
  obtain ⟨h1, h2⟩ := hV
  rw [Matrix.det_fin_two, h1, h2]
  push_cast
  rw [← Complex.mul_conj, ← Complex.mul_conj]
  ring

#print axioms IsQuat.det_eq

/-- **`V⋆ V = det V · 1`** on the quaternion form.

DERIVED: `0`, `1` are the matrix indices. -/
theorem IsQuat.star_mul_self {V : Matrix (Fin 2) (Fin 2) ℂ} (hV : IsQuat V) :
    star V * V = V.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hd := hV.det_eq
  obtain ⟨h1, h2⟩ := hV
  rw [hd]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2, Complex.mul_conj, Complex.normSq_eq_conj_mul_self] <;>
    ring

#print axioms IsQuat.star_mul_self

/-- **`V V⋆ = det V · 1`** on the quaternion form.

DERIVED: `0`, `1` are the matrix indices. -/
theorem IsQuat.mul_star_self {V : Matrix (Fin 2) (Fin 2) ℂ} (hV : IsQuat V) :
    V * star V = V.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hd := hV.det_eq
  obtain ⟨h1, h2⟩ := hV
  rw [hd]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2, Complex.mul_conj, Complex.normSq_eq_conj_mul_self] <;>
    ring

#print axioms IsQuat.mul_star_self

/-- **Normalisation back into `SU(2)`.** On the quaternion form with `det V ≠ 0`,
`(√(re det V))⁻¹ • V` is special unitary.

DERIVED: `0` is the excluded determinant; `2` is the matrix size in `det (c • V) = c² det V`; `1` the
unit determinant. -/
theorem IsQuat.normalise_mem {V : Matrix (Fin 2) (Fin 2) ℂ} (hV : IsQuat V) (h0 : V.det ≠ 0) :
    ((Real.sqrt (V.det.re))⁻¹ : ℂ) • V ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hd := hV.det_eq
  set d : ℝ := Complex.normSq (V 0 0) + Complex.normSq (V 0 1) with hdd
  have hre : V.det.re = d := by rw [hd, Complex.ofReal_re]
  have hd0 : 0 ≤ d := add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hdpos : 0 < d := by
    rcases hd0.lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [hd, ← h, Complex.ofReal_zero]) h0
  have hs : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd0
  have hsne : (Real.sqrt d : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hdpos).ne'
  rw [hre, Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hV.mul_star_self, hd,
      smul_smul]
    have : ((Real.sqrt d : ℂ)⁻¹ * star ((Real.sqrt d : ℂ)⁻¹)) * (d : ℂ) = 1 := by
      rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
      field_simp
      first | exact_mod_cast hs | exact_mod_cast hs.symm
    rw [this, one_smul]
  · rw [Matrix.det_smul, hd, Fintype.card_fin]
    field_simp
    first | exact_mod_cast hs | exact_mod_cast hs.symm

#print axioms IsQuat.normalise_mem

/-! ## The quaternion norm, and dominance -/

/-- The first row of a matrix, as a vector of `ℂ²` with the Euclidean norm.

DERIVED: `2` is the Euclidean exponent and the size; `0` the first row. -/
noncomputable def qv (V : Matrix (Fin 2) (Fin 2) ℂ) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 (fun i => V 0 i)

/-- **The quaternion norm**: the Euclidean norm of the first row. On the quaternion form its square is
`re det V` (`IsQuat.det_re_eq`).

DERIVED: no numeral. -/
noncomputable def qnorm (V : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ‖qv V‖

/-- DERIVED: no numeral. -/
theorem qnorm_nonneg (V : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ qnorm V := norm_nonneg _

/-- DERIVED: `2` is the square; `0`, `1` are the matrix indices. -/
theorem qnorm_sq (V : Matrix (Fin 2) (Fin 2) ℂ) :
    qnorm V ^ 2 = Complex.normSq (V 0 0) + Complex.normSq (V 0 1) := by
  unfold qnorm
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)),
    Fin.sum_univ_two]
  simp [qv, Complex.sq_norm]

#print axioms qnorm_sq

/-- The triangle inequality.

DERIVED: no numeral. -/
theorem qnorm_add_le (V W : Matrix (Fin 2) (Fin 2) ℂ) : qnorm (V + W) ≤ qnorm V + qnorm W := by
  unfold qnorm
  have h : qv (V + W) = qv V + qv W := rfl
  rw [h]
  exact norm_add_le _ _

#print axioms qnorm_add_le

/-- DERIVED: no numeral. -/
theorem qnorm_neg (V : Matrix (Fin 2) (Fin 2) ℂ) : qnorm (-V) = qnorm V := by
  unfold qnorm
  have h : qv (-V) = -qv V := rfl
  rw [h, norm_neg]

#print axioms qnorm_neg

/-- Real scaling scales the norm by the absolute value.

DERIVED: no numeral. -/
theorem qnorm_smul_real (t : ℝ) (V : Matrix (Fin 2) (Fin 2) ℂ) :
    qnorm ((t : ℂ) • V) = |t| * qnorm V := by
  unfold qnorm
  have h : qv ((t : ℂ) • V) = (t : ℂ) • qv V := rfl
  rw [h, norm_smul, Complex.norm_real, Real.norm_eq_abs]

#print axioms qnorm_smul_real

/-- The triangle inequality over a finite sum.

DERIVED: `0` is the empty sum. -/
theorem qnorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin 2) (Fin 2) ℂ) :
    qnorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, qnorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h : qv (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := rfl
    unfold qnorm
    rw [h, norm_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (qnorm_add_le _ _).trans (by linarith)

#print axioms qnorm_sum_le

/-- On the quaternion form, `re det V` is the squared quaternion norm.

DERIVED: `2` is the square. -/
theorem IsQuat.det_re_eq {V : Matrix (Fin 2) (Fin 2) ℂ} (hV : IsQuat V) :
    V.det.re = qnorm V ^ 2 := by
  rw [hV.det_eq, Complex.ofReal_re, qnorm_sq]

#print axioms IsQuat.det_re_eq

/-- **An `SU(2)` matrix has quaternion norm one.**

DERIVED: `1` is the determinant and the norm; `2` the square. -/
theorem qnorm_of_mem {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) : qnorm U = 1 := by
  have h := (isQuat_of_mem hU).det_re_eq
  rw [(Matrix.mem_specialUnitaryGroup_iff.mp hU).2, Complex.one_re] at h
  have h0 := qnorm_nonneg U
  exact le_antisymm (by nlinarith) (by nlinarith)

#print axioms qnorm_of_mem

/-- **Dominance keeps the determinant away from zero.** If `V = W + E` has the quaternion form, `W` is
special unitary and `qnorm E < 1`, then `det V ≠ 0`: `1 = qnorm W ≤ qnorm V + qnorm E`. A block step
`V = U U' + c · Σ (six staples)` has `qnorm` of the staple part at most `6c`, so it never divides by
zero when `c < 1/6`, and the normalised block link is a continuous function of the configuration.

DERIVED: `1` is the norm of `W`; `0` the excluded determinant. -/
theorem det_ne_zero_of_dominant {V W E : Matrix (Fin 2) (Fin 2) ℂ} (hV : IsQuat V)
    (hVWE : V = W + E) (hW : W ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) (hE : qnorm E < 1) :
    V.det ≠ 0 := by
  have h1 : qnorm W ≤ qnorm V + qnorm E := by
    have hW' : W = V + -E := by rw [hVWE]; abel
    calc qnorm W = qnorm (V + -E) := by rw [hW']
      _ ≤ qnorm V + qnorm (-E) := qnorm_add_le _ _
      _ = qnorm V + qnorm E := by rw [qnorm_neg]
  rw [qnorm_of_mem hW] at h1
  have hpos : 0 < qnorm V := by linarith
  intro h0
  have h2 := hV.det_re_eq
  rw [h0, Complex.zero_re] at h2
  nlinarith [hpos]

#print axioms det_ne_zero_of_dominant

end MassGap.SU2Quat
