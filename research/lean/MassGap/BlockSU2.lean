import Mathlib
import MassGap.SU2Quat

/-!
# MassGap.BlockSU2 — one averaged block step of an `SU(2)` link, continuous and gauge covariant

The observer reads the gauge field through a block step: the doubled link `W = U U'` plus `c` times the
six staples beside it, normalised back into `SU(2)`. For `0 ≤ c < 1/6` the staple part has quaternion
norm at most `6c < 1`, so the sum never vanishes (`SU2Quat.det_ne_zero_of_dominant`) and the
normalisation is a continuous function of the links. That is what makes the blocked field an observer
of the continuum theory in the sense of `ContinuumFlow.Flow`.

* `blockMat c W S = W + c · Σᵢ Sᵢ`: quaternion form (`blockMat_isQuat`), non-zero determinant for
  `0 ≤ c < 1/6` (`blockMat_det_ne_zero`).
* `blockLink c hc0 hc W S ∈ SU(2)`: the normalised block link.
* `continuous_blockLink`: continuous in `(W, S)`.
* `blockLink_gauge`: `blockLink (g W h⁻¹) (g Sᵢ h⁻¹) = g · blockLink W S · h⁻¹` — the block link
  transforms as a link from the start of its paths to their common end.
-/

namespace MassGap.BlockSU2

open Matrix MassGap.SU2Quat

/-- The `2 × 2` matrix of an `SU(2)` element.

DERIVED: `2` is the matrix size. -/
abbrev mat (U : MassGap.SUN.SU 2) : Matrix (Fin 2) (Fin 2) ℂ := (U : Matrix (Fin 2) (Fin 2) ℂ)

/-- **The unnormalised block matrix**: the doubled link plus `c` times the six staples.

DERIVED: `6` is the number of staples beside a link in four dimensions (three transverse directions,
two sides each). -/
noncomputable def blockMat (c : ℝ) (W : MassGap.SUN.SU 2) (S : Fin 6 → MassGap.SUN.SU 2) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  mat W + (c : ℂ) • ∑ i, mat (S i)

/-- DERIVED: `6` is the staple count. -/
theorem blockMat_isQuat (c : ℝ) (W : MassGap.SUN.SU 2) (S : Fin 6 → MassGap.SUN.SU 2) :
    IsQuat (blockMat c W S) := by
  unfold blockMat
  refine (isQuat_of_mem W.2).add (IsQuat.smul_real ?_ c)
  have h : ∀ s : Finset (Fin 6), IsQuat (∑ i ∈ s, mat (S i)) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact ⟨by simp, by simp⟩
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (isQuat_of_mem (S a).2).add ih
  exact h Finset.univ

#print axioms blockMat_isQuat

/-- **The block matrix never vanishes for `0 ≤ c < 1/6`**: the staple part has quaternion norm at most
`6c < 1` against the unit norm of the doubled link.

DERIVED: `6` is the staple count; `1` the norm of an `SU(2)` matrix; `0` the excluded determinant. -/
theorem blockMat_det_ne_zero {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (W : MassGap.SUN.SU 2)
    (S : Fin 6 → MassGap.SUN.SU 2) : (blockMat c W S).det ≠ 0 := by
  refine det_ne_zero_of_dominant (blockMat_isQuat c W S) rfl W.2 ?_
  have hsum : qnorm (∑ i, mat (S i)) ≤ 6 := by
    calc qnorm (∑ i, mat (S i)) ≤ ∑ i, qnorm (mat (S i)) := qnorm_sum_le _ _
      _ = ∑ _i : Fin 6, (1 : ℝ) := Finset.sum_congr rfl (fun i _ => qnorm_of_mem (S i).2)
      _ = 6 := by simp
  rw [qnorm_smul_real, abs_of_nonneg hc0]
  nlinarith [qnorm_nonneg (∑ i, mat (S i))]

#print axioms blockMat_det_ne_zero

/-- **The normalised block link**, in `SU(2)` (`SU2Quat.IsQuat.normalise_mem`).

DERIVED: `6` is the staple count; `1/6` the dominance bound on `c`. -/
noncomputable def blockLink (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 6) (W : MassGap.SUN.SU 2)
    (S : Fin 6 → MassGap.SUN.SU 2) : MassGap.SUN.SU 2 :=
  ⟨((Real.sqrt (blockMat c W S).det.re)⁻¹ : ℂ) • blockMat c W S,
    (blockMat_isQuat c W S).normalise_mem (blockMat_det_ne_zero hc0 hc W S)⟩

/-- The determinant's real part is positive.

DERIVED: `0` is the bound; `2` the square; `6` the staple count (`1/6` the dominance bound). -/
theorem blockMat_det_re_pos {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (W : MassGap.SUN.SU 2)
    (S : Fin 6 → MassGap.SUN.SU 2) : 0 < (blockMat c W S).det.re := by
  have h := (blockMat_isQuat c W S).det_re_eq
  have hne := blockMat_det_ne_zero hc0 hc W S
  have hq : qnorm (blockMat c W S) ≠ 0 := by
    intro hz
    apply hne
    have hd := (blockMat_isQuat c W S).det_eq
    rw [hd]
    have : Complex.normSq ((blockMat c W S) 0 0) + Complex.normSq ((blockMat c W S) 0 1) = 0 := by
      rw [← qnorm_sq, hz]; ring
    rw [this, Complex.ofReal_zero]
  rw [h]
  exact pow_pos ((qnorm_nonneg _).lt_of_ne (Ne.symm hq)) 2

#print axioms blockMat_det_re_pos

/-- **The block link is continuous** in the doubled link and the staples.

DERIVED: `6` is the staple count; `1/6` the dominance bound. -/
theorem continuous_blockLink {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) :
    Continuous (fun p : MassGap.SUN.SU 2 × (Fin 6 → MassGap.SUN.SU 2) => blockLink c hc0 hc p.1 p.2) := by
  have hmat : Continuous (fun p : MassGap.SUN.SU 2 × (Fin 6 → MassGap.SUN.SU 2) => blockMat c p.1 p.2) := by
    unfold blockMat
    refine (continuous_subtype_val.comp continuous_fst).add (continuous_const.smul ?_)
    exact continuous_finset_sum _ (fun i _ =>
      continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))
  have hre : Continuous (fun p : MassGap.SUN.SU 2 × (Fin 6 → MassGap.SUN.SU 2) =>
      (blockMat c p.1 p.2).det.re) := Complex.continuous_re.comp hmat.matrix_det
  have hsq : Continuous (fun p : MassGap.SUN.SU 2 × (Fin 6 → MassGap.SUN.SU 2) =>
      ((Real.sqrt (blockMat c p.1 p.2).det.re : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp hre)
  have hne : ∀ p : MassGap.SUN.SU 2 × (Fin 6 → MassGap.SUN.SU 2),
      ((Real.sqrt (blockMat c p.1 p.2).det.re : ℝ) : ℂ) ≠ 0 := by
    intro p
    exact_mod_cast (Real.sqrt_pos.mpr (blockMat_det_re_pos hc0 hc p.1 p.2)).ne'
  exact (hsq.inv₀ hne).smul hmat |>.subtype_mk _

#print axioms continuous_blockLink

/-- The block matrix of gauge-transformed inputs is the gauge-transformed block matrix.

DERIVED: `6` is the staple count. -/
theorem blockMat_gauge (c : ℝ) (g h W : MassGap.SUN.SU 2) (S : Fin 6 → MassGap.SUN.SU 2) :
    blockMat c (g * W * h⁻¹) (fun i => g * S i * h⁻¹) = mat g * blockMat c W S * mat h⁻¹ := by
  unfold blockMat
  simp only [mat, Submonoid.coe_mul]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum,
    Finset.sum_mul]

#print axioms blockMat_gauge

/-- **The block link is gauge covariant**: `blockLink (g W h⁻¹) (g Sᵢ h⁻¹) = g · blockLink W S · h⁻¹`.
Left and right multiplication by `SU(2)` leave the determinant, and so the normalisation, unchanged.

DERIVED: `6` is the staple count; `1` the determinant of an `SU(2)` matrix; `1/6` the dominance bound. -/
theorem blockLink_gauge {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (g h W : MassGap.SUN.SU 2)
    (S : Fin 6 → MassGap.SUN.SU 2) :
    blockLink c hc0 hc (g * W * h⁻¹) (fun i => g * S i * h⁻¹) = g * blockLink c hc0 hc W S * h⁻¹ := by
  have hM := blockMat_gauge c g h W S
  have hdetg : (mat g).det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2
  have hdeth : (mat h⁻¹).det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp (h⁻¹).2).2
  have hdet : (blockMat c (g * W * h⁻¹) (fun i => g * S i * h⁻¹)).det = (blockMat c W S).det := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, hdetg, hdeth, one_mul, mul_one]
  apply Subtype.ext
  simp only [blockLink, Submonoid.coe_mul]
  rw [hdet, hM, Matrix.mul_smul, Matrix.smul_mul]

#print axioms blockLink_gauge

/-- The block matrix of inverted inputs is the adjoint of the block matrix (`U⁻¹ = U⋆` in `SU(2)`).

DERIVED: `6` is the staple count. -/
theorem blockMat_inv (c : ℝ) (W : MassGap.SUN.SU 2) (S : Fin 6 → MassGap.SUN.SU 2) :
    blockMat c W⁻¹ (fun i => (S i)⁻¹) = star (blockMat c W S) := by
  unfold blockMat
  rw [star_add, star_smul, star_sum, Complex.star_def, Complex.conj_ofReal]
  rfl

#print axioms blockMat_inv

/-- **The block link commutes with inversion**: inverting the doubled link and every staple inverts
the block link. The adjoint of a quaternion-form matrix has the same determinant, which is real, so
the normalisation is unchanged.

DERIVED: `6` is the staple count; `1/6` the dominance bound. -/
theorem blockLink_inv {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (W : MassGap.SUN.SU 2)
    (S : Fin 6 → MassGap.SUN.SU 2) :
    blockLink c hc0 hc W⁻¹ (fun i => (S i)⁻¹) = (blockLink c hc0 hc W S)⁻¹ := by
  have hM := blockMat_inv c W S
  have hdet : (blockMat c W⁻¹ (fun i => (S i)⁻¹)).det = (blockMat c W S).det := by
    rw [hM, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, (blockMat_isQuat c W S).det_eq, Complex.star_def,
      Complex.conj_ofReal]
  apply Subtype.ext
  show ((Real.sqrt (blockMat c W⁻¹ (fun i => (S i)⁻¹)).det.re)⁻¹ : ℂ) • blockMat c W⁻¹ (fun i => (S i)⁻¹)
    = star (((Real.sqrt (blockMat c W S).det.re)⁻¹ : ℂ) • blockMat c W S)
  rw [hdet, hM, star_smul, star_inv₀, Complex.star_def, Complex.conj_ofReal]

#print axioms blockLink_inv

/-- **The block link does not depend on the order of the staples.**

DERIVED: `6` is the staple count; `1/6` the dominance bound. -/
theorem blockLink_perm {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (W : MassGap.SUN.SU 2)
    (S : Fin 6 → MassGap.SUN.SU 2) (σ : Equiv.Perm (Fin 6)) :
    blockLink c hc0 hc W (S ∘ σ) = blockLink c hc0 hc W S := by
  have hM : blockMat c W (S ∘ σ) = blockMat c W S := by
    unfold blockMat
    congr 2
    exact Equiv.sum_comp σ (fun i => mat (S i))
  apply Subtype.ext
  show ((Real.sqrt (blockMat c W (S ∘ σ)).det.re)⁻¹ : ℂ) • blockMat c W (S ∘ σ)
    = ((Real.sqrt (blockMat c W S).det.re)⁻¹ : ℂ) • blockMat c W S
  rw [hM]

#print axioms blockLink_perm

end MassGap.BlockSU2
