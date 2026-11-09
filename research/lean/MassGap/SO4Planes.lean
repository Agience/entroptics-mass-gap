import Mathlib
import MassGap.ObserverRotation

noncomputable section

/-!
# MassGap.SO4Planes — `SO(4)` from three plane rotations, and the powers of `pyth`

## Plane rotations generate `SO(4)`

`r01 c s`, `r12 c s`, `r23 c s` are the rotations by `(c, s)`, `c² + s² = 1`, in the planes of the
axes `(0, 1)`, `(1, 2)`, `(2, 3)`. `so4_le_of_planes`: a submonoid of the 4×4 real matrices containing
all three families contains `SO(4)`. The proof is the Givens reduction. `givens_exists`: for every
`(x, y)` there is a rotation taking it to `(r, 0)` with `r ≥ 0`. Six rotations, `(2,3)`, `(1,2)`,
`(0,1)` on the first column, `(2,3)`, `(1,2)` on the second, `(2,3)` on the third, clear the entries
below the diagonal with non-negative diagonal entries in the first three places. An orthogonal matrix
of that shape with determinant `1` is the identity (`eq_one_of_triangular`). Each rotation is undone
by the rotation by `(c, -s)` (`r01_inv` and its siblings), so the matrix is a product of plane
rotations.

## The powers of `pyth` are dense in the rotations of its plane

`rot01 θ = r01 (cos θ) (sin θ)` is a continuous homomorphism from `ℝ` (`rot01_add`) and is
`2π`-periodic. `pyth = rot01 pythAngle` with `pythAngle = arccos (3/5)` (`pyth_eq_rot01`). Its angle
is an irrational multiple of `2π` (`pythAngle_irrational`): if `pythAngle / 2π = a / b`, then
`pyth ^ |b| = rot01 (± a · 2π) = 1`, against `ObserverRotation.pyth_pow_ne_one`. So the integer
multiples of the angle are dense on the circle (`AddCircle.denseRange_zsmul_coe_iff`), and
`rot01_mem_closure`: every rotation of the `(0, 1)` plane is a limit of `rot01 (k · pythAngle)`,
`k ∈ ℤ`, which are `pyth ^ k` for `k ≥ 0` (`rot01_nat_mul`) and powers of `rot01 (-pythAngle)`
otherwise. `rot01_eq_cos_sin`: every `(c, s)` on the unit circle is `(cos θ, sin θ)` for some `θ`.
-/

namespace MassGap.SO4Planes

open MassGap.ObserverRotation Real
open scoped Matrix

/-- `SO(4)` as a submonoid of the 4×4 real matrices.

DERIVED: `4` is the dimension. -/
abbrev SO4 : Submonoid (Matrix (Fin 4) (Fin 4) ℝ) := Matrix.specialOrthogonalGroup (Fin 4) ℝ

/-! ## 1. Plane rotations -/

/-- The rotation by `(c, s)` in the plane of the axes `0, 1`.

DERIVED: `0`, `1` the entries of the identity outside the plane; `4` the dimension. -/
def r01 (c s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![c, -s, 0, 0; s, c, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- The rotation by `(c, s)` in the plane of the axes `1, 2`.

DERIVED: `0`, `1` the entries of the identity outside the plane; `4` the dimension. -/
def r12 (c s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, c, -s, 0; 0, s, c, 0; 0, 0, 0, 1]

/-- The rotation by `(c, s)` in the plane of the axes `2, 3`.

DERIVED: `0`, `1` the entries of the identity outside the plane; `4` the dimension. -/
def r23 (c s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, c, -s; 0, 0, s, c]

/-- The rows of `r01 c s * M`.

DERIVED: `0`–`3` the rows. -/
theorem r01_mul_apply (c s : ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin 4) :
    (r01 c s * M) 0 j = c * M 0 j - s * M 1 j ∧ (r01 c s * M) 1 j = s * M 0 j + c * M 1 j ∧
      (r01 c s * M) 2 j = M 2 j ∧ (r01 c s * M) 3 j = M 3 j := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [r01, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

#print axioms r01_mul_apply

/-- The rows of `r12 c s * M`.

DERIVED: `0`–`3` the rows. -/
theorem r12_mul_apply (c s : ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin 4) :
    (r12 c s * M) 0 j = M 0 j ∧ (r12 c s * M) 1 j = c * M 1 j - s * M 2 j ∧
      (r12 c s * M) 2 j = s * M 1 j + c * M 2 j ∧ (r12 c s * M) 3 j = M 3 j := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [r12, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

#print axioms r12_mul_apply

/-- The rows of `r23 c s * M`.

DERIVED: `0`–`3` the rows. -/
theorem r23_mul_apply (c s : ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin 4) :
    (r23 c s * M) 0 j = M 0 j ∧ (r23 c s * M) 1 j = M 1 j ∧
      (r23 c s * M) 2 j = c * M 2 j - s * M 3 j ∧ (r23 c s * M) 3 j = s * M 2 j + c * M 3 j := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [r23, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

#print axioms r23_mul_apply

/-- The rotation by `(c, -s)` undoes the rotation by `(c, s)`.

DERIVED: `1` the identity and the radius. -/
theorem r01_inv {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) : r01 c (-s) * r01 c s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [r01, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | linear_combination h | ring

#print axioms r01_inv

/-- DERIVED: `1` the identity and the radius. -/
theorem r12_inv {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) : r12 c (-s) * r12 c s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [r12, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | linear_combination h | ring

#print axioms r12_inv

/-- DERIVED: `1` the identity and the radius. -/
theorem r23_inv {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) : r23 c (-s) * r23 c s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [r23, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | linear_combination h | ring

#print axioms r23_inv

/-- **`r01 c s ∈ SO(4)`** on the unit circle.

DERIVED: `1` the radius. -/
theorem r01_mem {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) : r01 c s ∈ SO4 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [r01, Matrix.mul_apply, Fin.sum_univ_four] <;>
      first | linear_combination h | ring
  · simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, r01, Fin.succAbove]
    first | linear_combination h | (simp [Fin.lt_def]; linear_combination h) | nlinarith [h]

#print axioms r01_mem

/-- DERIVED: `1` the radius. -/
theorem r12_mem {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) : r12 c s ∈ SO4 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [r12, Matrix.mul_apply, Fin.sum_univ_four] <;>
      first | linear_combination h | ring
  · simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, r12, Fin.succAbove]
    first | linear_combination h | (simp [Fin.lt_def]; linear_combination h) | nlinarith [h]

#print axioms r12_mem

/-- DERIVED: `1` the radius. -/
theorem r23_mem {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) : r23 c s ∈ SO4 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [r23, Matrix.mul_apply, Fin.sum_univ_four] <;>
      first | linear_combination h | ring
  · simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, r23, Fin.succAbove]
    first | linear_combination h | (simp [Fin.lt_def]; linear_combination h) | nlinarith [h]

#print axioms r23_mem

/-! ## 2. The Givens reduction -/

/-- **One Givens rotation**: every `(x, y)` is turned to `(r, 0)`, `r ≥ 0`, by a rotation `(c, s)`:
`s x + c y = 0` and `c x - s y ≥ 0`.

DERIVED: `0` the cleared entry and the sign; `1` the radius. -/
theorem givens_exists (x y : ℝ) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ s * x + c * y = 0 ∧ 0 ≤ c * x - s * y := by
  by_cases h0 : x ^ 2 + y ^ 2 = 0
  · have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    exact ⟨1, 0, by norm_num, by rw [hx, hy]; ring, by rw [hx, hy]; norm_num⟩
  · have hpos : 0 < x ^ 2 + y ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    set r := Real.sqrt (x ^ 2 + y ^ 2) with hr
    have hr0 : 0 < r := Real.sqrt_pos.mpr hpos
    have hr2 : r ^ 2 = x ^ 2 + y ^ 2 := Real.sq_sqrt hpos.le
    refine ⟨x / r, -y / r, ?_, ?_, ?_⟩
    · rw [div_pow, div_pow, neg_sq, ← add_div, ← hr2, div_self (pow_pos hr0 2).ne']
    · field_simp
      ring
    · have e : x / r * x - -y / r * y = r := by
        field_simp
        rw [hr2]
        ring
      rw [e]
      exact hr0.le

#print axioms givens_exists

/-- DERIVED: `0` the sign; `1` the square. -/
theorem one_of_mul_self {a : ℝ} (h0 : 0 ≤ a) (h : a * a = 1) : a = 1 := by
  rcases mul_self_eq_one_iff.mp h with h | h
  · exact h
  · linarith

/-- DERIVED: `0` the vanishing sum. -/
theorem zero_of_sum3 {a b c : ℝ} (h : a * a + b * b + c * c = 0) : a = 0 := by
  have : a * a = 0 := by nlinarith [mul_self_nonneg a, mul_self_nonneg b, mul_self_nonneg c]
  exact mul_self_eq_zero.mp this

/-- **An orthogonal matrix of determinant `1`, zero below the diagonal, with the first three diagonal
entries non-negative, is the identity.** Column by column and row by row: a unit column `(M₀₀, 0, 0,
0)` with `M₀₀ ≥ 0` has `M₀₀ = 1`, so the rest of row `0` vanishes, and so on; the determinant gives
`M₃₃ = 1`.

DERIVED: `0` the cleared entries and the signs; `1` the identity; `4` the dimension; `0`–`3` the row and
column indices in `Fin 4`. -/
theorem eq_one_of_triangular {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : M ∈ SO4)
    (h10 : M 1 0 = 0) (h20 : M 2 0 = 0) (h30 : M 3 0 = 0) (h21 : M 2 1 = 0) (h31 : M 3 1 = 0)
    (h32 : M 3 2 = 0) (p0 : 0 ≤ M 0 0) (p1 : 0 ≤ M 1 1) (p2 : 0 ≤ M 2 2) : M = 1 := by
  have hT : Mᵀ * M = 1 := transpose_mul_self_of_mem hM
  have hO : M * Mᵀ = 1 := by
    have h := (Matrix.mem_specialOrthogonalGroup_iff.mp hM).1
    rw [Matrix.mem_orthogonalGroup_iff] at h
    exact h
  have hdet : M.det = 1 := (Matrix.mem_specialOrthogonalGroup_iff.mp hM).2
  have c00 := congrFun (congrFun hT 0) 0
  have c11 := congrFun (congrFun hT 1) 1
  have c22 := congrFun (congrFun hT 2) 2
  have r00 := congrFun (congrFun hO 0) 0
  have r11 := congrFun (congrFun hO 1) 1
  have r22 := congrFun (congrFun hO 2) 2
  simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, Matrix.one_apply_eq,
    h10, h20, h30, h21, h31, h32, mul_zero, zero_mul, add_zero, zero_add] at c00 c11 c22 r00 r11 r22
  have e00 : M 0 0 = 1 := one_of_mul_self p0 c00
  have e01 : M 0 1 = 0 := zero_of_sum3 (b := M 0 2) (c := M 0 3) (by linear_combination r00 - (M 0 0 + 1) * e00)
  have e02 : M 0 2 = 0 := zero_of_sum3 (b := M 0 1) (c := M 0 3)
    (by linear_combination r00 - (M 0 0 + 1) * e00)
  have e03 : M 0 3 = 0 := zero_of_sum3 (b := M 0 1) (c := M 0 2)
    (by linear_combination r00 - (M 0 0 + 1) * e00)
  have e11 : M 1 1 = 1 := one_of_mul_self p1 (by linear_combination c11 - M 0 1 * e01)
  have e12 : M 1 2 = 0 := zero_of_sum3 (b := M 1 3) (c := 0)
    (by linear_combination r11 - (M 1 1 + 1) * e11)
  have e13 : M 1 3 = 0 := zero_of_sum3 (b := M 1 2) (c := 0)
    (by linear_combination r11 - (M 1 1 + 1) * e11)
  have e22 : M 2 2 = 1 := one_of_mul_self p2
    (by linear_combination c22 - M 0 2 * e02 - M 1 2 * e12)
  have e23 : M 2 3 = 0 := zero_of_sum3 (b := 0) (c := 0)
    (by linear_combination r22 - (M 2 2 + 1) * e22)
  have hdiag : M = Matrix.diagonal ![1, 1, 1, M 3 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal, e00, e01, e02, e03, e11, e12, e13, e22, e23, h10, h20, h30, h21, h31,
        h32]
  have e33 : M 3 3 = 1 := by
    rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_four] at hdet
    simpa using hdet
  rw [hdiag, e33]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Matrix.one_apply]

#print axioms eq_one_of_triangular

section Reduce

variable (G : Submonoid (Matrix (Fin 4) (Fin 4) ℝ))
  (h01 : ∀ c s : ℝ, c ^ 2 + s ^ 2 = 1 → r01 c s ∈ G)
  (h12 : ∀ c s : ℝ, c ^ 2 + s ^ 2 = 1 → r12 c s ∈ G)
  (h23 : ∀ c s : ℝ, c ^ 2 + s ^ 2 = 1 → r23 c s ∈ G)
include h01 h12 h23

omit h01 h12 in
/-- Undoing a `(2, 3)` rotation inside `G`.

DERIVED: `1` the radius. -/
theorem mem_of_r23 {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : r23 c s * M ∈ G) : M ∈ G := by
  have e : M = r23 c (-s) * (r23 c s * M) := by rw [← mul_assoc, r23_inv h, one_mul]
  rw [e]
  exact G.mul_mem (h23 c (-s) (by rw [neg_sq]; exact h)) hM

omit h01 h23 in
/-- Undoing a `(1, 2)` rotation inside `G`.

DERIVED: `1` the radius. -/
theorem mem_of_r12 {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : r12 c s * M ∈ G) : M ∈ G := by
  have e : M = r12 c (-s) * (r12 c s * M) := by rw [← mul_assoc, r12_inv h, one_mul]
  rw [e]
  exact G.mul_mem (h12 c (-s) (by rw [neg_sq]; exact h)) hM

omit h12 h23 in
/-- Undoing a `(0, 1)` rotation inside `G`.

DERIVED: `1` the radius. -/
theorem mem_of_r01 {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : r01 c s * M ∈ G) : M ∈ G := by
  have e : M = r01 c (-s) * (r01 c s * M) := by rw [← mul_assoc, r01_inv h, one_mul]
  rw [e]
  exact G.mul_mem (h01 c (-s) (by rw [neg_sq]; exact h)) hM

omit h01 h12 in
/-- Third column. DERIVED: `0` the cleared entries and signs; `0`–`3` the indices in `Fin 4`. -/
theorem givens6 {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : M ∈ SO4)
    (h10 : M 1 0 = 0) (h20 : M 2 0 = 0) (h30 : M 3 0 = 0) (h21 : M 2 1 = 0) (h31 : M 3 1 = 0)
    (p0 : 0 ≤ M 0 0) (p1 : 0 ≤ M 1 1) : M ∈ G := by
  obtain ⟨c, s, hcs, hz, hp⟩ := givens_exists (M 2 2) (M 3 2)
  refine mem_of_r23 G h23 hcs ?_
  have hM' : r23 c s * M = 1 := by
    have a0 := r23_mul_apply c s M 0
    have a1 := r23_mul_apply c s M 1
    have a2 := r23_mul_apply c s M 2
    refine eq_one_of_triangular (SO4.mul_mem (r23_mem hcs) hM) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [a0.2.1, h10]
    · rw [a0.2.2.1, h20, h30]; ring
    · rw [a0.2.2.2, h20, h30]; ring
    · rw [a1.2.2.1, h21, h31]; ring
    · rw [a1.2.2.2, h21, h31]; ring
    · rw [a2.2.2.2]; linarith
    · rw [a0.1]; exact p0
    · rw [a1.2.1]; exact p1
    · rw [a2.2.2.1]; exact hp
  rw [hM']
  exact G.one_mem

omit h01 in
/-- Second column, lower entry. DERIVED: `0` the cleared entries and signs; `0`–`3` the indices in
`Fin 4`. -/
theorem givens5 {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : M ∈ SO4)
    (h10 : M 1 0 = 0) (h20 : M 2 0 = 0) (h30 : M 3 0 = 0) (h31 : M 3 1 = 0)
    (p0 : 0 ≤ M 0 0) : M ∈ G := by
  obtain ⟨c, s, hcs, hz, hp⟩ := givens_exists (M 1 1) (M 2 1)
  refine mem_of_r12 G h12 hcs ?_
  have a0 := r12_mul_apply c s M 0
  have a1 := r12_mul_apply c s M 1
  refine givens6 G h23 (SO4.mul_mem (r12_mem hcs) hM) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [a0.2.1, h10, h20]; ring
  · rw [a0.2.2.1, h10, h20]; ring
  · rw [a0.2.2.2, h30]
  · rw [a1.2.2.1]; linarith
  · rw [a1.2.2.2, h31]
  · rw [a0.1]; exact p0
  · rw [a1.2.1]; exact hp

omit h01 in
/-- Second column, upper entry. DERIVED: `0` the cleared entries and signs; `0`–`3` the indices in
`Fin 4`. -/
theorem givens4 {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : M ∈ SO4)
    (h10 : M 1 0 = 0) (h20 : M 2 0 = 0) (h30 : M 3 0 = 0) (p0 : 0 ≤ M 0 0) : M ∈ G := by
  obtain ⟨c, s, hcs, hz, hp⟩ := givens_exists (M 2 1) (M 3 1)
  refine mem_of_r23 G h23 hcs ?_
  have a0 := r23_mul_apply c s M 0
  have a1 := r23_mul_apply c s M 1
  refine givens5 G h12 h23 (SO4.mul_mem (r23_mem hcs) hM) ?_ ?_ ?_ ?_ ?_
  · rw [a0.2.1, h10]
  · rw [a0.2.2.1, h20, h30]; ring
  · rw [a0.2.2.2, h20, h30]; ring
  · rw [a1.2.2.2]; linarith
  · rw [a0.1]; exact p0

/-- First column, top entry. DERIVED: `0` the cleared entries and signs; `0`–`3` the indices in
`Fin 4`. -/
theorem givens3 {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : M ∈ SO4)
    (h20 : M 2 0 = 0) (h30 : M 3 0 = 0) : M ∈ G := by
  obtain ⟨c, s, hcs, hz, hp⟩ := givens_exists (M 0 0) (M 1 0)
  refine mem_of_r01 G h01 hcs ?_
  have a0 := r01_mul_apply c s M 0
  refine givens4 G h12 h23 (SO4.mul_mem (r01_mem hcs) hM) ?_ ?_ ?_ ?_
  · rw [a0.2.1]; linarith
  · rw [a0.2.2.1, h20]
  · rw [a0.2.2.2, h30]
  · rw [a0.1]; exact hp

/-- First column, middle entry. DERIVED: `0` the cleared entries; `0`–`3` the indices in `Fin 4`. -/
theorem givens2 {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : M ∈ SO4) (h30 : M 3 0 = 0) : M ∈ G := by
  obtain ⟨c, s, hcs, hz, hp⟩ := givens_exists (M 1 0) (M 2 0)
  refine mem_of_r12 G h12 hcs ?_
  have a0 := r12_mul_apply c s M 0
  refine givens3 G h01 h12 h23 (SO4.mul_mem (r12_mem hcs) hM) ?_ ?_
  · rw [a0.2.2.1]; linarith
  · rw [a0.2.2.2, h30]

/-- **Plane rotations generate `SO(4)`**: a submonoid containing every rotation of the planes
`(0, 1)`, `(1, 2)`, `(2, 3)` contains `SO(4)`.

DERIVED: `0` the cleared entry; `4` the dimension. -/
theorem so4_le_of_planes : SO4 ≤ G := by
  intro M hM
  obtain ⟨c, s, hcs, hz, hp⟩ := givens_exists (M 2 0) (M 3 0)
  refine mem_of_r23 G h23 hcs ?_
  have a0 := r23_mul_apply c s M 0
  refine givens2 G h01 h12 h23 (SO4.mul_mem (r23_mem hcs) hM) ?_
  rw [a0.2.2.2]; linarith

end Reduce

#print axioms givens6
#print axioms givens5
#print axioms givens4
#print axioms givens3
#print axioms givens2
#print axioms so4_le_of_planes

/-! ## 3. The powers of `pyth` -/

/-- The rotation by the angle `θ` in the plane of the axes `0, 1`.

DERIVED: no numeral. -/
def rot01 (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := r01 (Real.cos θ) (Real.sin θ)

/-- The composite of two `(0, 1)` rotations.

DERIVED: no numeral. -/
theorem r01_mul_r01 (c s c' s' : ℝ) : r01 c s * r01 c' s' = r01 (c * c' - s * s') (s * c' + c * s') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [r01, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

#print axioms r01_mul_r01

/-- **`rot01` is a homomorphism from `ℝ`.**

DERIVED: no numeral. -/
theorem rot01_add (x y : ℝ) : rot01 (x + y) = rot01 x * rot01 y := by
  rw [rot01, rot01, rot01, r01_mul_r01, Real.cos_add, Real.sin_add]

#print axioms rot01_add

/-- DERIVED: `0` the zero angle; `1` the identity. -/
theorem rot01_zero : rot01 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot01, r01, Matrix.one_apply]

#print axioms rot01_zero

/-- **`rot01` is `2π`-periodic.**

DERIVED: `2π` the period. -/
theorem rot01_add_int_two_pi (x : ℝ) (m : ℤ) : rot01 (x + m * (2 * π)) = rot01 x := by
  rw [rot01, rot01, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

#print axioms rot01_add_int_two_pi

/-- DERIVED: `2π` the period; `1` the identity. -/
theorem rot01_int_two_pi (m : ℤ) : rot01 (m * (2 * π)) = 1 := by
  have h := rot01_add_int_two_pi 0 m
  rw [zero_add, rot01_zero] at h
  exact h

#print axioms rot01_int_two_pi

/-- DERIVED: `0` the base of the induction. -/
theorem rot01_nat_mul (n : ℕ) (x : ℝ) : rot01 (n * x) = rot01 x ^ n := by
  induction n with
  | zero => simp [rot01_zero]
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : ℝ) * x = n * x + x by push_cast; ring, rot01_add, ih, pow_succ]

#print axioms rot01_nat_mul

/-- `rot01` is continuous.

DERIVED: no numeral. -/
theorem continuous_rot01 : Continuous rot01 := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [rot01, r01] <;> fun_prop

#print axioms continuous_rot01

/-- **The angle of `pyth`**, `arccos (3/5)`.

DERIVED: `3/5` the cosine of `pyth`. -/
def pythAngle : ℝ := Real.arccos (3 / 5)

/-- DERIVED: `3/5` the cosine. -/
theorem cos_pythAngle : Real.cos pythAngle = 3 / 5 :=
  Real.cos_arccos (by norm_num) (by norm_num)

#print axioms cos_pythAngle

/-- DERIVED: `4/5 = √(1 − (3/5)²)` the sine. -/
theorem sin_pythAngle : Real.sin pythAngle = 4 / 5 := by
  rw [pythAngle, Real.sin_arccos, show (1 : ℝ) - (3 / 5) ^ 2 = (4 / 5) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

#print axioms sin_pythAngle

/-- **`pyth` is the rotation by `pythAngle`.**

DERIVED: `3/5`, `4/5` as in `pyth`. -/
theorem pyth_eq_rot01 : pyth = rot01 pythAngle := by
  rw [rot01, cos_pythAngle, sin_pythAngle]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pyth, r01]

#print axioms pyth_eq_rot01

/-- **The angle of `pyth` is an irrational multiple of `2π`.** If `pythAngle / 2π = a / b`, then
`|b| · pythAngle = ± a · 2π`, so `pyth ^ |b| = 1` with `|b| ≥ 1`, against `pyth_pow_ne_one`.

DERIVED: `2π` the period; `1` the identity; `0` the excluded denominator. -/
theorem pythAngle_irrational : Irrational (pythAngle / (2 * π)) := by
  rw [irrational_iff_ne_rational]
  intro a b hb h
  have hpi : (2 * π) ≠ 0 := by positivity
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have key : pythAngle * b = a * (2 * π) := by
    have e : pythAngle = a / b * (2 * π) := by rw [← h, div_mul_cancel₀ _ hpi]
    rw [e]
    field_simp
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg b
  · have hn0 : n ≠ 0 := by rintro rfl; exact hb (by simp [hn])
    have hpow : pyth ^ n = 1 := by
      rw [pyth_eq_rot01, ← rot01_nat_mul, mul_comm]
      have : pythAngle * (n : ℝ) = a * (2 * π) := by rw [hn] at key; exact_mod_cast key
      rw [this, rot01_int_two_pi]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    exact pyth_pow_ne_one m hpow
  · have hn0 : n ≠ 0 := by rintro rfl; exact hb (by simp [hn])
    have hpow : pyth ^ n = 1 := by
      rw [pyth_eq_rot01, ← rot01_nat_mul, mul_comm]
      have : pythAngle * (n : ℝ) = ((-a : ℤ) : ℝ) * (2 * π) := by
        rw [hn] at key; push_cast at key ⊢; linarith
      rw [this, rot01_int_two_pi]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    exact pyth_pow_ne_one m hpow

#print axioms pythAngle_irrational

/-- **Every rotation of the `(0, 1)` plane is a limit of integer multiples of `pyth`'s rotation**:
`rot01 θ` lies in the closure of `{rot01 (k · pythAngle) : k ∈ ℤ}`. The multiples of an irrational
angle are dense on the circle (`AddCircle.denseRange_zsmul_coe_iff`), hence their lifts are dense in
`ℝ` (`QuotientAddGroup.dense_preimage_mk`), and `rot01` is continuous and `2π`-periodic.

DERIVED: `2π` the period. -/
theorem rot01_mem_closure (θ : ℝ) :
    rot01 θ ∈ closure (Set.range (fun k : ℤ => rot01 (k * pythAngle))) := by
  have hd : DenseRange (· • (pythAngle : AddCircle (2 * π)) : ℤ → AddCircle (2 * π)) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr pythAngle_irrational
  have hd' : Dense (((↑) : ℝ → AddCircle (2 * π)) ⁻¹'
      Set.range (· • (pythAngle : AddCircle (2 * π)) : ℤ → AddCircle (2 * π))) :=
    QuotientAddGroup.dense_preimage_mk.mpr hd
  have hθ : θ ∈ closure (((↑) : ℝ → AddCircle (2 * π)) ⁻¹'
      Set.range (· • (pythAngle : AddCircle (2 * π)) : ℤ → AddCircle (2 * π))) := by
    rw [hd'.closure_eq]; exact Set.mem_univ θ
  refine closure_mono ?_ (mem_closure_image continuous_rot01.continuousAt hθ)
  rintro _ ⟨x, ⟨k, hk⟩, rfl⟩
  refine ⟨k, ?_⟩
  have h2 : ((x - k * pythAngle : ℝ) : AddCircle (2 * π)) = 0 := by
    rw [AddCircle.coe_sub, ← zsmul_eq_mul, AddCircle.coe_zsmul]
    simp only at hk
    rw [hk, sub_self]
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (2 * π)).mp h2
  rw [zsmul_eq_mul] at hm
  show rot01 (k * pythAngle) = rot01 x
  rw [show x = k * pythAngle + m * (2 * π) by linarith, rot01_add_int_two_pi]

#print axioms rot01_mem_closure

/-- **Every point of the unit circle is `(cos θ, sin θ)`**: `θ = ± arccos c` with the sign of `s`.

DERIVED: `0` the sign of `s`; `1` the radius. -/
theorem exists_angle {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) : ∃ θ : ℝ, Real.cos θ = c ∧ Real.sin θ = s := by
  have hc1 : -1 ≤ c := by nlinarith [sq_nonneg s, sq_nonneg (c + 1)]
  have hc2 : c ≤ 1 := by nlinarith [sq_nonneg s, sq_nonneg (c - 1)]
  have hs : Real.sqrt (1 - c ^ 2) = |s| := by
    rw [show 1 - c ^ 2 = s ^ 2 by linarith, Real.sqrt_sq_eq_abs]
  rcases le_or_gt 0 s with hs0 | hs0
  · refine ⟨Real.arccos c, Real.cos_arccos hc1 hc2, ?_⟩
    rw [Real.sin_arccos, hs, abs_of_nonneg hs0]
  · refine ⟨-Real.arccos c, by rw [Real.cos_neg, Real.cos_arccos hc1 hc2], ?_⟩
    rw [Real.sin_neg, Real.sin_arccos, hs, abs_of_neg hs0, neg_neg]

#print axioms exists_angle

end MassGap.SO4Planes
