import Mathlib

/-!
# MassGap.FrobeniusUnitary — the Frobenius norm is unitarily invariant

On `N × N` complex matrices with the Frobenius norm (`Matrix.frobeniusNormedAddCommGroup`, a local
instance here and at every use):

* `frob_sq`: `‖X‖² = Re tr(Xᴴ X)`;
* `frob_unitary_mul`, `frob_mul_unitary`: a unitary factor on either side keeps the norm.
-/

open scoped Matrix

namespace MassGap.FrobeniusUnitary

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

variable {N : ℕ}

/-- `‖X‖² = Re tr(Xᴴ X)` for the Frobenius norm. DERIVED: `2` the square. -/
theorem frob_sq (X : Matrix (Fin N) (Fin N) ℂ) : ‖X‖ ^ 2 = (Matrix.trace (Xᴴ * X)).re := by
  have h1 : ‖X‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
    rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) _)]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Real.rpow_two _
  have h2 : (Matrix.trace (Xᴴ * X)).re = ∑ j, ∑ i, ‖X i j‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [← starRingEnd_apply, RCLike.conj_mul]
    norm_cast
  rw [h1, h2, Finset.sum_comm]

/-- A unitary factor on the left keeps the norm. DERIVED: `2` the square. -/
theorem frob_unitary_mul {u : Matrix (Fin N) (Fin N) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (X : Matrix (Fin N) (Fin N) ℂ) : ‖u * X‖ = ‖X‖ := by
  have hu' : uᴴ * u = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hu
  have h : ‖u * X‖ ^ 2 = ‖X‖ ^ 2 := by
    rw [frob_sq, frob_sq, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ u X, hu',
      Matrix.one_mul]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- A unitary factor on the right keeps the norm. DERIVED: `2` the square. -/
theorem frob_mul_unitary {u : Matrix (Fin N) (Fin N) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (X : Matrix (Fin N) (Fin N) ℂ) : ‖X * u‖ = ‖X‖ := by
  have hu' : u * uᴴ = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp hu
  have ht : Matrix.trace ((X * u)ᴴ * (X * u)) = Matrix.trace (Xᴴ * X) := by
    calc Matrix.trace ((X * u)ᴴ * (X * u)) = Matrix.trace (uᴴ * (Xᴴ * X * u)) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Xᴴ * X * u * uᴴ) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Xᴴ * X) := by rw [Matrix.mul_assoc (Xᴴ * X), hu', Matrix.mul_one]
  have h : ‖X * u‖ ^ 2 = ‖X‖ ^ 2 := by
    rw [frob_sq, frob_sq, ht]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

end MassGap.FrobeniusUnitary

#print axioms MassGap.FrobeniusUnitary.frob_sq
#print axioms MassGap.FrobeniusUnitary.frob_unitary_mul
#print axioms MassGap.FrobeniusUnitary.frob_mul_unitary
