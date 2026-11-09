import Mathlib
import MassGap.FrobeniusUnitary
import MassGap.WilsonAction

/-!
# MassGap.HolonomyLadder — the lattice Stokes ladder for unitary holonomies

On `N × N` complex matrices with the Frobenius norm. `lprod f k = f 0 f 1 ⋯ f (k−1)`, the ordered
product along a path.

* `ladder`: for unitary `u v w : ℕ → M`,
  `‖u₀⋯u_{k−1} − w₀ (v₀⋯v_{k−1}) w_k*‖ ≤ Σ_{i<k} ‖u_i − w_i v_i w_{i+1}*‖`.
  Read on two parallel paths `u`, `v` joined by rungs `w`, each summand is one plaquette's distance from
  `1`: the holonomy of `u` is the rung-conjugate of the holonomy of `v`, up to the plaquettes between
  them. With `w_k = w_0` (a closed ladder) the traces of the two holonomies differ by at most `N` times
  that sum (`abs_trace_sub_le_of_ladder`).
* `norm_entry_le`, `abs_trace_le`: `|X_ij| ≤ ‖X‖` and `|tr X| ≤ N‖X‖`.
* `norm_sub_one_sq`: `‖g − 1‖² = 2N · wilsonDensity g` for `g ∈ SU(N)`. The plaquette action is the
  squared Frobenius distance to `1`.
* `norm_mul_sub_mul_le`: `‖AB − A'B'‖ ≤ ‖A − A'‖ + ‖B − B'‖` for unitary `A'` and `B`.

DERIVED (module-wide): `2` is the square and the `2N` of `‖g − 1‖² = 2N − 2 Re tr g`; `0`, `1` are the
empty product and the identity.
-/

open scoped Matrix

namespace MassGap.HolonomyLadder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

open MassGap.FrobeniusUnitary

variable {N : ℕ}

theorem star_mul_self {u : Matrix (Fin N) (Fin N) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    star u * u = 1 := Matrix.mem_unitaryGroup_iff'.mp hu

theorem mul_star_self {u : Matrix (Fin N) (Fin N) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    u * star u = 1 := Matrix.mem_unitaryGroup_iff.mp hu

/-- The ordered product `f 0 ⋯ f (k−1)`. -/
noncomputable def lprod (f : ℕ → Matrix (Fin N) (Fin N) ℂ) (k : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  ((List.range k).map f).prod

theorem lprod_zero (f : ℕ → Matrix (Fin N) (Fin N) ℂ) : lprod f 0 = 1 := by simp [lprod]

theorem lprod_succ (f : ℕ → Matrix (Fin N) (Fin N) ℂ) (k : ℕ) :
    lprod f (k + 1) = lprod f k * f k := by
  simp [lprod, List.range_succ, List.map_append, List.prod_append]

theorem lprod_mem {f : ℕ → Matrix (Fin N) (Fin N) ℂ} (hf : ∀ i, f i ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (k : ℕ) : lprod f k ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  induction k with
  | zero => rw [lprod_zero]; exact one_mem _
  | succ k ih => rw [lprod_succ]; exact mul_mem ih (hf k)

/-- **The ladder.** -/
theorem ladder (u v w : ℕ → Matrix (Fin N) (Fin N) ℂ)
    (hu : ∀ i, u i ∈ Matrix.unitaryGroup (Fin N) ℂ) (hv : ∀ i, v i ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hw : ∀ i, w i ∈ Matrix.unitaryGroup (Fin N) ℂ) (k : ℕ) :
    ‖lprod u k - w 0 * lprod v k * star (w k)‖
      ≤ ∑ i ∈ Finset.range k, ‖u i - w i * v i * star (w (i + 1))‖ := by
  induction k with
  | zero =>
    rw [lprod_zero, lprod_zero, Matrix.mul_one, mul_star_self (hw 0), sub_self, norm_zero]
    simp
  | succ k ih =>
    rw [lprod_succ, lprod_succ, Finset.sum_range_succ]
    set P := lprod u k
    set Q := lprod v k
    set W := w 0 * Q * star (w k) with hWdef
    have hWm : W ∈ Matrix.unitaryGroup (Fin N) ℂ :=
      mul_mem (mul_mem (hw 0) (lprod_mem hv k)) (Unitary.star_mem (hw k))
    have hW : W * (w k * v k * star (w (k + 1))) = w 0 * (Q * v k) * star (w (k + 1)) := by
      simp only [hWdef, mul_assoc]
      rw [← mul_assoc (star (w k)) (w k), star_mul_self (hw k), Matrix.one_mul]
    have key : P * u k - w 0 * (Q * v k) * star (w (k + 1))
        = (P - W) * u k + W * (u k - w k * v k * star (w (k + 1))) := by
      rw [sub_mul, mul_sub, hW]; abel
    rw [key]
    calc ‖(P - W) * u k + W * (u k - w k * v k * star (w (k + 1)))‖
        ≤ ‖(P - W) * u k‖ + ‖W * (u k - w k * v k * star (w (k + 1)))‖ := norm_add_le _ _
      _ = ‖P - W‖ + ‖u k - w k * v k * star (w (k + 1))‖ := by
          rw [frob_mul_unitary (hu k), frob_unitary_mul hWm]
      _ ≤ _ := by linarith

/-- `|X_ij| ≤ ‖X‖`. -/
theorem norm_entry_le (X : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) : ‖X i j‖ ≤ ‖X‖ := by
  have h1 : ‖X‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
    rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) _)]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Real.rpow_two _
  have h2 : ‖X i j‖ ^ 2 ≤ ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
    calc ‖X i j‖ ^ 2 ≤ ∑ j, ‖X i j‖ ^ 2 :=
          Finset.single_le_sum (f := fun j => ‖X i j‖ ^ 2) (fun j _ => sq_nonneg _)
            (Finset.mem_univ j)
      _ ≤ ∑ i, ∑ j, ‖X i j‖ ^ 2 :=
          Finset.single_le_sum (f := fun i => ∑ j, ‖X i j‖ ^ 2)
            (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rw [← h1] at h2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- `|tr X| ≤ N ‖X‖`. -/
theorem abs_trace_le (X : Matrix (Fin N) (Fin N) ℂ) : ‖Matrix.trace X‖ ≤ N * ‖X‖ := by
  unfold Matrix.trace Matrix.diag
  calc ‖∑ i, X i i‖ ≤ ∑ i, ‖X i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, ‖X‖ := Finset.sum_le_sum fun i _ => norm_entry_le X i i
    _ = N * ‖X‖ := by simp

/-- The trace is conjugation invariant under a unitary. -/
theorem trace_conj {w : Matrix (Fin N) (Fin N) ℂ} (hw : w ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (Q : Matrix (Fin N) (Fin N) ℂ) : Matrix.trace (w * Q * star w) = Matrix.trace Q := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, star_mul_self hw, Matrix.one_mul]

/-- **The closed ladder bounds the trace difference.** -/
theorem abs_trace_sub_le_of_ladder (u v w : ℕ → Matrix (Fin N) (Fin N) ℂ)
    (hu : ∀ i, u i ∈ Matrix.unitaryGroup (Fin N) ℂ) (hv : ∀ i, v i ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hw : ∀ i, w i ∈ Matrix.unitaryGroup (Fin N) ℂ) (k : ℕ) (hk : w k = w 0) :
    ‖Matrix.trace (lprod u k) - Matrix.trace (lprod v k)‖
      ≤ N * ∑ i ∈ Finset.range k, ‖u i - w i * v i * star (w (i + 1))‖ := by
  have h := ladder u v w hu hv hw k
  rw [hk] at h
  rw [← trace_conj (hw 0) (lprod v k), ← Matrix.trace_sub]
  exact (abs_trace_le _).trans (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg N))

/-- `‖AB − A'B'‖ ≤ ‖A − A'‖ + ‖B − B'‖` for unitary `A'` and `B`. -/
theorem norm_mul_sub_mul_le {A A' B B' : Matrix (Fin N) (Fin N) ℂ}
    (hA' : A' ∈ Matrix.unitaryGroup (Fin N) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    ‖A * B - A' * B'‖ ≤ ‖A - A'‖ + ‖B - B'‖ := by
  have e : A * B - A' * B' = (A - A') * B + A' * (B - B') := by
    rw [sub_mul, mul_sub]; abel
  rw [e]
  calc ‖(A - A') * B + A' * (B - B')‖ ≤ ‖(A - A') * B‖ + ‖A' * (B - B')‖ := norm_add_le _ _
    _ = ‖A - A'‖ + ‖B - B'‖ := by rw [frob_mul_unitary hB, frob_unitary_mul hA']

/-- `‖u − X‖ = ‖1 − X u*‖` for unitary `u`. -/
theorem norm_sub_eq_one_sub {u X : Matrix (Fin N) (Fin N) ℂ}
    (hu : u ∈ Matrix.unitaryGroup (Fin N) ℂ) : ‖u - X‖ = ‖1 - X * star u‖ := by
  rw [← frob_mul_unitary hu (1 - X * star u)]
  congr 1
  rw [sub_mul, Matrix.one_mul, Matrix.mul_assoc, star_mul_self hu, Matrix.mul_one]

/-- `‖u − X‖ = ‖u Y − 1‖` when `X Y = 1` with `Y` unitary. -/
theorem norm_sub_eq_mul_sub_one {u X Y : Matrix (Fin N) (Fin N) ℂ}
    (hY : Y ∈ Matrix.unitaryGroup (Fin N) ℂ) (hXY : X * Y = 1) : ‖u - X‖ = ‖u * Y - 1‖ := by
  rw [← frob_mul_unitary hY (u - X), sub_mul, hXY]

/-- `‖g − 1‖² = 2N · wilsonDensity g` on `SU(N)`, `N ≠ 0`. -/
theorem norm_sub_one_sq (hN : N ≠ 0) (g : MassGap.SUN.SU N) :
    ‖(g : Matrix (Fin N) (Fin N) ℂ) - 1‖ ^ 2 = 2 * N * WilsonAction.wilsonDensity g := by
  have hu : (g : Matrix (Fin N) (Fin N) ℂ) ∈ Matrix.unitaryGroup (Fin N) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1
  rw [frob_sq, WilsonAction.wilsonDensity]
  set G := (g : Matrix (Fin N) (Fin N) ℂ)
  have e : (G - 1)ᴴ * (G - 1) = 1 - Gᴴ - G + 1 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, sub_mul, mul_sub, mul_sub,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_one, ← Matrix.star_eq_conjTranspose,
      star_mul_self hu]
    abel
  rw [e, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_one,
    Matrix.trace_conjTranspose]
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re, Fintype.card_fin, Complex.star_def,
    Complex.conj_re]
  field_simp
  ring

/-- `‖g − 1‖ ≤ √(2N S)` whenever `wilsonDensity g ≤ S`. -/
theorem norm_sub_one_le (hN : N ≠ 0) (g : MassGap.SUN.SU N) {S : ℝ}
    (hS : WilsonAction.wilsonDensity g ≤ S) :
    ‖(g : Matrix (Fin N) (Fin N) ℂ) - 1‖ ≤ Real.sqrt (2 * N * S) := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sub_one_sq hN]
  apply Real.sqrt_le_sqrt
  have : (0 : ℝ) ≤ 2 * N := by positivity
  nlinarith

end MassGap.HolonomyLadder

#print axioms MassGap.HolonomyLadder.ladder
#print axioms MassGap.HolonomyLadder.abs_trace_sub_le_of_ladder
#print axioms MassGap.HolonomyLadder.norm_sub_one_sq
