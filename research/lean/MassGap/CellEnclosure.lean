import Mathlib
import MassGap.Complete

/-!
# MassGap.CellEnclosure — Path 2 / B1: the single gauge cell, toward an exact-rational gap bound

The minimal gauge cell (one plaquette) of the SU(2) Kogut–Susskind Hamiltonian, in the character basis
`|j⟩`, `j = 0, 1/2, 1, …` (index `i = 2j ∈ {0,…,2·jmax}` after truncation): the symmetric TRIDIAGONAL

    H(λ) = diag(j(j+1)) − λ·(nearest-neighbour 1's),   j(j+1) = i(i+2)/4.

Goal of this file (a grind, built up over iterations): a **certified exact-rational lower bound** on the cell
gap `E₁ − E₀ ≥ κ₀ = ¼ln3`, hence `m_cell = e^{−gap} ≤ e^{−κ₀} = 3^{−1/4} < 1` — the F-independent radius `r`
that Path 1's `gap_uniform_in_volume_of_intensive` consumes (sub-lemma **B1** of the physical U-a; see
see `certify/small_volume_enclosure.py`). The port mirrors `certify/small_volume_enclosure.py`: Sturm/Sylvester
inertia (eigenvalue counting by pivot signs) + a Schur/Feshbach truncation tail, all in `ℚ`.

Status: object + basic structure + the closing exp-monotonicity step (`cell_clears_floor`). The Sturm inertia
count and the Feshbach tail are the remaining pieces.
-/

namespace MassGap.CellEnclosure

open scoped Matrix

/-- Retained character states `j = 0, 1/2, …, jmax`, i.e. `i = 2j ∈ {0,…,2·jmax}`. -/
abbrev dim (jmax : ℕ) : ℕ := 2 * jmax + 1

/-- The single-plaquette Kogut–Susskind Hamiltonian truncated at `jmax`, exact rationals: the SU(2) Casimir
`j(j+1) = i(i+2)/4` on the diagonal and the nearest-neighbour electric coupling `−λ` off it. -/
noncomputable def Hcell (jmax : ℕ) (lam : ℚ) : Matrix (Fin (dim jmax)) (Fin (dim jmax)) ℚ :=
  Matrix.of fun i j =>
    if i = j then ((i.val : ℚ) * (i.val + 2)) / 4
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -lam
    else 0

/-- The cell Hamiltonian is symmetric (real, so this is Hermiticity): the diagonal and the nearest-neighbour
off-diagonal are both invariant under `i ↔ j`. -/
theorem Hcell_transpose (jmax : ℕ) (lam : ℚ) : (Hcell jmax lam)ᵀ = Hcell jmax lam := by
  ext i j
  simp only [Matrix.transpose_apply, Hcell, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij; rfl
  · rw [if_neg (show ¬ j = i from fun h => hij h.symm), if_neg hij]
    exact if_congr or_comm rfl rfl

/-- **Closing step (exp-monotonicity): a cell gap at least the entropy floor gives `m_cell ≤ 3^{−1/4} < 1`.**
For any real `gap ≥ κ₀ = ¼ln3`, the cell magnitude `m_cell = e^{−gap}` clears the entropy-floor ceiling
`e^{−κ₀} = 3^{−1/4}`. This is the last step of B1; the exact-rational Sturm/Feshbach lower bound `gap ≥ κ₀`
is the remaining content. -/
theorem cell_clears_floor {gap : ℝ} (h : κ₀YM ≤ gap) :
    Real.exp (-gap) ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
  have h3 : (3 : ℝ) ^ (-(1 : ℝ) / 4) = Real.exp (-κ₀YM) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]; unfold κ₀YM; congr 1; ring
  rw [h3]
  exact Real.exp_le_exp.mpr (by linarith)

/-- And below one: `m_cell = e^{−gap} < 1` as soon as the gap clears the (positive) floor. -/
theorem cell_lt_one {gap : ℝ} (h : κ₀YM ≤ gap) : Real.exp (-gap) < 1 := by
  have hpos : 0 < gap := lt_of_lt_of_le κ₀YM_pos h
  calc Real.exp (-gap) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

/-- **The entropy floor is at most `1/2`.** `κ₀ = ¼ln3 ≤ ½` (from `ln 3 ≤ 3 − 1 = 2`), hence `≤ 3/4`. A cheap
bound used to clear the floor with the crude two-state gap below. -/
theorem κ₀YM_le_half : κ₀YM ≤ 1 / 2 := by
  have hlog : Real.log 3 ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h3 : (3 : ℝ) ^ (-(1 : ℝ) / 4) = Real.exp (-κ₀YM) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]; unfold κ₀YM; congr 1; ring
  have : κ₀YM = (1 / 4) * Real.log 3 := by
    have := congrArg (fun t => -Real.log t) h3
    simp only [Real.log_exp] at this
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 3)] at this
    linarith [this]
  rw [this]; linarith

/-- **The two-state truncation gap clears the floor, at every coupling.** The minimal character truncation
(`j = 0, j = 1/2`) is `[[0, −λ], [−λ, 3/4]]`, with eigenvalues `3/8 ± √(9/64 + λ²)` and spectral gap
`2√(9/64 + λ²) ≥ 2·(3/8) = 3/4 ≥ κ₀`. Proved from `√(9/64 + λ²) ≥ √(9/64) = 3/8` and `κ₀ ≤ 1/2`.
A building block toward the Feshbach-tail single-cell bound: this small truncation has a large tail
(`D_min = 2`), so on its own it certifies the true single-cell gap only where `E₁ < D_min`; the full
`certify/small_volume_enclosure.py` uses `jmax = 30` for a uniform-in-λ bound. -/
theorem twoState_gap_clears_floor (lam : ℝ) : κ₀YM ≤ 2 * Real.sqrt (9 / 64 + lam ^ 2) := by
  have h38 : Real.sqrt (9 / 64 : ℝ) = 3 / 8 := by
    rw [show (9 / 64 : ℝ) = (3 / 8) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hmono : Real.sqrt (9 / 64 : ℝ) ≤ Real.sqrt (9 / 64 + lam ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg lam])
  rw [h38] at hmono
  have hk := κ₀YM_le_half
  linarith

/-! ## The Sturm / Feshbach lower-bound engine (toward the general-`jmax`, all-`λ` cell gap)

The remaining content of B1 is a certified lower bound `E₀ ≥ s`, `E₁ ≥ s + κ₀` on the exact-rational
tridiagonal cell, uniformly in `λ`. The reusable engine is the LDLᵀ (completing-the-square)
factorization of the shifted cell `Hcell − sI`: if it factors as `Lᵀ D L` with a **nonnegative**
pivot diagonal `D`, the shifted cell is positive semidefinite, hence `E₀ ≥ s` — the Sturm inertia
count with zero negative pivots. The `E₁` half counts exactly one negative pivot (codimension-1),
which feeds `eigenvalues_gap_of_codim1_form`. This subsection builds that engine bottom-up. -/

open Matrix in
/-- **PSD from an LDLᵀ certificate.** A matrix equal to `Lᵀ * diagonal d * L` with `d` nonnegative
(the completing-the-square factorization of a shifted tridiagonal cell) is positive semidefinite —
the final step of the Sturm/Feshbach `E₀ ≥ s` lower-bound engine: with every pivot `d i ≥ 0`, the
shifted cell `Hcell − sI` is PSD, so its least eigenvalue `E₀ ≥ s`. -/
theorem posSemidef_of_ldl {n : ℕ} (T L : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hT : T = Lᵀ * Matrix.diagonal d * L) : T.PosSemidef := by
  have hD : (Matrix.diagonal d).PosSemidef := (Matrix.posSemidef_diagonal_iff).2 hd
  have hLT : (L)ᴴ = Lᵀ := by ext i j; simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hpsd := hD.conjTranspose_mul_mul_same L
  rw [hLT] at hpsd
  rwa [hT]

/-- Unit lower-bidiagonal LDLᵀ factor: `1` on the diagonal, multiplier `e i` at `(i, i−1)`. Its
`Lᵀ · diagonal p · L` reconstruction (see `ldl_entry`) is the symmetric tridiagonal whose pivots are
`p`; providing pivots `p` and multipliers `e` matching `Hcell − s•I` is the completing-the-square
certificate that, when `p ≥ 0`, gives `Hcell − s•I ⪰ 0` (i.e. `E₀ ≥ s`) via `posSemidef_of_ldl`. -/
def Lbi {n : ℕ} (e : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if j = i then 1 else if j.val + 1 = i.val then e i else 0

/-- The bidiagonal entry as its two mutually-exclusive indicator pieces (diagonal `1`, subdiagonal `e`). -/
lemma Lbi_apply {n : ℕ} (e : Fin n → ℝ) (a b : Fin n) :
    (Lbi e) a b = (if a = b then (1:ℝ) else 0) + (if a.val = b.val + 1 then e a else 0) := by
  unfold Lbi
  simp only [Matrix.of_apply]
  by_cases h1 : a = b
  · have hv : a.val = b.val := by rw [h1]
    rw [if_pos h1.symm, if_pos h1, if_neg (show ¬ a.val = b.val + 1 by omega)]; ring
  · have hba : ¬ b = a := fun h => h1 h.symm
    rw [if_neg hba, if_neg h1]
    by_cases h2 : a.val = b.val + 1
    · rw [if_pos h2, if_pos (show b.val + 1 = a.val by omega)]; ring
    · rw [if_neg h2, if_neg (show ¬ b.val + 1 = a.val by omega)]; ring

/-- Commute two nested guards over a zero default (used to re-key a sum by the inner index). -/
lemma ite_ite_comm {A B : Prop} [Decidable A] [Decidable B] (x : ℝ) :
    (if A then (if B then x else 0) else 0) = (if B then (if A then x else 0) else 0) := by
  split_ifs <;> rfl

/-- **The LDLᵀ entry formula.** For the unit lower-bidiagonal `L = Lbi e` and diagonal pivots `p`,
`(Lᵀ · diagonal p · L)` is symmetric tridiagonal: at `(i,j)` it is the diagonal `p i` plus the
boundary correction `∑ₖ [k=i+1=j+1] eₖ(pₖeₖ)`, with sub/super entries `p·e`. This produces the pivots
that `posSemidef_of_ldl` consumes — the completing-the-square heart of the Sturm `E₀ ≥ s` engine. -/
theorem ldl_entry {n : ℕ} (p e : Fin n → ℝ) (i j : Fin n) :
    ((Lbi e)ᵀ * Matrix.diagonal p * (Lbi e)) i j
      = (if i = j then p i else 0) + (if i.val = j.val + 1 then p i * e i else 0)
        + (if j.val = i.val + 1 then e j * p j else 0)
        + ∑ k, (if k.val = i.val + 1 ∧ k.val = j.val + 1 then e k * (p k * e k) else 0) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp_rw [Matrix.transpose_apply, Matrix.diagonal_mul, Lbi_apply, add_mul, mul_add,
    Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    ite_ite_comm, Finset.sum_ite_eq' Finset.univ i, Finset.sum_ite_eq' Finset.univ j,
    Finset.mem_univ, if_true, ← ite_and]
  ring

/-! ### Parametric pivot construction (the forward-recurrence certificate as functions)

The Sturm/LDLᵀ pivots as explicit functions of the diagonal `d`, shift `s`, and coupling `lam`, via the
backward recurrence `p(last)=d(last)−s`, `p(i)=(d(i)−s)−lam²/p(i+1)` (`pivotSeq`), and the multipliers
`e(i)=−lam/p(i)` (`multSeq`). The two recurrence identities that `tridiag_ldl_of_recurrence` consumes
(`pivotSeq_recurD` for the diagonal, `multSeq_pivot` for the off-diagonal) hold whenever the relevant
pivot is nonzero — isolating the remaining content to the sign/nonzero analysis (all pivots nonzero,
exactly one negative) over the physical coupling range, the exact-rational Sturm computation. -/

/-- The backward LDLᵀ pivot sequence: `p(last)=d(last)−s`, `p(i)=(d(i)−s)−lam²/p(i+1)`. -/
noncomputable def pivotSeq {n : ℕ} (d : Fin (n+1) → ℝ) (s lam : ℝ) : Fin (n+1) → ℝ :=
  Fin.reverseInduction (d (Fin.last n) - s) (fun i pnext => (d i.castSucc - s) - lam^2 / pnext)

@[simp] lemma pivotSeq_last {n : ℕ} (d : Fin (n+1) → ℝ) (s lam : ℝ) :
    pivotSeq d s lam (Fin.last n) = d (Fin.last n) - s := by
  simp [pivotSeq]

lemma pivotSeq_castSucc {n : ℕ} (d : Fin (n+1) → ℝ) (s lam : ℝ) (i : Fin n) :
    pivotSeq d s lam i.castSucc = (d i.castSucc - s) - lam^2 / (pivotSeq d s lam i.succ) := by
  simp [pivotSeq]

/-- The multiplier sequence `e(i) = −lam / p(i)`. -/
noncomputable def multSeq {n : ℕ} (d : Fin (n+1) → ℝ) (s lam : ℝ) : Fin (n+1) → ℝ :=
  fun i => -lam / pivotSeq d s lam i

/-- **Off-diagonal recurrence (nonzero pivot):** `−lam = e(i)·p(i)` when `p(i) ≠ 0`. -/
lemma multSeq_pivot {n : ℕ} (d : Fin (n+1) → ℝ) (s lam : ℝ) (i : Fin (n+1))
    (hp : pivotSeq d s lam i ≠ 0) :
    -lam = multSeq d s lam i * pivotSeq d s lam i := by
  unfold multSeq; field_simp

/-- **Diagonal recurrence (nonzero next pivot):** `d(i)−s = p(i) + e(i+1)²·p(i+1)` when `p(i+1) ≠ 0`. -/
lemma pivotSeq_recurD {n : ℕ} (d : Fin (n+1) → ℝ) (s lam : ℝ) (i : Fin n)
    (hp : pivotSeq d s lam i.succ ≠ 0) :
    d i.castSucc - s =
      pivotSeq d s lam i.castSucc + (multSeq d s lam i.succ)^2 * pivotSeq d s lam i.succ := by
  rw [pivotSeq_castSucc]; unfold multSeq; field_simp; ring

/-- **hrecO in the `tridiag_ldl_of_recurrence` form** for the parametric pivots (nonzero pivots). -/
lemma pivotSeq_hrecO {n : ℕ} (d : Fin (n+1) → ℝ) (s lam : ℝ)
    (hnz : ∀ i : Fin (n+1), pivotSeq d s lam i ≠ 0) (i j : Fin (n+1)) (_ : j.val = i.val + 1) :
    -lam = multSeq d s lam j * pivotSeq d s lam j :=
  multSeq_pivot d s lam j (hnz j)

/-- **hrecD in the `tridiag_ldl_of_recurrence` sum-form** for the parametric pivots (nonzero pivots):
the correction sum picks out the single `i.succ` term, or is empty at the last index. -/
lemma pivotSeq_hrecD_sum {n : ℕ} (d : Fin (n+1) → ℝ) (s lam : ℝ)
    (hnz : ∀ i : Fin (n+1), pivotSeq d s lam i ≠ 0) (i : Fin (n+1)) :
    d i - s = pivotSeq d s lam i + ∑ k, if k.val = i.val + 1 then
      multSeq d s lam k * (pivotSeq d s lam k * multSeq d s lam k) else 0 := by
  induction i using Fin.lastCases with
  | last =>
    have hsum : (∑ k : Fin (n+1), if k.val = (Fin.last n).val + 1 then
        multSeq d s lam k * (pivotSeq d s lam k * multSeq d s lam k) else 0) = 0 := by
      apply Finset.sum_eq_zero; intro k _
      rw [if_neg]; have := k.isLt; simp only [Fin.val_last]; omega
    rw [hsum, pivotSeq_last]; ring
  | cast i' =>
    have hsum : (∑ k : Fin (n+1), if k.val = (i'.castSucc).val + 1 then
        multSeq d s lam k * (pivotSeq d s lam k * multSeq d s lam k) else 0)
        = multSeq d s lam i'.succ * (pivotSeq d s lam i'.succ * multSeq d s lam i'.succ) := by
      rw [Finset.sum_eq_single i'.succ]
      · rw [if_pos]; simp [Fin.val_succ, Fin.coe_castSucc]
      · intro k _ hk; rw [if_neg]; intro hc; apply hk
        apply Fin.ext; simp only [Fin.val_succ, Fin.coe_castSucc] at hc ⊢; omega
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum]
    have hrec := pivotSeq_recurD d s lam i' (hnz i'.succ)
    rw [hrec]; ring

end MassGap.CellEnclosure
