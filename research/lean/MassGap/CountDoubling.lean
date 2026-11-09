import Mathlib
import MassGap.DoublingRecursion

/-!
# MassGap.CountDoubling — the Rényi-2 count of the excited levels never grows along a time doubling

A positive transfer operator, normalized by its top eigenvalue, has excited levels `y_i ∈ [0, 1]` (a finite family
here). At time `m` the excited weight is `e(m) = ∑ y_i^m` (`wsum`; it is `DoublingRecursion.excited` by
`excited_eq_wsum`). Its Rényi-2 count at time `m` is

  `R₂(m) = e(m)² / e(2m)`,

the participation number of the level distribution `p_i = y_i^m / e(m)` (`∑ p_i² = e(2m)/e(m)²`). This module proves
that the count is fixed by the first read: it never grows when the time doubles, and with the held weight it fixes the
transfer gap at every later doubling. No dynamics enter; only positivity of the spectrum (reflection positivity of the
transfer) and two Cauchy–Schwarz steps. Declarations are in the namespace `MassGap.CountDoubling`.

## 1. The count (proved)

* `wsum_double_le_sq`: `e(2m) ≤ e(m)²`, so `one_le_count2`: `R₂(m) ≥ 1` when `e(2m) > 0`.
* `count2_double_le`: `R₂(2m) ≤ R₂(m)`. Proof: with `q_i = y_i^m`, Cauchy–Schwarz gives `(∑q²)² ≤ (∑q)(∑q³)` and
  `(∑q³)² ≤ (∑q²)(∑q⁴)`, hence `(∑q²)³ ≤ (∑q)²(∑q⁴)` (Hölder at exponents `3/2`, `3`), which is the claim.
* `count2_iter_le`: `R₂(2^j m) ≤ R₂(m)` for every `j`.

## 2. The next-window floor is the count (proved; an identity)

* `wsum_double_eq`: `e(2m) = e(m)² / R₂(m)`. So `floor_of_count`: a count bound `R₂(m) ≤ Q` gives the next-time floor
  `e(m)²/Q ≤ e(2m)`, and `count_of_floor` is the converse. The floor and the count bound are the same statement;
  neither is discharged by the other.

## 3. The rate sandwich at every doubling (proved)

With `y₁` the top excited level and `R = m · (−log y₁)` its rate at time `m` (the transfer gap in window units):

* `rate_ge`: `−log e(m) ≤ R` (the lower half: a held weight bounds the gap below).
* `rate_le`: `R ≤ −log e(m) + log R₂(m)` (the upper half: the count is the whole correction).
* `rate_le_seed`: `2^j m · (−log y₁) ≤ −log e(2^j m) + log R₂(m)` for every `j`: the count read at the first time `m`
  bounds the upper half at every later doubling of the time.

## 4. What this does and does not reach

The doubling of `DoublingRecursion`/`CouplingTower` doubles all four sides of the torus. Along one direction `μ` at
fixed transverse sides (the corners `v`, `v + E μ`, `v + 2 E μ` of `DoublingPower.FactRep`) the transfer operator is
one operator and §1–§3 apply as stated: the count at corner `v + E μ` is at most the count at `v`. Across a window step
`w → w + 1` the transverse slice doubles too and the transfer operator changes; the levels `y_i` are those of a
different operator and `count2_double_le` does not compare them.

## 5. Relation to the defect

`DoublingRecursion.defect s w m = 2 log powSum m − log powSum (2m)` is `log` of the Rényi-2 count of the full spectrum
`w` (top level included) at time `m`: `defect = log (powSum m² / powSum (2m))`. `count2` here is the count of the
excited levels `y_i = w_i / w_{i₀}` only, the top removed (`excited_eq_wsum`). `StallRigid.defect_double_le_two`,
`d(2m) ≤ 2 d(m)`, bounds the full-spectrum log count at the doubled time by twice its value; `count2_double_le` bounds
the excited count at the doubled time by its value, with no factor.

## What does not follow

* No bound on `R₂` across a transverse doubling, so no bound on the window count along a coupling tower, and so no
  next-window floor (`TransferBand.WindowOverlap` and its floor input stay open; §2 shows the floor is the count).
* `BasinGrowth.RelLip` is not touched: this module reads at one coupling.
* The levels here are a finite family; the Wilson slice transfer operator has infinitely many, and no eigenvalue
  list of it is in the tree.

DERIVED (module-wide): `2` the square of the purity, the doubled time and the base of `2^j`; `3`, `4` the powers
`q³`, `q⁴` in Hölder's exponents `3/2`, `3`; `1` the floor of the count; `0` the signs.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.CountDoubling

open Finset Real

variable {ι : Type} (t : Finset ι) (y : ι → ℝ)

/-- **The excited weight at time `m`**: `e(m) = ∑ y_i^m`. DERIVED: no numeral. -/
def wsum (m : ℕ) : ℝ := ∑ i ∈ t, y i ^ m

/-- **The Rényi-2 count at time `m`**: `R₂(m) = e(m)² / e(2m)`. DERIVED: `2` the square and the doubled time. -/
def count2 (m : ℕ) : ℝ := wsum t y m ^ 2 / wsum t y (2 * m)

variable {t y}

/-- `e(k m) = ∑ (y_i^m)^k`. DERIVED: no numeral. -/
theorem wsum_mul (k m : ℕ) : wsum t y (k * m) = ∑ i ∈ t, (y i ^ m) ^ k := by
  unfold wsum
  refine sum_congr rfl fun i _ => ?_
  rw [← pow_mul, mul_comm]

/-- **The excited part squares**: `e(2m) ≤ e(m)²`. DERIVED: `2` the square and the doubled time. -/
theorem wsum_double_le_sq (hy : ∀ i ∈ t, 0 ≤ y i) (m : ℕ) : wsum t y (2 * m) ≤ wsum t y m ^ 2 := by
  rw [wsum_mul, sq, wsum, sum_mul]
  refine sum_le_sum fun i hi => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left
    (single_le_sum (f := fun i => y i ^ m) (fun j hj => pow_nonneg (hy j hj) m) hi)
    (pow_nonneg (hy i hi) m)

/-- **The count is at least one.** DERIVED: `1` the floor; `0` the sign. -/
theorem one_le_count2 (hy : ∀ i ∈ t, 0 ≤ y i) {m : ℕ} (h2 : 0 < wsum t y (2 * m)) :
    1 ≤ count2 t y m := by
  rw [count2, le_div_iff₀ h2, one_mul]
  exact wsum_double_le_sq hy m

/-- **Hölder at exponents `3/2`, `3`**: `(∑q²)³ ≤ (∑q)² ∑q⁴` for `q ≥ 0`, through two Cauchy–Schwarz steps.
DERIVED: `2`, `3`, `4` the powers. -/
theorem holder_three {q : ι → ℝ} (hq : ∀ i ∈ t, 0 ≤ q i) :
    (∑ i ∈ t, q i ^ 2) ^ 3 ≤ (∑ i ∈ t, q i) ^ 2 * ∑ i ∈ t, q i ^ 4 := by
  have A : (∑ i ∈ t, q i ^ 2) ^ 2 ≤ (∑ i ∈ t, q i) * ∑ i ∈ t, q i ^ 3 :=
    sum_sq_le_sum_mul_sum_of_sq_le_mul t hq (fun i hi => pow_nonneg (hq i hi) 3)
      (fun i _ => by ring_nf; exact le_rfl)
  have B : (∑ i ∈ t, q i ^ 3) ^ 2 ≤ (∑ i ∈ t, q i ^ 2) * ∑ i ∈ t, q i ^ 4 :=
    sum_sq_le_sum_mul_sum_of_sq_le_mul t (fun i hi => pow_nonneg (hq i hi) 2)
      (fun i hi => pow_nonneg (hq i hi) 4) (fun i _ => by ring_nf; exact le_rfl)
  set S1 := ∑ i ∈ t, q i
  set S2 := ∑ i ∈ t, q i ^ 2
  set S3 := ∑ i ∈ t, q i ^ 3
  set S4 := ∑ i ∈ t, q i ^ 4
  have h1 : 0 ≤ S1 := sum_nonneg hq
  have h2 : 0 ≤ S2 := sum_nonneg fun i hi => pow_nonneg (hq i hi) 2
  have h3 : 0 ≤ S3 := sum_nonneg fun i hi => pow_nonneg (hq i hi) 3
  rcases h2.lt_or_eq with h2p | h2z
  · -- `S2⁴ ≤ S1² S3² ≤ S1² S2 S4`, then divide by `S2 > 0`
    have hA2 : (S2 ^ 2) ^ 2 ≤ (S1 * S3) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) A 2
    have hB' : S1 ^ 2 * S3 ^ 2 ≤ S1 ^ 2 * (S2 * S4) := mul_le_mul_of_nonneg_left B (sq_nonneg _)
    have key : S2 * S2 ^ 3 ≤ S2 * (S1 ^ 2 * S4) := by nlinarith [hA2, hB']
    exact le_of_mul_le_mul_left key h2p
  · rw [← h2z]
    have : 0 ≤ S4 := sum_nonneg fun i hi => pow_nonneg (hq i hi) 4
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity

/-- **The count never grows along a time doubling**: `R₂(2m) ≤ R₂(m)`, when `e(2m) > 0`.
DERIVED: `2` the doubled time; `3`, `4` through `holder_three`. -/
theorem count2_double_le (hy : ∀ i ∈ t, 0 ≤ y i) {m : ℕ} (h2 : 0 < wsum t y (2 * m)) :
    count2 t y (2 * m) ≤ count2 t y m := by
  have hq : ∀ i ∈ t, 0 ≤ y i ^ m := fun i hi => pow_nonneg (hy i hi) m
  have H := holder_three hq
  have e1 : wsum t y m = ∑ i ∈ t, (y i ^ m) ^ 1 := by rw [← wsum_mul, one_mul]
  have e2 : wsum t y (2 * m) = ∑ i ∈ t, (y i ^ m) ^ 2 := wsum_mul 2 m
  have e4 : wsum t y (2 * (2 * m)) = ∑ i ∈ t, (y i ^ m) ^ 4 := by
    rw [← mul_assoc, wsum_mul]; norm_num
  simp only [pow_one] at e1
  rw [← e1, ← e2, ← e4] at H
  have h4 : 0 < wsum t y (2 * (2 * m)) := by
    obtain ⟨i, hi, hne⟩ := exists_ne_zero_of_sum_ne_zero h2.ne'
    have hp : 0 < y i ^ (2 * m) := lt_of_le_of_ne (pow_nonneg (hy i hi) _) (Ne.symm hne)
    have e : y i ^ (2 * (2 * m)) = (y i ^ (2 * m)) ^ 2 := by rw [← pow_mul]; ring_nf
    exact lt_of_lt_of_le (by rw [e]; exact pow_pos hp 2)
      (single_le_sum (f := fun i => y i ^ (2 * (2 * m))) (fun j hj => pow_nonneg (hy j hj) _) hi)
  rw [count2, count2, div_le_div_iff₀ h4 h2]
  nlinarith [H]

/-- **A positive top level makes every weight positive.** DERIVED: `0` the sign. -/
theorem wsum_pos {i₁ : ι} (hi₁ : i₁ ∈ t) (hy₁ : 0 < y i₁) (hy : ∀ i ∈ t, 0 ≤ y i) (m : ℕ) :
    0 < wsum t y m :=
  lt_of_lt_of_le (pow_pos hy₁ m)
    (single_le_sum (f := fun i => y i ^ m) (fun j hj => pow_nonneg (hy j hj) m) hi₁)

/-- **The count read at the first time bounds it at every later doubling**: `R₂(2^j m) ≤ R₂(m)`.
DERIVED: `2` the base of the doubling; `0` the start of the count. -/
theorem count2_iter_le {i₁ : ι} (hi₁ : i₁ ∈ t) (hy₁ : 0 < y i₁) (hy : ∀ i ∈ t, 0 ≤ y i) (m : ℕ) :
    ∀ j : ℕ, count2 t y (2 ^ j * m) ≤ count2 t y m := by
  have hpos := wsum_pos hi₁ hy₁ hy
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have e : 2 ^ (j + 1) * m = 2 * (2 ^ j * m) := by ring
    rw [e]
    exact (count2_double_le hy (hpos _)).trans ih

/-! ## 2. The next-time floor is the count -/

/-- **The identity** `e(2m) = e(m)² / R₂(m)`. DERIVED: `2` the square and the doubled time. -/
theorem wsum_double_eq (hy : ∀ i ∈ t, 0 ≤ y i) {m : ℕ} (h2 : 0 < wsum t y (2 * m)) :
    wsum t y (2 * m) = wsum t y m ^ 2 / count2 t y m := by
  have ha : 0 < wsum t y m ^ 2 := lt_of_lt_of_le h2 (wsum_double_le_sq hy m)
  have hm : wsum t y m ≠ 0 := fun h => by rw [h] at ha; norm_num at ha
  rw [count2]; field_simp

/-- **A count bound is a next-time floor**: `R₂(m) ≤ Q` gives `e(m)²/Q ≤ e(2m)`. DERIVED: `2` the square. -/
theorem floor_of_count (hy : ∀ i ∈ t, 0 ≤ y i) {m : ℕ} (h2 : 0 < wsum t y (2 * m)) {Q : ℝ}
    (hQ : count2 t y m ≤ Q) : wsum t y m ^ 2 / Q ≤ wsum t y (2 * m) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le one_pos ((one_le_count2 hy h2).trans hQ)
  rw [count2, div_le_iff₀ h2] at hQ
  rw [div_le_iff₀ hQ0]; linarith

/-- **A next-time floor is a count bound** (the converse). DERIVED: `2` the square; `0` the sign. -/
theorem count_of_floor {m : ℕ} (h2 : 0 < wsum t y (2 * m)) {Q : ℝ} (hQ0 : 0 < Q)
    (hf : wsum t y m ^ 2 / Q ≤ wsum t y (2 * m)) : count2 t y m ≤ Q := by
  rw [div_le_iff₀ hQ0] at hf
  rw [count2, div_le_iff₀ h2]; linarith

/-! ## 3. The rate sandwich -/

/-- **The lower half**: a held weight bounds the rate of the top level below, `−log e(m) ≤ m (−log y₁)`.
DERIVED: `0` the sign. -/
theorem rate_ge {i₁ : ι} (hi₁ : i₁ ∈ t) (hy₁ : 0 < y i₁) (hy : ∀ i ∈ t, 0 ≤ y i) (m : ℕ) :
    -Real.log (wsum t y m) ≤ (m : ℝ) * (-Real.log (y i₁)) := by
  have h := Real.log_le_log (pow_pos hy₁ m)
    (single_le_sum (f := fun i => y i ^ m) (fun j hj => pow_nonneg (hy j hj) m) hi₁)
  rw [Real.log_pow] at h
  change (m : ℝ) * Real.log (y i₁) ≤ Real.log (wsum t y m) at h
  linarith

/-- `e(2m) ≤ y₁^m e(m)` for the top level `y₁`. DERIVED: `2` the doubled time. -/
theorem wsum_double_le_top {i₁ : ι} (hy : ∀ i ∈ t, 0 ≤ y i) (htop : ∀ i ∈ t, y i ≤ y i₁) (m : ℕ) :
    wsum t y (2 * m) ≤ y i₁ ^ m * wsum t y m := by
  unfold wsum
  rw [mul_sum]
  refine sum_le_sum fun i hi => ?_
  rw [two_mul, pow_add]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hy i hi) (htop i hi) m) (pow_nonneg (hy i hi) m)

/-- **The upper half**: the count is the whole correction, `m (−log y₁) ≤ −log e(m) + log R₂(m)`.
DERIVED: `2` the doubled time inside `R₂`. -/
theorem rate_le {i₁ : ι} (hi₁ : i₁ ∈ t) (hy₁ : 0 < y i₁) (hy : ∀ i ∈ t, 0 ≤ y i)
    (htop : ∀ i ∈ t, y i ≤ y i₁) (m : ℕ) :
    (m : ℝ) * (-Real.log (y i₁)) ≤ -Real.log (wsum t y m) + Real.log (count2 t y m) := by
  have he := wsum_pos hi₁ hy₁ hy m
  have h2 := wsum_pos hi₁ hy₁ hy (2 * m)
  have hl := Real.log_le_log h2 (wsum_double_le_top hy htop m)
  rw [Real.log_mul (pow_pos hy₁ m).ne' he.ne', Real.log_pow] at hl
  rw [count2, Real.log_div (pow_pos he 2).ne' h2.ne', Real.log_pow]
  push_cast at hl ⊢
  linarith

/-- **The seed count bounds the upper half at every doubling**: `2^j m (−log y₁) ≤ −log e(2^j m) + log R₂(m)`.
DERIVED: `2` the base of the doubling. -/
theorem rate_le_seed {i₁ : ι} (hi₁ : i₁ ∈ t) (hy₁ : 0 < y i₁) (hy : ∀ i ∈ t, 0 ≤ y i)
    (htop : ∀ i ∈ t, y i ≤ y i₁) (m j : ℕ) :
    ((2 ^ j * m : ℕ) : ℝ) * (-Real.log (y i₁))
      ≤ -Real.log (wsum t y (2 ^ j * m)) + Real.log (count2 t y m) := by
  have hpos := wsum_pos hi₁ hy₁ hy
  have hc := count2_iter_le hi₁ hy₁ hy m j
  have hc0 : 0 < count2 t y (2 ^ j * m) := div_pos (pow_pos (hpos _) 2) (hpos _)
  have := rate_le hi₁ hy₁ hy htop (2 ^ j * m)
  have := Real.log_le_log hc0 hc
  linarith

/-! ## 4. The link to the doubling recursion -/

/-- **The tree's excited weight is the weight of the normalized levels** `y_i = w_i / w_{i₀}` on the excited
indices. It is the identity `StallRigid.excited_eq_sum`, restated in `wsum` form without importing `StallRigid`.
DERIVED: no numeral. -/
theorem excited_eq_wsum [DecidableEq ι] (s : Finset ι) (w : ι → ℝ) (i₀ : ι) (m : ℕ) :
    DoublingRecursion.excited s w i₀ m = wsum (s.erase i₀) (fun i => w i / w i₀) m := by
  unfold DoublingRecursion.excited wsum
  rw [sum_div]
  exact sum_congr rfl fun i _ => (div_pow _ _ _).symm

/-- **The normalized levels of a positive spectrum are nonnegative.** DERIVED: `0` the sign. -/
theorem levels_nonneg [DecidableEq ι] {s : Finset ι} {w : ι → ℝ} {i₀ : ι}
    (h : DoublingRecursion.Top s w i₀) : ∀ i ∈ s.erase i₀, 0 ≤ w i / w i₀ :=
  fun i hi => div_nonneg (h.nonneg i (mem_of_mem_erase hi)) h.pos.le

/-- **The tree's spectrum: the count of its excited levels never grows along a time doubling**, wherever the
excited weight at time `2m` is positive. DERIVED: `2` the doubled time. -/
theorem excited_count_double_le [DecidableEq ι] {s : Finset ι} {w : ι → ℝ} {i₀ : ι}
    (h : DoublingRecursion.Top s w i₀) {m : ℕ}
    (h2 : 0 < DoublingRecursion.excited s w i₀ (2 * m)) :
    count2 (s.erase i₀) (fun i => w i / w i₀) (2 * m) ≤ count2 (s.erase i₀) (fun i => w i / w i₀) m := by
  rw [excited_eq_wsum] at h2
  exact count2_double_le (levels_nonneg h) h2

end MassGap.CountDoubling

end

#print axioms MassGap.CountDoubling.wsum_mul
#print axioms MassGap.CountDoubling.wsum_double_le_sq
#print axioms MassGap.CountDoubling.one_le_count2
#print axioms MassGap.CountDoubling.holder_three
#print axioms MassGap.CountDoubling.count2_double_le
#print axioms MassGap.CountDoubling.wsum_pos
#print axioms MassGap.CountDoubling.count2_iter_le
#print axioms MassGap.CountDoubling.wsum_double_eq
#print axioms MassGap.CountDoubling.floor_of_count
#print axioms MassGap.CountDoubling.count_of_floor
#print axioms MassGap.CountDoubling.rate_ge
#print axioms MassGap.CountDoubling.wsum_double_le_top
#print axioms MassGap.CountDoubling.rate_le
#print axioms MassGap.CountDoubling.rate_le_seed
#print axioms MassGap.CountDoubling.excited_eq_wsum
#print axioms MassGap.CountDoubling.levels_nonneg
#print axioms MassGap.CountDoubling.excited_count_double_le
