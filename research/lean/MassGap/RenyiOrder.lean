import Mathlib
import MassGap.FreeLevels

/-!
# MassGap.RenyiOrder — order ½ is the sharp Rényi order of the moment closure

`ApertureCount.state_pow_le_renyi` turns one variance bound and per-mode hypercontractivity into every even
moment through the Rényi-½ count `R_½ = (∑_k √p_k)²` of the normalized spectrum, and `state_pow_comb_le` does the same for one reading in uncorrelated modes. This module
shows that the order is fixed by that single-reading closure (`ClosesAt`): every Rényi count of order `α ≤ ½`
closes it, and no count of order `α > ½` does, as the spike readings of §4 show. Declarations are in the namespace
`MassGap.RenyiOrder`.

## 1. The Rényi counts (defined)

For weights `w` on a finite index set, `p = w / ∑ w`:

* `renyiSum α w = ∑_k p_k^α` (real power);
* `renyiCount α w = (∑_k p_k^α)^{1/(1−α)}` for `α ≠ 1`, and `renyiCount 1 w = spDim w = exp H`, the
  entroptics read (`ApertureModes.spDim`).
* `renyiCount_half`: `renyiCount (1/2) w = spRenyi w`, the count of `ApertureCount` (every `w`).

## 2. Monotonicity in the order (proved)

All for nonnegative weights with positive total (a finite probability vector after normalization), and
orders `α > 0`:

* `renShannon_le`: `(1 − α) H ≤ log ∑ p^α` (from `log x ≤ x − 1` on `p^{α−1}/∑ p^α`, term by term), so
  `spDim_le_renyiCount` (`exp H ≤ R_α` for `α < 1`) and `renyiCount_le_spDim` (`R_α ≤ exp H` for `α > 1`).
* `renJensen_lt_one`, `renJensen_gt_one`: with `θ = (1 − β)/(1 − α)`, `∑ p^β ≤ (∑ p^α)^θ` for
  `0 < α ≤ β < 1`, and `(∑ p^α)^θ ≤ ∑ p^β` for `1 < α ≤ β` (Jensen, `Real.rpow_arith_mean_le_arith_mean_rpow`,
  in the weights `p` on `z = p^{α−1}`).
* `renyiCount_antitone`: `0 < α ≤ β` gives `R_β ≤ R_α`, across `α = 1` as well.
* `renyiCount_two_le_spDim_le_spRenyi`: `R_2 ≤ exp H ≤ R_½`.

## 3. The closure at every order `α ≤ ½` (proved)

* `spRenyi_le_renyiCount`: `R_½ ≤ R_α` for `0 < α ≤ ½`, every nonnegative weight vector (a zero total
  gives `R_½ = 0`).
* `state_pow_le_renyiCount`: the conclusion of `state_pow_le_renyi` holds with `R_α` in place of `R_½`, at
  every `α ∈ (0, ½]`, under the same hypotheses (screen translation, per-mode hypercontractivity).
* `ClosesAt α`: the single-reading closure read through `R_α` with a uniform constant: for every order `2p`
  and per-mode constant `K ≥ 0` there is one `K'` such that, for every state and every finite family of
  uncorrelated modes `e_a` with `ν(e_a^{2p}) ≤ K ν(e_a²)^p`, the reading `F = ∑_a e_a` has
  `ν(F^{2p}) ≤ K' (R_α(λ) ν(F²))^p`, `λ_a = ν(e_a²)` the reading's spectrum over its modes.
* `closesAt_of_le_half`: `ClosesAt α` for every `α ∈ (0, ½]`, with `K' = K`
  (`ApertureCount.state_pow_comb_le`, `sq_sum_sqrt`: `(∑ √λ)² = R_½ ∑ λ`).

## 4. The spike test: every order `α > ½` fails (proved)

On the cube `{±1}^m` (`ApertureCount.cubeState`), with `N = 2^m`, `D = N − 1`, `β = (1 − α)/α` and
`ε = N^{−β}/2`, the screen `spScreen m α S = c_S χ_S` has `c_∅ = √(1 − ε)` and
`c_S = √(ε/D) · cw m S` for `S ≠ ∅` (`cw` the binary weights of `ApertureCount`, in `[1/2, 1]`,
`spCw_ge_half`). The top mode carries `1 − ε`; the other `D` modes share `ε`.

* `sp_mul`, `sp_pow`: the modes are uncorrelated and `ν((c_S χ_S)^{2p}) = (c_S²)^p`: per-mode
  hypercontractivity with constant `1` at every order and every `m`.
* `sp_sq_injective`, `sp_gram`, `sp_H1`: the squared weights are distinct, so every eigenspace of the Gram
  matrix is one-dimensional, and the basis-free H1 of `ApertureCount.ApertureCountAt` holds with `C = 1` at
  every Wick exponent, for every `α ∈ (0, 1)` and every `m`. `sp_H1` is proved separately; `ClosesAt` does not require it.
* `sp_renyi_le`: for `α ∈ (0, 1)` and `m ≥ 1`, `R_α ≤ 4^{1/(1−α)}` (the order `β` is the one at which
  `D (ε/D)^α ≤ N^{1−α} N^{−(1−α)} = 1`, `sp_D_rpow_le`).
* `sp_peak`, `sp_peak_sq`, `sp_moment_ge`: at the point `x = (+1, …, +1)` the reading is `∑_S c_S`, at least
  `D √(ε/D)/2`, whose square is at least `N^γ/16`, `γ = 1 − β = (2α − 1)/α`; so
  `ν(F^{2p}) ≥ (N^γ/16)^p / N`, while `ν(F²) ≤ 1` (`sp_T_le`).
* `counts_separate` (the Shannon case `ApertureCount.spRenyi_unbounded_at_bounded_spDim` generalized to every
  order `α > ½`, `α = 1` included): one `C` with, for every `B`, a positive weight vector with `R_α ≤ C` and
  `R_½ ≥ B`. For `α ≥ 3/4` the spike of order `3/4` is used, through `R_α ≤ R_{3/4}`.
* `not_closesAt`: for every `α > ½`, `ClosesAt α` fails. With `r = min α (3/4)`, `γ = γ(r)`, at
  `p = ⌈2/γ⌉₊` (so `2p ≥ 4/γ`) and `K = 1`, a uniform `K'` would give `N ≤ 16^p |K'| 4^{p/(1−r)}` for every
  `m ≥ 1`.

## 5. The sharp order (proved)

* `renyi_order_sharp`: `ClosesAt α` holds for every `α ∈ (0, ½]` and fails for every `α > ½`.
* `half_isGreatest`: `½` is the greatest element of `{α > 0 | ClosesAt α}`.

So the count that controls the single-reading moment closure is the Rényi-½ count: the count Entroptics reads for moment
control is of order `½`, and the order is set by the closure, not chosen. This is a statement about the closure
alone: no clause of `ApertureCountAt` other than its per-mode form enters, and the open inputs (S), (M),
(E) of the route are not used.

## 6. The free spectrum (proved)

* `free_orders_comparable`: if `R_½ ≤ c exp H`, then for every `α ∈ [½, 1]`, `R_α ≤ R_½ ≤ c R_α`.
* `free_orders`: `FreeLevels.free_h3_local` gives `R_½ ≤ A_κ² e² exp H` on the free flowed box spectrum, so
  there all orders in `[½, 1]` agree up to `A_κ² e²`, uniformly in the zoom. On that class the order is not
  visible; the sharpness of §5 is carried by the spike spectra, which the free class excludes.

## What does not follow

* Orders `α ≤ 0` are not treated (`0^α` is not `0` there, so zero weights would count); the closure for
  `α ∈ (0, ½]` and the failure for `α > ½` cover every positive order.
* `ClosesAt` fixes the per-mode constant `K` and asks one `K'` for all states and families at that order.
  The failure is at one order `2p ≥ 4/γ`, which grows as `α ↓ ½`. At the fourth moment alone the spike
  gives `ν(F⁴)/ν(F²)²` of order `ε² D` (argued), unbounded only for `α > 2/3`; whether the closure through
  `R_α`, `α ∈ (½, 2/3]`, fails at the fourth moment is not proved.
* The failing family is a single reading in uncorrelated modes (the form of `state_pow_comb_le`), not a
  translation screen of `state_pow_le_renyi`; the screen-level failure at `α > ½` is not stated.
* Nothing here bounds any count of the lattice screens of `ApertureCount`; H3 and `FreeLevels.FreeScreenSpectrum`
  stay hypotheses, and so do (S), (M), (E).

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the signs and the lower ends; `1` the Shannon order, the normalization, the unit
per-mode constant and the least nonempty set; `2` the squares and the exponent `1/(1 − ½) = 2` of `R_½`,
and the Rényi-2 order of the chain; `1/2` the sharp order and the lower end of `cw`; `4 = 2 · 2` the count
bound (twice from `ν(F²) ≥ 1/2`, twice from the two parts of the sum); `16 = 4 · 4` the peak factor (`1/2`
from `cw ≥ 1/2` squared, `D ≥ N/2` and the `1/2` of `ε`); `β = (1 − α)/α` the exponent that holds
`D (ε/D)^α` at `1`; `γ = 1 − β`; `p = ⌈2/γ⌉₊` the order at which `N^{γp} ≥ N²`. CHOSEN: the factor `1/2` in
`ε = N^{−β}/2` (any factor in `(0, 1)` keeps the top weight strictly largest); the reference order `3/4`
for `α ≥ 3/4` (any order in `(½, 1)` serves). Inherited: `cw`, `wt` and the cube from `ApertureCount`;
`A_κ` (`FreeLevels.renyiFactorL`) and the hypotheses of `FreeLevels.free_h3_local`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.RenyiOrder

open Filter
open MassGap.ApertureModes MassGap.ApertureCount

/-! ## 1. The Rényi counts -/

section Counts

variable {κ : Type*} [Fintype κ]

/-- **The Rényi sum of order `α`**: `∑_k p_k^α`, `p = w / ∑ w`. DERIVED: no numeral. -/
def renyiSum (α : ℝ) (w : κ → ℝ) : ℝ := ∑ k, (w k / ∑ j, w j) ^ α

/-- **The Rényi count of order `α`**: `(∑_k p_k^α)^{1/(1−α)}`, and `exp H` at `α = 1`.
DERIVED: `1` the Shannon order and the exponent's numerator. -/
def renyiCount (α : ℝ) (w : κ → ℝ) : ℝ :=
  if α = 1 then spDim w else renyiSum α w ^ (1 / (1 - α))

/-- DERIVED: `1` the Shannon order. -/
theorem renyiCount_one (w : κ → ℝ) : renyiCount 1 w = spDim w := if_pos rfl

/-- DERIVED: `1` the Shannon order. -/
theorem renyiCount_of_ne {α : ℝ} (hα : α ≠ 1) (w : κ → ℝ) :
    renyiCount α w = renyiSum α w ^ (1 / (1 - α)) := if_neg hα

/-- DERIVED: `0` the sign. -/
theorem renyiSum_nonneg (α : ℝ) {w : κ → ℝ} (hw : ∀ k, 0 ≤ w k) : 0 ≤ renyiSum α w :=
  Finset.sum_nonneg fun k _ =>
    Real.rpow_nonneg (div_nonneg (hw k) (Finset.sum_nonneg fun j _ => hw j)) _

/-- DERIVED: `0` the sign. -/
theorem renyiCount_nonneg (α : ℝ) {w : κ → ℝ} (hw : ∀ k, 0 ≤ w k) : 0 ≤ renyiCount α w := by
  unfold renyiCount
  split_ifs
  · exact (spDim_pos w).le
  · exact Real.rpow_nonneg (renyiSum_nonneg α hw) _

/-- **Order `½` is the count of `ApertureCount`**: `renyiCount (1/2) w = spRenyi w`. DERIVED: `1/2` the
order; `2` its exponent `1/(1 − ½)`. -/
theorem renyiCount_half (w : κ → ℝ) : renyiCount (1 / 2) w = spRenyi w := by
  rw [renyiCount_of_ne (by norm_num), show (1 : ℝ) / (1 - 1 / 2) = 2 by norm_num, Real.rpow_two]
  unfold renyiSum spRenyi
  simp only [Real.sqrt_eq_rpow]

/-- DERIVED: `0` the sign. -/
theorem spRenyi_nonneg (w : κ → ℝ) : 0 ≤ spRenyi w := by
  unfold spRenyi
  exact sq_nonneg _

variable {w : κ → ℝ}

/-- DERIVED: `0` the sign. -/
theorem renP_nonneg (hw : ∀ k, 0 ≤ w k) (k : κ) : 0 ≤ w k / ∑ j, w j :=
  div_nonneg (hw k) (Finset.sum_nonneg fun j _ => hw j)

/-- DERIVED: `1` the normalization. -/
theorem renP_sum (hS : 0 < ∑ j, w j) : ∑ k, w k / ∑ j, w j = 1 := by
  rw [← Finset.sum_div, div_self hS.ne']

end Counts

/-! ## 2. Monotonicity in the order -/

section Monotone

variable {κ : Type*} [Fintype κ]

/-- DERIVED: `0` the sign. -/
theorem renSum_pos {p : κ → ℝ} (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∑ k, p k = 1) (α : ℝ) :
    0 < ∑ k, p k ^ α := by
  obtain ⟨k, hk⟩ : ∃ k, 0 < p k := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have := Finset.sum_nonpos (s := Finset.univ) fun k _ => h k
    linarith
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hk α)
    (Finset.single_le_sum (f := fun k => p k ^ α) (fun j _ => Real.rpow_nonneg (hp0 j) α)
      (Finset.mem_univ k))

/-- One term of the Shannon–Rényi comparison: `(1 − α)(−x log x) − x log S ≤ x^α/S − x`, from
`log y ≤ y − 1` at `y = x^{α−1}/S`. DERIVED: `0` the empty term; `1` the order and `log y ≤ y − 1`. -/
theorem renTerm_le {x α S : ℝ} (hx : 0 ≤ x) (hα : 0 < α) (hS : 0 < S) :
    (1 - α) * Real.negMulLog x - x * Real.log S ≤ x ^ α / S - x := by
  rcases hx.eq_or_lt with h | h
  · rw [← h, Real.zero_rpow hα.ne']
    simp
  · have hl := Real.log_le_sub_one_of_pos (div_pos (Real.rpow_pos_of_pos h (α - 1)) hS)
    rw [Real.log_div (Real.rpow_pos_of_pos h _).ne' hS.ne', Real.log_rpow h] at hl
    have key := mul_le_mul_of_nonneg_left hl h.le
    have e : x * (x ^ α / x) = x ^ α := mul_div_cancel₀ _ h.ne'
    calc (1 - α) * Real.negMulLog x - x * Real.log S
        = x * ((α - 1) * Real.log x - Real.log S) := by rw [Real.negMulLog]; ring
      _ ≤ x * (x ^ (α - 1) / S - 1) := key
      _ = x * (x ^ α / x) / S - x := by rw [Real.rpow_sub_one h.ne']; ring
      _ = x ^ α / S - x := by rw [e]

/-- **Shannon against the Rényi sum**: `(1 − α) H ≤ log ∑ p^α` for every order `α > 0`.
DERIVED: `1` the Shannon order; `0` the sign. -/
theorem renShannon_le {p : κ → ℝ} (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∑ k, p k = 1) {α : ℝ} (hα : 0 < α) :
    (1 - α) * ∑ k, Real.negMulLog (p k) ≤ Real.log (∑ k, p k ^ α) := by
  have hS := renSum_pos hp0 hp1 α
  have h := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => renTerm_le (hp0 k) hα hS
  have eL : ∑ k, ((1 - α) * Real.negMulLog (p k) - p k * Real.log (∑ k, p k ^ α))
      = (1 - α) * ∑ k, Real.negMulLog (p k) - Real.log (∑ k, p k ^ α) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hp1, one_mul]
  have eR : ∑ k, (p k ^ α / (∑ k, p k ^ α) - p k) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hp1, div_self hS.ne', sub_self]
  rw [eL, eR] at h
  linarith

variable {w : κ → ℝ}

/-- **Shannon below every order `α < 1`**: `exp H ≤ R_α`. DERIVED: `1` the Shannon order. -/
theorem spDim_le_renyiCount (hw : ∀ k, 0 ≤ w k) (hS : 0 < ∑ j, w j) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) : spDim w ≤ renyiCount α w := by
  have hp0 := renP_nonneg hw
  have hp1 := renP_sum hS
  have h := renShannon_le hp0 hp1 hα0
  have hSp := renSum_pos hp0 hp1 α
  rw [renyiCount_of_ne hα1.ne, renyiSum, Real.rpow_def_of_pos hSp, spDim, Real.exp_le_exp, mul_one_div,
    le_div_iff₀ (by linarith)]
  rw [mul_comm]
  exact h

/-- **Shannon above every order `α > 1`**: `R_α ≤ exp H`. DERIVED: `1` the Shannon order. -/
theorem renyiCount_le_spDim (hw : ∀ k, 0 ≤ w k) (hS : 0 < ∑ j, w j) {α : ℝ} (hα1 : 1 < α) :
    renyiCount α w ≤ spDim w := by
  have hp0 := renP_nonneg hw
  have hp1 := renP_sum hS
  have h := renShannon_le hp0 hp1 (by linarith : (0 : ℝ) < α)
  have hSp := renSum_pos hp0 hp1 α
  rw [renyiCount_of_ne hα1.ne', renyiSum, Real.rpow_def_of_pos hSp, spDim, Real.exp_le_exp, mul_one_div,
    div_le_iff_of_neg (by linarith)]
  rw [mul_comm]
  exact h

/-- DERIVED: `0` the empty weight. -/
theorem renMul_rpow {x α : ℝ} (hx : 0 ≤ x) (hα : 0 < α) : x * x ^ (α - 1) = x ^ α := by
  rcases hx.eq_or_lt with h | h
  · rw [← h, zero_mul, Real.zero_rpow hα.ne']
  · rw [Real.rpow_sub_one h.ne', mul_div_cancel₀ _ h.ne']

/-- DERIVED: `1` the shift of the exponent. -/
theorem renMul_rpow_rpow {x α β θ : ℝ} (hx : 0 ≤ x) (hβ : 0 < β) (hθ : (α - 1) * θ = β - 1) :
    x * (x ^ (α - 1)) ^ θ = x ^ β := by
  rw [← Real.rpow_mul hx, hθ]
  exact renMul_rpow hx hβ

/-- DERIVED: `1` the Shannon order. -/
theorem renTheta_mul {α β : ℝ} (hβ : β ≠ 1) : (1 - β) / (1 - α) * (1 / (1 - β)) = 1 / (1 - α) := by
  have h : 1 - β ≠ 0 := sub_ne_zero.2 (Ne.symm hβ)
  calc (1 - β) / (1 - α) * (1 / (1 - β)) = (1 - β) * (1 / (1 - β)) / (1 - α) := by ring
    _ = 1 / (1 - α) := by rw [mul_one_div_cancel h]

/-- **Jensen below order `1`**: `∑ p^β ≤ (∑ p^α)^θ`, `θ = (1 − β)/(1 − α) ∈ (0, 1]`, for
`0 < α ≤ β < 1`. DERIVED: `1` the Shannon order and the Jensen exponent bound. -/
theorem renJensen_lt_one {p : κ → ℝ} (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∑ k, p k = 1) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hβ : β < 1) :
    ∑ k, p k ^ β ≤ (∑ k, p k ^ α) ^ ((1 - β) / (1 - α)) := by
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (1 - β) / (1 - α) := ⟨_, rfl⟩
  rw [← hθ]
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have h1α : 0 < 1 - α := by linarith
  have hθ0 : 0 < θ := by rw [hθ]; exact div_pos (by linarith) h1α
  have hθ1 : θ ≤ 1 := by rw [hθ]; exact (div_le_one h1α).2 (by linarith)
  have hθe : (α - 1) * θ = β - 1 := by
    rw [hθ, show α - 1 = -(1 - α) by ring, neg_mul, mul_div_cancel₀ _ h1α.ne']
    ring
  have hJ : (∑ k, p k * (p k ^ (α - 1)) ^ θ) ^ θ⁻¹ ≤ ∑ k, p k * ((p k ^ (α - 1)) ^ θ) ^ θ⁻¹ :=
    Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ p (fun k => (p k ^ (α - 1)) ^ θ)
      (fun k _ => hp0 k) hp1 (fun k _ => Real.rpow_nonneg (Real.rpow_nonneg (hp0 k) _) _)
      ((one_le_inv₀ hθ0).2 hθ1)
  have e1 : ∑ k, p k * (p k ^ (α - 1)) ^ θ = ∑ k, p k ^ β :=
    Finset.sum_congr rfl fun k _ => renMul_rpow_rpow (hp0 k) hβ0 hθe
  have e2 : ∑ k, p k * ((p k ^ (α - 1)) ^ θ) ^ θ⁻¹ = ∑ k, p k ^ α :=
    Finset.sum_congr rfl fun k _ => by
      rw [Real.rpow_rpow_inv (Real.rpow_nonneg (hp0 k) _) hθ0.ne', renMul_rpow (hp0 k) hα]
  rw [e1, e2] at hJ
  have hb0 : 0 ≤ ∑ k, p k ^ β := Finset.sum_nonneg fun k _ => Real.rpow_nonneg (hp0 k) _
  calc ∑ k, p k ^ β = ((∑ k, p k ^ β) ^ θ⁻¹) ^ θ := (Real.rpow_inv_rpow hb0 hθ0.ne').symm
    _ ≤ (∑ k, p k ^ α) ^ θ := Real.rpow_le_rpow (Real.rpow_nonneg hb0 _) hJ hθ0.le

/-- **Jensen above order `1`**: `(∑ p^α)^θ ≤ ∑ p^β`, `θ = (1 − β)/(1 − α) ≥ 1`, for `1 < α ≤ β`.
DERIVED: `1` the Shannon order and the Jensen exponent bound. -/
theorem renJensen_gt_one {p : κ → ℝ} (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∑ k, p k = 1) {α β : ℝ}
    (hα : 1 < α) (hαβ : α ≤ β) :
    (∑ k, p k ^ α) ^ ((1 - β) / (1 - α)) ≤ ∑ k, p k ^ β := by
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := by linarith
  have h1α : 1 - α < 0 := by linarith
  have hθ1 : 1 ≤ (1 - β) / (1 - α) := (le_div_iff_of_neg h1α).2 (by linarith)
  have hθe : (α - 1) * ((1 - β) / (1 - α)) = β - 1 := by
    rw [show α - 1 = -(1 - α) by ring, neg_mul, mul_div_cancel₀ _ h1α.ne]
    ring
  have hJ : (∑ k, p k * p k ^ (α - 1)) ^ ((1 - β) / (1 - α))
      ≤ ∑ k, p k * (p k ^ (α - 1)) ^ ((1 - β) / (1 - α)) :=
    Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ p (fun k => p k ^ (α - 1))
      (fun k _ => hp0 k) hp1 (fun k _ => Real.rpow_nonneg (hp0 k) _) hθ1
  have e1 : ∑ k, p k * p k ^ (α - 1) = ∑ k, p k ^ α :=
    Finset.sum_congr rfl fun k _ => renMul_rpow (hp0 k) hα0
  have e2 : ∑ k, p k * (p k ^ (α - 1)) ^ ((1 - β) / (1 - α)) = ∑ k, p k ^ β :=
    Finset.sum_congr rfl fun k _ => renMul_rpow_rpow (hp0 k) hβ0 hθe
  rw [e1, e2] at hJ
  exact hJ

/-- **The counts decrease with the order below `1`**. DERIVED: `0` the sign; `1` the Shannon order. -/
theorem renyiCount_anti_lt_one (hw : ∀ k, 0 ≤ w k) (hS : 0 < ∑ j, w j) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hβ : β < 1) : renyiCount β w ≤ renyiCount α w := by
  have hp0 := renP_nonneg hw
  have hp1 := renP_sum hS
  have h := renJensen_lt_one hp0 hp1 hα hαβ hβ
  have hb0 : 0 ≤ ∑ k, (w k / ∑ j, w j) ^ β := Finset.sum_nonneg fun k _ => Real.rpow_nonneg (hp0 k) _
  have ha0 : 0 ≤ ∑ k, (w k / ∑ j, w j) ^ α := Finset.sum_nonneg fun k _ => Real.rpow_nonneg (hp0 k) _
  rw [renyiCount_of_ne hβ.ne, renyiCount_of_ne (ne_of_lt (lt_of_le_of_lt hαβ hβ))]
  unfold renyiSum
  calc (∑ k, (w k / ∑ j, w j) ^ β) ^ (1 / (1 - β))
      ≤ ((∑ k, (w k / ∑ j, w j) ^ α) ^ ((1 - β) / (1 - α))) ^ (1 / (1 - β)) :=
        Real.rpow_le_rpow hb0 h (div_nonneg zero_le_one (by linarith))
    _ = (∑ k, (w k / ∑ j, w j) ^ α) ^ (1 / (1 - α)) := by
        rw [← Real.rpow_mul ha0, renTheta_mul hβ.ne]

/-- **The counts decrease with the order above `1`**. DERIVED: `0` the sign; `1` the Shannon order. -/
theorem renyiCount_anti_gt_one (hw : ∀ k, 0 ≤ w k) (hS : 0 < ∑ j, w j) {α β : ℝ} (hα : 1 < α)
    (hαβ : α ≤ β) : renyiCount β w ≤ renyiCount α w := by
  have hp0 := renP_nonneg hw
  have hp1 := renP_sum hS
  have h := renJensen_gt_one hp0 hp1 hα hαβ
  have hβ : 1 < β := lt_of_lt_of_le hα hαβ
  have ha0 : 0 ≤ ∑ k, (w k / ∑ j, w j) ^ α := Finset.sum_nonneg fun k _ => Real.rpow_nonneg (hp0 k) _
  rw [renyiCount_of_ne hβ.ne', renyiCount_of_ne hα.ne']
  unfold renyiSum
  calc (∑ k, (w k / ∑ j, w j) ^ β) ^ (1 / (1 - β))
      ≤ ((∑ k, (w k / ∑ j, w j) ^ α) ^ ((1 - β) / (1 - α))) ^ (1 / (1 - β)) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos (renSum_pos hp0 hp1 α) _) h
          (one_div_nonpos.2 (by linarith))
    _ = (∑ k, (w k / ∑ j, w j) ^ α) ^ (1 / (1 - α)) := by
        rw [← Real.rpow_mul ha0, renTheta_mul hβ.ne']

/-- **The Rényi counts are non-increasing in the order**: `0 < α ≤ β` gives `R_β ≤ R_α`, with
`R_1 = exp H`. DERIVED: `0` the sign; `1` the Shannon order. -/
theorem renyiCount_antitone (hw : ∀ k, 0 ≤ w k) (hS : 0 < ∑ j, w j) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) : renyiCount β w ≤ renyiCount α w := by
  rcases lt_trichotomy β 1 with hβ | hβ | hβ
  · exact renyiCount_anti_lt_one hw hS hα hαβ hβ
  · subst hβ
    rcases hαβ.lt_or_eq with h | h
    · rw [renyiCount_one]
      exact spDim_le_renyiCount hw hS hα h
    · rw [h]
  · rcases lt_trichotomy α 1 with ha | ha | ha
    · exact (renyiCount_le_spDim hw hS hβ).trans (spDim_le_renyiCount hw hS hα ha)
    · subst ha
      rw [renyiCount_one]
      exact renyiCount_le_spDim hw hS hβ
    · exact renyiCount_anti_gt_one hw hS ha hαβ

/-- **The chain `R_2 ≤ exp H ≤ R_½`**. DERIVED: `2` the collision order; `1/2` the order of the closure. -/
theorem renyiCount_two_le_spDim_le_spRenyi (hw : ∀ k, 0 ≤ w k) (hS : 0 < ∑ j, w j) :
    renyiCount 2 w ≤ spDim w ∧ spDim w ≤ spRenyi w := by
  refine ⟨renyiCount_le_spDim hw hS (by norm_num), ?_⟩
  rw [← renyiCount_half]
  exact spDim_le_renyiCount hw hS (by norm_num) (by norm_num)

/-- **Shannon below every order up to `1`**. DERIVED: `1` the Shannon order. -/
theorem spDim_le_renyiCount_of_le_one (hw : ∀ k, 0 ≤ w k) (hS : 0 < ∑ j, w j) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α ≤ 1) : spDim w ≤ renyiCount α w := by
  rcases hα1.lt_or_eq with h | h
  · exact spDim_le_renyiCount hw hS hα0 h
  · rw [h, renyiCount_one]

end Monotone

/-! ## 3. The closure at every order `α ≤ ½` -/

section Closure

variable {κ : Type*} [Fintype κ]

/-- **`R_½` is at most every count of order `α ≤ ½`**, on every nonnegative weight vector.
DERIVED: `1/2` the order; `0` the zero total. -/
theorem spRenyi_le_renyiCount {w : κ → ℝ} (hw : ∀ k, 0 ≤ w k) {α : ℝ} (hα0 : 0 < α)
    (hα : α ≤ 1 / 2) : spRenyi w ≤ renyiCount α w := by
  rcases (Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => hw k).eq_or_lt with h0 | hpos
  · have hz : spRenyi w = 0 := by
      unfold spRenyi
      rw [← h0]
      simp
    rw [hz]
    exact renyiCount_nonneg α hw
  · rw [← renyiCount_half]
    exact renyiCount_antitone hw hpos hα0 hα

/-- **The Minkowski sum through the count**: `(∑ √λ)² = R_½ ∑ λ`. DERIVED: `2` the square. -/
theorem sq_sum_sqrt {w : κ → ℝ} (hw : ∀ k, 0 ≤ w k) :
    (∑ k, Real.sqrt (w k)) ^ 2 = spRenyi w * ∑ k, w k := by
  unfold spRenyi
  rcases (Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => hw k).eq_or_lt with h0 | hpos
  · have hz : ∀ k, w k = 0 := fun k =>
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hw j).1 h0.symm k (Finset.mem_univ k)
    simp [hz]
  · have e : ∑ k, Real.sqrt (w k) = Real.sqrt (∑ j, w j) * ∑ k, Real.sqrt (w k / ∑ j, w j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Real.sqrt_div (hw k), mul_div_cancel₀ _ (Real.sqrt_pos.2 hpos).ne']
    rw [e, mul_pow, Real.sq_sqrt hpos.le, mul_comm]

/-- **Uncorrelated modes add their variances**. DERIVED: `2` the square. -/
theorem renState_sum_sq {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (ν : MassGap.DLRLimit.State X) {ι : Type*} [Fintype ι] (e : ι → C(X, ℝ))
    (horth : ∀ a b, a ≠ b → ν (e a * e b) = 0) :
    ν ((∑ a, e a) ^ 2) = ∑ a, ν (e a ^ 2) := by
  rw [sq, Finset.sum_mul_sum, ν.map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ν.map_sum, Finset.sum_eq_single a (fun b _ hba => horth a b (Ne.symm hba))
    (fun h => absurd (Finset.mem_univ a) h), sq]

/-- **The screen closure at every order `α ≤ ½`**: the hypotheses of `ApertureCount.state_pow_le_renyi`
give `ν(G₀^{2p}) ≤ K (R_α ν(G₀²))^p` for every `α ∈ (0, ½]`. DERIVED: `2` the even power and the
variance; `1/2` the order. -/
theorem state_pow_le_renyiCount {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (ν : MassGap.DLRLimit.State X) {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (F : ι → C(X, ℝ)) {G₀ : C(X, ℝ)} {p : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (htr : ∀ y q, ν (F y ^ q) = ν (G₀ ^ q))
    (h1 : ∀ α, ν (mode ν F α ^ (2 * p)) ≤ K * eig ν F α ^ p) {α : ℝ} (hα0 : 0 < α)
    (hα : α ≤ 1 / 2) :
    ν (G₀ ^ (2 * p)) ≤ K * (renyiCount α (eig ν F) * ν (G₀ ^ 2)) ^ p := by
  have hm2 : 0 ≤ ν (G₀ ^ 2) := ν.nonneg _ fun x => by simp only [ContinuousMap.pow_apply]; positivity
  refine (state_pow_le_renyi ν F hK htr h1).trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (spRenyi_nonneg _) hm2)
    (mul_le_mul_of_nonneg_right (spRenyi_le_renyiCount (eig_nonneg ν F) hα0 hα) hm2) p) hK

/-- **The single-reading closure read through the count of order `α`, with a uniform constant**: for every
order `2p` and per-mode constant `K ≥ 0`, one `K'` serves every state and every finite family of
uncorrelated modes with `ν(e_a^{2p}) ≤ K ν(e_a²)^p`: `ν(F^{2p}) ≤ K' (R_α(λ) ν(F²))^p`, `F = ∑ e_a`,
`λ_a = ν(e_a²)`. DERIVED: `2` the even power and the variances; `0` the signs. -/
def ClosesAt (α : ℝ) : Prop :=
  ∀ (p : ℕ) (K : ℝ), 0 ≤ K → ∃ K' : ℝ, ∀ (X : Type) [TopologicalSpace X] [CompactSpace X]
    (ν : MassGap.DLRLimit.State X) (ι : Type) [Fintype ι] [Nonempty ι] (e : ι → C(X, ℝ)),
    (∀ a b, a ≠ b → ν (e a * e b) = 0) → (∀ a, ν (e a ^ (2 * p)) ≤ K * ν (e a ^ 2) ^ p) →
    ν ((∑ a, e a) ^ (2 * p)) ≤ K' * (renyiCount α (fun a => ν (e a ^ 2)) * ν ((∑ a, e a) ^ 2)) ^ p

/-- **Every order `α ≤ ½` closes**, with `K' = K`. DERIVED: `1` the unit coefficients; `2` the even power;
`1/2` the order. -/
theorem closesAt_of_le_half {α : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 2) : ClosesAt α := by
  intro p K hK
  refine ⟨K, fun X _ _ ν ι _ _ e horth h1 => ?_⟩
  have hlam : ∀ a, 0 ≤ ν (e a ^ 2) := fun a =>
    ν.nonneg _ fun x => by simp only [ContinuousMap.pow_apply]; positivity
  have hc := state_pow_comb_le ν e (fun _ => (1 : ℝ)) (fun a => ν (e a ^ 2)) hlam hK p h1
  simp only [one_smul, abs_one, one_mul] at hc
  have hv := renState_sum_sq ν e horth
  have hT0 : 0 ≤ ν ((∑ a, e a) ^ 2) := by rw [hv]; exact Finset.sum_nonneg fun a _ => hlam a
  calc ν ((∑ a, e a) ^ (2 * p)) ≤ K * (∑ a, Real.sqrt (ν (e a ^ 2))) ^ (2 * p) := hc
    _ = K * (spRenyi (fun a => ν (e a ^ 2)) * ν ((∑ a, e a) ^ 2)) ^ p := by
        rw [pow_mul, sq_sum_sqrt hlam, hv]
    _ ≤ K * (renyiCount α (fun a => ν (e a ^ 2)) * ν ((∑ a, e a) ^ 2)) ^ p :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (spRenyi_nonneg _) hT0)
          (mul_le_mul_of_nonneg_right (spRenyi_le_renyiCount hlam hα0 hα) hT0) p) hK

end Closure

/-! ## 4. The spike test -/

section Spike

variable (m : ℕ) {α : ℝ}

/-- **The binary weights in closed form**: `cw m S = exp(−(∑_{i ∈ S} 2^i)/2^{m+1})`. DERIVED: `2` the
binary base; `1` the shift. -/
theorem spCw_eq_exp (S : Finset (Fin m)) :
    cw m S = Real.exp (-((∑ i ∈ S, (2 : ℝ) ^ (i : ℕ)) / 2 ^ (m + 1))) := by
  unfold cw wt
  rw [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.sum_div]

/-- DERIVED: `0` the sign. -/
theorem spCw_pos (S : Finset (Fin m)) : 0 < cw m S := by
  rw [spCw_eq_exp]
  exact Real.exp_pos _

/-- DERIVED: `1` the upper end. -/
theorem spCw_le_one (S : Finset (Fin m)) : cw m S ≤ 1 := by
  rw [spCw_eq_exp]
  exact Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))

/-- **Every binary weight is at least `1/2`**: `∑_{i ∈ S} 2^i < 2^m`, so the exponent is at least `−1/2`.
DERIVED: `1/2` the lower end; `2` the binary base. -/
theorem spCw_ge_half (S : Finset (Fin m)) : 1 / 2 ≤ cw m S := by
  have hgeom : ∑ i ∈ Finset.range m, (2 : ℝ) ^ i = 2 ^ m - 1 := by
    have h := geom_sum_mul (2 : ℝ) m
    rw [show (2 : ℝ) - 1 = 1 by norm_num, mul_one] at h
    exact h
  have hsum : ∑ i ∈ S, (2 : ℝ) ^ (i : ℕ) ≤ 2 ^ m := by
    calc ∑ i ∈ S, (2 : ℝ) ^ (i : ℕ) ≤ ∑ i : Fin m, (2 : ℝ) ^ (i : ℕ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun i _ _ => by positivity
      _ = ∑ i ∈ Finset.range m, (2 : ℝ) ^ i := Fin.sum_univ_eq_sum_range (fun i => (2 : ℝ) ^ i) m
      _ ≤ 2 ^ m := by rw [hgeom]; linarith
  have hx : (∑ i ∈ S, (2 : ℝ) ^ (i : ℕ)) / 2 ^ (m + 1) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity), pow_succ]
    linarith
  have h := Real.add_one_le_exp (-((∑ i ∈ S, (2 : ℝ) ^ (i : ℕ)) / 2 ^ (m + 1)))
  rw [spCw_eq_exp]
  linarith

/-- **The number of cube characters**: `N = 2^m`. DERIVED: `2` the two values of a coordinate. -/
def spN : ℝ := (2 : ℝ) ^ m

/-- DERIVED: `0` the sign. -/
theorem spN_pos : 0 < spN m := by unfold spN; positivity

/-- DERIVED: `1` the lower end. -/
theorem spN_one_le : 1 ≤ spN m := by unfold spN; exact one_le_pow₀ (by norm_num)

/-- DERIVED: `2` the lower end at one coordinate. -/
theorem spN_two_le (hm : 1 ≤ m) : 2 ≤ spN m := by
  unfold spN
  calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm

/-- **The number of modes off the top**: `D = N − 1`. DERIVED: `1` the top mode. -/
def spD : ℝ := spN m - 1

/-- DERIVED: `0` the sign. -/
theorem spD_nonneg : 0 ≤ spD m := by unfold spD; linarith [spN_one_le m]

/-- DERIVED: `1` the lower end. -/
theorem spD_one_le (hm : 1 ≤ m) : 1 ≤ spD m := by unfold spD; linarith [spN_two_le m hm]

/-- DERIVED: `0` the sign. -/
theorem spD_pos (hm : 1 ≤ m) : 0 < spD m := by linarith [spD_one_le m hm]

/-- DERIVED: no numeral. -/
theorem spD_le : spD m ≤ spN m := by unfold spD; linarith

/-- DERIVED: `2` the half. -/
theorem spD_half_le (hm : 1 ≤ m) : spN m / 2 ≤ spD m := by unfold spD; linarith [spN_two_le m hm]

/-- **The nonempty sets number `D`**. DERIVED: `1` the empty set; `2` the subsets of a coordinate. -/
theorem spCard : ((Finset.univ.erase (∅ : Finset (Fin m))).card : ℝ) = spD m := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_finset,
    Fintype.card_fin, Nat.cast_sub Nat.one_le_two_pow]
  simp [spD, spN]

/-- **The exponent of the spike**: `β = (1 − α)/α`. DERIVED: `1` the Shannon order. -/
def spBeta (α : ℝ) : ℝ := (1 - α) / α

/-- **The growth exponent**: `γ = 1 − β = (2α − 1)/α`. DERIVED: `1` the linear exponent. -/
def spGam (α : ℝ) : ℝ := 1 - spBeta α

/-- **The weight off the top**: `ε = N^{−β}/2`. CHOSEN: the factor `1/2` (keeps the top strictly largest).
-/
def spEps (α : ℝ) : ℝ := spN m ^ (-spBeta α) / 2

/-- DERIVED: `0` the sign; `1` the upper end of the order. -/
theorem spBeta_nonneg (hα0 : 0 < α) (hα1 : α ≤ 1) : 0 ≤ spBeta α := div_nonneg (by linarith) hα0.le

/-- **`γ > 0` exactly above order `½`**. DERIVED: `1/2` the order. -/
theorem spGam_pos (hα : 1 / 2 < α) : 0 < spGam α := by
  have hα0 : 0 < α := by linarith
  have h : (1 - α) / α < 1 := (div_lt_one hα0).2 (by linarith)
  unfold spGam spBeta
  linarith

/-- DERIVED: `1` the upper end. -/
theorem spRpow_le_one (hα0 : 0 < α) (hα1 : α ≤ 1) : spN m ^ (-spBeta α) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (spN_one_le m) (neg_nonpos.2 (spBeta_nonneg hα0 hα1))

/-- DERIVED: `0` the sign. -/
theorem spEps_pos : 0 < spEps m α := div_pos (Real.rpow_pos_of_pos (spN_pos m) _) two_pos

/-- DERIVED: `1/2` the upper end. -/
theorem spEps_le_half (hα0 : 0 < α) (hα1 : α ≤ 1) : spEps m α ≤ 1 / 2 := by
  unfold spEps
  linarith [spRpow_le_one m hα0 hα1]

/-- DERIVED: `1/2` the upper end. -/
theorem spEps_lt_half (hα0 : 0 < α) (hα1 : α < 1) (hm : 1 ≤ m) : spEps m α < 1 / 2 := by
  have h : spN m ^ (-spBeta α) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith [spN_two_le m hm])
      (neg_neg_of_pos (div_pos (by linarith) hα0))
  unfold spEps
  linarith

/-- DERIVED: `2` the factor of `ε`. -/
theorem spEps_le_rpow : spEps m α ≤ spN m ^ (-spBeta α) := by
  unfold spEps
  linarith [Real.rpow_pos_of_pos (spN_pos m) (-spBeta α)]

/-- **The coefficients of the spike**: `c_∅ = √(1 − ε)`, `c_S = √(ε/D) · cw m S` for `S ≠ ∅`.
DERIVED: `1` the total weight. -/
def spCoef (α : ℝ) (S : Finset (Fin m)) : ℝ :=
  if S = ∅ then Real.sqrt (1 - spEps m α) else Real.sqrt (spEps m α / spD m) * cw m S

/-- **The spike screen**: `c_S χ_S`. DERIVED: no numeral. -/
def spScreen (α : ℝ) (S : Finset (Fin m)) : C(Fin m → Bool, ℝ) := spCoef m α S • walsh m S

/-- DERIVED: `1` the total weight. -/
theorem spCoef_empty : spCoef m α ∅ = Real.sqrt (1 - spEps m α) := if_pos rfl

/-- DERIVED: no numeral. -/
theorem spCoef_ne {S : Finset (Fin m)} (hS : S ≠ ∅) :
    spCoef m α S = Real.sqrt (spEps m α / spD m) * cw m S := if_neg hS

/-- DERIVED: `0` the sign. -/
theorem spCoef_nonneg (S : Finset (Fin m)) : 0 ≤ spCoef m α S := by
  unfold spCoef
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact mul_nonneg (Real.sqrt_nonneg _) (spCw_pos m S).le

/-- DERIVED: `1` the total weight; `2` the square. -/
theorem spCoef_sq_empty (hα0 : 0 < α) (hα1 : α ≤ 1) : spCoef m α ∅ ^ 2 = 1 - spEps m α := by
  rw [spCoef_empty, Real.sq_sqrt (by linarith [spEps_le_half m hα0 hα1])]

/-- DERIVED: `2` the square. -/
theorem spCoef_sq_ne {S : Finset (Fin m)} (hS : S ≠ ∅) :
    spCoef m α S ^ 2 = spEps m α / spD m * cw m S ^ 2 := by
  rw [spCoef_ne m hS, mul_pow, Real.sq_sqrt (div_nonneg (spEps_pos m).le (spD_nonneg m))]

/-- DERIVED: `1` the upper end of `cw`; `2` the square. -/
theorem spCoef_sq_ne_le {S : Finset (Fin m)} (hS : S ≠ ∅) : spCoef m α S ^ 2 ≤ spEps m α / spD m := by
  rw [spCoef_sq_ne m hS]
  exact mul_le_of_le_one_right (div_nonneg (spEps_pos m).le (spD_nonneg m))
    (pow_le_one₀ (spCw_pos m S).le (spCw_le_one m S))

/-- A nonempty set of coordinates needs a coordinate. DERIVED: `1` the least count. -/
theorem spOne_le {S : Finset (Fin m)} (hS : S ≠ ∅) : 1 ≤ m := by
  obtain ⟨i, -⟩ := Finset.nonempty_iff_ne_empty.2 hS
  exact Nat.one_le_iff_ne_zero.2 (Fin.pos i).ne'

/-- **The spike modes are uncorrelated**, with variances `c_S²`. DERIVED: `0` the off-diagonal; `2` the
square. -/
theorem sp_mul (S T : Finset (Fin m)) :
    cubeState m (spScreen m α S * spScreen m α T) = if S = T then spCoef m α S ^ 2 else 0 := by
  simp only [spScreen, smul_mul_smul_comm, (cubeState m).map_smul, cube_walsh_mul]
  split_ifs with h
  · subst h; ring
  · ring

/-- DERIVED: `0` the off-diagonal. -/
theorem sp_orth (S T : Finset (Fin m)) (h : S ≠ T) :
    cubeState m (spScreen m α S * spScreen m α T) = 0 := by
  rw [sp_mul, if_neg h]

/-- **Every spike mode is hypercontractive with constant `1` at every order**: `ν((c_S χ_S)^{2p}) =
(c_S²)^p`. DERIVED: `2` the even power. -/
theorem sp_pow (S : Finset (Fin m)) (p : ℕ) :
    cubeState m (spScreen m α S ^ (2 * p)) = (spCoef m α S ^ 2) ^ p := by
  have hw : walsh m S ^ (2 * p) = 1 := by rw [pow_mul, sq, walsh_mul_self, one_pow]
  rw [spScreen, smul_pow, hw, (cubeState m).map_smul, (cubeState m).map_one, mul_one, pow_mul]

/-- DERIVED: `2` the variance. -/
theorem sp_sq (S : Finset (Fin m)) : cubeState m (spScreen m α S ^ 2) = spCoef m α S ^ 2 := by
  simpa using sp_pow m (α := α) S 1

/-- **The variance of the spike reading**: `ν(F²) = ∑_S c_S²`. DERIVED: `2` the variance. -/
theorem sp_var : cubeState m ((∑ S, spScreen m α S) ^ 2) = ∑ S, spCoef m α S ^ 2 := by
  rw [renState_sum_sq (cubeState m) (spScreen m α) (sp_orth m)]
  exact Finset.sum_congr rfl fun S _ => sp_sq m S

/-- DERIVED: `0`, `1` the lower and upper ends. -/
theorem renMul_div_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a * (b / a) ≤ b := by
  rcases ha.eq_or_lt with h | h
  · rw [← h, zero_mul]; exact hb
  · exact (mul_div_cancel₀ _ h.ne').le

/-- **`ν(F²) ≤ 1`**. DERIVED: `1` the total weight; `2` the square. -/
theorem sp_T_le (hα0 : 0 < α) (hα1 : α ≤ 1) : ∑ S, spCoef m α S ^ 2 ≤ 1 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (∅ : Finset (Fin m))), spCoef_sq_empty m hα0 hα1]
  have hrest : ∑ S ∈ Finset.univ.erase ∅, spCoef m α S ^ 2 ≤ spEps m α := by
    calc ∑ S ∈ Finset.univ.erase ∅, spCoef m α S ^ 2
        ≤ ∑ S ∈ Finset.univ.erase (∅ : Finset (Fin m)), spEps m α / spD m :=
          Finset.sum_le_sum fun S hS => spCoef_sq_ne_le m (Finset.ne_of_mem_erase hS)
      _ = spD m * (spEps m α / spD m) := by rw [Finset.sum_const, nsmul_eq_mul, spCard]
      _ ≤ spEps m α := renMul_div_le (spD_nonneg m) (spEps_pos m).le
  linarith

/-- **`ν(F²) ≥ 1/2`**. DERIVED: `1/2` the lower end; `2` the square. -/
theorem sp_T_ge (hα0 : 0 < α) (hα1 : α ≤ 1) : 1 / 2 ≤ ∑ S, spCoef m α S ^ 2 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (∅ : Finset (Fin m))), spCoef_sq_empty m hα0 hα1]
  have h0 : 0 ≤ ∑ S ∈ Finset.univ.erase ∅, spCoef m α S ^ 2 := Finset.sum_nonneg fun S _ => sq_nonneg _
  linarith [spEps_le_half m hα0 hα1]

/-- **The top weight is strictly largest** for `α < 1`. DERIVED: `2` the square. -/
theorem sp_lt_top (hα0 : 0 < α) (hα1 : α < 1) {S : Finset (Fin m)} (hS : S ≠ ∅) :
    spCoef m α S ^ 2 < spCoef m α ∅ ^ 2 := by
  have hm := spOne_le m hS
  rw [spCoef_sq_empty m hα0 hα1.le]
  have h1 : spEps m α / spD m ≤ spEps m α := div_le_self (spEps_pos m).le (spD_one_le m hm)
  linarith [spCoef_sq_ne_le m (α := α) hS, spEps_lt_half m hα0 hα1 hm]

/-- **The squared spike weights are distinct** (`ApertureCount.cw_sq_injective` off the top).
DERIVED: `2` the square. -/
theorem sp_sq_injective (hα0 : 0 < α) (hα1 : α < 1) :
    Function.Injective fun S : Finset (Fin m) => spCoef m α S ^ 2 := by
  intro S T h
  have h' : spCoef m α S ^ 2 = spCoef m α T ^ 2 := h
  by_cases hS : S = ∅ <;> by_cases hT : T = ∅
  · rw [hS, hT]
  · rw [hS] at h'
    exact absurd h' (sp_lt_top m hα0 hα1 hT).ne'
  · rw [hT] at h'
    exact absurd h' (sp_lt_top m hα0 hα1 hS).ne
  · have hm := spOne_le m hS
    rw [spCoef_sq_ne m hS, spCoef_sq_ne m hT] at h'
    have hc : 0 < spEps m α / spD m := div_pos (spEps_pos m) (spD_pos m hm)
    exact cw_sq_injective m (mul_left_cancel₀ hc.ne' h')

/-- **The spike Gram matrix is diagonal**. DERIVED: `2` the square. -/
theorem sp_gram : gram (cubeState m) (spScreen m α) = Matrix.diagonal fun S => spCoef m α S ^ 2 := by
  ext S T
  rw [Matrix.diagonal_apply]
  exact sp_mul m S T

/-- **Every unit eigenvector's mode meets the per-mode bound with equality**. DERIVED: `2` the even
power. -/
theorem sp_unitEig_pow (hα0 : 0 < α) (hα1 : α < 1) (p : ℕ) {lam : ℝ} {v : Finset (Fin m) → ℝ}
    (hv : IsUnitEig (gram (cubeState m) (spScreen m α)) lam v) :
    cubeState m ((∑ S, v S • spScreen m α S) ^ (2 * p)) = lam ^ p := by
  obtain ⟨y, hlam, hy, hz⟩ := isUnitEig_diag (sp_sq_injective m hα0 hα1) (sp_gram m) hv
  have hlam' : lam = spCoef m α y ^ 2 := hlam
  rw [Finset.sum_eq_single y (fun z _ hzy => by rw [hz z hzy, zero_smul])
    (fun h => absurd (Finset.mem_univ y) h), smul_pow, (cubeState m).map_smul, sp_pow, pow_mul (v y),
    hy, one_pow, one_mul, hlam']

/-- **The basis-free H1 holds on the spike with `C = 1`**, at every order, Wick exponent and `m`.
DERIVED: `1` the constant `C`; `2` the even power; `0` the sign. -/
theorem sp_H1 (hα0 : 0 < α) (hα1 : α < 1) (p w : ℕ) {lam : ℝ} {v : Finset (Fin m) → ℝ}
    (hv : IsUnitEig (gram (cubeState m) (spScreen m α)) lam v) :
    cubeState m ((∑ S, v S • spScreen m α S) ^ (2 * p)) ≤ ((2 * p).factorial : ℝ) ^ w * (1 * lam) ^ p := by
  have h := sp_unitEig_pow m hα0 hα1 p hv
  have h0 : 0 ≤ lam ^ p := by
    rw [← h]
    exact (cubeState m).nonneg _ fun x => by
      simp only [ContinuousMap.pow_apply]; exact (even_two_mul p).pow_nonneg _
  rw [h, one_mul]
  exact le_mul_of_one_le_left h0 (one_le_pow₀ (by exact_mod_cast Nat.factorial_pos _))

/-- **The peak**: `∑_S c_S ≥ D √(ε/D)/2`. DERIVED: `1/2` the lower end of `cw`; `2` its reciprocal. -/
theorem sp_peak : spD m * (Real.sqrt (spEps m α / spD m) / 2) ≤ ∑ S, spCoef m α S := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (∅ : Finset (Fin m)))]
  have h := Finset.card_nsmul_le_sum (Finset.univ.erase (∅ : Finset (Fin m))) (spCoef m α)
    (Real.sqrt (spEps m α / spD m) / 2) fun S hS => by
      rw [spCoef_ne m (Finset.ne_of_mem_erase hS)]
      have := spCw_ge_half m S
      have h0 := Real.sqrt_nonneg (spEps m α / spD m)
      nlinarith
  rw [nsmul_eq_mul, spCard] at h
  linarith [spCoef_nonneg m (α := α) ∅]

/-- **The square of the peak grows like `N^γ`**: `N^γ/16 ≤ (D √(ε/D)/2)²`. DERIVED: `16 = 4 · 4` (`D ≥ N/2`,
the `1/2` of `ε`, and the square of the `1/2` of the peak); `1` the shift `γ = 1 − β`. -/
theorem sp_peak_sq (hm : 1 ≤ m) :
    spN m ^ spGam α / 16 ≤ (spD m * (Real.sqrt (spEps m α / spD m) / 2)) ^ 2 := by
  have hD := spD_pos m hm
  have hε := spEps_pos m (α := α)
  have e1 : (spD m * (Real.sqrt (spEps m α / spD m) / 2)) ^ 2 = spD m * spEps m α / 4 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (div_nonneg hε.le hD.le)]
    calc spD m ^ 2 * (spEps m α / spD m / 2 ^ 2) = spD m * (spEps m α / spD m) * spD m / 4 := by ring
      _ = spD m * spEps m α / 4 := by rw [mul_div_cancel₀ _ hD.ne']; ring
  have e2 : spN m ^ spGam α = spN m ^ (-spBeta α) * spN m := by
    rw [← Real.rpow_add_one (spN_pos m).ne']
    congr 1
    unfold spGam
    ring
  have e3 : spN m ^ (-spBeta α) = 2 * spEps m α := by unfold spEps; ring
  have h3 : spN m / 2 * spEps m α ≤ spD m * spEps m α :=
    mul_le_mul_of_nonneg_right (spD_half_le m hm) hε.le
  rw [e1, e2, e3]
  calc 2 * spEps m α * spN m / 16 = spN m / 2 * spEps m α / 4 := by ring
    _ ≤ spD m * spEps m α / 4 := div_le_div_of_nonneg_right h3 (by norm_num)

/-- **The moments of the spike reading**: `ν(F^{2p}) ≥ (N^γ/16)^p / N`, from the point `(+1, …, +1)`.
DERIVED: `16` as in `sp_peak_sq`; `2` the even power. -/
theorem sp_moment_ge (hm : 1 ≤ m) (p : ℕ) :
    (spN m ^ spGam α / 16) ^ p / spN m ≤ cubeState m ((∑ S, spScreen m α S) ^ (2 * p)) := by
  have hval : (∑ S, spScreen m α S) (fun _ => false) = ∑ S, spCoef m α S := by
    simp only [spScreen, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
      walsh, ContinuousMap.coe_mk, sgnB_false, Finset.prod_const_one, mul_one]
  have hP0 : 0 ≤ spD m * (Real.sqrt (spEps m α / spD m) / 2) :=
    mul_nonneg (spD_nonneg m) (by positivity)
  have hsingle : (∑ S, spCoef m α S) ^ (2 * p) ≤ ∑ x, ((∑ S, spScreen m α S) ^ (2 * p)) x := by
    have h := Finset.single_le_sum (f := fun x => ((∑ S, spScreen m α S) ^ (2 * p)) x)
      (fun x _ => by simp only [ContinuousMap.pow_apply]; exact (even_two_mul p).pow_nonneg _)
      (Finset.mem_univ (fun _ => false))
    simp only [ContinuousMap.pow_apply] at h ⊢
    rw [hval] at h
    exact h
  have hN := spN_pos m
  have hg0 : 0 ≤ spN m ^ spGam α / 16 := div_nonneg (Real.rpow_nonneg hN.le _) (by norm_num)
  calc (spN m ^ spGam α / 16) ^ p / spN m
      ≤ ((spD m * (Real.sqrt (spEps m α / spD m) / 2)) ^ 2) ^ p / spN m :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ hg0 (sp_peak_sq m hm) p) hN.le
    _ = (spD m * (Real.sqrt (spEps m α / spD m) / 2)) ^ (2 * p) / spN m := by rw [pow_mul]
    _ ≤ (∑ S, spCoef m α S) ^ (2 * p) / spN m :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ hP0 (sp_peak m) _) hN.le
    _ ≤ (∑ x, ((∑ S, spScreen m α S) ^ (2 * p)) x) / spN m := div_le_div_of_nonneg_right hsingle hN.le
    _ = cubeState m ((∑ S, spScreen m α S) ^ (2 * p)) := (cubeState_apply m _).symm

/-- **The off-top mass at order `α`**: `D (ε/D)^α ≤ N^{1−α} N^{−(1−α)} = 1`. DERIVED: `1` the bound and
the Shannon order. -/
theorem sp_D_rpow_le (hα0 : 0 < α) (hα1 : α < 1) (hm : 1 ≤ m) :
    spD m * (spEps m α / spD m) ^ α ≤ 1 := by
  have hD := spD_pos m hm
  have hN := spN_pos m
  have hε := spEps_pos m (α := α)
  rw [Real.div_rpow hε.le hD.le]
  have e1 : spD m * (spEps m α ^ α / spD m ^ α) = spD m ^ (1 - α) * spEps m α ^ α := by
    rw [Real.rpow_sub hD, Real.rpow_one]
    ring
  have h1 : spD m ^ (1 - α) ≤ spN m ^ (1 - α) := Real.rpow_le_rpow hD.le (spD_le m) (by linarith)
  have h2 : spEps m α ^ α ≤ spN m ^ (-(1 - α)) := by
    calc spEps m α ^ α ≤ (spN m ^ (-spBeta α)) ^ α :=
          Real.rpow_le_rpow hε.le (spEps_le_rpow m) hα0.le
      _ = spN m ^ (-spBeta α * α) := (Real.rpow_mul hN.le _ _).symm
      _ = spN m ^ (-(1 - α)) := by unfold spBeta; rw [neg_mul, div_mul_cancel₀ _ hα0.ne']
  have h3 : spN m ^ (1 - α) * spN m ^ (-(1 - α)) = 1 := by
    rw [← Real.rpow_add hN, add_neg_cancel, Real.rpow_zero]
  rw [e1]
  calc spD m ^ (1 - α) * spEps m α ^ α ≤ spN m ^ (1 - α) * spN m ^ (-(1 - α)) :=
        mul_le_mul h1 h2 (Real.rpow_nonneg hε.le _) (Real.rpow_nonneg hN.le _)
    _ = 1 := h3

/-- **The count of order `α ∈ (0, 1)` stays bounded on the spike**: `R_α ≤ 4^{1/(1−α)}`.
DERIVED: `4 = 2 · 2` (`ν(F²) ≥ 1/2` and the two parts of the sum). -/
theorem sp_renyi_le (hα0 : 0 < α) (hα1 : α < 1) (hm : 1 ≤ m) :
    renyiCount α (fun S : Finset (Fin m) => spCoef m α S ^ 2) ≤ (4 : ℝ) ^ (1 / (1 - α)) := by
  have hT1 := sp_T_le m hα0 hα1.le
  have hT2 := sp_T_ge m hα0 hα1.le
  have hT0 : 0 < ∑ U, spCoef m α U ^ 2 := by linarith
  have hterm : ∀ S : Finset (Fin m),
      (spCoef m α S ^ 2 / ∑ U, spCoef m α U ^ 2) ^ α ≤ 2 * (spCoef m α S ^ 2) ^ α := by
    intro S
    have hc := Real.rpow_nonneg (sq_nonneg (spCoef m α S)) α
    have hTα : ∑ U, spCoef m α U ^ 2 ≤ (∑ U, spCoef m α U ^ 2) ^ α := by
      have := Real.rpow_le_rpow_of_exponent_ge hT0 hT1 hα1.le
      rwa [Real.rpow_one] at this
    rw [Real.div_rpow (sq_nonneg _) hT0.le]
    calc (spCoef m α S ^ 2) ^ α / (∑ U, spCoef m α U ^ 2) ^ α
        ≤ (spCoef m α S ^ 2) ^ α / ∑ U, spCoef m α U ^ 2 := div_le_div_of_nonneg_left hc hT0 hTα
      _ ≤ 2 * (spCoef m α S ^ 2) ^ α := by
          rw [div_le_iff₀ hT0]
          nlinarith
  have hsum : ∑ S, (spCoef m α S ^ 2) ^ α ≤ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (∅ : Finset (Fin m))), spCoef_sq_empty m hα0 hα1.le]
    have h1 : (1 - spEps m α) ^ α ≤ 1 :=
      Real.rpow_le_one (by linarith [spEps_le_half m hα0 hα1.le]) (by linarith [spEps_pos m (α := α)])
        hα0.le
    have h2 : ∑ S ∈ Finset.univ.erase ∅, (spCoef m α S ^ 2) ^ α ≤ spD m * (spEps m α / spD m) ^ α := by
      calc ∑ S ∈ Finset.univ.erase ∅, (spCoef m α S ^ 2) ^ α
          ≤ ∑ S ∈ Finset.univ.erase (∅ : Finset (Fin m)), (spEps m α / spD m) ^ α :=
            Finset.sum_le_sum fun S hS =>
              Real.rpow_le_rpow (sq_nonneg _) (spCoef_sq_ne_le m (Finset.ne_of_mem_erase hS)) hα0.le
        _ = spD m * (spEps m α / spD m) ^ α := by rw [Finset.sum_const, nsmul_eq_mul, spCard]
    linarith [sp_D_rpow_le m hα0 hα1 hm]
  rw [renyiCount_of_ne hα1.ne]
  refine Real.rpow_le_rpow (renyiSum_nonneg α fun S => sq_nonneg _) ?_
    (div_nonneg zero_le_one (by linarith))
  calc renyiSum α (fun S : Finset (Fin m) => spCoef m α S ^ 2)
      = ∑ S, (spCoef m α S ^ 2 / ∑ U, spCoef m α U ^ 2) ^ α := rfl
    _ ≤ ∑ S, 2 * (spCoef m α S ^ 2) ^ α := Finset.sum_le_sum fun S _ => hterm S
    _ = 2 * ∑ S, (spCoef m α S ^ 2) ^ α := by rw [Finset.mul_sum]
    _ ≤ 2 * 2 := by linarith
    _ = 4 := by norm_num

end Spike

/-! ## 4b. Every order `α > ½` fails -/

section Fail

/-- **The counts separate above order `½`**: for every `α > ½` one `C` such that for every `B` a positive
weight vector has `R_α ≤ C` and `R_½ ≥ B` (`ApertureCount.spRenyi_unbounded_at_bounded_spDim` is the case
`α = 1`). DERIVED: `16` as in `sp_peak_sq`. CHOSEN: the reference order `3/4` for `α ≥ 3/4`. -/
theorem counts_separate {α : ℝ} (hα : 1 / 2 < α) :
    ∃ C : ℝ, ∀ B : ℝ, ∃ (m : ℕ) (w : Finset (Fin m) → ℝ),
      (∀ S, 0 < w S) ∧ renyiCount α w ≤ C ∧ B ≤ spRenyi w := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min α (3 / 4) := ⟨_, rfl⟩
  have hr12 : 1 / 2 < r := by rw [hr]; exact lt_min hα (by norm_num)
  have hr0 : 0 < r := by linarith
  have hr1 : r < 1 := by rw [hr]; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hrα : r ≤ α := by rw [hr]; exact min_le_left _ _
  have hγ := spGam_pos hr12
  have htend : Tendsto (fun m : ℕ => spN m ^ spGam r) atTop atTop :=
    (tendsto_rpow_atTop hγ).comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  refine ⟨(4 : ℝ) ^ (1 / (1 - r)), fun B => ?_⟩
  obtain ⟨m, hmB, hm⟩ := ((htend.eventually_ge_atTop (16 * B)).and (eventually_ge_atTop 1)).exists
  have hT1 := sp_T_le m hr0 hr1.le
  have hT0 : 0 < ∑ U, spCoef m r U ^ 2 := by linarith [sp_T_ge m hr0 hr1.le]
  refine ⟨m, fun S => spCoef m r S ^ 2, fun S => ?_, ?_, ?_⟩
  · show 0 < spCoef m r S ^ 2
    by_cases hS : S = ∅
    · rw [hS, spCoef_sq_empty m hr0 hr1.le]
      linarith [spEps_le_half m hr0 hr1.le]
    · rw [spCoef_sq_ne m hS]
      exact mul_pos (div_pos (spEps_pos m) (spD_pos m hm)) (pow_pos (spCw_pos m S) 2)
  · exact (renyiCount_antitone (fun S => sq_nonneg _) hT0 hr0 hrα).trans (sp_renyi_le m hr0 hr1 hm)
  · have hge : ∑ S, spCoef m r S ≤ ∑ S, Real.sqrt (spCoef m r S ^ 2 / ∑ U, spCoef m r U ^ 2) :=
      Finset.sum_le_sum fun S _ => Real.le_sqrt_of_sq_le (le_div_self (sq_nonneg _) hT0 hT1)
    have hR : spRenyi (fun S : Finset (Fin m) => spCoef m r S ^ 2)
        = (∑ S, Real.sqrt (spCoef m r S ^ 2 / ∑ U, spCoef m r U ^ 2)) ^ 2 := rfl
    have hP0 : 0 ≤ spD m * (Real.sqrt (spEps m r / spD m) / 2) :=
      mul_nonneg (spD_nonneg m) (by positivity)
    rw [hR]
    calc B ≤ spN m ^ spGam r / 16 := by linarith
      _ ≤ (spD m * (Real.sqrt (spEps m r / spD m) / 2)) ^ 2 := sp_peak_sq m hm
      _ ≤ (∑ S, spCoef m r S) ^ 2 := pow_le_pow_left₀ hP0 (sp_peak m) 2
      _ ≤ (∑ S, Real.sqrt (spCoef m r S ^ 2 / ∑ U, spCoef m r U ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (Finset.sum_nonneg fun S _ => spCoef_nonneg m S) hge 2

/-- **No order above `½` closes**: for every `α > ½`, `ClosesAt α` fails, at the order `2p`,
`p = ⌈2/γ⌉₊`, and the per-mode constant `K = 1`, on the spike of order `min α (3/4)`.
DERIVED: `1` the per-mode constant; `16`, `4` as in `sp_peak_sq`, `sp_renyi_le`; `2` the exponent of
`N^{γp} ≥ N²`. CHOSEN: the reference order `3/4`. -/
theorem not_closesAt {α : ℝ} (hα : 1 / 2 < α) : ¬ ClosesAt α := by
  intro hC
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min α (3 / 4) := ⟨_, rfl⟩
  have hr12 : 1 / 2 < r := by rw [hr]; exact lt_min hα (by norm_num)
  have hr0 : 0 < r := by linarith
  have hr1 : r < 1 := by rw [hr]; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hrα : r ≤ α := by rw [hr]; exact min_le_left _ _
  have hγ := spGam_pos hr12
  obtain ⟨p, hp0⟩ : ∃ p : ℕ, p = ⌈2 / spGam r⌉₊ := ⟨_, rfl⟩
  have hp : 2 ≤ spGam r * p := by
    have h := Nat.le_ceil (2 / spGam r)
    rw [← hp0, div_le_iff₀ hγ] at h
    rw [mul_comm]
    exact h
  obtain ⟨K', hK'⟩ := hC p 1 zero_le_one
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = (4 : ℝ) ^ (1 / (1 - r)) := ⟨_, rfl⟩
  have hbound : ∀ m : ℕ, 1 ≤ m → spN m ≤ 16 ^ p * (|K'| * C ^ p) := by
    intro m hm
    have h1 : ∀ S : Finset (Fin m),
        cubeState m (spScreen m r S ^ (2 * p)) ≤ 1 * cubeState m (spScreen m r S ^ 2) ^ p :=
      fun S => le_of_eq (by rw [sp_pow, sp_sq, one_mul])
    have hcl := hK' (Fin m → Bool) (cubeState m) (Finset (Fin m)) (spScreen m r) (sp_orth m) h1
    simp only [sp_sq, sp_var] at hcl
    have hT1 := sp_T_le m hr0 hr1.le
    have hT0 : 0 < ∑ U, spCoef m r U ^ 2 := by linarith [sp_T_ge m hr0 hr1.le]
    have hR : renyiCount α (fun S : Finset (Fin m) => spCoef m r S ^ 2) ≤ C := by
      rw [hCdef]
      exact (renyiCount_antitone (fun S => sq_nonneg _) hT0 hr0 hrα).trans (sp_renyi_le m hr0 hr1 hm)
    have hR0 := renyiCount_nonneg α (fun S : Finset (Fin m) => sq_nonneg (spCoef m r S))
    have hRT0 : 0 ≤ renyiCount α (fun S : Finset (Fin m) => spCoef m r S ^ 2) * ∑ U, spCoef m r U ^ 2 :=
      mul_nonneg hR0 hT0.le
    have hRT : renyiCount α (fun S : Finset (Fin m) => spCoef m r S ^ 2) * ∑ U, spCoef m r U ^ 2 ≤ C :=
      (mul_le_of_le_one_right hR0 hT1).trans hR
    have hup : K' * (renyiCount α (fun S : Finset (Fin m) => spCoef m r S ^ 2)
        * ∑ U, spCoef m r U ^ 2) ^ p ≤ |K'| * C ^ p :=
      (mul_le_mul_of_nonneg_right (le_abs_self K') (pow_nonneg hRT0 p)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hRT0 hRT p) (abs_nonneg K'))
    have hchain := (sp_moment_ge m (α := r) hm p).trans (hcl.trans hup)
    have hN := spN_pos m
    have hNγ : spN m ^ 2 ≤ (spN m ^ spGam r) ^ p := by
      rw [← Real.rpow_natCast (spN m ^ spGam r) p, ← Real.rpow_mul hN.le, ← Real.rpow_natCast (spN m) 2]
      exact Real.rpow_le_rpow_of_exponent_le (spN_one_le m) (by push_cast; exact hp)
    rw [div_pow, div_div, div_le_iff₀ (mul_pos (by positivity) hN)] at hchain
    have hmul : spN m * spN m ≤ (16 ^ p * (|K'| * C ^ p)) * spN m := by
      calc spN m * spN m = spN m ^ 2 := (sq _).symm
        _ ≤ (spN m ^ spGam r) ^ p := hNγ
        _ ≤ |K'| * C ^ p * (16 ^ p * spN m) := hchain
        _ = (16 ^ p * (|K'| * C ^ p)) * spN m := by ring
    exact le_of_mul_le_mul_right hmul hN
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (16 ^ p * (|K'| * C ^ p)) (by norm_num : (1 : ℝ) < 2)
  have hb := hbound (n + 1) (by omega)
  have h2 : (2 : ℝ) ^ n ≤ spN (n + 1) := by
    unfold spN
    exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
  linarith

end Fail

/-! ## 5. The sharp order -/

/-- **Order `½` is the sharp Rényi order of the closure**: the closure read through `R_α` with a uniform
constant holds for every `α ∈ (0, ½]` and fails for every `α > ½`. DERIVED: `1/2` the order; `0` the
lower end. -/
theorem renyi_order_sharp :
    (∀ α : ℝ, 0 < α → α ≤ 1 / 2 → ClosesAt α) ∧ (∀ α : ℝ, 1 / 2 < α → ¬ ClosesAt α) :=
  ⟨fun _ h0 h => closesAt_of_le_half h0 h, fun _ h => not_closesAt h⟩

/-- **`½` is the greatest order that closes**. DERIVED: `1/2` the order; `0` the lower end. -/
theorem half_isGreatest : IsGreatest {α : ℝ | 0 < α ∧ ClosesAt α} (1 / 2) :=
  ⟨⟨by norm_num, closesAt_of_le_half (by norm_num) le_rfl⟩,
    fun _ hα => not_lt.1 fun hlt => not_closesAt hlt hα.2⟩

/-! ## 6. The free spectrum -/

section Free

/-- **Where `R_½ ≤ c exp H`, the orders in `[½, 1]` agree up to `c`**: `R_α ≤ R_½ ≤ c R_α`.
DERIVED: `1/2`, `1` the ends of the interval. -/
theorem free_orders_comparable {κ : Type*} [Fintype κ] {w : κ → ℝ} (hw : ∀ k, 0 ≤ w k)
    (hS : 0 < ∑ j, w j) {c : ℝ} (hc0 : 0 ≤ c) (hc : spRenyi w ≤ c * spDim w) {α : ℝ} (hα : 1 / 2 ≤ α)
    (hα1 : α ≤ 1) : renyiCount α w ≤ spRenyi w ∧ spRenyi w ≤ c * renyiCount α w := by
  refine ⟨?_, hc.trans (mul_le_mul_of_nonneg_left
    (spDim_le_renyiCount_of_le_one hw hS (by linarith) hα1) hc0)⟩
  rw [← renyiCount_half]
  exact renyiCount_antitone hw hS (by norm_num) hα

/-- **On the free flowed box spectrum the orders in `[½, 1]` agree up to `A_κ² e²`** (`FreeLevels.free_h3_local`),
uniformly in the zoom `K`. DERIVED: `1/2`, `1` the ends; `2` the squares. Inherited: the hypotheses and the
factor of `FreeLevels.free_h3_local`. -/
theorem free_orders {L t : ℝ} {K : ℕ} {κ' : Type*} [Fintype κ'] (hK : 0 < K) (hL : 0 < L) (ht : 0 < t)
    {m : ℕ} (hm : 0 < m) {τ κ : ℝ} (hτ : 0 < τ) (hτσ : τ ≤ 2 * t / L ^ 2) (hκ : 0 ≤ κ)
    {w : (Fin (2 * m) → Fin K) → ℝ} (hw : ∀ k, 0 < w k) (htop : ∀ k, w k ≤ w (fun _ => ⟨0, hK⟩))
    (hloc : ∀ k, Real.log (w (fun _ => ⟨0, hK⟩) / w k)
      ≤ κ * (FreeLevels.boxU L t K k - FreeLevels.boxU L t K (fun _ : Fin (2 * m) => (⟨0, hK⟩ : Fin K))))
    {lam : κ' → ℝ} (e : κ' ≃ (Fin (2 * m) → Fin K))
    (hlam : lam = FreeLevels.heatSpec w (FreeLevels.boxU L t K) ∘ e) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {α : ℝ} (hα : 1 / 2 ≤ α) (hα1 : α ≤ 1) :
    renyiCount α lam ≤ spRenyi lam
      ∧ spRenyi lam ≤ FreeLevels.renyiFactorL m κ a ^ 2 * Real.exp 1 ^ 2 * renyiCount α lam := by
  have h := (FreeLevels.free_h3_local hK hL ht hm hτ hτσ hκ hw htop hloc e hlam ha0 ha1).2.2
  have hpos : ∀ k, 0 < lam k := fun k => by
    rw [hlam]
    exact mul_pos (hw _) (Real.exp_pos _)
  have hS : 0 < ∑ k, lam k :=
    Finset.sum_pos (fun k _ => hpos k) ⟨e.symm (fun _ => ⟨0, hK⟩), Finset.mem_univ _⟩
  exact free_orders_comparable (fun k => (hpos k).le) hS (by positivity) h hα hα1

end Free

end MassGap.RenyiOrder

end

#print axioms MassGap.RenyiOrder.renyiCount_one
#print axioms MassGap.RenyiOrder.renyiCount_of_ne
#print axioms MassGap.RenyiOrder.renyiSum_nonneg
#print axioms MassGap.RenyiOrder.renyiCount_nonneg
#print axioms MassGap.RenyiOrder.renyiCount_half
#print axioms MassGap.RenyiOrder.spRenyi_nonneg
#print axioms MassGap.RenyiOrder.renP_nonneg
#print axioms MassGap.RenyiOrder.renP_sum
#print axioms MassGap.RenyiOrder.renSum_pos
#print axioms MassGap.RenyiOrder.renTerm_le
#print axioms MassGap.RenyiOrder.renShannon_le
#print axioms MassGap.RenyiOrder.spDim_le_renyiCount
#print axioms MassGap.RenyiOrder.renyiCount_le_spDim
#print axioms MassGap.RenyiOrder.renMul_rpow
#print axioms MassGap.RenyiOrder.renMul_rpow_rpow
#print axioms MassGap.RenyiOrder.renTheta_mul
#print axioms MassGap.RenyiOrder.renJensen_lt_one
#print axioms MassGap.RenyiOrder.renJensen_gt_one
#print axioms MassGap.RenyiOrder.renyiCount_anti_lt_one
#print axioms MassGap.RenyiOrder.renyiCount_anti_gt_one
#print axioms MassGap.RenyiOrder.renyiCount_antitone
#print axioms MassGap.RenyiOrder.renyiCount_two_le_spDim_le_spRenyi
#print axioms MassGap.RenyiOrder.spDim_le_renyiCount_of_le_one
#print axioms MassGap.RenyiOrder.spRenyi_le_renyiCount
#print axioms MassGap.RenyiOrder.sq_sum_sqrt
#print axioms MassGap.RenyiOrder.renState_sum_sq
#print axioms MassGap.RenyiOrder.state_pow_le_renyiCount
#print axioms MassGap.RenyiOrder.closesAt_of_le_half
#print axioms MassGap.RenyiOrder.spCw_eq_exp
#print axioms MassGap.RenyiOrder.spCw_pos
#print axioms MassGap.RenyiOrder.spCw_le_one
#print axioms MassGap.RenyiOrder.spCw_ge_half
#print axioms MassGap.RenyiOrder.spN_pos
#print axioms MassGap.RenyiOrder.spN_one_le
#print axioms MassGap.RenyiOrder.spN_two_le
#print axioms MassGap.RenyiOrder.spD_nonneg
#print axioms MassGap.RenyiOrder.spD_one_le
#print axioms MassGap.RenyiOrder.spD_pos
#print axioms MassGap.RenyiOrder.spD_le
#print axioms MassGap.RenyiOrder.spD_half_le
#print axioms MassGap.RenyiOrder.spCard
#print axioms MassGap.RenyiOrder.spBeta_nonneg
#print axioms MassGap.RenyiOrder.spGam_pos
#print axioms MassGap.RenyiOrder.spRpow_le_one
#print axioms MassGap.RenyiOrder.spEps_pos
#print axioms MassGap.RenyiOrder.spEps_le_half
#print axioms MassGap.RenyiOrder.spEps_lt_half
#print axioms MassGap.RenyiOrder.spEps_le_rpow
#print axioms MassGap.RenyiOrder.spCoef_empty
#print axioms MassGap.RenyiOrder.spCoef_ne
#print axioms MassGap.RenyiOrder.spCoef_nonneg
#print axioms MassGap.RenyiOrder.spCoef_sq_empty
#print axioms MassGap.RenyiOrder.spCoef_sq_ne
#print axioms MassGap.RenyiOrder.spCoef_sq_ne_le
#print axioms MassGap.RenyiOrder.spOne_le
#print axioms MassGap.RenyiOrder.sp_mul
#print axioms MassGap.RenyiOrder.sp_orth
#print axioms MassGap.RenyiOrder.sp_pow
#print axioms MassGap.RenyiOrder.sp_sq
#print axioms MassGap.RenyiOrder.sp_var
#print axioms MassGap.RenyiOrder.renMul_div_le
#print axioms MassGap.RenyiOrder.sp_T_le
#print axioms MassGap.RenyiOrder.sp_T_ge
#print axioms MassGap.RenyiOrder.sp_lt_top
#print axioms MassGap.RenyiOrder.sp_sq_injective
#print axioms MassGap.RenyiOrder.sp_gram
#print axioms MassGap.RenyiOrder.sp_unitEig_pow
#print axioms MassGap.RenyiOrder.sp_H1
#print axioms MassGap.RenyiOrder.sp_peak
#print axioms MassGap.RenyiOrder.sp_peak_sq
#print axioms MassGap.RenyiOrder.sp_moment_ge
#print axioms MassGap.RenyiOrder.sp_D_rpow_le
#print axioms MassGap.RenyiOrder.sp_renyi_le
#print axioms MassGap.RenyiOrder.counts_separate
#print axioms MassGap.RenyiOrder.not_closesAt
#print axioms MassGap.RenyiOrder.renyi_order_sharp
#print axioms MassGap.RenyiOrder.half_isGreatest
#print axioms MassGap.RenyiOrder.free_orders_comparable
#print axioms MassGap.RenyiOrder.free_orders
