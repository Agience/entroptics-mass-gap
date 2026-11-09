import Mathlib
import MassGap.ObserverGapScale
import MassGap.ObserverGapSplit

/-!
# MassGap.ObserverResidual — the residual's gap without an invariant coarse span

`ObserverGapSplit.gapAt_iff_split` splits the gap across a coarse span `C` that `T` maps into
itself. The observer's coarse view is not invariant in general (a block observable at time zero is
not a block observable after one fine step), and the observer's pre-space need not carry an
orthogonal split. This module states what replaces invariance, in three forms, each feeding
`ObserverGapScale.observer_M_iff_gap`.

All statements are about `Transfer.TransferData A` and one power `T^k`; `E_k(x) = ⟨x, x⟩ − ⟨T^k x, T^k x⟩`
is the decay of `x` over `k` steps (a non-negative quadratic form, `form_pow_le`).

1. **Slow vectors are near the coarse span** (`iter_contract_of_near_coarse`,
   `gapAt_of_near_coarse`, `gapAt_iff_near_coarse`). No invariance, no orthogonality, no split. If
   `T^k` contracts the coarse vectors orthogonal to the vacuum by `ρc` and every vacuum-orthogonal `x`
   has a coarse approximant `c` with `κ ‖x − c‖² ≤ E_k(x)`, the transfer is gapped, with an explicit
   rate. The condition says: a vector that has decayed little over `k` steps is close to what the
   coarse view sees. It is necessary as well (`c = 0`).
2. **Three numbers at one time** (`iter_contract_of_leak`, `gapAt_of_leak`). With an orthogonal split
   `x = c + d` (no invariance): the coarse contraction `ρc` of `T^k`, the residual contraction `ρr`,
   and the leakage `η`, `⟨T^k c, T^k d⟩² ≤ η² ‖c‖² ‖d‖²` (the correlation of a coarse and a residual
   vector at lag `2k`). If `η² < (1 − ρc²)(1 − ρr²)` the transfer is gapped. Invariance is `η = 0`
   (`gapAt_of_split`). `split_rates_do_not_suffice`: a positive transfer on `ℝ³` with coarse and
   residual contracted at rate `1/2` (squared), leakage exactly `1/2`, and no gap; the criterion is
   sharp there.
3. **The residual contraction from local correlations** (`schur_bound`, `frame_of_gram`,
   `residual_contract_of_local`). On the span of a family `dᵢ` (local residual observables, one per
   block): if the lag-`2k` correlations `|⟨T^k dᵢ, T^k dⱼ⟩|` have row sums at most `s`, and the
   equal-time Gram matrix has diagonal at least `g` and off-diagonal row sums at most `δ < g`, then
   `T^k` contracts the span by `s / (g − δ)` (squared). Both inputs are finite sums of two-point
   functions of local observables.
-/

namespace MassGap.ObserverResidual

open MassGap

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-! ## 0. The decay form -/

/-- Every power of `T` contracts the form on every vector.

DERIVED: no numeral beyond the base case `0` of the induction. -/
theorem form_pow_le (D : Transfer.TransferData A) (k : ℕ) (y : A) :
    D.form ((D.T ^ k) y) ((D.T ^ k) y) ≤ D.form y y := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply]
    exact (ih (D.T y)).trans (D.T_contract y)

#print axioms form_pow_le

/-- The expansion of a difference.

DERIVED: `2` is the cross-term count; `-1` the scalar of the negation. -/
theorem form_sub_self (D : Transfer.TransferData A) (x y : A) :
    D.form (x - y) (x - y) = D.form x x - 2 * D.form x y + D.form y y := by
  have hn : x - y = x + (-1 : ℝ) • y := by rw [neg_one_smul, sub_eq_add_neg]
  rw [hn, D.toPreForm.form_add_self]
  simp only [D.toPreForm.form_smul_right, D.form_smul_left]
  ring

#print axioms form_sub_self

/-- The expansion of `c + 2d`.

DERIVED: `2` is the scalar on `d` and the cross-term count; `4 = 2·2` its square and the doubled cross
term. -/
theorem form_add_two (D : Transfer.TransferData A) (x y : A) :
    D.form (x + (2 : ℝ) • y) (x + (2 : ℝ) • y)
      = D.form x x + 4 * D.form x y + 4 * D.form y y := by
  rw [D.toPreForm.form_add_self]
  simp only [D.toPreForm.form_smul_right, D.form_smul_left]
  ring

#print axioms form_add_two

/-- **A contraction of `T^k` by `1 − λ` on the vacuum's complement is a gap.** For `k ≥ 1` and
`0 < λ < 1`, some `0 < ρ < 1` has `GapAt D ρ` (`ObserverGapSplit.gapAt_of_iterate` at `√(1 − λ)`).

DERIVED: `0` and `1` bracket `λ`, `ρ` and `k`; `2` is the form's degree. -/
theorem gap_of_iter_contract (D : Transfer.TransferData A) {k : ℕ} (hk : 0 < k) {lam : ℝ}
    (hl0 : 0 < lam) (hl1 : lam < 1)
    (h : ∀ x, D.form x D.vac = 0 →
      D.form ((D.T ^ k) x) ((D.T ^ k) x) ≤ (1 - lam) * D.form x x) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ TransferGap.GapAt D ρ := by
  set ρ0 := Real.sqrt (1 - lam) with hρ0def
  have hpos : 0 < 1 - lam := by linarith
  have hρ0 : 0 < ρ0 := Real.sqrt_pos.mpr hpos
  have hρ0sq : ρ0 ^ 2 = 1 - lam := Real.sq_sqrt hpos.le
  have hρ1 : ρ0 < 1 := by
    rw [hρ0def, Real.sqrt_lt' one_pos]
    linarith
  have hk' : (0 : ℝ) < 1 / (k : ℝ) := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  refine ⟨ρ0 ^ (1 / (k : ℝ)), Real.rpow_pos_of_pos hρ0 _, Real.rpow_lt_one hρ0.le hρ1 hk',
    ObserverGapSplit.gapAt_of_iterate D hk hρ0 hρ1.le ?_⟩
  intro x hx
  rw [hρ0sq]
  exact h x hx

#print axioms gap_of_iter_contract

/-! ## 1. Slow vectors are near the coarse span -/

/-- **The gap from the coarse gap and nearness of slow vectors, with no invariance.** `C` is any set
of coarse vectors. If `T^k` contracts its vacuum-orthogonal members by `ρc` (`ρc² < 1`), and every
vacuum-orthogonal `x` has a vacuum-orthogonal `c ∈ C` with `κ ‖x − c‖² ≤ E_k(x)` (`κ > 0`), then
`T^k` contracts the vacuum's complement by `1 − λ`, `λ = (1 − ρc²) κ / (2(2κ + 2 + 1 − ρc²))`.

With `d = x − c`: `E_k` is a non-negative quadratic form, so `E_k(c) ≤ 2E_k(x) + 2E_k(d)` (the
remainder is `E_k(c + 2d) ≥ 0`), `E_k(d) ≤ ‖d‖²`, `(1 − ρc²)‖c‖² ≤ E_k(c)` and `‖x‖² ≤ 2‖c‖² + 2‖d‖²`.

DERIVED: `0` is orthogonality to the vacuum; `1` the contraction bound; `2` is the form's degree and
the parallelogram constant (`‖x‖² ≤ 2‖c‖² + 2‖d‖²`, `E_k(c) ≤ 2E_k(x) + 2E_k(d)`); `2κ + 2` collects
`2κ E_k(x)` and `2κ‖d‖² ≤ 2E_k(x)`; `4` is `2²` in `E_k(c + 2d)`. -/
theorem iter_contract_of_near_coarse (D : Transfer.TransferData A) (C : Set A) (k : ℕ)
    {ρc κ : ℝ} (hρc : ρc ^ 2 < 1) (hκ : 0 < κ)
    (hcoarse : ∀ c ∈ C, D.form c D.vac = 0 →
      D.form ((D.T ^ k) c) ((D.T ^ k) c) ≤ ρc ^ 2 * D.form c c)
    (hnear : ∀ x, D.form x D.vac = 0 → ∃ c ∈ C, D.form c D.vac = 0 ∧
      κ * D.form (x - c) (x - c) ≤ D.form x x - D.form ((D.T ^ k) x) ((D.T ^ k) x)) :
    ∀ x, D.form x D.vac = 0 → D.form ((D.T ^ k) x) ((D.T ^ k) x)
      ≤ (1 - (1 - ρc ^ 2) * κ / (2 * (2 * κ + 2 + (1 - ρc ^ 2)))) * D.form x x := by
  intro x hx
  obtain ⟨c, hcC, hcv, hnr⟩ := hnear x hx
  obtain ⟨d, hd⟩ : ∃ d, d = x - c := ⟨_, rfl⟩
  rw [← hd] at hnr
  have hxcd : x = c + d := by rw [hd]; abel
  have hxx : D.form x x = D.form c c + 2 * D.form c d + D.form d d := by
    rw [hxcd, D.toPreForm.form_add_self]
  have hTx : D.form ((D.T ^ k) x) ((D.T ^ k) x)
      = D.form ((D.T ^ k) c) ((D.T ^ k) c) + 2 * D.form ((D.T ^ k) c) ((D.T ^ k) d)
        + D.form ((D.T ^ k) d) ((D.T ^ k) d) := by
    rw [hxcd, map_add, D.toPreForm.form_add_self]
  have hpar := form_pow_le D k (c + (2 : ℝ) • d)
  rw [map_add, map_smul, form_add_two, form_add_two] at hpar
  have hcmd := D.form_nonneg (c - d)
  rw [form_sub_self] at hcmd
  have hco := hcoarse c hcC hcv
  have hA := D.form_nonneg c
  have hB := D.form_nonneg d
  have hQ := D.form_nonneg ((D.T ^ k) d)
  rw [hTx, hxx] at hnr ⊢
  set Ac := D.form c c
  set B := D.form d d
  set X := D.form c d
  set P := D.form ((D.T ^ k) c) ((D.T ^ k) c)
  set R := D.form ((D.T ^ k) c) ((D.T ^ k) d)
  set Q := D.form ((D.T ^ k) d) ((D.T ^ k) d)
  set E := Ac + 2 * X + B - (P + 2 * R + Q) with hE
  set α := 1 - ρc ^ 2 with hα
  have hα0 : 0 < α := by rw [hα]; linarith
  have hEc : Ac - P ≤ 2 * E + 2 * B := by rw [hE]; linarith
  have hcoA : α * Ac ≤ Ac - P := by rw [hα]; linarith
  have h1 : κ * (α * Ac) ≤ κ * (2 * E + 2 * B) :=
    mul_le_mul_of_nonneg_left (hcoA.trans hEc) hκ.le
  have h2 : α * (κ * B) ≤ α * E := mul_le_mul_of_nonneg_left hnr hα0.le
  have h3 : α * κ * (Ac + 2 * X + B) ≤ α * κ * (2 * Ac + 2 * B) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_pos hα0 hκ).le
  have hkey : α * κ * (Ac + 2 * X + B) ≤ 2 * (2 * κ + 2 + α) * E := by nlinarith
  have hden : 0 < 2 * (2 * κ + 2 + α) := by positivity
  have hlam : α * κ / (2 * (2 * κ + 2 + α)) * (Ac + 2 * X + B) ≤ E := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    linarith
  have : (1 - α * κ / (2 * (2 * κ + 2 + α))) * (Ac + 2 * X + B)
      = (Ac + 2 * X + B) - α * κ / (2 * (2 * κ + 2 + α)) * (Ac + 2 * X + B) := by ring
  rw [this]
  linarith

#print axioms iter_contract_of_near_coarse

/-- **The gap from the coarse gap and nearness of slow vectors.** Under the hypotheses of
`iter_contract_of_near_coarse` with `k ≥ 1`, the transfer is `GapAt ρ` for some `0 < ρ < 1`.

DERIVED: `0` and `1` bracket the rates and `k`; `2` is the form's degree and, with `2κ + 2`, the
constants of `iter_contract_of_near_coarse`. -/
theorem gapAt_of_near_coarse (D : Transfer.TransferData A) (C : Set A) {k : ℕ} (hk : 0 < k)
    {ρc κ : ℝ} (hρc : ρc ^ 2 < 1) (hκ : 0 < κ)
    (hcoarse : ∀ c ∈ C, D.form c D.vac = 0 →
      D.form ((D.T ^ k) c) ((D.T ^ k) c) ≤ ρc ^ 2 * D.form c c)
    (hnear : ∀ x, D.form x D.vac = 0 → ∃ c ∈ C, D.form c D.vac = 0 ∧
      κ * D.form (x - c) (x - c) ≤ D.form x x - D.form ((D.T ^ k) x) ((D.T ^ k) x)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ TransferGap.GapAt D ρ := by
  have hα0 : 0 < 1 - ρc ^ 2 := by linarith
  have hα1 : 1 - ρc ^ 2 ≤ 1 := by nlinarith [sq_nonneg ρc]
  have hden : 0 < 2 * (2 * κ + 2 + (1 - ρc ^ 2)) := by positivity
  refine gap_of_iter_contract D hk (div_pos (mul_pos hα0 hκ) hden) ?_
    (iter_contract_of_near_coarse D C k hρc hκ hcoarse hnear)
  rw [div_lt_one hden]
  nlinarith

#print axioms gapAt_of_near_coarse

/-- **The gap is exactly: a gapped coarse view plus nearness of slow vectors.** For any submodule `C`
(no invariance asked): `GapAt D ρ` for some `0 < ρ < 1` if and only if, at some `k ≥ 1`, `T^k`
contracts the vacuum-orthogonal part of `C` by some `ρc² < 1` and every vacuum-orthogonal `x` lies
within `‖x − c‖² ≤ E_k(x)/κ` of a vacuum-orthogonal `c ∈ C`, for some `κ > 0`. The forward direction
takes `k = 1`, `c = 0`, `κ = 1 − ρ²`: the content is in the backward direction, where the coarse gap
does the work and the residual is only asked to be paid by the decay.

DERIVED: `0` and `1` bracket the rates, `k` and `κ`; `2` is the form's degree. -/
theorem gapAt_iff_near_coarse (D : Transfer.TransferData A) (C : Submodule ℝ A) :
    (∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ TransferGap.GapAt D ρ) ↔
      ∃ k : ℕ, 0 < k ∧ ∃ ρc κ : ℝ, ρc ^ 2 < 1 ∧ 0 < κ
        ∧ (∀ c ∈ C, D.form c D.vac = 0 →
            D.form ((D.T ^ k) c) ((D.T ^ k) c) ≤ ρc ^ 2 * D.form c c)
        ∧ (∀ x, D.form x D.vac = 0 → ∃ c ∈ C, D.form c D.vac = 0 ∧
            κ * D.form (x - c) (x - c) ≤ D.form x x - D.form ((D.T ^ k) x) ((D.T ^ k) x)) := by
  constructor
  · rintro ⟨ρ, hρ0, hρ1, hg⟩
    have hρ2 : ρ ^ 2 < 1 := by nlinarith
    refine ⟨1, one_pos, ρ, 1 - ρ ^ 2, hρ2, by linarith, ?_, ?_⟩
    · intro c _ hcv
      rw [pow_one]
      exact hg c hcv
    · intro x hx
      refine ⟨0, C.zero_mem, D.toPreForm.form_zero_left _, ?_⟩
      rw [sub_zero, pow_one]
      have := hg x hx
      linarith
  · rintro ⟨k, hk, ρc, κ, hρc, hκ, hcoarse, hnear⟩
    exact gapAt_of_near_coarse D (C : Set A) hk hρc hκ hcoarse hnear

#print axioms gapAt_iff_near_coarse

/-! ## 2. Three numbers at one time: coarse rate, residual rate, leakage -/

/-- The real-number core: a coarse contraction, a residual contraction and a bounded cross term give a
contraction of the sum when the leakage is below the geometric mean of the two decays.

DERIVED: `0` the lower bound of the norms; `1` the contraction bound; `2` the cross-term count; `4`
is `2²` in the discriminant `(pA + qB)² − 4pqAB = (pA − qB)²`. -/
theorem quad_core {P Q R Ac B αc αr η lam : ℝ} (hA : 0 ≤ Ac) (hB : 0 ≤ B)
    (hP : P ≤ (1 - αc) * Ac) (hQ : Q ≤ (1 - αr) * B) (hR : R ^ 2 ≤ η ^ 2 * (Ac * B))
    (hc : lam ≤ αc) (hr : lam ≤ αr) (hdet : η ^ 2 ≤ (αc - lam) * (αr - lam)) :
    P + 2 * R + Q ≤ (1 - lam) * (Ac + B) := by
  have hp : 0 ≤ αc - lam := by linarith
  have hq : 0 ≤ αr - lam := by linarith
  have hS : 0 ≤ (αc - lam) * Ac + (αr - lam) * B := by positivity
  have hAB : 0 ≤ Ac * B := mul_nonneg hA hB
  have hsq : (2 * R) ^ 2 ≤ ((αc - lam) * Ac + (αr - lam) * B) ^ 2 := by
    nlinarith [sq_nonneg ((αc - lam) * Ac - (αr - lam) * B), mul_le_mul_of_nonneg_right hdet hAB]
  have h2R := le_of_sq_le_sq hsq hS
  nlinarith

#print axioms quad_core

/-- **The gap of `T^k` from three numbers, with no invariance.** `C` holds the vacuum and every vector
splits as `c + d`, `c ∈ C`, `d` orthogonal to `C`. If `T^k` contracts `C ∩ Ω^⊥` by `ρc`, contracts
`C^⊥` by `ρr`, and the leakage `⟨T^k c, T^k d⟩ = ⟨c, T^{2k} d⟩` (a coarse–residual correlation at lag
`2k`) is at most `η ‖c‖ ‖d‖`, then for every `λ ≤ 1 − ρc²`, `λ ≤ 1 − ρr²` with
`η² ≤ (1 − ρc² − λ)(1 − ρr² − λ)`, `T^k` contracts the vacuum's complement by `1 − λ`. At `η = 0` and
`k = 1` this is `ObserverGapSplit.gapAt_of_split`, whose invariance gives `η = 0`.

DERIVED: `0` is orthogonality; `1` the contraction bound; `2` is the form's degree and the cross-term
count. -/
theorem iter_contract_of_leak (D : Transfer.TransferData A) (C : Submodule ℝ A)
    (hvac : D.vac ∈ C)
    (hsplit : ∀ x : A, ∃ c ∈ C, ∃ d : A, (∀ z ∈ C, D.form z d = 0) ∧ x = c + d)
    (k : ℕ) {ρc ρr η lam : ℝ}
    (hcoarse : ∀ c ∈ C, D.form c D.vac = 0 →
      D.form ((D.T ^ k) c) ((D.T ^ k) c) ≤ ρc ^ 2 * D.form c c)
    (hres : ∀ d : A, (∀ z ∈ C, D.form z d = 0) →
      D.form ((D.T ^ k) d) ((D.T ^ k) d) ≤ ρr ^ 2 * D.form d d)
    (hleak : ∀ c ∈ C, D.form c D.vac = 0 → ∀ d : A, (∀ z ∈ C, D.form z d = 0) →
      D.form ((D.T ^ k) c) ((D.T ^ k) d) ^ 2 ≤ η ^ 2 * (D.form c c * D.form d d))
    (hc : lam ≤ 1 - ρc ^ 2) (hr : lam ≤ 1 - ρr ^ 2)
    (hdet : η ^ 2 ≤ (1 - ρc ^ 2 - lam) * (1 - ρr ^ 2 - lam)) :
    ∀ x, D.form x D.vac = 0 →
      D.form ((D.T ^ k) x) ((D.T ^ k) x) ≤ (1 - lam) * D.form x x := by
  intro x hx
  obtain ⟨c, hcC, d, hd, rfl⟩ := hsplit x
  have hdv : D.form d D.vac = 0 := by rw [D.form_symm]; exact hd _ hvac
  have hcv : D.form c D.vac = 0 := by
    have := hx
    rw [D.form_add_left, hdv, add_zero] at this
    exact this
  have hcd : D.form c d = 0 := hd c hcC
  have hxx : D.form (c + d) (c + d) = D.form c c + D.form d d := by
    rw [D.toPreForm.form_add_self, hcd]; ring
  have hTx : D.form ((D.T ^ k) (c + d)) ((D.T ^ k) (c + d))
      = D.form ((D.T ^ k) c) ((D.T ^ k) c) + 2 * D.form ((D.T ^ k) c) ((D.T ^ k) d)
        + D.form ((D.T ^ k) d) ((D.T ^ k) d) := by
    rw [map_add, D.toPreForm.form_add_self]
  rw [hTx, hxx]
  refine quad_core (D.form_nonneg c) (D.form_nonneg d) ?_ ?_ (hleak c hcC hcv d hd) hc hr ?_
  · have := hcoarse c hcC hcv; linarith
  · have := hres d hd; linarith
  · have e1 : 1 - (1 - ρc ^ 2) = ρc ^ 2 := by ring
    linarith

#print axioms iter_contract_of_leak

/-- **The gap from three numbers.** Under the split of `iter_contract_of_leak`, with `k ≥ 1`,
`ρc² < 1`, `ρr² < 1` and `η² < (1 − ρc²)(1 − ρr²)`, the transfer is `GapAt ρ` for some `0 < ρ < 1`.
The contraction of `T^k` is `1 − λ` with
`λ = ((1 − ρc²)(1 − ρr²) − η²)/((1 − ρc²) + (1 − ρr²))`.

DERIVED: `0` and `1` bracket the rates and `k`; `2` is the form's degree. -/
theorem gapAt_of_leak (D : Transfer.TransferData A) (C : Submodule ℝ A) (hvac : D.vac ∈ C)
    (hsplit : ∀ x : A, ∃ c ∈ C, ∃ d : A, (∀ z ∈ C, D.form z d = 0) ∧ x = c + d)
    {k : ℕ} (hk : 0 < k) {ρc ρr η : ℝ} (hρc : ρc ^ 2 < 1) (hρr : ρr ^ 2 < 1)
    (hη : η ^ 2 < (1 - ρc ^ 2) * (1 - ρr ^ 2))
    (hcoarse : ∀ c ∈ C, D.form c D.vac = 0 →
      D.form ((D.T ^ k) c) ((D.T ^ k) c) ≤ ρc ^ 2 * D.form c c)
    (hres : ∀ d : A, (∀ z ∈ C, D.form z d = 0) →
      D.form ((D.T ^ k) d) ((D.T ^ k) d) ≤ ρr ^ 2 * D.form d d)
    (hleak : ∀ c ∈ C, D.form c D.vac = 0 → ∀ d : A, (∀ z ∈ C, D.form z d = 0) →
      D.form ((D.T ^ k) c) ((D.T ^ k) d) ^ 2 ≤ η ^ 2 * (D.form c c * D.form d d)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ TransferGap.GapAt D ρ := by
  set αc := 1 - ρc ^ 2 with hαc
  set αr := 1 - ρr ^ 2 with hαr
  have hc0 : 0 < αc := by rw [hαc]; linarith
  have hr0 : 0 < αr := by rw [hαr]; linarith
  have hc1 : αc ≤ 1 := by rw [hαc]; nlinarith [sq_nonneg ρc]
  have hr1 : αr ≤ 1 := by rw [hαr]; nlinarith [sq_nonneg ρr]
  have hsum : 0 < αc + αr := by linarith
  set lam := (αc * αr - η ^ 2) / (αc + αr) with hlamdef
  have hl : lam * (αc + αr) = αc * αr - η ^ 2 := div_mul_cancel₀ _ hsum.ne'
  have hη0 := sq_nonneg η
  have hlc : lam ≤ αc := by nlinarith
  have hlr : lam ≤ αr := by nlinarith
  have hl0 : 0 < lam := by
    rw [hlamdef]; exact div_pos (by linarith) hsum
  have hl1 : lam < 1 := by nlinarith
  have hdet : η ^ 2 ≤ (αc - lam) * (αr - lam) := by nlinarith [sq_nonneg lam]
  exact gap_of_iter_contract D hk hl0 hl1
    (iter_contract_of_leak D C hvac hsplit k hcoarse hres hleak hlc hlr hdet)

#print axioms gapAt_of_leak

/-- The mixing step on `ℝ³`: coordinate `0` fixed (the vacuum), coordinates `1` and `2` both replaced
by their mean (the orthogonal projection onto `e₁ + e₂`).

DERIVED: `3` is the least dimension holding a vacuum, a coarse and a residual direction; `0`, `1`, `2`
index them; `2` in the mean is the number of coordinates averaged. -/
noncomputable def mixStep : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x := fun i => if i = 0 then x 0 else (x 1 + x 2) / 2
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- The transfer of the mixing step: the standard inner product and the vacuum at coordinate `0`.

DERIVED: `3`, `0`, `1`, `2` as in `mixStep`; `1` the vacuum's norm. -/
noncomputable def mixTransfer : Transfer.TransferData (Fin 3 → ℝ) where
  form x y := x 0 * y 0 + x 1 * y 1 + x 2 * y 2
  form_symm x y := by ring
  form_add_left x y z := by simp only [Pi.add_apply]; ring
  form_smul_left r x y := by simp only [Pi.smul_apply, smul_eq_mul]; ring
  form_nonneg x := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  T := mixStep
  vac := fun i => if i = 0 then 1 else 0
  T_symm x y := by simp [mixStep]; ring
  T_contract x := by
    simp [mixStep]
    nlinarith [sq_nonneg (x 1 - x 2)]
  T_vac := by
    funext i
    fin_cases i <;> simp [mixStep]
  vac_norm := by simp

/-- DERIVED: `0`, `1`, `2` index the coordinates; `3` the dimension, as in `mixStep`. -/
theorem mix_form (x y : Fin 3 → ℝ) :
    mixTransfer.form x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := rfl

/-- DERIVED: `0`, `1`, `2` index the coordinates; `2` in the mean is the number averaged; `3` the dimension,
as in `mixStep`. -/
theorem mix_T (x : Fin 3 → ℝ) :
    mixTransfer.T x = fun i => if i = 0 then x 0 else (x 1 + x 2) / 2 := rfl

/-- DERIVED: `0` the vacuum's coordinate, `1` its value. -/
theorem mix_vac : mixTransfer.vac = fun i => if i = 0 then (1 : ℝ) else 0 := rfl

/-- **Coarse and residual contracted, no gap: the leakage is needed.** For the mixing transfer on
`ℝ³` with the coarse span `ObserverGapSplit.triCoarse` (the vectors with no coordinate `2`): the
transfer is positive, the coarse span holds the vacuum, every vector splits as coarse plus orthogonal
residual, `T` contracts the coarse vacuum complement and the residual each by `1/2` (squared), the
leakage is `η = 1/2`, and `GapAt D ρ` fails at every `ρ² < 1`: `e₁ + e₂` is invariant and orthogonal to
the vacuum. Here `η² = (1 − 1/2)(1 − 1/2)`, so the strict criterion of `gapAt_of_leak` fails by
equality: it is sharp on this example. The coarse span is not invariant (`T e₁ = (e₁ + e₂)/2`).

DERIVED: `3` the dimension; `1/2` the contraction of `e₁` and of `e₂` (each is half on the invariant
line) and the leakage `⟨T e₁, T e₂⟩ = 1/2`; `0`, `1`, `2` index the coordinates; `2` in the squares is
the form's degree. -/
theorem split_rates_do_not_suffice :
    ∃ (D : Transfer.TransferData (Fin 3 → ℝ)) (C : Submodule ℝ (Fin 3 → ℝ)),
      GNSHilbert.PositiveTransfer D ∧ D.vac ∈ C
        ∧ (∀ x, ∃ c ∈ C, ∃ d, (∀ z ∈ C, D.form z d = 0) ∧ x = c + d)
        ∧ (∀ c ∈ C, D.form c D.vac = 0 → D.form (D.T c) (D.T c) ≤ 1 / 2 * D.form c c)
        ∧ (∀ d, (∀ z ∈ C, D.form z d = 0) → D.form (D.T d) (D.T d) ≤ 1 / 2 * D.form d d)
        ∧ (∀ c ∈ C, D.form c D.vac = 0 → ∀ d, (∀ z ∈ C, D.form z d = 0) →
            D.form (D.T c) (D.T d) ^ 2 ≤ (1 / 2) ^ 2 * (D.form c c * D.form d d))
        ∧ ∀ ρ : ℝ, ρ ^ 2 < 1 → ¬ TransferGap.GapAt D ρ := by
  -- the residual is the third axis
  have hres_ax : ∀ d : Fin 3 → ℝ, (∀ z ∈ ObserverGapSplit.triCoarse, mixTransfer.form z d = 0) →
      d 0 = 0 ∧ d 1 = 0 := by
    intro d hd
    have h0 := hd (fun i => if i = 0 then 1 else 0) (by
      show (if (2 : Fin 3) = 0 then (1 : ℝ) else 0) = 0
      simp)
    have h1 := hd (fun i => if i = 1 then 1 else 0) (by
      show (if (2 : Fin 3) = 1 then (1 : ℝ) else 0) = 0
      simp)
    rw [mix_form] at h0 h1
    simp at h0 h1
    exact ⟨h0, h1⟩
  have hco_ax : ∀ c ∈ ObserverGapSplit.triCoarse, mixTransfer.form c mixTransfer.vac = 0 →
      c 0 = 0 ∧ c 2 = 0 := by
    intro c hc hcv
    have hc2 : c 2 = 0 := hc
    rw [mix_form, mix_vac] at hcv
    simp at hcv
    exact ⟨hcv, hc2⟩
  refine ⟨mixTransfer, ObserverGapSplit.triCoarse, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    show 0 ≤ mixTransfer.form x (mixTransfer.T x)
    rw [mix_form, mix_T]
    simp
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1 + x 2)]
  · show (mixTransfer.vac 2) = 0
    rw [mix_vac]
    simp
  · intro x
    refine ⟨fun i => if i = 2 then 0 else x i, by
      show (if (2 : Fin 3) = 2 then (0 : ℝ) else x 2) = 0; simp,
      fun i => if i = 2 then x 2 else 0, fun z hz => ?_, ?_⟩
    · have hz2 : z 2 = 0 := hz
      rw [mix_form]
      simp [hz2]
    · funext i
      fin_cases i <;> simp
  · intro c hc hcv
    obtain ⟨hc0, hc2⟩ := hco_ax c hc hcv
    rw [mix_form, mix_form, mix_T]
    simp [hc0, hc2]
    nlinarith [sq_nonneg (c 1)]
  · intro d hd
    obtain ⟨hd0, hd1⟩ := hres_ax d hd
    rw [mix_form, mix_form, mix_T]
    simp [hd0, hd1]
    nlinarith [sq_nonneg (d 2)]
  · intro c hc hcv d hd
    obtain ⟨hc0, hc2⟩ := hco_ax c hc hcv
    obtain ⟨hd0, hd1⟩ := hres_ax d hd
    rw [mix_form, mix_form, mix_form, mix_T, mix_T]
    simp [hc0, hc2, hd0, hd1]
    nlinarith [sq_nonneg (c 1 * d 2)]
  · intro ρ hρ hg
    have hx : mixTransfer.form (fun i => if i = 0 then (0 : ℝ) else 1) mixTransfer.vac = 0 := by
      rw [mix_form, mix_vac]; simp
    have h := hg _ hx
    rw [mix_form, mix_form, mix_T] at h
    simp at h
    nlinarith [sq_abs ρ, abs_nonneg ρ]

#print axioms split_rates_do_not_suffice

/-! ## 3. The residual contraction from local correlations -/

/-- The form of a finite combination in the left slot.

DERIVED: no numeral beyond the empty sum's `0`. -/
theorem form_sum_left (D : Transfer.TransferData A) {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    (x : ι → A) (y : A) :
    D.form (∑ i ∈ S, a i • x i) y = ∑ i ∈ S, a i * D.form (x i) y := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp only [Finset.sum_empty]
    exact D.toPreForm.form_zero_left y
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, D.form_add_left, D.form_smul_left, ih]

#print axioms form_sum_left

/-- The form of two finite combinations.

DERIVED: no numeral. -/
theorem form_sum_sum (D : Transfer.TransferData A) {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    (u v : ι → A) :
    D.form (∑ i ∈ S, a i • u i) (∑ j ∈ S, a j • v j)
      = ∑ i ∈ S, ∑ j ∈ S, a i * a j * D.form (u i) (v j) := by
  rw [form_sum_left]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [D.form_symm, form_sum_left, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [D.form_symm]
  ring

#print axioms form_sum_sum

/-- **The Schur bound.** A matrix `M` dominated entrywise by a symmetric kernel `K` with row sums at
most `s` has quadratic form at most `s ∑ aᵢ²` in absolute value. `|aᵢ aⱼ| ≤ (aᵢ² + aⱼ²)/2` and the
two halves are the row and column sums.

DERIVED: `2` is the square and the halving of `|aᵢ aⱼ| ≤ (aᵢ² + aⱼ²)/2`. -/
theorem schur_bound {ι : Type*} (S : Finset ι) (a : ι → ℝ) (M K : ι → ι → ℝ) {s : ℝ}
    (hMK : ∀ i ∈ S, ∀ j ∈ S, |M i j| ≤ K i j)
    (hsym : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i)
    (hrow : ∀ i ∈ S, ∑ j ∈ S, K i j ≤ s) :
    |∑ i ∈ S, ∑ j ∈ S, a i * a j * M i j| ≤ s * ∑ i ∈ S, a i ^ 2 := by
  have hpt : ∀ i ∈ S, ∀ j ∈ S,
      |a i * a j * M i j| ≤ a i ^ 2 / 2 * K i j + a j ^ 2 / 2 * K i j := by
    intro i hi j hj
    have hK := hMK i hi j hj
    have hK0 : 0 ≤ K i j := (abs_nonneg _).trans hK
    rw [abs_mul, abs_mul]
    have h1 : |a i| * |a j| * |M i j| ≤ |a i| * |a j| * K i j :=
      mul_le_mul_of_nonneg_left hK (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    nlinarith [mul_nonneg (sq_nonneg (|a i| - |a j|)) hK0, sq_abs (a i), sq_abs (a j)]
  have hrowA : ∑ i ∈ S, ∑ j ∈ S, a i ^ 2 / 2 * K i j ≤ s / 2 * ∑ i ∈ S, a i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    rw [← Finset.mul_sum]
    have := hrow i hi
    have h2 : 0 ≤ a i ^ 2 / 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h2]
  have hcolA : ∑ i ∈ S, ∑ j ∈ S, a j ^ 2 / 2 * K i j ≤ s / 2 * ∑ i ∈ S, a i ^ 2 := by
    rw [Finset.sum_comm]
    have : ∑ j ∈ S, ∑ i ∈ S, a j ^ 2 / 2 * K i j = ∑ j ∈ S, ∑ i ∈ S, a j ^ 2 / 2 * K j i := by
      refine Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun i hi => ?_))
      rw [hsym i hi j hj]
    rw [this]
    exact hrowA
  calc |∑ i ∈ S, ∑ j ∈ S, a i * a j * M i j|
      ≤ ∑ i ∈ S, |∑ j ∈ S, a i * a j * M i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, |a i * a j * M i j| :=
        Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, (a i ^ 2 / 2 * K i j + a j ^ 2 / 2 * K i j) :=
        Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hpt i hi j hj))
    _ = ∑ i ∈ S, ∑ j ∈ S, a i ^ 2 / 2 * K i j + ∑ i ∈ S, ∑ j ∈ S, a j ^ 2 / 2 * K i j := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib)
    _ ≤ s * ∑ i ∈ S, a i ^ 2 := by linarith

#print axioms schur_bound

/-- **The frame bound from the equal-time Gram matrix.** If the local vectors `dᵢ` have
`⟨dᵢ, dᵢ⟩ ≥ g` and off-diagonal row sums `∑_{j ≠ i} |⟨dᵢ, dⱼ⟩| ≤ δ`, then
`(g − δ) ∑ aᵢ² ≤ ‖∑ aᵢ dᵢ‖²`.

DERIVED: `0` is the off-diagonal entry removed at `j = i`; `2` the square of the coefficients. -/
theorem frame_of_gram (D : Transfer.TransferData A) {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (a : ι → ℝ) (d : ι → A) {g δ : ℝ}
    (hdiag : ∀ i ∈ S, g ≤ D.form (d i) (d i))
    (hoff : ∀ i ∈ S, ∑ j ∈ S.erase i, |D.form (d i) (d j)| ≤ δ) :
    (g - δ) * ∑ i ∈ S, a i ^ 2 ≤ D.form (∑ i ∈ S, a i • d i) (∑ i ∈ S, a i • d i) := by
  set M : ι → ι → ℝ := fun i j => if j = i then 0 else D.form (d i) (d j) with hM
  have hsplitG : ∀ i ∈ S, ∑ j ∈ S, a i * a j * D.form (d i) (d j)
      = a i ^ 2 * D.form (d i) (d i) + ∑ j ∈ S, a i * a j * M i j := by
    intro i hi
    have hterm : ∀ j ∈ S, a i * a j * D.form (d i) (d j)
        = (if j = i then a i * a i * D.form (d i) (d i) else 0) + a i * a j * M i j := by
      intro j _
      by_cases hji : j = i
      · subst hji; simp [hM]
      · simp [hM, hji]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq' S i, if_pos hi]
    ring
  have hrowK : ∀ i ∈ S, ∑ j ∈ S, |M i j| ≤ δ := by
    intro i hi
    have hz : |M i i| = 0 := by simp [hM]
    rw [← Finset.sum_erase S hz]
    have : ∑ j ∈ S.erase i, |M i j| = ∑ j ∈ S.erase i, |D.form (d i) (d j)| := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      simp [hM, hji]
    rw [this]
    exact hoff i hi
  have hsymK : ∀ i ∈ S, ∀ j ∈ S, |M i j| = |M j i| := by
    intro i _ j _
    by_cases hji : j = i
    · subst hji; rfl
    · have hij : i ≠ j := fun h => hji h.symm
      simp [hM, hji, hij, D.form_symm (d i) (d j)]
  have hsch := schur_bound S a M (fun i j => |M i j|) (fun i _ j _ => le_rfl) hsymK hrowK
  have hdiagsum : g * ∑ i ∈ S, a i ^ 2 ≤ ∑ i ∈ S, a i ^ 2 * D.form (d i) (d i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => by
      have := hdiag i hi
      nlinarith [sq_nonneg (a i)])
  rw [form_sum_sum, Finset.sum_congr rfl hsplitG, Finset.sum_add_distrib]
  have := neg_abs_le (∑ i ∈ S, ∑ j ∈ S, a i * a j * M i j)
  linarith

#print axioms frame_of_gram

/-- **The residual contraction from local correlations.** On the span of a finite family of local
vectors `dᵢ` (one residual observable per block): if the correlations at lag `2k`,
`|⟨T^k dᵢ, T^k dⱼ⟩| = |⟨dᵢ, T^{2k} dⱼ⟩|`, are bounded by a symmetric kernel with row sums at most
`s ≥ 0`, and the equal-time Gram matrix has diagonal at least `g` and off-diagonal row sums at most
`δ < g`, then `‖T^k y‖² ≤ s/(g − δ) ‖y‖²` for every `y = ∑ aᵢ dᵢ`. Both inputs are finite sums of
two-point functions of local observables; `s < g − δ` is a residual contraction at rate below one,
the `hres` input of `iter_contract_of_leak` on the span.

DERIVED: `0` the lower bound of `s`; `2` is the form's degree and the doubled lag `2k`. -/
theorem residual_contract_of_local (D : Transfer.TransferData A) {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → ℝ) (d : ι → A) (k : ℕ) (K : ι → ι → ℝ) {s g δ : ℝ}
    (hs : 0 ≤ s)
    (hdyn : ∀ i ∈ S, ∀ j ∈ S, |D.form ((D.T ^ k) (d i)) ((D.T ^ k) (d j))| ≤ K i j)
    (hsym : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i)
    (hrow : ∀ i ∈ S, ∑ j ∈ S, K i j ≤ s)
    (hdiag : ∀ i ∈ S, g ≤ D.form (d i) (d i))
    (hoff : ∀ i ∈ S, ∑ j ∈ S.erase i, |D.form (d i) (d j)| ≤ δ) (hgδ : δ < g) :
    D.form ((D.T ^ k) (∑ i ∈ S, a i • d i)) ((D.T ^ k) (∑ i ∈ S, a i • d i))
      ≤ s / (g - δ) * D.form (∑ i ∈ S, a i • d i) (∑ i ∈ S, a i • d i) := by
  have hTy : (D.T ^ k) (∑ i ∈ S, a i • d i) = ∑ i ∈ S, a i • (D.T ^ k) (d i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => map_smul _ _ _)
  rw [hTy, form_sum_sum]
  have hsch := schur_bound S a (fun i j => D.form ((D.T ^ k) (d i)) ((D.T ^ k) (d j))) K
    hdyn hsym hrow
  have hfr := frame_of_gram D S a d hdiag hoff
  have hgd : 0 < g - δ := by linarith
  have h1 := le_abs_self (∑ i ∈ S, ∑ j ∈ S, a i * a j * D.form ((D.T ^ k) (d i)) ((D.T ^ k) (d j)))
  have hsum : ∑ i ∈ S, a i ^ 2 ≤ D.form (∑ i ∈ S, a i • d i) (∑ i ∈ S, a i • d i) / (g - δ) := by
    rw [le_div_iff₀ hgd]; linarith
  calc ∑ i ∈ S, ∑ j ∈ S, a i * a j * D.form ((D.T ^ k) (d i)) ((D.T ^ k) (d j))
      ≤ s * ∑ i ∈ S, a i ^ 2 := h1.trans hsch
    _ ≤ s * (D.form (∑ i ∈ S, a i • d i) (∑ i ∈ S, a i • d i) / (g - δ)) :=
        mul_le_mul_of_nonneg_left hsum hs
    _ = s / (g - δ) * D.form (∑ i ∈ S, a i • d i) (∑ i ∈ S, a i • d i) := by ring

#print axioms residual_contract_of_local

/-! ## 4. For the smeared observer -/

open MassGap.ContinuumFlow MassGap.FlowCapstone MassGap.ObserverFlow MassGap.ObserverClay
  MassGap.ObserverGapScale

/-- **M for the smeared observer from a gapped coarse view and nearness of slow vectors.** For any
set `C` of vectors of the observer's pre-space at step `m₀` (no invariance, no split), a coarse
contraction of `T^k` on `C` and the nearness `κ ‖x − c‖² ≤ E_k(x)` give `FlowClusterAbs`.

DERIVED: `2` is the rank and the form's degree; `0` and `1` bracket the rates, `k`, `κ` and `L`; `1/6`
the dominance bound. -/
theorem observer_M_of_near_coarse {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (τ : Fin 4) {r : ℝ} (hphys : (obsFlowF c hc0 hc n R).PhysRange r) (m0 : ℕ) {L : ℝ}
    (hL : 0 < L) (C : Set (MarginMono 2 τ r →₀ ℝ)) {k : ℕ} (hk : 0 < k) {ρc κ : ℝ}
    (hρc : ρc ^ 2 < 1) (hκ : 0 < κ)
    (hcoarse : ∀ y ∈ C, (obsTransfer hc0 hc n R τ hphys m0).form y
        (obsTransfer hc0 hc n R τ hphys m0).vac = 0 →
      (obsTransfer hc0 hc n R τ hphys m0).form
          (((obsTransfer hc0 hc n R τ hphys m0).T ^ k) y)
          (((obsTransfer hc0 hc n R τ hphys m0).T ^ k) y)
        ≤ ρc ^ 2 * (obsTransfer hc0 hc n R τ hphys m0).form y y)
    (hnear : ∀ x, (obsTransfer hc0 hc n R τ hphys m0).form x
        (obsTransfer hc0 hc n R τ hphys m0).vac = 0 →
      ∃ y ∈ C, (obsTransfer hc0 hc n R τ hphys m0).form y
          (obsTransfer hc0 hc n R τ hphys m0).vac = 0 ∧
        κ * (obsTransfer hc0 hc n R τ hphys m0).form (x - y) (x - y)
          ≤ (obsTransfer hc0 hc n R τ hphys m0).form x x
            - (obsTransfer hc0 hc n R τ hphys m0).form
              (((obsTransfer hc0 hc n R τ hphys m0).T ^ k) x)
              (((obsTransfer hc0 hc n R τ hphys m0).T ^ k) x)) :
    FlowClusterAbs two_ne (obsFlowF c hc0 hc n R) τ r L :=
  (observer_M_iff_gap hc0 hc n R τ hphys m0 hL).mpr
    (gapAt_of_near_coarse _ C hk hρc hκ hcoarse hnear)

#print axioms observer_M_of_near_coarse

/-- **M for the smeared observer from three numbers at one time.** For a submodule `C` of the
observer's pre-space at step `m₀` holding the vacuum, with an orthogonal split (no invariance): the
coarse rate `ρc`, the residual rate `ρr` and the leakage `η` of `T^k`, with
`η² < (1 − ρc²)(1 − ρr²)`, give `FlowClusterAbs`.

DERIVED: `2` is the rank and the form's degree; `0` and `1` bracket the rates, `k` and `L`; `1/6` the
dominance bound. -/
theorem observer_M_of_leak {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (τ : Fin 4) {r : ℝ} (hphys : (obsFlowF c hc0 hc n R).PhysRange r) (m0 : ℕ) {L : ℝ}
    (hL : 0 < L) (C : Submodule ℝ (MarginMono 2 τ r →₀ ℝ))
    (hvac : (obsTransfer hc0 hc n R τ hphys m0).vac ∈ C)
    (hsplit : ∀ x, ∃ y ∈ C, ∃ z, (∀ w ∈ C, (obsTransfer hc0 hc n R τ hphys m0).form w z = 0)
      ∧ x = y + z)
    {k : ℕ} (hk : 0 < k) {ρc ρr η : ℝ} (hρc : ρc ^ 2 < 1) (hρr : ρr ^ 2 < 1)
    (hη : η ^ 2 < (1 - ρc ^ 2) * (1 - ρr ^ 2))
    (hcoarse : ∀ y ∈ C, (obsTransfer hc0 hc n R τ hphys m0).form y
        (obsTransfer hc0 hc n R τ hphys m0).vac = 0 →
      (obsTransfer hc0 hc n R τ hphys m0).form
          (((obsTransfer hc0 hc n R τ hphys m0).T ^ k) y)
          (((obsTransfer hc0 hc n R τ hphys m0).T ^ k) y)
        ≤ ρc ^ 2 * (obsTransfer hc0 hc n R τ hphys m0).form y y)
    (hres : ∀ z, (∀ w ∈ C, (obsTransfer hc0 hc n R τ hphys m0).form w z = 0) →
      (obsTransfer hc0 hc n R τ hphys m0).form
          (((obsTransfer hc0 hc n R τ hphys m0).T ^ k) z)
          (((obsTransfer hc0 hc n R τ hphys m0).T ^ k) z)
        ≤ ρr ^ 2 * (obsTransfer hc0 hc n R τ hphys m0).form z z)
    (hleak : ∀ y ∈ C, (obsTransfer hc0 hc n R τ hphys m0).form y
        (obsTransfer hc0 hc n R τ hphys m0).vac = 0 →
      ∀ z, (∀ w ∈ C, (obsTransfer hc0 hc n R τ hphys m0).form w z = 0) →
      (obsTransfer hc0 hc n R τ hphys m0).form
          (((obsTransfer hc0 hc n R τ hphys m0).T ^ k) y)
          (((obsTransfer hc0 hc n R τ hphys m0).T ^ k) z) ^ 2
        ≤ η ^ 2 * ((obsTransfer hc0 hc n R τ hphys m0).form y y
          * (obsTransfer hc0 hc n R τ hphys m0).form z z)) :
    FlowClusterAbs two_ne (obsFlowF c hc0 hc n R) τ r L :=
  (observer_M_iff_gap hc0 hc n R τ hphys m0 hL).mpr
    (gapAt_of_leak _ C hvac hsplit hk hρc hρr hη hcoarse hres hleak)

#print axioms observer_M_of_leak

end MassGap.ObserverResidual
