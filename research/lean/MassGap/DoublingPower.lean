import Mathlib
import MassGap.DoublingRecursion

/-!
# MassGap.DoublingPower — the doubling recursion from four trace facts, with no eigenvalue list

`DoublingRecursion` Part 1 derives purity squaring from a finite nonnegative spectrum. Its proof uses
four facts about the sequence `a m = Tr Kᵐ` and the top eigenvalue `λ`, and nothing else:

* `base`      — `a m = λᵐ (1 + s)` with `s ≥ 0` (the excited weight, relative);
* `dbl_le`    — `a (2m) ≤ λᵐ · a m`;
* `dbl_le_sq` — `a (2m) ≤ λ²ᵐ (1 + s²)`;
* `dbl_ge`, `quad_ge` — `λ²ᵐ ≤ a (2m)` and `λ⁴ᵐ ≤ a (4m)`.

`PowerFacts a λ s m` packages them. For an integral operator with a bounded symmetric kernel these
are kernel inequalities (`MassGap.KernelPower`): no trace-class theory and no spectral expansion is
needed. This module re-derives the squaring lemma from `PowerFacts` (`defect_squaring`,
`excited_le_two_defect`), turns a family of them into `DoublingRecursion.Positive`
(`positive_of_facts`), and bounds the excited weight on every dyadic corner from one seed
(`excited_le_corner`).
-/

namespace MassGap.DoublingPower

open Real MassGap.DoublingRecursion

/-- The four trace facts at one power `m`. -/
structure PowerFacts (a : ℕ → ℝ) (lam s : ℝ) (m : ℕ) : Prop where
  lam_pos : 0 < lam
  s_nonneg : 0 ≤ s
  base : a m = lam ^ m * (1 + s)
  dbl_le : a (2 * m) ≤ lam ^ m * a m
  dbl_le_sq : a (2 * m) ≤ lam ^ (2 * m) * (1 + s ^ 2)
  dbl_ge : lam ^ (2 * m) ≤ a (2 * m)
  quad_ge : lam ^ (2 * (2 * m)) ≤ a (2 * (2 * m))

/-- `2 log a m − log a (2m)`. -/
noncomputable def defect (a : ℕ → ℝ) (m : ℕ) : ℝ := 2 * log (a m) - log (a (2 * m))

variable {a : ℕ → ℝ} {lam s : ℝ} {m : ℕ}

theorem PowerFacts.lam_pow_pos (h : PowerFacts a lam s m) (k : ℕ) : 0 < lam ^ k :=
  pow_pos h.lam_pos k

theorem PowerFacts.a_pos (h : PowerFacts a lam s m) : 0 < a m := by
  rw [h.base]; exact mul_pos (h.lam_pow_pos m) (by linarith [h.s_nonneg])

theorem PowerFacts.a2_pos (h : PowerFacts a lam s m) : 0 < a (2 * m) :=
  lt_of_lt_of_le (h.lam_pow_pos _) h.dbl_ge

theorem PowerFacts.a4_pos (h : PowerFacts a lam s m) : 0 < a (2 * (2 * m)) :=
  lt_of_lt_of_le (h.lam_pow_pos _) h.quad_ge

/-- `s ≤ exp(defect) − 1`. -/
theorem excited_le (h : PowerFacts a lam s m) : s ≤ exp (defect a m) - 1 := by
  have hl := h.lam_pow_pos m
  have hA := h.a_pos
  have hB := h.a2_pos
  have h1 : log (a m / lam ^ m) ≤ defect a m := by
    rw [log_div hA.ne' hl.ne', defect]
    have : log (a (2 * m)) ≤ log (lam ^ m * a m) := log_le_log hB h.dbl_le
    rw [log_mul hl.ne' hA.ne'] at this
    linarith
  have h2 : a m / lam ^ m = 1 + s := by
    rw [h.base]; field_simp
  have h3 : 1 + s ≤ exp (defect a m) := by
    rw [← h2]
    calc a m / lam ^ m = exp (log (a m / lam ^ m)) := (exp_log (div_pos hA hl)).symm
      _ ≤ exp (defect a m) := exp_le_exp.mpr h1
  linarith

theorem defect_nonneg (h : PowerFacts a lam s m) : 0 ≤ defect a m := by
  have := excited_le h
  have := h.s_nonneg
  exact one_le_exp_iff.mp (by linarith)

/-- `defect (2m) ≤ 2 s²`. -/
theorem defect_double_le (h : PowerFacts a lam s m) : defect a (2 * m) ≤ 2 * s ^ 2 := by
  have hB := h.a2_pos
  have hC := h.a4_pos
  have hs1 : 0 < 1 + s ^ 2 := by positivity
  have hl4 : lam ^ (2 * (2 * m)) = (lam ^ (2 * m)) ^ 2 := by rw [← pow_mul]; ring_nf
  have hsq : a (2 * m) ^ 2 ≤ a (2 * (2 * m)) * (1 + s ^ 2) ^ 2 := by
    calc a (2 * m) ^ 2 ≤ (lam ^ (2 * m) * (1 + s ^ 2)) ^ 2 :=
          pow_le_pow_left₀ hB.le h.dbl_le_sq 2
      _ = lam ^ (2 * (2 * m)) * (1 + s ^ 2) ^ 2 := by rw [hl4]; ring
      _ ≤ a (2 * (2 * m)) * (1 + s ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_right h.quad_ge (by positivity)
  have hl := log_le_log (by positivity) hsq
  rw [log_pow, log_mul hC.ne' (by positivity), log_pow] at hl
  have hlog : log (1 + s ^ 2) ≤ s ^ 2 := by
    have := log_le_sub_one_of_pos hs1; linarith
  unfold defect
  push_cast at hl
  linarith

theorem excited_le_of_small (h : PowerFacts a lam s m) (hd : defect a m ≤ 1 / 4) :
    s ≤ 4 / 3 * defect a m := by
  have hd0 := defect_nonneg h
  have hexp := exp_bound_div_one_sub_of_interval hd0 (by linarith)
  have hb : 1 / (1 - defect a m) ≤ 1 + 4 / 3 * defect a m := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith [excited_le h]

theorem excited_le_two_defect (h : PowerFacts a lam s m) (hd : defect a m ≤ 1 / 4) :
    s ≤ 2 * defect a m := by
  have := excited_le_of_small h hd
  have := defect_nonneg h
  linarith

theorem defect_squaring (h : PowerFacts a lam s m) (hd : defect a m ≤ 1 / 4) :
    defect a (2 * m) ≤ 4 * defect a m ^ 2 := by
  have h1 := defect_double_le h
  have h2 := excited_le_of_small h hd
  have : s ^ 2 ≤ (4 / 3 * defect a m) ^ 2 := pow_le_pow_left₀ h.s_nonneg h2 2
  nlinarith

/-- A corner function realised, in every direction and at every corner, by trace facts. -/
def FactRep (x : Pt → ℝ) : Prop :=
  ∀ μ v, ∃ (a : ℕ → ℝ) (lam s : ℝ) (m : ℕ), PowerFacts a lam s m ∧ x v = log (a m) ∧
    x (v + E μ) = log (a (2 * m)) ∧ x (v + E μ + E μ) = log (a (2 * (2 * m)))

theorem positive_of_facts {x : Pt → ℝ} (hx : FactRep x) : Positive x where
  nonneg μ v := by
    obtain ⟨a, lam, s, m, h, h1, h2, -⟩ := hx μ v
    have := defect_nonneg h
    rw [p, h1, h2]; unfold defect at this; linarith
  sq μ v hp := by
    obtain ⟨a, lam, s, m, h, h1, h2, h3⟩ := hx μ v
    have e1 : p x μ v = defect a m := by rw [p, h1, h2]; rfl
    have e2 : p x μ (v + E μ) = defect a (2 * m) := by rw [p, h2, h3]; rfl
    rw [e1] at hp ⊢; rw [e2]
    exact defect_squaring h hp

/-- One seed bounds the relative excited weight of the direction-0 transfer on every dyadic
corner: `Δ ≤ 1/7480` at corner 0 gives `s ≤ (1/2)^(2^k)` at corner `k`. -/
theorem excited_le_corner {x : Pt → ℝ} (hx : Positive x) (h0 : Δ x (corner 0) ≤ 1 / 7480) (k : ℕ)
    {a : ℕ → ℝ} {lam s : ℝ} {m : ℕ} (h : PowerFacts a lam s m)
    (h1 : x (corner k) = log (a m)) (h2 : x (corner k + E 0) = log (a (2 * m))) :
    s ≤ (1 / 2) ^ (2 ^ k) := by
  have hit := iterate hx (by linarith) k
  have hpd : p x 0 (corner k) = defect a m := by rw [p, h1, h2]; rfl
  have h8 := p_le_Δ hx (corner k)
  have hpos : 0 ≤ ((1 : ℝ) / 2) ^ (2 ^ k) := by positivity
  have hhalf : ((1 : ℝ) / 2) ^ (2 ^ k) ≤ 1 / 2 := by
    have := pow_le_pow_of_le_one (a := (1 : ℝ) / 2) (by norm_num) (by norm_num)
      (Nat.one_le_two_pow (n := k))
    simpa using this
  have hd : defect a m ≤ 1 / 4 := by rw [← hpd]; linarith
  have := excited_le_two_defect h hd
  rw [← hpd] at this
  linarith

#print axioms defect_squaring
#print axioms positive_of_facts
#print axioms excited_le_corner

end MassGap.DoublingPower
