import Mathlib
import MassGap.DoublingWilson

/-!
# MassGap.DoublingSharp — the doubling recursion with constant 250 and seed threshold 1/1000

`DoublingRecursion` uses the squaring bound `p(2m) ≤ 4p²` (valid for `p ≤ 1/4`) and the class bound
`3^j`, which give `C₄ = 3740` and seed `1/7480`. Near zero the squaring factor is `2` and the class
bound `2^j`, so the constant tends to `2·(8 + 4·4 + 2·16 + 64) = 240`. Here:

* `defect_squaring_sharp` — from the four trace facts, `p ≤ 1/100 ⇒ p(2m) ≤ (41/20)·p²`;
* `rec_sharp` — `Δ ≤ 1/1000 ⇒ Δ(a+𝟙) ≤ 250·Δ(a)²`;
* `iterate_sharp` — `250·Δ(0) ≤ 1/4 ⇒ 250·Δ(k𝟙) ≤ (1/4)^(2^k)`;
* `wilson_gap_sharp` — `DoublingWilson.wilson_gap` with the seed `1/1000` in place of `1/7480`.

The seed threshold is 7.48 times larger; a Monte Carlo band on `Δ` of half-width `ε` costs `∝ 1/ε²`,
so certification at the threshold is about 56 times cheaper.
-/

namespace MassGap.DoublingSharp

open Real MassGap.DoublingRecursion MassGap.DoublingPower

/-- The sharp squaring hypothesis. -/
structure PositiveS (x : Pt → ℝ) : Prop where
  nonneg : ∀ μ v, 0 ≤ p x μ v
  sq : ∀ μ v, p x μ v ≤ 1 / 100 → p x μ (v + E μ) ≤ 41 / 20 * p x μ v ^ 2

variable {a : ℕ → ℝ} {lam s : ℝ} {m : ℕ}

theorem defect_squaring_sharp (h : PowerFacts a lam s m) (hd : defect a m ≤ 1 / 100) :
    defect a (2 * m) ≤ 41 / 20 * defect a m ^ 2 := by
  set d := defect a m
  have hd0 : 0 ≤ d := defect_nonneg h
  have h1 := defect_double_le h
  have h2 := excited_le h
  have hs0 := h.s_nonneg
  have hexp : Real.exp d ≤ 100 / 99 := by
    have := exp_bound_div_one_sub_of_interval hd0 (by linarith)
    calc Real.exp d ≤ 1 / (1 - d) := this
      _ ≤ 100 / 99 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hm : Real.exp d - 1 ≤ d * Real.exp d := by
    have e1 := Real.add_one_le_exp (-d)
    have e2 : Real.exp (-d) * Real.exp d = 1 := by rw [← Real.exp_add]; simp
    have e3 := Real.exp_pos d
    nlinarith
  have hs : s ≤ d * (100 / 99) := by
    calc s ≤ Real.exp d - 1 := h2
      _ ≤ d * Real.exp d := hm
      _ ≤ d * (100 / 99) := mul_le_mul_of_nonneg_left hexp hd0
  have : s ^ 2 ≤ (d * (100 / 99)) ^ 2 := pow_le_pow_left₀ hs0 hs 2
  nlinarith

theorem positiveS_of_facts {x : Pt → ℝ} (hx : FactRep x) : PositiveS x where
  nonneg μ v := (positive_of_facts hx).nonneg μ v
  sq μ v hp := by
    obtain ⟨a, lam, s, m, h, h1, h2, h3⟩ := hx μ v
    have e1 : p x μ v = defect a m := by rw [p, h1, h2]; rfl
    have e2 : p x μ (v + E μ) = defect a (2 * m) := by rw [p, h2, h3]; rfl
    rw [e1] at hp ⊢; rw [e2]
    exact defect_squaring_sharp h hp

variable {x : Pt → ℝ}

theorem sqrS (hx : PositiveS x) (μ : Fin 4) (v u t : Pt) (h1 : v + E μ = u) (h2 : u + E μ = t)
    (hs : 2 * x v - x u ≤ 1 / 100) : 2 * x u - x t ≤ 41 / 20 * (2 * x v - x u) ^ 2 := by
  have := hx.sq μ v
  simp only [p, h1, h2] at this
  exact this hs

theorem nnS (hx : PositiveS x) (μ : Fin 4) (v u : Pt) (h : v + E μ = u) : 0 ≤ 2 * x v - x u := by
  have := hx.nonneg μ v; rw [p, h] at this; exact this

/-- The raising step with separate bounds: `≤ 2a + (41/20) c²`. -/
theorem stepS (hx : PositiveS x) (μ ν : Fin 4) (cμ cν cμν cνν cμνν : Pt)
    (h3 : cν + E μ = cμν) (h4 : cμ + E ν = cμν) (h5 : cν + E ν = cνν)
    (h6 : cμν + E ν = cμνν) (h7 : cνν + E μ = cμνν) {A B : ℝ} (hB : B ≤ 1 / 100)
    (hA : 2 * x cν - x cμν ≤ A) (hC : 2 * x cμ - x cμν ≤ B) :
    2 * x cνν - x cμνν ≤ 2 * A + 41 / 20 * B ^ 2 := by
  have n1 := nnS hx ν cν cνν h5
  have n2 := nnS hx ν cμ cμν h4
  have s1 := sqrS hx ν cμ cμν cμνν h4 h6 (by linarith)
  have : (2 * x cμ - x cμν) ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ n2 hC 2
  have _ := h3; have _ := h7
  nlinarith

theorem rec_zero_sharp (hx : PositiveS x) (hD : Δ x ![0, 0, 0, 0] ≤ 1 / 1000) :
    Δ x ![1, 1, 1, 1] ≤ 250 * Δ x ![0, 0, 0, 0] ^ 2 := by
  have e00 : (![0, 0, 0, 0] : Pt) + one = ![1, 1, 1, 1] := by decide
  have e11 : (![1, 1, 1, 1] : Pt) + one = ![2, 2, 2, 2] := by decide
  simp only [Δ, e00, e11] at hD ⊢
  set D := 16 * x ![0, 0, 0, 0] - x ![1, 1, 1, 1] with hDdef
  have a1 := nnS hx 1 ![0, 0, 0, 0] ![0, 1, 0, 0] (by decide)
  have a2 := nnS hx 2 ![0, 1, 0, 0] ![0, 1, 1, 0] (by decide)
  have a3 := nnS hx 3 ![0, 1, 1, 0] ![0, 1, 1, 1] (by decide)
  have a4 := nnS hx 0 ![0, 1, 1, 1] ![1, 1, 1, 1] (by decide)
  have b1 := nnS hx 0 ![0, 0, 0, 0] ![1, 0, 0, 0] (by decide)
  have b2 := nnS hx 2 ![1, 0, 0, 0] ![1, 0, 1, 0] (by decide)
  have b3 := nnS hx 3 ![1, 0, 1, 0] ![1, 0, 1, 1] (by decide)
  have b4 := nnS hx 1 ![1, 0, 1, 1] ![1, 1, 1, 1] (by decide)
  have c2 := nnS hx 1 ![1, 0, 0, 0] ![1, 1, 0, 0] (by decide)
  have c3 := nnS hx 3 ![1, 1, 0, 0] ![1, 1, 0, 1] (by decide)
  have c4 := nnS hx 2 ![1, 1, 0, 1] ![1, 1, 1, 1] (by decide)
  have d3 := nnS hx 2 ![1, 1, 0, 0] ![1, 1, 1, 0] (by decide)
  have d4 := nnS hx 3 ![1, 1, 1, 0] ![1, 1, 1, 1] (by decide)
  have hD0 : 0 ≤ D := by linarith
  have B1 : 2 * x ![0, 1, 1, 1] - x ![1, 1, 1, 1] ≤ D := by linarith
  have B2 : 2 * x ![1, 0, 1, 1] - x ![1, 1, 1, 1] ≤ D := by linarith
  have B3 : 2 * x ![1, 1, 0, 1] - x ![1, 1, 1, 1] ≤ D := by linarith
  have B4 : 2 * x ![1, 1, 1, 0] - x ![1, 1, 1, 1] ≤ D := by linarith
  have k1 : 2 * D + 41 / 20 * D ^ 2 ≤ 2003 / 1000 * D := by nlinarith
  have S1 : 2 * x ![2, 0, 1, 1] - x ![2, 1, 1, 1] ≤ 2003 / 1000 * D :=
    (stepS hx 1 0 ![0, 1, 1, 1] ![1, 0, 1, 1] ![1, 1, 1, 1] ![2, 0, 1, 1] ![2, 1, 1, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith) B2 B1).trans k1
  have S2 : 2 * x ![2, 1, 0, 1] - x ![2, 1, 1, 1] ≤ 2003 / 1000 * D :=
    (stepS hx 2 0 ![0, 1, 1, 1] ![1, 1, 0, 1] ![1, 1, 1, 1] ![2, 1, 0, 1] ![2, 1, 1, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith) B3 B1).trans k1
  have S4 : 2 * x ![2, 1, 1, 0] - x ![2, 1, 1, 1] ≤ 2003 / 1000 * D :=
    (stepS hx 3 0 ![0, 1, 1, 1] ![1, 1, 1, 0] ![1, 1, 1, 1] ![2, 1, 1, 0] ![2, 1, 1, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith) B4 B1).trans k1
  have k2 : 2 * (2003 / 1000 * D) + 41 / 20 * (2003 / 1000 * D) ^ 2 ≤ 4015 / 1000 * D := by
    nlinarith
  have S3 : 2 * x ![2, 2, 0, 1] - x ![2, 2, 1, 1] ≤ 4015 / 1000 * D :=
    (stepS hx 2 1 ![2, 0, 1, 1] ![2, 1, 0, 1] ![2, 1, 1, 1] ![2, 2, 0, 1] ![2, 2, 1, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith) S2 S1).trans k2
  have S6 : 2 * x ![2, 2, 1, 0] - x ![2, 2, 1, 1] ≤ 4015 / 1000 * D :=
    (stepS hx 3 1 ![2, 0, 1, 1] ![2, 1, 1, 0] ![2, 1, 1, 1] ![2, 2, 1, 0] ![2, 2, 1, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith) S4 S1).trans k2
  have k3 : 2 * (4015 / 1000 * D) + 41 / 20 * (4015 / 1000 * D) ^ 2 ≤ 807 / 100 * D := by
    nlinarith
  have S7 : 2 * x ![2, 2, 2, 0] - x ![2, 2, 2, 1] ≤ 807 / 100 * D :=
    (stepS hx 3 2 ![2, 2, 0, 1] ![2, 2, 1, 0] ![2, 2, 1, 1] ![2, 2, 2, 0] ![2, 2, 2, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith) S6 S3).trans k3
  have m1 := nnS hx 1 ![2, 0, 1, 1] ![2, 1, 1, 1] (by decide)
  have m2 := nnS hx 2 ![2, 2, 0, 1] ![2, 2, 1, 1] (by decide)
  have m3 := nnS hx 3 ![2, 2, 2, 0] ![2, 2, 2, 1] (by decide)
  have q0 := sqrS hx 0 ![0, 1, 1, 1] ![1, 1, 1, 1] ![2, 1, 1, 1] (by decide) (by decide)
    (by linarith)
  have q1 := sqrS hx 1 ![2, 0, 1, 1] ![2, 1, 1, 1] ![2, 2, 1, 1] (by decide) (by decide)
    (by linarith)
  have q2 := sqrS hx 2 ![2, 2, 0, 1] ![2, 2, 1, 1] ![2, 2, 2, 1] (by decide) (by decide)
    (by linarith)
  have q3 := sqrS hx 3 ![2, 2, 2, 0] ![2, 2, 2, 1] ![2, 2, 2, 2] (by decide) (by decide)
    (by linarith)
  have r0 : (2 * x ![0, 1, 1, 1] - x ![1, 1, 1, 1]) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ a4 B1 2
  have r1 : (2 * x ![2, 0, 1, 1] - x ![2, 1, 1, 1]) ^ 2 ≤ (2003 / 1000 * D) ^ 2 :=
    pow_le_pow_left₀ m1 S1 2
  have r2 : (2 * x ![2, 2, 0, 1] - x ![2, 2, 1, 1]) ^ 2 ≤ (4015 / 1000 * D) ^ 2 :=
    pow_le_pow_left₀ m2 S3 2
  have r3 : (2 * x ![2, 2, 2, 0] - x ![2, 2, 2, 1]) ^ 2 ≤ (807 / 100 * D) ^ 2 :=
    pow_le_pow_left₀ m3 S7 2
  have f0 := q0.trans (mul_le_mul_of_nonneg_left r0 (by norm_num : (0 : ℝ) ≤ 41 / 20))
  have f1 := q1.trans (mul_le_mul_of_nonneg_left r1 (by norm_num : (0 : ℝ) ≤ 41 / 20))
  have f2 := q2.trans (mul_le_mul_of_nonneg_left r2 (by norm_num : (0 : ℝ) ≤ 41 / 20))
  have f3 := q3.trans (mul_le_mul_of_nonneg_left r3 (by norm_num : (0 : ℝ) ≤ 41 / 20))
  have hsum : 16 * x ![1, 1, 1, 1] - x ![2, 2, 2, 2]
      = 8 * (2 * x ![1, 1, 1, 1] - x ![2, 1, 1, 1]) + 4 * (2 * x ![2, 1, 1, 1] - x ![2, 2, 1, 1])
        + 2 * (2 * x ![2, 2, 1, 1] - x ![2, 2, 2, 1]) + (2 * x ![2, 2, 2, 1] - x ![2, 2, 2, 2]) := by
    ring
  clear a1 a2 a3 b1 b2 b3 b4 c2 c3 c4 d3 d4 k1 k2 k3 S2 S4 S6 B2 B3 B4 q0 q1 q2 q3 r0 r1 r2 r3
  rw [hsum]
  have hD2 : 0 ≤ D ^ 2 := sq_nonneg D
  have hc : 8 * (41 / 20 * D ^ 2) + 4 * (41 / 20 * (2003 / 1000 * D) ^ 2)
      + 2 * (41 / 20 * (4015 / 1000 * D) ^ 2) + 41 / 20 * (807 / 100 * D) ^ 2 ≤ 250 * D ^ 2 := by
    nlinarith
  linarith

theorem positiveS_shift (hx : PositiveS x) (a : Pt) : PositiveS (shift x a) where
  nonneg μ v := by
    have := hx.nonneg μ (a + v); simpa [p, shift, add_assoc] using this
  sq μ v h := by
    have := hx.sq μ (a + v) (by simpa [p, shift, add_assoc] using h)
    simpa [p, shift, add_assoc] using this

theorem rec_sharp (hx : PositiveS x) (a : Pt) (hD : Δ x a ≤ 1 / 1000) :
    Δ x (a + one) ≤ 250 * Δ x a ^ 2 := by
  have := rec_zero_sharp (positiveS_shift hx a) (by rwa [Δ_shift])
  rwa [Δ_shift_one, Δ_shift] at this

theorem iterate_sharp (hx : PositiveS x) (hp : Positive x) (h0 : 250 * Δ x (corner 0) ≤ 1 / 4) :
    ∀ k, 250 * Δ x (corner k) ≤ (1 / 4) ^ (2 ^ k) := by
  intro k
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    have hk0 := Δ_nonneg hp (corner k)
    have hq : ((1 : ℝ) / 4) ^ (2 ^ k) ≤ 1 / 4 := by
      have := pow_le_pow_of_le_one (a := (1 : ℝ) / 4) (by norm_num) (by norm_num)
        (Nat.one_le_two_pow (n := k))
      simpa using this
    have hsmall : Δ x (corner k) ≤ 1 / 1000 := by linarith
    have hr := rec_sharp hx (corner k) hsmall
    rw [corner_succ]
    have hsq : (250 * Δ x (corner k)) ^ 2 ≤ ((1 / 4 : ℝ) ^ (2 ^ k)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) ih 2
    have : ((1 / 4 : ℝ) ^ (2 ^ k)) ^ 2 = (1 / 4) ^ (2 ^ (k + 1)) := by
      rw [← pow_mul, pow_succ]
    nlinarith

/-- The excited weight at corner `k` from the sharp seed. -/
theorem excited_le_corner_sharp (hx : PositiveS x) (hp : Positive x)
    (h0 : Δ x (corner 0) ≤ 1 / 1000) (k : ℕ) {a : ℕ → ℝ} {lam s : ℝ} {m : ℕ}
    (h : PowerFacts a lam s m) (h1 : x (corner k) = Real.log (a m))
    (h2 : x (corner k + E 0) = Real.log (a (2 * m))) :
    s ≤ (1 / 2) ^ (2 ^ k) := by
  have hit := iterate_sharp hx hp (by linarith) k
  have hpd : p x 0 (corner k) = defect a m := by rw [p, h1, h2]; rfl
  have h8 := p_le_Δ hp (corner k)
  have hq : ((1 : ℝ) / 4) ^ (2 ^ k) ≤ (1 / 2) ^ (2 ^ k) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hq1 : ((1 : ℝ) / 4) ^ (2 ^ k) ≤ 1 / 4 := by
    have := pow_le_pow_of_le_one (a := (1 : ℝ) / 4) (by norm_num) (by norm_num)
      (Nat.one_le_two_pow (n := k))
    simpa using this
  have hpos : 0 ≤ ((1 : ℝ) / 4) ^ (2 ^ k) := by positivity
  have hd : defect a m ≤ 1 / 4 := by rw [← hpd]; linarith
  have := excited_le_two_defect h hd
  rw [← hpd] at this
  linarith

open MeasureTheory MassGap.RectWilson MassGap.RectTransfer MassGap.KernelPower
  MassGap.DoublingWilson MassGap.SlabKernelOperator

variable {N : ℕ} (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)

include hN hβ hn he in
/-- `DoublingWilson.wilson_gap` with the sharp seed `1/1000`. -/
theorem wilson_gap_sharp
    (h0 : 16 * Real.log (ZR (fun _ => n) N β) - Real.log (ZR (fun _ => 2 * n) N β) ≤ 1 / 1000)
    (k : ℕ) :
    ∃ ψ : Lp ℝ 2 (hS 0 (tr (ext n (corner k)) 0) N), ‖ψ‖ = 1 ∧
      ∃ c : ℝ, |c| = ‖kernelCLM (kT 0 (tr (ext n (corner k)) 0) N β) 1 (continuous_kT β).measurable
          zero_le_one (abs_kT_le hN hβ) (hS 0 (tr (ext n (corner k)) 0) N)
          (hS 0 (tr (ext n (corner k)) 0) N)‖ ∧
      kernelCLM (kT 0 (tr (ext n (corner k)) 0) N β) 1 (continuous_kT β).measurable zero_le_one
          (abs_kT_le hN hβ) (hS 0 (tr (ext n (corner k)) 0) N) (hS 0 (tr (ext n (corner k)) 0) N) ψ
        = c • ψ ∧
      ∀ f : Lp ℝ 2 (hS 0 (tr (ext n (corner k)) 0) N), inner ℝ f ψ = 0 →
        ‖((kernelCLM (kT 0 (tr (ext n (corner k)) 0) N β) 1 (continuous_kT β).measurable
          zero_le_one (abs_kT_le hN hβ) (hS 0 (tr (ext n (corner k)) 0) N)
          (hS 0 (tr (ext n (corner k)) 0) N)) ^ n) f‖
          ≤ 1 / 2 * ‖kernelCLM (kT 0 (tr (ext n (corner k)) 0) N β) 1 (continuous_kT β).measurable
            zero_le_one (abs_kT_le hN hβ) (hS 0 (tr (ext n (corner k)) 0) N)
            (hS 0 (tr (ext n (corner k)) 0) N)‖ ^ n * ‖f‖ := by
  set T := tr (ext n (corner k)) 0
  have hfr := factRep hN hβ hn he
  have hp := positive_of_facts hfr
  have hx := positiveS_of_facts hfr
  have hΔ : Δ (xW N n β) (corner 0) ≤ 1 / 1000 := by rw [Δ_corner0]; exact h0
  obtain ⟨φ, hφm, ⟨B, hφb⟩, hφ1, c, hc, heig⟩ :=
    KernelEigen.exists_eigen (μ := hS 0 T N) (continuous_kT β) zero_le_one (abs_kT_le hN hβ)
      (kT_symm β) (K_pos hN hβ 0 T)
  have hc0 : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hc; linarith [K_pos hN hβ 0 T]
  obtain ⟨n', hn'⟩ := he
  set j := 2 ^ k * n' with hjdef
  have hj : 1 ≤ j := by
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h2 : 1 ≤ n' := by omega
    rw [hjdef]; exact Nat.mul_le_mul h1 h2
  have hpf := powerFacts (μ := hS 0 T N) (continuous_kT β).measurable zero_le_one
    (abs_kT_le hN hβ) (kT_symm β) hφm hφb hφ1 heig hc hc0 j hj
  have hm : ext n (corner k) 0 = 2 * j := by simp only [ext, corner, hjdef, hn']; ring
  have h1 : xW N n β (corner k) = Real.log (F N β 0 T (2 * j)) := by
    rw [xW_eq hN hβ hn ⟨n', hn'⟩ (corner k) 0, hm]
  have h2 : xW N n β (corner k + E 0) = Real.log (F N β 0 T (2 * (2 * j))) := by
    rw [xW_eq hN hβ hn ⟨n', hn'⟩ (corner k + E 0) 0, tr_ext_add, ext_add_self, hm]
  have hexc := excited_le_corner_sharp hx hp hΔ k hpf h1 h2
  have hidx : 2 ^ k * n / 2 = j := by
    rw [hn', hjdef, show 2 ^ k * (n' + n') = 2 * (2 ^ k * n') by ring]
    exact Nat.mul_div_cancel_left _ two_pos
  refine ⟨KernelGap.vac (μ := hS 0 T N) hφm hφb, KernelGap.norm_vac hφm hφb hφ1, c, hc,
    KernelGap.K_vac _ _ _ hφm hφb heig, fun f hf => ?_⟩
  exact KernelGap.gap_of_excited (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
    (kT_symm β) hφm hφb hφ1 heig hc hc0 k n (by omega) ⟨n', hn'⟩ (by rw [hidx]; exact hexc) f hf

#print axioms rec_sharp
#print axioms iterate_sharp
#print axioms wilson_gap_sharp

end MassGap.DoublingSharp
