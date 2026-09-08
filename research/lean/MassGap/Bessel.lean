import Mathlib

/-!
# C-2: the leading character ratio `r = I₂/I₁ > 0` from the modified-Bessel series

Mathlib carries no modified Bessel `Iν`, so we give the elementary power series for integer order,

    `I_n(x) = Σ_{k≥0} (x/2)^{2k+n} / (k! (k+n)!)`,

prove it is **summable** (termwise comparison with the exponential series `Σ ((x/2)²)^k/k! = exp((x/2)²)`)
and **strictly positive** for `x > 0` (every term is positive), hence `r = I₂/I₁ > 0` (`ym_ratio_pos`, a
theorem); the only input is that the Bessel argument (a coupling scale) is positive. The numeric value
`r(β⋆) ∈ [0.182, 0.184]` is separately certified in
`research/code/certify/beta_star_enclosure.py` (only positivity enters the Lean proof).
-/

namespace MassGap.Bessel

open scoped BigOperators Nat

/-- The `k`-th term of the modified Bessel series `I_n(x)`: `(x/2)^{2k+n} / (k! (k+n)!)`. -/
noncomputable def besselTerm (n : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  (x / 2) ^ (2 * k + n) / ((k.factorial : ℝ) * ((k + n).factorial : ℝ))

/-- The modified Bessel function of the first kind at integer order `n`,
`I_n(x) = Σ_k (x/2)^{2k+n}/(k!(k+n)!)`. -/
noncomputable def besselI (n : ℕ) (x : ℝ) : ℝ := ∑' k, besselTerm n x k

theorem besselTerm_nonneg (n : ℕ) (x : ℝ) (k : ℕ) (hx : 0 ≤ x) : 0 ≤ besselTerm n x k := by
  unfold besselTerm
  apply div_nonneg
  · exact pow_nonneg (by linarith) _
  · exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem besselTerm_pos (n : ℕ) (x : ℝ) (k : ℕ) (hx : 0 < x) : 0 < besselTerm n x k := by
  unfold besselTerm
  apply div_pos
  · exact pow_pos (by linarith) _
  · exact mul_pos (by exact_mod_cast k.factorial_pos) (by exact_mod_cast (k + n).factorial_pos)

/-- Each term is bounded by the corresponding term of `(x/2)^n · exp((x/2)²)` (drop the `(k+n)!` factor,
which is `≥ 1`). -/
theorem besselTerm_le (n : ℕ) (x : ℝ) (k : ℕ) (hx : 0 ≤ x) :
    besselTerm n x k ≤ (x / 2) ^ n * ((x / 2) ^ 2) ^ k / (k.factorial : ℝ) := by
  have hx2 : (0 : ℝ) ≤ x / 2 := by linarith
  have hnum : (x / 2) ^ (2 * k + n) = (x / 2) ^ n * ((x / 2) ^ 2) ^ k := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  unfold besselTerm
  rw [hnum, ← div_div]
  apply div_le_self
  · exact div_nonneg (mul_nonneg (pow_nonneg hx2 n) (pow_nonneg (sq_nonneg (x / 2)) k))
      (Nat.cast_nonneg _)
  · have h1 : (1 : ℕ) ≤ (k + n).factorial := (k + n).factorial_pos
    exact_mod_cast h1

theorem besselI_summable (n : ℕ) (x : ℝ) (hx : 0 ≤ x) : Summable (besselTerm n x) := by
  have hg : Summable (fun k => (x / 2) ^ n * ((x / 2) ^ 2) ^ k / (k.factorial : ℝ)) := by
    have h := (Real.summable_pow_div_factorial ((x / 2) ^ 2)).mul_left ((x / 2) ^ n)
    simpa [mul_div_assoc] using h
  exact Summable.of_nonneg_of_le (fun k => besselTerm_nonneg n x k hx)
    (fun k => besselTerm_le n x k hx) hg

/-- **The modified Bessel `I_n` is strictly positive for a positive argument.** Every series term is
positive (`besselTerm_pos`) and the series is summable, so its `tsum` is positive. -/
theorem besselI_pos (n : ℕ) {x : ℝ} (hx : 0 < x) : 0 < besselI n x := by
  unfold besselI
  exact (besselI_summable n x hx.le).tsum_pos
    (fun k => besselTerm_nonneg n x k hx.le) 0 (besselTerm_pos n x 0 hx)

/-- **The leading character ratio `I₂/I₁` is positive** for a positive argument — the C-2 content. -/
theorem ratio_pos {x : ℝ} (hx : 0 < x) : 0 < besselI 2 x / besselI 1 x :=
  div_pos (besselI_pos 2 hx) (besselI_pos 1 hx)

end MassGap.Bessel
