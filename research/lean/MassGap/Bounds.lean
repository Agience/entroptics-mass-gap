import Mathlib

/-!
# Correlation bounds (PAPER Sec 3, Sec 9)

* `strehl_bound` -- the Strehl / maximal-correlation bound `rho'(1)^2 <= 1` for a
  correlation `|r| <= 1`.
* `ising_transfer` -- the Ising-strip transfer certificate `rho'(1) = tanh b < 1`
  (the solvable case of "no interior transition").
-/

namespace MassGap

/-- **Strehl bound** (Sec 3/9): a correlation `r` with `|r| <= 1` has `r^2 <= 1`.
With `r = rho'(1)` the top correlation singular value, this is `rho'(1)^2 <= 1`. -/
theorem strehl_bound (r : ℝ) (h : |r| ≤ 1) : r ^ 2 ≤ 1 := by
  have h' := abs_le.mp h
  nlinarith [h'.1, h'.2]

/-- **Ising transfer certificate** (Sec 9): on the exactly-solvable Ising strip the
single-cut maximal correlation is `rho'(1) = tanh b`, and `tanh b < 1` for every `b`,
so the interior condition `rho'(1) < 1` holds unconditionally there. -/
theorem ising_transfer (b : ℝ) : Real.tanh b < 1 := by
  have hc : (0 : ℝ) < Real.cosh b := Real.cosh_pos b
  rw [Real.tanh_eq_sinh_div_cosh, div_lt_one hc]
  have h : Real.cosh b - Real.sinh b = Real.exp (-b) := by
    rw [Real.cosh_eq, Real.sinh_eq]; ring
  nlinarith [Real.exp_pos (-b), h]

end MassGap
