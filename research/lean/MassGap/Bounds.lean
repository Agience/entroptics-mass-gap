import Mathlib

/-!
# Correlation bounds

Two elementary real inequalities used where a maximal correlation `ρ'(1)` is bounded.

* `strehl_bound` — a real `r` with `|r| ≤ 1` satisfies `r ^ 2 ≤ 1`.
* `ising_transfer` — `Real.tanh b < 1` for every real `b`.

Both are statements about real numbers. Neither mentions a lattice, a transfer operator or a
correlation; the reading of `r` as a correlation and of `tanh b` as an Ising-strip maximal
correlation is supplied by the call site.
-/

namespace MassGap

/-- Squaring preserves the unit bound: a real `r` with `|r| ≤ 1` satisfies `r ^ 2 ≤ 1`. Stated for an
arbitrary real; nothing in it identifies `r` with a correlation.

DERIVED: the `1` on both sides is the same unit bound, carried from hypothesis to conclusion; the `2`
is the square being bounded. -/
theorem strehl_bound (r : ℝ) (h : |r| ≤ 1) : r ^ 2 ≤ 1 := by
  have h' := abs_le.mp h
  nlinarith [h'.1, h'.2]

/-- `Real.tanh b < 1` for every real `b`, with no hypothesis on `b`. The proof rewrites `tanh` as
`sinh / cosh`, uses `Real.cosh_pos`, and closes on `cosh b - sinh b = exp (-b) > 0`. The statement is
about `Real.tanh` alone; the identification of `tanh b` with an Ising-strip maximal correlation is
made by the caller, not here.

DERIVED: the `1` is the supremum of `tanh` on `ℝ`, equivalently the `cosh b - sinh b > 0` the proof
reduces to. -/
theorem ising_transfer (b : ℝ) : Real.tanh b < 1 := by
  have hc : (0 : ℝ) < Real.cosh b := Real.cosh_pos b
  rw [Real.tanh_eq_sinh_div_cosh, div_lt_one hc]
  have h : Real.cosh b - Real.sinh b = Real.exp (-b) := by
    rw [Real.cosh_eq, Real.sinh_eq]; ring
  nlinarith [Real.exp_pos (-b), h]

end MassGap
