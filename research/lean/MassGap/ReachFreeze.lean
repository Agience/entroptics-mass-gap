import Mathlib

/-!
# MassGap.ReachFreeze — decay of a sequence satisfying a one-step contraction

Elementary real analysis about a sequence `sigma : ℕ → ℝ` obeying

    sigma (n + 1) ≤ (1 - c) * sigma n   for every n,

for a fixed real `c`. Nothing in this file mentions a lattice, a gauge group or a transfer operator;
`sigma` and `c` are arbitrary and every hypothesis is supplied by the caller.

* `excess_geometric` — with `c ≤ 1`, the contraction gives `sigma n ≤ (1 - c)^n * sigma 0`.
* `excess_exp_bound` — with `c ≤ 1` and `0 ≤ sigma 0`, it gives `sigma n ≤ exp (-c * n) * sigma 0`,
  by `1 - c ≤ exp (-c)`.
* `excess_tendsto_zero` — with `0 < c ≤ 1` and `sigma` nonnegative termwise, `sigma` converges to `0`.
* `gap_from_contraction` — the conjunction of the exponential bound, the limit, and `0 < c`.
* `excess_tendsto_zero_of_geom` — the same limit from a direct domination `σ n ≤ C * ρ^n` with
  `0 ≤ ρ < 1`, with no one-step contraction assumed.
* `confines_of_tension_lt_floor` — for reals `μ`, `κ`, `κ₀`, from `κ₀ ≤ κ` and `μ < κ₀` it follows
  that `μ - κ < 0`.

Every result is conditional on the hypotheses written into its statement. In particular `0 < c` is a
hypothesis throughout and is established nowhere in this file.
-/

namespace MassGap

variable {sigma : ℕ → ℝ} {c : ℝ}

/-- From the one-step bound `sigma (n + 1) ≤ (1 - c) * sigma n` for every `n`, together with
`c ≤ 1`, every term obeys `sigma n ≤ (1 - c)^n * sigma 0`. Proved by induction on `n`; `c ≤ 1` is
what makes `1 - c` nonnegative, so multiplying the inductive bound by it preserves the inequality.

No lower bound on `c` is assumed here, and `sigma` is not assumed nonnegative.

DERIVED: `1` is the successor step in `n + 1` and the unit from which `c` is subtracted to form the
contraction ratio `1 - c`, which appears in the hypothesis and in the conclusion; `c ≤ 1` is the same
unit, bounding the ratio below by zero. `0` indexes the initial term `sigma 0`. `c` is a variable of
the section, fixed by the caller. -/
theorem excess_geometric (hc1 : c ≤ 1)
    (hstep : ∀ n, sigma (n + 1) ≤ (1 - c) * sigma n) :
    ∀ n, sigma n ≤ (1 - c) ^ n * sigma 0 := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      have h1c : (0 : ℝ) ≤ 1 - c := by linarith
      calc sigma (k + 1) ≤ (1 - c) * sigma k := hstep k
        _ ≤ (1 - c) * ((1 - c) ^ k * sigma 0) := by
              exact mul_le_mul_of_nonneg_left ih h1c
        _ = (1 - c) ^ (k + 1) * sigma 0 := by ring

/-- The geometric bound of `excess_geometric` restated exponentially: with `c ≤ 1`, the one-step
contraction, and `0 ≤ sigma 0`, every term obeys `sigma n ≤ exp (-c * n) * sigma 0`.

The step is `1 - c ≤ exp (-c)` (from `Real.add_one_le_exp`), raised to the `n`-th power and then
multiplied through by `sigma 0`, which is why the nonnegativity of `sigma 0` is required — it is the
factor the inequality is multiplied by. Only `sigma 0` need be nonnegative; later terms are
unconstrained.

DERIVED: `1` is the successor step `n + 1` and the unit in `c ≤ 1` and in the ratio `1 - c`. `0`
indexes the initial term `sigma 0` and is its asserted lower bound in `hσ0`. The exponent `-c * n`
contains no literal; `c` is a section variable. -/
theorem excess_exp_bound (hc1 : c ≤ 1)
    (hstep : ∀ n, sigma (n + 1) ≤ (1 - c) * sigma n) (hσ0 : 0 ≤ sigma 0) :
    ∀ n, sigma n ≤ Real.exp (-c * n) * sigma 0 := by
  intro n
  have hgeo := excess_geometric hc1 hstep n
  have h1c : (0 : ℝ) ≤ 1 - c := by linarith
  have h1 : 1 - c ≤ Real.exp (-c) := by
    have := Real.add_one_le_exp (-c); linarith
  have h2 : (1 - c) ^ n ≤ (Real.exp (-c)) ^ n := by gcongr
  have h3 : (Real.exp (-c)) ^ n = Real.exp (-c * n) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hle : (1 - c) ^ n ≤ Real.exp (-c * n) := by rw [← h3]; exact h2
  calc sigma n ≤ (1 - c) ^ n * sigma 0 := hgeo
    _ ≤ Real.exp (-c * n) * sigma 0 := by exact mul_le_mul_of_nonneg_right hle hσ0

/-- With `0 < c ≤ 1`, the one-step contraction, and `sigma` nonnegative at every index, `sigma`
converges to `0` along `atTop`.

The proof squeezes `sigma` between the constant `0` and the bound of `excess_geometric`: `0 < c` puts
the ratio `1 - c` strictly below `1`, so `(1 - c)^n * sigma 0` converges to `0`, and termwise
nonnegativity supplies the lower side.

DERIVED: `0` is the strict lower bound on `c`, the termwise lower bound on `sigma`, and the limit
point. `1` is the unit in `c ≤ 1`, in `1 - c`, and the successor step `n + 1`. -/
theorem excess_tendsto_zero (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hstep : ∀ n, sigma (n + 1) ≤ (1 - c) * sigma n)
    (hσnn : ∀ n, 0 ≤ sigma n) :
    Filter.Tendsto sigma Filter.atTop (nhds 0) := by
  have hub := excess_geometric hc1 hstep
  have h1c : (0 : ℝ) ≤ 1 - c := by linarith
  have hlt : (1 - c) < 1 := by linarith
  have hpow : Filter.Tendsto (fun n => (1 - c) ^ n * sigma 0) Filter.atTop (nhds 0) := by
    have hz := tendsto_pow_atTop_nhds_zero_of_lt_one h1c hlt
    simpa using hz.mul_const (sigma 0)
  exact squeeze_zero hσnn hub hpow

/-- The three preceding results packaged as one conjunction. From `0 < c ≤ 1`, termwise
nonnegativity of `sigma`, and the one-step contraction, it returns: the exponential bound
`sigma n ≤ exp (-c * n) * sigma 0` for every `n`, convergence of `sigma` to `0`, and `0 < c` itself.

The third conjunct is the hypothesis `hc0` returned unchanged, so it adds no information beyond what
the caller supplied. The conclusion is a statement about `sigma` and `c` only; no operator, spectrum
or gap appears in it.

DERIVED: `0` is the strict lower bound on `c` (as hypothesis and as third conjunct), the termwise
lower bound on `sigma`, the index of `sigma 0`, and the limit point. `1` is the unit in `c ≤ 1`, in
`1 - c`, and the successor step `n + 1`. -/
theorem gap_from_contraction (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hσnn : ∀ n, 0 ≤ sigma n)
    (hstep : ∀ n, sigma (n + 1) ≤ (1 - c) * sigma n) :
    (∀ n, sigma n ≤ Real.exp (-c * n) * sigma 0) ∧
      Filter.Tendsto sigma Filter.atTop (nhds 0) ∧ 0 < c :=
  ⟨excess_exp_bound hc1 hstep (hσnn 0),
   excess_tendsto_zero hc0 hc1 hstep hσnn, hc0⟩

/-- For reals `μ`, `κ`, `κ₀`: if `κ₀ ≤ κ` and `μ < κ₀` then `μ - κ < 0`. Transitivity of the two
orderings, discharged by `linarith`.

The three variables are arbitrary reals. The intended reading is `μ` a centre-vortex tension, `κ` an
entropy density, `κ₀` a lower bound on it from `Floor.lean`, and `μ - κ` a free-energy density, but
no such interpretation enters the statement or the proof, and nothing about vortices, condensation or
confinement is asserted by it.

DERIVED: `0` is the sign asserted of the difference `μ - κ`; it is the only numeral. `μ`, `κ` and
`κ₀` are implicit arguments. -/
theorem confines_of_tension_lt_floor {μ κ κ₀ : ℝ} (hfloor : κ₀ ≤ κ) (htension : μ < κ₀) :
    μ - κ < 0 := by linarith

/-- A nonnegative sequence `σ` dominated termwise by a geometric sequence, `σ n ≤ C * ρ^n` with
`0 ≤ ρ < 1`, converges to `0` along `atTop`. Squeeze between the constant `0` and `C * ρ^n`.

The domination is assumed, not derived, and no one-step contraction is required: this is the form to
use when only a geometric envelope is available. `C` is an arbitrary real and is not assumed
positive; the hypothesis `hbound` together with `hσnn` forces it to be nonnegative whenever `σ` is
not identically zero, but the statement asserts nothing about it.

DERIVED: `0` is the lower bound on the ratio `ρ`, the termwise lower bound on `σ`, and the limit
point. `1` is the strict upper bound on `ρ` that makes `ρ^n` a null sequence. `C` and `ρ` are
implicit arguments. -/
theorem excess_tendsto_zero_of_geom {σ : ℕ → ℝ} {C ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hσnn : ∀ n, 0 ≤ σ n) (hbound : ∀ n, σ n ≤ C * ρ ^ n) :
    Filter.Tendsto σ Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun n => C * ρ ^ n) Filter.atTop (nhds 0) := by
    have hz := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
    simpa using hz.const_mul C
  exact squeeze_zero hσnn hbound hpow

end MassGap
