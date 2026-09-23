import Mathlib

/-!
# MassGap.Condensation — the directed-cube-path weight sequence

Everything here is about one real-valued sequence,
`vortexTerm μ n = 3^n · e^{-μ(4n+2)}`: a count `3^n` of directed-cube paths against the Boltzmann
weight of the area `4n+2` they enclose at tension `μ`.

Four groups of facts are proved about it, all for arbitrary real `μ`:

* `one_lt_base` — `μ < ¼ log 3` implies `1 < 3 e^{-4μ}`, the sequence's geometric base;
* `vortexTerm_tendsto_atTop` — under the same hypothesis the terms diverge, `vortexTerm μ n → ∞`. No
  sum over `n` appears in the statement, and the reverse implication is not proved;
* `log_vortexTerm` and `vortex_free_energy_per_step` — the log-weight `n log 3 − μ(4n+2)` and its exact
  per-step increment `4(¼ log 3 − μ)`;
* `log_Z_ge`, `density_ratio_ge` and `lower_ratio_tendsto` — for any `Z : ℕ → ℝ` dominating the
  sequence pointwise, `log (Z n)` is bounded below by the log-weight, and after division by the area
  that lower bound converges to `¼ log 3 − μ`. The liminf of `log (Z n) / (4n+2)` itself is not formed.

No declaration here mentions a lattice, a partition function or a vortex: `Z` is an arbitrary
dominating sequence and `μ` an arbitrary real.

Build: `lake build MassGap.Condensation`.
-/

namespace MassGap.Condensation

open Filter Topology

/-- The weight sequence `μ ↦ n ↦ 3^n · exp (-μ(4n + 2))`. It is positive for every real `μ` and every
`n`, since both factors are.

DERIVED: `3` is the directed-cube-path branching count per step, so `3^n` counts the length-`n`
surfaces; `4` is the area each step adds; `2` is the area of the length-zero surface, so the exponent
`4n + 2` is the total area carrying the tension `μ`. -/
noncomputable def vortexTerm (μ : ℝ) (n : ℕ) : ℝ := (3 : ℝ) ^ n * Real.exp (-μ * (4 * (n : ℝ) + 2))

/-- `μ < ¼ log 3` implies `1 < 3 · exp (-4μ)`. Proved by rewriting `1/3` as `exp (-log 3)` and
applying `Real.exp_lt_exp`. This base is what `vortexTerm_tendsto_atTop` feeds to
`tendsto_pow_atTop_atTop_of_one_lt`.

DERIVED: `1` is the threshold a geometric base must clear to diverge; `3` and `4` are `vortexTerm`'s
own branching count and per-step area, so `3 e^{-4μ}` is its term ratio; the `1 / 4` and `3` in the
hypothesis are those same two numbers rearranged, since `3 e^{-4μ} > 1` is exactly `μ < ¼ log 3`. -/
theorem one_lt_base {μ : ℝ} (hμ : μ < (1 / 4) * Real.log 3) : (1 : ℝ) < 3 * Real.exp (-4 * μ) := by
  have h13 : (1 / 3 : ℝ) < Real.exp (-4 * μ) := by
    rw [show (1 / 3 : ℝ) = Real.exp (-Real.log 3) by
          rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]; norm_num]
    exact Real.exp_lt_exp.mpr (by linarith)
  linarith

/-- For `μ < ¼ log 3`, `vortexTerm μ n → ∞` as `n → ∞`. The proof factors the sequence as
`exp (-2μ) · (3 e^{-4μ})^n`, applies `tendsto_pow_atTop_atTop_of_one_lt` to the base supplied by
`one_lt_base`, and scales by the positive constant through `Tendsto.const_mul_atTop`. The conclusion
is divergence of the terms; the statement contains no sum over `n`, and the converse is not proved.

DERIVED: `1 / 4` and `3` are `one_lt_base`'s hypothesis, which is where the numerals enter; they are
`vortexTerm`'s own `3` and `4` rearranged. -/
theorem vortexTerm_tendsto_atTop {μ : ℝ} (hμ : μ < (1 / 4) * Real.log 3) :
    Tendsto (vortexTerm μ) atTop atTop := by
  have hfac : ∀ n, vortexTerm μ n = Real.exp (-2 * μ) * (3 * Real.exp (-4 * μ)) ^ n := by
    intro n
    unfold vortexTerm
    rw [mul_pow, ← Real.exp_nat_mul,
        show -μ * (4 * (n : ℝ) + 2) = -2 * μ + (n : ℝ) * (-4 * μ) by ring, Real.exp_add]
    ring
  rw [tendsto_congr hfac]
  exact Tendsto.const_mul_atTop (Real.exp_pos _)
    (tendsto_pow_atTop_atTop_of_one_lt (one_lt_base hμ))

/-- `Real.log (vortexTerm μ n) = n · log 3 − μ(4n + 2)`, an identity for every real `μ` and every `n`.
It is `Real.log_mul` on the two positive factors, then `Real.log_pow` and `Real.log_exp`.

DERIVED: `3`, `4` and `2` are `vortexTerm`'s branching count, per-step area and base area, carried
through the logarithm unchanged. -/
theorem log_vortexTerm {μ : ℝ} (n : ℕ) :
    Real.log (vortexTerm μ n) = (n : ℝ) * Real.log 3 - μ * (4 * (n : ℝ) + 2) := by
  unfold vortexTerm
  rw [Real.log_mul (pow_ne_zero n (by norm_num : (3 : ℝ) ≠ 0)) (Real.exp_ne_zero _),
      Real.log_pow, Real.log_exp]
  ring

/-- The log-weight increment from `n` to `n + 1` is the constant `4(¼ log 3 − μ)`, exactly and for
every `n`. Two applications of `log_vortexTerm` then `push_cast; ring`: the `n`-dependence cancels, so
this is an equality rather than a bound, and it needs no hypothesis on `μ`. It is a statement about
`vortexTerm` alone and says nothing about any sequence dominating it.

DERIVED: the `1` in `n + 1` is the single step the increment is taken over; `4` on the right is the
area each step adds, and the `1 / 4` and `3` inside the bracket are `log 3` divided over those four
plaquettes, so the bracket is a per-plaquette rate and the leading `4` converts it back to a per-step
rate. -/
theorem vortex_free_energy_per_step {μ : ℝ} (n : ℕ) :
    Real.log (vortexTerm μ (n + 1)) - Real.log (vortexTerm μ n) = 4 * ((1 / 4) * Real.log 3 - μ) := by
  rw [log_vortexTerm (n + 1), log_vortexTerm n]
  push_cast
  ring

/-! ### Lower bounds transferred to a dominating sequence

The three declarations below take an arbitrary `Z : ℕ → ℝ` with `vortexTerm μ n ≤ Z n` for every `n`
and push the weight's log, and its log per unit area, downwards onto `Z`. `Z` carries no constraint
beyond that domination, and nothing identifies it with a partition function. The last statement is a
limit of the lower bound sequence, `n log 3 / (4n+2) − μ → ¼ log 3 − μ`; no limit or liminf of
`log (Z n) / (4n+2)` is formed. -/

/-- If `vortexTerm μ n ≤ Z n` for every `n`, then `n log 3 − μ(4n + 2) ≤ Real.log (Z n)`. The left-hand
side is `log_vortexTerm`, and `Real.log_le_log` needs its first argument positive, which `vortexTerm`
is by `positivity`. `Z` is an arbitrary real sequence; the domination hypothesis is its only
constraint.

DERIVED: `3`, `4` and `2` are `vortexTerm`'s branching count, per-step area and base area, arriving
through `log_vortexTerm`. -/
theorem log_Z_ge {μ : ℝ} {Z : ℕ → ℝ} (hZ : ∀ n, vortexTerm μ n ≤ Z n) (n : ℕ) :
    (n : ℝ) * Real.log 3 - μ * (4 * n + 2) ≤ Real.log (Z n) := by
  have hpos : 0 < vortexTerm μ n := by unfold vortexTerm; positivity
  calc (n : ℝ) * Real.log 3 - μ * (4 * n + 2)
      = Real.log (vortexTerm μ n) := (log_vortexTerm n).symm
    _ ≤ Real.log (Z n) := Real.log_le_log hpos (hZ n)

/-- `log_Z_ge` divided by the area `4n + 2`: `n log 3 / (4n+2) − μ ≤ Real.log (Z n) / (4n+2)`. The
division is `div_le_div_iff_of_pos_right` applied to `0 < 4n + 2`, which `positivity` supplies for
every `n`; `hn : 0 < n` is asked of callers even though the denominator is already positive at
`n = 0`.

DERIVED: `0` in `hn` is the excluded index; `3`, `4` and `2` are `vortexTerm`'s branching count,
per-step area and base area, the last two forming the area `4n + 2` that both sides are divided
by. -/
theorem density_ratio_ge {μ : ℝ} {Z : ℕ → ℝ} (hZ : ∀ n, vortexTerm μ n ≤ Z n) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * Real.log 3 / (4 * n + 2) - μ ≤ Real.log (Z n) / (4 * n + 2) := by
  have h4 : 0 < (4 * (n : ℝ) + 2) := by positivity
  have hstep := (div_le_div_iff_of_pos_right h4).mpr (log_Z_ge hZ n)
  have hrw : ((n : ℝ) * Real.log 3 - μ * (4 * n + 2)) / (4 * n + 2)
      = (n : ℝ) * Real.log 3 / (4 * n + 2) - μ := by field_simp
  rwa [hrw] at hstep

/-- The lower-bound sequence of `density_ratio_ge` converges:
`n log 3 / (4n + 2) − μ → ¼ log 3 − μ`. Proved by rewriting `n / (4n+2)` as `1 / (4 + 2/n)` eventually,
sending `2/n → 0`, and multiplying by the constant `log 3`. It is a statement about the bound only:
`Z` does not appear in it.

DERIVED: `3`, `4` and `2` are `vortexTerm`'s branching count, per-step area and base area; the limit's
`1 / 4` is `lim n/(4n+2)`, the reciprocal of the per-step area, so the limit is the per-plaquette
counting rate `¼ log 3` less the tension. -/
theorem lower_ratio_tendsto {μ : ℝ} :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) * Real.log 3 / (4 * n + 2) - μ) atTop
      (𝓝 (1 / 4 * Real.log 3 - μ)) := by
  have hnd : Filter.Tendsto (fun n : ℕ => (n : ℝ) / (4 * n + 2)) atTop (𝓝 (1 / 4)) := by
    have he : (fun n : ℕ => (n : ℝ) / (4 * n + 2)) =ᶠ[atTop] (fun n : ℕ => 1 / (4 + 2 / n)) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      field_simp
    rw [tendsto_congr' he]
    have h2n : Filter.Tendsto (fun n : ℕ => (2 : ℝ) / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 2
    have h4 : Filter.Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (𝓝 4) := tendsto_const_nhds
    have hden : Filter.Tendsto (fun n : ℕ => (4 : ℝ) + 2 / n) atTop (𝓝 4) := by
      simpa using h4.add h2n
    have hc : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have := hc.div hden (by norm_num)
    simpa [Pi.div_def, one_div] using this
  have hmain : Filter.Tendsto (fun n : ℕ => (n : ℝ) * Real.log 3 / (4 * n + 2)) atTop
      (𝓝 (1 / 4 * Real.log 3)) := by
    have := hnd.mul_const (Real.log 3)
    have he : (fun n : ℕ => (n : ℝ) / (4 * n + 2) * Real.log 3)
        = (fun n : ℕ => (n : ℝ) * Real.log 3 / (4 * n + 2)) := by
      funext n; ring
    rw [he] at this
    simpa using this
  simpa using hmain.sub_const μ

end MassGap.Condensation
