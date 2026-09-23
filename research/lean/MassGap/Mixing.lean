import MassGap.ReachFreeze
import MassGap.Certify

/-!
# MassGap.Mixing — geometric decay and a Lipschitz-grid ceiling for a single-cut maximal correlation

Two real-analysis facts, phrased for a single-cut maximal correlation `ρ'(1)`:

* `gap_of_maximal_correlation` — a nonnegative sequence dominated by `σ 0 * ρ₁ ^ n` with `ρ₁ < 1`
  converges to `0`.
* `interior_mixing_of_analytic_grid` — an `L`-Lipschitz function on `Set.Icc a b` whose value is
  certified at or below `(1 - ε) - L * δ` on a `δ`-net of the interval stays strictly below `1` on
  the whole interval.

Each is a wrapper: the first around `ReachFreeze.excess_tendsto_zero_of_geom`, the second around
`Certify.le_of_lipschitz_grid`.

Scope: the index quantified over is a separation `n` in the first statement and a parameter
`β ∈ [a, b]` in the second. No volume index occurs in either, so neither constrains behaviour as the
volume grows; the intensive premise `∀ F, m_hi F ≤ r` that
`Certify.gap_uniform_in_volume_of_intensive` consumes is a separate statement.
-/

namespace MassGap

open Filter

/-- A nonnegative real sequence dominated by a geometric one converges to zero. Takes `0 ≤ ρ₁`,
`ρ₁ < 1`, nonnegativity of `σ` at every index, and the domination `σ n ≤ σ 0 * ρ₁ ^ n` at every
index; concludes `Tendsto σ atTop (nhds 0)`. The domination `hsub` is a hypothesis supplied by the
caller, not derived here. The index `n` is a separation; the statement carries no volume index.
Wraps `ReachFreeze.excess_tendsto_zero_of_geom`.

DERIVED: `0` is the lower bound on `ρ₁` and on each `σ n`, the initial index in `σ 0`, and the
limit point; `1` is the strict ceiling on `ρ₁` that makes `ρ₁ ^ n` decay. Both come from the
sequence's own arithmetic, not from the model. -/
theorem gap_of_maximal_correlation {σ : ℕ → ℝ} {ρ₁ : ℝ}
    (hρ0 : 0 ≤ ρ₁) (hρ1 : ρ₁ < 1) (hσnn : ∀ n, 0 ≤ σ n)
    (hsub : ∀ n, σ n ≤ σ 0 * ρ₁ ^ n) :
    Tendsto σ atTop (nhds 0) :=
  excess_tendsto_zero_of_geom hρ0 hρ1 hσnn hsub

/-- A Lipschitz function certified below a margin on a net stays strictly below `1` on the whole
interval. Takes `0 ≤ L`, `0 < ε`, the `L`-Lipschitz estimate `|ρ₁ x - ρ₁ y| ≤ L * |x - y|` on
`Set.Icc a b`, and a covering hypothesis giving every `β ∈ [a, b]` some `γ ∈ [a, b]` with
`|β - γ| ≤ δ` and `ρ₁ γ ≤ (1 - ε) - L * δ`; concludes `ρ₁ β < 1` for every `β ∈ [a, b]`. The proof
applies `Certify.le_of_lipschitz_grid` at `B = 1 - ε` to get `ρ₁ β ≤ 1 - ε`, then uses `0 < ε` for
strictness. Quantifies over `β` in the interval only; no volume index appears, so the bound is not
transported between volumes. Companion of `Interior.interior_confinement_of_analytic_grid`, with
`ρ₁` in place of the squared-displacement functional.

DERIVED: `0` is the lower bound on the Lipschitz constant `L` and the strict lower bound on the
margin `ε`; `1` is the ceiling in the conclusion and the base of the certified value `(1 - ε)`.
`L`, `δ` and `ε` are all the caller's; no numeral is a model constant. -/
theorem interior_mixing_of_analytic_grid {ρ₁ : ℝ → ℝ} {a b L δ ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε)
    (hlip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |ρ₁ x - ρ₁ y| ≤ L * |x - y|)
    (hcover : ∀ β ∈ Set.Icc a b, ∃ γ ∈ Set.Icc a b, |β - γ| ≤ δ ∧ ρ₁ γ ≤ (1 - ε) - L * δ) :
    ∀ β ∈ Set.Icc a b, ρ₁ β < 1 := by
  intro β hβ
  have h : ρ₁ β ≤ 1 - ε := le_of_lipschitz_grid hL hlip hcover β hβ
  linarith

end MassGap
