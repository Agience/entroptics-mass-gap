import MassGap.ReachFreeze
import MassGap.Certify

/-!
# MassGap.Mixing — the A1 resolution route via `ρ'(1)` (single-cut maximal correlation)

A1 reduces to the junction `κ − μ ≤ c`, equivalently `ρ'(1) < 1` (Dobrushin–Shlosman complete analyticity;
notes §8–§9). Reflection positivity makes the Euclidean-time transfer operator self-adjoint (reversible), so
the single-cut maximal correlation equals the dominant sub-vacuum eigenvalue, `ρ'(1) = m_hi`, and
`ρ'(n) = ρ'(1)^n` **exactly**: one cut controls every separation and every volume, so `ρ'(1) < 1` gives the
uniform-in-volume gap for free — no separate intensive-margin companion.

This module implements the two Lean pieces of the resolution plan (§9):
* **S1** — `ρ'(1) < 1 ⇒ the correlator forgets` (`gap_of_maximal_correlation`);
* **S3** — interior `ρ'(1) < 1` from finite-volume analyticity + a finite grid
  (`interior_mixing_of_analytic_grid`).

Both reduce to already-proved lemmas (`ReachFreeze.excess_tendsto_zero_of_geom`,
`Certify.le_of_lipschitz_grid`). Imported by the `MassGap` aggregate (`MassGap.lean`).
-/

namespace MassGap

open Filter

/-- **S1 — `ρ'(1) < 1 ⇒ the correlator forgets.** With the reach-freeze excess bounded by the single-cut
maximal correlation, `σ n ≤ σ 0 · ρ'(1)^n` (RP reversibility gives `ρ'(n) = ρ'(1)^n`), a strict `ρ'(1) < 1`
sends `σ → 0`: the gap. Volume-uniform because one `ρ'(1)` bounds every `n`. Wraps
`excess_tendsto_zero_of_geom`. -/
theorem gap_of_maximal_correlation {σ : ℕ → ℝ} {ρ₁ : ℝ}
    (hρ0 : 0 ≤ ρ₁) (hρ1 : ρ₁ < 1) (hσnn : ∀ n, 0 ≤ σ n)
    (hsub : ∀ n, σ n ≤ σ 0 * ρ₁ ^ n) :
    Tendsto σ atTop (nhds 0) :=
  excess_tendsto_zero_of_geom hρ0 hρ1 hσnn hsub

/-- **S3 — interior `ρ'(1) < 1` from finite-volume analyticity + a finite grid.** If the single-cut maximal
correlation `ρ'(1)(·)` is `L`-Lipschitz on `[a,b]` (finite-volume analyticity — a bounded connected-correlator
modulus, the §5.1 argument applied to the maximal-correlation functional) and a `δ`-grid certifies
`ρ'(1)(γ) ≤ (1−ε) − L·δ` with strict margin `ε > 0`, then `ρ'(1)(β) < 1` throughout. Reuses
`le_of_lipschitz_grid` (`B = 1 − ε`). The analog of `Interior.interior_confinement_of_analytic_grid` with
`ρ'(1)` in place of `⟨d²⟩`; by RP reversibility this closes the gap uniform in volume. -/
theorem interior_mixing_of_analytic_grid {ρ₁ : ℝ → ℝ} {a b L δ ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε)
    (hlip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |ρ₁ x - ρ₁ y| ≤ L * |x - y|)
    (hcover : ∀ β ∈ Set.Icc a b, ∃ γ ∈ Set.Icc a b, |β - γ| ≤ δ ∧ ρ₁ γ ≤ (1 - ε) - L * δ) :
    ∀ β ∈ Set.Icc a b, ρ₁ β < 1 := by
  intro β hβ
  have h : ρ₁ β ≤ 1 - ε := le_of_lipschitz_grid hL hlip hcover β hβ
  linarith

end MassGap
