import MassGap.Complete

/-!
# MassGap.Interior — a substrate bound on a compact coupling interval, from a finite grid

`Complete.confinement_of_substrate_bound` consumes an aperture-independent bound on the lag second
moment `⟨d²⟩` and returns confinement at every large enough aperture. This module supplies such a
bound on a compact interval `[a,b]` from finitely many deterministic reads together with a Lipschitz
constant, via `Certify.le_of_lipschitz_grid`.

The Lipschitz constant is the finite-volume statistical-mechanics identity
`d⟨d²⟩/dβ = −Cov_β(⟨d²⟩, S)`, which `WilsonAnalytic` proves and bounds: `cov_bound_extensive` gives
an `O(#Plaq)` bound with no further hypothesis, and `cov_bound_local` / `cov_bound_summable` give a
volume-independent one under clustering.

The bound `B`, the aperture `N`, the Lipschitz constant `L` and the grid spacing `δ` are parameters
of every declaration here; no value is fixed. Both theorems are stated at one fixed aperture `N`,
for the coupling range `Icc a b` only.

DERIVED: no numeral is fixed in this module.
-/

namespace MassGap

open Set

/-- The substrate's lag second moment through an aperture of size `N`, as a function of the
coupling: a definitional alias for `Complete.d2At N β`, with `β` as the moving argument so that the
grid and Lipschitz lemmas below can speak about `d2 N : ℝ → ℝ`.

DERIVED: no numeral appears in the statement. -/
noncomputable def d2 (N : ℕ) (β : ℝ) : ℝ := d2At N β

/-- A derivative bound on `Icc a b` gives a Lipschitz bound there. If `d2 N` is differentiable at
every point of `Icc a b` and `‖deriv (d2 N) x‖ ≤ L` at every such point, then
`|d2 N x − d2 N y| ≤ L * |x − y|` for all `x, y ∈ Icc a b`. Proved from
`Convex.norm_image_sub_le_of_norm_deriv_le` on `convex_Icc a b`.

`L` is not assumed nonnegative; the derivative bound forces `0 ≤ L` whenever `Icc a b` is nonempty.
Differentiability and a value for `L` are hypotheses here, not results: for `⟨d²⟩` they come from
`WilsonAnalytic.wilsonSystem_expect_hasDerivAt`, which identifies the derivative as `−Cov_β(·, S)`,
and from `cov_bound_local` or `cov_bound_extensive`, which bound that covariance.

DERIVED: no numeral appears in the statement. -/
theorem d2_lipschitz_of_deriv_bound {N : ℕ} {a b L : ℝ}
    (hdiff : ∀ x ∈ Icc a b, DifferentiableAt ℝ (d2 N) x)
    (hbnd : ∀ x ∈ Icc a b, ‖deriv (d2 N) x‖ ≤ L) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |d2 N x - d2 N y| ≤ L * |x - y| := by
  intro x hx y hy
  have h := (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le hdiff hbnd hx hy
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  calc |d2 N x - d2 N y| = |d2 N y - d2 N x| := abs_sub_comm _ _
    _ ≤ L * |y - x| := h
    _ = L * |x - y| := by rw [abs_sub_comm y x]

/-- A bound on `⟨d²⟩` across a compact coupling interval, from finitely many reads. The hypotheses
are `0 ≤ L`, differentiability of `d2 N` on `Icc a b`, the derivative bound `‖deriv (d2 N) x‖ ≤ L`
there, and a cover `hcover`: every `β ∈ Icc a b` admits some `γ ∈ Icc a b` with `|β − γ| ≤ δ` whose
read satisfies `d2 N γ ≤ B − L * δ`. The conclusion is `d2 N β ≤ B` for every `β ∈ Icc a b`. It is
`Certify.le_of_lipschitz_grid` applied to the Lipschitz bound `d2_lipschitz_of_deriv_bound`
supplies.

The aperture `N` is fixed throughout and the conclusion covers `Icc a b` only; `B`, `L` and `δ` are
the caller's. Supplying this at every `N` with a single `B` is the hypothesis of
`Complete.confinement_of_bounded_substrate`.

DERIVED: the only numeral in the statement is the `0` in `0 ≤ L`, the sign condition
`le_of_lipschitz_grid` asks of a Lipschitz constant. -/
theorem d2_le_of_analytic_grid {N : ℕ} {a b B L δ : ℝ} (hL : 0 ≤ L)
    (hdiff : ∀ x ∈ Icc a b, DifferentiableAt ℝ (d2 N) x)
    (hbnd : ∀ x ∈ Icc a b, ‖deriv (d2 N) x‖ ≤ L)
    (hcover : ∀ β ∈ Icc a b, ∃ γ ∈ Icc a b, |β - γ| ≤ δ ∧ d2 N γ ≤ B - L * δ) :
    ∀ β ∈ Icc a b, d2 N β ≤ B :=
  le_of_lipschitz_grid hL (d2_lipschitz_of_deriv_bound hdiff hbnd) hcover

#print axioms d2_le_of_analytic_grid

end MassGap
