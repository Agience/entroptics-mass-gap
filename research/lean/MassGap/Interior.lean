import MassGap.Complete

/-!
# MassGap.Interior — a substrate bound on a compact coupling interval, from a finite grid

`Complete.confinement_of_substrate_bound` turns one aperture-independent bound on the lag second
moment `⟨d²⟩` into confinement at every large enough aperture. This module supplies such a bound on a
compact interval `[a,b]` from finitely many deterministic reads plus a Lipschitz constant, via
`Certify.le_of_lipschitz_grid`.

The Lipschitz constant is the finite-volume statistical-mechanics fact
`|d⟨d²⟩/dβ| = |Cov_β(⟨d²⟩, S)|`, which `WilsonAnalytic` proves and bounds: `cov_bound_extensive` gives
the assumption-free `O(#Plaq)`, and `cov_bound_local` / `cov_bound_summable` give a volume-independent
one under clustering.

Nothing here fixes a bound, an aperture, or a grid spacing: `B`, `N`, `L` and `δ` are all parameters,
and the conclusion is stated for whatever the caller measures.
-/

namespace MassGap

open Set

/-- The substrate's lag second moment through an aperture of size `N`, as a function of the coupling.
This is `Complete.d2At`, named here because the grid argument treats it as a function of `β`. -/
noncomputable def d2 (N : ℕ) (β : ℝ) : ℝ := d2At N β

/-- **Derivative bound ⟹ Lipschitz (finite-volume analyticity).** If `⟨d²⟩` has β-derivative bounded
by `L` on `[a,b]`, it is `L`-Lipschitz there. `WilsonAnalytic.wilsonSystem_expect_hasDerivAt` proves
the derivative exists and equals `−Cov_β(·, S)`; `cov_bound_local` bounds it without the volume. -/
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

/-- **A substrate bound on a compact interval, from a finite grid.** A Lipschitz constant `L` on
`⟨d²⟩` together with a `δ`-grid of deterministic reads each clearing `B − L·δ` gives `⟨d²⟩ ≤ B`
throughout `[a,b]`.

`B`, `L`, `δ` and the aperture `N` are all the caller's: nothing is fixed here. Supplying this at
every `N` with one `B` is exactly the hypothesis of `Complete.confinement_of_bounded_substrate`. -/
theorem d2_le_of_analytic_grid {N : ℕ} {a b B L δ : ℝ} (hL : 0 ≤ L)
    (hdiff : ∀ x ∈ Icc a b, DifferentiableAt ℝ (d2 N) x)
    (hbnd : ∀ x ∈ Icc a b, ‖deriv (d2 N) x‖ ≤ L)
    (hcover : ∀ β ∈ Icc a b, ∃ γ ∈ Icc a b, |β - γ| ≤ δ ∧ d2 N γ ≤ B - L * δ) :
    ∀ β ∈ Icc a b, d2 N β ≤ B :=
  le_of_lipschitz_grid hL (d2_lipschitz_of_deriv_bound hdiff hbnd) hcover

#print axioms d2_le_of_analytic_grid

end MassGap
