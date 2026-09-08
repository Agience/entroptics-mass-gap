import MassGap.Complete

/-!
# MassGap.Interior — the crossover interior from finite-volume analyticity (no `d2_le_bound`)

A1's interior arm — `μYM β < κ₀` on a compact `[a,b]` with `βcYM ≤ a` — reduces to a **β-derivative bound**
on the whitened second moment `⟨d²⟩` (finite-volume analyticity) plus a **finite deterministic grid** of
reads, through the already-proved aperture scaling `Moment.Read.tension_lt_floor_of_lag_moment` and the grid
lemma `Certify.le_of_lipschitz_grid`. It does NOT use the `d2_le_bound` axiom.

The derivative bound is the finite-volume statistical-mechanics fact
`|d⟨d²⟩/dβ| = |Cov_β(⟨d²⟩, S)| ≤ ¼·range(⟨d²⟩)·range(S) = (L/2)²·N_p/2` — the connected correlator of two
bounded observables at finite volume (an established fact, not the `d2_le_bound` axiom). Notes in
`certify/apriori_A1.py`.

After this file, the sole open input of A1-uniform is the intensive margin **U-a** (notes §5.2):
`limsup_L μ(β,L) < κ₀`, consumed by `Certify.gap_uniform_in_volume_of_intensive`.

Imported by the `MassGap` aggregate (`MassGap.lean`).
-/

namespace MassGap

open Set

/-- The whitened lag second moment as a function of β, `⟨d²⟩(β) = ∑_d p_d(β)·d²`. -/
noncomputable def d2 (β : ℝ) : ℝ := ∑ d, pcorrYM β d * (d : ℝ) ^ 2

/-- **Derivative bound ⟹ Lipschitz (finite-volume analyticity).** If `⟨d²⟩` has β-derivative bounded by `L`
on `[a,b]`, it is `L`-Lipschitz there. The derivative bound is the finite-volume fact
`|d⟨d²⟩/dβ| = |Cov_β(⟨d²⟩,S)| ≤ ¼·range(⟨d²⟩)·range(S)`.

API RISK: `Convex.norm_image_sub_le_of_norm_deriv_le` (exact name / argument order / result orientation).
If it differs: use `Convex.lipschitzOnWith_of_nnnorm_deriv_le` then `LipschitzOnWith.dist_le_mul` + `Real.dist_eq`. -/
theorem d2_lipschitz_of_deriv_bound {a b L : ℝ}
    (hdiff : ∀ x ∈ Icc a b, DifferentiableAt ℝ d2 x)
    (hbnd : ∀ x ∈ Icc a b, ‖deriv d2 x‖ ≤ L) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |d2 x - d2 y| ≤ L * |x - y| := by
  intro x hx y hy
  have h := (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le hdiff hbnd hx hy
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  calc |d2 x - d2 y| = |d2 y - d2 x| := abs_sub_comm _ _
    _ ≤ L * |y - x| := h
    _ = L * |x - y| := by rw [abs_sub_comm y x]

/-- **Interior confinement from finite-volume analyticity + a finite grid — no `d2_le_bound`.** On a compact
`[a,b]`: a β-derivative bound `L` on `⟨d²⟩` (finite-volume analyticity) together with a `δ`-grid of
deterministic reads certifying `⟨d²⟩(γ) ≤ 1 − L·δ` give `μYM β < κ₀` throughout — an established external fact
(finite-volume analyticity ⇒ the derivative bound) plus a finite deterministic grid, not the `d2_le_bound`
axiom.

API RISK: `(readYM β).tension_lt_floor_of_lag_moment` must accept `hb` after `unfold d2` (defeq to
`∑ d, pcorrYM β d * d²`); this is the exact call in `Complete.ym_crossover_confinement`. -/
theorem interior_confinement_of_analytic_grid {a b L δ : ℝ} (hL : 0 ≤ L)
    (hdiff : ∀ x ∈ Icc a b, DifferentiableAt ℝ d2 x)
    (hbnd : ∀ x ∈ Icc a b, ‖deriv d2 x‖ ≤ L)
    (hcover : ∀ β ∈ Icc a b, ∃ γ ∈ Icc a b, |β - γ| ≤ δ ∧ d2 γ ≤ 1 - L * δ) :
    ∀ β ∈ Icc a b, μYM β < κ₀YM := by
  intro β hβ
  have hlip := d2_lipschitz_of_deriv_bound hdiff hbnd
  have hb : d2 β ≤ 1 := le_of_lipschitz_grid hL hlip hcover β hβ
  unfold d2 at hb
  unfold μYM κ₀YM
  exact (readYM β).tension_lt_floor_of_lag_moment hb ym_finite_aperture

#print axioms interior_confinement_of_analytic_grid
-- Expected: the three foundational + `wilson_reflection_positive` (via `readYM`), and NOT `d2_le_bound`.

/-! ## The sole open core, as a named target (U-a)

After `interior_confinement_of_analytic_grid` closes the fixed-volume interior and the two ends are cited
(`ym_character`, `ym_asymfree`), the whole of A1-uniform reduces to ONE intensive inequality:

> **U-a.** `∃ r < 1, ∀ F, m_hi(F) ≤ r` — the dominant transfer magnitude stays below one uniformly in the
> volume `F = L^d` (equivalently `limsup_L μ(·,L) < κ₀`, a margin that does not dilute as `a → 0`).

It is the single hypothesis `hbound` of `Certify.gap_uniform_in_volume_of_intensive`, which then yields the
uniform-in-volume gap. `κ₀ = ¼log3` is per-area and `L`-independent (`Floor`, proved); U-a is the intensive
self-sourcing contraction `c > 0` (notes §5.2).

**The radius is now grounded.** `CellSpectrum.gap_uniform_of_cell_intensive` pins the U-a radius `r` to the
machine-checked single-cell ceiling `3^{-1/4} = e^{-κ₀}` — the value `Hcell2_clears_floor` proves the single
plaquette clears at every coupling. So the remaining input sharpens from "some `r < 1`" to the intensivity bound
`∀ F, m_hi(F) ≤ 3^{-1/4}` (adding volume does not raise the dominant magnitude above the single plaquette), and
everything downstream — the F-uniform gap — follows by machine check, foundational axioms only. -/

end MassGap
