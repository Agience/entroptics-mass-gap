import MassGap.Complete

/-!
# MassGap.Interior — a substrate bound on a compact coupling interval, from a finite grid

`Complete.confinement_of_bounded_substrate` consumes an aperture-independent bound on the second
moment `d2At` about the circle distance and returns confinement at every large enough aperture. This
module supplies such a bound at one aperture on a compact interval `[a,b]` from finitely many reads
together with a Lipschitz constant, via `Certify.le_of_lipschitz_grid`, and feeds it to the sharp
criterion (`ym_crossover_confinement_of_grid_sharp`) and to the model
(`ym_mass_gap_grid_certified_sharp`, at the extent-`16` read `d2At 15`, the functional the grid
script computes; the object it is computed on differs, see that theorem).

Differentiability of `d2At N` and the Lipschitz constant `L` are hypotheses throughout; no theorem
in the development supplies either. `WilsonAnalytic.wilsonSystem_expect_hasDerivAt` identifies the
coupling derivative of a single Gibbs expectation as `−Cov_β(·, S)`, and `cov_bound_extensive` bounds
such a covariance by an `O(#Plaq)` constant, `cov_bound_local` / `cov_bound_summable` by a
volume-independent one under clustering. `d2At N` is not a single expectation: it is
`∑_d ρ_d circLag(d)² / ∑_d ρ_d` with each `ρ_d` a connected correlator, so its derivative is a
quotient-rule combination of such covariances, and the clamp `max β 0` in `readYMAt` leaves it
unconstrained at `β = 0`.

The bound `B`, the Lipschitz constant `L` and the grid spacing `δ` are parameters of every
declaration here. Every theorem is stated at one fixed aperture, for the coupling range `Icc a b`
only; the aperture is the variable `N` except in `ym_mass_gap_grid_certified_sharp`, which pins it to
`15` (periodic extent `16`), the extent of the ensembles the grid data is read from.
-/

namespace MassGap

open Set

/-- The substrate's second moment about the circle distance (`Moment.circLag`) through an aperture of
size `N`, i.e. on the periodic extent `N + 1`, as a function of the coupling: a definitional alias for
`Complete.d2At N β`, with `β` as the moving argument so that the grid and Lipschitz lemmas below can
speak about `d2 N : ℝ → ℝ`.

DERIVED: no numeral appears in the statement. -/
noncomputable def d2 (N : ℕ) (β : ℝ) : ℝ := d2At N β

/-- A derivative bound on `Icc a b` gives a Lipschitz bound there. If `d2 N` is differentiable at
every point of `Icc a b` and `‖deriv (d2 N) x‖ ≤ L` at every such point, then
`|d2 N x − d2 N y| ≤ L * |x − y|` for all `x, y ∈ Icc a b`. Proved from
`Convex.norm_image_sub_le_of_norm_deriv_le` on `convex_Icc a b`.

`L` is not assumed nonnegative; the derivative bound forces `0 ≤ L` whenever `Icc a b` is nonempty.
Differentiability and a value for `L` are hypotheses here, not results, and nothing in the
development discharges them for `d2 N`: `WilsonAnalytic.wilsonSystem_expect_hasDerivAt` and the
`cov_bound_*` lemmas speak about a single Gibbs expectation, while `d2 N` is a ratio of connected
correlators (see the module header).

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

/-- Interior confinement from a finite grid, stated on the circle-distance moment under the sharp
ceiling. At one aperture `N` (periodic extent `N + 1`) and on `Icc a b`: if `d2At N` is
differentiable there with `‖deriv (d2At N)‖ ≤ L` (`hdiff`, `hbnd`), and every coupling of the
interval lies within `δ` of a coupling `γ` of the interval with `d2At N γ ≤ B - L * δ` (`hcover`),
and `B` sits under the sharp ceiling `substrateThreshold · (N+1)² = arccos(3^{−1/4})²(N+1)²/(2π)²`
(`haperture`), then `μYMAt N β < κ₀YM` at every `β ∈ Icc a b`.

It is `d2_le_of_analytic_grid` followed by `Complete.confinement_at_of_d2_sharp`. Every hypothesis
is about `d2At N`, the moment of `readYMAt N β` against `Moment.circLag d = min d (N+1−d)`. That is
the functional `certify/ym_crossover_confinement_of_grid.py` computes in `d2_from_profiles` (the half
profile mirrored round the circle, normalised to total weight one) — the same lag arity, distance and
normalisation. The object it is evaluated on is not the same: `d2At` reads the `SU(3)` correlation of
one `(0,1)` plaquette along one transverse axis on the periodic `(N+1)⁴` lattice
(`WilsonBridge.corrClay`), while the script reads `SU(2)` `16³×32` ensembles, a site field summed over
all planes, averaged over three spatial axes, connected against a sample mean and clipped at zero, and
bounds it statistically (nominal empirical-Bernstein), not deterministically. At `N = 15` the ceiling
is `3.2480…`.

What the grid data does and does not supply. `hcover` asks for `d2At N γ ≤ B − L·δ` at grid points
at most `δ` from every coupling of the interval, with `L` the derivative bound. The `13`-point grid of
`data/9_1_dat_d2_certified.csv` has largest gap `0.3`, so `δ ≥ 0.15`, and its largest upper
(`99.9999%`) is `1.3712`, so `L ≤ (3.2480 − 1.3712)/0.15 ≈ 12.5` would be needed. No derivative
bound for `d2At` is proved (module header), and the finite-volume covariance constants in the
development are of order `10⁶`–`10⁷` at extent `16`, so that grid cannot meet `hcover`; `L` and
`δ` are left free so that the requirement `L·δ ≤ B − max_γ d2At N γ` is explicit.

DERIVED: `0 ≤ L` is the sign condition `le_of_lipschitz_grid` asks of a Lipschitz constant;
`((N : ℝ) + 1) ^ 2` is the periodic extent squared, the aperture factor of
`Complete.confinement_at_of_d2_sharp` (the `1` the lag arity's successor, the `2` the second
moment's exponent). `B`, `L`, `δ`, `a`, `b` and `N` are variables. -/
theorem ym_crossover_confinement_of_grid_sharp {N : ℕ} {a b B L δ : ℝ} (hL : 0 ≤ L)
    (haperture : B < substrateThreshold * ((N : ℝ) + 1) ^ 2)
    (hdiff : ∀ x ∈ Icc a b, DifferentiableAt ℝ (d2At N) x)
    (hbnd : ∀ x ∈ Icc a b, ‖deriv (d2At N) x‖ ≤ L)
    (hcover : ∀ β ∈ Icc a b, ∃ γ ∈ Icc a b, |β - γ| ≤ δ ∧ d2At N γ ≤ B - L * δ) :
    ∀ β ∈ Icc a b, μYMAt N β < κ₀YM :=
  fun β hβ =>
    confinement_at_of_d2_sharp haperture
      (d2_le_of_analytic_grid (N := N) hL hdiff hbnd hcover β hβ)

#print axioms ym_crossover_confinement_of_grid_sharp

/-- Gap, non-triviality and `SO(4)` for `ymModelAt 15` — the model read on the periodic extent `16`,
the spatial extent of the ensembles the grid data comes from — with the interior discharged by a
grid on `d2At 15`, the functional that data computes. The hypotheses are:

* `hstrong`: `μYMAt 15 β < κ₀YM` for `β < a`, and `hweak`: the same for `b < β` — the two ends,
  bare hypotheses as in `ym_A1_of_grid`;
* `hL`, `hdiff`, `hbnd`, `hcover`: the grid on `Icc a b` for the circle-distance moment `d2At 15`,
  exactly as in `ym_crossover_confinement_of_grid_sharp`;
* `haperture`: `B < substrateThreshold · 16² = arccos(3^{−1/4})² · 16² / (2π)² = 3.2480…`, the sharp
  ceiling at extent `16`.

The interior is not a hypothesis here: it is produced by `ym_crossover_confinement_of_grid_sharp`
from the grid hypotheses, and the three pieces are assembled into `A1_YM (ymModelAt 15)` by the same
case split as `ym_A1_of_grid`. The interval `[a,b]` is the caller's and nothing ties it to the
measured couplings: with `a > b` the grid hypotheses are empty and `hstrong` and `hweak` carry
`A1` alone, so the grid carries exactly as much of the coupling line as `[a,b]` covers. Of the grid
hypotheses, `hdiff` and `hbnd` are proved nowhere, and `hcover` is the one the `13`-point grid cannot
meet (see `ym_crossover_confinement_of_grid_sharp`, which also lists how the measured object differs
from `d2At 15`).

DERIVED: `15` is the aperture index of a periodic extent of `16` sites — `Fin (15 + 1)` indexes lags
`0 … 15` — and `16` in `(16 : ℝ) ^ 2` is that extent, the `(N + 1)` of
`ym_crossover_confinement_of_grid_sharp`'s ceiling at `N = 15`; the `2` is the second moment's
exponent. `0 ≤ L` is the sign of a Lipschitz constant, and the `0` of `nhds 0` and `< 0` is the
limit and the sign of the non-triviality clause. CHOSEN: extent `16` is the spatial extent of the
`L16` ensembles `certify/ym_crossover_confinement_of_grid.py` reads. -/
theorem ym_mass_gap_grid_certified_sharp {a b B L δ : ℝ}
    (hstrong : ∀ β, β < a → μYMAt 15 β < κ₀YM)
    (hL : 0 ≤ L)
    (haperture : B < substrateThreshold * (16 : ℝ) ^ 2)
    (hdiff : ∀ x ∈ Icc a b, DifferentiableAt ℝ (d2At 15) x)
    (hbnd : ∀ x ∈ Icc a b, ‖deriv (d2At 15) x‖ ≤ L)
    (hcover : ∀ β ∈ Icc a b, ∃ γ ∈ Icc a b, |β - γ| ≤ δ ∧ d2At 15 γ ≤ B - L * δ)
    (hweak : ∀ β, b < β → μYMAt 15 β < κ₀YM) :
    (∀ β, Filter.Tendsto
        (fun τ => ‖∑ k ∈ (ymModelAt 15).s β,
          (ymModelAt 15).P β k * ((ymModelAt 15).m β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
      (∀ β, (ymModelAt 15).μ β - (ymModelAt 15).κ < 0) ∧
      (∀ d d', (ymModelAt 15).R d = (ymModelAt 15).R d') := by
  have hap : B < substrateThreshold * (((15 : ℕ) : ℝ) + 1) ^ 2 :=
    haperture.trans_eq (by norm_num)
  have hint := ym_crossover_confinement_of_grid_sharp (N := 15) hL hap hdiff hbnd hcover
  refine mass_gap_of_model (ymModelAt 15) ?_ (ym_A2_at 15)
  show ∀ β, μYMAt 15 β < κ₀YM
  intro β
  rcases lt_or_ge β a with h | h
  · exact hstrong β h
  · rcases le_or_gt β b with h2 | h2
    · exact hint β ⟨h, h2⟩
    · exact hweak β h2

#print axioms ym_mass_gap_grid_certified_sharp

end MassGap
