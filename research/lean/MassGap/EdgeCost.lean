import Mathlib
import MassGap.NonAbelianForget
import MassGap.AsymptoticScaling

/-!
# MassGap.EdgeCost — why a flux edge costs the same per unit length at every zoom

The author's chain: a fixed aperture reads an infinite substrate; finite information; flux edges cost `σ` per
unit length (`NonAbelianForget.ConfinedEdges`, `NonAbelianForget.edge_mass`: `σ > h` at every zoom,
uniform, gives one physical mass); hence a gap. The open step is why `σ` stays positive and the same at
every zoom in 4D `SU(N)`, although zooming in weakens the coupling. This module evaluates three proposed
reasons and proves what each one supplies.

## 1. Fixed by the aperture

`sigmaPhys σlat a β = σlat β / a β²`: the lattice string tension at coupling `β` in the units of the
aperture, `a β` the spacing.

* `area_exponent_phys`: an area law `σlat · (R/a)(T/a)` over a loop of physical sides `R × T` read at
  spacing `a` is `sigmaPhys · R T`. This is the units step and holds by construction.
* `aperture_reading_const_iff`: the area-law reading of every fixed physical loop is the same at every
  coupling iff `sigmaPhys` is the same constant at every coupling.
* `creutz_cancels`, `creutz_phys`, `creutz_reading_const_iff`: with a perimeter term `p (R + T)` and a
  constant, the Creutz combination of four loops cancels both and returns `σlat δ²`; at physical sides it
  returns `sigmaPhys · δ²`. So the aperture's Creutz reading at fixed physical `δ` is zoom-independent iff
  `sigmaPhys` is. The Wilson loop itself is not (argued, not formalised): its perimeter coefficient in
  physical units is `p/a`, the static self-energy. The model takes `p`, `c` independent of loop size.
* `spacing_from_sigma_is_vacuous`: if the spacing is set from the string tension itself
  (`a := √(σlat/σ₀)`), `sigmaPhys ≡ σ₀` for every positive `σlat`. Read this way "by construction" is
  circular: it fixes the unit and asserts nothing about the measure.
* `StringScalingAt N σlat`: `sigmaPhys σlat (aRun N) → σ₀ > 0` against the fixed two-loop spacing
  `AsymptoticScaling.aRun N`. `stringScaling_satisfiable` (`σlat = c · aRun²`) and
  `bounded_sigma_fails_scaling` (a lattice tension bounded below fails it) show it is a constraint on the
  measure. `stringScaling_sqrt`: it gives `AsymptoticScalingAt N √σlat`, the mass-scaling predicate
  already in the tree.
* `sigmaPhys_heatKernel`: the 2D test. The heat-kernel action has `σlat = (g² C/2) a²` at every spacing
  (input from the exact solution of 2D Yang–Mills, not derived here), so `sigmaPhys = g² C/2` at every
  zoom. For the 2D Wilson action the same constancy holds only in the limit: at `g = 1`, `C_F = 3/4`,
  `σlat = −log(I₂(β)/I₁(β))`, `β = 4/a²`, `sigmaPhys = 0.4185, 0.3869, 0.3779, 0.3755, 0.37502` at
  `a = 1, 1/2, 1/4, 1/10, 1/50`, against `3/8` (numerical, not formalised). In 4D there is no exact
  solution and no such test.
* `edgeRate_le_of_sigma_ge`: what `ConfinedEdges` needs from the tension is a lower bound
  `inf_k sigmaPhys k > h`, not equality across zooms.

## 2. Non-abelian self-cost

`invCoup b₀ r₀ u₀ r = u₀ − 2 b₀ log(r/r₀)`: the one-loop inverse coupling `1/g²(r)` at distance `r`, from
`1/g²(r₀) = u₀`, for `μ dg/dμ = −b₀ g³`.

* `invCoup_strictAntiOn`: for `b₀ > 0` the coupling grows with distance (asymptotic freedom).
  `invCoup_abelian`: at `b₀ = 0` (pure `U(1)`) it is constant.
* `rStar b₀ r₀ u₀ us = r₀ exp((u₀ − us)/(2b₀))`, `invCoup_rStar`: the distance at which `1/g² = us`.
  `rStar_rg_invariant`: it does not depend on the reference point along the one-loop flow. This is
  dimensional transmutation: a physical length fixed by a dimensionless coupling, the same at every
  cutoff on the flow. `rStar_shift`: the lengths for two target couplings differ by a fixed factor, so
  the flow generates one scale.
* `spacing_of_rStar`: `r₀ = rStar · exp(−(u₀ − us)/(2b₀))` (the one-loop form of the spacing at fixed
  physical length; its identification with `aRun`'s coupling normalisation is not proved here).
  `rStar_ratio_tendsto`: the transmuted length in units of the cutoff tends to infinity as the coupling
  at the cutoff tends to zero.
* `abelian_no_scale`, `abelian_dilation`: at `b₀ = 0` no distance reaches any other coupling and the flow
  is dilation invariant; `invCoup_dilation`: at `b₀ ≠ 0` a dilation by `s` shifts `1/g²` by `−2b₀ log s`.
  Only the non-abelian running generates a length.
* `vPert C b₀ r₀ u₀ r = −C/(4π r · invCoup r)`: the RG-improved Coulomb potential `−C_F g²(r)/(4π r)`.
  `invCoup_pos_iff`: the perturbative coupling is positive exactly for `r < rStar b₀ r₀ u₀ 0` (the
  Landau length `1/Λ`). `vPert_neg_on_domain`: the perturbative potential lives on that bounded range,
  so it cannot supply the linear coefficient `lim_{r→∞} V(r)/r`. On its range the force `dV/dr` is
  positive and grows toward `1/Λ` (argued): the self-interaction does make the edge stiffen with
  length, but at every finite order the potential is Coulomb times powers of `g²(r)`, with no
  `r`-linear term, and the expansion stops at `1/Λ`.

## 3. Edges cannot end

* `scalar_mem_SU`: `ω · 1 ∈ SU(N)` for `ωᴺ = 1`. `scalar_fundamental`: it acts on the fundamental by `ω`.
* `centre_adjoint_trivial`: every element of the centre of `SU(N)` acts trivially by conjugation, so
  gluons carry no centre charge (N-ality `0`).
* `centre_fundamental_nontrivial`: for `N ≥ 2` some central element moves every nonzero fundamental
  vector, so a fundamental endpoint is not centre-neutral.
* `centre_phase`, `edge_can_end_iff`: the phase `ωᵏ (ω · star ω)ᵐ` of the primitive centre element
  (read on `k` fundamentals and `m` adjoints; the tensor action is interpretation) is `1` iff `N ∣ k`.
  So an endpoint is centre-neutral only if `N ∣ k`: a fundamental edge cannot end on gluons, `N`
  fundamental edges can meet at a junction, and adjoint edges are allowed by the centre to end (that
  they break is dynamical, not proved). Prose: with `NonAbelianForget.NoAbelianSector` (finite centre)
  the conserved flux is a residue mod `N`; at `U(1)` (infinite centre) it would be an integer.

## The combination

(2) supplies the fixed physical length that (1) presupposes (`rStar_rg_invariant`) and shows that the
one-loop flow has only one (`rStar_shift`; none at `b₀ = 0`, `abelian_no_scale`); (3) says which edges
the cost can attach to. None of the three proves that
`sigmaPhys` has a positive limit: `StringScalingAt N σlat` for the 4D `SU(N)` Wilson measure, with `σlat`
the area-law coefficient of that measure, is the remaining statement. It is the continuum limit of the
area law, i.e. confinement.

DERIVED (module-wide): `2` in `a²` the dimension of an area; `2` and `4π` in `invCoup`, `vPert` the
one-loop normalisation `μ dg/dμ = −b₀g³` and the Coulomb kernel `1/(4πr)`; `1` the shift in
`exp x ≥ x + 1`; `0` the sign conditions.
-/

namespace MassGap.EdgeCost

open Filter Topology
open MassGap.AsymptoticScaling

/-! ## 1. Fixed by the aperture -/

section Aperture

/-- The lattice string tension `σlat β` in aperture units, `a β` the spacing at coupling `β`.

DERIVED: `2` the dimension of an area. -/
noncomputable def sigmaPhys (σlat a : ℝ → ℝ) (β : ℝ) : ℝ := σlat β / a β ^ 2

/-- **Units.** The lattice area-law exponent of a loop of physical sides `R × T`, read at spacing `a`,
is the physical tension times the physical area. -/
theorem area_exponent_phys {σlat a R T : ℝ} (ha : a ≠ 0) :
    σlat * (R / a) * (T / a) = σlat / a ^ 2 * (R * T) := by
  field_simp

/-- **The area-law reading of every fixed physical loop is zoom-independent iff the physical tension
is.** -/
theorem aperture_reading_const_iff {σlat a : ℝ → ℝ} (ha : ∀ β, a β ≠ 0) (σ₀ : ℝ) :
    (∀ β R T : ℝ, Real.exp (-(σlat β * (R / a β) * (T / a β))) = Real.exp (-(σ₀ * (R * T)))) ↔
      ∀ β, sigmaPhys σlat a β = σ₀ := by
  constructor
  · intro h β
    have h1 := h β 1 1
    rw [Real.exp_eq_exp, area_exponent_phys (ha β)] at h1
    simp only [mul_one, neg_inj] at h1
    exact h1
  · intro h β R T
    rw [area_exponent_phys (ha β)]
    exact congrArg (fun s => Real.exp (-(s * (R * T)))) (h β)

/-- `−log W` of an `R × T` loop with area, perimeter and constant terms. -/
def minusLogW (s p c R T : ℝ) : ℝ := s * (R * T) + p * (R + T) + c

/-- **The Creutz combination cancels perimeter and constant.**

DERIVED: `2` the area dimension of `δ²`. -/
theorem creutz_cancels (s p c R T δ : ℝ) :
    minusLogW s p c R T + minusLogW s p c (R - δ) (T - δ) - minusLogW s p c R (T - δ)
      - minusLogW s p c (R - δ) T = s * δ ^ 2 := by
  unfold minusLogW; ring

/-- **The Creutz reading at physical sides is the physical tension times `δ²`**, whatever the
lattice perimeter coefficient `p`. -/
theorem creutz_phys (s p c a R T δ : ℝ) :
    minusLogW s p c (R / a) (T / a) + minusLogW s p c ((R - δ) / a) ((T - δ) / a)
      - minusLogW s p c (R / a) ((T - δ) / a) - minusLogW s p c ((R - δ) / a) (T / a)
      = s / a ^ 2 * δ ^ 2 := by
  unfold minusLogW; ring

/-- **The aperture's Creutz reading at a fixed physical `δ ≠ 0` is zoom-independent iff the physical
tension is.** -/
theorem creutz_reading_const_iff {σlat p c a : ℝ → ℝ} {R T δ : ℝ} (hδ : δ ≠ 0) (σ₀ : ℝ) :
    (∀ β, minusLogW (σlat β) (p β) (c β) (R / a β) (T / a β)
        + minusLogW (σlat β) (p β) (c β) ((R - δ) / a β) ((T - δ) / a β)
        - minusLogW (σlat β) (p β) (c β) (R / a β) ((T - δ) / a β)
        - minusLogW (σlat β) (p β) (c β) ((R - δ) / a β) (T / a β) = σ₀ * δ ^ 2) ↔
      ∀ β, sigmaPhys σlat a β = σ₀ :=
  forall_congr' fun β => by
    rw [creutz_phys]
    exact mul_left_inj' (pow_ne_zero 2 hδ)

/-- **Setting the spacing from the tension makes the statement empty.** For every positive lattice
tension, `a := √(σlat/σ₀)` gives `sigmaPhys ≡ σ₀`. -/
theorem spacing_from_sigma_is_vacuous {σlat : ℝ → ℝ} (hσ : ∀ β, 0 < σlat β) {σ₀ : ℝ}
    (h0 : 0 < σ₀) : ∃ a : ℝ → ℝ, (∀ β, 0 < a β) ∧ ∀ β, sigmaPhys σlat a β = σ₀ := by
  refine ⟨fun β => Real.sqrt (σlat β / σ₀), fun β => Real.sqrt_pos.2 (div_pos (hσ β) h0),
    fun β => ?_⟩
  have hne := (hσ β).ne'
  have hne0 := h0.ne'
  simp only [sigmaPhys]
  rw [Real.sq_sqrt (div_pos (hσ β) h0).le]
  field_simp

/-- **String-tension scaling against the fixed two-loop spacing**: `σlat/aRun²` has a positive
limit. -/
def StringScalingAt (N : ℕ) (σlat : ℝ → ℝ) : Prop :=
  ∃ σ₀ : ℝ, 0 < σ₀ ∧ Tendsto (sigmaPhys σlat (aRun N)) atTop (nhds σ₀)

/-- `σlat = c · aRun²` satisfies it. -/
theorem stringScaling_satisfiable {N : ℕ} (hN : 1 ≤ N) {c : ℝ} (hc : 0 < c) :
    StringScalingAt N (fun β => c * aRun N β ^ 2) := by
  refine ⟨c, hc, ?_⟩
  have heq : sigmaPhys (fun β => c * aRun N β ^ 2) (aRun N) =ᶠ[atTop] fun _ => c := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    simp only [sigmaPhys]
    exact mul_div_cancel_right₀ _ (pow_ne_zero 2 (aRun_pos hN hβ).ne')
  exact Tendsto.congr' heq.symm tendsto_const_nhds

/-- **A lattice tension bounded below fails it.** -/
theorem bounded_sigma_fails_scaling {N : ℕ} (hN : 1 ≤ N) {σlat : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hbdd : ∀ᶠ β in atTop, c ≤ σlat β) : ¬ StringScalingAt N σlat := by
  rintro ⟨σ₀, hσ₀, hlim⟩
  have hub : ∀ᶠ β in atTop, sigmaPhys σlat (aRun N) β < σ₀ + 1 :=
    hlim.eventually (gt_mem_nhds (by linarith))
  have hσ1 : (0 : ℝ) < σ₀ + 1 := by linarith
  have hε0 : 0 < min 1 (c / (σ₀ + 1)) := lt_min one_pos (div_pos hc hσ1)
  obtain ⟨β₀, hβ₀⟩ := Filter.eventually_atTop.mp (hbdd.and hub)
  obtain ⟨β, hβ, hβpos, hlt⟩ := exists_beta_aRun_lt hN hε0 β₀
  obtain ⟨hb, hu⟩ := hβ₀ β hβ.le
  have ha := aRun_pos hN hβpos
  have hu' : σlat β < (σ₀ + 1) * aRun N β ^ 2 := by
    simp only [sigmaPhys] at hu
    rwa [div_lt_iff₀ (by positivity)] at hu
  have hε1 : min 1 (c / (σ₀ + 1)) ≤ 1 := min_le_left _ _
  have hε2 : min 1 (c / (σ₀ + 1)) ≤ c / (σ₀ + 1) := min_le_right _ _
  have hsq : aRun N β ^ 2 < c / (σ₀ + 1) := by
    nlinarith [mul_pos ha (sub_pos.2 hlt)]
  rw [lt_div_iff₀ hσ1] at hsq
  nlinarith

/-- **String-tension scaling is mass scaling of `√σ`**: it gives `AsymptoticScalingAt N √σlat`. -/
theorem stringScaling_sqrt {N : ℕ} (hN : 1 ≤ N) {σlat : ℝ → ℝ} (h : StringScalingAt N σlat) :
    AsymptoticScalingAt N (fun β => Real.sqrt (σlat β)) := by
  obtain ⟨σ₀, hσ₀, hlim⟩ := h
  refine ⟨Real.sqrt σ₀, Real.sqrt_pos.2 hσ₀, ?_⟩
  have heq : (fun β => Real.sqrt (sigmaPhys σlat (aRun N) β)) =ᶠ[atTop]
      fun β => Real.sqrt (σlat β) / aRun N β := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    have ha := aRun_pos hN hβ
    simp only [sigmaPhys]
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq ha.le]
  exact ((Real.continuous_sqrt.tendsto σ₀).comp hlim).congr' heq

/-- **2D heat-kernel action**: `σlat = (g² C/2) a²` at every spacing gives `sigmaPhys = g² C/2` at
every zoom. The form of `σlat` is the exact solution of 2D Yang–Mills, taken as input.

DERIVED: `2` the heat-kernel exponent `g² C₂ A/2` and the area dimension. -/
theorem sigmaPhys_heatKernel {a : ℝ → ℝ} (ha : ∀ β, a β ≠ 0) (gsq C β : ℝ) :
    sigmaPhys (fun β => gsq * C / 2 * a β ^ 2) a β = gsq * C / 2 :=
  mul_div_cancel_right₀ _ (pow_ne_zero 2 (ha β))

/-- **A lower bound on the tension is what the edge rate needs.** `σ₀ ≤ σ` and `slab ≥ 0` give
`edgeRate σ h slab ≤ edgeRate σ₀ h slab`; with `h < σ₀` and `slab > 0` the right side is `< 1`
(`uniform_edgeRate`). -/
theorem edgeRate_le_of_sigma_ge {σ σ₀ h slab : ℝ} (hσ : σ₀ ≤ σ) (hs : 0 ≤ slab) :
    NonAbelianForget.edgeRate σ h slab ≤ NonAbelianForget.edgeRate σ₀ h slab := by
  unfold NonAbelianForget.edgeRate
  exact Real.exp_le_exp.2 (by nlinarith)

/-- **A zoom-uniform lower bound on the physical tension gives a zoom-uniform edge rate below one.**
This is the rate half of `ConfinedEdges`; the minorisation and the edge expansion are not built here. -/
theorem uniform_edgeRate {σk : ℕ → ℝ} {σ₀ h slab : ℝ} (hlow : ∀ k, σ₀ ≤ σk k) (hσ : h < σ₀)
    (hs : 0 < slab) : ∃ q : ℝ, q < 1 ∧ ∀ k, NonAbelianForget.edgeRate (σk k) h slab ≤ q :=
  ⟨_, NonAbelianForget.edgeRate_lt_one hσ hs, fun k => edgeRate_le_of_sigma_ge (hlow k) hs.le⟩

end Aperture

/-! ## 2. Non-abelian self-cost -/

section Running

/-- One-loop inverse coupling `1/g²(r)` at distance `r`, from `1/g²(r₀) = u₀`, for `μ dg/dμ = −b₀ g³`
(`d(1/g²)/d log μ = 2 b₀`, `μ = 1/r`).

DERIVED: `2` from `d(g⁻²) = −2 g⁻³ dg`. -/
noncomputable def invCoup (b₀ r₀ u₀ r : ℝ) : ℝ := u₀ - 2 * b₀ * Real.log (r / r₀)

/-- **Asymptotic freedom**: for `b₀ > 0` the coupling grows with distance. -/
theorem invCoup_strictAntiOn {b₀ r₀ u₀ : ℝ} (hb : 0 < b₀) (hr₀ : 0 < r₀) :
    StrictAntiOn (invCoup b₀ r₀ u₀) (Set.Ioi 0) := by
  intro r hr r' hr' hlt
  have h : Real.log (r / r₀) < Real.log (r' / r₀) :=
    Real.log_lt_log (div_pos hr hr₀) (div_lt_div_of_pos_right hlt hr₀)
  simp only [invCoup]
  nlinarith

/-- **Pure `U(1)`** (`b₀ = 0`): the coupling does not run. -/
theorem invCoup_abelian (r₀ u₀ r : ℝ) : invCoup 0 r₀ u₀ r = u₀ := by
  simp [invCoup]

/-- A dilation by `s` shifts `1/g²` by `−2 b₀ log s`. -/
theorem invCoup_dilation {b₀ r₀ u₀ r s : ℝ} (hr₀ : 0 < r₀) (hr : 0 < r) (hs : 0 < s) :
    invCoup b₀ r₀ u₀ (s * r) = invCoup b₀ r₀ u₀ r - 2 * b₀ * Real.log s := by
  simp only [invCoup]
  rw [show s * r / r₀ = s * (r / r₀) by ring, Real.log_mul hs.ne' (div_pos hr hr₀).ne']
  ring

/-- **At `b₀ = 0` the flow is dilation invariant.** -/
theorem abelian_dilation (r₀ u₀ r s : ℝ) : invCoup 0 r₀ u₀ (s * r) = invCoup 0 r₀ u₀ r := by
  simp [invCoup]

/-- **At `b₀ = 0` no distance reaches any other coupling**: no length is generated. -/
theorem abelian_no_scale {r₀ u₀ us : ℝ} (h : us ≠ u₀) (r : ℝ) : invCoup 0 r₀ u₀ r ≠ us := by
  rw [invCoup_abelian]; exact h.symm

/-- The distance at which `1/g²` reaches `us`: `r₀ exp((u₀ − us)/(2b₀))`.

DERIVED: `2` as in `invCoup`. -/
noncomputable def rStar (b₀ r₀ u₀ us : ℝ) : ℝ := r₀ * Real.exp ((u₀ - us) / (2 * b₀))

theorem rStar_pos {b₀ r₀ u₀ us : ℝ} (hr₀ : 0 < r₀) : 0 < rStar b₀ r₀ u₀ us :=
  mul_pos hr₀ (Real.exp_pos _)

theorem invCoup_rStar {b₀ r₀ u₀ us : ℝ} (hb : 0 < b₀) (hr₀ : 0 < r₀) :
    invCoup b₀ r₀ u₀ (rStar b₀ r₀ u₀ us) = us := by
  simp only [invCoup, rStar]
  rw [mul_div_cancel_left₀ _ hr₀.ne', Real.log_exp]
  have h2 : (2 * b₀) ≠ 0 := by positivity
  have : 2 * b₀ * ((u₀ - us) / (2 * b₀)) = u₀ - us := by field_simp
  linarith

/-- **Dimensional transmutation.** The length at which the coupling reaches `us` is the same from
every reference point along the one-loop flow. -/
theorem rStar_rg_invariant {b₀ r₀ r₁ u₀ us : ℝ} (hb : 0 < b₀) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) :
    rStar b₀ r₁ (invCoup b₀ r₀ u₀ r₁) us = rStar b₀ r₀ u₀ us := by
  simp only [rStar, invCoup]
  have h2 : (2 * b₀) ≠ 0 := by positivity
  have hsplit : (u₀ - 2 * b₀ * Real.log (r₁ / r₀) - us) / (2 * b₀)
      = (u₀ - us) / (2 * b₀) + -Real.log (r₁ / r₀) := by
    rw [show (u₀ - 2 * b₀ * Real.log (r₁ / r₀) - us) / (2 * b₀)
        = (u₀ - us) / (2 * b₀) - 2 * b₀ * Real.log (r₁ / r₀) / (2 * b₀) by ring,
      mul_div_cancel_left₀ _ h2]
    ring
  rw [hsplit, Real.exp_add, Real.exp_neg, Real.exp_log (div_pos hr₁ hr₀), inv_div]
  field_simp

/-- **The cutoff is the transmuted length times the one-loop factor** `exp(−(u₀ − us)/(2b₀))`
(an identity of the definition: at fixed transmuted length, the cutoff falls like `exp(−1/(2b₀g₀²))`
as the coupling at the cutoff falls). -/
theorem spacing_of_rStar (b₀ r₀ u₀ us : ℝ) :
    r₀ = rStar b₀ r₀ u₀ us * Real.exp (-((u₀ - us) / (2 * b₀))) := by
  rw [rStar, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- **One length up to a fixed factor.** The lengths at which the coupling reaches two values `us`,
`us'` differ by the factor `exp((us − us')/(2b₀))`, independent of the cutoff and of `u₀`: the one-loop
flow generates a single scale. -/
theorem rStar_shift (b₀ r₀ u₀ us us' : ℝ) :
    rStar b₀ r₀ u₀ us' = rStar b₀ r₀ u₀ us * Real.exp ((us - us') / (2 * b₀)) := by
  simp only [rStar]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Weak coupling at the cutoff is a long edge in cutoff units**: `rStar/r₀ → ∞` as `u₀ → ∞`.

DERIVED: `1` the shift in `exp x ≥ x + 1`. -/
theorem rStar_ratio_tendsto {b₀ r₀ : ℝ} (hb : 0 < b₀) (hr₀ : 0 < r₀) (us : ℝ) :
    Tendsto (fun u₀ => rStar b₀ r₀ u₀ us / r₀) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨us + 2 * b₀ * b, fun u₀ hu => ?_⟩
  simp only [rStar]
  rw [mul_div_cancel_left₀ _ hr₀.ne']
  have h1 := Real.add_one_le_exp ((u₀ - us) / (2 * b₀))
  have h2 : b ≤ (u₀ - us) / (2 * b₀) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  linarith

/-- **The perturbative coupling is positive exactly below the Landau length** `rStar b₀ r₀ u₀ 0`. -/
theorem invCoup_pos_iff {b₀ r₀ u₀ r : ℝ} (hb : 0 < b₀) (hr₀ : 0 < r₀) (hr : 0 < r) :
    0 < invCoup b₀ r₀ u₀ r ↔ r < rStar b₀ r₀ u₀ 0 := by
  have hA := invCoup_strictAntiOn (u₀ := u₀) hb hr₀
  have hR : rStar b₀ r₀ u₀ 0 ∈ Set.Ioi (0 : ℝ) := rStar_pos hr₀
  have hr' : r ∈ Set.Ioi (0 : ℝ) := hr
  have h0 : invCoup b₀ r₀ u₀ (rStar b₀ r₀ u₀ 0) = 0 := invCoup_rStar hb hr₀
  constructor
  · intro hu
    by_contra hge
    rcases (not_lt.mp hge).lt_or_eq with hlt | heq
    · have := hA hR hr' hlt
      linarith
    · rw [← heq] at hu
      linarith
  · intro hlt
    have := hA hr' hR hlt
    linarith

/-- The RG-improved Coulomb potential `−C g²(r)/(4π r)` (tree-level kernel with the one-loop running
coupling; the scheme constant of the full one-loop potential is not included), `C` the Casimir of
the source.

DERIVED: `4π` the Coulomb kernel. -/
noncomputable def vPert (C b₀ r₀ u₀ r : ℝ) : ℝ := -(C / (4 * Real.pi * r * invCoup b₀ r₀ u₀ r))

/-- The RG-improved Coulomb potential is negative wherever the perturbative coupling is positive. A
remark only: a potential is defined up to an additive self-energy, so its sign carries no cost per
length. -/
theorem vPert_neg {C b₀ r₀ u₀ r : ℝ} (hC : 0 < C) (hr : 0 < r) (hu : 0 < invCoup b₀ r₀ u₀ r) :
    vPert C b₀ r₀ u₀ r < 0 := by
  unfold vPert
  have hpi : 0 < 4 * Real.pi := by positivity
  exact neg_neg_of_pos (div_pos hC (mul_pos (mul_pos hpi hr) hu))

/-- **The perturbative potential is defined only below the Landau length.** Every `r` at which the
perturbative coupling is positive lies below `rStar b₀ r₀ u₀ 0 = 1/Λ`, so `lim_{r→∞} V(r)/r`, the
linear coefficient, is not reached by it. -/
theorem vPert_neg_on_domain {C b₀ r₀ u₀ : ℝ} (hC : 0 < C) (hb : 0 < b₀) (hr₀ : 0 < r₀) :
    ∀ r, 0 < r → 0 < invCoup b₀ r₀ u₀ r → r < rStar b₀ r₀ u₀ 0 ∧ vPert C b₀ r₀ u₀ r < 0 :=
  fun _ hr hu => ⟨(invCoup_pos_iff hb hr₀ hr).1 hu, vPert_neg hC hr hu⟩

end Running

/-! ## 3. Edges cannot end -/

section Centre

open Matrix

variable {N : ℕ}

/-- `star ω * ω = 1` for a root of unity. -/
theorem star_mul_self_of_pow {ω : ℂ} (hN : N ≠ 0) (hω : ω ^ N = 1) : star ω * ω = 1 := by
  have hnorm : ‖ω‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hω hN
  show (starRingEnd ℂ) ω * ω = 1
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hnorm]
  simp

/-- **`ω · 1 ∈ SU(N)`** for `ωᴺ = 1`. -/
theorem scalar_mem_SU {ω : ℂ} (hN : N ≠ 0) (hω : ω ^ N = 1) :
    ω • (1 : Matrix (Fin N) (Fin N) ℂ) ∈ Matrix.specialUnitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
  refine ⟨?_, ?_⟩
  · rw [star_smul, star_one, Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul,
      star_mul_self_of_pow hN hω, one_smul]
  · rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, hω]

/-- `ω · 1` acts on the fundamental by `ω`. -/
theorem scalar_fundamental (ω : ℂ) (v : Fin N → ℂ) :
    (ω • (1 : Matrix (Fin N) (Fin N) ℂ)) *ᵥ v = ω • v := by
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]

/-- **The centre acts trivially on the adjoint**: every central element of `SU(N)` fixes every matrix
under conjugation. Gluons carry N-ality `0`. -/
theorem centre_adjoint_trivial [NeZero N] (z : MassGap.SUN.SU N)
    (hz : z ∈ Subgroup.center (MassGap.SUN.SU N)) (X : Matrix (Fin N) (Fin N) ℂ) :
    (z : Matrix (Fin N) (Fin N) ℂ) * X * star (z : Matrix (Fin N) (Fin N) ℂ) = X := by
  have hcomm : NonAbelianForget.Commutes (z : Matrix (Fin N) (Fin N) ℂ) := by
    intro g hg
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨g, hg⟩)
  obtain ⟨hoff, heq⟩ := NonAbelianForget.commutant_SU hcomm
  have hsc : (z : Matrix (Fin N) (Fin N) ℂ)
      = (z : Matrix (Fin N) (Fin N) ℂ) 0 0 • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [heq i 0]
    · simp [hoff i j hij, Matrix.one_apply_ne hij]
  have hu : (z : Matrix (Fin N) (Fin N) ℂ) * star (z : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp z.2).1
  have hzX : (z : Matrix (Fin N) (Fin N) ℂ) * X = X * (z : Matrix (Fin N) (Fin N) ℂ) := by
    rw [hsc, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  rw [hzX, mul_assoc, hu, mul_one]

/-- **The centre acts nontrivially on the fundamental** for `N ≥ 2`: some central element of `SU(N)`
moves every nonzero vector. A fundamental endpoint is not centre-neutral. -/
theorem centre_fundamental_nontrivial (hN : 2 ≤ N) :
    ∃ z ∈ Matrix.specialUnitaryGroup (Fin N) ℂ, ∀ v : Fin N → ℂ, v ≠ 0 → z *ᵥ v ≠ v := by
  have hN0 : N ≠ 0 := by omega
  have hprim := Complex.isPrimitiveRoot_exp N hN0
  set ω := Complex.exp (2 * Real.pi * Complex.I / N)
  have hne : ω ≠ 1 := hprim.ne_one (by omega)
  refine ⟨ω • 1, scalar_mem_SU hN0 hprim.pow_eq_one, fun v hv h => hv ?_⟩
  rw [scalar_fundamental] at h
  have h0 : (ω - 1) • v = 0 := by rw [sub_smul, h, one_smul, sub_self]
  exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne)

/-- **N-ality, as phase arithmetic.** `ωᵏ (ω · star ω)ᵐ = ωᵏ`. Read on `k` fundamental and `m` adjoint
factors (`scalar_fundamental`: `ω` per fundamental; `centre_adjoint_trivial`: `1` per adjoint) this is
the centre phase; the tensor-product action itself is not formalised, and an antifundamental (phase
`star ω = ω^{N−1}`) counts as `N − 1` fundamentals. -/
theorem centre_phase {ω : ℂ} (hN : N ≠ 0) (hω : ω ^ N = 1) (k m : ℕ) :
    ω ^ k * (ω * star ω) ^ m = ω ^ k := by
  rw [mul_comm ω, star_mul_self_of_pow hN hω, one_pow, mul_one]

/-- **An endpoint of N-ality `k` dressed with gluons is centre-neutral iff `N ∣ k`.** Centre
neutrality is necessary for an edge to end: a single fundamental edge (`k = 1`, `N ≥ 2`) cannot end
on gluons; `N` fundamental edges can meet at a junction; for adjoint edges (`k = 0`) ending is allowed
by the centre, and whether they actually break is dynamical and not proved here. -/
theorem edge_can_end_iff {ω : ℂ} (hN : N ≠ 0) (hω : IsPrimitiveRoot ω N) (k m : ℕ) :
    ω ^ k * (ω * star ω) ^ m = 1 ↔ N ∣ k := by
  rw [centre_phase hN hω.pow_eq_one]
  exact hω.pow_eq_one_iff_dvd k

end Centre

#print axioms aperture_reading_const_iff
#print axioms creutz_phys
#print axioms creutz_reading_const_iff
#print axioms spacing_from_sigma_is_vacuous
#print axioms stringScaling_satisfiable
#print axioms bounded_sigma_fails_scaling
#print axioms stringScaling_sqrt
#print axioms sigmaPhys_heatKernel
#print axioms uniform_edgeRate
#print axioms invCoup_strictAntiOn
#print axioms abelian_no_scale
#print axioms invCoup_dilation
#print axioms invCoup_rStar
#print axioms rStar_rg_invariant
#print axioms spacing_of_rStar
#print axioms rStar_shift
#print axioms rStar_ratio_tendsto
#print axioms invCoup_pos_iff
#print axioms vPert_neg_on_domain
#print axioms scalar_mem_SU
#print axioms centre_adjoint_trivial
#print axioms centre_fundamental_nontrivial
#print axioms edge_can_end_iff

end MassGap.EdgeCost
