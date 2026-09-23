import MassGap.LagTwoSix

/-!
# MassGap.DiffractionNoGo — the diffraction ceiling at extents four and six

`Moment.Read.substrate_lt_of_tension_lt_floor` bounds the substrate ratio
`(∑ p d * circLag d ^ 2) / (N + 1) ^ 2` above by `(1 - 3 ^ (-1/4)) / 8` whenever the read's tension
is below the entropy floor. This module writes that bound out in closed form at the two smallest
even extents, compares it with the exact confinement criterion, and refutes the implication from the
bound to the criterion at each extent.

## Sections 0-1: closed forms

`clag_four` and `clag_six` decide `Moment.circLag` at extents four and six: `0, 1, 2, 1` and
`0, 1, 2, 3, 2, 1`. `rho_sum_four`, `rho_moment_four` and `substrate_num_four` fold a
circle-symmetric read at extent four into `Z₄ = ρ 0 + 2 * ρ 1 + ρ 2` and moment
`2 * ρ 1 + 4 * ρ 2`; `rho_sum_six`, `rho_moment_six` and `substrate_num_six` do the same at extent
six with `Z₆ = ρ 0 + 2 * ρ 1 + 2 * ρ 2 + ρ 3` and moment `2 * ρ 1 + 8 * ρ 2 + 9 * ρ 3`.

## Section 2: the bound in closed form

`ceiling_of_confines_four` and `ceiling_of_confines_six` substitute those into
`substrate_lt_of_tension_lt_floor` and clear denominators. With `c = 3 ^ (-1/4)` the results are

    extent four:   (2c - 1) * ρ 1 + (1 + c) * ρ 2                            <  (1 - c) * ρ 0
    extent six:    (18c - 14) * ρ 1 + (18c - 2) * ρ 2 + 9 * (1 + c) * ρ 3    <  9 * (1 - c) * ρ 0

Both take `R.tension < (1/4) * log 3` and a positive cosine average as hypotheses. By
`ApertureRoute.confines_iff_pos_and_tension_lt_floor` that pair is confinement at the aperture in
question, so these are consequences of confinement rather than routes to it.

## Section 3: the criterion implies the bound

`ConfinesSharp.confines_extent_four_iff` and `confines_extent_six_iff` give the exact criteria

    extent four:        2c * ρ 1 +              (1 + c) * ρ 2                <  (1 - c) * ρ 0
    extent six:   9 * (2c - 1) * ρ 1 + 9 * (1 + 2c) * ρ 2 + 9 * (1 + c) * ρ 3 <  9 * (1 - c) * ρ 0

No coefficient of the bound exceeds the criterion's, and three are strictly smaller: by `1` on `ρ 1`
at extent four, and by `5` on `ρ 1` and `11` on `ρ 2` at extent six. On `ρ 2` at extent four and
`ρ 3` at extent six they agree, at `1 + c` and `9 * (1 + c)`. With nonnegative lags that gives
`criterion_implies_ceiling_four` and `criterion_implies_ceiling_six`. The bound is the criterion with
each lag cosine `cos (π * d / m)` replaced by the upper bound `1 - 2 * d ^ 2 / m ^ 2`, which is the
inequality `Moment.Read.cos_avg_le_circ` spends.

## Section 4: the converse fails at both extents

`CeilingClosesFour` and `CeilingClosesSix` state the single-extent implications from the bound,
together with the coupling-uniform facts the tree proves at that extent, to the exact criterion.
`not_ceilingClosesFour` and `not_ceilingClosesSix` refute them, and
`ceiling_admits_lag_two_above_threshold` and `ceiling_admits_lag_two_above_threshold_six` restate
the witnesses as existentials with their lag-two ratios.

At extent four the premise list is `SpectralFour.FourRepresentable` in full — nonnegativity,
`ρ 2 ≤ ρ 1`, the log-convexity instance `ρ 1 ^ 2 ≤ ρ 0 * ρ 2`, and the quadratic
`2 * ρ 1 ^ 2 ≤ ρ 2 ^ 2 + ρ 0 * ρ 2` — all four of which `SlabQuadratic.wilsonSpectral` discharges at
every `β ≥ 0`. The witness is `(ρ 0, ρ 1, ρ 2) = (1, 4/25, 1/20)`. The geometric mode
`ρ d = (1/5) ^ circLag d` is not used: it clears the bound and fails the criterion but violates
`SlabQuadratic.wilson_quadratic`, `2/25` against `26/625`, so it is not a possible Wilson
correlation. `SpectralFour.missing_inequalities_independent` states that the quadratic does not
follow from the other three.

At extent six the premise list is `MomentShape.Shape 6 3`'s three non-trivial instances, and the
witness is the geometric mode `(1/4) ^ circLag d`, that is `(1, 1/4, 1/16, 1/64)`. Checked
numerically, not carried as premises, it also satisfies `ShapeNoGo`'s `Hankel` 3x3 condition on
levels `{0, 1, 2}` (on the boundary, with two vanishing minors),
`MomentShape.corrClay_even_antitone`, `WeakArm.wilsonCorrAt_le_at_zero` and
`LagTwoSix.lag_three_le_lag_two`.

Computed figures, not proved here. At extent four, holding `ρ 1` at the quadratic's boundary
`ρ 1 = √((ρ 2 ^ 2 + ρ 2) / 2)`, the window where the bound holds and the criterion fails is
`ρ 2 / ρ 0 ∈ (0.029696, 0.076534)`, with `1/20` inside it; the upper endpoint is a factor `2.577`
above the lower and `4.109` above `LagTwoBound.lagTwoThreshold = 0.0186240`. At extent six, on the
geometric family, the criterion's root is `0.211990` and the bound's is `0.361779`, with `1/4`
between them. `LagTwoSix.vSix = 0.183837` is the criterion's root on the flat-tail family
`(1, v, v ^ 2, v ^ 2)`, a different family, and is not an endpoint of either window.

## Scope

* Each bound instance carries confinement at its own aperture as a hypothesis, and
  `ApertureRoute.ConfinesAtAnAperture` is existential over apertures. So combining the extent-four
  and extent-six instances adds nothing: if confinement holds at some aperture the existential is
  already met, and if it holds at none then no instance of either bound has its hypothesis.
* Sections 3 and 4 are separate from that: they concern what the bound would give if granted at a
  single extent as a free premise.
* The opposite direction is a different pair of theorems.
  `Moment.Read.tension_lt_floor_of_circ_moment` and `Complete.confinement_at_of_substrate_sharp`
  give confinement from a substrate ratio below
  `substrateThreshold = arccos (3 ^ (-1/4)) ^ 2 / (2π) ^ 2 ≈ 0.0126877`. Reduced to lag two, that
  sufficient threshold is `0.0104826` at extent four on the geometric cone `(1, v, v ^ 2)` and
  `0.0195132` at extent six on the flat-tail cone, both below the exact criteria's `0.0186240` and
  `0.0337959`; at extent six on the geometric cone it is `0.0309317`, also below `0.0337959`. Those
  four figures are computed, not proved here.
* `Moment.Read.tension_ge_floor_of_substrate` excludes a substrate ratio at or above the bound; that
  direction is unaffected by anything here.
* `LagTwoSix.LagTwoRatioSix` — a bound `ρ 2 ≤ K * ρ 0` at every nonnegative coupling with
  `K < lagTwoThresholdSix` — is unchanged by this module, which neither weakens nor supplies it.
-/

namespace MassGap.DiffractionNoGo

open scoped BigOperators

/-! ## 0. The circle distances at the two smallest even extents -/

/-- The four values of `Moment.circLag` on `Fin (3 + 1)`: `0, 1, 2, 1`. Each conjunct by `decide`.

DERIVED: `3` is the aperture, so the extent is `3 + 1 = 4`; `0, 1, 2, 3` are the lag indices, and
the values `0, 1, 2, 1` are `min d (4 - d)` at each, folding the circle at the antipode `2`. -/
theorem clag_four :
    Moment.circLag (0 : Fin (3 + 1)) = 0 ∧ Moment.circLag (1 : Fin (3 + 1)) = 1 ∧
      Moment.circLag (2 : Fin (3 + 1)) = 2 ∧ Moment.circLag (3 : Fin (3 + 1)) = 1 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

#print axioms clag_four

/-- The six values of `Moment.circLag` on `Fin (5 + 1)`: `0, 1, 2, 3, 2, 1`. Each conjunct by
`decide`.

DERIVED: `5` is the aperture, so the extent is `5 + 1 = 6`; `0` through `5` are the lag indices, and
the values fold at the antipode `3`, which is why `4` reads `2` and `5` reads `1`. -/
theorem clag_six :
    Moment.circLag (0 : Fin (5 + 1)) = 0 ∧ Moment.circLag (1 : Fin (5 + 1)) = 1 ∧
      Moment.circLag (2 : Fin (5 + 1)) = 2 ∧ Moment.circLag (3 : Fin (5 + 1)) = 3 ∧
      Moment.circLag (4 : Fin (5 + 1)) = 2 ∧ Moment.circLag (5 : Fin (5 + 1)) = 1 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

#print axioms clag_six

/-! ## 1. The read's mass and second moment in closed form -/

/-- `∑ d, R.ρ d = R.ρ 0 + 2 * R.ρ 1 + R.ρ 2` for a `Moment.Read 3` with `R.ρ 3 = R.ρ 1`. Expands the
four-term sum and folds the symmetric pair.

DERIVED: `3` is the aperture; `0`, `1`, `2` and `3` are the lag indices, with `3` and `1` identified
by the symmetry hypothesis; the coefficient `2` counts that identified pair. -/
theorem rho_sum_four (R : Moment.Read 3) (hsym : R.ρ 3 = R.ρ 1) :
    ∑ d, R.ρ d = R.ρ 0 + 2 * R.ρ 1 + R.ρ 2 := by
  rw [Fin.sum_univ_four, hsym]; ring

#print axioms rho_sum_four

/-- `∑ d, R.ρ d * (circLag d : ℝ) ^ 2 = 2 * R.ρ 1 + 4 * R.ρ 2` for a `Moment.Read 3` with
`R.ρ 3 = R.ρ 1`. Substitutes `clag_four` and folds the symmetric pair.

DERIVED: `3` is the aperture; the lag indices are `0` to `3`; the exponent `2` is the moment's
order; the coefficient `2` on `R.ρ 1` is the two lags at circle distance one, whose squared distance
is `1`, and `4` on `R.ρ 2` is the squared distance `2 ^ 2` at the single antipodal lag. -/
theorem rho_moment_four (R : Moment.Read 3) (hsym : R.ρ 3 = R.ρ 1) :
    ∑ d, R.ρ d * (Moment.circLag d : ℝ) ^ 2 = 2 * R.ρ 1 + 4 * R.ρ 2 := by
  obtain ⟨h0, h1, h2, h3⟩ := clag_four
  rw [Fin.sum_univ_four, h0, h1, h2, h3, hsym]
  push_cast
  ring

#print axioms rho_moment_four

/-- `∑ d, R.p d * (circLag d : ℝ) ^ 2 = (2 * R.ρ 1 + 4 * R.ρ 2) / (R.ρ 0 + 2 * R.ρ 1 + R.ρ 2)` for a
`Moment.Read 3` with `R.ρ 3 = R.ρ 1`. Pulls the normalisation out of the sum, then applies
`rho_moment_four` and `rho_sum_four`.

DERIVED: `3` is the aperture; the lag indices are `0` to `3`; the exponent `2` is the moment's
order; the coefficients `2` and `4` are the folded multiplicity and the squared antipodal distance,
as in `rho_moment_four`, and the `2` in the denominator is the folded pair's multiplicity. -/
theorem substrate_num_four (R : Moment.Read 3) (hsym : R.ρ 3 = R.ρ 1) :
    ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2
      = (2 * R.ρ 1 + 4 * R.ρ 2) / (R.ρ 0 + 2 * R.ρ 1 + R.ρ 2) := by
  have hsplit : ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2
      = (∑ d, R.ρ d * (Moment.circLag d : ℝ) ^ 2) / (∑ d, R.ρ d) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    simp only [Moment.Read.p]
    ring
  rw [hsplit, rho_moment_four R hsym, rho_sum_four R hsym]

#print axioms substrate_num_four

/-- `∑ d, R.ρ d = R.ρ 0 + 2 * R.ρ 1 + 2 * R.ρ 2 + R.ρ 3` for a `Moment.Read 5` with `R.ρ 5 = R.ρ 1`
and `R.ρ 4 = R.ρ 2`. Expands the six-term sum and folds the two symmetric pairs.

DERIVED: `5` is the aperture; `0` through `5` are the lag indices, with `5` identified to `1` and
`4` to `2`; the two coefficients `2` count those identified pairs. -/
theorem rho_sum_six (R : Moment.Read 5) (hs1 : R.ρ 5 = R.ρ 1) (hs2 : R.ρ 4 = R.ρ 2) :
    ∑ d, R.ρ d = R.ρ 0 + 2 * R.ρ 1 + 2 * R.ρ 2 + R.ρ 3 := by
  rw [Fin.sum_univ_six, hs1, hs2]; ring

#print axioms rho_sum_six

/-- `∑ d, R.ρ d * (circLag d : ℝ) ^ 2 = 2 * R.ρ 1 + 8 * R.ρ 2 + 9 * R.ρ 3` for a `Moment.Read 5`
with the two symmetry hypotheses. Substitutes `clag_six` and folds.

DERIVED: `5` is the aperture; the lag indices run `0` to `5`; the exponent `2` is the moment's
order. The coefficients are multiplicity times squared distance: `2 = 2 * 1 ^ 2` for the pair at
circle distance one, `8 = 2 * 2 ^ 2` for the pair at distance two, and `9 = 1 * 3 ^ 2` for the
single antipodal lag. -/
theorem rho_moment_six (R : Moment.Read 5) (hs1 : R.ρ 5 = R.ρ 1) (hs2 : R.ρ 4 = R.ρ 2) :
    ∑ d, R.ρ d * (Moment.circLag d : ℝ) ^ 2
      = 2 * R.ρ 1 + 8 * R.ρ 2 + 9 * R.ρ 3 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := clag_six
  rw [Fin.sum_univ_six, h0, h1, h2, h3, h4, h5, hs1, hs2]
  push_cast
  ring

#print axioms rho_moment_six

/-- `∑ d, R.p d * (circLag d : ℝ) ^ 2 = (2 * R.ρ 1 + 8 * R.ρ 2 + 9 * R.ρ 3) / (R.ρ 0 + 2 * R.ρ 1 + 2 * R.ρ 2 + R.ρ 3)`
for a `Moment.Read 5` with the two symmetry hypotheses. Pulls the normalisation out, then applies
`rho_moment_six` and `rho_sum_six`.

DERIVED: `5` is the aperture; the lag indices run `0` to `5`; the exponent `2` is the moment's
order; `2`, `8` and `9` are the multiplicity-weighted squared distances of `rho_moment_six`, and the
two `2`s in the denominator are the folded pairs' multiplicities. -/
theorem substrate_num_six (R : Moment.Read 5) (hs1 : R.ρ 5 = R.ρ 1) (hs2 : R.ρ 4 = R.ρ 2) :
    ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2
      = (2 * R.ρ 1 + 8 * R.ρ 2 + 9 * R.ρ 3)
          / (R.ρ 0 + 2 * R.ρ 1 + 2 * R.ρ 2 + R.ρ 3) := by
  have hsplit : ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2
      = (∑ d, R.ρ d * (Moment.circLag d : ℝ) ^ 2) / (∑ d, R.ρ d) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    simp only [Moment.Read.p]
    ring
  rw [hsplit, rho_moment_six R hs1 hs2, rho_sum_six R hs1 hs2]

#print axioms substrate_num_six

/-! ## 2. The bound in closed form at each extent

Both theorems below take `R.tension < (1/4) * log 3` and a positive cosine average as hypotheses. By
`ApertureRoute.confines_iff_pos_and_tension_lt_floor` that pair is the confinement condition at the
aperture, so each theorem states a consequence of confinement at its own aperture. -/

/-- For a `Moment.Read 3` with `R.ρ 3 = R.ρ 1`, a positive cosine average and
`R.tension < (1 / 4) * Real.log 3`, writing `c = (3 : ℝ) ^ (-(1 : ℝ) / 4)`:

    (2 * c - 1) * R.ρ 1 + (1 + c) * R.ρ 2 < (1 - c) * R.ρ 0.

`Moment.Read.substrate_lt_of_tension_lt_floor` with `substrate_num_four` substituted and the
denominators `Z₄` and `8` cleared by `div_lt_div_iff₀`.

Scope: the two hypotheses together are confinement at this aperture, by
`ApertureRoute.confines_iff_pos_and_tension_lt_floor`.

DERIVED: `3` is the aperture and the argument of the logarithm and of `c`; `1` and `4` are the
exponent `-1/4` of `c` and the coefficient `1/4` of the floor `(1/4) * log 3`; `0` is the strict
lower bound on the cosine average and the contact lag index; `2` is the criterion's coefficient on
`R.ρ 1`, which is `4` times the lag-one weight `1` divided by the `2` of the halved period. The
squared extent `16 = 4 ^ 2` and the constant `8` of `Moment.Read.cos_avg_le_circ` are cleared in the
proof and do not survive into the statement. -/
theorem ceiling_of_confines_four (R : Moment.Read 3) (hsym : R.ρ 3 = R.ρ 1)
    (hpos : 0 < ∑ d, R.p d * Real.cos (R.θ d))
    (htens : R.tension < (1 / 4) * Real.log 3) :
    (2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1) * R.ρ 1
        + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * R.ρ 2
      < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * R.ρ 0 := by
  have hcap := R.substrate_lt_of_tension_lt_floor hpos htens
  have hZ0 : (0 : ℝ) < R.ρ 0 + 2 * R.ρ 1 + R.ρ 2 := by
    rw [← rho_sum_four R hsym]; exact R.hpos
  rw [substrate_num_four R hsym, div_div,
    div_lt_div_iff₀ (mul_pos hZ0 (by positivity)) (by norm_num : (0 : ℝ) < 8)] at hcap
  norm_num at hcap
  nlinarith [hcap]

#print axioms ceiling_of_confines_four

/-- For a `Moment.Read 5` with `R.ρ 5 = R.ρ 1`, `R.ρ 4 = R.ρ 2`, a positive cosine average and
`R.tension < (1 / 4) * Real.log 3`, writing `c = (3 : ℝ) ^ (-(1 : ℝ) / 4)`:

    (18c - 14) * R.ρ 1 + (18c - 2) * R.ρ 2 + (9 + 9c) * R.ρ 3 < (9 - 9c) * R.ρ 0.

`Moment.Read.substrate_lt_of_tension_lt_floor` with `substrate_num_six` substituted and the
denominators `Z₆` and `8` cleared.

Scope: as at extent four, the two hypotheses together are confinement at this aperture.

DERIVED: `5` is the aperture and `0` to `5` the lag indices; `3` is the base of `c` and the
logarithm's argument, with `1` and `4` its exponent and the floor's coefficient; `0` is the strict
lower bound on the cosine average. `9` is `36 / 4`, what the squared extent `36 = 6 ^ 2` leaves after
the clearing divides through by `4`; `18`, `14` and `2` are the lag weights `2, 8, 9` of
`rho_moment_six` carried through that same clearing against `8 * (1 - c)`. -/
theorem ceiling_of_confines_six (R : Moment.Read 5) (hs1 : R.ρ 5 = R.ρ 1) (hs2 : R.ρ 4 = R.ρ 2)
    (hpos : 0 < ∑ d, R.p d * Real.cos (R.θ d))
    (htens : R.tension < (1 / 4) * Real.log 3) :
    (18 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 14) * R.ρ 1
        + (18 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 2) * R.ρ 2
        + (9 + 9 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * R.ρ 3
      < (9 - 9 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * R.ρ 0 := by
  have hcap := R.substrate_lt_of_tension_lt_floor hpos htens
  have hZ0 : (0 : ℝ) < R.ρ 0 + 2 * R.ρ 1 + 2 * R.ρ 2 + R.ρ 3 := by
    rw [← rho_sum_six R hs1 hs2]; exact R.hpos
  rw [substrate_num_six R hs1 hs2, div_div,
    div_lt_div_iff₀ (mul_pos hZ0 (by positivity)) (by norm_num : (0 : ℝ) < 8)] at hcap
  norm_num at hcap
  nlinarith [hcap]

#print axioms ceiling_of_confines_six

/-! ## 3. The ceiling is implied by the exact criterion, and is therefore never stronger -/

/-- The extent-four criterion implies the extent-four bound. From `0 ≤ r₁` and
`2c * r₁ + (1 + c) * r₂ < (1 - c) * r₀`, the conclusion `(2c - 1) * r₁ + (1 + c) * r₂ < (1 - c) * r₀`,
by `nlinarith`. The two differ only in that coefficient on `r₁`, so nonnegativity of the first lag
settles it.

Scope: the implication runs one way only; `not_ceilingClosesFour` refutes the converse.

DERIVED: `0` is the lower bound on `r₁`; `3`, `1` and `4` are the constant
`c = 3 ^ (-1/4)`; `2` is the criterion's coefficient on `r₁`, and the subtracted `1` is the
difference between the criterion's and the bound's coefficients there. -/
theorem criterion_implies_ceiling_four {r₀ r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁)
    (h : 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) * r₁ + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₂
        < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀) :
    (2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1) * r₁ + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₂
      < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀ := by
  nlinarith [h, h₁]

#print axioms criterion_implies_ceiling_four

/-- The extent-six criterion implies the extent-six bound. From `0 ≤ r₁`, `0 ≤ r₂` and
`(2c - 1) * r₁ + (1 + 2c) * r₂ + (1 + c) * r₃ < (1 - c) * r₀`, the conclusion
`(18c - 14) * r₁ + (18c - 2) * r₂ + (9 + 9c) * r₃ < (9 - 9c) * r₀`, by `nlinarith`. Scaled by `9`
the criterion's coefficients are `9 * (2c - 1)` and `9 * (1 + 2c)`, exceeding the bound's by `5` on
`r₁` and `11` on `r₂`, and agreeing on `r₃`.

DERIVED: `0` is the lower bound on `r₁` and `r₂`; `3`, `1` and `4` are the constant `c`; `2` is the
criterion's coefficient on `r₁` and on `r₂`; `18`, `14` and `9` are the bound's cleared
coefficients, as in `ceiling_of_confines_six`. -/
theorem criterion_implies_ceiling_six {r₀ r₁ r₂ r₃ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂)
    (h : (2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1) * r₁
          + (1 + 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₂
          + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₃
        < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀) :
    (18 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 14) * r₁
        + (18 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 2) * r₂
        + (9 + 9 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₃
      < (9 - 9 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀ := by
  nlinarith [h, h₁, h₂]

#print axioms criterion_implies_ceiling_six

/-! ## 4. THE REFUTATION: the ceiling does not imply the criterion, at either extent

`CeilingClosesFour` and `CeilingClosesSix` are the single-extent implications a diffraction argument
would have to supply — the ceiling, plus the uniform facts the tree proves at that extent, delivering
the exact criterion. Both are refuted.

What is and is not granted, stated so the strength of each refutation is readable. At extent four the
premise list is `SpectralFour.FourRepresentable` in full, which is everything the tree proves of the
extent-four triple at `β ≥ 0`, so the refutation there is against the complete set. At extent six the
premise list is `MomentShape.Shape 6 3`'s three non-trivial instances; the witness additionally
satisfies `ShapeNoGo`'s `Hankel` 3×3 PSD condition, `MomentShape.corrClay_even_antitone`,
`WeakArm.wilsonCorrAt_le_at_zero` and `LagTwoSix.lag_three_le_lag_two`, checked numerically rather
than carried as premises, so granting those too would not rescue the implication.

These refutations are NOT what closes the aperture differential — section 1.1 does that, and does it
for a different reason. -/

/-- The implication a diffraction argument would have to supply at extent four: the ceiling, together
with EVERY coupling-uniform fact the tree proves of the extent-four triple, giving the exact
criterion.

The premise list is `SpectralFour.FourRepresentable` verbatim — nonnegativity, `ρ(2) ≤ ρ(1)`, the
log-convexity instance `ρ(1)² ≤ ρ(0)ρ(2)`, and the quadratic `2ρ(1)² ≤ ρ(2)² + ρ(0)ρ(2)` — and that
is deliberate: `SlabQuadratic.wilsonSpectral` discharges all four at every `β ≥ 0`, so an implication
refuted against THIS list is refuted against everything a diffraction argument may help itself to.
Granting less would refute a weaker implication and prove nothing about the route.

`MomentShape.Shape 4 2` alone supplies only the third of the four. `LinkGram.wilson_lag_two_le_lag_one`
supplies the second and `SlabQuadratic.wilson_quadratic` the fourth, and the fourth is INDEPENDENT of
the others — `SpectralFour.missing_inequalities_independent` — so omitting it is not harmless.

DERIVED: no literal here is chosen and none is a level. `3`, `1` and `4` are the floor `c = 3^{−1/4}`
carried in by name from `Floor.lean`. The `2` in `2c` and in `2r₁²` is the criterion's own coefficient
on `ρ(1)`, which `SpectralFour.FourRepresentable` also carries; `1 ± c` are the criterion's remaining
coefficients and `2c−1` is the ceiling's, from section 2's clearing of
`(2ρ(1)+4ρ(2))/(16·Z₄)` in which `16 = 4²` is the squared extent and `2, 4` are `Moment.circLag`
squared. `0` is a sign and the exponent `2` is a square. -/
def CeilingClosesFour : Prop :=
  ∀ r₀ r₁ r₂ : ℝ, 0 < r₀ → 0 ≤ r₁ → 0 ≤ r₂ → r₁ ^ 2 ≤ r₀ * r₂ →
    r₂ ≤ r₁ → 2 * r₁ ^ 2 ≤ r₂ ^ 2 + r₀ * r₂ →
    ((2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1) * r₁ + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₂
      < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀) →
    (2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) * r₁ + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₂
      < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀)

#print axioms CeilingClosesFour

/-- `¬ CeilingClosesFour`. The witness is `(r₀, r₁, r₂) = (1, 4/25, 1/20)`, which satisfies all four
`FourRepresentable` conjuncts — nonnegativity, `r₂ ≤ r₁`, log-convexity `16/625 ≤ 1/20`, and the
quadratic `32/625 ≤ 21/400` — clears the bound, and fails the criterion.
`LagTwoBound.floor_bounds` supplies the numeric bracket on `c` for both `linarith` calls.

Scope. The geometric mode `ρ d = (1/5) ^ circLag d` is not used as the witness: it clears the bound
and fails the criterion but violates `SlabQuadratic.wilson_quadratic`, `2/25` against `26/625`, so
it is not a possible Wilson correlation at any `β`. `SpectralFour.missing_inequalities_independent`
states that the quadratic does not follow from the other three conjuncts. The witness is also not a
slow mode: `ZeroMode.lam_pow_lt_of_tension` asks `λ ^ (n/2) < 0.360246`, and the witness's lag-two
ratio is `0.05`.

DERIVED: the statement is `¬ CeilingClosesFour` and contains no numeral of its own; the numerals of
the implication are documented at `CeilingClosesFour`.

CHOSEN: `1/20` for `r₂`, a round rational inside the window `(0.0296959, 0.0765343)` in which the
bound holds and the criterion fails; `4/25` for `r₁`, the quadratic's own largest admissible value
`√(21/800) = 0.1620` rounded down, which rounds against the refutation. Both live in the proof term.
Any point strictly inside the window serves. -/
theorem not_ceilingClosesFour : ¬ CeilingClosesFour := by
  intro h
  have hc := MassGap.LagTwoBound.floor_bounds
  have hceil : (2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1) * (4 / 25)
        + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * (1 / 20)
      < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * 1 := by
    linarith [hc.1, hc.2]
  have := h 1 (4 / 25) (1 / 20) one_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hceil
  linarith [hc.1, hc.2]

#print axioms not_ceilingClosesFour

/-- The extent-four witness as an existential: there are `r₀ r₁ r₂` with `0 < r₀`, the three
nonnegativity and shape conditions of `FourRepresentable`, satisfying the bound, failing the
criterion, and with `2 * LagTwoBound.lagTwoThreshold < r₂ / r₀`. The witness is
`(1, 4/25, 1/20)`, and `LagTwoBound.lagTwoThreshold_lt` supplies the comparison.

Scope: the full `FourRepresentable` premise set is carried, so the triple is one the extent-four
uniform facts admit.

DERIVED: `0` is the strict lower bound on `r₀` and the lower bounds on `r₁` and `r₂`; the exponent
`2` is the square in the log-convexity and quadratic conditions; `3`, `1` and `4` are the constant
`c = 3 ^ (-1/4)`; the leading `2` in `2 * lagTwoThreshold` is the factor being reported, read off
the witness's ratio `1/20` against the threshold's `0.0186240`, not a chosen tolerance. -/
theorem ceiling_admits_lag_two_above_threshold :
    ∃ r₀ r₁ r₂ : ℝ, 0 < r₀ ∧ 0 ≤ r₁ ∧ 0 ≤ r₂ ∧ r₁ ^ 2 ≤ r₀ * r₂ ∧
      r₂ ≤ r₁ ∧ 2 * r₁ ^ 2 ≤ r₂ ^ 2 + r₀ * r₂ ∧
      ((2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1) * r₁ + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₂
        < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀) ∧
      ¬ (2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) * r₁ + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₂
        < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀) ∧
      2 * MassGap.LagTwoBound.lagTwoThreshold < r₂ / r₀ := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have hT := MassGap.LagTwoBound.lagTwoThreshold_lt
  refine ⟨1, 4 / 25, 1 / 20, one_pos, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, ?_, ?_, ?_⟩
  · linarith [hc.1, hc.2]
  · rw [not_lt]; linarith [hc.1, hc.2]
  · rw [show (1 : ℝ) / 20 / 1 = 1 / 20 by norm_num]; linarith [hT]

#print axioms ceiling_admits_lag_two_above_threshold

/-- `lagTwoThresholdSix < 1/16`, from `LagTwoSix.vSix_root` alone. Needed to say where the extent-six
witness sits relative to the bar; the true value is `0.0337959`, so this is a loose bracket used only
for a comparison, and it rounds AWAY from the claim.

DERIVED: `1/16` is the extent-six witness rate `1/4` squared. Nothing is fitted. -/
theorem lagTwoThresholdSix_lt_sixteenth : MassGap.LagTwoSix.lagTwoThresholdSix < 1 / 16 := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have hroot := MassGap.LagTwoSix.vSix_root
  have hv0 := MassGap.LagTwoSix.vSix_pos
  have hv : MassGap.LagTwoSix.vSix < 1 / 4 := by
    nlinarith [hroot, hv0, hc.1, hc.2]
  rw [MassGap.LagTwoSix.lagTwoThresholdSix]
  nlinarith [hv, hv0]

#print axioms lagTwoThresholdSix_lt_sixteenth

/-- The implication a diffraction argument would have to supply at extent six. The three
log-convexity instances are the ones `LagTwoSix.lagTwoThresholdSix_sharp` exhibits at half-extent
three — `(0,1)`, `(0,2)` and `(1,2)`, the last two folded through `ρ(4) = ρ(2)`.

DERIVED: no literal here is chosen and none is a level. `3`, `1` and `4` are the floor `c = 3^{−1/4}`
carried in by name from `Floor.lean`. `18`, `14`, `2` and `9` are the extent-six ceiling's cleared
coefficients — `(18c−14)`, `(18c−2)`, `9(1+c)` and `9(1−c)` — produced by section 2's denominator
clearing from the substrate ratio `(2ρ(1)+8ρ(2)+9ρ(3))/(36·Z₆)`, in which `36 = 6²` is the squared
extent and `2, 8, 9` are `Moment.circLag` squared; the `9` here is `36/4`, that denominator's
surviving factor after the clearing divides through by `4`. `0` is a sign and the exponent `2` is a
square. -/
def CeilingClosesSix : Prop :=
  ∀ r₀ r₁ r₂ r₃ : ℝ, 0 < r₀ → 0 ≤ r₁ → 0 ≤ r₂ → 0 ≤ r₃ →
    r₁ ^ 2 ≤ r₀ * r₂ → r₂ ^ 2 ≤ r₀ * r₂ → r₃ ^ 2 ≤ r₂ ^ 2 →
    ((18 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 14) * r₁
        + (18 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 2) * r₂
        + (9 + 9 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₃
      < (9 - 9 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀) →
    ((2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1) * r₁
        + (1 + 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₂
        + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₃
      < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀)

#print axioms CeilingClosesSix

/-- `¬ CeilingClosesSix`. The witness is the geometric mode `(1/4) ^ circLag d`, that is
`(r₀, r₁, r₂, r₃) = (1, 1/4, 1/16, 1/64)`, which meets all three log-convexity instances available
at half-extent three — the first with equality — clears the bound, and fails the criterion.
`LagTwoBound.floor_bounds` supplies the numeric bracket on `c`.

Scope: the witness's lag-two ratio is `1/16`, above `LagTwoSix.lagTwoThresholdSix` by
`lagTwoThresholdSix_lt_sixteenth`. The factor `1.81` that
`LagTwoSix.lagTwoThreshold_lt_lagTwoThresholdSix` reports between the two extents' thresholds is a
separate statement and is not affected by this one.

DERIVED: the statement is `¬ CeilingClosesSix` and contains no numeral of its own; the numerals of
the implication are documented at `CeilingClosesSix`.

CHOSEN: `1/4` as the geometric ratio, a round number inside `(0.211990, 0.361779)`, the criterion's
root and the bound's root on the geometric family `ρ d = λ ^ circLag d`. Both endpoints are roots of
cubics in `λ`: `(2c - 1)λ + (1 + 2c)λ ^ 2 + (1 + c)λ ^ 3 = 1 - c` for the criterion and
`(18c - 14)λ + (18c - 2)λ ^ 2 + 9(1 + c)λ ^ 3 = 9(1 - c)` for the bound.
`LagTwoSix.vSix = 0.183837` is the criterion's root on the flat-tail family `(1, v, v ^ 2, v ^ 2)`,
a different family, and is not an endpoint here. -/
theorem not_ceilingClosesSix : ¬ CeilingClosesSix := by
  intro h
  have hc := MassGap.LagTwoBound.floor_bounds
  have hceil : (18 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 14) * (1 / 4)
        + (18 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 2) * (1 / 16)
        + (9 + 9 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * (1 / 64)
      < (9 - 9 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * 1 := by
    linarith [hc.1, hc.2]
  have := h 1 (1 / 4) (1 / 16) (1 / 64) one_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hceil
  linarith [hc.1, hc.2]

#print axioms not_ceilingClosesSix

/-- The extent-six witness as an existential: there are `r₀ r₁ r₂ r₃` with `0 < r₀`, the three
nonnegativity conditions and the three log-convexity instances, satisfying the bound, failing the
criterion, and with `LagTwoSix.lagTwoThresholdSix < r₂ / r₀`. The witness is `(1, 1/4, 1/16, 1/64)`
and the last conjunct comes from `lagTwoThresholdSix_lt_sixteenth`.

DERIVED: `0` is the strict lower bound on `r₀` and the lower bounds on the other three; the exponent
`2` is the square in the three log-convexity conditions; `3`, `1` and `4` are the constant
`c = 3 ^ (-1/4)`; `18`, `14`, `2` and `9` are the bound's cleared coefficients and `2`, `1` the
criterion's, both as documented at `CeilingClosesSix`. -/
theorem ceiling_admits_lag_two_above_threshold_six :
    ∃ r₀ r₁ r₂ r₃ : ℝ, 0 < r₀ ∧ 0 ≤ r₁ ∧ 0 ≤ r₂ ∧ 0 ≤ r₃ ∧
      r₁ ^ 2 ≤ r₀ * r₂ ∧ r₂ ^ 2 ≤ r₀ * r₂ ∧ r₃ ^ 2 ≤ r₂ ^ 2 ∧
      ((18 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 14) * r₁
          + (18 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 2) * r₂
          + (9 + 9 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₃
        < (9 - 9 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀) ∧
      ¬ ((2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1) * r₁
          + (1 + 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₂
          + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₃
        < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀) ∧
      MassGap.LagTwoSix.lagTwoThresholdSix < r₂ / r₀ := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have hT := lagTwoThresholdSix_lt_sixteenth
  refine ⟨1, 1 / 4, 1 / 16, 1 / 64, one_pos, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · linarith [hc.1, hc.2]
  · rw [not_lt]; linarith [hc.1, hc.2]
  · rw [show (1 : ℝ) / 16 / 1 = 1 / 16 by norm_num]; exact hT

#print axioms ceiling_admits_lag_two_above_threshold_six

/-! ## 5. Footprints -/

section Audit
#print axioms clag_four
#print axioms clag_six
#print axioms rho_sum_four
#print axioms rho_moment_four
#print axioms substrate_num_four
#print axioms rho_sum_six
#print axioms rho_moment_six
#print axioms substrate_num_six
#print axioms ceiling_of_confines_four
#print axioms ceiling_of_confines_six
#print axioms criterion_implies_ceiling_four
#print axioms criterion_implies_ceiling_six
#print axioms CeilingClosesFour
#print axioms not_ceilingClosesFour
#print axioms ceiling_admits_lag_two_above_threshold
#print axioms lagTwoThresholdSix_lt_sixteenth
#print axioms CeilingClosesSix
#print axioms not_ceilingClosesSix
#print axioms ceiling_admits_lag_two_above_threshold_six
end Audit

end MassGap.DiffractionNoGo
