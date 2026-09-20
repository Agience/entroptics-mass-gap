import MassGap.ApertureRoute
import MassGap.PowerTail
import MassGap.WilsonAnalytic

/-!
# MassGap.ConfinesZero — `ConfinesAtAnAperture` at and around zero coupling

`ApertureRoute.ConfinesAtAnAperture` is the single open hypothesis of the development:

    ∃ a : EvenAp, ∀ β : ℝ, 3^{−1/4} < cosAvgEven a β

and `ApertureRoute.flagship_of_confinement_at_an_aperture` turns it into the gap, non-triviality,
`SO(4)` and the continuum object. This file settles the part of the coupling line that the tree's
existing theorems already reach, and reduces what is left to one statement.

## What is proved here

* `cosAvgEven_at_zero` — **at zero coupling the cosine average is exactly `1`**, at EVERY even
  aperture. `PowerTail.wilsonCorrAt_at_zero_coupling` kills the correlation at every lag of nonzero
  circle distance (product Haar factorises the two plaquettes), and
  `PowerTail.contact_value_pos_at_zero_coupling` keeps lag `0` strictly positive. So the normalised
  read is a point mass at lag `0`, where `θ = 0` and `cos θ = 1`. Nothing is estimated.
* `cosAvgEven_eq_one_of_nonpos` — and therefore at every NONPOSITIVE coupling, because `readEven`
  clamps at `max β 0` (`EvenAperture.readEven_eq_at_zero`). The negative half-line is not an
  achievement; it is the clamp, and it is stated so that `confines_near_zero` is not misread as
  two-sided evidence.
* `continuous_cosAvgEven` — `β ↦ cosAvgEven a β` is CONTINUOUS on all of `ℝ`, at every even
  aperture. The input is `WilsonAnalytic.wilsonSystem_expect_hasDerivAt`, which differentiates a
  bounded measurable observable's Gibbs expectation in `β` on the genuine Wilson measure with no
  hypothesis at all; `corrClay` is three such expectations, the clamp is continuous, and the
  denominator is the second clause of the PROVED reflection positivity, so it never vanishes.
* `confines_near_zero`, `confines_below_a_cut` — the hypothesis therefore holds on a NEIGHBOURHOOD
  of zero, and in fact on a half-line `(−∞, b)`. The cut is existential and no numeral is named for
  it: it is whatever the continuity of the Wilson expectation supplies.

## The closed form at the smallest admissible extent

`EvenAp` needs `N + 1 = 2m` with `2 ≤ m`, so the smallest extent is four (`ap4`). There the lag
angles are `0, π/2, π, 3π/2` with cosines `1, 0, −1, 0`, and circle symmetry
(`MomentShape.wilsonCorrAt_neg`) identifies lag `3` with lag `1`. So

    cosAvgEven ap4 β = (ρ(0) − ρ(2)) / (ρ(0) + 2ρ(1) + ρ(2))          (`cosAvgEven_extent_four`)

with `ρ = wilsonCorrAt 3 (max β 0)`. The hypothesis at the smallest aperture is a statement about
THREE NUMBERS, and lag `1` enters the denominator only — it can only hurt.

`confines_extent_four_of_lag_two_small` is what the tree's proved shape facts do to that ratio.
`LogConvex.corrClay_log_convex_at_extent_four` gives `ρ(1)² ≤ ρ(0)ρ(2)` and
`Complete.wilson_reflection_positive_at_even` gives `ρ ≥ 0`; together they reduce the whole
hypothesis at extent four to a bound on the SECOND lag alone,

    (1 + 3^{−1/4})² ρ(2) < (1 − 3^{−1/4})² ρ(0),

and that threshold is not chosen — it is the exact one, as the identity

    ((1−c)ρ₀ − (1+c)ρ₂)² − 4c²ρ₀ρ₂ = ((1−c)²ρ₀ − (1+c)²ρ₂)(ρ₀ − ρ₂)

shows by vanishing at it. `WeakArm.corrClay_le_at_zero` and `MomentShape.corrClay_even_antitone`
DO NOT apply here: both carry `3 ≤ m`, which is extent six and above. At extent four the only shape
facts available are nonnegativity, circle symmetry and log-convexity.

## What remains, as one Prop

`MissesTheFloor` — at some even aperture the cosine average is never EQUAL to `3^{−1/4}`. With
continuity and the value `1` at zero coupling this is EQUIVALENT to `ConfinesAtAnAperture`
(`confinesAtAnAperture_iff_missesTheFloor`), by the intermediate value theorem: the average starts
above the floor, so if it were ever below it, it would have to cross. So what is open is exactly

  **the cosine average staying off the floor `3^{−1/4}` away from zero coupling** —

an inequality everywhere has become a non-equality everywhere, and nothing else is left on this side.
This file does not close it and claims no bound on `cosAvgEven` at large `β`.

DERIVED: `3^{−1/4} = e^{−κ₀YM}` with `κ₀YM = ¼ log 3` counted off directed cube paths in `Floor.lean`;
`4` is the smallest even extent with `2 ≤ m`, read off `Complete.wilson_reflection_positive_at_even`'s
hypotheses; the lag angles `2π d / 4` are `Moment.Read.θ` at that extent. No numeral in this file is
a magnitude and none is fitted.
-/

namespace MassGap.ConfinesZero

open MassGap MassGap.EvenAperture MassGap.ApertureRoute
open MassGap.WilsonLattice MassGap.WilsonAction MassGap.WilsonReal MassGap.CompactGauge
open MeasureTheory

/-! ## 0. Two small facts about the read -/

/-- A lag other than the origin has circle distance at least one. `circLag d = min d (N+1−d)`, and
both entries are at least one exactly when `d ≠ 0`. -/
theorem one_le_circLag {N : ℕ} {d : Fin (N + 1)} (hd : d ≠ 0) : 1 ≤ Moment.circLag d := by
  have hv : (d : ℕ) ≠ 0 := by
    intro h
    exact hd (Fin.val_injective (by simpa using h))
  have hlt := d.isLt
  simp only [Moment.circLag, le_min_iff]
  omega

#print axioms one_le_circLag

/-- The read's raw profile is the Wilson correlation at the CLAMPED coupling, by definition. -/
theorem readEven_rho (a : EvenAp) (β : ℝ) (d : Fin (a.1 + 1)) :
    (readEven a β).ρ d = MassGap.wilsonCorrAt a.1 (max β 0) d := rfl

#print axioms readEven_rho

/-- The lag angle does not see the coupling: `Moment.Read.θ` discards its read and is `2π d /(N+1)`.
Stated so the numerator of the cosine average can be split into a `β`-dependent profile and a
constant weight. -/
theorem readEven_theta (a : EvenAp) (β : ℝ) (d : Fin (a.1 + 1)) :
    (readEven a β).θ d = (readEven a 0).θ d := rfl

#print axioms readEven_theta

/-- The floor is below one. `3 > 1` and the exponent is negative, so the power is a proper fraction —
which is what makes a point mass at lag zero clear it with room. -/
theorem floor_lt_one : (3 : ℝ) ^ (-(1 : ℝ) / 4) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

#print axioms floor_lt_one

/-- The floor is positive. -/
theorem floor_pos : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) :=
  Real.rpow_pos_of_pos (by norm_num) _

#print axioms floor_pos

/-! ## 1. Zero coupling: the cosine average is exactly one

At `β = 0` the state is product Haar and the two plaquettes read disjoint link sets, so the connected
correlation vanishes at every lag of nonzero circle distance
(`PowerTail.wilsonCorrAt_at_zero_coupling`) while the contact value stays strictly positive
(`PowerTail.contact_value_pos_at_zero_coupling`). The normalised read is therefore a point mass at
lag zero, where the angle is zero and the cosine is one. -/

/-- **THE COSINE AVERAGE AT ZERO COUPLING IS ONE**, at every even aperture. No estimate is made: the
profile is a contact term, so the probability vector is the indicator of lag zero. -/
theorem cosAvgEven_at_zero (a : EvenAp) : cosAvgEven a 0 = 1 := by
  have hzero : ∀ d : Fin (a.1 + 1), d ≠ 0 → (readEven a 0).ρ d = 0 := by
    intro d hd
    rw [readEven_rho, max_self]
    exact MassGap.PowerTail.wilsonCorrAt_at_zero_coupling a.1 d (one_le_circLag hd)
  have hpos : 0 < (readEven a 0).ρ 0 := by
    rw [readEven_rho, max_self]
    exact MassGap.PowerTail.contact_value_pos_at_zero_coupling a.1
  have hsum : ∑ d, (readEven a 0).ρ d = (readEven a 0).ρ 0 :=
    Finset.sum_eq_single (0 : Fin (a.1 + 1)) (fun d _ hd => hzero d hd)
      (fun h => absurd (Finset.mem_univ (0 : Fin (a.1 + 1))) h)
  have hp0 : (readEven a 0).p 0 = 1 := by
    simp only [Moment.Read.p, hsum]
    exact div_self (ne_of_gt hpos)
  have hpz : ∀ d : Fin (a.1 + 1), d ≠ 0 → (readEven a 0).p d = 0 := by
    intro d hd
    simp [Moment.Read.p, hzero d hd]
  have hθ0 : (readEven a 0).θ 0 = 0 := by simp [Moment.Read.θ]
  show ∑ d, (readEven a 0).p d * Real.cos ((readEven a 0).θ d) = 1
  rw [Finset.sum_eq_single (0 : Fin (a.1 + 1))
      (fun d _ hd => by rw [hpz d hd, zero_mul])
      (fun h => absurd (Finset.mem_univ (0 : Fin (a.1 + 1))) h),
    hp0, hθ0, Real.cos_zero, mul_one]

#print axioms cosAvgEven_at_zero

/-- **AND THEREFORE THE HYPOTHESIS HOLDS AT ZERO COUPLING**, at every even aperture. -/
theorem confines_at_zero (a : EvenAp) : (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a 0 := by
  rw [cosAvgEven_at_zero]
  exact floor_lt_one

#print axioms confines_at_zero

/-- **THE NEGATIVE HALF-LINE IS THE CLAMP, NOT A RESULT.** `readEven` reads the ensemble at
`max β 0`, so at every nonpositive coupling it is the `β = 0` read and the cosine average is the same
`1`. `EvenAperture.readEven_eq_at_zero` already names this as the price of the restriction; it is
recorded here so that `confines_near_zero` below is not read as symmetric evidence about the
coupling line. -/
theorem cosAvgEven_eq_one_of_nonpos (a : EvenAp) {β : ℝ} (hβ : β ≤ 0) : cosAvgEven a β = 1 := by
  show ∑ d, (readEven a β).p d * Real.cos ((readEven a β).θ d) = 1
  rw [readEven_eq_at_zero a hβ]
  exact cosAvgEven_at_zero a

#print axioms cosAvgEven_eq_one_of_nonpos

/-! ## 2. Continuity in the coupling, and a neighbourhood of zero

`WilsonAnalytic.wilsonSystem_expect_hasDerivAt` differentiates the Gibbs expectation of any bounded
measurable observable in `β`, on the genuine Wilson measure, with no hypothesis whatever — the
Boltzmann weight is positive and the action is bounded, so differentiation under the integral is
dominated by a constant. `corrClay` is a difference of a product expectation and a product of two
expectations, so it inherits continuity; the clamp `max β 0` is continuous; and the denominator of
the read is the second clause of `Complete.wilson_reflection_positive_at_even`, which is strictly
positive at every nonnegative coupling and therefore at every clamped one. -/

/-- The Gibbs expectation of a bounded measurable observable is continuous in the coupling.
`WilsonAnalytic.wilsonSystem_expect_hasDerivAt` gives more — it is differentiable — and this is the
consequence the read needs. -/
theorem continuous_wilsonSystem_expect {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    [DecidableEq Pq] (bd : Pq → List (Lk × Bool))
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hmeas : Measurable O) (M : ℝ) (hbound : ∀ U, |O U| ≤ M) :
    Continuous (fun β : ℝ => (wilsonSystem bd (wilsonDensity (N := N))).expect
      (probHaar (MassGap.SUN.SU N)) β O) :=
  continuous_iff_continuousAt.mpr fun β =>
    (MassGap.WilsonAnalytic.wilsonSystem_expect_hasDerivAt hN bd β O hmeas M hbound).continuousAt

#print axioms continuous_wilsonSystem_expect

/-- The CONNECTED plaquette correlation is continuous in the coupling, on any Wilson system. Three
expectations, each of an observable bounded by the plaquette density's own bound. -/
theorem continuous_wilsonCorrConn {Nc : ℕ} (hNc : Nc ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    [DecidableEq Pq] (bd : Pq → List (Lk × Bool)) (p₀ p : Pq) :
    Continuous (fun β : ℝ => MassGap.WilsonBridge.wilsonCorrConn (Nc := Nc) bd p₀ β p) := by
  have hb : ∀ (q : Pq) (U : (wilsonSystem bd (wilsonDensity (N := Nc))).Config),
      |wilsonPlaqObs (N := Nc) bd q U| ≤ 2 := fun q U =>
    abs_le.mpr ⟨by linarith [wilsonPlaqObs_nonneg hNc bd q U], wilsonPlaqObs_le_two hNc bd q U⟩
  have hprod : ∀ U : (wilsonSystem bd (wilsonDensity (N := Nc))).Config,
      |wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd p U| ≤ 4 := by
    intro U
    rw [abs_mul]
    nlinarith [hb p₀ U, hb p U, abs_nonneg (wilsonPlaqObs (N := Nc) bd p₀ U),
      abs_nonneg (wilsonPlaqObs (N := Nc) bd p U)]
  have h1 := continuous_wilsonSystem_expect hNc bd
      (fun U => wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd p U)
      ((measurable_wilsonPlaqObs bd p₀).mul (measurable_wilsonPlaqObs bd p)) 4 hprod
  have h2 := continuous_wilsonSystem_expect hNc bd (wilsonPlaqObs (N := Nc) bd p₀)
      (measurable_wilsonPlaqObs bd p₀) 2 (hb p₀)
  have h3 := continuous_wilsonSystem_expect hNc bd (wilsonPlaqObs (N := Nc) bd p)
      (measurable_wilsonPlaqObs bd p) 2 (hb p)
  exact h1.sub (h2.mul h3)

#print axioms continuous_wilsonCorrConn

/-- **THE CORRELATION THE SUBSTRATE READ CONSUMES IS CONTINUOUS IN THE COUPLING**, at every aperture
and every lag, with no hypothesis. `wilsonCorrAt N β = corrClay (N+1) β` by definition, and that is
the connected correlation of two explicit plaquettes of the four-dimensional `SU(3)` lattice. -/
theorem continuous_wilsonCorrAt (N : ℕ) (d : Fin (N + 1)) :
    Continuous (fun β : ℝ => MassGap.wilsonCorrAt N β d) := by
  have h := continuous_wilsonCorrConn (Nc := 3) (by norm_num)
    (MassGap.WilsonHypercubic.bd (d := 4) (n := N + 1))
    ((0, 1), (fun _ => 0 : MassGap.WilsonHypercubic.Site 4 (N + 1)))
    ((0, 1), MassGap.WilsonBridge.siteAtHyper 2 d)
  exact h

#print axioms continuous_wilsonCorrAt

/-- **THE COSINE AVERAGE IS CONTINUOUS IN THE COUPLING**, at every even aperture, on all of `ℝ`. A
ratio of finite sums of continuous functions whose denominator is the total mass, strictly positive
by the second clause of the PROVED reflection positivity at every clamped coupling. -/
theorem continuous_cosAvgEven (a : EvenAp) : Continuous (cosAvgEven a) := by
  have hclamp : Continuous (fun β : ℝ => max β 0) := continuous_id.max continuous_const
  have hden : Continuous (fun β : ℝ => ∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d) :=
    continuous_finsetSum _ (fun d _ => (continuous_wilsonCorrAt a.1 d).comp hclamp)
  have hnum : Continuous (fun β : ℝ =>
      ∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d * Real.cos ((readEven a 0).θ d)) :=
    continuous_finsetSum _ (fun d _ =>
      ((continuous_wilsonCorrAt a.1 d).comp hclamp).mul continuous_const)
  have hne : ∀ β : ℝ, (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d) ≠ 0 := fun β =>
    ne_of_gt (MassGap.wilson_reflection_positive_at_even a.1 a.2.choose a.2.choose_spec.1
      a.2.choose_spec.2 (le_max_right β 0)).2
  have key : (cosAvgEven a) = fun β : ℝ =>
      (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d * Real.cos ((readEven a 0).θ d))
        / (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d) := by
    funext β
    have hsumeq : (∑ d', (readEven a β).ρ d')
        = ∑ d', MassGap.wilsonCorrAt a.1 (max β 0) d' := rfl
    show ∑ d, (readEven a β).p d * Real.cos ((readEven a β).θ d) = _
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    show (readEven a β).ρ d / (∑ d', (readEven a β).ρ d') * Real.cos ((readEven a β).θ d) = _
    rw [div_mul_eq_mul_div, readEven_rho, readEven_theta, hsumeq]
  rw [key]
  exact hnum.div hden hne

#print axioms continuous_cosAvgEven

/-- **CONFINEMENT HOLDS ON A NEIGHBOURHOOD OF ZERO COUPLING**, at every even aperture. The radius is
existential and nothing names a value for it: it is whatever the continuity of the Wilson expectation
supplies at the point where the cosine average is exactly one. -/
theorem confines_near_zero (a : EvenAp) :
    ∃ b > 0, ∀ β : ℝ, |β| < b → (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β := by
  have hev : ∀ᶠ β in nhds (0 : ℝ), (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β :=
    (continuous_cosAvgEven a).continuousAt (lt_mem_nhds (confines_at_zero a))
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨b, hb, hball⟩ := hev
  refine ⟨b, hb, fun β hβ => hball ?_⟩
  simpa [Real.dist_eq] using hβ

#print axioms confines_near_zero

/-- **AND ON A WHOLE HALF-LINE BELOW A CUT.** The negative side is the clamp
(`cosAvgEven_eq_one_of_nonpos`), so what `confines_near_zero` gives on `(−b, 0]` is already free; the
content of the cut is entirely on `[0, b)`. -/
theorem confines_below_a_cut (a : EvenAp) :
    ∃ b > 0, ∀ β : ℝ, β < b → (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β := by
  obtain ⟨b, hb, h⟩ := confines_near_zero a
  refine ⟨b, hb, fun β hβ => ?_⟩
  by_cases hle : β ≤ 0
  · rw [cosAvgEven_eq_one_of_nonpos a hle]
    exact floor_lt_one
  · exact h β (by rw [abs_of_pos (not_le.mp hle)]; exact hβ)

#print axioms confines_below_a_cut

/-! ## 3. The closed form at the smallest admissible extent

`EvenAp` carries `N + 1 = 2m` with `2 ≤ m`, so the smallest extent is four. There are four lags, the
angles are `0, π/2, π, 3π/2`, the cosines are `1, 0, −1, 0`, and circle symmetry identifies lag `3`
with lag `1`. The hypothesis at this aperture is therefore a statement about three numbers. -/

/-- The smallest aperture the PROVED reflection positivity admits: extent four.

DERIVED: `3` is `N` with `N + 1 = 4 = 2 * 2`, the smallest even extent carrying `2 ≤ m`. Both are
read off `Complete.wilson_reflection_positive_at_even`'s hypotheses and neither is chosen here —
`EvenAperture.two_le_half_is_load_bearing` is the negative control that extent two does not qualify. -/
abbrev ap4 : EvenAp := ⟨3, 2, rfl, le_refl 2⟩

#print axioms ap4

/-- **THE CLOSED FORM AT EXTENT FOUR.** With `ρ = wilsonCorrAt 3 (max β 0)`,

    cosAvgEven ap4 β = (ρ(0) − ρ(2)) / (ρ(0) + 2ρ(1) + ρ(2)).

The first lag contributes `cos(π/2) = 0` to the numerator and its full weight to the denominator, so
it can only lower the ratio; the whole hypothesis at this aperture is that the contact value exceeds
the antipodal one by enough to carry the first lag's mass. -/
theorem cosAvgEven_extent_four (β : ℝ) :
    cosAvgEven ap4 β
      = (MassGap.wilsonCorrAt 3 (max β 0) 0 - MassGap.wilsonCorrAt 3 (max β 0) 2)
        / (MassGap.wilsonCorrAt 3 (max β 0) 0 + 2 * MassGap.wilsonCorrAt 3 (max β 0) 1
            + MassGap.wilsonCorrAt 3 (max β 0) 2) := by
  have hsym : MassGap.wilsonCorrAt 3 (max β 0) 3 = MassGap.wilsonCorrAt 3 (max β 0) 1 := by
    have h := MassGap.MomentShape.wilsonCorrAt_neg 3 (max β 0) (1 : Fin 4)
    have hneg : (-(1 : Fin 4)) = (3 : Fin 4) := by decide
    rwa [hneg] at h
  have hexp : cosAvgEven ap4 β
      = ∑ d : Fin 4, (MassGap.wilsonCorrAt 3 (max β 0) d
          / (∑ d' : Fin 4, MassGap.wilsonCorrAt 3 (max β 0) d'))
        * Real.cos (2 * Real.pi * ((d : ℕ) : ℝ) / (((3 : ℕ) : ℝ) + 1)) := rfl
  rw [hexp]
  simp only [Fin.sum_univ_four]
  have hd : ((3 : ℕ) : ℝ) + 1 = 4 := by norm_num
  have v0 : (((0 : Fin 4) : ℕ) : ℝ) = 0 := by norm_num
  have v1 : (((1 : Fin 4) : ℕ) : ℝ) = 1 := by norm_num
  have v2 : (((2 : Fin 4) : ℕ) : ℝ) = 2 := by norm_num
  have v3 : (((3 : Fin 4) : ℕ) : ℝ) = 3 := by norm_num
  have c0 : Real.cos (2 * Real.pi * (0 : ℝ) / 4) = 1 := by norm_num
  have c1 : Real.cos (2 * Real.pi * (1 : ℝ) / 4) = 0 := by
    have h : 2 * Real.pi * (1 : ℝ) / 4 = Real.pi / 2 := by ring
    rw [h, Real.cos_pi_div_two]
  have c2 : Real.cos (2 * Real.pi * (2 : ℝ) / 4) = -1 := by
    have h : 2 * Real.pi * (2 : ℝ) / 4 = Real.pi := by ring
    rw [h, Real.cos_pi]
  have c3 : Real.cos (2 * Real.pi * (3 : ℝ) / 4) = 0 := by
    have h : 2 * Real.pi * (3 : ℝ) / 4 = Real.pi + Real.pi / 2 := by ring
    rw [h, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two]
    ring
  rw [hd, v0, v1, v2, v3, c0, c1, c2, c3, hsym]
  have hS : MassGap.wilsonCorrAt 3 (max β 0) 0 + MassGap.wilsonCorrAt 3 (max β 0) 1
        + MassGap.wilsonCorrAt 3 (max β 0) 2 + MassGap.wilsonCorrAt 3 (max β 0) 1
      = MassGap.wilsonCorrAt 3 (max β 0) 0 + 2 * MassGap.wilsonCorrAt 3 (max β 0) 1
        + MassGap.wilsonCorrAt 3 (max β 0) 2 := by ring
  rw [hS]
  ring

#print axioms cosAvgEven_extent_four

/-- **WHAT THE PROVED SHAPE FACTS DO TO THE RATIO AT EXTENT FOUR.**

The tree proves, at this extent and with no further hypothesis, that the profile is nonnegative
(`Complete.wilson_reflection_positive_at_even`), that it is circle-symmetric
(`MomentShape.wilsonCorrAt_neg`), and that it is log-convex
(`LogConvex.corrClay_log_convex_at_extent_four`: `ρ(1)² ≤ ρ(0)ρ(2)`). Those three reduce the whole
hypothesis at extent four to a bound on the SECOND lag alone.

**THE THRESHOLD IS EXACT, NOT FITTED.** With `c = 3^{−1/4}` the identity

    ((1−c)ρ₀ − (1+c)ρ₂)² − 4c²ρ₀ρ₂ = ((1−c)²ρ₀ − (1+c)²ρ₂)(ρ₀ − ρ₂)

is a `ring` identity, and its right factorisation vanishes exactly at `(1+c)²ρ₂ = (1−c)²ρ₀`. So this
hypothesis is the weakest one that log-convexity can carry: at equality the route gives nothing, and
the constant is read off the floor rather than chosen to clear anything.

**WHAT DOES NOT APPLY HERE.** `WeakArm.corrClay_le_at_zero` and `MomentShape.corrClay_even_antitone`
both carry `3 ≤ m`, which is extent six and above. Neither is available at extent four, and this
statement does not use them. -/
theorem confines_extent_four_of_lag_two_small (β : ℝ)
    (h : (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 * MassGap.wilsonCorrAt 3 (max β 0) 2
        < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 * MassGap.wilsonCorrAt 3 (max β 0) 0) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven ap4 β := by
  rw [cosAvgEven_extent_four β]
  have hrp := MassGap.wilson_reflection_positive_at_even 3 2 (by norm_num) (by norm_num)
    (le_max_right β (0 : ℝ))
  set c : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hcdef
  set r0 : ℝ := MassGap.wilsonCorrAt 3 (max β 0) 0 with hr0
  set r1 : ℝ := MassGap.wilsonCorrAt 3 (max β 0) 1 with hr1
  set r2 : ℝ := MassGap.wilsonCorrAt 3 (max β 0) 2 with hr2
  have hc0 : 0 < c := by rw [hcdef]; exact floor_pos
  have hc1 : c < 1 := by rw [hcdef]; exact floor_lt_one
  have h0 : 0 ≤ r0 := by rw [hr0]; exact hrp.1 0
  have h1 : 0 ≤ r1 := by rw [hr1]; exact hrp.1 1
  have h2 : 0 ≤ r2 := by rw [hr2]; exact hrp.1 2
  have hlc : r1 ^ 2 ≤ r0 * r2 := by
    have hh := MassGap.LogConvex.corrClay_log_convex_at_extent_four (max β 0)
    have e1 : ((0 : Fin 4) + 1) = (1 : Fin 4) := by decide
    have e0 : ((0 : Fin 4) + 0) = (0 : Fin 4) := by decide
    have e2 : ((1 : Fin 4) + 1) = (2 : Fin 4) := by decide
    rw [e1, e0, e2] at hh
    rw [hr0, hr1, hr2]
    exact hh
  have hgap : 0 < (1 - c) * r0 - (1 + c) * r2 := by
    nlinarith [h, h0, h2, hc0, hc1, mul_nonneg (sub_nonneg.2 hc1.le) h0]
  have hr : r2 < r0 := by nlinarith [hgap, h2, hc0, hc1]
  have hkey : 0 < ((1 - c) * r0 - (1 + c) * r2) ^ 2 - 4 * c ^ 2 * r0 * r2 := by
    have hid : ((1 - c) * r0 - (1 + c) * r2) ^ 2 - 4 * c ^ 2 * r0 * r2
        = ((1 - c) ^ 2 * r0 - (1 + c) ^ 2 * r2) * (r0 - r2) := by ring
    rw [hid]
    exact mul_pos (by linarith) (by linarith)
  have hq : 4 * c ^ 2 * r1 ^ 2 ≤ 4 * c ^ 2 * (r0 * r2) :=
    mul_le_mul_of_nonneg_left hlc (by positivity)
  have hAsq : (2 * c * r1) ^ 2 < ((1 - c) * r0 - (1 + c) * r2) ^ 2 := by nlinarith [hkey, hq]
  have hnn : 0 ≤ 2 * c * r1 := by positivity
  have hcr : 2 * c * r1 < (1 - c) * r0 - (1 + c) * r2 := by nlinarith [hAsq, hnn, hgap]
  have hD : 0 < r0 + 2 * r1 + r2 := by nlinarith [hgap, h1, h2, hc0, hc1]
  rw [lt_div_iff₀ hD]
  nlinarith [hcr]

#print axioms confines_extent_four_of_lag_two_small

/-! ## 3a. A LARGER EXTENT IS NOT THE SAME PROBLEM — the closed form at extent six

`ApertureRoute` records that the aperture cancels EXACTLY in the substrate route
(`Complete.surplus_ge`'s `hcancel`), so the criterion `(2π)²·substrateRatio/2 < 1 − 3^{−1/4}` carries
no `N`. That is a statement about THAT ROUTE'S SUFFICIENT BOUND, and it does not transfer to
`cosAvgEven` itself, which is checked here rather than assumed.

At extent six the angles are `2πd/6` and the cosines are `1, ½, −½, −1, −½, ½`, so the first lag
enters the NUMERATOR with a positive weight, where at extent four its cosine is exactly zero and it
enters the denominator alone. The two closed forms are therefore genuinely different problems, and
extent four is not automatically the easiest. Nothing here says which extent is easier — that is a
statement about the profiles, which this file does not bound. -/

/-- The next even aperture: extent six.

DERIVED: `5` is `N` with `N + 1 = 6 = 2 * 3`, the next even extent after four carrying `2 ≤ m`. As
with `ap4` both are read off `Complete.wilson_reflection_positive_at_even`'s hypotheses. -/
abbrev ap6 : EvenAp := ⟨5, 3, rfl, by norm_num⟩

#print axioms ap6

/-- **THE CLOSED FORM AT EXTENT SIX.** With `ρ = wilsonCorrAt 5 (max β 0)`,

    cosAvgEven ap6 β = (ρ(0) + ρ(1) − ρ(2) − ρ(3)) / (ρ(0) + 2ρ(1) + 2ρ(2) + ρ(3)).

Compare `cosAvgEven_extent_four`: there `ρ(1)` appears only in the denominator, here it appears in
the numerator with weight `+1`. So the aperture is not a free parameter that the bar ignores — what
`Complete.surplus_ge` makes aperture-free is the substrate route's LOWER BOUND on the cosine average,
not the cosine average. -/
theorem cosAvgEven_extent_six (β : ℝ) :
    cosAvgEven ap6 β
      = (MassGap.wilsonCorrAt 5 (max β 0) 0 + MassGap.wilsonCorrAt 5 (max β 0) 1
            - MassGap.wilsonCorrAt 5 (max β 0) 2 - MassGap.wilsonCorrAt 5 (max β 0) 3)
        / (MassGap.wilsonCorrAt 5 (max β 0) 0 + 2 * MassGap.wilsonCorrAt 5 (max β 0) 1
            + 2 * MassGap.wilsonCorrAt 5 (max β 0) 2 + MassGap.wilsonCorrAt 5 (max β 0) 3) := by
  have hsym5 : MassGap.wilsonCorrAt 5 (max β 0) 5 = MassGap.wilsonCorrAt 5 (max β 0) 1 := by
    have h := MassGap.MomentShape.wilsonCorrAt_neg 5 (max β 0) (1 : Fin 6)
    have hneg : (-(1 : Fin 6)) = (5 : Fin 6) := by decide
    rwa [hneg] at h
  have hsym4 : MassGap.wilsonCorrAt 5 (max β 0) 4 = MassGap.wilsonCorrAt 5 (max β 0) 2 := by
    have h := MassGap.MomentShape.wilsonCorrAt_neg 5 (max β 0) (2 : Fin 6)
    have hneg : (-(2 : Fin 6)) = (4 : Fin 6) := by decide
    rwa [hneg] at h
  have hexp : cosAvgEven ap6 β
      = ∑ d : Fin 6, (MassGap.wilsonCorrAt 5 (max β 0) d
          / (∑ d' : Fin 6, MassGap.wilsonCorrAt 5 (max β 0) d'))
        * Real.cos (2 * Real.pi * ((d : ℕ) : ℝ) / (((5 : ℕ) : ℝ) + 1)) := rfl
  rw [hexp]
  simp only [Fin.sum_univ_six]
  have hd : ((5 : ℕ) : ℝ) + 1 = 6 := by norm_num
  have v0 : (((0 : Fin 6) : ℕ) : ℝ) = 0 := by norm_num
  have v1 : (((1 : Fin 6) : ℕ) : ℝ) = 1 := by norm_num
  have v2 : (((2 : Fin 6) : ℕ) : ℝ) = 2 := by norm_num
  have v3 : (((3 : Fin 6) : ℕ) : ℝ) = 3 := by norm_num
  have v4 : (((4 : Fin 6) : ℕ) : ℝ) = 4 := by norm_num
  have v5 : (((5 : Fin 6) : ℕ) : ℝ) = 5 := by norm_num
  have c0 : Real.cos (2 * Real.pi * (0 : ℝ) / 6) = 1 := by norm_num
  have c1 : Real.cos (2 * Real.pi * (1 : ℝ) / 6) = 1 / 2 := by
    have h : 2 * Real.pi * (1 : ℝ) / 6 = Real.pi / 3 := by ring
    rw [h, Real.cos_pi_div_three]
  have c2 : Real.cos (2 * Real.pi * (2 : ℝ) / 6) = -(1 / 2) := by
    have h : 2 * Real.pi * (2 : ℝ) / 6 = Real.pi - Real.pi / 3 := by ring
    rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]
  have c3 : Real.cos (2 * Real.pi * (3 : ℝ) / 6) = -1 := by
    have h : 2 * Real.pi * (3 : ℝ) / 6 = Real.pi := by ring
    rw [h, Real.cos_pi]
  have c4 : Real.cos (2 * Real.pi * (4 : ℝ) / 6) = -(1 / 2) := by
    have h : 2 * Real.pi * (4 : ℝ) / 6 = Real.pi + Real.pi / 3 := by ring
    rw [h, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]
    ring
  have c5 : Real.cos (2 * Real.pi * (5 : ℝ) / 6) = 1 / 2 := by
    have h : 2 * Real.pi * (5 : ℝ) / 6 = 2 * Real.pi - Real.pi / 3 := by ring
    rw [h, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi, Real.cos_pi_div_three]
    ring
  rw [hd, v0, v1, v2, v3, v4, v5, c0, c1, c2, c3, c4, c5, hsym5, hsym4]
  have hS : MassGap.wilsonCorrAt 5 (max β 0) 0 + MassGap.wilsonCorrAt 5 (max β 0) 1
        + MassGap.wilsonCorrAt 5 (max β 0) 2 + MassGap.wilsonCorrAt 5 (max β 0) 3
        + MassGap.wilsonCorrAt 5 (max β 0) 2 + MassGap.wilsonCorrAt 5 (max β 0) 1
      = MassGap.wilsonCorrAt 5 (max β 0) 0 + 2 * MassGap.wilsonCorrAt 5 (max β 0) 1
        + 2 * MassGap.wilsonCorrAt 5 (max β 0) 2 + MassGap.wilsonCorrAt 5 (max β 0) 3 := by ring
  rw [hS]
  ring

#print axioms cosAvgEven_extent_six

/-! ## 4. What remains

Everything above is about a neighbourhood of zero coupling. `ConfinesAtAnAperture` asks for EVERY
coupling, and that is the whole of what is left. Because the cosine average is continuous and starts
strictly above the floor, the remaining obligation can be stated without an inequality at all. -/

/-- **THE REMAINING OBLIGATION.** At some even aperture the cosine average is never EQUAL to the
entropy floor `3^{−1/4}`.

This is the whole of what is open on this side, and it is EQUIVALENT to `ConfinesAtAnAperture`
(`confinesAtAnAperture_iff_missesTheFloor`), not merely sufficient for it. The equivalence is the
intermediate value theorem against `cosAvgEven_at_zero`: the average is `1` at zero coupling, so a
coupling at which it fell below the floor would force a coupling at which it equalled the floor.

What it says in words: **the cosine average must stay off the floor away from zero coupling.** It is
not proved here and nothing in this file bounds `cosAvgEven` at large `β`. The obstruction is
visible in `cosAvgEven_extent_four` — as the profile flattens, `ρ(2)` approaches `ρ(0)` and the ratio
goes to zero — and `confines_extent_four_of_lag_two_small` is the sharp form of what the tree's
proved shape facts can still carry against it.

DERIVED: `3^{−1/4} = e^{−κ₀YM}` with `κ₀YM = ¼ log 3`, counted off directed cube paths in
`Floor.lean`; it is `ApertureRoute.ConfinesAtAnAperture`'s own constant, carried through unchanged. -/
def MissesTheFloor : Prop :=
  ∃ a : EvenAp, ∀ β : ℝ, cosAvgEven a β ≠ (3 : ℝ) ^ (-(1 : ℝ) / 4)

#print axioms MissesTheFloor

/-- **MISSING THE FLOOR IS ENOUGH.** By the intermediate value theorem on the continuous
`cosAvgEven`, together with its value `1` at zero coupling. -/
theorem confinesAtAnAperture_of_missesTheFloor (h : MissesTheFloor) : ConfinesAtAnAperture := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, fun β => ?_⟩
  by_contra hcon
  rw [not_lt] at hcon
  have hlt : cosAvgEven a β < (3 : ℝ) ^ (-(1 : ℝ) / 4) := lt_of_le_of_ne hcon (ha β)
  have h0 : (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a 0 := confines_at_zero a
  have hcont : ContinuousOn (cosAvgEven a) (Set.uIcc β 0) :=
    (continuous_cosAvgEven a).continuousOn
  have hmem : (3 : ℝ) ^ (-(1 : ℝ) / 4) ∈ Set.uIcc (cosAvgEven a β) (cosAvgEven a 0) := by
    rw [Set.mem_uIcc]
    exact Or.inl ⟨le_of_lt hlt, le_of_lt h0⟩
  obtain ⟨x, _, hx⟩ := intermediate_value_uIcc hcont hmem
  exact ha x hx

#print axioms confinesAtAnAperture_of_missesTheFloor

/-- And it is NECESSARY, trivially — so nothing is strengthened by stating the remainder this way. -/
theorem missesTheFloor_of_confinesAtAnAperture (h : ConfinesAtAnAperture) : MissesTheFloor := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun β => ne_of_gt (ha β)⟩

#print axioms missesTheFloor_of_confinesAtAnAperture

/-- **THE OPEN HYPOTHESIS, RESTATED EXACTLY.** `ConfinesAtAnAperture` and `MissesTheFloor` are the
same statement. The inequality at every coupling has become a non-equality at every coupling, and the
difference is paid for by the continuity of the Wilson expectation and the point mass at zero
coupling — both proved above, both foundational-only. -/
theorem confinesAtAnAperture_iff_missesTheFloor : ConfinesAtAnAperture ↔ MissesTheFloor :=
  ⟨missesTheFloor_of_confinesAtAnAperture, confinesAtAnAperture_of_missesTheFloor⟩

#print axioms confinesAtAnAperture_iff_missesTheFloor

/-- **THE FLAGSHIP FROM THE REMAINING OBLIGATION.** `ApertureRoute.FlagshipAt` — the gap,
non-triviality, `SO(4)` and the continuum object — follows from `MissesTheFloor` alone. -/
theorem flagship_of_missesTheFloor (h : MissesTheFloor) :
    FlagshipAt (confinesAtAnAperture_of_missesTheFloor h) :=
  flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_missesTheFloor

end MassGap.ConfinesZero
