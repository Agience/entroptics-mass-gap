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

* `cosAvgEven_at_zero` — **at zero coupling the cosine average is exactly `1`**, at every even
  aperture. `PowerTail.wilsonCorrAt_at_zero_coupling` kills the correlation at every lag of nonzero
  circle distance (product Haar factorises the two plaquettes), and
  `PowerTail.contact_value_pos_at_zero_coupling` keeps lag `0` strictly positive. So the normalised
  read is a point mass at lag `0`, where `θ = 0` and `cos θ = 1`. Nothing is estimated.
* `cosAvgEven_eq_one_of_nonpos` — and therefore at every nonpositive coupling, because `readEven`
  clamps at `max β 0` (`EvenAperture.readEven_eq_at_zero`). The negative half-line is not an
  achievement; it is the clamp, and it is stated so that `confines_near_zero` is not misread as
  two-sided evidence.
* `continuous_cosAvgEven` — `β ↦ cosAvgEven a β` is continuous on all of `ℝ`, at every even
  aperture. The input is `WilsonAnalytic.wilsonSystem_expect_hasDerivAt`, which differentiates a
  bounded measurable observable's Gibbs expectation in `β` on the genuine Wilson measure with no
  hypothesis at all; `corrClay` is three such expectations, the clamp is continuous, and the
  denominator is the second clause of the proved reflection positivity, so it never vanishes.
* `confines_near_zero`, `confines_below_a_cut` — the hypothesis therefore holds on a neighbourhood
  of zero, and in fact on a half-line `(−∞, b)`. The cut is existential and no numeral is named for
  it: it is whatever the continuity of the Wilson expectation supplies.

## The closed form at the smallest admissible extent

`EvenAp` needs `N + 1 = 2m` with `2 ≤ m`, so the smallest extent is four (`ap4`). There the lag
angles are `0, π/2, π, 3π/2` with cosines `1, 0, −1, 0`, and circle symmetry
(`MomentShape.wilsonCorrAt_neg`) identifies lag `3` with lag `1`. So

    cosAvgEven ap4 β = (ρ(0) − ρ(2)) / (ρ(0) + 2ρ(1) + ρ(2))          (`cosAvgEven_extent_four`)

with `ρ = wilsonCorrAt 3 (max β 0)`. The hypothesis at the smallest aperture is a statement about
three numbers, and lag `1` enters the denominator only — it can only hurt.

`confines_extent_four_of_lag_two_small` is what the tree's proved shape facts do to that ratio.
`LogConvex.corrClay_log_convex_at_extent_four` gives `ρ(1)² ≤ ρ(0)ρ(2)` and
`Complete.wilson_reflection_positive_at_even` gives `ρ ≥ 0`; together they reduce the whole
hypothesis at extent four to a bound on the second lag alone,

    (1 + 3^{−1/4})² ρ(2) < (1 − 3^{−1/4})² ρ(0),

and that threshold is not chosen — it is the exact one, as the identity

    ((1−c)ρ₀ − (1+c)ρ₂)² − 4c²ρ₀ρ₂ = ((1−c)²ρ₀ − (1+c)²ρ₂)(ρ₀ − ρ₂)

shows by vanishing at it. `WeakArm.corrClay_le_at_zero` and `MomentShape.corrClay_even_antitone`
DO not apply here: both carry `3 ≤ m`, which is extent six and above. At extent four the only shape
facts available are nonnegativity, circle symmetry and log-convexity.

## The restatement as a non-equality

`MissesTheFloor` says that at some even aperture the cosine average is never equal to `3^(-1/4)`.
`confinesAtAnAperture_iff_missesTheFloor` proves it equivalent to `ConfinesAtAnAperture`: the
forward direction is trivial, and the reverse is the intermediate value theorem against
`cosAvgEven_at_zero` and `continuous_cosAvgEven`, since a coupling at which the average fell below
the floor would force one at which it equalled the floor. So the inequality at every coupling and
the non-equality at every coupling are the same statement.

No declaration here bounds `cosAvgEven` at large `β`.

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

/-- `1 ≤ Moment.circLag d` for every lag `d ≠ 0`. `circLag d` is `min d (N + 1 - d)`, and both
entries are at least one exactly when `d ≠ 0`.

DERIVED: `1` is the least circle distance a lag other than the origin can have; `0` is the origin
lag the hypothesis excludes; `N + 1` is the lag arity, `Fin (N + 1)` indexing lags `0 … N`. -/
theorem one_le_circLag {N : ℕ} {d : Fin (N + 1)} (hd : d ≠ 0) : 1 ≤ Moment.circLag d := by
  have hv : (d : ℕ) ≠ 0 := by
    intro h
    exact hd (Fin.val_injective (by simpa using h))
  have hlt := d.isLt
  simp only [Moment.circLag, le_min_iff]
  omega

#print axioms one_le_circLag

/-- `(readEven a β).ρ d = wilsonCorrAt a.1 (max β 0) d`, by `rfl`: the read's raw profile is the
Wilson correlation at the clamped coupling.

DERIVED: `1` in `a.1` is the `EvenAp` projection to the extent index and in `Fin (a.1 + 1)` the lag
arity offset; `0` is the clamp's lower end. -/
theorem readEven_rho (a : EvenAp) (β : ℝ) (d : Fin (a.1 + 1)) :
    (readEven a β).ρ d = MassGap.wilsonCorrAt a.1 (max β 0) d := rfl

#print axioms readEven_rho

/-- `(readEven a β).θ d = (readEven a 0).θ d`, by `rfl`: the lag angle does not depend on the
coupling, `Moment.Read.θ` being `2π d / (N + 1)`. It lets the numerator of the cosine average split
into a `β`-dependent profile and a constant weight.

DERIVED: `1` in `a.1` is the `EvenAp` projection and in `Fin (a.1 + 1)` the lag arity offset; `0` is
the coupling the angle is compared at. -/
theorem readEven_theta (a : EvenAp) (β : ℝ) (d : Fin (a.1 + 1)) :
    (readEven a β).θ d = (readEven a 0).θ d := rfl

#print axioms readEven_theta

/-- `(3 : ℝ) ^ (-(1 : ℝ) / 4) < 1`, by `Real.rpow_lt_one_of_one_lt_of_neg`: the base exceeds one and
the exponent is negative. This is what lets a point mass at lag zero, whose cosine average is `1`,
clear the floor.

DERIVED: `3`, `1` and `4` form the entropy floor `3 ^ (-(1 : ℝ) / 4) = e^(-κ₀YM)` with
`κ₀YM = ¼ log 3`; the final `1` is the level it is shown to fall below. -/
theorem floor_lt_one : (3 : ℝ) ^ (-(1 : ℝ) / 4) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

#print axioms floor_lt_one

/-- `0 < (3 : ℝ) ^ (-(1 : ℝ) / 4)`, by `Real.rpow_pos_of_pos`.

DERIVED: `0` is the level the floor is shown to exceed; `3`, `1` and `4` form the entropy floor
`3 ^ (-(1 : ℝ) / 4) = e^(-κ₀YM)`. -/
theorem floor_pos : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) :=
  Real.rpow_pos_of_pos (by norm_num) _

#print axioms floor_pos

/-! ## 1. Zero coupling: the cosine average is exactly one

At `β = 0` the state is product Haar and the two plaquettes read disjoint link sets, so the connected
correlation vanishes at every lag of nonzero circle distance
(`PowerTail.wilsonCorrAt_at_zero_coupling`) while the contact value stays strictly positive
(`PowerTail.contact_value_pos_at_zero_coupling`). The normalised read is therefore a point mass at
lag zero, where the angle is zero and the cosine is one. -/

/-- `cosAvgEven a 0 = 1` at every even aperture `a`. `PowerTail.wilsonCorrAt_at_zero_coupling` makes
the profile vanish at every lag of nonzero circle distance, which by `one_le_circLag` is every lag
but `0`, and `PowerTail.contact_value_pos_at_zero_coupling` keeps the contact value strictly
positive. The probability vector is therefore the indicator of lag `0`, where `θ 0 = 0` and
`cos 0 = 1`. No estimate is made.

DERIVED: `0` is the coupling and the contact lag; `1` is `cos 0`, the value the average takes. -/
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

/-- `3 ^ (-(1 : ℝ) / 4) < cosAvgEven a 0` at every even aperture, from `cosAvgEven_at_zero` and
`floor_lt_one`.

DERIVED: `3`, `1` and `4` form the entropy floor; `0` is the coupling. -/
theorem confines_at_zero (a : EvenAp) : (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a 0 := by
  rw [cosAvgEven_at_zero]
  exact floor_lt_one

#print axioms confines_at_zero

/-- `cosAvgEven a β = 1` at every `β ≤ 0`. `readEven` reads the ensemble at `max β 0`, so at a
nonpositive coupling it is the `β = 0` read (`EvenAperture.readEven_eq_at_zero`) and
`cosAvgEven_at_zero` applies.

The value on the negative half-line is therefore the clamp's, not a property of the ensemble at
negative coupling.

DERIVED: `0` is the upper end of the coupling range and the clamp's lower end; `1` is the value the
average takes. -/
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

/-- The Gibbs expectation of a measurable observable bounded by `M` is continuous in the coupling,
on any Wilson system with `N ≠ 0`. It is the `continuousAt` of
`WilsonAnalytic.wilsonSystem_expect_hasDerivAt`, which gives differentiability.

DERIVED: `0` is the colour count value the hypothesis `hN` excludes. -/
theorem continuous_wilsonSystem_expect {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    [DecidableEq Pq] (bd : Pq → List (Lk × Bool))
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hmeas : Measurable O) (M : ℝ) (hbound : ∀ U, |O U| ≤ M) :
    Continuous (fun β : ℝ => (wilsonSystem bd (wilsonDensity (N := N))).expect
      (probHaar (MassGap.SUN.SU N)) β O) :=
  continuous_iff_continuousAt.mpr fun β =>
    (MassGap.WilsonAnalytic.wilsonSystem_expect_hasDerivAt hN bd β O hmeas M hbound).continuousAt

#print axioms continuous_wilsonSystem_expect

/-- The connected plaquette correlation `wilsonCorrConn bd p₀ · p` is continuous in the coupling, on
any Wilson system with `Nc ≠ 0`. It is a difference of a product expectation and a product of two
expectations, each continuous by `continuous_wilsonSystem_expect`; the bounds `2` on a single
plaquette observable and `4` on the product come from `wilsonPlaqObs_nonneg` and
`wilsonPlaqObs_le_two`.

DERIVED: `0` is the colour count value the hypothesis `hNc` excludes. The bounds `2` and `4` appear
in the proof, where `2` is `wilsonPlaqObs_le_two` and `4` its square. -/
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

/-- `fun β => wilsonCorrAt N β d` is continuous, at every aperture `N` and every lag `d`, with no
hypothesis. `wilsonCorrAt N β` is `corrClay (N + 1) β` by definition, the connected correlation of
two explicit plaquettes of the four-dimensional `SU(3)` lattice, so
`continuous_wilsonCorrConn` at `Nc = 3` applies.

DERIVED: `1` in `Fin (N + 1)` is the lag arity offset. The `3`, `4`, `(0, 1)` and `2` of the
instantiation appear in the proof term and are `wilsonCorrAt`'s own. -/
theorem continuous_wilsonCorrAt (N : ℕ) (d : Fin (N + 1)) :
    Continuous (fun β : ℝ => MassGap.wilsonCorrAt N β d) := by
  have h := continuous_wilsonCorrConn (Nc := 3) (by norm_num)
    (MassGap.WilsonHypercubic.bd (d := 4) (n := N + 1))
    ((0, 1), (fun _ => 0 : MassGap.WilsonHypercubic.Site 4 (N + 1)))
    ((0, 1), MassGap.WilsonBridge.siteAtHyper 2 d)
  exact h

#print axioms continuous_wilsonCorrAt

/-- **The connected plaquette correlation is differentiable in the coupling**, on any Wilson system.

The strict upgrade of `continuous_wilsonCorrConn`, by the same three expectations: the Gibbs
expectation of a bounded measurable observable has a derivative in `β`
(`WilsonAnalytic.wilsonSystem_expect_hasDerivAt`, whose derivative is minus the connected correlation
with the action), and `wilsonCorrConn` is a difference of a product expectation and a product of
expectations.

DERIVED: `0` is the colour count value the hypothesis `hNc` excludes, the only numeral in the
statement. The `2` and `4` of the proof are `wilsonPlaqObs_le_two`'s bound on a single plaquette
density and its square, the bound on a product of two, read exactly as
`continuous_wilsonCorrConn` reads them. Neither is chosen here. -/
theorem differentiable_wilsonCorrConn {Nc : ℕ} (hNc : Nc ≠ 0) {Lk Pq : Type} [Fintype Lk]
    [Fintype Pq] [DecidableEq Pq] (bd : Pq → List (Lk × Bool)) (p₀ p : Pq) :
    Differentiable ℝ (fun β : ℝ => MassGap.WilsonBridge.wilsonCorrConn (Nc := Nc) bd p₀ β p) := by
  have hb : ∀ (q : Pq) (U : (wilsonSystem bd (wilsonDensity (N := Nc))).Config),
      |wilsonPlaqObs (N := Nc) bd q U| ≤ 2 := fun q U =>
    abs_le.mpr ⟨by linarith [wilsonPlaqObs_nonneg hNc bd q U], wilsonPlaqObs_le_two hNc bd q U⟩
  have hprod : ∀ U : (wilsonSystem bd (wilsonDensity (N := Nc))).Config,
      |wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd p U| ≤ 4 := by
    intro U
    rw [abs_mul]
    nlinarith [hb p₀ U, hb p U, abs_nonneg (wilsonPlaqObs (N := Nc) bd p₀ U),
      abs_nonneg (wilsonPlaqObs (N := Nc) bd p U)]
  intro β
  have h1 := (MassGap.WilsonAnalytic.wilsonSystem_expect_hasDerivAt hNc bd β
      (fun U => wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd p U)
      ((measurable_wilsonPlaqObs bd p₀).mul (measurable_wilsonPlaqObs bd p)) 4
      hprod).differentiableAt
  have h2 := (MassGap.WilsonAnalytic.wilsonSystem_expect_hasDerivAt hNc bd β
      (wilsonPlaqObs (N := Nc) bd p₀) (measurable_wilsonPlaqObs bd p₀) 2 (hb p₀)).differentiableAt
  have h3 := (MassGap.WilsonAnalytic.wilsonSystem_expect_hasDerivAt hNc bd β
      (wilsonPlaqObs (N := Nc) bd p) (measurable_wilsonPlaqObs bd p) 2 (hb p)).differentiableAt
  exact h1.sub (h2.mul h3)

#print axioms differentiable_wilsonCorrConn

/-- `fun β => wilsonCorrAt N β d` is differentiable on `ℝ`, at every aperture `N` and every lag `d`,
with no hypothesis. It is `differentiable_wilsonCorrConn` at `Nc = 3` on the Clay lattice's boundary
map, and strengthens `continuous_wilsonCorrAt`.

DERIVED: `1` in `Fin (N + 1)` is the lag arity offset, the only numeral in the statement. In the
proof term, `3` is `SU(3)`'s rank and `4` the dimension, both the Clay problem's own data, `(0, 1)`
is the plaquette's plane and `2` the transverse direction the lag runs along; all are
`wilsonCorrAt`'s, inherited through `corrClay`, and identical to `continuous_wilsonCorrAt`'s. -/
theorem differentiable_wilsonCorrAt (N : ℕ) (d : Fin (N + 1)) :
    Differentiable ℝ (fun β : ℝ => MassGap.wilsonCorrAt N β d) :=
  differentiable_wilsonCorrConn (Nc := 3) (by norm_num)
    (MassGap.WilsonHypercubic.bd (d := 4) (n := N + 1))
    ((0, 1), (fun _ => 0 : MassGap.WilsonHypercubic.Site 4 (N + 1)))
    ((0, 1), MassGap.WilsonBridge.siteAtHyper 2 d)

#print axioms differentiable_wilsonCorrAt

/-- `d2At N` is differentiable at every positive coupling, at every aperture. This is the shape
`Interior.d2_lipschitz_of_deriv_bound` and `Interior.d2_le_of_analytic_grid` take as their `hdiff`
hypothesis on an interval `Set.Icc a b` with `0 < a`.

On a neighbourhood of `β > 0` the clamp in `readYMAt` is inert, so `d2At N x` is
`∑ d, (wilsonCorrAt N x d / ∑ d', wilsonCorrAt N x d') * (circLag d) ^ 2` there, with `circLag d` a
natural number not depending on `x`. Numerator and denominator are finite sums of
`differentiable_wilsonCorrAt`, and the denominator is nonzero at `β` by `(readYMAt N β).hpos`.

Scope: the statement is at `0 < β`, where `Interior`'s grids on `Set.Icc a b` with `0 < a` use it.
Below zero `d2At N` is constant (the `β = 0` read), so its left derivative at `0` is `0`; its right
derivative at `0` is the unclamped ratio's.

The proof uses `(readYMAt N β).hpos`, so this declaration carries
`wilson_reflection_positive_at`, which `readYMAt` is the entry point for;
`differentiable_wilsonCorrConn` and `differentiable_wilsonCorrAt` do not.

DERIVED: the `0` in `0 < β` is the clamp point of `readYMAt`, strictly excluded so that a
neighbourhood of `β` lies on the nonnegative range. The `2` inside `d2At` is the exponent of the
circle distance, the second moment, fixed by that definition. -/
theorem differentiable_d2At (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    DifferentiableAt ℝ (MassGap.d2At N) β := by
  have hden : DifferentiableAt ℝ
      (fun x : ℝ => ∑ d' : Fin (N + 1), MassGap.wilsonCorrAt N x d') β := by
    have hfn : (fun x : ℝ => ∑ d' : Fin (N + 1), MassGap.wilsonCorrAt N x d')
        = ∑ d' : Fin (N + 1), (fun x : ℝ => MassGap.wilsonCorrAt N x d') := by
      funext x
      simp only [Finset.sum_apply]
    rw [hfn]
    exact DifferentiableAt.sum (fun d' _ => differentiable_wilsonCorrAt N d' β)
  have hne : (∑ d' : Fin (N + 1), MassGap.wilsonCorrAt N β d') ≠ 0 := by
    have h := (MassGap.readYMAt N β).hpos
    simp only [MassGap.readYMAt_rho_of_nonneg N hβ.le] at h
    exact ne_of_gt h
  have hg : DifferentiableAt ℝ
      (fun x : ℝ => ∑ d : Fin (N + 1),
        MassGap.wilsonCorrAt N x d / (∑ d' : Fin (N + 1), MassGap.wilsonCorrAt N x d')
          * (Moment.circLag d : ℝ) ^ 2) β := by
    have hfn : (fun x : ℝ => ∑ d : Fin (N + 1),
          MassGap.wilsonCorrAt N x d / (∑ d' : Fin (N + 1), MassGap.wilsonCorrAt N x d')
            * (Moment.circLag d : ℝ) ^ 2)
        = ∑ d : Fin (N + 1), (fun x : ℝ =>
          MassGap.wilsonCorrAt N x d / (∑ d' : Fin (N + 1), MassGap.wilsonCorrAt N x d')
            * (Moment.circLag d : ℝ) ^ 2) := by
      funext x
      simp only [Finset.sum_apply]
    rw [hfn]
    exact DifferentiableAt.sum
      (fun d _ => ((differentiable_wilsonCorrAt N d β).div hden hne).mul_const _)
  refine hg.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hβ] with x hx
  show ∑ d : Fin (N + 1), (MassGap.readYMAt N x).p d * (Moment.circLag d : ℝ) ^ 2 = _
  simp only [Moment.Read.p, MassGap.readYMAt_rho_of_nonneg N hx.le]

#print axioms differentiable_d2At

/-- The Gibbs expectation of a measurable observable bounded by `M` is Lipschitz in the coupling
with constant `4 * M * Fintype.card Pq`, on any Wilson system with `N ≠ 0`. The derivative is minus
the connected correlation with the action (`wilsonSystem_expect_hasDerivAt`),
`cov_bound_extensive` bounds it by `4 * M * #Plaq` with no further hypothesis, and
`Convex.norm_image_sub_le_of_norm_deriv_le` on `Set.univ` turns that into the Lipschitz bound.

The constant is extensive: it carries `Fintype.card Pq`, so it grows with the volume.
`WilsonAnalytic.expect_lipschitz_local` is the version without that factor, under a clustering
hypothesis. `WilsonAnalytic.expect_lipschitz` is the same statement for `sysReal` alone.

DERIVED: `0` is the colour count value the hypothesis `hN` excludes; `4` is
`cov_bound_extensive`'s own factor, from the plaquette density's range `[0, 2]` doubled. Neither is
chosen here. -/
theorem wilsonSystem_expect_lipschitz {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk]
    [Fintype Pq] (bd : Pq → List (Lk × Bool))
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hmeas : Measurable O) (M : ℝ) (hbound : ∀ U, |O U| ≤ M) (x y : ℝ) :
    |(wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) x O
        - (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) y O|
      ≤ (4 * M * (Fintype.card Pq : ℝ)) * |x - y| := by
  have hdiff : ∀ z ∈ (Set.univ : Set ℝ),
      DifferentiableAt ℝ (fun s : ℝ => (wilsonSystem bd (wilsonDensity (N := N))).expect
        (probHaar (MassGap.SUN.SU N)) s O) z :=
    fun z _ => (MassGap.WilsonAnalytic.wilsonSystem_expect_hasDerivAt hN bd z O hmeas M
      hbound).differentiableAt
  have hbnd : ∀ z ∈ (Set.univ : Set ℝ),
      ‖deriv (fun s : ℝ => (wilsonSystem bd (wilsonDensity (N := N))).expect
        (probHaar (MassGap.SUN.SU N)) s O) z‖ ≤ 4 * M * (Fintype.card Pq : ℝ) := by
    intro z _
    rw [(MassGap.WilsonAnalytic.wilsonSystem_expect_hasDerivAt hN bd z O hmeas M hbound).deriv,
      Real.norm_eq_abs, abs_neg]
    exact MassGap.WilsonAnalytic.cov_bound_extensive hN bd z O hmeas M hbound
  have h := (convex_univ (𝕜 := ℝ)).norm_image_sub_le_of_norm_deriv_le hdiff hbnd
    (Set.mem_univ y) (Set.mem_univ x)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact h

#print axioms wilsonSystem_expect_lipschitz

/-- **The connected plaquette correlation is lipschitz in the coupling**, with an explicit constant.

`wilsonCorrConn = ⟨φ₀φ⟩ − ⟨φ₀⟩⟨φ⟩`, three expectations. Each is Lipschitz by
`wilsonSystem_expect_lipschitz`, and the product of two is handled by
`|f(x)g(x) − f(y)g(y)| ≤ |f(x)|·|g(x)−g(y)| + |g(y)|·|f(x)−f(y)|`, the magnitudes coming from
`wilsonSystem_expect_abs_le`.

DERIVED: `0` is the colour count value the hypothesis `hNc` excludes; `48` is not chosen — it is
`16 + 2·8 + 2·8` read off the three terms, where `16 = 4·4` is the product observable's Lipschitz
constant, `8 = 4·2` each single plaquette's, and the two `2`s are the magnitudes
`wilsonPlaqObs_le_two` supplies. In the proof, `4` is the product's bound and `2` a single
plaquette's. -/
theorem lipschitz_wilsonCorrConn {Nc : ℕ} (hNc : Nc ≠ 0) {Lk Pq : Type} [Fintype Lk]
    [Fintype Pq] [DecidableEq Pq] (bd : Pq → List (Lk × Bool)) (p₀ p : Pq) (x y : ℝ) :
    |MassGap.WilsonBridge.wilsonCorrConn (Nc := Nc) bd p₀ x p
        - MassGap.WilsonBridge.wilsonCorrConn (Nc := Nc) bd p₀ y p|
      ≤ (48 * (Fintype.card Pq : ℝ)) * |x - y| := by
  have hb : ∀ (q : Pq) (U : (wilsonSystem bd (wilsonDensity (N := Nc))).Config),
      |wilsonPlaqObs (N := Nc) bd q U| ≤ 2 := fun q U =>
    abs_le.mpr ⟨by linarith [wilsonPlaqObs_nonneg hNc bd q U], wilsonPlaqObs_le_two hNc bd q U⟩
  have hprod : ∀ U : (wilsonSystem bd (wilsonDensity (N := Nc))).Config,
      |wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd p U| ≤ 4 := by
    intro U
    rw [abs_mul]
    nlinarith [hb p₀ U, hb p U, abs_nonneg (wilsonPlaqObs (N := Nc) bd p₀ U),
      abs_nonneg (wilsonPlaqObs (N := Nc) bd p U)]
  set V : ℝ := (Fintype.card Pq : ℝ) with hV
  have hV0 : 0 ≤ V := by positivity
  have hxy : 0 ≤ |x - y| := abs_nonneg _
  -- the three Lipschitz bounds
  have L1 := wilsonSystem_expect_lipschitz hNc bd
      (fun U => wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd p U)
      ((measurable_wilsonPlaqObs bd p₀).mul (measurable_wilsonPlaqObs bd p)) 4 hprod x y
  have L2 := wilsonSystem_expect_lipschitz hNc bd (wilsonPlaqObs (N := Nc) bd p₀)
      (measurable_wilsonPlaqObs bd p₀) 2 (hb p₀) x y
  have L3 := wilsonSystem_expect_lipschitz hNc bd (wilsonPlaqObs (N := Nc) bd p)
      (measurable_wilsonPlaqObs bd p) 2 (hb p) x y
  -- the two magnitudes
  have M2 := wilsonSystem_expect_abs_le hNc bd x (wilsonPlaqObs (N := Nc) bd p₀)
      (measurable_wilsonPlaqObs bd p₀) 2 (hb p₀)
  have M3 := wilsonSystem_expect_abs_le hNc bd y (wilsonPlaqObs (N := Nc) bd p)
      (measurable_wilsonPlaqObs bd p) 2 (hb p)
  set A : ℝ → ℝ := fun s => (wilsonSystem bd (wilsonDensity (N := Nc))).expect
    (probHaar (MassGap.SUN.SU Nc)) s
      (fun U => wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd p U) with hA
  set F : ℝ → ℝ := fun s => (wilsonSystem bd (wilsonDensity (N := Nc))).expect
    (probHaar (MassGap.SUN.SU Nc)) s (wilsonPlaqObs (N := Nc) bd p₀) with hF
  set G : ℝ → ℝ := fun s => (wilsonSystem bd (wilsonDensity (N := Nc))).expect
    (probHaar (MassGap.SUN.SU Nc)) s (wilsonPlaqObs (N := Nc) bd p) with hG
  have habs : ∀ u v : ℝ, |u + v| ≤ |u| + |v| := by
    intro u v
    first
      | exact abs_add u v
      | exact abs_add_le u v
      | exact abs_add' u v
  show |(A x - F x * G x) - (A y - F y * G y)| ≤ (48 * V) * |x - y|
  have hsplit : (A x - F x * G x) - (A y - F y * G y)
      = (A x - A y) + (-(F x * (G x - G y) + G y * (F x - F y))) := by ring
  rw [hsplit]
  have hstep : |(A x - A y) + (-(F x * (G x - G y) + G y * (F x - F y)))|
      ≤ |A x - A y| + (|F x| * |G x - G y| + |G y| * |F x - F y|) := by
    refine le_trans (habs _ _) ?_
    rw [abs_neg]
    gcongr
    refine le_trans (habs _ _) ?_
    rw [abs_mul, abs_mul]
  refine le_trans hstep ?_
  have h1 : |A x - A y| ≤ (4 * 4 * V) * |x - y| := by simpa [hA] using L1
  have h2 : |G x - G y| ≤ (4 * 2 * V) * |x - y| := by simpa [hG] using L3
  have h3 : |F x - F y| ≤ (4 * 2 * V) * |x - y| := by simpa [hF] using L2
  have h4 : |F x| ≤ 2 := by simpa [hF] using M2
  have h5 : |G y| ≤ 2 := by simpa [hG] using M3
  nlinarith [abs_nonneg (A x - A y), abs_nonneg (F x - F y), abs_nonneg (G x - G y),
    abs_nonneg (F x), abs_nonneg (G y), hxy, hV0]

#print axioms lipschitz_wilsonCorrConn

/-- `|wilsonCorrAt N x d - wilsonCorrAt N y d| ≤ 48 * Fintype.card (Plaq 4 (N + 1)) * |x - y|`, at
every aperture `N` and every lag `d`, with no hypothesis. It is `lipschitz_wilsonCorrConn` at
`Nc = 3` on the Clay lattice's boundary map.

The constant is extensive: it carries the plaquette count of the extent-`(N + 1)` lattice, so it
grows with the aperture.

DERIVED: `48` is `lipschitz_wilsonCorrConn`'s constant, derived there; `4` in `Plaq 4 (N + 1)` is
the dimension and `1` the lag arity offset in `N + 1`. In the proof term, `3` is `SU(3)`'s rank,
`(0, 1)` the plaquette's plane and `2` the transverse direction, all `wilsonCorrAt`'s own, exactly
as in `differentiable_wilsonCorrAt`. -/
theorem lipschitz_wilsonCorrAt (N : ℕ) (d : Fin (N + 1)) (x y : ℝ) :
    |MassGap.wilsonCorrAt N x d - MassGap.wilsonCorrAt N y d|
      ≤ (48 * (Fintype.card (MassGap.WilsonHypercubic.Plaq 4 (N + 1)) : ℝ)) * |x - y| :=
  lipschitz_wilsonCorrConn (Nc := 3) (by norm_num)
    (MassGap.WilsonHypercubic.bd (d := 4) (n := N + 1))
    ((0, 1), (fun _ => 0 : MassGap.WilsonHypercubic.Site 4 (N + 1)))
    ((0, 1), MassGap.WilsonBridge.siteAtHyper 2 d) x y

#print axioms lipschitz_wilsonCorrAt

/-- On a compact coupling range `Icc a b` with `0 ≤ a`, there is an `m > 0` with
`m ≤ ∑ d : Fin (N + 1), wilsonCorrAt N β d` at every aperture `N` and every `β ∈ Icc a b`. The
witness is `exp (-(128 * b)) * δ₀`: every `wilsonCorrAt N β d` is nonnegative, so the sum is at
least the contact term, `InfiniteVolume.exists_uniform_contact_floor` bounds that below by
`exp (-(128 * β)) * δ₀`, and the exponential is decreasing, so the value at `b` serves throughout.

`m` is bound outside the quantifier over `N` and over `β`. `Moment.Read.hpos` gives `0 < ∑ ρ` with
no constant, which a quotient estimate cannot use.

DERIVED: `0` is the sign condition on `a`, the strict positivity asserted of `m`, and the contact
lag; `1` is the lag arity offset in `Fin (N + 1)`. In the proof, `128` is
`exists_uniform_contact_floor`'s own exponent — `16·dim` at `dim = 4`, doubled, which is
`StrongCoupling.touchDeg_bd_le`'s plaquette-touch count. None is chosen here. -/
theorem exists_profile_sum_floor {a b : ℝ} (ha : 0 ≤ a) :
    ∃ m : ℝ, 0 < m ∧ ∀ (N : ℕ), ∀ β ∈ Set.Icc a b,
      m ≤ ∑ d : Fin (N + 1), MassGap.wilsonCorrAt N β d := by
  obtain ⟨δ₀, hδ₀, hfloor⟩ := MassGap.InfiniteVolume.exists_uniform_contact_floor
  refine ⟨Real.exp (-(128 * b)) * δ₀, mul_pos (Real.exp_pos _) hδ₀, ?_⟩
  intro N β hβ
  obtain ⟨hab, hbb⟩ := hβ
  have hβ0 : 0 ≤ β := le_trans ha hab
  have hmono : Real.exp (-(128 * b)) ≤ Real.exp (-(128 * β)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hcontact : Real.exp (-(128 * β)) * δ₀ ≤ MassGap.wilsonCorrAt N β 0 :=
    hfloor N β hβ0
  have hterm : Real.exp (-(128 * b)) * δ₀ ≤ MassGap.wilsonCorrAt N β 0 :=
    le_trans (mul_le_mul_of_nonneg_right hmono hδ₀.le) hcontact
  refine le_trans hterm ?_
  refine Finset.single_le_sum (f := fun d : Fin (N + 1) => MassGap.wilsonCorrAt N β d) ?_
    (Finset.mem_univ (0 : Fin (N + 1)))
  intro d _
  have h := (MassGap.readYMAt N β).hρ d
  rwa [MassGap.readYMAt_rho_of_nonneg N hβ0] at h

#print axioms exists_profile_sum_floor

/-- **The zero-coupling profile is a delta at lag zero, at every aperture.**

`PowerTail.wilsonCorrAt_at_zero_coupling` kills every weight whose circle distance is at least one,
and `one_le_circLag` says that is exactly the lags other than `0`. No parity condition enters, so
this holds where the `EvenAp` family cannot reach — in particular at `nCorrYM = 16`, whose extent
`17` is odd and which is therefore **not** an `EvenAp`.

DERIVED: `0` is the lag the hypothesis excludes, the coupling, and the value the profile takes;
`1` is the lag arity offset in `Fin (N + 1)`. In the proof, `1` is also `one_le_circLag`'s
threshold. Nothing is chosen. -/
theorem profile_at_zero_coupling_eq_zero (N : ℕ) {d : Fin (N + 1)} (hd : d ≠ 0) :
    (MassGap.readYMAt N 0).ρ d = 0 := by
  rw [MassGap.readYMAt_rho_of_nonneg N le_rfl]
  exact MassGap.PowerTail.wilsonCorrAt_at_zero_coupling N d (one_le_circLag hd)

#print axioms profile_at_zero_coupling_eq_zero

/-- `cosAvgYMAt N 0 = 1` at every aperture `N`, with no parity condition.
`profile_at_zero_coupling_eq_zero` makes the profile a delta at lag zero, so `p 0 = 1` by
`Moment.Read.p_sum` and `p d = 0` elsewhere, while `θ 0 = 2π · 0 / (N + 1) = 0` and `cos 0 = 1`.

`cosAvgEven_at_zero` is the same statement for an `EvenAp`. This version applies at every `N`,
including apertures of odd extent such as the pinned `nCorrYM = 16`, which is not an `EvenAp`.

DERIVED: `0` is the coupling; `1` is `cos 0`, the value the average takes. Nothing is chosen. -/
theorem cosAvgYMAt_at_zero_coupling (N : ℕ) : MassGap.cosAvgYMAt N 0 = 1 := by
  have hsum : ∀ d : Fin (N + 1), d ≠ 0 →
      (MassGap.readYMAt N 0).p d * Real.cos ((MassGap.readYMAt N 0).θ d) = 0 := by
    intro d hd
    have hρ : (MassGap.readYMAt N 0).ρ d = 0 := profile_at_zero_coupling_eq_zero N hd
    have hp : (MassGap.readYMAt N 0).p d = 0 := by
      show (MassGap.readYMAt N 0).ρ d / _ = 0
      rw [hρ, zero_div]
    rw [hp, zero_mul]
  have hone : (MassGap.readYMAt N 0).p 0 = 1 := by
    have h := (MassGap.readYMAt N 0).p_sum
    rw [Finset.sum_eq_single (0 : Fin (N + 1))] at h
    · exact h
    · intro d _ hd
      show (MassGap.readYMAt N 0).ρ d / _ = 0
      rw [profile_at_zero_coupling_eq_zero N hd, zero_div]
    · intro hmem
      exact absurd (Finset.mem_univ (0 : Fin (N + 1))) hmem
  have hθ0 : (MassGap.readYMAt N 0).θ 0 = 0 := by
    show 2 * Real.pi * ((0 : Fin (N + 1)) : ℝ) / ((N : ℝ) + 1) = 0
    simp
  show ∑ d, (MassGap.readYMAt N 0).p d * Real.cos ((MassGap.readYMAt N 0).θ d) = 1
  rw [Finset.sum_eq_single (0 : Fin (N + 1))]
  · rw [hone, hθ0, Real.cos_zero, mul_one]
  · intro d _ hd
    exact hsum d hd
  · intro hmem
    exact absurd (Finset.mem_univ (0 : Fin (N + 1))) hmem

#print axioms cosAvgYMAt_at_zero_coupling

/-- `μYMAt N 0 < κ₀YM` at every aperture `N`, with no parity restriction.
`μYMAt N 0 = -log (cosAvgYMAt N 0) = -log 1 = 0` by `cosAvgYMAt_at_zero_coupling`, and `κ₀YM_pos`
puts the floor above zero.

The statement is at the single coupling `0`. `A1_YM ymModel` quantifies over all of `ℝ`, `ymModel.μ`
being `μYM`, which reads the clamped coupling `max β 0`; so at `β < 0` it is this statement, and on
`0 < β` it is supplied through `Complete.confinement_of_bounded_substrate`'s route.

DERIVED: `0` is the coupling and the resulting tension. In the proof, `1` is the cosine average it
comes from. Nothing is chosen. -/
theorem confines_at_zero_coupling (N : ℕ) : MassGap.μYMAt N 0 < MassGap.κ₀YM := by
  have hμ : MassGap.μYMAt N 0 = 0 := by
    show -Real.log (∑ d, (MassGap.readYMAt N 0).p d
      * Real.cos ((MassGap.readYMAt N 0).θ d)) = 0
    rw [show (∑ d, (MassGap.readYMAt N 0).p d * Real.cos ((MassGap.readYMAt N 0).θ d))
        = MassGap.cosAvgYMAt N 0 from rfl, cosAvgYMAt_at_zero_coupling N, Real.log_one, neg_zero]
  rw [hμ]
  exact MassGap.κ₀YM_pos

#print axioms confines_at_zero_coupling





/-- `Continuous (cosAvgEven a)` at every even aperture, on all of `ℝ`. The average is a ratio of
finite sums: the numerator is `∑ d, wilsonCorrAt a.1 (max β 0) d * cos ((readEven a 0).θ d)` — the
angles not depending on `β`, by `readEven_theta` — and the denominator the same sum of profiles.
Both are continuous by `continuous_wilsonCorrAt` composed with the continuous clamp, and the
denominator never vanishes by the second clause of
`Complete.wilson_reflection_positive_at_even`, which applies because the clamped coupling is
nonnegative.

DERIVED: no numeral appears in the statement. -/
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

/-- There is a `b > 0` with `3 ^ (-(1 : ℝ) / 4) < cosAvgEven a β` for every `β` with `|β| < b`, at
every even aperture. It is `continuous_cosAvgEven` and `confines_at_zero` through
`Metric.eventually_nhds_iff`. The radius `b` is existential and no value is named for it.

DERIVED: `0` is the positivity threshold on the radius; `3`, `1` and `4` form the entropy floor
`3 ^ (-(1 : ℝ) / 4)`. -/
theorem confines_near_zero (a : EvenAp) :
    ∃ b > 0, ∀ β : ℝ, |β| < b → (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β := by
  have hev : ∀ᶠ β in nhds (0 : ℝ), (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β :=
    (continuous_cosAvgEven a).continuousAt (lt_mem_nhds (confines_at_zero a))
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨b, hb, hball⟩ := hev
  refine ⟨b, hb, fun β hβ => hball ?_⟩
  simpa [Real.dist_eq] using hβ

#print axioms confines_near_zero

/-- There is a `b > 0` with `3 ^ (-(1 : ℝ) / 4) < cosAvgEven a β` for every `β < b`, at every even
aperture. Below zero the value is `1` by `cosAvgEven_eq_one_of_nonpos`, which is the clamp; above
zero it is `confines_near_zero`. The content of the cut is therefore on `[0, b)`.

DERIVED: `0` is the positivity threshold on the cut; `3`, `1` and `4` form the entropy floor. -/
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

/-- The smallest aperture the proved reflection positivity admits: extent four.

DERIVED: `3` is `N` with `N + 1 = 4 = 2 * 2`, the smallest even extent carrying `2 ≤ m`. Both are
read off `Complete.wilson_reflection_positive_at_even`'s hypotheses and neither is chosen here —
`EvenAperture.two_le_half_is_load_bearing` is the negative control that extent two does not qualify. -/
abbrev ap4 : EvenAp := ⟨3, 2, rfl, le_refl 2⟩

#print axioms ap4

/-- The closed form at extent four. With `ρ = wilsonCorrAt 3 (max β 0)`,

    cosAvgEven ap4 β = (ρ 0 - ρ 2) / (ρ 0 + 2 * ρ 1 + ρ 2).

The four lag angles are `2πd/4`, with cosines `1, 0, -1, 0`, and circle symmetry
(`MomentShape.wilsonCorrAt_neg`) identifies lag `3` with lag `1`. Lag `1` therefore contributes
nothing to the numerator and its full weight to the denominator.

DERIVED: `3` is the aperture index, with `3 + 1 = 4` the extent; `0`, `1`, `2` are lag indices and
`0` is also the clamp's lower end; the coefficient `2` on `ρ 1` is the number of lags circle
symmetry identifies with lag `1`, namely `1` and `3`. -/
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

/-- From a bound on the second lag alone, confinement at extent four: given

    (1 + c)^2 * ρ 2 < (1 - c)^2 * ρ 0,     c = 3 ^ (-(1 : ℝ) / 4),  ρ = wilsonCorrAt 3 (max β 0),

the conclusion is `c < cosAvgEven ap4 β`. The other inputs are nonnegativity of the profile
(`Complete.wilson_reflection_positive_at_even`) and log-convexity
(`LogConvex.corrClay_log_convex_at_extent_four`, giving `ρ 1 ^ 2 ≤ ρ 0 * ρ 2`), both available at
this extent with no further hypothesis; circle symmetry enters through
`cosAvgEven_extent_four`.

The threshold is the exact one log-convexity can carry: the `ring` identity

    ((1-c) ρ₀ - (1+c) ρ₂)^2 - 4 c^2 ρ₀ ρ₂ = ((1-c)^2 ρ₀ - (1+c)^2 ρ₂)(ρ₀ - ρ₂)

has its right factorisation vanish exactly at `(1+c)^2 ρ₂ = (1-c)^2 ρ₀`.

`WeakArm.corrClay_le_at_zero` and `MomentShape.corrClay_even_antitone` both carry `3 ≤ m`, which is
extent six and above, and are not used here.

DERIVED: `3`, `1` and `4` form the entropy floor `c = 3 ^ (-(1 : ℝ) / 4)`; the `1`s in `1 + c` and
`1 - c` are the endpoints the floor is measured from; the exponents `2` are squares; `0`, `1` and
`2` are lag indices and `0` is also the clamp's lower end; the aperture index is `3`, with
`3 + 1 = 4` the extent. -/
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

/-! ## 3a. A larger extent is not the same problem — the closed form at extent six

`ApertureRoute` records that the aperture cancels exactly in the substrate route
(`Complete.surplus_ge`'s `hcancel`), so the criterion `(2π)²·substrateRatio/2 < 1 − 3^{−1/4}` carries
no `N`. That is a statement about that route's sufficient bound, and it does not transfer to
`cosAvgEven` itself, which is checked here rather than assumed.

At extent six the angles are `2πd/6` and the cosines are `1, ½, −½, −1, −½, ½`, so the first lag
enters the numerator with a positive weight, where at extent four its cosine is exactly zero and it
enters the denominator alone. The two closed forms are therefore genuinely different problems, and
extent four is not automatically the easiest. Nothing here says which extent is easier — that is a
statement about the profiles, which this file does not bound. -/

/-- The next even aperture: extent six.

DERIVED: `5` is `N` with `N + 1 = 6 = 2 * 3`, the next even extent after four carrying `2 ≤ m`. As
with `ap4` both are read off `Complete.wilson_reflection_positive_at_even`'s hypotheses. -/
abbrev ap6 : EvenAp := ⟨5, 3, rfl, by norm_num⟩

#print axioms ap6

/-- The closed form at extent six. With `ρ = wilsonCorrAt 5 (max β 0)`,

    cosAvgEven ap6 β = (ρ 0 + ρ 1 - ρ 2 - ρ 3) / (ρ 0 + 2 * ρ 1 + 2 * ρ 2 + ρ 3).

The six lag angles are `2πd/6`, with cosines `1, ½, -½, -1, -½, ½`, and circle symmetry identifies
lag `5` with lag `1` and lag `4` with lag `2`.

Compared with `cosAvgEven_extent_four`, `ρ 1` enters the numerator here with a positive coefficient
where at extent four its cosine is zero and it enters the denominator alone, so the two closed forms
differ. What `Complete.surplus_ge` makes aperture-free is the substrate route's lower bound on the
cosine average, not the cosine average itself.

DERIVED: `5` is the aperture index, with `5 + 1 = 6` the extent; `0`, `1`, `2`, `3` are lag indices
and `0` is also the clamp's lower end; each coefficient `2` is the number of lags circle symmetry
identifies with the lag it multiplies — `1` with `5`, and `2` with `4`. -/
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

Everything above is about a neighbourhood of zero coupling. `ConfinesAtAnAperture` asks for every
coupling, and that is the whole of what is left. Because the cosine average is continuous and starts
strictly above the floor, the remaining obligation can be stated without an inequality at all. -/

/-- At some even aperture the cosine average is never equal to the entropy floor
`3 ^ (-(1 : ℝ) / 4)`: `∃ a : EvenAp, ∀ β : ℝ, cosAvgEven a β ≠ 3 ^ (-(1 : ℝ) / 4)`.

`confinesAtAnAperture_iff_missesTheFloor` proves this equivalent to
`ApertureRoute.ConfinesAtAnAperture`, not merely sufficient for it: the reverse direction is the
intermediate value theorem against `cosAvgEven_at_zero` and `continuous_cosAvgEven`, since the
average is `1` at zero coupling, so a coupling at which it fell below the floor would force one at
which it equalled the floor.

It is a non-equality at every coupling where `ConfinesAtAnAperture` is an inequality. No
declaration in this module bounds `cosAvgEven` at large `β`. `cosAvgEven_extent_four` shows the
ratio at extent four approaching zero as `ρ(2)` approaches `ρ(0)`, and
`confines_extent_four_of_lag_two_small` is the bound the module's shape facts do carry.

DERIVED: `3^{−1/4} = e^{−κ₀YM}` with `κ₀YM = ¼ log 3`, counted off directed cube paths in
`Floor.lean`; it is `ApertureRoute.ConfinesAtAnAperture`'s own constant, carried through unchanged. -/
def MissesTheFloor : Prop :=
  ∃ a : EvenAp, ∀ β : ℝ, cosAvgEven a β ≠ (3 : ℝ) ^ (-(1 : ℝ) / 4)

#print axioms MissesTheFloor

/-- `ConfinesAtAnAperture` from `MissesTheFloor`. At the aperture the hypothesis supplies, a
coupling with `cosAvgEven a β` below the floor would, with `confines_at_zero` above it and
`continuous_cosAvgEven` between, give a coupling at which the average equalled the floor by
`intermediate_value_uIcc`, contradicting `MissesTheFloor`.

DERIVED: no numeral appears in the statement. -/
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

/-- `MissesTheFloor` from `ConfinesAtAnAperture`: a strict inequality is in particular a
non-equality, by `ne_of_gt`.

DERIVED: no numeral appears in the statement. -/
theorem missesTheFloor_of_confinesAtAnAperture (h : ConfinesAtAnAperture) : MissesTheFloor := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun β => ne_of_gt (ha β)⟩

#print axioms missesTheFloor_of_confinesAtAnAperture

/-- `ConfinesAtAnAperture ↔ MissesTheFloor`, the two implications above combined. The inequality at
every coupling and the non-equality at every coupling are the same statement, the reverse direction
using `continuous_cosAvgEven` and `cosAvgEven_at_zero`.

DERIVED: no numeral appears in the statement. -/
theorem confinesAtAnAperture_iff_missesTheFloor : ConfinesAtAnAperture ↔ MissesTheFloor :=
  ⟨missesTheFloor_of_confinesAtAnAperture, confinesAtAnAperture_of_missesTheFloor⟩

#print axioms confinesAtAnAperture_iff_missesTheFloor

/-- `ApertureRoute.FlagshipAt` at the realisation `MissesTheFloor` produces: the mode sum tending
to zero, non-triviality, direction-independence of `R`, and the OS0–OS3 subsequential limit. It is
`flagship_of_confinement_at_an_aperture` applied to
`confinesAtAnAperture_of_missesTheFloor h`.

DERIVED: no numeral appears in the statement. -/
theorem flagship_of_missesTheFloor (h : MissesTheFloor) :
    FlagshipAt (confinesAtAnAperture_of_missesTheFloor h) :=
  flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_missesTheFloor

end MassGap.ConfinesZero
