import Mathlib
import MassGap.CompactBeta
import MassGap.ConfinesZero
import MassGap.ApertureRoute
import MassGap.ContactDominance

/-!
# MassGap.MomentArms — the substrate bound assembled from bounds on pieces of the coupling line

`Complete.ym_mass_gap_of_substrate` consumes `∃ B, ∀ N β, d2At N β ≤ B`, a bound on the circular
second moment uniform in the aperture and the coupling.
`CompactBeta.d2At_jointUniform_on_Icc_of_equicontinuous` supplies such a bound on a compact interval.
This file assembles a bound on the whole line out of bounds on pieces of it, weakens the hypothesis
in three further ways, and supplies two envelope-shaped sufficient conditions.

## §1 Three arms, on `d2At`

`circLag_zero` and `d2At_at_zero` compute the moment at zero coupling: the correlation vanishes at
every lag of nonzero circle distance (`PowerTail.wilsonCorrAt_at_zero_coupling`) and the contact
value stays positive, so the read is a point mass at lag zero, where `circLag` is `0`. `d2At_nonneg`
is the other sign. `d2At_bound_of_three_arms` takes bounds on `(-∞, a]`, `[a, b]` and `[b, ∞)` and
returns their maximum; `confinement_of_three_arms` and `ym_mass_gap_of_three_arms` feed it to
`MassGap.confinement_of_bounded_substrate` and `MassGap.ym_mass_gap_of_substrate`.

## §2 Two arms, on `d2Even`

`EvenAperture.d2Even` is built from `readEven`, whose positivity comes from
`Complete.wilson_reflection_positive_at_even`, a theorem at even extent, so nothing in this section
mentions `readYMAt`. `readEven` reads the correlation at `max β 0`, so
`readEven_eq_zero_of_nonpos`, `d2Even_at_zero` and `d2Even_eq_zero_of_nonpos` give
`d2Even a β = 0` for every `β ≤ 0`. `d2Even_bound_of_two_arms` therefore needs bounds on `[0, b]`
and `[b, ∞)` only; `confines_of_two_arms` and `flagship_of_two_arms` carry it to
`ApertureRoute.ConfinesAtAnAperture` and `ApertureRoute.FlagshipAt`.

## §3 The bound asked only from some aperture onwards

`ApertureRoute.confinement_at_an_aperture_of_substrate` quantifies over every even aperture but uses
the bound at the single aperture `EvenAperture.exists_evenAp_of_eventually` picks out.
`confines_of_large_aperture_bound` re-proves it with the hypothesis restricted to apertures of extent
at least `N₀`, choosing the aperture to satisfy the window condition and exceed `N₀` — both are
eventual in the extent. `large_aperture_bound_of_substrate_bound` derives the weaker hypothesis from
the stronger one at `N₀ = 0`. `confines_of_two_arms_at_large_apertures` and
`flagship_of_two_arms_at_large_apertures` combine §2 and §3.

## §4–§5 Far-share envelopes

`ContactDominance.farShare R m` is the probability a read puts beyond circle distance `m`.
`ContactDominance.circ_moment_le_of_envelope` bounds the circular second moment by
`∑' m, (2 m + 1) a m` when `farShare ≤ a m` at every `m`; the weight `2 m + 1` is `(m+1)² - m²`, the
number of lags at distance `m`. `substrate_even_of_share_envelope` and its `large_aperture`,
`confines` and `flagship` corollaries are that at `readEven`.
`ContactDominance.circ_moment_le_of_tail_envelope` asks for the envelope only from a cut `m₀`
upward, paying `m₀ ^ 2` for the near block, and `substrate_even_of_tail_envelope` and its corollaries
are that version. `summable_cubic_weight` and `flagship_of_cubic_tail_share` instantiate at
`a m = C / (m + 1) ^ 3`.

## §6 Geometric envelopes

`summable_geometric_weight` gives convergence for `a m = C * r ^ m` with `0 ≤ r < 1`, splitting
`(2 m + 1) r ^ m` into `2 * (m r ^ m)` and `r ^ m` and applying
`summable_pow_mul_geometric_of_norm_lt_one` to each. `confines_of_geometric_far_share` and
`flagship_of_geometric_far_share` run the §5 chain at that envelope.

## Scope

* The arms other than the negative half-line are hypotheses in every theorem here. `d2At_at_zero`
  and `d2Even_at_zero` bound the moment at one coupling, which is not a bound on a half-line.
* `ContactDominance`'s exponent threshold: a power envelope `C (m+1) ^ (-s)` has weighted total
  `∑ (2m+1) C (m+1) ^ (-s)`, convergent exactly when `s > 2`. At `s = 2` the sum is harmonic, and
  `ContactDominance.square_share_is_not_enough` exhibits reads whose far share stays under
  `(4/3)(m+1) ^ (-2)` at every aperture with unbounded moments. `3` is the first integer exponent
  for which `summable_cubic_weight` holds.
* What `ApertureRoute.FlagshipAt` asserts is limited, and `MassGap.FlagshipScope` — not imported
  here — measures it: `FlagshipScope.flagship_for_bogus` proves the whole flagship conclusion for
  `bogusWilson`, an object with no read, correlation, gauge group or lattice;
  `gap_summand_is_manufactured` shows the gap clause's summand is `exp (-(κ₀ - μ)) ^ τ`, whose
  magnitude is its own bound; `flagship_measure_half_needs_no_hypothesis` shows the measure half
  adds no hypothesis beyond `ConfinesAtAnAperture`, which is its one argument; and
  `Q_is_constant_in_the_test_configuration` shows OS1 and OS3 hold because
  the reflected form does not depend on the components those actions move. The statement in these
  chains that is about the Wilson correlation is `ApertureRoute.ConfinesAtAnAperture`, which is about
  `cosAvgEven` of `readEven`; each `flagship_of_…` is its packaging.
-/

namespace MassGap.MomentArms

/-- `Moment.circLag (0 : Fin (N + 1)) = 0`: the circular distance from the origin to itself, which is
`min 0 ((N + 1) - 0)`. Closed by `simp` on the definition.

DERIVED: the first `0` is the lag whose distance is taken; `1` is the `+ 1` in the lag index type
`Fin (N + 1)`, one index per lag including contact; the final `0` is the resulting distance. -/
theorem circLag_zero {N : ℕ} : Moment.circLag (0 : Fin (N + 1)) = 0 := by
  simp [Moment.circLag]

#print axioms circLag_zero

/-- `MassGap.d2At N 0 = 0` at every aperture `N`.

`PowerTail.wilsonCorrAt_at_zero_coupling` makes the raw correlation vanish at every lag of nonzero
circle distance, so the normalised read is a point mass at lag zero, and `circLag_zero` makes the
weight there zero. The sum is therefore termwise zero.

Scope: one coupling. A value at a point is not a bound on an interval, and none is claimed. This is
stated through `readYMAt`, so it carries whatever axiom that read does;
`d2Even_at_zero` is the `readEven` counterpart.

DERIVED: `0` occurs twice — the coupling at which the moment is taken, and the value it takes. -/
theorem d2At_at_zero (N : ℕ) : MassGap.d2At N 0 = 0 := by
  have hp : ∀ d : Fin (N + 1), d ≠ 0 → (MassGap.readYMAt N 0).p d = 0 := by
    intro d hd
    -- `(readYMAt N β).ρ = wilsonCorrAt N β` holds by definition, which is why
    -- `ShareEnvelope.readYMAt_rho` proves it by `rfl`; the citation is not in this import closure.
    have hrho : (MassGap.readYMAt N 0).ρ d = 0 :=
      MassGap.PowerTail.wilsonCorrAt_at_zero_coupling N d
        (MassGap.ConfinesZero.one_le_circLag hd)
    simp [Moment.Read.p, hrho]
  unfold MassGap.d2At
  refine Finset.sum_eq_zero (fun d _ => ?_)
  rcases eq_or_ne d 0 with rfl | hd
  · rw [circLag_zero]
    norm_num
  · rw [hp d hd]
    ring

#print axioms d2At_at_zero

/-- `0 ≤ MassGap.d2At N β` at every aperture and every real coupling. Each summand is a probability
weight (`Moment.Read.p_nonneg`) times a square, so `Finset.sum_nonneg` applies.

DERIVED: `0` is the lower bound on the moment. -/
theorem d2At_nonneg (N : ℕ) (β : ℝ) : 0 ≤ MassGap.d2At N β := by
  unfold MassGap.d2At
  exact Finset.sum_nonneg (fun d _ =>
    mul_nonneg ((MassGap.readYMAt N β).p_nonneg d) (sq_nonneg _))

#print axioms d2At_nonneg

/-! ## §1 Assembling a bound on the line from bounds on three pieces of it -/

/-- Given bounds on `MassGap.d2At`, uniform in the aperture, on `(-∞, a]`, on `Set.Icc a b` and on
`[b, ∞)`, there is one bound serving every aperture and every real coupling. The witness is the
maximum of the three, and the proof splits `β` against `a` and then against `b`.

Scope: all three bounds are hypotheses; `CompactBeta.d2At_jointUniform_on_Icc_of_equicontinuous` is
one source of the middle one, itself conditional.

DERIVED: no numeral appears in the statement; `a` and `b` are the caller's cut points. -/
theorem d2At_bound_of_three_arms {a b : ℝ}
    (hlow : ∃ B : ℝ, ∀ (N : ℕ), ∀ β ≤ a, MassGap.d2At N β ≤ B)
    (hmid : ∃ B : ℝ, ∀ (N : ℕ), ∀ β ∈ Set.Icc a b, MassGap.d2At N β ≤ B)
    (hhigh : ∃ B : ℝ, ∀ (N : ℕ), ∀ β, b ≤ β → MassGap.d2At N β ≤ B) :
    ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B := by
  obtain ⟨B₁, h₁⟩ := hlow
  obtain ⟨B₂, h₂⟩ := hmid
  obtain ⟨B₃, h₃⟩ := hhigh
  refine ⟨max B₁ (max B₂ B₃), fun N β => ?_⟩
  rcases le_total β a with hβ | hβ
  · exact (h₁ N β hβ).trans (le_max_left _ _)
  · rcases le_total β b with hβ' | hβ'
    · exact (h₂ N β ⟨hβ, hβ'⟩).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (h₃ N β hβ').trans ((le_max_right _ _).trans (le_max_right _ _))

#print axioms d2At_bound_of_three_arms

/-- `MassGap.confinement_of_bounded_substrate` with its hypothesis supplied by
`d2At_bound_of_three_arms`: from the three arm bounds, `μYMAt N β < κ₀YM` at every coupling, for
eventually every aperture.

DERIVED: no numeral appears in the statement; `a` and `b` are the caller's cut points. -/
theorem confinement_of_three_arms {a b : ℝ}
    (hlow : ∃ B : ℝ, ∀ (N : ℕ), ∀ β ≤ a, MassGap.d2At N β ≤ B)
    (hmid : ∃ B : ℝ, ∀ (N : ℕ), ∀ β ∈ Set.Icc a b, MassGap.d2At N β ≤ B)
    (hhigh : ∃ B : ℝ, ∀ (N : ℕ), ∀ β, b ≤ β → MassGap.d2At N β ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, MassGap.μYMAt N β < MassGap.κ₀YM :=
  MassGap.confinement_of_bounded_substrate (d2At_bound_of_three_arms hlow hmid hhigh)

#print axioms confinement_of_three_arms

/-- `MassGap.ym_mass_gap_of_substrate` with its hypothesis supplied by `d2At_bound_of_three_arms`.
For eventually every aperture, the conclusion conjoins: the mode sum of `MassGap.ymModelAt N` tends
to `0` at every coupling; `μ β - κ < 0` at every coupling; and `R` is constant.

DERIVED: `0` occurs twice — the limit point of the mode sum, and the comparison point in
`μ β - κ < 0`. -/
theorem ym_mass_gap_of_three_arms {a b : ℝ}
    (hlow : ∃ B : ℝ, ∀ (N : ℕ), ∀ β ≤ a, MassGap.d2At N β ≤ B)
    (hmid : ∃ B : ℝ, ∀ (N : ℕ), ∀ β ∈ Set.Icc a b, MassGap.d2At N β ≤ B)
    (hhigh : ∃ B : ℝ, ∀ (N : ℕ), ∀ β, b ≤ β → MassGap.d2At N β ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (∀ β, Filter.Tendsto
          (fun τ => ‖∑ k ∈ (MassGap.ymModelAt N).s β,
            (MassGap.ymModelAt N).P β k * ((MassGap.ymModelAt N).m β k) ^ τ‖)
          Filter.atTop (nhds 0)) ∧
        (∀ β, (MassGap.ymModelAt N).μ β - (MassGap.ymModelAt N).κ < 0) ∧
        (∀ d d', (MassGap.ymModelAt N).R d = (MassGap.ymModelAt N).R d') :=
  MassGap.ym_mass_gap_of_substrate (d2At_bound_of_three_arms hlow hmid hhigh)

#print axioms ym_mass_gap_of_three_arms


/-! ## §2 The same split on `d2Even`, where the nonpositive arm is computed

`d2At` goes through `readYMAt`. `EvenAperture.d2Even` goes through `readEven`, whose positivity comes
from `Complete.wilson_reflection_positive_at_even`, a theorem at even extent at least four, and
`ApertureRoute.confinement_at_an_aperture_of_substrate` consumes `∃ B, ∀ a β, d2Even a β ≤ B`.

Nothing below mentions `readYMAt`, so `wilson_reflection_positive_at` does not enter. `readEven`
reads the correlation at `max β 0`, so below zero coupling it reads it at zero, where the profile is
a point mass and the moment is `0` — `ConfinesZero.cosAvgEven_eq_one_of_nonpos` is the same fact for
the cosine average. The three arms of §1 become two, on `[0, b]` and `[b, ∞)`.
-/

/-- `EvenAperture.readEven a β = EvenAperture.readEven a 0` for every `β ≤ 0`. `readEven` reads the
correlation at `max β 0`, which is `0` on the nonpositive half-line, and `readA_congr` transports the
equality of arguments to the reads.

DERIVED: `0` occurs twice — the upper bound on `β`, and the coupling the read is shown to be taken
at. -/
theorem readEven_eq_zero_of_nonpos (a : MassGap.EvenAperture.EvenAp) {β : ℝ} (hβ : β ≤ 0) :
    MassGap.EvenAperture.readEven a β = MassGap.EvenAperture.readEven a 0 := by
  unfold MassGap.EvenAperture.readEven
  refine MassGap.EvenAperture.readA_congr ?_
  rw [max_eq_right hβ, max_self]

#print axioms readEven_eq_zero_of_nonpos

/-- `EvenAperture.d2Even a 0 = 0` at every even aperture. The same point-mass argument as
`d2At_at_zero`, read through `readEven`: `NonnegArm.readEven_rho` with `max_self` identifies the raw
profile with `wilsonCorrAt`, which `PowerTail.wilsonCorrAt_at_zero_coupling` kills off contact, and
`circLag_zero` kills the weight at contact.

Scope: stated through `readEven`, whose positivity comes from
`Complete.wilson_reflection_positive_at_even`, so `wilson_reflection_positive_at` does not appear.

DERIVED: `0` occurs twice — the coupling at which the moment is taken, and the value it takes. -/
theorem d2Even_at_zero (a : MassGap.EvenAperture.EvenAp) :
    MassGap.EvenAperture.d2Even a 0 = 0 := by
  have hp : ∀ d : Fin (a.1 + 1), d ≠ 0 → (MassGap.EvenAperture.readEven a 0).p d = 0 := by
    intro d hd
    have hrho : (MassGap.EvenAperture.readEven a 0).ρ d = 0 := by
      rw [MassGap.NonnegArm.readEven_rho, max_self]
      exact MassGap.PowerTail.wilsonCorrAt_at_zero_coupling a.1 d
        (MassGap.ConfinesZero.one_le_circLag hd)
    simp [Moment.Read.p, hrho]
  unfold MassGap.EvenAperture.d2Even
  refine Finset.sum_eq_zero (fun d _ => ?_)
  rcases eq_or_ne d 0 with rfl | hd
  · rw [circLag_zero]
    norm_num
  · rw [hp d hd]
    ring

#print axioms d2Even_at_zero

/-- `EvenAperture.d2Even a β = 0` for every `β ≤ 0`, by `readEven_eq_zero_of_nonpos` followed by
`d2Even_at_zero`. The nonpositive half-line carries no separate hypothesis in the theorems below.

DERIVED: `0` occurs twice — the upper bound on `β`, and the value the moment takes there. -/
theorem d2Even_eq_zero_of_nonpos (a : MassGap.EvenAperture.EvenAp) {β : ℝ} (hβ : β ≤ 0) :
    MassGap.EvenAperture.d2Even a β = 0 := by
  unfold MassGap.EvenAperture.d2Even
  rw [readEven_eq_zero_of_nonpos a hβ]
  exact d2Even_at_zero a

#print axioms d2Even_eq_zero_of_nonpos

/-- Given bounds on `EvenAperture.d2Even`, uniform in the even aperture, on `Set.Icc 0 b` and on
`[b, ∞)`, there is one bound serving every even aperture and every real coupling. The witness is
`max 0 (max B₁ B₂)`, and the nonpositive branch is closed by `d2Even_eq_zero_of_nonpos` rather than
by a hypothesis.

Scope: two arms rather than the three of `d2At_bound_of_three_arms`, because the third is computed.

DERIVED: `0` is the lower endpoint of the middle interval `Set.Icc 0 b`, which is where the computed
half-line ends. -/
theorem d2Even_bound_of_two_arms {b : ℝ}
    (hmid : ∃ B : ℝ, ∀ (a : MassGap.EvenAperture.EvenAp), ∀ β ∈ Set.Icc (0 : ℝ) b,
      MassGap.EvenAperture.d2Even a β ≤ B)
    (hhigh : ∃ B : ℝ, ∀ (a : MassGap.EvenAperture.EvenAp), ∀ β, b ≤ β →
      MassGap.EvenAperture.d2Even a β ≤ B) :
    ∃ B : ℝ, ∀ (a : MassGap.EvenAperture.EvenAp) (β : ℝ),
      MassGap.EvenAperture.d2Even a β ≤ B := by
  obtain ⟨B₁, h₁⟩ := hmid
  obtain ⟨B₂, h₂⟩ := hhigh
  refine ⟨max 0 (max B₁ B₂), fun a β => ?_⟩
  rcases le_total β 0 with hβ | hβ
  · rw [d2Even_eq_zero_of_nonpos a hβ]
    exact le_max_left _ _
  · rcases le_total β b with hβ' | hβ'
    · exact (h₁ a β ⟨hβ, hβ'⟩).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (h₂ a β hβ').trans ((le_max_right _ _).trans (le_max_right _ _))

#print axioms d2Even_bound_of_two_arms

/-- `ApertureRoute.confinement_at_an_aperture_of_substrate` with its hypothesis supplied by
`d2Even_bound_of_two_arms`: the two arm bounds give `ApertureRoute.ConfinesAtAnAperture`.

DERIVED: `0` is the lower endpoint of the middle interval `Set.Icc 0 b`. -/
theorem confines_of_two_arms {b : ℝ}
    (hmid : ∃ B : ℝ, ∀ (a : MassGap.EvenAperture.EvenAp), ∀ β ∈ Set.Icc (0 : ℝ) b,
      MassGap.EvenAperture.d2Even a β ≤ B)
    (hhigh : ∃ B : ℝ, ∀ (a : MassGap.EvenAperture.EvenAp), ∀ β, b ≤ β →
      MassGap.EvenAperture.d2Even a β ≤ B) :
    MassGap.ApertureRoute.ConfinesAtAnAperture :=
  MassGap.ApertureRoute.confinement_at_an_aperture_of_substrate
    (d2Even_bound_of_two_arms hmid hhigh)

#print axioms confines_of_two_arms

/-- `ApertureRoute.flagship_of_confinement_at_an_aperture` at `confines_of_two_arms`:
`ApertureRoute.FlagshipAt` for that confinement witness. See the module header for what `FlagshipAt`
asserts.

DERIVED: `0` is the lower endpoint of the middle interval `Set.Icc 0 b`. -/
theorem flagship_of_two_arms {b : ℝ}
    (hmid : ∃ B : ℝ, ∀ (a : MassGap.EvenAperture.EvenAp), ∀ β ∈ Set.Icc (0 : ℝ) b,
      MassGap.EvenAperture.d2Even a β ≤ B)
    (hhigh : ∃ B : ℝ, ∀ (a : MassGap.EvenAperture.EvenAp), ∀ β, b ≤ β →
      MassGap.EvenAperture.d2Even a β ≤ B) :
    MassGap.ApertureRoute.FlagshipAt (confines_of_two_arms hmid hhigh) :=
  MassGap.ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_two_arms


/-! ## §3 The bound asked only at large apertures

`ApertureRoute.confinement_at_an_aperture_of_substrate` asks for `∀ (a : EvenAp) (β : ℝ),
d2Even a β ≤ B`, but consumes it at the single aperture
`EvenAperture.exists_evenAp_of_eventually` picks out of the window condition. The hypothesis can
therefore be restricted to apertures of extent at least `N₀`, with the aperture chosen to satisfy
the window condition and exceed `N₀` — both conditions are eventual in the extent.

`large_aperture_bound_of_substrate_bound` derives the restricted hypothesis from the unrestricted
one, so every consequence of the latter remains a consequence.
-/

/-- A bound on `EvenAperture.d2Even` at every even aperture gives one holding from some extent
onwards, with `N₀ := 0`. So the hypothesis of `confines_of_large_aperture_bound` is implied by the
hypothesis of `confines_of_two_arms`, and the restriction is a weakening rather than a different
statement.

DERIVED: no numeral appears in the statement; the `N₀ = 0` used as the witness lives in the proof. -/
theorem large_aperture_bound_of_substrate_bound
    (h : ∃ B : ℝ, ∀ (a : MassGap.EvenAperture.EvenAp) (β : ℝ),
      MassGap.EvenAperture.d2Even a β ≤ B) :
    ∃ B : ℝ, ∃ N₀ : ℕ, ∀ (a : MassGap.EvenAperture.EvenAp), N₀ ≤ a.1 → ∀ (β : ℝ),
      MassGap.EvenAperture.d2Even a β ≤ B := by
  obtain ⟨B, hB⟩ := h
  exact ⟨B, 0, fun a _ β => hB a β⟩

#print axioms large_aperture_bound_of_substrate_bound

/-- `ApertureRoute.ConfinesAtAnAperture` from a bound on `EvenAperture.d2Even` holding only at even
apertures of extent at least `N₀`.

The proof re-runs `ApertureRoute.confinement_at_an_aperture_of_substrate`: the window condition
`(2π/(N+1))² B / 2 < 1 - 3 ^ (-1/4)` is eventual in the extent by
`Moment.aperture_factor_tendsto_zero`, so conjoining it with `Filter.eventually_ge_atTop N₀` lets
`EvenAperture.exists_evenAp_of_eventually` pick an aperture meeting both, and
`Moment.Read.cos_avg_ge_circ` closes it there.

Scope: the original quantifies over every even aperture but consumes the bound at the single
aperture it chooses, which is why restricting to large extents costs nothing.

DERIVED: no numeral appears in the statement; `N₀` and `B` are existentially bound. The `2`, `3` and
`4` of the window condition and the floor `3 ^ (-1/4)` are inside the proof. -/
theorem confines_of_large_aperture_bound
    (h : ∃ B : ℝ, ∃ N₀ : ℕ, ∀ (a : MassGap.EvenAperture.EvenAp), N₀ ≤ a.1 → ∀ (β : ℝ),
      MassGap.EvenAperture.d2Even a β ≤ B) :
    MassGap.ApertureRoute.ConfinesAtAnAperture := by
  obtain ⟨B, N₀, hB⟩ := h
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) :=
    (Moment.aperture_factor_tendsto_zero B).eventually_lt_const Moment.floor_rhs_pos
  obtain ⟨a, ha⟩ :=
    MassGap.EvenAperture.exists_evenAp_of_eventually ((Filter.eventually_ge_atTop N₀).and hev)
  refine ⟨a, fun β => ?_⟩
  have hd2 : MassGap.EvenAperture.d2Even a β
      = ∑ d, (MassGap.EvenAperture.readEven a β).p d * (Moment.circLag d : ℝ) ^ 2 := rfl
  have hmul : (2 * Real.pi / ((a.1 : ℝ) + 1)) ^ 2
        * (∑ d, (MassGap.EvenAperture.readEven a β).p d * (Moment.circLag d : ℝ) ^ 2)
      ≤ (2 * Real.pi / ((a.1 : ℝ) + 1)) ^ 2 * B := by
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [← hd2]
    exact hB a ha.1 β
  have hge := (MassGap.EvenAperture.readEven a β).cos_avg_ge_circ
  have hwin := ha.2
  show (3 : ℝ) ^ (-(1 : ℝ) / 4)
      < ∑ d, (MassGap.EvenAperture.readEven a β).p d
          * Real.cos ((MassGap.EvenAperture.readEven a β).θ d)
  linarith

#print axioms confines_of_large_aperture_bound

/-- `ApertureRoute.flagship_of_confinement_at_an_aperture` at `confines_of_large_aperture_bound`.

DERIVED: no numeral appears in the statement. -/
theorem flagship_of_large_aperture_bound
    (h : ∃ B : ℝ, ∃ N₀ : ℕ, ∀ (a : MassGap.EvenAperture.EvenAp), N₀ ≤ a.1 → ∀ (β : ℝ),
      MassGap.EvenAperture.d2Even a β ≤ B) :
    MassGap.ApertureRoute.FlagshipAt (confines_of_large_aperture_bound h) :=
  MassGap.ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_large_aperture_bound

/-- `confines_of_large_aperture_bound` with its hypothesis assembled from two arms: bounds on
`Set.Icc 0 b` and on `[b, ∞)`, each asked only at even apertures of extent at least `N₀`. The
nonpositive branch is closed by `d2Even_eq_zero_of_nonpos`, so the witness is `max 0 (max B₁ B₂)`.

DERIVED: `0` is the lower endpoint of the middle interval `Set.Icc 0 b`. -/
theorem confines_of_two_arms_at_large_apertures {b : ℝ} {N₀ : ℕ}
    (hmid : ∃ B : ℝ, ∀ (a : MassGap.EvenAperture.EvenAp), N₀ ≤ a.1 → ∀ β ∈ Set.Icc (0 : ℝ) b,
      MassGap.EvenAperture.d2Even a β ≤ B)
    (hhigh : ∃ B : ℝ, ∀ (a : MassGap.EvenAperture.EvenAp), N₀ ≤ a.1 → ∀ β, b ≤ β →
      MassGap.EvenAperture.d2Even a β ≤ B) :
    MassGap.ApertureRoute.ConfinesAtAnAperture := by
  refine confines_of_large_aperture_bound ?_
  obtain ⟨B₁, h₁⟩ := hmid
  obtain ⟨B₂, h₂⟩ := hhigh
  refine ⟨max 0 (max B₁ B₂), N₀, fun a hN β => ?_⟩
  rcases le_total β 0 with hβ | hβ
  · rw [d2Even_eq_zero_of_nonpos a hβ]
    exact le_max_left _ _
  · rcases le_total β b with hβ' | hβ'
    · exact (h₁ a hN β ⟨hβ, hβ'⟩).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (h₂ a hN β hβ').trans ((le_max_right _ _).trans (le_max_right _ _))

#print axioms confines_of_two_arms_at_large_apertures

/-- `ApertureRoute.flagship_of_confinement_at_an_aperture` at
`confines_of_two_arms_at_large_apertures`.

DERIVED: `0` is the lower endpoint of the middle interval `Set.Icc 0 b`. -/
theorem flagship_of_two_arms_at_large_apertures {b : ℝ} {N₀ : ℕ}
    (hmid : ∃ B : ℝ, ∀ (a : MassGap.EvenAperture.EvenAp), N₀ ≤ a.1 → ∀ β ∈ Set.Icc (0 : ℝ) b,
      MassGap.EvenAperture.d2Even a β ≤ B)
    (hhigh : ∃ B : ℝ, ∀ (a : MassGap.EvenAperture.EvenAp), N₀ ≤ a.1 → ∀ β, b ≤ β →
      MassGap.EvenAperture.d2Even a β ≤ B) :
    MassGap.ApertureRoute.FlagshipAt (confines_of_two_arms_at_large_apertures hmid hhigh) :=
  MassGap.ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_two_arms_at_large_apertures


/-! ## §4 The far-share envelope, at `readEven`

`ContactDominance.substrate_of_share_envelope` turns a summable envelope on the far share into the
substrate bound, stated on `readYMAt` and `d2At`. `ContactDominance.farShare` and
`circ_moment_le_of_envelope` are stated for an arbitrary `Moment.Read`, so the same terms apply at
`readEven`, whose positivity comes from `wilson_reflection_positive_at_even`.

`farShare R m` is the probability the read puts beyond circle distance `m`. An envelope `a` bounding
it uniformly, with `∑ (2 * m + 1) * a m` convergent, bounds the circular second moment by that sum,
layer by layer, `2 * m + 1` being the number of lags at distance `m`.
-/

/-- If `a : ℕ → ℝ` is nonnegative, `fun m => (2 * m + 1) * a m` is summable, and
`ContactDominance.farShare (readEven p β) m ≤ a m` at every even aperture, coupling and `m`, then
`EvenAperture.d2Even` is bounded by `∑' m, (2 * m + 1) * a m`. It is
`ContactDominance.circ_moment_le_of_envelope`, which is stated for an arbitrary `Moment.Read`,
applied at `readEven p β`.

DERIVED: `0` is the lower bound on the envelope; `2` and `1` are the layer weight `2 * m + 1`, the
number of lags at circle distance `m`, which is `(m + 1) ^ 2 - m ^ 2`. -/
theorem substrate_even_of_share_envelope (a : ℕ → ℝ)
    (ha0 : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * a m))
    (ha : ∀ (p : MassGap.EvenAperture.EvenAp) (β : ℝ) (m : ℕ),
      MassGap.ContactDominance.farShare (MassGap.EvenAperture.readEven p β) m ≤ a m) :
    ∃ B : ℝ, ∀ (p : MassGap.EvenAperture.EvenAp) (β : ℝ),
      MassGap.EvenAperture.d2Even p β ≤ B :=
  ⟨∑' m : ℕ, (2 * (m : ℝ) + 1) * a m, fun p β =>
    MassGap.ContactDominance.circ_moment_le_of_envelope
      (MassGap.EvenAperture.readEven p β) a ha0 (ha p β) hs⟩

#print axioms substrate_even_of_share_envelope

/-- `substrate_even_of_share_envelope` with the envelope asked only at even apertures of extent at
least `N₀`, and the conclusion in the matching restricted form with `N₁ := N₀`.

DERIVED: `0` is the lower bound on the envelope; `2` and `1` are the layer weight `2 * m + 1`. -/
theorem large_aperture_bound_of_share_envelope {N₀ : ℕ} (a : ℕ → ℝ)
    (ha0 : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * a m))
    (ha : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (m : ℕ),
      MassGap.ContactDominance.farShare (MassGap.EvenAperture.readEven p β) m ≤ a m) :
    ∃ B : ℝ, ∃ N₁ : ℕ, ∀ (p : MassGap.EvenAperture.EvenAp), N₁ ≤ p.1 → ∀ (β : ℝ),
      MassGap.EvenAperture.d2Even p β ≤ B :=
  ⟨∑' m : ℕ, (2 * (m : ℝ) + 1) * a m, N₀, fun p hp β =>
    MassGap.ContactDominance.circ_moment_le_of_envelope
      (MassGap.EvenAperture.readEven p β) a ha0 (ha p hp β) hs⟩

#print axioms large_aperture_bound_of_share_envelope

/-- `confines_of_large_aperture_bound` with its hypothesis supplied by
`large_aperture_bound_of_share_envelope`: a summable-weighted far-share envelope at large apertures
gives `ApertureRoute.ConfinesAtAnAperture`.

DERIVED: `0` is the lower bound on the envelope; `2` and `1` are the layer weight `2 * m + 1`. -/
theorem confines_of_share_envelope {N₀ : ℕ} (a : ℕ → ℝ)
    (ha0 : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * a m))
    (ha : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (m : ℕ),
      MassGap.ContactDominance.farShare (MassGap.EvenAperture.readEven p β) m ≤ a m) :
    MassGap.ApertureRoute.ConfinesAtAnAperture :=
  confines_of_large_aperture_bound (large_aperture_bound_of_share_envelope a ha0 hs ha)

#print axioms confines_of_share_envelope

/-- `ApertureRoute.flagship_of_confinement_at_an_aperture` at `confines_of_share_envelope`. The
hypothesis is one summable-weighted far-share envelope, asked only from extent `N₀` onwards, and the
axiom footprint of the chain is the foundational three.

DERIVED: `0` is the lower bound on the envelope; `2` and `1` are the layer weight `2 * m + 1`. -/
theorem flagship_of_share_envelope {N₀ : ℕ} (a : ℕ → ℝ)
    (ha0 : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * a m))
    (ha : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (m : ℕ),
      MassGap.ContactDominance.farShare (MassGap.EvenAperture.readEven p β) m ≤ a m) :
    MassGap.ApertureRoute.FlagshipAt (confines_of_share_envelope a ha0 hs ha) :=
  MassGap.ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_share_envelope


/-! ## §5 The envelope asked only beyond a cut, and a power instance

`ContactDominance.circ_moment_le_of_tail_envelope` assumes the envelope only from a cut `m₀` upward
and pays `m₀ ^ 2` for the near block, which `farShare ≤ 1` caps on its own. It is stated for an
arbitrary `Moment.Read`, so it applies at `readEven` as §4's lemma does.

The exponent: `2 * m + 1` is `(m + 1) ^ 2 - m ^ 2`, the second moment's layer weight, so a power
envelope `C * (m + 1) ^ (-s)` has weighted total `∑ (2 * m + 1) * C * (m + 1) ^ (-s)`, convergent
exactly when `s > 2`. At `s = 2` that sum is harmonic, and
`ContactDominance.square_share_is_not_enough` exhibits reads whose far share stays under
`(4/3) * (m + 1) ^ (-2)` at every aperture with unbounded moments. `s = 3` is the first integer
exponent for which `summable_cubic_weight` holds, and `flagship_of_cubic_tail_share` runs the chain
there.
-/

/-- `substrate_even_of_share_envelope` with the envelope required only from a cut `m₀` upward. The
bound becomes `m₀ ^ 2 + ∑' m, (2 * m + 1) * a m`, the first term paying for the near block, which
`farShare ≤ 1` caps on its own. It is `ContactDominance.circ_moment_le_of_tail_envelope` at
`readEven p β`.

Scope: nothing is asked of the envelope below `m₀`, so the hypothesis is weaker than
`substrate_even_of_share_envelope`'s.

DERIVED: `0` is the lower bound on the envelope; `2` and `1` are the layer weight `2 * m + 1`. The
`m₀ ^ 2` paid for the near block appears in the witness, not in the statement. -/
theorem substrate_even_of_tail_envelope (m₀ : ℕ) (a : ℕ → ℝ)
    (ha0 : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * a m))
    (ha : ∀ (p : MassGap.EvenAperture.EvenAp) (β : ℝ) (m : ℕ), m₀ ≤ m →
      MassGap.ContactDominance.farShare (MassGap.EvenAperture.readEven p β) m ≤ a m) :
    ∃ B : ℝ, ∀ (p : MassGap.EvenAperture.EvenAp) (β : ℝ),
      MassGap.EvenAperture.d2Even p β ≤ B :=
  ⟨(m₀ : ℝ) ^ 2 + ∑' m : ℕ, (2 * (m : ℝ) + 1) * a m, fun p β =>
    MassGap.ContactDominance.circ_moment_le_of_tail_envelope
      (MassGap.EvenAperture.readEven p β) m₀ a ha0 (ha p β) hs⟩

#print axioms substrate_even_of_tail_envelope

/-- `substrate_even_of_tail_envelope` with the envelope asked only at even apertures of extent at
least `N₀`, and the conclusion in the matching restricted form with `N₁ := N₀`.

DERIVED: `0` is the lower bound on the envelope; `2` and `1` are the layer weight `2 * m + 1`. -/
theorem large_aperture_bound_of_tail_envelope {N₀ : ℕ} (m₀ : ℕ) (a : ℕ → ℝ)
    (ha0 : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * a m))
    (ha : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (m : ℕ), m₀ ≤ m →
      MassGap.ContactDominance.farShare (MassGap.EvenAperture.readEven p β) m ≤ a m) :
    ∃ B : ℝ, ∃ N₁ : ℕ, ∀ (p : MassGap.EvenAperture.EvenAp), N₁ ≤ p.1 → ∀ (β : ℝ),
      MassGap.EvenAperture.d2Even p β ≤ B :=
  ⟨(m₀ : ℝ) ^ 2 + ∑' m : ℕ, (2 * (m : ℝ) + 1) * a m, N₀, fun p hp β =>
    MassGap.ContactDominance.circ_moment_le_of_tail_envelope
      (MassGap.EvenAperture.readEven p β) m₀ a ha0 (ha p hp β) hs⟩

#print axioms large_aperture_bound_of_tail_envelope

/-- `confines_of_large_aperture_bound` with its hypothesis supplied by
`large_aperture_bound_of_tail_envelope`: a summable-weighted far-share envelope, asked only beyond a
cut and only at large apertures, gives `ApertureRoute.ConfinesAtAnAperture`.

DERIVED: `0` is the lower bound on the envelope; `2` and `1` are the layer weight `2 * m + 1`. -/
theorem confines_of_tail_envelope {N₀ : ℕ} (m₀ : ℕ) (a : ℕ → ℝ)
    (ha0 : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * a m))
    (ha : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (m : ℕ), m₀ ≤ m →
      MassGap.ContactDominance.farShare (MassGap.EvenAperture.readEven p β) m ≤ a m) :
    MassGap.ApertureRoute.ConfinesAtAnAperture :=
  confines_of_large_aperture_bound (large_aperture_bound_of_tail_envelope m₀ a ha0 hs ha)

#print axioms confines_of_tail_envelope

/-- `ApertureRoute.flagship_of_confinement_at_an_aperture` at `confines_of_tail_envelope`.

DERIVED: `0` is the lower bound on the envelope; `2` and `1` are the layer weight `2 * m + 1`. -/
theorem flagship_of_tail_envelope {N₀ : ℕ} (m₀ : ℕ) (a : ℕ → ℝ)
    (ha0 : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * a m))
    (ha : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (m : ℕ), m₀ ≤ m →
      MassGap.ContactDominance.farShare (MassGap.EvenAperture.readEven p β) m ≤ a m) :
    MassGap.ApertureRoute.FlagshipAt (confines_of_tail_envelope m₀ a ha0 hs ha) :=
  MassGap.ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_tail_envelope

/-! ### The instance `a m = C / (m + 1) ^ 3` -/

/-- For `0 ≤ C`, `fun m => (2 * m + 1) * (C / (m + 1) ^ 3)` is summable. The bound
`2 * m + 1 ≤ 2 * (m + 1)` reduces the cube to a square, and
`ContactDominance.summable_inv_succ_sq` scaled by `2 * C` dominates it.

Scope: the exponent `3` is what makes the weighted series converge. With `2` in its place the
weighted series is harmonic, and `ContactDominance.square_share_is_not_enough` exhibits reads whose
far share stays under a square envelope at every aperture with unbounded moments.

DERIVED: `0` is the lower bound on `C`; the leading `2` and the first `1` are the layer weight
`2 * m + 1`; the second `1` is the `+ 1` in `(m + 1)` keeping the denominator nonzero at `m = 0`;
`3` is the exponent, the first integer for which the weighted series converges. -/
theorem summable_cubic_weight {C : ℝ} (hC : 0 ≤ C) :
    Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * (C / ((m : ℝ) + 1) ^ 3)) := by
  have hnn : ∀ m : ℕ, (0 : ℝ) ≤ C / ((m : ℝ) + 1) ^ 3 :=
    fun m => div_nonneg hC (by positivity)
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (by positivity) (hnn m)) (fun m => ?_)
    ((MassGap.ContactDominance.summable_inv_succ_sq).mul_left (2 * C))
  have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hle : (2 * (m : ℝ) + 1) ≤ 2 * ((m : ℝ) + 1) := by linarith
  calc (2 * (m : ℝ) + 1) * (C / ((m : ℝ) + 1) ^ 3)
      ≤ (2 * ((m : ℝ) + 1)) * (C / ((m : ℝ) + 1) ^ 3) :=
        mul_le_mul_of_nonneg_right hle (hnn m)
    _ = 2 * C * (1 / ((m : ℝ) + 1) ^ 2) := by
        field_simp

#print axioms summable_cubic_weight

/-- `flagship_of_tail_envelope` at the envelope `a m = C / (m + 1) ^ 3`, with nonnegativity from
`div_nonneg` and summability from `summable_cubic_weight`. The hypothesis is one constant `C`, one
cut `m₀` and one aperture floor `N₀`: the far share is at most `C / (m + 1) ^ 3` beyond the cut, at
every coupling, from that extent onwards.

Scope: the nonpositive half-line, extents below `N₀` and circle distances below `m₀` are all outside
the hypothesis.

DERIVED: `0` is the lower bound on `C`; `1` occurs twice, as the `+ 1` in each copy of `(m + 1)`,
keeping the denominator nonzero at `m = 0`; `3` occurs twice, as the exponent in each copy of the
envelope — `summable_cubic_weight`'s exponent, the first integer for which the weighted series
converges. -/
theorem flagship_of_cubic_tail_share {N₀ m₀ : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (m : ℕ), m₀ ≤ m →
      MassGap.ContactDominance.farShare (MassGap.EvenAperture.readEven p β) m
        ≤ C / ((m : ℝ) + 1) ^ 3) :
    MassGap.ApertureRoute.FlagshipAt
      (confines_of_tail_envelope (N₀ := N₀) m₀ (fun m => C / ((m : ℝ) + 1) ^ 3)
        (fun m => div_nonneg hC (by positivity)) (summable_cubic_weight hC) ha) :=
  MassGap.ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_cubic_tail_share


/-! ## §6 The geometric envelope

§5's envelope is a power. A geometric envelope `C * r ^ m` with `r < 1` is the shape a decay rate
supplies: `‖C τ‖ ≤ M * exp (-Δ * τ)` with `Δ > 0` is `r = exp (-Δ)`.
`Infer.Horizon` in `entroptics-infer` assumes `z n ≤ M * r ^ n` with `r < 1`;
`Forgetting.forgets_of_margin` consumes a margin `r < 1` on the modes; and
`CertifiedGap.ratio_lt_one_of_certified` produces such an `r` from a numerical band.

`summable_geometric_weight` is the one new fact: `(2 * m + 1) * r ^ m` splits into `2 * (m * r ^ m)`
and `r ^ m`, and `summable_pow_mul_geometric_of_norm_lt_one` gives both at `‖r‖ < 1`.
`confines_of_geometric_far_share` and `flagship_of_geometric_far_share` run §5's chain there. The
geometric far share is a hypothesis in both.
-/

/-- For `0 ≤ r < 1`, `fun m => (2 * m + 1) * (C * r ^ m)` is summable. The summand is
`2 * C * (m ^ 1 * r ^ m) + C * (m ^ 0 * r ^ m)`, and
`summable_pow_mul_geometric_of_norm_lt_one` gives both pieces at `‖r‖ < 1`.

Scope: `C` is unconstrained in sign, since summability is preserved by scaling.

DERIVED: `0` is the lower bound on `r`, needed to identify `‖r‖` with `r`; `1` is the upper bound on
`r`, the convergence threshold for a geometric series; `2` and the second `1` are the layer weight
`2 * m + 1`, which is `(m + 1) ^ 2 - m ^ 2`. -/
theorem summable_geometric_weight {C r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * (C * r ^ m)) := by
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have h1 : Summable (fun m : ℕ => (m : ℝ) ^ 1 * r ^ m) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have h0 : Summable (fun m : ℕ => (m : ℝ) ^ 0 * r ^ m) :=
    summable_pow_mul_geometric_of_norm_lt_one 0 hnorm
  refine ((h1.mul_left (2 * C)).add (h0.mul_left C)).congr (fun m => ?_)
  ring

#print axioms summable_geometric_weight

/-- `confines_of_tail_envelope` at the envelope `a m = C * r ^ m`, with `0 ≤ C`, `0 ≤ r < 1`,
nonnegativity from `mul_nonneg` and `pow_nonneg`, and summability from `summable_geometric_weight`.

DERIVED: `0` occurs twice, as the lower bound on `C` and on `r`; `1` is the upper bound on `r`, the
convergence threshold for a geometric series. -/
theorem confines_of_geometric_far_share {N₀ m₀ : ℕ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (m : ℕ), m₀ ≤ m →
      MassGap.ContactDominance.farShare (MassGap.EvenAperture.readEven p β) m ≤ C * r ^ m) :
    MassGap.ApertureRoute.ConfinesAtAnAperture :=
  confines_of_tail_envelope (N₀ := N₀) m₀ (fun m => C * r ^ m)
    (fun m => mul_nonneg hC (pow_nonneg hr0 m)) (summable_geometric_weight hr0 hr1) ha

#print axioms confines_of_geometric_far_share

/-- `ApertureRoute.flagship_of_confinement_at_an_aperture` at `confines_of_geometric_far_share`: a
geometric far-share envelope `C * r ^ m` with `0 ≤ r < 1`, beyond a cut and from some extent onwards,
gives `ApertureRoute.FlagshipAt`.

Writing `r = exp (-Δ)` puts the hypothesis in the form a decay rate `Δ > 0` supplies.
`Forgetting.forgets_iff_margin` characterises such a margin and
`CertifiedGap.ratio_lt_one_of_certified` produces one from a numerical band; neither is used here.

DERIVED: `0` occurs twice, as the lower bound on `C` and on `r`; `1` is the upper bound on `r`, the
convergence threshold for a geometric series. -/
theorem flagship_of_geometric_far_share {N₀ m₀ : ℕ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (m : ℕ), m₀ ≤ m →
      MassGap.ContactDominance.farShare (MassGap.EvenAperture.readEven p β) m ≤ C * r ^ m) :
    MassGap.ApertureRoute.FlagshipAt (confines_of_geometric_far_share hC hr0 hr1 ha) :=
  MassGap.ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_geometric_far_share


/-! ## The scope of `ApertureRoute.FlagshipAt`

Every `flagship_of_…` here ends at `ApertureRoute.flagship_of_confinement_at_an_aperture`.
`MassGap.FlagshipScope`, not imported here, measures what that endpoint asserts:

* `flagship_for_bogus` proves the whole flagship conclusion — the gap clause, `μ - κ < 0`, the
  isotropy clause and the OS0–OS3 continuum measure — for `bogusWilson`, an object containing no
  read, correlation, gauge group or lattice, whose tension is the constant `0`.
* `gap_summand_is_manufactured`: the summand the gap clause is about is `exp (-(κ₀ - μ)) ^ τ` — one
  mode, weight `1`, magnitude equal to its own bound.
* `flagship_measure_half_needs_no_hypothesis`: the measure half adds no hypothesis beyond
  `ConfinesAtAnAperture`, which is its one argument.
* `Q_is_constant_in_the_test_configuration`: OS1 and OS3 hold because the reflected form does not
  depend on the components those actions move.

The statement in these chains that is about the Wilson correlation is
`ApertureRoute.ConfinesAtAnAperture`: it is about `cosAvgEven` of `readEven`, hence about
`wilsonCorrAt` at an even aperture. Each `confines_of_…` here is that statement; each
`flagship_of_…` is the packaging the assembly consumes.
-/
end MassGap.MomentArms
