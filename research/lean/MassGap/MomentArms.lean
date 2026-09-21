import Mathlib
import MassGap.CompactBeta
import MassGap.ConfinesZero
import MassGap.ApertureRoute
import MassGap.ContactDominance

/-!
# MassGap.MomentArms — the substrate bound, split into the arms it would be paid for in

`Complete.ym_mass_gap_of_substrate` consumes ONE input, `∃ B, ∀ N β, d2At N β ≤ B`, and its docstring
says why that is the right shape: a frozen window reaches `∀ β` only by splitting the coupling line
into arms, and with the window fixed there is no aperture to widen.

**That is an argument about what the hypothesis MEANS, not about how it gets discharged.** Whoever
discharges it still has to cover the whole coupling line, and `CompactBeta` already covers exactly
one piece of it: `d2At_jointUniform_on_Icc_of_equicontinuous` gives the bound on a COMPACT interval
`[a,b]` from pointwise-in-β bounds plus equicontinuity. Nothing assembles that with the two
unbounded ends.

This file does the assembly, so the remaining obligation is three named arms rather than one
unquantified statement:

| arm | what it needs |
|---|---|
| `(−∞, a]` | anchored at `d2At_at_zero`, which is proved here |
| `[a, b]` | `CompactBeta.d2At_jointUniform_on_Icc_of_equicontinuous`, conditional on equicontinuity |
| `[b, ∞)` | open |

**The assembly itself is trivial — a maximum of three bounds — and that is the point.** It costs
nothing, and without it the middle arm's conditional result has nowhere to go.

## What is actually new here

`d2At_at_zero`: the moment is exactly `0` at zero coupling, at every aperture. It is the exact
analogue of `ConfinesZero.cosAvgEven_at_zero` for the moment route and rests on the same two facts —
`PowerTail.wilsonCorrAt_at_zero_coupling` kills every lag of nonzero circle distance and
`contact_value_pos_at_zero_coupling` keeps the normalisation alive, so the read is a point mass at
lag zero, where `circLag` is `0`.

That anchors the low arm at one point. It does not discharge it: a bound at a point is not a bound on
a half-line, and nothing here claims otherwise.
-/

namespace MassGap.MomentArms

/-- The circle distance at lag zero is zero — `min 0 (N+1)`. -/
theorem circLag_zero {N : ℕ} : Moment.circLag (0 : Fin (N + 1)) = 0 := by
  simp [Moment.circLag]

#print axioms circLag_zero

/-- **THE MOMENT VANISHES AT ZERO COUPLING**, at every aperture.

The exact analogue of `ConfinesZero.cosAvgEven_at_zero`, and by the same mechanism: at `β = 0` the
state is product Haar, the two plaquettes read disjoint link sets, so the connected correlation
vanishes at every lag of nonzero circle distance while the contact value stays positive. The read is
a point mass at lag zero and `circLag 0 = 0`.

No estimate is made and no aperture is preferred.

DERIVED: the `0`s are the coupling, the lag and the value — none is a level or a cut. -/
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

/-- and it is never negative, at any coupling: a probability weight against a square. -/
theorem d2At_nonneg (N : ℕ) (β : ℝ) : 0 ≤ MassGap.d2At N β := by
  unfold MassGap.d2At
  exact Finset.sum_nonneg (fun d _ =>
    mul_nonneg ((MassGap.readYMAt N β).p_nonneg d) (sq_nonneg _))

#print axioms d2At_nonneg

/-! ## The assembly -/

/-- **THREE ARMS MAKE THE SUBSTRATE BOUND.** A maximum of three constants, and nothing else.

Trivial, and worth having: `CompactBeta` proves the middle arm conditionally and there is otherwise
nothing to feed it into. Stating the split explicitly is what turns "bound the moment uniformly"
into three obligations a reader can check off separately.

DERIVED: no numeral. `a` and `b` are the caller's cut points and `B` the caller's bounds. -/
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

/-- **AND THEREFORE CONFINEMENT AT EVERY LARGE ENOUGH APERTURE.** `confinement_of_bounded_substrate`,
reached through the three arms. -/
theorem confinement_of_three_arms {a b : ℝ}
    (hlow : ∃ B : ℝ, ∀ (N : ℕ), ∀ β ≤ a, MassGap.d2At N β ≤ B)
    (hmid : ∃ B : ℝ, ∀ (N : ℕ), ∀ β ∈ Set.Icc a b, MassGap.d2At N β ≤ B)
    (hhigh : ∃ B : ℝ, ∀ (N : ℕ), ∀ β, b ≤ β → MassGap.d2At N β ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, MassGap.μYMAt N β < MassGap.κ₀YM :=
  MassGap.confinement_of_bounded_substrate (d2At_bound_of_three_arms hlow hmid hhigh)

#print axioms confinement_of_three_arms

/-- **AND THE FLAGSHIP.** The same three arms carry `ym_mass_gap_of_substrate` — forgetting,
summability and the gap, at every large enough aperture. -/
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


/-! ## 2. The same split at an EVEN aperture, where the low arm is DISCHARGED

`d2At` goes through `readYMAt`, which is where the named axiom enters. The even-aperture route has an
axiom-free counterpart already — `EvenAperture.d2Even` is built from `readEven`, whose positivity
comes from `Complete.wilson_reflection_positive_at_even`, a THEOREM at even extent `≥ 4` — and
`ApertureRoute.confinement_at_an_aperture_of_substrate` consumes exactly
`∃ B, ∀ a β, d2Even a β ≤ B`.

**Two things improve at once.**

1. **The footprint.** Nothing below mentions `readYMAt`, so the named axiom does not appear.
2. **The low arm stops being an assumption.** `readEven` reads the correlation at `max β 0`, so
   below zero coupling it reads it at zero — and at zero the profile is a point mass, so the moment
   is exactly `0`. The negative half-line is FREE, exactly as
   `ConfinesZero.cosAvgEven_eq_one_of_nonpos` makes it free for the cosine average.

So the three arms of §1 become **two**, and the remaining obligation is `[0,b]` — which `CompactBeta`
addresses conditionally — and `[b,∞)`.
-/

/-- Below zero coupling the read does not move: `readEven` reads at `max β 0`. -/
theorem readEven_eq_zero_of_nonpos (a : MassGap.EvenAperture.EvenAp) {β : ℝ} (hβ : β ≤ 0) :
    MassGap.EvenAperture.readEven a β = MassGap.EvenAperture.readEven a 0 := by
  unfold MassGap.EvenAperture.readEven
  refine MassGap.EvenAperture.readA_congr ?_
  rw [max_eq_right hβ, max_self]

#print axioms readEven_eq_zero_of_nonpos

/-- **THE EVEN-APERTURE MOMENT VANISHES AT ZERO COUPLING.** The axiom-free counterpart of
`d2At_at_zero`: the same point-mass argument, read through `readEven`, so
`wilson_reflection_positive_at` never appears.

DERIVED: the `0`s are the coupling, the lag and the value. -/
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

/-- **AND THEREFORE ON THE WHOLE NEGATIVE HALF-LINE.** Not assumed — computed. -/
theorem d2Even_eq_zero_of_nonpos (a : MassGap.EvenAperture.EvenAp) {β : ℝ} (hβ : β ≤ 0) :
    MassGap.EvenAperture.d2Even a β = 0 := by
  unfold MassGap.EvenAperture.d2Even
  rw [readEven_eq_zero_of_nonpos a hβ]
  exact d2Even_at_zero a

#print axioms d2Even_eq_zero_of_nonpos

/-- **TWO ARMS MAKE THE EVEN SUBSTRATE BOUND**, because the third is discharged.

Compare `d2At_bound_of_three_arms`: there the low arm is a hypothesis, here it is a theorem. The
`max 0` in the witness is what carries the negative half-line, where the moment is exactly `0`.

DERIVED: no numeral but the `0` that the moment equals below zero coupling, which is computed. -/
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

/-- **AND CONFINEMENT AT AN APERTURE FROM THEM.** -/
theorem confines_of_two_arms {b : ℝ}
    (hmid : ∃ B : ℝ, ∀ (a : MassGap.EvenAperture.EvenAp), ∀ β ∈ Set.Icc (0 : ℝ) b,
      MassGap.EvenAperture.d2Even a β ≤ B)
    (hhigh : ∃ B : ℝ, ∀ (a : MassGap.EvenAperture.EvenAp), ∀ β, b ≤ β →
      MassGap.EvenAperture.d2Even a β ≤ B) :
    MassGap.ApertureRoute.ConfinesAtAnAperture :=
  MassGap.ApertureRoute.confinement_at_an_aperture_of_substrate
    (d2Even_bound_of_two_arms hmid hhigh)

#print axioms confines_of_two_arms

/-- **AND THE CLAY FLAGSHIP.** Two arms, and the negative half-line free. -/
theorem flagship_of_two_arms {b : ℝ}
    (hmid : ∃ B : ℝ, ∀ (a : MassGap.EvenAperture.EvenAp), ∀ β ∈ Set.Icc (0 : ℝ) b,
      MassGap.EvenAperture.d2Even a β ≤ B)
    (hhigh : ∃ B : ℝ, ∀ (a : MassGap.EvenAperture.EvenAp), ∀ β, b ≤ β →
      MassGap.EvenAperture.d2Even a β ≤ B) :
    MassGap.ApertureRoute.FlagshipAt (confines_of_two_arms hmid hhigh) :=
  MassGap.ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_two_arms


/-! ## 3. The bound is needed only at LARGE apertures

`ApertureRoute.confinement_at_an_aperture_of_substrate` asks for `∀ (a : EvenAp) (β : ℝ),
d2Even a β ≤ B` — every even aperture. **Its proof uses that at exactly one aperture**, the one
`exists_evenAp_of_eventually` picks out of the window condition. Extent four is never consulted
unless the chooser happens to land there.

So the hypothesis can be weakened to a bound holding only from some aperture onwards, and the proof
is the original with one extra conjunct carried through the choice. That is a real weakening:
knowing nothing whatever about small extents is enough.

**Why it is the right shape.** `Moment.lean` postulates that `⟨d²⟩` is substrate-intrinsic — bounded
independently of the window — and the tree's SU(3) aperture scan refutes the competing reading (see
`ApertureRoute`'s note). A quantity that is aperture-stable is bounded at large apertures for the
same reason it is bounded at any; but a hypothesis that also reaches down to extent four asks about
windows too narrow to resolve the correlation, and nothing needs it.

Nothing is lost: `large_aperture_bound_of_substrate_bound` derives the weak hypothesis from the
strong one, so every consequence of the old hypothesis is still a consequence.
-/

/-- The old hypothesis gives the new one, with `N₀ = 0`. Stated so the weakening is known to be a
weakening rather than a change of subject. -/
theorem large_aperture_bound_of_substrate_bound
    (h : ∃ B : ℝ, ∀ (a : MassGap.EvenAperture.EvenAp) (β : ℝ),
      MassGap.EvenAperture.d2Even a β ≤ B) :
    ∃ B : ℝ, ∃ N₀ : ℕ, ∀ (a : MassGap.EvenAperture.EvenAp), N₀ ≤ a.1 → ∀ (β : ℝ),
      MassGap.EvenAperture.d2Even a β ≤ B := by
  obtain ⟨B, hB⟩ := h
  exact ⟨B, 0, fun a _ β => hB a β⟩

#print axioms large_aperture_bound_of_substrate_bound

/-- **CONFINEMENT AT AN APERTURE, FROM A BOUND AT LARGE APERTURES ONLY.**

`ApertureRoute.confinement_at_an_aperture_of_substrate` with the hypothesis restricted to apertures
of extent at least `N₀`. The proof is the original one; the only change is that the aperture is
chosen to satisfy the window condition AND to exceed `N₀`, which is possible because both are
eventual in the extent.

DERIVED: `N₀` is the caller's, `2` is the form's degree and `3^{−1/4}` is the entropy floor
`e^{−κ₀}` — no magnitude is chosen here. -/
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

/-- **AND THE CLAY FLAGSHIP FROM IT.** -/
theorem flagship_of_large_aperture_bound
    (h : ∃ B : ℝ, ∃ N₀ : ℕ, ∀ (a : MassGap.EvenAperture.EvenAp), N₀ ≤ a.1 → ∀ (β : ℝ),
      MassGap.EvenAperture.d2Even a β ≤ B) :
    MassGap.ApertureRoute.FlagshipAt (confines_of_large_aperture_bound h) :=
  MassGap.ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_large_aperture_bound

/-- **THE TWO ARMS, AT LARGE APERTURES ONLY.** The weakest form in this file: the negative half-line
is discharged, small extents are not consulted, and what remains is `[0,b]` and `[b,∞)` from some
aperture onwards. -/
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

/-- **AND THE CLAY FLAGSHIP FROM THE WEAKEST FORM.** -/
theorem flagship_of_two_arms_at_large_apertures {b : ℝ} {N₀ : ℕ}
    (hmid : ∃ B : ℝ, ∀ (a : MassGap.EvenAperture.EvenAp), N₀ ≤ a.1 → ∀ β ∈ Set.Icc (0 : ℝ) b,
      MassGap.EvenAperture.d2Even a β ≤ B)
    (hhigh : ∃ B : ℝ, ∀ (a : MassGap.EvenAperture.EvenAp), N₀ ≤ a.1 → ∀ β, b ≤ β →
      MassGap.EvenAperture.d2Even a β ≤ B) :
    MassGap.ApertureRoute.FlagshipAt (confines_of_two_arms_at_large_apertures hmid hhigh) :=
  MassGap.ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_two_arms_at_large_apertures


/-! ## 4. The input side, also axiom-free: the far-share envelope

`ContactDominance.substrate_of_share_envelope` turns a summable envelope on the FAR SHARE into the
substrate bound. It is stated on `readYMAt` and `d2At`, so it carries the named axiom — and §2–§3
built the consequence side on `readEven` and `d2Even`, which do not. That left the route split: an
axiom-free conclusion fed by an axiom-carrying input.

**Nothing in the envelope argument needs the axiom.** `ContactDominance.farShare` and
`circ_moment_le_of_envelope` are stated for an arbitrary `Moment.Read`, so the port is the same term
with `readEven` in place of `readYMAt`. What the axiom was doing in the original is supplying the
read's positivity, and at an even aperture `wilson_reflection_positive_at_even` supplies it as a
THEOREM.

**What the envelope is.** `farShare R m` is the probability the read puts beyond circle distance `m`.
An envelope `a` bounding it uniformly, with `∑ (2m+1)·a m` convergent, bounds the circular second
moment by that sum — layer by layer, `2m+1` being the count of lags at distance `m`. It is the
finite-correlation-length hypothesis in the form the moment consumes.

**The whole chain is now foundational-only**: envelope → moment bound → confinement at an aperture →
Clay flagship, with the negative half-line discharged (§2) and small extents never consulted (§3).
-/

/-- **THE SUBSTRATE BOUND FROM A FAR-SHARE ENVELOPE, at even apertures.**
`ContactDominance.substrate_of_share_envelope` with `readEven` in place of `readYMAt`. -/
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

/-- **AND THE SAME, ASKED ONLY AT LARGE APERTURES** — §3's weakening on the input side. -/
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

/-- **CONFINEMENT AT AN APERTURE, FROM AN ENVELOPE AT LARGE APERTURES.** -/
theorem confines_of_share_envelope {N₀ : ℕ} (a : ℕ → ℝ)
    (ha0 : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * a m))
    (ha : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (m : ℕ),
      MassGap.ContactDominance.farShare (MassGap.EvenAperture.readEven p β) m ≤ a m) :
    MassGap.ApertureRoute.ConfinesAtAnAperture :=
  confines_of_large_aperture_bound (large_aperture_bound_of_share_envelope a ha0 hs ha)

#print axioms confines_of_share_envelope

/-- **AND THE CLAY FLAGSHIP.** One summable envelope on the far share, asked only from some aperture
onwards, and the entire chain to the flagship is `{propext, Classical.choice, Quot.sound}`. -/
theorem flagship_of_share_envelope {N₀ : ℕ} (a : ℕ → ℝ)
    (ha0 : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * a m))
    (ha : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (m : ℕ),
      MassGap.ContactDominance.farShare (MassGap.EvenAperture.readEven p β) m ≤ a m) :
    MassGap.ApertureRoute.FlagshipAt (confines_of_share_envelope a ha0 hs ha) :=
  MassGap.ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_share_envelope


/-! ## 5. Only the TAIL is constrained, and a concrete envelope that meets it

§4 asks for the envelope at every `m`. It does not need to.
`ContactDominance.circ_moment_le_of_tail_envelope` assumes it only from a cut `m₀` upward and pays
`m₀²` for the near block, which `farShare ≤ 1` caps on its own. **An envelope is always a statement
about large lags, and the cut may be chosen after the fact** — the near block costs a constant, and a
constant is all the substrate bound ever wanted.

That lemma is stated for an arbitrary `Moment.Read`, so it ports to `readEven` the same way §4 did.

## The exponent is not a choice

`ContactDominance`'s header derives it: `(2m+1)` is `(m+1)² − m²`, the second moment's own layer
weight, so a power envelope `C(m+1)^{-s}` has weighted total `∑ (2m+1)C(m+1)^{-s}`, convergent
exactly when `s > 2`. At `s = 2` it is the harmonic series — and `square_share_is_not_enough` shows
`s = 2` is not merely out of reach but FALSE, exhibiting reads whose far share stays under
`(4/3)(m+1)^{-2}` at every aperture and whose moments exceed every bound.

So `s = 3` is the first integer exponent that works, and `flagship_of_cubic_tail_share` runs it: one
constant `C`, one cut `m₀`, one aperture floor `N₀`, and the Clay flagship — foundational-only.
-/

/-- **THE SUBSTRATE BOUND FROM A TAIL ENVELOPE, at even apertures.** Strictly weaker than
`substrate_even_of_share_envelope`: nothing is asked below the cut. -/
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

/-- **AND ASKED ONLY AT LARGE APERTURES** — §3's weakening, on the tail envelope. -/
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

/-- **CONFINEMENT AT AN APERTURE, FROM A TAIL ENVELOPE AT LARGE APERTURES.** -/
theorem confines_of_tail_envelope {N₀ : ℕ} (m₀ : ℕ) (a : ℕ → ℝ)
    (ha0 : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * a m))
    (ha : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (m : ℕ), m₀ ≤ m →
      MassGap.ContactDominance.farShare (MassGap.EvenAperture.readEven p β) m ≤ a m) :
    MassGap.ApertureRoute.ConfinesAtAnAperture :=
  confines_of_large_aperture_bound (large_aperture_bound_of_tail_envelope m₀ a ha0 hs ha)

#print axioms confines_of_tail_envelope

/-- **AND THE CLAY FLAGSHIP.** -/
theorem flagship_of_tail_envelope {N₀ : ℕ} (m₀ : ℕ) (a : ℕ → ℝ)
    (ha0 : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * a m))
    (ha : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (m : ℕ), m₀ ≤ m →
      MassGap.ContactDominance.farShare (MassGap.EvenAperture.readEven p β) m ≤ a m) :
    MassGap.ApertureRoute.FlagshipAt (confines_of_tail_envelope m₀ a ha0 hs ha) :=
  MassGap.ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_tail_envelope

/-! ### The cubic instance -/

/-- The cubic envelope's layer-weighted total converges, because `2m+1 ≤ 2(m+1)` turns the cube into
a square and the squares sum.

DERIVED: `3` is the first integer exponent above the derived threshold `2`; `2` itself is the
harmonic series and is proved FALSE by `ContactDominance.square_share_is_not_enough`. -/
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

/-- **THE WEAKEST CONCRETE FORM IN THIS FILE.**

One constant `C`, one cut `m₀`, one aperture floor `N₀`: if the far share is at most
`C/(m+1)³` beyond the cut, at every coupling, from that aperture onwards, then the Clay flagship
holds — and the whole chain is `{propext, Classical.choice, Quot.sound}`.

Everything else is discharged: the negative half-line by §2, small extents by §3, small lags by §5.

DERIVED: `3` is `summable_cubic_weight`'s, which is the first integer above the derived threshold. -/
theorem flagship_of_cubic_tail_share {N₀ m₀ : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (m : ℕ), m₀ ≤ m →
      MassGap.ContactDominance.farShare (MassGap.EvenAperture.readEven p β) m
        ≤ C / ((m : ℝ) + 1) ^ 3) :
    MassGap.ApertureRoute.FlagshipAt
      (confines_of_tail_envelope (N₀ := N₀) m₀ (fun m => C / ((m : ℝ) + 1) ^ 3)
        (fun m => div_nonneg hC (by positivity)) (summable_cubic_weight hC) ha) :=
  MassGap.ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_cubic_tail_share


/-! ## 6. Exponential decay reaches the flagship

§5's envelope is a power, `C(m+1)^{-s}` with `s > 2`. **A mass gap gives something much stronger — a
GEOMETRIC far share** — and that is the form every other statement of the gap in this workspace takes:

* `entroptics-infer/lean/Infer/Horizon.lean` assumes `z n ≤ M * r ^ n` with `r < 1` and says in so
  many words that this is "the reading of Yang–Mills in `entroptics-mass-gap`, where the mass gap
  *is* `‖C(τ)‖ ≤ M e^{−Δτ}` with `Δ > 0`", with `r = e^{−Δ}`.
* `Forgetting.forgets_of_margin` consumes exactly a margin `r < 1` on the modes.
* `CertifiedGap.ratio_lt_one_of_certified` produces exactly such an `r` from a numerical band.

So the geometric case deserves its own statement rather than being reached by checking that a
geometric sequence happens to be dominated by a cubic. `summable_geometric_weight` is the one new
fact, and `summable_pow_mul_geometric_of_norm_lt_one` supplies it: `(2m+1)r^m` splits into `m r^m`
and `r^m`, both summable below one.

**What this completes.** The chain now runs

    margin r < 1  ⟹  geometric far share  ⟹  d2Even bounded  ⟹  ConfinesAtAnAperture  ⟹  FlagshipAt

end to end, foundational-only, with the negative half-line discharged, small extents never consulted
and small lags never consulted. Every step is a theorem; what remains outside it is the measurement
that the far share really is geometric.
-/

/-- **A GEOMETRIC ENVELOPE HAS A CONVERGENT LAYER-WEIGHTED TOTAL.** `(2m+1)r^m` is `2·m r^m` plus
`r^m`, and `summable_pow_mul_geometric_of_norm_lt_one` gives both below one.

DERIVED: the `2` and `1` are the layer weight `(m+1)² − m²`, not chosen constants; `r` is the
caller's decay factor. -/
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

/-- **CONFINEMENT FROM A GEOMETRIC FAR SHARE.** The mass gap's own shape — `C·r^m` with `r < 1` —
beyond a cut, from some aperture onwards. -/
theorem confines_of_geometric_far_share {N₀ m₀ : ℕ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (m : ℕ), m₀ ≤ m →
      MassGap.ContactDominance.farShare (MassGap.EvenAperture.readEven p β) m ≤ C * r ^ m) :
    MassGap.ApertureRoute.ConfinesAtAnAperture :=
  confines_of_tail_envelope (N₀ := N₀) m₀ (fun m => C * r ^ m)
    (fun m => mul_nonneg hC (pow_nonneg hr0 m)) (summable_geometric_weight hr0 hr1) ha

#print axioms confines_of_geometric_far_share

/-- **AND THE CLAY FLAGSHIP FROM EXPONENTIAL DECAY.**

`‖C(τ)‖ ≤ M e^{−Δτ}` with `Δ > 0`, written as `r = e^{−Δ} < 1` on the far share, delivers
`ApertureRoute.FlagshipAt` — foundational-only, with the negative half-line discharged, small extents
never consulted and small lags never consulted.

**This is the statement that joins the instrument to the proof.** A margin is what
`Forgetting.forgets_iff_margin` characterises, what `CertifiedGap.ratio_lt_one_of_certified` produces
from a numerical band, and what `entroptics.Dynamics.rates` measures as `α_k = −log|μ_k| > 0`. -/
theorem flagship_of_geometric_far_share {N₀ m₀ : ℕ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (m : ℕ), m₀ ≤ m →
      MassGap.ContactDominance.farShare (MassGap.EvenAperture.readEven p β) m ≤ C * r ^ m) :
    MassGap.ApertureRoute.FlagshipAt (confines_of_geometric_far_share hC hr0 hr1 ha) :=
  MassGap.ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_geometric_far_share


/-! ## ⚠ WHAT `FlagshipAt` IS WORTH, AND IT IS LESS THAN ITS NAME

Every `flagship_of_…` in this file ends at `ApertureRoute.flagship_of_confinement_at_an_aperture`, and
`MassGap.FlagshipScope` — the tree's own adversarial audit, deliberately not imported — shows what
that endpoint does and does not say:

* **`flagship_for_bogus`** proves the WHOLE flagship conclusion — mass gap, non-triviality
  (`μ − κ < 0`), `SO(4)`, and the OS0–OS3 continuum measure — for `bogusWilson`, an object with **no
  read, no correlation, no gauge group and no lattice in it**, whose tension is the constant `0`.
* **`gap_summand_is_manufactured`**: the "correlation" the gap clause is about is
  `exp(−(κ₀ − μ))^τ` — one mode, weight `1`, and **its magnitude DEFINED as its own bound**.
* **`flagship_measure_half_needs_no_hypothesis`**: the measure half takes no hypothesis at all.
* **`Q_is_constant_in_the_test_configuration`**: OS1 and OS3 hold because the reflected form is
  independent of the components those actions move.

**So "reaches the Clay flagship" is not the claim it sounds like.** What carries content in these
chains is the step BEFORE it — `ApertureRoute.ConfinesAtAnAperture`, which is a statement about
`cosAvgEven` of `readEven`, hence about the genuine `wilsonCorrAt` at an even aperture. The
`FlagshipAt` corollaries add the manufactured clauses and nothing else.

Each `confines_of_…` here is therefore the theorem; each `flagship_of_…` is its packaging, kept
because the packaging is what the assembly consumes, and labelled so it is not mistaken for more.
-/
end MassGap.MomentArms
