import Mathlib
import MassGap.ConfinesEight

/-!
# MassGap.FlatProfileAllApertures — no choice of aperture rescues the shape-facts route

`ApertureRoute.ConfinesAtAnAperture` is `∃ a : EvenAp, ∀ β, c < cosAvgEven a β` — EXISTENTIAL over
apertures. That quantifier is the route's one degree of freedom, and the threshold table invites the
thought that it can be spent well:

    extent      4         6         8        10        12
    threshold   0.0186240 0.0337959 0.0354567 0.0302593 0.0250940

The relief rises to extent eight and falls after (`LagTwoEight.bEight_pos` says why). Reading that
table it is natural to ask what happens at extent 100, or 10^6 — whether some far aperture makes the
obligation easy. **This file answers it once, for every even aperture at the same time: it does
not.**

## What is proved

`LagTwoBound`, `LagTwoSix` and `LagTwoEight` each exhibit a profile at their own extent, sitting
exactly at their own threshold, that fails their own criterion — that is what makes those thresholds
SHARP. Three extents, three witnesses, three separate arguments. The statement here is one witness
that works at EVERY even aperture, and it is the simplest one there is:

    ρ ≡ 1

The constant profile satisfies every shape fact the tree states — nonnegativity, strict contact
positivity, contact maximality, antitonicity in the circle distance, reflection symmetry, and both
the Cauchy–Schwarz and slab-quadratic inequalities — with EQUALITY throughout. And its cosine
average is exactly `0` at every even aperture, because the cosines of a full turn cancel in
antipodal pairs (`cos_circle_sum_eq_zero`). Since `0 < 3^{-1/4}`, it fails the criterion at every
aperture, by a margin that does not shrink with the extent.

## Why this is the right no-go, and what it does NOT say

It does not say the mass gap is false — the constant profile is not a Wilson correlation at any
coupling. `ConfinesZero.cosAvgEven_at_zero` proves the actual Wilson profile is a point mass at zero
coupling, cosine average exactly `1`, and `continuous_cosAvgEven` carries that onto a neighbourhood.
What it says is that **no assembly of the tree's β-uniform shape facts can decide the criterion at
any aperture**, so the aperture existential cannot be spent to avoid a dynamical estimate. The
obligation is β-dependence, and it is β-dependence at every extent equally.

This is the aperture-indexed companion to `ClayAssembly.flat_profile_admits_no_uniform_quartic_constant`
(which closes the same door on the substrate route) and to
`FreeFieldLagTwo.flat_profile_meets_every_uniform_fact` (which establishes the premise set at extent
four). Together the three say: the flat profile defeats BOTH routes at EVERY aperture.

DERIVED: no numeral in this file is a magnitude. `2 * m` is the even extent, `2` and `≤` in `2 ≤ m`
are `EvenAp`'s own membership condition, `0` is the contact lag and the value the cosine average
takes, `1` is the constant profile's single value, and `2 * π` is one turn of the circle. The floor
`3 ^ (-(1:ℝ)/4)` is `ApertureRoute`'s constant, carried through unchanged.
-/

namespace MassGap.FlatProfileAllApertures

open MassGap MassGap.EvenAperture MassGap.ApertureRoute MassGap.ConfinesZero

/-! ## 1. The cosines of a full turn cancel -/

/-- **A half-turn flips the cosine.** `cos(2π(m+i)/(2m)) = −cos(2πi/(2m))`, because the shift by `m`
of `2m` is a shift of the angle by exactly `π`.

DERIVED: `m` is half the extent and `2 * m` the extent; `2 * π` is one turn. -/
theorem cos_half_turn_shift (m : ℕ) (hm : 0 < m) (i : ℕ) :
    Real.cos (2 * Real.pi * ((m + i : ℕ) : ℝ) / (2 * m))
      = - Real.cos (2 * Real.pi * (i : ℝ) / (2 * m)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h2m : (2 * (m : ℝ)) ≠ 0 := ne_of_gt (by linarith)
  have harg : 2 * Real.pi * ((m : ℝ) + (i : ℝ)) / (2 * (m : ℝ))
      = 2 * Real.pi * (i : ℝ) / (2 * (m : ℝ)) + Real.pi := by
    field_simp
    ring
  push_cast
  rw [harg, Real.cos_add, Real.cos_pi, Real.sin_pi]
  ring

#print axioms cos_half_turn_shift

/-- **THE FULL TURN SUMS TO ZERO**, at every even extent. The circle splits at its midpoint and the
upper half is the lower half negated, term by term, by `cos_half_turn_shift`.

This is the one arithmetic fact the no-go needs, and it is where the EVENNESS of the extent is used:
an odd extent has no exact antipode and the pairing does not close. -/
theorem cos_circle_sum_eq_zero (m : ℕ) (hm : 0 < m) :
    ∑ d ∈ Finset.range (2 * m), Real.cos (2 * Real.pi * (d : ℝ) / (2 * m)) = 0 := by
  set F : ℕ → ℝ := fun d => Real.cos (2 * Real.pi * (d : ℝ) / (2 * m)) with hFdef
  have hsplit : ∑ d ∈ Finset.range (2 * m), F d
      = (∑ d ∈ Finset.range m, F d) + ∑ d ∈ Finset.Ico m (2 * m), F d :=
    (Finset.sum_range_add_sum_Ico F (by omega : m ≤ 2 * m)).symm
  have hre : ∑ d ∈ Finset.Ico m (2 * m), F d = ∑ i ∈ Finset.range m, F (m + i) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [show 2 * m - m = m from by omega]
  have hsum : ∑ i ∈ Finset.range m, F (m + i) = ∑ i ∈ Finset.range m, (-(F i)) :=
    Finset.sum_congr rfl (fun i _ => cos_half_turn_shift m hm i)
  have hcancel : ∑ i ∈ Finset.range m, (-(F i)) = - ∑ i ∈ Finset.range m, F i := by
    simp
  rw [hsplit, hre, hsum, hcancel]
  ring

#print axioms cos_circle_sum_eq_zero

/-- **The circle distance does not change the cosine.** `cos(2π·circLag d/(N+1)) = cos(2πd/(N+1))`,
because `circLag d` is either `d` itself or `N+1-d`, and a full turn is a period.

The tree proves this inside `Moment.Read.cos_theta_circ`, which needs a `Read` to state it on. This
is the same arithmetic with no read attached, so it can be applied to a bare index. -/
theorem cos_circLag_eq {N : ℕ} (d : Fin (N + 1)) :
    Real.cos (2 * Real.pi * (MassGap.Moment.circLag d : ℝ) / ((N : ℝ) + 1))
      = Real.cos (2 * Real.pi * ((d : ℕ) : ℝ) / ((N : ℝ) + 1)) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rcases le_total ((d : ℕ)) (N + 1 - (d : ℕ)) with h | h
  · rw [MassGap.Moment.circLag, min_eq_left h]
  · rw [MassGap.Moment.circLag, min_eq_right h]
    have hd : ((N + 1 - (d : ℕ) : ℕ) : ℝ) = ((N : ℝ) + 1) - (d : ℕ) := by
      have hle : (d : ℕ) ≤ N + 1 := le_of_lt d.isLt
      push_cast [Nat.cast_sub hle]
      ring
    rw [hd]
    have hrw : 2 * Real.pi * (((N : ℝ) + 1) - (d : ℕ)) / ((N : ℝ) + 1)
        = 2 * Real.pi - 2 * Real.pi * (d : ℕ) / ((N : ℝ) + 1) := by
      field_simp
    rw [hrw, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
    ring

#print axioms cos_circLag_eq

/-- **THE COSINE AVERAGE OF THE FLAT PROFILE IS EXACTLY ZERO**, at every even aperture. The weights
are `1/(2m)` at every lag, so the average is the full-turn sum divided by the extent. -/
theorem flat_cosAvg_eq_zero (a : EvenAp) :
    ∑ d : Fin (a.1 + 1),
        ((1 : ℝ) / (∑ _d' : Fin (a.1 + 1), (1 : ℝ)))
          * Real.cos (2 * Real.pi * (MassGap.Moment.circLag d : ℝ) / ((a.1 : ℝ) + 1)) = 0 := by
  obtain ⟨m, hm, hm2⟩ := a.2
  have hmpos : 0 < m := by omega
  have hcast : ((a.1 : ℝ) + 1) = 2 * (m : ℝ) := by exact_mod_cast hm
  have hbase : ∑ d : Fin (a.1 + 1),
      Real.cos (2 * Real.pi * ((d : ℕ) : ℝ) / ((a.1 : ℝ) + 1)) = 0 := by
    rw [Fin.sum_univ_eq_sum_range
      (fun k : ℕ => Real.cos (2 * Real.pi * (k : ℝ) / ((a.1 : ℝ) + 1))) (a.1 + 1)]
    rw [hm, hcast]
    exact cos_circle_sum_eq_zero m hmpos
  simp only [cos_circLag_eq]
  rw [← Finset.mul_sum, hbase, mul_zero]

#print axioms flat_cosAvg_eq_zero

/-! ## 2. The no-go -/

/-- **NO EVEN APERTURE IS RESCUED BY THE SHAPE FACTS.**

At EVERY even aperture there is a profile satisfying every `β`-uniform shape fact the tree states —
strict positivity, contact maximality, antitonicity in the circle distance, the Cauchy–Schwarz
inequality `ρ(j)² ≤ ρ(0)·ρ(2j)`, and the slab quadratic `2ρ(j)² ≤ ρ(k)² + ρ(0)·ρ(k)` — whose cosine
average is exactly `0`, hence strictly BELOW the entropy floor `3^{-1/4}`.

Reflection symmetry `ρ(d) = ρ(n-d)` is not listed as a conjunct because it holds by CONSTRUCTION
here: the profile is read through `circLag`, and `circLag d = circLag (n-d)` is what `circLag`
means. Stating it would add nothing to check.

The two quantified conjuncts are STRONGER than the tree's own facts, not weaker: `SlabQuadratic`
states its quadratic at the single pair of lags `(1, 2)` and this witness meets it at every pair, so
no reading of the premise set makes the no-go easier than the tree's obligation.

So the existential over apertures in `ApertureRoute.ConfinesAtAnAperture` cannot be spent to avoid a
dynamical estimate: there is no far aperture at which the obligation becomes a consequence of shape.
The three per-extent sharpness results (`LagTwoBound`, `LagTwoSix.lagTwoThresholdSix_sharp`,
`LagTwoEight.lagTwoThresholdEight_sharp`) are the same conclusion at three extents; this is all of
them, with one witness.

DERIVED: every conjunct is a fact the tree proves of the Wilson profile with no coupling hypothesis;
the `1` is the constant profile's value and the `0` its cosine average. -/
theorem flat_profile_defeats_the_criterion_at_every_even_aperture (a : EvenAp) :
    ∃ ρ : ℕ → ℝ,
      (∀ j, 0 < ρ j) ∧
      (∀ j, ρ j ≤ ρ 0) ∧
      (∀ j k, j ≤ k → ρ k ≤ ρ j) ∧
      (∀ j, ρ j ^ 2 ≤ ρ 0 * ρ (2 * j)) ∧
      (∀ j k, 2 * ρ j ^ 2 ≤ ρ k ^ 2 + ρ 0 * ρ k) ∧
      0 < ∑ d : Fin (a.1 + 1), ρ (MassGap.Moment.circLag d) ∧
      ∑ d : Fin (a.1 + 1),
          (ρ (MassGap.Moment.circLag d)
              / (∑ d' : Fin (a.1 + 1), ρ (MassGap.Moment.circLag d')))
            * Real.cos (2 * Real.pi * (MassGap.Moment.circLag d : ℝ) / ((a.1 : ℝ) + 1))
        < (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
  refine ⟨fun _ => 1, fun _ => one_pos, fun _ => le_rfl, fun _ _ _ => le_rfl,
    fun _ => by norm_num, fun _ _ => by norm_num, ?_, ?_⟩
  · have hcard : ∑ _d : Fin (a.1 + 1), (1 : ℝ) = ((a.1 + 1 : ℕ) : ℝ) := by simp
    rw [hcard]
    have hn : (0 : ℕ) < a.1 + 1 := Nat.succ_pos _
    exact_mod_cast hn
  · have hz := flat_cosAvg_eq_zero a
    have hfloor : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
    simpa only [hz] using hfloor

#print axioms flat_profile_defeats_the_criterion_at_every_even_aperture

/-- **AND THE MARGIN DOES NOT SHRINK WITH THE EXTENT.** The failure is by the full floor
`3^{-1/4} = 0.7598…` at every even aperture, not by an amount that decays as the aperture grows.
So there is no sense in which a large aperture is "nearly enough" and a sharper shape fact would
close the remaining distance — the distance is the same at every extent. -/
theorem flat_profile_margin_is_aperture_independent (a : EvenAp) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4)
      - ∑ d : Fin (a.1 + 1),
          ((1 : ℝ) / (∑ _d' : Fin (a.1 + 1), (1 : ℝ)))
            * Real.cos (2 * Real.pi * (MassGap.Moment.circLag d : ℝ) / ((a.1 : ℝ) + 1))
        = (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
  rw [flat_cosAvg_eq_zero a]
  ring

#print axioms flat_profile_margin_is_aperture_independent

end MassGap.FlatProfileAllApertures
