import Mathlib
import MassGap.ConfinesEight
import MassGap.Spectral

/-!
# MassGap.FlatProfileAllApertures — the constant profile, at every even aperture

The constant function `ρ ≡ 1` and what it satisfies. Every theorem here is about that one profile,
and each is stated uniformly over the even apertures `EvenAp` rather than at a fixed extent.

## The arithmetic

`cos_half_turn_shift` — shifting the index by `m` at extent `2 * m` shifts the angle by `π`, so the
cosine changes sign. `cos_circle_sum_eq_zero` — the cosines over a full turn therefore cancel in
antipodal pairs and sum to `0`. This is where the extent being even is used: the pairing needs an
exact antipode. `cos_circLag_eq` — folding a lag through `Moment.circLag` does not change its
cosine, because a full turn is a period. `flat_cosAvg_eq_zero` assembles the three: with equal
weights `1 / (2m)` at every lag, the cosine average of the constant profile is exactly `0` at every
even aperture.

## The statements about the profile

`flat_profile_defeats_the_criterion_at_every_even_aperture` exhibits `ρ ≡ 1` as satisfying seven
conjuncts at once — strict positivity, contact maximality, antitonicity, the Cauchy–Schwarz
inequality `ρ j ^ 2 ≤ ρ 0 * ρ (2 * j)`, the slab quadratic `2 * ρ j ^ 2 ≤ ρ k ^ 2 + ρ 0 * ρ k`, a
positive normalisation, and a cosine average strictly below `3 ^ (-1/4)`. The first five hold with
equality. `flat_profile_margin_is_aperture_independent` records that the shortfall is the whole of
`3 ^ (-1/4)` at every aperture, since the average is `0`.

`flat_profile_hankel_psd` is the Hankel form evaluated on the constant profile: `0 ≤ ∑ᵢⱼ cᵢcⱼ`, which
is a square. `flatSpectralForm` and `flat_profile_is_spectral` give `ρ ≡ 1` a
`Spectral.PeriodicSpectralForm` with a single mode at `λ = 1` and weight `1/2`.

## Scope

Reflection symmetry is not a conjunct of the main theorem: the profile is read through
`Moment.circLag`, and `circLag d = circLag (n - d)` holds by that definition, so there is nothing to
state. The quantified conjuncts are stated at all pairs of lags, whereas `SlabQuadratic` states its
quadratic at one pair.

The constant profile is not a Wilson correlation at any coupling:
`ConfinesZero.cosAvgEven_at_zero` gives cosine average exactly `1` for the Wilson profile at zero
coupling. Nothing here is a statement about `wilsonCorrAt`, and no theorem below takes a coupling as
an argument.
-/

namespace MassGap.FlatProfileAllApertures

open MassGap MassGap.EvenAperture MassGap.ApertureRoute MassGap.ConfinesZero

/-! ## 1. The cosines of a full turn cancel -/

/-- Shifting the index by `m` at extent `2 * m` negates the cosine:
`cos (2π (m + i) / (2m)) = -cos (2π i / (2m))`, for every natural `i`.

The shift moves the angle by exactly `π`. `i` is unrestricted — it may exceed the extent, since the
identity is about the real-valued cosine and not about a residue.

DERIVED: `2 * m` is the extent, `m` being half of it; `2 * Real.pi` is one turn of the circle. `0` is
the strict lower bound in `hm : 0 < m`, which the division needs. -/
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

/-- The cosines over a full turn at extent `2 * m` sum to `0`:
`∑_{d < 2m} cos (2π d / (2m)) = 0`, for every `m > 0`.

The range splits at the midpoint and `cos_half_turn_shift` negates the upper half term by term. The
extent is `2 * m` by construction, so the statement is about even extents only — an odd extent has no
exact antipode and this pairing does not close.

DERIVED: `2 * m` is the extent and the summation range; `2 * Real.pi` is one turn. `0` is the strict
lower bound in `hm : 0 < m` and the value of the sum. -/
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

/-- Folding a lag through the circle distance leaves its cosine unchanged:
`cos (2π · circLag d / (N + 1)) = cos (2π · d / (N + 1))` for every `d : Fin (N + 1)`.

`Moment.circLag d` is the smaller of `d` and `N + 1 - d`, and replacing one by the other reflects the
angle through a full turn. `Moment.cos_theta_circ` states the same arithmetic attached to a `Read`;
this version takes a bare index, so it applies wherever a lag is in hand.

DERIVED: `1` is the offset in the aperture size `N + 1`, the number of lags on the circle. `2` is the
`2 * Real.pi` of one turn. -/
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

/-- The equal-weight cosine average over an even aperture is `0`.

The weights are `1 / (∑ 1) = 1 / (2m)` at every lag, so the sum factors as the full-turn cosine sum
times that constant, and `cos_circLag_eq` followed by `cos_circle_sum_eq_zero` makes the sum vanish.

Scope: the aperture is an `EvenAp`, whose membership condition supplies the `m` with extent `2 * m`;
the statement does not hold at odd extent. The profile does not appear as a variable — the weights
are the constant ones, which is what `ρ ≡ 1` gives.

DERIVED: `1` is the constant numerator of each weight and the offset in the aperture size `a.1 + 1`.
`2` is the `2 * Real.pi` of one turn. `0` is the value of the average. -/
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

/-- At every even aperture there is a profile `ρ : ℕ → ℝ` satisfying seven conjuncts at once:
`0 < ρ j`; `ρ j ≤ ρ 0`; `ρ k ≤ ρ j` whenever `j ≤ k`; `ρ j ^ 2 ≤ ρ 0 * ρ (2 * j)`;
`2 * ρ j ^ 2 ≤ ρ k ^ 2 + ρ 0 * ρ k`; a strictly positive normalisation
`0 < ∑ d, ρ (circLag d)`; and a cosine average strictly below `3 ^ (-1/4)`.

The witness supplied is the constant `fun _ => 1`. The first five conjuncts then hold with equality,
and the last is `flat_cosAvg_eq_zero` together with positivity of `3 ^ (-1/4)`.

Scope. The fourth and fifth conjuncts are quantified over all lags `j` and all pairs `j, k`, which is
more than `SlabQuadratic` states — that module fixes one pair. Reflection symmetry is not a conjunct:
the profile is read through `Moment.circLag`, so `circLag d = circLag (n - d)` holds by definition and
there is nothing to assert. No coupling appears anywhere in the statement, and `ρ` is an arbitrary
function on `ℕ`, not a Wilson correlation.

DERIVED: `0` is the contact lag `ρ 0` and the strict lower bound in the positivity conjuncts. `1` is
the offset in the aperture size `a.1 + 1`. `2` is the lag doubling in `ρ (2 * j)`, the exponent in
`ρ j ^ 2`, the coefficient in the slab quadratic, and the `2 * Real.pi` of one turn. `3` and `4` are
the base and the root in `3 ^ (-(1 : ℝ) / 4)`, the constant `ApertureRoute` carries. -/
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

/-- At every even aperture, `3 ^ (-1/4)` minus the equal-weight cosine average equals `3 ^ (-1/4)`.

Immediate from `flat_cosAvg_eq_zero`: subtracting `0` changes nothing. The content is that the
difference does not depend on the aperture, so it neither shrinks nor grows with the extent.

Scope: the average here is the equal-weight one, written out rather than taken from a profile
variable, and the aperture must be an `EvenAp`.

DERIVED: `3` and `4` are the base and root of the constant `3 ^ (-(1 : ℝ) / 4)`. `1` is the numerator
of each weight, the offset in `a.1 + 1`, and the numerator of the exponent. `2` is the `2 * Real.pi`
of one turn. -/
theorem flat_profile_margin_is_aperture_independent (a : EvenAp) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4)
      - ∑ d : Fin (a.1 + 1),
          ((1 : ℝ) / (∑ _d' : Fin (a.1 + 1), (1 : ℝ)))
            * Real.cos (2 * Real.pi * (MassGap.Moment.circLag d : ℝ) / ((a.1 : ℝ) + 1))
        = (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
  rw [flat_cosAvg_eq_zero a]
  ring

#print axioms flat_profile_margin_is_aperture_independent

/-! ## The Hankel form on the constant profile -/

/-- `0 ≤ ∑ i, ∑ j, c i * c j * 1` for any real coefficient family `c` on any `Fintype`.

This is the Hankel form `∑ᵢⱼ cᵢ cⱼ ρ (eᵢ + eⱼ)` with `ρ ≡ 1` substituted, so the profile value is the
literal `1` and the sum collapses to `(∑ c) ^ 2`.

Scope. The statement carries no profile, no extent and no level family: the levels `eᵢ` have been
substituted away along with `ρ`, so `0 ≤ ∑ᵢⱼ cᵢcⱼ` is what is asserted and nothing in the statement
refers to `Hankel.corrClay_hankel_psd` or to a Wilson correlation. The index type is arbitrary and
may be empty, in which case both sides are `0`.

DERIVED: `1` is the constant profile's value, standing in the position the Hankel form reads `ρ` at.
`0` is the lower bound. Neither is a level index. -/
theorem flat_profile_hankel_psd {ι : Type*} [Fintype ι] (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * (1 : ℝ) := by
  have h : ∑ i, ∑ j, c i * c j * (1 : ℝ) = (∑ i, c i) * (∑ j, c j) := by
    simp only [mul_one]
    rw [Finset.sum_mul_sum]
  rw [h]
  exact mul_self_nonneg _

#print axioms flat_profile_hankel_psd

/-! ## A periodic spectral form for the constant profile -/

/-- A `Spectral.PeriodicSpectralForm n (fun _ => 1)` at every `n`: one mode, indexed by `Unit`, with
decay factor `lam = 1` and weight `w = 1 / 2`.

The representation clause holds because `w * (lam ^ d + lam ^ (n - d)) = (1/2) * (1 + 1) = 1` at every
lag, and `hlam1 : lam ≤ 1` holds with equality.

Scope: `lam = 1` sits at the top of the range `PeriodicSpectralForm` permits, so this form exhibits no
decay. The structure imposes no strict bound `lam < 1`; that is what a separate `SpectralBound.SpectralAt`
would add.

DERIVED: `1` is the constant profile's value, and it is the only numeral in the statement — the mode's
decay factor and the weight `1 / 2` are fields of the term, not part of the type. -/
noncomputable def flatSpectralForm (n : ℕ) :
    MassGap.Spectral.PeriodicSpectralForm n (fun _ => (1 : ℝ)) where
  Idx := Unit
  w := fun _ => (1 : ℝ) / 2
  lam := fun _ => (1 : ℝ)
  hw := fun _ => by norm_num
  hlam0 := fun _ => by norm_num
  hlam1 := fun _ => le_rfl
  hrep := fun d => by simp only [one_pow, Finset.sum_const, Finset.card_univ]; norm_num

#print axioms flatSpectralForm

/-- `Nonempty (Spectral.PeriodicSpectralForm n (fun _ => 1))` at every `n`, witnessed by
`flatSpectralForm`. This is the shape `Complete.WilsonSpectral` is stated in, with the constant
profile in place of `wilsonCorrAt`.

DERIVED: `1` is the constant profile's value, and is the only numeral in the statement. -/
theorem flat_profile_is_spectral (n : ℕ) :
    Nonempty (MassGap.Spectral.PeriodicSpectralForm n (fun _ => (1 : ℝ))) :=
  ⟨flatSpectralForm n⟩

#print axioms flat_profile_is_spectral

end MassGap.FlatProfileAllApertures
