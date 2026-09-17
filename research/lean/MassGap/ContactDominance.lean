import Mathlib
import MassGap.Complete
import MassGap.ZeroMode
import MassGap.Substrate
import MassGap.WilsonModel

/-!
# Contact dominance: the substrate hypothesis as a condition on the far share

`WilsonModel.existence_and_gap_of_substrate` consumes

    h : ∃ B : ℝ, ∀ N β, d2At N β ≤ B

with `d2At N β = ∑ d, (readYMAt N β).p d * (Moment.circLag d : ℝ) ^ 2`. This file rewrites that
hypothesis as an exact statement about ONE scalar profile — the share of the read's weight beyond a
cut — and reads off the threshold that profile must clear.

## The far share and the layer cake

`farShare R m = ∑_{d : circLag d > m} R.p d` is the probability the read puts at circle lag strictly
beyond `m`. Because `k² = ∑_{m<k} (2m+1)`, the circular second moment is EXACTLY the `(2m+1)`-weighted
sum of that profile:

    ∑_d p d · circLag(d)²  =  ∑_{m < N+1} (2m+1) · farShare R m        (`circ_moment_eq_layer`)

No inequality is used, so nothing is given away: the substrate hypothesis and a uniform bound on this
weighted sum are the same statement.

## What the threshold is

From the identity, a uniform envelope `farShare ≤ a m` with `∑ (2m+1)·a m` convergent bounds the
moment by that sum (`circ_moment_le_of_envelope`), and the bound is the sum itself — no constant is
introduced. Convergence of `∑ (2m+1)·a m` is the whole condition, and since the layer cake is an IDENTITY the
condition is not merely sufficient — it is the hypothesis restated. A power envelope `a m = C(m+1)^{-s}`
meets it exactly when `s > 2`. `substrate_of_cubic_share` runs it at `s = 3`;
`square_envelope_not_summable` proves the weighted total diverges at `s = 2`; and
`square_share_is_not_enough` shows `s = 2` is not merely out of reach but FALSE — `squareRead` is a
family of reads whose far share stays under `(4/3)(m+1)^{-2}` at every aperture and whose moments
exceed every `B`. The threshold exponent `2` is DERIVED: `(2m+1)` is `(m+1)² − m²`, the second
moment's own weight, and a square share profile has weighted total `∑ (2m+1)(m+1)^{-2}`, which is the
harmonic series.

Two cruder facts bracket the identity and are stated separately because they are what a numerical
certificate can check at a single aperture: a cut bound
`moment ≤ m² + (N+1)²/4 · farShare m` (`circ_moment_le_cut`) and its Chebyshev converse
`(m+1)² · farShare m ≤ moment` (`farShare_le_of_circ_moment`).

Only the TAIL of the profile is constrained. `circ_moment_le_of_tail_envelope` assumes the envelope
from a cut `m₀` upward and nothing below it: `farShare ≤ 1` caps the near block by `m₀²` on its own.
So an envelope is always a statement about large lags, and the cut may be chosen after the fact.

## The two quantifiers are not of equal weight

`∀ N` and `∀ β` split the hypothesis into an APERTURE half — `∃ B, ∀ N, d2At N β ≤ B` at one
coupling, with `B` free to depend on `β` — and the COUPLING half, that those `B` are bounded over
`β`. The first is implied by the hypothesis (`aperture_uniform_of_substrate`) and is discharged by a
per-`β` envelope (`aperture_uniform_of_share_envelope`), so it asks strictly less.
`aperture_uniformity_does_not_give_coupling_uniformity` shows the gap is real: `sepRead` is a family
of reads satisfying every clause `wilson_reflection_positive_at` asserts whose moments are bounded in
the aperture at each coupling and unbounded over couplings. So no argument controlling the aperture
one coupling at a time can reach the hypothesis. It is a statement about `Moment.Read` families, so
it shows the implication is not formal — it does not say the aperture half is easy, and at a general
fixed `β` that half still needs a clustering estimate the tree has only near `β = 0`.

## The hypothesis is not slack

`envelope_load_bearing` exhibits a family of reads meeting every clause
`wilson_reflection_positive_at` asserts whose far share is identically `1` below the antipode: the
only envelope it admits is `a ≡ 1`, `∑ (2m+1)·1` diverges, and the moments are unbounded. Drop
summability and the conclusion fails. `square_share_is_not_enough` says the same at the threshold
itself, where the envelope is as small as it can be while still failing. `envelope_nonvacuous`
exhibits a read the criterion accepts with bound `0`.

## Why the aperture argument cannot be run forwards

`Moment.Read.substrate_lt_of_tension_lt_floor` turns a tension below the entropy floor into
`substrateRatio < (1 − 3^{−1/4})/8`. Re-entering `Complete.confinement_at_of_substrate_sharp` needs
`substrateRatio < substrateThreshold`. `substrateThreshold_lt_ceiling` proves the second number is
strictly the smaller, so the forward run produces a bound weaker than the one it would have to supply
and the loop does not close. `aperture_constants_ordered` places all three constants of the aperture
argument in order; the outer two differ by exactly `π²/4`, since
`(1 − 3^{−1/4})/8 = (π²/4)·(2(1 − 3^{−1/4})/(2π)²)`, which is the factor
`Real.cos_le_one_sub_mul_cos_sq` gives away against `Sharp.cos_ge_tangent`. So the gap is a property
of the two cosine inequalities, not of this development's numbers. Neither theorem bounds `d2At`
itself in any case: both speak of the ratio, which carries the aperture divided out.
-/

namespace MassGap.ContactDominance

open MassGap.Moment

/-! ### The far share -/

/-- The lags whose circle distance exceeds a cut `m`.

DERIVED: `1` is `Fin (N+1)`'s own offset -- the lag index runs over the whole period. The cut `m` is a parameter, not a constant. -/
def farSet (N m : ℕ) : Finset (Fin (N + 1)) :=
  Finset.univ.filter (fun d => m < Moment.circLag d)

/-- **The far share**: the probability a read places strictly beyond circle lag `m`.

DERIVED: nothing is chosen. `m` is the cut, quantified over; the set is `circLag > m` because the
moment weights by `circLag`. -/
noncomputable def farShare {N : ℕ} (R : Moment.Read N) (m : ℕ) : ℝ :=
  ∑ d ∈ farSet N m, R.p d

theorem farShare_nonneg {N : ℕ} (R : Moment.Read N) (m : ℕ) : 0 ≤ farShare R m :=
  Finset.sum_nonneg (fun d _ => R.p_nonneg d)

theorem farShare_le_one {N : ℕ} (R : Moment.Read N) (m : ℕ) : farShare R m ≤ 1 := by
  have h : ∑ d ∈ farSet N m, R.p d ≤ ∑ d ∈ Finset.univ, R.p d :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun d _ _ => R.p_nonneg d)
  rw [R.p_sum] at h
  exact h

/-! ### The two crude bounds: a cut, and its Chebyshev converse -/

/-- **The cut bound.** Splitting the lag range at `m`, the near half contributes at most `m²` and the
far half at most the squared half-period times its share.

DERIVED: `m²` is the largest squared lag below the cut and `(N+1)²/4` the largest on the circle
(`Substrate.circLag_le_half`). Nothing is chosen. -/
theorem circ_moment_le_cut {N : ℕ} (R : Moment.Read N) (m : ℕ) :
    ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2
      ≤ (m : ℝ) ^ 2 + ((N : ℝ) + 1) ^ 2 / 4 * farShare R m := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun d : Fin (N + 1) => m < Moment.circLag d)
    (fun d => R.p d * (Moment.circLag d : ℝ) ^ 2)
  -- far half: every squared lag is at most the squared half-period
  have hfar : ∑ d ∈ Finset.univ.filter (fun d : Fin (N + 1) => m < Moment.circLag d),
      R.p d * (Moment.circLag d : ℝ) ^ 2
      ≤ ((N : ℝ) + 1) ^ 2 / 4 * farShare R m := by
    have hterm : ∀ d ∈ Finset.univ.filter (fun d : Fin (N + 1) => m < Moment.circLag d),
        R.p d * (Moment.circLag d : ℝ) ^ 2 ≤ ((N : ℝ) + 1) ^ 2 / 4 * R.p d := by
      intro d _
      have h0 : (0 : ℝ) ≤ (Moment.circLag d : ℝ) := Nat.cast_nonneg _
      have h1 := MassGap.Substrate.circLag_le_half d
      have hN : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
      have hsq : (Moment.circLag d : ℝ) ^ 2 ≤ ((N : ℝ) + 1) ^ 2 / 4 := by nlinarith [h0, h1, hN]
      calc R.p d * (Moment.circLag d : ℝ) ^ 2
          ≤ R.p d * (((N : ℝ) + 1) ^ 2 / 4) := mul_le_mul_of_nonneg_left hsq (R.p_nonneg d)
        _ = ((N : ℝ) + 1) ^ 2 / 4 * R.p d := by ring
    calc ∑ d ∈ Finset.univ.filter (fun d : Fin (N + 1) => m < Moment.circLag d),
          R.p d * (Moment.circLag d : ℝ) ^ 2
        ≤ ∑ d ∈ Finset.univ.filter (fun d : Fin (N + 1) => m < Moment.circLag d),
            ((N : ℝ) + 1) ^ 2 / 4 * R.p d := Finset.sum_le_sum hterm
      _ = ((N : ℝ) + 1) ^ 2 / 4 * farShare R m := by
            rw [← Finset.mul_sum]; rfl
  -- near half: every squared lag is at most `m²`, and the shares sum to at most one
  have hnear : ∑ d ∈ Finset.univ.filter (fun d : Fin (N + 1) => ¬ m < Moment.circLag d),
      R.p d * (Moment.circLag d : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by
    have hterm : ∀ d ∈ Finset.univ.filter (fun d : Fin (N + 1) => ¬ m < Moment.circLag d),
        R.p d * (Moment.circLag d : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 * R.p d := by
      intro d hd
      simp only [Finset.mem_filter, not_lt] at hd
      have hc : (Moment.circLag d : ℝ) ≤ (m : ℝ) := by exact_mod_cast hd.2
      have h0 : (0 : ℝ) ≤ (Moment.circLag d : ℝ) := Nat.cast_nonneg _
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hsq : (Moment.circLag d : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by nlinarith [h0, hc, hm0]
      calc R.p d * (Moment.circLag d : ℝ) ^ 2
          ≤ R.p d * (m : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsq (R.p_nonneg d)
        _ = (m : ℝ) ^ 2 * R.p d := by ring
    have hshare : ∑ d ∈ Finset.univ.filter (fun d : Fin (N + 1) => ¬ m < Moment.circLag d),
        R.p d ≤ 1 := by
      have h : ∑ d ∈ Finset.univ.filter (fun d : Fin (N + 1) => ¬ m < Moment.circLag d), R.p d
          ≤ ∑ d ∈ Finset.univ, R.p d :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun d _ _ => R.p_nonneg d)
      rw [R.p_sum] at h
      exact h
    calc ∑ d ∈ Finset.univ.filter (fun d : Fin (N + 1) => ¬ m < Moment.circLag d),
          R.p d * (Moment.circLag d : ℝ) ^ 2
        ≤ ∑ d ∈ Finset.univ.filter (fun d : Fin (N + 1) => ¬ m < Moment.circLag d),
            (m : ℝ) ^ 2 * R.p d := Finset.sum_le_sum hterm
      _ = (m : ℝ) ^ 2 * ∑ d ∈ Finset.univ.filter
            (fun d : Fin (N + 1) => ¬ m < Moment.circLag d), R.p d := by rw [← Finset.mul_sum]
      _ ≤ (m : ℝ) ^ 2 * 1 := by
            refine mul_le_mul_of_nonneg_left hshare (by positivity)
      _ = (m : ℝ) ^ 2 := by ring
  linarith [hsplit.symm.le, hsplit.le, hfar, hnear]

#print axioms circ_moment_le_cut

/-- **Chebyshev, the other way.** Beyond the cut every squared lag is at least `(m+1)²`, so the far
share is capped by the moment.

DERIVED: `(m+1)²` is the smallest squared lag strictly beyond `m`. -/
theorem farShare_le_of_circ_moment {N : ℕ} (R : Moment.Read N) (m : ℕ) :
    ((m : ℝ) + 1) ^ 2 * farShare R m ≤ ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2 := by
  classical
  have hterm : ∀ d ∈ farSet N m,
      ((m : ℝ) + 1) ^ 2 * R.p d ≤ R.p d * (Moment.circLag d : ℝ) ^ 2 := by
    intro d hd
    simp only [farSet, Finset.mem_filter] at hd
    have hc : (m : ℝ) + 1 ≤ (Moment.circLag d : ℝ) := by
      have : (m + 1 : ℕ) ≤ Moment.circLag d := hd.2
      exact_mod_cast this
    have h0 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    have hsq : ((m : ℝ) + 1) ^ 2 ≤ (Moment.circLag d : ℝ) ^ 2 := by nlinarith [hc, h0]
    calc ((m : ℝ) + 1) ^ 2 * R.p d = R.p d * ((m : ℝ) + 1) ^ 2 := by ring
      _ ≤ R.p d * (Moment.circLag d : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (R.p_nonneg d)
  calc ((m : ℝ) + 1) ^ 2 * farShare R m
      = ∑ d ∈ farSet N m, ((m : ℝ) + 1) ^ 2 * R.p d := by rw [farShare, Finset.mul_sum]
    _ ≤ ∑ d ∈ farSet N m, R.p d * (Moment.circLag d : ℝ) ^ 2 := Finset.sum_le_sum hterm
    _ ≤ ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun d _ _ => mul_nonneg (R.p_nonneg d) (sq_nonneg _))

#print axioms farShare_le_of_circ_moment

/-! ### The layer cake: the moment IS the weighted far-share profile -/

/-- `∑_{m<k} (2m+1) = k²` — the discrete derivative of the square.

DERIVED: `2m+1` is `(m+1)² − m²`. Nothing is chosen. -/
theorem sum_range_odd (k : ℕ) : ∑ m ∈ Finset.range k, (2 * (m : ℝ) + 1) = (k : ℝ) ^ 2 := by
  induction k with
  | zero => simp
  | succ j ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- Below a ceiling the `<` filter of a range IS the shorter range. -/
theorem filter_lt_range {k n : ℕ} (hk : k ≤ n) :
    (Finset.range n).filter (fun m => m < k) = Finset.range k := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨lt_of_lt_of_le h hk, h⟩

/-- The circle lag never reaches the lag arity. -/
theorem circLag_lt_succ {N : ℕ} (d : Fin (N + 1)) : Moment.circLag d < N + 1 := by
  have h := d.isLt
  unfold Moment.circLag
  omega

/-- **THE LAYER CAKE — the substrate moment is exactly the weighted far-share profile.**

    ∑_d p(d)·circLag(d)²  =  ∑_{m < N+1} (2m+1)·farShare R m

An identity, not a bound: the two sides are the same number at every aperture and for every read. So
the substrate hypothesis is precisely a uniform bound on the right-hand sum, and the whole content of
`∃ B, ∀ N β, d2At N β ≤ B` is that the far-share profile stays summable against the weight `2m+1`.

DERIVED: `2m+1` is `(m+1)² − m²` (`sum_range_odd`); `N+1` is the lag arity. -/
theorem circ_moment_eq_layer {N : ℕ} (R : Moment.Read N) :
    ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2
      = ∑ m ∈ Finset.range (N + 1), (2 * (m : ℝ) + 1) * farShare R m := by
  classical
  have hpt : ∀ d : Fin (N + 1), R.p d * (Moment.circLag d : ℝ) ^ 2
      = ∑ m ∈ Finset.range (N + 1),
          (if m < Moment.circLag d then (2 * (m : ℝ) + 1) * R.p d else 0) := by
    intro d
    have h : ∑ m ∈ Finset.range (N + 1),
        (if m < Moment.circLag d then (2 * (m : ℝ) + 1) * R.p d else 0)
        = ∑ m ∈ (Finset.range (N + 1)).filter (fun m => m < Moment.circLag d),
            (2 * (m : ℝ) + 1) * R.p d := (Finset.sum_filter _ _).symm
    rw [h, filter_lt_range (le_of_lt (circLag_lt_succ d)), ← Finset.sum_mul, sum_range_odd]
    ring
  rw [Finset.sum_congr rfl (fun d _ => hpt d), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [farShare, farSet, Finset.mul_sum, Finset.sum_filter]

#print axioms circ_moment_eq_layer

/-! ### The criterion -/

/-- **A summable far-share envelope bounds the moment, and the bound IS the sum.**

No constant is introduced anywhere: the bound is `∑' m, (2m+1)·a m`, the envelope's own weighted
total. The aperture does not appear, which is what makes the conclusion uniform in it. -/
theorem circ_moment_le_of_envelope {N : ℕ} (R : Moment.Read N) (a : ℕ → ℝ)
    (ha0 : ∀ m, 0 ≤ a m) (ha : ∀ m, farShare R m ≤ a m)
    (hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * a m)) :
    ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2 ≤ ∑' m : ℕ, (2 * (m : ℝ) + 1) * a m := by
  rw [circ_moment_eq_layer]
  have h1 : ∑ m ∈ Finset.range (N + 1), (2 * (m : ℝ) + 1) * farShare R m
      ≤ ∑ m ∈ Finset.range (N + 1), (2 * (m : ℝ) + 1) * a m :=
    Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left (ha m) (by positivity))
  have h2 : ∑ m ∈ Finset.range (N + 1), (2 * (m : ℝ) + 1) * a m
      ≤ ∑' m : ℕ, (2 * (m : ℝ) + 1) * a m :=
    hs.sum_le_tsum _ (fun m _ => mul_nonneg (by positivity) (ha0 m))
  linarith

#print axioms circ_moment_le_of_envelope

/-- **THE SUBSTRATE HYPOTHESIS FROM A UNIFORM FAR-SHARE ENVELOPE.**

One profile `a`, good at every aperture and every coupling, whose `(2m+1)`-weighted total converges,
discharges `∃ B, ∀ N β, d2At N β ≤ B`. `B` is the total; nothing is fitted.

By `circ_moment_eq_layer` this is not a sufficient condition that gives something away — the moment
IS the weighted profile — so the only slack is between `farShare` and its envelope. -/
theorem substrate_of_share_envelope (a : ℕ → ℝ)
    (ha0 : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * a m))
    (ha : ∀ (N : ℕ) (β : ℝ) (m : ℕ), farShare (MassGap.readYMAt N β) m ≤ a m) :
    ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B :=
  ⟨∑' m : ℕ, (2 * (m : ℝ) + 1) * a m, fun N β =>
    circ_moment_le_of_envelope (MassGap.readYMAt N β) a ha0 (ha N β) hs⟩

#print axioms substrate_of_share_envelope

/-- **Confinement at every large enough aperture, from the far-share envelope.** The composition with
`Complete.confinement_of_bounded_substrate`. -/
theorem confinement_of_share_envelope (a : ℕ → ℝ)
    (ha0 : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * a m))
    (ha : ∀ (N : ℕ) (β : ℝ) (m : ℕ), farShare (MassGap.readYMAt N β) m ≤ a m) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, MassGap.μYMAt N β < MassGap.κ₀YM :=
  MassGap.confinement_of_bounded_substrate (substrate_of_share_envelope a ha0 hs ha)

#print axioms confinement_of_share_envelope


/-- **THE WHOLE STATEMENT, FROM A FAR-SHARE ENVELOPE.**

`WilsonModel.existence_and_gap_of_substrate` takes exactly `∃ B, ∀ N β, d2At N β ≤ B`, so
`substrate_of_share_envelope` discharges it and the mass gap, non-triviality, `SO(4)` invariance and
the continuum measure all follow from one scalar profile: a uniform bound on the share of the
connected plaquette correlation beyond each cut, summable against `2m+1`.

Stated as the composition so that the far-share condition is visibly the LAST hypothesis and not a
reformulation alongside one. -/
theorem yang_mills_of_share_envelope (a : ℕ → ℝ)
    (ha0 : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * a m))
    (ha : ∀ (N : ℕ) (β : ℝ) (m : ℕ), farShare (MassGap.readYMAt N β) m ≤ a m) :
    ∃ h : (∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B),
      ((∀ β, Filter.Tendsto (fun τ => ‖∑ k ∈ (MassGap.WilsonModel.wilsonOfSubstrate h).model.gap.s β,
            (MassGap.WilsonModel.wilsonOfSubstrate h).model.gap.P β k
              * ((MassGap.WilsonModel.wilsonOfSubstrate h).model.gap.m β k) ^ τ‖)
          Filter.atTop (nhds 0)) ∧
        (∀ β, (MassGap.WilsonModel.wilsonOfSubstrate h).model.gap.μ β
            - (MassGap.WilsonModel.wilsonOfSubstrate h).model.gap.κ < 0) ∧
        (∀ d d', (MassGap.WilsonModel.wilsonOfSubstrate h).model.gap.R d
            = (MassGap.WilsonModel.wilsonOfSubstrate h).model.gap.R d')) := by
  refine ⟨substrate_of_share_envelope a ha0 hs ha, ?_⟩
  exact (MassGap.WilsonModel.existence_and_gap_of_substrate
    (substrate_of_share_envelope a ha0 hs ha)).1

#print axioms yang_mills_of_share_envelope

/-! ### The threshold exponent is two -/

/-- `∑ 1/(m+1)²` converges. -/
theorem summable_inv_succ_sq : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := by
    simpa using Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
  have h' := (summable_nat_add_iff 1).mpr h
  refine h'.congr (fun m => ?_)
  push_cast
  ring

/-- **A cubic far-share envelope discharges the substrate hypothesis.**

`farShare ≤ C/(m+1)³` uniformly in aperture and coupling gives `∃ B, ∀ N β, d2At N β ≤ B`. The
exponent `3` is not chosen for room: it is the smallest INTEGER above the threshold `2` that
`square_envelope_not_summable` shows cannot be reached. -/
theorem substrate_of_cubic_share {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ (N : ℕ) (β : ℝ) (m : ℕ),
      farShare (MassGap.readYMAt N β) m ≤ C / ((m : ℝ) + 1) ^ 3) :
    ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B := by
  have hnn : ∀ m : ℕ, (0 : ℝ) ≤ C / ((m : ℝ) + 1) ^ 3 :=
    fun m => div_nonneg hC (by positivity)
  refine substrate_of_share_envelope (fun m => C / ((m : ℝ) + 1) ^ 3) hnn ?_ ha
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (by positivity) (hnn m)) (fun m => ?_)
    ((summable_inv_succ_sq).mul_left (2 * C))
  have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hnum : 2 * (m : ℝ) + 1 ≤ 2 * ((m : ℝ) + 1) := by linarith
  have hrw : 2 * C * (1 / ((m : ℝ) + 1) ^ 2) = (2 * ((m : ℝ) + 1)) * (C / ((m : ℝ) + 1) ^ 3) := by
    field_simp
    try ring
  rw [hrw]
  exact mul_le_mul_of_nonneg_right hnum (by positivity)

#print axioms substrate_of_cubic_share

/-- **The threshold is exactly two: a square envelope is not summable against `2m+1`.**

`(2m+1)/(m+1)² ≥ 1/(m+1)`, and the harmonic series diverges. So no envelope falling off like
`(m+1)^{-2}` can be fed to `circ_moment_le_of_envelope`, and the exponent `3` above cannot be
lowered to `2`. -/
theorem square_envelope_not_summable {C : ℝ} (hC : 0 < C) :
    ¬ Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * (C / ((m : ℝ) + 1) ^ 2)) := by
  intro hs
  have hharm : ¬ Summable (fun m : ℕ => C * (1 / ((m : ℝ) + 1))) := by
    intro h
    have h' : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1)) := by
      have := h.mul_left (1 / C)
      refine this.congr (fun m => ?_)
      field_simp
    have h2 : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
      refine (summable_nat_add_iff 1).mp (h'.congr (fun m => ?_))
      push_cast
      ring
    exact (Real.not_summable_one_div_natCast) h2
  refine hharm (Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hs)
  have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hnum : (m : ℝ) + 1 ≤ 2 * (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hrw : C * (1 / ((m : ℝ) + 1)) = ((m : ℝ) + 1) * (C / ((m : ℝ) + 1) ^ 2) := by
    field_simp
    try ring
  rw [hrw]
  exact mul_le_mul_of_nonneg_right hnum (by positivity)

#print axioms square_envelope_not_summable

/-! ### The companion threshold, on the correlation rather than on the share

`Moment.circ_moment_le_of_geometric` consumes `p d ≤ C·r^{circLag d}` with `r < 1`, which is a RATE.
The same argument runs against any envelope in the circle lag whose squared-lag moment converges, and
a power envelope has no rate in it — which matters because asymptotic freedom denies a decay rate
uniform in the coupling while leaving a power untouched. The threshold exponent here is `3`, one
above the share's `2`, because the share has already absorbed one summation. -/

/-- **A summable squared-lag envelope on the read's own weights bounds the moment.**

`p d ≤ b (circLag d)` with `∑ k²·b k` convergent gives `moment ≤ 2·∑' k²·b k`, uniformly in the
aperture. The `2` is the fibre multiplicity of the circle lag (`Moment.sum_circLag_le_two_mul`): each
distance is attained by at most two lags. Nothing else enters. -/
theorem circ_moment_le_of_weight_envelope {N : ℕ} (R : Moment.Read N) (b : ℕ → ℝ)
    (hb0 : ∀ k, 0 ≤ b k)
    (hdecay : ∀ d, R.p d ≤ b (Moment.circLag d))
    (hs : Summable (fun k : ℕ => (k : ℝ) ^ 2 * b k)) :
    ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2 ≤ 2 * ∑' k : ℕ, (k : ℝ) ^ 2 * b k := by
  have hg0 : ∀ k : ℕ, (0 : ℝ) ≤ (k : ℝ) ^ 2 * b k := fun k => mul_nonneg (sq_nonneg _) (hb0 k)
  have hterm : ∀ d : Fin (N + 1), R.p d * (Moment.circLag d : ℝ) ^ 2
      ≤ (fun k : ℕ => (k : ℝ) ^ 2 * b k) (Moment.circLag d) := by
    intro d
    have := mul_le_mul_of_nonneg_right (hdecay d) (sq_nonneg ((Moment.circLag d : ℝ)))
    calc R.p d * (Moment.circLag d : ℝ) ^ 2
        ≤ b (Moment.circLag d) * (Moment.circLag d : ℝ) ^ 2 := this
      _ = (Moment.circLag d : ℝ) ^ 2 * b (Moment.circLag d) := by ring
  have hfib := Moment.sum_circLag_le_two_mul (N := N) (fun k : ℕ => (k : ℝ) ^ 2 * b k) hg0
  have hpart : ∑ k ∈ Finset.range (N + 2), (k : ℝ) ^ 2 * b k
      ≤ ∑' k : ℕ, (k : ℝ) ^ 2 * b k := hs.sum_le_tsum _ (fun k _ => hg0 k)
  calc ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2
      ≤ ∑ d : Fin (N + 1), (fun k : ℕ => (k : ℝ) ^ 2 * b k) (Moment.circLag d) :=
        Finset.sum_le_sum (fun d _ => hterm d)
    _ ≤ 2 * ∑ k ∈ Finset.range (N + 2), (k : ℝ) ^ 2 * b k := hfib
    _ ≤ 2 * ∑' k : ℕ, (k : ℝ) ^ 2 * b k := by linarith

#print axioms circ_moment_le_of_weight_envelope

/-- **THE SUBSTRATE HYPOTHESIS FROM A UNIFORM CORRELATION ENVELOPE.** One envelope `b` in the circle
lag, good at every aperture and every coupling, with `∑ k²·b k` convergent. No rate is asked for. -/
theorem substrate_of_weight_envelope (b : ℕ → ℝ)
    (hb0 : ∀ k, 0 ≤ b k)
    (hs : Summable (fun k : ℕ => (k : ℝ) ^ 2 * b k))
    (hdecay : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)),
      (MassGap.readYMAt N β).p d ≤ b (Moment.circLag d)) :
    ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B :=
  ⟨2 * ∑' k : ℕ, (k : ℝ) ^ 2 * b k, fun N β =>
    circ_moment_le_of_weight_envelope (MassGap.readYMAt N β) b hb0 (hdecay N β) hs⟩

#print axioms substrate_of_weight_envelope

/-- `∑ k²/(k+1)⁴` converges, by comparison with `∑ 1/(k+1)²`. -/
theorem summable_sq_div_succ_pow_four :
    Summable (fun k : ℕ => (k : ℝ) ^ 2 * (1 / ((k : ℝ) + 1) ^ 4)) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) summable_inv_succ_sq
  have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk : (k : ℝ) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith
  have hL : (k : ℝ) ^ 2 * (1 / ((k : ℝ) + 1) ^ 4) = (k : ℝ) ^ 2 / ((k : ℝ) + 1) ^ 4 := by ring
  rw [hL, div_le_div_iff₀ (by positivity) (by positivity)]
  have hb : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := sq_nonneg _
  nlinarith [hk, hb]

/-- **A quartic correlation envelope discharges the substrate hypothesis.**

`p d ≤ C/(circLag d + 1)⁴` uniformly in aperture and coupling is enough. The exponent `4` is the
smallest INTEGER above the threshold `3` that `circ_moment_le_of_weight_envelope` sets, and `3` is
where `∑ k²·b k` stops converging. -/
theorem substrate_of_quartic_decay {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)),
      (MassGap.readYMAt N β).p d ≤ C / ((Moment.circLag d : ℝ) + 1) ^ 4) :
    ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B := by
  refine substrate_of_weight_envelope (fun k => C / ((k : ℝ) + 1) ^ 4)
    (fun k => div_nonneg hC (by positivity)) ?_ ?_
  · refine (summable_sq_div_succ_pow_four.mul_left C).congr (fun k => ?_)
    ring
  · intro N β d
    exact hdecay N β d

#print axioms substrate_of_quartic_decay

/-! ### The same hypothesis in the unnormalised correlation

`Moment.Read.p` divides by the total mass, so the substrate hypothesis is a statement about the
correlation only through a RATIO. Stated that way it is uniform Cesàro contact dominance: the
squared-lag-weighted total of `ρ` must stay within a fixed multiple of the plain total. -/

/-- The normalised moment is the `ρ`-weighted moment over the total mass. -/
theorem circ_moment_eq_rho_ratio {N : ℕ} (R : Moment.Read N) :
    ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2
      = (∑ d, R.ρ d * (Moment.circLag d : ℝ) ^ 2) / (∑ d, R.ρ d) := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  simp only [Moment.Read.p]
  ring

/-- **THE HYPOTHESIS AS CESÀRO CONTACT DOMINANCE.**

    ∑_d p(d)·circLag(d)² ≤ B   ↔   ∑_d ρ(d)·circLag(d)² ≤ B·∑_d ρ(d)

An equivalence, so the substrate hypothesis is exactly: the squared-lag-weighted total of the
connected correlation is within a fixed multiple of its plain total, at every aperture and every
coupling. No decay, no rate, no normalisation. -/
theorem circ_moment_le_iff_rho {N : ℕ} (R : Moment.Read N) (B : ℝ) :
    (∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2 ≤ B)
      ↔ (∑ d, R.ρ d * (Moment.circLag d : ℝ) ^ 2 ≤ B * ∑ d, R.ρ d) := by
  rw [circ_moment_eq_rho_ratio, div_le_iff₀ R.hpos]

#print axioms circ_moment_le_iff_rho

/-- **THE TWO INPUTS A CORRELATION BOUND MUST SUPPLY.**

An envelope `ρ d ≤ b (circLag d)` with `∑ k²·b k` convergent, AND a strictly positive lower bound `c`
on the total mass, give `moment ≤ (2/c)·∑' k²·b k`. Both are needed and neither is implied by the
other: the envelope alone leaves the normalisation free, and the mass bound alone says nothing about
where the weight sits.

DERIVED: the `2` is the fibre multiplicity of the circle lag (`Moment.sum_circLag_le_two_mul`); `c`
is the caller's mass bound and the sum is the envelope's own. -/
theorem circ_moment_le_of_rho_envelope {N : ℕ} (R : Moment.Read N) (b : ℕ → ℝ) (c : ℝ)
    (hc : 0 < c) (hmass : c ≤ ∑ d, R.ρ d)
    (hb0 : ∀ k, 0 ≤ b k) (hrho : ∀ d, R.ρ d ≤ b (Moment.circLag d))
    (hs : Summable (fun k : ℕ => (k : ℝ) ^ 2 * b k)) :
    ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2 ≤ (2 / c) * ∑' k : ℕ, (k : ℝ) ^ 2 * b k := by
  have hg0 : ∀ k : ℕ, (0 : ℝ) ≤ (k : ℝ) ^ 2 * b k := fun k => mul_nonneg (sq_nonneg _) (hb0 k)
  have hnum : ∑ d, R.ρ d * (Moment.circLag d : ℝ) ^ 2 ≤ 2 * ∑' k : ℕ, (k : ℝ) ^ 2 * b k := by
    have hterm : ∀ d : Fin (N + 1), R.ρ d * (Moment.circLag d : ℝ) ^ 2
        ≤ (fun k : ℕ => (k : ℝ) ^ 2 * b k) (Moment.circLag d) := by
      intro d
      have h := mul_le_mul_of_nonneg_right (hrho d) (sq_nonneg ((Moment.circLag d : ℝ)))
      calc R.ρ d * (Moment.circLag d : ℝ) ^ 2
          ≤ b (Moment.circLag d) * (Moment.circLag d : ℝ) ^ 2 := h
        _ = (Moment.circLag d : ℝ) ^ 2 * b (Moment.circLag d) := by ring
    have hfib := Moment.sum_circLag_le_two_mul (N := N) (fun k : ℕ => (k : ℝ) ^ 2 * b k) hg0
    have hpart : ∑ k ∈ Finset.range (N + 2), (k : ℝ) ^ 2 * b k
        ≤ ∑' k : ℕ, (k : ℝ) ^ 2 * b k := hs.sum_le_tsum _ (fun k _ => hg0 k)
    calc ∑ d, R.ρ d * (Moment.circLag d : ℝ) ^ 2
        ≤ ∑ d : Fin (N + 1), (fun k : ℕ => (k : ℝ) ^ 2 * b k) (Moment.circLag d) :=
          Finset.sum_le_sum (fun d _ => hterm d)
      _ ≤ 2 * ∑ k ∈ Finset.range (N + 2), (k : ℝ) ^ 2 * b k := hfib
      _ ≤ 2 * ∑' k : ℕ, (k : ℝ) ^ 2 * b k := by linarith
  rw [circ_moment_eq_rho_ratio, div_le_iff₀ R.hpos]
  have hT : (0 : ℝ) ≤ ∑' k : ℕ, (k : ℝ) ^ 2 * b k := tsum_nonneg hg0
  have hfinal : 2 * (∑' k : ℕ, (k : ℝ) ^ 2 * b k)
      ≤ 2 / c * (∑' k : ℕ, (k : ℝ) ^ 2 * b k) * (∑ d, R.ρ d) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith [hT, hmass, hc]
  linarith [hnum, hfinal]

#print axioms circ_moment_le_of_rho_envelope

/-! ### Negative control: the envelope hypothesis is load-bearing, and the criterion is not vacuous -/

/-- The contact read: all weight at lag zero.

DERIVED: the `1` and `0` are the values of an indicator, and `p` normalises, so neither is a
magnitude. -/
noncomputable def contactRead (N : ℕ) : Moment.Read N where
  ρ := fun d => if d = 0 then 1 else 0
  hρ := fun d => by split <;> norm_num
  hpos := by simp

theorem contactRead_sum (N : ℕ) : ∑ d, (contactRead N).ρ d = 1 := by
  show ∑ d : Fin (N + 1), (if d = 0 then (1 : ℝ) else 0) = 1
  simp

/-- **The criterion accepts something.** The contact read's far share is zero at every cut, so the
zero envelope applies and the bound it gives is `0`. -/
theorem contactRead_farShare (N m : ℕ) : farShare (contactRead N) m = 0 := by
  classical
  refine Finset.sum_eq_zero (fun d hd => ?_)
  simp only [farSet, Finset.mem_filter] at hd
  have hne : d ≠ 0 := by
    intro h
    rw [h] at hd
    have hz : Moment.circLag (0 : Fin (N + 1)) = 0 := by
      have hv : ((0 : Fin (N + 1)) : ℕ) = 0 := rfl
      unfold Moment.circLag; rw [hv]; omega
    omega
  show (contactRead N).ρ d / (∑ d', (contactRead N).ρ d') = 0
  have : (contactRead N).ρ d = 0 := by
    show (if d = 0 then (1 : ℝ) else 0) = 0
    rw [if_neg hne]
  rw [this, zero_div]

/-- **NON-VACUITY.** A read satisfying the two clauses of `wilson_reflection_positive_at` whose far
share is bounded by a summable envelope, with moment zero. So `circ_moment_le_of_envelope` is not
an implication out of an unsatisfiable hypothesis. -/
theorem envelope_nonvacuous (N : ℕ) :
    (∀ m, farShare (contactRead N) m ≤ (fun _ : ℕ => (0 : ℝ)) m) ∧
      Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * (0 : ℝ)) ∧
      ∑ d, (contactRead N).p d * (Moment.circLag d : ℝ) ^ 2 ≤ 0 := by
  refine ⟨fun m => le_of_eq (contactRead_farShare N m), by simpa using summable_zero, ?_⟩
  have := circ_moment_le_of_envelope (contactRead N) (fun _ => (0 : ℝ))
    (fun _ => le_refl 0) (fun m => le_of_eq (contactRead_farShare N m))
    (by simpa using summable_zero)
  simpa using this

#print axioms envelope_nonvacuous

/-- The antipodal read puts everything strictly beyond every cut below the antipode. -/
theorem antipodeRead_farShare (k m : ℕ) (hm : m ≤ k) :
    farShare (MassGap.Substrate.antipodeRead k) m = 1 := by
  classical
  have hmem : MassGap.Substrate.antipode k ∈ farSet (2 * k + 1) m := by
    simp only [farSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [MassGap.Substrate.circLag_antipode k]
    omega
  have hsum := MassGap.Substrate.antipodeRead_sum k
  have hp : ∀ d, (MassGap.Substrate.antipodeRead k).p d
      = (MassGap.Substrate.antipodeRead k).ρ d := by
    intro d; simp [Moment.Read.p, hsum]
  have hzero : ∀ d ∈ farSet (2 * k + 1) m, d ≠ MassGap.Substrate.antipode k →
      (MassGap.Substrate.antipodeRead k).p d = 0 := by
    intro d _ hne
    rw [hp d]
    show (if d = MassGap.Substrate.antipode k then (1 : ℝ) else 0) = 0
    rw [if_neg hne]
  rw [farShare, Finset.sum_eq_single_of_mem _ hmem hzero, hp]
  show (if MassGap.Substrate.antipode k = MassGap.Substrate.antipode k then (1 : ℝ) else 0) = 1
  rw [if_pos rfl]

/-- **THE ENVELOPE HYPOTHESIS IS LOAD-BEARING.**

The antipodal family satisfies exactly the two clauses `wilson_reflection_positive_at` asserts, its
far share is `1` at every cut the aperture admits — so the only envelope covering the family is
`a ≡ 1`, whose `(2m+1)`-weighted total diverges — and its moments exceed every `B`. Remove
summability from `circ_moment_le_of_envelope` and the conclusion is false, not merely unproved. -/
theorem envelope_load_bearing :
    (∀ (a : ℕ → ℝ), (∀ (k m : ℕ), m ≤ k → farShare (MassGap.Substrate.antipodeRead k) m ≤ a m) →
        ∀ m, (1 : ℝ) ≤ a m) ∧
      (¬ Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * (1 : ℝ))) ∧
      (∀ B : ℝ, ∃ (N : ℕ) (R : Moment.Read N),
        B < ∑ d, R.p d * ((Moment.circLag d : ℕ) : ℝ) ^ 2) := by
  refine ⟨?_, ?_, MassGap.Substrate.rp_alone_leaves_moment_unbounded⟩
  · intro a ha m
    have := ha m m (le_refl m)
    rwa [antipodeRead_farShare m m (le_refl m)] at this
  · intro hs
    have htend := hs.tendsto_atTop_zero
    have hev : ∀ᶠ m : ℕ in Filter.atTop, (2 * (m : ℝ) + 1) * (1 : ℝ) < 1 :=
      htend.eventually_lt_const (by norm_num)
    obtain ⟨m, hm⟩ := hev.exists
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith

#print axioms envelope_load_bearing

/-! ### Only the tail is constrained

The near lags need no hypothesis at all: `farShare ≤ 1` caps their contribution to the layer cake by
`m₀²`, whatever the correlation does there. So an envelope is only ever a statement about the profile
beyond a fixed cut, and the cut may be chosen after the fact. -/

/-- **A TAIL envelope is enough.** Nothing is assumed below the cut `m₀`; the layer cake's near block
is bounded by `∑_{m<m₀}(2m+1) = m₀²` from `farShare ≤ 1` alone.

DERIVED: `m₀²` is `sum_range_odd` at `m₀` — the near block's worst case, not a chosen allowance. -/
theorem circ_moment_le_of_tail_envelope {N : ℕ} (R : Moment.Read N) (m₀ : ℕ) (a : ℕ → ℝ)
    (ha0 : ∀ m, 0 ≤ a m) (ha : ∀ m, m₀ ≤ m → farShare R m ≤ a m)
    (hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * a m)) :
    ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2
      ≤ (m₀ : ℝ) ^ 2 + ∑' m : ℕ, (2 * (m : ℝ) + 1) * a m := by
  classical
  rw [circ_moment_eq_layer]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (N + 1))
    (fun m => m < m₀) (fun m => (2 * (m : ℝ) + 1) * farShare R m)
  have hnear : ∑ m ∈ (Finset.range (N + 1)).filter (fun m => m < m₀),
      (2 * (m : ℝ) + 1) * farShare R m ≤ (m₀ : ℝ) ^ 2 := by
    have hterm : ∀ m ∈ (Finset.range (N + 1)).filter (fun m => m < m₀),
        (2 * (m : ℝ) + 1) * farShare R m ≤ (2 * (m : ℝ) + 1) := by
      intro m _
      calc (2 * (m : ℝ) + 1) * farShare R m ≤ (2 * (m : ℝ) + 1) * 1 :=
            mul_le_mul_of_nonneg_left (farShare_le_one R m) (by positivity)
        _ = (2 * (m : ℝ) + 1) := mul_one _
    have hsub : (Finset.range (N + 1)).filter (fun m => m < m₀) ⊆ Finset.range m₀ := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
      exact hm.2
    calc ∑ m ∈ (Finset.range (N + 1)).filter (fun m => m < m₀),
          (2 * (m : ℝ) + 1) * farShare R m
        ≤ ∑ m ∈ (Finset.range (N + 1)).filter (fun m => m < m₀), (2 * (m : ℝ) + 1) :=
          Finset.sum_le_sum hterm
      _ ≤ ∑ m ∈ Finset.range m₀, (2 * (m : ℝ) + 1) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => by positivity)
      _ = (m₀ : ℝ) ^ 2 := sum_range_odd m₀
  have hfar : ∑ m ∈ (Finset.range (N + 1)).filter (fun m => ¬ m < m₀),
      (2 * (m : ℝ) + 1) * farShare R m ≤ ∑' m : ℕ, (2 * (m : ℝ) + 1) * a m := by
    have hterm : ∀ m ∈ (Finset.range (N + 1)).filter (fun m => ¬ m < m₀),
        (2 * (m : ℝ) + 1) * farShare R m ≤ (2 * (m : ℝ) + 1) * a m := by
      intro m hm
      simp only [Finset.mem_filter, not_lt] at hm
      exact mul_le_mul_of_nonneg_left (ha m hm.2) (by positivity)
    calc ∑ m ∈ (Finset.range (N + 1)).filter (fun m => ¬ m < m₀),
          (2 * (m : ℝ) + 1) * farShare R m
        ≤ ∑ m ∈ (Finset.range (N + 1)).filter (fun m => ¬ m < m₀),
            (2 * (m : ℝ) + 1) * a m := Finset.sum_le_sum hterm
      _ ≤ ∑ m ∈ Finset.range (N + 1), (2 * (m : ℝ) + 1) * a m :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun m _ _ => mul_nonneg (by positivity) (ha0 m))
      _ ≤ ∑' m : ℕ, (2 * (m : ℝ) + 1) * a m :=
          hs.sum_le_tsum _ (fun m _ => mul_nonneg (by positivity) (ha0 m))
  linarith [hsplit.le, hsplit.ge, hnear, hfar]

#print axioms circ_moment_le_of_tail_envelope

/-- **The substrate hypothesis from a TAIL envelope.** The cut `m₀` is uniform in aperture and
coupling; below it nothing is assumed. -/
theorem substrate_of_tail_envelope (m₀ : ℕ) (a : ℕ → ℝ)
    (ha0 : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * a m))
    (ha : ∀ (N : ℕ) (β : ℝ) (m : ℕ), m₀ ≤ m → farShare (MassGap.readYMAt N β) m ≤ a m) :
    ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B :=
  ⟨(m₀ : ℝ) ^ 2 + ∑' m : ℕ, (2 * (m : ℝ) + 1) * a m, fun N β =>
    circ_moment_le_of_tail_envelope (MassGap.readYMAt N β) m₀ a ha0 (ha N β) hs⟩

#print axioms substrate_of_tail_envelope

/-! ### The aperture half and the coupling half

The hypothesis carries two quantifiers, `∀ N` and `∀ β`, and they are not of equal weight. Split it:

* the APERTURE half, at one coupling — `∃ B, ∀ N, d2At N β ≤ B`, with `B` free to depend on `β`;
* the COUPLING half — that those `B` are bounded over `β`, which is the hypothesis itself.

The first follows from the second (`aperture_uniform_of_substrate`) and is discharged by a per-`β`
envelope (`aperture_uniform_of_share_envelope`), so it asks strictly less. The theorems below show
the gap is real: granting the aperture half at EVERY coupling does not give the hypothesis, because
a family can be bounded in the aperture at each coupling with the bound growing without limit in the
coupling. So any proof must use something about how the Wilson measure moves in `β`, and no amount of
aperture control substitutes for it — the same shape of statement as
`Substrate.substrate_bound_needs_more_than_positivity`, one quantifier up.

What this does NOT say is that the aperture half is easy. It is a statement about `Moment.Read`
families, so it shows the implication is not formal; at a general fixed `β` the aperture half needs a
clustering estimate at that coupling, which the tree has only near `β = 0` (`StrongCoupling`). -/

/-- The lag at half the period, at any aperture.

DERIVED: `(N+1)/2` is half the period, the largest value `circLag` attains. `1` is the period offset and `2` the halving; both are the circle's, not chosen. -/
def midLag (N : ℕ) : Fin (N + 1) := ⟨(N + 1) / 2, by omega⟩

theorem circLag_midLag (N : ℕ) : Moment.circLag (midLag N) = (N + 1) / 2 := by
  have hv : ((midLag N : Fin (N + 1)) : ℕ) = (N + 1) / 2 := rfl
  unfold Moment.circLag
  rw [hv]
  omega

/-- **All the weight at half the period**, at any aperture — the largest circle moment a read can
have. `Substrate.antipodeRead` is this at odd `N`; this one carries every aperture, which is what a
family indexed by `N` needs.

DERIVED: the `1` and `0` are the values of an indicator and `p` normalises, so neither is a
magnitude; `(N+1)/2` is half the period. -/
noncomputable def midRead (N : ℕ) : Moment.Read N where
  ρ := fun d => if d = midLag N then 1 else 0
  hρ := fun d => by split <;> norm_num
  hpos := by simp

theorem midRead_sum (N : ℕ) : ∑ d, (midRead N).ρ d = 1 := by
  show ∑ d : Fin (N + 1), (if d = midLag N then (1 : ℝ) else 0) = 1
  simp

theorem midRead_moment (N : ℕ) :
    ∑ d, (midRead N).p d * (Moment.circLag d : ℝ) ^ 2 = ((((N + 1) / 2 : ℕ)) : ℝ) ^ 2 := by
  have hsum := midRead_sum N
  have hp : ∀ d, (midRead N).p d = (midRead N).ρ d := by
    intro d; simp [Moment.Read.p, hsum]
  have hterm : ∀ d : Fin (N + 1),
      (midRead N).p d * (Moment.circLag d : ℝ) ^ 2
        = if d = midLag N then ((Moment.circLag d : ℕ) : ℝ) ^ 2 else 0 := by
    intro d
    rw [hp d]
    show (if d = midLag N then (1 : ℝ) else 0) * _ = _
    split <;> ring
  rw [Finset.sum_congr rfl (fun d _ => hterm d),
    Finset.sum_ite_eq' Finset.univ (midLag N) (fun d => ((Moment.circLag d : ℕ) : ℝ) ^ 2)]
  simp only [Finset.mem_univ, if_true]
  rw [circLag_midLag N]

/-- The contact read has moment zero — every far share vanishes. -/
theorem contactRead_moment (N : ℕ) :
    ∑ d, (contactRead N).p d * (Moment.circLag d : ℝ) ^ 2 = 0 := by
  rw [circ_moment_eq_layer]
  refine Finset.sum_eq_zero (fun m _ => ?_)
  rw [contactRead_farShare]
  ring

/-- **A family bounded in the aperture at every coupling, unbounded over couplings.** At coupling `β`
it is the mid-lag read while the aperture stays below `β` and the contact read afterwards, so at each
`β` only finitely many apertures carry any weight away from zero.

DERIVED: the switch is at `(N : ℝ) ≤ β`, which is the statement "the aperture has not yet passed the
coupling"; no magnitude is chosen, and any strictly increasing switch gives the same family. -/
noncomputable def sepRead (N : ℕ) (β : ℝ) : Moment.Read N :=
  if (N : ℝ) ≤ β then midRead N else contactRead N

/-- At a fixed coupling the family's moments are capped, by a cap that depends on the coupling. -/
theorem sepRead_moment_le (N : ℕ) (β : ℝ) :
    ∑ d, (sepRead N β).p d * (Moment.circLag d : ℝ) ^ 2 ≤ ((β + 1) / 2) ^ 2 := by
  unfold sepRead
  split
  · rename_i hle
    rw [midRead_moment]
    have hnat : 2 * ((N + 1) / 2) ≤ N + 1 := by omega
    have hcast : (2 : ℝ) * ((((N + 1) / 2 : ℕ)) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    have h0 : (0 : ℝ) ≤ ((((N + 1) / 2 : ℕ)) : ℝ) := Nat.cast_nonneg _
    have hN : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [hN] at hcast
    nlinarith [hle, hcast, h0]
  · rw [contactRead_moment]
    positivity

theorem sepRead_aperture_bounded (β : ℝ) :
    ∃ B : ℝ, ∀ N : ℕ, ∑ d, (sepRead N β).p d * (Moment.circLag d : ℝ) ^ 2 ≤ B :=
  ⟨((β + 1) / 2) ^ 2, fun N => sepRead_moment_le N β⟩

theorem sepRead_moment_unbounded (B : ℝ) :
    ∃ (N : ℕ) (β : ℝ), B < ∑ d, (sepRead N β).p d * (Moment.circLag d : ℝ) ^ 2 := by
  obtain ⟨k, hk⟩ := exists_nat_gt B
  refine ⟨2 * k + 1, ((2 * k + 1 : ℕ) : ℝ), ?_⟩
  unfold sepRead
  rw [if_pos (le_refl (((2 * k + 1 : ℕ) : ℝ))), midRead_moment]
  have hdiv : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  rw [hdiv]
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  nlinarith [hk, hk0]

/-- **THE APERTURE HALF DOES NOT GIVE THE COUPLING HALF.**

`sepRead` is a family of reads meeting exactly the two clauses `wilson_reflection_positive_at`
asserts. At every coupling its circular second moments are bounded in the aperture; over couplings
they exceed every `B`. So `(∀ β, ∃ B, ∀ N, …)` does not imply `(∃ B, ∀ N β, …)`, and no argument that
controls the aperture at each coupling separately can reach the substrate hypothesis.

The measured flatness of `d2At` in the aperture at one coupling is therefore consistent with the
hypothesis and does not bear on it: this theorem says exactly that such flatness, even granted at
EVERY coupling, leaves the hypothesis open. -/
theorem aperture_uniformity_does_not_give_coupling_uniformity :
    (∀ β : ℝ, ∃ B : ℝ, ∀ N : ℕ,
        ∑ d, (sepRead N β).p d * (Moment.circLag d : ℝ) ^ 2 ≤ B) ∧
      ¬ (∃ B : ℝ, ∀ (N : ℕ) (β : ℝ),
        ∑ d, (sepRead N β).p d * (Moment.circLag d : ℝ) ^ 2 ≤ B) := by
  refine ⟨sepRead_aperture_bounded, ?_⟩
  rintro ⟨B, hB⟩
  obtain ⟨N, β, h⟩ := sepRead_moment_unbounded B
  exact absurd (hB N β) (not_le.mpr h)

#print axioms aperture_uniformity_does_not_give_coupling_uniformity

/-- The aperture half is implied by the hypothesis, so it is the weaker of the two. -/
theorem aperture_uniform_of_substrate (h : ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B) (β : ℝ) :
    ∃ B : ℝ, ∀ N : ℕ, MassGap.d2At N β ≤ B := by
  obtain ⟨B, hB⟩ := h
  exact ⟨B, fun N => hB N β⟩

/-- The aperture half at ONE coupling, from an envelope at that coupling only. The envelope may
depend on `β`; what `substrate_of_share_envelope` additionally requires is that it need not. -/
theorem aperture_uniform_of_share_envelope (β : ℝ) (a : ℕ → ℝ)
    (ha0 : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * a m))
    (ha : ∀ (N : ℕ) (m : ℕ), farShare (MassGap.readYMAt N β) m ≤ a m) :
    ∃ B : ℝ, ∀ N : ℕ, MassGap.d2At N β ≤ B :=
  ⟨∑' m : ℕ, (2 * (m : ℝ) + 1) * a m, fun N =>
    circ_moment_le_of_envelope (MassGap.readYMAt N β) a ha0 (ha N) hs⟩

#print axioms aperture_uniform_of_share_envelope


/-! ### Sharpness: the threshold exponent is exactly two

`square_envelope_not_summable` shows the criterion cannot be entered at exponent `2`. The family
below shows more: exponent `2` is not merely out of the criterion's reach, it is FALSE. Its far share
obeys a square envelope with a constant free of the aperture, and its moments are unbounded. So an
envelope condition is enough exactly above exponent `2` and not at it. -/

/-- The telescoping weight `1/j² − 1/(j+1)²`, and `0` at the origin.

DERIVED: nothing is chosen. The weight is the increment of `−1/j²`, which is the profile whose
partial sums are exactly the square envelope this family is built to saturate. -/
noncomputable def telWeight (j : ℕ) : ℝ :=
  if j = 0 then 0 else 1 / (j : ℝ) ^ 2 - 1 / ((j : ℝ) + 1) ^ 2

theorem telWeight_nonneg (j : ℕ) : 0 ≤ telWeight j := by
  unfold telWeight
  split
  · exact le_refl 0
  · rename_i h
    have hj : (1 : ℝ) ≤ (j : ℝ) := by
      have : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr h
      exact_mod_cast this
    have h1 : (0 : ℝ) < (j : ℝ) := by linarith
    have h2 : (0 : ℝ) < (j : ℝ) + 1 := by linarith
    rw [sub_nonneg, div_le_div_iff₀ (by positivity : (0:ℝ) < ((j:ℝ)+1)^2)
      (by positivity : (0:ℝ) < (j:ℝ)^2)]
    nlinarith [hj, h1, h2]

/-- **The telescoping sum.** `∑_{j ≤ M} telWeight j = 1 − 1/(M+1)²`. -/
theorem telWeight_sum (M : ℕ) :
    ∑ j ∈ Finset.range (M + 1), telWeight j = 1 - 1 / ((M : ℝ) + 1) ^ 2 := by
  induction M with
  | zero => simp [telWeight]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hne : n + 1 ≠ 0 := Nat.succ_ne_zero n
      have hval : telWeight (n + 1)
          = 1 / (((n : ℝ) + 1)) ^ 2 - 1 / (((n : ℝ) + 1) + 1) ^ 2 := by
        unfold telWeight
        rw [if_neg hne]
        push_cast
        ring
      rw [hval]
      push_cast
      ring

/-- **A read whose far share saturates a square envelope.** Weight `telWeight j` at lag `j` for
`1 ≤ j ≤ k+1`, and nothing beyond; on that range the circle lag IS the lag index, so the far share
telescopes.

DERIVED: `k+1` is the antipode of the period `2k+2`, which is the largest lag at which the circle
distance still equals the index; the weights are `telWeight`. Nothing is chosen. -/
noncomputable def squareRead (k : ℕ) : Moment.Read (2 * k + 1) where
  ρ := fun d => if (d : ℕ) ≤ k + 1 then telWeight (d : ℕ) else 0
  hρ := fun d => by
    split
    · exact telWeight_nonneg _
    · exact le_refl 0
  hpos := by
    have hnn : ∀ d : Fin (2 * k + 1 + 1),
        (0 : ℝ) ≤ (if (d : ℕ) ≤ k + 1 then telWeight (d : ℕ) else 0) := by
      intro d; split
      · exact telWeight_nonneg _
      · exact le_refl 0
    have hmem : (⟨1, by omega⟩ : Fin (2 * k + 1 + 1)) ∈ Finset.univ := Finset.mem_univ _
    have hle := Finset.single_le_sum
      (f := fun d : Fin (2 * k + 1 + 1) =>
        (if (d : ℕ) ≤ k + 1 then telWeight (d : ℕ) else 0)) (fun d _ => hnn d) hmem
    have hval : (if ((⟨1, by omega⟩ : Fin (2 * k + 1 + 1)) : ℕ) ≤ k + 1
        then telWeight (((⟨1, by omega⟩ : Fin (2 * k + 1 + 1)) : ℕ)) else 0) = 3 / 4 := by
      have hv : ((⟨1, by omega⟩ : Fin (2 * k + 1 + 1)) : ℕ) = 1 := rfl
      rw [hv, if_pos (by omega)]
      unfold telWeight
      norm_num
    rw [hval] at hle
    show (0 : ℝ) < ∑ d : Fin (2 * k + 1 + 1),
      (if (d : ℕ) ≤ k + 1 then telWeight (d : ℕ) else 0)
    linarith

/-- Every sum against the circle lag collapses to the near range, where the lag is the index. -/
theorem squareRead_sum_eq (k : ℕ) (g : ℕ → ℝ) :
    ∑ d : Fin (2 * k + 1 + 1), (squareRead k).ρ d * g (Moment.circLag d)
      = ∑ j ∈ Finset.range (k + 2), telWeight j * g j := by
  classical
  have hfin : ∑ d : Fin (2 * k + 1 + 1), (squareRead k).ρ d * g (Moment.circLag d)
      = ∑ j ∈ Finset.range (2 * k + 1 + 1),
          (if j ≤ k + 1 then telWeight j else 0) * g (min j (2 * k + 1 + 1 - j)) :=
    Fin.sum_univ_eq_sum_range
      (fun j => (if j ≤ k + 1 then telWeight j else 0) * g (min j (2 * k + 1 + 1 - j)))
      (2 * k + 1 + 1)
  rw [hfin]
  have hsub : Finset.range (k + 2) ⊆ Finset.range (2 * k + 1 + 1) := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  have hzero : ∀ j ∈ Finset.range (2 * k + 1 + 1), j ∉ Finset.range (k + 2) →
      (if j ≤ k + 1 then telWeight j else 0) * g (min j (2 * k + 1 + 1 - j)) = 0 := by
    intro j _ hnj
    simp only [Finset.mem_range, not_lt] at hnj
    rw [if_neg (by omega)]
    ring
  rw [← Finset.sum_subset hsub hzero]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  simp only [Finset.mem_range] at hj
  rw [if_pos (by omega)]
  have hmin : min j (2 * k + 1 + 1 - j) = j := by omega
  rw [hmin]

/-- The read's total mass is `1 − 1/(k+2)²`, so it lies between `3/4` and `1`. -/
theorem squareRead_mass (k : ℕ) :
    ∑ d, (squareRead k).ρ d = 1 - 1 / ((k : ℝ) + 2) ^ 2 := by
  have h := squareRead_sum_eq k (fun _ => 1)
  simp only [mul_one] at h
  rw [h, telWeight_sum (k + 1)]
  push_cast
  ring

theorem squareRead_mass_ge (k : ℕ) : (3 : ℝ) / 4 ≤ ∑ d, (squareRead k).ρ d := by
  rw [squareRead_mass]
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h2 : (2 : ℝ) ≤ (k : ℝ) + 2 := by linarith
  have hpos : (0 : ℝ) < ((k : ℝ) + 2) ^ 2 := by positivity
  have hq : 1 / ((k : ℝ) + 2) ^ 2 ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 4)]
    nlinarith [h2]
  linarith

theorem squareRead_mass_le (k : ℕ) : ∑ d, (squareRead k).ρ d ≤ 1 := by
  rw [squareRead_mass]
  have h : (0 : ℝ) < 1 / ((k : ℝ) + 2) ^ 2 := by positivity
  linarith

/-- The far share is the far `ρ`-mass over the total, for any read. -/
theorem farShare_eq_rho {N : ℕ} (R : Moment.Read N) (m : ℕ) :
    farShare R m = (∑ d ∈ farSet N m, R.ρ d) / (∑ d, R.ρ d) := by
  rw [farShare, Finset.sum_div]
  rfl

/-- Beyond a cut, the telescoping profile carries at most `1/(m+1)²`. -/
theorem tel_far_le (k m : ℕ) :
    ∑ j ∈ Finset.range (k + 2), telWeight j * (if m < j then (1 : ℝ) else 0)
      ≤ 1 / ((m : ℝ) + 1) ^ 2 := by
  classical
  have hfilt : ∑ j ∈ Finset.range (k + 2), telWeight j * (if m < j then (1 : ℝ) else 0)
      = ∑ j ∈ (Finset.range (k + 2)).filter (fun j => m < j), telWeight j := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split <;> ring
  rw [hfilt]
  by_cases hle : m + 1 ≤ k + 2
  · have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (k + 2))
      (fun j => m < j) telWeight
    have hnot : (Finset.range (k + 2)).filter (fun j => ¬ m < j) = Finset.range (m + 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, not_lt]
      omega
    rw [hnot] at hsplit
    have h1 := telWeight_sum (k + 1)
    have h2 := telWeight_sum m
    have h1' : ∑ j ∈ Finset.range (k + 2), telWeight j = 1 - 1 / ((k : ℝ) + 2) ^ 2 := by
      rw [show k + 2 = (k + 1) + 1 from rfl, h1]; push_cast; ring
    have hkpos : (0 : ℝ) < 1 / ((k : ℝ) + 2) ^ 2 := by positivity
    linarith [hsplit, h1', h2]
  · have hgt : k + 2 < m + 1 := by omega
    have hempty : (Finset.range (k + 2)).filter (fun j => m < j) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr ?_
      intro j hj
      simp only [Finset.mem_range] at hj
      omega
    rw [hempty, Finset.sum_empty]
    positivity

/-- **The far share obeys a square envelope, at every aperture.** -/
theorem squareRead_farShare_le (k m : ℕ) :
    farShare (squareRead k) m ≤ (4 / 3) / ((m : ℝ) + 1) ^ 2 := by
  classical
  have hnum : ∑ d ∈ farSet (2 * k + 1) m, (squareRead k).ρ d ≤ 1 / ((m : ℝ) + 1) ^ 2 := by
    have hrw : ∑ d ∈ farSet (2 * k + 1) m, (squareRead k).ρ d
        = ∑ d : Fin (2 * k + 1 + 1), (squareRead k).ρ d
            * (fun j : ℕ => if m < j then (1 : ℝ) else 0) (Moment.circLag d) := by
      rw [farSet, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      by_cases hc : m < Moment.circLag d
      · simp [hc]
      · simp [hc]
    rw [hrw, squareRead_sum_eq k (fun j : ℕ => if m < j then (1 : ℝ) else 0)]
    exact tel_far_le k m
  have hmass := squareRead_mass_ge k
  have hden : (0 : ℝ) < ∑ d, (squareRead k).ρ d := (squareRead k).hpos
  have hnn : (0 : ℝ) ≤ ∑ d ∈ farSet (2 * k + 1) m, (squareRead k).ρ d :=
    Finset.sum_nonneg (fun d _ => (squareRead k).hρ d)
  have hm : (0 : ℝ) < ((m : ℝ) + 1) ^ 2 := by positivity
  have hcancel : (1 / ((m : ℝ) + 1) ^ 2) * ((m : ℝ) + 1) ^ 2 = 1 := by field_simp
  have hF : (∑ d ∈ farSet (2 * k + 1) m, (squareRead k).ρ d) * ((m : ℝ) + 1) ^ 2 ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hnum hm.le
    linarith [this, hcancel.le, hcancel.ge]
  rw [farShare_eq_rho, div_le_div_iff₀ hden hm]
  linarith [hF, hmass]

/-- The harmonic comparison: the telescoping profile's squared-lag total dominates `H_{k+2} − 1`. -/
theorem squareRead_moment_ge (k : ℕ) :
    (∑ j ∈ Finset.range (k + 2), 1 / ((j : ℝ) + 1)) - 1
      ≤ ∑ d, (squareRead k).p d * (Moment.circLag d : ℝ) ^ 2 := by
  classical
  have hnum : ∑ d, (squareRead k).ρ d * (Moment.circLag d : ℝ) ^ 2
      = ∑ j ∈ Finset.range (k + 2), telWeight j * (j : ℝ) ^ 2 :=
    squareRead_sum_eq k (fun j : ℕ => (j : ℝ) ^ 2)
  have hcmp : ∀ j ∈ Finset.range (k + 2),
      1 / ((j : ℝ) + 1) - telWeight j * (j : ℝ) ^ 2 ≤ (if j = 0 then (1 : ℝ) else 0) := by
    intro j _
    rcases Nat.eq_zero_or_pos j with h0 | hp
    · subst h0
      simp [telWeight]
    · have hne : j ≠ 0 := Nat.pos_iff_ne_zero.mp hp
      rw [if_neg hne]
      have hj : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hp
      have hval : telWeight j * (j : ℝ) ^ 2
          = (2 * (j : ℝ) + 1) / ((j : ℝ) + 1) ^ 2 := by
        unfold telWeight
        rw [if_neg hne]
        field_simp
        ring
      rw [hval]
      have h1 : (0 : ℝ) < (j : ℝ) + 1 := by linarith
      have hle : 1 / ((j : ℝ) + 1) ≤ (2 * (j : ℝ) + 1) / ((j : ℝ) + 1) ^ 2 := by
        rw [div_le_div_iff₀ h1 (by positivity)]
        nlinarith [hj]
      linarith
  have hsum := Finset.sum_le_sum hcmp
  have hone : ∑ j ∈ Finset.range (k + 2), (if j = 0 then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_ite_eq' (Finset.range (k + 2)) 0 (fun _ => (1 : ℝ))]
    rw [if_pos (Finset.mem_range.mpr (by omega))]
  have hdist : ∑ j ∈ Finset.range (k + 2),
      (1 / ((j : ℝ) + 1) - telWeight j * (j : ℝ) ^ 2)
      = (∑ j ∈ Finset.range (k + 2), 1 / ((j : ℝ) + 1))
        - ∑ j ∈ Finset.range (k + 2), telWeight j * (j : ℝ) ^ 2 := by
    rw [Finset.sum_sub_distrib]
  rw [hdist, hone] at hsum
  have hmomeq : ∑ d, (squareRead k).p d * (Moment.circLag d : ℝ) ^ 2
      = (∑ d, (squareRead k).ρ d * (Moment.circLag d : ℝ) ^ 2)
          / (∑ d, (squareRead k).ρ d) := circ_moment_eq_rho_ratio (squareRead k)
  have hmassle := squareRead_mass_le k
  have hmasspos : (0 : ℝ) < ∑ d, (squareRead k).ρ d := (squareRead k).hpos
  have hnumnn : (0 : ℝ) ≤ ∑ d, (squareRead k).ρ d * (Moment.circLag d : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun d _ => mul_nonneg ((squareRead k).hρ d) (sq_nonneg _))
  have hge : ∑ d, (squareRead k).ρ d * (Moment.circLag d : ℝ) ^ 2
      ≤ ∑ d, (squareRead k).p d * (Moment.circLag d : ℝ) ^ 2 := by
    rw [hmomeq, le_div_iff₀ hmasspos]
    nlinarith [hnumnn, hmassle, hmasspos]
  rw [hnum] at hge
  linarith [hsum, hge]

/-- **SHARPNESS: A SQUARE FAR-SHARE ENVELOPE IS NOT ENOUGH.**

`squareRead` satisfies the two clauses of `wilson_reflection_positive_at`, its far share is under
`(4/3)/(m+1)²` at every cut and every aperture, and its circular second moments exceed every `B`. So
the threshold exponent in `substrate_of_cubic_share` is exactly `2`: above it the envelope
discharges the substrate hypothesis, at it the hypothesis is FALSE.

The mechanism is the layer cake: a square share profile has weighted total
`∑ (2m+1)/(m+1)² ≍ ∑ 1/(m+1)`, which is the harmonic series. -/
theorem square_share_is_not_enough :
    (∀ k m : ℕ, farShare (squareRead k) m ≤ (4 / 3) / ((m : ℝ) + 1) ^ 2) ∧
      (∀ B : ℝ, ∃ k : ℕ, B < ∑ d, (squareRead k).p d * (Moment.circLag d : ℝ) ^ 2) := by
  refine ⟨squareRead_farShare_le, fun B => ?_⟩
  have htend : Filter.Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range n, (1 / (i + 1) : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_sum_range_one_div_nat_succ_atTop
  have hev := htend.eventually_gt_atTop (B + 1)
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨n, ?_⟩
  have hmono : ∑ i ∈ Finset.range n, (1 / (i + 1) : ℝ)
      ≤ ∑ i ∈ Finset.range (n + 2), (1 / (i + 1) : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (by intro j hj; simp only [Finset.mem_range] at hj ⊢; omega)
      (fun i _ _ => by positivity)
  have hge := squareRead_moment_ge n
  have hcast : ∑ i ∈ Finset.range (n + 2), (1 / (i + 1) : ℝ)
      = ∑ j ∈ Finset.range (n + 2), 1 / ((j : ℝ) + 1) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    push_cast
    ring
  rw [hcast] at hmono
  linarith

#print axioms square_share_is_not_enough


/-! ### Why the aperture argument cannot be run forwards -/

/-- `3/4 < 3^{-1/4} < 19/25`, from `(3^{-1/4})⁴ = 1/3` and the strict monotonicity of the fourth
power on the nonnegatives.

DERIVED: `3` and `-1/4` are `e^{-κ₀}` with `κ₀ = ¼log3`; the two rationals are the coarsest brackets
that separate the two constants below, and the proof exhibits them rather than assuming them. -/
theorem rpow_bracket :
    (3 : ℝ) / 4 < (3 : ℝ) ^ (-(1 : ℝ) / 4) ∧ (3 : ℝ) ^ (-(1 : ℝ) / 4) < 19 / 25 := by
  set f : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hf
  have hfpos : 0 < f := Real.rpow_pos_of_pos (by norm_num) _
  have hf4 : f ^ (4 : ℕ) = 1 / 3 := by
    rw [hf, ← Real.rpow_natCast ((3 : ℝ) ^ (-(1 : ℝ) / 4)) 4,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    have he : -(1 : ℝ) / 4 * ((4 : ℕ) : ℝ) = -(1 : ℝ) := by push_cast; ring
    rw [he, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_one]
    norm_num
  constructor
  · by_contra hcon
    push_neg at hcon
    have hle : f ^ (4 : ℕ) ≤ ((3 : ℝ) / 4) ^ (4 : ℕ) := pow_le_pow_left₀ hfpos.le hcon 4
    rw [hf4] at hle
    norm_num at hle
  · by_contra hcon
    push_neg at hcon
    have hle : ((19 : ℝ) / 25) ^ (4 : ℕ) ≤ f ^ (4 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) hcon 4
    rw [hf4] at hle
    norm_num at hle

/-- `arccos y < π/2 − y` for `y ∈ (0,1)`, because `sin x < x`. -/
theorem arccos_lt_half_pi_sub {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    Real.arccos y < Real.pi / 2 - y := by
  have hy1' : y ≤ 1 := le_of_lt hy1
  have hy0' : (-1 : ℝ) ≤ y := by linarith
  have hpos : 0 < Real.arcsin y := Real.arcsin_pos.mpr hy0
  have hsin : Real.sin (Real.arcsin y) = y := Real.sin_arcsin hy0' hy1'
  have hlt : Real.sin (Real.arcsin y) < Real.arcsin y := Real.sin_lt hpos
  rw [hsin] at hlt
  rw [Real.arccos]
  linarith

/-- **THE FORWARD RUN CANNOT RE-ENTER.**

    substrateThreshold  <  (1 − 3^{−1/4}) / 8

`Moment.Read.substrate_lt_of_tension_lt_floor` turns `μ < κ₀` into a substrate ratio below the right
side; `Complete.confinement_at_of_substrate_sharp` consumes a ratio below the left side. The left is
strictly the smaller, so what the first produces is not what the second consumes and running the
aperture argument forwards yields no new bound.

DERIVED: both constants are the development's own — `arccos(3^{−1/4})²/(2π)²` is
`Complete.substrateThreshold` and `(1 − 3^{−1/4})/8` is the ceiling of
`Moment.Read.substrate_lt_of_tension_lt_floor`. The brackets on `3^{−1/4}` and `π` are exhibited by
`rpow_bracket` and Mathlib's `pi_gt_three` / `pi_lt_d2`. -/
theorem substrateThreshold_lt_ceiling :
    MassGap.substrateThreshold < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8 := by
  obtain ⟨hlow, hhigh⟩ := rpow_bracket
  unfold MassGap.substrateThreshold
  set f : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hf
  have hf0 : 0 < f := by linarith
  have hf1 : f < 1 := by linarith
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi15 : Real.pi < 3.15 := Real.pi_lt_d2
  have hA : Real.arccos f < Real.pi / 2 - f := arccos_lt_half_pi_sub hf0 hf1
  have hA0 : 0 ≤ Real.arccos f := Real.arccos_nonneg f
  have hAub : Real.arccos f < 0.825 := by linarith
  have hAsq : Real.arccos f ^ 2 < 0.69 := by nlinarith [hA0, hAub]
  have hpisq : (36 : ℝ) < (2 * Real.pi) ^ 2 := by nlinarith [hpi3, Real.pi_pos]
  have hpisq0 : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
  have hrhs : (0.69 : ℝ) < (1 - f) / 8 * (2 * Real.pi) ^ 2 := by nlinarith [hpisq, hhigh]
  rw [div_lt_iff₀ hpisq0]
  linarith

#print axioms substrateThreshold_lt_ceiling

/-- **The two numbers, side by side.** `taylor_le_substrateThreshold` already places the
origin-tangent threshold below `substrateThreshold`; this places `substrateThreshold` strictly below
the ceiling a tension under the floor produces. So the three constants of the aperture argument are
ordered

    2(1 − 3^{−1/4})/(2π)²  ≤  substrateThreshold  <  (1 − 3^{−1/4})/8

and the forward direction lands on the far side of the entry condition. -/
theorem aperture_constants_ordered :
    2 * (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / (2 * Real.pi) ^ 2 ≤ MassGap.substrateThreshold ∧
      MassGap.substrateThreshold < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8 :=
  ⟨MassGap.taylor_le_substrateThreshold, substrateThreshold_lt_ceiling⟩

#print axioms aperture_constants_ordered

end MassGap.ContactDominance
