import Mathlib
import MassGap.Complete
import MassGap.ZeroMode
import MassGap.Substrate
import MassGap.WilsonModel

/-!
# Contact dominance: the substrate hypothesis as a condition on the far share

`WilsonModel.existence_and_gap_of_substrate` consumes

    h : ∃ B : ℝ, ∀ N β, d2At N β ≤ B

with `d2At N β = ∑ d, (readYMAt N β).p d * (Moment.circLag d : ℝ) ^ 2`. This file restates that
hypothesis as a condition on one scalar profile — the share of a read's weight beyond a cut — and
records the exponent at which such a condition can be met.

## The far share and the layer cake

`farShare R m = ∑_{d : circLag d > m} R.p d` is the probability a read places at circle lag strictly
beyond `m`. Because `k² = ∑_{m<k} (2m+1)`, the circular second moment equals the `(2m+1)`-weighted
sum of that profile:

    ∑_d p d · circLag(d)²  =  ∑_{m < N+1} (2m+1) · farShare R m        (`circ_moment_eq_layer`)

The two sides are the same number at every aperture and for every read, so a uniform bound on the
weighted sum and the substrate hypothesis are the same condition.

## The exponent

From the identity, a nonnegative envelope `farShare ≤ a m` with `∑ (2m+1)·a m` convergent bounds the
moment by that sum (`circ_moment_le_of_envelope`); the bound is the sum itself, and the aperture does
not enter it. A power envelope `a m = C(m+1)^{-s}` has convergent weighted total exactly when
`s > 2`. `substrate_of_cubic_share` runs the criterion at `s = 3`; `square_envelope_not_summable`
shows the weighted total diverges at `s = 2`; and `square_share_is_not_enough` exhibits `squareRead`,
a family of `Moment.Read`s whose far share stays under `(4/3)(m+1)^{-2}` at every aperture and whose
circular second moments exceed every `B`. The exponent `2` comes from the weight: `(2m+1)` is
`(m+1)² − m²`, so a square share profile has weighted total `∑ (2m+1)(m+1)^{-2}`, which diverges like
the harmonic series.

Two cruder bounds are stated separately because each holds at a single aperture and a single cut: a
cut bound `moment ≤ m² + (N+1)²/4 · farShare m` (`circ_moment_le_cut`) and its Chebyshev converse
`(m+1)² · farShare m ≤ moment` (`farShare_le_of_circ_moment`).

Only the tail of the profile is constrained. `circ_moment_le_of_tail_envelope` assumes the envelope
from a cut `m₀` upward and nothing below it: `farShare ≤ 1` caps the near block by `m₀²` on its own.
The cut is therefore a parameter of the criterion rather than of the read.

## The two quantifiers

`∀ N` and `∀ β` split the hypothesis into an aperture half — `∃ B, ∀ N, d2At N β ≤ B` at one
coupling, with `B` bound inside the quantifier over couplings and so free to depend on `β` — and a
coupling half, that those `B` are bounded over `β`. The aperture half follows from the hypothesis
(`aperture_uniform_of_substrate`) and is discharged by a per-`β` envelope
(`aperture_uniform_of_share_envelope`).
`aperture_uniformity_does_not_give_coupling_uniformity` separates the two on abstract `Moment.Read`
families: `sepRead` is bounded in the aperture at each coupling and unbounded over couplings, so
`(∀ β, ∃ B, ∀ N, …)` does not imply `(∃ B, ∀ N β, …)` for `Moment.Read` families. That statement
quantifies over `sepRead`, not over `readYMAt`.

## Summability carries weight in the criterion

`envelope_load_bearing` exhibits `Moment.Read` families whose far share is `1` at every cut the
aperture admits: the only envelope covering them is `a ≡ 1`, `∑ (2m+1)·1` diverges, and circular
second moments over `Moment.Read` families exceed every `B`. `square_share_is_not_enough` does the
same at the exponent itself. `envelope_nonvacuous` exhibits a read the criterion accepts with bound
`0`.

## The constants of the aperture argument

`Moment.Read.substrate_lt_of_tension_lt_floor` produces `substrateRatio < (1 − 3^{−1/4})/8`;
`Complete.confinement_at_of_substrate_sharp` consumes `substrateRatio < substrateThreshold`.
`substrateThreshold_lt_ceiling` proves the second number is strictly smaller than the first, and
`aperture_constants_ordered` places all three in order. The outer two differ by the factor `π²/4`:
`(1 − 3^{−1/4})/8 = (π²/4)·(2(1 − 3^{−1/4})/(2π)²)`. All three constants are ratios with the
aperture divided out; none of them bounds `d2At` itself.
-/

namespace MassGap.ContactDominance

open MassGap.Moment

/-! ### The far share -/

/-- The lags whose circle distance exceeds a cut `m`, as a `Finset (Fin (N + 1))`.

DERIVED: `1` is the offset in `Fin (N + 1)`: the lag index ranges over the whole period `N + 1`. The
cut `m` is a parameter. -/
def farSet (N m : ℕ) : Finset (Fin (N + 1)) :=
  Finset.univ.filter (fun d => m < Moment.circLag d)

/-- The far share: the total `p`-weight a read places at circle lag strictly beyond `m`, summed over
`farSet N m`. It is a real number in the unit interval, by `farShare_nonneg` and `farShare_le_one`.

DERIVED: no numeral appears in the statement. -/
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

/-- The cut bound. At one aperture and one cut `m`, the circular second moment of `R` is at most
`m² + ((N+1)²/4)·farShare R m`. The proof splits the lag range at `m`: below the cut every squared
lag is at most `m²` and the shares there sum to at most one; above it every squared lag is at most
the squared half-period, by `Substrate.circLag_le_half`.

DERIVED: the exponent `2` is the moment's own power, applied to `m` and to the half-period. `1` in
`(N : ℝ) + 1` is the period `N + 1`. `4` is the square of the halving in `circLag ≤ (N+1)/2`, so
`(N+1)²/4` is the largest squared circle distance available at this aperture. -/
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

/-- The Chebyshev converse of the cut bound: `(m+1)² · farShare R m` is at most the circular second
moment. Beyond the cut every squared lag is at least `(m+1)²`, and the terms dropped from the moment
are nonnegative.

DERIVED: `1` makes `m + 1` the smallest lag strictly beyond the cut `m`; the exponent `2` is the
moment's own power, applied to that smallest lag. -/
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

/-! ### The layer cake: the moment as a weighted far-share profile -/

/-- `∑_{m < k} (2m + 1) = k²` in `ℝ`, by induction on `k`.

DERIVED: `2` and `1` form the summand `2m + 1 = (m+1)² − m²`, the increment of the square; the
exponent `2` on the right is that square. -/
theorem sum_range_odd (k : ℕ) : ∑ m ∈ Finset.range k, (2 * (m : ℝ) + 1) = (k : ℝ) ^ 2 := by
  induction k with
  | zero => simp
  | succ j ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- When `k ≤ n`, filtering `Finset.range n` by `· < k` gives `Finset.range k`.

DERIVED: no numeral appears in the statement. -/
theorem filter_lt_range {k n : ℕ} (hk : k ≤ n) :
    (Finset.range n).filter (fun m => m < k) = Finset.range k := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨lt_of_lt_of_le h hk, h⟩

/-- The circle lag of any `d : Fin (N + 1)` is strictly below `N + 1`: it never reaches the lag
arity.

DERIVED: `1` is the offset in `Fin (N + 1)`, which is both the lag arity and the period. -/
theorem circLag_lt_succ {N : ℕ} (d : Fin (N + 1)) : Moment.circLag d < N + 1 := by
  have h := d.isLt
  unfold Moment.circLag
  omega

/-- The layer cake. For any `R : Moment.Read N`,

    ∑_d p(d)·circLag(d)²  =  ∑_{m < N+1} (2m+1)·farShare R m

This is an equality, not a bound: the two sides are the same number at every aperture and for every
read. `sum_range_odd` supplies the pointwise expansion of `circLag(d)²` and `circLag_lt_succ` fixes
the index range.

DERIVED: the exponent `2` is the moment's own power. The weight `2m + 1` is `(m+1)² − m²`
(`sum_range_odd`). `1` in `Finset.range (N + 1)` is the lag arity, which `circLag` never reaches
(`circLag_lt_succ`). -/
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

/-- A nonnegative envelope `a` with `farShare R m ≤ a m` at every cut, and with `(2m+1)·a m`
summable, bounds the circular second moment of `R` by `∑' m, (2m+1)·a m`. The bound is the envelope's
own weighted total and the aperture `N` does not occur in it. The proof rewrites the moment by
`circ_moment_eq_layer` and compares term by term against the tsum.

DERIVED: `0` in `ha0` is the sign condition on the envelope. `2` and `1` form the layer-cake weight
`2m + 1 = (m+1)² − m²`. The exponent `2` is the moment's own power. -/
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

/-- One nonnegative profile `a` bounding `farShare (readYMAt N β) m` at every aperture, every
coupling and every cut, with `(2m+1)·a m` summable, yields `∃ B, ∀ N β, d2At N β ≤ B`. The witness
supplied for `B` is `∑' m, (2m+1)·a m`, and the per-aperture bound comes from
`circ_moment_le_of_envelope`.

DERIVED: `0` in `ha0` is the sign condition on the envelope; `2` and `1` form the layer-cake weight
`2m + 1`. -/
theorem substrate_of_share_envelope (a : ℕ → ℝ)
    (ha0 : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * a m))
    (ha : ∀ (N : ℕ) (β : ℝ) (m : ℕ), farShare (MassGap.readYMAt N β) m ≤ a m) :
    ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B :=
  ⟨∑' m : ℕ, (2 * (m : ℝ) + 1) * a m, fun N β =>
    circ_moment_le_of_envelope (MassGap.readYMAt N β) a ha0 (ha N β) hs⟩

#print axioms substrate_of_share_envelope

/-- From the same envelope hypotheses, `μYMAt N β < κ₀YM` at every `β`, for `N` eventually in
`Filter.atTop`. The composition of `substrate_of_share_envelope` with
`MassGap.confinement_of_bounded_substrate`; the aperture quantifier is `∀ᶠ`, so the conclusion holds
for all large enough `N` rather than for every `N`.

DERIVED: `0` in `ha0` is the sign condition on the envelope; `2` and `1` form the layer-cake weight
`2m + 1`. -/
theorem confinement_of_share_envelope (a : ℕ → ℝ)
    (ha0 : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * a m))
    (ha : ∀ (N : ℕ) (β : ℝ) (m : ℕ), farShare (MassGap.readYMAt N β) m ≤ a m) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, MassGap.μYMAt N β < MassGap.κ₀YM :=
  MassGap.confinement_of_bounded_substrate (substrate_of_share_envelope a ha0 hs ha)

#print axioms confinement_of_share_envelope


/-- The envelope hypotheses yield a witness `h : ∃ B, ∀ N β, d2At N β ≤ B` paired with the first
component of `MassGap.WilsonModel.existence_and_gap_of_substrate h`, stated for
`wilsonOfSubstrate h`: the norm of the weighted moment sum over `gap.s β` tends to `0` along
`Filter.atTop` in `τ` at every `β`; `gap.μ β - gap.κ` is negative at every `β`; and `gap.R` takes the
same value at any two arguments. The conclusion is a `∃ h, …`, so the witness and the three clauses
are bound together, and the clauses are stated about the model built from that particular witness.

`substrate_of_share_envelope` supplies the witness.

DERIVED: `0` in `ha0` is the sign condition on the envelope; `2` and `1` form the layer-cake weight
`2m + 1`; `0` in `nhds 0` is the limit point of the norm; `0` in `… < 0` is the sign asserted of
`gap.μ β - gap.κ`. -/
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

/-- `fun m => 1/((m : ℝ) + 1)²` is summable, obtained from Mathlib's
`Real.summable_one_div_nat_pow` at exponent `2` by shifting the index by one.

DERIVED: `1` in the numerator is the constant of the comparison series; `1` in `(m : ℝ) + 1` is the
index shift that keeps the summand finite at `m = 0`; `2` is the exponent. -/
theorem summable_inv_succ_sq : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := by
    simpa using Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
  have h' := (summable_nat_add_iff 1).mpr h
  refine h'.congr (fun m => ?_)
  push_cast
  ring

/-- `farShare (readYMAt N β) m ≤ C/(m+1)³`, uniformly in aperture and coupling, yields
`∃ B, ∀ N β, d2At N β ≤ B`. The proof passes that envelope to `substrate_of_share_envelope`,
dominating `(2m+1)·C/(m+1)³` by `2C/(m+1)²` and citing `summable_inv_succ_sq`.

DERIVED: `0` in `hC` is the sign condition on `C`. `1` in `(m : ℝ) + 1` shifts the index so the
envelope is finite at `m = 0`. `3` is the envelope exponent: the least integer strictly above `2`,
and `square_envelope_not_summable` shows exponent `2` gives a divergent weighted total. -/
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

/-- For `C > 0` the weighted envelope `fun m => (2m+1)·(C/(m+1)²)` is not summable. The proof
bounds it below by `C/(m+1)` and cites `Real.not_summable_one_div_natCast`. An envelope falling off
like `(m+1)^{-2}` therefore cannot be supplied to `circ_moment_le_of_envelope`.

DERIVED: `0` in `hC` is the strict sign condition on `C`; `2` and `1` form the layer-cake weight
`2m + 1`; `1` in `(m : ℝ) + 1` is the index shift; the exponent `2` is the envelope's power. -/
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

/-! ### The companion exponent, on the correlation rather than on the share

`Moment.circ_moment_le_of_geometric` consumes `p d ≤ C·r^{circLag d}` with `r < 1`, which is a decay
rate. The lemmas below run the same argument against any envelope in the circle lag whose squared-lag
moment converges; a power envelope carries no rate. The exponent here is `3`, one above the share's
`2`, because the far share has already absorbed one summation. -/

/-- A nonnegative envelope `b` in the circle lag with `R.p d ≤ b (circLag d)` and `(k : ℝ)^2 * b k`
summable bounds the circular second moment of `R` by `2·∑' k, k²·b k`. The aperture `N` does not
occur in the bound. `Moment.sum_circLag_le_two_mul` turns the sum over lags into a sum over circle
distances, and `Summable.sum_le_tsum` closes the partial sum against the tsum.

DERIVED: `0` in `hb0` is the sign condition on the envelope. The exponents `2` are the squared circle
lag, in the summability hypothesis and in the moment. The factor `2` in the conclusion is the fibre
multiplicity of `circLag` (`Moment.sum_circLag_le_two_mul`): a circle distance is attained by at most
two lags. -/
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

/-- One nonnegative envelope `b` in the circle lag, bounding `(readYMAt N β).p d` at every aperture,
coupling and lag, with `(k : ℝ)^2 * b k` summable, yields `∃ B, ∀ N β, d2At N β ≤ B`. The witness
supplied for `B` is `2 · ∑' k, k²·b k`, from `circ_moment_le_of_weight_envelope`. The hypothesis is a
pointwise envelope, not a decay rate.

DERIVED: `0` in `hb0` is the sign condition on the envelope; the exponent `2` is the squared circle
lag; `1` in `Fin (N + 1)` is the lag arity at aperture `N`. -/
theorem substrate_of_weight_envelope (b : ℕ → ℝ)
    (hb0 : ∀ k, 0 ≤ b k)
    (hs : Summable (fun k : ℕ => (k : ℝ) ^ 2 * b k))
    (hdecay : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)),
      (MassGap.readYMAt N β).p d ≤ b (Moment.circLag d)) :
    ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B :=
  ⟨2 * ∑' k : ℕ, (k : ℝ) ^ 2 * b k, fun N β =>
    circ_moment_le_of_weight_envelope (MassGap.readYMAt N β) b hb0 (hdecay N β) hs⟩

#print axioms substrate_of_weight_envelope

/-- `fun k => (k : ℝ)^2 * (1/((k : ℝ) + 1)^4)` is summable, by comparison with
`summable_inv_succ_sq`.

DERIVED: the exponent `2` is the squared-lag weight; `1` in the numerator and `1` in `(k : ℝ) + 1`
are the constant and the index shift of the envelope; `4` is the envelope's exponent, so the summand
falls off like `(k+1)^{-2}`. -/
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

/-- `(readYMAt N β).p d ≤ C/(circLag d + 1)⁴`, uniformly in aperture and coupling, yields
`∃ B, ∀ N β, d2At N β ≤ B`. The proof passes that envelope to `substrate_of_weight_envelope`, with
summability from `summable_sq_div_succ_pow_four`.

DERIVED: `0` in `hC` is the sign condition on `C`. `1` in `Fin (N + 1)` is the lag arity; `1` in
`(circLag d : ℝ) + 1` shifts the lag so the envelope is finite at lag `0`. `4` is the envelope
exponent: the least integer strictly above `3`, which is where `∑ k²·b k` stops converging for a
power envelope. -/
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

`Moment.Read.p` divides by the total mass, so the substrate hypothesis constrains the correlation `ρ`
only through a ratio. Written that way it reads: the squared-lag-weighted total of `ρ` stays within a
fixed multiple of its plain total. -/

/-- The `p`-weighted circular second moment equals the `ρ`-weighted one divided by the total
`ρ`-mass, by unfolding `Moment.Read.p` termwise.

DERIVED: the exponent `2` on each side is the moment's own power. -/
theorem circ_moment_eq_rho_ratio {N : ℕ} (R : Moment.Read N) :
    ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2
      = (∑ d, R.ρ d * (Moment.circLag d : ℝ) ^ 2) / (∑ d, R.ρ d) := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  simp only [Moment.Read.p]
  ring

/-- For any `B` and any single read,

    ∑_d p(d)·circLag(d)² ≤ B   ↔   ∑_d ρ(d)·circLag(d)² ≤ B·∑_d ρ(d)

from `circ_moment_eq_rho_ratio` and `div_le_iff₀` applied to `R.hpos`. A bound on the normalised
moment is thus the same as: the squared-lag-weighted total of `ρ` lies within the fixed multiple `B`
of its plain total. No decay or rate enters.

DERIVED: the exponent `2` on each side of the equivalence is the moment's own power. -/
theorem circ_moment_le_iff_rho {N : ℕ} (R : Moment.Read N) (B : ℝ) :
    (∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2 ≤ B)
      ↔ (∑ d, R.ρ d * (Moment.circLag d : ℝ) ^ 2 ≤ B * ∑ d, R.ρ d) := by
  rw [circ_moment_eq_rho_ratio, div_le_iff₀ R.hpos]

#print axioms circ_moment_le_iff_rho

/-- Two inputs bound the normalised moment from an unnormalised envelope: `ρ d ≤ b (circLag d)` with
`(k : ℝ)^2 * b k` summable, and a strictly positive lower bound `c` on the total `ρ`-mass. Together
they give `moment ≤ (2/c)·∑' k, k²·b k`. Neither input follows from the other: the envelope leaves
the normalisation free, and the mass bound says nothing about where the weight sits.

DERIVED: `0` in `hc` is the strict sign condition on `c`, and `0` in `hb0` the sign condition on the
envelope. The exponents `2` are the squared circle lag. The factor `2` in `2/c` is the fibre
multiplicity of `circLag` (`Moment.sum_circLag_le_two_mul`); `c` is the caller's own mass bound. -/
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

/-! ### Controls: the summability hypothesis is used, and the criterion is not vacuous -/

/-- The contact read at aperture `N`: `ρ` is the indicator of the lag index `0`, so all weight sits
at zero separation.

DERIVED: `0` in `d = 0` is the lag index carrying the weight. `1` and `0` are the two values of the
indicator; `Moment.Read.p` divides by the total `ρ`-mass, so their common scale does not reach the
normalised read. -/
noncomputable def contactRead (N : ℕ) : Moment.Read N where
  ρ := fun d => if d = 0 then 1 else 0
  hρ := fun d => by split <;> norm_num
  hpos := by simp

theorem contactRead_sum (N : ℕ) : ∑ d, (contactRead N).ρ d = 1 := by
  show ∑ d : Fin (N + 1), (if d = 0 then (1 : ℝ) else 0) = 1
  simp

/-- The contact read's far share vanishes at every aperture and every cut: the only lag carrying
weight has circle lag `0`, so it lies outside `farSet N m`.

DERIVED: `0` is the asserted value of the far share, a sum over an index set on which `ρ` is zero. -/
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

/-- The hypotheses of `circ_moment_le_of_envelope` are satisfiable. At every aperture `N` the
contact read's far share is bounded by the constant envelope `fun _ => 0`, that envelope's weighted
family is summable, and the moment bound it yields is `0`. The statement is about `contactRead`, an
abstract `Moment.Read N`; no Wilson observable appears in it.

DERIVED: `0` is the value of the envelope and hence also the bound on the moment; `2` and `1` form
the layer-cake weight `2m + 1`; the exponent `2` is the moment's own power. -/
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

/-- For `m ≤ k`, the far share of `Substrate.antipodeRead k` at cut `m` is `1`: all its weight sits
at the antipode, whose circle lag `Substrate.circLag_antipode` places strictly beyond every such cut.
`Substrate.antipodeRead_sum` supplies the normalisation.

DERIVED: `1` is the asserted value of the far share, the whole weight of a normalised read. -/
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

/-- Three conjuncts about the summability hypothesis of `circ_moment_le_of_envelope`. First: any
envelope `a` with `farShare (Substrate.antipodeRead k) m ≤ a m` for all `m ≤ k` satisfies `1 ≤ a m`
at every `m`, by `antipodeRead_farShare` on the diagonal `k = m`. Second: the constant envelope
`a ≡ 1` has a non-summable weighted family, since `(2m+1)·1` does not tend to zero. Third: for every
`B` some aperture carries a `Moment.Read` whose circular second moment exceeds `B`; this conjunct is
`Substrate.rp_alone_leaves_moment_unbounded` and quantifies over `Moment.Read` families, naming
neither the antipodal family nor any Wilson observable.

DERIVED: `1` in `(1 : ℝ) ≤ a m` is the whole weight of a normalised read, the value the antipodal far
share takes. `2` and `1` form the layer-cake weight `2m + 1`, and the following `1` is the constant
envelope it is applied to. The exponent `2` is the moment's own power. -/
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

The near lags need no hypothesis: `farShare ≤ 1` caps their contribution to the layer cake by `m₀²`,
whatever the correlation does there. An envelope is therefore a statement about the profile beyond a
fixed cut, and the cut is a parameter of the criterion. -/

/-- A tail envelope suffices. The hypothesis `ha` constrains `farShare R m` only for `m₀ ≤ m`, and
the conclusion bounds the circular second moment by `m₀² + ∑' m, (2m+1)·a m`. The layer cake's near
block is bounded by `∑_{m < m₀} (2m+1) = m₀²` using `farShare_le_one` and `sum_range_odd` alone; the
far block is compared against the tsum.

DERIVED: `0` in `ha0` is the sign condition on the envelope. `2` and `1` form the layer-cake weight
`2m + 1`, in the summability hypothesis and in the tsum. The exponent `2` on the moment is its own
power; the exponent `2` on `m₀` comes from `sum_range_odd` at `m₀`, the largest value the near block
can take. -/
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

/-- A tail envelope whose cut `m₀` is fixed uniformly in aperture and coupling yields
`∃ B, ∀ N β, d2At N β ≤ B`. Below the cut nothing is assumed. The witness supplied for `B` is
`m₀² + ∑' m, (2m+1)·a m`, from `circ_moment_le_of_tail_envelope`.

DERIVED: `0` in `ha0` is the sign condition on the envelope; `2` and `1` form the layer-cake weight
`2m + 1`. The cut `m₀` is a parameter. -/
theorem substrate_of_tail_envelope (m₀ : ℕ) (a : ℕ → ℝ)
    (ha0 : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * a m))
    (ha : ∀ (N : ℕ) (β : ℝ) (m : ℕ), m₀ ≤ m → farShare (MassGap.readYMAt N β) m ≤ a m) :
    ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B :=
  ⟨(m₀ : ℝ) ^ 2 + ∑' m : ℕ, (2 * (m : ℝ) + 1) * a m, fun N β =>
    circ_moment_le_of_tail_envelope (MassGap.readYMAt N β) m₀ a ha0 (ha N β) hs⟩

#print axioms substrate_of_tail_envelope

/-! ### The aperture half and the coupling half

The hypothesis carries two quantifiers, `∀ N` and `∀ β`. Splitting them gives:

* the aperture half, at one coupling — `∃ B, ∀ N, d2At N β ≤ B`, with `B` bound inside the
  quantifier over couplings and so free to depend on `β`;
* the coupling half — that those `B` are bounded over `β`, which is the hypothesis itself.

The aperture half follows from the hypothesis (`aperture_uniform_of_substrate`) and is discharged by
a per-`β` envelope (`aperture_uniform_of_share_envelope`). The theorems below separate the two on
abstract `Moment.Read` families: `sepRead` is bounded in the aperture at each coupling by a bound
that grows without limit in the coupling, so `(∀ β, ∃ B, ∀ N, …)` does not imply `(∃ B, ∀ N β, …)`
for `Moment.Read` families. That is the shape of
`Substrate.substrate_bound_needs_more_than_positivity`, one quantifier up. It quantifies over
`sepRead`, not over `readYMAt`. -/

/-- The lag index at half the period, as an element of `Fin (N + 1)` at any aperture.
`circLag_midLag` computes its circle lag as `(N + 1) / 2`.

DERIVED: `1` is the offset in `Fin (N + 1)` and the period `N + 1`; `2` is the halving, so
`(N + 1) / 2` is the largest value `circLag` attains on this circle. -/
def midLag (N : ℕ) : Fin (N + 1) := ⟨(N + 1) / 2, by omega⟩

theorem circLag_midLag (N : ℕ) : Moment.circLag (midLag N) = (N + 1) / 2 := by
  have hv : ((midLag N : Fin (N + 1)) : ℕ) = (N + 1) / 2 := rfl
  unfold Moment.circLag
  rw [hv]
  omega

/-- The read whose `ρ` is the indicator of `midLag N`: all weight at half the period, at any
aperture. `Substrate.antipodeRead` is the same read at odd `N`; `midRead` is defined at every `N`,
which is what a family indexed by `N` needs. `midRead_moment` computes its circular second moment as
`((N + 1) / 2)²`.

DERIVED: `1` and `0` are the two values of the indicator; `Moment.Read.p` divides by the total
`ρ`-mass, so their common scale does not reach the normalised read. -/
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

/-- The contact read's circular second moment is `0` at every aperture, by `circ_moment_eq_layer`
and `contactRead_farShare`.

DERIVED: the exponent `2` is the moment's own power; `0` is the asserted value of the moment, every
term of the layer cake vanishing. -/
theorem contactRead_moment (N : ℕ) :
    ∑ d, (contactRead N).p d * (Moment.circLag d : ℝ) ^ 2 = 0 := by
  rw [circ_moment_eq_layer]
  refine Finset.sum_eq_zero (fun m _ => ?_)
  rw [contactRead_farShare]
  ring

/-- A `Moment.Read N` indexed by aperture and coupling: `midRead N` while `(N : ℝ) ≤ β`, and
`contactRead N` afterwards. At a fixed `β` only finitely many apertures carry weight away from lag
zero, so the moments are bounded there (`sepRead_moment_le`); over couplings they are not
(`sepRead_moment_unbounded`).

DERIVED: no numeral appears in the statement. The switch is the comparison `(N : ℝ) ≤ β`; any
strictly increasing switch gives a family with the same two properties. -/
noncomputable def sepRead (N : ℕ) (β : ℝ) : Moment.Read N :=
  if (N : ℝ) ≤ β then midRead N else contactRead N

/-- The circular second moment of `sepRead N β` is at most `((β + 1)/2)²`, a cap depending on `β`
and not on `N`. On the `midRead` branch it follows from `midRead_moment` together with `(N : ℝ) ≤ β`;
on the `contactRead` branch the moment is `0`.

DERIVED: the exponent `2` on the moment is its own power. In `((β + 1)/2)²` the `1` and the inner `2`
come from `circLag (midLag N) = (N + 1)/2`, with `N` replaced using `(N : ℝ) ≤ β`; the outer exponent
`2` squares that lag. -/
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

/-- The two halves separated on the `sepRead` family. The first conjunct: at every coupling the
circular second moments of `sepRead N β` are bounded in the aperture, by `sepRead_aperture_bounded`.
The second: no single `B` bounds them over all apertures and couplings, by
`sepRead_moment_unbounded`. So `(∀ β, ∃ B, ∀ N, …)` does not imply `(∃ B, ∀ N β, …)` for
`Moment.Read` families.

The statement quantifies over `sepRead`, an abstract family of `Moment.Read`s. It names no Wilson
observable, and `d2At` does not occur in it.

DERIVED: the exponent `2` in each conjunct is the moment's own power. -/
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

/-- The aperture half follows from the substrate hypothesis: given `∃ B, ∀ N β, d2At N β ≤ B` and
any `β`, the same `B` bounds `d2At N β` over all `N`.

DERIVED: no numeral appears in the statement; the `2` in `d2At` belongs to that definition's name. -/
theorem aperture_uniform_of_substrate (h : ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B) (β : ℝ) :
    ∃ B : ℝ, ∀ N : ℕ, MassGap.d2At N β ≤ B := by
  obtain ⟨B, hB⟩ := h
  exact ⟨B, fun N => hB N β⟩

/-- The aperture half at one coupling, from an envelope assumed at that coupling only. Here `β` is
bound outside the envelope `a`, so `a` may depend on it; `substrate_of_share_envelope` is the same
statement with `a` bound outside the quantifier over couplings. The witness supplied for `B` is
`∑' m, (2m+1)·a m`, from `circ_moment_le_of_envelope`.

DERIVED: `0` in `ha0` is the sign condition on the envelope; `2` and `1` form the layer-cake weight
`2m + 1`. -/
theorem aperture_uniform_of_share_envelope (β : ℝ) (a : ℕ → ℝ)
    (ha0 : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * a m))
    (ha : ∀ (N : ℕ) (m : ℕ), farShare (MassGap.readYMAt N β) m ≤ a m) :
    ∃ B : ℝ, ∀ N : ℕ, MassGap.d2At N β ≤ B :=
  ⟨∑' m : ℕ, (2 * (m : ℝ) + 1) * a m, fun N =>
    circ_moment_le_of_envelope (MassGap.readYMAt N β) a ha0 (ha N) hs⟩

#print axioms aperture_uniform_of_share_envelope


/-! ### The exponent is exactly two

`square_envelope_not_summable` shows the criterion cannot be entered at exponent `2`. The family
below goes further: at exponent `2` the conclusion itself fails over `Moment.Read` families. Its far
share obeys a square envelope whose constant is free of the aperture, and its circular second moments
are unbounded. An envelope condition therefore carries the conclusion above exponent `2` and not at
it. -/

/-- The telescoping weight: `1/j² − 1/(j+1)²` for `j ≥ 1`, and `0` at `j = 0`. It is nonnegative
(`telWeight_nonneg`) and its partial sums telescope (`telWeight_sum`).

DERIVED: `0` in `j = 0` is the index excluded from the formula, where `1/j²` is undefined, and the
`0` after it is the value taken there. `1` is the numerator of each term; the exponents `2` are the
square whose increment this weight is; `1` in `(j : ℝ) + 1` is the index shift between the two
terms. -/
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

/-- `∑_{j < M+1} telWeight j = 1 − 1/(M+1)²`, by induction on `M`.

DERIVED: `1` in `Finset.range (M + 1)` makes the range reach `M` inclusive. On the right, the leading
`1` is the first surviving term `1/1²` of the telescope, the `1` in the numerator and the `1` in
`(M : ℝ) + 1` are the last surviving term, and `2` is its exponent. -/
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

/-- A read carrying weight `telWeight j` at lag index `j` for `j ≤ k + 1` and nothing beyond. On
that range the circle lag equals the lag index, so sums against `circLag` collapse to
`Finset.range (k + 2)` (`squareRead_sum_eq`) and the far share telescopes
(`squareRead_farShare_le`). Positivity of the total mass is witnessed by the weight at index `1`,
which is `3/4`.

DERIVED: `2` and `1` in `Moment.Read (2 * k + 1)` fix the aperture index at `2k + 1`, so the period
is `2k + 2`; the family is defined at those apertures only. `1` in `k + 1` is the antipodal index of
that period, the largest lag at which the circle distance still equals the index. `0` is the weight
given outside that range. The `3 / 4` the `hpos` field computes with is `telWeight 1`, the weight at
index `1`, which is what witnesses the positive total mass. -/
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

/-- For any `g`, the `ρ`-weighted sum of `g ∘ circLag` over the whole period equals
`∑_{j < k+2} telWeight j * g j`: outside `j ≤ k + 1` the weight is zero, and inside it
`circLag d = d`.

DERIVED: `2` and the first `1` in `Fin (2 * k + 1 + 1)` are the aperture index `2k + 1`; the second
`1` is the `Fin` offset, so the period is `2k + 2`. `2` in `Finset.range (k + 2)` makes the range
cover indices `0` through `k + 1`, which is where `squareRead k` puts weight. -/
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

/-- The total `ρ`-mass of `squareRead k` is `1 − 1/(k+2)²`, from `squareRead_sum_eq` at the constant
function and `telWeight_sum (k + 1)`. `squareRead_mass_ge` and `squareRead_mass_le` bracket it
between `3/4` and `1`.

DERIVED: the leading `1` is the first surviving term `1/1²` of the telescope. `1` in the numerator
and `2` in `(k : ℝ) + 2` are the last surviving term, indexed by the first position beyond the
support; `2` is its exponent. -/
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

/-- For any read, the far share equals the `ρ`-mass on `farSet N m` divided by the total `ρ`-mass,
by unfolding `Moment.Read.p` termwise.

DERIVED: no numeral appears in the statement. -/
theorem farShare_eq_rho {N : ℕ} (R : Moment.Read N) (m : ℕ) :
    farShare R m = (∑ d ∈ farSet N m, R.ρ d) / (∑ d, R.ρ d) := by
  rw [farShare, Finset.sum_div]
  rfl

/-- The telescoping profile carries at most `1/(m+1)²` beyond a cut `m`. The proof splits
`Finset.range (k + 2)` at `m`, applies `telWeight_sum` to both parts when `m + 1 ≤ k + 2`, and
observes that the far part is empty otherwise.

DERIVED: `2` in `Finset.range (k + 2)` is the index range of `squareRead k`'s support. `1` and `0`
are the two values of the indicator selecting lags beyond the cut. On the right, `1` is the numerator
of the bound, `1` in `(m : ℝ) + 1` is the smallest index beyond the cut, and `2` is the exponent of
the square profile this weight saturates. -/
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

/-- `farShare (squareRead k) m ≤ (4/3)/(m+1)²` at every aperture index `k` and every cut `m`. The
bound combines `tel_far_le`, which caps the far `ρ`-mass by `1/(m+1)²`, with `squareRead_mass_ge`,
which keeps the total `ρ`-mass at or above `3/4`.

DERIVED: `4/3` is the reciprocal of the mass lower bound `3/4` of `squareRead_mass_ge`, which is
`telWeight 1 = 1 − 1/2²`. `1` in `(m : ℝ) + 1` is the smallest lag beyond the cut, and `2` is the
exponent of the square envelope. -/
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

/-- The circular second moment of `squareRead k` is at least `(∑_{j < k+2} 1/(j+1)) − 1`. Termwise
`telWeight j · j² = (2j+1)/(j+1)²`, which dominates `1/(j+1)` for `j ≥ 1`; the `j = 0` term is
carried by the subtracted `1`, and `squareRead_mass_le` turns the `ρ`-weighted sum into a lower bound
for the `p`-weighted one.

DERIVED: `2` in `Finset.range (k + 2)` is the index range of the support; `1` in `(j : ℝ) + 1` is the
harmonic index shift. The subtracted `1` covers the `j = 0` term, where `telWeight 0 = 0` while
`1/(0+1) = 1`. The exponent `2` on the right is the moment's own power. -/
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

/-- Two conjuncts at exponent `2`. First, the far share of `squareRead k` stays under
`(4/3)/(m+1)²` at every aperture index and every cut, with a constant free of the aperture
(`squareRead_farShare_le`). Second, its circular second moments exceed every `B`
(`squareRead_moment_ge` together with the divergence of `∑ 1/(i+1)`). So an envelope at exponent `2`
does not bound the circular second moment over a `Moment.Read` family, while
`circ_moment_le_of_envelope` fed a cubic envelope does.

Both conjuncts are about `squareRead`, a family of `Moment.Read`s at aperture index `2k + 1`.
Neither mentions `readYMAt`, `d2At` or any Wilson observable.

The mechanism is the layer cake: a square share profile has weighted total
`∑ (2m+1)/(m+1)² ≍ ∑ 1/(m+1)`, the harmonic series.

DERIVED: `4/3` is the reciprocal of the mass bound `3/4` of `squareRead_mass_ge`. `1` in
`(m : ℝ) + 1` is the smallest lag beyond the cut, and the `2` above it is the envelope's exponent.
The remaining `2` is the moment's own power. -/
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


/-! ### The constants of the aperture argument, in order -/

/-- `3/4 < 3^{-1/4} < 19/25`, from `(3^{-1/4})⁴ = 1/3` and the strict monotonicity of the fourth
power on the nonnegatives. Each side is proved by contradiction, raising the candidate bracket to the
fourth power.

DERIVED: `3` is the base and `-1/4` the exponent of `3^{-1/4}`, which is `exp (-κ₀)` for
`κ₀ = (log 3)/4`; `1` and `4` are the numerator and denominator of that exponent. `3/4` and `19/25`
are the two rational brackets, exhibited here and consumed by `substrateThreshold_lt_ceiling`. -/
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

/-- For `0 < y < 1`, `Real.arccos y < π/2 − y`. From `Real.arccos y = π/2 − Real.arcsin y` together
with `Real.sin_lt`, which gives `y = sin (arcsin y) < arcsin y`.

DERIVED: `0` and `1` are the endpoints of the open interval the hypotheses place `y` in; `2` in `π/2`
is the halving of `π` in the `arccos`/`arcsin` identity. -/
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

/-- `MassGap.substrateThreshold < (1 − 3^{−1/4}) / 8`.

`Moment.Read.substrate_lt_of_tension_lt_floor` produces a substrate ratio below the right-hand
number; `Complete.confinement_at_of_substrate_sharp` consumes a ratio below the left-hand one. This
 theorem places the left one strictly below the right.

The proof unfolds `MassGap.substrateThreshold`, bounds `arccos (3^{−1/4})` above by `0.825` using
`arccos_lt_half_pi_sub` and `rpow_bracket`, squares that to `0.69`, and bounds `(2π)²` below by `36`
using `Real.pi_gt_three`; `Real.pi_lt_d2` supplies the upper bracket on `π`.

DERIVED: `1` and the base `3` with exponent `-1/4` form `1 − 3^{−1/4}`, the numerator of the ceiling
that `Moment.Read.substrate_lt_of_tension_lt_floor` produces, and `1` and `4` are the numerator and
denominator of that exponent. `8` is that ceiling's divisor. `MassGap.substrateThreshold` is
`arccos(3^{−1/4})²/(2π)²` and contributes no literal of its own to this statement. -/
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

/-- The three constants of the aperture argument, in order:

    2(1 − 3^{−1/4})/(2π)²  ≤  substrateThreshold  <  (1 − 3^{−1/4})/8

The left inequality is `MassGap.taylor_le_substrateThreshold`, which places the origin-tangent
number below `substrateThreshold`; the right is `substrateThreshold_lt_ceiling`. The outer two differ
by the factor `π²/4`.

DERIVED: the leading `2` is the numerator of the origin-tangent bound
`MassGap.taylor_le_substrateThreshold` supplies; the `2` in `(2 * Real.pi)` is the period of the
angle it is divided by, and the exponent `2` squares that period. `1` and the base `3` with exponent
`-1/4` form `1 − 3^{−1/4}` on both sides, with `1` and `4` the numerator and denominator of that
exponent. `8` is the divisor of the ceiling. -/
theorem aperture_constants_ordered :
    2 * (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / (2 * Real.pi) ^ 2 ≤ MassGap.substrateThreshold ∧
      MassGap.substrateThreshold < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8 :=
  ⟨MassGap.taylor_le_substrateThreshold, substrateThreshold_lt_ceiling⟩

#print axioms aperture_constants_ordered

end MassGap.ContactDominance
