import Mathlib
import MassGap.ContactDominance

/-!
# MassGap.ShareEnvelope — condensed far shares, and a contact-relative power law

Two sufficient conditions for `∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B`, and one equivalence.

## The condensation

`farShare R m` is the probability a read puts beyond circle distance `m`. It is antitone in the cut
with no hypothesis beyond `Moment.Read`'s own nonnegativity (`farShare_antitone`), which brackets the
layer cake from both sides by its condensation onto the cuts `cut m₀ j` — `m₀`, `2 * m₀ + 1`,
`4 * m₀ + 3`, … , the cuts at which `m + 1` has doubled `j` times:

    3 * (m₀+1)^2 * ∑_{j<J} 4^j * farShare R (cut m₀ (j+1))          (`condensed_le_layer`)
      ≤ ∑_{m ≤ cut m₀ J} (2m+1) * farShare R m
      ≤ (m₀+1)^2 * (1 + 3 * ∑_{j<J} 4^j * farShare R (cut m₀ j))    (`layer_le_condensed`)

`substrate_iff_dyadic_shares` reads off the equivalence: for every `m₀`,

    (∃ B, ∀ N β, d2At N β ≤ B) ↔ (∃ S, ∀ N β J, ∑_{j<J} 4^j * farShare (readYMAt N β) (cut m₀ j) ≤ S).

This is Cauchy condensation for the weight `2m + 1`, exact because that weight is the discrete
derivative of the square: `4^j` is `((m₀+1)2^{j+1})^2 - ((m₀+1)2^j)^2` over `3 (m₀+1)^2`.

## The doubling contraction

Bounding the condensed sum by a geometric series gives `circ_moment_le_of_share_doubling`:

    farShare R (2m+1) ≤ θ * farShare R m  for m ≥ m₀, with 0 ≤ θ < 1/4
      ⟹  ∑ d, p d * circLag d ^ 2 ≤ (m₀+1)^2 * (1 + 3/(1 - 4θ))

uniformly in the aperture, hence `substrate_of_share_doubling`, `confinement_of_share_doubling` and
`yang_mills_of_share_doubling`. Nothing is assumed below `m₀`: `farShare ≤ 1` caps the near block at
`(m₀+1)^2` on its own, and `layer_partial_le` runs the finite induction in one pass.

The threshold `1/4` corresponds exactly to `ContactDominance`'s exponent threshold `s > 2`: on a
power profile `a m = C (m+1)^(-s)` the ratio `a (2m+1) / a m` is identically `2^(-s)`. That exactness
is what fixes the step as `m ↦ 2m + 1` rather than `m ↦ 2m`; under the latter the contraction of a
power would be `((m+1)/(2m+1))^s`, larger than `2^(-s)` at every finite `m`.

`farShare_doubling_iff_tail_mass` divides the normalisation out of both sides, so
`substrate_of_tail_mass_doubling` states the same condition on `wilsonCorrAt` alone, with no
normalisation, envelope or lower bound on `∑ d, wilsonCorrAt N β d`. `scaleRead`,
`farShare_scale_invariant`, `circ_moment_scale_invariant` and `mass_floor_is_not_scale_free` compare
that with `ContactDominance.circ_moment_le_of_rho_envelope`, which carries a floor `c ≤ ∑ ρ` with
`c > 0`: the conclusion and the share are invariant under `ρ ↦ t * ρ` and the floor is not.

## The contact-relative power law

`substrate_of_contact_relative_decay` takes

    wilsonCorrAt N β d ≤ C * wilsonCorrAt N β 0 / (circLag d) ^ 4   for circLag d ≥ m₀

uniformly in aperture and coupling. No normalisation, total mass, floor or rate appears in it:
`contact_le_total` gives `ρ 0 ≤ ∑ ρ` from nonnegativity alone, so the contact term normalises from
inside, and `contact_relative_scale_invariant` makes the condition invariant under `ρ ↦ t * ρ`
exactly as the conclusion is. `p_le_one` caps the near lags, so nothing is assumed below the cut.
`substrate_of_inverse_eighth_decay` is the same at exponent `8`, the exponent the short-distance form
of the connected `F²` correlation carries; `ρ(0)` and `ρ(d)` carry the same power of the coupling, so
the ratio has no coupling in it at leading order.

`farShare_le_of_contact_relative` converts the law into the far-share envelope
`farShare R m ≤ (2C/3)/m^3`, summed by telescoping (`quartic_step`, `inv_quartic_tail`) rather than
by an integral comparison, so the constant is exact at every finite aperture. `cubicShare` and
`substrate_of_contact_relative_share` route the same reduction through
`ContactDominance.substrate_of_tail_envelope`.

## Scope and the sharpness statements

* `substrate_iff_dyadic_shares` is an equivalence; the doubling contraction and the contact-relative
  law are sufficient conditions. The contraction is strictly stronger than
  `ContactDominance.substrate_of_tail_envelope`, and `contact_relative_is_strictly_stronger`
  exhibits `Substrate.tailRead`, whose moment is at most `1` at every aperture and which admits no
  `(C, m₀)` at exponent `4`.
* Both conditions still have to hold uniformly in the coupling:
  `ContactDominance.aperture_uniformity_does_not_give_coupling_uniformity` applies, and a contraction
  or a constant depending on `β` does not give the hypothesis. What each form fixes is the shape —
  a power law with no rate in it, which is the side of
  `Substrate.bounded_moment_does_not_give_geometric_decay` the substrate hypothesis uses.
* `doubling_nonvacuous` and `contact_relative_nonvacuous`: `contactRead` meets each condition at
  `θ = 0` and `C = 0` with moment zero, so neither is an implication out of an unsatisfiable
  hypothesis.
* `doubling_load_bearing` and `contact_relative_load_bearing`: `ContactDominance.midRead` admits no
  `θ < 1` at any cut and no `C` at any cut, and its moments exceed every `B`. The second also shows
  what the contact-relative condition asks for that a share condition does not — weight at short
  lags.
* `quarter_doubling_is_not_enough` and `quarter_doubling_gives_no_bound`: `squareRead` contracts by
  exactly `1/4` at every cut and aperture with unbounded moments, so `θ < 1/4` is the hypothesis and
  not a margin. It is the same family as `ContactDominance.square_share_is_not_enough`, since
  `(m+1)^(-s)` contracts by exactly `2^(-s)` across `m ↦ 2m + 1`.
* `cubic_contact_relative_is_not_enough` and `cubic_contact_relative_gives_no_bound`: `cubeRead`
  obeys the contact-relative condition at exponent `3` with constant `1` at every aperture and has
  unbounded moments. The threshold exponent is `3` — the moment weights by `k ^ 2` and the circle lag
  has multiplicity two, so the weighted total is `∑ k^2 * C / k^s`, convergent exactly when `s > 3`.
  It is one above the share's threshold `2` because the share has already absorbed a summation.
* The axiom footprint of the `readYMAt` statements carries `wilson_reflection_positive_at`, from
  which that read is constructed.
-/

namespace MassGap.ShareEnvelope

open MassGap.Moment MassGap.ContactDominance

/-! ### The far share is antitone in the cut -/

/-- `farSet N m' ⊆ farSet N m` whenever `m ≤ m'`: raising the cut shrinks the far set. Both are
filters of `Finset.univ` by `m < Moment.circLag d`, so `omega` settles the membership.

DERIVED: no numeral appears in the statement. -/
theorem farSet_subset {N : ℕ} {m m' : ℕ} (h : m ≤ m') : farSet N m' ⊆ farSet N m := by
  intro d hd
  simp only [farSet, Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
  omega

/-- `farShare R m' ≤ farShare R m` whenever `m ≤ m'`, by `Finset.sum_le_sum_of_subset_of_nonneg` on
`farSet_subset` with `Moment.Read.p_nonneg`.

Scope: no hypothesis beyond the `Moment.Read` interface. It is what lets the condensation below read
the profile along a sparse sequence of cuts.

DERIVED: no numeral appears in the statement. -/
theorem farShare_antitone {N : ℕ} (R : Moment.Read N) {m m' : ℕ} (h : m ≤ m') :
    farShare R m' ≤ farShare R m :=
  Finset.sum_le_sum_of_subset_of_nonneg (farSet_subset h) (fun d _ _ => R.p_nonneg d)

#print axioms farShare_antitone

/-! ### The cut sequence

`cut m₀ j` doubles `m + 1` starting from `m₀`: `cut m₀ 0 = m₀` and `cut m₀ (j+1) = 2 * cut m₀ j + 1`,
so `cut m₀ j + 1 = (m₀ + 1) * 2 ^ j`. Everything below is stated against `cut`, so no natural
subtraction appears. -/

/-- The sequence with `cut m₀ 0 = m₀` and `cut m₀ (j + 1) = 2 * cut m₀ j + 1`, so that
`cut m₀ j + 1 = (m₀ + 1) * 2 ^ j` (`cut_succ_cast`): the `j`-th doubling of `m₀ + 1`, less one.

DERIVED: no numeral appears in the type. In the body, `0` is the base index and `1` its value's
offset; `2` and the trailing `1` are the step `m ↦ 2 * m + 1`, the cut at which `m + 1` doubles,
since `(2 * m + 1) + 1 = 2 * (m + 1)`. -/
def cut (m₀ : ℕ) : ℕ → ℕ
  | 0 => m₀
  | j + 1 => 2 * cut m₀ j + 1

/-- `(cut m₀ j : ℝ) + 1 = ((m₀ : ℝ) + 1) * 2 ^ j`, by induction on `j`. This is the identity the
name `cut` refers to: the successor of the cut doubles at each step.

DERIVED: `1` occurs twice, as the successor on each side — the quantity that doubles; `2` is the
base of the doubling. -/
theorem cut_succ_cast (m₀ : ℕ) (j : ℕ) :
    ((cut m₀ j : ℕ) : ℝ) + 1 = ((m₀ : ℝ) + 1) * 2 ^ j := by
  induction j with
  | zero =>
      have hval : cut m₀ 0 = m₀ := rfl
      rw [hval]
      norm_num
  | succ i ih =>
      have hval : cut m₀ (i + 1) = 2 * cut m₀ i + 1 := rfl
      rw [hval, pow_succ]
      push_cast
      nlinarith [ih]

/-- `m₀ ≤ cut m₀ j` at every `j`: the sequence never falls below its start.

DERIVED: no numeral appears in the statement. -/
theorem le_cut (m₀ : ℕ) (j : ℕ) : m₀ ≤ cut m₀ j := by
  induction j with
  | zero => exact le_refl _
  | succ i ih =>
      have hval : cut m₀ (i + 1) = 2 * cut m₀ i + 1 := rfl
      omega

/-- `cut m₀ j < cut m₀ (j + 1)`: the sequence is strictly increasing, since the successor step is
`m ↦ 2 * m + 1`.

DERIVED: `1` is the index step. -/
theorem cut_lt_succ (m₀ : ℕ) (j : ℕ) : cut m₀ j < cut m₀ (j + 1) := by
  have hval : cut m₀ (j + 1) = 2 * cut m₀ j + 1 := rfl
  omega

/-- `j ≤ cut m₀ j` at every `j`: the sequence outruns its own index, so every aperture is passed by
some cut. `layer_le_full` uses this to reduce a partial layer cake to the full one.

DERIVED: no numeral appears in the statement. -/
theorem self_le_cut (m₀ : ℕ) (j : ℕ) : j ≤ cut m₀ j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ i ih =>
      have hval : cut m₀ (i + 1) = 2 * cut m₀ i + 1 := rfl
      omega

/-- If `0 ≤ θ` and `a (2 * m + 1) ≤ θ * a m` at every `m ≥ m₀`, then `a (cut m₀ j) ≤ θ ^ j * a m₀`.
Induction on `j`, the contraction applying at `cut m₀ j` because `le_cut` puts it above `m₀`.

DERIVED: `0` is the lower bound on the contraction factor `θ`, which is what lets the induction
multiply by it; `2` and `1` are the doubling step `m ↦ 2 * m + 1`. -/
theorem le_pow_of_doubling {a : ℕ → ℝ} {m₀ : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hdb : ∀ m, m₀ ≤ m → a (2 * m + 1) ≤ θ * a m) (j : ℕ) :
    a (cut m₀ j) ≤ θ ^ j * a m₀ := by
  induction j with
  | zero =>
      have hval : cut m₀ 0 = m₀ := rfl
      rw [hval]
      simp
  | succ i ih =>
      have hval : cut m₀ (i + 1) = 2 * cut m₀ i + 1 := rfl
      rw [hval]
      calc a (2 * cut m₀ i + 1) ≤ θ * a (cut m₀ i) := hdb _ (le_cut m₀ i)
        _ ≤ θ * (θ ^ i * a m₀) := mul_le_mul_of_nonneg_left ih hθ0
        _ = θ ^ (i + 1) * a m₀ := by ring

/-! ### The weight `2m + 1` summed over a block -/

/-- `∑ m ∈ Finset.Ico A B, (2 * m + 1) = B ^ 2 - A ^ 2` for `A ≤ B`: the weight `2 * m + 1` is the
discrete derivative of the square, so a block's weight telescopes exactly.

DERIVED: `2` occurs three times — the coefficient in the weight, and the exponent on each of the two
endpoints; `1` is the offset in the weight. -/
theorem sum_Ico_odd {A B : ℕ} (h : A ≤ B) :
    ∑ m ∈ Finset.Ico A B, (2 * (m : ℝ) + 1) = (B : ℝ) ^ 2 - (A : ℝ) ^ 2 := by
  rw [Finset.sum_Ico_eq_sub _ h, sum_range_odd, sum_range_odd]

/-- `((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j`: squaring the doubling gives the block weight's growth factor.

DERIVED: `2` occurs twice, as the base of the doubling and as the exponent squaring it; `4` is the
resulting base, which is what the condensed sums below weight by. -/
theorem two_pow_sq (j : ℕ) : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/-! ### The layer cake bracketed by its condensation -/

/-- For an antitone profile bounded by `1`,

    ∑ m ∈ Finset.range (cut m₀ J + 1), (2 * m + 1) * a m
      ≤ (m₀ + 1) ^ 2 * (1 + 3 * ∑ j ∈ Finset.range J, 4 ^ j * a (cut m₀ j)).

The near block `m ≤ m₀` costs `(m₀ + 1) ^ 2` from `a ≤ 1` alone (`sum_Ico_odd`); the block between
consecutive cuts has weight exactly `3 * (m₀ + 1) ^ 2 * 4 ^ j` and profile at most `a (cut m₀ j)`
there, by antitonicity.

DERIVED: `1` occurs five times — the bound on `a`, the `+ 1` making the range inclusive, the offset
in the weight `2 * m + 1`, the successor in `(m₀ + 1)`, and the near block's share of the bracket.
`2` occurs twice, as the coefficient in the weight and as the exponent on `(m₀ + 1)`, both from
`sum_Ico_odd`. `3` is `4 - 1`, the weight of one block as a multiple of the block before it; `4` is
that growth factor, `two_pow_sq`'s. -/
theorem layer_le_condensed {a : ℕ → ℝ} {m₀ : ℕ}
    (ha1 : ∀ m, a m ≤ 1) (hanti : ∀ m m' : ℕ, m ≤ m' → a m' ≤ a m) (J : ℕ) :
    ∑ m ∈ Finset.range (cut m₀ J + 1), (2 * (m : ℝ) + 1) * a m
      ≤ ((m₀ : ℝ) + 1) ^ 2 * (1 + 3 * ∑ j ∈ Finset.range J, (4 : ℝ) ^ j * a (cut m₀ j)) := by
  induction J with
  | zero =>
      have hcut : cut m₀ 0 = m₀ := rfl
      rw [hcut]
      have hterm : ∀ m ∈ Finset.range (m₀ + 1),
          (2 * (m : ℝ) + 1) * a m ≤ (2 * (m : ℝ) + 1) := by
        intro m _
        calc (2 * (m : ℝ) + 1) * a m ≤ (2 * (m : ℝ) + 1) * 1 :=
              mul_le_mul_of_nonneg_left (ha1 m) (by positivity)
          _ = (2 * (m : ℝ) + 1) := mul_one _
      have hsum : ∑ m ∈ Finset.range (m₀ + 1), (2 * (m : ℝ) + 1) = ((m₀ : ℝ) + 1) ^ 2 := by
        rw [sum_range_odd]
        push_cast
        ring
      calc ∑ m ∈ Finset.range (m₀ + 1), (2 * (m : ℝ) + 1) * a m
          ≤ ∑ m ∈ Finset.range (m₀ + 1), (2 * (m : ℝ) + 1) := Finset.sum_le_sum hterm
        _ = ((m₀ : ℝ) + 1) ^ 2 := hsum
        _ = ((m₀ : ℝ) + 1) ^ 2 * (1 + 3 * ∑ j ∈ Finset.range 0, (4 : ℝ) ^ j * a (cut m₀ j)) := by
              simp
  | succ J ih =>
      have hle : cut m₀ J + 1 ≤ cut m₀ (J + 1) + 1 := by
        have := cut_lt_succ m₀ J
        omega
      have hsplit : ∑ m ∈ Finset.range (cut m₀ (J + 1) + 1), (2 * (m : ℝ) + 1) * a m
          = (∑ m ∈ Finset.range (cut m₀ J + 1), (2 * (m : ℝ) + 1) * a m)
            + ∑ m ∈ Finset.Ico (cut m₀ J + 1) (cut m₀ (J + 1) + 1), (2 * (m : ℝ) + 1) * a m := by
        simp only [Finset.range_eq_Ico]
        rw [← Finset.sum_Ico_consecutive (fun m : ℕ => (2 * (m : ℝ) + 1) * a m)
          (Nat.zero_le (cut m₀ J + 1)) hle]
      have hblock : ∑ m ∈ Finset.Ico (cut m₀ J + 1) (cut m₀ (J + 1) + 1),
          (2 * (m : ℝ) + 1) * a m ≤ 3 * ((m₀ : ℝ) + 1) ^ 2 * ((4 : ℝ) ^ J * a (cut m₀ J)) := by
        have hterm : ∀ m ∈ Finset.Ico (cut m₀ J + 1) (cut m₀ (J + 1) + 1),
            (2 * (m : ℝ) + 1) * a m ≤ (2 * (m : ℝ) + 1) * a (cut m₀ J) := by
          intro m hm
          simp only [Finset.mem_Ico] at hm
          have hmono : a m ≤ a (cut m₀ J) := hanti _ _ (by omega)
          exact mul_le_mul_of_nonneg_left hmono (by positivity)
        have hweight : ∑ m ∈ Finset.Ico (cut m₀ J + 1) (cut m₀ (J + 1) + 1), (2 * (m : ℝ) + 1)
            = 3 * (((m₀ : ℝ) + 1) * 2 ^ J) ^ 2 := by
          rw [sum_Ico_odd hle]
          have hA : ((cut m₀ J + 1 : ℕ) : ℝ) = ((m₀ : ℝ) + 1) * 2 ^ J := by
            push_cast
            exact cut_succ_cast m₀ J
          have hB : ((cut m₀ (J + 1) + 1 : ℕ) : ℝ) = ((m₀ : ℝ) + 1) * 2 ^ (J + 1) := by
            push_cast
            exact cut_succ_cast m₀ (J + 1)
          rw [hA, hB, pow_succ]
          ring
        calc ∑ m ∈ Finset.Ico (cut m₀ J + 1) (cut m₀ (J + 1) + 1), (2 * (m : ℝ) + 1) * a m
            ≤ ∑ m ∈ Finset.Ico (cut m₀ J + 1) (cut m₀ (J + 1) + 1),
                (2 * (m : ℝ) + 1) * a (cut m₀ J) := Finset.sum_le_sum hterm
          _ = (∑ m ∈ Finset.Ico (cut m₀ J + 1) (cut m₀ (J + 1) + 1),
                (2 * (m : ℝ) + 1)) * a (cut m₀ J) := by rw [← Finset.sum_mul]
          _ = 3 * (((m₀ : ℝ) + 1) * 2 ^ J) ^ 2 * a (cut m₀ J) := by rw [hweight]
          _ = 3 * ((m₀ : ℝ) + 1) ^ 2 * ((4 : ℝ) ^ J * a (cut m₀ J)) := by
                rw [mul_pow, two_pow_sq]
                ring
      have hgeom : ∑ j ∈ Finset.range (J + 1), (4 : ℝ) ^ j * a (cut m₀ j)
          = (∑ j ∈ Finset.range J, (4 : ℝ) ^ j * a (cut m₀ j))
            + (4 : ℝ) ^ J * a (cut m₀ J) := Finset.sum_range_succ _ _
      rw [hsplit, hgeom]
      nlinarith [ih, hblock]

/-- For a nonnegative antitone profile,

    3 * (m₀ + 1) ^ 2 * ∑ j ∈ Finset.range J, 4 ^ j * a (cut m₀ (j + 1))
      ≤ ∑ m ∈ Finset.range (cut m₀ J + 1), (2 * m + 1) * a m.

On the `j`-th block every index is at most `cut m₀ (j + 1)`, so antitonicity bounds the profile there
from below by its value at the block's far end; the block's weight is exactly
`3 * (m₀ + 1) ^ 2 * 4 ^ j`.

With `layer_le_condensed` this brackets the layer cake by the same condensed sum from both sides,
which is what makes `substrate_iff_dyadic_shares` an equivalence.

DERIVED: `0` is the lower bound on the profile. `3` is `4 - 1`, the weight of one block as a multiple
of the block before it, and `4` is that growth factor. `1` occurs four times — the successor in
`(m₀ + 1)`, the shift `j + 1` to the block's far end, the `+ 1` making the range inclusive, and the
offset in the weight `2 * m + 1`. `2` occurs twice, as the exponent on `(m₀ + 1)` and as the
coefficient in the weight. -/
theorem condensed_le_layer {a : ℕ → ℝ} {m₀ : ℕ}
    (ha0 : ∀ m, 0 ≤ a m) (hanti : ∀ m m' : ℕ, m ≤ m' → a m' ≤ a m) (J : ℕ) :
    3 * ((m₀ : ℝ) + 1) ^ 2 * ∑ j ∈ Finset.range J, (4 : ℝ) ^ j * a (cut m₀ (j + 1))
      ≤ ∑ m ∈ Finset.range (cut m₀ J + 1), (2 * (m : ℝ) + 1) * a m := by
  induction J with
  | zero =>
      have hrhs : (0 : ℝ) ≤ ∑ m ∈ Finset.range (cut m₀ 0 + 1), (2 * (m : ℝ) + 1) * a m :=
        Finset.sum_nonneg (fun m _ => mul_nonneg (by positivity) (ha0 m))
      simpa using hrhs
  | succ J ih =>
      have hle : cut m₀ J + 1 ≤ cut m₀ (J + 1) + 1 := by
        have := cut_lt_succ m₀ J
        omega
      have hsplit : ∑ m ∈ Finset.range (cut m₀ (J + 1) + 1), (2 * (m : ℝ) + 1) * a m
          = (∑ m ∈ Finset.range (cut m₀ J + 1), (2 * (m : ℝ) + 1) * a m)
            + ∑ m ∈ Finset.Ico (cut m₀ J + 1) (cut m₀ (J + 1) + 1), (2 * (m : ℝ) + 1) * a m := by
        simp only [Finset.range_eq_Ico]
        rw [← Finset.sum_Ico_consecutive (fun m : ℕ => (2 * (m : ℝ) + 1) * a m)
          (Nat.zero_le (cut m₀ J + 1)) hle]
      have hweight : ∑ m ∈ Finset.Ico (cut m₀ J + 1) (cut m₀ (J + 1) + 1), (2 * (m : ℝ) + 1)
          = 3 * (((m₀ : ℝ) + 1) * 2 ^ J) ^ 2 := by
        rw [sum_Ico_odd hle]
        have hA : ((cut m₀ J + 1 : ℕ) : ℝ) = ((m₀ : ℝ) + 1) * 2 ^ J := by
          push_cast
          exact cut_succ_cast m₀ J
        have hB : ((cut m₀ (J + 1) + 1 : ℕ) : ℝ) = ((m₀ : ℝ) + 1) * 2 ^ (J + 1) := by
          push_cast
          exact cut_succ_cast m₀ (J + 1)
        rw [hA, hB, pow_succ]
        ring
      have hblock : 3 * ((m₀ : ℝ) + 1) ^ 2 * ((4 : ℝ) ^ J * a (cut m₀ (J + 1)))
          ≤ ∑ m ∈ Finset.Ico (cut m₀ J + 1) (cut m₀ (J + 1) + 1), (2 * (m : ℝ) + 1) * a m := by
        have hterm : ∀ m ∈ Finset.Ico (cut m₀ J + 1) (cut m₀ (J + 1) + 1),
            (2 * (m : ℝ) + 1) * a (cut m₀ (J + 1)) ≤ (2 * (m : ℝ) + 1) * a m := by
          intro m hm
          simp only [Finset.mem_Ico] at hm
          exact mul_le_mul_of_nonneg_left (hanti _ _ (by omega)) (by positivity)
        calc 3 * ((m₀ : ℝ) + 1) ^ 2 * ((4 : ℝ) ^ J * a (cut m₀ (J + 1)))
            = 3 * (((m₀ : ℝ) + 1) * 2 ^ J) ^ 2 * a (cut m₀ (J + 1)) := by
              rw [mul_pow, two_pow_sq]; ring
          _ = (∑ m ∈ Finset.Ico (cut m₀ J + 1) (cut m₀ (J + 1) + 1),
                (2 * (m : ℝ) + 1)) * a (cut m₀ (J + 1)) := by rw [hweight]
          _ = ∑ m ∈ Finset.Ico (cut m₀ J + 1) (cut m₀ (J + 1) + 1),
                (2 * (m : ℝ) + 1) * a (cut m₀ (J + 1)) := by rw [← Finset.sum_mul]
          _ ≤ ∑ m ∈ Finset.Ico (cut m₀ J + 1) (cut m₀ (J + 1) + 1),
                (2 * (m : ℝ) + 1) * a m := Finset.sum_le_sum hterm
      have hgeom : ∑ j ∈ Finset.range (J + 1), (4 : ℝ) ^ j * a (cut m₀ (j + 1))
          = (∑ j ∈ Finset.range J, (4 : ℝ) ^ j * a (cut m₀ (j + 1)))
            + (4 : ℝ) ^ J * a (cut m₀ (J + 1)) := Finset.sum_range_succ _ _
      rw [hsplit, hgeom]
      nlinarith [ih, hblock]

/-- `layer_le_condensed` with the condensed sum evaluated under a doubling contraction: for an
antitone profile bounded by `1` with `0 ≤ θ` and `a (2 * m + 1) ≤ θ * a m` above `m₀`,

    ∑ m ∈ Finset.range (cut m₀ J + 1), (2 * m + 1) * a m
      ≤ (m₀ + 1) ^ 2 * (1 + 3 * ∑ j ∈ Finset.range J, (4 * θ) ^ j).

`le_pow_of_doubling` supplies `a (cut m₀ j) ≤ θ ^ j * a m₀ ≤ θ ^ j`, so each condensed term is at
most `(4 * θ) ^ j`.

DERIVED: `1` occurs six times — the bound on `a`, the offset in the contraction step `2 * m + 1`,
the `+ 1` making the range inclusive, the offset in the weight `2 * m + 1`, the successor in
`(m₀ + 1)`, and the near block's share of the bracket. `0` is the lower bound on `θ`. `2` occurs
three times — the coefficient in the contraction step, the coefficient in the weight, and the
exponent on `(m₀ + 1)`. `3` is `4 - 1`, the block-weight ratio, and `4` is the growth factor the
contraction is measured against. -/
theorem layer_partial_le {a : ℕ → ℝ} {m₀ : ℕ} {θ : ℝ}
    (ha1 : ∀ m, a m ≤ 1) (hanti : ∀ m m' : ℕ, m ≤ m' → a m' ≤ a m) (hθ0 : 0 ≤ θ)
    (hdb : ∀ m, m₀ ≤ m → a (2 * m + 1) ≤ θ * a m) (J : ℕ) :
    ∑ m ∈ Finset.range (cut m₀ J + 1), (2 * (m : ℝ) + 1) * a m
      ≤ ((m₀ : ℝ) + 1) ^ 2 * (1 + 3 * ∑ j ∈ Finset.range J, (4 * θ) ^ j) := by
  have hup := layer_le_condensed (a := a) (m₀ := m₀) ha1 hanti J
  have hcmp : ∑ j ∈ Finset.range J, (4 : ℝ) ^ j * a (cut m₀ j)
      ≤ ∑ j ∈ Finset.range J, (4 * θ) ^ j := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    have hprof : a (cut m₀ j) ≤ θ ^ j := by
      have h1 := le_pow_of_doubling (a := a) (m₀ := m₀) hθ0 hdb j
      have h2 : θ ^ j * a m₀ ≤ θ ^ j * 1 :=
        mul_le_mul_of_nonneg_left (ha1 m₀) (by positivity)
      linarith
    calc (4 : ℝ) ^ j * a (cut m₀ j) ≤ (4 : ℝ) ^ j * θ ^ j :=
          mul_le_mul_of_nonneg_left hprof (by positivity)
      _ = (4 * θ) ^ j := by rw [mul_pow]
  have hM : (0 : ℝ) ≤ ((m₀ : ℝ) + 1) ^ 2 := by positivity
  nlinarith [hup, hcmp, hM]

/-! ### The moment bound from a doubling contraction -/

/-- `∑ j ∈ Finset.range J, r ^ j ≤ 1 / (1 - r)` for `0 ≤ r < 1`, at every finite `J`.

DERIVED: `0` is the lower bound on the ratio `r`; `1` occurs three times — the upper bound on `r`,
which is the convergence threshold, and the numerator and the `1 -` of the geometric total. -/
theorem geom_partial_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (J : ℕ) :
    ∑ j ∈ Finset.range J, r ^ j ≤ 1 / (1 - r) := by
  have hne : r ≠ 1 := ne_of_lt hr1
  have h1 : (0 : ℝ) < 1 - r := by linarith
  have hne1 : r - 1 ≠ 0 := by
    intro h
    exact hne (by linarith)
  have hne2 : (1 : ℝ) - r ≠ 0 := ne_of_gt h1
  have hp : (0 : ℝ) ≤ r ^ J := pow_nonneg hr0 J
  rw [geom_sum_eq hne]
  have heq : (r ^ J - 1) / (r - 1) = (1 - r ^ J) / (1 - r) := by
    field_simp
    ring
  rw [heq, div_le_div_iff₀ h1 h1]
  nlinarith [hp, h1]

/-- If `0 ≤ θ < 1 / 4` and `farShare R (2 * m + 1) ≤ θ * farShare R m` at every `m ≥ m₀`, then

    ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2 ≤ (m₀ + 1) ^ 2 * (1 + 3 / (1 - 4 * θ)).

`layer_partial_le` bounds the layer cake by `(m₀ + 1) ^ 2 * (1 + 3 * ∑ (4 * θ) ^ j)` and
`geom_partial_le` sums the geometric series, which converges because `4 * θ < 1`.

Scope: nothing is assumed below `m₀` — `farShare ≤ 1` caps the near block on its own. The bound is
uniform in the aperture `N`.

DERIVED: `0` is the lower bound on `θ`. `1` occurs five times — the numerator of the threshold
`1 / 4`, the offset in the doubling step `2 * m + 1`, the successor in `(m₀ + 1)`, the near block's
share of the bracket, and the `1 -` of the geometric total. `4` occurs twice, as the denominator of
the threshold and as the factor multiplying `θ` in the geometric total; both are the block-weight
growth factor `two_pow_sq` produces. `2` occurs three times — the coefficient in the doubling step,
the exponent on the circle lag, and the exponent on `(m₀ + 1)`. `3` is `4 - 1`, the block-weight
ratio. -/
theorem circ_moment_le_of_share_doubling {N : ℕ} (R : Moment.Read N) (m₀ : ℕ) (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 4)
    (hdb : ∀ m, m₀ ≤ m → farShare R (2 * m + 1) ≤ θ * farShare R m) :
    ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2
      ≤ ((m₀ : ℝ) + 1) ^ 2 * (1 + 3 / (1 - 4 * θ)) := by
  classical
  rw [circ_moment_eq_layer]
  have h4 : (0 : ℝ) ≤ 4 * θ := by linarith
  have h4' : 4 * θ < 1 := by linarith
  have hpart := layer_partial_le (a := fun m => farShare R m) (m₀ := m₀) (θ := θ)
    (fun m => farShare_le_one R m) (fun m m' h => farShare_antitone R h) hθ0 hdb N
  have hcover : N + 1 ≤ cut m₀ N + 1 := by
    have := self_le_cut m₀ N
    omega
  have hmono : ∑ m ∈ Finset.range (N + 1), (2 * (m : ℝ) + 1) * farShare R m
      ≤ ∑ m ∈ Finset.range (cut m₀ N + 1), (2 * (m : ℝ) + 1) * farShare R m :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
      (fun m _ _ => mul_nonneg (by positivity) (farShare_nonneg R m))
  have hgeom : ∑ j ∈ Finset.range N, (4 * θ) ^ j ≤ 1 / (1 - 4 * θ) :=
    geom_partial_le h4 h4' N
  have hM : (0 : ℝ) ≤ ((m₀ : ℝ) + 1) ^ 2 := by positivity
  have hstep : ((m₀ : ℝ) + 1) ^ 2 * (1 + 3 * ∑ j ∈ Finset.range N, (4 * θ) ^ j)
      ≤ ((m₀ : ℝ) + 1) ^ 2 * (1 + 3 / (1 - 4 * θ)) := by
    have h3 : 3 * ∑ j ∈ Finset.range N, (4 * θ) ^ j ≤ 3 / (1 - 4 * θ) := by
      have hmul := mul_le_mul_of_nonneg_left hgeom (by norm_num : (0 : ℝ) ≤ 3)
      calc 3 * ∑ j ∈ Finset.range N, (4 * θ) ^ j ≤ 3 * (1 / (1 - 4 * θ)) := hmul
        _ = 3 / (1 - 4 * θ) := by ring
    exact mul_le_mul_of_nonneg_left (by linarith) hM
  linarith [hpart, hmono, hstep]

#print axioms circ_moment_le_of_share_doubling

/-! ### Condensation: the hypothesis is equivalent to a bound at a geometric sequence of cuts

`layer_le_condensed` and `condensed_le_layer` bracket the layer cake by the same condensed sum from
both sides, up to the factor `3(m₀+1)²` and a shift of one cut. Since `farShare` is antitone for
free, that makes the substrate hypothesis equivalent to uniform boundedness of

    ∑_{j} 4^j · farShare R (cut m₀ j)

(`substrate_iff_dyadic_shares`). This is Cauchy condensation for the weight `2m+1`: the `4^j` is the
weight of the `j`-th block over the block before it. What it buys is that only a geometric sequence
of cuts has to be estimated — `O(log N)` numbers per `(N, β)` instead of `N` — and it gives away
nothing, because it is an equivalence rather than a sufficient condition. -/

/-- `farShare R m = 0` for `N ≤ m`: `Moment.circLag` never exceeds the aperture, so the far set is
empty past it.

DERIVED: `0` is the value of the share beyond the aperture. -/
theorem farShare_eq_zero {N : ℕ} (R : Moment.Read N) {m : ℕ} (hm : N ≤ m) : farShare R m = 0 := by
  classical
  refine Finset.sum_eq_zero (fun d hd => ?_)
  simp only [farSet, Finset.mem_filter, Finset.mem_univ, true_and] at hd
  exact absurd hd (by have hlt := circLag_lt_succ d; omega)

/-- `∑ m ∈ Finset.range K, (2 * m + 1) * farShare R m ≤ ∑ m ∈ Finset.range (N + 1), (2 * m + 1) * farShare R m`
at every `K`: the terms past the aperture vanish by `farShare_eq_zero`, so no range exceeds the full
one.

DERIVED: `2` occurs twice and `1` three times — the coefficient and offset of the weight `2 * m + 1`
on each side, and the `+ 1` making the full range inclusive of the aperture. -/
theorem layer_le_full {N : ℕ} (R : Moment.Read N) (K : ℕ) :
    ∑ m ∈ Finset.range K, (2 * (m : ℝ) + 1) * farShare R m
      ≤ ∑ m ∈ Finset.range (N + 1), (2 * (m : ℝ) + 1) * farShare R m := by
  by_cases h : K ≤ N + 1
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
      (fun m _ _ => mul_nonneg (by positivity) (farShare_nonneg R m))
  · refine le_of_eq (Finset.sum_subset ?_ ?_).symm
    · intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    · intro x hx hnx
      simp only [Finset.mem_range] at hx hnx
      rw [farShare_eq_zero R (by omega), mul_zero]

/-- If `∑ j ∈ Finset.range J, 4 ^ j * farShare R (cut m₀ j) ≤ S` at every `J`, then
`∑ d, R.p d * (circLag d : ℝ) ^ 2 ≤ (m₀ + 1) ^ 2 * (1 + 3 * S)`. It is `layer_le_condensed` with the
condensed sum bounded by `S`, and `layer_le_full` to reach the whole layer cake.

DERIVED: `4` is the block-weight growth factor; `2` occurs twice, as the exponent on the circle lag
and on `(m₀ + 1)`; `1` occurs twice, as the successor in `(m₀ + 1)` and the near block's share of the
bracket; `3` is `4 - 1`, the block-weight ratio. -/
theorem circ_moment_le_of_dyadic_shares {N : ℕ} (R : Moment.Read N) (m₀ : ℕ) (S : ℝ)
    (hS : ∀ J : ℕ, ∑ j ∈ Finset.range J, (4 : ℝ) ^ j * farShare R (cut m₀ j) ≤ S) :
    ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2 ≤ ((m₀ : ℝ) + 1) ^ 2 * (1 + 3 * S) := by
  rw [circ_moment_eq_layer]
  have hcover : N + 1 ≤ cut m₀ N + 1 := by
    have := self_le_cut m₀ N
    omega
  have hmono : ∑ m ∈ Finset.range (N + 1), (2 * (m : ℝ) + 1) * farShare R m
      ≤ ∑ m ∈ Finset.range (cut m₀ N + 1), (2 * (m : ℝ) + 1) * farShare R m :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
      (fun m _ _ => mul_nonneg (by positivity) (farShare_nonneg R m))
  have hup := layer_le_condensed (a := fun m => farShare R m) (m₀ := m₀)
    (fun m => farShare_le_one R m) (fun m m' h => farShare_antitone R h) N
  have hM : (0 : ℝ) ≤ ((m₀ : ℝ) + 1) ^ 2 := by positivity
  have hstep : ((m₀ : ℝ) + 1) ^ 2
        * (1 + 3 * ∑ j ∈ Finset.range N, (4 : ℝ) ^ j * farShare R (cut m₀ j))
      ≤ ((m₀ : ℝ) + 1) ^ 2 * (1 + 3 * S) :=
    mul_le_mul_of_nonneg_left (by linarith [hS N]) hM
  linarith [hmono, hup, hstep]

#print axioms circ_moment_le_of_dyadic_shares

/-- If `∑ d, R.p d * (circLag d : ℝ) ^ 2 ≤ B`, then
`3 * (m₀ + 1) ^ 2 * ∑ j ∈ Finset.range J, 4 ^ j * farShare R (cut m₀ (j + 1)) ≤ B` at every `J`. It is
`condensed_le_layer` followed by `layer_le_full` and the hypothesis.

This is the converse of `circ_moment_le_of_dyadic_shares`, and what makes
`substrate_iff_dyadic_shares` an equivalence.

DERIVED: `2` occurs twice, as the exponent on the circle lag and on `(m₀ + 1)`; `3` is the
block-weight ratio `4 - 1` and `4` the growth factor; `1` occurs twice, as the successor in
`(m₀ + 1)` and as the shift `j + 1` to the block's far end. -/
theorem dyadic_shares_le_of_circ_moment {N : ℕ} (R : Moment.Read N) (m₀ : ℕ) (B : ℝ)
    (hB : ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2 ≤ B) (J : ℕ) :
    3 * ((m₀ : ℝ) + 1) ^ 2 * ∑ j ∈ Finset.range J, (4 : ℝ) ^ j * farShare R (cut m₀ (j + 1))
      ≤ B := by
  have h1 := condensed_le_layer (a := fun m => farShare R m) (m₀ := m₀)
    (fun m => farShare_nonneg R m) (fun m m' h => farShare_antitone R h) J
  have h2 := layer_le_full R (cut m₀ J + 1)
  rw [circ_moment_eq_layer] at hB
  linarith

#print axioms dyadic_shares_le_of_circ_moment

/-- `∑ j ∈ Finset.range (J + 1), 4 ^ j * a (cut m₀ j) = 4 * (∑ i ∈ Finset.range J, 4 ^ i * a (cut m₀ (i + 1))) + a (cut m₀ 0)`:
the condensed sum with its first term peeled off, so that
`dyadic_shares_le_of_circ_moment`'s shifted sum can be reassembled.

DERIVED: `1` occurs twice, as the `+ 1` extending the range and the shift `i + 1`; `4` occurs three
times, as the growth factor in each of the two sums and as the factor pulled out; `0` is the index of
the peeled term. -/
theorem dyadic_sum_shift {a : ℕ → ℝ} {m₀ : ℕ} (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), (4 : ℝ) ^ j * a (cut m₀ j)
      = 4 * (∑ i ∈ Finset.range J, (4 : ℝ) ^ i * a (cut m₀ (i + 1))) + a (cut m₀ 0) := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  have hterm : ∀ i ∈ Finset.range J,
      (4 : ℝ) ^ (i + 1) * a (cut m₀ (i + 1)) = 4 * ((4 : ℝ) ^ i * a (cut m₀ (i + 1))) := by
    intro i _
    rw [pow_succ]
    ring
  rw [Finset.sum_congr rfl hterm]
  norm_num

/-- `∃ B, ∀ N β, d2At N β ≤ B` from a bound `S` on the condensed sums
`∑ j ∈ Finset.range J, 4 ^ j * farShare (readYMAt N β) (cut m₀ j)`, uniform in the aperture, the
coupling and `J`. It is `circ_moment_le_of_dyadic_shares` at `readYMAt N β`.

DERIVED: `4` is the block-weight growth factor. -/
theorem substrate_of_dyadic_shares (m₀ : ℕ) (S : ℝ)
    (hS : ∀ (N : ℕ) (β : ℝ) (J : ℕ),
      ∑ j ∈ Finset.range J, (4 : ℝ) ^ j * farShare (MassGap.readYMAt N β) (cut m₀ j) ≤ S) :
    ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B :=
  ⟨((m₀ : ℝ) + 1) ^ 2 * (1 + 3 * S), fun N β =>
    circ_moment_le_of_dyadic_shares (MassGap.readYMAt N β) m₀ S (hS N β)⟩

#print axioms substrate_of_dyadic_shares

/-- The converse: a bound `B` on `d2At` gives a bound `S` on the condensed sums, uniform in the
aperture, the coupling and `J`. `dyadic_shares_le_of_circ_moment` bounds the shifted sum and
`dyadic_sum_shift` reassembles the unshifted one, the peeled term being at most `1`.

DERIVED: `4` is the block-weight growth factor. -/
theorem dyadic_shares_of_substrate (m₀ : ℕ) (h : ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B) :
    ∃ S : ℝ, ∀ (N : ℕ) (β : ℝ) (J : ℕ),
      ∑ j ∈ Finset.range J, (4 : ℝ) ^ j * farShare (MassGap.readYMAt N β) (cut m₀ j) ≤ S := by
  obtain ⟨B, hB⟩ := h
  have hB0 : 0 ≤ B := by
    refine le_trans ?_ (hB 0 0)
    exact Finset.sum_nonneg
      (fun d _ => mul_nonneg ((MassGap.readYMAt 0 0).p_nonneg d) (sq_nonneg _))
  have hMpos : (0 : ℝ) < 3 * ((m₀ : ℝ) + 1) ^ 2 := by positivity
  refine ⟨4 * B / (3 * ((m₀ : ℝ) + 1) ^ 2) + 1, ?_⟩
  intro N β J
  have hquot : (0 : ℝ) ≤ 4 * B / (3 * ((m₀ : ℝ) + 1) ^ 2) :=
    div_nonneg (by linarith) (le_of_lt hMpos)
  cases J with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      linarith
  | succ J' =>
      rw [dyadic_sum_shift (a := fun m => farShare (MassGap.readYMAt N β) m) (m₀ := m₀) J']
      have hd := dyadic_shares_le_of_circ_moment (MassGap.readYMAt N β) m₀ B (hB N β) J'
      have h1 : ∑ i ∈ Finset.range J',
          (4 : ℝ) ^ i * farShare (MassGap.readYMAt N β) (cut m₀ (i + 1))
          ≤ B / (3 * ((m₀ : ℝ) + 1) ^ 2) := by
        rw [le_div_iff₀ hMpos]
        linarith [hd]
      have h2 : farShare (MassGap.readYMAt N β) (cut m₀ 0) ≤ 1 := farShare_le_one _ _
      have h3 : 4 * (B / (3 * ((m₀ : ℝ) + 1) ^ 2)) = 4 * B / (3 * ((m₀ : ℝ) + 1) ^ 2) := by ring
      linarith [h1, h2, h3]

#print axioms dyadic_shares_of_substrate

/-- At every starting cut `m₀`,

    (∃ B, ∀ N β, d2At N β ≤ B) ↔ (∃ S, ∀ N β J, ∑ j ∈ Finset.range J, 4 ^ j * farShare (readYMAt N β) (cut m₀ j) ≤ S).

The two directions are `substrate_of_dyadic_shares` and `dyadic_shares_of_substrate`.

Scope: an equivalence, so it restates the hypothesis rather than weakening or strengthening it. The
cuts off the sequence `m₀, 2 * m₀ + 1, 4 * m₀ + 3, …` need no separate treatment because
`farShare_antitone` controls each block by its left endpoint.

DERIVED: `4` is the block-weight growth factor, the square of the doubling. -/
theorem substrate_iff_dyadic_shares (m₀ : ℕ) :
    (∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B)
      ↔ (∃ S : ℝ, ∀ (N : ℕ) (β : ℝ) (J : ℕ),
          ∑ j ∈ Finset.range J, (4 : ℝ) ^ j * farShare (MassGap.readYMAt N β) (cut m₀ j) ≤ S) :=
  ⟨dyadic_shares_of_substrate m₀, fun ⟨S, hS⟩ => substrate_of_dyadic_shares m₀ S hS⟩

#print axioms substrate_iff_dyadic_shares

/-! ### The doubling contraction as a sufficient condition -/

/-- `∃ B, ∀ N β, d2At N β ≤ B` from one cut `m₀` and one ratio `θ` with `0 ≤ θ < 1 / 4` such that
`farShare (readYMAt N β) (2 * m + 1) ≤ θ * farShare (readYMAt N β) m` at every aperture, coupling and
`m ≥ m₀`. The witness is `(m₀ + 1) ^ 2 * (1 + 3 / (1 - 4 * θ))` from
`circ_moment_le_of_share_doubling`.

Scope: the contraction is required uniformly in the aperture and the coupling; one holding at each
coupling with `θ` depending on `β` does not satisfy it. The axiom footprint carries
`wilson_reflection_positive_at`, from which `readYMAt` is constructed.

DERIVED: `0` is the lower bound on `θ`; `1` occurs twice, as the numerator of the threshold `1 / 4`
and the offset in the doubling step `2 * m + 1`; `4` is the threshold's denominator, the block-weight
growth factor; `2` is the coefficient in the doubling step. -/
theorem substrate_of_share_doubling (m₀ : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 4)
    (hdb : ∀ (N : ℕ) (β : ℝ) (m : ℕ), m₀ ≤ m →
      farShare (MassGap.readYMAt N β) (2 * m + 1) ≤ θ * farShare (MassGap.readYMAt N β) m) :
    ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B :=
  ⟨((m₀ : ℝ) + 1) ^ 2 * (1 + 3 / (1 - 4 * θ)), fun N β =>
    circ_moment_le_of_share_doubling (MassGap.readYMAt N β) m₀ θ hθ0 hθ (hdb N β)⟩

#print axioms substrate_of_share_doubling

/-- `∀ᶠ N in atTop, ∀ β, μYMAt N β < κ₀YM` from the same doubling contraction, by
`MassGap.confinement_of_bounded_substrate` at `substrate_of_share_doubling`.

DERIVED: `0` is the lower bound on `θ`; `1` occurs twice, as the numerator of the threshold `1 / 4`
and the offset in the doubling step; `4` is the threshold's denominator; `2` is the coefficient in
the doubling step. -/
theorem confinement_of_share_doubling (m₀ : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 4)
    (hdb : ∀ (N : ℕ) (β : ℝ) (m : ℕ), m₀ ≤ m →
      farShare (MassGap.readYMAt N β) (2 * m + 1) ≤ θ * farShare (MassGap.readYMAt N β) m) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, MassGap.μYMAt N β < MassGap.κ₀YM :=
  MassGap.confinement_of_bounded_substrate (substrate_of_share_doubling m₀ θ hθ0 hθ hdb)

#print axioms confinement_of_share_doubling

/-- `WilsonModel.existence_and_gap_of_substrate` with its hypothesis supplied by
`substrate_of_share_doubling`: from the doubling contraction there is a substrate witness `h` such
that the model `WilsonModel.wilsonOfSubstrate h` has its mode sum tending to `0` at every coupling,
`gap.μ β - gap.κ < 0` at every coupling, and `gap.R` constant.

DERIVED: `0` occurs three times — the lower bound on `θ`, the limit point of the mode sum, and the
comparison point in `gap.μ β - gap.κ < 0`. `1` occurs twice, as the numerator of the threshold
`1 / 4` and the offset in the doubling step; `4` is the threshold's denominator; `2` is the
coefficient in the doubling step. -/
theorem yang_mills_of_share_doubling (m₀ : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 4)
    (hdb : ∀ (N : ℕ) (β : ℝ) (m : ℕ), m₀ ≤ m →
      farShare (MassGap.readYMAt N β) (2 * m + 1) ≤ θ * farShare (MassGap.readYMAt N β) m) :
    ∃ h : (∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B),
      ((∀ β, Filter.Tendsto (fun τ => ‖∑ k ∈ (MassGap.WilsonModel.wilsonOfSubstrate h).model.gap.s β,
            (MassGap.WilsonModel.wilsonOfSubstrate h).model.gap.P β k
              * ((MassGap.WilsonModel.wilsonOfSubstrate h).model.gap.m β k) ^ τ‖)
          Filter.atTop (nhds 0)) ∧
        (∀ β, (MassGap.WilsonModel.wilsonOfSubstrate h).model.gap.μ β
            - (MassGap.WilsonModel.wilsonOfSubstrate h).model.gap.κ < 0) ∧
        (∀ d d', (MassGap.WilsonModel.wilsonOfSubstrate h).model.gap.R d
            = (MassGap.WilsonModel.wilsonOfSubstrate h).model.gap.R d')) := by
  refine ⟨substrate_of_share_doubling m₀ θ hθ0 hθ hdb, ?_⟩
  exact (MassGap.WilsonModel.existence_and_gap_of_substrate
    (substrate_of_share_doubling m₀ θ hθ0 hθ hdb)).1

#print axioms yang_mills_of_share_doubling

/-! ### The same condition on the unnormalised correlator -/

/-- `farShare R (2 * m + 1) ≤ θ * farShare R m` if and only if
`∑ d ∈ farSet N (2 * m + 1), R.ρ d ≤ θ * ∑ d ∈ farSet N m, R.ρ d`. The total mass `∑ d, R.ρ d`
divides both sides of the share form and cancels, so the contraction never reads it — neither its
value nor a floor under it.

Scope: an equivalence, at every cut and every `θ`.

DERIVED: `2` occurs twice and `1` twice, as the coefficient and offset of the doubling step
`2 * m + 1` on each side of the equivalence. -/
theorem farShare_doubling_iff_tail_mass {N : ℕ} (R : Moment.Read N) (m : ℕ) (θ : ℝ) :
    (farShare R (2 * m + 1) ≤ θ * farShare R m)
      ↔ (∑ d ∈ farSet N (2 * m + 1), R.ρ d ≤ θ * ∑ d ∈ farSet N m, R.ρ d) := by
  have hT : (0 : ℝ) < ∑ d, R.ρ d := R.hpos
  have hkey : θ * ((∑ d ∈ farSet N m, R.ρ d) / (∑ d, R.ρ d))
      = (θ * ∑ d ∈ farSet N m, R.ρ d) / (∑ d, R.ρ d) := by ring
  rw [farShare_eq_rho, farShare_eq_rho, hkey, div_le_div_iff₀ hT hT]
  constructor
  · intro h
    exact le_of_mul_le_mul_right h hT
  · intro h
    exact mul_le_mul_of_nonneg_right h hT.le

#print axioms farShare_doubling_iff_tail_mass

/-- `(readYMAt N β).ρ d = wilsonCorrAt N (max β 0) d`, by `rfl`: the read's unnormalised profile is
the constructed correlation at the clamped coupling. At `0 ≤ β` the clamp is inert
(`Complete.readYMAt_rho_of_nonneg`).

DERIVED: `1` is the `+ 1` in the lag index type `Fin (N + 1)`, one index per lag including
contact; `0` is the clamp point in `max β 0`. -/
theorem readYMAt_rho (N : ℕ) (β : ℝ) (d : Fin (N + 1)) :
    (MassGap.readYMAt N β).ρ d = MassGap.wilsonCorrAt N (max β 0) d := rfl

/-- `∃ B, ∀ N β, d2At N β ≤ B` from a contraction on the unnormalised tail masses:
`∑ d ∈ farSet N (2 * m + 1), wilsonCorrAt N β d ≤ θ * ∑ d ∈ farSet N m, wilsonCorrAt N β d` at every
aperture, coupling and `m ≥ m₀`, with `0 ≤ θ < 1 / 4`. It is `substrate_of_share_doubling` through
`farShare_doubling_iff_tail_mass` and `readYMAt_rho`.

Scope: no normalisation, envelope or lower bound on `∑ d, wilsonCorrAt N β d` appears. The
hypothesis is invariant under `ρ ↦ t * ρ`, as the conclusion is — the property
`mass_floor_is_not_scale_free` shows an envelope-plus-floor pair does not have.

DERIVED: `0` is the lower bound on `θ`; `1` occurs twice, as the numerator of the threshold `1 / 4`
and the offset in the doubling step; `4` is the threshold's denominator, the block-weight growth
factor; `2` is the coefficient in the doubling step. -/
theorem substrate_of_tail_mass_doubling (m₀ : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 4)
    (h : ∀ (N : ℕ) (β : ℝ) (m : ℕ), m₀ ≤ m →
      ∑ d ∈ farSet N (2 * m + 1), MassGap.wilsonCorrAt N β d
        ≤ θ * ∑ d ∈ farSet N m, MassGap.wilsonCorrAt N β d) :
    ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B := by
  refine substrate_of_share_doubling m₀ θ hθ0 hθ ?_
  intro N β m hm
  refine (farShare_doubling_iff_tail_mass (MassGap.readYMAt N β) m θ).mpr ?_
  simpa only [readYMAt_rho] using h N (max β 0) m hm

#print axioms substrate_of_tail_mass_doubling

/-! ### Rescaling: the share and the moment are invariant, a mass floor is not -/

/-- The read with its unnormalised profile multiplied by `t`, for `0 < t`. The normalised weights
`p` are unchanged, since the factor cancels between numerator and total.

DERIVED: `0` is the strict lower bound on `t`, which `Moment.Read`'s `hpos` field requires — at
`t ≤ 0` the total mass would not be positive and the result would not be a read. -/
noncomputable def scaleRead {N : ℕ} (R : Moment.Read N) {t : ℝ} (ht : 0 < t) : Moment.Read N where
  ρ := fun d => t * R.ρ d
  hρ := fun d => mul_nonneg ht.le (R.hρ d)
  hpos := by
    have hrw : ∑ d, t * R.ρ d = t * ∑ d, R.ρ d := by rw [← Finset.mul_sum]
    show (0 : ℝ) < ∑ d, t * R.ρ d
    rw [hrw]
    exact mul_pos ht R.hpos

theorem scaleRead_sum {N : ℕ} (R : Moment.Read N) {t : ℝ} (ht : 0 < t) :
    ∑ d, (scaleRead R ht).ρ d = t * ∑ d, R.ρ d := by
  show ∑ d, t * R.ρ d = t * ∑ d, R.ρ d
  rw [← Finset.mul_sum]

theorem scaleRead_p {N : ℕ} (R : Moment.Read N) {t : ℝ} (ht : 0 < t) (d : Fin (N + 1)) :
    (scaleRead R ht).p d = R.p d := by
  show (t * R.ρ d) / (∑ d', (scaleRead R ht).ρ d') = R.ρ d / ∑ d', R.ρ d'
  rw [scaleRead_sum R ht]
  exact mul_div_mul_left _ _ (ne_of_gt ht)

/-- `farShare (scaleRead R ht) m = farShare R m` at every cut: the rescaling factor cancels between
the far mass and the total.

DERIVED: `0` is the strict lower bound on the rescaling factor `t`. -/
theorem farShare_scale_invariant {N : ℕ} (R : Moment.Read N) {t : ℝ} (ht : 0 < t) (m : ℕ) :
    farShare (scaleRead R ht) m = farShare R m :=
  Finset.sum_congr rfl (fun d _ => scaleRead_p R ht d)

/-- `∑ d, (scaleRead R ht).p d * (circLag d : ℝ) ^ 2 = ∑ d, R.p d * (circLag d : ℝ) ^ 2`: the
normalised weights are unchanged by the rescaling, so the moment is too.

DERIVED: `0` is the strict lower bound on `t`; the exponent `2` occurs twice, once in each circular
second moment. -/
theorem circ_moment_scale_invariant {N : ℕ} (R : Moment.Read N) {t : ℝ} (ht : 0 < t) :
    ∑ d, (scaleRead R ht).p d * (Moment.circLag d : ℝ) ^ 2
      = ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2 :=
  Finset.sum_congr rfl (fun d _ => by rw [scaleRead_p R ht d])

/-- For every read and every `c > 0` there is a `t > 0` such that `scaleRead R ht` has the same far
share at every cut and the same circular second moment, and fails `c ≤ ∑ d, ρ d`.

`ContactDominance.circ_moment_le_of_rho_envelope` consumes an envelope on `ρ` together with such a
floor. Its conclusion is invariant under `ρ ↦ t * ρ`, as is the far share; the floor is not. So that
pair constrains one degree of freedom the conclusion does not see, which
`substrate_of_tail_mass_doubling` — mentioning no total mass — does not.

DERIVED: `0` occurs twice, as the strict lower bound on `c` and on the rescaling factor `t`; the
exponent `2` occurs twice, once in each circular second moment. -/
theorem mass_floor_is_not_scale_free {N : ℕ} (R : Moment.Read N) (c : ℝ) (hc : 0 < c) :
    ∃ (t : ℝ) (ht : 0 < t),
      (∀ m, farShare (scaleRead R ht) m = farShare R m) ∧
        (∑ d, (scaleRead R ht).p d * (Moment.circLag d : ℝ) ^ 2
          = ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2) ∧
        ¬ (c ≤ ∑ d, (scaleRead R ht).ρ d) := by
  have hT : (0 : ℝ) < ∑ d, R.ρ d := R.hpos
  refine ⟨c / (2 * ∑ d, R.ρ d), by positivity, ?_, ?_, ?_⟩
  · exact fun m => farShare_scale_invariant R _ m
  · exact circ_moment_scale_invariant R _
  · rw [scaleRead_sum R (by positivity : (0 : ℝ) < c / (2 * ∑ d, R.ρ d))]
    have hval : c / (2 * ∑ d, R.ρ d) * ∑ d, R.ρ d = c / 2 := by
      field_simp
      try ring
    rw [hval]
    linarith

#print axioms mass_floor_is_not_scale_free

/-! ### A read satisfying the contraction -/

/-- `ContactDominance.contactRead N` satisfies the contraction at `θ = 0` and every cut, and its
circular second moment is `0`. All its weight sits at lag zero, so every far share vanishes.

So the hypothesis of `circ_moment_le_of_share_doubling` is satisfiable.

DERIVED: `2` occurs twice, as the coefficient in the doubling step and as the exponent on the circle
lag; `1` is the offset in the doubling step; `0` occurs twice, as the contraction factor at which
the read meets the hypothesis and as the value of its moment. -/
theorem doubling_nonvacuous (N : ℕ) :
    (∀ m : ℕ, farShare (contactRead N) (2 * m + 1) ≤ (0 : ℝ) * farShare (contactRead N) m) ∧
      ∑ d, (contactRead N).p d * (Moment.circLag d : ℝ) ^ 2 = 0 :=
  ⟨fun m => by rw [contactRead_farShare, contactRead_farShare]; norm_num,
    contactRead_moment N⟩

#print axioms doubling_nonvacuous

/-! ### A read failing the contraction, with unbounded moments -/

/-- `farShare (midRead N) m = 1` for `m < (N + 1) / 2`: all of `midRead`'s weight sits at the
antipode, so every cut below half the period leaves the whole of it in the far set.

DERIVED: `1` occurs twice, as the `+ 1` making the period `N + 1` and as the value of the share; `2`
is the halving that locates the antipode. -/
theorem midRead_farShare (N m : ℕ) (hm : m < (N + 1) / 2) : farShare (midRead N) m = 1 := by
  classical
  have hmem : midLag N ∈ farSet N m := by
    simp only [farSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [circLag_midLag N]
    exact hm
  have hsum := midRead_sum N
  have hp : ∀ d, (midRead N).p d = (midRead N).ρ d := by
    intro d; simp [Moment.Read.p, hsum]
  have hzero : ∀ d ∈ farSet N m, d ≠ midLag N → (midRead N).p d = 0 := by
    intro d _ hne
    rw [hp d]
    show (if d = midLag N then (1 : ℝ) else 0) = 0
    rw [if_neg hne]
  rw [farShare, Finset.sum_eq_single_of_mem _ hmem hzero, hp]
  show (if midLag N = midLag N then (1 : ℝ) else 0) = 1
  rw [if_pos rfl]

/-- Two facts about `ContactDominance.midRead`, conjoined: at every `θ < 1` and every cut `m₀` there
are an aperture and an `m ≥ m₀` with `θ * farShare (midRead N) m < farShare (midRead N) (2 * m + 1)`;
and its circular second moments exceed every `B`.

The first holds because `midRead_farShare` makes both shares `1` below the antipode, so the
contraction would need `θ ≥ 1`.

So the contraction hypothesis of `circ_moment_le_of_share_doubling` is used: without it the
conclusion does not hold for this family.

DERIVED: `1` occurs twice, as the upper bound on `θ` — the value both shares take — and as the offset
in the doubling step; `2` occurs twice, as the coefficient in the doubling step and as the exponent
on the circle lag. -/
theorem doubling_load_bearing :
    (∀ θ : ℝ, θ < 1 → ∀ m₀ : ℕ, ∃ N m : ℕ, m₀ ≤ m ∧
        θ * farShare (midRead N) m < farShare (midRead N) (2 * m + 1)) ∧
      (∀ B : ℝ, ∃ N : ℕ, B < ∑ d, (midRead N).p d * (Moment.circLag d : ℝ) ^ 2) := by
  constructor
  · intro θ hθ m₀
    refine ⟨4 * m₀ + 3, m₀, le_refl _, ?_⟩
    have h1 : farShare (midRead (4 * m₀ + 3)) m₀ = 1 :=
      midRead_farShare _ _ (by omega)
    have h2 : farShare (midRead (4 * m₀ + 3)) (2 * m₀ + 1) = 1 :=
      midRead_farShare _ _ (by omega)
    rw [h1, h2]
    linarith
  · intro B
    obtain ⟨k, hk⟩ := exists_nat_gt B
    refine ⟨2 * k + 1, ?_⟩
    rw [midRead_moment]
    have hdiv : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    rw [hdiv]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    nlinarith [hk, hk0]

#print axioms doubling_load_bearing

/-! ### The threshold ratio is exactly one quarter

`ContactDominance.squareRead` is the family whose far share saturates a square envelope. In this
parametrisation it meets the contraction at `θ = 1 / 4` exactly, at every cut and every aperture, and
its moments are unbounded. So the strict inequality `θ < 1 / 4` in
`circ_moment_le_of_share_doubling` is the hypothesis rather than a margin around it. -/

/-- `∑ d ∈ farSet (2 * k + 1) m, (squareRead k).ρ d = ∑ j ∈ Finset.range (k + 2), telWeight j * (if m < j then 1 else 0)`:
the far mass collapses onto the telescoping weights, the indicator selecting the lags beyond the cut.

DERIVED: `2` occurs twice, as the coefficient in the aperture `2 * k + 1` and as the `+ 2` bounding
the telescoping range at the antipode; `1` occurs twice, as the offset in the aperture and as the
indicator's value; `0` is the indicator's value off the far set. -/
theorem squareRead_farMass (k m : ℕ) :
    ∑ d ∈ farSet (2 * k + 1) m, (squareRead k).ρ d
      = ∑ j ∈ Finset.range (k + 2), telWeight j * (if m < j then (1 : ℝ) else 0) := by
  classical
  have hrw : ∑ d ∈ farSet (2 * k + 1) m, (squareRead k).ρ d
      = ∑ d : Fin (2 * k + 1 + 1), (squareRead k).ρ d
          * (fun j : ℕ => if m < j then (1 : ℝ) else 0) (Moment.circLag d) := by
    rw [farSet, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    by_cases hc : m < Moment.circLag d
    · simp [hc]
    · simp [hc]
  rw [hrw, squareRead_sum_eq k (fun j : ℕ => if m < j then (1 : ℝ) else 0)]

/-- For `m + 1 ≤ k + 2`, the telescoping far mass equals `1 / (m + 1) ^ 2 - 1 / (k + 2) ^ 2`
exactly. The weights telescope, so the partial sum from `m + 1` to the antipode is the difference of
the two endpoints' reciprocal squares.

DERIVED: `1` occurs five times — the successor in the hypothesis `m + 1`, the indicator's value, the
numerator of each of the two fractions, and the `+ 1` in `(m + 1)`. `2` occurs five times — the `+ 2`
in the hypothesis, the `+ 2` bounding the telescoping range, the exponent on `(m + 1)`, the `+ 2` in
`(k + 2)`, and the exponent on it. `0` is the indicator's value off the far set. -/
theorem tel_far_eq_of_le (k m : ℕ) (h : m + 1 ≤ k + 2) :
    ∑ j ∈ Finset.range (k + 2), telWeight j * (if m < j then (1 : ℝ) else 0)
      = 1 / ((m : ℝ) + 1) ^ 2 - 1 / ((k : ℝ) + 2) ^ 2 := by
  classical
  have hfilt : ∑ j ∈ Finset.range (k + 2), telWeight j * (if m < j then (1 : ℝ) else 0)
      = ∑ j ∈ (Finset.range (k + 2)).filter (fun j => m < j), telWeight j := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split <;> ring
  rw [hfilt]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (k + 2))
    (fun j => m < j) telWeight
  have hnot : (Finset.range (k + 2)).filter (fun j => ¬ m < j) = Finset.range (m + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, not_lt]
    omega
  rw [hnot] at hsplit
  have h1 := telWeight_sum (k + 1)
  have h2 := telWeight_sum m
  have h1' : ∑ j ∈ Finset.range (k + 2), telWeight j = 1 - 1 / ((k : ℝ) + 2) ^ 2 := by
    rw [show k + 2 = (k + 1) + 1 from rfl, h1]
    push_cast
    ring
  linarith [hsplit, h1', h2]

/-- For `k + 2 ≤ m + 1` the telescoping far mass is `0`: the cut is past the antipode, so the
indicator selects nothing.

DERIVED: `2` occurs twice, as the `+ 2` in the hypothesis and the `+ 2` bounding the telescoping
range; `1` occurs twice, as the successor in the hypothesis and the indicator's value; `0` occurs
twice, as the indicator's value off the far set and as the resulting mass. -/
theorem tel_far_eq_of_gt (k m : ℕ) (h : k + 2 ≤ m + 1) :
    ∑ j ∈ Finset.range (k + 2), telWeight j * (if m < j then (1 : ℝ) else 0) = 0 := by
  refine Finset.sum_eq_zero (fun j hj => ?_)
  simp only [Finset.mem_range] at hj
  rw [if_neg (by omega), mul_zero]

/-- The telescoping far mass is nonnegative: a sum of nonnegative weights times an indicator.

DERIVED: `0` occurs twice, as the lower bound and as the indicator's value off the far set; `2` is
the `+ 2` bounding the telescoping range; `1` is the indicator's value on it. -/
theorem tel_far_nonneg (k m : ℕ) :
    0 ≤ ∑ j ∈ Finset.range (k + 2), telWeight j * (if m < j then (1 : ℝ) else 0) :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (telWeight_nonneg j) (by split <;> norm_num))

/-- `∑ d ∈ farSet (2*k+1) (2*m+1), (squareRead k).ρ d ≤ (1/4) * ∑ d ∈ farSet (2*k+1) m, (squareRead k).ρ d`
at every `k` and `m`: the telescoping family contracts by exactly one quarter across each doubling,
on the unnormalised tail masses. The three cases of `tel_far_eq_of_le`, `tel_far_eq_of_gt` and
`tel_far_nonneg` cover the cut being below, at or past the antipode.

DERIVED: `2` occurs three times, as the coefficient in the aperture `2 * k + 1` on each side and in
the doubling step `2 * m + 1`; `1` occurs four times, as the offset in each aperture, the offset in
the doubling step, and the numerator of `1 / 4`; `4` is the contraction's denominator, the square of
the doubling. -/
theorem squareRead_tail_mass_quarter (k m : ℕ) :
    ∑ d ∈ farSet (2 * k + 1) (2 * m + 1), (squareRead k).ρ d
      ≤ (1 / 4 : ℝ) * ∑ d ∈ farSet (2 * k + 1) m, (squareRead k).ρ d := by
  rw [squareRead_farMass, squareRead_farMass]
  by_cases h2 : (2 * m + 1) + 1 ≤ k + 2
  · have hm : m + 1 ≤ k + 2 := by omega
    rw [tel_far_eq_of_le k (2 * m + 1) h2, tel_far_eq_of_le k m hm]
    have hc : (0 : ℝ) ≤ 1 / ((k : ℝ) + 2) ^ 2 := by positivity
    have hkey : (1 : ℝ) / (((2 * m + 1 : ℕ) : ℝ) + 1) ^ 2
        = (1 / 4) * (1 / ((m : ℝ) + 1) ^ 2) := by
      have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      push_cast
      field_simp
      ring
    rw [hkey]
    linarith
  · rw [tel_far_eq_of_gt k (2 * m + 1) (by omega)]
    have := tel_far_nonneg k m
    linarith

/-- `farShare (squareRead k) (2 * m + 1) ≤ (1 / 4) * farShare (squareRead k) m`:
`squareRead_tail_mass_quarter` transported to the shares by `farShare_doubling_iff_tail_mass`.

DERIVED: `2` and the first `1` are the coefficient and offset of the doubling step `2 * m + 1`; the
second `1` and `4` are the numerator and denominator of the contraction factor. -/
theorem squareRead_quarter_doubling (k m : ℕ) :
    farShare (squareRead k) (2 * m + 1) ≤ (1 / 4 : ℝ) * farShare (squareRead k) m :=
  (farShare_doubling_iff_tail_mass (squareRead k) m (1 / 4)).mpr
    (squareRead_tail_mass_quarter k m)

/-- Two facts about `ContactDominance.squareRead`, conjoined: it contracts by `1 / 4` across every
doubling at every aperture, and its circular second moments exceed every `B`.

So the strict inequality `θ < 1 / 4` in `circ_moment_le_of_share_doubling` cannot be relaxed to `≤`.
It is the same family as `ContactDominance.square_share_is_not_enough`, since `(m + 1) ^ (-s)`
contracts by exactly `2 ^ (-s)` across `m ↦ 2 * m + 1`, which makes `θ = 1 / 4` and the envelope
exponent `s = 2` the same threshold.

DERIVED: `2` occurs twice, as the coefficient in the doubling step and as the exponent on the circle
lag; `1` occurs twice, as the offset in the doubling step and as the numerator of the contraction
factor; `4` is its denominator. -/
theorem quarter_doubling_is_not_enough :
    (∀ k m : ℕ, farShare (squareRead k) (2 * m + 1) ≤ (1 / 4 : ℝ) * farShare (squareRead k) m) ∧
      (∀ B : ℝ, ∃ k : ℕ, B < ∑ d, (squareRead k).p d * (Moment.circLag d : ℝ) ^ 2) :=
  ⟨squareRead_quarter_doubling, square_share_is_not_enough.2⟩

#print axioms quarter_doubling_is_not_enough

/-- There is no `B` bounding the circular second moment of every read contracting by `1 / 4` across
every doubling: for each candidate `B`, `quarter_doubling_is_not_enough` supplies a `squareRead k`
exceeding it.

Stated without the criterion's own constant, so nothing turns on how `3 / (1 - 4 * θ)` evaluates at
`θ = 1 / 4`.

DERIVED: `2` occurs twice, as the coefficient in the doubling step and as the exponent on the circle
lag; `1` occurs twice, as the offset in the doubling step and as the numerator of the contraction
factor; `4` is its denominator. -/
theorem quarter_doubling_gives_no_bound :
    ¬ ∃ B : ℝ, ∀ (N : ℕ) (R : Moment.Read N),
        (∀ m : ℕ, farShare R (2 * m + 1) ≤ (1 / 4 : ℝ) * farShare R m) →
        ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2 ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨k, hk⟩ := square_share_is_not_enough.2 B
  exact absurd (hB (2 * k + 1) (squareRead k) (fun m => squareRead_quarter_doubling k m))
    (not_le.mpr hk)

#print axioms quarter_doubling_gives_no_bound

/-! ### Contact-relative decay: a power law measured against the read's own contact term

The conditions above are on the share, which carries the normalisation `∑ ρ` inside it. The condition
in this section is on the correlation itself, measured against its value at lag zero:

    ρ d ≤ C * ρ 0 / (circLag d) ^ 4   whenever   circLag d ≥ m₀.

Three properties follow from its shape:

* It is scale-free (`contact_relative_scale_invariant`): `ρ ↦ t * ρ` multiplies both sides by `t`, so
  the condition is invariant exactly as the conclusion is. No mass floor appears, because
  `contact_le_total` gives `ρ 0 ≤ ∑ ρ` from nonnegativity alone, so
  `ContactDominance.circ_moment_le_of_rho_envelope`'s extra hypothesis `c ≤ ∑ ρ` is not needed.
* It is a power, not a rate. `Substrate.bounded_moment_does_not_give_geometric_decay` says a bounded
  moment does not give a geometric bound, and asymptotic freedom denies a decay rate uniform in the
  coupling; neither bears on a power law.
* Nothing is assumed below the cut `m₀`, because `p_le_one` caps the near lags — the same structure
  as `ContactDominance.circ_moment_le_of_tail_envelope`.

The threshold exponent is `3`, and `4` is the smallest integer above it: the moment weights by
`k ^ 2` and the circle lag has multiplicity two (`Moment.sum_circLag_le_two_mul`), so the envelope's
weighted total is `∑ k ^ 2 * C / k ^ s`, convergent exactly when `s > 3`. That is one above the
share's threshold `2` because the share has already absorbed a summation.
`cubic_contact_relative_is_not_enough` and `cubic_contact_relative_gives_no_bound` show that at
`s = 3` with `C = 1` there is no bound.

Scope: a sufficient condition, strictly stronger than the substrate hypothesis —
`contact_relative_is_strictly_stronger` exhibits `Substrate.tailRead`, whose moment is at most `1` at
every aperture and which admits no `(C, m₀)` at exponent `4`. The condition is required uniformly in
the aperture and the coupling; `ContactDominance.aperture_uniformity_does_not_give_coupling_uniformity`
applies to it as to the others. What the form fixes is the shape: one dimensionless constant `C` in
front of a fixed power, with no rate, normalisation or total mass in it.
-/

/-- `Moment.circLag (0 : Fin (N + 1)) = 0` at every aperture: the circular distance from the origin
to itself.

DERIVED: `0` occurs twice, as the lag whose distance is taken and as the distance; `1` is the `+ 1`
in the lag index type `Fin (N + 1)`. -/
theorem circLag_origin (N : ℕ) : Moment.circLag (0 : Fin (N + 1)) = 0 := by
  have hv : ((0 : Fin (N + 1)) : ℕ) = 0 := rfl
  unfold Moment.circLag
  rw [hv]
  omega

/-- `R.p d ≤ 1` at every lag, since the normalised weights are nonnegative and sum to one. This is
what caps the near lags when a decay condition is assumed only beyond a cut.

DERIVED: `1` occurs twice, as the `+ 1` in the lag index type `Fin (N + 1)` and as the bound, which
is the total the weights sum to. -/
theorem p_le_one {N : ℕ} (R : Moment.Read N) (d : Fin (N + 1)) : R.p d ≤ 1 := by
  have h := Finset.single_le_sum (f := fun d' : Fin (N + 1) => R.p d')
    (fun d' _ => R.p_nonneg d') (Finset.mem_univ d)
  rwa [R.p_sum] at h

/-- `R.ρ 0 ≤ ∑ d, R.ρ d`: the contact weight is at most the total mass, from nonnegativity of the
profile alone. This is why a contact-relative bound needs no mass floor — the contact term
normalises the read from inside.

DERIVED: `0` is the contact lag index. -/
theorem contact_le_total {N : ℕ} (R : Moment.Read N) : R.ρ 0 ≤ ∑ d, R.ρ d :=
  Finset.single_le_sum (f := fun d : Fin (N + 1) => R.ρ d) (fun d _ => R.hρ d)
    (Finset.mem_univ (0 : Fin (N + 1)))

/-- If `0 ≤ A` and `R.ρ d ≤ A * R.ρ 0`, then `R.p d ≤ A`: dividing by the total mass gives
`p d ≤ A * (ρ 0 / ∑ ρ)`, and `contact_le_total` makes the bracket at most `1`.

DERIVED: `1` is the `+ 1` in the lag index type `Fin (N + 1)`; `0` occurs twice, as the lower bound
on `A` and as the contact lag index. -/
theorem p_le_of_contact_relative {N : ℕ} (R : Moment.Read N) {d : Fin (N + 1)} {A : ℝ}
    (hA : 0 ≤ A) (h : R.ρ d ≤ A * R.ρ 0) : R.p d ≤ A := by
  have hS : (0 : ℝ) < ∑ d', R.ρ d' := R.hpos
  show R.ρ d / (∑ d', R.ρ d') ≤ A
  rw [div_le_iff₀ hS]
  calc R.ρ d ≤ A * R.ρ 0 := h
    _ ≤ A * ∑ d', R.ρ d' := mul_le_mul_of_nonneg_left (contact_le_total R) hA

/-- `((scaleRead R ht).ρ d ≤ A * (scaleRead R ht).ρ 0) ↔ (R.ρ d ≤ A * R.ρ 0)`: both sides carry one
factor of the rescaling, so `ρ ↦ t * ρ` leaves the condition unchanged, as it leaves the far share
and the moment unchanged (`farShare_scale_invariant`, `circ_moment_scale_invariant`).

DERIVED: `0` occurs three times — the strict lower bound on the rescaling factor `t`, and the contact
lag index on each side of the equivalence; `1` is the `+ 1` in the lag index type `Fin (N + 1)`. -/
theorem contact_relative_scale_invariant {N : ℕ} (R : Moment.Read N) {t : ℝ} (ht : 0 < t)
    (d : Fin (N + 1)) (A : ℝ) :
    ((scaleRead R ht).ρ d ≤ A * (scaleRead R ht).ρ 0) ↔ (R.ρ d ≤ A * R.ρ 0) := by
  show (t * R.ρ d ≤ A * (t * R.ρ 0)) ↔ _
  constructor
  · intro h
    have h' : t * R.ρ d ≤ t * (A * R.ρ 0) := by linarith
    exact le_of_mul_le_mul_left h' ht
  · intro h
    have h' : t * R.ρ d ≤ t * (A * R.ρ 0) := mul_le_mul_of_nonneg_left h ht.le
    linarith

#print axioms contact_relative_scale_invariant

/-- `if k < m₀ + 1 then 1 else C / k ^ 4`: the weight envelope a contact-relative tail bound
produces — the trivial bound below the cut, and `C / k ^ 4` beyond it.

DERIVED: no numeral appears in the type. In the body, the first `1` is the `+ 1` writing the cut as
`m₀ + 1`, so the tail branch is never evaluated at `k = 0`; the second `1` is the value below the
cut, which `p_le_one` gives for every read rather than assuming anything about the correlation
there; `4` is the exponent, the smallest integer above the threshold `3` at which `∑ k ^ 2 * b k`
stops converging. `C` and `m₀` are the caller's. -/
noncomputable def quarticWeight (m₀ : ℕ) (C : ℝ) (k : ℕ) : ℝ :=
  if k < m₀ + 1 then 1 else C / (k : ℝ) ^ 4

theorem quarticWeight_nonneg (m₀ : ℕ) {C : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    0 ≤ quarticWeight m₀ C k := by
  unfold quarticWeight
  split
  · norm_num
  · exact div_nonneg hC (by positivity)

/-- `Summable (fun k => (k : ℝ) ^ 2 * quarticWeight m₀ C k)` for `0 ≤ C`: below the cut there are
finitely many terms, and beyond it the terms are `C / k ^ 2`.

DERIVED: `0` is the lower bound on `C`; the exponent `2` is the moment's own weight, which is what
the envelope has to beat. -/
theorem quarticWeight_summable (m₀ : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    Summable (fun k : ℕ => (k : ℝ) ^ 2 * quarticWeight m₀ C k) := by
  refine (summable_nat_add_iff (m₀ + 1)).mp ?_
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (by positivity) (quarticWeight_nonneg m₀ hC _))
    (fun n => ?_) (summable_inv_succ_sq.mul_left C)
  have hk : ((n + (m₀ + 1) : ℕ) : ℝ) = (n : ℝ) + (m₀ : ℝ) + 1 := by push_cast; ring
  have hlt : ¬ (n + (m₀ + 1) < m₀ + 1) := by omega
  have hval : quarticWeight m₀ C (n + (m₀ + 1)) = C / ((n : ℝ) + (m₀ : ℝ) + 1) ^ 4 := by
    unfold quarticWeight
    rw [if_neg hlt, hk]
  have hm : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have h2 : (0 : ℝ) < (n : ℝ) + (m₀ : ℝ) + 1 := by linarith
  show ((n + (m₀ + 1) : ℕ) : ℝ) ^ 2 * quarticWeight m₀ C (n + (m₀ + 1))
      ≤ C * (1 / ((n : ℝ) + 1) ^ 2)
  rw [hval, hk]
  have hrw : ((n : ℝ) + (m₀ : ℝ) + 1) ^ 2 * (C / ((n : ℝ) + (m₀ : ℝ) + 1) ^ 4)
      = C / ((n : ℝ) + (m₀ : ℝ) + 1) ^ 2 := by
    field_simp
  rw [hrw, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + (m₀ : ℝ) + 1) ^ 2 := by nlinarith [hm, hn]
  exact mul_le_mul_of_nonneg_left hsq hC

/-- If `0 ≤ C` and `R.ρ d ≤ C * R.ρ 0 / (circLag d : ℝ) ^ 4` at every lag with `m₀ ≤ circLag d`, then
`∑ d, R.p d * (circLag d : ℝ) ^ 2 ≤ 2 * ∑' k, (k : ℝ) ^ 2 * quarticWeight m₀ C k`.

`p_le_of_contact_relative` turns the hypothesis into a bound on the normalised weights and
`p_le_one` caps the near lags, so the whole profile is under `quarticWeight m₀ C`;
`Moment.sum_circLag_le_two_mul` then costs a factor of two.

Scope: nothing is assumed below the cut, and no normalisation or lower bound on the total mass
appears. The proof invokes the hypothesis only at `circLag d ≥ m₀ + 1`, so its lag-zero instance is
never used — which matters at `m₀ = 0`, where the hypothesis as written covers `circLag d = 0` and
the fourth power vanishes there, degenerating to `ρ 0 ≤ 0`. The intended cut is `m₀ ≥ 1`, and the
conclusion does not depend on which.

DERIVED: `0` occurs twice, as the lower bound on `C` and as the contact lag index; `1` is the `+ 1`
in the lag index type `Fin (N + 1)`; `4` is the envelope's exponent; `2` occurs three times — the
exponent on the circle lag in the moment, the circle lag's multiplicity from
`Moment.sum_circLag_le_two_mul`, and the exponent in the envelope's own weighted sum. -/
theorem circ_moment_le_of_contact_relative {N : ℕ} (R : Moment.Read N) (m₀ : ℕ) {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ d : Fin (N + 1), m₀ ≤ Moment.circLag d →
      R.ρ d ≤ C * R.ρ 0 / (Moment.circLag d : ℝ) ^ 4) :
    ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2
      ≤ 2 * ∑' k : ℕ, (k : ℝ) ^ 2 * quarticWeight m₀ C k := by
  refine circ_moment_le_of_weight_envelope R (quarticWeight m₀ C)
    (fun k => quarticWeight_nonneg m₀ hC k) (fun d => ?_) (quarticWeight_summable m₀ hC)
  by_cases hk : Moment.circLag d < m₀ + 1
  · have hval : quarticWeight m₀ C (Moment.circLag d) = 1 := by
      unfold quarticWeight
      rw [if_pos hk]
    rw [hval]
    exact p_le_one R d
  · have hge : m₀ ≤ Moment.circLag d := by omega
    have hval : quarticWeight m₀ C (Moment.circLag d) = C / (Moment.circLag d : ℝ) ^ 4 := by
      unfold quarticWeight
      rw [if_neg hk]
    rw [hval]
    refine p_le_of_contact_relative R (A := C / (Moment.circLag d : ℝ) ^ 4)
      (div_nonneg hC (by positivity)) ?_
    calc R.ρ d ≤ C * R.ρ 0 / (Moment.circLag d : ℝ) ^ 4 := h d hge
      _ = C / (Moment.circLag d : ℝ) ^ 4 * R.ρ 0 := by ring

#print axioms circ_moment_le_of_contact_relative

/-- `∃ B, ∀ N β, d2At N β ≤ B` from one cut `m₀` and one constant `C ≥ 0` such that
`wilsonCorrAt N β d ≤ C * wilsonCorrAt N β 0 / (circLag d : ℝ) ^ 4` at every aperture, coupling and
lag with `m₀ ≤ circLag d`. The witness is `2 * ∑' k, k ^ 2 * quarticWeight m₀ C k`, from
`circ_moment_le_of_contact_relative`.

Scope: the hypothesis mentions no normalisation, total mass or rate, only the correlation relative
to its own value at lag zero. The cut is meant at `m₀ ≥ 1`; see
`circ_moment_le_of_contact_relative` for why the lag-zero instance is never used. The axiom
footprint carries `wilson_reflection_positive_at`, from which `readYMAt` is constructed.

DERIVED: `0` occurs twice, as the lower bound on `C` and as the contact lag index; `1` is the `+ 1`
in the lag index type `Fin (N + 1)`; `4` is the exponent of the power law. -/
theorem substrate_of_contact_relative_decay (m₀ : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)), m₀ ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d
        ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4) :
    ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B :=
  ⟨2 * ∑' k : ℕ, (k : ℝ) ^ 2 * quarticWeight m₀ C k, fun N β =>
    circ_moment_le_of_contact_relative (MassGap.readYMAt N β) m₀ hC
      (fun d hd => by simpa only [readYMAt_rho] using h N (max β 0) d hd)⟩

#print axioms substrate_of_contact_relative_decay

/-- `∀ᶠ N in atTop, ∀ β, μYMAt N β < κ₀YM` from the same contact-relative power law, by
`MassGap.confinement_of_bounded_substrate` at `substrate_of_contact_relative_decay`.

DERIVED: `0` occurs twice, as the lower bound on `C` and as the contact lag index; `1` is the `+ 1`
in the lag index type; `4` is the exponent of the power law. -/
theorem confinement_of_contact_relative_decay (m₀ : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)), m₀ ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d
        ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, MassGap.μYMAt N β < MassGap.κ₀YM :=
  MassGap.confinement_of_bounded_substrate (substrate_of_contact_relative_decay m₀ C hC h)

#print axioms confinement_of_contact_relative_decay

/-- `WilsonModel.existence_and_gap_of_substrate` with its hypothesis supplied by
`substrate_of_contact_relative_decay`: from the power law there is a substrate witness `hsub` such
that `WilsonModel.wilsonOfSubstrate hsub` has its mode sum tending to `0` at every coupling,
`gap.μ β - gap.κ < 0` at every coupling, and `gap.R` constant.

DERIVED: `0` occurs four times — the lower bound on `C`, the contact lag index, the limit point of
the mode sum, and the comparison point in `gap.μ β - gap.κ < 0`; `1` is the `+ 1` in the lag index
type; `4` is the exponent of the power law. -/
theorem yang_mills_of_contact_relative_decay (m₀ : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)), m₀ ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d
        ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4) :
    ∃ hsub : (∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B),
      ((∀ β, Filter.Tendsto
            (fun τ => ‖∑ k ∈ (MassGap.WilsonModel.wilsonOfSubstrate hsub).model.gap.s β,
              (MassGap.WilsonModel.wilsonOfSubstrate hsub).model.gap.P β k
                * ((MassGap.WilsonModel.wilsonOfSubstrate hsub).model.gap.m β k) ^ τ‖)
          Filter.atTop (nhds 0)) ∧
        (∀ β, (MassGap.WilsonModel.wilsonOfSubstrate hsub).model.gap.μ β
            - (MassGap.WilsonModel.wilsonOfSubstrate hsub).model.gap.κ < 0) ∧
        (∀ d d', (MassGap.WilsonModel.wilsonOfSubstrate hsub).model.gap.R d
            = (MassGap.WilsonModel.wilsonOfSubstrate hsub).model.gap.R d')) := by
  refine ⟨substrate_of_contact_relative_decay m₀ C hC h, ?_⟩
  exact (MassGap.WilsonModel.existence_and_gap_of_substrate
    (substrate_of_contact_relative_decay m₀ C hC h)).1

#print axioms yang_mills_of_contact_relative_decay

/-! ### The same statement at exponent eight

The perturbative short-distance form of the connected `F²` correlation is `ρ d ∼ g ^ 4 / d ^ 8`, and
`ρ 0` carries the same `g ^ 4`, so the ratio `ρ d / ρ 0` is a power law with no leading coupling
dependence. `8` is five above the threshold `3`. The two statements below make the exponent explicit:
the eighth power with some constant, uniform in aperture and coupling, suffices. -/

/-- `∃ B, ∀ N β, d2At N β ≤ B` from `wilsonCorrAt N β d ≤ C * wilsonCorrAt N β 0 / (circLag d) ^ 8`
beyond a cut. Beyond a lag of one the eighth power exceeds the fourth, so the hypothesis implies the
one `substrate_of_contact_relative_decay` takes.

Scope: any exponent above `3` would serve; `8` is the one the short-distance form of the connected
plaquette correlation carries, with a constant that is coupling-free at leading order. The
hypothesis still requires one `C` covering every coupling.

DERIVED: `0` occurs twice, as the lower bound on `C` and as the contact lag index; `1` is the `+ 1`
in the lag index type `Fin (N + 1)`; `8` is the exponent. -/
theorem substrate_of_inverse_eighth_decay (m₀ : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)), m₀ ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d
        ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 8) :
    ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B := by
  refine substrate_of_contact_relative_decay (m₀ + 1) C hC ?_
  intro N β d hd
  have hk1 : 1 ≤ Moment.circLag d := by omega
  have hk : (1 : ℝ) ≤ (Moment.circLag d : ℝ) := by exact_mod_cast hk1
  have hpos : (0 : ℝ) < (Moment.circLag d : ℝ) := by linarith
  -- Only the lag-zero value is needed, and that is the plaquette-energy variance
  -- (`PlaqVariance.corrClay_zero_pos`, foundational-only), not reflection positivity.
  -- DERIVED: the index `0` is the lag the variance sits at; no value.
  have h0 : 0 ≤ MassGap.wilsonCorrAt N β 0 := (MassGap.PlaqVariance.corrClay_zero_pos N β).le
  have hCρ : 0 ≤ C * MassGap.wilsonCorrAt N β 0 := mul_nonneg hC h0
  have h2 : (1 : ℝ) ≤ (Moment.circLag d : ℝ) ^ 2 := by nlinarith [hk]
  have h4 : (1 : ℝ) ≤ (Moment.circLag d : ℝ) ^ 4 := by nlinarith [h2]
  have hpow : (Moment.circLag d : ℝ) ^ 4 ≤ (Moment.circLag d : ℝ) ^ 8 := by nlinarith [h4]
  have hle : C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 8
      ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hCρ, hpow]
  exact le_trans (h N β d (by omega)) hle

#print axioms substrate_of_inverse_eighth_decay

/-- `WilsonModel.existence_and_gap_of_substrate` with its hypothesis supplied by
`substrate_of_inverse_eighth_decay`: the same three conclusions as
`yang_mills_of_contact_relative_decay`, from the exponent-eight form of the power law.

DERIVED: `0` occurs four times — the lower bound on `C`, the contact lag index, the limit point of
the mode sum, and the comparison point in `gap.μ β - gap.κ < 0`; `1` is the `+ 1` in the lag index
type; `8` is the exponent. -/
theorem yang_mills_of_inverse_eighth_decay (m₀ : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)), m₀ ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d
        ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 8) :
    ∃ hsub : (∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B),
      ((∀ β, Filter.Tendsto
            (fun τ => ‖∑ k ∈ (MassGap.WilsonModel.wilsonOfSubstrate hsub).model.gap.s β,
              (MassGap.WilsonModel.wilsonOfSubstrate hsub).model.gap.P β k
                * ((MassGap.WilsonModel.wilsonOfSubstrate hsub).model.gap.m β k) ^ τ‖)
          Filter.atTop (nhds 0)) ∧
        (∀ β, (MassGap.WilsonModel.wilsonOfSubstrate hsub).model.gap.μ β
            - (MassGap.WilsonModel.wilsonOfSubstrate hsub).model.gap.κ < 0) ∧
        (∀ d d', (MassGap.WilsonModel.wilsonOfSubstrate hsub).model.gap.R d
            = (MassGap.WilsonModel.wilsonOfSubstrate hsub).model.gap.R d')) := by
  refine ⟨substrate_of_inverse_eighth_decay m₀ C hC h, ?_⟩
  exact (MassGap.WilsonModel.existence_and_gap_of_substrate
    (substrate_of_inverse_eighth_decay m₀ C hC h)).1

#print axioms yang_mills_of_inverse_eighth_decay

/-! ### The far-share envelope the law produces

The reduction above runs through the weight envelope. The same hypothesis also produces an explicit
far-share envelope, the parametrisation `ContactDominance` states its threshold in: a quartic
contact-relative law gives

    farShare R m ≤ (2 * C / 3) / m ^ 3        for `m` above the cut and above `1`

(`farShare_le_of_contact_relative`), and `3` is one power above the share threshold `2` that
`ContactDominance.square_share_is_not_enough` shows does not suffice. The `1 / 3` is the telescoped
total of the fourth power and the `2` is the circle lag's multiplicity.

The tail sum is bounded by telescoping rather than by an integral comparison, so the constant is
exact at every finite aperture: `1 / (u+1) ^ 4 ≤ 1 / (3 * u ^ 3) - 1 / (3 * (u+1) ^ 3)`
(`quartic_step`), whose surplus is `(6u^2 + 4u + 1) / (3 u^3 (u+1)^4)`. -/

/-- `1 / (u + 1) ^ 4 ≤ 1 / (3 * u ^ 3) - 1 / (3 * (u + 1) ^ 3)` for `0 < u`: one step of the
telescope for the quartic tail. The surplus `(6 * u ^ 2 + 4 * u + 1) / (3 * u ^ 3 * (u + 1) ^ 4)` is
exhibited in the proof.

DERIVED: `0` is the strict lower bound on `u`. `1` occurs five times — the numerator of each of the
three fractions, and the `+ 1` in each of the two copies of `(u + 1)`. `4` is the exponent being
telescoped. `3` occurs four times — the coefficient and the exponent in each of the two terms of the
telescope, and it is the exponent the fourth power integrates to, since
`d/du (-1 / (3 * u ^ 3)) = 1 / u ^ 4`. -/
theorem quartic_step {u : ℝ} (hu : 0 < u) :
    1 / (u + 1) ^ 4 ≤ 1 / (3 * u ^ 3) - 1 / (3 * (u + 1) ^ 3) := by
  have hu1 : (0 : ℝ) < u + 1 := by linarith
  have hne : u ≠ 0 := ne_of_gt hu
  have hne1 : u + 1 ≠ 0 := ne_of_gt hu1
  have h3 : (0 : ℝ) < u ^ 3 := pow_pos hu 3
  have h4 : (0 : ℝ) < (u + 1) ^ 4 := pow_pos hu1 4
  rw [← sub_nonneg]
  have hexp : 1 / (3 * u ^ 3) - 1 / (3 * (u + 1) ^ 3) - 1 / (u + 1) ^ 4
      = (6 * u ^ 2 + 4 * u + 1) / (3 * u ^ 3 * (u + 1) ^ 4) := by
    field_simp
    ring
  rw [hexp]
  have hnum : (0 : ℝ) ≤ 6 * u ^ 2 + 4 * u + 1 := by nlinarith [hu]
  have hden : (0 : ℝ) < 3 * u ^ 3 * (u + 1) ^ 4 :=
    mul_pos (mul_pos (by norm_num) h3) h4
  exact div_nonneg hnum hden.le

/-- `∑ i ∈ Finset.range K, 1 / (x + 1 + i) ^ 4 ≤ 1 / (3 * x ^ 3)` at every finite `K`, for `0 < x`,
by telescoping `quartic_step`. No integral comparison and no limit is taken, so the bound holds at
every finite `K` rather than in the limit.

DERIVED: `0` is the strict lower bound on `x`. `1` occurs three times — the numerator on each side
and the `+ 1` in the summand's argument. `4` is the exponent being summed; `3` occurs twice, as the
coefficient and the exponent of the telescoped total. -/
theorem inv_quartic_tail {x : ℝ} (hx : 0 < x) (K : ℕ) :
    ∑ i ∈ Finset.range K, 1 / (x + 1 + (i : ℝ)) ^ 4 ≤ 1 / (3 * x ^ 3) := by
  have hgen : ∀ J : ℕ, ∑ i ∈ Finset.range J, 1 / (x + 1 + (i : ℝ)) ^ 4
      ≤ 1 / (3 * x ^ 3) - 1 / (3 * (x + (J : ℝ)) ^ 3) := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
        have hJ : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
        have hu : (0 : ℝ) < x + (J : ℝ) := by linarith
        have hkey := quartic_step hu
        have h1 : x + (J : ℝ) + 1 = x + 1 + (J : ℝ) := by ring
        rw [h1] at hkey
        have hcast : ((J + 1 : ℕ) : ℝ) = (J : ℝ) + 1 := by push_cast; ring
        rw [Finset.sum_range_succ, hcast]
        have h2 : x + ((J : ℝ) + 1) = x + 1 + (J : ℝ) := by ring
        rw [h2]
        linarith [ih, hkey]
  have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have huu : (0 : ℝ) < x + (K : ℝ) := by linarith
  have hpos : (0 : ℝ) < 1 / (3 * (x + (K : ℝ)) ^ 3) := by
    refine div_pos one_pos ?_
    have h3 := pow_pos huu 3
    linarith
  linarith [hgen K]

/-- If `0 ≤ C` and `R.ρ d ≤ C * R.ρ 0 / (circLag d : ℝ) ^ 4` beyond the cut `m₀`, then
`farShare R m ≤ (2 * C / 3) / m ^ 3` at every `m` with `m₀ ≤ m` and `1 ≤ m`.
`Moment.sum_circLag_le_two_mul` costs the factor of two and `inv_quartic_tail` sums the tail.

DERIVED: `0` occurs twice, as the lower bound on `C` and as the contact lag index; `1` occurs twice,
as the `+ 1` in the lag index type `Fin (N + 1)` and as the lower bound on the cut `m`, which keeps
the denominator nonzero; `4` is the law's exponent; `2` is the circle lag's multiplicity; `3` occurs
twice, as the denominator of the constant — the quartic tail's telescoped total — and as the
resulting exponent, which is what one summation leaves of a quartic law. -/
theorem farShare_le_of_contact_relative {N : ℕ} (R : Moment.Read N) (m₀ : ℕ) {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ d : Fin (N + 1), m₀ ≤ Moment.circLag d →
      R.ρ d ≤ C * R.ρ 0 / (Moment.circLag d : ℝ) ^ 4)
    (m : ℕ) (hm₀ : m₀ ≤ m) (hm1 : 1 ≤ m) :
    farShare R m ≤ (2 * C / 3) / (m : ℝ) ^ 3 := by
  classical
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hg0 : ∀ k : ℕ, 0 ≤ (if m < k then C / (k : ℝ) ^ 4 else 0) := by
    intro k
    split
    · exact div_nonneg hC (by positivity)
    · exact le_refl 0
  have hstep1 : farShare R m
      ≤ ∑ d : Fin (N + 1), (if m < Moment.circLag d then C / (Moment.circLag d : ℝ) ^ 4 else 0) := by
    have hterm : ∀ d ∈ farSet N m,
        R.p d ≤ (if m < Moment.circLag d then C / (Moment.circLag d : ℝ) ^ 4 else 0) := by
      intro d hd
      simp only [farSet, Finset.mem_filter, Finset.mem_univ, true_and] at hd
      rw [if_pos hd]
      refine p_le_of_contact_relative R (A := C / (Moment.circLag d : ℝ) ^ 4)
        (div_nonneg hC (by positivity)) ?_
      calc R.ρ d ≤ C * R.ρ 0 / (Moment.circLag d : ℝ) ^ 4 := h d (by omega)
        _ = C / (Moment.circLag d : ℝ) ^ 4 * R.ρ 0 := by ring
    calc farShare R m
        ≤ ∑ d ∈ farSet N m,
            (if m < Moment.circLag d then C / (Moment.circLag d : ℝ) ^ 4 else 0) :=
          Finset.sum_le_sum hterm
      _ ≤ ∑ d : Fin (N + 1),
            (if m < Moment.circLag d then C / (Moment.circLag d : ℝ) ^ 4 else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun d _ _ => hg0 _)
  have hstep2 := Moment.sum_circLag_le_two_mul (N := N)
    (fun k => if m < k then C / (k : ℝ) ^ 4 else 0) hg0
  have hfilter : (Finset.range (N + 2)).filter (fun k => m < k) = Finset.Ico (m + 1) (N + 2) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  have htail : ∑ k ∈ Finset.range (N + 2), (if m < k then C / (k : ℝ) ^ 4 else 0)
      ≤ C * (1 / (3 * (m : ℝ) ^ 3)) := by
    have he1 : ∑ k ∈ Finset.range (N + 2), (if m < k then C / (k : ℝ) ^ 4 else 0)
        = ∑ k ∈ Finset.Ico (m + 1) (N + 2), C / (k : ℝ) ^ 4 := by
      rw [← hfilter, Finset.sum_filter]
    have he2 : ∑ k ∈ Finset.Ico (m + 1) (N + 2), C / (k : ℝ) ^ 4
        = ∑ i ∈ Finset.range (N + 2 - (m + 1)), C / ((m : ℝ) + 1 + (i : ℝ)) ^ 4 := by
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hc : (((m + 1 + i : ℕ)) : ℝ) = (m : ℝ) + 1 + (i : ℝ) := by push_cast; ring
      rw [hc]
    have he3 : ∑ i ∈ Finset.range (N + 2 - (m + 1)), C / ((m : ℝ) + 1 + (i : ℝ)) ^ 4
        = C * ∑ i ∈ Finset.range (N + 2 - (m + 1)), 1 / ((m : ℝ) + 1 + (i : ℝ)) ^ 4 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [he1, he2, he3]
    exact mul_le_mul_of_nonneg_left (inv_quartic_tail hmpos _) hC
  have hfinal : (2 : ℝ) * (C * (1 / (3 * (m : ℝ) ^ 3))) = (2 * C / 3) / (m : ℝ) ^ 3 := by
    field_simp
  calc farShare R m
      ≤ ∑ d : Fin (N + 1),
          (if m < Moment.circLag d then C / (Moment.circLag d : ℝ) ^ 4 else 0) := hstep1
    _ ≤ 2 * ∑ k ∈ Finset.range (N + 2), (if m < k then C / (k : ℝ) ^ 4 else 0) := hstep2
    _ ≤ 2 * (C * (1 / (3 * (m : ℝ) ^ 3))) := by linarith [htail]
    _ = (2 * C / 3) / (m : ℝ) ^ 3 := hfinal

#print axioms farShare_le_of_contact_relative

/-- `(2 * C / 3) / m ^ 3`: the far-share envelope `farShare_le_of_contact_relative` produces from a
quartic contact-relative law. At `m = 0` the value is `0`;
`ContactDominance.substrate_of_tail_envelope`, which consumes it, reads it only above the cut.

DERIVED: no numeral appears in the type. In the body, `2` is the circle lag's multiplicity, the `3`
in the denominator of the constant is the quartic tail's telescoped total (`inv_quartic_tail`), and
the exponent `3` is what one summation leaves of a quartic law. -/
noncomputable def cubicShare (C : ℝ) (m : ℕ) : ℝ := (2 * C / 3) / (m : ℝ) ^ 3

theorem cubicShare_nonneg {C : ℝ} (hC : 0 ≤ C) (m : ℕ) : 0 ≤ cubicShare C m := by
  unfold cubicShare
  exact div_nonneg (by linarith) (by positivity)

/-- `Summable (fun m => (2 * m + 1) * cubicShare C m)` for `0 ≤ C`: the summand is `O(m ^ (-2))`,
which is what the share's threshold exponent `2` means.

DERIVED: `0` is the lower bound on `C`; `2` and `1` are the coefficient and offset of the layer
weight `2 * m + 1`. -/
theorem cubicShare_summable {C : ℝ} (hC : 0 ≤ C) :
    Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * cubicShare C m) := by
  refine (summable_nat_add_iff 1).mp ?_
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (by positivity) (cubicShare_nonneg hC _))
    (fun n => ?_) (summable_inv_succ_sq.mul_left (2 * C))
  have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  show (2 * ((n + 1 : ℕ) : ℝ) + 1) * cubicShare C (n + 1) ≤ 2 * C * (1 / ((n : ℝ) + 1) ^ 2)
  unfold cubicShare
  rw [hc, ← sub_nonneg]
  have hexp : 2 * C * (1 / ((n : ℝ) + 1) ^ 2)
      - (2 * ((n : ℝ) + 1) + 1) * ((2 * C / 3) / ((n : ℝ) + 1) ^ 3)
      = (2 * C * (n : ℝ)) / (3 * ((n : ℝ) + 1) ^ 3) := by
    field_simp
    ring
  rw [hexp]
  exact div_nonneg (mul_nonneg (by linarith) hn) (by positivity)

/-- `∃ B, ∀ N β, d2At N β ≤ B` from the same contact-relative power law as
`substrate_of_contact_relative_decay`, routed through `ContactDominance.substrate_of_tail_envelope`
with the explicit profile `cubicShare C`, whose weighted total converges by
`cubicShare_summable`.

Scope: the same hypothesis and the same conclusion as `substrate_of_contact_relative_decay`, in a
different parametrisation. The envelope's exponent `3` is one above the share threshold `2` that
`ContactDominance.square_share_is_not_enough` shows does not suffice.

DERIVED: `0` occurs twice, as the lower bound on `C` and as the contact lag index; `1` is the `+ 1`
in the lag index type `Fin (N + 1)`; `4` is the law's exponent. -/
theorem substrate_of_contact_relative_share (m₀ : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)), m₀ ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d
        ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4) :
    ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B :=
  substrate_of_tail_envelope (max m₀ 1) (cubicShare C) (cubicShare_nonneg hC)
    (cubicShare_summable hC)
    (fun N β m hm =>
      farShare_le_of_contact_relative (MassGap.readYMAt N β) m₀ hC
        (fun d hd => by simpa only [readYMAt_rho] using h N (max β 0) d hd) m
        (le_trans (le_max_left m₀ 1) hm) (le_trans (le_max_right m₀ 1) hm))

#print axioms substrate_of_contact_relative_share

/-! ### A read satisfying the contact-relative condition, and one failing it -/

/-- `ContactDominance.contactRead N` meets the contact-relative condition at `C = 0` beyond lag one,
and its circular second moment is `0`. All its weight sits at lag zero, so every other weight
vanishes.

So the hypothesis of `circ_moment_le_of_contact_relative` is satisfiable.

DERIVED: `1` occurs twice, as the `+ 1` in the lag index type `Fin (N + 1)` and as the cut beyond
which the condition is asked; `0` occurs three times — the constant `C` at which the read meets the
condition, the contact lag index, and the value of the moment; `4` is the condition's exponent; `2`
is the exponent on the circle lag in the moment. -/
theorem contact_relative_nonvacuous (N : ℕ) :
    (∀ d : Fin (N + 1), 1 ≤ Moment.circLag d →
        (contactRead N).ρ d
          ≤ (0 : ℝ) * (contactRead N).ρ 0 / (Moment.circLag d : ℝ) ^ 4) ∧
      ∑ d, (contactRead N).p d * (Moment.circLag d : ℝ) ^ 2 = 0 := by
  refine ⟨fun d hd => ?_, contactRead_moment N⟩
  have hne : d ≠ 0 := by
    intro hz
    rw [hz, circLag_origin N] at hd
    omega
  have hval : (contactRead N).ρ d = 0 := by
    show (if d = 0 then (1 : ℝ) else 0) = 0
    rw [if_neg hne]
  rw [hval]
  norm_num

#print axioms contact_relative_nonvacuous

/-- Two facts about `ContactDominance.midRead`, conjoined: at every constant `C` and every cut `m₀`
there are an aperture and a lag beyond the cut at which
`C * (midRead N).ρ 0 / (circLag d) ^ 4 < (midRead N).ρ d`; and its circular second moments exceed
every `B`.

`midRead` puts all its weight at the antipode and none at lag zero, so its contact value is `0` and
the right side vanishes while the left is `1`, whatever `C` is.

So the contact-relative hypothesis of `circ_moment_le_of_contact_relative` is used, and it asks for
something a share condition does not: weight at short lags.

DERIVED: `1` is the `+ 1` in the lag index type `Fin (N + 1)`; `0` is the contact lag index; `4` is
the condition's exponent; `2` is the exponent on the circle lag in the moment. -/
theorem contact_relative_load_bearing :
    (∀ (C : ℝ) (m₀ : ℕ), ∃ (N : ℕ) (d : Fin (N + 1)), m₀ ≤ Moment.circLag d ∧
        C * (midRead N).ρ 0 / (Moment.circLag d : ℝ) ^ 4 < (midRead N).ρ d) ∧
      (∀ B : ℝ, ∃ N : ℕ, B < ∑ d, (midRead N).p d * (Moment.circLag d : ℝ) ^ 2) := by
  refine ⟨fun C m₀ => ⟨2 * m₀ + 1, midLag (2 * m₀ + 1), ?_, ?_⟩, doubling_load_bearing.2⟩
  · rw [circLag_midLag]
    omega
  · have hv0 : ((0 : Fin (2 * m₀ + 1 + 1)) : ℕ) = 0 := rfl
    have hvm : ((midLag (2 * m₀ + 1) : Fin (2 * m₀ + 1 + 1)) : ℕ) = (2 * m₀ + 1 + 1) / 2 := rfl
    have hne : (0 : Fin (2 * m₀ + 1 + 1)) ≠ midLag (2 * m₀ + 1) := by
      intro hz
      have hval : ((0 : Fin (2 * m₀ + 1 + 1)) : ℕ)
          = ((midLag (2 * m₀ + 1) : Fin (2 * m₀ + 1 + 1)) : ℕ) := by rw [hz]
      rw [hv0, hvm] at hval
      omega
    have hρ0 : (midRead (2 * m₀ + 1)).ρ (0 : Fin (2 * m₀ + 1 + 1)) = 0 := by
      show (if (0 : Fin (2 * m₀ + 1 + 1)) = midLag (2 * m₀ + 1) then (1 : ℝ) else 0) = 0
      rw [if_neg hne]
    have hρm : (midRead (2 * m₀ + 1)).ρ (midLag (2 * m₀ + 1)) = 1 := by
      show (if midLag (2 * m₀ + 1) = midLag (2 * m₀ + 1) then (1 : ℝ) else 0) = 1
      rw [if_pos rfl]
    rw [hρ0, hρm]
    norm_num

#print axioms contact_relative_load_bearing

/-! ### The threshold exponent is exactly three

The family below meets the contact-relative condition at exponent `3` with constant `1` at every
aperture and every cut, and its moments are unbounded. So the exponent `4` in
`circ_moment_le_of_contact_relative` cannot be lowered to `3`. It is the counterpart of
`ContactDominance.square_share_is_not_enough` one exponent up, because the share has already absorbed
a summation. -/

/-- The read on `Fin (2 * k + 1 + 1)` with profile `1 / (d + 1) ^ 3` at every lag `d ≤ k + 1` and `0`
beyond. Its total mass is under `2` (`cubeRead_mass_le`) and its circular second moments are
unbounded (`cubeRead_moment_unbounded`).

DERIVED: `2` and `1` in the type are the aperture `2 * k + 1`, the even period the antipode needs.
In the body, `1` in the numerator is the contact value the profile is measured against, which `p`
normalises away; the `+ 1` in `(d + 1)` keeps the denominator nonzero at `d = 0`; `k + 1` is the
antipode of the period `2 * k + 2`, the largest lag at which the circle distance equals the index;
`3` is the threshold exponent, at which `∑ k ^ 2 * b k` stops converging; `0` is the weight beyond
the antipode. -/
noncomputable def cubeRead (k : ℕ) : Moment.Read (2 * k + 1) where
  ρ := fun d => if (d : ℕ) ≤ k + 1 then 1 / (((d : ℕ) : ℝ) + 1) ^ 3 else 0
  hρ := fun d => by
    split
    · positivity
    · exact le_refl 0
  hpos := by
    have hnn : ∀ d : Fin (2 * k + 1 + 1),
        (0 : ℝ) ≤ (if (d : ℕ) ≤ k + 1 then 1 / (((d : ℕ) : ℝ) + 1) ^ 3 else 0) := by
      intro d
      split
      · positivity
      · exact le_refl 0
    have hle := Finset.single_le_sum
      (f := fun d : Fin (2 * k + 1 + 1) =>
        (if (d : ℕ) ≤ k + 1 then 1 / (((d : ℕ) : ℝ) + 1) ^ 3 else 0))
      (fun d _ => hnn d) (Finset.mem_univ (0 : Fin (2 * k + 1 + 1)))
    have hval : (if ((0 : Fin (2 * k + 1 + 1)) : ℕ) ≤ k + 1
        then 1 / ((((0 : Fin (2 * k + 1 + 1)) : ℕ) : ℝ) + 1) ^ 3 else 0) = 1 := by
      have hv : ((0 : Fin (2 * k + 1 + 1)) : ℕ) = 0 := rfl
      rw [hv, if_pos (by omega)]
      norm_num
    rw [hval] at hle
    show (0 : ℝ) < ∑ d : Fin (2 * k + 1 + 1),
      (if (d : ℕ) ≤ k + 1 then 1 / (((d : ℕ) : ℝ) + 1) ^ 3 else 0)
    linarith

/-- `∑ d, (cubeRead k).ρ d * g (circLag d) = ∑ j ∈ Finset.range (k + 2), 1 / (j + 1) ^ 3 * g j` at
every `g`: the profile vanishes past the antipode, and on the near range the circle lag equals the
index, so every sum against the circle lag collapses to a sum over `Finset.range (k + 2)`.

DERIVED: `2` occurs twice, as the coefficient in the aperture `2 * k + 1` and as the `+ 2` bounding
the collapsed range at the antipode; `1` occurs three times — the offset in the aperture, the `+ 1`
in the index type, and the numerator of the profile; `3` is the profile's exponent. -/
theorem cubeRead_sum_eq (k : ℕ) (g : ℕ → ℝ) :
    ∑ d : Fin (2 * k + 1 + 1), (cubeRead k).ρ d * g (Moment.circLag d)
      = ∑ j ∈ Finset.range (k + 2), 1 / ((j : ℝ) + 1) ^ 3 * g j := by
  classical
  have hfin : ∑ d : Fin (2 * k + 1 + 1), (cubeRead k).ρ d * g (Moment.circLag d)
      = ∑ j ∈ Finset.range (2 * k + 1 + 1),
          (if j ≤ k + 1 then 1 / ((j : ℝ) + 1) ^ 3 else 0) * g (min j (2 * k + 1 + 1 - j)) :=
    Fin.sum_univ_eq_sum_range
      (fun j => (if j ≤ k + 1 then 1 / ((j : ℝ) + 1) ^ 3 else 0) * g (min j (2 * k + 1 + 1 - j)))
      (2 * k + 1 + 1)
  rw [hfin]
  have hsub : Finset.range (k + 2) ⊆ Finset.range (2 * k + 1 + 1) := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  have hzero : ∀ j ∈ Finset.range (2 * k + 1 + 1), j ∉ Finset.range (k + 2) →
      (if j ≤ k + 1 then 1 / ((j : ℝ) + 1) ^ 3 else 0) * g (min j (2 * k + 1 + 1 - j)) = 0 := by
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

/-- `∑ d, (cubeRead k).ρ d ≤ 2`, by comparing `1 / (j + 1) ^ 3` with the telescoping weight.

DERIVED: `2` is the bound on the total mass. -/
theorem cubeRead_mass_le (k : ℕ) : ∑ d, (cubeRead k).ρ d ≤ 2 := by
  have hsum := cubeRead_sum_eq k (fun _ => 1)
  simp only [mul_one] at hsum
  rw [hsum]
  have hcmp : ∀ j ∈ Finset.range (k + 2),
      1 / ((j : ℝ) + 1) ^ 3 ≤ (if j = 0 then (1 : ℝ) else 0) + telWeight j := by
    intro j _
    rcases Nat.eq_zero_or_pos j with h0 | hp
    · subst h0
      rw [if_pos rfl]
      unfold telWeight
      norm_num
    · have hne : j ≠ 0 := Nat.pos_iff_ne_zero.mp hp
      have hj : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hp
      have h1 : (0 : ℝ) < (j : ℝ) := by linarith
      have h2 : (0 : ℝ) < (j : ℝ) + 1 := by linarith
      have hval : telWeight j = 1 / (j : ℝ) ^ 2 - 1 / ((j : ℝ) + 1) ^ 2 := by
        unfold telWeight
        rw [if_neg hne]
      have key : 1 / ((j : ℝ) + 1) ^ 3 ≤ 1 / (j : ℝ) ^ 2 - 1 / ((j : ℝ) + 1) ^ 2 := by
        rw [div_sub_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hj, h1, h2, pow_pos h1 3, pow_pos h1 4]
      rw [if_neg hne, zero_add, hval]
      exact key
  have hsum2 : ∑ j ∈ Finset.range (k + 2), ((if j = 0 then (1 : ℝ) else 0) + telWeight j) ≤ 2 := by
    have hone : ∑ j ∈ Finset.range (k + 2), (if j = 0 then (1 : ℝ) else 0) = 1 := by
      rw [Finset.sum_ite_eq' (Finset.range (k + 2)) 0 (fun _ => (1 : ℝ)),
        if_pos (Finset.mem_range.mpr (by omega))]
    have htel : ∑ j ∈ Finset.range (k + 2), telWeight j ≤ 1 := by
      have h := telWeight_sum (k + 1)
      rw [show k + 2 = (k + 1) + 1 from rfl, h]
      have hp : (0 : ℝ) < 1 / (((k + 1 : ℕ) : ℝ) + 1) ^ 2 := by positivity
      linarith
    rw [Finset.sum_add_distrib, hone]
    linarith
  linarith [Finset.sum_le_sum hcmp, hsum2]

/-- `((∑ j ∈ Finset.range (k + 2), 1 / (j + 1)) - 1) / 8 ≤ ∑ d, (cubeRead k).p d * (circLag d) ^ 2`:
the normalised squared-lag total dominates an eighth of the harmonic partial sum, less its first
term. The weight `j ^ 2 / (j + 1) ^ 3` is at least `1 / (4 * (j + 1))` for `j ≥ 1`, and the total
mass is at most `2` by `cubeRead_mass_le`.

DERIVED: `2` occurs twice, as the `+ 2` bounding the collapsed range at the antipode and as the
exponent on the circle lag; `1` occurs three times — the numerator of the harmonic term, the `+ 1` in
its denominator, and the first term subtracted off; `8` is the product of the weight's factor `4`
with the mass bound `2`. -/
theorem cubeRead_moment_ge (k : ℕ) :
    ((∑ j ∈ Finset.range (k + 2), 1 / ((j : ℝ) + 1)) - 1) / 8
      ≤ ∑ d, (cubeRead k).p d * (Moment.circLag d : ℝ) ^ 2 := by
  classical
  have hnum : ∑ d, (cubeRead k).ρ d * (Moment.circLag d : ℝ) ^ 2
      = ∑ j ∈ Finset.range (k + 2), 1 / ((j : ℝ) + 1) ^ 3 * (j : ℝ) ^ 2 :=
    cubeRead_sum_eq k (fun j => (j : ℝ) ^ 2)
  have hcmp : ∀ j ∈ Finset.range (k + 2),
      (1 / 4) * (1 / ((j : ℝ) + 1)) - (if j = 0 then (1 : ℝ) / 4 else 0)
        ≤ 1 / ((j : ℝ) + 1) ^ 3 * (j : ℝ) ^ 2 := by
    intro j _
    rcases Nat.eq_zero_or_pos j with h0 | hp
    · subst h0
      rw [if_pos rfl]
      norm_num
    · have hne : j ≠ 0 := Nat.pos_iff_ne_zero.mp hp
      rw [if_neg hne]
      have hj : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hp
      have h2 : (0 : ℝ) < (j : ℝ) + 1 := by linarith
      have hrw : 1 / ((j : ℝ) + 1) ^ 3 * (j : ℝ) ^ 2 = (j : ℝ) ^ 2 / ((j : ℝ) + 1) ^ 3 := by
        ring
      have hL : (1 : ℝ) / 4 * (1 / ((j : ℝ) + 1)) = 1 / (4 * ((j : ℝ) + 1)) := by
        field_simp
      rw [hrw, sub_zero, hL, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hj, h2, mul_nonneg (sub_nonneg.mpr hj) (sq_nonneg ((j : ℝ) + 1)),
        mul_nonneg (sub_nonneg.mpr hj) (sq_nonneg (j : ℝ))]
  have hdist : ∑ j ∈ Finset.range (k + 2),
      ((1 / 4) * (1 / ((j : ℝ) + 1)) - (if j = 0 then (1 : ℝ) / 4 else 0))
      = (1 / 4) * (∑ j ∈ Finset.range (k + 2), 1 / ((j : ℝ) + 1)) - 1 / 4 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq' (Finset.range (k + 2)) 0 (fun _ => (1 : ℝ) / 4),
      if_pos (Finset.mem_range.mpr (by omega))]
  have hlow : ((∑ j ∈ Finset.range (k + 2), 1 / ((j : ℝ) + 1)) - 1) / 4
      ≤ ∑ d, (cubeRead k).ρ d * (Moment.circLag d : ℝ) ^ 2 := by
    have h := Finset.sum_le_sum hcmp
    rw [hdist] at h
    rw [hnum]
    linarith
  have hH : (1 : ℝ) ≤ ∑ j ∈ Finset.range (k + 2), 1 / ((j : ℝ) + 1) := by
    have h := Finset.single_le_sum
      (f := fun j : ℕ => 1 / ((j : ℝ) + 1))
      (fun j _ => by positivity) (Finset.mem_range.mpr (by omega : 0 < k + 2))
    calc (1 : ℝ) = 1 / (((0 : ℕ) : ℝ) + 1) := by norm_num
      _ ≤ ∑ j ∈ Finset.range (k + 2), 1 / ((j : ℝ) + 1) := h
  have hmass := cubeRead_mass_le k
  have hmasspos : (0 : ℝ) < ∑ d, (cubeRead k).ρ d := (cubeRead k).hpos
  have hmomeq := circ_moment_eq_rho_ratio (cubeRead k)
  rw [hmomeq, le_div_iff₀ hmasspos]
  nlinarith [hlow, hmass, hmasspos, hH]

/-- `∃ k, B < ∑ d, (cubeRead k).p d * (circLag d) ^ 2` at every `B`: the harmonic partial sums in
`cubeRead_moment_ge` are unbounded.

DERIVED: `2` is the exponent on the circle lag. -/
theorem cubeRead_moment_unbounded (B : ℝ) :
    ∃ k : ℕ, B < ∑ d, (cubeRead k).p d * (Moment.circLag d : ℝ) ^ 2 := by
  have htend : Filter.Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range n, (1 / (i + 1) : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_sum_range_one_div_nat_succ_atTop
  have hev := htend.eventually_gt_atTop (8 * B + 1)
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨n, ?_⟩
  have hmono : ∑ i ∈ Finset.range n, (1 / (i + 1) : ℝ)
      ≤ ∑ i ∈ Finset.range (n + 2), (1 / (i + 1) : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (by intro j hj; simp only [Finset.mem_range] at hj ⊢; omega)
      (fun i _ _ => by positivity)
  have hcast : ∑ i ∈ Finset.range (n + 2), (1 / (i + 1) : ℝ)
      = ∑ j ∈ Finset.range (n + 2), 1 / ((j : ℝ) + 1) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [hcast] at hmono
  have hge := cubeRead_moment_ge n
  linarith

/-- Two facts about `cubeRead`, conjoined: it obeys the contact-relative condition at exponent `3`
with constant `1` beyond every lag of one, at every aperture; and its circular second moments exceed
every `B`.

So the exponent `4` in `circ_moment_le_of_contact_relative` cannot be lowered to `3`. It is the same
mechanism as `ContactDominance.square_share_is_not_enough` one exponent up: a profile `1 / k ^ s` has
squared-lag total `∑ k ^ 2 / k ^ s`, harmonic at `s = 3`, exactly as a square share has weighted
total `∑ (2m+1) / (m+1) ^ 2` at `s = 2`.

DERIVED: `2` occurs twice, as the coefficient in the aperture `2 * k + 1` and as the exponent on the
circle lag; `1` occurs four times — the offset in the aperture, the `+ 1` in the index type, the cut
beyond which the condition is asked, and the constant `C`; `0` is the contact lag index; `3` is the
exponent at which the condition is met. -/
theorem cubic_contact_relative_is_not_enough :
    (∀ (k : ℕ) (d : Fin (2 * k + 1 + 1)), 1 ≤ Moment.circLag d →
        (cubeRead k).ρ d
          ≤ (1 : ℝ) * (cubeRead k).ρ 0 / (Moment.circLag d : ℝ) ^ 3) ∧
      (∀ B : ℝ, ∃ k : ℕ, B < ∑ d, (cubeRead k).p d * (Moment.circLag d : ℝ) ^ 2) := by
  refine ⟨fun k d hd => ?_, cubeRead_moment_unbounded⟩
  have hρ0 : (cubeRead k).ρ (0 : Fin (2 * k + 1 + 1)) = 1 := by
    have hv : ((0 : Fin (2 * k + 1 + 1)) : ℕ) = 0 := rfl
    show (if ((0 : Fin (2 * k + 1 + 1)) : ℕ) ≤ k + 1
      then 1 / ((((0 : Fin (2 * k + 1 + 1)) : ℕ) : ℝ) + 1) ^ 3 else 0) = 1
    rw [hv, if_pos (by omega)]
    norm_num
  rw [hρ0, one_mul]
  by_cases hk : (d : ℕ) ≤ k + 1
  · have hclag : Moment.circLag d = (d : ℕ) := by
      have hlt : (d : ℕ) < 2 * k + 1 + 1 := d.isLt
      unfold Moment.circLag
      omega
    have hd1 : 1 ≤ (d : ℕ) := by rw [hclag] at hd; exact hd
    have hj : (1 : ℝ) ≤ ((d : ℕ) : ℝ) := by exact_mod_cast hd1
    have hdpos : (0 : ℝ) < ((d : ℕ) : ℝ) := by linarith
    have hval : (cubeRead k).ρ d = 1 / (((d : ℕ) : ℝ) + 1) ^ 3 := by
      show (if (d : ℕ) ≤ k + 1 then 1 / ((((d : ℕ)) : ℝ) + 1) ^ 3 else 0) = _
      rw [if_pos hk]
    rw [hval, hclag]
    rw [div_le_div_iff₀ (by positivity) (pow_pos hdpos 3)]
    nlinarith [hj]
  · have hval : (cubeRead k).ρ d = 0 := by
      show (if (d : ℕ) ≤ k + 1 then 1 / ((((d : ℕ)) : ℝ) + 1) ^ 3 else 0) = 0
      rw [if_neg hk]
    rw [hval]
    have hd1 : 1 ≤ Moment.circLag d := hd
    have hc : (1 : ℝ) ≤ (Moment.circLag d : ℝ) := by exact_mod_cast hd1
    positivity

#print axioms cubic_contact_relative_is_not_enough

/-- There is no `B` bounding the circular second moment of every read obeying the contact-relative
condition at exponent `3` with constant `1` from lag one upward: for each candidate `B`,
`cubic_contact_relative_is_not_enough` supplies a `cubeRead k` exceeding it.

Stated without the criterion's own constant, so nothing turns on how
`∑' k, k ^ 2 * quarticWeight m₀ C k` evaluates at the threshold.

DERIVED: `1` occurs three times — the `+ 1` in the lag index type `Fin (N + 1)`, the cut beyond which
the condition is asked, and the constant `C`; `0` is the contact lag index; `3` is the exponent at
which the condition is stated; `2` is the exponent on the circle lag in the moment. -/
theorem cubic_contact_relative_gives_no_bound :
    ¬ ∃ B : ℝ, ∀ (N : ℕ) (R : Moment.Read N),
        (∀ d : Fin (N + 1), 1 ≤ Moment.circLag d →
          R.ρ d ≤ (1 : ℝ) * R.ρ 0 / (Moment.circLag d : ℝ) ^ 3) →
        ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2 ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨k, hk⟩ := cubeRead_moment_unbounded B
  exact absurd (hB (2 * k + 1) (cubeRead k)
    (fun d hd => cubic_contact_relative_is_not_enough.1 k d hd)) (not_le.mpr hk)

#print axioms cubic_contact_relative_gives_no_bound

/-! ### A read satisfying the substrate hypothesis and failing the contact-relative condition

`Substrate.tailRead` has circular second moment at most `1` at every aperture, so it satisfies the
substrate hypothesis with `B = 1`, and admits no contact-relative bound at exponent `4` with any
constant: its far atom's weight falls off like `(k+1) ^ (-3)` while the condition asks for
`(k+1) ^ (-4)`. So the contact-relative reduction is a sufficient condition and not a restatement;
`substrate_iff_dyadic_shares` is the file's one equivalence. -/

/-- `(Substrate.tailRead k).ρ 0 = 1`: the tail read's unnormalised weight at lag zero.

DERIVED: `0` is the contact lag index; `2` and the first `1` are the aperture `2 * k + 1`; the second
`1` is the `+ 1` in the index type `Fin (2 * k + 1 + 1)`; the final `1` is the weight's value. -/
theorem tailRead_rho_zero (k : ℕ) : (MassGap.Substrate.tailRead k).ρ (0 : Fin (2 * k + 1 + 1)) = 1 := by
  have hne : (0 : Fin (2 * k + 1 + 1)) ≠ MassGap.Substrate.antipode k := by
    intro hz
    have hval : ((0 : Fin (2 * k + 1 + 1)) : ℕ)
        = ((MassGap.Substrate.antipode k : Fin (2 * k + 1 + 1)) : ℕ) := by rw [hz]
    have hv0 : ((0 : Fin (2 * k + 1 + 1)) : ℕ) = 0 := rfl
    have hva : ((MassGap.Substrate.antipode k : Fin (2 * k + 1 + 1)) : ℕ) = k + 1 := rfl
    rw [hv0, hva] at hval
    omega
  show (if (0 : Fin (2 * k + 1 + 1)) = 0 then (1 : ℝ) else 0)
      + (if (0 : Fin (2 * k + 1 + 1)) = MassGap.Substrate.antipode k
          then MassGap.Substrate.tailWeight k else 0) = 1
  rw [if_pos rfl, if_neg hne]
  ring

/-- `(Substrate.tailRead k).ρ (Substrate.antipode k) = Substrate.tailWeight k`: the tail read's
unnormalised weight at the antipode.

DERIVED: no numeral appears in the statement. -/
theorem tailRead_rho_antipode (k : ℕ) :
    (MassGap.Substrate.tailRead k).ρ (MassGap.Substrate.antipode k)
      = MassGap.Substrate.tailWeight k := by
  have hne : MassGap.Substrate.antipode k ≠ (0 : Fin (2 * k + 1 + 1)) := by
    intro hz
    have hval : ((MassGap.Substrate.antipode k : Fin (2 * k + 1 + 1)) : ℕ)
        = ((0 : Fin (2 * k + 1 + 1)) : ℕ) := by rw [hz]
    have hv0 : ((0 : Fin (2 * k + 1 + 1)) : ℕ) = 0 := rfl
    have hva : ((MassGap.Substrate.antipode k : Fin (2 * k + 1 + 1)) : ℕ) = k + 1 := rfl
    rw [hv0, hva] at hval
    omega
  show (if MassGap.Substrate.antipode k = 0 then (1 : ℝ) else 0)
      + (if MassGap.Substrate.antipode k = MassGap.Substrate.antipode k
          then MassGap.Substrate.tailWeight k else 0) = _
  rw [if_neg hne, if_pos rfl]
  ring

/-- Two facts about `Substrate.tailRead`, conjoined: its circular second moment is at most `1` at
every aperture; and no pair `(C, m₀)` makes it obey the contact-relative condition at exponent `4`.
At the antipode the condition reads `(k+1) ^ (-3) ≤ C * (k+1) ^ (-4)`, which forces `k + 1 ≤ C`.

So `substrate_of_contact_relative_decay` is a sufficient condition and not a restatement: a
correlation may satisfy the substrate hypothesis while its far weight falls off one power too slowly
for the condition to hold.

DERIVED: `2` occurs twice, as the exponent on the circle lag and as the coefficient in the aperture
`2 * k + 1`; `1` occurs three times — the bound on the moment, the offset in the aperture, and the
`+ 1` in the index type; `0` is the contact lag index; `4` is the exponent at which the condition is
denied. -/
theorem contact_relative_is_strictly_stronger :
    (∀ k : ℕ, ∑ d, (MassGap.Substrate.tailRead k).p d * (Moment.circLag d : ℝ) ^ 2 ≤ 1) ∧
      ¬ ∃ (C : ℝ) (m₀ : ℕ), ∀ (k : ℕ) (d : Fin (2 * k + 1 + 1)), m₀ ≤ Moment.circLag d →
          (MassGap.Substrate.tailRead k).ρ d
            ≤ C * (MassGap.Substrate.tailRead k).ρ 0 / (Moment.circLag d : ℝ) ^ 4 := by
  refine ⟨MassGap.Substrate.tailRead_moment_le_one, ?_⟩
  rintro ⟨C, m₀, hCm⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  refine absurd (hCm (n + m₀) (MassGap.Substrate.antipode (n + m₀)) ?_) ?_
  · rw [MassGap.Substrate.circLag_antipode]
    omega
  · rw [MassGap.Substrate.circLag_antipode, tailRead_rho_zero, tailRead_rho_antipode, mul_one]
    have hcast : (((n + m₀ + 1 : ℕ)) : ℝ) = (n : ℝ) + (m₀ : ℝ) + 1 := by push_cast; ring
    have hw : MassGap.Substrate.tailWeight (n + m₀)
        = 1 / (((n + m₀ : ℕ) : ℝ) + 1) ^ 3 := rfl
    have hm : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg _
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have hx : (((n + m₀ : ℕ) : ℝ) + 1) = (n : ℝ) + (m₀ : ℝ) + 1 := by push_cast; ring
    rw [hw, hx, hcast, not_le]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have hX : (0 : ℝ) < (n : ℝ) + (m₀ : ℝ) + 1 := by linarith
    have hX3 : (0 : ℝ) < ((n : ℝ) + (m₀ : ℝ) + 1) ^ 3 := by positivity
    nlinarith [hn, hm, hnn, hX, hX3,
      mul_pos (show (0 : ℝ) < ((n : ℝ) + (m₀ : ℝ) + 1) - C by linarith) hX3]

#print axioms contact_relative_is_strictly_stronger

end MassGap.ShareEnvelope
