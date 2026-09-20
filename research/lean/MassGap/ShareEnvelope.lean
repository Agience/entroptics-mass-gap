import Mathlib
import MassGap.ContactDominance

/-!
# The far share, condensed onto a geometric sequence of cuts

`ContactDominance.substrate_of_share_envelope` discharges the substrate hypothesis from a profile
`a : ℕ → ℝ` with `farShare ≤ a` and `∑ (2m+1)·a m < ∞` — a statement about EVERY cut. This file cuts
that down to a geometric sequence of cuts, exactly, and then reads the resulting condition as a
ratio, which removes the read's normalisation from it entirely.

## The main result: an EQUIVALENCE

`farShare` is antitone in the cut (`farShare_antitone`) with no hypothesis beyond `p ≥ 0`, which the
read interface already gives. That alone makes the layer cake comparable, in BOTH directions, to its
condensation onto the cuts `cut m₀ j` — `m₀`, `2m₀+1`, `4m₀+3`, … , the cuts at which `m+1` has
doubled `j` times:

    3(m₀+1)²·∑_{j<J} 4^j·farShare R (cut m₀ (j+1))          (`condensed_le_layer`)
      ≤ ∑_{m ≤ cut m₀ J} (2m+1)·farShare R m
      ≤ (m₀+1)²·(1 + 3·∑_{j<J} 4^j·farShare R (cut m₀ j))   (`layer_le_condensed`)

so for every `m₀`

    (∃ B, ∀ N β, d2At N β ≤ B)  ↔  (∃ S, ∀ N β J, ∑_{j<J} 4^j·farShare (readYMAt N β) (cut m₀ j) ≤ S)

(`substrate_iff_dyadic_shares`). Nothing is given away in either direction: the whole content of the
substrate hypothesis is that those `4^j`-weighted shares stay bounded, and every cut off that
sequence is already controlled by antitonicity. The `4^j` is the weight of one block of cuts over the
block before it, `((m₀+1)2^{j+1})² − ((m₀+1)2^j)²` over `3(m₀+1)²`; it is Cauchy condensation for the
weight `2m+1`, and it is exact because that weight IS the discrete derivative of the square.

## The sufficient ratio form

Bounding the condensed sum by a geometric series gives the criterion the rest of the file is about:

    farShare R (2m+1) ≤ θ · farShare R m  for m ≥ m₀,  with 0 ≤ θ < 1/4
      ⟹  ∑ d, p d · circLag(d)² ≤ (m₀+1)² · (1 + 3/(1 − 4θ))

(`circ_moment_le_of_share_doubling`), uniformly in the aperture, hence `substrate_of_share_doubling`
and `yang_mills_of_share_doubling`.

`1/4` is DERIVED, not chosen, and the correspondence with the exponent threshold of
`ContactDominance` is EXACT rather than asymptotic: on a power profile `a m = C (m+1)^{-s}` the ratio
`a (2m+1) / a m` is identically `2^{-s}`, so `θ < 1/4` says exactly `s > 2`. The `4` is the square
weight's own doubling, `((2m+2)/(m+1))² = 4`; the `3` is `4 − 1`, the weight of one block of cuts as
a multiple of the block before it.

Nothing is assumed below `m₀`: as in `ContactDominance.circ_moment_le_of_tail_envelope`, the near
block is capped by `farShare ≤ 1` on its own, here at `(m₀+1)²`. That near-block bound is restated
rather than reused: `circ_moment_le_of_tail_envelope` reaches it through a `Summable` envelope and a
`tsum`, and the envelope this criterion implies is indexed by `⌊log₂((m+1)/(m₀+1))⌋`, whose tsum is a
detour. The finite induction `layer_partial_le` runs the whole thing in one pass.

## Why the step is `m ↦ 2m+1` and not `m ↦ 2m`

The cut variable that matters is `m+1`, because the near block below `m` weighs `m²` while the first
lag beyond it weighs `(m+1)²`, and `ContactDominance`'s envelopes are powers of `m+1`. Under
`m ↦ 2m` a power `(m+1)^{-s}` contracts by `((m+1)/(2m+1))^s`, which exceeds `2^{-s}` at every finite
`m` — the criterion would then be strictly stronger than the exponent threshold it is meant to
match, and `ContactDominance.squareRead` would NOT witness sharpness at `1/4`. Under `m ↦ 2m+1` the
contraction is identically `2^{-s}` and `squareRead` saturates `1/4` exactly
(`squareRead_quarter_doubling`). The parametrisation is forced by the weight, not chosen.

## Why the ratio form matters

`farShare R m = (∑_{circLag > m} ρ d) / (∑_d ρ d)`, so the normalisation divides out of BOTH sides of
`farShare R (2m+1) ≤ θ · farShare R m`, and the criterion is EQUIVALENT to the same inequality on the
raw tail masses (`farShare_doubling_iff_tail_mass`). `substrate_of_tail_mass_doubling` states it that
way: a condition on `wilsonCorrAt` alone — no normalisation, no envelope, and no lower bound on
`∑ d, wilsonCorrAt N β d`.

That last point is the reason for stating it. `ContactDominance.circ_moment_le_of_rho_envelope` needs
a floor `c ≤ ∑ ρ` with `c > 0` alongside its envelope, and `mass_floor_is_not_scale_free` shows that
pair is strictly stronger than the conclusion it is used for: the conclusion is invariant under
`ρ ↦ t·ρ` (`farShare_scale_invariant`, `circ_moment_scale_invariant`) and the pair is not.

## What it does NOT do, and where each form sits

It does not discharge the substrate hypothesis. `substrate_iff_dyadic_shares` is an equivalence, so it
moves the obligation rather than reducing it; the doubling contraction is a SUFFICIENT special case
of that equivalence and is STRICTLY STRONGER than `ContactDominance.substrate_of_tail_envelope` —
a uniformly summable share envelope does not imply a uniform contraction, because a family of
profiles may be flat across a doubling at a scale that runs off to infinity with the aperture while
staying under one envelope. So the order is

    doubling contraction  ⟹  condensed bound  ⟺  substrate hypothesis  ⟸  summable share envelope

and only the middle link is an equivalence. Where the doubling form earns its place is that it is the
only one of the four that mentions neither the size of the share nor the total mass.

Like every other criterion in this tree it still has to be met by the Wilson measure at every
coupling, and `ContactDominance.aperture_uniformity_does_not_give_coupling_uniformity` applies
verbatim: a contraction holding at each coupling with `θ` depending on `β` says nothing. What the
form buys is that the hypothesis is a POWER law rather than a rate — `θ < 1/4` forces
`farShare m ≲ (m+1)^{-log₂(1/θ)}` and nothing exponential — which is the side of
`Substrate.bounded_moment_does_not_give_geometric_decay` the substrate hypothesis actually needs.

## The correlator form: a power law against the read's own contact term

The second half of the file leaves the share entirely. `substrate_of_contact_relative_decay` takes

    wilsonCorrAt N β d ≤ C · wilsonCorrAt N β 0 / (circLag d)⁴   for  circLag d ≥ m₀

— uniformly in aperture and coupling — and discharges the substrate hypothesis. No normalisation, no
total mass, no floor and no rate appear in it: `ρ 0 ≤ ∑ ρ` holds from nonnegativity alone
(`contact_le_total`), so the contact term normalises the read from inside, and the condition is
scale-free under `ρ ↦ t·ρ` (`contact_relative_scale_invariant`) exactly as the conclusion is.
`substrate_of_inverse_eighth_decay` is the same statement at the exponent the short-distance form of
the connected `F²` correlation carries; since `ρ(0)` and `ρ(d)` carry the same power of the coupling,
that ratio has no coupling in it at leading order, and `8` is five above the threshold.

The threshold exponent here is EXACTLY `3` — one above the share's `2`, because the share has already
absorbed a summation — and `cubic_contact_relative_gives_no_bound` shows that at `3` there is no
bound at all. What the quartic law leaves, after one summation, is a CUBIC far-share envelope
`(2C/3)/m³` (`farShare_le_of_contact_relative`, `cubicShare`), which is one full power above the
share threshold `square_share_is_not_enough` shows is FALSE; the tail is summed by telescoping
(`quartic_step`, `inv_quartic_tail`), so the constant is exact at every finite aperture rather than
asymptotic.

This is a SUFFICIENT condition and it gives something away: `contact_relative_is_strictly_stronger`
exhibits `Substrate.tailRead`, whose moment is at most `1` at every aperture and which admits no
`(C, m₀)` at exponent `4` at all. What remains open is what the first half of the file says it is —
that ONE constant `C` covers every coupling.

## Negative controls

* `doubling_nonvacuous` — the contact read meets the hypothesis at `θ = 0` and its moment is `0`, so
  the criterion is not an implication out of an unsatisfiable hypothesis.
* `doubling_load_bearing` — `ContactDominance.midRead` satisfies exactly the two clauses
  `wilson_reflection_positive_at` asserts, its far share is `1` at every cut below the antipode so it
  admits NO `θ < 1` at any cut `m₀`, and its moments exceed every `B`. Drop the contraction and the
  conclusion is false, not merely unproved.
* `quarter_doubling_is_not_enough` — the threshold is EXACTLY `1/4`, and AT it the statement is
  FALSE. `ContactDominance.squareRead` satisfies the contraction with `θ = 1/4` at every cut and
  every aperture (`squareRead_quarter_doubling`) and its moments exceed every `B`. It is the same
  family `ContactDominance.square_share_is_not_enough` uses: the two sharpness statements are one
  fact in two parametrisations, which is what makes `θ = 1/4` and `s = 2` the same threshold.
* `contact_relative_nonvacuous` — the contact read meets the correlator condition at `C = 0` and its
  moment is `0`.
* `contact_relative_load_bearing` — `ContactDominance.midRead` puts no weight at lag zero, so its
  contact value is `0` and NO constant works at any cut, and its moments exceed every `B`. Drop the
  condition and the conclusion is false, not merely unproved. It also says what the condition asks
  for that a share condition does not: contact dominance.
* `cubic_contact_relative_is_not_enough` / `cubic_contact_relative_gives_no_bound` — the threshold
  exponent is EXACTLY `3`, and AT it there is no bound whatsoever: `cubeRead` obeys the condition at
  exponent `3` with the constant `1` at every aperture and its moments exceed every `B`.
* `contact_relative_is_strictly_stronger` — `Substrate.tailRead` satisfies the substrate hypothesis
  with `B = 1` and admits no `(C, m₀)` at exponent `4`, so the correlator form is a sufficient
  condition and not a restatement.
-/

namespace MassGap.ShareEnvelope

open MassGap.Moment MassGap.ContactDominance

/-! ### The far share is antitone in the cut, for free -/

/-- Raising the cut shrinks the far set. -/
theorem farSet_subset {N : ℕ} {m m' : ℕ} (h : m ≤ m') : farSet N m' ⊆ farSet N m := by
  intro d hd
  simp only [farSet, Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
  omega

/-- **The far share is antitone in the cut.** No hypothesis beyond the read interface: `p ≥ 0` and
the far sets nest. This is what lets a criterion read the profile along a sparse sequence of cuts. -/
theorem farShare_antitone {N : ℕ} (R : Moment.Read N) {m m' : ℕ} (h : m ≤ m') :
    farShare R m' ≤ farShare R m :=
  Finset.sum_le_sum_of_subset_of_nonneg (farSet_subset h) (fun d _ _ => R.p_nonneg d)

#print axioms farShare_antitone

/-! ### The cut sequence

`cut m₀ j` doubles `m + 1` from `m₀`: `cut m₀ 0 = m₀`, `cut m₀ (j+1) = 2·cut m₀ j + 1`, so
`cut m₀ j + 1 = (m₀ + 1)·2^j`. Everything is stated against `cut` so that no natural subtraction
appears anywhere. -/

/-- The cut sequence: the `j`-th doubling of `m₀ + 1`, less one.

DERIVED: `2m+1` is the cut at which `m+1` has doubled — `(2m+1)+1 = 2(m+1)`. Nothing is chosen. -/
def cut (m₀ : ℕ) : ℕ → ℕ
  | 0 => m₀
  | j + 1 => 2 * cut m₀ j + 1

/-- `cut m₀ j + 1 = (m₀ + 1)·2^j`, in `ℝ`. -/
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

/-- The cut sequence never falls below its start. -/
theorem le_cut (m₀ : ℕ) (j : ℕ) : m₀ ≤ cut m₀ j := by
  induction j with
  | zero => exact le_refl _
  | succ i ih =>
      have hval : cut m₀ (i + 1) = 2 * cut m₀ i + 1 := rfl
      omega

/-- The cut sequence is strictly increasing. -/
theorem cut_lt_succ (m₀ : ℕ) (j : ℕ) : cut m₀ j < cut m₀ (j + 1) := by
  have hval : cut m₀ (j + 1) = 2 * cut m₀ j + 1 := rfl
  omega

/-- The cut sequence outruns its own index, so every aperture is covered by some cut. -/
theorem self_le_cut (m₀ : ℕ) (j : ℕ) : j ≤ cut m₀ j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ i ih =>
      have hval : cut m₀ (i + 1) = 2 * cut m₀ i + 1 := rfl
      omega

/-- A profile contracting across each doubling is geometric along the cut sequence. -/
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

/-! ### The weight of a block of cuts -/

/-- `∑_{A ≤ m < B} (2m+1) = B² − A²`, the telescoping of the square. -/
theorem sum_Ico_odd {A B : ℕ} (h : A ≤ B) :
    ∑ m ∈ Finset.Ico A B, (2 * (m : ℝ) + 1) = (B : ℝ) ^ 2 - (A : ℝ) ^ 2 := by
  rw [Finset.sum_Ico_eq_sub _ h, sum_range_odd, sum_range_odd]

/-- `(2^j)² = 4^j`. -/
theorem two_pow_sq (j : ℕ) : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/-! ### The partial layer cake under a doubling contraction -/

/-- **The layer cake up to the `J`-th cut, under a doubling contraction.**

The near block `m ≤ m₀` costs `(m₀+1)²` from `a ≤ 1` alone; the block between consecutive cuts costs
`3(m₀+1)²(4θ)^j`, because its weight is EXACTLY `3(m₀+1)²4^j` and the profile on it is at most `θ^j`.

DERIVED: `(m₀+1)²` is `∑_{m ≤ m₀}(2m+1)` and `3·4^j` is `((m₀+1)2^{j+1})² − ((m₀+1)2^j)²` over
`(m₀+1)²` — both are the square weight's own arithmetic, not allowances. -/
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

/-- **The condensed sum bounds the layer cake from BELOW too**, so the two are comparable in both
directions and the criterion below is an equivalence rather than a sufficient condition. On the
`j`-th block every cut is at most `cut m₀ (j+1)`, so antitonicity bounds the profile there from
below by its value at the block's far end. -/
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

/-- The doubling contraction, fed through the condensed bound: `a (cut m₀ j) ≤ θ^j`. -/
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

/-! ### The moment bound -/

/-- A partial geometric sum is under `1/(1−r)`. -/
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

/-- **THE MOMENT BOUND FROM A DOUBLING CONTRACTION.**

`farShare R (2m+1) ≤ θ·farShare R m` for `m ≥ m₀`, with `0 ≤ θ < 1/4`, bounds the circular second
moment by `(m₀+1)²·(1 + 3/(1−4θ))` — at every aperture, with nothing assumed below `m₀`.

DERIVED: `(m₀+1)²` is the near block's own worst case, `3·4^j` the weight of the `j`-th block, and
`1/(1−4θ)` the geometric total those two produce. No constant is introduced. -/
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

/-! ### Condensation: the hypothesis is EQUIVALENT to a bound at a geometric sequence of cuts

`layer_le_condensed` and `condensed_le_layer` bracket the layer cake by the same condensed sum from
both sides, up to the factor `3(m₀+1)²` and a shift of one cut. Since `farShare` is antitone for
free, that makes the substrate hypothesis EQUIVALENT to uniform boundedness of

    ∑_{j} 4^j · farShare R (cut m₀ j)

(`substrate_iff_dyadic_shares`). This is Cauchy condensation for the weight `2m+1`: the `4^j` is the
weight of the `j`-th block over the block before it. What it buys is that only a GEOMETRIC sequence
of cuts has to be estimated — `O(log N)` numbers per `(N, β)` instead of `N` — and it gives away
nothing, because it is an equivalence rather than a sufficient condition. -/

/-- Beyond the aperture there is nothing left: `circLag` never reaches `N+1`. -/
theorem farShare_eq_zero {N : ℕ} (R : Moment.Read N) {m : ℕ} (hm : N ≤ m) : farShare R m = 0 := by
  classical
  refine Finset.sum_eq_zero (fun d hd => ?_)
  simp only [farSet, Finset.mem_filter, Finset.mem_univ, true_and] at hd
  exact absurd hd (by have hlt := circLag_lt_succ d; omega)

/-- The layer cake over any range is under the full one, because the profile vanishes beyond the
aperture. -/
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

/-- **The moment from the condensed sum.** -/
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

/-- **The condensed sum from the moment** — the converse, which is what makes the criterion an
equivalence. -/
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

/-- Peeling the first cut off the condensed sum. -/
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

/-- The substrate hypothesis from the condensed sums. -/
theorem substrate_of_dyadic_shares (m₀ : ℕ) (S : ℝ)
    (hS : ∀ (N : ℕ) (β : ℝ) (J : ℕ),
      ∑ j ∈ Finset.range J, (4 : ℝ) ^ j * farShare (MassGap.readYMAt N β) (cut m₀ j) ≤ S) :
    ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B :=
  ⟨((m₀ : ℝ) + 1) ^ 2 * (1 + 3 * S), fun N β =>
    circ_moment_le_of_dyadic_shares (MassGap.readYMAt N β) m₀ S (hS N β)⟩

#print axioms substrate_of_dyadic_shares

/-- The condensed sums from the substrate hypothesis. -/
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

/-- **THE SUBSTRATE HYPOTHESIS IS EXACTLY A BOUND AT A GEOMETRIC SEQUENCE OF CUTS.**

An EQUIVALENCE, at every starting cut `m₀`. The forward direction loses nothing and the reverse
direction loses nothing, so this is a restatement of the open hypothesis and not a strengthening of
it: the whole content of `∃ B, ∀ N β, d2At N β ≤ B` is that the `4^j`-weighted far shares at the
cuts `m₀, 2m₀+1, 4m₀+3, …` stay uniformly bounded.

What it removes from the obligation is every cut that is not on that sequence. `farShare` is antitone
for free (`farShare_antitone`), so the cuts in between are already controlled by their block's left
endpoint, and nothing has to be said about them. -/
theorem substrate_iff_dyadic_shares (m₀ : ℕ) :
    (∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B)
      ↔ (∃ S : ℝ, ∀ (N : ℕ) (β : ℝ) (J : ℕ),
          ∑ j ∈ Finset.range J, (4 : ℝ) ^ j * farShare (MassGap.readYMAt N β) (cut m₀ j) ≤ S) :=
  ⟨dyadic_shares_of_substrate m₀, fun ⟨S, hS⟩ => substrate_of_dyadic_shares m₀ S hS⟩

#print axioms substrate_iff_dyadic_shares

/-! ### The substrate hypothesis, and the whole statement -/

/-- **THE SUBSTRATE HYPOTHESIS FROM A DOUBLING CONTRACTION OF THE FAR SHARE.**

One cut `m₀` and one ratio `θ < 1/4`, good at every aperture and every coupling, discharge
`∃ B, ∀ N β, d2At N β ≤ B`. `B` is `(m₀+1)²(1 + 3/(1−4θ))`; nothing is fitted.

The axiom footprint carries `wilson_reflection_positive_at` because `readYMAt` is constructed from
it. -/
theorem substrate_of_share_doubling (m₀ : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 4)
    (hdb : ∀ (N : ℕ) (β : ℝ) (m : ℕ), m₀ ≤ m →
      farShare (MassGap.readYMAt N β) (2 * m + 1) ≤ θ * farShare (MassGap.readYMAt N β) m) :
    ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B :=
  ⟨((m₀ : ℝ) + 1) ^ 2 * (1 + 3 / (1 - 4 * θ)), fun N β =>
    circ_moment_le_of_share_doubling (MassGap.readYMAt N β) m₀ θ hθ0 hθ (hdb N β)⟩

#print axioms substrate_of_share_doubling

/-- **Confinement at every large enough aperture, from the doubling contraction.** -/
theorem confinement_of_share_doubling (m₀ : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 4)
    (hdb : ∀ (N : ℕ) (β : ℝ) (m : ℕ), m₀ ≤ m →
      farShare (MassGap.readYMAt N β) (2 * m + 1) ≤ θ * farShare (MassGap.readYMAt N β) m) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, MassGap.μYMAt N β < MassGap.κ₀YM :=
  MassGap.confinement_of_bounded_substrate (substrate_of_share_doubling m₀ θ hθ0 hθ hdb)

#print axioms confinement_of_share_doubling

/-- **THE WHOLE STATEMENT, FROM A DOUBLING CONTRACTION OF THE FAR SHARE.**

`WilsonModel.existence_and_gap_of_substrate` takes exactly `∃ B, ∀ N β, d2At N β ≤ B`, so the mass
gap, non-triviality, `SO(4)` invariance and the continuum measure all follow from one ratio: the
share of the connected plaquette correlation beyond a cut contracts by better than four when the cut
doubles. -/
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

/-! ### The same condition on the RAW correlator: no normalisation, no mass floor -/

/-- **The contraction is scale-free: it is the same statement on the unnormalised tail masses.**

An equivalence, not a sufficient condition. `∑ d, ρ d` appears on both sides of the share form and
cancels, so the criterion never needs the total mass — neither its value nor a floor under it. -/
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

/-- The Wilson read's weights ARE the constructed correlation. -/
theorem readYMAt_rho (N : ℕ) (β : ℝ) (d : Fin (N + 1)) :
    (MassGap.readYMAt N β).ρ d = MassGap.wilsonCorrAt N β d := rfl

/-- **THE SUBSTRATE HYPOTHESIS FROM A CONDITION ON THE RAW CORRELATOR.**

No normalisation, no envelope, and no lower bound on `∑ d, wilsonCorrAt N β d`: only that the mass
the connected plaquette correlation places beyond a cut contracts by a factor below `1/4` when the
cut's successor index doubles, uniformly in aperture and coupling.

This is the form `mass_floor_is_not_scale_free` says the unnormalised route should take. The
hypothesis is invariant under `ρ ↦ t·ρ`, exactly as the conclusion is. -/
theorem substrate_of_tail_mass_doubling (m₀ : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 4)
    (h : ∀ (N : ℕ) (β : ℝ) (m : ℕ), m₀ ≤ m →
      ∑ d ∈ farSet N (2 * m + 1), MassGap.wilsonCorrAt N β d
        ≤ θ * ∑ d ∈ farSet N m, MassGap.wilsonCorrAt N β d) :
    ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B := by
  refine substrate_of_share_doubling m₀ θ hθ0 hθ ?_
  intro N β m hm
  refine (farShare_doubling_iff_tail_mass (MassGap.readYMAt N β) m θ).mpr ?_
  simpa only [readYMAt_rho] using h N β m hm

#print axioms substrate_of_tail_mass_doubling

/-! ### Why the unnormalised route must not carry a mass floor -/

/-- The read rescaled, `ρ ↦ t·ρ`.

DERIVED: `0` is the strict positivity the rescaling factor must have for `Moment.Read`'s own
`hpos` field to survive it — a nonpositive `t` would not give a read at all. It is the structure's
requirement, not a threshold. -/
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

/-- **The far share is scale-free.** -/
theorem farShare_scale_invariant {N : ℕ} (R : Moment.Read N) {t : ℝ} (ht : 0 < t) (m : ℕ) :
    farShare (scaleRead R ht) m = farShare R m :=
  Finset.sum_congr rfl (fun d _ => scaleRead_p R ht d)

/-- **So is the circular second moment.** -/
theorem circ_moment_scale_invariant {N : ℕ} (R : Moment.Read N) {t : ℝ} (ht : 0 < t) :
    ∑ d, (scaleRead R ht).p d * (Moment.circLag d : ℝ) ^ 2
      = ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2 :=
  Finset.sum_congr rfl (fun d _ => by rw [scaleRead_p R ht d])

/-- **A MASS FLOOR IS NOT SCALE-FREE — the unnormalised envelope route is strictly stronger than
what it is used to prove.**

`ContactDominance.circ_moment_le_of_rho_envelope` consumes an envelope on `ρ` AND a floor `c ≤ ∑ ρ`
with `c > 0`. Its conclusion — a bound on `∑ p d · circLag(d)²` — is invariant under `ρ ↦ t·ρ`, and
so is the far share; the floor is not. For every read and every `c > 0` there is a rescaling that
leaves the share and the moment EXACTLY unchanged and breaks the floor.

So the pair (envelope, floor) is strictly stronger than the hypothesis it discharges, by one whole
scale degree of freedom, and `substrate_of_tail_mass_doubling` — which mentions no total mass at all
— is the form the unnormalised route should take. -/
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

/-! ### Negative control: the criterion is not vacuous -/

/-- **NON-VACUITY.** The contact read satisfies the two clauses `wilson_reflection_positive_at`
asserts, meets the contraction at `θ = 0` and every cut, and has moment zero. So
`circ_moment_le_of_share_doubling` is not an implication out of an unsatisfiable hypothesis. -/
theorem doubling_nonvacuous (N : ℕ) :
    (∀ m : ℕ, farShare (contactRead N) (2 * m + 1) ≤ (0 : ℝ) * farShare (contactRead N) m) ∧
      ∑ d, (contactRead N).p d * (Moment.circLag d : ℝ) ^ 2 = 0 :=
  ⟨fun m => by rw [contactRead_farShare, contactRead_farShare]; norm_num,
    contactRead_moment N⟩

#print axioms doubling_nonvacuous

/-! ### Negative control: the contraction is load-bearing -/

/-- The mid-lag read's far share is `1` at every cut below half the period. -/
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

/-- **THE CONTRACTION IS LOAD-BEARING.**

`midRead` meets exactly the two clauses `wilson_reflection_positive_at` asserts. Its far share is `1`
at every cut below the antipode, so at every cut `m₀` and every `θ < 1` there is an aperture at which
the contraction FAILS — and its moments exceed every `B`. Remove the contraction from
`circ_moment_le_of_share_doubling` and the conclusion is false, not merely unproved. -/
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

/-! ### Sharpness: the threshold ratio is exactly one quarter

`ContactDominance.squareRead` is the family whose far share saturates a square envelope. Read in this
parametrisation it saturates the contraction at `θ = 1/4` EXACTLY — at every cut and every aperture —
and its moments are unbounded. So `θ < 1/4` is not a margin: at `1/4` the statement is false. -/

/-- The far `ρ`-mass of `squareRead`, collapsed onto the telescoping profile. -/
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

/-- The telescoping far mass, EXACTLY, below the aperture's own reach. -/
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

/-- Beyond the aperture's reach the far mass is zero. -/
theorem tel_far_eq_of_gt (k m : ℕ) (h : k + 2 ≤ m + 1) :
    ∑ j ∈ Finset.range (k + 2), telWeight j * (if m < j then (1 : ℝ) else 0) = 0 := by
  refine Finset.sum_eq_zero (fun j hj => ?_)
  simp only [Finset.mem_range] at hj
  rw [if_neg (by omega), mul_zero]

/-- The far mass is nonnegative. -/
theorem tel_far_nonneg (k m : ℕ) :
    0 ≤ ∑ j ∈ Finset.range (k + 2), telWeight j * (if m < j then (1 : ℝ) else 0) :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (telWeight_nonneg j) (by split <;> norm_num))

/-- **The telescoping family contracts by EXACTLY one quarter across each doubling**, on the raw
tail masses — so also on the shares, by `farShare_doubling_iff_tail_mass`. -/
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

/-- The contraction at `θ = 1/4`, on the shares. -/
theorem squareRead_quarter_doubling (k m : ℕ) :
    farShare (squareRead k) (2 * m + 1) ≤ (1 / 4 : ℝ) * farShare (squareRead k) m :=
  (farShare_doubling_iff_tail_mass (squareRead k) m (1 / 4)).mpr
    (squareRead_tail_mass_quarter k m)

/-- **SHARPNESS: A CONTRACTION BY ONE QUARTER IS NOT ENOUGH.**

`squareRead` satisfies the two clauses of `wilson_reflection_positive_at`, contracts by exactly `1/4`
across every doubling at every aperture, and its circular second moments exceed every `B`. So the
threshold in `circ_moment_le_of_share_doubling` is exactly `1/4`: below it the contraction discharges
the substrate hypothesis, at it the hypothesis is FALSE.

It is the same family, and the same failure, as `ContactDominance.square_share_is_not_enough` — which
is the point: `θ = 1/4` and the envelope exponent `s = 2` are one threshold, since
`(m+1)^{-s}` contracts by exactly `2^{-s}` across `m ↦ 2m+1`. -/
theorem quarter_doubling_is_not_enough :
    (∀ k m : ℕ, farShare (squareRead k) (2 * m + 1) ≤ (1 / 4 : ℝ) * farShare (squareRead k) m) ∧
      (∀ B : ℝ, ∃ k : ℕ, B < ∑ d, (squareRead k).p d * (Moment.circLag d : ℝ) ^ 2) :=
  ⟨squareRead_quarter_doubling, square_share_is_not_enough.2⟩

#print axioms quarter_doubling_is_not_enough

/-- **At `θ = 1/4` there is NO bound at all** — not a weaker one, none.

Stated without the criterion's own constant so that nothing turns on how `3/(1−4θ)` evaluates at
`θ = 1/4`: for EVERY `B` whatsoever, some read satisfying the two clauses
`wilson_reflection_positive_at` asserts contracts by `1/4` across every doubling from the cut `0`
upward and has moment above `B`. So `θ < 1/4` in `circ_moment_le_of_share_doubling` is the hypothesis
doing the work, not a margin around it. -/
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

Everything above is a condition on the SHARE, which carries the normalisation `∑ ρ` inside it. The
condition in this section is a condition on the correlation itself, measured against its value at
lag zero:

    ρ d ≤ C · ρ 0 / (circLag d)⁴   whenever   circLag d ≥ m₀.

Three properties follow from the shape alone, before any estimate of the Wilson measure:

* it is SCALE-FREE (`contact_relative_scale_invariant`). `ρ ↦ t·ρ` multiplies both sides by `t`, so
  the condition is invariant exactly as the conclusion is — which is what
  `mass_floor_is_not_scale_free` says the unnormalised route has to be. No mass floor appears,
  because `ρ 0 ≤ ∑ ρ` holds for free from nonnegativity (`contact_le_total`): the contact term
  normalises the read from inside, and `circ_moment_le_of_rho_envelope`'s extra hypothesis `c ≤ ∑ ρ`
  is not needed.
* it is a POWER, not a RATE. `Substrate.bounded_moment_does_not_give_geometric_decay` says a bounded
  moment does not give a geometric bound, and asymptotic freedom denies a decay rate uniform in the
  coupling; neither bears on a power law, which has no rate in it.
* nothing is assumed below the cut `m₀`, because `p ≤ 1` caps the near lags on its own
  (`p_le_one`) — the same structure as `ContactDominance.circ_moment_le_of_tail_envelope`.

THE THRESHOLD EXPONENT IS EXACTLY `3`, and `4` is the smallest integer above it. The moment weights
by `k²` and the circle lag has multiplicity two (`Moment.sum_circLag_le_two_mul`), so the envelope's
weighted total is `∑ k²·C/kˢ`, which converges exactly when `s > 3`. It is one above the share's
threshold `2` because the share has already absorbed a summation.
`cubic_contact_relative_is_not_enough` and `cubic_contact_relative_gives_no_bound` show `3` is not
merely out of reach but FALSE: at `s = 3` with `C = 1` there is no bound whatsoever.

WHAT THIS IS, STATED PLAINLY. It is a SUFFICIENT condition, and a strictly stronger one than the
substrate hypothesis — `contact_relative_is_strictly_stronger` exhibits `Substrate.tailRead`, whose
moment is at most `1` at every aperture and which admits no `(C, m₀)` at exponent `4` at all. So
this moves the obligation to a power-law bound on the connected plaquette correlation relative to
its own contact value, uniform in the aperture AND in the coupling. The coupling direction is where
the content is, exactly as `ContactDominance.aperture_uniformity_does_not_give_coupling_uniformity`
says; what the form buys is that the thing to be shown uniform is one dimensionless constant `C` in
front of a fixed power, with no rate, no normalisation and no total mass in it.
-/

/-- The circle lag at the origin is zero, at every aperture. -/
theorem circLag_origin (N : ℕ) : Moment.circLag (0 : Fin (N + 1)) = 0 := by
  have hv : ((0 : Fin (N + 1)) : ℕ) = 0 := rfl
  unfold Moment.circLag
  rw [hv]
  omega

/-- Every weight is at most one, since the weights sum to one. This is what caps the near lags when
a decay condition is only assumed beyond a cut. -/
theorem p_le_one {N : ℕ} (R : Moment.Read N) (d : Fin (N + 1)) : R.p d ≤ 1 := by
  have h := Finset.single_le_sum (f := fun d' : Fin (N + 1) => R.p d')
    (fun d' _ => R.p_nonneg d') (Finset.mem_univ d)
  rwa [R.p_sum] at h

/-- **The contact weight is at most the total mass.** Nonnegativity alone; no hypothesis beyond the
read interface. This is the whole reason a contact-relative bound needs no mass floor. -/
theorem contact_le_total {N : ℕ} (R : Moment.Read N) : R.ρ 0 ≤ ∑ d, R.ρ d :=
  Finset.single_le_sum (f := fun d : Fin (N + 1) => R.ρ d) (fun d _ => R.hρ d)
    (Finset.mem_univ (0 : Fin (N + 1)))

/-- **A bound relative to the contact term is a bound on the normalised weight, with the same
constant.** `p d = ρ d / ∑ ρ ≤ A · (ρ 0 / ∑ ρ) ≤ A`, since `ρ 0 ≤ ∑ ρ`. -/
theorem p_le_of_contact_relative {N : ℕ} (R : Moment.Read N) {d : Fin (N + 1)} {A : ℝ}
    (hA : 0 ≤ A) (h : R.ρ d ≤ A * R.ρ 0) : R.p d ≤ A := by
  have hS : (0 : ℝ) < ∑ d', R.ρ d' := R.hpos
  show R.ρ d / (∑ d', R.ρ d') ≤ A
  rw [div_le_iff₀ hS]
  calc R.ρ d ≤ A * R.ρ 0 := h
    _ ≤ A * ∑ d', R.ρ d' := mul_le_mul_of_nonneg_left (contact_le_total R) hA

/-- **The contact-relative condition is scale-free.** Both sides carry one factor of the rescaling,
so `ρ ↦ t·ρ` leaves it unchanged — exactly as it leaves the far share and the moment unchanged
(`farShare_scale_invariant`, `circ_moment_scale_invariant`). An equivalence, not an implication. -/
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

/-- The weight envelope a contact-relative tail bound produces: nothing below the cut, `C/k⁴` beyond
it.

DERIVED: the `1` below the cut is the read's own normalisation — `p ≤ ∑ p = 1` holds for every read
(`p_le_one`), so it is not an assumption about the correlation there. The `4` is the smallest
INTEGER above the threshold exponent `3`, which is where `∑ k²·b k` stops converging and which
`cubic_contact_relative_is_not_enough` shows is FALSE. The cut is written `m₀ + 1` rather than `m₀`
so that the tail branch is never evaluated at `k = 0`. `C` and `m₀` are the caller's. -/
noncomputable def quarticWeight (m₀ : ℕ) (C : ℝ) (k : ℕ) : ℝ :=
  if k < m₀ + 1 then 1 else C / (k : ℝ) ^ 4

theorem quarticWeight_nonneg (m₀ : ℕ) {C : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    0 ≤ quarticWeight m₀ C k := by
  unfold quarticWeight
  split
  · norm_num
  · exact div_nonneg hC (by positivity)

/-- The envelope's squared-lag total converges: beyond the cut the terms are `C/k²`. -/
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

/-- **THE MOMENT BOUND FROM A CONTACT-RELATIVE POWER LAW.**

`ρ d ≤ C·ρ 0 / (circLag d)⁴` beyond a cut `m₀` bounds the circular second moment by
`2·∑' k, k²·quarticWeight m₀ C k` — at every aperture, with nothing assumed below the cut, no
normalisation and no lower bound on the total mass.

DERIVED: the `2` is the circle lag's multiplicity (`Moment.sum_circLag_le_two_mul`) and the sum is
the envelope's own. No constant is introduced.

THE CUT IS READ AS `m₀ + 1`. The proof invokes the hypothesis only at `circLag d ≥ m₀ + 1`, so the
lag-zero instance is never consumed — which matters, because at `m₀ = 0` the hypothesis as written
covers `circLag d = 0`, where the fourth power vanishes and the inequality degenerates to
`ρ 0 ≤ 0`. The intended cut is `m₀ ≥ 1`, and nothing in the conclusion depends on which. -/
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

/-- **THE SUBSTRATE HYPOTHESIS FROM A CONTACT-RELATIVE POWER LAW ON THE RAW CORRELATOR.**

One cut `m₀` and one dimensionless constant `C`, good at every aperture and every coupling, discharge
`∃ B, ∀ N β, d2At N β ≤ B`. `B` is `2·∑' k, k²·quarticWeight m₀ C k`; nothing is fitted.

The hypothesis mentions no normalisation, no total mass and no rate: only that the connected
plaquette correlation at circle lag `d` is under `C/d⁴` times its own value at lag zero. The cut is
meant at `m₀ ≥ 1`; see `circ_moment_le_of_contact_relative` for why the lag-zero instance of the
hypothesis is never consumed.

The axiom footprint carries `wilson_reflection_positive_at` because `readYMAt` is constructed from
it. -/
theorem substrate_of_contact_relative_decay (m₀ : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)), m₀ ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d
        ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4) :
    ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B :=
  ⟨2 * ∑' k : ℕ, (k : ℝ) ^ 2 * quarticWeight m₀ C k, fun N β =>
    circ_moment_le_of_contact_relative (MassGap.readYMAt N β) m₀ hC
      (fun d hd => by simpa only [readYMAt_rho] using h N β d hd)⟩

#print axioms substrate_of_contact_relative_decay

/-- **Confinement at every large enough aperture, from the contact-relative power law.** -/
theorem confinement_of_contact_relative_decay (m₀ : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)), m₀ ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d
        ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, MassGap.μYMAt N β < MassGap.κ₀YM :=
  MassGap.confinement_of_bounded_substrate (substrate_of_contact_relative_decay m₀ C hC h)

#print axioms confinement_of_contact_relative_decay

/-- **THE WHOLE STATEMENT, FROM A CONTACT-RELATIVE POWER LAW.**

`WilsonModel.existence_and_gap_of_substrate` takes exactly `∃ B, ∀ N β, d2At N β ≤ B`, so the mass
gap, non-triviality, `SO(4)` invariance and the continuum measure all follow from one inequality on
the connected plaquette correlation: beyond a fixed lag it is under a fixed multiple of its own
contact value divided by the fourth power of the circle distance, uniformly in aperture and
coupling. -/
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

/-! ### The eighth power: the same statement at the exponent the short-distance form carries

The perturbative short-distance form of the connected `F²` correlation is `ρ(d) ∼ g⁴/d⁸`, and `ρ(0)`
carries the same `g⁴`, so the RATIO `ρ(d)/ρ(0)` is a power law with NO leading coupling dependence.
That is the shape the criterion above consumes, and `8` is five above the threshold `3` — so the
margin is not marginal. The reduction below makes the exponent explicit: it is enough to have the
eighth power with SOME constant, uniform in aperture and coupling. -/

/-- **THE SUBSTRATE HYPOTHESIS FROM AN INVERSE-EIGHTH CONTACT-RELATIVE BOUND.**

`ρ d ≤ C·ρ 0 / (circLag d)⁸` beyond a cut is enough, because beyond a lag of one the eighth power is
above the fourth. The exponent is not the point — any exponent above `3` would do, and this is the
one the short-distance form of the connected plaquette correlation carries, with a constant that is
coupling-free at leading order. What remains open is that ONE constant covers every coupling. -/
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
  have h0 : 0 ≤ MassGap.wilsonCorrAt N β 0 := (MassGap.wilson_reflection_positive_at N β).1 0
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

/-- **THE WHOLE STATEMENT, FROM THE INVERSE-EIGHTH BOUND.** -/
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

/-! ### The share envelope the law produces: exactly cubic, one full power above the threshold

The criterion above runs through the weight envelope, which is the parametrisation the hypothesis is
stated in. The same hypothesis also produces an explicit FAR-SHARE envelope, which is the
parametrisation `ContactDominance` states the threshold in, and it is worth writing down because it
says how much margin the law carries: a quartic contact-relative law gives

    farShare R m ≤ (2C/3)/m³        for `m` above the cut and above `1`

(`farShare_le_of_contact_relative`), and `3` is one full power above the share threshold `2` that
`ContactDominance.square_share_is_not_enough` shows is FALSE. The `1/3` is the tail integral of the
fourth power and the `2` is the circle lag's multiplicity; neither is an allowance.

The tail sum is bounded by telescoping rather than by an integral comparison, so the constant is
exact at every finite aperture: `1/(u+1)⁴ ≤ 1/(3u³) − 1/(3(u+1)³)` (`quartic_step`), whose surplus is
`(6u²+4u+1)/(3u³(u+1)⁴)`. -/

/-- One step of the quartic tail telescope: `1/(u+1)⁴ ≤ 1/(3u³) − 1/(3(u+1)³)`.

DERIVED: `3` is the exponent the fourth power telescopes to — `d/du (−1/(3u³)) = 1/u⁴` — and the
surplus `(6u²+4u+1)/(3u³(u+1)⁴)` is exhibited in the proof rather than assumed. -/
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

/-- **The quartic tail, summed exactly.** `∑_{i<K} 1/(x+1+i)⁴ ≤ 1/(3x³)` at every finite `K`, by
telescoping `quartic_step`. No integral comparison and no limit. -/
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

/-- **THE FAR-SHARE ENVELOPE A CONTACT-RELATIVE QUARTIC LAW PRODUCES.**

`farShare R m ≤ (2C/3)/m³` at every cut above the law's own cut and above `1`, at every aperture.

DERIVED: the `2` is the circle lag's multiplicity (`Moment.sum_circLag_le_two_mul`) and the `1/3` is
the quartic tail's telescoped total (`inv_quartic_tail`). Neither is an allowance, and the exponent
`3` is what the quartic law leaves after one summation. -/
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

/-- The cubic far-share envelope a quartic contact-relative law produces.

DERIVED: `2` is the circle lag's multiplicity, `3` in the numerator is the quartic tail's telescoped
total (`inv_quartic_tail`), and the exponent `3` is what one summation leaves of a quartic law. At
`m = 0` the value is `0`, which is below nothing the envelope is used for — the criterion consuming
it (`ContactDominance.substrate_of_tail_envelope`) reads it only above the cut. -/
noncomputable def cubicShare (C : ℝ) (m : ℕ) : ℝ := (2 * C / 3) / (m : ℝ) ^ 3

theorem cubicShare_nonneg {C : ℝ} (hC : 0 ≤ C) (m : ℕ) : 0 ≤ cubicShare C m := by
  unfold cubicShare
  exact div_nonneg (by linarith) (by positivity)

/-- **The envelope's weighted total converges** — `(2m+1)·m^{-3}` is `O(m^{-2})`, which is what the
threshold exponent `2` means. -/
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

/-- **THE SUBSTRATE HYPOTHESIS THROUGH THE SHARE ENVELOPE.**

The same reduction as `substrate_of_contact_relative_decay`, routed through the far share instead of
the weights, so that what discharges `ContactDominance.substrate_of_tail_envelope` is an explicit
profile `a m = (2C/3)/m³` with `∑ (2m+1)·a m` convergent — the object the criterion of this tree is
stated in, one full power above the threshold `square_share_is_not_enough` shows is FALSE. -/
theorem substrate_of_contact_relative_share (m₀ : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)), m₀ ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d
        ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4) :
    ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B :=
  substrate_of_tail_envelope (max m₀ 1) (cubicShare C) (cubicShare_nonneg hC)
    (cubicShare_summable hC)
    (fun N β m hm =>
      farShare_le_of_contact_relative (MassGap.readYMAt N β) m₀ hC
        (fun d hd => by simpa only [readYMAt_rho] using h N β d hd) m
        (le_trans (le_max_left m₀ 1) hm) (le_trans (le_max_right m₀ 1) hm))

#print axioms substrate_of_contact_relative_share

/-! ### Negative control: the criterion is not vacuous, and the condition is load-bearing -/

/-- **NON-VACUITY.** The contact read satisfies the two clauses `wilson_reflection_positive_at`
asserts, meets the contact-relative condition at `C = 0` beyond lag one, and has moment zero. So
`circ_moment_le_of_contact_relative` is not an implication out of an unsatisfiable hypothesis. -/
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

/-- **THE CONTACT-RELATIVE CONDITION IS LOAD-BEARING.**

`midRead` meets exactly the two clauses `wilson_reflection_positive_at` asserts. It puts ALL its
weight at the antipode and NONE at lag zero, so its contact value is `0` and the right-hand side of
the condition vanishes while the left-hand side is `1`: at every cut `m₀` and every constant `C`
whatsoever there is an aperture and a lag at which the condition FAILS. Its moments exceed every `B`.
Remove the condition from `circ_moment_le_of_contact_relative` and the conclusion is false, not
merely unproved.

This also says what the condition is really asking for, which a share condition does not: CONTACT
DOMINANCE. A correlation with no weight at short lags admits no contact-relative bound at all. -/
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

/-! ### Negative control: the threshold exponent is exactly three

The family below satisfies the contact-relative condition at exponent `3` with the constant `1` — the
smallest constant there is — at every aperture and every cut, and its moments are unbounded. So the
`4` in `circ_moment_le_of_contact_relative` cannot be lowered to `3`: AT the threshold the statement
is false, not merely unproved. It is the exponent-`3` counterpart of
`ContactDominance.square_share_is_not_enough`, one exponent up, because the share has absorbed a
summation. -/

/-- The cubic contact profile: weight `1/(j+1)³` at lag `j`, out to the antipode, and nothing beyond.

DERIVED: `3` is the threshold exponent itself — the exponent at which `∑ k²·b k` stops converging.
The `1` in the numerator is the contact value the profile is measured against, which `p` normalises
away, so it fixes no scale; `k + 1` is the antipode of the period `2k+2`, the largest lag at which
the circle distance still equals the index; `2 * k + 1` is the even-period aperture that antipode
needs. Nothing is chosen. -/
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

/-- Every sum against the circle lag collapses to the near range, where the lag is the index. -/
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

/-- The cubic profile's total mass is under `2`, by comparison with the telescoping weight. -/
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

/-- The cubic profile's squared-lag total dominates a quarter of the harmonic tail. -/
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

/-- The cubic profile's moments exceed every bound: the harmonic series again. -/
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

/-- **SHARPNESS: THE THRESHOLD EXPONENT IS EXACTLY THREE.**

`cubeRead` satisfies the two clauses of `wilson_reflection_positive_at`, obeys the contact-relative
condition at exponent `3` with constant `1` beyond every lag of one, and its circular second moments
exceed every `B`. So the exponent `4` in `circ_moment_le_of_contact_relative` is not a margin: at `3`
the statement is FALSE.

It is the same mechanism as `ContactDominance.square_share_is_not_enough` one exponent up — a profile
`1/kˢ` has squared-lag total `∑ k²/kˢ`, which is the harmonic series at `s = 3` exactly as a square
share has weighted total `∑ (2m+1)/(m+1)²` at `s = 2`. -/
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

/-- **At exponent three there is NO bound at all** — not a weaker one, none.

Stated without the criterion's own constant, so that nothing turns on how
`∑' k, k²·quarticWeight m₀ C k` evaluates at the threshold: for EVERY `B` whatsoever, some read
satisfying the two clauses `wilson_reflection_positive_at` asserts obeys the contact-relative
condition at exponent `3` with constant `1` from lag one upward and has moment above `B`. -/
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

/-! ### Negative control: the condition is STRICTLY STRONGER than the substrate hypothesis

`Substrate.tailRead` has circular second moment at most `1` at every aperture — so it satisfies the
substrate hypothesis with `B = 1` — and admits no contact-relative bound at exponent `4` with any
constant, because its far atom's weight falls off like `(k+1)^{-3}` while the condition would ask for
`(k+1)^{-4}`. So the reduction above gives away something, and this is what: the criterion is a
sufficient condition and not a restatement. `substrate_iff_dyadic_shares` remains the only
equivalence in the file. -/

/-- The tail read's contact weight is `1`. -/
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

/-- The tail read's weight at the antipode is the tail weight. -/
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

/-- **THE CONTACT-RELATIVE CONDITION IS STRICTLY STRONGER THAN THE SUBSTRATE HYPOTHESIS.**

`Substrate.tailRead` satisfies the two clauses `wilson_reflection_positive_at` asserts, its moment is
at most `1` at every aperture, and no `(C, m₀)` makes it obey the contact-relative condition at
exponent `4`: at the antipode the condition reads `(k+1)^{-3} ≤ C·(k+1)^{-4}`, which forces
`k + 1 ≤ C`.

So `substrate_of_contact_relative_decay` is a SUFFICIENT condition that gives something away, and
what it gives away is exactly this: a correlation may satisfy the substrate hypothesis while its far
weight falls off one power too slowly for the criterion to see it. -/
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
