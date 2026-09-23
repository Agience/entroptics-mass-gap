import MassGap.LagTwoBound
import MassGap.ReflectionStrong
import MassGap.SliceTransfer
import MassGap.HaarVariance

/-!
# MassGap.SpectralBound — the lag-two threshold in the eigenvalue variable, and two route bounds

`LagTwoBound.confines_of_lag_two_ratio` reduces `ApertureRoute.ConfinesAtAnAperture` at the smallest
even aperture to `ρ 2 ≤ K * ρ 0` at every nonnegative coupling, with `K` strictly below
`LagTwoBound.lagTwoThreshold`. This module restates that in the subdominant-eigenvalue variable,
proves the restatement is an equivalence, and establishes two facts about candidate routes.

## Section 1: the threshold in the eigenvalue variable

`lambdaThreshold = (1 - c) / (1 + c)` at `c = (3 : ℝ) ^ (-(1 : ℝ) / 4)`, and
`lambdaThreshold_sq : lambdaThreshold ^ 2 = LagTwoBound.lagTwoThreshold` holds by `rfl` — no square
root is extracted, because `lagTwoThreshold` is already written as a square.

`floor_sq_tight` and `floor_tight` re-derive the floor's bracket one digit finer than
`LagTwoBound.floor_bounds`, from `LagTwoBound.floor_pow_four` and `ConfinesZero.floor_pos`; only the
lower digit is new, since `floor_bounds`' upper bound is already `0.759836`.
`lambdaThreshold_gt` and `lambdaThreshold_lt` then bracket the threshold strictly between `0.136469`
and `0.13647`.

Scope on the bracket: `0.13647` is an upper bound, so a hypothesis `Λ < 0.13647` does not give the
criterion. `0.136469` is the largest five-digit numeral provably below the threshold, and
`confines_of_subdominant_le` is stated at that value. Both rationals report the closed form; the
closed form is what decides.

## Section 2: the eigenvalue variable is a change of variable

`SpectralAt β Λ` says the two moments the extent-four criterion reads are `ρ 0 = ∑ w i` and
`ρ 2 = ∑ w i * lam i ^ 2` for finitely many `w i ≥ 0` and `|lam i| ≤ Λ`. That is `ρ d = ∑ w i * lam i ^ d`
at `d = 0` and `d = 2`; no operator, no completeness and no identification of a partition function
with a trace appears.

`lag_two_le_of_spectralAt` gives `ρ 2 ≤ Λ ^ 2 * ρ 0`, and `spectralAt_iff` proves the converse at
every real coupling:

    SpectralAt β Λ  ↔  0 ≤ Λ ∧ ρ 2 ≤ Λ ^ 2 * ρ 0.

The backward direction uses one weight and one eigenvalue, `w = ρ 0` and `lam = √(ρ 2 / ρ 0)`,
admissible because `PlaqVariance.corrClay_zero_pos` makes the denominator positive and
`ReflectionStrong.corrClay_nonneg_even_lag` makes the numerator nonnegative at lag two with no
condition on the coupling. So at this extent the two forms of the criterion are the same inequality
under `K = Λ ^ 2`, and `confines_of_subdominant_bound` is `confines_of_lag_two_ratio`
reparametrised.

`SliceTransfer.transferKernel_selfAdjoint_psd` proves the slice kernel symmetric and
positive-semidefinite and does not identify the partition function with a trace of its powers; that
is unchanged, and by `spectralAt_iff` it is not required for the statements here.

## Section 3: the remaining obligation, and the expansion's domain

`LagTwoBound.exists_cut_lag_two_ratio` proves the ratio bound at any positive constant on a derived
interval `[0, b]`, from `StrongCoupling.corrClay_abs_le_coreConst_mul_rate_pow` over
`ContactFloor.corrClay_zero_ge`. Its constant depends on `touchDeg` and `β` only — no
`Fintype.card Pq` and no extent.

`TailRatioAtEveryCut` and `TailSubdominantAtEveryCut` state a bound of the same shape on `[b, ∞)` at
every cut, and `confines_of_tail_ratio` and `confines_of_tail_subdominant` prove each sufficient;
the gluing costs nothing because `exists_cut_lag_two_ratio` supplies a cut at every constant. Both
are sufficient conditions only: `ConfinesAtAnAperture` asks for the criterion pointwise in `β`,
while these ask for one constant uniform on each tail, so they are the stronger request and no
converse is proved here. `TailRatio.ratio_below_threshold_of_tail_ratio` and
`TailRatio.tail_ratio_of_ratio_below_threshold_of_limit` relate them to the pointwise form.

`expansion_domain_bounded` shows that `corrClay_abs_le_coreConst_mul_rate_pow`'s own hypothesis
`coreRate (16 * 4) β < 1` fails from some coupling onward: `StrongArm.coreRate_exceeds` makes the
rate exceed one somewhere and `StrongArm.coreRate_mono_beta` keeps it there. That is a statement
about the estimate, not about the correlation.

## Section 4: the Doeblin minorisation constant

`abs_hsRe_le` and `abs_sliceForm_le` confine the cross form to `[-N * L, N * L]`, with `L` the slice's
link count. `sliceForm_one` evaluates it at the constant identity as `N * L`, and `sliceForm_flip`
at `HaarVariance.flipEl m` as `(m - 2) * L`, which is `(N - 4) * L` at `N = m + 2`.
`crossFactor_ratio` turns that difference into the identity

    crossFactor b 1 flip = exp (-(4 * b * L)) * crossFactor b 1 1,

so the ratio of the cross factor's two values is exactly `exp (-(4 * b * L))`.
`doeblinFloor b L = 1 - exp (-(4 * b * L))` names the subdominant-ratio value a minorisation of
constant `exp (-(4 * b * L))` would report, `doeblinFloor_exceeds` shows it passes any target below
one once `L` is large enough, and `doeblin_exceeds_lambdaThreshold` instantiates that at
`lambdaThreshold`.

Scope on section 4. The Doeblin theorem itself — that `T (V, W) ≥ ε * reference` bounds the
subdominant ratio by `1 - ε` — is not formalised here, and `doeblinFloor` asserts nothing about it;
everything proved about `doeblinFloor` is real analysis about `1 - exp (-(4 * b * L))`.
That `L` grows with the lattice is not proved either: `L` enters as `Fintype.card ι` for an
arbitrary finite index, and `SliceTransfer.sliceLinks`' cardinality is not computed in this tree.
Nothing here bounds the true subdominant eigenvalue from below or claims the slice kernel has no
gap.

## Scope

No eigenvalue and no ratio is bounded on any tail here. `SpectralAt β Λ` is not established for any
`Λ` below `lambdaThreshold` at every coupling, and by `spectralAt_iff` that is the same statement as
`TailRatioAtEveryCut`. No measured quantity appears in any statement or proof in this module.
-/

namespace MassGap.SpectralBound

open MassGap MassGap.SUN MassGap.CharacterExpansion

/-! ## 1. The threshold in the eigenvalue variable -/

/-- `0.5773502 < ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 < 0.5773507`, one digit finer than
`LagTwoBound.floor_sq_bounds`. The square `c ^ 2` satisfies `(c ^ 2) ^ 2 = 1 / 3` by
`LagTwoBound.floor_pow_four`, and is positive by `ConfinesZero.floor_pos`; each side follows by
contradiction and `norm_num` on the squared comparison.

DERIVED: `3` and the `1/3` are `LagTwoBound.floor_pow_four`'s, which is `Floor.lean`'s directed-path
count; `0.5773502` and `0.5773507` are the two rationals whose squares bracket `1/3` at this
resolution and they REPORT the derived quantity rather than decide anything. The `4` is the exponent
`floor_pow_four` carries and the `2` is the square being bracketed. -/
theorem floor_sq_tight :
    0.5773502 < ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2
      ∧ ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 < 0.5773507 := by
  set c : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hcdef
  have hc0 : 0 < c := by rw [hcdef]; exact MassGap.ConfinesZero.floor_pos
  have h4 : c ^ (4 : ℕ) = 1 / 3 := by rw [hcdef]; exact MassGap.LagTwoBound.floor_pow_four
  have hs0 : 0 < c ^ 2 := by positivity
  have hs2 : (c ^ 2) ^ 2 = 1 / 3 := by rw [← h4]; ring
  constructor
  · by_contra hcon
    rw [not_lt] at hcon
    have hsq : (c ^ 2) ^ 2 ≤ (0.5773502 : ℝ) ^ 2 := by nlinarith [hs0, hcon]
    rw [hs2] at hsq
    norm_num at hsq
  · by_contra hcon
    rw [not_lt] at hcon
    have hsq : ((0.5773507 : ℝ)) ^ 2 ≤ (c ^ 2) ^ 2 := by nlinarith [hs0, hcon]
    rw [hs2] at hsq
    norm_num at hsq

#print axioms floor_sq_tight

/-- `0.7598356 < (3 : ℝ) ^ (-(1 : ℝ) / 4) < 0.759836`, from `floor_sq_tight` and positivity of the
floor.

Scope: only the lower digit improves on `LagTwoBound.floor_bounds`. `lambdaThreshold < 0.13647` has
a margin of about `4.1e-7` in the floor, which `floor_bounds`' lower digit `0.759835` does not
clear; its upper bound is already `0.759836` and is reproduced unchanged.

DERIVED: `3`, `1` and `4` are `3^{−(1)/4}`'s, inherited from `LagTwoBound.floor_pow_four`;
`0.7598356` and `0.759836` are the two rationals whose squares bracket `3^{−1/2}` at the resolution
`floor_sq_tight` supplies, and they report rather than decide. Nothing is chosen. -/
theorem floor_tight :
    0.7598356 < (3 : ℝ) ^ (-(1 : ℝ) / 4) ∧ (3 : ℝ) ^ (-(1 : ℝ) / 4) < 0.759836 := by
  obtain ⟨hlo, hhi⟩ := floor_sq_tight
  set c : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hcdef
  have hc0 : 0 < c := by rw [hcdef]; exact MassGap.ConfinesZero.floor_pos
  constructor
  · by_contra hcon
    rw [not_lt] at hcon
    have hsq : c ^ 2 ≤ (0.7598356 : ℝ) ^ 2 := by nlinarith [hc0, hcon]
    have : (0.5773502 : ℝ) < (0.7598356 : ℝ) ^ 2 := lt_of_lt_of_le hlo hsq
    norm_num at this
  · by_contra hcon
    rw [not_lt] at hcon
    have hsq : ((0.759836 : ℝ)) ^ 2 ≤ c ^ 2 := by nlinarith [hc0, hcon]
    have : ((0.759836 : ℝ)) ^ 2 < 0.5773507 := lt_of_le_of_lt hsq hhi
    norm_num at this

#print axioms floor_tight

/-- The threshold on the subdominant eigenvalue: `(1 - c) / (1 + c)` at
`c = (3 : ℝ) ^ (-(1 : ℝ) / 4)`. This is the positive root of `LagTwoBound.lagTwoThreshold`, and
`lambdaThreshold_sq` records that the square relation holds by `rfl`, since `lagTwoThreshold` is
already written as a square.

DERIVED: inherited digit for digit from `LagTwoBound.lagTwoThreshold`. `3` and `4` are the
directed-path count and the per-area normalisation of `Floor.lean`, which together are the entropy
floor `κ₀ = ¼ log 3` and hence `c = e^{−κ₀}`; the two `1`s are the `1 − c` and `1 + c` of the
log-convexity quadratic whose discriminant is identically `4`, so its positive root is this ratio.
No numeral is chosen and none is fitted. -/
noncomputable def lambdaThreshold : ℝ :=
  (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4))

#print axioms lambdaThreshold

/-- `lambdaThreshold ^ 2 = LagTwoBound.lagTwoThreshold`, by `rfl`.

DERIVED: the `2` is the lag index of `ρ(2)`, which is why the eigenvalue threshold is the square root
of the ratio threshold and not some other power. -/
theorem lambdaThreshold_sq : lambdaThreshold ^ 2 = MassGap.LagTwoBound.lagTwoThreshold := rfl

#print axioms lambdaThreshold_sq

/-- `0 < lambdaThreshold`, by `div_pos` from `0 < c < 1` (`ConfinesZero.floor_pos` and
`ConfinesZero.floor_lt_one`).

DERIVED: the `0` and the two `1`s are the sign and the `1 ± c` of the definition. -/
theorem lambdaThreshold_pos : 0 < lambdaThreshold := by
  have hc0 : 0 < (3 : ℝ) ^ (-(1 : ℝ) / 4) := MassGap.ConfinesZero.floor_pos
  have hc1 : (3 : ℝ) ^ (-(1 : ℝ) / 4) < 1 := MassGap.ConfinesZero.floor_lt_one
  unfold lambdaThreshold
  exact div_pos (by linarith) (by linarith)

#print axioms lambdaThreshold_pos

/-- `0.136469 < lambdaThreshold`, from `floor_tight`'s upper bound after clearing the denominator.
This is the largest five-digit numeral in this position provably below the threshold.

DERIVED: `0.136469` REPORTS the derived `lambdaThreshold` and decides nothing; it is the truncation
of the closed form, and `confines_of_subdominant_le` is the one statement that reads it. -/
theorem lambdaThreshold_gt : 0.136469 < lambdaThreshold := by
  obtain ⟨_, hhi⟩ := floor_tight
  have hc0 : 0 < (3 : ℝ) ^ (-(1 : ℝ) / 4) := MassGap.ConfinesZero.floor_pos
  unfold lambdaThreshold
  set c : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hcdef
  have hden : (0 : ℝ) < 1 + c := by linarith
  rw [lt_div_iff₀ hden]
  linarith

#print axioms lambdaThreshold_gt

/-- `lambdaThreshold < 0.13647`, from `floor_tight`'s lower bound. `0.13647` is a rounding up of
the threshold, so a hypothesis `Λ < 0.13647` does not give the criterion and no statement below is
available at that value.

DERIVED: `0.13647` REPORTS the derived `lambdaThreshold` from above; it decides nothing and is used
nowhere except to bracket. -/
theorem lambdaThreshold_lt : lambdaThreshold < 0.13647 := by
  obtain ⟨hlo, _⟩ := floor_tight
  have hc0 : 0 < (3 : ℝ) ^ (-(1 : ℝ) / 4) := MassGap.ConfinesZero.floor_pos
  unfold lambdaThreshold
  set c : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hcdef
  have hden : (0 : ℝ) < 1 + c := by linarith
  rw [div_lt_iff₀ hden]
  linarith

#print axioms lambdaThreshold_lt

/-! ## 2. From a subdominant-eigenvalue bound to `ConfinesAtAnAperture` -/

/-- `SpectralAt β Λ`: there are `n`, weights `w : Fin n → ℝ` and eigenvalues `lam : Fin n → ℝ` with
`0 ≤ w i` and `|lam i| ≤ Λ` at every `i`, such that `wilsonCorrAt 3 β 0 = ∑ i, w i` and
`wilsonCorrAt 3 β 2 = ∑ i, w i * lam i ^ 2`.

This is `ρ d = ∑ i, w i * lam i ^ d` read at `d = 0` and `d = 2`. No operator, no completeness
condition and no identification of a partition function with a trace enters. A `Prop`; nothing in
this module establishes it for any `Λ`.

Scope: `SliceTransfer.transferKernel_selfAdjoint_psd` builds a symmetric positive-semidefinite slice
kernel; the Fubini step relating a partition function to a trace, and a spectral decomposition
beyond it, are not in this tree.

DERIVED: `0` and `2` are the two lag indices `ConfinesZero.confines_extent_four_of_lag_two_small`
reads, and the `2` in `λᵢ²` is that same lag. The `3` in `wilsonCorrAt 3` is the extent-four index
`N + 1 = 4`, the smallest even extent `EvenAp` admits. -/
def SpectralAt (β Λ : ℝ) : Prop :=
  ∃ (n : ℕ) (w lam : Fin n → ℝ),
    (∀ i, 0 ≤ w i) ∧ (∀ i, |lam i| ≤ Λ)
      ∧ MassGap.wilsonCorrAt 3 β 0 = ∑ i, w i
      ∧ MassGap.wilsonCorrAt 3 β 2 = ∑ i, w i * lam i ^ 2

#print axioms SpectralAt

/-- The same at every nonnegative coupling — the shape `LagTwoBound.confines_of_lag_two_ratio`
consumes.

DERIVED: the `0` is the sign of the coupling half-line the bridge reads. -/
def LagSpectralBound (Λ : ℝ) : Prop := ∀ β : ℝ, 0 ≤ β → SpectralAt β Λ

#print axioms LagSpectralBound

/-- `SpectralAt β Λ → wilsonCorrAt 3 β 2 ≤ Λ ^ 2 * wilsonCorrAt 3 β 0`. Each term satisfies
`w i * lam i ^ 2 ≤ Λ ^ 2 * w i` because the weight is nonnegative and `|lam i| ≤ Λ`, and the
right-hand sides sum to `Λ ^ 2 * ρ 0`. The `d = 0` moment is what makes the conclusion a ratio
rather than an absolute bound.

DERIVED: the `2`s are the lag index and the square it forces; `0` is the contact lag the ratio is
normalised by; `3` is the extent-four index `N + 1 = 4`. -/
theorem lag_two_le_of_spectralAt {β Λ : ℝ} (h : SpectralAt β Λ) :
    MassGap.wilsonCorrAt 3 β 2 ≤ Λ ^ 2 * MassGap.wilsonCorrAt 3 β 0 := by
  obtain ⟨n, w, lam, hw, hl, h0, h2⟩ := h
  rw [h2, h0, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have habs : (0 : ℝ) ≤ |lam i| := abs_nonneg _
  have hsq : lam i ^ 2 ≤ Λ ^ 2 := by
    nlinarith [mul_self_le_mul_self habs (hl i), sq_abs (lam i)]
  nlinarith [hw i, hsq]

#print axioms lag_two_le_of_spectralAt

/-- `SpectralAt β Λ ↔ (0 ≤ Λ ∧ wilsonCorrAt 3 β 2 ≤ Λ ^ 2 * wilsonCorrAt 3 β 0)`, at every real
coupling.

Forward is `lag_two_le_of_spectralAt` together with non-emptiness of the index type: `∑ w i = ρ 0`
is positive by `PlaqVariance.corrClay_zero_pos`, so some `i` exists and `0 ≤ |lam i| ≤ Λ`.
Backward uses one weight and one eigenvalue, `w = ρ 0` and `lam = √(ρ 2 / ρ 0)`, and needs two facts
holding at every real `β`: `corrClay_zero_pos` for the denominator and
`ReflectionStrong.corrClay_nonneg_even_lag` at `Nap = 3`, half-extent `2` and the even lag two for
the numerator.

Scope: the two forms of the criterion at this extent are the same inequality under `K = Λ ^ 2`.
Neither a transfer operator nor a spectral decomposition is needed to state or use either.

DERIVED: `0` and `2` are the two lag indices; `3` is the extent-four index `N + 1 = 4`; the `2` in
`Λ²` is the lag. The `1` and the `2` passed to `corrClay_nonneg_even_lag` are `Nap = 3`'s
half-extent data, that lemma's own. -/
theorem spectralAt_iff (β Λ : ℝ) :
    SpectralAt β Λ ↔
      (0 ≤ Λ ∧ MassGap.wilsonCorrAt 3 β 2 ≤ Λ ^ 2 * MassGap.wilsonCorrAt 3 β 0) := by
  have hρ0 : 0 < MassGap.wilsonCorrAt 3 β 0 := by
    rw [MassGap.StrongArm.wilsonCorrAt_eq_corrClay]
    exact MassGap.PlaqVariance.corrClay_zero_pos 3 β
  have hρ2 : 0 ≤ MassGap.wilsonCorrAt 3 β 2 := by
    rw [MassGap.StrongArm.wilsonCorrAt_eq_corrClay]
    exact MassGap.ReflectionStrong.corrClay_nonneg_even_lag 3 2 (by norm_num) (by norm_num) β
      (by decide)
  constructor
  · intro h
    refine ⟨?_, lag_two_le_of_spectralAt h⟩
    obtain ⟨n, w, lam, hw, hl, h0, _⟩ := h
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exfalso
      subst hn
      rw [h0] at hρ0
      simp at hρ0
    · exact le_trans (abs_nonneg (lam ⟨0, hn⟩)) (hl ⟨0, hn⟩)
  · rintro ⟨hΛ0, hle⟩
    refine ⟨1, fun _ => MassGap.wilsonCorrAt 3 β 0,
      fun _ => Real.sqrt (MassGap.wilsonCorrAt 3 β 2 / MassGap.wilsonCorrAt 3 β 0),
      fun _ => hρ0.le, fun _ => ?_, by simp, ?_⟩
    · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      have hdiv : MassGap.wilsonCorrAt 3 β 2 / MassGap.wilsonCorrAt 3 β 0 ≤ Λ ^ 2 := by
        rw [div_le_iff₀ hρ0]
        exact hle
      calc Real.sqrt (MassGap.wilsonCorrAt 3 β 2 / MassGap.wilsonCorrAt 3 β 0)
          ≤ Real.sqrt (Λ ^ 2) := Real.sqrt_le_sqrt hdiv
        _ = Λ := Real.sqrt_sq hΛ0
    · have hdnn : 0 ≤ MassGap.wilsonCorrAt 3 β 2 / MassGap.wilsonCorrAt 3 β 0 :=
        div_nonneg hρ2 hρ0.le
      have hne : MassGap.wilsonCorrAt 3 β 0 ≠ 0 := ne_of_gt hρ0
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Real.sq_sqrt hdnn]
      field_simp
      norm_num

#print axioms spectralAt_iff

/-- From `0 ≤ Λ`, `Λ < lambdaThreshold` and `LagSpectralBound Λ`, the conclusion
`ApertureRoute.ConfinesAtAnAperture`. `lag_two_le_of_spectralAt` at each coupling supplies
`confines_of_lag_two_ratio`'s hypothesis at `K = Λ ^ 2`, and `lambdaThreshold_sq` puts that constant
under the threshold. The hypothesis `0 ≤ Λ` is what makes squaring preserve the strict
inequality.

DERIVED: `0` is that sign; the `2` is the square that carries `Λ` to the ratio constant. -/
theorem confines_of_subdominant_bound {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : Λ < lambdaThreshold)
    (h : LagSpectralBound Λ) : ApertureRoute.ConfinesAtAnAperture := by
  refine MassGap.LagTwoBound.confines_of_lag_two_ratio (Λ ^ 2) ?_
    (fun β hβ => lag_two_le_of_spectralAt (h β hβ))
  rw [← lambdaThreshold_sq]
  nlinarith [hΛ, hΛ0, lambdaThreshold_pos]

#print axioms confines_of_subdominant_bound

/-- The same conclusion from `Λ ≤ 0.136469` in place of `Λ < lambdaThreshold`, via
`lambdaThreshold_gt`.

Scope: `0.136469` is the largest five-digit numeral provably below the threshold; the content is
`confines_of_subdominant_bound` at the closed form. `0.13647` is not available, since
`lambdaThreshold_lt` places the threshold strictly below it.

DERIVED: `0.136469` reports `lambdaThreshold` from below (`lambdaThreshold_gt`) and decides nothing;
`0` is a sign. -/
theorem confines_of_subdominant_le {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ 0.136469)
    (h : LagSpectralBound Λ) : ApertureRoute.ConfinesAtAnAperture :=
  confines_of_subdominant_bound hΛ0 (lt_of_le_of_lt hΛ lambdaThreshold_gt) h

#print axioms confines_of_subdominant_le

/-! ## 3. What remains, as named `Prop`s, and why the expansion cannot supply it -/

/-- The proposition: at every cut `0 < b` there is a `K < LagTwoBound.lagTwoThreshold` with
`wilsonCorrAt 3 β 2 ≤ K * wilsonCorrAt 3 β 0` for every `β ≥ b`. A bound of the shape
`LagTwoBound.exists_cut_lag_two_ratio` proves on `[0, b]`, asked instead on `[b, ∞)`, at every cut.
A `Prop`; nothing here proves it.

Scope: quantifying over every cut is what makes the gluing in `confines_of_tail_ratio` free, since
the cut `exists_cut_lag_two_ratio` supplies is not the caller's to choose.

DERIVED: `2` and `0` are the two lag indices; `3` is the extent-four index `N + 1 = 4`; `0 < b` is a
sign. `lagTwoThreshold` is `LagTwoBound`'s derived number. -/
def TailRatioAtEveryCut : Prop :=
  ∀ b : ℝ, 0 < b → ∃ K : ℝ, K < MassGap.LagTwoBound.lagTwoThreshold ∧
    ∀ β : ℝ, b ≤ β → MassGap.wilsonCorrAt 3 β 2 ≤ K * MassGap.wilsonCorrAt 3 β 0

#print axioms TailRatioAtEveryCut

/-- `TailRatioAtEveryCut → ApertureRoute.ConfinesAtAnAperture`. Below the cut,
`LagTwoBound.exists_cut_lag_two_ratio` at half the threshold; above it, the hypothesis at that same
cut; the two constants are joined by `max`, which stays under the threshold because both do.
`PlaqVariance.corrClay_zero_pos` is what allows weakening a smaller constant to a larger one, the
denominator being strictly positive at every real coupling and extent.

Scope: the implication runs one way; nothing here says the tail must be closed this way.

DERIVED: no numeral occurs in the statement. The halving of the threshold in the proof is a device
for strictness; any constant strictly inside it would serve. -/
theorem confines_of_tail_ratio (h : TailRatioAtEveryCut) : ApertureRoute.ConfinesAtAnAperture := by
  have hT : 0 < MassGap.LagTwoBound.lagTwoThreshold := MassGap.LagTwoBound.lagTwoThreshold_pos
  obtain ⟨b, hb, hlow⟩ :=
    MassGap.LagTwoBound.exists_cut_lag_two_ratio (MassGap.LagTwoBound.lagTwoThreshold / 2)
      (by linarith)
  obtain ⟨K₁, hK₁, hhigh⟩ := h b hb
  refine MassGap.LagTwoBound.confines_of_lag_two_ratio
    (max (MassGap.LagTwoBound.lagTwoThreshold / 2) K₁) (max_lt (by linarith) hK₁) ?_
  intro β hβ
  have hρ0 : 0 < MassGap.wilsonCorrAt 3 β 0 := by
    rw [MassGap.StrongArm.wilsonCorrAt_eq_corrClay]
    exact MassGap.PlaqVariance.corrClay_zero_pos 3 β
  by_cases hc : β ≤ b
  · exact le_trans (hlow β hβ hc)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hρ0.le)
  · exact le_trans (hhigh β (not_le.mp hc).le)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hρ0.le)

#print axioms confines_of_tail_ratio

/-- The proposition: at every cut `0 < b` there is a `Λ` with `0 ≤ Λ`, `Λ < lambdaThreshold` and
`SpectralAt β Λ` for every `β ≥ b`. The eigenvalue-variable form of `TailRatioAtEveryCut`. A `Prop`;
nothing here proves it.

DERIVED: `0` is a sign; `lambdaThreshold` is the derived closed form of section 1. -/
def TailSubdominantAtEveryCut : Prop :=
  ∀ b : ℝ, 0 < b → ∃ Λ : ℝ, 0 ≤ Λ ∧ Λ < lambdaThreshold ∧ ∀ β : ℝ, b ≤ β → SpectralAt β Λ

#print axioms TailSubdominantAtEveryCut

/-- `TailSubdominantAtEveryCut → ApertureRoute.ConfinesAtAnAperture`, by squaring the eigenvalue
bound into a ratio bound at each cut and applying `confines_of_tail_ratio`.

DERIVED: no numeral occurs in the statement. The square in the proof is `lambdaThreshold_sq`'s. -/
theorem confines_of_tail_subdominant (h : TailSubdominantAtEveryCut) :
    ApertureRoute.ConfinesAtAnAperture := by
  refine confines_of_tail_ratio (fun b hb => ?_)
  obtain ⟨Λ, hΛ0, hΛ, hsp⟩ := h b hb
  refine ⟨Λ ^ 2, ?_, fun β hβ => lag_two_le_of_spectralAt (hsp β hβ)⟩
  rw [← lambdaThreshold_sq]
  nlinarith [hΛ, hΛ0, lambdaThreshold_pos]

#print axioms confines_of_tail_subdominant

/-- There is `0 < B` such that `1 < StrongCoupling.coreRate (16 * 4) β` for every `β ≥ B`.
`StrongArm.coreRate_exceeds` makes the rate exceed one somewhere and
`StrongArm.coreRate_mono_beta` keeps it above one thereafter.

Scope: `StrongCoupling.corrClay_abs_le_coreConst_mul_rate_pow` carries the hypothesis
`coreRate (16 * 4) β < 1`, so no instance of that estimate applies above `B`. This is a statement
about the estimate's hypothesis, not about the correlation; nothing here says `ρ 2 / ρ 0` is large
at strong coupling.

DERIVED: `16·4` is `StrongCoupling.touchDeg_bd_le` at `dim = 4`, the same degree
`LagTwoBound.exists_cut_lag_two_ratio` uses; `1` is the geometric series' own radius, not a cutoff;
`0` is a sign. -/
theorem expansion_domain_bounded :
    ∃ B : ℝ, 0 < B ∧ ∀ β : ℝ, B ≤ β → 1 < MassGap.StrongCoupling.coreRate (16 * 4) β := by
  obtain ⟨β₀, hβ₀, hlt⟩ := MassGap.StrongArm.coreRate_exceeds (16 * 4) 1
  refine ⟨max β₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun β hβ => ?_⟩
  have h1 : β₀ ≤ β := le_trans (le_max_left _ _) hβ
  exact lt_of_lt_of_le hlt (MassGap.StrongArm.coreRate_mono_beta (16 * 4) hβ₀ h1)

#print axioms expansion_domain_bounded

/-! ## 4. The Doeblin route, refuted in the volume -/

section Doeblin

variable {N : ℕ} {ι : Type} [Fintype ι]

/-- `|hsRe V W| ≤ (N : ℝ)` for `V W : SU N`. `CrossingIntegration.hsRe_coe_eq` presents `hsRe V W`
as the real part of the trace of `V * W⁻¹`, itself an element of `SU N`, and
`WilsonAction.abs_re_trace_le` bounds that by the rank.

DERIVED: no numeral occurs in the statement; the bound is the rank `N`, read off
`abs_re_trace_le`. -/
theorem abs_hsRe_le (V W : SU N) :
    |hsRe (V : Matrix (Fin N) (Fin N) ℂ) (W : Matrix (Fin N) (Fin N) ℂ)| ≤ (N : ℝ) := by
  rw [MassGap.CrossingIntegration.hsRe_coe_eq]
  exact MassGap.WilsonAction.abs_re_trace_le _

#print axioms abs_hsRe_le

/-- `|SliceTransfer.sliceForm V W| ≤ (N : ℝ) * (Fintype.card ι : ℝ)`: the slice form is a sum of
`Fintype.card ι` terms each bounded by `abs_hsRe_le`.

Scope: the bound grows with the link count. `sliceForm_one` and `sliceForm_flip` evaluate the form
at two configurations, showing the range is not slack.

DERIVED: `N` is the rank and `Fintype.card ι` is the slice's link count; both are read off the
object, neither is chosen. -/
theorem abs_sliceForm_le (V W : ι → SU N) :
    |MassGap.SliceTransfer.sliceForm V W| ≤ (N : ℝ) * (Fintype.card ι : ℝ) := by
  unfold MassGap.SliceTransfer.sliceForm
  calc |∑ l : ι, hsRe ((V l : Matrix (Fin N) (Fin N) ℂ)) ((W l : Matrix (Fin N) (Fin N) ℂ))|
      ≤ ∑ l : ι, |hsRe ((V l : Matrix (Fin N) (Fin N) ℂ)) ((W l : Matrix (Fin N) (Fin N) ℂ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l : ι, (N : ℝ) := Finset.sum_le_sum (fun l _ => abs_hsRe_le (V l) (W l))
    _ = (N : ℝ) * (Fintype.card ι : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

#print axioms abs_sliceForm_le

/-- `SliceTransfer.sliceForm 1 1 = (N : ℝ) * (Fintype.card ι : ℝ)` at the constant identity, since
`hsRe 1 1` is the real trace of the identity matrix, which is `N`. So `abs_sliceForm_le`'s bound is
attained at the top.

DERIVED: `N` is the rank, `Fintype.card ι` the link count; `1` is the group identity. -/
theorem sliceForm_one :
    MassGap.SliceTransfer.sliceForm (fun _ : ι => (1 : SU N)) (fun _ => (1 : SU N))
      = (N : ℝ) * (Fintype.card ι : ℝ) := by
  have hterm : hsRe ((1 : SU N) : Matrix (Fin N) (Fin N) ℂ)
      ((1 : SU N) : Matrix (Fin N) (Fin N) ℂ) = (N : ℝ) := by
    rw [MassGap.CrossingIntegration.hsRe_coe_eq]
    simp
  unfold MassGap.SliceTransfer.sliceForm
  rw [Finset.sum_congr rfl (fun l _ => hterm), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_comm]

#print axioms sliceForm_one

/-- `SliceTransfer.sliceForm 1 (flipEl m) = ((m : ℝ) - 2) * (Fintype.card ι : ℝ)`.
`HaarVariance.flipEl m` is `diag (-1, -1, 1, …, 1)` in `SU (m + 2)` and is its own conjugate
transpose (`flipMat_star`), so each term is `Re (trace (flipMat m)) = m - 2` by
`HaarVariance.reTr_flipEl`. At `N = m + 2` that value is `N - 4` per link, so the two evaluations
differ by `4 * Fintype.card ι`.

DERIVED: `m − 2` is `HaarVariance.reTr_flipEl`'s value, which counts the two `−1` entries the
determinant condition forces; `2` in `m + 2` is the rank offset that makes `N ≥ 2` structural. -/
theorem sliceForm_flip (m : ℕ) :
    MassGap.SliceTransfer.sliceForm (fun _ : ι => (1 : SU (m + 2)))
        (fun _ => MassGap.HaarVariance.flipEl m)
      = ((m : ℝ) - 2) * (Fintype.card ι : ℝ) := by
  have htr : (Matrix.trace (MassGap.HaarVariance.flipMat m)).re = (m : ℝ) - 2 :=
    MassGap.HaarVariance.reTr_flipEl m
  have hterm : hsRe ((1 : SU (m + 2)) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)
      ((MassGap.HaarVariance.flipEl m : SU (m + 2)) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)
      = (m : ℝ) - 2 := by
    show (Matrix.trace ((1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)
        * Matrix.conjTranspose (MassGap.HaarVariance.flipMat m))).re = (m : ℝ) - 2
    rw [one_mul, ← Matrix.star_eq_conjTranspose, MassGap.HaarVariance.flipMat_star]
    exact htr
  unfold MassGap.SliceTransfer.sliceForm
  rw [Finset.sum_congr rfl (fun l _ => hterm), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_comm]

#print axioms sliceForm_flip

/-- `crossFactor b V W = Real.exp (b * SliceTransfer.sliceForm V W)`, the part of
`SliceTransfer.transferKernel` depending on both arguments. `transferKernel_eq_crossFactor` records
the factorisation `exp (-s V / 2) * crossFactor b V W * exp (-s W / 2)`, whose outer factors each
depend on one argument. That those outer factors cancel from the ratio a minorisation forms is not
proved here.

DERIVED: `b` is the caller's coupling; no numeral. -/
noncomputable def crossFactor (b : ℝ) (V W : ι → SU N) : ℝ :=
  Real.exp (b * MassGap.SliceTransfer.sliceForm V W)

#print axioms crossFactor

/-- `SliceTransfer.transferKernel b s V W = exp (-(s V) / 2) * crossFactor b V W * exp (-(s W) / 2)`,
by `rfl`.

DERIVED: the `2` is `transferKernel`'s own even split of the intra-slice action between its two
arguments, which is what makes the kernel symmetric. -/
theorem transferKernel_eq_crossFactor (b : ℝ) (s : (ι → SU N) → ℝ) (V W : ι → SU N) :
    MassGap.SliceTransfer.transferKernel b s V W
      = Real.exp (-(s V) / 2) * crossFactor b V W * Real.exp (-(s W) / 2) := rfl

#print axioms transferKernel_eq_crossFactor

/-- An identity between two values of the cross factor:

    crossFactor b 1 (flipEl m) = exp (-(4 * b * Fintype.card ι)) * crossFactor b 1 1,

at every real `b` and every `m`. Substituting `sliceForm_one` and `sliceForm_flip` and combining the
exponentials.

Scope: this is an equality between two evaluations of the cross factor, not a bound on it. Reading
it as a bound on a minorisation constant requires `0 ≤ b`, so that the flipped value is the smaller
of the two, and the Doeblin argument itself, neither of which is proved here.

DERIVED: `4` is `(m + 2) - (m - 2)`, the difference between the two evaluated slice forms per link,
which counts the two `-1` entries of `flipEl` once in each trace; `2` is the rank offset in `m + 2`;
`1` is the group identity in the first argument. `Fintype.card ι` is the link count. -/
theorem crossFactor_ratio (b : ℝ) (m : ℕ) :
    crossFactor b (fun _ : ι => (1 : SU (m + 2))) (fun _ => MassGap.HaarVariance.flipEl m)
      = Real.exp (-(4 * b * (Fintype.card ι : ℝ)))
        * crossFactor b (fun _ : ι => (1 : SU (m + 2))) (fun _ => (1 : SU (m + 2))) := by
  unfold crossFactor
  rw [sliceForm_one, sliceForm_flip, ← Real.exp_add]
  congr 1
  push_cast
  ring

#print axioms crossFactor_ratio

end Doeblin

/-- `doeblinFloor b L = 1 - Real.exp (-(4 * b * L))`, a real-valued function of a coupling and a
link count.

Scope: the Doeblin argument — from `T (V, W) ≥ ε * reference` at every pair, a bound `1 - ε` on the
subdominant ratio — is not formalised in this tree, and this definition asserts nothing about it. It
names the value that argument would report at `ε = exp (-(4 * b * L))`, which `crossFactor_ratio`
identifies as the cross factor's own ratio. Everything proved about `doeblinFloor` below is real
analysis about `1 - exp (-(4 * b * L))`.

DERIVED: `4` is `crossFactor_ratio`'s, the gap between the two evaluated cross forms; `1` is the
Dobrushin coefficient's own normalisation; `L` is the slice's link count and `b` the coupling. -/
noncomputable def doeblinFloor (b : ℝ) (L : ℕ) : ℝ := 1 - Real.exp (-(4 * b * (L : ℝ)))

#print axioms doeblinFloor

/-- For `0 < b` and `Λ < 1`, there is `L₀` such that `Λ < doeblinFloor b L` for every `L ≥ L₀`. The
only analytic input is `1 + x ≤ exp x`; the threshold `L₀` is whatever `exists_nat_gt` supplies at
`1 / (4 * b * (1 - Λ))`, and no value is named for it.

DERIVED: `4` is `doeblinFloor`'s; `1` is the Dobrushin normalisation and the `1` of `1 + x ≤ eˣ`;
`0 < b` is a sign. -/
theorem doeblinFloor_exceeds {b : ℝ} (hb : 0 < b) {Λ : ℝ} (hΛ : Λ < 1) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → Λ < doeblinFloor b L := by
  have ht : 0 < 1 - Λ := by linarith
  obtain ⟨L₀, hL₀⟩ := exists_nat_gt (1 / (4 * b * (1 - Λ)))
  refine ⟨L₀, fun L hL => ?_⟩
  have hLR : ((L₀ : ℕ) : ℝ) ≤ (L : ℝ) := Nat.cast_le.mpr hL
  have hpos : (0 : ℝ) < 4 * b * (1 - Λ) := by positivity
  have hkey : 1 / (4 * b * (1 - Λ)) < (L : ℝ) := lt_of_lt_of_le hL₀ hLR
  have hone : 1 < (L : ℝ) * (4 * b * (1 - Λ)) := by
    rw [div_lt_iff₀ hpos] at hkey
    exact hkey
  set x : ℝ := 4 * b * (L : ℝ) with hxdef
  have hprod : 1 < (1 - Λ) * x := by rw [hxdef]; nlinarith [hone]
  have hbig : 1 < (1 - Λ) * (1 + x) := by nlinarith [hprod, ht]
  have hgrow : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hmul : (1 - Λ) * (1 + x) ≤ (1 - Λ) * Real.exp x :=
    mul_le_mul_of_nonneg_left hgrow ht.le
  have h1 : 1 < (1 - Λ) * Real.exp x := lt_of_lt_of_le hbig hmul
  have hcancel : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have hEF : Real.exp (-x) < 1 - Λ := by
    nlinarith [h1, hcancel, Real.exp_pos x, Real.exp_pos (-x)]
  unfold doeblinFloor
  rw [hxdef] at hEF
  linarith

#print axioms doeblinFloor_exceeds

/-- For every `0 < b` there is `L₀` such that `lambdaThreshold < doeblinFloor b L` at every
`L ≥ L₀`. `doeblinFloor_exceeds` at `Λ = lambdaThreshold`, admissible because `lambdaThreshold_lt`
puts the threshold below `0.13647` and hence below one.

Scope. The statement is about `doeblinFloor`, whose bearing on a Doeblin argument is the external
step described at that definition. That `L` grows with the lattice is not proved here: `L` enters as
`Fintype.card ι` for an arbitrary finite index, and `SliceTransfer.sliceLinks`' cardinality is not
computed in this tree. Nothing here bounds the true subdominant eigenvalue from below or says the
slice kernel has no gap.

DERIVED: `0 < b` is a sign; `lambdaThreshold` is section 1's closed form; `1` is
`lambdaThreshold_lt` composed with `0.13647 < 1`. -/
theorem doeblin_exceeds_lambdaThreshold {b : ℝ} (hb : 0 < b) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → lambdaThreshold < doeblinFloor b L :=
  doeblinFloor_exceeds hb (by linarith [lambdaThreshold_lt])

#print axioms doeblin_exceeds_lambdaThreshold

end MassGap.SpectralBound
