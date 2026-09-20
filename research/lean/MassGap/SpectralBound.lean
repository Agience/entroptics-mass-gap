import MassGap.LagTwoBound
import MassGap.ReflectionStrong
import MassGap.SliceTransfer
import MassGap.HaarVariance

/-!
# MassGap.SpectralBound — the subdominant eigenvalue B5 asks for, and where the routes to it stop

`LagTwoBound.confines_of_lag_two_ratio` reduces Clay row B5 at the smallest even aperture to one
inequality: a lag-two ratio `ρ(2) ≤ K·ρ(0)` at every nonnegative coupling with `K` strictly below the
derived `LagTwoBound.lagTwoThreshold`. This file does three things with that reduction: it puts the
threshold in the eigenvalue variable, it proves that variable is a relabelling rather than a second
route, and it settles what each candidate route in this tree can and cannot reach.

## 1. The threshold in the eigenvalue variable, in closed form

Through the spectral form `ρ(d) = ∑ₙ wₙ λₙᵈ` with `wₙ ≥ 0` on the vacuum complement, the ratio
criterion is a bound on the SUBDOMINANT EIGENVALUE, and the threshold there is the square root of
`lagTwoThreshold`:

    lambdaThreshold = (1 − 3^{−1/4}) / (1 + 3^{−1/4}),        lambdaThreshold² = lagTwoThreshold.

`lambdaThreshold_sq` is that identity and it is definitional — no root is extracted, because
`lagTwoThreshold` was already a square. `lambdaThreshold_gt` and `lambdaThreshold_lt` bracket it
between `0.136469` and `0.13647`.

**THE TWO-SIDED BRACKET CORRECTS A ROUNDING.** `0.13647` is an upper bound on the threshold and NOT
a usable target: `lambdaThreshold < 0.13647` is proved here, so a hypothesis `λ_max < 0.13647` does
NOT imply the criterion. The largest five-digit numeral that does is `0.136469`, and
`confines_of_subdominant_le` is stated at that value. The bracketing rationals decide nothing — the
decision is made by the closed form — but the direction of the rounding does, and it goes the wrong
way.

The bracket needed is finer than `LagTwoBound.floor_bounds` supplies, so `floor_sq_tight` and
`floor_tight` re-derive the floor's bracket one digit further, from `LagTwoBound.floor_pow_four`
and `ConfinesZero.floor_pos`. Nothing new is assumed; only the LOWER digit is new, since
`LagTwoBound.floor_bounds`' upper bound is already `0.759836`.

## 2. The eigenvalue variable is a CHANGE OF VARIABLE, and that is proved

`SpectralAt β Λ` says the two moments the criterion reads — `ρ(0)` and `ρ(2)` at extent four — are
`∑ wᵢ` and `∑ wᵢ λᵢ²` for finitely many nonnegative weights and eigenvalues bounded by `Λ`.
`lag_two_le_of_spectralAt` turns it into `ρ(2) ≤ Λ²·ρ(0)`, and `confines_of_subdominant_bound`
composes with `LagTwoBound.confines_of_lag_two_ratio`.

**AND THE CONVERSE HOLDS TOO, SO THE SPECTRAL FORM BUYS NOTHING HERE.** `spectralAt_iff` proves

    SpectralAt β Λ  ↔  0 ≤ Λ ∧ ρ(2) ≤ Λ²·ρ(0),

at every real coupling. The backward direction is one weight and one eigenvalue: `w₁ = ρ(0)` and
`λ₁ = √(ρ(2)/ρ(0))`, admissible because `PlaqVariance.corrClay_zero_pos` makes the denominator
positive and `ReflectionStrong.corrClay_nonneg_even_lag` makes the numerator nonnegative at lag two
with NO condition on the coupling. So at extent four the subdominant-eigenvalue statement and the
lag-two ratio statement are the same statement, and `confines_of_subdominant_bound` is
`LagTwoBound.confines_of_lag_two_ratio` reparametrised by `K = Λ²`.

THAT IS THE POINT AND IT IS WORTH MORE THAN A ONE-WAY BRIDGE WOULD BE. B5 at the smallest even
aperture does not need `Z = Tr(Tⁿ)`, does not need a spectral decomposition, and does not need the
weights to come from anything: the eigenvalue threshold `0.1364697…` is the square root of the ratio
threshold and the transfer-operator language is a relabelling of a single inequality. A spectral
route is therefore not blocked by the missing Fubini step in `SliceTransfer` — it is not needed at
this extent. What it would buy is the same thing the ratio route needs and neither has: the bound at
large coupling.

`SliceTransfer` still proves the kernel symmetric and positive-semidefinite
(`transferKernel_selfAdjoint_psd`) and still does not identify `Z` with a trace of its powers; that
remains true and is now known not to be on the critical path for B5 at extent four.

## 3. Where each route in this tree stops, as named `Prop`s

**The cluster expansion.** `LagTwoBound.exists_cut_lag_two_ratio` already proves the ratio bound at
ANY constant on a derived interval `[0, b]`, from `StrongCoupling.corrClay_abs_le_coreConst_mul_rate_pow`
over `ContactFloor.corrClay_zero_ge`. The answer to "is that constant volume-independent" is YES and
it is already in the tree: `coreConst` and `coreRate` take `touchDeg` and `β` and nothing else — no
`Fintype.card Pq`, no extent — which is exactly the property the Doeblin route lacks. It is also NOT
`coreConst` in disguise, because the ratio constant carries a factor `coreRate(16·4, β)` that
vanishes at `β = 0`; `LagTwoBound.contact_relative_constant_too_large` bounds a different quantity,
the CONTACT-RELATIVE constant, which has no such factor.

What the expansion does not give is a tail. `expansion_domain_bounded` proves it: the rate exceeds
one from some coupling onward and stays there, so `corrClay_abs_le_coreConst_mul_rate_pow`'s own
hypothesis `coreRate (16·4) β < 1` is false on a whole half-line. The expansion converges on a
bounded set of couplings and the crossover is not in it.

`TailRatioAtEveryCut` and `TailSubdominantAtEveryCut` name a remainder, and
`confines_of_tail_ratio` / `confines_of_tail_subdominant` prove each SUFFICIENT — the gluing is free,
because `exists_cut_lag_two_ratio` supplies a cut at every constant, so any tail bound at every cut
can be met from below. SUFFICIENT AND NOT PROVED NECESSARY: `ConfinesAtAnAperture` asks only for the
criterion pointwise in `β`, while these ask for one constant uniform on each tail, so they are
strictly the stronger request and something weaker may also close it. No converse is proved.

**The Doeblin route, refuted rather than assessed.** Strict positivity of the kernel
(`SliceTransfer.transferKernel_pos`) gives a minorisation constant `ε` and a subdominant-ratio
estimate `1 − ε`. `abs_hsRe_le` and `abs_sliceForm_le` show the cross form is confined to
`[−N·L, N·L]` with `L` the number of spatial links in the slice, so an `ε` read off that range is
`e^{−2bNL}`. That is an estimate, and an estimate can be improved. What cannot is the kernel's own
spread: `sliceForm_one` and `sliceForm_flip` evaluate the cross form at two configurations the tree
already carries, the constant identity and `HaarVariance.flipEl`, and their values differ by exactly
`4L`. So `crossFactor_ratio` gives `ε ≤ e^{−4bL}` as a property of the kernel's own cross factor and
not of any bound on it, and `doeblin_exceeds_lambdaThreshold` concludes: at every fixed coupling
`b > 0` there is a slice size beyond which `1 − ε` exceeds `lambdaThreshold`.

THE DOEBLIN THEOREM ITSELF IS NOT FORMALISED HERE, and nothing below asserts it. What is proved is
about the CONSTANT that argument consumes: `crossFactor_ratio` is an identity between two values of
the cross factor, so `ε` is at most `e^{−4bL}` however sharply the minorisation is taken, and
`doeblinFloor_exceeds` shows `1 − ε` is then already past the target. A sharper minorisation cannot
rescue the route because the limit is the kernel's spread and not the estimate's slack.

## What is NOT proved here

No eigenvalue is bounded and no ratio is bounded on any tail. `SpectralAt β Λ` is never established
for any `Λ` below `lambdaThreshold` at every coupling — and by `spectralAt_iff` that is exactly the
same debt as `TailRatioAtEveryCut`, not a second one. The crossover is untouched.
`LagTwoBound.confines_below_derived_cut` remains the strongest unconditional statement in this
direction and this file does not improve it.

What is added: the target in the eigenvalue variable with its rounding corrected, a PROOF that the
eigenvalue variable is a relabelling and not a second route, the remaining obligation as a named
`Prop` with its sufficiency proved, a proof that the cluster expansion's own hypothesis fails on a
half-line, and a proof that the Doeblin constant degenerates in the slice size.

No measured quantity appears anywhere in this file, in a statement or in a proof.

Foundational footprint only (`#print axioms` on every declaration). The module is not in the library
root's import list, so no repository-wide sweep covers it; the footprints below are this file's own
build output.
Build: `python code/lean_build.py build MassGap.SpectralBound`.
-/

namespace MassGap.SpectralBound

open MassGap MassGap.SUN MassGap.CharacterExpansion

/-! ## 1. The threshold in the eigenvalue variable -/

/-- **THE FLOOR'S SQUARE, ONE DIGIT FINER THAN `LagTwoBound.floor_sq_bounds`.**
`c² = 3^{−1/2}` with `(c²)² = 1/3` and `c² > 0`.

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

/-- **THE FLOOR ITSELF, ONE DIGIT FINER THAN `LagTwoBound.floor_bounds`.**
`3^{−1/4}` bracketed between `0.7598356` and `0.759836`, from the bracket on its square.

The finer bracket is needed on the LOWER side only: `lambdaThreshold < 0.13647` has a margin of about
`4.1·10⁻⁷` in the floor and `LagTwoBound.floor_bounds`' lower digit `0.759835` does not clear it. That
file's UPPER bound is already `0.759836` and is reproduced here unchanged, so `floor_tight` half
duplicates it.

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

/-- **THE THRESHOLD ON THE SUBDOMINANT EIGENVALUE.** `(1 − c)/(1 + c)` at `c = 3^{−1/4}`.

This is `LagTwoBound.lagTwoThreshold`'s own positive root, made a definition because the eigenvalue
is the variable B5 is naturally stated in: through `ρ(d) = ∑ₙ wₙ λₙᵈ` the criterion is
`λ_max < lambdaThreshold`, and `lambdaThreshold² = lagTwoThreshold` (`lambdaThreshold_sq`) is
definitional — no square root is taken, because `lagTwoThreshold` was already a square.

DERIVED: inherited digit for digit from `LagTwoBound.lagTwoThreshold`. `3` and `4` are the
directed-path count and the per-area normalisation of `Floor.lean`, which together are the entropy
floor `κ₀ = ¼ log 3` and hence `c = e^{−κ₀}`; the two `1`s are the `1 − c` and `1 + c` of the
log-convexity quadratic whose discriminant is identically `4`, so its positive root is this ratio.
No numeral is chosen and none is fitted. -/
noncomputable def lambdaThreshold : ℝ :=
  (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4))

#print axioms lambdaThreshold

/-- **THE SQUARE IS THE LAG-TWO THRESHOLD**, definitionally.

DERIVED: the `2` is the lag index of `ρ(2)`, which is why the eigenvalue threshold is the square root
of the ratio threshold and not some other power. -/
theorem lambdaThreshold_sq : lambdaThreshold ^ 2 = MassGap.LagTwoBound.lagTwoThreshold := rfl

#print axioms lambdaThreshold_sq

/-- Positivity, from `0 < c < 1`.

DERIVED: the `0` and the two `1`s are the sign and the `1 ± c` of the definition. -/
theorem lambdaThreshold_pos : 0 < lambdaThreshold := by
  have hc0 : 0 < (3 : ℝ) ^ (-(1 : ℝ) / 4) := MassGap.ConfinesZero.floor_pos
  have hc1 : (3 : ℝ) ^ (-(1 : ℝ) / 4) < 1 := MassGap.ConfinesZero.floor_lt_one
  unfold lambdaThreshold
  exact div_pos (by linarith) (by linarith)

#print axioms lambdaThreshold_pos

/-- **THE THRESHOLD IS ABOVE `0.136469`** — the direction a user of the bridge needs, and the
largest five-digit numeral in this position that is provably below it.

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

/-- **AND STRICTLY BELOW `0.13647`.** This is the correction the file exists to record: `0.13647` is
a rounding UP of the threshold, so `λ_max < 0.13647` does NOT give the criterion, and no statement
below is available at that value.

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

/-- **THE SPECTRAL FORM, AT ONE COUPLING, AND ONLY AS FAR AS THE CRITERION READS IT.**

`SpectralAt β Λ` says the two moments the extent-four criterion consumes are

    ρ(0) = ∑ᵢ wᵢ,        ρ(2) = ∑ᵢ wᵢ λᵢ²,        wᵢ ≥ 0,   |λᵢ| ≤ Λ

for finitely many weights and eigenvalues. This is `ρ(d) = ∑ᵢ wᵢ λᵢᵈ` read at `d = 0` and `d = 2` and
nothing more: no operator, no completeness, no identification of `Z` with a trace. `wᵢ ≥ 0` is what
positive-semidefiniteness of a transfer kernel supplies; `|λᵢ| ≤ Λ` is the mass gap itself, on the
vacuum complement, and is the content of the hypothesis.

THIS IS NOT DISCHARGED ANYWHERE. `SliceTransfer.transferKernel_selfAdjoint_psd` builds a symmetric
positive-semidefinite slice kernel and stops there; `SliceTransfer`'s header names the missing Fubini
step that `Z = Tr(Tⁿ)` needs, and a spectral decomposition is a further step beyond that.

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

/-- **THE SPECTRAL FORM GIVES THE RATIO, WITH CONSTANT `Λ²`.** Each term obeys
`wᵢ λᵢ² ≤ Λ² wᵢ` because the weight is nonnegative, and the sum of the right-hand sides is `Λ² ρ(0)`.
That is the whole argument; the `d = 0` moment is what makes it a RATIO rather than an absolute
bound.

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

/-- **THE SPECTRAL FORM IS THE RATIO BOUND, IN BOTH DIRECTIONS.** At extent four, and at every real
coupling,

    SpectralAt β Λ  ↔  0 ≤ Λ ∧ ρ(2) ≤ Λ²·ρ(0).

Forward is `lag_two_le_of_spectralAt` plus the observation that the index type cannot be empty:
`∑ wᵢ = ρ(0) > 0` by `PlaqVariance.corrClay_zero_pos`, so there is an `i`, and `0 ≤ |λᵢ| ≤ Λ`.

Backward is one weight and one eigenvalue — `w₁ = ρ(0)`, `λ₁ = √(ρ(2)/ρ(0))` — and it needs exactly
two facts the tree already has unconditionally in `β`: `corrClay_zero_pos` for the denominator and
`ReflectionStrong.corrClay_nonneg_even_lag` for the numerator, the latter at `Nap = 3`, half-extent
`m = 2` and the EVEN lag two, where the reflection-positivity argument carries no sign condition on
the coupling.

WHAT THIS MEANS FOR B5. The subdominant-eigenvalue form of the criterion at the smallest even
aperture is not stronger, not weaker and not harder than the lag-two ratio form; it is the same
inequality under `K = Λ²`. No transfer operator, no `Z = Tr(Tⁿ)` and no spectral decomposition is
needed to state or to use it, and building one would not advance B5 at this extent.

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

/-- **THE TARGET BRIDGE, IN THE EIGENVALUE VARIABLE.** A subdominant-eigenvalue bound `Λ` strictly
below `lambdaThreshold`, holding at every nonnegative coupling, gives
`ApertureRoute.ConfinesAtAnAperture` — and with it everything
`ApertureRoute.flagship_of_confinement_at_an_aperture` carries.

`0 ≤ Λ` is a sign, not a magnitude: it is what makes `Λ < lambdaThreshold` square correctly.

DERIVED: `0` is that sign; the `2` is the square that carries `Λ` to the ratio constant. -/
theorem confines_of_subdominant_bound {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : Λ < lambdaThreshold)
    (h : LagSpectralBound Λ) : ApertureRoute.ConfinesAtAnAperture := by
  refine MassGap.LagTwoBound.confines_of_lag_two_ratio (Λ ^ 2) ?_
    (fun β hβ => lag_two_le_of_spectralAt (h β hβ))
  rw [← lambdaThreshold_sq]
  nlinarith [hΛ, hΛ0, lambdaThreshold_pos]

#print axioms confines_of_subdominant_bound

/-- **THE SAME AT A NUMERAL.** `λ_max ≤ 0.136469` on the vacuum complement, at every nonnegative
coupling, closes B5 at the smallest even aperture.

`0.136469` is NOT the bound's own content — `confines_of_subdominant_bound` at the closed form is —
it is the largest five-digit numeral provably below `lambdaThreshold`. `0.13647` is NOT available:
`lambdaThreshold_lt` puts the threshold strictly below it.

DERIVED: `0.136469` reports `lambdaThreshold` from below (`lambdaThreshold_gt`) and decides nothing;
`0` is a sign. -/
theorem confines_of_subdominant_le {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ 0.136469)
    (h : LagSpectralBound Λ) : ApertureRoute.ConfinesAtAnAperture :=
  confines_of_subdominant_bound hΛ0 (lt_of_le_of_lt hΛ lambdaThreshold_gt) h

#print axioms confines_of_subdominant_le

/-! ## 3. What remains, as named `Prop`s, and why the expansion cannot supply it -/

/-- **WHAT IS MISSING FROM THE RATIO ROUTE: A TAIL BOUND ABOVE EVERY CUT.**

`LagTwoBound.exists_cut_lag_two_ratio` proves the ratio bound at ANY constant on a derived `[0, b]`,
with `b` depending on the constant. So the only thing between this tree and B5 at extent four is a
bound of the same shape on `[b, ∞)`, at every cut — and "at every cut" is what makes the gluing free,
since the cut the expansion supplies is not under the caller's control.

This is the crossover, stated as a proposition rather than as prose. No expansion in this tree
converges through it (`expansion_domain_bounded`). No measured quantity enters this file.

DERIVED: `2` and `0` are the two lag indices; `3` is the extent-four index `N + 1 = 4`; `0 < b` is a
sign. `lagTwoThreshold` is `LagTwoBound`'s derived number. -/
def TailRatioAtEveryCut : Prop :=
  ∀ b : ℝ, 0 < b → ∃ K : ℝ, K < MassGap.LagTwoBound.lagTwoThreshold ∧
    ∀ β : ℝ, b ≤ β → MassGap.wilsonCorrAt 3 β 2 ≤ K * MassGap.wilsonCorrAt 3 β 0

#print axioms TailRatioAtEveryCut

/-- **THE TAIL IS SUFFICIENT, AND THE GLUING IS FREE.**

Below the cut, `LagTwoBound.exists_cut_lag_two_ratio` at half the threshold; above it, the hypothesis
at that same cut; the two constants are joined by `max`, which stays under the threshold because both
do. `PlaqVariance.corrClay_zero_pos` is what lets a smaller constant be weakened to a larger one —
the denominator is strictly positive at every real coupling and every extent.

No converse is proved. Nothing here says the tail must be closed this way, only that closing it this
way closes B5 at the smallest even aperture.

DERIVED: the `2` is the device for strictness that `LagTwoBound.confines_below_derived_cut` also uses
— any constant strictly inside the threshold serves — and the `0` and `2` are lag indices. -/
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

/-- The same in the eigenvalue variable: a subdominant bound strictly below `lambdaThreshold` above
every cut.

DERIVED: `0` is a sign; `lambdaThreshold` is the derived closed form of section 1. -/
def TailSubdominantAtEveryCut : Prop :=
  ∀ b : ℝ, 0 < b → ∃ Λ : ℝ, 0 ≤ Λ ∧ Λ < lambdaThreshold ∧ ∀ β : ℝ, b ≤ β → SpectralAt β Λ

#print axioms TailSubdominantAtEveryCut

/-- **AND IT TOO IS SUFFICIENT**, by squaring the eigenvalue bound into a ratio bound at each cut.

DERIVED: the `2` is the lag index and the square it forces. -/
theorem confines_of_tail_subdominant (h : TailSubdominantAtEveryCut) :
    ApertureRoute.ConfinesAtAnAperture := by
  refine confines_of_tail_ratio (fun b hb => ?_)
  obtain ⟨Λ, hΛ0, hΛ, hsp⟩ := h b hb
  refine ⟨Λ ^ 2, ?_, fun β hβ => lag_two_le_of_spectralAt (hsp β hβ)⟩
  rw [← lambdaThreshold_sq]
  nlinarith [hΛ, hΛ0, lambdaThreshold_pos]

#print axioms confines_of_tail_subdominant

/-- **THE EXPANSION'S OWN CONVERGENCE CONDITION FAILS ON A HALF-LINE.**

`StrongCoupling.corrClay_abs_le_coreConst_mul_rate_pow` carries the hypothesis
`coreRate (16·4) β < 1`. `StrongArm.coreRate_exceeds` says the rate is unbounded above in the
coupling and `StrongArm.coreRate_mono_beta` says it is monotone there, so once it passes one it never
returns: there is a `B` beyond which the hypothesis is FALSE at every coupling.

Hence no instance of that estimate can contribute to `TailRatioAtEveryCut` at any cut above `B`, and
the cluster expansion — the one bound in this tree whose constant does not count links — cannot reach
the crossover. That is a statement about this estimate, not about the correlation: nothing here says
`ρ(2)/ρ(0)` is large at strong coupling.

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

/-- **THE CROSS FORM IS CONFINED TO `[−N, N]` ON ONE LINK.** `CrossingIntegration.hsRe_coe_eq`
presents `hsRe V W` as the real trace of `V W⁻¹`, an element of `SU(N)` like any other, and
`WilsonAction.abs_re_trace_le` bounds that by the rank.

DERIVED: `N` is the rank, from `abs_re_trace_le`; no numeral is chosen. -/
theorem abs_hsRe_le (V W : SU N) :
    |hsRe (V : Matrix (Fin N) (Fin N) ℂ) (W : Matrix (Fin N) (Fin N) ℂ)| ≤ (N : ℝ) := by
  rw [MassGap.CrossingIntegration.hsRe_coe_eq]
  exact MassGap.WilsonAction.abs_re_trace_le _

#print axioms abs_hsRe_le

/-- **AND THE SLICE FORM TO `[−N·L, N·L]`, WITH `L` THE NUMBER OF LINKS IN THE SLICE.**

The bound COUNTS LINKS, and that is the obstruction the Doeblin route runs into, made explicit: it is
uniform in nothing that grows with the lattice. This is a bound and could in principle be slack;
`sliceForm_one` and `sliceForm_flip` below settle that it is not, by evaluating the cross form.

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

/-- **THE UPPER END IS ATTAINED, AT THE CONSTANT IDENTITY.** `hsRe 1 1 = Re tr 1 = N`, so the slice
form there is exactly `N·L`. The bound of `abs_sliceForm_le` is therefore not slack at the top, and
no sharper estimate can shrink the spread from this side.

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

/-- **AND A CONFIGURATION `4L` BELOW IT**, from a witness the tree already carries.
`HaarVariance.flipEl m` is `diag(−1, −1, 1, …, 1)` in `SU(m+2)`; it is its own conjugate transpose
(`flipMat_star`), so `hsRe 1 (flipEl m) = Re tr (flipEl m) = m − 2`, which is `N − 4` at
`N = m + 2`.

The two evaluations together are the point of this section: the spread of the cross form over slice
configurations is at least `4L` as a PROPERTY OF THE KERNEL, not as a property of an estimate on it.

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

/-- **THE KERNEL'S NON-PRODUCT FACTOR.** `SliceTransfer.transferKernel` is
`e^{−s(V)/2} · crossFactor · e^{−s(W)/2}` (`transferKernel_eq_crossFactor`), and the two outer factors
depend on one argument each. This definition isolates the part that depends on BOTH, which is where
the coupling between slices is; that the outer factors cancel out of the ratio a minorisation forms
is the reason for isolating it and is NOT proved here.

DERIVED: `b` is the caller's coupling; no numeral. -/
noncomputable def crossFactor (b : ℝ) (V W : ι → SU N) : ℝ :=
  Real.exp (b * MassGap.SliceTransfer.sliceForm V W)

#print axioms crossFactor

/-- The factorisation, definitionally.

DERIVED: the `2` is `transferKernel`'s own even split of the intra-slice action between its two
arguments, which is what makes the kernel symmetric. -/
theorem transferKernel_eq_crossFactor (b : ℝ) (s : (ι → SU N) → ℝ) (V W : ι → SU N) :
    MassGap.SliceTransfer.transferKernel b s V W
      = Real.exp (-(s V) / 2) * crossFactor b V W * Real.exp (-(s W) / 2) := rfl

#print axioms transferKernel_eq_crossFactor

/-- **THE MINORISATION CONSTANT IS AT MOST `e^{−4bL}`.** Exactly, not as an estimate: the two
configurations of `sliceForm_one` and `sliceForm_flip` give

    crossFactor b 1 flip  =  e^{−4bL} · crossFactor b 1 1,

so at every NONNEGATIVE coupling and every rank `m + 2` the ratio of the cross factor's smallest
value to its largest is at most `e^{−4bL}` — the sign of `b` is what makes the identity readable as a
min-over-max. A sharper minorisation cannot help: this is the cross factor itself, not a bound on it.
What is proved is the displayed identity; the min-over-max reading is its use.

DERIVED: `4` is `(m + 2) − (m − 2)`, the difference of the two evaluated cross forms — the two `−1`
entries of `flipEl` counted twice, once in each trace — and `Fintype.card ι` is the link count. -/
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

/-- **THE SUBDOMINANT-RATIO ESTIMATE A MINORISATION OF CONSTANT `e^{−4bL}` DELIVERS.**

THE FORM OF THE DOEBLIN ARGUMENT IS EXTERNAL AND IS NOT PROVED IN THIS TREE: from
`T(V, W) ≥ ε · (reference)` for every pair it bounds the subdominant ratio by `1 − ε`. This
definition ASSERTS NOTHING ABOUT THAT. It names the number that argument would deliver at the best
`ε` this kernel admits — `crossFactor_ratio` puts `ε ≤ e^{−4bL}` — so `doeblinFloor b L` is a FLOOR
on whatever that route could report, which is the useless direction, and
`doeblin_exceeds_lambdaThreshold` shows the floor is already above the target.

Everything proved about `doeblinFloor` below is elementary real analysis about `1 − e^{−4bL}`. Its
bearing on the Doeblin route rests on the external statement above, and on nothing proved here.

DERIVED: `4` is `crossFactor_ratio`'s, the gap between the two evaluated cross forms; `1` is the
Dobrushin coefficient's own normalisation; `L` is the slice's link count and `b` the coupling. -/
noncomputable def doeblinFloor (b : ℝ) (L : ℕ) : ℝ := 1 - Real.exp (-(4 * b * (L : ℝ)))

#print axioms doeblinFloor

/-- **THE ESTIMATE PASSES ANY TARGET BELOW ONE, ONCE THE SLICE IS BIG ENOUGH.**

`e^x ≥ 1 + x` is the only analytic input; the threshold `L₀` is whatever `exists_nat_gt` supplies at
`1/(4b(1 − Λ))` and no numeral is named for it.

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

/-- **THE DOEBLIN ROUTE CANNOT REACH B5'S TARGET, AND THE FAILURE IS IN THE VOLUME.**

At every fixed coupling `b > 0` there is a slice size `L₀` beyond which the best subdominant-ratio
estimate a minorisation of this kernel can deliver already exceeds `lambdaThreshold`. A slice's
spatial-link count grows with the lattice, so every large enough lattice is past `L₀` at every
coupling — THAT the count grows is not proved here, since `L` enters these statements as
`Fintype.card ι` for an arbitrary finite index and `SliceTransfer.sliceLinks`' cardinality is not
computed anywhere in the tree.

This refutes the route rather than assessing it. `crossFactor_ratio` is an identity between two
values of the cross factor, so no sharper minorisation constant exists to be found: the ratio really
is at most `e^{−4bL}`.

WHAT IS NOT CLAIMED: nothing here bounds the true subdominant eigenvalue from below, and nothing here
says the slice kernel has no gap. What is refuted is one method of bounding it.

DERIVED: `0 < b` is a sign; `lambdaThreshold` is section 1's closed form; `1` is
`lambdaThreshold_lt` composed with `0.13647 < 1`. -/
theorem doeblin_exceeds_lambdaThreshold {b : ℝ} (hb : 0 < b) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → lambdaThreshold < doeblinFloor b L :=
  doeblinFloor_exceeds hb (by linarith [lambdaThreshold_lt])

#print axioms doeblin_exceeds_lambdaThreshold

end MassGap.SpectralBound
