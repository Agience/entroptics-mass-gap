import MassGap.Spectral
import MassGap.LagTwoBound

/-!
# MassGap.PeriodicLagTwo — a periodic spectral form at extent four gives `ConfinesAtAnAperture`

`LagTwoBound.confines_of_lag_two_ratio` takes a constant `K < LagTwoBound.lagTwoThreshold` together
with `∀ β ≥ 0, wilsonCorrAt 3 β 2 ≤ K * wilsonCorrAt 3 β 0`, and returns
`ApertureRoute.ConfinesAtAnAperture`. `Spectral.PeriodicSpectralForm 4 ρ` is the shape a transfer
operator on a circle of extent four supplies: nonnegative weights `w`, decay factors `lam` in
`[0, 1]`, and `hrep : ρ d = ∑ k, w k * (lam k ^ d + lam k ^ (4 − d))`. This module converts a
uniform rate bound on such a form into that hypothesis, with `K := 2 * r ^ 2`.

## How the constant arises

At `n = 4`, `hrep` reads

    ρ 0 = ∑ w k * (lam k ^ 0 + lam k ^ 4) = ∑ w k * (1 + lam k ^ 4)
    ρ 2 = ∑ w k * (lam k ^ 2 + lam k ^ 2)

Dropping `lam k ^ 4 ≥ 0` from the first gives `∑ w k ≤ ρ 0` (`sum_w_le_contact`). The second is the
self-paired lag, where both exponents are `2`, so a bound `lam k ≤ r` at every mode of nonzero weight
gives `ρ 2 ≤ 2 * r ^ 2 * ∑ w k` (`half_lag_le`, an instance of `Spectral.periodic_decay_le` at
`d = 2`). Composing the two gives `ρ 2 ≤ 2 * r ^ 2 * ρ 0`. The coefficient `2` is the number of terms
in `lam k ^ d + lam k ^ (n − d)`, not a bound on their size; `SpectralFour`'s `FourRepresentable`
cone records the same multiplicity on the curve `λ ↦ (1 + λ⁴, λ + λ³, 2λ²)`.

## Scope

`r` and the form are hypotheses at every declaration here; neither is constructed. The extent is
fixed at `4` throughout, so `ρ : Fin 4 → ℝ` and the aperture argument to `wilsonCorrAt` is `3`. The
threshold enters only by name — its closed form is `((1 − c)/(1 + c))²` at `c = 3 ^ (−1/4)`, proved
elsewhere — and no decimal literal appears in any statement in this file, since
`two_mul_sq_lt_lagTwoThreshold_iff` restates the rate condition without one.

DERIVED: `4` is the periodic extent; `3` is the aperture, for which `wilsonCorrAt 3 β` has lag type
`Fin (3 + 1)`; `2` as a lag index is the self-paired lag at extent four, `2` as a coefficient is the
term count in `lam ^ d + lam ^ (n − d)`, and `2` as an exponent is that lag; `0` is the contact lag
and the sign condition on `r`, on the weights and on the coupling; `1` is the upper bound the form
puts on `lam`. Every declaration is checked with `#print axioms`.

Build: `python research/code/lean_build.py build MassGap.PeriodicLagTwo`.
-/

namespace MassGap.PeriodicLagTwo

open Finset

variable {ρ : Fin 4 → ℝ}

/-- The total weight is at most the contact value: `∑ k, S.w k ≤ ρ 0` for any
`Spectral.PeriodicSpectralForm 4 ρ`. Rewriting with `S.hrep 0` turns `ρ 0` into
`∑ k, S.w k * (1 + S.lam k ^ 4)`, and the summand-wise inequality follows from `S.hw` and `S.hlam0`.
The upper bound `S.hlam1` is not used.

DERIVED: `4` is the extent the form is stated at; `0` is the contact lag, whose exponent pair is
`(0, 4)`. -/
theorem sum_w_le_contact (S : Spectral.PeriodicSpectralForm 4 ρ) :
    ∑ k, S.w k ≤ ρ 0 := by
  rw [S.hrep 0]
  refine Finset.sum_le_sum fun k _ => ?_
  have hw : 0 ≤ S.w k := S.hw k
  have h4 : 0 ≤ (S.lam k) ^ ((4 : ℕ) - ((0 : Fin 4) : ℕ)) := pow_nonneg (S.hlam0 k) _
  have h0 : (S.lam k) ^ (((0 : Fin 4) : ℕ)) = 1 := by norm_num
  nlinarith [hw, h4]

#print axioms sum_w_le_contact

/-- The half-lag value is bounded by `2 * r ^ 2` times the total weight. From `0 ≤ r` and a rate
bound `S.lam k ≤ r` at every mode with `S.w k ≠ 0`, the conclusion is
`ρ 2 ≤ 2 * r ^ 2 * ∑ k, S.w k`. It is `Spectral.periodic_decay_le` instantiated at `d = 2`, whose
side condition `2 * (2 : ℕ) ≤ 4` holds by `decide`.

The rate bound is imposed only at modes of nonzero weight; modes with `S.w k = 0` are unconstrained.

DERIVED: `4` is the extent; `2` as the lag argument of `ρ` and as the exponent of `r` is the
self-paired lag at extent four; the leading `2` is the number of terms in
`lam ^ d + lam ^ (n − d)`; `0` is the sign condition on `r` and the weight value the rate bound
excludes. -/
theorem half_lag_le (S : Spectral.PeriodicSpectralForm 4 ρ) {r : ℝ} (hr : 0 ≤ r)
    (hgap : ∀ k, S.w k ≠ 0 → S.lam k ≤ r) :
    ρ 2 ≤ 2 * r ^ 2 * ∑ k, S.w k := by
  have h := Spectral.periodic_decay_le S hgap hr (2 : Fin 4) (by decide)
  have he : (((2 : Fin 4) : ℕ)) = 2 := rfl
  rw [he] at h
  linarith [h]

#print axioms half_lag_le

/-- A rate on the weighted modes bounds the lag-two ratio: from `0 ≤ r` and `S.lam k ≤ r` at every
mode with `S.w k ≠ 0`, the conclusion is `ρ 2 ≤ 2 * r ^ 2 * ρ 0`. It chains `half_lag_le` with
`sum_w_le_contact`, the second step using `0 ≤ 2 * r ^ 2`.

The bound is non-strict and carries the constant as a factor rather than as a quotient, which is the
shape `LagTwoBound.confines_of_lag_two_ratio` consumes. No positivity of `ρ 0` is assumed.

DERIVED: `4` is the extent; `2` as the lag argument of `ρ` and as the exponent of `r` is the
self-paired lag, and the leading `2` is the term count in `lam ^ d + lam ^ (n − d)`; `0` is the
contact lag, the sign condition on `r`, and the weight value the rate bound excludes. -/
theorem lag_two_ratio_of_periodic_rate (S : Spectral.PeriodicSpectralForm 4 ρ) {r : ℝ} (hr : 0 ≤ r)
    (hgap : ∀ k, S.w k ≠ 0 → S.lam k ≤ r) :
    ρ 2 ≤ 2 * r ^ 2 * ρ 0 := by
  have h2 : ρ 2 ≤ 2 * r ^ 2 * ∑ k, S.w k := half_lag_le S hr hgap
  have hw : ∑ k, S.w k ≤ ρ 0 := sum_w_le_contact S
  have hnn : 0 ≤ 2 * r ^ 2 := by positivity
  calc ρ 2 ≤ 2 * r ^ 2 * ∑ k, S.w k := h2
    _ ≤ 2 * r ^ 2 * ρ 0 := mul_le_mul_of_nonneg_left hw hnn

#print axioms lag_two_ratio_of_periodic_rate

/-- A periodic form at extent four with a uniform rate below the threshold gives
`ApertureRoute.ConfinesAtAnAperture`. The hypotheses are `0 ≤ r`, the strict bound
`2 * r ^ 2 < LagTwoBound.lagTwoThreshold`, and `hform`: for every `β ≥ 0` there exists a
`Spectral.PeriodicSpectralForm 4 (MassGap.wilsonCorrAt 3 β)` whose modes of nonzero weight all
satisfy `S.lam k ≤ r`. It is `LagTwoBound.confines_of_lag_two_ratio` at `K := 2 * r ^ 2`, with
`hrate` discharging `hK` and `lag_two_ratio_of_periodic_rate` discharging the ratio hypothesis at
each `β`.

The form may differ at each `β`; only `r` is held uniform in the coupling, and only nonnegative
couplings are quantified over. The aperture is `3`, so the correlation is `wilsonCorrAt 3 β` with
lag type `Fin (3 + 1)`.

DERIVED: `0` is the lower end of the coupling range, the sign condition on `r`, and the weight value
the rate bound excludes; `2` as a coefficient is the term count in `lam ^ d + lam ^ (n − d)` and `2`
as an exponent is the self-paired lag; `4` is the periodic extent; `3` is the aperture. -/
theorem confines_of_periodic_rate {r : ℝ} (hr : 0 ≤ r)
    (hrate : 2 * r ^ 2 < MassGap.LagTwoBound.lagTwoThreshold)
    (hform : ∀ β : ℝ, 0 ≤ β →
      ∃ S : Spectral.PeriodicSpectralForm 4 (MassGap.wilsonCorrAt 3 β),
        ∀ k, S.w k ≠ 0 → S.lam k ≤ r) :
    ApertureRoute.ConfinesAtAnAperture :=
  MassGap.LagTwoBound.confines_of_lag_two_ratio (2 * r ^ 2) hrate
    (fun β hβ => by
      obtain ⟨S, hgap⟩ := hform β hβ
      exact lag_two_ratio_of_periodic_rate S hr hgap)

#print axioms confines_of_periodic_rate

/-- The rate condition restated as a bound on `r ^ 2` alone:
`2 * r ^ 2 < lagTwoThreshold ↔ r ^ 2 < lagTwoThreshold / 2`. Proved by `linarith` in both
directions; it uses no property of `lagTwoThreshold`, asserts nothing about its value, and names no
decimal.

DERIVED: the `2` multiplying `r ^ 2` is the term count that produced the coefficient in
`lag_two_ratio_of_periodic_rate`, and the `2` dividing `lagTwoThreshold` is the same one moved
across; the `2` in each `r ^ 2` is the self-paired lag. -/
theorem two_mul_sq_lt_lagTwoThreshold_iff {r : ℝ} :
    2 * r ^ 2 < MassGap.LagTwoBound.lagTwoThreshold
      ↔ r ^ 2 < MassGap.LagTwoBound.lagTwoThreshold / 2 := by
  constructor <;> intro h <;> linarith

#print axioms two_mul_sq_lt_lagTwoThreshold_iff

end MassGap.PeriodicLagTwo
