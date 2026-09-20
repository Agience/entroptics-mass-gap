import MassGap.Spectral
import MassGap.LagTwoBound

/-!
# From a periodic spectral form to confinement at an aperture

`LagTwoBound.confines_of_lag_two_ratio` consumes `∀ β ≥ 0, ρ(2) ≤ K·ρ(0)` with ONE `K` strictly
below `lagTwoThreshold`, uniform in the coupling. `Spectral.PeriodicSpectralForm` is the shape a
transfer operator supplies. This file joins them, and the join is `K := 2r²`.

## The shape of the consumable statement, which is what fixes `K`

`hrep` reads `ρ d = ∑ k, w k * (λₖ^d + λₖ^(n − d))`. At `n = 4`:

    ρ 0 = ∑ w k * (1 + λₖ⁴)        exponents 0 and 4
    ρ 2 = ∑ w k * (λₖ² + λₖ²)      exponents 2 and 2 — the self-paired lag

so a rate `r` on the weighted modes gives `ρ(2) ≤ 2r²·(∑ w) ≤ 2r²·ρ(0)`, and the constant handed to
`confines_of_lag_two_ratio` is `2r²`. It is `2r²` and not `r²`: `SpectralFour`'s `FourRepresentable`
cone is built on the same curve `λ ↦ (1 + λ⁴, λ + λ³, 2λ²)` and its `DERIVED` note gives the reason
in the same words — the `2` is the number of terms in `λ^d + λ^{n−d}` at the self-paired lag, the
shape's own multiplicity. This file does not discover that; it composes it into the ratio.

DERIVED: the `2` in `2 * r ^ 2` is that multiplicity. No decimal appears anywhere in this file; the
threshold enters only as `LagTwoBound.lagTwoThreshold`, whose closed form is `((1−c)/(1+c))²` at
`c = 3^(−1/4)`. For the record, since a rounded numeral has already cost this tree once: the root of
`2r² = lagTwoThreshold` is `0.096498676…`, so `0.0965` and `0.0965029` are that ROUNDED UP and both
put `2r²` ABOVE the threshold; the largest safe six-digit numeral is `0.096498`. It is not used
here — `two_mul_sq_lt_lagTwoThreshold_iff` restates the condition without one.

## What this does not do

It does not produce `r` and it does not produce the form. `TailRatio.no_lag_two_bound_from_triple`
proves the shape facts give no bound on `ρ(2)/ρ(0)` at all, so `r` comes from the dynamics, and
`Spectral2` shows a form on its own carries no gap.

Foundational footprint only (`#print axioms` on every declaration).
Build: `python research/code/lean_build.py build MassGap.PeriodicLagTwo`.
-/

namespace MassGap.PeriodicLagTwo

open Finset

variable {ρ : Fin 4 → ℝ}

/-- **The total weight is a lower bound for the contact value.** `ρ 0 = ∑ w (1 + λ⁴)` and `λ⁴ ≥ 0`.
Uses `hw` and `hlam0` only — `hlam1` is never needed. -/
theorem sum_w_le_contact (S : Spectral.PeriodicSpectralForm 4 ρ) :
    ∑ k, S.w k ≤ ρ 0 := by
  rw [S.hrep 0]
  refine Finset.sum_le_sum fun k _ => ?_
  have hw : 0 ≤ S.w k := S.hw k
  have h4 : 0 ≤ (S.lam k) ^ ((4 : ℕ) - ((0 : Fin 4) : ℕ)) := pow_nonneg (S.hlam0 k) _
  have h0 : (S.lam k) ^ (((0 : Fin 4) : ℕ)) = 1 := by norm_num
  nlinarith [hw, h4]

#print axioms sum_w_le_contact

/-- **The half-lag value is at most `2r²` times the total weight.**

This is `Spectral.periodic_decay_le` read at `d = 2`, not a second proof of it: that lemma already
gives `ρ d ≤ 2·(∑ w)·r^d` on the near half, and `2 * (2 : Fin 4) ≤ 4` by `decide`. -/
theorem half_lag_le (S : Spectral.PeriodicSpectralForm 4 ρ) {r : ℝ} (hr : 0 ≤ r)
    (hgap : ∀ k, S.w k ≠ 0 → S.lam k ≤ r) :
    ρ 2 ≤ 2 * r ^ 2 * ∑ k, S.w k := by
  have h := Spectral.periodic_decay_le S hgap hr (2 : Fin 4) (by decide)
  have he : (((2 : Fin 4) : ℕ)) = 2 := rfl
  rw [he] at h
  linarith [h]

#print axioms half_lag_le

/-- **THE CONSUMABLE STATEMENT: a rate on the weighted modes bounds the lag-two ratio by `2r²`.**

This is the shape `LagTwoBound.confines_of_lag_two_ratio` takes — non-strict, with the constant out
front so it can be quantified over the coupling. It needs no positivity of `ρ 0`. -/
theorem lag_two_ratio_of_periodic_rate (S : Spectral.PeriodicSpectralForm 4 ρ) {r : ℝ} (hr : 0 ≤ r)
    (hgap : ∀ k, S.w k ≠ 0 → S.lam k ≤ r) :
    ρ 2 ≤ 2 * r ^ 2 * ρ 0 := by
  have h2 : ρ 2 ≤ 2 * r ^ 2 * ∑ k, S.w k := half_lag_le S hr hgap
  have hw : ∑ k, S.w k ≤ ρ 0 := sum_w_le_contact S
  have hnn : 0 ≤ 2 * r ^ 2 := by positivity
  calc ρ 2 ≤ 2 * r ^ 2 * ∑ k, S.w k := h2
    _ ≤ 2 * r ^ 2 * ρ 0 := mul_le_mul_of_nonneg_left hw hnn

#print axioms lag_two_ratio_of_periodic_rate

/-- **THE PAYOFF: a periodic form with a small enough rate at every nonnegative coupling gives
confinement at an aperture.**

`confines_of_lag_two_ratio` at `K := 2r²`, whose `hK` is exactly `hrate`. The form is asked for at
each `β` separately and the rate is the one thing held uniform, which is the weakest shape that
theorem's `K` permits. -/
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

/-- **The rate condition, stated without a decimal.** Generic arithmetic: `2x < c ↔ x < c/2`. It
records the restatement and says nothing about the threshold's value. -/
theorem two_mul_sq_lt_lagTwoThreshold_iff {r : ℝ} :
    2 * r ^ 2 < MassGap.LagTwoBound.lagTwoThreshold
      ↔ r ^ 2 < MassGap.LagTwoBound.lagTwoThreshold / 2 := by
  constructor <;> intro h <;> linarith

#print axioms two_mul_sq_lt_lagTwoThreshold_iff

end MassGap.PeriodicLagTwo
