import Mathlib
import MassGap.TwoDVanish
import MassGap.StripLift
import MassGap.StripOsc

/-!
# MassGap.StripClose — the axis anchor without a cited input, and `Z(t)/Z(0)` as a plane average

Two compositions of proved statements. Declarations are in `MassGap.StripClose`.

## The axis and the vertical segment

`MixPlane.axis_mem_vanishSet` and `MixPlane.segment_first_stall` read the cited `LayerSplit.TwoDCharacter N β` only
for `DA N β 0 · → 0`, which `TwoDVanish.decoupled_vanishes` proves at every `β ≥ 0`. The forms here read `N ≠ 0`
instead.

* `axis_mem_vanishSet`, `axis_subset`, `axis_nhds`: `(β, 0) ∈ MixPlane.VanishSet N` at every `β ≥ 0`; the whole
  axis lies in the vanishing set; each axis point has a quadrant neighbourhood in it.
* `segment_first_stall`: if the segment `{β} × [0, β]` meets `MixPlane.StallSet N`, there is a least `t* ∈ (0, β]`
  with `(β, t*)` stalled and `(β, t)` vanishing for `t ∈ [0, t*)`.
* `segment_gap_of_noStall`: if the segment misses the stall set, one window `w ≥ 1` gives
  `StripLift.TransferGapAt` at rate `log 2 / 2^w` at every `t ∈ [0, β]`.
* `gap_below_first_stall`: otherwise, with `t*` as above, every `t' < t*` has a window `w(t') ≥ 1` giving the
  transfer gap at rate `log 2 / 2^{w(t')}` at every `t ∈ [0, t']`, for every side `2^v`, `v ≥ w(t')`.
* `segment_gap_dichotomy`: at every `β ≥ 0` one of the two holds.

## The ratio of partition functions

With `E_plane[F] = ∫ e^{−β S_in} F dU / ∫ e^{−β S_in} dU` (`planeE`), the in-plane Gibbs average on the side-`n` torus:

* `YR_pos`: `Y(U) > 0` at every `t` and `U` (each factor `1 + c_t` is `e^{…}/H(−2t)`), so `StripGas.YR` needs no
  width for its positivity.
* `exp_sum_yS`: `exp(Σ_x yS(U, x)) = Y(U)`, from `StripOsc.log_YR_eq_sum_sym`, at every `t`.
* `ZA_ratio`: `Z(β, t, n)/Z(β, 0, n) = e^{−8 t n⁴ ⟨φ⟩} H(−2t)^{4 n⁴} · E_plane[exp(Σ_x yS(U, x))]`, at every `β`,
  `t`, `n` and `N ≠ 0`.
* `logZA_sub`: `log Z(β, t, n) − log Z(β, 0, n) = n⁴ ℓ(t) + log E_plane[exp(Σ_x yS(U, x))]`, with
  `ℓ = CumulantStrip.ell`.
* `exp_sum_yR`, `planeE_yR`: for `|t| ≤ t₁` the enumeration summand `yR` of `StripGas.log_YR_eq_sum` gives the same
  plane average.

The composition carries the bulk factor `e^{n⁴ ℓ(t)}`: the plane average of `exp(Σ yS)` is the ratio divided by it,
not the ratio itself. None of `n ≥ 3`, `n` even, or a bound on `|t|` is read: they enter only the bounds on `yS`
(`StripOsc.abs_yS_le`), not the identity.

DERIVED (module-wide): `0` the decoupled end, the lower ends and the sign; `1` the least window and the unit of the
product; `8 = 2 · 4`, `4` the normal orientations and `2` the orientations of a plaquette, as in
`CumulantStrip.ZA_eq_gas`. Inherited: `t₁ = e^{−88}/16` of `StripGas.tOne`, read only in `exp_sum_yR`, `planeE_yR`; `t₂ = e^{−128}/16` of `StripOsc.tTwo`.

## What does not follow

* `gap_below_first_stall` gives a rate on each closed `[0, t']`, `t' < t*`. No single rate on `[0, t*)` is proved:
  the window `w(t')` may grow without bound as `t' → t*`, and at `t*` the seed fails at every window.
* Nothing here decides whether the stall set meets the segment. `MixPlane.NoStallOnSegment N β` stays open.
* `ZA_ratio` is an identity. It bounds nothing: the second layer `log E_plane[exp(Σ_x yS)]` is not estimated here, and
  `StripOsc.abs_yS_le` controls `yS` only for `0 < |t| ≤ t₂ = e^{−128}/16`.
* The plane average is at finite `n`; no limit in `n` is taken.
* No strip bound follows: the plane average is not controlled, and `t = β` is reached only if the segment misses the
  stall set.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.StripClose

open Finset MeasureTheory Filter Topology Set
open MassGap.MixPlane (VanishSet StallSet Quad NoStallOnSegment)

variable {N : ℕ}

/-! ## 1. The axis anchor and the vertical segment -/

/-- **The axis anchor, with no cited input**: `(β, 0) ∈ VanishSet N` at every `β ≥ 0`, through
`TwoDVanish.decoupled_vanishes`. DERIVED: `0` the decoupled end. -/
theorem axis_mem_vanishSet (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) : (β, (0 : ℝ)) ∈ VanishSet N :=
  ⟨hβ, le_rfl, TwoDVanish.decoupled_vanishes hN hβ⟩

/-- **The axis lies in the vanishing set.** DERIVED: `0` the decoupled end. -/
theorem axis_subset (hN : N ≠ 0) : {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.2 = 0} ⊆ VanishSet N := by
  rintro ⟨β, t⟩ ⟨hβ, rfl⟩
  exact axis_mem_vanishSet hN hβ

/-- **A quadrant neighbourhood of each axis point.** DERIVED: `0` the decoupled end. -/
theorem axis_nhds (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    ∀ᶠ q in 𝓝 (β, (0 : ℝ)), q ∈ Quad → q ∈ VanishSet N :=
  MixPlane.eventually_mem_vanishSet hN (axis_mem_vanishSet hN hβ)

/-- **First stall on the segment, with no cited input**: if the segment above `β ≥ 0` meets the stall set, there
is a least `t* ∈ (0, β]` with `(β, t*)` stalled and `(β, t)` vanishing for `t ∈ [0, t*)`. DERIVED: `0` the axis. -/
theorem segment_first_stall (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (h : ¬ NoStallOnSegment N β) :
    ∃ ts : ℝ, 0 < ts ∧ ts ≤ β ∧ (β, ts) ∈ StallSet N ∧
      ∀ t : ℝ, 0 ≤ t → t < ts → (β, t) ∈ VanishSet N := by
  have h' : ∃ t : ℝ, 0 ≤ t ∧ t ≤ β ∧ (β, t) ∈ StallSet N := by
    by_contra hn
    exact h fun t h0 h1 hs => hn ⟨t, h0, h1, hs⟩
  exact MixPlane.first_stall_of_path (γ := fun t => (β, t)) hN (continuous_const.prodMk continuous_id)
    (fun t ht _ => ⟨hβ, ht⟩) (axis_mem_vanishSet hN hβ) h'

/-- **No stall gives one rate on the whole segment**: if `{β} × [0, β]` misses the stall set, one window `w ≥ 1`
gives `TransferGapAt` at rate `log 2 / 2^w` at every `t ∈ [0, β]`. DERIVED: `0` the axis; `1` the least window. -/
theorem segment_gap_of_noStall (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (h : NoStallOnSegment N β) :
    ∃ w : ℕ, 1 ≤ w ∧ ∀ (t : ℝ) (ht : 0 ≤ t), t ≤ β →
      StripLift.TransferGapAt hN hβ ht (StripLift.seedMass w) w := by
  refine StripLift.segment_gap hN hβ fun s h0 h1 => ?_
  by_contra hv
  exact h s h0 h1 ⟨⟨hβ, h0⟩, hv⟩

/-- **The gap below the first stall**: if the segment above `β ≥ 0` meets the stall set, with `t*` the first stall,
every `t' < t*` has a window `w ≥ 1` giving `TransferGapAt` at rate `log 2 / 2^w` at every `t ∈ [0, t']`, for every
side `2^v`, `v ≥ w`. The window depends on `t'`. DERIVED: `0` the axis; `1` the least window. -/
theorem gap_below_first_stall (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (h : ¬ NoStallOnSegment N β) :
    ∃ ts : ℝ, 0 < ts ∧ ts ≤ β ∧ (β, ts) ∈ StallSet N ∧
      ∀ t' : ℝ, t' < ts → ∃ w : ℕ, 1 ≤ w ∧ ∀ (t : ℝ) (ht : 0 ≤ t), t ≤ t' →
        StripLift.TransferGapAt hN hβ ht (StripLift.seedMass w) w := by
  obtain ⟨ts, hpos, hle, hst, hv⟩ := segment_first_stall hN hβ h
  exact ⟨ts, hpos, hle, hst, fun t' ht' =>
    StripLift.segment_gap hN hβ fun s h0 h1 => hv s h0 (h1.trans_lt ht')⟩

/-- **The segment dichotomy**: at every `β ≥ 0`, either one rate serves the whole segment `{β} × [0, β]`, or there
is a first stall `t* ∈ (0, β]` below which every closed sub-segment `[0, t']` carries one rate. DERIVED: `0` the
axis; `1` the least window. -/
theorem segment_gap_dichotomy (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    (∃ w : ℕ, 1 ≤ w ∧ ∀ (t : ℝ) (ht : 0 ≤ t), t ≤ β →
      StripLift.TransferGapAt hN hβ ht (StripLift.seedMass w) w) ∨
    (∃ ts : ℝ, 0 < ts ∧ ts ≤ β ∧ (β, ts) ∈ StallSet N ∧
      ∀ t' : ℝ, t' < ts → ∃ w : ℕ, 1 ≤ w ∧ ∀ (t : ℝ) (ht : 0 ≤ t), t ≤ t' →
        StripLift.TransferGapAt hN hβ ht (StripLift.seedMass w) w) := by
  by_cases h : NoStallOnSegment N β
  · exact Or.inl (segment_gap_of_noStall hN hβ h)
  · exact Or.inr (gap_below_first_stall hN hβ h)

/-! ## 2. The ratio of partition functions as a plane average -/

section Ratio

open MassGap.CumulantStrip MassGap.MixCut MassGap.MixExpand MassGap.MixEqui MassGap.RectWilson MassGap.StripWidth

variable {n : ℕ}

/-- **The in-plane Gibbs average** `E_plane[F] = ∫ e^{−β S_in} F dU / ∫ e^{−β S_in} dU` on the side-`n` torus.
No numeral. -/
def planeE (N : ℕ) (β : ℝ) (n : ℕ) (F : (Lk n → SUN.SU N) → ℝ) : ℝ :=
  (∫ U, Real.exp (-(β * sinR N n U)) * F U ∂piH N n) / ∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n

/-- **`Z(β, 0, n)` is the in-plane mass**: `Z(β, 0, n) = ∫ e^{−β S_in} dU`. DERIVED: `0` the decoupled end. -/
theorem ZA_zero_eq (β : ℝ) (n : ℕ) :
    AnisoTorus.ZA N β 0 n = ∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n := by
  rw [MixCut.ZA_eq_int]
  simp only [zero_mul, add_zero]

/-- **Each tilted factor is positive**: `1 + c_t(x) = e^{−2t (x − ⟨φ⟩)}/H(−2t) > 0`. DERIVED: `1` the unit of the
product; `2` the orientations; `0` the sign. -/
theorem one_add_cT_pos (hN : N ≠ 0) (t x : ℝ) : 0 < 1 + cT N t x := by
  have hH := CumulantStrip.haarTilt_pos (N := N) hN t
  have h := div_pos (Real.exp_pos (-(2 * t) * (x - WindowRead.haarMeanN N))) hH
  unfold cT
  linarith

/-- **`Y(U) > 0` at every `t`**: the integrand `∏_p (1 + g_p)` is positive and continuous against a probability
measure. No width is read. DERIVED: `0` the sign; `1` the unit of the product. -/
theorem YR_pos (hN : N ≠ 0) (t : ℝ) (U : Lk n → SUN.SU N) : 0 < StripGas.YR N n t U := by
  have hpos : ∀ a : St n → SUN.SU N,
      0 < ∏ p ∈ (Finset.univ : Finset (Pm n)), (1 + StripGas.gR N n t U p a) := fun a =>
    Finset.prod_pos fun p _ => by
      unfold StripGas.gR CumulantStrip.gg
      exact one_add_cT_pos hN t _
  have hc : Continuous fun a : St n → SUN.SU N =>
      ∏ p ∈ (Finset.univ : Finset (Pm n)), (1 + StripGas.gR N n t U p a) :=
    continuous_finsetProd _ fun p _ => continuous_const.add (StripGas.continuous_gR t U p)
  unfold StripGas.YR StripGas.Yg
  rw [integral_pos_iff_support_of_nonneg (fun a => (hpos a).le) (StripGas.integrable_cont hc)]
  have hs : Function.support (fun a : St n → SUN.SU N =>
      ∏ p ∈ (Finset.univ : Finset (Pm n)), (1 + StripGas.gR N n t U p a)) = Set.univ :=
    Set.eq_univ_of_forall fun a => (hpos a).ne'
  rw [hs, measure_univ]
  exact zero_lt_one

/-- **`exp(Σ_x yS(U, x)) = Y(U)`**, at every `t`, from `StripOsc.log_YR_eq_sum_sym` and `YR_pos`. No numeral. -/
theorem exp_sum_yS (hN : N ≠ 0) (t : ℝ) (U : Lk n → SUN.SU N) :
    Real.exp (∑ x, StripOsc.yS N n t U x) = StripGas.YR N n t U := by
  rw [← StripOsc.log_YR_eq_sum_sym, Real.exp_log (YR_pos hN t U)]

/-- **`Z(t)/Z(0)` as a plane average**: at every `β`, `t`, `n` and `N ≠ 0`,
`Z(β, t, n)/Z(β, 0, n) = e^{−8 t n⁴ ⟨φ⟩} H(−2t)^{4 n⁴} E_plane[exp(Σ_x yS(U, x))]`. Composes
`CumulantStrip.ZA_eq_gas`, `StripGas.ZG_eq_integral_YR` and `exp_sum_yS`. DERIVED: `8 = 2 · 4`; `4` the normal
orientations; `2` the orientations; `0` the decoupled end. -/
theorem ZA_ratio (hN : N ≠ 0) (β t : ℝ) (n : ℕ) :
    AnisoTorus.ZA N β t n / AnisoTorus.ZA N β 0 n
      = Real.exp (-t * (8 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N)) * haarTilt N (-(2 * t)) ^ (4 * n ^ 4)
        * planeE N β n (fun U => Real.exp (∑ x, StripOsc.yS N n t U x)) := by
  have hY : (fun U : Lk n → SUN.SU N => Real.exp (∑ x, StripOsc.yS N n t U x))
      = StripGas.YR N n t := funext fun U => exp_sum_yS hN t U
  rw [hY, CumulantStrip.ZA_eq_gas hN, StripGas.ZG_eq_integral_YR, ZA_zero_eq]
  unfold planeE
  rw [mul_div_assoc]

/-- **The log form**: `log Z(β, t, n) − log Z(β, 0, n) = n⁴ ℓ(t) + log E_plane[exp(Σ_x yS(U, x))]`, with
`ℓ(t) = 4 log H(−2t) − 8 t ⟨φ⟩` (`CumulantStrip.ell`), at every `β`, `t`, `n` and `N ≠ 0`. DERIVED: as in
`ZA_ratio`. -/
theorem logZA_sub (hN : N ≠ 0) (β t : ℝ) (n : ℕ) :
    AnisoTorus.logZA N β t n - AnisoTorus.logZA N β 0 n
      = (n : ℝ) ^ 4 * ell N t + Real.log (planeE N β n (fun U => Real.exp (∑ x, StripOsc.yS N n t U x))) := by
  have hr := ZA_ratio hN β t n
  set c := planeE N β n (fun U => Real.exp (∑ x, StripOsc.yS N n t U x)) with hcdef
  have ha := Real.exp_pos (-t * (8 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N))
  have hb := pow_pos (CumulantStrip.haarTilt_pos (N := N) hN t) (4 * n ^ 4)
  have hZt := MixCut.ZA_pos (N := N) β t n
  have hZ0 := MixCut.ZA_pos (N := N) β 0 n
  have hq : 0 < AnisoTorus.ZA N β t n / AnisoTorus.ZA N β 0 n := div_pos hZt hZ0
  have hab := mul_pos ha hb
  have hc : 0 < c := by
    by_contra h
    have h := not_lt.mp h
    nlinarith
  unfold AnisoTorus.logZA
  rw [← Real.log_div hZt.ne' hZ0.ne', hr, Real.log_mul hab.ne' hc.ne', Real.log_mul ha.ne' hb.ne',
    Real.log_exp, Real.log_pow]
  unfold ell
  push_cast
  ring

/-- **The enumeration summand gives `Y` too**: for `|t| ≤ t₁`, `exp(Σ_x yR(U, x)) = Y(U)`, from
`StripGas.log_YR_eq_sum`. Inherited: `t₁` of `StripGas.tOne`. -/
theorem exp_sum_yR (hN : N ≠ 0) {t : ℝ} (ht : |t| ≤ StripGas.tOne) (U : Lk n → SUN.SU N) :
    Real.exp (∑ x, StripGas.yR N n t U x) = StripGas.YR N n t U := by
  rw [← StripGas.log_YR_eq_sum hN ht, Real.exp_log (YR_pos hN t U)]

/-- **The two summands give one plane average**, for `|t| ≤ t₁`. Inherited: `t₁` of `StripGas.tOne`. -/
theorem planeE_yR (hN : N ≠ 0) (β : ℝ) {t : ℝ} (ht : |t| ≤ StripGas.tOne) (n : ℕ) :
    planeE N β n (fun U => Real.exp (∑ x, StripGas.yR N n t U x))
      = planeE N β n (fun U => Real.exp (∑ x, StripOsc.yS N n t U x)) := by
  have e : (fun U : Lk n → SUN.SU N => Real.exp (∑ x, StripGas.yR N n t U x))
      = fun U => Real.exp (∑ x, StripOsc.yS N n t U x) :=
    funext fun U => (exp_sum_yR hN ht U).trans (exp_sum_yS hN t U).symm
  rw [e]

end Ratio

end MassGap.StripClose

#print axioms MassGap.StripClose.axis_mem_vanishSet
#print axioms MassGap.StripClose.axis_subset
#print axioms MassGap.StripClose.axis_nhds
#print axioms MassGap.StripClose.segment_first_stall
#print axioms MassGap.StripClose.segment_gap_of_noStall
#print axioms MassGap.StripClose.gap_below_first_stall
#print axioms MassGap.StripClose.segment_gap_dichotomy
#print axioms MassGap.StripClose.ZA_zero_eq
#print axioms MassGap.StripClose.one_add_cT_pos
#print axioms MassGap.StripClose.YR_pos
#print axioms MassGap.StripClose.exp_sum_yS
#print axioms MassGap.StripClose.ZA_ratio
#print axioms MassGap.StripClose.logZA_sub
#print axioms MassGap.StripClose.exp_sum_yR
#print axioms MassGap.StripClose.planeE_yR
