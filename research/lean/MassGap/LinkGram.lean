import Mathlib
import MassGap.OddLagSplit

/-!
# MassGap.LinkGram — link-reflection positivity for a general half-local observable

`OddLagSplit.odd_crossing_integral_nonneg` proves the crossing integral nonnegative for one
plaquette-energy observable. Three steps of that argument look at the observable at all —
`OddLagSplit.aObs_local`, `measurable_aObs` and `abs_aObs_le`, which are half-locality,
measurability and boundedness. The rest does not: `boltz_eq_paired_cross` is a statement about the
weight alone, the three-block factorisation and the mirror transport move variables, and
`CrossingIntegration.wilson_crossing_pairing_nonneg`, which the chain ends in, already takes an
arbitrary bounded measurable function of the positive half's variables.

This file carries the three properties as hypotheses on a parameter `F` and re-runs the chain.

`gram_refl_positive` is the result:
`0 ≤ ReflectPositive.EW N β (fun U => F U * F (reflConf τ (a + a + 1) U))`, for every measurable `F`
bounded by some `MF` that reads `oblkS τ a m` alone, at `N ≠ 0`, at even extent `n = 2 * m` with
`2 ≤ m`, and at `0 ≤ β`.

Build: `python research/code/lean_build.py build MassGap.LinkGram`.
-/

namespace MassGap.LinkGram

open MassGap MassGap.Reflect MassGap.ReflectPositive MassGap.OddLagSplit
open MassGap.ActionSplit MassGap.CrossingIntegration MassGap.CharacterExpansion
open MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.WilsonReal MassGap.WilsonHypercubic MassGap.WilsonBridge
open MeasureTheory

variable {d n : ℕ} [NeZero n] {N : ℕ}
variable (τ : Fin d) (a : Fin n) (m : ℕ)

/-! ## 1. The dressed observable, for a general half-local `F` -/

/-- The positive half's observable together with its half of the Boltzmann weight:
`F U * exp (-β * actPlusO τ a m U)`. This is the crossing integration's `a`, with the observable
left as a parameter; `OddLagSplit.aObs` is the instance at `F = F_q − aC`.

DERIVED: no numeral appears in this statement. -/
noncomputable def gObs (F : (Link d n → MassGap.SUN.SU N) → ℝ) (β : ℝ)
    (U : Link d n → MassGap.SUN.SU N) : ℝ :=
  F U * Real.exp (-β * actPlusO τ a m U)

/-- `gObs` reads the positive half alone, given that `F` does: if `U` and `V` agree on
`oblkS τ a m` then `gObs τ a m F β U = gObs τ a m F β V`. The weight half is `actPlusO_local`,
which is where the two extent hypotheses are spent.

DERIVED: `n = 2 * m` is the even-extent condition — the statement holds at even extent only, `m`
being the half-extent — and `0 < m` is `actPlusO_local`'s own. Both are carried from
`OddLagSplit`. -/
theorem gObs_local (F : (Link d n → MassGap.SUN.SU N) → ℝ)
    (hFloc : ∀ U V : Link d n → MassGap.SUN.SU N,
      (∀ l ∈ oblkS τ a m, U l = V l) → F U = F V)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ) (U V : Link d n → MassGap.SUN.SU N)
    (hS : ∀ l ∈ oblkS τ a m, U l = V l) :
    gObs τ a m F β U = gObs τ a m F β V := by
  unfold gObs
  rw [hFloc U V hS, actPlusO_local τ a m hm hm0 U V hS]

/-- `gObs τ a m F β` is measurable when `F` is: a product of `F` with the exponential of a
measurable action sum.

DERIVED: no numeral appears in this statement. -/
theorem measurable_gObs (F : (Link d n → MassGap.SUN.SU N) → ℝ) (hF : Measurable F) (β : ℝ) :
    Measurable (gObs (N := N) τ a m F β) :=
  hF.mul ((measurable_const.mul (measurable_actSum (oplqPlus τ a m))).exp)

/-- The dressed observable is bounded:
`|gObs τ a m F β U| ≤ MF * exp (|β| * (2 * card (oplqPlus τ a m)))`, with `MF` the caller's bound
on `F`.

DERIVED: `2` is `WilsonAction.wilsonDensity`'s own range bound, reaching here through
`ActionSplit.abs_actSum_le`, so `2 * card` bounds the action of the positive half's plaquettes; the
card is a count. `0` is the rank condition `N ≠ 0`, which `abs_actSum_le` consumes because the
density divides by `N`. -/
theorem abs_gObs_le (F : (Link d n → MassGap.SUN.SU N) → ℝ) {MF : ℝ}
    (hFb : ∀ U, |F U| ≤ MF) (hN : N ≠ 0) (β : ℝ) (U : Link d n → MassGap.SUN.SU N) :
    |gObs τ a m F β U| ≤ MF * Real.exp (|β| * (2 * (oplqPlus τ a m).card)) := by
  unfold gObs
  rw [abs_mul]
  have hsecond : |Real.exp (-β * actPlusO (N := N) τ a m U)|
      ≤ Real.exp (|β| * (2 * (oplqPlus τ a m).card)) := by
    rw [abs_of_nonneg (Real.exp_nonneg _)]
    refine Real.exp_le_exp.mpr ?_
    have hA : |actPlusO (N := N) τ a m U| ≤ 2 * (oplqPlus τ a m).card := abs_actSum_le hN _ U
    calc -β * actPlusO (N := N) τ a m U ≤ |(-β) * actPlusO (N := N) τ a m U| := le_abs_self _
      _ = |β| * |actPlusO (N := N) τ a m U| := by rw [abs_mul, abs_neg]
      _ ≤ |β| * (2 * (oplqPlus τ a m).card) := mul_le_mul_of_nonneg_left hA (abs_nonneg β)
  exact mul_le_mul (hFb U) hsecond (abs_nonneg _) (le_trans (abs_nonneg _) (hFb U))

/-- The dressed observable as a function of the positive half's variables alone — the crossing
integration's `a`, obtained by composing `gObs` with `extendS`. `OddLagSplit.aHalf` is the
instance.

DERIVED: no numeral appears in this statement. -/
noncomputable def gHalf (F : (Link d n → MassGap.SUN.SU N) → ℝ) (β : ℝ)
    (x : ↥(oblkS τ a m) → MassGap.SUN.SU N) : ℝ :=
  gObs τ a m F β (extendS τ a m x)

/-- `gHalf τ a m F β` is measurable when `F` is, by `measurable_gObs` and `measurable_extendS`.

DERIVED: no numeral appears in this statement. -/
theorem measurable_gHalf (F : (Link d n → MassGap.SUN.SU N) → ℝ) (hF : Measurable F) (β : ℝ) :
    Measurable (gHalf (N := N) τ a m F β) :=
  (measurable_gObs τ a m F hF β).comp (measurable_extendS τ a m)

/-- `gHalf` inherits `abs_gObs_le`'s bound, at every configuration of the positive half.

DERIVED: `2` is `WilsonAction.wilsonDensity`'s range bound, carried from `abs_gObs_le`; the card is
a count and `MF` is the caller's bound on `F`. `0` is the rank condition `N ≠ 0`, carried with
it. -/
theorem abs_gHalf_le (F : (Link d n → MassGap.SUN.SU N) → ℝ) {MF : ℝ}
    (hFb : ∀ U, |F U| ≤ MF) (hN : N ≠ 0) (β : ℝ) (x : ↥(oblkS τ a m) → MassGap.SUN.SU N) :
    |gHalf (N := N) τ a m F β x| ≤ MF * Real.exp (|β| * (2 * (oplqPlus τ a m).card)) :=
  abs_gObs_le τ a m F hFb hN β _

/-! ## 2. The integrand, after the plane substitution -/

/-- The reflected product whose integral the crossing argument bounds: `gObs` at `U`, times `gObs`
at the mirror configuration `reflConf τ (a + a + 1) U`, times the cross-term weight. This is
`OddLagSplit.oddIntegrand` with the observable left as a parameter.

DERIVED: no numeral appears in this statement; `a + a + 1` is the link reflection's own constant,
carried from `OddLagSplit`. -/
noncomputable def gIntegrand (F : (Link d n → MassGap.SUN.SU N) → ℝ) (β : ℝ)
    (U : Link d n → MassGap.SUN.SU N) : ℝ :=
  gObs τ a m F β U * gObs τ a m F β (reflConf τ (a + a + 1) U)
    * Real.exp (-β * actCrossO τ a m (invLink (uplane τ a m) U))

/-- `gIntegrand τ a m F β` is measurable when `F` is. The mirror and the plane substitution are
measurable because `reflConf` and `invLink` preserve the measure.

DERIVED: `a + a + 1` is the link reflection's own constant, carried from `OddLagSplit`. -/
theorem measurable_gIntegrand (F : (Link d n → MassGap.SUN.SU N) → ℝ) (hF : Measurable F)
    (β : ℝ) : Measurable (gIntegrand (N := N) τ a m F β) :=
  (((measurable_gObs τ a m F hF β)).mul
      ((measurable_gObs τ a m F hF β).comp
        (reflConf_measurePreserving (N := N) τ (a + a + 1)).measurable)).mul
    ((measurable_const.mul ((measurable_actSum (oplqCross τ a m)).comp
      (invLink_measurePreserving (N := N) (uplane τ a m)).measurable)).exp)

/-- `gIntegrand` is bounded, by `abs_gObs_le` twice and `abs_exp_actCrossO_le` once.

DERIVED: `2` is `WilsonAction.wilsonDensity`'s range bound, carried through
`ActionSplit.abs_actSum_le`; the cards are counts. `0` is the rank condition `N ≠ 0`, which those
bounds consume. -/
theorem abs_gIntegrand_le (F : (Link d n → MassGap.SUN.SU N) → ℝ) {MF : ℝ}
    (hFb : ∀ U, |F U| ≤ MF) (hN : N ≠ 0) (β : ℝ) (U : Link d n → MassGap.SUN.SU N) :
    |gIntegrand (N := N) τ a m F β U|
      ≤ (MF * Real.exp (|β| * (2 * (oplqPlus τ a m).card)))
        * (MF * Real.exp (|β| * (2 * (oplqPlus τ a m).card)))
        * Real.exp (|β| * (2 * (oplqCross τ a m).card)) := by
  have hMF : 0 ≤ MF := le_trans (abs_nonneg _) (hFb U)
  show |gObs τ a m F β U * gObs τ a m F β (reflConf τ (a + a + 1) U)
      * Real.exp (-β * actCrossO τ a m (invLink (uplane τ a m) U))| ≤ _
  rw [abs_mul, abs_mul]
  refine mul_le_mul (mul_le_mul (abs_gObs_le τ a m F hFb hN β U)
    (abs_gObs_le τ a m F hFb hN β _) (abs_nonneg _) (by positivity))
    (abs_exp_actCrossO_le τ a m hN β _) (abs_nonneg _) (by positivity)

/-- The substitution on the upper plane leaves the two observables alone: `F` and its mirror read
the positive half or its mirror, and the plane meets neither, so the integral of the reflected
product equals the integral of `gIntegrand`. This is `OddLagSplit`'s proof of
`integral_odd_eq_oddIntegrand` with `aObs_local` replaced by `gObs_local`.

DERIVED: `a + a + 1` is the link reflection's own constant; `n = 2 * m` is the even-extent
condition, so this holds at even extent only, and `0 < m` accompanies it. All are carried from
`OddLagSplit`. -/
theorem integral_odd_eq_gIntegrand (F : (Link d n → MassGap.SUN.SU N) → ℝ)
    (hF : Measurable F)
    (hFloc : ∀ U V : Link d n → MassGap.SUN.SU N,
      (∀ l ∈ oblkS τ a m, U l = V l) → F U = F V)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ) :
    (∫ U, gObs (N := N) τ a m F β U * gObs τ a m F β (reflConf τ (a + a + 1) U)
        * Real.exp (-β * actCrossO τ a m U)
        ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N))))
      = ∫ U, gIntegrand (N := N) τ a m F β U
        ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N))) := by
  have hFm : Measurable (fun U : Link d n → MassGap.SUN.SU N =>
      gObs (N := N) τ a m F β U * gObs τ a m F β (reflConf τ (a + a + 1) U)
        * Real.exp (-β * actCrossO τ a m U)) :=
    ((measurable_gObs τ a m F hF β).mul
        ((measurable_gObs τ a m F hF β).comp
          (reflConf_measurePreserving (N := N) τ (a + a + 1)).measurable)).mul
      ((measurable_const.mul (measurable_actSum (oplqCross τ a m))).exp)
  rw [← integral_comp_of_mp (invLink_measurePreserving (N := N) (uplane τ a m)) hFm]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
  have hoff : ∀ l : Link d n, l ∈ oblkS τ a m →
      invLink (uplane τ a m) U l = U l := by
    intro l hl
    refine invLink_of_not_mem _ _ (fun hc => ?_)
    exact (Finset.disjoint_left.mp (oblkS_disjoint_oblkR τ a m)) hl
      ((mem_uplane τ a m l).mp hc).1
  have hoffT : ∀ l : Link d n, l ∈ oblkT τ a m →
      invLink (uplane τ a m) U l = U l := by
    intro l hl
    refine invLink_of_not_mem _ _ (fun hc => ?_)
    exact (Finset.disjoint_left.mp (oblkT_disjoint_oblkR τ a m)) hl
      ((mem_uplane τ a m l).mp hc).1
  have h1 : gObs (N := N) τ a m F β (invLink (uplane τ a m) U) = gObs τ a m F β U :=
    gObs_local τ a m F hFloc hm hm0 β _ _ hoff
  have h2 : gObs (N := N) τ a m F β (reflConf τ (a + a + 1) (invLink (uplane τ a m) U))
      = gObs τ a m F β (reflConf τ (a + a + 1) U) := by
    refine gObs_local τ a m F hFloc hm hm0 β _ _ (fun l hl => ?_)
    have hT : reflLink τ (a + a + 1) l ∈ oblkT τ a m := oblkS_maps_oblkT τ a m hm hm0 hl
    show (if l.1 = τ then (invLink (uplane τ a m) U (reflLink τ (a + a + 1) l))⁻¹
        else invLink (uplane τ a m) U (reflLink τ (a + a + 1) l))
      = (if l.1 = τ then (U (reflLink τ (a + a + 1) l))⁻¹
        else U (reflLink τ (a + a + 1) l))
    rw [hoffT _ hT]
  show gObs τ a m F β (invLink (uplane τ a m) U)
      * gObs τ a m F β (reflConf τ (a + a + 1) (invLink (uplane τ a m) U))
      * Real.exp (-β * actCrossO τ a m (invLink (uplane τ a m) U)) = _
  rw [h1, h2]
  rfl

/-- The integrand in the crossing integration's variables: at a configuration split as
`joinO τ a m g x (mirrorT τ a m hm hm0 y)`, `gIntegrand` factors into the constant cross weight
`exp (-β * card (oplqCross τ a m))` times `gHalf` at `x`, `gHalf` at `y`, and the exponential of
`(β / N) * hsRe` of the two crossing words. `OddLagSplit.oddIntegrand_join` is the instance at one
plaquette energy.

DERIVED: `N ≠ 0` is what `actCrossO_eq_trace_sum` consumes, the density dividing by `N`;
`n = 2 * m` is the even-extent condition and `0 < m` accompanies it; `2 ≤ m` is the plane
assignment's own bound, spent in `sum_re_tr_oplqCross`. The `1 / N` of `actCrossO_eq_trace_sum` is
absorbed into `β / N` and does not appear here. -/
theorem gIntegrand_join (F : (Link d n → MassGap.SUN.SU N) → ℝ)
    (hFloc : ∀ U V : Link d n → MassGap.SUN.SU N,
      (∀ l ∈ oblkS τ a m, U l = V l) → F U = F V)
    (hN : N ≠ 0) (hm : n = 2 * m) (hm0 : 0 < m) (hm2 : 2 ≤ m) (β : ℝ)
    (g : ↥(oblkR τ a m) → MassGap.SUN.SU N) (x y : ↥(oblkS τ a m) → MassGap.SUN.SU N) :
    gIntegrand (N := N) τ a m F β (joinO τ a m g x (mirrorT τ a m hm hm0 y))
      = Real.exp (-β * ((oplqCross τ a m).card : ℝ))
        * (gHalf τ a m F β x * gHalf τ a m F β y
          * Real.exp ((β / (N : ℝ))
            * hsRe (crossWord τ a m hm hm0 (planeAct (planeA τ a m) (planeB τ a m) g x))
                (crossWord τ a m hm hm0 y))) := by
  have h1 : gObs (N := N) τ a m F β (joinO τ a m g x (mirrorT τ a m hm hm0 y))
      = gHalf τ a m F β x :=
    gObs_local τ a m F hFloc hm hm0 β _ _
      (fun l hl => by rw [joinO_mem_S τ a m g x _ hl, extendS_mem τ a m x hl])
  have h2 : gObs (N := N) τ a m F β
      (reflConf τ (a + a + 1) (joinO τ a m g x (mirrorT τ a m hm hm0 y)))
      = gHalf τ a m F β y :=
    gObs_local τ a m F hFloc hm hm0 β _ _
      (fun l hl => by
        rw [reflConf_joinO_mirror τ a m hm hm0 g x y hl, extendS_mem τ a m y hl])
  have h3 : actCrossO (N := N) τ a m
      (invLink (uplane τ a m) (joinO τ a m g x (mirrorT τ a m hm hm0 y)))
      = ((oplqCross τ a m).card : ℝ)
        - (1 / (N : ℝ)) * hsRe (crossWord τ a m hm hm0
            (planeAct (planeA τ a m) (planeB τ a m) g x)) (crossWord τ a m hm hm0 y) := by
    rw [actCrossO_eq_trace_sum τ a m hN, sum_re_tr_oplqCross τ a m hm hm0 hm2 g x y]
  show gObs τ a m F β (joinO τ a m g x (mirrorT τ a m hm hm0 y))
      * gObs τ a m F β (reflConf τ (a + a + 1) (joinO τ a m g x (mirrorT τ a m hm hm0 y)))
      * Real.exp (-β * actCrossO τ a m
          (invLink (uplane τ a m) (joinO τ a m g x (mirrorT τ a m hm hm0 y)))) = _
  rw [h1, h2, h3]
  have hexp : Real.exp (-β * (((oplqCross τ a m).card : ℝ)
        - (1 / (N : ℝ)) * hsRe (crossWord τ a m hm hm0
            (planeAct (planeA τ a m) (planeB τ a m) g x)) (crossWord τ a m hm hm0 y)))
      = Real.exp (-β * ((oplqCross τ a m).card : ℝ))
        * Real.exp ((β / (N : ℝ)) * hsRe (crossWord τ a m hm hm0
            (planeAct (planeA τ a m) (planeB τ a m) g x)) (crossWord τ a m hm hm0 y)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-! ## 3. The crossing integral, and the positivity -/

/-- The pairing integral is nonnegative for every half-local observable:
`0 ≤ ∫ gObs τ a m F β U * gObs τ a m F β (reflConf τ (a + a + 1) U) * exp (-β * actCrossO τ a m U)`.
This is `OddLagSplit.odd_crossing_integral_nonneg` with the observable left as a parameter, and it
ends in `CrossingIntegration.wilson_crossing_pairing_nonneg`.

DERIVED: `a + a + 1` is the link reflection's own constant. `2 ≤ m` is the plane assignment's own
bound and `0 ≤ β` the cross kernel's sign condition; `n = 2 * m` restricts the statement to even
extent and `0 < m` accompanies it, and `N ≠ 0` is the rank condition. All are carried from
`OddLagSplit`; no numeral is chosen here. -/
theorem g_crossing_integral_nonneg (F : (Link d n → MassGap.SUN.SU N) → ℝ)
    (hF : Measurable F) {MF : ℝ} (hFb : ∀ U, |F U| ≤ MF)
    (hFloc : ∀ U V : Link d n → MassGap.SUN.SU N,
      (∀ l ∈ oblkS τ a m, U l = V l) → F U = F V)
    (hN : N ≠ 0) (hm : n = 2 * m) (hm0 : 0 < m) (hm2 : 2 ≤ m) {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ ∫ U, gObs (N := N) τ a m F β U
        * gObs τ a m F β (reflConf τ (a + a + 1) U)
        * Real.exp (-β * actCrossO τ a m U)
        ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N))) := by
  have hMF : 0 ≤ MF := le_trans (abs_nonneg _) (hFb (fun _ => 1))
  rw [integral_odd_eq_gIntegrand τ a m F hF hFloc hm hm0 β,
    integral_oblk_mirror τ a m hm hm0 _ (measurable_gIntegrand τ a m F hF β)
      (abs_gIntegrand_le τ a m F hFb hN β)]
  have hstep : (∫ g, (∫ x, (∫ y, gIntegrand (N := N) τ a m F β
            (joinO τ a m g x (mirrorT τ a m hm hm0 y))
          ∂(cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N))))
        ∂(cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N))))
      ∂(cvol ↥(oblkR τ a m) (probHaar (MassGap.SUN.SU N))))
      = Real.exp (-β * ((oplqCross τ a m).card : ℝ))
        * ∫ g, (∫ x, (∫ y, gHalf τ a m F β x * gHalf τ a m F β y
              * Real.exp ((β / (N : ℝ))
                * hsRe (crossWord τ a m hm hm0
                    (planeAct (planeA τ a m) (planeB τ a m) g x))
                  (crossWord τ a m hm hm0 y))
            ∂(cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N))))
          ∂(cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N))))
        ∂(cvol ↥(oblkR τ a m) (probHaar (MassGap.SUN.SU N))) := by
    have hy : ∀ (g : ↥(oblkR τ a m) → MassGap.SUN.SU N)
        (x : ↥(oblkS τ a m) → MassGap.SUN.SU N),
        (∫ y, gIntegrand (N := N) τ a m F β
            (joinO τ a m g x (mirrorT τ a m hm hm0 y))
          ∂(cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N))))
        = Real.exp (-β * ((oplqCross τ a m).card : ℝ))
          * ∫ y, (gHalf τ a m F β x * gHalf τ a m F β y
              * Real.exp ((β / (N : ℝ))
                * hsRe (crossWord τ a m hm hm0
                    (planeAct (planeA τ a m) (planeB τ a m) g x))
                  (crossWord τ a m hm hm0 y)))
            ∂(cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N))) := by
      intro g x
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall
        (fun y => gIntegrand_join τ a m F hFloc hN hm hm0 hm2 β g x y))
    have hx : ∀ g : ↥(oblkR τ a m) → MassGap.SUN.SU N,
        (∫ x, (∫ y, gIntegrand (N := N) τ a m F β
              (joinO τ a m g x (mirrorT τ a m hm hm0 y))
            ∂(cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N))))
          ∂(cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N))))
        = Real.exp (-β * ((oplqCross τ a m).card : ℝ))
          * ∫ x, (∫ y, (gHalf τ a m F β x * gHalf τ a m F β y
                * Real.exp ((β / (N : ℝ))
                  * hsRe (crossWord τ a m hm hm0
                      (planeAct (planeA τ a m) (planeB τ a m) g x))
                    (crossWord τ a m hm hm0 y)))
              ∂(cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N))))
            ∂(cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N))) := by
      intro g
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun x => hy g x))
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun g => hx g))
  rw [hstep]
  refine mul_nonneg (Real.exp_nonneg _) ?_
  refine wilson_crossing_pairing_nonneg
    (cvol ↥(oblkR τ a m) (probHaar (MassGap.SUN.SU N)))
    (cvol ↥(oblkS τ a m) (probHaar (MassGap.SUN.SU N)))
    (measurable_uncurry_planeAct (planeA τ a m) (planeB τ a m))
    (fun g => planeAct_measurePreserving (planeA τ a m) (planeB τ a m) g)
    (fun g h u => planeAct_mul (planeA τ a m) (planeB τ a m) g h u)
    (crossWord τ a m hm hm0)
    (measurable_coord_crossWord τ a m hm hm0)
    (fun p v => abs_coord_crossWord_le_one τ a m hm hm0 p v)
    (fun g u v => hsRe_crossWord_planeAct τ a m hm hm0 g u v)
    (measurable_gHalf τ a m F hF β) (by positivity)
    (fun x => abs_gHalf_le τ a m F hFb hN β x) ?_
  positivity

/-- Link-reflection positivity of the Wilson Gibbs state for a general half-local observable:
`0 ≤ ReflectPositive.EW N β (fun U => F U * F (reflConf τ (a + a + 1) U))`, the reflection being the
link reflection with constant `a + a + 1`, for every measurable `F` bounded by `MF` that reads the
positive half `oblkS τ a m` alone.

The hypothesis list is `OddLagSplit.odd_crossing_integral_nonneg`'s — `N ≠ 0`, even extent,
`2 ≤ m`, `0 ≤ β` — plus the three properties of `F` that `aObs_local`, `measurable_aObs` and
`abs_aObs_le` supply for a single plaquette. Nothing is assumed about the measure; positivity of
the partition function comes from `wilsonSystem_partition_pos`.

DERIVED: `a + a + 1` is the link reflection's own constant. `2 ≤ m`, `0 ≤ β`, `n = 2 * m`, `0 < m`
and `N ≠ 0` are carried from `OddLagSplit`; no numeral is chosen here. -/
theorem gram_refl_positive (F : (Link d n → MassGap.SUN.SU N) → ℝ)
    (hF : Measurable F) {MF : ℝ} (hFb : ∀ U, |F U| ≤ MF)
    (hFloc : ∀ U V : Link d n → MassGap.SUN.SU N,
      (∀ l ∈ oblkS τ a m, U l = V l) → F U = F V)
    (hN : N ≠ 0) (hm : n = 2 * m) (hm0 : 0 < m) (hm2 : 2 ≤ m) {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ MassGap.ReflectPositive.EW N β
      (fun U => F U * F (reflConf τ (a + a + 1) U)) := by
  have hZ : 0 < (MassGap.WilsonHypercubic.sysWilson N d n).partition
      (probHaar (MassGap.SUN.SU N)) β :=
    wilsonSystem_partition_pos hN (bd (d := d) (n := n)) β
  have hcross := g_crossing_integral_nonneg τ a m F hF hFb hFloc hN hm hm0 hm2 hβ
  have hint : ∀ U : Link d n → MassGap.SUN.SU N,
      F U * F (reflConf τ (a + a + 1) U)
          * (MassGap.WilsonHypercubic.sysWilson N d n).boltz β U
        = gObs τ a m F β U * gObs τ a m F β (reflConf τ (a + a + 1) U)
          * Real.exp (-β * actCrossO τ a m U) := by
    intro U
    rw [boltz_eq_paired_cross τ a m hN hm hm0 β U]
    unfold gObs
    ring
  have hEq : (∫ U, gObs (N := N) τ a m F β U
        * gObs τ a m F β (reflConf τ (a + a + 1) U)
        * Real.exp (-β * actCrossO τ a m U)
        ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N))))
      = ∫ U, F U * F (reflConf τ (a + a + 1) U)
          * (MassGap.WilsonHypercubic.sysWilson N d n).boltz β U
        ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N))) :=
    integral_congr_ae (Filter.Eventually.of_forall (fun U => (hint U).symm))
  unfold MassGap.ReflectPositive.EW System.expect System.corrNum
  exact div_nonneg (le_of_le_of_eq hcross hEq) hZ.le

section Audit
#print axioms gObs
#print axioms gHalf
#print axioms gIntegrand
#print axioms gObs_local
#print axioms measurable_gObs
#print axioms abs_gObs_le
#print axioms measurable_gHalf
#print axioms abs_gHalf_le
#print axioms measurable_gIntegrand
#print axioms abs_gIntegrand_le
#print axioms integral_odd_eq_gIntegrand
#print axioms gIntegrand_join
#print axioms g_crossing_integral_nonneg
#print axioms gram_refl_positive
end Audit

end MassGap.LinkGram
