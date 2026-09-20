import Mathlib
import MassGap.OddLagSplit
import MassGap.LagOneDominates

/-!
# MassGap.LinkGram — link-reflection positivity for a GENERAL half-local observable

`OddLagSplit.plaqReflPositive_odd` proves `0 ≤ ⟨(F_q − a)·θ F_q⟩` at a link reflection for ONE
plaquette-energy observable. Every step of its proof except three is indifferent to which observable
is carried: `boltz_eq_paired_cross` is a statement about the weight alone, the three-block
factorisation and the mirror transport move variables, and
`CrossingIntegration.wilson_crossing_pairing_nonneg` — the theorem the chain ends in — already takes
an ARBITRARY bounded measurable function of the positive half's variables.

The three that are not indifferent are `OddLagSplit.aObs_local`, `measurable_aObs` and
`abs_aObs_le`: measurability, boundedness and half-locality of the observable. This file carries
those three as hypotheses instead of proving them of one plaquette, and re-runs the chain.

`gram_refl_positive` is the result: link-reflection positivity of the Wilson Gibbs state for any
measurable, bounded, `oblkS`-local real observable, at every even extent with `2 ≤ m` and every
`0 ≤ β` — the same domain `OddLagSplit.corrClay_reflection_positive` has.

`MassGap.LagOneDominates.pairReflPositive_iff` then turns the two-plaquette instance into
`wilsonCorrAt 3 β 2 ≤ wilsonCorrAt 3 β 1`, which is `SpectralFour.FourRepresentable`'s third
conjunct at the Clay aperture.

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

/-- **The positive half's observable-and-weight**, the crossing integration's `a`, with the
observable left as a parameter. `OddLagSplit.aObs` is the instance at `F = F_q − aC`.

DERIVED: no numeral. -/
noncomputable def gObs (F : (Link d n → MassGap.SUN.SU N) → ℝ) (β : ℝ)
    (U : Link d n → MassGap.SUN.SU N) : ℝ :=
  F U * Real.exp (-β * actPlusO τ a m U)

/-- **It reads the positive half alone**, provided `F` does. `actPlusO_local` supplies the weight.

DERIVED: no numeral. -/
theorem gObs_local (F : (Link d n → MassGap.SUN.SU N) → ℝ)
    (hFloc : ∀ U V : Link d n → MassGap.SUN.SU N,
      (∀ l ∈ oblkS τ a m, U l = V l) → F U = F V)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ) (U V : Link d n → MassGap.SUN.SU N)
    (hS : ∀ l ∈ oblkS τ a m, U l = V l) :
    gObs τ a m F β U = gObs τ a m F β V := by
  unfold gObs
  rw [hFloc U V hS, actPlusO_local τ a m hm hm0 U V hS]

/-- DERIVED: no numeral. -/
theorem measurable_gObs (F : (Link d n → MassGap.SUN.SU N) → ℝ) (hF : Measurable F) (β : ℝ) :
    Measurable (gObs (N := N) τ a m F β) :=
  hF.mul ((measurable_const.mul (measurable_actSum (oplqPlus τ a m))).exp)

/-- **The dressed observable is bounded.**

DERIVED: `2` is `WilsonAction.wilsonDensity`'s own range bound, through `ActionSplit.abs_actSum_le`;
the card is a count and `MF` is the caller's bound on `F`. -/
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

/-- **The dressed observable as a function of the positive half alone** — the crossing
integration's `a`. `OddLagSplit.aHalf` is the instance.

DERIVED: no numeral. -/
noncomputable def gHalf (F : (Link d n → MassGap.SUN.SU N) → ℝ) (β : ℝ)
    (x : ↥(oblkS τ a m) → MassGap.SUN.SU N) : ℝ :=
  gObs τ a m F β (extendS τ a m x)

/-- DERIVED: no numeral. -/
theorem measurable_gHalf (F : (Link d n → MassGap.SUN.SU N) → ℝ) (hF : Measurable F) (β : ℝ) :
    Measurable (gHalf (N := N) τ a m F β) :=
  (measurable_gObs τ a m F hF β).comp (measurable_extendS τ a m)

/-- DERIVED: `2` is `WilsonAction.wilsonDensity`'s range bound, carried from `abs_gObs_le`; the card
is a count and `MF` is the caller's bound on `F`. -/
theorem abs_gHalf_le (F : (Link d n → MassGap.SUN.SU N) → ℝ) {MF : ℝ}
    (hFb : ∀ U, |F U| ≤ MF) (hN : N ≠ 0) (β : ℝ) (x : ↥(oblkS τ a m) → MassGap.SUN.SU N) :
    |gHalf (N := N) τ a m F β x| ≤ MF * Real.exp (|β| * (2 * (oplqPlus τ a m).card)) :=
  abs_gObs_le τ a m F hFb hN β _

/-! ## 2. The integrand, after the plane substitution -/

/-- `OddLagSplit.oddIntegrand` with the observable left as a parameter.

DERIVED: no numeral; `a + a + 1` is the link reflection's own constant, carried. -/
noncomputable def gIntegrand (F : (Link d n → MassGap.SUN.SU N) → ℝ) (β : ℝ)
    (U : Link d n → MassGap.SUN.SU N) : ℝ :=
  gObs τ a m F β U * gObs τ a m F β (reflConf τ (a + a + 1) U)
    * Real.exp (-β * actCrossO τ a m (invLink (uplane τ a m) U))

/-- DERIVED: `a + a + 1` is the link reflection's own constant, carried from `OddLagSplit`. -/
theorem measurable_gIntegrand (F : (Link d n → MassGap.SUN.SU N) → ℝ) (hF : Measurable F)
    (β : ℝ) : Measurable (gIntegrand (N := N) τ a m F β) :=
  (((measurable_gObs τ a m F hF β)).mul
      ((measurable_gObs τ a m F hF β).comp
        (reflConf_measurePreserving (N := N) τ (a + a + 1)).measurable)).mul
    ((measurable_const.mul ((measurable_actSum (oplqCross τ a m)).comp
      (invLink_measurePreserving (N := N) (uplane τ a m)).measurable)).exp)

/-- DERIVED: `2` is `WilsonAction.wilsonDensity`'s range bound, carried through `abs_actSum_le`; the
cards are counts. -/
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

/-- **The substitution on the upper plane leaves the two observables alone** — `F` and its mirror
read the positive half or its mirror, and the plane meets neither. `OddLagSplit`'s proof of
`integral_odd_eq_oddIntegrand`, with `aObs_local` replaced by `gObs_local`.

DERIVED: `a + a + 1` is the link reflection's own constant and `n = 2 * m` the extent's own parity,
both carried from `OddLagSplit`. -/
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

/-- **THE INTEGRAND, IN THE CROSSING INTEGRATION'S VARIABLES.** `OddLagSplit.oddIntegrand_join`
with the observable left as a parameter.

DERIVED: no numeral of this file's; `1/N` and the card are `actCrossO_eq_trace_sum`'s. -/
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

/-- **THE PAIRING INTEGRAL IS NONNEGATIVE, FOR EVERY HALF-LOCAL OBSERVABLE.**
`OddLagSplit.odd_crossing_integral_nonneg` with the observable left as a parameter.

DERIVED: `2 ≤ m` is the plane assignment's own bound and `0 ≤ β` the cross kernel's, both carried
from `OddLagSplit`; no numeral is chosen here. -/
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

/-- **LINK-REFLECTION POSITIVITY OF THE WILSON GIBBS STATE, FOR A GENERAL HALF-LOCAL OBSERVABLE.**

`0 ≤ ⟨F · (F ∘ θ)⟩` at the link reflection with constant `a + a + 1`, for every measurable, bounded
observable `F` that reads the positive half `oblkS τ a m` alone.

The hypothesis list is exactly `OddLagSplit.odd_crossing_integral_nonneg`'s — even extent, `2 ≤ m`,
`0 ≤ β` — plus the three properties of `F` that `aObs_local`, `measurable_aObs` and `abs_aObs_le`
supply for a single plaquette. Nothing is assumed about the measure.

DERIVED: no numeral of this file's; `2 ≤ m` and `0 ≤ β` are carried from `OddLagSplit`. -/
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

/-! ## 4. The Clay instance — the two-plaquette observable of `LagOneDominates`

DERIVED throughout this section: `4` is the dimension and the extent, `3` is `SU(3)`'s rank and the
Clay aperture, `(0,1)` the plaquette plane and `2` the lag axis — all `WilsonBridge.corrClay`'s own.
The half-extent `m = 2` is `4 = 2 · 2`, and the reflection base `a = 0` is the origin of the level
count. No magnitude is chosen. -/

/-- **BOTH PLAQUETTES LIE IN THE POSITIVE HALF.** Every link of the `(0,1)` plaquette based at lag
site `s` runs transverse to the lag axis (`bd_link_dir_ne`) and sits at lag coordinate `s`
(`bd_link_tau_coord`), so `oblkS 2 0 2`'s transverse condition `0 < lv ∧ lv ≤ m` reads `0 < s ≤ 2` —
satisfied at `s = 1` and `s = 2`, which are exactly the two lag sites of the half.

DERIVED: `0 < s` and `s ≤ 2` are `oblkS`'s own transverse condition at `a = 0`, `m = 2`. -/
theorem pl_local {s : Fin 4} (h0 : 0 < (s : ℕ)) (h2 : (s : ℕ) ≤ 2)
    (l : Link 4 4) (hl : l ∈ (bd (MassGap.LagOneDominates.pl s)).map Prod.fst) :
    l ∈ oblkS (2 : Fin 4) (0 : Fin 4) 2 := by
  simp only [MassGap.LagOneDominates.pl] at hl
  have hdir : l.1 ≠ (2 : Fin 4) :=
    MassGap.ReflectPositive.bd_link_dir_ne (n := 4)
      MassGap.LagOneDominates.plane_ne.1 MassGap.LagOneDominates.plane_ne.2 _ l hl
  have hco : l.2 (2 : Fin 4) = siteAtHyper (d := 4) (n := 4) (2 : Fin 4) s (2 : Fin 4) :=
    MassGap.ReflectPositive.bd_link_tau_coord (n := 4)
      MassGap.LagOneDominates.plane_ne.1 MassGap.LagOneDominates.plane_ne.2 _ l hl
  rw [mem_oblkS, if_neg hdir]
  have hval : lv (0 : Fin 4) (l.2 (2 : Fin 4)) = (s : ℕ) := by
    rw [hco]
    simp [lv, siteAtHyper]
  rw [hval]
  exact ⟨h0, h2⟩

/-- **THE TWO-TERM OBSERVABLE READS THE POSITIVE HALF ALONE.** Each plaquette's holonomy depends only
on its own links (`ReflectionPositivity.hol_congr_on_support`), and `pl_local` puts those links in
`oblkS`.

DERIVED: `1` and `2` are the two lag sites of the half. -/
theorem gapObs_local (U V : Link 4 4 → MassGap.SUN.SU 3)
    (hS : ∀ l ∈ oblkS (2 : Fin 4) (0 : Fin 4) 2, U l = V l) :
    MassGap.LagOneDominates.gapObs U = MassGap.LagOneDominates.gapObs V := by
  have h1 : MassGap.ReflectPositive.plaqE 3 (MassGap.LagOneDominates.pl 1) U
      = MassGap.ReflectPositive.plaqE 3 (MassGap.LagOneDominates.pl 1) V := by
    show wilsonDensity (wilsonHol (bd (d := 4) (n := 4)) (MassGap.LagOneDominates.pl 1) U)
      = wilsonDensity (wilsonHol (bd (d := 4) (n := 4)) (MassGap.LagOneDominates.pl 1) V)
    rw [MassGap.ReflectionPositivity.hol_congr_on_support (bd (d := 4) (n := 4))
      (MassGap.LagOneDominates.pl 1) U V
      (fun l hl => hS l (pl_local (by norm_num) (by norm_num) l hl))]
  have h2 : MassGap.ReflectPositive.plaqE 3 (MassGap.LagOneDominates.pl 2) U
      = MassGap.ReflectPositive.plaqE 3 (MassGap.LagOneDominates.pl 2) V := by
    show wilsonDensity (wilsonHol (bd (d := 4) (n := 4)) (MassGap.LagOneDominates.pl 2) U)
      = wilsonDensity (wilsonHol (bd (d := 4) (n := 4)) (MassGap.LagOneDominates.pl 2) V)
    rw [MassGap.ReflectionPositivity.hol_congr_on_support (bd (d := 4) (n := 4))
      (MassGap.LagOneDominates.pl 2) U V
      (fun l hl => hS l (pl_local (by norm_num) (by norm_num) l hl))]
  show MassGap.ReflectPositive.plaqE 3 (MassGap.LagOneDominates.pl 1) U
      - MassGap.ReflectPositive.plaqE 3 (MassGap.LagOneDominates.pl 2) U = _
  rw [h1, h2]
  rfl

/-- DERIVED: no numeral. -/
theorem measurable_gapObs : Measurable MassGap.LagOneDominates.gapObs :=
  (MassGap.ReflectPositive.measurable_plaqE _).sub (MassGap.ReflectPositive.measurable_plaqE _)

/-- DERIVED: `2` is `WilsonAction.wilsonDensity`'s own range bound — each plaquette energy lies in
`[0, 2]`, so their difference lies in `[−2, 2]`. It is carried, not chosen. -/
theorem abs_gapObs_le (U : Link 4 4 → MassGap.SUN.SU 3) :
    |MassGap.LagOneDominates.gapObs U| ≤ 2 := by
  have h1 := MassGap.ReflectPositive.plaqE_nonneg (Nc := 3) (by norm_num)
    (MassGap.LagOneDominates.pl 1) U
  have h2 := MassGap.ReflectPositive.plaqE_le_two (Nc := 3) (by norm_num)
    (MassGap.LagOneDominates.pl 1) U
  have h3 := MassGap.ReflectPositive.plaqE_nonneg (Nc := 3) (by norm_num)
    (MassGap.LagOneDominates.pl 2) U
  have h4 := MassGap.ReflectPositive.plaqE_le_two (Nc := 3) (by norm_num)
    (MassGap.LagOneDominates.pl 2) U
  show |MassGap.ReflectPositive.plaqE 3 (MassGap.LagOneDominates.pl 1) U
      - MassGap.ReflectPositive.plaqE 3 (MassGap.LagOneDominates.pl 2) U| ≤ 2
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- **THE NAMED HYPOTHESIS OF `LagOneDominates`, DISCHARGED.**

`gram_refl_positive` at `d = 4`, `n = 4`, `N = 3`, `τ = 2`, `a = 0`, `m = 2`, with `F` the two-term
observable `F₁ − F₂`. The reflection constant `a + a + 1` is `1`, the link reflection whose positive
half is the pair of lag sites `{1, 2}`.

DERIVED: `4 = 2 · 2` is the extent and its half; `2 ≤ 2` is `OddLagSplit`'s own plane-assignment
bound met at the smallest extent that meets it; `0 ≤ β` is the cross kernel's sign condition. -/
theorem pairReflPositive {β : ℝ} (hβ : 0 ≤ β) : MassGap.LagOneDominates.PairReflPositive β := by
  have h := gram_refl_positive (2 : Fin 4) (0 : Fin 4) 2 MassGap.LagOneDominates.gapObs
    measurable_gapObs abs_gapObs_le gapObs_local (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hβ
  have hc : ((0 : Fin 4) + 0 + 1) = (1 : Fin 4) := by decide
  rw [hc] at h
  exact le_of_le_of_eq h
    (congrArg (MassGap.ReflectPositive.EW 3 β) (funext fun U => mul_comm _ _))

/-- **`ρ(2) ≤ ρ(1)` FOR THE SU(3) WILSON CORRELATION AT THE CLAY APERTURE, AT EVERY `β ≥ 0`.**

The third conjunct of `SpectralFour.FourRepresentable` at extent four, which
`SpectralFour.tripleFacts_not_ordered` shows does NOT follow from `TailRatio.TripleFacts`, and which
`SpectralFour.ordered_is_what_nonneg_lam_buys` identifies with positivity of the transfer spectrum.

It is proved here as reflection positivity at a LINK plane for a two-term half-space observable —
`LagOneDominates.pairReflPositive_iff` makes that identification exact — with the link-reflection
positivity supplied by `gram_refl_positive`, which is `OddLagSplit`'s crossing integration run with
the observable left as a parameter.

DERIVED: `3` is the Clay aperture; `1` and `2` are lag indices; `0 ≤ β` is the cross kernel's own
sign condition, carried from `OddLagSplit`. -/
theorem wilson_lag_two_le_lag_one {β : ℝ} (hβ : 0 ≤ β) :
    MassGap.wilsonCorrAt 3 β 2 ≤ MassGap.wilsonCorrAt 3 β 1 :=
  MassGap.LagOneDominates.lag_two_le_lag_one (pairReflPositive hβ)

/-- **THE EXTENT-FOUR REGION, WITH ONLY THE QUADRATIC LEFT.**

Three of `SpectralFour.FourRepresentable`'s four conjuncts now hold of the Wilson triple at every
`0 ≤ β`: `0 ≤ ρ(0)` and `0 ≤ ρ(2)` from `TailRatio.triple_wilsonCorrAt`, and `ρ(2) ≤ ρ(1)` from
`wilson_lag_two_le_lag_one`. The remaining hypothesis is the quadratic
`2ρ(1)² ≤ ρ(2)² + ρ(0)·ρ(2)`, which `SpectralFour.tripleFacts_not_quadratic` shows is independent of
everything else the tree proves. This file does not touch it; `MassGap.SlabQuadratic.wilson_quadratic`
supplies it, at every real coupling.

DERIVED: `3` is the Clay aperture; `0, 1, 2` are lag indices; `2` in `2ρ(1)²` is
`SpectralFour.FourRepresentable`'s own coefficient. -/
theorem wilsonSpectral_of_quadratic {β : ℝ} (hβ : 0 ≤ β)
    (hquad : 2 * MassGap.wilsonCorrAt 3 β 1 ^ 2
      ≤ MassGap.wilsonCorrAt 3 β 2 ^ 2
        + MassGap.wilsonCorrAt 3 β 0 * MassGap.wilsonCorrAt 3 β 2) :
    MassGap.WilsonSpectral 3 β :=
  MassGap.LagOneDominates.wilsonSpectral_of_pair_and_quadratic hβ (pairReflPositive hβ) hquad

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
#print axioms pl_local
#print axioms gapObs_local
#print axioms measurable_gapObs
#print axioms abs_gapObs_le
#print axioms pairReflPositive
#print axioms wilson_lag_two_le_lag_one
#print axioms wilsonSpectral_of_quadratic
end Audit

end MassGap.LinkGram
