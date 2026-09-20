import Mathlib
import MassGap.ReflectPositive
import MassGap.SpectralFour

/-!
# MassGap.LagOneDominates — `ρ(2) ≤ ρ(1)` IS a reflection-positivity instance

`SpectralFour.four_iff` reduces `Complete.WilsonSpectral 3 β` to four inequalities on the triple
`(ρ(0), ρ(1), ρ(2))` at extent four. Two are proved; `ρ(2) ≤ ρ(1)` is one of the two that are not,
and `SpectralFour.ordered_is_what_nonneg_lam_buys` identifies it as positivity of the transfer
spectrum rather than as an estimate on a correlation.

This file names the reflection form whose positivity it is, and proves the identification EXACTLY.

## The identity

Write `F_s` for the plaquette-energy observable of the `(0,1)` plaquette based at lag-site `s` along
the lag axis `2`, and `θ_c` for `Reflect.reflConf 2 c`, whose action on lag sites is `s ↦ c − s`
(`plaqE_siteAtHyper_reflConf`). Take the LINK reflection `θ₁` — the one whose two planes fall
between lag sites `0,1` and between `2,3`, so that it has no fixed site and its positive half is the
pair of lag sites `{1, 2}`. Then for the TWO-TERM half-space observable `G = F₁ − F₂`,

    θ₁G = F₀ − F₃,   ⟨θ₁G · G⟩ = ⟨F₀F₁⟩ − ⟨F₀F₂⟩ − ⟨F₃F₁⟩ + ⟨F₃F₂⟩ = 2(ρ(1) − ρ(2)).

The two mixed terms are folded onto the first two by the reflection invariance of the Gibbs state at
`θ₃` (`Reflect.expect_reflect_invariant`), which sends `3 ↦ 0` and `2 ↦ 1`; no
translation invariance of the two-point function is used anywhere, and the disconnected floor `⟨F⟩²`
cancels because `G` has zero total weight. `pairing_eq_two_mul_gap` is that computation, and
`pairReflPositive_iff` turns it into an IFF: the target is not merely implied by this positivity, it
IS it.

## What this changes about the obligation

`ReflectPositive.PlaqReflPositive Nc τ c β q` is the ONE-observable pairing `0 ≤ ⟨(F_q − a)·θ_c F_q⟩`,
and `OddLagSplit.plaqReflPositive_odd` PROVES it at exactly this reflection — the link reflection with
constant `a + a + 1` — at every even extent `≥ 4` and every `0 ≤ β`, with the plaquette's links
required to lie in the positive half `OddLagSplit.oblkS`. At `τ = 2`, `a = 0`, `m = 2`, `n = 4` that
half is the transverse links at lag levels `1` and `2`, so BOTH of `G`'s plaquettes lie in it
(`LinkGram.pl_local`).

So `PairReflPositive` is the TWO-TERM Gram instance of a positivity the tree proves in the one-term
case, at the same plane, the same half, the same extent and the same coupling range. `LinkGram`
supplies the two-term case and hence `PairReflPositive` itself: `OddLagSplit`'s crossing integration
is stated about the single plaquette observable `wilsonDensity (wilsonHol (bd q₀) U) − aC`, while
`CrossingIntegration.wilson_crossing_pairing_nonneg` — the result that chain ends in — already takes
an ARBITRARY bounded measurable function of the positive half's variables, so the chain re-runs with
the observable as a parameter.

This file carries `PairReflPositive` as a hypothesis and proves it equivalent to the target;
`MassGap.LinkGram.pairReflPositive` discharges it at every `0 ≤ β`.

Build: `python research/code/lean_build.py build MassGap.LagOneDominates`.
-/

namespace MassGap.LagOneDominates

open MassGap MassGap.Reflect MassGap.ReflectPositive
open MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.WilsonReal MassGap.WilsonHypercubic MassGap.WilsonBridge
open MeasureTheory

variable {d n Nc : ℕ}

/-! ## 1. The reflection acts on lag sites by `s ↦ c − s`

`ReflectPositive.reflPlaq_origin` and `plaqE_lag` do this at the origin only, which is all
`corrHyper_eq_pairing` needs. A two-term observable needs it at a general lag site. -/

/-- **THE REFLECTION ON A LAG SITE.** `reflSite τ c` fixes every coordinate but `τ` and sends the
`τ` coordinate `s` to `c − s`, so it carries the lag site `s` to the lag site `c − s`.

DERIVED: no numeral; `c` and `s` are the caller's and `τ` is the caller's axis. -/
theorem reflSite_siteAtHyper [NeZero n] (τ : Fin d) (c s : Fin n) :
    reflSite τ c (siteAtHyper (d := d) (n := n) τ s) = siteAtHyper τ (c - s) := by
  funext j
  by_cases hj : j = τ
  · subst hj
    simp [reflSite, siteAtHyper]
  · simp [reflSite, siteAtHyper, Function.update_of_ne hj]

/-- **THE REFLECTION ON A LAG-SITE PLAQUETTE.** A plaquette whose plane misses the reflection axis
keeps its plane and moves its corner, so `reflPlaq` takes its third branch and
`reflSite_siteAtHyper` finishes it.

DERIVED: no numeral. -/
theorem reflPlaq_siteAtHyper [NeZero n] {μ ν τ : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ) (c s : Fin n) :
    reflPlaq τ c (((μ, ν), siteAtHyper τ s) : Plaq d n)
      = ((μ, ν), siteAtHyper τ (c - s)) := by
  simp only [reflPlaq, hμ, hν, if_false, reflSite_siteAtHyper]

/-- **THE OBSERVABLE AT LAG SITE `s`, COMPOSED WITH `θ_c`, IS THE OBSERVABLE AT LAG SITE `c − s`.**

`ReflectPositive.plaqE_lag` is the `s = 0` case. The general case is what a half-space observable
built from more than one plaquette needs, and it is the only geometric input to the identity in §4.

DERIVED: no numeral. -/
theorem plaqE_siteAtHyper_reflConf (Nc : ℕ) [NeZero n] {μ ν τ : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ)
    (c s : Fin n) (U : Link d n → MassGap.SUN.SU Nc) :
    plaqE Nc (((μ, ν), siteAtHyper τ s) : Plaq d n) (reflConf τ c U)
      = plaqE Nc (((μ, ν), siteAtHyper τ (c - s)) : Plaq d n) U := by
  rw [plaqE_reflConf Nc τ c, reflPlaq_siteAtHyper hμ hν]

/-! ## 2. The Gibbs state is linear on a product of two differences

`ReflectPositive.EW_pair_sub_const` expands `(F − a)(G − a)` for two plaquette observables centred
at a CONSTANT. A two-term half-space observable needs the expansion of `(F − G)(H − K)` for four
plaquette observables, which is a different combination and not an instance of it. -/

/-- The integrand of a two-plaquette correlation is integrable against the Boltzmann weight.

DERIVED: `4` is `2 · 2`, the product of `WilsonAction.wilsonDensity`'s own range bound with itself
(`ReflectPositive.abs_plaqE_le_two`). It is carried from there, not chosen. -/
private theorem intPair (hNc : Nc ≠ 0) [NeZero n] (β : ℝ) (p q : Plaq d n) :
    Integrable (fun U => (plaqE Nc p U * plaqE Nc q U)
        * (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).boltz β U)
      ((wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).vol
        (probHaar (MassGap.SUN.SU Nc))) :=
  wilsonSystem_mul_boltz_integrable hNc _ β _
    ((measurable_plaqE p).mul (measurable_plaqE q)) 4 (fun U => by
      rw [abs_mul]
      exact le_trans (mul_le_mul (abs_plaqE_le_two hNc p U) (abs_plaqE_le_two hNc q U)
        (abs_nonneg _) (by norm_num)) (by norm_num))

/-- **THE GIBBS STATE EXPANDS A PRODUCT OF TWO DIFFERENCES.**

    ⟨(F_p − F_q)(F_r − F_s)⟩ = ⟨F_p F_r⟩ − ⟨F_p F_s⟩ − ⟨F_q F_r⟩ + ⟨F_q F_s⟩.

Four integrability side conditions and one division by the partition function; no property of the
plaquettes is used, and they need not be distinct.

DERIVED: no numeral; the four terms are the four products. -/
theorem EW_diff_mul_diff (hNc : Nc ≠ 0) [NeZero n] (β : ℝ) (p q r s : Plaq d n) :
    EW Nc β (fun U => (plaqE Nc p U - plaqE Nc q U) * (plaqE Nc r U - plaqE Nc s U))
      = EW Nc β (fun U => plaqE Nc p U * plaqE Nc r U)
        - EW Nc β (fun U => plaqE Nc p U * plaqE Nc s U)
        - EW Nc β (fun U => plaqE Nc q U * plaqE Nc r U)
        + EW Nc β (fun U => plaqE Nc q U * plaqE Nc s U) := by
  have hpr := intPair hNc β p r
  have hps := intPair hNc β p s
  have hqr := intPair hNc β q r
  have hqs := intPair hNc β q s
  have hA : Integrable (fun U => (plaqE Nc p U * plaqE Nc r U - plaqE Nc p U * plaqE Nc s U)
        * (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).boltz β U)
      ((wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).vol
        (probHaar (MassGap.SUN.SU Nc))) := by
    have he : (fun U => (plaqE Nc p U * plaqE Nc r U - plaqE Nc p U * plaqE Nc s U)
          * (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).boltz β U)
        = fun U => (plaqE Nc p U * plaqE Nc r U)
              * (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).boltz β U
            - (plaqE Nc p U * plaqE Nc s U)
              * (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).boltz β U :=
      funext fun U => by ring
    rw [he]
    exact hpr.sub hps
  have hB : Integrable (fun U => (plaqE Nc q U * plaqE Nc r U - plaqE Nc q U * plaqE Nc s U)
        * (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).boltz β U)
      ((wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).vol
        (probHaar (MassGap.SUN.SU Nc))) := by
    have he : (fun U => (plaqE Nc q U * plaqE Nc r U - plaqE Nc q U * plaqE Nc s U)
          * (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).boltz β U)
        = fun U => (plaqE Nc q U * plaqE Nc r U)
              * (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).boltz β U
            - (plaqE Nc q U * plaqE Nc s U)
              * (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).boltz β U :=
      funext fun U => by ring
    rw [he]
    exact hqr.sub hqs
  have hsplit : ∀ U, ((plaqE Nc p U - plaqE Nc q U) * (plaqE Nc r U - plaqE Nc s U))
        * (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).boltz β U
      = (plaqE Nc p U * plaqE Nc r U - plaqE Nc p U * plaqE Nc s U)
          * (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).boltz β U
        - (plaqE Nc q U * plaqE Nc r U - plaqE Nc q U * plaqE Nc s U)
          * (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).boltz β U :=
    fun U => by ring
  have hsplitA : ∀ U, (plaqE Nc p U * plaqE Nc r U - plaqE Nc p U * plaqE Nc s U)
        * (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).boltz β U
      = (plaqE Nc p U * plaqE Nc r U)
          * (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).boltz β U
        - (plaqE Nc p U * plaqE Nc s U)
          * (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).boltz β U :=
    fun U => by ring
  have hsplitB : ∀ U, (plaqE Nc q U * plaqE Nc r U - plaqE Nc q U * plaqE Nc s U)
        * (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).boltz β U
      = (plaqE Nc q U * plaqE Nc r U)
          * (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).boltz β U
        - (plaqE Nc q U * plaqE Nc s U)
          * (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).boltz β U :=
    fun U => by ring
  unfold EW System.expect System.corrNum
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit), integral_sub hA hB,
    integral_congr_ae (Filter.Eventually.of_forall hsplitA),
    integral_congr_ae (Filter.Eventually.of_forall hsplitB),
    integral_sub hpr hps, integral_sub hqr hqs]
  ring

/-! ## 3. The Clay geometry at extent four

DERIVED throughout this section: `4` is `WilsonBridge.corrClay`'s own dimension and the extent
`3 + 1` of the Clay aperture; `3` is `SU(3)`'s rank, also `corrClay`'s own; `(0, 1)` is the
plaquette's plane and `2` the lag axis, all three of them `corrClay`'s own choices. The lag arguments
`0, 1, 2, 3` are the four indices of `Fin 4`. No magnitude is chosen anywhere in this file. -/

/-- The `(0,1)` plaquette based at lag site `s` along the lag axis `2`, in the Clay geometry.

DERIVED: `(0,1)` is `corrClay`'s own plaquette plane, `2` its own lag axis, and `4` its dimension and
extent. -/
def pl (s : Fin 4) : Plaq 4 4 :=
  (((0 : Fin 4), (1 : Fin 4)), siteAtHyper (2 : Fin 4) s)

/-- Lag site `0` is the origin, which is the base plaquette `corrHyper` is written at.

DERIVED: `0` is the base lag site; the other numerals are `pl`'s, carried. -/
theorem pl_zero : pl 0 = (((0 : Fin 4), (1 : Fin 4)), (fun _ => 0 : Site 4 4)) := by
  have h : siteAtHyper (d := 4) (n := 4) (2 : Fin 4) 0 = (fun _ => 0 : Site 4 4) := by
    funext j
    by_cases hj : j = 2
    · subst hj
      simp [siteAtHyper]
    · simp [siteAtHyper, Function.update_of_ne hj]
  rw [pl, h]

/-- The plane misses the lag axis — the side condition every reflection identity above carries.

DERIVED: `0`, `1` and `2` are `corrClay`'s own plane and axis directions, carried. -/
theorem plane_ne : ((0 : Fin 4) ≠ 2) ∧ ((1 : Fin 4) ≠ 2) := by decide

/-- **THE TWO-TERM HALF-SPACE OBSERVABLE.** The difference of the plaquette energies at the two lag
sites `1` and `2` — the two sites of the positive half of the link reflection `θ₁`.

It is not centred at the mean and does not need to be: it already annihilates constants, which is
why the disconnected floor cancels in `pairing_eq_two_mul_gap` with no one-point function left over.

DERIVED: `1` and `2` are the two lag sites of the positive half, read off the reflection; `3` is
`SU(3)`. -/
noncomputable def gapObs (U : Link 4 4 → MassGap.SUN.SU 3) : ℝ :=
  plaqE 3 (pl 1) U - plaqE 3 (pl 2) U

/-- **THE HYPOTHESIS, NAMED.** Reflection positivity of the Wilson Gibbs state at the LINK
reflection `θ₁`, for the TWO-TERM observable `gapObs` supported on the positive half.

This is `ReflectPositive.PlaqReflPositive 3 2 1 β q` with the single plaquette observable `F_q − a`
replaced by `F₁ − F₂`. `OddLagSplit.plaqReflPositive_odd` is the one-term case at this very
reflection; `MassGap.LinkGram.pairReflPositive` proves this two-term case, at every `0 ≤ β`.

It is a hypothesis of this file, discharged in `MassGap.LinkGram`.

DERIVED: `0` is the sign asserted, which IS positive semidefiniteness and not a threshold; `2` is the
lag axis and `1` the reflection constant, the smallest odd one, whose planes fall between lag sites
`0,1` and `2,3`; `3` is `SU(3)`. -/
def PairReflPositive (β : ℝ) : Prop :=
  0 ≤ EW 3 β (fun U => gapObs (reflConf (2 : Fin 4) (1 : Fin 4) U) * gapObs U)

/-! ## 4. The identity -/

/-- **THE REFLECTED OBSERVABLE.** `θ₁` sends lag site `1` to `0` and lag site `2` to `3`, so the
mirror of `F₁ − F₂` is `F₀ − F₃`.

DERIVED: `1 − 1 = 0` and `1 − 2 = 3` in `Fin 4`; the numerals are lag indices. -/
theorem gapObs_refl (U : Link 4 4 → MassGap.SUN.SU 3) :
    gapObs (reflConf (2 : Fin 4) (1 : Fin 4) U) = plaqE 3 (pl 0) U - plaqE 3 (pl 3) U := by
  have e1 : (1 : Fin 4) - 1 = 0 := by decide
  have e2 : (1 : Fin 4) - 2 = 3 := by decide
  simp only [gapObs, pl, plaqE_siteAtHyper_reflConf 3 plane_ne.1 plane_ne.2, e1, e2]

/-- **THE REFLECTION `θ₃` FOLDS THE TWO MIXED TERMS ONTO THE TWO BASE TERMS.**
`θ₃` sends lag site `3 ↦ 0`, `2 ↦ 1`, `1 ↦ 2`, `0 ↦ 3`, and the Gibbs state is invariant under it
(`Reflect.expect_reflect_invariant`, which holds at EVERY reflection constant — measure preservation
and action invariance, neither of which reads the constant's parity). So `⟨F₃F₁⟩ = ⟨F₀F₂⟩` and
`⟨F₃F₂⟩ = ⟨F₀F₁⟩`, with no translation invariance of the two-point function used.

`θ₃` is a LINK reflection: `s ↦ 3 − s` has no fixed lag site, because `2s = 3` has no solution in
`Fin 4`. Only the invariance is used here, so that costs nothing; the site reflections at this extent
are the even constants `0` and `2`.

DERIVED: `3` is the reflection constant that carries lag site `3` to `0` and `2` to `1`, which is
what the two mixed terms need; the other numerals are lag indices. -/
theorem EW_pair_fold (β : ℝ) (s : Fin 4) :
    EW 3 β (fun U => plaqE 3 (pl 3) U * plaqE 3 (pl (3 - s)) U)
      = EW 3 β (fun U => plaqE 3 (pl 0) U * plaqE 3 (pl s) U) := by
  have h : EW 3 β (fun U => plaqE 3 (pl 0) (reflConf (2 : Fin 4) (3 : Fin 4) U)
        * plaqE 3 (pl s) (reflConf (2 : Fin 4) (3 : Fin 4) U))
      = EW 3 β (fun U => plaqE 3 (pl 0) U * plaqE 3 (pl s) U) :=
    Reflect.expect_reflect_invariant (n := 4) 3 (2 : Fin 4) (3 : Fin 4) β
      (fun U => plaqE 3 (pl 0) U * plaqE 3 (pl s) U)
  have e0 : (3 : Fin 4) - 0 = 3 := by decide
  have hpt : (fun U => plaqE 3 (pl 3) U * plaqE 3 (pl (3 - s)) U)
      = fun U => plaqE 3 (pl 0) (reflConf (2 : Fin 4) (3 : Fin 4) U)
        * plaqE 3 (pl s) (reflConf (2 : Fin 4) (3 : Fin 4) U) := by
    funext U
    simp only [pl, plaqE_siteAtHyper_reflConf 3 plane_ne.1 plane_ne.2, e0]
  exact (congrArg (EW 3 β) hpt).trans h

/-- **THE WILSON CORRELATION AS A TWO-POINT FUNCTION MINUS THE SQUARED MEAN.**
`ReflectPositive.corrHyper_unfold` with the displaced one-point function folded back onto the base
one by `ReflectPositive.EW_plaqE_lag`.

DERIVED: `3` is the Clay aperture on the left and `SU(3)`'s rank on the right; `0` is the base lag. -/
theorem wilsonCorrAt_eq (β : ℝ) (s : Fin 4) :
    MassGap.wilsonCorrAt 3 β s
      = EW 3 β (fun U => plaqE 3 (pl 0) U * plaqE 3 (pl s) U)
        - EW 3 β (plaqE 3 (pl 0)) * EW 3 β (plaqE 3 (pl 0)) := by
  have hu := ReflectPositive.corrHyper_unfold (d := 4) (n := 4) 3
    (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) β s
  have hm := ReflectPositive.EW_plaqE_lag (d := 4) (n := 4) 3 plane_ne.1 plane_ne.2 s β
  show MassGap.WilsonBridge.corrHyper (d := 4) 3 4 (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) β s = _
  rw [hu, hm, ← pl_zero]
  rfl

/-- **THE IDENTITY.** The reflection pairing of the two-term half-space observable with its own
mirror IS twice the gap the target asks for:

    ⟨θ₁(F₁ − F₂) · (F₁ − F₂)⟩ = 2·(ρ(1) − ρ(2)).

Every ingredient is proved: the reflection's action on lag sites (§1), linearity of the state on a
product of two differences (§2), the fold `EW_pair_fold`, and the unfolding `wilsonCorrAt_eq`. Note
what does NOT appear on the right: the one-point function. `F₁ − F₂` annihilates constants, so the
disconnected floor cancels between the four terms rather than being subtracted by hand.

DERIVED: `2` on the right is the number of terms the fold produces — the pairing counts each of the
two mixed products once — and is not a magnitude; `1` and `2` inside `wilsonCorrAt` are lag
indices. -/
theorem pairing_eq_two_mul_gap (β : ℝ) :
    EW 3 β (fun U => gapObs (reflConf (2 : Fin 4) (1 : Fin 4) U) * gapObs U)
      = 2 * (MassGap.wilsonCorrAt 3 β 1 - MassGap.wilsonCorrAt 3 β 2) := by
  have hobs : EW 3 β (fun U => gapObs (reflConf (2 : Fin 4) (1 : Fin 4) U) * gapObs U)
      = EW 3 β (fun U => (plaqE 3 (pl 0) U - plaqE 3 (pl 3) U)
        * (plaqE 3 (pl 1) U - plaqE 3 (pl 2) U)) :=
    congrArg (EW 3 β) (funext fun U => by rw [gapObs_refl, gapObs])
  have hexp := EW_diff_mul_diff (d := 4) (n := 4) (Nc := 3) (by norm_num) β
    (pl 0) (pl 3) (pl 1) (pl 2)
  have hf1 : EW 3 β (fun U => plaqE 3 (pl 3) U * plaqE 3 (pl 1) U)
      = EW 3 β (fun U => plaqE 3 (pl 0) U * plaqE 3 (pl 2) U) := by
    have h := EW_pair_fold β 2
    have he : (3 : Fin 4) - 2 = 1 := by decide
    rwa [he] at h
  have hf2 : EW 3 β (fun U => plaqE 3 (pl 3) U * plaqE 3 (pl 2) U)
      = EW 3 β (fun U => plaqE 3 (pl 0) U * plaqE 3 (pl 1) U) := by
    have h := EW_pair_fold β 1
    have he : (3 : Fin 4) - 1 = 2 := by decide
    rwa [he] at h
  rw [hobs, hexp, hf1, hf2, wilsonCorrAt_eq β 1, wilsonCorrAt_eq β 2]
  ring

/-! ## 5. What it buys, and what it does not -/

/-- **THE TARGET, FROM THE NAMED HYPOTHESIS.** `ρ(2) ≤ ρ(1)` at the Clay aperture, for every `β` at
which `PairReflPositive` holds — which `MassGap.LinkGram.pairReflPositive` shows is every `0 ≤ β`.

DERIVED: `3` is the Clay aperture; `1` and `2` are lag indices. -/
theorem lag_two_le_lag_one {β : ℝ} (h : PairReflPositive β) :
    MassGap.wilsonCorrAt 3 β 2 ≤ MassGap.wilsonCorrAt 3 β 1 := by
  have h0 : (0 : ℝ) ≤ EW 3 β (fun U => gapObs (reflConf (2 : Fin 4) (1 : Fin 4) U) * gapObs U) := h
  rw [pairing_eq_two_mul_gap] at h0
  linarith

/-- **AND THE CONVERSE — so the hypothesis is EXACT, not merely sufficient.**

`PairReflPositive β` holds if and only if `ρ(2) ≤ ρ(1)`. Read with
`SpectralFour.ordered_is_what_nonneg_lam_buys`, which identifies the same inequality with `λ ≥ 0`,
this says that at extent four positivity of the transfer spectrum and reflection positivity of this
one two-term half-space observable are the SAME statement about the Wilson measure — neither is an
estimate on the other.

DERIVED: `3` is the Clay aperture; `1` and `2` are lag indices. -/
theorem pairReflPositive_iff {β : ℝ} :
    PairReflPositive β ↔ MassGap.wilsonCorrAt 3 β 2 ≤ MassGap.wilsonCorrAt 3 β 1 := by
  constructor
  · exact lag_two_le_lag_one
  · intro h
    have h0 : (0 : ℝ) ≤ 2 * (MassGap.wilsonCorrAt 3 β 1 - MassGap.wilsonCorrAt 3 β 2) := by
      linarith
    show (0 : ℝ) ≤ EW 3 β (fun U => gapObs (reflConf (2 : Fin 4) (1 : Fin 4) U) * gapObs U)
    rw [pairing_eq_two_mul_gap]
    exact h0

/-- **THE ONE-TERM CASE IS NOT ENOUGH, AND HERE IS WHY.**

`ReflectPositive.PlaqReflPositive 3 2 1 β (pl 1)` — which `OddLagSplit.plaqReflPositive_odd` proves —
is the pairing of a SINGLE plaquette observable with its own mirror, and by
`ReflectPositive.corrHyper_eq_pairing` that pairing is `ρ(1)` itself. So the one-term instance at
this reflection delivers `0 ≤ ρ(1)` and nothing else: it is already a field of
`TailRatio.TripleFacts`, and `SpectralFour.tripleFacts_not_ordered` exhibits a triple satisfying
every field of `TripleFacts` at which `ρ(2) ≤ ρ(1)` fails.

The content of `PairReflPositive` is therefore entirely in the CROSS term `⟨F₀F₂⟩` — the one the
one-term pairing never produces, and the one `EW_diff_mul_diff` is stated to reach.

DERIVED: `1` is the reflection constant and the lag it produces; `0` is the base lag; `3` is
`SU(3)`'s rank and the Clay aperture. -/
theorem one_term_pairing_is_lag_one (β : ℝ) :
    MassGap.wilsonCorrAt 3 β 1
      = EW 3 β (fun U => (plaqE 3 (pl 0) U - EW 3 β (plaqE 3 (pl 0)))
        * (plaqE 3 (pl 0) (reflConf (2 : Fin 4) (1 : Fin 4) U)
          - EW 3 β (plaqE 3 (pl 0)))) := by
  rw [pl_zero]
  exact ReflectPositive.corrHyper_eq_pairing (d := 4) (n := 4) (Nc := 3) (by norm_num)
    plane_ne.1 plane_ne.2 β (1 : Fin 4)

/-- **`WilsonSpectral 3 β` FROM THIS HYPOTHESIS AND THE QUADRATIC.**

`SpectralFour.wilsonSpectral_of_representable` needs all four fields of `FourRepresentable`. Two are
proved (`TailRatio.triple_wilsonCorrAt`), `ρ(2) ≤ ρ(1)` is `lag_two_le_lag_one`, and the quadratic
`2ρ(1)² ≤ ρ(2)² + ρ(0)·ρ(2)` is carried as a hypothesis here, so this file's own contribution is
exactly one of the two. `MassGap.SlabQuadratic.wilson_quadratic` supplies the quadratic and
`MassGap.SlabQuadratic.wilsonSpectral` is the composite with no hypothesis left.

DERIVED: `3` is the Clay aperture, `0, 1, 2` are lag indices, `2` in `2ρ(1)²` is
`SpectralFour.FourRepresentable`'s own coefficient and the exponent is a square. -/
theorem wilsonSpectral_of_pair_and_quadratic {β : ℝ} (hβ : 0 ≤ β) (hpair : PairReflPositive β)
    (hquad : 2 * MassGap.wilsonCorrAt 3 β 1 ^ 2
      ≤ MassGap.wilsonCorrAt 3 β 2 ^ 2
        + MassGap.wilsonCorrAt 3 β 0 * MassGap.wilsonCorrAt 3 β 2) :
    MassGap.WilsonSpectral 3 β := by
  obtain ⟨h0, _, h2, _, _, _, _⟩ := MassGap.TailRatio.triple_wilsonCorrAt hβ
  exact MassGap.SpectralFour.wilsonSpectral_of_representable
    ⟨h0.le, h2, lag_two_le_lag_one hpair, hquad⟩

section Audit
#print axioms pl
#print axioms gapObs
#print axioms reflSite_siteAtHyper
#print axioms reflPlaq_siteAtHyper
#print axioms plaqE_siteAtHyper_reflConf
#print axioms EW_diff_mul_diff
#print axioms pl_zero
#print axioms plane_ne
#print axioms PairReflPositive
#print axioms gapObs_refl
#print axioms EW_pair_fold
#print axioms wilsonCorrAt_eq
#print axioms pairing_eq_two_mul_gap
#print axioms lag_two_le_lag_one
#print axioms pairReflPositive_iff
#print axioms one_term_pairing_is_lag_one
#print axioms wilsonSpectral_of_pair_and_quadratic
end Audit

end MassGap.LagOneDominates
