import Mathlib
import MassGap.ReflectPositive
import MassGap.SpectralFour

/-!
# MassGap.LagOneDominates — `ρ(2) ≤ ρ(1)` as a reflection-positivity statement

At extent four, `SpectralFour.four_iff` reduces `Complete.WilsonSpectral 3 β` to four inequalities on
the triple `(ρ(0), ρ(1), ρ(2))`. This module identifies one of them, `ρ(2) ≤ ρ(1)`, with the
positivity of one reflection pairing, and proves the identification as an equivalence.

## The identity

`pl s` is the `(0,1)` plaquette based at lag site `s` along the lag axis `2`, and `plaqE 3 (pl s)` is
its energy observable; write `F_s` for the latter. `Reflect.reflConf 2 c` acts on lag sites by
`s ↦ c - s` (`plaqE_siteAtHyper_reflConf`). The reflection taken is the one at constant `1`, whose
planes fall between lag sites `0,1` and between `2,3`, so it fixes no lag site and its positive half
is `{1, 2}`.

`gapObs` is the two-term observable `F₁ - F₂`, supported on that half. Then

    θ₁ gapObs = F₀ - F₃,
    ⟨θ₁ gapObs · gapObs⟩ = ⟨F₀F₁⟩ - ⟨F₀F₂⟩ - ⟨F₃F₁⟩ + ⟨F₃F₂⟩ = 2 (ρ(1) - ρ(2)).

`gapObs_refl` is the first line. `EW_diff_mul_diff` expands the product, `EW_pair_fold` folds the two
mixed terms onto the first two using invariance of the Gibbs state under the reflection at constant
`3` (`Reflect.expect_reflect_invariant`, which holds at every constant), and `wilsonCorrAt_eq`
unfolds the correlation. `pairing_eq_two_mul_gap` is the assembled identity.

No translation invariance of the two-point function is used. The disconnected term `⟨F⟩²` cancels
between the four products because `gapObs` has zero total weight, so it does not appear on the right.

## The statements

* `PairReflPositive β` names the hypothesis `0 ≤ ⟨θ₁ gapObs · gapObs⟩`.
* `lag_two_le_lag_one` derives `ρ(2) ≤ ρ(1)` from it.
* `pairReflPositive_iff` is the equivalence, so the two are the same statement about the Wilson
  measure. Read alongside `SpectralFour.ordered_is_what_nonneg_lam_buys`, which identifies the same
  inequality with non-negativity of the transfer spectrum.
* `one_term_pairing_is_lag_one` records that the one-plaquette pairing at this reflection is `ρ(1)`
  itself, by `ReflectPositive.corrHyper_eq_pairing`. So the content of `PairReflPositive` is in the
  cross term `⟨F₀F₂⟩`, which the one-term pairing does not produce. `ρ(1) ≥ 0` alone is a field of
  `TailRatio.TripleFacts`, and `SpectralFour.tripleFacts_not_ordered` exhibits a triple satisfying
  every such field at which `ρ(2) ≤ ρ(1)` fails.
* `wilsonSpectral_of_pair_and_quadratic` composes `lag_two_le_lag_one` with the two fields
  `TailRatio.triple_wilsonCorrAt` proves and a quadratic taken as a hypothesis.

## Scope

`PairReflPositive` is a hypothesis throughout this file; `LinkGram.pairReflPositive` supplies it at
every `0 ≤ β`. `ReflectPositive.PlaqReflPositive Nc τ c β q` is the corresponding one-observable
pairing, proved by `OddLagSplit.plaqReflPositive_odd` at this same reflection, at every even extent
at least four and every `0 ≤ β`, with the plaquette's links required to lie in `OddLagSplit.oblkS`.

Everything below §3 is at the single geometry `d = 4`, `n = 4`, `Nc = 3`, plane `(0,1)`, lag axis `2`.
§1 and §2 are stated at general `d`, `n` and `Nc`.

Build: `python research/code/lean_build.py build MassGap.LagOneDominates`.
-/

namespace MassGap.LagOneDominates

open MassGap MassGap.Reflect MassGap.ReflectPositive
open MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.WilsonReal MassGap.WilsonHypercubic MassGap.WilsonBridge
open MeasureTheory

variable {d n Nc : ℕ}

/-! ## 1. The reflection acts on lag sites by `s ↦ c - s`

`ReflectPositive.reflPlaq_origin` and `ReflectPositive.plaqE_lag` state this at the origin, which is
what `ReflectPositive.corrHyper_eq_pairing` uses. The two-term observable of §3 needs it at a general
lag site, which is what the three lemmas here supply. -/

/-- `reflSite τ c (siteAtHyper τ s) = siteAtHyper τ (c - s)`: the reflection carries the lag site `s`
to the lag site `c - s`.

It fixes every coordinate but the `τ` one, where the subtraction is in `Fin n`. Stated at general
dimension `d`, extent `n` and axis `τ`.

DERIVED: the statement carries no numeral; `c`, `s`, `τ`, `d` and `n` are all parameters. -/
theorem reflSite_siteAtHyper [NeZero n] (τ : Fin d) (c s : Fin n) :
    reflSite τ c (siteAtHyper (d := d) (n := n) τ s) = siteAtHyper τ (c - s) := by
  funext j
  by_cases hj : j = τ
  · subst hj
    simp [reflSite, siteAtHyper]
  · simp [reflSite, siteAtHyper, Function.update_of_ne hj]

/-- `reflPlaq τ c ((μ, ν), siteAtHyper τ s) = ((μ, ν), siteAtHyper τ (c - s))`, when neither `μ` nor
`ν` is the reflection axis `τ`.

Under those hypotheses `reflPlaq` keeps the plane and moves only the corner, which
`reflSite_siteAtHyper` computes. The two conditions `μ ≠ τ` and `ν ≠ τ` are required — a plaquette
whose plane meets the axis takes a different branch.

DERIVED: the statement carries no numeral. -/
theorem reflPlaq_siteAtHyper [NeZero n] {μ ν τ : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ) (c s : Fin n) :
    reflPlaq τ c (((μ, ν), siteAtHyper τ s) : Plaq d n)
      = ((μ, ν), siteAtHyper τ (c - s)) := by
  simp only [reflPlaq, hμ, hν, if_false, reflSite_siteAtHyper]

/-- The plaquette energy at lag site `s`, evaluated on the reflected configuration, is the plaquette
energy at lag site `c - s` on the original: `plaqE Nc (pl_s) (reflConf τ c U) = plaqE Nc (pl_{c-s}) U`,
when the plane misses the axis.

`plaqE_reflConf` moves the reflection onto the plaquette and `reflPlaq_siteAtHyper` computes it.
`ReflectPositive.plaqE_lag` is the case `s = 0`. This is the only geometric input to the identity in
§4.

DERIVED: the statement carries no numeral. -/
theorem plaqE_siteAtHyper_reflConf (Nc : ℕ) [NeZero n] {μ ν τ : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ)
    (c s : Fin n) (U : Link d n → MassGap.SUN.SU Nc) :
    plaqE Nc (((μ, ν), siteAtHyper τ s) : Plaq d n) (reflConf τ c U)
      = plaqE Nc (((μ, ν), siteAtHyper τ (c - s)) : Plaq d n) U := by
  rw [plaqE_reflConf Nc τ c, reflPlaq_siteAtHyper hμ hν]

/-! ## 2. The Gibbs state on a product of two differences

`ReflectPositive.EW_pair_sub_const` expands `(F - a) * (G - a)` for two plaquette observables centred
at a constant. The two-term observable of §3 needs `(F - G) * (H - K)` for four plaquette
observables, a different combination, which `EW_diff_mul_diff` supplies. -/

/-- The product of two plaquette energies, times the Boltzmann weight, is integrable against the
product Haar measure, at every real `β` and every pair of plaquettes.

The bound passed to `wilsonSystem_mul_boltz_integrable` is the product of
`ReflectPositive.abs_plaqE_le_two`'s bound with itself. `Nc ≠ 0` is required so the gauge group is
inhabited.

DERIVED: `0` is the excluded gauge order in `hNc : Nc ≠ 0`, and is the only numeral in the statement;
the numeric bound is supplied in the proof term. -/
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

/-- `⟨(F_p - F_q)(F_r - F_s)⟩ = ⟨F_p F_r⟩ - ⟨F_p F_s⟩ - ⟨F_q F_r⟩ + ⟨F_q F_s⟩` for the Wilson Gibbs
state, at four arbitrary plaquettes.

The four integrability side conditions come from `intPair`, and the division by the partition
function is the same on both sides. No property of the plaquettes is used and they need not be
distinct; `β` is any real.

DERIVED: `0` is the excluded gauge order in `hNc : Nc ≠ 0`, and is the only numeral in the statement;
the four products are written out rather than indexed. -/
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

/-! ## 3. The geometry at extent four

Everything from here on is at one geometry: dimension `4`, extent `4`, gauge order `3`, plaquette
plane `(0, 1)` and lag axis `2` — the choices `WilsonBridge.corrClay` is written at. The lag
arguments `0, 1, 2, 3` are the four indices of `Fin 4`. -/

/-- The `(0, 1)` plaquette based at lag site `s` along the lag axis `2`, as a `Plaq 4 4`.

DERIVED: `0` and `1` are the plane's two directions and `2` the lag axis, the choices
`WilsonBridge.corrClay` is written at. `4` is both the dimension and the extent of the lattice those
choices sit in. -/
def pl (s : Fin 4) : Plaq 4 4 :=
  (((0 : Fin 4), (1 : Fin 4)), siteAtHyper (2 : Fin 4) s)

/-- `pl 0` is the `(0, 1)` plaquette at the origin — the base plaquette
`ReflectPositive.corrHyper` is written at.

The lag-site construction at `0` produces the constant-zero site, which is what the `siteAtHyper`
computation in the proof establishes.

DERIVED: `0` is the base lag site and the site's every coordinate, and also the plane's first
direction. `1` is the plane's second direction. `4` is the dimension and the extent, carried from
`pl`. -/
theorem pl_zero : pl 0 = (((0 : Fin 4), (1 : Fin 4)), (fun _ => 0 : Site 4 4)) := by
  have h : siteAtHyper (d := 4) (n := 4) (2 : Fin 4) 0 = (fun _ => 0 : Site 4 4) := by
    funext j
    by_cases hj : j = 2
    · subst hj
      simp [siteAtHyper]
    · simp [siteAtHyper, Function.update_of_ne hj]
  rw [pl, h]

/-- The plane's two directions are both distinct from the lag axis: `(0 : Fin 4) ≠ 2` and
`(1 : Fin 4) ≠ 2`.

This is the side condition `reflPlaq_siteAtHyper` and `plaqE_siteAtHyper_reflConf` carry, discharged
at this geometry by `decide`.

DERIVED: `0` and `1` are the plane's two directions, `2` is the lag axis, and `4` is the dimension
they are indices in. -/
theorem plane_ne : ((0 : Fin 4) ≠ 2) ∧ ((1 : Fin 4) ≠ 2) := by decide

/-- The difference of the plaquette energies at lag sites `1` and `2` — the two sites of the positive
half of the reflection at constant `1`.

It is not centred at its mean, and is not required to be: a difference already annihilates constants,
which is why `pairing_eq_two_mul_gap` has no one-point function on its right.

DERIVED: `4` is the dimension and the extent of the configuration type `Link 4 4 → SU 3`, and `3` is
the gauge order. The lag sites `1` and `2` are arguments to `pl` in the body. -/
noncomputable def gapObs (U : Link 4 4 → MassGap.SUN.SU 3) : ℝ :=
  plaqE 3 (pl 1) U - plaqE 3 (pl 2) U

/-- The `Prop` `0 ≤ ⟨gapObs ∘ reflConf 2 1 · gapObs⟩`: positivity of the reflection pairing of the
two-term observable with its own mirror, at the reflection along axis `2` with constant `1`.

This is the two-term counterpart of `ReflectPositive.PlaqReflPositive`, whose one-observable case at
the same reflection `OddLagSplit.plaqReflPositive_odd` proves. `LinkGram.pairReflPositive` supplies
this one at every `0 ≤ β`; within this file it is a hypothesis.

DERIVED: the statement carries no numeral — `PairReflPositive` takes only `β : ℝ`, and the axis,
constant and gauge order are fixed inside the body. -/
def PairReflPositive (β : ℝ) : Prop :=
  0 ≤ EW 3 β (fun U => gapObs (reflConf (2 : Fin 4) (1 : Fin 4) U) * gapObs U)

/-! ## 4. The identity -/

/-- `gapObs (reflConf 2 1 U) = plaqE 3 (pl 0) U - plaqE 3 (pl 3) U`: the mirror of `F₁ - F₂` under
the reflection at constant `1` is `F₀ - F₃`.

`plaqE_siteAtHyper_reflConf` at the two lag sites, with `1 - 1 = 0` and `1 - 2 = 3` computed in
`Fin 4`.

DERIVED: `1` is the reflection constant and the first lag site, `2` the lag axis and the second lag
site, `0` and `3` the two image lag sites, `4` the dimension and extent, `3` also the gauge order.
All are indices, none a magnitude. -/
theorem gapObs_refl (U : Link 4 4 → MassGap.SUN.SU 3) :
    gapObs (reflConf (2 : Fin 4) (1 : Fin 4) U) = plaqE 3 (pl 0) U - plaqE 3 (pl 3) U := by
  have e1 : (1 : Fin 4) - 1 = 0 := by decide
  have e2 : (1 : Fin 4) - 2 = 3 := by decide
  simp only [gapObs, pl, plaqE_siteAtHyper_reflConf 3 plane_ne.1 plane_ne.2, e1, e2]

/-- `⟨F₃ · F_{3-s}⟩ = ⟨F₀ · F_s⟩` at every lag `s`.

The reflection at constant `3` sends lag site `s` to `3 - s`, so it exchanges `3 ↦ 0` and `2 ↦ 1`,
and the Gibbs state is invariant under it by `Reflect.expect_reflect_invariant` — which holds at
every reflection constant, since its ingredients are measure preservation and action invariance and
neither reads the constant's parity.

Scope: only the invariance is used, not any positivity, so the constant's parity is immaterial here.
No translation invariance of the two-point function is used.

DERIVED: `3` is the reflection constant, carrying lag site `3` to `0` and `2` to `1`, and is also the
gauge order. `0` is the image lag site. `4` is the dimension and the extent. -/
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

/-- `wilsonCorrAt 3 β s = ⟨F₀ F_s⟩ - ⟨F₀⟩ ^ 2`, at every lag `s : Fin 4` and every real `β`.

`ReflectPositive.corrHyper_unfold` with the displaced one-point function folded back onto the base
one by `ReflectPositive.EW_plaqE_lag`, so the subtracted term is the base mean squared rather than a
product of two displaced means.

DERIVED: `3` is the aperture index of `wilsonCorrAt` on the left and the gauge order on the right.
`0` is the base lag site. `4` is the dimension, the extent, and the range of `s`. -/
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

/-- `⟨θ₁ gapObs · gapObs⟩ = 2 * (wilsonCorrAt 3 β 1 - wilsonCorrAt 3 β 2)`, at every real `β`.

`gapObs_refl` computes the mirror, `EW_diff_mul_diff` expands the product into four terms,
`EW_pair_fold` folds the two mixed terms onto the first two, and `wilsonCorrAt_eq` unfolds each
correlation.

The one-point function does not appear on the right: `gapObs` is a difference, so the disconnected
term cancels between the four products rather than being subtracted by hand.

DERIVED: `2` is the factor on the right, produced by the fold identifying each mixed product with one
of the base products; it is also the lag axis of the reflection and the second lag index. `1` is the
reflection constant and the first lag index. `3` is the gauge order and the aperture index of
`wilsonCorrAt`. `4` is the dimension and the extent. -/
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

/-! ## 5. Consequences of the identity -/

/-- `wilsonCorrAt 3 β 2 ≤ wilsonCorrAt 3 β 1` at any `β` for which `PairReflPositive β` holds.

`pairing_eq_two_mul_gap` turns the hypothesis into `0 ≤ 2 * (ρ(1) - ρ(2))`.
`LinkGram.pairReflPositive` supplies the hypothesis at every `0 ≤ β`; no sign condition on `β`
appears in this statement.

DERIVED: `3` is the aperture index of `wilsonCorrAt`; `1` and `2` are the two lag indices
compared. -/
theorem lag_two_le_lag_one {β : ℝ} (h : PairReflPositive β) :
    MassGap.wilsonCorrAt 3 β 2 ≤ MassGap.wilsonCorrAt 3 β 1 := by
  have h0 : (0 : ℝ) ≤ EW 3 β (fun U => gapObs (reflConf (2 : Fin 4) (1 : Fin 4) U) * gapObs U) := h
  rw [pairing_eq_two_mul_gap] at h0
  linarith

/-- `PairReflPositive β` holds exactly when `wilsonCorrAt 3 β 2 ≤ wilsonCorrAt 3 β 1`.

Both directions are `pairing_eq_two_mul_gap` read one way and the other, so the two are the same
statement about the Wilson measure rather than one bounding the other.
`SpectralFour.ordered_is_what_nonneg_lam_buys` identifies the same inequality with non-negativity of
the transfer spectrum at this extent.

DERIVED: `3` is the aperture index of `wilsonCorrAt`; `1` and `2` are the two lag indices. -/
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

/-- `wilsonCorrAt 3 β 1` equals the one-plaquette reflection pairing at the base plaquette:
`⟨(F₀ - ⟨F₀⟩) · (θ₁ F₀ - ⟨F₀⟩)⟩`.

`ReflectPositive.corrHyper_eq_pairing` at lag `1`, after rewriting `pl 0` as the origin plaquette.

Consequence for the one-term hypothesis: `ReflectPositive.PlaqReflPositive 3 2 1 β (pl 1)`, which
`OddLagSplit.plaqReflPositive_odd` proves, asserts `0 ≤ ρ(1)` and nothing more. That is already a
field of `TailRatio.TripleFacts`, and `SpectralFour.tripleFacts_not_ordered` exhibits a triple
satisfying every field of `TripleFacts` at which `ρ(2) ≤ ρ(1)` fails. The content of
`PairReflPositive` is in the cross term `⟨F₀F₂⟩`, which the one-term pairing does not produce and
`EW_diff_mul_diff` is stated to reach.

DERIVED: `1` is the reflection constant and the lag index, `0` the base lag site, `2` the lag axis,
`3` the gauge order and the aperture index, and `4` the dimension and the extent. -/
theorem one_term_pairing_is_lag_one (β : ℝ) :
    MassGap.wilsonCorrAt 3 β 1
      = EW 3 β (fun U => (plaqE 3 (pl 0) U - EW 3 β (plaqE 3 (pl 0)))
        * (plaqE 3 (pl 0) (reflConf (2 : Fin 4) (1 : Fin 4) U)
          - EW 3 β (plaqE 3 (pl 0)))) := by
  rw [pl_zero]
  exact ReflectPositive.corrHyper_eq_pairing (d := 4) (n := 4) (Nc := 3) (by norm_num)
    plane_ne.1 plane_ne.2 β (1 : Fin 4)

/-- `WilsonSpectral 3 β` from `0 ≤ β`, `PairReflPositive β`, and the quadratic
`2 * ρ(1) ^ 2 ≤ ρ(2) ^ 2 + ρ(0) * ρ(2)`.

`SpectralFour.wilsonSpectral_of_representable` takes four fields of `FourRepresentable`. Two come
from `TailRatio.triple_wilsonCorrAt`, the third is `lag_two_le_lag_one` applied to `hpair`, and the
fourth is `hquad`.

Scope: `hquad` is a hypothesis here. `SlabQuadratic.wilson_quadratic` supplies it and
`SlabQuadratic.wilsonSpectral` is the composite with neither hypothesis left.

DERIVED: `0` is the lower bound in `hβ : 0 ≤ β` and a lag index; `1` and `2` are lag indices; `2` is
also the coefficient and the exponent in `SpectralFour.FourRepresentable`'s quadratic field; `3` is
the aperture index of `wilsonCorrAt` and of `WilsonSpectral`. -/
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
