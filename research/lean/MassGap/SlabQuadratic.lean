import Mathlib
import MassGap.ReflectionStrong
import MassGap.LinkGram

/-!
# MassGap.SlabQuadratic — the extent-four quadratic, from the slab Gram form

`wilson_quadratic` states

    2 * ρ(1)^2 ≤ ρ(2)^2 + ρ(0) * ρ(2),      ρ(d) = MassGap.wilsonCorrAt 3 β d

at every real `β`, as one instance of Cauchy–Schwarz in `ReflectionStrong.wilsonGibbsReflForm`, the
`Transfer.ReflForm` on the slab algebra `LogConvex.localObs (blkS τ a m) (blkR τ a m)`. That form's
`form_nonneg` carries no sign condition on the coupling, which is why `wilson_quadratic` does not
either.

## The two vectors and the six entries

`RF β` is the form at `τ = 2`, `a = 0`, `m = 2`, `n = 4`, where the reflection constant `a + a` is
`0`, so the reflection acts on lag sites by `s ↦ -s`. Its fixed lag sites are `0` and `2`, and the
two halves are the single sites `1` and `3`. Writing `F_s` for `cObs β s`, the centred
`(0,1)`-plaquette energy at lag site `s`, the vectors are

    x = F₁,     y = F₀ + F₂,

and `RF_entry` with the fold `EW_fold` gives the six entries as

    ⟨x,x⟩ = ρ(2),   ⟨x,F₀⟩ = ⟨x,F₂⟩ = ρ(1),   ⟨F₀,F₀⟩ = ⟨F₂,F₂⟩ = ρ(0),   ⟨F₀,F₂⟩ = ρ(2),

which are the theorems `entry_one_one` through `entry_two_two`. Hence `⟨x,y⟩ = 2ρ(1)` and
`⟨y,y⟩ = 2ρ(0) + 2ρ(2)`, and `⟨x,y⟩^2 ≤ ⟨x,x⟩⟨y,y⟩` reads `4ρ(1)^2 ≤ 2ρ(2)(ρ(0) + ρ(2))`, which is
the quadratic.

## Membership at the far plane

`ReflectionStrong.plaqObs_sub_const_mem` carries `hlv : lv a (q.2 τ) < m`, which admits lag sites `0`
and `1` but not site `2`, and `y` uses site `2`. `transverse_plaq_links_le` supplies the weaker
condition the geometry allows: a plaquette spanning two directions transverse to the lag axis has all
four links transverse (`ReflectPositive.bd_link_dir_ne`) and at its own lag coordinate
(`ReflectPositive.bd_link_tau_coord`), and `ActionSplit.mem_blkS_union_blkR` admits a transverse link
at every level `≤ m`, the far plane `lv = m` included. `cObs_mem` is that step applied to the centred
observable, and the two together are what this module adds to the slab machinery.

## What the final theorem needs

`wilsonSpectral` combines `wilson_quadratic` with `LinkGram.wilson_lag_two_le_lag_one` through
`LinkGram.wilsonSpectral_of_quadratic` to give `MassGap.WilsonSpectral 3 β` at every `0 ≤ β`. The
hypothesis `0 ≤ β` is consumed by the link-reflection half alone, not by `wilson_quadratic`.

DERIVED: `4` is the spacetime dimension and the extent; `3` is `SU(3)`'s rank and the Clay aperture,
whose lag type is `Fin (3 + 1)`; `2` is the lag axis, the half-extent `m`, the exponent in the
squares, and the term count in `y = F₀ + F₂`; `0` is the level origin `a`, the reflection constant
`a + a`, the contact lag, and the lower end of the coupling range; `1` is the other plaquette
direction and a lag index. No magnitude is chosen.

Build: `python research/code/lean_build.py build MassGap.SlabQuadratic`.
-/

namespace MassGap.SlabQuadratic

open MassGap MassGap.Reflect MassGap.ReflectPositive MassGap.LogConvex
open MassGap.ActionSplit MassGap.ReflectionStrong
open MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.WilsonReal MassGap.WilsonHypercubic MassGap.WilsonBridge
open MeasureTheory

/-! ## 1. A transverse plaquette at the far plane is still a slab observable

DERIVED throughout this module: `4` is the dimension and the extent, `3` is `SU(3)`'s rank and the
Clay aperture, `(0, 1)` is the plaquette plane and `2` the lag axis — all `WilsonBridge.corrClay`'s
own. `m = 2` is half the extent and `a = 0` the level origin. No magnitude is chosen. -/

/-- Every link of a plaquette spanning two directions transverse to the axis `τ`, at a site with
`lv a (x τ) ≤ m`, lies in `blkS τ a m ∪ blkR τ a m`. The hypotheses are `μ ≠ τ` and `ν ≠ τ`, so the
plaquette does not step along the axis: `ReflectPositive.bd_link_dir_ne` makes each boundary link
transverse and `bd_link_tau_coord` puts it at the plaquette's own lag coordinate, after which
`ActionSplit.mem_blkS_union_blkR` admits it at every level `≤ m`.

The condition is `≤ m` rather than `< m`, so the far plane `lv = m` is included.
`ActionSplit.plaq_links_le` carries `< m` because it also covers plaquettes with one direction along
the axis, whose second link steps to the next level.

DERIVED: no numeral appears in the statement; `m` is the caller's half-extent and `≤ m` is
`mem_blkS_union_blkR`'s own transverse condition. -/
theorem transverse_plaq_links_le {d n : ℕ} [NeZero n] {μ ν τ : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ)
    (a : Fin n) (m : ℕ) (x : Site d n) (hlv : lv a (x τ) ≤ m) :
    ∀ l ∈ (bd (((μ, ν), x) : Plaq d n)).map Prod.fst, l ∈ blkS τ a m ∪ blkR τ a m := by
  intro l hl
  have hdir : l.1 ≠ τ := MassGap.ReflectPositive.bd_link_dir_ne hμ hν x l hl
  have hco : l.2 τ = x τ := MassGap.ReflectPositive.bd_link_tau_coord hμ hν x l hl
  rw [mem_blkS_union_blkR, if_neg hdir, hco]
  exact hlv

/-! ## 2. The Clay slab, its three vectors and its six entries -/

/-- The centring constant: the Gibbs expectation `EW 3 β` of the `(0,1)`-plaquette energy at lag
site `0`. `EW_plaqE_pl` states that the same value is obtained at every lag site, so the choice of
site `0` here fixes no extra content.

DERIVED: `3` is `SU(3)`'s rank; `0` is the base lag site. -/
noncomputable def mean (β : ℝ) : ℝ := EW 3 β (plaqE 3 (MassGap.LagOneDominates.pl 0))

/-- The centred `(0,1)`-plaquette energy at lag site `s`, as a function of a link configuration:
`plaqE 3 (pl s) U - mean β`. Membership in the slab algebra is `cObs_mem`, not part of this
definition.

DERIVED: `3` is `SU(3)`'s rank and `4` the dimension and extent, both `corrClay`'s own; `s` is the
caller's lag site. -/
noncomputable def cObs (β : ℝ) (s : Fin 4) : (Link 4 4 → MassGap.SUN.SU 3) → ℝ :=
  fun U => plaqE 3 (MassGap.LagOneDominates.pl s) U - mean β

/-- `EW 3 β (plaqE 3 (pl p)) = mean β` at every lag site `p : Fin 4`: the one-point function does
not depend on the lag site. It is `ReflectPositive.EW_plaqE_lag`, which comes from reflection
invariance of the Gibbs state rather than from translation invariance.

DERIVED: `3` is `SU(3)`'s rank, `4` the extent the lag site ranges over; `p` is the caller's lag
site. -/
theorem EW_plaqE_pl (β : ℝ) (p : Fin 4) :
    EW 3 β (plaqE 3 (MassGap.LagOneDominates.pl p)) = mean β := by
  have h := MassGap.ReflectPositive.EW_plaqE_lag (d := 4) (n := 4) 3
    MassGap.LagOneDominates.plane_ne.1 MassGap.LagOneDominates.plane_ne.2 p β
  rw [mean, MassGap.LagOneDominates.pl_zero]
  exact h

/-- `cObs β s ∈ localObs (blkS 2 0 2) (blkR 2 0 2)` for every lag site `s` with `(s : ℕ) ≤ 2`. The
three `mem_localObs` obligations are discharged by measurability of `plaqE`, the bound
`|plaqE - mean β| ≤ 2 + |mean β|` from `plaqE_nonneg` and `plaqE_le_two`, and locality, which uses
`transverse_plaq_links_le` at `hlv` to see that the plaquette's links lie in the union.

The bound `s ≤ 2` admits all three sites `0`, `1`, `2` that the vectors `x = F₁` and `y = F₀ + F₂`
use; `ReflectionStrong.plaqObs_sub_const_mem` alone would give only `s < 2`.

DERIVED: `4` is the extent the lag site ranges over; `2` is the lag axis, the half-extent `m`, and
hence the bound `s ≤ 2`, which is `mem_blkS_union_blkR`'s transverse condition at this geometry
rather than a chosen cut; `0` is the level origin. -/
theorem cObs_mem (β : ℝ) {s : Fin 4} (hs : (s : ℕ) ≤ 2) :
    cObs β s ∈ localObs (blkS (2 : Fin 4) (0 : Fin 4) 2) (blkR (2 : Fin 4) (0 : Fin 4) 2) := by
  have hlv : lv (0 : Fin 4) ((MassGap.LagOneDominates.pl s).2 (2 : Fin 4)) ≤ 2 := by
    show lv (0 : Fin 4) (siteAtHyper (d := 4) (n := 4) (2 : Fin 4) s (2 : Fin 4)) ≤ 2
    simpa [lv, siteAtHyper] using hs
  refine mem_localObs.mpr ⟨?_, ⟨2 + |mean β|, fun U => ?_⟩, fun U V hS hR => ?_⟩
  · exact (measurable_plaqE _).sub measurable_const
  · have h1 : 0 ≤ plaqE 3 (MassGap.LagOneDominates.pl s) U :=
      plaqE_nonneg (by norm_num) _ U
    have h2 : plaqE 3 (MassGap.LagOneDominates.pl s) U ≤ 2 :=
      plaqE_le_two (by norm_num) _ U
    have h3 : -|mean β| ≤ mean β := neg_abs_le _
    have h4 : mean β ≤ |mean β| := le_abs_self _
    show |plaqE 3 (MassGap.LagOneDominates.pl s) U - mean β| ≤ 2 + |mean β|
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  · have hUV : ∀ l ∈ blkS (2 : Fin 4) (0 : Fin 4) 2 ∪ blkR (2 : Fin 4) (0 : Fin 4) 2,
        U l = V l := by
      intro l hl
      rcases Finset.mem_union.mp hl with h | h
      · exact hS l h
      · exact hR l h
    show wilsonDensity (wilsonHol (bd (d := 4) (n := 4))
          (MassGap.LagOneDominates.pl s) U) - mean β
        = wilsonDensity (wilsonHol (bd (d := 4) (n := 4))
          (MassGap.LagOneDominates.pl s) V) - mean β
    rw [MassGap.ReflectionPositivity.hol_congr_on_support (bd (d := 4) (n := 4))
      (MassGap.LagOneDominates.pl s) U V
      (fun l hl => hUV l (transverse_plaq_links_le
        MassGap.LagOneDominates.plane_ne.1 MassGap.LagOneDominates.plane_ne.2
        (0 : Fin 4) 2 _ hlv l hl))]

/-- The slab reflection form at the Clay geometry: `ReflectionStrong.wilsonGibbsReflForm` with
`N = 3`, `d = 4`, `n = 4`, axis `τ = 2`, level origin `a = 0` and half-extent `m = 2`. The
reflection constant is `a + a = 0`, so the induced action on lag sites is `s ↦ -s`.

Its `form_nonneg` field holds at every real `β`; no sign condition on the coupling enters here.

DERIVED: `3` is `SU(3)`'s rank; `4 = 2 * 2` is the extent and its half; `2` is also the lag axis;
`0` is the level origin. -/
noncomputable def RF (β : ℝ) :
    MassGap.Transfer.ReflForm
      ↥(localObs (Ω := MassGap.SUN.SU 3)
        (blkS (2 : Fin 4) (0 : Fin 4) 2) (blkR (2 : Fin 4) (0 : Fin 4) 2)) :=
  wilsonGibbsReflForm (N := 3) (d := 4) (n := 4) (by norm_num) (2 : Fin 4) (0 : Fin 4) 2
    (by norm_num) (by norm_num) β

/-- The two-point function is invariant under the lag reflection at any constant `c : Fin 4`:
`EW 3 β (plaqE(pl (c - s)) * plaqE(pl (c - t))) = EW 3 β (plaqE(pl s) * plaqE(pl t))`. It is
`Reflect.expect_reflect_invariant` together with
`LagOneDominates.plaqE_siteAtHyper_reflConf`, which identifies the reflected plaquette at site `s`
with the plaquette at site `c - s`.

`c`, `s` and `t` are all arguments; `LagOneDominates.EW_pair_fold` is the instance at a fixed
constant.

DERIVED: `3` is `SU(3)`'s rank, `4` the dimension and extent, `2` the lag axis — all `corrClay`'s
own. -/
theorem EW_fold (β : ℝ) (c s t : Fin 4) :
    EW 3 β (fun U => plaqE 3 (MassGap.LagOneDominates.pl (c - s)) U
        * plaqE 3 (MassGap.LagOneDominates.pl (c - t)) U)
      = EW 3 β (fun U => plaqE 3 (MassGap.LagOneDominates.pl s) U
        * plaqE 3 (MassGap.LagOneDominates.pl t) U) := by
  have h : EW 3 β (fun U => plaqE 3 (MassGap.LagOneDominates.pl s) (reflConf (2 : Fin 4) c U)
        * plaqE 3 (MassGap.LagOneDominates.pl t) (reflConf (2 : Fin 4) c U))
      = EW 3 β (fun U => plaqE 3 (MassGap.LagOneDominates.pl s) U
        * plaqE 3 (MassGap.LagOneDominates.pl t) U) :=
    Reflect.expect_reflect_invariant (n := 4) 3 (2 : Fin 4) c β
      (fun U => plaqE 3 (MassGap.LagOneDominates.pl s) U
        * plaqE 3 (MassGap.LagOneDominates.pl t) U)
  have hpt : (fun U => plaqE 3 (MassGap.LagOneDominates.pl (c - s)) U
        * plaqE 3 (MassGap.LagOneDominates.pl (c - t)) U)
      = fun U => plaqE 3 (MassGap.LagOneDominates.pl s) (reflConf (2 : Fin 4) c U)
        * plaqE 3 (MassGap.LagOneDominates.pl t) (reflConf (2 : Fin 4) c U) := by
    funext U
    simp only [MassGap.LagOneDominates.pl,
      MassGap.LagOneDominates.plaqE_siteAtHyper_reflConf 3
        MassGap.LagOneDominates.plane_ne.1 MassGap.LagOneDominates.plane_ne.2]
  exact (congrArg (EW 3 β) hpt).trans h

/-- A general entry of the Gram matrix: for lag sites `s`, `t` with `(s : ℕ) ≤ 2` and `(t : ℕ) ≤ 2`,
`(RF β).form ⟨cObs β s, _⟩ ⟨cObs β t, _⟩` equals the two-point function at sites `0 - s` and `t`
minus `mean β * mean β`. The reflection at constant `0` sends `s` to `-s`, which is where the first
argument acquires its sign; `ReflectPositive.EW_pair_sub_const` and `EW_plaqE_pl` expand the centring.

The entries `entry_one_one` through `entry_two_two` are the instances of this at the specific sites.

DERIVED: `4` is the extent the lag sites range over; `2` bounds them, being the half-extent; `0` is
the reflection constant `a + a` at `a = 0`; `3` is `SU(3)`'s rank. -/
theorem RF_entry (β : ℝ) {s t : Fin 4} (hs : (s : ℕ) ≤ 2) (ht : (t : ℕ) ≤ 2) :
    (RF β).form ⟨cObs β s, cObs_mem β hs⟩ ⟨cObs β t, cObs_mem β ht⟩
      = EW 3 β (fun U => plaqE 3 (MassGap.LagOneDominates.pl (0 - s)) U
          * plaqE 3 (MassGap.LagOneDominates.pl t) U) - mean β * mean β := by
  have hc : ((0 : Fin 4) + 0) = (0 : Fin 4) := by decide
  have hstep : (RF β).form ⟨cObs β s, cObs_mem β hs⟩ ⟨cObs β t, cObs_mem β ht⟩
      = EW 3 β (fun U => (plaqE 3 (MassGap.LagOneDominates.pl (0 - s)) U - mean β)
          * (plaqE 3 (MassGap.LagOneDominates.pl t) U - mean β)) := by
    show MassGap.Transfer.reflForm 3 (2 : Fin 4) ((0 : Fin 4) + 0) β (cObs β s) (cObs β t) = _
    rw [hc]
    refine congrArg (EW 3 β) (funext fun U => ?_)
    show (plaqE 3 (MassGap.LagOneDominates.pl s) (reflConf (2 : Fin 4) (0 : Fin 4) U) - mean β)
        * (plaqE 3 (MassGap.LagOneDominates.pl t) U - mean β) = _
    simp only [MassGap.LagOneDominates.pl,
      MassGap.LagOneDominates.plaqE_siteAtHyper_reflConf 3
        MassGap.LagOneDominates.plane_ne.1 MassGap.LagOneDominates.plane_ne.2]
  rw [hstep, MassGap.ReflectPositive.EW_pair_sub_const (d := 4) (n := 4) (Nc := 3) (by norm_num)
    β (MassGap.LagOneDominates.pl (0 - s)) (MassGap.LagOneDominates.pl t) (mean β),
    EW_plaqE_pl, EW_plaqE_pl]
  ring

/-! ## 3. The six entries, in the correlation's own terms -/

/-- `⟨F₁, F₁⟩ = wilsonCorrAt 3 β 2`. The reflection carries lag site `1` to `3`, and `EW_fold` at
constant `3` folds `⟨F₃ F₁⟩` onto `⟨F₀ F₂⟩`, which `LagOneDominates.wilsonCorrAt_eq` identifies with
the correlation at lag `2`.

DERIVED: `3` is the Clay aperture; the remaining numerals `1`, `2` are lag indices. -/
theorem entry_one_one (β : ℝ) :
    (RF β).form ⟨cObs β 1, cObs_mem β (by norm_num)⟩ ⟨cObs β 1, cObs_mem β (by norm_num)⟩
      = MassGap.wilsonCorrAt 3 β 2 := by
  rw [RF_entry β (by norm_num) (by norm_num)]
  have h01 : (0 : Fin 4) - 1 = 3 := by decide
  have hfold := EW_fold β 3 0 2
  have e1 : (3 : Fin 4) - 0 = 3 := by decide
  have e2 : (3 : Fin 4) - 2 = 1 := by decide
  rw [e1, e2] at hfold
  rw [h01, hfold, MassGap.LagOneDominates.wilsonCorrAt_eq β 2, mean]

/-- `⟨F₁, F₀⟩ = wilsonCorrAt 3 β 1`. `⟨F₃ F₀⟩` folds onto `⟨F₀ F₃⟩`, which is the correlation at lag
`3`, and `SpectralFour.wilson_lag_three` gives `ρ(3) = ρ(1)` at extent four.

DERIVED: the first `3` is the Clay aperture; the remaining numerals `0`, `1`, `3` are lag
indices. -/
theorem entry_one_zero (β : ℝ) :
    (RF β).form ⟨cObs β 1, cObs_mem β (by norm_num)⟩ ⟨cObs β 0, cObs_mem β (by norm_num)⟩
      = MassGap.wilsonCorrAt 3 β 1 := by
  rw [RF_entry β (by norm_num) (by norm_num)]
  have h01 : (0 : Fin 4) - 1 = 3 := by decide
  have hfold := EW_fold β 3 0 3
  have e1 : (3 : Fin 4) - 0 = 3 := by decide
  have e2 : (3 : Fin 4) - 3 = 0 := by decide
  rw [e1, e2] at hfold
  rw [h01, hfold, ← MassGap.SpectralFour.wilson_lag_three β,
    MassGap.LagOneDominates.wilsonCorrAt_eq β 3, mean]

/-- `⟨F₁, F₂⟩ = wilsonCorrAt 3 β 1`. `⟨F₃ F₂⟩` folds onto `⟨F₀ F₁⟩` under `EW_fold` at constant `3`,
which is the correlation at lag `1`.

DERIVED: `3` is the Clay aperture; the remaining numerals `1`, `2` are lag indices. -/
theorem entry_one_two (β : ℝ) :
    (RF β).form ⟨cObs β 1, cObs_mem β (by norm_num)⟩ ⟨cObs β 2, cObs_mem β (by norm_num)⟩
      = MassGap.wilsonCorrAt 3 β 1 := by
  rw [RF_entry β (by norm_num) (by norm_num)]
  have h01 : (0 : Fin 4) - 1 = 3 := by decide
  have hfold := EW_fold β 3 0 1
  have e1 : (3 : Fin 4) - 0 = 3 := by decide
  have e2 : (3 : Fin 4) - 1 = 2 := by decide
  rw [e1, e2] at hfold
  rw [h01, hfold, MassGap.LagOneDominates.wilsonCorrAt_eq β 1, mean]

/-- `⟨F₀, F₀⟩ = wilsonCorrAt 3 β 0`. Lag site `0` is fixed by the reflection, so `0 - 0 = 0` and no
fold is needed; the entry is the centred plaquette-energy variance, which is the correlation at lag
`0`.

DERIVED: `3` is the Clay aperture; the remaining `0`s are lag indices. -/
theorem entry_zero_zero (β : ℝ) :
    (RF β).form ⟨cObs β 0, cObs_mem β (by norm_num)⟩ ⟨cObs β 0, cObs_mem β (by norm_num)⟩
      = MassGap.wilsonCorrAt 3 β 0 := by
  rw [RF_entry β (by norm_num) (by norm_num)]
  have h00 : (0 : Fin 4) - 0 = 0 := by decide
  rw [h00, MassGap.LagOneDominates.wilsonCorrAt_eq β 0, mean]

/-- `⟨F₀, F₂⟩ = wilsonCorrAt 3 β 2`. Lag site `0` is fixed by the reflection, so `0 - 0 = 0` and the
entry is the two-point function at sites `0` and `2`, the correlation at lag `2`.

DERIVED: `3` is the Clay aperture; the remaining numerals `0`, `2` are lag indices. -/
theorem entry_zero_two (β : ℝ) :
    (RF β).form ⟨cObs β 0, cObs_mem β (by norm_num)⟩ ⟨cObs β 2, cObs_mem β (by norm_num)⟩
      = MassGap.wilsonCorrAt 3 β 2 := by
  rw [RF_entry β (by norm_num) (by norm_num)]
  have h00 : (0 : Fin 4) - 0 = 0 := by decide
  rw [h00, MassGap.LagOneDominates.wilsonCorrAt_eq β 2, mean]

/-- `⟨F₂, F₂⟩ = wilsonCorrAt 3 β 0`. Site `2` is the second fixed site of the reflection, `0 - 2 = 2`
in `Fin 4`, and `EW_fold` at constant `2` folds `⟨F₂ F₂⟩` onto `⟨F₀ F₀⟩`, the correlation at lag `0`.

DERIVED: `3` is the Clay aperture; the remaining numerals `0`, `2` are lag indices. -/
theorem entry_two_two (β : ℝ) :
    (RF β).form ⟨cObs β 2, cObs_mem β (by norm_num)⟩ ⟨cObs β 2, cObs_mem β (by norm_num)⟩
      = MassGap.wilsonCorrAt 3 β 0 := by
  rw [RF_entry β (by norm_num) (by norm_num)]
  have h02 : (0 : Fin 4) - 2 = 2 := by decide
  have hfold := EW_fold β 2 0 0
  have e1 : (2 : Fin 4) - 0 = 2 := by decide
  rw [e1] at hfold
  rw [h02, hfold, MassGap.LagOneDominates.wilsonCorrAt_eq β 0, mean]

/-! ## 4. Cauchy–Schwarz, and the quadratic -/

/-- `2 * ρ(1)^2 ≤ ρ(2)^2 + ρ(0) * ρ(2)` at every real `β`, where `ρ(d) = wilsonCorrAt 3 β d`.

It is `Transfer.ReflForm.cauchy_schwarz` on `RF β` at `x = F₁` and `y = F₀ + F₂`. Bilinearity gives
`⟨x, y⟩ = 2ρ(1)` and `⟨y, y⟩ = 2ρ(0) + 2ρ(2)` from `entry_one_zero`, `entry_one_two`,
`entry_zero_zero`, `entry_zero_two` and `entry_two_two`, and `⟨x, x⟩ = ρ(2)` is `entry_one_one`; the
Cauchy–Schwarz inequality then reads `4ρ(1)^2 ≤ ρ(2)(2ρ(0) + 2ρ(2))`, which `nlinarith` rearranges.

No hypothesis on `β` is required: what Cauchy–Schwarz consumes is the `form_nonneg` field of
`ReflectionStrong.wilsonGibbsReflForm`, which holds at every real coupling.

This is the fourth conjunct of `SpectralFour.FourRepresentable`.
`SpectralFour.tripleFacts_not_quadratic` shows it does not follow from `TailRatio.TripleFacts`, and
`SpectralFour.missing_inequalities_independent` shows it does not follow from `ρ(2) ≤ ρ(1)`. It also
does not follow from `ρ(1)^2 ≤ ρ(0)ρ(2)` together with `ρ(2) ≤ ρ(1)`, which give only
`2ρ(1)^2 ≤ 2ρ(0)ρ(2)`, since `ρ(0)ρ(2) ≤ ρ(2)^2` does not hold in general.

DERIVED: the coefficient `2` is `FourRepresentable`'s own, arriving here as the number of terms in
`y = F₀ + F₂`, the two fixed lag sites of the reflection; the exponents `2` are squares; `0`, `1`
and `2` are lag indices; `3` is the Clay aperture. -/
theorem wilson_quadratic (β : ℝ) :
    2 * MassGap.wilsonCorrAt 3 β 1 ^ 2
      ≤ MassGap.wilsonCorrAt 3 β 2 ^ 2
        + MassGap.wilsonCorrAt 3 β 0 * MassGap.wilsonCorrAt 3 β 2 := by
  set x : ↥(localObs (Ω := MassGap.SUN.SU 3)
      (blkS (2 : Fin 4) (0 : Fin 4) 2) (blkR (2 : Fin 4) (0 : Fin 4) 2)) :=
    ⟨cObs β 1, cObs_mem β (by norm_num)⟩ with hx
  set y₀ : ↥(localObs (Ω := MassGap.SUN.SU 3)
      (blkS (2 : Fin 4) (0 : Fin 4) 2) (blkR (2 : Fin 4) (0 : Fin 4) 2)) :=
    ⟨cObs β 0, cObs_mem β (by norm_num)⟩ with hy0
  set y₂ : ↥(localObs (Ω := MassGap.SUN.SU 3)
      (blkS (2 : Fin 4) (0 : Fin 4) 2) (blkR (2 : Fin 4) (0 : Fin 4) 2)) :=
    ⟨cObs β 2, cObs_mem β (by norm_num)⟩ with hy2
  have hxy : (RF β).form x (y₀ + y₂)
      = 2 * MassGap.wilsonCorrAt 3 β 1 := by
    rw [(RF β).toPreForm.form_add_right x y₀ y₂, hx, hy0, hy2, entry_one_zero, entry_one_two]
    ring
  have hyy : (RF β).form (y₀ + y₂) (y₀ + y₂)
      = 2 * MassGap.wilsonCorrAt 3 β 0 + 2 * MassGap.wilsonCorrAt 3 β 2 := by
    rw [(RF β).toPreForm.form_add_self y₀ y₂, hy0, hy2, entry_zero_zero, entry_zero_two,
      entry_two_two]
    ring
  have hxx : (RF β).form x x = MassGap.wilsonCorrAt 3 β 2 := by
    rw [hx, entry_one_one]
  have hcs := (RF β).cauchy_schwarz x (y₀ + y₂)
  rw [hxy, hxx, hyy] at hcs
  nlinarith [hcs]

/-- `MassGap.WilsonSpectral 3 β` at every `β` with `0 ≤ β`. It is
`LinkGram.wilsonSpectral_of_quadratic` applied to `hβ` and `wilson_quadratic β`.

The four conjuncts of `SpectralFour.FourRepresentable` that `SpectralFour.wilsonSpectral_iff`
identifies with `WilsonSpectral 3 β` are supplied as follows: `0 ≤ ρ(0)` and `0 ≤ ρ(2)` by
`TailRatio.triple_wilsonCorrAt`; `ρ(2) ≤ ρ(1)` by `LinkGram.wilson_lag_two_le_lag_one`, from
link-reflection positivity for a two-term half-space observable; and
`2ρ(1)^2 ≤ ρ(2)^2 + ρ(0)ρ(2)` by `wilson_quadratic`.

The hypothesis `0 ≤ β` is consumed only by the link-reflection conjunct.
`OddLagSplit.negctl_odd_discharge_needs_nonneg_coupling` is an iff stating that the `SU(3)` cross
kernel that argument integrates is positive semidefinite exactly on `0 ≤ β`, so that conjunct's
proof is unavailable at negative coupling; it makes no claim about `ρ(2) ≤ ρ(1)` there.

DERIVED: `3` is the Clay aperture; `0` is the lower end of the coupling range, the cross kernel's
own sign condition. -/
theorem wilsonSpectral {β : ℝ} (hβ : 0 ≤ β) : MassGap.WilsonSpectral 3 β :=
  MassGap.LinkGram.wilsonSpectral_of_quadratic hβ (wilson_quadratic β)

section Audit
#print axioms transverse_plaq_links_le
#print axioms mean
#print axioms cObs
#print axioms RF
#print axioms EW_plaqE_pl
#print axioms cObs_mem
#print axioms EW_fold
#print axioms RF_entry
#print axioms entry_one_one
#print axioms entry_one_zero
#print axioms entry_one_two
#print axioms entry_zero_zero
#print axioms entry_zero_two
#print axioms entry_two_two
#print axioms wilson_quadratic
#print axioms wilsonSpectral
end Audit

end MassGap.SlabQuadratic
