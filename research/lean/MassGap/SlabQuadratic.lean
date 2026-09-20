import Mathlib
import MassGap.ReflectionStrong
import MassGap.LinkGram

/-!
# MassGap.SlabQuadratic — the extent-four quadratic, from the slab Gram form

`SpectralFour.four_iff` leaves two inequalities open at the Clay aperture. `LinkGram` closes
`ρ(2) ≤ ρ(1)`. This file closes the other one,

    2·ρ(1)² ≤ ρ(2)² + ρ(0)·ρ(2),

as one instance of Cauchy–Schwarz in `ReflectionStrong.wilsonGibbsReflForm` — the `Transfer.ReflForm`
the tree already builds on the slab algebra `LogConvex.localObs (blkS τ a m) (blkR τ a m)`, whose
`form_nonneg` holds at EVERY REAL coupling.

## The two vectors

At `τ = 2`, `a = 0`, `m = 2`, `n = 4` the reflection constant is `a + a = 0`: the SITE reflection
`s ↦ −s`, whose two fixed lag sites are `0` and `2` and whose halves are the single sites `1` and
`3`. Write `F_s` for the centred `(0,1)`-plaquette energy at lag site `s`. Then

    x = F₁,     y = F₀ + F₂,

and the form's six entries are read off `ReflectPositive.EW_pair_sub_const` and the reflection's
action `s ↦ −s`:

    ⟨x,x⟩ = ρ(2),   ⟨x,F₀⟩ = ⟨x,F₂⟩ = ρ(1),   ⟨F₀,F₀⟩ = ⟨F₂,F₂⟩ = ρ(0),   ⟨F₀,F₂⟩ = ρ(2),

so `⟨x,y⟩ = 2ρ(1)`, `⟨y,y⟩ = 2ρ(0) + 2ρ(2)`, and `⟨x,y⟩² ≤ ⟨x,x⟩⟨y,y⟩` reads
`4ρ(1)² ≤ 2ρ(2)(ρ(0) + ρ(2))`, which is the quadratic exactly.

## What had to be added

`ReflectionStrong.plaqObs_sub_const_mem` carries `hlv : lv a (q.2 τ) < m`, which admits lag sites `0`
and `1` but NOT site `2` — and `y` needs site `2`. That bound is stricter than the geometry: a
plaquette spanning two directions TRANSVERSE to the lag axis has all four of its links transverse and
at its own lag level (`ReflectPositive.bd_link_dir_ne`, `bd_link_tau_coord`), and
`ActionSplit.mem_blkS_union_blkR` puts a transverse link in `blkS ∪ blkR` at every level `≤ m`.
`transverse_plaq_links_le` and `cObs_mem` are that one step, and they are the only thing this file
adds to the slab machinery.

Composed with `LinkGram.wilson_lag_two_le_lag_one`, `wilsonSpectral` is
`Complete.WilsonSpectral 3 β` at every `0 ≤ β`, with no hypothesis left.

Build: `python research/code/lean_build.py build MassGap.SlabQuadratic`.
-/

namespace MassGap.SlabQuadratic

open MassGap MassGap.Reflect MassGap.ReflectPositive MassGap.LogConvex
open MassGap.ActionSplit MassGap.ReflectionStrong
open MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.WilsonReal MassGap.WilsonHypercubic MassGap.WilsonBridge
open MeasureTheory

/-! ## 1. A transverse plaquette at the FAR plane is still a slab observable

DERIVED throughout: `4` is the dimension and the extent, `3` is `SU(3)`'s rank and the Clay aperture,
`(0,1)` the plaquette plane and `2` the lag axis — all `WilsonBridge.corrClay`'s own. `m = 2` is half
the extent and `a = 0` the level origin. No magnitude is chosen. -/

/-- **EVERY LINK OF A TRANSVERSE PLAQUETTE AT LEVEL `≤ m` LIES IN `blkS ∪ blkR`.**

`ActionSplit.plaq_links_le` carries `lv < m` because it also covers plaquettes with one direction
ALONG the axis, whose second link steps to the next level. A plaquette spanning two directions
transverse to the axis does not step: all four of its links are transverse
(`ReflectPositive.bd_link_dir_ne`) and sit at its own lag coordinate
(`ReflectPositive.bd_link_tau_coord`), and `ActionSplit.mem_blkS_union_blkR` admits a transverse link
at every level `≤ m`. So the far plane `lv = m` is included.

DERIVED: `m` is the caller's half-extent; `≤ m` is `mem_blkS_union_blkR`'s own transverse condition,
read off rather than chosen. -/
theorem transverse_plaq_links_le {d n : ℕ} [NeZero n] {μ ν τ : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ)
    (a : Fin n) (m : ℕ) (x : Site d n) (hlv : lv a (x τ) ≤ m) :
    ∀ l ∈ (bd (((μ, ν), x) : Plaq d n)).map Prod.fst, l ∈ blkS τ a m ∪ blkR τ a m := by
  intro l hl
  have hdir : l.1 ≠ τ := MassGap.ReflectPositive.bd_link_dir_ne hμ hν x l hl
  have hco : l.2 τ = x τ := MassGap.ReflectPositive.bd_link_tau_coord hμ hν x l hl
  rw [mem_blkS_union_blkR, if_neg hdir, hco]
  exact hlv

/-! ## 2. The Clay slab, its three vectors and its six entries -/

/-- The mean plaquette energy — the centring constant, the same at every lag site
(`ReflectPositive.EW_plaqE_lag`).

DERIVED: `3` is `SU(3)`'s rank; `0` is the base lag site. -/
noncomputable def mean (β : ℝ) : ℝ := EW 3 β (plaqE 3 (MassGap.LagOneDominates.pl 0))

/-- The centred plaquette energy at lag site `s`.

DERIVED: `3` is `SU(3)`'s rank and `4` the dimension and extent, both `corrClay`'s own; `s` is the
caller's lag site. -/
noncomputable def cObs (β : ℝ) (s : Fin 4) : (Link 4 4 → MassGap.SUN.SU 3) → ℝ :=
  fun U => plaqE 3 (MassGap.LagOneDominates.pl s) U - mean β

/-- **THE ONE-POINT FUNCTION IS THE SAME AT EVERY LAG SITE.** `ReflectPositive.EW_plaqE_lag`, which
is reflection invariance of the Gibbs state, not translation invariance.

DERIVED: `3` is `SU(3)`'s rank; `p` is the caller's lag site. -/
theorem EW_plaqE_pl (β : ℝ) (p : Fin 4) :
    EW 3 β (plaqE 3 (MassGap.LagOneDominates.pl p)) = mean β := by
  have h := MassGap.ReflectPositive.EW_plaqE_lag (d := 4) (n := 4) 3
    MassGap.LagOneDominates.plane_ne.1 MassGap.LagOneDominates.plane_ne.2 p β
  rw [mean, MassGap.LagOneDominates.pl_zero]
  exact h

/-- **THE CENTRED OBSERVABLE AT LAG SITE `s ≤ 2` IS A SLAB OBSERVABLE.**

`ReflectionStrong.plaqObs_sub_const_mem` gives sites `0` and `1`; `transverse_plaq_links_le` adds the
far plane, site `2`. All three are needed: `y` is `F₀ + F₂`.

DERIVED: `2` is the half-extent `m`, so `s ≤ 2` is `mem_blkS_union_blkR`'s transverse condition at
this geometry, not a chosen cut. -/
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

/-- **THE SLAB REFLECTION FORM AT THE CLAY GEOMETRY.** `ReflectionStrong.wilsonGibbsReflForm` at
`τ = 2`, `a = 0`, `m = 2`, `n = 4` — reflection constant `a + a = 0`, the site reflection `s ↦ −s`.

DERIVED: `4 = 2 · 2` is the extent and its half; `0` is the level origin. -/
noncomputable def RF (β : ℝ) :
    MassGap.Transfer.ReflForm
      ↥(localObs (Ω := MassGap.SUN.SU 3)
        (blkS (2 : Fin 4) (0 : Fin 4) 2) (blkR (2 : Fin 4) (0 : Fin 4) 2)) :=
  wilsonGibbsReflForm (N := 3) (d := 4) (n := 4) (by norm_num) (2 : Fin 4) (0 : Fin 4) 2
    (by norm_num) (by norm_num) β

/-- **THE REFLECTION FOLDS A TWO-POINT FUNCTION.** `Reflect.expect_reflect_invariant` at constant
`c`, which sends lag site `s` to `c − s`; the general form of `LagOneDominates.EW_pair_fold`.

DERIVED: `3` is `SU(3)`'s rank, `4` the dimension and extent, `2` the lag axis — all
`corrClay`'s own. `c`, `s` and `t` are the caller's and no magnitude is chosen. -/
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

/-- **AN ENTRY OF THE GRAM MATRIX.** The form pairs `F_s` with `F_t` as the centred two-point
function at lag sites `−s` and `t`, because the reflection at constant `0` sends `s` to `−s`.

DERIVED: `0` is the reflection constant `a + a` at `a = 0`; `3` is `SU(3)`'s rank. -/
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

/-- `⟨F₁, F₁⟩ = ρ(2)` — the reflection carries lag site `1` to `3`, and `⟨F₃F₁⟩` folds onto `⟨F₀F₂⟩`.

DERIVED: the numerals are lag indices. -/
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

/-- `⟨F₁, F₀⟩ = ρ(1)` — `⟨F₃F₀⟩` folds onto `⟨F₀F₃⟩`, and `ρ(3) = ρ(1)`
(`SpectralFour.wilson_lag_three`).

DERIVED: the numerals are lag indices. -/
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

/-- `⟨F₁, F₂⟩ = ρ(1)` — `⟨F₃F₂⟩` folds onto `⟨F₀F₁⟩`.

DERIVED: the numerals are lag indices. -/
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

/-- `⟨F₀, F₀⟩ = ρ(0)` — lag site `0` is fixed by the reflection, so this is the plaquette-energy
variance.

DERIVED: the numerals are lag indices. -/
theorem entry_zero_zero (β : ℝ) :
    (RF β).form ⟨cObs β 0, cObs_mem β (by norm_num)⟩ ⟨cObs β 0, cObs_mem β (by norm_num)⟩
      = MassGap.wilsonCorrAt 3 β 0 := by
  rw [RF_entry β (by norm_num) (by norm_num)]
  have h00 : (0 : Fin 4) - 0 = 0 := by decide
  rw [h00, MassGap.LagOneDominates.wilsonCorrAt_eq β 0, mean]

/-- `⟨F₀, F₂⟩ = ρ(2)` — both lag sites are fixed by the reflection.

DERIVED: the numerals are lag indices. -/
theorem entry_zero_two (β : ℝ) :
    (RF β).form ⟨cObs β 0, cObs_mem β (by norm_num)⟩ ⟨cObs β 2, cObs_mem β (by norm_num)⟩
      = MassGap.wilsonCorrAt 3 β 2 := by
  rw [RF_entry β (by norm_num) (by norm_num)]
  have h00 : (0 : Fin 4) - 0 = 0 := by decide
  rw [h00, MassGap.LagOneDominates.wilsonCorrAt_eq β 2, mean]

/-- `⟨F₂, F₂⟩ = ρ(0)` — lag site `2` is the OTHER fixed site of the reflection, so this is again the
variance; `⟨F₂F₂⟩` folds onto `⟨F₀F₀⟩`.

DERIVED: the numerals are lag indices. -/
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

/-- **THE QUADRATIC, AT EVERY REAL COUPLING.**

    2·ρ(1)² ≤ ρ(2)² + ρ(0)·ρ(2)

is `Transfer.ReflForm.cauchy_schwarz` applied to `x = F₁` and `y = F₀ + F₂` in the slab algebra of
the site reflection at constant `0`. The form's `form_nonneg` — which is what Cauchy–Schwarz consumes
— is `ReflectionStrong.wilsonGibbsReflForm`'s, and carries NO sign condition on `β`.

This is `SpectralFour.FourRepresentable`'s fourth conjunct, which
`SpectralFour.tripleFacts_not_quadratic` shows does not follow from `TailRatio.TripleFacts`, and
which `SpectralFour.missing_inequalities_independent` shows does not follow from `ρ(2) ≤ ρ(1)`
either.

It is also not a consequence of the two facts now available beside it: `ρ(1)² ≤ ρ(0)ρ(2)` together
with `ρ(2) ≤ ρ(1)` gives only `2ρ(1)² ≤ 2ρ(0)ρ(2)`, and `ρ(0)ρ(2) ≤ ρ(2)²` is false in general.

DERIVED: `2` in `2ρ(1)²` is `FourRepresentable`'s own coefficient, and it arrives here as the number
of terms in `y = F₀ + F₂` — the two fixed lag sites of the reflection; the exponent is a square. `0`,
`1`, `2` are lag indices and `3` is the Clay aperture. -/
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

/-- **`Complete.WilsonSpectral 3 β`, AT EVERY NONNEGATIVE COUPLING, WITH NO HYPOTHESIS LEFT.**

All four conjuncts of `SpectralFour.FourRepresentable` now hold of the Wilson triple:

* `0 ≤ ρ(0)` and `0 ≤ ρ(2)` — `TailRatio.triple_wilsonCorrAt`;
* `ρ(2) ≤ ρ(1)` — `LinkGram.wilson_lag_two_le_lag_one`, link-reflection positivity for a two-term
  half-space observable;
* `2ρ(1)² ≤ ρ(2)² + ρ(0)ρ(2)` — `wilson_quadratic` above, Cauchy–Schwarz in the slab form.

`SpectralFour.wilsonSpectral_iff` makes those four together equivalent to `WilsonSpectral 3 β`, so
this is the whole statement. `0 ≤ β` is consumed only by the link-reflection half, and
`OddLagSplit.negctl_odd_discharge_needs_nonneg_coupling` is what stands behind it: an IFF saying the
SU(3) cross kernel that argument integrates is positive semidefinite exactly on `0 ≤ β`. That refutes
the ROUTE at negative coupling; it does not say `ρ(2) ≤ ρ(1)` fails there.

DERIVED: `3` is the Clay aperture; `0 ≤ β` is the cross kernel's own sign condition. -/
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
