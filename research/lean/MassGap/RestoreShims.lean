import Mathlib
import MassGap.HeatBath
import MassGap.HeatBathErgodic
import MassGap.KnabeCriterion
import MassGap.HeatBathGapDecay
import MassGap.LocalGauge

noncomputable section

/-!
# MassGap.RestoreShims — heat-bath conditional expectations and the ergodic limit of the lazy heat bath

Its declarations keep the namespaces `HeatBath` and `HeatBathErgodic`; they sit in this module because they import
`KnabeCriterion`, `HeatBathGapDecay` and `LocalGauge`, which those modules do not.

`HeatBath.heatLift β M l` lifts the heat bath at the torus link `l` to the `ℤ⁴` observables. This
module makes it a linear map of `KnabeCriterion.periodicGaugeInvSubmodule M` (namespace `HeatBath`) and
proves the ergodic limit of the lazy heat bath from a Poincaré inequality (namespace `HeatBathErgodic`):

1. `heatLift` keeps periodic gauge invariance (`heatLift_mem`), through `pullback_gaugeTransform`,
   `restrictConf_igauge` and the two-sided invariance of Haar measure (`heatAvg_gauge`).
2. `torusCondExp β M l` is `heatLift β M l` as a linear map of `periodicGaugeInvSubmodule M`. At
   `M = 2j + 1` it is `torusForm`-self-adjoint (`torusCondExp_selfAdj`), idempotent
   (`torusCondExp_idem`), its values do not read `l` (`torusCondExp_readsNot`), it keeps the torus
   reading of every observable not reading `l` (`torusCondExp_keeps`), and two of them at links sharing
   no plaquette commute (`torusCondExp_comm`). These are the analytic fields of
   `KnabeCriterion.WilsonHeatBath`; `MassGap.BoxPatch` supplies the patch data and builds the structure.
3. `RestoreShims.ergodicLimit_of_poincare`: on a patch system with a unit vector `u`
   (`B(u, u) = 1`, `B(Hv, u) = 0`) and a Poincaré inequality `B(v, v) − B(v, u)² ≤ C B(Hv, v)`, the
   lazy heat bath at `K = |ι| + 1` has `B(Tᴹ f, g) → B(f, u) B(g, u)`. The variance of `Tᴹ f`
   contracts by `1 − (K(C + 1))⁻¹` per step (`Tstep_form`), and `HeatBathErgodic.tendsto_of_sq_le`
   turns the geometric bound into the limit.
-/

namespace MassGap.HeatBath

open MeasureTheory
open MassGap.LatticeGauge
open MassGap.WilsonLattice (wilsonSystem wilsonHol)
open MassGap.WilsonAction (wilsonDensity)
open MassGap.CompactGauge (probHaar)
open MassGap.SUN (SU)
open MassGap.KnabeCriterion
open MassGap.PeriodicState (torusObs torusState)
open MassGap.InfiniteLattice (siteMod linkMod pullback finMod)

section Torus

variable {N : ℕ}

/-- **The pullback intertwines the gauge actions**: a torus gauge transformation pulled back is the
`ℤ⁴` gauge transformation by the periodic gauge function (`InfiniteLattice.siteMod_ishift`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem pullback_gaugeTransform (M : ℕ) (g : WilsonHypercubic.Site 4 (M + 1) → SU N)
    (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    pullback M (LocalGauge.gaugeTransform g W)
      = GaugeInvariantAlgebra.igaugeTransform (fun x => g (siteMod M x)) (pullback M W) := by
  funext l
  show g (siteMod M l.2) * W (linkMod M l) * (g (WilsonHypercubic.shift l.1 (siteMod M l.2)))⁻¹
    = g (siteMod M l.2) * W (linkMod M l)
      * (g (siteMod M (InfiniteLattice.ishift l.1 l.2)))⁻¹
  rw [InfiniteLattice.siteMod_ishift]

#print axioms pullback_gaugeTransform

/-- **The restriction intertwines the gauge actions**: restricting a `ℤ⁴` configuration transformed
by a periodic gauge function is transforming its restriction on the torus.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem restrictConf_igauge (M : ℕ) (g : WilsonHypercubic.Site 4 (M + 1) → SU N)
    (U : GibbsSpec.IConf (SU N)) :
    restrictConf M (GaugeInvariantAlgebra.igaugeTransform (fun x => g (siteMod M x)) U)
      = LocalGauge.gaugeTransform g (restrictConf M U) := by
  funext l
  show g (siteMod M (liftSite M l.2)) * U (liftLink M l)
      * (g (siteMod M (InfiniteLattice.ishift l.1 (liftSite M l.2))))⁻¹
    = g l.2 * U (liftLink M l) * (g (WilsonHypercubic.shift l.1 l.2))⁻¹
  rw [InfiniteLattice.siteMod_ishift, siteMod_liftSite]

#print axioms restrictConf_igauge

/-- The torus reading of a periodic gauge-invariant observable is invariant under every torus gauge
transformation.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem torusObs_gauge {M : ℕ} {F : C(GibbsSpec.IConf (SU N), ℝ)}
    (hF : F ∈ periodicGaugeInvSubmodule (N := N) M) (g : WilsonHypercubic.Site 4 (M + 1) → SU N)
    (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    torusObs M F (LocalGauge.gaugeTransform g W) = torusObs M F W := by
  have hF' : PeriodicGaugeInv M F := hF
  show F (pullback M (LocalGauge.gaugeTransform g W)) = F (pullback M W)
  rw [pullback_gaugeTransform]
  exact hF' g (pullback M W)

#print axioms torusObs_gauge

/-- **The heat bath keeps torus gauge invariance.** The gauge transformation at the updated link is
a two-sided translation of the integration variable (`integral_twoSided`), and the weight is gauge
invariant (`LocalGauge.boltz_gauge_invariant_local`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem heatAvg_gauge (β : ℝ) {M : ℕ} (l : WilsonHypercubic.Link 4 (M + 1))
    {φ : (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ}
    (hφ : ∀ (g : WilsonHypercubic.Site 4 (M + 1) → SU N)
      (W : WilsonHypercubic.Link 4 (M + 1) → SU N), φ (LocalGauge.gaugeTransform g W) = φ W)
    (g : WilsonHypercubic.Site 4 (M + 1) → SU N) (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    heatAvg (bdT M) β l φ (LocalGauge.gaugeTransform g W) = heatAvg (bdT M) β l φ W := by
  have hupd : ∀ h : SU N, Function.update (LocalGauge.gaugeTransform g W) l h
      = LocalGauge.gaugeTransform g
          (Function.update W l ((g l.2)⁻¹ * h * g (WilsonHypercubic.shift l.1 l.2))) := by
    intro h
    funext l'
    by_cases hl : l' = l
    · rw [hl, Function.update_self]
      show h = g l.2 * Function.update W l ((g l.2)⁻¹ * h * g (WilsonHypercubic.shift l.1 l.2)) l
        * (g (WilsonHypercubic.shift l.1 l.2))⁻¹
      rw [Function.update_self]
      group
    · rw [Function.update_of_ne hl]
      show g l'.2 * W l' * (g (WilsonHypercubic.shift l'.1 l'.2))⁻¹
        = g l'.2 * Function.update W l ((g l.2)⁻¹ * h * g (WilsonHypercubic.shift l.1 l.2)) l'
          * (g (WilsonHypercubic.shift l'.1 l'.2))⁻¹
      rw [Function.update_of_ne hl]
  have hwt : ∀ V : WilsonHypercubic.Link 4 (M + 1) → SU N,
      wt (bdT M) β (LocalGauge.gaugeTransform g V) = wt (bdT M) β V :=
    fun V => LocalGauge.boltz_gauge_invariant_local g β V
  unfold heatAvg heatNum heatPart
  simp only [hupd, hφ, hwt]
  rw [integral_twoSided (fun y => φ (Function.update W l y) * wt (bdT M) β (Function.update W l y)),
    integral_twoSided (fun y => wt (bdT M) β (Function.update W l y))]

#print axioms heatAvg_gauge


/-- **The lifted heat bath keeps periodic gauge invariance** (`restrictConf_igauge`,
`heatAvg_gauge`, `torusObs_gauge`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem heatLift_mem (β : ℝ) (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1))
    {F : C(GibbsSpec.IConf (SU N), ℝ)} (hF : F ∈ periodicGaugeInvSubmodule (N := N) M) :
    heatLift β M l F ∈ periodicGaugeInvSubmodule (N := N) M := by
  show ∀ (g : WilsonHypercubic.Site 4 (M + 1) → SU N) (U : GibbsSpec.IConf (SU N)),
    heatLift β M l F (GaugeInvariantAlgebra.igaugeTransform (fun x => g (siteMod M x)) U)
      = heatLift β M l F U
  intro g U
  show heatAvg (bdT M) β l (torusObs M F)
      (restrictConf M (GaugeInvariantAlgebra.igaugeTransform (fun x => g (siteMod M x)) U))
    = heatAvg (bdT M) β l (torusObs M F) (restrictConf M U)
  rw [restrictConf_igauge]
  exact heatAvg_gauge β l (fun g' W => torusObs_gauge hF g' W) g (restrictConf M U)

#print axioms heatLift_mem

/-- **The heat-bath conditional expectation at the torus link `l`** as a linear map of the
periodic gauge-invariant observables at extent `M + 1` (`heatAvg_add`, `heatAvg_const_mul`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
def torusCondExp (β : ℝ) (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1)) :
    ↥(periodicGaugeInvSubmodule (N := N) M) →ₗ[ℝ] ↥(periodicGaugeInvSubmodule (N := N) M) where
  toFun x := ⟨heatLift β M l (x : C(GibbsSpec.IConf (SU N), ℝ)), heatLift_mem β M l x.2⟩
  map_add' x y := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro U
    show heatAvg (bdT M) β l
        (torusObs M ((x : C(GibbsSpec.IConf (SU N), ℝ)) + (y : C(GibbsSpec.IConf (SU N), ℝ))))
        (restrictConf M U)
      = heatAvg (bdT M) β l (torusObs M (x : C(GibbsSpec.IConf (SU N), ℝ))) (restrictConf M U)
        + heatAvg (bdT M) β l (torusObs M (y : C(GibbsSpec.IConf (SU N), ℝ))) (restrictConf M U)
    exact heatAvg_add (bdT M) β l (continuous_torusObs M _) (continuous_torusObs M _)
      (restrictConf M U)
  map_smul' c x := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro U
    show heatAvg (bdT M) β l (torusObs M (c • (x : C(GibbsSpec.IConf (SU N), ℝ))))
        (restrictConf M U)
      = c * heatAvg (bdT M) β l (torusObs M (x : C(GibbsSpec.IConf (SU N), ℝ))) (restrictConf M U)
    exact heatAvg_const_mul (bdT M) β l c _ (restrictConf M U)

/-- The underlying observable of `torusCondExp β M l x` is `heatLift β M l x`, by definition.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem torusCondExp_coe (β : ℝ) (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1))
    (x : ↥(periodicGaugeInvSubmodule (N := N) M)) :
    ((torusCondExp β M l x : ↥(periodicGaugeInvSubmodule (N := N) M))
      : C(GibbsSpec.IConf (SU N), ℝ)) = heatLift β M l (x : C(GibbsSpec.IConf (SU N), ℝ)) := rfl

#print axioms torusCondExp_coe

/-- **Self-adjointness for `torusForm`** (detailed balance, `expect_heatAvg_mul`).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `0` is the excluded rank in `hN`. -/
theorem torusCondExp_selfAdj (hN : N ≠ 0) (β : ℝ) (j : ℕ)
    (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1))
    (x y : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) :
    torusForm hN β j (torusCondExp β (2 * j + 1) l x) y
      = torusForm hN β j x (torusCondExp β (2 * j + 1) l y) := by
  rw [torusForm_apply, torusForm_apply]
  show ReflectPositive.EW (d := 4) (n := 2 * j + 1 + 1) N β
      (fun W => torusObs (2 * j + 1) (heatLift β (2 * j + 1) l (x : C(GibbsSpec.IConf (SU N), ℝ))) W
        * torusObs (2 * j + 1) (y : C(GibbsSpec.IConf (SU N), ℝ)) W)
    = ReflectPositive.EW (d := 4) (n := 2 * j + 1 + 1) N β
      (fun W => torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) W
        * torusObs (2 * j + 1) (heatLift β (2 * j + 1) l (y : C(GibbsSpec.IConf (SU N), ℝ))) W)
  rw [torusObs_heatLift, torusObs_heatLift]
  exact expect_heatAvg_mul (bdT (2 * j + 1)) β l (continuous_torusObs _ _)
    (continuous_torusObs _ _)

#print axioms torusCondExp_selfAdj

/-- **Idempotence** (`heatAvg_of_readsNot`, `heatAvg_update`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem torusCondExp_idem (β : ℝ) (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1))
    (x : ↥(periodicGaugeInvSubmodule (N := N) M)) :
    torusCondExp β M l (torusCondExp β M l x) = torusCondExp β M l x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro U
  show heatAvg (bdT M) β l (torusObs M (heatLift β M l (x : C(GibbsSpec.IConf (SU N), ℝ))))
      (restrictConf M U)
    = heatAvg (bdT M) β l (torusObs M (x : C(GibbsSpec.IConf (SU N), ℝ))) (restrictConf M U)
  rw [torusObs_heatLift]
  exact heatAvg_of_readsNot (bdT M) β l (fun W g => heatAvg_update (bdT M) β l _ W g) _

#print axioms torusCondExp_idem

/-- **The values do not read `l`** (`heatAvg_update`).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent. -/
theorem torusCondExp_readsNot (β : ℝ) (j : ℕ) (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1))
    (x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) :
    ReadsNot j l ((torusCondExp β (2 * j + 1) l x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
      : C(GibbsSpec.IConf (SU N), ℝ)) := by
  unfold ReadsNot
  intro W g
  show torusObs (2 * j + 1) (heatLift β (2 * j + 1) l (x : C(GibbsSpec.IConf (SU N), ℝ)))
      (Function.update W l g)
    = torusObs (2 * j + 1) (heatLift β (2 * j + 1) l (x : C(GibbsSpec.IConf (SU N), ℝ))) W
  rw [torusObs_heatLift]
  exact heatAvg_update (bdT (2 * j + 1)) β l _ W g

#print axioms torusCondExp_readsNot

/-- **The torus reading of an observable not reading `l` is kept** (`heatAvg_of_readsNot`).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent. -/
theorem torusCondExp_keeps (β : ℝ) (j : ℕ) (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1))
    (x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
    (hx : ReadsNot j l (x : C(GibbsSpec.IConf (SU N), ℝ))) :
    torusObs (2 * j + 1)
        ((torusCondExp β (2 * j + 1) l x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
          : C(GibbsSpec.IConf (SU N), ℝ))
      = torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) := by
  show torusObs (2 * j + 1) (heatLift β (2 * j + 1) l (x : C(GibbsSpec.IConf (SU N), ℝ)))
    = torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ))
  rw [torusObs_heatLift]
  funext W
  exact heatAvg_of_readsNot (bdT (2 * j + 1)) β l hx W

#print axioms torusCondExp_keeps

/-- **Conditional expectations at links sharing no plaquette commute** (`heatAvg_comm`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem torusCondExp_comm (β : ℝ) (M : ℕ) {l l' : WilsonHypercubic.Link 4 (M + 1)} (hll : l ≠ l')
    (hs : ¬ SharePlaq (bdT M) l l') (x : ↥(periodicGaugeInvSubmodule (N := N) M)) :
    torusCondExp β M l (torusCondExp β M l' x) = torusCondExp β M l' (torusCondExp β M l x) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro U
  show heatAvg (bdT M) β l (torusObs M (heatLift β M l' (x : C(GibbsSpec.IConf (SU N), ℝ))))
      (restrictConf M U)
    = heatAvg (bdT M) β l' (torusObs M (heatLift β M l (x : C(GibbsSpec.IConf (SU N), ℝ))))
      (restrictConf M U)
  rw [torusObs_heatLift, torusObs_heatLift]
  exact heatAvg_comm (bdT M) β hll hs (continuous_torusObs M _) _

#print axioms torusCondExp_comm

end Torus

end MassGap.HeatBath

namespace MassGap.HeatBathErgodic

open MeasureTheory Filter
open MassGap.HeatBath MassGap.KnabeCriterion MassGap.HeatBathGapDecay
open MassGap.WilsonLattice (wilsonSystem)
open MassGap.WilsonAction (wilsonDensity)
open MassGap.CompactGauge (probHaar)
open MassGap.SUN (SU)

section Ergodic

/-- `B(Hv, v) = Σᵢ B(hᵢv, hᵢv)` on a patch system (`KnabeCriterion.form_proj_self`).

DERIVED: no numeral. -/
theorem form_H_eq_sum (S : PatchSystem) (v : S.E) :
    S.B (S.H v) v = ∑ i, S.B (S.h i v) (S.h i v) := by
  show S.B (totalOp S.h v) v = _
  rw [totalOp_apply, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => form_proj_self S.B (S.h i) (S.selfAdj i) (S.idem i) v)

#print axioms form_H_eq_sum

/-- **`H` pairs to zero with a vector every `hᵢ` sends to a null vector**: `B(Hv, u) = 0` when
`B(hᵢu, hᵢu) = 0` for every `i` (`HeatBathGapDecay.form_eq_zero_of_null`).

DERIVED: `0` is the null value. -/
theorem form_H_left_zero (S : PatchSystem) (u : S.E) (hu : ∀ i, S.B (S.h i u) (S.h i u) = 0)
    (v : S.E) : S.B (S.H v) u = 0 := by
  show S.B (totalOp S.h v) u = 0
  rw [totalOp_apply, map_sum, LinearMap.sum_apply]
  exact Finset.sum_eq_zero (fun i _ => by
    rw [S.selfAdj i v u]
    exact form_eq_zero_of_null S (hu i) v)

#print axioms form_H_left_zero

/-- **The ergodic limit from a Poincaré inequality.** On a patch system with a vector `u`,
`B(u, u) = 1`, `B(Hv, u) = 0` for every `v`, and `B(v, v) − B(v, u)² ≤ C B(Hv, v)` at some `C ≥ 0`:
for all `f`, `g` and `L = B(f, u) B(g, u)`, `ErgodicLimit S f g L`. The lazy step keeps `B(·, u)`
(`step_diff`) and lowers the variance `B(v, v) − B(v, u)²` by `K⁻¹ B(Hv, v)` (`Tstep_form`), so by
the factor `q = 1 − (K(C + 1))⁻¹`; Cauchy–Schwarz bounds
`(B(Tᴹf, g) − L)² ≤ qᴹ (B(f, f) − B(f, u)²) B(g, g)` (`form_sq_le_mul`), and `tendsto_of_sq_le`
closes it.

DERIVED: `0` is the sign of `C` and the null pairing; `1` is the normalisation of `u` and the shift
`C + 1`; `2` is the square. -/
theorem ergodicLimit_of_poincare (S : PatchSystem) (u : S.E) (hu : S.B u u = 1)
    (hHu : ∀ v, S.B (S.H v) u = 0) {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ v, S.B v v - S.B v u ^ 2 ≤ C * S.B (S.H v) v) (f g : S.E) {L : ℝ}
    (hL : S.B f u * S.B g u = L) : ErgodicLimit S f g L := by
  unfold ErgodicLimit
  rw [← hL]
  have hKc : ((Kc S : ℕ) : ℝ) = (Fintype.card S.ι : ℝ) + 1 := by
    unfold Kc
    exact Nat.cast_succ _
  have hK1 : (1 : ℝ) ≤ ((Kc S : ℕ) : ℝ) := by
    rw [hKc]
    have := Nat.cast_nonneg (α := ℝ) (Fintype.card S.ι)
    linarith
  have hK0 : (0 : ℝ) < ((Kc S : ℕ) : ℝ) := by linarith
  have hK : ∀ v : S.E, S.B (S.H v) (S.H v) ≤ ((Kc S : ℕ) : ℝ) * S.B (S.H v) v := by
    intro v
    rw [hKc]
    have h1 := H_form_le_card S v
    have h2 := S.H_form_nonneg v
    nlinarith
  have hmv : ∀ v : S.E, S.B (Tstep S ((Kc S : ℕ) : ℝ) v) u = S.B v u := by
    intro v
    have h := step_diff S ((Kc S : ℕ) : ℝ) v u
    rw [hHu, mul_zero, sub_eq_zero] at h
    exact h.symm
  have hmean : ∀ M, S.B (Titer S ((Kc S : ℕ) : ℝ) M f) u = S.B f u := by
    intro M
    induction M with
    | zero => rfl
    | succ M ih => rw [Titer_succ, hmv, ih]
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1 - (((Kc S : ℕ) : ℝ) * (C + 1))⁻¹ := ⟨_, rfl⟩
  have hKC : 1 ≤ ((Kc S : ℕ) : ℝ) * (C + 1) := by
    nlinarith [mul_nonneg hK0.le hC]
  have hinv0 : 0 < (((Kc S : ℕ) : ℝ) * (C + 1))⁻¹ := inv_pos.mpr (by linarith)
  have hinv1 : (((Kc S : ℕ) : ℝ) * (C + 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hKC
  have hq0 : 0 ≤ q := by
    rw [hq]
    linarith
  have hq1 : q < 1 := by
    rw [hq]
    linarith
  have hC1 : C + 1 ≠ 0 := (by linarith : (0 : ℝ) < C + 1).ne'
  have hstep : ∀ v : S.E,
      S.B (Tstep S ((Kc S : ℕ) : ℝ) v) (Tstep S ((Kc S : ℕ) : ℝ) v) - S.B v u ^ 2
        ≤ q * (S.B v v - S.B v u ^ 2) := by
    intro v
    have hT := Tstep_form S hK0 hK v
    have hPv := hP v
    have hD := S.H_form_nonneg v
    have h1 : S.B v v - S.B v u ^ 2 ≤ (C + 1) * S.B (S.H v) v := by nlinarith
    have h2 : (((Kc S : ℕ) : ℝ) * (C + 1))⁻¹ * (S.B v v - S.B v u ^ 2)
        ≤ (((Kc S : ℕ) : ℝ) * (C + 1))⁻¹ * ((C + 1) * S.B (S.H v) v) :=
      mul_le_mul_of_nonneg_left h1 hinv0.le
    have h3 : (((Kc S : ℕ) : ℝ) * (C + 1))⁻¹ * ((C + 1) * S.B (S.H v) v)
        = (((Kc S : ℕ) : ℝ))⁻¹ * S.B (S.H v) v := by
      rw [mul_inv]
      calc (((Kc S : ℕ) : ℝ))⁻¹ * (C + 1)⁻¹ * ((C + 1) * S.B (S.H v) v)
          = (((Kc S : ℕ) : ℝ))⁻¹ * ((C + 1)⁻¹ * (C + 1)) * S.B (S.H v) v := by ring
        _ = (((Kc S : ℕ) : ℝ))⁻¹ * S.B (S.H v) v := by rw [inv_mul_cancel₀ hC1, mul_one]
    rw [hq]
    linarith [hT, h2, h3]
  have hdecay : ∀ M : ℕ,
      S.B (Titer S ((Kc S : ℕ) : ℝ) M f) (Titer S ((Kc S : ℕ) : ℝ) M f) - S.B f u ^ 2
        ≤ q ^ M * (S.B f f - S.B f u ^ 2) := by
    intro M
    induction M with
    | zero => simp only [Titer_zero, pow_zero, one_mul, le_refl]
    | succ M ih =>
      rw [Titer_succ, pow_succ q M]
      have h := hstep (Titer S ((Kc S : ℕ) : ℝ) M f)
      rw [hmean M] at h
      calc S.B (Tstep S ((Kc S : ℕ) : ℝ) (Titer S ((Kc S : ℕ) : ℝ) M f))
            (Tstep S ((Kc S : ℕ) : ℝ) (Titer S ((Kc S : ℕ) : ℝ) M f)) - S.B f u ^ 2
          ≤ q * (S.B (Titer S ((Kc S : ℕ) : ℝ) M f) (Titer S ((Kc S : ℕ) : ℝ) M f)
              - S.B f u ^ 2) := h
        _ ≤ q * (q ^ M * (S.B f f - S.B f u ^ 2)) := mul_le_mul_of_nonneg_left ih hq0
        _ = q ^ M * q * (S.B f f - S.B f u ^ 2) := by ring
  have hbound : ∀ M : ℕ, (S.B (Titer S ((Kc S : ℕ) : ℝ) M f) g - S.B f u * S.B g u) ^ 2
      ≤ q ^ M * ((S.B f f - S.B f u ^ 2) * S.B g g) := by
    intro M
    obtain ⟨w, hw⟩ : ∃ w : S.E, w = Titer S ((Kc S : ℕ) : ℝ) M f - S.B f u • u := ⟨_, rfl⟩
    have e1 : S.B w g = S.B (Titer S ((Kc S : ℕ) : ℝ) M f) g - S.B f u * S.B g u := by
      rw [hw]
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      linear_combination (-(S.B f u)) * S.symm u g
    have e2 : S.B w w = S.B (Titer S ((Kc S : ℕ) : ℝ) M f) (Titer S ((Kc S : ℕ) : ℝ) M f)
        - S.B f u ^ 2 := by
      rw [hw]
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      linear_combination (-(S.B f u)) * S.symm u (Titer S ((Kc S : ℕ) : ℝ) M f)
        + (-2 * S.B f u) * hmean M + (S.B f u) ^ 2 * hu
    have hcs := form_sq_le_mul S.B S.symm S.nonneg w g
    rw [e1, e2] at hcs
    have hgg := S.nonneg g
    calc (S.B (Titer S ((Kc S : ℕ) : ℝ) M f) g - S.B f u * S.B g u) ^ 2
        ≤ (S.B (Titer S ((Kc S : ℕ) : ℝ) M f) (Titer S ((Kc S : ℕ) : ℝ) M f) - S.B f u ^ 2)
          * S.B g g := hcs
      _ ≤ (q ^ M * (S.B f f - S.B f u ^ 2)) * S.B g g :=
          mul_le_mul_of_nonneg_right (hdecay M) hgg
      _ = q ^ M * ((S.B f f - S.B f u ^ 2) * S.B g g) := by ring
  exact tendsto_of_sq_le hq0 hq1 hbound

#print axioms ergodicLimit_of_poincare

end Ergodic

end MassGap.HeatBathErgodic
