import Mathlib
import MassGap.OverlapSweep

/-!
# The overlapping block gap as a floor at the two-loop scale

`OverlapSweep.clay_continuum_of_overlapDynamics` takes two inputs about the overlapping block dynamics: the
gap at one coupling and the linear-loss step `OverlapBlockStep`, a comparison of two couplings one dyadic
step apart. The tower consumes only their consequence `gamma_eventually_ge_lin`: a positive floor of the gap
at fixed `s`-size at every large coupling. This module takes that floor as the input.

* `gapAt_eventually_of_floor`, `uniformPhysGapAlong_of_floor`: a floor `g > 0` of `γ` at every large `β` and
  the Chebyshev conversion give the uniform physical gap along `s` at rate `c₀ √g`.
* `floor_of_overlapBlockStep`: the base and the step give the floor (so the floor is the weaker input).
* `clay_continuum_of_overlapFloor`: the floor along a scale function `s` with `ScaleDominatesRun`, and E, N, Y.
* `scaleFunction_const_mul_aRun`, `clay_continuum_of_overlapFloorRun`: along `s = κ · aRun` the
  domination holds by construction, and the single input is
  `∃ g > 0, ∀ᶠ β, g ≤ overlapGap hN β ⌈1/(κ aRun β)⌉₊`: at each large coupling separately, a Poincaré
  inequality for the box dynamics at cell side `1/(κ aRun β)`. No statement compares two couplings.

Why the floor and not the step along `aRun`: the true spacing is `aRun · R(β)` with `R` drifting by `O(g⁴)`
per dyadic step (SCALE-STEP-FINDINGS, "Sizing the loss"); a drift of that order is not of the form `C s β`
(geometric along the tower), so `BlockStepLin` along `κ · aRun` holds only when the drift is a gain, while
the floor holds whenever `R` is bounded and the gap is bounded below at fixed true size.
-/

namespace MassGap.OverlapFloor

open MassGap MassGap.OverlapSweep
open Filter

variable {N : ℕ}

section Transfer

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **The transfer gap at a uniform rate in `s`-units from a floor of `γ`.**

DERIVED: `0` the signs. -/
theorem gapAt_eventually_of_floor (D : ℝ → Transfer.TransferData A) {γ s : ℝ → ℝ}
    {β₀ βUV g c₀ : ℝ} (hs : ScaleAlong.ScaleFunction s β₀) (hg : 0 ≤ g) (hc₀ : 0 ≤ c₀)
    (hfloor : ∀ᶠ β in atTop, g ≤ γ β)
    (hconv : BlockDynamicStep.ChebyshevConversion D γ s c₀ βUV) :
    ∀ᶠ β in atTop, TransferGap.GapAt (D β) (Real.exp (-(c₀ * Real.sqrt g * s β))) := by
  have _ := hg
  filter_upwards [hfloor, hs.eventually_le, Filter.eventually_ge_atTop βUV] with β hγ hsβ hβ
  refine GapStep.gapAt_mono _ (Real.exp_pos _).le ?_ (hconv β hβ)
  rw [Real.exp_le_exp, neg_le_neg_iff]
  have hsq := Real.sqrt_le_sqrt hγ
  have h1 := mul_le_mul_of_nonneg_left hsq hc₀
  exact mul_le_mul_of_nonneg_right h1 hsβ.1.le

#print axioms gapAt_eventually_of_floor

end Transfer

/-- **The uniform physical gap along `s` from a floor of the block gap.**

DERIVED: `2` the least rank; `0`, `1` the signs. -/
theorem uniformPhysGapAlong_of_floor (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    {γ s : ℝ → ℝ} {β₀ βUV g c₀ : ℝ} (hs : ScaleAlong.ScaleFunction s β₀) (hβ₀ : 0 < β₀)
    (hg : 0 < g) (hc₀ : 0 < c₀) (hfloor : ∀ᶠ β in atTop, g ≤ γ β)
    (hconv : BlockDynamicStep.ChebyshevConversion
      (fun β => PeriodicState.periodicGaugeInvData τ p hN β) γ s c₀ βUV) :
    ConstantPhysics.UniformPhysGapAlong τ p hN s := by
  set M := c₀ * Real.sqrt g with hM
  have hMpos : 0 < M := mul_pos hc₀ (Real.sqrt_pos.mpr hg)
  refine ⟨M, hMpos, ?_⟩
  filter_upwards [gapAt_eventually_of_floor _ hs hg.le hc₀.le hfloor hconv,
    hs.eventually_le, Filter.eventually_ge_atTop β₀] with β hgap hsβ hββ
  obtain ⟨hpos, _⟩ := hsβ
  have hβ0 : 0 ≤ β := (hβ₀.trans_le hββ).le
  have hr0 : 0 < Real.exp (-(M * s β)) := Real.exp_pos _
  have hr1 : Real.exp (-(M * s β)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  refine ⟨_, GapStep.periodic_clayGapAt_of_gapAt τ p hN2 hN hβ0 hr0 hr1 hgap, ?_⟩
  rw [Real.log_exp, neg_neg, mul_div_assoc, div_self hpos.ne', mul_one]

#print axioms uniformPhysGapAlong_of_floor

/-- **The base and the linear-loss step give the floor.** The floor is the weaker input.

DERIVED: `2` the budget; `0`, `1` the signs. -/
theorem floor_of_overlapBlockStep (hN : N ≠ 0) {s : ℝ → ℝ} {β₀ βUV C : ℝ}
    (hs : ScaleAlong.ScaleFunction s β₀) (hUVβ₀ : βUV ≤ β₀) (hg₀ : 0 < gammaOverlap hN s β₀)
    (hC : 0 ≤ C) (hCs : ∀ β, βUV ≤ β → C * s β ≤ 1) (hb : 2 * C * s β₀ < 1)
    (hstep : OverlapBlockStep hN s βUV C) :
    ∃ g : ℝ, 0 < g ∧ ∀ᶠ β in atTop, g ≤ gammaOverlap hN s β :=
  ⟨gammaOverlap hN s β₀ * (1 - 2 * C * s β₀), mul_pos hg₀ (by linarith),
    gamma_eventually_ge_lin hs hUVβ₀ hg₀.le hC hCs hstep⟩

#print axioms floor_of_overlapBlockStep

open MassGap.ContinuumField MassGap.ContinuumSchwinger in
/-- **The continuum Clay statement from a floor of the overlapping block gap along a scale function.**

DERIVED: `2` the least rank; `0` the reflection plane and the signs; `4` the spacetime dimension; `1` the
least colour count and the scale cap; `1012500` the conversion constant. -/
theorem clay_continuum_of_overlapFloor (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {s : ℝ → ℝ} {β₀ βUV g : ℝ} (hs : ScaleAlong.ScaleFunction s β₀) (hβ₀ : 0 < β₀)
    (hg : 0 < g) (hfloor : ∀ᶠ β in atTop, g ≤ gammaOverlap hN s β)
    (hs1 : ∀ β, βUV ≤ β → s β ≤ 1)
    (hdomR : ScaleAlong.ScaleDominatesRun s N)
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconvK : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum hN Z τ hZ hB L := by
  have hN1 : 1 ≤ N := by omega
  have hS := uniformPhysGapAlong_of_floor τ 0 hN2 hN hs hβ₀ hg (by norm_num : (0 : ℝ) < 1 / 1012500)
    hfloor (overlapConversion τ hN s βUV hs1)
  obtain ⟨κ, hκ, hdom⟩ := hdomR
  have hR : ConstantPhysics.UniformPhysGapAlong τ 0 hN (AsymptoticScaling.aRun N) :=
    ScaleAlong.uniformPhysGapAlong_of_dominates τ 0 hN hκ hdom
      (Filter.eventually_gt_atTop (0 : ℝ) |>.mono (fun _ h => AsymptoticScaling.aRun_pos hN1 h))
      (hs.eventually_le.mono (fun _ h => h.1)) hS
  have hW : WeakCouplingWindow.FixedWindowDecay τ 0 hN L :=
    (ConstantPhysics.fixedWindowDecayAlong_aRun τ 0 hN L).mp
      (ConstantPhysics.fixedWindowDecayAlong_of_uniformPhysGapAlong τ 0 hN hL
        (Filter.eventually_gt_atTop (0 : ℝ) |>.mono (fun _ h => AsymptoticScaling.aRun_pos hN1 h))
        (fun b hb => WeakCouplingWindow.eventually_aRun_le hN1 hb) hR)
  exact ClayRoutes.clay_continuum_of_fixedWindowDecay hN2 hN Z τ hZ hB hL hW O G hconvK hY

#print axioms clay_continuum_of_overlapFloor

/-- **`κ · aRun` is a scale function** from every positive coupling.

DERIVED: `1` the least colour count; `0` the signs. -/
theorem scaleFunction_const_mul_aRun (hN1 : 1 ≤ N) {κ β₀ : ℝ} (hκ : 0 < κ) (hβ₀ : 0 < β₀) :
    ScaleAlong.ScaleFunction (fun β => κ * AsymptoticScaling.aRun N β) β₀ where
  cont := ((AsymptoticScaling.continuous_aRun N).const_smul κ).continuousOn
  pos := fun β hβ => mul_pos hκ (AsymptoticScaling.aRun_pos hN1 (hβ₀.trans_le hβ))
  vanish := by
    have h := (ConstantPhysics.tendsto_aRun_zero (N := N) hN1).const_mul κ
    simpa using h

#print axioms scaleFunction_const_mul_aRun

open MassGap.ContinuumField MassGap.ContinuumSchwinger in
/-- **The continuum Clay statement from one family of single-coupling statements.** At every large `β`
separately, the overlapping block gap at cell side `⌈1/(κ aRun β)⌉₊` is at least `g > 0`; with E, N, Y,
`ClayRoutes.ClayContinuum`. No input compares two couplings, and `ScaleDominatesRun` holds by construction.

DERIVED: `2` the least rank; `0` the signs; `4` the spacetime dimension; `1` the least colour count and
the scale cap. -/
theorem clay_continuum_of_overlapFloorRun (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {κ g : ℝ} (hκ : 0 < κ) (hg : 0 < g)
    (hfloor : ∀ᶠ β in atTop,
      g ≤ overlapGap hN β (BlockGapDef.blockSide (fun β => κ * AsymptoticScaling.aRun N β) β))
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconvK : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum hN Z τ hZ hB L := by
  have hN1 : 1 ≤ N := by omega
  set s : ℝ → ℝ := fun β => κ * AsymptoticScaling.aRun N β with hsdef
  have hs : ScaleAlong.ScaleFunction s 1 := scaleFunction_const_mul_aRun hN1 hκ one_pos
  obtain ⟨βUV, hUV⟩ := Filter.eventually_atTop.mp (hs.eventually_small 1 one_pos)
  have hdomR : ScaleAlong.ScaleDominatesRun s N :=
    ⟨κ, hκ, Filter.Eventually.of_forall (fun _ => le_rfl)⟩
  exact clay_continuum_of_overlapFloor hN2 hN Z τ hZ hB hL hs one_pos hg hfloor hUV hdomR O G hconvK hY

#print axioms clay_continuum_of_overlapFloorRun

end MassGap.OverlapFloor
