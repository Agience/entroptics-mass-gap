import Mathlib
import MassGap.UVIRSplit
import MassGap.HeatBathLocal
import MassGap.PairCorrSharp

noncomputable section

/-!
# MassGap.EdgeStep — the UV step on the physical correlation length, at any finite budget

## What it gives

`GapAt D (e^{−a/ξ})` says the transfer data at spacing `a` contracts the vacuum complement by
`e^{−a/ξ}` per step, so every reflected connected pairing falls by `e^{−ℓ/ξ}` across a physical
length `ℓ`: `ξ` is a physical correlation length, and the length at which the attenuation reaches
`e^{−κ}` is `κ ξ`.

1. `EdgeStepAbove D a βUV δ ξ₀`: for every two couplings `β, β' ≥ βUV` one block step apart
   (`a β / 2 ≤ a β' ≤ a β`, the admissibility of `UVIRSplit.LossStep`) and every `ξ ≥ ξ₀`, the gap at
   correlation length `ξ` at `β` gives the gap at correlation length `ξ + δ(a β)` at `β'`. A block step
   lengthens the physical correlation length by at most `δ(a β)`. `ξ₀` carries no sign condition.
2. `lossStepBelow_of_edgeStepAbove`: at `ξ₀ ≤ M₁⁻¹`, non-negative `δ` and a spacing positive from
   `βUV` on, the edge step gives `UVIRSplit.LossStepBelow` at `M₁` with the loss `M₁² δ`: a rate
   `0 < M ≤ M₁` loses at most `M² δ/(1 + M δ) ≤ M₁² δ`.
3. `uvBelowIR_of_edgeStep`: `IRGapAt` at `β₀` at a rate `M₀ > 0`, the edge step above `M₀⁻¹` from
   `βUV > 0`, and a finite budget `E` for `δ` along the dyadic tower below `aRun N β₀`, give at the
   LOWERED rate `M₁ = M₀/(1 + 2 M₀ E)`: `0 < M₁`, `IRGapAt` at `β₀` at `M₁`, and
   `ClayRoutes.UVBelowIR` at `M₁` (losses `M₁² δ`, budget `M₁² E`, which `2 M₁ E ≤ 1` puts below `M₁`).
4. `fixedWindowDecay_of_edgeStep`: the same inputs give `WeakCouplingWindow.FixedWindowDecay τ p hN L`
   at every `L > 0`, through item 3 and `UVIRSplit.fixedWindowDecay_of_uv_ir_below` at `M₁`. No
   condition relates `E` to `M₀`.
5. `fixedWindowDecay_floor_su2_of_edgeStep`: at `SU(2)`, the IR input is the proved floor box
   (`PairCorrSharp.boxPatchGap_floor_su2`, `HeatBathLocal.irGapAt_boxRate`); the edge step above the
   inverse box rate, with a finite budget and non-negative `δ`, are the only hypotheses.
6. `edgeStep_of_fixedWindowDecay`: the converse. `FixedWindowDecay` gives a rate `M > 0`, a coupling
   `βUV > 0`, `IRGapAt` at `βUV` at `M` and the edge step above `M⁻¹` from `βUV` at ZERO loss.
7. `fixedWindowDecay_iff_edgeStep`: items 4 and 6 as one iff. At `2 ≤ N` and `0 < L`,
   `FixedWindowDecay τ p hN L` holds iff there are `βUV, β₀, M₀, E, ξ₀, δ` meeting the hypotheses of
   item 4. The edge step with a finite budget and one IR gap restates the uniform physical gap scale
   by scale; it does not weaken it.

## Scope

`EdgeStepAbove` at `δ = 0`, positive spacings and `ξ₀ > 0` at least the supremum over `β' ≥ βUV` of
the true correlation lengths, when that supremum is finite, holds trivially (`GapStep.gapAt_mono`;
`edgeStep_of_fixedWindowDecay` is this case), so the clipped step carries content only where the true
correlation length exceeds `ξ₀`; a finite supremum is itself the uniform-gap question.
`ClayRoutes.UVBelowIR` at a rate `M₀` asks the summed losses to stay below `M₀` itself; at the floor
`M₀` is the box rate, about `3.0·10⁻⁵/aRun 2 β₀` at `SU(2)` and `1.45·10⁻⁴/aRun 3 β₀` at `SU(3)`. The
edge step with any finite budget `E` gives `UVBelowIR` at the lowered rate `M₁ = M₀/(1 + 2 M₀ E)`, not
at `M₀` (item 3): the comparison is met by lowering the rate, which `IRGapAt` at `M₀` permits.
`UVBelowIR` at a free rate with `IRGapAt` at the same rate is also `FixedWindowDecay` restated: one
direction is `UVIRSplit.fixedWindowDecay_of_uv_ir_below`, the other composes
`UVIRSplit.irGapAt_of_fixedWindowDecay` with `ClayRoutes.uvBelowIR_of_uniform_gap` at zero loss; no
single theorem states that iff, and both directions are at a rate the proof chooses, not at the box
rate.

DERIVED (module-wide): `4` in `Fin 4` is the spacetime dimension; `2` is the block factor of
`UVIRSplit.LossStep` and, in `2 ≤ N`, the least rank with a non-zero Haar variance; `1` in `1 ≤ N` is
the least colour count, for `aRun_pos`, and in `1 + 2 M₀ E` the rate at `E = 0`; `0` is the excluded
colour count and the sign of rates, losses and lengths; `2606` and `307/10000` are
`PairCorrSharp.boxPatchGap_floor_su2`'s side and gap. The `2` in `M₀/(1 + 2 M₀ E)` is CHOSEN: any
factor of at least `1` serves.
-/

namespace MassGap.EdgeStep

open MassGap MassGap.AsymptoticScaling MassGap.UVIRSplit

section Abstract

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **The block step on the correlation length, clipped at `ξ₀`.** For two couplings `β, β' ≥ βUV`
one block step apart and every `ξ ≥ ξ₀`: the gap at rate `e^{−a β/ξ}` at `β` gives the gap at rate
`e^{−a β'/(ξ + δ(a β))}` at `β'`.

Scope: `ξ₀` carries no sign condition. At `ξ₀ ≤ 0` and `0 ≤ a β` the premise holds at every
`ξ ∈ [ξ₀, 0]`: at `ξ = 0`, `a β / 0 = 0` and the rate is `1`; below it the rate exceeds `1`; every
family meets `GapAt` there (`TransferGap.gapAt_of_one_le_sq`). The step then asserts the gap at `β'`
outright at every correlation length `ξ + δ(a β)` with `ξ₀ ≤ ξ ≤ 0`, the shortest being
`ξ₀ + δ(a β)`.

DERIVED: `2` is the block factor. -/
def EdgeStepAbove (D : ℝ → Transfer.TransferData A) (a : ℝ → ℝ) (βUV : ℝ) (δ : ℝ → ℝ)
    (ξ₀ : ℝ) : Prop :=
  ∀ β β' : ℝ, βUV ≤ β → βUV ≤ β' → a β / 2 ≤ a β' → a β' ≤ a β →
    ∀ ξ : ℝ, ξ₀ ≤ ξ → TransferGap.GapAt (D β) (Real.exp (-(a β / ξ))) →
      TransferGap.GapAt (D β') (Real.exp (-(a β' / (ξ + δ (a β)))))

/-- The rate a correlation length loses: at `0 < M ≤ M₁`, `0 ≤ d` and `M u = 1`,
`(M − M₁² d)(u + d) ≤ 1`.

DERIVED: `2` is the square; `0` is the sign of `M` and `d`; `1` is the normalisation `M u = 1` and
the bound. -/
theorem rate_loss_le {M M₁ u d : ℝ} (hM : 0 < M) (hMM : M ≤ M₁) (hu : M * u = 1) (hd : 0 ≤ d) :
    (M - M₁ ^ 2 * d) * (u + d) ≤ 1 := by
  have hu0 : 0 < u := by
    by_contra h
    have h' : u ≤ 0 := not_lt.mp h
    nlinarith
  have hsq : M ^ 2 ≤ M₁ ^ 2 := pow_le_pow_left₀ hM.le hMM 2
  have h1 : M ^ 2 * u = M := by nlinarith
  have h2 : 0 ≤ (M₁ ^ 2 - M ^ 2) * d * u :=
    mul_nonneg (mul_nonneg (by linarith) hd) hu0.le
  have h3 : 0 ≤ M₁ ^ 2 * d * d := mul_nonneg (mul_nonneg (sq_nonneg _) hd) hd
  nlinarith

#print axioms rate_loss_le

/-- **The edge step gives the clipped rate step with loss `M₁² δ`.** At `ξ₀ ≤ M₁⁻¹`,
non-negative `δ` and a spacing positive from `βUV` on: `EdgeStepAbove D a βUV δ ξ₀` gives
`UVIRSplit.LossStepBelow D a βUV (M₁² δ) M₁`. No sign of `M₁` is assumed. At `M ≤ 0` the conclusion's
rate is at least one (`TransferGap.gapAt_of_one_le_sq`); at `0 < M ≤ M₁` the edge step at
`ξ = M⁻¹ ≥ ξ₀` gives the rate `e^{−a β'/(M⁻¹ + δ)}`, at most `e^{−(M − M₁² δ)·a β'}` (`rate_loss_le`).

DERIVED: `2` is the block factor and the square; `0` is the sign of `δ` and the spacing. -/
theorem lossStepBelow_of_edgeStepAbove (D : ℝ → Transfer.TransferData A) (a : ℝ → ℝ) {βUV : ℝ}
    {δ : ℝ → ℝ} {ξ₀ M₁ : ℝ} (hξ₀ : ξ₀ ≤ M₁⁻¹) (hδ : ∀ s : ℝ, 0 ≤ δ s)
    (ha : ∀ β : ℝ, βUV ≤ β → 0 < a β) (h : EdgeStepAbove D a βUV δ ξ₀) :
    LossStepBelow D a βUV (fun s => M₁ ^ 2 * δ s) M₁ := by
  intro β β' h1 h2 h3 h4 M hM hg
  have ha' : 0 < a β' := ha β' h2
  have hd := hδ (a β)
  rcases le_or_gt M 0 with hM0 | hM0
  · apply TransferGap.gapAt_of_one_le_sq
    have hx : 0 ≤ -((M - M₁ ^ 2 * δ (a β)) * a β') := by
      have : (M - M₁ ^ 2 * δ (a β)) * a β' ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg M₁]) ha'.le
      linarith
    exact one_le_pow₀ (Real.one_le_exp hx)
  · have hMu : M * M⁻¹ = 1 := mul_inv_cancel₀ hM0.ne'
    have hξ : ξ₀ ≤ M⁻¹ := hξ₀.trans (inv_anti₀ hM0 hM)
    have hg' : TransferGap.GapAt (D β) (Real.exp (-(a β / M⁻¹))) := by
      rw [div_inv_eq_mul, mul_comm]
      exact hg
    have hstep := h β β' h1 h2 h3 h4 M⁻¹ hξ hg'
    have hu0 : 0 < M⁻¹ := inv_pos.mpr hM0
    have hden : 0 < M⁻¹ + δ (a β) := by linarith
    have hkey := rate_loss_le hM0 hM hMu hd
    have hle : (M - M₁ ^ 2 * δ (a β)) * a β' ≤ a β' / (M⁻¹ + δ (a β)) := by
      rw [le_div_iff₀ hden]
      have := mul_le_mul_of_nonneg_left hkey ha'.le
      nlinarith
    exact GapStep.gapAt_mono _ (Real.exp_pos _).le
      (Real.exp_le_exp.mpr (by linarith)) hstep

#print axioms lossStepBelow_of_edgeStepAbove

end Abstract

section Wilson

variable {N : ℕ}

/-- **The edge step at the periodic data along `aRun N`.**

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank. -/
def UVEdgeStepAbove (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (βUV : ℝ) (δ : ℝ → ℝ) (ξ₀ : ℝ) : Prop :=
  EdgeStepAbove (fun β => PeriodicState.periodicGaugeInvData τ p hN β) (aRun N) βUV δ ξ₀

/-- **The edge step gives `UVBelowIR` at the lowered rate.** At `0 < βUV ≤ β₀`, `0 < M₀`,
`ξ₀ ≤ M₀⁻¹`, non-negative `δ` with `UVIRSplit.LossBudget δ (aRun N β₀) E`,
`UVEdgeStepAbove τ p hN βUV δ ξ₀` and `UVIRSplit.IRGapAt τ p hN β₀ M₀`: at
`M₁ = M₀/(1 + 2 M₀ E)`, `0 < M₁`, `IRGapAt τ p hN β₀ M₁` and
`ClayRoutes.UVBelowIR τ p hN β₀ βUV M₁`. `IRGapAt` passes from `M₀` to `M₁ ≤ M₀` by
`GapStep.gapAt_mono`; the clipped rate step at `M₁` with loss `M₁² δ` is
`lossStepBelow_of_edgeStepAbove` (`ξ₀ ≤ M₀⁻¹ ≤ M₁⁻¹`); its budget `M₁² E` is below `M₁` because
`2 M₁ E ≤ 1`. The conclusion is at `M₁`, not at `M₀`.

DERIVED: `4` is the spacetime dimension; `1` in `1 + 2 M₀ E` is the rate at `E = 0`, `M₁ = M₀`; `0` is
the excluded rank and the sign of `βUV`, `M₀`, `δ`. CHOSEN: the `2` of `1 + 2 M₀ E`, any factor of at
least `1` serves. -/
theorem uvBelowIR_of_edgeStep (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {βUV β₀ M₀ E ξ₀ : ℝ}
    {δ : ℝ → ℝ} (hβUV : 0 < βUV) (hUVβ₀ : βUV ≤ β₀) (hM₀ : 0 < M₀) (hξ₀ : ξ₀ ≤ M₀⁻¹)
    (hbud : LossBudget δ (aRun N β₀) E) (hδ : ∀ s : ℝ, 0 ≤ δ s)
    (hedge : UVEdgeStepAbove τ p hN βUV δ ξ₀) (hir : IRGapAt τ p hN β₀ M₀) :
    0 < M₀ / (1 + 2 * M₀ * E) ∧ IRGapAt τ p hN β₀ (M₀ / (1 + 2 * M₀ * E)) ∧
      ClayRoutes.UVBelowIR τ p hN β₀ βUV (M₀ / (1 + 2 * M₀ * E)) := by
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  have hβ₀ : 0 < β₀ := lt_of_lt_of_le hβUV hUVβ₀
  have ha₀ : 0 < aRun N β₀ := aRun_pos hN1 hβ₀
  have hE0 : 0 ≤ E := by
    have h := hbud 0
    rw [Finset.sum_range_zero] at h
    exact h
  set M₁ : ℝ := M₀ / (1 + 2 * M₀ * E) with hM₁def
  have hden : 0 < 1 + 2 * M₀ * E := by positivity
  have hM₁ : 0 < M₁ := div_pos hM₀ hden
  have hM₁eq : M₁ * (1 + 2 * M₀ * E) = M₀ := div_mul_cancel₀ M₀ hden.ne'
  have hM₁le : M₁ ≤ M₀ := by nlinarith [mul_nonneg (mul_nonneg hM₁.le hM₀.le) hE0]
  have hM₁E : 2 * (M₁ * E) ≤ 1 := by
    -- `2 M₁ M₀ E = M₀ − M₁ ≤ M₀`, divide by `M₀ > 0`
    have h' : M₀ * (2 * (M₁ * E)) ≤ M₀ * 1 := by nlinarith
    exact le_of_mul_le_mul_left h' hM₀
  have hbudlt : M₁ ^ 2 * E < M₁ := by nlinarith
  have hξ₁ : ξ₀ ≤ M₁⁻¹ := hξ₀.trans (inv_anti₀ hM₁ hM₁le)
  have hir₁ : IRGapAt τ p hN β₀ M₁ := by
    unfold IRGapAt at hir ⊢
    refine GapStep.gapAt_mono _ (Real.exp_pos _).le (Real.exp_le_exp.mpr ?_) hir
    have := mul_le_mul_of_nonneg_right hM₁le ha₀.le
    linarith
  have hbud₁ : LossBudget (fun s => M₁ ^ 2 * δ s) (aRun N β₀) (M₁ ^ 2 * E) := by
    intro n
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hbud n) (sq_nonneg _)
  have huv : UVLossStepBelow τ p hN βUV (fun s => M₁ ^ 2 * δ s) M₁ :=
    lossStepBelow_of_edgeStepAbove _ _ hξ₁ hδ
      (fun β hβ => aRun_pos hN1 (lt_of_lt_of_le hβUV hβ)) hedge
  exact ⟨hM₁, hir₁, fun s => M₁ ^ 2 * δ s, M₁ ^ 2 * E,
    fun s => mul_nonneg (sq_nonneg _) (hδ s), hbud₁, hbudlt, huv⟩

#print axioms uvBelowIR_of_edgeStep

/-- **`FixedWindowDecay` from the edge step and a gap at one coupling, at any finite budget.** At
`2 ≤ N`, `0 < L`, `0 < βUV ≤ β₀`, `0 < M₀`, `ξ₀ ≤ M₀⁻¹`, non-negative `δ` with
`UVIRSplit.LossBudget δ (aRun N β₀) E`, `UVEdgeStepAbove τ p hN βUV δ ξ₀` and
`UVIRSplit.IRGapAt τ p hN β₀ M₀`: `WeakCouplingWindow.FixedWindowDecay τ p hN L`. No relation between
`E` and `M₀` is assumed. `uvBelowIR_of_edgeStep` gives `IRGapAt` and `ClayRoutes.UVBelowIR` at
`M₁ = M₀/(1 + 2 M₀ E)`, and `UVIRSplit.fixedWindowDecay_of_uv_ir_below` consumes them at `M₁`.

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded rank and the sign of `L`, `βUV`, `M₀`, `δ`. -/
theorem fixedWindowDecay_of_edgeStep (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) {L : ℝ}
    (hL : 0 < L) {βUV β₀ M₀ E ξ₀ : ℝ} {δ : ℝ → ℝ} (hβUV : 0 < βUV) (hUVβ₀ : βUV ≤ β₀)
    (hM₀ : 0 < M₀) (hξ₀ : ξ₀ ≤ M₀⁻¹) (hbud : LossBudget δ (aRun N β₀) E)
    (hδ : ∀ s : ℝ, 0 ≤ δ s) (hedge : UVEdgeStepAbove τ p hN βUV δ ξ₀)
    (hir : IRGapAt τ p hN β₀ M₀) :
    WeakCouplingWindow.FixedWindowDecay τ p hN L := by
  obtain ⟨_, hir₁, ε, E₁, hε, hbud₁, hlt, huv⟩ :=
    uvBelowIR_of_edgeStep τ p hN hβUV hUVβ₀ hM₀ hξ₀ hbud hδ hedge hir
  exact fixedWindowDecay_of_uv_ir_below τ p hN2 hN hL (lt_of_lt_of_le hβUV hUVβ₀) hUVβ₀ hbud₁ hlt
    hε huv hir₁

#print axioms fixedWindowDecay_of_edgeStep

/-- **At `SU(2)`, from the floor box and the edge step alone.** At a window `L > 0`, a non-negative
`δ` with a finite budget `E` along the dyadic tower below `aRun 2 (floorBeta 2)`, and the edge step
from `floorBeta 2` above the inverse box rate: `WeakCouplingWindow.FixedWindowDecay τ 0 h2 L`. The IR
input is `PairCorrSharp.boxPatchGap_floor_su2` through `HeatBathLocal.irGapAt_boxRate`.

DERIVED: `2` is the rank; `4` in `Fin 4` is the spacetime dimension; `0` is the reflection plane, the
excluded rank and the sign of `L` and `δ`; `2606`, `307/10000` are
`PairCorrSharp.boxPatchGap_floor_su2`'s side and gap. -/
theorem fixedWindowDecay_floor_su2_of_edgeStep (h2 : (2 : ℕ) ≠ 0) (τ : Fin 4) {L : ℝ} (hL : 0 < L)
    {δ : ℝ → ℝ} {E : ℝ} (hbud : LossBudget δ (aRun 2 (PairCorrSharp.floorBeta 2)) E)
    (hδ : ∀ s : ℝ, 0 ≤ δ s)
    (hedge : UVEdgeStepAbove τ 0 h2 (PairCorrSharp.floorBeta 2) δ
      (HeatBathLocal.boxRate 2 (PairCorrSharp.floorBeta 2) 2606 (307 / 10000))⁻¹) :
    WeakCouplingWindow.FixedWindowDecay τ 0 h2 L := by
  obtain ⟨hpos, hir⟩ := HeatBathLocal.irGapAt_boxRate τ 0 (by norm_num) h2
    (PairCorrSharp.floorBeta_pos h2) (PairCorrSharp.boxPatchGap_floor_su2 h2)
  exact fixedWindowDecay_of_edgeStep τ 0 (by norm_num) h2 hL (PairCorrSharp.floorBeta_pos h2)
    le_rfl hpos le_rfl hbud hδ hedge hir

#print axioms fixedWindowDecay_floor_su2_of_edgeStep

/-- **The converse: `FixedWindowDecay` gives the edge step at zero loss.** At `2 ≤ N` and `0 < L`,
`FixedWindowDecay τ p hN L` gives `M > 0` and `βUV > 0` with `IRGapAt τ p hN βUV M` and
`UVEdgeStepAbove τ p hN βUV 0 M⁻¹`: at every `β' ≥ βUV` the gap at physical rate `M`
(`UVIRSplit.irGapAt_of_fixedWindowDecay`) gives the gap at every correlation length `ξ ≥ M⁻¹`.

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded rank, the loss and the sign of `L`, `M`, `βUV`. CHOSEN (proof): the `1` of `max b 1`,
any threshold past `b` and `0` serves. -/
theorem edgeStep_of_fixedWindowDecay (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) {L : ℝ}
    (hL : 0 < L) (h : WeakCouplingWindow.FixedWindowDecay τ p hN L) :
    ∃ M : ℝ, 0 < M ∧ ∃ βUV : ℝ, 0 < βUV ∧ IRGapAt τ p hN βUV M ∧
      UVEdgeStepAbove τ p hN βUV (fun _ => 0) M⁻¹ := by
  have hN1 : 1 ≤ N := by omega
  obtain ⟨M, hM, hev⟩ := irGapAt_of_fixedWindowDecay τ p hN2 hN hL h
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.mp hev
  refine ⟨M, hM, max b 1, lt_of_lt_of_le one_pos (le_max_right b 1),
    hb _ (le_max_left b 1), ?_⟩
  intro β β' _ h2 _ _ ξ hξ _
  have hβ' : 0 < β' := lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_right b 1)) h2
  have ha' : 0 < aRun N β' := aRun_pos hN1 hβ'
  have hMinv : 0 < M⁻¹ := inv_pos.mpr hM
  have hξ0 : 0 < ξ := lt_of_lt_of_le hMinv hξ
  have hMξ : 1 ≤ M * ξ := by
    have := mul_le_mul_of_nonneg_left hξ hM.le
    rwa [mul_inv_cancel₀ hM.ne'] at this
  have hg := hb β' (le_trans (le_max_left b 1) h2)
  unfold IRGapAt at hg
  have hle : aRun N β' / (ξ + 0) ≤ M * aRun N β' := by
    rw [add_zero, div_le_iff₀ hξ0]
    nlinarith
  exact GapStep.gapAt_mono _ (Real.exp_pos _).le (Real.exp_le_exp.mpr (by linarith)) hg

#print axioms edgeStep_of_fixedWindowDecay

/-- **`FixedWindowDecay` is the edge step with a finite budget and one IR gap.** At `2 ≤ N` and
`0 < L`: `WeakCouplingWindow.FixedWindowDecay τ p hN L` iff there are `βUV, β₀, M₀, E, ξ₀` and `δ` with
`0 < βUV ≤ β₀`, `0 < M₀`, `ξ₀ ≤ M₀⁻¹`, `UVIRSplit.LossBudget δ (aRun N β₀) E`, non-negative `δ`,
`UVEdgeStepAbove τ p hN βUV δ ξ₀` and `UVIRSplit.IRGapAt τ p hN β₀ M₀`. Right to left is
`fixedWindowDecay_of_edgeStep`; left to right is `edgeStep_of_fixedWindowDecay` with `β₀ = βUV`,
`ξ₀ = M⁻¹`, `δ = 0` and `E = 0`.

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded rank and the sign of `L`, `βUV`, `M₀`, `δ`. -/
theorem fixedWindowDecay_iff_edgeStep (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) {L : ℝ}
    (hL : 0 < L) :
    WeakCouplingWindow.FixedWindowDecay τ p hN L ↔
      ∃ (βUV β₀ M₀ E ξ₀ : ℝ) (δ : ℝ → ℝ), 0 < βUV ∧ βUV ≤ β₀ ∧ 0 < M₀ ∧ ξ₀ ≤ M₀⁻¹ ∧
        LossBudget δ (aRun N β₀) E ∧ (∀ s : ℝ, 0 ≤ δ s) ∧
        UVEdgeStepAbove τ p hN βUV δ ξ₀ ∧ IRGapAt τ p hN β₀ M₀ := by
  constructor
  · intro h
    obtain ⟨M, hM, βUV, hβUV, hir, hedge⟩ := edgeStep_of_fixedWindowDecay τ p hN2 hN hL h
    exact ⟨βUV, βUV, M, 0, M⁻¹, fun _ => 0, hβUV, le_rfl, hM, le_rfl,
      fun n => by simp, fun _ => le_rfl, hedge, hir⟩
  · rintro ⟨βUV, β₀, M₀, E, ξ₀, δ, hβUV, hUVβ₀, hM₀, hξ₀, hbud, hδ, hedge, hir⟩
    exact fixedWindowDecay_of_edgeStep τ p hN2 hN hL hβUV hUVβ₀ hM₀ hξ₀ hbud hδ hedge hir

#print axioms fixedWindowDecay_iff_edgeStep

end Wilson

end MassGap.EdgeStep
