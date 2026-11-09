import Mathlib
import MassGap.OneLoopInput

/-!
# MassGap.OneLoopPrefactor — the strong end reads no prefactor

`OneLoopInput.strongEnd_of_oneLoopAbove` consumes the comparison `D(β, w + 1) ≤ D(β − c, w)` with prefactor `1`.
The only exact four-dimensional comparison in the tree, `OneStepZoom.stack_step`, is an identity with prefactor
`4 = 2^{d−2}`, the growth of the transverse plane count `n²` under doubling. This module proves that the strong end
does not read the prefactor: any prefactor `K β`, uniform in the window, and any additive slack `ε β w → 0` along
the windows, give `CouplingTower.StrongEnd N` from one vanishing read, exactly as prefactor `1` does. It is a thin
reduction: `K` and `ε` are absorbed by the limit. Declarations are in `MassGap.OneLoopPrefactor`.

## 1. The transport (proved)

* `tendsto_of_slack_step`: on any reading, `0 ≤ g (w + 1) ≤ K · h w + ε w` at `w ≥ 1`, `h → 0`, `ε → 0`, give
  `g → 0`. The limit of `K · h + ε` is `K · 0 + 0`; no size of `K` enters.
* `OneLoopAboveSlack N β₀ K ε`: `D(β, w + 1) ≤ K β · D(β − leanStep N, w) + ε β w` at `β ≥ β₀`, `w ≥ 1`.
* `oneLoopAboveSlack_of_oneLoopAbove`: `OneLoopInput.OneLoopAbove N β₀` is the case `K = 1`, `ε = 0`.
* `vanishes_add_nsmul_slack`, `strongEnd_of_oneLoopAboveSlack`: the slack form with one vanishing read at `x ≥ 0`,
  `β₀ ≤ x + c`, gives the read at `x + n c` for every `n`, so `StrongEnd N`. `strongEnd_of_oneLoopAboveSlack_low`:
  at `β₀ ≤ c` the read `D(0, ·) = 0` serves. The prefactor `4` of `stack_step` is the case `K = fun _ => 4`.

## What does not follow

* Any comparison for the Wilson measure, at any prefactor. Argued, not proved: the size of the prefactor is not
  the open part of `OneLoopAbove`; the open part is that the defect at `β` and window `w + 1` is controlled,
  uniformly in `w`, by the defect at a coupling lower by a fixed step at window `w`. That uniform one-step control is
  the multiscale content. Computed outside Lean, not proved: exact `U(1)` heat-kernel theta sums show that the
  prefactor-`1` comparison on the stack fails at weak coupling, where no coupling-lowering map absorbs the `4`.

DERIVED (module-wide): `0` the limit and the signs; `1` the least window and the one-step index; `2` the least rank;
`4 = 2^{d−2}` the transverse factor of `OneStepZoom.stack_step` at `d = 4` (prose only).
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.OneLoopPrefactor

open Filter Topology
open MassGap.CouplingTower (windowCoupling StrongEnd windowCoupling_nonneg)
open MassGap.StrongAnchor (Vanishes vanishes_zero)
open MassGap.OneLoopInput (leanStep leanStep_pos OneLoopAbove)

/-! ## 1. The transport -/

/-- **A step with any prefactor and a vanishing slack carries the limit `0`.** DERIVED: `0` the limit and the
sign; `1` the least window and the one-step index. -/
theorem tendsto_of_slack_step {g h ε : ℕ → ℝ} (K : ℝ) (hnn : ∀ w : ℕ, 1 ≤ w → 0 ≤ g (w + 1))
    (hs : ∀ w : ℕ, 1 ≤ w → g (w + 1) ≤ K * h w + ε w) (hh : Tendsto h atTop (𝓝 0))
    (hε : Tendsto ε atTop (𝓝 0)) : Tendsto g atTop (𝓝 0) := by
  have hu : Tendsto (fun w => K * h w + ε w) atTop (𝓝 0) := by
    simpa using (hh.const_mul K).add hε
  have ht : Tendsto (fun w => g (w + 1)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with w hw
      exact hnn w hw
    · filter_upwards [eventually_ge_atTop 1] with w hw
      exact hs w hw
  exact (tendsto_add_atTop_iff_nat 1).mp ht

/-- **The comparison with a prefactor and a slack**: `D(β, w + 1) ≤ K β · D(β − c, w) + ε β w` at `β ≥ β₀`,
`w ≥ 1`, with `ε β w → 0` along the windows. DERIVED: `0` the limit; `1` the least window and the step. -/
def OneLoopAboveSlack (N : ℕ) (β₀ : ℝ) (K : ℝ → ℝ) (ε : ℝ → ℕ → ℝ) : Prop :=
  (∀ β : ℝ, β₀ ≤ β → Tendsto (ε β) atTop (𝓝 0)) ∧
    ∀ β : ℝ, β₀ ≤ β → ∀ w : ℕ, 1 ≤ w →
      windowCoupling N β (w + 1) ≤ K β * windowCoupling N (β - leanStep N) w + ε β w

/-- **Prefactor `1`, no slack, is `OneLoopAbove`.** DERIVED: `0` the slack; `1` the prefactor. -/
theorem oneLoopAboveSlack_of_oneLoopAbove {N : ℕ} {β₀ : ℝ} (h : OneLoopAbove N β₀) :
    OneLoopAboveSlack N β₀ (fun _ => 1) (fun _ _ => 0) :=
  ⟨fun _ _ => tendsto_const_nhds, fun β hβ w hw => by simpa using h β hβ w hw⟩

/-- **The slack form carries one vanishing read up the lattice `x + n c`.** DERIVED: `0` the sign; `1` the
step; `2` the least rank. -/
theorem vanishes_add_nsmul_slack {N : ℕ} (hN : 2 ≤ N) {β₀ x : ℝ} {K : ℝ → ℝ} {ε : ℝ → ℕ → ℝ}
    (h : OneLoopAboveSlack N β₀ K ε) (hx : 0 ≤ x) (hle : β₀ ≤ x + leanStep N) (hv : Vanishes N x) (n : ℕ) :
    Vanishes N (x + n * leanStep N) := by
  have hc := leanStep_pos hN
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    have hn : (0 : ℝ) ≤ n * leanStep N := by positivity
    have e : x + ((n + 1 : ℕ) : ℝ) * leanStep N - leanStep N = x + n * leanStep N := by push_cast; ring
    have hβ : β₀ ≤ x + ((n + 1 : ℕ) : ℝ) * leanStep N := by push_cast; nlinarith
    have hpos : (0 : ℝ) ≤ x + ((n + 1 : ℕ) : ℝ) * leanStep N := by positivity
    refine tendsto_of_slack_step (K (x + ((n + 1 : ℕ) : ℝ) * leanStep N))
      (fun w hw => windowCoupling_nonneg (by omega) hpos (by omega)) (fun w hw => ?_) ih (h.1 _ hβ)
    have := h.2 _ hβ w hw
    rwa [e] at this

/-- **The slack form and one vanishing read give the strong end**, at every prefactor. `K` and `ε` are absorbed
by the limit: the transport uses only that vanishing at `β − c` implies vanishing at `β`. The whole burden is the
comparison hypothesis `OneLoopAboveSlack`, the open multiscale statement. DERIVED: `0` the sign; `2` the least
rank. -/
theorem strongEnd_of_oneLoopAboveSlack {N : ℕ} (hN : 2 ≤ N) {β₀ x : ℝ} {K : ℝ → ℝ} {ε : ℝ → ℕ → ℝ}
    (h : OneLoopAboveSlack N β₀ K ε) (hx : 0 ≤ x) (hle : β₀ ≤ x + leanStep N) (hv : Vanishes N x) :
    StrongEnd N := by
  have hc := leanStep_pos hN
  refine frequently_atTop.mpr fun a => ?_
  obtain ⟨n, hn⟩ := exists_nat_ge ((a - x) / leanStep N)
  refine ⟨x + n * leanStep N, ?_, vanishes_add_nsmul_slack hN h hx hle hv n⟩
  have := (div_le_iff₀ hc).mp hn
  linarith

/-- **At `β₀ ≤ c` the slack form alone gives the strong end**, from the read `D(0, ·) = 0`. DERIVED: `0` the
ultralocal coupling; `2` the least rank. -/
theorem strongEnd_of_oneLoopAboveSlack_low {N : ℕ} (hN : 2 ≤ N) {β₀ : ℝ} {K : ℝ → ℝ} {ε : ℝ → ℕ → ℝ}
    (h : OneLoopAboveSlack N β₀ K ε) (hle : β₀ ≤ leanStep N) : StrongEnd N :=
  strongEnd_of_oneLoopAboveSlack hN h le_rfl (by linarith) vanishes_zero

end MassGap.OneLoopPrefactor

end

#print axioms MassGap.OneLoopPrefactor.tendsto_of_slack_step
#print axioms MassGap.OneLoopPrefactor.oneLoopAboveSlack_of_oneLoopAbove
#print axioms MassGap.OneLoopPrefactor.vanishes_add_nsmul_slack
#print axioms MassGap.OneLoopPrefactor.strongEnd_of_oneLoopAboveSlack
#print axioms MassGap.OneLoopPrefactor.strongEnd_of_oneLoopAboveSlack_low
