import Mathlib
import MassGap.EndpointAudit
import MassGap.ScaleControlRun
import MassGap.AttractCost
import MassGap.TensionFloor
import MassGap.MultiScale

/-!
# MassGap.InputAudit — the fixed-`t₀` count over unboundedly many windows, in every carrier

`EndpointAudit.not_endpointN_of_levels_unbounded` rules out `RunSeedN.EndpointN N` when the low-level count of the
window slices is unbounded in the window. The same clause, `GlueballArea.ZeroFluxCount g₀ E t₀ C` with `t₀` and `C`
fixed before `∃ᶠ ℓ`, sits in four more carriers of the gap input, and each of them reaches
`GlueballArea.UniformGlueball N m t₀ C ℓ` at the windows it visits. This module states the no-go once, on
`UniformGlueball`, and reads it into the carriers. Declarations are in the namespace `MassGap.InputAudit`.

* `ZeroFluxLevelsUnbounded N D`: for every `K`, eventually in `ℓ` and frequently in `β`, some window slice has, on
  every zero-flux level family (`GlueballArea.ZeroFluxLevels`), more than `K` levels within `D` of the ground.
  Argued, not proved: the one-glueball momentum states of a slice of transverse side `L ≥ 2ℓ` number `∼ (L·p_D)³`
  within `D > m_G` of the ground (§4 of the `EndpointAudit` module docstring).
* **`not_frequently_uniformGlueball`**: under it, no fixed `t₀ ≥ 0`, `C` has `UniformGlueball N m t₀ C ℓ` (any `m`,
  which may vary with `ℓ`) frequently in `ℓ` (`EndpointAudit.card_mul_exp_le_of_count`).
* **`not_tensionFloorRun`**: (V) with the tension-floor count clause, frequently in `ℓ` at one `t₀` and one `C`,
  fails.
* **`not_attractRun`**: (V) with the attraction clause, frequently in `ℓ` at one `t₀` and one `C`, fails.
* **`not_scaleControlRun`**: `¬ ScaleControlRun`; **`not_multiScaleEndpoint`**: `¬ MultiScale.Endpoint`
  (`MultiScale.endpoint_iff_run`).

The capstone `ClayRunSeed.clayStatement_of_narrowAtRS` takes `WDeltaRun.RunSeed N` in its gap slot, which fixes one
physical scale and no heat-trace time, and `EndpointAudit.EndpointS N` asks its counts at one window; neither is
reached by these statements.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` the least side, the window's lower end and `SU(2)`; `5` the window's upper end; `1` the
ground weight.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.InputAudit

open Filter
open MassGap.GlueballArea (ZeroFluxLevels ZeroFluxCount UniformGlueball)
open MassGap.AsymptoticScaling (aRun)

section NoGo

variable (N : ℕ) [NeZero N]

/-- **The low-level count of the window slices exceeds every bound**: for every `K`, eventually in `ℓ` and
frequently in `β`, some power-of-two side `n ≥ 2` with `n a ∈ [2ℓ, 5ℓ]` and some step `i` have, on every
zero-flux level family, more than `K` levels within `D` of the ground. Argued (module docstring) for `D` above
the glueball mass, not proved.
DERIVED: `2` the least side and the window's lower end; `5` the window's upper end. -/
def ZeroFluxLevelsUnbounded (D : ℝ) : Prop :=
  ∀ K : ℝ, ∀ᶠ ℓ in atTop, ∃ᶠ β in atTop, ∃ n : ℕ, PeriodicState.IsPow2 n ∧ 2 ≤ n ∧
    2 * ℓ ≤ (n : ℝ) * aRun N β ∧ (n : ℝ) * aRun N β ≤ 5 * ℓ ∧ ∃ i : Fin 4,
      ∀ (ι : Type) (g₀ : ι) (E : ι → ℝ), ZeroFluxLevels N β n i g₀ E →
        ∃ S : Finset ι, (∀ j ∈ S, E j - E g₀ ≤ D) ∧ K < (S.card : ℝ)

variable {N}

/-- **No fixed count over unboundedly many windows**: under `ZeroFluxLevelsUnbounded N D`, no `t₀ ≥ 0` and `C`
have `UniformGlueball N m t₀ C ℓ` (at some `m`) frequently in `ℓ`. `card_mul_exp_le_of_count` bounds the number of
levels within `D` of the ground on every slice of such a window by `(1 + C) e^{D t₀}`. DERIVED: `1` the ground
weight. -/
theorem not_frequently_uniformGlueball {D t₀ C : ℝ} (ht₀ : 0 ≤ t₀) (h : ZeroFluxLevelsUnbounded N D) :
    ¬ ∃ᶠ ℓ in atTop, ∃ m : ℝ, UniformGlueball N m t₀ C ℓ := by
  intro hfr
  obtain ⟨ℓ, ⟨m, hU⟩, hL⟩ := (hfr.and_eventually (h ((1 + C) * Real.exp (D * t₀)))).exists
  obtain ⟨β, ⟨n, hn, h2, hlo, hhi, i, hlev⟩, hS⟩ := (hL.and_eventually hU).exists
  obtain ⟨ι, g₀, E, hZ, -, hc⟩ := hS n hn h2 hlo hhi i
  obtain ⟨S, hSD, hK⟩ := hlev ι g₀ E hZ
  have hcard := EndpointAudit.card_mul_exp_le_of_count ht₀ hc S hSD
  have h1 := mul_lt_mul_of_pos_right hK (Real.exp_pos (-(D * t₀)))
  rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at h1
  linarith

end NoGo

section Carriers

/-- **The tension-floor run fails**: under `ZeroFluxLevelsUnbounded 2 D`, (V) with
`TensionFloor.TensionFloorCountAt`, frequently in `ℓ`, is false at every `c, c', σ ≥ 0`, `t₀ ≥ 0`
(`TensionFloor.uniformGlueball_of_tensionFloorCount`). -/
theorem not_tensionFloorRun {D σ A c c' t₀ C : ℝ} {X : TensionFloor.Extent} (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hσ : 0 ≤ σ) (ht₀ : 0 ≤ t₀) (h : ZeroFluxLevelsUnbounded 2 D) :
    ¬ ∃ᶠ ℓ in atTop, FluxCost.VortexCostAt σ A ℓ ∧ TensionFloor.TensionFloorCountAt X σ A c c' t₀ C ℓ :=
  fun hfr => not_frequently_uniformGlueball ht₀ h
    (hfr.mono fun _ hℓ => ⟨_, TensionFloor.uniformGlueball_of_tensionFloorCount hc hc' hσ hℓ.1 hℓ.2⟩)

/-- **The attraction run fails**: under `ZeroFluxLevelsUnbounded 2 D`, (V) with
`AttractCost.AttractAt`, frequently in `ℓ`, is false at every `c, c', σ ≥ 0`, `t₀ ≥ 0`
(`AttractCost.uniformGlueball_of_attract`). -/
theorem not_attractRun {D σ A c c' t₀ C : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c') (hσ : 0 ≤ σ) (ht₀ : 0 ≤ t₀)
    (h : ZeroFluxLevelsUnbounded 2 D) :
    ¬ ∃ᶠ ℓ in atTop, FluxCost.VortexCostAt σ A ℓ ∧ AttractCost.AttractAt σ A c c' t₀ C ℓ :=
  fun hfr => not_frequently_uniformGlueball ht₀ h
    (hfr.mono fun _ hℓ => ⟨_, AttractCost.uniformGlueball_of_attract hc hc' hσ hℓ.1 hℓ.2⟩)

/-- **The scale-control run fails**: under `ZeroFluxLevelsUnbounded 2 D`, `¬ ScaleControlRun`
(`ScaleControl.uniformGlueball_of_scaleControlAt` at the rate `diagRate c c' σ δ (2ℓ)`, which varies with `ℓ`). -/
theorem not_scaleControlRun {D : ℝ} (h : ZeroFluxLevelsUnbounded 2 D) : ¬ MassGap.ScaleControlRun := by
  rintro ⟨c, c', σ, δ, α, V, D', B, t₀, Cc, m, Co, ℓ₀, -, -, -, -, -, hfr⟩
  obtain ⟨ℓ, hR⟩ := hfr.exists
  exact not_frequently_uniformGlueball hR.t₀_nonneg h (hfr.mono fun _ hℓ =>
    ⟨_, ScaleControl.uniformGlueball_of_scaleControlAt (ScaleControlRun.scaleControlAt_of_runAt hℓ)⟩)

/-- **The `SU(2)` multiscale endpoint fails**: under `ZeroFluxLevelsUnbounded 2 D`, `¬ MultiScale.Endpoint`
(`MultiScale.endpoint_iff_run`). -/
theorem not_multiScaleEndpoint {D : ℝ} (h : ZeroFluxLevelsUnbounded 2 D) : ¬ MultiScale.Endpoint :=
  fun hE => not_scaleControlRun h (MultiScale.endpoint_iff_run.1 hE)

end Carriers

end MassGap.InputAudit

end

#print axioms MassGap.InputAudit.not_frequently_uniformGlueball
#print axioms MassGap.InputAudit.not_tensionFloorRun
#print axioms MassGap.InputAudit.not_attractRun
#print axioms MassGap.InputAudit.not_scaleControlRun
#print axioms MassGap.InputAudit.not_multiScaleEndpoint
