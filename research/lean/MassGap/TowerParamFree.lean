import Mathlib
import MassGap.StrongEndVanishing
import MassGap.GapReadsTensorProved

/-!
# MassGap.TowerParamFree — the coupling tower with no seed in its statements

This module states the coupling tower, the weak end (W) and confinement (IR) with no threshold on the window
coupling: each holds for every window coupling near `0` (`∀ᶠ u₀ in 𝓝 0`), or near `0` from above
(`∀ᶠ u₀ in 𝓝[>] 0`) where the tower needs a positive value, and the strong end enters only as the vanishing read
of `StrongEndVanishing`. How small "near" is stays inside the proofs.
Declarations are in the namespace `MassGap.TowerParamFree`.

* `weakEnd_near_zero`: (W) at every window coupling near `0`, for `2 ≤ N`.
* `confinedAt_near_zero`: (IR) at rate `log 2` at every window coupling near `0`; the link is
  `GapReadsTensorProved.gapReadsTensor`.
* `vanishing_iff_towers`: the window coupling vanishes along the windows at arbitrarily large `β` exactly when
  coupling towers exist at every positive window coupling near `0`.
* `measuredTower_of_vanishing`: if the window coupling vanishes at arbitrarily large `β` and (UV) holds along the
  towers near `0`, then at every positive window coupling near `0` a coupling tower is a measured tower with the
  per-step gap.

DERIVED (module-wide): `0` the limit of the window coupling, the signs, and the plane and time axis of
`periodicGaugeInvDataG`; `2` the least rank, and in `2 log 2` the first halving of `dySpacingG` and the window
base; `1` the reference coupling of `dySpacingG`. Proof-internal constant: `1/1000` the sharp seed of
`DoublingSharp`, used only to exhibit the neighbourhood.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.TowerParamFree

open Filter Topology
open MassGap MassGap.ZoomSelfScale MassGap.MeasuredTower MassGap.MeasuredSpacing MassGap.ClayTreeG
  MassGap.FlowG MassGap.TimeGroupG MassGap.PeriodicReduceG MassGap.FlowClusterG
open MassGap.CouplingTower (windowCoupling StrongEnd WeakEnd CouplingTower ConfinedAt UVConverges)

variable {N : ℕ}

/-- The seed's half-line is a neighbourhood of `0`. Proof-internal: `1/1000` the seed. -/
private theorem seed_mem_nhds : Set.Iic (1 / 1000 : ℝ) ∈ 𝓝 (0 : ℝ) :=
  Iic_mem_nhds (by norm_num)

/-- The positive part of the seed's half-line is a right neighbourhood of `0`. DERIVED: `0` the sign.
Proof-internal: `1/1000` the seed. -/
private theorem seed_mem_nhdsGT : Set.Ioc (0 : ℝ) (1 / 1000) ∈ 𝓝[>] (0 : ℝ) :=
  inter_mem (self_mem_nhdsWithin) (nhdsWithin_le_nhds seed_mem_nhds)

/-- **(W) near `0`**: for `2 ≤ N`, the weak end holds at every window coupling near `0`.
DERIVED: `2` the least rank; `0` the limit. -/
theorem weakEnd_near_zero (hN : 2 ≤ N) : ∀ᶠ u₀ in 𝓝 (0 : ℝ), WeakEnd N u₀ := by
  filter_upwards [seed_mem_nhds] with u hu
  exact WeakEndProved.weakEnd hN hu

/-- **(IR) near `0`**: confinement at rate `log 2` holds at every window coupling near `0`.
DERIVED: `2` the least rank and `log 2` the window rate; `0` the limit. -/
theorem confinedAt_near_zero [NeZero N] (hN2 : 2 ≤ N) :
    ∀ᶠ u₀ in 𝓝 (0 : ℝ), ConfinedAt N u₀ (Real.log 2) := by
  filter_upwards [seed_mem_nhds] with u hu
  exact GapReadsTensorProved.confinedAt hN2 hu

/-- **The vanishing read is the towers near `0`**: the window coupling vanishes along the windows at
arbitrarily large `β` exactly when, at every positive window coupling near `0`, a coupling tower exists.
DERIVED: `2` the least rank; `0` the limit and the sign. -/
theorem vanishing_iff_towers (hN : 2 ≤ N) :
    (∃ᶠ β in atTop, Tendsto (windowCoupling N β) atTop (𝓝 0)) ↔
      ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∃ βs : ℕ → ℝ, CouplingTower N u₀ βs id :=
  by
  rw [← StrongEndVanishing.strongEnd_iff_vanishing (by omega)]
  constructor
  · intro hS
    filter_upwards [seed_mem_nhdsGT] with u ⟨hu0, hu⟩
    exact WeakEndProved.couplingTower_of_strongEnd hN hu0 hu hS
  · intro h
    obtain ⟨u, ⟨βs, hT⟩, -, hu⟩ := (h.and seed_mem_nhdsGT).exists
    exact CouplingTower.strongEnd_of_couplingTower (by omega) hu hT

/-- **The vanishing read and (UV) give measured towers near `0`**: if the window coupling vanishes at
arbitrarily large `β` and (UV) holds along the coupling towers at every positive window coupling near `0`, then
at every positive window coupling near `0` some coupling tower is a measured tower with the per-step gap.
DERIVED: `2` the least rank and the first halving of `dySpacingG`, `log 2` the window rate; `1` the
reference coupling of `dySpacingG`; `0` the limit, the signs, and the plane and time axis. -/
theorem measuredTower_of_vanishing [NeZero N] [Fact (2 ≤ N)]
    (hV : ∃ᶠ β in atTop, Tendsto (windowCoupling N β) atTop (𝓝 0))
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ),
      ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ∃ μ : ℝ, UVConverges N βs id μ) :
    ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∃ βs : ℕ → ℝ, CouplingTower N u₀ βs id ∧
      MeasTowerG (MassGap.SUN.SU N) βs ∧
      ∀ᶠ k in atTop, ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        TransferGap.GapAt (periodicGaugeInvDataG (MassGap.SUN.SU N) 0 0 (βs k)) r ∧
        2 * Real.log 2 / GaugeRunning.aRunG (MassGap.SUN.SU N) 1
          ≤ -Real.log r / dySpacingG (MassGap.SUN.SU N) k := by
  have hS : StrongEnd N := (StrongEndVanishing.strongEnd_iff_vanishing (NeZero.ne N)).mpr hV
  filter_upwards [seed_mem_nhdsGT, hUV] with u ⟨hu0, hu⟩ hu'
  exact GapReadsTensorProved.measuredTower_of_strongEnd hu0 hu hS hu'

end MassGap.TowerParamFree

#print axioms MassGap.TowerParamFree.weakEnd_near_zero
#print axioms MassGap.TowerParamFree.confinedAt_near_zero
#print axioms MassGap.TowerParamFree.vanishing_iff_towers
#print axioms MassGap.TowerParamFree.measuredTower_of_vanishing
