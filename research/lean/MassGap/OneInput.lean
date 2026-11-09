import Mathlib
import MassGap.ConstantPhysicsLine
import MassGap.StrongAnchor
import MassGap.DisclosureFloor

/-!
# MassGap.OneInput — the root at `SU(N)` from the bridge and the one residual the tree does not prove

The root `ClayStatementG.ClayStatementOf (SU N)` asks for a measured tower `βs` (`MeasTowerG`) and every clause of
`ClayStatementAtP` at the schedule along `βs`. Every capstone in the tree that concludes it takes the bridge
(`StrongEnd N`, or the stronger `StrongAnchor.NoStall N ⇔ DisclosureFloor.NoCriticalPoint N`) together with two
further inputs along the coupling towers near `0⁺`: an ultraviolet input (`∃ μ, UVConverges N βs id μ`, or the
stronger `ScaleLightCone.ZoomSettlesUV N βs`) and an existence bundle (`ConstantPhysicsLine.ExistAlong N βs`, or
one of the bundles that imply it: `OpenAlong`, `OpenAlongR`, `OpenAlongW`, `CoreInputsAlong*`, `FlowInputsAlong`,
`BlFamCoreAlong`). The one capstone without the bridge, `ConsolidatedRoot.clayStatementOf_of_flow`, takes
`SUNFromScale.FlowInputsN N` and `MeasuredTower.AsymScalingG (SU N) R` instead. No theorem in the tree concludes
any of the ultraviolet inputs, any of the existence bundles, `FlowInputsN` or `AsymScalingG`; each is reached only
from another bundle of the same kind.

This module composes the root from the bridge and the weakest form of what remains. Declarations are in the
namespace `MassGap.OneInput`.

## What is derived (proved)

Along one coupling tower `βs` at a window coupling `u₀` in the seed basin, the observer's transfer gap at step `0`
(`CouplingTower.observerGap_along`) and `AbelianGenG (SU N)` (`AbelianGen.abelianGenG_SU`) are proved, and
`ClayGFinal.clayStatementOf_of_noNTAlong` derives the Hamiltonian and spectral gaps, the non-triviality clauses,
`OS2`/`OS4`, the link and observer generation. What it still needs at that tower is `MeasTowerG (SU N) βs` and
`ExistAlong N βs`. The bridge gives the towers at every window coupling near `0⁺`
(`TowerParamFree.vanishing_iff_towers`).

* `clayStatement_of_strongEnd`: `StrongEnd N` and the residual `R` give `ClayStatementOf (SU N)`, where `R` asks,
  at window couplings arbitrarily close to `0⁺` (frequently, not eventually), that every coupling tower there is a
  measured tower carrying `ExistAlong`.
* `clayStatement_of_noCriticalPoint`: the same from `DisclosureFloor.NoCriticalPoint N`
  (`StrongAnchor.strongEnd_of_noStall ∘ DisclosureFloor.noStall_iff_noCriticalPoint`).
* `residual_of_reads`: the inputs of `ConstantPhysicsLine.clayStatementOf_of_reads` other than the bridge, (UV)
  and `ExistAlong` eventually near `0⁺`, give `R`. So `R` is implied by what the capstones that take the bridge ask; it
  asks the measured tower in place of the convergence of the window reading (`MeasTowerG` is the band
  `c a_k ≤ mU ≤ 2 c a_k`, which (UV) gives with the proved confinement `GapReadsTensorProved.confinedAt`
  through `CouplingTower.measTowerG_of_confinedAt_uv`), and it asks it only frequently near `0⁺`.
* `clayStatementOf_of_reads'`: `clayStatement_of_strongEnd` read at the tree's input form, as a check that the
  composition reproduces `ConstantPhysicsLine.clayStatementOf_of_reads`.

## What remains, plainly

The final hypothesis list of `clayStatement_of_strongEnd` is two inputs, not one:

1. the bridge, `StrongEnd N`;
2. the residual `R`, which carries two distinct contents under one quantifier: the measured tower along the
   towers (the ultraviolet side: the measured unit mass stays in the band `c a_k ≤ mU ≤ 2 c a_k` along the tower;
   the floor in window units is proved, `FinalBridge.windowReading_floor`, the upper half is not), and `ExistAlong` (the existence clauses of the
   continuum limit: class moments, physical range, the mixing with its Riemann, tie, covariance and channel
   clauses, the kernel with its asymptotic-freedom coefficient, non-Gaussianity, the Ward identity, the
   composites with their data, `OS` and link, and the cross reading). Read as clauses, the hypotheses are
   the bridge, the ultraviolet input, the existence input. Writing `R` as one hypothesis is not a fold of the
   second and third.

`R` keeps `∀ βs` over the towers at `u₀`, so the bridge does the work of producing a tower. The form with `∃ βs`
in its place would carry the tower itself and with it the bridge (`ConstantPhysicsLine.frequently_towers_iff`);
it is `ConstantPhysicsLine.LineOfConstantPhysics N`, a bundle of the same three inputs.

DERIVED (module-wide): `0` the limit `0⁺` of the window coupling; `2` the least rank of `SU(N)` and the base of
`log 2`. Inherited, not derived here: `1/1000` the seed of `DoublingSharp`, which `CouplingTower.observerGap_along`
and `GapReadsTensorProved.confinedAt` fix; it enters only `ConstantPhysicsLine.seed_near` and `ConstantPhysicsLine.clayStatementOf_of_tower`,
used to pick one `u₀` from a frequent set, and appears in no public statement. `log 2` the window rate of
`CouplingTower.windowGap`, inherited through `GapReadsTensorProved.confinedAt`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.OneInput

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayTreeG
  MassGap.ClayStatementG MassGap.ClayWiringG MassGap.FlowG MassGap.TimeGroupG
  MassGap.EnergyBoundG MassGap.ObserverOSG MassGap.ObserverLinkedG MassGap.SymPlaqG
  MassGap.InputsG MassGap.CompReduceG MassGap.LinkReduce MassGap.LinkReduceG MassGap.SUInputs
  MassGap.ClayGFinal Filter
open scoped Topology Matrix
open MassGap.MeasuredTower (schedAlongG MeasTowerG)
open MassGap.MeasuredSpacing (schedOS_alongG)
open MassGap.CouplingTower (StrongEnd CouplingTower UVConverges)
open MassGap.ConstantPhysicsLine (ExistAlong seed_near clayStatementOf_of_tower)

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

/-- **The root at `SU(N)` from the bridge and the residual.** `StrongEnd N` gives a coupling tower at every window
coupling near `0⁺` (`TowerParamFree.vanishing_iff_towers`); the residual, at window couplings arbitrarily close
to `0⁺`, makes every such tower a measured tower carrying `ExistAlong`; one such coupling in the seed basin gives
the root (`clayStatementOf_of_tower`). The residual carries two open contents, the ultraviolet input and the
existence input (module docstring). DERIVED: `0` the limit `0⁺`; `2` the least rank. -/
theorem clayStatement_of_strongEnd (hS : StrongEnd N)
    (hR : ∃ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      MeasTowerG (MassGap.SUN.SU N) βs ∧ ExistAlong N βs) :
    ClayStatementOf (MassGap.SUN.SU N) := by
  have htow : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∃ βs : ℕ → ℝ, CouplingTower N u₀ βs id :=
    (TowerParamFree.vanishing_iff_towers (Fact.out : 2 ≤ N)).mp
      ((StrongEndVanishing.strongEnd_iff_vanishing (NeZero.ne N)).mp hS)
  obtain ⟨u, ⟨hRu, βs, hT⟩, -, hu⟩ := ((hR.and_eventually htow).and_eventually seed_near).exists
  obtain ⟨hM, hE⟩ := hRu βs hT
  exact clayStatementOf_of_tower hu hT hM hE

/-- **The root at `SU(N)` from no critical point and the residual.** `DisclosureFloor.NoCriticalPoint N` is
`StrongAnchor.NoStall N` (`DisclosureFloor.noStall_iff_noCriticalPoint`), which gives `StrongEnd N`
(`StrongAnchor.strongEnd_of_noStall`, the anchor proved). DERIVED: `0` the limit `0⁺`; `2` the least rank. -/
theorem clayStatement_of_noCriticalPoint (hC : DisclosureFloor.NoCriticalPoint N)
    (hR : ∃ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      MeasTowerG (MassGap.SUN.SU N) βs ∧ ExistAlong N βs) :
    ClayStatementOf (MassGap.SUN.SU N) :=
  clayStatement_of_strongEnd
    (StrongAnchor.strongEnd_of_noStall (NeZero.ne N)
      ((DisclosureFloor.noStall_iff_noCriticalPoint (NeZero.ne N)).mpr hC)) hR

/-- **The tree's inputs give the residual.** (UV) and `ExistAlong` along the towers eventually near `0⁺` (the
inputs of `ConstantPhysicsLine.clayStatementOf_of_reads` besides the bridge) give the residual: the measured tower
from (UV) and the proved confinement (`CouplingTower.measTowerG_of_confinedAt_uv`,
`GapReadsTensorProved.confinedAt`), and eventually gives frequently on `𝓝[>] 0`. DERIVED: `0` the limit `0⁺`;
`2` the least rank and the base of `log 2`. -/
theorem residual_of_reads
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ∃ μ : ℝ, UVConverges N βs id μ)
    (hE : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ExistAlong N βs) :
    ∃ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      MeasTowerG (MassGap.SUN.SU N) βs ∧ ExistAlong N βs := by
  refine ((hUV.and hE).and seed_near).frequently.mono fun u hu' βs hT => ?_
  obtain ⟨⟨h1, h2⟩, _, hu⟩ := hu'
  obtain ⟨μ, hμ⟩ := h1 βs hT
  exact ⟨CouplingTower.measTowerG_of_confinedAt_uv hT (Real.log_pos one_lt_two)
    (GapReadsTensorProved.confinedAt (Fact.out : 2 ≤ N) hu) hμ, h2 βs hT⟩

/-- **Check: the composition reproduces `ConstantPhysicsLine.clayStatementOf_of_reads`.** DERIVED: `0` the limit
`0⁺`; `2` the least rank. -/
theorem clayStatementOf_of_reads' (hS : StrongEnd N)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ∃ μ : ℝ, UVConverges N βs id μ)
    (hE : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ExistAlong N βs) :
    ClayStatementOf (MassGap.SUN.SU N) :=
  clayStatement_of_strongEnd hS (residual_of_reads hUV hE)

end MassGap.OneInput

end

#print axioms MassGap.OneInput.clayStatement_of_strongEnd
#print axioms MassGap.OneInput.clayStatement_of_noCriticalPoint
#print axioms MassGap.OneInput.residual_of_reads
#print axioms MassGap.OneInput.clayStatementOf_of_reads'
