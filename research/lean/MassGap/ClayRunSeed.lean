import Mathlib
import MassGap.ClusterRoute
import MassGap.EndpointAudit

/-!
# MassGap.ClayRunSeed — the cluster capstone with the run seed in the gap slot

`ClusterRoute.NarrowInputsAtCL` carries, per `N`, the gap input `RunSeedN.EndpointN N` and uses it only
through `RunSeedN.runSeed_of_endpointN` (in `ClusterRoute.clayInputsN_of_narrowAtCL`). This module states the
cluster capstone with the gap slot at its weakest input, `WDeltaRun.RunSeed N`. Declarations are in the namespace
`MassGap.ClayRunSeed`.

* `NarrowAtG N hN2 W r G`: the inputs of `ClusterRoute.NarrowInputsAtCL` with the gap slot `G`.
* `NarrowInputsAtRS N hN2 W r`: `NarrowAtG` at `G = WDeltaRun.RunSeed N`.
* **`clayInputsN_of_narrowAtRS`** and the capstone **`clayStatement_of_narrowAtRS`**: `∃ W r, NarrowInputsAtRS N hN2 W r`
  at every `N ≥ 2` gives `MassGap.ClayStatementDy`.
* **`narrowInputsAtRS_of_endpointS`**: the single-window endpoint `EndpointAudit.EndpointS N` in the gap slot
  (`EndpointAudit.runSeed_of_endpointS`).
* **`narrowInputsAtRS_of_CL`**: `NarrowInputsAtCL` gives `NarrowInputsAtRS` (`RunSeedN.runSeed_of_endpointN`).

`RunSeed N` asks, at one physical scale and eventually in `β`, that the doubling defect be at most `1/1000`; it fixes
no heat-trace time over unboundedly many windows, so `EndpointAudit.not_endpointN_of_levels_unbounded` does not
reach it.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` the least colour count; `0` the plane and the reference step.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ClayRunSeed

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP
open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup MassGap.ContinuumReconstruction
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData MassGap.ReflAvg
  MassGap.MixConvRP MassGap.MultiScaleAll MassGap.CompositesRen MassGap.CompositesRenAll
  MassGap.MultiScaleOS MassGap.ApproxFromExpand MassGap.StrongExpand MassGap.CovFromFlow
  MassGap.SU2Best MassGap.NondegFromProxy MassGap.NonGaussFromScale
  MassGap.ProxyGenObserver MassGap.ProxyBoundFromScale MassGap.ObserverFlowSUN MassGap.FlowChoice
  MassGap.ProxyGenLimN MassGap.FlowCovN MassGap.ApproxJoint MassGap.ClayNarrow
  MassGap.ObserverMultigrid MassGap.ClayNarrowMG MassGap.ScalePC MassGap.ScalePM MassGap.ClusterRoute
open MassGap.ScaleControlFull (zOne)

variable {N : ℕ}

/-- **The per-`N` inputs of the cluster route with gap slot `G`**: `ClusterRoute.NarrowInputsAtCL` with
`RunSeedN.EndpointN N` replaced by `G`. DERIVED: `2` the least colour count; `0` the plane and the reference step. -/
def NarrowAtG (N : ℕ) (hN2 : 2 ≤ N) (W : ConfFlow N) (r : ℝ) (G : Prop) : Prop :=
  haveI : NeZero N := ⟨by omega⟩
  (Φ0 W).PhysRange r ∧
  ∃ (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)),
    SubstrateCoreCL W (ZCanon.zFix N zri zwe) b Wf
      ∧ ExpandStrong Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ ClusterPM Wf cf
      ∧ CovC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ WardT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe))
      ∧ CompNondeg (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ (∀ P, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
          (mixKG hN2 W (CRen N (ZCanon.zFix N zri zwe) μ) r) (gramF hN2 W r) P)
      ∧ (∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (ne_zero_of_two_le hN2) ℓ)
      ∧ G

/-- **The gap slot is monotone**: `G → G'` carries `NarrowAtG … G` to `NarrowAtG … G'`. -/
theorem NarrowAtG.mono {hN2 : 2 ≤ N} {W : ConfFlow N} {r : ℝ} {G G' : Prop} (hG : G → G')
    (h : NarrowAtG N hN2 W r G) : NarrowAtG N hN2 W r G' := by
  obtain ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hcl, hV, hW, hP, hB, h3, hEnd⟩ := h
  exact ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hcl, hV, hW, hP, hB, h3, hG hEnd⟩

/-- **The per-`N` inputs of the cluster route at the run seed**: `NarrowAtG` with gap slot
`WDeltaRun.RunSeed N`. DERIVED: `2` the least colour count. -/
def NarrowInputsAtRS (N : ℕ) (hN2 : 2 ≤ N) (W : ConfFlow N) (r : ℝ) : Prop :=
  haveI : NeZero N := ⟨by omega⟩
  NarrowAtG N hN2 W r (WDeltaRun.RunSeed N)

/-- **`NarrowInputsAtRS` gives the general-`N` bundle at `W`** (`ClusterRoute.approxK_of_beyond_covC_cl`,
`ClusterRoute.inputsAt_of_covC_phys_cl`). DERIVED: `2` the least colour count. -/
theorem clayInputsN_of_narrowAtRS (hN2 : 2 ≤ N) {W : ConfFlow N} {r : ℝ}
    (h : NarrowInputsAtRS N hN2 W r) : SUNBest.ClayInputsN N hN2 := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hcl, hV, hW, hP, hB, h3, hRS⟩ := h
  obtain ⟨t, C, G, I⟩ := inputsAt_of_covC_phys_cl hN2 hri hwe S hE hcl hV hW hP hphys
    (approxK_of_beyond_covC_cl hN2 S hE hcl hV hP hphys hB) h3 hRS
  exact ⟨W, r, t, |C|, zri, zwe, μ, G, I⟩

/-- **`ClayStatementDy` from `NarrowInputsAtRS` at some observer and margin, at every `N ≥ 2`**
(`SUNBest.clayStatement_of_inputs`). DERIVED: `2` the least colour count. -/
theorem clayStatement_of_narrowAtRS
    (h : ∀ (N : ℕ) (hN2 : 2 ≤ N), ∃ (W : ConfFlow N) (r : ℝ), NarrowInputsAtRS N hN2 W r) :
    MassGap.ClayStatementDy :=
  SUNBest.clayStatement_of_inputs fun N hN2 => by
    obtain ⟨W, r, hA⟩ := h N hN2
    exact clayInputsN_of_narrowAtRS hN2 hA

/-- **The single-window endpoint in the gap slot gives `NarrowInputsAtRS`**
(`EndpointAudit.runSeed_of_endpointS`). DERIVED: `2` the least colour count. -/
theorem narrowInputsAtRS_of_endpointS (hN2 : 2 ≤ N) {W : ConfFlow N} {r : ℝ}
    (h : haveI : NeZero N := ⟨by omega⟩; NarrowAtG N hN2 W r (EndpointAudit.EndpointS N)) :
    NarrowInputsAtRS N hN2 W r :=
  haveI : NeZero N := ⟨by omega⟩
  NarrowAtG.mono EndpointAudit.runSeed_of_endpointS h

/-- **`NarrowInputsAtCL` gives `NarrowInputsAtRS`** (`RunSeedN.runSeed_of_endpointN`). DERIVED: `2` the least
colour count. -/
theorem narrowInputsAtRS_of_CL (hN2 : 2 ≤ N) {W : ConfFlow N} {r : ℝ}
    (h : NarrowInputsAtCL N hN2 W r) : NarrowInputsAtRS N hN2 W r :=
  haveI : NeZero N := ⟨by omega⟩
  NarrowAtG.mono RunSeedN.runSeed_of_endpointN h

end MassGap.ClayRunSeed

end

#print axioms MassGap.ClayRunSeed.NarrowAtG.mono
#print axioms MassGap.ClayRunSeed.clayInputsN_of_narrowAtRS
#print axioms MassGap.ClayRunSeed.clayStatement_of_narrowAtRS
#print axioms MassGap.ClayRunSeed.narrowInputsAtRS_of_endpointS
#print axioms MassGap.ClayRunSeed.narrowInputsAtRS_of_CL
