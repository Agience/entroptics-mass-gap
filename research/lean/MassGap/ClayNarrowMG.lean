import Mathlib
import MassGap.ClayNarrow
import MassGap.ObserverMultigrid

/-!
# MassGap.ClayNarrowMG — the `SU(N)` bundle at any observer of bounded reach

`NarrowInputsAt N hN2 W r` is the per-`N` bundle of `ClayNarrow.NarrowInputsN` at an arbitrary observer `W`
with `(Φ0 W).PhysRange r`, and `clayInputsN_of_narrowAt` reduces it to `SUNBest.ClayInputsN N hN2`. The observer
`ObserverFlowSUN.sunFam` (`narrowInputsAt_of_narrow`) and the multigrid observer `ObserverMultigrid.mgFam`
(`NarrowInputsMG`, `inputsAt_of_narrowMG`) are instances. No `ClayStatement` capstone is stated from these
bundles: each carries `RunSeedN.EndpointN N`, refuted by `EndpointAudit.not_endpointN_of_levels_unbounded`
under the argued growth of the zero-flux level count; `ClayRunSeed.clayStatement_of_narrowAtRS` takes
`RunSeed N` in that slot. Declarations are in the namespace `MassGap.ClayNarrowMG`.

## The per-`N` inputs of `NarrowInputsMG N hN2`

Witnesses: `c, hc0, hc, m` (`1 ≤ m`), `s₀, r` (`0 ≤ s₀ ≤ r`), `zri, zwe` (nowhere zero), `μ`, `b`, `Wf`, `cf`;
`W = mgFam hN2 c hc0 hc m s₀`, `z = ZCanon.zFix N zri zwe`. The clauses are those of `ClayNarrow.NarrowInputsN`
at this `W`: `SubstrateCoreAt W z b Wf`, `ExpandStrong Wf cf z μ`, `CoefBound cf`, `CovC (CRen N z μ)`,
`WardT (rhoD (fR N) z)`, `CompNondeg (CRen N z μ)`, the clause of `ApproxK` beyond the margin `r` at `W`,
`∃ ℓ > 0, ThreePointAtScale ℓ`, and `RunSeedN.EndpointN N`. The margin may equal the reach
(`s₀ ≤ r`), as `ObserverMultigrid.mgFam_physRange` allows.

## How the chain reads the observer

The `SU(N)` chain reads the observer only through `PhysRange r` of `Φ0 W` and through the `scale` field of the
substrate core (`CompositesRenAll.uv_of_scale`, `ClaySUFinal.classMoments_of_siteExp`, both at any `W`).
`ClayNarrow.approxK_of_beyond_covC` is stated at any `W` with a `PhysRange` hypothesis and is used as is.
`FlowCovN.inputsAt_of_covC` is stated at `sunFam`; `inputsAt_of_covC_phys` is its proof at any `W`, with
`sunFam_physRange` replaced by a hypothesis `(Φ0 W).PhysRange r`. At `mgFam` that hypothesis is
`ObserverMultigrid.mgFam_physRange hN2 hc0 hc m hs0 hr`.

## What is proved

* `inputsAt_of_covC_phys`: `SUNBest.InputsAt hN2 W r t |C| zri zwe μ G` for some `t, C, G` from the substrate,
  flow and target clauses, `PhysRange r`, `ApproxK`, the three-point clause and `WDeltaRun.RunSeed N`, at any
  `W`.
* `NarrowInputsAt N hN2 W r`: the nine clauses of `ClayNarrow.NarrowInputsN` at an arbitrary observer `W` and
  margin `r`, together with `(Φ0 W).PhysRange r`; the remaining witnesses `zri, zwe, μ, b, Wf, cf` as there.
* `clayInputsN_of_narrowAt`: `NarrowInputsAt N hN2 W r → SUNBest.ClayInputsN N hN2`, witnessed at `W`.
* `narrowInputsAt_of_narrowMG`: `NarrowInputsMG N hN2` gives `NarrowInputsAt N hN2 (mgFam hN2 c hc0 hc m s₀) r`
  for some witnesses (`ObserverMultigrid.mgFam_physRange`).
* `narrowInputsAt_of_narrow`: `ClayNarrow.NarrowInputsN N hN2` gives
  `NarrowInputsAt N hN2 (sunFam hN2 c hc0 hc s₀) r` for some witnesses (`ObserverFlowSUN.sunFam_physRange`).
* `inputsAt_of_narrowMG`: `NarrowInputsMG N hN2 → SUNBest.ClayInputsN N hN2`, witnessed at
  `W = mgFam hN2 c hc0 hc m s₀`.

## The scale input at this observer

The reduction `inputsAt_of_narrowMG` is a valid implication. Its scale input, the `top` and `scale` fields of
`SubstrateCoreAt (mgFam hN2 c hc0 hc m s₀) z b Wf`, reduces at `b = 1` to the observer's moment condition
`ObserverMultigrid.MW (mgFam hN2 c hc0 hc m s₀)` (`ScaleSatisfiable.scaleControlAll_one_iff`, restated as
`ObserverMultigrid.mw_iff`; `ObserverMultigrid.substrateCoreAt_of_MW` builds the core from `MW` and `af`).
`MW (mgFam …)` is a deterministic bound on the flowed origin plaquette at every input
(`BulkBound.facV_le_of_MW`), expected false by the π-flux argument of `BulkBound.not_MW_blFam` (not written
at `mgFam`); the scale input at `b < 1` is open.

Three properties of the observer bear on it (`ObserverMultigrid` §3):

* The stride-`d` staple is a thin `d × 1` rectangle, not a block average; at the coarsest level
  (`d ≈ s₀/(2 m a_k)`) one long thin loop carries the full edge weight `c`. That the levels give a smoothing
  kernel of physical width `s₀` is not shown.
* `¬ ∀ᶠ k, (mgFam hN2 c hc0 hc m s₀).V k = id` is not proved; `ObserverMultigrid.mgFam_moves` gives a moved
  configuration only at `m = 1`, a step with `J_k = 1`, and `c > 0`. `ScaleIdentityNoGo.not_substrateCoreAt_of_id`
  makes `SubstrateCoreAt W z b Wf` false at every eventually-identity `W`, so `MW (mgFam …)` can hold only where
  that case is excluded.
* At `s₀ = 0` every member is the identity (`ObserverMultigrid.mgFam_V_of_lt`); at `c = 0` the block step
  returns its link at every stride (as `ConstFlowN.sunStep_of_eq_zero` at `sunFam`; not restated for `mgFam`),
  so `mgFam` is then the identity (argued for `c = 0`) and `SubstrateCoreAt` fails by
  `ScaleIdentityNoGo.not_substrateCoreAt_of_id`; a witness of `NarrowInputsMG` needs `c > 0` and `s₀ > 0`.

`mgFam` holds no link at its bare value, so the held-boundary mechanism that `SunFamLeak` identifies at
`sunFam` is absent. `SunFamLeak.not_substrateCoreAt_of_plaqLeak` still applies at `mgFam`, as at any
`ConfFlow`; whether `SunFamLeak.PlaqLeak` holds at `mgFam` is not settled.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` the least colour count; `0` the lower end of the observer's scale and the plane;
`1` the least number of steps per level; `12` the bound of the block-step flow.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ClayNarrowMG

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
  MassGap.ObserverMultigrid

variable {N : ℕ}

/-- **`FlowCovN.inputsAt_of_covC` at any observer with `PhysRange r`**: module docstring.
DERIVED: `2` the least colour count; `0` the lower end of the scale. -/
theorem inputsAt_of_covC_phys (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {r : ℝ}
    {zri zwe : ℕ → ℝ} (hri : ∀ k, zri k ≠ 0) (hwe : ∀ k, zwe k ≠ 0) {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCoreAt W (ZCanon.zFix N zri zwe) b Wf)
    (hE : ExpandStrong Wf cf (ZCanon.zFix N zri zwe) μ) (hcb : CoefBound cf)
    (hV : CovC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ))
    (hW : WardT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe)))
    (hP : CompNondeg (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ))
    (hphys : (Φ0 W).PhysRange r)
    (hA : ApproxK (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
      (mixKG hN2 W (CRen N (ZCanon.zFix N zri zwe) μ) r) (gramF hN2 W r))
    (h3 : ∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (ne_zero_of_two_le hN2) ℓ)
    (hfar : WDeltaRun.RunSeed N) :
    ∃ (t C : ℝ) (G : ℝ → ℝ), SUNBest.InputsAt hN2 W r t |C| zri zwe μ G := by
  obtain ⟨t, C, ht, hS⟩ := uv_of_scale S.b_pos S.top S.scale
  have hU := ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) W ht hS
  obtain ⟨G, hK, hAF⟩ := S.af
  obtain ⟨ℓ, hℓ, h3'⟩ := h3
  exact ⟨t, C, G,
    { t_pos := ht
      moments := hU
      phys := hphys
      far := hfar
      hri := hri
      hwe := hwe
      kernel := hK
      af := hAF
      low := obsLower_of_scale (ne_zero_of_two_le hN2) hℓ zri zwe h3'
      ward := hW
      comp := compOS_of_covC S hE hcb hV hP
      approx := hA }⟩

/-- **The per-`N` inputs at an arbitrary observer `W` and margin `r`**: `(Φ0 W).PhysRange r` and the nine
clauses of `ClayNarrow.NarrowInputsN` at `W`. Module docstring.
DERIVED: `2` the least colour count; `0` the plane and the reference step. -/
def NarrowInputsAt (N : ℕ) (hN2 : 2 ≤ N) (W : ConfFlow N) (r : ℝ) : Prop :=
  haveI : NeZero N := ⟨by omega⟩
  (Φ0 W).PhysRange r ∧
  ∃ (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)),
    SubstrateCoreAt W (ZCanon.zFix N zri zwe) b Wf
      ∧ ExpandStrong Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ CoefBound cf
      ∧ CovC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ WardT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe))
      ∧ CompNondeg (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ (∀ P, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
          (mixKG hN2 W (CRen N (ZCanon.zFix N zri zwe) μ) r) (gramF hN2 W r) P)
      ∧ (∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (ne_zero_of_two_le hN2) ℓ)
      ∧ RunSeedN.EndpointN N

/-- **`NarrowInputsAt` gives the general-`N` bundle at `W`** (`ClayNarrow.approxK_of_beyond_covC`,
`RunSeedN.runSeed_of_endpointN`, `inputsAt_of_covC_phys`). DERIVED: `2` the least colour count. -/
theorem clayInputsN_of_narrowAt (hN2 : 2 ≤ N) {W : ConfFlow N} {r : ℝ} (h : NarrowInputsAt N hN2 W r) :
    SUNBest.ClayInputsN N hN2 := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP, hB, h3, hEnd⟩ := h
  obtain ⟨t, C, G, I⟩ := inputsAt_of_covC_phys hN2 hri hwe S hE hC hV hW hP hphys
    (approxK_of_beyond_covC hN2 S hE hC hV hP hphys hB) h3 (RunSeedN.runSeed_of_endpointN hEnd)
  exact ⟨W, r, t, |C|, zri, zwe, μ, G, I⟩

/-- **The per-`N` inputs at the multigrid observer**: `ClayNarrow.NarrowInputsN` with
`sunFam hN2 c hc0 hc s₀` replaced by `mgFam hN2 c hc0 hc m s₀` (`1 ≤ m`) and `s₀ < r` relaxed to `s₀ ≤ r`.
Module docstring.
DERIVED: `2` the least colour count; `0` the lower end of the observer's scale; `1` the least number of steps
per level; `12` the bound of the block-step flow. -/
def NarrowInputsMG (N : ℕ) (hN2 : 2 ≤ N) : Prop :=
  haveI : NeZero N := ⟨by omega⟩
  ∃ (c : ℝ) (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ) (_ : 1 ≤ m) (s₀ r : ℝ)
    (_ : 0 ≤ s₀) (_ : s₀ ≤ r)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)),
    SubstrateCoreAt (mgFam hN2 c hc0 hc m s₀) (ZCanon.zFix N zri zwe) b Wf
      ∧ ExpandStrong Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ CoefBound cf
      ∧ CovC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ WardT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe))
      ∧ CompNondeg (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ (∀ P, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
          (mixKG hN2 (mgFam hN2 c hc0 hc m s₀) (CRen N (ZCanon.zFix N zri zwe) μ) r)
          (gramF hN2 (mgFam hN2 c hc0 hc m s₀) r) P)
      ∧ (∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (ne_zero_of_two_le hN2) ℓ)
      ∧ RunSeedN.EndpointN N

/-- **`NarrowInputsMG` gives the general bundle at `mgFam`** (`ObserverMultigrid.mgFam_physRange`).
DERIVED: `2` the least colour count; `12 = 2 · 6` the coupling bound of
`ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem narrowInputsAt_of_narrowMG (hN2 : 2 ≤ N) (h : NarrowInputsMG N hN2) :
    ∃ (c : ℝ) (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ) (s₀ r : ℝ),
      NarrowInputsAt N hN2 (mgFam hN2 c hc0 hc m s₀) r := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨c, hc0, hc, m, -, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP,
    hB, h3, hEnd⟩ := h
  exact ⟨c, hc0, hc, m, s₀, r, mgFam_physRange hN2 hc0 hc m hs0 hr, zri, zwe, hri, hwe, μ, b, Wf, cf,
    S, hE, hC, hV, hW, hP, hB, h3, hEnd⟩

/-- **`ClayNarrow.NarrowInputsN` gives the general bundle at `sunFam`** (`ObserverFlowSUN.sunFam_physRange`).
DERIVED: `2` the least colour count; `12 = 2 · 6` the coupling bound of
`ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem narrowInputsAt_of_narrow (hN2 : 2 ≤ N) (h : NarrowInputsN N hN2) :
    ∃ (c : ℝ) (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N)) (s₀ r : ℝ),
      NarrowInputsAt N hN2 (sunFam hN2 c hc0 hc s₀) r := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP,
    hB, h3, hEnd⟩ := h
  exact ⟨c, hc0, hc, s₀, r, sunFam_physRange hN2 hc0 hc hs0 hr, zri, zwe, hri, hwe, μ, b, Wf, cf,
    S, hE, hC, hV, hW, hP, hB, h3, hEnd⟩

/-- **`NarrowInputsMG` gives the general-`N` bundle at `mgFam`** (`narrowInputsAt_of_narrowMG`,
`clayInputsN_of_narrowAt`). DERIVED: `2` the least colour count. -/
theorem inputsAt_of_narrowMG (hN2 : 2 ≤ N) (h : NarrowInputsMG N hN2) : SUNBest.ClayInputsN N hN2 := by
  obtain ⟨c, hc0, hc, m, s₀, r, hA⟩ := narrowInputsAt_of_narrowMG hN2 h
  exact clayInputsN_of_narrowAt hN2 hA

end MassGap.ClayNarrowMG

end

#print axioms MassGap.ClayNarrowMG.inputsAt_of_covC_phys
#print axioms MassGap.ClayNarrowMG.clayInputsN_of_narrowAt
#print axioms MassGap.ClayNarrowMG.narrowInputsAt_of_narrowMG
#print axioms MassGap.ClayNarrowMG.narrowInputsAt_of_narrow
#print axioms MassGap.ClayNarrowMG.inputsAt_of_narrowMG
