import Mathlib
import MassGap.SU2Best
import MassGap.ObserverTheory
import MassGap.ClayStatementG

/-!
# MassGap.SUNBest — the general-`N` capstone, and `SU2Best` read through it

The `SU2Best` bundles are stated at `N = 2`. The chain they feed ends in
`CompositesRenAll.clayStatementAt_SU_ren_low`, which is stated for every `N ≥ 2` and takes the gap as
`WDeltaRun.RunSeed N`. Every `N = 2` restriction of `SU2Best` sits above that theorem: in the flow-side
layer (`ConfFlow 2`, `msProx`, `ScaleControlAll`, `ExpandStrong`, `FlowCov`, `FlowWard`, `ProxyGen`), in the
gap reduction (`MultiScale.Endpoint → ScaleControlRun → FluxCost.runSeed_two_iff_vortex → RunSeed 2`) and in
the observer (`ObserverChoice.obsW = FlowZero.apeFam`, a `ConfFlow 2`). This module states the general-`N`
capstone at the inputs of `clayStatementAt_SU_ren_low` with `z = ZCanon.zFix N zri zwe`, and proves that the
`SU2Best` inputs give that bundle at `N = 2`. It proves no new mathematics. Declarations are in the namespace
`MassGap.SUNBest`.

## 1. The bundle

`InputsAt hN2 W r t C zri zwe μ G` at `SU(N)`, observer `W`:

* `t_pos`, `moments : ClassMoments W (SymPlaqClass N) t C` — moments of the flowed energy density;
* `phys : PhysRange r` of `energy0 W (SymPlaqClass N)`;
* `far : WDeltaRun.RunSeed N` — the gap;
* `hri`, `hwe` — the renormalisation factors `zri`, `zwe` are nowhere zero;
* `kernel`, `af` — a two-point kernel `G` of the trace at `zFix N zri zwe` with the asymptotic-freedom
  coefficient;
* `low : ObsLower`, `ward : WardT` at `zFix N zri zwe`;
* `comp : CompOS (CRen N (zFix N zri zwe) μ)` — `ConvC ∧ OS0C ∧ OS1C ∧ CovC ∧ CompNondeg`;
* `approx : ApproxK` at `CRen N (zFix N zri zwe) μ`, `W`, `r`.

## 2. What is proved

* **`clayStatementAt_N_best`**: `InputsAt hN2 W …` gives `ClayStatementAt hN2 W (SymPlaqClass N)
  (symPlaq_refl N)` for every `N ≥ 2` (`clayStatementAt_SU_ren_low`, with `hz`, `hzS`, `hzP` from
  `ZCanon.zFix_ne`, `ZCanon.tendsto_zFix_sc`, `ZCanon.tendsto_zFix_ps`).
* `runSeed_of_bindingSU'`: the gap field from the split binding statement `ObserverTheory.BindingSU N σ A`
  (flux share and zero-flux defect, every `N`); `RunSeed N` is equivalent to it
  (`ObserverTheory.runSeed_iff_bindingSU`), so either form can fill `far`.
* `ClayInputsN N hN2`: `∃ W r t C zri zwe μ G, InputsAt hN2 W r t C zri zwe μ G`.
  `clayStatementSU_of_inputs`: it gives `ClayStatementG.ClayStatementSUDy N hN2`.
  **`clayStatement_of_inputs`**: `ClayInputsN` at every `N ≥ 2` gives `ClayStatementDy`, and
  `clayStatementClassical_SU_of_inputs` the `SU` component of `ClayStatementG.ClayStatementClassicalDy`.
* **`inputsAt_two_of_su2Best`**: the `SU2Best` inputs (`SubstrateAt obsW`, `GradientFlowProps`, `ObsLower`,
  `CompNondeg`, `ProxyGen`) give
  `InputsAt (le_refl 2) obsW r t |C| zri zwe μ G` for some `t`, `C`, `G`. Derived: `moments` from `scale`
  (`CompositesRenAll.uv_of_scale`, `ClaySUFinal.classMoments_of_siteExp`), `phys` from
  `ObserverChoice.obsW_physRange`, `far` from `endpoint` (`MultiScale.endpoint_iff_run`,
  `ScaleControlRun.runSeed_two_of_scaleControlRun`), `ward` from `SU2Best.wardT_of_props`, `comp` from
  `convC_ren_of_all`, `os0C_of_ren_all'`, `os1C_of_ren_all`, `covC_of_strong` and `CompNondeg`, `approx`
  from `approxK_of_expandRP` and `expandRP_of_strong`, `kernel` and `af` from `S.af`; `hri`, `hwe`, `low`
  passed through. `clayInputsN_two_of_su2Best` packs it. So at `N = 2` the general-`N` bundle follows
  from the `SU2Best` inputs, with no further hypothesis. Its `far` goes through `SubstrateAt.endpoint`
  (`MultiScale.Endpoint`), which `InputAudit.not_multiScaleEndpoint` refutes under the argued growth of the
  zero-flux level count.

## 3. What the general-`N` bundle needs, by `N`

At `N = 2` every field has a reduction (`inputsAt_two_of_su2Best`). At `N ≥ 3`:

* `far`: no producer. The `N`-general forms are `ObserverTheory.BindingSU N`, `FluxCost.BindingPlane N`
  (single-plane centre twists of `Z_N³`) and `FiniteReadingFlux.runSeed_iff_bindingRead`; the vortex form
  (`FluxCost.VortexCostAt`, `1 − zR` with one `Z₂` twist per plane), the odd-sector levels
  (`ScaleControlRun.OddLevels`, characters odd under `e_ν`) and the loop-state chain (`ElectricLoops`,
  `su2_mandelstam`; `LoopsGenerate.giles` via unit quaternions) are `SU(2)`.
* `W`: no `N`-general observer in the tree other than `ConfFlow.identity N`, which
  `PlaquetteFloor.not_classMoments_identity` excludes from `moments`. `obsW` is built from the `SU(2)` APE
  step (`ObserverFlow.obsConfFlow`, a normalised sum of the link and `c ×` six staples: in `SU(2)` such a
  sum is a real multiple of a group element). The archived `ObserverFlowN.BlockStep G` builds the
  flow, range, reflection and gauge covariance for any step; what it lacks at `SU(N)`, `N ≥ 3`, is a
  continuous projection of `W + c Σ Sᵢ` back to `SU(N)` (unitary polar part plus a determinant root).
* `moments`, `comp`, `approx`, `ward`: the reductions of `SU2Best` read only lattice composites `CRen 2`,
  the flowed proxies and the state, and call `N`-general lemmas (`mixConvG_of_cov`, `reflLimG_of_cov`,
  `reflCovLat_CRen`, `unifLocal_buildRen`) at `le_refl 2`. They are stated at `ConfFlow 2` and `h2N`; the
  port to `N` is to restate them at `N` and check that no step uses `SU(2)` structure.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` the least colour count and the limits of the scalar and pseudoscalar factors; `1`
the least `N` of `ZCanon`; `4` the dimension.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.SUNBest

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP
open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData MassGap.ReflAvg
  MassGap.MixConvRP MassGap.MultiScaleAll MassGap.CompositesRen MassGap.CompositesRenAll
  MassGap.MultiScaleOS MassGap.ApproxFromExpand MassGap.StrongExpand MassGap.CovFromFlow
  MassGap.ObserverChoice

/-! ## 1. The bundle and the capstone -/

section General

variable {N : ℕ}

/-- **The general-`N` inputs at one observer**: module docstring, §1. DERIVED: `2` the least colour
count. -/
structure InputsAt (hN2 : 2 ≤ N) (W : ConfFlow N) (r t C : ℝ) (zri zwe : ℕ → ℝ) (μ : OffMix)
    (G : ℝ → ℝ) : Prop where
  t_pos : 0 < t
  moments : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C
  phys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r
  /-- The gap. -/
  far : WDeltaRun.RunSeed N
  hri : ∀ k, zri k ≠ 0
  hwe : ∀ k, zwe k ≠ 0
  kernel : TwoPointKernel (ne_zero_of_two_le hN2) (rhoD (fR N) (ZCanon.zFix N zri zwe)) G
  af : AFCoefficient N G
  low : InputsTriage.ObsLower (ne_zero_of_two_le hN2) (ZCanon.zFix N zri zwe)
  ward : WardT (ne_zero_of_two_le hN2) (rhoD (fR N) (ZCanon.zFix N zri zwe))
  comp : CompOS (ne_zero_of_two_le hN2) (CRen N (ZCanon.zFix N zri zwe) μ)
  approx : ApproxK (kernC (ne_zero_of_two_le hN2) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
    (mixKG hN2 W (CRen N (ZCanon.zFix N zri zwe) μ) r) (gramF hN2 W r)

/-- **The general-`N` capstone**: `clayStatementAt_SU_ren_low` at `z = zFix N zri zwe`. DERIVED: `1` the
least `N` of `ZCanon`; `2` the least colour count. -/
theorem clayStatementAt_N_best {hN2 : 2 ≤ N} {W : ConfFlow N} {r t C : ℝ} {zri zwe : ℕ → ℝ}
    {μ : OffMix} {G : ℝ → ℝ} (I : InputsAt hN2 W r t C zri zwe μ G) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  clayStatementAt_SU_ren_low hN2 W I.t_pos I.moments I.phys I.far (ZCanon.zFix N zri zwe)
    (ZCanon.zFix_ne (by omega) I.hri I.hwe) (ZCanon.tendsto_zFix_sc (by omega) _ _)
    (ZCanon.tendsto_zFix_ps (by omega) _ _) G I.kernel I.af I.low I.ward μ I.comp I.approx

/-- **The gap field from the split binding statement** (`ObserverTheory.runSeed_iff_bindingSU`).
DERIVED: `2` the least colour count. -/
theorem runSeed_of_bindingSU' (hN2 : 2 ≤ N) {σ A : ℝ}
    (h : haveI : NeZero N := ⟨by omega⟩; ObserverTheory.BindingSU N σ A) : WDeltaRun.RunSeed N := by
  haveI : NeZero N := ⟨by omega⟩
  exact (ObserverTheory.runSeed_iff_bindingSU N).2 ⟨σ, A, h⟩

/-- **The general-`N` inputs at some observer.** DERIVED: `2` the least colour count. -/
def ClayInputsN (N : ℕ) (hN2 : 2 ≤ N) : Prop :=
  ∃ (W : ConfFlow N) (r t C : ℝ) (zri zwe : ℕ → ℝ) (μ : OffMix) (G : ℝ → ℝ),
    InputsAt hN2 W r t C zri zwe μ G

/-- `ClayInputsN` gives `ClayStatementG.ClayStatementSUDy N` (`ClayStatementG.clayStatementSUDy_iff`).
DERIVED: `2` the least colour count. -/
theorem clayStatementSU_of_inputs (hN2 : 2 ≤ N) (h : ClayInputsN N hN2) :
    ClayStatementG.ClayStatementSUDy N hN2 := by
  obtain ⟨W, r, t, C, zri, zwe, μ, G, I⟩ := h
  exact (ClayStatementG.clayStatementSUDy_iff N hN2).2
    ⟨W, SymPlaqClass N, symPlaq_refl N, clayStatementAt_N_best I⟩

end General

/-- **`ClayStatementDy` from the general-`N` inputs at every `N ≥ 2`.** DERIVED: `2` the least colour
count. -/
theorem clayStatement_of_inputs (h : ∀ (N : ℕ) (hN2 : 2 ≤ N), ClayInputsN N hN2) :
    MassGap.ClayStatementDy := fun N hN2 => by
  obtain ⟨W, r, t, C, zri, zwe, μ, G, I⟩ := h N hN2
  exact ⟨W, SymPlaqClass N, symPlaq_refl N, clayStatementAt_N_best I⟩

/-- **The `SU` component of `ClayStatementClassicalDy`** from the general-`N` inputs.
DERIVED: `2` the least colour count. -/
theorem clayStatementClassical_SU_of_inputs (h : ∀ (N : ℕ) (hN2 : 2 ≤ N), ClayInputsN N hN2) :
    ∀ (N : ℕ) (hN2 : 2 ≤ N), ClayStatementG.ClayStatementSUDy N hN2 :=
  fun N hN2 => clayStatementSU_of_inputs hN2 (h N hN2)

/-! ## 2. `SU2Best` read through the general-`N` bundle -/

local notation "h2N" => (ne_zero_of_two_le (le_refl 2) : (2 : ℕ) ≠ 0)

/-- **The `SU2Best` inputs give the general-`N` bundle at `N = 2`**: module docstring, §2.
DERIVED: `1` the smearing scale; `2` the colour count. -/
theorem inputsAt_two_of_su2Best {r : ℝ} (hr : 1 < r)
    {zri zwe : ℕ → ℝ} (hri : ∀ k, zri k ≠ 0) (hwe : ∀ k, zwe k ≠ 0) {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow 2} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SU2Best.SubstrateAt obsW (ZCanon.zFix 2 zri zwe) b Wf)
    (F : SU2Best.GradientFlowProps Wf cf (ZCanon.zFix 2 zri zwe) μ)
    (hlow : InputsTriage.ObsLower h2N (ZCanon.zFix 2 zri zwe))
    (hnd : CompNondeg h2N (CRen 2 (ZCanon.zFix 2 zri zwe) μ))
    (hG : ProxyGen obsW b Wf cf r) :
    ∃ (t C : ℝ) (G : ℝ → ℝ), InputsAt (le_refl 2) obsW r t |C| zri zwe μ G := by
  have H := S.toStrong F
  have h' : MultiScaleAllRen' obsW (ZCanon.zFix 2 zri zwe) μ := ⟨b, Wf, cf, H.toRenAt, F.coef⟩
  obtain ⟨t, C, ht, hS⟩ := uv_of_scale S.b_pos S.top S.scale
  have hU := ClaySUFinal.classMoments_of_siteExp h2N obsW ht hS
  have hCO : CompOS h2N (CRen 2 (ZCanon.zFix 2 zri zwe) μ) :=
    ⟨convC_ren_of_all (multiScaleAllRen_of' h'), os0C_of_ren_all' h',
      os1C_of_ren_all (multiScaleAllRen_of' h'), covC_of_strong H F.cov, hnd⟩
  obtain ⟨G, hK, hAF⟩ := S.af
  exact ⟨t, C, G,
    { t_pos := ht
      moments := hU
      phys := obsW_physRange hr
      far := ScaleControlRun.runSeed_two_of_scaleControlRun (MultiScale.endpoint_iff_run.1 S.endpoint)
      hri := hri
      hwe := hwe
      kernel := hK
      af := hAF
      low := hlow
      ward := SU2Best.wardT_of_props S F
      comp := hCO
      approx := approxK_of_expandRP hU (obsW_physRange hr) hCO (expandRP_of_strong S.b_pos F.expand)
        hG }⟩

/-- **`ClayInputsN 2` from the `SU2Best` inputs.** DERIVED: `1` the smearing scale; `2` the colour
count. -/
theorem clayInputsN_two_of_su2Best {r : ℝ} (hr : 1 < r)
    {zri zwe : ℕ → ℝ} (hri : ∀ k, zri k ≠ 0) (hwe : ∀ k, zwe k ≠ 0) {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow 2} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SU2Best.SubstrateAt obsW (ZCanon.zFix 2 zri zwe) b Wf)
    (F : SU2Best.GradientFlowProps Wf cf (ZCanon.zFix 2 zri zwe) μ)
    (hlow : InputsTriage.ObsLower h2N (ZCanon.zFix 2 zri zwe))
    (hnd : CompNondeg h2N (CRen 2 (ZCanon.zFix 2 zri zwe) μ))
    (hG : ProxyGen obsW b Wf cf r) : ClayInputsN 2 (le_refl 2) := by
  obtain ⟨t, C, G, I⟩ := inputsAt_two_of_su2Best hr hri hwe S F hlow hnd hG
  exact ⟨obsW, r, t, |C|, zri, zwe, μ, G, I⟩

end MassGap.SUNBest

end

#print axioms MassGap.SUNBest.clayStatementAt_N_best
#print axioms MassGap.SUNBest.runSeed_of_bindingSU'
#print axioms MassGap.SUNBest.clayStatementSU_of_inputs
#print axioms MassGap.SUNBest.clayStatement_of_inputs
#print axioms MassGap.SUNBest.clayStatementClassical_SU_of_inputs
#print axioms MassGap.SUNBest.inputsAt_two_of_su2Best
#print axioms MassGap.SUNBest.clayInputsN_two_of_su2Best
