import Mathlib
import MassGap.ObserverTowerPM
import MassGap.ClusterRoute

/-!
# MassGap.ObserverTowerCL — the root along the towers on the cluster route

`ObserverTowerPM.clayStatementOf_of_coreObsPM` reads the flow core `ObserverTowerPM.CoreInputsAlongWPM`, whose
scale clause `ScalePM.ScaleControlAllPM b Wf` carries one Gevrey index `r` over every channel, and whose
`OS0C` is read through that common index and `MultiScaleOS.CoefBound` (`ScalePM.os0C_of_scalePM`). On the
near-Gaussian count of `ScalePM` §4 (argued) one `r` holds only on the channels of dimension `≤ 4r`, so the
common index may fail on the channel tower. `ClusterRoute` reads `OS0C` from a cluster bound on separated
composites instead (`ClusterRoute.os0C_of_cluster`, `β = 1`) and lets every channel carry its own index
(`ClusterRoute.ScalePMChan`). This module states the root on that route. Declarations are in the namespace
`MassGap.ObserverTowerCL`.

## 1. The consumers of `scale` at the per-channel index (proved)

`ObserverTowerPM.coreClausesWPM` reads its substrate core through seven consumers. `ClusterRoute` has four at
the per-channel index (`uv_of_chan`, `convC_of_chan`, `os1C_of_chan`, and `os0C_of_cluster` in place of
`os0C_of_scalePM`, which needs no scale clause). This module adds the rest; the proxies' bound takes one
index on a finite channel set through `ClusterRoute.ScalePMChan.uniform`:

* `eventually_proxB_sq_le_chan`, `proxyBound_of_scaleChan`: `ScaleControlChan b Wf` and
  `UniformBoundF (Φ0 W)` give `ProxyBound W b Wf cf r` (`ObserverTowerPM.proxyBound_of_scalePM` with the
  largest index on the support of the doubled family).
* `uB_of_coreCL`, `proxyBound_of_coreCL`, `sepConv_of_chan`.
* **`coreClausesWCL`**: `ObserverTowerPM.coreClausesWPM` with `SubstrateCorePM` replaced by
  `ClusterRoute.SubstrateCoreCL` and `CoefBound cf` replaced by `ClusterRoute.ClusterPM Wf cf`.

## 2. The copy over a coupling family

`coreClausesWCL` and `ClusterRoute.substrateCoreCL_of_corePM` are copied over the coupling family by
`FieldSweep`'s `#along_generalize_more` (kernel-checked; the existing copies are reused), and no copy in
`MassGap.CouplingGen.Along` mentions `dyBeta`.

## 3. The root

* `CoreInputsAlongWCL N βs`: `ObserverTowerPM.CoreInputsAlongWPM N βs` with the copy of `SubstrateCoreCL` in
  place of the copy of `SubstrateCorePM` and the copy of `ClusterPM Wf cf` in place of `CoefBound cf`, every
  other field unchanged.
* `openAlongW_of_coreWCL`: `CoreInputsAlongWCL ⇒ ObserverTower.OpenAlongW`.
* **`clayStatementOf_of_coreObsCL`**: `StrongEnd N`, (UV) and `CoreInputsAlongWCL` along the towers near
  `0⁺` give `ClayStatementOf (SU N)`.
* `coreWCL_of_coreWPM_cluster`: the fields of `CoreInputsAlongWPM` together with `ClusterPM` at the same flow
  and coefficients give `CoreInputsAlongWCL` (the copy of `substrateCoreCL_of_corePM`; `CoefBound` dropped).

## 4. Relation to the moment core

The two cores differ in two fields. The scale field of the cluster core is weaker: `ScaleControlAllPM`
gives `ScaleControlChan` (`ClusterRoute.scaleControlChan_of_PM`), and the converse fails as stated (argued),
since `ScaleControlChan` has no common index and no `1 ≤ r`. `CoefBound cf` is dropped. `ClusterPM Wf cf` is
added, and the moment core does not give it: `ScaleControlAllPM` bounds the single-point moments of fixed
order with growth `((2p)!)^r`, `r ≥ 1`, while `ClusterPM` asks the cumulants of `n` separated factors within
`γⁿ n^{n−2}`, uniformly in `n`; Möbius inversion of the moment bounds gives at best `((2n)!)^r` growth,
beyond `γⁿ n^{n−2}` (argued). So `clayStatementOf_of_coreObsCL` is a sibling of
`ObserverTowerPM.clayStatementOf_of_coreObsPM`, not a weakening; `coreWCL_of_coreWPM_cluster` states the
exact gap between them (one added field).

## 5. The rough tail on the cluster core (argued)

`BlFamCore.RoughTail` refutes the exponential moment of a channel of dimension `> 4` at `s = b`
(`BlFamCore.not_scaleControlAll_of_roughTail`, proved). The cluster core asks an exponential moment only on
the plaquette class at `s = b` (dimension `4`), where the floor `exp(−c a_k^{−4} log(1/a_k))` of `BlFamCore`
§2 lies below every `exp(−L a_k^{−4})` (argued). Every other clause fixes its order before the step limit:
`ScalePMChan.chan` fixes the moment order `2p`, and `ClusterPM` fixes the number `n` of factors, so each
cumulant it bounds is a fixed polynomial in moments of order at most `n`. At a fixed order the floor of a
rough tail tends to `0` (`ObserverTowerPM.tendsto_roughFloor`, proved), so it puts no lower bound on any of
these quantities. `RoughTail` does not refute the cluster core through any of its clauses (argued). The
per-channel index removes the second risk of `ObserverTowerPM` §4: a near-Gaussian channel of dimension `d`
needs an index of order `d/4` (argued), which `ScalePMChan` grants channel by channel.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the signs, the plane, the lower end of the scale and the limits; `1` the spacing
bound; `2` the least rank, the doubling of a family and the mean; `2`, `1`, `3`, `4` in `(2 · 1 + 3)⁴` the
unit cube's site count. The prose of §4–§5 cites `4` the plaquette dimension, `2p` the moment order, `r ≥ 1`
and `((2p)!)^r` from `ScalePM.ScalePMAt`, `γⁿ n^{n−2}` the tree count of `ClusterPM`, `4r` the dimension one
order covers, `2n` in `((2n)!)^r`, `1` the exponent of `os0C_of_cluster`, and `d/4` the argued index count of
`ScalePM` §4.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ObserverTowerCL

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
  MassGap.SU2Best MassGap.NondegFromProxy MassGap.NonGaussFromScale
  MassGap.ProxyGenObserver MassGap.ProxyBoundFromScale MassGap.ScalePC MassGap.ScalePM
  MassGap.ClusterRoute
open MassGap.ScaleControlFull (zOne)

/-! ## 1. The consumers of `scale` at the per-channel index -/

section Clauses

variable {N : ℕ}

/-- **The square of a proxy product is bounded uniformly in the step under the per-channel moment input**,
at `0 < s ≤ b` (`ScalePM.abs_msLat_le_on_pm` on the doubled family at the largest index of its channels).
DERIVED: `0` the lower end of the scale; `1` the spacing bound; `2` the doubling of the family. -/
theorem eventually_proxB_sq_le_chan [NeZero N] {b : ℝ} {Wf : ℝ → ConfFlow N}
    (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (hsc : ScaleControlChan b Wf) (P : TMonoG Ix0) {s : ℝ} (hs : 0 < s)
    (hsb : s ≤ b) :
    ∃ C : ℝ, ∀ᶠ k in atTop, |stateK (NeZero.ne N) k (proxB Wf cf k s P * proxB Wf cf k s P)| ≤ C := by
  classical
  obtain ⟨γ, γP, H⟩ := hsc
  set F : Fin P.1 ⊕ Fin P.1 → CDatum (CbR N zOne) := Sum.elim P.2 P.2 with hF
  obtain ⟨r, t, K, ht, hK1, hev⟩ := H.uniform (Finset.univ.biUnion fun i => (cf (F i).1 s).support)
  refine ⟨(1 + Fintype.card (Fin P.1 ⊕ Fin P.1)
      * (((2 * Fintype.card (Fin P.1 ⊕ Fin P.1)).factorial : ℝ) ^ r * K))
      * ∏ i, (msTsize (F i).2 * msPsize t γ γP cf s (F i).1), ?_⟩
  filter_upwards [hev s hs hsb (Fintype.card (Fin P.1 ⊕ Fin P.1)),
    (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)] with k hk hk1
  rw [proxB_sq_eq]
  exact abs_msLat_le_on_pm Wf cf ht hs hk1.le F hK1 (fun i j hj =>
    hk j (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hj⟩))

/-- **`ProxyBound` from the per-channel moment input and the observer's uniform bound**
(`ObserverTowerPM.proxyBound_of_scalePM` with `eventually_proxB_sq_le_chan`). DERIVED: `2` the mean. -/
theorem proxyBound_of_scaleChan [NeZero N] {W : ConfFlow N} {b r : ℝ} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hsc : ScaleControlChan b Wf)
    (hB : UniformBoundF (NeZero.ne N) (Φ0 W)) : ProxyBound W b Wf cf r := by
  intro P s hs hsb
  obtain ⟨CB, hCB⟩ := eventually_proxB_sq_le_chan cf hsc P.1 hs hsb
  have hCB' := hCB.filter_mono ultra_le
  refine ⟨⟨CB, hCB'.mono fun k hk => ?_⟩, fun Q => ?_⟩
  · have h := abs_rform_le k (proxB Wf cf k s P.1) (proxB Wf cf k s P.1)
    unfold proxD
    linarith [le_abs_self (stateK (NeZero.ne N) k (proxB Wf cf k s P.1 * proxB Wf cf k s P.1))]
  · obtain ⟨CV, hCV⟩ := eventually_obs_sq_le hB Q.1
    refine ⟨(CB + CV) / 2, ?_⟩
    filter_upwards [hCB', hCV] with k hk hv
    have h := abs_rform_le k (proxB Wf cf k s P.1) (prodSmear (dySpacing N k) ((Φ0 W).mono k Q.1))
    unfold proxX
    linarith [le_abs_self (stateK (NeZero.ne N) k (proxB Wf cf k s P.1 * proxB Wf cf k s P.1)),
      le_abs_self (stateK (NeZero.ne N) k (prodSmear (dySpacing N k) ((Φ0 W).mono k Q.1)
        * prodSmear (dySpacing N k) ((Φ0 W).mono k Q.1)))]

/-- **The observer's uniform bound from the cluster core** (the plaquette class at `s = b`,
`ClusterRoute.uv_of_chan`). DERIVED: no numeral. -/
theorem uB_of_coreCL [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {b : ℝ} {Wf : ℝ → ConfFlow N}
    (S : SubstrateCoreCL W z b Wf) : UniformBoundF (NeZero.ne N) (Φ0 W) := by
  obtain ⟨t, C, ht, hS⟩ := uv_of_chan S.b_pos S.top S.scale
  exact ClaySUGap.uB (NeZero.ne N) W (ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) W ht hS)

/-- **`ProxyBound` from the cluster core**, for every coefficient family `cf` and every `r`.
DERIVED: no numeral. -/
theorem proxyBound_of_coreCL [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {b r : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (S : SubstrateCoreCL W z b Wf) :
    ProxyBound W b Wf cf r :=
  proxyBound_of_scaleChan S.scale (uB_of_coreCL S)

/-- **`SepConv` of the tensor sector from the per-channel moment input and `ExpandR`**
(`CompReduce.sepConv_of_comp` on `ClusterRoute.convC_of_chan`). DERIVED: `0` the sign of `b`. -/
theorem sepConv_of_chan [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ} (hb : 0 < b)
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hsc : ScaleControlChan b Wf)
    (hex : ExpandR Wf cf z μ) : SepConv (NeZero.ne N) (rhoD (fR N) z) :=
  CompReduce.sepConv_of_comp (NeZero.ne N) (rhoD (fR N) z) (CRen N z μ) eI
    (fun k α => buildRen_he2 _ _ μ k α) (convC_of_chan hb hsc hex)

/-- **The flow-side clauses at any observer with a physical range, from the cluster core**:
`ObserverTowerPM.coreClausesWPM` with `SubstrateCorePM` replaced by `SubstrateCoreCL` and `CoefBound cf`
replaced by `ClusterPM Wf cf`. DERIVED: `2` the least rank; `0` the plane; `2`, `1`, `3`, `4` in
`(2 · 1 + 3)⁴` the unit cube's site count. -/
theorem coreClausesWCL (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {r : ℝ} (hphys : (Φ0 W).PhysRange r)
    {zri zwe : ℕ → ℝ} {μ : OffMix} {b : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCoreCL W (ZCanon.zFix N zri zwe) b Wf)
    (hE : ExpandStrong Wf cf (ZCanon.zFix N zri zwe) μ) (hcl : ClusterPM Wf cf)
    (hV : FlowCovN.FlowCovLim Wf cf) (hW : WardFromLattice.FlowWard Wf cf) (hP : ProxyNondeg Wf cf)
    (hL : ProxyGenLimN.ProxyGenLimGerm W b Wf cf r)
    (h3 : ∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (NeZero.ne N) ℓ) :
    (∃ t C : ℝ, 0 < t ∧ FlowUV.SiteExp (NeZero.ne N) W (SymPlaqClass N) (t * (2 * 1 + 3) ^ 4) C)
      ∧ (∃ G : ℝ → ℝ, TwoPointKernel (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe)) G
          ∧ AFCoefficient N G)
      ∧ NonGaussianT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe))
      ∧ WardT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe))
      ∧ CompOS (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ ApproxK (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
          (mixKG hN2 W (CRen N (ZCanon.zFix N zri zwe) μ) r) (gramF hN2 W r) := by
  have hER := expandR_of_strong hE
  obtain ⟨t, C, ht, hS⟩ := uv_of_chan S.b_pos S.top S.scale
  have hU := ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) W ht hS
  have hCv := convC_of_chan S.b_pos S.scale hER
  have hSep := sepConv_of_chan S.b_pos S.scale hER
  have hCO : CompOS (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) :=
    ⟨hCv, os0C_of_cluster hCv hER hcl, os1C_of_chan S.b_pos S.scale hER,
      FlowCovN.covC_of_flowCovLim hER hCv hV, compNondeg_of_proxy hER hCv hP⟩
  obtain ⟨ℓ, hℓ, h3'⟩ := h3
  exact ⟨⟨t, C, ht, hS⟩, S.af,
    InputsTriage.nonGaussianT_rhoD_of_lower (NeZero.ne N) (fR N) (ZCanon.zFix N zri zwe) hSep
      (obsLower_of_scale (NeZero.ne N) hℓ zri zwe h3'),
    WardFromLattice.wardT_of_flowWard hSep hER hW, hCO,
    ProxyGenLimN.approxK_of_germ hN2 hU hphys hCO hE
      (ProxyGenLimN.germ_of_limGerm (uB_of_coreCL S) (proxyBound_of_coreCL S) hL)⟩

end Clauses

end MassGap.ObserverTowerCL

end

/-! ### The copy over a coupling family -/

namespace MassGap.ObserverTowerCL

set_option Elab.async false in
set_option maxHeartbeats 0 in
#along_generalize_more MassGap.ContinuumSchwinger.dyBeta from MassGap.ObserverTowerCL.coreClausesWCL
  MassGap.ClusterRoute.substrateCoreCL_of_corePM

-- No copy mentions the source (every copy in `MassGap.CouplingGen.Along`, the new ones included).
run_cmd do
  let env ← Lean.getEnv
  let src := ``MassGap.ContinuumSchwinger.dyBeta
  let pre := `MassGap.CouplingGen.Along
  for (c, ci) in env.constants.map₂.toList do
    if pre.isPrefixOf c then
      let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
      if used.contains src then
        throwError "copy {c} still mentions {src}"

end MassGap.ObserverTowerCL

/-! ## 3. The root -/

noncomputable section

namespace MassGap.ObserverTowerCL

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.ClayTreeG MassGap.ClayStatementG MassGap.FlowG Filter
open scoped Topology
open MassGap.FlowAlong (cpl schedAlongG_eq)
open MassGap.CouplingTower (StrongEnd CouplingTower UVConverges)
open MassGap.CompositeLink (Φ0)
open MassGap.CompositesRen (OffMix)
open MassGap.ObserverTower (OpenAlongW ApproxAlongW physRangeG_of_physRange energy0G_alongW
  clayStatementOf_of_openW)
open MassGap.ObserverTowerPM (CoreInputsAlongWPM)

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

variable (N) in
/-- **The flow-side bundle along `βs` at any observer, on the cluster route**:
`ObserverTowerPM.CoreInputsAlongWPM` with the copy of `ClusterRoute.SubstrateCoreCL` in place of the copy of
`ScalePM.SubstrateCorePM` and the copy of `ClusterRoute.ClusterPM Wf cf` in place of `CoefBound cf`, every
other field unchanged. DERIVED: `0` the signs. -/
def CoreInputsAlongWCL (βs : ℕ → ℝ) : Prop :=
  ∃ (W : ConfFlow N) (r : ℝ) (_ : (Φ0 W).PhysRange r)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : CompositesBuild.Ix0 → ℝ → (MultiScaleAll.MIx →₀ ℝ)),
    CouplingGen.Along.ClusterRoute.SubstrateCoreCL (cpl βs) W (ZCanon.zFix N zri zwe) b Wf
      ∧ CouplingGen.Along.StrongExpand.ExpandStrong (cpl βs) Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ CouplingGen.Along.ClusterRoute.ClusterPM (cpl βs) Wf cf
      ∧ CouplingGen.Along.FlowCovN.FlowCovLim (cpl βs) Wf cf
      ∧ CouplingGen.Along.WardFromLattice.FlowWard (cpl βs) Wf cf
      ∧ CouplingGen.Along.NondegFromProxy.ProxyNondeg (cpl βs) Wf cf
      ∧ CouplingGen.Along.ProxyGenLimN.ProxyGenLimGerm (cpl βs) W b Wf cf r
      ∧ ∃ ℓ : ℝ, 0 < ℓ
          ∧ CouplingGen.Along.NonGaussFromScale.ThreePointAtScale (cpl βs) (NeZero.ne N) ℓ

set_option maxRecDepth 100000 in
/-- **`CoreInputsAlongWCL ⇒ OpenAlongW`**: the clauses of `OpenAlongW` at `W.toG` from the copy of
`coreClausesWCL` at `cpl βs`, in the schedule form along `βs` (as `ObserverTowerPM.openAlongW_of_coreWPM`).
DERIVED: `0` the signs; `2`, `1`, `3`, `4` in `(2 · 1 + 3)⁴` the unit cube's site count; `2` the least
rank. -/
theorem openAlongW_of_coreWCL {βs : ℕ → ℝ} (h : CoreInputsAlongWCL N βs) : OpenAlongW N βs := by
  obtain ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hcl, hV, hW, hP, hL, h3⟩ := h
  obtain ⟨⟨t, C, ht, hSE⟩, ⟨Gk, hK, hAF⟩, hNG, hWT, hCO, hA⟩ :=
    CouplingGen.Along.ObserverTowerCL.coreClausesWCL (cpl βs) (Fact.out : 2 ≤ N) hphys S hE hcl hV hW hP
      hL h3
  have hsched := schedAlongG_eq (N := N) βs
  refine ⟨W.toG, r, physRangeG_of_physRange βs hphys, t * (2 * 1 + 3) ^ 4, C, by positivity, ?_, zri, zwe,
    hri, hwe, μ, ⟨Gk, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hsched]
    exact hSE
  · rw [hsched]
    exact hK
  · rw [constsG_SU N]
    exact hAF
  · rw [hsched]
    exact hNG
  · rw [hsched]
    exact hWT
  · rw [hsched]
    exact hCO
  · unfold ApproxAlongW
    rw [hsched, energy0G_alongW βs W]
    exact hA

/-- **The root at `SU(N)` from the strong end, (UV) and the bundle on the cluster route along the towers
near `0⁺`** (`ObserverTower.clayStatementOf_of_openW`, `openAlongW_of_coreWCL`). The observer is an
existential `W : ConfFlow N` with a physical range. Its hypothesis `hF` is a sibling of that of
`ObserverTowerPM.clayStatementOf_of_coreObsPM` (module docstring, §4; `coreWCL_of_coreWPM_cluster`).
DERIVED: `0` the limit `0⁺`. -/
theorem clayStatementOf_of_coreObsCL (hS : StrongEnd N)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      ∃ μ : ℝ, UVConverges N βs id μ)
    (hF : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      CoreInputsAlongWCL N βs) :
    ClayStatementOf (MassGap.SUN.SU N) :=
  clayStatementOf_of_openW hS hUV (hF.mono fun _ h βs hT => openAlongW_of_coreWCL (h βs hT))

omit [Fact (2 ≤ N)] in
/-- **The moment core and the cluster input at the same data give the cluster core**: the fields of
`ObserverTowerPM.CoreInputsAlongWPM` with `ClusterPM` added at the same flow and coefficients give
`CoreInputsAlongWCL` (the copy of `ClusterRoute.substrateCoreCL_of_corePM` at `cpl βs`; `CoefBound` is not
read). DERIVED: `0` the signs. -/
theorem coreWCL_of_coreWPM_cluster {βs : ℕ → ℝ}
    (h : ∃ (W : ConfFlow N) (r : ℝ) (_ : (Φ0 W).PhysRange r)
      (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
      (Wf : ℝ → ConfFlow N) (cf : CompositesBuild.Ix0 → ℝ → (MultiScaleAll.MIx →₀ ℝ)),
      CouplingGen.Along.ScalePM.SubstrateCorePM (cpl βs) W (ZCanon.zFix N zri zwe) b Wf
        ∧ CouplingGen.Along.StrongExpand.ExpandStrong (cpl βs) Wf cf (ZCanon.zFix N zri zwe) μ
        ∧ MultiScaleOS.CoefBound cf
        ∧ CouplingGen.Along.ClusterRoute.ClusterPM (cpl βs) Wf cf
        ∧ CouplingGen.Along.FlowCovN.FlowCovLim (cpl βs) Wf cf
        ∧ CouplingGen.Along.WardFromLattice.FlowWard (cpl βs) Wf cf
        ∧ CouplingGen.Along.NondegFromProxy.ProxyNondeg (cpl βs) Wf cf
        ∧ CouplingGen.Along.ProxyGenLimN.ProxyGenLimGerm (cpl βs) W b Wf cf r
        ∧ ∃ ℓ : ℝ, 0 < ℓ
            ∧ CouplingGen.Along.NonGaussFromScale.ThreePointAtScale (cpl βs) (NeZero.ne N) ℓ) :
    CoreInputsAlongWCL N βs := by
  obtain ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, -, hcl, F⟩ := h
  exact ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf,
    CouplingGen.Along.ClusterRoute.substrateCoreCL_of_corePM (cpl βs) S, hE, hcl, F⟩

omit [Fact (2 ≤ N)] in
/-- **The moment core with the cluster input gives its fields**: `CoreInputsAlongWPM` is the hypothesis of
`coreWCL_of_coreWPM_cluster` without its `ClusterPM` field. DERIVED: `0` the sign of `ℓ`. -/
theorem coreWPM_of_coreWPM_cluster {βs : ℕ → ℝ}
    (h : ∃ (W : ConfFlow N) (r : ℝ) (_ : (Φ0 W).PhysRange r)
      (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
      (Wf : ℝ → ConfFlow N) (cf : CompositesBuild.Ix0 → ℝ → (MultiScaleAll.MIx →₀ ℝ)),
      CouplingGen.Along.ScalePM.SubstrateCorePM (cpl βs) W (ZCanon.zFix N zri zwe) b Wf
        ∧ CouplingGen.Along.StrongExpand.ExpandStrong (cpl βs) Wf cf (ZCanon.zFix N zri zwe) μ
        ∧ MultiScaleOS.CoefBound cf
        ∧ CouplingGen.Along.ClusterRoute.ClusterPM (cpl βs) Wf cf
        ∧ CouplingGen.Along.FlowCovN.FlowCovLim (cpl βs) Wf cf
        ∧ CouplingGen.Along.WardFromLattice.FlowWard (cpl βs) Wf cf
        ∧ CouplingGen.Along.NondegFromProxy.ProxyNondeg (cpl βs) Wf cf
        ∧ CouplingGen.Along.ProxyGenLimN.ProxyGenLimGerm (cpl βs) W b Wf cf r
        ∧ ∃ ℓ : ℝ, 0 < ℓ
            ∧ CouplingGen.Along.NonGaussFromScale.ThreePointAtScale (cpl βs) (NeZero.ne N) ℓ) :
    CoreInputsAlongWPM N βs := by
  obtain ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, -, F⟩ := h
  exact ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, F⟩

end MassGap.ObserverTowerCL

end

#print axioms MassGap.ObserverTowerCL.eventually_proxB_sq_le_chan
#print axioms MassGap.ObserverTowerCL.proxyBound_of_scaleChan
#print axioms MassGap.ObserverTowerCL.uB_of_coreCL
#print axioms MassGap.ObserverTowerCL.proxyBound_of_coreCL
#print axioms MassGap.ObserverTowerCL.sepConv_of_chan
#print axioms MassGap.ObserverTowerCL.coreClausesWCL
#print axioms MassGap.CouplingGen.Along.ObserverTowerCL.coreClausesWCL
#print axioms MassGap.CouplingGen.Along.ClusterRoute.substrateCoreCL_of_corePM
#print axioms MassGap.ObserverTowerCL.openAlongW_of_coreWCL
#print axioms MassGap.ObserverTowerCL.clayStatementOf_of_coreObsCL
#print axioms MassGap.ObserverTowerCL.coreWCL_of_coreWPM_cluster
#print axioms MassGap.ObserverTowerCL.coreWPM_of_coreWPM_cluster
