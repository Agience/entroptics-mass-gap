import Mathlib
import MassGap.ObserverTower
import MassGap.ScalePM

/-!
# MassGap.ObserverTowerPM — the root along the towers with the scale input by moments

`ObserverTower.clayStatementOf_of_coreObs` reads the flow core `ObserverTower.CoreInputsAlongW`, whose
substrate core `SU2Best.SubstrateCoreAt` carries `scale : MultiScaleAll.ScaleControlAll b Wf`: one
exponential moment over every channel, at every scale in `[a_k, b]`. A rough tail of the observer refutes
it at every `b > 0` (`BlFamCore.not_substrateCoreAt_of_roughTail`). `ScalePM.ScaleControlAllPM b Wf` asks
the exponential moment of the plaquette class at `s = b` only, and on every channel the moments of each
fixed order `2p` with growth `((2p)!)^r`, the scale and the order fixed before the step grows. This module
states the root with the substrate core `ScalePM.SubstrateCorePM`. Declarations are in the namespace
`MassGap.ObserverTowerPM`.

## 1. The consumers of `scale` at the moment input (proved)

`ObserverTower.coreClausesW` reads `scale` through six consumers: the one-site exponential moment
(`CompositesRenAll.uv_of_scale`, also inside `ProxyGenObserver.uB_of_core`), `ConvC`
(`FlowChoice.convC_of_choice`), `SepConv` (`WardFromLattice.sepConv_of_scale_expand`), `OS0C`, `OS1C`
(`MultiScaleOS`) and the proxies' bound (`ProxyBoundFromScale.proxyBound_of_core`). `ScalePM` proves the
first four at the moment input (`uv_of_scalePM`, `convC_of_scalePM`, `os0C_of_scalePM`, `os1C_of_scalePM`).
This module adds the rest:

* `eventually_proxB_sq_le_pm`, `proxyBound_of_scalePM`: `ScaleControlAllPM b Wf` and
  `UniformBoundF (Φ0 W)` give `ProxyBound W b Wf cf r` (the square of a proxy product at fixed `s` and
  `P` is the flowed reading of the doubled family, bounded by `ScalePM.abs_msLat_le_on_pm` at its order).
* `uB_of_corePM`, `proxyBound_of_corePM`, `sepConv_of_scalePM`.
* **`coreClausesWPM`**: `ObserverTower.coreClausesW` with `SubstrateCoreAt` replaced by `SubstrateCorePM`.
* `substrateCorePM_of_coreAt`: `SubstrateCoreAt ⇒ SubstrateCorePM` (through `ScalePC.substrateCorePC_of_core`
  and `ScalePM.substrateCorePM_of_corePC`; the scale clause at `b > 0`).

## 2. The copy over a coupling family

`coreClausesWPM` and `substrateCorePM_of_coreAt` are copied over the coupling family by
`FieldSweep`'s `#along_generalize_more` (kernel-checked; the existing copies are reused), and no copy
mentions `dyBeta`.

## 3. The root

* `CoreInputsAlongWPM N βs`: `ObserverTower.CoreInputsAlongW N βs` with the copy of `SubstrateCorePM` in
  place of the copy of `SubstrateCoreAt`, every other field unchanged.
* **`coreWPM_of_coreW`**: `CoreInputsAlongW ⇒ CoreInputsAlongWPM`.
* `openAlongW_of_coreWPM`: `CoreInputsAlongWPM ⇒ ObserverTower.OpenAlongW`.
* **`clayStatementOf_of_coreObsPM`**: `StrongEnd N`, (UV) and `CoreInputsAlongWPM` along the towers near
  `0⁺` give `ClayStatementOf (SU N)`. Its hypothesis is implied by that of
  `ObserverTower.clayStatementOf_of_coreObs` (`coreWPM_of_coreW`).

## 4. One growth index over the channels, and `OS0C` (argued)

`OS0C` asks one `β` for every `n` and every family of `n` composites, over all of `Ix0`; the composites
reach every channel dimension `cdim`. `ScalePM.os0C_of_scalePM` reads `n` insertions of a composite through
the single-point `2n`-th moments of its channels (`ObserverOS.abs_state_prod_le`), which cost
`((2n)!)^{rⱼ}`, about `γⁿ (n!)^{2rⱼ}`, at channel `j`. A per-channel index `rⱼ` gives `OS0C` only if
`sup_j rⱼ < ∞`, which is one `r`; a composite's constant `Ccᵢ` enters as `Ccᵢⁿ` and cannot absorb
`(n!)^{2rⱼ − β}`. So the field keeps one `r` over all channels, as `ScalePM.ScalePMAt` states it, and a
per-dimension `r` is not a weaker input for this chain. The near-Gaussian count of `ScalePM` §4 (argued)
puts one `r` only on the channels of dimension `≤ 4r`; on that count `ScaleControlAllPM` fails on the
channel tower, and `OS0C` on all composites needs a bound that reads the separation in place of the
single-point moments. That count is not proved here.

That bound exists. `ClusterRoute.os0C_of_cluster` gives `OS0C` with `β = 1` from `ClusterRoute.ClusterPM`, a
tree-graph bound on the cumulants of separated smeared factors, with no moment uniform in the channel
dimension. `ClusterRoute.ScalePMChan` is the moment input with a Gevrey index `rⱼ` per channel; its consumers
are `ScalePMChan.uniform`, `uv_of_chan`, `convC_of_chan`, `os1C_of_chan`, with the core
`ClusterRoute.SubstrateCoreCL` and `scaleControlChan_of_PM` (`ScaleControlAllPM ⇒ ScaleControlChan`).
`ClusterPassage` reduces `ClusterPM` to pointwise cumulant bounds at separated lattice sites (`PointGap`).
`ObserverTowerCL` states the root on that route.

## 5. The rough tail and the moment input

`BlFamCore.not_scaleControlAll_of_roughTail` reads the exponential moment of the channel `jn n` at
`s = b`; `ScaleControlAllPM` has that only for the plaquette class. At a fixed order `2p` a rough tail
`ν_k(cutF) ≥ exp(−L a_k^{−4(n+1)})` bounds the `2p`-th moment of a channel of dimension `d` below by a
multiple of `(a_k^{−d})^{2p} exp(−L a_k^{−4(n+1)})` (argued), and that floor tends to `0`
(`tendsto_roughFloor`, proved): it puts no lower bound on the limit of any fixed-order moment. `RoughTail`
therefore does not refute `ScaleControlAllPM` through the moments of fixed order (argued, `ScalePM` §4: a
refutation needs orders growing with the step). At the plaquette class (dimension `4`) the floor
`exp(−c a_k^{−4} log(1/a_k))` of `BlFamCore` §2 lies below every `exp(−L a_k^{−4})` (argued), so the
exponential clause `top` is not refuted either (argued).

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the signs, the plane, the lower end of the scale and the limits; `1` the spacing
bound and the floor of the exponent `m`; `2` the least rank, the doubling of a family and the mean;
`2`, `1`, `3`, `4` in `(2 · 1 + 3)⁴` the unit cube's site count. The prose of §4–§5 cites `4(n + 1)`, the
dimension of the channel `jn n`, `4` the plaquette dimension (§5), and `4r`, `2rⱼ` the counts of `ScalePM`
§1 and §4.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ObserverTowerPM

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
open MassGap.ScaleControlFull (zOne)

/-! ## 1. The consumers of `scale` at the moment input -/

section Clauses

variable {N : ℕ}

/-- **The square of a proxy product is bounded uniformly in the step under the moment input**, at
`0 < s ≤ b` (`ScalePM.abs_msLat_le_on_pm` on the doubled family at its order). DERIVED: `0` the lower end
of the scale; `1` the spacing bound; `2` the doubling of the family. -/
theorem eventually_proxB_sq_le_pm [NeZero N] {b : ℝ} {Wf : ℝ → ConfFlow N} (cf : Ix0 → ℝ → (MIx →₀ ℝ))
    (hsc : ScaleControlAllPM b Wf) (P : TMonoG Ix0) {s : ℝ} (hs : 0 < s) (hsb : s ≤ b) :
    ∃ C : ℝ, ∀ᶠ k in atTop, |stateK (NeZero.ne N) k (proxB Wf cf k s P * proxB Wf cf k s P)| ≤ C := by
  classical
  obtain ⟨r, γ, γP, H⟩ := hsc
  set F : Fin P.1 ⊕ Fin P.1 → CDatum (CbR N zOne) := Sum.elim P.2 P.2 with hF
  obtain ⟨t, K, ht, hK1, hev⟩ := H.uniform (Finset.univ.biUnion fun i => (cf (F i).1 s).support)
  refine ⟨(1 + Fintype.card (Fin P.1 ⊕ Fin P.1)
      * (((2 * Fintype.card (Fin P.1 ⊕ Fin P.1)).factorial : ℝ) ^ r * K))
      * ∏ i, (msTsize (F i).2 * msPsize t γ γP cf s (F i).1), ?_⟩
  filter_upwards [hev s hs hsb (Fintype.card (Fin P.1 ⊕ Fin P.1)),
    (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)] with k hk hk1
  rw [proxB_sq_eq]
  exact abs_msLat_le_on_pm Wf cf ht hs hk1.le F hK1 (fun i j hj =>
    hk j (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hj⟩))

/-- **`ProxyBound` from the moment input and the observer's uniform bound** (the proof of
`ProxyBoundFromScale.proxyBound_of_scale` with `eventually_proxB_sq_le_pm`). DERIVED: `2` the mean. -/
theorem proxyBound_of_scalePM [NeZero N] {W : ConfFlow N} {b r : ℝ} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hsc : ScaleControlAllPM b Wf) (hB : UniformBoundF (NeZero.ne N) (Φ0 W)) :
    ProxyBound W b Wf cf r := by
  intro P s hs hsb
  obtain ⟨CB, hCB⟩ := eventually_proxB_sq_le_pm cf hsc P.1 hs hsb
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

/-- **The observer's uniform bound from the moment core** (the plaquette class at `s = b`,
`ScalePM.uv_of_scalePM`). DERIVED: no numeral. -/
theorem uB_of_corePM [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {b : ℝ} {Wf : ℝ → ConfFlow N}
    (S : SubstrateCorePM W z b Wf) : UniformBoundF (NeZero.ne N) (Φ0 W) := by
  obtain ⟨t, C, ht, hS⟩ := uv_of_scalePM S.b_pos S.top S.scale
  exact ClaySUGap.uB (NeZero.ne N) W (ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) W ht hS)

/-- **`ProxyBound` from the moment core**, for every coefficient family `cf` and every `r`.
DERIVED: no numeral. -/
theorem proxyBound_of_corePM [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {b r : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (S : SubstrateCorePM W z b Wf) :
    ProxyBound W b Wf cf r :=
  proxyBound_of_scalePM S.scale (uB_of_corePM S)

/-- **`SepConv` of the tensor sector from the moment input and `ExpandR`** (`CompReduce.sepConv_of_comp`
on `ScalePM.convC_of_scalePM`). DERIVED: no numeral. -/
theorem sepConv_of_scalePM [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ} (hb : 0 < b)
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hsc : ScaleControlAllPM b Wf)
    (hex : ExpandR Wf cf z μ) : SepConv (NeZero.ne N) (rhoD (fR N) z) :=
  CompReduce.sepConv_of_comp (NeZero.ne N) (rhoD (fR N) z) (CRen N z μ) eI
    (fun k α => buildRen_he2 _ _ μ k α) (convC_of_scalePM hb hsc hex)

/-- **The flow-side clauses at any observer with a physical range, from the moment core**:
`ObserverTower.coreClausesW` with `SubstrateCoreAt` replaced by `SubstrateCorePM`. DERIVED: `2` the least
rank; `0` the plane; `2`, `1`, `3`, `4` in `(2 · 1 + 3)⁴` the unit cube's site count. -/
theorem coreClausesWPM (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {r : ℝ} (hphys : (Φ0 W).PhysRange r)
    {zri zwe : ℕ → ℝ} {μ : OffMix} {b : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCorePM W (ZCanon.zFix N zri zwe) b Wf)
    (hE : ExpandStrong Wf cf (ZCanon.zFix N zri zwe) μ) (hC : CoefBound cf)
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
  obtain ⟨t, C, ht, hS⟩ := uv_of_scalePM S.b_pos S.top S.scale
  have hU := ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) W ht hS
  have hCv := convC_of_scalePM S.b_pos S.scale hER
  have hSep := sepConv_of_scalePM S.b_pos S.scale hER
  have hCO : CompOS (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) :=
    ⟨hCv, os0C_of_scalePM S.b_pos S.scale hER hC, os1C_of_scalePM S.b_pos S.scale hER,
      FlowCovN.covC_of_flowCovLim hER hCv hV, compNondeg_of_proxy hER hCv hP⟩
  obtain ⟨ℓ, hℓ, h3'⟩ := h3
  exact ⟨⟨t, C, ht, hS⟩, S.af,
    InputsTriage.nonGaussianT_rhoD_of_lower (NeZero.ne N) (fR N) (ZCanon.zFix N zri zwe) hSep
      (obsLower_of_scale (NeZero.ne N) hℓ zri zwe h3'),
    WardFromLattice.wardT_of_flowWard hSep hER hW, hCO,
    ProxyGenLimN.approxK_of_germ hN2 hU hphys hCO hE
      (ProxyGenLimN.germ_of_limGerm (uB_of_corePM S) (proxyBound_of_corePM S) hL)⟩

/-- **`SubstrateCoreAt ⇒ SubstrateCorePM`** (`ScalePC.substrateCorePC_of_core`,
`ScalePM.substrateCorePM_of_corePC`). DERIVED: no numeral. -/
theorem substrateCorePM_of_coreAt [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {b : ℝ}
    {Wf : ℝ → ConfFlow N} (S : SubstrateCoreAt W z b Wf) : SubstrateCorePM W z b Wf :=
  substrateCorePM_of_corePC (substrateCorePC_of_core S)

/-- **At a fixed order the floor of a rough tail vanishes**: for `L > 0`, `m ≥ 1` and every `q`,
`(a_k^{−1})^q exp(−L / a_k^m) → 0`. At `m = 4(n + 1)` and `q = 2p d` it is the lower bound that
`BlFamCore.RoughTail` puts on the `2p`-th moment of a channel of dimension `d` (argued, module docstring §5).
DERIVED: `1` the floor of `m`; `0` the limit. -/
theorem tendsto_roughFloor [NeZero N] {L : ℝ} (hL : 0 < L) {m : ℕ} (hm : 1 ≤ m) (q : ℕ) :
    Tendsto (fun k => (dySpacing N k)⁻¹ ^ q * Real.exp (-(L / dySpacing N k ^ m))) atTop (𝓝 0) := by
  have hpos : ∀ k, 0 < dySpacing N k := fun k => dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  have h0 : Tendsto (dySpacing N) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_dySpacing N, Eventually.of_forall hpos⟩
  have hx : Tendsto (fun k => (dySpacing N k)⁻¹) atTop atTop := tendsto_inv_nhdsGT_zero.comp h0
  have hg : Tendsto (fun x : ℝ => (L⁻¹) ^ q * ((L * x) ^ q * Real.exp (-(L * x)))) atTop (𝓝 0) := by
    have h1 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero q).comp (tendsto_id.const_mul_atTop hL)).const_mul
      ((L⁻¹) ^ q)
    rw [mul_zero] at h1
    exact h1
  have hf : Tendsto (fun x : ℝ => x ^ q * Real.exp (-(L * x))) atTop (𝓝 0) := by
    refine hg.congr fun x => ?_
    rw [mul_pow, ← mul_assoc, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hL.ne', one_pow, one_mul]
  have hfx := hf.comp hx
  refine squeeze_zero' (Eventually.of_forall fun k => ?_) ?_ hfx
  · exact mul_nonneg (pow_nonneg (inv_pos.mpr (hpos k)).le _) (Real.exp_pos _).le
  · filter_upwards [hx.eventually_ge_atTop 1] with k hk
    simp only [Function.comp_apply]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (pow_nonneg (by linarith) _)
    have hxm : (dySpacing N k)⁻¹ ≤ (dySpacing N k)⁻¹ ^ m := le_self_pow₀ hk (by omega)
    have e : L / dySpacing N k ^ m = L * (dySpacing N k)⁻¹ ^ m := by
      rw [div_eq_mul_inv, inv_pow]
    rw [e]
    have := mul_le_mul_of_nonneg_left hxm hL.le
    linarith

end Clauses

end MassGap.ObserverTowerPM

end

/-! ### The copy over a coupling family -/

namespace MassGap.ObserverTowerPM

set_option Elab.async false in
set_option maxHeartbeats 0 in
#along_generalize_more MassGap.ContinuumSchwinger.dyBeta from MassGap.ObserverTowerPM.coreClausesWPM
  MassGap.ObserverTowerPM.substrateCorePM_of_coreAt

-- No copy mentions the source.
run_cmd do
  let env ← Lean.getEnv
  let src := ``MassGap.ContinuumSchwinger.dyBeta
  let pre := `MassGap.CouplingGen.Along
  for (c, ci) in env.constants.map₂.toList do
    if pre.isPrefixOf c then
      let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
      if used.contains src then
        throwError "copy {c} still mentions {src}"

end MassGap.ObserverTowerPM

/-! ## 3. The root -/

noncomputable section

namespace MassGap.ObserverTowerPM

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.ClayTreeG MassGap.ClayStatementG MassGap.FlowG Filter
open scoped Topology
open MassGap.FlowAlong (cpl schedAlongG_eq)
open MassGap.CouplingTower (StrongEnd CouplingTower UVConverges)
open MassGap.CompositeLink (Φ0)
open MassGap.CompositesRen (OffMix)
open MassGap.ObserverTower (CoreInputsAlongW OpenAlongW ApproxAlongW physRangeG_of_physRange
  energy0G_alongW clayStatementOf_of_openW)

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

variable (N) in
/-- **The flow-side bundle along `βs` at any observer, with the scale input by moments**:
`ObserverTower.CoreInputsAlongW` with the copy of `ScalePM.SubstrateCorePM` in place of the copy of
`SU2Best.SubstrateCoreAt`, every other field unchanged. DERIVED: `0` the signs. -/
def CoreInputsAlongWPM (βs : ℕ → ℝ) : Prop :=
  ∃ (W : ConfFlow N) (r : ℝ) (_ : (Φ0 W).PhysRange r)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : CompositesBuild.Ix0 → ℝ → (MultiScaleAll.MIx →₀ ℝ)),
    CouplingGen.Along.ScalePM.SubstrateCorePM (cpl βs) W (ZCanon.zFix N zri zwe) b Wf
      ∧ CouplingGen.Along.StrongExpand.ExpandStrong (cpl βs) Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ MultiScaleOS.CoefBound cf
      ∧ CouplingGen.Along.FlowCovN.FlowCovLim (cpl βs) Wf cf
      ∧ CouplingGen.Along.WardFromLattice.FlowWard (cpl βs) Wf cf
      ∧ CouplingGen.Along.NondegFromProxy.ProxyNondeg (cpl βs) Wf cf
      ∧ CouplingGen.Along.ProxyGenLimN.ProxyGenLimGerm (cpl βs) W b Wf cf r
      ∧ ∃ ℓ : ℝ, 0 < ℓ
          ∧ CouplingGen.Along.NonGaussFromScale.ThreePointAtScale (cpl βs) (NeZero.ne N) ℓ

omit [Fact (2 ≤ N)] in
/-- **`CoreInputsAlongW ⇒ CoreInputsAlongWPM`**: the copy of `substrateCorePM_of_coreAt` at `cpl βs`, the
other fields unchanged. DERIVED: no numeral. -/
theorem coreWPM_of_coreW {βs : ℕ → ℝ} (h : CoreInputsAlongW N βs) : CoreInputsAlongWPM N βs := by
  obtain ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, F⟩ := h
  exact ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf,
    CouplingGen.Along.ObserverTowerPM.substrateCorePM_of_coreAt (cpl βs) S, F⟩

set_option maxRecDepth 100000 in
/-- **`CoreInputsAlongWPM ⇒ OpenAlongW`**: the clauses of `OpenAlongW` at `W.toG` from the copy of
`coreClausesWPM` at `cpl βs`, in the schedule form along `βs` (as `ObserverTower.openAlongW_of_coreW`).
DERIVED: `0` the signs; `2`, `1`, `3`, `4` in `(2 · 1 + 3)⁴` the unit cube's site count; `2` the least
rank. -/
theorem openAlongW_of_coreWPM {βs : ℕ → ℝ} (h : CoreInputsAlongWPM N βs) : OpenAlongW N βs := by
  obtain ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP, hL, h3⟩ := h
  obtain ⟨⟨t, C, ht, hSE⟩, ⟨Gk, hK, hAF⟩, hNG, hWT, hCO, hA⟩ :=
    CouplingGen.Along.ObserverTowerPM.coreClausesWPM (cpl βs) (Fact.out : 2 ≤ N) hphys S hE hC hV hW hP
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

/-- **The root at `SU(N)` from the strong end, (UV) and the bundle with the scale input by moments along
the towers near `0⁺`** (`ObserverTower.clayStatementOf_of_openW`, `openAlongW_of_coreWPM`). The observer
is an existential `W : ConfFlow N` with a physical range; its hypothesis `hF` is implied by that of
`ObserverTower.clayStatementOf_of_coreObs` (`coreWPM_of_coreW`). DERIVED: `0` the limit `0⁺`. -/
theorem clayStatementOf_of_coreObsPM (hS : StrongEnd N)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      ∃ μ : ℝ, UVConverges N βs id μ)
    (hF : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      CoreInputsAlongWPM N βs) :
    ClayStatementOf (MassGap.SUN.SU N) :=
  clayStatementOf_of_openW hS hUV (hF.mono fun _ h βs hT => openAlongW_of_coreWPM (h βs hT))

end MassGap.ObserverTowerPM

end

#print axioms MassGap.ObserverTowerPM.eventually_proxB_sq_le_pm
#print axioms MassGap.ObserverTowerPM.proxyBound_of_scalePM
#print axioms MassGap.ObserverTowerPM.uB_of_corePM
#print axioms MassGap.ObserverTowerPM.proxyBound_of_corePM
#print axioms MassGap.ObserverTowerPM.sepConv_of_scalePM
#print axioms MassGap.ObserverTowerPM.coreClausesWPM
#print axioms MassGap.ObserverTowerPM.substrateCorePM_of_coreAt
#print axioms MassGap.ObserverTowerPM.tendsto_roughFloor
#print axioms MassGap.CouplingGen.Along.ObserverTowerPM.coreClausesWPM
#print axioms MassGap.CouplingGen.Along.ObserverTowerPM.substrateCorePM_of_coreAt
#print axioms MassGap.ObserverTowerPM.coreWPM_of_coreW
#print axioms MassGap.ObserverTowerPM.openAlongW_of_coreWPM
#print axioms MassGap.ObserverTowerPM.clayStatementOf_of_coreObsPM
