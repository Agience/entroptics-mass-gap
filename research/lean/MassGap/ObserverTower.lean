import Mathlib
import MassGap.FieldSweep

/-!
# MassGap.ObserverTower — the root along the towers at any observer with a physical range

`FieldSweep.clayStatementOf_of_core` derives `ClayStatementOf (SU N)` from `StrongEnd N`, (UV) and
`FieldSweep.CoreInputsAlong N βs` along the coupling towers near `0⁺`. Every link of that chain
(`TowerOpen.OpenAlongR`, `LinkAlongG.ApproxAlong`, `FlowAlong.energy0G_along`, `ConsolidatedRoot.obsW`,
`CoreInputsAlong`) names the block-step observer `ObserverFlowSUN.sunFam hN2 c hc0 hc s₀`. This module
restates the chain at an arbitrary observer and recovers the `sunFam` statements as instances.
Declarations are in the namespace `MassGap.ObserverTower`.

## What the chain reads of the observer

An observer is a configuration flow `W : ContinuumFlow.ConfFlow N`. Its structure carries continuity of each
`V k`, gauge covariance, reflection covariance in each axis, a range `W.range k` and locality within it. Beyond the
structure, the chain reads one property of `W`: a physical range `r`, `(CompositeLink.Φ0 W).PhysRange r`
(eventually `a_k · W.range k ≤ r`). In `FieldSweep.coreClausesK` the observer enters only through
`ObserverFlowSUN.sunFam_physRange`; the remaining steps (`CompositesRenAll.uv_of_scale`,
`ClaySUFinal.classMoments_of_siteExp`, `ProxyGenLimN.approxK_of_germ`, `ProxyGenObserver.uB_of_core`,
`ProxyBoundFromScale.proxyBound_of_core`) are stated at any `W`. Along the tower,
`ConstantPhysicsLine.ExistAlong` already takes any `W : ConfFlowG (SU N)` with the physical range of its
energy flow; `ConsolidatedRoot` and `LinkAlongG` fix `W = obsW` and use only `physRange_sunFam`.
No new mathematics enters: every proof below is the corresponding `sunFam` proof with that one lemma
replaced by the hypothesis.

Non-degeneracy of `W` is not read by the chain; it is forced by the core inputs: an eventually identity
observer refutes `SU2Best.SubstrateCoreAt` (`ScaleIdentityNoGo.not_substrateCoreAt_of_id`), as does a
plaquette leak (`SunFamLeak.not_substrateCoreAt_of_plaqLeak`).

## 1. The clauses at `stateK` at any observer

* **`coreClausesW`**: `FieldSweep.coreClausesK` with `sunFam … s₀` replaced by any `W` with
  `(Φ0 W).PhysRange r`. Copied over the coupling family by `#along_generalize_more` (kernel-checked; the
  existing copies are reused), and the copies are checked not to mention `dyBeta`.

## 2. The tower statements at any observer

* `ApproxAlongW N βs W r zri zwe μ`: `LinkAlongG.ApproxAlong` at any `W : ConfFlowG (SU N)`;
  `ApproxAlong N βs hc0 hc s₀ r …` is `ApproxAlongW N βs (obsW N hc0 hc s₀) r …` by definition.
* **`linkAlongW`**: `LinkAlongG.linkAlong` at any `W` with the physical range of its energy flow.
* `OpenAlongW N βs`: `TowerOpen.OpenAlongR` with the observer an existential `W : ConfFlowG (SU N)` and
  its physical range a clause. **`openAlongW_of_openAlongR`**: `OpenAlongR ⇒ OpenAlongW` (the instance
  `W = obsW`). **`existAlong_of_openW`**: `OpenAlongW ⇒ ConstantPhysicsLine.ExistAlong`.
* **`clayStatementOf_of_openW`**: `StrongEnd N`, (UV) and `OpenAlongW` along the towers near `0⁺` give
  `ClayStatementOf (SU N)`.

## 3. The root at any observer

* `physRangeG_of_physRange`, `energy0G_alongW`: `(Φ0 W).PhysRange r` gives the physical range of the
  energy flow of `W.toG` along `βs`, and on the copy of `schedSU` that energy flow is `(Φ0 W).toGFlow`
  (by definition).
* `CoreInputsAlongW N βs`: `FieldSweep.CoreInputsAlong N βs` with the observer an existential
  `W : ConfFlow N` with `(Φ0 W).PhysRange r`, every other field unchanged. **`coreW_of_core`**:
  `CoreInputsAlong ⇒ CoreInputsAlongW` (the instance `W = sunFam … s₀`, `sunFam_physRange`).
* **`openAlongW_of_coreW`**: `CoreInputsAlongW ⇒ OpenAlongW`.
* **`clayStatementOf_of_coreObs`**: `StrongEnd N`, (UV) and `CoreInputsAlongW` along the towers near `0⁺`
  give `ClayStatementOf (SU N)`. Its hypothesis is implied by that of `FieldSweep.clayStatementOf_of_core`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the signs, the plane and the limit `0⁺`; `2` the least rank; `2`, `1`, `3`, `4`
in `(2 · 1 + 3)⁴` the unit cube's site count. The construction bound `12 c < sin(π/N)`
of `sunFam` appears only in the instances `openAlongW_of_openAlongR` and `coreW_of_core`, read from the
statements they instantiate.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ObserverTower

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
  MassGap.ProxyGenObserver MassGap.ProxyBoundFromScale

/-! ## 1. The clauses at `stateK` at any observer -/

section Clauses

variable {N : ℕ}

/-- **The flow-side clauses at any observer with a physical range**: `FieldSweep.coreClausesK` with
`sunFam … s₀` and `ObserverFlowSUN.sunFam_physRange` replaced by `W` and `hphys`. DERIVED: `2` the least
colour count; `0` the plane; `2`, `1`, `3`, `4` in `(2 · 1 + 3)⁴` the unit cube's site count. -/
theorem coreClausesW (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {r : ℝ} (hphys : (Φ0 W).PhysRange r)
    {zri zwe : ℕ → ℝ} {μ : OffMix} {b : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCoreAt W (ZCanon.zFix N zri zwe) b Wf)
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
  obtain ⟨t, C, ht, hS⟩ := uv_of_scale S.b_pos S.top S.scale
  have hU := ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) W ht hS
  have hCv := FlowChoice.convC_of_choice S.b_pos S.scale hE
  have hSep := WardFromLattice.sepConv_of_scale_expand S.b_pos S.scale hER
  have hCO : CompOS (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) :=
    ⟨hCv, os0C_of_scale_expand_coef S.b_pos S.scale hER hC, os1C_of_scale_expand S.b_pos S.scale hER,
      FlowCovN.covC_of_flowCovLim hER hCv hV, compNondeg_of_proxy hER hCv hP⟩
  obtain ⟨ℓ, hℓ, h3'⟩ := h3
  exact ⟨⟨t, C, ht, hS⟩, S.af,
    InputsTriage.nonGaussianT_rhoD_of_lower (NeZero.ne N) (fR N) (ZCanon.zFix N zri zwe) hSep
      (obsLower_of_scale (NeZero.ne N) hℓ zri zwe h3'),
    WardFromLattice.wardT_of_flowWard hSep hER hW, hCO,
    ProxyGenLimN.approxK_of_germ hN2 hU hphys hCO hE
      (ProxyGenLimN.germ_of_limGerm (uB_of_core S) (proxyBound_of_core S) hL)⟩

end Clauses

end MassGap.ObserverTower

end

/-! ### The copy over a coupling family -/

namespace MassGap.ObserverTower

set_option Elab.async false in
set_option maxHeartbeats 0 in
#along_generalize_more MassGap.ContinuumSchwinger.dyBeta from MassGap.ObserverTower.coreClausesW

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

end MassGap.ObserverTower

/-! ## 2. The tower statements at any observer -/

noncomputable section

namespace MassGap.ObserverTower

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverEnergyBox
  MassGap.ClayStatement MassGap.ClayTreeG MassGap.ClayStatementG MassGap.ClayWiringG MassGap.FlowG
  MassGap.TimeGroupG MassGap.EnergyBoundG MassGap.ObserverOSG MassGap.ObserverLinkedG MassGap.SymPlaqG
  MassGap.CompReduceG MassGap.LinkReduce MassGap.LinkReduceG MassGap.ClayGFinal Filter
open scoped Topology
open MassGap.MeasuredTower (schedAlongG)
open MassGap.MeasuredSpacing (schedOS_alongG schedShiftInv_alongG)
open MassGap.CouplingTower (StrongEnd CouplingTower UVConverges)
open MassGap.ConsolidatedRoot (obsW rhoZ csZ physRange_sunFam riemann_rhoZ tie_rhoZ channel_rhoZ
  compData_csZ he1_csZ he2_csZ tensorCov_rhoZ)
open MassGap.LinkAlongG (ApproxAlong linkCPreG_of_approx unifLocal_csZ reflCovLat_csZ mixKCG)
open MassGap.TowerOpen (SiteExpG classMomentsG_of_siteExpG OpenAlongR)
open MassGap.CompositeLink (ApproxK)

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

variable (N) in
/-- **`ApproxK` of the three kernels along `βs` at an observer `W`**: `LinkAlongG.ApproxAlong` with
`obsW N hc0 hc s₀` replaced by `W`. DERIVED: `0` the plane. -/
def ApproxAlongW (βs : ℕ → ℝ) (W : ConfFlowG (MassGap.SUN.SU N)) (r : ℝ) (zri zwe : ℕ → ℝ)
    (μ : CompositesRen.OffMix) : Prop :=
  ApproxK (kernCG (schedAlongG _ βs) (csZ N zri zwe μ) 0)
    (fun P (Q : MarginMonoG (MassGap.SUN.SU N) 0 r) =>
      mixKCG (schedAlongG _ βs) (csZ N zri zwe μ)
        (energy0G (schedAlongG _ βs) W (SymPlaqClassG (MassGap.SUN.SU N))
          (symPlaqG_refl (MassGap.SUN.SU N))) 0 P Q.1)
    (fun Q Q' : MarginMonoG (MassGap.SUN.SU N) 0 r =>
      kernFG (schedAlongG _ βs)
        (energy0G (schedAlongG _ βs) W (SymPlaqClassG (MassGap.SUN.SU N))
          (symPlaqG_refl (MassGap.SUN.SU N))) 0 Q.1 Q'.1)

/-- **The link along every coupling tower at an observer `W`**: `LinkAlongG.linkAlong` with
`obsW N hc0 hc s₀` and `ConsolidatedRoot.physRange_sunFam` replaced by `W` and `hphys`. DERIVED: `0` the
plane. -/
theorem linkAlongW (βs : ℕ → ℝ) (W : ConfFlowG (MassGap.SUN.SU N)) {r : ℝ}
    (hphys : (energy0G (schedAlongG _ βs) W (SymPlaqClassG (MassGap.SUN.SU N))
      (symPlaqG_refl (MassGap.SUN.SU N))).PhysRange (schedAlongG _ βs) r) {t C₀ : ℝ}
    (hU : ClassMomentsG (schedAlongG _ βs) W (SymPlaqClassG (MassGap.SUN.SU N)) t C₀)
    (zri zwe : ℕ → ℝ) (μ : CompositesRen.OffMix) (hCO : ConvCG (schedAlongG _ βs) (csZ N zri zwe μ))
    (hA : ApproxAlongW N βs W r zri zwe μ) :
    ∃ wC : TSepG (csZ N zri zwe μ).Ix 0 → preHGAlong βs W hU hphys,
      LinkCPreG (schedAlongG _ βs) 0 (preVacGAlong βs W hU hphys) (preTimeGAlong βs W hU hphys)
          (csZ N zri zwe μ) wC
        ∧ ∀ (P : TSep 0) (Q : MarginMonoDG (MassGap.SUN.SU N) (SymPlaqClassG (MassGap.SUN.SU N)) 0 r),
          Tendsto (fun k => mixLatTG (schedAlongG _ βs) (rhoZ N zri zwe)
              (energyMapG (schedAlongG _ βs) W (SymPlaqClassG (MassGap.SUN.SU N))) 0 k P.1 Q.1.1)
              (ultra : Filter ℕ)
              (𝓝 (mixTG (schedAlongG _ βs) (rhoZ N zri zwe)
                (energyMapG (schedAlongG _ βs) W (SymPlaqClassG (MassGap.SUN.SU N))) 0 P.1 Q.1.1))
            ∧ inner ℂ (wOfC CompositesBuild.eI wC P) (preCvecGAlong βs W hU hphys Q)
              = (mixTG (schedAlongG _ βs) (rhoZ N zri zwe)
                  (energyMapG (schedAlongG _ βs) W (SymPlaqClassG (MassGap.SUN.SU N))) 0 P.1 Q.1.1 : ℂ) := by
  obtain ⟨wC, hLC, hX⟩ := linkCPreG_of_approx (schedAlongG _ βs) (schedOS_alongG _ βs)
    (energy0G (schedAlongG _ βs) W (SymPlaqClassG (MassGap.SUN.SU N)) (symPlaqG_refl (MassGap.SUN.SU N)))
    (preBGAlong βs W hU) (posPreserving_of_physRangeG _ _ hphys 0)
    (rhoZ N zri zwe) (csZ N zri zwe μ) CompositesBuild.eI (he1_csZ zri zwe μ) (he2_csZ zri zwe μ)
    (unifLocal_csZ zri zwe μ) (reflCovLat_csZ zri zwe μ) hCO hA
  exact ⟨wC, hLC, fun P Q => hX P Q.1⟩

variable (N) in
/-- **The clauses along `βs` that remain open, at any observer**: `TowerOpen.OpenAlongR` with the observer
an existential `W : ConfFlowG (SU N)` and the physical range `r` of its energy flow a clause, the other
clauses unchanged. DERIVED: `0` the signs. -/
def OpenAlongW (βs : ℕ → ℝ) : Prop :=
  ∃ (W : ConfFlowG (MassGap.SUN.SU N)) (r : ℝ)
    (_ : (energy0G (schedAlongG _ βs) W (SymPlaqClassG (MassGap.SUN.SU N))
      (symPlaqG_refl (MassGap.SUN.SU N))).PhysRange (schedAlongG _ βs) r)
    (s C₀ : ℝ) (_ : 0 < s)
    (_ : SiteExpG (schedAlongG _ βs) W (SymPlaqClassG (MassGap.SUN.SU N)) s C₀)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : CompositesRen.OffMix)
    (_ : ∃ Gk : ℝ → ℝ, TwoPointKernelG (schedAlongG _ βs) (rhoZ N zri zwe) Gk
      ∧ AFCoefficientG (constsG (MassGap.SUN.SU N)) Gk)
    (_ : NonGaussianTG (schedAlongG _ βs) (rhoZ N zri zwe))
    (_ : WardTG (schedAlongG _ βs) (rhoZ N zri zwe))
    (_ : CompOSG (schedAlongG _ βs) (csZ N zri zwe μ)),
    ApproxAlongW N βs W r zri zwe μ

/-- **`OpenAlongR ⇒ OpenAlongW`**: the instance `W = obsW N hc0 hc s₀` with
`ConsolidatedRoot.physRange_sunFam`. DERIVED: no numeral. -/
theorem openAlongW_of_openAlongR {βs : ℕ → ℝ} (h : OpenAlongR N βs) : OpenAlongW N βs := by
  obtain ⟨c, hc0, hc, s₀, r, hs0, hr, s, C₀, hs, hSE, zri, zwe, hri, hwe, μ, hK, hNG, hWard, hCO, hA⟩ := h
  exact ⟨obsW N hc0 hc s₀, r, physRange_sunFam βs hc0 hc hs0 hr, s, C₀, hs, hSE, zri, zwe, hri, hwe, μ,
    hK, hNG, hWard, hCO, hA⟩

/-- **`OpenAlongW ⇒ ExistAlong`**: the class moments from `SiteExpG` at `t = s / (2 · 1 + 3)⁴`
(`TowerOpen.classMomentsG_of_siteExpG`), the link from `linkAlongW`, and the spacing clauses of
`ConsolidatedRoot` §1. DERIVED: `0` the sign of `t`; `2`, `1`, `3`, `4` in `(2 · 1 + 3)⁴` the unit cube's
site count. -/
theorem existAlong_of_openW {βs : ℕ → ℝ} (h : OpenAlongW N βs) : ConstantPhysicsLine.ExistAlong N βs := by
  obtain ⟨W, r, hphys, s, C₀, hs, hSE, zri, zwe, hri, hwe, μ, ⟨Gk, hK, hAF⟩, hNG, hWard, hCO, hA⟩ := h
  have h625 : (0 : ℝ) < (2 * 1 + 3) ^ 4 := by norm_num
  have ht : 0 < s / (2 * 1 + 3) ^ 4 := div_pos hs h625
  have hSE' : SiteExpG (schedAlongG _ βs) W (SymPlaqClassG (MassGap.SUN.SU N))
      (s / (2 * 1 + 3) ^ 4 * (2 * 1 + 3) ^ 4) C₀ := by
    rw [div_mul_cancel₀ s h625.ne']
    exact hSE
  have hU := classMomentsG_of_siteExpG (schedAlongG _ βs) (schedShiftInv_alongG _ βs) W
    (symPlaqG_nonneg (G := MassGap.SUN.SU N)) ht hSE'
  obtain ⟨wC, hLC, hX⟩ := linkAlongW βs W hphys hU zri zwe μ hCO.1 hA
  exact ⟨W, _, _, ht, hU, r, hphys, rhoZ N zri zwe, riemann_rhoZ zri zwe, tie_rhoZ βs zri zwe,
    tensorCov_rhoZ βs zri zwe μ hCO, channel_rhoZ βs zri zwe, Gk, hK, hAF, hNG, hWard, csZ N zri zwe μ, wC,
    CompositesBuild.eI, he1_csZ zri zwe μ, he2_csZ zri zwe μ, compData_csZ hri hwe μ, hCO, hLC, hX⟩

/-- **The root at `SU(N)` from the strong end, (UV) and `OpenAlongW` along the towers near `0⁺`**
(`ConstantPhysicsLine.clayStatementOf_of_reads`, `existAlong_of_openW`). DERIVED: `0` the limit `0⁺`. -/
theorem clayStatementOf_of_openW (hS : StrongEnd N)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      ∃ μ : ℝ, UVConverges N βs id μ)
    (hO : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → OpenAlongW N βs) :
    ClayStatementOf (MassGap.SUN.SU N) :=
  ConstantPhysicsLine.clayStatementOf_of_reads hS hUV
    (hO.mono fun _ h βs hT => existAlong_of_openW (h βs hT))

end MassGap.ObserverTower

end

/-! ## 3. The root at any observer -/

noncomputable section

namespace MassGap.ObserverTower

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayTreeG MassGap.ClayStatementG MassGap.FlowG Filter
open scoped Topology
open MassGap.FlowAlong (cpl schedAlongG_eq)
open MassGap.MeasuredTower (schedAlongG)
open MassGap.CouplingTower (StrongEnd CouplingTower UVConverges)
open MassGap.CompositeLink (Φ0)
open MassGap.CompositesRen (OffMix)

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

/-- **The physical range of `Φ0 W` is the physical range of the energy flow of `W.toG` along `βs`**: the
schedule along `βs` has the `SU(N)` dyadic spacing. DERIVED: no numeral. -/
theorem physRangeG_of_physRange (βs : ℕ → ℝ) {W : ConfFlow N} {r : ℝ} (h : (Φ0 W).PhysRange r) :
    (energy0G (schedAlongG _ βs) W.toG (SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N))
      (SymPlaqG.symPlaqG_refl (MassGap.SUN.SU N))).PhysRange (schedAlongG _ βs) r := by
  filter_upwards [h] with k hk
  show (schedAlongG (MassGap.SUN.SU N) βs).a k * (W.range k : ℝ) ≤ r
  have ha : (schedAlongG (MassGap.SUN.SU N) βs).a k = dySpacing N k := congrFun (dySpacingG_SU N) k
  rw [ha]
  exact hk

omit [Fact (2 ≤ N)] in
set_option maxRecDepth 100000 in
/-- **The energy flow of `W.toG` on the copy of `schedSU` is `Φ0 W`**, field by field and by definition
(`FlowAlong.energy0G_along` at any `W`). DERIVED: no numeral. -/
theorem energy0G_alongW (βs : ℕ → ℝ) (W : ConfFlow N) :
    energy0G (CouplingGen.Along.ClayTreeG.schedSU (cpl βs) N) W.toG
        (SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N)) (SymPlaqG.symPlaqG_refl (MassGap.SUN.SU N))
      = (Φ0 W).toGFlow :=
  rfl

variable (N) in
/-- **The flow-side bundle along `βs` at any observer**: `FieldSweep.CoreInputsAlong` with the observer an
existential `W : ConfFlow N` with physical range `r`, every other field unchanged. DERIVED: `0` the
signs. -/
def CoreInputsAlongW (βs : ℕ → ℝ) : Prop :=
  ∃ (W : ConfFlow N) (r : ℝ) (_ : (Φ0 W).PhysRange r)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : CompositesBuild.Ix0 → ℝ → (MultiScaleAll.MIx →₀ ℝ)),
    CouplingGen.Along.SU2Best.SubstrateCoreAt (cpl βs) W (ZCanon.zFix N zri zwe) b Wf
      ∧ CouplingGen.Along.StrongExpand.ExpandStrong (cpl βs) Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ MultiScaleOS.CoefBound cf
      ∧ CouplingGen.Along.FlowCovN.FlowCovLim (cpl βs) Wf cf
      ∧ CouplingGen.Along.WardFromLattice.FlowWard (cpl βs) Wf cf
      ∧ CouplingGen.Along.NondegFromProxy.ProxyNondeg (cpl βs) Wf cf
      ∧ CouplingGen.Along.ProxyGenLimN.ProxyGenLimGerm (cpl βs) W b Wf cf r
      ∧ ∃ ℓ : ℝ, 0 < ℓ
          ∧ CouplingGen.Along.NonGaussFromScale.ThreePointAtScale (cpl βs) (NeZero.ne N) ℓ

/-- **`CoreInputsAlong ⇒ CoreInputsAlongW`**: the instance `W = sunFam … s₀` with
`ObserverFlowSUN.sunFam_physRange`. DERIVED: `2` the least rank. -/
theorem coreW_of_core {βs : ℕ → ℝ} (h : FieldSweep.CoreInputsAlong N βs) : CoreInputsAlongW N βs := by
  obtain ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, F⟩ := h
  exact ⟨_, r, ObserverFlowSUN.sunFam_physRange (Fact.out : 2 ≤ N) hc0 hc hs0 hr, zri, zwe, hri, hwe, μ, b,
    Wf, cf, F⟩

set_option maxRecDepth 100000 in
/-- **`CoreInputsAlongW ⇒ OpenAlongW`**: the clauses of `OpenAlongW` at `W.toG` from the copy of
`coreClausesW` at `cpl βs`, in the schedule form along `βs` (as `FieldSweep.openAlongR_of_core`).
DERIVED: `0` the signs; `2`, `1`, `3`, `4` in `(2 · 1 + 3)⁴` the unit cube's site count; `2` the least
rank. -/
theorem openAlongW_of_coreW {βs : ℕ → ℝ} (h : CoreInputsAlongW N βs) : OpenAlongW N βs := by
  obtain ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP, hL, h3⟩ := h
  obtain ⟨⟨t, C, ht, hSE⟩, ⟨Gk, hK, hAF⟩, hNG, hWT, hCO, hA⟩ :=
    CouplingGen.Along.ObserverTower.coreClausesW (cpl βs) (Fact.out : 2 ≤ N) hphys S hE hC hV hW hP hL h3
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

/-- **The root at `SU(N)` from the strong end, (UV) and the bundle at any observer along the towers near
`0⁺`** (`clayStatementOf_of_openW`, `openAlongW_of_coreW`). The observer is an existential
`W : ConfFlow N` (continuous, gauge covariant, reflection covariant, local within its range) with a physical
range; its hypothesis `hF` is implied by that of `FieldSweep.clayStatementOf_of_core` (`coreW_of_core`).
DERIVED: `0` the limit `0⁺`. -/
theorem clayStatementOf_of_coreObs (hS : StrongEnd N)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      ∃ μ : ℝ, UVConverges N βs id μ)
    (hF : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      CoreInputsAlongW N βs) :
    ClayStatementOf (MassGap.SUN.SU N) :=
  clayStatementOf_of_openW hS hUV (hF.mono fun _ h βs hT => openAlongW_of_coreW (h βs hT))

end MassGap.ObserverTower

end

#print axioms MassGap.ObserverTower.coreClausesW
#print axioms MassGap.CouplingGen.Along.ObserverTower.coreClausesW
#print axioms MassGap.ObserverTower.linkAlongW
#print axioms MassGap.ObserverTower.openAlongW_of_openAlongR
#print axioms MassGap.ObserverTower.existAlong_of_openW
#print axioms MassGap.ObserverTower.clayStatementOf_of_openW
#print axioms MassGap.ObserverTower.physRangeG_of_physRange
#print axioms MassGap.ObserverTower.energy0G_alongW
#print axioms MassGap.ObserverTower.coreW_of_core
#print axioms MassGap.ObserverTower.openAlongW_of_coreW
#print axioms MassGap.ObserverTower.clayStatementOf_of_coreObs
