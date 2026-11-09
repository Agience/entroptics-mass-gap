import Mathlib
import MassGap.FlowAlong
import MassGap.FlowCovN

/-!
# MassGap.FieldSweep — the flow-side bundle along the towers, field by field, at its consumed strength

`FlowAlong.clayStatementOf_of_flowAlong` takes `StrongEnd N`, (UV) and `FlowAlong.FlowInputsAlong N βs`
along the coupling towers near `0⁺`. This module reads each field of `FlowInputsAlong` against its
consumer and against the other fields, and states the root with every field at the strength the chain
reads it. Declarations are in the namespace `MassGap.FieldSweep`.

## 1. What each field gives (proved, at `dyBeta`, then along every tower)

The flow core, `b_pos`, `top`, `scale` (`ScaleControlAll`), `expand` (`ExpandStrong`) and `coef`
(`CoefBound`), gives the regularity clauses with no further input: the one-site exponential moment
(`CompositesRenAll.uv_of_scale`), `ConvC` (`FlowChoice.convC_of_choice`), `OS0C`
(`MultiScaleOS.os0C_of_scale_expand_coef`), `OS1C` (`MultiScaleOS.os1C_of_scale_expand`), `SepConv`
(`WardFromLattice.sepConv_of_scale_expand`), the observer's uniform bound and the proxies' bound
(`ProxyGenObserver.uB_of_core`, `ProxyBoundFromScale.proxyBound_of_core`). Each remaining field gives one
target clause, and under the core it is equivalent to it or to a clause between it and the target:

* `af` is the target clause `TwoPointKernel ∧ AFCoefficient` itself;
* `cov` (`FlowCov`) gives `FlowCovN.FlowCovLim` (`FlowCovN.flowCovLim_of_flowCov`), which under the core is
  `CovC` (`FlowCovN.flowCovLim_iff_covC_of_choice`); `FlowCov` is `CovC ∧ RemCov` (`FlowCovN`), and the
  chain reads only `FlowCovLim`;
* `ward` (`FlowWard`) is `WardT` under the core (`FlowChoice.flowWard_iff_wardT_of_choice`);
* `nondeg` (`ProxyNondeg`) is `CompNondeg` under the core (`FlowChoice.proxyNondeg_iff_compNondeg_of_choice`);
* `ProxyGenLim` gives its germ at `s → 0⁺` (`ProxyGenLimN.limGerm_of_proxyGenLim`), which with the core
  gives `ApproxK` (`ProxyGenLimN.approxK_of_germ`); the chain reads only the germ;
* the three-point clause gives `NonGaussianT` with `SepConv` (`NonGaussFromScale.obsLower_of_scale`).

No field is a consequence of the others: `af`, `ward`, `nondeg`, the germ and the three-point clause
are each a target clause moved onto the flowed proxies, and the core is the asymptotic-freedom moment
bound with the small-flow-time expansion. No field is discharged by a choice of the witnesses that keeps
the others (`FlowChoice`: zero coefficients meet `coef`, `cov` and `ward` and refute `nondeg`;
`ScaleSatisfiable.scaleAt_top`: `top` pins the moment at `s = b` to the observer). `b_pos` keeps `scale`
and `ProxyGenLim` from holding vacuously: at `b ≤ 0` the scale window `[a_k, b]` and the index set
`0 < s ≤ b` of `ProxyGenLim` are empty (the germ, an existential over that window, is then false).
Whether `scale` holds at the observer `sunFam … s₀` is open in the tree: `SunFamLeak` proves that a
boundary leak of the flowed plaquette (`SunFamLeak.PlaqLeak`) refutes the core at `sunFam`
(`SunFamLeak.not_substrateCoreAt_sunFam_of_leak`), and the leak's order is open in both directions
(`a³` argued in `ScaleSatisfiable` §3; a boundary field smooth on the flow scale gives `a⁵`, no leak).
`BulkBound` bounds the flowed configuration on every input of the core.

* **`coreClausesK`**: the clauses of `CouplingGen.flowClausesK` from the core, `FlowCovLim`, `FlowWard`,
  `ProxyNondeg`, the germ `ProxyGenLimGerm` and the three-point clause.

## 2. The copy along the towers

`#along_generalize_more` is `CouplingGen`'s `#along_generalize` that reuses the copies already in the
environment: a declaration whose copy `MassGap.CouplingGen.Along.X` exists is not copied again. It copies
`coreClausesK`, `FlowCovN.flowCovLim_of_flowCov`, `ProxyGenLimN.limGerm_of_proxyGenLim` and the three
equivalences `FlowCovN.flowCovLim_iff_covC_of_choice`, `FlowChoice.flowWard_iff_wardT_of_choice`,
`FlowChoice.proxyNondeg_iff_compNondeg_of_choice` over the coupling family, with the field projections of
`SubstrateCoreAt`, `GradientFlowProps` and `GradientFlowPropsN` (the copied structures have no `casesOn`,
so their fields are read through the copied projections). Every copy is checked by the kernel; none
fails, so none of these proofs reads the definition of `dyBeta`.

## 3. The root

* `CoreInputsAlong N βs`: `FlowInputsAlong N βs` with `cov` read as `FlowCovLim` and `ProxyGenLim` read as
  its germ, the other fields unchanged.
* **`coreAlong_of_flowAlong`**: `FlowInputsAlong N βs ⇒ CoreInputsAlong N βs`.
* **`openAlongR_of_core`**: `CoreInputsAlong N βs ⇒ TowerOpen.OpenAlongR N βs`.
* **`clayStatementOf_of_core`**: `StrongEnd N`, (UV) and `CoreInputsAlong` along the towers near `0⁺` give
  `ClayStatementOf (SU N)`. Its hypothesis is implied by that of `FlowAlong.clayStatementOf_of_flowAlong`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the signs, the lower end of the observer's scale, the plane and the limit
`0⁺`; `2` the least rank; `2`, `1`, `3`, `4` in `(2 · 1 + 3)⁴` the unit cube's site count; `π` in `π/N`
the angle of the centre of `SU(N)`; `12` a sufficient bound on `c`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.FieldSweep

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
  MassGap.ProxyGenObserver MassGap.ProxyBoundFromScale MassGap.ObserverFlowSUN

/-! ## 1. The clauses at `stateK` from the bundle at its consumed strength -/

section Clauses

variable {N : ℕ}

/-- **The flow-side clauses from the core and the five target-side fields**: `CouplingGen.flowClausesK`
with `FlowCov` read as `FlowCovN.FlowCovLim` (`FlowCovN.covC_of_flowCovLim`) and `ProxyGenLim` read as its
germ (`ProxyGenLimN.germ_of_limGerm`, `ProxyGenLimN.approxK_of_germ`). DERIVED: `2` the least colour
count; `0` the lower end of the observer's scale and the plane; `2`, `1`, `3`, `4` in `(2 · 1 + 3)⁴` the
unit cube's site count; `π` in `π/N` the angle of the centre of `SU(N)`; `12` a sufficient bound on `c`. -/
theorem coreClausesK (hN2 : 2 ≤ N) [NeZero N] {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) {s₀ r : ℝ} (hs0 : 0 ≤ s₀) (hr : s₀ < r)
    {zri zwe : ℕ → ℝ} {μ : OffMix} {b : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCoreAt (sunFam hN2 c hc0 hc s₀) (ZCanon.zFix N zri zwe) b Wf)
    (hE : ExpandStrong Wf cf (ZCanon.zFix N zri zwe) μ) (hC : CoefBound cf)
    (hV : FlowCovN.FlowCovLim Wf cf) (hW : WardFromLattice.FlowWard Wf cf) (hP : ProxyNondeg Wf cf)
    (hL : ProxyGenLimN.ProxyGenLimGerm (sunFam hN2 c hc0 hc s₀) b Wf cf r)
    (h3 : ∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (NeZero.ne N) ℓ) :
    (∃ t C : ℝ, 0 < t ∧ FlowUV.SiteExp (NeZero.ne N) (sunFam hN2 c hc0 hc s₀) (SymPlaqClass N)
        (t * (2 * 1 + 3) ^ 4) C)
      ∧ (∃ G : ℝ → ℝ, TwoPointKernel (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe)) G
          ∧ AFCoefficient N G)
      ∧ NonGaussianT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe))
      ∧ WardT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe))
      ∧ CompOS (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ ApproxK (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
          (mixKG hN2 (sunFam hN2 c hc0 hc s₀) (CRen N (ZCanon.zFix N zri zwe) μ) r)
          (gramF hN2 (sunFam hN2 c hc0 hc s₀) r) := by
  have hER := expandR_of_strong hE
  obtain ⟨t, C, ht, hS⟩ := uv_of_scale S.b_pos S.top S.scale
  have hU := ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) (sunFam hN2 c hc0 hc s₀) ht hS
  have hphys := sunFam_physRange hN2 hc0 hc hs0 hr
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

end MassGap.FieldSweep

end

/-! ## 2. The copy over a coupling family, reusing the copies in the environment -/

namespace MassGap.FieldSweep

section Generate

open Lean Meta Elab Command
open MassGap.CouplingGen (GenM isTainted constRefs addAlong alongName)

/-- Copy `n` and every tainted declaration it reaches, dependencies first, as `CouplingGen.gen`, except
that a declaration whose copy is already in the environment is not copied again. DERIVED: no numeral. -/
partial def genMore (src : Name) (B : Expr) (n : Name) : GenM Bool := do
  if n == src then return true
  unless (← isTainted src n) do return true
  if (← getEnv).contains (alongName n) then return true
  if let some b := (← get).done[n]? then return b
  modify fun s => { s with done := s.done.insert n true }
  let ci ← getConstInfo n
  let ok ← match ci with
    | .ctorInfo v => genMore src B v.induct
    | .recInfo v => match v.all with
      | i :: _ => genMore src B i
      | [] => pure false
    | _ => do
      let own : NameSet := match ci with
        | .inductInfo v => v.ctors.foldl (·.insert ·) (({} : NameSet).insert n)
        | _ => ({} : NameSet).insert n
      let mut okDeps := true
      for d in (← constRefs ci) do
        unless own.contains d do
          unless (← genMore src B d) do okDeps := false
      if okDeps then addAlong src B ci else pure false
  modify fun s => { s with done := s.done.insert n ok }
  return ok

/-- `#along_generalize_more src from r₁ … rₙ`: `#along_generalize` reusing the copies in the
environment. DERIVED: no numeral. -/
elab "#along_generalize_more " src:ident " from " roots:ident+ : command => do
  let srcN ← liftCoreM <| realizeGlobalConstNoOverload src
  let rootNs ← roots.mapM fun r => liftCoreM <| realizeGlobalConstNoOverload r
  liftCoreM do
    let B := mkFVar ⟨`_along_B⟩
    let (oks, st) ← (rootNs.mapM fun r => genMore srcN B r).run {}
    let rs := (rootNs.zip oks).map fun (a, b) => s!"{a}: {b}"
    logInfo m!"along: {st.added} copies added; failed: {st.failed}; roots copied: {rs}"
    unless st.failed.isEmpty && oks.all id do
      throwError "along: a copy failed the kernel check"

end Generate

set_option Elab.async false in
set_option maxHeartbeats 0 in
#along_generalize_more MassGap.ContinuumSchwinger.dyBeta from MassGap.FieldSweep.coreClausesK
  MassGap.FlowCovN.flowCovLim_of_flowCov MassGap.ProxyGenLimN.limGerm_of_proxyGenLim
  MassGap.FlowCovN.flowCovLim_iff_covC_of_choice MassGap.FlowChoice.flowWard_iff_wardT_of_choice
  MassGap.FlowChoice.proxyNondeg_iff_compNondeg_of_choice MassGap.SU2Best.SubstrateCoreAt.b_pos
  MassGap.SU2Best.SubstrateCoreAt.scale MassGap.SU2Best.GradientFlowProps.expand
  MassGap.SU2Best.GradientFlowProps.coef MassGap.SU2Best.GradientFlowProps.cov
  MassGap.SU2Best.GradientFlowProps.ward MassGap.NondegFromProxy.GradientFlowPropsN.props
  MassGap.NondegFromProxy.GradientFlowPropsN.nondeg

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

end MassGap.FieldSweep

/-! ## 3. The root along the towers -/

noncomputable section

namespace MassGap.FieldSweep

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayTreeG MassGap.ClayStatementG MassGap.FlowG Filter
open scoped Topology
open MassGap.FlowAlong (cpl FlowInputsAlong schedAlongG_eq energy0G_along)
open MassGap.CouplingTower (StrongEnd CouplingTower UVConverges)
open MassGap.TowerOpen (OpenAlongR)
open MassGap.LinkAlongG (ApproxAlong)
open MassGap.ObserverFlowSUN (sunFam)
open MassGap.CompositesRen (OffMix)

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

variable (N) in
/-- **The flow-side bundle along `βs` at its consumed strength**: `FlowInputsAlong` with `FlowCov` read as
`FlowCovLim` and `ProxyGenLim` as its germ at `s → 0⁺` (module docstring). DERIVED: `0` the signs and the
lower end of the observer's scale; `2` the least rank; `π` in `π/N` the angle of the centre of `SU(N)`;
`12` a sufficient bound on `c`. -/
def CoreInputsAlong (βs : ℕ → ℝ) : Prop :=
  ∃ (c : ℝ) (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N)) (s₀ r : ℝ) (_ : 0 ≤ s₀) (_ : s₀ < r)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : CompositesBuild.Ix0 → ℝ → (MultiScaleAll.MIx →₀ ℝ)),
    CouplingGen.Along.SU2Best.SubstrateCoreAt (cpl βs) (sunFam (Fact.out : 2 ≤ N) c hc0 hc s₀)
        (ZCanon.zFix N zri zwe) b Wf
      ∧ CouplingGen.Along.StrongExpand.ExpandStrong (cpl βs) Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ MultiScaleOS.CoefBound cf
      ∧ CouplingGen.Along.FlowCovN.FlowCovLim (cpl βs) Wf cf
      ∧ CouplingGen.Along.WardFromLattice.FlowWard (cpl βs) Wf cf
      ∧ CouplingGen.Along.NondegFromProxy.ProxyNondeg (cpl βs) Wf cf
      ∧ CouplingGen.Along.ProxyGenLimN.ProxyGenLimGerm (cpl βs) (sunFam (Fact.out : 2 ≤ N) c hc0 hc s₀)
          b Wf cf r
      ∧ ∃ ℓ : ℝ, 0 < ℓ
          ∧ CouplingGen.Along.NonGaussFromScale.ThreePointAtScale (cpl βs) (NeZero.ne N) ℓ

/-- **`FlowInputsAlong ⇒ CoreInputsAlong`**: `FlowCov` gives `FlowCovLim` under the core
(`FlowCovN.flowCovLim_of_flowCov` along `βs`), and `ProxyGenLim` gives its germ
(`ProxyGenLimN.limGerm_of_proxyGenLim` along `βs`). DERIVED: `2` the least rank. -/
theorem coreAlong_of_flowAlong {βs : ℕ → ℝ} (h : FlowInputsAlong N βs) : CoreInputsAlong N βs := by
  obtain ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, F, hL, h3⟩ := h
  have hb := CouplingGen.Along.SU2Best.SubstrateCoreAt.b_pos (cpl βs) S
  have hsc := CouplingGen.Along.SU2Best.SubstrateCoreAt.scale (cpl βs) S
  have Fp := CouplingGen.Along.NondegFromProxy.GradientFlowPropsN.props (cpl βs) F
  have hE := CouplingGen.Along.SU2Best.GradientFlowProps.expand (cpl βs) Fp
  exact ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE,
    CouplingGen.Along.SU2Best.GradientFlowProps.coef (cpl βs) Fp,
    CouplingGen.Along.FlowCovN.flowCovLim_of_flowCov (cpl βs) hb hsc hE
      (CouplingGen.Along.SU2Best.GradientFlowProps.cov (cpl βs) Fp),
    CouplingGen.Along.SU2Best.GradientFlowProps.ward (cpl βs) Fp,
    CouplingGen.Along.NondegFromProxy.GradientFlowPropsN.nondeg (cpl βs) F,
    CouplingGen.Along.ProxyGenLimN.limGerm_of_proxyGenLim (cpl βs) hb hL, h3⟩

set_option maxRecDepth 100000 in
/-- **`CoreInputsAlong ⇒ OpenAlongR`**: the clauses of `OpenAlongR` from the copy of `coreClausesK` at
`cpl βs`, in the schedule form along `βs` (as `FlowAlong.openAlongR_of_flowAlong`). DERIVED: `0` the
signs; `2`, `1`, `3`, `4` in `(2 · 1 + 3)⁴` the unit cube's site count; `2` the least rank. -/
theorem openAlongR_of_core {βs : ℕ → ℝ} (h : CoreInputsAlong N βs) : OpenAlongR N βs := by
  obtain ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP, hL, h3⟩ := h
  obtain ⟨⟨t, C, ht, hSE⟩, ⟨Gk, hK, hAF⟩, hNG, hWT, hCO, hA⟩ :=
    CouplingGen.Along.FieldSweep.coreClausesK (cpl βs) (Fact.out : 2 ≤ N) hc0 hc hs0 hr S hE hC hV hW hP
      hL h3
  have hsched := schedAlongG_eq (N := N) βs
  refine ⟨c, hc0, hc, s₀, r, hs0, hr, t * (2 * 1 + 3) ^ 4, C, by positivity, ?_, zri, zwe, hri, hwe, μ,
    ⟨Gk, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
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
  · unfold ApproxAlong
    rw [hsched, energy0G_along βs hc0 hc s₀]
    exact hA

/-- **The root at `SU(N)` from the strong end, (UV) and the bundle at its consumed strength along the
towers near `0⁺`** (`TowerOpen.clayStatementOf_of_reduced`, `openAlongR_of_core`). Its hypothesis `hF` is
implied by that of `FlowAlong.clayStatementOf_of_flowAlong` (`coreAlong_of_flowAlong`). DERIVED: `0` the
limit `0⁺`; `2` the least rank. -/
theorem clayStatementOf_of_core (hS : StrongEnd N)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      ∃ μ : ℝ, UVConverges N βs id μ)
    (hF : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      CoreInputsAlong N βs) :
    ClayStatementOf (MassGap.SUN.SU N) :=
  TowerOpen.clayStatementOf_of_reduced hS hUV
    (hF.mono fun _ h βs hT => openAlongR_of_core (h βs hT))

end MassGap.FieldSweep

end

#print axioms MassGap.FieldSweep.coreClausesK
#print axioms MassGap.CouplingGen.Along.FieldSweep.coreClausesK
#print axioms MassGap.CouplingGen.Along.FlowCovN.flowCovLim_of_flowCov
#print axioms MassGap.CouplingGen.Along.ProxyGenLimN.limGerm_of_proxyGenLim
#print axioms MassGap.CouplingGen.Along.FlowCovN.flowCovLim_iff_covC_of_choice
#print axioms MassGap.CouplingGen.Along.FlowChoice.flowWard_iff_wardT_of_choice
#print axioms MassGap.CouplingGen.Along.FlowChoice.proxyNondeg_iff_compNondeg_of_choice
#print axioms MassGap.FieldSweep.coreAlong_of_flowAlong
#print axioms MassGap.FieldSweep.openAlongR_of_core
#print axioms MassGap.FieldSweep.clayStatementOf_of_core
