import Mathlib
import MassGap.TowerOpen

/-!
# MassGap.CouplingGen — the flow-side chain of `SU(N)` at any coupling sequence

The step-`k` state of the two-loop schedule is `stateK hN k = periodicState hN (dyBeta hN k)`, with
`dyBeta hN k` a coupling chosen by `Classical.choose` so that the two-loop running spacing at it is
`dySpacing N k` (`ContinuumSchwinger.aRun_dyBeta`). The proofs of the flow-side clauses at `SU(N)` —
the one-site exponential moment, non-Gaussianity, the Ward identity, `CompOS` of the composites and
`ApproxK` of the three kernels — read `stateK` through properties of the periodic state that hold at
every coupling (reflection positivity, reflection and translation invariance, the link change of
variables), and never through `aRun_dyBeta`, `one_le_dyBeta` or `tendsto_dyBeta`. So the whole chain
holds with `dyBeta` replaced by any family of couplings.

This module carries out that replacement in the kernel. `flowClausesK` states the clauses at `stateK`
from the flow-side bundle of `SUNFromScale.FlowInputsN` without its gap field `RunSeed`. The command
`#along_generalize dyBeta from …` then walks every declaration that the listed roots reach and that
mentions `dyBeta` (directly or through another such declaration), and adds for each one a copy over a
variable coupling family `B : {N : ℕ} → 1 ≤ N → ℕ → ℝ`: the copy of `X` is
`MassGap.CouplingGen.Along.X` (the prefix `MassGap.` of `X` dropped), its first argument is `B`, and its
type and value are those of `X` with `dyBeta` replaced by `B` and every such declaration `Y` by the copy
`Along.Y B`. Structures are copied as inductive types with `B` as their first parameter, with their
constructors and recursors. Every copy is checked by the kernel; a copy whose proof used the definition
of `dyBeta` (its `Classical.choose` specification) fails the check and is reported, and so is every
declaration that depends on it. No such failure occurs for the roots below.

The copies at `B = fun _ _ => βs` are the chain along the coupling sequence `βs`: the state of step `k`
is `periodicState hN (βs k)` (`ContinuumSchwinger.stateAlong`) at the same spacing `dySpacing N k`.
`MassGap.FlowAlong` reads them along every coupling tower.

## Roots

* `flowClausesK`: the clauses at `stateK` from `SubstrateCoreAt`, `GradientFlowPropsN`, `ProxyGenLim`
  and the three-point clause at the block-step observer `sunFam hN2 c hc0 hc s₀`;
* `ClayTreeG.schedSU`: the schedule of `ClayStatement` (`dySpacing N`, `stateK`), whose copy is the
  schedule along `βs` and which carries the `SU(N)` clauses to the schedule form.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` the least colour count; `0` the lower end of the observer's scale and the
plane; `1`, `3`, `4` in `(2 · 1 + 3)⁴` the unit cube's site count; `4` the canonical dimension; `π` in
`π/N` the angle of the centre of `SU(N)`; `12` a sufficient bound on `c`.
At `B = dyBeta` each copy is definitionally equal to its original; `FlowAlong.flowAlong_dyBeta` uses this.
The check after the command confirms that no copy mentions `dyBeta`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.CouplingGen

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

/-! ## 1. The clauses at `stateK` from the flow-side bundle -/

section Clauses

variable {N : ℕ}

/-- **The flow-side clauses at the block-step observer**, from the substrate core, the flow bundle,
`ProxyGenLim` and the three-point clause (`SUNFromScale.inputsAt_of_flow` without the gap): one
exponential moment of the flowed reading at one site (`CompositesRenAll.uv_of_scale`), the two-point
kernel with its asymptotic-freedom coefficient (`S.af`), non-Gaussianity
(`InputsTriage.nonGaussianT_rhoD_of_lower`, `NonGaussFromScale.obsLower_of_scale`,
`WardFromLattice.sepConv_of_scale_expand`), the Ward identity (`SU2Best.wardT_of_core`), `CompOS` of the
composites, and `ApproxK` of the three kernels (`ApproxFromExpand.approxK_of_expandRP_SU`). DERIVED: `2`
the least colour count; `0` the lower end of the observer's scale and the plane; `2`, `1`, `3`, `4` in
`(2 · 1 + 3)⁴` the unit cube's site count; `π` in `π/N` the angle of the centre of `SU(N)`; `12` a
sufficient bound on `c`. -/
theorem flowClausesK (hN2 : 2 ≤ N) [NeZero N] {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) {s₀ r : ℝ} (hs0 : 0 ≤ s₀) (hr : s₀ < r)
    {zri zwe : ℕ → ℝ} {μ : OffMix} {b : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCoreAt (sunFam hN2 c hc0 hc s₀) (ZCanon.zFix N zri zwe) b Wf)
    (F : GradientFlowPropsN Wf cf (ZCanon.zFix N zri zwe) μ)
    (hL : ProxyGenLim (sunFam hN2 c hc0 hc s₀) b Wf cf r)
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
  have hE := expandR_of_strong F.props.expand
  obtain ⟨t, C, ht, hS⟩ := uv_of_scale S.b_pos S.top S.scale
  have hU := ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) (sunFam hN2 c hc0 hc s₀) ht hS
  have hphys := sunFam_physRange hN2 hc0 hc hs0 hr
  have hCO : CompOS (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) :=
    ⟨convC_of_core S F.props, os0C_of_scale_expand_coef S.b_pos S.scale hE F.props.coef,
      os1C_of_scale_expand S.b_pos S.scale hE,
      covC_of_scale_strong S.b_pos S.scale F.props.expand F.props.cov,
      compNondeg_of_core S F.props F.nondeg⟩
  obtain ⟨ℓ, hℓ, h3'⟩ := h3
  exact ⟨⟨t, C, ht, hS⟩, S.af,
    InputsTriage.nonGaussianT_rhoD_of_lower (NeZero.ne N) (fR N) (ZCanon.zFix N zri zwe)
      (WardFromLattice.sepConv_of_scale_expand S.b_pos S.scale hE)
      (obsLower_of_scale (NeZero.ne N) hℓ zri zwe h3'),
    wardT_of_core S F.props, hCO,
    approxK_of_expandRP_SU hN2 hU hphys hCO (expandRP_of_strong S.b_pos F.props.expand)
      (proxyGen_of_lim (uB_of_core S) (proxyBound_of_core S) hL)⟩

end Clauses

end MassGap.CouplingGen

end

/-! ## 2. The copy over a coupling family -/

namespace MassGap.CouplingGen

section Generate

open Lean Meta Elab Command

/-- **The name of the copy** of `n`: `MassGap.CouplingGen.Along` followed by `n` without its leading
`MassGap`. DERIVED: no numeral. -/
def alongName (n : Name) : Name :=
  `MassGap.CouplingGen.Along ++ n.replacePrefix `MassGap .anonymous

/-- The state of the walk: which declarations mention the source, which copies are made, which
failed. DERIVED: no numeral. -/
structure GenState where
  /-- Whether a declaration mentions the source, directly or through another one. -/
  taint : Std.HashMap Name Bool := {}
  /-- Whether the copy of a declaration is in the environment. -/
  done : Std.HashMap Name Bool := {}
  /-- Declarations whose copy failed the kernel check. -/
  failed : Array Name := #[]
  /-- Number of copies added. -/
  added : Nat := 0

/-- The walk's monad. DERIVED: no numeral. -/
abbrev GenM := StateRefT GenState CoreM

/-- Whether a declaration lives in a `MassGap` module (or in the current one). DERIVED: no numeral. -/
def inMassGap (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => match env.header.moduleNames[i]? with
    | some m => (`MassGap).isPrefixOf m
    | none => false
  | none => true

/-- The constants and the projected structures an expression mentions. DERIVED: no numeral. -/
def refs (e : Expr) : CoreM (Array Name) := do
  let r ← IO.mkRef (#[] : Array Name)
  e.forEach fun x => match x with
    | .const n _ => r.modify (·.push n)
    | .proj s _ _ => r.modify (·.push s)
    | _ => pure ()
  r.get

/-- The constants a declaration mentions: its type, its value, the types of its constructors, the
inductive type of a constructor or recursor. DERIVED: no numeral. -/
def constRefs (ci : ConstantInfo) : CoreM (Array Name) := do
  let mut cs ← refs ci.type
  match ci with
  | .defnInfo v => cs := cs ++ (← refs v.value)
  | .thmInfo v => cs := cs ++ (← refs v.value)
  | .opaqueInfo v => cs := cs ++ (← refs v.value)
  | .inductInfo v =>
    for c in v.ctors do
      cs := cs ++ (← refs (← getConstInfo c).type)
  | .ctorInfo v => cs := cs.push v.induct
  | .recInfo v => cs := cs ++ v.all.toArray
  | _ => pure ()
  return cs

/-- Whether `n` mentions `src`, directly or through another declaration. DERIVED: no numeral. -/
partial def isTainted (src n : Name) : GenM Bool := do
  if n == src then return true
  if let some b := (← get).taint[n]? then return b
  modify fun s => { s with taint := s.taint.insert n false }
  let env ← getEnv
  unless inMassGap env n do return false
  let some ci := env.find? n | return false
  let mut t := false
  for c in (← constRefs ci) do
    if c != n then
      if (← isTainted src c) then t := true
  modify fun s => { s with taint := s.taint.insert n t }
  return t

/-- The expression with `src` replaced by `B` and every tainted declaration `Y` by `Along.Y B`.
DERIVED: no numeral. -/
partial def tr (taint : Std.HashMap Name Bool) (src : Name) (B : Expr) (e : Expr) : Expr :=
  e.replace fun x => match x with
    | .const n us =>
      if n == src then some B
      else if taint.getD n false then some (mkApp (.const (alongName n) us) B) else none
    | .proj s i b =>
      if taint.getD s false then some (.proj (alongName s) i (tr taint src B b)) else none
    | _ => none

/-- Add the copy of one declaration, all of whose tainted dependencies have copies. DERIVED: no
numeral. -/
def addAlong (src : Name) (B : Expr) (ci : ConstantInfo) : GenM Bool := do
  let taint := (← get).taint
  let tyB := (← getConstInfo src).type
  let close (body : Expr) (pi : Bool) : Expr :=
    let b := (tr taint src B body).abstract #[B]
    if pi then .forallE `B tyB b .default else .lam `B tyB b .default
  let n' := alongName ci.name
  let decl : Declaration ← match ci with
    | .defnInfo v =>
      let d : DefinitionVal :=
        { name := n', levelParams := v.levelParams, type := close v.type true,
          value := close v.value false, hints := v.hints, safety := v.safety, all := [n'] }
      pure (.defnDecl d)
    | .thmInfo v =>
      let d : TheoremVal :=
        { name := n', levelParams := v.levelParams, type := close v.type true,
          value := close v.value false, all := [n'] }
      pure (.thmDecl d)
    | .opaqueInfo v =>
      let d : OpaqueVal :=
        { name := n', levelParams := v.levelParams, type := close v.type true,
          value := close v.value false, isUnsafe := v.isUnsafe, all := [n'] }
      pure (.opaqueDecl d)
    | .inductInfo v => do
      unless v.all.length == 1 do throwError "along: mutual inductive {ci.name}"
      let ctors ← v.ctors.mapM fun c => do
        let cc ← getConstInfo c
        let k : Constructor := { name := alongName c, type := close cc.type true }
        pure k
      let t : InductiveType := { name := n', type := close v.type true, ctors := ctors }
      pure (.inductDecl v.levelParams (v.numParams + 1) [t] v.isUnsafe)
    | _ => throwError "along: unsupported declaration {ci.name}"
  try
    addDecl decl
    let st ← getReducibilityStatus ci.name
    if st != .semireducible then setReducibilityStatus n' st
    modify fun s => { s with added := s.added + 1 }
    return true
  catch ex =>
    logError m!"along: {ci.name}: {ex.toMessageData}"
    modify fun s => { s with failed := s.failed.push ci.name }
    return false

/-- Copy `n` and every tainted declaration it reaches, dependencies first. Returns whether the copy
of `n` (if `n` is tainted) is in the environment. DERIVED: no numeral. -/
partial def gen (src : Name) (B : Expr) (n : Name) : GenM Bool := do
  if n == src then return true
  unless (← isTainted src n) do return true
  if let some b := (← get).done[n]? then return b
  modify fun s => { s with done := s.done.insert n true }
  let ci ← getConstInfo n
  let ok ← match ci with
    | .ctorInfo v => gen src B v.induct
    | .recInfo v => match v.all with
      | i :: _ => gen src B i
      | [] => pure false
    | _ => do
      let own : NameSet := match ci with
        | .inductInfo v => v.ctors.foldl (·.insert ·) (({} : NameSet).insert n)
        | _ => ({} : NameSet).insert n
      let mut okDeps := true
      for d in (← constRefs ci) do
        unless own.contains d do
          unless (← gen src B d) do okDeps := false
      if okDeps then addAlong src B ci else pure false
  modify fun s => { s with done := s.done.insert n ok }
  return ok

/-- `#along_generalize src from r₁ … rₙ`: copy every declaration the roots reach that mentions `src`
over a variable `B : type of src` in place of `src`. DERIVED: no numeral. -/
elab "#along_generalize " src:ident " from " roots:ident+ : command => do
  let srcN ← liftCoreM <| realizeGlobalConstNoOverload src
  let rootNs ← roots.mapM fun r => liftCoreM <| realizeGlobalConstNoOverload r
  liftCoreM do
    let B := mkFVar ⟨`_along_B⟩
    let (oks, st) ← (rootNs.mapM fun r => gen srcN B r).run {}
    let nT : Nat := st.taint.fold (fun a _ b => if b then a + 1 else a) 0
    let rs := (rootNs.zip oks).map fun (a, b) => s!"{a}: {b}"
    logInfo m!"along: {nT} declarations mention {srcN}; {st.added} copies added; \
      failed: {st.failed}; roots copied: {rs}"

end Generate

set_option Elab.async false in
set_option maxHeartbeats 0 in
#along_generalize MassGap.ContinuumSchwinger.dyBeta from MassGap.CouplingGen.flowClausesK
  MassGap.ClayTreeG.schedSU

-- No copy mentions the source: every constant of this module under `MassGap.CouplingGen.Along` is free of
-- `dyBeta`, in its type and its value.
run_cmd do
  let env ← Lean.getEnv
  let src := ``MassGap.ContinuumSchwinger.dyBeta
  let pre := `MassGap.CouplingGen.Along
  let mut n : Nat := 0
  for (c, ci) in env.constants.map₂.toList do
    if pre.isPrefixOf c then
      n := n + 1
      let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
      if used.contains src then
        throwError "copy {c} still mentions {src}"
  if n == 0 then throwError "no copies found under {pre}"
  Lean.logInfo m!"along check: {n} copies, none mentions {src}"

end MassGap.CouplingGen

#print axioms MassGap.CouplingGen.flowClausesK
#print axioms MassGap.CouplingGen.Along.CouplingGen.flowClausesK
#print axioms MassGap.CouplingGen.Along.ClayTreeG.schedSU
