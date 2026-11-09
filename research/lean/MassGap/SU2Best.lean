import Mathlib
import MassGap.ObserverChoice
import MassGap.WardFromLattice

/-!
# MassGap.SU2Best — the `SU(2)` substrate and flow bundles of the rooted reductions

This module states the bundles that five reductions already proved elsewhere read. It proves no new
mathematics. Declarations are in the namespace `MassGap.SU2Best`.

* `StrongExpand` (`ExpandStrong`): one operator-form expansion clause `ExpandStrong` gives `ExpandR` and
  `ExpandRP`.
* `CovFromFlow.covC_of_strong`: `CovC` of the renormalised composites from `FlowCov`.
* `WardFromLattice.wardT_of_flowWard`: `WardT` from `FlowWard`, under `SepConv` (from
  `WardFromLattice.sepConv_of_multiScale`) and `ExpandR`.
* `ObserverChoice.obsW_physRange`: `PhysRange r` of the fixed observer `obsW` for every `r > 1`.
* `ZCanon.zFix`: at `z = zFix 2 zri zwe` the inputs `hz`, `hzS`, `hzP` hold when `zri`, `zwe` are nowhere
  zero.

## 1. The bundles

* `SubstrateAt W z b Wf`: `StrongExpand.MultiScaleStrongAt` without its `expand` field (`b_pos`, `top`,
  `scale`, `af`, `endpoint`).
* `GradientFlowProps Wf cf z μ`: the clauses about the flowed proxies and their expansion: `expand :
  ExpandStrong Wf cf z μ`, `coef : CoefBound cf`, `cov : FlowCov Wf cf`, `ward : FlowWard Wf cf`.
* `SubstrateAt.toStrong`: the two together give `MultiScaleStrongAt W z μ b Wf cf`.
* At every `SU(N)` (`[NeZero N]`): `GradientFlowProps Wf cf z μ` with `Wf : ℝ → ConfFlow N`;
  `SubstrateCoreAt W z b Wf`, the fields of `SubstrateAt` other than `endpoint` (`SubstrateAt.toCore` at
  `N = 2`); `SubstrateCoreAt.toFlowRen` gives `CompositesRenAll.FlowRenAt`; `wardT_of_core` gives
  `WardT (rhoD (fR N) z)`.

## 2. No capstone through `SubstrateAt`

No `ClayStatementAt` is stated from `SubstrateAt`: its `endpoint` field,
`MultiScale.Endpoint`, is refuted by `InputAudit.not_multiScaleEndpoint` under the argued growth of the zero-flux level count. `SubstrateCoreAt` drops that field; `SUNFromScale` and
`SUNBest` read it with the gap `RunSeed N` as a separate input.

## 3. Ledger: the fields of the bundles

Substrate (`SubstrateAt obsW (zFix 2 zri zwe) b Wf`, with `hri`, `hwe`):
* `b_pos`, `top : Wf b = obsW`: hold by definition for `Wf = FlowZero.apeFam (1/12)`, `b = 1`
  (`ObserverChoice`, §3); not instantiated here.
* `scale : ScaleControlAll b Wf`: OPEN (the asymptotic-freedom moments of every flowed monomial).
* `af`: a two-point kernel of the trace at `z` with the asymptotic-freedom coefficient: OPEN.
* `endpoint : MultiScale.Endpoint`, including `ScaleControlRun.OddLevels`: refuted by
  `InputAudit.not_multiScaleEndpoint` under the argued growth of the zero-flux level count.
* `hri`, `hwe`: the renormalisation factors `zri`, `zwe` are nowhere zero: a choice, constrained only by
  the inputs that read `z`.

Flow (`GradientFlowProps Wf cf (zFix 2 zri zwe) μ`):
* `expand : ExpandStrong`: OPEN; ARGUED as the small-flow-time expansion in operator form.
* `coef : CoefBound cf`: OPEN; ARGUED as the boundedness of the expansion coefficients.
* `cov : FlowCov`: OPEN; ARGUED as the rotation covariance of the flowed proxies near `s = 0`.
* `ward : FlowWard`: OPEN; ARGUED as the translation Ward identity of the flowed proxies near `s = 0`
  (`WardFromLattice` proves the exact lattice translation and link-change identities it rests on).

Observer (`ProxyGen obsW b Wf cf r`): OPEN; the flowed proxies are approximated in the reflection form by
margin monomials of `obsW` at margin `r > 1`.

Non-vanishing:
* `ObsLower (zFix 2 zri zwe)`: OPEN (the lower bound that stands for `NonGaussianT`).
* `CompNondeg (CRen 2 (zFix 2 zri zwe) μ)`: OPEN. `StrongExpand.not_compNondeg_of_expandStrong_zero`
  excludes it at the zero coefficients `cf = 0` whenever one combination has a non-zero on-shell classical
  part.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` is `SU(2)` and the limits of the scalar and pseudoscalar factors; `1` the
physical smearing scale of the observer and the bound below `r`; `4` the dimension.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.SU2Best

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

local notation "h2N" => (ne_zero_of_two_le (le_refl 2) : (2 : ℕ) ≠ 0)

variable {N : ℕ}

/-! ## 1. The bundles -/

/-- **The substrate**: `MultiScaleStrongAt` without the expansion clause. DERIVED: `0` the lower end of
the scale; `2` is `SU(2)`. -/
structure SubstrateAt (W : ConfFlow 2) (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow 2) : Prop where
  b_pos : 0 < b
  /-- The flow to the physical scale is `W`. -/
  top : Wf b = W
  /-- Every intermediate scale: the asymptotic-freedom moments of every monomial. -/
  scale : ScaleControlAll b Wf
  /-- Asymptotic freedom: a two-point kernel of the trace at `z` with the asymptotic-freedom coefficient. -/
  af : ∃ G : ℝ → ℝ, TwoPointKernel h2N (rhoD (fR 2) z) G ∧ AFCoefficient 2 G
  /-- Strong coupling at the physical scale: the slice endpoint with the odd levels. -/
  endpoint : MultiScale.Endpoint

/-- **The flow-side clauses**: the expansion in operator form, the coefficient bound, and the covariance
and Ward identity of the flowed proxies near `s = 0`, at every `SU(N)`. -/
structure GradientFlowProps [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (z : Chan → ℕ → ℝ)
    (μ : OffMix) : Prop where
  expand : ExpandStrong Wf cf z μ
  coef : CoefBound cf
  cov : FlowCov Wf cf
  ward : WardFromLattice.FlowWard Wf cf

/-- The substrate and the flow-side clauses give `MultiScaleStrongAt`. -/
theorem SubstrateAt.toStrong {W : ConfFlow 2} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow 2} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (S : SubstrateAt W z b Wf)
    (F : GradientFlowProps Wf cf z μ) : MultiScaleStrongAt W z μ b Wf cf :=
  ⟨S.b_pos, S.top, S.scale, F.expand, S.af, S.endpoint⟩

/-- **`WardT` from the flow-side clauses** (`WardFromLattice.wardT_of_flowWard`, `SepConv` from
`WardFromLattice.sepConv_of_multiScale`, `ExpandR` from `expandR_of_strong`). DERIVED: `2` is `SU(2)`. -/
theorem wardT_of_props {W : ConfFlow 2} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow 2} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (S : SubstrateAt W z b Wf)
    (F : GradientFlowProps Wf cf z μ) : WardT h2N (rhoD (fR 2) z) :=
  WardFromLattice.wardT_of_flowWard
    (WardFromLattice.sepConv_of_multiScale (S.toStrong F).toRenAt F.coef)
    (expandR_of_strong F.expand) F.ward

/-- **The substrate at `SU(N)`**: the fields of `SubstrateAt` other than `endpoint`. DERIVED: `0` the lower
end of the scale. -/
structure SubstrateCoreAt [NeZero N] (W : ConfFlow N) (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow N) :
    Prop where
  b_pos : 0 < b
  /-- The flow to the physical scale is `W`. -/
  top : Wf b = W
  /-- Every intermediate scale: the asymptotic-freedom moments of every monomial. -/
  scale : ScaleControlAll b Wf
  /-- Asymptotic freedom: a two-point kernel of the trace at `z` with the asymptotic-freedom coefficient. -/
  af : ∃ G : ℝ → ℝ, TwoPointKernel (NeZero.ne N) (rhoD (fR N) z) G ∧ AFCoefficient N G

/-- `SubstrateAt` contains `SubstrateCoreAt`. -/
theorem SubstrateAt.toCore {W : ConfFlow 2} {z : Chan → ℕ → ℝ} {b : ℝ} {Wf : ℝ → ConfFlow 2}
    (S : SubstrateAt W z b Wf) : SubstrateCoreAt W z b Wf :=
  ⟨S.b_pos, S.top, S.scale, S.af⟩

/-- **The flow-side inputs of `CompositesRenAll.clayStatementAt_SU_of_flowRen`** from the substrate core
and the flow-side clauses (`ExpandR` from `expandR_of_strong`). -/
theorem SubstrateCoreAt.toFlowRen [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (S : SubstrateCoreAt W z b Wf)
    (F : GradientFlowProps Wf cf z μ) : FlowRenAt W z μ b Wf cf :=
  ⟨S.b_pos, S.top, S.scale, expandR_of_strong F.expand⟩

/-- **`WardT` from the substrate core and the flow-side clauses**, at every `SU(N)`
(`WardFromLattice.wardT_of_flowWard`, `SepConv` from `WardFromLattice.sepConv_of_scale_expand`, `ExpandR`
from `expandR_of_strong`). -/
theorem wardT_of_core [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (S : SubstrateCoreAt W z b Wf)
    (F : GradientFlowProps Wf cf z μ) : WardT (NeZero.ne N) (rhoD (fR N) z) :=
  WardFromLattice.wardT_of_flowWard
    (WardFromLattice.sepConv_of_scale_expand S.b_pos S.scale (expandR_of_strong F.expand))
    (expandR_of_strong F.expand) F.ward

end MassGap.SU2Best

end

#print axioms MassGap.SU2Best.SubstrateAt.toStrong
#print axioms MassGap.SU2Best.wardT_of_props
#print axioms MassGap.SU2Best.SubstrateAt.toCore
#print axioms MassGap.SU2Best.SubstrateCoreAt.toFlowRen
#print axioms MassGap.SU2Best.wardT_of_core
