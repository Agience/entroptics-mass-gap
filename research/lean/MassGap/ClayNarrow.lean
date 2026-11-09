import Mathlib
import MassGap.FlowCovN
import MassGap.ApproxJoint
import MassGap.RunSeedN

/-!
# MassGap.ClayNarrow — one per-`N` bundle for the `SU(N)` route

`FlowCovN.clayStatement_of_covC` and `ApproxJoint.clayStatement_of_beyond` each narrow one per-`N` input of the
`SU(N)` route to `MassGap.ClayStatementDy`: `CovC` in place of `FlowCov`, and the clause of `ApproxK` beyond the
margin in place of `ApproxK`. `RunSeedN.runSeed_of_endpointN` replaces the gap input `WDeltaRun.RunSeed N` with
the more specific `EndpointN N`: `EndpointN N → RunSeed N` is proved and the converse is not, so
`NarrowInputsN ⇒ FlowCovInputsN` and not the reverse. This module states the bundle with all three
replacements at once and reduces it to `FlowCovInputsN` (`flowCovInputsN_of_narrow`). It states no
`ClayStatement` capstone from the bundle: `EndpointN N` is refuted by
`EndpointAudit.not_endpointN_of_levels_unbounded` under the argued growth of the zero-flux level count.
Declarations are in the namespace `MassGap.ClayNarrow`.

## The per-`N` inputs of `NarrowInputsN N hN2`

Witnesses as in `FlowCovN.FlowCovInputsN`: `c, hc0, hc, s₀, r` (`0 ≤ s₀ < r`), `zri, zwe` (nowhere zero), `μ`,
`b`, `Wf`, `cf`; `W = sunFam hN2 c hc0 hc s₀`, `z = ZCanon.zFix N zri zwe`. "Reads neither" means the clause
mentions neither the flow `Wf` nor the coefficients `cf`.

Substrate and flow (they read `Wf` or `cf`):

* `SubstrateCoreAt W z b Wf`: `0 < b`; `top`, `Wf b = W`; `scale`, `ScaleControlAll b Wf` (the
  asymptotic-freedom moments of every monomial at every flow scale); `af`, a two-point kernel of the trace at
  `z` with the asymptotic-freedom coefficient (`af` alone reads neither).
* `ExpandStrong Wf cf z μ`: the joint reflection forms of renormalised composites and of their flowed proxies
  agree to `K (s/d)^ε` at every flow scale `s ≤ θ d`.
* `CoefBound cf`: the proxy coefficients have fixed finite support and the power-and-log bound in `s`.

Target clauses (clauses of `ClayStatement`, here restated; each reads neither):

* `CovC (CRen N z μ)`: the composite limits transform under `O(4)` with `repF` (field `cov` of `CompOS`).
* `WardT (rhoD (fR N) z)`: the Ward identity of the stress tensor.
* `CompNondeg (CRen N z μ)`: a combination of composites with a non-zero leading on-shell value has a
  non-zero separated two-point reading.

Generation (reads neither):

* `∀ P, BeyondR r P → ApproxKAt (kernC (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) P`: every
  separated composite monomial whose times lie beyond `r` is a limit, in the joint reflection form, of real
  combinations of the observer's margin monomials beyond `r`.

Non-triviality (reads neither):

* `∃ ℓ > 0, ThreePointAtScale ℓ`: a bare three-point reading of `ℓ`-separated continuous test functions
  bounded below by `κ · a_k^12` along `ultra`.

The gap (reads none of the witnesses):

* `RunSeedN.EndpointN N`: the strong-coupling end at `SU(N)`; on every power-of-two slice of the physical
  window, the zero-flux levels with the loop-shell pair bound, rate and count, the generation field `gen`
  (on the family `words` a theorem at every `N ≠ 0`, `ProcesiSeparation.excited_mem_closure_words_all`), and
  the charged flux levels with a gap `m > 0` and a count. It gives `WDeltaRun.RunSeed N`.

## What is proved

* `compOS_of_covC`: `CompOS (CRen N z μ)` from `SubstrateCoreAt`, `ExpandStrong`, `CoefBound`, `CovC`,
  `CompNondeg` (the block of `FlowCovN.inputsAt_of_covC`).
* **`approxK_of_beyond_covC`**: `ApproxJoint.approxK_of_beyond_core` with `GradientFlowPropsN` (which carries
  `FlowCov`) replaced by `ExpandStrong`, `CoefBound`, `CovC`, `CompNondeg`.
* **`flowCovInputsN_of_narrow`**: `NarrowInputsN N hN2 → FlowCovN.FlowCovInputsN N hN2`
  (`approxK_of_beyond_covC`, `RunSeedN.runSeed_of_endpointN`).
* No `ClayStatement` capstone is stated from `NarrowInputsN`: it carries `EndpointN N`, refuted by
  `EndpointAudit.not_endpointN_of_levels_unbounded` under the argued growth of the zero-flux level count.
  `ClayRunSeed.clayStatement_of_narrowAtRS` takes `RunSeed N` in that slot.
* **`narrowInputsN_of_flowCov`**: `FlowCovInputsN N hN2 → EndpointN N → NarrowInputsN N hN2`
  (`ApproxK` restricted to the monomials beyond `r`). With `flowCovInputsN_of_narrow`: at the same witnesses,
  `NarrowInputsN` is `FlowCovInputsN` with `RunSeed N` replaced by `EndpointN N`.
* `narrowInputsN_of_beyond`: `ApproxJoint.FlowBeyondInputsN N hN2 → EndpointN N → NarrowInputsN N hN2`
  (`FlowChoice.covC_of_flowCov_choice`).
* `narrowInputsN_of_approx`: `ProxyGenLimN.FlowApproxInputsN N hN2 → EndpointN N → NarrowInputsN N hN2`.
* **`narrowInputsN_two_of_endpoint`**: at `N = 2`, `FlowCovInputsN 2 → MultiScale.Endpoint →
  NarrowInputsN 2` (`RunSeedN.endpointN_two_of_endpoint`).

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` the least colour count; `0` the lower end of the observer's scale and the plane;
`12` the bound of the block-step flow.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ClayNarrow

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
  MassGap.ProxyGenLimN MassGap.FlowCovN MassGap.ApproxJoint

variable {N : ℕ}

/-- **`CompOS` of the renormalised composites with `CovC` and `CompNondeg` as inputs**: module docstring.
DERIVED: no numeral. -/
theorem compOS_of_covC [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (S : SubstrateCoreAt W z b Wf)
    (hE : ExpandStrong Wf cf z μ) (hcb : CoefBound cf) (hV : CovC (NeZero.ne N) (CRen N z μ))
    (hP : CompNondeg (NeZero.ne N) (CRen N z μ)) : CompOS (NeZero.ne N) (CRen N z μ) :=
  ⟨convC_of_choice S.b_pos S.scale hE,
    os0C_of_scale_expand_coef S.b_pos S.scale (expandR_of_strong hE) hcb,
    os1C_of_scale_expand S.b_pos S.scale (expandR_of_strong hE), hV, hP⟩

/-- **`ApproxK` from the composites beyond the margin, with `CovC` in place of `FlowCov`**: module
docstring. DERIVED: `2` the least colour count; `0` the plane and the reference step. -/
theorem approxK_of_beyond_covC (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ}
    {μ : OffMix} {b r : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCoreAt W z b Wf) (hE : ExpandStrong Wf cf z μ) (hcb : CoefBound cf)
    (hV : CovC (NeZero.ne N) (CRen N z μ)) (hP : CompNondeg (NeZero.ne N) (CRen N z μ))
    (hphys : (Φ0 W).PhysRange r)
    (hB : ∀ P, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N z μ) 0)
      (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) P) :
    ApproxK (kernC (NeZero.ne N) (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) := by
  obtain ⟨t, C, ht, hS⟩ := uv_of_scale S.b_pos S.top S.scale
  have hU := ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) W ht hS
  have hCO := compOS_of_covC S hE hcb hV hP
  let D := capData hN2 W hU hphys (CRen N z μ)
    (unifLocal_buildRen (rhoD (fR N) z) (bareD (fR N) (bR N)) μ) (reflCovLat_CRen z μ) hCO
  refine approxK_iff_forall.2 fun P => ?_
  obtain ⟨n, hn⟩ := exists_beyond_iterate (NeZero.ne N) r P
  exact approxKAt_of_iterate D 0 n P (hB _ hn)

/-- **The per-`N` inputs**: `FlowCovN.FlowCovInputsN` with `ApproxK` replaced by its clause beyond the
margin (a narrowing) and `WDeltaRun.RunSeed N` by the more specific `RunSeedN.EndpointN N`. Module docstring.
DERIVED: `2` the least colour count; `0` the lower end of the observer's scale; `12` the bound of the
block-step flow. -/
def NarrowInputsN (N : ℕ) (hN2 : 2 ≤ N) : Prop :=
  haveI : NeZero N := ⟨by omega⟩
  ∃ (c : ℝ) (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N)) (s₀ r : ℝ) (_ : 0 ≤ s₀) (_ : s₀ < r)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)),
    SubstrateCoreAt (sunFam hN2 c hc0 hc s₀) (ZCanon.zFix N zri zwe) b Wf
      ∧ ExpandStrong Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ CoefBound cf
      ∧ CovC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ WardT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe))
      ∧ CompNondeg (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ (∀ P, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
          (mixKG hN2 (sunFam hN2 c hc0 hc s₀) (CRen N (ZCanon.zFix N zri zwe) μ) r)
          (gramF hN2 (sunFam hN2 c hc0 hc s₀) r) P)
      ∧ (∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (ne_zero_of_two_le hN2) ℓ)
      ∧ RunSeedN.EndpointN N

/-- **`NarrowInputsN` gives `FlowCovInputsN`** (`approxK_of_beyond_covC`, `RunSeedN.runSeed_of_endpointN`).
DERIVED: `2` the least colour count. -/
theorem flowCovInputsN_of_narrow (hN2 : 2 ≤ N) (h : NarrowInputsN N hN2) : FlowCovInputsN N hN2 := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP, hB, h3,
    hEnd⟩ := h
  exact ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP,
    approxK_of_beyond_covC hN2 S hE hC hV hP (sunFam_physRange hN2 hc0 hc hs0 hr) hB, h3,
    RunSeedN.runSeed_of_endpointN hEnd⟩

/-- **`FlowCovInputsN` and `EndpointN N` give `NarrowInputsN`** (`ApproxK` restricted beyond the margin,
`ApproxJoint.approxK_iff_forall`). DERIVED: `2` the least colour count. -/
theorem narrowInputsN_of_flowCov (hN2 : 2 ≤ N) (h : FlowCovInputsN N hN2)
    (hEnd : haveI : NeZero N := ⟨by omega⟩; RunSeedN.EndpointN N) : NarrowInputsN N hN2 := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP, hA, h3,
    -⟩ := h
  exact ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP,
    fun P _ => approxK_iff_forall.1 hA P, h3, hEnd⟩

/-- **`FlowBeyondInputsN` and `EndpointN N` give `NarrowInputsN`** (`FlowChoice.covC_of_flowCov_choice`).
DERIVED: `2` the least colour count. -/
theorem narrowInputsN_of_beyond (hN2 : 2 ≤ N) (h : FlowBeyondInputsN N hN2)
    (hEnd : haveI : NeZero N := ⟨by omega⟩; RunSeedN.EndpointN N) : NarrowInputsN N hN2 := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP, hB, h3,
    -⟩ := h
  exact ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC,
    covC_of_flowCov_choice S.b_pos S.scale hE hV, hW, hP, hB, h3, hEnd⟩

/-- **`FlowApproxInputsN` and `EndpointN N` give `NarrowInputsN`** (`FlowCovN.flowCovInputsN_of_approx`).
DERIVED: `2` the least colour count. -/
theorem narrowInputsN_of_approx (hN2 : 2 ≤ N) (h : FlowApproxInputsN N hN2)
    (hEnd : haveI : NeZero N := ⟨by omega⟩; RunSeedN.EndpointN N) : NarrowInputsN N hN2 :=
  narrowInputsN_of_flowCov hN2 (flowCovInputsN_of_approx hN2 h) hEnd

/-- **At `N = 2` the gap input is the `SU(2)` endpoint**: `FlowCovInputsN 2` and `MultiScale.Endpoint` give
`NarrowInputsN 2` (`RunSeedN.endpointN_two_of_endpoint`). DERIVED: `2` the colour count. -/
theorem narrowInputsN_two_of_endpoint (h : FlowCovInputsN 2 le_rfl) (hEnd : MultiScale.Endpoint) :
    NarrowInputsN 2 le_rfl :=
  narrowInputsN_of_flowCov le_rfl h (RunSeedN.endpointN_two_of_endpoint hEnd)

end MassGap.ClayNarrow

end

#print axioms MassGap.ClayNarrow.compOS_of_covC
#print axioms MassGap.ClayNarrow.approxK_of_beyond_covC
#print axioms MassGap.ClayNarrow.flowCovInputsN_of_narrow
#print axioms MassGap.ClayNarrow.narrowInputsN_of_flowCov
#print axioms MassGap.ClayNarrow.narrowInputsN_of_beyond
#print axioms MassGap.ClayNarrow.narrowInputsN_of_approx
#print axioms MassGap.ClayNarrow.narrowInputsN_two_of_endpoint
