import Mathlib
import MassGap.ExpandMatch

/-!
# MassGap.FlowSym — the two symmetry clauses of the bundle, `FlowCovLim` and `FlowWard`

`ProxBound.CoreInputsAlongWPB` carries, at the flows `Wf` and the coefficients `cf`, the `CouplingGen.Along`
copies (at `cpl βs`) of two clauses on the flowed proxies at vanishing flow time. This module states them in
the base form, `FlowCovN.FlowCovLim` and `WardFromLattice.FlowWard`:

* `FlowCovN.FlowCovLim Wf cf`: for every `R ∈ O(4)` and admissible family `F`, the flowed reading of the
  rotated family is `∑_σ ∏ⱼ repF R iⱼ σⱼ · lim_ultra msLat_s((σⱼ, fⱼ))` up to an error vanishing as `s → 0⁺`;
* `WardFromLattice.FlowWard Wf cf`: for some `κ`, the flowed readings of the tensor sector (`msT`) satisfy the
  translation Ward identity of `ClayStatement.WardT` up to an error vanishing as `s → 0⁺`.

This module states what the tree proves about them. Declarations are in the namespace `MassGap.FlowSym`.

## 1. Both clauses are the continuum clauses read through the expansion (proved)

* **`flowSym_iff_covC_wardT`**: under `ExpandFam.ExpandLim Wf cf z μ`, `ConvC (CRen N z μ)` and
  `SepConv (rhoD (fR N) z)`, `FlowCovLim Wf cf ∧ FlowWard Wf cf ↔ CovC (CRen N z μ) ∧ WardT (rhoD (fR N) z)`
  (`ExpandFam.flowCovLim_iff_covCL`, `ExpandFam.wardT_iff_flowWardL`).
* **`flowSym_iff_of_expandMatch`**: the same with `ExpandMatch` (the bundle's expansion field) in place of
  `ExpandLim` (`ExpandFam.expandLim_of_expandRF`).

So on the bundle both clauses read the same limit through `msLat`: `FlowCovLim` is `CovC`, the `O(4)`
covariance of the continuum composites, and `FlowWard` is `WardT`, the translation Ward identity of the
continuum tensor sector. Neither reads `Wf` or `cf` beyond what `ExpandLim` transports.

## 2. Each clause alone is met by the zero proxy (proved)

* `msLat_of_isEmpty`: the flowed reading of the empty family is `1` (the state is normalised).
* `msLat_zero`: at `cf = 0` the flowed reading of every non-empty family is `0`.
* **`flowCovLim_zero`**: `FlowCovLim Wf 0` at every flow `Wf`.
* **`flowWard_zero`**: `FlowWard Wf 0` at every flow `Wf` (with `κ = 0`; any `κ` serves).

The zero coefficients are the degenerate case (every proxy constant, `0`). Read alone, neither clause carries
content there: both are met. On the bundle the zero coefficients are excluded by `ExpandMatch` with
`ProxyNondeg` under `ConvC` of `CRen N z μ` and an on-shell witness for `CompNondeg`
(`ExpandMatch.not_compNondeg_of_expandMatch_zero` against `ExpandFam.compNondeg_of_proxyL`); the content of
the two clauses is the content of `CovC` and `WardT` (§1). On the bundle these two clauses ask what `CovC`
and `WardT` ask (§1).

## 3. What does not follow (argued, stated plainly)

* (a) Hypercubic covariance does not give `FlowCovLim`. The tree proves invariance of the continuum
  Schwinger functions of `HypScalar` fields under signed permutations
  (`ContinuumHypercubic.rotation_hypercubic`), and the axis-covariance of particular observer flows
  (`ObserverRotation.obsConfFlow_iaxis`). It does not prove the hypercubic covariance of `latC` on the
  composites `CRen N z μ` with `repF`, nor of the flowed proxies at the bundle's `Wf`, `cf` (`Wf` is any
  `ConfFlow`; no axis-covariance field is carried). Where it does hold, the hypercubic group is finite and
  not dense in `O(4)`; the rotations that are not signed permutations are the restoration of rotation
  symmetry (`ContinuumHypercubic.RotationOpenAlong`). The Symanzik/Lüscher argument (flowed fields at fixed
  physical flow time have lattice artefacts `O(a²/s)` and an `O(4)`-covariant continuum limit) needs the
  continuum limit of the flowed theory at fixed `s` to be `O(4)` covariant, which is the same restoration
  at fixed `s` (`FlowCovN.RemCov` states it exactly). It does not follow from `ExpandMatch`, whose
  remainder bounds give no identity at any one `s` (`FlowCovN` §1). So `FlowCovLim` is not discharged.
* (b) The two clauses do not fold. `WardT` is the translation Ward identity: its contact term moves the
  test functions (`∂_ν fᵢ`), not the tensor indices. The rotation Ward identity needs the moment current
  `x_ν Θ_{μρ} − x_ρ Θ_{μν}` and a spin contact term acting by the representation on the indices; `WardT`
  carries neither, and passing from an infinitesimal identity to the finite rotations of `CovC` needs
  differentiability of the Schwinger functions in `R`, which the tree does not have. Conversely `CovC` is
  kinematic and fixes no normalisation of `Θ` (the existential `κ` and the contact term of `WardT` are
  dynamical). Neither implies the other on the tree's statements. Writing `FlowCovLim ∧ FlowWard` as one
  clause, or replacing it by `CovC ∧ WardT` through §1, is a relabelling: the count does not change.
* (c) Neither clause follows from `ExpandMatch`. `ExpandMatch` relates two readings (`latC` and `msLat`)
  and carries no symmetry; under it each clause is equivalent to its continuum target (§1), so it would
  follow from `ExpandMatch` exactly when `CovC` and `WardT` follow from the lattice theory, which is open.

## 4. The count

No input is removed and none is folded. The bundle `CoreInputsAlongWPB` keeps its nine clauses
(`ApertureBridge`, `ExpandMatch`, `ProxBound`, `ZoomSettling`, `FlowCovLim`, `FlowWard`, `ProxyNondeg`,
`ProxyGenLimGerm`, `ThreePointAtScale`); `FlowCovLim` maps to `CovC` and `FlowWard` to `WardT` through
`flowSym_iff_of_expandMatch`. No capstone is built here. The theorems here are at the base definitions; the
bundle's clauses are their `CouplingGen.Along` copies at `cpl βs`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the zero coefficients, the zero witness `κ = 0`, the zero reading and the limit
point; `1` the normalisation of the state.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.FlowSym

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
  MassGap.ProxyGenLimN MassGap.FlowCovN
open MassGap.WardFromLattice (msT FlowWard)
open MassGap.ScaleControlFull (zOne)

variable {N : ℕ}

/-! ## 1. Both clauses are the continuum clauses read through the expansion -/

/-- **`FlowCovLim ∧ FlowWard ↔ CovC ∧ WardT`** under `ExpandLim`, `ConvC` and `SepConv`: module docstring,
§1. DERIVED: no numeral. -/
theorem flowSym_iff_covC_wardT [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hL : ExpandFam.ExpandLim Wf cf z μ)
    (hCv : ConvC (NeZero.ne N) (CRen N z μ)) (hS : SepConv (NeZero.ne N) (rhoD (fR N) z)) :
    (FlowCovLim Wf cf ∧ FlowWard Wf cf)
      ↔ (CovC (NeZero.ne N) (CRen N z μ) ∧ WardT (NeZero.ne N) (rhoD (fR N) z)) :=
  and_congr (ExpandFam.flowCovLim_iff_covCL hL hCv) (ExpandFam.wardT_iff_flowWardL hS hL).symm

/-- **The same from the bundle's expansion field `ExpandMatch`**: module docstring, §1. DERIVED: no
numeral. -/
theorem flowSym_iff_of_expandMatch [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hE : ExpandMatch.ExpandMatch Wf cf z μ)
    (hCv : ConvC (NeZero.ne N) (CRen N z μ)) (hS : SepConv (NeZero.ne N) (rhoD (fR N) z)) :
    (FlowCovLim Wf cf ∧ FlowWard Wf cf)
      ↔ (CovC (NeZero.ne N) (CRen N z μ) ∧ WardT (NeZero.ne N) (rhoD (fR N) z)) :=
  flowSym_iff_covC_wardT (ExpandFam.expandLim_of_expandRF hE.1) hCv hS

/-! ## 2. The zero proxy -/

/-- **The flowed reading of the empty family is `1`**: module docstring, §2. DERIVED: `1` the
normalisation of the state. -/
theorem msLat_of_isEmpty [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ) (s : ℝ)
    {ι : Type} [Fintype ι] [IsEmpty ι] (F : ι → CDatum (CbR N zOne)) : msLat Wf cf k s F = 1 := by
  unfold msLat
  rw [Finset.univ_eq_empty, Finset.prod_empty]
  exact MassGap.DLRLimit.State.map_one _

/-- **At `cf = 0` the flowed reading of a non-empty family is `0`**: module docstring, §2. DERIVED: `0` the
zero coefficients. -/
theorem msLat_zero [NeZero N] (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) {ι : Type} [Fintype ι] [Nonempty ι]
    (F : ι → CDatum (CbR N zOne)) : msLat Wf 0 k s F = 0 := by
  unfold msLat
  rw [Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary ι))
    (by rw [msProx_zero, smear_zero_field]), MassGap.DLRLimit.State.map_zero]

/-- **`FlowCovLim` holds at the zero coefficients**, at every flow: module docstring, §2. DERIVED: `0` the
zero coefficients; `1` the empty reading. -/
theorem flowCovLim_zero [NeZero N] (Wf : ℝ → ConfFlow N) : FlowCovLim Wf 0 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  intro R _ ι _ _ F _ η hη
  refine Eventually.of_forall fun s => Eventually.of_forall fun k => ?_
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hc : ∀ G : ι → CDatum (CbR N zOne), limUnder (ultra : Filter ℕ) (fun k => msLat Wf 0 k s G) = 1 :=
      fun G => by
        simp_rw [msLat_of_isEmpty]
        exact tendsto_const_nhds.limUnder_eq
    simp_rw [hc, msLat_of_isEmpty, mul_one, Finset.univ_eq_empty, Finset.prod_empty,
      Finset.sum_const, Fintype.card_piFinset, nsmul_eq_mul, mul_one]
    simp [Finset.univ_eq_empty, hη.le]
  · have hc : ∀ G : ι → CDatum (CbR N zOne), limUnder (ultra : Filter ℕ) (fun k => msLat Wf 0 k s G) = 0 :=
      fun G => by
        simp_rw [msLat_zero]
        exact tendsto_const_nhds.limUnder_eq
    simp_rw [hc, msLat_zero, mul_zero, Finset.sum_const_zero, sub_zero, abs_zero]
    exact hη.le

/-- **At `cf = 0` the flowed reading of a non-empty tensor family is `0`**: module docstring, §2.
DERIVED: `0` the zero coefficients. -/
theorem msT_zero [NeZero N] (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (G : ι → TDatum) : msT Wf 0 k s G = 0 := by
  unfold msT
  exact Finset.sum_eq_zero fun α _ => by rw [msLat_zero, mul_zero]

/-- **`FlowWard` holds at the zero coefficients**, at every flow, with `κ = 0`: module docstring, §2.
DERIVED: `0` the zero coefficients and the witness. -/
theorem flowWard_zero [NeZero N] (Wf : ℝ → ConfFlow N) : FlowWard Wf 0 := by
  refine ⟨0, fun ν n F I h dh df d _ _ _ _ _ _ _ η hη => ?_⟩
  refine Eventually.of_forall fun s => Eventually.of_forall fun k => ?_
  have h1 : ∑ m, msT Wf 0 k s (Fin.cons (α := fun _ => TDatum) (stressC 0 m ν, dh m) F) = 0 :=
    Finset.sum_eq_zero fun m _ => msT_zero Wf k s _
  have h2 : ∑ i ∈ I, msT Wf 0 k s (Function.update F i ((F i).1, df i)) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      haveI : Nonempty (Fin n) := ⟨i⟩
      exact msT_zero Wf k s _
  rw [h1, h2, add_zero, abs_zero]
  exact hη.le

/-- **Both clauses at the zero coefficients**: module docstring, §2. DERIVED: `0` the zero coefficients. -/
theorem flowSym_zero [NeZero N] (Wf : ℝ → ConfFlow N) : FlowCovLim Wf 0 ∧ FlowWard Wf 0 :=
  ⟨flowCovLim_zero Wf, flowWard_zero Wf⟩

end MassGap.FlowSym

end

#print axioms MassGap.FlowSym.flowSym_iff_covC_wardT
#print axioms MassGap.FlowSym.flowSym_iff_of_expandMatch
#print axioms MassGap.FlowSym.msLat_of_isEmpty
#print axioms MassGap.FlowSym.msLat_zero
#print axioms MassGap.FlowSym.flowCovLim_zero
#print axioms MassGap.FlowSym.msT_zero
#print axioms MassGap.FlowSym.flowWard_zero
#print axioms MassGap.FlowSym.flowSym_zero
