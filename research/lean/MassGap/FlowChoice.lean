import Mathlib
import MassGap.SUNFromScale

/-!
# MassGap.FlowChoice — what the choice of the flow `Wf` and the coefficients `cf` can discharge

`SUNFromScale.clayStatement_of_flow` takes, at each `N ≥ 2`, some flow `Wf : ℝ → ConfFlow N` and some
coefficients `cf : Ix0 → ℝ → (MIx →₀ ℝ)` with `SubstrateCoreAt W z b Wf` (its field `top` is `Wf b = W`),
the flow bundle `NondegFromProxy.GradientFlowPropsN Wf cf z μ` (`ExpandStrong`, `CoefBound`, `FlowCov`,
`FlowWard`, `ProxyNondeg`) and `ProxyGenLim W b Wf cf r`. `Wf` and `cf` are the prover's choice. This
module reads each clause of the bundle against that choice, jointly with `ScaleControlAll b Wf` (the
field `scale` of the substrate, which also reads `Wf`). Declarations are in the namespace
`MassGap.FlowChoice`.

## 1. `CoefBound` on the exact leading-logarithm class

`cfScaled κ γ i s = ∑_j κ_{ij} s^{d_j} / s^{d_i} (1 + |log s|)^{γ_i} e_j`, for any finitely supported
`κ i : MIx →₀ ℝ` and any `γ : Ix0 → ℝ`: an exact leading-logarithm shape, with no `ḡ²(s)` corrections and
one log exponent per composite.
* **`coefBound_cfScaled`**: `CoefBound (cfScaled κ γ)` for every `κ`, `γ` (`S i = supp κ i`,
  `K i = ∑_j |κ_{ij}|`, `γc = γ`).
* `cfLead = cfScaled (i ↦ e_{inl i}) 0` and `cfLead_eq`: at every `s ≠ 0`, `cfLead i s = e_{inl i}`, the
  proxy of `i` is its own flowed monomial with coefficient `1`.
`CoefBound` reads only `cf`, so it holds on this exact class whatever `Wf` is. Choosing `cf` in the class
constrains `ExpandStrong`: the class has `s`-independent `κ` and one log exponent per composite, and it is
not shown to contain the coefficients of any flow that meets `ExpandStrong`. `CoefBound` therefore stays
an input of the capstones below.

## 2. `FlowWard` and `ProxyNondeg`: choice-invariant

Under `ScaleControlAll b Wf` (`0 < b`) and `ExpandStrong Wf cf z μ`:
* **`flowWard_iff_wardT_of_choice`**: `FlowWard Wf cf ↔ WardT (rhoD (fR N) z)`
  (`WardFromLattice.wardT_iff_flowWard`, `SepConv` from `WardFromLattice.sepConv_of_scale_expand`).
* **`proxyNondeg_iff_compNondeg_of_choice`**: `ProxyNondeg Wf cf ↔ CompNondeg (CRen N z μ)`
  (`NondegFromProxy.proxyNondeg_iff`, `ConvC` from `convC_of_choice`).
* **`flowWard_choice_iff`**, **`proxyNondeg_choice_iff`**: for two choices `(b, Wf, cf)`, `(b', Wf', cf')`
  at the same `z`, `μ`, each meeting `ScaleControlAll` and `ExpandStrong`, the clause holds at one iff
  it holds at the other.
`WardT (rhoD (fR N) z)` and `CompNondeg (CRen N z μ)` read neither `Wf` nor `cf`. So no choice that keeps
`scale` and `ExpandStrong` makes either clause easier: each is a statement about the composites at
`z`, `μ`.

## 3. `FlowCov`: discharged by zero scales, which the bundle excludes

* **`exists_onShellTopN`**: at every `N ≥ 2`, `c = e_{eI α}` with `α = (0, 1, 0, 1)` has `OnShellTopN N c`.
  The witness is the abelian potential `A_μ(x) = ½ v_{μν} x_ν H`, `v = asym 0 1`, `H = diag(1, −1, 0, …)`,
  at `g = 1` (`CompReduce.adm_abPot`, `CompReduce.onShell_abPot`), where `cval = 2 v_{01} v_{01} = 2`
  (`CompReduce.cval_abPot`). So the premise of `CompNondeg` and `ProxyNondeg` is met by some combination
  at every `N ≥ 2`; neither clause holds vacuously.

* `msProx_of_zeroScale`, `msLat_of_zeroScale`, `msLat_of_empty`: at a scale `s` with `cf i s = 0` for
  every `i`, every proxy is `0` and every flowed reading of a non-empty family is `0`; the reading of the
  empty family is `1`.
* **`flowCovAt_of_zeroScale`**: such a scale meets `FlowCovAt Wf cf s`, for every `Wf`.
* **`flowCov_of_frequently_zero`**: if `cf · s = 0` at scales accumulating at `0`, then `FlowCov Wf cf`.
  `flowCov_zero`: `FlowCov Wf 0`. `flowWard_zero`: `FlowWard Wf 0`.
* **`contC_eq_zero_of_frequently_zero`**: `ExpandR Wf cf z μ` with `cf · s = 0` at scales accumulating at
  `0` forces `contC F = 0` for every non-empty continuous separated family.
* **`not_compNondeg_of_frequently_zero`**, **`not_proxyNondeg_of_frequently_zero`**,
  **`not_gradientFlowPropsN_of_frequently_zero`**: hence such a choice contradicts `CompNondeg`, and
  (with `scale`) `ProxyNondeg` and the whole bundle, given a combination with `OnShellTopN N c`. The
  primed versions `not_compNondeg_of_frequently_zero'`, `not_proxyNondeg_of_frequently_zero'`,
  `not_gradientFlowPropsN_of_frequently_zero'` take it from `exists_onShellTopN` at `N ≥ 2`. The
  discharge of `FlowCov` by zero scales is not compatible with the bundle.
* `covC_of_flowCov_choice`, `not_flowCov_of_not_covC`: under `scale` and `ExpandStrong`, `FlowCov Wf cf`
  gives `CovC (CRen N z μ)` (`CovFromFlow.covC_of_scale_strong`); if `CovC` fails, no choice meets
  `FlowCov`. The converse is not proved: `CovC` gives the proxies' covariance only up to the rate.

## 4. `ExpandStrong` at the constant choice

* **`tendsto_latC_sub_of_expandR_const`**: at the constant flow `Wf s = W` with `s`-independent
  coefficients `cf i s = c i`, `ExpandR` gives, for every continuous separated family `F` and every
  `s₁`, `latC F − msLat_k(s₁) F → 0` as `k → ∞`: the composites' lattice readings at every separation are
  asymptotically those of one fixed combination of `W`-flowed fields. With `MultiScaleAll.scale_const`
  this choice reduces `scale` to the moment at `s = b`; it moves the content of `ExpandStrong` to this
  asymptotic identity at all separations.

## 5. The bundle with the choice-free clauses

* `convC_of_choice`: `scale` and `ExpandStrong` give `ConvC (CRen N z μ)`.
* **`gradientFlowPropsN_iff`**: under `scale`, `GradientFlowPropsN Wf cf z μ ↔ ExpandStrong ∧ CoefBound cf
  ∧ FlowCov ∧ WardT (rhoD (fR N) z) ∧ CompNondeg (CRen N z μ)`.
* **`gradientFlowPropsN_cfScaled_iff`**: at `cf = cfScaled κ γ`, `CoefBound` drops:
  `GradientFlowPropsN ↔ ExpandStrong ∧ FlowCov ∧ WardT ∧ CompNondeg`.
* `FlowChoiceInputsN N hN2`: the inputs of `SUNFromScale.FlowInputsN` with the flow bundle written as
  `ExpandStrong ∧ CoefBound ∧ FlowCov ∧ WardT ∧ CompNondeg` (`cf` free). **`flowInputsN_of_choice`**,
  **`flowInputsN_iff_choice`**: it is equivalent to `FlowInputsN`; **`clayStatement_of_choice`**:
  `FlowChoiceInputsN N hN2` at every `N ≥ 2` gives `ClayStatementDy`.

Per-`N` inputs of `clayStatement_of_choice`: `SubstrateCoreAt` (`b_pos`, `top`, `scale`, `af`),
`ExpandStrong Wf cf z μ`, `CoefBound cf`, `FlowCov Wf cf`, `WardT (rhoD (fR N) z)`,
`CompNondeg (CRen N z μ)`, `ProxyGenLim W b Wf cf r`, the three-point clause and `WDeltaRun.RunSeed N`.
`WardT` and `CompNondeg` read neither `Wf` nor `cf`.

## 6. Argued (no declaration)

* The identity flow at small `s` with coefficients matching the renormalised composites would make the
  rate clause of `ExpandStrong` an identity, but `ScaleAt` at `s ≫ a_k` asks
  `ν_k(exp((s/a_k)^{d_j} t (1 + |log s|)^{−γ_j} |O_j|)) ≤ C` of unflowed fields, which fails when `O_j`
  is not almost surely `0`; `scale` forces `Wf s` to smooth at the scale `s`. The content of
  `ExpandStrong` is in its conjunction with `scale` (`convC_of_choice` is one consequence).
* `ProxyGenLim` reads every `0 < s ≤ b` and margin monomials of `W` beyond `r > s₀`; a proxy supported
  at times below `r` is reached only through the time evolution of the observer's vectors, at every
  choice. No choice here discharges it.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the limit of the scale, the zero coefficients and the excluded value; `1` the
unit coefficient of `cfLead`, the reading of the empty family and the top of the scale range of
`CoefBound`; `2` the two points and the least colour count.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.FlowChoice

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

variable {N : ℕ}

/-! ## 1. `CoefBound` -/

/-- **The leading-logarithm coefficients**: `cfScaled κ γ i s j = κ_{ij} s^{d_j} / s^{d_i} (1 + |log s|)^{γ_i}`.
DERIVED: `0` the excluded coefficient. -/
def cfScaled (κ : Ix0 → MIx →₀ ℝ) (γ : Ix0 → ℝ) : Ix0 → ℝ → (MIx →₀ ℝ) := fun i s =>
  Finsupp.onFinset (κ i).support (fun j => κ i j * (s ^ mDim j / s ^ cdim i.1 * afLog (γ i) s))
    (fun _ hj => Finsupp.mem_support_iff.2 (left_ne_zero_of_mul hj))

/-- **`CoefBound` holds on the leading-logarithm class.** DERIVED: `0` the sign. -/
theorem coefBound_cfScaled (κ : Ix0 → MIx →₀ ℝ) (γ : Ix0 → ℝ) : CoefBound (cfScaled κ γ) := by
  refine ⟨fun i => (κ i).support, fun i => ∑ j ∈ (κ i).support, |κ i j|, γ,
    fun i s hs _ => ⟨Finsupp.support_onFinset_subset, fun j => ?_⟩⟩
  have hx : 0 ≤ s ^ mDim j / s ^ cdim i.1 * afLog (γ i) s := by
    have := afLog_pos (γ i) s
    positivity
  show |κ i j * (s ^ mDim j / s ^ cdim i.1 * afLog (γ i) s)|
    ≤ (∑ j ∈ (κ i).support, |κ i j|) * s ^ mDim j / s ^ cdim i.1 * afLog (γ i) s
  rw [abs_mul, abs_of_nonneg hx]
  have hk : |κ i j| ≤ ∑ j ∈ (κ i).support, |κ i j| := by
    rcases eq_or_ne (κ i j) 0 with h0 | h0
    · rw [h0, abs_zero]
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    · exact Finset.single_le_sum (f := fun j => |κ i j|) (fun _ _ => abs_nonneg _)
        (Finsupp.mem_support_iff.2 h0)
  calc |κ i j| * (s ^ mDim j / s ^ cdim i.1 * afLog (γ i) s)
      ≤ (∑ j ∈ (κ i).support, |κ i j|) * (s ^ mDim j / s ^ cdim i.1 * afLog (γ i) s) :=
        mul_le_mul_of_nonneg_right hk hx
    _ = (∑ j ∈ (κ i).support, |κ i j|) * s ^ mDim j / s ^ cdim i.1 * afLog (γ i) s := by ring

/-- **The leading coefficients**: each composite's proxy is its own flowed monomial.
DERIVED: `1` the unit coefficient; `0` the log exponent. -/
def cfLead : Ix0 → ℝ → (MIx →₀ ℝ) := cfScaled (fun i => Finsupp.single (Sum.inl i) 1) (fun _ => 0)

/-- **`cfLead i s = e_{inl i}` at every `s ≠ 0`.** DERIVED: `1` the unit coefficient; `0` the excluded
scale and the log exponent. -/
theorem cfLead_eq (i : Ix0) {s : ℝ} (hs : s ≠ 0) : cfLead i s = Finsupp.single (Sum.inl i) 1 := by
  classical
  ext j
  show (Finsupp.single (Sum.inl i) (1 : ℝ)) j * (s ^ mDim j / s ^ cdim i.1 * afLog 0 s) = _
  have hA : afLog 0 s = 1 := by simp [afLog]
  rw [hA, mul_one]
  by_cases hj : j = Sum.inl i
  · subst hj
    rw [Finsupp.single_eq_same, one_mul]
    exact div_self (pow_ne_zero _ hs)
  · rw [Finsupp.single_apply, if_neg (fun h => hj h.symm), zero_mul]

/-- **`CoefBound cfLead`.** DERIVED: no numeral. -/
theorem coefBound_cfLead : CoefBound cfLead := coefBound_cfScaled _ _

/-! ## 2. Choice-invariant clauses -/

/-- **`ConvC` from the scale clause and `ExpandStrong`**, at any choice. DERIVED: `0` the lower end of
the scale. -/
theorem convC_of_choice [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hb : 0 < b) (hsc : ScaleControlAll b Wf) (hE : ExpandStrong Wf cf z μ) :
    ConvC (NeZero.ne N) (CRen N z μ) :=
  (InputsTriage.convC_iff_boundC _ _).2 (boundC_ren_of_scale_expand hb hsc (expandR_of_strong hE))

/-- **`FlowWard` is `WardT`** at any choice meeting `scale` and `ExpandStrong`. DERIVED: `0` the lower
end of the scale. -/
theorem flowWard_iff_wardT_of_choice [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hb : 0 < b) (hsc : ScaleControlAll b Wf)
    (hE : ExpandStrong Wf cf z μ) :
    WardFromLattice.FlowWard Wf cf ↔ WardT (NeZero.ne N) (rhoD (fR N) z) :=
  (WardFromLattice.wardT_iff_flowWard
    (WardFromLattice.sepConv_of_scale_expand hb hsc (expandR_of_strong hE)) (expandR_of_strong hE)).symm

/-- **`ProxyNondeg` is `CompNondeg`** at any choice meeting `scale` and `ExpandStrong`. DERIVED: `0` the
lower end of the scale. -/
theorem proxyNondeg_iff_compNondeg_of_choice [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hb : 0 < b) (hsc : ScaleControlAll b Wf)
    (hE : ExpandStrong Wf cf z μ) :
    ProxyNondeg Wf cf ↔ CompNondeg (NeZero.ne N) (CRen N z μ) :=
  proxyNondeg_iff (expandR_of_strong hE) (convC_of_choice hb hsc hE)

/-- **`FlowWard` does not depend on the choice** among those meeting `scale` and `ExpandStrong` at the
same `z`, `μ`. DERIVED: `0` the lower ends of the scales. -/
theorem flowWard_choice_iff [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {b b' : ℝ}
    {Wf Wf' : ℝ → ConfFlow N} {cf cf' : Ix0 → ℝ → (MIx →₀ ℝ)}
    (hb : 0 < b) (hsc : ScaleControlAll b Wf) (hE : ExpandStrong Wf cf z μ)
    (hb' : 0 < b') (hsc' : ScaleControlAll b' Wf') (hE' : ExpandStrong Wf' cf' z μ) :
    WardFromLattice.FlowWard Wf cf ↔ WardFromLattice.FlowWard Wf' cf' :=
  (flowWard_iff_wardT_of_choice hb hsc hE).trans (flowWard_iff_wardT_of_choice hb' hsc' hE').symm

/-- **`ProxyNondeg` does not depend on the choice** among those meeting `scale` and `ExpandStrong` at
the same `z`, `μ`. DERIVED: `0` the lower ends of the scales. -/
theorem proxyNondeg_choice_iff [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {b b' : ℝ}
    {Wf Wf' : ℝ → ConfFlow N} {cf cf' : Ix0 → ℝ → (MIx →₀ ℝ)}
    (hb : 0 < b) (hsc : ScaleControlAll b Wf) (hE : ExpandStrong Wf cf z μ)
    (hb' : 0 < b') (hsc' : ScaleControlAll b' Wf') (hE' : ExpandStrong Wf' cf' z μ) :
    ProxyNondeg Wf cf ↔ ProxyNondeg Wf' cf' :=
  (proxyNondeg_iff_compNondeg_of_choice hb hsc hE).trans
    (proxyNondeg_iff_compNondeg_of_choice hb' hsc' hE').symm

/-- **`FlowCov` gives `CovC`** at any choice meeting `scale` and `ExpandStrong`. DERIVED: `0` the lower
end of the scale. -/
theorem covC_of_flowCov_choice [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hb : 0 < b) (hsc : ScaleControlAll b Wf)
    (hE : ExpandStrong Wf cf z μ) (hC : FlowCov Wf cf) : CovC (NeZero.ne N) (CRen N z μ) :=
  covC_of_scale_strong hb hsc hE hC

/-- **If `CovC` fails, no choice meeting `scale` and `ExpandStrong` meets `FlowCov`.** DERIVED: `0` the
lower end of the scale. -/
theorem not_flowCov_of_not_covC [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hb : 0 < b) (hsc : ScaleControlAll b Wf)
    (hE : ExpandStrong Wf cf z μ) (hn : ¬ CovC (NeZero.ne N) (CRen N z μ)) : ¬ FlowCov Wf cf :=
  fun hC => hn (covC_of_flowCov_choice hb hsc hE hC)

/-! ## 3. Zero scales -/

/-- At a zero scale every proxy is `0`. DERIVED: `0` the zero coefficients. -/
theorem msProx_of_zeroScale [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {s : ℝ}
    (h : ∀ i, cf i s = 0) (k : ℕ) (i : Ix0) : msProx Wf cf k s i = 0 := by
  unfold msProx
  rw [h i]
  simp

/-- At a zero scale every flowed reading of a non-empty family is `0`. DERIVED: `0` the zero
coefficients. -/
theorem msLat_of_zeroScale [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {s : ℝ}
    (h : ∀ i, cf i s = 0) {ι : Type} [Fintype ι] [Nonempty ι] (k : ℕ) (F : ι → Ix0 × TestFn) :
    msLat Wf cf k s F = 0 := by
  unfold msLat
  rw [Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary ι))
    (by rw [msProx_of_zeroScale h, smear_zero_field]), MassGap.DLRLimit.State.map_zero]

/-- The flowed reading of the empty family is `1`. DERIVED: `1` the unit observable. -/
theorem msLat_of_empty [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (s : ℝ)
    {ι : Type} [Fintype ι] [IsEmpty ι] (k : ℕ) (F : ι → Ix0 × TestFn) : msLat Wf cf k s F = 1 := by
  unfold msLat
  rw [Finset.univ_eq_empty, Finset.prod_empty, MassGap.DLRLimit.State.map_one]

/-- **A zero scale meets `FlowCovAt`**, for every flow. DERIVED: `0` the zero coefficients; `1` the
reading of the empty family. -/
theorem flowCovAt_of_zeroScale [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {s : ℝ}
    (h : ∀ i, cf i s = 0) : FlowCovAt Wf cf s := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  intro R _ ι _ _ F _
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hl : limUnder (ultra : Filter ℕ) (fun _ : ℕ => (1 : ℝ)) = 1 :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) (ultra : Filter ℕ) (𝓝 1)).limUnder_eq
    simp only [msLat_of_empty, hl, Finset.univ_eq_empty, Finset.prod_empty, one_mul,
      Finset.sum_const, Fintype.card_piFinset, nsmul_eq_mul, Nat.cast_one]
    exact tendsto_const_nhds
  · have hl : limUnder (ultra : Filter ℕ) (fun _ : ℕ => (0 : ℝ)) = 0 :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) (ultra : Filter ℕ) (𝓝 0)).limUnder_eq
    simp only [msLat_of_zeroScale h, hl, mul_zero, Finset.sum_const_zero]
    exact tendsto_const_nhds

/-- **Zero scales accumulating at `0` meet `FlowCov`.** DERIVED: `0` the limit of the scale and the zero
coefficients. -/
theorem flowCov_of_frequently_zero [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (h : ∃ᶠ s in 𝓝[>] (0 : ℝ), ∀ i, cf i s = 0) : FlowCov Wf cf :=
  h.mono fun _ hs => flowCovAt_of_zeroScale hs

/-- **`FlowCov Wf 0`.** DERIVED: `0` the zero coefficients. -/
theorem flowCov_zero [NeZero N] (Wf : ℝ → ConfFlow N) : FlowCov Wf 0 :=
  flowCov_of_frequently_zero (Filter.Frequently.of_forall fun _ _ => rfl)

/-- **`FlowWard Wf 0`**: every flowed reading of the Ward identity is `0`. DERIVED: `0` the zero
coefficients and `κ`. -/
theorem flowWard_zero [NeZero N] (Wf : ℝ → ConfFlow N) : WardFromLattice.FlowWard Wf 0 := by
  refine ⟨0, fun ν n F I h dh df d _ _ _ _ _ _ _ η hη =>
    Filter.Eventually.of_forall fun s => Filter.Eventually.of_forall fun k => ?_⟩
  have h0 : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (G : ι → TDatum),
      WardFromLattice.msT Wf 0 k s G = 0 := by
    intro ι _ _ _ G
    unfold WardFromLattice.msT
    exact Finset.sum_eq_zero fun α _ => by
      rw [msLat_of_zeroScale (cf := 0) (s := s) (fun _ => rfl), mul_zero]
  have hI : ∀ i ∈ I, WardFromLattice.msT Wf 0 k s (Function.update F i ((F i).1, df i)) = 0 :=
    fun i _ => by
      haveI : Nonempty (Fin n) := ⟨i⟩
      exact h0 _
  rw [Finset.sum_eq_zero fun m _ => h0 _, Finset.sum_eq_zero hI, add_zero, abs_zero]
  exact hη.le

/-- **`ExpandR` with zero scales accumulating at `0` forces every non-empty separated reading to `0`.**
DERIVED: `0` the limit of the scale, the zero coefficients and the limit value. -/
theorem contC_eq_zero_of_frequently_zero [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hE : ExpandR Wf cf z μ)
    (h0 : ∃ᶠ s in 𝓝[>] (0 : ℝ), ∀ i, cf i s = 0) {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (F : ι → CDatum (CRen N z μ)) {d : ℝ} (hd : 0 < d) (hc : ContD F) (hs : SepD d F) :
    contC (NeZero.ne N) (CRen N z μ) F = 0 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨θ, ε, Kr, κr, hθ, hε, hEx⟩ := hE
  have hT : Tendsto (fun k => latC (NeZero.ne N) (CRen N z μ) k F) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    set c : ℝ := Kr ^ Fintype.card ι * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2) with hcdef
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), c * (s / d) ^ ε < η ∧ s < θ * d ∧ 0 < s :=
      (eventually_rate_lt hε c hη).and
        (((gt_mem_nhds (mul_pos hθ hd)).filter_mono nhdsWithin_le_nhds).and
          (eventually_mem_nhdsWithin.mono fun s hs => hs))
    obtain ⟨s, hz, hs1, hs2, hs3⟩ := (h0.and_eventually hev).exists
    filter_upwards [hEx ι F d hd hc hs s hs3 hs2.le] with k hk
    rw [msLat_of_zeroScale hz, sub_zero] at hk
    rw [Real.dist_eq, sub_zero]
    have hr : Kr ^ Fintype.card ι * (s / d) ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)
        = c * (s / d) ^ ε := by
      rw [hcdef]
      ring
    linarith
  exact (hT.mono_left ultra_le).limUnder_eq

/-- **Zero scales accumulating at `0` contradict `CompNondeg`** under `ExpandR`, as soon as one
combination has `OnShellTopN N c`. DERIVED: `0` the limit of the scale and the zero coefficients. -/
theorem not_compNondeg_of_frequently_zero [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hE : ExpandR Wf cf z μ)
    (h0 : ∃ᶠ s in 𝓝[>] (0 : ℝ), ∀ i, cf i s = 0) {c : Ix0 →₀ ℝ} (hon : OnShellTopN N c) :
    ¬ CompNondeg (NeZero.ne N) (CRen N z μ) := by
  intro hN
  obtain ⟨f, h, hf, hh, ⟨d, hd, hfh⟩, hne⟩ := hN c hon
  apply hne
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  have hz := contC_eq_zero_of_frequently_zero hE h0 (pairF i j f h) hd (adm_pair hf hh hfh).1
    (adm_pair hf hh hfh).2
  rw [show contC (NeZero.ne N) (CRen N z μ) (![(i, f), (j, h)] : Fin 2 → CDatum (CRen N z μ)) = 0
    from hz, mul_zero]

/-- **Zero scales accumulating at `0` contradict `ProxyNondeg`** under `scale` and `ExpandStrong`, as
soon as one combination has `OnShellTopN N c`. DERIVED: `0` the limit and the lower end of the scale. -/
theorem not_proxyNondeg_of_frequently_zero [NeZero N] {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ} (hb : 0 < b)
    (hsc : ScaleControlAll b Wf) (hE : ExpandStrong Wf cf z μ)
    (h0 : ∃ᶠ s in 𝓝[>] (0 : ℝ), ∀ i, cf i s = 0) {c : Ix0 →₀ ℝ} (hon : OnShellTopN N c) :
    ¬ ProxyNondeg Wf cf := fun hP =>
  not_compNondeg_of_frequently_zero (expandR_of_strong hE) h0 hon
    ((proxyNondeg_iff_compNondeg_of_choice hb hsc hE).1 hP)

/-- **Zero scales accumulating at `0` contradict the flow bundle** under `scale`, as soon as one
combination has `OnShellTopN N c`. DERIVED: `0` the limit and the lower end of the scale. -/
theorem not_gradientFlowPropsN_of_frequently_zero [NeZero N] {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ} (hb : 0 < b)
    (hsc : ScaleControlAll b Wf) (h0 : ∃ᶠ s in 𝓝[>] (0 : ℝ), ∀ i, cf i s = 0) {c : Ix0 →₀ ℝ}
    (hon : OnShellTopN N c) : ¬ GradientFlowPropsN Wf cf z μ := fun F =>
  not_proxyNondeg_of_frequently_zero hb hsc F.props.expand h0 hon F.nondeg

/-- **An on-shell combination at every `N ≥ 2`**: `e_{eI (0,1,0,1)}` on the abelian potential with
`v = asym 0 1`, `H = diag(1, −1, 0, …)`, `g = 1`. DERIVED: `0`, `1` the axes of the plane; `1` the unit
coefficient and the coupling; `2` the least colour count. -/
theorem exists_onShellTopN (hN2 : 2 ≤ N) : ∃ c : Ix0 →₀ ℝ, OnShellTopN N c := by
  classical
  have hv : ∀ a b, CompReduce.asym 0 1 b a = -CompReduce.asym 0 1 a b := by
    intro a b
    simp only [CompReduce.asym]
    ring
  refine ⟨Finsupp.single (eI ![0, 1, 0, 1]) 1,
    CompReduce.abPot (CompReduce.Hc hN2) (CompReduce.asym 0 1), 1, CompReduce.adm_abPot hN2 _,
    CompReduce.onShell_abPot _ _ 1, ?_⟩
  rw [Finsupp.support_single _ one_ne_zero, Finset.sup_singleton,
    Finset.filter_true_of_mem (fun _ _ => by simp_all), Finset.sum_singleton, Finsupp.single_eq_same,
    one_pow, one_mul,
    show (eI ![0, 1, 0, 1]).1 = [([([], (![0, 1, 0, 1] : Idx4) 0, (![0, 1, 0, 1] : Idx4) 1),
      ([], (![0, 1, 0, 1] : Idx4) 2, (![0, 1, 0, 1] : Idx4) 3)], true)] from rfl,
    CompReduce.cval_abPot hN2 _ hv]
  show (1 : ℝ) * (2 * (CompReduce.asym 0 1 0 1 * CompReduce.asym 0 1 0 1)) ≠ 0
  norm_num [CompReduce.asym, CompReduce.dl]

/-- `not_compNondeg_of_frequently_zero` with the combination from `exists_onShellTopN`.
DERIVED: `0` the limit of the scale; `2` the least colour count. -/
theorem not_compNondeg_of_frequently_zero' (hN2 : 2 ≤ N) [NeZero N] {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hE : ExpandR Wf cf z μ)
    (h0 : ∃ᶠ s in 𝓝[>] (0 : ℝ), ∀ i, cf i s = 0) : ¬ CompNondeg (NeZero.ne N) (CRen N z μ) :=
  not_compNondeg_of_frequently_zero hE h0 (exists_onShellTopN hN2).choose_spec

/-- `not_proxyNondeg_of_frequently_zero` with the combination from `exists_onShellTopN`.
DERIVED: `0` the limit and the lower end of the scale; `2` the least colour count. -/
theorem not_proxyNondeg_of_frequently_zero' (hN2 : 2 ≤ N) [NeZero N] {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ} (hb : 0 < b)
    (hsc : ScaleControlAll b Wf) (hE : ExpandStrong Wf cf z μ)
    (h0 : ∃ᶠ s in 𝓝[>] (0 : ℝ), ∀ i, cf i s = 0) : ¬ ProxyNondeg Wf cf :=
  not_proxyNondeg_of_frequently_zero hb hsc hE h0 (exists_onShellTopN hN2).choose_spec

/-- `not_gradientFlowPropsN_of_frequently_zero` with the combination from `exists_onShellTopN`.
DERIVED: `0` the limit and the lower end of the scale; `2` the least colour count. -/
theorem not_gradientFlowPropsN_of_frequently_zero' (hN2 : 2 ≤ N) [NeZero N] {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ} (hb : 0 < b)
    (hsc : ScaleControlAll b Wf) (h0 : ∃ᶠ s in 𝓝[>] (0 : ℝ), ∀ i, cf i s = 0) :
    ¬ GradientFlowPropsN Wf cf z μ :=
  not_gradientFlowPropsN_of_frequently_zero hb hsc h0 (exists_onShellTopN hN2).choose_spec

/-! ## 4. The constant choice -/

/-- **`ExpandR` at the constant flow and `s`-independent coefficients**: the composites' lattice readings
are asymptotically the flowed readings at any one scale `s₁`. DERIVED: `0` the limit and the sign of
the scale. -/
theorem tendsto_latC_sub_of_expandR_const [NeZero N] {W : ConfFlow N} {c : Ix0 → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hE : ExpandR (fun _ => W) (fun i _ => c i) z μ) {ι : Type}
    [Fintype ι] [DecidableEq ι] (F : ι → CDatum (CRen N z μ)) {d : ℝ} (hd : 0 < d) (hc : ContD F)
    (hs : SepD d F) (s₁ : ℝ) :
    Tendsto (fun k => latC (NeZero.ne N) (CRen N z μ) k F
      - msLat (fun _ => W) (fun i _ => c i) k s₁ F) atTop (𝓝 0) := by
  obtain ⟨θ, ε, Kr, κr, hθ, hε, hEx⟩ := hE
  rw [Metric.tendsto_nhds]
  intro η hη
  set C : ℝ := Kr ^ Fintype.card ι * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2) with hCdef
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), C * (s / d) ^ ε < η ∧ s < θ * d ∧ 0 < s :=
    (eventually_rate_lt hε C hη).and
      (((gt_mem_nhds (mul_pos hθ hd)).filter_mono nhdsWithin_le_nhds).and
        (eventually_mem_nhdsWithin.mono fun s hs => hs))
  obtain ⟨s, hs1, hs2, hs3⟩ := hev.exists
  filter_upwards [hEx ι F d hd hc hs s hs3 hs2.le] with k hk
  have e : msLat (fun _ => W) (fun i _ => c i) k s F = msLat (fun _ => W) (fun i _ => c i) k s₁ F := rfl
  rw [e] at hk
  rw [Real.dist_eq, sub_zero]
  have hr : Kr ^ Fintype.card ι * (s / d) ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)
      = C * (s / d) ^ ε := by
    rw [hCdef]
    ring
  linarith

/-! ## 5. The bundle with the choice-free clauses -/

/-- **The flow bundle with `FlowWard` and `ProxyNondeg` replaced by `WardT` and `CompNondeg`**, under
`scale`. DERIVED: `0` the lower end of the scale. -/
theorem gradientFlowPropsN_iff [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ} (hb : 0 < b) (hsc : ScaleControlAll b Wf) :
    GradientFlowPropsN Wf cf z μ ↔ ExpandStrong Wf cf z μ ∧ CoefBound cf ∧ FlowCov Wf cf
      ∧ WardT (NeZero.ne N) (rhoD (fR N) z) ∧ CompNondeg (NeZero.ne N) (CRen N z μ) := by
  constructor
  · rintro ⟨⟨hE, hC, hV, hW⟩, hP⟩
    exact ⟨hE, hC, hV, (flowWard_iff_wardT_of_choice hb hsc hE).1 hW,
      (proxyNondeg_iff_compNondeg_of_choice hb hsc hE).1 hP⟩
  · rintro ⟨hE, hC, hV, hW, hP⟩
    exact ⟨⟨hE, hC, hV, (flowWard_iff_wardT_of_choice hb hsc hE).2 hW⟩,
      (proxyNondeg_iff_compNondeg_of_choice hb hsc hE).2 hP⟩

/-- **The flow bundle at the leading-logarithm coefficients**: `CoefBound` drops. DERIVED: `0` the lower
end of the scale. -/
theorem gradientFlowPropsN_cfScaled_iff [NeZero N] {Wf : ℝ → ConfFlow N} {κ : Ix0 → MIx →₀ ℝ}
    {γ : Ix0 → ℝ} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ} (hb : 0 < b) (hsc : ScaleControlAll b Wf) :
    GradientFlowPropsN Wf (cfScaled κ γ) z μ ↔ ExpandStrong Wf (cfScaled κ γ) z μ
      ∧ FlowCov Wf (cfScaled κ γ) ∧ WardT (NeZero.ne N) (rhoD (fR N) z)
      ∧ CompNondeg (NeZero.ne N) (CRen N z μ) := by
  rw [gradientFlowPropsN_iff hb hsc]
  exact ⟨fun ⟨hE, _, hV, hW, hP⟩ => ⟨hE, hV, hW, hP⟩,
    fun ⟨hE, hV, hW, hP⟩ => ⟨hE, coefBound_cfScaled κ γ, hV, hW, hP⟩⟩

/-- **The per-`N` inputs with the choice-free clauses**: `SUNFromScale.FlowInputsN` with the flow
bundle written as `ExpandStrong ∧ CoefBound ∧ FlowCov ∧ WardT ∧ CompNondeg`.
DERIVED: `2` the least colour count; `0` the lower end of the observer's scale. -/
def FlowChoiceInputsN (N : ℕ) (hN2 : 2 ≤ N) : Prop :=
  haveI : NeZero N := ⟨by omega⟩
  ∃ (c : ℝ) (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N)) (s₀ r : ℝ) (_ : 0 ≤ s₀) (_ : s₀ < r)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)),
    SubstrateCoreAt (sunFam hN2 c hc0 hc s₀) (ZCanon.zFix N zri zwe) b Wf
      ∧ ExpandStrong Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ CoefBound cf
      ∧ FlowCov Wf cf
      ∧ WardT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe))
      ∧ CompNondeg (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ ProxyGenLim (sunFam hN2 c hc0 hc s₀) b Wf cf r
      ∧ (∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (ne_zero_of_two_le hN2) ℓ)
      ∧ WDeltaRun.RunSeed N

/-- **`FlowChoiceInputsN` gives `SUNFromScale.FlowInputsN`.** DERIVED: `2` the least colour count. -/
theorem flowInputsN_of_choice (hN2 : 2 ≤ N) (h : FlowChoiceInputsN N hN2) :
    SUNFromScale.FlowInputsN N hN2 := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP, hL, h3,
    hfar⟩ := h
  exact ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S,
    (gradientFlowPropsN_iff S.b_pos S.scale).2 ⟨hE, hC, hV, hW, hP⟩, hL, h3, hfar⟩

/-- **`FlowChoiceInputsN` is `SUNFromScale.FlowInputsN`.** DERIVED: `2` the least colour count. -/
theorem flowInputsN_iff_choice (hN2 : 2 ≤ N) :
    FlowChoiceInputsN N hN2 ↔ SUNFromScale.FlowInputsN N hN2 := by
  haveI : NeZero N := ⟨by omega⟩
  refine ⟨flowInputsN_of_choice hN2, fun h => ?_⟩
  obtain ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, F, hL, h3, hfar⟩ := h
  obtain ⟨hE, hC, hV, hW, hP⟩ := (gradientFlowPropsN_iff S.b_pos S.scale).1 F
  exact ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP, hL, h3,
    hfar⟩

/-- **`ClayStatementDy` from `FlowChoiceInputsN` at every `N ≥ 2`** (`SUNFromScale.clayStatement_of_flow`).
DERIVED: `2` the least colour count. -/
theorem clayStatement_of_choice (h : ∀ (N : ℕ) (hN2 : 2 ≤ N), FlowChoiceInputsN N hN2) :
    MassGap.ClayStatementDy :=
  SUNFromScale.clayStatement_of_flow fun N hN2 => flowInputsN_of_choice hN2 (h N hN2)

end MassGap.FlowChoice

end

#print axioms MassGap.FlowChoice.coefBound_cfScaled
#print axioms MassGap.FlowChoice.cfLead_eq
#print axioms MassGap.FlowChoice.coefBound_cfLead
#print axioms MassGap.FlowChoice.convC_of_choice
#print axioms MassGap.FlowChoice.flowWard_iff_wardT_of_choice
#print axioms MassGap.FlowChoice.proxyNondeg_iff_compNondeg_of_choice
#print axioms MassGap.FlowChoice.flowWard_choice_iff
#print axioms MassGap.FlowChoice.proxyNondeg_choice_iff
#print axioms MassGap.FlowChoice.covC_of_flowCov_choice
#print axioms MassGap.FlowChoice.not_flowCov_of_not_covC
#print axioms MassGap.FlowChoice.msProx_of_zeroScale
#print axioms MassGap.FlowChoice.msLat_of_zeroScale
#print axioms MassGap.FlowChoice.msLat_of_empty
#print axioms MassGap.FlowChoice.flowCovAt_of_zeroScale
#print axioms MassGap.FlowChoice.flowCov_of_frequently_zero
#print axioms MassGap.FlowChoice.flowCov_zero
#print axioms MassGap.FlowChoice.flowWard_zero
#print axioms MassGap.FlowChoice.contC_eq_zero_of_frequently_zero
#print axioms MassGap.FlowChoice.not_compNondeg_of_frequently_zero
#print axioms MassGap.FlowChoice.not_proxyNondeg_of_frequently_zero
#print axioms MassGap.FlowChoice.not_gradientFlowPropsN_of_frequently_zero
#print axioms MassGap.FlowChoice.exists_onShellTopN
#print axioms MassGap.FlowChoice.not_compNondeg_of_frequently_zero'
#print axioms MassGap.FlowChoice.not_proxyNondeg_of_frequently_zero'
#print axioms MassGap.FlowChoice.not_gradientFlowPropsN_of_frequently_zero'
#print axioms MassGap.FlowChoice.tendsto_latC_sub_of_expandR_const
#print axioms MassGap.FlowChoice.gradientFlowPropsN_iff
#print axioms MassGap.FlowChoice.gradientFlowPropsN_cfScaled_iff
#print axioms MassGap.FlowChoice.flowInputsN_of_choice
#print axioms MassGap.FlowChoice.flowInputsN_iff_choice
#print axioms MassGap.FlowChoice.clayStatement_of_choice
