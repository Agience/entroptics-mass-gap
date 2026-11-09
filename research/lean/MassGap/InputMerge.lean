import Mathlib
import MassGap.ClayRunSeed

/-!
# MassGap.InputMerge — the run-seed capstone with a shrunk bundle

`ClayRunSeed.clayStatement_of_narrowAtRS` takes, per `N ≥ 2`, the bundle `ClayRunSeed.NarrowInputsAtRS`.
This module sorts its inputs into observer-side (statements about the observer `W`, its flow `Wf`, the
flowed proxies `msProx Wf cf` and how they read the composites) and substrate-side (statements about the
Wilson states `stateK` alone), states `CovC` and `CompNondeg` in observer form (`af`, `WardT` and the
generation clause are kept as stated and read as observer double limits on admissible families, §2),
removes what the rest of the bundle already gives, and states the shrunk bundle
`NarrowInputsAtMin` with its capstone. Declarations are in the namespace `MassGap.InputMerge`.

## 1. What the bundle consumes (proved, by reading the consumers)

* `ExpandStrong Wf cf z μ` is read only through `StrongExpand.expandR_of_strong`: `ExpandR` suffices.
* `ScalePMChan`'s channel clause is read by `ConvC` (`ClusterRoute.boundC_ren_of_chan`) and `OS1C`
  (`ClusterRoute.os1C_of_chan`), and each fixes the scale `s` and the moment order `p = #F` before it reads
  the clause. So the Gevrey index, the rate `tⱼ` and the uniformity in `s` and `p` are never read:
  **`FinMom b Wf`** (every channel, every `s ∈ (0, b]`, every `p`, the `2p`-th moment of the flowed
  monomial eventually bounded in the step) suffices. `chanPM_local` turns it into `ScaleChanPM` at index
  `0` on any finite channel set at one `(s, p)`; `convC_of_finMom`, `os1C_of_finMom` re-prove the two
  consumers. `finMom_of_chan`: `ScaleControlChan` gives `FinMom`.
* The plaquette exponential at `s = b` is read only by `uv` (`uv_of_plaq`).

## 2. Every composite limit is the observer's double limit (proved)

* `obsLimC Wf cf F = lim_{s → 0⁺} lim_ultra msLat Wf cf k s F`: the observer's flowed reading of a family,
  first in the step, then in the flow scale.
* **`tendsto_obsLim`**, **`contC_eq_obsLimC`**: under `ExpandR` and `ConvC`, on every admissible family,
  `contC (CRen N z μ) F = obsLimC Wf cf F`.
* **`contT_rhoD_eq_obs`**: the tensor-sector readings (`TwoPointKernel`, `WardT`, `NonGaussianT` read them)
  are `∑_α (∏ᵢ cᵢ(αᵢ)) · obsLimC Wf cf ((eI αᵢ, fᵢ))ᵢ` on admissible families (`CompReduce.contT_expand`).

So under `ExpandR` and `ConvC` no clause on the continuum composites reads anything but the observer's
flowed readings. For `CovC` and `CompNondeg` the tree already has the observer forms with equivalences:
`FlowCovN.flowCovLim_iff_covC` (`FlowCovLim Wf cf ↔ CovC`) and `NondegFromProxy.proxyNondeg_iff`
(`ProxyNondeg Wf cf ↔ CompNondeg`). These are restatements: each moves its content, none removes it.

## 3. The verdict table (reductions proved above; sides and non-implications argued, no declaration)

| input of `NarrowInputsAtRS` | side | verdict in `NarrowInputsAtMin` |
|---|---|---|
| `PhysRange r` of `Φ0 W` | observer | kept |
| `ScalePMChan.chan` (Gevrey moments, every channel) | observer | narrowed to `FinMom` (§1); the growth index is never read; `ClusterPM` carries the `n`-point growth for `OS0C` |
| `ScalePMChan.top` (plaquette exponential at `s = b`) | observer | kept; not implied by `FinMom` or `chan`: `chan` bounds centred moments and so says nothing of the mean `a_k⁻⁴ ν_k(O)`, which `top` bounds; the per-channel index is unbounded, an exponential moment needs index at most `1` |
| `af` (two-point kernel of the trace, `AFCoefficient`) | substrate read through `contT` | kept; equal to an observer double-limit statement (`contT_rhoD_eq_obs`); not implied by `ThreePointAtScale` (order three) nor by any upper bound |
| `ExpandStrong` | observer | narrowed to `ExpandR` (§1) |
| `ClusterPM` (cumulants of separated flowed proxies) | observer reading, substrate content (clustering) | kept; only `OS0C` reads it. It does not give `FinMom` (single-point moments are not separated families) nor `OS1C` (a bound, no translation identity) |
| `CovC` | substrate | replaced by `FlowCovLim Wf cf` (observer, equivalent under `ExpandR` + `ConvC`) |
| `WardT` | substrate read through `contT` | kept; on admissible stress families it reads the observer's double limit (`contT_rhoD_eq_obs`); the stress family need not be admissible as `WardT` quantifies, so no bundle form is stated here |
| `CompNondeg` | substrate | replaced by `ProxyNondeg Wf cf` (observer, equivalent under `ExpandR` + `ConvC`); `af` covers the trace combination only, so it cannot replace the clause for all combinations |
| generation clause | observer | kept (equivalent under the CL bundle to `GenerationCyclic.ObserverCyclicCL`, `GenerationCyclic.cyclic_of_generation`) |
| `∃ ℓ, ThreePointAtScale` | substrate (bare plaquette field, lattice readings) | kept; under `SepConv` (not in the bundle) it would be `NonGaussianT` at `rhoD`, reading `contT`; as stated it reads lattice readings at scale `ℓ` (argued); `af` does not give it (`ThreePointAnomaly` §4 lists the four missing links) |
| `RunSeed N` | substrate (Wilson partition functions) | kept; reads `RectWilson.ZR` only, no composite and no flow, so §2 does not reach it |

## 4. What cannot move, and why (argued; no declaration)

`RunSeed N` is the one input that reads neither the composites nor the observer: it is a bound on the
doubling defect of the Wilson partition function at a physical side. Every observer input above is a
statement at fixed physical separation `d` and flow scale `s ≤ θ d`, or the limit `s → 0⁺`; none asserts
decay in distance, and `ClusterPM` asserts no decay rate (`ClusterRoute.ClusterGap` at `m = 0`). A gap is
a statement at growing distance, so some input must read it. In observer terms it would be the
self-consistency of the observer's reading under zoom: the reading of `W` at its scale reproducing itself
when the box doubles. Stated on the observer's flowed plaquette class, that is a defect bound for the
flowed partition functions, which no module here relates to `defectW`; the comparison flowed → unflowed at
growing side is the missing statement.

`ClusterPM` is observer-read and substrate in content: it is the uniformity in the number of separated
insertions that a decay rate gives (`ClusterRoute` §4).

## 5. The capstone

* `SubstrateCoreMin W z b Wf`: `b > 0`, `Wf b = W`, the plaquette exponential at `s = b`, `FinMom b Wf`,
  `af`. `coreMin_of_coreCL`.
* `compOS_of_min`: `CompOS (CRen N z μ)` from `SubstrateCoreMin`, `ExpandR`, `ClusterPM`, `FlowCovLim`,
  `ProxyNondeg`.
* `NarrowInputsAtMin N hN2 W r`: `PhysRange r`; `SubstrateCoreMin`, `ExpandR`, `ClusterPM`, `FlowCovLim`,
  `WardT`, `ProxyNondeg`, the generation clause, `∃ ℓ, ThreePointAtScale`, `RunSeed N`.
* **`clayStatement_of_narrowAtMin`**: `∃ W r, NarrowInputsAtMin N hN2 W r` at every `N ≥ 2` gives
  `MassGap.ClayStatementDy`.
* **`narrowInputsAtMin_of_RS`**: `NarrowInputsAtRS` gives `NarrowInputsAtMin` at the same `W`, `r`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the Gevrey index and the lower end of the scale; `1` the rate, the floor of `K`
and the spacing bound; `2` the even powers, the halves and the least colour count.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.InputMerge

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
  MassGap.ProxyGenLimN MassGap.FlowCovN MassGap.ApproxJoint MassGap.ClayNarrow
  MassGap.ObserverMultigrid MassGap.ClayNarrowMG MassGap.ScalePC MassGap.ScalePM MassGap.ClusterRoute
  MassGap.ClayRunSeed
open MassGap.ScaleControlFull (zOne)

variable {N : ℕ}

/-! ## 1. Finite moments in place of the Gevrey clause -/

/-- **Finite flowed moments**: every channel, every scale in `(0, b]`, every order `p`, the `2p`-th moment of
the flowed monomial (physical units, centred) is eventually bounded in the step. DERIVED: `2` the even
power; `0` the lower end of the scale. -/
def FinMom [NeZero N] (b : ℝ) (Wf : ℝ → ConfFlow N) : Prop :=
  ∀ s : ℝ, 0 < s → s ≤ b → ∀ (j : MIx) (p : ℕ), ∃ M : ℝ,
    ∀ᶠ k in atTop, stateK (NeZero.ne N) k (msFlow Wf k s j ^ (2 * p)) ≤ M

/-- **`ScaleControlChan` gives `FinMom`.** DERIVED: `2` the even power. -/
theorem finMom_of_chan [NeZero N] {b : ℝ} {Wf : ℝ → ConfFlow N} (h : ScaleControlChan b Wf) :
    FinMom b Wf := by
  obtain ⟨γ, γP, H⟩ := h
  intro s hs hsb j p
  obtain ⟨r, t, K, -, hj⟩ := H.chan j
  exact ⟨((2 * p).factorial : ℝ) ^ r / msMu t γ γP j s ^ (2 * p) * K,
    (hj s hs hsb p).mono fun k hk => hk⟩

/-- **`FinMom` at one scale and one order as `ScaleChanPM`** at index `0`, rate `1`, one `K ≥ 1` on a
finite channel set. DERIVED: `0` the index; `1` the rate and the floor of `K`; `2` the even power. -/
theorem chanPM_local [NeZero N] {b : ℝ} {Wf : ℝ → ConfFlow N} (hm : FinMom b Wf) (γ : Ix0 → ℝ) (γP : ℝ)
    (T : Finset MIx) {s : ℝ} (hs : 0 < s) (hsb : s ≤ b) (p : ℕ) :
    ∃ (r : ℕ) (t K : ℝ), 0 < t ∧ 1 ≤ K ∧
      ∀ᶠ k in atTop, ∀ j ∈ T, ScaleChanPM Wf r t K γ γP k s j p := by
  classical
  choose M hM using fun j => hm s hs hsb j p
  have hw : ∀ j, 0 ≤ |M j| * msMu 1 γ γP j s ^ (2 * p) := fun j =>
    mul_nonneg (abs_nonneg _) (pow_nonneg (msMu_pos one_pos γ γP hs j).le _)
  have hS0 : 0 ≤ ∑ j ∈ T, |M j| * msMu 1 γ γP j s ^ (2 * p) := Finset.sum_nonneg fun j _ => hw j
  refine ⟨0, 1, 1 + ∑ j ∈ T, |M j| * msMu 1 γ γP j s ^ (2 * p), one_pos, by linarith, ?_⟩
  filter_upwards [(Filter.eventually_all_finset T).2 fun j _ => hM j] with k hk j hj
  unfold ScaleChanPM
  have hμ : 0 < msMu 1 γ γP j s ^ (2 * p) := pow_pos (msMu_pos one_pos γ γP hs j) _
  have hle : |M j| * msMu 1 γ γP j s ^ (2 * p)
      ≤ 1 + ∑ j ∈ T, |M j| * msMu 1 γ γP j s ^ (2 * p) := by
    have := Finset.single_le_sum (f := fun j => |M j| * msMu 1 γ γP j s ^ (2 * p))
      (fun j _ => hw j) hj
    linarith
  rw [pow_zero, div_mul_eq_mul_div, one_mul, le_div_iff₀ hμ]
  calc stateK (NeZero.ne N) k (msFlow Wf k s j ^ (2 * p)) * msMu 1 γ γP j s ^ (2 * p)
      ≤ |M j| * msMu 1 γ γP j s ^ (2 * p) :=
        mul_le_mul_of_nonneg_right ((hk j hj).trans (le_abs_self _)) hμ.le
    _ ≤ _ := hle

/-- **`BoundC (CRen N z μ)` from `FinMom` and `ExpandR`** (`ClusterRoute.boundC_ren_of_chan`'s proof at
`chanPM_local`). DERIVED: `1` the spacing bound; `0` the log exponents. -/
theorem boundC_of_finMom [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hm : FinMom b Wf)
    (hex : ExpandR Wf c z μ) : InputsTriage.BoundC (NeZero.ne N) (CRen N z μ) := by
  classical
  obtain ⟨θ, ε, Kr, κr, hθ, -, hE⟩ := hex
  intro ι _ _ F hF
  obtain ⟨hcont, d, hd, hsep⟩ := hF
  have hs : 0 < min (θ * d) b := lt_min (mul_pos hθ hd) hb
  obtain ⟨r, t, K, ht, hK1, hev⟩ := chanPM_local hm (0 : Ix0 → ℝ) 0
    (Finset.univ.biUnion fun i => (c (F i).1 (min (θ * d) b)).support) hs (min_le_right _ _)
    (Fintype.card ι)
  refine ⟨(1 + Fintype.card ι * (((2 * Fintype.card ι).factorial : ℝ) ^ r * K))
      * ∏ i, (msTsize (F i).2 * msPsize t (0 : Ix0 → ℝ) 0 c (min (θ * d) b) (F i).1)
    + Kr ^ Fintype.card ι * (min (θ * d) b / d) ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2), ?_⟩
  refine Filter.Eventually.filter_mono ultra_le ?_
  filter_upwards [hev, hE ι F d hd hcont hsep (min (θ * d) b) hs (min_le_left _ _),
    (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)] with k hk hrem hk1
  have hP := abs_msLat_le_on_pm Wf c ht hs hk1.le F hK1 (fun i j hj =>
    hk j (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hj⟩))
  have htri := abs_sub_abs_le_abs_sub (latC (NeZero.ne N) (CRen N z μ) k F)
    (msLat Wf c k (min (θ * d) b) F)
  linarith

/-- **`ConvC (CRen N z μ)` from `FinMom` and `ExpandR`.** DERIVED: no numeral. -/
theorem convC_of_finMom [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hm : FinMom b Wf)
    (hex : ExpandR Wf c z μ) : ConvC (NeZero.ne N) (CRen N z μ) :=
  (InputsTriage.convC_iff_boundC _ _).2 (boundC_of_finMom hb hm hex)

/-- **`OS1C (CRen N z μ)` from `FinMom` and `ExpandR`** (`ClusterRoute.os1C_of_chan`'s proof at
`chanPM_local`). DERIVED: `2` the halves; `0` the limit and the log exponents. -/
theorem os1C_of_finMom [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hm : FinMom b Wf)
    (hex : ExpandR Wf c z μ) : OS1C (NeZero.ne N) (CRen N z μ) := by
  classical
  have hconv : ConvC (NeZero.ne N) (CRen N z μ) := convC_of_finMom hb hm hex
  obtain ⟨θ, ε, Kr, κr, hθ, hε, hE⟩ := hex
  intro ι _ _ F hF v
  obtain ⟨hcont, d, hd, hsep⟩ := hF
  have hFv_c : ContD (fun i => translateD v (F i)) :=
    fun i => (hcont i).comp (continuous_id.sub continuous_const)
  have hFv_s : SepD d (fun i => translateD v (F i)) :=
    fun i j hij => ContinuumSep.sepBy_translate (hsep i j hij) v
  have hΔ : Tendsto (fun k => latC (NeZero.ne N) (CRen N z μ) k (fun i => translateD v (F i))
      - latC (NeZero.ne N) (CRen N z μ) k F) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    set A1 : ℝ := Kr ^ Fintype.card ι * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2) with hA1
    set A2 : ℝ := Kr ^ Fintype.card ι
      * ∏ i, ((d ^ κr (translateD v (F i)).1)⁻¹ * l1 (translateD v (F i)).2) with hA2
    have hφ : Tendsto (fun s : ℝ => (|A1| + |A2|) * (s / d) ^ ε) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun s : ℝ => s / d) (𝓝 0) (𝓝 0) := by
        simpa using (tendsto_id (x := (𝓝 (0 : ℝ)))).div_const d
      have h2 := (h1.rpow_const (Or.inr hε.le)).const_mul (|A1| + |A2|)
      rw [Real.zero_rpow hε.ne', mul_zero] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    obtain ⟨s, hsQ, hsI⟩ := ((hφ.eventually (gt_mem_nhds (half_pos hη))).and
      (Ioo_mem_nhdsGT (lt_min (mul_pos hθ hd) hb) :
        ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Set.Ioo 0 (min (θ * d) b))).exists
    have hs : 0 < s := hsI.1
    have hsθ : s ≤ θ * d := hsI.2.le.trans (min_le_left _ _)
    have hsb : s ≤ b := hsI.2.le.trans (min_le_right _ _)
    have hx : 0 ≤ (s / d) ^ ε := Real.rpow_nonneg (div_nonneg hs.le hd.le) _
    obtain ⟨r, t, K, ht, hK1, hevU⟩ := chanPM_local hm (0 : Ix0 → ℝ) 0
      (Finset.univ.biUnion fun i => (c (F i).1 s).support) hs hsb (Fintype.card ι)
    have hS : ∀ᶠ k in atTop, ∀ i, ∀ j ∈ (c (F i).1 s).support,
        ScaleChanPM Wf r t K (0 : Ix0 → ℝ) 0 k s j (Fintype.card ι) := by
      filter_upwards [hevU] with k hk i j hj
      exact hk j (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hj⟩)
    have hmid : Tendsto (fun k => msLat Wf c k s (fun i => translateD v (F i)) - msLat Wf c k s F)
        atTop (𝓝 0) := msLat_translate_sub_tendsto_pm Wf c ht hs hK1 F hS hcont v
    filter_upwards [hE ι F d hd hcont hsep s hs hsθ, hE ι _ d hd hFv_c hFv_s s hs hsθ,
      (Metric.tendsto_nhds.mp hmid) (η / 2) (half_pos hη)] with k h1 h2 h3
    have h1' : |latC (NeZero.ne N) (CRen N z μ) k F - msLat Wf c k s F| ≤ |A1| * (s / d) ^ ε := by
      refine h1.trans ?_
      calc Kr ^ Fintype.card ι * (s / d) ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)
          = A1 * (s / d) ^ ε := by rw [hA1]; ring
        _ ≤ |A1| * (s / d) ^ ε := mul_le_mul_of_nonneg_right (le_abs_self _) hx
    have h2' : |latC (NeZero.ne N) (CRen N z μ) k (fun i => translateD v (F i))
        - msLat Wf c k s (fun i => translateD v (F i))| ≤ |A2| * (s / d) ^ ε := by
      refine h2.trans ?_
      calc Kr ^ Fintype.card ι * (s / d) ^ ε
            * ∏ i, ((d ^ κr (translateD v (F i)).1)⁻¹ * l1 (translateD v (F i)).2)
          = A2 * (s / d) ^ ε := by rw [hA2]; ring
        _ ≤ |A2| * (s / d) ^ ε := mul_le_mul_of_nonneg_right (le_abs_self _) hx
    have h3' : |msLat Wf c k s (fun i => translateD v (F i)) - msLat Wf c k s F| < η / 2 := by
      rw [Real.dist_eq, sub_zero] at h3
      exact h3
    have hsQ' : (|A1| + |A2|) * (s / d) ^ ε < η / 2 := hsQ
    have hsQ'' : |A1| * (s / d) ^ ε + |A2| * (s / d) ^ ε < η / 2 := by rw [← add_mul]; exact hsQ'
    rw [Real.dist_eq, sub_zero]
    obtain ⟨a1l, a1r⟩ := abs_le.mp h1'
    obtain ⟨a2l, a2r⟩ := abs_le.mp h2'
    obtain ⟨a3l, a3r⟩ := abs_lt.mp h3'
    rw [abs_lt]
    constructor <;> linarith
  have h := (hconv ι F ⟨hcont, d, hd, hsep⟩).add (hΔ.mono_left ultra_le)
  rw [add_zero] at h
  refine h.congr fun k => ?_
  ring

/-- **`uv` from the plaquette exponential at `s = b`** (`ClusterRoute.uv_of_chan`'s proof).
DERIVED: `4` the dimension; `2 · 1 + 3` the site count. -/
theorem uv_of_plaq [NeZero N] {W : ConfFlow N} {b : ℝ} {Wf : ℝ → ConfFlow N} (hb : 0 < b)
    (htop : Wf b = W)
    (hpl : ∃ (γ : Ix0 → ℝ) (γP t C : ℝ), 0 < t ∧
      ∀ᶠ k in atTop, ∀ q, ScaleChan Wf t C γ γP k b (Sum.inr q)) :
    ∃ t C : ℝ, 0 < t ∧ FlowUV.SiteExp (NeZero.ne N) W (SymPlaqClass N) (t * (2 * 1 + 3) ^ 4) C := by
  obtain ⟨γ, γP, t, C, ht, hev⟩ := hpl
  have hpos : 0 < t * b ^ 4 / afLog γP b := div_pos (mul_pos ht (pow_pos hb 4)) (afLog_pos _ _)
  refine ⟨t * b ^ 4 / afLog γP b / (2 * 1 + 3) ^ 4, C, div_pos hpos (by norm_num), ?_⟩
  rw [div_mul_cancel₀ _ (by norm_num : ((2 : ℝ) * 1 + 3) ^ 4 ≠ 0)]
  unfold FlowUV.SiteExp
  filter_upwards [hev] with k hk
  rintro O ⟨q, rfl⟩
  have h1 := hk q
  unfold ScaleChan at h1
  rw [htop, mField_inr, mDim_inr, msMu_inr] at h1
  have e : msAbs (W.fieldMap k (sym (plaqField q))).1 = (W.fieldMap k (sym (plaqField q))).1 := by
    ext U
    have key : ∀ O ∈ SymPlaqClass N, ∀ U, 0 ≤ (W.fieldMap k O).1 U :=
      fun O hO U => symPlaq_nonneg (NeZero.ne N) O hO (W.V k U)
    rw [msAbs_apply]
    exact abs_of_nonneg (key _ ⟨q, rfl⟩ U)
  rw [e] at h1
  exact h1

/-! ## 2. The composite limits as the observer's double limit -/

/-- **The observer's double limit** of a family: `lim_{s → 0⁺} lim_ultra msLat Wf cf k s F`.
DERIVED: `0` the limit of the scale. -/
def obsLimC [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) {ι : Type} [Fintype ι]
    (F : ι → Ix0 × TestFn) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun s => limUnder (ultra : Filter ℕ) (fun k => msLat Wf cf k s F))

/-- **The flowed limits tend to the composite limit as `s → 0⁺`**, under `ExpandR` and `ConvC`, on every
admissible family. DERIVED: `0` the limit of the scale. -/
theorem tendsto_obsLim [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ}
    {μ : OffMix} (hE : ExpandR Wf cf z μ) (hC : ConvC (NeZero.ne N) (CRen N z μ)) {ι : Type}
    [Fintype ι] [DecidableEq ι] (F : ι → CDatum (CRen N z μ)) (hF : Adm F) :
    Tendsto (fun s => limUnder (ultra : Filter ℕ) (fun k => msLat Wf cf k s F)) (𝓝[>] (0 : ℝ))
      (𝓝 (contC (NeZero.ne N) (CRen N z μ) F)) := by
  obtain ⟨θ, ε, Kr, κr, hθ, hε, hEx⟩ := hE
  obtain ⟨hcont, d, hd, hsep⟩ := hF
  set A : ℝ := Kr ^ Fintype.card ι * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2) with hA
  have hφ : Tendsto (fun s : ℝ => |A| * (s / d) ^ ε) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => s / d) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_id (x := (𝓝 (0 : ℝ)))).div_const d
    have h2 := (h1.rpow_const (Or.inr hε.le)).const_mul |A|
    rw [Real.zero_rpow hε.ne', mul_zero] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  rw [Metric.tendsto_nhds]
  intro η hη
  filter_upwards [hφ.eventually (gt_mem_nhds hη),
    (Ioo_mem_nhdsGT (mul_pos hθ hd) : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Set.Ioo 0 (θ * d))] with s h1 h2
  have hx : 0 ≤ (s / d) ^ ε := Real.rpow_nonneg (div_nonneg h2.1.le hd.le) _
  have hb := FlowCovN.abs_sub_limUnder_le (hC ι F ⟨hcont, d, hd, hsep⟩)
    (((hEx ι F d hd hcont hsep s h2.1 h2.2.le).filter_mono ultra_le).mono fun k hk =>
      hk.trans (by
        calc Kr ^ Fintype.card ι * (s / d) ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)
            = A * (s / d) ^ ε := by rw [hA]; ring
          _ ≤ |A| * (s / d) ^ ε := mul_le_mul_of_nonneg_right (le_abs_self _) hx))
  rw [Real.dist_eq, abs_sub_comm]
  have h1' : |A| * (s / d) ^ ε < η := h1
  linarith

/-- **Every composite limit is the observer's double limit**, under `ExpandR` and `ConvC`, on every
admissible family. DERIVED: no numeral. -/
theorem contC_eq_obsLimC [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ}
    {μ : OffMix} (hE : ExpandR Wf cf z μ) (hC : ConvC (NeZero.ne N) (CRen N z μ)) {ι : Type}
    [Fintype ι] [DecidableEq ι] (F : ι → CDatum (CRen N z μ)) (hF : Adm F) :
    contC (NeZero.ne N) (CRen N z μ) F = obsLimC Wf cf F :=
  ((tendsto_obsLim hE hC F hF).limUnder_eq).symm

/-- **The tensor-sector readings as the observer's double limits**: on every admissible family,
`contT (rhoD (fR N) z) F = ∑_α (∏ᵢ cᵢ(αᵢ)) · obsLimC Wf cf ((eI αᵢ, fᵢ))ᵢ` (`CompReduce.contT_expand`).
DERIVED: no numeral. -/
theorem contT_rhoD_eq_obs [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hE : ExpandR Wf cf z μ) (hC : ConvC (NeZero.ne N) (CRen N z μ))
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → TDatum) (hF : Adm F) :
    contT (NeZero.ne N) (rhoD (fR N) z) F
      = ∑ α : ι → Idx4, (∏ i, (F i).1 (α i)) * obsLimC Wf cf (fun i => (eI (α i), (F i).2)) := by
  rw [CompReduce.contT_expand (NeZero.ne N) (rhoD (fR N) z) (CRen N z μ) eI
    (fun k α => buildRen_he2 _ _ μ k α) hC F hF]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [contC_eq_obsLimC hE hC _ (CompReduce.adm_relabel hF _)]
  rfl

/-! ## 3. The shrunk core and the capstone -/

/-- **The substrate core with finite moments**: `ClusterRoute.SubstrateCoreCL` with the channel clause
replaced by `FinMom b Wf` and the plaquette exponential at `s = b` kept. DERIVED: no numeral. -/
structure SubstrateCoreMin [NeZero N] (W : ConfFlow N) (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow N) :
    Prop where
  b_pos : 0 < b
  /-- The flow to the physical scale is `W`. -/
  top : Wf b = W
  /-- The plaquette class at the physical scale, exponentially. -/
  plaq : ∃ (γ : Ix0 → ℝ) (γP t C : ℝ), 0 < t ∧
    ∀ᶠ k in atTop, ∀ q, ScaleChan Wf t C γ γP k b (Sum.inr q)
  /-- Finite flowed moments at every scale in `(0, b]`. -/
  mom : FinMom b Wf
  /-- Asymptotic freedom: a two-point kernel of the trace at `z` with the asymptotic-freedom coefficient. -/
  af : ∃ G : ℝ → ℝ, TwoPointKernel (NeZero.ne N) (rhoD (fR N) z) G ∧ AFCoefficient N G

/-- `SubstrateCoreCL` gives `SubstrateCoreMin`. DERIVED: no numeral. -/
theorem coreMin_of_coreCL [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {b : ℝ} {Wf : ℝ → ConfFlow N}
    (S : SubstrateCoreCL W z b Wf) : SubstrateCoreMin W z b Wf :=
  ⟨S.b_pos, S.top, by
    obtain ⟨γ, γP, H⟩ := S.scale
    obtain ⟨t, C, ht, h⟩ := H.top
    exact ⟨γ, γP, t, C, ht, h⟩, finMom_of_chan S.scale, S.af⟩

/-- **`CompOS (CRen N z μ)` from the shrunk core, `ExpandR`, `ClusterPM` and the observer forms of `CovC`
and `CompNondeg`.** DERIVED: no numeral. -/
theorem compOS_of_min [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (S : SubstrateCoreMin W z b Wf)
    (hE : ExpandR Wf cf z μ) (hcl : ClusterPM Wf cf) (hV : FlowCovLim Wf cf) (hP : ProxyNondeg Wf cf) :
    CompOS (NeZero.ne N) (CRen N z μ) :=
  have hC : ConvC (NeZero.ne N) (CRen N z μ) := convC_of_finMom S.b_pos S.mom hE
  ⟨hC, os0C_of_cluster hC hE hcl, os1C_of_finMom S.b_pos S.mom hE, covC_of_flowCovLim hE hC hV,
    compNondeg_of_proxy hE hC hP⟩

/-- **`ApproxK` from the generation clause beyond `r`** at the shrunk inputs
(`ClusterRoute.approxK_of_beyond_covC_cl`'s proof). DERIVED: `2` the least colour count; `0` the plane and
the reference step. -/
theorem approxK_of_beyond_min (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ}
    {μ : OffMix} {b r : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCoreMin W z b Wf) (hE : ExpandR Wf cf z μ) (hcl : ClusterPM Wf cf)
    (hV : FlowCovLim Wf cf) (hP : ProxyNondeg Wf cf) (hphys : (Φ0 W).PhysRange r)
    (hB : ∀ P, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N z μ) 0)
      (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) P) :
    ApproxK (kernC (NeZero.ne N) (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) := by
  obtain ⟨t, C, ht, hS⟩ := uv_of_plaq S.b_pos S.top S.plaq
  have hU := ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) W ht hS
  have hCO := compOS_of_min S hE hcl hV hP
  let D := capData hN2 W hU hphys (CRen N z μ)
    (unifLocal_buildRen (rhoD (fR N) z) (bareD (fR N) (bR N)) μ) (reflCovLat_CRen z μ) hCO
  refine approxK_iff_forall.2 fun P => ?_
  obtain ⟨n, hn⟩ := exists_beyond_iterate (NeZero.ne N) r P
  exact approxKAt_of_iterate D 0 n P (hB _ hn)

/-- **The per-`N` inputs, shrunk**: `ClayRunSeed.NarrowInputsAtRS` with `ScalePMChan` narrowed to the
plaquette exponential and `FinMom`, `ExpandStrong` to `ExpandR`, `CovC` replaced by `FlowCovLim Wf cf` and
`CompNondeg` by `ProxyNondeg Wf cf`. DERIVED: `2` the least colour count; `0` the plane and the reference
step. -/
def NarrowInputsAtMin (N : ℕ) (hN2 : 2 ≤ N) (W : ConfFlow N) (r : ℝ) : Prop :=
  haveI : NeZero N := ⟨by omega⟩
  (Φ0 W).PhysRange r ∧
  ∃ (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)),
    SubstrateCoreMin W (ZCanon.zFix N zri zwe) b Wf
      ∧ ExpandR Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ ClusterPM Wf cf
      ∧ FlowCovLim Wf cf
      ∧ WardT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe))
      ∧ ProxyNondeg Wf cf
      ∧ (∀ P, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
          (mixKG hN2 W (CRen N (ZCanon.zFix N zri zwe) μ) r) (gramF hN2 W r) P)
      ∧ (∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (ne_zero_of_two_le hN2) ℓ)
      ∧ WDeltaRun.RunSeed N

/-- **`NarrowInputsAtMin` gives the general-`N` bundle at `W`.** DERIVED: `2` the least colour count. -/
theorem clayInputsN_of_narrowAtMin (hN2 : 2 ≤ N) {W : ConfFlow N} {r : ℝ}
    (h : NarrowInputsAtMin N hN2 W r) : SUNBest.ClayInputsN N hN2 := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hcl, hV, hW, hP, hB, h3, hRS⟩ := h
  obtain ⟨t, C, ht, hS⟩ := uv_of_plaq S.b_pos S.top S.plaq
  have hU := ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) W ht hS
  obtain ⟨G, hK, hAF⟩ := S.af
  obtain ⟨ℓ, hℓ, h3'⟩ := h3
  exact ⟨W, r, t, |C|, zri, zwe, μ, G,
    { t_pos := ht
      moments := hU
      phys := hphys
      far := hRS
      hri := hri
      hwe := hwe
      kernel := hK
      af := hAF
      low := obsLower_of_scale (ne_zero_of_two_le hN2) hℓ zri zwe h3'
      ward := hW
      comp := compOS_of_min S hE hcl hV hP
      approx := approxK_of_beyond_min hN2 S hE hcl hV hP hphys hB }⟩

/-- **`ClayStatementDy` from `NarrowInputsAtMin` at some observer and margin, at every `N ≥ 2`**
(`SUNBest.clayStatement_of_inputs`). DERIVED: `2` the least colour count. -/
theorem clayStatement_of_narrowAtMin
    (h : ∀ (N : ℕ) (hN2 : 2 ≤ N), ∃ (W : ConfFlow N) (r : ℝ), NarrowInputsAtMin N hN2 W r) :
    MassGap.ClayStatementDy :=
  SUNBest.clayStatement_of_inputs fun N hN2 => by
    obtain ⟨W, r, hA⟩ := h N hN2
    exact clayInputsN_of_narrowAtMin hN2 hA

/-- **`NarrowInputsAtRS` gives `NarrowInputsAtMin`** at the same `W`, `r` (`coreMin_of_coreCL`,
`StrongExpand.expandR_of_strong`, `FlowCovN.flowCovLim_of_covC`, `NondegFromProxy.proxyNondeg_of_compNondeg`,
with `ConvC` from `ClusterRoute.convC_of_chan`). DERIVED: `2` the least colour count. -/
theorem narrowInputsAtMin_of_RS (hN2 : 2 ≤ N) {W : ConfFlow N} {r : ℝ}
    (h : NarrowInputsAtRS N hN2 W r) : NarrowInputsAtMin N hN2 W r := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hcl, hV, hW, hP, hB, h3, hRS⟩ := h
  have hE' := expandR_of_strong hE
  have hC := convC_of_chan S.b_pos S.scale hE'
  exact ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, coreMin_of_coreCL S, hE', hcl,
    flowCovLim_of_covC hE' hC hV, hW, proxyNondeg_of_compNondeg hE' hC hP, hB, h3, hRS⟩

end MassGap.InputMerge

end

#print axioms MassGap.InputMerge.finMom_of_chan
#print axioms MassGap.InputMerge.chanPM_local
#print axioms MassGap.InputMerge.boundC_of_finMom
#print axioms MassGap.InputMerge.convC_of_finMom
#print axioms MassGap.InputMerge.os1C_of_finMom
#print axioms MassGap.InputMerge.uv_of_plaq
#print axioms MassGap.InputMerge.tendsto_obsLim
#print axioms MassGap.InputMerge.contC_eq_obsLimC
#print axioms MassGap.InputMerge.contT_rhoD_eq_obs
#print axioms MassGap.InputMerge.coreMin_of_coreCL
#print axioms MassGap.InputMerge.compOS_of_min
#print axioms MassGap.InputMerge.approxK_of_beyond_min
#print axioms MassGap.InputMerge.clayInputsN_of_narrowAtMin
#print axioms MassGap.InputMerge.clayStatement_of_narrowAtMin
#print axioms MassGap.InputMerge.narrowInputsAtMin_of_RS
