import Mathlib
import MassGap.ProxyGenLimN

/-!
# MassGap.FlowCovN — `FlowCov` against `CovC`, and the capstone with `CovC` as the per-`N` input

`ProxyGenLimN.FlowApproxInputsN` carries, at each `N ≥ 2`, `CovFromFlow.FlowCov Wf cf`: at flow scales
`s` accumulating at `0`, the flowed readings `msLat Wf cf k s` of every rotated admissible family converge
along `ultra` to `∑_σ ∏ⱼ repF R iⱼ σⱼ · lim_ultra msLat Wf cf k s ((σⱼ, fⱼ))` (exact covariance of the
proxies' limits at that scale). It is read once, through `CovFromFlow.covC_of_scale_strong`, to produce
`CovC (CRen N z μ)` (the field `cov` of `CompOS`). This module states what separates `FlowCov` from
`CovC`, the rate-level covariance clause `FlowCovLim`, which is equivalent to `CovC`, and the
capstone with `CovC` in place of `FlowCov`. Declarations are in the namespace `MassGap.FlowCovN`.

## 1. `FlowCov = CovC + covariance of the expansion remainder` (proved)

`RemCovAt Wf cf z μ s`: for every `R ∈ O(4)` and every admissible family `F`, the expansion remainder of
the rotated family, `latC(F ∘ R) − msLat_s(F ∘ R)`, converges along `ultra` to
`∑_σ ∏ⱼ repF R iⱼ σⱼ · (contC((σⱼ, fⱼ)) − lim_ultra msLat_s((σⱼ, fⱼ)))`: the remainder at the fixed scale
`s` transforms with `repF` in the limit. `RemCov Wf cf z μ`: `RemCovAt` at scales accumulating at `0`.

* `covC_apply`: `CovC (CRen N z μ)` at a family `F : ι → Ix0 × TestFn`, with `repF` written out.
* **`flowCovAt_of_covC_remCovAt`**, **`remCovAt_of_covC_flowCovAt`**: under `CovC`, at each scale `s`,
  `FlowCovAt s ↔ RemCovAt s` (`msLat = latC − (latC − msLat)`; no other hypothesis).
* **`covC_of_flowCovAt_remCovAt`**: `FlowCovAt s` and `RemCovAt s` at one scale `s` give `CovC`
  (`latC = msLat + (latC − msLat)`; no other hypothesis).
* **`flowCov_iff_remCov_of_covC`**: under `CovC`, `FlowCov Wf cf ↔ RemCov Wf cf z μ`.
* **`flowCov_iff_covC_and_remCov`**: under `ScaleControlAll b Wf` (`0 < b`) and `ExpandStrong Wf cf z μ`,
  `FlowCov Wf cf ↔ CovC (CRen N z μ) ∧ RemCov Wf cf z μ`.

So the content of `FlowCov` beyond the target clause `CovC` is exactly `RemCov`: exact covariance of the
expansion remainder at fixed scales accumulating at `0`. `ExpandR` bounds that remainder by
`K (s/d)^ε` at each `s` and gives no identity at any one `s`; `CovC → FlowCov` is therefore
`CovC → RemCov`, which is not proved and is not derived from the rate bounds (they bound the remainder, they give no
identity at any one `s`).

## 2. The rate-level covariance of the proxies is `CovC` (proved)

`FlowCovLim Wf cf`: for every `R ∈ O(4)`, admissible `F` and `η > 0`, at all small `s > 0`, eventually
along `ultra`, `|msLat_s(F ∘ R) − ∑_σ ∏ⱼ repF R iⱼ σⱼ · lim_ultra msLat_s((σⱼ, fⱼ))| ≤ η`: the proxies are
covariant up to an error that vanishes as `s → 0⁺`.

* `abs_sub_limUnder_le`: `v → T` along `ultra` and `|v − w| ≤ e` eventually give `|T − lim_ultra w| ≤ e`
  (`w` is eventually bounded, so it converges along the ultrafilter).
* `eventually_rate`: `ExpandR` and `ConvC` give, for every `R`, admissible `F` and `η > 0`, at all small
  `s`: eventually `|latC(F ∘ R) − msLat_s(F ∘ R)| ≤ η` and
  `|∑_σ p_σ contC(σ) − ∑_σ p_σ lim_ultra msLat_s(σ)| ≤ η` (the rotated family is `d/2`-separated,
  `CovFromFlow.sepBy_rotTest`; the index families are `d`-separated).
* **`flowCovLim_of_covC`**, **`covC_of_flowCovLim`**, **`flowCovLim_iff_covC`**: under `ExpandR` and
  `ConvC`, `FlowCovLim Wf cf ↔ CovC (CRen N z μ)`.
* **`flowCovLim_iff_covC_of_choice`**: under `scale` and `ExpandStrong`, `FlowCovLim Wf cf ↔ CovC`.
* `flowCovLim_of_flowCov`: under `scale` and `ExpandStrong`, `FlowCov → FlowCovLim`.

`FlowCovLim` is the choice-free restatement on the proxy side: `CovC` reads neither `Wf` nor `cf`.
`FlowCov` asks the error of `FlowCovLim` to be exactly `0` at scales accumulating at `0`; that extra
clause is `RemCov` (§1).

## 3. The capstone (proved)

* `inputsAt_of_covC`: `ProxyGenLimN.inputsAt_of_approx` with `GradientFlowPropsN` replaced by
  `ExpandStrong`, `CoefBound`, `CovC`, `WardT`, `CompNondeg` (`CompOS` assembled from
  `FlowChoice.convC_of_choice`, `os0C_of_scale_expand_coef`, `os1C_of_scale_expand`, `CovC`,
  `CompNondeg`).
* `FlowCovInputsN N hN2`: `ProxyGenLimN.FlowApproxInputsN` with `FlowCov Wf cf` replaced by
  `CovC (CRen N (zFix N zri zwe) μ)`.
* **`flowCovInputsN_of_approx`**: `FlowApproxInputsN N hN2 → FlowCovInputsN N hN2`
  (`FlowChoice.covC_of_flowCov_choice`). At the same witnesses, the converse holds exactly when
  `RemCov` holds there (§1).
* **`clayStatement_of_covC`**: `FlowCovInputsN N hN2` at every `N ≥ 2` gives `ClayStatementDy`.

Per-`N` inputs of `clayStatement_of_covC`: `SubstrateCoreAt` (`b_pos`, `top`, `scale`, `af`),
`ExpandStrong Wf cf z μ`, `CoefBound cf`, `CovC (CRen N z μ)`, `WardT (rhoD (fR N) z)`,
`CompNondeg (CRen N z μ)`, `ApproxK` at `r`, the three-point clause and `WDeltaRun.RunSeed N`, at
`z = zFix N zri zwe`. `CovC`, `WardT`, `CompNondeg` and `ApproxK` read neither `Wf` nor `cf`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the limit of the scale; `2` the halving of the separation (`√4`, the
dimension), the least colour count; `3`, `4` the splits of the tolerance; `4` the dimension; `12` the
bound of the block-step flow.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.FlowCovN

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
  MassGap.ProxyGenObserver MassGap.ProxyBoundFromScale MassGap.ObserverFlowSUN MassGap.FlowChoice
  MassGap.ProxyGenLimN

variable {N : ℕ}

/-! ## 1. The remainder clause -/

/-- **Covariance of the expansion remainder at scale `s`**: module docstring, §1.
DERIVED: `4` the dimension. -/
def RemCovAt [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (z : Chan → ℕ → ℝ)
    (μ : OffMix) (s : ℝ) : Prop :=
  ∀ R : Matrix (Fin 4) (Fin 4) ℝ, R ∈ Matrix.orthogonalGroup (Fin 4) ℝ →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → Ix0 × TestFn), Adm F →
      Tendsto (fun k => latC (NeZero.ne N) (CRen N z μ) k (fun i => ((F i).1, rotTest R (F i).2))
          - msLat Wf cf k s (fun i => ((F i).1, rotTest R (F i).2))) (ultra : Filter ℕ)
        (𝓝 (∑ σ ∈ Fintype.piFinset (fun i => (repF R (F i).1).support),
          (∏ i, repF R (F i).1 (σ i))
            * (contC (NeZero.ne N) (CRen N z μ) (fun i => (σ i, (F i).2))
              - limUnder (ultra : Filter ℕ) (fun k => msLat Wf cf k s (fun i => (σ i, (F i).2))))))

/-- **The expansion remainder is covariant at scales arbitrarily close to `0`**: module docstring, §1.
DERIVED: `0` the limit of the scale. -/
def RemCov [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (z : Chan → ℕ → ℝ)
    (μ : OffMix) : Prop :=
  ∃ᶠ s in 𝓝[>] (0 : ℝ), RemCovAt Wf cf z μ s

/-- `CovC (CRen N z μ)` at a family of `Ix0 × TestFn`, with the representation `repF` written out.
DERIVED: `4` the dimension. -/
theorem covC_apply [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} (hC : CovC (NeZero.ne N) (CRen N z μ))
    {R : Matrix (Fin 4) (Fin 4) ℝ} (hR : R ∈ Matrix.orthogonalGroup (Fin 4) ℝ) {ι : Type} [Fintype ι]
    [DecidableEq ι] (F : ι → Ix0 × TestFn) (hF : Adm F) :
    Tendsto (fun k => latC (NeZero.ne N) (CRen N z μ) k (fun i => ((F i).1, rotTest R (F i).2)))
      (ultra : Filter ℕ)
      (𝓝 (∑ σ ∈ Fintype.piFinset (fun i => (repF R (F i).1).support),
        (∏ i, repF R (F i).1 (σ i)) * contC (NeZero.ne N) (CRen N z μ) (fun i => (σ i, (F i).2)))) :=
  hC R hR ι F hF

/-- **Under `CovC`, `RemCovAt s` gives `FlowCovAt s`**: module docstring, §1. DERIVED: no numeral. -/
theorem flowCovAt_of_covC_remCovAt [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} {s : ℝ} (hC : CovC (NeZero.ne N) (CRen N z μ))
    (hRm : RemCovAt Wf cf z μ s) : FlowCovAt Wf cf s := by
  intro R hR ι _ _ F hF
  have h := ((covC_apply hC hR F hF).sub (hRm R hR ι F hF)).congr fun k => sub_sub_cancel _ _
  convert h using 2
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun σ _ => by ring

/-- **Under `CovC`, `FlowCovAt s` gives `RemCovAt s`**: module docstring, §1. DERIVED: no numeral. -/
theorem remCovAt_of_covC_flowCovAt [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} {s : ℝ} (hC : CovC (NeZero.ne N) (CRen N z μ))
    (hF : FlowCovAt Wf cf s) : RemCovAt Wf cf z μ s := by
  intro R hR ι _ _ F hFa
  have h := (covC_apply hC hR F hFa).sub (hF R hR ι F hFa)
  convert h using 2
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun σ _ => by ring

/-- **`FlowCovAt s` and `RemCovAt s` at one scale give `CovC`**: module docstring, §1. DERIVED: no
numeral. -/
theorem covC_of_flowCovAt_remCovAt [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} {s : ℝ} (hF : FlowCovAt Wf cf s) (hRm : RemCovAt Wf cf z μ s) :
    CovC (NeZero.ne N) (CRen N z μ) := by
  intro R hR ι _ _ F hFa
  have h := ((hF R hR ι F hFa).add (hRm R hR ι F hFa)).congr fun k => add_sub_cancel _ _
  show Tendsto (fun k => latC (NeZero.ne N) (CRen N z μ) k (fun i => ((F i).1, rotTest R (F i).2)))
    (ultra : Filter ℕ)
    (𝓝 (∑ σ ∈ Fintype.piFinset (fun i => (repF R (F i).1).support),
      (∏ i, repF R (F i).1 (σ i)) * contC (NeZero.ne N) (CRen N z μ) (fun i => (σ i, (F i).2))))
  convert h using 2
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun σ _ => by ring

/-- **Under `CovC`, `FlowCov ↔ RemCov`**: module docstring, §1. DERIVED: no numeral. -/
theorem flowCov_iff_remCov_of_covC [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hC : CovC (NeZero.ne N) (CRen N z μ)) :
    FlowCov Wf cf ↔ RemCov Wf cf z μ :=
  ⟨fun h => h.mono fun _ hs => remCovAt_of_covC_flowCovAt hC hs,
    fun h => h.mono fun _ hs => flowCovAt_of_covC_remCovAt hC hs⟩

/-- **`FlowCov` is `CovC` together with `RemCov`**, at any choice meeting `scale` and `ExpandStrong`:
module docstring, §1. DERIVED: `0` the lower end of the scale. -/
theorem flowCov_iff_covC_and_remCov [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hb : 0 < b) (hsc : ScaleControlAll b Wf)
    (hE : ExpandStrong Wf cf z μ) :
    FlowCov Wf cf ↔ CovC (NeZero.ne N) (CRen N z μ) ∧ RemCov Wf cf z μ := by
  constructor
  · intro h
    have hC := covC_of_flowCov_choice hb hsc hE h
    exact ⟨hC, (flowCov_iff_remCov_of_covC hC).1 h⟩
  · rintro ⟨hC, h⟩
    exact (flowCov_iff_remCov_of_covC hC).2 h

/-! ## 2. The rate-level covariance -/

/-- **The flowed proxies are covariant up to an error vanishing as `s → 0⁺`**: module docstring, §2.
DERIVED: `0` the limit of the scale; `4` the dimension. -/
def FlowCovLim [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) : Prop :=
  ∀ R : Matrix (Fin 4) (Fin 4) ℝ, R ∈ Matrix.orthogonalGroup (Fin 4) ℝ →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → Ix0 × TestFn), Adm F →
      ∀ η : ℝ, 0 < η → ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
        |msLat Wf cf k s (fun i => ((F i).1, rotTest R (F i).2))
          - ∑ σ ∈ Fintype.piFinset (fun i => (repF R (F i).1).support),
              (∏ i, repF R (F i).1 (σ i))
                * limUnder (ultra : Filter ℕ) (fun k => msLat Wf cf k s (fun i => (σ i, (F i).2)))| ≤ η

/-- **The limit of a nearby sequence**: module docstring, §2. DERIVED: `1` the margin around the
limit. -/
theorem abs_sub_limUnder_le {v w : ℕ → ℝ} {T e : ℝ} (hv : Tendsto v (ultra : Filter ℕ) (𝓝 T))
    (h : ∀ᶠ k in (ultra : Filter ℕ), |v k - w k| ≤ e) :
    |T - limUnder (ultra : Filter ℕ) w| ≤ e := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hb : ∀ᶠ k in (ultra : Filter ℕ), |w k| ≤ |T| + 1 + e := by
    filter_upwards [h, hv.abs.eventually (gt_mem_nhds (lt_add_one |T|))] with k hk hk'
    have h5 := abs_sub_abs_le_abs_sub (w k) (v k)
    rw [abs_sub_comm] at h5
    linarith
  obtain ⟨y, hy⟩ := exists_tendsto_ultra_of_ultra w _ hb
  rw [hy.limUnder_eq]
  exact le_of_tendsto ((hv.sub hy).abs) h

/-- **The two rate bounds at all small scales**: module docstring, §2. DERIVED: `2` the halving of the
separation; `0` the limit of the scale. -/
theorem eventually_rate [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ}
    {μ : OffMix} (hE : ExpandR Wf cf z μ) (hCv : ConvC (NeZero.ne N) (CRen N z μ))
    {R : Matrix (Fin 4) (Fin 4) ℝ} (hR : R ∈ Matrix.orthogonalGroup (Fin 4) ℝ) {ι : Type} [Fintype ι]
    [DecidableEq ι] (F : ι → Ix0 × TestFn) (hFa : Adm F) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      (∀ᶠ k in (ultra : Filter ℕ),
        |latC (NeZero.ne N) (CRen N z μ) k (fun i => ((F i).1, rotTest R (F i).2))
          - msLat Wf cf k s (fun i => ((F i).1, rotTest R (F i).2))| ≤ η)
      ∧ |∑ σ ∈ Fintype.piFinset (fun i => (repF R (F i).1).support),
            (∏ i, repF R (F i).1 (σ i)) * contC (NeZero.ne N) (CRen N z μ) (fun i => (σ i, (F i).2))
          - ∑ σ ∈ Fintype.piFinset (fun i => (repF R (F i).1).support),
            (∏ i, repF R (F i).1 (σ i))
              * limUnder (ultra : Filter ℕ) (fun k => msLat Wf cf k s (fun i => (σ i, (F i).2)))|
        ≤ η := by
  obtain ⟨θ, ε, Kr, κr, hθ, hε, hEx⟩ := hE
  have hRR := orth_transpose_mul hR
  obtain ⟨hcont, d, hd, hsep⟩ := hFa
  have hd2 : 0 < d / 2 := half_pos hd
  have hGc : ContD (fun i => ((F i).1, rotTest R (F i).2) : ι → CDatum (CRen N z μ)) :=
    fun i => continuous_rotTest' hRR (hcont i)
  have hGs : SepD (d / 2) (fun i => ((F i).1, rotTest R (F i).2) : ι → CDatum (CRen N z μ)) :=
    fun i j hij => sepBy_rotTest hRR hd (hsep i j hij)
  have hSc : ∀ σ : ι → Ix0, ContD (fun i => (σ i, (F i).2) : ι → CDatum (CRen N z μ)) :=
    fun σ i => hcont i
  have hSs : ∀ σ : ι → Ix0, SepD d (fun i => (σ i, (F i).2) : ι → CDatum (CRen N z μ)) :=
    fun σ i j hij => hsep i j hij
  let A : ℝ := Kr ^ Fintype.card ι * ∏ i, ((d / 2) ^ κr (F i).1)⁻¹ * l1 (rotTest R (F i).2)
  let B : (ι → Ix0) → ℝ := fun σ => Kr ^ Fintype.card ι * ∏ i, ((d ^ κr (σ i))⁻¹ * l1 (F i).2)
  let S : Finset (ι → Ix0) := Fintype.piFinset (fun i => (repF R (F i).1).support)
  let p : (ι → Ix0) → ℝ := fun σ => ∏ i, repF R (F i).1 (σ i)
  let c : ℝ := ∑ σ ∈ S, |p σ| * B σ
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      A * (s / (d / 2)) ^ ε < η ∧ c * (s / d) ^ ε < η ∧ s < θ * (d / 2) ∧ 0 < s :=
    (eventually_rate_lt hε A hη).and ((eventually_rate_lt hε c hη).and
      (((gt_mem_nhds (mul_pos hθ hd2)).filter_mono nhdsWithin_le_nhds).and
        (eventually_mem_nhdsWithin.mono fun s hs => hs)))
  filter_upwards [hev] with s ⟨hs1, hs2, hs3, hs4⟩
  have hsd : s ≤ θ * d := by
    have := mul_pos hθ hd
    linarith
  refine ⟨?_, ?_⟩
  · filter_upwards [(hEx ι _ (d / 2) hd2 hGc hGs s hs4 hs3.le).filter_mono ultra_le] with k hk
    have e : Kr ^ Fintype.card ι * (s / (d / 2)) ^ ε
        * ∏ i, (((d / 2) ^ κr (F i).1)⁻¹ * l1 (rotTest R (F i).2)) = A * (s / (d / 2)) ^ ε := by
      dsimp only [A]
      ring
    exact (hk.trans (le_of_eq e)).trans hs1.le
  · have hσ : ∀ σ ∈ S, |contC (NeZero.ne N) (CRen N z μ) (fun i => (σ i, (F i).2))
        - limUnder (ultra : Filter ℕ) (fun k => msLat Wf cf k s (fun i => (σ i, (F i).2)))|
          ≤ B σ * (s / d) ^ ε := by
      intro σ _
      refine abs_sub_limUnder_le (hCv ι _ ⟨hSc σ, d, hd, hSs σ⟩) ?_
      filter_upwards [(hEx ι _ d hd (hSc σ) (hSs σ) s hs4 hsd).filter_mono ultra_le] with k hk
      dsimp only [B] at hk ⊢
      refine hk.trans (le_of_eq ?_)
      ring
    have hsum : ∑ σ ∈ S, |p σ| * (B σ * (s / d) ^ ε) = c * (s / d) ^ ε := by
      show _ = (∑ σ ∈ S, |p σ| * B σ) * (s / d) ^ ε
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun σ _ => by ring
    show |∑ σ ∈ S, p σ * contC (NeZero.ne N) (CRen N z μ) (fun i => (σ i, (F i).2))
        - ∑ σ ∈ S, p σ * limUnder (ultra : Filter ℕ)
            (fun k => msLat Wf cf k s (fun i => (σ i, (F i).2)))| ≤ η
    rw [← Finset.sum_sub_distrib]
    calc |∑ σ ∈ S, (p σ * contC (NeZero.ne N) (CRen N z μ) (fun i => (σ i, (F i).2))
            - p σ * limUnder (ultra : Filter ℕ) (fun k => msLat Wf cf k s (fun i => (σ i, (F i).2))))|
        ≤ ∑ σ ∈ S, |p σ * contC (NeZero.ne N) (CRen N z μ) (fun i => (σ i, (F i).2))
            - p σ * limUnder (ultra : Filter ℕ) (fun k => msLat Wf cf k s (fun i => (σ i, (F i).2)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ σ ∈ S, |p σ| * (B σ * (s / d) ^ ε) := by
          refine Finset.sum_le_sum fun σ hσS => ?_
          rw [← mul_sub, abs_mul]
          exact mul_le_mul_of_nonneg_left (hσ σ hσS) (abs_nonneg _)
      _ = c * (s / d) ^ ε := hsum
      _ ≤ η := hs2.le

/-- **`CovC` gives `FlowCovLim`** under `ExpandR` and `ConvC`: module docstring, §2. DERIVED: `3` the
split of the tolerance. -/
theorem flowCovLim_of_covC [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hE : ExpandR Wf cf z μ) (hCv : ConvC (NeZero.ne N) (CRen N z μ))
    (hC : CovC (NeZero.ne N) (CRen N z μ)) : FlowCovLim Wf cf := by
  intro R hR ι _ _ F hFa η hη
  have h3 : (0 : ℝ) < η / 3 := by linarith
  have hT := Metric.tendsto_nhds.1 (covC_apply hC hR F hFa) (η / 3) h3
  filter_upwards [eventually_rate hE hCv hR F hFa h3] with s ⟨h1, h2⟩
  filter_upwards [h1, hT] with k hk1 hk2
  rw [Real.dist_eq] at hk2
  set L := latC (NeZero.ne N) (CRen N z μ) k (fun i => ((F i).1, rotTest R (F i).2))
  set M := msLat Wf cf k s (fun i => ((F i).1, rotTest R (F i).2))
  set X := ∑ σ ∈ Fintype.piFinset (fun i => (repF R (F i).1).support),
    (∏ i, repF R (F i).1 (σ i)) * contC (NeZero.ne N) (CRen N z μ) (fun i => (σ i, (F i).2))
  set Y := ∑ σ ∈ Fintype.piFinset (fun i => (repF R (F i).1).support),
    (∏ i, repF R (F i).1 (σ i))
      * limUnder (ultra : Filter ℕ) (fun k => msLat Wf cf k s (fun i => (σ i, (F i).2)))
  have i1 := abs_sub_le M L Y
  have i2 := abs_sub_le L X Y
  rw [abs_sub_comm] at hk1
  linarith

/-- **`FlowCovLim` gives `CovC`** under `ExpandR` and `ConvC`: module docstring, §2. DERIVED: `4` the
split of the tolerance. -/
theorem covC_of_flowCovLim [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hE : ExpandR Wf cf z μ) (hCv : ConvC (NeZero.ne N) (CRen N z μ))
    (hL : FlowCovLim Wf cf) : CovC (NeZero.ne N) (CRen N z μ) := by
  intro R hR ι _ _ F hFa
  show Tendsto (fun k => latC (NeZero.ne N) (CRen N z μ) k (fun i => ((F i).1, rotTest R (F i).2)))
    (ultra : Filter ℕ)
    (𝓝 (∑ σ ∈ Fintype.piFinset (fun i => (repF R (F i).1).support),
      (∏ i, repF R (F i).1 (σ i)) * contC (NeZero.ne N) (CRen N z μ) (fun i => (σ i, (F i).2))))
  rw [Metric.tendsto_nhds]
  intro η hη
  have h4 : (0 : ℝ) < η / 4 := by linarith
  obtain ⟨s, ⟨h1, h2⟩, h3⟩ :=
    ((eventually_rate hE hCv hR F hFa h4).and (hL R hR ι F hFa (η / 4) h4)).exists
  filter_upwards [h1, h3] with k hk1 hk3
  rw [Real.dist_eq]
  set L := latC (NeZero.ne N) (CRen N z μ) k (fun i => ((F i).1, rotTest R (F i).2))
  set M := msLat Wf cf k s (fun i => ((F i).1, rotTest R (F i).2))
  set X := ∑ σ ∈ Fintype.piFinset (fun i => (repF R (F i).1).support),
    (∏ i, repF R (F i).1 (σ i)) * contC (NeZero.ne N) (CRen N z μ) (fun i => (σ i, (F i).2))
  set Y := ∑ σ ∈ Fintype.piFinset (fun i => (repF R (F i).1).support),
    (∏ i, repF R (F i).1 (σ i))
      * limUnder (ultra : Filter ℕ) (fun k => msLat Wf cf k s (fun i => (σ i, (F i).2)))
  have i1 := abs_sub_le L M Y
  have i2 := abs_sub_le L Y X
  rw [abs_sub_comm Y X] at i2
  linarith

/-- **`FlowCovLim ↔ CovC`** under `ExpandR` and `ConvC`: module docstring, §2. DERIVED: no numeral. -/
theorem flowCovLim_iff_covC [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hE : ExpandR Wf cf z μ) (hCv : ConvC (NeZero.ne N) (CRen N z μ)) :
    FlowCovLim Wf cf ↔ CovC (NeZero.ne N) (CRen N z μ) :=
  ⟨covC_of_flowCovLim hE hCv, flowCovLim_of_covC hE hCv⟩

/-- **`FlowCovLim ↔ CovC`** at any choice meeting `scale` and `ExpandStrong`: module docstring, §2.
DERIVED: `0` the lower end of the scale. -/
theorem flowCovLim_iff_covC_of_choice [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hb : 0 < b) (hsc : ScaleControlAll b Wf)
    (hE : ExpandStrong Wf cf z μ) : FlowCovLim Wf cf ↔ CovC (NeZero.ne N) (CRen N z μ) :=
  flowCovLim_iff_covC (expandR_of_strong hE) (convC_of_choice hb hsc hE)

/-- **`FlowCov` gives `FlowCovLim`** at any choice meeting `scale` and `ExpandStrong`. DERIVED: `0` the
lower end of the scale. -/
theorem flowCovLim_of_flowCov [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hb : 0 < b) (hsc : ScaleControlAll b Wf)
    (hE : ExpandStrong Wf cf z μ) (hF : FlowCov Wf cf) : FlowCovLim Wf cf :=
  (flowCovLim_iff_covC_of_choice hb hsc hE).2 (covC_of_flowCov_choice hb hsc hE hF)

/-! ## 3. The capstone -/

/-- **`ProxyGenLimN.inputsAt_of_approx` with `CovC` in place of `FlowCov`**: module docstring, §3.
DERIVED: `2` the least colour count; `0` the lower end of the observer's scale; `12` the bound of the
block-step flow. -/
theorem inputsAt_of_covC (hN2 : 2 ≤ N) [NeZero N] {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) {s₀ r : ℝ} (hs0 : 0 ≤ s₀) (hr : s₀ < r)
    {zri zwe : ℕ → ℝ} (hri : ∀ k, zri k ≠ 0) (hwe : ∀ k, zwe k ≠ 0) {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCoreAt (sunFam hN2 c hc0 hc s₀) (ZCanon.zFix N zri zwe) b Wf)
    (hE : ExpandStrong Wf cf (ZCanon.zFix N zri zwe) μ) (hcb : CoefBound cf)
    (hV : CovC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ))
    (hW : WardT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe)))
    (hP : CompNondeg (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ))
    (hA : ApproxK (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
      (mixKG hN2 (sunFam hN2 c hc0 hc s₀) (CRen N (ZCanon.zFix N zri zwe) μ) r)
      (gramF hN2 (sunFam hN2 c hc0 hc s₀) r))
    (h3 : ∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (ne_zero_of_two_le hN2) ℓ)
    (hfar : WDeltaRun.RunSeed N) :
    ∃ (t C : ℝ) (G : ℝ → ℝ),
      SUNBest.InputsAt hN2 (sunFam hN2 c hc0 hc s₀) r t |C| zri zwe μ G := by
  obtain ⟨t, C, ht, hS⟩ := uv_of_scale S.b_pos S.top S.scale
  have hU := ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) (sunFam hN2 c hc0 hc s₀) ht hS
  obtain ⟨G, hK, hAF⟩ := S.af
  obtain ⟨ℓ, hℓ, h3'⟩ := h3
  exact ⟨t, C, G,
    { t_pos := ht
      moments := hU
      phys := sunFam_physRange hN2 hc0 hc hs0 hr
      far := hfar
      hri := hri
      hwe := hwe
      kernel := hK
      af := hAF
      low := obsLower_of_scale (ne_zero_of_two_le hN2) hℓ zri zwe h3'
      ward := hW
      comp := ⟨convC_of_choice S.b_pos S.scale hE,
        os0C_of_scale_expand_coef S.b_pos S.scale (expandR_of_strong hE) hcb,
        os1C_of_scale_expand S.b_pos S.scale (expandR_of_strong hE), hV, hP⟩
      approx := hA }⟩

/-- **The per-`N` inputs with `CovC` in place of `FlowCov`**: `ProxyGenLimN.FlowApproxInputsN` with its
clause `FlowCov Wf cf` replaced by `CovC (CRen N (zFix N zri zwe) μ)`.
DERIVED: `2` the least colour count; `0` the lower end of the observer's scale; `12` the bound of the
block-step flow. -/
def FlowCovInputsN (N : ℕ) (hN2 : 2 ≤ N) : Prop :=
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
      ∧ ApproxK (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
          (mixKG hN2 (sunFam hN2 c hc0 hc s₀) (CRen N (ZCanon.zFix N zri zwe) μ) r)
          (gramF hN2 (sunFam hN2 c hc0 hc s₀) r)
      ∧ (∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (ne_zero_of_two_le hN2) ℓ)
      ∧ WDeltaRun.RunSeed N

/-- **`FlowApproxInputsN` gives `FlowCovInputsN`** (`FlowChoice.covC_of_flowCov_choice`). DERIVED: `2`
the least colour count. -/
theorem flowCovInputsN_of_approx (hN2 : 2 ≤ N) (h : FlowApproxInputsN N hN2) :
    FlowCovInputsN N hN2 := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP, hA, h3,
    hfar⟩ := h
  exact ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC,
    covC_of_flowCov_choice S.b_pos S.scale hE hV, hW, hP, hA, h3, hfar⟩

/-- **`ClayStatementDy` from `FlowCovInputsN` at every `N ≥ 2`** (`SUNBest.clayStatement_of_inputs`).
DERIVED: `2` the least colour count. -/
theorem clayStatement_of_covC (h : ∀ (N : ℕ) (hN2 : 2 ≤ N), FlowCovInputsN N hN2) :
    MassGap.ClayStatementDy :=
  SUNBest.clayStatement_of_inputs fun N hN2 => by
    haveI : NeZero N := ⟨by omega⟩
    obtain ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP, hA, h3,
      hfar⟩ := h N hN2
    obtain ⟨t, C, G, I⟩ := inputsAt_of_covC hN2 hc0 hc hs0 hr hri hwe S hE hC hV hW hP hA h3 hfar
    exact ⟨sunFam hN2 c hc0 hc s₀, r, t, |C|, zri, zwe, μ, G, I⟩

end MassGap.FlowCovN

end

#print axioms MassGap.FlowCovN.covC_apply
#print axioms MassGap.FlowCovN.flowCovAt_of_covC_remCovAt
#print axioms MassGap.FlowCovN.remCovAt_of_covC_flowCovAt
#print axioms MassGap.FlowCovN.covC_of_flowCovAt_remCovAt
#print axioms MassGap.FlowCovN.flowCov_iff_remCov_of_covC
#print axioms MassGap.FlowCovN.flowCov_iff_covC_and_remCov
#print axioms MassGap.FlowCovN.abs_sub_limUnder_le
#print axioms MassGap.FlowCovN.eventually_rate
#print axioms MassGap.FlowCovN.flowCovLim_of_covC
#print axioms MassGap.FlowCovN.covC_of_flowCovLim
#print axioms MassGap.FlowCovN.flowCovLim_iff_covC
#print axioms MassGap.FlowCovN.flowCovLim_iff_covC_of_choice
#print axioms MassGap.FlowCovN.flowCovLim_of_flowCov
#print axioms MassGap.FlowCovN.inputsAt_of_covC
#print axioms MassGap.FlowCovN.flowCovInputsN_of_approx
#print axioms MassGap.FlowCovN.clayStatement_of_covC
