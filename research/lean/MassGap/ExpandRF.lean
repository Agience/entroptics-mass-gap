import Mathlib
import MassGap.ObserverGen

/-!
# MassGap.ExpandRF — the expansion clause with per-composite constants

`CompositesRenAll.ExpandR Wf cf z μ` fixes one ratio `θ`, one rate `ε` and one constant `K_r` for every
family of composites: `|latC F − msLat_s F| ≤ K_r^{#F} (s/d)^ε ∏ᵢ d^{−κ_r(iᵢ)} ‖fᵢ‖₁`. The index set `Ix0`
holds composites of every dimension. This module reads every consumer of `ExpandR` on the path of
`InputMerge.clayStatement_of_narrowAtMin` and its observer forms (`ObserverBundle`, `ObserverGen`), states
the clause with the constant per composite (`ExpandRF`), re-proves every consumer from it, and states the
bundle `NarrowInputsAtMinF` with its capstone. Declarations are in the namespace `MassGap.ExpandFam`.

## 1. What each consumer reads (proved, by the proofs below)

* **One family at a time.** `boundC_of_finMom`, `os1C_of_finMom`, `tendsto_obsLim` (`contC_eq_obsLimC`,
  `contT_rhoD_eq_obs`), `FlowCovN.eventually_rate` (`covC_of_flowCovLim`, `flowCovLim_of_covC`),
  `NondegFromProxy.latRead_sub_proxRead_le` (`compNondeg_of_proxy`, `proxyNondeg_of_compNondeg`),
  `WardFromLattice.latT_smallFlow` (`wardT_iff_flowWard`, `ObserverBundle.contT_eq_iff_flowNear`,
  `af_iff_flowAF`, `obsLower_iff_flowThree`) and `ObserverGen.kernC_diag_flowedN`
  (`generation_iff_flowGen`) each fix one admissible family, or finitely many built from it (its
  translate; its rotation and the relabellings `σ` over the support of `repF R`; the pairs over the
  support of `c`; the tensor components `α : ι → Idx4`; the reflected pair `ΘP ∪ P`), and read only that
  the remainder tends to `0` as `s → 0⁺`, eventually in the step. That is `ExpandLim`: for every admissible
  family and `η > 0`, for all small `s > 0`, eventually in the step, `|latC F − msLat_s F| ≤ η`. No rate,
  no ratio, no constant is read. The `L`-suffixed theorems below re-prove each from `ExpandLim`.
* **Uniformly over families: `ClusterRoute.os0C_of_cluster` only.** It reads the clause at the one scale
  `s = θ' d`, `θ' = min(θ, θc, 1)`, for every `n` and every `d`-separated family, `0 < d ≤ 1`. There
  `K_r^n ≤ ∏ᵢ |K_r|` enters `OS0C`'s per-composite constant `Ccᵢ = Kcᵢ θ'^{−λᵢ} + |K_r|`, and `ε` enters
  only `α = 1 + θ'^ε ≤ 2`. So a constant `K_r(i)` per composite is absorbed into `Ccᵢ` the way `ScalePC`
  absorbed per-channel constants, and a factor `n!` is absorbed by `OS0C`'s `(n!)^β`, `β = 1`
  (`os0C_of_clusterF`).

## 2. The clause

* `ExpandRF Wf cf z μ`: one `θ > 0`, one `ε > 0`, and per composite `K_r(i)`, `κ_r(i)`, with
  `|latC F − msLat_s F| ≤ (s/d)^ε · #F! · ∏ᵢ K_r(iᵢ) d^{−κ_r(iᵢ)} ‖fᵢ‖₁` for `0 < s ≤ θ d`.
* `expandRF_of_expandR`: `ExpandR → ExpandRF` (`K_r(i) = |K_r|`, `K_r^n ≤ n! |K_r|^n`).
* `expandLim_of_expandRF`: `ExpandRF → ExpandLim`.

## 3. The consumers re-proved

* From `ExpandLim`: `boundC_of_finMomL`, `convC_of_finMomL`, `os1C_of_finMomL`, `tendsto_obsLimL`,
  `contC_eq_obsLimCL`, `eventually_rateL`, `flowCovLim_of_covCL`, `covC_of_flowCovLimL`,
  `flowCovLim_iff_covCL`, `latRead_sub_proxRead_small`, `compNondeg_of_proxyL`,
  `proxyNondeg_of_compNondegL`, `proxyNondeg_iffL`, `latT_smallFlowL`, `sepConv_of_finMomL`,
  `contT_eq_iff_flowNearL`, `af_iff_flowAFL`, `obsLower_iff_flowThreeL`, `threePoint_iff_flowThreeL`,
  `wardT_of_flowWardL`, `flowWard_of_wardTL`, `wardT_iff_flowWardL`, `kernC_diag_flowedNL`,
  `generation_iff_flowGenL`.
* From `ExpandRF`: `os0C_of_clusterF` (`α = 1 + θ'^ε`, `γ_OS = max(e γ, 1)`, `β = 1`,
  `Ccᵢ = Kcᵢ θ'^{−λᵢ} + |K_r(i)|`, `κᵢ = max(λᵢ, κ_r(i))`).

## 4. The bundles

* `compOS_of_minF`, `approxK_of_beyond_minF`; `NarrowInputsAtMinF N hN2 W r` is
  `InputMerge.NarrowInputsAtMin` with `ExpandRF` in place of `ExpandR`.
  **`clayStatement_of_narrowAtMinF`**: `∃ W r, NarrowInputsAtMinF N hN2 W r` at every `N ≥ 2` gives
  `MassGap.ClayStatementDy`. **`narrowInputsAtMinF_of_min`**: `NarrowInputsAtMin` gives `NarrowInputsAtMinF`.
* `NarrowInputsAtObsF`: `ObserverBundle.NarrowInputsAtObs` with `ExpandRF`. `narrowInputsAtObsF_iff_minF`,
  `clayStatement_of_narrowAtObsF`, `narrowInputsAtObsF_of_obs`.

## 5. Why `θ` stays one number, and the free field (argued; no declaration)

* **`θ` per family is not absorbed.** At scale `s` the cluster bound gives the factor `∏ᵢ Kcᵢ s^{−λᵢ}`.
  With a ratio `θ_F` per family the scale is `s = θ_F d` and each factor carries `θ_F^{−λᵢ}`: the
  family's ratio raised to every factor's exponent. If `θ_F → 0` along families of growing composites, no
  constant per composite bounds `∏ᵢ θ_F^{−λᵢ}` against `γⁿ n!`. So `OS0C` by this route needs one `θ`;
  the other consumers do not (`ExpandLim` has none).
* **The free field meets `ExpandRF`.** For the leading proxy of `∂ⁿφ` the relative remainder is about
  `min(1, (n s/d)²) ≤ n² (s/d)²`, for every `θ`. With `ε = 2`, `K_r(i) = 1 + n_i²` (so that
  `∑ᵢ n_i² ≤ ∏ᵢ (1 + n_i²)` on a family) and the reading itself bounded as in `OS0C` (`γ^m m! ∏ᵢ Cᵢ`, the
  `m!` and `γ^m` absorbed by `#F!` and `K_r`), the absolute remainder fits `ExpandRF`. With one `K_r` it
  fails once `n² > K_r`, which is the defect `ExpandRF` removes.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `1` the margin `c + 1`, the floor of `γ_OS`, `β` and the top of `θ'`; `2` the halves
and the least colour count; `3`, `4` the splits of the tolerance; `16` as in `NonGaussLink.latT_trace_rhoD`;
`0` the limit point, the plane and the signs.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ExpandFam

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
  MassGap.ClayRunSeed MassGap.InputMerge MassGap.ObserverRunSeed MassGap.ObserverBundle
  MassGap.ObserverGen
open MassGap.WardFromLattice (msT SmallFlow eq_neg_of_smallFlow flowSum_of_eq_neg FlowWard)
open MassGap.ScaleControlFull (zOne)

variable {N : ℕ}

/-! ## 1. The clauses -/

/-- **The expansion of the renormalised composites with per-composite constants**: one ratio `θ`, one
rate `ε`, and per composite `K_r(i)`, `κ_r(i)`; the remainder of a family `F` at scale `s ≤ θ d` is at most
`(s/d)^ε · #F! · ∏ᵢ K_r(iᵢ) d^{−κ_r(iᵢ)} ‖fᵢ‖₁`. Module docstring, §2. DERIVED: no numeral. -/
def ExpandRF [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) (z : Chan → ℕ → ℝ)
    (μ : OffMix) : Prop :=
  ∃ (θ ε : ℝ) (Kr κr : Ix0 → ℝ), 0 < θ ∧ 0 < ε ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → CDatum (CRen N z μ)) (d : ℝ), 0 < d →
      ContD F → SepD d F → ∀ s : ℝ, 0 < s → s ≤ θ * d → ∀ᶠ k in atTop,
        |latC (NeZero.ne N) (CRen N z μ) k F - msLat Wf c k s F|
          ≤ (s / d) ^ ε * ((Fintype.card ι).factorial : ℝ)
            * ∏ i, (Kr (F i).1 * ((d ^ κr (F i).1)⁻¹ * l1 (F i).2))

/-- **The expansion one family at a time**: for every admissible family and `η > 0`, for all small
`s > 0`, eventually in the step, `|latC F − msLat_s F| ≤ η`. Module docstring, §1.
DERIVED: `0` the limit point. -/
def ExpandLim [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) (z : Chan → ℕ → ℝ)
    (μ : OffMix) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → CDatum (CRen N z μ)), Adm F →
    ∀ η : ℝ, 0 < η → ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in atTop,
      |latC (NeZero.ne N) (CRen N z μ) k F - msLat Wf c k s F| ≤ η

/-- **`ExpandR` gives `ExpandRF`** with `K_r(i) = |K_r|`: `K_r^n ≤ n! |K_r|^n`. DERIVED: `1` the floor
of `n!`. -/
theorem expandRF_of_expandR [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (h : ExpandR Wf c z μ) : ExpandRF Wf c z μ := by
  obtain ⟨θ, ε, Kr, κr, hθ, hε, hE⟩ := h
  refine ⟨θ, ε, fun _ => |Kr|, κr, hθ, hε, fun ι _ _ F d hd hc hsep s hs hsd => ?_⟩
  filter_upwards [hE ι F d hd hc hsep s hs hsd] with k hk
  refine hk.trans ?_
  have hx : 0 ≤ ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2) :=
    Finset.prod_nonneg fun i _ => mul_nonneg (inv_nonneg.mpr (Real.rpow_nonneg hd.le _))
      (MeasureTheory.integral_nonneg fun x => abs_nonneg _)
  have hsε : 0 ≤ (s / d) ^ ε := Real.rpow_nonneg (div_nonneg hs.le hd.le) _
  have hf1 : (1 : ℝ) ≤ ((Fintype.card ι).factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hK : Kr ^ Fintype.card ι ≤ ((Fintype.card ι).factorial : ℝ) * |Kr| ^ Fintype.card ι :=
    (le_abs_self _).trans ((abs_pow Kr _).le.trans
      (le_mul_of_one_le_left (pow_nonneg (abs_nonneg _) _) hf1))
  have e : ∏ i, (|Kr| * ((d ^ κr (F i).1)⁻¹ * l1 (F i).2))
      = |Kr| ^ Fintype.card ι * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [e]
  calc Kr ^ Fintype.card ι * (s / d) ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)
      = (s / d) ^ ε * (Kr ^ Fintype.card ι * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)) := by ring
    _ ≤ (s / d) ^ ε * (((Fintype.card ι).factorial : ℝ) * |Kr| ^ Fintype.card ι
          * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK hx) hsε
    _ = _ := by ring

/-- **`ExpandRF` gives `ExpandLim`.** DERIVED: `0` the limit point. -/
theorem expandLim_of_expandRF [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (h : ExpandRF Wf c z μ) : ExpandLim Wf c z μ := by
  obtain ⟨θ, ε, Kr, κr, hθ, hε, hE⟩ := h
  intro ι _ _ F hF η hη
  obtain ⟨hcont, d, hd, hsep⟩ := hF
  set A : ℝ := ((Fintype.card ι).factorial : ℝ)
    * ∏ i, (Kr (F i).1 * ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)) with hA
  filter_upwards [eventually_rate_lt (d := d) hε |A| hη,
    (gt_mem_nhds (mul_pos hθ hd)).filter_mono nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin.mono fun s hs => hs] with s hs1 hs2 hs3
  have hs0 : (0 : ℝ) < s := hs3
  filter_upwards [hE ι F d hd hcont hsep s hs0 hs2.le] with k hk
  have hx : 0 ≤ (s / d) ^ ε := Real.rpow_nonneg (div_nonneg hs0.le hd.le) _
  calc |latC (NeZero.ne N) (CRen N z μ) k F - msLat Wf c k s F|
      ≤ (s / d) ^ ε * ((Fintype.card ι).factorial : ℝ)
          * ∏ i, (Kr (F i).1 * ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)) := hk
    _ = A * (s / d) ^ ε := by rw [hA]; ring
    _ ≤ |A| * (s / d) ^ ε := mul_le_mul_of_nonneg_right (le_abs_self _) hx
    _ ≤ η := hs1.le

/-- `c · (η / (c + 1)) ≤ η` for `c, η ≥ 0`. DERIVED: `1` the margin. -/
theorem mul_div_succ_le {c η : ℝ} (hc : 0 ≤ c) (hη : 0 ≤ η) : c * (η / (c + 1)) ≤ η := by
  rw [← mul_div_assoc, div_le_iff₀ (by linarith : (0 : ℝ) < c + 1)]
  nlinarith

/-! ## 2. `ConvC`, `OS1C` and the observer's double limit from `ExpandLim` -/

/-- **`BoundC (CRen N z μ)` from `FinMom` and `ExpandLim`**: at one scale `s ∈ (0, b)` with remainder at
most `1`. DERIVED: `1` the remainder bound and the spacing bound; `0` the log exponents. -/
theorem boundC_of_finMomL [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hm : FinMom b Wf)
    (hL : ExpandLim Wf c z μ) : InputsTriage.BoundC (NeZero.ne N) (CRen N z μ) := by
  classical
  intro ι _ _ F hF
  obtain ⟨s, hrem, hsI⟩ := ((hL ι F hF 1 one_pos).and
    (Ioo_mem_nhdsGT hb : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Set.Ioo 0 b)).exists
  obtain ⟨r, t, K, ht, hK1, hev⟩ := chanPM_local hm (0 : Ix0 → ℝ) 0
    (Finset.univ.biUnion fun i => (c (F i).1 s).support) hsI.1 hsI.2.le (Fintype.card ι)
  refine ⟨(1 + Fintype.card ι * (((2 * Fintype.card ι).factorial : ℝ) ^ r * K))
      * ∏ i, (msTsize (F i).2 * msPsize t (0 : Ix0 → ℝ) 0 c s (F i).1) + 1, ?_⟩
  refine Filter.Eventually.filter_mono ultra_le ?_
  filter_upwards [hev, hrem, (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)] with k hk hr hk1
  have hP := abs_msLat_le_on_pm Wf c ht hsI.1 hk1.le F hK1 (fun i j hj =>
    hk j (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hj⟩))
  have htri := abs_sub_abs_le_abs_sub (latC (NeZero.ne N) (CRen N z μ) k F) (msLat Wf c k s F)
  linarith

/-- **`ConvC (CRen N z μ)` from `FinMom` and `ExpandLim`.** DERIVED: no numeral. -/
theorem convC_of_finMomL [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hm : FinMom b Wf)
    (hL : ExpandLim Wf c z μ) : ConvC (NeZero.ne N) (CRen N z μ) :=
  (InputsTriage.convC_iff_boundC _ _).2 (boundC_of_finMomL hb hm hL)

/-- **`OS1C (CRen N z μ)` from `FinMom` and `ExpandLim`** (`InputMerge.os1C_of_finMom`'s proof, one scale
per tolerance). DERIVED: `3` the split of the tolerance; `0` the limit and the log exponents. -/
theorem os1C_of_finMomL [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hm : FinMom b Wf)
    (hL : ExpandLim Wf c z μ) : OS1C (NeZero.ne N) (CRen N z μ) := by
  classical
  have hconv : ConvC (NeZero.ne N) (CRen N z μ) := convC_of_finMomL hb hm hL
  intro ι _ _ F hF v
  obtain ⟨hcont, d, hd, hsep⟩ := hF
  have hFv : Adm (fun i => translateD v (F i)) :=
    ⟨fun i => (hcont i).comp (continuous_id.sub continuous_const), d, hd,
      fun i j hij => ContinuumSep.sepBy_translate (hsep i j hij) v⟩
  have hΔ : Tendsto (fun k => latC (NeZero.ne N) (CRen N z μ) k (fun i => translateD v (F i))
      - latC (NeZero.ne N) (CRen N z μ) k F) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    have h3 : (0 : ℝ) < η / 3 := by positivity
    obtain ⟨s, h1, h2, hsI⟩ := ((hL ι F ⟨hcont, d, hd, hsep⟩ (η / 3) h3).and
      ((hL ι _ hFv (η / 3) h3).and
        (Ioo_mem_nhdsGT hb : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Set.Ioo 0 b))).exists
    obtain ⟨r, t, K, ht, hK1, hevU⟩ := chanPM_local hm (0 : Ix0 → ℝ) 0
      (Finset.univ.biUnion fun i => (c (F i).1 s).support) hsI.1 hsI.2.le (Fintype.card ι)
    have hS : ∀ᶠ k in atTop, ∀ i, ∀ j ∈ (c (F i).1 s).support,
        ScaleChanPM Wf r t K (0 : Ix0 → ℝ) 0 k s j (Fintype.card ι) := by
      filter_upwards [hevU] with k hk i j hj
      exact hk j (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hj⟩)
    have hmid : Tendsto (fun k => msLat Wf c k s (fun i => translateD v (F i)) - msLat Wf c k s F)
        atTop (𝓝 0) := msLat_translate_sub_tendsto_pm Wf c ht hsI.1 hK1 F hS hcont v
    filter_upwards [h1, h2, (Metric.tendsto_nhds.mp hmid) (η / 3) h3] with k hk1 hk2 hk3
    rw [Real.dist_eq, sub_zero] at hk3 ⊢
    have hk2' : |latC (NeZero.ne N) (CRen N z μ) k (fun i => translateD v (F i))
        - msLat Wf c k s (fun i => translateD v (F i))| ≤ η / 3 := hk2
    have hk3' : |msLat Wf c k s (fun i => translateD v (F i)) - msLat Wf c k s F| < η / 3 := hk3
    obtain ⟨a1l, a1r⟩ := abs_le.mp hk1
    obtain ⟨a2l, a2r⟩ := abs_le.mp hk2'
    obtain ⟨a3l, a3r⟩ := abs_lt.mp hk3'
    rw [abs_lt]
    constructor <;> linarith
  have h := (hconv ι F ⟨hcont, d, hd, hsep⟩).add (hΔ.mono_left ultra_le)
  rw [add_zero] at h
  refine h.congr fun k => ?_
  ring

/-- **The flowed limits tend to the composite limit as `s → 0⁺`**, under `ExpandLim` and `ConvC`, on every
admissible family. DERIVED: `2` the halving; `0` the limit of the scale. -/
theorem tendsto_obsLimL [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hL : ExpandLim Wf cf z μ) (hC : ConvC (NeZero.ne N) (CRen N z μ))
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → CDatum (CRen N z μ)) (hF : Adm F) :
    Tendsto (fun s => limUnder (ultra : Filter ℕ) (fun k => msLat Wf cf k s F)) (𝓝[>] (0 : ℝ))
      (𝓝 (contC (NeZero.ne N) (CRen N z μ) F)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  filter_upwards [hL ι F hF (η / 2) (half_pos hη)] with s hs
  have hb := FlowCovN.abs_sub_limUnder_le (hC ι F hF) (hs.filter_mono ultra_le)
  rw [Real.dist_eq, abs_sub_comm]
  linarith

/-- **Every composite limit is the observer's double limit**, under `ExpandLim` and `ConvC`.
DERIVED: no numeral. -/
theorem contC_eq_obsLimCL [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hL : ExpandLim Wf cf z μ) (hC : ConvC (NeZero.ne N) (CRen N z μ))
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → CDatum (CRen N z μ)) (hF : Adm F) :
    contC (NeZero.ne N) (CRen N z μ) F = obsLimC Wf cf F :=
  ((tendsto_obsLimL hL hC F hF).limUnder_eq).symm

/-! ## 3. `CovC` and `CompNondeg` in observer form from `ExpandLim` -/

/-- **The two bounds of `FlowCovN.eventually_rate` from `ExpandLim`**: the rotated family and the finitely
many relabelled families, each at its own small scales. DERIVED: `2` the halving of the separation; `1` the
margin; `0` the limit of the scale. -/
theorem eventually_rateL [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hL : ExpandLim Wf cf z μ) (hCv : ConvC (NeZero.ne N) (CRen N z μ))
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
  have hRR := orth_transpose_mul hR
  obtain ⟨hcont, d, hd, hsep⟩ := hFa
  have hd2 : 0 < d / 2 := half_pos hd
  have hG : Adm (fun i => ((F i).1, rotTest R (F i).2) : ι → CDatum (CRen N z μ)) :=
    ⟨fun i => continuous_rotTest' hRR (hcont i), d / 2, hd2,
      fun i j hij => sepBy_rotTest hRR hd (hsep i j hij)⟩
  have hSa : ∀ σ : ι → Ix0, Adm (fun i => (σ i, (F i).2) : ι → CDatum (CRen N z μ)) :=
    fun σ => ⟨fun i => hcont i, d, hd, fun i j hij => hsep i j hij⟩
  set S : Finset (ι → Ix0) := Fintype.piFinset (fun i => (repF R (F i).1).support) with hSdef
  set p : (ι → Ix0) → ℝ := fun σ => ∏ i, repF R (F i).1 (σ i) with hpdef
  set c : ℝ := ∑ σ ∈ S, |p σ| with hcdef
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun σ _ => abs_nonneg _
  have hη' : 0 < η / (c + 1) := div_pos hη (by linarith)
  filter_upwards [hL ι _ hG η hη,
    (Filter.eventually_all_finset S).2 fun σ _ => hL ι _ (hSa σ) _ hη'] with s h1 h2
  refine ⟨h1.filter_mono ultra_le, ?_⟩
  have hσ : ∀ σ ∈ S, |contC (NeZero.ne N) (CRen N z μ) (fun i => (σ i, (F i).2))
      - limUnder (ultra : Filter ℕ) (fun k => msLat Wf cf k s (fun i => (σ i, (F i).2)))|
        ≤ η / (c + 1) := fun σ hσS =>
    FlowCovN.abs_sub_limUnder_le (hCv ι _ (hSa σ)) ((h2 σ hσS).filter_mono ultra_le)
  show |∑ σ ∈ S, p σ * contC (NeZero.ne N) (CRen N z μ) (fun i => (σ i, (F i).2))
      - ∑ σ ∈ S, p σ * limUnder (ultra : Filter ℕ)
          (fun k => msLat Wf cf k s (fun i => (σ i, (F i).2)))| ≤ η
  rw [← Finset.sum_sub_distrib]
  calc |∑ σ ∈ S, (p σ * contC (NeZero.ne N) (CRen N z μ) (fun i => (σ i, (F i).2))
          - p σ * limUnder (ultra : Filter ℕ) (fun k => msLat Wf cf k s (fun i => (σ i, (F i).2))))|
      ≤ ∑ σ ∈ S, |p σ * contC (NeZero.ne N) (CRen N z μ) (fun i => (σ i, (F i).2))
          - p σ * limUnder (ultra : Filter ℕ) (fun k => msLat Wf cf k s (fun i => (σ i, (F i).2)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ ∈ S, |p σ| * (η / (c + 1)) := by
        refine Finset.sum_le_sum fun σ hσS => ?_
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_left (hσ σ hσS) (abs_nonneg _)
    _ = c * (η / (c + 1)) := by rw [hcdef, Finset.sum_mul]
    _ ≤ η := mul_div_succ_le hc0 hη.le

/-- **`CovC` gives `FlowCovLim`** under `ExpandLim` and `ConvC` (`FlowCovN.flowCovLim_of_covC`'s proof).
DERIVED: `3` the split of the tolerance. -/
theorem flowCovLim_of_covCL [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hL : ExpandLim Wf cf z μ) (hCv : ConvC (NeZero.ne N) (CRen N z μ))
    (hC : CovC (NeZero.ne N) (CRen N z μ)) : FlowCovLim Wf cf := by
  intro R hR ι _ _ F hFa η hη
  have h3 : (0 : ℝ) < η / 3 := by linarith
  have hT := Metric.tendsto_nhds.1 (covC_apply hC hR F hFa) (η / 3) h3
  filter_upwards [eventually_rateL hL hCv hR F hFa h3] with s ⟨h1, h2⟩
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

/-- **`FlowCovLim` gives `CovC`** under `ExpandLim` and `ConvC` (`FlowCovN.covC_of_flowCovLim`'s proof).
DERIVED: `4` the split of the tolerance. -/
theorem covC_of_flowCovLimL [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hL : ExpandLim Wf cf z μ) (hCv : ConvC (NeZero.ne N) (CRen N z μ))
    (hV : FlowCovLim Wf cf) : CovC (NeZero.ne N) (CRen N z μ) := by
  intro R hR ι _ _ F hFa
  show Tendsto (fun k => latC (NeZero.ne N) (CRen N z μ) k (fun i => ((F i).1, rotTest R (F i).2)))
    (ultra : Filter ℕ)
    (𝓝 (∑ σ ∈ Fintype.piFinset (fun i => (repF R (F i).1).support),
      (∏ i, repF R (F i).1 (σ i)) * contC (NeZero.ne N) (CRen N z μ) (fun i => (σ i, (F i).2))))
  rw [Metric.tendsto_nhds]
  intro η hη
  have h4 : (0 : ℝ) < η / 4 := by linarith
  obtain ⟨s, ⟨h1, h2⟩, h3⟩ :=
    ((eventually_rateL hL hCv hR F hFa h4).and (hV R hR ι F hFa (η / 4) h4)).exists
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

/-- **`FlowCovLim ↔ CovC`** under `ExpandLim` and `ConvC`. DERIVED: no numeral. -/
theorem flowCovLim_iff_covCL [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hL : ExpandLim Wf cf z μ)
    (hCv : ConvC (NeZero.ne N) (CRen N z μ)) :
    FlowCovLim Wf cf ↔ CovC (NeZero.ne N) (CRen N z μ) :=
  ⟨covC_of_flowCovLimL hL hCv, flowCovLim_of_covCL hL hCv⟩

/-- **The two-point remainder at small scales**: under `ExpandLim`, for every `η > 0`, for all small
`s > 0`, eventually in the step, `|latRead − proxRead_s| ≤ η` (the pairs over the support of `c`).
DERIVED: `2` the two points; `1` the margin. -/
theorem latRead_sub_proxRead_small [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hL : ExpandLim Wf cf z μ) (c : Ix0 →₀ ℝ) {f h : TestFn}
    (hf : Continuous f.1) (hh : Continuous h.1) {d : ℝ} (hd : 0 < d)
    (hfh : ContinuumSep.sepBy d f h) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in atTop,
      |latRead (N := N) z μ c f h k - proxRead Wf cf c f h k s| ≤ η := by
  set M : ℝ := ∑ i ∈ c.support, ∑ j ∈ c.support, |c i * c j| with hMdef
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hη' : 0 < η / (M + 1) := div_pos hη (by linarith)
  have hadm : ∀ i j : Ix0, Adm (pairF i j f h : Fin 2 → CDatum (CRen N z μ)) := fun i j =>
    ⟨(adm_pair hf hh hfh).1, d, hd, (adm_pair hf hh hfh).2⟩
  filter_upwards [(Filter.eventually_all_finset c.support).2 fun i _ =>
    (Filter.eventually_all_finset c.support).2 fun j _ =>
      hL (Fin 2) (pairF i j f h) (hadm i j) _ hη'] with s hs
  have hk : ∀ᶠ k in atTop, ∀ i ∈ c.support, ∀ j ∈ c.support,
      |latC (NeZero.ne N) (CRen N z μ) k (pairF i j f h) - msLat Wf cf k s (pairF i j f h)|
        ≤ η / (M + 1) :=
    (Filter.eventually_all_finset c.support).2 fun i hi =>
      (Filter.eventually_all_finset c.support).2 fun j hj => hs i hi j hj
  filter_upwards [hk] with k hk
  have e : latRead (N := N) z μ c f h k - proxRead Wf cf c f h k s
      = ∑ i ∈ c.support, ∑ j ∈ c.support, c i * c j
          * (latC (NeZero.ne N) (CRen N z μ) k (pairF i j f h) - msLat Wf cf k s (pairF i j f h)) := by
    unfold latRead proxRead
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  calc |∑ i ∈ c.support, ∑ j ∈ c.support, c i * c j
          * (latC (NeZero.ne N) (CRen N z μ) k (pairF i j f h) - msLat Wf cf k s (pairF i j f h))|
      ≤ ∑ i ∈ c.support, ∑ j ∈ c.support, |c i * c j| * (η / (M + 1)) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hk i hi j hj) (abs_nonneg _)
    _ = M * (η / (M + 1)) := by
        rw [hMdef, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
    _ ≤ η := mul_div_succ_le hM0 hη.le

/-- **`CompNondeg` from the proxies** under `ExpandLim` and `ConvC`
(`NondegFromProxy.compNondeg_of_proxy`'s proof). DERIVED: `2` the half of the lower bound; `0` the
excluded value. -/
theorem compNondeg_of_proxyL [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hL : ExpandLim Wf cf z μ) (hC : ConvC (NeZero.ne N) (CRen N z μ))
    (hP : ProxyNondeg Wf cf) : CompNondeg (NeZero.ne N) (CRen N z μ) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  intro c hon
  obtain ⟨f, h, hf, hh, ⟨d, hd, hfh⟩, δ, hδ, hfr⟩ := hP c hon
  refine ⟨f, h, hf, hh, ⟨d, hd, hfh⟩, ?_⟩
  obtain ⟨s, hs1, hs2⟩ :=
    (hfr.and_eventually (latRead_sub_proxRead_small hL c hf hh hd hfh (half_pos hδ))).exists
  have hT := tendsto_latRead hC c hf hh hd hfh
  intro h0
  change contRead (N := N) z μ c f h = 0 at h0
  rw [h0] at hT
  have hsmall : ∀ᶠ k in (ultra : Filter ℕ), |latRead (N := N) z μ c f h k| < δ / 2 := by
    filter_upwards [(Metric.tendsto_nhds.mp hT) (δ / 2) (half_pos hδ)] with k hk
    rwa [Real.dist_eq, sub_zero] at hk
  obtain ⟨k, hk1, hk2, hk3⟩ := (hsmall.and (hs1.and (hs2.filter_mono ultra_le))).exists
  have htri := abs_sub_abs_le_abs_sub (proxRead Wf cf c f h k s) (latRead (N := N) z μ c f h k)
  rw [abs_sub_comm] at htri
  linarith

/-- **The proxies from `CompNondeg`** under `ExpandLim` and `ConvC`
(`NondegFromProxy.proxyNondeg_of_compNondeg`'s proof). DERIVED: `2` the half of the lower bound; `4` its
quarters; `0` the excluded value and the limit of the scale. -/
theorem proxyNondeg_of_compNondegL [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hL : ExpandLim Wf cf z μ) (hC : ConvC (NeZero.ne N) (CRen N z μ))
    (hN : CompNondeg (NeZero.ne N) (CRen N z μ)) : ProxyNondeg Wf cf := by
  intro c hon
  obtain ⟨f, h, hf, hh, ⟨d, hd, hfh⟩, hne⟩ := hN c hon
  have hR : contRead (N := N) z μ c f h ≠ 0 := hne
  have hRp : 0 < |contRead (N := N) z μ c f h| := abs_pos.2 hR
  refine ⟨f, h, hf, hh, ⟨d, hd, hfh⟩, |contRead (N := N) z μ c f h| / 2, half_pos hRp, ?_⟩
  have hT := tendsto_latRead hC c hf hh hd hfh
  refine Filter.Eventually.frequently ?_
  filter_upwards [latRead_sub_proxRead_small hL c hf hh hd hfh
    (show (0 : ℝ) < |contRead (N := N) z μ c f h| / 4 by positivity)] with s hs
  filter_upwards [(Metric.tendsto_nhds.mp hT) (|contRead (N := N) z μ c f h| / 4) (by positivity),
    hs.filter_mono ultra_le] with k hk1 hk2
  rw [Real.dist_eq] at hk1
  have t1 := abs_sub_abs_le_abs_sub (contRead (N := N) z μ c f h) (latRead (N := N) z μ c f h k)
  have t2 := abs_sub_abs_le_abs_sub (latRead (N := N) z μ c f h k) (proxRead Wf cf c f h k s)
  rw [abs_sub_comm] at t1
  linarith

/-- **`ProxyNondeg ↔ CompNondeg`** under `ExpandLim` and `ConvC`. DERIVED: no numeral. -/
theorem proxyNondeg_iffL [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hL : ExpandLim Wf cf z μ) (hC : ConvC (NeZero.ne N) (CRen N z μ)) :
    ProxyNondeg Wf cf ↔ CompNondeg (NeZero.ne N) (CRen N z μ) :=
  ⟨compNondeg_of_proxyL hL hC, proxyNondeg_of_compNondegL hL hC⟩

/-! ## 4. `OS0C` from `ExpandRF` -/

/-- **`OS0C (CRen N z μ)` from `ConvC`, `ExpandRF` and the cluster input**, with `β = 1`:
`α = 1 + θ'^ε`, `γ_OS = max(e γ, 1)`, `Ccᵢ = Kcᵢ θ'^{−λᵢ} + |K_r(i)|`, `κᵢ = max(λᵢ, κ_r(i))`,
`θ' = min(θ, θc, 1)` (`ClusterRoute.os0C_of_cluster`'s proof; the remainder's `n!` is the cluster bound's).
DERIVED: `1` the exponent `β`, the floor of `γ_OS` and the top of `θ'`. -/
theorem os0C_of_clusterF [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hconv : ConvC (NeZero.ne N) (CRen N z μ))
    (hex : ExpandRF Wf c z μ) (hcl : ClusterPM Wf c) : OS0C (NeZero.ne N) (CRen N z μ) := by
  obtain ⟨θc, γ, Kc, lam, hθc, hγ, hKc, hC⟩ := hcl
  obtain ⟨θ, ε, Kr, κr, hθ, hε, hE⟩ := hex
  set θ' : ℝ := min θ (min θc 1) with hθ'def
  have hθ'0 : 0 < θ' := lt_min hθ (lt_min hθc one_pos)
  have hθ'θ : θ' ≤ θ := min_le_left _ _
  have hθ'c : θ' ≤ θc := (min_le_right _ _).trans (min_le_left _ _)
  set Γ : ℝ := max (Real.exp 1 * γ) 1 with hΓdef
  refine ⟨1 + θ' ^ ε, Γ, 1, fun i => Kc i * θ'⁻¹ ^ lam i + |Kr i|, fun i => max (lam i) (κr i), ?_⟩
  intro n F d hd hd1 hcont hsep
  beta_reduce
  have hs : 0 < θ' * d := mul_pos hθ'0 hd
  have hsθ : θ' * d ≤ θ * d := mul_le_mul_of_nonneg_right hθ'θ hd.le
  have hsc : θ' * d ≤ θc * d := mul_le_mul_of_nonneg_right hθ'c hd.le
  have hA := abs_contC_le_cl hs F ⟨hcont, d, hd, hsep⟩ hγ Kc lam hKc
    (hC n F d hd hd1 hcont hsep (θ' * d) hs hsc) hconv
    (hE (Fin n) F d hd hcont hsep (θ' * d) hs hsθ)
  have hsd : θ' * d / d = θ' := mul_div_cancel_right₀ θ' hd.ne'
  rw [Fintype.card_fin, hsd] at hA
  have hl1 : ∀ i, 0 ≤ l1 (F i).2 := fun i => MeasureTheory.integral_nonneg fun x => abs_nonneg _
  have hx : ∀ i, 0 ≤ (d ^ κr (F i).1)⁻¹ * l1 (F i).2 := fun i =>
    mul_nonneg (inv_nonneg.mpr (Real.rpow_nonneg hd.le _)) (hl1 i)
  have hfac : ∀ i, l1 (F i).2 * (Kc (F i).1 * (θ' * d)⁻¹ ^ lam (F i).1)
      ≤ (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr (F i).1|)
        * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2
      ∧ |Kr (F i).1| * ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)
      ≤ (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr (F i).1|)
        * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2 := fun i =>
    os0_factor_le (hl1 i) (hKc _) hθ'0 hd hd1 rfl le_rfl
  have hθε : 0 ≤ θ' ^ ε := Real.rpow_nonneg hθ'0.le _
  have hZ0 : 0 ≤ ∏ i, (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr (F i).1|)
        * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2 :=
    Finset.prod_nonneg fun i _ => (mul_nonneg (abs_nonneg _) (hx i)).trans (hfac i).2
  have hF0 : ∀ i, 0 ≤ l1 (F i).2 * (Kc (F i).1 * (θ' * d)⁻¹ ^ lam (F i).1) := fun i =>
    mul_nonneg (hl1 i) (mul_nonneg (hKc _).le (Real.rpow_nonneg (inv_nonneg.mpr hs.le) _))
  have hPi1 : ∏ i, (l1 (F i).2 * (Kc (F i).1 * (θ' * d)⁻¹ ^ lam (F i).1))
      ≤ ∏ i, (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr (F i).1|)
        * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2 :=
    Finset.prod_le_prod (fun i _ => hF0 i) (fun i _ => (hfac i).1)
  have hPi10 : 0 ≤ ∏ i, (l1 (F i).2 * (Kc (F i).1 * (θ' * d)⁻¹ ^ lam (F i).1)) :=
    Finset.prod_nonneg fun i _ => hF0 i
  have hPi2 : ∏ i, (Kr (F i).1 * ((d ^ κr (F i).1)⁻¹ * l1 (F i).2))
      ≤ ∏ i, (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr (F i).1|)
        * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2 := by
    refine (le_abs_self _).trans ?_
    rw [Finset.abs_prod]
    refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => ?_)
    rw [abs_mul, abs_of_nonneg (hx i)]
    exact (hfac i).2
  have hM : (Real.exp 1 * γ) ^ n * (n.factorial : ℝ) ≤ Γ ^ n * (n.factorial : ℝ) :=
    mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (mul_nonneg (Real.exp_pos 1).le hγ) (le_max_left _ _) n) (Nat.cast_nonneg _)
  have hΓ1 : (1 : ℝ) ≤ Γ ^ n := one_le_pow₀ (le_max_right _ _)
  have hM0 : 0 ≤ Γ ^ n * (n.factorial : ℝ) :=
    mul_nonneg (zero_le_one.trans hΓ1) (Nat.cast_nonneg _)
  have hT1 := mul_le_mul hM hPi1 hPi10 hM0
  have hT2 : θ' ^ ε * (n.factorial : ℝ) * ∏ i, (Kr (F i).1 * ((d ^ κr (F i).1)⁻¹ * l1 (F i).2))
      ≤ θ' ^ ε * (Γ ^ n * (n.factorial : ℝ) * ∏ i, (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr (F i).1|)
        * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2) := by
    have hf0 : (0 : ℝ) ≤ (n.factorial : ℝ) := Nat.cast_nonneg _
    have h1 : θ' ^ ε * (n.factorial : ℝ) * ∏ i, (Kr (F i).1 * ((d ^ κr (F i).1)⁻¹ * l1 (F i).2))
        ≤ θ' ^ ε * (n.factorial : ℝ) * ∏ i, (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr (F i).1|)
          * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2 :=
      mul_le_mul_of_nonneg_left hPi2 (mul_nonneg hθε hf0)
    have h2 : 0 ≤ θ' ^ ε * (n.factorial : ℝ) * ∏ i, (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr (F i).1|)
          * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2 :=
      mul_nonneg (mul_nonneg hθε hf0) hZ0
    refine h1.trans ?_
    calc θ' ^ ε * (n.factorial : ℝ) * ∏ i, (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr (F i).1|)
          * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2
        = 1 * (θ' ^ ε * (n.factorial : ℝ) * ∏ i, (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr (F i).1|)
          * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2) := (one_mul _).symm
      _ ≤ Γ ^ n * (θ' ^ ε * (n.factorial : ℝ) * ∏ i, (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr (F i).1|)
          * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2) :=
        mul_le_mul_of_nonneg_right hΓ1 h2
      _ = θ' ^ ε * (Γ ^ n * (n.factorial : ℝ) * ∏ i, (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr (F i).1|)
          * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2) := by ring
  rw [Real.rpow_one]
  calc |contC (NeZero.ne N) (CRen N z μ) F| ≤ _ := hA
    _ ≤ Γ ^ n * (n.factorial : ℝ) * ∏ i, (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr (F i).1|)
          * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2
        + θ' ^ ε * (Γ ^ n * (n.factorial : ℝ) * ∏ i, (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr (F i).1|)
          * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2) := add_le_add hT1 hT2
    _ = (1 + θ' ^ ε) * Γ ^ n * (n.factorial : ℝ) * ∏ i, (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr (F i).1|)
          * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2 := by ring

/-! ## 5. The shrunk bundle with `ExpandRF` -/

/-- **`CompOS (CRen N z μ)` from the shrunk core, `ExpandRF`, `ClusterPM` and the observer forms of `CovC`
and `CompNondeg`** (`InputMerge.compOS_of_min` with every consumer re-proved). DERIVED: no numeral. -/
theorem compOS_of_minF [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (S : SubstrateCoreMin W z b Wf)
    (hE : ExpandRF Wf cf z μ) (hcl : ClusterPM Wf cf) (hV : FlowCovLim Wf cf) (hP : ProxyNondeg Wf cf) :
    CompOS (NeZero.ne N) (CRen N z μ) :=
  have hL : ExpandLim Wf cf z μ := expandLim_of_expandRF hE
  have hC : ConvC (NeZero.ne N) (CRen N z μ) := convC_of_finMomL S.b_pos S.mom hL
  ⟨hC, os0C_of_clusterF hC hE hcl, os1C_of_finMomL S.b_pos S.mom hL, covC_of_flowCovLimL hL hC hV,
    compNondeg_of_proxyL hL hC hP⟩

/-- **`ApproxK` from the generation clause beyond `r`** at the shrunk inputs with `ExpandRF`
(`InputMerge.approxK_of_beyond_min`'s proof). DERIVED: `2` the least colour count; `0` the plane and the
reference step. -/
theorem approxK_of_beyond_minF (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ}
    {μ : OffMix} {b r : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCoreMin W z b Wf) (hE : ExpandRF Wf cf z μ) (hcl : ClusterPM Wf cf)
    (hV : FlowCovLim Wf cf) (hP : ProxyNondeg Wf cf) (hphys : (Φ0 W).PhysRange r)
    (hB : ∀ P, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N z μ) 0)
      (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) P) :
    ApproxK (kernC (NeZero.ne N) (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) := by
  obtain ⟨t, C, ht, hS⟩ := uv_of_plaq S.b_pos S.top S.plaq
  have hU := ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) W ht hS
  have hCO := compOS_of_minF S hE hcl hV hP
  let D := capData hN2 W hU hphys (CRen N z μ)
    (unifLocal_buildRen (rhoD (fR N) z) (bareD (fR N) (bR N)) μ) (reflCovLat_CRen z μ) hCO
  refine approxK_iff_forall.2 fun P => ?_
  obtain ⟨n, hn⟩ := exists_beyond_iterate (NeZero.ne N) r P
  exact approxKAt_of_iterate D 0 n P (hB _ hn)

/-- **The per-`N` inputs with per-composite expansion constants**: `InputMerge.NarrowInputsAtMin` with
`ExpandRF` in place of `ExpandR`. DERIVED: `2` the least colour count; `0` the plane and the reference
step. -/
def NarrowInputsAtMinF (N : ℕ) (hN2 : 2 ≤ N) (W : ConfFlow N) (r : ℝ) : Prop :=
  haveI : NeZero N := ⟨by omega⟩
  (Φ0 W).PhysRange r ∧
  ∃ (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)),
    SubstrateCoreMin W (ZCanon.zFix N zri zwe) b Wf
      ∧ ExpandRF Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ ClusterPM Wf cf
      ∧ FlowCovLim Wf cf
      ∧ WardT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe))
      ∧ ProxyNondeg Wf cf
      ∧ (∀ P, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
          (mixKG hN2 W (CRen N (ZCanon.zFix N zri zwe) μ) r) (gramF hN2 W r) P)
      ∧ (∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (ne_zero_of_two_le hN2) ℓ)
      ∧ WDeltaRun.RunSeed N

/-- **`NarrowInputsAtMinF` gives the general-`N` bundle at `W`** (`InputMerge.clayInputsN_of_narrowAtMin`'s
proof with `compOS_of_minF`, `approxK_of_beyond_minF`). DERIVED: `2` the least colour count. -/
theorem clayInputsN_of_narrowAtMinF (hN2 : 2 ≤ N) {W : ConfFlow N} {r : ℝ}
    (h : NarrowInputsAtMinF N hN2 W r) : SUNBest.ClayInputsN N hN2 := by
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
      comp := compOS_of_minF S hE hcl hV hP
      approx := approxK_of_beyond_minF hN2 S hE hcl hV hP hphys hB }⟩

/-- **`ClayStatementDy` from `NarrowInputsAtMinF` at some observer and margin, at every `N ≥ 2`**
(`SUNBest.clayStatement_of_inputs`). DERIVED: `2` the least colour count. -/
theorem clayStatement_of_narrowAtMinF
    (h : ∀ (N : ℕ) (hN2 : 2 ≤ N), ∃ (W : ConfFlow N) (r : ℝ), NarrowInputsAtMinF N hN2 W r) :
    MassGap.ClayStatementDy :=
  SUNBest.clayStatement_of_inputs fun N hN2 => by
    obtain ⟨W, r, hA⟩ := h N hN2
    exact clayInputsN_of_narrowAtMinF hN2 hA

/-- **`NarrowInputsAtMin` gives `NarrowInputsAtMinF`** at the same `W`, `r` (`expandRF_of_expandR`).
DERIVED: `2` the least colour count. -/
theorem narrowInputsAtMinF_of_min (hN2 : 2 ≤ N) {W : ConfFlow N} {r : ℝ}
    (h : NarrowInputsAtMin N hN2 W r) : NarrowInputsAtMinF N hN2 W r := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hcl, hV, hW, hP, hB, h3, hRS⟩ := h
  exact ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, expandRF_of_expandR hE, hcl, hV, hW, hP, hB, h3,
    hRS⟩

/-! ## 6. The observer forms from `ExpandLim` -/

/-- `SmallFlow` is preserved by a constant factor. DERIVED: `1` the margin. -/
theorem smallFlow_const_mul {a : ℕ → ℝ} {b : ℝ → ℕ → ℝ} (h : SmallFlow a b) (c : ℝ) :
    SmallFlow (fun k => c * a k) (fun s k => c * b s k) := by
  intro η hη
  have hη' : 0 < η / (|c| + 1) := div_pos hη (by positivity)
  filter_upwards [h _ hη'] with s hs
  filter_upwards [hs] with k hk
  show |c * a k - c * b s k| ≤ η
  rw [← mul_sub, abs_mul]
  exact (mul_le_mul_of_nonneg_left hk (abs_nonneg c)).trans (mul_div_succ_le (abs_nonneg c) hη.le)

/-- **The lattice reading of the tensor sector is its flowed reading at small flow time**, on every
admissible family, from `ExpandLim` (`WardFromLattice.latT_smallFlow` with the tensor components read one
at a time). DERIVED: no numeral. -/
theorem latT_smallFlowL [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hL : ExpandLim Wf cf z μ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : ι → TDatum) (hG : Adm G) :
    SmallFlow (fun k => latT (NeZero.ne N) (rhoD (fR N) z) k G) (fun s k => msT Wf cf k s G) := by
  obtain ⟨hc, d, hd, hsep⟩ := hG
  have hA : ∀ α : ι → Idx4, Adm (fun i => (eI (α i), (G i).2) : ι → CDatum (CRen N z μ)) :=
    fun α => ⟨fun i => hc i, d, hd, fun i j hij => hsep i j hij⟩
  have hS : SmallFlow
      (fun k => ∑ α : ι → Idx4, (∏ i, (G i).1 (α i))
        * latC (NeZero.ne N) (CRen N z μ) k (fun i => (eI (α i), (G i).2)))
      (fun s k => ∑ α : ι → Idx4, (∏ i, (G i).1 (α i))
        * msLat Wf cf k s (fun i => (eI (α i), (G i).2))) :=
    SmallFlow.sum Finset.univ fun α _ =>
      smallFlow_const_mul (fun η hη => hL ι _ (hA α) η hη) (∏ i, (G i).1 (α i))
  intro η hη
  filter_upwards [hS η hη] with s hs
  filter_upwards [hs] with k hk
  rw [CompReduce.latT_expand (NeZero.ne N) (rhoD (fR N) z) (CRen N z μ) eI
    (fun k α => buildRen_he2 _ _ μ k α) k G]
  exact hk

/-- **`SepConv` of the tensor sector from `FinMom` and `ExpandLim`** (`convC_of_finMomL`,
`CompReduce.sepConv_of_comp`). DERIVED: no numeral. -/
theorem sepConv_of_finMomL [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hm : FinMom b Wf)
    (hL : ExpandLim Wf cf z μ) : SepConv (NeZero.ne N) (rhoD (fR N) z) :=
  CompReduce.sepConv_of_comp (NeZero.ne N) (rhoD (fR N) z) (CRen N z μ) eI
    (fun k α => buildRen_he2 _ _ μ k α) (convC_of_finMomL hb hm hL)

/-- **`contT G = V ↔ FlowNear Wf cf G V`** under `SepConv` and `ExpandLim`
(`ObserverBundle.contT_eq_iff_flowNear`'s proof). DERIVED: no numeral. -/
theorem contT_eq_iff_flowNearL [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hS : SepConv (NeZero.ne N) (rhoD (fR N) z)) (hL : ExpandLim Wf cf z μ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (G : ι → TDatum) (hG : Adm G) (V : ℝ) :
    contT (NeZero.ne N) (rhoD (fR N) z) G = V ↔ FlowNear Wf cf G V := by
  have hA := latT_smallFlowL hL G hG
  have hT := hS ι G hG
  have hTB : Tendsto (fun _ : ℕ => -V) (ultra : Filter ℕ) (𝓝 (-V)) := tendsto_const_nhds
  constructor
  · intro h η hη
    have hF := flowSum_of_eq_neg hA (smallFlow_const V) hT hTB (by rw [h, neg_neg]) η hη
    filter_upwards [hF] with s hs
    filter_upwards [hs] with k hk
    simpa [sub_eq_add_neg] using hk
  · intro h
    have hW : ∀ η : ℝ, 0 < η → ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
        |msT Wf cf k s G + -V| ≤ η := by
      intro η hη
      filter_upwards [h η hη] with s hs
      filter_upwards [hs] with k hk
      simpa [sub_eq_add_neg] using hk
    have := eq_neg_of_smallFlow hA (smallFlow_const V) hW hT hTB
    rw [this, neg_neg]

/-- **`af` is `FlowAF`** under `SepConv` and `ExpandLim`. DERIVED: no numeral. -/
theorem af_iff_flowAFL [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hS : SepConv (NeZero.ne N) (rhoD (fR N) z))
    (hL : ExpandLim Wf cf z μ) :
    (∃ G : ℝ → ℝ, TwoPointKernel (NeZero.ne N) (rhoD (fR N) z) G ∧ AFCoefficient N G)
      ↔ FlowAF Wf cf := by
  constructor
  · rintro ⟨G, ⟨hGc, hK⟩, hAF⟩
    exact ⟨G, hGc, fun f g hf hg hsep =>
      (contT_eq_iff_flowNearL hS hL _ (adm_trace2 hf hg hsep) _).1 (hK f g hf hg hsep), hAF⟩
  · rintro ⟨G, hGc, hK, hAF⟩
    exact ⟨G, ⟨hGc, fun f g hf hg hsep =>
      (contT_eq_iff_flowNearL hS hL _ (adm_trace2 hf hg hsep) _).2 (hK f g hf hg hsep)⟩, hAF⟩

/-- **`ObsLower` is `FlowThreeLower`** under `ExpandLim` (`ObserverBundle.obsLower_iff_flowThree`'s
proof). DERIVED: `16`, `3` as in `NonGaussLink.latT_trace_rhoD`; `2` the halving. -/
theorem obsLower_iff_flowThreeL [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hL : ExpandLim Wf cf z μ) :
    InputsTriage.ObsLower (NeZero.ne N) z ↔ FlowThreeLower Wf cf := by
  have hq : (0 : ℝ) < ((N : ℝ) / 16) ^ 3 :=
    pow_pos (div_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))) (by norm_num)) 3
  have hlat : ∀ (a b c : TestFn) (k : ℕ),
      |latT (NeZero.ne N) (rhoD (fR N) z) k (fun i : Fin 3 => (trC, (![a, b, c] : Fin 3 → TestFn) i))|
        = ((N : ℝ) / 16) ^ 3 * |NonGaussLink.obsRead (NeZero.ne N) z k ![a, b, c]| := by
    intro a b c k
    rw [NonGaussLink.latT_trace_rhoD (NeZero.ne N) (fR N) z k ![a, b, c], abs_mul, abs_of_pos hq]
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, hsep, κ, hκ, hev⟩
    have hA := latT_smallFlowL hL _ (InputsTriage.adm_trace3 ha hb hc hsep)
    have hp : 0 < ((N : ℝ) / 16) ^ 3 * κ / 2 := by positivity
    refine ⟨a, b, c, ha, hb, hc, hsep, ((N : ℝ) / 16) ^ 3 * κ / 2, hp, ?_⟩
    filter_upwards [hA _ hp] with s hs
    filter_upwards [hs.filter_mono ultra_le, hev] with k hk1 hk2
    have h1 := hlat a b c k
    have h2 := abs_sub_abs_le_abs_sub
      (latT (NeZero.ne N) (rhoD (fR N) z) k (fun i : Fin 3 => (trC, (![a, b, c] : Fin 3 → TestFn) i)))
      (msT Wf cf k s (fun i : Fin 3 => (trC, (![a, b, c] : Fin 3 → TestFn) i)))
    have h3 : ((N : ℝ) / 16) ^ 3 * κ
        ≤ ((N : ℝ) / 16) ^ 3 * |NonGaussLink.obsRead (NeZero.ne N) z k ![a, b, c]| :=
      mul_le_mul_of_nonneg_left hk2 hq.le
    have hk1' : |latT (NeZero.ne N) (rhoD (fR N) z) k
        (fun i : Fin 3 => (trC, (![a, b, c] : Fin 3 → TestFn) i))
        - msT Wf cf k s (fun i : Fin 3 => (trC, (![a, b, c] : Fin 3 → TestFn) i))|
        ≤ ((N : ℝ) / 16) ^ 3 * κ / 2 := hk1
    linarith
  · rintro ⟨a, b, c, ha, hb, hc, hsep, κ, hκ, hev⟩
    have hA := latT_smallFlowL hL _ (InputsTriage.adm_trace3 ha hb hc hsep)
    obtain ⟨s, hs1, hs2⟩ := ((hA (κ / 2) (half_pos hκ)).and hev).exists
    refine ⟨a, b, c, ha, hb, hc, hsep, κ / 2 / ((N : ℝ) / 16) ^ 3, div_pos (half_pos hκ) hq, ?_⟩
    filter_upwards [hs1.filter_mono ultra_le, hs2] with k hk1 hk2
    have h1 := hlat a b c k
    have h2 := abs_sub_abs_le_abs_sub
      (msT Wf cf k s (fun i : Fin 3 => (trC, (![a, b, c] : Fin 3 → TestFn) i)))
      (latT (NeZero.ne N) (rhoD (fR N) z) k (fun i : Fin 3 => (trC, (![a, b, c] : Fin 3 → TestFn) i)))
    have hk1' : |latT (NeZero.ne N) (rhoD (fR N) z) k
        (fun i : Fin 3 => (trC, (![a, b, c] : Fin 3 → TestFn) i))
        - msT Wf cf k s (fun i : Fin 3 => (trC, (![a, b, c] : Fin 3 → TestFn) i))| ≤ κ / 2 := hk1
    rw [abs_sub_comm] at h2
    rw [div_le_iff₀ hq]
    linarith

/-- **`∃ ℓ > 0, ThreePointAtScale` is `FlowThreeLower`** at `z = zFix N zri zwe`, under `ExpandLim`.
DERIVED: `0` the sign of `ℓ`. -/
theorem threePoint_iff_flowThreeL [NeZero N] {zri zwe : ℕ → ℝ} {μ : OffMix} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hL : ExpandLim Wf cf (ZCanon.zFix N zri zwe) μ) :
    (∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (NeZero.ne N) ℓ) ↔ FlowThreeLower Wf cf :=
  (obsLower_zFix_iff (NeZero.ne N) zri zwe).symm.trans (obsLower_iff_flowThreeL hL)

/-- **`WardT` from the flowed Ward clause** under `SepConv` and `ExpandLim`
(`WardFromLattice.wardT_of_flowWard`'s proof). DERIVED: no numeral. -/
theorem wardT_of_flowWardL [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hS : SepConv (NeZero.ne N) (rhoD (fR N) z)) (hL : ExpandLim Wf cf z μ)
    (hW : FlowWard Wf cf) : WardT (NeZero.ne N) (rhoD (fR N) z) := by
  obtain ⟨κ, hκ⟩ := hW
  refine ⟨κ, fun ν n F I h dh df d hd hF hh hdh hFc hdf hloc => ?_⟩
  have hG := WardFromLattice.adm_stress hF hd hh hdh hloc
  have hH := WardFromLattice.adm_deriv hF hFc hdf
  exact eq_neg_of_smallFlow
    (SmallFlow.sum Finset.univ fun m _ => latT_smallFlowL hL _ (hG (stressC κ m ν) m))
    (SmallFlow.sum I fun i _ => latT_smallFlowL hL _ (hH i))
    (hκ ν n F I h dh df d hd hF hh hdh hFc hdf hloc)
    (tendsto_finsetSum _ fun m _ => hS _ _ (hG (stressC κ m ν) m))
    (tendsto_finsetSum _ fun i _ => hS _ _ (hH i))

/-- **The flowed Ward clause from `WardT`** under `SepConv` and `ExpandLim`
(`WardFromLattice.flowWard_of_wardT`'s proof). DERIVED: no numeral. -/
theorem flowWard_of_wardTL [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hS : SepConv (NeZero.ne N) (rhoD (fR N) z)) (hL : ExpandLim Wf cf z μ)
    (hW : WardT (NeZero.ne N) (rhoD (fR N) z)) : FlowWard Wf cf := by
  obtain ⟨κ, hκ⟩ := hW
  refine ⟨κ, fun ν n F I h dh df d hd hF hh hdh hFc hdf hloc => ?_⟩
  have hG := WardFromLattice.adm_stress hF hd hh hdh hloc
  have hH := WardFromLattice.adm_deriv hF hFc hdf
  exact flowSum_of_eq_neg
    (SmallFlow.sum Finset.univ fun m _ => latT_smallFlowL hL _ (hG (stressC κ m ν) m))
    (SmallFlow.sum I fun i _ => latT_smallFlowL hL _ (hH i))
    (tendsto_finsetSum _ fun m _ => hS _ _ (hG (stressC κ m ν) m))
    (tendsto_finsetSum _ fun i _ => hS _ _ (hH i))
    (hκ ν n F I h dh df d hd hF hh hdh hFc hdf hloc)

/-- **`WardT ↔ FlowWard`** under `SepConv` and `ExpandLim`. DERIVED: no numeral. -/
theorem wardT_iff_flowWardL [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hS : SepConv (NeZero.ne N) (rhoD (fR N) z))
    (hL : ExpandLim Wf cf z μ) :
    WardT (NeZero.ne N) (rhoD (fR N) z) ↔ FlowWard Wf cf :=
  ⟨flowWard_of_wardTL hS hL, wardT_of_flowWardL hS hL⟩

/-- **The diagonal is the small-scale limit of the flowed reading**, under `ExpandLim` and `ConvC`
(`ObserverGen.kernC_diag_flowedN`'s statement). DERIVED: `2` the halving of `η`; `0` the plane. -/
theorem kernC_diag_flowedNL [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hL : ExpandLim Wf cf z μ) (hC : ConvC (NeZero.ne N) (CRen N z μ))
    (P : TSepG (CRen N z μ).Ix 0) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
      |sgnC (CRen N z μ) 0 P.1 * msLat Wf cf k s (pairC (CRen N z μ) 0 P.1 P.1)
        - kernC (NeZero.ne N) (CRen N z μ) 0 P P| ≤ η := by
  have hadm := adm_pairC (CRen N z μ) P P
  set F := pairC (CRen N z μ) 0 P.1 P.1 with hF
  have hLc := hC _ F hadm
  filter_upwards [hL _ F hadm (η / 2) (half_pos hη)] with s hs
  filter_upwards [hs.filter_mono ultra_le, hLc.eventually (Metric.ball_mem_nhds _ (half_pos hη))]
    with k hk1 hk2
  show |sgnC (CRen N z μ) 0 P.1 * msLat Wf cf k s F
    - sgnC (CRen N z μ) 0 P.1 * contC (NeZero.ne N) (CRen N z μ) F| ≤ η
  rw [← mul_sub, abs_mul, ApproxFromExpand.abs_sgnC, one_mul]
  rw [Real.dist_eq] at hk2
  have htri := abs_sub_le (msLat Wf cf k s F) (latC (NeZero.ne N) (CRen N z μ) k F)
    (contC (NeZero.ne N) (CRen N z μ) F)
  rw [abs_sub_comm] at hk1
  linarith

/-- **The generation clause is `FlowGen`** under `ExpandLim` and `ConvC`
(`ObserverGen.generation_iff_flowGen`'s proof). DERIVED: `2` the halving of the tolerance. -/
theorem generation_iff_flowGenL (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} {r : ℝ} (hL : ExpandLim Wf cf z μ)
    (hC : ConvC (NeZero.ne N) (CRen N z μ)) :
    (∀ P, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N z μ) 0)
        (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) P)
      ↔ FlowGen hN2 W Wf cf z μ r := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  constructor
  · intro h
    unfold FlowGen
    intro P hP ε hε
    obtain ⟨c, hc⟩ := h P hP (ε / 2) (half_pos hε)
    refine ⟨c, ?_⟩
    filter_upwards [kernC_diag_flowedNL hL hC P (half_pos hε)] with s hs
    filter_upwards [hs] with k hk
    have := (abs_le.mp hk).2
    linarith
  · intro h P hP
    unfold ApproxKAt
    intro ε hε
    obtain ⟨c, hc⟩ := h P hP (ε / 2) (half_pos hε)
    refine ⟨c, ?_⟩
    obtain ⟨s, hs1, hs2⟩ := (hc.and (kernC_diag_flowedNL hL hC P (half_pos hε))).exists
    obtain ⟨k, hk1, hk2⟩ := (hs1.and hs2).exists
    have := (abs_le.mp hk2).1
    linarith

/-! ## 7. The observer bundle with `ExpandRF` -/

/-- **The per-`N` inputs on the observer's flow with per-composite expansion constants**:
`ObserverBundle.NarrowInputsAtObs` with `ExpandRF` in place of `ExpandR`. DERIVED: `2` the least colour
count; `0` the plane and the reference step. -/
def NarrowInputsAtObsF (N : ℕ) (hN2 : 2 ≤ N) (W : ConfFlow N) (r : ℝ) : Prop :=
  haveI : NeZero N := ⟨by omega⟩
  (Φ0 W).PhysRange r ∧
  ∃ (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)),
    ObserverCore W b Wf
      ∧ ExpandRF Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ ClusterPM Wf cf
      ∧ FlowCovLim Wf cf
      ∧ FlowAF Wf cf
      ∧ FlowWard Wf cf
      ∧ ProxyNondeg Wf cf
      ∧ (∀ P, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
          (mixKG hN2 W (CRen N (ZCanon.zFix N zri zwe) μ) r) (gramF hN2 W r) P)
      ∧ FlowThreeLower Wf cf
      ∧ ObsRunSeedW N

/-- **`NarrowInputsAtObsF` is `NarrowInputsAtMinF`** at the same `W`, `r`
(`ObserverBundle.narrowInputsAtObs_iff_min`'s proof with the `L`-forms). DERIVED: `2` the least colour
count. -/
theorem narrowInputsAtObsF_iff_minF (hN2 : 2 ≤ N) {W : ConfFlow N} {r : ℝ} :
    NarrowInputsAtObsF N hN2 W r ↔ NarrowInputsAtMinF N hN2 W r := by
  haveI : NeZero N := ⟨by omega⟩
  constructor
  · rintro ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hcl, hV, hAF, hW, hP, hB, h3, hOS⟩
    have hL := expandLim_of_expandRF hE
    have hS := sepConv_of_finMomL S.b_pos S.mom hL
    exact ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, min_of_core S ((af_iff_flowAFL hS hL).2 hAF), hE,
      hcl, hV, (wardT_iff_flowWardL hS hL).2 hW, hP, hB, (threePoint_iff_flowThreeL hL).2 h3,
      (obsRunSeedW_iff (by omega)).1 hOS⟩
  · rintro ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hcl, hV, hW, hP, hB, h3, hRS⟩
    have hL := expandLim_of_expandRF hE
    have hS := sepConv_of_finMomL S.b_pos S.mom hL
    exact ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, core_of_min S, hE, hcl, hV,
      (af_iff_flowAFL hS hL).1 S.af, (wardT_iff_flowWardL hS hL).1 hW, hP, hB,
      (threePoint_iff_flowThreeL hL).1 h3, (obsRunSeedW_iff (by omega)).2 hRS⟩

/-- **`ClayStatementDy` from `NarrowInputsAtObsF` at some observer and margin, at every `N ≥ 2`**.
DERIVED: `2` the least colour count. -/
theorem clayStatement_of_narrowAtObsF
    (h : ∀ (N : ℕ) (hN2 : 2 ≤ N), ∃ (W : ConfFlow N) (r : ℝ), NarrowInputsAtObsF N hN2 W r) :
    MassGap.ClayStatementDy :=
  clayStatement_of_narrowAtMinF fun N hN2 => by
    obtain ⟨W, r, hA⟩ := h N hN2
    exact ⟨W, r, (narrowInputsAtObsF_iff_minF hN2).1 hA⟩

/-- **`NarrowInputsAtObs` gives `NarrowInputsAtObsF`** at the same `W`, `r` (`expandRF_of_expandR`).
DERIVED: `2` the least colour count. -/
theorem narrowInputsAtObsF_of_obs (hN2 : 2 ≤ N) {W : ConfFlow N} {r : ℝ}
    (h : NarrowInputsAtObs N hN2 W r) : NarrowInputsAtObsF N hN2 W r := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hcl, hV, hAF, hW, hP, hB, h3, hOS⟩ := h
  exact ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, expandRF_of_expandR hE, hcl, hV, hAF, hW, hP, hB,
    h3, hOS⟩

end MassGap.ExpandFam

end

#print axioms MassGap.ExpandFam.expandRF_of_expandR
#print axioms MassGap.ExpandFam.expandLim_of_expandRF
#print axioms MassGap.ExpandFam.mul_div_succ_le
#print axioms MassGap.ExpandFam.boundC_of_finMomL
#print axioms MassGap.ExpandFam.convC_of_finMomL
#print axioms MassGap.ExpandFam.os1C_of_finMomL
#print axioms MassGap.ExpandFam.tendsto_obsLimL
#print axioms MassGap.ExpandFam.contC_eq_obsLimCL
#print axioms MassGap.ExpandFam.eventually_rateL
#print axioms MassGap.ExpandFam.flowCovLim_of_covCL
#print axioms MassGap.ExpandFam.covC_of_flowCovLimL
#print axioms MassGap.ExpandFam.flowCovLim_iff_covCL
#print axioms MassGap.ExpandFam.latRead_sub_proxRead_small
#print axioms MassGap.ExpandFam.compNondeg_of_proxyL
#print axioms MassGap.ExpandFam.proxyNondeg_of_compNondegL
#print axioms MassGap.ExpandFam.proxyNondeg_iffL
#print axioms MassGap.ExpandFam.os0C_of_clusterF
#print axioms MassGap.ExpandFam.compOS_of_minF
#print axioms MassGap.ExpandFam.approxK_of_beyond_minF
#print axioms MassGap.ExpandFam.clayInputsN_of_narrowAtMinF
#print axioms MassGap.ExpandFam.clayStatement_of_narrowAtMinF
#print axioms MassGap.ExpandFam.narrowInputsAtMinF_of_min
#print axioms MassGap.ExpandFam.smallFlow_const_mul
#print axioms MassGap.ExpandFam.latT_smallFlowL
#print axioms MassGap.ExpandFam.sepConv_of_finMomL
#print axioms MassGap.ExpandFam.contT_eq_iff_flowNearL
#print axioms MassGap.ExpandFam.af_iff_flowAFL
#print axioms MassGap.ExpandFam.obsLower_iff_flowThreeL
#print axioms MassGap.ExpandFam.threePoint_iff_flowThreeL
#print axioms MassGap.ExpandFam.wardT_of_flowWardL
#print axioms MassGap.ExpandFam.flowWard_of_wardTL
#print axioms MassGap.ExpandFam.wardT_iff_flowWardL
#print axioms MassGap.ExpandFam.kernC_diag_flowedNL
#print axioms MassGap.ExpandFam.generation_iff_flowGenL
#print axioms MassGap.ExpandFam.narrowInputsAtObsF_iff_minF
#print axioms MassGap.ExpandFam.clayStatement_of_narrowAtObsF
#print axioms MassGap.ExpandFam.narrowInputsAtObsF_of_obs
