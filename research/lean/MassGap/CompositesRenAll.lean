import Mathlib
import MassGap.CompositesRen
import MassGap.CompositeNondeg

/-!
# MassGap.CompositesRenAll — the multi-scale control at the renormalised composites

`MultiScaleAll` reads its composite inputs (`expand`, `OS0C`, `OS1C`, `CovC`, `CompNondeg`, `approx`) at
`CbR 2 zOne = build (rhoD (fR 2) zOne) (bareD …)`, whose off-tensor fields are bare (`CompositeNondeg`). This
module states the same multi-scale control with the expansion read at the renormalised family
`CompositesRen.CRen 2 z μ`, derives `BoundC` and `ConvC` there, and proves the `SU(N)` capstone
`clayStatementAt_SU_of_flowRen` with every composite input read at `CRen N z μ` and the gap `RunSeed N` as an
input. No capstone is stated from the `SU(2)` record `MultiScaleAllRen`: its `endpoint` field,
`MultiScale.Endpoint`, is refuted by `InputAudit.not_multiScaleEndpoint` under the argued growth of the
zero-flux level count.

## 1. The statement

`MultiScaleAllRen W z μ` is `∃ b Wf c, MultiScaleAllRenAt W z μ b Wf c`, with the fields of
`MultiScaleAll.MultiScaleAllAt` except:

* `expand` is `ExpandR Wf c z μ`: the clause `MultiScaleAll.Expand` with `latC (CRen 2 z μ)` in place of
  `latC (CbR 2 zOne)`. The flowed side `msLat Wf c k s F` is unchanged: it reads only the index `i : Ix0` and
  the test function of each insertion, and both families have index type `Ix0`.
* `af` reads the trace channel at `rhoD (fR 2) z` in place of `rhoD (fR 2) zOne`.

`z` is free. The scale clause `scale`, the endpoint and `Wf b = W` are as in `MultiScaleAll`.

## 2. What is proved

* `uv_of_scale` (every `SU(N)`): the `uv` clause of `ScaleControlFull` from `scale` at `s = b` and
  `Wf b = W` (the proof of `MultiScaleAll.multiScale_of_all`, which uses no other field).
* `boundC_ren_of_scale_expand` (every `SU(N)`), `boundC_ren_of_all`, `convC_ren_of_all`: `BoundC (CRen N z μ)`
  and `ConvC (CRen N z μ)` from `scale` and `ExpandR`, by the chain of `MultiScaleAll.boundC_of_scale_expand`
  (`abs_msLat_le` at `s = min(θ d, b)` plus the remainder). The derivation reads no property of the composite
  family beyond its index type, so it ports unchanged.
* `clayStatementAt_SU_ren_low`: `CompositesRen.clayStatementAt_SU_ren` with `ObsLower` in place of
  `ObsThreePoint` (`InputsTriage.nonGaussianT_rhoD_of_lower`, with `SepConv (rhoD (fR N) z)` from `ConvC` of
  `CRen N z μ` by `CompReduce.sepConv_of_comp` and `buildRen_he2`).
* **`clayStatementAt_SU_of_flowRen`** (every `N ≥ 2`): `FlowRenAt W z μ b Wf c` (the fields `b_pos`,
  `top`, `scale`, `expand` of `MultiScaleAllRenAt`, at `ConfFlow N`) with the gap `RunSeed N`, `hz`, `hzS`,
  `hzP`, `phys`, a kernel `G` with `AFCoefficient N G`, `ObsLower z`, `WardT`, `OS0C ∧ OS1C ∧ CovC ∧
  CompNondeg` and `ApproxK` at `CRen N z μ` gives `ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N)`;
  `ClassMoments` and `ConvC` are derived. `clayStatementAt_SU_of_flowRen_zFix` discharges `hz`, `hzS`, `hzP`
  at `z = zFix N zri zwe`. `MultiScaleAllRenAt.toFlowRenAt` reads `FlowRenAt` off the `SU(2)` record.
* `ren_CRen_tensor`, `latC_CRen_tensor`, `contC_CRen_tensor`: on the tensor indices (`dec i.1 = some α`)
  `CRen N z μ` and `CbR N z` have the same fields, lattice readings and continuum readings, for every `μ`.
* `not_compNondeg_comb`: for any composites, `CompNondeg` fails when one combination `c` has a non-zero
  on-shell top-dimension classical part and every separated two-point reading of `c` is `0`.
* `not_compNondeg_CRen_of_tensor`: for every `z`, `μ`, `CompNondeg (CRen 2 z μ)` fails as soon as a
  combination supported on the tensor indices has a non-zero on-shell top-dimension classical part and
  vanishing separated two-point readings in `CbR 2 z`.

## 3. Argued (no declaration)

* **`ExpandR` is the physical form of the expansion.** `CRen 2 z μ` reads off the tensor indices the field
  `e^{lz k i} a_k^{−cdim i}(bare i − ∑_{lowJ} m k i j bare j)`, and on the tensor indices the mixing of
  `rhoD (fR 2) z`. The flowed monomials `a_k^{−d_j}(O_j ∘ V_k^{(s)} − ν_k)` are in the same physical units.
  The small-flow-time expansion of a renormalised composite has coefficients `c_{ij}(s)` independent of the
  lattice step, of size `s^{d_j − d_i}` times powers of `log s`; the factor `a_k^{−cdim i}` and the
  logarithms `lz` sit in the composite, not in `c`. So the `k`-independent `c : Ix0 → ℝ → (MIx →₀ ℝ)` of
  `MultiScaleAll` is the expected form here. At `CbR 2 zOne` it is not: the off-tensor readings are of size
  `a_k^{d_i + d_j}` (`CompositesRen.latC_two_noMix` relates the two), so `Expand` there could hold only with
  coefficients that make the flowed side vanish as well.
* **`z` must stay free.** At `zOne = zFix 2 1 1` the factor is `1` on `ri` and `we`: the tensor composites'
  traceless-Ricci and Weyl channel parts are the bare dimensionless combinations, with no `a_k^{−4}`. A
  combination of tensor indices projecting onto one of these channels has a non-zero on-shell classical top
  part (the classical traceless-Ricci or Weyl component of `F F`) and separated two-point readings of size
  `a_k^{8}` in `CbR 2 zOne`, expected to vanish in the limit. By `not_compNondeg_CRen_of_tensor` this makes
  `CompNondeg (CRen 2 zOne μ)` fail for every `μ`. The vanishing is not proved here. The capstone therefore
  keeps `z` free; the expected choice is `zFix 2 zri zwe` with `zri k, zwe k ∼ a_k^{−4}` (times the channel's
  logarithms), for which `clayStatementAt_SU_of_flowRen_zFix` discharges `hz`, `hzS`, `hzP`.
* **The general-group path has no fixed composite family.** Every `G` capstone (`ClayG.clayStatementAtG_GS`,
  `ClayGFinal.clayStatementAtG_GS_at`, `ClayGFinal.clayStatementAtG_GS_noNT`, `ClayGFinal.ClayAtGNoNT`,
  `AbelianGen`, `ClayWiringG`, `SymPlaqG`) takes `Cs : CompositesG G` (or `Cs : Composites N`, sent by
  `Composites.toG`) as an input, with `CompDataG Cs` and `CompOSG (canonSched G) Cs` as hypotheses. The tree
  has no `CompositesG` construction (no `G` analogue of `CompositesBuild.build`, `Ix0` bare fields, `repF` or
  `RenTensor`). So the defect of `build` (bare off-tensor fields) does not occur on the `G` path, and there is
  no family at which to state a `G` analogue of `CompositeNondeg.not_compNondeg_single`'s consequence. A `G`
  analogue of `buildRen` would need a `G` bare family with `ClassicalLeadG` (the `Tied` clause), a `G`
  tensor mixing with `RenTensor`, and the `RepTie` proof over `GPotG G`; none is in the tree, so it does not
  port directly.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` is `SU(2)`, the two points and the limits of the scalar and pseudoscalar
factors; `4` the dimension of the plaquette density; `1` the floor `1 + |log s|`, the unit field and the
spacing bound; `2 · 1 + 3` the site count of `classMoments_of_siteExp`; `0` the plane and the vanishing
readings.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.CompositesRenAll

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
  MassGap.MixConvRP MassGap.MultiScaleAll MassGap.CompositesRen
open MassGap.ScaleControlFull (zOne)

local notation "h2N" => (ne_zero_of_two_le (le_refl 2) : (2 : ℕ) ≠ 0)

variable {N : ℕ}

/-! ## 1. The statement -/

/-- **The small-flow-time expansion of the renormalised composites `CRen N z μ`**: `MultiScaleAll.Expand`
with the lattice reading of `CRen N z μ`, at every `SU(N)`. -/
def ExpandR [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) (z : Chan → ℕ → ℝ)
    (μ : OffMix) : Prop :=
  ∃ (θ ε Kr : ℝ) (κr : Ix0 → ℝ), 0 < θ ∧ 0 < ε ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → CDatum (CRen N z μ)) (d : ℝ), 0 < d →
      ContD F → SepD d F → ∀ s : ℝ, 0 < s → s ≤ θ * d → ∀ᶠ k in atTop,
        |latC (NeZero.ne N) (CRen N z μ) k F - msLat Wf c k s F|
          ≤ Kr ^ Fintype.card ι * (s / d) ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)

/-- **The multi-scale statement at the renormalised composites**, at its data. Module docstring, §1. -/
structure MultiScaleAllRenAt (W : ConfFlow 2) (z : Chan → ℕ → ℝ) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow 2) (c : Ix0 → ℝ → (MIx →₀ ℝ)) : Prop where
  b_pos : 0 < b
  /-- The flow to the physical scale is `W`. -/
  top : Wf b = W
  /-- Every intermediate scale: the asymptotic-freedom moments of every monomial. -/
  scale : ScaleControlAll b Wf
  /-- The small-flow-time expansion of the renormalised composites. -/
  expand : ExpandR Wf c z μ
  /-- Asymptotic freedom: a two-point kernel of the trace at `z` with the asymptotic-freedom coefficient. -/
  af : ∃ G : ℝ → ℝ, TwoPointKernel h2N (rhoD (fR 2) z) G ∧ AFCoefficient 2 G
  /-- Strong coupling at the physical scale: the slice endpoint with the odd levels. -/
  endpoint : MultiScale.Endpoint

/-- **Control at every intermediate scale, with the renormalised composites** (`SU(2)`, at the flow `W`,
the channel factor `z` and the off-tensor renormalisation `μ`). -/
def MultiScaleAllRen (W : ConfFlow 2) (z : Chan → ℕ → ℝ) (μ : OffMix) : Prop :=
  ∃ (b : ℝ) (Wf : ℝ → ConfFlow 2) (c : Ix0 → ℝ → (MIx →₀ ℝ)), MultiScaleAllRenAt W z μ b Wf c

/-! ## 2. `uv`, `BoundC`, `ConvC` -/

/-- **`uv` from the scale clause at `s = b`** on the plaquette indices (the proof of
`MultiScaleAll.multiScale_of_all`). DERIVED: `4` the dimension; `2 · 1 + 3` the site count. -/
theorem uv_of_scale [NeZero N] {W : ConfFlow N} {b : ℝ} {Wf : ℝ → ConfFlow N} (hb : 0 < b)
    (htop : Wf b = W) (hsc : ScaleControlAll b Wf) :
    ∃ t C : ℝ, 0 < t ∧ FlowUV.SiteExp (NeZero.ne N) W (SymPlaqClass N) (t * (2 * 1 + 3) ^ 4) C := by
  obtain ⟨t, C, γ, γP, ht, hev⟩ := hsc
  have hpos : 0 < t * b ^ 4 / afLog γP b := div_pos (mul_pos ht (pow_pos hb 4)) (afLog_pos _ _)
  refine ⟨t * b ^ 4 / afLog γP b / (2 * 1 + 3) ^ 4, C, div_pos hpos (by norm_num), ?_⟩
  rw [div_mul_cancel₀ _ (by norm_num : ((2 : ℝ) * 1 + 3) ^ 4 ≠ 0)]
  unfold FlowUV.SiteExp
  filter_upwards [hev, (tendsto_dySpacing N).eventually (gt_mem_nhds hb)] with k hk hkb
  rintro O ⟨q, rfl⟩
  have h1 := hk b hkb.le le_rfl (Sum.inr q)
  rw [htop, mField_inr, mDim_inr, msMu_inr] at h1
  have e : msAbs (W.fieldMap k (sym (plaqField q))).1 = (W.fieldMap k (sym (plaqField q))).1 := by
    ext U
    have key : ∀ O ∈ SymPlaqClass N, ∀ U, 0 ≤ (W.fieldMap k O).1 U :=
      fun O hO U => symPlaq_nonneg (NeZero.ne N) O hO (W.V k U)
    rw [msAbs_apply]
    exact abs_of_nonneg (key _ ⟨q, rfl⟩ U)
  rw [e] at h1
  exact h1

/-- **`BoundC (CRen N z μ)` from the scale clause and `ExpandR`**, at every `SU(N)`: at `s = min(θ d, b)` the renormalised
reading is the flowed reading (bounded uniformly in the step, `abs_msLat_le`) up to the remainder.
DERIVED: `1` the spacing bound. -/
theorem boundC_ren_of_scale_expand [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hsc : ScaleControlAll b Wf)
    (hex : ExpandR Wf c z μ) : InputsTriage.BoundC (NeZero.ne N) (CRen N z μ) := by
  obtain ⟨t, C, γ, γP, ht, hev⟩ := hsc
  obtain ⟨θ, ε, Kr, κr, hθ, -, hE⟩ := hex
  intro ι _ _ F hF
  obtain ⟨hcont, d, hd, hsep⟩ := hF
  have hs : 0 < min (θ * d) b := lt_min (mul_pos hθ hd) hb
  refine ⟨(1 + Fintype.card ι * (((2 * Fintype.card ι).factorial : ℝ) * (Real.exp C * C)))
      * ∏ i, (msTsize (F i).2 * msPsize t γ γP c (min (θ * d) b) (F i).1)
    + Kr ^ Fintype.card ι * (min (θ * d) b / d) ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2), ?_⟩
  refine Filter.Eventually.filter_mono ultra_le ?_
  filter_upwards [hev, hE ι F d hd hcont hsep (min (θ * d) b) hs (min_le_left _ _),
    (tendsto_dySpacing N).eventually (gt_mem_nhds hs),
    (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)] with k hk hrem hks hk1
  have hP := abs_msLat_le Wf c ht hs hk1.le (hk _ hks.le (min_le_right _ _)) F
  have htri := abs_sub_abs_le_abs_sub (latC (NeZero.ne N) (CRen N z μ) k F)
    (msLat Wf c k (min (θ * d) b) F)
  linarith

/-- **`BoundC (CRen 2 z μ)` from `MultiScaleAllRen`.** -/
theorem boundC_ren_of_all {W : ConfFlow 2} {z : Chan → ℕ → ℝ} {μ : OffMix}
    (h : MultiScaleAllRen W z μ) : InputsTriage.BoundC h2N (CRen 2 z μ) := by
  obtain ⟨b, Wf, c, H⟩ := h
  exact boundC_ren_of_scale_expand H.b_pos H.scale H.expand

/-- **`ConvC (CRen 2 z μ)` from `MultiScaleAllRen`** (`InputsTriage.convC_iff_boundC`). -/
theorem convC_ren_of_all {W : ConfFlow 2} {z : Chan → ℕ → ℝ} {μ : OffMix}
    (h : MultiScaleAllRen W z μ) : ConvC h2N (CRen 2 z μ) :=
  (InputsTriage.convC_iff_boundC _ _).2 (boundC_ren_of_all h)

/-! ## 3. The capstones -/

section Capstone

/-- **The SU capstone at `CRen N z μ` with `ObsLower`**: `CompositesRen.clayStatementAt_SU_ren` with
`NonGaussianT` from `ObsLower` (`InputsTriage.nonGaussianT_rhoD_of_lower`), `SepConv` from `hCO`
(`CompReduce.sepConv_of_comp`, `buildRen_he2`). DERIVED: `2` the least colour count; `0` the plane. -/
theorem clayStatementAt_SU_ren_low (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (z : Chan → ℕ → ℝ) (hz : ∀ c k, z c k ≠ 0)
    (hzS : Tendsto (fun k => z .sc k * dySpacing N k ^ 4) atTop (𝓝 2))
    (hzP : Tendsto (fun k => z .ps k * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) (rhoD (fR N) z) G)
    (hAF : AFCoefficient N G)
    (hLow : InputsTriage.ObsLower (ne_zero_of_two_le hN2) z)
    (hWard : WardT (ne_zero_of_two_le hN2) (rhoD (fR N) z))
    (μ : OffMix)
    (hCO : CompOS (ne_zero_of_two_le hN2) (CRen N z μ))
    (hA : ApproxK (kernC (ne_zero_of_two_le hN2) (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r)
      (gramF hN2 W r)) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) := by
  have hN := ne_zero_of_two_le hN2
  have hUL := unifLocal_buildRen (rhoD (fR N) z) (bareD (fR N) (bR N)) μ
  have hcov : ReflCovLat (CRen N z μ) 0 := reflCovLat_CRen z μ
  have hMC := mixConvG_of_cov hN2 W hU hphys (CRen N z μ) hUL hcov hCO
  obtain ⟨wC, hLC, hX⟩ := linkCPreG_of_kernels hN2 W hU hphys (rhoD (fR N) z) (CRen N z μ) eI
    (fun α => buildRen_he1 _ _ μ α) (fun k α => buildRen_he2 _ _ μ k α) hCO
    (jointRPKG_of_reflLim hN2 W hU hphys (CRen N z μ) hUL
      (reflLimG_of_cov hN2 W (CRen N z μ) r hcov hCO hMC)) hA hMC
  have hS : SepConv hN (rhoD (fR N) z) :=
    CompReduce.sepConv_of_comp hN (rhoD (fR N) z) (CRen N z μ) eI
      (fun k α => buildRen_he2 _ _ μ k α) hCO.1
  exact ClaySUFinal.clayStatementAt_SU_final hN2 W ht hU hphys hfar (rhoD (fR N) z)
    (riemann_mixOfZ (opD (fR N)) (mD N) (ZD z) (coefRiemann_mD N))
    (scalarTie_D hN (fR N) z hzS).2
    (channelTie_D (fR N) (bR N) z hzP (tiedB_R hN)) G hK hAF
    (InputsTriage.nonGaussianT_rhoD_of_lower hN (fR N) z hS hLow) hWard
    (CRen N z μ) wC eI (fun α => buildRen_he1 _ _ μ α) (fun k α => buildRen_he2 _ _ μ k α)
    (buildRen_compData _ _ μ (by omega) (tiedB_R hN) (renTensor_D hN (fR N) (bR N) z hz)) hCO
    (fun R _ α => buildRen_hrep _ _ μ R α) hLC hX

/-- **The flow-side inputs at `SU(N)`**: a physical scale `b > 0`, flows `Wf` with `Wf b = W`, the scale
clause `ScaleControlAll b Wf` and the expansion `ExpandR Wf c z μ`. These are the fields of
`MultiScaleAllRenAt` other than `af` and `endpoint`. -/
structure FlowRenAt [NeZero N] (W : ConfFlow N) (z : Chan → ℕ → ℝ) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) : Prop where
  b_pos : 0 < b
  /-- The flow to the physical scale is `W`. -/
  top : Wf b = W
  /-- Every intermediate scale: the asymptotic-freedom moments of every monomial. -/
  scale : ScaleControlAll b Wf
  /-- The small-flow-time expansion of the renormalised composites. -/
  expand : ExpandR Wf c z μ

/-- **The `SU(N)` capstone from the flow-side inputs**: `FlowRenAt W z μ b Wf c` with the gap
`RunSeed N`, `hz`, `hzS`, `hzP`, `phys`, a two-point kernel `G` of `rhoD (fR N) z` with the
asymptotic-freedom coefficient, `ObsLower z`, `WardT (rhoD (fR N) z)`, `OS0C ∧ OS1C ∧ CovC ∧ CompNondeg`
of `CRen N z μ` and `ApproxK` at `CRen N z μ` gives `ClayStatementAt` at `W`. `ClassMoments` (from
`uv_of_scale`) and `ConvC` (from `boundC_ren_of_scale_expand`) are derived. DERIVED: `2` the least colour
count and the limits of the scalar and pseudoscalar factors; `4` the dimension. -/
theorem clayStatementAt_SU_of_flowRen (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {r : ℝ}
    {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ} {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    (H : FlowRenAt W z μ b Wf c) (hfar : WDeltaRun.RunSeed N)
    (hz : ∀ c k, z c k ≠ 0)
    (hzS : Tendsto (fun k => z .sc k * dySpacing N k ^ 4) atTop (𝓝 2))
    (hzP : Tendsto (fun k => z .ps k * dySpacing N k ^ 4) atTop (𝓝 2))
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) (rhoD (fR N) z) G)
    (hAF : AFCoefficient N G)
    (hlow : InputsTriage.ObsLower (ne_zero_of_two_le hN2) z)
    (hward : WardT (ne_zero_of_two_le hN2) (rhoD (fR N) z))
    (hos : OS0C (ne_zero_of_two_le hN2) (CRen N z μ) ∧ OS1C (ne_zero_of_two_le hN2) (CRen N z μ)
      ∧ CovC (ne_zero_of_two_le hN2) (CRen N z μ) ∧ CompNondeg (ne_zero_of_two_le hN2) (CRen N z μ))
    (happrox : ApproxK (kernC (ne_zero_of_two_le hN2) (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r)
      (gramF hN2 W r)) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) := by
  have hconv : ConvC (ne_zero_of_two_le hN2) (CRen N z μ) :=
    (InputsTriage.convC_iff_boundC _ _).2 (boundC_ren_of_scale_expand H.b_pos H.scale H.expand)
  obtain ⟨t, C, ht, hS⟩ := uv_of_scale H.b_pos H.top H.scale
  exact clayStatementAt_SU_ren_low hN2 W ht
    (ClaySUFinal.classMoments_of_siteExp (ne_zero_of_two_le hN2) W ht hS) hphys hfar
    z hz hzS hzP G hK hAF hlow hward μ ⟨hconv, hos⟩ happrox

/-- **The `SU(N)` capstone at `z = zFix N zri zwe`**: `hz`, `hzS`, `hzP` are discharged when `zri`, `zwe`
are nowhere zero (`ZCanon.zFix_ne`, `ZCanon.tendsto_zFix_sc`, `ZCanon.tendsto_zFix_ps`). DERIVED: `2` the
least colour count. -/
theorem clayStatementAt_SU_of_flowRen_zFix (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {r : ℝ}
    {zri zwe : ℕ → ℝ} (hri : ∀ k, zri k ≠ 0) (hwe : ∀ k, zwe k ≠ 0) {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    (H : FlowRenAt W (ZCanon.zFix N zri zwe) μ b Wf c) (hfar : WDeltaRun.RunSeed N)
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) (rhoD (fR N) (ZCanon.zFix N zri zwe)) G)
    (hAF : AFCoefficient N G)
    (hlow : InputsTriage.ObsLower (ne_zero_of_two_le hN2) (ZCanon.zFix N zri zwe))
    (hward : WardT (ne_zero_of_two_le hN2) (rhoD (fR N) (ZCanon.zFix N zri zwe)))
    (hos : OS0C (ne_zero_of_two_le hN2) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ OS1C (ne_zero_of_two_le hN2) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ CovC (ne_zero_of_two_le hN2) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ CompNondeg (ne_zero_of_two_le hN2) (CRen N (ZCanon.zFix N zri zwe) μ))
    (happrox : ApproxK (kernC (ne_zero_of_two_le hN2) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
      (mixKG hN2 W (CRen N (ZCanon.zFix N zri zwe) μ) r) (gramF hN2 W r)) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  clayStatementAt_SU_of_flowRen hN2 H hfar (ZCanon.zFix_ne (by omega) hri hwe)
    (ZCanon.tendsto_zFix_sc (by omega) _ _) (ZCanon.tendsto_zFix_ps (by omega) _ _) hphys G hK hAF
    hlow hward hos happrox

end Capstone

/-- **`MultiScaleAllRenAt` contains the flow-side inputs** (`b_pos`, `top`, `scale`, `expand`). -/
theorem MultiScaleAllRenAt.toFlowRenAt {W : ConfFlow 2} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow 2} {c : Ix0 → ℝ → (MIx →₀ ℝ)} (H : MultiScaleAllRenAt W z μ b Wf c) :
    FlowRenAt W z μ b Wf c :=
  ⟨H.b_pos, H.top, H.scale, H.expand⟩

/-! ## 4. The tensor indices of `CRen` and `CompNondeg` -/

section Tensor

/-- **On the tensor indices `CRen N z μ` and `CbR N z` have the same field**, for every `μ`.
DERIVED: no numeral. -/
theorem ren_CRen_tensor (z : Chan → ℕ → ℝ) (μ : OffMix) {i : Ix0} {α : Idx4} (hd : dec i.1 = some α)
    (k : ℕ) : (CRen N z μ).ren k i = (CbR N z).ren k i := by
  show renR _ _ μ k i = renF _ _ k i
  rw [renR_of_some _ _ μ hd, renF_of_some _ _ hd]

/-- **A family on tensor indices reads the same in `CRen N z μ` and `CbR N z`**, at every step.
DERIVED: no numeral. -/
theorem latC_CRen_tensor (hN : N ≠ 0) (z : Chan → ℕ → ℝ) (μ : OffMix) {ι : Type} [Fintype ι]
    (F : ι → CDatum (CRen N z μ)) (hF : ∀ x, ∃ α, dec (F x).1.1 = some α) (k : ℕ) :
    latC hN (CRen N z μ) k F = latC hN (CbR N z) k F := by
  unfold latC cField
  congr 1
  funext x
  obtain ⟨α, hα⟩ := hF x
  rw [ren_CRen_tensor z μ hα k]

/-- The continuum readings agree as well. DERIVED: no numeral. -/
theorem contC_CRen_tensor (hN : N ≠ 0) (z : Chan → ℕ → ℝ) (μ : OffMix) {ι : Type} [Fintype ι]
    (F : ι → CDatum (CRen N z μ)) (hF : ∀ x, ∃ α, dec (F x).1.1 = some α) :
    contC hN (CRen N z μ) F = contC hN (CbR N z) F := by
  unfold contC
  congr 1
  funext k
  exact latC_CRen_tensor hN z μ F hF k

/-- **`CompNondeg C` fails when one combination with a non-zero on-shell top-dimension classical part has
every separated two-point reading `0`.** DERIVED: `2` the two points; `0` the vanishing reading. -/
theorem not_compNondeg_comb (hN : N ≠ 0) (C : Composites N) (c : C.Ix →₀ ℝ)
    (hon : ∃ (A : GPot N) (g : ℝ), GPot.Adm A ∧ OnShell g A
      ∧ ∑ i ∈ c.support.filter (fun i => cdim (C.cl i) = c.support.sup (fun j => cdim (C.cl j))),
          c i * g ^ cnF (C.cl i) * cval g A (C.cl i) ≠ 0)
    (hzero : ∀ f h : TestFn, Continuous f.1 → Continuous h.1 →
      (∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d f h) →
      ∑ i ∈ c.support, ∑ j ∈ c.support,
        c i * c j * contC hN C (![(i, f), (j, h)] : Fin 2 → CDatum C) = 0) :
    ¬ CompNondeg hN C := by
  intro H
  obtain ⟨f, h, hf, hh, hsep, hne⟩ := H c hon
  exact hne (hzero f h hf hh hsep)

/-- **`CompNondeg (CRen 2 z μ)` fails, for every `μ`, as soon as a combination supported on the tensor
indices has a non-zero on-shell top-dimension classical part and vanishing separated two-point readings in
`CbR 2 z`.** DERIVED: `2` the colour count and the two points; `0` the vanishing reading. -/
theorem not_compNondeg_CRen_of_tensor (z : Chan → ℕ → ℝ) (μ : OffMix) (c : Ix0 →₀ ℝ)
    (hc : ∀ i ∈ c.support, ∃ α, dec i.1 = some α)
    (hon : ∃ (A : GPot 2) (g : ℝ), GPot.Adm A ∧ OnShell g A
      ∧ ∑ i ∈ c.support.filter (fun i => cdim i.1 = c.support.sup (fun j => cdim j.1)),
          c i * g ^ cnF i.1 * cval g A i.1 ≠ 0)
    (hzero : ∀ f h : TestFn, Continuous f.1 → Continuous h.1 →
      (∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d f h) →
      ∑ i ∈ c.support, ∑ j ∈ c.support,
        c i * c j * contC h2N (CbR 2 z) (![(i, f), (j, h)] : Fin 2 → CDatum (CbR 2 z)) = 0) :
    ¬ CompNondeg h2N (CRen 2 z μ) := by
  refine not_compNondeg_comb h2N (CRen 2 z μ) c hon fun f h hf hh hsep => ?_
  rw [← hzero f h hf hh hsep]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  rw [contC_CRen_tensor h2N z μ _ (fun x => by fin_cases x; exacts [hc i hi, hc j hj])]
  rfl

end Tensor

end MassGap.CompositesRenAll

end

#print axioms MassGap.CompositesRenAll.uv_of_scale
#print axioms MassGap.CompositesRenAll.boundC_ren_of_scale_expand
#print axioms MassGap.CompositesRenAll.boundC_ren_of_all
#print axioms MassGap.CompositesRenAll.convC_ren_of_all
#print axioms MassGap.CompositesRenAll.clayStatementAt_SU_ren_low
#print axioms MassGap.CompositesRenAll.clayStatementAt_SU_of_flowRen
#print axioms MassGap.CompositesRenAll.clayStatementAt_SU_of_flowRen_zFix
#print axioms MassGap.CompositesRenAll.MultiScaleAllRenAt.toFlowRenAt
#print axioms MassGap.CompositesRenAll.ren_CRen_tensor
#print axioms MassGap.CompositesRenAll.latC_CRen_tensor
#print axioms MassGap.CompositesRenAll.contC_CRen_tensor
#print axioms MassGap.CompositesRenAll.not_compNondeg_comb
#print axioms MassGap.CompositesRenAll.not_compNondeg_CRen_of_tensor
