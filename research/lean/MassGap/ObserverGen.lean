import Mathlib
import MassGap.ObserverBundle

/-!
# MassGap.ObserverGen — the generation clause on the observer's flowed readings

`ObserverBundle.NarrowInputsAtObs` states every clause on the observer's flowed readings except `ExpandR`
(the bridge) and the generation clause
`∀ P, BeyondR r P → ApproxKAt (kernC (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) P`.
That clause reads three kernels. `gramF` is the observer's own Gram kernel (`contSF` of `Φ0 W` on margin
monomials). `ApproxKAt` reads `kernC` only on the diagonal `kernC(P, P) = sgn(P) · contC(ΘP ∪ P)`, a
composite limit on the admissible family `pairC P P` (`CompositeLink.adm_pairC`). `mixKG(P, Q) =
sgn(P) · lim_ultra mixLatC(P, Q)` reads the composites of `P` and the flowed fields of the margin monomial
`Q` in one lattice expectation. This module moves the diagonal onto the flowed readings, states the
generation clause in that form (`FlowGen`), proves it equivalent under the bundle, states the bundle with
`FlowGen` in its place, and states as a declaration what the mixed kernel still needs. Declarations are in
the namespace `MassGap.ObserverGen`.

These are restatements. `FlowGen` moves the diagonal of the generation clause onto the observer's flowed
readings and removes no content; `NarrowInputsAtObs'` is satisfiable exactly when `NarrowInputsAtObs` is
(`narrowInputsAtObs'_iff`).

## 1. The diagonal (proved)

* `kernC_eq_obsLim`: under `ExpandR` and `ConvC`, `kernC(P, P) = sgn(P) · obsLimC Wf cf (ΘP ∪ P)`
  (`InputMerge.contC_eq_obsLimC` at `CompositeLink.adm_pairC`).
* `kernC_diag_flowedN`: under `ExpandR` and `ConvC`, for every `η > 0`, for all small `s > 0`, eventually
  along `ultra`, `|sgn(P) · msLat Wf cf k s (ΘP ∪ P) − kernC(P, P)| ≤ η`. The proof of
  `ApproxFromExpand.kernC_diag_flowed` at every `N` with the two inputs named.

## 2. The flowed generation clause (defined; equivalence proved)

* `FlowGen hN2 W Wf cf z μ r`: for every `P` beyond `r` and `ε > 0`, real coefficients `c` on the margin
  monomials with, for all small `s > 0`, eventually along `ultra`,
  `sgn(P) · msLat Wf cf k s (ΘP ∪ P) − 2 xL(mixKG P) c + gForm(gramF) c c ≤ ε`.
* **`generation_iff_flowGen`**: under `ExpandR` and `ConvC`, the generation clause is `FlowGen`.
* `NarrowInputsAtObs' N hN2 W r`: `NarrowInputsAtObs` with the generation clause replaced by `FlowGen`.
  **`narrowInputsAtObs'_iff`** (`ConvC` from `InputMerge.convC_of_finMom`), `narrowInputsAtObs'_iff_min`,
  **`clayStatement_of_narrowAtObs'`**.

## 3. The mixed kernel (what remains; stated and proved conditionally)

`mixKG` is not rewritten by the bundle. Its observer side, `(Φ0 W).field k` on `Q`, is already the
observer. Its composite side, `cField` of `P` inside the same expectation as the observer's fields, is
compared with the flowed proxies by no clause of the bundle: `ExpandR` quantifies over families
`F : ι → CDatum (CRen N z μ)` of composites only and compares `latC` with `msLat`; a mixed reading is not
such a family. (`ApproxFromExpand` §2 argues the same for the cross term; `ApproxFromExpand.diag_match_not_approxK`
and `ProxyGenLimN.decoupled_core` prove that the diagonal and the observer's Gram kernel do not control it.)

The missing statement is the mixed small-flow-time expansion, stated here:

* `msMix W Wf cf k s P Q`: the mixed flowed reading, `ν_k(∏ᵢ smear a_k (msProx(s, Pᵢ)) (Θfᵢ) ·
  ∏ⱼ smear a_k ((Φ0 W)_k Qⱼ))`: the composites of `P` replaced by their flowed proxies, the observer's
  fields of `Q` kept.
* `ExpandMix W Wf cf z μ r`: for every `P`, every margin monomial `Q` and `η > 0`, for all small `s > 0`,
  eventually along `ultra`, `|mixLatC(P, Q) − msMix(s, P, Q)| ≤ η`. No clause of the bundle states it:
  `ExpandR` reads composite families only. That the bundle does not imply it is argued (above), not proved.
* `mixConvG_of_obs`: the bundle gives `CompositesRen.MixConvG` (the mixed readings converge along `ultra`;
  `CompositesRen.mixConvG_of_cov` with `CompOS` from `InputMerge.compOS_of_min`).
* **`mixKG_eq_obsMix`**: under `MixConvG` and `ExpandMix`, `mixKG(P, Q) = sgn(P) · obsMix(P, Q)`,
  `obsMix = lim_{s → 0⁺} lim_ultra msMix`.
* `FlowGenMix`: `FlowGen` with `mixKG` replaced by `sgn · obsMix`. **`flowGen_iff_mix`**: under
  `MixConvG` and `ExpandMix`, `FlowGen ↔ FlowGenMix`; so with `ExpandMix` the generation clause reads
  the observer's flowed readings, its own Gram kernel and nothing else.

So the generation clause, under the bundle, reads exactly one composite object that is not the observer's
flowed reading: the mixed kernel `mixKG`, and the statement that would move it is `ExpandMix`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` the least colour count, the cross-term factor and the halving of the tolerance;
`0` the plane, the reflection, the limit of the scale and the signs.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ObserverGen

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
open MassGap.WardFromLattice (FlowWard)

variable {N : ℕ}

/-! ## 1. The diagonal -/

/-- **The diagonal of the composite kernel is the observer's double limit**, under `ExpandR` and `ConvC`
(`InputMerge.contC_eq_obsLimC` at `CompositeLink.adm_pairC`). DERIVED: `0` the plane. -/
theorem kernC_eq_obsLim [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hE : ExpandR Wf cf z μ) (hC : ConvC (NeZero.ne N) (CRen N z μ))
    (P : TSepG (CRen N z μ).Ix 0) :
    kernC (NeZero.ne N) (CRen N z μ) 0 P P
      = sgnC (CRen N z μ) 0 P.1 * obsLimC Wf cf (pairC (CRen N z μ) 0 P.1 P.1) := by
  unfold kernC
  rw [contC_eq_obsLimC hE hC _ (adm_pairC (CRen N z μ) P P)]

/-- **The diagonal is the small-scale limit of the flowed reading**, under `ExpandR` and `ConvC`: for
every `η > 0`, for all small `s > 0`, eventually along `ultra`,
`|sgn(P) · msLat Wf cf k s (ΘP ∪ P) − kernC(P, P)| ≤ η`. DERIVED: `2` the halving of `η`; `0` the plane
and the limit of the scale. -/
theorem kernC_diag_flowedN [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hE : ExpandR Wf cf z μ) (hC : ConvC (NeZero.ne N) (CRen N z μ))
    (P : TSepG (CRen N z μ).Ix 0) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
      |sgnC (CRen N z μ) 0 P.1 * msLat Wf cf k s (pairC (CRen N z μ) 0 P.1 P.1)
        - kernC (NeZero.ne N) (CRen N z μ) 0 P P| ≤ η := by
  obtain ⟨θ, ε, Kr, κr, hθ, hε, hEx⟩ := hE
  obtain ⟨hcont, d, hd, hsep⟩ := adm_pairC (CRen N z μ) P P
  set F := pairC (CRen N z μ) 0 P.1 P.1 with hF
  have hL := hC _ F ⟨hcont, d, hd, hsep⟩
  set Mc : ℝ := |Kr ^ Fintype.card (Fin P.1.1 ⊕ Fin P.1.1)
    * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)| with hMc
  have hrp : Tendsto (fun s : ℝ => Mc * (s / d) ^ ε) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun s : ℝ => Mc * (s / d) ^ ε) 0 :=
      continuousAt_const.mul ((continuousAt_id.div_const d).rpow_const (Or.inr hε.le))
    have h0 := hc.tendsto
    simp only [zero_div, Real.zero_rpow hε.ne', mul_zero] at h0
    exact h0
  have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), Mc * (s / d) ^ ε < η / 2 :=
    (hrp.eventually (gt_mem_nhds (half_pos hη))).filter_mono nhdsWithin_le_nhds
  have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < θ * d :=
    (gt_mem_nhds (mul_pos hθ hd)).filter_mono nhdsWithin_le_nhds
  have h3 : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := eventually_mem_nhdsWithin.mono fun s hs => hs
  filter_upwards [h1, h2, h3] with s hs1 hs2 hs3
  have hk := hEx _ F d hd hcont hsep s hs3 hs2.le
  filter_upwards [hk.filter_mono ultra_le, hL.eventually (Metric.ball_mem_nhds _ (half_pos hη))]
    with k hk1 hk2
  have hx : 0 ≤ (s / d) ^ ε := Real.rpow_nonneg (div_nonneg hs3.le hd.le) _
  have hb : Kr ^ Fintype.card (Fin P.1.1 ⊕ Fin P.1.1) * (s / d) ^ ε
      * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2) ≤ Mc * (s / d) ^ ε := by
    rw [hMc, mul_right_comm]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hx
  show |sgnC (CRen N z μ) 0 P.1 * msLat Wf cf k s F
    - sgnC (CRen N z μ) 0 P.1 * contC (NeZero.ne N) (CRen N z μ) F| ≤ η
  rw [← mul_sub, abs_mul, ApproxFromExpand.abs_sgnC, one_mul]
  rw [Real.dist_eq] at hk2
  have htri := abs_sub_le (msLat Wf cf k s F) (latC (NeZero.ne N) (CRen N z μ) k F)
    (contC (NeZero.ne N) (CRen N z μ) F)
  rw [abs_sub_comm] at hk1
  linarith

/-! ## 2. The flowed generation clause -/

/-- **The generation clause on the observer's flowed readings**: for every composite monomial `P` beyond
`r` and `ε > 0`, real coefficients on the margin monomials with, for all small `s > 0`, eventually along
`ultra`, `sgn(P) · msLat Wf cf k s (ΘP ∪ P) − 2 xL(mixKG P) c + gForm(gramF) c c ≤ ε`. The diagonal is
the observer's flowed reading; the mixed kernel `mixKG` is kept (module docstring, §3). DERIVED: `2` the
cross-term factor; `0` the plane, the sign of `ε` and the limit of the scale. -/
def FlowGen [NeZero N] (hN2 : 2 ≤ N) (W : ConfFlow N) (Wf : ℝ → ConfFlow N)
    (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (z : Chan → ℕ → ℝ) (μ : OffMix) (r : ℝ) : Prop :=
  ∀ P : TSepG (CRen N z μ).Ix 0, BeyondR r P → ∀ ε : ℝ, 0 < ε → ∃ c : MarginMono N 0 r →₀ ℝ,
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
      sgnC (CRen N z μ) 0 P.1 * msLat Wf cf k s (pairC (CRen N z μ) 0 P.1 P.1)
        - 2 * xL (mixKG hN2 W (CRen N z μ) r P) c + gForm (gramF hN2 W r) c c ≤ ε

/-- **The generation clause is `FlowGen`** under `ExpandR` and `ConvC` (`kernC_diag_flowedN`).
DERIVED: `2` the halving of the tolerance. -/
theorem generation_iff_flowGen (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} {r : ℝ} (hE : ExpandR Wf cf z μ)
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
    filter_upwards [kernC_diag_flowedN hE hC P (half_pos hε)] with s hs
    filter_upwards [hs] with k hk
    have := (abs_le.mp hk).2
    linarith
  · intro h P hP
    unfold ApproxKAt
    intro ε hε
    obtain ⟨c, hc⟩ := h P hP (ε / 2) (half_pos hε)
    refine ⟨c, ?_⟩
    obtain ⟨s, hs1, hs2⟩ := (hc.and (kernC_diag_flowedN hE hC P (half_pos hε))).exists
    obtain ⟨k, hk1, hk2⟩ := (hs1.and hs2).exists
    have := (abs_le.mp hk2).1
    linarith

/-- **The per-`N` inputs with the generation clause on the observer's flowed readings**:
`ObserverBundle.NarrowInputsAtObs` with the generation clause replaced by `FlowGen`. DERIVED: `2` the
least colour count; `0` the plane. -/
def NarrowInputsAtObs' (N : ℕ) (hN2 : 2 ≤ N) (W : ConfFlow N) (r : ℝ) : Prop :=
  haveI : NeZero N := ⟨by omega⟩
  (Φ0 W).PhysRange r ∧
  ∃ (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)),
    ObserverCore W b Wf
      ∧ ExpandR Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ ClusterPM Wf cf
      ∧ FlowCovLim Wf cf
      ∧ FlowAF Wf cf
      ∧ FlowWard Wf cf
      ∧ ProxyNondeg Wf cf
      ∧ FlowGen hN2 W Wf cf (ZCanon.zFix N zri zwe) μ r
      ∧ FlowThreeLower Wf cf
      ∧ ObsRunSeedW N

/-- **`NarrowInputsAtObs'` is `NarrowInputsAtObs`** at the same `W`, `r` (`generation_iff_flowGen`, with
`ConvC` from `InputMerge.convC_of_finMom`). DERIVED: `2` the least colour count. -/
theorem narrowInputsAtObs'_iff (hN2 : 2 ≤ N) {W : ConfFlow N} {r : ℝ} :
    NarrowInputsAtObs' N hN2 W r ↔ NarrowInputsAtObs N hN2 W r := by
  haveI : NeZero N := ⟨by omega⟩
  constructor
  · rintro ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hcl, hV, hAF, hW, hP, hG, h3, hOS⟩
    have hC := convC_of_finMom S.b_pos S.mom hE
    exact ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hcl, hV, hAF, hW, hP,
      (generation_iff_flowGen hN2 hE hC).2 hG, h3, hOS⟩
  · rintro ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hcl, hV, hAF, hW, hP, hB, h3, hOS⟩
    have hC := convC_of_finMom S.b_pos S.mom hE
    exact ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hcl, hV, hAF, hW, hP,
      (generation_iff_flowGen hN2 hE hC).1 hB, h3, hOS⟩

/-- **`NarrowInputsAtObs'` is `InputMerge.NarrowInputsAtMin`** (`narrowInputsAtObs'_iff`,
`ObserverBundle.narrowInputsAtObs_iff_min`). DERIVED: `2` the least colour count. -/
theorem narrowInputsAtObs'_iff_min (hN2 : 2 ≤ N) {W : ConfFlow N} {r : ℝ} :
    NarrowInputsAtObs' N hN2 W r ↔ NarrowInputsAtMin N hN2 W r :=
  (narrowInputsAtObs'_iff hN2).trans (narrowInputsAtObs_iff_min hN2)

/-- **`ClayStatementDy` from `NarrowInputsAtObs'` at some observer and margin, at every `N ≥ 2`**
(`ObserverBundle.clayStatement_of_narrowAtObs`). DERIVED: `2` the least colour count. -/
theorem clayStatement_of_narrowAtObs'
    (h : ∀ (N : ℕ) (hN2 : 2 ≤ N), ∃ (W : ConfFlow N) (r : ℝ), NarrowInputsAtObs' N hN2 W r) :
    MassGap.ClayStatementDy :=
  clayStatement_of_narrowAtObs fun N hN2 => by
    obtain ⟨W, r, hA⟩ := h N hN2
    exact ⟨W, r, (narrowInputsAtObs'_iff hN2).1 hA⟩

/-! ## 3. The mixed kernel: what remains -/

/-- **The mixed flowed reading**: the composites of `P` replaced by their flowed proxies at scale `s`
(test functions reflected), the observer's flowed fields of `Q` kept, read in `stateK`. DERIVED: `0` the
plane. -/
def msMix [NeZero N] (W : ConfFlow N) (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ)
    (s : ℝ) (P : TMonoG Ix0) (Q : Mono N) : ℝ :=
  stateK (NeZero.ne N) k
    ((∏ i, smear (dySpacing N k) (msProx Wf cf k s (P.2 i).1) ((P.2 i).2.reflect 0))
      * ∏ j, smear (dySpacing N k) ((Φ0 W).field k (Q.2 j)).1.1 ((Φ0 W).field k (Q.2 j)).2)

/-- **The observer's double limit of the mixed reading**: `lim_{s → 0⁺} lim_ultra msMix`. DERIVED: `0`
the limit of the scale. -/
def obsMix [NeZero N] (W : ConfFlow N) (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ))
    (P : TMonoG Ix0) (Q : Mono N) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun s => limUnder (ultra : Filter ℕ) (fun k => msMix W Wf cf k s P Q))

/-- **The mixed small-flow-time expansion**: for every composite monomial `P`, every margin monomial `Q`
and `η > 0`, for all small `s > 0`, eventually along `ultra`, `|mixLatC(P, Q) − msMix(s, P, Q)| ≤ η`.
Not a clause of the bundle (module docstring, §3). DERIVED: `0` the plane and the limit of the scale. -/
def ExpandMix [NeZero N] (W : ConfFlow N) (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ))
    (z : Chan → ℕ → ℝ) (μ : OffMix) (r : ℝ) : Prop :=
  ∀ (P : TSepG (CRen N z μ).Ix 0) (Q : MarginMono N 0 r) (η : ℝ), 0 < η →
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
      |mixLatC (NeZero.ne N) (CRen N z μ) (Φ0 W) 0 k P.1 Q.1 - msMix W Wf cf k s P.1 Q.1| ≤ η

/-- **The bundle gives the convergence of the mixed readings** (`CompositesRen.mixConvG_of_cov`, with
`CompOS` from `InputMerge.compOS_of_min` and `af` from `FlowAF`). DERIVED: `2` the least colour count. -/
theorem mixConvG_of_obs (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {μ : OffMix}
    {b r : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (S : ObserverCore W b Wf)
    (hE : ExpandR Wf cf z μ) (hcl : ClusterPM Wf cf) (hV : FlowCovLim Wf cf) (hP : ProxyNondeg Wf cf)
    (hAF : FlowAF Wf cf) (hphys : (Φ0 W).PhysRange r) : MixConvG hN2 W (CRen N z μ) r := by
  obtain ⟨t, C, ht, hSE⟩ := uv_of_plaq S.b_pos S.top S.plaq
  have hU := ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) W ht hSE
  have hS := sepConv_of_finMom S.b_pos S.mom hE
  have hCO := compOS_of_min (min_of_core S ((af_iff_flowAF hS hE).2 hAF)) hE hcl hV hP
  exact mixConvG_of_cov hN2 W hU hphys (CRen N z μ)
    (unifLocal_buildRen (rhoD (fR N) z) (bareD (fR N) (bR N)) μ) (reflCovLat_CRen z μ) hCO

/-- **Under `MixConvG` and `ExpandMix`, the mixed kernel is the observer's double limit of the mixed
flowed reading**: `mixKG(P, Q) = sgn(P) · obsMix(P, Q)`. DERIVED: `2` the halving of `η`. -/
theorem mixKG_eq_obsMix (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {μ : OffMix}
    {r : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hMC : MixConvG hN2 W (CRen N z μ) r)
    (hX : ExpandMix W Wf cf z μ r) (P : TSepG (CRen N z μ).Ix 0) (Q : MarginMono N 0 r) :
    mixKG hN2 W (CRen N z μ) r P Q = sgnC (CRen N z μ) 0 P.1 * obsMix W Wf cf P.1 Q.1 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨x, hx⟩ := hMC P Q
  have hT : Tendsto (fun s => limUnder (ultra : Filter ℕ) (fun k => msMix W Wf cf k s P.1 Q.1))
      (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    filter_upwards [hX P Q (η / 2) (half_pos hη)] with s hs
    have h := FlowCovN.abs_sub_limUnder_le hx hs
    rw [Real.dist_eq, abs_sub_comm]
    linarith
  show sgnC (CRen N z μ) 0 P.1 * limUnder (ultra : Filter ℕ)
      (fun k => mixLatC (ne_zero_of_two_le hN2) (CRen N z μ) (Φ0 W) 0 k P.1 Q.1) = _
  rw [hx.limUnder_eq]
  unfold obsMix
  rw [hT.limUnder_eq]

/-- **The generation clause with the mixed kernel on the flowed readings**: `FlowGen` with `mixKG`
replaced by `sgn · obsMix`. Every kernel it reads is the observer's: the flowed readings `msLat`,
`msMix` and the Gram kernel `gramF`. DERIVED: `2` the cross-term factor; `0` the plane, the sign of `ε`
and the limit of the scale. -/
def FlowGenMix [NeZero N] (hN2 : 2 ≤ N) (W : ConfFlow N) (Wf : ℝ → ConfFlow N)
    (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (z : Chan → ℕ → ℝ) (μ : OffMix) (r : ℝ) : Prop :=
  ∀ P : TSepG (CRen N z μ).Ix 0, BeyondR r P → ∀ ε : ℝ, 0 < ε → ∃ c : MarginMono N 0 r →₀ ℝ,
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
      sgnC (CRen N z μ) 0 P.1 * msLat Wf cf k s (pairC (CRen N z μ) 0 P.1 P.1)
        - 2 * xL (fun Q : MarginMono N 0 r => sgnC (CRen N z μ) 0 P.1 * obsMix W Wf cf P.1 Q.1) c
        + gForm (gramF hN2 W r) c c ≤ ε

/-- **Under `MixConvG` and `ExpandMix`, `FlowGen` is `FlowGenMix`** (`mixKG_eq_obsMix`).
DERIVED: no numeral. -/
theorem flowGen_iff_mix (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {μ : OffMix}
    {r : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hMC : MixConvG hN2 W (CRen N z μ) r)
    (hX : ExpandMix W Wf cf z μ r) :
    FlowGen hN2 W Wf cf z μ r ↔ FlowGenMix hN2 W Wf cf z μ r := by
  have h : mixKG hN2 W (CRen N z μ) r
      = fun P Q => sgnC (CRen N z μ) 0 P.1 * obsMix W Wf cf P.1 Q.1 :=
    funext fun P => funext fun Q => mixKG_eq_obsMix hN2 hMC hX P Q
  unfold FlowGen FlowGenMix
  rw [h]

end MassGap.ObserverGen

end

#print axioms MassGap.ObserverGen.kernC_eq_obsLim
#print axioms MassGap.ObserverGen.kernC_diag_flowedN
#print axioms MassGap.ObserverGen.generation_iff_flowGen
#print axioms MassGap.ObserverGen.narrowInputsAtObs'_iff
#print axioms MassGap.ObserverGen.narrowInputsAtObs'_iff_min
#print axioms MassGap.ObserverGen.clayStatement_of_narrowAtObs'
#print axioms MassGap.ObserverGen.mixConvG_of_obs
#print axioms MassGap.ObserverGen.mixKG_eq_obsMix
#print axioms MassGap.ObserverGen.flowGen_iff_mix
