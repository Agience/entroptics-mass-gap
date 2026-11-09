import Mathlib
import MassGap.ProxyGenObserver

/-!
# MassGap.ProxyBoundFromScale — `ProxyBound` from the substrate

`ProxyGenObserver.proxyGen_iff` splits `ProxyGen` into `ProxyBound W b Wf cf r` and
`ProxyGenLim W b Wf cf r`. This module proves `ProxyBound W b Wf cf r` from the substrate's scale
clause `ScaleControlAll b Wf` and the observer's `UniformBoundF (Φ0 W)`, for every coefficient family
`cf` and every `r`. Declarations
are in the namespace `MassGap.ProxyBoundFromScale`.

Notation as in `ProxyGenObserver`: `B_k^s(P) = proxB Wf cf k s P`, `V_k(Q) = prodSmear a_k ((Φ0 W).mono k Q)`,
`⟪X, Y⟫_k = ν_k(θX · Y)`, `θ = ireflObs 0 0`, `ν_k = stateK k`.

Every declaration of §1–§2, `proxyBound_of_scale` and `proxyBound_of_core` are stated at every `SU(N)`
(`[NeZero N]`); `proxyBound_of_substrate` is at `SU(2)`.

## 1. The reflected reading against the squares (proved)

* `abs_rform_le`: `|⟪X, Y⟫_k| ≤ (ν_k(X²) + ν_k(Y²)) / 2`. Pointwise `|θX · Y| ≤ ((θX)² + Y²)/2`,
  `(θX)² = θ(X²)` (precomposition), and `ν_k ∘ θ = ν_k` (`ContinuumNontrivial.stateK_refl`). No
  half-space membership is used.

## 2. The squares are bounded (proved)

* `proxB_sq_eq`: `ν_k(B_k^s(P)²) = msLat Wf cf k s (P ⊔ P)`, the flowed reading of the doubled family.
* `eventually_proxB_sq_le`: under `ScaleControlAll b Wf`, at `0 < s ≤ b`, `|ν_k(B_k^s(P)²)|` is bounded
  eventually in the step (`MultiScaleAll.abs_msLat_le` on the doubled family, once `a_k ≤ s` and
  `a_k ≤ 1`). The bound depends on `s` through `msPsize`; no bound on the coefficients `cf` is used.
* `obs_sq_eq`: `ν_k(V_k(Q)²) = latSF (Φ0 W) k (Q ⊔ Q)`.
* `eventually_obs_sq_le`: under `UniformBoundF (Φ0 W)`, `|ν_k(V_k(Q)²)|` is bounded eventually along
  `ultra` (`ContinuumFlow.tendsto_contSF` on the doubled family).

## 3. `ProxyBound` (proved)

* **`proxyBound_of_scale`**: `ScaleControlAll b Wf` and `UniformBoundF (Φ0 W)` give
  `ProxyBound W b Wf cf r`.
* `proxyBound_of_core`: `SubstrateCoreAt W z b Wf` gives `ProxyBound W b Wf cf r` at every `SU(N)`.
* **`proxyBound_of_substrate`**: `SubstrateAt W z b Wf` gives `ProxyBound W b Wf cf r`
  (`SubstrateAt.scale`, `ProxyGenObserver.uB_of_substrate`).
* No `ClayStatementAt` capstone is stated through `SubstrateAt`: its `endpoint` field,
  `MultiScale.Endpoint`, is refuted by `InputAudit.not_multiScaleEndpoint` under the argued growth of the zero-flux level count.
  `SUNFromScale` states the `SU(N)` capstone through `SubstrateCoreAt` with the gap `RunSeed N` as an input.

Of the two clauses of `ProxyGenObserver.proxyGen_iff`, the uniform bound is discharged here; the
generation statement `ProxyGenLim` remains an input.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the plane, the reflection constant and the lower end of the scale; `1` the
spacing bound and the margin above each limit; `2` `SU(2)`, the doubling of a family and the mean.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ProxyBoundFromScale

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
  MassGap.ObserverChoice MassGap.SU2Best MassGap.NondegFromProxy MassGap.NonGaussFromScale
  MassGap.ProxyGenObserver
open MassGap.ScaleControlFull (zOne)

local notation "h2N" => (ne_zero_of_two_le (le_refl 2) : (2 : ℕ) ≠ 0)

variable {N : ℕ}

/-! ## 1. The reflected reading against the squares -/

/-- **The reflected reading is at most the mean of the squares' readings**:
`|ν_k(θX · Y)| ≤ (ν_k(X²) + ν_k(Y²)) / 2`. DERIVED: `0` the plane and the reflection constant; `2` the
mean. -/
theorem abs_rform_le [NeZero N] (k : ℕ) (X Y : C(Cfg N, ℝ)) :
    |rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) X Y|
      ≤ (stateK (NeZero.ne N) k (X * X) + stateK (NeZero.ne N) k (Y * Y)) / 2 := by
  have key : ∀ a c : ℝ, |a * c| ≤ 1 / 2 * (a * a + c * c) := fun a c => by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (a - c), sq_nonneg (a + c)]
  have hpt : ∀ U, |(LatticeReflection.ireflObs 0 0 X * Y) U|
      ≤ ((1 / 2 : ℝ) • (LatticeReflection.ireflObs 0 0 (X * X) + Y * Y)) U := by
    intro U
    simp only [ContinuousMap.mul_apply, ContinuousMap.smul_apply, ContinuousMap.add_apply,
      LatticeReflection.ireflObs_apply, smul_eq_mul]
    exact key _ _
  have h := abs_state_le_of_abs_le (stateK (NeZero.ne N) k) _ _ hpt
  rw [(stateK (NeZero.ne N) k).map_smul, (stateK (NeZero.ne N) k).map_add,
    MassGap.ContinuumNontrivial.stateK_refl] at h
  rw [rform_apply]
  linarith

/-! ## 2. The squares are bounded -/

/-- **The square of a proxy product is the flowed reading of the doubled family.**
DERIVED: `2` the doubling. -/
theorem proxB_sq_eq [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ) (s : ℝ)
    (P : TMonoG Ix0) :
    stateK (NeZero.ne N) k (proxB Wf cf k s P * proxB Wf cf k s P)
      = msLat Wf cf k s (Sum.elim P.2 P.2 : Fin P.1 ⊕ Fin P.1 → CDatum (CbR N zOne)) := by
  unfold msLat proxB
  rw [Fintype.prod_sum_type]
  rfl

/-- **The square of a proxy product is bounded uniformly in the step**: under `ScaleControlAll b Wf`,
at `0 < s ≤ b`, eventually in the step. DERIVED: `0` the lower end of the scale; `1` the spacing
bound. -/
theorem eventually_proxB_sq_le [NeZero N] {b : ℝ} {Wf : ℝ → ConfFlow N} (cf : Ix0 → ℝ → (MIx →₀ ℝ))
    (hsc : ScaleControlAll b Wf) (P : TMonoG Ix0) {s : ℝ} (hs : 0 < s) (hsb : s ≤ b) :
    ∃ C : ℝ, ∀ᶠ k in atTop, |stateK (NeZero.ne N) k (proxB Wf cf k s P * proxB Wf cf k s P)| ≤ C := by
  obtain ⟨t, C, γ, γP, ht, hev⟩ := hsc
  set F : Fin P.1 ⊕ Fin P.1 → CDatum (CbR N zOne) := Sum.elim P.2 P.2 with hF
  refine ⟨(1 + Fintype.card (Fin P.1 ⊕ Fin P.1)
      * (((2 * Fintype.card (Fin P.1 ⊕ Fin P.1)).factorial : ℝ) * (Real.exp C * C)))
      * ∏ i, (msTsize (F i).2 * msPsize t γ γP cf s (F i).1), ?_⟩
  filter_upwards [hev, (tendsto_dySpacing N).eventually (gt_mem_nhds hs),
    (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)] with k hk hks hk1
  rw [proxB_sq_eq]
  exact abs_msLat_le Wf cf ht hs hk1.le (hk s hks.le hsb) F

/-- **The square of an observer monomial is the flowed reading of the doubled family.**
DERIVED: `2` the doubling. -/
theorem obs_sq_eq [NeZero N] (W : ConfFlow N) (k : ℕ) (Q : Mono N) :
    stateK (NeZero.ne N) k (prodSmear (dySpacing N k) ((Φ0 W).mono k Q)
        * prodSmear (dySpacing N k) ((Φ0 W).mono k Q))
      = latSF (NeZero.ne N) (Φ0 W) k (Sum.elim Q.2 Q.2) := by
  unfold latSF latSk latS prodSmear
  rw [Fintype.prod_sum_type]
  rfl

/-- **The square of an observer monomial is bounded along `ultra`** under `UniformBoundF (Φ0 W)`.
DERIVED: `1` the margin above the limit. -/
theorem eventually_obs_sq_le [NeZero N] {W : ConfFlow N} (hB : UniformBoundF (NeZero.ne N) (Φ0 W)) (Q : Mono N) :
    ∃ C : ℝ, ∀ᶠ k in (ultra : Filter ℕ),
      |stateK (NeZero.ne N) k (prodSmear (dySpacing N k) ((Φ0 W).mono k Q)
        * prodSmear (dySpacing N k) ((Φ0 W).mono k Q))| ≤ C := by
  have hT := (continuous_abs.tendsto _).comp (tendsto_contSF (NeZero.ne N) (Φ0 W) hB (Sum.elim Q.2 Q.2))
  refine ⟨|contSF (NeZero.ne N) (Φ0 W) (Sum.elim Q.2 Q.2)| + 1, ?_⟩
  filter_upwards [hT.eventually (gt_mem_nhds (lt_add_one _))] with k hk
  rw [obs_sq_eq]
  exact hk.le

/-! ## 3. `ProxyBound` -/

/-- **`ProxyBound` from the scale clause and the observer's uniform bound.** Module docstring, §3.
DERIVED: `2` the mean. -/
theorem proxyBound_of_scale [NeZero N] {W : ConfFlow N} {b r : ℝ} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hsc : ScaleControlAll b Wf) (hB : UniformBoundF (NeZero.ne N) (Φ0 W)) :
    ProxyBound W b Wf cf r := by
  intro P s hs hsb
  obtain ⟨CB, hCB⟩ := eventually_proxB_sq_le cf hsc P.1 hs hsb
  have hCB' := hCB.filter_mono ultra_le
  refine ⟨⟨CB, hCB'.mono fun k hk => ?_⟩, fun Q => ?_⟩
  · have h := abs_rform_le k (proxB Wf cf k s P.1) (proxB Wf cf k s P.1)
    unfold proxD
    linarith [le_abs_self (stateK (NeZero.ne N) k (proxB Wf cf k s P.1 * proxB Wf cf k s P.1))]
  · obtain ⟨CV, hCV⟩ := eventually_obs_sq_le hB Q.1
    refine ⟨(CB + CV) / 2, ?_⟩
    filter_upwards [hCB', hCV] with k hk hv
    have h := abs_rform_le k (proxB Wf cf k s P.1) (prodSmear (dySpacing N k) ((Φ0 W).mono k Q.1))
    unfold proxX
    linarith [le_abs_self (stateK (NeZero.ne N) k (proxB Wf cf k s P.1 * proxB Wf cf k s P.1)),
      le_abs_self (stateK (NeZero.ne N) k (prodSmear (dySpacing N k) ((Φ0 W).mono k Q.1)
        * prodSmear (dySpacing N k) ((Φ0 W).mono k Q.1)))]

/-- **`ProxyBound` from the substrate core**, at every `SU(N)`, for every coefficient family `cf` and
every `r`. DERIVED: no numeral. -/
theorem proxyBound_of_core [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {b r : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (S : SubstrateCoreAt W z b Wf) :
    ProxyBound W b Wf cf r :=
  proxyBound_of_scale S.scale (uB_of_core S)

/-- **`ProxyBound` from the substrate**, for every coefficient family `cf` and every `r`.
DERIVED: no numeral. -/
theorem proxyBound_of_substrate {W : ConfFlow 2} {z : Chan → ℕ → ℝ} {b r : ℝ}
    {Wf : ℝ → ConfFlow 2} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (S : SubstrateAt W z b Wf) :
    ProxyBound W b Wf cf r :=
  proxyBound_of_scale S.scale (uB_of_substrate S)

end MassGap.ProxyBoundFromScale

end

#print axioms MassGap.ProxyBoundFromScale.abs_rform_le
#print axioms MassGap.ProxyBoundFromScale.proxB_sq_eq
#print axioms MassGap.ProxyBoundFromScale.eventually_proxB_sq_le
#print axioms MassGap.ProxyBoundFromScale.obs_sq_eq
#print axioms MassGap.ProxyBoundFromScale.eventually_obs_sq_le
#print axioms MassGap.ProxyBoundFromScale.proxyBound_of_scale
#print axioms MassGap.ProxyBoundFromScale.proxyBound_of_core
#print axioms MassGap.ProxyBoundFromScale.proxyBound_of_substrate
