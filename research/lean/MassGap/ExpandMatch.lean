import Mathlib
import MassGap.ApertureCount
import MassGap.ExpandRF

/-!
# MassGap.ExpandMatch — the part of `ExpandStrong` the single-observer route reads

`ApertureCount.clayStatementOf_of_apertureCount` carries, along every coupling tower, the copy of
`StrongExpand.ExpandStrong Wf cf z μ`: a bilinear rate clause (for every monomial `P` and every family `F`,
two reflected readings matched at rate `(s/d)^ε` with one constant `K_r`) and a membership clause. This
module reads every consumer of that field on the route, states the clause that is read (`ExpandMatch`),
re-proves every consumer from it, and states the root with `ExpandMatch` in place of `ExpandStrong`.
Declarations are in the namespace `MassGap.ExpandMatch`.

## 1. What the route reads (proved, by the proofs below)

The field enters `ObserverTowerCL.coreClausesWCL` twice:

* through `expandR_of_strong` (the empty monomial), whose consumers there are `convC_of_chan`,
  `os0C_of_cluster`, `os1C_of_chan`, `sepConv_of_chan`, `covC_of_flowCovLim`, `compNondeg_of_proxy` and
  `wardT_of_flowWard`. The module `MassGap.ExpandRF` (namespace `MassGap.ExpandFam`) re-proves `OS0C` from
  the clause `ExpandRF` (per-composite constants), and all the others from its germ `ExpandLim` (no rate,
  no ratio, no constant);
* through `ProxyGenLimN.eventually_expandRP` inside `ProxyGenLimN.approxK_of_germ`: for every separated
  positive-time monomial `P` and `η > 0`, for all small `s > 0`, eventually along `ultra`, the proxy
  product `B^s(P)` in the half-space algebra and `⟪A(P) − B^s(P), A(P) − B^s(P)⟫ ≤ η`. That is `RPGerm`.

So `ExpandMatch Wf cf z μ := ExpandRF Wf cf z μ ∧ RPGerm Wf cf z μ`.

## 2. Why it is weaker (proved where stated)

* `expandMatch_of_strong`: `ExpandStrong → ExpandMatch` (`expandR_of_strong`, `expandRF_of_expandR`,
  `eventually_expandRP`). So `coreWAM_of_coreWAC`: the bundle of `clayStatementOf_of_apertureCount` gives the
  bundle of `clayStatementOf_of_apertureMatch`.
* What `ExpandMatch` drops (argued, by reading the two clauses). The bilinear clause at every pair
  `(P, F)` with `F ≠ P`; the proxy-left, composite-right bound as a separate statement; the rate
  `(s/d)^ε` and the constants of the reflected reading at every `P ≠ ∅` (`RPGerm` is a germ); the single
  constant `K_r` at `P = ∅` (`ExpandRF` has one per composite; `ExpandRF` §5 argues the free field meets
  it and fails `ExpandR` once `n² > K_r`). `ExpandRF` keeps a rate `(s/d)^ε` for every family read alone.
* `germ_without_rate`: on the remainder form, a germ is a strictly larger class than a rate. The
  remainder `(−log s)⁻¹` tends to `0` at `0⁺` and is bounded by no `K s^ε`, `ε > 0`, on any `(0, θ]`.
  This separates the two forms of a real remainder; no lattice model is given in which `ExpandMatch`
  holds and `ExpandStrong` fails, so the strictness of `expandMatch_of_strong` is not proved.

## 3. The load-bearing tests (proved)

* Not met by the zero coefficients. `contC_eq_zero_of_expandLim_zero`: at `cf = 0` every proxy is `0`, so
  `ExpandLim` forces every separated composite reading to `0`; `not_compNondeg_of_expandMatch_zero`:
  `ExpandMatch Wf 0 z μ` contradicts `CompNondeg (CRen N z μ)` at every `SU(N)` as soon as one combination
  has a non-zero on-shell top-dimension classical part (the `ExpandRF` component alone is read). That
  premise is `NondegFromProxy.OnShellTopN N c`, met at every `N ≥ 2` by `FlowChoice.exists_onShellTopN`.
  The capstone's chain derives `CompNondeg` from the same bundle (`compNondeg_of_proxyL`), so at `N ≥ 2`
  no bundle with `cf = 0` and `ProxyNondeg` exists.
* The mixed reading cannot be dropped from `RPGerm`. `form_sub_split`: for a symmetric bilinear form,
  `⟪A − B, A − B⟫ = (⟪A, A⟫ − ⟪B, B⟫) − 2(⟪B, A⟫ − ⟪B, B⟫)`, so `germ_of_split`: the diagonal germ and
  the mixed germ give the reflection-norm germ. `diag_not_enough`: on `ℝ²` with the dot product (a positive
  form), `A = (0, 1)`, `B = (1, 0)` constant in `s` have the diagonal germ (`⟪A, A⟫ − ⟪B, B⟫ = 0`) and
  `⟪A − B, A − B⟫` does not tend to `0`. Every consumer of `ExpandR` reads one family at a time on the
  diagonal (`ExpandLim`); this abstract model (not a lattice model) shows that a diagonal reading, with
  the mixed term dropped, does not in general give the bound `⟪A − B^s, A − B^s⟫ ≤ η` that
  `approxK_of_rpGerm` reads. `ProxyCov.rpGerm_iff_mixGerm`: under `ExpandLim` and the coefficients' parity
  `ProxyCov.CfParity` (the flowed proxies are then reflection covariant with the composites' signs), the
  diagonal germ holds (`ProxyCov.diag_germ`) and `RPGerm` is equivalent to the mixed germ
  `ProxyCov.MixGerm` alone.

## 4. The route

* `approxK_of_rpGerm`: `ProxyGenLimN.approxK_of_germ` with `RPGerm` in place of `ExpandStrong`.
* `coreClausesWAM`: `ObserverTowerCL.coreClausesWCL` with `ExpandMatch` in place of `ExpandStrong`.
* Copied over the coupling family by `#along_generalize_more` (kernel-checked; no copy mentions `dyBeta`).
* `CoreInputsAlongWAM N βs`: `ApertureCount.CoreInputsAlongWAC` with the copy of `ExpandMatch` in place of the
  copy of `ExpandStrong`. `openAlongW_of_coreWAM`; **`clayStatementOf_of_apertureMatch`**: `StrongEnd N`,
  the settling window reading and `CoreInputsAlongWAM` along the towers near `0⁺` give
  `ClayStatementOf (SU N)`.

## 5. What remains argued

`ExpandMatch` is a hypothesis. That the lattice composites and their flowed proxies meet it (the
small-flow-time expansion inside a reflected correlation, per family, as `s → 0⁺`) is argued from the free
field (`ExpandRF` §5), not proved. No Lean proof of a non-perturbative small-flow-time expansion exists in
the repository or the archive.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the plane, the signs, the zero coefficients, the limit point and the diagonal
difference; `1` the unit vectors of `ℝ²` and the bound of the contradiction; `2` the parallelogram factor,
the least colour count and the two points; `4` the split `ε = 2 (ε/4) + 2 (ε/4)`; `2`, `1`, `3`, `4` in
`(2 · 1 + 3)⁴` the unit cube's site count.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ExpandMatch

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
  MassGap.ProxyGenLimN MassGap.ScalePC MassGap.ScalePM MassGap.ClusterRoute MassGap.ObserverTowerCL

variable {N : ℕ}

/-! ## 1. The clause -/

/-- **The reflection-norm germ**: for every separated positive-time monomial `P` and `η > 0`, for all small
`s > 0`, eventually along `ultra`, the proxy product in the half-space algebra and
`⟪A_k − B_k^s, A_k − B_k^s⟫_k ≤ η`. Module docstring, §1. DERIVED: `0` the plane and the limit point. -/
def RPGerm [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (z : Chan → ℕ → ℝ)
    (μ : OffMix) : Prop :=
  ∀ (P : TSepG (CRen N z μ).Ix 0) (η : ℝ), 0 < η →
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
      proxB Wf cf k s P.1 ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0
      ∧ rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0)
          (prodSmear (dySpacing N k) (cMono (NeZero.ne N) (CRen N z μ) k P.1) - proxB Wf cf k s P.1)
          (prodSmear (dySpacing N k) (cMono (NeZero.ne N) (CRen N z μ) k P.1) - proxB Wf cf k s P.1)
        ≤ η

/-- **The expansion clause the single-observer route reads**: `ExpandRF` and `RPGerm`. Module docstring,
§1. DERIVED: no numeral. -/
def ExpandMatch [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (z : Chan → ℕ → ℝ)
    (μ : OffMix) : Prop :=
  ExpandFam.ExpandRF Wf cf z μ ∧ RPGerm Wf cf z μ

/-- **`ExpandStrong` gives `ExpandMatch`.** DERIVED: no numeral. -/
theorem expandMatch_of_strong [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (h : ExpandStrong Wf cf z μ) : ExpandMatch Wf cf z μ :=
  ⟨ExpandFam.expandRF_of_expandR (expandR_of_strong h), fun P _ hη => eventually_expandRP h P hη⟩

/-! ## 2. A germ is weaker than a rate -/

/-- **A germ with no rate**: `(−log s)⁻¹ → 0` at `0⁺`, and no `K s^ε`, `ε > 0`, bounds it on any `(0, θ]`.
DERIVED: `0` the limit point; `1` the bound of the contradiction. -/
theorem germ_without_rate :
    Tendsto (fun s : ℝ => (-Real.log s)⁻¹) (𝓝[>] 0) (𝓝 0)
      ∧ ∀ K ε θ : ℝ, 0 < ε → 0 < θ →
        ¬ ∀ s : ℝ, 0 < s → s ≤ θ → (-Real.log s)⁻¹ ≤ K * s ^ ε := by
  refine ⟨tendsto_inv_atTop_zero.comp (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero), ?_⟩
  intro K ε θ hε hθ H
  have hT : Tendsto (fun s : ℝ => K * (Real.log s * s ^ ε)) (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_log_mul_rpow_nhdsGT_zero hε).const_mul K
    rwa [mul_zero] at h
  have hb1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), |K * (Real.log s * s ^ ε)| < 1 :=
    (Metric.tendsto_nhds.1 hT 1 one_pos).mono fun s hs => by
      rwa [Real.dist_eq, sub_zero] at hs
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      |K * (Real.log s * s ^ ε)| < 1 ∧ s < θ ∧ s < 1 ∧ 0 < s :=
    hb1.and (((gt_mem_nhds hθ).filter_mono nhdsWithin_le_nhds).and
      (((gt_mem_nhds one_pos).filter_mono nhdsWithin_le_nhds).and
        (eventually_mem_nhdsWithin.mono fun s hs => hs)))
  obtain ⟨s, h1, h2, h3, h4⟩ := hev.exists
  have hlog : Real.log s < 0 := Real.log_neg h4 h3
  have hpos : 0 < -Real.log s := by linarith
  have hb := mul_le_mul_of_nonneg_right (H s h4 h2.le) hpos.le
  rw [inv_mul_cancel₀ hpos.ne'] at hb
  have e : K * s ^ ε * -Real.log s = -(K * (Real.log s * s ^ ε)) := by ring
  rw [e] at hb
  linarith [(abs_lt.1 h1).1]

/-! ## 3. The load-bearing tests -/

/-- **At `cf = 0`, `ExpandLim` forces every non-empty separated composite reading to `0`.**
DERIVED: `0` the zero coefficients and the limit. -/
theorem contC_eq_zero_of_expandLim_zero [NeZero N] {Wf : ℝ → ConfFlow N} {z : Chan → ℕ → ℝ} {μ : OffMix}
    (h : ExpandFam.ExpandLim Wf 0 z μ) {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (F : ι → CDatum (CRen N z μ)) {d : ℝ} (hd : 0 < d) (hc : ContD F) (hs : SepD d F) :
    contC (NeZero.ne N) (CRen N z μ) F = 0 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hz : ∀ k s, msLat Wf 0 k s F = 0 := fun k s => by
    unfold msLat
    rw [Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary ι))
      (by rw [msProx_zero, smear_zero_field]), MassGap.DLRLimit.State.map_zero]
  have hT : Tendsto (fun k => latC (NeZero.ne N) (CRen N z μ) k F) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    obtain ⟨s, hk⟩ := (h ι F ⟨hc, d, hd, hs⟩ (η / 2) (half_pos hη)).exists
    filter_upwards [hk] with k hk
    rw [hz, sub_zero] at hk
    rw [Real.dist_eq, sub_zero]
    linarith
  exact (hT.mono_left ultra_le).limUnder_eq

/-- **`ExpandMatch` at the zero coefficients contradicts `CompNondeg`** as soon as one combination has a
non-zero on-shell top-dimension classical part, at every `SU(N)`. DERIVED: `0` the zero coefficients;
`2` the two points. -/
theorem not_compNondeg_of_expandMatch_zero [NeZero N] {Wf : ℝ → ConfFlow N} {z : Chan → ℕ → ℝ}
    {μ : OffMix} (h : ExpandMatch Wf 0 z μ) (c : Ix0 →₀ ℝ)
    (hon : ∃ (A : GPot N) (g : ℝ), GPot.Adm A ∧ OnShell g A
      ∧ ∑ i ∈ c.support.filter (fun i => cdim i.1 = c.support.sup (fun j => cdim j.1)),
          c i * g ^ cnF i.1 * cval g A i.1 ≠ 0) :
    ¬ CompNondeg (NeZero.ne N) (CRen N z μ) := by
  have hL := ExpandFam.expandLim_of_expandRF h.1
  refine not_compNondeg_comb (NeZero.ne N) (CRen N z μ) c hon fun f g hf hg hsep => ?_
  obtain ⟨d, hd, hfg⟩ := hsep
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  have hc : ContD (![(i, f), (j, g)] : Fin 2 → CDatum (CRen N z μ)) := by
    intro x
    fin_cases x
    exacts [hf, hg]
  have hgf : ContinuumSep.sepBy d g f := fun y w hy hw => by
    obtain ⟨m, hm⟩ := hfg w y hw hy
    exact ⟨m, by rw [abs_sub_comm]; exact hm⟩
  have hs : SepD d (![(i, f), (j, g)] : Fin 2 → CDatum (CRen N z μ)) := by
    intro x y hxy
    fin_cases x <;> fin_cases y
    · exact (hxy rfl).elim
    · exact hfg
    · exact hgf
    · exact (hxy rfl).elim
  rw [contC_eq_zero_of_expandLim_zero hL _ hd hc hs, mul_zero]

section Form

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **The reflection-norm distance splits into a diagonal and a mixed difference** for a symmetric
bilinear form. DERIVED: `2` the parallelogram factor. -/
theorem form_sub_split (f : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : ∀ x y, f x y = f y x) (A B : V) :
    f (A - B) (A - B) = (f A A - f B B) - 2 * (f B A - f B B) := by
  simp only [map_sub, LinearMap.sub_apply]
  rw [hs A B]
  ring

/-- **The diagonal germ and the mixed germ give the reflection-norm germ.** DERIVED: `0` the limit;
`2` the parallelogram factor. -/
theorem germ_of_split {α : Type*} {l : Filter α} (f : α → V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hs : ∀ a x y, f a x y = f a y x) (A B : α → V)
    (hd : Tendsto (fun a => f a (A a) (A a) - f a (B a) (B a)) l (𝓝 0))
    (hm : Tendsto (fun a => f a (B a) (A a) - f a (B a) (B a)) l (𝓝 0)) :
    Tendsto (fun a => f a (A a - B a) (A a - B a)) l (𝓝 0) := by
  have h := hd.sub (hm.const_mul 2)
  rw [mul_zero, sub_zero] at h
  exact h.congr fun a => (form_sub_split (f a) (hs a) (A a) (B a)).symm

end Form

/-- The dot product on `ℝ²` as a bilinear form. DERIVED: no numeral. -/
def dotF : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => x.1 * y.1 + x.2 * y.2)
    (fun x x' y => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun c x y => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (fun x y y' => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun c x y => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)

/-- **The diagonal germ does not give the reflection-norm germ.** On `ℝ²` with the dot product (symmetric,
positive), the constant families `A = (0, 1)`, `B = (1, 0)` have `⟪A, A⟫ − ⟪B, B⟫ → 0`, and
`⟪A − B, A − B⟫` does not tend to `0` at `0⁺`. DERIVED: `0` the coordinates, the diagonal difference and
the limit point; `1` the unit vectors. -/
theorem diag_not_enough :
    (∀ x y, dotF x y = dotF y x) ∧ (∀ x, 0 ≤ dotF x x)
      ∧ Tendsto (fun _ : ℝ => dotF ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), (1 : ℝ))
          - dotF ((1 : ℝ), (0 : ℝ)) ((1 : ℝ), (0 : ℝ))) (𝓝[>] 0) (𝓝 0)
      ∧ ¬ Tendsto (fun _ : ℝ => dotF (((0 : ℝ), (1 : ℝ)) - ((1 : ℝ), (0 : ℝ)))
          (((0 : ℝ), (1 : ℝ)) - ((1 : ℝ), (0 : ℝ)))) (𝓝[>] 0) (𝓝 0) := by
  refine ⟨fun x y => ?_, fun x => ?_, ?_, ?_⟩
  · simp only [dotF, LinearMap.mk₂_apply]
    ring
  · simp only [dotF, LinearMap.mk₂_apply]
    exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  · simp only [dotF, LinearMap.mk₂_apply]
    norm_num
  · rw [tendsto_const_nhds_iff]
    simp only [dotF, LinearMap.mk₂_apply, Prod.fst_sub, Prod.snd_sub]
    norm_num

/-! ## 4. The consumers -/

/-- **`ApproxK` from `RPGerm` and the germ**, at every `SU(N)` (`ProxyGenLimN.approxK_of_germ`'s proof
with `RPGerm` in place of `eventually_expandRP`). DERIVED: `4` and `2` the split
`ε = 2 (ε/4) + 2 (ε/4)`; `2` the least colour count; `0` the plane. -/
theorem approxK_of_rpGerm (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {t C : ℝ}
    (hU : ClassMoments (NeZero.ne N) W (SymPlaqClass N) t C) {r : ℝ} (hphys : (Φ0 W).PhysRange r)
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hCO : CompOS (NeZero.ne N) (CRen N z μ)) {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hE : RPGerm Wf cf z μ) (hG : ProxyGenGerm W Wf cf r) :
    ApproxK (kernC (NeZero.ne N) (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r)
      (gramF hN2 W r) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hUL : UnifLocal (CRen N z μ) := unifLocal_buildRen (rhoD (fR N) z) (bareD (fR N) (bR N)) μ
  have hcov : ReflCovLat (CRen N z μ) 0 := reflCovLat_CRen z μ
  have hMC := mixConvG_of_cov hN2 W hU hphys (CRen N z μ) hUL hcov hCO
  have hRL := reflLimG_of_cov hN2 W (CRen N z μ) r hcov hCO hMC
  have hpos := Flow.posPreserving_of_physRange (NeZero.ne N) (Φ0 W) hphys 0
  intro P ε hε
  obtain ⟨s, ⟨a, ha⟩, hEs⟩ := ((hG P (ε / 4) (by positivity)).and_eventually
    (hE P (ε / 4) (by positivity))).exists
  refine ⟨a, ?_⟩
  have hX : Tendsto (fun k => xL (fun Q : MarginMono N 0 r =>
      rMixC (NeZero.ne N) (CRen N z μ) (Φ0 W) 0 k P.1 Q.1) a) (ultra : Filter ℕ)
      (𝓝 (xL (mixKG hN2 W (CRen N z μ) r P) a)) :=
    tendsto_xL (g := fun k (Q : MarginMono N 0 r) => rMixC (NeZero.ne N) (CRen N z μ) (Φ0 W) 0 k P.1 Q.1)
      (fun Q => hRL.2 P Q) a
  have hGr : Tendsto (fun k => gForm (fun Q Q' : MarginMono N 0 r =>
      latSF (NeZero.ne N) (Φ0 W) k (pairFam 0 Q.1 Q'.1)) a a) (ultra : Filter ℕ)
      (𝓝 (gForm (gramF hN2 W r) a a)) :=
    tendsto_gForm (G := fun k (Q Q' : MarginMono N 0 r) => latSF (NeZero.ne N) (Φ0 W) k (pairFam 0 Q.1 Q'.1))
      (fun Q Q' => tendsto_contSF (NeZero.ne N) (Φ0 W) (ClaySUGap.uB (NeZero.ne N) W hU) (pairFam 0 Q.1 Q'.1)) a
  have hT := (((hRL.1 P P).sub (hX.const_mul 2)).add hGr).congr fun k =>
    (rform_sub_yW W z μ k P.1 a).symm
  have hQ : ∀ᶠ k in atTop, ∀ Q ∈ a.support, prodSmear (dySpacing N k) ((Φ0 W).mono k Q.1)
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 :=
    (Filter.eventually_all_finset a.support).mpr fun Q _ => eventually_flow_mem (Φ0 W) hpos Q
  have hev : ∀ᶠ k in (ultra : Filter ℕ),
      rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0)
        (prodSmear (dySpacing N k) (cMono (NeZero.ne N) (CRen N z μ) k P.1) - yW W k a)
        (prodSmear (dySpacing N k) (cMono (NeZero.ne N) (CRen N z μ) k P.1) - yW W k a) ≤ ε := by
    filter_upwards [hEs, ha, (eventually_cMono_mem (NeZero.ne N) (CRen N z μ) hUL P).filter_mono ultra_le,
      hQ.filter_mono ultra_le] with k hk1 hk2 hA hY
    have hYm : yW W k a ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 :=
      Submodule.sum_mem _ fun Q hQ => Submodule.smul_mem _ _ (hY Q hQ)
    have hp := rform_para_le (rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0))
      (rform_symm_k k)
      (prodSmear (dySpacing N k) (cMono (NeZero.ne N) (CRen N z μ) k P.1)) (proxB Wf cf k s P.1) (yW W k a)
      (by
        rw [rform_apply]
        exact stateK_rp (NeZero.ne N) k 0 _ (sub_mem (sub_mem hA hk1.1) (sub_mem hk1.1 hYm)))
    linarith [hk1.2]
  exact le_of_tendsto hT hev

/-- **The flow-side clauses at any observer with a physical range, from `ExpandMatch`**:
`ObserverTowerCL.coreClausesWCL` with `ExpandMatch` in place of `ExpandStrong` (`ExpandFam`'s consumers
from `ExpandLim` and `ExpandRF`, `approxK_of_rpGerm`). DERIVED: `2` the least rank; `0` the plane; `2`, `1`,
`3`, `4` in `(2 · 1 + 3)⁴` the unit cube's site count. -/
theorem coreClausesWAM (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {r : ℝ} (hphys : (Φ0 W).PhysRange r)
    {zri zwe : ℕ → ℝ} {μ : OffMix} {b : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCoreCL W (ZCanon.zFix N zri zwe) b Wf)
    (hE : ExpandMatch Wf cf (ZCanon.zFix N zri zwe) μ) (hcl : ClusterPM Wf cf)
    (hV : FlowCovN.FlowCovLim Wf cf) (hW : WardFromLattice.FlowWard Wf cf) (hP : ProxyNondeg Wf cf)
    (hL : ProxyGenLimN.ProxyGenLimGerm W b Wf cf r)
    (h3 : ∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (NeZero.ne N) ℓ) :
    (∃ t C : ℝ, 0 < t ∧ FlowUV.SiteExp (NeZero.ne N) W (SymPlaqClass N) (t * (2 * 1 + 3) ^ 4) C)
      ∧ (∃ G : ℝ → ℝ, TwoPointKernel (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe)) G
          ∧ AFCoefficient N G)
      ∧ NonGaussianT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe))
      ∧ WardT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe))
      ∧ CompOS (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ ApproxK (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
          (mixKG hN2 W (CRen N (ZCanon.zFix N zri zwe) μ) r) (gramF hN2 W r) := by
  have hLim := ExpandFam.expandLim_of_expandRF hE.1
  have hm := InputMerge.finMom_of_chan S.scale
  obtain ⟨t, C, ht, hS⟩ := uv_of_chan S.b_pos S.top S.scale
  have hU := ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) W ht hS
  have hCv := ExpandFam.convC_of_finMomL S.b_pos hm hLim
  have hSep := ExpandFam.sepConv_of_finMomL S.b_pos hm hLim
  have hCO : CompOS (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) :=
    ⟨hCv, ExpandFam.os0C_of_clusterF hCv hE.1 hcl, ExpandFam.os1C_of_finMomL S.b_pos hm hLim,
      ExpandFam.covC_of_flowCovLimL hLim hCv hV, ExpandFam.compNondeg_of_proxyL hLim hCv hP⟩
  obtain ⟨ℓ, hℓ, h3'⟩ := h3
  exact ⟨⟨t, C, ht, hS⟩, S.af,
    InputsTriage.nonGaussianT_rhoD_of_lower (NeZero.ne N) (fR N) (ZCanon.zFix N zri zwe) hSep
      (obsLower_of_scale (NeZero.ne N) hℓ zri zwe h3'),
    ExpandFam.wardT_of_flowWardL hSep hLim hW, hCO,
    approxK_of_rpGerm hN2 hU hphys hCO hE.2
      (ProxyGenLimN.germ_of_limGerm (uB_of_coreCL S) (proxyBound_of_coreCL S) hL)⟩

end MassGap.ExpandMatch

end

/-! ### The copy over a coupling family -/

namespace MassGap.ExpandMatch

set_option Elab.async false in
set_option maxHeartbeats 0 in
#along_generalize_more MassGap.ContinuumSchwinger.dyBeta from MassGap.ExpandMatch.coreClausesWAM
  MassGap.ExpandMatch.expandMatch_of_strong

-- No copy mentions the source (every copy in `MassGap.CouplingGen.Along`, the new ones included).
run_cmd do
  let env ← Lean.getEnv
  let src := ``MassGap.ContinuumSchwinger.dyBeta
  let pre := `MassGap.CouplingGen.Along
  for (c, ci) in env.constants.map₂.toList do
    if pre.isPrefixOf c then
      let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
      if used.contains src then
        throwError "copy {c} still mentions {src}"

end MassGap.ExpandMatch

/-! ## 5. The root -/

noncomputable section

namespace MassGap.ExpandMatch

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.ClayTreeG MassGap.ClayStatementG MassGap.FlowG Filter
open scoped Topology
open MassGap.FlowAlong (cpl schedAlongG_eq)
open MassGap.CouplingTower (StrongEnd CouplingTower UVConverges)
open MassGap.CompositeLink (Φ0)
open MassGap.CompositesRen (OffMix)
open MassGap.ObserverTower (OpenAlongW ApproxAlongW physRangeG_of_physRange energy0G_alongW
  clayStatementOf_of_openW)
open MassGap.ScaleLightCone (ZoomSettlesUV uvConverges_of_zoomSettlesUV)
open MassGap.ApertureCount (CoreInputsAlongWAC)

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

variable (N) in
/-- **The flow-side bundle along `βs` with the aperture count and the read expansion**:
`ApertureCount.CoreInputsAlongWAC` with the copy of `ExpandMatch` in place of the copy of `ExpandStrong`,
every other field unchanged. DERIVED: `0` the signs. -/
def CoreInputsAlongWAM (βs : ℕ → ℝ) : Prop :=
  ∃ (W : ConfFlow N) (r : ℝ) (_ : (Φ0 W).PhysRange r)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : CompositesBuild.Ix0 → ℝ → (MultiScaleAll.MIx →₀ ℝ)),
    0 < b ∧ Wf b = W
      ∧ CouplingGen.Along.ApertureCount.ApertureCount (cpl βs) (ZCanon.zFix N zri zwe) b Wf
      ∧ CouplingGen.Along.ExpandMatch.ExpandMatch (cpl βs) Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ CouplingGen.Along.ScaleLightCone.ZoomSettles (cpl βs) Wf cf
      ∧ CouplingGen.Along.FlowCovN.FlowCovLim (cpl βs) Wf cf
      ∧ CouplingGen.Along.WardFromLattice.FlowWard (cpl βs) Wf cf
      ∧ CouplingGen.Along.NondegFromProxy.ProxyNondeg (cpl βs) Wf cf
      ∧ CouplingGen.Along.ProxyGenLimN.ProxyGenLimGerm (cpl βs) W b Wf cf r
      ∧ ∃ ℓ : ℝ, 0 < ℓ
          ∧ CouplingGen.Along.NonGaussFromScale.ThreePointAtScale (cpl βs) (NeZero.ne N) ℓ

omit [Fact (2 ≤ N)] in
/-- **The aperture-count bundle gives the read-expansion bundle** (the copy of `expandMatch_of_strong` at
`cpl βs`). DERIVED: no numeral. -/
theorem coreWAM_of_coreWAC {βs : ℕ → ℝ} (h : CoreInputsAlongWAC N βs) : CoreInputsAlongWAM N βs := by
  obtain ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, hb, htop, hZ, hE, F⟩ := h
  exact ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, hb, htop, hZ,
    CouplingGen.Along.ExpandMatch.expandMatch_of_strong (cpl βs) hE, F⟩

set_option maxRecDepth 100000 in
/-- **`CoreInputsAlongWAM ⇒ OpenAlongW`**: the clauses of `OpenAlongW` at `W.toG` from the copies of
`substrateCoreCL_of_apertureCount`, `clusterPM_of_zoomSettles` and `coreClausesWAM` at `cpl βs`, in the
schedule form along `βs` (as `ObserverTowerCL.openAlongW_of_coreWCL`). DERIVED: `0` the signs; `2`, `1`,
`3`, `4` in `(2 · 1 + 3)⁴` the unit cube's site count; `2` the least rank. -/
theorem openAlongW_of_coreWAM {βs : ℕ → ℝ} (h : CoreInputsAlongWAM N βs) : OpenAlongW N βs := by
  obtain ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, hb, htop, hZ, hE, hz, hV, hW, hP, hL, h3⟩ := h
  have S := CouplingGen.Along.ApertureCount.substrateCoreCL_of_apertureCount (cpl βs) (Fact.out : 2 ≤ N)
    hb htop hZ
  have hcl := CouplingGen.Along.ScaleLightCone.clusterPM_of_zoomSettles (cpl βs) hz
  obtain ⟨⟨t, C, ht, hSE⟩, ⟨Gk, hK, hAF⟩, hNG, hWT, hCO, hA⟩ :=
    CouplingGen.Along.ExpandMatch.coreClausesWAM (cpl βs) (Fact.out : 2 ≤ N) hphys S hE hcl hV hW hP
      hL h3
  have hsched := schedAlongG_eq (N := N) βs
  refine ⟨W.toG, r, physRangeG_of_physRange βs hphys, t * (2 * 1 + 3) ^ 4, C, by positivity, ?_, zri, zwe,
    hri, hwe, μ, ⟨Gk, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hsched]
    exact hSE
  · rw [hsched]
    exact hK
  · rw [constsG_SU N]
    exact hAF
  · rw [hsched]
    exact hNG
  · rw [hsched]
    exact hWT
  · rw [hsched]
    exact hCO
  · unfold ApproxAlongW
    rw [hsched, energy0G_alongW βs W]
    exact hA

/-- **The root at `SU(N)` from the strong end, the separated zoom, the aperture count and the read
expansion**: `StrongEnd N`, the settling window reading and `CoreInputsAlongWAM` along the towers near `0⁺`
give `ClayStatementOf (SU N)`. Its hypothesis `hF` is implied by that of
`ApertureCount.clayStatementOf_of_apertureCount` (`coreWAM_of_coreWAC`). DERIVED: `0` the limit `0⁺`. -/
theorem clayStatementOf_of_apertureMatch (hS : StrongEnd N)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ZoomSettlesUV N βs)
    (hF : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      CoreInputsAlongWAM N βs) :
    ClayStatementOf (MassGap.SUN.SU N) :=
  clayStatementOf_of_openW hS (hUV.mono fun _ h βs hT => uvConverges_of_zoomSettlesUV (h βs hT))
    (hF.mono fun _ h βs hT => openAlongW_of_coreWAM (h βs hT))

end MassGap.ExpandMatch

end

#print axioms MassGap.ExpandMatch.expandMatch_of_strong
#print axioms MassGap.ExpandMatch.germ_without_rate
#print axioms MassGap.ExpandMatch.contC_eq_zero_of_expandLim_zero
#print axioms MassGap.ExpandMatch.not_compNondeg_of_expandMatch_zero
#print axioms MassGap.ExpandMatch.form_sub_split
#print axioms MassGap.ExpandMatch.germ_of_split
#print axioms MassGap.ExpandMatch.diag_not_enough
#print axioms MassGap.ExpandMatch.approxK_of_rpGerm
#print axioms MassGap.ExpandMatch.coreClausesWAM
#print axioms MassGap.CouplingGen.Along.ExpandMatch.coreClausesWAM
#print axioms MassGap.CouplingGen.Along.ExpandMatch.expandMatch_of_strong
#print axioms MassGap.ExpandMatch.coreWAM_of_coreWAC
#print axioms MassGap.ExpandMatch.openAlongW_of_coreWAM
#print axioms MassGap.ExpandMatch.clayStatementOf_of_apertureMatch
