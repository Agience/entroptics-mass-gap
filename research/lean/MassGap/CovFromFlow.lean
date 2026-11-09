import Mathlib
import MassGap.ExpandStrong

/-!
# MassGap.CovFromFlow — `CovC` of the renormalised composites from the covariance of the flowed proxies

The target asks `CovC (CRen 2 z μ)` (`ClayStatement.CovC`: for
every `R ∈ O(4)` and every admissible family `F = (iⱼ, fⱼ)`, the lattice readings of `(iⱼ, fⱼ ∘ R)` converge
along `ultra` to `∑_σ ∏ⱼ rep R iⱼ σⱼ · contC((σⱼ, fⱼ))`). This module replaces that input by a clause on the
flowed proxies at fixed flow scale, `FlowCov`, and derives `CovC` from it with the expansion `ExpandR` and
`ConvC`. Declarations are in the namespace `MassGap.CovFromFlow`.

## 1. The clause

`FlowCovAt Wf cf s`: for every `R ∈ O(4)` and every admissible family `F`, the flowed readings
`msLat Wf cf k s` of the rotated family `(iⱼ, fⱼ ∘ R)` converge along `ultra` to
`∑_σ ∏ⱼ repF R iⱼ σⱼ · lim_ultra msLat Wf cf k s ((σⱼ, fⱼ))`. It reads the flowed proxies
`msProx Wf cf k s` at one scale `s`, the state `stateK` and the composite representation `repF` (the `rep`
field of `CRen 2 z μ`); it reads no composite field, no `latC`, no `contC`.

`FlowCov Wf cf`: `FlowCovAt Wf cf s` holds for scales `s > 0` arbitrarily close to `0`
(`∃ᶠ s in 𝓝[>] 0`). It is not asked at every scale.

## 2. What is proved

* `FlowCovAt`, `FlowCov`, `covC_of_flowCov` and `covC_of_scale_strong` (`scale`, `ExpandStrong` and
  `FlowCov` give `CovC (CRen N z μ)`) are stated at every `SU(N)` (`[NeZero N]`); `covC_of_strong` reads
  the `SU(2)` record `MultiScaleStrongAt`.
* `orth_transpose_mul`: `R ∈ O(4)` gives `Rᵀ R = 1`.
* `continuous_rotTest'`: a continuous test function rotated by `R` is continuous.
* `sum_sq_mulVec`: `∑ₙ (R v)ₙ² = ∑ₙ vₙ²` for `Rᵀ R = 1`.
* `sepBy_rotTest`: if `f`, `g` are `d`-separated (sup-distance, `ContinuumSep.sepBy`) then `f ∘ R`, `g ∘ R`
  are `d/2`-separated. The supports' difference `v` has `|(R v)ₘ| ≥ d` for some `m`, so `∑ vₙ² ≥ d²`, and
  four coordinates each below `d/2` give `∑ vₙ² < d²`. A rotation does not preserve the sup-distance; the
  factor `1/2` is `√4` (the dimension) and is absorbed by the rate.
* `tendsto_of_scales`: a real-analysis lemma along `ultra`. If `vₓ → Tₓ` for `x ∈ S`, and for every `η > 0`
  there are sequences `w`, `wₓ` with `|u − w| ≤ e`, `|vₓ − wₓ| ≤ eₓ` eventually, `w → ∑ₓ pₓ lim wₓ`, and
  `e + ∑ₓ |pₓ| eₓ < η`, then `u → ∑ₓ pₓ Tₓ`. Each `wₓ` converges along the ultrafilter because it is
  eventually bounded (`MixConvRP.exists_tendsto_ultra_of_ultra`), and `|Tₓ − lim wₓ| ≤ eₓ`.
* **`covC_of_flowCov`**: `ExpandR Wf cf z μ`, `ConvC (CRen 2 z μ)` and `FlowCov Wf cf` give
  `CovC (CRen 2 z μ)`. For `F` admissible at separation `d`: the rotated family is continuous and
  `d/2`-separated, so `ExpandR` bounds `|latC(F∘R) − msLat_s(F∘R)|` by `A (s/(d/2))^ε`; each index family
  `(σⱼ, fⱼ)` has the test functions of `F`, so it is admissible at `d` and `ExpandR` bounds
  `|latC − msLat_s|` there by `B_σ (s/d)^ε`; `ConvC` gives `latC((σⱼ, fⱼ)) → contC((σⱼ, fⱼ))`. The constants
  `A`, `B_σ` do not depend on `s`. Choosing `s` with `FlowCovAt s`, `s < θ d/2` and both rates below `η/2`
  (possible since the good scales accumulate at `0`), `tendsto_of_scales` closes.
* `covC_of_strong`: `MultiScaleStrongAt W z μ b Wf cf` and `FlowCov Wf cf` give `CovC (CRen 2 z μ)`
  (`ConvC` from `CompositesRenAll.convC_ren_of_all`, `ExpandR` from `StrongExpand.expandR_of_strong`).
* No `ClayStatement` capstone is stated from `MultiScaleStrongAt`: its `endpoint` field,
  `MultiScale.Endpoint`, is refuted by `InputAudit.not_multiScaleEndpoint` under the argued growth of the
  zero-flux level count.

## 3. Argued (no declaration)

* **Why `FlowCov` is expected.** At fixed physical flow scale `s` the flowed fields `Wf s` are smooth on the
  scale `√s`; their lattice readings have continuum limits as `a_k → 0`, and the continuum gradient flow is
  `O(4)` covariant, so the hypercubic artefacts of the flowed monomials vanish in the limit. The proxy
  `∑ⱼ cf i s j · msFlow j` is covariant with the composites' representation when the coefficients `cf · s`
  intertwine the rotation of the flowed monomials with `repF`, as the coefficients of the continuum
  small-flow-time expansion do. Neither step is proved here.
* **Not derivable from the present inputs.** `Wf` is a free input. `ScaleControlAll`, `ExpandStrong`,
  `ProxyGen` and `CoefBound` bound moments, rates and coefficient sizes; none states a symmetry of `Wf s` or
  an intertwining of `cf`. The exact signed-permutation covariance of the lattice (`ObserverRotation`,
  `ObserverAxisN`) and the reduction of `SO(4)` to one rotation plus orbit continuity
  (`ObserverRotationDense.observerSO4_of_pyth`) are proved for invariant scalar readings of a flow, not for
  the covariant proxy readings with `repF`; carrying them to `FlowCovAt` would need the hypercubic
  covariance of `msProx` (a property of `Wf` and `cf`) and a version of that reduction for covariant
  readings.
* **Non-circular.** `FlowCov` reads the proxies at a fixed scale, where the fields are smooth; `CovC` reads
  the composites, whose lattice fields are not. Given `ExpandR` and `ConvC`, `CovC` implies covariance of
  the proxies only up to the rate `(s/d)^ε`, not `FlowCovAt` at any one scale; `FlowCov` asks for exact
  covariance of the proxies' limits at scales accumulating at `0`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` is `SU(2)`, the halving of the separation (`√4`, the dimension) and of `η`, and the
limits of the scalar and pseudoscalar factors; `4` the dimension; `0` the limit of the scale; `1` the
identity and the margin around the limit.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.CovFromFlow

open Filter
open scoped Topology Matrix
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
  MassGap.MultiScaleOS MassGap.ApproxFromExpand MassGap.StrongExpand

local notation "h2N" => (ne_zero_of_two_le (le_refl 2) : (2 : ℕ) ≠ 0)

variable {N : ℕ}

/-! ## 1. The clause -/

/-- **Covariance of the flowed proxies at scale `s`**: module docstring, §1.
DERIVED: `4` the dimension. -/
def FlowCovAt [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (s : ℝ) : Prop :=
  ∀ R : Matrix (Fin 4) (Fin 4) ℝ, R ∈ Matrix.orthogonalGroup (Fin 4) ℝ →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → Ix0 × TestFn), Adm F →
      Tendsto (fun k => msLat Wf cf k s (fun i => ((F i).1, rotTest R (F i).2))) (ultra : Filter ℕ)
        (𝓝 (∑ σ ∈ Fintype.piFinset (fun i => (repF R (F i).1).support),
          (∏ i, repF R (F i).1 (σ i))
            * limUnder (ultra : Filter ℕ) (fun k => msLat Wf cf k s (fun i => (σ i, (F i).2)))))

/-- **The flowed proxies are covariant at scales arbitrarily close to `0`**: module docstring, §1.
DERIVED: `0` the limit of the scale. -/
def FlowCov [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) : Prop :=
  ∃ᶠ s in 𝓝[>] (0 : ℝ), FlowCovAt Wf cf s

/-! ## 2. Rotated test functions -/

/-- `R ∈ O(4)` gives `Rᵀ R = 1`. DERIVED: `4` the dimension; `1` the identity. -/
theorem orth_transpose_mul {R : Matrix (Fin 4) (Fin 4) ℝ} (hR : R ∈ Matrix.orthogonalGroup (Fin 4) ℝ) :
    Rᵀ * R = 1 := by
  have h := hR
  rw [Matrix.mem_orthogonalGroup_iff'] at h
  simpa using h

/-- A continuous test function rotated by `R` is continuous. DERIVED: `4` the dimension; `1` the
identity. -/
theorem continuous_rotTest' {R : Matrix (Fin 4) (Fin 4) ℝ} (hR : Rᵀ * R = 1) {f : TestFn}
    (hf : Continuous f.1) : Continuous (rotTest R f).1 := by
  have e : (rotTest R f).1 = fun y => f.1 (R.mulVec y) := funext (rotTest_apply R hR f)
  rw [e]
  exact hf.comp (Continuous.matrix_mulVec continuous_const continuous_id)

/-- `∑ₙ (R v)ₙ² = ∑ₙ vₙ²` for `Rᵀ R = 1`. DERIVED: `4` the dimension; `1` the identity; `2` the square. -/
theorem sum_sq_mulVec {R : Matrix (Fin 4) (Fin 4) ℝ} (hR : Rᵀ * R = 1) (v : Fin 4 → ℝ) :
    ∑ n, (R.mulVec v n) ^ 2 = ∑ n, v n ^ 2 := by
  have h : dotProduct (R.mulVec v) (R.mulVec v) = dotProduct v v := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hR,
      Matrix.one_mulVec]
  simpa [dotProduct, sq] using h

/-- **A rotation halves the sup-distance separation at worst**: module docstring, §2.
DERIVED: `2` the factor `√4`; `4` the dimension. -/
theorem sepBy_rotTest {R : Matrix (Fin 4) (Fin 4) ℝ} (hR : Rᵀ * R = 1) {d : ℝ} (hd : 0 < d)
    {f g : TestFn} (h : ContinuumSep.sepBy d f g) :
    ContinuumSep.sepBy (d / 2) (rotTest R f) (rotTest R g) := by
  intro y w hy hw
  rw [rotTest_apply R hR] at hy hw
  obtain ⟨m, hm⟩ := h _ _ hy hw
  by_contra hcon
  push Not at hcon
  have hv : ∀ n, (y - w) n ^ 2 < (d / 2) ^ 2 := fun n => by
    have h1 := hcon n
    have h0 := abs_nonneg (y n - w n)
    have h2 := sq_abs (y n - w n)
    rw [Pi.sub_apply]
    nlinarith
  have hsum : ∑ n, (y - w) n ^ 2 < d ^ 2 := by
    rw [Fin.sum_univ_four]
    nlinarith [hv 0, hv 1, hv 2, hv 3]
  have e : R.mulVec (y - w) m = R.mulVec y m - R.mulVec w m := by
    rw [Matrix.mulVec_sub, Pi.sub_apply]
  have hm2 : d ^ 2 ≤ (R.mulVec (y - w) m) ^ 2 := by
    rw [e]
    have h0 := abs_nonneg (R.mulVec y m - R.mulVec w m)
    have h2 := sq_abs (R.mulVec y m - R.mulVec w m)
    nlinarith
  have hle : (R.mulVec (y - w) m) ^ 2 ≤ ∑ n, (R.mulVec (y - w) n) ^ 2 :=
    Finset.single_le_sum (f := fun n => (R.mulVec (y - w) n) ^ 2) (fun n _ => sq_nonneg _)
      (Finset.mem_univ m)
  rw [sum_sq_mulVec hR] at hle
  linarith

/-! ## 3. Convergence along `ultra` through approximating sequences -/

/-- **Convergence through approximating sequences**: module docstring, §2.
DERIVED: `2` the halving of `η`; `1` the margin around the limit. -/
theorem tendsto_of_scales {X : Type} (S : Finset X) (p : X → ℝ) (u : ℕ → ℝ) (v : X → ℕ → ℝ)
    (T : X → ℝ) (hv : ∀ x ∈ S, Tendsto (v x) (ultra : Filter ℕ) (𝓝 (T x)))
    (h : ∀ η : ℝ, 0 < η → ∃ (w : ℕ → ℝ) (wx : X → ℕ → ℝ) (e : ℝ) (ex : X → ℝ),
      (∀ᶠ k in (ultra : Filter ℕ), |u k - w k| ≤ e)
      ∧ (∀ x ∈ S, ∀ᶠ k in (ultra : Filter ℕ), |v x k - wx x k| ≤ ex x)
      ∧ Tendsto w (ultra : Filter ℕ) (𝓝 (∑ x ∈ S, p x * limUnder (ultra : Filter ℕ) (wx x)))
      ∧ e + ∑ x ∈ S, |p x| * ex x < η) :
    Tendsto u (ultra : Filter ℕ) (𝓝 (∑ x ∈ S, p x * T x)) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨w, wx, e, ex, h1, h2, h3, h4⟩ := h (η / 2) (half_pos hη)
  have hL : ∀ x ∈ S, |T x - limUnder (ultra : Filter ℕ) (wx x)| ≤ ex x := by
    intro x hx
    have hb : ∀ᶠ k in (ultra : Filter ℕ), |wx x k| ≤ |T x| + 1 + ex x := by
      filter_upwards [h2 x hx, (hv x hx).abs.eventually (gt_mem_nhds (lt_add_one |T x|))]
        with k hk hk'
      have h5 := abs_sub_abs_le_abs_sub (wx x k) (v x k)
      rw [abs_sub_comm] at h5
      linarith
    obtain ⟨y, hy⟩ := exists_tendsto_ultra_of_ultra (wx x) _ hb
    rw [hy.limUnder_eq]
    exact le_of_tendsto (((hv x hx).sub hy).abs) (h2 x hx)
  have hM : |∑ x ∈ S, p x * limUnder (ultra : Filter ℕ) (wx x) - ∑ x ∈ S, p x * T x|
      ≤ ∑ x ∈ S, |p x| * ex x := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
    rw [← mul_sub, abs_mul, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left (hL x hx) (abs_nonneg _)
  filter_upwards [h1, Metric.tendsto_nhds.1 h3 (η / 2) (half_pos hη)] with k hk1 hk3
  rw [Real.dist_eq] at hk3 ⊢
  have i1 := abs_sub_le (u k) (w k) (∑ x ∈ S, p x * T x)
  have i2 := abs_sub_le (w k) (∑ x ∈ S, p x * limUnder (ultra : Filter ℕ) (wx x))
    (∑ x ∈ S, p x * T x)
  linarith

/-! ## 4. `CovC` from `FlowCov` -/

/-- **`CovC` from the expansion, `ConvC` and the covariance of the flowed proxies**: module docstring,
§2. DERIVED: `2` the halving of the separation and of `η`; `0` the limit of the scale. -/
theorem covC_of_flowCov [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ}
    {μ : OffMix} (hE : ExpandR Wf cf z μ) (hC : ConvC (NeZero.ne N) (CRen N z μ)) (hF : FlowCov Wf cf) :
    CovC (NeZero.ne N) (CRen N z μ) := by
  obtain ⟨θ, ε, Kr, κr, hθ, hε, hEx⟩ := hE
  intro R hR ι _ _ F hFa
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
  have hFadm : Adm F := ⟨hcont, d, hd, hsep⟩
  let A : ℝ := Kr ^ Fintype.card ι * ∏ i, ((d / 2) ^ κr (F i).1)⁻¹ * l1 (rotTest R (F i).2)
  let B : (ι → Ix0) → ℝ := fun σ => Kr ^ Fintype.card ι * ∏ i, ((d ^ κr (σ i))⁻¹ * l1 (F i).2)
  let S : Finset (ι → Ix0) := Fintype.piFinset (fun i => (repF R (F i).1).support)
  let p : (ι → Ix0) → ℝ := fun σ => ∏ i, repF R (F i).1 (σ i)
  let c : ℝ := ∑ σ ∈ S, |p σ| * B σ
  show Tendsto (fun k => latC (NeZero.ne N) (CRen N z μ) k (fun i => ((F i).1, rotTest R (F i).2)))
    (ultra : Filter ℕ) (𝓝 (∑ σ ∈ S, p σ * contC (NeZero.ne N) (CRen N z μ) (fun i => (σ i, (F i).2))))
  refine tendsto_of_scales S p _ (fun σ k => latC (NeZero.ne N) (CRen N z μ) k (fun i => (σ i, (F i).2)))
    (fun σ => contC (NeZero.ne N) (CRen N z μ) (fun i => (σ i, (F i).2)))
    (fun σ _ => hC ι _ ⟨hSc σ, d, hd, hSs σ⟩) fun η hη => ?_
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      A * (s / (d / 2)) ^ ε < η / 2 ∧ c * (s / d) ^ ε < η / 2 ∧ s < θ * (d / 2) ∧ 0 < s :=
    (eventually_rate_lt hε A (half_pos hη)).and ((eventually_rate_lt hε c (half_pos hη)).and
      (((gt_mem_nhds (mul_pos hθ hd2)).filter_mono nhdsWithin_le_nhds).and
        (eventually_mem_nhdsWithin.mono fun s hs => hs)))
  obtain ⟨s, hfs, hs1, hs2, hs3, hs4⟩ := (hF.and_eventually hev).exists
  have hsd : s ≤ θ * d := by
    have := mul_pos hθ hd
    linarith
  refine ⟨fun k => msLat Wf cf k s (fun i => ((F i).1, rotTest R (F i).2)),
    fun σ k => msLat Wf cf k s (fun i => (σ i, (F i).2)),
    A * (s / (d / 2)) ^ ε, fun σ => B σ * (s / d) ^ ε, ?_, ?_, ?_, ?_⟩
  · filter_upwards [(hEx ι _ (d / 2) hd2 hGc hGs s hs4 hs3.le).filter_mono ultra_le] with k hk
    dsimp only [A] at hk ⊢
    refine hk.trans (le_of_eq ?_)
    ring
  · intro σ _
    filter_upwards [(hEx ι _ d hd (hSc σ) (hSs σ) s hs4 hsd).filter_mono ultra_le] with k hk
    dsimp only [B] at hk ⊢
    refine hk.trans (le_of_eq ?_)
    ring
  · exact hfs R hR ι F hFadm
  · have hsum : ∑ σ ∈ S, |p σ| * (B σ * (s / d) ^ ε) = c * (s / d) ^ ε := by
      show _ = (∑ σ ∈ S, |p σ| * B σ) * (s / d) ^ ε
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun σ _ => by ring
    show A * (s / (d / 2)) ^ ε + ∑ σ ∈ S, |p σ| * (B σ * (s / d) ^ ε) < η
    rw [hsum]
    linarith

/-- **`CovC` from the scale clause, `ExpandStrong` and `FlowCov`**, at every `SU(N)` (`ConvC` from
`boundC_ren_of_scale_expand`, `ExpandR` from `expandR_of_strong`). -/
theorem covC_of_scale_strong [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hsc : ScaleControlAll b Wf)
    (hE : ExpandStrong Wf cf z μ) (hF : FlowCov Wf cf) : CovC (NeZero.ne N) (CRen N z μ) :=
  covC_of_flowCov (expandR_of_strong hE)
    ((InputsTriage.convC_iff_boundC _ _).2 (boundC_ren_of_scale_expand hb hsc (expandR_of_strong hE))) hF

/-- **`CovC` from the multi-scale statement and `FlowCov`** (`convC_ren_of_all`, `expandR_of_strong`). -/
theorem covC_of_strong {W : ConfFlow 2} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow 2} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (H : MultiScaleStrongAt W z μ b Wf cf)
    (hF : FlowCov Wf cf) : CovC h2N (CRen 2 z μ) :=
  covC_of_flowCov (expandR_of_strong H.expand) (convC_ren_of_all ⟨b, Wf, cf, H.toRenAt⟩) hF

end MassGap.CovFromFlow

end

#print axioms MassGap.CovFromFlow.orth_transpose_mul
#print axioms MassGap.CovFromFlow.continuous_rotTest'
#print axioms MassGap.CovFromFlow.sum_sq_mulVec
#print axioms MassGap.CovFromFlow.sepBy_rotTest
#print axioms MassGap.CovFromFlow.tendsto_of_scales
#print axioms MassGap.CovFromFlow.covC_of_flowCov
#print axioms MassGap.CovFromFlow.covC_of_scale_strong
#print axioms MassGap.CovFromFlow.covC_of_strong
