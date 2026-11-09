import Mathlib
import MassGap.ScalePC

/-!
# MassGap.ScalePM — the scale input as per-channel moments of every order

`ScalePC.ScaleControlAllPC b Wf` asks, per channel `j`, an exponential moment
`ν_k(exp(tⱼ a_k^{−d_j} |O_j ∘ V_k^{(s)}|)) ≤ Cⱼ`, eventually in the step and uniformly in `s ∈ [a_k, b]`. This
module states the weakest moment input the capstone's consumers read, `ScaleControlAllPM`, proves that
`ScaleControlAllPC` gives it, and re-proves every consumer from it. Declarations are in the namespace `MassGap.ScalePM`.

## 1. What each consumer reads

* `uv` (`ScalePC.uv_of_scalePC`, then `ClaySUFinal.classMoments_of_siteExp`): the plaquette class only, at the
  one scale `s = b`, as the exponential moment `FlowUV.SiteExp` with one constant over the class.
  `ObserverOSEuclidS.ClassMoments` is `CubeMomentsAt` at every field of the class:
  `∀ᶠ k, ∀ R ≥ 0, ∀ p, ν_k(cubeSum_R^{2p}) ≤ ((2R + 1)⁴)^{2p} (2p)! t^{−2p} C`, every even moment with
  `(2p)!` growth, uniformly in `p` at each step; that is an exponential moment of the cube sum. It is read
  by `abs_latSF_le_M` at `p = n`, the number of insertions, inside `capData` and the energy chain. The
  plaquette class has dimension `4`; `ScaleControlAllPM` keeps the exponential form for it, at `s = b` only
  (field `top`).
* `BoundC`, `ConvC`, `OS1C` (the `msLat` chain): at one `s` and one family of `n` composites, the `2n`-th
  moment of `msFlow j` for each channel `j` in the finite support of the family's coefficients, eventually in
  the step. Each consumer fixes `s` and `n` before the limit in `k`, so the eventual threshold may depend on
  `s` and `p`; and the bound `B` of `BoundC` is per family, so for these three a finite bound at each
  `(j, s, p)` would do.
* `OS0C`: the same moments with `n` unbounded, and the bound must be `α γⁿ (n!)^β ∏ᵢ Ccᵢ …` with one `β`.
  Through `ObserverOS.abs_state_prod_le` the factor constant is common to the `n` factors; a channel growth
  `ν_k(msFlow_j^{2p}) ≤ Kⱼ ((2p)!)^r μ_j(s)^{−2p}` with one `r ≥ 1` over all channels closes it with
  `α = 2^r + θ'^ε`, `γ = 8^r`, `β = 2r` (`one_add_mul_factPow_le`). With an index `rⱼ` per channel, `n`
  insertions of one channel give `((2n)!)^{rⱼ}`, about `γⁿ (n!)^{2rⱼ}`, which no fixed `β` bounds once
  `2rⱼ > β`.

## 2. The statement

* `ScaleChanPM Wf r t K γ γP k s j p`: `ν_k(msFlow_j(s)^{2p}) ≤ ((2p)!)^r / μ_j(s)^{2p} · K`, on the centred
  flowed monomial `msFlow` (`a_k^{−d_j}(O_j ∘ V_k^{(s)} − ν_k(·))`), the quantity the chain reads.
* `ScalePMAt b Wf r γ γP`: `1 ≤ r`; for every channel `j` (monomial or plaquette) one `tⱼ > 0`, `Kⱼ` with
  `∀ s ∈ (0, b], ∀ p, ∀ᶠ k, ScaleChanPM Wf r tⱼ Kⱼ γ γP k s j p`; and one `t > 0`, `C` with, eventually in
  the step, `ScaleChan Wf t C γ γP k b (inr q)` for every plaquette `q` (the class at `s = b`).
* `ScaleControlAllPM b Wf`: `∃ r γ γP, ScalePMAt b Wf r γ γP`.

Against `ScaleControlAllPC` it is weaker in four ways: the moment order `p` and the scale `s` are fixed
before the step tends to infinity (`∀ s ∀ p ∀ᶠ k`, not `∀ᶠ k ∀ s ∀ p`); the growth in `p` is
`((2p)!)^r` for any one `r ≥ 1`, not `(2p)!`; the plaquette class is exponential at `s = b` only; and
the moments are of the centred monomial.

## 3. What is proved

* `scaleChanPM_of_scaleChan`, `scaleControlAllPM_of_scaleControlAllPC` (at `b > 0`, with `r = 1`,
  `K = e^C C`, `MultiScaleAll.state_pow_le_of_exp` through `ScalePC.msFlow_moment_chan`).
* `scaleChanPM_mono`, `ScalePMAt.uniform` (one `t`, `K ≥ 1` on a finite channel set, for every `s`, `p`).
* The chain: `msProx_moment_pm`, `abs_msLat_le_on_pm`, `abs_msLat_le_wS_pm`, `abs_contC_le_pm`,
  `msLat_translate_sub_tendsto_pm`, `one_add_mul_factPow_le`.
* The consumers: `uv_of_scalePM`, `boundC_ren_of_scalePM`, `convC_of_scalePM`, `os1C_of_scalePM`,
  `os0C_of_scalePM`.
* `SubstrateCorePM`, `substrateCorePM_of_corePC`, `compOS_of_covC_pm`, `approxK_of_beyond_covC_pm`,
  `inputsAt_of_covC_phys_pm`, `NarrowInputsAtPM`, `narrowInputsAtPM_of_narrowAtPC`,
  `clayInputsN_of_narrowAtPM`. No `ClayStatement` capstone is stated from `NarrowInputsAtPM`: it carries
  `RunSeedN.EndpointN N`, refuted by `EndpointAudit.not_endpointN_of_levels_unbounded` under the argued growth
  of the zero-flux level count.

## 4. The positivity lower bound (argued; no declaration)

`ScalePC` §3 argues a lower bound `ν_k(|O_j ∘ V_k − ν_k(·)| > ρ) ≥ exp(−c (s/a_k)⁴ log(s/a_k))` from
positivity of the Wilson state near the `π`-flux configuration, which conflicts with the exponential tail of
`ScaleChan` once `d_j > 4`. At fixed `s` and `p` the same bound gives
`ν_k(msFlow_j^{2p}) ≥ (ρ a_k^{−d_j})^{2p} exp(−c (s/a_k)⁴ log(s/a_k))`, which tends to `0` as `k → ∞`: a
polynomial factor against a factor smaller than every power of `a_k`. It puts no floor under the limit at
any fixed order, so it does not conflict with `ScaleChanPM` at any `d_j` and any `r`. The conflict needs
orders `p` of size `(s/a_k)⁴` or more, growing with the step, and `ScaleControlAllPM` fixes `p` before the
step grows.

What `ScaleControlAllPM` still asks is that the flowed moments at `s > 0` converge with growth
`((2p)!)^r` in `p`, with one `r` over the channel tower. If the flowed composite of dimension `d_j` is close
to a polynomial of degree `d_j / 2` in a near-Gaussian flowed field strength, its `2p`-th moments grow like
`((2p)!)^{d_j/4}`, so a common `r` holds on channels of dimension `≤ 4r` and not above. That limit belongs
to this route, not to `OS0C`. `OS0C` bounds only separated families (`SepD d F`), and the massive free field
meets it with `β = 0`: at separation `d` the Wick expansion of `n` Wick-ordered composites of degrees `mᵢ`
has no pairing inside a factor, and the Cauchy bound gives `|S| ≤ ∏ᵢ (e K mᵢ)^{mᵢ/2}` with
`K = supᵢ ∑ⱼ G(xᵢ − xⱼ) ≤ c d^{−4}`, a factor per composite; growth in `n!` appears only at coincident
points or without a mass. The route loses the separation: `ObserverOS.abs_state_prod_le` bounds the
product of `n` separated factors by the single-point `2n`-th moment of each factor (Hölder), where every
pairing inside a factor is present, so `n` insertions of a channel of dimension `d_j` cost
`((2n)!)^{d_j/4}`, about `γⁿ (n!)^{d_j/2}`, and no fixed `β = 2r` covers the tower. `OS0C` on all
composites needs a bound that reads the separation (a cluster bound on the connected moments of the
separated product) in place of the single-point moments. Neither the near-Gaussian behaviour nor these
counts are proved here.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `1` the floor of `r`, of `K` and the top of the scale range; `2` the even moment
powers and `β = 2r`; `8` `one_add_mul_fact_le`'s; `4` the plaquette dimension; `2 · 1 + 3` the site count
of `uv`; `0` the signs and limits.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ScalePM

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
  MassGap.ObserverMultigrid MassGap.ClayNarrowMG MassGap.ScalePC
open MassGap.ScaleControlFull (zOne)

variable {N : ℕ}

/-! ## 1. The statement -/

/-- **One moment of one channel**: `ν_k(msFlow_j(s)^{2p}) ≤ ((2p)!)^r / μ_j(s)^{2p} · K`.
DERIVED: `2` the even power. -/
def ScaleChanPM [NeZero N] (Wf : ℝ → ConfFlow N) (r : ℕ) (t K : ℝ) (γ : Ix0 → ℝ) (γP : ℝ) (k : ℕ)
    (s : ℝ) (j : MIx) (p : ℕ) : Prop :=
  stateK (NeZero.ne N) k (msFlow Wf k s j ^ (2 * p))
    ≤ ((2 * p).factorial : ℝ) ^ r / msMu t γ γP j s ^ (2 * p) * K

/-- **The scale input as per-channel moments of every order, at the growth index `r`**: one `tⱼ > 0`,
`Kⱼ` per channel, the order and the scale fixed before the step; the plaquette class exponential at
`s = b`. DERIVED: `1` the floor of `r`; `0` the lower end of the scale. -/
structure ScalePMAt [NeZero N] (b : ℝ) (Wf : ℝ → ConfFlow N) (r : ℕ) (γ : Ix0 → ℝ) (γP : ℝ) : Prop where
  one_le : 1 ≤ r
  /-- Every channel, every scale in `(0, b]`, every order, eventually in the step. -/
  chan : ∀ j : MIx, ∃ t K : ℝ, 0 < t ∧ ∀ s : ℝ, 0 < s → s ≤ b → ∀ p : ℕ,
    ∀ᶠ k in atTop, ScaleChanPM Wf r t K γ γP k s j p
  /-- The plaquette class at the physical scale, with one set of constants. -/
  top : ∃ t C : ℝ, 0 < t ∧ ∀ᶠ k in atTop, ∀ q, ScaleChan Wf t C γ γP k b (Sum.inr q)

/-- **Control at every intermediate scale, by moments.** DERIVED: no numeral. -/
def ScaleControlAllPM [NeZero N] (b : ℝ) (Wf : ℝ → ConfFlow N) : Prop :=
  ∃ (r : ℕ) (γ : Ix0 → ℝ) (γP : ℝ), ScalePMAt b Wf r γ γP

/-- **The exponential bound of one channel gives every moment at `r = 1`, `K = e^C C`.**
DERIVED: `1` the index. -/
theorem scaleChanPM_of_scaleChan [NeZero N] {Wf : ℝ → ConfFlow N} {t C : ℝ} {γ : Ix0 → ℝ} {γP : ℝ}
    (ht : 0 < t) {k : ℕ} {s : ℝ} (hs : 0 < s) {j : MIx} (h : ScaleChan Wf t C γ γP k s j) (p : ℕ) :
    ScaleChanPM Wf 1 t (Real.exp C * C) γ γP k s j p := by
  unfold ScaleChanPM
  rw [pow_one]
  exact (msFlow_moment_chan Wf ht hs h p).2

/-- **The per-channel exponential input gives the moment input.** DERIVED: `1` the index; `0` the limit
of the spacing. -/
theorem scaleControlAllPM_of_scaleControlAllPC [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    (h : ScaleControlAllPC b Wf) : ScaleControlAllPM b Wf := by
  obtain ⟨γ, γP, H⟩ := h
  refine ⟨1, γ, γP, le_rfl, fun j => ?_, ?_⟩
  · obtain ⟨t, C, ht, hev⟩ := H.chan j
    refine ⟨t, Real.exp C * C, ht, fun s hs hsb p => ?_⟩
    filter_upwards [hev, (tendsto_dySpacing N).eventually (gt_mem_nhds hs)] with k hk hks
    exact scaleChanPM_of_scaleChan ht hs (hk s hks.le hsb) p
  · obtain ⟨t, C, ht, hev⟩ := H.plaq
    refine ⟨t, C, ht, ?_⟩
    filter_upwards [hev, (tendsto_dySpacing N).eventually (gt_mem_nhds hb)] with k hk hkb
    exact hk b hkb.le le_rfl

/-! ## 2. Uniform constants on a finite channel set -/

/-- **A smaller rate and a larger constant keep the moment bound.** DERIVED: `2` the even power; `0` the
signs. -/
theorem scaleChanPM_mono [NeZero N] {Wf : ℝ → ConfFlow N} {r : ℕ} {t t' K K' : ℝ} {γ : Ix0 → ℝ}
    {γP : ℝ} {k : ℕ} {s : ℝ} {j : MIx} {p : ℕ} (hs : 0 < s) (ht' : 0 < t') (htt : t' ≤ t)
    (hKK : K ≤ K') (hK' : 0 ≤ K') (h : ScaleChanPM Wf r t K γ γP k s j p) :
    ScaleChanPM Wf r t' K' γ γP k s j p := by
  unfold ScaleChanPM at h ⊢
  have hm' := msMu_pos ht' γ γP hs j
  have hle := msMu_mono_t htt γ γP j hs
  have hf : (0 : ℝ) ≤ ((2 * p).factorial : ℝ) ^ r := pow_nonneg (Nat.cast_nonneg _) _
  have h1 : ((2 * p).factorial : ℝ) ^ r / msMu t γ γP j s ^ (2 * p)
      ≤ ((2 * p).factorial : ℝ) ^ r / msMu t' γ γP j s ^ (2 * p) :=
    div_le_div_of_nonneg_left hf (pow_pos hm' _) (pow_le_pow_left₀ hm'.le hle _)
  have h0 : 0 ≤ ((2 * p).factorial : ℝ) ^ r / msMu t γ γP j s ^ (2 * p) :=
    div_nonneg hf (pow_nonneg (hm'.le.trans hle) _)
  calc _ ≤ _ := h
    _ ≤ ((2 * p).factorial : ℝ) ^ r / msMu t γ γP j s ^ (2 * p) * K' :=
        mul_le_mul_of_nonneg_left hKK h0
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 hK'

/-- **One `t > 0`, `K ≥ 1` on a finite channel set**, at every scale and order (`t` the least, `K` the
largest of the channel constants and `1`). DERIVED: `1` the floor of `K` and the extra rate. -/
theorem ScalePMAt.uniform [NeZero N] {b : ℝ} {Wf : ℝ → ConfFlow N} {r : ℕ} {γ : Ix0 → ℝ} {γP : ℝ}
    (h : ScalePMAt b Wf r γ γP) (T : Finset MIx) :
    ∃ t K : ℝ, 0 < t ∧ 1 ≤ K ∧ ∀ s : ℝ, 0 < s → s ≤ b → ∀ p : ℕ,
      ∀ᶠ k in atTop, ∀ j ∈ T, ScaleChanPM Wf r t K γ γP k s j p := by
  classical
  choose tf Kf htf hev using h.chan
  set t := (insert 1 (T.image tf)).min' (Finset.insert_nonempty _ _) with htdef
  set K := (insert 1 (T.image Kf)).max' (Finset.insert_nonempty _ _) with hKdef
  have ht : 0 < t := by
    refine (Finset.lt_min'_iff _ _).2 fun y hy => ?_
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
      exact htf j
  have hK1 : 1 ≤ K := Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  refine ⟨t, K, ht, hK1, fun s hs hsb p => ?_⟩
  filter_upwards [(Filter.eventually_all_finset T).2 fun j _ => hev j s hs hsb p] with k hk j hj
  exact scaleChanPM_mono hs ht
    (Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hj)))
    (Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hj))) (by linarith)
    (hk j hj)

/-! ## 3. The moment chain -/

/-- **The moment of a proxy from the moments of its channels**, at one order.
DERIVED: `2` the even powers; `1` the floor of `K`. -/
theorem msProx_moment_pm [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) {r : ℕ}
    {t K : ℝ} {γ : Ix0 → ℝ} {γP : ℝ} (ht : 0 < t) {k : ℕ} {s : ℝ} (hs : 0 < s) (hK1 : 1 ≤ K)
    {i : Ix0} (p : ℕ) (hS : ∀ j ∈ (c i s).support, ScaleChanPM Wf r t K γ γP k s j p) :
    stateK (NeZero.ne N) k (msProx Wf c k s i ^ (2 * p))
      ≤ ((2 * p).factorial : ℝ) ^ r * K * msPsize t γ γP c s i ^ (2 * p) := by
  set S := (c i s).support with hSdef
  set B := ∑ j ∈ S, |c i s j| / msMu t γ γP j s
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => div_nonneg (abs_nonneg _) (msMu_pos ht γ γP hs j).le
  rcases p with _ | n
  · simp only [mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, one_mul, mul_one,
      (stateK (NeZero.ne N) k).map_one]
    exact hK1
  · set m := 2 * (n + 1)
    have hm' : m = (2 * n + 1) + 1 := by omega
    have hev : Even m := ⟨n + 1, by omega⟩
    have hpt : ∀ U, (msProx Wf c k s i ^ m) U
        ≤ (((S.card : ℝ) ^ (2 * n + 1)) • ∑ j ∈ S, (|c i s j| ^ m) • msFlow Wf k s j ^ m) U := by
      intro U
      have hP : msProx Wf c k s i U = ∑ j ∈ S, c i s j * msFlow Wf k s j U := by
        simp only [msProx, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply,
          smul_eq_mul, hSdef]
      simp only [ContinuousMap.pow_apply, ContinuousMap.smul_apply, ContinuousMap.coe_sum,
        Finset.sum_apply, smul_eq_mul]
      rw [hP]
      have hab : |∑ j ∈ S, c i s j * msFlow Wf k s j U|
          ≤ ∑ j ∈ S, |c i s j| * |msFlow Wf k s j U| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => abs_mul _ _))
      calc (∑ j ∈ S, c i s j * msFlow Wf k s j U) ^ m
          = |∑ j ∈ S, c i s j * msFlow Wf k s j U| ^ m := (hev.pow_abs _).symm
        _ ≤ (∑ j ∈ S, |c i s j| * |msFlow Wf k s j U|) ^ m := pow_le_pow_left₀ (abs_nonneg _) hab m
        _ ≤ (S.card : ℝ) ^ (2 * n + 1) * ∑ j ∈ S, (|c i s j| * |msFlow Wf k s j U|) ^ m := by
            rw [hm']
            exact pow_sum_le_card_mul_sum_pow
              (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) _
        _ = (S.card : ℝ) ^ (2 * n + 1) * ∑ j ∈ S, |c i s j| ^ m * msFlow Wf k s j U ^ m := by
            congr 1
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [mul_pow, hev.pow_abs (msFlow Wf k s j U)]
    have hsum : ∑ j ∈ S, (|c i s j| / msMu t γ γP j s) ^ m ≤ (S.card : ℝ) * B ^ m := by
      calc ∑ j ∈ S, (|c i s j| / msMu t γ γP j s) ^ m ≤ ∑ _j ∈ S, B ^ m :=
            Finset.sum_le_sum fun j hj => pow_le_pow_left₀
              (div_nonneg (abs_nonneg _) (msMu_pos ht γ γP hs j).le)
              (Finset.single_le_sum (f := fun j => |c i s j| / msMu t γ γP j s)
                (fun j _ => div_nonneg (abs_nonneg _) (msMu_pos ht γ γP hs j).le) hj) m
        _ = (S.card : ℝ) * B ^ m := by rw [Finset.sum_const, nsmul_eq_mul]
    have hK0 : 0 ≤ K := by linarith
    have hf0 : (0 : ℝ) ≤ (m.factorial : ℝ) ^ r := pow_nonneg (Nat.cast_nonneg _) _
    calc stateK (NeZero.ne N) k (msProx Wf c k s i ^ m)
        ≤ stateK (NeZero.ne N) k
            (((S.card : ℝ) ^ (2 * n + 1)) • ∑ j ∈ S, (|c i s j| ^ m) • msFlow Wf k s j ^ m) :=
          (stateK (NeZero.ne N) k).mono hpt
      _ = (S.card : ℝ) ^ (2 * n + 1)
            * ∑ j ∈ S, |c i s j| ^ m * stateK (NeZero.ne N) k (msFlow Wf k s j ^ m) := by
          rw [(stateK (NeZero.ne N) k).map_smul, (stateK (NeZero.ne N) k).map_sum]
          simp only [(stateK (NeZero.ne N) k).map_smul]
      _ ≤ (S.card : ℝ) ^ (2 * n + 1)
            * ∑ j ∈ S, |c i s j| ^ m
              * ((m.factorial : ℝ) ^ r / msMu t γ γP j s ^ m * K) := by
          gcongr with j hj
          exact hS j hj
      _ = (m.factorial : ℝ) ^ r * K
            * ((S.card : ℝ) ^ (2 * n + 1) * ∑ j ∈ S, (|c i s j| / msMu t γ γP j s) ^ m) := by
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [div_pow]
          ring
      _ ≤ (m.factorial : ℝ) ^ r * K
            * ((S.card : ℝ) ^ (2 * n + 1) * ((S.card : ℝ) * B ^ m)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (pow_nonneg (Nat.cast_nonneg _) _))
            (mul_nonneg hf0 hK0)
      _ = (m.factorial : ℝ) ^ r * K * ((S.card : ℝ) * B) ^ m := by
          rw [hm']
          ring
      _ ≤ (m.factorial : ℝ) ^ r * K * msPsize t γ γP c s i ^ m := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hB0) ?_ m)
            (mul_nonneg hf0 hK0)
          show (S.card : ℝ) * B ≤ (S.card : ℝ) * B + 1
          linarith

/-- **The flowed reading of a family, one `t`, `K`**, from the `2n`-th moments of its channels.
DERIVED: `2` the even powers; `3` the box of `riemann_le`; `1` the spacing bound. -/
theorem abs_msLat_le_on_pm [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) {r : ℕ}
    {t K : ℝ} {γ : Ix0 → ℝ} {γP : ℝ} (ht : 0 < t) {k : ℕ} {s : ℝ} (hs : 0 < s)
    (hk1 : dySpacing N k ≤ 1) {ι : Type} [Fintype ι] (F : ι → CDatum (CbR N zOne)) (hK1 : 1 ≤ K)
    (hS : ∀ i, ∀ j ∈ (c (F i).1 s).support, ScaleChanPM Wf r t K γ γP k s j (Fintype.card ι)) :
    |msLat Wf c k s F|
      ≤ (1 + Fintype.card ι * (((2 * Fintype.card ι).factorial : ℝ) ^ r * K))
        * ∏ i, (msTsize (F i).2 * msPsize t γ γP c s (F i).1) := by
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  unfold msLat
  refine abs_state_prod_le (stateK (NeZero.ne N) k)
    (fun i => smear (dySpacing N k) (msProx Wf c k s (F i).1) (F i).2)
    (fun i => msTsize (F i).2 * msPsize t γ γP c s (F i).1)
    (fun i => mul_pos (msTsize_pos _) (msPsize_pos ht γ γP c hs _)) (fun i => ?_)
  have hK0 : 0 ≤ K := by linarith
  set n := Fintype.card ι
  have h1 := moment_smear_le (stateK (NeZero.ne N) k)
    (MassGap.ContinuumNontrivial.stateK_transObs (NeZero.ne N) k) ha hk1
    (msProx Wf c k s (F i).1) (F i).2 (tIs (F i).2) n
  have h2 := msProx_moment_pm Wf c ht hs hK1 n (hS i)
  have hT0 : 0 ≤ tM (F i).2 * (2 * tR (F i).2 + 3) ^ 4 :=
    mul_nonneg (tIs (F i).2).M_nonneg (by have := (tIs (F i).2).1; positivity)
  have hT : (tM (F i).2 * (2 * tR (F i).2 + 3) ^ 4) ^ (2 * n) ≤ msTsize (F i).2 ^ (2 * n) :=
    pow_le_pow_left₀ hT0 (by unfold msTsize; linarith) _
  have hP0 : 0 ≤ ((2 * n).factorial : ℝ) ^ r * K * msPsize t γ γP c s (F i).1 ^ (2 * n) :=
    mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hK0)
      (pow_nonneg (msPsize_pos ht γ γP c hs _).le _)
  calc stateK (NeZero.ne N) k (smear (dySpacing N k) (msProx Wf c k s (F i).1) (F i).2 ^ (2 * n))
      ≤ (tM (F i).2 * (2 * tR (F i).2 + 3) ^ 4) ^ (2 * n)
          * stateK (NeZero.ne N) k (msProx Wf c k s (F i).1 ^ (2 * n)) := h1
    _ ≤ (tM (F i).2 * (2 * tR (F i).2 + 3) ^ 4) ^ (2 * n)
          * (((2 * n).factorial : ℝ) ^ r * K * msPsize t γ γP c s (F i).1 ^ (2 * n)) :=
        mul_le_mul_of_nonneg_left h2 (pow_nonneg hT0 _)
    _ ≤ msTsize (F i).2 ^ (2 * n)
          * (((2 * n).factorial : ℝ) ^ r * K * msPsize t γ γP c s (F i).1 ^ (2 * n)) :=
        mul_le_mul_of_nonneg_right hT hP0
    _ = ((2 * n).factorial : ℝ) ^ r * K
          * (msTsize (F i).2 * msPsize t γ γP c s (F i).1) ^ (2 * n) := by
        rw [mul_pow]; ring

/-- **The flowed reading in the `L¹` form with one `tᵢ`, `Kᵢ` per factor**: each `Kᵢ` is moved into its
factor bound (`Kᵢ ≤ Kᵢ^{2n}`, `n ≥ 1`), so the common constant is `((2n)!)^r`.
DERIVED: `2` the even powers; `1` the floor of `Kᵢ` and of `n`. -/
theorem abs_msLat_le_wS_pm [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) {r : ℕ}
    {γ : Ix0 → ℝ} {γP : ℝ} {k : ℕ} {s : ℝ} (hs : 0 < s) {ι : Type} [Fintype ι]
    (F : ι → CDatum (CbR N zOne)) (tf Kf : ι → ℝ) (htf : ∀ i, 0 < tf i) (hKf : ∀ i, 1 ≤ Kf i)
    (hS : ∀ i, ∀ j ∈ (c (F i).1 s).support, ScaleChanPM Wf r (tf i) (Kf i) γ γP k s j (Fintype.card ι)) :
    |msLat Wf c k s F|
      ≤ (1 + Fintype.card ι * (((2 * Fintype.card ι).factorial : ℝ) ^ r))
        * ∏ i, ((wS (dySpacing N k) (F i).2 + dySpacing N k)
          * (Kf i * msPsize (tf i) γ γP c s (F i).1)) := by
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  unfold msLat
  refine abs_state_prod_le (stateK (NeZero.ne N) k)
    (fun i => smear (dySpacing N k) (msProx Wf c k s (F i).1) (F i).2)
    (fun i => (wS (dySpacing N k) (F i).2 + dySpacing N k)
      * (Kf i * msPsize (tf i) γ γP c s (F i).1))
    (fun i => mul_pos (add_pos_of_nonneg_of_pos (wS_nonneg ha _) ha)
      (mul_pos (by linarith [hKf i]) (msPsize_pos (htf i) γ γP c hs _)))
    (c := ((2 * Fintype.card ι).factorial : ℝ) ^ r) (fun i => ?_)
  set n := Fintype.card ι with hn
  set K := Kf i with hKdef
  set P := msPsize (tf i) γ γP c s (F i).1 with hPdef
  have hn1 : 1 ≤ 2 * n := by
    have : 0 < n := Fintype.card_pos_iff.2 ⟨i⟩
    omega
  have hKp : K ≤ K ^ (2 * n) := by
    calc K = K ^ 1 := (pow_one _).symm
      _ ≤ K ^ (2 * n) := pow_le_pow_right₀ (hKf i) hn1
  have h1 := moment_smear_wS (stateK (NeZero.ne N) k)
    (MassGap.ContinuumNontrivial.stateK_transObs (NeZero.ne N) k) ha
    (msProx Wf c k s (F i).1) (F i).2 n
  have h2 := msProx_moment_pm Wf c (htf i) hs (hKf i) n (hS i)
  have hW0 := wS_nonneg ha (F i).2
  have hP0 : 0 ≤ stateK (NeZero.ne N) k (msProx Wf c k s (F i).1 ^ (2 * n)) :=
    (stateK (NeZero.ne N) k).nonneg _ (fun U => by
      rw [ContinuousMap.pow_apply]
      exact (even_two_mul _).pow_nonneg _)
  have hPp : 0 ≤ P ^ (2 * n) := pow_nonneg (msPsize_pos (htf i) γ γP c hs _).le _
  have hf0 : (0 : ℝ) ≤ ((2 * n).factorial : ℝ) ^ r := pow_nonneg (Nat.cast_nonneg _) _
  have hWa : 0 ≤ (wS (dySpacing N k) (F i).2 + dySpacing N k) ^ (2 * n) := pow_nonneg (by linarith) _
  calc stateK (NeZero.ne N) k (smear (dySpacing N k) (msProx Wf c k s (F i).1) (F i).2 ^ (2 * n))
      ≤ wS (dySpacing N k) (F i).2 ^ (2 * n)
        * stateK (NeZero.ne N) k (msProx Wf c k s (F i).1 ^ (2 * n)) := h1
    _ ≤ (wS (dySpacing N k) (F i).2 + dySpacing N k) ^ (2 * n)
        * (((2 * n).factorial : ℝ) ^ r * K * P ^ (2 * n)) :=
        mul_le_mul (pow_le_pow_left₀ hW0 (by linarith) _) h2 hP0 hWa
    _ ≤ (wS (dySpacing N k) (F i).2 + dySpacing N k) ^ (2 * n)
        * (((2 * n).factorial : ℝ) ^ r * K ^ (2 * n) * P ^ (2 * n)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKp hf0) hPp)
          hWa
    _ = ((2 * n).factorial : ℝ) ^ r
        * ((wS (dySpacing N k) (F i).2 + dySpacing N k) * (K * P)) ^ (2 * n) := by
        rw [mul_pow, mul_pow]; ring

/-- **The continuum reading in the `L¹` form with one `tᵢ`, `Kᵢ` per factor** (`abs_msLat_le_wS_pm`,
`tendsto_wS`). DERIVED: `0` the limit of the spacing. -/
theorem abs_contC_le_pm [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {r : ℕ} {γ : Ix0 → ℝ} {γP : ℝ} {s : ℝ} (hs : 0 < s)
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → CDatum (CRen N z μ)) (hF : Adm F)
    (tf Kf : ι → ℝ) (htf : ∀ i, 0 < tf i) (hKf : ∀ i, 1 ≤ Kf i)
    (hS : ∀ᶠ k in atTop, ∀ i, ∀ j ∈ (c (F i).1 s).support,
      ScaleChanPM Wf r (tf i) (Kf i) γ γP k s j (Fintype.card ι))
    (hconv : ConvC (NeZero.ne N) (CRen N z μ)) {Rm : ℝ}
    (hrem : ∀ᶠ k in atTop, |latC (NeZero.ne N) (CRen N z μ) k F - msLat Wf c k s F| ≤ Rm) :
    |contC (NeZero.ne N) (CRen N z μ) F|
      ≤ (1 + Fintype.card ι * (((2 * Fintype.card ι).factorial : ℝ) ^ r))
        * ∏ i, (l1 (F i).2 * (Kf i * msPsize (tf i) γ γP c s (F i).1)) + Rm := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hlim : Tendsto (fun k =>
      (1 + Fintype.card ι * (((2 * Fintype.card ι).factorial : ℝ) ^ r))
        * ∏ i, ((wS (dySpacing N k) (F i).2 + dySpacing N k)
          * (Kf i * msPsize (tf i) γ γP c s (F i).1)) + Rm)
      atTop (𝓝 ((1 + Fintype.card ι * (((2 * Fintype.card ι).factorial : ℝ) ^ r))
        * ∏ i, (l1 (F i).2 * (Kf i * msPsize (tf i) γ γP c s (F i).1)) + Rm)) := by
    refine (Tendsto.const_mul _ (tendsto_finsetProd _ fun i _ => ?_)).add_const Rm
    have h1 := ((tendsto_wS (N := N) (F i).2 (hF.1 i)).add (tendsto_dySpacing N)).mul_const
      (Kf i * msPsize (tf i) γ γP c s (F i).1)
    rwa [add_zero] at h1
  have hev : ∀ᶠ k in (ultra : Filter ℕ), |latC (NeZero.ne N) (CRen N z μ) k F|
      ≤ (1 + Fintype.card ι * (((2 * Fintype.card ι).factorial : ℝ) ^ r))
        * ∏ i, ((wS (dySpacing N k) (F i).2 + dySpacing N k)
          * (Kf i * msPsize (tf i) γ γP c s (F i).1)) + Rm := by
    refine Filter.Eventually.filter_mono ultra_le ?_
    filter_upwards [hS, hrem] with k hk hr
    have hP := abs_msLat_le_wS_pm Wf c hs F tf Kf htf hKf hk
    have htri := abs_sub_abs_le_abs_sub (latC (NeZero.ne N) (CRen N z μ) k F) (msLat Wf c k s F)
    linarith
  exact le_of_tendsto_of_tendsto ((hconv ι F hF).abs) (hlim.mono_left ultra_le) hev

/-- **`MultiScaleOS.msLat_translate_sub_tendsto` from the `2n`-th moments of the family's channels.**
DERIVED: `2` the even powers; `1` the spacing bound; `0` the limit. -/
theorem msLat_translate_sub_tendsto_pm [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ))
    {r : ℕ} {t K : ℝ} {γ : Ix0 → ℝ} {γP : ℝ} (ht : 0 < t) {s : ℝ} (hs : 0 < s) (hK1 : 1 ≤ K)
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → CDatum (CbR N zOne))
    (hS : ∀ᶠ k in atTop, ∀ i, ∀ j ∈ (c (F i).1 s).support,
      ScaleChanPM Wf r t K γ γP k s j (Fintype.card ι))
    (hF : ContD F) (v : Fin 4 → ℝ) :
    Tendsto (fun k => msLat Wf c k s (fun i => translateD v (F i)) - msLat Wf c k s F) atTop
      (𝓝 0) := by
  let nk : ℕ → ISite := fun k i => ⌊v i / dySpacing N k⌋
  let w : ℕ → Fin 4 → ℝ := fun k => v - site (dySpacing N k) (nk k)
  have hwa : ∀ k i, |w k i| ≤ dySpacing N k := by
    intro k i
    have ha := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
    have h1 := Int.floor_le (v i / dySpacing N k)
    have h2 := Int.lt_floor_add_one (v i / dySpacing N k)
    have e : w k i = v i - dySpacing N k * ((⌊v i / dySpacing N k⌋ : ℤ) : ℝ) := rfl
    rw [e, abs_le]
    have h1' := (le_div_iff₀ ha).mp h1
    have h2' := (div_lt_iff₀ ha).mp h2
    constructor <;> nlinarith
  set n := Fintype.card ι with hn
  set c0 : ℝ := ((2 * n).factorial : ℝ) ^ r * K with hc0
  have hK0 : 0 ≤ c0 := mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (by linarith)
  have hlim : Tendsto (fun k => ∑ T ∈ (Finset.univ : Finset (Finset ι)).erase ∅,
      (1 + n * c0) * ∏ i, (if i ∈ T then (wD (dySpacing N k) (F i).2 (w k) + dySpacing N k)
        * msPsize t γ γP c s (F i).1 else msTsize (F i).2 * msPsize t γ γP c s (F i).1))
      atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∑ T ∈ (Finset.univ : Finset (Finset ι)).erase ∅,
        (1 + n * c0) * ∏ i, (if i ∈ T then 0 else msTsize (F i).2 * msPsize t γ γP c s (F i).1) := by
      symm
      refine Finset.sum_eq_zero fun T hT => ?_
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hT)
      exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) (if_pos hi))
    rw [h0]
    refine tendsto_finsetSum _ fun T _ => (tendsto_finsetProd _ fun i _ => ?_).const_mul _
    by_cases hi : i ∈ T
    · simp only [if_pos hi]
      have h1 := ((wD_tendsto (F i).2 (hF i) w hwa).add (tendsto_dySpacing N)).mul_const
        (msPsize t γ γP c s (F i).1)
      rwa [add_zero, zero_mul] at h1
    · simp only [if_neg hi]
      exact tendsto_const_nhds
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hS, (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)] with k hk hk1
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  have hw1 : ∀ i, |w k i| ≤ 1 := fun i => (hwa k i).trans hk1.le
  rw [Real.norm_eq_abs, msLat_translate_lat Wf c k s F v (nk k)]
  unfold msLat
  simp only [translateD]
  have hP0 : ∀ i, 0 ≤ stateK (NeZero.ne N) k (msProx Wf c k s (F i).1 ^ (2 * n)) := fun i =>
    (stateK (NeZero.ne N) k).nonneg _ (fun U => by
      rw [ContinuousMap.pow_apply]
      exact (even_two_mul n).pow_nonneg _)
  refine abs_state_prod_sub_le (stateK (NeZero.ne N) k)
    (fun i => smear (dySpacing N k) (msProx Wf c k s (F i).1) ((F i).2.translate (w k)))
    (fun i => smear (dySpacing N k) (msProx Wf c k s (F i).1) (F i).2)
    (fun i => (wD (dySpacing N k) (F i).2 (w k) + dySpacing N k) * msPsize t γ γP c s (F i).1)
    (fun i => msTsize (F i).2 * msPsize t γ γP c s (F i).1)
    (fun i => mul_pos (add_pos_of_nonneg_of_pos
      (Finset.sum_nonneg fun x _ => mul_nonneg (pow_nonneg ha.le 4) (abs_nonneg _)) ha)
      (msPsize_pos ht γ γP c hs _))
    (fun i => mul_pos (msTsize_pos _) (msPsize_pos ht γ γP c hs _)) (c := c0) (fun i => ?_) (fun i => ?_)
  · have hW0 : 0 ≤ wD (dySpacing N k) (F i).2 (w k) :=
      Finset.sum_nonneg fun x _ => mul_nonneg (pow_nonneg ha.le 4) (abs_nonneg _)
    have h1 := moment_smear_sub_le (stateK (NeZero.ne N) k)
      (ContinuumNontrivial.stateK_transObs (NeZero.ne N) k) ha
      (msProx Wf c k s (F i).1) (F i).2 (hw1) n
    have h2 := msProx_moment_pm Wf c ht hs hK1 n (hk i)
    calc stateK (NeZero.ne N) k ((smear (dySpacing N k) (msProx Wf c k s (F i).1)
          ((F i).2.translate (w k)) - smear (dySpacing N k) (msProx Wf c k s (F i).1) (F i).2) ^ (2 * n))
        ≤ wD (dySpacing N k) (F i).2 (w k) ^ (2 * n)
          * stateK (NeZero.ne N) k (msProx Wf c k s (F i).1 ^ (2 * n)) := h1
      _ ≤ (wD (dySpacing N k) (F i).2 (w k) + dySpacing N k) ^ (2 * n)
          * (c0 * msPsize t γ γP c s (F i).1 ^ (2 * n)) :=
          mul_le_mul (pow_le_pow_left₀ hW0 (by linarith) _) h2 (hP0 i)
            (pow_nonneg (by linarith) _)
      _ = c0 * ((wD (dySpacing N k) (F i).2 (w k) + dySpacing N k)
          * msPsize t γ γP c s (F i).1) ^ (2 * n) := by rw [mul_pow]; ring
  · have h1 := moment_smear_le (stateK (NeZero.ne N) k)
      (ContinuumNontrivial.stateK_transObs (NeZero.ne N) k) ha hk1.le
      (msProx Wf c k s (F i).1) (F i).2 (tIs (F i).2) n
    have h2 := msProx_moment_pm Wf c ht hs hK1 n (hk i)
    have hT0 : 0 ≤ tM (F i).2 * (2 * tR (F i).2 + 3) ^ 4 :=
      mul_nonneg (tIs (F i).2).M_nonneg (by have := (tIs (F i).2).1; positivity)
    have hT : (tM (F i).2 * (2 * tR (F i).2 + 3) ^ 4) ^ (2 * n) ≤ msTsize (F i).2 ^ (2 * n) :=
      pow_le_pow_left₀ hT0 (by unfold msTsize; linarith) _
    calc stateK (NeZero.ne N) k (smear (dySpacing N k) (msProx Wf c k s (F i).1) (F i).2 ^ (2 * n))
        ≤ (tM (F i).2 * (2 * tR (F i).2 + 3) ^ 4) ^ (2 * n)
          * stateK (NeZero.ne N) k (msProx Wf c k s (F i).1 ^ (2 * n)) := h1
      _ ≤ msTsize (F i).2 ^ (2 * n) * (c0 * msPsize t γ γP c s (F i).1 ^ (2 * n)) :=
          mul_le_mul hT h2 (hP0 i) (pow_nonneg (msTsize_pos _).le _)
      _ = c0 * (msTsize (F i).2 * msPsize t γ γP c s (F i).1) ^ (2 * n) := by rw [mul_pow]; ring

/-- **`1 + n ((2n)!)^r ≤ 2^r (8^r)ⁿ (n!)^{2r}`** for `r ≥ 1` (`one_add_mul_fact_le` at `e = 1`, raised to
the `r`-th power; `1 + x^r ≤ (1 + x)^r`). DERIVED: `2`, `8` those of `one_add_mul_fact_le`; `1` the floor of
`r`. -/
theorem one_add_mul_factPow_le (n r : ℕ) (hr : 1 ≤ r) :
    1 + (n : ℝ) * ((2 * n).factorial : ℝ) ^ r
      ≤ 2 ^ r * (8 ^ r) ^ n * (n.factorial : ℝ) ^ (2 * r) := by
  have h1 := one_add_mul_fact_le n (zero_le_one' ℝ)
  simp only [mul_one] at h1
  set A : ℝ := ((2 * n).factorial : ℝ) with hA
  have hA0 : 0 ≤ A := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hnr : (n : ℝ) ≤ (n : ℝ) ^ r := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, Nat.cast_zero, zero_pow (by omega)]
    · exact le_self_pow₀ (by exact_mod_cast hpos) (by omega)
  have h2 : (n : ℝ) * A ^ r ≤ ((n : ℝ) * A) ^ r := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hnr (pow_nonneg hA0 _)
  have h3 : 1 + ((n : ℝ) * A) ^ r ≤ (1 + (n : ℝ) * A) ^ r := by
    have := pow_add_pow_le (zero_le_one' ℝ) (mul_nonneg hn0 hA0) (by omega : r ≠ 0)
    rwa [one_pow] at this
  have h4 : (1 + (n : ℝ) * A) ^ r ≤ ((1 + 1) * 8 ^ n * (n.factorial : ℝ) ^ 2) ^ r :=
    pow_le_pow_left₀ (by positivity) h1 r
  have e : ((1 + 1 : ℝ) * 8 ^ n * (n.factorial : ℝ) ^ 2) ^ r
      = 2 ^ r * (8 ^ r) ^ n * (n.factorial : ℝ) ^ (2 * r) := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm n r]
    norm_num
  linarith

/-! ## 4. The consumers on the capstone path -/

/-- **`uv` from the plaquette class at `s = b`.** DERIVED: `4` the dimension; `2 · 1 + 3` the site
count. -/
theorem uv_of_scalePM [NeZero N] {W : ConfFlow N} {b : ℝ} {Wf : ℝ → ConfFlow N} (hb : 0 < b)
    (htop : Wf b = W) (hsc : ScaleControlAllPM b Wf) :
    ∃ t C : ℝ, 0 < t ∧ FlowUV.SiteExp (NeZero.ne N) W (SymPlaqClass N) (t * (2 * 1 + 3) ^ 4) C := by
  obtain ⟨r, γ, γP, H⟩ := hsc
  obtain ⟨t, C, ht, hev⟩ := H.top
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

/-- **`BoundC (CRen N z μ)` from the moment input and `ExpandR`**: at `s = min(θ d, b)` the family of `n`
composites reads the `2n`-th moments of the channels in the supports of its coefficients.
DERIVED: `1` the spacing bound. -/
theorem boundC_ren_of_scalePM [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hsc : ScaleControlAllPM b Wf)
    (hex : ExpandR Wf c z μ) : InputsTriage.BoundC (NeZero.ne N) (CRen N z μ) := by
  classical
  obtain ⟨r, γ, γP, H⟩ := hsc
  obtain ⟨θ, ε, Kr, κr, hθ, -, hE⟩ := hex
  intro ι _ _ F hF
  obtain ⟨hcont, d, hd, hsep⟩ := hF
  have hs : 0 < min (θ * d) b := lt_min (mul_pos hθ hd) hb
  obtain ⟨t, K, ht, hK1, hev⟩ :=
    H.uniform (Finset.univ.biUnion fun i => (c (F i).1 (min (θ * d) b)).support)
  refine ⟨(1 + Fintype.card ι * (((2 * Fintype.card ι).factorial : ℝ) ^ r * K))
      * ∏ i, (msTsize (F i).2 * msPsize t γ γP c (min (θ * d) b) (F i).1)
    + Kr ^ Fintype.card ι * (min (θ * d) b / d) ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2), ?_⟩
  refine Filter.Eventually.filter_mono ultra_le ?_
  filter_upwards [hev _ hs (min_le_right _ _) (Fintype.card ι),
    hE ι F d hd hcont hsep (min (θ * d) b) hs (min_le_left _ _),
    (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)] with k hk hrem hk1
  have hP := abs_msLat_le_on_pm Wf c ht hs hk1.le F hK1 (fun i j hj =>
    hk j (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hj⟩))
  have htri := abs_sub_abs_le_abs_sub (latC (NeZero.ne N) (CRen N z μ) k F)
    (msLat Wf c k (min (θ * d) b) F)
  linarith

/-- **`ConvC (CRen N z μ)` from the moment input and `ExpandR`.** DERIVED: no numeral. -/
theorem convC_of_scalePM [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hsc : ScaleControlAllPM b Wf)
    (hex : ExpandR Wf c z μ) : ConvC (NeZero.ne N) (CRen N z μ) :=
  (InputsTriage.convC_iff_boundC _ _).2 (boundC_ren_of_scalePM hb hsc hex)

/-- **`OS1C (CRen N z μ)` from the moment input and `ExpandR`** (the proof of
`ScalePC.os1C_of_scalePC` with the `2n`-th moments at the chosen `s`). DERIVED: `2` the halves; `0` the
limit. -/
theorem os1C_of_scalePM [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hsc : ScaleControlAllPM b Wf)
    (hex : ExpandR Wf c z μ) : OS1C (NeZero.ne N) (CRen N z μ) := by
  classical
  have hconv : ConvC (NeZero.ne N) (CRen N z μ) := convC_of_scalePM hb hsc hex
  obtain ⟨r, γ, γP, H⟩ := hsc
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
    obtain ⟨t, K, ht, hK1, hevU⟩ := H.uniform (Finset.univ.biUnion fun i => (c (F i).1 s).support)
    have hS : ∀ᶠ k in atTop, ∀ i, ∀ j ∈ (c (F i).1 s).support,
        ScaleChanPM Wf r t K γ γP k s j (Fintype.card ι) := by
      filter_upwards [hevU s hs hsb (Fintype.card ι)] with k hk i j hj
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

/-- **`OS0C (CRen N z μ)` from the moment input, `ExpandR` and `CoefBound`**: composite `i` reads the finite
channel set `S i`; its `tᵢ`, `Kᵢ` (`ScalePMAt.uniform` on `S i`) go into `Ccᵢ`, and `α = 2^r + θ'^ε`,
`γ = 8^r`, `β = 2r` are common. DERIVED: `2`, `8` from `one_add_mul_factPow_le`; `1` the top of the
scale range. -/
theorem os0C_of_scalePM [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hsc : ScaleControlAllPM b Wf)
    (hex : ExpandR Wf c z μ) (hcoef : CoefBound c) : OS0C (NeZero.ne N) (CRen N z μ) := by
  have hconv : ConvC (NeZero.ne N) (CRen N z μ) := convC_of_scalePM hb hsc hex
  obtain ⟨S, Kc, γc, hcb⟩ := hcoef
  obtain ⟨r, γ, γP, H⟩ := hsc
  choose ti Ki hti hKi hev using fun i : Ix0 => H.uniform (S i)
  obtain ⟨θ, ε, Kr, κr, hθ, hε, hE⟩ := hex
  set θ' : ℝ := min θ (min b 1) with hθ'def
  have hθ'0 : 0 < θ' := lt_min hθ (lt_min hb one_pos)
  have hθ'θ : θ' ≤ θ := min_le_left _ _
  have hθ'b : θ' ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hθ'1 : θ' ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  set P : Ix0 → ℝ := fun i =>
    Ki i * (((S i).card : ℝ) ^ 2 * (max (Kc i) 0 / ti i) + 1) with hPdef
  have hPpos : ∀ i, 0 < P i := fun i => by
    have : 0 ≤ ((S i).card : ℝ) ^ 2 * (max (Kc i) 0 / ti i) :=
      mul_nonneg (sq_nonneg _) (div_nonneg (le_max_right _ _) (hti i).le)
    exact mul_pos (by linarith [hKi i]) (by linarith)
  refine ⟨2 ^ r + θ' ^ ε, 8 ^ r, ((2 * r : ℕ) : ℝ), fun i => P i * θ'⁻¹ ^ kap γ γP γc S i + |Kr|,
    fun i => max (kap γ γP γc S i) (κr i), ?_⟩
  intro n F d hd hd1 hcont hsep
  beta_reduce
  have hs : 0 < θ' * d := mul_pos hθ'0 hd
  have hsθ : θ' * d ≤ θ * d := mul_le_mul_of_nonneg_right hθ'θ hd.le
  have hsθ' : θ' * d ≤ θ' := mul_le_of_le_one_right hθ'0.le hd1
  have hsb : θ' * d ≤ b := hsθ'.trans hθ'b
  have hs1 : θ' * d ≤ 1 := hsθ'.trans hθ'1
  have hS : ∀ᶠ k in atTop, ∀ i, ∀ j ∈ (c (F i).1 (θ' * d)).support,
      ScaleChanPM Wf r (ti (F i).1) (Ki (F i).1) γ γP k (θ' * d) j (Fintype.card (Fin n)) := by
    have hall := (Filter.eventually_all (ι := Fin n)).2 fun i =>
      hev (F i).1 (θ' * d) hs hsb (Fintype.card (Fin n))
    filter_upwards [hall] with k hk i j hj
    exact hk i j ((hcb (F i).1 (θ' * d) hs hs1).1 hj)
  have hA := abs_contC_le_pm hs F ⟨hcont, d, hd, hsep⟩ (fun i => ti (F i).1) (fun i => Ki (F i).1)
    (fun i => hti _) (fun i => hKi _) hS hconv (hE (Fin n) F d hd hcont hsep (θ' * d) hs hsθ)
  have hsd : θ' * d / d = θ' := mul_div_cancel_right₀ θ' hd.ne'
  rw [Fintype.card_fin, hsd] at hA
  have hl1 : ∀ i, 0 ≤ l1 (F i).2 := fun i => MeasureTheory.integral_nonneg fun x => abs_nonneg _
  have hPs : ∀ i, Ki (F i).1 * msPsize (ti (F i).1) γ γP c (θ' * d) (F i).1
      ≤ P (F i).1 * (θ' * d)⁻¹ ^ kap γ γP γc S (F i).1 := fun i => by
    have h := msPsize_le (hti (F i).1) γ γP c hcb (F i).1 hs hs1
    have hm := mul_le_mul_of_nonneg_left h (by linarith [hKi (F i).1] : (0 : ℝ) ≤ Ki (F i).1)
    calc _ ≤ _ := hm
      _ = P (F i).1 * (θ' * d)⁻¹ ^ kap γ γP γc S (F i).1 := by simp only [hPdef]; ring
  have hfac : ∀ i, l1 (F i).2 * (Ki (F i).1 * msPsize (ti (F i).1) γ γP c (θ' * d) (F i).1)
      ≤ (P (F i).1 * θ'⁻¹ ^ kap γ γP γc S (F i).1 + |Kr|)
        * (d ^ max (kap γ γP γc S (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2
      ∧ |Kr| * ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)
      ≤ (P (F i).1 * θ'⁻¹ ^ kap γ γP γc S (F i).1 + |Kr|)
        * (d ^ max (kap γ γP γc S (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2 := fun i =>
    os0_factor_le (hl1 i) (hPpos _) hθ'0 hd hd1 rfl (hPs i)
  have hθε : 0 ≤ θ' ^ ε := Real.rpow_nonneg hθ'0.le _
  have hZ0 : 0 ≤ ∏ i, (P (F i).1 * θ'⁻¹ ^ kap γ γP γc S (F i).1 + |Kr|)
        * (d ^ max (kap γ γP γc S (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2 :=
    Finset.prod_nonneg fun i _ => (mul_nonneg (abs_nonneg Kr)
      (mul_nonneg (inv_nonneg.mpr (Real.rpow_nonneg hd.le _)) (hl1 i))).trans (hfac i).2
  have hF0 : ∀ i, 0 ≤ l1 (F i).2 * (Ki (F i).1 * msPsize (ti (F i).1) γ γP c (θ' * d) (F i).1) :=
    fun i => mul_nonneg (hl1 i) (mul_nonneg (by linarith [hKi (F i).1])
      (msPsize_pos (hti _) γ γP c hs _).le)
  have hPi1 : ∏ i, (l1 (F i).2 * (Ki (F i).1 * msPsize (ti (F i).1) γ γP c (θ' * d) (F i).1))
      ≤ ∏ i, (P (F i).1 * θ'⁻¹ ^ kap γ γP γc S (F i).1 + |Kr|)
        * (d ^ max (kap γ γP γc S (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2 :=
    Finset.prod_le_prod (fun i _ => hF0 i) (fun i _ => (hfac i).1)
  have hPi10 : 0 ≤ ∏ i, (l1 (F i).2 * (Ki (F i).1 * msPsize (ti (F i).1) γ γP c (θ' * d) (F i).1)) :=
    Finset.prod_nonneg fun i _ => hF0 i
  have hPi2 : ∏ i, (|Kr| * ((d ^ κr (F i).1)⁻¹ * l1 (F i).2))
      ≤ ∏ i, (P (F i).1 * θ'⁻¹ ^ kap γ γP γc S (F i).1 + |Kr|)
        * (d ^ max (kap γ γP γc S (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2 :=
    Finset.prod_le_prod (fun i _ => mul_nonneg (abs_nonneg _)
      (mul_nonneg (inv_nonneg.mpr (Real.rpow_nonneg hd.le _)) (hl1 i))) (fun i _ => (hfac i).2)
  have hrem : Kr ^ n * θ' ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)
      ≤ θ' ^ ε * ∏ i, (|Kr| * ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)) := by
    have hPi : 0 ≤ ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2) :=
      Finset.prod_nonneg fun i _ => mul_nonneg (inv_nonneg.mpr (Real.rpow_nonneg hd.le _)) (hl1 i)
    have hK : Kr ^ n ≤ |Kr| ^ n := (le_abs_self _).trans (abs_pow Kr n).le
    have e : ∏ i, (|Kr| * ((d ^ κr (F i).1)⁻¹ * l1 (F i).2))
        = |Kr| ^ n * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [e]
    calc Kr ^ n * θ' ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)
        = θ' ^ ε * (Kr ^ n * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)) := by ring
      _ ≤ θ' ^ ε * (|Kr| ^ n * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK hPi) hθε
  have hmain1 := one_add_mul_factPow_le n r H.one_le
  have h8 : (1 : ℝ) ≤ (8 ^ r) ^ n * (n.factorial : ℝ) ^ (2 * r) := by
    have : (1 : ℝ) ≤ (8 ^ r) ^ n := one_le_pow₀ (one_le_pow₀ (by norm_num))
    have h2 : (1 : ℝ) ≤ (n.factorial : ℝ) ^ (2 * r) :=
      one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n))
    nlinarith
  have h2r : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  have hX : 0 ≤ (2 : ℝ) ^ r * (8 ^ r) ^ n * (n.factorial : ℝ) ^ (2 * r) := by positivity
  have hM := mul_le_mul hmain1 hPi1 hPi10 hX
  have hR2 := mul_le_mul_of_nonneg_left hPi2 hθε
  have hR3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h8 hθε) hZ0
  rw [Real.rpow_natCast]
  linarith

/-! ## 5. The substrate core by moments and the bundle -/

/-- **The substrate core with the moment input**: `ScalePC.SubstrateCorePC` with `scale` replaced by
`ScaleControlAllPM b Wf`. DERIVED: no numeral. -/
structure SubstrateCorePM [NeZero N] (W : ConfFlow N) (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow N) :
    Prop where
  b_pos : 0 < b
  /-- The flow to the physical scale is `W`. -/
  top : Wf b = W
  /-- Every intermediate scale, per channel, by moments. -/
  scale : ScaleControlAllPM b Wf
  /-- Asymptotic freedom: a two-point kernel of the trace at `z` with the asymptotic-freedom coefficient. -/
  af : ∃ G : ℝ → ℝ, TwoPointKernel (NeZero.ne N) (rhoD (fR N) z) G ∧ AFCoefficient N G

/-- `SubstrateCorePC` gives `SubstrateCorePM`. DERIVED: no numeral. -/
theorem substrateCorePM_of_corePC [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {b : ℝ}
    {Wf : ℝ → ConfFlow N} (S : SubstrateCorePC W z b Wf) : SubstrateCorePM W z b Wf :=
  ⟨S.b_pos, S.top, scaleControlAllPM_of_scaleControlAllPC S.b_pos S.scale, S.af⟩

/-- **`ClayNarrow.compOS_of_covC` from the moment core.** DERIVED: no numeral. -/
theorem compOS_of_covC_pm [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (S : SubstrateCorePM W z b Wf)
    (hE : ExpandStrong Wf cf z μ) (hcb : CoefBound cf) (hV : CovC (NeZero.ne N) (CRen N z μ))
    (hP : CompNondeg (NeZero.ne N) (CRen N z μ)) : CompOS (NeZero.ne N) (CRen N z μ) :=
  ⟨convC_of_scalePM S.b_pos S.scale (expandR_of_strong hE),
    os0C_of_scalePM S.b_pos S.scale (expandR_of_strong hE) hcb,
    os1C_of_scalePM S.b_pos S.scale (expandR_of_strong hE), hV, hP⟩

/-- **`ClayNarrow.approxK_of_beyond_covC` from the moment core.** DERIVED: `2` the least colour count;
`0` the plane and the reference step. -/
theorem approxK_of_beyond_covC_pm (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ}
    {μ : OffMix} {b r : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCorePM W z b Wf) (hE : ExpandStrong Wf cf z μ) (hcb : CoefBound cf)
    (hV : CovC (NeZero.ne N) (CRen N z μ)) (hP : CompNondeg (NeZero.ne N) (CRen N z μ))
    (hphys : (Φ0 W).PhysRange r)
    (hB : ∀ P, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N z μ) 0)
      (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) P) :
    ApproxK (kernC (NeZero.ne N) (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) := by
  obtain ⟨t, C, ht, hS⟩ := uv_of_scalePM S.b_pos S.top S.scale
  have hU := ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) W ht hS
  have hCO := compOS_of_covC_pm S hE hcb hV hP
  let D := capData hN2 W hU hphys (CRen N z μ)
    (unifLocal_buildRen (rhoD (fR N) z) (bareD (fR N) (bR N)) μ) (reflCovLat_CRen z μ) hCO
  refine approxK_iff_forall.2 fun P => ?_
  obtain ⟨n, hn⟩ := exists_beyond_iterate (NeZero.ne N) r P
  exact approxKAt_of_iterate D 0 n P (hB _ hn)

/-- **`ClayNarrowMG.inputsAt_of_covC_phys` from the moment core.** DERIVED: `2` the least colour count;
`0` the lower end of the scale. -/
theorem inputsAt_of_covC_phys_pm (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {r : ℝ}
    {zri zwe : ℕ → ℝ} (hri : ∀ k, zri k ≠ 0) (hwe : ∀ k, zwe k ≠ 0) {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCorePM W (ZCanon.zFix N zri zwe) b Wf)
    (hE : ExpandStrong Wf cf (ZCanon.zFix N zri zwe) μ) (hcb : CoefBound cf)
    (hV : CovC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ))
    (hW : WardT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe)))
    (hP : CompNondeg (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ))
    (hphys : (Φ0 W).PhysRange r)
    (hA : ApproxK (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
      (mixKG hN2 W (CRen N (ZCanon.zFix N zri zwe) μ) r) (gramF hN2 W r))
    (h3 : ∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (ne_zero_of_two_le hN2) ℓ)
    (hfar : WDeltaRun.RunSeed N) :
    ∃ (t C : ℝ) (G : ℝ → ℝ), SUNBest.InputsAt hN2 W r t |C| zri zwe μ G := by
  obtain ⟨t, C, ht, hS⟩ := uv_of_scalePM S.b_pos S.top S.scale
  have hU := ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) W ht hS
  obtain ⟨G, hK, hAF⟩ := S.af
  obtain ⟨ℓ, hℓ, h3'⟩ := h3
  exact ⟨t, C, G,
    { t_pos := ht
      moments := hU
      phys := hphys
      far := hfar
      hri := hri
      hwe := hwe
      kernel := hK
      af := hAF
      low := obsLower_of_scale (ne_zero_of_two_le hN2) hℓ zri zwe h3'
      ward := hW
      comp := compOS_of_covC_pm S hE hcb hV hP
      approx := hA }⟩

/-- **The per-`N` inputs with the moment scale input**: `ScalePC.NarrowInputsAtPC` with
`SubstrateCorePC` replaced by `SubstrateCorePM`. DERIVED: `2` the least colour count; `0` the plane and
the reference step. -/
def NarrowInputsAtPM (N : ℕ) (hN2 : 2 ≤ N) (W : ConfFlow N) (r : ℝ) : Prop :=
  haveI : NeZero N := ⟨by omega⟩
  (Φ0 W).PhysRange r ∧
  ∃ (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)),
    SubstrateCorePM W (ZCanon.zFix N zri zwe) b Wf
      ∧ ExpandStrong Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ CoefBound cf
      ∧ CovC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ WardT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe))
      ∧ CompNondeg (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ (∀ P, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
          (mixKG hN2 W (CRen N (ZCanon.zFix N zri zwe) μ) r) (gramF hN2 W r) P)
      ∧ (∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (ne_zero_of_two_le hN2) ℓ)
      ∧ RunSeedN.EndpointN N

/-- **`NarrowInputsAtPC` gives `NarrowInputsAtPM`** at the same witnesses (`substrateCorePM_of_corePC`).
DERIVED: `2` the least colour count. -/
theorem narrowInputsAtPM_of_narrowAtPC (hN2 : 2 ≤ N) {W : ConfFlow N} {r : ℝ}
    (h : NarrowInputsAtPC N hN2 W r) : NarrowInputsAtPM N hN2 W r := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP, hB, h3, hEnd⟩ := h
  exact ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, substrateCorePM_of_corePC S, hE, hC, hV, hW, hP, hB, h3,
    hEnd⟩

/-- **`NarrowInputsAtPM` gives the general-`N` bundle at `W`** (`approxK_of_beyond_covC_pm`,
`RunSeedN.runSeed_of_endpointN`, `inputsAt_of_covC_phys_pm`). DERIVED: `2` the least colour count. -/
theorem clayInputsN_of_narrowAtPM (hN2 : 2 ≤ N) {W : ConfFlow N} {r : ℝ}
    (h : NarrowInputsAtPM N hN2 W r) : SUNBest.ClayInputsN N hN2 := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP, hB, h3, hEnd⟩ := h
  obtain ⟨t, C, G, I⟩ := inputsAt_of_covC_phys_pm hN2 hri hwe S hE hC hV hW hP hphys
    (approxK_of_beyond_covC_pm hN2 S hE hC hV hP hphys hB) h3 (RunSeedN.runSeed_of_endpointN hEnd)
  exact ⟨W, r, t, |C|, zri, zwe, μ, G, I⟩

end MassGap.ScalePM

end

#print axioms MassGap.ScalePM.scaleChanPM_of_scaleChan
#print axioms MassGap.ScalePM.scaleControlAllPM_of_scaleControlAllPC
#print axioms MassGap.ScalePM.scaleChanPM_mono
#print axioms MassGap.ScalePM.ScalePMAt.uniform
#print axioms MassGap.ScalePM.msProx_moment_pm
#print axioms MassGap.ScalePM.abs_msLat_le_on_pm
#print axioms MassGap.ScalePM.abs_msLat_le_wS_pm
#print axioms MassGap.ScalePM.abs_contC_le_pm
#print axioms MassGap.ScalePM.msLat_translate_sub_tendsto_pm
#print axioms MassGap.ScalePM.one_add_mul_factPow_le
#print axioms MassGap.ScalePM.uv_of_scalePM
#print axioms MassGap.ScalePM.boundC_ren_of_scalePM
#print axioms MassGap.ScalePM.convC_of_scalePM
#print axioms MassGap.ScalePM.os1C_of_scalePM
#print axioms MassGap.ScalePM.os0C_of_scalePM
#print axioms MassGap.ScalePM.substrateCorePM_of_corePC
#print axioms MassGap.ScalePM.compOS_of_covC_pm
#print axioms MassGap.ScalePM.approxK_of_beyond_covC_pm
#print axioms MassGap.ScalePM.inputsAt_of_covC_phys_pm
#print axioms MassGap.ScalePM.narrowInputsAtPM_of_narrowAtPC
#print axioms MassGap.ScalePM.clayInputsN_of_narrowAtPM
