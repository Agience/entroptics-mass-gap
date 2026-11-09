import Mathlib
import MassGap.ClayNarrowMG

/-!
# MassGap.ScalePC — the scale input with one set of constants per channel

`MultiScaleAll.ScaleControlAll b Wf` asks one rate `t > 0` and one constant `C` over the whole index family
`MIx` (every admissible monomial, of unbounded dimension `cdim`, and every plaquette). By positivity of the
Wilson state, one `C` over the channel tower forces a deterministic bound on the flowed origin plaquette
(`BulkBound.facV_le_of_scaleControlAll`), false at the ray-averaged observer at `b ≥ 1`
(`BulkBound.not_scaleControlAll_of_one_le`). The target's `OS0C` carries one `Cᵢ`, `κᵢ` per composite. This
module states the scale input per channel and reduces the `SU(N)` bundle to it. Declarations are in the
namespace `MassGap.ScalePC`.

## 1. The statement

* `ScaleChan Wf t C γ γP k s j`: the moment bound of `ScaleAt` for the one channel `j`;
  `ScaleAt Wf t C γ γP k s ↔ ∀ j, ScaleChan Wf t C γ γP k s j` (`scaleAt_iff`).
* `ScalePCAt b Wf γ γP`: for every monomial `i : Ix0` there are `tᵢ > 0`, `Cᵢ` with, eventually in the step,
  `ScaleChan Wf tᵢ Cᵢ γ γP k s (inl i)` at every `s ∈ [a_k, b]`; and one `t > 0`, `C` for the plaquette class
  (every `inr q`). The log exponents `γ i` are per monomial, as in `ScaleControlAll`.
* `ScaleControlAllPC b Wf`: `∃ γ γP, ScalePCAt b Wf γ γP`.
* `scaleControlAllPC_of_scaleControlAll`: `ScaleControlAll` gives `ScaleControlAllPC`.

The plaquette class keeps one constant: every consumer that reads it (`uv`, `ClassMoments`) needs one
constant over the class `SymPlaqClass N`. The class is the hypercubic orbit sums `sym (plaqField q)`,
`q : IPlaq`, each of dimension `4` with 384 plaquette terms; it has no growing dimension, so the tower
argument of `BulkBound` does not apply.

## 2. What is derived (proved)

* `ScalePCAt.uniform`: on any finite set `T` of channels there are one `t > 0`, `C ≥ 1` with, eventually in
  the step, the bound at every `s ∈ [a_k, b]` and every `j ∈ T` (`t = min`, `C = max`; `scaleChan_mono`).
* The moment chain on a finite channel set: `msFlow_moment_chan`, `msProx_moment_on`, `abs_msLat_le_on`,
  `msLat_translate_sub_tendsto_on`; with per-factor constants, `abs_msLat_le_wS_pc` and `abs_contC_le_pc`
  (each factor carries its own `e^{Cᵢ} Cᵢ`, moved into the factor bound of `abs_state_prod_le`, which then
  has the common constant `(2n)!`).
* `uv_of_scalePC` (plaquette class at `s = b`), `boundC_ren_of_scalePC`, `convC_of_scalePC`
  (one `F`: the channels are the supports of the coefficients of its composites at `s = min(θ d, b)`),
  `os1C_of_scalePC` (one `F`, one `s`), `os0C_of_scalePC` (with `CoefBound`: composite `i` reads the
  finite set `S i`; its `tᵢ`, `Cᵢ` go into `Ccᵢ`; `α = 2 + θ'^ε`, `γ = 8`, `β = 2`).
* `SubstrateCorePC` (`SU2Best.SubstrateCoreAt` with `scale : ScaleControlAllPC b Wf`),
  `substrateCorePC_of_core`, `compOS_of_covC_pc`, `approxK_of_beyond_covC_pc`, `inputsAt_of_covC_phys_pc`.
* `NarrowInputsAtPC N hN2 W r` (`ClayNarrowMG.NarrowInputsAt` with the core per channel),
  `narrowInputsAtPC_of_narrowAt`, `clayInputsN_of_narrowAtPC`. No `ClayStatement` capstone is stated from
  `NarrowInputsAtPC`: it carries `RunSeedN.EndpointN N`, refuted by
  `EndpointAudit.not_endpointN_of_levels_unbounded` under the argued growth of the zero-flux level count.

## 3. The no-go of `BulkBound` and the per-channel input (argued; no declaration)

`BulkBound.facV_le_of_scaleAt_one` reads the channels `inl (jn n)` for every `n` at one step with one `t`,
`C`: on the open set `{G > 0}` it gets `exp(L_n) ν_k(G) ≤ C` with `L_n` unbounded in `n` and `ν_k(G) > 0`
fixed. With `Cₙ` per channel the inequality is `exp(L_n) ν_k(G) ≤ Cₙ`, which holds for `Cₙ` large; the
tower gives nothing, and the sup bound is not forced. Per channel `j = jn n` (`d_j = 4(n + 1)`) at one
`s`, `ScalePCAt` asks the tail bound `ν_k(N − Re tr (V_k U)_p > ρ) ≤ Cⱼ exp(−(tⱼ/2)(s^{d_j}/afLog)
(ρ²/a_k⁴)^{n+1})` eventually in `k`: the probability that the flowed origin plaquette deviates by `ρ`
must fall like `exp(−c a_k^{−d_j})`. The lower bound of `BulkBound` §2, made quantitative, is
`exp(−2β_k |∂S_k|)` times the Haar measure of the set of inputs on the links `S_k` read by `V_k` whose
output stays within `ρ` of a configuration with `N − Re tr = 4` (the `π`-flux fixed point). If `|S_k|`
grows like `(s/a_k)⁴` and that set has Haar measure `≥ exp(−c (s/a_k)⁴ log(s/a_k))` (bounded Lipschitz
constant of `V_k`), the two bounds conflict for `d_j > 4` as `k → ∞`. Neither the quantitative lower
bound nor the locality and Lipschitz properties of an observer are proved here; the per-channel input is
open at every observer, and its single-channel content at high `d_j` is this tail bound.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `1` the floor of `C`, the spacing bound and the top of the scale range; `2` the even
moment powers, `β` and the first term of `α`; `8` `one_add_mul_fact_le`'s; `4` the plaquette dimension;
`2 · 1 + 3` the site count of `uv`; `0` the signs and limits.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ScalePC

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
  MassGap.ObserverMultigrid MassGap.ClayNarrowMG
open MassGap.ScaleControlFull (zOne)

variable {N : ℕ}

/-! ## 1. The statement -/

/-- **The scale bound for one channel**: `ν_k(exp((μ_j(s) / a_k^{d_j}) · |O_j ∘ V_k^{(s)}|)) ≤ C`.
DERIVED: no numeral. -/
def ScaleChan [NeZero N] (Wf : ℝ → ConfFlow N) (t C : ℝ) (γ : Ix0 → ℝ) (γP : ℝ) (k : ℕ) (s : ℝ)
    (j : MIx) : Prop :=
  stateK (NeZero.ne N) k
    (expC ((msMu t γ γP j s / dySpacing N k ^ mDim j) • msAbs ((Wf s).fieldMap k (mField j)).1)) ≤ C

/-- `ScaleAt` is `ScaleChan` at every channel. DERIVED: no numeral. -/
theorem scaleAt_iff [NeZero N] {Wf : ℝ → ConfFlow N} {t C : ℝ} {γ : Ix0 → ℝ} {γP : ℝ} {k : ℕ} {s : ℝ} :
    ScaleAt Wf t C γ γP k s ↔ ∀ j, ScaleChan Wf t C γ γP k s j := Iff.rfl

/-- **The scale input per channel, at the log exponents `γ`, `γP`**: one `tᵢ > 0`, `Cᵢ` per monomial, one
`t > 0`, `C` for the plaquette class; each eventually in the step, at every `s ∈ [a_k, b]`.
DERIVED: no numeral. -/
structure ScalePCAt [NeZero N] (b : ℝ) (Wf : ℝ → ConfFlow N) (γ : Ix0 → ℝ) (γP : ℝ) : Prop where
  /-- Every monomial channel, with its own constants. -/
  mono : ∀ i : Ix0, ∃ t C : ℝ, 0 < t ∧ ∀ᶠ k in atTop, ∀ s : ℝ, dySpacing N k ≤ s → s ≤ b →
    ScaleChan Wf t C γ γP k s (Sum.inl i)
  /-- The plaquette class, with one set of constants. -/
  plaq : ∃ t C : ℝ, 0 < t ∧ ∀ᶠ k in atTop, ∀ s : ℝ, dySpacing N k ≤ s → s ≤ b →
    ∀ q, ScaleChan Wf t C γ γP k s (Sum.inr q)

/-- **Control at every intermediate scale, per channel.** DERIVED: no numeral. -/
def ScaleControlAllPC [NeZero N] (b : ℝ) (Wf : ℝ → ConfFlow N) : Prop :=
  ∃ (γ : Ix0 → ℝ) (γP : ℝ), ScalePCAt b Wf γ γP

/-- **The one-constant input gives the per-channel input.** DERIVED: no numeral. -/
theorem scaleControlAllPC_of_scaleControlAll [NeZero N] {b : ℝ} {Wf : ℝ → ConfFlow N}
    (h : ScaleControlAll b Wf) : ScaleControlAllPC b Wf := by
  obtain ⟨t, C, γ, γP, ht, hev⟩ := h
  exact ⟨γ, γP, ⟨fun i => ⟨t, C, ht, hev.mono fun k hk s h1 h2 => hk s h1 h2 (Sum.inl i)⟩,
    ⟨t, C, ht, hev.mono fun k hk s h1 h2 q => hk s h1 h2 (Sum.inr q)⟩⟩⟩

/-! ## 2. Uniform constants on a finite channel set -/

/-- `μ_j(s)` is monotone in `t`. DERIVED: `0` the signs. -/
theorem msMu_mono_t {t t' : ℝ} (htt : t' ≤ t) (γ : Ix0 → ℝ) (γP : ℝ) (j : MIx) {s : ℝ} (hs : 0 < s) :
    msMu t' γ γP j s ≤ msMu t γ γP j s := by
  cases j <;> simp only [msMu] <;>
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right htt (pow_pos hs _).le)
      (afLog_pos _ _).le

/-- **A smaller rate and a larger constant keep the bound.** DERIVED: `0` the signs. -/
theorem scaleChan_mono [NeZero N] {Wf : ℝ → ConfFlow N} {t t' C C' : ℝ} {γ : Ix0 → ℝ} {γP : ℝ}
    {k : ℕ} {s : ℝ} {j : MIx} (hs : 0 < s) (htt : t' ≤ t) (hCC : C ≤ C')
    (h : ScaleChan Wf t C γ γP k s j) : ScaleChan Wf t' C' γ γP k s j := by
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  unfold ScaleChan at h ⊢
  refine le_trans ((stateK (NeZero.ne N) k).mono fun U => ?_) (h.trans hCC)
  simp only [expC_apply, ContinuousMap.smul_apply, smul_eq_mul, msAbs_apply]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (msMu_mono_t htt γ γP j hs) (pow_pos ha _).le) (abs_nonneg _))

/-- Every channel has its constants. DERIVED: no numeral. -/
theorem ScalePCAt.chan [NeZero N] {b : ℝ} {Wf : ℝ → ConfFlow N} {γ : Ix0 → ℝ} {γP : ℝ}
    (h : ScalePCAt b Wf γ γP) (j : MIx) :
    ∃ t C : ℝ, 0 < t ∧ ∀ᶠ k in atTop, ∀ s : ℝ, dySpacing N k ≤ s → s ≤ b →
      ScaleChan Wf t C γ γP k s j := by
  rcases j with i | q
  · exact h.mono i
  · obtain ⟨t, C, ht, hev⟩ := h.plaq
    exact ⟨t, C, ht, hev.mono fun k hk s h1 h2 => hk s h1 h2 q⟩

/-- **One `t > 0`, `C ≥ 1` on a finite channel set** (`t` the least, `C` the largest of the channel
constants and `1`). DERIVED: `1` the floor of `C` and the extra rate. -/
theorem ScalePCAt.uniform [NeZero N] {b : ℝ} {Wf : ℝ → ConfFlow N} {γ : Ix0 → ℝ} {γP : ℝ}
    (h : ScalePCAt b Wf γ γP) (T : Finset MIx) :
    ∃ t C : ℝ, 0 < t ∧ 1 ≤ C ∧ ∀ᶠ k in atTop, ∀ s : ℝ, dySpacing N k ≤ s → s ≤ b →
      ∀ j ∈ T, ScaleChan Wf t C γ γP k s j := by
  classical
  choose tf Cf htf hev using h.chan
  set t := (insert 1 (T.image tf)).min' (Finset.insert_nonempty _ _) with htdef
  set C := (insert 1 (T.image Cf)).max' (Finset.insert_nonempty _ _) with hCdef
  have ht : 0 < t := by
    refine (Finset.lt_min'_iff _ _).2 fun y hy => ?_
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
      exact htf j
  refine ⟨t, C, ht, Finset.le_max' _ _ (Finset.mem_insert_self _ _), ?_⟩
  have hall : ∀ᶠ k in atTop, ∀ j ∈ T, ∀ s : ℝ, dySpacing N k ≤ s → s ≤ b →
      ScaleChan Wf (tf j) (Cf j) γ γP k s j :=
    (Filter.eventually_all_finset T).2 fun j _ => hev j
  filter_upwards [hall] with k hk s h1 h2 j hj
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  exact scaleChan_mono (ha.trans_le h1)
    (Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hj)))
    (Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hj))) (hk j hj s h1 h2)

/-! ## 3. The moment chain on a finite channel set -/

/-- **`MultiScaleAll.msFlow_moment` from the one channel.** DERIVED: `2` the even powers. -/
theorem msFlow_moment_chan [NeZero N] (Wf : ℝ → ConfFlow N) {t C : ℝ} {γ : Ix0 → ℝ} {γP : ℝ}
    (ht : 0 < t) {k : ℕ} {s : ℝ} (hs : 0 < s) {j : MIx} (hS : ScaleChan Wf t C γ γP k s j) (p : ℕ) :
    1 ≤ C ∧ stateK (NeZero.ne N) k (msFlow Wf k s j ^ (2 * p))
      ≤ ((2 * p).factorial : ℝ) / msMu t γ γP j s ^ (2 * p) * (Real.exp C * C) := by
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  have had : 0 < dySpacing N k ^ mDim j := pow_pos ha _
  have hmu := msMu_pos ht γ γP hs j
  set G : C(Cfg N, ℝ) := ((Wf s).fieldMap k (mField j)).1 with hG
  have hl : 0 ≤ msMu t γ γP j s / dySpacing N k ^ mDim j := (div_pos hmu had).le
  obtain ⟨h1, h2⟩ := exp_abs_sub_le (stateK (NeZero.ne N) k) G hl hS
  refine ⟨h1, ?_⟩
  have e : expC (msMu t γ γP j s • msAbs (msFlow Wf k s j))
      = expC ((msMu t γ γP j s / dySpacing N k ^ mDim j)
        • msAbs (G - stateK (NeZero.ne N) k G • (1 : C(Cfg N, ℝ)))) := by
    ext U
    simp only [msFlow, expC_apply, ContinuousMap.smul_apply, smul_eq_mul, msAbs_apply,
      ContinuousMap.sub_apply, ContinuousMap.one_apply, mul_one, ← hG]
    congr 1
    rw [abs_mul, abs_inv, abs_of_pos had, div_eq_mul_inv]
    ring
  have h3 : stateK (NeZero.ne N) k (expC (msMu t γ γP j s • msAbs (msFlow Wf k s j)))
      ≤ Real.exp C * C := by
    rw [e]; exact h2
  exact state_pow_le_of_exp (stateK (NeZero.ne N) k) (msFlow Wf k s j) hmu h3 p

/-- **`MultiScaleAll.msProx_moment` on the support of the coefficients**, with `1 ≤ C`.
DERIVED: `2` the even powers; `1` the floor of `C`. -/
theorem msProx_moment_on [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) {t C : ℝ}
    {γ : Ix0 → ℝ} {γP : ℝ} (ht : 0 < t) {k : ℕ} {s : ℝ} (hs : 0 < s) (hC1 : 1 ≤ C) {i : Ix0}
    (hS : ∀ j ∈ (c i s).support, ScaleChan Wf t C γ γP k s j) (p : ℕ) :
    stateK (NeZero.ne N) k (msProx Wf c k s i ^ (2 * p))
      ≤ ((2 * p).factorial : ℝ) * (Real.exp C * C) * msPsize t γ γP c s i ^ (2 * p) := by
  have hK1 : 1 ≤ Real.exp C * C := by
    have := Real.add_one_le_exp C
    nlinarith
  set S := (c i s).support with hSdef
  set B := ∑ j ∈ S, |c i s j| / msMu t γ γP j s
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => div_nonneg (abs_nonneg _) (msMu_pos ht γ γP hs j).le
  rcases p with _ | n
  · simp only [mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, mul_one,
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
    have hK0 : 0 ≤ Real.exp C * C := by linarith
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
              * ((m.factorial : ℝ) / msMu t γ γP j s ^ m * (Real.exp C * C)) := by
          gcongr with j hj
          exact (msFlow_moment_chan Wf ht hs (hS j hj) (n + 1)).2
      _ = (m.factorial : ℝ) * (Real.exp C * C)
            * ((S.card : ℝ) ^ (2 * n + 1) * ∑ j ∈ S, (|c i s j| / msMu t γ γP j s) ^ m) := by
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [div_pow]
          ring
      _ ≤ (m.factorial : ℝ) * (Real.exp C * C)
            * ((S.card : ℝ) ^ (2 * n + 1) * ((S.card : ℝ) * B ^ m)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (pow_nonneg (Nat.cast_nonneg _) _))
            (mul_nonneg (Nat.cast_nonneg _) hK0)
      _ = (m.factorial : ℝ) * (Real.exp C * C) * ((S.card : ℝ) * B) ^ m := by
          rw [hm']
          ring
      _ ≤ (m.factorial : ℝ) * (Real.exp C * C) * msPsize t γ γP c s i ^ m := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hB0) ?_ m)
            (mul_nonneg (Nat.cast_nonneg _) hK0)
          show (S.card : ℝ) * B ≤ (S.card : ℝ) * B + 1
          linarith

/-- **`MultiScaleAll.abs_msLat_le` on the supports of the family's coefficients.**
DERIVED: `2` the even powers; `3` the box of `riemann_le`; `1` the spacing bound. -/
theorem abs_msLat_le_on [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) {t C : ℝ}
    {γ : Ix0 → ℝ} {γP : ℝ} (ht : 0 < t) {k : ℕ} {s : ℝ} (hs : 0 < s) (hk1 : dySpacing N k ≤ 1)
    {ι : Type} [Fintype ι] (F : ι → CDatum (CbR N zOne)) (hC1 : 1 ≤ C)
    (hS : ∀ i, ∀ j ∈ (c (F i).1 s).support, ScaleChan Wf t C γ γP k s j) :
    |msLat Wf c k s F|
      ≤ (1 + Fintype.card ι * (((2 * Fintype.card ι).factorial : ℝ) * (Real.exp C * C)))
        * ∏ i, (msTsize (F i).2 * msPsize t γ γP c s (F i).1) := by
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  unfold msLat
  refine abs_state_prod_le (stateK (NeZero.ne N) k)
    (fun i => smear (dySpacing N k) (msProx Wf c k s (F i).1) (F i).2)
    (fun i => msTsize (F i).2 * msPsize t γ γP c s (F i).1)
    (fun i => mul_pos (msTsize_pos _) (msPsize_pos ht γ γP c hs _)) (fun i => ?_)
  have hK0 : 0 ≤ Real.exp C * C := mul_nonneg (Real.exp_pos _).le (by linarith)
  set n := Fintype.card ι
  have h1 := moment_smear_le (stateK (NeZero.ne N) k)
    (MassGap.ContinuumNontrivial.stateK_transObs (NeZero.ne N) k) ha hk1
    (msProx Wf c k s (F i).1) (F i).2 (tIs (F i).2) n
  have h2 := msProx_moment_on Wf c ht hs hC1 (hS i) n
  have hT0 : 0 ≤ tM (F i).2 * (2 * tR (F i).2 + 3) ^ 4 :=
    mul_nonneg (tIs (F i).2).M_nonneg (by have := (tIs (F i).2).1; positivity)
  have hT : (tM (F i).2 * (2 * tR (F i).2 + 3) ^ 4) ^ (2 * n) ≤ msTsize (F i).2 ^ (2 * n) :=
    pow_le_pow_left₀ hT0 (by unfold msTsize; linarith) _
  have hP0 : 0 ≤ ((2 * n).factorial : ℝ) * (Real.exp C * C) * msPsize t γ γP c s (F i).1 ^ (2 * n) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hK0) (pow_nonneg (msPsize_pos ht γ γP c hs _).le _)
  calc stateK (NeZero.ne N) k (smear (dySpacing N k) (msProx Wf c k s (F i).1) (F i).2 ^ (2 * n))
      ≤ (tM (F i).2 * (2 * tR (F i).2 + 3) ^ 4) ^ (2 * n)
          * stateK (NeZero.ne N) k (msProx Wf c k s (F i).1 ^ (2 * n)) := h1
    _ ≤ (tM (F i).2 * (2 * tR (F i).2 + 3) ^ 4) ^ (2 * n)
          * (((2 * n).factorial : ℝ) * (Real.exp C * C) * msPsize t γ γP c s (F i).1 ^ (2 * n)) :=
        mul_le_mul_of_nonneg_left h2 (pow_nonneg hT0 _)
    _ ≤ msTsize (F i).2 ^ (2 * n)
          * (((2 * n).factorial : ℝ) * (Real.exp C * C) * msPsize t γ γP c s (F i).1 ^ (2 * n)) :=
        mul_le_mul_of_nonneg_right hT hP0
    _ = ((2 * n).factorial : ℝ) * (Real.exp C * C)
          * (msTsize (F i).2 * msPsize t γ γP c s (F i).1) ^ (2 * n) := by
        rw [mul_pow]; ring

/-- **The flowed reading in the `L¹` form with one `tᵢ`, `Cᵢ` per factor**: each factor's `e^{Cᵢ} Cᵢ` is
moved into its bound (`e^{Cᵢ} Cᵢ ≤ (e^{Cᵢ} Cᵢ)^{2n}`, `n ≥ 1`), so the common constant is `(2n)!`.
DERIVED: `2` the even powers; `1` the floor of `Cᵢ` and of `n`. -/
theorem abs_msLat_le_wS_pc [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ))
    {γ : Ix0 → ℝ} {γP : ℝ} {k : ℕ} {s : ℝ} (hs : 0 < s) {ι : Type} [Fintype ι]
    (F : ι → CDatum (CbR N zOne)) (tf Cf : ι → ℝ) (htf : ∀ i, 0 < tf i) (hCf : ∀ i, 1 ≤ Cf i)
    (hS : ∀ i, ∀ j ∈ (c (F i).1 s).support, ScaleChan Wf (tf i) (Cf i) γ γP k s j) :
    |msLat Wf c k s F|
      ≤ (1 + Fintype.card ι * ((2 * Fintype.card ι).factorial : ℝ))
        * ∏ i, ((wS (dySpacing N k) (F i).2 + dySpacing N k)
          * (Real.exp (Cf i) * Cf i * msPsize (tf i) γ γP c s (F i).1)) := by
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  have hK1 : ∀ i, 1 ≤ Real.exp (Cf i) * Cf i := fun i => by
    have := Real.add_one_le_exp (Cf i)
    nlinarith [hCf i]
  unfold msLat
  refine abs_state_prod_le (stateK (NeZero.ne N) k)
    (fun i => smear (dySpacing N k) (msProx Wf c k s (F i).1) (F i).2)
    (fun i => (wS (dySpacing N k) (F i).2 + dySpacing N k)
      * (Real.exp (Cf i) * Cf i * msPsize (tf i) γ γP c s (F i).1))
    (fun i => mul_pos (add_pos_of_nonneg_of_pos (wS_nonneg ha _) ha)
      (mul_pos (by linarith [hK1 i]) (msPsize_pos (htf i) γ γP c hs _)))
    (c := ((2 * Fintype.card ι).factorial : ℝ)) (fun i => ?_)
  set n := Fintype.card ι with hn
  set K := Real.exp (Cf i) * Cf i with hKdef
  set P := msPsize (tf i) γ γP c s (F i).1 with hPdef
  have hn1 : 1 ≤ 2 * n := by
    have : 0 < n := Fintype.card_pos_iff.2 ⟨i⟩
    omega
  have hKp : K ≤ K ^ (2 * n) := by
    calc K = K ^ 1 := (pow_one _).symm
      _ ≤ K ^ (2 * n) := pow_le_pow_right₀ (hK1 i) hn1
  have h1 := moment_smear_wS (stateK (NeZero.ne N) k)
    (MassGap.ContinuumNontrivial.stateK_transObs (NeZero.ne N) k) ha
    (msProx Wf c k s (F i).1) (F i).2 n
  have h2 := msProx_moment_on Wf c (htf i) hs (hCf i) (hS i) n
  have hW0 := wS_nonneg ha (F i).2
  have hP0 : 0 ≤ stateK (NeZero.ne N) k (msProx Wf c k s (F i).1 ^ (2 * n)) :=
    (stateK (NeZero.ne N) k).nonneg _ (fun U => by
      rw [ContinuousMap.pow_apply]
      exact (even_two_mul _).pow_nonneg _)
  have hPp : 0 ≤ P ^ (2 * n) := pow_nonneg (msPsize_pos (htf i) γ γP c hs _).le _
  have hf0 : (0 : ℝ) ≤ ((2 * n).factorial : ℝ) := Nat.cast_nonneg _
  have hWa : 0 ≤ (wS (dySpacing N k) (F i).2 + dySpacing N k) ^ (2 * n) := pow_nonneg (by linarith) _
  calc stateK (NeZero.ne N) k (smear (dySpacing N k) (msProx Wf c k s (F i).1) (F i).2 ^ (2 * n))
      ≤ wS (dySpacing N k) (F i).2 ^ (2 * n)
        * stateK (NeZero.ne N) k (msProx Wf c k s (F i).1 ^ (2 * n)) := h1
    _ ≤ (wS (dySpacing N k) (F i).2 + dySpacing N k) ^ (2 * n)
        * (((2 * n).factorial : ℝ) * K * P ^ (2 * n)) :=
        mul_le_mul (pow_le_pow_left₀ hW0 (by linarith) _) h2 hP0 hWa
    _ ≤ (wS (dySpacing N k) (F i).2 + dySpacing N k) ^ (2 * n)
        * (((2 * n).factorial : ℝ) * K ^ (2 * n) * P ^ (2 * n)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKp hf0) hPp)
          hWa
    _ = ((2 * n).factorial : ℝ)
        * ((wS (dySpacing N k) (F i).2 + dySpacing N k) * (K * P)) ^ (2 * n) := by
        rw [mul_pow, mul_pow]; ring

/-- **The continuum reading in the `L¹` form with one `tᵢ`, `Cᵢ` per factor** (`abs_msLat_le_wS_pc`,
`tendsto_wS`). DERIVED: `0` the limit of the spacing. -/
theorem abs_contC_le_pc [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {γ : Ix0 → ℝ} {γP : ℝ} {s : ℝ} (hs : 0 < s)
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → CDatum (CRen N z μ)) (hF : Adm F)
    (tf Cf : ι → ℝ) (htf : ∀ i, 0 < tf i) (hCf : ∀ i, 1 ≤ Cf i)
    (hS : ∀ᶠ k in atTop, ∀ i, ∀ j ∈ (c (F i).1 s).support, ScaleChan Wf (tf i) (Cf i) γ γP k s j)
    (hconv : ConvC (NeZero.ne N) (CRen N z μ)) {Rm : ℝ}
    (hrem : ∀ᶠ k in atTop, |latC (NeZero.ne N) (CRen N z μ) k F - msLat Wf c k s F| ≤ Rm) :
    |contC (NeZero.ne N) (CRen N z μ) F|
      ≤ (1 + Fintype.card ι * ((2 * Fintype.card ι).factorial : ℝ))
        * ∏ i, (l1 (F i).2 * (Real.exp (Cf i) * Cf i * msPsize (tf i) γ γP c s (F i).1)) + Rm := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hlim : Tendsto (fun k =>
      (1 + Fintype.card ι * ((2 * Fintype.card ι).factorial : ℝ))
        * ∏ i, ((wS (dySpacing N k) (F i).2 + dySpacing N k)
          * (Real.exp (Cf i) * Cf i * msPsize (tf i) γ γP c s (F i).1)) + Rm)
      atTop (𝓝 ((1 + Fintype.card ι * ((2 * Fintype.card ι).factorial : ℝ))
        * ∏ i, (l1 (F i).2 * (Real.exp (Cf i) * Cf i * msPsize (tf i) γ γP c s (F i).1)) + Rm)) := by
    refine (Tendsto.const_mul _ (tendsto_finsetProd _ fun i _ => ?_)).add_const Rm
    have h1 := ((tendsto_wS (N := N) (F i).2 (hF.1 i)).add (tendsto_dySpacing N)).mul_const
      (Real.exp (Cf i) * Cf i * msPsize (tf i) γ γP c s (F i).1)
    rwa [add_zero] at h1
  have hev : ∀ᶠ k in (ultra : Filter ℕ), |latC (NeZero.ne N) (CRen N z μ) k F|
      ≤ (1 + Fintype.card ι * ((2 * Fintype.card ι).factorial : ℝ))
        * ∏ i, ((wS (dySpacing N k) (F i).2 + dySpacing N k)
          * (Real.exp (Cf i) * Cf i * msPsize (tf i) γ γP c s (F i).1)) + Rm := by
    refine Filter.Eventually.filter_mono ultra_le ?_
    filter_upwards [hS, hrem] with k hk hr
    have hP := abs_msLat_le_wS_pc Wf c hs F tf Cf htf hCf hk
    have htri := abs_sub_abs_le_abs_sub (latC (NeZero.ne N) (CRen N z μ) k F) (msLat Wf c k s F)
    linarith
  exact le_of_tendsto_of_tendsto ((hconv ι F hF).abs) (hlim.mono_left ultra_le) hev

/-- **`MultiScaleOS.msLat_translate_sub_tendsto` on the supports of the family's coefficients.**
DERIVED: `2` the even powers; `1` the spacing bound; `0` the limit. -/
theorem msLat_translate_sub_tendsto_on [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ))
    {t C : ℝ} {γ : Ix0 → ℝ} {γP : ℝ} (ht : 0 < t) {s : ℝ} (hs : 0 < s) (hC1 : 1 ≤ C)
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → CDatum (CbR N zOne))
    (hS : ∀ᶠ k in atTop, ∀ i, ∀ j ∈ (c (F i).1 s).support, ScaleChan Wf t C γ γP k s j)
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
  set c0 : ℝ := ((2 * n).factorial : ℝ) * (Real.exp C * C) with hc0
  have hK0 : 0 ≤ c0 := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Real.exp_pos _).le (by linarith))
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
    have h2 := msProx_moment_on Wf c ht hs hC1 (hk i) n
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
    have h2 := msProx_moment_on Wf c ht hs hC1 (hk i) n
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

/-! ## 4. The consumers on the capstone path -/

/-- **`uv` from the plaquette class at `s = b`** (the proof of `CompositesRenAll.uv_of_scale`).
DERIVED: `4` the dimension; `2 · 1 + 3` the site count. -/
theorem uv_of_scalePC [NeZero N] {W : ConfFlow N} {b : ℝ} {Wf : ℝ → ConfFlow N} (hb : 0 < b)
    (htop : Wf b = W) (hsc : ScaleControlAllPC b Wf) :
    ∃ t C : ℝ, 0 < t ∧ FlowUV.SiteExp (NeZero.ne N) W (SymPlaqClass N) (t * (2 * 1 + 3) ^ 4) C := by
  obtain ⟨γ, γP, H⟩ := hsc
  obtain ⟨t, C, ht, hev⟩ := H.plaq
  have hpos : 0 < t * b ^ 4 / afLog γP b := div_pos (mul_pos ht (pow_pos hb 4)) (afLog_pos _ _)
  refine ⟨t * b ^ 4 / afLog γP b / (2 * 1 + 3) ^ 4, C, div_pos hpos (by norm_num), ?_⟩
  rw [div_mul_cancel₀ _ (by norm_num : ((2 : ℝ) * 1 + 3) ^ 4 ≠ 0)]
  unfold FlowUV.SiteExp
  filter_upwards [hev, (tendsto_dySpacing N).eventually (gt_mem_nhds hb)] with k hk hkb
  rintro O ⟨q, rfl⟩
  have h1 := hk b hkb.le le_rfl q
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

/-- **`BoundC (CRen N z μ)` from the per-channel scale input and `ExpandR`**: at `s = min(θ d, b)` the
channels read are the supports of the coefficients of the family's composites, a finite set.
DERIVED: `1` the spacing bound. -/
theorem boundC_ren_of_scalePC [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hsc : ScaleControlAllPC b Wf)
    (hex : ExpandR Wf c z μ) : InputsTriage.BoundC (NeZero.ne N) (CRen N z μ) := by
  classical
  obtain ⟨γ, γP, H⟩ := hsc
  obtain ⟨θ, ε, Kr, κr, hθ, -, hE⟩ := hex
  intro ι _ _ F hF
  obtain ⟨hcont, d, hd, hsep⟩ := hF
  have hs : 0 < min (θ * d) b := lt_min (mul_pos hθ hd) hb
  obtain ⟨t, C, ht, hC1, hev⟩ :=
    H.uniform (Finset.univ.biUnion fun i => (c (F i).1 (min (θ * d) b)).support)
  refine ⟨(1 + Fintype.card ι * (((2 * Fintype.card ι).factorial : ℝ) * (Real.exp C * C)))
      * ∏ i, (msTsize (F i).2 * msPsize t γ γP c (min (θ * d) b) (F i).1)
    + Kr ^ Fintype.card ι * (min (θ * d) b / d) ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2), ?_⟩
  refine Filter.Eventually.filter_mono ultra_le ?_
  filter_upwards [hev, hE ι F d hd hcont hsep (min (θ * d) b) hs (min_le_left _ _),
    (tendsto_dySpacing N).eventually (gt_mem_nhds hs),
    (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)] with k hk hrem hks hk1
  have hP := abs_msLat_le_on Wf c ht hs hk1.le F hC1 (fun i j hj =>
    hk _ hks.le (min_le_right _ _) j (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hj⟩))
  have htri := abs_sub_abs_le_abs_sub (latC (NeZero.ne N) (CRen N z μ) k F)
    (msLat Wf c k (min (θ * d) b) F)
  linarith

/-- **`ConvC (CRen N z μ)` from the per-channel scale input and `ExpandR`.** DERIVED: no numeral. -/
theorem convC_of_scalePC [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hsc : ScaleControlAllPC b Wf)
    (hex : ExpandR Wf c z μ) : ConvC (NeZero.ne N) (CRen N z μ) :=
  (InputsTriage.convC_iff_boundC _ _).2 (boundC_ren_of_scalePC hb hsc hex)

/-- **`OS1C (CRen N z μ)` from the per-channel scale input and `ExpandR`** (the proof of
`MultiScaleOS.os1C_of_scale_expand`; at the chosen `s` the channels are the supports of the family's
coefficients). DERIVED: `2` the halves; `0` the limit. -/
theorem os1C_of_scalePC [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hsc : ScaleControlAllPC b Wf)
    (hex : ExpandR Wf c z μ) : OS1C (NeZero.ne N) (CRen N z μ) := by
  classical
  have hconv : ConvC (NeZero.ne N) (CRen N z μ) := convC_of_scalePC hb hsc hex
  obtain ⟨γ, γP, H⟩ := hsc
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
    obtain ⟨t, C, ht, hC1, hevU⟩ := H.uniform (Finset.univ.biUnion fun i => (c (F i).1 s).support)
    have hS : ∀ᶠ k in atTop, ∀ i, ∀ j ∈ (c (F i).1 s).support, ScaleChan Wf t C γ γP k s j := by
      filter_upwards [hevU, (tendsto_dySpacing N).eventually (gt_mem_nhds hs)] with k hk hks i j hj
      exact hk s hks.le hsb j (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hj⟩)
    have hmid : Tendsto (fun k => msLat Wf c k s (fun i => translateD v (F i)) - msLat Wf c k s F)
        atTop (𝓝 0) := msLat_translate_sub_tendsto_on Wf c ht hs hC1 F hS hcont v
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

/-- **`OS0C (CRen N z μ)` from the per-channel scale input, `ExpandR` and `CoefBound`**: composite `i`
reads the finite channel set `S i`; its `tᵢ`, `Cᵢ` (`ScalePCAt.uniform` on `S i`) go into `Ccᵢ`, and
`α = 2 + θ'^ε`, `γ = 8`, `β = 2` are common. DERIVED: `8`, `2` from `one_add_mul_fact_le`; `1` the top of
the scale range. -/
theorem os0C_of_scalePC [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hsc : ScaleControlAllPC b Wf)
    (hex : ExpandR Wf c z μ) (hcoef : CoefBound c) : OS0C (NeZero.ne N) (CRen N z μ) := by
  have hconv : ConvC (NeZero.ne N) (CRen N z μ) := convC_of_scalePC hb hsc hex
  obtain ⟨S, K, γc, hcb⟩ := hcoef
  obtain ⟨γ, γP, H⟩ := hsc
  choose ti Ci hti hCi hev using fun i : Ix0 => H.uniform (S i)
  obtain ⟨θ, ε, Kr, κr, hθ, hε, hE⟩ := hex
  set θ' : ℝ := min θ (min b 1) with hθ'def
  have hθ'0 : 0 < θ' := lt_min hθ (lt_min hb one_pos)
  have hθ'θ : θ' ≤ θ := min_le_left _ _
  have hθ'b : θ' ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hθ'1 : θ' ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hK1 : ∀ i, 1 ≤ Real.exp (Ci i) * Ci i := fun i => by
    have := Real.add_one_le_exp (Ci i)
    nlinarith [hCi i]
  set P : Ix0 → ℝ := fun i =>
    Real.exp (Ci i) * Ci i * (((S i).card : ℝ) ^ 2 * (max (K i) 0 / ti i) + 1) with hPdef
  have hPpos : ∀ i, 0 < P i := fun i => by
    have : 0 ≤ ((S i).card : ℝ) ^ 2 * (max (K i) 0 / ti i) :=
      mul_nonneg (sq_nonneg _) (div_nonneg (le_max_right _ _) (hti i).le)
    exact mul_pos (by linarith [hK1 i]) (by linarith)
  refine ⟨2 + θ' ^ ε, 8, 2, fun i => P i * θ'⁻¹ ^ kap γ γP γc S i + |Kr|,
    fun i => max (kap γ γP γc S i) (κr i), ?_⟩
  intro n F d hd hd1 hcont hsep
  beta_reduce
  have hs : 0 < θ' * d := mul_pos hθ'0 hd
  have hsθ : θ' * d ≤ θ * d := mul_le_mul_of_nonneg_right hθ'θ hd.le
  have hsθ' : θ' * d ≤ θ' := mul_le_of_le_one_right hθ'0.le hd1
  have hsb : θ' * d ≤ b := hsθ'.trans hθ'b
  have hs1 : θ' * d ≤ 1 := hsθ'.trans hθ'1
  have hS : ∀ᶠ k in atTop, ∀ i, ∀ j ∈ (c (F i).1 (θ' * d)).support,
      ScaleChan Wf (ti (F i).1) (Ci (F i).1) γ γP k (θ' * d) j := by
    have hall := (Filter.eventually_all (ι := Fin n)).2 fun i => hev (F i).1
    filter_upwards [hall, (tendsto_dySpacing N).eventually (gt_mem_nhds hs)] with k hk hks i j hj
    exact hk i (θ' * d) hks.le hsb j ((hcb (F i).1 (θ' * d) hs hs1).1 hj)
  have hA := abs_contC_le_pc hs F ⟨hcont, d, hd, hsep⟩ (fun i => ti (F i).1) (fun i => Ci (F i).1)
    (fun i => hti _) (fun i => hCi _) hS hconv (hE (Fin n) F d hd hcont hsep (θ' * d) hs hsθ)
  have hsd : θ' * d / d = θ' := mul_div_cancel_right₀ θ' hd.ne'
  rw [Fintype.card_fin, hsd] at hA
  have hl1 : ∀ i, 0 ≤ l1 (F i).2 := fun i => MeasureTheory.integral_nonneg fun x => abs_nonneg _
  have hPs : ∀ i, Real.exp (Ci (F i).1) * Ci (F i).1 * msPsize (ti (F i).1) γ γP c (θ' * d) (F i).1
      ≤ P (F i).1 * (θ' * d)⁻¹ ^ kap γ γP γc S (F i).1 := fun i => by
    have h := msPsize_le (hti (F i).1) γ γP c hcb (F i).1 hs hs1
    have hm := mul_le_mul_of_nonneg_left h (by linarith [hK1 (F i).1] :
      (0 : ℝ) ≤ Real.exp (Ci (F i).1) * Ci (F i).1)
    calc _ ≤ _ := hm
      _ = P (F i).1 * (θ' * d)⁻¹ ^ kap γ γP γc S (F i).1 := by simp only [hPdef]; ring
  have hfac : ∀ i, l1 (F i).2
        * (Real.exp (Ci (F i).1) * Ci (F i).1 * msPsize (ti (F i).1) γ γP c (θ' * d) (F i).1)
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
  have hF0 : ∀ i, 0 ≤ l1 (F i).2
      * (Real.exp (Ci (F i).1) * Ci (F i).1 * msPsize (ti (F i).1) γ γP c (θ' * d) (F i).1) :=
    fun i => mul_nonneg (hl1 i) (mul_nonneg (by linarith [hK1 (F i).1])
      (msPsize_pos (hti _) γ γP c hs _).le)
  have hPi1 : ∏ i, (l1 (F i).2
        * (Real.exp (Ci (F i).1) * Ci (F i).1 * msPsize (ti (F i).1) γ γP c (θ' * d) (F i).1))
      ≤ ∏ i, (P (F i).1 * θ'⁻¹ ^ kap γ γP γc S (F i).1 + |Kr|)
        * (d ^ max (kap γ γP γc S (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2 :=
    Finset.prod_le_prod (fun i _ => hF0 i) (fun i _ => (hfac i).1)
  have hPi10 : 0 ≤ ∏ i, (l1 (F i).2
        * (Real.exp (Ci (F i).1) * Ci (F i).1 * msPsize (ti (F i).1) γ γP c (θ' * d) (F i).1)) :=
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
  have hmain1 : 1 + (n : ℝ) * ((2 * n).factorial : ℝ) ≤ (1 + 1) * 8 ^ n * (n.factorial : ℝ) ^ 2 := by
    have := one_add_mul_fact_le n (zero_le_one' ℝ)
    simpa only [mul_one] using this
  have h8 : (1 : ℝ) ≤ 8 ^ n * (n.factorial : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ 8 ^ n := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ (n.factorial : ℝ) ^ 2 :=
      one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n))
    nlinarith
  have hX : 0 ≤ (1 + 1 : ℝ) * 8 ^ n * (n.factorial : ℝ) ^ 2 := by positivity
  have hM := mul_le_mul hmain1 hPi1 hPi10 hX
  have hR2 := mul_le_mul_of_nonneg_left hPi2 hθε
  have hR3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h8 hθε) hZ0
  rw [Real.rpow_two]
  linarith

/-! ## 5. The substrate core per channel and the bundle -/

/-- **The substrate core with the per-channel scale input**: `SU2Best.SubstrateCoreAt` with `scale` replaced
by `ScaleControlAllPC b Wf`. DERIVED: no numeral. -/
structure SubstrateCorePC [NeZero N] (W : ConfFlow N) (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow N) :
    Prop where
  b_pos : 0 < b
  /-- The flow to the physical scale is `W`. -/
  top : Wf b = W
  /-- Every intermediate scale, per channel. -/
  scale : ScaleControlAllPC b Wf
  /-- Asymptotic freedom: a two-point kernel of the trace at `z` with the asymptotic-freedom coefficient. -/
  af : ∃ G : ℝ → ℝ, TwoPointKernel (NeZero.ne N) (rhoD (fR N) z) G ∧ AFCoefficient N G

/-- `SubstrateCoreAt` gives `SubstrateCorePC`. DERIVED: no numeral. -/
theorem substrateCorePC_of_core [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {b : ℝ}
    {Wf : ℝ → ConfFlow N} (S : SubstrateCoreAt W z b Wf) : SubstrateCorePC W z b Wf :=
  ⟨S.b_pos, S.top, scaleControlAllPC_of_scaleControlAll S.scale, S.af⟩

/-- **`ClayNarrow.compOS_of_covC` from the per-channel core.** DERIVED: no numeral. -/
theorem compOS_of_covC_pc [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (S : SubstrateCorePC W z b Wf)
    (hE : ExpandStrong Wf cf z μ) (hcb : CoefBound cf) (hV : CovC (NeZero.ne N) (CRen N z μ))
    (hP : CompNondeg (NeZero.ne N) (CRen N z μ)) : CompOS (NeZero.ne N) (CRen N z μ) :=
  ⟨convC_of_scalePC S.b_pos S.scale (expandR_of_strong hE),
    os0C_of_scalePC S.b_pos S.scale (expandR_of_strong hE) hcb,
    os1C_of_scalePC S.b_pos S.scale (expandR_of_strong hE), hV, hP⟩

/-- **`ClayNarrow.approxK_of_beyond_covC` from the per-channel core.** DERIVED: `2` the least colour count;
`0` the plane and the reference step. -/
theorem approxK_of_beyond_covC_pc (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ}
    {μ : OffMix} {b r : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCorePC W z b Wf) (hE : ExpandStrong Wf cf z μ) (hcb : CoefBound cf)
    (hV : CovC (NeZero.ne N) (CRen N z μ)) (hP : CompNondeg (NeZero.ne N) (CRen N z μ))
    (hphys : (Φ0 W).PhysRange r)
    (hB : ∀ P, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N z μ) 0)
      (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) P) :
    ApproxK (kernC (NeZero.ne N) (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) := by
  obtain ⟨t, C, ht, hS⟩ := uv_of_scalePC S.b_pos S.top S.scale
  have hU := ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) W ht hS
  have hCO := compOS_of_covC_pc S hE hcb hV hP
  let D := capData hN2 W hU hphys (CRen N z μ)
    (unifLocal_buildRen (rhoD (fR N) z) (bareD (fR N) (bR N)) μ) (reflCovLat_CRen z μ) hCO
  refine approxK_iff_forall.2 fun P => ?_
  obtain ⟨n, hn⟩ := exists_beyond_iterate (NeZero.ne N) r P
  exact approxKAt_of_iterate D 0 n P (hB _ hn)

/-- **`ClayNarrowMG.inputsAt_of_covC_phys` from the per-channel core.** DERIVED: `2` the least colour
count; `0` the lower end of the scale. -/
theorem inputsAt_of_covC_phys_pc (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {r : ℝ}
    {zri zwe : ℕ → ℝ} (hri : ∀ k, zri k ≠ 0) (hwe : ∀ k, zwe k ≠ 0) {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCorePC W (ZCanon.zFix N zri zwe) b Wf)
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
  obtain ⟨t, C, ht, hS⟩ := uv_of_scalePC S.b_pos S.top S.scale
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
      comp := compOS_of_covC_pc S hE hcb hV hP
      approx := hA }⟩

/-- **The per-`N` inputs with the per-channel scale input**: `ClayNarrowMG.NarrowInputsAt` with
`SubstrateCoreAt` replaced by `SubstrateCorePC`. DERIVED: `2` the least colour count; `0` the plane and the
reference step. -/
def NarrowInputsAtPC (N : ℕ) (hN2 : 2 ≤ N) (W : ConfFlow N) (r : ℝ) : Prop :=
  haveI : NeZero N := ⟨by omega⟩
  (Φ0 W).PhysRange r ∧
  ∃ (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)),
    SubstrateCorePC W (ZCanon.zFix N zri zwe) b Wf
      ∧ ExpandStrong Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ CoefBound cf
      ∧ CovC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ WardT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe))
      ∧ CompNondeg (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ (∀ P, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
          (mixKG hN2 W (CRen N (ZCanon.zFix N zri zwe) μ) r) (gramF hN2 W r) P)
      ∧ (∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (ne_zero_of_two_le hN2) ℓ)
      ∧ RunSeedN.EndpointN N

/-- **`NarrowInputsAt` gives `NarrowInputsAtPC`** at the same witnesses (`substrateCorePC_of_core`).
DERIVED: `2` the least colour count. -/
theorem narrowInputsAtPC_of_narrowAt (hN2 : 2 ≤ N) {W : ConfFlow N} {r : ℝ}
    (h : NarrowInputsAt N hN2 W r) : NarrowInputsAtPC N hN2 W r := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP, hB, h3, hEnd⟩ := h
  exact ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, substrateCorePC_of_core S, hE, hC, hV, hW, hP, hB, h3, hEnd⟩

/-- **`NarrowInputsAtPC` gives the general-`N` bundle at `W`** (`approxK_of_beyond_covC_pc`,
`RunSeedN.runSeed_of_endpointN`, `inputsAt_of_covC_phys_pc`). DERIVED: `2` the least colour count. -/
theorem clayInputsN_of_narrowAtPC (hN2 : 2 ≤ N) {W : ConfFlow N} {r : ℝ}
    (h : NarrowInputsAtPC N hN2 W r) : SUNBest.ClayInputsN N hN2 := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP, hB, h3, hEnd⟩ := h
  obtain ⟨t, C, G, I⟩ := inputsAt_of_covC_phys_pc hN2 hri hwe S hE hC hV hW hP hphys
    (approxK_of_beyond_covC_pc hN2 S hE hC hV hP hphys hB) h3 (RunSeedN.runSeed_of_endpointN hEnd)
  exact ⟨W, r, t, |C|, zri, zwe, μ, G, I⟩

end MassGap.ScalePC

end

#print axioms MassGap.ScalePC.scaleControlAllPC_of_scaleControlAll
#print axioms MassGap.ScalePC.scaleChan_mono
#print axioms MassGap.ScalePC.ScalePCAt.uniform
#print axioms MassGap.ScalePC.msFlow_moment_chan
#print axioms MassGap.ScalePC.msProx_moment_on
#print axioms MassGap.ScalePC.abs_msLat_le_on
#print axioms MassGap.ScalePC.abs_msLat_le_wS_pc
#print axioms MassGap.ScalePC.abs_contC_le_pc
#print axioms MassGap.ScalePC.msLat_translate_sub_tendsto_on
#print axioms MassGap.ScalePC.uv_of_scalePC
#print axioms MassGap.ScalePC.boundC_ren_of_scalePC
#print axioms MassGap.ScalePC.convC_of_scalePC
#print axioms MassGap.ScalePC.os1C_of_scalePC
#print axioms MassGap.ScalePC.os0C_of_scalePC
#print axioms MassGap.ScalePC.substrateCorePC_of_core
#print axioms MassGap.ScalePC.compOS_of_covC_pc
#print axioms MassGap.ScalePC.approxK_of_beyond_covC_pc
#print axioms MassGap.ScalePC.inputsAt_of_covC_phys_pc
#print axioms MassGap.ScalePC.narrowInputsAtPC_of_narrowAt
#print axioms MassGap.ScalePC.clayInputsN_of_narrowAtPC
