import Mathlib
import MassGap.BulkBound
import MassGap.ObserverTower

/-!
# MassGap.BlFamCore — the substrate core at the ray-averaged observer below scale `1`

`ObserverTower.clayStatementOf_of_coreObs` reads the observer only through its physical range and the
flow core `ObserverTower.CoreInputsAlongW`. The ray-averaged observer `ObserverBlock.blFam` has a physical
range (`ObserverBlock.blFam_physRange`) and is not eventually the identity
(`ObserverBlock.blFam_not_eventually_id`); at `b ≥ 1` its core is refuted (`BulkBound`). This module tests
the core at `blFam` with `b < 1`, states the residual, and gives the root at `blFam`. Declarations are in the
namespace `MassGap.BlFamCore`.

## 1. The rough tail: a refutation at every `b > 0` (proved)

`cutF W k ρ = min(1, max(0, x − ρ))`, `x = N − Re tr (V_k U)_p` the flowed origin plaquette defect.

* **`exp_mul_cut_le_of_scaleAt`**: `ScaleAt Wf t C γ γP k s` with `t, s > 0` gives, for every channel
  `jn n` of `BulkBound`'s tower (dimension `4(n + 1)`) and every `ρ ≥ 0`,
  `exp(μ_n(s) a_k^{−4(n+1)} · ½ ρ^{2(n+1)}) · ν_k(cutF (Wf s) k ρ) ≤ C`, `μ_n(s) = msMu t γ γP (jn n) s`.
  One channel, any scale `s`: the factor `(1 + |log s|)^{γ_n}` enters as a fixed positive number.
* `RoughTail W`: some `ρ > 0` and channel `n` with, for every `L > 0`, frequently
  `ν_k(cutF W k ρ) ≥ exp(−L a_k^{−4(n+1)})`: rough flowed plaquettes keep a probability that does not
  decay at the rate `a_k^{−4(n+1)}`.
* **`not_scaleControlAll_of_roughTail`**: `b > 0` and `RoughTail (Wf b)` give `¬ ScaleControlAll b Wf`.
  `not_substrateCoreAt_of_roughTail`: `RoughTail W` refutes `SubstrateCoreAt W z b Wf` for every `z`,
  `b`, `Wf` (through `top`).
* **`cut_decay_of_scaleControlAll`** (the same, read forward): `ScaleControlAll b Wf` at `b > 0` forces, for
  every `ρ > 0` and every `n`, some `L > 0` with eventually `ν_k(cutF (Wf b) k ρ) < exp(−L a_k^{−4(n+1)})`.

## 2. The no-go patterns at `blFam`, `b < 1`

* Identity (`ScaleIdentityNoGo`): does not apply, `ObserverBlock.blFam_not_eventually_id` (proved).
* Plaquette leak (`SunFamLeak.PlaqLeak`): not decided. `blFam` holds no boundary, so the boundary weight
  of `SunFamLeak` §3 is absent; the bulk flowed plaquette mean `O(a_k⁴)` is not proved either.
* The sup bound of `BulkBound` §3: does not apply below `1` (proved, `exists_gamma_tower_le_one`). Its
  proof runs the channel tower `n → ∞` at one step; at `s = b < 1` the tower term is
  `(t/2) q^{n+1} / (1 + |log b|)^{γ_n}` with `q = ρ² b⁴ / a_k⁴` (the `2` is the reflection average `½` of
  `BulkBound.chan_ge`), and the choice `γ_i = cdim(i)²` makes the ratio `q^{n+1} / (1 + |log b|)^{γ_n}`
  eventually at most `1` for every `q`, so the term stays bounded in `n`. `MW` reads `s = 1` only.
* The `π`-flux fixed point: it persists at every member and every step, `facV_blFam_fpi` (`x = 4`), and
  the rough set is charged at every step, `stateK_cutF_blFam_pos` (`ν_k(cutF … ρ) > 0` for `ρ < 4`,
  by `BulkBound.stateK_pos_of_local`). Section 1 turns it into a refutation once the charge has a rate:
  `RoughTail (blFam …)` refutes the core at every `b > 0`, including `b < 1`.

**`RoughTail` at `blFam` (argued, not a declaration).** `cutF` is local on the read set of the origin
plaquette, `≍ (s₀/a_k)⁴` links (`ObserverMultigrid.mgRange`). The DLR bound behind
`BulkBound.periodicState_pos_of_local` gives `ν_k(G) ≥ e^{−2β_k |∂S|} ∫ G(splice u P) du`. One block step
at stride `d` moves its output by at most a factor, depending on `c` and `d` only, times the sup-norm change
of its inputs (each staple has a number of links linear in its length and weight `c/d`, and the polar
projection is Lipschitz on the slit domain), so `blMap` has a sup-norm Lipschitz constant `≤ e^{O(m J_k²)}`,
`J_k ≍ log₂(s₀/a_k)`. A sup-norm ball
of radius `ε_k = e^{−O(m log²(1/a_k))}` around the `π`-flux configuration then keeps `x > ρ` for `ρ < 4`,
and its Haar measure is `≥ ε_k^{O((s₀/a_k)⁴)}`. Together
`log ν_k(cutF) ≥ −O((s₀/a_k)⁴ (β_k + m log²(1/a_k)))`, which is `o(a_k^{−8})` when `β_k a_k⁴ → 0`
(true along a logarithmically running tower), so `RoughTail` holds with `n = 1`. Lean has no lower bound
on the Haar measure of a ball in `SU(N)` and no Lipschitz bound for `ObserverFlowSUN.projMat`; these are
the two missing pieces.

**The mechanism (argued).** The scale field asks an exponential moment of every monomial with one rate.
For the channel of dimension `8` (`4(n + 1)` at `n = 1`) that moment weighs a rough output at rate
`a_k^{−8}`, while the Wilson measure charges any configuration on a read set of `(s₀/a_k)⁴` links at rate
`a_k^{−4}` up to logarithms. `ScalePC` §3 argues the same conflict channel by channel: with one `tⱼ`, `Cⱼ`
per channel the tail bound still falls at rate `a_k^{−d_j}`, against the positivity floor
`exp(−c (s/a_k)⁴ log(s/a_k))`, once `d_j > 4`; per-channel constants do not remove it. Any observer with a
rough output on a set of non-negligible size fails, at every `b > 0`. Every averaging observer in the tree
has rough fixed points: sign configurations for `sunFam`, `mgFam` (`SunFamFlux`), the `π`-flux slice for
`blFam`; the gradient flow of the Wilson action has the `π`-flux saddle. An observer escapes only if, for
every `ρ > 0`, its outputs with origin defect `> ρ` form a set of probability below every
`e^{−L a_k^{−4(n+1)}}` (`cut_decay_of_scaleControlAll`, proved); with the charge rate above, this asks a
deterministic smoother: `sup_U x(V_k U) → 0`. No family in the tree has that property (argued; at `blFam`
the defect of the `π`-flux configuration is `4` at every step, `facV_blFam_fpi`), and whether a continuous,
gauge-covariant, local observer with it exists is not decided here. The obstruction lives in the
exponential moments of the channels of dimension `> 4` (the dimensions `5`, `6` included, outside the
`jn` tower), not in the choice of observer.

The existing escape is `ScalePM.ScaleControlAllPM`: exponential only on the plaquette class at `s = b`
(dimension `4`, where the floor lies below every `exp(−L a_k^{−4})` and puts no bound on the tail), and on
every other channel the moments of fixed order `2p` with growth `((2p)!)^r`, the order and the scale fixed
before the step grows. At fixed
order the positivity floor tends to `0` (`ScalePM` §4, argued; `ObserverTowerPM.tendsto_roughFloor`), so
those moments beat `RoughTail` at every `d_j`. `ObserverTowerPM` states the root through it.

## 3. The fields provable at `blFam` and the residual

Proved at `blFam`: the physical range (`blFam_physRange`, any `r ≥ s₀ ≥ 0`), non-identity, `b_pos` and
`top` (any `b > 0`, `Wf := fun _ => blFam …`), and `CoefBound` alone (`coefBound_zero`; the
coefficients are constrained only jointly with `ExpandStrong` and `ProxyNondeg`). No other field is proved.
`af` and `ThreePointAtScale` do not read the observer; `ExpandStrong`, `CoefBound`, `FlowCovLim`,
`FlowWard`, `ProxyNondeg` read `Wf` and `cf` near `s = 0⁺` only; the observer `W = blFam …` enters through
`top` (with `scale` at `s = b`) and the germ `ProxyGenLimGerm W b Wf cf r`.

* `BlFamCoreAlong N βs`: `ObserverTower.CoreInputsAlongW N βs` at `W = blFam … m s₀` with `r ≥ s₀ ≥ 0`,
  the physical range discharged. `coreW_of_blFamCore`: `BlFamCoreAlong ⇒ CoreInputsAlongW`.
* **`clayStatementOf_of_blFamCore`**: `StrongEnd N`, (UV) and `BlFamCoreAlong` along the towers near `0⁺`
  give `ClayStatementOf (SU N)`.
* **`not_blFamCoreAlong_of_roughTail`**: the copy of `RoughTail` along `βs` at every member refutes
  `BlFamCoreAlong N βs`. By §2 (argued) the hypothesis of the capstone is false along logarithmic towers.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the signs and the limit `0⁺`; `1` the cut-off's ceiling, the scale bound
`b < 1` and the shift `n + 1`; `1/2` the reflection average of `BulkBound.chan_ge`; `2` the even power,
the least rank, the base of the dyadic logarithm and the boundary weight `2β_k`; `4` the dimension per
pair of `p1` factors, the `π`-flux defect and the link count `(s₀/a_k)⁴` of a read set; `8 = 4(n + 1)` at
`n = 1`, the dimension-`8` channel; `12` the coupling bound inherited from `blFam`; `π` in `π/N`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.BlFamCore

open MassGap.SUN (SU)
open MassGap.InfiniteLattice MassGap.ContinuumFlow MassGap.ContinuumSchwinger MassGap.MultiScaleAll
  MassGap.ClayStatement MassGap.ClassicalLimit MassGap.CompositesBuild MassGap.ObserverEnergyBox
  MassGap.ObserverMultigrid MassGap.ObserverBlock MassGap.BulkBound MassGap.ClayData
open Filter
open scoped Topology

/-! ## 1. The rough tail -/

section Rough

variable {N : ℕ}

/-- **The rough cut-off** `min(1, max(0, x − ρ))` of the flowed origin plaquette defect
`x = (flowP W k)(U) = N − Re tr (V_k U)_p`. DERIVED: `0`, `1` the clamp. -/
def cutF (W : ConfFlow N) (k : ℕ) (ρ : ℝ) : C(Cfg N, ℝ) :=
  ⟨fun U => min 1 (max 0 ((flowP W k).1 U - ρ)),
    continuous_const.min (continuous_const.max ((flowP W k).1.continuous.sub continuous_const))⟩

/-- DERIVED: `0`, `1` the clamp. -/
theorem cutF_apply (W : ConfFlow N) (k : ℕ) (ρ : ℝ) (U : Cfg N) :
    cutF W k ρ U = min 1 (max 0 (facV (W.V k U) p1 - ρ)) := by
  show min 1 (max 0 ((flowP W k).1 U - ρ)) = _
  rw [flowP_apply]

/-- **One channel of the tower at any scale `s`**: the scale clause bounds the rough probability by the
channel's weight. DERIVED: `0` the signs; `1/2`, `2` from `BulkBound.chan_ge`; `4` the dimension per pair
of `p1` factors; `1` the shift and the cut-off's ceiling. -/
theorem exp_mul_cut_le_of_scaleAt [NeZero N] {Wf : ℝ → ConfFlow N} {t C : ℝ} {γ : Ix0 → ℝ} {γP : ℝ}
    {k : ℕ} {s : ℝ} (ht : 0 < t) (hs : 0 < s) (h : ScaleAt Wf t C γ γP k s) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (n : ℕ) :
    Real.exp (msMu t γ γP (Sum.inl (jn n)) s / dySpacing N k ^ (4 * (n + 1))
        * ((1 / 2 : ℝ) * ρ ^ (2 * (n + 1))))
      * stateK (NeZero.ne N) k (cutF (Wf s) k ρ) ≤ C := by
  have hN : N ≠ 0 := NeZero.ne N
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.one_le_iff_ne_zero.mpr hN) k
  have hlam : 0 ≤ msMu t γ γP (Sum.inl (jn n)) s / dySpacing N k ^ (4 * (n + 1)) :=
    div_nonneg (msMu_pos ht γ γP hs _).le (pow_pos ha _).le
  have hj := h (Sum.inl (jn n))
  have hd : mDim (Sum.inl (jn n)) = 4 * (n + 1) := cdim_mono n
  rw [hd] at hj
  have hpt : ∀ U : Cfg N,
      (Real.exp (msMu t γ γP (Sum.inl (jn n)) s / dySpacing N k ^ (4 * (n + 1))
          * ((1 / 2 : ℝ) * ρ ^ (2 * (n + 1)))) • cutF (Wf s) k ρ) U
        ≤ expC ((msMu t γ γP (Sum.inl (jn n)) s / dySpacing N k ^ (4 * (n + 1)))
            • msAbs ((Wf s).fieldMap k (mField (Sum.inl (jn n)))).1) U := by
    intro U
    simp only [ContinuousMap.smul_apply, smul_eq_mul, expC_apply, msAbs_apply]
    rw [cutF_apply]
    by_cases hc : facV ((Wf s).V k U) p1 ≤ ρ
    · rw [max_eq_left (by linarith), min_eq_right zero_le_one, mul_zero]
      exact (Real.exp_pos _).le
    · replace hc := not_le.mp hc
      have hX : (1 / 2 : ℝ) * ρ ^ (2 * (n + 1))
          ≤ |((Wf s).fieldMap k (mField (Sum.inl (jn n)))).1 U| := by
        have hc' := chan_ge (N := N) n ((Wf s).V k U)
        have hpow : ρ ^ (2 * (n + 1)) ≤ facV ((Wf s).V k U) p1 ^ (2 * (n + 1)) :=
          pow_le_pow_left₀ hρ hc.le _
        have hval : ((Wf s).fieldMap k (mField (Sum.inl (jn n)))).1 U
            = (MassGap.ReflAvg.bR N (jn n)).1 ((Wf s).V k U) := rfl
        rw [hval]
        exact le_trans (by linarith) (le_abs_self _)
      have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hX hlam)
      have hG1 : min 1 (max 0 (facV ((Wf s).V k U) p1 - ρ)) ≤ 1 := min_le_left _ _
      calc _ ≤ Real.exp (msMu t γ γP (Sum.inl (jn n)) s / dySpacing N k ^ (4 * (n + 1))
            * ((1 / 2 : ℝ) * ρ ^ (2 * (n + 1)))) * 1 :=
            mul_le_mul_of_nonneg_left hG1 (Real.exp_pos _).le
        _ ≤ _ := by rw [mul_one]; exact hexp
  have hmono := (stateK hN k).mono hpt
  rw [(stateK hN k).map_smul] at hmono
  exact hmono.trans hj

/-- **A rough tail**: some `ρ > 0` and channel `n` with, for every `L > 0`, frequently
`ν_k(cutF W k ρ) ≥ exp(−L / a_k^{4(n+1)})`. DERIVED: `0` the signs; `4` the dimension per pair of `p1`
factors; `1` the shift. -/
def RoughTail [NeZero N] (W : ConfFlow N) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∃ n : ℕ, ∀ L : ℝ, 0 < L → ∃ᶠ k in atTop,
    Real.exp (-(L / dySpacing N k ^ (4 * (n + 1)))) ≤ stateK (NeZero.ne N) k (cutF W k ρ)

/-- **A rough tail at the physical-scale flow excludes `ScaleControlAll`, at every `b > 0`.**
DERIVED: `0` the signs and the limit of the spacing; `1/2`, `2` from `exp_mul_cut_le_of_scaleAt` and the
halved rate; `4`, `1` the channel's dimension. -/
theorem not_scaleControlAll_of_roughTail [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    (hR : RoughTail (Wf b)) : ¬ ScaleControlAll b Wf := by
  rintro ⟨t, C, γ, γP, ht, hev⟩
  obtain ⟨ρ, hρ, n, hL⟩ := hR
  have hN : N ≠ 0 := NeZero.ne N
  have hμ0 : 0 < msMu t γ γP (Sum.inl (jn n)) b := msMu_pos ht γ γP hb _
  set K : ℝ := msMu t γ γP (Sum.inl (jn n)) b * ((1 / 2 : ℝ) * ρ ^ (2 * (n + 1))) with hK
  have hK0 : 0 < K := mul_pos hμ0 (mul_pos (by norm_num) (pow_pos hρ _))
  have hC1 : 0 < 2 * (|C| + 1) := by positivity
  have hε : 0 < K / (2 * (|C| + 1)) := div_pos hK0 hC1
  have hsmall : ∀ᶠ k in atTop, dySpacing N k ≤ b :=
    (tendsto_dySpacing N).eventually (eventually_le_nhds hb)
  have hpow : Tendsto (fun k => dySpacing N k ^ (4 * (n + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_dySpacing N).pow (4 * (n + 1))
  have hsm2 : ∀ᶠ k in atTop, dySpacing N k ^ (4 * (n + 1)) < K / (2 * (|C| + 1)) :=
    hpow.eventually (gt_mem_nhds hε)
  obtain ⟨k, hk, ⟨hev', hsk⟩, hsk2⟩ :=
    ((hL (K / 2) (half_pos hK0)).and_eventually ((hev.and hsmall).and hsm2)).exists
  have hA := exp_mul_cut_le_of_scaleAt ht hb (hev' b hsk le_rfl) hρ.le n
  have hp0 : 0 < dySpacing N k ^ (4 * (n + 1)) :=
    pow_pos (dySpacing_pos (Nat.one_le_iff_ne_zero.mpr hN) k) _
  set p : ℝ := dySpacing N k ^ (4 * (n + 1)) with hp
  have he : msMu t γ γP (Sum.inl (jn n)) b / p * ((1 / 2 : ℝ) * ρ ^ (2 * (n + 1))) = K / p := by
    rw [hK]; ring
  rw [he] at hA
  have h1 : Real.exp (K / p) * Real.exp (-(K / 2 / p)) ≤ C :=
    le_trans (mul_le_mul_of_nonneg_left hk (Real.exp_pos _).le) hA
  rw [← Real.exp_add] at h1
  have h2 : K / p + -(K / 2 / p) = K / (2 * p) := by field_simp; ring
  rw [h2] at h1
  have h3 := Real.add_one_le_exp (K / (2 * p))
  have h4 : |C| + 1 < K / (2 * p) := by
    rw [lt_div_iff₀ (mul_pos two_pos hp0)]
    rw [lt_div_iff₀ hC1] at hsk2
    nlinarith [hsk2]
  linarith [le_abs_self C]

/-- **No substrate core at an observer with a rough tail**, any `z`, `b`, `Wf`. DERIVED: no numeral. -/
theorem not_substrateCoreAt_of_roughTail [NeZero N] {W : ConfFlow N} (hR : RoughTail W)
    (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow N) : ¬ SU2Best.SubstrateCoreAt W z b Wf := fun S =>
  not_scaleControlAll_of_roughTail S.b_pos (by rw [S.top]; exact hR) S.scale

/-- **What the scale field asks of the observer at `s = b`**: for every `ρ > 0` and every channel `n`, the
rough probability decays faster than some `exp(−L / a_k^{4(n+1)})`. DERIVED: `0` the signs; `4`, `1` the
channel's dimension. -/
theorem cut_decay_of_scaleControlAll [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    (h : ScaleControlAll b Wf) {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    ∃ L : ℝ, 0 < L ∧ ∀ᶠ k in atTop,
      stateK (NeZero.ne N) k (cutF (Wf b) k ρ) < Real.exp (-(L / dySpacing N k ^ (4 * (n + 1)))) := by
  by_contra hc
  refine not_scaleControlAll_of_roughTail hb ⟨ρ, hρ, n, fun L hL => ?_⟩ h
  have h1 : ¬ ∀ᶠ k in atTop, stateK (NeZero.ne N) k (cutF (Wf b) k ρ)
      < Real.exp (-(L / dySpacing N k ^ (4 * (n + 1)))) := fun hev => hc ⟨L, hL, hev⟩
  rw [Filter.not_eventually] at h1
  exact h1.mono fun k hk => not_lt.mp hk

end Rough

/-! ## 2. The no-go patterns at `blFam` below scale `1` -/

section Patterns

/-- **The sup-bound route of `BulkBound` does not run below scale `1`**: for `0 < b < 1` some `γ` makes
every tower term `q^{n+1} / (1 + |log b|)^{γ(jn n)}` eventually at most `1`, for every `q`.
DERIVED: `0`, `1` the window of `b`; `1` the shift and the bound. -/
theorem exists_gamma_tower_le_one {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∃ γ : Ix0 → ℝ, ∀ q : ℝ, ∀ᶠ n in atTop, q ^ (n + 1) / afLog (γ (jn n)) b ≤ 1 := by
  refine ⟨fun i => ((cdim i.1 ^ 2 : ℕ) : ℝ), fun q => ?_⟩
  set B : ℝ := 1 + |Real.log b| with hB
  have hlog : Real.log b < 0 := Real.log_neg hb0 hb1
  have hB1 : 1 < B := by
    have := abs_pos.mpr hlog.ne
    rw [hB]; linarith
  have hB0 : 0 < B := by linarith
  have hgrow : Tendsto (fun n : ℕ => B ^ n) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hB1
  filter_upwards [hgrow.eventually_ge_atTop (|q|)] with n hn
  show q ^ (n + 1) / afLog (((cdim (jn n).1 ^ 2 : ℕ) : ℝ)) b ≤ 1
  have hc : cdim (jn n).1 = 4 * (n + 1) := cdim_mono n
  have haf : afLog (((cdim (jn n).1 ^ 2 : ℕ) : ℝ)) b = B ^ ((4 * (n + 1)) ^ 2) := by
    rw [afLog, ← hB, hc, Real.rpow_natCast]
  rw [haf, div_le_one (pow_pos hB0 _)]
  have hX : |q| ≤ B ^ (n + 1) := hn.trans (pow_le_pow_right₀ hB1.le (Nat.le_succ n))
  calc q ^ (n + 1) ≤ |q| ^ (n + 1) := by
        rw [← abs_pow]; exact le_abs_self _
    _ ≤ (B ^ (n + 1)) ^ (n + 1) := pow_le_pow_left₀ (abs_nonneg q) hX _
    _ = B ^ ((n + 1) * (n + 1)) := by rw [← pow_mul]
    _ ≤ B ^ ((4 * (n + 1)) ^ 2) := pow_le_pow_right₀ hB1.le (by nlinarith)

variable {n : ℕ}

/-- **The `π`-flux defect persists at every member of `blFam` and every step**, at every smoothing scale.
DERIVED: `2` the least rank; `4` the defect; `12` the coupling bound. -/
theorem facV_blFam_fpi (hN : 2 ≤ n + 2) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / ((n + 2 : ℕ) : ℝ))) (m : ℕ) (s : ℝ) (k : ℕ) :
    facV ((blFam hN c hc0 hc m s).V k (dgConf (zeta fpi))) p1 = 4 := by
  rw [blFam_V_fpi hN hc0 hc m s k, facV_fpi]

/-- **The rough set of `blFam` is charged at every step**: `ν_k(cutF … ρ) > 0` for `ρ < 4`.
DERIVED: `0` the signs; `1` the cut-off's ceiling; `2` the least rank; `4` the defect; `12` the coupling
bound. -/
theorem stateK_cutF_blFam_pos (hN : 2 ≤ n + 2) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / ((n + 2 : ℕ) : ℝ))) (m : ℕ) (s : ℝ) (k : ℕ) {ρ : ℝ} (hρ : ρ < 4) :
    0 < stateK (NeZero.ne (n + 2)) k (cutF (blFam hN c hc0 hc m s) k ρ) := by
  obtain ⟨S, hS⟩ := (flowP (blFam hN c hc0 hc m s) k).2.1
  refine stateK_pos_of_local (NeZero.ne (n + 2)) k _ S (fun U V hUV => ?_)
    (fun U => le_min zero_le_one (le_max_left _ _)) (P := dgConf (zeta fpi)) ?_
  · show min 1 (max 0 ((flowP _ k).1 U - ρ)) = min 1 (max 0 ((flowP _ k).1 V - ρ))
    rw [hS U V hUV]
  · rw [cutF_apply, facV_blFam_fpi hN hc0 hc m s k]
    exact lt_min one_pos (lt_max_of_lt_right (by linarith))

/-- **`CoefBound` alone is no constraint**: the zero coefficients meet it. DERIVED: `0` the zero
coefficients and the zero bound. -/
theorem coefBound_zero : MultiScaleOS.CoefBound (0 : Ix0 → ℝ → (MIx →₀ ℝ)) :=
  ⟨fun _ => ∅, fun _ => 0, fun _ => 0, fun _ _ _ _ => ⟨by simp, fun _ => by simp⟩⟩

end Patterns

end MassGap.BlFamCore

end

/-! ### The copy over a coupling family -/

namespace MassGap.BlFamCore

set_option Elab.async false in
set_option maxHeartbeats 0 in
#along_generalize_more MassGap.ContinuumSchwinger.dyBeta from MassGap.BlFamCore.not_substrateCoreAt_of_roughTail

-- No copy mentions the source.
run_cmd do
  let env ← Lean.getEnv
  let src := ``MassGap.ContinuumSchwinger.dyBeta
  let pre := `MassGap.CouplingGen.Along
  for (c, ci) in env.constants.map₂.toList do
    if pre.isPrefixOf c then
      let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
      if used.contains src then
        throwError "copy {c} still mentions {src}"

end MassGap.BlFamCore

/-! ## 3. The residual and the root at `blFam` -/

noncomputable section

namespace MassGap.BlFamCore

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.ClayTreeG MassGap.ClayStatementG Filter
open scoped Topology
open MassGap.FlowAlong (cpl)
open MassGap.CouplingTower (StrongEnd CouplingTower UVConverges)
open MassGap.CompositesRen (OffMix)
open MassGap.ObserverBlock (blFam blFam_physRange)

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

variable (N) in
/-- **The core along `βs` at the ray-averaged observer**: `ObserverTower.CoreInputsAlongW N βs` at
`W = blFam … m s₀`, `0 ≤ s₀ ≤ r`, with the physical range discharged. DERIVED: `0` the signs; `12` the
coupling bound inherited from `blFam`; `π` in `π/N`. -/
def BlFamCoreAlong (βs : ℕ → ℝ) : Prop :=
  ∃ (c : ℝ) (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ) (s₀ r : ℝ) (_ : 0 ≤ s₀)
    (_ : s₀ ≤ r) (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : CompositesBuild.Ix0 → ℝ → (MultiScaleAll.MIx →₀ ℝ)),
    CouplingGen.Along.SU2Best.SubstrateCoreAt (cpl βs) (blFam (Fact.out : 2 ≤ N) c hc0 hc m s₀)
        (ZCanon.zFix N zri zwe) b Wf
      ∧ CouplingGen.Along.StrongExpand.ExpandStrong (cpl βs) Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ MultiScaleOS.CoefBound cf
      ∧ CouplingGen.Along.FlowCovN.FlowCovLim (cpl βs) Wf cf
      ∧ CouplingGen.Along.WardFromLattice.FlowWard (cpl βs) Wf cf
      ∧ CouplingGen.Along.NondegFromProxy.ProxyNondeg (cpl βs) Wf cf
      ∧ CouplingGen.Along.ProxyGenLimN.ProxyGenLimGerm (cpl βs)
          (blFam (Fact.out : 2 ≤ N) c hc0 hc m s₀) b Wf cf r
      ∧ ∃ ℓ : ℝ, 0 < ℓ
          ∧ CouplingGen.Along.NonGaussFromScale.ThreePointAtScale (cpl βs) (NeZero.ne N) ℓ

/-- **`BlFamCoreAlong ⇒ CoreInputsAlongW`**: the instance `W = blFam … m s₀` with
`ObserverBlock.blFam_physRange`. DERIVED: `2` the least rank. -/
theorem coreW_of_blFamCore {βs : ℕ → ℝ} (h : BlFamCoreAlong N βs) :
    ObserverTower.CoreInputsAlongW N βs := by
  obtain ⟨c, hc0, hc, m, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, F⟩ := h
  exact ⟨_, r, blFam_physRange (Fact.out : 2 ≤ N) hc0 hc m hs0 hr, zri, zwe, hri, hwe, μ, b, Wf, cf, F⟩

/-- **The root at `SU(N)` from the strong end, (UV) and the core at `blFam` along the towers near `0⁺`**
(`ObserverTower.clayStatementOf_of_coreObs`, `coreW_of_blFamCore`). DERIVED: `0` the limit `0⁺`. -/
theorem clayStatementOf_of_blFamCore (hS : StrongEnd N)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      ∃ μ : ℝ, UVConverges N βs id μ)
    (hF : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      BlFamCoreAlong N βs) :
    ClayStatementOf (MassGap.SUN.SU N) :=
  ObserverTower.clayStatementOf_of_coreObs hS hUV (hF.mono fun _ h βs hT => coreW_of_blFamCore (h βs hT))

/-- **A rough tail along `βs` at every member refutes the core at `blFam` along `βs`** (the copy of
`not_substrateCoreAt_of_roughTail` at `cpl βs`). DERIVED: `12` the coupling bound inherited from `blFam`;
`π` in `π/N`; `2` the least rank. -/
theorem not_blFamCoreAlong_of_roughTail {βs : ℕ → ℝ}
    (hR : ∀ (c : ℝ) (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ) (s₀ : ℝ),
      CouplingGen.Along.BlFamCore.RoughTail (cpl βs) (blFam (Fact.out : 2 ≤ N) c hc0 hc m s₀)) :
    ¬ BlFamCoreAlong N βs := by
  rintro ⟨c, hc0, hc, m, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, -⟩
  exact CouplingGen.Along.BlFamCore.not_substrateCoreAt_of_roughTail (cpl βs) (hR c hc0 hc m s₀) _ b Wf S

end MassGap.BlFamCore

end

#print axioms MassGap.BlFamCore.cutF_apply
#print axioms MassGap.BlFamCore.exp_mul_cut_le_of_scaleAt
#print axioms MassGap.BlFamCore.not_scaleControlAll_of_roughTail
#print axioms MassGap.BlFamCore.not_substrateCoreAt_of_roughTail
#print axioms MassGap.BlFamCore.cut_decay_of_scaleControlAll
#print axioms MassGap.BlFamCore.exists_gamma_tower_le_one
#print axioms MassGap.BlFamCore.facV_blFam_fpi
#print axioms MassGap.BlFamCore.stateK_cutF_blFam_pos
#print axioms MassGap.BlFamCore.coefBound_zero
#print axioms MassGap.CouplingGen.Along.BlFamCore.not_substrateCoreAt_of_roughTail
#print axioms MassGap.BlFamCore.coreW_of_blFamCore
#print axioms MassGap.BlFamCore.clayStatementOf_of_blFamCore
#print axioms MassGap.BlFamCore.not_blFamCoreAlong_of_roughTail
