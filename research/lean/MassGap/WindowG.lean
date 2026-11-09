import Mathlib
import MassGap.TorusDecayG
import MassGap.WeakCouplingWindow
import MassGap.DoublingClay2
import MassGap.ClayTreeG
import MassGap.WDeltaRun

/-!
# MassGap.WindowG — the run seed of `G` gives the weak-coupling gap at the periodic state of `G`

`WeakCouplingWindow`, `DoublingClay2` and `WDeltaRun` with `SUN.SU N` replaced by a `GaugeGroup G` with
`GaugeSimple G`, the spacing `AsymptoticScaling.aRun N` by `GaugeRunning.aRunG G` and the seed
`ZoomSelfScale.defectW` by `TorusDoubling.defectWG G 4 (wilsonDensityG G)`.

* `eventually_aRunG_le`, `continuous_aRunG`, `tendsto_dyBetaG`: the running spacing of `G` is eventually
  below every positive bound, it is continuous, and the coupling of step `k` runs to infinity.
* `FixedWindowDecayG G τ p L`: one factor `q ∈ (0, 1)` such that at every large `β` some even lag
  `2h ≥ 2` of physical length `2h · aRunG G β ≤ L` has, for every gauge-invariant half-space
  observable and every slack, `torusConnG … (2h) ≤ q · torusConnG … 0 + ε` along `periodicUltraG G β`.
* `gapAt_physical_of_fixedWindowDecayG`: from it, some `c > 0` has, at every large `β`, a rate
  `0 < r` with `TransferGap.GapAt (periodicGaugeInvDataG G τ p β) r` and `c/L ≤ −log r / aRunG G β`.
  The lag is even, so `PeriodicReduceG.gapAt_of_torusLagClearG` applies without positivity of the
  transfer operator.
* `nPG`, `WDelta2G`, `fixedWindowDecayG_of_WDelta2G`: the seed at the power-of-two side
  `nPG = 2^{⌈log₂⌈2ℓ₀/aRunG⌉⌉}` gives `FixedWindowDecayG G 0 0 (5ℓ₀)` (`TorusDecayG.dyadic_torus_decayG`).
* `RunSeedG G`: some `C > 0` such that, eventually in `β`, a power of two `n ≥ 2` with
  `n · aRunG G β ≤ C` has `defectWG G 4 (wilsonDensityG G) β n ≤ 1/1000`.
  `wDelta2G_of_runSeedG`: it gives `WDelta2G G ℓ₀` at every `ℓ₀` with `C ≤ 2ℓ₀`;
  `fixedWindowDecayG_of_runSeedG`: hence `FixedWindowDecayG G 0 0 L` at some `L > 0`.
* `runSeedG_SU`: at `SU(N)`, `N ≥ 2`, `RunSeedG` is `WDeltaRun.RunSeed N`.

DERIVED (module-wide): `4` the dimension; `0` the plane and the slicing direction; `2` the even lag,
the doubling and the `2ℓ₀` of `nPG`; `5` the window factor of `DoublingClay2.nP_bounds`
(`nP · a ≤ 4ℓ₀ + 2a` at `a ≤ ℓ₀/2`); `1/2` the gap factor of `dyadic_torus_decayG`; `1/1000` the sharp
seed; `1` the reference coupling of `dyBetaG` and the least rank of `AsymptoticScaling.aRun 1`.
-/

namespace MassGap.WindowG

open Filter MassGap MassGap.ClayTreeG MassGap.PeriodicReduceG MassGap.GaugeGroup
  MassGap.WeakCouplingWindow

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  [GaugeSimple G]

/-! ## 1. The running spacing of `G` -/

section Running

theorem continuous_aRunG : Continuous (GaugeRunning.aRunG G) := by
  have h : GaugeRunning.aRunG G = fun β => AsymptoticScaling.aRun 1 (lamG G * β) :=
    funext (aRunG_eq G)
  rw [h]
  exact (AsymptoticScaling.continuous_aRun 1).comp (continuous_const.mul continuous_id)

/-- **The running spacing of `G` is eventually below any positive bound.** -/
theorem eventually_aRunG_le {b : ℝ} (hb : 0 < b) :
    ∀ᶠ β in atTop, GaugeRunning.aRunG G β ≤ b := by
  have h := eventually_aRun_le (N := 1) le_rfl hb
  have ht : Tendsto (fun β => lamG G * β) atTop atTop :=
    tendsto_id.const_mul_atTop (lamG_pos G)
  filter_upwards [ht.eventually h] with β hβ
  rw [aRunG_eq]
  exact hβ

/-- **The coupling of step `k` runs to infinity.** The running spacing has a positive minimum on
every interval `[1, B]`, which `dySpacingG G k` eventually undercuts. -/
theorem tendsto_dyBetaG : Tendsto (dyBetaG G) atTop atTop := by
  refine Filter.tendsto_atTop.mpr (fun B => ?_)
  obtain ⟨x, hx, hmin⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := max B 1)).exists_isMinOn
    ⟨1, le_refl 1, le_max_right B 1⟩ (continuous_aRunG G).continuousOn
  have hm : 0 < GaugeRunning.aRunG G x := aRunG_pos G (lt_of_lt_of_le one_pos hx.1)
  have hev : ∀ᶠ k in atTop, dySpacingG G k < GaugeRunning.aRunG G x :=
    (tendsto_dySpacingG G).eventually (gt_mem_nhds hm)
  filter_upwards [hev] with k hk
  by_contra hlt
  rw [not_le] at hlt
  have hmem : dyBetaG G k ∈ Set.Icc (1 : ℝ) (max B 1) :=
    ⟨one_le_dyBetaG G k, hlt.le.trans (le_max_left B 1)⟩
  have h1 := isMinOn_iff.mp hmin _ hmem
  rw [aRunG_dyBetaG] at h1
  linarith

end Running

/-! ## 2. The input at a fixed window, and the gap from it -/

section Window

/-- **Decay by a fixed factor across a fixed physical window, at an even lag, at every large
coupling**, for the periodic Wilson state of `G`. See the module docstring. -/
def FixedWindowDecayG (τ : Fin 4) (p : ℤ) (L : ℝ) : Prop :=
  ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ᶠ β in atTop, ∃ h : ℕ, h ≠ 0 ∧
    ((2 * h : ℕ) : ℝ) * GaugeRunning.aRunG G β ≤ L ∧
    ∀ x ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ p, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in ((periodicUltraG G β : Ultrafilter ℕ) : Filter ℕ),
        torusConnG G τ p β j x (2 * h) ≤ q * torusConnG G τ p β j x 0 + ε

/-- **The weak-coupling gap of `G` from the input.** The proof takes `c = −log q` and at each large
`β` the rate `r = q^{1/(2h)}`. -/
theorem gapAt_physical_of_fixedWindowDecayG (τ : Fin 4) (p : ℤ) {L : ℝ} (hL : 0 < L)
    (h : FixedWindowDecayG G τ p L) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ β in atTop, ∃ r : ℝ, 0 < r ∧
      TransferGap.GapAt (periodicGaugeInvDataG G τ p β) r
        ∧ c / L ≤ -Real.log r / GaugeRunning.aRunG G β := by
  obtain ⟨q, hq0, hq1, hev⟩ := h
  refine ⟨-Real.log q, neg_pos.mpr (Real.log_neg hq0 hq1), ?_⟩
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with β hβ hβ0
  obtain ⟨h, hh, hwin, hlag⟩ := hβ
  have hm : 2 * h ≠ 0 := by omega
  have ha : 0 < GaugeRunning.aRunG G β := aRunG_pos G hβ0
  have hr0 : 0 < stepRate q (2 * h) := stepRate_pos hq0 (2 * h)
  have hlc : TorusLagClearG G τ p β (2 * h) (stepRate q (2 * h)) := by
    intro x hx ε hε
    rw [stepRate_pow hq0.le hm]
    exact hlag x hx ε hε
  exact ⟨stepRate q (2 * h), hr0, gapAt_of_torusLagClearG τ p β hh hr0.le hlc,
    physical_rate_ge hq0 hq1 hm ha hL hwin⟩

end Window

/-! ## 3. The seed at the power-of-two side -/

section Seed

/-- The power-of-two side: the least power of two at least `2ℓ₀/aRunG G β`. -/
noncomputable def nPG (ℓ₀ β : ℝ) : ℕ :=
  2 ^ Nat.clog 2 ⌈2 * ℓ₀ / GaugeRunning.aRunG G β⌉₊

/-- **The seed at the power-of-two side, eventually in `β` (named hypothesis).**
DERIVED: `1/1000` the sharp seed threshold of `DoublingSharp.rec_sharp`; `4` the dimension. -/
def WDelta2G (ℓ₀ : ℝ) : Prop :=
  ∀ᶠ β in atTop, TorusDoubling.defectWG G 4 (wilsonDensityG G) β (nPG G ℓ₀ β) ≤ 1 / 1000

/-- **The seed at the power-of-two side gives `FixedWindowDecayG`** at window `5ℓ₀`, factor `½`,
lag `nPG`. -/
theorem fixedWindowDecayG_of_WDelta2G {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) (hW : WDelta2G G ℓ₀) :
    FixedWindowDecayG G 0 0 (5 * ℓ₀) := by
  refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
  filter_upwards [hW, eventually_gt_atTop (0 : ℝ),
    eventually_aRunG_le G (b := ℓ₀ / 2) (by positivity)] with β hβW hβ0 haLe
  set a := GaugeRunning.aRunG G β
  have ha : 0 < a := aRunG_pos G hβ0
  obtain ⟨h2, hna⟩ := DoublingClay2.nP_bounds hℓ ha haLe
  set c := Nat.clog 2 ⌈2 * ℓ₀ / a⌉₊ with hc
  have hnP : nPG G ℓ₀ β = 2 ^ c := rfl
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at h2
    omega
  have e : 2 * 2 ^ (c - 1) = nPG G ℓ₀ β := by
    rw [hnP, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hc0)]
  refine ⟨2 ^ (c - 1), pow_ne_zero _ two_ne_zero, ?_, fun x hx ε hε => ?_⟩
  · rw [e, hnP]
    linarith
  · rw [e]
    exact TorusDecayG.dyadic_torus_decayG β hβ0.le (nPG G ℓ₀ β) ⟨c, rfl⟩ h2 hβW x hx ε hε

/-- **The run seed of `G`.** There is `C > 0` such that, eventually in `β`, some power of two
`n ≥ 2` with `n · aRunG G β ≤ C` has `defectWG G 4 (wilsonDensityG G) β n ≤ 1/1000`.
DERIVED: `1/1000` the sharp seed threshold of `DoublingSharp.rec_sharp`; `2` the least even side; `4` the
dimension. -/
def RunSeedG : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ β in atTop, ∃ n : ℕ, PeriodicState.IsPow2 n ∧ 2 ≤ n ∧
    (n : ℝ) * GaugeRunning.aRunG G β ≤ C ∧
    TorusDoubling.defectWG G 4 (wilsonDensityG G) β n ≤ 1 / 1000

/-- **`WDelta2G` from a seed at a power of two below `C / aRunG`**, for every `ℓ₀` with `C ≤ 2ℓ₀`.
The power of two `nPG G ℓ₀ β` is at least `2ℓ₀/a ≥ C/a ≥ n`, so it is `2ᵏ n`, and
`DoublingWilsonG.defectWG_pow_le` carries the seed there. -/
theorem wDelta2G_of_seed_le {C : ℝ}
    (hev : ∀ᶠ β in atTop, ∃ n : ℕ, PeriodicState.IsPow2 n ∧ 2 ≤ n ∧
      (n : ℝ) * GaugeRunning.aRunG G β ≤ C ∧
      TorusDoubling.defectWG G 4 (wilsonDensityG G) β n ≤ 1 / 1000)
    {ℓ₀ : ℝ} (hℓ : C ≤ 2 * ℓ₀) : WDelta2G G ℓ₀ := by
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with β ⟨n, ⟨b, hb⟩, hn2, hna, hd⟩ hβ
  have ha : 0 < GaugeRunning.aRunG G β := aRunG_pos G hβ
  have h1 : (n : ℝ) ≤ 2 * ℓ₀ / GaugeRunning.aRunG G β := by
    rw [le_div_iff₀ ha]; linarith
  have h2 : (n : ℝ) ≤ (⌈2 * ℓ₀ / GaugeRunning.aRunG G β⌉₊ : ℝ) := h1.trans (Nat.le_ceil _)
  have h3 : n ≤ ⌈2 * ℓ₀ / GaugeRunning.aRunG G β⌉₊ := by exact_mod_cast h2
  have h4 : n ≤ nPG G ℓ₀ β := h3.trans (Nat.le_pow_clog (by norm_num) _)
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [hb] at hn2
    norm_num at hn2
  have he : Even n := by rw [hb]; exact Nat.even_pow.mpr ⟨even_two, hb0⟩
  set c := Nat.clog 2 ⌈2 * ℓ₀ / GaugeRunning.aRunG G β⌉₊ with hc
  have hnP : nPG G ℓ₀ β = 2 ^ c := rfl
  rw [hnP, hb] at h4
  have hbc : b ≤ c := (Nat.pow_le_pow_iff_right (by norm_num)).mp h4
  have hk := DoublingWilsonG.defectWG_pow_le hβ.le hn2 he hd (c - b)
  have e : 2 ^ (c - b) * n = nPG G ℓ₀ β := by
    rw [hnP, hb, ← pow_add, Nat.sub_add_cancel hbc]
  rw [e] at hk
  exact hk

/-- **`WDelta2G` at every large `ℓ₀` from the run seed.** -/
theorem wDelta2G_of_runSeedG (h : RunSeedG G) :
    ∃ C : ℝ, 0 < C ∧ ∀ ℓ₀ : ℝ, C ≤ 2 * ℓ₀ → WDelta2G G ℓ₀ := by
  obtain ⟨C, hC, hev⟩ := h
  exact ⟨C, hC, fun ℓ₀ hℓ => wDelta2G_of_seed_le G hev hℓ⟩

/-- **The run seed of `G` gives `FixedWindowDecayG` at a positive window.** -/
theorem fixedWindowDecayG_of_runSeedG (h : RunSeedG G) :
    ∃ L : ℝ, 0 < L ∧ FixedWindowDecayG G 0 0 L := by
  obtain ⟨C, hC, hW⟩ := wDelta2G_of_runSeedG G h
  exact ⟨5 * C, by positivity, fixedWindowDecayG_of_WDelta2G G hC (hW C (by linarith))⟩

end Seed

/-! ## 4. At `SU(N)` the run seed of `G` is the tree's run seed -/

section SU

/-- **At `SU(N)`, `N ≥ 2`, `RunSeedG` is `WDeltaRun.RunSeed N`**: `GaugeRunning.aRunG_SU`,
`GaugeInstances.wilsonDensityG_SU` and `TorusDoubling.defectWG_four_eq`. -/
theorem runSeedG_SU (N : ℕ) [NeZero N] [Fact (2 ≤ N)] :
    RunSeedG (SUN.SU N) ↔ WDeltaRun.RunSeed N := by
  have h : ∀ (β : ℝ) (n : ℕ),
      TorusDoubling.defectWG (SUN.SU N) 4 (wilsonDensityG (SUN.SU N)) β n
        = ZoomSelfScale.defectW N β n :=
    fun β n => TorusDoubling.defectWG_four_eq N β n
  unfold RunSeedG WDeltaRun.RunSeed
  simp only [GaugeRunning.aRunG_SU, h]

end SU

end MassGap.WindowG

#print axioms MassGap.WindowG.tendsto_dyBetaG
#print axioms MassGap.WindowG.gapAt_physical_of_fixedWindowDecayG
#print axioms MassGap.WindowG.fixedWindowDecayG_of_WDelta2G
#print axioms MassGap.WindowG.wDelta2G_of_runSeedG
#print axioms MassGap.WindowG.fixedWindowDecayG_of_runSeedG
#print axioms MassGap.WindowG.runSeedG_SU
