import Mathlib
import MassGap.StrongLocalFiniteSize

/-!
# MassGap.FlowScalingOnly — the block observer's step, its reach, and the comparison read on `[2^{-16}, β]`

`FlowComp.flowEnergyComp_of_split` gives the bare–flowed comparison `FlowEnergyComp hN W κ C K (η₁ + η₂)` from
a strong part at a fixed coupling `x₀` and a scaling part `∫_{x₀}^β (bareDelta − K flowDelta) ≤ η₂`.
`StrongLocalFiniteSize.strongPart_of_reach` proves the strong part at `x₀ = 2^{-16}` from a reach hypothesis on
the flow at its step. This module fixes the flow to the ray-averaged multigrid family
`ObserverBlock.blFam … m s`, fixes the step to the one matching the running spacing, proves the reach
hypothesis there, so the strong part tends to `0` and the comparison is its scaling part: the scaling part at
budget `η₂` gives `FlowEnergyComp` at every budget above `η₂`, and `FlowEnergyComp` at budget `η` gives the
scaling part at every budget above `η` (`FlowScalingEquiv.scaling_of_flowEnergyComp_lt`, by the two-sided bounds
`StrongFiniteSize.abs_defectW_strong_le` and `StrongLocalFiniteSize.abs_flowDefect_le_tail`). The scaling part is
the comparison restated on `[2^{-16}, β]`; the equivalence is `FlowScalingEquiv.flowEnergyComp_blFam_iff_scaling`.

## 1. The observer's step (defined, proved)

* `obsStep N β`: the least `k` with `dySpacing N (k + 1) < aRun N β` (and `0` when there is none). The
  repository leaves `κ` a free parameter of `ObsRunSeedFlowW` and `FlowEnergyComp`; `obsStep` is the step
  whose dyadic spacing matches the running lattice spacing at `β`.
* **`obsStep_spec`**: at `β > 0` with `aRun N β ≤ dySpacing N 0`,
  `aRun N β ≤ dySpacing N (obsStep N β) < 2 · aRun N β`: the finest dyadic step at or above the running
  spacing, within a factor `2`. `eventually_obsStep`: this holds eventually in `β`
  (`WeakCouplingWindow.eventually_aRun_le`).

## 2. The reach hypothesis at `blFam` (proved)

* **`reach_blFam`**: for `0 ≤ s`, `0 < C` and `4 s < θ C`, eventually in `β`, every side `n` in the window has
  `2 ((blFam … m s).range (obsStep N β) + 1) ≤ θ n`. From `spacing_mul_mgRange_le`
  (`dySpacing N k · range ≤ s`), `aRun N β ≤ dySpacing N (obsStep N β)`, the window's lower edge
  `C/2 < n · aRun N β`, and `aRun N β ≤ (θ C − 4 s)/4` eventually: `2 a (range + 1) ≤ 2 s + 2 a ≤ θ C / 2 < θ n a`.

## 3. The comparison and its scaling part (proved one way here; the converse is `FlowScalingEquiv`)

With `x₀ = 2^{-16}`, `0 ≤ s`, `0 < C` and `4 s < C` (the existence of a `θ < 1` with `4 s < θ C` is exactly
`4 s < C`; the proof takes `θ = (4 s + C)/(2 C)`):

* **`flowEnergyComp_blFam_of_scaling`**: the scaling part with budget `η₂` gives
  `FlowEnergyComp hN (blFam … m s) (obsStep N) C K (η + η₂)` for every `η > 0` and every `K`.
* **`flowEnergyComp_blFam_of_scaling_lt`**: the same gives `FlowEnergyComp … K η'` for every `η' > η₂`.
* **`runSeed_blFam_of_scaling`**: with `0 ≤ K`, `K δ + η₂ < 1/1000` and the flowed seed
  `ObsRunSeedFlowW hN (blFam … m s) (obsStep N) C δ`, the scaling part gives `WDeltaRun.RunSeed N`
  (`ObserverFlowSeed.runSeed_of_flowSeed`).
* `scaling_eq`: the scaling part's integral is
  `(defectW N β n − K F(β)) − (defectW N x₀ n − K F(x₀))`, `F = flowDefect hN W k n`: the bare-minus-flowed
  defect accumulated on `[x₀, β]`.

## 4. Non-vacuity (proved)

* `eventually_exists_inWin`: at `C > 0` the window holds a side eventually in `β`, so neither the reach
  hypothesis nor `FlowEnergyComp` is met by an empty window.
* **`eventually_blFam_moves_obsStep`**: for `c > 0`, `m ≥ 1`, `s > 0`, eventually in `β` the flow
  `(blFam … m s).V (obsStep N β)` moves a configuration: at the observer's step the flow is not the identity
  (`ObserverBlock.blFam_moves`, since `2 m · dySpacing N (obsStep N β) < 4 m · aRun N β ≤ s` eventually).
  So the comparison obtained here is not the degenerate case `FlowComp.flowEnergyComp_blFam_coarse`.
* **`nonvacuous_blFam`**: at `N = 2`, `c = 1/24`, `m = 1`, `s = 1`, `C = 8`, `θ = 3/4`: `4 s < θ C < C`, the
  window is eventually nonempty, the reach hypothesis holds, and the flow moves at the observer's step.

## Growing-quantity test (argued, not declarations)

Every constant here is fixed before `β`: `s`, `C`, `θ`, `m`, `K`, `η`, `η₂`. The growing quantities are the
window side `n ∈ (C/(2a), C/a]`, `a = aRun N β → 0`, the flow's lattice range at the step,
`range ≤ s / dySpacing N (obsStep N β) ≤ s / a`, and the coupling range `[x₀, β]`. The reach hypothesis
compares `range` with `θ n`: both grow like `1/a`, with ratio at most `2 s / C`, so it is a condition on the
fixed ratio `s / C`, not a fixed constant against a growing quantity. The strong part holds for every fixed
`η > 0` because its bound tends to `0` in `n` at fixed `θ < 1`. The scaling part is where a constant fixed
before `β` (`η₂`) meets quantities that grow with `β` (the side `n` and the range `[x₀, β]`); this is the same
test `FlowEnergyComp` itself faces, since the two differ by a term tending to `0`. It is assumed here, not
proved.

## What is assumed, and what remains

Assumed: the scaling part at `x₀ = 2^{-16}`, which is `FlowEnergyComp` at `blFam` and `obsStep` up to an
arbitrarily small change of budget:

  `∀ᶠ β in atTop, ∀ n, InWin N C β n →
     ∫_{2^{-16}}^β (bareDelta hN n x − K · flowDelta hN (blFam … m s) (obsStep N β) n x) ≤ η₂`.

By `scaling_eq` it asserts that the bare defect accumulated on `[2^{-16}, β]` at the window side exceeds `K`
times the flowed defect accumulated there by at most `η₂`. It is not trivially true: at `K = 0` it is the bare
seed's weak-coupling part `defectW N β n − defectW N 2^{-16} n ≤ η₂`. It is not known to be false. For
`runSeed_blFam_of_scaling` the flowed seed `ObsRunSeedFlowW` at `blFam` and `obsStep` is a second input, open; the two read at one side
are `ObserverOneInput.blockSeedScaling_iff`, and the merges formalized in `ObserverOneInput` do not reduce the pair.

Proved: the step, the reach hypothesis, the strong part at `blFam`, and that the scaling part at budget `η₂`
gives `FlowEnergyComp` at every `η' > η₂`, at `0 ≤ s`, `0 < C`, `4 s < C`. The converse (`FlowEnergyComp` at
`η` gives the scaling part at every budget above `η`) is `FlowScalingEquiv.scaling_of_flowEnergyComp_lt`, and
the equivalence is `FlowScalingEquiv.flowEnergyComp_blFam_iff_scaling`.

DERIVED (module-wide): `65536 = 2^{16}` the strong-coupling threshold of `StrongLocalFiniteSize`; `2` the
halving per dyadic step, the window's lower edge `C/2` and the least side; `4 = 2 · 2` the window's lower
edge times the factor `2` in `2 (range + 1)`; `1` the successor in `range + 1` and the least level;
`0` the default step and the lower ends; `1/1000` the sharp seed.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.FlowScalingOnly

open Filter Set
open MassGap.ObserverFlowSeed (bareDelta flowDelta InWin FlowEnergyComp ObsRunSeedFlowW runSeed_of_flowSeed)
open MassGap.FlowComp (flowDefect flowEnergyComp_of_split integral_excess continuous_excess)
open MassGap.ContinuumSchwinger (dySpacing dySpacing_pos dySpacing_mul_pow tendsto_dySpacing)
open MassGap.ObserverMultigrid (mgLevels mgRange spacing_mul_mgRange_le)
open MassGap.ObserverBlock (blFam blFam_moves)
open MassGap.AsymptoticScaling (aRun aRun_pos)
open MassGap.WeakCouplingWindow (eventually_aRun_le)
open MassGap.StrongLocalFiniteSize (strongPart_of_reach)

variable {N : ℕ}

/-! ## 1. The observer's step -/

open Classical in
/-- **The observer's step at coupling `β`**: the least `k` with `dySpacing N (k + 1) < aRun N β`, and `0` when
there is none. DERIVED: `1` the next step; `0` the default. -/
def obsStep (N : ℕ) (β : ℝ) : ℕ :=
  if h : ∃ k : ℕ, dySpacing N (k + 1) < aRun N β then Nat.find h else 0

/-- One dyadic step halves the spacing. DERIVED: `2` the halving; `1` the step. -/
theorem dySpacing_succ_mul_two (N k : ℕ) : dySpacing N (k + 1) * 2 = dySpacing N k := by
  simpa using dySpacing_mul_pow N (Nat.le_add_right k 1)

open Classical in
/-- **The observer's step matches the running spacing within a factor `2`**: at `β > 0` with
`aRun N β ≤ dySpacing N 0`, `aRun N β ≤ dySpacing N (obsStep N β) < 2 · aRun N β`.
DERIVED: `2` the halving; `0` the coarsest step; `1` the least colour count and the next step. -/
theorem obsStep_spec (hN : 1 ≤ N) {β : ℝ} (hβ : 0 < β) (ha : aRun N β ≤ dySpacing N 0) :
    aRun N β ≤ dySpacing N (obsStep N β) ∧ dySpacing N (obsStep N β) < 2 * aRun N β := by
  have hpos := aRun_pos hN hβ
  have hex : ∃ k : ℕ, dySpacing N (k + 1) < aRun N β := by
    obtain ⟨K, hK⟩ := eventually_atTop.mp ((tendsto_dySpacing N).eventually (gt_mem_nhds hpos))
    exact ⟨K, hK (K + 1) (by omega)⟩
  unfold obsStep
  rw [dif_pos hex]
  have hspec : dySpacing N (Nat.find hex + 1) < aRun N β := Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex, ¬ dySpacing N (j + 1) < aRun N β := fun j hj => Nat.find_min hex hj
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
    · rw [h0]; exact ha
    · have h1 := hmin (Nat.find hex - 1) (by omega)
      rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at h1
      exact not_lt.mp h1
  · have h2 := dySpacing_succ_mul_two N (Nat.find hex)
    linarith

/-- **Eventually in `β` the observer's step matches the running spacing within a factor `2`.**
DERIVED: `2` the halving; `0` the coarsest step and the lower coupling. -/
theorem eventually_obsStep (hN : 1 ≤ N) :
    ∀ᶠ β in atTop,
      aRun N β ≤ dySpacing N (obsStep N β) ∧ dySpacing N (obsStep N β) < 2 * aRun N β := by
  filter_upwards [eventually_aRun_le (N := N) hN (dySpacing_pos hN 0), eventually_gt_atTop (0 : ℝ)]
    with β ha hβ
  exact obsStep_spec hN hβ ha

/-! ## 2. The reach hypothesis at `blFam` -/

/-- **The reach hypothesis of `strongPart_of_reach` at `blFam` and the observer's step**: for `0 ≤ s`,
`0 < C` and `4 s < θ C`, eventually in `β`, every window side `n` has
`2 ((blFam … m s).range (obsStep N β) + 1) ≤ θ n`. DERIVED: `4 = 2 · 2` the window's lower edge `C/2` times
the factor `2` of the reach condition; `1` the successor; `0` the lower ends; `12` as in
`ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem reach_blFam (hN2 : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ)
    {s C θ : ℝ} (hs0 : 0 ≤ s) (hC : 0 < C) (hθ : 4 * s < θ * C) :
    ∀ᶠ β in atTop, ∀ n : ℕ, InWin N C β n →
      2 * (((blFam hN2 c hc0 hc m s).range (obsStep N β) : ℕ) + 1 : ℝ) ≤ θ * n := by
  have hN1 : 1 ≤ N := by omega
  have hθ0 : 0 < θ := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  filter_upwards [eventually_obsStep hN1,
    eventually_aRun_le (N := N) hN1 (by linarith : (0 : ℝ) < (θ * C - 4 * s) / 4),
    eventually_gt_atTop (0 : ℝ)] with β ⟨h1, _⟩ h2 hβ n hw
  have ha := aRun_pos hN1 hβ
  have hR := spacing_mul_mgRange_le (m := m) hN1 hs0 (obsStep N β)
  change 2 * (((mgRange m (mgLevels N m s (obsStep N β)) : ℕ) : ℝ) + 1) ≤ θ * n
  have hR0 : (0 : ℝ) ≤ ((mgRange m (mgLevels N m s (obsStep N β)) : ℕ) : ℝ) := Nat.cast_nonneg _
  have haR : aRun N β * ((mgRange m (mgLevels N m s (obsStep N β)) : ℕ) : ℝ) ≤ s :=
    (mul_le_mul_of_nonneg_right h1 hR0).trans hR
  have hwin := mul_lt_mul_of_pos_left hw.2.2.1 hθ0
  have key : 2 * (((mgRange m (mgLevels N m s (obsStep N β)) : ℕ) : ℝ) + 1) * aRun N β
      < θ * n * aRun N β := by
    linarith
  exact (lt_of_mul_lt_mul_right key ha.le).le

/-! ## 3. The comparison and its scaling part -/

/-- **The scaling part is the bare-minus-flowed defect accumulated on `[x₀, β]`.** DERIVED: `0` the lower
coupling and the excluded side. -/
theorem scaling_eq (hN : N ≠ 0) (W : MassGap.ContinuumFlow.ConfFlow N) (k : ℕ) {n : ℕ} (hn : n ≠ 0)
    (K x₀ β : ℝ) :
    ∫ x in x₀..β, (bareDelta hN n x - K * flowDelta hN W k n x)
      = (MassGap.ZoomSelfScale.defectW N β n - K * flowDefect hN W k n β)
        - (MassGap.ZoomSelfScale.defectW N x₀ n - K * flowDefect hN W k n x₀) := by
  have h := continuous_excess hN W k n K
  rw [← integral_excess hN W k hn K β, ← integral_excess hN W k hn K x₀]
  exact (intervalIntegral.integral_interval_sub_left (h.intervalIntegrable 0 β)
    (h.intervalIntegrable 0 x₀)).symm

/-- **The block observer's comparison from its scaling part.** At `0 ≤ s`, `0 < C`, `4 s < C`, for every `K`
and `η > 0`, the scaling part at `x₀ = 2^{-16}` with budget `η₂` gives
`FlowEnergyComp hN (blFam … m s) (obsStep N) C K (η + η₂)`. The strong part is
`strongPart_of_reach` at `θ = (4 s + C)/(2 C) < 1`, with the reach hypothesis `reach_blFam`.
DERIVED: `65536 = 2^{16}` the strong-coupling threshold; `4`, `2`, `12` as in `reach_blFam`. -/
theorem flowEnergyComp_blFam_of_scaling (hN2 : 2 ≤ N) (hN : N ≠ 0) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ) {s C K η η₂ : ℝ} (hs0 : 0 ≤ s) (hC : 0 < C)
    (hsC : 4 * s < C) (hη : 0 < η)
    (hl : ∀ᶠ β in atTop, ∀ n : ℕ, InWin N C β n →
      ∫ x in (1 / 65536 : ℝ)..β,
        (bareDelta hN n x - K * flowDelta hN (blFam hN2 c hc0 hc m s) (obsStep N β) n x) ≤ η₂) :
    FlowEnergyComp hN (blFam hN2 c hc0 hc m s) (obsStep N) C K (η + η₂) := by
  have hθ1 : (4 * s + C) / (2 * C) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hθ : 4 * s < (4 * s + C) / (2 * C) * C := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_right hsC hC]
  exact flowEnergyComp_of_split hN _ (obsStep N) (1 / 65536)
    (strongPart_of_reach hN _ (obsStep N) hC hθ1 hη (reach_blFam hN2 hc0 hc m hs0 hC hθ)) hl

/-- **Every budget above the scaling budget**: under the hypotheses of `flowEnergyComp_blFam_of_scaling`,
`FlowEnergyComp … K η'` for every `η' > η₂`. DERIVED: no numeral beyond those of the scaling part, `12`, `65536`, `4` as in
`flowEnergyComp_blFam_of_scaling`. -/
theorem flowEnergyComp_blFam_of_scaling_lt (hN2 : 2 ≤ N) (hN : N ≠ 0) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ) {s C K η₂ η' : ℝ} (hs0 : 0 ≤ s) (hC : 0 < C)
    (hsC : 4 * s < C) (hη' : η₂ < η')
    (hl : ∀ᶠ β in atTop, ∀ n : ℕ, InWin N C β n →
      ∫ x in (1 / 65536 : ℝ)..β,
        (bareDelta hN n x - K * flowDelta hN (blFam hN2 c hc0 hc m s) (obsStep N β) n x) ≤ η₂) :
    FlowEnergyComp hN (blFam hN2 c hc0 hc m s) (obsStep N) C K η' := by
  have h := flowEnergyComp_blFam_of_scaling hN2 hN hc0 hc m (η := η' - η₂) hs0 hC hsC (by linarith) hl
  rwa [sub_add_cancel] at h

/-- **The run seed from two open inputs: the block observer's flowed seed `ObsRunSeedFlowW` and the scaling
part** (equivalently `FlowEnergyComp`, up to budget: `FlowScalingEquiv.flowEnergyComp_blFam_iff_scaling`). At `0 ≤ s`, `0 < C`,
`4 s < C`, `0 ≤ K` and `K δ + η₂ < 1/1000`. DERIVED: `1/1000` the sharp seed; `12`, `65536`, `4` as in
`flowEnergyComp_blFam_of_scaling`. -/
theorem runSeed_blFam_of_scaling (hN2 : 2 ≤ N) (hN : N ≠ 0) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ) {s C K δ η₂ : ℝ} (hs0 : 0 ≤ s) (hC : 0 < C)
    (hsC : 4 * s < C) (hK : 0 ≤ K) (hsum : K * δ + η₂ < 1 / 1000)
    (hS : ObsRunSeedFlowW hN (blFam hN2 c hc0 hc m s) (obsStep N) C δ)
    (hl : ∀ᶠ β in atTop, ∀ n : ℕ, InWin N C β n →
      ∫ x in (1 / 65536 : ℝ)..β,
        (bareDelta hN n x - K * flowDelta hN (blFam hN2 c hc0 hc m s) (obsStep N β) n x) ≤ η₂) :
    MassGap.WDeltaRun.RunSeed N :=
  runSeed_of_flowSeed hN hC hK (η := 1 / 1000 - K * δ) (by linarith) hS
    (flowEnergyComp_blFam_of_scaling_lt hN2 hN hc0 hc m hs0 hC hsC (by linarith) hl)

/-! ## 4. Non-vacuity -/

/-- **The window holds a side eventually** (`C > 0`): `n = 2^{⌊log₂ ⌊C/a⌋⌋}`. DERIVED: `4` the least
`⌊C/a⌋` giving a side `≥ 2`; `2` the base, the least side and the window's ratio; `1` the successor. -/
theorem eventually_exists_inWin (hN : 1 ≤ N) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ β in atTop, ∃ n : ℕ, InWin N C β n := by
  filter_upwards [eventually_aRun_le (N := N) hN (by positivity : (0 : ℝ) < C / 4),
    eventually_gt_atTop (0 : ℝ)] with β ha hβ
  have hpos := aRun_pos hN hβ
  have hx4 : (4 : ℝ) ≤ C / aRun N β := by
    rw [le_div_iff₀ hpos]
    linarith
  have hF4 : 4 ≤ ⌊C / aRun N β⌋₊ := Nat.le_floor (by exact_mod_cast hx4)
  have hb1 : 1 ≤ Nat.log 2 ⌊C / aRun N β⌋₊ := Nat.le_log_of_pow_le one_lt_two (by omega)
  have hnF : 2 ^ Nat.log 2 ⌊C / aRun N β⌋₊ ≤ ⌊C / aRun N β⌋₊ := Nat.pow_log_le_self 2 (by omega)
  have hFn : ⌊C / aRun N β⌋₊ < 2 ^ Nat.log 2 ⌊C / aRun N β⌋₊ * 2 := by
    simpa [pow_succ] using Nat.lt_pow_succ_log_self one_lt_two ⌊C / aRun N β⌋₊
  refine ⟨2 ^ Nat.log 2 ⌊C / aRun N β⌋₊, ⟨_, rfl⟩, ?_, ?_, ?_⟩
  · calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ Nat.log 2 ⌊C / aRun N β⌋₊ := Nat.pow_le_pow_right (by norm_num) hb1
  · have h1 : ((⌊C / aRun N β⌋₊ : ℕ) : ℝ) + 1 ≤ 2 * ((2 ^ Nat.log 2 ⌊C / aRun N β⌋₊ : ℕ) : ℝ) := by
      have : ⌊C / aRun N β⌋₊ + 1 ≤ 2 * 2 ^ Nat.log 2 ⌊C / aRun N β⌋₊ := by omega
      exact_mod_cast this
    have h2 : C / aRun N β < ((⌊C / aRun N β⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : C < (((⌊C / aRun N β⌋₊ : ℕ) : ℝ) + 1) * aRun N β := by rwa [div_lt_iff₀ hpos] at h2
    have h4 := mul_le_mul_of_nonneg_right h1 hpos.le
    linarith
  · have h1 : ((2 ^ Nat.log 2 ⌊C / aRun N β⌋₊ : ℕ) : ℝ) ≤ C / aRun N β :=
      (Nat.cast_le.mpr hnF).trans (Nat.floor_le (by positivity))
    rwa [le_div_iff₀ hpos] at h1

/-- **At the observer's step the flow moves a configuration**, eventually in `β` (`c > 0`, `m ≥ 1`, `s > 0`):
`2 m · dySpacing N (obsStep N β) < 4 m · aRun N β ≤ s`, so at least one level, and `blFam_moves`.
DERIVED: `2` the stride ratio and the factor of `obsStep_spec`; `4 = 2 · 2`; `1` the least level; `12` as
in `ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem eventually_blFam_moves_obsStep (hN2 : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c) (hcpos : 0 < c)
    (hc : 12 * c < Real.sin (Real.pi / N)) {m : ℕ} (hm : 1 ≤ m) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ β in atTop, ∃ U, (blFam hN2 c hc0 hc m s).V (obsStep N β) U ≠ U := by
  have hN1 : 1 ≤ N := by omega
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  filter_upwards [eventually_obsStep hN1,
    eventually_aRun_le (N := N) hN1 (by positivity : (0 : ℝ) < s / (4 * m))] with β ⟨_, h2⟩ ha
  have hd := dySpacing_pos hN1 (obsStep N β)
  have hlev : 1 ≤ mgLevels N m s (obsStep N β) := by
    have h2' : (2 : ℝ) ≤ s / (m * dySpacing N (obsStep N β)) := by
      rw [le_div_iff₀ (mul_pos hm' hd)]
      rw [le_div_iff₀ (by positivity)] at ha
      nlinarith [mul_lt_mul_of_pos_left h2 hm']
    have h3 : 2 ≤ ⌊s / ((m : ℝ) * dySpacing N (obsStep N β))⌋₊ := Nat.le_floor (by exact_mod_cast h2')
    exact Nat.le_log_of_pow_le one_lt_two (by simpa using h3)
  exact blFam_moves hN2 hc0 hcpos hc hm hlev

/-- `12 · (1/24) < sin (π/2)`. DERIVED: `12` the staple bound; `24 = 2 · 12`; `2` the rank. -/
theorem hc_two : 12 * (1 / 24 : ℝ) < Real.sin (Real.pi / ((2 : ℕ) : ℝ)) := by
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num, Real.sin_pi_div_two]
  norm_num

/-- **Non-vacuity at `N = 2`, `c = 1/24`, `m = 1`, `s = 1`, `C = 8`, `θ = 3/4`**: `4 s < θ C < C`; the window
is eventually nonempty; the reach hypothesis holds at the observer's step; and there the flow moves a
configuration. DERIVED: `8 > 4 · 1 / (3/4)`; `3/4 < 1`; the remaining numerals as in the lemmas used; `1/24` the
coupling of `hc_two`, `24 = 2 · 12`. -/
theorem nonvacuous_blFam :
    4 * (1 : ℝ) < 3 / 4 * 8 ∧ (3 / 4 : ℝ) < 1 ∧ 4 * (1 : ℝ) < 8 ∧
    (∀ᶠ β in atTop, ∃ n : ℕ, InWin 2 8 β n) ∧
    (∀ᶠ β in atTop, ∀ n : ℕ, InWin 2 8 β n →
      2 * (((blFam le_rfl (1 / 24) (by norm_num) hc_two 1 1).range (obsStep 2 β) : ℕ) + 1 : ℝ)
        ≤ 3 / 4 * n) ∧
    (∀ᶠ β in atTop, ∃ U, (blFam le_rfl (1 / 24) (by norm_num) hc_two 1 1).V (obsStep 2 β) U ≠ U) :=
  ⟨by norm_num, by norm_num, by norm_num,
    eventually_exists_inWin (by norm_num) (by norm_num),
    reach_blFam le_rfl (by norm_num) hc_two 1 (by norm_num) (by norm_num) (by norm_num),
    eventually_blFam_moves_obsStep le_rfl (by norm_num) (by norm_num) hc_two le_rfl (by norm_num)⟩

end MassGap.FlowScalingOnly

end

#print axioms MassGap.FlowScalingOnly.dySpacing_succ_mul_two
#print axioms MassGap.FlowScalingOnly.obsStep_spec
#print axioms MassGap.FlowScalingOnly.eventually_obsStep
#print axioms MassGap.FlowScalingOnly.reach_blFam
#print axioms MassGap.FlowScalingOnly.scaling_eq
#print axioms MassGap.FlowScalingOnly.flowEnergyComp_blFam_of_scaling
#print axioms MassGap.FlowScalingOnly.flowEnergyComp_blFam_of_scaling_lt
#print axioms MassGap.FlowScalingOnly.runSeed_blFam_of_scaling
#print axioms MassGap.FlowScalingOnly.eventually_exists_inWin
#print axioms MassGap.FlowScalingOnly.eventually_blFam_moves_obsStep
#print axioms MassGap.FlowScalingOnly.hc_two
#print axioms MassGap.FlowScalingOnly.nonvacuous_blFam
