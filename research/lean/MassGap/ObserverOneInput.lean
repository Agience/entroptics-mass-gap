import Mathlib
import MassGap.FlowScalingEquiv
import MassGap.ObserverRegime

/-!
# MassGap.ObserverOneInput — whether the observer's gap clause rests on one input

The gap clause has three observer forms: the bare energy-reading seed `ObserverRunSeed.ObsRunSeedW`
(equivalent to `WDeltaRun.RunSeed`, `ObserverRunSeed.obsRunSeedW_iff`); the flowed pair, the flowed seed
`ObserverFlowSeed.ObsRunSeedFlowW` with the comparison `ObserverFlowSeed.FlowEnergyComp`
(`ObserverFlowSeed.runSeed_of_flowSeed`; at the block flow `ObserverBlock.blFam … m s` and the step
`FlowScalingOnly.obsStep` the comparison at every budget above `η` is its scaling part at every budget above `η`, `FlowScalingEquiv.flowEnergyComp_blFam_iff_scaling`);
and the coarse regime `ObserverRegime.ObsRegimeW`. This module asks whether one observer-side input can replace
the flowed pair, and what the coarse regime implies among the three. The two merges formalized here (the
conjunction at one side and the summed budget) are the pair and `RunSeed`; that every merge is one of these is
argued. Deriving the seed from the comparison is, at the identity flow, as hard as `RunSeed`; no single flowed
input that reduces the pair is found. The pair
remains, read as two inequalities at one side. Declarations are in the namespace `MassGap.ObserverOneInput`.

## 1. The merge at one side is the pair (proved)

`FlowComp.inWin_unique`: at `β > 0` the window `InWin N C β` holds at most one side. So the comparison's
"every side in the window" is the one side the flowed seed uses.

* `FlowSeedComp hN W κ C K δ η`: eventually in `β`, some side `n` in the window has the flowed budget `δ` and
  the comparison budget `η` at that same side.
* **`flowSeedComp_iff`** (`1 ≤ N`): `FlowSeedComp hN W κ C K δ η ↔ ObsRunSeedFlowW hN W κ C δ ∧
  FlowEnergyComp hN W κ C K η`, for every flow, step, `C`, `K`, `δ`, `η`. The merge is the conjunction.
* `runSeed_of_flowSeedComp`: `0 < C`, `0 ≤ K`, `K δ + η ≤ 1/1000` and `FlowSeedComp` give `RunSeed N`.
* `flowSeedComp_iff_defect`: `FlowSeedComp` is, eventually at one side in the window,
  `flowDefect ≤ δ` and `defectW − K · flowDefect ≤ η`: two inequalities between the bare defect `D` and the
  flowed defect `F` at one side.
* `flowSeedComp_identity_iff`: at the identity flow, `K = 1`, `η = 0`, it is the flowed seed alone, which is
  the bare seed on the window at budget `δ` (the degenerate case).

## 2. One budget is the bare seed (proved)

A flowed seed whose budget already contains the comparison is a budget for the sum
`K · flowDelta + (bareDelta − K · flowDelta)`, which is `bareDelta`.

* `WinSeed N`: `RunSeed N` with the window's lower edge `C/2` added.
* **`runSeed_iff_winSeed`**: `RunSeed N ↔ WinSeed N` at `N ≠ 0`. A seed side `n` with `n a ≤ C` is carried to
  `2^k n` in `(C/2, C]` by `WDeltaRun.defectW_pow_le`.
* `OneBudgetFlow hN W κ K`: some `C > 0` with, eventually, a side in the window whose summed change
  `K · flowDelta + (bareDelta − K · flowDelta)` has the sharp budget `1/1000`.
* **`oneBudgetFlow_iff_runSeed`**: `OneBudgetFlow hN W κ K ↔ RunSeed N` for every flow `W`, step `κ` and `K`.
  The summed budget cancels the flowed term identically (`ring`), so `W`, `κ` and `K` drop out: it is the run
  seed restated.

In the two-number picture of §1 the pair is the set `{F ≤ δ, D − K F ≤ η}`; its projection to `D` is
`D ≤ K δ + η` (`K ≥ 0`), the bare seed. Every condition that gives `RunSeed` through `D`
implies `D ≤ 1/1000` at a window side; the question is whether some single condition is easier to establish than
the pair. No such condition is found; this is argued, not a declaration, and is not a theorem about all
conditions. The two formalized merges are `flowSeedComp_iff` and `oneBudgetFlow_iff_runSeed`.

## 3. The two halves are separate (reductions proved; independence argued)

* **`runSeed_of_flowEnergyComp_zero`**: at `K = 0` the comparison alone, with `η ≤ 1/1000` and `0 < C`, gives
  `RunSeed N`. The comparison at `K = 0` is the bare seed; its content as a second input is `K > 0`.
* **`runSeed_of_comp_imp_seed`**: at the identity flow the comparison holds with `K = 1`, `η = 0`
  (`ObserverFlowSeed.flowEnergyComp_identity`); so any proof that the comparison implies the flowed seed at
  budget `δ ≤ 1/1000` there is a proof of `RunSeed N`. Deriving the seed from the comparison is, at the identity
  flow, as hard as `RunSeed` itself.
* That the flowed seed does not carry the comparison at a moving flow is argued: the seed bounds `F` alone,
  and the bare plaquette is not a function of the flowed field (`ObserverFlowSeed`, analysis). No degenerate
  `ConfFlow` makes the flowed seed free: a constant map is not gauge covariant (the trivial configuration is
  not fixed by a non-constant gauge transformation), so this half has no proved separation here.

## 4. The block flow: the two inputs at one side (proved)

At `blFam … m s`, `obsStep N`, `x₀ = 2^{-16}`, `0 ≤ s`, `0 < C`, `4 s < C`:

* `BlockSeedScaling hN2 c hc0 hc m s C K δ η₂`: eventually in `β`, one side `n` in the window has
  `flowDefect hN (blFam … m s) (obsStep N β) n β ≤ δ` and the scaling part
  `∫_{2^{-16}}^β (bareDelta − K flowDelta) ≤ η₂`.
* **`runSeed_of_blockSeedScaling`**: `0 ≤ K`, `K δ + η₂ < 1/1000` and `BlockSeedScaling` give `RunSeed N`.
  The strong part is `StrongLocalFiniteSize.strongPart_of_reach` with `FlowScalingOnly.reach_blFam`.
* **`blockSeedScaling_iff`**: `BlockSeedScaling … ↔ ObsRunSeedFlowW hN (blFam … m s) (obsStep N) C δ ∧
  (scaling part at every side in the window)`: the hypotheses of `FlowScalingOnly.runSeed_blFam_of_scaling`,
  read at the one side.

## 5. The coarse regime implies none of the three (proved for `RunSeed` at the constant reading; the rest argued)

`ObsRegimeW hN W R C Q dist θ α` is stated for any `ConfFlow` `W` and any block reading `R`, not at `blFam`
or `obsStep`; its step index `k` runs over the flow's steps under `stateK hN k`. The comparison theorem enters
as the hypothesis `DobCompareW1` inside it (eventually in `k`); the identification of `C` with the coarse
field's W1 interdependence matrix is argued in `ObserverRegime`, not formalized. Its proved consequence is
`ObserverRegime.obsRegimeW_cov`: separated coarse covariances decay geometrically in block distance, uniformly in the step, on one finite
block set with constants that may depend on it. On one block set every bounded reading meets the predicate
(`ObserverBlockReading.obsRegimeW_of_bounded`), so it is clustering of the coarse readings in `stateK` only in
the uniform form `ObserverBlockReading.ObsRegimeUnif`.

* `stateCov_const_left`: a constant reading has covariance `0` with every reading.
* **`obsRegimeW_const`**: at every `N ≠ 0` and every flow `W`, `ObsRegimeW` holds for the constant reading
  (`ι = Unit`, `Y = ℝ`, `R = 0`, `C = 0`, `Q = 0`, `dist = 0`, `θ = 1`, `α = 0`).
* **`runSeed_of_obsRegimeW_const_imp`**: so a proof that `ObsRegimeW` (with `R` free) implies `RunSeed N`
  is a proof of `RunSeed N`. The predicate does not pin the reading; `ObserverBlockReading` pins it to the block energy of the flowed
configuration and proves that pinning alone leaves it vacuous on a fixed block set
(`obsRegimeW_blockRead_vacuous`). A membership statement of this form cannot witness non-triviality.

Argued: even with `R` the gauge classes of the flowed blocks, `ObsRegimeW` gives covariance decay in the
states `stateK`, not a bound on `defectW N β n = 16 log Z(n) − log Z(2n)`, the torus free-energy defect that
`RunSeed`, `ObsRunSeedFlowW` and `FlowEnergyComp` all read. No module derives a torus free-energy bound from
infinite-volume coarse clustering; `ObserverRegime` §3 routes the coarse regime to the gap through
`FlowCapstone.FlowClusterAbs` (in form, the reader step not built), not through `RunSeed`. So `ObsRegimeW`
implies none of `RunSeed`, `ObsRunSeedFlowW`, `FlowEnergyComp` by any proved route.

## Tests (argued, not declarations)

* Restatement against discharge: `flowSeedComp_iff` and `blockSeedScaling_iff` are the pair at one side,
  and `oneBudgetFlow_iff_runSeed` is `RunSeed`. None discharges an input.
* Growing quantity: `K`, `δ`, `η`, `η₂`, `C`, `s` are fixed before `β`; the side `n ∈ (C/(2a), C/a]` grows.
  The one-side forms face exactly the test the pair faces (`FlowScalingOnly`, growing-quantity test): the
  merges move no constant past a growing quantity.
* Free theory: the Gaussian test of `ObserverFlowSeed` (the comparison meets its budget only at `K = 0`, since
  the excess `K c_n/x` is not integrable at `x → 0`) applies unchanged to the one-side forms, which contain the
  comparison at the witness side; at `K = 0` they are the bare seed (`runSeed_of_flowEnergyComp_zero`).
* Degenerate case: at the identity flow the merge is the flowed seed alone (`flowSeedComp_identity_iff`); at
  the constant coarse reading `ObsRegimeW` holds outright (`obsRegimeW_const`).

## What remains

Two inputs at one side of the window, at `blFam … m s`, `obsStep N`: the flowed seed `F(β) ≤ δ` and the
scaling part `(D − K F)(β) − (D − K F)(2^{-16}) ≤ η₂`, with `0 ≤ K`, `K δ + η₂ < 1/1000`. This module replaces
no existing input; it proves that the merges considered are the pair or `RunSeed`, and that the comparison
does not carry the seed.

DERIVED (module-wide): `1/1000` the sharp seed; `65536 = 2^{16}` the strong-coupling threshold of
`StrongLocalFiniteSize`; `2` the window's lower edge, the doubling and the least side; `4`, `2` as in
`FlowScalingOnly.reach_blFam`; `0`, `1` the degenerate constants of the coarse reading and the unit flow
constant.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ObserverOneInput

open Filter Set
open MassGap.ZoomSelfScale (defectW)
open MassGap.ObserverFlowSeed (bareDelta flowDelta InWin Budget FlowEnergyComp ObsRunSeedFlowW
  runSeed_of_flowSeed flowEnergyComp_identity)
open MassGap.FlowComp (flowDefect flowEnergyComp_iff_defect obsRunSeedFlowW_iff_defect inWin_unique
  integral_le_of_budget budget_of_integral integral_bareDelta continuous_bareDelta continuous_flowDelta
  continuous_excess integral_excess)
open MassGap.ContinuumFlow (ConfFlow)
open MassGap.ObserverBlock (blFam)
open MassGap.FlowScalingOnly (obsStep reach_blFam scaling_eq eventually_exists_inWin)
open MassGap.StrongLocalFiniteSize (strongPart_of_reach)
open MassGap.AsymptoticScaling (aRun aRun_pos)

variable {N : ℕ}

/-! ## 1. The merge at one side -/

/-- **The flowed seed and the comparison at one side**: eventually in `β`, some side in the window has the
flowed budget `δ` and the comparison budget `η`. DERIVED: no numeral. -/
def FlowSeedComp (hN : N ≠ 0) (W : ConfFlow N) (κ : ℝ → ℕ) (C K δ η : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∃ n : ℕ, InWin N C β n ∧ Budget β δ (flowDelta hN W (κ β) n) ∧
    Budget β η (fun x => bareDelta hN n x - K * flowDelta hN W (κ β) n x)

/-- **The merge at one side is the pair** (`1 ≤ N`): the window holds one side at `β > 0`.
DERIVED: `0` the lower coupling. -/
theorem flowSeedComp_iff (hN1 : 1 ≤ N) (hN : N ≠ 0) (W : ConfFlow N) (κ : ℝ → ℕ) (C K δ η : ℝ) :
    FlowSeedComp hN W κ C K δ η ↔ ObsRunSeedFlowW hN W κ C δ ∧ FlowEnergyComp hN W κ C K η := by
  constructor
  · intro h
    refine ⟨h.mono fun β ⟨n, hw, hb, _⟩ => ⟨n, hw, hb⟩, ?_⟩
    filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with β ⟨n, hw, _, hc⟩ hβ m hm
    rw [← inWin_unique hN1 hβ hw hm]
    exact hc
  · rintro ⟨hS, hc⟩
    filter_upwards [hS, hc] with β ⟨n, hw, hb⟩ hcb
    exact ⟨n, hw, hb, hcb n hw⟩

/-- **The run seed from the merge at one side.** DERIVED: `1/1000` the sharp seed. -/
theorem runSeed_of_flowSeedComp (hN1 : 1 ≤ N) (hN : N ≠ 0) {W : ConfFlow N} {κ : ℝ → ℕ} {C K δ η : ℝ}
    (hC : 0 < C) (hK : 0 ≤ K) (hsum : K * δ + η ≤ 1 / 1000) (h : FlowSeedComp hN W κ C K δ η) :
    WDeltaRun.RunSeed N := by
  obtain ⟨hS, hc⟩ := (flowSeedComp_iff hN1 hN W κ C K δ η).mp h
  exact runSeed_of_flowSeed hN hC hK hsum hS hc

/-- **The merge at one side in defect form**: eventually one side in the window has `F ≤ δ` and
`D − K F ≤ η`, `D = defectW N β n`, `F = flowDefect hN W (κ β) n β`. DERIVED: `0` the lower coupling;
`2` the least side. -/
theorem flowSeedComp_iff_defect (hN : N ≠ 0) (W : ConfFlow N) (κ : ℝ → ℕ) (C K δ η : ℝ) :
    FlowSeedComp hN W κ C K δ η ↔
      ∀ᶠ β in atTop, ∃ n : ℕ, InWin N C β n ∧ flowDefect hN W (κ β) n β ≤ δ ∧
        defectW N β n - K * flowDefect hN W (κ β) n β ≤ η := by
  constructor
  · intro h
    filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β ⟨n, hw, hb, hc⟩ hβ
    have hn : n ≠ 0 := by have := hw.2.1; omega
    refine ⟨n, hw, integral_le_of_budget hβ (continuous_flowDelta hN W (κ β) n) hb, ?_⟩
    have hI := integral_le_of_budget hβ (continuous_excess hN W (κ β) n K) hc
    rwa [integral_excess hN W (κ β) hn K β] at hI
  · intro h
    refine h.mono fun β ⟨n, hw, hb, hc⟩ => ⟨n, hw,
      budget_of_integral (continuous_flowDelta hN W (κ β) n) hb,
      budget_of_integral (continuous_excess hN W (κ β) n K) ?_⟩
    rw [integral_excess hN W (κ β) (by have := hw.2.1; omega) K β]
    exact hc

/-- **The degenerate case**: at the identity flow, `K = 1`, `η = 0`, the merge is the flowed seed alone.
DERIVED: `1` the unit constant; `0` the slack. -/
theorem flowSeedComp_identity_iff (hN1 : 1 ≤ N) (hN : N ≠ 0) (κ : ℝ → ℕ) (C δ : ℝ) :
    FlowSeedComp hN (ConfFlow.identity N) κ C 1 δ 0 ↔ ObsRunSeedFlowW hN (ConfFlow.identity N) κ C δ := by
  rw [flowSeedComp_iff hN1 hN]
  exact ⟨fun h => h.1, fun h => ⟨h, flowEnergyComp_identity hN κ C⟩⟩

/-! ## 2. One budget is the bare seed -/

/-- **The run seed on the window**: `RunSeed N` with the lower edge `C/2`. DERIVED: `1/1000` the sharp
seed. -/
def WinSeed (N : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ β in atTop, ∃ n : ℕ, InWin N C β n ∧ defectW N β n ≤ 1 / 1000

/-- **The run seed is the run seed on the window.** A side `n` with `n a ≤ C` is carried to `2^k n` in
`(C/2, C]`, `k = ⌊log₂ ⌊C/(n a)⌋⌋`, by `WDeltaRun.defectW_pow_le`. DERIVED: `2` the base, the least side
and the lower edge; `1` the successor and the least floor; `0` the lower coupling. -/
theorem runSeed_iff_winSeed (hN : N ≠ 0) : WDeltaRun.RunSeed N ↔ WinSeed N := by
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  constructor
  · rintro ⟨C, hC, hev⟩
    refine ⟨C, hC, ?_⟩
    filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with β ⟨n, ⟨b, hb⟩, hn2, hna, hd⟩ hβ
    have ha := aRun_pos hN1 hβ
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hna0 : 0 < (n : ℝ) * aRun N β := mul_pos hnpos ha
    set x := C / ((n : ℝ) * aRun N β) with hx
    have hx1 : (1 : ℝ) ≤ x := by rw [hx, le_div_iff₀ hna0]; linarith
    have hF1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx1)
    set k := Nat.log 2 ⌊x⌋₊ with hk
    have hle : 2 ^ k ≤ ⌊x⌋₊ := Nat.pow_log_le_self 2 (by omega)
    have hlt : ⌊x⌋₊ < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self one_lt_two _
    have hle' : ((2 ^ k : ℕ) : ℝ) ≤ x := (Nat.cast_le.mpr hle).trans (Nat.floor_le (by linarith))
    have hlt' : x < ((2 ^ (k + 1) : ℕ) : ℝ) := by
      have h1 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      have h2 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := Nat.cast_le.mpr hlt
      push_cast at h2 ⊢
      linarith
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hb
      omega
    have heven : Even n := by rw [hb]; exact (Nat.even_pow.mpr ⟨even_two, hb0⟩)
    refine ⟨2 ^ k * n, ⟨⟨k + b, by rw [hb, pow_add]⟩, ?_, ?_, ?_⟩,
      WDeltaRun.defectW_pow_le hN hβ.le hn2 heven hd k⟩
    · have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      nlinarith
    · have h3 : C < ((2 ^ (k + 1) : ℕ) : ℝ) * ((n : ℝ) * aRun N β) := by
        rwa [hx, div_lt_iff₀ hna0] at hlt'
      push_cast at h3 ⊢
      rw [pow_succ] at h3
      nlinarith
    · have h3 : ((2 ^ k : ℕ) : ℝ) * ((n : ℝ) * aRun N β) ≤ C := by
        rwa [hx, le_div_iff₀ hna0] at hle'
      push_cast at h3 ⊢
      nlinarith
  · rintro ⟨C, hC, hev⟩
    exact ⟨C, hC, hev.mono fun β ⟨n, hw, hd⟩ => ⟨n, hw.1, hw.2.1, hw.2.2.2, hd⟩⟩

/-- **The flowed seed with the comparison in its budget**: some `C > 0` with, eventually, a side in the window
whose summed change `K · flowDelta + (bareDelta − K · flowDelta)` has the sharp budget. DERIVED: `1/1000` the
sharp seed. -/
def OneBudgetFlow (hN : N ≠ 0) (W : ConfFlow N) (κ : ℝ → ℕ) (K : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ β in atTop, ∃ n : ℕ, InWin N C β n ∧
    Budget β (1 / 1000) (fun x => K * flowDelta hN W (κ β) n x
      + (bareDelta hN n x - K * flowDelta hN W (κ β) n x))

/-- **One budget is the run seed**, for every flow, step and `K`. DERIVED: `1/1000` the sharp seed; `0` the
lower coupling; `2` the least side. -/
theorem oneBudgetFlow_iff_runSeed (hN : N ≠ 0) (W : ConfFlow N) (κ : ℝ → ℕ) (K : ℝ) :
    OneBudgetFlow hN W κ K ↔ WDeltaRun.RunSeed N := by
  have hsum : ∀ β n, (fun x => K * flowDelta hN W (κ β) n x
      + (bareDelta hN n x - K * flowDelta hN W (κ β) n x)) = bareDelta hN n := by
    intro β n
    funext x
    ring
  rw [runSeed_iff_winSeed hN]
  constructor
  · rintro ⟨C, hC, hev⟩
    refine ⟨C, hC, ?_⟩
    filter_upwards [hev, eventually_ge_atTop (0 : ℝ)] with β ⟨n, hw, hb⟩ hβ
    rw [hsum] at hb
    have hI := integral_le_of_budget hβ (continuous_bareDelta hN n) hb
    rw [integral_bareDelta hN (by have := hw.2.1; omega)] at hI
    exact ⟨n, hw, hI⟩
  · rintro ⟨C, hC, hev⟩
    refine ⟨C, hC, hev.mono fun β ⟨n, hw, hd⟩ => ⟨n, hw, ?_⟩⟩
    rw [hsum]
    refine budget_of_integral (continuous_bareDelta hN n) ?_
    rw [integral_bareDelta hN (by have := hw.2.1; omega)]
    exact hd

/-! ## 3. The two halves are separate -/

/-- **At `K = 0` the comparison alone is the run seed.** DERIVED: `0` the constant; `1/1000` the sharp
seed. -/
theorem runSeed_of_flowEnergyComp_zero (hN : N ≠ 0) {W : ConfFlow N} {κ : ℝ → ℕ} {C η : ℝ} (hC : 0 < C)
    (hη : η ≤ 1 / 1000) (h : FlowEnergyComp hN W κ C 0 η) : WDeltaRun.RunSeed N := by
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  refine ⟨C, hC, ?_⟩
  filter_upwards [(flowEnergyComp_iff_defect hN W κ C 0 η).mp h, eventually_exists_inWin hN1 hC]
    with β hb ⟨n, hw⟩
  have h1 := hb n hw
  rw [zero_mul, sub_zero] at h1
  exact ⟨n, hw.1, hw.2.1, hw.2.2.2, h1.trans hη⟩

/-- **Deriving the flowed seed from the comparison is as hard as the run seed**: at the identity flow the comparison holds with `K = 1`,
`η = 0`, so an implication from it to the flowed seed at budget `δ ≤ 1/1000` gives `RunSeed N`.
DERIVED: `1` the unit constant; `0` the slack; `1/1000` the sharp seed. -/
theorem runSeed_of_comp_imp_seed (hN : N ≠ 0) {κ : ℝ → ℕ} {C δ : ℝ} (hC : 0 < C) (hδ : δ ≤ 1 / 1000)
    (himp : FlowEnergyComp hN (ConfFlow.identity N) κ C 1 0 →
      ObsRunSeedFlowW hN (ConfFlow.identity N) κ C δ) : WDeltaRun.RunSeed N :=
  runSeed_of_flowSeed hN hC zero_le_one (by linarith) (himp (flowEnergyComp_identity hN κ C))
    (flowEnergyComp_identity hN κ C)

/-! ## 4. The block flow: the two inputs at one side -/

/-- **The block observer's two inputs at one side**: eventually in `β`, one side in the window has the flowed
defect within `δ` and the scaling part on `[2^{-16}, β]` within `η₂`. DERIVED: `65536 = 2^{16}` the
strong-coupling threshold; `12` as in `ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
def BlockSeedScaling (hN2 : 2 ≤ N) (hN : N ≠ 0) (c : ℝ) (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N))
    (m : ℕ) (s C K δ η₂ : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∃ n : ℕ, InWin N C β n ∧
    flowDefect hN (blFam hN2 c hc0 hc m s) (obsStep N β) n β ≤ δ ∧
    ∫ x in (1 / 65536 : ℝ)..β,
      (bareDelta hN n x - K * flowDelta hN (blFam hN2 c hc0 hc m s) (obsStep N β) n x) ≤ η₂

/-- **The run seed from the block observer's two inputs at one side.** The strong part on `[0, 2^{-16}]` is
`strongPart_of_reach` at `θ = (4 s + C)/(2 C)` with `reach_blFam`. DERIVED: `1/1000` the sharp seed;
`65536 = 2^{16}`; `4`, `2`, `12` as in `reach_blFam`. -/
theorem runSeed_of_blockSeedScaling (hN2 : 2 ≤ N) (hN : N ≠ 0) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ) {s C K δ η₂ : ℝ} (hs0 : 0 ≤ s) (hC : 0 < C)
    (hsC : 4 * s < C) (hK : 0 ≤ K) (hsum : K * δ + η₂ < 1 / 1000)
    (h : BlockSeedScaling hN2 hN c hc0 hc m s C K δ η₂) : WDeltaRun.RunSeed N := by
  have hθ1 : (4 * s + C) / (2 * C) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hθ : 4 * s < (4 * s + C) / (2 * C) * C := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_right hsC hC]
  have hstr := strongPart_of_reach (K := K) hN (blFam hN2 c hc0 hc m s) (obsStep N) hC hθ1
    (η := 1 / 1000 - K * δ - η₂) (by linarith) (reach_blFam hN2 hc0 hc m hs0 hC hθ)
  refine ⟨C, hC, ?_⟩
  filter_upwards [h, hstr] with β ⟨n, hw, hF, hl⟩ hs
  have hn : n ≠ 0 := by have := hw.2.1; omega
  rw [scaling_eq hN _ _ hn K] at hl
  have h1 := hs n hw
  have hKF : K * flowDefect hN (blFam hN2 c hc0 hc m s) (obsStep N β) n β ≤ K * δ :=
    mul_le_mul_of_nonneg_left hF hK
  exact ⟨n, hw.1, hw.2.1, hw.2.2.2, by linarith⟩

/-- **The block observer's two inputs at one side are the hypotheses of
`FlowScalingOnly.runSeed_blFam_of_scaling`** (the flowed seed, and the scaling part at every side in the
window). DERIVED: `0` the lower coupling; `65536 = 2^{16}`; `12` as in
`ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem blockSeedScaling_iff (hN2 : 2 ≤ N) (hN : N ≠ 0) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ) (s C K δ η₂ : ℝ) :
    BlockSeedScaling hN2 hN c hc0 hc m s C K δ η₂ ↔
      ObsRunSeedFlowW hN (blFam hN2 c hc0 hc m s) (obsStep N) C δ ∧
        ∀ᶠ β in atTop, ∀ n : ℕ, InWin N C β n →
          ∫ x in (1 / 65536 : ℝ)..β,
            (bareDelta hN n x - K * flowDelta hN (blFam hN2 c hc0 hc m s) (obsStep N β) n x) ≤ η₂ := by
  have hN1 : 1 ≤ N := by omega
  rw [obsRunSeedFlowW_iff_defect]
  constructor
  · intro h
    refine ⟨h.mono fun β ⟨n, hw, hF, _⟩ => ⟨n, hw, hF⟩, ?_⟩
    filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with β ⟨n, hw, _, hl⟩ hβ n' hw'
    rw [← inWin_unique hN1 hβ hw hw']
    exact hl
  · rintro ⟨hS, hl⟩
    filter_upwards [hS, hl] with β ⟨n, hw, hF⟩ hlb
    exact ⟨n, hw, hF, hlb n hw⟩

/-! ## 5. The coarse regime at the constant reading -/

/-- **A constant reading has covariance `0`** with every reading. DERIVED: `0` the covariance. -/
theorem stateCov_const_left {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (ν : MassGap.DLRLimit.State X) {F : C(X, ℝ)} {c : ℝ} (hF : ∀ x, F x = c) (H : C(X, ℝ)) :
    MassGap.FocusZoom.stateCov ν F H = 0 := by
  have h1 : F = c • (1 : C(X, ℝ)) := ContinuousMap.ext fun x => by simp [hF x]
  have h2 : F * H = c • H := ContinuousMap.ext fun x => by simp [hF x]
  unfold MassGap.FocusZoom.stateCov
  rw [h2, h1, ν.map_smul, ν.map_smul, ν.map_one]
  ring

/-- **The coarse regime holds at the constant reading**, at every `N ≠ 0` and every flow: one block, block
datum `ℝ`, reading `0`, `C = 0`, `Q = 0`, `dist = 0`, `θ = 1`, `α = 0`. DERIVED: `0`, `1` the degenerate
constants. -/
theorem obsRegimeW_const (hN : N ≠ 0) (W : ConfFlow N) :
    MassGap.ObserverRegime.ObsRegimeW (ι := Unit) (Y := fun _ => ℝ) hN W (fun _ _ _ => (0 : ℝ))
      (0 : Matrix Unit Unit ℝ) 0 (fun _ _ => 0) 1 0 := by
  refine ⟨le_rfl, zero_lt_one, zero_lt_one, le_rfl, le_rfl, fun _ => rfl,
    fun _ _ _ => Nat.zero_le _, ⟨fun _ _ => le_rfl, fun _ => by simp⟩, Eventually.of_forall ?_⟩
  intro k f h F H hF _ Lf Lh _ _ _ _
  rw [stateCov_const_left _ (c := f fun _ => 0) hF H, abs_zero, zero_mul]

/-- **The coarse regime with a free reading does not carry the run seed**: an implication from it to
`RunSeed N` at the constant reading is a proof of `RunSeed N`. DERIVED: `0`, `1` the degenerate constants. -/
theorem runSeed_of_obsRegimeW_const_imp (hN : N ≠ 0) (W : ConfFlow N)
    (himp : MassGap.ObserverRegime.ObsRegimeW (ι := Unit) (Y := fun _ => ℝ) hN W (fun _ _ _ => (0 : ℝ))
      (0 : Matrix Unit Unit ℝ) 0 (fun _ _ => 0) 1 0 → WDeltaRun.RunSeed N) :
    WDeltaRun.RunSeed N :=
  himp (obsRegimeW_const hN W)

end MassGap.ObserverOneInput

end

#print axioms MassGap.ObserverOneInput.flowSeedComp_iff
#print axioms MassGap.ObserverOneInput.runSeed_of_flowSeedComp
#print axioms MassGap.ObserverOneInput.flowSeedComp_iff_defect
#print axioms MassGap.ObserverOneInput.flowSeedComp_identity_iff
#print axioms MassGap.ObserverOneInput.runSeed_iff_winSeed
#print axioms MassGap.ObserverOneInput.oneBudgetFlow_iff_runSeed
#print axioms MassGap.ObserverOneInput.runSeed_of_flowEnergyComp_zero
#print axioms MassGap.ObserverOneInput.runSeed_of_comp_imp_seed
#print axioms MassGap.ObserverOneInput.runSeed_of_blockSeedScaling
#print axioms MassGap.ObserverOneInput.blockSeedScaling_iff
#print axioms MassGap.ObserverOneInput.stateCov_const_left
#print axioms MassGap.ObserverOneInput.obsRegimeW_const
#print axioms MassGap.ObserverOneInput.runSeed_of_obsRegimeW_const_imp
