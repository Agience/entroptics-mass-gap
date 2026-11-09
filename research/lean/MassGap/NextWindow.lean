import Mathlib
import MassGap.TransferBand
import MassGap.DoublingSharp

/-!
# MassGap.NextWindow — the next-window reading along a coupling tower: its ceiling, and what a floor needs

`TransferBand.windowUpper_of_overlap` reduces the upper half of (M) along a coupling tower at `u₀`
(`CouplingTower N u₀ βs id`, so `D(βs k, k) = u₀` eventually, `D = windowCoupling N`) to three inputs: a
next-window floor `t ≤ D(βs k, k+1)` with `t > 0`, a ceiling `D(βs k, k+1) ≤ B`, and the overlap
`TransferBand.WindowOverlap`. This module discharges the ceiling in the basin, and settles what each available
structure gives for the floor. The floor itself is not proved. Declarations are in the namespace `MassGap.NextWindow`.

## 1. The ceiling (proved, every `u₀ ≤ 1/1000`)

* `next_le_sq`: on a tower at `u₀ ≤ 1/1000`, eventually `D(βs k, k+1) ≤ 250 u₀²`
  (`CouplingTower.windowCoupling_succ_le`, the squaring recursion of `DoublingSharp`).
* `next_le_quarter`: eventually `D(βs k, k+1) ≤ u₀/4` (`CouplingTower.basin_contracts`).
* `windowUpper_of_floor`: the floor and the overlap alone give
  `WindowUpper N βs (log(30 (e^{8u₀ + 500 u₀²} − 1)/t))`: the input `B` of `windowUpper_of_overlap` is gone.
* `measTowerG_of_floor_deep`: the same at the deep seed `u₀ ≤ (1/2)^{2^i}/250`, `i ≥ 1`.

## 2. The floor along the tower's own steps (proved)

* `floor_iff_drop`: on a tower, eventually `t ≤ D(βs k, k+1)` exactly when, eventually, one tower step moves the
  next-window reading by at most `u₀ − t`: `D(βs (k+1), k+1) − D(βs k, k+1) ≤ u₀ − t`. The floor is a statement
  about the size of one step of the tower at a fixed window.
* `step_drop`: in the basin that step is at least `3u₀/4`. So a floor through continuity of `β ↦ D(β, k+1)`
  (`CouplingTower.continuous_windowCoupling`) cannot come from the step being small: it needs the step's change
  pinned inside `[3u₀/4, u₀ − t]`, an interval of length below `u₀/4`.
* `lipschitz_step_ge`: any Lipschitz bound `L_k` of `D(·, k+1)` on the step satisfies `3u₀/4 ≤ L_k |βs(k+1) − βs k|`.
* `next_le_of_monotoneOn`: monotonicity of `D(·, k+1)` on the step with `βs k ≤ βs (k+1)` gives
  `D(βs k, k+1) ≤ u₀`: the ceiling side, never the floor.

## 3. The doubling structure gives no floor (proved)

* `spike`: the corner function `x(0) = u₀/16`, `x(v) = 0` elsewhere. `spike_positive`, `spike_positiveS`: it
  satisfies `DoublingRecursion.Positive` and `DoublingSharp.PositiveS`, the positivity facts the recursion reads;
  `spike_Δ_zero`, `spike_Δ_one`: `Δ(corner 0) = u₀` and `Δ(corner 1) = 0`. So reflection positivity in the form the
  tree uses, the squaring facts and the corner lemmas (`StallRigid.pred_le`, `StallRigid.exists_step`, which read
  only `Positive`) bound the next window above and never below. `TransferBand.flat_stall` is the same at the
  level of one finite transfer spectrum: defect `u₀` at time `m` and at most `2 e^{−C}(e^{u₀} − 1)` at time `2m`,
  every `C`.

## 4. A tower chosen to carry the floor (proved)

* `exists_floored_tower_iff`: a coupling tower with `t ≤ D(βs k, k+1)` eventually exists exactly when, for every
  `J`, eventually in `b` some `β ≥ J` has `D(β, b) = u₀` and `t ≤ D(β, b+1)` (the selection of
  `CouplingTower.exists_tendsto_of_forall_eventually`). The construction of `CouplingTower.eventually_crossing`
  places `D(·, b) = u₀` by the intermediate value theorem on one window; the floor asks a second inequality at the
  same coupling, which one real parameter does not control.
* `windowUpper_of_crossings`: under that crossing condition, a tower with the floor and the ceiling `250 u₀²`
  exists, and on it the overlap gives `WindowUpper`.

## The exact missing inequality

`NextFloor N u₀ t`: for every `J`, eventually in `b`, some `β ≥ J` has `D(β, b) = u₀` and `t ≤ D(β, b+1)`.
With `t ≤ 250 u₀²` forced by `floor_le_sq` with `exists_floored_tower_iff`; `t > 0` is fixed and the bound is uniform
in `b`. In step-scaling terms it says the step-scaling function at `u₀` is positive: the theory read at twice the window does not return to the trivial fixed point at once.

## What does not follow

* `NextFloor` is proved at no `u₀ > 0`. Every structure in the tree that relates two windows at one coupling is
  an upper bound (`spike`, `flat_stall`); no lower bound `D(β, w+1) ≥ f(D(β, w))` with `f > 0` on `(0, 1/1000]` is
  in the tree, and `spike` shows none follows from `Positive` and `PositiveS`.
* `spike` is a corner function, not the logarithm of a Wilson partition function; it shows what the positivity
  facts allow, not that a Wilson torus realises it. `flat_stall` is a finite spectrum, not a slice transfer.
* Monotonicity of `β ↦ D(β, w)` is proved nowhere (`CouplingTower`, section 5); `step_drop` shows it would give
  the ceiling only.
* The overlap `WindowOverlap` stays open, as in `TransferBand`.
* `measTowerG_of_floor_deep` needs `log(30 (e^{8u₀+500u₀²} − 1)/t) ≤ 2 · 2^i log 2`; with `t ≤ 250 u₀²` this places
  `t` within a factor `e^{−2·2^i log 2}` of the scale `u₀`, and no theorem here does.

DERIVED (module-wide): `1` the least window and the step; `0` the signs and the base corner; `16 = 2⁴` the copies
in `Δ`; `2` the doubling and the doubled ceiling `500 = 2 · 250`; `3/4 = 1 − 1/4` from the contraction. Inherited:
`250`, `1/1000` of `DoublingSharp.rec_sharp`; `1/4` of `CouplingTower.basin_contracts`; `30`, `8`, `2` of
`StallRigid.fork_quant`; `(1/2)^{2^i}/250` the deep seed of `ReflFloor.mass_floor_deep`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.NextWindow

open Filter Topology
open MassGap MassGap.DoublingRecursion
open MassGap.CouplingTower (CouplingTower windowCoupling)
open MassGap.BandUpper (WindowUpper)
open MassGap.MeasuredTower (MeasTowerG)

/-! ## 3. The doubling structure gives no floor -/

/-- The spike corner function: `u₀/16` at the base corner, `0` elsewhere. DERIVED: `16 = 2⁴` the copies;
`0` the base corner. -/
def spike (u₀ : ℝ) : Pt → ℝ := fun v => if v = corner 0 then u₀ / 16 else 0

/-- A shifted point is not the corner `0`. DERIVED: `0` the corner. -/
theorem add_E_ne (v : Pt) (μ : Fin 4) : v + E μ ≠ corner 0 := by
  intro h
  have := congrFun h μ
  fin_cases μ <;> simp [E, corner] at this

/-- **The spike is positive.** DERIVED: `0` the sign. -/
theorem spike_positive {u₀ : ℝ} (hu : 0 ≤ u₀) : Positive (spike u₀) where
  nonneg μ v := by
    have h1 := add_E_ne v μ
    simp only [DoublingRecursion.p, spike]
    rw [if_neg h1]
    split_ifs <;> linarith
  sq μ v _ := by
    have h1 := add_E_ne v μ
    have h2 := add_E_ne (v + E μ) μ
    simp only [DoublingRecursion.p, spike]
    rw [if_neg h1, if_neg h2]
    have := sq_nonneg (2 * (if v = corner 0 then u₀ / 16 else 0) - 0)
    linarith

/-- **The spike meets the sharp squaring facts.** DERIVED: `0` the sign. -/
theorem spike_positiveS {u₀ : ℝ} (hu : 0 ≤ u₀) : DoublingSharp.PositiveS (spike u₀) where
  nonneg μ v := (spike_positive hu).nonneg μ v
  sq μ v _ := by
    have h1 := add_E_ne v μ
    have h2 := add_E_ne (v + E μ) μ
    simp only [DoublingRecursion.p, spike]
    rw [if_neg h1, if_neg h2]
    have := sq_nonneg (2 * (if v = corner 0 then u₀ / 16 else 0) - 0)
    nlinarith

/-- The corner after `0`. DERIVED: `0`, `1` the corners. -/
theorem corner_zero_add_one : (corner 0 : Pt) + one = corner 1 := by
  funext i; fin_cases i <;> rfl

/-- The corner after `1`. DERIVED: `1`, `2` the corners. -/
theorem corner_one_add_one : (corner 1 : Pt) + one = corner 2 := by
  funext i; fin_cases i <;> rfl

/-- **The spike holds `u₀` at the window.** DERIVED: `16` the copies. -/
theorem spike_Δ_zero (u₀ : ℝ) : Δ (spike u₀) (corner 0) = u₀ := by
  have h1 : (corner 1 : Pt) ≠ corner 0 := by decide
  simp only [DoublingRecursion.Δ, spike]
  rw [corner_zero_add_one, if_neg h1, if_pos trivial]
  ring

/-- **The spike vanishes at the next window.** DERIVED: `16` the copies. -/
theorem spike_Δ_one (u₀ : ℝ) : Δ (spike u₀) (corner 1) = 0 := by
  have h1 : (corner 1 : Pt) ≠ corner 0 := by decide
  have h2 : (corner 2 : Pt) ≠ corner 0 := by decide
  simp only [DoublingRecursion.Δ, spike]
  rw [corner_one_add_one, if_neg h1, if_neg h2]
  ring

/-- **No floor from positivity.** For every `u₀ ≥ 0` a corner function satisfies `Positive` and `PositiveS`, holds
`Δ(corner 0) = u₀` and has `Δ(corner 1) = 0`. It is not a Wilson partition function; it shows what the positivity
facts allow. DERIVED: `0` the sign and the vanishing. -/
theorem no_floor_from_positivity {u₀ : ℝ} (hu : 0 ≤ u₀) :
    ∃ x : Pt → ℝ, Positive x ∧ DoublingSharp.PositiveS x ∧ Δ x (corner 0) = u₀ ∧ Δ x (corner 1) = 0 :=
  ⟨spike u₀, spike_positive hu, spike_positiveS hu, spike_Δ_zero u₀, spike_Δ_one u₀⟩

/-! ## 1, 2, 4. Along a coupling tower -/

section Tower

variable {N : ℕ} [NeZero N]

/-- **The ceiling of the next window.** On a tower at `u₀ ≤ 1/1000`, eventually `D(βs k, k+1) ≤ 250 u₀²`.
Inherited: `250`, `1/1000` of `DoublingSharp.rec_sharp`. -/
theorem next_le_sq {u₀ : ℝ} (hu : u₀ ≤ 1 / 1000) {βs : ℕ → ℝ} (hT : CouplingTower N u₀ βs id) :
    ∀ᶠ k in atTop, windowCoupling N (βs k) (k + 1) ≤ 250 * u₀ ^ 2 := by
  filter_upwards [hT.2.2] with k ⟨hk, hβ, hg⟩
  have hg' : windowCoupling N (βs k) k = u₀ := hg
  have hk' : 1 ≤ k := hk
  have h := CouplingTower.windowCoupling_succ_le (NeZero.ne N) hβ hk' (by rw [hg']; exact hu)
  rwa [hg'] at h

/-- **The next window is at most a quarter.** Inherited: `1/4` of `CouplingTower.basin_contracts`. -/
theorem next_le_quarter {u₀ : ℝ} (hu : u₀ ≤ 1 / 1000) {βs : ℕ → ℝ} (hT : CouplingTower N u₀ βs id) :
    ∀ᶠ k in atTop, windowCoupling N (βs k) (k + 1) ≤ u₀ / 4 := by
  filter_upwards [hT.2.2] with k ⟨hk, hβ, hg⟩
  have hg' : windowCoupling N (βs k) k = u₀ := hg
  have hk' : 1 ≤ k := hk
  have h := CouplingTower.basin_contracts (NeZero.ne N) hβ hk' (by rw [hg']; exact hu)
  rwa [hg'] at h

/-- **The tower at the next step**: eventually `D(βs (k+1), k+1) = u₀`. DERIVED: `1` the step. -/
theorem tower_succ {u₀ : ℝ} {βs : ℕ → ℝ} (hT : CouplingTower N u₀ βs id) :
    ∀ᶠ k in atTop, windowCoupling N (βs (k + 1)) (k + 1) = u₀ :=
  ((tendsto_add_atTop_nat 1).eventually hT.2.2).mono fun _ h => h.2.2

/-- **The floor is the size of one tower step.** On a tower, eventually `t ≤ D(βs k, k+1)` exactly when,
eventually, `D(βs (k+1), k+1) − D(βs k, k+1) ≤ u₀ − t`. DERIVED: `1` the step. -/
theorem floor_iff_drop {u₀ t : ℝ} {βs : ℕ → ℝ} (hT : CouplingTower N u₀ βs id) :
    (∀ᶠ k in atTop, t ≤ windowCoupling N (βs k) (k + 1)) ↔
      ∀ᶠ k in atTop, windowCoupling N (βs (k + 1)) (k + 1) - windowCoupling N (βs k) (k + 1) ≤ u₀ - t := by
  constructor
  · intro h
    filter_upwards [h, tower_succ hT] with k h1 h2
    rw [h2]; linarith
  · intro h
    filter_upwards [h, tower_succ hT] with k h1 h2
    rw [h2] at h1; linarith

/-- **In the basin one tower step moves the next window by at least `3u₀/4`.** DERIVED: `3/4 = 1 − 1/4`.
Inherited: `1/4`, `1/1000` of `CouplingTower.basin_contracts`. -/
theorem step_drop {u₀ : ℝ} (hu : u₀ ≤ 1 / 1000) {βs : ℕ → ℝ} (hT : CouplingTower N u₀ βs id) :
    ∀ᶠ k in atTop,
      3 * u₀ / 4 ≤ windowCoupling N (βs (k + 1)) (k + 1) - windowCoupling N (βs k) (k + 1) := by
  filter_upwards [next_le_quarter hu hT, tower_succ hT] with k h1 h2
  rw [h2]; linarith

/-- **A Lipschitz bound on the step is not small.** If eventually the step's change is at most
`L_k |βs (k+1) − βs k|`, then eventually `3u₀/4 ≤ L_k |βs (k+1) − βs k|`. DERIVED: `3/4` as in `step_drop`;
`1/1000` the basin seed of `CouplingTower.basin_contracts`. -/
theorem lipschitz_step_ge {u₀ : ℝ} (hu : u₀ ≤ 1 / 1000) {βs : ℕ → ℝ} (hT : CouplingTower N u₀ βs id)
    {L : ℕ → ℝ}
    (hL : ∀ᶠ k in atTop, windowCoupling N (βs (k + 1)) (k + 1) - windowCoupling N (βs k) (k + 1)
      ≤ L k * |βs (k + 1) - βs k|) :
    ∀ᶠ k in atTop, 3 * u₀ / 4 ≤ L k * |βs (k + 1) - βs k| := by
  filter_upwards [step_drop hu hT, hL] with k h1 h2
  linarith

/-- **Monotonicity gives the ceiling side.** If `βs k ≤ βs (k+1)`, `D(·, k+1)` is monotone on `[βs k, βs (k+1)]`
and `D(βs (k+1), k+1) = u₀`, then `D(βs k, k+1) ≤ u₀`. DERIVED: `1` the step. -/
theorem next_le_of_monotoneOn {u₀ : ℝ} {βs : ℕ → ℝ} {k : ℕ} (hle : βs k ≤ βs (k + 1))
    (hmono : MonotoneOn (fun β => windowCoupling N β (k + 1)) (Set.Icc (βs k) (βs (k + 1))))
    (hg : windowCoupling N (βs (k + 1)) (k + 1) = u₀) : windowCoupling N (βs k) (k + 1) ≤ u₀ := by
  have : windowCoupling N (βs k) (k + 1) ≤ windowCoupling N (βs (k + 1)) (k + 1) :=
    hmono ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle
  rw [hg] at this
  exact this

variable (N) in
/-- **The next-window floor at `u₀`, in the crossing form.** For every `J`, eventually in `b`, some coupling
`β ≥ J` reads `D(β, b) = u₀` at the window and `t ≤ D(β, b+1)` at the next one. DERIVED: `1` the least window
and the step; `0` the sign. -/
def NextFloor (u₀ t : ℝ) : Prop :=
  ∀ J : ℕ, ∀ᶠ b in atTop, ∃ β : ℝ, (J : ℝ) ≤ β ∧
    (1 ≤ b ∧ 0 ≤ β ∧ windowCoupling N β b = u₀ ∧ t ≤ windowCoupling N β (b + 1))

/-- **A tower carries the floor exactly when the crossings do.** DERIVED: `1` the step. -/
theorem exists_floored_tower_iff {u₀ t : ℝ} :
    (∃ βs : ℕ → ℝ, CouplingTower N u₀ βs id ∧ ∀ᶠ k in atTop, t ≤ windowCoupling N (βs k) (k + 1)) ↔
      NextFloor N u₀ t := by
  constructor
  · rintro ⟨βs, ⟨hβ, -, hev⟩, hfl⟩ J
    filter_upwards [hβ.eventually (eventually_ge_atTop (J : ℝ)), hev, hfl] with b h1 ⟨h2, h3, h4⟩ h5
    exact ⟨βs b, h1, h2, h3, h4, h5⟩
  · intro h
    obtain ⟨βs, hT, hev⟩ := CouplingTower.exists_tendsto_of_forall_eventually
      (P := fun b β => 1 ≤ b ∧ 0 ≤ β ∧ windowCoupling N β b = u₀ ∧ t ≤ windowCoupling N β (b + 1)) h
    exact ⟨βs, ⟨hT, tendsto_id, hev.mono fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩⟩, hev.mono fun _ h => h.2.2.2⟩

/-- **The floor is at most `250 u₀²`.** A floored tower at `u₀ ≤ 1/1000` has `t ≤ 250 u₀²`.
Inherited: `250`, `1/1000`. -/
theorem floor_le_sq {u₀ t : ℝ} (hu : u₀ ≤ 1 / 1000) {βs : ℕ → ℝ} (hT : CouplingTower N u₀ βs id)
    (hfl : ∀ᶠ k in atTop, t ≤ windowCoupling N (βs k) (k + 1)) : t ≤ 250 * u₀ ^ 2 := by
  obtain ⟨k, h1, h2⟩ := (hfl.and (next_le_sq hu hT)).exists
  linarith

variable [Fact (2 ≤ N)]

/-- **The floor and the overlap give the upper half of (M).** On a tower at `u₀ ≤ 1/1000`, a floor
`t ≤ D(βs k, k+1)` (`t > 0`) and an overlap at some `a > 0`, eventually, give
`WindowUpper N βs (log(30 (e^{8u₀ + 2 · 250 u₀²} − 1)/t))`. Inherited: `30`, `8`, `2` of `StallRigid.fork_quant`;
`250`, `1/1000` of `DoublingSharp.rec_sharp`. -/
theorem windowUpper_of_floor {u₀ t : ℝ} (hu : u₀ ≤ 1 / 1000) (ht : 0 < t) {βs : ℕ → ℝ}
    (hT : CouplingTower N u₀ βs id) (hfl : ∀ᶠ k in atTop, t ≤ windowCoupling N (βs k) (k + 1))
    (hov : ∀ᶠ k in atTop, ∃ a : ℝ, 0 < a ∧ TransferBand.WindowOverlap N (βs k) k a) :
    WindowUpper N βs (Real.log (30 * (Real.exp (8 * u₀ + 2 * (250 * u₀ ^ 2)) - 1) / t)) :=
  TransferBand.windowUpper_of_overlap ht hT (by
    filter_upwards [hfl, next_le_sq hu hT, hov] with k h1 h2 h3
    exact ⟨h1, h2, h3⟩)

/-- **The measured tower from the floor and the overlap at the tower's depth.** At `i ≥ 1`,
`u₀ ≤ (1/2)^{2^i}/250`, with `log(30 (e^{8u₀+500u₀²} − 1)/t) ≤ 2 · 2^i log 2`. DERIVED: `1` the least depth;
`2` the band ratio and the least `2^i`; `1/4 = (1/2)²`. Inherited: the deep seed; `250`; `30`, `8`, `2`. -/
theorem measTowerG_of_floor_deep {u₀ t : ℝ} {i : ℕ} (hi : 1 ≤ i)
    (hu : u₀ ≤ (1 / 2 : ℝ) ^ (2 ^ i) / 250) (ht : 0 < t) {βs : ℕ → ℝ} (hT : CouplingTower N u₀ βs id)
    (hfl : ∀ᶠ k in atTop, t ≤ windowCoupling N (βs k) (k + 1))
    (hov : ∀ᶠ k in atTop, ∃ a : ℝ, 0 < a ∧ TransferBand.WindowOverlap N (βs k) k a)
    (hU : Real.log (30 * (Real.exp (8 * u₀ + 2 * (250 * u₀ ^ 2)) - 1) / t) ≤ 2 * (2 ^ i * Real.log 2)) :
    MeasTowerG (MassGap.SUN.SU N) βs := by
  have h2 : 2 ≤ 2 ^ i := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
  have hp : (1 / 2 : ℝ) ^ (2 ^ i) ≤ (1 / 2) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) h2
  have hu' : u₀ ≤ 1 / 1000 := by nlinarith
  have hfull : ∀ᶠ k in atTop, t ≤ windowCoupling N (βs k) (k + 1) ∧
      windowCoupling N (βs k) (k + 1) ≤ 250 * u₀ ^ 2 ∧
      ∃ a : ℝ, 0 < a ∧ TransferBand.WindowOverlap N (βs k) k a := by
    filter_upwards [hfl, next_le_sq hu' hT, hov] with k h1 h2 h3
    exact ⟨h1, h2, h3⟩
  exact TransferBand.measTowerG_of_overlap_deep hi hu ht hT hfull hU

/-- **The crossing floor gives a tower with the floor and the ceiling, and on it the overlap gives the upper half
of (M).** Inherited: as in `windowUpper_of_floor`. -/
theorem windowUpper_of_crossings {u₀ t : ℝ} (hu : u₀ ≤ 1 / 1000) (ht : 0 < t) (hF : NextFloor N u₀ t) :
    ∃ βs : ℕ → ℝ, CouplingTower N u₀ βs id ∧
      (∀ᶠ k in atTop, t ≤ windowCoupling N (βs k) (k + 1) ∧
        windowCoupling N (βs k) (k + 1) ≤ 250 * u₀ ^ 2) ∧
      ((∀ᶠ k in atTop, ∃ a : ℝ, 0 < a ∧ TransferBand.WindowOverlap N (βs k) k a) →
        WindowUpper N βs (Real.log (30 * (Real.exp (8 * u₀ + 2 * (250 * u₀ ^ 2)) - 1) / t))) := by
  obtain ⟨βs, hT, hfl⟩ := exists_floored_tower_iff.mpr hF
  exact ⟨βs, hT, hfl.and (next_le_sq hu hT), fun hov => windowUpper_of_floor hu ht hT hfl hov⟩

end Tower

end MassGap.NextWindow

end

#print axioms MassGap.NextWindow.add_E_ne
#print axioms MassGap.NextWindow.spike_positive
#print axioms MassGap.NextWindow.spike_positiveS
#print axioms MassGap.NextWindow.corner_zero_add_one
#print axioms MassGap.NextWindow.corner_one_add_one
#print axioms MassGap.NextWindow.spike_Δ_zero
#print axioms MassGap.NextWindow.spike_Δ_one
#print axioms MassGap.NextWindow.no_floor_from_positivity
#print axioms MassGap.NextWindow.next_le_sq
#print axioms MassGap.NextWindow.next_le_quarter
#print axioms MassGap.NextWindow.tower_succ
#print axioms MassGap.NextWindow.floor_iff_drop
#print axioms MassGap.NextWindow.step_drop
#print axioms MassGap.NextWindow.lipschitz_step_ge
#print axioms MassGap.NextWindow.next_le_of_monotoneOn
#print axioms MassGap.NextWindow.exists_floored_tower_iff
#print axioms MassGap.NextWindow.floor_le_sq
#print axioms MassGap.NextWindow.windowUpper_of_floor
#print axioms MassGap.NextWindow.measTowerG_of_floor_deep
#print axioms MassGap.NextWindow.windowUpper_of_crossings
