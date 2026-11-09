import Mathlib
import MassGap.FinalBridge

/-!
# MassGap.FloorSelfSim — does self-similarity carry the floor from the towers to every coupling?

The question: zoom in and the picture looks the same, so does a floor at one zoom give a floor at every zoom,
and with it `FinalBridge.MassReadOpens N` (`0 < mU β` at every `β ≥ 0`)? In the tree the zoom is the coupling
tower (`CouplingTower.CouplingTower N u₀ βs id`: at step `k` the window `2^k` reads the one value `u₀`), and the
floor along it is `FinalBridge.windowReading_floor`: `log 2 ≤ 2^k m′(β_k)` eventually, for `u₀` near `0⁺`.
Declarations are in the namespace `MassGap.FloorSelfSim`.

## 1. The floor at a tower step is a positive mass (proved)

* `mU_pos_of_confinedAt`: `ConfinedAt N u₀ m` at `m > 0` and one step `g(β, w) = u₀` give `0 < mU β`. No
  finiteness of `mU` is used: the floor is `ofReal (m / 2^w) ≤ mU β` in `[0, ∞]`.
* `measSpacing_pos_of_floor`: the window-unit floor `log 2 ≤ 2^k m′(β_k)` gives `0 < m′(β_k)`, so
  `m′(β_k) ≥ log 2 / 2^k > 0` (`floor_div_le`).
* `tower_mass_pos`, `tower_readOpens`: along every tower at `u₀ ≤ 1/1000`, eventually `0 < mU (βs k)`, and the
  read `ReadOpens N (βs k)` holds at every such step. This is point (b), with no finiteness hypothesis.

## 2. What "a tower through `β`" means (proved)

* `exists_tower_through`: given one tower at `u₀`, for every coupling `β` and every index `k` there is a tower
  at `u₀` whose `k`-th coupling is `β` (change one entry; every clause of the tower is eventual). Plainly, "`β`
  lies on some tower" is no constraint on `β` and carries no floor.
* The clause the floor reads at `β` is the step equation at one window: `BasinStep N β` (some window `w ≥ 1`
  reads a value `u₀ ∈ (0, 1/1000]`), and its closed form `BasinWindow N β` (some window `w ≥ 1` reads at most
  `1/1000`). `basinStep_of_tower`: the eventual steps of a basin tower are basin steps;
  `basinWindow_of_basinStep`.
* `not_basinStep_zero` (test at the anchor): at `β = 0` every window reads `0`, so `β = 0` is the step of no
  tower at `u₀ > 0`. The covering by tower steps in the strict sense fails at the anchor point itself; the cover
  has to be read in the closed form `BasinWindow`.

## 3. The covering clause and its strength (proved)

* `mU_pos_of_basinWindow`: `BasinWindow N β` at `β ≥ 0` gives the floor `ofReal (log 2 / 2^w) ≤ mU β` at that
  window, hence `0 < mU β` (`GapReadsTensorProved.confinedAt` at `u₀ = g(β, w)`). This is point (c).
* `TowerCover N := ∀ β ≥ 0, BasinWindow N β`: every coupling has a window in the basin.
  `massReadOpens_of_towerCover`: `TowerCover N ⇒ MassReadOpens N`.
* `basinWindow_iff_vanishes`: at `β ≥ 0`, `BasinWindow N β ↔ StrongAnchor.Vanishes N β` (the seed form of the
  vanishing read, `CouplingTower.tendsto_zero_of_seed` and `StrongAnchor.vanishes_iff_seed`).
* **`towerCover_iff_noStall`**: `TowerCover N ↔ StrongAnchor.NoStall N`. The covering clause is `NoStall`
  restated, not a weaker input.
* `towerCover_iff_massReadOpens`: under the template `FinalBridge.MassGivesVanishing N`,
  `TowerCover N ↔ MassReadOpens N` (`FinalBridge.massReadOpens_iff_noStall`).
* `basinWindow_anchor`: the clause holds on an interval `[0, β₀)`, `β₀ > 0` (`StrongAnchor.strongAnchor`).

Plainly: the residual of the self-similarity route is `TowerCover N`, and it is equal to `NoStall N`. It
implies `MassReadOpens N` (proved) and is implied by it only under the template `MassGivesVanishing N`; so it is
at least as strong as `MassReadOpens N`, and not strictly weaker than either. No capstone is built: the count does
not move. This route is the same problem as `NoStall N`, not an easier one.

## 4. Load tests (proved)

* `towers_without_cover` (towers do not cover): for the reading `g β w = |β − w|` a tower at every `u₀ > 0`
  exists (`βs k = k + u₀`), and the coupling `1/2` has no window at or below `1/1000`. For an abstract reading `g`,
  towers at every `u₀` exist while a given coupling has no window in the basin: the notion of a tower alone does
  not give a cover. Whether the lattice window coupling covers is the content of `TowerCover N`.
* `free_basinWindow_massless` (free field): the massless free window `WindowFreq.freeWindow 0` has a window at or
  below `1/1000` (it tends to `−∞`, `WindowFreq.tendsto_defect_massless`), while the massless read stalls
  (`FinalBridge.freeRead_massless_stalls`). So the passage from one basin window to a floor is not
  self-similarity: it is the gauge theory's sign `windowCoupling_nonneg` and the squaring `DoublingSharp.rec_sharp`
  of `CouplingTower.basin_contracts`. At the free field the clause that reads the mass is the vanishing read
  itself (`WindowFreq.freeWindow_vanishes_iff`).

## 5. The answer to the question, plainly

Self-similarity along a tower carries the floor from one step to the next only along a level set of the window
coupling: step `k` and step `k+1` read the same `u₀` at windows `2^k`, `2^{k+1}`, and the floor `log 2` in window
units is the same statement at each. It does not carry the floor across couplings off the level sets. Every
coupling that some basin level set passes through already has a basin window, and a basin window already has the
vanishing read; so the self-similar floor reaches exactly the couplings where `Vanishes` holds. The question "why
does a floor remain at every coupling" becomes, under this route, "why does every coupling have one window in the
basin", which is `NoStall N` (`towerCover_iff_noStall`). Nothing here proves it beyond the anchor `[0, β₀)`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the signs, the lower end of the couplings and the ultralocal coupling; `1` the least
window index and the base of `log 2 > 0`; `2` the window base `2^w` and the least rank of `SU(N)`; `log 2` the
window rate of `CouplingTower.windowGap` (through `GapReadsTensorProved.confinedAt`). Inherited, not derived here:
`1/1000` the seed of `DoublingSharp` (the edge of the basin). Counterexample choices: the reading `|β − w|`, the
tower `k + u₀` and the coupling `1/2` in `towers_without_cover`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.FloorSelfSim

open Filter Topology
open scoped ENNReal
open MassGap.CouplingTower (windowCoupling CouplingTower TowerOf ConfinedAt windowCoupling_zero
  tendsto_zero_of_seed)
open MassGap.MeasuredSpacing (mU measSpacing)

variable {N : ℕ} [NeZero N]

/-! ## 1. The floor at a tower step is a positive mass -/

/-- **A confined step has a positive mass**: `ConfinedAt N u₀ m` at `m > 0` and one step `g(β, w) = u₀` give
`0 < mU β`. DERIVED: `0` the sign; `1` the least index; `2` the window base. -/
theorem mU_pos_of_confinedAt {u₀ m β : ℝ} {w : ℕ} (hIR : ConfinedAt N u₀ m) (hm : 0 < m) (hβ : 0 ≤ β)
    (hw : 1 ≤ w) (hg : windowCoupling N β w = u₀) : 0 < mU (NeZero.ne N) β :=
  lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (div_pos hm (by positivity))) (hIR β hβ w hw hg)

/-- **The window-unit floor gives a positive spacing**: `log 2 ≤ 2^k m′(β_k)` gives `0 < m′(β_k)`.
DERIVED: `1` the base of `log 2 > 0`; `2` the window base. -/
theorem measSpacing_pos_of_floor {βs : ℕ → ℝ} {k : ℕ}
    (h : Real.log 2 ≤ ScaleLightCone.windowReading N βs k) : 0 < measSpacing (NeZero.ne N) (βs k) := by
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have hr : 0 < (2 : ℝ) ^ k * measSpacing (NeZero.ne N) (βs k) := lt_of_lt_of_le hl h
  exact pos_of_mul_pos_right hr hp.le

/-- **The floor in lattice units**: `log 2 ≤ 2^k m′(β_k)` gives `log 2 / 2^k ≤ m′(β_k)`.
DERIVED: `2` the window base. -/
theorem floor_div_le {βs : ℕ → ℝ} {k : ℕ} (h : Real.log 2 ≤ ScaleLightCone.windowReading N βs k) :
    Real.log 2 / 2 ^ k ≤ measSpacing (NeZero.ne N) (βs k) := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  rw [div_le_iff₀ hp, mul_comm]
  exact h

/-- **(b) Along a basin tower the mass is positive at every eventual step**, with no finiteness hypothesis.
DERIVED: `2` the least rank; `log 2` the window rate. Inherited: `1/1000` the seed of `DoublingSharp`. -/
theorem tower_mass_pos (hN2 : 2 ≤ N) {u₀ : ℝ} (hu : u₀ ≤ 1 / 1000) {βs : ℕ → ℝ} {ws : ℕ → ℕ}
    (hT : CouplingTower N u₀ βs ws) : ∀ᶠ k in atTop, 0 < mU (NeZero.ne N) (βs k) := by
  filter_upwards [hT.2.2] with k ⟨hw, hβ, hg⟩
  exact mU_pos_of_confinedAt (GapReadsTensorProved.confinedAt hN2 hu) (Real.log_pos one_lt_two) hβ hw hg

/-- **(b) The read opens at every eventual step of a basin tower.** DERIVED: `2` the least rank.
Inherited: `1/1000` the seed. -/
theorem tower_readOpens (hN2 : 2 ≤ N) {u₀ : ℝ} (hu : u₀ ≤ 1 / 1000) {βs : ℕ → ℝ} {ws : ℕ → ℕ}
    (hT : CouplingTower N u₀ βs ws) : ∀ᶠ k in atTop, FinalBridge.ReadOpens N (βs k) :=
  (tower_mass_pos hN2 hu hT).mono fun _ h => (FinalBridge.readOpens_iff _).mpr h

/-! ## 2. What "a tower through `β`" means -/

/-- **Membership in a tower is no constraint**: given one tower at `u₀`, every coupling `β` is the `k`-th
coupling of some tower at `u₀`, for every `k`. DERIVED: no numeral. -/
theorem exists_tower_through {u₀ : ℝ} {βs : ℕ → ℝ} {ws : ℕ → ℕ} (hT : CouplingTower N u₀ βs ws)
    (β : ℝ) (k : ℕ) : ∃ βs' : ℕ → ℝ, CouplingTower N u₀ βs' ws ∧ βs' k = β := by
  refine ⟨Function.update βs k β, ⟨?_, hT.2.1, ?_⟩, Function.update_self k β βs⟩
  · refine hT.1.congr' ?_
    filter_upwards [eventually_gt_atTop k] with j hj
    exact (Function.update_of_ne hj.ne' β βs).symm
  · filter_upwards [hT.2.2, eventually_gt_atTop k] with j h hj
    rw [Function.update_of_ne hj.ne' β βs]
    exact h

variable (N) in
/-- **`β` is a step of a basin tower**: some window `w ≥ 1` reads a value `u₀ ∈ (0, 1/1000]` at `β`.
DERIVED: `0` the sign; `1` the least index. Inherited: `1/1000` the seed. -/
def BasinStep (β : ℝ) : Prop :=
  ∃ w : ℕ, 1 ≤ w ∧ ∃ u₀ : ℝ, 0 < u₀ ∧ u₀ ≤ 1 / 1000 ∧ windowCoupling N β w = u₀

variable (N) in
/-- **`β` has a basin window**: some window `w ≥ 1` reads at most `1/1000` at `β`.
DERIVED: `1` the least index. Inherited: `1/1000` the seed. -/
def BasinWindow (β : ℝ) : Prop :=
  ∃ w : ℕ, 1 ≤ w ∧ windowCoupling N β w ≤ 1 / 1000

/-- **The eventual steps of a basin tower are basin steps.** DERIVED: `0` the sign.
Inherited: `1/1000` the seed. -/
theorem basinStep_of_tower {u₀ : ℝ} (hu0 : 0 < u₀) (hu : u₀ ≤ 1 / 1000) {βs : ℕ → ℝ}
    (hT : CouplingTower N u₀ βs id) : ∀ᶠ k in atTop, BasinStep N (βs k) := by
  filter_upwards [hT.2.2] with k hk
  exact ⟨k, hk.1, u₀, hu0, hu, hk.2.2⟩

/-- **A basin step is a basin window.** DERIVED: no numeral. -/
theorem basinWindow_of_basinStep {β : ℝ} (h : BasinStep N β) : BasinWindow N β := by
  obtain ⟨w, hw, u₀, -, hu, hg⟩ := h
  exact ⟨w, hw, hg ▸ hu⟩

/-- **Test at the anchor: `β = 0` is the step of no tower at `u₀ > 0`.** DERIVED: `0` the ultralocal coupling. -/
theorem not_basinStep_zero : ¬ BasinStep N 0 := by
  rintro ⟨w, -, u₀, hu0, -, hg⟩
  rw [windowCoupling_zero] at hg
  linarith

/-! ## 3. The covering clause and its strength -/

/-- **(c) A basin window gives the floor and a positive mass**: at `β ≥ 0`, a window `w ≥ 1` with
`g(β, w) ≤ 1/1000` gives `ofReal (log 2 / 2^w) ≤ mU β`, so `0 < mU β`. DERIVED: `1` the least window; `2` the
least rank and the base; `log 2` the window rate. Inherited: `1/1000` the seed of `DoublingSharp`. -/
theorem mU_pos_of_basinWindow (hN2 : 2 ≤ N) {β : ℝ} (hβ : 0 ≤ β) (h : BasinWindow N β) :
    ∃ w : ℕ, 1 ≤ w ∧ ENNReal.ofReal (Real.log 2 / 2 ^ w) ≤ mU (NeZero.ne N) β ∧ 0 < mU (NeZero.ne N) β := by
  obtain ⟨w, hw, hs⟩ := h
  have hIR := GapReadsTensorProved.confinedAt hN2 hs
  exact ⟨w, hw, hIR β hβ w hw rfl, mU_pos_of_confinedAt hIR (Real.log_pos one_lt_two) hβ hw rfl⟩

variable (N) in
/-- **The covering clause**: every coupling `β ≥ 0` has a basin window. DERIVED: `0` the lower end. -/
def TowerCover : Prop := ∀ β : ℝ, 0 ≤ β → BasinWindow N β

/-- **(c) The cover gives the bridge**: `TowerCover N ⇒ MassReadOpens N`. DERIVED: `2` the least rank. -/
theorem massReadOpens_of_towerCover (hN2 : 2 ≤ N) (hC : TowerCover N) : FinalBridge.MassReadOpens N :=
  fun β hβ => (FinalBridge.readOpens_iff β).mpr (mU_pos_of_basinWindow hN2 hβ (hC β hβ)).choose_spec.2.2

/-- **A basin window is the vanishing read**: at `β ≥ 0`, `BasinWindow N β ↔ Vanishes N β`.
DERIVED: `0` the lower end. Inherited: `1/1000` the seed. -/
theorem basinWindow_iff_vanishes {β : ℝ} (hβ : 0 ≤ β) : BasinWindow N β ↔ StrongAnchor.Vanishes N β := by
  constructor
  · rintro ⟨w, hw, hs⟩
    exact tendsto_zero_of_seed (NeZero.ne N) hβ hw hs
  · intro h
    obtain ⟨c, hc, hlt⟩ := (StrongAnchor.vanishes_iff_seed (NeZero.ne N) hβ).mp h
    exact ⟨c, hc, hlt.le⟩

/-- **The covering clause is `NoStall`**: `TowerCover N ↔ NoStall N`. DERIVED: `0` the lower end. -/
theorem towerCover_iff_noStall : TowerCover N ↔ StrongAnchor.NoStall N := by
  rw [StrongAnchor.noStall_iff (NeZero.ne N)]
  exact forall₂_congr fun β hβ => basinWindow_iff_vanishes hβ

/-- **Under the finite-size template the cover is the bridge**: `MassGivesVanishing N` gives
`TowerCover N ↔ MassReadOpens N`. DERIVED: `2` the least rank. -/
theorem towerCover_iff_massReadOpens (hN2 : 2 ≤ N) (hT : FinalBridge.MassGivesVanishing N) :
    TowerCover N ↔ FinalBridge.MassReadOpens N :=
  towerCover_iff_noStall.trans (FinalBridge.massReadOpens_iff_noStall hN2 hT).symm

/-- **The cover holds on the anchor**: on some `[0, β₀)`, `β₀ > 0`, every coupling has a basin window.
DERIVED: `0` the lower end. -/
theorem basinWindow_anchor : ∃ β₀ > 0, ∀ β : ℝ, 0 ≤ β → β < β₀ → BasinWindow N β := by
  obtain ⟨β₀, hβ₀, h⟩ := StrongAnchor.strongAnchor (NeZero.ne N)
  exact ⟨β₀, hβ₀, fun β h0 hlt => (basinWindow_iff_vanishes h0).mpr (h β h0 hlt)⟩

/-! ## 4. Load tests -/

/-- **Towers do not cover**: for the reading `g β w = |β − w|` there is a tower at every `u₀ > 0`, and the
coupling `1/2` has no window at or below `1/1000`. Counterexample choices: the reading `|β − w|`, the tower
`k + u₀`, the coupling `1/2`. DERIVED: `0` the sign; `1` the least index. Inherited: `1/1000` the seed. -/
theorem towers_without_cover :
    (∀ u₀ : ℝ, 0 < u₀ → TowerOf (fun β w => |β - (w : ℝ)|) u₀ (fun k => (k : ℝ) + u₀) id) ∧
      ¬ ∃ w : ℕ, 1 ≤ w ∧ |(1 / 2 : ℝ) - (w : ℝ)| ≤ 1 / 1000 := by
  refine ⟨fun u₀ hu0 => ⟨tendsto_atTop_add_const_right _ u₀ tendsto_natCast_atTop_atTop, tendsto_id, ?_⟩, ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with k hk
    refine ⟨hk, by positivity, ?_⟩
    show |(k : ℝ) + u₀ - (k : ℝ)| = u₀
    rw [add_sub_cancel_left, abs_of_pos hu0]
  · rintro ⟨w, hw, hle⟩
    have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
    have := neg_abs_le ((1 / 2 : ℝ) - (w : ℝ))
    linarith

/-- **Free field: one window below the seed is not a mass.** The massless free window has a window `w ≥ 1` at
or below `1/1000`, while the massless read stalls. DERIVED: `0` the zero mass; `1` the least index; `2` the
window base. Inherited: `1/1000` the seed. -/
theorem free_basinWindow_massless :
    (∃ w : ℕ, 1 ≤ w ∧ WindowFreq.freeWindow 0 w ≤ 1 / 1000) ∧
      ¬ Tendsto (fun w : ℕ => (2 : ℝ) ^ w * 0) atTop atTop := by
  refine ⟨?_, FinalBridge.freeRead_massless_stalls⟩
  have ht : Tendsto (fun w : ℕ => WindowFreq.freeWindow 0 w) atTop atBot :=
    WindowFreq.tendsto_defect_massless.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
  obtain ⟨w, hle, hw⟩ := ((ht.eventually (eventually_le_atBot (1 / 1000 : ℝ))).and
    (eventually_ge_atTop 1)).exists
  exact ⟨w, hw, hle⟩

end MassGap.FloorSelfSim

end

#print axioms MassGap.FloorSelfSim.mU_pos_of_confinedAt
#print axioms MassGap.FloorSelfSim.measSpacing_pos_of_floor
#print axioms MassGap.FloorSelfSim.floor_div_le
#print axioms MassGap.FloorSelfSim.tower_mass_pos
#print axioms MassGap.FloorSelfSim.tower_readOpens
#print axioms MassGap.FloorSelfSim.exists_tower_through
#print axioms MassGap.FloorSelfSim.basinStep_of_tower
#print axioms MassGap.FloorSelfSim.basinWindow_of_basinStep
#print axioms MassGap.FloorSelfSim.not_basinStep_zero
#print axioms MassGap.FloorSelfSim.mU_pos_of_basinWindow
#print axioms MassGap.FloorSelfSim.massReadOpens_of_towerCover
#print axioms MassGap.FloorSelfSim.basinWindow_iff_vanishes
#print axioms MassGap.FloorSelfSim.towerCover_iff_noStall
#print axioms MassGap.FloorSelfSim.towerCover_iff_massReadOpens
#print axioms MassGap.FloorSelfSim.basinWindow_anchor
#print axioms MassGap.FloorSelfSim.towers_without_cover
#print axioms MassGap.FloorSelfSim.free_basinWindow_massless
