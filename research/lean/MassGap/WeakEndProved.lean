import Mathlib
import MassGap.CouplingTower
import MassGap.Telescope
import MassGap.TwistedTraceBoundFull

/-!
# MassGap.WeakEndProved — the weak-coupling end (W) holds for every `N ≥ 2`

`CouplingTower.WeakEnd N u₀` asks that on every fixed window `2^w`, `w ≥ 1`, frequently in `β`, the window
coupling exceeds `u₀`. For `u₀ ≤ 1/1000` it follows from (B₂), `DeltaLengthTower.DeltaLengthUnbounded N`, read through
`CouplingTower.weakEnd_of_deltaLengthUnbounded`, and (B₂) is `TwistedTraceBoundN.deltaLengthUnbounded`:
on a fixed torus the doubling defect exceeds `1/1000` at every large `β` (`defect_gt`; the proof gives
`log(4/3) ≥ 1/4`).

* **`weakEnd`**: `WeakEnd N u₀` for `2 ≤ N` and `u₀ ≤ 1/1000`. No positivity of `u₀` is needed.
* `couplingTower_of_strongEnd`: for `0 < u₀ ≤ 1/1000`, (S) alone gives a coupling tower at `u₀`.
* `strongEnd_iff_exists_couplingTower'`: for `0 < u₀ ≤ 1/1000`, (S) holds exactly when a tower exists.
* `couplingTower_of_focus'`: `Telescope.couplingTower_of_focus` with (W) discharged, at the price of
  `2 ≤ N` in place of `N ≠ 0` and `u₀ ≤ 1/1000`.
* `measuredTower_of_strongEnd`: `CouplingTower.measuredTower_of_ends` with (W) discharged.

So the coupling tower at a basin value `u₀` rests on (S) alone.

The range `2 ≤ N` is the range of (B₂) in `TwistedTraceBoundN.deltaLengthUnbounded`.

DERIVED (module-wide): `1/1000` the seed; `2` the least `N`; `0` the sign of `u₀`.
-/

noncomputable section

namespace MassGap.WeakEndProved

open Filter
open MassGap MassGap.ZoomSelfScale MassGap.MeasuredTower MassGap.MeasuredSpacing MassGap.ClayTreeG
  MassGap.FlowG MassGap.TimeGroupG MassGap.PeriodicReduceG MassGap.FlowClusterG
open MassGap.CouplingTower (windowCoupling StrongEnd WeakEnd CouplingTower GapReadsTensor UVConverges)

/-- **(W) for SU(N), every `N ≥ 2`, at every `u₀ ≤ 1/1000`.** -/
theorem weakEnd {N : ℕ} (hN : 2 ≤ N) {u₀ : ℝ} (hu : u₀ ≤ 1 / 1000) : WeakEnd N u₀ :=
  CouplingTower.weakEnd_of_deltaLengthUnbounded hu (TwistedTraceBoundN.deltaLengthUnbounded hN)

/-- **A coupling tower from (S) alone**, at every `0 < u₀ ≤ 1/1000`. -/
theorem couplingTower_of_strongEnd {N : ℕ} (hN : 2 ≤ N) {u₀ : ℝ} (hu0 : 0 < u₀)
    (hu : u₀ ≤ 1 / 1000) (hS : StrongEnd N) : ∃ βs : ℕ → ℝ, CouplingTower N u₀ βs id :=
  CouplingTower.exists_couplingTower (by omega) hu0 hS (weakEnd hN hu)

/-- **(S) holds exactly when a coupling tower exists**, at every `0 < u₀ ≤ 1/1000`, with no (W). -/
theorem strongEnd_iff_exists_couplingTower' {N : ℕ} (hN : 2 ≤ N) {u₀ : ℝ} (hu0 : 0 < u₀)
    (hu : u₀ ≤ 1 / 1000) : StrongEnd N ↔ ∃ βs : ℕ → ℝ, CouplingTower N u₀ βs id :=
  CouplingTower.strongEnd_iff_exists_couplingTower (by omega) hu0 hu (weakEnd hN hu)

/-- **A tower from focus and the link alone**: `Telescope.couplingTower_of_focus` with (W) discharged. -/
theorem couplingTower_of_focus' {N : ℕ} (hN : 2 ≤ N) {u₀ : ℝ} (hu0 : 0 < u₀) (hu : u₀ ≤ 1 / 1000)
    {A B : ℝ → ℝ} {K : ℝ} (k : ℕ) (hL : Telescope.LineSeedsBasin N A K)
    (hF : ∃ᶠ β in atTop, 0 ≤ β ∧ ∃ w : ℕ, 1 ≤ w + k ∧ 4 * K ≤ ((2 : ℝ) ^ k) ^ 2 * B β ∧
      Telescope.InFocus (A β) (B β) w) : ∃ βs : ℕ → ℝ, CouplingTower N u₀ βs id :=
  Telescope.couplingTower_of_focus (by omega) hu0 (weakEnd hN hu) k hL hF

/-- **(S), the link and (UV) give a measured coupling tower with the per-step gap**:
`CouplingTower.measuredTower_of_ends` with (W) discharged. -/
theorem measuredTower_of_strongEnd {N : ℕ} [NeZero N] [Fact (2 ≤ N)] {u₀ : ℝ} (hu0 : 0 < u₀)
    (hu : u₀ ≤ 1 / 1000) (hS : StrongEnd N) (hG : GapReadsTensor N)
    (hUV : ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ∃ μ : ℝ, UVConverges N βs id μ) :
    ∃ βs : ℕ → ℝ, CouplingTower N u₀ βs id ∧ MeasTowerG (MassGap.SUN.SU N) βs ∧
      ∀ᶠ k in atTop, ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        TransferGap.GapAt
          (periodicGaugeInvDataG (MassGap.SUN.SU N) 0 0 (βs k)) r ∧
        2 * Real.log 2 / GaugeRunning.aRunG (MassGap.SUN.SU N) 1
          ≤ -Real.log r / dySpacingG (MassGap.SUN.SU N) k :=
  CouplingTower.measuredTower_of_ends hu0 hu hS (weakEnd Fact.out hu) hG hUV

end MassGap.WeakEndProved

#print axioms MassGap.WeakEndProved.weakEnd
#print axioms MassGap.WeakEndProved.couplingTower_of_strongEnd
#print axioms MassGap.WeakEndProved.strongEnd_iff_exists_couplingTower'
#print axioms MassGap.WeakEndProved.couplingTower_of_focus'
#print axioms MassGap.WeakEndProved.measuredTower_of_strongEnd
