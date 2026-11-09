import Mathlib
import MassGap.CouplingTower

/-!
# MassGap.StrongEndVanishing — the strong end is the vanishing of the window coupling

`CouplingTower.StrongEnd N` is the strong-coupling end with no threshold: frequently in `β`, the window
coupling vanishes along the windows, `windowCoupling N β w → 0` as `w → ∞`. The finite-size defect of the
periodic Wilson torus tends to `0` as the torus grows: that is the measured read. This module gives what that
read yields at one coupling. Declarations are in the namespace `MassGap.StrongEndVanishing`.

## 1. The vanishing read (proved)

* `exists_window_lt_of_tendsto_zero`: a vanishing window coupling is eventually below every positive value, at
  some window `c ≥ 1`.
* `strongEnd_iff_vanishing`: `StrongEnd N ↔ ∃ᶠ β in atTop, Tendsto (windowCoupling N β) atTop (𝓝 0)`, the
  definition unfolded. The basin form used inside proofs is `CouplingTower.strongEnd_iff_seed`.

## 2. The window gap from the vanishing read (proved)

* `windowGap_of_vanishing`: at `β ≥ 0` and `2 ≤ N`, if the window coupling vanishes along the windows, the
  periodic Clay gap holds at some rate `0 < r < 1`; the window is one that the limit puts in the basin
  (`CouplingTower.windowGap`). `2 ≤ N` is the hypothesis of `GapStep.periodic_clayGapAt_of_gapAt`, the passage
  from the transfer gap to the Clay gap.
* `frequently_windowGap`: (S) gives, frequently in `β`, the periodic Clay gap at some rate in `(0, 1)`.

So the confinement read at `β` is "the finite-size defect vanishes": no threshold appears in either statement.

DERIVED (module-wide): `0` the limit of the defect, the plane, the time axis and the signs; `1` the upper end of
the rate interval and the least window index; `2` the least rank of `SU(N)`. Proof-internal constant:
`1/1000` the sharp seed of `DoublingSharp`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.StrongEndVanishing

open Filter Topology
open MassGap.CouplingTower (windowCoupling StrongEnd windowCoupling_nonneg windowCoupling_decay windowGap)

variable {N : ℕ}

/-! ## 1. The vanishing read -/

/-- **A vanishing window coupling is eventually below every positive value**, at a window `c ≥ 1`.
DERIVED: `0` the limit and the sign of `ε`; `1` the least window index. -/
theorem exists_window_lt_of_tendsto_zero {β : ℝ} (h : Tendsto (windowCoupling N β) atTop (𝓝 0)) {ε : ℝ}
    (hε : 0 < ε) : ∃ c : ℕ, 1 ≤ c ∧ windowCoupling N β c < ε := by
  obtain ⟨c, hlt, hc⟩ := ((h.eventually (eventually_lt_nhds hε)).and (eventually_ge_atTop 1)).exists
  exact ⟨c, hc, hlt⟩

/-- **The strong end is the vanishing of the window coupling**: frequently in `β`, the doubling defect of the
torus of side `2^w` tends to `0` as `w → ∞`; this is the definition of `StrongEnd`. DERIVED: `0` the excluded
rank and the limit. -/
theorem strongEnd_iff_vanishing (_hN : N ≠ 0) :
    StrongEnd N ↔ ∃ᶠ β in atTop, Tendsto (windowCoupling N β) atTop (𝓝 0) :=
  Iff.rfl

/-! ## 2. The window gap from the vanishing read -/

/-- **The vanishing read gives the window gap**: at `β ≥ 0`, if the window coupling vanishes along the windows,
the periodic Clay gap holds at a rate in `(0, 1)`. DERIVED: `2` the least rank; `0` the plane, the time axis,
the signs and the limit; `1` the upper end of the rate interval. -/
theorem windowGap_of_vanishing (hN2 : 2 ≤ N) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (h : Tendsto (windowCoupling N β) atTop (𝓝 0)) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ PeriodicContent.PeriodicClayGapAt 0 0 hN β r := by
  obtain ⟨w, hw, hs⟩ := exists_window_lt_of_tendsto_zero h (show (0 : ℝ) < 1 / 1000 by norm_num)
  obtain ⟨r, hr0, hr1, -, hcl, -⟩ := windowGap hN2 hN hβ hw hs.le
  exact ⟨r, hr0, hr1, hcl⟩

/-- **(S) gives the window gap frequently in `β`.** DERIVED: `2` the least rank; `0` the plane, the time axis
and the signs; `1` the upper end of the rate interval. -/
theorem frequently_windowGap (hN2 : 2 ≤ N) (hN : N ≠ 0) (hS : StrongEnd N) :
    ∃ᶠ β in atTop, 0 ≤ β ∧ ∃ r : ℝ, 0 < r ∧ r < 1 ∧ PeriodicContent.PeriodicClayGapAt 0 0 hN β r := by
  refine (((strongEnd_iff_vanishing hN).mp hS).and_eventually (eventually_ge_atTop 0)).mono ?_
  rintro β ⟨hv, hβ⟩
  exact ⟨hβ, windowGap_of_vanishing hN2 hN hβ hv⟩

end MassGap.StrongEndVanishing

#print axioms MassGap.StrongEndVanishing.exists_window_lt_of_tendsto_zero
#print axioms MassGap.StrongEndVanishing.strongEnd_iff_vanishing
#print axioms MassGap.StrongEndVanishing.windowGap_of_vanishing
#print axioms MassGap.StrongEndVanishing.frequently_windowGap
