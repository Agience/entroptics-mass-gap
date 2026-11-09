import Mathlib
import MassGap.LineSeedsBasin
import MassGap.StrongEndVanishing

/-!
# MassGap.LineSeedsVanishing — the line read with no sector threshold

`LineSeedsBasin` reads the strong end through two sector clauses at one window, each held below the sector
threshold of `CentreSectorSeedN.defectW_le_of_sectorsN`, with the tension area held above `K_F`. This module states
the same read with no threshold: a positive measured tension makes the flux share fall below every positive value
on large windows, and a zero-flux defect that falls below every positive value on large windows then makes the
window coupling vanish.
Declarations are in the namespace `MassGap.LineSeedsVanishing`.

* `fluxShare_eventually_le`: with `TensionBelow N A` and `0 < A β`, at every step the flux share of the window
  `2^w` is eventually below every positive value. No area threshold enters: the area `A(β) 2^w (2^w − 2)` grows
  without bound.
* `ZeroFluxVanishing N β`: at every step the zero-flux defect of the window `2^w` is eventually below every
  positive value. It is the zero-flux clause of `LineSeedsBasin.ZeroFluxAtWindow` with the threshold replaced by
  every positive value; like that clause it bounds the defect from above only.
* `vanishing_of_tension_zeroFlux`: at `β ≥ 0`, a positive measured tension and `ZeroFluxVanishing N β` make the
  window coupling vanish along the windows.
* `strongEnd_of_tension_zeroFlux`: if, at arbitrarily large `β`, the measured tension is positive and the
  zero-flux defect vanishes, the strong end holds.

DERIVED (module-wide): `0` the limit, the signs and the positivity of the tension; `2` the dyadic side, the least
window with a hop and the time extent `2^w − 2`; `1` the least window index; `3` the power of `N` in the flux
bound; `4` the four steps. Proof-internal constants: the sector threshold `1/80000` of
`CentreSectorSeedN.defectW_le_of_sectorsN` and the seed `1/1000` of `CouplingTower.tendsto_zero_of_seed`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.LineSeedsVanishing

open Filter Topology
open MassGap MassGap.ZoomSelfScale
open MassGap.CouplingTower (windowCoupling StrongEnd)
open MassGap.CentreSectorSeedN (fluxShareN trivialDefectN)
open MassGap.LineSeedsBasin (TensionBelow)

variable {N : ℕ} [NeZero N]

/-- The dyadic area `2^w (2^w − 2)` grows without bound. DERIVED: `2` the side and the least hop. -/
theorem tendsto_area : Tendsto (fun w : ℕ => (2 : ℝ) ^ w * ((2 : ℝ) ^ w - 2)) atTop atTop := by
  have h2 : Tendsto (fun w : ℕ => (2 : ℝ) ^ w) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  exact h2.atTop_mul_atTop₀ (tendsto_atTop_add_const_right _ (-2) h2 |>.congr fun w => by ring)

/-- **The flux share falls below every positive value on large windows**: with a measured tension `A` and
`0 < A β`, at every step `i`. DERIVED: `0` the signs; `2` the least window with a hop; `3` the power of `N`. -/
theorem fluxShare_eventually_le {A : ℝ → ℝ} (hT : TensionBelow N A) {β : ℝ} (hβ : 0 ≤ β) (hA : 0 < A β)
    (i : Fin 4) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ w in atTop, fluxShareN N β (2 ^ w) i ≤ ε := by
  have hu : Tendsto (fun w : ℕ => (N : ℝ) ^ 3 * Real.exp (-(A β * ((2 : ℝ) ^ w * ((2 : ℝ) ^ w - 2)))))
      atTop (𝓝 0) := by
    have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_area.const_mul_atTop hA)
    simpa using he.const_mul ((N : ℝ) ^ 3)
  filter_upwards [hu.eventually (gt_mem_nhds hε), eventually_ge_atTop 2] with w hw hw2
  exact (LineSeedsBasin.fluxShareN_le_of_area hβ w i (hT β hβ w hw2 i)).trans hw.le

variable (N) in
/-- **The zero-flux read with no threshold**: at every step, the zero-flux defect of the window `2^w` is
eventually below every positive value. DERIVED: `0` the sign of `ε`; `2` the dyadic side. -/
def ZeroFluxVanishing (β : ℝ) : Prop :=
  ∀ i : Fin 4, ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, trivialDefectN N β (2 ^ w) i ≤ ε

/-- **A positive tension and a vanishing zero-flux defect make the window coupling vanish.**
DERIVED: `0` the limit and the signs; `2` the least window with a hop and the dyadic side; `4` the steps. -/
theorem vanishing_of_tension_zeroFlux {A : ℝ → ℝ} (hT : TensionBelow N A) {β : ℝ} (hβ : 0 ≤ β)
    (hA : 0 < A β) (hZ : ZeroFluxVanishing N β) : Tendsto (windowCoupling N β) atTop (𝓝 0) := by
  have hε : (0 : ℝ) < 1 / 80000 := by norm_num
  have hF : ∀ i : Fin 4, ∀ᶠ w in atTop, fluxShareN N β (2 ^ w) i ≤ 1 / 80000 :=
    fun i => fluxShare_eventually_le hT hβ hA i hε
  have hZ' : ∀ i : Fin 4, ∀ᶠ w in atTop, trivialDefectN N β (2 ^ w) i ≤ 1 / 80000 :=
    fun i => hZ i _ hε
  have hall : ∀ᶠ w in atTop, 2 ≤ w ∧ ∀ i : Fin 4,
      fluxShareN N β (2 ^ w) i ≤ 1 / 80000 ∧ trivialDefectN N β (2 ^ w) i ≤ 1 / 80000 := by
    filter_upwards [eventually_ge_atTop 2, hF 0, hF 1, hF 2, hF 3, hZ' 0, hZ' 1, hZ' 2, hZ' 3]
      with w hw f0 f1 f2 f3 z0 z1 z2 z3
    refine ⟨hw, fun i => ?_⟩
    fin_cases i
    exacts [⟨f0, z0⟩, ⟨f1, z1⟩, ⟨f2, z2⟩, ⟨f3, z3⟩]
  obtain ⟨w, hw, hs⟩ := hall.exists
  have hn : 2 ≤ 2 ^ w := DeltaLengthTower.two_le_two_pow (by omega : 1 ≤ w)
  have he : Even (2 ^ w) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have hd : windowCoupling N β w ≤ 1 / 1000 := CentreSectorSeedN.defectW_le_of_sectorsN hβ hn he hs
  exact CouplingTower.tendsto_zero_of_seed (NeZero.ne N) hβ (by omega) hd

/-- **The strong end from the line read**: if at arbitrarily large `β` the measured tension is positive and the
zero-flux defect falls below every positive value on large windows, the strong end holds.
DERIVED: `0` the limit and the signs. -/
theorem strongEnd_of_tension_zeroFlux {A : ℝ → ℝ} (hT : TensionBelow N A)
    (h : ∃ᶠ β in atTop, 0 < A β ∧ ZeroFluxVanishing N β) : StrongEnd N := by
  refine (StrongEndVanishing.strongEnd_iff_vanishing (NeZero.ne N)).mpr ?_
  refine (h.and_eventually (eventually_ge_atTop 0)).mono ?_
  rintro β ⟨⟨hA, hZ⟩, hβ⟩
  exact vanishing_of_tension_zeroFlux hT hβ hA hZ

end MassGap.LineSeedsVanishing

#print axioms MassGap.LineSeedsVanishing.tendsto_area
#print axioms MassGap.LineSeedsVanishing.fluxShare_eventually_le
#print axioms MassGap.LineSeedsVanishing.vanishing_of_tension_zeroFlux
#print axioms MassGap.LineSeedsVanishing.strongEnd_of_tension_zeroFlux
