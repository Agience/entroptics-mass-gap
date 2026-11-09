import Mathlib
import MassGap.FlowScalingOnly

/-!
# MassGap.FlowScalingEquiv — the block observer's comparison is its scaling part on `[2^{-16}, β]`

`FlowScalingOnly.flowEnergyComp_blFam_of_scaling_lt` gives the bare–flowed comparison
`FlowEnergyComp hN (blFam … m s) (obsStep N) C K η'` at every budget `η' > η₂` from the scaling part at
budget `η₂`. This module proves the converse and with it the equivalence: the scaling part is the
comparison restated on `[2^{-16}, β]` up to an arbitrarily small change of budget (both read at every
budget strictly above `η`); this equivalence is proved.

## 1. The strong part from below (proved)

* **`strongLower_of_reach`**: the two-sided companion of `StrongLocalFiniteSize.strongPart_of_reach`. At
  `x₀ = 2^{-16}`, `C > 0`, `θ < 1`, `ε > 0` and any `K`, under the same reach hypothesis, eventually in `β`
  every window side `n` has `−ε ≤ defectW N x₀ n − K · flowDefect hN W (κ β) n x₀`. From
  `|defectW N x₀ n| ≤ x₀ · strongBound n` (`StrongFiniteSize.abs_defectW_strong_le`) and
  `|flowDefect hN W k n x₀| ≤ x₀ · strongReachBound θ n` (`StrongLocalFiniteSize.abs_flowDefect_le_tail`),
  both tending to `0` as the window side grows (`StrongLocalFiniteSize.eventually_inWin_ge`).

## 2. The converse and the equivalence (proved)

With `x₀ = 2^{-16}`, `0 ≤ s`, `0 < C`, `4 s < C`, and `θ = (4 s + C)/(2 C) < 1` as in
`FlowScalingOnly.flowEnergyComp_blFam_of_scaling`:

* **`scaling_of_flowEnergyComp`**: `FlowEnergyComp hN (blFam … m s) (obsStep N) C K η` gives the scaling part
  at budget `η + ε` for every `ε > 0`. By `FlowScalingOnly.scaling_eq` the scaling integral is
  `(defectW N β n − K F(β)) − (defectW N x₀ n − K F(x₀))`; the first term is at most `η`
  (`FlowComp.flowEnergyComp_iff_defect`), the second at least `−ε` (`strongLower_of_reach`).
* **`scaling_of_flowEnergyComp_lt`**: the same gives the scaling part at every budget `η' > η`.
* **`flowEnergyComp_blFam_iff_scaling`**: for every `K` and `η`,
  `(∀ η' > η, FlowEnergyComp … K η') ↔ (∀ η' > η, scaling part at budget η')`.

Both sides are statements about every budget strictly above `η`, so the strict inequalities lost in each
direction (the strong part tends to `0` but is not `0`) are absorbed and the two sides are the same
condition. Neither side is met by an empty window: at `C > 0` the window holds a side eventually in `β`
(`FlowScalingOnly.eventually_exists_inWin`). At `K = 0` the left side is `defectW N β n ≤ η'` at the window
side (`FlowComp.flowEnergyComp_iff_defect`) and the right side is `defectW N β n − defectW N x₀ n ≤ η'`
(`FlowScalingOnly.scaling_eq`): bounds on the bare defect at the window side, which no hypothesis here
supplies.

What remains: neither side of the equivalence is proved. The scaling part at `blFam` and `obsStep`, and so
`FlowEnergyComp` there, is assumed in `FlowScalingOnly` and open; this module shows only that the two are the
same condition.

DERIVED (module-wide): `65536 = 2^{16}` the strong-coupling threshold of `StrongLocalFiniteSize`; `2`
splitting a budget and the least side; `4`, `2` as in `FlowScalingOnly.reach_blFam`; `1` keeping
`|K| + 1` positive.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.FlowScalingEquiv

open Filter Set
open MassGap.ObserverFlowSeed (bareDelta flowDelta InWin FlowEnergyComp)
open MassGap.FlowComp (flowDefect flowEnergyComp_iff_defect)
open MassGap.ContinuumFlow (ConfFlow)
open MassGap.ObserverBlock (blFam)
open MassGap.StrongFiniteSize (strongBound abs_defectW_strong_le tendsto_strongBound)
open MassGap.StrongLocalFiniteSize (strongReachBound reachTail abs_flowDefect_le_tail
  tendsto_strongReachBound eventually_inWin_ge)
open MassGap.FlowScalingOnly (obsStep reach_blFam scaling_eq flowEnergyComp_blFam_of_scaling_lt)

variable {N : ℕ}

/-! ## 1. The strong part from below -/

/-- **The strong part from below**: at `x₀ = 2^{-16}`, `C > 0`, `θ < 1`, `ε > 0` and any `K`, if eventually
in `β` the window side `n` has `2 (W.range (κ β) + 1) ≤ θ n`, then eventually in `β`, at the window side,
`−ε ≤ defectW N x₀ n − K · flowDefect hN W (κ β) n x₀`. DERIVED: `65536 = 2^{16}`; `2` splitting `ε`;
`1` keeping `|K| + 1` positive. -/
theorem strongLower_of_reach (hN : N ≠ 0) (W : ConfFlow N) (κ : ℝ → ℕ) {C K θ ε : ℝ} (hC : 0 < C)
    (hθ : θ < 1) (hε : 0 < ε)
    (hr : ∀ᶠ β in atTop, ∀ n : ℕ, InWin N C β n → 2 * ((W.range (κ β) : ℝ) + 1) ≤ θ * n) :
    ∀ᶠ β in atTop, ∀ n : ℕ, InWin N C β n →
      -ε ≤ MassGap.ZoomSelfScale.defectW N (1 / 65536) n
        - K * flowDefect hN W (κ β) n (1 / 65536) := by
  have hK1 : 0 < |K| + 1 := by positivity
  have ev1 := (tendsto_order.mp tendsto_strongBound).2 (ε / 2) (by positivity)
  have ev2 := (tendsto_order.mp (tendsto_strongReachBound hθ)).2 (ε / (2 * (|K| + 1))) (by positivity)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (ev1.and ev2)
  filter_upwards [hr, eventually_inWin_ge hN hC n₀] with β hrβ hwβ n hw
  obtain ⟨hb1, hb2⟩ := hn₀ n (hwβ n hw)
  have hn0 : n ≠ 0 := by have := hw.2.1; omega
  have hD := abs_defectW_strong_le hN hn0 (β := 1 / 65536) (by norm_num) le_rfl
  have hF := abs_flowDefect_le_tail hN W (κ β) n hθ.le (hrβ n hw) (by norm_num) le_rfl
  have hs1 : 0 ≤ strongBound n := by unfold strongBound; positivity
  have hs2 : 0 ≤ strongReachBound θ n := by unfold strongReachBound reachTail; positivity
  have hKF : K * flowDefect hN W (κ β) n (1 / 65536)
      ≤ |K| * |flowDefect hN W (κ β) n (1 / 65536)| := by
    rw [← abs_mul]
    exact le_abs_self _
  have hKb : |K| * (ε / (2 * (|K| + 1))) ≤ ε / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg K]
  have hD' := (neg_abs_le (MassGap.ZoomSelfScale.defectW N (1 / 65536) n)).trans'
    (neg_le_neg hD)
  have hK0 := abs_nonneg K
  have e1 : (1 / 65536 : ℝ) * strongBound n ≤ ε / 2 := by nlinarith
  have e2 : |K| * |flowDefect hN W (κ β) n (1 / 65536)| ≤ ε / 2 := by
    calc _ ≤ |K| * ((1 / 65536) * strongReachBound θ n) := mul_le_mul_of_nonneg_left hF hK0
      _ ≤ |K| * (ε / (2 * (|K| + 1))) := mul_le_mul_of_nonneg_left (by nlinarith) hK0
      _ ≤ ε / 2 := hKb
  linarith

/-! ## 2. The converse and the equivalence -/

/-- **The scaling part from the block observer's comparison.** At `0 ≤ s`, `0 < C`, `4 s < C`, for every `K`,
`η` and `ε > 0`, `FlowEnergyComp hN (blFam … m s) (obsStep N) C K η` gives, eventually in `β`, at every
window side, `∫_{2^{-16}}^β (bareDelta − K · flowDelta) ≤ η + ε`. The strong part from below is
`strongLower_of_reach` at `θ = (4 s + C)/(2 C) < 1`, with the reach hypothesis
`FlowScalingOnly.reach_blFam`. DERIVED: `65536 = 2^{16}` the strong-coupling threshold; `4`, `2` as in
`reach_blFam`; `12 = 2 · 6` the coupling bound of `ObserverBlock.blFam` (`avg_coupling`). -/
theorem scaling_of_flowEnergyComp (hN2 : 2 ≤ N) (hN : N ≠ 0) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ) {s C K η ε : ℝ} (hs0 : 0 ≤ s) (hC : 0 < C)
    (hsC : 4 * s < C) (hε : 0 < ε)
    (hF : FlowEnergyComp hN (blFam hN2 c hc0 hc m s) (obsStep N) C K η) :
    ∀ᶠ β in atTop, ∀ n : ℕ, InWin N C β n →
      ∫ x in (1 / 65536 : ℝ)..β,
        (bareDelta hN n x - K * flowDelta hN (blFam hN2 c hc0 hc m s) (obsStep N β) n x) ≤ η + ε := by
  have hθ1 : (4 * s + C) / (2 * C) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hθ : 4 * s < (4 * s + C) / (2 * C) * C := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_right hsC hC]
  have hlow := strongLower_of_reach (K := K) hN _ (obsStep N) hC hθ1 hε
    (reach_blFam hN2 hc0 hc m hs0 hC hθ)
  filter_upwards [(flowEnergyComp_iff_defect hN _ (obsStep N) C K η).mp hF, hlow]
    with β hb hl n hw
  rw [scaling_eq hN _ _ (by have := hw.2.1; omega) K]
  have h1 := hb n hw
  have h2 := hl n hw
  linarith

/-- **Every budget above the comparison's budget**: under the hypotheses of `scaling_of_flowEnergyComp`, the
scaling part holds at every budget `η' > η`. DERIVED: no numeral beyond those of the scaling part: `65536 = 2^{16}` the strong-coupling
threshold; `4` as in `reach_blFam`; `12 = 2 · 6` the coupling bound of `ObserverBlock.blFam`. -/
theorem scaling_of_flowEnergyComp_lt (hN2 : 2 ≤ N) (hN : N ≠ 0) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ) {s C K η η' : ℝ} (hs0 : 0 ≤ s) (hC : 0 < C)
    (hsC : 4 * s < C) (hη' : η < η')
    (hF : FlowEnergyComp hN (blFam hN2 c hc0 hc m s) (obsStep N) C K η) :
    ∀ᶠ β in atTop, ∀ n : ℕ, InWin N C β n →
      ∫ x in (1 / 65536 : ℝ)..β,
        (bareDelta hN n x - K * flowDelta hN (blFam hN2 c hc0 hc m s) (obsStep N β) n x) ≤ η' := by
  have h := scaling_of_flowEnergyComp hN2 hN hc0 hc m (ε := η' - η) hs0 hC hsC (by linarith) hF
  simpa only [add_sub_cancel] using h

/-- **The block observer's comparison is its scaling part on `[2^{-16}, β]`, at every budget above `η`.** At `0 ≤ s`, `0 < C`,
`4 s < C`, for every `K` and `η`: `FlowEnergyComp hN (blFam … m s) (obsStep N) C K η'` at every `η' > η` iff
the scaling part `∫_{2^{-16}}^β (bareDelta − K · flowDelta) ≤ η'` holds eventually at every window side at
every `η' > η`. DERIVED: `2` the midpoint of `η` and `η'`; `65536 = 2^{16}` the strong-coupling
threshold; `4` as in `reach_blFam`; `12 = 2 · 6` the coupling bound of `ObserverBlock.blFam`. -/
theorem flowEnergyComp_blFam_iff_scaling (hN2 : 2 ≤ N) (hN : N ≠ 0) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ) {s C : ℝ} (hs0 : 0 ≤ s) (hC : 0 < C)
    (hsC : 4 * s < C) (K η : ℝ) :
    (∀ η' > η, FlowEnergyComp hN (blFam hN2 c hc0 hc m s) (obsStep N) C K η') ↔
      (∀ η' > η, ∀ᶠ β in atTop, ∀ n : ℕ, InWin N C β n →
        ∫ x in (1 / 65536 : ℝ)..β,
          (bareDelta hN n x - K * flowDelta hN (blFam hN2 c hc0 hc m s) (obsStep N β) n x) ≤ η') := by
  constructor
  · intro h η' hη'
    exact scaling_of_flowEnergyComp_lt hN2 hN hc0 hc m hs0 hC hsC (η := (η + η') / 2)
      (by linarith) (h _ (by linarith))
  · intro h η' hη'
    exact flowEnergyComp_blFam_of_scaling_lt hN2 hN hc0 hc m hs0 hC hsC (η₂ := (η + η') / 2)
      (by linarith) (h _ (by linarith))

end MassGap.FlowScalingEquiv

end

#print axioms MassGap.FlowScalingEquiv.strongLower_of_reach
#print axioms MassGap.FlowScalingEquiv.scaling_of_flowEnergyComp
#print axioms MassGap.FlowScalingEquiv.scaling_of_flowEnergyComp_lt
#print axioms MassGap.FlowScalingEquiv.flowEnergyComp_blFam_iff_scaling
