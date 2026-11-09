import Mathlib
import MassGap.StrongEndVanishing

/-!
# MassGap.SelfSimilarStep — one doubling map at every scale, and what it gives the strong end

A box at scale `2^w` is the whole system at a coarser scale: the doubling that takes the window reading at side
`2^w` to the reading at side `2^{w+1}` is the same map at every scale. This module states that step on the real
window coupling `windowCoupling N β w = defectW N β (2^w)` (the doubling defect of the periodic Wilson torus,
`CouplingTower` §1) and proves what it gives: if one continuous map `Φ`, independent of the scale `w` and of the
coupling `β`, bounds every doubling, and `Φ` has no fixed point between the trivial point `0` and the reading at
the first window, then the reading falls monotonically to `0` along the windows at every coupling, so the strong
end `CouplingTower.StrongEnd` holds and the periodic Clay gap holds at every `β ≥ 0`.
Declarations are in the namespace `MassGap.SelfSimilarStep`.

## 1. One map along an orbit (proved, abstract)

* `orbit_bound`: an orbit `h (k+1) ≤ Φ (h k)`, `h ≥ 0`, with `Φ 0 ≤ 0` and `Φ x < x` on `(0, h 0]`, stays below
  its start and decreases.
* `orbit_tendsto_zero`: with `Φ` continuous it tends to `0`. Its limit `L` is a point with `L ≤ Φ L` in
  `[0, h 0]`, and the only such point is `0`. No rate, no threshold, and no monotonicity of `Φ` enter.
* `orbit_drops_below`: the same argument above a level `a`: a continuous `Φ` bounding the steps taken at or above
  `a`, with `Φ x < x` on `[a, h 0]`, sends the orbit below `a` at some step.

## 2. The self-similar step on a window reading (defined; consequences proved)

For a window reading `g : ℝ → ℕ → ℝ` (coupling, window index):

* `OneMap g Φ`: at every `β ≥ 0` and every window `w ≥ 1`, `g β (w+1) ≤ Φ (g β w)`. One map at every scale and
  every coupling.
* `NoFixedBelow g Φ`: `Φ 0 ≤ 0`, and `Φ x < x` for every `x ∈ (0, g β 1]`, at every `β ≥ 0`. The range is swept
  from the first window, which is fixed in lattice units.
* `SelfSimilar g`: some continuous `Φ` with both.

* `tendsto_of_selfSimilar`: a nonnegative reading with `SelfSimilar` vanishes along the windows at every `β ≥ 0`.
* `antitone_of_selfSimilar`: it decreases from the first window at every `β ≥ 0`.
* `freeLimit_antitone`: if the readings at each window converge as `β → ∞` (the free limit of a fixed box), the
  limits decrease along the windows. This is a necessary condition of `SelfSimilar` that can be checked on the
  free theory alone.
* `le_map_of_joint_limit`, `lt_of_joint_limit`: if the readings at two neighbouring windows converge to one value
  `x₀` as `β → ∞`, then `x₀ ≤ Φ x₀`: the map does not lower the free value, and `NoFixedBelow` puts every
  first-window reading strictly below it. The map is marginal at the free end (asymptotic freedom), and
  `NoFixedBelow` asks for no fixed point strictly below it.

## 3. The Wilson window coupling (proved from one named input)

`WilsonSelfSimilar N := SelfSimilar (windowCoupling N)`, the named input.

* `basin_map` (proved): the map exists near the trivial point. Some continuous `Φ` with `Φ 0 = 0` and some
  `a > 0` bound every doubling whose reading is at most `a`, and `Φ x < x` on `(0, a]`
  (`CouplingTower.windowCoupling_succ_le`, from `DoublingSharp.rec_sharp`). `WilsonSelfSimilar` asks for the same
  map through the crossover, up to the first-window reading.
* `vanishing_of_wilsonSelfSimilar`: at every `β ≥ 0` the window coupling vanishes along the windows.
* `strongEnd_of_wilsonSelfSimilar`: `WilsonSelfSimilar N → StrongEnd N`, for `N ≠ 0`.
* `windowGap_of_wilsonSelfSimilar`: the periodic Clay gap at every `β ≥ 0`, for `2 ≤ N`.

## 4. Tests

* Circularity. `OneMap` compares the doubling defect of the torus of side `2^w` with that of side `2^{w+1}`
  only: two finite-volume partition functions at one coupling. It reads no correlation beyond a window and no
  gap. `NoFixedBelow` is a property of one real function `Φ`.
* Abelian. `not_selfSimilar_of_limit`: a nonnegative reading that converges to a positive value at one
  `β ≥ 0` is not self-similar; it covers an orbit that approaches a positive fixed value without reaching it.
  `oneMap_id_of_const`: a reading constant along the windows (a line of fixed points, the Coulomb phase of
  `U(1)`) has a scale-free map, the identity. `not_noFixedBelow_of_const`: what it lacks is `NoFixedBelow`, for
  every map that bounds it. So a reading with a positive Coulomb value fails the step at the fixed-point clause,
  and that clause carries the non-abelian content. The test is conditional: the tree does not compute an
  abelian window reading.
* Degenerate. `noFixedBelow_at_zero`: at `β = 0` the clause is empty (`windowCoupling_zero`), and
  `oneMap_at_zero` reads `0 ≤ Φ 0`; with `Φ 0 ≤ 0`, `Φ 0 = 0`. `selfSimilar_const_zero`: the ultralocal
  reading `g ≡ 0` is self-similar, so the step alone does not exclude the trivial theory; along a coupling tower
  the condition `g = u₀ > 0` does. Windows start at `w = 1` (side `2`), where `windowCoupling_nonneg` holds.
* Strength. `WilsonSelfSimilar` implies `StrongEnd`, and more: monotone decrease from the first window at every
  coupling, uniformly in `β` through `Φ`. It is a sufficient condition and is not shown equivalent to `StrongEnd`.
  The start window is fixed: with a start chosen per coupling inside the basin, the clause would be met by
  `basin_map` and would say no more than `StrongEnd`.

DERIVED (module-wide): `0` the trivial (ultralocal) fixed point, the limit of the reading and the signs; `1` the
least window index and the step; `2` the doubling and the least rank. Proof-internal constants: `1/1000` the
sharp seed of `DoublingSharp` and `250` its squaring constant, in `basin_map` and nowhere in a statement.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.SelfSimilarStep

open Filter Topology
open MassGap.CouplingTower (windowCoupling StrongEnd windowCoupling_nonneg windowCoupling_succ_le
  windowCoupling_zero)

/-! ## 1. One map along an orbit -/

/-- **An orbit under a map with no fixed point below its start stays below the start and decreases.**
DERIVED: `0` the trivial point and the signs; `1` the step. -/
theorem orbit_bound {Φ : ℝ → ℝ} {h : ℕ → ℝ} (hΦ0 : Φ 0 ≤ 0) (hnn : ∀ k, 0 ≤ h k)
    (hstep : ∀ k, h (k + 1) ≤ Φ (h k)) (hfix : ∀ x, 0 < x → x ≤ h 0 → Φ x < x) :
    (∀ k, h k ≤ h 0) ∧ Antitone h := by
  have hle : ∀ x, 0 ≤ x → x ≤ h 0 → Φ x ≤ x := by
    intro x hx0 hx
    rcases hx0.eq_or_lt with h0 | hpos
    · rw [← h0]; exact hΦ0
    · exact (hfix x hpos hx).le
  have hb : ∀ k, h k ≤ h 0 := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hstep k).trans ((hle _ (hnn k) ih).trans ih)
  exact ⟨hb, antitone_nat_of_succ_le fun k => (hstep k).trans (hle _ (hnn k) (hb k))⟩

/-- **An orbit under one continuous map with no fixed point below its start tends to `0`.**
DERIVED: `0` the trivial point, the limit and the signs; `1` the step. -/
theorem orbit_tendsto_zero {Φ : ℝ → ℝ} (hΦ : Continuous Φ) {h : ℕ → ℝ} (hΦ0 : Φ 0 ≤ 0)
    (hnn : ∀ k, 0 ≤ h k) (hstep : ∀ k, h (k + 1) ≤ Φ (h k))
    (hfix : ∀ x, 0 < x → x ≤ h 0 → Φ x < x) : Tendsto h atTop (𝓝 0) := by
  obtain ⟨hb, hanti⟩ := orbit_bound hΦ0 hnn hstep hfix
  have hbdd : BddBelow (Set.range h) := ⟨0, by rintro _ ⟨k, rfl⟩; exact hnn k⟩
  have hL := tendsto_atTop_ciInf hanti hbdd
  have hL0 : 0 ≤ ⨅ k, h k := le_ciInf hnn
  have hLM : (⨅ k, h k) ≤ h 0 := ciInf_le hbdd 0
  have hfixL : (⨅ k, h k) ≤ Φ (⨅ k, h k) := by
    have h1 : Tendsto (fun k => h (k + 1)) atTop (𝓝 (⨅ k, h k)) :=
      hL.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun k => Φ (h k)) atTop (𝓝 (Φ (⨅ k, h k))) := (hΦ.tendsto _).comp hL
    exact le_of_tendsto_of_tendsto' h1 h2 hstep
  have hzero : (⨅ k, h k) = 0 := by
    by_contra hne
    have hpos : 0 < ⨅ k, h k := lt_of_le_of_ne hL0 (Ne.symm hne)
    linarith [hfix _ hpos hLM]
  rw [hzero] at hL
  exact hL

/-- **Above a level, the orbit drops below it**: a continuous map bounding the steps taken at or above `a`, with
no fixed point in `[a, h 0]`, sends the orbit below `a`. DERIVED: `1` the step. -/
theorem orbit_drops_below {Φ : ℝ → ℝ} (hΦ : Continuous Φ) {h : ℕ → ℝ} {a : ℝ}
    (hstep : ∀ k, a ≤ h k → h (k + 1) ≤ Φ (h k)) (hfix : ∀ x, a ≤ x → x ≤ h 0 → Φ x < x) :
    ∃ k, h k < a := by
  by_contra hne
  push Not at hne
  have hb : ∀ k, h k ≤ h 0 := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hstep k (hne k)).trans ((hfix _ (hne k) ih).le.trans ih)
  have hanti : Antitone h :=
    antitone_nat_of_succ_le fun k => (hstep k (hne k)).trans (hfix _ (hne k) (hb k)).le
  have hbdd : BddBelow (Set.range h) := ⟨a, by rintro _ ⟨k, rfl⟩; exact hne k⟩
  have hL := tendsto_atTop_ciInf hanti hbdd
  have hLa : a ≤ ⨅ k, h k := le_ciInf hne
  have hLM : (⨅ k, h k) ≤ h 0 := ciInf_le hbdd 0
  have hfixL : (⨅ k, h k) ≤ Φ (⨅ k, h k) := by
    have h1 : Tendsto (fun k => h (k + 1)) atTop (𝓝 (⨅ k, h k)) :=
      hL.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun k => Φ (h k)) atTop (𝓝 (Φ (⨅ k, h k))) := (hΦ.tendsto _).comp hL
    exact le_of_tendsto_of_tendsto' h1 h2 fun k => hstep k (hne k)
  linarith [hfix _ hLa hLM]

/-! ## 2. The self-similar step on a window reading -/

/-- **One map at every scale**: at every `β ≥ 0` and window `w ≥ 1`, the doubling of the reading is bounded by
`Φ` of the reading. `Φ` depends on neither `w` nor `β`. DERIVED: `0` the sign of `β`; `1` the least window index
and the step. -/
def OneMap (g : ℝ → ℕ → ℝ) (Φ : ℝ → ℝ) : Prop :=
  ∀ β : ℝ, 0 ≤ β → ∀ w : ℕ, 1 ≤ w → g β (w + 1) ≤ Φ (g β w)

/-- **No fixed point below the first window**: `Φ 0 ≤ 0`, and `Φ x < x` on `(0, g β 1]` at every `β ≥ 0`.
DERIVED: `0` the trivial point and the signs; `1` the first window. -/
def NoFixedBelow (g : ℝ → ℕ → ℝ) (Φ : ℝ → ℝ) : Prop :=
  Φ 0 ≤ 0 ∧ ∀ β : ℝ, 0 ≤ β → ∀ x : ℝ, 0 < x → x ≤ g β 1 → Φ x < x

/-- **The self-similar step**: one continuous map at every scale, with no fixed point between the trivial point
and the first-window reading. -/
def SelfSimilar (g : ℝ → ℕ → ℝ) : Prop :=
  ∃ Φ : ℝ → ℝ, Continuous Φ ∧ OneMap g Φ ∧ NoFixedBelow g Φ

section Reading

variable {g : ℝ → ℕ → ℝ}

/-- **A self-similar reading vanishes along the windows** at every `β ≥ 0`.
DERIVED: `0` the limit and the signs; `1` the least window index. -/
theorem tendsto_of_selfSimilar (hnn : ∀ β : ℝ, 0 ≤ β → ∀ w : ℕ, 1 ≤ w → 0 ≤ g β w)
    (h : SelfSimilar g) {β : ℝ} (hβ : 0 ≤ β) : Tendsto (g β) atTop (𝓝 0) := by
  obtain ⟨Φ, hΦ, hmap, hΦ0, hfix⟩ := h
  have ho := orbit_tendsto_zero hΦ hΦ0 (h := fun k => g β (k + 1))
    (fun k => hnn β hβ (k + 1) (by omega))
    (fun k => hmap β hβ (k + 1) (by omega))
    (fun x hx hx' => hfix β hβ x hx (by simpa using hx'))
  exact (tendsto_add_atTop_iff_nat 1).mp ho

/-- **A self-similar reading decreases from the first window** at every `β ≥ 0`.
DERIVED: `0` the signs; `1` the first window. -/
theorem antitone_of_selfSimilar (hnn : ∀ β : ℝ, 0 ≤ β → ∀ w : ℕ, 1 ≤ w → 0 ≤ g β w)
    (h : SelfSimilar g) {β : ℝ} (hβ : 0 ≤ β) : Antitone fun k => g β (k + 1) := by
  obtain ⟨Φ, -, hmap, hΦ0, hfix⟩ := h
  exact (orbit_bound hΦ0 (h := fun k => g β (k + 1))
    (fun k => hnn β hβ (k + 1) (by omega))
    (fun k => hmap β hβ (k + 1) (by omega))
    (fun x hx hx' => hfix β hβ x hx (by simpa using hx'))).2

/-- **The free limits decrease along the windows**: if each window's reading converges as `β → ∞`, a
self-similar reading has non-increasing limits. A test on the free theory alone.
DERIVED: `0` the sign of `β`; `1` the first window and the step. -/
theorem freeLimit_antitone (hnn : ∀ β : ℝ, 0 ≤ β → ∀ w : ℕ, 1 ≤ w → 0 ≤ g β w)
    (h : SelfSimilar g) {x : ℕ → ℝ} (hx : ∀ k, Tendsto (fun β => g β (k + 1)) atTop (𝓝 (x k))) :
    Antitone x := by
  refine antitone_nat_of_succ_le fun k => le_of_tendsto_of_tendsto (hx (k + 1)) (hx k) ?_
  filter_upwards [eventually_ge_atTop 0] with β hβ
  exact antitone_of_selfSimilar hnn h hβ (Nat.le_succ k)

/-- **The map does not lower the free value**: if the readings at windows `w` and `w + 1` converge to one
value `x₀` as `β → ∞`, then `x₀ ≤ Φ x₀`. DERIVED: `0` the sign of `β`; `1` the least window index and the
step. -/
theorem le_map_of_joint_limit {Φ : ℝ → ℝ} (hΦ : Continuous Φ) (hmap : OneMap g Φ) {w : ℕ} (hw : 1 ≤ w)
    {x₀ : ℝ} (h1 : Tendsto (fun β => g β w) atTop (𝓝 x₀))
    (h2 : Tendsto (fun β => g β (w + 1)) atTop (𝓝 x₀)) : x₀ ≤ Φ x₀ := by
  refine le_of_tendsto_of_tendsto h2 ((hΦ.tendsto x₀).comp h1) ?_
  filter_upwards [eventually_ge_atTop 0] with β hβ
  exact hmap β hβ w hw

/-- **Every first-window reading lies below a positive free value**: with `OneMap` and `NoFixedBelow`, a
positive joint limit `x₀` of two neighbouring windows exceeds `g β 1` at every `β ≥ 0`.
DERIVED: `0` the signs; `1` the first window and the step. -/
theorem lt_of_joint_limit {Φ : ℝ → ℝ} (hΦ : Continuous Φ) (hmap : OneMap g Φ) (hfix : NoFixedBelow g Φ)
    {w : ℕ} (hw : 1 ≤ w) {x₀ : ℝ} (hx₀ : 0 < x₀) (h1 : Tendsto (fun β => g β w) atTop (𝓝 x₀))
    (h2 : Tendsto (fun β => g β (w + 1)) atTop (𝓝 x₀)) {β : ℝ} (hβ : 0 ≤ β) : g β 1 < x₀ := by
  by_contra hle
  push Not at hle
  have := hfix.2 β hβ x₀ hx₀ hle
  linarith [le_map_of_joint_limit hΦ hmap hw h1 h2]

/-- **Abelian test: a reading with a positive limit is not self-similar.** If at one `β ≥ 0` the reading
converges to `L > 0` (a Coulomb fixed value, reached or only approached), no continuous scale-free map without
fixed points below the first window bounds it. DERIVED: `0` the signs and the limit. -/
theorem not_selfSimilar_of_limit (hnn : ∀ β : ℝ, 0 ≤ β → ∀ w : ℕ, 1 ≤ w → 0 ≤ g β w) {β : ℝ}
    (hβ : 0 ≤ β) {L : ℝ} (hL : 0 < L) (hlim : Tendsto (g β) atTop (𝓝 L)) : ¬ SelfSimilar g :=
  fun h => hL.ne' (tendsto_nhds_unique hlim (tendsto_of_selfSimilar hnn h hβ))

/-- **A line of fixed points has a scale-free map**: a reading constant along the windows is bounded by the
identity at every scale. What fails for it is `NoFixedBelow`, not `OneMap`. -/
theorem oneMap_id_of_const {c : ℝ → ℝ} (hc : ∀ β w, g β w = c β) : OneMap g id := by
  intro β _ w _
  simp [hc]

/-- **Abelian test: a positive line of fixed points has no map without fixed points below it.** If the reading
is constant along the windows at every coupling and positive at one `β ≥ 0`, no map bounding it meets
`NoFixedBelow`. DERIVED: `0` the signs; `1` the first window. -/
theorem not_noFixedBelow_of_const {c : ℝ → ℝ} (hc : ∀ β w, g β w = c β) {Φ : ℝ → ℝ} (hmap : OneMap g Φ)
    {β : ℝ} (hβ : 0 ≤ β) (hpos : 0 < c β) : ¬ NoFixedBelow g Φ := by
  rintro ⟨-, hfix⟩
  have h1 := hmap β hβ 1 le_rfl
  have h2 := hfix β hβ (c β) hpos (hc β 1).ge
  rw [hc, hc] at h1
  linarith

end Reading

/-- **The ultralocal reading is self-similar**: `g ≡ 0` with `Φ = 0`. The step alone does not exclude the
trivial theory. DERIVED: `0` the trivial point. -/
theorem selfSimilar_const_zero : SelfSimilar fun _ _ => 0 := by
  refine ⟨fun _ => 0, continuous_const, fun _ _ _ _ => le_rfl, le_rfl, ?_⟩
  intro β _ x hx hle
  exact absurd hle (not_le.mpr hx)

/-! ## 3. The Wilson window coupling -/

/-- **The self-similar step of the Wilson window coupling** (the named input): one continuous map, independent
of the scale and the coupling, bounds every doubling of the periodic Wilson torus defect, and has no fixed point
between `0` and the first-window reading. -/
def WilsonSelfSimilar (N : ℕ) : Prop := SelfSimilar (windowCoupling N)

variable {N : ℕ}

/-- DERIVED: `0` the signs; `1` the least window index. -/
theorem windowCoupling_nonneg' (hN : N ≠ 0) :
    ∀ β : ℝ, 0 ≤ β → ∀ w : ℕ, 1 ≤ w → 0 ≤ windowCoupling N β w :=
  fun _ hβ _ hw => windowCoupling_nonneg hN hβ hw

/-- **The map exists near the trivial point** (proved): some continuous `Φ` with `Φ 0 = 0` and some `a > 0`
bound every doubling of a reading at most `a`, at every `β ≥ 0` and window `w ≥ 1`, and `Φ x < x` on `(0, a]`.
DERIVED: `0` the trivial point and the signs; `1` the least window index and the step. -/
theorem basin_map (hN : N ≠ 0) :
    ∃ Φ : ℝ → ℝ, Continuous Φ ∧ Φ 0 = 0 ∧ ∃ a : ℝ, 0 < a ∧
      (∀ β : ℝ, 0 ≤ β → ∀ w : ℕ, 1 ≤ w → windowCoupling N β w ≤ a →
        windowCoupling N β (w + 1) ≤ Φ (windowCoupling N β w)) ∧
      ∀ x : ℝ, 0 < x → x ≤ a → Φ x < x := by
  refine ⟨fun x => 250 * x ^ 2, continuous_const.mul (continuous_pow 2), by simp, 1 / 1000,
    by norm_num, fun β hβ w hw h => windowCoupling_succ_le hN hβ hw h, ?_⟩
  intro x hx hxa
  nlinarith [mul_pos hx (show (0 : ℝ) < 1 - 250 * x by linarith)]

/-- **The self-similar step makes the window coupling vanish at every `β ≥ 0`.**
DERIVED: `0` the limit, the excluded rank and the signs. -/
theorem vanishing_of_wilsonSelfSimilar (hN : N ≠ 0) (h : WilsonSelfSimilar N) {β : ℝ} (hβ : 0 ≤ β) :
    Tendsto (windowCoupling N β) atTop (𝓝 0) :=
  tendsto_of_selfSimilar (windowCoupling_nonneg' hN) h hβ

/-- **The self-similar step gives the strong end.** DERIVED: `0` the excluded rank. -/
theorem strongEnd_of_wilsonSelfSimilar (hN : N ≠ 0) (h : WilsonSelfSimilar N) : StrongEnd N :=
  (StrongEndVanishing.strongEnd_iff_vanishing hN).mpr
    ((eventually_ge_atTop 0).mono fun _ hβ => vanishing_of_wilsonSelfSimilar hN h hβ).frequently

/-- **The self-similar step gives the periodic Clay gap at every `β ≥ 0`.** DERIVED: `2` the least rank; `0` the
plane, the time axis and the signs; `1` the upper end of the rate interval. -/
theorem windowGap_of_wilsonSelfSimilar (hN2 : 2 ≤ N) (hN : N ≠ 0) (h : WilsonSelfSimilar N) {β : ℝ}
    (hβ : 0 ≤ β) : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ PeriodicContent.PeriodicClayGapAt 0 0 hN β r :=
  StrongEndVanishing.windowGap_of_vanishing hN2 hN hβ (vanishing_of_wilsonSelfSimilar hN h hβ)

/-- **Degenerate test at `β = 0`**: the fixed-point clause reads nothing there. DERIVED: `0` the ultralocal
coupling and the signs; `1` the first window. -/
theorem noFixedBelow_at_zero (x : ℝ) (hx : 0 < x) : ¬ x ≤ windowCoupling N 0 1 := by
  rw [windowCoupling_zero]
  exact not_le.mpr hx

/-- **Degenerate test at `β = 0`**: the step reads `0 ≤ Φ 0`. DERIVED: `0` the ultralocal coupling; `1` the
least window index and the step. -/
theorem oneMap_at_zero {Φ : ℝ → ℝ} (h : OneMap (windowCoupling N) Φ) : 0 ≤ Φ 0 := by
  have := h 0 le_rfl 1 le_rfl
  rwa [windowCoupling_zero, windowCoupling_zero] at this

end MassGap.SelfSimilarStep

#print axioms MassGap.SelfSimilarStep.orbit_bound
#print axioms MassGap.SelfSimilarStep.orbit_tendsto_zero
#print axioms MassGap.SelfSimilarStep.orbit_drops_below
#print axioms MassGap.SelfSimilarStep.tendsto_of_selfSimilar
#print axioms MassGap.SelfSimilarStep.antitone_of_selfSimilar
#print axioms MassGap.SelfSimilarStep.freeLimit_antitone
#print axioms MassGap.SelfSimilarStep.le_map_of_joint_limit
#print axioms MassGap.SelfSimilarStep.lt_of_joint_limit
#print axioms MassGap.SelfSimilarStep.not_selfSimilar_of_limit
#print axioms MassGap.SelfSimilarStep.oneMap_id_of_const
#print axioms MassGap.SelfSimilarStep.not_noFixedBelow_of_const
#print axioms MassGap.SelfSimilarStep.selfSimilar_const_zero
#print axioms MassGap.SelfSimilarStep.windowCoupling_nonneg'
#print axioms MassGap.SelfSimilarStep.basin_map
#print axioms MassGap.SelfSimilarStep.vanishing_of_wilsonSelfSimilar
#print axioms MassGap.SelfSimilarStep.strongEnd_of_wilsonSelfSimilar
#print axioms MassGap.SelfSimilarStep.windowGap_of_wilsonSelfSimilar
#print axioms MassGap.SelfSimilarStep.noFixedBelow_at_zero
#print axioms MassGap.SelfSimilarStep.oneMap_at_zero
