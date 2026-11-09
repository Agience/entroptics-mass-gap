import Mathlib
import MassGap.StrongAnchor
import MassGap.SelfSimilarStep

/-!
# MassGap.ZoomStep — one doubling of the box as a step down in the coupling

At large `β` the lattice is zoomed in. Asymptotic freedom (antiscreening) says that one doubling of the box reads
like the same box at a smaller coupling. This module states that step on the window coupling
`D(β, w) = CouplingTower.windowCoupling N β w` as one inter-coupling comparison, proves that finitely many steps
walk a coupling into the proved strong anchor and so give the vanishing read there, and tests the step on the
stall witness, on a free massive-type family and on the converse. Declarations are in the namespace
`MassGap.ZoomStep`.

## 1. The zoom path (defined; consequences proved, abstract)

For a reading `g : ℝ → ℕ → ℝ` (coupling, window index):

* `ZoomPath g βs`: a sequence of couplings `βs k ≥ 0` with `g (βs k) (w + 1) ≤ g (βs (k + 1)) w` at every window
  `w ≥ 1`. One doubling at `βs k` reads at most what the undoubled box reads at `βs (k + 1)`.
* `Reaches βs`: the couplings come below every `ε > 0`. No threshold: the anchor's edge is existential, so the path
  is asked to come below all of them.
* `ZoomReachOf g β`: a zoom path from `β` that reaches.
* `path_le` (window bookkeeping): `g (βs 0) (w + k) ≤ g (βs k) w` at every `w ≥ 1`. The window `w + k ≥ 1` at the
  start is read against the window `w ≥ 1` at the `k`-th coupling; no window below `1` is read.
* `tendsto_of_path`: if the reading vanishes along the windows at `βs k`, it vanishes at `βs 0` (a squeeze; no
  seed and no basin constant enter).
* `tendsto_of_reach`: a nonnegative reading with an anchor (vanishing on `[0, b)`, `b > 0`) vanishes at every
  coupling that has a reaching zoom path.

## 2. The structural form: one map with no fixed point above `0`

* `ZoomStepMap g φ`: `φ ≥ 0` on `β ≥ 0`, and `g β (w + 1) ≤ g (φ β) w` at every `β ≥ 0` and `w ≥ 1`. `φ` is the
  effective coupling after one doubling.
* `NoFixedAbove φ`: `φ` continuous and `φ x < x` for every `x > 0`. No step size, no rate and no
  monotonicity of `φ` is asked; the step may shrink to `0` at `0` (asymptotic freedom puts the marginal point at
  `β = ∞`, not here). `map_zero_le` derives `φ 0 ≤ 0` from it.
* `zoomPath_of_map`, `reaches_of_noFixedAbove` (through `SelfSimilarStep.orbit_tendsto_zero`, reused):
  the iterates `φ^[k] β` form a zoom path that reaches. `zoomReachOf_of_map`: so every `β ≥ 0` has one.

## 3. Tests

* Stall witness. `stall_traps`: for a reading equal to a constant `c > 0` at every window on a ray `[b₀, ∞)` and
  vanishing along the windows on `[0, b₀)` (the deconfined-centre stall of the map, `D ≡ 45 log N` on the ray),
  every zoom path that starts on the ray stays on it: a step into `[0, b₀)` would read `c` at a doubling against a
  reading that tends to `0`. `stall_not_reach`, `stall_not_frequently`: no coupling on the ray has a reaching zoom
  path, for any path and so for any map `φ`; the named input fails on the witness. `stall_path_const`: the
  comparison clause alone is met there (the constant path, `φ = id`); what fails is the reach. `stallToy`
  (CHOSEN `b₀ = 1`, `c = 1`) is one such reading.
* Free massive-type family. `massiveToy β w = exp(−2^w · 2^{−β})`, a massive read at the window with mass
  `2^{−β}` in lattice units (CHOSEN profile, base `2` to match the doubling). `massiveToy_step`: it meets
  `ZoomStepMap` with `unitShift β = max (β − 1) 0` (the step `1` is DERIVED from the base-`2` profile: doubling the
  side is the mass halving). `unitShift_noFixedAbove`, `massiveToy_zoomReach`: every `β ≥ 0` has a reaching path.
* Converse. `bumpToy β w = 1` at `w = 2` and `0` elsewhere (CHOSEN). `bump_vanishing_not_reach`: it vanishes along
  the windows at every coupling, so it meets the abstract `StrongEnd`, while no zoom path exists from any
  coupling (the step at `w = 1` reads `1 ≤ 0`). So on abstract readings the vanishing read, at every coupling,
  does not give the zoom step.

## 4. The Wilson window coupling (proved from one named input)

* `ZoomReach N := ∃ᶠ β in atTop, ZoomReachOf (windowCoupling N) β`, the named input in its weakest form here:
  the comparison is asked only along the paths, and the paths only from frequently-large couplings.
* `WilsonZoomStep N := ∃ φ, ZoomStepMap (windowCoupling N) φ ∧ NoFixedAbove φ`, the structural form.
* `vanishes_of_zoomReachOf`: a reaching zoom path from `β` gives `StrongAnchor.Vanishes N β`, from
  `StrongAnchor.strongAnchor`, `CouplingTower.windowCoupling_nonneg` and `tendsto_of_reach`.
* `strongEnd_of_zoomReach`: `ZoomReach N → StrongEnd N`.
* `zoomReach_of_wilsonZoomStep`, `vanishes_of_wilsonZoomStep`, `strongEnd_of_wilsonZoomStep`: the structural form
  gives `ZoomReach N` and the vanishing read at every `β ≥ 0`.
* `zoomReachOf_zero` (degenerate): at `β = 0` the constant path at `0` reaches, since `D(0, ·) = 0`.

## Strength

`ZoomReach N` implies `StrongEnd N`, so it is at least as strong. On abstract readings it is strictly stronger
(`bump_vanishing_not_reach`). For the Wilson window coupling neither direction of the converse is decided:
`StrongEnd N ⇒ ZoomReach N` is not proved and not refuted. `WilsonZoomStep N` implies `ZoomReach N`, so it is at least as strong; strictness is not shown. It gives
the vanishing read at every `β ≥ 0`, which also excludes stalls at intermediate couplings (it implies
`StrongAnchor.NoStall` through `noStall_iff`; that link is not stated here). Neither `ZoomReach N` nor
`WilsonZoomStep N` is proved for `SU(N)`; each is a named open input. The comparison is one-sided, so
`RunningCrossover.not_exactCovariant` (no exact covariance `D = H(β − w c)` through `β = 0`) does not apply to it.

## What does not follow

* `ZoomReach N` or `WilsonZoomStep N` for the Wilson measure. No proved fact about `D` compares two couplings at
  shifted windows; the sweep found none in the tree or in its history. The nearest are the value map
  `SelfSimilarStep.OneMap` (one coupling), the covariance band `RunningCrossover.stepDropOn_of_covariantOn` and the
  one-loop shift `RunningCrossover.aOneG_sub_step` (spacing, not `D`).
* `StrongEnd N ⇒ ZoomReach N`: refuted on abstract readings; open for the Wilson window coupling.
* Any step size: `NoFixedAbove` asks no uniform drop, and the tests do not bound `φ β − β` for the Wilson reading.

DERIVED (module-wide): `0` the trivial coupling, the limit and the signs; `1` the least window index and the
step in the window index; `2` the doubling. CHOSEN (tests only): `stallToy` (`b₀ = 1`, `c = 1`), the profile
`2^{−β}` of `massiveToy`, and `bumpToy` (the window `2` and the value `1`). Inherited: none in a statement.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.ZoomStep

open Filter Topology
open MassGap.CouplingTower (windowCoupling StrongEnd windowCoupling_nonneg windowCoupling_zero)
open MassGap.StrongAnchor (Vanishes Anchor strongAnchor)

/-! ## 1. The zoom path -/

/-- **A zoom path**: couplings `βs k ≥ 0` such that one doubling at `βs k` reads at most the undoubled window at
`βs (k + 1)`, at every window `w ≥ 1`. DERIVED: `0` the sign of the coupling; `1` the least window index and the
step. -/
def ZoomPath (g : ℝ → ℕ → ℝ) (βs : ℕ → ℝ) : Prop :=
  (∀ k, 0 ≤ βs k) ∧ ∀ k w : ℕ, 1 ≤ w → g (βs k) (w + 1) ≤ g (βs (k + 1)) w

/-- **The path reaches the trivial coupling**: it comes below every `ε > 0`. DERIVED: `0` the trivial
coupling. -/
def Reaches (βs : ℕ → ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∃ k, βs k < ε

/-- **A reaching zoom path from `β`.** DERIVED: `0` the start index. -/
def ZoomReachOf (g : ℝ → ℕ → ℝ) (β : ℝ) : Prop :=
  ∃ βs : ℕ → ℝ, βs 0 = β ∧ ZoomPath g βs ∧ Reaches βs

section Reading

variable {g : ℝ → ℕ → ℝ}

/-- **Window bookkeeping**: `k` steps compare the window `w + k` at the start with the window `w` at the `k`-th
coupling. DERIVED: `0` the start; `1` the least window index and the step. -/
theorem path_le {βs : ℕ → ℝ} (h : ZoomPath g βs) :
    ∀ k w : ℕ, 1 ≤ w → g (βs 0) (w + k) ≤ g (βs k) w := by
  intro k
  induction k with
  | zero => intro w _; simp
  | succ k ih =>
    intro w hw
    have h1 := ih (w + 1) (by omega)
    have h2 := h.2 k w hw
    rw [show w + (k + 1) = w + 1 + k by omega]
    exact h1.trans h2

/-- **Vanishing passes back along a path**: a reading nonnegative at the start that vanishes along the windows
at `βs k` vanishes at `βs 0`. DERIVED: `0` the limit and the signs; `1` the least window index. -/
theorem tendsto_of_path {βs : ℕ → ℝ} (hnn : ∀ w : ℕ, 1 ≤ w → 0 ≤ g (βs 0) w) (h : ZoomPath g βs) (k : ℕ)
    (hk : Tendsto (g (βs k)) atTop (𝓝 0)) : Tendsto (g (βs 0)) atTop (𝓝 0) := by
  have hs : Tendsto (fun w => g (βs 0) (w + k)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hk ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with w hw
      exact hnn (w + k) (by omega)
    · filter_upwards [eventually_ge_atTop 1] with w hw
      exact path_le h k w hw
  exact (tendsto_add_atTop_iff_nat k).mp hs

/-- **A reaching zoom path walks into the anchor**: a nonnegative reading that vanishes on `[0, b)` for some
`b > 0` vanishes at every coupling with a reaching zoom path. DERIVED: `0` the limit and the signs; `1` the least
window index. -/
theorem tendsto_of_reach (hnn : ∀ β : ℝ, 0 ≤ β → ∀ w : ℕ, 1 ≤ w → 0 ≤ g β w)
    (hanc : Anchor fun β => Tendsto (g β) atTop (𝓝 0)) {β : ℝ} (h : ZoomReachOf g β) :
    Tendsto (g β) atTop (𝓝 0) := by
  obtain ⟨b, hb, hV⟩ := hanc
  obtain ⟨βs, h0, hp, hr⟩ := h
  obtain ⟨k, hk⟩ := hr b hb
  have := tendsto_of_path (fun w hw => hnn _ (hp.1 0) w hw) hp k (hV _ (hp.1 k) hk)
  rwa [h0] at this

/-! ## 2. The structural form -/

/-- **The zoom step as a map**: `φ β ≥ 0`, and one doubling at `β` reads at most the undoubled window at `φ β`,
at every `β ≥ 0` and `w ≥ 1`. DERIVED: `0` the signs; `1` the least window index and the step. -/
def ZoomStepMap (g : ℝ → ℕ → ℝ) (φ : ℝ → ℝ) : Prop :=
  (∀ β : ℝ, 0 ≤ β → 0 ≤ φ β) ∧ ∀ β : ℝ, 0 ≤ β → ∀ w : ℕ, 1 ≤ w → g β (w + 1) ≤ g (φ β) w

/-- **No fixed point above the trivial coupling**: `φ` continuous with `φ x < x` at every `x > 0`.
DERIVED: `0` the trivial coupling. -/
def NoFixedAbove (φ : ℝ → ℝ) : Prop := Continuous φ ∧ ∀ x : ℝ, 0 < x → φ x < x

/-- DERIVED: `0` the trivial coupling. -/
theorem map_zero_le {φ : ℝ → ℝ} (h : NoFixedAbove φ) : φ 0 ≤ 0 := by
  have h1 : Tendsto φ (𝓝[>] (0 : ℝ)) (𝓝 (φ 0)) := (h.1.tendsto 0).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  exact le_of_tendsto_of_tendsto h1 h2
    (eventually_nhdsWithin_of_forall fun x (hx : 0 < x) => (h.2 x hx).le)

/-- DERIVED: `0` the signs and the start. -/
theorem orbit_nonneg {φ : ℝ → ℝ} (hφ : ∀ β : ℝ, 0 ≤ β → 0 ≤ φ β) {β : ℝ} (hβ : 0 ≤ β) :
    ∀ k : ℕ, 0 ≤ φ^[k] β := by
  intro k
  induction k with
  | zero => exact hβ
  | succ k ih => rw [Function.iterate_succ_apply']; exact hφ _ ih

/-- **The iterates of the map are a zoom path.** DERIVED: `0` the sign of `β`. -/
theorem zoomPath_of_map {φ : ℝ → ℝ} (h : ZoomStepMap g φ) {β : ℝ} (hβ : 0 ≤ β) :
    ZoomPath g fun k => φ^[k] β :=
  ⟨orbit_nonneg h.1 hβ, fun k w hw => by
    simp only [Function.iterate_succ_apply']
    exact h.2 _ (orbit_nonneg h.1 hβ k) w hw⟩

/-- **The iterates reach the trivial coupling** (through `SelfSimilarStep.orbit_tendsto_zero`).
DERIVED: `0` the limit and the signs. -/
theorem reaches_of_noFixedAbove {φ : ℝ → ℝ} (hφ : ∀ β : ℝ, 0 ≤ β → 0 ≤ φ β) (hfix : NoFixedAbove φ)
    {β : ℝ} (hβ : 0 ≤ β) : Reaches fun k => φ^[k] β := by
  have ht : Tendsto (fun k => φ^[k] β) atTop (𝓝 0) :=
    SelfSimilarStep.orbit_tendsto_zero hfix.1 (map_zero_le hfix) (orbit_nonneg hφ hβ)
      (fun k => by rw [Function.iterate_succ_apply']) (fun x hx _ => hfix.2 x hx)
  intro ε hε
  exact (ht.eventually (gt_mem_nhds hε)).exists

/-- **The structural step gives a reaching zoom path from every `β ≥ 0`.** DERIVED: `0` the sign of `β`. -/
theorem zoomReachOf_of_map {φ : ℝ → ℝ} (h : ZoomStepMap g φ) (hfix : NoFixedAbove φ) {β : ℝ} (hβ : 0 ≤ β) :
    ZoomReachOf g β :=
  ⟨fun k => φ^[k] β, rfl, zoomPath_of_map h hβ, reaches_of_noFixedAbove h.1 hfix hβ⟩

/-! ## 3. Tests on abstract readings -/

/-- **Stall witness: a zoom path that starts on the stall ray stays on it.** The reading is the constant
`c > 0` on `[b₀, ∞)` at every window and vanishes along the windows on `[0, b₀)`.
DERIVED: `0` the signs and the limit; `1` the least window index and the step. -/
theorem stall_traps {b₀ c : ℝ} (hc : 0 < c) (hstall : ∀ β : ℝ, b₀ ≤ β → ∀ w : ℕ, g β w = c)
    (hvan : ∀ β : ℝ, 0 ≤ β → β < b₀ → Tendsto (g β) atTop (𝓝 0)) {βs : ℕ → ℝ} (hp : ZoomPath g βs)
    (h0 : b₀ ≤ βs 0) : ∀ k : ℕ, b₀ ≤ βs k := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    by_contra hlt
    push Not at hlt
    have hT := hvan _ (hp.1 (k + 1)) hlt
    obtain ⟨w, hw, hw1⟩ := ((hT.eventually (gt_mem_nhds hc)).and (eventually_ge_atTop 1)).exists
    have hs := hp.2 k w hw1
    rw [hstall _ ih] at hs
    linarith

/-- **Stall witness: no coupling on the ray has a reaching zoom path**, whatever the path (so whatever the
map). DERIVED: `0` the signs. -/
theorem stall_not_reach {b₀ c : ℝ} (hb₀ : 0 < b₀) (hc : 0 < c)
    (hstall : ∀ β : ℝ, b₀ ≤ β → ∀ w : ℕ, g β w = c)
    (hvan : ∀ β : ℝ, 0 ≤ β → β < b₀ → Tendsto (g β) atTop (𝓝 0)) {β : ℝ} (hβ : b₀ ≤ β) :
    ¬ ZoomReachOf g β := by
  rintro ⟨βs, h0, hp, hr⟩
  obtain ⟨k, hk⟩ := hr b₀ hb₀
  have := stall_traps hc hstall hvan hp (by rw [h0]; exact hβ) k
  linarith

/-- **Stall witness: the named input fails** (frequently-large couplings have no reaching path).
DERIVED: `0` the signs. -/
theorem stall_not_frequently {b₀ c : ℝ} (hb₀ : 0 < b₀) (hc : 0 < c)
    (hstall : ∀ β : ℝ, b₀ ≤ β → ∀ w : ℕ, g β w = c)
    (hvan : ∀ β : ℝ, 0 ≤ β → β < b₀ → Tendsto (g β) atTop (𝓝 0)) :
    ¬ ∃ᶠ β in atTop, ZoomReachOf g β :=
  Filter.not_frequently.mpr
    ((eventually_ge_atTop b₀).mono fun _ hβ => stall_not_reach hb₀ hc hstall hvan hβ)

/-- **Stall witness: the comparison clause alone is met** on the ray, by the constant path (`φ = id`). What the
witness fails is the reach. DERIVED: `0` the sign of `β`; `1` the step. -/
theorem stall_path_const {b₀ c : ℝ} (hstall : ∀ β : ℝ, b₀ ≤ β → ∀ w : ℕ, g β w = c) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ : b₀ ≤ β) : ZoomPath g fun _ => β :=
  ⟨fun _ => hβ0, fun _ w _ => by rw [hstall β hβ, hstall β hβ]⟩

end Reading

/-- **A stall reading** (CHOSEN: edge `1`, stall value `1`): `0` below the edge, `1` on the ray. -/
def stallToy (β : ℝ) (_w : ℕ) : ℝ := if β < 1 then 0 else 1

/-- **The stall reading fails the named input.** CHOSEN: `1` the edge and the stall value. -/
theorem stallToy_not_frequently : ¬ ∃ᶠ β in atTop, ZoomReachOf stallToy β :=
  stall_not_frequently (b₀ := 1) (c := 1) one_pos one_pos
    (fun β hβ w => by simp [stallToy, not_lt.mpr hβ])
    (fun β _ hβ => by
      have e : stallToy β = fun _ => 0 := funext fun _ => by simp [stallToy, hβ]
      rw [e]; exact tendsto_const_nhds)

/-- **A free massive-type reading** (CHOSEN profile: mass `2^{−β}` in lattice units). -/
def massiveToy (β : ℝ) (w : ℕ) : ℝ := Real.exp (-((2 : ℝ) ^ w * (2 : ℝ) ^ (-β)))

/-- **The unit shift** `β ↦ max (β − 1) 0`. DERIVED: `1` the halving of the base-`2` mass per doubling; `0` the
trivial coupling. -/
def unitShift (β : ℝ) : ℝ := max (β - 1) 0

/-- **The free massive-type reading meets the zoom step with the unit shift.** DERIVED: `1` the step, `2` the
doubling. -/
theorem massiveToy_step : ZoomStepMap massiveToy unitShift := by
  refine ⟨fun β _ => le_max_right _ _, fun β _ w _ => ?_⟩
  have h1 : (2 : ℝ) ^ (-max (β - 1) 0) ≤ (2 : ℝ) ^ (1 - β) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by have := le_max_left (β - 1) 0; linarith)
  have h2 : (2 : ℝ) ^ (1 - β) = 2 * (2 : ℝ) ^ (-β) := by
    rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_one]
  have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ w := by positivity
  have h4 : (2 : ℝ) ^ w * (2 : ℝ) ^ (-max (β - 1) 0) ≤ (2 : ℝ) ^ (w + 1) * (2 : ℝ) ^ (-β) := by
    calc (2 : ℝ) ^ w * (2 : ℝ) ^ (-max (β - 1) 0) ≤ (2 : ℝ) ^ w * (2 : ℝ) ^ (1 - β) :=
          mul_le_mul_of_nonneg_left h1 h3
      _ = (2 : ℝ) ^ (w + 1) * (2 : ℝ) ^ (-β) := by rw [h2]; ring
  simp only [massiveToy, unitShift]
  exact Real.exp_le_exp.mpr (neg_le_neg h4)

/-- **The unit shift has no fixed point above `0`.** DERIVED: `1` the step; `0` the trivial coupling. -/
theorem unitShift_noFixedAbove : NoFixedAbove unitShift :=
  ⟨(continuous_id.sub continuous_const).max continuous_const,
    fun x hx => max_lt (by linarith) hx⟩

/-- **The free massive-type reading has a reaching zoom path from every `β ≥ 0`.** DERIVED: `0` the sign. -/
theorem massiveToy_zoomReach {β : ℝ} (hβ : 0 ≤ β) : ZoomReachOf massiveToy β :=
  zoomReachOf_of_map massiveToy_step unitShift_noFixedAbove hβ

/-- **A bump reading** (CHOSEN: value `1` at window `2`, `0` elsewhere). -/
def bumpToy (_β : ℝ) (w : ℕ) : ℝ := if w = 2 then 1 else 0

/-- **Converse test: vanishing at every coupling does not give the zoom step.** The bump vanishes along the
windows at every coupling, and no zoom path exists from any coupling. CHOSEN: the window `2` and the value `1`;
DERIVED: `1` the least window index. -/
theorem bump_vanishing_not_reach :
    (∀ β : ℝ, Tendsto (bumpToy β) atTop (𝓝 0)) ∧ ∀ β : ℝ, ¬ ZoomReachOf bumpToy β := by
  refine ⟨fun β => ?_, fun β => ?_⟩
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 3] with w hw
    simp only [bumpToy]
    rw [if_neg (by omega)]
  · rintro ⟨βs, -, hp, -⟩
    have := hp.2 0 1 le_rfl
    norm_num [bumpToy] at this

/-! ## 4. The Wilson window coupling -/

variable {N : ℕ}

/-- **The zoom step on the Wilson window coupling, path form** (the named open input): frequently as `β → ∞`,
a zoom path from `β` reaches the trivial coupling. -/
def ZoomReach (N : ℕ) : Prop := ∃ᶠ β in atTop, ZoomReachOf (windowCoupling N) β

/-- **The zoom step on the Wilson window coupling, structural form**: one effective-coupling map `φ` with no
fixed point above `0` bounds every doubling. -/
def WilsonZoomStep (N : ℕ) : Prop := ∃ φ : ℝ → ℝ, ZoomStepMap (windowCoupling N) φ ∧ NoFixedAbove φ

/-- **A reaching zoom path gives the vanishing read** (from the proved strong anchor). DERIVED: `0` the excluded
rank. -/
theorem vanishes_of_zoomReachOf (hN : N ≠ 0) {β : ℝ} (h : ZoomReachOf (windowCoupling N) β) :
    Vanishes N β :=
  tendsto_of_reach (fun _ hβ _ hw => windowCoupling_nonneg hN hβ hw) (strongAnchor hN) h

/-- **The zoom step gives the strong end.** DERIVED: `0` the excluded rank. -/
theorem strongEnd_of_zoomReach (hN : N ≠ 0) (h : ZoomReach N) : StrongEnd N :=
  h.mono fun _ hβ => vanishes_of_zoomReachOf hN hβ

/-- **The structural form gives the vanishing read at every `β ≥ 0`.** DERIVED: `0` the sign and the excluded
rank. -/
theorem vanishes_of_wilsonZoomStep (hN : N ≠ 0) (h : WilsonZoomStep N) {β : ℝ} (hβ : 0 ≤ β) :
    Vanishes N β := by
  obtain ⟨φ, hφ, hfix⟩ := h
  exact vanishes_of_zoomReachOf hN (zoomReachOf_of_map hφ hfix hβ)

/-- **The structural form gives the path form.** DERIVED: `0` the sign. -/
theorem zoomReach_of_wilsonZoomStep (h : WilsonZoomStep N) : ZoomReach N := by
  obtain ⟨φ, hφ, hfix⟩ := h
  exact ((eventually_ge_atTop 0).mono fun _ hβ => zoomReachOf_of_map hφ hfix hβ).frequently

/-- **The structural form gives the strong end.** DERIVED: `0` the excluded rank. -/
theorem strongEnd_of_wilsonZoomStep (hN : N ≠ 0) (h : WilsonZoomStep N) : StrongEnd N :=
  strongEnd_of_zoomReach hN (zoomReach_of_wilsonZoomStep h)

/-- **Degenerate test at `β = 0`**: the constant path at `0` reaches, since the window coupling is `0` there.
DERIVED: `0` the ultralocal coupling. -/
theorem zoomReachOf_zero : ZoomReachOf (windowCoupling N) 0 :=
  ⟨fun _ => 0, rfl, ⟨fun _ => le_rfl, fun _ w _ => by rw [windowCoupling_zero, windowCoupling_zero]⟩,
    fun _ hε => ⟨0, hε⟩⟩

end MassGap.ZoomStep

#print axioms MassGap.ZoomStep.path_le
#print axioms MassGap.ZoomStep.tendsto_of_path
#print axioms MassGap.ZoomStep.tendsto_of_reach
#print axioms MassGap.ZoomStep.map_zero_le
#print axioms MassGap.ZoomStep.orbit_nonneg
#print axioms MassGap.ZoomStep.zoomPath_of_map
#print axioms MassGap.ZoomStep.reaches_of_noFixedAbove
#print axioms MassGap.ZoomStep.zoomReachOf_of_map
#print axioms MassGap.ZoomStep.stall_traps
#print axioms MassGap.ZoomStep.stall_not_reach
#print axioms MassGap.ZoomStep.stall_not_frequently
#print axioms MassGap.ZoomStep.stall_path_const
#print axioms MassGap.ZoomStep.stallToy_not_frequently
#print axioms MassGap.ZoomStep.massiveToy_step
#print axioms MassGap.ZoomStep.unitShift_noFixedAbove
#print axioms MassGap.ZoomStep.massiveToy_zoomReach
#print axioms MassGap.ZoomStep.bump_vanishing_not_reach
#print axioms MassGap.ZoomStep.vanishes_of_zoomReachOf
#print axioms MassGap.ZoomStep.strongEnd_of_zoomReach
#print axioms MassGap.ZoomStep.vanishes_of_wilsonZoomStep
#print axioms MassGap.ZoomStep.zoomReach_of_wilsonZoomStep
#print axioms MassGap.ZoomStep.strongEnd_of_wilsonZoomStep
#print axioms MassGap.ZoomStep.zoomReachOf_zero
