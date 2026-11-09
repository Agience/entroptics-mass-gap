import Mathlib
import MassGap.ObserverFlowSeed
import MassGap.ObserverBlock

/-!
# MassGap.FlowComp — the bare–flowed comparison as one inequality between defects

`ObserverFlowSeed.runSeed_of_flowSeed` gives `WDeltaRun.RunSeed N` from the observer's flowed seed
`ObsRunSeedFlowW hN W κ C δ` and the comparison `FlowEnergyComp hN W κ C K η`. This module puts both on the
integrated readings, splits the comparison into a flowed part and a remainder observable, and records what each
split does and does not carry.

## 1. Budgets are integrals (proved)

* `continuous_torusState`: `x ↦ torusState hN M x f` is continuous in the coupling
  (`WilsonAnalytic.wilsonSystem_expect_hasDerivAt`); hence `bareDelta hN n` and `flowDelta hN W k n` are
  continuous (`continuous_bareDelta`, `continuous_flowDelta`).
* **`budget_iff_integral`**: for continuous `g` and `0 ≤ β`, `Budget β η g ↔ ∫₀^β g ≤ η`
  (`budget_of_integral` takes `Φ = ∫₀^· g`; `integral_le_of_budget` is
  `intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le`). A budget carries no pointwise content beyond
  its integral.
* `integral_bareDelta`: `∫₀^β bareDelta hN n = defectW N β n` at `n ≠ 0`.
* `flowDefect hN W k n β = ∫₀^β flowDelta hN W k n`, the flowed defect.
* **`flowEnergyComp_iff_defect`**: `FlowEnergyComp hN W κ C K η` iff eventually in `β`, at every side `n` in
  the window, `defectW N β n − K · flowDefect hN W (κ β) n β ≤ η`.
* **`obsRunSeedFlowW_iff_defect`**: `ObsRunSeedFlowW hN W κ C δ` iff eventually some side in the window has
  `flowDefect hN W (κ β) n β ≤ δ`.
* `inWin_unique`: at `β > 0` the window holds at most one side (powers of two within a factor `2`), so "every
  side in the window" in `FlowEnergyComp` is the one side the seed uses.

So the pair (flowed seed, comparison) is `D ≤ K F + η` and `F ≤ δ` for the bare defect `D` and the flowed
defect `F` at one side: the comparison is one inequality between two numbers per `β`.

## 2. The coupling split (proved)

* `budget_split`: integrals on `[0, x₀]` and `[x₀, β]` add.
* **`flowEnergyComp_of_split`**: for a fixed `x₀`, the strong part `defectW N x₀ n − K · flowDefect hN W (κ β) n x₀
  ≤ η₁` and the scaling part `∫_{x₀}^β (bareDelta − K flowDelta) ≤ η₂`, both eventually in `β` at the side in
  the window, give `FlowEnergyComp hN W κ C K (η₁ + η₂)`.

The strong part is read at the fixed coupling `x₀` while the side `n` in the window `C/2 < n · aRun N β ≤ C`
grows. At `x₀ = 2^{-16}` it is proved in `StrongLocalFiniteSize.strongPart_of_reach`, for any `K` and `η₁ > 0`,
given a reach hypothesis on the flow at its step: `2 (W.range (κ β) + 1) ≤ θ n` with `θ < 1` at every window
side. For a flow of lattice range at most `s / aRun N β` this holds eventually once `4 s < θ C`.

## 3. The remainder observable (proved)

* `remRead hN W k n β = ∑_p torusState hN (n−1) β (φ_p − φ_p ∘ V_k)` at the origin, with
  `bareRead = flowRead + remRead` (`bareRead_eq_flowRead_add_remRead`, linearity of the torus state) and
  `remDelta = bareDelta − flowDelta` (`remDelta_eq`).
* `flowEnergyComp_one_iff`: at `K = 1` the comparison is the budget `η` of the remainder's doubling change.
* `RemControl hN W κ C K' η'`: eventually, at the side in the window, `remDelta − K' · bareDelta` is within a
  budget `η'`: the finite-size change of the reach-`r` remainder observable controlled by that of the
  plaquette.
* **`flowEnergyComp_iff_remControl`**: at `K > 0`,
  `FlowEnergyComp hN W κ C K η ↔ RemControl hN W κ C (1 − K⁻¹) (η / K)`, from the identity
  `bareDelta − K flowDelta = K (remDelta − (1 − K⁻¹) bareDelta)`.

So "the finite-size effect of the remainder observable is controlled by that of the plaquette" is the
comparison itself, rescaled. For the one observable `φ_p − φ_p ∘ V` it discharges nothing. A reduction with
content needs a statement uniform over a class of observables that is proved for some other member of the
class (§ Analysis).

## 4. Per-site closeness: a growing budget (proved)

* `abs_remRead_le`, `remDelta_le`: if `|φ_p − φ_p ∘ V_k| ≤ ε` pointwise for every ordered direction pair and every step, then
  `|remRead| ≤ 16 ε` and `remDelta ≤ 512 ε n⁴`.
* `flowEnergyComp_one_of_closeness`: then `FlowEnergyComp hN W κ C 1 η` holds once `512 ε n⁴ β ≤ η` at the side
  in the window. With `n > C/(2 aRun N β)` growing and `ε` fixed by the smearing weight, `512 ε n⁴ β` grows
  without bound: per-site closeness alone gives the comparison with the budget `512 ε n⁴ β` (proved); argued:
  no per-site argument cancels the extensive error `16 n⁴ · ε` in the doubling change, so `η` is not fixed
  before `β`.

## 5. The degenerate case: a flow that is the identity at the observer's step (proved)

* `flowEnergyComp_of_eventually_id`: if eventually `W.V (κ β) = id`, the comparison holds at `K = 1`, `η = 0`.
* `flowEnergyComp_blFam_coarse`: `ObserverBlock.blFam` satisfies it at any step choice `κ` with eventually
  `s < 2 m · dySpacing N (κ β)` (`ObserverBlock.blFam_V_of_lt`). There the observer's aperture `s` is below
  two coarse spacings and the flow does nothing; the flowed seed is then the bare seed. This is the degenerate
  end, not the observer's working regime (`blFam_not_eventually_id`: at the step matching `aRun N β → 0` the
  flow moves configurations).

## Analysis of the open comparison (argued, not declarations)

* By §1 and §3 the content of `FlowEnergyComp` at `K > 0` is `D − K F ≤ η` for the bare and flowed defects at
  the one window side. `defectW ≥ 0` at even sides `n ≥ 2`, `β ≥ 0` (`DoublingRecursion.Δ_nonneg` applied to `DoublingWilson.positive`, with `DoublingWilson.Δ_corner0`), so it forces
  `F ≥ −η/K`; with the flowed seed, `−η/K ≤ F ≤ δ` and `D ≤ K δ + η`.
* Growing-quantity test with `K`, `η` fixed before `β` and the window. At a fixed lattice step (`κ` bounded) the
  flow's reach is fixed in lattice units and both changes, in the scaling regime, are the finite-size change
  of `⟨F²⟩` times operator coefficients: `flowDelta ≈ λ(x) bareDelta` with `λ(x) → λ_∞` as `x → ∞`. With
  `K = 1/λ_∞` the excess is `O(g²(x))` times a change whose integral is the bounded defect, so any fixed `η > 0`
  is met eventually: no growing quantity. But then the flowed seed is the bare seed up to the factor `λ_∞`,
  since the flow's physical aperture tends to `0`. At a step matching the coupling (physical aperture `s`
  fixed, lattice reach `∝ 1/aRun N β`) the excess carries the dimension-six part of the flowed density, of
  relative size `(s/C)²`; this is bounded before `β` and must fit `η ≤ 1/1000 − K δ`, which requires `C ≫ s`.
* A uniform form with content: for every gauge-invariant local observable `O` of reach at most `r` and norm at
  most `1`, `16 n⁴ Δ_n⟨O⟩ − λ_O · bareDelta` within a budget `ε(r)` at the window side, with `ε(r)` fixed before
  `β`. At a matching step the reach `r` grows with `β`, so `ε` must be read at a physical reach, and the class
  must be closed under the flow; neither the statement nor its strong-coupling half is in the tree.

## What is open

The open input is `FlowEnergyComp` at `K > 0` for a flow that is not the identity at the observer's step,
equivalently (§1) `defectW N β n ≤ η + K · flowDefect hN W (κ β) n β` at the window side. §2's strong part
(finite-size effects at fixed coupling `x₀` vanish as the side grows) and scaling part
(`∫_{x₀}^β (bareDelta − K flowDelta) ≤ η₂` at `K = 1/λ_∞`) are one sufficient route; the strong part is proved at `x₀ = 2^{-16}` under the reach hypothesis
(`StrongLocalFiniteSize`), which holds for `ObserverBlock.blFam` at the step `FlowScalingOnly.obsStep`
(`FlowScalingOnly.reach_blFam`); there the strong part tends to `0` and the comparison is equivalent to its
scaling part, which is open.

DERIVED (module-wide): `4` the dimension; `16 = 2⁴` the copies of the side-`n` box in the side-`2n` box and the
count of ordered planes; `2` the doubling, the least side and the window's lower edge; `32 = 2 · 16` the two
readings of the doubling change; `512 = 16 · 32`; `0` the lower coupling, the origin and the excluded colour
count; `1` the unit comparison constant.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.FlowComp

open Real Filter Set
open MassGap MassGap.ObserverFlowSeed MassGap.ObserverRunSeed MassGap.EffectiveCoupling MassGap.EnergySeed
open MassGap.ZoomSelfScale
open MassGap.PeriodicState MassGap.ContinuumField MassGap.ContinuumFlow MassGap.ObserverEnergyMoments

variable {N : ℕ}

/-! ## 1. Budgets are integrals -/

/-- **The torus reading is continuous in the coupling.** DERIVED: `4` the dimension; `1` the successor writing
the extent. -/
theorem continuous_torusState (hN : N ≠ 0) (M : ℕ)
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    Continuous (fun x : ℝ => torusState hN M x f) := by
  obtain ⟨B, hB⟩ := MassGap.InfiniteLattice.bounded_of_continuous f.continuous
  refine continuous_iff_continuousAt.mpr fun β => ?_
  change ContinuousAt (fun x : ℝ => MassGap.ReflectPositive.EW (d := 4) (n := M + 1) N x (torusObs M f)) β
  exact (MassGap.WilsonAnalytic.wilsonSystem_expect_hasDerivAt hN
    (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1)) β (torusObs M f) (measurable_torusObs M f) B
    (fun W => hB _)).continuousAt

/-- The bare reading is continuous in the coupling. DERIVED: `4` the dimension; `1` the successor;
`0` the origin. -/
theorem continuous_bareRead (hN : N ≠ 0) (n : ℕ) : Continuous (bareRead hN n) := by
  change Continuous fun β => ∑ p : Fin 4 × Fin 4, torusState hN (n - 1) β (plaqField (N := N) (p, 0)).1
  exact continuous_finsetSum _ fun p _ => continuous_torusState hN (n - 1) _

/-- The flowed reading is continuous in the coupling. DERIVED: `4` the dimension; `1` the successor;
`0` the origin. -/
theorem continuous_flowRead (hN : N ≠ 0) (W : ConfFlow N) (k n : ℕ) : Continuous (flowRead hN W k n) := by
  change Continuous fun β =>
    ∑ p : Fin 4 × Fin 4, torusState hN (n - 1) β (W.fieldMap k (plaqField (N := N) (p, 0))).1
  exact continuous_finsetSum _ fun p _ => continuous_torusState hN (n - 1) _

/-- The bare doubling change is continuous in the coupling. DERIVED: `16 = 2⁴`; `2` the doubling;
`4` the dimension. -/
theorem continuous_bareDelta (hN : N ≠ 0) (n : ℕ) : Continuous (bareDelta hN n) := by
  change Continuous fun β => 16 * (n : ℝ) ^ 4 * (bareRead hN (2 * n) β - bareRead hN n β)
  exact continuous_const.mul ((continuous_bareRead hN _).sub (continuous_bareRead hN _))

/-- The flowed doubling change is continuous in the coupling. DERIVED: `16 = 2⁴`; `2` the doubling;
`4` the dimension. -/
theorem continuous_flowDelta (hN : N ≠ 0) (W : ConfFlow N) (k n : ℕ) : Continuous (flowDelta hN W k n) := by
  change Continuous fun β => 16 * (n : ℝ) ^ 4 * (flowRead hN W k (2 * n) β - flowRead hN W k n β)
  exact continuous_const.mul ((continuous_flowRead hN W k _).sub (continuous_flowRead hN W k _))

/-- **A continuous rate with total at most `η` is a budget `η`** (`Φ = ∫₀^· g`). DERIVED: `0` the lower
coupling. -/
theorem budget_of_integral {β η : ℝ} {g : ℝ → ℝ} (hg : Continuous g) (h : ∫ x in (0 : ℝ)..β, g x ≤ η) :
    Budget β η g :=
  ⟨fun y => ∫ x in (0 : ℝ)..y, g x, g, by simp, h,
    fun x _ => (hg.integral_hasStrictDerivAt 0 x).hasDerivAt, fun _ _ => le_rfl⟩

/-- **A budget bounds the integral of a continuous rate.** DERIVED: `0` the lower coupling. -/
theorem integral_le_of_budget {β η : ℝ} {g : ℝ → ℝ} (hβ : 0 ≤ β) (hg : Continuous g) (h : Budget β η g) :
    ∫ x in (0 : ℝ)..β, g x ≤ η := by
  obtain ⟨Φ, φ, h0, hΦβ, hd, hle⟩ := h
  have hI := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hβ
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (Ioo_subset_Icc_self hx)).hasDerivWithinAt)
    hg.integrableOn_Icc (fun x hx => hle x (Ioo_subset_Ico_self hx))
  rw [h0, sub_zero] at hI
  linarith

/-- **For a continuous rate a budget is its integral.** DERIVED: `0` the lower coupling. -/
theorem budget_iff_integral {β η : ℝ} {g : ℝ → ℝ} (hβ : 0 ≤ β) (hg : Continuous g) :
    Budget β η g ↔ ∫ x in (0 : ℝ)..β, g x ≤ η :=
  ⟨integral_le_of_budget hβ hg, budget_of_integral hg⟩

/-- **The integrated bare change is the defect.** DERIVED: `0` the lower coupling and the excluded side. -/
theorem integral_bareDelta (hN : N ≠ 0) {n : ℕ} (hn : n ≠ 0) (β : ℝ) :
    ∫ x in (0 : ℝ)..β, bareDelta hN n x = defectW N β n := by
  have hd : ∀ x ∈ uIcc (0 : ℝ) β, HasDerivAt (fun y => defectW N y n) (bareDelta hN n x) x :=
    fun x _ => by
      rw [← finiteSize_eq_bareDelta hN hn x]
      exact hasDerivAt_defectW' hN n x
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((continuous_bareDelta hN n).intervalIntegrable 0 β),
    defectW_zero, sub_zero]

/-- **The flowed defect**: the integrated flowed doubling change. DERIVED: `0` the lower coupling. -/
def flowDefect (hN : N ≠ 0) (W : ConfFlow N) (k n : ℕ) (β : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..β, flowDelta hN W k n x

/-- The excess is continuous in the coupling. DERIVED: no numeral. -/
theorem continuous_excess (hN : N ≠ 0) (W : ConfFlow N) (k n : ℕ) (K : ℝ) :
    Continuous fun x => bareDelta hN n x - K * flowDelta hN W k n x :=
  (continuous_bareDelta hN n).sub (continuous_const.mul (continuous_flowDelta hN W k n))

/-- **The integrated excess is the bare defect less `K` times the flowed defect.** DERIVED: `0` the lower
coupling and the excluded side. -/
theorem integral_excess (hN : N ≠ 0) (W : ConfFlow N) (k : ℕ) {n : ℕ} (hn : n ≠ 0) (K β : ℝ) :
    ∫ x in (0 : ℝ)..β, (bareDelta hN n x - K * flowDelta hN W k n x)
      = defectW N β n - K * flowDefect hN W k n β := by
  have hf : Continuous fun x => K * flowDelta hN W k n x :=
    continuous_const.mul (continuous_flowDelta hN W k n)
  rw [intervalIntegral.integral_sub ((continuous_bareDelta hN n).intervalIntegrable 0 β)
      (hf.intervalIntegrable 0 β),
    intervalIntegral.integral_const_mul, integral_bareDelta hN hn]
  rfl

/-- **The comparison is one inequality between defects**: `FlowEnergyComp` iff eventually, at the side in the
window, `defectW − K · flowDefect ≤ η`. DERIVED: `0` the lower coupling; `2` the least side. -/
theorem flowEnergyComp_iff_defect (hN : N ≠ 0) (W : ConfFlow N) (κ : ℝ → ℕ) (C K η : ℝ) :
    FlowEnergyComp hN W κ C K η ↔
      ∀ᶠ β in atTop, ∀ n : ℕ, InWin N C β n → defectW N β n - K * flowDefect hN W (κ β) n β ≤ η := by
  constructor
  · intro h
    filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β hb hβ n hw
    have hI := integral_le_of_budget hβ (continuous_excess hN W (κ β) n K) (hb n hw)
    rwa [integral_excess hN W (κ β) (by have := hw.2.1; omega) K β] at hI
  · intro h
    refine h.mono fun β hb n hw => budget_of_integral (continuous_excess hN W (κ β) n K) ?_
    rw [integral_excess hN W (κ β) (by have := hw.2.1; omega) K β]
    exact hb n hw

/-- **The flowed seed is a bound on the flowed defect.** DERIVED: `0` the lower coupling. -/
theorem obsRunSeedFlowW_iff_defect (hN : N ≠ 0) (W : ConfFlow N) (κ : ℝ → ℕ) (C δ : ℝ) :
    ObsRunSeedFlowW hN W κ C δ ↔
      ∀ᶠ β in atTop, ∃ n : ℕ, InWin N C β n ∧ flowDefect hN W (κ β) n β ≤ δ := by
  constructor
  · intro h
    filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β ⟨n, hw, hb⟩ hβ
    exact ⟨n, hw, integral_le_of_budget hβ (continuous_flowDelta hN W (κ β) n) hb⟩
  · intro h
    exact h.mono fun β ⟨n, hw, hb⟩ => ⟨n, hw, budget_of_integral (continuous_flowDelta hN W (κ β) n) hb⟩

/-- Two powers of two, the first below the second, differ by a factor at least `2`. DERIVED: `2` the base. -/
theorem two_mul_le_of_pow2 {n m : ℕ} (hn : IsPow2 n) (hm : IsPow2 m) (h : n < m) : 2 * n ≤ m := by
  obtain ⟨b, rfl⟩ := hn
  obtain ⟨c, rfl⟩ := hm
  have hbc : b < c := by
    by_contra hcb
    have := Nat.pow_le_pow_right (by norm_num : 2 > 0) (not_lt.mp hcb)
    omega
  calc 2 * 2 ^ b = 2 ^ (b + 1) := by ring
    _ ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) hbc

/-- **The window holds at most one side.** DERIVED: `1` the least colour count; `0` the sign; `2` the window's
ratio. -/
theorem inWin_unique (hN : 1 ≤ N) {C β : ℝ} (hβ : 0 < β) {n m : ℕ} (hn : InWin N C β n)
    (hm : InWin N C β m) : n = m := by
  have ha := AsymptoticScaling.aRun_pos hN hβ
  have key : ∀ {n m : ℕ}, InWin N C β n → InWin N C β m → ¬ n < m := by
    intro n m hn hm hlt
    have h2 : (2 * n : ℝ) ≤ m := by exact_mod_cast two_mul_le_of_pow2 hn.1 hm.1 hlt
    have := mul_le_mul_of_nonneg_right h2 ha.le
    linarith [hn.2.2.1, hm.2.2.2]
  rcases lt_trichotomy n m with h | h | h
  · exact absurd h (key hn hm)
  · exact h
  · exact absurd h (key hm hn)

/-! ## 2. The coupling split -/

/-- **Integrals on adjacent coupling ranges add to a budget.** DERIVED: `0` the lower coupling. -/
theorem budget_split {β x₀ η₁ η₂ : ℝ} {g : ℝ → ℝ} (hg : Continuous g)
    (hs : ∫ x in (0 : ℝ)..x₀, g x ≤ η₁) (hl : ∫ x in x₀..β, g x ≤ η₂) : Budget β (η₁ + η₂) g := by
  refine budget_of_integral hg ?_
  rw [← intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable 0 x₀)
    (hg.intervalIntegrable x₀ β)]
  linarith

/-- **The comparison from a strong part at a fixed coupling `x₀` and a scaling part on `[x₀, β]`.**
DERIVED: `0` the lower coupling; `2` the least side. -/
theorem flowEnergyComp_of_split (hN : N ≠ 0) (W : ConfFlow N) (κ : ℝ → ℕ) {C K η₁ η₂ : ℝ} (x₀ : ℝ)
    (hs : ∀ᶠ β in atTop, ∀ n : ℕ, InWin N C β n → defectW N x₀ n - K * flowDefect hN W (κ β) n x₀ ≤ η₁)
    (hl : ∀ᶠ β in atTop, ∀ n : ℕ, InWin N C β n →
      ∫ x in x₀..β, (bareDelta hN n x - K * flowDelta hN W (κ β) n x) ≤ η₂) :
    FlowEnergyComp hN W κ C K (η₁ + η₂) := by
  filter_upwards [hs, hl] with β h1 h2 n hw
  refine budget_split (continuous_excess hN W (κ β) n K) ?_ (h2 n hw)
  rw [integral_excess hN W (κ β) (by have := hw.2.1; omega) K x₀]
  exact h1 n hw

/-! ## 3. The remainder observable -/

/-- **The remainder reading**: the plaquette densities less their flowed fields, at the origin.
DERIVED: `4` the dimension; `1` the successor; `0` the origin. -/
def remRead (hN : N ≠ 0) (W : ConfFlow N) (k n : ℕ) (β : ℝ) : ℝ :=
  ∑ p : Fin 4 × Fin 4, torusState hN (n - 1) β
    ((plaqField (N := N) (p, 0)).1 - (W.fieldMap k (plaqField (N := N) (p, 0))).1)

/-- **The bare reading is the flowed reading plus the remainder** (linearity of the torus state).
DERIVED: no numeral. -/
theorem bareRead_eq_flowRead_add_remRead (hN : N ≠ 0) (W : ConfFlow N) (k n : ℕ) (β : ℝ) :
    bareRead hN n β = flowRead hN W k n β + remRead hN W k n β := by
  unfold bareRead flowRead remRead
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [(torusState hN (n - 1) β).map_sub]
  ring

/-- The remainder's doubling change. DERIVED: `16 = 2⁴`; `2` the doubling; `4` the dimension. -/
def remDelta (hN : N ≠ 0) (W : ConfFlow N) (k n : ℕ) (β : ℝ) : ℝ :=
  16 * (n : ℝ) ^ 4 * (remRead hN W k (2 * n) β - remRead hN W k n β)

/-- **The remainder's change is the bare change less the flowed change.** DERIVED: `2` the doubling. -/
theorem remDelta_eq (hN : N ≠ 0) (W : ConfFlow N) (k n : ℕ) (β : ℝ) :
    remDelta hN W k n β = bareDelta hN n β - flowDelta hN W k n β := by
  unfold remDelta bareDelta flowDelta
  rw [bareRead_eq_flowRead_add_remRead hN W k (2 * n) β, bareRead_eq_flowRead_add_remRead hN W k n β]
  ring

/-- **At `K = 1` the comparison is the budget of the remainder's change.** DERIVED: `1` the unit constant. -/
theorem flowEnergyComp_one_iff (hN : N ≠ 0) (W : ConfFlow N) (κ : ℝ → ℕ) (C η : ℝ) :
    FlowEnergyComp hN W κ C 1 η ↔
      ∀ᶠ β in atTop, ∀ n : ℕ, InWin N C β n → Budget β η (remDelta hN W (κ β) n) := by
  constructor
  · intro h
    refine h.mono fun β hb n hw => budget_mono (hb n hw) (fun x _ => ?_) le_rfl
    rw [remDelta_eq]
    show bareDelta hN n x - flowDelta hN W (κ β) n x ≤ bareDelta hN n x - 1 * flowDelta hN W (κ β) n x
    linarith
  · intro h
    refine h.mono fun β hb n hw => budget_mono (hb n hw) (fun x _ => ?_) le_rfl
    rw [remDelta_eq]
    show bareDelta hN n x - 1 * flowDelta hN W (κ β) n x ≤ bareDelta hN n x - flowDelta hN W (κ β) n x
    linarith

/-- **The remainder controlled by the plaquette**: eventually, at the side in the window, the remainder's
change less `K'` times the bare change is within a budget `η'`. DERIVED: no numeral. -/
def RemControl (hN : N ≠ 0) (W : ConfFlow N) (κ : ℝ → ℕ) (C K' η' : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ n : ℕ, InWin N C β n →
    Budget β η' (fun x => remDelta hN W (κ β) n x - K' * bareDelta hN n x)

/-- **A budget scales by a nonnegative constant.** DERIVED: `0` the sign. -/
theorem budget_const_mul {β η c : ℝ} {g : ℝ → ℝ} (hc : 0 ≤ c) (h : Budget β η g) :
    Budget β (c * η) (fun x => c * g x) := by
  obtain ⟨Φ, φ, h0, hβ, hd, hg⟩ := h
  exact ⟨fun x => c * Φ x, fun x => c * φ x, by simp [h0], mul_le_mul_of_nonneg_left hβ hc,
    fun x hx => (hd x hx).const_mul c, fun x hx => mul_le_mul_of_nonneg_left (hg x hx) hc⟩

/-- **Remainder control is the comparison, rescaled**: at `K > 0`,
`FlowEnergyComp K η ↔ RemControl (1 − K⁻¹) (η / K)`. DERIVED: `1` the unit; `0` the sign. -/
theorem flowEnergyComp_iff_remControl (hN : N ≠ 0) (W : ConfFlow N) (κ : ℝ → ℕ) (C : ℝ) {K η : ℝ}
    (hK : 0 < K) : FlowEnergyComp hN W κ C K η ↔ RemControl hN W κ C (1 - K⁻¹) (η / K) := by
  have hKK : K * K⁻¹ = 1 := mul_inv_cancel₀ hK.ne'
  constructor
  · intro h
    refine h.mono fun β hb n hw =>
      budget_mono (budget_const_mul (inv_nonneg.mpr hK.le) (hb n hw)) (fun x _ => ?_) (div_eq_inv_mul η K).ge
    show remDelta hN W (κ β) n x - (1 - K⁻¹) * bareDelta hN n x
      ≤ K⁻¹ * (bareDelta hN n x - K * flowDelta hN W (κ β) n x)
    rw [remDelta_eq]
    exact le_of_eq (by linear_combination (flowDelta hN W (κ β) n x) * hKK)
  · intro h
    refine h.mono fun β hb n hw =>
      budget_mono (budget_const_mul hK.le (hb n hw)) (fun x _ => ?_) (le_of_eq ?_)
    · show bareDelta hN n x - K * flowDelta hN W (κ β) n x
        ≤ K * (remDelta hN W (κ β) n x - (1 - K⁻¹) * bareDelta hN n x)
      rw [remDelta_eq]
      exact le_of_eq (by linear_combination (-(bareDelta hN n x)) * hKK)
    · field_simp

/-! ## 4. Per-site closeness: a growing budget -/

/-- **Per-site closeness bounds the remainder reading.** DERIVED: `16` the ordered planes; `0` the origin. -/
theorem abs_remRead_le (hN : N ≠ 0) (W : ConfFlow N) (k n : ℕ) (β : ℝ) {ε : ℝ}
    (hε : ∀ (p : Fin 4 × Fin 4) (U : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)),
      |(plaqField (N := N) (p, 0)).1 U - (W.fieldMap k (plaqField (N := N) (p, 0))).1 U| ≤ ε) :
    |remRead hN W k n β| ≤ 16 * ε := by
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hε (0, 0) (fun _ => 1))
  have hp : ∀ p : Fin 4 × Fin 4, |torusState hN (n - 1) β
      ((plaqField (N := N) (p, 0)).1 - (W.fieldMap k (plaqField (N := N) (p, 0))).1)| ≤ ε := by
    intro p
    refine ((torusState hN (n - 1) β).abs_le_norm _).trans ?_
    refine (ContinuousMap.norm_le _ hε0).mpr fun U => ?_
    rw [Real.norm_eq_abs]
    exact hε p U
  unfold remRead
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun p _ => hp p).trans ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- **Per-site closeness bounds the remainder's change by `512 ε n⁴`**, a quantity growing with the side.
DERIVED: `512 = 16 · 32`; `32 = 2 · 16`; `4` the dimension. -/
theorem remDelta_le (hN : N ≠ 0) (W : ConfFlow N) (k n : ℕ) (β : ℝ) {ε : ℝ}
    (hε : ∀ (p : Fin 4 × Fin 4) (U : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)),
      |(plaqField (N := N) (p, 0)).1 U - (W.fieldMap k (plaqField (N := N) (p, 0))).1 U| ≤ ε) :
    remDelta hN W k n β ≤ 512 * ε * (n : ℝ) ^ 4 := by
  have h1 := abs_le.mp (abs_remRead_le hN W k (2 * n) β hε)
  have h2 := abs_le.mp (abs_remRead_le hN W k n β hε)
  have hab : remRead hN W k (2 * n) β - remRead hN W k n β ≤ 32 * ε := by linarith [h1.2, h2.1]
  have := mul_le_mul_of_nonneg_left hab (by positivity : (0 : ℝ) ≤ 16 * (n : ℝ) ^ 4)
  unfold remDelta
  linarith

/-- **Per-site closeness gives the comparison at `K = 1` only with the budget `512 ε n⁴ β`.**
DERIVED: `512` as in `remDelta_le`; `1` the unit constant; `0` the lower coupling. -/
theorem flowEnergyComp_one_of_closeness (hN : N ≠ 0) {W : ConfFlow N} {κ : ℝ → ℕ} {C η ε : ℝ}
    (hε : ∀ (k : ℕ) (p : Fin 4 × Fin 4) (U : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)),
      |(plaqField (N := N) (p, 0)).1 U - (W.fieldMap k (plaqField (N := N) (p, 0))).1 U| ≤ ε)
    (hη : ∀ᶠ β in atTop, ∀ n : ℕ, InWin N C β n → 512 * ε * (n : ℝ) ^ 4 * β ≤ η) :
    FlowEnergyComp hN W κ C 1 η := by
  refine hη.mono fun β hb n hw => ?_
  refine ⟨fun x => 512 * ε * (n : ℝ) ^ 4 * x, fun _ => 512 * ε * (n : ℝ) ^ 4, by simp, hb n hw,
    fun x _ => ?_, fun x _ => ?_⟩
  · simpa using (hasDerivAt_id' x).const_mul (512 * ε * (n : ℝ) ^ 4)
  · show bareDelta hN n x - 1 * flowDelta hN W (κ β) n x ≤ 512 * ε * (n : ℝ) ^ 4
    have := remDelta_le hN W (κ β) n x (hε (κ β))
    rw [remDelta_eq] at this
    linarith

/-! ## 5. The degenerate case -/

/-- A flow that is the identity at step `k` leaves every field unchanged. DERIVED: no numeral. -/
theorem fieldMap_of_V_id {W : ConfFlow N} {k : ℕ} (h : W.V k = id)
    (O : MassGap.ContinuumField.LField (MassGap.SUN.SU N)) : (W.fieldMap k O).1 = O.1 := by
  ext U
  show O.1 (W.V k U) = O.1 U
  rw [h]
  rfl

/-- At a step where the flow is the identity the flowed reading is the bare reading. DERIVED: no numeral. -/
theorem flowRead_of_V_id (hN : N ≠ 0) {W : ConfFlow N} {k : ℕ} (h : W.V k = id) (n : ℕ) (β : ℝ) :
    flowRead hN W k n β = bareRead hN n β := by
  unfold flowRead bareRead
  simp only [fieldMap_of_V_id h]

/-- **A flow that is eventually the identity at the observer's step satisfies the comparison at `K = 1`,
`η = 0`.** DERIVED: `1` the unit constant; `0` the slack. -/
theorem flowEnergyComp_of_eventually_id (hN : N ≠ 0) {W : ConfFlow N} {κ : ℝ → ℕ} (C : ℝ)
    (h : ∀ᶠ β in atTop, W.V (κ β) = id) : FlowEnergyComp hN W κ C 1 0 := by
  refine h.mono fun β hβ n _ => ⟨fun _ => 0, fun _ => 0, rfl, le_rfl,
    fun x _ => hasDerivAt_const x (0 : ℝ), fun x _ => ?_⟩
  show bareDelta hN n x - 1 * flowDelta hN W (κ β) n x ≤ 0
  unfold flowDelta
  rw [flowRead_of_V_id hN hβ, flowRead_of_V_id hN hβ]
  unfold bareDelta
  linarith

/-- **`blFam` at a coarse step**: if eventually the aperture `s` is below `2 m` coarse spacings at the
observer's step, the ray-averaged multigrid flow is the identity there and satisfies the comparison at
`K = 1`, `η = 0`. DERIVED: `2` the stride ratio; `12` the staple count bound of `blFam`; `1`, `0` as above. -/
theorem flowEnergyComp_blFam_coarse (hN2 : 2 ≤ N) (hN : N ≠ 0) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ) {s : ℝ} (hs0 : 0 ≤ s) {κ : ℝ → ℕ} (C : ℝ)
    (h : ∀ᶠ β in atTop, s < 2 * (m * ContinuumSchwinger.dySpacing N (κ β))) :
    FlowEnergyComp hN (ObserverBlock.blFam hN2 c hc0 hc m s) κ C 1 0 :=
  flowEnergyComp_of_eventually_id hN C
    (h.mono fun _ hβ => ObserverBlock.blFam_V_of_lt hN2 hc0 hc m hs0 hβ)

end MassGap.FlowComp

end

#print axioms MassGap.FlowComp.continuous_torusState
#print axioms MassGap.FlowComp.continuous_bareRead
#print axioms MassGap.FlowComp.continuous_flowRead
#print axioms MassGap.FlowComp.continuous_bareDelta
#print axioms MassGap.FlowComp.continuous_flowDelta
#print axioms MassGap.FlowComp.budget_of_integral
#print axioms MassGap.FlowComp.integral_le_of_budget
#print axioms MassGap.FlowComp.budget_iff_integral
#print axioms MassGap.FlowComp.integral_bareDelta
#print axioms MassGap.FlowComp.continuous_excess
#print axioms MassGap.FlowComp.integral_excess
#print axioms MassGap.FlowComp.flowEnergyComp_iff_defect
#print axioms MassGap.FlowComp.obsRunSeedFlowW_iff_defect
#print axioms MassGap.FlowComp.two_mul_le_of_pow2
#print axioms MassGap.FlowComp.inWin_unique
#print axioms MassGap.FlowComp.budget_split
#print axioms MassGap.FlowComp.flowEnergyComp_of_split
#print axioms MassGap.FlowComp.bareRead_eq_flowRead_add_remRead
#print axioms MassGap.FlowComp.remDelta_eq
#print axioms MassGap.FlowComp.flowEnergyComp_one_iff
#print axioms MassGap.FlowComp.budget_const_mul
#print axioms MassGap.FlowComp.flowEnergyComp_iff_remControl
#print axioms MassGap.FlowComp.abs_remRead_le
#print axioms MassGap.FlowComp.remDelta_le
#print axioms MassGap.FlowComp.flowEnergyComp_one_of_closeness
#print axioms MassGap.FlowComp.fieldMap_of_V_id
#print axioms MassGap.FlowComp.flowRead_of_V_id
#print axioms MassGap.FlowComp.flowEnergyComp_of_eventually_id
#print axioms MassGap.FlowComp.flowEnergyComp_blFam_coarse
