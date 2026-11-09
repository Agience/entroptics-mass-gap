import Mathlib
import MassGap.ObserverTheory
import MassGap.TomboulisYaffe
import MassGap.VortexStrong

/-!
# MassGap.FluxCost — the flux half of the `SU(N)` binding statement as 't Hooft vortex free energies

`ObserverTheory.FluxCostAt N σ A ℓ` asks, eventually in `β`, at every power-of-two side `n ≥ 2` of physical length
`n a ∈ [2ℓ, 5ℓ]` (`a = aRun N β`), at every corner step `i`, that the flux share
`fluxShareN N β n i = 1 − N⁻³ Σ_g Z_g/Z` (`CentreSectorSeedN.fluxShareN_eq_mean`) is at most `A e^{−σ n a}`.
This module rewrites that statement at the same objects as a bound on the single-plane centre twists, and at
`SU(2)` as a bound on the 't Hooft vortex ratios `zR` of the corner tori, the objects of
`TomboulisYaffe` and `VortexCondense`; and it proves what the flux half gives for Wilson loops through the
Tomboulis–Yaffe decomposition, given that module's unproved chessboard input.

## 1. Single-plane twists (every `N`)

* `PlaneCostAt N σ A ℓ`: the same window, the bound `1 − Z_{e_ν}/Z ≤ A e^{−σ n a}` for the three generators `e_ν`
  of the centre `Z_N³` of the slice of step `i` (`twistRatioN N β n i (Pi.single ν 1)`).
* `one_sub_twistRatioN_le_cube`: every twist deficit is at most `N³` times the flux share (the deficits are
  non-negative and add up to `N³ · fluxShareN`).
* `planeCostAt_of_fluxCostAt`: `FluxCostAt N σ A ℓ ⇒ PlaneCostAt N σ (N³ A) ℓ`.
* `fluxCostAt_of_planeCostAt`: `PlaneCostAt N σ A ℓ ⇒ FluxCostAt N σ (9⌊N/2⌋² A) ℓ`
  (`TwistDeficitUnionN.fluxShareN_le_of_single`).
* `exists_fluxCostAt_iff`: `(∃ A, FluxCostAt N σ A ℓ) ↔ ∃ A, PlaneCostAt N σ A ℓ`.
* `BindingPlane N σ A`: `σ > 0` and, frequently in `ℓ`, `PlaneCostAt ∧ HiddenCostAt`;
  `runSeed_iff_bindingPlane`: `WDeltaRun.RunSeed N ↔ ∃ σ A, BindingPlane N σ A`
  (`ObserverTheory.runSeed_iff_bindingSU`).

## 2. The 't Hooft vortex ratios at `SU(2)`

* `VortexCostAt σ A ℓ`: the same window, `1 − zR (Lc n i) i ν β ≤ A e^{−σ n a}` for every corner step `i` and
  every transverse `ν`: the vortex ratio `Z(twist in the plane (i, ν))/Z` of the corner torus `Lc n i`.
  `1 − zR` is `VortexCondense.elw`, twice the `SU(2)` electric weight `exp(−F_el)` of Tomboulis–Yaffe.
* `planeCostAt_two_iff`: `PlaneCostAt 2 σ A ℓ ↔ VortexCostAt σ A ℓ` (`GapSideVortexRect.twistRatioN_eq_zR`).
* `exists_fluxCostAt_two_iff`: `(∃ A, FluxCostAt 2 σ A ℓ) ↔ ∃ A, VortexCostAt σ A ℓ`.
* `runSeed_two_iff_vortex`: `WDeltaRun.RunSeed 2 ↔ ∃ σ A, 0 < σ ∧ ∃ᶠ ℓ, VortexCostAt σ A ℓ ∧ HiddenCostAt 2 σ A ℓ`.

## 3. From the flux half to Wilson loops (conditional on `TomboulisYaffe.ChessboardFlux`)

* `wloop_le_of_vortex`: on the corner torus `Lc n i`, plane `(i, ν)`, `1 − zR ≤ A e^{−σx}` with `A ≤ 2` and
  `ChessboardFlux` give, on every `AdmTwo` rectangle `m × m'`, `wloopR ≤ 2 exp(−σx · mm'/(L_i L_ν))`
  (`TomboulisYaffe.tyTwo_of_chessboard`).
* `Lc_le`: every extent of `Lc n i` is at most `2n`.
* `wloop_le_phys`: at `x = n a`, `a > 0`, `σ ≥ 0`, the same loops satisfy
  `wloopR ≤ 2 exp(−(σ/(4 n a)) · (m a)(m' a))`: an area law in physical units with tension `σ/(4 n a)`.

At sides `n a ∈ [2ℓ, 5ℓ]` that tension is at least `σ/(20ℓ)` and at most `σ/(8ℓ)`. Argued, not a declaration:
`BindingSU` asks `FluxCostAt` only frequently in `ℓ`, so through this route the tension `σ/(4 n a)` tends to `0`
along those `ℓ` and gives no tension bounded below uniformly in the box; the Tomboulis–Yaffe route turns a
cross-section rate into a loop rate (`TomboulisYaffe.area_two_of_chessboard` needs `1 − zR ≤ exp(−s L_a L_b)`),
and `FluxCostAt` is a rate per length.

## What is not proved

* No declaration in the tree bounds `fluxShareN`, `twistRatioN` or `zR` above by a Wilson-loop quantity, a
  string tension (`EdgeCost.StringScalingAt`, which is a predicate on an arbitrary function `σlat`, not tied to
  the Wilson measure), `NoTransition.Floor`, or `NonAbelianForget.ConfinedEdges` (a predicate on an arbitrary
  `ApertureReading`). The direction "tension ⇒ small flux share" is not in the tree. Evaluation, not a
  theorem: it is the converse of the Tomboulis–Yaffe inequality (`tyTwo_of_chessboard`: small electric weight ⇒
  area law), and no proof of it is known to us.
* `ChessboardFlux` itself is not proved (`Chessboard.chessboardFlux_of`: it follows from `FullLoopFlux`, which
  fails in some geometries, and `OutsideFlux`, for which no proof is known).

DERIVED (module-wide): `4` the dimension and `3 = |{ν ≠ i}|`; `N³ = |Z_N³|` (`SliceCentreAction.card_cen`);
`9⌊N/2⌋²` from `TwistDeficitUnionN.fluxShareN_le_of_single`; `2` and `5` the window of
`ObserverTheory.FluxCostAt`; `2` in `A ≤ 2` the factor `(1 − zR)/2` of `tyTwo_of_chessboard`; `4 = 2 · 2` the
bound `L_i L_ν ≤ (2n)²` (`Lc_le`), `20 = 4 · 5`, `8 = 4 · 2`.
-/

noncomputable section

namespace MassGap.FluxCost

open Filter MassGap MassGap.CentreSectorSeedN
open MassGap.SliceCentreAction (Cen)
open MassGap.ObserverTheory (FluxCostAt HiddenCostAt BindingSU)

/-! ## 1. Single-plane twists -/

section Plane

variable (N : ℕ) [NeZero N]

/-- **The single-plane twists cost `σ` per length** at the window `[2ℓ, 5ℓ]`: every step's generator twist
deficit `1 − Z_{e_ν}/Z`. DERIVED: `2` and `5` the window of `ObserverTheory.FluxCostAt` (`5` leaves
room for the power of two at or above `⌈2ℓ/a⌉`, which is below `4ℓ + 2a`); `2` also the least side. -/
def PlaneCostAt (σ A ℓ : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
    2 * ℓ ≤ (n : ℝ) * AsymptoticScaling.aRun N β → (n : ℝ) * AsymptoticScaling.aRun N β ≤ 5 * ℓ →
    ∀ i : Fin 4, ∀ ν : {j : Fin 4 // j ≠ i},
      1 - twistRatioN N β n i (Pi.single ν 1)
        ≤ A * Real.exp (-(σ * ((n : ℝ) * AsymptoticScaling.aRun N β)))

variable {N}

/-- Every centre twist deficit is non-negative. -/
theorem one_sub_twistRatioN_nonneg {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) (g : Cen i N) :
    0 ≤ 1 - twistRatioN N β n i g := by
  rw [TwistDeficitUnionN.one_sub_twistRatioN (N := N) hβ n i g]
  exact div_nonneg (TwistDeficitUnionN.deficit_nonneg (bdd_halfKN hβ _ i)
    SliceCentreAction.centreAction _) (hs_halfKN_pos (N := N) hβ n i).le

/-- **Each centre twist deficit is at most `N³` times the flux share.** -/
theorem one_sub_twistRatioN_le_cube {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) (g : Cen i N) :
    1 - twistRatioN N β n i g ≤ (N : ℝ) ^ 3 * fluxShareN N β n i := by
  have hm := fluxShareN_eq_mean (N := N) hβ n i
  have hN3 : ((N : ℝ) ^ 3) ≠ 0 := by
    have : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
    positivity
  have hs : ∑ h : Cen i N, (1 - twistRatioN N β n i h) = (N : ℝ) ^ 3 * fluxShareN N β n i := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, SliceCentreAction.card_cen, hm,
      nsmul_eq_mul]
    simp only [Nat.cast_pow, mul_one]
    rw [mul_sub, mul_one, ← mul_assoc, mul_inv_cancel₀ hN3, one_mul]
  rw [← hs]
  exact Finset.single_le_sum (fun h _ => one_sub_twistRatioN_nonneg hβ n i h) (Finset.mem_univ g)

theorem planeCostAt_mono {σ A A' ℓ : ℝ} (hA : A ≤ A') (h : PlaneCostAt N σ A ℓ) :
    PlaneCostAt N σ A' ℓ := by
  filter_upwards [h] with β hβ n hn h2 hlo hup i ν
  exact (hβ n hn h2 hlo hup i ν).trans (mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le)

theorem fluxCostAt_mono {σ A A' ℓ : ℝ} (hA : A ≤ A') (h : FluxCostAt N σ A ℓ) :
    FluxCostAt N σ A' ℓ := by
  filter_upwards [h] with β hβ n hn h2 hlo hup i
  exact (hβ n hn h2 hlo hup i).trans (mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le)

theorem hiddenCostAt_mono {σ A A' ℓ : ℝ} (hA : A ≤ A') (h : HiddenCostAt N σ A ℓ) :
    HiddenCostAt N σ A' ℓ := by
  filter_upwards [h] with β hβ n hn h2 hlo hup i
  exact (hβ n hn h2 hlo hup i).trans (mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le)

/-- **The flux half gives the single-plane form** with `A` multiplied by `N³`. -/
theorem planeCostAt_of_fluxCostAt {σ A ℓ : ℝ} (h : FluxCostAt N σ A ℓ) :
    PlaneCostAt N σ ((N : ℝ) ^ 3 * A) ℓ := by
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β hβ hβ0 n hn h2 hlo hup i ν
  have h1 := one_sub_twistRatioN_le_cube (N := N) hβ0 n i (Pi.single ν 1)
  have h2' := mul_le_mul_of_nonneg_left (hβ n hn h2 hlo hup i)
    (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 3)
  rw [mul_assoc]
  exact h1.trans h2'

/-- **The single-plane form gives the flux half** with `A` multiplied by `9⌊N/2⌋²`. -/
theorem fluxCostAt_of_planeCostAt {σ A ℓ : ℝ} (h : PlaneCostAt N σ A ℓ) :
    FluxCostAt N σ (9 * ((N / 2 : ℕ) : ℝ) ^ 2 * A) ℓ := by
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β hβ hβ0 n hn h2 hlo hup i
  set δ := A * Real.exp (-(σ * ((n : ℝ) * AsymptoticScaling.aRun N β))) with hδ_def
  have hν0 : (i + 1) ≠ i := by fin_cases i <;> decide
  have hδ : 0 ≤ δ :=
    (one_sub_twistRatioN_nonneg hβ0 n i (Pi.single ⟨i + 1, hν0⟩ 1)).trans
      (hβ n hn h2 hlo hup i ⟨i + 1, hν0⟩)
  have hf := TwistDeficitUnionN.fluxShareN_le_of_single (N := N) hβ0 n i hδ
    (fun ν => by have := hβ n hn h2 hlo hup i ν; linarith)
  refine hf.trans (le_of_eq ?_)
  rw [hδ_def]; ring

/-- **The flux half is the single-plane form**, up to the constant. -/
theorem exists_fluxCostAt_iff {σ ℓ : ℝ} :
    (∃ A, FluxCostAt N σ A ℓ) ↔ ∃ A, PlaneCostAt N σ A ℓ :=
  ⟨fun ⟨_, h⟩ => ⟨_, planeCostAt_of_fluxCostAt h⟩, fun ⟨_, h⟩ => ⟨_, fluxCostAt_of_planeCostAt h⟩⟩

variable (N) in
/-- **The binding statement at `SU(N)` with the flux half in single-plane form.** -/
def BindingPlane (σ A : ℝ) : Prop :=
  0 < σ ∧ ∃ᶠ ℓ in atTop, PlaneCostAt N σ A ℓ ∧ HiddenCostAt N σ A ℓ

theorem bindingSU_of_bindingPlane {σ A : ℝ} (h : BindingPlane N σ A) :
    BindingSU N σ (max (9 * ((N / 2 : ℕ) : ℝ) ^ 2 * A) A) := by
  refine ⟨h.1, h.2.mono fun ℓ hℓ => ⟨?_, ?_⟩⟩
  · exact fluxCostAt_mono (le_max_left _ _) (fluxCostAt_of_planeCostAt hℓ.1)
  · exact hiddenCostAt_mono (le_max_right _ _) hℓ.2

theorem bindingPlane_of_bindingSU {σ A : ℝ} (h : BindingSU N σ A) :
    BindingPlane N σ (max ((N : ℝ) ^ 3 * A) A) := by
  refine ⟨h.1, h.2.mono fun ℓ hℓ => ⟨?_, ?_⟩⟩
  · exact planeCostAt_mono (le_max_left _ _) (planeCostAt_of_fluxCostAt hℓ.1)
  · exact hiddenCostAt_mono (le_max_right _ _) hℓ.2

variable (N) in
/-- **The run seed of `SU(N)` is the binding statement in single-plane form.** -/
theorem runSeed_iff_bindingPlane : WDeltaRun.RunSeed N ↔ ∃ σ A : ℝ, BindingPlane N σ A := by
  rw [ObserverTheory.runSeed_iff_bindingSU]
  exact ⟨fun ⟨σ, A, h⟩ => ⟨σ, _, bindingPlane_of_bindingSU h⟩,
    fun ⟨σ, A, h⟩ => ⟨σ, _, bindingSU_of_bindingPlane h⟩⟩

end Plane

/-! ## 2. The 't Hooft vortex ratios at `SU(2)` -/

section Two

open MassGap.GapSideVortexRect (zR Lc twistRatioN_eq_zR)

/-- **The 't Hooft vortex ratios cost `σ` per length** at the window `[2ℓ, 5ℓ]`: at every corner step `i`, the
vortex ratio of the corner torus `Lc n i` in every plane `(i, ν)` has deficit at most `A e^{−σ n a}`.
DERIVED: `2` and `5` the window, as in `PlaneCostAt`; `2` also the least side and the rank of `SU(2)`. -/
def VortexCostAt (σ A ℓ : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
    2 * ℓ ≤ (n : ℝ) * AsymptoticScaling.aRun 2 β → (n : ℝ) * AsymptoticScaling.aRun 2 β ≤ 5 * ℓ →
    ∀ i : Fin 4, ∀ ν : {j : Fin 4 // j ≠ i},
      1 - zR (Lc n i) i ν.1 β ≤ A * Real.exp (-(σ * ((n : ℝ) * AsymptoticScaling.aRun 2 β)))

theorem even_of_pow2 {n : ℕ} (hn : PeriodicState.IsPow2 n) (h2 : 2 ≤ n) : Even n := by
  obtain ⟨b, rfl⟩ := hn
  rcases Nat.eq_zero_or_pos b with h0 | h0
  · subst h0; norm_num at h2
  · exact DeltaLengthTower.even_two_pow h0

/-- **At `SU(2)` the single-plane form is the vortex form.** -/
theorem planeCostAt_two_iff {σ A ℓ : ℝ} : PlaneCostAt 2 σ A ℓ ↔ VortexCostAt σ A ℓ := by
  constructor
  · intro h
    filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β hβ hβ0 n hn h2 hlo hup i ν
    rw [← twistRatioN_eq_zR hβ0 h2 (even_of_pow2 hn h2) i ν]
    exact hβ n hn h2 hlo hup i ν
  · intro h
    filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β hβ hβ0 n hn h2 hlo hup i ν
    rw [twistRatioN_eq_zR hβ0 h2 (even_of_pow2 hn h2) i ν]
    exact hβ n hn h2 hlo hup i ν

/-- **At `SU(2)` the flux half is the vortex form**, up to the constant. -/
theorem exists_fluxCostAt_two_iff {σ ℓ : ℝ} :
    (∃ A, FluxCostAt 2 σ A ℓ) ↔ ∃ A, VortexCostAt σ A ℓ := by
  rw [exists_fluxCostAt_iff]
  exact exists_congr fun _ => planeCostAt_two_iff

/-- **The run seed of `SU(2)` is the vortex form of the flux half with the hidden half.** -/
theorem runSeed_two_iff_vortex :
    WDeltaRun.RunSeed 2 ↔
      ∃ σ A : ℝ, 0 < σ ∧ ∃ᶠ ℓ in atTop, VortexCostAt σ A ℓ ∧ HiddenCostAt 2 σ A ℓ := by
  rw [runSeed_iff_bindingPlane]
  refine exists_congr fun σ => exists_congr fun A => ?_
  unfold BindingPlane
  refine and_congr Iff.rfl ⟨fun h => h.mono fun ℓ hℓ => ⟨planeCostAt_two_iff.mp hℓ.1, hℓ.2⟩,
    fun h => h.mono fun ℓ hℓ => ⟨planeCostAt_two_iff.mpr hℓ.1, hℓ.2⟩⟩

end Two

/-! ## 3. From the flux half to Wilson loops, given the chessboard input -/

section Wilson

open MassGap.GapSideVortexRect (zR Lc)

/-- Every extent of the corner torus `Lc n i` is at most `2n`. An alias of `VortexStrong.Lc_le_two`. -/
alias Lc_le := MassGap.VortexStrong.Lc_le_two

/-- **The vortex form of the flux half bounds the Wilson loops of the corner torus**, given
`TomboulisYaffe.ChessboardFlux`: `1 − zR ≤ A e^{−σx}`, `A ≤ 2` give
`wloopR ≤ 2 exp(−σx · mm'/(L_i L_ν))` on every `AdmTwo` rectangle of the plane `(i, ν)`. -/
theorem wloop_le_of_vortex {σ A x β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) (i : Fin 4)
    (ν : {j : Fin 4 // j ≠ i}) (o : RectWilson.RSite (Lc n i)) (hA : A ≤ 2)
    (hv : 1 - zR (Lc n i) i ν.1 β ≤ A * Real.exp (-(σ * x)))
    (hCB : TomboulisYaffe.ChessboardFlux (Lc n i) i ν.1 o β) {m m' : ℕ}
    (hadm : TomboulisYaffe.AdmTwo (Lc n i i) (Lc n i ν.1) m m') :
    VortexCondense.wloopR (Lc n i) i ν.1 m m' o β
      ≤ 2 * Real.exp (-(σ * x) * (((m : ℝ) * m') / ((Lc n i i : ℝ) * Lc n i ν.1))) := by
  have hTY := TomboulisYaffe.tyTwo_of_chessboard (Lc n i) (Ne.symm ν.2) o hCB hadm
  have hz := VortexCondense.zR_Lc_le_one hβ hn he i ν
  have h0 : 0 ≤ (1 - zR (Lc n i) i ν.1 β) / 2 := by linarith
  have he0 := Real.exp_pos (-(σ * x))
  have hle : (1 - zR (Lc n i) i ν.1 β) / 2 ≤ Real.exp (-(σ * x)) := by
    have := mul_le_mul_of_nonneg_right hA he0.le
    linarith
  have hp : 0 ≤ ((m : ℝ) * m') / ((Lc n i i : ℝ) * Lc n i ν.1) := by positivity
  have hr := Real.rpow_le_rpow h0 hle hp
  rw [← Real.exp_mul] at hr
  linarith

/-- **In physical units the tension is `σ/(4 n a)`**: at `x = n a`, the same loops satisfy
`wloopR ≤ 2 exp(−(σ/(4 n a)) · (m a)(m' a))`. -/
theorem wloop_le_phys {σ A a β : ℝ} (hσ : 0 ≤ σ) (ha : 0 < a) (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n)
    (he : Even n) (i : Fin 4) (ν : {j : Fin 4 // j ≠ i}) (o : RectWilson.RSite (Lc n i)) (hA : A ≤ 2)
    (hv : 1 - zR (Lc n i) i ν.1 β ≤ A * Real.exp (-(σ * ((n : ℝ) * a))))
    (hCB : TomboulisYaffe.ChessboardFlux (Lc n i) i ν.1 o β) {m m' : ℕ}
    (hadm : TomboulisYaffe.AdmTwo (Lc n i i) (Lc n i ν.1) m m') :
    VortexCondense.wloopR (Lc n i) i ν.1 m m' o β
      ≤ 2 * Real.exp (-(σ / (4 * ((n : ℝ) * a)) * (((m : ℝ) * a) * ((m' : ℝ) * a)))) := by
  have hW := wloop_le_of_vortex hβ hn he i ν o hA hv hCB hadm
  refine hW.trans ?_
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hLi : (0 : ℝ) < Lc n i i := by
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le m) hadm.1.2.2.1
  have hLν : (0 : ℝ) < Lc n i ν.1 := by
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le m') hadm.1.2.2.2
  have hP : (0 : ℝ) < (Lc n i i : ℝ) * Lc n i ν.1 := mul_pos hLi hLν
  have hPle : (Lc n i i : ℝ) * Lc n i ν.1 ≤ 4 * (n : ℝ) ^ 2 := by
    have h1 : (Lc n i i : ℝ) ≤ 2 * n := by exact_mod_cast Lc_le n i i
    have h2 : (Lc n i ν.1 : ℝ) ≤ 2 * n := by exact_mod_cast Lc_le n i ν.1
    nlinarith
  have hmm : (0 : ℝ) ≤ (m : ℝ) * m' := by positivity
  have hnum : 0 ≤ σ * ((n : ℝ) * a) * ((m : ℝ) * m') := by positivity
  have key : σ / (4 * ((n : ℝ) * a)) * (((m : ℝ) * a) * ((m' : ℝ) * a))
      ≤ σ * ((n : ℝ) * a) * (((m : ℝ) * m') / ((Lc n i i : ℝ) * Lc n i ν.1)) := by
    have e1 : σ / (4 * ((n : ℝ) * a)) * (((m : ℝ) * a) * ((m' : ℝ) * a))
        = σ * ((n : ℝ) * a) * ((m : ℝ) * m') / (4 * (n : ℝ) ^ 2) := by
      field_simp
    have e2 : σ * ((n : ℝ) * a) * (((m : ℝ) * m') / ((Lc n i i : ℝ) * Lc n i ν.1))
        = σ * ((n : ℝ) * a) * ((m : ℝ) * m') / ((Lc n i i : ℝ) * Lc n i ν.1) := by
      ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_left hnum hP hPle
  have : -(σ * ((n : ℝ) * a)) * (((m : ℝ) * m') / ((Lc n i i : ℝ) * Lc n i ν.1))
      ≤ -(σ / (4 * ((n : ℝ) * a)) * (((m : ℝ) * a) * ((m' : ℝ) * a))) := by linarith
  have := Real.exp_le_exp.mpr this
  linarith

end Wilson

end MassGap.FluxCost

end

#print axioms MassGap.FluxCost.one_sub_twistRatioN_le_cube
#print axioms MassGap.FluxCost.planeCostAt_of_fluxCostAt
#print axioms MassGap.FluxCost.fluxCostAt_of_planeCostAt
#print axioms MassGap.FluxCost.exists_fluxCostAt_iff
#print axioms MassGap.FluxCost.runSeed_iff_bindingPlane
#print axioms MassGap.FluxCost.planeCostAt_two_iff
#print axioms MassGap.FluxCost.exists_fluxCostAt_two_iff
#print axioms MassGap.FluxCost.runSeed_two_iff_vortex
#print axioms MassGap.FluxCost.Lc_le
#print axioms MassGap.FluxCost.wloop_le_of_vortex
#print axioms MassGap.FluxCost.wloop_le_phys
