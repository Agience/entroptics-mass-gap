import Mathlib
import MassGap.ScaleControl
import MassGap.ElectricLoops
import MassGap.MixConvRP

/-!
# MassGap.ScaleControlRun — the full gap input `WDeltaRun.RunSeed 2` from scale control plus odd-flux levels

`ScaleControl ℓ` gives (T), `HiddenCostAt 2 m A ℓ`, at one window. `FluxCost.runSeed_two_iff_vortex` asks for
(V) `VortexCostAt σ A ℓ` and (T) `HiddenCostAt 2 σ A ℓ` at one `σ > 0`, one `A`, frequently in `ℓ`. This module
adds what (V) needs and makes the constants uniform.

## 1. What (V) needs (proved: the reduction; argued: why the block contraction does not supply it)

By `VortexAperture.one_sub_zR_eq_oddFlux`, `1 − zR (Lc n i) i ν β = 2 · oddFlux / hs(halfKN)`, `oddFlux` the
summed Hilbert–Schmidt trace of the real sector kernels `ElectricLoops.rsec halfKN act ψ` over the characters
`ψ` odd under the twist `e_ν`. (V) is a bound on a trace over the whole odd electric-flux sector.

* `OddLevels β n i ν g₀ E m t₀ Co`: the odd sector in its levels. Eigenfunctions `φ_j` of `rsec halfKN act ψ_j`
  (`ψ_j(e_ν) ≠ 1`), orthonormal, eigenvalues `λ_j² = e^{−F_j t}` (`t = n a`), exhausting the trace:
  `oddFlux = Σ_j e^{−F_j t}` (bookkeeping: the Hilbert–Schmidt spectral theorem for each of the four odd
  sector kernels, as `TensionFloor.EigenLevels` is for `trivKN`; not proved in the tree). Physics, open:
  `gap` (`F_j ≥ E_{g₀} + m`: one unit of electric flux winding direction `ν` costs at least `m` above the
  zero-flux ground `E_{g₀}` of the same slice) and `count` (`Σ_j e^{−(F_j − E_{g₀}) t₀} ≤ Co`, the odd heat trace
  at the physical time `t₀`, relative to the zero-flux ground).
* `tsum_odd_le`: `gap`, `count`, `t₀ ≤ t` give `Σ_j e^{−F_j t} ≤ e^{−E_{g₀} t} · Co e^{m t₀} e^{−m t}`.
* `exp_ground_le_hs`: `EigenLevels` gives `e^{−E_{g₀} t} ≤ hs(trivKN)` (`hs_trivKN_pos` forces summability).
* **`one_sub_zR_le_of_oddLevels`**: with `hs(trivKN) ≤ hs(halfKN)`, `1 − zR ≤ 2 Co e^{m t₀} e^{−m n a}`.

Why the fields of `ScaleControl.SliceControl` do not give this (argued from proved statements, not a
declaration): every operator in `SliceControl` is `trivKN`, which annihilates every winding state
(`ElectricLoops.trivKN_windState`), so `bridge` reads `0` on the winding loop states and the block contraction
`contract` (through `KernelNear` and `BoxFocusTest.cov_le_of_kernelNear`) bounds covariances of the
infinite-volume `periodicState` on `ℤ⁴`, which has no flux sectors; and the (E1) input
(`LoopsGenerate.excited_mem_closure_loops`) is about the excited levels of `trivKN` only. The winding transfer
bound runs one way only (`ElectricLoops.winding_transfer_le`: a state's transfer is at most the sector trace);
a bound on finitely many winding states does not bound a Hilbert–Schmidt sum over the whole sector. So the odd
sector enters as its own levels with its own gap and count, `OddLevels`, the odd-sector counterpart of
`EigenLevels + ZeroFluxGap + ZeroFluxCount`.

Circularity check (argued): `OddLevels` is not `VortexCostAt`, `ElecCostAt` or `RunSeed`. Its `gap` is a
spectral statement on the eigenvalues of the odd sector kernels and its `count` a heat-trace bound at the fixed
time `t₀`; the trace bound at the window time `t = n a` is derived from both. With the eigen clauses dropped,
the one-level choice `F = −log(oddFlux)/t` would make `gap` the trace bound itself; the eigen clauses tie `F`
to the eigenvalues of the real sector kernels, which excludes that choice (argued: an orthonormal family of
eigenfunctions of the odd sector kernels with nonzero eigenvalues has `Σ λ_j² ≤ Σ_ψ hs(rsec ψ)`, with equality
only for a complete family, so `trace` forces `F` to be the full odd spectrum; not proved in the tree). As a
statement on one slice, `OddLevels` is strictly stronger than `VortexCostAt`: a level-uniform odd gap plus a
heat-trace bound at a fixed time.

## 2. The run (proved)

* `SliceRun`: a `ScaleControl.SliceControl` record and, for every `ν`, an `OddLevels` record on the same
  zero-flux levels (`ctl.g₀`, `ctl.E`) at constants `m, t₀, Co`.
* `ScaleControlRunAt … ℓ`: the sign conditions of `ScaleControlAt` and, eventually in `β`, a `SliceRun` at every
  slice of the window. `scaleControlAt_of_runAt` forgets the odd records.
* `vortexCostAt_of_runAt`: `VortexCostAt m (2 Co e^{m t₀}) ℓ`.
* `ScaleControlRun`: constants fixed once (`c, c', σ, δ, α, V, D, B, t₀, Cc, m, Co`, an `ℓ₀ > 0`) with
  `diagRate c c' σ δ (2ℓ₀) > 0`, `m > 0`, `Cc, Co ≥ 0`, and `ScaleControlRunAt` at them frequently in `ℓ`.
* `diagRate_le_sup`: `diagRate c c' σ δ t ≤ √(c c' σ) + c σ δ/2` (`t > 0`), so the (T) constant
  `2 Cc e^{diagRate(2ℓ) t₀}` of `ScaleControl.hiddenCostAt_of_scaleControlAt` is bounded uniformly in `ℓ`.
* **`runSeed_two_of_scaleControlRun`**: `ScaleControlRun → WDeltaRun.RunSeed 2`, at
  `σ* = min(diagRate(2ℓ₀), m)`, `A* = max(2 Cc e^{(√(c c' σ) + c σ δ/2) t₀}, 2 Co e^{m t₀})`, through
  `FluxCost.runSeed_two_iff_vortex`; (T) at `ℓ ≥ ℓ₀` uses `ScaleControl.diagRate_mono`.
* `InputAudit.not_scaleControlRun` refutes `ScaleControlRun` under the argued growth of the zero-flux level count, so no `ClayStatementAt` capstone is stated from it.

DERIVED (module-wide): `2` is `SU(2)` and the factor of `1 − zR = 2 · oddFlux / hs`; `2` and `5` the window of
`FluxCost.VortexCostAt`; `2ℓ₀` the window's lower end at `ℓ₀`; `√(c c' σ) + c σ δ/2` the `t → ∞` value of
`diagRate` (`ScaleControl.diagRate_eq` with the logarithm `≤ 0`).
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ScaleControlRun

open MeasureTheory Filter
open MassGap.ScaleControl (SliceControl ScaleControlAt diagRate_eq diagRate_mono hiddenCostAt_of_scaleControlAt)
open MassGap.CentreSectorSeedN (trivKN hSN halfKN)
open MassGap.TensionFloor (Slice EigenLevels)
open MassGap.AsymptoticScaling (aRun aRun_pos)
open MassGap.LoopZoom (diagRate)
open MassGap.KernelPower (hs)
open MassGap.VortexAperture (oddFlux)
open MassGap.GapSideVortexRect (zR Lc)

/-! ## 1. The odd electric-flux sector in its levels, and (V) -/

/-- **The odd electric-flux sector of the plane `(i, ν)` in its levels**, relative to the zero-flux ground
`E g₀`: eigenfunctions of the odd real sector kernels of `halfKN`, eigenvalues `λ_j² = e^{−F_j n a}`
exhausting `oddFlux` (bookkeeping, spectral theorem), the gap `F_j ≥ E g₀ + m` and the count at `t₀`
(physics, open). -/
structure OddLevels (β : ℝ) (n : ℕ) (i : Fin 4) (ν : {j : Fin 4 // j ≠ i}) {ι : Type} (g₀ : ι)
    (E : ι → ℝ) (m t₀ Co : ℝ) : Type 1 where
  /-- Index type of the odd levels. -/
  κ : Type
  /-- The sector character of each level. -/
  ψ : κ → AddChar (SliceCentreAction.Cen i 2) ℂ
  /-- The eigenfunctions. -/
  φ : κ → Slice n i → ℝ
  /-- The eigenvalues. -/
  lam : κ → ℝ
  /-- The level energies. -/
  F : κ → ℝ
  /-- Bookkeeping: each level lies in a sector odd under the twist `e_ν`. -/
  odd : ∀ j, ψ j (Pi.single ν 1) ≠ 1
  /-- Bookkeeping: orthonormal eigenfunctions of the odd real sector kernels. -/
  norm : ∀ j, ∫ x, φ j x * φ j x ∂(hSN 2 n i) = 1
  orth : ∀ j k, j ≠ k → ∫ x, φ j x * φ k x ∂(hSN 2 n i) = 0
  eigen : ∀ j x, ∫ y, ElectricLoops.rsec (halfKN 2 β n i)
      (SliceCentreAction.act (μ := i) (T := CentreSectorSeed.Tr n i) (N := 2)) (ψ j) x y * φ j y
        ∂(hSN 2 n i) = lam j * φ j x
  energy : ∀ j, lam j ^ 2 = Real.exp (-(F j * ((n : ℝ) * aRun 2 β)))
  /-- Bookkeeping: the levels exhaust the odd trace. -/
  trace : oddFlux β n i ν = ∑' j, Real.exp (-(F j * ((n : ℝ) * aRun 2 β)))
  /-- Physics, open: winding electric flux costs at least `m` above the zero-flux ground. -/
  gap : ∀ j, E g₀ + m ≤ F j
  /-- Physics, open: the odd heat trace at `t₀`, relative to the zero-flux ground, is at most `Co`. -/
  count_summable : Summable (fun j => Real.exp (-((F j - E g₀) * t₀)))
  count : ∑' j, Real.exp (-((F j - E g₀) * t₀)) ≤ Co

/-- **Gap and count carry the odd trace to every later time**:
`Σ_j e^{−F_j t} ≤ e^{−E₀ t} · Co e^{m t₀} e^{−m t}` at `t ≥ t₀`. -/
theorem tsum_odd_le {κ : Type} {F : κ → ℝ} {E₀ m t₀ t Co : ℝ} (hgap : ∀ j, E₀ + m ≤ F j)
    (hs0 : Summable (fun j => Real.exp (-((F j - E₀) * t₀))))
    (hc : ∑' j, Real.exp (-((F j - E₀) * t₀)) ≤ Co) (ht : t₀ ≤ t) :
    ∑' j, Real.exp (-(F j * t))
      ≤ Real.exp (-(E₀ * t)) * (Co * Real.exp (m * t₀) * Real.exp (-(m * t))) := by
  set K := Real.exp (-(E₀ * t)) * Real.exp (-(m * (t - t₀))) with hK
  have hK0 : 0 ≤ K := by positivity
  have hterm : ∀ j, Real.exp (-(F j * t)) ≤ K * Real.exp (-((F j - E₀) * t₀)) := by
    intro j
    rw [hK, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : m * (t - t₀) ≤ (F j - E₀) * (t - t₀) :=
      mul_le_mul_of_nonneg_right (by linarith [hgap j]) (sub_nonneg.2 ht)
    nlinarith
  have hsK : Summable (fun j => K * Real.exp (-((F j - E₀) * t₀))) := hs0.mul_left K
  have hsL : Summable (fun j => Real.exp (-(F j * t))) :=
    Summable.of_nonneg_of_le (fun j => (Real.exp_pos _).le) hterm hsK
  have hρ : Real.exp (-(m * (t - t₀))) = Real.exp (m * t₀) * Real.exp (-(m * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc ∑' j, Real.exp (-(F j * t)) ≤ ∑' j, K * Real.exp (-((F j - E₀) * t₀)) :=
        hsL.tsum_le_tsum hterm hsK
    _ = K * ∑' j, Real.exp (-((F j - E₀) * t₀)) := tsum_mul_left
    _ ≤ K * Co := mul_le_mul_of_nonneg_left hc hK0
    _ = Real.exp (-(E₀ * t)) * (Co * Real.exp (m * t₀) * Real.exp (-(m * t))) := by
        rw [hK, hρ]; ring

/-- **The zero-flux ground weight is at most the zero-flux trace**: `e^{−E_{g₀} n a} ≤ hs(trivKN)`. -/
theorem exp_ground_le_hs {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {i : Fin 4} {ι : Type} {g₀ : ι} {E : ι → ℝ}
    {φ : ι → Slice n i → ℝ} {μ : ι → ℝ} (hL : EigenLevels β n i g₀ E φ μ) :
    Real.exp (-(E g₀ * ((n : ℝ) * aRun 2 β))) ≤ hs (hSN 2 n i) (trivKN 2 β n i) := by
  have hpos := CentreSectorSeedN.hs_trivKN_pos (N := 2) hβ n i
  rw [hL.hs_eq] at hpos ⊢
  have hsum : Summable (fun j => Real.exp (-(E j * ((n : ℝ) * aRun 2 β)))) := by
    by_contra h
    rw [tsum_eq_zero_of_not_summable h] at hpos
    exact lt_irrefl _ hpos
  exact hsum.le_tsum g₀ (fun j _ => (Real.exp_pos _).le)

/-- **(V) on one slice from the odd levels**: `1 − zR (Lc n i) i ν β ≤ 2 Co e^{m t₀} e^{−m n a}`. -/
theorem one_sub_zR_le_of_oddLevels {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) (i : Fin 4)
    (ν : {j : Fin 4 // j ≠ i}) {ι : Type} {g₀ : ι} {E : ι → ℝ} {φ : ι → Slice n i → ℝ} {μ : ι → ℝ}
    (hL : EigenLevels β n i g₀ E φ μ) {m t₀ Co : ℝ} (O : OddLevels β n i ν g₀ E m t₀ Co)
    (ht : t₀ ≤ (n : ℝ) * aRun 2 β) :
    1 - zR (Lc n i) i ν.1 β
      ≤ 2 * Co * Real.exp (m * t₀) * Real.exp (-(m * ((n : ℝ) * aRun 2 β))) := by
  rw [VortexAperture.one_sub_zR_eq_oddFlux hβ hn he i ν]
  have hH := CentreSectorSeedN.hs_halfKN_pos (N := 2) hβ n i
  have hle := CentreSectorSeedN.hs_trivKN_le (N := 2) hβ n i
  have hG := exp_ground_le_hs hβ hL
  have hO : oddFlux β n i ν ≤ Real.exp (-(E g₀ * ((n : ℝ) * aRun 2 β)))
      * (Co * Real.exp (m * t₀) * Real.exp (-(m * ((n : ℝ) * aRun 2 β)))) := by
    rw [O.trace]
    exact tsum_odd_le O.gap O.count_summable O.count ht
  have hCo : 0 ≤ Co := (tsum_nonneg fun j => (Real.exp_pos _).le).trans O.count
  have hR : 0 ≤ Co * Real.exp (m * t₀) * Real.exp (-(m * ((n : ℝ) * aRun 2 β))) := by positivity
  rw [div_le_iff₀ hH]
  have := mul_le_mul_of_nonneg_right (hG.trans hle) hR
  nlinarith

/-! ## 2. The run -/

/-- **One slice of the run**: a `SliceControl` record and, for every transverse `ν`, the odd levels on the
same zero-flux levels. -/
structure SliceRun (c c' σ δ α V D B t₀ Cc m Co : ℝ) (β : ℝ) (n : ℕ) (i : Fin 4) : Type 1 where
  ctl : SliceControl c c' σ δ α V D B t₀ Cc β n i
  odd : ∀ ν : {j : Fin 4 // j ≠ i}, OddLevels β n i ν ctl.g₀ ctl.E m t₀ Co

/-- **Scale control with the odd levels at the window `[2ℓ, 5ℓ]`**: the sign conditions of `ScaleControlAt`
and, eventually in `β`, a `SliceRun` at every power-of-two side `n ≥ 2` with `n a ∈ [2ℓ, 5ℓ]` and every step. -/
structure ScaleControlRunAt (c c' σ δ α V D B t₀ Cc m Co ℓ : ℝ) : Prop where
  c_nonneg : 0 ≤ c
  c'_nonneg : 0 ≤ c'
  σ_nonneg : 0 ≤ σ
  step_pos : 0 < c * σ * δ
  α_nonneg : 0 ≤ α
  V_nonneg : 0 ≤ V
  D_nonneg : 0 ≤ D
  t₀_nonneg : 0 ≤ t₀
  t₀_le : t₀ ≤ 2 * ℓ
  slices : ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
    2 * ℓ ≤ (n : ℝ) * aRun 2 β → (n : ℝ) * aRun 2 β ≤ 5 * ℓ → ∀ i : Fin 4,
      Nonempty (SliceRun c c' σ δ α V D B t₀ Cc m Co β n i)

/-- Forgetting the odd levels gives `ScaleControlAt`. -/
theorem scaleControlAt_of_runAt {c c' σ δ α V D B t₀ Cc m Co ℓ : ℝ}
    (h : ScaleControlRunAt c c' σ δ α V D B t₀ Cc m Co ℓ) : ScaleControlAt c c' σ δ α V D B t₀ Cc ℓ where
  c_nonneg := h.c_nonneg
  c'_nonneg := h.c'_nonneg
  σ_nonneg := h.σ_nonneg
  step_pos := h.step_pos
  α_nonneg := h.α_nonneg
  V_nonneg := h.V_nonneg
  D_nonneg := h.D_nonneg
  t₀_nonneg := h.t₀_nonneg
  t₀_le := h.t₀_le
  slices := by
    filter_upwards [h.slices] with β hS n hn h2 hlo hhi i
    obtain ⟨R⟩ := hS n hn h2 hlo hhi i
    exact ⟨R.ctl⟩

/-- **(V) at the window**: `VortexCostAt m (2 Co e^{m t₀}) ℓ`. -/
theorem vortexCostAt_of_runAt {c c' σ δ α V D B t₀ Cc m Co ℓ : ℝ}
    (h : ScaleControlRunAt c c' σ δ α V D B t₀ Cc m Co ℓ) :
    FluxCost.VortexCostAt m (2 * Co * Real.exp (m * t₀)) ℓ := by
  filter_upwards [h.slices, eventually_ge_atTop (0 : ℝ)] with β hS hβ0 n hn h2 hlo hhi i ν
  obtain ⟨R⟩ := hS n hn h2 hlo hhi i
  exact one_sub_zR_le_of_oddLevels hβ0 h2 (FluxCost.even_of_pow2 hn h2) i ν R.ctl.levels (R.odd ν)
    (h.t₀_le.trans hlo)

/-- **The run**: constants fixed once, with a positive (T) rate at `ℓ₀ > 0` and a positive odd gap `m`, and
`ScaleControlRunAt` at them frequently in `ℓ`. -/
def _root_.MassGap.ScaleControlRun : Prop :=
  ∃ c c' σ δ α V D B t₀ Cc m Co ℓ₀ : ℝ, 0 < ℓ₀ ∧ 0 < diagRate c c' σ δ (2 * ℓ₀) ∧ 0 < m ∧ 0 ≤ Cc ∧
    0 ≤ Co ∧ ∃ᶠ ℓ in atTop, ScaleControlRunAt c c' σ δ α V D B t₀ Cc m Co ℓ

/-- **`diagRate` is at most its `t → ∞` value** `√(c c' σ) + c σ δ/2` (`t > 0`, `c σ δ > 0`). -/
theorem diagRate_le_sup {c c' σ δ t : ℝ} (ht : 0 < t) (hq : 0 < c * σ * δ) :
    diagRate c c' σ δ t ≤ Real.sqrt (c * c' * σ) + c * σ * δ / 2 := by
  rw [diagRate_eq ht hq]
  have he : Real.exp (-(c * σ * δ * t / 4)) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by have := mul_pos hq ht; linarith)
  have hL : Real.log (1 - Real.exp (-(c * σ * δ * t / 4))) ≤ 0 :=
    Real.log_nonpos (by linarith) (by linarith [Real.exp_pos (-(c * σ * δ * t / 4))])
  have : 2 * Real.log (1 - Real.exp (-(c * σ * δ * t / 4))) / t ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) ht.le
  linarith

/-- `HiddenCostAt` at a smaller rate and a larger constant. -/
theorem hiddenCostAt_weaken {σ σ' A A' ℓ : ℝ} (hσ : σ' ≤ σ) (hA0 : 0 ≤ A) (hA : A ≤ A')
    (h : ObserverTheory.HiddenCostAt 2 σ A ℓ) : ObserverTheory.HiddenCostAt 2 σ' A' ℓ := by
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with β hβ hβ0 n hn h2 hlo hup i
  have hx : 0 ≤ (n : ℝ) * aRun 2 β := mul_nonneg (Nat.cast_nonneg n) (aRun_pos (by norm_num) hβ0).le
  have he : Real.exp (-(σ * ((n : ℝ) * aRun 2 β))) ≤ Real.exp (-(σ' * ((n : ℝ) * aRun 2 β))) :=
    Real.exp_le_exp.2 (by nlinarith)
  refine (hβ n hn h2 hlo hup i).trans ?_
  calc A * Real.exp (-(σ * ((n : ℝ) * aRun 2 β))) ≤ A * Real.exp (-(σ' * ((n : ℝ) * aRun 2 β))) :=
        mul_le_mul_of_nonneg_left he hA0
    _ ≤ A' * Real.exp (-(σ' * ((n : ℝ) * aRun 2 β))) :=
        mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le

/-- `VortexCostAt` at a smaller rate and a larger constant. -/
theorem vortexCostAt_weaken {σ σ' A A' ℓ : ℝ} (hσ : σ' ≤ σ) (hA0 : 0 ≤ A) (hA : A ≤ A')
    (h : FluxCost.VortexCostAt σ A ℓ) : FluxCost.VortexCostAt σ' A' ℓ := by
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with β hβ hβ0 n hn h2 hlo hup i ν
  have hx : 0 ≤ (n : ℝ) * aRun 2 β := mul_nonneg (Nat.cast_nonneg n) (aRun_pos (by norm_num) hβ0).le
  have he : Real.exp (-(σ * ((n : ℝ) * aRun 2 β))) ≤ Real.exp (-(σ' * ((n : ℝ) * aRun 2 β))) :=
    Real.exp_le_exp.2 (by nlinarith)
  refine (hβ n hn h2 hlo hup i ν).trans ?_
  calc A * Real.exp (-(σ * ((n : ℝ) * aRun 2 β))) ≤ A * Real.exp (-(σ' * ((n : ℝ) * aRun 2 β))) :=
        mul_le_mul_of_nonneg_left he hA0
    _ ≤ A' * Real.exp (-(σ' * ((n : ℝ) * aRun 2 β))) :=
        mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le

/-- **The full gap input from the run**: `ScaleControlRun → WDeltaRun.RunSeed 2`. -/
theorem runSeed_two_of_scaleControlRun (h : ScaleControlRun) : WDeltaRun.RunSeed 2 := by
  obtain ⟨c, c', σ, δ, α, V, D, B, t₀, Cc, m, Co, ℓ₀, hℓ₀, hpos, hm, hCc, hCo, hfr⟩ := h
  set Mx := Real.sqrt (c * c' * σ) + c * σ * δ / 2
  refine FluxCost.runSeed_two_iff_vortex.2
    ⟨min (diagRate c c' σ δ (2 * ℓ₀)) m,
      max (2 * Cc * Real.exp (Mx * t₀)) (2 * Co * Real.exp (m * t₀)), lt_min hpos hm, ?_⟩
  refine (hfr.and_eventually (eventually_ge_atTop ℓ₀)).mono fun ℓ ⟨hR, hℓ⟩ => ⟨?_, ?_⟩
  · exact vortexCostAt_weaken (min_le_right _ _) (by positivity) (le_max_right _ _)
      (vortexCostAt_of_runAt hR)
  · have hS := scaleControlAt_of_runAt hR
    have h2ℓ₀ : 0 < 2 * ℓ₀ := by linarith
    have h2ℓ : 0 < 2 * ℓ := by linarith
    have hmono := diagRate_mono (c' := c') hR.step_pos h2ℓ₀ (by linarith : 2 * ℓ₀ ≤ 2 * ℓ)
    have hsup := diagRate_le_sup (c' := c') h2ℓ hR.step_pos
    have hA : 2 * Cc * Real.exp (diagRate c c' σ δ (2 * ℓ) * t₀) ≤ 2 * Cc * Real.exp (Mx * t₀) :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hsup hR.t₀_nonneg)) (by positivity)
    exact hiddenCostAt_weaken ((min_le_left _ _).trans hmono) (by positivity)
      (hA.trans (le_max_left _ _)) (hiddenCostAt_of_scaleControlAt hS)

end MassGap.ScaleControlRun

end

#print axioms MassGap.ScaleControlRun.tsum_odd_le
#print axioms MassGap.ScaleControlRun.exp_ground_le_hs
#print axioms MassGap.ScaleControlRun.one_sub_zR_le_of_oddLevels
#print axioms MassGap.ScaleControlRun.scaleControlAt_of_runAt
#print axioms MassGap.ScaleControlRun.vortexCostAt_of_runAt
#print axioms MassGap.ScaleControlRun.diagRate_le_sup
#print axioms MassGap.ScaleControlRun.hiddenCostAt_weaken
#print axioms MassGap.ScaleControlRun.vortexCostAt_weaken
#print axioms MassGap.ScaleControlRun.runSeed_two_of_scaleControlRun
