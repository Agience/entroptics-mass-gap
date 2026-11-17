import Mathlib
import MassGap.PurityOddTimeLower
import MassGap.PurityPlaqCount
import MassGap.GaugeInstances
import MassGap.HaarVariance

/-!
# MassGap.PurityOddTimeWilson — `Ψ_T(2β) ≥ 0` at odd `T` on the `SU(N)` Wilson lattice

The lower bound of Corollary 8.2 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood,
*Thermal Purity Bounds…*, at odd `T = 2j + 1`, `j ≥ 1`, for the plaquette action on the 4-torus with gauge
group `SU(N)`, `N ≥ 2`, at `β > 0`, every spatial extent at least `2`.

* `ZRG_SU_eq_ZR`: the general-group partition function `RectWilsonG.ZRG` at `G = SU(N)` is the
  `SU(N)` partition function `RectWilson.ZR`.
* `nontrivial_SU`: `SU(N)` at `N ≥ 2` is nontrivial (`HaarVariance.flipEl`).
* `log_ZR_double_nonneg_odd`, `psi_nonneg_wilson_odd`: `2 log Z(L) − log Z(L′) ≥ 0` and
  `Ψ_T(2β) ≥ 0` at odd `T = L μ`, from `PurityOddTimeLower.ZRG_defect_odd_nonneg` and
  `PurityPlaqCount.psi_eq_log_ZR`.

DERIVED (module-wide): `2` the least rank of `SU(N)` with an element other than `1`, the least
spatial extent, and the doubling `L′ μ = 2 L μ`; `4` the dimension.
-/

namespace MassGap.PurityOddTimeWilson

open MeasureTheory MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.CompactGauge
  MassGap.RectWilson MassGap.RectWilsonG MassGap.PurityPlaqCount

/-- `ZRG` over `SU(N)` is `ZR`: the gauge-group instance of `SU(N)` carries the Wilson density
(`GaugeInstances.wilsonDensityG_SU`). -/
theorem ZRG_SU_eq_ZR {N : ℕ} [NeZero N] (L : Fin 4 → ℕ) (β : ℝ) :
    ZRG (SUN.SU N) L β = ZR L N β := rfl

/-- `SU(N)` at `N ≥ 2` has an element other than `1`. -/
theorem nontrivial_SU {N : ℕ} (hN : 2 ≤ N) : Nontrivial (SUN.SU N) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  exact nontrivial_of_ne (HaarVariance.flipEl m) 1 fun e =>
    HaarVariance.reTr_flipEl_ne_reTr_one m (by rw [e])

/-- `2 log Z(L₁) − log Z(L₂) ≥ 0` on the `SU(N)` Wilson lattice at odd `T = L₁ μ = 2j + 1`,
`j ≥ 1`, `L₂ μ = 2T`, equal spatial extents, each at least `2`, `β > 0`, `N ≥ 2`. -/
theorem log_ZR_double_nonneg_odd {N : ℕ} (hN : 2 ≤ N) {β : ℝ} (hβ : 0 < β)
    {L₁ L₂ : Fin 4 → ℕ} (μ : Fin 4) (hL : ∀ i, i ≠ μ → L₂ i = L₁ i) (h2 : L₂ μ = 2 * L₁ μ)
    (hS : ∀ i, i ≠ μ → 2 ≤ L₁ i) (j : ℕ) (hj : 1 ≤ j) (hT : L₁ μ = 2 * j + 1) :
    0 ≤ 2 * Real.log (ZR L₁ N β) - Real.log (ZR L₂ N β) := by
  haveI : NeZero N := ⟨by omega⟩
  haveI := nontrivial_SU hN
  have htr : RectWilson.tr L₂ μ = RectWilson.tr L₁ μ := funext fun i => hL i.1 i.2
  have h := PurityOddTimeLower.ZRG_defect_odd_nonneg (G := SUN.SU N) (μ := μ) hβ
    (fun ν => hS ν.1 ν.2) htr j hj hT (by rw [h2, hT])
  rw [ZRG_SU_eq_ZR, ZRG_SU_eq_ZR] at h
  linarith

/-- The lower bound `Ψ_T(2β) ≥ 0` of Corollary 8.2 on the `SU(N)` Wilson lattice at odd
`T = L₁ μ = 2j + 1`, `j ≥ 1`, `β > 0`, `N ≥ 2`, every spatial extent at least `2`: `Ψ_T(2β)` is real
(`psi_eq_log_ZR`) and nonnegative (`log_ZR_double_nonneg_odd`). -/
theorem psi_nonneg_wilson_odd {N : ℕ} (hN : 2 ≤ N) {β : ℝ} (hβ : 0 < β) {L₁ L₂ : Fin 4 → ℕ}
    (μ : Fin 4) (hL : ∀ i, i ≠ μ → L₂ i = L₁ i) (h2 : L₂ μ = 2 * L₁ μ)
    (hS : ∀ i, i ≠ μ → 2 ≤ L₁ i) (j : ℕ) (hj : 1 ≤ j) (hT : L₁ μ = 2 * j + 1) :
    0 ≤ (PurityCancel.psi
      (Measure.pi fun _ : RLink L₁ => probHaar (SUN.SU N)) (plaqAction L₁ N)
      (Measure.pi fun _ : RLink L₂ => probHaar (SUN.SU N)) (plaqAction L₂ N)
      ((2 * β : ℝ) : ℂ)).re := by
  rw [psi_eq_log_ZR (by omega) μ hL h2 β, Complex.ofReal_re]
  exact log_ZR_double_nonneg_odd hN hβ μ hL h2 hS j hj hT

end MassGap.PurityOddTimeWilson

#print axioms MassGap.PurityOddTimeWilson.ZRG_SU_eq_ZR
#print axioms MassGap.PurityOddTimeWilson.nontrivial_SU
#print axioms MassGap.PurityOddTimeWilson.log_ZR_double_nonneg_odd
#print axioms MassGap.PurityOddTimeWilson.psi_nonneg_wilson_odd
