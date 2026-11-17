import MassGap.PuritySpectralMeasure
import MassGap.ShellMeasure

/-!
# MassGap.PurityShellFloor — Proposition A.1 for a self-adjoint operator with spectrum in `[0, 1]` on a Hilbert space

Proposition A.1 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford
and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510,
`Paper-2/Paper-2.pdf`), for a self-adjoint `a` on a complex Hilbert space with spectrum in
`[0, 1]` and real time `t > 0`. The spectral measure `σ_u` of `u` on `[0, 1]` is
`MassGap.ShellMeasure.vecMeasure`; its push-forward under the energy map
`E(λ) = −log λ` (`∞` at `λ = 0`, `MassGap.PuritySpectralMeasure.energy`) is a measure on `[0, ∞]`
that carries the mass at `λ = 0` at `E = ∞`.

* `energyMeasure`: `μ_u = E_* σ_u` on `[0, ∞]`.
* `energyMeasure_real_univ`, `isProbability`: `μ_u([0, ∞]) = ‖u‖²`, a probability measure for
  `‖u‖ = 1`.
* `re_inner_powT_eq_integral`: `Re ⟪u, a^t u⟫ = ∫ e^{−tE} dμ_u` for real `t > 0`.
* `shell_floor`: Proposition A.1. `‖u‖ = 1`, `Re ⟪u, a^t u⟫ ≥ c > 0` give
  `σ_u([e^{−Λ}, 1]) ≥ c/(2 − c)` for `Λ = t⁻¹ log(2/c)`.
-/

namespace MassGap.PurityShellFloor

open MeasureTheory Real Set
open scoped ENNReal
open MassGap.ShellMeasure (vecMeasure re_inner_cfc_eq_integral vecMeasure_real_univ)
open MassGap.PuritySpectralMeasure (energy lap_energy_rpow measurable_energy energy_le_iff)
open MassGap.ContinuumTimeGroup (powT)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- `x ↦ E(x)` is measurable on `[0, 1]`. -/
theorem measurable_energy_val : Measurable (fun x : Icc (0 : ℝ) 1 => energy x.1) :=
  measurable_energy.comp measurable_subtype_coe

/-- The energy spectral measure of `u`: `σ_u` pushed forward under `λ ↦ E(λ)`. -/
noncomputable def energyMeasure (a : E →L[ℂ] E) (u : E) : Measure ℝ≥0∞ :=
  (vecMeasure a u).map (fun x => energy x.1)

/-- `μ_u([0, ∞]) = ‖u‖²`. -/
theorem energyMeasure_real_univ {a : E →L[ℂ] E} (ha : IsSelfAdjoint a)
    (hsp : spectrum ℝ a ⊆ Icc 0 1) (u : E) : (energyMeasure a u).real univ = ‖u‖ ^ 2 := by
  rw [← vecMeasure_real_univ ha hsp u, energyMeasure, measureReal_def, measureReal_def,
    Measure.map_apply measurable_energy_val MeasurableSet.univ, preimage_univ]

/-- `μ_u` is a probability measure for `‖u‖ = 1`. -/
theorem isProbability {a : E →L[ℂ] E} (ha : IsSelfAdjoint a) (hsp : spectrum ℝ a ⊆ Icc 0 1)
    {u : E} (hu : ‖u‖ = 1) : IsProbabilityMeasure (energyMeasure a u) := by
  have h := energyMeasure_real_univ ha hsp u
  rw [hu, one_pow] at h
  haveI : IsFiniteMeasure (energyMeasure a u) := by unfold energyMeasure; infer_instance
  refine ⟨?_⟩
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), ← measureReal_def, h, ENNReal.ofReal_one]

/-- The time correlator is the Laplace transform of `μ_u`: `Re ⟪u, a^t u⟫ = ∫ e^{−tE} dμ_u` for
real `t > 0`. -/
theorem re_inner_powT_eq_integral {a : E →L[ℂ] E} (hsp : spectrum ℝ a ⊆ Icc 0 1) (u : E) {t : ℝ}
    (ht : 0 < t) :
    (inner ℂ u (powT a t u)).re = ∫ x, PurityLaplace.lap t x ∂(energyMeasure a u) := by
  rw [energyMeasure, integral_map measurable_energy_val.aemeasurable
    (PurityLaplace.lap_measurable t).aestronglyMeasurable]
  have hrep := re_inner_cfc_eq_integral hsp u (Real.continuous_rpow_const ht.le)
  beta_reduce at hrep
  rw [show powT a t = cfc (fun x : ℝ => x ^ t) a from rfl, hrep]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
    (lap_energy_rpow x.2.1 x.2.2 ht).symm)

/-- Proposition A.1 on a Hilbert space: for `‖u‖ = 1` and `Re ⟪u, a^t u⟫ ≥ c > 0` at
real `t > 0`, the spectral weight of `u` on `[e^{−Λ}, 1]`, `Λ = t⁻¹ log(2/c)`, is at least
`c/(2 − c)`. -/
theorem shell_floor {a : E →L[ℂ] E} (ha : IsSelfAdjoint a) (hsp : spectrum ℝ a ⊆ Icc 0 1)
    {u : E} (hu : ‖u‖ = 1) {t c : ℝ} (ht : 0 < t) (hc : 0 < c)
    (hR : c ≤ (inner ℂ u (powT a t u)).re) :
    c / (2 - c) ≤ (vecMeasure a u).real {x | exp (-(log (2 / c) / t)) ≤ x.1} := by
  haveI := isProbability ha hsp hu
  have hR' := hR.trans_eq (re_inner_powT_eq_integral hsp u ht)
  have hfl := PurityLaplace.laplace_floor ht hc hR'
  have hc1 : c ≤ 1 := hR'.trans (PurityLaplace.integral_lap_le_one ht.le _)
  have hΛ : 0 ≤ log (2 / c) / t :=
    div_nonneg (log_nonneg (by rw [le_div_iff₀ hc]; linarith)) ht.le
  refine hfl.trans_eq ?_
  rw [energyMeasure, measureReal_def, measureReal_def,
    Measure.map_apply measurable_energy_val measurableSet_Iic]
  congr 2
  ext x
  simp only [mem_preimage, mem_Iic, mem_setOf_eq, energy_le_iff hΛ]

end MassGap.PurityShellFloor

#print axioms MassGap.PurityShellFloor.energyMeasure_real_univ
#print axioms MassGap.PurityShellFloor.isProbability
#print axioms MassGap.PurityShellFloor.re_inner_powT_eq_integral
#print axioms MassGap.PurityShellFloor.shell_floor
