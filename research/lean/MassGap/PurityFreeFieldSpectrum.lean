import Mathlib
import MassGap.PurityFreeField
import MassGap.PurityFreeFieldLimit

/-!
# MassGap.PurityFreeFieldSpectrum — the one-particle measure of Proposition B.1 has no gap

Proposition B.1 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford
and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510,
`Paper-2/Paper-2.pdf`). The one-particle space of the generalized free field with squared-mass
density `ρ(s) = c s²/log²(e + s)` has measure `ρ(s) ds d³p/(2E)` on `(0, ∞) × ℝ³`, energy
`E(s, p) = √(|p|² + s)`.

* `energy`, `density`, `oneParticle`: `E`, `ρ(s)/(2E)` and the measure
  `ρ(s)/(2E) · (ds|_{(0,∞)} ⊗ d³p)`; `lowRegion ε`: `0 < s < ε²/4`, `|p| < ε/2`.
* `energy_lowRegion`: energy in `(0, ε)` on `lowRegion ε` (`PurityFreeField.energy_mem`).
* `rho_pos`, `density_pos`: `ρ(s) > 0` and `ρ(s)/(2E) > 0` at `c > 0`, `s > 0`.
* `oneParticle_lowRegion_pos`, `low_energy_pos`: at `c > 0`, `ε > 0`, `lowRegion ε` and the set
  of energies in `(0, ε)` have positive measure.
* `energy_pos_ae`: `E > 0` almost everywhere.
* `no_gap`, `no_mass_gap`: at `c > 0` no `m > 0` has `E ≥ m` almost everywhere.

Not formalized here: the Wightman construction, Fock space, locality and positivity of the
generalized free field, and the identification of `oneParticle` with its one-particle spectral
measure (taken here as its definition); uniqueness of the vacuum.

DERIVED (module-wide): `2` the mass-shell normalization `2E` and the square in `|p|²`; `4 = 2²`
in `ε²/4` from `|p| < ε/2`, `s < ε²/4` giving `|p|² + s < ε²/2 < ε²`; `3` the spatial dimension.
-/

namespace MassGap.PurityFreeFieldSpectrum

open Real MeasureTheory Set Metric
open MassGap.PurityFreeFieldLimit (rho one_le_log)

/-- The mass-momentum space `(s, p)`, `s` the squared mass, `p ∈ ℝ³`. -/
abbrev P := ℝ × EuclideanSpace ℝ (Fin 3)

/-- `E(s, p) = √(|p|² + s)`. -/
noncomputable def energy (x : P) : ℝ := sqrt (‖x.2‖ ^ 2 + x.1)

/-- `ρ(s)/(2E)`. -/
noncomputable def density (c : ℝ) (x : P) : ℝ := rho c x.1 / (2 * energy x)

/-- The base measure `ds|_{(0,∞)} ⊗ d³p`. -/
noncomputable def base : Measure P :=
  (volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3)))

/-- The one-particle measure `ρ(s) ds d³p/(2E)`. -/
noncomputable def oneParticle (c : ℝ) : Measure P :=
  base.withDensity fun x => ENNReal.ofReal (density c x)

/-- `0 < s < ε²/4`, `|p| < ε/2`. -/
def lowRegion (ε : ℝ) : Set P := Ioo 0 (ε ^ 2 / 4) ×ˢ ball 0 (ε / 2)

theorem energy_pos {x : P} (hx : 0 < x.1) : 0 < energy x := sqrt_pos.2 (by positivity)

theorem energy_lowRegion {ε : ℝ} {x : P} (hx : x ∈ lowRegion ε) :
    0 < energy x ∧ energy x < ε := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hx
  exact PurityFreeField.energy_mem h1 h2 (norm_nonneg _) (mem_ball_zero_iff.1 h3)

theorem rho_pos {c s : ℝ} (hc : 0 < c) (hs : 0 < s) : 0 < rho c s := by
  have h := one_le_log hs.le
  exact div_pos (mul_pos hc (pow_pos hs 2)) (pow_pos (by linarith) 2)

theorem density_pos {c : ℝ} (hc : 0 < c) {x : P} (hx : 0 < x.1) : 0 < density c x :=
  div_pos (rho_pos hc hx) (mul_pos two_pos (energy_pos hx))

theorem measurable_energy : Measurable energy :=
  (by unfold energy; fun_prop : Continuous energy).measurable

theorem measurable_density (c : ℝ) : Measurable (density c) := by
  have hr : Measurable (rho c) := by unfold rho; fun_prop
  exact (hr.comp measurable_fst).div (measurable_const.mul measurable_energy)

theorem base_lowRegion_pos {ε : ℝ} (hε : 0 < ε) : 0 < base (lowRegion ε) := by
  have h1 : 0 < (volume.restrict (Ioi (0 : ℝ))) (Ioo 0 (ε ^ 2 / 4)) := by
    rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.2 Ioo_subset_Ioi_self,
      Real.volume_Ioo, ENNReal.ofReal_pos, sub_zero]
    positivity
  have h2 : 0 < (volume : Measure (EuclideanSpace ℝ (Fin 3))) (ball 0 (ε / 2)) :=
    measure_ball_pos volume 0 (by positivity)
  rw [base, lowRegion, Measure.prod_prod]
  exact ENNReal.mul_pos h1.ne' h2.ne'

/-- `lowRegion ε` has positive one-particle measure at `c > 0`, `ε > 0`. -/
theorem oneParticle_lowRegion_pos {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    0 < oneParticle c (lowRegion ε) := by
  refine pos_iff_ne_zero.2 fun h => (base_lowRegion_pos hε).ne' ?_
  rw [oneParticle, withDensity_apply_eq_zero' (measurable_density c).ennreal_ofReal.aemeasurable]
    at h
  exact measure_mono_null (fun x hx =>
    mem_inter (show ENNReal.ofReal (density c x) ≠ 0 from
      (ENNReal.ofReal_pos.2 (density_pos hc hx.1.1)).ne') hx) h

/-- Excitations of arbitrarily small positive energy: the energies in `(0, ε)` have positive
one-particle measure at `c > 0`, `ε > 0`. -/
theorem low_energy_pos {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    0 < oneParticle c {x | 0 < energy x ∧ energy x < ε} :=
  lt_of_lt_of_le (oneParticle_lowRegion_pos hc hε) (measure_mono fun _ hx => energy_lowRegion hx)

/-- `E > 0` almost everywhere for the one-particle measure. -/
theorem energy_pos_ae (c : ℝ) : ∀ᵐ x ∂oneParticle c, 0 < energy x := by
  have h0 : (volume.restrict (Ioi (0 : ℝ))) (Iic 0) = 0 := by
    rw [Measure.restrict_apply measurableSet_Iic]
    exact measure_mono_null (fun x hx => (not_lt.2 (mem_Iic.1 hx.1) (mem_Ioi.1 hx.2)).elim) measure_empty
  have hb : ∀ᵐ x ∂base, 0 < energy x := by
    rw [ae_iff]
    refine measure_mono_null (t := Iic 0 ×ˢ univ)
      (fun x hx => ⟨not_lt.1 fun h => hx (energy_pos h), trivial⟩) ?_
    rw [base, Measure.prod_prod, h0, zero_mul]
  unfold oneParticle
  exact (withDensity_absolutelyContinuous _ _).ae_le hb

/-- No gap: at `c > 0` and `m > 0`, the energy is not at least `m` almost everywhere. -/
theorem no_gap {c : ℝ} (hc : 0 < c) {m : ℝ} (hm : 0 < m) :
    ¬ ∀ᵐ x ∂oneParticle c, m ≤ energy x := by
  intro h
  rw [ae_iff] at h
  exact (oneParticle_lowRegion_pos hc hm).ne'
    (measure_mono_null (fun x hx => not_le.2 (energy_lowRegion hx).2) h)

/-- No positive mass gap at `c > 0`. -/
theorem no_mass_gap {c : ℝ} (hc : 0 < c) : ¬ ∃ m > 0, ∀ᵐ x ∂oneParticle c, m ≤ energy x :=
  fun ⟨_, hm, h⟩ => no_gap hc hm h

end MassGap.PurityFreeFieldSpectrum

#print axioms MassGap.PurityFreeFieldSpectrum.energy_pos
#print axioms MassGap.PurityFreeFieldSpectrum.energy_lowRegion
#print axioms MassGap.PurityFreeFieldSpectrum.rho_pos
#print axioms MassGap.PurityFreeFieldSpectrum.density_pos
#print axioms MassGap.PurityFreeFieldSpectrum.measurable_energy
#print axioms MassGap.PurityFreeFieldSpectrum.measurable_density
#print axioms MassGap.PurityFreeFieldSpectrum.base_lowRegion_pos
#print axioms MassGap.PurityFreeFieldSpectrum.oneParticle_lowRegion_pos
#print axioms MassGap.PurityFreeFieldSpectrum.low_energy_pos
#print axioms MassGap.PurityFreeFieldSpectrum.energy_pos_ae
#print axioms MassGap.PurityFreeFieldSpectrum.no_gap
#print axioms MassGap.PurityFreeFieldSpectrum.no_mass_gap
