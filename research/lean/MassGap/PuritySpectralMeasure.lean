import MassGap.PurityLaplace
import MassGap.PuritySpectralTrace

/-!
# MassGap.PuritySpectralMeasure — the spectral measure of Proposition A.1, on finite-dimensional spaces

The spectral measure that Proposition A.1 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood,
T. Romanov, I. J. Sessford and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak
Coupling* (research draft, 15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit
8e01510, `Paper-2/Paper-2.pdf`) takes as input, built from a transfer operator on a
finite-dimensional inner product space as an explicit sum of Dirac masses; the spectral measure of
a bounded `0 ≤ a ≤ 1` on a complex Hilbert space is `MassGap.ShellMeasure.vecMeasure`. `K` is
symmetric with eigenbasis `e_i` (Mathlib's `eigenvalues`, `eigenvectorBasis`), the energy of `λ_i`
is `E_i = −log λ_i` (`∞` at `λ_i = 0`), and the spectral measure of `v` is
`μ_v = Σ_i ‖⟪e_i, v⟫‖² δ_{E_i}` on `[0, ∞]`. `transfer_eq_integral` and `transfer_floor` take
`K ≥ 0` with eigenvalues `λ_i ≤ 1` and a natural time `T ≥ 1`.

* `lap_energy`: `e^{−T E(λ)} = λ^T` for `0 ≤ λ ≤ 1`, `T ≥ 1`.
* `lap_energy_rpow`: `e^{−t E(λ)} = λ^t` for `0 ≤ λ ≤ 1`, real `t > 0`.
* `measurable_energy`: `E` is measurable.
* `energy_le_iff`: `E(λ) ≤ Λ ↔ e^{−Λ} ≤ λ` for `Λ ≥ 0`.
* `specMeasure_univ`, `isProbability`: `μ_v([0, ∞]) = ‖v‖²`, a probability measure for `‖v‖ = 1`.
* `specMeasure_real_apply`: `μ_v(S) = Σ_{E_i ∈ S} ‖⟪e_i, v⟫‖²`.
* `integral_lap`: `∫ e^{−tE} dμ_v = Σ_i ‖⟪e_i, v⟫‖² e^{−t E_i}`.
* `transfer_eq_integral`: `R(T) = re ⟪K^T v, v⟫ = ∫ e^{−TE} dμ_v` for `T ≥ 1`.
* `transfer_floor`: Proposition A.1 for the transfer operator. `‖v‖ = 1`, `R(T) ≥ c > 0` give
  `Σ_{λ_i ≥ e^{−Λ}} ‖⟪e_i, v⟫‖² ≥ c/(2 − c)` for `Λ = T⁻¹ log(2/c)`.
-/

namespace MassGap.PuritySpectralMeasure

open MeasureTheory Real LinearMap RCLike
open scoped InnerProductSpace ENNReal

/-- The energy of an eigenvalue: `−log λ` for `λ > 0`, `∞` otherwise. -/
noncomputable def energy (l : ℝ) : ℝ≥0∞ := if 0 < l then ENNReal.ofReal (-log l) else ⊤

/-- `e^{−T E(λ)} = λ^T` for `0 ≤ λ ≤ 1` and `T ≥ 1`. -/
theorem lap_energy {l : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) {T : ℕ} (hT : 0 < T) :
    PurityLaplace.lap T (energy l) = l ^ T := by
  unfold PurityLaplace.lap energy
  by_cases hl : 0 < l
  · rw [if_pos hl, if_neg ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (neg_nonneg.2 (log_nonpos h0 h1)),
      show -(T : ℝ) * -log l = T * log l by ring, Real.exp_nat_mul, exp_log hl]
  · rw [if_neg hl, if_pos rfl, le_antisymm (not_lt.1 hl) h0, zero_pow hT.ne']

/-- `e^{−t E(λ)} = λ^t` for `0 ≤ λ ≤ 1` and real `t > 0`. -/
theorem lap_energy_rpow {l : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) {t : ℝ} (ht : 0 < t) :
    PurityLaplace.lap t (energy l) = l ^ t := by
  unfold PurityLaplace.lap energy
  by_cases hl : 0 < l
  · rw [if_pos hl, if_neg ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (neg_nonneg.2 (log_nonpos h0 h1)),
      show -t * -log l = log l * t by ring, rpow_def_of_pos hl]
  · rw [if_neg hl, if_pos rfl, le_antisymm (not_lt.1 hl) h0, zero_rpow ht.ne']

/-- The energy map is measurable. -/
theorem measurable_energy : Measurable energy :=
  Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (ENNReal.measurable_ofReal.comp measurable_log.neg) measurable_const

/-- `E(λ) ≤ Λ ↔ e^{−Λ} ≤ λ` for `Λ ≥ 0`. -/
theorem energy_le_iff {l Λ : ℝ} (hΛ : 0 ≤ Λ) : energy l ≤ ENNReal.ofReal Λ ↔ exp (-Λ) ≤ l := by
  unfold energy
  by_cases hl : 0 < l
  · rw [if_pos hl, ENNReal.ofReal_le_ofReal_iff hΛ, ← le_log_iff_exp_le hl]
    constructor <;> intro h <;> linarith
  · rw [if_neg hl]
    simp only [top_le_iff, ENNReal.ofReal_ne_top, false_iff, not_le]
    exact lt_of_le_of_lt (not_lt.1 hl) (exp_pos _)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} (hn : Module.finrank 𝕜 E = n)

/-- The spectral measure of `v`: `μ_v = Σ_i ‖⟪e_i, v⟫‖² δ_{E(λ_i)}`. -/
noncomputable def specMeasure {K : E →ₗ[𝕜] E} (hK : K.IsSymmetric) (v : E) : Measure ℝ≥0∞ :=
  ∑ i, ENNReal.ofReal (‖⟪hK.eigenvectorBasis hn i, v⟫_𝕜‖ ^ 2) •
    Measure.dirac (energy (hK.eigenvalues hn i))

/-- `μ_v([0, ∞]) = ‖v‖²`. -/
theorem specMeasure_univ {K : E →ₗ[𝕜] E} (hK : K.IsSymmetric) (v : E) :
    specMeasure hn hK v Set.univ = ENNReal.ofReal (‖v‖ ^ 2) := by
  simp only [specMeasure, Measure.finsetSum_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity),
    (hK.eigenvectorBasis hn).sum_sq_norm_inner_right]

/-- For `‖v‖ = 1`, `μ_v` is a probability measure. -/
theorem isProbability {K : E →ₗ[𝕜] E} (hK : K.IsSymmetric) {v : E} (hv : ‖v‖ = 1) :
    IsProbabilityMeasure (specMeasure hn hK v) :=
  ⟨by rw [specMeasure_univ, hv]; simp⟩

/-- `μ_v(S) = Σ_{E_i ∈ S} ‖⟪e_i, v⟫‖²`. -/
theorem specMeasure_real_apply {K : E →ₗ[𝕜] E} (hK : K.IsSymmetric) (v : E) {S : Set ℝ≥0∞}
    (hS : MeasurableSet S) :
    (specMeasure hn hK v).real S =
      ∑ i, S.indicator (fun _ => ‖⟪hK.eigenvectorBasis hn i, v⟫_𝕜‖ ^ 2)
        (energy (hK.eigenvalues hn i)) := by
  rw [measureReal_def, specMeasure]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ne_top _ _))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.dirac_apply' _ hS]
  by_cases hx : energy (hK.eigenvalues hn i) ∈ S
  · simp [hx]
  · simp [hx]

/-- `∫ e^{−tE} dμ_v = Σ_i ‖⟪e_i, v⟫‖² e^{−t E_i}` for `t ≥ 0`. -/
theorem integral_lap {K : E →ₗ[𝕜] E} (hK : K.IsSymmetric) (v : E) {t : ℝ} (ht : 0 ≤ t) :
    ∫ x, PurityLaplace.lap t x ∂(specMeasure hn hK v) =
      ∑ i, ‖⟪hK.eigenvectorBasis hn i, v⟫_𝕜‖ ^ 2 *
        PurityLaplace.lap t (energy (hK.eigenvalues hn i)) := by
  rw [specMeasure, integral_finsetSum_measure (fun i _ =>
    (PurityLaplace.lap_integrable ht _).smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

/-- The transfer correlator is the Laplace transform of the spectral measure:
`re ⟪K^T v, v⟫ = ∫ e^{−TE} dμ_v` for `K ≥ 0` with eigenvalues `≤ 1` and `T ≥ 1`. -/
theorem transfer_eq_integral {K : E →ₗ[𝕜] E} (hK : K.IsPositive)
    (h1 : ∀ i, hK.isSymmetric.eigenvalues hn i ≤ 1) (v : E) {T : ℕ} (hT : 0 < T) :
    re ⟪(K ^ T) v, v⟫_𝕜 = ∫ x, PurityLaplace.lap T x ∂(specMeasure hn hK.isSymmetric v) := by
  rw [integral_lap hn _ v (Nat.cast_nonneg T), PuritySpectralTrace.re_inner_pow_eq hn hK.isSymmetric]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lap_energy (hK.nonneg_eigenvalues hn i) (h1 i) hT, mul_comm]

/-- Proposition A.1 for a transfer operator: for `‖v‖ = 1` and `re ⟪K^T v, v⟫ ≥ c > 0`, the
spectral weight of `v` on the eigenvalues `λ_i ≥ e^{−Λ}`, `Λ = T⁻¹ log(2/c)`, is at least
`c/(2 − c)`. -/
theorem transfer_floor {K : E →ₗ[𝕜] E} (hK : K.IsPositive)
    (h1 : ∀ i, hK.isSymmetric.eigenvalues hn i ≤ 1) {v : E} (hv : ‖v‖ = 1) {T : ℕ} (hT : 0 < T)
    {c : ℝ} (hc : 0 < c) (hR : c ≤ re ⟪(K ^ T) v, v⟫_𝕜) :
    c / (2 - c) ≤ ∑ i ∈ Finset.univ.filter
        (fun i => exp (-(log (2 / c) / T)) ≤ hK.isSymmetric.eigenvalues hn i),
      ‖⟪hK.isSymmetric.eigenvectorBasis hn i, v⟫_𝕜‖ ^ 2 := by
  haveI := isProbability hn hK.isSymmetric hv
  have hfl := PurityLaplace.laplace_floor (Nat.cast_pos.2 hT) hc
    (hR.trans_eq (transfer_eq_integral hn hK h1 v hT))
  have hc1 : c ≤ 1 := (hR.trans_eq (transfer_eq_integral hn hK h1 v hT)).trans
    (PurityLaplace.integral_lap_le_one (Nat.cast_nonneg T) _)
  have hΛ : 0 ≤ log (2 / c) / T :=
    div_nonneg (log_nonneg (by rw [le_div_iff₀ hc]; linarith)) (Nat.cast_nonneg T)
  rw [specMeasure_real_apply hn _ v measurableSet_Iic] at hfl
  refine hfl.trans_eq ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Set.indicator_apply]
  exact if_congr (by rw [Set.mem_Iic, energy_le_iff hΛ]) rfl rfl

end MassGap.PuritySpectralMeasure

#print axioms MassGap.PuritySpectralMeasure.lap_energy
#print axioms MassGap.PuritySpectralMeasure.lap_energy_rpow
#print axioms MassGap.PuritySpectralMeasure.measurable_energy
#print axioms MassGap.PuritySpectralMeasure.energy_le_iff
#print axioms MassGap.PuritySpectralMeasure.specMeasure_univ
#print axioms MassGap.PuritySpectralMeasure.isProbability
#print axioms MassGap.PuritySpectralMeasure.specMeasure_real_apply
#print axioms MassGap.PuritySpectralMeasure.integral_lap
#print axioms MassGap.PuritySpectralMeasure.transfer_eq_integral
#print axioms MassGap.PuritySpectralMeasure.transfer_floor
