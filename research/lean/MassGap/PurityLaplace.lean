import Mathlib

/-!
# MassGap.PurityLaplace — Proposition A.1 of the purity paper

Proposition A.1 (finite physical-energy weight) of D. Bhattacharjee, U. Bhattacharya,
J. M. Lockwood, T. Romanov, I. J. Sessford and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills
Theory at Weak Coupling* (research draft, 15 November 2026, <https://github.com/anaxia-research/4Y-M>,
commit 8e01510, `Paper-2/Paper-2.pdf`).

A probability spectral measure `μ` lives on `[0, ∞]`, here `ℝ≥0∞`, with Laplace transform
`R(t) = ∫ e^{−tE} dμ(E)` and `e^{−t∞} = 0` (`lap`). The statement is uniform over a family `μ_k`, so
it is stated for one measure.

* `split_le`, `split_ge`: for `0 ≤ g ≤ 1` with `g ≤ ε` off `S` and `g ≥ ε` on `S`,
  `ε μ(S) ≤ ∫ g dμ ≤ μ(S) + ε(1 − μ(S))`.
* `split_rearrange`: `c ≤ ∫ g dμ` and `ε < 1` give `μ(S) ≥ (c − ε)/(1 − ε)`.
* `integral_lap_le_one`: `R(t) ≤ 1` for `t ≥ 0`.
* `laplace_floor`: `R(t) ≥ c > 0`, `t > 0` give `μ([0, Λ]) ≥ c/(2 − c)` for `Λ = t⁻¹ log(2/c)`.
* `laplace_floor_converse`: `μ([0, Λ]) ≥ δ`, `t, Λ ≥ 0` give `R(t) ≥ δ e^{−tΛ}`.
* `escape_tendsto`: the counterexample `⟨e_k, e^{−tH_k} e_k⟩ = e^{−kt} → 0` for `t > 0`.
* `dirac_lap`, `dirac_weight_zero`: the counterexample in the proposition's setting. The spectral
  measure `μ_k = δ_k` has `R_k(t) = e^{−kt}` and `μ_k([0, Λ]) = 0` for `k > Λ`.

The spectral measure of a unit vector under a transfer operator `0 ≤ K ≤ 1` on a finite-dimensional
space is `MassGap.PuritySpectralMeasure`. For a bounded `0 ≤ a ≤ 1` on a complex Hilbert space, the spectral measure of `u` and `Re ⟪u, a^τ u⟫ = ∫ e^{−τE} dσ_u` at real `τ > 0` are `MassGap.ShellMeasure` (`vecMeasure`, `rateMeasure`, `re_inner_powT_eq_laplace`); `rateMeasure` lives on `ℝ` and omits the mass at `λ = 0`. The push-forward of `vecMeasure` to a
probability measure on `[0, ∞]` carrying the mass at `λ = 0`, and the proposition at real `t > 0`,
are `MassGap.PurityShellFloor`. Not formalized here: the unbounded generator `H ≥ 0`; the two-vector Hilbert-space model of the counterexample (norm one, `H_k e = k e`, gaps
`≥ 1`), of which the spectral measures and their Laplace transforms are formalized; the remark that
a lower gap `m` gives the interval `[m, Λ]`.
-/

namespace MassGap.PurityLaplace

open MeasureTheory Real Filter Topology
open scoped ENNReal

section Split

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- Upper split: `g ≤ 1`, `g ≤ ε` off `S` give `∫ g dμ ≤ μ(S) + ε(1 − μ(S))`. -/
theorem split_le {g : X → ℝ} {S : Set X} {ε : ℝ} (hS : MeasurableSet S) (hg : Integrable g μ)
    (h1 : ∀ x, g x ≤ 1) (hε : ∀ x, x ∉ S → g x ≤ ε) :
    ∫ x, g x ∂μ ≤ μ.real S + ε * (1 - μ.real S) := by
  have hle : ∀ x, g x ≤ S.indicator (fun _ => (1 : ℝ)) x + Sᶜ.indicator (fun _ => ε) x := by
    intro x
    by_cases hx : x ∈ S
    · simp [hx, h1 x]
    · simp [hx, hε x hx]
  have hi1 : Integrable (S.indicator (fun _ => (1 : ℝ))) μ := (integrable_const 1).indicator hS
  have hi2 : Integrable (Sᶜ.indicator (fun _ => ε)) μ := (integrable_const ε).indicator hS.compl
  calc ∫ x, g x ∂μ ≤ ∫ x, (S.indicator (fun _ => (1 : ℝ)) x + Sᶜ.indicator (fun _ => ε) x) ∂μ :=
        integral_mono hg (hi1.add hi2) hle
    _ = μ.real S + ε * (1 - μ.real S) := by
        rw [integral_add hi1 hi2, integral_indicator_const _ hS, integral_indicator_const _ hS.compl,
          measureReal_compl hS, probReal_univ]
        simp [smul_eq_mul]
        ring

/-- Lower split: `g ≥ 0`, `g ≥ ε` on `S` give `ε μ(S) ≤ ∫ g dμ`. -/
theorem split_ge {g : X → ℝ} {S : Set X} {ε : ℝ} (hS : MeasurableSet S) (hg : Integrable g μ)
    (h0 : ∀ x, 0 ≤ g x) (hε : ∀ x, x ∈ S → ε ≤ g x) :
    ε * μ.real S ≤ ∫ x, g x ∂μ := by
  have hle : ∀ x, S.indicator (fun _ => ε) x ≤ g x := by
    intro x
    by_cases hx : x ∈ S
    · simp [hx, hε x hx]
    · simp [hx, h0 x]
  have := integral_mono ((integrable_const ε).indicator hS) hg hle
  rw [integral_indicator_const _ hS, smul_eq_mul] at this
  linarith

/-- Rearrangement: `c ≤ ∫ g dμ` and `ε < 1` give `(c − ε)/(1 − ε) ≤ μ(S)`. -/
theorem split_rearrange {g : X → ℝ} {S : Set X} {ε c : ℝ} (hS : MeasurableSet S)
    (hg : Integrable g μ) (h1 : ∀ x, g x ≤ 1) (hε : ∀ x, x ∉ S → g x ≤ ε)
    (hc : c ≤ ∫ x, g x ∂μ) (hε1 : ε < 1) :
    (c - ε) / (1 - ε) ≤ μ.real S := by
  have := split_le hS hg h1 hε
  rw [div_le_iff₀ (by linarith)]
  nlinarith

end Split

/-- The Laplace weight `e^{−tE}` on `[0, ∞]`, with `e^{−t∞} = 0`. -/
noncomputable def lap (t : ℝ) (E : ℝ≥0∞) : ℝ := if E = ⊤ then 0 else exp (-t * E.toReal)

theorem lap_measurable (t : ℝ) : Measurable (lap t) :=
  Measurable.ite (measurableSet_singleton ⊤) measurable_const
    (Real.measurable_exp.comp (measurable_const.mul ENNReal.measurable_toReal))

theorem lap_nonneg (t : ℝ) (E : ℝ≥0∞) : 0 ≤ lap t E := by
  unfold lap; split_ifs <;> positivity

theorem lap_le_one {t : ℝ} (ht : 0 ≤ t) (E : ℝ≥0∞) : lap t E ≤ 1 := by
  unfold lap
  split_ifs
  · norm_num
  · exact exp_le_one_iff.2 (by nlinarith [ENNReal.toReal_nonneg (a := E)])

theorem lap_integrable {t : ℝ} (ht : 0 ≤ t) (μ : Measure ℝ≥0∞) [IsProbabilityMeasure μ] :
    Integrable (lap t) μ :=
  Integrable.of_bound (lap_measurable t).aestronglyMeasurable 1 (ae_of_all _ fun E => by
    rw [Real.norm_eq_abs, abs_of_nonneg (lap_nonneg t E)]; exact lap_le_one ht E)

/-- `R(t) = ∫ e^{−tE} dμ ≤ 1` for a probability measure and `t ≥ 0`. -/
theorem integral_lap_le_one {t : ℝ} (ht : 0 ≤ t) (μ : Measure ℝ≥0∞) [IsProbabilityMeasure μ] :
    ∫ E, lap t E ∂μ ≤ 1 := by
  have := integral_mono (lap_integrable ht μ) (integrable_const (1 : ℝ)) (lap_le_one ht)
  simpa using this

/-- Proposition A.1: a floor `R(t) ≥ c > 0` at `t > 0` gives `μ([0, Λ]) ≥ c/(2 − c)` for
`Λ = t⁻¹ log(2/c)`. -/
theorem laplace_floor {μ : Measure ℝ≥0∞} [IsProbabilityMeasure μ] {t c : ℝ} (ht : 0 < t)
    (hc : 0 < c) (hR : c ≤ ∫ E, lap t E ∂μ) :
    c / (2 - c) ≤ μ.real (Set.Iic (ENNReal.ofReal (log (2 / c) / t))) := by
  have hint := lap_integrable ht.le μ
  have hc1 : c ≤ 1 := hR.trans (integral_lap_le_one ht.le μ)
  have hΛ : 0 ≤ log (2 / c) / t :=
    div_nonneg (log_nonneg (by rw [le_div_iff₀ hc]; linarith)) ht.le
  have heΛ : exp (-t * (log (2 / c) / t)) = c / 2 := by
    rw [show -t * (log (2 / c) / t) = -log (2 / c) by field_simp, exp_neg,
      exp_log (by positivity)]
    field_simp
  have hoff : ∀ E, E ∉ Set.Iic (ENNReal.ofReal (log (2 / c) / t)) → lap t E ≤ c / 2 := by
    intro E hE
    rw [Set.mem_Iic, not_le] at hE
    unfold lap
    split_ifs with htop
    · positivity
    · rw [← heΛ, exp_le_exp]
      have := (ENNReal.ofReal_lt_iff_lt_toReal hΛ htop).1 hE
      nlinarith
  have := split_rearrange measurableSet_Iic hint (lap_le_one ht.le) hoff hR (by linarith)
  calc c / (2 - c) = (c - c / 2) / (1 - c / 2) := by
        field_simp
        ring
    _ ≤ _ := this

/-- Proposition A.1, converse: `μ([0, Λ]) ≥ δ`, `t, Λ ≥ 0` give `R(t) ≥ δ e^{−tΛ}`. -/
theorem laplace_floor_converse {μ : Measure ℝ≥0∞} [IsProbabilityMeasure μ] {t Λ δ : ℝ}
    (ht : 0 ≤ t) (hΛ : 0 ≤ Λ) (hδ : δ ≤ μ.real (Set.Iic (ENNReal.ofReal Λ))) :
    δ * exp (-t * Λ) ≤ ∫ E, lap t E ∂μ := by
  have hon : ∀ E, E ∈ Set.Iic (ENNReal.ofReal Λ) → exp (-t * Λ) ≤ lap t E := by
    intro E hE
    rw [Set.mem_Iic] at hE
    have htop : E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hE
    unfold lap
    rw [if_neg htop, exp_le_exp]
    have := ENNReal.toReal_le_of_le_ofReal hΛ hE
    nlinarith
  have := split_ge measurableSet_Iic (lap_integrable ht μ) (lap_nonneg t) hon
  nlinarith [exp_pos (-t * Λ)]

/-- The counterexample's scalar sequence: `e^{−kt} → 0` as `k → ∞` for `t > 0`. -/
theorem escape_tendsto {t : ℝ} (ht : 0 < t) :
    Tendsto (fun k : ℕ => exp (-((k : ℝ) * t))) atTop (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_natCast_atTop_atTop.atTop_mul_const ht)

/-- The counterexample's spectral measure `δ_k`: `R_k(t) = e^{−kt}`. -/
theorem dirac_lap (t : ℝ) (k : ℕ) :
    ∫ E, lap t E ∂(Measure.dirac (k : ℝ≥0∞)) = exp (-t * k) := by
  rw [integral_dirac]
  unfold lap
  rw [if_neg (ENNReal.natCast_ne_top k), ENNReal.toReal_natCast]

/-- The counterexample's spectral measure `δ_k` has no weight on `[0, Λ]` once `k > Λ ≥ 0`. -/
theorem dirac_weight_zero {Λ : ℝ} (hΛ : 0 ≤ Λ) {k : ℕ} (hk : Λ < k) :
    (Measure.dirac (k : ℝ≥0∞)).real (Set.Iic (ENNReal.ofReal Λ)) = 0 := by
  have hnot : (k : ℝ≥0∞) ∉ Set.Iic (ENNReal.ofReal Λ) := by
    rw [Set.mem_Iic, not_le, ENNReal.ofReal_lt_iff_lt_toReal hΛ (ENNReal.natCast_ne_top k),
      ENNReal.toReal_natCast]
    exact hk
  rw [measureReal_def, Measure.dirac_apply' _ measurableSet_Iic, Set.indicator_of_notMem hnot]
  rfl

end MassGap.PurityLaplace

#print axioms MassGap.PurityLaplace.split_le
#print axioms MassGap.PurityLaplace.split_ge
#print axioms MassGap.PurityLaplace.split_rearrange
#print axioms MassGap.PurityLaplace.lap_measurable
#print axioms MassGap.PurityLaplace.lap_nonneg
#print axioms MassGap.PurityLaplace.lap_le_one
#print axioms MassGap.PurityLaplace.lap_integrable
#print axioms MassGap.PurityLaplace.integral_lap_le_one
#print axioms MassGap.PurityLaplace.laplace_floor
#print axioms MassGap.PurityLaplace.laplace_floor_converse
#print axioms MassGap.PurityLaplace.escape_tendsto
#print axioms MassGap.PurityLaplace.dirac_lap
#print axioms MassGap.PurityLaplace.dirac_weight_zero
