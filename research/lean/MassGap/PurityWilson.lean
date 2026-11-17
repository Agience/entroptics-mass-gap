import MassGap.PurityContraction

/-!
# MassGap.PurityWilson — analytic steps of Lemma 5.3 and Theorem 5.4 of the purity paper

The analytic steps of Lemma 5.3 (the bounds (5.5)) and Theorem 5.4 ((5.6)) of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood,
T. Romanov, I. J. Sessford and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak
Coupling* (research draft, 15 November 2026, <https://github.com/anaxia-research/4Y-M>,
commit 8e01510, `Paper-2/Paper-2.pdf`).

* `ratio_tanh`: `(b − a)/(b + a) = tanh(½ log(b/a))` for `a, b > 0`.
* `kernel_lower`, `kernel_upper`: (5.5) for a kernel `A = ∫ exp(F g) dν(g)` over a probability
  measure `ν`. If `∫ F dν = βMq/d` then `e^{βMq/d} ≤ A`, by Jensen's inequality for `exp`; if
  `F ≤ βM` then `A ≤ e^{βM}`.
* `wilson_ratio`: with `a = e^{βMq/d}`, `b = e^{βM}` and `M = 3L³`,
  `(b − a)/(b + a) = tanh(3βL³(1 − q/d)/2)`.
* `wilson_ratio_le`: (5.6), `tanh(3βL³(1 − q/d)/2) ≤ tanh(3βL³/2) < 1` for `β, L, q ≥ 0`, `d > 0`.
* `wilson_gap_pos`: `−log tanh(3βL³/2) > 0` for `β > 0`, `L ≥ 1`.
* `wilson_eigen_le`: (5.6) on the hypotheses of `PurityContraction.eigen_le`, with the pointwise
  bounds `e^{3βL³q/d} ≤ A ≤ e^{3βL³}` as hypotheses: every eigenfunction with `ψ/h` bounded and
  nonconstant has `|λ/λ₀| ≤ tanh(3βL³/2)`.

Not formalized here: the Wilson transfer kernel itself; the Haar average
`∫ Re Tr(U_e g_y V_e g_x⁻¹) dg = q` (which uses independence of `g_x` and `g_y` for `L ≥ 2`) that
gives `∫ F dν = βMq/d`, and `Re Tr W ≤ d`, which with `β ≥ 0` gives `F ≤ βM`; the composition of
`kernel_lower` and `kernel_upper` into the hypotheses `hAa` and `hAb` of `wilson_eigen_le`;
existence of the bounded positive top eigenfunction `h` (hypothesis `hK`) and simplicity of `λ₀`;
positivity, compactness and injectivity of the operator (`λ₁ > 0` for the slice kernel `kTG` is
`PurityLam1Pos`); the passage from
`|λ/λ₀| ≤ tanh(3βL³/2)` to `Δ_lat ≥ −log tanh(3βL³/2)`; gauge invariance of the top
eigenfunction; the rank-one kernel at `β = 0`. On a compact space the composition and the top
eigenfunction are `PurityWilsonCompact` and `PurityThermalCompact.norm_rem_le`.
-/

namespace MassGap.PurityWilson

open MeasureTheory Real

/-- `tanh x = 1 − 2/(e^{2x} + 1)`. -/
theorem tanh_eq_one_sub (x : ℝ) : tanh x = 1 - 2 / (exp (2 * x) + 1) := by
  rw [tanh_eq_sinh_div_cosh, sinh_eq, cosh_eq, show 2 * x = x + x by ring, exp_add, exp_neg]
  have hu := exp_pos x
  field_simp
  ring

/-- `(b − a)/(b + a) = tanh(½ log(b/a))` for `a, b > 0`. -/
theorem ratio_tanh {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (b - a) / (b + a) = tanh (log (b / a) / 2) := by
  rw [tanh_eq_one_sub, show 2 * (log (b / a) / 2) = log (b / a) by ring, exp_log (div_pos hb ha)]
  field_simp
  ring

theorem tanh_mono {x y : ℝ} (h : x ≤ y) : tanh x ≤ tanh y := by
  rw [tanh_eq_one_sub, tanh_eq_one_sub]
  have := exp_le_exp.2 (by linarith : 2 * x ≤ 2 * y)
  have := exp_pos (2 * x)
  have : 2 / (exp (2 * y) + 1) ≤ 2 / (exp (2 * x) + 1) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  linarith

theorem tanh_lt_one (x : ℝ) : tanh x < 1 := by
  rw [tanh_eq_one_sub]
  have : 0 < 2 / (exp (2 * x) + 1) := div_pos (by norm_num) (by linarith [exp_pos (2 * x)])
  linarith

theorem tanh_pos {x : ℝ} (hx : 0 < x) : 0 < tanh x := by
  rw [tanh_eq_one_sub]
  have := one_lt_exp_iff.2 (by linarith : 0 < 2 * x)
  have : 2 / (exp (2 * x) + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  linarith

/-- `−log tanh x > 0` for `x > 0`. -/
theorem neg_log_tanh_pos {x : ℝ} (hx : 0 < x) : 0 < -log (tanh x) := by
  have := log_neg (tanh_pos hx) (tanh_lt_one _)
  linarith

/-- (5.5), lower bound: `e^{∫ F dν} ≤ ∫ e^F dν` (Jensen). -/
theorem kernel_lower {G : Type*} [MeasurableSpace G] {ν : Measure G} [IsProbabilityMeasure ν]
    {F : G → ℝ} {c : ℝ} (hF : Integrable F ν) (heF : Integrable (fun g => exp (F g)) ν)
    (hc : ∫ g, F g ∂ν = c) : exp c ≤ ∫ g, exp (F g) ∂ν := by
  rw [← hc]
  exact (convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ fun _ => Set.mem_univ _) hF heF)

/-- (5.5), upper bound: `F ≤ c` gives `∫ e^F dν ≤ e^c`. -/
theorem kernel_upper {G : Type*} [MeasurableSpace G] {ν : Measure G} [IsProbabilityMeasure ν]
    {F : G → ℝ} {c : ℝ} (heF : Integrable (fun g => exp (F g)) ν) (hFc : ∀ g, F g ≤ c) :
    ∫ g, exp (F g) ∂ν ≤ exp c := by
  have := integral_mono heF (integrable_const (exp c)) fun g => exp_le_exp.2 (hFc g)
  simpa using this

/-- With `a = e^{βMq/d}`, `b = e^{βM}`, `M = 3L³`: `(b − a)/(b + a) = tanh(3βL³(1 − q/d)/2)`. -/
theorem wilson_ratio (β L q d : ℝ) (hd : d ≠ 0) :
    (exp (β * (3 * L ^ 3)) - exp (β * (3 * L ^ 3) * q / d)) /
        (exp (β * (3 * L ^ 3)) + exp (β * (3 * L ^ 3) * q / d)) =
      tanh (3 * β * L ^ 3 * (1 - q / d) / 2) := by
  rw [ratio_tanh (exp_pos _) (exp_pos _), ← exp_sub, log_exp]
  congr 1
  field_simp

/-- (5.6): `tanh(3βL³(1 − q/d)/2) ≤ tanh(3βL³/2) < 1`. -/
theorem wilson_ratio_le {β L q d : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L) (hd : 0 < d) (hq : 0 ≤ q) :
    tanh (3 * β * L ^ 3 * (1 - q / d) / 2) ≤ tanh (3 * β * L ^ 3 / 2) ∧
      tanh (3 * β * L ^ 3 / 2) < 1 := by
  refine ⟨tanh_mono ?_, tanh_lt_one _⟩
  have : 0 ≤ 3 * β * L ^ 3 := by positivity
  have : 0 ≤ q / d := div_nonneg hq hd.le
  nlinarith

/-- `−log tanh(3βL³/2) > 0` for `β > 0`, `L ≥ 1`. -/
theorem wilson_gap_pos {β L : ℝ} (hβ : 0 < β) (hL : 1 ≤ L) : 0 < -log (tanh (3 * β * L ^ 3 / 2)) := by
  have hL3 : 0 < L ^ 3 := by positivity
  exact neg_log_tanh_pos (by positivity)

/-- Theorem 5.4, (5.6), given the pointwise kernel bounds as hypotheses: for a `D A D` kernel with `e^{3βL³q/d} ≤ A ≤ e^{3βL³}`, every eigenfunction
with `ψ/h` bounded and nonconstant has `|λ/λ₀| ≤ tanh(3βL³(1 − q/d)/2) ≤ tanh(3βL³/2)`. -/
theorem wilson_eigen_le {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (hμ : μ ≠ 0) {D h ψ : X → ℝ} {A : X → X → ℝ} {β L q d dl du hl hu m M lam0 lam : ℝ}
    (hβ : 0 ≤ β) (hL : 0 ≤ L) (hd : 0 < d) (hq : 0 ≤ q) (hqd : q ≤ d)
    (hdl : 0 < dl) (hDm : Measurable D) (hDl : ∀ x, dl ≤ D x) (hDu : ∀ x, D x ≤ du)
    (hhl : 0 < hl) (hhm : Measurable h) (hhl' : ∀ x, hl ≤ h x) (hhu : ∀ x, h x ≤ hu)
    (hA : ∀ x, Measurable (A x))
    (hAa : ∀ x y, exp (β * (3 * L ^ 3) * q / d) ≤ A x y) (hAb : ∀ x y, A x y ≤ exp (β * (3 * L ^ 3)))
    (hψm : Measurable ψ) (hφm : ∀ x, m ≤ ψ x / h x) (hφM : ∀ x, ψ x / h x ≤ M)
    (hlam0 : 0 < lam0) (hK : ∀ x, ∫ y, D x * A x y * D y * h y ∂μ = lam0 * h x)
    (hψ : ∀ x, ∫ y, D x * A x y * D y * ψ y ∂μ = lam * ψ x)
    (hne : ∃ x x', ψ x / h x ≠ ψ x' / h x') :
    |lam / lam0| ≤ tanh (3 * β * L ^ 3 * (1 - q / d) / 2) ∧
      |lam / lam0| ≤ tanh (3 * β * L ^ 3 / 2) := by
  have hab : exp (β * (3 * L ^ 3) * q / d) ≤ exp (β * (3 * L ^ 3)) := by
    rw [exp_le_exp, mul_div_assoc]
    have : 0 ≤ β * (3 * L ^ 3) := by positivity
    have : q / d ≤ 1 := (div_le_one hd).2 hqd
    nlinarith
  have := PurityContraction.eigen_le hμ hdl hDm hDl hDu hhl hhm hhl' hhu (exp_pos _) hab hA hAa hAb
    hψm hφm hφM hlam0 hK hψ hne
  rw [wilson_ratio β L q d hd.ne'] at this
  exact ⟨this, this.trans (wilson_ratio_le hβ hL hd hq).1⟩

end MassGap.PurityWilson

#print axioms MassGap.PurityWilson.tanh_eq_one_sub
#print axioms MassGap.PurityWilson.ratio_tanh
#print axioms MassGap.PurityWilson.tanh_mono
#print axioms MassGap.PurityWilson.tanh_lt_one
#print axioms MassGap.PurityWilson.tanh_pos
#print axioms MassGap.PurityWilson.neg_log_tanh_pos
#print axioms MassGap.PurityWilson.kernel_lower
#print axioms MassGap.PurityWilson.kernel_upper
#print axioms MassGap.PurityWilson.wilson_ratio
#print axioms MassGap.PurityWilson.wilson_ratio_le
#print axioms MassGap.PurityWilson.wilson_gap_pos
#print axioms MassGap.PurityWilson.wilson_eigen_le
