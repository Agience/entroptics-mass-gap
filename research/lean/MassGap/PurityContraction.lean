import MassGap.PurityRow

/-!
# MassGap.PurityContraction — the contraction step of Theorem 5.2 of the purity paper

Theorem 5.2 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford
and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`).

The kernel is `K(x, y) = D(x) A(x, y) D(y)` with `0 < a ≤ A ≤ b`, on a finite measure `μ ≠ 0`,
with `D` and `h` measurable and bounded above and below by positive constants, and
`∫ K(x, y) h(y) dμ(y) = λ₀ h(x)`, `λ₀ > 0`. Every eigenfunction `ψ`,
`∫ K(x, y) ψ(y) dμ(y) = λ ψ(x)`, whose Doob transform `ψ/h` is bounded and nonconstant has
`|λ/λ₀| ≤ (b − a)/(b + a)`. The bound does not involve the size of `D`.

* `weighted_abs_le`: `avg_abs_le` for the measure `ρ dμ`, `c ≤ ρ ≤ C`, `c > 0`.
* `doob_row`: `(λ/λ₀)(ψ/h)(x)` is the average of `ψ/h` against the density `A(x, ·)` with respect
  to `dw = D h dμ`; the factor `D(x)` cancels.
* `eigen_le`: paper, (5.2), for the eigenfunctions with `ψ/h` bounded and nonconstant. The proof
  bounds `|(λ/λ₀)(φ(x) − φ(x'))|`, `φ = ψ/h`, by `(b − a)/(b + a) · (sup φ − inf φ)` row by row
  and takes the supremum over `x` and the infimum over `x'`.
* `top_simple`: the eigenspace at `λ₀` within the functions with `ψ/h` bounded is spanned by `h`.

Not formalized here: compactness and self-adjointness of the operator; existence, positivity and
continuity of `h`; that every eigenfunction is continuous, hence has `ψ/h` bounded (a hypothesis on
`ψ` here); that the nonzero spectrum consists of eigenvalues; the gap `−log ρ`; the two-point
sharpness example (`PurityRow.row_sharp_bool` is its row form).
-/

namespace MassGap.PurityContraction

open MeasureTheory Set MassGap.PurityRow

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- `avg_abs_le` for the measure `ρ dμ` with `c ≤ ρ ≤ C`, `c > 0`. -/
theorem weighted_abs_le (hμ : μ ≠ 0) {ρ f g φ : X → ℝ} {c C a b m M : ℝ} (hc : 0 < c)
    (hρ : Measurable ρ) (hρc : ∀ y, c ≤ ρ y) (hρC : ∀ y, ρ y ≤ C)
    (ha : 0 < a) (hab : a ≤ b) (hf : Measurable f) (hg : Measurable g) (hφ : Measurable φ)
    (hfa : ∀ y, a ≤ f y) (hfb : ∀ y, f y ≤ b) (hga : ∀ y, a ≤ g y) (hgb : ∀ y, g y ≤ b)
    (hφm : ∀ y, m ≤ φ y) (hφM : ∀ y, φ y ≤ M) :
    |(∫ y, ρ y * (φ y * f y) ∂μ) / (∫ y, ρ y * f y ∂μ) -
      (∫ y, ρ y * (φ y * g y) ∂μ) / (∫ y, ρ y * g y ∂μ)| ≤ (b - a) / (b + a) * (M - m) := by
  have hρ0 : ∀ y, 0 ≤ ρ y := fun y => hc.le.trans (hρc y)
  have hρi : Integrable ρ μ :=
    Integrable.of_bound hρ.aestronglyMeasurable (max |c| |C|) (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]; exact abs_le_max_abs_abs (hρc y) (hρC y))
  have conv : ∀ u : X → ℝ,
      ∫ y, u y ∂(μ.withDensity fun y => ENNReal.ofReal (ρ y)) = ∫ y, ρ y * u y ∂μ := by
    intro u
    have := integral_withDensity_eq_integral_smul (μ := μ) hρ.real_toNNReal u
    simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hρ0 _)] at this
    exact this
  haveI : IsFiniteMeasure (μ.withDensity fun y => ENNReal.ofReal (ρ y)) :=
    isFiniteMeasure_withDensity_ofReal hρi.hasFiniteIntegral
  have hw : (μ.withDensity fun y => ENNReal.ofReal (ρ y)) ≠ 0 := by
    intro h0
    have h1 := conv (fun _ => 1)
    rw [h0, integral_zero_measure] at h1
    have h2 : ∫ _, c ∂μ ≤ ∫ y, ρ y * 1 ∂μ :=
      integral_mono (integrable_const c) (by simpa using hρi) (fun y => by simpa using hρc y)
    rw [integral_const, smul_eq_mul, ← h1] at h2
    have : 0 < μ.real univ :=
      ENNReal.toReal_pos (Measure.measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)
    nlinarith
  have := avg_abs_le hw ha hab hf hg hφ hfa hfb hga hgb hφm hφM
  simpa only [avg, conv] using this

omit [IsFiniteMeasure μ] in
/-- The Doob row: with `ρ = D h`, `(λ/λ₀)(ψ/h)(x) = ∫ ρ (ψ/h) A(x, ·) dμ / ∫ ρ A(x, ·) dμ`. -/
theorem doob_row {D h ψ : X → ℝ} {A : X → X → ℝ} {lam0 lam : ℝ} (hlam0 : 0 < lam0)
    (hD : ∀ x, 0 < D x) (hh : ∀ x, 0 < h x)
    (hK : ∀ x, ∫ y, D x * A x y * D y * h y ∂μ = lam0 * h x)
    (hψ : ∀ x, ∫ y, D x * A x y * D y * ψ y ∂μ = lam * ψ x) (x : X) :
    lam / lam0 * (ψ x / h x) =
      (∫ y, D y * h y * (ψ y / h y * A x y) ∂μ) / ∫ y, D y * h y * A x y ∂μ := by
  have eN : ∫ y, D x * A x y * D y * ψ y ∂μ = D x * ∫ y, D y * h y * (ψ y / h y * A x y) ∂μ := by
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [show D x * (D y * h y * (ψ y / h y * A x y)) = D x * A x y * D y * ψ y * (h y / h y) by ring,
      div_self (hh y).ne', mul_one]
  have eZ : ∫ y, D x * A x y * D y * h y ∂μ = D x * ∫ y, D y * h y * A x y ∂μ := by
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  have h1 := hψ x
  rw [eN] at h1
  have h2 := hK x
  rw [eZ] at h2
  generalize (∫ y, D y * h y * A x y ∂μ) = Z at h2 ⊢
  generalize (∫ y, D y * h y * (ψ y / h y * A x y) ∂μ) = N at h1 ⊢
  have hZ : 0 < Z := by nlinarith [hD x, hh x, mul_pos hlam0 (hh x)]
  rw [eq_div_iff hZ.ne']
  apply mul_left_cancel₀ (hD x).ne'
  rw [h1, show D x * (lam / lam0 * (ψ x / h x) * Z) = lam / lam0 * (ψ x / h x) * (D x * Z) by ring,
    h2, div_mul_div_comm, div_mul_cancel₀ _ (mul_ne_zero hlam0.ne' (hh x).ne')]

/-- Paper, (5.2), on the eigenfunctions `ψ` with `ψ/h` bounded and nonconstant:
`|λ/λ₀| ≤ (b − a)/(b + a)`. -/
theorem eigen_le (hμ : μ ≠ 0) {D h ψ : X → ℝ} {A : X → X → ℝ}
    {a b dl du hl hu m M lam0 lam : ℝ}
    (hdl : 0 < dl) (hDm : Measurable D) (hDl : ∀ x, dl ≤ D x) (hDu : ∀ x, D x ≤ du)
    (hhl : 0 < hl) (hhm : Measurable h) (hhl' : ∀ x, hl ≤ h x) (hhu : ∀ x, h x ≤ hu)
    (ha : 0 < a) (hab : a ≤ b) (hA : ∀ x, Measurable (A x))
    (hAa : ∀ x y, a ≤ A x y) (hAb : ∀ x y, A x y ≤ b)
    (hψm : Measurable ψ) (hφm : ∀ x, m ≤ ψ x / h x) (hφM : ∀ x, ψ x / h x ≤ M)
    (hlam0 : 0 < lam0) (hK : ∀ x, ∫ y, D x * A x y * D y * h y ∂μ = lam0 * h x)
    (hψ : ∀ x, ∫ y, D x * A x y * D y * ψ y ∂μ = lam * ψ x)
    (hne : ∃ x x', ψ x / h x ≠ ψ x' / h x') :
    |lam / lam0| ≤ (b - a) / (b + a) := by
  obtain ⟨x₁, x₂, hne⟩ := hne
  haveI : Nonempty X := ⟨x₁⟩
  have hbA : BddAbove (range fun x => ψ x / h x) := ⟨M, by rintro _ ⟨x, rfl⟩; exact hφM x⟩
  have hbB : BddBelow (range fun x => ψ x / h x) := ⟨m, by rintro _ ⟨x, rfl⟩; exact hφm x⟩
  obtain ⟨S, hSd⟩ : ∃ S, S = ⨆ x, ψ x / h x := ⟨_, rfl⟩
  obtain ⟨I, hId⟩ : ∃ I, I = ⨅ x, ψ x / h x := ⟨_, rfl⟩
  have hS : ∀ x, ψ x / h x ≤ S := fun x => hSd ▸ le_ciSup hbA x
  have hI : ∀ x, I ≤ ψ x / h x := fun x => hId ▸ ciInf_le hbB x
  have hSI : I < S := by
    rcases lt_or_gt_of_ne hne with h' | h' <;> linarith [hS x₁, hS x₂, hI x₁, hI x₂]
  have hD : ∀ x, 0 < D x := fun x => hdl.trans_le (hDl x)
  have hh : ∀ x, 0 < h x := fun x => hhl.trans_le (hhl' x)
  have key : ∀ x x', |lam / lam0| * (ψ x / h x - ψ x' / h x') ≤ (b - a) / (b + a) * (S - I) := by
    intro x x'
    have hw := weighted_abs_le hμ (ρ := fun y => D y * h y) (φ := fun y => ψ y / h y)
      (mul_pos hdl hhl) (hDm.mul hhm)
      (fun y => mul_le_mul (hDl y) (hhl' y) hhl.le (hD y).le)
      (fun y => mul_le_mul (hDu y) (hhu y) (hh y).le ((hD y).le.trans (hDu y)))
      ha hab (hA x) (hA x') (hψm.div hhm) (hAa x) (hAb x) (hAa x') (hAb x') hI hS
    rw [← doob_row hlam0 hD hh hK hψ x, ← doob_row hlam0 hD hh hK hψ x', ← mul_sub,
      abs_mul] at hw
    exact (mul_le_mul_of_nonneg_left (le_abs_self _) (abs_nonneg _)).trans hw
  have hr := abs_nonneg (lam / lam0)
  have hrS : |lam / lam0| * S = ⨆ x, |lam / lam0| * (ψ x / h x) := by
    rw [hSd, Real.mul_iSup_of_nonneg hr]
  have hrI : |lam / lam0| * I = ⨅ x, |lam / lam0| * (ψ x / h x) := by
    rw [hId, Real.mul_iInf_of_nonneg hr]
  have h1 : ∀ x', |lam / lam0| * S ≤ (b - a) / (b + a) * (S - I) + |lam / lam0| * (ψ x' / h x') := by
    intro x'
    rw [hrS]
    exact ciSup_le fun x => by linarith [key x x']
  have h2 : |lam / lam0| * S - (b - a) / (b + a) * (S - I) ≤ |lam / lam0| * I := by
    rw [hrI]
    exact le_ciInf fun x' => by linarith [h1 x']
  exact le_of_mul_le_mul_right (by linarith) (sub_pos.2 hSI)

/-- Simplicity of `λ₀` within the functions with `ψ/h` bounded: such an eigenfunction at `λ₀` is a
multiple of `h`. -/
theorem top_simple (hμ : μ ≠ 0) {D h ψ : X → ℝ} {A : X → X → ℝ}
    {a b dl du hl hu m M lam0 : ℝ}
    (hdl : 0 < dl) (hDm : Measurable D) (hDl : ∀ x, dl ≤ D x) (hDu : ∀ x, D x ≤ du)
    (hhl : 0 < hl) (hhm : Measurable h) (hhl' : ∀ x, hl ≤ h x) (hhu : ∀ x, h x ≤ hu)
    (ha : 0 < a) (hab : a ≤ b) (hA : ∀ x, Measurable (A x))
    (hAa : ∀ x y, a ≤ A x y) (hAb : ∀ x y, A x y ≤ b)
    (hψm : Measurable ψ) (hφm : ∀ x, m ≤ ψ x / h x) (hφM : ∀ x, ψ x / h x ≤ M)
    (hlam0 : 0 < lam0) (hK : ∀ x, ∫ y, D x * A x y * D y * h y ∂μ = lam0 * h x)
    (hψ : ∀ x, ∫ y, D x * A x y * D y * ψ y ∂μ = lam0 * ψ x) :
    ∃ c, ∀ x, ψ x = c * h x := by
  obtain ⟨x₀, -⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_ne_zero.2 hμ)
  by_contra hc
  push Not at hc
  obtain ⟨x₁, hx₁⟩ := hc (ψ x₀ / h x₀)
  have hne : ψ x₁ / h x₁ ≠ ψ x₀ / h x₀ := fun heq =>
    hx₁ (by rw [← heq, div_mul_cancel₀ _ (hhl.trans_le (hhl' x₁)).ne'])
  have := eigen_le hμ hdl hDm hDl hDu hhl hhm hhl' hhu ha hab hA hAa hAb hψm hφm hφM hlam0 hK hψ
    ⟨x₁, x₀, hne⟩
  rw [div_self hlam0.ne', abs_one] at this
  have : (b - a) / (b + a) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  linarith

end MassGap.PurityContraction

#print axioms MassGap.PurityContraction.weighted_abs_le
#print axioms MassGap.PurityContraction.doob_row
#print axioms MassGap.PurityContraction.eigen_le
#print axioms MassGap.PurityContraction.top_simple
