import Mathlib

/-!
# MassGap.PurityTrace — the scalar content of Proposition 6.1 of the purity paper

Proposition 6.1 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford
and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`).

The kernel `A` takes values in `[a, b]` with `0 < a < b`, `B = b/a` and `τ = (B − 1)/(B + 1)`.

* `ratio_le`, `ratio_attained`, `attained_mem`: for `a ≤ m ≤ b`,
  `(b − m)(m − a)/m² ≤ (b − a)²/(4ab)`, with equality at `m = 2ab/(a + b) ∈ [a, b]`; the gap is
  `((a + b)m − 2ab)²/(4ab m²)`.
* `tau_identity`, `tau_mem`: `(b − a)²/(4ab) = τ²/(1 − τ²)` and `0 < τ < 1`.
* `variance_ratio_le`: the second and third relations of (6.1). For a probability measure and
  `A ∈ [a, b]` almost everywhere, `Var(A)/Ā² ≤ (b − a)²/(4ab) = τ²/(1 − τ²)`, from the
  Bhatia–Davis inequality `Var(A) ≤ (b − Ā)(Ā − a)` (Mathlib `variance_le_sub_mul_sub`).
* `pow_le_sq_mul`: `x^T ≤ ε^(T−2) x²` at `0 ≤ x ≤ ε`, `T ≥ 2`.
* `tail_le`, `tail_le_of_sq`: (6.2) over a finite family. Ratios `r_j ∈ [0, τ]` and `T ≥ 2` give
  `Σ r_j^T ≤ τ^{T−2} Σ r_j²`; with the hypothesis `Σ r_j² ≤ τ²/(1 − τ²)`,
  `Σ r_j^T ≤ τ^T/(1 − τ²)`.
* `psi_le`, `thermal_trace_bound`: (6.3). With the hypotheses `Σ r_j² ≤ τ²/(1 − τ²)`,
  `Tr R^T = 1 + Σ r_j^T` (the statement's form) and `Tr R^{2T} ≥ 1`,
  `ψ_T = 2 log Tr R^T − log Tr R^{2T} ≤ 2 log (1 + τ^T/(1 − τ²))`.

The operator steps of the proof are not in this module: the Rayleigh bound `λ₀ ≥ S Ā`, the
Hilbert–Schmidt identity `Tr K² = S² ∫ A² d(ρ ⊗ ρ)`, their combination `Tr R² − 1 ≤ Var(A)/Ā²`
(the first relation of (6.1)), the spectral expansion `Tr R^T = 1 + Σ_{j ≥ 1} r_j^T`, and
`r_j ∈ [0, τ]` from Theorem 5.2. The spectral expansion in finite dimension is
`MassGap.PuritySpectralTrace`.
-/

namespace MassGap.PurityTrace

open Real MeasureTheory ProbabilityTheory

/-- The scalar ratio `(b − m)(m − a)/m²` is at most `(b − a)²/(4ab)` on `[a, b]`. -/
theorem ratio_le {a b m : ℝ} (ha : 0 < a) (ham : a ≤ m) (hmb : m ≤ b) :
    (b - m) * (m - a) / m ^ 2 ≤ (b - a) ^ 2 / (4 * a * b) := by
  have hm : 0 < m := lt_of_lt_of_le ha ham
  have hb : 0 < b := lt_of_lt_of_le hm hmb
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg ((a + b) * m - 2 * a * b)]

/-- The maximum of `(b − m)(m − a)/m²` is attained at `m = 2ab/(a + b)`. -/
theorem ratio_attained {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    let m := 2 * a * b / (a + b)
    (b - m) * (m - a) / m ^ 2 = (b - a) ^ 2 / (4 * a * b) := by
  intro m
  have hab : 0 < a + b := by linarith
  have hm : m = 2 * a * b / (a + b) := rfl
  rw [hm]
  field_simp
  ring

/-- The maximizer `2ab/(a + b)` lies in `[a, b]`. -/
theorem attained_mem {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    a ≤ 2 * a * b / (a + b) ∧ 2 * a * b / (a + b) ≤ b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hs : 0 < a + b := by linarith
  constructor
  · rw [le_div_iff₀ hs]; nlinarith
  · rw [div_le_iff₀ hs]; nlinarith

/-- `τ = (B − 1)/(B + 1)` with `B = b/a` lies in `(0, 1)`. -/
theorem tau_mem {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < (b / a - 1) / (b / a + 1) ∧ (b / a - 1) / (b / a + 1) < 1 := by
  have hB : 1 < b / a := (one_lt_div ha).2 hab
  constructor
  · apply div_pos <;> linarith
  · rw [div_lt_one (by linarith)]
    linarith

/-- `(b − a)²/(4ab) = τ²/(1 − τ²)` with `τ = (B − 1)/(B + 1)`, `B = b/a`. -/
theorem tau_identity {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    let τ := (b / a - 1) / (b / a + 1)
    (b - a) ^ 2 / (4 * a * b) = τ ^ 2 / (1 - τ ^ 2) := by
  intro τ
  have hb : 0 < b := ha.trans hab
  have hτ : τ = (b - a) / (b + a) := by
    show (b / a - 1) / (b / a + 1) = (b - a) / (b + a)
    field_simp
  have hba : 0 < b + a := by linarith
  have h1 : 1 - τ ^ 2 = 4 * a * b / (b + a) ^ 2 := by
    rw [hτ]; field_simp; ring
  rw [h1, hτ]
  field_simp

/-- The second and third relations of (6.1): the normalized variance of a kernel with values in `[a, b]` is at most
`(b − a)²/(4ab)`. -/
theorem variance_ratio_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {a b : ℝ} {A : Ω → ℝ} (ha : 0 < a) (h : ∀ᵐ ω ∂μ, A ω ∈ Set.Icc a b) (hA : AEMeasurable A μ) :
    variance A μ / (μ[A]) ^ 2 ≤ (b - a) ^ 2 / (4 * a * b) := by
  have hint : Integrable A μ :=
    (memLp_of_bounded h hA.aestronglyMeasurable 1).integrable le_rfl
  have hlo : a ≤ μ[A] := by
    have := integral_mono_ae (integrable_const a) hint (h.mono fun ω hω => hω.1)
    simpa using this
  have hhi : μ[A] ≤ b := by
    have := integral_mono_ae hint (integrable_const b) (h.mono fun ω hω => hω.2)
    simpa using this
  have hm : 0 < μ[A] := lt_of_lt_of_le ha hlo
  calc variance A μ / (μ[A]) ^ 2 ≤ (b - μ[A]) * (μ[A] - a) / (μ[A]) ^ 2 :=
        div_le_div_of_nonneg_right (variance_le_sub_mul_sub h hA) (by positivity)
    _ ≤ (b - a) ^ 2 / (4 * a * b) := ratio_le ha hlo hhi

/-- The second and third relations of (6.1) in the `τ` form. -/
theorem variance_ratio_le_tau {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {a b : ℝ} {A : Ω → ℝ} (ha : 0 < a) (hab : a < b)
    (h : ∀ᵐ ω ∂μ, A ω ∈ Set.Icc a b) (hA : AEMeasurable A μ) :
    variance A μ / (μ[A]) ^ 2 ≤
      ((b / a - 1) / (b / a + 1)) ^ 2 / (1 - ((b / a - 1) / (b / a + 1)) ^ 2) := by
  have := tau_identity ha hab
  simp only at this
  rw [← this]
  exact variance_ratio_le ha h hA

/-- Pointwise: `0 ≤ x ≤ ε` and `T ≥ 2` give `x^T ≤ ε^(T−2) x²`. -/
theorem pow_le_sq_mul {x ε : ℝ} (h0 : 0 ≤ x) (hx : x ≤ ε) {T : ℕ} (hT : 2 ≤ T) :
    x ^ T ≤ ε ^ (T - 2) * x ^ 2 := by
  calc x ^ T = x ^ (T - 2) * x ^ 2 := by rw [← pow_add, Nat.sub_add_cancel hT]
    _ ≤ ε ^ (T - 2) * x ^ 2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 hx _) (sq_nonneg x)

/-- Paper, (6.2): eigenvalues in `[0, τ]` give `Σ r_j^T ≤ τ^{T−2} Σ r_j²` for `T ≥ 2`. -/
theorem tail_le {ι : Type*} (s : Finset ι) (r : ι → ℝ) {τ : ℝ} (hr0 : ∀ j ∈ s, 0 ≤ r j)
    (hrτ : ∀ j ∈ s, r j ≤ τ) {T : ℕ} (hT : 2 ≤ T) :
    ∑ j ∈ s, r j ^ T ≤ τ ^ (T - 2) * ∑ j ∈ s, r j ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  exact fun j hj => pow_le_sq_mul (hr0 j hj) (hrτ j hj) hT

/-- Paper, (6.2): with `Σ r_j² ≤ τ²/(1 − τ²)`, `Σ r_j^T ≤ τ^T/(1 − τ²)`. -/
theorem tail_le_of_sq {ι : Type*} (s : Finset ι) (r : ι → ℝ) {τ : ℝ} (hτ0 : 0 ≤ τ)
    (hr0 : ∀ j ∈ s, 0 ≤ r j) (hrτ : ∀ j ∈ s, r j ≤ τ)
    (hsq : ∑ j ∈ s, r j ^ 2 ≤ τ ^ 2 / (1 - τ ^ 2)) {T : ℕ} (hT : 2 ≤ T) :
    ∑ j ∈ s, r j ^ T ≤ τ ^ T / (1 - τ ^ 2) := by
  calc ∑ j ∈ s, r j ^ T ≤ τ ^ (T - 2) * ∑ j ∈ s, r j ^ 2 := tail_le s r hr0 hrτ hT
    _ ≤ τ ^ (T - 2) * (τ ^ 2 / (1 - τ ^ 2)) :=
        mul_le_mul_of_nonneg_left hsq (pow_nonneg hτ0 _)
    _ = τ ^ T / (1 - τ ^ 2) := by
        rw [← mul_div_assoc, ← pow_add, Nat.sub_add_cancel hT]

/-- Paper, (6.3): `Tr R^{2T} ≥ 1` and `0 < Tr R^T ≤ 1 + U` give `ψ_T ≤ 2 log (1 + U)`. -/
theorem psi_le {X Y U : ℝ} (hX : 0 < X) (hXU : X ≤ 1 + U) (hY : 1 ≤ Y) :
    2 * log X - log Y ≤ 2 * log (1 + U) := by
  have h1 : log X ≤ log (1 + U) := log_le_log hX hXU
  have h2 : 0 ≤ log Y := log_nonneg hY
  linarith

/-- Paper, Proposition 6.1, (6.2)–(6.3): eigenvalue ratios `r_j ∈ [0, τ]` with
`Σ r_j² ≤ τ²/(1 − τ²)`, `T ≥ 2` and `Tr R^{2T} ≥ 1` give
`ψ_T = 2 log (1 + Σ r_j^T) − log Tr R^{2T} ≤ 2 log (1 + τ^T/(1 − τ²))`. -/
theorem thermal_trace_bound {ι : Type*} (s : Finset ι) (r : ι → ℝ) {τ Y : ℝ} (hτ0 : 0 ≤ τ)
    (hr0 : ∀ j ∈ s, 0 ≤ r j) (hrτ : ∀ j ∈ s, r j ≤ τ)
    (hsq : ∑ j ∈ s, r j ^ 2 ≤ τ ^ 2 / (1 - τ ^ 2)) {T : ℕ} (hT : 2 ≤ T) (hY : 1 ≤ Y) :
    2 * log (1 + ∑ j ∈ s, r j ^ T) - log Y ≤ 2 * log (1 + τ ^ T / (1 - τ ^ 2)) := by
  have hpos : 0 < 1 + ∑ j ∈ s, r j ^ T := by
    have : 0 ≤ ∑ j ∈ s, r j ^ T := Finset.sum_nonneg fun j hj => pow_nonneg (hr0 j hj) _
    linarith
  exact psi_le hpos (by linarith [tail_le_of_sq s r hτ0 hr0 hrτ hsq hT]) hY

end MassGap.PurityTrace

#print axioms MassGap.PurityTrace.ratio_le
#print axioms MassGap.PurityTrace.ratio_attained
#print axioms MassGap.PurityTrace.attained_mem
#print axioms MassGap.PurityTrace.tau_mem
#print axioms MassGap.PurityTrace.tau_identity
#print axioms MassGap.PurityTrace.variance_ratio_le
#print axioms MassGap.PurityTrace.variance_ratio_le_tau
#print axioms MassGap.PurityTrace.pow_le_sq_mul
#print axioms MassGap.PurityTrace.tail_le
#print axioms MassGap.PurityTrace.tail_le_of_sq
#print axioms MassGap.PurityTrace.psi_le
#print axioms MassGap.PurityTrace.thermal_trace_bound
