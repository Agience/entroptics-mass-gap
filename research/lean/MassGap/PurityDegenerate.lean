import MassGap.PurityWilson

/-!
# MassGap.PurityDegenerate — the finite-volume constant degenerates, §6.3 of the purity paper

Section 6.3 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford
and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`).

The certified gap of Theorem 5.2 at the Wilson kernel is `−log tanh x`, `x = 3β_W L³/2`.

* `hasSum_neg_log_tanh`: the exact identity `−log tanh x = 2 Σ_j e^{−2(2j+1)x}/(2j+1)`, `x > 0`.
* `bound_six_four`: paper, (6.4), `2e^{−X} ≤ −log tanh(X/2) ≤ 2e^{−X}/(1 − e^{−2X})`, `X > 0`
  (`X = 3β_W L³`).
* `tendsto_scaled`: at a spacing `a` with `X(a) ≥ κ/a³` for `0 < a < 1`, `κ > 0` (a fixed physical
  length `ℓ ~ L a` and `β_W` bounded below), `a⁻¹ · (−log tanh(X(a)/2)) → 0` as `a → 0⁺`.
* `tendsto_atTop`, `tendsto_volume`: at a fixed cutoff, `−log tanh(X/2) → 0` as `X → ∞`, so at
  fixed `β_W > 0` the bound tends to `0` as `L → ∞` (it is not uniform in `L`).

The two-point family. On two points with counting measure (a constant rescaling of the measure
rescales `K_a` and leaves `r_a` and the purity unchanged), `K_a = [[a⁻², 1], [1, a⁻²]]`,
`0 < a < 1`, with eigenvalues `λ₀ = a⁻² + 1` on `(1, 1)` and `λ₁ = a⁻² − 1` on `(1, −1)`.

* `Ka_pos`, `form_pos`, `Ka_injective`: the entries are positive and the operator is positive
  definite, hence injective.
* `mulVec_top`, `mulVec_excited`: the two eigenvectors.
* `ratio_eq`: `λ₁/λ₀ = r_a = (1 − a²)/(1 + a²) = (a⁻² − 1)/(a⁻² + 1)`, the formula
  `(b − a)/(b + a)` of Lemma 5.1 evaluated at the largest and smallest entries `b = a⁻²`, `a = 1`
  of `K_a`.
* `rate_bounds`, `tendsto_rate`, `tendsto_rate_div`: `2a/(1 + a²) ≤ −a⁻¹ log r_a ≤ 2a/(1 − a²)`,
  so `−a⁻¹ log r_a → 0` and `−a⁻¹ log r_a ∼ 2a`.
* `trace_pow`: `Tr K_a^n = λ₀ⁿ + λ₁ⁿ`; `purity_eq`: `Tr K_a^{2T}/(Tr K_a^T)² = (1 + s²)/(1 + s)²`,
  `s = r_a^T`.
* `tendsto_pow_floor`, `tendsto_purity`: at `T_a = ⌊t/a⌋`, `t ≥ 0`, `r_a^{T_a} → 1` and the thermal
  purity tends to `1/2` as `a → 0⁺`.
-/

namespace MassGap.PurityDegenerate

open Real Filter Topology
open scoped Matrix


/-- `tanh x = (1 − e^{−2x})/(1 + e^{−2x})`. DERIVED: `2` is the doubling in `tanh`; `1` from
`tanh_eq_one_sub`. -/
theorem tanh_eq_ratio (x : ℝ) : tanh x = (1 - exp (-2 * x)) / (1 + exp (-2 * x)) := by
  rw [PurityWilson.tanh_eq_one_sub, show -2 * x = -(2 * x) by ring, exp_neg]
  have h := exp_pos (2 * x)
  field_simp
  ring

/-- With `y = e^{−2x}`, `x > 0`: `0 < y < 1`. DERIVED: `2` as in `tanh_eq_ratio`; `0`, `1` the
range `e^{−2x} ∈ (0, 1)` of a negative exponent. -/
theorem y_mem {x : ℝ} (hx : 0 < x) : 0 < exp (-2 * x) ∧ exp (-2 * x) < 1 :=
  ⟨exp_pos _, exp_lt_one_iff.2 (by linarith)⟩

/-- `−log tanh x = log(1 + y) − log(1 − y)`, `y = e^{−2x}`, `x > 0`. DERIVED: `2` as in
`tanh_eq_ratio`; `1` from `tanh x = (1 − y)/(1 + y)`. -/
theorem neg_log_tanh_eq {x : ℝ} (hx : 0 < x) :
    -log (tanh x) = log (1 + exp (-2 * x)) - log (1 - exp (-2 * x)) := by
  obtain ⟨h0, h1⟩ := y_mem hx
  rw [tanh_eq_ratio, log_div (by linarith) (by linarith)]
  ring

/-- The series of `log(1 + y) − log(1 − y)` in the form `2 y^{2j+1}/(2j+1)`. DERIVED: `2`, `1`
from `hasSum_log_sub_log_of_abs_lt_one`. -/
theorem hasSum_y {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) :
    HasSum (fun j : ℕ => 2 * y ^ (2 * j + 1) / (2 * j + 1)) (log (1 + y) - log (1 - y)) := by
  have := hasSum_log_sub_log_of_abs_lt_one (x := y) (by rw [abs_of_nonneg h0]; exact h1)
  convert this using 2 with j
  ring

/-- The exact identity of §6.3: `−log tanh x = 2 Σ_j e^{−2(2j+1)x}/(2j+1)`, `x > 0`. DERIVED: `2`,
`1` are the paper's. -/
theorem hasSum_neg_log_tanh {x : ℝ} (hx : 0 < x) :
    HasSum (fun j : ℕ => 2 * exp (-2 * (2 * j + 1) * x) / (2 * j + 1)) (-log (tanh x)) := by
  obtain ⟨h0, h1⟩ := y_mem hx
  rw [neg_log_tanh_eq hx]
  convert hasSum_y h0.le h1 using 2 with j
  rw [← exp_nat_mul]
  push_cast
  ring_nf

/-- `2y ≤ log(1 + y) − log(1 − y) ≤ 2y/(1 − y²)` for `0 ≤ y < 1`. DERIVED: `2` from `hasSum_y`
and the square of the geometric ratio; `1` the ratio's bound. -/
theorem y_bounds {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) :
    2 * y ≤ log (1 + y) - log (1 - y) ∧ log (1 + y) - log (1 - y) ≤ 2 * y / (1 - y ^ 2) := by
  have hs := hasSum_y h0 h1
  have hnn : ∀ j : ℕ, 0 ≤ 2 * y ^ (2 * j + 1) / (2 * j + 1) := fun j => by positivity
  refine ⟨?_, ?_⟩
  · have := le_hasSum hs 0 (fun j _ => hnn j)
    simpa using this
  · have hy2 : y ^ 2 < 1 := by nlinarith
    have hg : HasSum (fun j : ℕ => 2 * y ^ (2 * j + 1)) (2 * y / (1 - y ^ 2)) := by
      have := (hasSum_geometric_of_lt_one (sq_nonneg y) hy2).mul_left (2 * y)
      have hf : (fun j : ℕ => 2 * y ^ (2 * j + 1)) = fun i : ℕ => 2 * y * (y ^ 2) ^ i := by
        funext j
        rw [pow_succ, pow_mul]
        ring
      rw [div_eq_mul_inv, hf]
      exact this
    refine hasSum_le (fun j => ?_) hs hg
    have : (1 : ℝ) ≤ 2 * j + 1 := by have := j.cast_nonneg (α := ℝ); linarith
    exact div_le_self (by positivity) this

/-- Paper, (6.4): `2e^{−X} ≤ −log tanh(X/2) ≤ 2e^{−X}/(1 − e^{−2X})` for `X > 0`; at
`X = 3β_W L³` this is the displayed bound. DERIVED: `2` are the paper's; `X/2 = x`; `1` from
`y_bounds` at `y = e^{−X}`, `y² = e^{−2X}`. -/
theorem bound_six_four {X : ℝ} (hX : 0 < X) :
    2 * exp (-X) ≤ -log (tanh (X / 2)) ∧
      -log (tanh (X / 2)) ≤ 2 * exp (-X) / (1 - exp (-2 * X)) := by
  have hx : 0 < X / 2 := by linarith
  obtain ⟨h0, h1⟩ := y_mem hx
  have hy : -2 * (X / 2) = -X := by ring
  have hsq : exp (-X) ^ 2 = exp (-2 * X) := by rw [← exp_nat_mul]; push_cast; ring_nf
  have := y_bounds h0.le h1
  rw [neg_log_tanh_eq hx]
  rw [hy] at this ⊢
  rw [hsq] at this
  exact this

/-- Eventually as `a → 0⁺`, `0 < a < 1`. DERIVED: `0` the base point; `1` the upper end. -/
theorem eventually_Ioo : ∀ᶠ a in 𝓝[>] (0 : ℝ), a ∈ Set.Ioo (0 : ℝ) 1 :=
  Ioo_mem_nhdsGT (by norm_num)

/-- On `0 < a < 1` with `κ/a³ ≤ X(a)`, `κ > 0`: `a⁻¹ · (−log tanh(X(a)/2)) ≤ C a²`,
`C = 2/(κ(1 − e^{−2κ}))`. DERIVED: `2` from (6.4); `3` the spatial dimension, `κ/a³ ≥ κ` and
`a⁻¹ a³ = a²`; `1` the range of `a`. -/
theorem scaled_le {κ : ℝ} (hκ : 0 < κ) {a X : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hX : κ / a ^ 3 ≤ X) :
    a⁻¹ * -log (tanh (X / 2)) ≤ 2 / (κ * (1 - exp (-2 * κ))) * a ^ 2 := by
  have ha3 : 0 < a ^ 3 := by positivity
  have ha3' : a ^ 3 ≤ 1 := pow_le_one₀ ha.le ha1.le
  have hκX : κ ≤ X := le_trans (by rw [le_div_iff₀ ha3]; nlinarith) hX
  have hXpos : 0 < X := lt_of_lt_of_le hκ hκX
  have hE : 0 < 1 - exp (-2 * κ) := by have := exp_lt_one_iff.2 (by linarith : -2 * κ < 0); linarith
  have hEX : exp (-2 * X) ≤ exp (-2 * κ) := exp_le_exp.2 (by linarith)
  have hup := (bound_six_four hXpos).2
  have h1 : 2 * exp (-X) / (1 - exp (-2 * X)) ≤ 2 * exp (-X) / (1 - exp (-2 * κ)) :=
    div_le_div_of_nonneg_left (by positivity) hE (by linarith)
  have h2 : exp (-X) ≤ a ^ 3 / κ := by
    have := add_one_le_exp X
    rw [exp_neg, inv_le_comm₀ (exp_pos X) (by positivity), inv_div]
    calc κ / a ^ 3 ≤ X := hX
      _ ≤ exp X := by linarith
  have hai : 0 < a⁻¹ := inv_pos.2 ha
  calc a⁻¹ * -log (tanh (X / 2)) ≤ a⁻¹ * (2 * (a ^ 3 / κ) / (1 - exp (-2 * κ))) := by
        refine mul_le_mul_of_nonneg_left (hup.trans (h1.trans ?_)) hai.le
        exact div_le_div_of_nonneg_right (by linarith) hE.le
    _ = 2 / (κ * (1 - exp (-2 * κ))) * a ^ 2 := by field_simp

/-- §6.3: at a fixed physical length, `a⁻¹ · (−log tanh(X(a)/2)) → 0` as `a → 0⁺` whenever
`κ/a³ ≤ X(a)` on `0 < a < 1`, `κ > 0`. DERIVED: `3` the spatial dimension (`X = 3β_W L³`,
`L ~ ℓ/a`); `0`, `1` the range of `a` in the hypothesis and `0` the limit; `2` from (6.4). -/
theorem tendsto_scaled {κ : ℝ} (hκ : 0 < κ) {X : ℝ → ℝ}
    (hX : ∀ a, 0 < a → a < 1 → κ / a ^ 3 ≤ X a) :
    Tendsto (fun a => a⁻¹ * -log (tanh (X a / 2))) (𝓝[>] 0) (𝓝 0) := by
  have hg : Tendsto (fun a : ℝ => 2 / (κ * (1 - exp (-2 * κ))) * a ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun a : ℝ => 2 / (κ * (1 - exp (-2 * κ))) * a ^ 2) (𝓝 0)
        (𝓝 (2 / (κ * (1 - exp (-2 * κ))) * 0 ^ 2)) :=
      ((continuous_const.mul (continuous_pow 2)).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
  · filter_upwards [eventually_Ioo] with a ha
    have hXp : 0 < X a := lt_of_lt_of_le (by have := pow_pos ha.1 3; positivity) (hX a ha.1 ha.2)
    exact mul_nonneg (inv_pos.2 ha.1).le (PurityWilson.neg_log_tanh_pos (by linarith)).le
  · filter_upwards [eventually_Ioo] with a ha
    exact scaled_le hκ ha.1 ha.2 (hX a ha.1 ha.2)

/-- §6.3: at a fixed cutoff the bound is not uniform in the volume, `−log tanh(X/2) → 0` as
`X → ∞`. DERIVED: `2` the half-argument of (6.4); `0` the limit. -/
theorem tendsto_atTop : Tendsto (fun X : ℝ => -log (tanh (X / 2))) atTop (𝓝 0) := by
  have hE : 0 < 1 - exp (-2 * 1) := by have := exp_lt_one_iff.2 (by norm_num : (-2 * 1 : ℝ) < 0); linarith
  have hg : Tendsto (fun X : ℝ => 2 * exp (-X) / (1 - exp (-2 * 1))) atTop (𝓝 0) := by
    have := (tendsto_exp_neg_atTop_nhds_zero.const_mul 2).div_const (1 - exp (-2 * 1))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with X hX
    exact (PurityWilson.neg_log_tanh_pos (by linarith)).le
  · filter_upwards [eventually_ge_atTop 1] with X hX
    refine (bound_six_four (by linarith)).2.trans ?_
    have : exp (-2 * X) ≤ exp (-2 * 1) := exp_le_exp.2 (by linarith)
    exact div_le_div_of_nonneg_left (by positivity) hE (by linarith)

/-! ### The two-point family -/


/-- §6.3: at fixed `β > 0`, the certified gap `−log tanh(3βL³/2) → 0` as `L → ∞`. DERIVED: `3` the
spatial dimension (`X = 3βL³`); `2` the half-argument of (6.4); `0` the bound on `β` and the
limit. -/
theorem tendsto_volume {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun L : ℝ => -log (tanh (3 * β * L ^ 3 / 2))) atTop (𝓝 0) :=
  tendsto_atTop.comp ((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).const_mul_atTop
    (by positivity : (0 : ℝ) < 3 * β))
/-- `K_a = [[a⁻², 1], [1, a⁻²]]` on two points. DERIVED: `2` the paper's exponent; `1` the
paper's off-diagonal entry. -/
noncomputable def Ka (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![(a ^ 2)⁻¹, 1; 1, (a ^ 2)⁻¹]

/-- The top eigenvalue `λ₀ = a⁻² + 1`. DERIVED: as in `Ka`. -/
noncomputable def lam0 (a : ℝ) : ℝ := (a ^ 2)⁻¹ + 1

/-- The excited eigenvalue `λ₁ = a⁻² − 1`. DERIVED: as in `Ka`. -/
noncomputable def lam1 (a : ℝ) : ℝ := (a ^ 2)⁻¹ - 1

/-- The normalized excited eigenvalue `r_a = (1 − a²)/(1 + a²)`. DERIVED: as in `Ka`. -/
noncomputable def r (a : ℝ) : ℝ := (1 - a ^ 2) / (1 + a ^ 2)

/-- The entries of `K_a` are positive, `a ≠ 0`. DERIVED: as in `Ka`. -/
theorem Ka_pos {a : ℝ} (ha : a ≠ 0) (i j : Fin 2) : 0 < Ka a i j := by
  have : 0 < (a ^ 2)⁻¹ := by positivity
  fin_cases i <;> fin_cases j <;> simp [Ka, this]

/-- `K_a (1, 1) = λ₀ (1, 1)`. -/
theorem mulVec_top (a : ℝ) : Ka a *ᵥ ![1, 1] = lam0 a • ![1, 1] := by
  ext i; fin_cases i <;> simp [Ka, lam0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring

/-- `K_a (1, −1) = λ₁ (1, −1)`. -/
theorem mulVec_excited (a : ℝ) : Ka a *ᵥ ![1, -1] = lam1 a • ![1, -1] := by
  ext i; fin_cases i <;> simp [Ka, lam1, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- `K_a` is positive definite for `0 < a < 1`: `⟨v, K_a v⟩ > 0` for `v ≠ 0`. DERIVED: `0`, `1`
the range of `a`; `0` the zero vector and the sign of the form. -/
theorem form_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {v : Fin 2 → ℝ} (hv : v ≠ 0) :
    0 < v ⬝ᵥ (Ka a *ᵥ v) := by
  have hl : 0 < (a ^ 2)⁻¹ - 1 := by
    have : a ^ 2 < 1 := by nlinarith
    have : 1 < (a ^ 2)⁻¹ := (one_lt_inv₀ (by positivity)).2 this
    linarith
  have hne : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra h
    simp only [not_or, ne_eq, not_not] at h
    exact hv (funext fun i => by fin_cases i <;> simp [h.1, h.2])
  have hs : 0 < v 0 ^ 2 + v 1 ^ 2 := by
    rcases hne with h | h
    · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; positivity
    · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; positivity
  have : v ⬝ᵥ (Ka a *ᵥ v) = ((a ^ 2)⁻¹ - 1) * (v 0 ^ 2 + v 1 ^ 2) + (v 0 + v 1) ^ 2 := by
    simp [Ka, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
  rw [this]
  have := mul_pos hl hs
  positivity

/-- `K_a` is injective for `0 < a < 1`. DERIVED: `0`, `1` the range of `a`, as in `form_pos`. -/
theorem Ka_injective {a : ℝ} (ha : 0 < a) (ha1 : a < 1) : Function.Injective (Ka a *ᵥ ·) := by
  intro v w h
  by_contra hne
  have := form_pos ha ha1 (sub_ne_zero.2 hne)
  simp only at h
  rw [Matrix.mulVec_sub, h, sub_self, dotProduct_zero] at this
  exact lt_irrefl _ this

/-- `λ₁/λ₀ = r_a = (a⁻² − 1)/(a⁻² + 1)`: the excited ratio equals the formula `(b − a)/(b + a)`
of Lemma 5.1 at the largest and smallest entries `b = a⁻²`, `a = 1` of `K_a`, at every `a ≠ 0`.
DERIVED: as in `Ka`. -/
theorem ratio_eq {a : ℝ} (ha : a ≠ 0) :
    lam1 a / lam0 a = r a ∧ r a = ((a ^ 2)⁻¹ - 1) / ((a ^ 2)⁻¹ + 1) := by
  have h2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have h3 : 1 + a ^ 2 ≠ 0 := by positivity
  refine ⟨?_, ?_⟩ <;> simp only [lam0, lam1, r] <;> field_simp

/-- `r_a > 0` for `0 < a < 1`. DERIVED: `0`, `1` the range of `a`. -/
theorem r_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) : 0 < r a := by
  unfold r; apply div_pos <;> nlinarith

/-- `r_a ≤ 1`. DERIVED: `1` from `1 − a² ≤ 1 + a²`. -/
theorem r_le_one {a : ℝ} : r a ≤ 1 := by
  unfold r; rw [div_le_one (by positivity)]; nlinarith

/-- `2a/(1 + a²) ≤ −a⁻¹ log r_a ≤ 2a/(1 − a²)`, `0 < a < 1`. DERIVED: `2`, `1` from
`1 − r_a = 2a²/(1 + a²)` and `1/r_a − 1 = 2a²/(1 − a²)`. -/
theorem rate_bounds {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    2 * a / (1 + a ^ 2) ≤ -a⁻¹ * log (r a) ∧ -a⁻¹ * log (r a) ≤ 2 * a / (1 - a ^ 2) := by
  have hr := r_pos ha ha1
  have hd : 0 < 1 - a ^ 2 := by nlinarith
  have hd' : 0 < 1 + a ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · have hl := log_le_sub_one_of_pos hr
    have : 2 * a ^ 2 / (1 + a ^ 2) ≤ -log (r a) := by
      have : 1 - r a = 2 * a ^ 2 / (1 + a ^ 2) := by unfold r; field_simp; ring
      linarith
    calc 2 * a / (1 + a ^ 2) = a⁻¹ * (2 * a ^ 2 / (1 + a ^ 2)) := by field_simp
      _ ≤ a⁻¹ * -log (r a) := mul_le_mul_of_nonneg_left this (inv_pos.2 ha).le
      _ = -a⁻¹ * log (r a) := by ring
  · have hl := log_le_sub_one_of_pos (inv_pos.2 hr)
    rw [log_inv] at hl
    have : (r a)⁻¹ - 1 = 2 * a ^ 2 / (1 - a ^ 2) := by
      unfold r; rw [inv_div]; field_simp; ring
    calc -a⁻¹ * log (r a) = a⁻¹ * -log (r a) := by ring
      _ ≤ a⁻¹ * (2 * a ^ 2 / (1 - a ^ 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) (inv_pos.2 ha).le
      _ = 2 * a / (1 - a ^ 2) := by field_simp

/-- `−a⁻¹ log r_a → 0` as `a → 0⁺`. DERIVED: `2` from `rate_bounds`. -/
theorem tendsto_rate : Tendsto (fun a => -a⁻¹ * log (r a)) (𝓝[>] 0) (𝓝 0) := by
  have hg : Tendsto (fun a : ℝ => 2 * a / (1 - a ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    have : ContinuousAt (fun a : ℝ => 2 * a / (1 - a ^ 2)) 0 :=
      (continuousAt_const.mul continuousAt_id).div
        (continuousAt_const.sub (continuousAt_id.pow 2)) (by norm_num)
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have hf : Tendsto (fun a : ℝ => 2 * a / (1 + a ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    have : ContinuousAt (fun a : ℝ => 2 * a / (1 + a ^ 2)) 0 :=
      (continuousAt_const.mul continuousAt_id).div
        (continuousAt_const.add (continuousAt_id.pow 2)) (by norm_num)
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hf hg ?_ ?_
  · filter_upwards [eventually_Ioo] with a ha using (rate_bounds ha.1 ha.2).1
  · filter_upwards [eventually_Ioo] with a ha using (rate_bounds ha.1 ha.2).2

/-- `−a⁻¹ log r_a ∼ 2a`: the ratio `(−a⁻¹ log r_a)/(2a) → 1` as `a → 0⁺`. DERIVED: `2` the
paper's; `1` from `rate_bounds`. -/
theorem tendsto_rate_div : Tendsto (fun a => -a⁻¹ * log (r a) / (2 * a)) (𝓝[>] 0) (𝓝 1) := by
  have hg : Tendsto (fun a : ℝ => 1 / (1 - a ^ 2)) (𝓝[>] 0) (𝓝 1) := by
    have : ContinuousAt (fun a : ℝ => 1 / (1 - a ^ 2)) 0 :=
      continuousAt_const.div (continuousAt_const.sub (continuousAt_id.pow 2)) (by norm_num)
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have hf : Tendsto (fun a : ℝ => 1 / (1 + a ^ 2)) (𝓝[>] 0) (𝓝 1) := by
    have : ContinuousAt (fun a : ℝ => 1 / (1 + a ^ 2)) 0 :=
      continuousAt_const.div (continuousAt_const.add (continuousAt_id.pow 2)) (by norm_num)
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hf hg ?_ ?_
  · filter_upwards [eventually_Ioo] with a ha
    have h2a : 0 < 2 * a := by linarith [ha.1]
    rw [le_div_iff₀ h2a]
    calc 1 / (1 + a ^ 2) * (2 * a) = 2 * a / (1 + a ^ 2) := by ring
      _ ≤ _ := (rate_bounds ha.1 ha.2).1
  · filter_upwards [eventually_Ioo] with a ha
    have h2a : 0 < 2 * a := by linarith [ha.1]
    rw [div_le_iff₀ h2a]
    calc -a⁻¹ * log (r a) ≤ 2 * a / (1 - a ^ 2) := (rate_bounds ha.1 ha.2).2
      _ = 1 / (1 - a ^ 2) * (2 * a) := by ring

/-- `K_aⁿ` in the eigenbasis. DERIVED: `2` the normalization of the eigenvectors `(1, ±1)`. -/
theorem Ka_pow (a : ℝ) (n : ℕ) :
    Ka a ^ n = !![(lam0 a ^ n + lam1 a ^ n) / 2, (lam0 a ^ n - lam1 a ^ n) / 2;
      (lam0 a ^ n - lam1 a ^ n) / 2, (lam0 a ^ n + lam1 a ^ n) / 2] := by
  induction n with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Ka, lam0, lam1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- `Tr K_aⁿ = λ₀ⁿ + λ₁ⁿ`. -/
theorem trace_pow (a : ℝ) (n : ℕ) : Matrix.trace (Ka a ^ n) = lam0 a ^ n + lam1 a ^ n := by
  rw [Ka_pow]; simp [Matrix.trace, Fin.sum_univ_two]

/-- The thermal purity `Tr K_a^{2T}/(Tr K_a^T)² = (1 + s²)/(1 + s)²`, `s = r_aᵀ`, `a ≠ 0`.
DERIVED: `2` the square in the purity; `1` the top level. -/
theorem purity_eq {a : ℝ} (ha : a ≠ 0) (T : ℕ) :
    Matrix.trace (Ka a ^ (2 * T)) / Matrix.trace (Ka a ^ T) ^ 2 =
      (1 + (r a ^ T) ^ 2) / (1 + r a ^ T) ^ 2 := by
  have hl0 : 0 < lam0 a := by unfold lam0; positivity
  have h1 : lam1 a = r a * lam0 a := by
    rw [← (ratio_eq ha).1]; field_simp
  have hu : lam0 a ^ T ≠ 0 := (pow_pos hl0 T).ne'
  calc Matrix.trace (Ka a ^ (2 * T)) / Matrix.trace (Ka a ^ T) ^ 2
      = ((1 + (r a ^ T) ^ 2) * (lam0 a ^ T) ^ 2) / ((1 + r a ^ T) * lam0 a ^ T) ^ 2 := by
        rw [trace_pow, trace_pow, h1]; congr 1 <;> ring
    _ = _ := by rw [mul_pow, mul_div_mul_right _ _ (pow_ne_zero 2 hu)]

/-- `r_a^{⌊t/a⌋} → 1` as `a → 0⁺`, `t ≥ 0`. DERIVED: `0` the base point `a → 0⁺` and the bound
on `t`; `1` the limit, `r_a → 1`. -/
theorem tendsto_pow_floor {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun a => r a ^ ⌊t / a⌋₊) (𝓝[>] 0) (𝓝 1) := by
  have hlow : Tendsto (fun a => exp (-t * (-a⁻¹ * log (r a)))) (𝓝[>] 0) (𝓝 1) := by
    have := (continuous_exp.tendsto _).comp (tendsto_rate.const_mul (-t))
    simpa [Function.comp_def] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_Ioo] with a ha
    have hr := r_pos ha.1 ha.2
    have hlog : log (r a) ≤ 0 := log_nonpos hr.le r_le_one
    have hN : (⌊t / a⌋₊ : ℝ) ≤ t / a := Nat.floor_le (div_nonneg ht ha.1.le)
    rw [← exp_log (pow_pos hr _), log_pow]
    apply exp_le_exp.2
    calc -t * (-a⁻¹ * log (r a)) = t / a * log (r a) := by ring
      _ ≤ ⌊t / a⌋₊ * log (r a) := mul_le_mul_of_nonpos_right hN hlog
  · filter_upwards [eventually_Ioo] with a ha
    exact pow_le_one₀ (r_pos ha.1 ha.2).le r_le_one

/-- §6.3: at `T_a = ⌊t/a⌋`, `t ≥ 0`, the thermal purity `Tr K_a^{2T_a}/(Tr K_a^{T_a})²` tends to
`1/2`, not to `1`, as `a → 0⁺`. DERIVED: `1/2 = (1 + 1)/(1 + 1)²`; `2` the square in the
purity. -/
theorem tendsto_purity {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun a => Matrix.trace (Ka a ^ (2 * ⌊t / a⌋₊)) / Matrix.trace (Ka a ^ ⌊t / a⌋₊) ^ 2)
      (𝓝[>] 0)
      (𝓝 (1 / 2)) := by
  have hs := tendsto_pow_floor ht
  have hc : Tendsto (fun a => (1 + (r a ^ ⌊t / a⌋₊) ^ 2) / (1 + r a ^ ⌊t / a⌋₊) ^ 2) (𝓝[>] 0)
      (𝓝 ((1 + 1 ^ 2) / (1 + 1) ^ 2)) :=
    (tendsto_const_nhds.add (hs.pow 2)).div ((tendsto_const_nhds.add hs).pow 2) (by norm_num)
  rw [show ((1 : ℝ) + 1 ^ 2) / (1 + 1) ^ 2 = 1 / 2 by norm_num] at hc
  refine hc.congr' ?_
  filter_upwards [eventually_Ioo] with a ha
  exact (purity_eq ha.1.ne' _).symm

end MassGap.PurityDegenerate

#print axioms MassGap.PurityDegenerate.hasSum_neg_log_tanh
#print axioms MassGap.PurityDegenerate.bound_six_four
#print axioms MassGap.PurityDegenerate.scaled_le
#print axioms MassGap.PurityDegenerate.tendsto_scaled
#print axioms MassGap.PurityDegenerate.tendsto_atTop
#print axioms MassGap.PurityDegenerate.Ka_pos
#print axioms MassGap.PurityDegenerate.mulVec_top
#print axioms MassGap.PurityDegenerate.mulVec_excited
#print axioms MassGap.PurityDegenerate.form_pos
#print axioms MassGap.PurityDegenerate.ratio_eq
#print axioms MassGap.PurityDegenerate.rate_bounds
#print axioms MassGap.PurityDegenerate.tendsto_rate
#print axioms MassGap.PurityDegenerate.tendsto_rate_div
#print axioms MassGap.PurityDegenerate.trace_pow
#print axioms MassGap.PurityDegenerate.purity_eq
#print axioms MassGap.PurityDegenerate.tendsto_pow_floor
#print axioms MassGap.PurityDegenerate.tendsto_purity
#print axioms MassGap.PurityDegenerate.Ka_injective
#print axioms MassGap.PurityDegenerate.tendsto_volume
