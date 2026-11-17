import Mathlib

/-!
# MassGap.PurityScalar — the scalar content of Sections 6 and 7 of the purity paper

Sections 6–7 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford and
S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`).

Section 7 (the multiscale route):
* `ascent`: paper, Lemma 7.2. `z ≥ 0`, `z 0 ≤ c q`, `z (i+1) ≤ z i ² + e i` and
  `e i ≤ c (1 − c) q^{2^{i+1}}` give `z i ≤ c q^{2^i}` for every `i`, with no condition on `c, q`.
* `ascent_wilson`: the instance `A = 1683/100`, `c = 9/10`, `q = 187/200`, reserve `3/561`:
  `y 0 ≤ 1/20`, `y (i+1) ≤ A y i ² + η i`, `η i ≤ (3/561) q^{2^{i+1}}` give
  `y i ≤ (10/187) q^{2^i}`.
* `constant_tolerance`: for `4 A η < 1`, `r = (1 − √(1 − 4Aη)) / (2A)` is a positive fixed point
  `r = A r² + η`, the stationary level of a constant error; `constant_root`: it is the smaller
  root, `r < 1/(2A)`, and the constant sequence `r` obeys the recurrence and does not tend to `0`.
* `bulk_cancel`, `bulk_cancel_pressure`: paper, Proposition 7.1. Writing `log Z = σ V t + log Z_c + R`
  at times `T` and `2T`, the bulk term cancels in `ψ = 2 log Z(T) − log Z(2T)`, and the pressure
  `T³ ψ / V` is invariant under the blocking `T ↦ T/b`, `V ↦ V/b³` up to `T³/V (2R₁ − R₂)`.
* `separate_bounds`: `|R(t)| ≤ ε V t` at `t = T, 2T` gives `|T³/V (2R₁ − R₂)| ≤ 4 ε T⁴`.
* `telescope`, `multiscale`: the blocked pressures telescope, `p 0 = p J + Σ_{j<J} δ j`.
* `fine_seed`: a coarse pressure `≤ C − δ` and a correction `≤ δ` give a fine pressure `≤ C`;
  `fine_seed_window` at the window constant `C = 1/(161 · 48³)`.

Section 6 (the routes that cannot reach the window):
* `geom_mass`, `geom_purity`, `geom_defect_ge`: the geometric spectrum `(1 − q) qⁿ` has mass `1`,
  purity `(1 − q)/(1 + q)` and defect `−log ((1 − q)/(1 + q)) ≥ 2q` (the first term of the series of
  `log (1 + q) − log (1 − q)`).
* `omegaL`, `modeQ`, `freq_le`, `modeQ_lt_one`, `gaussian_mode_defect`: paper, Proposition 6.3. The
  lattice frequency `ω_L = 2 arsinh (sin (π/L))` of the lowest Gaussian mode satisfies
  `T ω_{2T} ≤ π`, so its occupation `q = e^{−T ω_{2T}}` is at least `e^{−π} > 1/81`, and its defect
  exceeds `2/81`, above the window budget `(2T)³ / (161 (48 T)³) = 1/(161 · 13824)` (`budget_eq`).
  `product_defect`: a further factor of purity `≤ 1` only raises the defect;
  `gaussian_product_defect`: so a product Gaussian state containing that mode exceeds the budget.
* `kernel_route_large`: paper, Proposition 6.2. With `τ = tanh (κ/2)`, `κ ≥ T³` and `T ≥ 3`,
  `U = τ^T / (1 − τ²)` has `log U ≥ 22`, so the kernel bound `2 log (1 + U)` exceeds `44`. Here `κ`
  is the paper's `β`. `kernel_route_window`: the paper's hypotheses `W ≥ 1/24`, `(2T)³ ≤ V < (48T)³`,
  `κ = 3 W V` give `κ ≥ T³`, and the bound exceeds `44` while the threshold `V/(161 (48T)³)` of
  Corollary 4.2 is below `1/161`.

DERIVED (module-wide): `1683/100 = 9 · 187/100` the quadratic coefficient of the paper's ascent;
`c = 9/10`, `q = 187/200` with `c q = A/20` and `c (1 − c) = A · 3/561`, so `c / A = 10/187`;
`81 > e⁴ ≥ e^π` from `e < 2.7182818286` and `π ≤ 4`; `161` and `48` the window coefficients of the
paper's Corollary 4.2 and Section 6, `48³ / 2³ = 13824`; `22` from `κ − 1 − log 4 ≥ 27 − 1 − 1.3863`.
-/

namespace MassGap.PurityScalar

open Real Finset

/-! ## Lemma 7.2: error-stable quadratic ascent -/

/-- Paper, Lemma 7.2. -/
theorem ascent {c q : ℝ} {z e : ℕ → ℝ} (hz : ∀ i, 0 ≤ z i) (h0 : z 0 ≤ c * q)
    (hstep : ∀ i, z (i + 1) ≤ z i ^ 2 + e i)
    (he : ∀ i, e i ≤ c * (1 - c) * q ^ 2 ^ (i + 1)) : ∀ i, z i ≤ c * q ^ 2 ^ i := by
  intro i
  induction i with
  | zero => simpa using h0
  | succ i ih =>
    have hsq : z i ^ 2 ≤ (c * q ^ 2 ^ i) ^ 2 := pow_le_pow_left₀ (hz i) ih 2
    have hr : (c * q ^ 2 ^ i) ^ 2 = c ^ 2 * q ^ 2 ^ (i + 1) := by
      rw [mul_pow, ← pow_mul, ← pow_succ]
    calc z (i + 1) ≤ z i ^ 2 + e i := hstep i
      _ ≤ c ^ 2 * q ^ 2 ^ (i + 1) + c * (1 - c) * q ^ 2 ^ (i + 1) := by
          rw [← hr]; exact add_le_add hsq (he i)
      _ = c * q ^ 2 ^ (i + 1) := by ring

/-- Paper, Lemma 7.2, the instance `A = 1683/100`, `c = 9/10`, `q = 187/200`, reserve `3/561`. -/
theorem ascent_wilson {y η : ℕ → ℝ} (hy : ∀ i, 0 ≤ y i) (h0 : y 0 ≤ 1 / 20)
    (hstep : ∀ i, y (i + 1) ≤ 1683 / 100 * y i ^ 2 + η i)
    (hη : ∀ i, η i ≤ 3 / 561 * (187 / 200 : ℝ) ^ 2 ^ (i + 1)) :
    ∀ i, y i ≤ 10 / 187 * (187 / 200 : ℝ) ^ 2 ^ i := by
  have key := ascent (c := 9 / 10) (q := 187 / 200) (z := fun i => 1683 / 100 * y i)
    (e := fun i => 1683 / 100 * η i) (fun i => by have := hy i; positivity)
    (by linarith) (fun i => by
      have := hstep i
      nlinarith)
    (fun i => by
      have := hη i
      nlinarith)
  intro i
  have := key i
  nlinarith

/-- A constant error `η` with `4 A η < 1` has the positive stationary level
`r = (1 − √(1 − 4Aη)) / (2A)`, `r = A r² + η`. -/
theorem constant_tolerance {A η : ℝ} (hA : 0 < A) (hη : 0 < η) (h : 4 * A * η < 1) :
    0 < (1 - √(1 - 4 * A * η)) / (2 * A) ∧
      (1 - √(1 - 4 * A * η)) / (2 * A) =
        A * ((1 - √(1 - 4 * A * η)) / (2 * A)) ^ 2 + η := by
  have hs0 : 0 ≤ √(1 - 4 * A * η) := Real.sqrt_nonneg _
  have hs2 : √(1 - 4 * A * η) ^ 2 = 1 - 4 * A * η := Real.sq_sqrt (by linarith)
  have hAη : 0 < A * η := mul_pos hA hη
  have hs1 : √(1 - 4 * A * η) < 1 := by nlinarith
  refine ⟨div_pos (by linarith) (by linarith), ?_⟩
  have key : A * ((1 - √(1 - 4 * A * η)) / (2 * A)) ^ 2 + η -
      (1 - √(1 - 4 * A * η)) / (2 * A) =
      (√(1 - 4 * A * η) ^ 2 - (1 - 4 * A * η)) / (4 * A) := by
    field_simp
    ring
  rw [hs2, sub_self, zero_div] at key
  linarith

/-- Paper, remark after Lemma 7.2: the stationary level is the smaller root, `r < 1/(2A)`, and the
constant sequence at `r` obeys the recurrence with constant error `η` and does not tend to `0`. -/
theorem constant_root {A η : ℝ} (hA : 0 < A) (hη : 0 < η) (h : 4 * A * η < 1) :
    (1 - √(1 - 4 * A * η)) / (2 * A) < 1 / (2 * A) ∧
      (∀ _i : ℕ, (1 - √(1 - 4 * A * η)) / (2 * A) =
        A * ((1 - √(1 - 4 * A * η)) / (2 * A)) ^ 2 + η) ∧
      ¬ Filter.Tendsto (fun _ : ℕ => (1 - √(1 - 4 * A * η)) / (2 * A)) Filter.atTop (nhds 0) := by
  obtain ⟨hr, hfix⟩ := constant_tolerance hA hη h
  refine ⟨?_, fun _ => hfix, ?_⟩
  · have hs : 0 < √(1 - 4 * A * η) := Real.sqrt_pos.2 (by linarith)
    exact div_lt_div_of_pos_right (by linarith) (by linarith)
  · intro ht
    rw [tendsto_const_nhds_iff] at ht
    exact hr.ne' ht

/-! ## Proposition 7.1: bulk cancellation and the multiscale telescope -/

/-- Paper, Proposition 7.1: the bulk term `σ V t` cancels in `2 log Z(T) − log Z(2T)`. -/
theorem bulk_cancel {σ V T lf₁ lf₂ lc₁ lc₂ R₁ R₂ : ℝ}
    (h₁ : lf₁ = σ * V * T + lc₁ + R₁) (h₂ : lf₂ = σ * V * (2 * T) + lc₂ + R₂) :
    2 * lf₁ - lf₂ = (2 * lc₁ - lc₂) + (2 * R₁ - R₂) := by
  rw [h₁, h₂]; ring

/-- Paper, Proposition 7.1: the pressure `T³ ψ / V` is invariant under the blocking
`T ↦ T/b`, `V ↦ V/b³` up to `T³/V (2R₁ − R₂)`. -/
theorem bulk_cancel_pressure {b V T ψf ψc R₁ R₂ : ℝ} (hb : b ≠ 0) (hV : V ≠ 0)
    (h : ψf = ψc + (2 * R₁ - R₂)) :
    T ^ 3 * ψf / V = (T / b) ^ 3 * ψc / (V / b ^ 3) + T ^ 3 / V * (2 * R₁ - R₂) := by
  rw [h]
  field_simp

/-- `|R(t)| ≤ ε V t` at `t = T, 2T` gives `|T³/V (2R₁ − R₂)| ≤ 4 ε T⁴`. -/
theorem separate_bounds {ε V T R₁ R₂ : ℝ} (hV : 0 < V) (hT : 0 ≤ T)
    (h₁ : |R₁| ≤ ε * V * T) (h₂ : |R₂| ≤ ε * V * (2 * T)) :
    |T ^ 3 / V * (2 * R₁ - R₂)| ≤ 4 * ε * T ^ 4 := by
  obtain ⟨h₁l, h₁r⟩ := abs_le.1 h₁
  obtain ⟨h₂l, h₂r⟩ := abs_le.1 h₂
  have hx : |2 * R₁ - R₂| ≤ 4 * ε * V * T := abs_le.2 ⟨by linarith, by linarith⟩
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ T ^ 3 / V)]
  calc T ^ 3 / V * |2 * R₁ - R₂| ≤ T ^ 3 / V * (4 * ε * V * T) :=
        mul_le_mul_of_nonneg_left hx (by positivity)
    _ = 4 * ε * T ^ 4 := by
        rw [div_mul_eq_mul_div, div_eq_iff hV.ne']; ring

/-- The blocked pressures telescope: `p j = p (j+1) + δ j` gives `p 0 = p J + Σ_{j<J} δ j`. -/
theorem telescope {p δ : ℕ → ℝ} (h : ∀ j, p j = p (j + 1) + δ j) :
    ∀ J, p 0 = p J + ∑ j ∈ range J, δ j := by
  intro J
  induction J with
  | zero => simp
  | succ J ih => rw [sum_range_succ]; linarith [h J]

/-- Paper, Proposition 7.1, multiscale form: along `T (j+1) = T j / b j`, `V (j+1) = V j / b j³` with
`ψ j = ψ (j+1) + (2 R₁ j − R₂ j)`, the pressure at scale `0` is the pressure at scale `J` plus the
summed remainders. -/
theorem multiscale {b T V ψ R₁ R₂ : ℕ → ℝ} (hb : ∀ j, b j ≠ 0) (hV : ∀ j, V j ≠ 0)
    (hT : ∀ j, T (j + 1) = T j / b j) (hVs : ∀ j, V (j + 1) = V j / b j ^ 3)
    (hψ : ∀ j, ψ j = ψ (j + 1) + (2 * R₁ j - R₂ j)) (J : ℕ) :
    T 0 ^ 3 * ψ 0 / V 0 = T J ^ 3 * ψ J / V J +
      ∑ j ∈ range J, T j ^ 3 / V j * (2 * R₁ j - R₂ j) := by
  refine telescope (p := fun j => T j ^ 3 * ψ j / V j) (fun j => ?_) J
  rw [hT, hVs]
  exact bulk_cancel_pressure (hb j) (hV j) (hψ j)

/-- A coarse pressure `≤ C − δ` and a correction `≤ δ` give a fine pressure `≤ C`. -/
theorem fine_seed {pf pc C δ : ℝ} (hc : pc ≤ C - δ) (hf : pf ≤ pc + δ) : pf ≤ C := by
  linarith

/-- `fine_seed` at the window constant `C = 1/(161 · 48³)` of the paper's Section 7. -/
theorem fine_seed_window {pf pc δ : ℝ} (hc : pc ≤ 1 / (161 * 48 ^ 3) - δ) (hf : pf ≤ pc + δ) :
    pf ≤ 1 / (161 * 48 ^ 3) :=
  fine_seed hc hf

/-! ## Proposition 6.3: the Gaussian mode -/

/-- The geometric spectrum `(1 − q) qⁿ` has mass `1`. -/
theorem geom_mass {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) : ∑' n : ℕ, (1 - q) * q ^ n = 1 := by
  rw [tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
  exact mul_inv_cancel₀ (sub_pos.2 h1).ne'

/-- The geometric spectrum `(1 − q) qⁿ` has purity `Σ ((1 − q) qⁿ)² = (1 − q)/(1 + q)`. -/
theorem geom_purity {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    ∑' n : ℕ, ((1 - q) * q ^ n) ^ 2 = (1 - q) / (1 + q) := by
  have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
  have hq21 : q ^ 2 < 1 := by nlinarith
  calc ∑' n : ℕ, ((1 - q) * q ^ n) ^ 2 = ∑' n : ℕ, (1 - q) ^ 2 * (q ^ 2) ^ n :=
        tsum_congr fun n => by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm n 2]
    _ = (1 - q) ^ 2 * ∑' n : ℕ, (q ^ 2) ^ n := tsum_mul_left
    _ = (1 - q) ^ 2 * (1 - q ^ 2)⁻¹ := by rw [tsum_geometric_of_lt_one hq2 hq21]
    _ = (1 - q) / (1 + q) := by
        rw [← div_eq_mul_inv, div_eq_div_iff (by nlinarith) (by linarith)]; ring

/-- The normalized purity of the geometric spectrum. -/
theorem geom_normalized_purity {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    (∑' n : ℕ, ((1 - q) * q ^ n) ^ 2) / (∑' n : ℕ, (1 - q) * q ^ n) ^ 2 = (1 - q) / (1 + q) := by
  rw [geom_purity h0 h1, geom_mass h0 h1, one_pow, div_one]

/-- The defect of the geometric spectrum is at least `2q`. -/
theorem geom_defect_ge {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    2 * q ≤ -log ((1 - q) / (1 + q)) := by
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one (x := q) (by rw [abs_of_nonneg h0]; exact h1)
  have h := le_hasSum hs 0 (fun j _ => mul_nonneg (by positivity) (pow_nonneg h0 _))
  simp only [Nat.cast_zero, mul_zero, zero_add, div_one, mul_one, pow_one] at h
  rw [Real.log_div (sub_pos.2 h1).ne' (by linarith)]
  linarith

/-- `arsinh x ≤ x` for `x ≥ 0`. -/
theorem arsinh_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) : arsinh x ≤ x :=
  calc arsinh x ≤ arsinh (sinh x) := arsinh_le_arsinh.2 (self_le_sinh_iff.2 hx)
    _ = x := arsinh_sinh x

/-- The lattice frequency of the lowest mode on a period `L`. -/
noncomputable def omegaL (L : ℝ) : ℝ := 2 * arsinh (sin (π / L))

/-- The occupation `e^{−T ω_{2T}}` of the lowest mode at time `T` on the period `2T`. -/
noncomputable def modeQ (T : ℝ) : ℝ := exp (-(T * omegaL (2 * T)))

/-- `T ω_{2T} ≤ π`. -/
theorem freq_le {T : ℝ} (hT : 0 < T) : T * omegaL (2 * T) ≤ π := by
  unfold omegaL
  have hx : 0 ≤ π / (2 * T) := by positivity
  have h1 : arsinh (sin (π / (2 * T))) ≤ π / (2 * T) :=
    (arsinh_le_arsinh.2 (sin_le hx)).trans (arsinh_le_self_of_nonneg hx)
  calc T * (2 * arsinh (sin (π / (2 * T)))) ≤ T * (2 * (π / (2 * T))) := by gcongr
    _ = π := by field_simp

/-- `0 < T ω_{2T}` for `T ≥ 1`. -/
theorem freq_pos {T : ℝ} (hT : 1 ≤ T) : 0 < T * omegaL (2 * T) := by
  unfold omegaL
  have hx : 0 < π / (2 * T) := by positivity
  have hxπ : π / (2 * T) < π := div_lt_self pi_pos (by linarith)
  have hs : 0 < sin (π / (2 * T)) := sin_pos_of_pos_of_lt_pi hx hxπ
  have := arsinh_pos_iff.2 hs
  positivity

theorem modeQ_pos (T : ℝ) : 0 < modeQ T := exp_pos _

theorem modeQ_lt_one {T : ℝ} (hT : 1 ≤ T) : modeQ T < 1 :=
  Real.exp_lt_one_iff.2 (by linarith [freq_pos hT])

/-- `e^π < 81`. -/
theorem exp_pi_lt : exp π < 81 := by
  have h4 : exp 4 = exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  calc exp π ≤ exp 4 := exp_le_exp.2 pi_le_four
    _ = exp 1 ^ 4 := h4
    _ < 2.7182818286 ^ 4 := pow_lt_pow_left₀ exp_one_lt_d9 (exp_pos 1).le (by norm_num)
    _ < 81 := by norm_num

/-- `1/81 < e^{−π}`. -/
theorem inv81_lt_exp_neg_pi : (1 : ℝ) / 81 < exp (-π) := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_lt_one_div_of_lt (exp_pos π) exp_pi_lt

/-- `1/81 < e^{−T ω_{2T}}`. -/
theorem inv81_lt_modeQ {T : ℝ} (hT : 0 < T) : (1 : ℝ) / 81 < modeQ T :=
  inv81_lt_exp_neg_pi.trans_le (exp_le_exp.2 (neg_le_neg (freq_le hT)))

/-- The window budget at time `T`: `(2T)³ / (161 (48 T)³) = 1/(161 · 13824)`. -/
theorem budget_eq {T : ℝ} (hT : T ≠ 0) :
    (2 * T) ^ 3 / (161 * (48 * T) ^ 3) = 1 / (161 * 13824) := by
  field_simp
  ring

/-- Paper, Proposition 6.3: the lowest Gaussian mode has defect above `2/81`, which is above the
window budget `1/(161 · 13824)`. -/
theorem gaussian_mode_defect {T : ℝ} (hT : 1 ≤ T) :
    (1 : ℝ) / (161 * 13824) < 2 / 81 ∧
      2 / 81 < -log ((1 - modeQ T) / (1 + modeQ T)) := by
  refine ⟨by norm_num, ?_⟩
  have h := geom_defect_ge (modeQ_pos T).le (modeQ_lt_one hT)
  have h81 := inv81_lt_modeQ (T := T) (by linarith)
  linarith

/-- A further factor of purity `P₂ ∈ (0, 1]` only raises the defect. -/
theorem product_defect {P₁ P₂ : ℝ} (h₁ : 0 < P₁) (h₂ : 0 < P₂) (h₂₁ : P₂ ≤ 1) :
    -log P₁ ≤ -log (P₁ * P₂) := by
  rw [Real.log_mul h₁.ne' h₂.ne']
  linarith [Real.log_nonpos h₂.le h₂₁]

/-- Paper, Proposition 6.3, consequence: a product state whose lowest Gaussian mode has purity
`(1 − q)/(1 + q)` and whose remaining factor has purity `P ∈ (0, 1]` has defect above the window
budget `1/(161 · 13824)`. -/
theorem gaussian_product_defect {T P : ℝ} (hT : 1 ≤ T) (hP : 0 < P) (hP1 : P ≤ 1) :
    (1 : ℝ) / (161 * 13824) < -log ((1 - modeQ T) / (1 + modeQ T) * P) := by
  obtain ⟨h1, h2⟩ := gaussian_mode_defect hT
  have hq := modeQ_lt_one hT
  have hq0 := modeQ_pos T
  have hm : 0 < (1 - modeQ T) / (1 + modeQ T) := div_pos (by linarith) (by linarith)
  linarith [product_defect hm hP hP1]

/-! ## Proposition 6.2: the kernel route -/

/-- Paper, Proposition 6.2: with `τ = tanh (κ/2)`, `κ ≥ T³` and `T ≥ 3`, `U = τ^T / (1 − τ²)` has
`log U ≥ 22`, and the kernel bound `2 log (1 + U)` exceeds `44`. -/
theorem kernel_route_large {κ : ℝ} {T : ℕ} (hT : 3 ≤ T) (hκ : (T : ℝ) ^ 3 ≤ κ) :
    22 ≤ log (tanh (κ / 2) ^ T / (1 - tanh (κ / 2) ^ 2)) ∧
      44 < 2 * log (1 + tanh (κ / 2) ^ T / (1 - tanh (κ / 2) ^ 2)) := by
  have hT3 : (3 : ℝ) ≤ T := by exact_mod_cast hT
  have hT27 : (27 : ℝ) ≤ (T : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hT3 3
    norm_num at this ⊢; linarith
  have hκ27 : 27 ≤ κ := by linarith
  have h2T : 2 * (T : ℝ) ≤ κ := by
    nlinarith [mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ (T : ℝ) ^ 2 by nlinarith)
      (show (0 : ℝ) ≤ T by linarith)]
  have ha := exp_pos (κ / 2)
  have hb := exp_pos (-(κ / 2))
  have hden : 0 < exp (κ / 2) + exp (-(κ / 2)) := by positivity
  have ht : tanh (κ / 2) =
      (exp (κ / 2) - exp (-(κ / 2))) / (exp (κ / 2) + exp (-(κ / 2))) := by
    rw [tanh_eq_sinh_div_cosh, sinh_eq, cosh_eq]
    field_simp
  have hab : exp (κ / 2) * exp (-(κ / 2)) = 1 := by rw [← exp_add]; simp
  have ha2 : κ + 1 ≤ exp (κ / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (κ / 2) = κ := by push_cast; ring
    rw [this]
    linarith [add_one_le_exp κ]
  have hloga : log (exp (κ / 2)) = κ / 2 := log_exp _
  rw [ht]
  generalize exp (κ / 2) = a at ha hden hab ha2 hloga ⊢
  generalize exp (-(κ / 2)) = b at hb hden hab ⊢
  have h4T : 2 * (T : ℝ) * b ≤ a - b := by
    refine le_of_mul_le_mul_right ?_ ha
    have e1 : 2 * (T : ℝ) * b * a = 2 * T := by linear_combination 2 * (T : ℝ) * hab
    have e2 : (a - b) * a = a ^ 2 - 1 := by linear_combination -hab
    rw [e1, e2]; linarith
  have hamb : 0 < a - b := by nlinarith
  set t := (a - b) / (a + b) with htdef
  have ht0 : 0 < t := div_pos hamb hden
  have h1t : 1 - t ^ 2 = 4 / (a + b) ^ 2 := by
    rw [htdef, div_pow, one_sub_div (by positivity)]
    congr 1
    linear_combination 4 * hab
  have hU0 : 0 < t ^ T / (1 - t ^ 2) := by
    rw [h1t]; exact div_pos (pow_pos ht0 T) (by positivity)
  have hlogU : log (t ^ T / (1 - t ^ 2)) = T * log t - (log 4 - 2 * log (a + b)) := by
    rw [h1t, Real.log_div (pow_pos ht0 T).ne' (by positivity), Real.log_pow,
      Real.log_div (by norm_num : (4 : ℝ) ≠ 0) (by positivity : (a + b) ^ 2 ≠ 0), Real.log_pow]
    push_cast; ring
  have hlt : -1 ≤ (T : ℝ) * log t := by
    have h := one_sub_inv_le_log_of_pos ht0
    have hinv : t⁻¹ = (a + b) / (a - b) := by rw [htdef, inv_div]
    have hk : -1 ≤ (T : ℝ) * (1 - (a + b) / (a - b)) := by
      rw [one_sub_div hamb.ne', mul_div_assoc', le_div_iff₀ hamb]
      linarith
    rw [hinv] at h
    calc -1 ≤ (T : ℝ) * (1 - (a + b) / (a - b)) := hk
      _ ≤ (T : ℝ) * log t := mul_le_mul_of_nonneg_left h (by positivity)
  have hlab : κ / 2 ≤ log (a + b) := by
    rw [← hloga]; exact Real.log_le_log ha (by linarith)
  have hlog4 : log 4 < 1.3863 := by
    have : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [this]; linarith [log_two_lt_d9]
  have h22 : 22 ≤ log (t ^ T / (1 - t ^ 2)) := by rw [hlogU]; linarith
  refine ⟨h22, ?_⟩
  have : log (t ^ T / (1 - t ^ 2)) < log (1 + t ^ T / (1 - t ^ 2)) :=
    Real.log_lt_log hU0 (by linarith)
  linarith

/-- Paper, Proposition 6.2, with its hypotheses: `W ≥ 1/24`, `(2T)³ ≤ V < (48T)³` and `κ = 3 W V`
(the paper's `β`) give `κ ≥ T³`, so the kernel bound exceeds `44`, while the threshold
`V/(161 (48T)³)` of Corollary 4.2 is below `1/161`. -/
theorem kernel_route_window {W V : ℝ} {T : ℕ} (hT : 3 ≤ T) (hW : 1 / 24 ≤ W)
    (hV : (2 * (T : ℝ)) ^ 3 ≤ V) (hV' : V < (48 * (T : ℝ)) ^ 3) :
    (T : ℝ) ^ 3 ≤ 3 * W * V ∧
      V / (161 * (48 * (T : ℝ)) ^ 3) < 1 / 161 ∧
      1 / 161 < 44 ∧
      44 < 2 * log (1 + tanh (3 * W * V / 2) ^ T / (1 - tanh (3 * W * V / 2) ^ 2)) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hV0 : 0 < V := lt_of_lt_of_le (by positivity) hV
  have hk : (T : ℝ) ^ 3 ≤ 3 * W * V := by
    have : 3 * (1 / 24) * V ≤ 3 * W * V := by
      apply mul_le_mul_of_nonneg_right _ hV0.le; linarith
    nlinarith
  have h48 : (0 : ℝ) < (48 * (T : ℝ)) ^ 3 := by positivity
  refine ⟨hk, ?_, by norm_num, (kernel_route_large hT hk).2⟩
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

end MassGap.PurityScalar

#print axioms MassGap.PurityScalar.ascent
#print axioms MassGap.PurityScalar.ascent_wilson
#print axioms MassGap.PurityScalar.constant_tolerance
#print axioms MassGap.PurityScalar.bulk_cancel
#print axioms MassGap.PurityScalar.bulk_cancel_pressure
#print axioms MassGap.PurityScalar.separate_bounds
#print axioms MassGap.PurityScalar.telescope
#print axioms MassGap.PurityScalar.multiscale
#print axioms MassGap.PurityScalar.fine_seed
#print axioms MassGap.PurityScalar.geom_mass
#print axioms MassGap.PurityScalar.geom_purity
#print axioms MassGap.PurityScalar.geom_normalized_purity
#print axioms MassGap.PurityScalar.geom_defect_ge
#print axioms MassGap.PurityScalar.arsinh_le_self_of_nonneg
#print axioms MassGap.PurityScalar.omegaL
#print axioms MassGap.PurityScalar.modeQ
#print axioms MassGap.PurityScalar.freq_le
#print axioms MassGap.PurityScalar.freq_pos
#print axioms MassGap.PurityScalar.modeQ_pos
#print axioms MassGap.PurityScalar.modeQ_lt_one
#print axioms MassGap.PurityScalar.exp_pi_lt
#print axioms MassGap.PurityScalar.inv81_lt_exp_neg_pi
#print axioms MassGap.PurityScalar.inv81_lt_modeQ
#print axioms MassGap.PurityScalar.budget_eq
#print axioms MassGap.PurityScalar.gaussian_mode_defect
#print axioms MassGap.PurityScalar.product_defect
#print axioms MassGap.PurityScalar.kernel_route_large
#print axioms MassGap.PurityScalar.fine_seed_window
#print axioms MassGap.PurityScalar.constant_root
#print axioms MassGap.PurityScalar.gaussian_product_defect
#print axioms MassGap.PurityScalar.kernel_route_window
