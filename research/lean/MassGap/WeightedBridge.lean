import Mathlib
import MassGap.HeatBathGapDecay
import MassGap.WeightedKnabe

noncomputable section

/-!
# MassGap.WeightedBridge — the ratio gap of `WeightedKnabe` from the patch gap in the tree's form

`WeightedKnabe.weighted_gap` consumes at each patch the ratio gap
`γ · B(A x, x)² ≤ B(A x, A x) · B(F x, x)` (`A` the weighted patch, `F` the unweighted one). The tree's
finite check (`BoxPatch.BoxLocalGap`, from `BoxGap.BoxFibreGap`) states the unweighted patch gap as
`γ · B(F x, x) ≤ B(F x, F x)`. On a Hilbert space the two are linked by the spectral theorem. This
module links them on a module with a symmetric non-negative form, with no completion: the lazy step
`T = id − F/K` drives `x` towards the null part of `F` geometrically, and `x − Tⁿx` lies in the range
of `F`, where the gap is a Poincaré inequality.

## What it gives

1. `step_form_le`: `B(Tv, Tv) ≤ B(v, v) − B(Fv, v)/K` (needs `B(Fv, Fv) ≤ K · B(Fv, v)`).
2. `range_poincare`: on the range of `F`, `γ · B(Fu, Fu) ≤ B(F(Fu), Fu)`.
3. `iter_F_form_le`: `B(F Tⁿx, F Tⁿx) ≤ (1 − γ/K)ⁿ · B(Fx, Fx)`; `iter_form_le`: `B(Tⁿx, Tⁿx) ≤ B(x, x)`;
   `sub_iter_mem_range`: `x − Tⁿx = F u` for some `u`.
4. `ratio_of_gap`: with `A` self-adjoint and dominated, `B(Az, Az) ≤ C · B(Fz, z)`, the patch gap
   `γ B(Fx, x) ≤ B(Fx, Fx)` and the bound `B(Fx, Fx) ≤ K B(Fx, x)` (`0 < γ ≤ K`) give the ratio gap
   `γ · B(Ax, x)² ≤ B(Ax, Ax) · B(Fx, x)` at every `x`.
5. `weighted_gap_of_patch_gap`: `WeightedKnabe.weighted_gap` with the patch gap in the tree's form.
-/

namespace MassGap.WeightedBridge

open Filter Topology MassGap.KnabeCriterion

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The lazy step `v ↦ v − (1/K) • F v`.

DERIVED: `1` is the unit of the step. -/
def step (F : E →ₗ[ℝ] E) (K : ℝ) (v : E) : E := v - (1 / K) • F v

/-- The lazy iterates `x, Tx, T²x, …`.

DERIVED: `0`, `1` index the recursion. -/
def iter (F : E →ₗ[ℝ] E) (K : ℝ) (x : E) : ℕ → E
  | 0 => x
  | n + 1 => step F K (iter F K x n)

/-- `F` commutes with the step.

DERIVED: no numeral beyond the step's. -/
theorem F_step (F : E →ₗ[ℝ] E) (K : ℝ) (v : E) : F (step F K v) = step F K (F v) := by
  simp only [step, map_sub, map_smul]

#print axioms F_step

/-- `F` commutes with the iterates: `F (Tⁿ x) = Tⁿ (F x)`.

DERIVED: `0`, `1` index the induction. -/
theorem F_iter (F : E →ₗ[ℝ] E) (K : ℝ) (x : E) (n : ℕ) : F (iter F K x n) = iter F K (F x) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iter, F_step, ih]

#print axioms F_iter

/-- `0 ≤ B(Fv, v)` from `B(Fv, Fv) ≤ K · B(Fv, v)`, `0 < K`.

DERIVED: `0` is the sign of the form and of `K`. -/
theorem form_F_nonneg (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hnn : ∀ x, 0 ≤ B x x) (F : E →ₗ[ℝ] E) {K : ℝ}
    (hK0 : 0 < K) (hK : ∀ x, B (F x) (F x) ≤ K * B (F x) x) (v : E) : 0 ≤ B (F v) v := by
  have h1 := hnn (F v)
  have h2 := hK v
  by_contra hneg
  push Not at hneg
  have : K * B (F v) v < 0 := mul_neg_of_pos_of_neg hK0 hneg
  linarith

#print axioms form_F_nonneg

/-- **One lazy step.** `B(Tv, Tv) ≤ B(v, v) − B(Fv, v)/K`.

DERIVED: `1`, `2` are the expansion's coefficients. -/
theorem step_form_le (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (F : E →ₗ[ℝ] E) {K : ℝ} (hK0 : 0 < K) (hK : ∀ x, B (F x) (F x) ≤ K * B (F x) x) (v : E) :
    B (step F K v) (step F K v) ≤ B v v - (1 / K) * B (F v) v := by
  have hexp : B (step F K v) (step F K v)
      = B v v - 2 * (1 / K) * B (F v) v + (1 / K) ^ 2 * B (F v) (F v) := by
    simp only [step, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hsymm v (F v)]
    ring
  rw [hexp]
  have h2 := hK v
  have hk : 0 < 1 / K := one_div_pos.mpr hK0
  have h3 : (1 / K) ^ 2 * B (F v) (F v) ≤ (1 / K) ^ 2 * (K * B (F v) v) :=
    mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have h4 : (1 / K) ^ 2 * (K * B (F v) v) = (1 / K) * B (F v) v := by
    field_simp
  linarith

#print axioms step_form_le

/-- **The gap on the range of `F` is a Poincaré inequality.** From `γ B(Fx, x) ≤ B(Fx, Fx)` at
every `x` and `B(Fx, Fx) ≤ K B(Fx, x)`: `γ · B(Fu, Fu) ≤ B(F(Fu), Fu)`. Cauchy–Schwarz for the form
`(a, b) ↦ B(Fa, b)` gives `B(Fu, Fu)² ≤ B(Fu, u) · B(F(Fu), Fu)`.

DERIVED: `0` is the sign of the forms; `2` is the square of Cauchy–Schwarz. -/
theorem range_poincare (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (F : E →ₗ[ℝ] E) (hsF : ∀ x y, B (F x) y = B x (F y)) {γ K : ℝ}
    (hγ : 0 < γ) (hK0 : 0 < K) (hgap : ∀ x, γ * B (F x) x ≤ B (F x) (F x))
    (hK : ∀ x, B (F x) (F x) ≤ K * B (F x) x) (u : E) :
    γ * B (F u) (F u) ≤ B (F (F u)) (F u) := by
  set Q : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := B.comp F with hQ
  have hQapp : ∀ a b, Q a b = B (F a) b := fun a b => rfl
  have hQsymm : ∀ a b, Q a b = Q b a := by
    intro a b
    rw [hQapp, hQapp, hsF, hsymm]
  have hQnn : ∀ a, 0 ≤ Q a a := fun a => by
    rw [hQapp]; exact form_F_nonneg B hnn F hK0 hK a
  have hcs := MassGap.HeatBathGapDecay.form_sq_le_mul Q hQsymm hQnn u (F u)
  rw [hQapp, hQapp, hQapp] at hcs
  -- hcs : B (F u) (F u) ^ 2 ≤ B (F u) u * B (F (F u)) (F u)
  have hg := hgap u
  have hFFu := hQnn (F u)
  rw [hQapp] at hFFu
  have hFu0 := hnn (F u)
  rcases eq_or_lt_of_le hFu0 with h0 | hpos
  · rw [← h0, mul_zero]; exact hFFu
  · -- γ B(Fu,Fu)² ≤ γ B(Fu,u) B(FFu,Fu) ≤ B(Fu,Fu) B(FFu,Fu)
    have h1 : γ * B (F u) (F u) ^ 2 ≤ B (F u) (F u) * B (F (F u)) (F u) := by
      calc γ * B (F u) (F u) ^ 2 ≤ γ * (B (F u) u * B (F (F u)) (F u)) :=
            mul_le_mul_of_nonneg_left hcs hγ.le
        _ = (γ * B (F u) u) * B (F (F u)) (F u) := by ring
        _ ≤ B (F u) (F u) * B (F (F u)) (F u) := mul_le_mul_of_nonneg_right hg hFFu
    have h2 : (γ * B (F u) (F u)) * B (F u) (F u) ≤ B (F (F u)) (F u) * B (F u) (F u) := by
      nlinarith [h1]
    exact le_of_mul_le_mul_right h2 hpos

#print axioms range_poincare

/-- **The step contracts the range of `F`.** For `v = F u`: `B(Tv, Tv) ≤ (1 − γ/K) · B(v, v)`.

DERIVED: `1` is the unit of the rate. -/
theorem step_range_le (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (F : E →ₗ[ℝ] E) (hsF : ∀ x y, B (F x) y = B x (F y)) {γ K : ℝ}
    (hγ : 0 < γ) (hK0 : 0 < K) (hgap : ∀ x, γ * B (F x) x ≤ B (F x) (F x))
    (hK : ∀ x, B (F x) (F x) ≤ K * B (F x) x) (u : E) :
    B (step F K (F u)) (step F K (F u)) ≤ (1 - γ / K) * B (F u) (F u) := by
  have h1 := step_form_le B hsymm F hK0 hK (F u)
  have h2 := range_poincare B hsymm hnn F hsF hγ hK0 hgap hK u
  have hk : 0 < 1 / K := one_div_pos.mpr hK0
  have h3 : (1 / K) * (γ * B (F u) (F u)) ≤ (1 / K) * B (F (F u)) (F u) :=
    mul_le_mul_of_nonneg_left h2 hk.le
  have h4 : (1 - γ / K) * B (F u) (F u) = B (F u) (F u) - (1 / K) * (γ * B (F u) (F u)) := by
    field_simp
  linarith

#print axioms step_range_le

/-- `B(F Tⁿx, F Tⁿx) ≤ (1 − γ/K)ⁿ · B(Fx, Fx)`.

DERIVED: `0`, `1` index the induction; `1` is the unit of the rate. -/
theorem iter_F_form_le (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (F : E →ₗ[ℝ] E) (hsF : ∀ x y, B (F x) y = B x (F y)) {γ K : ℝ}
    (hγ : 0 < γ) (hK0 : 0 < K) (hγK : γ ≤ K) (hgap : ∀ x, γ * B (F x) x ≤ B (F x) (F x))
    (hK : ∀ x, B (F x) (F x) ≤ K * B (F x) x) (x : E) (n : ℕ) :
    B (F (iter F K x n)) (F (iter F K x n)) ≤ (1 - γ / K) ^ n * B (F x) (F x) := by
  have hρ0 : 0 ≤ 1 - γ / K := by
    rw [sub_nonneg, div_le_one hK0]; exact hγK
  induction n with
  | zero => simp [iter]
  | succ n ih =>
    show B (F (step F K (iter F K x n))) (F (step F K (iter F K x n))) ≤ _
    rw [F_step]
    calc B (step F K (F (iter F K x n))) (step F K (F (iter F K x n)))
        ≤ (1 - γ / K) * B (F (iter F K x n)) (F (iter F K x n)) :=
          step_range_le B hsymm hnn F hsF hγ hK0 hgap hK (iter F K x n)
      _ ≤ (1 - γ / K) * ((1 - γ / K) ^ n * B (F x) (F x)) := mul_le_mul_of_nonneg_left ih hρ0
      _ = (1 - γ / K) ^ (n + 1) * B (F x) (F x) := by ring

#print axioms iter_F_form_le

/-- The iterates do not grow: `B(Tⁿx, Tⁿx) ≤ B(x, x)`.

DERIVED: `0`, `1` index the induction. -/
theorem iter_form_le (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (F : E →ₗ[ℝ] E) {K : ℝ} (hK0 : 0 < K)
    (hK : ∀ x, B (F x) (F x) ≤ K * B (F x) x) (x : E) (n : ℕ) :
    B (iter F K x n) (iter F K x n) ≤ B x x := by
  induction n with
  | zero => exact le_refl _
  | succ n ih =>
    have h1 := step_form_le B hsymm F hK0 hK (iter F K x n)
    have h2 := form_F_nonneg B hnn F hK0 hK (iter F K x n)
    have hk : 0 ≤ 1 / K := (one_div_pos.mpr hK0).le
    have h3 : 0 ≤ (1 / K) * B (F (iter F K x n)) (iter F K x n) := mul_nonneg hk h2
    show B (step F K (iter F K x n)) (step F K (iter F K x n)) ≤ B x x
    linarith

#print axioms iter_form_le

/-- `x − Tⁿx` lies in the range of `F`.

DERIVED: `0`, `1` index the induction. -/
theorem sub_iter_mem_range (F : E →ₗ[ℝ] E) (K : ℝ) (x : E) (n : ℕ) :
    ∃ u, x - iter F K x n = F u := by
  induction n with
  | zero => exact ⟨0, by simp [iter]⟩
  | succ n ih =>
    obtain ⟨u, hu⟩ := ih
    refine ⟨u + (1 / K) • iter F K x n, ?_⟩
    show x - step F K (iter F K x n) = F (u + (1 / K) • iter F K x n)
    rw [map_add, map_smul, ← hu]
    simp only [step]
    abel

#print axioms sub_iter_mem_range

/-- A real sequence whose square is dominated by a null sequence is null.

DERIVED: `0` is the limit; `2` is the square. -/
theorem tendsto_zero_of_sq_le {g h : ℕ → ℝ} (hle : ∀ n, g n ^ 2 ≤ h n)
    (hh : Tendsto h atTop (𝓝 0)) : Tendsto g atTop (𝓝 0) := by
  have hs : Tendsto (fun n => Real.sqrt (h n)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hh
    simpa [Function.comp_def] using this
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero (fun n => abs_nonneg _) (fun n => Real.abs_le_sqrt (hle n)) hs

#print axioms tendsto_zero_of_sq_le

/-- **The ratio gap from the patch gap.** `B` symmetric non-negative; `F`, `A` self-adjoint for `B`;
`0 < γ ≤ K`; the patch gap `γ B(Fx, x) ≤ B(Fx, Fx)` and the bound `B(Fx, Fx) ≤ K B(Fx, x)` at every
`x`; `A` dominated by `F`: `B(Az, Az) ≤ C · B(Fz, z)`. Then at every `x`:
`γ · B(Ax, x)² ≤ B(Ax, Ax) · B(Fx, x)`.

The proof: `yₙ = x − Tⁿx = F uₙ` has `γ B(yₙ, yₙ) ≤ B(Fyₙ, yₙ)` (`range_poincare`), so the ratio
gap holds at `yₙ` by Cauchy–Schwarz; the remainder `Tⁿx` has `B(F Tⁿx, Tⁿx) ≤ (1 − γ/K)ⁿ B(Fx, Fx)/γ`,
so every term it contributes is null, and the inequality passes to the limit.

DERIVED: `0` is the sign of the form and of `γ`, and the limit of the remainders; `2` is the
square and the cross-term coefficient. -/
theorem ratio_of_gap (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (F A : E →ₗ[ℝ] E) (hsF : ∀ x y, B (F x) y = B x (F y))
    (hsA : ∀ x y, B (A x) y = B x (A y)) {γ K C : ℝ} (hγ : 0 < γ) (hK0 : 0 < K) (hγK : γ ≤ K)
    (hgap : ∀ x, γ * B (F x) x ≤ B (F x) (F x))
    (hK : ∀ x, B (F x) (F x) ≤ K * B (F x) x) (hAF : ∀ z, B (A z) (A z) ≤ C * B (F z) z)
    (x : E) :
    γ * B (A x) x ^ 2 ≤ B (A x) (A x) * B (F x) x := by
  set z : ℕ → E := fun n => iter F K x n with hz
  set ρ := 1 - γ / K with hρ
  have hρ0 : 0 ≤ ρ := by rw [hρ, sub_nonneg, div_le_one hK0]; exact hγK
  have hρ1 : ρ < 1 := by rw [hρ]; have := div_pos hγ hK0; linarith
  have hpow : Tendsto (fun n => ρ ^ n) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
  -- the remainder's F-energy and its square norm
  have hFz : ∀ n, B (F (z n)) (F (z n)) ≤ ρ ^ n * B (F x) (F x) := fun n =>
    iter_F_form_le B hsymm hnn F hsF hγ hK0 hγK hgap hK x n
  have hzz : ∀ n, B (z n) (z n) ≤ B x x := fun n => iter_form_le B hsymm hnn F hK0 hK x n
  have hFFx := hnn (F x)
  have hxx := hnn x
  have hAxx := hnn (A x)
  -- d n = B(F z, z) ≤ ρⁿ B(Fx,Fx)/γ
  have hd : ∀ n, B (F (z n)) (z n) ≤ ρ ^ n * B (F x) (F x) / γ := by
    intro n
    have h1 := hgap (z n)
    rw [le_div_iff₀ hγ]
    linarith [hFz n]
  have hd0 : ∀ n, 0 ≤ B (F (z n)) (z n) := fun n => form_F_nonneg B hnn F hK0 hK (z n)
  have hdlim : Tendsto (fun n => ρ ^ n * B (F x) (F x) / γ) atTop (𝓝 0) := by
    have := (hpow.mul_const (B (F x) (F x))).div_const γ
    simpa using this
  have hdt : Tendsto (fun n => B (F (z n)) (z n)) atTop (𝓝 0) :=
    squeeze_zero hd0 hd hdlim
  -- f n = B(Az, Az) ≤ C d n
  have hft : Tendsto (fun n => B (A (z n)) (A (z n))) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => C * B (F (z n)) (z n)) atTop (𝓝 0) := by
      simpa using hdt.const_mul C
    exact squeeze_zero (fun n => hnn _) (fun n => hAF (z n)) hlim
  have hcs := MassGap.HeatBathGapDecay.form_sq_le_mul B hsymm hnn
  -- a n = B(Az, x), b n = B(Az, z), e n = B(Ax, Az), c n = B(Fz, x)
  have hat : Tendsto (fun n => B (A (z n)) x) atTop (𝓝 0) := by
    refine tendsto_zero_of_sq_le (h := fun n => B (A (z n)) (A (z n)) * B x x)
      (fun n => hcs _ _) ?_
    simpa using hft.mul_const (B x x)
  have hbt : Tendsto (fun n => B (A (z n)) (z n)) atTop (𝓝 0) := by
    refine tendsto_zero_of_sq_le (h := fun n => B (A (z n)) (A (z n)) * B x x) (fun n => ?_) ?_
    · exact (hcs _ _).trans (mul_le_mul_of_nonneg_left (hzz n) (hnn _))
    · simpa using hft.mul_const (B x x)
  have het : Tendsto (fun n => B (A x) (A (z n))) atTop (𝓝 0) := by
    refine tendsto_zero_of_sq_le (h := fun n => B (A x) (A x) * B (A (z n)) (A (z n)))
      (fun n => hcs _ _) ?_
    simpa using hft.const_mul (B (A x) (A x))
  have hct : Tendsto (fun n => B (F (z n)) x) atTop (𝓝 0) := by
    refine tendsto_zero_of_sq_le (h := fun n => ρ ^ n * B (F x) (F x) * B x x) (fun n => ?_) ?_
    · exact (hcs _ _).trans (mul_le_mul_of_nonneg_right (hFz n) hxx)
    · simpa using (hpow.mul_const (B (F x) (F x))).mul_const (B x x)
  -- the inequality at every n, written through the remainders
  have hineq : ∀ n, γ * (B (A x) x - 2 * B (A (z n)) x + B (A (z n)) (z n)) ^ 2
      ≤ (B (A x) (A x) - 2 * B (A x) (A (z n)) + B (A (z n)) (A (z n)))
        * (B (F x) x - 2 * B (F (z n)) x + B (F (z n)) (z n)) := by
    intro n
    obtain ⟨u, hu⟩ := sub_iter_mem_range F K x n
    set y := x - z n with hy
    have hyu : y = F u := hu
    have hP : γ * B y y ≤ B (F y) y := by
      rw [hyu]; exact range_poincare B hsymm hnn F hsF hγ hK0 hgap hK u
    have hr : γ * B (A y) y ^ 2 ≤ B (A y) (A y) * B (F y) y := by
      have h1 := hcs (A y) y
      have hAyy := hnn (A y)
      calc γ * B (A y) y ^ 2 ≤ γ * (B (A y) (A y) * B y y) := mul_le_mul_of_nonneg_left h1 hγ.le
        _ = B (A y) (A y) * (γ * B y y) := by ring
        _ ≤ B (A y) (A y) * B (F y) y := mul_le_mul_of_nonneg_left hP hAyy
    have e1 : B (A y) y = B (A x) x - 2 * B (A (z n)) x + B (A (z n)) (z n) := by
      rw [hy]
      simp only [map_sub, LinearMap.sub_apply]
      rw [hsA x (z n), hsymm x (A (z n))]
      ring
    have e2 : B (A y) (A y) = B (A x) (A x) - 2 * B (A x) (A (z n)) + B (A (z n)) (A (z n)) := by
      rw [hy]
      simp only [map_sub, LinearMap.sub_apply]
      rw [hsymm (A (z n)) (A x)]
      ring
    have e3 : B (F y) y = B (F x) x - 2 * B (F (z n)) x + B (F (z n)) (z n) := by
      rw [hy]
      simp only [map_sub, LinearMap.sub_apply]
      rw [hsF x (z n), hsymm x (F (z n))]
      ring
    rw [e1, e2, e3] at hr
    exact hr
  -- pass to the limit
  have hL : Tendsto (fun n => (B (A x) (A x) - 2 * B (A x) (A (z n)) + B (A (z n)) (A (z n)))
        * (B (F x) x - 2 * B (F (z n)) x + B (F (z n)) (z n))
      - γ * (B (A x) x - 2 * B (A (z n)) x + B (A (z n)) (z n)) ^ 2) atTop
      (𝓝 ((B (A x) (A x) - 2 * 0 + 0) * (B (F x) x - 2 * 0 + 0)
        - γ * (B (A x) x - 2 * 0 + 0) ^ 2)) := by
    refine Tendsto.sub (Tendsto.mul ?_ ?_) (Tendsto.const_mul γ (Tendsto.pow ?_ 2))
    · exact (tendsto_const_nhds.sub (het.const_mul 2)).add hft
    · exact (tendsto_const_nhds.sub (hct.const_mul 2)).add hdt
    · exact (tendsto_const_nhds.sub (hat.const_mul 2)).add hbt
  have hlim := ge_of_tendsto' hL (fun n => sub_nonneg.mpr (hineq n))
  simp only [mul_zero, sub_zero, add_zero] at hlim
  linarith

#print axioms ratio_of_gap

/-- **`WeightedKnabe.weighted_gap` with the patch gap in the tree's form.** The hypotheses of
`weighted_gap`, with the ratio gap replaced by: at every patch `k`, the unweighted patch gap
`γ B(F_k x, x) ≤ B(F_k x, F_k x)`, the bound `B(F_k x, F_k x) ≤ K B(F_k x, x)`, and the domination
`B(A_k z, A_k z) ≤ C · B(F_k z, z)` (`A = patchOp c h`, `F = patchOp s h`), with `0 < γ ≤ K`.
Conclusion: `(γ a₁²/N − a₂ + b − e) · B(Hx, x) ≤ b · B(Hx, Hx)`.

DERIVED: `0` is the sign of the weights and of `γ`. -/
theorem weighted_gap_of_patch_gap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (h : ι → E →ₗ[ℝ] E)
    (hsa : ∀ i x y, B (h i x) y = B x (h i y)) (hid : ∀ i x, h i (h i x) = h i x)
    (c s : κ → ι → ℝ) (w : ι → ι → ℝ) (hc : ∀ k i, 0 ≤ c k i) (hs : ∀ k i, 0 ≤ s k i)
    {a₁ a₂ b e N γ K C : ℝ}
    (hcov : ∀ i, ∑ k, c k i = a₁) (hcovs : ∀ i, ∑ k, s k i = N) (hN : 0 < N)
    (hγ : 0 < γ) (hK0 : 0 < K) (hγK : γ ≤ K)
    (hcov2 : ∀ i, pairWeight c i i = a₂)
    (hpair : ∀ i j, i ≠ j →
      ((∀ x, h i (h j x) = h j (h i x)) ∧ pairWeight c i j ≤ b) ∨ |pairWeight c i j - b| ≤ w i j)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j ≤ e) (hcol : ∀ j, ∑ i, w i j ≤ e)
    (hgap : ∀ k x, γ * B (patchOp s h k x) x ≤ B (patchOp s h k x) (patchOp s h k x))
    (hK : ∀ k x, B (patchOp s h k x) (patchOp s h k x) ≤ K * B (patchOp s h k x) x)
    (hAF : ∀ k z, B (patchOp c h k z) (patchOp c h k z) ≤ C * B (patchOp s h k z) z) (x : E) :
    (γ * a₁ ^ 2 / N - a₂ + b - e) * B (totalOp h x) x ≤ b * B (totalOp h x) (totalOp h x) := by
  have hself : ∀ (d : κ → ι → ℝ) k x y, B (patchOp d h k x) y = B x (patchOp d h k y) := by
    intro d k x y
    rw [patchOp_apply, patchOp_apply, map_sum, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hsa i x y]
  refine MassGap.WeightedKnabe.weighted_gap B hsymm hnn h hsa hid c s w hc hs hcov hcovs hN hγ.le
    hcov2 hpair hw hrow hcol (fun k y => ?_) x
  exact ratio_of_gap B hsymm hnn (patchOp s h k) (patchOp c h k) (hself s k) (hself c k) hγ hK0 hγK
    (hgap k) (hK k) (hAF k) y

#print axioms weighted_gap_of_patch_gap

end MassGap.WeightedBridge
