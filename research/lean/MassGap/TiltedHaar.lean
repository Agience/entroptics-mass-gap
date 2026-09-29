import Mathlib
import MassGap.PairInterface

noncomputable section

/-!
# MassGap.TiltedHaar — the tilted constants from the Haar constants



## What it gives

`tiltBounds_of_haarConsts`: for a feature `X` with `‖X‖ ≤ 1` and Haar constants `H`, at every
`0 ≤ κ ≤ 3` and `s ≥ √(q4/D)`,
`TiltBounds P X κ (M2bound H.D H.q4 H.t3 κ) (mbarBound H.D H.q4 H.t3 s κ)`. Group-independent.

## The route

* **No evaluation of `exp` at any point.** `Complex.exp_bound'` at `n = 6` (hypothesis
  `‖x‖/7 ≤ 1/2`, conclusion `‖exp x − Σ_{m<6} xᵐ/m!‖ ≤ ‖x‖⁶/6! · 2`), cast to `ℝ` through
  `Complex.ofReal_exp`, gives `exp_taylor6` on `|y| ≤ 3`; `|y|ᵏ ≤ r^{k−2} y²` turns it into
  `exp_sub_one_sub_le` and `abs_exp_sub_quad_le` with the polynomial coefficients `cR r`, `cR3 r`.
  `Real.exp_bound` (hypothesis `|x| ≤ 1`) does not reach `κ = 10 β̄₃ = 1.762`; `Complex.exp_bound'`
  does.
* **No subdivision of `[0, κ]`.** The partition function obeys `E e^{⟪θ, X⟫} ≥ 1 + E⟪θ, X⟫ = 1`
  (`Real.add_one_le_exp`, `HaarConsts.mean`), and every numerator bound is a polynomial in `r = ‖θ‖`
  with non-negative coefficients, so its value at `κ` bounds it on `[0, κ]`.
* Second moment: `e^y ≤ 1 + y + cR(κ) y²` on `|y| ≤ κ`, times `⟪u, X⟫² ≥ 0`:
  `E⟪u,X⟫² e^{⟪θ,X⟫} ≤ ‖u‖²/D + t3 ‖u‖² κ + cR(κ) q4 ‖u‖² κ²` (the last by Cauchy–Schwarz from
  `HaarConsts.fourth`, in the quadratic-form version `PairInterface.abs_le_of_quad`).
* Mean: `e^y = 1 + y + y²/2 + R₃(y)`, `|R₃(y)| ≤ cR3(κ) y²`:
  `|E⟪w,X⟫ e^{⟪θ,X⟫}| ≤ ‖w‖κ/D + t3 ‖w‖ κ²/2 + cR3(κ) √(1/D) √q4 κ² ‖w‖`, and
  `√(1/D) √q4 ≤ s` enters as `q4/D ≤ s²` in the quadratic form.
-/

namespace MassGap.TiltedHaar

open MeasureTheory
open MassGap.PairInterface

/-! ## 1. Polynomial bounds on `exp` -/

section ExpBounds

/-- **The sixth-order Taylor bound on `|y| ≤ 3`** (`Complex.exp_bound'` at `n = 6`, `Complex.ofReal_exp`).

DERIVED: `3` satisfies `3/7 ≤ 1/2`, the hypothesis of `Complex.exp_bound'` at `n + 1 = 7`; `1, 2, 6,
24, 120` are `m!` for `m ≤ 5`; `2, 3, 4, 5` are the exponents of the Taylor terms; `6` is the order
and the exponent of the remainder; `360 = 6!/2`, the factor `2` of `Complex.exp_bound'`. -/
theorem exp_taylor6 {y : ℝ} (hy : |y| ≤ 3) :
    |Real.exp y - (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120)| ≤ |y| ^ 6 / 360 := by
  have hx : ‖(y : ℂ)‖ / ((Nat.succ 6 : ℕ) : ℝ) ≤ 1 / 2 := by
    have h1 : ‖(y : ℂ)‖ = |y| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have h7 : ((Nat.succ 6 : ℕ) : ℝ) = 7 := by rw [Nat.cast_succ]; norm_num
    rw [h1, h7]
    linarith
  have hC := Complex.exp_bound' hx
  have hR : |Real.exp y - ∑ m ∈ Finset.range 6, y ^ m / (m.factorial : ℝ)|
      ≤ |y| ^ 6 / ((Nat.factorial 6 : ℕ) : ℝ) * 2 := by
    exact_mod_cast hC
  have hs : ∑ m ∈ Finset.range 6, y ^ m / (m.factorial : ℝ)
      = 1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120 := by
    norm_num [Finset.sum_range_succ, Nat.factorial] <;> ring
  have h6 : ((Nat.factorial 6 : ℕ) : ℝ) = 720 := by norm_num [Nat.factorial]
  calc |Real.exp y - (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120)|
      = |Real.exp y - ∑ m ∈ Finset.range 6, y ^ m / (m.factorial : ℝ)| := by rw [hs]
    _ ≤ |y| ^ 6 / ((Nat.factorial 6 : ℕ) : ℝ) * 2 := hR
    _ = |y| ^ 6 / 360 := by rw [h6]; ring

#print axioms exp_taylor6

/-- The powers of `|y|` against `y²` on `|y| ≤ r`: `|y|ᵏ ≤ r^{k−2} y²` for `k = 3, 4, 5, 6`.

DERIVED: `3, 4, 5, 6` are the exponents `k` of `|y|`; `2` is the exponent of `y²`; the powers
`1, 2, 3, 4` of `r` are `k − 2`, from `|y|^{k−2} ≤ r^{k−2}`. -/
private theorem abs_pow_le {y r : ℝ} (hy : |y| ≤ r) :
    |y| ^ 3 ≤ r * y ^ 2 ∧ |y| ^ 4 ≤ r ^ 2 * y ^ 2 ∧ |y| ^ 5 ≤ r ^ 3 * y ^ 2
      ∧ |y| ^ 6 ≤ r ^ 4 * y ^ 2 := by
  have ha0 : 0 ≤ |y| := abs_nonneg y
  have hy2 : |y| ^ 2 = y ^ 2 := sq_abs y
  have hsq : 0 ≤ |y| ^ 2 := sq_nonneg _
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc |y| ^ 3 = |y| * |y| ^ 2 := by ring
      _ ≤ r * |y| ^ 2 := mul_le_mul_of_nonneg_right hy hsq
      _ = r * y ^ 2 := by rw [hy2]
  · calc |y| ^ 4 = |y| ^ 2 * |y| ^ 2 := by ring
      _ ≤ r ^ 2 * |y| ^ 2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha0 hy 2) hsq
      _ = r ^ 2 * y ^ 2 := by rw [hy2]
  · calc |y| ^ 5 = |y| ^ 3 * |y| ^ 2 := by ring
      _ ≤ r ^ 3 * |y| ^ 2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha0 hy 3) hsq
      _ = r ^ 3 * y ^ 2 := by rw [hy2]
  · calc |y| ^ 6 = |y| ^ 4 * |y| ^ 2 := by ring
      _ ≤ r ^ 4 * |y| ^ 2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha0 hy 4) hsq
      _ = r ^ 4 * y ^ 2 := by rw [hy2]

/-- **`e^y − 1 − y ≤ cR r · y²` on `|y| ≤ r ≤ 3`** (`exp_taylor6`, `|y|ᵏ ≤ r^{k−2} y²`).

DERIVED: `1` is `e⁰`; `2` is the square; `3` is `exp_taylor6`'s range. -/
theorem exp_sub_one_sub_le {y r : ℝ} (hy : |y| ≤ r) (hr : r ≤ 3) :
    Real.exp y - 1 - y ≤ cR r * y ^ 2 := by
  have h6 := exp_taylor6 (le_trans hy hr)
  have hup := (abs_le.mp h6).2
  obtain ⟨k3, k4, k5, k6⟩ := abs_pow_le hy
  have hy3 : y ^ 3 ≤ |y| ^ 3 := le_trans (le_abs_self _) (le_of_eq (abs_pow y 3))
  have hy4 : y ^ 4 = |y| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hy5 : y ^ 5 ≤ |y| ^ 5 := le_trans (le_abs_self _) (le_of_eq (abs_pow y 5))
  simp only [cR]
  linarith

#print axioms exp_sub_one_sub_le

/-- **`|e^y − 1 − y − y²/2| ≤ cR3 r · y²` on `|y| ≤ r ≤ 3`.**

DERIVED: `1` is `e⁰`; `2` is the square and `2!`; `3` is `exp_taylor6`'s range. -/
theorem abs_exp_sub_quad_le {y r : ℝ} (hy : |y| ≤ r) (hr : r ≤ 3) :
    |Real.exp y - 1 - y - y ^ 2 / 2| ≤ cR3 r * y ^ 2 := by
  have h6 := exp_taylor6 (le_trans hy hr)
  have hlo := (abs_le.mp h6).1
  have hup := (abs_le.mp h6).2
  obtain ⟨k3, k4, k5, k6⟩ := abs_pow_le hy
  have hy3 : y ^ 3 ≤ |y| ^ 3 := le_trans (le_abs_self _) (le_of_eq (abs_pow y 3))
  have hy3' : -|y| ^ 3 ≤ y ^ 3 := by
    have := neg_abs_le (y ^ 3)
    rwa [abs_pow] at this
  have hy4 : y ^ 4 = |y| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hy4' : 0 ≤ |y| ^ 4 := by positivity
  have hy5 : y ^ 5 ≤ |y| ^ 5 := le_trans (le_abs_self _) (le_of_eq (abs_pow y 5))
  have hy5' : -|y| ^ 5 ≤ y ^ 5 := by
    have := neg_abs_le (y ^ 5)
    rwa [abs_pow] at this
  rw [abs_le]
  constructor
  · simp only [cR3]
    linarith
  · simp only [cR3]
    linarith

#print axioms abs_exp_sub_quad_le

/-- `cR` is non-negative on `r ≥ 0`.

DERIVED: `0` is the sign. -/
theorem cR_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ cR r := by
  have h2 := pow_nonneg hr 2
  have h3 := pow_nonneg hr 3
  have h4 := pow_nonneg hr 4
  simp only [cR]
  linarith

#print axioms cR_nonneg

/-- `cR3` is non-negative on `r ≥ 0`.

DERIVED: `0` is the sign. -/
theorem cR3_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ cR3 r := by
  have h2 := pow_nonneg hr 2
  have h3 := pow_nonneg hr 3
  have h4 := pow_nonneg hr 4
  simp only [cR3]
  linarith

#print axioms cR3_nonneg

end ExpBounds

/-! ## 2. The tilted constants -/

section Tilted

variable {Ω : Type} [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {X : Ω → E}

/-- A linear functional of a feature of norm at most `1` is bounded by `κ` when `‖θ‖ ≤ κ`.

DERIVED: `1` is the norm bound of the feature. -/
private theorem abs_inner_le (hX1 : ∀ g, ‖X g‖ ≤ 1) {κ : ℝ} {θ : E} (hθ : ‖θ‖ ≤ κ) (g : Ω) :
    |inner ℝ θ (X g)| ≤ κ :=
  le_trans (abs_real_inner_le_norm θ (X g))
    (le_trans (mul_le_of_le_one_right (norm_nonneg θ) (hX1 g)) hθ)

/-- **The tilted partition function is at least `1`**: `E e^{⟪θ,X⟫} ≥ 1 + E⟪θ,X⟫ = 1`
(`Real.add_one_le_exp`, `HaarConsts.mean`).

DERIVED: `1` is `e⁰` and the normalisation of `P`. -/
theorem one_le_integral_exp (H : HaarConsts P X) (hX : Continuous X) (θ : E) :
    1 ≤ ∫ g, Real.exp (inner ℝ θ (X g)) ∂P := by
  have hc1 : Continuous fun g => inner ℝ θ (X g) := continuous_const.inner hX
  have hi1 : Integrable (fun g => inner ℝ θ (X g)) P := integrable_of_continuous P hc1
  have hi2 : Integrable (fun g => inner ℝ θ (X g) + 1) P :=
    integrable_of_continuous P (hc1.add continuous_const)
  have hi3 : Integrable (fun g => Real.exp (inner ℝ θ (X g))) P :=
    integrable_of_continuous P (Real.continuous_exp.comp hc1)
  have hmean : ∫ g, (inner ℝ θ (X g) + 1) ∂P = 1 := by
    rw [integral_add hi1 (integrable_const 1), H.mean θ, integral_const, probReal_univ,
      smul_eq_mul]
    ring
  calc (1 : ℝ) = ∫ g, (inner ℝ θ (X g) + 1) ∂P := hmean.symm
    _ ≤ ∫ g, Real.exp (inner ℝ θ (X g)) ∂P :=
        integral_mono hi2 hi3 (fun g => Real.add_one_le_exp _)

#print axioms one_le_integral_exp

/-- **The fourth moment controls the mixed square**: `E⟪u,X⟫²⟪θ,X⟫² ≤ q4 ‖u‖²‖θ‖²`
(the quadratic form `2t a²b² ≤ t² a⁴ + b⁴`, `PairInterface.abs_le_of_quad`, and
`HaarConsts.fourth` twice).

DERIVED: `2` is the square; `q4` is a field. -/
theorem integral_sq_mul_sq_le (H : HaarConsts P X) (hX : Continuous X) (u θ : E) :
    ∫ g, inner ℝ u (X g) ^ 2 * inner ℝ θ (X g) ^ 2 ∂P ≤ H.q4 * ‖u‖ ^ 2 * ‖θ‖ ^ 2 := by
  have hcu := (continuous_const.inner hX : Continuous fun g => inner ℝ u (X g))
  have hcθ := (continuous_const.inner hX : Continuous fun g => inner ℝ θ (X g))
  have hpt : ∀ (t : ℝ) (g : Ω), 2 * t * (inner ℝ u (X g) ^ 2 * inner ℝ θ (X g) ^ 2)
      ≤ t ^ 2 * inner ℝ u (X g) ^ 4 + inner ℝ θ (X g) ^ 4 := by
    intro t g
    nlinarith [sq_nonneg (t * inner ℝ u (X g) ^ 2 - inner ℝ θ (X g) ^ 2)]
  have hq : ∀ t : ℝ, 2 * t * ∫ g, inner ℝ u (X g) ^ 2 * inner ℝ θ (X g) ^ 2 ∂P
      ≤ t ^ 2 * (H.q4 * ‖u‖ ^ 4) + H.q4 * ‖θ‖ ^ 4 := by
    intro t
    have hbase : 2 * t * ∫ g, inner ℝ u (X g) ^ 2 * inner ℝ θ (X g) ^ 2 ∂P
        ≤ t ^ 2 * ∫ g, inner ℝ u (X g) ^ 4 ∂P + ∫ g, inner ℝ θ (X g) ^ 4 ∂P :=
      quad_integral (integrable_of_continuous P ((hcu.pow 2).mul (hcθ.pow 2)))
        (integrable_of_continuous P (hcu.pow 4)) (integrable_of_continuous P (hcθ.pow 4)) hpt t
    have h4u := H.fourth u
    have h4θ := H.fourth θ
    have ht := mul_le_mul_of_nonneg_left h4u (sq_nonneg t)
    linarith
  have hC : 0 ≤ H.q4 * ‖u‖ ^ 2 * ‖θ‖ ^ 2 :=
    mul_nonneg (mul_nonneg H.q4_nonneg (sq_nonneg _)) (sq_nonneg _)
  have habs := abs_le_of_quad (mul_nonneg H.q4_nonneg (pow_nonneg (norm_nonneg u) 4)) hC
    (le_of_eq (by ring)) hq
  exact le_trans (le_abs_self _) habs

#print axioms integral_sq_mul_sq_le

/-- **The tilted second moment** at a tilt of norm at most `κ ≤ 3`.

DERIVED: `0` is the lower end of `κ`; `3` is `exp_sub_one_sub_le`'s range; `1` is the norm bound
of the feature; `2` is the moment order. -/
theorem tilt_second_le (H : HaarConsts P X) (hX : Continuous X) (hX1 : ∀ g, ‖X g‖ ≤ 1)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ3 : κ ≤ 3) {θ : E} (hθ : ‖θ‖ ≤ κ) (u : E) :
    ∫ g, inner ℝ u (X g) ^ 2 * Real.exp (inner ℝ θ (X g)) ∂P
      ≤ M2bound H.D H.q4 H.t3 κ * ‖u‖ ^ 2 * ∫ g, Real.exp (inner ℝ θ (X g)) ∂P := by
  have hcu := (continuous_const.inner hX : Continuous fun g => inner ℝ u (X g))
  have hcθ := (continuous_const.inner hX : Continuous fun g => inner ℝ θ (X g))
  have hcR := cR_nonneg hκ0
  -- the pointwise Taylor bound, times `⟪u, X⟫² ≥ 0`
  have hpt : ∀ g, inner ℝ u (X g) ^ 2 * Real.exp (inner ℝ θ (X g))
      ≤ inner ℝ u (X g) ^ 2 + inner ℝ u (X g) ^ 2 * inner ℝ θ (X g)
        + cR κ * (inner ℝ u (X g) ^ 2 * inner ℝ θ (X g) ^ 2) := by
    intro g
    have h1 := exp_sub_one_sub_le (abs_inner_le hX1 hθ g) hκ3
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (inner ℝ u (X g)))
    nlinarith [h2]
  have hi1 : Integrable (fun g => inner ℝ u (X g) ^ 2) P := integrable_of_continuous P (hcu.pow 2)
  have hi2 : Integrable (fun g => inner ℝ u (X g) ^ 2 * inner ℝ θ (X g)) P :=
    integrable_of_continuous P ((hcu.pow 2).mul hcθ)
  have hi3 : Integrable (fun g => inner ℝ u (X g) ^ 2 * inner ℝ θ (X g) ^ 2) P :=
    integrable_of_continuous P ((hcu.pow 2).mul (hcθ.pow 2))
  have hint : ∫ g, inner ℝ u (X g) ^ 2 * Real.exp (inner ℝ θ (X g)) ∂P
      ≤ ∫ g, inner ℝ u (X g) ^ 2 ∂P + ∫ g, inner ℝ u (X g) ^ 2 * inner ℝ θ (X g) ∂P
        + cR κ * ∫ g, inner ℝ u (X g) ^ 2 * inner ℝ θ (X g) ^ 2 ∂P := by
    calc ∫ g, inner ℝ u (X g) ^ 2 * Real.exp (inner ℝ θ (X g)) ∂P
        ≤ ∫ g, (inner ℝ u (X g) ^ 2 + inner ℝ u (X g) ^ 2 * inner ℝ θ (X g)
            + cR κ * (inner ℝ u (X g) ^ 2 * inner ℝ θ (X g) ^ 2)) ∂P :=
          integral_mono
            (integrable_of_continuous P ((hcu.pow 2).mul (Real.continuous_exp.comp hcθ)))
            ((hi1.fun_add hi2).fun_add (hi3.const_mul (cR κ))) hpt
      _ = ∫ g, inner ℝ u (X g) ^ 2 ∂P + ∫ g, inner ℝ u (X g) ^ 2 * inner ℝ θ (X g) ∂P
            + cR κ * ∫ g, inner ℝ u (X g) ^ 2 * inner ℝ θ (X g) ^ 2 ∂P := by
          rw [integral_add (hi1.fun_add hi2) (hi3.const_mul (cR κ)), integral_add hi1 hi2,
            integral_const_mul]
  have hsec := H.second u
  have hthird := le_trans (le_abs_self _) (H.third u θ)
  have hfour := integral_sq_mul_sq_le H hX u θ
  have hθ2 : ‖θ‖ ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ (norm_nonneg θ) hθ 2
  have hu2 : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
  have k1 : H.t3 * ‖u‖ ^ 2 * ‖θ‖ ≤ H.t3 * ‖u‖ ^ 2 * κ :=
    mul_le_mul_of_nonneg_left hθ (mul_nonneg H.t3_nonneg hu2)
  have k2 : cR κ * (H.q4 * ‖u‖ ^ 2 * ‖θ‖ ^ 2) ≤ cR κ * (H.q4 * ‖u‖ ^ 2 * κ ^ 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hθ2 (mul_nonneg H.q4_nonneg hu2)) hcR
  have k3 := mul_le_mul_of_nonneg_left hfour hcR
  have hM : 0 ≤ M2bound H.D H.q4 H.t3 κ * ‖u‖ ^ 2 := by
    refine mul_nonneg ?_ hu2
    simp only [M2bound]
    have := one_div_pos.mpr H.D_pos
    have := mul_nonneg H.t3_nonneg hκ0
    have := mul_nonneg (mul_nonneg hcR H.q4_nonneg) (sq_nonneg κ)
    linarith
  have hZ := one_le_integral_exp H hX θ
  have hMZ := le_mul_of_one_le_right hM hZ
  have hbound : ∫ g, inner ℝ u (X g) ^ 2 * Real.exp (inner ℝ θ (X g)) ∂P
      ≤ M2bound H.D H.q4 H.t3 κ * ‖u‖ ^ 2 := by
    have e : M2bound H.D H.q4 H.t3 κ * ‖u‖ ^ 2
        = ‖u‖ ^ 2 / H.D + H.t3 * ‖u‖ ^ 2 * κ + cR κ * (H.q4 * ‖u‖ ^ 2 * κ ^ 2) := by
      simp only [M2bound]
      ring
    rw [e]
    linarith
  linarith

#print axioms tilt_second_le

/-- **The tilted mean** at a tilt of norm at most `κ ≤ 3`, with `s ≥ √(q4/D)`.

DERIVED: `0` is the lower end of `κ` and `s`; `3` is `abs_exp_sub_quad_le`'s range; `1` is the norm
bound of the feature; `2` is the square in `s²`. -/
theorem tilt_mean_le (H : HaarConsts P X) (hX : Continuous X) (hX1 : ∀ g, ‖X g‖ ≤ 1)
    {κ s : ℝ} (hκ0 : 0 ≤ κ) (hκ3 : κ ≤ 3) (hs0 : 0 ≤ s) (hs : H.q4 / H.D ≤ s ^ 2)
    {θ : E} (hθ : ‖θ‖ ≤ κ) (w : E) :
    |∫ g, inner ℝ w (X g) * Real.exp (inner ℝ θ (X g)) ∂P|
      ≤ mbarBound H.D H.q4 H.t3 s κ * ‖w‖ * ∫ g, Real.exp (inner ℝ θ (X g)) ∂P := by
  have hcw := (continuous_const.inner hX : Continuous fun g => inner ℝ w (X g))
  have hcθ := (continuous_const.inner hX : Continuous fun g => inner ℝ θ (X g))
  have hD := H.D_pos
  have hcR3 := cR3_nonneg hκ0
  have hcR : Continuous fun g =>
      Real.exp (inner ℝ θ (X g)) - 1 - inner ℝ θ (X g) - inner ℝ θ (X g) ^ 2 / 2 :=
    (((Real.continuous_exp.comp hcθ).sub continuous_const).sub hcθ).sub
      ((hcθ.pow 2).div_const 2)
  have hib : Integrable (fun g => inner ℝ w (X g)) P := integrable_of_continuous P hcw
  have hiby : Integrable (fun g => inner ℝ w (X g) * inner ℝ θ (X g)) P :=
    integrable_of_continuous P (hcw.mul hcθ)
  have hiyb : Integrable (fun g => inner ℝ θ (X g) ^ 2 * inner ℝ w (X g)) P :=
    integrable_of_continuous P ((hcθ.pow 2).mul hcw)
  have hibR : Integrable (fun g => inner ℝ w (X g)
      * (Real.exp (inner ℝ θ (X g)) - 1 - inner ℝ θ (X g) - inner ℝ θ (X g) ^ 2 / 2)) P :=
    integrable_of_continuous P (hcw.mul hcR)
  -- the Taylor decomposition of the integral
  have hsplit : ∫ g, inner ℝ w (X g) * Real.exp (inner ℝ θ (X g)) ∂P
      = ∫ g, inner ℝ w (X g) ∂P + ∫ g, inner ℝ w (X g) * inner ℝ θ (X g) ∂P
        + (1 / 2 * ∫ g, inner ℝ θ (X g) ^ 2 * inner ℝ w (X g) ∂P
          + ∫ g, inner ℝ w (X g)
              * (Real.exp (inner ℝ θ (X g)) - 1 - inner ℝ θ (X g) - inner ℝ θ (X g) ^ 2 / 2)
              ∂P) := by
    rw [← integral_lin2 hiyb hibR (1 / 2), ← integral_add hib hiby,
      ← integral_add (hib.fun_add hiby) ((hiyb.const_mul (1 / 2)).fun_add hibR)]
    exact integral_congr_pointwise (fun g => by ring)
  -- the linear term
  have hlin : |∫ g, inner ℝ w (X g) * inner ℝ θ (X g) ∂P| ≤ ‖w‖ * ‖θ‖ / H.D := by
    have hpt : ∀ (t : ℝ) (g : Ω), 2 * t * (inner ℝ w (X g) * inner ℝ θ (X g))
        ≤ t ^ 2 * inner ℝ w (X g) ^ 2 + inner ℝ θ (X g) ^ 2 := by
      intro t g
      nlinarith [sq_nonneg (t * inner ℝ w (X g) - inner ℝ θ (X g))]
    have hq : ∀ t : ℝ, 2 * t * ∫ g, inner ℝ w (X g) * inner ℝ θ (X g) ∂P
        ≤ t ^ 2 * (‖w‖ ^ 2 / H.D) + ‖θ‖ ^ 2 / H.D := by
      intro t
      have hbase : 2 * t * ∫ g, inner ℝ w (X g) * inner ℝ θ (X g) ∂P
          ≤ t ^ 2 * ∫ g, inner ℝ w (X g) ^ 2 ∂P + ∫ g, inner ℝ θ (X g) ^ 2 ∂P :=
        quad_integral hiby (integrable_of_continuous P (hcw.pow 2))
          (integrable_of_continuous P (hcθ.pow 2)) hpt t
      have h2 := mul_le_mul_of_nonneg_left (H.second w) (sq_nonneg t)
      have h3 := H.second θ
      linarith
    refine abs_le_of_quad (div_nonneg (sq_nonneg _) hD.le)
      (div_nonneg (mul_nonneg (norm_nonneg w) (norm_nonneg θ)) hD.le) (le_of_eq ?_) hq
    ring
  -- the quadratic term
  have hquad : |∫ g, inner ℝ θ (X g) ^ 2 * inner ℝ w (X g) ∂P| ≤ H.t3 * ‖θ‖ ^ 2 * ‖w‖ :=
    H.third θ w
  -- the remainder
  have hrem : |∫ g, inner ℝ w (X g)
      * (Real.exp (inner ℝ θ (X g)) - 1 - inner ℝ θ (X g) - inner ℝ θ (X g) ^ 2 / 2) ∂P|
      ≤ cR3 κ * (s * ‖w‖ * ‖θ‖ ^ 2) := by
    have hcabs : Continuous fun g => |inner ℝ w (X g)| * inner ℝ θ (X g) ^ 2 :=
      (continuous_abs.comp hcw).mul (hcθ.pow 2)
    have hJ : ∫ g, |inner ℝ w (X g)| * inner ℝ θ (X g) ^ 2 ∂P ≤ s * ‖w‖ * ‖θ‖ ^ 2 := by
      have hpt : ∀ (t : ℝ) (g : Ω), 2 * t * (|inner ℝ w (X g)| * inner ℝ θ (X g) ^ 2)
          ≤ t ^ 2 * inner ℝ w (X g) ^ 2 + inner ℝ θ (X g) ^ 4 := by
        intro t g
        have habs2 : t ^ 2 * |inner ℝ w (X g)| ^ 2 = t ^ 2 * inner ℝ w (X g) ^ 2 := by
          rw [sq_abs]
        nlinarith [sq_nonneg (t * |inner ℝ w (X g)| - inner ℝ θ (X g) ^ 2), habs2]
      have hq : ∀ t : ℝ, 2 * t * ∫ g, |inner ℝ w (X g)| * inner ℝ θ (X g) ^ 2 ∂P
          ≤ t ^ 2 * (‖w‖ ^ 2 / H.D) + H.q4 * ‖θ‖ ^ 4 := by
        intro t
        have hbase : 2 * t * ∫ g, |inner ℝ w (X g)| * inner ℝ θ (X g) ^ 2 ∂P
            ≤ t ^ 2 * ∫ g, inner ℝ w (X g) ^ 2 ∂P + ∫ g, inner ℝ θ (X g) ^ 4 ∂P :=
          quad_integral (integrable_of_continuous P hcabs)
            (integrable_of_continuous P (hcw.pow 2)) (integrable_of_continuous P (hcθ.pow 4))
            hpt t
        have h2 := mul_le_mul_of_nonneg_left (H.second w) (sq_nonneg t)
        have h3 := H.fourth θ
        linarith
      have hX4 : 0 ≤ ‖w‖ ^ 2 * ‖θ‖ ^ 4 := by positivity
      have hABC : ‖w‖ ^ 2 / H.D * (H.q4 * ‖θ‖ ^ 4) ≤ (s * ‖w‖ * ‖θ‖ ^ 2) ^ 2 := by
        have e1 : ‖w‖ ^ 2 / H.D * (H.q4 * ‖θ‖ ^ 4) = H.q4 / H.D * (‖w‖ ^ 2 * ‖θ‖ ^ 4) := by
          ring
        have e2 : (s * ‖w‖ * ‖θ‖ ^ 2) ^ 2 = s ^ 2 * (‖w‖ ^ 2 * ‖θ‖ ^ 4) := by ring
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_right hs hX4
      have habs := abs_le_of_quad (div_nonneg (sq_nonneg _) hD.le)
        (mul_nonneg (mul_nonneg hs0 (norm_nonneg w)) (sq_nonneg _)) hABC hq
      exact le_trans (le_abs_self _) habs
    have hptR : ∀ g, |inner ℝ w (X g)
        * (Real.exp (inner ℝ θ (X g)) - 1 - inner ℝ θ (X g) - inner ℝ θ (X g) ^ 2 / 2)|
        ≤ cR3 κ * (|inner ℝ w (X g)| * inner ℝ θ (X g) ^ 2) := by
      intro g
      rw [abs_mul]
      have h1 := abs_exp_sub_quad_le (abs_inner_le hX1 hθ g) hκ3
      have h2 := mul_le_mul_of_nonneg_left h1 (abs_nonneg (inner ℝ w (X g)))
      nlinarith [h2]
    calc |∫ g, inner ℝ w (X g)
          * (Real.exp (inner ℝ θ (X g)) - 1 - inner ℝ θ (X g) - inner ℝ θ (X g) ^ 2 / 2) ∂P|
        ≤ ∫ g, |inner ℝ w (X g)
          * (Real.exp (inner ℝ θ (X g)) - 1 - inner ℝ θ (X g) - inner ℝ θ (X g) ^ 2 / 2)| ∂P :=
          abs_integral_le_integral_abs
      _ ≤ ∫ g, cR3 κ * (|inner ℝ w (X g)| * inner ℝ θ (X g) ^ 2) ∂P :=
          integral_mono (integrable_of_continuous P (continuous_abs.comp (hcw.mul hcR)))
            (integrable_of_continuous P (continuous_const.mul hcabs)) hptR
      _ = cR3 κ * ∫ g, |inner ℝ w (X g)| * inner ℝ θ (X g) ^ 2 ∂P := integral_const_mul _ _
      _ ≤ cR3 κ * (s * ‖w‖ * ‖θ‖ ^ 2) := mul_le_mul_of_nonneg_left hJ hcR3
  -- assemble
  have hθ2 : ‖θ‖ ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ (norm_nonneg θ) hθ 2
  have hw0 := norm_nonneg w
  have k1 : ‖w‖ * ‖θ‖ / H.D ≤ ‖w‖ * κ / H.D :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hθ hw0) hD.le
  have k2 : H.t3 * ‖θ‖ ^ 2 * ‖w‖ ≤ H.t3 * κ ^ 2 * ‖w‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hθ2 H.t3_nonneg) hw0
  have k3 : cR3 κ * (s * ‖w‖ * ‖θ‖ ^ 2) ≤ cR3 κ * (s * ‖w‖ * κ ^ 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hθ2 (mul_nonneg hs0 hw0)) hcR3
  have hmean := H.mean w
  have htot : |∫ g, inner ℝ w (X g) * Real.exp (inner ℝ θ (X g)) ∂P|
      ≤ mbarBound H.D H.q4 H.t3 s κ * ‖w‖ := by
    rw [hsplit, hmean, zero_add]
    have ha1 := abs_add_le (∫ g, inner ℝ w (X g) * inner ℝ θ (X g) ∂P)
      (1 / 2 * ∫ g, inner ℝ θ (X g) ^ 2 * inner ℝ w (X g) ∂P
        + ∫ g, inner ℝ w (X g)
            * (Real.exp (inner ℝ θ (X g)) - 1 - inner ℝ θ (X g) - inner ℝ θ (X g) ^ 2 / 2) ∂P)
    have ha2 := abs_add_le (1 / 2 * ∫ g, inner ℝ θ (X g) ^ 2 * inner ℝ w (X g) ∂P)
      (∫ g, inner ℝ w (X g)
          * (Real.exp (inner ℝ θ (X g)) - 1 - inner ℝ θ (X g) - inner ℝ θ (X g) ^ 2 / 2) ∂P)
    have ha3 : |1 / 2 * ∫ g, inner ℝ θ (X g) ^ 2 * inner ℝ w (X g) ∂P|
        = 1 / 2 * |∫ g, inner ℝ θ (X g) ^ 2 * inner ℝ w (X g) ∂P| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have e : mbarBound H.D H.q4 H.t3 s κ * ‖w‖
        = ‖w‖ * κ / H.D + 1 / 2 * (H.t3 * κ ^ 2 * ‖w‖) + cR3 κ * (s * ‖w‖ * κ ^ 2) := by
      simp only [mbarBound]
      ring
    rw [e]
    linarith
  have hZ := one_le_integral_exp H hX θ
  have hM : 0 ≤ mbarBound H.D H.q4 H.t3 s κ * ‖w‖ := le_trans (abs_nonneg _) htot
  exact le_trans htot (le_mul_of_one_le_right hM hZ)

#print axioms tilt_mean_le

/-- **THE TILTED CONSTANTS FROM THE HAAR CONSTANTS** (`tilt_second_le`, `tilt_mean_le`).

DERIVED: `0` is the lower end of `κ` and `s`; `3` is the range of the `exp` bounds; `1` is the norm
bound of the feature; `2` is the square in `s²`. -/
theorem tiltBounds_of_haarConsts (H : HaarConsts P X) (hX : Continuous X) (hX1 : ∀ g, ‖X g‖ ≤ 1)
    {κ s : ℝ} (hκ0 : 0 ≤ κ) (hκ3 : κ ≤ 3) (hs0 : 0 ≤ s) (hs : H.q4 / H.D ≤ s ^ 2) :
    TiltBounds P X κ (M2bound H.D H.q4 H.t3 κ) (mbarBound H.D H.q4 H.t3 s κ) := by
  intro θ hθ
  exact ⟨fun u => tilt_second_le H hX hX1 hκ0 hκ3 hθ u,
    fun w => tilt_mean_le H hX hX1 hκ0 hκ3 hs0 hs hθ w⟩

#print axioms tiltBounds_of_haarConsts

end Tilted

end MassGap.TiltedHaar
