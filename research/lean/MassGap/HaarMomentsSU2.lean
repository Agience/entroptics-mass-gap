import Mathlib
import MassGap.HaarMoments
import MassGap.PairInterface
import MassGap.SimpleGroup

noncomputable section

/-!
# MassGap.HaarMomentsSU2 — the Haar constants of the `SU(2)` link feature

Every theorem here is proved from explicit left translations of `probHaar (SU 2)`. The feature
lemmas use the `MassGap.PairInterface` statements `inner_realFeature`, `frob_featDual` and
`integrable_of_continuous`.

## What it gives

`haarConsts_su2 : HaarConsts (probHaar (SU 2)) (realFeature 2)` with `D = 4`, `q4 = 1/8`, `t3 = 0`.

## The route (substitution method of the module `MassGap.HaarMoments`, whose declarations live in
namespace `MassGap.SUN`)

Write `U = [[a, −b̄], [b, ā]]`. Every step substitutes `U ↦ A U` for one explicit `A ∈ SU(2)` and
uses `MeasureTheory.integral_mul_left_eq_self`.
1. Phases. `MassGap.SUN.h0 = diag(i, −i)` sends `a ↦ i a`, so `E a² = 0` and `E a³ā = 0`;
   `q8 = diag(ζ, ζ̄)`, `ζ = e^{iπ/4}`, sends `a ↦ ζ a`, so `E a⁴ = 0` (`haar_su2_sq_zero`,
   `haar_su2_pow_four_zero`, `haar_su2_cube_conj_zero`).
2. `E|a|⁴ = 1/3` (`haar_su2_normSq_sq`). With `p = E|a|⁴`, `s = E|a|²|b|²`, `R = Re ab̄`,
   `J = Im ab̄`: `|a|² + |b|² = 1` and `E|a|² = 1/2` give `p + s = 1/2`; `h0` sends `R ↦ −R`, so
   `E R = 0`; `q8` sends `R ↦ −J`, so `E R² = E J²`, and `R² + J² = |a|²|b|²` gives `E R² = s/2`; the
   rotation `rot45 = (1/√2)[[1, 1], [−1, 1]]` sends `a ↦ (a + b)/√2`, `|a|² ↦ 1/2 + R`, so
   `p = 1/4 + E R + E R² = 1/4 + s/2`. Hence `p = 1/3`.
3. With `x = Re a`, `y = Im a`: `h0` sends `(x, y) ↦ (−y, x)`, so `E x² = E y²` and `E x⁴ = E y⁴`,
   and kills `E(x³y + xy³)`; hence `E(Re a)² = (E|a|²)/2 = 1/4` (`haar_su2_re_sq`). `q8` sends
   `x ↦ (x − y)/√2` and `(x − y)⁴/4 = (3/4)(x² + y²)² − x⁴/2 − y⁴/2 − (x³y + xy³)`, so
   `E x⁴ = (3/4)(1/3) − E x⁴`, `E(Re a)⁴ = 1/8` (`haar_su2_re_four`).
4. Transitivity. `⟪w, X U⟫ = Re(c₁a + c₂b)/√2` with `c₁ = F₀₀ + F̄₁₁`, `c₂ = F₀₁ − F̄₁₀`,
   `F = featDual 2 w`, `|c|² ≤ 2‖w‖²`; left multiplication by `(1/|c|)[[c₁, c₂], [−c̄₂, c̄₁]] ∈ SU(2)`
   turns `c₁a + c₂b` into `|c| a` (`exists_rot_su2`), and `MeasureTheory.integral_mul_left_eq_self`
   moves every moment to `a`: `E⟪w, X⟫² = (|c|²/2)(1/4) ≤ ‖w‖²/4`, `E⟪w, X⟫⁴ = (|c|⁴/4)(1/8) ≤ ‖w‖⁴/8`.
5. Parity. `MassGap.SimpleGroup.negOne2 = −1 ∈ SU(2)` has `X(−U) = −X(U)`; odd moments vanish.
-/

namespace MassGap.HaarMomentsSU2

open MeasureTheory
open MassGap.SUN (SU)
open MassGap.CompactGauge (probHaar)
open MassGap.PairInterface
open MassGap.SimpleGroup (negOne2)

/-! ### Membership in `SU(2)` -/

/-- A literal `2 × 2` complex matrix lies in `SU(2)` when its rows are orthonormal and its
determinant is `1`.

DERIVED: `2` is the rank; `0` and `1` index the rows and are the values of `U U†` off and on the
diagonal; `1` is the determinant. -/
private lemma mem_su2_of (p q r s : ℂ)
    (h00 : p * (starRingEnd ℂ) p + q * (starRingEnd ℂ) q = 1)
    (h01 : p * (starRingEnd ℂ) r + q * (starRingEnd ℂ) s = 0)
    (h10 : r * (starRingEnd ℂ) p + s * (starRingEnd ℂ) q = 0)
    (h11 : r * (starRingEnd ℂ) r + s * (starRingEnd ℂ) s = 1)
    (hdet : p * s - q * r = 1) :
    !![p, q; r, s] ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · have hent : ∀ i j : Fin 2, (!![p, q; r, s] * star !![p, q; r, s]) i j
        = !![p, q; r, s] i 0 * (starRingEnd ℂ) (!![p, q; r, s] j 0)
          + !![p, q; r, s] i 1 * (starRingEnd ℂ) (!![p, q; r, s] j 1) := by
      intro i j
      rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.star_apply]
      all_goals rfl
    ext i j
    rw [hent]
    try rw [Matrix.one_fin_two]
    fin_cases i <;> fin_cases j
    · exact h00
    · exact h01
    · exact h10
    · exact h11
  · rw [Matrix.det_fin_two_of]
    exact hdet

/-- A unit vector `(d₁, d₂)` of `ℂ²` is the first row of `[[d₁, d₂], [−d̄₂, d̄₁]] ∈ SU(2)`.

DERIVED: `2` is the rank; `1` is the unit norm. -/
private lemma mem_su2_unit (d₁ d₂ : ℂ)
    (h : d₁ * (starRingEnd ℂ) d₁ + d₂ * (starRingEnd ℂ) d₂ = 1) :
    !![d₁, d₂; -(starRingEnd ℂ) d₂, (starRingEnd ℂ) d₁] ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine mem_su2_of _ _ _ _ h ?_ ?_ ?_ ?_
  · rw [map_neg, Complex.conj_conj, Complex.conj_conj]
    ring
  · ring
  · rw [map_neg, Complex.conj_conj, Complex.conj_conj]
    linear_combination h
  · linear_combination h

/-- `π/4 · i` is `(π/4 : ℝ) · i`.

DERIVED: `4` is the order-`8` phase's denominator. -/
private lemma pi4I_eq : (Real.pi / 4 * Complex.I : ℂ) = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by
  first
    | (push_cast; ring)
    | push_cast
    | (rw [Complex.ofReal_div]; norm_num)

/-- `conj(iπ/4) = −iπ/4`.

DERIVED: `4` as in `pi4I_eq`. -/
private lemma conj_pi4I :
    (starRingEnd ℂ) (Real.pi / 4 * Complex.I : ℂ) = -(Real.pi / 4 * Complex.I) := by
  rw [pi4I_eq, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- `conj ζ = ζ̄`, `ζ = e^{iπ/4}`.

DERIVED: `4` as in `pi4I_eq`. -/
private lemma conj_zeta :
    (starRingEnd ℂ) (Complex.exp (Real.pi / 4 * Complex.I))
      = Complex.exp (-(Real.pi / 4 * Complex.I)) := by
  rw [← Complex.exp_conj, conj_pi4I]

/-- `conj ζ̄ = ζ`.

DERIVED: `4` as in `pi4I_eq`. -/
private lemma conj_zeta' :
    (starRingEnd ℂ) (Complex.exp (-(Real.pi / 4 * Complex.I)))
      = Complex.exp (Real.pi / 4 * Complex.I) := by
  rw [← Complex.exp_conj, map_neg, conj_pi4I, neg_neg]

/-- `ζ ζ̄ = 1`.

DERIVED: `4` as in `pi4I_eq`; `1` is `e⁰`. -/
private lemma zeta_mul_zeta' :
    Complex.exp (Real.pi / 4 * Complex.I) * Complex.exp (-(Real.pi / 4 * Complex.I)) = 1 := by
  rw [Complex.exp_neg, mul_inv_cancel₀ (Complex.exp_ne_zero _)]

/-- `ζ² = i` (`e^{iπ/2} = i`).

DERIVED: `4` as in `pi4I_eq`; `2 = 4/2` is the square and the denominator of `π/2`. -/
private lemma zeta_sq : Complex.exp (Real.pi / 4 * Complex.I) ^ 2 = Complex.I := by
  rw [sq, ← Complex.exp_add]
  have h : (Real.pi / 4 * Complex.I + Real.pi / 4 * Complex.I : ℂ) = Real.pi / 2 * Complex.I := by
    ring
  rw [h, Complex.exp_pi_div_two_mul_I]

/-- `Re ζ = √2/2`.

DERIVED: `4` as in `pi4I_eq`; `√2/2 = cos(π/4)`. -/
private lemma zeta_re : (Complex.exp (Real.pi / 4 * Complex.I)).re = Real.sqrt 2 / 2 := by
  rw [pi4I_eq, Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_four]

/-- `Im ζ = √2/2`.

DERIVED: `4` as in `pi4I_eq`; `√2/2 = sin(π/4)`. -/
private lemma zeta_im : (Complex.exp (Real.pi / 4 * Complex.I)).im = Real.sqrt 2 / 2 := by
  rw [pi4I_eq, Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_four]

/-- `diag(ζ, ζ̄) ∈ SU(2)`.

DERIVED: `4` as in `pi4I_eq`; `0` is the off-diagonal entry; `2` is the rank. -/
private lemma q8_mem :
    !![Complex.exp (Real.pi / 4 * Complex.I), 0; 0, Complex.exp (-(Real.pi / 4 * Complex.I))]
      ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hm := zeta_mul_zeta'
  refine mem_su2_of _ _ _ _ ?_ ?_ ?_ ?_ ?_
  · rw [conj_zeta, map_zero]
    linear_combination hm
  · rw [map_zero]
    ring
  · rw [map_zero]
    ring
  · rw [conj_zeta', map_zero]
    linear_combination hm
  · linear_combination hm

/-- `(√2)² = 2`.

DERIVED: `2` is the radicand and the square. -/
private lemma sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

/-- `(√2)⁴ = 4`.

DERIVED: `4 = 2²`, `2` from `sqrt2_sq`. -/
private lemma sqrt2_pow4 : Real.sqrt 2 ^ 4 = 4 := by
  have h : Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 := by ring
  rw [h, sqrt2_sq]
  norm_num

/-- `(1/√2)(1/√2) = 1/2` in `ℂ`.

DERIVED: `2` is the radicand; `1/2 = 1/(√2)²`. -/
private lemma sqrt2_inv_mul_self :
    ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)] <;> norm_num
  rw [← mul_inv, h] <;> norm_num

/-- `|1/√2|² = 1/2`.

DERIVED: `2` is the radicand; `1/2 = (√2)⁻¹ · (√2)⁻¹`, as `sqrt2_inv_mul_self`. -/
private lemma normSq_sqrt2_inv : Complex.normSq ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
  rw [Complex.normSq_inv, Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    <;> norm_num

/-- `(1/√2)[[1, 1], [−1, 1]] ∈ SU(2)`.

DERIVED: `2` is the rank and the radicand; `1/2` is `sqrt2_inv_mul_self`. -/
private lemma rot45_mem :
    !![((Real.sqrt 2)⁻¹ : ℂ), ((Real.sqrt 2)⁻¹ : ℂ); -((Real.sqrt 2)⁻¹ : ℂ), ((Real.sqrt 2)⁻¹ : ℂ)]
      ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hs : (starRingEnd ℂ) ((Real.sqrt 2)⁻¹ : ℂ) = ((Real.sqrt 2)⁻¹ : ℂ) := by
    first
      | (rw [map_inv₀, Complex.conj_ofReal])
      | (rw [Complex.conj_ofReal])
  have hc := sqrt2_inv_mul_self
  refine mem_su2_of _ _ _ _ ?_ ?_ ?_ ?_ ?_
  · rw [hs]
    linear_combination 2 * hc
  · rw [map_neg, hs]
    ring
  · rw [hs]
    ring
  · rw [map_neg, hs]
    linear_combination 2 * hc
  · linear_combination 2 * hc

/-- `q8 = diag(e^{iπ/4}, e^{−iπ/4}) ∈ SU(2)`, the phase of order `8`.

DERIVED: `2` is the rank; `4` in `π/4` makes `ζ⁴ = −1`, the least order killing `a⁴` and `a²b̄²`;
`0` is the off-diagonal entry. -/
def q8 : SU 2 :=
  ⟨!![Complex.exp (Real.pi / 4 * Complex.I), 0; 0, Complex.exp (-(Real.pi / 4 * Complex.I))], by
    exact q8_mem⟩

/-- `rot45 = (1/√2)[[1, 1], [−1, 1]] ∈ SU(2)`, mixing the first column's two entries.

DERIVED: `2` is the rank and the `√2` of a unit rotation by `π/4`; `1` is the rotation's entry
before normalisation. -/
def rot45 : SU 2 :=
  ⟨!![((Real.sqrt 2)⁻¹ : ℂ), ((Real.sqrt 2)⁻¹ : ℂ); -((Real.sqrt 2)⁻¹ : ℂ), ((Real.sqrt 2)⁻¹ : ℂ)],
    by exact rot45_mem⟩

/-! ### Entries, translations, integrability -/

/-- DERIVED: `2` is the rank; `0`, `1` index the entries. -/
private lemma negOne_coe : (negOne2 : Matrix (Fin 2) (Fin 2) ℂ) = -1 := rfl

/-- DERIVED: `2` is the rank; `0` indexes the entry; `4` as in `q8`. -/
private lemma q8_00 :
    (q8 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = Complex.exp (Real.pi / 4 * Complex.I) := rfl

/-- DERIVED: `2` is the rank; `0`, `1` index the entry; `0` is its value. -/
private lemma q8_01 : (q8 : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := rfl

/-- DERIVED: `2` is the rank; `1`, `0` index the entry; `0` is its value. -/
private lemma q8_10 : (q8 : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := rfl

/-- DERIVED: `2` is the rank; `1` indexes the entry; `4` as in `q8`. -/
private lemma q8_11 :
    (q8 : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = Complex.exp (-(Real.pi / 4 * Complex.I)) := rfl

/-- DERIVED: `2` is the rank and the radicand; `0` indexes the entry. -/
private lemma rot45_00 : (rot45 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = ((Real.sqrt 2)⁻¹ : ℂ) := rfl

/-- DERIVED: `2` is the rank and the radicand; `0`, `1` index the entry. -/
private lemma rot45_01 : (rot45 : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = ((Real.sqrt 2)⁻¹ : ℂ) := rfl

/-- The entries of a product in `SU(2)`.

DERIVED: `2` is the rank; `0`, `1` are the summation index. -/
private lemma mul_entry (A U : SU 2) (i j : Fin 2) :
    ((A * U : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) i j
      = (A : Matrix (Fin 2) (Fin 2) ℂ) i 0 * (U : Matrix (Fin 2) (Fin 2) ℂ) 0 j
        + (A : Matrix (Fin 2) (Fin 2) ℂ) i 1 * (U : Matrix (Fin 2) (Fin 2) ℂ) 1 j := by
  rw [Submonoid.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- Left translation preserves real Haar integrals.

DERIVED: `2` is the rank. -/
private lemma int_left (f : SU 2 → ℝ) (A : SU 2) :
    ∫ U, f (A * U) ∂(probHaar (SU 2)) = ∫ U, f U ∂(probHaar (SU 2)) := by
  haveI := MassGap.CompactGauge.isMulLeftInvariant_probHaar (SU 2)
  exact integral_mul_left_eq_self f A

/-- A real function odd under one left translation has Haar integral `0`.

DERIVED: `2` is the rank; `0` is the value. -/
private lemma int_zero_of_odd (f : SU 2 → ℝ) (A : SU 2) (hf : ∀ U : SU 2, f (A * U) = -f U) :
    ∫ U, f U ∂(probHaar (SU 2)) = 0 := by
  have h : ∫ U, f U ∂(probHaar (SU 2)) = -∫ U, f U ∂(probHaar (SU 2)) := by
    calc ∫ U, f U ∂(probHaar (SU 2)) = ∫ U, f (A * U) ∂(probHaar (SU 2)) := (int_left f A).symm
      _ = ∫ U, -f U ∂(probHaar (SU 2)) := integral_congr_ae (Filter.Eventually.of_forall hf)
      _ = -∫ U, f U ∂(probHaar (SU 2)) := integral_neg f
  linarith

/-- A complex function multiplied by a phase `φ ≠ 1` under one left translation has Haar integral
`0`.

DERIVED: `2` is the rank; `1` is the excluded phase; `0` is the value. -/
private lemma int_zero_of_phase (f : SU 2 → ℂ) (A : SU 2) (φ : ℂ) (hφ : φ ≠ 1)
    (hf : ∀ U : SU 2, f (A * U) = φ * f U) :
    ∫ U, f U ∂(probHaar (SU 2)) = 0 := by
  haveI := MassGap.CompactGauge.isMulLeftInvariant_probHaar (SU 2)
  have step : ∫ U, f U ∂(probHaar (SU 2)) = φ * ∫ U, f U ∂(probHaar (SU 2)) := by
    calc ∫ U, f U ∂(probHaar (SU 2)) = ∫ U, f (A * U) ∂(probHaar (SU 2)) :=
          (integral_mul_left_eq_self f A).symm
      _ = ∫ U, φ * f U ∂(probHaar (SU 2)) := integral_congr_ae (Filter.Eventually.of_forall hf)
      _ = φ * ∫ U, f U ∂(probHaar (SU 2)) := integral_const_mul φ f
  have hz : (1 - φ) * ∫ U, f U ∂(probHaar (SU 2)) = 0 := by
    rw [sub_mul, one_mul, ← step, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm hφ))

/-- Continuous real functions on `SU(2)` are Haar integrable.

DERIVED: `2` is the rank. -/
private lemma intg {f : SU 2 → ℝ} (hf : Continuous f) : Integrable f (probHaar (SU 2)) := by
  haveI := MassGap.CompactGauge.isProbabilityMeasure_probHaar (SU 2)
  exact integrable_of_continuous (probHaar (SU 2)) hf

/-- The Haar integral of a constant.

DERIVED: `2` is the rank. -/
private lemma int_const (c : ℝ) : ∫ _U : SU 2, c ∂(probHaar (SU 2)) = c := by
  haveI := MassGap.CompactGauge.isProbabilityMeasure_probHaar (SU 2)
  first
    | (rw [integral_const, MeasureTheory.measureReal_def, measure_univ, ENNReal.toReal_one,
        one_smul])
    | simp

/-- Linearity of the Haar integral in the shape `k₁a − k₂b − k₃c − d`.

DERIVED: `2` is the rank. -/
private lemma int_comb (a b c d : SU 2 → ℝ) (ha : Continuous a) (hb : Continuous b)
    (hc : Continuous c) (hd : Continuous d) (k₁ k₂ k₃ : ℝ) :
    ∫ U, (k₁ * a U - k₂ * b U - k₃ * c U - d U) ∂(probHaar (SU 2))
      = k₁ * ∫ U, a U ∂(probHaar (SU 2)) - k₂ * ∫ U, b U ∂(probHaar (SU 2))
        - k₃ * ∫ U, c U ∂(probHaar (SU 2)) - ∫ U, d U ∂(probHaar (SU 2)) := by
  have hA : Continuous (fun U => k₁ * a U) := continuous_const.mul ha
  have hB : Continuous (fun U => k₂ * b U) := continuous_const.mul hb
  have hC : Continuous (fun U => k₃ * c U) := continuous_const.mul hc
  have hAB : Continuous (fun U => k₁ * a U - k₂ * b U) := hA.sub hB
  have hABC : Continuous (fun U => k₁ * a U - k₂ * b U - k₃ * c U) := hAB.sub hC
  rw [integral_sub (intg hABC) (intg hd), integral_sub (intg hAB) (intg hC),
    integral_sub (intg hA) (intg hB), integral_const_mul, integral_const_mul, integral_const_mul]

/-- DERIVED: `2` is the rank; `0` is the index of `a = U₀₀`. -/
private lemma int_left_re2 (A : SU 2) :
    ∫ U : SU 2, (((A * U : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 2 ∂(probHaar (SU 2))
      = ∫ U : SU 2, ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 2 ∂(probHaar (SU 2)) :=
  int_left (fun U : SU 2 => ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 2) A

/-- DERIVED: `2` is the rank; `0` is the index of `a`; `4` is the moment order. -/
private lemma int_left_re4 (A : SU 2) :
    ∫ U : SU 2, (((A * U : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 4 ∂(probHaar (SU 2))
      = ∫ U : SU 2, ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 4 ∂(probHaar (SU 2)) :=
  int_left (fun U : SU 2 => ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 4) A

/-- DERIVED: `2` is the rank; `i`, `j` index the entry. -/
private lemma cont_entry (i j : Fin 2) :
    Continuous (fun U : SU 2 => (U : Matrix (Fin 2) (Fin 2) ℂ) i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

/-! ### The first column: `a = U₀₀`, `b = U₁₀` -/

/-- `a = U₀₀`. DERIVED: `2` is the rank; `0` indexes the entry. -/
private def entA (U : SU 2) : ℂ := (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0

/-- `b = U₁₀`. DERIVED: `2` is the rank; `1`, `0` index the entry. -/
private def entB (U : SU 2) : ℂ := (U : Matrix (Fin 2) (Fin 2) ℂ) 1 0

/-- `|a|²`. DERIVED: `2` is the rank. -/
private def nrmA (U : SU 2) : ℝ := Complex.normSq (entA U)

/-- `|b|²`. DERIVED: `2` is the rank. -/
private def nrmB (U : SU 2) : ℝ := Complex.normSq (entB U)

/-- `Re ab̄`. DERIVED: `2` is the rank. -/
private def crR (U : SU 2) : ℝ := (entA U * (starRingEnd ℂ) (entB U)).re

/-- `Im ab̄`. DERIVED: `2` is the rank. -/
private def crI (U : SU 2) : ℝ := (entA U * (starRingEnd ℂ) (entB U)).im

/-- `x = Re a`. DERIVED: `2` is the rank. -/
private def reA (U : SU 2) : ℝ := (entA U).re

/-- `y = Im a`. DERIVED: `2` is the rank. -/
private def imA (U : SU 2) : ℝ := (entA U).im

private lemma cont_entA : Continuous entA := cont_entry 0 0

private lemma cont_entB : Continuous entB := cont_entry 1 0

private lemma cont_nrmA : Continuous nrmA := Complex.continuous_normSq.comp cont_entA

private lemma cont_nrmB : Continuous nrmB := Complex.continuous_normSq.comp cont_entB

private lemma cont_crR : Continuous crR :=
  Complex.continuous_re.comp (cont_entA.mul (Complex.continuous_conj.comp cont_entB))

private lemma cont_crI : Continuous crI :=
  Complex.continuous_im.comp (cont_entA.mul (Complex.continuous_conj.comp cont_entB))

private lemma cont_reA : Continuous reA := Complex.continuous_re.comp cont_entA

private lemma cont_imA : Continuous imA := Complex.continuous_im.comp cont_entA

/-- `E|a|² = 1/2` (`MassGap.SUN.f00_mean`).

DERIVED: `1/2` is the second moment of `MassGap.SUN.haar_su2_second_moment`. -/
private lemma int_nrmA : ∫ U : SU 2, nrmA U ∂(probHaar (SU 2)) = 1 / 2 := MassGap.SUN.f00_mean

/-- The first column is a unit vector: `|a|² + |b|² = 1`.

DERIVED: `2` is the rank; `1` is the `(0, 0)` entry of `U†U = 1`. -/
private lemma nrmA_add_nrmB (U : SU 2) : nrmA U + nrmB U = 1 := by
  have hu : star (U : Matrix (Fin 2) (Fin 2) ℂ) * (U : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp U.2).1
  have h0 : (star (U : Matrix (Fin 2) (Fin 2) ℂ) * (U : Matrix (Fin 2) (Fin 2) ℂ)) 0 0 = 1 := by
    rw [hu, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.star_apply] at h0
  have h1 : ((nrmA U + nrmB U : ℝ) : ℂ) = 1 := by
    unfold nrmA nrmB entA entB
    rw [Complex.ofReal_add, Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    exact h0
  exact_mod_cast h1

/-- `|a|² = x² + y²`. DERIVED: no numeral beyond the rank `2`. -/
private lemma nrmA_eq (U : SU 2) : nrmA U = reA U * reA U + imA U * imA U := by
  unfold nrmA reA imA
  exact Complex.normSq_apply _

/-- `(Re ab̄)² + (Im ab̄)² = |a|²|b|²`.

DERIVED: `2` is the square. -/
private lemma crR_sq_add (U : SU 2) : crR U ^ 2 + crI U ^ 2 = nrmA U * nrmB U := by
  have h := Complex.normSq_apply (entA U * (starRingEnd ℂ) (entB U))
  rw [Complex.normSq_mul, Complex.normSq_conj] at h
  unfold crR crI nrmA nrmB
  linear_combination (-1 : ℝ) * h

/-- `(h0 U)₀₀ = i a`. DERIVED: `2` is the rank; `0` indexes the entry. -/
private lemma entA_h0 (U : SU 2) : entA (MassGap.SUN.h0 * U) = Complex.I * entA U := by
  unfold entA
  rw [MassGap.SUN.h0_mul_entry, show MassGap.SUN.h0mat 0 0 = Complex.I from rfl]

/-- `(h0 U)₁₀ = −i b`. DERIVED: `2` is the rank; `1`, `0` index the entry. -/
private lemma entB_h0 (U : SU 2) : entB (MassGap.SUN.h0 * U) = -Complex.I * entB U := by
  unfold entB
  rw [MassGap.SUN.h0_mul_entry, show MassGap.SUN.h0mat 1 1 = -Complex.I from rfl]

/-- `(q8 U)₀₀ = ζ a`. DERIVED: `2` is the rank; `4` as in `q8`. -/
private lemma entA_q8 (U : SU 2) :
    entA (q8 * U) = Complex.exp (Real.pi / 4 * Complex.I) * entA U := by
  unfold entA
  rw [mul_entry, q8_00, q8_01]
  ring

/-- `(q8 U)₁₀ = ζ̄ b`. DERIVED: `2` is the rank; `4` as in `q8`. -/
private lemma entB_q8 (U : SU 2) :
    entB (q8 * U) = Complex.exp (-(Real.pi / 4 * Complex.I)) * entB U := by
  unfold entB
  rw [mul_entry, q8_10, q8_11]
  ring

/-- `(rot45 U)₀₀ = (a + b)/√2`. DERIVED: `2` is the radicand. -/
private lemma entA_rot (U : SU 2) :
    entA (rot45 * U) = ((Real.sqrt 2)⁻¹ : ℂ) * (entA U + entB U) := by
  unfold entA entB
  rw [mul_entry, rot45_00, rot45_01]
  ring

/-- `h0` sends `Re ab̄ ↦ −Re ab̄` (`ab̄ ↦ i · i · ab̄`). DERIVED: `2` is the rank. -/
private lemma crR_h0 (U : SU 2) : crR (MassGap.SUN.h0 * U) = -crR U := by
  unfold crR
  rw [entA_h0, entB_h0, map_mul, map_neg, Complex.conj_I, neg_neg]
  have h : Complex.I * entA U * (Complex.I * (starRingEnd ℂ) (entB U))
      = -(entA U * (starRingEnd ℂ) (entB U)) := by
    linear_combination (entA U * (starRingEnd ℂ) (entB U)) * Complex.I_sq
  rw [h, Complex.neg_re]

/-- `q8` sends `Re ab̄ ↦ −Im ab̄` (`ab̄ ↦ ζ² ab̄ = i ab̄`). DERIVED: `2` is the rank. -/
private lemma crR_q8 (U : SU 2) : crR (q8 * U) = -crI U := by
  unfold crR crI
  rw [entA_q8, entB_q8, map_mul, conj_zeta']
  have h : Complex.exp (Real.pi / 4 * Complex.I) * entA U
        * (Complex.exp (Real.pi / 4 * Complex.I) * (starRingEnd ℂ) (entB U))
      = Complex.I * (entA U * (starRingEnd ℂ) (entB U)) := by
    linear_combination (entA U * (starRingEnd ℂ) (entB U)) * zeta_sq
  rw [h, Complex.mul_re, Complex.I_re, Complex.I_im]
  ring

/-- `rot45` sends `|a|² ↦ |a + b|²/2 = 1/2 + Re ab̄`.

DERIVED: `1/2 = |1/√2|²`, with `|a|² + |b|² = 1`. -/
private lemma nrmA_rot (U : SU 2) : nrmA (rot45 * U) = 1 / 2 + crR U := by
  have h1 := nrmA_add_nrmB U
  unfold nrmA nrmB at h1
  unfold nrmA crR
  rw [entA_rot, Complex.normSq_mul, Complex.normSq_add, normSq_sqrt2_inv]
  linarith

/-- `h0` sends `x ↦ −y`. DERIVED: `2` is the rank. -/
private lemma reA_h0 (U : SU 2) : reA (MassGap.SUN.h0 * U) = -imA U := by
  unfold reA imA
  rw [entA_h0, Complex.mul_re, Complex.I_re, Complex.I_im]
  ring

/-- `h0` sends `y ↦ x`. DERIVED: `2` is the rank. -/
private lemma imA_h0 (U : SU 2) : imA (MassGap.SUN.h0 * U) = reA U := by
  unfold reA imA
  rw [entA_h0, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- `q8` sends `x ↦ (x − y)/√2`.

DERIVED: `√2/2 = Re ζ = Im ζ`. -/
private lemma reA_q8 (U : SU 2) : reA (q8 * U) = Real.sqrt 2 / 2 * (reA U - imA U) := by
  unfold reA imA
  rw [entA_q8, Complex.mul_re, zeta_re, zeta_im]
  ring

/-! ### The moments of `a` -/

/-- `E a² = 0` (`h0` on the left: `a² ↦ −a²`).

DERIVED: `2` is the rank and the power; `0` is the index of `a = U₀₀` and the value. -/
theorem haar_su2_sq_zero :
    ∫ U : SU 2, ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ 2 ∂(probHaar (SU 2)) = 0 := by
  have hpt : ∀ U : SU 2, (((MassGap.SUN.h0 * U : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ 2
      = (-1 : ℂ) * ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ 2 := by
    intro U
    rw [MassGap.SUN.h0_mul_entry, show MassGap.SUN.h0mat 0 0 = Complex.I from rfl]
    linear_combination ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ 2 * Complex.I_sq
  exact int_zero_of_phase (fun U : SU 2 => ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ 2)
    MassGap.SUN.h0 (-1) (by norm_num) hpt

#print axioms haar_su2_sq_zero

/-- `E a⁴ = 0` (`q8` on the left: `a⁴ ↦ ζ⁴ a⁴ = −a⁴`).

DERIVED: `2` is the rank; `4` is the power; `0` is the index and the value. -/
theorem haar_su2_pow_four_zero :
    ∫ U : SU 2, ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ 4 ∂(probHaar (SU 2)) = 0 := by
  have hpt : ∀ U : SU 2, (((q8 * U : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ 4
      = (-1 : ℂ) * ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ 4 := by
    intro U
    rw [mul_entry, q8_00, q8_01]
    linear_combination ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ 4
        * (Complex.exp (Real.pi / 4 * Complex.I) ^ 2 + Complex.I) * zeta_sq
      + ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ 4 * Complex.I_sq
  exact int_zero_of_phase (fun U : SU 2 => ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ 4)
    q8 (-1) (by norm_num) hpt

#print axioms haar_su2_pow_four_zero

/-- `E a³ā = 0` (`h0` on the left: phase `i³ · (−i) = −1`).

DERIVED: `2` is the rank; `3` is the power of `a`; `0` is the index and the value. -/
theorem haar_su2_cube_conj_zero :
    ∫ U : SU 2, ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ 3 * star ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0)
      ∂(probHaar (SU 2)) = 0 := by
  have hpt : ∀ U : SU 2, (((MassGap.SUN.h0 * U : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ 3
        * star (((MassGap.SUN.h0 * U : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0)
      = (-1 : ℂ) * (((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ 3
        * star ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0)) := by
    intro U
    rw [MassGap.SUN.h0_mul_entry, show MassGap.SUN.h0mat 0 0 = Complex.I from rfl, star_mul',
      show star Complex.I = -Complex.I from Complex.conj_I]
    linear_combination (-(((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ 3
        * star ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0)) * (Complex.I ^ 2 - 1)) * Complex.I_sq
  exact int_zero_of_phase (fun U : SU 2 => ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ 3
      * star ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0))
    MassGap.SUN.h0 (-1) (by norm_num) hpt

#print axioms haar_su2_cube_conj_zero

/-- **`E|a|⁴ = 1/3`** (step 2 of the module docstring).

DERIVED: `2` is the rank and the square; `0` is the index; `1/3` solves `p + s = 1/2`,
`p = 1/4 + s/2`. -/
theorem haar_su2_normSq_sq :
    ∫ U : SU 2, Complex.normSq ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ 2 ∂(probHaar (SU 2)) = 1 / 3 := by
  show ∫ U : SU 2, nrmA U ^ 2 ∂(probHaar (SU 2)) = 1 / 3
  -- `p + s = 1/2`
  have hpt2 : ∀ U : SU 2, nrmA U ^ 2 + nrmA U * nrmB U = nrmA U := fun U => by
    have h := nrmA_add_nrmB U
    linear_combination nrmA U * h
  have hE2 : ∫ U : SU 2, nrmA U ^ 2 ∂(probHaar (SU 2))
      + ∫ U : SU 2, nrmA U * nrmB U ∂(probHaar (SU 2)) = 1 / 2 := by
    calc ∫ U : SU 2, nrmA U ^ 2 ∂(probHaar (SU 2))
          + ∫ U : SU 2, nrmA U * nrmB U ∂(probHaar (SU 2))
        = ∫ U : SU 2, (nrmA U ^ 2 + nrmA U * nrmB U) ∂(probHaar (SU 2)) :=
          (integral_add (intg (cont_nrmA.pow 2)) (intg (cont_nrmA.mul cont_nrmB))).symm
      _ = ∫ U : SU 2, nrmA U ∂(probHaar (SU 2)) :=
          integral_congr_ae (Filter.Eventually.of_forall hpt2)
      _ = 1 / 2 := int_nrmA
  -- `E Re ab̄ = 0`
  have hE3 : ∫ U : SU 2, crR U ∂(probHaar (SU 2)) = 0 :=
    int_zero_of_odd crR MassGap.SUN.h0 crR_h0
  -- `E (Re ab̄)² = E (Im ab̄)²`
  have hpt4 : ∀ U : SU 2, crR (q8 * U) ^ 2 = crI U ^ 2 := fun U => by
    rw [crR_q8, neg_sq]
  have hE4 : ∫ U : SU 2, crR U ^ 2 ∂(probHaar (SU 2)) = ∫ U : SU 2, crI U ^ 2 ∂(probHaar (SU 2)) := by
    calc ∫ U : SU 2, crR U ^ 2 ∂(probHaar (SU 2))
        = ∫ U : SU 2, crR (q8 * U) ^ 2 ∂(probHaar (SU 2)) :=
          (int_left (fun U : SU 2 => crR U ^ 2) q8).symm
      _ = ∫ U : SU 2, crI U ^ 2 ∂(probHaar (SU 2)) :=
          integral_congr_ae (Filter.Eventually.of_forall hpt4)
  -- `E (Re ab̄)² + E (Im ab̄)² = s`
  have hE5 : ∫ U : SU 2, crR U ^ 2 ∂(probHaar (SU 2)) + ∫ U : SU 2, crI U ^ 2 ∂(probHaar (SU 2))
      = ∫ U : SU 2, nrmA U * nrmB U ∂(probHaar (SU 2)) := by
    calc ∫ U : SU 2, crR U ^ 2 ∂(probHaar (SU 2)) + ∫ U : SU 2, crI U ^ 2 ∂(probHaar (SU 2))
        = ∫ U : SU 2, (crR U ^ 2 + crI U ^ 2) ∂(probHaar (SU 2)) :=
          (integral_add (intg (cont_crR.pow 2)) (intg (cont_crI.pow 2))).symm
      _ = ∫ U : SU 2, nrmA U * nrmB U ∂(probHaar (SU 2)) :=
          integral_congr_ae (Filter.Eventually.of_forall crR_sq_add)
  -- `p = 1/4 + E Re ab̄ + E (Re ab̄)²`
  have hc14 : Continuous (fun _ : SU 2 => (1 / 4 : ℝ)) := continuous_const
  have hpt6 : ∀ U : SU 2, nrmA (rot45 * U) ^ 2 = (1 / 4 + crR U) + crR U ^ 2 := fun U => by
    rw [nrmA_rot]
    ring
  have hE6 : ∫ U : SU 2, nrmA U ^ 2 ∂(probHaar (SU 2))
      = 1 / 4 + ∫ U : SU 2, crR U ∂(probHaar (SU 2)) + ∫ U : SU 2, crR U ^ 2 ∂(probHaar (SU 2)) := by
    calc ∫ U : SU 2, nrmA U ^ 2 ∂(probHaar (SU 2))
        = ∫ U : SU 2, nrmA (rot45 * U) ^ 2 ∂(probHaar (SU 2)) :=
          (int_left (fun U : SU 2 => nrmA U ^ 2) rot45).symm
      _ = ∫ U : SU 2, ((1 / 4 + crR U) + crR U ^ 2) ∂(probHaar (SU 2)) :=
          integral_congr_ae (Filter.Eventually.of_forall hpt6)
      _ = ∫ U : SU 2, (1 / 4 + crR U) ∂(probHaar (SU 2))
            + ∫ U : SU 2, crR U ^ 2 ∂(probHaar (SU 2)) :=
          integral_add (intg (hc14.add cont_crR)) (intg (cont_crR.pow 2))
      _ = (∫ _U : SU 2, (1 / 4 : ℝ) ∂(probHaar (SU 2)) + ∫ U : SU 2, crR U ∂(probHaar (SU 2)))
            + ∫ U : SU 2, crR U ^ 2 ∂(probHaar (SU 2)) := by
          rw [integral_add (intg hc14) (intg cont_crR)]
      _ = 1 / 4 + ∫ U : SU 2, crR U ∂(probHaar (SU 2)) + ∫ U : SU 2, crR U ^ 2 ∂(probHaar (SU 2)) := by
          rw [int_const]
  linarith

#print axioms haar_su2_normSq_sq

/-- **`E(Re a)² = 1/4`**: `h0` sends `Re a ↦ −Im a`, so `E(Re a)² = E(Im a)²`, and their sum is
`E|a|² = 1/2`.

DERIVED: `2` is the rank and the square; `0` is the index; `1/4 = (1/2)/2`, `1/2` being
`MassGap.SUN.f00_mean`. -/
theorem haar_su2_re_sq :
    ∫ U : SU 2, ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 2 ∂(probHaar (SU 2)) = 1 / 4 := by
  show ∫ U : SU 2, reA U ^ 2 ∂(probHaar (SU 2)) = 1 / 4
  have hpt : ∀ U : SU 2, reA (MassGap.SUN.h0 * U) ^ 2 = imA U ^ 2 := fun U => by
    rw [reA_h0, neg_sq]
  have h1 : ∫ U : SU 2, reA U ^ 2 ∂(probHaar (SU 2)) = ∫ U : SU 2, imA U ^ 2 ∂(probHaar (SU 2)) := by
    calc ∫ U : SU 2, reA U ^ 2 ∂(probHaar (SU 2))
        = ∫ U : SU 2, reA (MassGap.SUN.h0 * U) ^ 2 ∂(probHaar (SU 2)) :=
          (int_left (fun U : SU 2 => reA U ^ 2) MassGap.SUN.h0).symm
      _ = ∫ U : SU 2, imA U ^ 2 ∂(probHaar (SU 2)) :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hpt' : ∀ U : SU 2, reA U ^ 2 + imA U ^ 2 = nrmA U := fun U => by
    rw [nrmA_eq]
    ring
  have h2 : ∫ U : SU 2, reA U ^ 2 ∂(probHaar (SU 2)) + ∫ U : SU 2, imA U ^ 2 ∂(probHaar (SU 2))
      = 1 / 2 := by
    calc ∫ U : SU 2, reA U ^ 2 ∂(probHaar (SU 2)) + ∫ U : SU 2, imA U ^ 2 ∂(probHaar (SU 2))
        = ∫ U : SU 2, (reA U ^ 2 + imA U ^ 2) ∂(probHaar (SU 2)) :=
          (integral_add (intg (cont_reA.pow 2)) (intg (cont_imA.pow 2))).symm
      _ = ∫ U : SU 2, nrmA U ∂(probHaar (SU 2)) :=
          integral_congr_ae (Filter.Eventually.of_forall hpt')
      _ = 1 / 2 := int_nrmA
  linarith

#print axioms haar_su2_re_sq

/-- **`E(Re a)⁴ = 1/8`**: with `x = Re a`, `y = Im a`, `q8` gives
`E x⁴ = E(x − y)⁴/4 = (3/4) E|a|⁴ − E x⁴/2 − E y⁴/2 − E(x³y + xy³)`; `h0` gives `E y⁴ = E x⁴` and
kills `E(x³y + xy³)`; so `2 E x⁴ = (3/4)(1/3)`.

DERIVED: `2` is the rank; `4` is the power; `0` is the index; `1/8 = (3/4)(1/3)/2`, `1/3` from
`haar_su2_normSq_sq`, `3/4` and `1/2` the coefficients of `(x − y)⁴/4` in `(x² + y²)²`, `x⁴`, `y⁴`. -/
theorem haar_su2_re_four :
    ∫ U : SU 2, ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 4 ∂(probHaar (SU 2)) = 1 / 8 := by
  show ∫ U : SU 2, reA U ^ 4 ∂(probHaar (SU 2)) = 1 / 8
  have hQ : ∫ U : SU 2, nrmA U ^ 2 ∂(probHaar (SU 2)) = 1 / 3 := haar_su2_normSq_sq
  -- `E y⁴ = E x⁴`
  have hpt1 : ∀ U : SU 2, reA (MassGap.SUN.h0 * U) ^ 4 = imA U ^ 4 := fun U => by
    rw [reA_h0]
    ring
  have hY : ∫ U : SU 2, reA U ^ 4 ∂(probHaar (SU 2)) = ∫ U : SU 2, imA U ^ 4 ∂(probHaar (SU 2)) := by
    calc ∫ U : SU 2, reA U ^ 4 ∂(probHaar (SU 2))
        = ∫ U : SU 2, reA (MassGap.SUN.h0 * U) ^ 4 ∂(probHaar (SU 2)) :=
          (int_left (fun U : SU 2 => reA U ^ 4) MassGap.SUN.h0).symm
      _ = ∫ U : SU 2, imA U ^ 4 ∂(probHaar (SU 2)) :=
          integral_congr_ae (Filter.Eventually.of_forall hpt1)
  -- `E(x³y + xy³) = 0`
  have hptO : ∀ U : SU 2,
      reA (MassGap.SUN.h0 * U) ^ 3 * imA (MassGap.SUN.h0 * U)
        + reA (MassGap.SUN.h0 * U) * imA (MassGap.SUN.h0 * U) ^ 3
      = -(reA U ^ 3 * imA U + reA U * imA U ^ 3) := fun U => by
    rw [reA_h0, imA_h0]
    ring
  have hO : ∫ U : SU 2, (reA U ^ 3 * imA U + reA U * imA U ^ 3) ∂(probHaar (SU 2)) = 0 :=
    int_zero_of_odd (fun U : SU 2 => reA U ^ 3 * imA U + reA U * imA U ^ 3) MassGap.SUN.h0 hptO
  -- the `q8` identity
  have hpt2 : ∀ U : SU 2, reA (q8 * U) ^ 4
      = 3 / 4 * nrmA U ^ 2 - 1 / 2 * reA U ^ 4 - 1 / 2 * imA U ^ 4
        - (reA U ^ 3 * imA U + reA U * imA U ^ 3) := fun U => by
    rw [reA_q8, nrmA_eq]
    linear_combination ((Real.sqrt 2 ^ 2 + 2) / 16 * (reA U - imA U) ^ 4) * sqrt2_sq
  have hX : ∫ U : SU 2, reA U ^ 4 ∂(probHaar (SU 2))
      = 3 / 4 * ∫ U : SU 2, nrmA U ^ 2 ∂(probHaar (SU 2))
        - 1 / 2 * ∫ U : SU 2, reA U ^ 4 ∂(probHaar (SU 2))
        - 1 / 2 * ∫ U : SU 2, imA U ^ 4 ∂(probHaar (SU 2))
        - ∫ U : SU 2, (reA U ^ 3 * imA U + reA U * imA U ^ 3) ∂(probHaar (SU 2)) := by
    calc ∫ U : SU 2, reA U ^ 4 ∂(probHaar (SU 2))
        = ∫ U : SU 2, reA (q8 * U) ^ 4 ∂(probHaar (SU 2)) :=
          (int_left (fun U : SU 2 => reA U ^ 4) q8).symm
      _ = ∫ U : SU 2, (3 / 4 * nrmA U ^ 2 - 1 / 2 * reA U ^ 4 - 1 / 2 * imA U ^ 4
            - (reA U ^ 3 * imA U + reA U * imA U ^ 3)) ∂(probHaar (SU 2)) :=
          integral_congr_ae (Filter.Eventually.of_forall hpt2)
      _ = 3 / 4 * ∫ U : SU 2, nrmA U ^ 2 ∂(probHaar (SU 2))
            - 1 / 2 * ∫ U : SU 2, reA U ^ 4 ∂(probHaar (SU 2))
            - 1 / 2 * ∫ U : SU 2, imA U ^ 4 ∂(probHaar (SU 2))
            - ∫ U : SU 2, (reA U ^ 3 * imA U + reA U * imA U ^ 3) ∂(probHaar (SU 2)) :=
          int_comb (fun U : SU 2 => nrmA U ^ 2) (fun U : SU 2 => reA U ^ 4)
            (fun U : SU 2 => imA U ^ 4) (fun U : SU 2 => reA U ^ 3 * imA U + reA U * imA U ^ 3)
            (cont_nrmA.pow 2) (cont_reA.pow 4) (cont_imA.pow 4)
            (((cont_reA.pow 3).mul cont_imA).add (cont_reA.mul (cont_imA.pow 3)))
            (3 / 4) (1 / 2) (1 / 2)
  linarith

#print axioms haar_su2_re_four

/-! ### The feature -/

/-- **Parity**: `X(−U) = −X(U)`.

DERIVED: `2` is the rank. -/
theorem realFeature_negOne (U : SU 2) : realFeature 2 (negOne2 * U) = -realFeature 2 U := by
  have hent : ∀ i j : Fin 2, ((negOne2 * U : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) i j
      = -(U : Matrix (Fin 2) (Fin 2) ℂ) i j := by
    intro i j
    rw [Submonoid.coe_mul, negOne_coe, neg_one_mul, Matrix.neg_apply]
  ext k
  simp only [realFeature, PiLp.neg_apply, PiLp.toLp_apply]
  rw [hent]
  split_ifs
  · rw [Complex.neg_re]
    ring
  · rw [Complex.neg_im]
    ring

#print axioms realFeature_negOne

/-- `|x + y|² ≤ 2|x|² + 2|y|²`.

DERIVED: `2` is the parallelogram constant. -/
private lemma normSq_add_le2 (x y : ℂ) :
    Complex.normSq (x + y) ≤ 2 * Complex.normSq x + 2 * Complex.normSq y := by
  rw [Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply, Complex.add_re,
    Complex.add_im]
  nlinarith [sq_nonneg (x.re - y.re), sq_nonneg (x.im - y.im)]

/-- `|x − y|² ≤ 2|x|² + 2|y|²`.

DERIVED: `2` is the parallelogram constant. -/
private lemma normSq_sub_le2 (x y : ℂ) :
    Complex.normSq (x - y) ≤ 2 * Complex.normSq x + 2 * Complex.normSq y := by
  rw [Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im]
  nlinarith [sq_nonneg (x.re + y.re), sq_nonneg (x.im + y.im)]

/-- DERIVED: `2` is the rank `N` of `inner_realFeature`, cast to `ℝ`. -/
private lemma sqrt_two_cast : Real.sqrt ((2 : ℕ) : ℝ) = Real.sqrt 2 := by norm_num

/-- **Transitivity of `SU(2)` on the unit sphere of `ℂ²`**: every functional of the feature is a
multiple of `Re a` after a left translation, with multiplier `ρ/√2`, `ρ² ≤ 2‖w‖²`.

DERIVED: `2` is the rank, the `√2` of `X = realify/√2`, and the bound `|c|² ≤ 2‖w‖²` (`c₁`, `c₂`
each collect two entries of `w`); `0` is the index of `a` and the sign of `ρ`. -/
theorem exists_rot_su2 (w : FE 2) :
    ∃ (ρ : ℝ) (A : SU 2), 0 ≤ ρ ∧ ρ ^ 2 ≤ 2 * ‖w‖ ^ 2 ∧ ∀ U : SU 2,
      inner ℝ w (realFeature 2 U)
        = ρ / Real.sqrt 2 * (((A * U : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re := by
  obtain ⟨c₁, hc₁⟩ : ∃ c : ℂ, c = featDual 2 w 0 0 + (starRingEnd ℂ) (featDual 2 w 1 1) :=
    ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c : ℂ, c = featDual 2 w 0 1 - (starRingEnd ℂ) (featDual 2 w 1 0) :=
    ⟨_, rfl⟩
  -- `⟪w, X U⟫ = Re(c₁ a + c₂ b)/√2`
  have hform : ∀ U : SU 2, inner ℝ w (realFeature 2 U)
      = (c₁ * (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + c₂ * (U : Matrix (Fin 2) (Fin 2) ℂ) 1 0).re
        / Real.sqrt 2 := by
    intro U
    rw [inner_realFeature, sqrt_two_cast]
    congr 1
    have h11 : (U : Matrix (Fin 2) (Fin 2) ℂ) 1 1
        = (starRingEnd ℂ) ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) := (MassGap.SUN.su2_conj_00 U).symm
    have h01 : (U : Matrix (Fin 2) (Fin 2) ℂ) 0 1
        = -(starRingEnd ℂ) ((U : Matrix (Fin 2) (Fin 2) ℂ) 1 0) := by
      rw [MassGap.SUN.su2_conj_10, neg_neg]
    rw [Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_two, h11, h01, hc₁, hc₂]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.add_im, Complex.sub_im, Complex.mul_im]
    ring
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = Complex.normSq c₁ + Complex.normSq c₂ := ⟨_, rfl⟩
  have hn0 : 0 ≤ n := by
    rw [hn]
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  -- `|c|² ≤ 2‖w‖²`
  have hbound : n ≤ 2 * ‖w‖ ^ 2 := by
    have hf := frob_featDual 2 w
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two] at hf
    have h1 : Complex.normSq c₁
        ≤ 2 * Complex.normSq (featDual 2 w 0 0) + 2 * Complex.normSq (featDual 2 w 1 1) := by
      rw [hc₁]
      have h := normSq_add_le2 (featDual 2 w 0 0) ((starRingEnd ℂ) (featDual 2 w 1 1))
      rwa [Complex.normSq_conj] at h
    have h2 : Complex.normSq c₂
        ≤ 2 * Complex.normSq (featDual 2 w 0 1) + 2 * Complex.normSq (featDual 2 w 1 0) := by
      rw [hc₂]
      have h := normSq_sub_le2 (featDual 2 w 0 1) ((starRingEnd ℂ) (featDual 2 w 1 0))
      rwa [Complex.normSq_conj] at h
    rw [hn]
    linarith
  rcases hn0.lt_or_eq with hpos | hzero
  · -- `c ≠ 0`: rotate `c/|c|` onto the first basis vector
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (Real.sqrt n)⁻¹ := ⟨_, rfl⟩
    have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hpos
    have htn : t * t * n = 1 := by
      rw [ht, ← mul_inv, Real.mul_self_sqrt hn0, inv_mul_cancel₀ hpos.ne']
    have htn' : t * t * (Complex.normSq c₁ + Complex.normSq c₂) = 1 := by
      rw [← hn]
      exact htn
    have hcancel : Real.sqrt n * t = 1 := by
      rw [ht]
      exact mul_inv_cancel₀ hspos.ne'
    have key : (t : ℂ) * c₁ * (starRingEnd ℂ) ((t : ℂ) * c₁)
        + (t : ℂ) * c₂ * (starRingEnd ℂ) ((t : ℂ) * c₂) = 1 := by
      rw [map_mul, map_mul, Complex.conj_ofReal]
      have e1 := Complex.mul_conj c₁
      have e2 := Complex.mul_conj c₂
      have e3 : ((t : ℂ) * (t : ℂ)) * (((Complex.normSq c₁ : ℝ) : ℂ) + ((Complex.normSq c₂ : ℝ) : ℂ))
          = 1 := by
        exact_mod_cast htn'
      linear_combination ((t : ℂ) * (t : ℂ)) * e1 + ((t : ℂ) * (t : ℂ)) * e2 + e3
    obtain ⟨A, hA0, hA1⟩ : ∃ A : SU 2, (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = (t : ℂ) * c₁
        ∧ (A : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = (t : ℂ) * c₂ :=
      ⟨⟨!![(t : ℂ) * c₁, (t : ℂ) * c₂; -(starRingEnd ℂ) ((t : ℂ) * c₂),
          (starRingEnd ℂ) ((t : ℂ) * c₁)], mem_su2_unit _ _ key⟩, rfl, rfl⟩
    refine ⟨Real.sqrt n, A, hspos.le, ?_, fun U => ?_⟩
    · rw [Real.sq_sqrt hn0]
      exact hbound
    · rw [hform U, mul_entry, hA0, hA1,
        show ∀ x y : ℂ, (t : ℂ) * c₁ * x + (t : ℂ) * c₂ * y = (t : ℂ) * (c₁ * x + c₂ * y) from
          fun x y => by ring,
        Complex.re_ofReal_mul,
        show ∀ x : ℝ, Real.sqrt n / Real.sqrt 2 * (t * x) = (Real.sqrt n * t) * (x / Real.sqrt 2) from
          fun x => by ring,
        hcancel, one_mul]
  · -- `c = 0`: the functional vanishes
    have hn1 : Complex.normSq c₁ = 0 :=
      le_antisymm (by linarith [Complex.normSq_nonneg c₂]) (Complex.normSq_nonneg c₁)
    have hn2 : Complex.normSq c₂ = 0 :=
      le_antisymm (by linarith [Complex.normSq_nonneg c₁]) (Complex.normSq_nonneg c₂)
    have hz1 : c₁ = 0 := Complex.normSq_eq_zero.mp hn1
    have hz2 : c₂ = 0 := Complex.normSq_eq_zero.mp hn2
    refine ⟨0, 1, le_rfl, by nlinarith [sq_nonneg ‖w‖], fun U => ?_⟩
    rw [hform U, hz1, hz2]
    simp

#print axioms exists_rot_su2

/-- The feature has mean `0` (parity).

DERIVED: `2` is the rank; `0` is the mean. -/
theorem feature_mean_su2 (w : FE 2) :
    ∫ U : SU 2, inner ℝ w (realFeature 2 U) ∂(probHaar (SU 2)) = 0 := by
  have hpt : ∀ U : SU 2, inner ℝ w (realFeature 2 (negOne2 * U)) = -inner ℝ w (realFeature 2 U) :=
    fun U => by rw [realFeature_negOne, inner_neg_right]
  exact int_zero_of_odd (fun U : SU 2 => inner ℝ w (realFeature 2 U)) negOne2 hpt

#print axioms feature_mean_su2

/-- **Second moments**: `E⟪w, X⟫² ≤ ‖w‖²/4` (`exists_rot_su2`, `haar_su2_re_sq`).

DERIVED: `2` is the rank and the moment order; `4 = 2 · 2`, `(ρ²/2)(1/4) ≤ (2‖w‖²/2)(1/4)`. -/
theorem feature_second_su2 (w : FE 2) :
    ∫ U : SU 2, inner ℝ w (realFeature 2 U) ^ 2 ∂(probHaar (SU 2)) ≤ ‖w‖ ^ 2 / 4 := by
  obtain ⟨ρ, A, _hρ0, hρ2, hrep⟩ := exists_rot_su2 w
  have hpt : ∀ U : SU 2, inner ℝ w (realFeature 2 U) ^ 2
      = ρ ^ 2 / 2 * (((A * U : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 2 := by
    intro U
    rw [hrep U, mul_pow, div_pow, sqrt2_sq]
  have hval : ∫ U : SU 2, inner ℝ w (realFeature 2 U) ^ 2 ∂(probHaar (SU 2))
      = ρ ^ 2 / 2 * (1 / 4) := by
    calc ∫ U : SU 2, inner ℝ w (realFeature 2 U) ^ 2 ∂(probHaar (SU 2))
        = ∫ U : SU 2, ρ ^ 2 / 2 * (((A * U : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 2
            ∂(probHaar (SU 2)) := integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = ρ ^ 2 / 2 * ∫ U : SU 2, (((A * U : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 2
            ∂(probHaar (SU 2)) := integral_const_mul _ _
      _ = ρ ^ 2 / 2 * ∫ U : SU 2, ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 2
            ∂(probHaar (SU 2)) := by rw [int_left_re2 A]
      _ = ρ ^ 2 / 2 * (1 / 4) := by rw [haar_su2_re_sq]
  rw [hval]
  linarith

#print axioms feature_second_su2

/-- **Fourth moments**: `E⟪w, X⟫⁴ ≤ ‖w‖⁴/8` (`exists_rot_su2`, `haar_su2_re_four`).

DERIVED: `2` is the rank; `4` is the moment order; `1/8 = ((2‖w‖²)²/4)(1/8)/‖w‖⁴`. -/
theorem feature_fourth_su2 (w : FE 2) :
    ∫ U : SU 2, inner ℝ w (realFeature 2 U) ^ 4 ∂(probHaar (SU 2)) ≤ 1 / 8 * ‖w‖ ^ 4 := by
  obtain ⟨ρ, A, _hρ0, hρ2, hrep⟩ := exists_rot_su2 w
  have hpt : ∀ U : SU 2, inner ℝ w (realFeature 2 U) ^ 4
      = ρ ^ 4 / 4 * (((A * U : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 4 := by
    intro U
    rw [hrep U, mul_pow, div_pow, sqrt2_pow4]
  have hval : ∫ U : SU 2, inner ℝ w (realFeature 2 U) ^ 4 ∂(probHaar (SU 2))
      = ρ ^ 4 / 4 * (1 / 8) := by
    calc ∫ U : SU 2, inner ℝ w (realFeature 2 U) ^ 4 ∂(probHaar (SU 2))
        = ∫ U : SU 2, ρ ^ 4 / 4 * (((A * U : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 4
            ∂(probHaar (SU 2)) := integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = ρ ^ 4 / 4 * ∫ U : SU 2, (((A * U : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 4
            ∂(probHaar (SU 2)) := integral_const_mul _ _
      _ = ρ ^ 4 / 4 * ∫ U : SU 2, ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 4
            ∂(probHaar (SU 2)) := by rw [int_left_re4 A]
      _ = ρ ^ 4 / 4 * (1 / 8) := by rw [haar_su2_re_four]
  have h4 : ρ ^ 4 ≤ 4 * ‖w‖ ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hρ2) (sub_nonneg.mpr hρ2),
      mul_nonneg (sq_nonneg ρ) (sub_nonneg.mpr hρ2)]
  rw [hval]
  linarith

#print axioms feature_fourth_su2

/-- **Mixed third moments vanish** (parity), stated in the `HaarConsts.third` shape with `t3 = 0`.

DERIVED: `2` is the rank and the square; `0` is `t3`. -/
theorem feature_third_su2 (u w : FE 2) :
    |∫ U : SU 2, inner ℝ u (realFeature 2 U) ^ 2 * inner ℝ w (realFeature 2 U) ∂(probHaar (SU 2))|
      ≤ 0 * ‖u‖ ^ 2 * ‖w‖ := by
  have hpt : ∀ U : SU 2,
      inner ℝ u (realFeature 2 (negOne2 * U)) ^ 2 * inner ℝ w (realFeature 2 (negOne2 * U))
        = -(inner ℝ u (realFeature 2 U) ^ 2 * inner ℝ w (realFeature 2 U)) := fun U => by
    rw [realFeature_negOne, inner_neg_right, inner_neg_right]
    ring
  have hzero : ∫ U : SU 2, inner ℝ u (realFeature 2 U) ^ 2 * inner ℝ w (realFeature 2 U)
      ∂(probHaar (SU 2)) = 0 :=
    int_zero_of_odd
      (fun U : SU 2 => inner ℝ u (realFeature 2 U) ^ 2 * inner ℝ w (realFeature 2 U)) negOne2 hpt
  rw [hzero]
  simp

#print axioms feature_third_su2

/-- **The Haar constants of the `SU(2)` feature**: `D = 4`, `q4 = 1/8`, `t3 = 0`.

DERIVED: `4` is `feature_second_su2`'s constant; `1/8` is `feature_fourth_su2`'s; `0` is the parity
value of `t3`; `2` is the rank. -/
def haarConsts_su2 : HaarConsts (probHaar (SU 2)) (realFeature 2) where
  D := 4
  q4 := 1 / 8
  t3 := 0
  D_pos := by norm_num
  q4_nonneg := by norm_num
  t3_nonneg := le_rfl
  mean := feature_mean_su2
  second := feature_second_su2
  fourth := feature_fourth_su2
  third := feature_third_su2

#print axioms haarConsts_su2

end MassGap.HaarMomentsSU2
