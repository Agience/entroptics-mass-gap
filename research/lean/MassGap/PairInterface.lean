import Mathlib
import MassGap.SUN

noncomputable section

/-!
# MassGap.PairInterface — the shared definitions of the sharp two-link route

The `def`s and the structure below are the interfaces that `HaarMomentsSU2`, `HaarMomentsSU3`,
`TiltedHaar`, `PairFibreAbstract`, `PairCount`, `PairWeight` and `PairCorrSharp` are written
against.

## Contents

1. **The link feature.** `FE N` is the real coordinate space of `N × N` complex matrices and
   `realFeature N U = realify(U)/√N`, so `‖realFeature N U‖ = 1` and
   `⟪realFeature N U, realFeature N V⟫ = Re tr(U V†)/N`. Every linear functional is
   `U ↦ Re tr(U · featDual N w)/√N`. Left and right multiplication and inversion act on the feature
   by linear isometries. One feature map serves every `N`; the group enters only through the Haar
   constants of section 2. The proofs go through the unscaled realification `matFeat` and its
   inverse `featMat`, with `⟪matFeat M, matFeat M'⟫ = Re tr(M M'†)`.
2. **Integration helpers.** A continuous function on a compact space is integrable against a
   finite measure (also vector-valued, and for a measurable continuous function on a space whose
   σ-algebra is not Borel, such as a product). The quadratic-form inequality
   `(∀ t, 2tI ≤ t²A + B) → |I| ≤ √A √B` (Cauchy–Schwarz without `rpow`), and its integrated form.
3. **The interfaces.** `HaarConsts P X`: the untilted moment constants `D`, `q4`, `t3` of a feature
   `X` under a probability measure `P` (`t3 = 0` is the parity case, `SU(2)`). `TiltBounds P X κ M₂ mb`:
   second moments at most `M₂` and mean at most `mb` under every tilt `e^{⟪θ, X⟫}` with `‖θ‖ ≤ κ`.
   `fibreWeight` and `FibreBound`: the pair weight `K e^{⟪X h, T X g⟫ + ⟪α, X h⟫ + ⟪γ, X g⟫}` and the
   covariance bound in exactly the shape `PairCorr.fibre_corr_le` concludes.
4. **The constants.** `cR`, `cR3` (Taylor coefficients of `e^y − 1 − y` and `e^y − 1 − y − y²/2`
   on `|y| ≤ r ≤ 3`), `M2bound`, `mbarBound` (the tilted constants), and `dstar` (the pair bound).
-/

namespace MassGap.PairInterface

open MeasureTheory
open MassGap.SUN (SU)

/-! ## 1. The link feature -/

section Feature

/-- **The real coordinate space of `N × N` complex matrices**: coordinate `(i, j, 0)` carries
`Re Uᵢⱼ`, coordinate `(i, j, 1)` carries `Im Uᵢⱼ`.

DERIVED: `2` is the number of real coordinates of one complex entry. -/
abbrev FE (N : ℕ) : Type := EuclideanSpace ℝ (Fin N × Fin N × Fin 2)

/-- **The link feature** `X U = realify(U)/√N`.

DERIVED: `2` is the `L²` exponent of `EuclideanSpace` and the number of real coordinates of an
entry; `0` selects the real part. -/
def realFeature (N : ℕ) (U : SU N) : FE N :=
  WithLp.toLp 2 (fun k : Fin N × Fin N × Fin 2 =>
    (Real.sqrt (N : ℝ))⁻¹ *
      (if k.2.2 = 0 then ((U : Matrix (Fin N) (Fin N) ℂ) k.1 k.2.1).re
        else ((U : Matrix (Fin N) (Fin N) ℂ) k.1 k.2.1).im))

/-- **The matrix of a linear functional**: `(featDual N w)ⱼᵢ = conj(wᵢⱼ)`, `wᵢⱼ = w(i,j,0) + i w(i,j,1)`.

DERIVED: `0` and `1` select the real and imaginary coordinate; `2` is their number. -/
def featDual (N : ℕ) (w : FE N) : Matrix (Fin N) (Fin N) ℂ :=
  fun j i => ⟨w (i, j, 0), -w (i, j, 1)⟩

/-- The unscaled realification of a complex matrix: `(i, j, 0) ↦ Re Mᵢⱼ`, `(i, j, 1) ↦ Im Mᵢⱼ`.

DERIVED: `2` is the `L²` exponent and the number of real coordinates of an entry; `0` selects the
real part. -/
private def matFeat (N : ℕ) (M : Matrix (Fin N) (Fin N) ℂ) : FE N :=
  WithLp.toLp 2 (fun k : Fin N × Fin N × Fin 2 =>
    if k.2.2 = 0 then (M k.1 k.2.1).re else (M k.1 k.2.1).im)

/-- The inverse of `matFeat`: `Mᵢⱼ = x(i, j, 0) + i x(i, j, 1)`.

DERIVED: `0` and `1` select the real and imaginary coordinate. -/
private def featMat (N : ℕ) (x : FE N) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ⟨x (i, j, 0), x (i, j, 1)⟩

/-- DERIVED: `0` selects the real part; `2` in `Fin 2` is the number of real coordinates of a
complex entry. -/
private theorem matFeat_apply (N : ℕ) (M : Matrix (Fin N) (Fin N) ℂ) (k : Fin N × Fin N × Fin 2) :
    matFeat N M k = if k.2.2 = 0 then (M k.1 k.2.1).re else (M k.1 k.2.1).im := rfl

/-- DERIVED: `0` is the real coordinate. -/
private theorem matFeat_re (N : ℕ) (M : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    matFeat N M (i, j, 0) = (M i j).re := by
  rw [matFeat_apply]
  exact if_pos rfl

/-- DERIVED: `1` is the imaginary coordinate, `0` the real one. -/
private theorem matFeat_im (N : ℕ) (M : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    matFeat N M (i, j, 1) = (M i j).im := by
  rw [matFeat_apply]
  exact if_neg (by decide : ¬ ((1 : Fin 2) = 0))

/-- DERIVED: no numeral. -/
private theorem star_re' (z : ℂ) : (star z).re = z.re := rfl

/-- DERIVED: no numeral. -/
private theorem star_im' (z : ℂ) : (star z).im = -z.im := rfl

/-- DERIVED: no numeral. -/
private theorem featMat_matFeat (N : ℕ) (M : Matrix (Fin N) (Fin N) ℂ) :
    featMat N (matFeat N M) = M := by
  refine Matrix.ext (fun i j => ?_)
  apply Complex.ext
  · exact matFeat_re N M i j
  · exact matFeat_im N M i j

/-- DERIVED: no numeral. -/
private theorem matFeat_featMat (N : ℕ) (x : FE N) : matFeat N (featMat N x) = x := by
  refine PiLp.ext (fun k => ?_)
  obtain ⟨i, j, c⟩ := k
  fin_cases c
  · exact matFeat_re N (featMat N x) i j
  · exact matFeat_im N (featMat N x) i j

/-- `matFeat` as a real-linear map.

DERIVED: no numeral. -/
private def matFeatₗ (N : ℕ) : Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] FE N where
  toFun := matFeat N
  map_add' M M' := by
    refine PiLp.ext (fun k => ?_)
    rw [PiLp.add_apply, matFeat_apply, matFeat_apply, matFeat_apply]
    split_ifs <;> simp [Matrix.add_apply]
  map_smul' r M := by
    refine PiLp.ext (fun k => ?_)
    rw [PiLp.smul_apply, matFeat_apply, matFeat_apply]
    split_ifs <;> simp [Matrix.smul_apply, Complex.smul_re, Complex.smul_im]

/-- `featMat` as a real-linear map.

DERIVED: no numeral. -/
private def featMatₗ (N : ℕ) : FE N →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ where
  toFun := featMat N
  map_add' x y := by
    refine Matrix.ext (fun i j => ?_)
    apply Complex.ext <;> simp [featMat, PiLp.add_apply]
  map_smul' r x := by
    refine Matrix.ext (fun i j => ?_)
    apply Complex.ext <;> simp [featMat, PiLp.smul_apply, Complex.smul_re, Complex.smul_im]

/-- Left multiplication by a fixed matrix, as a real-linear map.

DERIVED: no numeral. -/
private def mulLeftₗ (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ where
  toFun M := A * M
  map_add' M M' := Matrix.mul_add A M M'
  map_smul' r M := Matrix.mul_smul A r M

/-- Right multiplication by a fixed matrix, as a real-linear map.

DERIVED: no numeral. -/
private def mulRightₗ (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ where
  toFun M := M * A
  map_add' M M' := Matrix.add_mul M M' A
  map_smul' r M := Matrix.smul_mul r M A

/-- The conjugate transpose, as a real-linear map.

DERIVED: no numeral. -/
private def starₗ (N : ℕ) : Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ where
  toFun M := star M
  map_add' M M' := star_add M M'
  map_smul' r M := by
    refine Matrix.ext (fun i j => ?_)
    apply Complex.ext <;>
      simp [Matrix.star_apply, Matrix.smul_apply, Complex.smul_re, Complex.smul_im]

/-- The inner product of two realifications, entrywise.

DERIVED: `0` and `1` are the real and imaginary coordinates. -/
private theorem inner_matFeat_sum (N : ℕ) (M M' : Matrix (Fin N) (Fin N) ℂ) :
    inner ℝ (matFeat N M) (matFeat N M')
      = ∑ i, ∑ j, ((M i j).re * (M' i j).re + (M i j).im * (M' i j).im) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fin.sum_univ_two, matFeat_re, matFeat_re, matFeat_im, matFeat_im, Real.inner_apply,
    Real.inner_apply]

/-- The real part of `tr(M M'†)`, entrywise.

DERIVED: no numeral. -/
private theorem trace_re_sum (N : ℕ) (M M' : Matrix (Fin N) (Fin N) ℂ) :
    (Matrix.trace (M * star M')).re
      = ∑ i, ∑ j, ((M i j).re * (M' i j).re + (M i j).im * (M' i j).im) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply, Complex.re_sum,
    Complex.mul_re, star_re', star_im']
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/-- **The realification is Frobenius-isometric**: `⟪matFeat M, matFeat M'⟫ = Re tr(M M'†)`.

DERIVED: no numeral. -/
private theorem inner_matFeat (N : ℕ) (M M' : Matrix (Fin N) (Fin N) ℂ) :
    inner ℝ (matFeat N M) (matFeat N M') = (Matrix.trace (M * star M')).re := by
  rw [inner_matFeat_sum, trace_re_sum]

/-- DERIVED: no numeral. -/
private theorem featDual_eq (N : ℕ) (w : FE N) : featDual N w = star (featMat N w) := by
  refine Matrix.ext (fun j i => ?_)
  rw [Matrix.star_apply]
  apply Complex.ext
  · rfl
  · rfl

/-- DERIVED: no numeral. -/
private theorem realFeature_eq (N : ℕ) (U : SU N) :
    realFeature N U = (Real.sqrt (N : ℝ))⁻¹ • matFeat N (U : Matrix (Fin N) (Fin N) ℂ) := by
  refine PiLp.ext (fun k => ?_)
  rw [PiLp.smul_apply, smul_eq_mul]
  rfl

/-- The coercion of the inverse is the conjugate transpose.

DERIVED: no numeral. -/
private theorem coe_inv_SU {N : ℕ} (V : SU N) :
    ((V⁻¹ : SU N) : Matrix (Fin N) (Fin N) ℂ) = star (V : Matrix (Fin N) (Fin N) ℂ) := rfl

/-- The feature is continuous.

DERIVED: no numeral. -/
theorem continuous_realFeature (N : ℕ) : Continuous (realFeature N) := by
  unfold realFeature
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => ?_)
  have hent : Continuous fun U : SU N => (U : Matrix (Fin N) (Fin N) ℂ) k.1 k.2.1 :=
    continuous_subtype_val.matrix_elem k.1 k.2.1
  exact continuous_const.mul
    (Continuous.if_const _ (Complex.continuous_re.comp hent) (Complex.continuous_im.comp hent))

#print axioms continuous_realFeature

/-- **The inner product of two features**: `⟪X U, X V⟫ = Re tr(U V†)/N`.

DERIVED: no numeral. -/
theorem inner_realFeature_realFeature (N : ℕ) (U V : SU N) :
    inner ℝ (realFeature N U) (realFeature N V)
      = (Matrix.trace ((U : Matrix (Fin N) (Fin N) ℂ) * star (V : Matrix (Fin N) (Fin N) ℂ))).re
        / (N : ℝ) := by
  rw [realFeature_eq, realFeature_eq, real_inner_smul_left, real_inner_smul_right, inner_matFeat]
  have hN : (Real.sqrt (N : ℝ))⁻¹ * (Real.sqrt (N : ℝ))⁻¹ = (N : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg N)]
  rw [← mul_assoc, hN, div_eq_inv_mul]

#print axioms inner_realFeature_realFeature

/-- **The feature has unit norm**: `Σᵢⱼ |Uᵢⱼ|² = N` for unitary `U`.

DERIVED: `0` is the excluded rank; `1` is the norm asserted. -/
theorem norm_realFeature {N : ℕ} (hN : N ≠ 0) (U : SU N) : ‖realFeature N U‖ = 1 := by
  have hU : (U : Matrix (Fin N) (Fin N) ℂ) * star (U : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp U.2).1
  have h1 : ‖realFeature N U‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_realFeature_realFeature, hU, Matrix.trace_one,
      Fintype.card_fin, Complex.natCast_re]
    exact div_self (Nat.cast_ne_zero.mpr hN)
  rw [← Real.sqrt_sq (norm_nonneg (realFeature N U)), h1, Real.sqrt_one]

#print axioms norm_realFeature

/-- **Every functional of the feature is a trace**: `⟪w, X U⟫ = Re tr(U · featDual w)/√N`.

DERIVED: no numeral. -/
theorem inner_realFeature (N : ℕ) (w : FE N) (U : SU N) :
    inner ℝ w (realFeature N U)
      = (Matrix.trace ((U : Matrix (Fin N) (Fin N) ℂ) * featDual N w)).re / Real.sqrt (N : ℝ) := by
  calc inner ℝ w (realFeature N U) = inner ℝ (realFeature N U) w := real_inner_comm _ _
    _ = (Real.sqrt (N : ℝ))⁻¹
          * inner ℝ (matFeat N (U : Matrix (Fin N) (Fin N) ℂ)) (matFeat N (featMat N w)) := by
        rw [realFeature_eq, real_inner_smul_left, matFeat_featMat]
    _ = (Real.sqrt (N : ℝ))⁻¹
          * (Matrix.trace ((U : Matrix (Fin N) (Fin N) ℂ) * star (featMat N w))).re := by
        rw [inner_matFeat]
    _ = (Matrix.trace ((U : Matrix (Fin N) (Fin N) ℂ) * featDual N w)).re
          / Real.sqrt (N : ℝ) := by
        rw [featDual_eq, div_eq_inv_mul]

#print axioms inner_realFeature

/-- **The functional matrix has the norm of the functional**: `‖featDual w‖²_F = ‖w‖²`.

DERIVED: `2` is the square of the norm. -/
theorem frob_featDual (N : ℕ) (w : FE N) :
    ∑ i, ∑ j, Complex.normSq (featDual N w i j) = ‖w‖ ^ 2 := by
  have h2 := inner_matFeat_sum N (featMat N w) (featMat N w)
  rw [matFeat_featMat] at h2
  rw [← real_inner_self_eq_norm_sq, h2]
  calc ∑ i, ∑ j, Complex.normSq (featDual N w i j)
      = ∑ i, ∑ j, (w (j, i, 0) * w (j, i, 0) + w (j, i, 1) * w (j, i, 1)) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        simp only [featDual, Complex.normSq_mk]
        ring
    _ = ∑ j, ∑ i, (w (j, i, 0) * w (j, i, 0) + w (j, i, 1) * w (j, i, 1)) := Finset.sum_comm
    _ = ∑ i, ∑ j, ((featMat N w i j).re * (featMat N w i j).re
          + (featMat N w i j).im * (featMat N w i j).im) := rfl

#print axioms frob_featDual

/-- Left multiplication by a unitary preserves the realified inner product.

DERIVED: `1` is the identity matrix. -/
private theorem inner_mulLeft (N : ℕ) {A : Matrix (Fin N) (Fin N) ℂ} (hA : star A * A = 1)
    (x y : FE N) :
    inner ℝ (matFeat N (A * featMat N x)) (matFeat N (A * featMat N y)) = inner ℝ x y := by
  rw [inner_matFeat, star_mul]
  have e : A * featMat N x * (star (featMat N y) * star A)
      = A * (featMat N x * star (featMat N y)) * star A := by
    simp only [mul_assoc]
  rw [e, Matrix.trace_mul_comm, ← mul_assoc, hA, one_mul, ← inner_matFeat, matFeat_featMat,
    matFeat_featMat]

/-- Right multiplication by a unitary preserves the realified inner product.

DERIVED: `1` is the identity matrix. -/
private theorem inner_mulRight (N : ℕ) {A : Matrix (Fin N) (Fin N) ℂ} (hA : A * star A = 1)
    (x y : FE N) :
    inner ℝ (matFeat N (featMat N x * A)) (matFeat N (featMat N y * A)) = inner ℝ x y := by
  rw [inner_matFeat, star_mul]
  have e : featMat N x * A * (star A * star (featMat N y))
      = featMat N x * (A * star A) * star (featMat N y) := by
    simp only [mul_assoc]
  rw [e, hA, mul_one, ← inner_matFeat, matFeat_featMat, matFeat_featMat]

/-- The conjugate transpose preserves the realified inner product.

DERIVED: no numeral. -/
private theorem inner_star (N : ℕ) (x y : FE N) :
    inner ℝ (matFeat N (star (featMat N x))) (matFeat N (star (featMat N y))) = inner ℝ x y := by
  rw [inner_matFeat, star_star, Matrix.trace_mul_comm, ← inner_matFeat, matFeat_featMat,
    matFeat_featMat]
  exact real_inner_comm _ _

/-- **Left multiplication is a linear isometry of the feature** (`V ↦ AV` is `ℂ`-linear and
Frobenius-isometric for unitary `A`).

DERIVED: no numeral. -/
theorem exists_isometry_mul_left (N : ℕ) (A : SU N) :
    ∃ T : FE N →ₗᵢ[ℝ] FE N, ∀ V : SU N, realFeature N (A * V) = T (realFeature N V) := by
  have hA : star (A : Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp A.2).1
  let L : FE N →ₗ[ℝ] FE N :=
    (matFeatₗ N).comp ((mulLeftₗ N (A : Matrix (Fin N) (Fin N) ℂ)).comp (featMatₗ N))
  have hL : ∀ x, L x = matFeat N ((A : Matrix (Fin N) (Fin N) ℂ) * featMat N x) := fun x => rfl
  refine ⟨L.isometryOfInner (fun x y => by rw [hL, hL]; exact inner_mulLeft N hA x y),
    fun V => ?_⟩
  show realFeature N (A * V) = L (realFeature N V)
  have hcoe : ((A * V : SU N) : Matrix (Fin N) (Fin N) ℂ)
      = (A : Matrix (Fin N) (Fin N) ℂ) * (V : Matrix (Fin N) (Fin N) ℂ) := rfl
  rw [realFeature_eq, realFeature_eq, map_smul, hL, featMat_matFeat, hcoe]

#print axioms exists_isometry_mul_left

/-- **Right multiplication is a linear isometry of the feature.**

DERIVED: no numeral. -/
theorem exists_isometry_mul_right (N : ℕ) (A : SU N) :
    ∃ T : FE N →ₗᵢ[ℝ] FE N, ∀ V : SU N, realFeature N (V * A) = T (realFeature N V) := by
  have hA : (A : Matrix (Fin N) (Fin N) ℂ) * star (A : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp A.2).1
  let L : FE N →ₗ[ℝ] FE N :=
    (matFeatₗ N).comp ((mulRightₗ N (A : Matrix (Fin N) (Fin N) ℂ)).comp (featMatₗ N))
  have hL : ∀ x, L x = matFeat N (featMat N x * (A : Matrix (Fin N) (Fin N) ℂ)) := fun x => rfl
  refine ⟨L.isometryOfInner (fun x y => by rw [hL, hL]; exact inner_mulRight N hA x y),
    fun V => ?_⟩
  show realFeature N (V * A) = L (realFeature N V)
  have hcoe : ((V * A : SU N) : Matrix (Fin N) (Fin N) ℂ)
      = (V : Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ) := rfl
  rw [realFeature_eq, realFeature_eq, map_smul, hL, featMat_matFeat, hcoe]

#print axioms exists_isometry_mul_right

/-- **Inversion is a linear isometry of the feature** (`V⁻¹ = V†`: transpose and conjugate, both
real-linear and Frobenius-isometric).

DERIVED: no numeral. -/
theorem exists_isometry_inv (N : ℕ) :
    ∃ T : FE N →ₗᵢ[ℝ] FE N, ∀ V : SU N, realFeature N V⁻¹ = T (realFeature N V) := by
  let L : FE N →ₗ[ℝ] FE N := (matFeatₗ N).comp ((starₗ N).comp (featMatₗ N))
  have hL : ∀ x, L x = matFeat N (star (featMat N x)) := fun x => rfl
  refine ⟨L.isometryOfInner (fun x y => by rw [hL, hL]; exact inner_star N x y), fun V => ?_⟩
  show realFeature N V⁻¹ = L (realFeature N V)
  rw [realFeature_eq, realFeature_eq, map_smul, hL, featMat_matFeat, coe_inv_SU]

#print axioms exists_isometry_inv

/-- **A plaquette trace against a frozen word is a feature functional**:
`Re tr(U D)/N = ⟪X U, X D⁻¹⟫` for `D ∈ SU(N)`, so the tilt vector `X D⁻¹` has norm `1`.

DERIVED: no numeral. -/
theorem reTr_mul_eq_inner (N : ℕ) (U D : SU N) :
    (Matrix.trace ((U : Matrix (Fin N) (Fin N) ℂ) * (D : Matrix (Fin N) (Fin N) ℂ))).re / (N : ℝ)
      = inner ℝ (realFeature N U) (realFeature N D⁻¹) := by
  rw [inner_realFeature_realFeature, coe_inv_SU, star_star]

#print axioms reTr_mul_eq_inner

end Feature

/-! ## 2. Integration helpers -/

section Helpers

/-- A continuous real function on a compact space is bounded in absolute value.

DERIVED: no numeral. -/
theorem exists_abs_le_of_continuous {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    {φ : Y → ℝ} (hφ : Continuous φ) : ∃ C : ℝ, ∀ y, |φ y| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_range (continuous_abs.comp hφ)).bddAbove
  exact ⟨C, fun y => hC (Set.mem_range_self y)⟩

#print axioms exists_abs_le_of_continuous

/-- **A continuous, measurable function on a compact space is integrable against a finite
measure.** The measurability is a separate hypothesis, so the σ-algebra need not be Borel (the
product σ-algebra of two Borel spaces is the case used).

DERIVED: no numeral. -/
theorem integrable_of_continuous_measurable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ] {φ : Y → ℝ} (hc : Continuous φ)
    (hm : Measurable φ) : Integrable φ μ := by
  obtain ⟨C, hC⟩ := exists_abs_le_of_continuous hc
  exact (integrable_const C).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => by rw [Real.norm_eq_abs]; exact hC y))

#print axioms integrable_of_continuous_measurable

/-- **A continuous function on a compact space into a second-countable normed group is integrable
against a finite measure.**

DERIVED: no numeral. -/
theorem integrable_of_continuous_vec {Y F : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    [NormedAddCommGroup F] [SecondCountableTopology F] {φ : Y → F} (hφ : Continuous φ) :
    Integrable φ μ := by
  obtain ⟨C, hC⟩ := exists_abs_le_of_continuous hφ.norm
  exact (integrable_const C).mono' hφ.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => le_trans (le_abs_self _) (hC y)))

#print axioms integrable_of_continuous_vec

/-- **A continuous function on a compact space is integrable against a finite measure.** The
helper every module below uses in place of the `SU(N)`-specific `PairCorr.integrable_su`.

DERIVED: no numeral. -/
theorem integrable_of_continuous {Ω : Type} [TopologicalSpace Ω] [CompactSpace Ω]
    [MeasurableSpace Ω] [OpensMeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {φ : Ω → ℝ} (hφ : Continuous φ) : Integrable φ P :=
  integrable_of_continuous_vec P hφ

#print axioms integrable_of_continuous

/-- Pointwise equal integrands have equal integrals.

DERIVED: no numeral. -/
theorem integral_congr_pointwise {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} {f g : Y → ℝ}
    (h : ∀ y, f y = g y) : ∫ y, f y ∂μ = ∫ y, g y ∂μ :=
  integral_congr_ae (Filter.Eventually.of_forall h)

#print axioms integral_congr_pointwise

/-- Linearity on two integrable terms.

DERIVED: no numeral. -/
theorem integral_lin2 {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} {F₁ F₂ : Y → ℝ}
    (h₁ : Integrable F₁ μ) (h₂ : Integrable F₂ μ) (c : ℝ) :
    ∫ y, (c * F₁ y + F₂ y) ∂μ = c * ∫ y, F₁ y ∂μ + ∫ y, F₂ y ∂μ := by
  rw [integral_add (h₁.const_mul c) h₂, integral_const_mul]

#print axioms integral_lin2

/-- Linearity on three integrable terms.

DERIVED: no numeral. -/
theorem integral_lin3 {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} {F₁ F₂ F₃ : Y → ℝ}
    (h₁ : Integrable F₁ μ) (h₂ : Integrable F₂ μ) (h₃ : Integrable F₃ μ) (c₁ c₂ : ℝ) :
    ∫ y, (c₁ * F₁ y + c₂ * F₂ y + F₃ y) ∂μ
      = c₁ * ∫ y, F₁ y ∂μ + c₂ * ∫ y, F₂ y ∂μ + ∫ y, F₃ y ∂μ := by
  rw [integral_add ((h₁.const_mul c₁).fun_add (h₂.const_mul c₂)) h₃,
    integral_add (h₁.const_mul c₁) (h₂.const_mul c₂), integral_const_mul, integral_const_mul]

#print axioms integral_lin3

/-- The sum of three integrable terms.

DERIVED: no numeral. -/
theorem integral_add3 {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} {F₁ F₂ F₃ : Y → ℝ}
    (h₁ : Integrable F₁ μ) (h₂ : Integrable F₂ μ) (h₃ : Integrable F₃ μ) :
    ∫ y, (F₁ y + F₂ y + F₃ y) ∂μ = ∫ y, F₁ y ∂μ + ∫ y, F₂ y ∂μ + ∫ y, F₃ y ∂μ := by
  rw [integral_add (h₁.fun_add h₂) h₃, integral_add h₁ h₂]

#print axioms integral_add3

/-- **The integrated quadratic form.** A pointwise `2tF ≤ t²G + K` integrates to
`2t ∫F ≤ t² ∫G + ∫K`.

DERIVED: `2` is the coefficient of the cross term and the square of `t`. -/
theorem quad_integral {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} {F G K : Y → ℝ}
    (hF : Integrable F μ) (hG : Integrable G μ) (hK : Integrable K μ)
    (hpt : ∀ (t : ℝ) (y : Y), 2 * t * F y ≤ t ^ 2 * G y + K y) (t : ℝ) :
    2 * t * ∫ y, F y ∂μ ≤ t ^ 2 * ∫ y, G y ∂μ + ∫ y, K y ∂μ := by
  calc 2 * t * ∫ y, F y ∂μ = ∫ y, 2 * t * F y ∂μ := (integral_const_mul (2 * t) F).symm
    _ ≤ ∫ y, (t ^ 2 * G y + K y) ∂μ :=
        integral_mono (hF.const_mul (2 * t)) ((hG.const_mul (t ^ 2)).fun_add hK) (fun y => hpt t y)
    _ = t ^ 2 * ∫ y, G y ∂μ + ∫ y, K y ∂μ := by
        rw [integral_add (hG.const_mul (t ^ 2)) hK, integral_const_mul]

#print axioms quad_integral

/-- **The quadratic-form inequality.** If `2tI ≤ t²A + B` for every real `t`, with `A ≥ 0`, then
`I² ≤ AB`, hence `|I| ≤ C` whenever `AB ≤ C²` and `C ≥ 0`.

DERIVED: `2` is the coefficient of the cross term and the square; `0` is the sign of `A`, `C`;
`1` is the shift in the witness `t = (B + 1)/(2I)` at `A = 0`. -/
theorem abs_le_of_quad {I A B C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hABC : A * B ≤ C ^ 2)
    (h : ∀ t : ℝ, 2 * t * I ≤ t ^ 2 * A + B) : |I| ≤ C := by
  have hsq : I ^ 2 ≤ A * B := by
    rcases hA.eq_or_lt with hA0 | hApos
    · have hI : I = 0 := by
        by_contra hI
        have hI' : I ≠ 0 := hI
        have h1 := h ((B + 1) / (2 * I))
        have e : 2 * ((B + 1) / (2 * I)) * I = B + 1 := by
          calc 2 * ((B + 1) / (2 * I)) * I = (B + 1) / (2 * I) * (2 * I) := by ring
            _ = B + 1 := div_mul_cancel₀ (B + 1) (mul_ne_zero two_ne_zero hI')
        have e2 : ((B + 1) / (2 * I)) ^ 2 * A = 0 := by rw [← hA0, mul_zero]
        linarith
      rw [hI, ← hA0]
      norm_num
    · obtain ⟨t, ht⟩ : ∃ t, t * A = I := ⟨I / A, div_mul_cancel₀ I hApos.ne'⟩
      have h1 := h t
      have e1 : t ^ 2 * A = t * I := by rw [← ht]; ring
      have h3 : t * I ≤ B := by linarith
      have e2 : I ^ 2 = A * (t * I) := by rw [← ht]; ring
      rw [e2]
      exact mul_le_mul_of_nonneg_left h3 hA
  exact abs_le_of_sq_le_sq (le_trans hsq hABC) hC

#print axioms abs_le_of_quad

/-- **Cauchy–Schwarz from the quadratic form**: `(∀ t, 2tI ≤ t²A + B) → |I| ≤ √A √B`.

DERIVED: `2` is the coefficient of the cross term and the square; `0` is the sign of `A`, `B`. -/
theorem abs_le_sqrt_mul_of_quad {I A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 2 * t * I ≤ t ^ 2 * A + B) : |I| ≤ Real.sqrt A * Real.sqrt B :=
  abs_le_of_quad hA (mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B))
    (le_of_eq (by rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB])) h

#print axioms abs_le_sqrt_mul_of_quad

end Helpers

/-! ## 3. The interfaces -/

section Interfaces

variable {Ω : Type} [MeasurableSpace Ω] {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The untilted Haar constants of a feature.** Mean `0`, second moments at most `‖w‖²/D`, fourth
moments at most `q4 ‖w‖⁴`, and the mixed third moments at most `t3 ‖u‖² ‖w‖`. At `SU(2)` the parity
`U ↦ −U` gives `t3 = 0`; the parity flag of the paper is the value `t3 = 0`.

DERIVED: `0` is the mean and the sign of the constants; `2`, `4` are the moment orders; `D` is a
field, not a numeral. -/
structure HaarConsts (P : Measure Ω) (X : Ω → E) where
  /-- The inverse second-moment scale: `E⟪w, X⟫² ≤ ‖w‖²/D`. -/
  D : ℝ
  /-- The fourth-moment constant. -/
  q4 : ℝ
  /-- The mixed third-moment constant. -/
  t3 : ℝ
  D_pos : 0 < D
  q4_nonneg : 0 ≤ q4
  t3_nonneg : 0 ≤ t3
  mean : ∀ w : E, ∫ g, inner ℝ w (X g) ∂P = 0
  second : ∀ w : E, ∫ g, inner ℝ w (X g) ^ 2 ∂P ≤ ‖w‖ ^ 2 / D
  fourth : ∀ w : E, ∫ g, inner ℝ w (X g) ^ 4 ∂P ≤ q4 * ‖w‖ ^ 4
  third : ∀ u w : E, |∫ g, inner ℝ u (X g) ^ 2 * inner ℝ w (X g) ∂P| ≤ t3 * ‖u‖ ^ 2 * ‖w‖

/-- **The tilted constants.** Under every tilt `e^{⟪θ, X⟫} P` with `‖θ‖ ≤ κ`, normalised by
`Z_θ = ∫ e^{⟪θ, X⟫}`: second moments at most `M₂ ‖w‖²` and `|E⟪w, X⟫| ≤ mb ‖w‖`. Stated unnormalised,
so no division appears.

DERIVED: `2` is the moment order. -/
def TiltBounds (P : Measure Ω) (X : Ω → E) (κ M₂ mb : ℝ) : Prop :=
  ∀ θ : E, ‖θ‖ ≤ κ →
    (∀ w : E, ∫ g, inner ℝ w (X g) ^ 2 * Real.exp (inner ℝ θ (X g)) ∂P
        ≤ M₂ * ‖w‖ ^ 2 * ∫ g, Real.exp (inner ℝ θ (X g)) ∂P) ∧
    (∀ w : E, |∫ g, inner ℝ w (X g) * Real.exp (inner ℝ θ (X g)) ∂P|
        ≤ mb * ‖w‖ * ∫ g, Real.exp (inner ℝ θ (X g)) ∂P)

/-- **The pair fibre weight** `K e^{⟪X h, T X g⟫ + ⟪α, X h⟫ + ⟪γ, X g⟫}`: `h` is the value of the
second link (`m` in `PairCorr`), `g` of the first (`l`), matching `PairCorr.fibre_corr_le`.

DERIVED: no numeral. -/
def fibreWeight (X : Ω → E) (K : ℝ) (T : E →L[ℝ] E) (α γ : E) (h g : Ω) : ℝ :=
  K * Real.exp (inner ℝ (X h) (T (X g)) + inner ℝ α (X h) + inner ℝ γ (X g))

/-- **The fibre covariance bound at constant `c`**, for every weight of coupling norm at most `τ`
and tilts at most `κ`, in the shape of `PairCorr.fibre_corr_le`: with `q(h) = ∫ w(h, ·)`,
`p(g) = ∫ w(·, g)` and `∫ a q = 0`, `∫∫ a b w ≤ (c/2)(∫ a² q + ∫ b² p)`.

DERIVED: `0` is the sign of `K` and the vanishing mean; `2` is the square and the halving. -/
def FibreBound [TopologicalSpace Ω] (P : Measure Ω) (X : Ω → E) (c τ κ : ℝ) : Prop :=
  ∀ (K : ℝ) (T : E →L[ℝ] E) (α γ : E), 0 < K → ‖T‖ ≤ τ → ‖α‖ ≤ κ → ‖γ‖ ≤ κ →
    ∀ a b : Ω → ℝ, Continuous a → Continuous b →
      ∫ h, a h * ∫ g, fibreWeight X K T α γ h g ∂P ∂P = 0 →
      ∫ h, ∫ g, a h * b g * fibreWeight X K T α γ h g ∂P ∂P
        ≤ c / 2 * (∫ h, a h ^ 2 * ∫ g, fibreWeight X K T α γ h g ∂P ∂P
          + ∫ g, b g ^ 2 * ∫ h, fibreWeight X K T α γ h g ∂P ∂P)

end Interfaces

/-! ## 4. The constants -/

section Constants

/-- **The Taylor coefficient of `e^y − 1 − y`** on `|y| ≤ r ≤ 3`: `e^y − 1 − y ≤ cR r · y²`
(`TiltedHaar.exp_sub_one_sub_le`).

DERIVED: `1/2, 1/6, 1/24, 1/120` are `1/k!` for `k = 2, …, 5`, each `|y|ᵏ ≤ r^{k−2} y²`; `1/360 = 2/6!`
is the remainder of `Complex.exp_bound'` at `n = 6` (its factor `2`); the exponents `2, 3, 4` are
`k − 2`. -/
def cR (r : ℝ) : ℝ := 1 / 2 + r / 6 + r ^ 2 / 24 + r ^ 3 / 120 + r ^ 4 / 360

/-- **The Taylor coefficient of `e^y − 1 − y − y²/2`** on `|y| ≤ r ≤ 3`:
`|e^y − 1 − y − y²/2| ≤ cR3 r · y²`.

DERIVED: as `cR` without the `k = 2` term. -/
def cR3 (r : ℝ) : ℝ := r / 6 + r ^ 2 / 24 + r ^ 3 / 120 + r ^ 4 / 360

/-- **The tilted second-moment constant**: `E_θ⟪u, X⟫² ≤ M2bound · ‖u‖²` for `‖θ‖ ≤ κ`, from
`e^y ≤ 1 + y + cR(κ) y²`, `E e^{⟪θ,X⟫} ≥ 1`, and the Haar constants.

DERIVED: `1` is the zeroth Taylor term; `2` is the moment order. -/
def M2bound (D q4 t3 κ : ℝ) : ℝ := 1 / D + t3 * κ + cR κ * q4 * κ ^ 2

/-- **The tilted mean constant**: `|E_θ⟪w, X⟫| ≤ mbarBound · ‖w‖` for `‖θ‖ ≤ κ`, with `s ≥ √(q4/D)`.

DERIVED: `2` is the Taylor order of the middle term and its `1/2!`. -/
def mbarBound (D q4 t3 s κ : ℝ) : ℝ := κ / D + t3 * κ ^ 2 / 2 + cR3 κ * κ ^ 2 * s

/-- The bound `e` on `Z·|E_π f|` for `f` centred and normalised in the tilted law.

DERIVED: `2` is the square of the coupling and the halving of the range argument
(`sd(g) ≤ G/2` for `0 ≤ g ≤ G`). -/
def dstarE (τ M₂ σ mb c₂ : ℝ) : ℝ := τ * σ * mb + c₂ * τ ^ 2 * M₂ / 2

/-- The lower bound `Z₀` on the pair partition function against the tilted product law.

DERIVED: `1` is `e⁰`; `2` is the square of the mean. -/
def dstarZ (τ mb : ℝ) : ℝ := 1 - τ * mb ^ 2

/-- The numerator of the pair bound.

DERIVED: `2` is the square. -/
def dstarNum (τ M₂ σ mb c₂ : ℝ) : ℝ :=
  τ * M₂ + c₂ * τ ^ 2 * M₂ + dstarE τ M₂ σ mb c₂ ^ 2 / dstarZ τ mb

/-- The denominator of the pair bound.

DERIVED: `1` is the normalisation; `2` is the square. -/
def dstarDen (τ M₂ σ mb c₂ : ℝ) : ℝ :=
  1 - τ * mb - dstarE τ M₂ σ mb c₂ ^ 2 / dstarZ τ mb

/-- **The pair bound** `δ* = num/den`: the maximal correlation of the fibre law.

DERIVED: no numeral. -/
def dstar (τ M₂ σ mb c₂ : ℝ) : ℝ := dstarNum τ M₂ σ mb c₂ / dstarDen τ M₂ σ mb c₂

end Constants

end MassGap.PairInterface
