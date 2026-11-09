import Mathlib
import MassGap.ElectricStep
import MassGap.HaarMoments
import MassGap.ChainCoarseSeed

/-!
# MassGap.SU2DiskLaw — Haar measure on `SU(2)` is normalised ball volume of `ℝ⁴` pushed to the sphere; the `(0,0)` entry is uniform on the unit disk, and the radial self-convolution `convT` is `π` times the group convolution

## The objects

* `qmat x = [[p, −p̄′], [p′, p̄]]`, `p = x₀ + i x₁`, `p′ = x₂ + i x₃`, the quaternion matrix of `x ∈ ℝ⁴`. It lies in
  `SU(2)` when `|x| = 1` (`qmat_mem`). `toSU x = qmat(x/‖x‖)`, and `1` at `x = 0`.
* `lmulE g`: left multiplication by `g ∈ SU(2)` on `ℝ⁴`. It is a linear isometry (`norm_lmulV`), and
  `toSU (lmulE g x) = g · toSU x` (`toSU_lmulE`).
* `ballP`: volume on the unit ball `B4`, normalised. `nu = ballP.map toSU`.

## What is proved

* `probHaar_eq_nu`. `nu` is a left-invariant probability measure: left multiplication is an isometry of `ℝ⁴`
  (`LinearIsometryEquiv.measurePreserving`). Haar uniqueness (`haarMeasure_unique`) then gives `probHaar (SU 2) = nu`.
* `conv_eq_ball`. For continuous `U, V` and `c = τ g`,
  `conv (U ∘ τ) (V ∘ τ) g = ∫ U(x₀/‖x‖) V((c x₀ + √(1 − c²) x₁)/‖x‖) dballP`.
  - The second argument starts as `⟪x, gvec g⟫/‖x‖` (`suTau_toSU_inv_mul`).
  - The reflection `reflG g` exchanges `gvec g` with `(c, √(1 − c²), 0, 0)`, fixes `e₀`, and preserves `ballP`.
* `lintegral_ball`: `∫_{B⁴} f(x₀/‖x‖, x₁/‖x‖) dx = (π/2) ∫_{|w|<1} f(w) dw` for measurable `f ≥ 0`. The proof:
  - split `ℝ⁴` into two planes (`measurePreserving_splitR4`);
  - take the radial integral in the second plane (`lintegral_radial`);
  - translate in `|b|²` (`lintegral_Ioi_add`);
  - scale `a = √t w` in the first plane (`lintegral_R2_smul`).

  So the direction of a uniform point of the ball projects to the uniform law on the disk.
* `lintegral_disk_ell`: for `sin ψ > 0`, the disk integral of `F(w₁, cos ψ w₁ + sin ψ w₂)` is `(sin ψ)⁻¹` times the
  integral of `F` over the ellipse `E_ψ` of `ConvolutionTransfer`. The circle is null (`volume_circle`).
* `volume_diskO` (`π`), `volume_B4` (`π²/2`).
* **The Weyl formula for class convolutions** (`conv_eq_ellInt`). Take continuous `U, V ≥ 0`, and `g` with
  `τ g = cos ψ ∈ (−1, 1)`. Then `conv (U ∘ τ) (V ∘ τ) g = ellInt ψ (U ⊗ V) / (π sin ψ)`.
* `convT_eq_pi_conv`: for `U` continuous and `≥ 0` on `[−1, 1]`, `convT U (τ g) = π · conv (U ∘ τ) (U ∘ τ) g`
  wherever `τ g ∈ (−1, 1)`.
* `eq_of_eq_on_Ioo`: two continuous functions on `SU(2)` that agree wherever `τ ∈ (−1, 1)` agree everywhere. The
  curve `g · diag(e^{it}, e^{−it})` (`dmat`) leaves `±1` into `τ ∈ (−1, 1)`.

DERIVED (module-wide):
- `4` is the real dimension of the quaternions.
- `π/2 = π · ½`: the plane's radial `π`, times `∫₀¹ t dt`.
- `π` is the area of the unit disk (`integral_sqrt_one_sub_sq`).
- `1/(π sin ψ)` is the density of `(τ h, τ(h⁻¹g))` on `E_ψ`, whose area is `π sin ψ` (`ellInt_one`).

Foundational footprint only (`#print axioms` at the end).
-/

noncomputable section

namespace MassGap.SU2DiskLaw

open MeasureTheory MeasureTheory.Measure Set MassGap.CompactGauge MassGap.SUN Complex

/-- `ℝ⁴` with its Euclidean structure. -/
abbrev R4 : Type := EuclideanSpace ℝ (Fin 4)

/-! ## 1. The quaternion matrix of a vector of `ℝ⁴` -/

/-- The sum of squares of the four coordinates. DERIVED: `0`–`3` the coordinate indices of `ℝ⁴`; `2` the
square. -/
def nsq4 (x : R4) : ℝ := x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2

theorem norm_sq_R4 (x : R4) : ‖x‖ ^ 2 = nsq4 x := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four]
  simp [Real.norm_eq_abs, sq_abs, nsq4]

/-- **The quaternion matrix** `[[p, −p̄'], [p', p̄]]` with `p = x₀ + i x₁`, `p' = x₂ + i x₃`. DERIVED: `0`–`3` the coordinate indices of
`ℝ⁴`; `2` the matrix size of `SU(2)`. -/
def qmat (x : R4) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x 0 : ℂ) + (x 1 : ℂ) * I, -((x 2 : ℂ) - (x 3 : ℂ) * I);
     (x 2 : ℂ) + (x 3 : ℂ) * I, (x 0 : ℂ) - (x 1 : ℂ) * I]

theorem qmat_mem {x : R4} (hx : nsq4 x = 1) : qmat x ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  unfold nsq4 at hx
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [qmat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Complex.ext_iff] <;>
      (try constructor) <;> first | ring1 | linear_combination hx
  · rw [qmat, Matrix.det_fin_two_of]
    apply Complex.ext <;> simp <;> first | ring1 | linear_combination hx

/-- `‖x‖⁻¹ x` has unit square sum for `x ≠ 0`. -/
theorem nsq4_normalise {x : R4} (hx : x ≠ 0) : nsq4 (‖x‖⁻¹ • x) = 1 := by
  have h := norm_sq_R4 x
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  unfold nsq4 at h ⊢
  simp only [PiLp.smul_apply, smul_eq_mul]
  field_simp
  linear_combination -h

/-- **The point of `SU(2)` on the ray of `x`**: the quaternion matrix of `x/‖x‖`, and `1` at `x = 0`. -/
def toSU (x : R4) : SU 2 :=
  if h : x = 0 then 1 else ⟨qmat (‖x‖⁻¹ • x), qmat_mem (nsq4_normalise h)⟩

theorem coe_toSU {x : R4} (hx : x ≠ 0) : (toSU x : Matrix (Fin 2) (Fin 2) ℂ) = qmat (‖x‖⁻¹ • x) := by
  simp [toSU, hx]

theorem continuous_qmat : Continuous qmat := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [qmat] <;> fun_prop

theorem measurable_toSU : Measurable toSU := by
  refine measurable_of_continuousOn_compl_singleton 0 ?_
  intro x hx
  have hx' : x ≠ 0 := hx
  refine ContinuousAt.continuousWithinAt ?_
  rw [Topology.IsInducing.subtypeVal.continuousAt_iff]
  have hev : (fun y => ((toSU y : SU 2) : Matrix (Fin 2) (Fin 2) ℂ)) =ᶠ[nhds x]
      fun y => qmat (‖y‖⁻¹ • y) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
    exact coe_toSU hy
  refine ContinuousAt.congr ?_ hev.symm
  refine continuous_qmat.continuousAt.comp ?_
  exact ((continuous_norm.continuousAt).inv₀ (norm_ne_zero_iff.mpr hx')).smul continuousAt_id

/-! ## 2. Left multiplication is an isometry of `ℝ⁴` -/

/-- An `SU(2)` element is `[[a, −b̄], [b, ā]]` with `a = g₀₀`, `b = g₁₀`. -/
theorem su2_eq (g : SU 2) : (g : Matrix (Fin 2) (Fin 2) ℂ)
    = !![(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0, -(starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0);
         (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0, (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0)] := by
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · simp [su2_conj_10]
  · rfl
  · simp [su2_conj_00]

/-- The first column of an `SU(2)` element is a unit vector. -/
theorem su2_col (g : SU 2) :
    ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im ^ 2
      + ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0).re ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0).im ^ 2 = 1 := by
  have hu : star (g : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1
  have h := congrArg Complex.re (congrFun (congrFun hu 0) 0)
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] at h
  linear_combination h

/-- The coordinates of `[[a, −b̄], [b, ā]] · qmat x`. DERIVED: `0`–`3` the coordinate indices of `ℝ⁴`;
`2` the `L²` exponent of the Euclidean space. -/
def lmulV (a b : ℂ) (x : R4) : R4 :=
  WithLp.toLp 2 ![a.re * x 0 - a.im * x 1 - b.re * x 2 - b.im * x 3,
    a.re * x 1 + a.im * x 0 - b.re * x 3 + b.im * x 2,
    b.re * x 0 - b.im * x 1 + a.re * x 2 + a.im * x 3,
    b.re * x 1 + b.im * x 0 + a.re * x 3 - a.im * x 2]

theorem qmat_lmulV (a b : ℂ) (x : R4) :
    qmat (lmulV a b x) = !![a, -(starRingEnd ℂ) b; b, (starRingEnd ℂ) a] * qmat x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qmat, lmulV, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;>
    (try constructor) <;> ring

theorem nsq4_lmulV (a b : ℂ) (x : R4) :
    nsq4 (lmulV a b x) = (a.re ^ 2 + a.im ^ 2 + b.re ^ 2 + b.im ^ 2) * nsq4 x := by
  simp [nsq4, lmulV]
  ring

/-- `lmulV a b` as a linear map. -/
def lmulL (a b : ℂ) : R4 →ₗ[ℝ] R4 where
  toFun := lmulV a b
  map_add' x y := by
    refine PiLp.ext fun i => ?_
    fin_cases i <;> simp [lmulV] <;> ring
  map_smul' r x := by
    refine PiLp.ext fun i => ?_
    fin_cases i <;> simp [lmulV] <;> ring

theorem norm_lmulV (g : SU 2) (x : R4) :
    ‖lmulV ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) x‖ = ‖x‖ := by
  have h := nsq4_lmulV ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) x
  rw [su2_col g, one_mul, ← norm_sq_R4, ← norm_sq_R4] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- **Left multiplication by `g` on `ℝ⁴`**, a linear isometry. -/
def lmulE (g : SU 2) : R4 ≃ₗᵢ[ℝ] R4 :=
  LinearIsometry.toLinearIsometryEquiv
    { lmulL ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) with
      norm_map' := norm_lmulV g } rfl

theorem lmulE_apply (g : SU 2) (x : R4) :
    lmulE g x = lmulV ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) x := rfl

/-- **Equivariance**: `toSU (g x) = g · toSU x` away from `0`. -/
theorem toSU_lmulE (g : SU 2) {x : R4} (hx : x ≠ 0) : toSU (lmulE g x) = g * toSU x := by
  have hn : ‖lmulE g x‖ = ‖x‖ := (lmulE g).norm_map x
  have hx' : lmulE g x ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; exact hx (norm_eq_zero.mp hn.symm)
  apply Subtype.ext
  rw [coe_toSU hx', Submonoid.coe_mul, coe_toSU hx, hn, ← LinearIsometryEquiv.map_smul, lmulE_apply,
    qmat_lmulV, ← su2_eq]

/-! ## 3. Haar measure on `SU(2)` from the ball of `ℝ⁴` -/

/-- The unit ball of `ℝ⁴`. -/
abbrev B4 : Set R4 := Metric.ball 0 1

/-- **Normalised volume on the unit ball of `ℝ⁴`.** -/
def ballP : Measure R4 := (volume B4)⁻¹ • volume.restrict B4

theorem volume_B4_pos : 0 < volume B4 := Metric.measure_ball_pos volume 0 one_pos

theorem volume_B4_lt_top : volume B4 < ⊤ := measure_ball_lt_top

instance : IsProbabilityMeasure ballP := by
  refine ⟨?_⟩
  rw [ballP, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel volume_B4_pos.ne' volume_B4_lt_top.ne

/-- A linear isometry preserves `ballP`. -/
theorem measurePreserving_ballP (L : R4 ≃ₗᵢ[ℝ] R4) : MeasurePreserving L ballP ballP := by
  have h0 := L.measurePreserving
  have hpre : (L : R4 → R4) ⁻¹' B4 = B4 := by
    ext x; simp [B4, Metric.mem_ball, dist_zero_right]
  have h1 := h0.restrict_preimage (s := B4) measurableSet_ball
  rw [hpre] at h1
  refine ⟨h1.measurable, ?_⟩
  rw [ballP, Measure.map_smul, h1.map_eq]

theorem ae_ne_zero_ballP : ∀ᵐ x ∂ballP, x ≠ (0 : R4) := by
  have h : ∀ᵐ x ∂(volume : Measure R4), x ≠ 0 := by
    rw [ae_iff]
    simp
  exact ae_smul_measure (ae_restrict_of_ae h) _

/-- **The candidate Haar measure**: `ballP` pushed to `SU(2)` along the ray map. -/
def nu : Measure (SU 2) := ballP.map toSU

instance : IsProbabilityMeasure nu := isProbabilityMeasure_map measurable_toSU.aemeasurable

instance : IsMulLeftInvariant nu := by
  refine ⟨fun g => ?_⟩
  unfold nu
  rw [Measure.map_map (measurable_const_mul g) measurable_toSU]
  have hae : ((fun x => g * x) ∘ toSU) =ᵐ[ballP] (toSU ∘ lmulE g) := by
    filter_upwards [ae_ne_zero_ballP] with x hx
    exact (toSU_lmulE g hx).symm
  rw [Measure.map_congr hae, ← Measure.map_map measurable_toSU (lmulE g).continuous.measurable,
    (measurePreserving_ballP (lmulE g)).map_eq]

/-- **Haar measure on `SU(2)` is `nu`.** -/
theorem probHaar_eq_nu : probHaar (SU 2) = nu := by
  have h := haarMeasure_unique nu (default : TopologicalSpace.PositiveCompacts (SU 2))
  have hd : ((default : TopologicalSpace.PositiveCompacts (SU 2)) : Set (SU 2)) = univ := TopologicalSpace.PositiveCompacts.coe_top
  rw [hd, measure_univ, one_smul] at h
  exact h.symm

/-! ## 4. The class coordinate on the sphere, and a reflection -/

open MassGap.ChainCoarseSeed MassGap.ElectricStep

/-- `½ Re tr g = Re g₀₀` on `SU(2)`. -/
theorem suTau_eq (g : SU 2) : suTau g = ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re := by
  unfold suTau WilsonAction.wilsonDensity
  rw [Matrix.trace_fin_two, ← su2_conj_00]
  simp
  ring

/-- The unit vector of `ℝ⁴` of an `SU(2)` element: `(Re g₀₀, Im g₀₀, Re g₁₀, Im g₁₀)`. -/
def gvec (g : SU 2) : R4 :=
  WithLp.toLp 2 ![((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re, ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im,
    ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0).re, ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0).im]

/-- The first coordinate vector. -/
def e0 : R4 := WithLp.toLp 2 ![1, 0, 0, 0]

theorem inner_e0 (x : R4) : inner ℝ x e0 = x 0 := by
  simp [e0, PiLp.inner_apply, Fin.sum_univ_four]

theorem suTau_toSU {x : R4} (hx : x ≠ 0) : suTau (toSU x) = x 0 / ‖x‖ := by
  rw [suTau_eq, coe_toSU hx]
  simp [qmat]
  ring

theorem suTau_toSU_inv_mul (g : SU 2) {x : R4} (hx : x ≠ 0) :
    suTau ((toSU x)⁻¹ * g) = inner ℝ x (gvec g) / ‖x‖ := by
  rw [suTau_eq]
  have hinv : (((toSU x)⁻¹ : SU 2) : Matrix (Fin 2) (Fin 2) ℂ)
      = star ((toSU x : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) := rfl
  rw [Submonoid.coe_mul, hinv, coe_toSU hx]
  simp [qmat, gvec, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, PiLp.inner_apply,
    Fin.sum_univ_four]
  ring

/-- The image of `gvec g` under the reflection: `(c, √(1 − c²), 0, 0)`, `c = Re g₀₀`. -/
def evec (c : ℝ) : R4 := WithLp.toLp 2 ![c, √(1 - c ^ 2), 0, 0]

theorem norm_gvec (g : SU 2) : ‖gvec g‖ = 1 := by
  have h := su2_col g
  have h2 : ‖gvec g‖ ^ 2 = 1 := by
    rw [norm_sq_R4]; simp [nsq4, gvec]; linear_combination h
  nlinarith [norm_nonneg (gvec g)]

theorem re00_sq_le (g : SU 2) : ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 2 ≤ 1 := by
  nlinarith [su2_col g, sq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im,
    sq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0).re, sq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0).im]

theorem norm_evec {c : ℝ} (hc : c ^ 2 ≤ 1) : ‖evec c‖ = 1 := by
  have h2 : ‖evec c‖ ^ 2 = 1 := by
    rw [norm_sq_R4]; simp [nsq4, evec]; rw [Real.sq_sqrt (by linarith)]; ring
  nlinarith [norm_nonneg (evec c)]

theorem inner_evec (c : ℝ) (x : R4) : inner ℝ x (evec c) = c * x 0 + √(1 - c ^ 2) * x 1 := by
  simp [evec, PiLp.inner_apply, Fin.sum_univ_four]
  try ring

/-- **The reflection** exchanging `gvec g` and `evec c`; it fixes `e0`. -/
def reflG (g : SU 2) : R4 ≃ₗᵢ[ℝ] R4 :=
  (ℝ ∙ (gvec g - evec ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re))ᗮ.reflection

theorem reflG_gvec (g : SU 2) : reflG g (gvec g) = evec ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re :=
  Submodule.reflection_sub (by rw [norm_gvec, norm_evec (re00_sq_le g)])

theorem reflG_e0 (g : SU 2) : reflG g e0 = e0 := by
  refine Submodule.reflection_mem_subspace_eq_self ?_
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [gvec, evec, e0, PiLp.inner_apply, Fin.sum_univ_four]

/-- **The reflection step.** Integrals of a function of the two coordinates `⟪x, e0⟫/‖x‖` and
`⟪x, gvec g⟫/‖x‖` against `ballP` equal those with `gvec g` replaced by `evec (Re g₀₀)`. -/
theorem integral_reflG (g : SU 2) (Φ : ℝ → ℝ → ℝ) :
    ∫ x, Φ (inner ℝ x e0 / ‖x‖) (inner ℝ x (gvec g) / ‖x‖) ∂ballP
      = ∫ x, Φ (inner ℝ x e0 / ‖x‖)
          (inner ℝ x (evec ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re) / ‖x‖) ∂ballP := by
  set R := reflG g
  have hR := measurePreserving_ballP R
  symm
  rw [← hR.integral_comp R.toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have a1 : inner ℝ (R x) e0 = inner ℝ x e0 := by
    conv_lhs => rw [← reflG_e0 g]
    exact LinearIsometryEquiv.inner_map_map _ _ _
  have a2 : inner ℝ (R x) (evec ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re) = inner ℝ x (gvec g) := by
    rw [← reflG_gvec g]
    exact LinearIsometryEquiv.inner_map_map _ _ _
  simp only
  rw [a1, a2, LinearIsometryEquiv.norm_map]

/-! ## 5. The convolution as a ball integral -/

theorem continuous_suTau : Continuous suTau := by
  unfold suTau
  exact continuous_const.sub WilsonAction.continuous_wilsonDensity

/-- **The class convolution on `SU(2)` as an integral over the ball.** For continuous `U, V`,
`conv (U ∘ τ) (V ∘ τ) g = ∫ U(x₀/‖x‖) V((c x₀ + √(1 − c²) x₁)/‖x‖) dballP`, `c = τ g`. -/
theorem conv_eq_ball (U V : ℝ → ℝ) (hU : Continuous U) (hV : Continuous V) (g : SU 2) :
    ElectricStep.conv (U ∘ suTau) (V ∘ suTau) g
      = ∫ x, U (x 0 / ‖x‖) * V ((suTau g * x 0 + √(1 - suTau g ^ 2) * x 1) / ‖x‖) ∂ballP := by
  unfold ElectricStep.conv
  rw [probHaar_eq_nu, nu, integral_map measurable_toSU.aemeasurable]
  swap
  · refine Continuous.aestronglyMeasurable ?_
    exact ((hU.comp continuous_suTau)).mul
      ((hV.comp continuous_suTau).comp (continuous_inv.mul continuous_const))
  have h1 : ∀ᵐ x ∂ballP, (U ∘ suTau) (toSU x) * (V ∘ suTau) ((toSU x)⁻¹ * g)
      = U (inner ℝ x e0 / ‖x‖) * V (inner ℝ x (gvec g) / ‖x‖) := by
    filter_upwards [ae_ne_zero_ballP] with x hx
    simp only [Function.comp_apply]
    rw [suTau_toSU hx, suTau_toSU_inv_mul g hx, inner_e0]
  rw [integral_congr_ae h1, integral_reflG g (fun a b => U a * V b)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [inner_e0, inner_evec, suTau_eq]

/-! ## 6. The ball integral of a function of the first two directions -/

open scoped ENNReal Real

/-- `ℝ⁴` as two planes. -/
def splitR4 (p : (ℝ × ℝ) × (ℝ × ℝ)) : R4 := WithLp.toLp 2 ![p.1.1, p.1.2, p.2.1, p.2.2]

theorem measurePreserving_splitR4 : MeasurePreserving splitR4 volume volume := by
  set Ψ : (ℝ × ℝ) × (ℝ × ℝ) → (Fin 4 → ℝ) := fun p => ![p.1.1, p.1.2, p.2.1, p.2.2] with hΨ
  have hm : Measurable Ψ := by
    refine measurable_pi_iff.mpr fun i => ?_
    fin_cases i <;> simp [hΨ] <;> fun_prop
  have h1 : MeasurePreserving Ψ volume volume := by
    refine ⟨hm, ?_⟩
    rw [volume_pi]
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
    have e : Ψ ⁻¹' univ.pi s = (s 0 ×ˢ s 1) ×ˢ (s 2 ×ˢ s 3) := by
      ext p
      simp only [hΨ, mem_preimage, mem_univ_pi, Fin.forall_fin_succ, mem_prod]
      simp [and_assoc]
    rw [e]
    simp only [Measure.volume_eq_prod, Measure.prod_prod, Fin.prod_univ_four]
    ring
  exact (PiLp.volume_preserving_toLp (Fin 4)).comp h1

/-- The open unit disk of the plane. -/
def diskO : Set (ℝ × ℝ) := {w | w.1 ^ 2 + w.2 ^ 2 < 1}

theorem measurableSet_diskO : MeasurableSet diskO :=
  measurableSet_lt (by fun_prop) measurable_const

/-- **Radial integrals in the plane**: `∫ H(|b|²) db = π ∫₀^∞ H(u) du`. -/
theorem lintegral_radial (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ b : ℝ × ℝ, H (b.1 ^ 2 + b.2 ^ 2) = ENNReal.ofReal π * ∫⁻ u in Ioi 0, H u := by
  rw [← lintegral_comp_polarCoord_symm]
  have e1 : ∀ p : ℝ × ℝ, (polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2 = p.1 ^ 2 := by
    intro p
    show (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2
    linear_combination p.1 ^ 2 * Real.sin_sq_add_cos_sq p.2
  simp_rw [e1]
  rw [show polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π from rfl, Measure.volume_eq_prod,
    ← Measure.prod_restrict, lintegral_prod _ (by fun_prop)]
  simp only [smul_eq_mul, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioo]
  have hsub : ∫⁻ u in Ioi 0, H u = ∫⁻ r in Ioi 0, ENNReal.ofReal (2 * r) * H (r ^ 2) := by
    have himg : (fun r : ℝ => r ^ 2) '' Ioi 0 = Ioi 0 := by
      ext u
      constructor
      · rintro ⟨r, hr, rfl⟩; exact pow_pos (show (0 : ℝ) < r from hr) 2
      · intro hu
        exact ⟨√u, Real.sqrt_pos.mpr hu, Real.sq_sqrt (le_of_lt hu)⟩
    have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioi (0 : ℝ)) (f := fun r => r ^ 2)
      (f' := fun r => 2 * r) measurableSet_Ioi
      (fun x _ => by simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt)
      (fun a ha b hb hab => by
        have ha' : (0 : ℝ) ≤ a := le_of_lt ha
        have hb' : (0 : ℝ) ≤ b := le_of_lt hb
        exact (pow_left_inj₀ ha' hb' two_ne_zero).mp hab) H
    rw [himg] at h
    rw [h]
    refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    rw [abs_of_pos (by have : (0 : ℝ) < r := hr; positivity)]
  rw [hsub, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [mul_comm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr0 : (0 : ℝ) ≤ r := le_of_lt hr
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), show π - -π = 2 * π by ring,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Translation on the half line. -/
theorem lintegral_Ioi_add (φ : ℝ → ℝ≥0∞) (A : ℝ) :
    ∫⁻ u in Ioi 0, φ (A + u) = ∫⁻ t in Ioi A, φ t := by
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi,
    ← lintegral_add_left_eq_self ((Ioi A).indicator φ) A]
  refine lintegral_congr fun u => ?_
  simp only [Set.indicator, Set.mem_Ioi, lt_add_iff_pos_right]

/-- Scaling in the plane. -/
theorem lintegral_R2_smul (G : ℝ × ℝ → ℝ≥0∞) (hG : Measurable G) {r : ℝ} (hr : 0 < r) :
    ∫⁻ a : ℝ × ℝ, G a = ENNReal.ofReal (r ^ 2) * ∫⁻ w, G (r • w) := by
  have hmap := Measure.map_addHaar_smul (volume : Measure (ℝ × ℝ)) hr.ne'
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  rw [hfin] at hmap
  have h2 : ∫⁻ w, G (r • w) = ∫⁻ a, G a ∂(Measure.map (r • ·) volume) :=
    (lintegral_map hG (measurable_const_smul r)).symm
  rw [h2, hmap, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

/-- The squared norm in the plane. -/
def nsq2 (a : ℝ × ℝ) : ℝ := a.1 ^ 2 + a.2 ^ 2

theorem nsq2_nonneg (a : ℝ × ℝ) : 0 ≤ nsq2 a := by unfold nsq2; positivity

theorem norm_splitR4 (p : (ℝ × ℝ) × (ℝ × ℝ)) : ‖splitR4 p‖ = √(nsq2 p.1 + nsq2 p.2) := by
  have h := norm_sq_R4 (splitR4 p)
  rw [← Real.sqrt_sq (norm_nonneg (splitR4 p)), h]
  congr 1
  simp [nsq4, nsq2, splitR4]
  ring

/-- **The ball integral of a function of the first two directions.** For `f ≥ 0` measurable on the
plane, `∫_{B⁴} f(x₀/‖x‖, x₁/‖x‖) dx = (π/2) ∫_{|w| < 1} f(w) dw`: the direction `x/‖x‖` of a uniform
point of the ball projects to the uniform law on the disk. -/
theorem lintegral_ball (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x in B4, f (x 0 / ‖x‖, x 1 / ‖x‖) = ENNReal.ofReal (π / 2) * ∫⁻ w, diskO.indicator f w := by
  have hc : ∀ i : Fin 4, Measurable fun x : R4 => x i :=
    fun i => (by fun_prop : Continuous fun x : R4 => x i).measurable
  have hF : Measurable fun x : R4 => f (x 0 / ‖x‖, x 1 / ‖x‖) :=
    hf.comp (((hc 0).div measurable_norm).prodMk ((hc 1).div measurable_norm))
  -- the integrand on the split coordinates
  set φ : (ℝ × ℝ) → ℝ → ℝ≥0∞ := fun a t => if t < 1 then f (a.1 / √t, a.2 / √t) else 0 with hφ
  have hφm : Measurable (Function.uncurry φ) := by
    refine Measurable.ite (measurableSet_lt measurable_snd measurable_const) ?_ measurable_const
    exact hf.comp ((measurable_fst.fst.div (Real.continuous_sqrt.measurable.comp measurable_snd)).prodMk
      (measurable_fst.snd.div (Real.continuous_sqrt.measurable.comp measurable_snd)))
  have e1 : ∀ p, B4.indicator (fun x : R4 => f (x 0 / ‖x‖, x 1 / ‖x‖)) (splitR4 p)
      = φ p.1 (nsq2 p.1 + nsq2 p.2) := by
    intro p
    have hn := norm_splitR4 p
    have h0 : 0 ≤ nsq2 p.1 + nsq2 p.2 := add_nonneg (nsq2_nonneg _) (nsq2_nonneg _)
    by_cases h : nsq2 p.1 + nsq2 p.2 < 1
    · have hb : splitR4 p ∈ B4 := by
        rw [B4, Metric.mem_ball, dist_zero_right, hn, Real.sqrt_lt' one_pos, one_pow]; exact h
      rw [Set.indicator_of_mem hb, hn]
      simp only [hφ, if_pos h]
      simp [splitR4]
    · have hb : splitR4 p ∉ B4 := by
        rw [B4, Metric.mem_ball, dist_zero_right, hn, Real.sqrt_lt' one_pos, one_pow]; exact h
      rw [Set.indicator_of_notMem hb]
      simp only [hφ, if_neg h]
  rw [← lintegral_indicator measurableSet_ball,
    ← measurePreserving_splitR4.lintegral_comp (hF.indicator measurableSet_ball)]
  simp_rw [e1]
  have hGm : Measurable fun p : (ℝ × ℝ) × (ℝ × ℝ) => φ p.1 (nsq2 p.1 + nsq2 p.2) :=
    hφm.comp (measurable_fst.prodMk (by unfold nsq2; fun_prop))
  rw [Measure.volume_eq_prod, lintegral_prod _ hGm.aemeasurable]
  -- the inner integral, radially
  set K : (ℝ × ℝ) → ℝ → ℝ≥0∞ := fun a t => if nsq2 a < t then φ a t else 0 with hK
  have e2 : ∀ a, ∫⁻ b, φ a (nsq2 a + nsq2 b) = ENNReal.ofReal π * ∫⁻ t, K a t := by
    intro a
    have hH : Measurable fun u => φ a (nsq2 a + u) :=
      hφm.comp (measurable_const.prodMk (measurable_const.add measurable_id))
    have h := lintegral_radial (fun u => φ a (nsq2 a + u)) hH
    rw [show (fun b : ℝ × ℝ => φ a (nsq2 a + nsq2 b)) = fun b => φ a (nsq2 a + (b.1 ^ 2 + b.2 ^ 2))
      from rfl, h, lintegral_Ioi_add (φ a) (nsq2 a), ← lintegral_indicator measurableSet_Ioi]
    rfl
  simp_rw [e2]
  have hKm : Measurable (Function.uncurry K) := by
    refine Measurable.ite (measurableSet_lt (by unfold nsq2; fun_prop) measurable_snd) hφm measurable_const
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_lintegral_swap hKm.aemeasurable]
  -- scaling at each `t`
  set D := ∫⁻ w, diskO.indicator f w with hD
  have e3 : ∀ t, ∫⁻ a, K a t = (Ioo (0 : ℝ) 1).indicator (fun t => ENNReal.ofReal t) t * D := by
    intro t
    by_cases ht : t ∈ Ioo (0 : ℝ) 1
    · rw [Set.indicator_of_mem ht]
      have hs := Real.sqrt_pos.mpr ht.1
      have hKt : Measurable fun a => K a t := hKm.comp (measurable_id.prodMk measurable_const)
      rw [lintegral_R2_smul (fun a => K a t) hKt hs, Real.sq_sqrt ht.1.le, hD]
      congr 1
      refine lintegral_congr fun w => ?_
      have hn : nsq2 (√t • w) = t * nsq2 w := by
        simp only [nsq2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        rw [mul_pow, mul_pow, Real.sq_sqrt ht.1.le]; ring
      have hst : √t ≠ 0 := hs.ne'
      simp only [hK, hφ, hn, if_pos ht.2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      by_cases hw : w ∈ diskO
      · have : t * nsq2 w < t := mul_lt_of_lt_one_right ht.1 hw
        rw [if_pos this, Set.indicator_of_mem hw]
        congr 1
        ext <;> field_simp
      · have : ¬ t * nsq2 w < t := by
          have := ht.1; unfold diskO at hw; unfold nsq2; simp only [mem_setOf_eq, not_lt] at hw
          nlinarith
        rw [if_neg this, Set.indicator_of_notMem hw]
    · rw [Set.indicator_of_notMem ht, zero_mul]
      have hz : ∀ a, K a t = 0 := by
        intro a
        simp only [hK, hφ]
        by_cases h1 : nsq2 a < t
        · have : ¬ t < 1 := fun h2 => ht ⟨lt_of_le_of_lt (nsq2_nonneg a) h1, h2⟩
          rw [if_pos h1, if_neg this]
        · rw [if_neg h1]
      simp [hz]
  simp_rw [e3]
  rw [lintegral_mul_const _ ((Measurable.indicator ENNReal.measurable_ofReal measurableSet_Ioo)),
    lintegral_indicator measurableSet_Ioo]
  have hhalf : ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal t = ENNReal.ofReal (1 / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (((by fun_prop : Continuous fun t : ℝ => t).integrableOn_Icc (a := (0 : ℝ)) (b := 1)).mono_set
        Ioo_subset_Icc_self)
      (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ht.1.le)]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, integral_id]
    norm_num
  rw [hhalf, ← mul_assoc, ← ENNReal.ofReal_mul Real.pi_pos.le]
  congr 2
  ring

/-! ## 7. From the disk to the ellipse -/

open MassGap.ConvolutionTransfer

/-- The closed unit disk. -/
def diskC : Set (ℝ × ℝ) := {w | w.1 ^ 2 + w.2 ^ 2 ≤ 1}

/-- The unit circle is null. -/
theorem volume_circle : (volume : Measure (ℝ × ℝ)) {w | w.1 ^ 2 + w.2 ^ 2 = 1} = 0 := by
  have hm : MeasurableSet {w : ℝ × ℝ | w.1 ^ 2 + w.2 ^ 2 = 1} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hm]
  refine Filter.Eventually.of_forall fun x => ?_
  have hsub : Prod.mk x ⁻¹' {w : ℝ × ℝ | w.1 ^ 2 + w.2 ^ 2 = 1}
      ⊆ ({√(1 - x ^ 2), -√(1 - x ^ 2)} : Set ℝ) := by
    intro y hy
    simp only [mem_preimage, mem_setOf_eq] at hy
    have h1 : 0 ≤ 1 - x ^ 2 := by nlinarith [sq_nonneg y]
    have h2 : (y - √(1 - x ^ 2)) * (y + √(1 - x ^ 2)) = 0 := by
      have := Real.sq_sqrt h1; nlinarith
    rcases mul_eq_zero.mp h2 with h | h
    · left; linarith
    · right; simp only [mem_singleton_iff]; linarith
  exact measure_mono_null hsub ((Set.toFinite _).measure_zero _)

/-- **The disk integral is the ellipse integral.** For `sin ψ > 0`,
`∫_{|w|<1} F(w₁, cos ψ w₁ + sin ψ w₂) dw = (sin ψ)⁻¹ ∫_{E_ψ} F`. -/
theorem lintegral_disk_ell {ψ : ℝ} (hs : 0 < Real.sin ψ) (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ w, diskO.indicator (fun w => F (w.1, Real.cos ψ * w.1 + Real.sin ψ * w.2)) w
      = ENNReal.ofReal (Real.sin ψ)⁻¹ * ∫⁻ p, (ellSet ψ).indicator F p := by
  set c := Real.cos ψ
  set s := Real.sin ψ
  set L : ℝ × ℝ → ℝ × ℝ := fun w => (w.1, c * w.1 + s * w.2) with hL
  have hLm : Measurable L := by fun_prop
  -- the push-forward of Lebesgue measure under `L`
  have hmap : Measure.map L volume = ENNReal.ofReal s⁻¹ • (volume : Measure (ℝ × ℝ)) := by
    have hsc : Measure.map (Prod.map id (fun z : ℝ => s * z)) (volume : Measure (ℝ × ℝ))
        = ENNReal.ofReal s⁻¹ • (volume : Measure (ℝ × ℝ)) := by
      rw [Measure.volume_eq_prod, ← Measure.map_prod_map _ _ measurable_id (measurable_const_mul s),
        Measure.map_id, Real.map_volume_mul_left hs.ne', abs_of_pos (inv_pos.mpr hs),
        Measure.prod_smul_right]
    have hsk : MeasurePreserving (fun p : ℝ × ℝ => (id p.1, p.2 + c * p.1)) volume volume := by
      rw [Measure.volume_eq_prod]
      exact MeasurePreserving.skew_product (g := fun a z => z + c * a) (MeasurePreserving.id volume)
        (measurable_snd.add (measurable_const.mul measurable_fst))
        (Filter.Eventually.of_forall fun a => (measurePreserving_add_right volume (c * a)).map_eq)
    have hcomp : L = (fun p : ℝ × ℝ => (id p.1, p.2 + c * p.1)) ∘ Prod.map id (fun z : ℝ => s * z) := by
      funext w
      show (w.1, c * w.1 + s * w.2) = (w.1, s * w.2 + c * w.1)
      rw [add_comm]
    rw [hcomp, ← Measure.map_map hsk.measurable (measurable_id.prodMap (measurable_const_mul s)), hsc,
      Measure.map_smul, hsk.map_eq]
  have hΦ : Measurable ((ellSet ψ).indicator F) := hF.indicator (measurableSet_ellSet ψ)
  have h1 : ∫⁻ w, (ellSet ψ).indicator F (L w) = ENNReal.ofReal s⁻¹ * ∫⁻ p, (ellSet ψ).indicator F p := by
    rw [← lintegral_map hΦ hLm, hmap, lintegral_smul_measure, smul_eq_mul]
  rw [← h1]
  -- the two integrands differ only on the circle
  have hcirc := measure_eq_zero_iff_ae_notMem.mp volume_circle
  refine lintegral_congr_ae ?_
  filter_upwards [hcirc] with w hw
  replace hw : w.1 ^ 2 + w.2 ^ 2 ≠ 1 := hw
  have hmem : w ∈ diskO ↔ L w ∈ ellSet ψ := by
    simp only [diskO, mem_setOf_eq, ellSet, hL, mem_Icc]
    have hs2 : 0 < s ^ 2 := by positivity
    have e : (c * w.1 + s * w.2 - w.1 * c) ^ 2 = s ^ 2 * w.2 ^ 2 := by ring
    rw [e]
    constructor
    · intro h
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · nlinarith [sq_nonneg w.2, sq_nonneg (w.1 + 1)]
      · nlinarith [sq_nonneg w.2, sq_nonneg (w.1 - 1)]
      · nlinarith [sq_nonneg w.2]
    · rintro ⟨-, h⟩
      have : w.2 ^ 2 ≤ 1 - w.1 ^ 2 := by
        by_contra hc; push Not at hc; nlinarith
      exact lt_of_le_of_ne (by linarith) hw
  by_cases h : w ∈ diskO
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.mp h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hmem.mpr h'))]

/-! ## 8. The Weyl convolution identity -/

/-- The ellipse integral of a continuous non-negative integrand, as a Lebesgue integral. -/
theorem lintegral_ell_ofReal {ψ : ℝ} (hs : 0 ≤ Real.sin ψ) (F : ℝ → ℝ → ℝ)
    (hF : Continuous (Function.uncurry F)) (hF0 : ∀ t y, 0 ≤ F t y) :
    ∫⁻ p, (ellSet ψ).indicator (fun p => ENNReal.ofReal (F p.1 p.2)) p
      = ENNReal.ofReal (ellInt ψ F) := by
  have hG : EllGood ψ F := ellGood_of_continuousOn hF.continuousOn
  rw [ellInt_eq_prod hs hG, ofReal_integral_eq_lintegral_ofReal hG.integrable
    (Filter.Eventually.of_forall fun p => Set.indicator_nonneg (fun q _ => hF0 q.1 q.2) p),
    Measure.volume_eq_prod]
  refine lintegral_congr fun p => ?_
  by_cases h : p ∈ ellSet ψ
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, ENNReal.ofReal_zero]

theorem ellInt_nonneg {ψ : ℝ} (hs : 0 ≤ Real.sin ψ) (F : ℝ → ℝ → ℝ)
    (hF : Continuous (Function.uncurry F)) (hF0 : ∀ t y, 0 ≤ F t y) : 0 ≤ ellInt ψ F := by
  rw [ellInt_eq_prod hs (ellGood_of_continuousOn hF.continuousOn)]
  exact integral_nonneg fun p => Set.indicator_nonneg (fun q _ => hF0 q.1 q.2) p

/-- The area of `E_ψ` is `π sin ψ`. -/
theorem ellInt_one (ψ : ℝ) : ellInt ψ (fun _ _ => 1) = π * Real.sin ψ := by
  unfold ellInt
  have e : ∀ t : ℝ, ∫ _ in ellLo ψ t..ellHi ψ t, (1 : ℝ) = 2 * Real.sin ψ * √(1 - t ^ 2) := by
    intro t
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    unfold ellHi ellLo
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq]
  ring

/-- **The area of the unit disk** is `π`. -/
theorem volume_diskO : (volume : Measure (ℝ × ℝ)) diskO = ENNReal.ofReal π := by
  have h := lintegral_disk_ell (ψ := π / 2) (by rw [Real.sin_pi_div_two]; exact one_pos)
    (fun _ => 1) measurable_const
  rw [lintegral_indicator_const measurableSet_diskO, one_mul] at h
  rw [h]
  have h2 := lintegral_ell_ofReal (ψ := π / 2) (by rw [Real.sin_pi_div_two]; exact zero_le_one)
    (fun _ _ => 1) continuous_const (fun _ _ => zero_le_one)
  simp only [ENNReal.ofReal_one] at h2
  rw [h2, ellInt_one, Real.sin_pi_div_two, inv_one, ENNReal.ofReal_one, one_mul, mul_one]

/-- **The volume of the unit ball of `ℝ⁴`** is `π²/2`. -/
theorem volume_B4 : volume B4 = ENNReal.ofReal (π / 2) * ENNReal.ofReal π := by
  have h := lintegral_ball (fun _ => 1) measurable_const
  rw [setLIntegral_one, lintegral_indicator_const measurableSet_diskO, one_mul, volume_diskO] at h
  exact h

/-- **The Weyl formula for the class convolution on `SU(2)`.** For continuous non-negative `U, V` and
`g` of class coordinate `τ g = cos ψ ∈ (−1, 1)`,
`conv (U ∘ τ) (V ∘ τ) g = (π sin ψ)⁻¹ ∫∫_{E_ψ} U(t) V(y) dt dy`. -/
theorem conv_eq_ellInt (U V : ℝ → ℝ) (hU : Continuous U) (hV : Continuous V)
    (hU0 : ∀ t, 0 ≤ U t) (hV0 : ∀ t, 0 ≤ V t) (g : SU 2) (hg : suTau g ∈ Ioo (-1 : ℝ) 1) :
    ElectricStep.conv (U ∘ suTau) (V ∘ suTau) g
      = ellInt (Real.arccos (suTau g)) (fun t y => U t * V y)
          / (π * Real.sin (Real.arccos (suTau g))) := by
  set c := suTau g with hc
  set ψ := Real.arccos c with hψ
  have hcos : Real.cos ψ = c := Real.cos_arccos hg.1.le hg.2.le
  have hsin : Real.sin ψ = √(1 - c ^ 2) := Real.sin_arccos c
  have hs : 0 < Real.sin ψ := by
    rw [hsin]; apply Real.sqrt_pos.mpr; nlinarith [hg.1, hg.2]
  rw [conv_eq_ball U V hU hV g]
  set Ψ : R4 → ℝ := fun x => U (x 0 / ‖x‖) * V ((c * x 0 + √(1 - c ^ 2) * x 1) / ‖x‖) with hΨdef
  have hΨ0 : ∀ x, 0 ≤ Ψ x := fun x => mul_nonneg (hU0 _) (hV0 _)
  have hcoord : ∀ i : Fin 4, Measurable fun x : R4 => x i :=
    fun i => (by fun_prop : Continuous fun x : R4 => x i).measurable
  have hΨm : Measurable Ψ :=
    (hU.measurable.comp ((hcoord 0).div measurable_norm)).mul
      (hV.measurable.comp (((measurable_const.mul (hcoord 0)).add
        (measurable_const.mul (hcoord 1))).div measurable_norm))
  have hFm : Measurable fun w : ℝ × ℝ => ENNReal.ofReal (U w.1 * V (Real.cos ψ * w.1 + Real.sin ψ * w.2)) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have e1 : ∫⁻ x in B4, ENNReal.ofReal (Ψ x)
      = ENNReal.ofReal (π / 2) * ∫⁻ w, diskO.indicator
          (fun w => ENNReal.ofReal (U w.1 * V (Real.cos ψ * w.1 + Real.sin ψ * w.2))) w := by
    rw [← lintegral_ball _ hFm]
    refine lintegral_congr fun x => ?_
    simp only [hΨdef, hcos, hsin]
    congr 3
    ring
  have hUV : Continuous (Function.uncurry fun t y => U t * V y) :=
    (hU.comp continuous_fst).mul (hV.comp continuous_snd)
  have hE0 := ellInt_nonneg hs.le (fun t y => U t * V y) hUV (fun t y => mul_nonneg (hU0 t) (hV0 y))
  rw [ballP, integral_smul_measure, integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall hΨ0) hΨm.aestronglyMeasurable, e1,
    lintegral_disk_ell hs (fun p => ENNReal.ofReal (U p.1 * V p.2))
      (ENNReal.measurable_ofReal.comp (by fun_prop)),
    lintegral_ell_ofReal hs.le (fun t y => U t * V y) hUV (fun t y => mul_nonneg (hU0 t) (hV0 y)),
    volume_B4]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  have hpi := Real.pi_pos
  field_simp

/-! ## 9. The radial convolution `convT` against the group convolution -/

/-- Clamp to `[−1, 1]`. -/
def clamp1 (t : ℝ) : ℝ := max (-1) (min t 1)

theorem clamp1_of_mem {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : clamp1 t = t := by
  unfold clamp1; rw [min_eq_left ht.2, max_eq_right ht.1]

theorem clamp1_mem (t : ℝ) : clamp1 t ∈ Icc (-1 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

theorem continuous_clamp1 : Continuous clamp1 := by unfold clamp1; fun_prop

/-- `ellInt` sees its integrand on `[−1, 1]²` only. -/
theorem ellInt_congr (ψ : ℝ) {F F' : ℝ → ℝ → ℝ}
    (h : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1, F t y = F' t y) : ellInt ψ F = ellInt ψ F' := by
  unfold ellInt
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le (by norm_num)] at ht
  refine intervalIntegral.integral_congr fun y hy => ?_
  exact h t ht y (Set.uIcc_subset_Icc (ellLo_mem ht) (ellHi_mem ht) hy)

/-- **The radial self-convolution is `π` times the group convolution.** For `U` continuous and
non-negative on `[−1, 1]`, at `g` with `τ g ∈ (−1, 1)`:
`convT U (τ g) = π · conv (U ∘ τ) (U ∘ τ) g`. -/
theorem convT_eq_pi_conv (U : ℝ → ℝ) (hU : Continuous U) (hU0 : ∀ t ∈ Icc (-1 : ℝ) 1, 0 ≤ U t)
    (g : SU 2) (hg : suTau g ∈ Ioo (-1 : ℝ) 1) :
    convT U (suTau g) = π * ElectricStep.conv (U ∘ suTau) (U ∘ suTau) g := by
  set U' := U ∘ clamp1 with hU'
  have hU'c : Continuous U' := hU.comp continuous_clamp1
  have hU'0 : ∀ t, 0 ≤ U' t := fun t => hU0 _ (clamp1_mem t)
  have hconv : ElectricStep.conv (U ∘ suTau) (U ∘ suTau) g
      = ElectricStep.conv (U' ∘ suTau) (U' ∘ suTau) g := by
    unfold ElectricStep.conv
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only [hU', Function.comp_apply, clamp1_of_mem (suTau_mem _)]
  have hs : 0 < Real.sin (Real.arccos (suTau g)) := by
    rw [Real.sin_arccos]; apply Real.sqrt_pos.mpr; nlinarith [hg.1, hg.2]
  rw [hconv, conv_eq_ellInt U' U' hU'c hU'c hU'0 hU'0 g hg]
  unfold convT ellConv
  rw [ellInt_congr _ (F' := fun t y => U' t * U' y) (fun t ht y hy => by
    simp only [hU', Function.comp_apply, clamp1_of_mem ht, clamp1_of_mem hy])]
  have hpi := Real.pi_pos
  field_simp

/-! ## 10. Continuous class data agreeing off `±1` agree everywhere -/

/-- The diagonal element `diag(e^{it}, e^{−it})`. -/
def dmat (t : ℝ) : SU 2 :=
  ⟨qmat (WithLp.toLp 2 ![Real.cos t, Real.sin t, 0, 0]),
    qmat_mem (by simp [nsq4, Real.cos_sq_add_sin_sq])⟩

theorem continuous_dmat : Continuous dmat := by
  refine Continuous.subtype_mk (continuous_qmat.comp ?_) _
  refine (PiLp.continuous_toLp 2 _).comp ?_
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp <;> fun_prop

theorem dmat_zero : dmat 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dmat, qmat]

theorem suTau_mul_dmat (g : SU 2) (t : ℝ) :
    suTau (g * dmat t) = ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re * Real.cos t
      - ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im * Real.sin t := by
  rw [suTau_eq, Submonoid.coe_mul]
  simp [dmat, qmat, Matrix.mul_apply, Fin.sum_univ_two, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem suTau_dmat (t : ℝ) : suTau (dmat t) = Real.cos t := by
  have h := suTau_mul_dmat 1 t
  rw [one_mul] at h
  rw [h]
  simp

/-- **Two continuous functions on `SU(2)` that agree wherever `τ ∈ (−1, 1)` agree everywhere.** -/
theorem eq_of_eq_on_Ioo {F₁ F₂ : SU 2 → ℝ} (h₁ : Continuous F₁) (h₂ : Continuous F₂)
    (h : ∀ g, suTau g ∈ Ioo (-1 : ℝ) 1 → F₁ g = F₂ g) (g : SU 2) : F₁ g = F₂ g := by
  by_cases hg : suTau g ∈ Ioo (-1 : ℝ) 1
  · exact h g hg
  have hmem := suTau_mem g
  have hre : ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 2 = 1 := by
    rw [← suTau_eq]
    rcases lt_or_eq_of_le hmem.1 with h1 | h1
    · rcases lt_or_eq_of_le hmem.2 with h2 | h2
      · exact absurd ⟨h1, h2⟩ hg
      · rw [h2]; norm_num
    · rw [← h1]; norm_num
  have him : ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im = 0 := by
    have := su2_col g
    nlinarith [sq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im,
      sq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0).re, sq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0).im]
  have hcl : IsClosed {t : ℝ | F₁ (g * dmat t) = F₂ (g * dmat t)} :=
    isClosed_eq (h₁.comp (continuous_const.mul continuous_dmat))
      (h₂.comp (continuous_const.mul continuous_dmat))
  have hsub : Ioo 0 π ⊆ {t : ℝ | F₁ (g * dmat t) = F₂ (g * dmat t)} := by
    intro t ht
    refine h _ ?_
    rw [suTau_mul_dmat, him, zero_mul, sub_zero]
    have hc1 : Real.cos t < 1 := by
      rw [← Real.cos_zero]; exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl ht.2.le ht.1
    have hc2 : -1 < Real.cos t := by
      rw [← Real.cos_pi]; exact Real.cos_lt_cos_of_nonneg_of_le_pi ht.1.le le_rfl ht.2
    have hre' : ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re = 1
        ∨ ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re = -1 := by
      have : (((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re - 1) * (((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re + 1) = 0 := by
        nlinarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    rcases hre' with h | h <;> rw [h] <;> constructor <;> linarith
  have h0 : (0 : ℝ) ∈ closure (Ioo 0 π) := by
    rw [closure_Ioo Real.pi_pos.ne]; exact ⟨le_rfl, Real.pi_pos.le⟩
  have := (hcl.closure_subset_iff.mpr hsub) h0
  simpa [dmat_zero] using this

end MassGap.SU2DiskLaw

#print axioms MassGap.SU2DiskLaw.probHaar_eq_nu
#print axioms MassGap.SU2DiskLaw.lintegral_ball
#print axioms MassGap.SU2DiskLaw.conv_eq_ellInt
#print axioms MassGap.SU2DiskLaw.convT_eq_pi_conv
#print axioms MassGap.SU2DiskLaw.eq_of_eq_on_Ioo
