import Mathlib

/-!
# MassGap.ConvolutionTransfer —the `SU(2)` class convolution carries likelihood-ratio order against the flat Gaussian, by a score identity, a reflection and the spherical projection inequality; the Migdal–Kadanoff step against the flat Gaussian, its only open input the projection gain

The convolution transfer is: `w_k⁴` LR-wider than a reference gives `w_{k+1}` LR-wider than the reference at
four times the time. Through TP₂ kernels that would fail for powers. This module proves the transfer with no
TP₂, against the flat (Lie-algebra) Gaussian `G_c(ψ) = e^{−ψ²/4c}`.

## What is proved

* **The spherical projection inequality** (`sphere_proj_gap`, from `capF_concaveOn` and `curvGap_nonneg`). For unit
  quaternions at angles `a, b ∈ [0, π]` whose axes have cosine `γ`, with `cos ψ = cos a cos b − γ sin a sin b` the
  angle of the product, `(a n_X + b n_K)·(sin ψ n_{XK}) + sin²a sin²b (1 − γ²)/3 ≤ ψ sin ψ`. In flat space the left
  side is `|x + k|²`; on `S³` the sum of two Lie-algebra logarithms projects onto the axis of the product by at most
  the product's angle. The proof: `z ↦ arccos z √(1 − z²) + z²/3` is concave on `[−1, 1]` (its slope in `ψ` has
  derivative `(ψ − sin ψ cos ψ − (2/3) sin³ψ)/sin²ψ ≥ 0`), the left side is affine in `γ`, and the endpoints
  `γ = ±1` are the commuting cases.
* **The ellipse picture** (`ellSet`, `ellLo`, `ellHi`, `ellSet_swap`, `ell_swap`, `ellInt`, `ellInt_mono`). In
  `t = cos a`, `y = cos b` the Haar measure of the pairs `(X, X⁻¹g)` is uniform on the ellipse
  `E_ψ = {(y − t cos ψ)² ≤ (1 − t²) sin²ψ}`, symmetric in `(t, y)`. For `u = U ∘ cos`, the class convolution
  `u ⋆ u` at `ψ` is `ellConv U ψ / sin ψ` with `ellConv U ψ = ∫∫_{E_ψ} U(t) U(y)`.
* **The score identity** (`hasDerivAt_ellConv`, `ibp_slice`, `hasDerivAt_convQuot`). `C(ψ) = ellConv U ψ / sin ψ`
  has derivative `bulkB/sin²ψ`, `bulkB = ∫∫_{E_ψ} U(t) U′(y)(y cos ψ − t)`: the log-slope of `u ⋆ u` at `g` is the
  bridge average of `ℓ_u(b) cos θ_g`.
* **The score bound** (`bulkB_nonpos`, `neg_bulkB_le_proj`, `gramInt_div_three_le_projDef`, `neg_bulkB_le`). For `U`
  non-decreasing (a decreasing class weight), the slice moment at fixed `t` is `≥ 0` (`slice_moment_nonneg`: reflect
  the axis across the plane orthogonal to `g`'s), so `bulkB ≤ 0`. With the LR hypothesis
  `U′(y)√(1 − y²) ≤ arccos y · U(y)/(2c)`, the swap of `E_ψ` and the bracket on `E_ψ` (`ell_bracket_le`, the
  projection inequality in these coordinates) give `−bulkB ≤ (ψ sin ψ · ellConv − Γ/3)/(4c)`, `Γ` the Gram integral.
* **The transfer for one convolution** (`convQuot_lrWider_flat_two`, `convQuot_lrWider_flat`, `convQuot_antitoneOn`,
  `ellConv_pos`). `u` decreasing and LR-wider than `G_c` give `u ⋆ u` decreasing and LR-wider than `G_{2c}`; if the
  projection deficit `projDef` is a fraction `κ` of `ψ sin ψ · ellConv`, LR-wider than `G_{2c/(1−κ)}`.
* **The Migdal–Kadanoff step** (`FlatAdmissible`, `admissible_pow_four`, `convT_bounds`, `admissible_of_convT`,
  `mk_step_flat`). The power step is exact, `G_a⁴ = G_{a/4}`. The fourfold convolution is two self-convolutions. With
  `FlatGain κ₀` in the first, admissible at `a` goes to admissible at `refFlat κ₀ a = a/(1 − κ₀ min(a/4, 1))`.
* **The entry** (`wilson_admissible`): `t ↦ e^{βt}`, i.e. `e^{β cos ψ}`, is admissible at `1/(2β)`, from
  `sin ψ ≤ ψ`.
* **The reference sequence** (`le_refFlat`). `a_{k+1} = refFlat κ₀ a_k` satisfies
  `a_{k+1} ≥ a_k + b a_k²` below `θ`, with `b = (κ₀/4) min(1, 4/θ)`.

## What is not proved here

* `FlatGain κ₀` (a `def`): the projection deficit of every weight admissible at `c` is at least
  `κ₀ min(c, 1) · ψ sin ψ · ellConv` at every angle. It is a hypothesis of `mk_step_flat`.
* The chain's members are taken `C¹` in `cos ψ` up to `±1`, as hypotheses.
* The value of `D(G_θ)`; `D(G_θ) ≥ 4` needs `θ ≳ 4 · 10⁴`.

DERIVED (module-wide): `1/3` is half the strong-concavity modulus `2/3` of `ψ sin ψ` in `z = cos ψ`, from
`ψ − sin ψ cos ψ ≥ (2/3) sin³ψ`; `4` is `m = 2^{d−2}` at `d = 4`; `2c` and `4c` are the times of one and two
self-convolutions, `8c = 4 · 2c`. CHOSEN: `κ₀ ≤ 1/2` keeps `1 − κ₀ min(a/4, 1) ≥ 1/2`; any bound below `1` serves.
-/

noncomputable section

namespace MassGap.ConvolutionTransfer

open Real Set MeasureTheory

/-! ## 1. The spherical projection inequality -/

section Sphere

/-- `ψ − sin ψ cos ψ − (2/3) sin³ψ ≥ 0` on `[0, π]`: it vanishes at `0` and its derivative is
`2 sin²ψ (1 − cos ψ)`. -/
theorem curvGap_nonneg {ψ : ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ π) :
    0 ≤ ψ - sin ψ * cos ψ - 2 / 3 * sin ψ ^ 3 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => x - sin x * cos x - 2 / 3 * sin x ^ 3)
      (2 * sin x ^ 2 * (1 - cos x)) x := by
    intro x
    have := ((hasDerivAt_id' x).sub ((hasDerivAt_sin x).mul (hasDerivAt_cos x))).sub
      (((hasDerivAt_sin x).pow 3).const_mul (2 / 3))
    refine this.congr_deriv ?_
    norm_num
    nlinarith [sin_sq_add_cos_sq x]
  have hmono : MonotoneOn (fun x : ℝ => x - sin x * cos x - 2 / 3 * sin x ^ 3) (Icc 0 π) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 π)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt) fun x _ => ?_
    rw [(hd x).deriv]
    have := cos_le_one x
    have : 0 ≤ 1 - cos x := by linarith
    positivity
  have := hmono ⟨le_refl 0, pi_pos.le⟩ ⟨h0, h1⟩ h0
  simpa using this

/-- The slope `D(ψ) = −1 − ψ cot ψ + (2/3) cos ψ`; `D ∘ arccos` is the derivative of
`z ↦ arccos z · √(1 − z²) + z²/3`. DERIVED: `2/3` the derivative of `z²/3` in `z`, the strong-concavity
modulus of `ψ sin ψ` in `z = cos ψ` (`ψ − sin ψ cos ψ ≥ (2/3) sin³ψ`). -/
def slopeD (ψ : ℝ) : ℝ := -1 - ψ * cos ψ / sin ψ + 2 / 3 * cos ψ

theorem hasDerivAt_slopeD {ψ : ℝ} (hψ : ψ ∈ Ioo 0 π) :
    HasDerivAt slopeD ((ψ - sin ψ * cos ψ - 2 / 3 * sin ψ ^ 3) / sin ψ ^ 2) ψ := by
  have hs : sin ψ ≠ 0 := (sin_pos_of_pos_of_lt_pi hψ.1 hψ.2).ne'
  have h := ((hasDerivAt_const ψ (-1 : ℝ)).sub
    (((hasDerivAt_id' ψ).mul (hasDerivAt_cos ψ)).div (hasDerivAt_sin ψ) hs)).add
    ((hasDerivAt_cos ψ).const_mul (2 / 3 : ℝ))
  have hN : -((1 * cos ψ + ψ * -sin ψ) * sin ψ - ψ * cos ψ * cos ψ) = ψ - sin ψ * cos ψ := by
    linear_combination ψ * sin_sq_add_cos_sq ψ
  have e : (0 : ℝ) - ((1 * cos ψ + ψ * -sin ψ) * sin ψ - ψ * cos ψ * cos ψ) / sin ψ ^ 2
      + 2 / 3 * -sin ψ
      = (-((1 * cos ψ + ψ * -sin ψ) * sin ψ - ψ * cos ψ * cos ψ) - 2 / 3 * sin ψ ^ 3)
        / sin ψ ^ 2 := by
    field_simp
    ring
  rw [hN] at e
  unfold slopeD
  exact h.congr_deriv e

theorem slopeD_monotoneOn : MonotoneOn slopeD (Ioo 0 π) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioo 0 π)
    (fun x hx => (hasDerivAt_slopeD hx).continuousAt.continuousWithinAt)
    (fun x hx => (hasDerivAt_slopeD (by rwa [interior_Ioo] at hx)).differentiableAt.differentiableWithinAt)
    fun x hx => ?_
  rw [interior_Ioo] at hx
  rw [(hasDerivAt_slopeD hx).deriv]
  exact div_nonneg (curvGap_nonneg hx.1.le hx.2.le) (sq_nonneg _)

/-- `F(z) = arccos z · √(1 − z²) + z²/3`, i.e. `ψ sin ψ + cos²ψ/3` at `z = cos ψ`. DERIVED: `1/3` half the
strong-concavity modulus `2/3` of `ψ sin ψ` in `z = cos ψ`, so `F` stays concave. -/
def capF (z : ℝ) : ℝ := arccos z * √(1 - z ^ 2) + z ^ 2 / 3

theorem hasDerivAt_capF {z : ℝ} (hz : z ∈ Ioo (-1) 1) :
    HasDerivAt capF (slopeD (arccos z)) z := by
  have h1 : z ≠ -1 := hz.1.ne'
  have h2 : z ≠ 1 := hz.2.ne
  have hw : 0 < 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  have hf : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * z)) z :=
    ((hasDerivAt_pow 2 z).const_sub 1).congr_deriv (by norm_num)
  have hp : HasDerivAt (fun y : ℝ => y ^ 2 / 3) (2 * z / 3) z :=
    ((hasDerivAt_pow 2 z).div_const 3).congr_deriv (by norm_num)
  have h := ((hasDerivAt_arccos h1 h2).mul (hf.sqrt hw.ne')).add hp
  have hsq : 0 < √(1 - z ^ 2) := Real.sqrt_pos.2 hw
  have e : -(1 / √(1 - z ^ 2)) * √(1 - z ^ 2) + arccos z * (-(2 * z) / (2 * √(1 - z ^ 2)))
      + 2 * z / 3 = slopeD (arccos z) := by
    unfold slopeD
    rw [cos_arccos hz.1.le hz.2.le, sin_arccos]
    field_simp
    ring
  unfold capF
  exact h.congr_deriv e

theorem capF_concaveOn : ConcaveOn ℝ (Icc (-1) 1) capF := by
  refine AntitoneOn.concaveOn_of_deriv (convex_Icc (-1) 1) ?_ ?_ ?_
  · unfold capF
    exact (continuous_arccos.mul ((continuous_const.sub (continuous_pow 2)).sqrt)).add
      ((continuous_pow 2).div_const 3) |>.continuousOn
  · rw [interior_Icc]
    exact fun z hz => (hasDerivAt_capF hz).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro x hx y hy hxy
    rw [(hasDerivAt_capF hx).deriv, (hasDerivAt_capF hy).deriv]
    have hmem : ∀ w ∈ Ioo (-1 : ℝ) 1, arccos w ∈ Ioo 0 π := fun w hw =>
      ⟨arccos_pos.2 hw.2, arccos_lt_pi.2 hw.1⟩
    exact slopeD_monotoneOn (hmem y hy) (hmem x hx) (arccos_le_arccos hxy)

/-- `arccos (cos x) · √(1 − cos² x) = x sin x` for `|x| ≤ π`. -/
theorem arccos_cos_mul_sqrt {x : ℝ} (h1 : -π ≤ x) (h2 : x ≤ π) :
    arccos (cos x) * √(1 - cos x ^ 2) = x * sin x := by
  rw [← sin_arccos]
  have h : arccos (cos x) = |x| := by
    rw [← cos_abs]
    exact arccos_cos (abs_nonneg x) (abs_le.2 ⟨h1, h2⟩)
  rw [h]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, sin_neg]
    ring

/-- `x sin x ≤ arccos (cos x) · √(1 − cos² x)` for `0 ≤ x ≤ 2π`. -/
theorem mul_sin_le_arccos_cos {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 2 * π) :
    x * sin x ≤ arccos (cos x) * √(1 - cos x ^ 2) := by
  rcases le_total x π with hx | hx
  · rw [arccos_cos_mul_sqrt (by linarith [pi_pos]) hx]
  · have hs : sin x ≤ 0 := by
      rw [← sin_sub_two_pi]
      exact sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
    have : x * sin x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1 hs
    exact this.trans (mul_nonneg (arccos_nonneg _) (Real.sqrt_nonneg _))

/-- **The spherical projection inequality.** Let `X, K` be unit quaternions at angles `a, b ∈ [0, π]`
with axes at cosine `γ`, and let `ψ` be the angle of `XK`, `cos ψ = cos a cos b − γ sin a sin b`. Then
`(a n_X + b n_K) · (sin ψ n_{XK}) + sin²a sin²b (1 − γ²)/3 ≤ ψ sin ψ`.
In the flat limit the left side is `(x + k)·(x + k)`, so this is the curvature of `S³` acting on the sum
of two Lie-algebra logarithms; the Gram term `sin²a sin²b (1 − γ²)` is the strong-concavity margin. -/
theorem sphere_proj_gap {a b γ : ℝ} (ha0 : 0 ≤ a) (haπ : a ≤ π) (hb0 : 0 ≤ b) (hbπ : b ≤ π)
    (hγ1 : -1 ≤ γ) (hγ2 : γ ≤ 1) :
    a * sin a * cos b + b * cos a * sin b + γ * (a * cos a * sin b + b * sin a * cos b)
      + sin a ^ 2 * sin b ^ 2 * (1 - γ ^ 2) / 3
      ≤ arccos (cos a * cos b - γ * sin a * sin b)
          * √(1 - (cos a * cos b - γ * sin a * sin b) ^ 2) := by
  have hm : cos (a - b) ∈ Icc (-1 : ℝ) 1 := ⟨neg_one_le_cos _, cos_le_one _⟩
  have hp : cos (a + b) ∈ Icc (-1 : ℝ) 1 := ⟨neg_one_le_cos _, cos_le_one _⟩
  have hw1 : 0 ≤ (1 - γ) / 2 := by linarith
  have hw2 : 0 ≤ (1 + γ) / 2 := by linarith
  have hc := capF_concaveOn.2 hm hp hw1 hw2 (by ring)
  simp only [smul_eq_mul] at hc
  have hz : (1 - γ) / 2 * cos (a - b) + (1 + γ) / 2 * cos (a + b)
      = cos a * cos b - γ * sin a * sin b := by
    rw [cos_sub, cos_add]; ring
  rw [hz] at hc
  unfold capF at hc
  have e1 := arccos_cos_mul_sqrt (x := a - b) (by linarith) (by linarith)
  have e2 := mul_sin_le_arccos_cos (x := a + b) (by linarith) (by linarith)
  have key : (1 - γ) / 2 * ((a - b) * sin (a - b) + cos (a - b) ^ 2 / 3)
      + (1 + γ) / 2 * ((a + b) * sin (a + b) + cos (a + b) ^ 2 / 3)
      - (cos a * cos b - γ * sin a * sin b) ^ 2 / 3
      = a * sin a * cos b + b * cos a * sin b + γ * (a * cos a * sin b + b * sin a * cos b)
        + sin a ^ 2 * sin b ^ 2 * (1 - γ ^ 2) / 3 := by
    rw [sin_sub, sin_add, cos_sub, cos_add]
    ring
  rw [e1] at hc
  nlinarith [mul_le_mul_of_nonneg_left e2 hw2]

end Sphere

/-! ## 2. The ellipse picture: the region, its symmetry, the slice moment -/

section Ellipse

/-- The ellipse `E_ψ` in the `(t, y) = (cos a, cos b)` plane: `t ∈ [−1, 1]` and
`(y − t cos ψ)² ≤ (1 − t²) sin²ψ`. Haar measure on `SU(2)` pushed to `(cos a, cos b)`, with `a` the angle of
`X` and `b` that of `X⁻¹ g` at `g` of angle `ψ`, is uniform on `E_ψ` with density `1/sin ψ`. -/
def ellSet (ψ : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc (-1 : ℝ) 1 ∧ (p.2 - p.1 * cos ψ) ^ 2 ≤ (1 - p.1 ^ 2) * sin ψ ^ 2}

/-- The lower end of the slice of `E_ψ` at `t`: `cos (a + ψ)` for `t = cos a`. -/
def ellLo (ψ t : ℝ) : ℝ := t * cos ψ - √(1 - t ^ 2) * sin ψ

/-- The upper end of the slice of `E_ψ` at `t`: `cos (a − ψ)` for `t = cos a`. -/
def ellHi (ψ t : ℝ) : ℝ := t * cos ψ + √(1 - t ^ 2) * sin ψ

theorem measurableSet_ellSet (ψ : ℝ) : MeasurableSet (ellSet ψ) :=
  (measurable_fst measurableSet_Icc).inter (measurableSet_le
    (by fun_prop : Continuous fun p : ℝ × ℝ => (p.2 - p.1 * cos ψ) ^ 2).measurable
    (by fun_prop : Continuous fun p : ℝ × ℝ => (1 - p.1 ^ 2) * sin ψ ^ 2).measurable)

theorem sqrt_one_sub_sq_sq {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : √(1 - t ^ 2) ^ 2 = 1 - t ^ 2 :=
  Real.sq_sqrt (by nlinarith [ht.1, ht.2])

theorem mem_ellSet_iff {ψ t y : ℝ} (hs : 0 ≤ sin ψ) (ht : t ∈ Icc (-1 : ℝ) 1) :
    (t, y) ∈ ellSet ψ ↔ y ∈ Icc (ellLo ψ t) (ellHi ψ t) := by
  have hw : 0 ≤ √(1 - t ^ 2) * sin ψ := mul_nonneg (Real.sqrt_nonneg _) hs
  have hsq : (√(1 - t ^ 2) * sin ψ) ^ 2 = (1 - t ^ 2) * sin ψ ^ 2 := by
    rw [mul_pow, sqrt_one_sub_sq_sq ht]
  simp only [ellSet, Set.mem_setOf_eq, ellLo, ellHi, Set.mem_Icc]
  constructor
  · rintro ⟨-, h⟩
    rw [← hsq] at h
    obtain ⟨h1, h2⟩ := abs_le_of_sq_le_sq' h hw
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    refine ⟨⟨ht.1, ht.2⟩, ?_⟩
    rw [← hsq]
    exact sq_le_sq' (by linarith) (by linarith)

/-- **`E_ψ` is symmetric** under `(t, y) ↦ (y, t)`: the Gram determinant of `(1, cos a, cos b, cos ψ)` is. -/
theorem ellSet_swap {ψ t y : ℝ} (h : (t, y) ∈ ellSet ψ) : (y, t) ∈ ellSet ψ := by
  obtain ⟨⟨ht1, ht2⟩, h⟩ := h
  have hz := sin_sq_add_cos_sq ψ
  have e : (t - y * cos ψ) ^ 2 - (1 - y ^ 2) * sin ψ ^ 2
      = (y - t * cos ψ) ^ 2 - (1 - t ^ 2) * sin ψ ^ 2 := by
    linear_combination (y ^ 2 - t ^ 2) * hz
  have hsym : (t - y * cos ψ) ^ 2 ≤ (1 - y ^ 2) * sin ψ ^ 2 := by linarith
  have hy : y ^ 2 ≤ 1 := by
    rcases eq_or_ne (sin ψ) 0 with h0 | h0
    · rw [h0] at h
      have h1 : y - t * cos ψ = 0 := by nlinarith [sq_nonneg (y - t * cos ψ)]
      have hc : cos ψ ^ 2 = 1 := by rw [h0] at hz; linarith
      have : y = t * cos ψ := by linarith
      rw [this, mul_pow, hc, mul_one]
      nlinarith
    · have hs2 : 0 < sin ψ ^ 2 := by positivity
      nlinarith [sq_nonneg (t - y * cos ψ)]
  obtain ⟨hy1, hy2⟩ := abs_le_of_sq_le_sq' (by simpa using hy : y ^ 2 ≤ 1 ^ 2) zero_le_one
  exact ⟨⟨hy1, hy2⟩, hsym⟩

theorem ellSet_subset (ψ : ℝ) : ellSet ψ ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := fun p hp =>
  ⟨hp.1, (ellSet_swap (t := p.1) (y := p.2) hp).1⟩

theorem ellSet_measure_lt_top (ψ : ℝ) : (volume.prod volume) (ellSet ψ) < ⊤ := by
  refine (measure_mono (ellSet_subset ψ)).trans_lt ?_
  rw [Measure.prod_prod]
  exact ENNReal.mul_lt_top measure_Icc_lt_top measure_Icc_lt_top

/-- **Swap over `E_ψ`.** The `t`-sliced and the `y`-sliced iterated integrals over the ellipse agree. -/
theorem ell_swap {ψ : ℝ} (hs : 0 ≤ sin ψ) {F : ℝ → ℝ → ℝ}
    (hF : AEStronglyMeasurable (Function.uncurry F) ((volume.prod volume).restrict (ellSet ψ)))
    {M : ℝ} (hM : ∀ p ∈ ellSet ψ, |F p.1 p.2| ≤ M) :
    ∫ t in (-1 : ℝ)..1, ∫ y in ellLo ψ t..ellHi ψ t, F t y
      = ∫ y in (-1 : ℝ)..1, ∫ t in ellLo ψ y..ellHi ψ y, F t y := by
  set g : ℝ × ℝ → ℝ := (ellSet ψ).indicator (Function.uncurry F) with hg
  have hint : Integrable g (volume.prod volume) := by
    rw [hg, integrable_indicator_iff (measurableSet_ellSet ψ)]
    refine IntegrableOn.of_bound (ellSet_measure_lt_top ψ) hF M ?_
    exact ae_restrict_of_forall_mem (measurableSet_ellSet ψ) fun p hp => by
      rw [Real.norm_eq_abs]; exact hM p hp
  have hlohi : ∀ t ∈ Icc (-1 : ℝ) 1, ellLo ψ t ≤ ellHi ψ t := fun t _ => by
    unfold ellLo ellHi
    have := mul_nonneg (Real.sqrt_nonneg (1 - t ^ 2)) hs
    linarith
  have inner1 : ∀ t ∈ Icc (-1 : ℝ) 1,
      ∫ y in ellLo ψ t..ellHi ψ t, F t y = ∫ y, g (t, y) := by
    intro t ht
    have e : (fun y => g (t, y)) = (Icc (ellLo ψ t) (ellHi ψ t)).indicator (F t) := by
      funext y
      by_cases h : (t, y) ∈ ellSet ψ
      · rw [hg, Set.indicator_of_mem h, Set.indicator_of_mem ((mem_ellSet_iff hs ht).1 h)]
        rfl
      · rw [hg, Set.indicator_of_notMem h,
          Set.indicator_of_notMem (fun h' => h ((mem_ellSet_iff hs ht).2 h'))]
    rw [e, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (hlohi t ht)]
  have inner2 : ∀ y ∈ Icc (-1 : ℝ) 1,
      ∫ t in ellLo ψ y..ellHi ψ y, F t y = ∫ t, g (t, y) := by
    intro y hy
    have e : (fun t => g (t, y)) = (Icc (ellLo ψ y) (ellHi ψ y)).indicator (fun t => F t y) := by
      funext t
      have hiff : (t, y) ∈ ellSet ψ ↔ t ∈ Icc (ellLo ψ y) (ellHi ψ y) :=
        ⟨fun h => (mem_ellSet_iff hs hy).1 (ellSet_swap h),
          fun h => ellSet_swap ((mem_ellSet_iff hs hy).2 h)⟩
      by_cases h : (t, y) ∈ ellSet ψ
      · rw [hg, Set.indicator_of_mem h, Set.indicator_of_mem (hiff.1 h)]
        rfl
      · rw [hg, Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hiff.2 h'))]
    rw [e, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (hlohi y hy)]
  have out1 : ∀ t ∉ Icc (-1 : ℝ) 1, ∫ y, g (t, y) = 0 := by
    intro t ht
    have : (fun y => g (t, y)) = fun _ => 0 := by
      funext y
      simp only [hg]
      exact Set.indicator_of_notMem (fun h => ht h.1) _
    rw [this, integral_zero]
  have out2 : ∀ y ∉ Icc (-1 : ℝ) 1, ∫ t, g (t, y) = 0 := by
    intro y hy
    have : (fun t => g (t, y)) = fun _ => 0 := by
      funext t
      simp only [hg]
      exact Set.indicator_of_notMem (fun h => hy (ellSet_swap h).1) _
    rw [this, integral_zero]
  have L : ∫ t in (-1 : ℝ)..1, ∫ y in ellLo ψ t..ellHi ψ t, F t y = ∫ t, ∫ y, g (t, y) := by
    rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero out1]
    exact setIntegral_congr_fun measurableSet_Icc inner1
  have R : ∫ y in (-1 : ℝ)..1, ∫ t in ellLo ψ y..ellHi ψ y, F t y = ∫ y, ∫ t, g (t, y) := by
    rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero out2]
    exact setIntegral_congr_fun measurableSet_Icc inner2
  rw [L, R]
  exact integral_integral_swap (f := fun t y => g (t, y)) hint

/-- **The slice moment.** For `U` non-decreasing on `[m − w, m + w]`, `∫ U(x)(x − m) ≥ 0` over that interval:
pair `m + r` with `m − r`. -/
theorem slice_moment_nonneg {U : ℝ → ℝ} (hU : Continuous U) {m w : ℝ} (hw : 0 ≤ w)
    (hmono : MonotoneOn U (Icc (m - w) (m + w))) :
    0 ≤ ∫ x in (m - w)..(m + w), U x * (x - m) := by
  have hci : ∀ a b : ℝ, IntervalIntegrable (fun r => U (r + m) * r) volume a b := fun a b =>
    ((hU.comp (continuous_add_const m)).mul continuous_id).intervalIntegrable a b
  have e1 : ∫ x in (m - w)..(m + w), U x * (x - m) = ∫ r in (-w)..w, U (r + m) * r := by
    rw [show m - w = -w + m by ring, show m + w = w + m by ring,
      ← intervalIntegral.integral_comp_add_right (fun x => U x * (x - m)) m]
    congr 1
    funext r
    ring
  have hneg : IntervalIntegrable (fun r => U (-r + m) * -r) volume 0 w :=
    ((hU.comp ((continuous_neg).add continuous_const)).mul continuous_neg).intervalIntegrable _ _
  have e3 : ∫ r in (-w)..0, U (r + m) * r = ∫ r in (0 : ℝ)..w, U (-r + m) * -r := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := w) (fun r => U (r + m) * r)
    simp only [neg_zero] at this
    rw [← this]
  have e2 : ∫ r in (-w)..w, U (r + m) * r
      = ∫ r in (0 : ℝ)..w, (U (r + m) - U (-r + m)) * r := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hci (-w) 0) (hci 0 w), e3,
      ← intervalIntegral.integral_add hneg (hci 0 w)]
    congr 1
    funext r
    ring
  rw [e1, e2]
  refine intervalIntegral.integral_nonneg hw fun r hr => ?_
  have h1 : -r + m ∈ Icc (m - w) (m + w) := ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have h2 : r + m ∈ Icc (m - w) (m + w) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have := hmono h1 h2 (by linarith [hr.1])
  exact mul_nonneg (by linarith) hr.1

end Ellipse

/-! ## 3. The bracket on the ellipse, and integrals over it -/

section EllInt

/-- The Gram determinant of `(cos a, cos b, cos ψ)`: `(1 − t²)(1 − y²) − (t y − cos ψ)²`. -/
def gram (ψ t y : ℝ) : ℝ := (1 - t ^ 2) * (1 - y ^ 2) - (t * y - cos ψ) ^ 2

theorem gram_eq (ψ t y : ℝ) :
    gram ψ t y = (1 - t ^ 2) * sin ψ ^ 2 - (y - t * cos ψ) ^ 2 := by
  unfold gram
  linear_combination (-(1 - t ^ 2)) * sin_sq_add_cos_sq ψ

theorem gram_nonneg {ψ t y : ℝ} (h : (t, y) ∈ ellSet ψ) : 0 ≤ gram ψ t y := by
  rw [gram_eq]; linarith [h.2]

/-- **The bracket on `E_ψ`.** With `t = cos a`, `y = cos b`:
`a (y − t cos ψ)/sin a + b (t − y cos ψ)/sin b + Gram/3 ≤ ψ sin ψ`. This is `sphere_proj_gap` in the
coordinates of the ellipse: the two terms are `a sin ψ cos θ_e` and `b sin ψ cos θ_g`, the projections of the
two sides of the spherical triangle `(e, X, g)` on the third. -/
theorem ell_bracket_le {ψ t y : ℝ} (hψ0 : 0 ≤ ψ) (hψπ : ψ ≤ π) (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hy : y ∈ Ioo (-1 : ℝ) 1) (hE : (t, y) ∈ ellSet ψ) :
    arccos t * ((y - t * cos ψ) / √(1 - t ^ 2)) + arccos y * ((t - y * cos ψ) / √(1 - y ^ 2))
      + gram ψ t y / 3 ≤ ψ * sin ψ := by
  set sa := √(1 - t ^ 2) with hsa
  set sb := √(1 - y ^ 2) with hsb
  have ht2 : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hy2 : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
  have hsa0 : 0 < sa := Real.sqrt_pos.2 ht2
  have hsb0 : 0 < sb := Real.sqrt_pos.2 hy2
  have hsa2 : sa ^ 2 = 1 - t ^ 2 := Real.sq_sqrt ht2.le
  have hsb2 : sb ^ 2 = 1 - y ^ 2 := Real.sq_sqrt hy2.le
  set γ := (t * y - cos ψ) / (sa * sb) with hγ
  have hγsb : γ * (sa * sb) = t * y - cos ψ := by rw [hγ]; field_simp
  have hG := gram_nonneg hE
  have hγsq : γ ^ 2 ≤ 1 := by
    have h1 : (γ * (sa * sb)) ^ 2 ≤ (sa * sb) ^ 2 := by
      rw [hγsb, mul_pow, hsa2, hsb2]; unfold gram at hG; linarith
    have hp : 0 < (sa * sb) ^ 2 := by positivity
    rw [mul_pow] at h1
    nlinarith
  obtain ⟨hγ1, hγ2⟩ := abs_le_of_sq_le_sq' (by simpa using hγsq : γ ^ 2 ≤ 1 ^ 2) zero_le_one
  have key := sphere_proj_gap (a := arccos t) (b := arccos y) (γ := γ) (arccos_nonneg _)
    (arccos_le_pi _) (arccos_nonneg _) (arccos_le_pi _) hγ1 hγ2
  rw [cos_arccos ht.1.le ht.2.le, cos_arccos hy.1.le hy.2.le, sin_arccos, sin_arccos] at key
  have hz : t * y - γ * sa * sb = cos ψ := by linear_combination (-1 : ℝ) * hγsb
  rw [hz, arccos_cos_mul_sqrt (by linarith [pi_pos]) hψπ] at key
  have hA : sa * y + γ * t * sb = (y - t * cos ψ) / sa := by
    rw [eq_div_iff hsa0.ne']
    linear_combination y * hsa2 + t * hγsb
  have hB : sb * t + γ * y * sa = (t - y * cos ψ) / sb := by
    rw [eq_div_iff hsb0.ne']
    linear_combination t * hsb2 + y * hγsb
  have hC : sa ^ 2 * sb ^ 2 * (1 - γ ^ 2) = gram ψ t y := by
    unfold gram
    rw [← hsa2, ← hsb2]
    linear_combination (-1 : ℝ) * (γ * (sa * sb) + (t * y - cos ψ)) * hγsb
  rw [← hA, ← hB, ← hC]
  linarith [key]

/-- `|(t − y cos ψ)/√(1 − y²)| ≤ sin ψ` on `E_ψ`. -/
theorem abs_ellQ_le {ψ t y : ℝ} (hs : 0 ≤ sin ψ) (hE : (t, y) ∈ ellSet ψ) :
    |(t - y * cos ψ) / √(1 - y ^ 2)| ≤ sin ψ := by
  have hE' := ellSet_swap hE
  have hy : y ∈ Icc (-1 : ℝ) 1 := hE'.1
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (1 - y ^ 2)) with h0 | hpos
  · rw [← h0, div_zero, abs_zero]; exact hs
  · rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have h2 := hE'.2
    simp only at h2
    have hsq : (√(1 - y ^ 2) * sin ψ) ^ 2 = (1 - y ^ 2) * sin ψ ^ 2 := by
      rw [mul_pow, sqrt_one_sub_sq_sq hy]
    rw [← hsq] at h2
    have := abs_le_of_sq_le_sq h2 (mul_nonneg hpos.le hs)
    linarith

/-- Integrands on `E_ψ` that are a.e.-strongly measurable for the restricted product measure and bounded. -/
def EllGood (ψ : ℝ) (F : ℝ → ℝ → ℝ) : Prop :=
  AEStronglyMeasurable (Function.uncurry F) ((volume.prod volume).restrict (ellSet ψ)) ∧
    ∃ M, ∀ p ∈ ellSet ψ, |F p.1 p.2| ≤ M

/-- The integral over `E_ψ`, sliced at fixed `t`. -/
def ellInt (ψ : ℝ) (F : ℝ → ℝ → ℝ) : ℝ := ∫ t in (-1 : ℝ)..1, ∫ y in ellLo ψ t..ellHi ψ t, F t y

theorem EllGood.integrable {ψ : ℝ} {F : ℝ → ℝ → ℝ} (hF : EllGood ψ F) :
    Integrable ((ellSet ψ).indicator (Function.uncurry F)) (volume.prod volume) := by
  obtain ⟨hm, M, hM⟩ := hF
  rw [integrable_indicator_iff (measurableSet_ellSet ψ)]
  refine IntegrableOn.of_bound (ellSet_measure_lt_top ψ) hm M ?_
  exact ae_restrict_of_forall_mem (measurableSet_ellSet ψ) fun p hp => by
    rw [Real.norm_eq_abs]; exact hM p hp

theorem ellInt_eq_prod {ψ : ℝ} (hs : 0 ≤ sin ψ) {F : ℝ → ℝ → ℝ} (hF : EllGood ψ F) :
    ellInt ψ F = ∫ p, (ellSet ψ).indicator (Function.uncurry F) p ∂(volume.prod volume) := by
  set g : ℝ × ℝ → ℝ := (ellSet ψ).indicator (Function.uncurry F) with hg
  have hlohi : ∀ t ∈ Icc (-1 : ℝ) 1, ellLo ψ t ≤ ellHi ψ t := fun t _ => by
    unfold ellLo ellHi
    have := mul_nonneg (Real.sqrt_nonneg (1 - t ^ 2)) hs
    linarith
  have inner1 : ∀ t ∈ Icc (-1 : ℝ) 1,
      ∫ y in ellLo ψ t..ellHi ψ t, F t y = ∫ y, g (t, y) := by
    intro t ht
    have e : (fun y => g (t, y)) = (Icc (ellLo ψ t) (ellHi ψ t)).indicator (F t) := by
      funext y
      by_cases h : (t, y) ∈ ellSet ψ
      · rw [hg, Set.indicator_of_mem h, Set.indicator_of_mem ((mem_ellSet_iff hs ht).1 h)]
        rfl
      · rw [hg, Set.indicator_of_notMem h,
          Set.indicator_of_notMem (fun h' => h ((mem_ellSet_iff hs ht).2 h'))]
    rw [e, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (hlohi t ht)]
  have out1 : ∀ t ∉ Icc (-1 : ℝ) 1, ∫ y, g (t, y) = 0 := by
    intro t ht
    have : (fun y => g (t, y)) = fun _ => 0 := by
      funext y
      simp only [hg]
      exact Set.indicator_of_notMem (fun h => ht h.1) _
    rw [this, integral_zero]
  unfold ellInt
  rw [integral_prod g hF.integrable, intervalIntegral.integral_of_le (by norm_num),
    ← integral_Icc_eq_integral_Ioc, ← setIntegral_eq_integral_of_forall_compl_eq_zero out1]
  exact setIntegral_congr_fun measurableSet_Icc inner1

theorem ellInt_swap {ψ : ℝ} (hs : 0 ≤ sin ψ) {F : ℝ → ℝ → ℝ} (hF : EllGood ψ F) :
    ellInt ψ F = ellInt ψ (fun t y => F y t) :=
  ell_swap hs hF.1 hF.2.choose_spec

theorem EllGood.add {ψ : ℝ} {F G : ℝ → ℝ → ℝ} (hF : EllGood ψ F) (hG : EllGood ψ G) :
    EllGood ψ (fun t y => F t y + G t y) := by
  obtain ⟨hFm, MF, hMF⟩ := hF
  obtain ⟨hGm, MG, hMG⟩ := hG
  refine ⟨hFm.add hGm, MF + MG, fun p hp => ?_⟩
  exact (abs_add_le _ _).trans (add_le_add (hMF p hp) (hMG p hp))

theorem ellInt_add {ψ : ℝ} (hs : 0 ≤ sin ψ) {F G : ℝ → ℝ → ℝ} (hF : EllGood ψ F)
    (hG : EllGood ψ G) : ellInt ψ (fun t y => F t y + G t y) = ellInt ψ F + ellInt ψ G := by
  rw [ellInt_eq_prod hs hF, ellInt_eq_prod hs hG, ellInt_eq_prod hs (hF.add hG),
    ← integral_add hF.integrable hG.integrable]
  congr 1
  funext p
  by_cases h : p ∈ ellSet ψ
  · simp only [Set.indicator_of_mem h]
    rfl
  · simp only [Set.indicator_of_notMem h, add_zero]

theorem ellInt_const_mul {ψ : ℝ} (r : ℝ) (F : ℝ → ℝ → ℝ) :
    ellInt ψ (fun t y => r * F t y) = r * ellInt ψ F := by
  unfold ellInt
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext t
  rw [← intervalIntegral.integral_const_mul]

/-- Almost every point of `ℝ²` has both coordinates different from `±1`. -/
theorem ae_coords_ne : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)),
    p.1 ≠ -1 ∧ p.1 ≠ 1 ∧ p.2 ≠ -1 ∧ p.2 ≠ 1 := by
  have h1 : ∀ a : ℝ, ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)), p.1 ≠ a := by
    intro a
    have : (volume.prod volume : Measure (ℝ × ℝ)) (Prod.fst ⁻¹' {a}) = 0 := by
      rw [← Set.prod_univ, Measure.prod_prod, Real.volume_singleton, zero_mul]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 this] with p hp
    exact fun h => hp h
  have h2 : ∀ a : ℝ, ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)), p.2 ≠ a := by
    intro a
    have : (volume.prod volume : Measure (ℝ × ℝ)) (Prod.snd ⁻¹' {a}) = 0 := by
      rw [← Set.univ_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 this] with p hp
    exact fun h => hp h
  filter_upwards [h1 (-1), h1 1, h2 (-1), h2 1] with p a b c d
  exact ⟨a, b, c, d⟩

/-- **Monotonicity of the integral over `E_ψ`**, from the inequality at interior points of `E_ψ`. -/
theorem ellInt_mono {ψ : ℝ} (hs : 0 ≤ sin ψ) {F G : ℝ → ℝ → ℝ} (hF : EllGood ψ F)
    (hG : EllGood ψ G)
    (h : ∀ t y, (t, y) ∈ ellSet ψ → t ∈ Ioo (-1 : ℝ) 1 → y ∈ Ioo (-1 : ℝ) 1 → F t y ≤ G t y) :
    ellInt ψ F ≤ ellInt ψ G := by
  rw [ellInt_eq_prod hs hF, ellInt_eq_prod hs hG]
  refine integral_mono_ae hF.integrable hG.integrable ?_
  filter_upwards [ae_coords_ne] with p hp
  by_cases hm : p ∈ ellSet ψ
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm]
    have h1 := hm.1
    have h2 := (ellSet_swap (t := p.1) (y := p.2) hm).1
    exact h p.1 p.2 hm ⟨lt_of_le_of_ne h1.1 (Ne.symm hp.1), lt_of_le_of_ne h1.2 hp.2.1⟩
      ⟨lt_of_le_of_ne h2.1 (Ne.symm hp.2.2.1), lt_of_le_of_ne h2.2 hp.2.2.2⟩
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]

/-- The outer function of `ellInt` is interval integrable. -/
theorem ellInt_outer_intervalIntegrable {ψ : ℝ} (hs : 0 ≤ sin ψ) {F : ℝ → ℝ → ℝ}
    (hF : EllGood ψ F) :
    IntervalIntegrable (fun t => ∫ y in ellLo ψ t..ellHi ψ t, F t y) volume (-1) 1 := by
  set g : ℝ × ℝ → ℝ := (ellSet ψ).indicator (Function.uncurry F) with hg
  have hI : Integrable (fun t => ∫ y, g (t, y)) volume := hF.integrable.integral_prod_left
  have hlohi : ∀ t ∈ Icc (-1 : ℝ) 1, ellLo ψ t ≤ ellHi ψ t := fun t _ => by
    unfold ellLo ellHi
    have := mul_nonneg (Real.sqrt_nonneg (1 - t ^ 2)) hs
    linarith
  have inner1 : ∀ t ∈ Icc (-1 : ℝ) 1,
      ∫ y in ellLo ψ t..ellHi ψ t, F t y = ∫ y, g (t, y) := by
    intro t ht
    have e : (fun y => g (t, y)) = (Icc (ellLo ψ t) (ellHi ψ t)).indicator (F t) := by
      funext y
      by_cases h : (t, y) ∈ ellSet ψ
      · rw [hg, Set.indicator_of_mem h, Set.indicator_of_mem ((mem_ellSet_iff hs ht).1 h)]
        rfl
      · rw [hg, Set.indicator_of_notMem h,
          Set.indicator_of_notMem (fun h' => h ((mem_ellSet_iff hs ht).2 h'))]
    rw [e, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (hlohi t ht)]
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
  exact (hI.integrableOn).congr_fun (fun t ht => (inner1 t ht).symm) measurableSet_Icc

end EllInt

/-! ## 4. The convolution on the ellipse and its derivative -/

section Conv

variable {U U' : ℝ → ℝ}

theorem isCompact_ellSet (ψ : ℝ) : IsCompact (ellSet ψ) := by
  have hcl : IsClosed (ellSet ψ) :=
    (isClosed_Icc.preimage continuous_fst).inter (isClosed_le
      (by fun_prop : Continuous fun p : ℝ × ℝ => (p.2 - p.1 * cos ψ) ^ 2)
      (by fun_prop : Continuous fun p : ℝ × ℝ => (1 - p.1 ^ 2) * sin ψ ^ 2))
  exact (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hcl (ellSet_subset ψ)

theorem ellGood_of_continuousOn {ψ : ℝ} {F : ℝ → ℝ → ℝ}
    (h : ContinuousOn (Function.uncurry F) (ellSet ψ)) : EllGood ψ F := by
  refine ⟨h.aestronglyMeasurable (measurableSet_ellSet ψ), ?_⟩
  obtain ⟨M, hM⟩ := (isCompact_ellSet ψ).exists_bound_of_continuousOn h
  exact ⟨M, fun p hp => by have := hM p hp; rwa [Real.norm_eq_abs] at this⟩

theorem ellHi_sq_add {ψ t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ellHi ψ t ^ 2 + (t * sin ψ - √(1 - t ^ 2) * cos ψ) ^ 2 = 1 := by
  unfold ellHi
  linear_combination (t ^ 2 + √(1 - t ^ 2) ^ 2) * sin_sq_add_cos_sq ψ + sqrt_one_sub_sq_sq ht

theorem ellLo_sq_add {ψ t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ellLo ψ t ^ 2 + (t * sin ψ + √(1 - t ^ 2) * cos ψ) ^ 2 = 1 := by
  unfold ellLo
  linear_combination (t ^ 2 + √(1 - t ^ 2) ^ 2) * sin_sq_add_cos_sq ψ + sqrt_one_sub_sq_sq ht

theorem ellHi_mem {ψ t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : ellHi ψ t ∈ Icc (-1 : ℝ) 1 := by
  have h := ellHi_sq_add (ψ := ψ) ht
  have h2 : ellHi ψ t ^ 2 ≤ 1 ^ 2 := by nlinarith [sq_nonneg (t * sin ψ - √(1 - t ^ 2) * cos ψ)]
  exact abs_le_of_sq_le_sq' h2 zero_le_one

theorem ellLo_mem {ψ t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : ellLo ψ t ∈ Icc (-1 : ℝ) 1 := by
  have h := ellLo_sq_add (ψ := ψ) ht
  have h2 : ellLo ψ t ^ 2 ≤ 1 ^ 2 := by nlinarith [sq_nonneg (t * sin ψ + √(1 - t ^ 2) * cos ψ)]
  exact abs_le_of_sq_le_sq' h2 zero_le_one

/-- `∂_ψ cos (a − ψ)` at `t = cos a`. -/
def hiD (ψ t : ℝ) : ℝ := t * -sin ψ + √(1 - t ^ 2) * cos ψ

/-- `∂_ψ cos (a + ψ)` at `t = cos a`. -/
def loD (ψ t : ℝ) : ℝ := t * -sin ψ - √(1 - t ^ 2) * cos ψ

theorem hasDerivAt_ellHi (ψ t : ℝ) : HasDerivAt (fun x => ellHi x t) (hiD ψ t) ψ := by
  unfold ellHi hiD
  exact ((hasDerivAt_cos ψ).const_mul t).add ((hasDerivAt_sin ψ).const_mul _)

theorem hasDerivAt_ellLo (ψ t : ℝ) : HasDerivAt (fun x => ellLo x t) (loD ψ t) ψ := by
  unfold ellLo loD
  exact ((hasDerivAt_cos ψ).const_mul t).sub ((hasDerivAt_sin ψ).const_mul _)

theorem abs_hiD_le {ψ t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : |hiD ψ t| ≤ 1 := by
  have h := ellHi_sq_add (ψ := ψ) ht
  have : hiD ψ t ^ 2 ≤ 1 ^ 2 := by
    unfold hiD; nlinarith [sq_nonneg (ellHi ψ t)]
  exact abs_le_of_sq_le_sq this zero_le_one

theorem abs_loD_le {ψ t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : |loD ψ t| ≤ 1 := by
  have h := ellLo_sq_add (ψ := ψ) ht
  have : loD ψ t ^ 2 ≤ 1 ^ 2 := by
    unfold loD; nlinarith [sq_nonneg (ellLo ψ t)]
  exact abs_le_of_sq_le_sq this zero_le_one

/-- The self-convolution on the ellipse, `∫∫_{E_ψ} U(t) U(y)`. For `u = U ∘ cos`, `ellConv U ψ / sin ψ` is the
`SU(2)` class convolution `u ⋆ u` at angle `ψ` relative to Haar, times `π`. -/
def ellConv (U : ℝ → ℝ) (ψ : ℝ) : ℝ := ellInt ψ (fun t y => U t * U y)

theorem ellConv_eq (hUc : Continuous U) (ψ : ℝ) :
    ellConv U ψ = ∫ t in (-1 : ℝ)..1,
      U t * ((∫ y in (0 : ℝ)..ellHi ψ t, U y) - ∫ y in (0 : ℝ)..ellLo ψ t, U y) := by
  unfold ellConv ellInt
  congr 1
  funext t
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_interval_sub_left
    (hUc.intervalIntegrable _ _) (hUc.intervalIntegrable _ _)]

/-- **The derivative of the convolution in the angle**, in boundary form. -/
theorem hasDerivAt_ellConv (hUc : Continuous U) (ψ₀ : ℝ) :
    HasDerivAt (ellConv U)
      (∫ t in (-1 : ℝ)..1, U t * (U (ellHi ψ₀ t) * hiD ψ₀ t - U (ellLo ψ₀ t) * loD ψ₀ t)) ψ₀ := by
  set Φ : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..x, U y with hΦ
  have hΦd : ∀ x, HasDerivAt Φ (U x) x := fun x => (hUc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hΦc : Continuous Φ := continuous_iff_continuousAt.2 fun x => (hΦd x).continuousAt
  obtain ⟨MU, hMU⟩ := isCompact_Icc.exists_bound_of_continuousOn (hUc.continuousOn (s := Icc (-1 : ℝ) 1))
  have hfun : ellConv U = fun ψ => ∫ t in (-1 : ℝ)..1, U t * (Φ (ellHi ψ t) - Φ (ellLo ψ t)) := by
    funext ψ; exact ellConv_eq hUc ψ
  rw [hfun]
  have hcHi : ∀ x, Continuous (fun t => ellHi x t) := fun x => by unfold ellHi; fun_prop
  have hcLo : ∀ x, Continuous (fun t => ellLo x t) := fun x => by unfold ellLo; fun_prop
  have hcHiD : ∀ x, Continuous (fun t => hiD x t) := fun x => by unfold hiD; fun_prop
  have hcLoD : ∀ x, Continuous (fun t => loD x t) := fun x => by unfold loD; fun_prop
  have hFc : ∀ x, Continuous (fun t => U t * (Φ (ellHi x t) - Φ (ellLo x t))) := fun x =>
    hUc.mul ((hΦc.comp (hcHi x)).sub (hΦc.comp (hcLo x)))
  have hF'c : ∀ x, Continuous
      (fun t => U t * (U (ellHi x t) * hiD x t - U (ellLo x t) * loD x t)) := fun x =>
    hUc.mul (((hUc.comp (hcHi x)).mul (hcHiD x)).sub ((hUc.comp (hcLo x)).mul (hcLoD x)))
  have hMU0 : 0 ≤ MU := le_trans (norm_nonneg _) (hMU 0 ⟨by norm_num, by norm_num⟩)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := -1) (b := 1) (x₀ := ψ₀) (s := univ)
    (F := fun x t => U t * (Φ (ellHi x t) - Φ (ellLo x t)))
    (F' := fun x t => U t * (U (ellHi x t) * hiD x t - U (ellLo x t) * loD x t))
    (bound := fun _ => MU * (MU + MU)) Filter.univ_mem
    (Filter.Eventually.of_forall fun x => (hFc x).aestronglyMeasurable)
    ((hFc ψ₀).intervalIntegrable _ _) (hF'c ψ₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t ht x _ => by
      have ht' : t ∈ Icc (-1 : ℝ) 1 := by
        rw [uIoc_of_le (by norm_num)] at ht; exact Ioc_subset_Icc_self ht
      have h1 := hMU t ht'
      have h2 := hMU _ (ellHi_mem (ψ := x) ht')
      have h3 := hMU _ (ellLo_mem (ψ := x) ht')
      have h4 := abs_hiD_le (ψ := x) ht'
      have h5 := abs_loD_le (ψ := x) ht'
      rw [Real.norm_eq_abs] at h1 h2 h3 ⊢
      rw [abs_mul]
      have hA : |U (ellHi x t) * hiD x t| ≤ MU := by
        rw [abs_mul]
        calc |U (ellHi x t)| * |hiD x t| ≤ MU * 1 :=
              mul_le_mul h2 h4 (abs_nonneg _) hMU0
          _ = MU := mul_one MU
      have hB : |U (ellLo x t) * loD x t| ≤ MU := by
        rw [abs_mul]
        calc |U (ellLo x t)| * |loD x t| ≤ MU * 1 :=
              mul_le_mul h3 h5 (abs_nonneg _) hMU0
          _ = MU := mul_one MU
      have hAB : |U (ellHi x t) * hiD x t - U (ellLo x t) * loD x t| ≤ MU + MU := by
        have := abs_sub_le (U (ellHi x t) * hiD x t) 0 (U (ellLo x t) * loD x t)
        simp only [sub_zero, zero_sub, abs_neg] at this
        linarith
      exact mul_le_mul h1 hAB (abs_nonneg _) hMU0)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ x _ =>
      ((((hΦd _).comp x (hasDerivAt_ellHi x t)).sub
        ((hΦd _).comp x (hasDerivAt_ellLo x t))).const_mul (U t)))
  exact key.2

/-- **Integration by parts on a slice.** `sin ψ (U(hi) ∂hi − U(lo) ∂lo) = ∫ U'(y)(y cos ψ − t) + cos ψ ∫ U`. -/
theorem ibp_slice (hUd : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt U (U' y) (Icc (-1) 1) y)
    (hU'c : ContinuousOn U' (Icc (-1) 1)) {ψ t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    sin ψ * (U (ellHi ψ t) * hiD ψ t - U (ellLo ψ t) * loD ψ t)
      = (∫ y in ellLo ψ t..ellHi ψ t, U' y * (y * cos ψ - t))
        + cos ψ * ∫ y in ellLo ψ t..ellHi ψ t, U y := by
  have hsub : uIcc (ellLo ψ t) (ellHi ψ t) ⊆ Icc (-1) 1 := uIcc_subset_Icc (ellLo_mem ht) (ellHi_mem ht)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (u := fun y => y * cos ψ - t) (u' := fun _ => cos ψ) (v := U) (v' := U')
    (a := ellLo ψ t) (b := ellHi ψ t)
    (fun y _ => (((hasDerivAt_id' y).mul_const (cos ψ)).sub_const t |>.congr_deriv
      (by ring)).hasDerivWithinAt)
    (fun y hy => (hUd y (hsub hy)).mono hsub)
    intervalIntegrable_const ((hU'c.mono hsub).intervalIntegrable)
  have e1 : ellHi ψ t * cos ψ - t = sin ψ * hiD ψ t := by
    unfold ellHi hiD; linear_combination t * sin_sq_add_cos_sq ψ
  have e2 : ellLo ψ t * cos ψ - t = sin ψ * loD ψ t := by
    unfold ellLo loD; linear_combination t * sin_sq_add_cos_sq ψ
  have hcomm : ∫ y in ellLo ψ t..ellHi ψ t, U' y * (y * cos ψ - t)
      = ∫ y in ellLo ψ t..ellHi ψ t, (y * cos ψ - t) * U' y := by
    congr 1; funext y; ring
  rw [hcomm, hibp, e1, e2, intervalIntegral.integral_const_mul]
  ring

/-- The bulk term: `∫∫_{E_ψ} U(t) U'(y) (y cos ψ − t)`. -/
def bulkB (U U' : ℝ → ℝ) (ψ : ℝ) : ℝ := ellInt ψ (fun t y => U t * (U' y * (y * cos ψ - t)))

theorem ellGood_UU (hUc : Continuous U) (ψ : ℝ) : EllGood ψ (fun t y => U t * U y) :=
  ellGood_of_continuousOn ((hUc.comp continuous_fst).mul (hUc.comp continuous_snd)).continuousOn

theorem ellGood_bulk (hUc : Continuous U) (hU'c : ContinuousOn U' (Icc (-1) 1)) (ψ : ℝ) :
    EllGood ψ (fun t y => U t * (U' y * (y * cos ψ - t))) := by
  refine ellGood_of_continuousOn ?_
  have h2 : ContinuousOn (fun p : ℝ × ℝ => U' p.2) (ellSet ψ) :=
    hU'c.comp continuous_snd.continuousOn fun p hp => (ellSet_swap (t := p.1) (y := p.2) hp).1
  exact ((hUc.comp continuous_fst).continuousOn).mul (h2.mul (by fun_prop))

/-- **The derivative of the class convolution** `C(ψ) = ellConv U ψ / sin ψ` is `bulkB / sin²ψ`. -/
theorem hasDerivAt_convQuot (hUc : Continuous U)
    (hUd : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt U (U' y) (Icc (-1) 1) y)
    (hU'c : ContinuousOn U' (Icc (-1) 1)) {ψ : ℝ} (hψ : ψ ∈ Ioo 0 π) :
    HasDerivAt (fun x => ellConv U x / sin x) (bulkB U U' ψ / sin ψ ^ 2) ψ := by
  have hs : 0 < sin ψ := sin_pos_of_pos_of_lt_pi hψ.1 hψ.2
  have hD := hasDerivAt_ellConv hUc ψ
  have hval : sin ψ * (∫ t in (-1 : ℝ)..1,
      U t * (U (ellHi ψ t) * hiD ψ t - U (ellLo ψ t) * loD ψ t))
      = bulkB U U' ψ + cos ψ * ellConv U ψ := by
    rw [← intervalIntegral.integral_const_mul]
    have hpt : ∀ t ∈ uIcc (-1 : ℝ) 1, sin ψ * (U t * (U (ellHi ψ t) * hiD ψ t - U (ellLo ψ t) * loD ψ t))
        = (∫ y in ellLo ψ t..ellHi ψ t, U t * (U' y * (y * cos ψ - t)))
          + cos ψ * ∫ y in ellLo ψ t..ellHi ψ t, U t * U y := by
      intro t ht
      rw [uIcc_of_le (by norm_num)] at ht
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        show sin ψ * (U t * (U (ellHi ψ t) * hiD ψ t - U (ellLo ψ t) * loD ψ t))
          = U t * (sin ψ * (U (ellHi ψ t) * hiD ψ t - U (ellLo ψ t) * loD ψ t)) by ring,
        ibp_slice hUd hU'c ht]
      ring
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add
      (ellInt_outer_intervalIntegrable hs.le (ellGood_bulk hUc hU'c ψ))
      ((ellInt_outer_intervalIntegrable hs.le (ellGood_UU hUc ψ)).const_mul _),
      intervalIntegral.integral_const_mul]
    rfl
  have h := hD.div (hasDerivAt_sin ψ) hs.ne'
  refine h.congr_deriv ?_
  rw [mul_comm] at hval
  rw [hval]
  ring

end Conv

/-! ## 5. The score bound: reflection, swap, and the spherical bracket -/

section Score

variable {U U' : ℝ → ℝ}

theorem monotoneOn_of_derivWithin (hUc : Continuous U)
    (hUd : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt U (U' y) (Icc (-1) 1) y)
    (hmono : ∀ y ∈ Ioo (-1 : ℝ) 1, 0 ≤ U' y) : MonotoneOn U (Icc (-1) 1) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := U') (convex_Icc _ _) hUc.continuousOn ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx ⊢
    exact (hUd x (Ioo_subset_Icc_self hx)).mono Ioo_subset_Icc_self
  · intro x hx
    rw [interior_Icc] at hx
    exact hmono x hx

/-- **The slice moment at `t`**: `∫_{slice} U(y)(y − t cos ψ) ≥ 0` for `U` non-decreasing. This is the reflection
of the axis of `X⁻¹g` across the plane orthogonal to the axis of `g`, which keeps both angles and moves `X⁻¹g`
closer to `g` exactly when its axis leans towards `g`'s. -/
theorem sliceS_nonneg (hUc : Continuous U) (hU : MonotoneOn U (Icc (-1) 1)) {ψ t : ℝ}
    (hs : 0 ≤ sin ψ) (ht : t ∈ Icc (-1 : ℝ) 1) :
    0 ≤ ∫ y in ellLo ψ t..ellHi ψ t, U y * (y - t * cos ψ) := by
  have hsub : Icc (t * cos ψ - √(1 - t ^ 2) * sin ψ) (t * cos ψ + √(1 - t ^ 2) * sin ψ)
      ⊆ Icc (-1) 1 :=
    fun y hy => ⟨(ellLo_mem (ψ := ψ) ht).1.trans hy.1, hy.2.trans (ellHi_mem (ψ := ψ) ht).2⟩
  exact slice_moment_nonneg hUc (mul_nonneg (Real.sqrt_nonneg _) hs) (hU.mono hsub)

theorem ellLo_eq_ellHi {ψ t : ℝ} (h : t ^ 2 = 1) : ellLo ψ t = ellHi ψ t := by
  unfold ellLo ellHi
  rw [show 1 - t ^ 2 = 0 by linarith, Real.sqrt_zero]
  ring

theorem sq_eq_one_of_not_mem {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (hn : t ∉ Ioo (-1 : ℝ) 1) :
    t ^ 2 = 1 := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h]; norm_num
  · rcases eq_or_lt_of_le ht.2 with h' | h'
    · rw [h']; norm_num
    · exact absurd ⟨h, h'⟩ hn

theorem ellGood_of_measurable {ψ : ℝ} {F : ℝ → ℝ → ℝ} (hm : Measurable (Function.uncurry F))
    {M : ℝ} (hM : ∀ p ∈ ellSet ψ, |F p.1 p.2| ≤ M) : EllGood ψ F :=
  ⟨hm.aestronglyMeasurable, M, hM⟩

/-- The projection term `a cos θ_e` weighted: `arccos t · U t · U y · (y − t cos ψ)/√(1 − t²)`. -/
def projTerm (U : ℝ → ℝ) (ψ t y : ℝ) : ℝ :=
  arccos t * U t * (U y * ((y - t * cos ψ) / √(1 - t ^ 2)))

theorem measurable_projTerm (hUc : Continuous U) (ψ : ℝ) :
    Measurable (fun p : ℝ × ℝ => projTerm U ψ p.1 p.2) := by
  have m1 : Measurable fun p : ℝ × ℝ => arccos p.1 * U p.1 :=
    ((continuous_arccos.comp continuous_fst).mul (hUc.comp continuous_fst)).measurable
  have m2 : Measurable fun p : ℝ × ℝ => U p.2 := (hUc.comp continuous_snd).measurable
  have m3 : Measurable fun p : ℝ × ℝ => (p.2 - p.1 * cos ψ) / √(1 - p.1 ^ 2) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ => p.2 - p.1 * cos ψ).measurable.div
      (by fun_prop : Continuous fun p : ℝ × ℝ => √(1 - p.1 ^ 2)).measurable
  exact m1.mul (m2.mul m3)

theorem abs_projTerm_le {ψ : ℝ} (hs : 0 ≤ sin ψ) {MU : ℝ}
    (hMU : ∀ y ∈ Icc (-1 : ℝ) 1, |U y| ≤ MU) {t y : ℝ} (hE : (t, y) ∈ ellSet ψ) :
    |projTerm U ψ t y| ≤ π * MU * (MU * 1) := by
  have ht := hE.1
  have hy := (ellSet_swap hE).1
  have hMU0 : 0 ≤ MU := (abs_nonneg _).trans (hMU t ht)
  have hq : |(y - t * cos ψ) / √(1 - t ^ 2)| ≤ 1 :=
    (abs_ellQ_le hs (ellSet_swap hE)).trans (sin_le_one ψ)
  have ha : |arccos t| ≤ π := by rw [abs_of_nonneg (arccos_nonneg t)]; exact arccos_le_pi t
  unfold projTerm
  rw [abs_mul, abs_mul, abs_mul]
  have h1 : |arccos t| * |U t| ≤ π * MU := mul_le_mul ha (hMU t ht) (abs_nonneg _) pi_pos.le
  have h2 : |U y| * |(y - t * cos ψ) / √(1 - t ^ 2)| ≤ MU * 1 :=
    mul_le_mul (hMU y hy) hq (abs_nonneg _) hMU0
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

theorem ellGood_projTerm (hUc : Continuous U) {ψ : ℝ} (hs : 0 ≤ sin ψ) :
    EllGood ψ (fun t y => projTerm U ψ t y) := by
  obtain ⟨MU, hMU⟩ := isCompact_Icc.exists_bound_of_continuousOn (hUc.continuousOn (s := Icc (-1 : ℝ) 1))
  simp only [Real.norm_eq_abs] at hMU
  exact ellGood_of_measurable (measurable_projTerm hUc ψ) fun p hp => abs_projTerm_le hs hMU hp

theorem ellGood_projTerm_swap (hUc : Continuous U) {ψ : ℝ} (hs : 0 ≤ sin ψ) :
    EllGood ψ (fun t y => projTerm U ψ y t) := by
  obtain ⟨MU, hMU⟩ := isCompact_Icc.exists_bound_of_continuousOn (hUc.continuousOn (s := Icc (-1 : ℝ) 1))
  simp only [Real.norm_eq_abs] at hMU
  have m1 : Measurable fun p : ℝ × ℝ => arccos p.2 * U p.2 :=
    ((continuous_arccos.comp continuous_snd).mul (hUc.comp continuous_snd)).measurable
  have m2 : Measurable fun p : ℝ × ℝ => U p.1 := (hUc.comp continuous_fst).measurable
  have m3 : Measurable fun p : ℝ × ℝ => (p.1 - p.2 * cos ψ) / √(1 - p.2 ^ 2) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ => p.1 - p.2 * cos ψ).measurable.div
      (by fun_prop : Continuous fun p : ℝ × ℝ => √(1 - p.2 ^ 2)).measurable
  have hm : Measurable (Function.uncurry fun t y => projTerm U ψ y t) := by
    unfold Function.uncurry projTerm
    exact m1.mul (m2.mul m3)
  exact ellGood_of_measurable hm
    fun p hp => abs_projTerm_le hs hMU (ellSet_swap (t := p.1) (y := p.2) hp)

theorem EllGood.const_mul {ψ : ℝ} {F : ℝ → ℝ → ℝ} (hF : EllGood ψ F) (r : ℝ) :
    EllGood ψ (fun t y => r * F t y) := by
  obtain ⟨hm, M, hM⟩ := hF
  refine ⟨hm.const_mul r, |r| * M, fun p hp => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hM p hp) (abs_nonneg r)

theorem ellInt_zero (ψ : ℝ) : ellInt ψ (fun _ _ => 0) = 0 := by
  simp [ellInt]

/-- The Gram integral `Γ(ψ) = ∫∫_{E_ψ} U(t) U(y) Gram(t, y, ψ)`: the strong-concavity margin of the bracket. -/
def gramInt (U : ℝ → ℝ) (ψ : ℝ) : ℝ := ellInt ψ (fun t y => U t * U y * gram ψ t y)

theorem ellGood_gram (hUc : Continuous U) (ψ : ℝ) :
    EllGood ψ (fun t y => U t * U y * gram ψ t y) := by
  refine ellGood_of_continuousOn ?_
  unfold gram
  exact (((hUc.comp continuous_fst).mul (hUc.comp continuous_snd)).mul (by fun_prop)).continuousOn

theorem gramInt_nonneg (hUc : Continuous U) (hpos : ∀ y ∈ Ioo (-1 : ℝ) 1, 0 < U y) {ψ : ℝ}
    (hs : 0 ≤ sin ψ) : 0 ≤ gramInt U ψ := by
  rw [gramInt, ← ellInt_zero ψ]
  refine ellInt_mono hs (ellGood_of_continuousOn continuousOn_const) (ellGood_gram hUc ψ) ?_
  intro t y hE ht hy
  exact mul_nonneg (mul_nonneg (hpos t ht).le
    (hpos y hy).le) (gram_nonneg hE)

/-- **The bulk term is non-positive**: the class convolution of a decreasing weight with itself decreases. -/
theorem bulkB_nonpos (hUc : Continuous U)
    (hUd : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt U (U' y) (Icc (-1) 1) y)
    (hU'c : ContinuousOn U' (Icc (-1) 1)) (hmono : ∀ y ∈ Ioo (-1 : ℝ) 1, 0 ≤ U' y)
    {ψ : ℝ} (hψ : ψ ∈ Ioo 0 π) : bulkB U U' ψ ≤ 0 := by
  have hs := (sin_pos_of_pos_of_lt_pi hψ.1 hψ.2).le
  have hU := monotoneOn_of_derivWithin hUc hUd hmono
  rw [bulkB, ellInt_swap hs (ellGood_bulk hUc hU'c ψ)]
  unfold ellInt
  have hpt : ∀ t ∈ uIcc (-1 : ℝ) 1, ∫ y in ellLo ψ t..ellHi ψ t, U y * (U' t * (t * cos ψ - y))
      = -(U' t * ∫ y in ellLo ψ t..ellHi ψ t, U y * (y - t * cos ψ)) := by
    intro t _
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    congr 1; funext y; ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_neg, neg_nonpos]
  refine intervalIntegral.integral_nonneg (by norm_num) fun t ht => ?_
  by_cases hin : t ∈ Ioo (-1 : ℝ) 1
  · exact mul_nonneg (hmono t hin) (sliceS_nonneg hUc hU hs ht)
  · rw [ellLo_eq_ellHi (sq_eq_one_of_not_mem ht hin), intervalIntegral.integral_same, mul_zero]

/-- The projection deficit: `ψ sin ψ · ∫∫ U U` minus the integral of the two projection terms. Its density is
`U(t) U(y) (ψ sin ψ − a sin ψ cos θ_e − b sin ψ cos θ_g) ≥ 0`, the curvature margin of the spherical triangle. -/
def projDef (U : ℝ → ℝ) (ψ : ℝ) : ℝ :=
  ψ * sin ψ * ellConv U ψ - ellInt ψ (fun t y => projTerm U ψ t y + projTerm U ψ y t)

/-- **The score bound, projection form.** For `U` positive and non-decreasing on `[−1, 1]` with
`U'(y) √(1 − y²) ≤ arccos y · U(y)/(2c)`, `−bulkB ≤ ∫∫ (projection terms)/(4c)`. -/
theorem neg_bulkB_le_proj (hUc : Continuous U)
    (hUd : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt U (U' y) (Icc (-1) 1) y)
    (hU'c : ContinuousOn U' (Icc (-1) 1))
    (hmono : ∀ y ∈ Ioo (-1 : ℝ) 1, 0 ≤ U' y) {c : ℝ} (hc : 0 < c)
    (hlr : ∀ y ∈ Ioo (-1 : ℝ) 1, U' y * √(1 - y ^ 2) ≤ arccos y * U y / (2 * c))
    {ψ : ℝ} (hψ : ψ ∈ Ioo 0 π) :
    -bulkB U U' ψ ≤ ellInt ψ (fun t y => projTerm U ψ t y + projTerm U ψ y t) / (4 * c) := by
  have hs0 : 0 < sin ψ := sin_pos_of_pos_of_lt_pi hψ.1 hψ.2
  have hs := hs0.le
  have hU := monotoneOn_of_derivWithin hUc hUd hmono
  -- Step A: `−bulkB = ∫ U'(t) S(t)`.
  have hA : -bulkB U U' ψ = ∫ t in (-1 : ℝ)..1,
      U' t * ∫ y in ellLo ψ t..ellHi ψ t, U y * (y - t * cos ψ) := by
    rw [bulkB, ellInt_swap hs (ellGood_bulk hUc hU'c ψ)]
    unfold ellInt
    have hpt : ∀ t ∈ uIcc (-1 : ℝ) 1, ∫ y in ellLo ψ t..ellHi ψ t, U y * (U' t * (t * cos ψ - y))
        = -(U' t * ∫ y in ellLo ψ t..ellHi ψ t, U y * (y - t * cos ψ)) := by
      intro t _
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
      congr 1; funext y; ring
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_neg, neg_neg]
  -- Step B: the LR hypothesis, slice by slice.
  have hgood3 : EllGood ψ (fun t y => U' t * (U y * (y - t * cos ψ))) := by
    refine ellGood_of_continuousOn ?_
    have h1 : ContinuousOn (fun p : ℝ × ℝ => U' p.1) (ellSet ψ) :=
      hU'c.comp continuous_fst.continuousOn fun p hp => hp.1
    exact h1.mul (((hUc.comp continuous_snd).mul (by fun_prop)).continuousOn)
  have hgood2 : EllGood ψ (fun t y => 1 / (2 * c) * projTerm U ψ t y) :=
    (ellGood_projTerm hUc hs).const_mul _
  have hB : ∫ t in (-1 : ℝ)..1, U' t * ∫ y in ellLo ψ t..ellHi ψ t, U y * (y - t * cos ψ)
      ≤ ∫ t in (-1 : ℝ)..1, ∫ y in ellLo ψ t..ellHi ψ t, 1 / (2 * c) * projTerm U ψ t y := by
    have hf : (fun t => U' t * ∫ y in ellLo ψ t..ellHi ψ t, U y * (y - t * cos ψ))
        = fun t => ∫ y in ellLo ψ t..ellHi ψ t, U' t * (U y * (y - t * cos ψ)) := by
      funext t; rw [intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by norm_num) ?_
      (ellInt_outer_intervalIntegrable hs hgood2) ?_
    · rw [hf]; exact ellInt_outer_intervalIntegrable hs hgood3
    · intro t ht
      by_cases hin : t ∈ Ioo (-1 : ℝ) 1
      · have hw2 : 0 < 1 - t ^ 2 := by nlinarith [hin.1, hin.2]
        have hw : 0 < √(1 - t ^ 2) := Real.sqrt_pos.2 hw2
        have hS := sliceS_nonneg hUc hU hs ht
        have hR : ∫ y in ellLo ψ t..ellHi ψ t, 1 / (2 * c) * projTerm U ψ t y
            = arccos t * U t / (2 * c) / √(1 - t ^ 2)
              * ∫ y in ellLo ψ t..ellHi ψ t, U y * (y - t * cos ψ) := by
          rw [← intervalIntegral.integral_const_mul]
          congr 1; funext y; unfold projTerm; ring
        rw [hR]
        have hle : U' t ≤ arccos t * U t / (2 * c) / √(1 - t ^ 2) :=
          (le_div_iff₀ hw).2 (hlr t hin)
        exact mul_le_mul_of_nonneg_right hle hS
      · rw [ellLo_eq_ellHi (sq_eq_one_of_not_mem ht hin), intervalIntegral.integral_same,
          intervalIntegral.integral_same, mul_zero]
  -- Step C: pull out the constant; Step D: symmetrise.
  have hC : ∫ t in (-1 : ℝ)..1, ∫ y in ellLo ψ t..ellHi ψ t, 1 / (2 * c) * projTerm U ψ t y
      = 1 / (2 * c) * ellInt ψ (fun t y => projTerm U ψ t y) :=
    ellInt_const_mul (1 / (2 * c)) (fun t y => projTerm U ψ t y)
  have hD : ellInt ψ (fun t y => projTerm U ψ t y) = ellInt ψ (fun t y => projTerm U ψ y t) :=
    ellInt_swap hs (ellGood_projTerm hUc hs)
  have hsum : ellInt ψ (fun t y => projTerm U ψ t y + projTerm U ψ y t)
      = 2 * ellInt ψ (fun t y => projTerm U ψ t y) := by
    rw [ellInt_add hs (ellGood_projTerm hUc hs) (ellGood_projTerm_swap hUc hs), ← hD]
    ring
  rw [hsum, hA]
  calc ∫ t in (-1 : ℝ)..1, U' t * ∫ y in ellLo ψ t..ellHi ψ t, U y * (y - t * cos ψ)
      ≤ 1 / (2 * c) * ellInt ψ (fun t y => projTerm U ψ t y) := hC ▸ hB
    _ = 2 * ellInt ψ (fun t y => projTerm U ψ t y) / (4 * c) := by
        field_simp; ring

/-- **The projection terms are bounded by the spherical bracket**:
`∫∫ (projection terms) ≤ ψ sin ψ · ∫∫ U U − Γ/3`, i.e. `projDef ≥ Γ/3 ≥ 0`. -/
theorem gramInt_div_three_le_projDef (hUc : Continuous U) (hpos : ∀ y ∈ Ioo (-1 : ℝ) 1, 0 < U y)
    {ψ : ℝ} (hψ : ψ ∈ Ioo 0 π) : gramInt U ψ / 3 ≤ projDef U ψ := by
  have hs := (sin_pos_of_pos_of_lt_pi hψ.1 hψ.2).le
  have hE : ellInt ψ (fun t y => projTerm U ψ t y + projTerm U ψ y t)
      ≤ ellInt ψ (fun t y => ψ * sin ψ * (U t * U y) + -(1 / 3) * (U t * U y * gram ψ t y)) := by
    refine ellInt_mono hs ((ellGood_projTerm hUc hs).add (ellGood_projTerm_swap hUc hs))
      (((ellGood_UU hUc ψ).const_mul _).add ((ellGood_gram hUc ψ).const_mul _)) ?_
    intro t y hEt ht hy
    have hb := ell_bracket_le hψ.1.le hψ.2.le ht hy hEt
    have hUU : 0 ≤ U t * U y :=
      mul_nonneg (hpos t ht).le (hpos y hy).le
    calc projTerm U ψ t y + projTerm U ψ y t
        = U t * U y * (arccos t * ((y - t * cos ψ) / √(1 - t ^ 2))
            + arccos y * ((t - y * cos ψ) / √(1 - y ^ 2))) := by
          unfold projTerm; ring
      _ ≤ U t * U y * (ψ * sin ψ - gram ψ t y / 3) :=
          mul_le_mul_of_nonneg_left (by linarith) hUU
      _ = ψ * sin ψ * (U t * U y) + -(1 / 3) * (U t * U y * gram ψ t y) := by ring
  have hrhs : ellInt ψ (fun t y => ψ * sin ψ * (U t * U y) + -(1 / 3) * (U t * U y * gram ψ t y))
      = ψ * sin ψ * ellConv U ψ - gramInt U ψ / 3 := by
    rw [ellInt_add hs ((ellGood_UU hUc ψ).const_mul _) ((ellGood_gram hUc ψ).const_mul _),
      ellInt_const_mul, ellInt_const_mul]
    unfold ellConv gramInt
    ring
  rw [hrhs] at hE
  unfold projDef
  linarith

/-- **The score bound, Gram form.** `−bulkB ≤ (ψ sin ψ · ellConv − Γ/3)/(4c)`. -/
theorem neg_bulkB_le (hUc : Continuous U)
    (hUd : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt U (U' y) (Icc (-1) 1) y)
    (hU'c : ContinuousOn U' (Icc (-1) 1)) (hpos : ∀ y ∈ Ioo (-1 : ℝ) 1, 0 < U y)
    (hmono : ∀ y ∈ Ioo (-1 : ℝ) 1, 0 ≤ U' y) {c : ℝ} (hc : 0 < c)
    (hlr : ∀ y ∈ Ioo (-1 : ℝ) 1, U' y * √(1 - y ^ 2) ≤ arccos y * U y / (2 * c))
    {ψ : ℝ} (hψ : ψ ∈ Ioo 0 π) :
    -bulkB U U' ψ ≤ (ψ * sin ψ * ellConv U ψ - gramInt U ψ / 3) / (4 * c) := by
  have h1 := neg_bulkB_le_proj hUc hUd hU'c hmono hc hlr hψ
  have h2 := gramInt_div_three_le_projDef hUc hpos hψ
  unfold projDef at h2
  have h4c : 0 < 4 * c := by positivity
  calc -bulkB U U' ψ ≤ ellInt ψ (fun t y => projTerm U ψ t y + projTerm U ψ y t) / (4 * c) := h1
    _ ≤ (ψ * sin ψ * ellConv U ψ - gramInt U ψ / 3) / (4 * c) :=
        div_le_div_of_nonneg_right (by linarith) h4c.le

end Score

/-! ## 6. The transfer for one convolution: likelihood-ratio order against the flat Gaussian -/

section Transfer

variable {U U' : ℝ → ℝ}

/-- The flat (Lie-algebra) Gaussian at time `a`: `e^{−ψ²/4a}`, the heat kernel of `ℝ³` read in the angle. -/
def flatG (a ψ : ℝ) : ℝ := Real.exp (-ψ ^ 2 / (4 * a))

theorem flatG_pos (a ψ : ℝ) : 0 < flatG a ψ := Real.exp_pos _

theorem ellConv_pos (hUc : Continuous U) (hpos : ∀ y ∈ Ioo (-1 : ℝ) 1, 0 < U y) {ψ : ℝ}
    (hψ : ψ ∈ Ioo 0 π) : 0 < ellConv U ψ := by
  have hs0 : 0 < sin ψ := sin_pos_of_pos_of_lt_pi hψ.1 hψ.2
  rw [ellConv_eq hUc ψ]
  set Φ : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..x, U y with hΦ
  have hΦd : ∀ x, HasDerivAt Φ (U x) x := fun x => (hUc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hΦc : Continuous Φ := continuous_iff_continuousAt.2 fun x => (hΦd x).continuousAt
  have hcHi : Continuous (fun t => ellHi ψ t) := by unfold ellHi; fun_prop
  have hcLo : Continuous (fun t => ellLo ψ t) := by unfold ellLo; fun_prop
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((hUc.mul ((hΦc.comp hcHi).sub (hΦc.comp hcLo))).intervalIntegrable _ _) ?_ (by norm_num)
  intro t ht
  have htI : t ∈ Icc (-1 : ℝ) 1 := Ioo_subset_Icc_self ht
  have hw2 : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hlt : ellLo ψ t < ellHi ψ t := by
    unfold ellLo ellHi
    have := mul_pos (Real.sqrt_pos.2 hw2) hs0
    linarith
  have hin : (∫ y in (0 : ℝ)..ellHi ψ t, U y) - ∫ y in (0 : ℝ)..ellLo ψ t, U y
      = ∫ y in ellLo ψ t..ellHi ψ t, U y :=
    intervalIntegral.integral_interval_sub_left (hUc.intervalIntegrable _ _)
      (hUc.intervalIntegrable _ _)
  refine mul_pos (hpos t ht) ?_
  show 0 < (∫ y in (0 : ℝ)..ellHi ψ t, U y) - ∫ y in (0 : ℝ)..ellLo ψ t, U y
  rw [hin]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (hUc.intervalIntegrable _ _) ?_ hlt
  intro y hy
  exact hpos y ⟨lt_of_le_of_lt (ellLo_mem (ψ := ψ) htI).1 hy.1,
    lt_of_lt_of_le hy.2 (ellHi_mem (ψ := ψ) htI).2⟩

/-- **The class convolution of a decreasing weight decreases.** -/
theorem convQuot_antitoneOn (hUc : Continuous U)
    (hUd : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt U (U' y) (Icc (-1) 1) y)
    (hU'c : ContinuousOn U' (Icc (-1) 1)) (hmono : ∀ y ∈ Ioo (-1 : ℝ) 1, 0 ≤ U' y) :
    AntitoneOn (fun x => ellConv U x / sin x) (Ioo 0 π) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioo 0 π)
    (fun x hx => (hasDerivAt_convQuot hUc hUd hU'c hx).continuousAt.continuousWithinAt)
    (fun x hx => by
      rw [interior_Ioo] at hx
      exact (hasDerivAt_convQuot hUc hUd hU'c hx).differentiableAt.differentiableWithinAt)
    fun x hx => ?_
  rw [interior_Ioo] at hx
  rw [(hasDerivAt_convQuot hUc hUd hU'c hx).deriv]
  exact div_nonpos_of_nonpos_of_nonneg (bulkB_nonpos hUc hUd hU'c hmono hx) (sq_nonneg _)

/-- **The convolution transfer for one class convolution, with gain.** Let `U` be positive and non-decreasing on
`[−1, 1]` with `U'(y) √(1 − y²) ≤ arccos y · U(y)/(2c)`: in the angle, `u = U ∘ cos` is a decreasing class weight
LR-wider than the flat Gaussian `e^{−ψ²/4c}`. If the projection deficit is at least a fraction `κ ∈ [0, 1)` of
`ψ sin ψ ∫∫ U U` at every angle, the self-convolution `u ⋆ u = ellConv U / sin` is LR-wider than the flat Gaussian
at time `2c/(1 − κ)`. At `κ = 0` the hypothesis is `gramInt_div_three_le_projDef`. -/
theorem convQuot_lrWider_flat (hUc : Continuous U)
    (hUd : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt U (U' y) (Icc (-1) 1) y)
    (hU'c : ContinuousOn U' (Icc (-1) 1)) (hpos : ∀ y ∈ Ioo (-1 : ℝ) 1, 0 < U y)
    (hmono : ∀ y ∈ Ioo (-1 : ℝ) 1, 0 ≤ U' y) {c : ℝ} (hc : 0 < c)
    (hlr : ∀ y ∈ Ioo (-1 : ℝ) 1, U' y * √(1 - y ^ 2) ≤ arccos y * U y / (2 * c))
    {κ : ℝ} (hκ1 : κ < 1)
    (hgain : ∀ ψ ∈ Ioo 0 π, κ * (ψ * sin ψ * ellConv U ψ) ≤ projDef U ψ) :
    MonotoneOn (fun x => ellConv U x / sin x / flatG (2 * c / (1 - κ)) x) (Ioo 0 π) := by
  have h1κ : 0 < 1 - κ := by linarith
  set k : ℝ := (1 - κ) / (8 * c) with hk
  have hfun : (fun x => ellConv U x / sin x / flatG (2 * c / (1 - κ)) x)
      = fun x => ellConv U x / sin x * Real.exp (x ^ 2 * k) := by
    funext x
    rw [flatG, div_eq_mul_inv, ← Real.exp_neg]
    congr 2
    rw [hk]
    field_simp
    ring
  rw [hfun]
  have hder : ∀ x ∈ Ioo 0 π, HasDerivAt (fun x => ellConv U x / sin x * Real.exp (x ^ 2 * k))
      (bulkB U U' x / sin x ^ 2 * Real.exp (x ^ 2 * k)
        + ellConv U x / sin x * (Real.exp (x ^ 2 * k) * (2 * x * k))) x := by
    intro x hx
    have he : HasDerivAt (fun x => Real.exp (x ^ 2 * k)) (Real.exp (x ^ 2 * k) * (2 * x * k)) x :=
      (((hasDerivAt_pow 2 x).mul_const k).exp).congr_deriv (by norm_num)
    exact (hasDerivAt_convQuot hUc hUd hU'c hx).mul he
  refine monotoneOn_of_deriv_nonneg (convex_Ioo 0 π)
    (fun x hx => (hder x hx).continuousAt.continuousWithinAt)
    (fun x hx => by
      rw [interior_Ioo] at hx
      exact (hder x hx).differentiableAt.differentiableWithinAt)
    fun x hx => ?_
  rw [interior_Ioo] at hx
  rw [(hder x hx).deriv]
  have hs0 : 0 < sin x := sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hE := ellConv_pos hUc hpos hx
  have hB := neg_bulkB_le_proj hUc hUd hU'c hmono hc hlr hx
  have hG := hgain x hx
  unfold projDef at hG
  -- `−bulkB ≤ (1 − κ) x sin x · E / (4c)`
  have hB' : -bulkB U U' x ≤ (1 - κ) * (x * sin x * ellConv U x) / (4 * c) := by
    have h4c : 0 < 4 * c := by positivity
    calc -bulkB U U' x
        ≤ ellInt x (fun t y => projTerm U x t y + projTerm U x y t) / (4 * c) := hB
      _ ≤ (1 - κ) * (x * sin x * ellConv U x) / (4 * c) :=
          div_le_div_of_nonneg_right (by linarith) h4c.le
  have he := Real.exp_pos (x ^ 2 * k)
  have key : 0 ≤ bulkB U U' x / sin x ^ 2 + ellConv U x / sin x * (2 * x * k) := by
    have e : bulkB U U' x / sin x ^ 2 + ellConv U x / sin x * (2 * x * k)
        = (bulkB U U' x + (1 - κ) * (x * sin x * ellConv U x) / (4 * c)) / sin x ^ 2 := by
      rw [hk]; field_simp; ring
    rw [e]
    exact div_nonneg (by linarith) (sq_nonneg _)
  have : bulkB U U' x / sin x ^ 2 * Real.exp (x ^ 2 * k)
      + ellConv U x / sin x * (Real.exp (x ^ 2 * k) * (2 * x * k))
      = Real.exp (x ^ 2 * k) * (bulkB U U' x / sin x ^ 2 + ellConv U x / sin x * (2 * x * k)) := by
    ring
  rw [this]
  exact mul_nonneg he.le key

/-- **The convolution transfer for one class convolution, no gain**: LR-wider than `e^{−ψ²/4c}` gives
LR-wider than `e^{−ψ²/8c}`. -/
theorem convQuot_lrWider_flat_two (hUc : Continuous U)
    (hUd : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt U (U' y) (Icc (-1) 1) y)
    (hU'c : ContinuousOn U' (Icc (-1) 1)) (hpos : ∀ y ∈ Ioo (-1 : ℝ) 1, 0 < U y)
    (hmono : ∀ y ∈ Ioo (-1 : ℝ) 1, 0 ≤ U' y) {c : ℝ} (hc : 0 < c)
    (hlr : ∀ y ∈ Ioo (-1 : ℝ) 1, U' y * √(1 - y ^ 2) ≤ arccos y * U y / (2 * c)) :
    MonotoneOn (fun x => ellConv U x / sin x / flatG (2 * c) x) (Ioo 0 π) := by
  have h := convQuot_lrWider_flat hUc hUd hU'c hpos hmono hc hlr (κ := 0) (by norm_num)
    (fun ψ hψ => by
      have h1 := gramInt_div_three_le_projDef hUc hpos hψ
      have h2 := gramInt_nonneg hUc hpos (sin_pos_of_pos_of_lt_pi hψ.1 hψ.2).le
      linarith)
  simpa using h

end Transfer

/-! ## 7. The cosine variable: admissible weights, the power step, one convolution -/

section Step

variable {U U' : ℝ → ℝ}

/-- A class weight in the cosine variable `t = cos ψ`, admissible at flat time `c`: continuous, `C¹` on `[−1, 1]`,
positive and non-decreasing in `t` (decreasing in the angle), with `U'(t)√(1 − t²) ≤ arccos t · U(t)/(2c)`, i.e.
`ψ ↦ U(cos ψ) e^{ψ²/4c}` non-decreasing: LR-wider than the flat Gaussian `e^{−ψ²/4c}`. -/
structure FlatAdmissible (U U' : ℝ → ℝ) (c : ℝ) : Prop where
  cont : Continuous U
  deriv : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt U (U' y) (Icc (-1) 1) y
  derivCont : ContinuousOn U' (Icc (-1) 1)
  pos : ∀ y ∈ Ioo (-1 : ℝ) 1, 0 < U y
  mono : ∀ y ∈ Ioo (-1 : ℝ) 1, 0 ≤ U' y
  lr : ∀ y ∈ Ioo (-1 : ℝ) 1, U' y * √(1 - y ^ 2) ≤ arccos y * U y / (2 * c)

/-- **The gain input.** For every weight admissible at flat time `c`, the projection deficit is at least a
fraction `κ₀ min(c, 1)` of `ψ sin ψ ∫∫ U U` at every angle. -/
def FlatGain (κ₀ : ℝ) : Prop :=
  ∀ (U U' : ℝ → ℝ) (c : ℝ), 0 < c → FlatAdmissible U U' c →
    ∀ ψ ∈ Ioo 0 π, κ₀ * min c 1 * (ψ * sin ψ * ellConv U ψ) ≤ projDef U ψ

/-- The class convolution `u ⋆ u` in the cosine variable. -/
def convT (U : ℝ → ℝ) (t : ℝ) : ℝ := ellConv U (arccos t) / sin (arccos t)

/-- Its derivative in `t`. -/
def convT' (U U' : ℝ → ℝ) (t : ℝ) : ℝ :=
  bulkB U U' (arccos t) / sin (arccos t) ^ 2 * -(1 / √(1 - t ^ 2))

theorem arccos_mem_Ioo {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : arccos t ∈ Ioo 0 π :=
  ⟨arccos_pos.2 ht.2, arccos_lt_pi.2 ht.1⟩

theorem hasDerivAt_convT {c : ℝ} (hU : FlatAdmissible U U' c) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (convT U) (convT' U U' t) t :=
  (hasDerivAt_convQuot hU.cont hU.deriv hU.derivCont (arccos_mem_Ioo ht)).comp t
    (hasDerivAt_arccos ht.1.ne' ht.2.ne)

/-- **One convolution in the cosine variable.** If `U` is admissible at `c` and the projection deficit is at least a
fraction `κ < 1`, then `convT U` is positive and non-decreasing with
`convT' · √(1 − t²) ≤ arccos t · convT U/(2 · 2c/(1 − κ))`. -/
theorem convT_bounds {c : ℝ} (hU : FlatAdmissible U U' c) (hc : 0 < c) {κ : ℝ} (hκ1 : κ < 1)
    (hgain : ∀ ψ ∈ Ioo 0 π, κ * (ψ * sin ψ * ellConv U ψ) ≤ projDef U ψ)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    0 < convT U t ∧ 0 ≤ convT' U U' t ∧
      convT' U U' t * √(1 - t ^ 2) ≤ arccos t * convT U t / (2 * (2 * c / (1 - κ))) := by
  have hψ := arccos_mem_Ioo ht
  set ψ := arccos t with hψdef
  have hs : sin ψ = √(1 - t ^ 2) := by rw [hψdef, sin_arccos]
  have hs0 : 0 < sin ψ := sin_pos_of_pos_of_lt_pi hψ.1 hψ.2
  have hE := ellConv_pos hU.cont hU.pos hψ
  have hB0 := bulkB_nonpos hU.cont hU.deriv hU.derivCont hU.mono hψ
  have hB := neg_bulkB_le_proj hU.cont hU.deriv hU.derivCont hU.mono hc hU.lr hψ
  have hG := hgain ψ hψ
  unfold projDef at hG
  have h1κ : 0 < 1 - κ := by linarith
  refine ⟨div_pos hE hs0, ?_, ?_⟩
  · unfold convT'
    rw [← hψdef, ← hs]
    have : 0 ≤ -bulkB U U' ψ := by linarith
    have e : bulkB U U' ψ / sin ψ ^ 2 * -(1 / sin ψ) = -bulkB U U' ψ / sin ψ ^ 3 := by
      field_simp
    rw [e]
    positivity
  · unfold convT' convT
    rw [← hψdef, ← hs]
    have h4c : 0 < 4 * c := by positivity
    have hB' : -bulkB U U' ψ ≤ (1 - κ) * (ψ * sin ψ * ellConv U ψ) / (4 * c) :=
      hB.trans (div_le_div_of_nonneg_right (by linarith) h4c.le)
    have e1 : bulkB U U' ψ / sin ψ ^ 2 * -(1 / sin ψ) * sin ψ = -bulkB U U' ψ / sin ψ ^ 2 := by
      field_simp
    have e2 : ψ * (ellConv U ψ / sin ψ) / (2 * (2 * c / (1 - κ)))
        = (1 - κ) * (ψ * sin ψ * ellConv U ψ) / (4 * c) / sin ψ ^ 2 := by
      field_simp
      ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_right hB' (sq_nonneg _)

/-- **A function equal to a positive multiple of `convT U` on `(−1, 1)` and `C¹` on `[−1, 1]` is admissible.** -/
theorem admissible_of_convT {c : ℝ} (hU : FlatAdmissible U U' c) (hc : 0 < c) {κ : ℝ} (hκ1 : κ < 1)
    (hgain : ∀ ψ ∈ Ioo 0 π, κ * (ψ * sin ψ * ellConv U ψ) ≤ projDef U ψ)
    {P P' : ℝ → ℝ} {μ : ℝ} (hμ : 0 < μ) (hPc : Continuous P)
    (hPd : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt P (P' y) (Icc (-1) 1) y)
    (hP'c : ContinuousOn P' (Icc (-1) 1)) (hPeq : ∀ y ∈ Ioo (-1 : ℝ) 1, P y = μ * convT U y) :
    FlatAdmissible P P' (2 * c / (1 - κ)) := by
  have hderiv : ∀ y ∈ Ioo (-1 : ℝ) 1, P' y = μ * convT' U U' y := by
    intro y hy
    have h1 : HasDerivAt P (P' y) y :=
      (hPd y (Ioo_subset_Icc_self hy)).hasDerivAt (Icc_mem_nhds hy.1 hy.2)
    have h2 : HasDerivAt P (μ * convT' U U' y) y := by
      refine ((hasDerivAt_convT hU hy).const_mul μ).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
      exact hPeq z hz
    exact h1.unique h2
  refine ⟨hPc, hPd, hP'c, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · rw [hPeq y hy]; exact mul_pos hμ (convT_bounds hU hc hκ1 hgain hy).1
  · rw [hderiv y hy]; exact mul_nonneg hμ.le (convT_bounds hU hc hκ1 hgain hy).2.1
  · rw [hderiv y hy, hPeq y hy]
    have := (convT_bounds hU hc hκ1 hgain hy).2.2
    have e1 : μ * convT' U U' y * √(1 - y ^ 2) = μ * (convT' U U' y * √(1 - y ^ 2)) := by ring
    have e2 : arccos y * (μ * convT U y) / (2 * (2 * c / (1 - κ)))
        = μ * (arccos y * convT U y / (2 * (2 * c / (1 - κ)))) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left this hμ.le

/-- The no-gain projection bound in the form `convT_bounds` takes (`κ = 0`). -/
theorem projDef_zero_gain {c : ℝ} (hU : FlatAdmissible U U' c) :
    ∀ ψ ∈ Ioo 0 π, (0 : ℝ) * (ψ * sin ψ * ellConv U ψ) ≤ projDef U ψ := by
  intro ψ hψ
  have h1 := gramInt_div_three_le_projDef hU.cont hU.pos hψ
  have h2 := gramInt_nonneg hU.cont hU.pos (sin_pos_of_pos_of_lt_pi hψ.1 hψ.2).le
  rw [zero_mul]
  linarith

/-- **The power step is exact for the flat Gaussian**: admissible at `a` gives the fourth power admissible at
`a/4`. -/
theorem admissible_pow_four {W W' : ℝ → ℝ} {a : ℝ} (hW : FlatAdmissible W W' a) (ha : 0 < a) :
    FlatAdmissible (fun t => W t ^ 4) (fun t => 4 * W t ^ 3 * W' t) (a / 4) := by
  refine ⟨hW.cont.pow 4, fun y hy => ?_, ?_, fun y hy => pow_pos (hW.pos y hy) 4,
    fun y hy => ?_, fun y hy => ?_⟩
  · exact ((hW.deriv y hy).pow 4).congr_deriv (by norm_num)
  · exact ((continuousOn_const.mul (hW.cont.continuousOn.pow 3)).mul hW.derivCont)
  · have := hW.mono y hy
    have := (hW.pos y hy).le
    positivity
  · have h := hW.lr y hy
    have hW3 : 0 ≤ 4 * W y ^ 3 := by have := (hW.pos y hy).le; positivity
    have := mul_le_mul_of_nonneg_left h hW3
    have e : arccos y * W y ^ 4 / (2 * (a / 4)) = 4 * W y ^ 3 * (arccos y * W y / (2 * a)) := by
      field_simp
    rw [e]
    calc 4 * W y ^ 3 * W' y * √(1 - y ^ 2) = 4 * W y ^ 3 * (W' y * √(1 - y ^ 2)) := by ring
      _ ≤ 4 * W y ^ 3 * (arccos y * W y / (2 * a)) := this

/-- **The Wilson start is admissible**: `t ↦ e^{βt}` (the weight `e^{β cos ψ}`) at flat time `1/(2β)`, because
`sin ψ ≤ ψ`. -/
theorem wilson_admissible {β : ℝ} (hβ : 0 < β) :
    FlatAdmissible (fun t => Real.exp (β * t)) (fun t => β * Real.exp (β * t)) (1 / (2 * β)) := by
  refine ⟨by fun_prop, fun y _ => ?_, by fun_prop, fun y _ => Real.exp_pos _,
    fun y _ => (mul_pos hβ (Real.exp_pos _)).le, fun y hy => ?_⟩
  · exact ((((hasDerivAt_id' y).const_mul β).exp).congr_deriv (by ring)).hasDerivWithinAt
  · have hs : √(1 - y ^ 2) ≤ arccos y := by
      rw [← sin_arccos]; exact sin_le (arccos_nonneg y)
    have e : arccos y * Real.exp (β * y) / (2 * (1 / (2 * β))) = β * Real.exp (β * y) * arccos y := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hs (mul_pos hβ (Real.exp_pos _)).le

/-- **Admissibility is LR order against the flat Gaussian in the angle**: `ψ ↦ U(cos ψ)/e^{−ψ²/4c}` is
non-decreasing on `(0, π)`. -/
theorem FlatAdmissible.lrWider {c : ℝ} (hU : FlatAdmissible U U' c) (hc : 0 < c) :
    MonotoneOn (fun ψ => U (cos ψ) / flatG c ψ) (Ioo 0 π) := by
  have hfun : (fun ψ => U (cos ψ) / flatG c ψ) = fun ψ => U (cos ψ) * Real.exp (ψ ^ 2 / (4 * c)) := by
    funext ψ
    rw [flatG, div_eq_mul_inv, ← Real.exp_neg]
    congr 2
    ring
  rw [hfun]
  have hder : ∀ ψ ∈ Ioo 0 π, HasDerivAt (fun ψ => U (cos ψ) * Real.exp (ψ ^ 2 / (4 * c)))
      (U' (cos ψ) * -sin ψ * Real.exp (ψ ^ 2 / (4 * c))
        + U (cos ψ) * (Real.exp (ψ ^ 2 / (4 * c)) * (2 * ψ / (4 * c)))) ψ := by
    intro ψ hψ
    have hy : cos ψ ∈ Ioo (-1 : ℝ) 1 :=
      ⟨by
        have := cos_lt_cos_of_nonneg_of_le_pi hψ.1.le le_rfl hψ.2
        rwa [cos_pi] at this,
       by
        have := cos_lt_cos_of_nonneg_of_le_pi le_rfl hψ.2.le hψ.1
        rwa [cos_zero] at this⟩
    have h1 : HasDerivAt U (U' (cos ψ)) (cos ψ) :=
      (hU.deriv _ (Ioo_subset_Icc_self hy)).hasDerivAt (Icc_mem_nhds hy.1 hy.2)
    have h2 : HasDerivAt (fun ψ => Real.exp (ψ ^ 2 / (4 * c)))
        (Real.exp (ψ ^ 2 / (4 * c)) * (2 * ψ / (4 * c))) ψ :=
      (((hasDerivAt_pow 2 ψ).div_const (4 * c)).exp).congr_deriv (by norm_num)
    exact (h1.comp ψ (hasDerivAt_cos ψ)).mul h2
  refine monotoneOn_of_deriv_nonneg (convex_Ioo 0 π)
    (fun x hx => (hder x hx).continuousAt.continuousWithinAt)
    (fun x hx => by
      rw [interior_Ioo] at hx
      exact (hder x hx).differentiableAt.differentiableWithinAt)
    fun ψ hψ => ?_
  rw [interior_Ioo] at hψ
  rw [(hder ψ hψ).deriv]
  have hy : cos ψ ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by
      have := cos_lt_cos_of_nonneg_of_le_pi hψ.1.le le_rfl hψ.2
      rwa [cos_pi] at this,
     by
      have := cos_lt_cos_of_nonneg_of_le_pi le_rfl hψ.2.le hψ.1
      rwa [cos_zero] at this⟩
  have hlr := hU.lr _ hy
  rw [arccos_cos hψ.1.le hψ.2.le, ← sin_arccos, arccos_cos hψ.1.le hψ.2.le] at hlr
  have he := Real.exp_pos (ψ ^ 2 / (4 * c))
  have key : 0 ≤ -(U' (cos ψ) * sin ψ) + U (cos ψ) * (2 * ψ / (4 * c)) := by
    have : ψ * U (cos ψ) / (2 * c) = U (cos ψ) * (2 * ψ / (4 * c)) := by field_simp; ring
    linarith
  have e : U' (cos ψ) * -sin ψ * Real.exp (ψ ^ 2 / (4 * c))
      + U (cos ψ) * (Real.exp (ψ ^ 2 / (4 * c)) * (2 * ψ / (4 * c)))
      = Real.exp (ψ ^ 2 / (4 * c)) * (-(U' (cos ψ) * sin ψ) + U (cos ψ) * (2 * ψ / (4 * c))) := by
    ring
  rw [e]
  exact mul_nonneg he.le key

end Step

/-! ## 8. The Migdal–Kadanoff step and the chain against the flat Gaussian -/

section Chain

/-- The reference after one Migdal–Kadanoff step with the gain `κ₀ min(a/4, 1)` in the first convolution:
`a ↦ a/(1 − κ₀ min(a/4, 1))`. -/
def refFlat (κ₀ a : ℝ) : ℝ := a / (1 - κ₀ * min (a / 4) 1)

/-- The reference sequence `a_{k+1} = refFlat κ₀ a_k`. -/
def refSeqFlat (κ₀ a₀ : ℝ) : ℕ → ℝ
  | 0 => a₀
  | k + 1 => refFlat κ₀ (refSeqFlat κ₀ a₀ k)

theorem gainFrac_le_half {κ₀ a : ℝ} (hκ0 : 0 ≤ κ₀) (hκ : κ₀ ≤ 1 / 2) : κ₀ * min (a / 4) 1 ≤ 1 / 2 := by
  have := min_le_right (a / 4) 1
  nlinarith [mul_le_mul_of_nonneg_left this hκ0]

theorem refFlat_pos {κ₀ a : ℝ} (hκ0 : 0 ≤ κ₀) (hκ : κ₀ ≤ 1 / 2) (ha : 0 < a) : 0 < refFlat κ₀ a := by
  have := gainFrac_le_half (a := a) hκ0 hκ
  unfold refFlat
  exact div_pos ha (by linarith)

/-- **The Migdal–Kadanoff step carries flat admissibility, with gain.** Let `W` be admissible at `a`. Let `P` agree on
`(−1, 1)` with a positive multiple of `convT (W⁴)` (the first two-fold class convolution of the fourth power), and
`W₁` with a positive multiple of `convT P` (the second), both `C¹` on `[−1, 1]`. Under `FlatGain κ₀`, `W₁` is
admissible at `refFlat κ₀ a`. -/
theorem mk_step_flat {κ₀ : ℝ} (hκ0 : 0 ≤ κ₀) (hκ : κ₀ ≤ 1 / 2) (hgain : FlatGain κ₀)
    {W W' : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hW : FlatAdmissible W W' a)
    {P P' W₁ W₁' : ℝ → ℝ} {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (hPc : Continuous P) (hPd : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt P (P' y) (Icc (-1) 1) y)
    (hP'c : ContinuousOn P' (Icc (-1) 1))
    (hPeq : ∀ y ∈ Ioo (-1 : ℝ) 1, P y = μ * convT (fun t => W t ^ 4) y)
    (hW₁c : Continuous W₁) (hW₁d : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt W₁ (W₁' y) (Icc (-1) 1) y)
    (hW₁'c : ContinuousOn W₁' (Icc (-1) 1))
    (hW₁eq : ∀ y ∈ Ioo (-1 : ℝ) 1, W₁ y = ν * convT P y) :
    FlatAdmissible W₁ W₁' (refFlat κ₀ a) := by
  have ha4 : 0 < a / 4 := by positivity
  have hU := admissible_pow_four hW ha
  set κ₁ := κ₀ * min (a / 4) 1 with hκ₁
  have hκ₁1 : κ₁ < 1 := by have := gainFrac_le_half (a := a) hκ0 hκ; linarith
  have hκ₁' : 0 < 1 - κ₁ := by linarith
  have hg1 : ∀ ψ ∈ Ioo 0 π, κ₁ * (ψ * sin ψ * ellConv (fun t => W t ^ 4) ψ)
      ≤ projDef (fun t => W t ^ 4) ψ := fun ψ hψ => hgain _ _ _ ha4 hU ψ hψ
  have hP := admissible_of_convT hU ha4 hκ₁1 hg1 hμ hPc hPd hP'c hPeq
  have hc1 : 0 < 2 * (a / 4) / (1 - κ₁) := by positivity
  have hW₁ := admissible_of_convT hP hc1 (κ := 0) (by norm_num) (projDef_zero_gain hP) hν hW₁c hW₁d
    hW₁'c hW₁eq
  have e : 2 * (2 * (a / 4) / (1 - κ₁)) / (1 - 0) = refFlat κ₀ a := by
    unfold refFlat
    rw [← hκ₁]
    field_simp
    ring
  rw [e] at hW₁
  exact hW₁

/-- `refFlat κ₀ a ≥ a + b a²` on `(0, θ]` with `b = (κ₀/4) min(1, 4/θ)`. -/
theorem le_refFlat {κ₀ a θ : ℝ} (hκ0 : 0 ≤ κ₀) (hκ : κ₀ ≤ 1 / 2) (ha : 0 < a) (haθ : a ≤ θ) :
    a + κ₀ / 4 * min 1 (4 / θ) * a ^ 2 ≤ refFlat κ₀ a := by
  have hθ : 0 < θ := ha.trans_le haθ
  set x := κ₀ * min (a / 4) 1 with hx
  have hx2 : x ≤ 1 / 2 := gainFrac_le_half hκ0 hκ
  have hx0 : 0 ≤ x := mul_nonneg hκ0 (le_min (by positivity) zero_le_one)
  -- `x ≥ (κ₀/4) min(1, 4/θ) a`
  have hxa : κ₀ / 4 * min 1 (4 / θ) * a ≤ x := by
    rw [hx]
    rcases le_total (a / 4) 1 with h | h
    · rw [min_eq_left h]
      have : min 1 (4 / θ) ≤ 1 := min_le_left _ _
      nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ κ₀ / 4 * a)]
    · rw [min_eq_right h]
      have h4 : min 1 (4 / θ) ≤ 4 / θ := min_le_right _ _
      have : 4 / θ * a ≤ 4 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hθ]; nlinarith
      have hm0 : 0 ≤ min 1 (4 / θ) := le_min zero_le_one (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right h4 ha.le]
  -- `a/(1 − x) ≥ a(1 + x)`
  have h1x : 0 < 1 - x := by linarith
  unfold refFlat
  rw [← hx, le_div_iff₀ h1x]
  nlinarith [mul_le_mul_of_nonneg_left hxa (by positivity : (0 : ℝ) ≤ a), mul_nonneg hx0 ha.le,
    mul_nonneg (mul_nonneg hx0 ha.le) hx0]

end Chain

/-! ## 9. Trigonometric identity for the ellipse coordinates -/

section Link

theorem sqrt_one_sub_cos_sq {φ : ℝ} (hφ : φ ∈ Icc 0 π) : √(1 - cos φ ^ 2) = sin φ := by
  rw [show 1 - cos φ ^ 2 = sin φ ^ 2 by linarith [sin_sq_add_cos_sq φ], Real.sqrt_sq_eq_abs,
    abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi hφ.1 hφ.2)]

end Link

#print axioms curvGap_nonneg
#print axioms capF_concaveOn
#print axioms sphere_proj_gap

#print axioms ell_swap
#print axioms slice_moment_nonneg

#print axioms ell_bracket_le
#print axioms ellInt_swap
#print axioms ellInt_mono
#print axioms ellInt_outer_intervalIntegrable

#print axioms hasDerivAt_ellConv
#print axioms ibp_slice
#print axioms hasDerivAt_convQuot

#print axioms bulkB_nonpos
#print axioms neg_bulkB_le_proj
#print axioms gramInt_div_three_le_projDef
#print axioms neg_bulkB_le
#print axioms ellConv_pos
#print axioms convQuot_antitoneOn
#print axioms convQuot_lrWider_flat
#print axioms convQuot_lrWider_flat_two

#print axioms convT_bounds
#print axioms admissible_of_convT
#print axioms admissible_pow_four
#print axioms wilson_admissible
#print axioms FlatAdmissible.lrWider
#print axioms mk_step_flat
#print axioms le_refFlat

end MassGap.ConvolutionTransfer
