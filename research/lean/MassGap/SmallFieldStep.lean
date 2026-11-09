import Mathlib
import MassGap.OneStepZoom
import MassGap.OneLoopPrefactor

/-!
# MassGap.SmallFieldStep — one block-spin step at quadratic order, its small-field correction, and the window defect

The first rung of multiscale control for the Wilson action, in the weak-coupling small-field region with explicit
constants, after Bałaban [Balaban84a, Balaban87, Balaban89b]. The step is stated for any linear curl `T : E → F`
(the linearized plaquette map of the side-`2n` torus) and any linear block map `B : E → G` (axial or averaging,
onto the side-`n` torus), so every constant is uniform in `n`, in the dimension and in the choice of block map.
Declarations are in `MassGap.SmallFieldStep`.

## 1. The Gaussian step (proved, exact)

`flucCurl T B = T(ker B)` is the space of fluctuation curls. `bgCurl T B A = T A − P(T A)`, `P` the orthogonal
projection onto `flucCurl T B`, and `bgAct T B A = ‖bgCurl T B A‖²`.

* `bgCurl_eq_of_block_eq`: `bgCurl` reads `A` only through the block field `B A`.
* `exists_background`: every fibre `{B A' = B A}` holds a background `A₀` with `T A₀ = bgCurl T B A`.
* `bgAct_isLeast`: `bgAct T B A = min {‖T A'‖² : B A' = B A}`, the background-field action of the block field.
* `fluct_split`: for a background `A₀` and every fluctuation `z ∈ ker B`,
  `‖T(A₀ + z)‖² = bgAct T B A + ‖T z‖²`, the fluctuation action independent of the block field.
* `fibre_gauss`: for a map `ι : Z → ker B` and a measure on `Z`, both supplied by the caller,
  `∫ exp(−(β/2)‖T(A₀ + ι z)‖²) = exp(−(β/2) bgAct T B A) · ∫ exp(−(β/2)‖T(ι z)‖²)`.
  The module does not tie `ι` and the measure to Lebesgue measure on `ker B`, nor require `ι` to be onto the
  fibre. At quadratic order the effective density of the block field is `exp(−(β/2) bgAct)` at the same `β`
  times a factor that reads no block field; "shift `0`" means exactly this, that the Gaussian density keeps the
  coupling `β`. `bgAct` is a quadratic form in the block field; it is not the coarse Wilson action of the block
  field, and its identification with the coarse coupling is not made here.
* `bgAct_of_block_zero`, `bgAct_of_ker_bot`: the unit tests. With `B = 0` every curl is fluctuation and
  `bgAct = 0`; with `ker B = ⊥` nothing is integrated and `bgAct = ‖T A‖²`.

## 2. The small-field correction for `U(1)` (proved, explicit)

`wilsonU1 β θ = β Σ_p (1 − cos θ_p)` on plaquette angles `θ ∈ EuclideanSpace ℝ P`; `sfConst = 5/48`.

* `one_sub_cos_le`, `le_one_sub_cos`: for `|x| ≤ δ ≤ 1`,
  `(1 − sfConst δ²) x²/2 ≤ 1 − cos x ≤ x²/2`. The constant is twice the quartic remainder `5/96` of
  `Real.cos_bound`.
* `wilsonU1_le`, `le_wilsonU1`: on `|θ_p| ≤ δ ≤ 1`, `(β/2)(1 − sfConst δ²)‖θ‖² ≤ wilsonU1 β θ ≤ (β/2)‖θ‖²`.
* `largeField_cost`: a plaquette with `δ ≤ |θ| ≤ π` costs at least `(1 − sfConst δ²) δ²/2`.
* `smallField_step`: on a fibre, with a background `A₀`, a fluctuation `z` and `|T(A₀ + z)_p| ≤ δ ≤ 1`,
  `(β/2)(1 − sfConst δ²)(bgAct + ‖T z‖²) ≤ wilsonU1 β (T(A₀ + z)) ≤ (β/2)(bgAct + ‖T z‖²)`.
* `fibre_smallField`: on a measurable small-field set `S` of fluctuations,
  `e^{−(β/2) bgAct} ∫_S e^{−(β/2)‖T z‖²} ≤ ∫_S e^{−wilsonU1} ≤ e^{−(β'/2) bgAct} ∫_S e^{−(β'/2)‖T z‖²}`,
  `β' = β(1 − sfConst δ²)`.

## 3. The large-field hypothesis (stated) and the full fibre (proved from it)

`LargeFieldSuppressed μ S f η`: `∫_{Sᶜ} f ≤ η ∫_S f`, the fibre weight off the small-field set at most `η` times
the weight on it. `fibre_le_of_suppressed`: then `∫_S f ≤ ∫ f ≤ (1 + η) ∫_S f`. `oneStep_sandwich`: with the
suppression at `f = e^{−wilsonU1}`, the whole fibre integral lies between the lower Gaussian bound of
`fibre_smallField` and `(1 + η)` times its upper bound. The suppression is Bałaban's large-field estimate; it is
not proved here. `largeField_cost` is the energy side of it; the entropy side (the count of large-field sets
against `exp(−β (1 − sfConst δ²) δ²/2)` per large plaquette) is the open part.

## 4. The window defect (proved)

`ZoomRem d L φ b r`: `L β (2n) = n^d b β + L (φ β) n + r β n`.

* `defK_rem_step`: `defK d L β (w + 1) = defK d L (φ β) w + defK d r β w`. The slack of the step is the doubling
  defect of the remainder, not its size.
* `zoomRem_canonical`: every log-partition has a remainder form, with the remainder the whole difference.
  `zoomRem_zero_iff`: remainder `0` is `OneStepZoom.ExactZoom`.
* `defK_bulk`: an extensive remainder `n^d ρ β` has defect `0`. `defK_const`: a constant remainder `c` has defect
  `(2^d − 1) c` at every window, so a bounded remainder with `c ≠ 0` gives a slack that does not vanish.
  An error bound `|r β n| ≤ C n^d`, which is what the small-field sandwich gives on the log-partition, is
  therefore not a vanishing slack at any `C > 0`.
* `tendsto_defK_of_local`: `r β (2^w) − (2^w)^d ρ β → 0` gives `defK d r β w → 0`.
* `OneStepLocal N β₀ b r ρ`: at `β ≥ β₀`, `ZoomRem 4 (logZ N) (· − leanStep N) b r` and the remainder is
  extensive up to a vanishing part. `oneLoopAboveSlack_of_oneStepLocal`: it gives
  `OneLoopPrefactor.OneLoopAboveSlack N β₀ 1 (defK 4 r)`; `strongEnd_of_oneStepLocal_low` the strong end at
  `β₀ ≤ leanStep N`. `tendsto_window_diff_of_oneStepLocal`: it gives
  `D(β, w + 1) − D(β − leanStep N, w) → 0`, the two-sided form of `OneLoopAboveSlack` at prefactor `1`.
  `exists_tail`, `exists_extensive`: a sequence `u` with `2^4 u w − u (w + 1) → 0` is extensive up to a vanishing
  part, `u w − (2^w)^4 a → 0` for one `a`. `oneStepLocal_iff`: some `OneStepLocal N β₀ b r ρ` holds if and only if
  `D(β, w + 1) − D(β − leanStep N, w) → 0` at every `β ≥ β₀`. `OneStepLocal` is equivalent to the two-sided
  comparison at prefactor `1`: a restatement of it, not a discharge of it.

## What does not follow

* The shift `leanStep N`. At quadratic order the shift is `0` (`fibre_gauss`) in the sense that the Gaussian
  density of the block field keeps the same `β`; `bgAct` is not the coarse Wilson action, and its identification
  with the coarse coupling is not made here. This holds for `U(1)` and for each of the `N² − 1` linearized colour
  components of `SU(N)` alike. The one-loop shift comes from the background
  dependence of the fluctuation integral through the cubic and quartic vertices of the non-abelian curl, which the
  linear curl `T` does not have. That computation is not in this module.
* `OneStepLocal`. The small-field sandwich controls the effective action to a relative error `sfConst δ²`, which
  on the torus is an extensive error; `defK_const` shows such an error does not vanish in the defect. What the
  multiscale analysis must supply is that the remainder after the shift is a bulk term plus a part whose
  doubling defect vanishes.
* `LargeFieldSuppressed` at an `η` uniform in the volume. A per-fibre `η` independent of `n` is a Peierls-type
  bound; it is a hypothesis here.
* Any statement for the `SU(N)` Haar integral `RectWilson.ZR`: the module works with linear fields and does not
  build the exponential chart, the gauge fixing or the Jacobian.

DERIVED (module-wide): `0` the limits, signs and the zero field; `1` the unit, the successor and the small-field
ceiling `δ ≤ 1` of `Real.cos_bound`; `2` the doubling, the square and the Gaussian half; `4` the spacetime
dimension; `5/48 = 2 · 5/96` the small-field constant `sfConst`, twice the quartic remainder of `Real.cos_bound`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.SmallFieldStep

open Filter Topology MeasureTheory
open MassGap.OneStepZoom (defK defK_wilson)
open MassGap.OneLoopInput (leanStep)
open MassGap.OneLoopPrefactor (OneLoopAboveSlack strongEnd_of_oneLoopAboveSlack_low)

/-! ## 1. The Gaussian step -/

section Gauss

variable {E F G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup G] [Module ℝ G]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The fluctuation curls**: the curls of the fields the block map does not see. -/
abbrev flucCurl (T : E →ₗ[ℝ] F) (B : E →ₗ[ℝ] G) : Submodule ℝ F := (LinearMap.ker B).map T

/-- **The background curl**: the curl of `A` with its fluctuation part projected out. -/
def bgCurl (T : E →ₗ[ℝ] F) (B : E →ₗ[ℝ] G) (A : E) : F :=
  T A - (flucCurl T B).starProjection (T A)

/-- **The background action** of the block field of `A`. DERIVED: `2` the square. -/
def bgAct (T : E →ₗ[ℝ] F) (B : E →ₗ[ℝ] G) (A : E) : ℝ := ‖bgCurl T B A‖ ^ 2

/-- **The background curl is orthogonal to every fluctuation curl.** -/
theorem bgCurl_mem_orthogonal (T : E →ₗ[ℝ] F) (B : E →ₗ[ℝ] G) (A : E) :
    bgCurl T B A ∈ (flucCurl T B)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal _

/-- **The background curl reads only the block field.** -/
theorem bgCurl_eq_of_block_eq (T : E →ₗ[ℝ] F) (B : E →ₗ[ℝ] G) {A A' : E} (h : B A = B A') :
    bgCurl T B A = bgCurl T B A' := by
  have hk : A - A' ∈ LinearMap.ker B := by
    rw [LinearMap.mem_ker, map_sub, h, sub_self]
  have hw : T A - T A' ∈ flucCurl T B := by
    rw [← map_sub]; exact Submodule.mem_map_of_mem hk
  have hp : (flucCurl T B).starProjection (T A - T A') = T A - T A' :=
    (Submodule.starProjection_eq_self_iff).2 hw
  rw [map_sub] at hp
  unfold bgCurl
  rw [sub_eq_sub_iff_sub_eq_sub, hp]

/-- **The background action reads only the block field.** DERIVED: `2` the square. -/
theorem bgAct_eq_of_block_eq (T : E →ₗ[ℝ] F) (B : E →ₗ[ℝ] G) {A A' : E} (h : B A = B A') :
    bgAct T B A = bgAct T B A' := by
  unfold bgAct; rw [bgCurl_eq_of_block_eq T B h]

/-- **Pythagoras on the curl**: the fine action is the background action plus the fluctuation part.
DERIVED: `2` the square. -/
theorem curl_split (T : E →ₗ[ℝ] F) (B : E →ₗ[ℝ] G) (A : E) :
    ‖T A‖ ^ 2 = bgAct T B A + ‖(flucCurl T B).starProjection (T A)‖ ^ 2 := by
  have h0 : inner ℝ (bgCurl T B A) ((flucCurl T B).starProjection (T A)) = 0 :=
    Submodule.starProjection_inner_eq_zero _ _ (Submodule.starProjection_apply_mem _ _)
  have e : T A = bgCurl T B A + (flucCurl T B).starProjection (T A) := by
    unfold bgCurl; abel
  unfold bgAct
  conv_lhs => rw [e]
  simp only [sq]
  exact norm_add_sq_eq_norm_sq_add_norm_sq_real h0

/-- **Every fibre holds a background**: a field with the same block field whose curl is the background curl. -/
theorem exists_background (T : E →ₗ[ℝ] F) (B : E →ₗ[ℝ] G) (A : E) :
    ∃ A₀ : E, B A₀ = B A ∧ T A₀ = bgCurl T B A := by
  obtain ⟨z, hz, hTz⟩ := (Submodule.mem_map).1
    (Submodule.starProjection_apply_mem (flucCurl T B) (T A))
  refine ⟨A - z, ?_, ?_⟩
  · rw [map_sub, LinearMap.mem_ker.1 hz, sub_zero]
  · rw [map_sub, hTz]; rfl

/-- **The background action is the least fine action on the fibre.** DERIVED: `2` the square. -/
theorem bgAct_isLeast (T : E →ₗ[ℝ] F) (B : E →ₗ[ℝ] G) (A : E) :
    IsLeast {s : ℝ | ∃ A' : E, B A' = B A ∧ s = ‖T A'‖ ^ 2} (bgAct T B A) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨A₀, hB, hT⟩ := exists_background T B A
    exact ⟨A₀, hB, by rw [hT]; rfl⟩
  · rintro s ⟨A', hB, rfl⟩
    rw [curl_split T B A', bgAct_eq_of_block_eq T B hB]
    exact le_add_of_nonneg_right (sq_nonneg _)

/-- **The fluctuation decouples**: on the fibre through a background `A₀`, the fine action is the background
action plus the fluctuation action. DERIVED: `2` the square. -/
theorem fluct_split (T : E →ₗ[ℝ] F) (B : E →ₗ[ℝ] G) {A A₀ z : E} (h₀ : T A₀ = bgCurl T B A)
    (hz : z ∈ LinearMap.ker B) : ‖T (A₀ + z)‖ ^ 2 = bgAct T B A + ‖T z‖ ^ 2 := by
  have hw : T z ∈ flucCurl T B := Submodule.mem_map_of_mem hz
  have h0 : inner ℝ (T A₀) (T z) = 0 := by
    rw [h₀]; exact Submodule.inner_left_of_mem_orthogonal hw (bgCurl_mem_orthogonal T B A)
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_real h0
  rw [map_add]
  unfold bgAct
  rw [← h₀]
  simp only [sq]
  linarith

/-- **The Gaussian fibre integral factorizes**: the background weight at the same coupling `β` times a
fluctuation integral that reads no block field. The coupling shift at quadratic order is `0`.
DERIVED: `2` the square and the Gaussian half. -/
theorem fibre_gauss (T : E →ₗ[ℝ] F) (B : E →ₗ[ℝ] G) {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (ι : Z → E) (hι : ∀ z, ι z ∈ LinearMap.ker B) {A A₀ : E} (h₀ : T A₀ = bgCurl T B A) (β : ℝ) :
    ∫ z, Real.exp (-(β / 2) * ‖T (A₀ + ι z)‖ ^ 2) ∂μ
      = Real.exp (-(β / 2) * bgAct T B A) * ∫ z, Real.exp (-(β / 2) * ‖T (ι z)‖ ^ 2) ∂μ := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [fluct_split T B h₀ (hι z), mul_add, Real.exp_add]

/-- **Unit test, no block field**: with `B = 0` every curl is a fluctuation curl and the background action is `0`.
DERIVED: `0` the zero map. -/
theorem bgAct_of_block_zero (T : E →ₗ[ℝ] F) (A : E) : bgAct T (0 : E →ₗ[ℝ] G) A = 0 := by
  have hA : A ∈ LinearMap.ker (0 : E →ₗ[ℝ] G) := by simp
  have hw : T A ∈ flucCurl T (0 : E →ₗ[ℝ] G) := Submodule.mem_map_of_mem hA
  unfold bgAct bgCurl
  rw [(Submodule.starProjection_eq_self_iff).2 hw, sub_self, norm_zero]
  norm_num

/-- **Unit test, no fluctuation**: with `ker B = ⊥` nothing is integrated and the background action is the fine
action. DERIVED: `2` the square. -/
theorem bgAct_of_ker_bot (T : E →ₗ[ℝ] F) (B : E →ₗ[ℝ] G) (hB : LinearMap.ker B = ⊥) (A : E) :
    bgAct T B A = ‖T A‖ ^ 2 := by
  have hW : flucCurl T B = ⊥ := by simp [flucCurl, hB]
  have hp : (flucCurl T B).starProjection (T A) = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff, hW, Submodule.bot_orthogonal_eq_top]
    exact Submodule.mem_top
  unfold bgAct bgCurl
  rw [hp, sub_zero]

end Gauss

/-! ## 2. The small-field correction for `U(1)` -/

/-- **The small-field constant.** DERIVED: `5/48 = 2 · 5/96`, twice the quartic remainder constant `5/96` of
`Real.cos_bound`. -/
def sfConst : ℝ := 5 / 48

/-- DERIVED: `0` the sign. -/
theorem sfConst_pos : 0 < sfConst := by unfold sfConst; norm_num

/-- **The plaquette cost is at most quadratic.** DERIVED: `1` the unit; `2` the square and the half. -/
theorem one_sub_cos_le (x : ℝ) : 1 - Real.cos x ≤ x ^ 2 / 2 := by
  linarith [Real.one_sub_sq_div_two_le_cos (x := x)]

/-- **The plaquette cost is quadratic up to the relative error `sfConst δ²` on `|x| ≤ δ ≤ 1`.**
DERIVED: `1` the unit and the ceiling of `Real.cos_bound`; `2` the square and the half. -/
theorem le_one_sub_cos {x δ : ℝ} (hx : |x| ≤ δ) (hδ : δ ≤ 1) :
    (1 - sfConst * δ ^ 2) * (x ^ 2 / 2) ≤ 1 - Real.cos x := by
  have hb := Real.cos_bound (hx.trans hδ)
  have h1 := (abs_le.1 hb).2
  have hx2 : x ^ 2 ≤ δ ^ 2 := by
    rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg x) hx 2
  have h4 : |x| ^ 4 = x ^ 2 * x ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]; ring
  have hq : x ^ 2 * x ^ 2 ≤ δ ^ 2 * x ^ 2 := mul_le_mul_of_nonneg_right hx2 (sq_nonneg x)
  unfold sfConst
  rw [h4] at h1
  nlinarith

/-- **The `U(1)` Wilson action** at plaquette angles `θ`. DERIVED: `1` the unit. -/
def wilsonU1 {P : Type*} [Fintype P] (β : ℝ) (θ : EuclideanSpace ℝ P) : ℝ :=
  β * ∑ p, (1 - Real.cos (θ p))

/-- **The Wilson action is at most the Gaussian action.** DERIVED: `0` the sign; `2` the square and the half. -/
theorem wilsonU1_le {P : Type*} [Fintype P] {β : ℝ} (hβ : 0 ≤ β) (θ : EuclideanSpace ℝ P) :
    wilsonU1 β θ ≤ β / 2 * ‖θ‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, wilsonU1]
  have : ∑ p, (1 - Real.cos (θ p)) ≤ ∑ p, (θ p) ^ 2 / 2 :=
    Finset.sum_le_sum fun p _ => one_sub_cos_le _
  calc β * ∑ p, (1 - Real.cos (θ p)) ≤ β * ∑ p, (θ p) ^ 2 / 2 := mul_le_mul_of_nonneg_left this hβ
    _ = β / 2 * ∑ p, (θ p) ^ 2 := by rw [Finset.mul_sum, Finset.mul_sum]; congr 1; funext p; ring

/-- **On the small-field region the Wilson action is at least the Gaussian action at `β(1 − sfConst δ²)`.**
DERIVED: `0` the sign; `1` the unit and the ceiling of `Real.cos_bound`; `2` the square and the half. -/
theorem le_wilsonU1 {P : Type*} [Fintype P] {β δ : ℝ} (hβ : 0 ≤ β) (hδ : δ ≤ 1)
    {θ : EuclideanSpace ℝ P} (hθ : ∀ p, |θ p| ≤ δ) :
    β / 2 * (1 - sfConst * δ ^ 2) * ‖θ‖ ^ 2 ≤ wilsonU1 β θ := by
  rw [EuclideanSpace.real_norm_sq_eq, wilsonU1]
  have : ∑ p, (1 - sfConst * δ ^ 2) * ((θ p) ^ 2 / 2) ≤ ∑ p, (1 - Real.cos (θ p)) :=
    Finset.sum_le_sum fun p _ => le_one_sub_cos (hθ p) hδ
  calc β / 2 * (1 - sfConst * δ ^ 2) * ∑ p, (θ p) ^ 2
      = β * ∑ p, (1 - sfConst * δ ^ 2) * ((θ p) ^ 2 / 2) := by
        rw [Finset.mul_sum, Finset.mul_sum]; congr 1; funext p; ring
    _ ≤ β * ∑ p, (1 - Real.cos (θ p)) := mul_le_mul_of_nonneg_left this hβ

/-- **A large plaquette costs at least `(1 − sfConst δ²) δ²/2`**, on `δ ≤ |x| ≤ π`, `0 ≤ δ ≤ 1`.
DERIVED: `0` the sign; `1` the unit and the ceiling of `Real.cos_bound`; `2` the square and the half. -/
theorem largeField_cost {x δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1) (hlo : δ ≤ |x|) (hhi : |x| ≤ Real.pi) :
    (1 - sfConst * δ ^ 2) * (δ ^ 2 / 2) ≤ 1 - Real.cos x := by
  have hc : Real.cos |x| ≤ Real.cos δ := Real.cos_le_cos_of_nonneg_of_le_pi hδ0 hhi hlo
  rw [Real.cos_abs] at hc
  have := le_one_sub_cos (x := δ) (δ := δ) (by rw [abs_of_nonneg hδ0]) hδ
  linarith

section Step

variable {E G P : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup G] [Module ℝ G] [Fintype P]

/-- **The small-field one-step bound**: on the fibre through a background `A₀`, at a small-field fluctuation `z`,
the fine Wilson action is the background action plus the fluctuation action at `β`, up to the relative error
`sfConst δ²`. Uniform in the lattice: no constant reads `T`, `B` or the volume.
DERIVED: `0` the sign; `1` the unit and the ceiling of `Real.cos_bound`; `2` the square and the half. -/
theorem smallField_step (T : E →ₗ[ℝ] EuclideanSpace ℝ P) (B : E →ₗ[ℝ] G) {A A₀ z : E}
    (h₀ : T A₀ = bgCurl T B A) (hz : z ∈ LinearMap.ker B) {β δ : ℝ} (hβ : 0 ≤ β) (hδ : δ ≤ 1)
    (hsf : ∀ p, |T (A₀ + z) p| ≤ δ) :
    β / 2 * (1 - sfConst * δ ^ 2) * (bgAct T B A + ‖T z‖ ^ 2) ≤ wilsonU1 β (T (A₀ + z)) ∧
      wilsonU1 β (T (A₀ + z)) ≤ β / 2 * (bgAct T B A + ‖T z‖ ^ 2) := by
  rw [← fluct_split T B h₀ hz]
  exact ⟨le_wilsonU1 hβ hδ hsf, wilsonU1_le hβ _⟩

/-- **The small-field fibre integral**: on a measurable set `S` of small-field fluctuations, the fibre integral of
the Wilson weight lies between the Gaussian fibre integrals at `β` and at `β(1 − sfConst δ²)`, each factorized into
a background weight and a fluctuation integral. DERIVED: `0` the sign; `1` the unit and the ceiling of
`Real.cos_bound`; `2` the square and the Gaussian half. -/
theorem fibre_smallField (T : E →ₗ[ℝ] EuclideanSpace ℝ P) (B : E →ₗ[ℝ] G) {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (ι : Z → E) (hι : ∀ z, ι z ∈ LinearMap.ker B) {A A₀ : E} (h₀ : T A₀ = bgCurl T B A)
    {β δ : ℝ} (hβ : 0 ≤ β) (hδ : δ ≤ 1) {S : Set Z} (hS : MeasurableSet S)
    (hsf : ∀ z ∈ S, ∀ p, |T (A₀ + ι z) p| ≤ δ)
    (hWi : Integrable (fun z => Real.exp (-wilsonU1 β (T (A₀ + ι z)))) (μ.restrict S))
    (hGi : Integrable (fun z => Real.exp (-(β / 2 * (1 - sfConst * δ ^ 2)) * ‖T (A₀ + ι z)‖ ^ 2))
      (μ.restrict S)) :
    Real.exp (-(β / 2) * bgAct T B A) * ∫ z in S, Real.exp (-(β / 2) * ‖T (ι z)‖ ^ 2) ∂μ
        ≤ ∫ z in S, Real.exp (-wilsonU1 β (T (A₀ + ι z))) ∂μ ∧
      ∫ z in S, Real.exp (-wilsonU1 β (T (A₀ + ι z))) ∂μ
        ≤ Real.exp (-(β / 2 * (1 - sfConst * δ ^ 2)) * bgAct T B A) *
          ∫ z in S, Real.exp (-(β / 2 * (1 - sfConst * δ ^ 2)) * ‖T (ι z)‖ ^ 2) ∂μ := by
  constructor
  · rw [← fibre_gauss T B (μ.restrict S) ι hι h₀ β]
    refine integral_mono_of_nonneg (Eventually.of_forall fun z => (Real.exp_pos _).le) hWi ?_
    refine (ae_restrict_iff' hS).2 (Eventually.of_forall fun z hz => ?_)
    refine Real.exp_le_exp.2 ?_
    have := (smallField_step T B h₀ (hι z) hβ hδ (hsf z hz)).2
    rw [← fluct_split T B h₀ (hι z)] at this
    linarith
  · have hg := fibre_gauss T B (μ.restrict S) ι hι h₀ (β * (1 - sfConst * δ ^ 2))
    have e1 : -(β * (1 - sfConst * δ ^ 2) / 2) = -(β / 2 * (1 - sfConst * δ ^ 2)) := by ring
    rw [e1] at hg
    rw [← hg]
    refine integral_mono_of_nonneg (Eventually.of_forall fun z => (Real.exp_pos _).le) hGi ?_
    refine (ae_restrict_iff' hS).2 (Eventually.of_forall fun z hz => ?_)
    refine Real.exp_le_exp.2 ?_
    have := le_wilsonU1 hβ hδ (hsf z hz)
    linarith

end Step

/-! ## 3. The large-field hypothesis and the full fibre -/

/-- **Large-field suppression on one fibre**: the weight off the small-field set `S` is at most `η` times the
weight on it. Bałaban's large-field estimate in its one-fibre form; a hypothesis, not proved here. -/
def LargeFieldSuppressed {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) (S : Set Z) (f : Z → ℝ) (η : ℝ) :
    Prop :=
  ∫ z in Sᶜ, f z ∂μ ≤ η * ∫ z in S, f z ∂μ

/-- **The suppressed fibre is the small-field fibre up to the factor `1 + η`.** DERIVED: `0` the sign; `1` the
unit. -/
theorem fibre_le_of_suppressed {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} {S : Set Z} {f : Z → ℝ} {η : ℝ}
    (hS : MeasurableSet S) (hfi : Integrable f μ) (hf : ∀ z, 0 ≤ f z) (h : LargeFieldSuppressed μ S f η) :
    ∫ z in S, f z ∂μ ≤ ∫ z, f z ∂μ ∧ ∫ z, f z ∂μ ≤ (1 + η) * ∫ z in S, f z ∂μ := by
  have hsplit := integral_add_compl hS hfi
  have hc : 0 ≤ ∫ z in Sᶜ, f z ∂μ := integral_nonneg hf
  unfold LargeFieldSuppressed at h
  constructor <;> nlinarith

section Sandwich

variable {E G P : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup G] [Module ℝ G] [Fintype P]

/-- **One step, small field plus suppressed large field**: the whole fibre integral of the Wilson weight lies
between the lower Gaussian bound at `β` on the small-field set and `1 + η` times the upper Gaussian bound at
`β(1 − sfConst δ²)`. DERIVED: `0` the sign; `1` the unit and the ceiling of `Real.cos_bound`; `2` the square and
the Gaussian half. -/
theorem oneStep_sandwich (T : E →ₗ[ℝ] EuclideanSpace ℝ P) (B : E →ₗ[ℝ] G) {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (ι : Z → E) (hι : ∀ z, ι z ∈ LinearMap.ker B) {A A₀ : E} (h₀ : T A₀ = bgCurl T B A)
    {β δ η : ℝ} (hβ : 0 ≤ β) (hδ : δ ≤ 1) {S : Set Z} (hS : MeasurableSet S)
    (hsf : ∀ z ∈ S, ∀ p, |T (A₀ + ι z) p| ≤ δ)
    (hWi : Integrable (fun z => Real.exp (-wilsonU1 β (T (A₀ + ι z)))) μ)
    (hGi : Integrable (fun z => Real.exp (-(β / 2 * (1 - sfConst * δ ^ 2)) * ‖T (A₀ + ι z)‖ ^ 2))
      (μ.restrict S))
    (hη : 0 ≤ η) (hLF : LargeFieldSuppressed μ S (fun z => Real.exp (-wilsonU1 β (T (A₀ + ι z)))) η) :
    Real.exp (-(β / 2) * bgAct T B A) * ∫ z in S, Real.exp (-(β / 2) * ‖T (ι z)‖ ^ 2) ∂μ
        ≤ ∫ z, Real.exp (-wilsonU1 β (T (A₀ + ι z))) ∂μ ∧
      ∫ z, Real.exp (-wilsonU1 β (T (A₀ + ι z))) ∂μ
        ≤ (1 + η) * (Real.exp (-(β / 2 * (1 - sfConst * δ ^ 2)) * bgAct T B A) *
          ∫ z in S, Real.exp (-(β / 2 * (1 - sfConst * δ ^ 2)) * ‖T (ι z)‖ ^ 2) ∂μ) := by
  obtain ⟨hlo, hhi⟩ := fibre_smallField T B μ ι hι h₀ hβ hδ hS hsf hWi.restrict hGi
  obtain ⟨h1, h2⟩ := fibre_le_of_suppressed hS hWi (fun z => (Real.exp_pos _).le) hLF
  refine ⟨hlo.trans h1, h2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hhi (by linarith)

end Sandwich

/-! ## 4. The window defect -/

/-- **A zoom with remainder**: the side-`2n` log-partition at `β` is the bulk, the side-`n` log-partition at `φ β`,
and a remainder `r`. DERIVED: `2` the doubling; `d` the dimension. -/
def ZoomRem (d : ℕ) (L : ℝ → ℕ → ℝ) (φ b : ℝ → ℝ) (r : ℝ → ℕ → ℝ) : Prop :=
  ∀ β : ℝ, ∀ n : ℕ, L β (2 * n) = (n : ℝ) ^ d * b β + L (φ β) n + r β n

/-- **The step with remainder**: the slack is the doubling defect of the remainder. DERIVED: `1` the step. -/
theorem defK_rem_step {d : ℕ} {L : ℝ → ℕ → ℝ} {φ b : ℝ → ℝ} {r : ℝ → ℕ → ℝ} (h : ZoomRem d L φ b r)
    (β : ℝ) (w : ℕ) : defK d L β (w + 1) = defK d L (φ β) w + defK d r β w := by
  unfold defK
  have e : (2 : ℕ) ^ (w + 1) = 2 * 2 ^ w := by ring
  rw [e, h β (2 ^ w), h β (2 * 2 ^ w)]
  push_cast
  rw [mul_pow]
  ring

/-- **Every log-partition has a remainder form**, with the remainder the whole difference; the form alone carries
no content. DERIVED: `0` the bulk; `2` the doubling. -/
theorem zoomRem_canonical (d : ℕ) (L : ℝ → ℕ → ℝ) (φ : ℝ → ℝ) :
    ZoomRem d L φ (fun _ => 0) (fun β n => L β (2 * n) - L (φ β) n) := by
  intro β n; ring

/-- **A zoom with remainder `0` is an exact zoom.** DERIVED: `0` the remainder. -/
theorem zoomRem_zero_iff (d : ℕ) (L : ℝ → ℕ → ℝ) (φ b : ℝ → ℝ) :
    ZoomRem d L φ b (fun _ _ => 0) ↔ MassGap.OneStepZoom.ExactZoom d L φ b := by
  unfold ZoomRem MassGap.OneStepZoom.ExactZoom
  simp only [add_zero]

/-- **An extensive remainder has defect `0`.** DERIVED: `0` the defect; `d` the dimension. -/
theorem defK_bulk (d : ℕ) (ρ : ℝ → ℝ) (β : ℝ) (w : ℕ) :
    defK d (fun β' (n : ℕ) => (n : ℝ) ^ d * ρ β') β w = 0 := by
  unfold defK
  push_cast
  rw [mul_pow]
  ring

/-- **A constant remainder has defect `(2^d − 1) c` at every window**: a bounded remainder that is not extensive
gives a slack that does not vanish. DERIVED: `1` the unit; `2` the doubling; `d` the dimension. -/
theorem defK_const (d : ℕ) (c β : ℝ) (w : ℕ) : defK d (fun _ _ => c) β w = ((2 : ℝ) ^ d - 1) * c := by
  unfold defK; ring

/-- **A remainder extensive up to a vanishing part has a vanishing defect.** DERIVED: `0` the limit; `1` the
successor; `2` the doubling; `d` the dimension. -/
theorem tendsto_defK_of_local {d : ℕ} {r : ℝ → ℕ → ℝ} {ρ : ℝ → ℝ} {β : ℝ}
    (hs : Tendsto (fun w : ℕ => r β (2 ^ w) - ((2 : ℝ) ^ w) ^ d * ρ β) atTop (𝓝 0)) :
    Tendsto (defK d r β) atTop (𝓝 0) := by
  set s : ℕ → ℝ := fun w => r β (2 ^ w) - ((2 : ℝ) ^ w) ^ d * ρ β with hsdef
  have e : defK d r β = fun w => (2 : ℝ) ^ d * s w - s (w + 1) := by
    funext w
    simp only [hsdef, defK]
    have e2 : (2 : ℕ) * 2 ^ w = 2 ^ (w + 1) := by ring
    have hp : (2 : ℝ) ^ d * ((2 : ℝ) ^ w) ^ d = ((2 : ℝ) ^ (w + 1)) ^ d := by
      rw [← mul_pow, ← pow_succ']
    rw [e2, ← hp]
    ring
  rw [e]
  have h1 : Tendsto (fun w => s (w + 1)) atTop (𝓝 0) := hs.comp (tendsto_add_atTop_nat 1)
  have := (hs.const_mul ((2 : ℝ) ^ d)).sub h1
  simpa using this

/-- **The one-step comparison in remainder form**: past `β₀`, the side-`2n` Wilson log-partition at `β` is a bulk
plus the side-`n` log-partition at `β − leanStep N` plus a remainder that is extensive up to a part vanishing along
the windows. Equivalent to the two-sided comparison (`oneStepLocal_iff`); a restatement, not a discharge.
DERIVED: `0` the limit; `2` the doubling; `4` the dimension. -/
def OneStepLocal (N : ℕ) (β₀ : ℝ) (b : ℝ → ℝ) (r : ℝ → ℕ → ℝ) (ρ : ℝ → ℝ) : Prop :=
  (∀ β : ℝ, β₀ ≤ β → ∀ n : ℕ, BondMove.logZ N β (2 * n)
      = (n : ℝ) ^ 4 * b β + BondMove.logZ N (β - leanStep N) n + r β n) ∧
    ∀ β : ℝ, β₀ ≤ β → Tendsto (fun w : ℕ => r β (2 ^ w) - ((2 : ℝ) ^ w) ^ 4 * ρ β) atTop (𝓝 0)

/-- The window step under `OneStepLocal`. DERIVED: `1` the step; `4` the dimension. -/
theorem window_step_of_oneStepLocal {N : ℕ} {β₀ : ℝ} {b : ℝ → ℝ} {r : ℝ → ℕ → ℝ} {ρ : ℝ → ℝ}
    (h : OneStepLocal N β₀ b r ρ) {β : ℝ} (hβ : β₀ ≤ β) (w : ℕ) :
    CouplingTower.windowCoupling N β (w + 1)
      = CouplingTower.windowCoupling N (β - leanStep N) w + defK 4 r β w := by
  rw [← defK_wilson]
  unfold defK
  have e : (2 : ℕ) ^ (w + 1) = 2 * 2 ^ w := by ring
  rw [e, h.1 β hβ (2 ^ w), h.1 β hβ (2 * 2 ^ w)]
  push_cast
  rw [mul_pow]
  ring

/-- **`OneStepLocal` gives `OneLoopAboveSlack` at prefactor `1`** with the slack the remainder's defect.
DERIVED: `1` the prefactor; `4` the dimension. -/
theorem oneLoopAboveSlack_of_oneStepLocal {N : ℕ} {β₀ : ℝ} {b : ℝ → ℝ} {r : ℝ → ℕ → ℝ} {ρ : ℝ → ℝ}
    (h : OneStepLocal N β₀ b r ρ) : OneLoopAboveSlack N β₀ (fun _ => 1) (fun β w => defK 4 r β w) := by
  refine ⟨fun β hβ => tendsto_defK_of_local (h.2 β hβ), fun β hβ w _ => ?_⟩
  rw [window_step_of_oneStepLocal h hβ w, one_mul]

/-- **The strong end from `OneStepLocal` at a low start.** DERIVED: `2` the least rank. -/
theorem strongEnd_of_oneStepLocal_low {N : ℕ} (hN : 2 ≤ N) {β₀ : ℝ} {b : ℝ → ℝ} {r : ℝ → ℕ → ℝ}
    {ρ : ℝ → ℝ} (h : OneStepLocal N β₀ b r ρ) (hle : β₀ ≤ leanStep N) : CouplingTower.StrongEnd N :=
  strongEnd_of_oneLoopAboveSlack_low hN (oneLoopAboveSlack_of_oneStepLocal h) hle

/-- **`OneStepLocal` is at least the two-sided comparison**: `D(β, w + 1) − D(β − leanStep N, w) → 0`, the form
of `OneLoopAboveSlack` at prefactor `1` with the slack on both sides. DERIVED: `0` the limit; `1` the step. -/
theorem tendsto_window_diff_of_oneStepLocal {N : ℕ} {β₀ : ℝ} {b : ℝ → ℝ} {r : ℝ → ℕ → ℝ} {ρ : ℝ → ℝ}
    (h : OneStepLocal N β₀ b r ρ) {β : ℝ} (hβ : β₀ ≤ β) :
    Tendsto (fun w : ℕ => CouplingTower.windowCoupling N β (w + 1)
      - CouplingTower.windowCoupling N (β - leanStep N) w) atTop (𝓝 0) := by
  have e : (fun w : ℕ => CouplingTower.windowCoupling N β (w + 1)
      - CouplingTower.windowCoupling N (β - leanStep N) w) = defK 4 r β := by
    funext w; rw [window_step_of_oneStepLocal h hβ w]; ring
  rw [e]
  exact tendsto_defK_of_local (h.2 β hβ)

/-- **A vanishing defect has a geometric tail**: for `e → 0` there is `s → 0` with `2^4 s w − s (w + 1) = e w`,
`s w = Σ_j e (w + j) 2^{−4(j+1)}`. DERIVED: `0` the limit; `1` the successor; `2^4` the doubling defect's factor
at `d = 4`. -/
theorem exists_tail {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) :
    ∃ s : ℕ → ℝ, Tendsto s atTop (𝓝 0) ∧ ∀ w : ℕ, (2 : ℝ) ^ 4 * s w - s (w + 1) = e w := by
  set q : ℝ := ((2 : ℝ) ^ 4)⁻¹ with hq
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq1 : q < 1 := by rw [hq]; norm_num
  obtain ⟨M, hM⟩ := he.abs.bddAbove_range
  have hb : ∀ k, |e k| ≤ M := fun k => hM ⟨k, rfl⟩
  have hg : Summable fun j : ℕ => M * q ^ (j + 1) :=
    ((summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hq0 hq1)).mul_left M
  have hbound : ∀ w j : ℕ, ‖e (w + j) * q ^ (j + 1)‖ ≤ M * q ^ (j + 1) := by
    intro w j
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hq0 _)]
    exact mul_le_mul_of_nonneg_right (hb _) (pow_nonneg hq0 _)
  have hsum : ∀ w : ℕ, Summable fun j : ℕ => e (w + j) * q ^ (j + 1) :=
    fun w => Summable.of_norm_bounded hg (hbound w)
  have hab : ∀ j : ℕ, Tendsto (fun w : ℕ => e (w + j) * q ^ (j + 1)) atTop (𝓝 ((fun _ : ℕ => (0 : ℝ)) j)) := by
    intro j
    have h1 : Tendsto (fun w : ℕ => e (w + j)) atTop (𝓝 0) := he.comp (tendsto_add_atTop_nat j)
    simpa using h1.mul_const (q ^ (j + 1))
  refine ⟨fun w => ∑' j : ℕ, e (w + j) * q ^ (j + 1), ?_, fun w => ?_⟩
  · have := tendsto_tsum_of_dominated_convergence (f := fun w j => e (w + j) * q ^ (j + 1))
      (g := fun _ => (0 : ℝ)) hg hab (Eventually.of_forall fun w j => hbound w j)
    simpa using this
  · have e1 : ∑' j : ℕ, e (w + (j + 1)) * q ^ (j + 1 + 1)
        = q * ∑' j : ℕ, e (w + 1 + j) * q ^ (j + 1) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun j => ?_
      rw [show w + (j + 1) = w + 1 + j by ring]
      ring
    have h16 : (2 : ℝ) ^ 4 * q = 1 := by rw [hq]; norm_num
    simp only
    rw [(hsum w).tsum_eq_zero_add]
    simp only [add_zero, zero_add, pow_one]
    rw [e1]
    linear_combination (e w + ∑' j : ℕ, e (w + 1 + j) * q ^ (j + 1)) * h16

/-- **A sequence whose doubling defect vanishes is extensive up to a vanishing part.** DERIVED: `0` the limit;
`1` the successor; `2^4` the doubling defect's factor at `d = 4`. -/
theorem exists_extensive {u e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hu : ∀ w : ℕ, (2 : ℝ) ^ 4 * u w - u (w + 1) = e w) :
    ∃ a : ℝ, Tendsto (fun w : ℕ => u w - ((2 : ℝ) ^ w) ^ 4 * a) atTop (𝓝 0) := by
  obtain ⟨s, hs, hse⟩ := exists_tail he
  refine ⟨u 0 - s 0, ?_⟩
  have ht : ∀ w : ℕ, u w - s w = ((2 : ℝ) ^ w) ^ 4 * (u 0 - s 0) := by
    intro w
    induction w with
    | zero => simp
    | succ k ih =>
      have h1 := hu k
      have h2 := hse k
      have hp : ((2 : ℝ) ^ (k + 1)) ^ 4 = (2 : ℝ) ^ 4 * ((2 : ℝ) ^ k) ^ 4 := by ring
      rw [hp, mul_assoc, ← ih]
      linarith
  have : (fun w : ℕ => u w - ((2 : ℝ) ^ w) ^ 4 * (u 0 - s 0)) = s := by
    funext w; linarith [ht w]
  rw [this]; exact hs

/-- **`OneStepLocal` is exactly the two-sided comparison**: some bulk, remainder and density make it hold if and
only if `D(β, w + 1) − D(β − leanStep N, w) → 0` at every `β ≥ β₀`: a restatement of the two-sided comparison, not
a discharge. DERIVED: `0` the limit; `1` the step. -/
theorem oneStepLocal_iff {N : ℕ} {β₀ : ℝ} :
    (∃ (b : ℝ → ℝ) (r : ℝ → ℕ → ℝ) (ρ : ℝ → ℝ), OneStepLocal N β₀ b r ρ) ↔
      ∀ β : ℝ, β₀ ≤ β → Tendsto (fun w : ℕ => CouplingTower.windowCoupling N β (w + 1)
        - CouplingTower.windowCoupling N (β - leanStep N) w) atTop (𝓝 0) := by
  constructor
  · rintro ⟨b, r, ρ, h⟩ β hβ
    exact tendsto_window_diff_of_oneStepLocal h hβ
  · intro h
    classical
    have key : ∀ β : ℝ, β₀ ≤ β → ∃ a : ℝ, Tendsto (fun w : ℕ =>
        (BondMove.logZ N β (2 * 2 ^ w) - BondMove.logZ N (β - leanStep N) (2 ^ w))
          - ((2 : ℝ) ^ w) ^ 4 * a) atTop (𝓝 0) := by
      intro β hβ
      refine exists_extensive (h β hβ) fun w => ?_
      rw [← defK_wilson]
      unfold defK
      have e : (2 : ℕ) ^ (w + 1) = 2 * 2 ^ w := by ring
      rw [e]
      ring
    refine ⟨fun _ => 0, fun β n => BondMove.logZ N β (2 * n) - BondMove.logZ N (β - leanStep N) n,
      fun β => if hβ : β₀ ≤ β then (key β hβ).choose else 0, fun β _ n => by ring, fun β hβ => ?_⟩
    simp only [dif_pos hβ]
    exact (key β hβ).choose_spec

end MassGap.SmallFieldStep

end

#print axioms MassGap.SmallFieldStep.bgCurl_eq_of_block_eq
#print axioms MassGap.SmallFieldStep.curl_split
#print axioms MassGap.SmallFieldStep.exists_background
#print axioms MassGap.SmallFieldStep.bgAct_isLeast
#print axioms MassGap.SmallFieldStep.fluct_split
#print axioms MassGap.SmallFieldStep.fibre_gauss
#print axioms MassGap.SmallFieldStep.bgAct_of_block_zero
#print axioms MassGap.SmallFieldStep.bgAct_of_ker_bot
#print axioms MassGap.SmallFieldStep.le_one_sub_cos
#print axioms MassGap.SmallFieldStep.le_wilsonU1
#print axioms MassGap.SmallFieldStep.wilsonU1_le
#print axioms MassGap.SmallFieldStep.largeField_cost
#print axioms MassGap.SmallFieldStep.smallField_step
#print axioms MassGap.SmallFieldStep.fibre_smallField
#print axioms MassGap.SmallFieldStep.fibre_le_of_suppressed
#print axioms MassGap.SmallFieldStep.oneStep_sandwich
#print axioms MassGap.SmallFieldStep.defK_rem_step
#print axioms MassGap.SmallFieldStep.defK_bulk
#print axioms MassGap.SmallFieldStep.defK_const
#print axioms MassGap.SmallFieldStep.tendsto_defK_of_local
#print axioms MassGap.SmallFieldStep.oneLoopAboveSlack_of_oneStepLocal
#print axioms MassGap.SmallFieldStep.strongEnd_of_oneStepLocal_low
#print axioms MassGap.SmallFieldStep.tendsto_window_diff_of_oneStepLocal
#print axioms MassGap.SmallFieldStep.exists_tail
#print axioms MassGap.SmallFieldStep.exists_extensive
#print axioms MassGap.SmallFieldStep.oneStepLocal_iff
#print axioms MassGap.SmallFieldStep.zoomRem_canonical
#print axioms MassGap.SmallFieldStep.zoomRem_zero_iff
#print axioms MassGap.SmallFieldStep.window_step_of_oneStepLocal
#print axioms MassGap.SmallFieldStep.one_sub_cos_le
#print axioms MassGap.SmallFieldStep.sfConst_pos
#print axioms MassGap.SmallFieldStep.bgCurl_mem_orthogonal
#print axioms MassGap.SmallFieldStep.bgAct_eq_of_block_eq
