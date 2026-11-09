import Mathlib
import MassGap.PairInterface

noncomputable section

/-!
# MassGap.PairFibreDens — the pair covariance bound for general single-link densities

`PairFibreAbstract.fibreBound_of_tiltBounds` with the linear tilts `e^{⟪α, X h⟫}`, `e^{⟪γ, X g⟫}`
replaced by arbitrary positive continuous densities `θ₁(h)`, `θ₂(g)` from a set `A` on which the
normalised moments obey `DensBounds` (second moments `≤ M₂ ‖w‖²`, means `≤ mb ‖w‖`). The proof is
`PairFibreAbstract`'s, which reads the tilts only through those two bounds.

## What it gives

`densFibreBound_of_densBounds`: the kernel `K e^{⟪X h, T X g⟫} θ₁(h) θ₂(g)` with `‖T‖ ≤ τ` and
`θ₁, θ₂ ∈ A` has the pair covariance bound at `dstar τ M₂ σ mb c₂`, under the side conditions of
`fibreBound_of_tiltBounds`. Single-link factors that are not exponentials of a linear functional —
the part of an adjacent-plaquette coupling that reads one link twice — ride in `θ₁`, `θ₂` and cost
only through `M₂`, `mb`.
-/

namespace MassGap.PairFibreDens

open MeasureTheory
open MassGap.PairInterface

variable {Ω : Type} [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {X : Ω → E}

/-- A positive continuous single-link density (unnormalised). -/
structure Dens (Ω : Type) [TopologicalSpace Ω] where
  /-- The density. -/
  f : Ω → ℝ
  cont : Continuous f
  pos : ∀ g, 0 < f g

/-- **The moment bounds of a set of densities**: for every `θ ∈ A`, the `θ`-weighted second moments
of `⟪w, X⟫` are at most `M₂ ‖w‖²` and the means at most `mb ‖w‖`, unnormalised.

DERIVED: `2` is the moment order. -/
def DensBounds (P : Measure Ω) (X : Ω → E) (A : Set (Dens Ω)) (M₂ mb : ℝ) : Prop :=
  ∀ θ ∈ A,
    (∀ w : E, ∫ g, inner ℝ w (X g) ^ 2 * θ.f g ∂P ≤ M₂ * ‖w‖ ^ 2 * ∫ g, θ.f g ∂P) ∧
    (∀ w : E, |∫ g, inner ℝ w (X g) * θ.f g ∂P| ≤ mb * ‖w‖ * ∫ g, θ.f g ∂P)

/-- **The density weight** `K e^{⟪X h, T X g⟫} θ₁(h) θ₂(g)`.

DERIVED: no numeral. -/
def densWeight (X : Ω → E) (K : ℝ) (T : E →L[ℝ] E) (θ₁ θ₂ : Dens Ω) (h g : Ω) : ℝ :=
  K * Real.exp (inner ℝ (X h) (T (X g))) * θ₁.f h * θ₂.f g

/-- **The pair covariance bound at constant `c`** for every density weight with `‖T‖ ≤ τ` and
`θ₁, θ₂ ∈ A`, in the shape of `PairInterface.FibreBound`. -/
def DensFibreBound (P : Measure Ω) (X : Ω → E) (c τ : ℝ) (A : Set (Dens Ω)) : Prop :=
  ∀ (K : ℝ) (T : E →L[ℝ] E) (θ₁ θ₂ : Dens Ω), 0 < K → ‖T‖ ≤ τ → θ₁ ∈ A → θ₂ ∈ A →
    ∀ a b : Ω → ℝ, Continuous a → Continuous b →
      ∫ h, a h * ∫ g, densWeight X K T θ₁ θ₂ h g ∂P ∂P = 0 →
      ∫ h, ∫ g, a h * b g * densWeight X K T θ₁ θ₂ h g ∂P ∂P
        ≤ c / 2 * (∫ h, a h ^ 2 * ∫ g, densWeight X K T θ₁ θ₂ h g ∂P ∂P
          + ∫ g, b g ^ 2 * ∫ h, densWeight X K T θ₁ θ₂ h g ∂P ∂P)

/-- **The normalised density** `θ/∫θ` against `P`.

DERIVED: no numeral. -/
def tiltDens (P : Measure Ω) (_X : Ω → E) (θ : Dens Ω) (g : Ω) : ℝ :=
  θ.f g / ∫ g', θ.f g' ∂P

/-! ## 1. One-variable helpers -/

section OneVar

/-- The tilted partition function is positive.

DERIVED: `0` is the sign. -/
private theorem tiltZ_pos (_hX : Continuous X) (θ : Dens Ω) :
    0 < ∫ g, θ.f g ∂P := by
  have hi : Integrable θ.f P := integrable_of_continuous P θ.cont
  have hs : Function.support θ.f = Set.univ := Set.eq_univ_of_forall fun g => (θ.pos g).ne'
  rw [integral_pos_iff_support_of_nonneg (fun g => (θ.pos g).le) hi, hs, measure_univ]
  exact zero_lt_one

/-- DERIVED: `0` is the sign. -/
private theorem tiltDens_nonneg (hX : Continuous X) (θ : Dens Ω) (g : Ω) : 0 ≤ tiltDens P X θ g := by
  unfold tiltDens
  exact div_nonneg (θ.pos g).le (tiltZ_pos (P := P) hX θ).le

/-- DERIVED: no numeral. -/
private theorem continuous_tiltDens (_hX : Continuous X) (θ : Dens Ω) :
    Continuous (tiltDens P X θ) := by
  show Continuous fun g => θ.f g / ∫ g', θ.f g' ∂P
  exact θ.cont.div_const _

/-- DERIVED: `1` is the normalisation. -/
private theorem integral_tiltDens (hX : Continuous X) (θ : Dens Ω) :
    ∫ g, tiltDens P X θ g ∂P = 1 := by
  show ∫ g, θ.f g / (∫ g', θ.f g' ∂P) ∂P = 1
  rw [integral_div]
  exact div_self (tiltZ_pos (P := P) hX θ).ne'

/-- A tilted integral is the unnormalised one over the partition function.

DERIVED: no numeral. -/
private theorem tilt_ratio (θ : Dens Ω) (F : Ω → ℝ) :
    ∫ g, F g * tiltDens P X θ g ∂P
      = (∫ g, F g * θ.f g ∂P) / ∫ g, θ.f g ∂P := by
  rw [← integral_div]
  refine integral_congr_pointwise (fun g => ?_)
  show F g * (θ.f g / ∫ g', θ.f g' ∂P)
    = F g * θ.f g / ∫ g', θ.f g' ∂P
  ring

/-- The normalised tilted second moment.

DERIVED: `2` is the moment order. -/
private theorem tilt_second (hX : Continuous X) {M₂ mb : ℝ} {A : Set (Dens Ω)} (hTB : DensBounds P X A M₂ mb)
    {θ : Dens Ω} (hθ : θ ∈ A) (w : E) :
    ∫ g, inner ℝ w (X g) ^ 2 * tiltDens P X θ g ∂P ≤ M₂ * ‖w‖ ^ 2 := by
  have hZ := tiltZ_pos (P := P) hX θ
  have e : ∫ g, inner ℝ w (X g) ^ 2 * tiltDens P X θ g ∂P
      = (∫ g, inner ℝ w (X g) ^ 2 * θ.f g ∂P)
        / ∫ g, θ.f g ∂P :=
    tilt_ratio θ (fun g => inner ℝ w (X g) ^ 2)
  rw [e, div_le_iff₀ hZ]
  exact (hTB θ hθ).1 w

/-- The normalised tilted mean.

DERIVED: no numeral. -/
private theorem tilt_mean (hX : Continuous X) {M₂ mb : ℝ} {A : Set (Dens Ω)} (hTB : DensBounds P X A M₂ mb)
    {θ : Dens Ω} (hθ : θ ∈ A) (w : E) :
    |∫ g, inner ℝ w (X g) * tiltDens P X θ g ∂P| ≤ mb * ‖w‖ := by
  have hZ := tiltZ_pos (P := P) hX θ
  have e : ∫ g, inner ℝ w (X g) * tiltDens P X θ g ∂P
      = (∫ g, inner ℝ w (X g) * θ.f g ∂P)
        / ∫ g, θ.f g ∂P :=
    tilt_ratio θ (fun g => inner ℝ w (X g))
  rw [e, abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
  exact (hTB θ hθ).2 w

/-- **Cauchy–Schwarz in a tilted law** (the quadratic form `ρ (t f − k)² ≥ 0`).

DERIVED: `2` is the square and the cross coefficient. -/
private theorem cs_tilt (hX : Continuous X) (θ : Dens Ω) {f k : Ω → ℝ} (hf : Continuous f)
    (hk : Continuous k) :
    |∫ g, f g * k g * tiltDens P X θ g ∂P|
      ≤ Real.sqrt (∫ g, f g ^ 2 * tiltDens P X θ g ∂P)
        * Real.sqrt (∫ g, k g ^ 2 * tiltDens P X θ g ∂P) := by
  have hρ := continuous_tiltDens (P := P) hX θ
  have hpt : ∀ (t : ℝ) (g : Ω), 2 * t * (f g * k g * tiltDens P X θ g)
      ≤ t ^ 2 * (f g ^ 2 * tiltDens P X θ g) + k g ^ 2 * tiltDens P X θ g := by
    intro t g
    linarith [mul_nonneg (tiltDens_nonneg (P := P) hX θ g) (sq_nonneg (t * f g - k g))]
  refine abs_le_sqrt_mul_of_quad
    (integral_nonneg (fun g => mul_nonneg (sq_nonneg _) (tiltDens_nonneg (P := P) hX θ g)))
    (integral_nonneg (fun g => mul_nonneg (sq_nonneg _) (tiltDens_nonneg (P := P) hX θ g))) (fun t => ?_)
  exact quad_integral (integrable_of_continuous P ((hf.mul hk).mul hρ))
    (integrable_of_continuous P ((hf.pow 2).mul hρ)) (integrable_of_continuous P ((hk.pow 2).mul hρ))
    hpt t

/-- From `‖y‖² ≤ K ‖y‖` and `K ≥ 0`: `‖y‖ ≤ K`.

DERIVED: `0` is the sign; `2` is the square. -/
private theorem norm_le_of_sq_le {y : E} {K : ℝ} (hK : 0 ≤ K) (h : ‖y‖ ^ 2 ≤ K * ‖y‖) :
    ‖y‖ ≤ K := by
  rcases (norm_nonneg y).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact hK
  · nlinarith

/-- **A linear functional integrates through the Bochner integral**:
`∫ c ⟪x, S X⟫ = ⟪x, ∫ c • S X⟫`.

DERIVED: no numeral. -/
private theorem inner_integral_smul (hX : Continuous X) {c : Ω → ℝ} (hc : Continuous c)
    (S : E →L[ℝ] E) (x : E) :
    ∫ g, c g * inner ℝ x (S (X g)) ∂P = inner ℝ x (∫ g, c g • S (X g) ∂P) := by
  have hint : Integrable (fun g => c g • S (X g)) P :=
    integrable_of_continuous_vec P (hc.smul (S.continuous.comp hX))
  rw [← integral_inner (𝕜 := ℝ) hint x]
  exact integral_congr_pointwise (fun g => (real_inner_smul_right _ _ _).symm)

/-- DERIVED: no numeral. -/
private theorem opnorm_apply_le (S : E →L[ℝ] E) {τ : ℝ} (hS : ‖S‖ ≤ τ) (x : E) :
    ‖S x‖ ≤ τ * ‖x‖ :=
  le_trans (S.le_opNorm x) (mul_le_mul_of_nonneg_right hS (norm_nonneg x))

/-- DERIVED: no numeral. -/
private theorem adj_opnorm (S : E →L[ℝ] E) : ‖ContinuousLinearMap.adjoint S‖ = ‖S‖ :=
  LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint S

/-- DERIVED: no numeral. -/
private theorem adj_norm_le (S : E →L[ℝ] E) {τ : ℝ} (hS : ‖S‖ ≤ τ) (x : E) :
    ‖(ContinuousLinearMap.adjoint S) x‖ ≤ τ * ‖x‖ :=
  opnorm_apply_le (ContinuousLinearMap.adjoint S) (by rw [adj_opnorm]; exact hS) x

/-- DERIVED: no numeral. -/
private theorem adj_swap_inner (T : E →L[ℝ] E) (x z : E) :
    inner ℝ x ((ContinuousLinearMap.adjoint T) z) = inner ℝ z (T x) := by
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact real_inner_comm _ _

/-- The coupling is at most `τ` on features of norm at most `1`.

DERIVED: `1` is the norm bound of the features and of `x`; `0` in `0 ≤ τ` is the sign of the
operator-norm budget. -/
private theorem abs_u_le (hX1 : ∀ g, ‖X g‖ ≤ 1) (S : E →L[ℝ] E) {τ : ℝ} (hτ : 0 ≤ τ)
    (hS : ‖S‖ ≤ τ) {x : E} (hx : ‖x‖ ≤ 1) (g : Ω) : |inner ℝ x (S (X g))| ≤ τ := by
  have h1 : ‖S (X g)‖ ≤ τ := by
    calc ‖S (X g)‖ ≤ τ * ‖X g‖ := opnorm_apply_le S hS (X g)
      _ ≤ τ * 1 := mul_le_mul_of_nonneg_left (hX1 g) hτ
      _ = τ := mul_one τ
  calc |inner ℝ x (S (X g))| ≤ ‖x‖ * ‖S (X g)‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 * τ := mul_le_mul hx h1 (norm_nonneg _) zero_le_one
    _ = τ := one_mul τ

/-- The mean vector `∫ ρ • S X` against its adjoint image.

DERIVED: `2` is the square. -/
private theorem mean_vec_sq (hX : Continuous X) {M₂ mb : ℝ} {A : Set (Dens Ω)} (hTB : DensBounds P X A M₂ mb)
    (S : E →L[ℝ] E) {θ : Dens Ω} (hθ : θ ∈ A) :
    ‖∫ g, tiltDens P X θ g • S (X g) ∂P‖ ^ 2
      ≤ mb * ‖(ContinuousLinearMap.adjoint S) (∫ g, tiltDens P X θ g • S (X g) ∂P)‖ := by
  obtain ⟨y, hy⟩ : ∃ y, y = ∫ g, tiltDens P X θ g • S (X g) ∂P := ⟨_, rfl⟩
  rw [← hy]
  have h0 := inner_integral_smul (P := P) hX (continuous_tiltDens (P := P) hX θ) S y
  rw [← hy] at h0
  have h1 : ‖y‖ ^ 2
      = ∫ g, inner ℝ ((ContinuousLinearMap.adjoint S) y) (X g) * tiltDens P X θ g ∂P := by
    rw [← real_inner_self_eq_norm_sq, ← h0]
    refine integral_congr_pointwise (fun g => ?_)
    rw [ContinuousLinearMap.adjoint_inner_left]
    ring
  rw [h1]
  exact le_trans (le_abs_self _) (tilt_mean hX hTB hθ _)

/-- **The mean vector has norm at most `τ mb`.**

DERIVED: `0` is the sign of `τ`, `mb`. -/
private theorem mean_vec (hX : Continuous X) {τ M₂ mb : ℝ} {A : Set (Dens Ω)} (hτ : 0 ≤ τ) (hmb : 0 ≤ mb)
    (hTB : DensBounds P X A M₂ mb) (S : E →L[ℝ] E) (hS : ‖S‖ ≤ τ) {θ : Dens Ω} (hθ : θ ∈ A) :
    ‖∫ g, tiltDens P X θ g • S (X g) ∂P‖ ≤ τ * mb := by
  have h1 := mean_vec_sq hX hTB S hθ
  have h2 := adj_norm_le S hS (∫ g, tiltDens P X θ g • S (X g) ∂P)
  refine norm_le_of_sq_le (mul_nonneg hτ hmb) ?_
  calc ‖∫ g, tiltDens P X θ g • S (X g) ∂P‖ ^ 2
      ≤ mb * ‖(ContinuousLinearMap.adjoint S) (∫ g, tiltDens P X θ g • S (X g) ∂P)‖ := h1
    _ ≤ mb * (τ * ‖∫ g, tiltDens P X θ g • S (X g) ∂P‖) := mul_le_mul_of_nonneg_left h2 hmb
    _ = τ * mb * ‖∫ g, tiltDens P X θ g • S (X g) ∂P‖ := by ring

/-- `mb ‖∫ ρ • S X‖ ≤ τ mb²` with no sign condition on `mb` (a negative `mb` forces the vector to
vanish).

DERIVED: `0` is the case split on the sign of `mb`; `2` is the square. -/
private theorem mean_vec_mul (hX : Continuous X) {τ M₂ mb : ℝ} {A : Set (Dens Ω)} (hτ : 0 ≤ τ)
    (hTB : DensBounds P X A M₂ mb) (S : E →L[ℝ] E) (hS : ‖S‖ ≤ τ) {θ : Dens Ω} (hθ : θ ∈ A) :
    mb * ‖∫ g, tiltDens P X θ g • S (X g) ∂P‖ ≤ τ * mb ^ 2 := by
  rcases le_or_gt 0 mb with hmb | hmb
  · have h := mean_vec hX hτ hmb hTB S hS hθ
    calc mb * ‖∫ g, tiltDens P X θ g • S (X g) ∂P‖ ≤ mb * (τ * mb) :=
          mul_le_mul_of_nonneg_left h hmb
      _ = τ * mb ^ 2 := by ring
  · have h1 := mean_vec_sq hX hTB S hθ
    have h2 : mb * ‖(ContinuousLinearMap.adjoint S) (∫ g, tiltDens P X θ g • S (X g) ∂P)‖ ≤ 0 := by
      nlinarith [norm_nonneg ((ContinuousLinearMap.adjoint S) (∫ g, tiltDens P X θ g • S (X g) ∂P))]
    have h4 : ‖∫ g, tiltDens P X θ g • S (X g) ∂P‖ ^ 2 = 0 :=
      le_antisymm (le_trans h1 h2) (sq_nonneg _)
    have h3 : ‖∫ g, tiltDens P X θ g • S (X g) ∂P‖ = 0 := (pow_eq_zero_iff two_ne_zero).mp h4
    rw [h3, mul_zero]
    exact mul_nonneg hτ (sq_nonneg mb)

/-- **The row of `e^u` is at least `1 + ⟪x, ∫ ρ • S X⟫`** (`Real.add_one_le_exp`).

DERIVED: `1` is `e⁰` and the normalisation. -/
private theorem row_exp_ge (hX : Continuous X) (S : E →L[ℝ] E) (θ : Dens Ω) (x : E) :
    1 + inner ℝ x (∫ g, tiltDens P X θ g • S (X g) ∂P)
      ≤ ∫ g, tiltDens P X θ g * Real.exp (inner ℝ x (S (X g))) ∂P := by
  have hρ := continuous_tiltDens (P := P) hX θ
  have hcu : Continuous fun g => inner ℝ x (S (X g)) :=
    continuous_const.inner (S.continuous.comp hX)
  have hi1 : Integrable (tiltDens P X θ) P := integrable_of_continuous P hρ
  have hi2 : Integrable (fun g => tiltDens P X θ g * inner ℝ x (S (X g))) P :=
    integrable_of_continuous P (hρ.mul hcu)
  have hi3 : Integrable (fun g => tiltDens P X θ g * Real.exp (inner ℝ x (S (X g)))) P :=
    integrable_of_continuous P (hρ.mul (Real.continuous_exp.comp hcu))
  have hpt : ∀ g, tiltDens P X θ g + tiltDens P X θ g * inner ℝ x (S (X g))
      ≤ tiltDens P X θ g * Real.exp (inner ℝ x (S (X g))) := by
    intro g
    linarith [mul_le_mul_of_nonneg_left (Real.add_one_le_exp (inner ℝ x (S (X g))))
      (tiltDens_nonneg (P := P) hX θ g)]
  calc 1 + inner ℝ x (∫ g, tiltDens P X θ g • S (X g) ∂P)
      = ∫ g, tiltDens P X θ g ∂P + ∫ g, tiltDens P X θ g * inner ℝ x (S (X g)) ∂P := by
        rw [integral_tiltDens (P := P) hX θ, inner_integral_smul hX hρ S x]
    _ = ∫ g, (tiltDens P X θ g + tiltDens P X θ g * inner ℝ x (S (X g))) ∂P :=
        (integral_add hi1 hi2).symm
    _ ≤ ∫ g, tiltDens P X θ g * Real.exp (inner ℝ x (S (X g))) ∂P :=
        integral_mono (hi1.fun_add hi2) hi3 hpt

/-- **The row of the remainder `R(u) = e^u − 1 − u` lies in `[0, c₂ τ² M₂]`.**

DERIVED: `0` is the lower end (`Real.add_one_le_exp`); `1` is `e⁰` and the norm bound of `x`;
`2` is the square. -/
private theorem G_bounds (hX : Continuous X) (hX1 : ∀ g, ‖X g‖ ≤ 1) {τ M₂ mb c₂ : ℝ} {A : Set (Dens Ω)}
    (hτ : 0 ≤ τ) (hc₂0 : 0 ≤ c₂) (hM₂ : 0 ≤ M₂) (hTB : DensBounds P X A M₂ mb)
    (hc₂ : ∀ u : ℝ, |u| ≤ τ → Real.exp u - 1 - u ≤ c₂ * u ^ 2)
    (S : E →L[ℝ] E) (hS : ‖S‖ ≤ τ) {θ : Dens Ω} (hθ : θ ∈ A) {x : E} (hx : ‖x‖ ≤ 1) :
    0 ≤ ∫ g, tiltDens P X θ g * (Real.exp (inner ℝ x (S (X g))) - 1 - inner ℝ x (S (X g))) ∂P ∧
    ∫ g, tiltDens P X θ g * (Real.exp (inner ℝ x (S (X g))) - 1 - inner ℝ x (S (X g))) ∂P
      ≤ c₂ * τ ^ 2 * M₂ := by
  have hρ := continuous_tiltDens (P := P) hX θ
  have hcu : Continuous fun g => inner ℝ x (S (X g)) :=
    continuous_const.inner (S.continuous.comp hX)
  have hR0 : ∀ g, 0 ≤ tiltDens P X θ g
      * (Real.exp (inner ℝ x (S (X g))) - 1 - inner ℝ x (S (X g))) := by
    intro g
    refine mul_nonneg (tiltDens_nonneg (P := P) hX θ g) ?_
    linarith [Real.add_one_le_exp (inner ℝ x (S (X g)))]
  refine ⟨integral_nonneg hR0, ?_⟩
  have hR : Continuous fun g => tiltDens P X θ g
      * (Real.exp (inner ℝ x (S (X g))) - 1 - inner ℝ x (S (X g))) :=
    hρ.mul (((Real.continuous_exp.comp hcu).sub continuous_const).sub hcu)
  have hQ : Continuous fun g =>
      c₂ * (inner ℝ ((ContinuousLinearMap.adjoint S) x) (X g) ^ 2 * tiltDens P X θ g) :=
    continuous_const.mul (((continuous_const.inner hX : Continuous fun g => inner ℝ ((ContinuousLinearMap.adjoint S) x) (X g)).pow 2).mul hρ)
  have hpt : ∀ g, tiltDens P X θ g * (Real.exp (inner ℝ x (S (X g))) - 1 - inner ℝ x (S (X g)))
      ≤ c₂ * (inner ℝ ((ContinuousLinearMap.adjoint S) x) (X g) ^ 2 * tiltDens P X θ g) := by
    intro g
    have e : inner ℝ ((ContinuousLinearMap.adjoint S) x) (X g) = inner ℝ x (S (X g)) :=
      ContinuousLinearMap.adjoint_inner_left S (X g) x
    rw [e]
    have h1 := hc₂ _ (abs_u_le hX1 S hτ hS hx g)
    linarith [mul_le_mul_of_nonneg_left h1 (tiltDens_nonneg (P := P) hX θ g)]
  have hSx : ‖(ContinuousLinearMap.adjoint S) x‖ ^ 2 ≤ τ ^ 2 := by
    have h2 : ‖(ContinuousLinearMap.adjoint S) x‖ ≤ τ := by
      calc ‖(ContinuousLinearMap.adjoint S) x‖ ≤ τ * ‖x‖ := adj_norm_le S hS x
        _ ≤ τ * 1 := mul_le_mul_of_nonneg_left hx hτ
        _ = τ := mul_one τ
    exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  calc ∫ g, tiltDens P X θ g * (Real.exp (inner ℝ x (S (X g))) - 1 - inner ℝ x (S (X g))) ∂P
      ≤ ∫ g, c₂ * (inner ℝ ((ContinuousLinearMap.adjoint S) x) (X g) ^ 2 * tiltDens P X θ g) ∂P :=
        integral_mono (integrable_of_continuous P hR) (integrable_of_continuous P hQ) hpt
    _ = c₂ * ∫ g, inner ℝ ((ContinuousLinearMap.adjoint S) x) (X g) ^ 2 * tiltDens P X θ g ∂P :=
        integral_const_mul _ _
    _ ≤ c₂ * (M₂ * ‖(ContinuousLinearMap.adjoint S) x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (tilt_second hX hTB hθ _) hc₂0
    _ ≤ c₂ * (M₂ * τ ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSx hM₂) hc₂0
    _ = c₂ * τ ^ 2 * M₂ := by ring

end OneVar

/-! ## 2. Pair integrals on the product -/

section Pair

/-- **The coupling is measurable for the product σ-algebra**: `⟪x, S y⟫ = Σᵢ ⟪x, bᵢ⟫⟪bᵢ, S y⟫`.

DERIVED: no numeral. -/
private theorem measurable_u (hX : Continuous X) (S : E →L[ℝ] E) :
    Measurable (fun p : Ω × Ω => inner ℝ (X p.1) (S (X p.2))) := by
  have b := stdOrthonormalBasis ℝ E
  have e : (fun p : Ω × Ω => inner ℝ (X p.1) (S (X p.2)))
      = fun p => ∑ i, inner ℝ (X p.1) (b i) * inner ℝ (b i) (S (X p.2)) := by
    funext p
    exact (b.sum_inner_mul_inner _ _).symm
  refine (congrArg Measurable e).mpr ?_
  refine Finset.measurable_sum _ (fun i _ => ?_)
  have h1 : Continuous fun h : Ω => inner ℝ (X h) (b i) := hX.inner continuous_const
  have h2 : Continuous fun g : Ω => inner ℝ (b i) (S (X g)) :=
    continuous_const.inner (S.continuous.comp hX)
  exact (h1.measurable.comp measurable_fst).mul (h2.measurable.comp measurable_snd)

/-- **The standard pair integrand is integrable on `P ⊗ P`.**

DERIVED: no numeral. -/
private theorem integrable_std (hX : Continuous X) (S : E →L[ℝ] E) {φ ψ : Ω → ℝ} {Ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) (hΨ : Continuous Ψ) :
    Integrable (fun p : Ω × Ω => φ p.1 * ψ p.2 * Ψ (inner ℝ (X p.1) (S (X p.2)))) (P.prod P) := by
  have hcu : Continuous fun p : Ω × Ω => inner ℝ (X p.1) (S (X p.2)) :=
    (hX.comp continuous_fst).inner (S.continuous.comp (hX.comp continuous_snd))
  have hc : Continuous fun p : Ω × Ω => φ p.1 * ψ p.2 * Ψ (inner ℝ (X p.1) (S (X p.2))) :=
    ((hφ.comp continuous_fst).mul (hψ.comp continuous_snd)).mul (hΨ.comp hcu)
  have hm : Measurable fun p : Ω × Ω => φ p.1 * ψ p.2 * Ψ (inner ℝ (X p.1) (S (X p.2))) :=
    ((hφ.measurable.comp measurable_fst).mul (hψ.measurable.comp measurable_snd)).mul
      (hΨ.measurable.comp (measurable_u hX S))
  exact integrable_of_continuous_measurable (P.prod P) hc hm

/-- **The pair integral** `∫ φ(h) ψ(g) Ψ(⟪X h, S X g⟫) d(P ⊗ P)`.

DERIVED: no numeral. -/
private def pairInt (P : Measure Ω) (X : Ω → E) (S : E →L[ℝ] E) (φ ψ : Ω → ℝ) (Ψ : ℝ → ℝ) : ℝ :=
  ∫ p : Ω × Ω, φ p.1 * ψ p.2 * Ψ (inner ℝ (X p.1) (S (X p.2))) ∂(P.prod P)

/-- The pair integral as an iterated integral, `g` inside.

DERIVED: no numeral. -/
private theorem pairInt_row (hX : Continuous X) (S : E →L[ℝ] E) {φ ψ : Ω → ℝ} {Ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) (hΨ : Continuous Ψ) :
    pairInt P X S φ ψ Ψ = ∫ h, φ h * ∫ g, ψ g * Ψ (inner ℝ (X h) (S (X g))) ∂P ∂P := by
  unfold pairInt
  rw [integral_prod _ (integrable_std (P := P) hX S hφ hψ hΨ)]
  refine integral_congr_pointwise (fun h => ?_)
  rw [← integral_const_mul]
  exact integral_congr_pointwise (fun g => mul_assoc _ _ _)

/-- The row function of a pair integral is integrable.

DERIVED: no numeral. -/
private theorem pairInt_row_integrable (hX : Continuous X) (S : E →L[ℝ] E) {φ ψ : Ω → ℝ}
    {Ψ : ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ) (hΨ : Continuous Ψ) :
    Integrable (fun h => φ h * ∫ g, ψ g * Ψ (inner ℝ (X h) (S (X g))) ∂P) P := by
  refine (integrable_std (P := P) hX S hφ hψ hΨ).integral_prod_left.congr
    (Filter.Eventually.of_forall (fun h => ?_))
  show ∫ g, φ (h, g).1 * ψ (h, g).2 * Ψ (inner ℝ (X (h, g).1) (S (X (h, g).2))) ∂P
    = φ h * ∫ g, ψ g * Ψ (inner ℝ (X h) (S (X g))) ∂P
  rw [← integral_const_mul]
  exact integral_congr_pointwise (fun g => mul_assoc _ _ _)

/-- **Swapping the factors replaces `S` by its adjoint** (`integral_prod_swap`).

DERIVED: no numeral. -/
private theorem pairInt_swap (S : E →L[ℝ] E) (φ ψ : Ω → ℝ) (Ψ : ℝ → ℝ) :
    pairInt P X S φ ψ Ψ = pairInt P X (ContinuousLinearMap.adjoint S) ψ φ Ψ := by
  unfold pairInt
  rw [← integral_prod_swap (fun p : Ω × Ω =>
    ψ p.1 * φ p.2 * Ψ (inner ℝ (X p.1) ((ContinuousLinearMap.adjoint S) (X p.2))))]
  refine integral_congr_pointwise (fun p => ?_)
  show φ p.1 * ψ p.2 * Ψ (inner ℝ (X p.1) (S (X p.2)))
    = ψ p.2 * φ p.1 * Ψ (inner ℝ (X p.2) ((ContinuousLinearMap.adjoint S) (X p.1)))
  rw [adj_swap_inner]
  ring

/-- **`e^u = 1 + u + R(u)` under the pair integral.**

DERIVED: `1` is `e⁰`. -/
private theorem pairInt_split (hX : Continuous X) (S : E →L[ℝ] E) {φ ψ : Ω → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) :
    pairInt P X S φ ψ Real.exp
      = pairInt P X S φ ψ (fun _ => 1) + pairInt P X S φ ψ (fun y => y)
        + pairInt P X S φ ψ (fun y => Real.exp y - 1 - y) := by
  have hid : Continuous fun y : ℝ => y := continuous_id
  have hR : Continuous fun y : ℝ => Real.exp y - 1 - y :=
    (Real.continuous_exp.sub continuous_const).sub continuous_id
  have h1 : Integrable (fun p : Ω × Ω => φ p.1 * ψ p.2 * 1) (P.prod P) :=
    integrable_std hX S hφ hψ continuous_const
  have h2 : Integrable (fun p : Ω × Ω => φ p.1 * ψ p.2 * inner ℝ (X p.1) (S (X p.2)))
      (P.prod P) :=
    integrable_std hX S hφ hψ hid
  have h3 : Integrable (fun p : Ω × Ω => φ p.1 * ψ p.2
      * (Real.exp (inner ℝ (X p.1) (S (X p.2))) - 1 - inner ℝ (X p.1) (S (X p.2)))) (P.prod P) :=
    integrable_std hX S hφ hψ hR
  unfold pairInt
  rw [← integral_add3 h1 h2 h3]
  exact integral_congr_pointwise (fun p => by ring)

/-- Centring the left function: `a = a₀ + (a − a₀)`.

DERIVED: no numeral. -/
private theorem expand_left (hX : Continuous X) (S : E →L[ℝ] E) {a ψ : Ω → ℝ}
    (ha : Continuous a) (hψ : Continuous ψ) (a₀ : ℝ) (θ : Dens Ω) :
    pairInt P X S (fun h => a h * tiltDens P X θ h) ψ Real.exp
      = a₀ * pairInt P X S (tiltDens P X θ) ψ Real.exp
        + pairInt P X S (fun h => (a h - a₀) * tiltDens P X θ h) ψ Real.exp := by
  have hρ := continuous_tiltDens (P := P) hX θ
  have h1 : Integrable (fun p : Ω × Ω => tiltDens P X θ p.1 * ψ p.2
      * Real.exp (inner ℝ (X p.1) (S (X p.2)))) (P.prod P) :=
    integrable_std hX S hρ hψ Real.continuous_exp
  have h2 : Integrable (fun p : Ω × Ω => (a p.1 - a₀) * tiltDens P X θ p.1 * ψ p.2
      * Real.exp (inner ℝ (X p.1) (S (X p.2)))) (P.prod P) :=
    integrable_std hX S ((ha.sub continuous_const).mul hρ) hψ Real.continuous_exp
  unfold pairInt
  rw [← integral_lin2 h1 h2 a₀]
  exact integral_congr_pointwise (fun p => by ring)

/-- Centring the right function: `b = b₀ + (b − b₀)`.

DERIVED: no numeral. -/
private theorem expand_right (hX : Continuous X) (S : E →L[ℝ] E) {φ b : Ω → ℝ}
    (hφ : Continuous φ) (hb : Continuous b) (b₀ : ℝ) (θ : Dens Ω) :
    pairInt P X S φ (fun g => b g * tiltDens P X θ g) Real.exp
      = b₀ * pairInt P X S φ (tiltDens P X θ) Real.exp
        + pairInt P X S φ (fun g => (b g - b₀) * tiltDens P X θ g) Real.exp := by
  have hρ := continuous_tiltDens (P := P) hX θ
  have h1 : Integrable (fun p : Ω × Ω => φ p.1 * tiltDens P X θ p.2
      * Real.exp (inner ℝ (X p.1) (S (X p.2)))) (P.prod P) :=
    integrable_std hX S hφ hρ Real.continuous_exp
  have h2 : Integrable (fun p : Ω × Ω => φ p.1 * ((b p.2 - b₀) * tiltDens P X θ p.2)
      * Real.exp (inner ℝ (X p.1) (S (X p.2)))) (P.prod P) :=
    integrable_std hX S hφ ((hb.sub continuous_const).mul hρ) Real.continuous_exp
  unfold pairInt
  rw [← integral_lin2 h1 h2 b₀]
  exact integral_congr_pointwise (fun p => by ring)

/-- Centring the left square: `a² = a₀² + 2a₀(a − a₀) + (a − a₀)²`.

DERIVED: `2` is the square and its cross coefficient. -/
private theorem expand_sq_left (hX : Continuous X) (S : E →L[ℝ] E) {a ψ : Ω → ℝ}
    (ha : Continuous a) (hψ : Continuous ψ) (a₀ : ℝ) (θ : Dens Ω) :
    pairInt P X S (fun h => a h ^ 2 * tiltDens P X θ h) ψ Real.exp
      = a₀ ^ 2 * pairInt P X S (tiltDens P X θ) ψ Real.exp
        + 2 * a₀ * pairInt P X S (fun h => (a h - a₀) * tiltDens P X θ h) ψ Real.exp
        + pairInt P X S (fun h => (a h - a₀) ^ 2 * tiltDens P X θ h) ψ Real.exp := by
  have hρ := continuous_tiltDens (P := P) hX θ
  have hfa : Continuous fun h => a h - a₀ := ha.sub continuous_const
  have h1 : Integrable (fun p : Ω × Ω => tiltDens P X θ p.1 * ψ p.2
      * Real.exp (inner ℝ (X p.1) (S (X p.2)))) (P.prod P) :=
    integrable_std hX S hρ hψ Real.continuous_exp
  have h2 : Integrable (fun p : Ω × Ω => (a p.1 - a₀) * tiltDens P X θ p.1 * ψ p.2
      * Real.exp (inner ℝ (X p.1) (S (X p.2)))) (P.prod P) :=
    integrable_std hX S (hfa.mul hρ) hψ Real.continuous_exp
  have h3 : Integrable (fun p : Ω × Ω => (a p.1 - a₀) ^ 2 * tiltDens P X θ p.1 * ψ p.2
      * Real.exp (inner ℝ (X p.1) (S (X p.2)))) (P.prod P) :=
    integrable_std hX S ((hfa.pow 2).mul hρ) hψ Real.continuous_exp
  unfold pairInt
  rw [← integral_lin3 h1 h2 h3 (a₀ ^ 2) (2 * a₀)]
  exact integral_congr_pointwise (fun p => by ring)

/-- Centring the right square.

DERIVED: `2` is the square and its cross coefficient. -/
private theorem expand_sq_right (hX : Continuous X) (S : E →L[ℝ] E) {φ b : Ω → ℝ}
    (hφ : Continuous φ) (hb : Continuous b) (b₀ : ℝ) (θ : Dens Ω) :
    pairInt P X S φ (fun g => b g ^ 2 * tiltDens P X θ g) Real.exp
      = b₀ ^ 2 * pairInt P X S φ (tiltDens P X θ) Real.exp
        + 2 * b₀ * pairInt P X S φ (fun g => (b g - b₀) * tiltDens P X θ g) Real.exp
        + pairInt P X S φ (fun g => (b g - b₀) ^ 2 * tiltDens P X θ g) Real.exp := by
  have hρ := continuous_tiltDens (P := P) hX θ
  have hfb : Continuous fun g => b g - b₀ := hb.sub continuous_const
  have h1 : Integrable (fun p : Ω × Ω => φ p.1 * tiltDens P X θ p.2
      * Real.exp (inner ℝ (X p.1) (S (X p.2)))) (P.prod P) :=
    integrable_std hX S hφ hρ Real.continuous_exp
  have h2 : Integrable (fun p : Ω × Ω => φ p.1 * ((b p.2 - b₀) * tiltDens P X θ p.2)
      * Real.exp (inner ℝ (X p.1) (S (X p.2)))) (P.prod P) :=
    integrable_std hX S hφ (hfb.mul hρ) Real.continuous_exp
  have h3 : Integrable (fun p : Ω × Ω => φ p.1 * ((b p.2 - b₀) ^ 2 * tiltDens P X θ p.2)
      * Real.exp (inner ℝ (X p.1) (S (X p.2)))) (P.prod P) :=
    integrable_std hX S hφ ((hfb.pow 2).mul hρ) Real.continuous_exp
  unfold pairInt
  rw [← integral_lin3 h1 h2 h3 (b₀ ^ 2) (2 * b₀)]
  exact integral_congr_pointwise (fun p => by ring)

end Pair

/-! ## 3. The one-sided bounds -/

section Bounds

/-- **(D) The pair partition function** is at least `1 − τ mb²`.

DERIVED: `1` is `e⁰`; `2` is the square of the mean; `0` in `0 ≤ τ` is the sign of the
operator-norm budget. -/
private theorem pair_Z_ge (hX : Continuous X) {τ M₂ mb : ℝ} {A : Set (Dens Ω)} (hτ : 0 ≤ τ)
    (hTB : DensBounds P X A M₂ mb) (S : E →L[ℝ] E) (hS : ‖S‖ ≤ τ)
    {θ₁ θ₂ : Dens Ω} (hθ₁ : θ₁ ∈ A) (hθ₂ : θ₂ ∈ A) :
    1 - τ * mb ^ 2 ≤ pairInt P X S (tiltDens P X θ₁) (tiltDens P X θ₂) Real.exp := by
  have hρ₁ := continuous_tiltDens (P := P) hX θ₁
  have hρ₂ := continuous_tiltDens (P := P) hX θ₂
  rw [pairInt_row hX S hρ₁ hρ₂ Real.continuous_exp]
  obtain ⟨v, hv⟩ : ∃ v, v = ∫ g, tiltDens P X θ₂ g • S (X g) ∂P := ⟨_, rfl⟩
  have hlow : ∀ h, tiltDens P X θ₁ h + inner ℝ v (X h) * tiltDens P X θ₁ h
      ≤ tiltDens P X θ₁ h
        * ∫ g, tiltDens P X θ₂ g * Real.exp (inner ℝ (X h) (S (X g))) ∂P := by
    intro h
    have h1 := row_exp_ge (P := P) hX S θ₂ (X h)
    rw [← hv] at h1
    have e : inner ℝ (X h) v = inner ℝ v (X h) := real_inner_comm _ _
    rw [e] at h1
    linarith [mul_le_mul_of_nonneg_left h1 (tiltDens_nonneg (P := P) hX θ₁ h)]
  have hint_low : Integrable (fun h => tiltDens P X θ₁ h + inner ℝ v (X h) * tiltDens P X θ₁ h) P :=
    integrable_of_continuous P (hρ₁.add ((continuous_const.inner hX : Continuous fun g => inner ℝ v (X g)).mul hρ₁))
  have hmono := integral_mono hint_low
    (pairInt_row_integrable hX S hρ₁ hρ₂ Real.continuous_exp) hlow
  have hi1 : Integrable (tiltDens P X θ₁) P := integrable_of_continuous P hρ₁
  have hi2 : Integrable (fun h => inner ℝ v (X h) * tiltDens P X θ₁ h) P :=
    integrable_of_continuous P ((continuous_const.inner hX : Continuous fun g => inner ℝ v (X g)).mul hρ₁)
  rw [integral_add hi1 hi2, integral_tiltDens (P := P) hX θ₁] at hmono
  have hm := tilt_mean hX hTB hθ₁ v
  have hmv := mean_vec_mul hX hτ hTB S hS hθ₂
  rw [← hv] at hmv
  have hna := neg_abs_le (∫ h, inner ℝ v (X h) * tiltDens P X θ₁ h ∂P)
  linarith

/-- **(C) The pair second moment of a left function**, homogeneous: `(1 − τ mb) E_μ f²`.

DERIVED: `1` is `e⁰` and the norm bound of the feature; `2` is the square; `0` in `0 ≤ τ` and
`0 ≤ mb` is the sign of the operator-norm budget and of the tilted-mean bound. -/
private theorem pair_S_ge (hX : Continuous X) (hX1 : ∀ g, ‖X g‖ ≤ 1) {τ M₂ mb : ℝ} {A : Set (Dens Ω)}
    (hτ : 0 ≤ τ) (hmb : 0 ≤ mb) (hTB : DensBounds P X A M₂ mb) (S : E →L[ℝ] E) (hS : ‖S‖ ≤ τ)
    {θ₁ θ₂ : Dens Ω} (hθ₂ : θ₂ ∈ A) {f : Ω → ℝ} (hf : Continuous f) :
    (1 - τ * mb) * ∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P
      ≤ pairInt P X S (fun h => f h ^ 2 * tiltDens P X θ₁ h) (tiltDens P X θ₂) Real.exp := by
  have hρ₁ := continuous_tiltDens (P := P) hX θ₁
  have hρ₂ := continuous_tiltDens (P := P) hX θ₂
  have hφ : Continuous fun h => f h ^ 2 * tiltDens P X θ₁ h := (hf.pow 2).mul hρ₁
  rw [pairInt_row hX S hφ hρ₂ Real.continuous_exp]
  obtain ⟨v, hv⟩ : ∃ v, v = ∫ g, tiltDens P X θ₂ g • S (X g) ∂P := ⟨_, rfl⟩
  have hvn : ‖v‖ ≤ τ * mb := by
    rw [hv]
    exact mean_vec hX hτ hmb hTB S hS hθ₂
  have hlow : ∀ h, (1 - τ * mb) * (f h ^ 2 * tiltDens P X θ₁ h)
      ≤ f h ^ 2 * tiltDens P X θ₁ h
        * ∫ g, tiltDens P X θ₂ g * Real.exp (inner ℝ (X h) (S (X g))) ∂P := by
    intro h
    have h1 := row_exp_ge (P := P) hX S θ₂ (X h)
    rw [← hv] at h1
    have h3 : ‖X h‖ * ‖v‖ ≤ τ * mb :=
      le_trans (mul_le_of_le_one_left (norm_nonneg v) (hX1 h)) hvn
    have h4 := abs_real_inner_le_norm (X h) v
    have h5 := neg_abs_le (inner ℝ (X h) v)
    have h6 : 1 - τ * mb
        ≤ ∫ g, tiltDens P X θ₂ g * Real.exp (inner ℝ (X h) (S (X g))) ∂P := by
      linarith
    have hw : 0 ≤ f h ^ 2 * tiltDens P X θ₁ h :=
      mul_nonneg (sq_nonneg _) (tiltDens_nonneg (P := P) hX θ₁ h)
    calc (1 - τ * mb) * (f h ^ 2 * tiltDens P X θ₁ h)
        = f h ^ 2 * tiltDens P X θ₁ h * (1 - τ * mb) := by ring
      _ ≤ f h ^ 2 * tiltDens P X θ₁ h
          * ∫ g, tiltDens P X θ₂ g * Real.exp (inner ℝ (X h) (S (X g))) ∂P :=
          mul_le_mul_of_nonneg_left h6 hw
  calc (1 - τ * mb) * ∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P
      = ∫ h, (1 - τ * mb) * (f h ^ 2 * tiltDens P X θ₁ h) ∂P := (integral_const_mul _ _).symm
    _ ≤ ∫ h, f h ^ 2 * tiltDens P X θ₁ h
          * ∫ g, tiltDens P X θ₂ g * Real.exp (inner ℝ (X h) (S (X g))) ∂P ∂P :=
        integral_mono (integrable_of_continuous P (continuous_const.mul hφ))
          (pairInt_row_integrable hX S hφ hρ₂ Real.continuous_exp) hlow

/-- **The remainder pair integral against a non-negative left weight** is at most
`c₂ τ² M₂ ∫ φ`.

DERIVED: `0` is the sign of the weight and of `τ`, `c₂`, `M₂`; `2` is the square; `1` is the norm
bound of the features and the `e⁰` subtracted in the remainder `eʸ − 1 − y`. -/
private theorem pair_R_le (hX : Continuous X) (hX1 : ∀ g, ‖X g‖ ≤ 1) {τ M₂ mb c₂ : ℝ} {A : Set (Dens Ω)}
    (hτ : 0 ≤ τ) (hc₂0 : 0 ≤ c₂) (hM₂ : 0 ≤ M₂) (hTB : DensBounds P X A M₂ mb)
    (hc₂ : ∀ u : ℝ, |u| ≤ τ → Real.exp u - 1 - u ≤ c₂ * u ^ 2)
    (S : E →L[ℝ] E) (hS : ‖S‖ ≤ τ) {θ₂ : Dens Ω} (hθ₂ : θ₂ ∈ A) {φ : Ω → ℝ} (hφ : Continuous φ)
    (hφ0 : ∀ h, 0 ≤ φ h) :
    pairInt P X S φ (tiltDens P X θ₂) (fun y => Real.exp y - 1 - y)
      ≤ c₂ * τ ^ 2 * M₂ * ∫ h, φ h ∂P := by
  have hρ₂ := continuous_tiltDens (P := P) hX θ₂
  have hR : Continuous fun y : ℝ => Real.exp y - 1 - y :=
    (Real.continuous_exp.sub continuous_const).sub continuous_id
  rw [pairInt_row hX S hφ hρ₂ hR]
  have hpt : ∀ h, φ h * ∫ g, tiltDens P X θ₂ g
        * (Real.exp (inner ℝ (X h) (S (X g))) - 1 - inner ℝ (X h) (S (X g))) ∂P
      ≤ c₂ * τ ^ 2 * M₂ * φ h := by
    intro h
    have hG := (G_bounds hX hX1 hτ hc₂0 hM₂ hTB hc₂ S hS hθ₂ (hX1 h)).2
    linarith [mul_le_mul_of_nonneg_left hG (hφ0 h)]
  calc ∫ h, φ h * ∫ g, tiltDens P X θ₂ g
          * (Real.exp (inner ℝ (X h) (S (X g))) - 1 - inner ℝ (X h) (S (X g))) ∂P ∂P
      ≤ ∫ h, c₂ * τ ^ 2 * M₂ * φ h ∂P :=
        integral_mono (pairInt_row_integrable hX S hφ hρ₂ hR)
          (integrable_of_continuous P (continuous_const.mul hφ)) hpt
    _ = c₂ * τ ^ 2 * M₂ * ∫ h, φ h ∂P := integral_const_mul _ _

/-- The range argument: for `0 ≤ G ≤ 2c` and `ρ ≥ 0`,
`2t(F ρ G − c F ρ) ≤ t² F² ρ + c² ρ`.

DERIVED: `2` is the square, the cross coefficient and the range `[0, 2c]`. -/
private theorem range_quad {t F ρ G c : ℝ} (hρ : 0 ≤ ρ) (hG0 : 0 ≤ G) (hG1 : G ≤ 2 * c) :
    2 * t * (F * ρ * G - c * (F * ρ)) ≤ t ^ 2 * (F ^ 2 * ρ) + c ^ 2 * ρ := by
  linarith [mul_nonneg hρ (sq_nonneg (t * F - (G - c))),
    mul_nonneg hρ (mul_nonneg hG0 (sub_nonneg.mpr hG1))]

/-- **(B) The pair mean of a centred left function**, homogeneous:
`|E[f e^u]| ≤ (τ σ mb + c₂ τ² M₂/2) √(E_μ f²)`.

DERIVED: `0` is the vanishing mean and the signs; `1` is `e⁰` and the norm bound of the feature;
`2` is the square and the halving of the range argument. -/
private theorem pair_M_abs (hX : Continuous X) (hX1 : ∀ g, ‖X g‖ ≤ 1) {τ M₂ mb σ c₂ : ℝ} {A : Set (Dens Ω)}
    (hτ : 0 ≤ τ) (hM₂ : 0 ≤ M₂) (hmb : 0 ≤ mb) (hc₂0 : 0 ≤ c₂) (hσ : 0 ≤ σ) (hσ2 : M₂ ≤ σ ^ 2)
    (hTB : DensBounds P X A M₂ mb) (hc₂ : ∀ u : ℝ, |u| ≤ τ → Real.exp u - 1 - u ≤ c₂ * u ^ 2)
    (S : E →L[ℝ] E) (hS : ‖S‖ ≤ τ) {θ₁ θ₂ : Dens Ω} (hθ₁ : θ₁ ∈ A) (hθ₂ : θ₂ ∈ A)
    {f : Ω → ℝ} (hf : Continuous f) (hf0 : ∫ h, f h * tiltDens P X θ₁ h ∂P = 0) :
    |pairInt P X S (fun h => f h * tiltDens P X θ₁ h) (tiltDens P X θ₂) Real.exp|
      ≤ dstarE τ M₂ σ mb c₂ * Real.sqrt (∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P) := by
  have hρ₁ := continuous_tiltDens (P := P) hX θ₁
  have hρ₂ := continuous_tiltDens (P := P) hX θ₂
  have hφ : Continuous fun h => f h * tiltDens P X θ₁ h := hf.mul hρ₁
  have hid : Continuous fun y : ℝ => y := continuous_id
  have hR : Continuous fun y : ℝ => Real.exp y - 1 - y :=
    (Real.continuous_exp.sub continuous_const).sub continuous_id
  have hvf0 : 0 ≤ ∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P :=
    integral_nonneg (fun h => mul_nonneg (sq_nonneg _) (tiltDens_nonneg (P := P) hX θ₁ h))
  -- the constant term vanishes
  have h1 : pairInt P X S (fun h => f h * tiltDens P X θ₁ h) (tiltDens P X θ₂) (fun _ => 1)
      = 0 := by
    rw [pairInt_row hX S hφ hρ₂ continuous_const]
    simp only [mul_one]
    rw [integral_tiltDens (P := P) hX θ₂]
    simp only [mul_one]
    exact hf0
  -- the linear term
  obtain ⟨v, hv⟩ : ∃ v, v = ∫ g, tiltDens P X θ₂ g • S (X g) ∂P := ⟨_, rfl⟩
  have hvn : ‖v‖ ≤ τ * mb := by
    rw [hv]
    exact mean_vec hX hτ hmb hTB S hS hθ₂
  have h2 : |pairInt P X S (fun h => f h * tiltDens P X θ₁ h) (tiltDens P X θ₂) (fun y => y)|
      ≤ σ * (τ * mb) * Real.sqrt (∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P) := by
    rw [pairInt_row hX S hφ hρ₂ hid]
    have e : ∫ h, f h * tiltDens P X θ₁ h
          * ∫ g, tiltDens P X θ₂ g * inner ℝ (X h) (S (X g)) ∂P ∂P
        = ∫ h, f h * inner ℝ v (X h) * tiltDens P X θ₁ h ∂P := by
      refine integral_congr_pointwise (fun h => ?_)
      rw [inner_integral_smul hX hρ₂ S (X h), ← hv, real_inner_comm]
      ring
    rw [e]
    have hcs := cs_tilt (P := P) hX θ₁ hf (continuous_const.inner hX : Continuous fun g => inner ℝ v (X g))
    have hsec := tilt_second hX hTB hθ₁ v
    have hM : Real.sqrt M₂ ≤ σ :=
      calc Real.sqrt M₂ ≤ Real.sqrt (σ ^ 2) := Real.sqrt_le_sqrt hσ2
        _ = σ := Real.sqrt_sq hσ
    have hsq : Real.sqrt (∫ h, inner ℝ v (X h) ^ 2 * tiltDens P X θ₁ h ∂P) ≤ σ * (τ * mb) := by
      calc Real.sqrt (∫ h, inner ℝ v (X h) ^ 2 * tiltDens P X θ₁ h ∂P)
          ≤ Real.sqrt (M₂ * ‖v‖ ^ 2) := Real.sqrt_le_sqrt hsec
        _ = Real.sqrt M₂ * ‖v‖ := by rw [Real.sqrt_mul hM₂, Real.sqrt_sq (norm_nonneg v)]
        _ ≤ σ * (τ * mb) := mul_le_mul hM hvn (norm_nonneg v) hσ
    calc |∫ h, f h * inner ℝ v (X h) * tiltDens P X θ₁ h ∂P|
        ≤ Real.sqrt (∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P)
          * Real.sqrt (∫ h, inner ℝ v (X h) ^ 2 * tiltDens P X θ₁ h ∂P) := hcs
      _ ≤ Real.sqrt (∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P) * (σ * (τ * mb)) :=
          mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
      _ = σ * (τ * mb) * Real.sqrt (∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P) := by ring
  -- the remainder, by the range argument
  have h3 : |pairInt P X S (fun h => f h * tiltDens P X θ₁ h) (tiltDens P X θ₂)
        (fun y => Real.exp y - 1 - y)|
      ≤ c₂ * τ ^ 2 * M₂ / 2 * Real.sqrt (∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P) := by
    rw [pairInt_row hX S hφ hρ₂ hR]
    have hrow := pairInt_row_integrable (P := P) hX S hφ hρ₂ hR
    have hc0 : 0 ≤ c₂ * τ ^ 2 * M₂ / 2 :=
      div_nonneg (mul_nonneg (mul_nonneg hc₂0 (sq_nonneg τ)) hM₂) zero_le_two
    have hlin : Integrable (fun h => c₂ * τ ^ 2 * M₂ / 2 * (f h * tiltDens P X θ₁ h)) P :=
      integrable_of_continuous P (continuous_const.mul hφ)
    have hF : Integrable (fun h => f h * tiltDens P X θ₁ h * ∫ g, tiltDens P X θ₂ g
          * (Real.exp (inner ℝ (X h) (S (X g))) - 1 - inner ℝ (X h) (S (X g))) ∂P
          - c₂ * τ ^ 2 * M₂ / 2 * (f h * tiltDens P X θ₁ h)) P :=
      hrow.sub hlin
    have hIeq : ∫ h, f h * tiltDens P X θ₁ h * ∫ g, tiltDens P X θ₂ g
          * (Real.exp (inner ℝ (X h) (S (X g))) - 1 - inner ℝ (X h) (S (X g))) ∂P ∂P
        = ∫ h, (f h * tiltDens P X θ₁ h * ∫ g, tiltDens P X θ₂ g
          * (Real.exp (inner ℝ (X h) (S (X g))) - 1 - inner ℝ (X h) (S (X g))) ∂P
          - c₂ * τ ^ 2 * M₂ / 2 * (f h * tiltDens P X θ₁ h)) ∂P := by
      rw [integral_sub hrow hlin, integral_const_mul, hf0, mul_zero, sub_zero]
    rw [hIeq]
    have hpt : ∀ (t : ℝ) (h : Ω), 2 * t * (f h * tiltDens P X θ₁ h * ∫ g, tiltDens P X θ₂ g
          * (Real.exp (inner ℝ (X h) (S (X g))) - 1 - inner ℝ (X h) (S (X g))) ∂P
          - c₂ * τ ^ 2 * M₂ / 2 * (f h * tiltDens P X θ₁ h))
        ≤ t ^ 2 * (f h ^ 2 * tiltDens P X θ₁ h)
          + (c₂ * τ ^ 2 * M₂ / 2) ^ 2 * tiltDens P X θ₁ h := by
      intro t h
      obtain ⟨hG0, hG1⟩ := G_bounds hX hX1 hτ hc₂0 hM₂ hTB hc₂ S hS hθ₂ (hX1 h)
      exact range_quad (tiltDens_nonneg (P := P) hX θ₁ h) hG0 (by linarith)
    have hq : ∀ t : ℝ, 2 * t * ∫ h, (f h * tiltDens P X θ₁ h * ∫ g, tiltDens P X θ₂ g
          * (Real.exp (inner ℝ (X h) (S (X g))) - 1 - inner ℝ (X h) (S (X g))) ∂P
          - c₂ * τ ^ 2 * M₂ / 2 * (f h * tiltDens P X θ₁ h)) ∂P
        ≤ t ^ 2 * ∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P + (c₂ * τ ^ 2 * M₂ / 2) ^ 2 := by
      intro t
      have hG2 : Integrable (fun h => f h ^ 2 * tiltDens P X θ₁ h) P :=
        integrable_of_continuous P ((hf.pow 2).mul hρ₁)
      have hK2 : Integrable (fun h => (c₂ * τ ^ 2 * M₂ / 2) ^ 2 * tiltDens P X θ₁ h) P :=
        integrable_of_continuous P (continuous_const.mul hρ₁)
      have hbase : 2 * t * ∫ h, (f h * tiltDens P X θ₁ h * ∫ g, tiltDens P X θ₂ g
            * (Real.exp (inner ℝ (X h) (S (X g))) - 1 - inner ℝ (X h) (S (X g))) ∂P
            - c₂ * τ ^ 2 * M₂ / 2 * (f h * tiltDens P X θ₁ h)) ∂P
          ≤ t ^ 2 * ∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P
            + ∫ h, (c₂ * τ ^ 2 * M₂ / 2) ^ 2 * tiltDens P X θ₁ h ∂P :=
        quad_integral hF hG2 hK2 hpt t
      have hK : ∫ h, (c₂ * τ ^ 2 * M₂ / 2) ^ 2 * tiltDens P X θ₁ h ∂P
          = (c₂ * τ ^ 2 * M₂ / 2) ^ 2 := by
        rw [integral_const_mul, integral_tiltDens (P := P) hX θ₁, mul_one]
      linarith
    have hs : (c₂ * τ ^ 2 * M₂ / 2 * Real.sqrt (∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P)) ^ 2
        = (∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P) * (c₂ * τ ^ 2 * M₂ / 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hvf0]
      ring
    exact abs_le_of_quad hvf0 (mul_nonneg hc0 (Real.sqrt_nonneg _)) (le_of_eq hs.symm) hq
  -- assemble
  rw [pairInt_split hX S hφ hρ₂, h1, zero_add]
  refine le_trans (abs_add_le _ _) ?_
  have h4 := add_le_add h2 h3
  unfold dstarE
  linarith [h4]

/-- **(A) The pair numerator of two centred functions**, homogeneous:
`E[f b e^u] ≤ (τ M₂ + c₂ τ² M₂) √(E_μ f²) √(E_ν b²)`.

DERIVED: `0` is the vanishing means and the signs; `1` is `e⁰` and the norm bound of the
feature; `2` is the square. -/
private theorem pair_N_le (hX : Continuous X) (hX1 : ∀ g, ‖X g‖ ≤ 1) {τ M₂ mb c₂ : ℝ} {A : Set (Dens Ω)}
    (hτ : 0 ≤ τ) (hM₂ : 0 ≤ M₂) (hc₂0 : 0 ≤ c₂)
    (hTB : DensBounds P X A M₂ mb) (hc₂ : ∀ u : ℝ, |u| ≤ τ → Real.exp u - 1 - u ≤ c₂ * u ^ 2)
    (S : E →L[ℝ] E) (hS : ‖S‖ ≤ τ) {θ₁ θ₂ : Dens Ω} (hθ₁ : θ₁ ∈ A) (hθ₂ : θ₂ ∈ A)
    {f b : Ω → ℝ} (hf : Continuous f) (hb : Continuous b)
    (hf0 : ∫ h, f h * tiltDens P X θ₁ h ∂P = 0) (hb0 : ∫ g, b g * tiltDens P X θ₂ g ∂P = 0) :
    pairInt P X S (fun h => f h * tiltDens P X θ₁ h) (fun g => b g * tiltDens P X θ₂ g)
        Real.exp
      ≤ (τ * M₂ + c₂ * τ ^ 2 * M₂)
        * (Real.sqrt (∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P)
          * Real.sqrt (∫ g, b g ^ 2 * tiltDens P X θ₂ g ∂P)) := by
  have hρ₁ := continuous_tiltDens (P := P) hX θ₁
  have hρ₂ := continuous_tiltDens (P := P) hX θ₂
  have hφ : Continuous fun h => f h * tiltDens P X θ₁ h := hf.mul hρ₁
  have hψ : Continuous fun g => b g * tiltDens P X θ₂ g := hb.mul hρ₂
  have hid : Continuous fun y : ℝ => y := continuous_id
  have hR : Continuous fun y : ℝ => Real.exp y - 1 - y :=
    (Real.continuous_exp.sub continuous_const).sub continuous_id
  have hvf0 : 0 ≤ ∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P :=
    integral_nonneg (fun h => mul_nonneg (sq_nonneg _) (tiltDens_nonneg (P := P) hX θ₁ h))
  have hvb0 : 0 ≤ ∫ g, b g ^ 2 * tiltDens P X θ₂ g ∂P :=
    integral_nonneg (fun g => mul_nonneg (sq_nonneg _) (tiltDens_nonneg (P := P) hX θ₂ g))
  -- the constant term vanishes
  have h1 : pairInt P X S (fun h => f h * tiltDens P X θ₁ h) (fun g => b g * tiltDens P X θ₂ g)
      (fun _ => 1) = 0 := by
    rw [pairInt_row hX S hφ hψ continuous_const]
    simp only [mul_one, hb0, mul_zero, integral_zero]
  -- the linear term, through the vector `w = ∫ b ρ₂ • S X`
  obtain ⟨w, hw⟩ : ∃ w, w = ∫ g, (b g * tiltDens P X θ₂ g) • S (X g) ∂P := ⟨_, rfl⟩
  have hw2 : ‖w‖ ≤ τ * Real.sqrt M₂ * Real.sqrt (∫ g, b g ^ 2 * tiltDens P X θ₂ g ∂P) := by
    have h0 := inner_integral_smul (P := P) hX hψ S w
    rw [← hw] at h0
    have hsq : ‖w‖ ^ 2 = ∫ g, b g * inner ℝ ((ContinuousLinearMap.adjoint S) w) (X g)
        * tiltDens P X θ₂ g ∂P := by
      rw [← real_inner_self_eq_norm_sq, ← h0]
      refine integral_congr_pointwise (fun g => ?_)
      rw [ContinuousLinearMap.adjoint_inner_left]
      ring
    have hcs := cs_tilt (P := P) hX θ₂ hb (continuous_const.inner hX : Continuous fun g => inner ℝ ((ContinuousLinearMap.adjoint S) w) (X g))
    have hsec := tilt_second hX hTB hθ₂ ((ContinuousLinearMap.adjoint S) w)
    have hadj := adj_norm_le S hS w
    have hK : 0 ≤ τ * Real.sqrt M₂ * Real.sqrt (∫ g, b g ^ 2 * tiltDens P X θ₂ g ∂P) :=
      mul_nonneg (mul_nonneg hτ (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    refine norm_le_of_sq_le hK ?_
    rw [hsq]
    calc ∫ g, b g * inner ℝ ((ContinuousLinearMap.adjoint S) w) (X g) * tiltDens P X θ₂ g ∂P
        ≤ |∫ g, b g * inner ℝ ((ContinuousLinearMap.adjoint S) w) (X g)
            * tiltDens P X θ₂ g ∂P| := le_abs_self _
      _ ≤ Real.sqrt (∫ g, b g ^ 2 * tiltDens P X θ₂ g ∂P)
          * Real.sqrt (∫ g, inner ℝ ((ContinuousLinearMap.adjoint S) w) (X g) ^ 2
            * tiltDens P X θ₂ g ∂P) := hcs
      _ ≤ Real.sqrt (∫ g, b g ^ 2 * tiltDens P X θ₂ g ∂P)
          * (Real.sqrt M₂ * ‖(ContinuousLinearMap.adjoint S) w‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
          calc Real.sqrt (∫ g, inner ℝ ((ContinuousLinearMap.adjoint S) w) (X g) ^ 2
                * tiltDens P X θ₂ g ∂P)
              ≤ Real.sqrt (M₂ * ‖(ContinuousLinearMap.adjoint S) w‖ ^ 2) :=
                Real.sqrt_le_sqrt hsec
            _ = Real.sqrt M₂ * ‖(ContinuousLinearMap.adjoint S) w‖ := by
                rw [Real.sqrt_mul hM₂, Real.sqrt_sq (norm_nonneg _)]
      _ ≤ Real.sqrt (∫ g, b g ^ 2 * tiltDens P X θ₂ g ∂P)
          * (Real.sqrt M₂ * (τ * ‖w‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hadj (Real.sqrt_nonneg _))
            (Real.sqrt_nonneg _)
      _ = τ * Real.sqrt M₂ * Real.sqrt (∫ g, b g ^ 2 * tiltDens P X θ₂ g ∂P) * ‖w‖ := by ring
  have h2 : |pairInt P X S (fun h => f h * tiltDens P X θ₁ h) (fun g => b g * tiltDens P X θ₂ g)
      (fun y => y)|
      ≤ τ * M₂ * (Real.sqrt (∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P)
        * Real.sqrt (∫ g, b g ^ 2 * tiltDens P X θ₂ g ∂P)) := by
    rw [pairInt_row hX S hφ hψ hid]
    have e : ∫ h, f h * tiltDens P X θ₁ h
          * ∫ g, b g * tiltDens P X θ₂ g * inner ℝ (X h) (S (X g)) ∂P ∂P
        = ∫ h, f h * inner ℝ w (X h) * tiltDens P X θ₁ h ∂P := by
      refine integral_congr_pointwise (fun h => ?_)
      rw [inner_integral_smul hX hψ S (X h), ← hw, real_inner_comm]
      ring
    rw [e]
    have hcs := cs_tilt (P := P) hX θ₁ hf (continuous_const.inner hX : Continuous fun g => inner ℝ w (X g))
    have hsec := tilt_second hX hTB hθ₁ w
    have hs1 : Real.sqrt (∫ h, inner ℝ w (X h) ^ 2 * tiltDens P X θ₁ h ∂P)
        ≤ Real.sqrt M₂ * ‖w‖ := by
      calc Real.sqrt (∫ h, inner ℝ w (X h) ^ 2 * tiltDens P X θ₁ h ∂P)
          ≤ Real.sqrt (M₂ * ‖w‖ ^ 2) := Real.sqrt_le_sqrt hsec
        _ = Real.sqrt M₂ * ‖w‖ := by rw [Real.sqrt_mul hM₂, Real.sqrt_sq (norm_nonneg w)]
    have hs2 : Real.sqrt M₂ * ‖w‖
        ≤ Real.sqrt M₂ * (τ * Real.sqrt M₂ * Real.sqrt (∫ g, b g ^ 2 * tiltDens P X θ₂ g ∂P)) :=
      mul_le_mul_of_nonneg_left hw2 (Real.sqrt_nonneg _)
    have hM : Real.sqrt M₂ * Real.sqrt M₂ = M₂ := Real.mul_self_sqrt hM₂
    calc |∫ h, f h * inner ℝ w (X h) * tiltDens P X θ₁ h ∂P|
        ≤ Real.sqrt (∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P)
          * Real.sqrt (∫ h, inner ℝ w (X h) ^ 2 * tiltDens P X θ₁ h ∂P) := hcs
      _ ≤ Real.sqrt (∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P)
          * (Real.sqrt M₂ * (τ * Real.sqrt M₂
            * Real.sqrt (∫ g, b g ^ 2 * tiltDens P X θ₂ g ∂P))) :=
          mul_le_mul_of_nonneg_left (le_trans hs1 hs2) (Real.sqrt_nonneg _)
      _ = τ * (Real.sqrt M₂ * Real.sqrt M₂) * (Real.sqrt (∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P)
          * Real.sqrt (∫ g, b g ^ 2 * tiltDens P X θ₂ g ∂P)) := by ring
      _ = τ * M₂ * (Real.sqrt (∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P)
          * Real.sqrt (∫ g, b g ^ 2 * tiltDens P X θ₂ g ∂P)) := by rw [hM]
  -- the remainder, by the quadratic form on the product
  have h3 : |pairInt P X S (fun h => f h * tiltDens P X θ₁ h) (fun g => b g * tiltDens P X θ₂ g)
      (fun y => Real.exp y - 1 - y)|
      ≤ c₂ * τ ^ 2 * M₂ * (Real.sqrt (∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P)
        * Real.sqrt (∫ g, b g ^ 2 * tiltDens P X θ₂ g ∂P)) := by
    have hA : pairInt P X S (fun h => f h ^ 2 * tiltDens P X θ₁ h) (tiltDens P X θ₂)
        (fun y => Real.exp y - 1 - y)
        ≤ c₂ * τ ^ 2 * M₂ * ∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P :=
      pair_R_le hX hX1 hτ hc₂0 hM₂ hTB hc₂ S hS hθ₂ ((hf.pow 2).mul hρ₁)
        (fun h => mul_nonneg (sq_nonneg _) (tiltDens_nonneg (P := P) hX θ₁ h))
    have hB : pairInt P X S (tiltDens P X θ₁) (fun g => b g ^ 2 * tiltDens P X θ₂ g)
        (fun y => Real.exp y - 1 - y)
        ≤ c₂ * τ ^ 2 * M₂ * ∫ g, b g ^ 2 * tiltDens P X θ₂ g ∂P := by
      rw [pairInt_swap]
      exact pair_R_le hX hX1 hτ hc₂0 hM₂ hTB hc₂ (ContinuousLinearMap.adjoint S)
        (by rw [adj_opnorm]; exact hS) hθ₁ ((hb.pow 2).mul hρ₂)
        (fun g => mul_nonneg (sq_nonneg _) (tiltDens_nonneg (P := P) hX θ₂ g))
    have hptP : ∀ (t : ℝ) (p : Ω × Ω),
        2 * t * (f p.1 * tiltDens P X θ₁ p.1 * (b p.2 * tiltDens P X θ₂ p.2)
          * (Real.exp (inner ℝ (X p.1) (S (X p.2))) - 1 - inner ℝ (X p.1) (S (X p.2))))
        ≤ t ^ 2 * (f p.1 ^ 2 * tiltDens P X θ₁ p.1 * tiltDens P X θ₂ p.2
          * (Real.exp (inner ℝ (X p.1) (S (X p.2))) - 1 - inner ℝ (X p.1) (S (X p.2))))
          + tiltDens P X θ₁ p.1 * (b p.2 ^ 2 * tiltDens P X θ₂ p.2)
            * (Real.exp (inner ℝ (X p.1) (S (X p.2))) - 1 - inner ℝ (X p.1) (S (X p.2))) := by
      intro t p
      have hR0 : 0 ≤ Real.exp (inner ℝ (X p.1) (S (X p.2))) - 1 - inner ℝ (X p.1) (S (X p.2)) := by
        linarith [Real.add_one_le_exp (inner ℝ (X p.1) (S (X p.2)))]
      have hw0 : 0 ≤ tiltDens P X θ₁ p.1 * tiltDens P X θ₂ p.2
          * (Real.exp (inner ℝ (X p.1) (S (X p.2))) - 1 - inner ℝ (X p.1) (S (X p.2))) :=
        mul_nonneg (mul_nonneg (tiltDens_nonneg (P := P) hX θ₁ p.1) (tiltDens_nonneg (P := P) hX θ₂ p.2)) hR0
      linarith [mul_nonneg hw0 (sq_nonneg (t * f p.1 - b p.2))]
    have hq : ∀ t : ℝ, 2 * t * pairInt P X S (fun h => f h * tiltDens P X θ₁ h)
          (fun g => b g * tiltDens P X θ₂ g) (fun y => Real.exp y - 1 - y)
        ≤ t ^ 2 * (c₂ * τ ^ 2 * M₂ * ∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P)
          + c₂ * τ ^ 2 * M₂ * ∫ g, b g ^ 2 * tiltDens P X θ₂ g ∂P := by
      intro t
      have hbase : 2 * t * pairInt P X S (fun h => f h * tiltDens P X θ₁ h)
            (fun g => b g * tiltDens P X θ₂ g) (fun y => Real.exp y - 1 - y)
          ≤ t ^ 2 * pairInt P X S (fun h => f h ^ 2 * tiltDens P X θ₁ h) (tiltDens P X θ₂)
              (fun y => Real.exp y - 1 - y)
            + pairInt P X S (tiltDens P X θ₁) (fun g => b g ^ 2 * tiltDens P X θ₂ g)
              (fun y => Real.exp y - 1 - y) := by
        unfold pairInt
        exact quad_integral (integrable_std (P := P) hX S hφ hψ hR)
          (integrable_std (P := P) hX S ((hf.pow 2).mul hρ₁) hρ₂ hR)
          (integrable_std (P := P) hX S hρ₁ ((hb.pow 2).mul hρ₂) hR) hptP t
      have ht := mul_le_mul_of_nonneg_left hA (sq_nonneg t)
      linarith
    have hs : (c₂ * τ ^ 2 * M₂ * (Real.sqrt (∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P)
          * Real.sqrt (∫ g, b g ^ 2 * tiltDens P X θ₂ g ∂P))) ^ 2
        = c₂ * τ ^ 2 * M₂ * (∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P)
          * (c₂ * τ ^ 2 * M₂ * ∫ g, b g ^ 2 * tiltDens P X θ₂ g ∂P) := by
      have hss : (Real.sqrt (∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P)
          * Real.sqrt (∫ g, b g ^ 2 * tiltDens P X θ₂ g ∂P)) ^ 2
          = (∫ h, f h ^ 2 * tiltDens P X θ₁ h ∂P) * ∫ g, b g ^ 2 * tiltDens P X θ₂ g ∂P := by
        rw [mul_pow, Real.sq_sqrt hvf0, Real.sq_sqrt hvb0]
      rw [mul_pow, hss]
      ring
    have hGm : 0 ≤ c₂ * τ ^ 2 * M₂ := mul_nonneg (mul_nonneg hc₂0 (sq_nonneg τ)) hM₂
    exact abs_le_of_quad (mul_nonneg hGm hvf0)
      (mul_nonneg hGm (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
      (le_of_eq hs.symm) hq
  -- assemble
  rw [pairInt_split hX S hφ hψ, h1, zero_add]
  refine le_trans (le_abs_self _) (le_trans (abs_add_le _ _) ?_)
  have h4 := add_le_add h2 h3
  linarith [h4]

end Bounds

/-! ## 4. From the fibre weight to the pair integrals -/

section Conversion

/-- **The density weight is the normalised pair density**:
`K e^u α(h) γ(g) = K Z_α Z_γ · ρ_α(h) ρ_γ(g) e^u`.

DERIVED: no numeral. -/
private theorem fw_eq (hX : Continuous X) (K : ℝ) (T : E →L[ℝ] E) (α γ : Dens Ω) (h g : Ω) :
    densWeight X K T α γ h g
      = K * (∫ g', α.f g' ∂P) * (∫ g', γ.f g' ∂P)
        * (tiltDens P X α h * tiltDens P X γ g * Real.exp (inner ℝ (X h) (T (X g)))) := by
  have hZa := (tiltZ_pos (P := P) hX α).ne'
  have hZg := (tiltZ_pos (P := P) hX γ).ne'
  have e1 : α.f h
      = tiltDens P X α h * ∫ g', α.f g' ∂P := by
    unfold tiltDens
    exact (div_mul_cancel₀ _ hZa).symm
  have e2 : γ.f g
      = tiltDens P X γ g * ∫ g', γ.f g' ∂P := by
    unfold tiltDens
    exact (div_mul_cancel₀ _ hZg).symm
  unfold densWeight
  rw [e1, e2]
  ring

/-- The iterated fibre integral of `φ₀(h) ψ₀(g) w` is `K Z_α Z_γ` times a pair integral.

DERIVED: no numeral. -/
private theorem conv_iter (hX : Continuous X) {K : ℝ} {T : E →L[ℝ] E} {α γ : Dens Ω}
    {φ₀ ψ₀ : Ω → ℝ} (hφ₀ : Continuous φ₀) (hψ₀ : Continuous ψ₀) :
    ∫ h, ∫ g, φ₀ h * ψ₀ g * densWeight X K T α γ h g ∂P ∂P
      = K * (∫ g', α.f g' ∂P) * (∫ g', γ.f g' ∂P)
        * pairInt P X T (fun h => φ₀ h * tiltDens P X α h) (fun g => ψ₀ g * tiltDens P X γ g)
            Real.exp := by
  have hφ : Continuous fun h => φ₀ h * tiltDens P X α h := hφ₀.mul (continuous_tiltDens (P := P) hX α)
  have hψ : Continuous fun g => ψ₀ g * tiltDens P X γ g := hψ₀.mul (continuous_tiltDens (P := P) hX γ)
  obtain ⟨Za, hZa⟩ : ∃ z, z = ∫ g', α.f g' ∂P := ⟨_, rfl⟩
  obtain ⟨Zg, hZg⟩ : ∃ z, z = ∫ g', γ.f g' ∂P := ⟨_, rfl⟩
  rw [← hZa, ← hZg, pairInt_row hX T hφ hψ Real.continuous_exp, ← integral_const_mul]
  refine integral_congr_pointwise (fun h => ?_)
  calc ∫ g, φ₀ h * ψ₀ g * densWeight X K T α γ h g ∂P
      = ∫ g, K * Za * Zg * (φ₀ h * tiltDens P X α h)
          * (ψ₀ g * tiltDens P X γ g * Real.exp (inner ℝ (X h) (T (X g)))) ∂P :=
        integral_congr_pointwise (fun g => by rw [fw_eq (P := P) hX, ← hZa, ← hZg]; ring)
    _ = K * Za * Zg * (φ₀ h * tiltDens P X α h)
          * ∫ g, ψ₀ g * tiltDens P X γ g * Real.exp (inner ℝ (X h) (T (X g))) ∂P :=
        integral_const_mul _ _
    _ = K * Za * Zg * (φ₀ h * tiltDens P X α h
          * ∫ g, ψ₀ g * tiltDens P X γ g * Real.exp (inner ℝ (X h) (T (X g))) ∂P) := by ring

/-- The row form `∫ φ₀(h) q(h)` of the fibre integral.

DERIVED: no numeral. -/
private theorem conv_row (hX : Continuous X) {K : ℝ} {T : E →L[ℝ] E} {α γ : Dens Ω}
    {φ₀ : Ω → ℝ} (hφ₀ : Continuous φ₀) :
    ∫ h, φ₀ h * ∫ g, densWeight X K T α γ h g ∂P ∂P
      = K * (∫ g', α.f g' ∂P) * (∫ g', γ.f g' ∂P)
        * pairInt P X T (fun h => φ₀ h * tiltDens P X α h) (tiltDens P X γ) Real.exp := by
  have hφ : Continuous fun h => φ₀ h * tiltDens P X α h := hφ₀.mul (continuous_tiltDens (P := P) hX α)
  obtain ⟨Za, hZa⟩ : ∃ z, z = ∫ g', α.f g' ∂P := ⟨_, rfl⟩
  obtain ⟨Zg, hZg⟩ : ∃ z, z = ∫ g', γ.f g' ∂P := ⟨_, rfl⟩
  rw [← hZa, ← hZg, pairInt_row hX T hφ (continuous_tiltDens (P := P) hX γ) Real.continuous_exp,
    ← integral_const_mul]
  refine integral_congr_pointwise (fun h => ?_)
  have hin : ∫ g, densWeight X K T α γ h g ∂P
      = ∫ g, K * Za * Zg * tiltDens P X α h
          * (tiltDens P X γ g * Real.exp (inner ℝ (X h) (T (X g)))) ∂P :=
    integral_congr_pointwise (fun g => by rw [fw_eq (P := P) hX, ← hZa, ← hZg]; ring)
  rw [hin, integral_const_mul]
  ring

/-- The column form `∫ ψ₀(g) p(g)` of the fibre integral (the swap and the adjoint).

DERIVED: no numeral. -/
private theorem conv_col (hX : Continuous X) {K : ℝ} {T : E →L[ℝ] E} {α γ : Dens Ω}
    {ψ₀ : Ω → ℝ} (hψ₀ : Continuous ψ₀) :
    ∫ g, ψ₀ g * ∫ h, densWeight X K T α γ h g ∂P ∂P
      = K * (∫ g', α.f g' ∂P) * (∫ g', γ.f g' ∂P)
        * pairInt P X T (tiltDens P X α) (fun g => ψ₀ g * tiltDens P X γ g) Real.exp := by
  have hψ : Continuous fun g => ψ₀ g * tiltDens P X γ g := hψ₀.mul (continuous_tiltDens (P := P) hX γ)
  obtain ⟨Za, hZa⟩ : ∃ z, z = ∫ g', α.f g' ∂P := ⟨_, rfl⟩
  obtain ⟨Zg, hZg⟩ : ∃ z, z = ∫ g', γ.f g' ∂P := ⟨_, rfl⟩
  rw [← hZa, ← hZg, pairInt_swap, pairInt_row hX (ContinuousLinearMap.adjoint T) hψ
    (continuous_tiltDens (P := P) hX α) Real.continuous_exp, ← integral_const_mul]
  refine integral_congr_pointwise (fun g => ?_)
  have hin : ∫ h, densWeight X K T α γ h g ∂P
      = ∫ h, K * Za * Zg * tiltDens P X γ g
          * (tiltDens P X α h
            * Real.exp (inner ℝ (X g) ((ContinuousLinearMap.adjoint T) (X h)))) ∂P :=
    integral_congr_pointwise (fun h => by
      rw [fw_eq (P := P) hX, ← hZa, ← hZg, adj_swap_inner]; ring)
  rw [hin, integral_const_mul]
  ring

end Conversion

/-! ## 5. The assembly -/

/-- **The algebra of the assembly (E).** With `E_π a = 0` written as `a₀ Z + m_a = 0`, the bounds
`|m_a| ≤ e x`, `|m_b| ≤ e y`, `S_a ≥ q x²`, `S_b ≥ q y²`, `N ≤ n₀ x y`, `Z ≥ Z₀ > 0`,
`q − e²/Z₀ > 0` give `E_π[ab] ≤ (dstar/2)(E_π a² + E_π b²)` with `dstar = (n₀ + e²/Z₀)/(q − e²/Z₀)`.

DERIVED: `0` is the signs and the vanishing mean; `2` is the square, the cross coefficient and
the halving. -/
private theorem assemble {Z Z₀ ma mb Sa Sb Nn a₀ b₀ x y e n₀ q : ℝ}
    (hZ0 : 0 < Z₀) (hZ : Z₀ ≤ Z) (hx : 0 ≤ x) (hy : 0 ≤ y) (he : 0 ≤ e) (hn₀ : 0 ≤ n₀)
    (hma : |ma| ≤ e * x) (hmb : |mb| ≤ e * y) (hSa : q * x ^ 2 ≤ Sa) (hSb : q * y ^ 2 ≤ Sb)
    (hN : Nn ≤ n₀ * (x * y)) (hden : 0 < q - e ^ 2 / Z₀) (hzero : a₀ * Z + ma = 0) :
    a₀ * b₀ * Z + a₀ * mb + b₀ * ma + Nn
      ≤ (n₀ + e ^ 2 / Z₀) / (q - e ^ 2 / Z₀) / 2
        * ((a₀ ^ 2 * Z + 2 * a₀ * ma + Sa) + (b₀ ^ 2 * Z + 2 * b₀ * mb + Sb)) := by
  have hZpos : 0 < Z := lt_of_lt_of_le hZ0 hZ
  obtain ⟨D, hD⟩ : ∃ D, D = q - e ^ 2 / Z₀ := ⟨_, rfl⟩
  obtain ⟨Nm, hNm⟩ : ∃ Nm, Nm = n₀ + e ^ 2 / Z₀ := ⟨_, rfl⟩
  rw [← hD, ← hNm]
  have hDpos : 0 < D := by rw [hD]; exact hden
  have hE0 : 0 ≤ e ^ 2 / Z₀ := div_nonneg (sq_nonneg e) hZ0.le
  have hNm0 : 0 ≤ Nm := by rw [hNm]; linarith
  -- the cross term
  have k1 : a₀ * mb ≤ e ^ 2 / Z₀ * (x * y) := by
    have h1 : a₀ * mb * Z = -(ma * mb) := by linear_combination mb * hzero
    have h2 : -(ma * mb) ≤ e ^ 2 * (x * y) := by
      calc -(ma * mb) ≤ |ma * mb| := neg_le_abs _
        _ = |ma| * |mb| := abs_mul _ _
        _ ≤ (e * x) * (e * y) := mul_le_mul hma hmb (abs_nonneg _) (mul_nonneg he hx)
        _ = e ^ 2 * (x * y) := by ring
    have h3 : a₀ * mb ≤ e ^ 2 * (x * y) / Z := by
      rw [le_div_iff₀ hZpos]
      linarith
    have h4 : e ^ 2 * (x * y) / Z ≤ e ^ 2 * (x * y) / Z₀ :=
      div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg e) (mul_nonneg hx hy)) hZ0 hZ
    have h5 : e ^ 2 * (x * y) / Z₀ = e ^ 2 / Z₀ * (x * y) := by ring
    linarith
  -- the left variance
  have k2 : D * x ^ 2 ≤ a₀ ^ 2 * Z + 2 * a₀ * ma + Sa := by
    have h1 : a₀ ^ 2 * Z + 2 * a₀ * ma = a₀ * ma := by linear_combination a₀ * hzero
    have h2 : a₀ * ma * Z = -(ma ^ 2) := by linear_combination ma * hzero
    have h3 : ma ^ 2 ≤ e ^ 2 * x ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg ma) hma 2
      rw [sq_abs] at h
      linarith [h]
    have h5 : a₀ * ma = -(ma ^ 2) / Z := by
      rw [eq_div_iff hZpos.ne']
      exact h2
    have h6 : ma ^ 2 / Z ≤ e ^ 2 * x ^ 2 / Z₀ :=
      le_trans (div_le_div_of_nonneg_right h3 hZpos.le)
        (div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg e) (sq_nonneg x)) hZ0 hZ)
    have h7 : e ^ 2 * x ^ 2 / Z₀ = e ^ 2 / Z₀ * x ^ 2 := by ring
    have h8 : -(ma ^ 2) / Z = -(ma ^ 2 / Z) := neg_div Z (ma ^ 2)
    rw [h1, hD]
    linarith
  -- the right variance
  have k3 : D * y ^ 2 ≤ b₀ ^ 2 * Z + 2 * b₀ * mb + Sb := by
    have h1 : -(mb ^ 2) / Z ≤ b₀ ^ 2 * Z + 2 * b₀ * mb := by
      rw [div_le_iff₀ hZpos]
      have e0 : (b₀ ^ 2 * Z + 2 * b₀ * mb) * Z + mb ^ 2 = (b₀ * Z + mb) ^ 2 := by ring
      linarith [sq_nonneg (b₀ * Z + mb)]
    have h3 : mb ^ 2 ≤ e ^ 2 * y ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg mb) hmb 2
      rw [sq_abs] at h
      linarith [h]
    have h6 : mb ^ 2 / Z ≤ e ^ 2 * y ^ 2 / Z₀ :=
      le_trans (div_le_div_of_nonneg_right h3 hZpos.le)
        (div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg e) (sq_nonneg y)) hZ0 hZ)
    have h7 : e ^ 2 * y ^ 2 / Z₀ = e ^ 2 / Z₀ * y ^ 2 := by ring
    have h8 : -(mb ^ 2) / Z = -(mb ^ 2 / Z) := neg_div Z (mb ^ 2)
    rw [hD]
    linarith
  -- the covariance
  have k4 : a₀ * b₀ * Z + a₀ * mb + b₀ * ma + Nn = a₀ * mb + Nn := by
    linear_combination b₀ * hzero
  rw [k4]
  have hNmxy : Nm * (x * y) = n₀ * (x * y) + e ^ 2 / Z₀ * (x * y) := by rw [hNm]; ring
  have hxy : x * y ≤ (x ^ 2 + y ^ 2) / 2 := by linarith [sq_nonneg (x - y)]
  have hcoef : 0 ≤ Nm / D / 2 := div_nonneg (div_nonneg hNm0 hDpos.le) zero_le_two
  calc a₀ * mb + Nn ≤ Nm * (x * y) := by linarith
    _ ≤ Nm * ((x ^ 2 + y ^ 2) / 2) := mul_le_mul_of_nonneg_left hxy hNm0
    _ = Nm / D / 2 * (D * x ^ 2 + D * y ^ 2) := by
        rw [show Nm / D / 2 * (D * x ^ 2 + D * y ^ 2) = Nm / D * D * ((x ^ 2 + y ^ 2) / 2) by ring,
          div_mul_cancel₀ Nm hDpos.ne']
    _ ≤ Nm / D / 2 * ((a₀ ^ 2 * Z + 2 * a₀ * ma + Sa) + (b₀ ^ 2 * Z + 2 * b₀ * mb + Sb)) :=
        mul_le_mul_of_nonneg_left (by linarith) hcoef

/-! ## 6. The stated results -/

/-- **(D) The partition function against the tilted product law** is at least `Z₀`.

DERIVED: `0` is the lower end of `τ`; `1` is the norm bound of the feature. -/
theorem Z_lower (hX : Continuous X) (hX1 : ∀ g, ‖X g‖ ≤ 1) {τ M₂ mb : ℝ} {A : Set (Dens Ω)} (hτ : 0 ≤ τ)
    (hTB : DensBounds P X A M₂ mb) {T : E →L[ℝ] E} (hT : ‖T‖ ≤ τ) {α γ : Dens Ω} (hα : α ∈ A)
    (hγ : γ ∈ A) :
    dstarZ τ mb
      ≤ ∫ h, ∫ g, Real.exp (inner ℝ (X h) (T (X g))) * tiltDens P X α h * tiltDens P X γ g ∂P ∂P := by
  have h1 := pair_Z_ge hX hτ hTB T hT hα hγ
  rw [pairInt_row hX T (continuous_tiltDens (P := P) hX α) (continuous_tiltDens (P := P) hX γ)
    Real.continuous_exp] at h1
  have e : ∫ h, ∫ g, Real.exp (inner ℝ (X h) (T (X g))) * tiltDens P X α h * tiltDens P X γ g
        ∂P ∂P
      = ∫ h, tiltDens P X α h
          * ∫ g, tiltDens P X γ g * Real.exp (inner ℝ (X h) (T (X g))) ∂P ∂P := by
    refine integral_congr_pointwise (fun h => ?_)
    rw [← integral_const_mul]
    exact integral_congr_pointwise (fun g => by ring)
  rw [e]
  exact h1

#print axioms Z_lower

/-- **The pair fibre bound** ((A)–(D) and the assembly (E) of the module docstring).

DERIVED: `0` is the lower end of `τ`, `M₂`, `mb`, `c₂`, `σ` and of `Z₀`, `den`; `1` is the norm
bound of the feature; `2` is the square. -/
theorem densFibreBound_of_densBounds (hX : Continuous X) (hX1 : ∀ g, ‖X g‖ ≤ 1)
    {τ M₂ mb σ c₂ : ℝ} {A : Set (Dens Ω)} (hτ : 0 ≤ τ) (hM₂ : 0 ≤ M₂) (hmb : 0 ≤ mb) (hc₂0 : 0 ≤ c₂)
    (hTB : DensBounds P X A M₂ mb)
    (hc₂ : ∀ u : ℝ, |u| ≤ τ → Real.exp u - 1 - u ≤ c₂ * u ^ 2)
    (hσ : 0 ≤ σ) (hσ2 : M₂ ≤ σ ^ 2)
    (hZ : 0 < dstarZ τ mb) (hden : 0 < dstarDen τ M₂ σ mb c₂) :
    DensFibreBound P X (dstar τ M₂ σ mb c₂) τ A := by
  intro K T α γ hK hT hα hγ a b ha hb hzero
  have hρ₁ := continuous_tiltDens (P := P) hX α
  have hρ₂ := continuous_tiltDens (P := P) hX γ
  have hC : 0 < K * (∫ g', α.f g' ∂P)
      * (∫ g', γ.f g' ∂P) :=
    mul_pos (mul_pos hK (tiltZ_pos (P := P) hX α)) (tiltZ_pos (P := P) hX γ)
  -- the fibre integrals as pair integrals
  have c1 := conv_iter (P := P) (K := K) (T := T) (α := α) (γ := γ) hX ha hb
  have c2 := conv_row (P := P) (K := K) (T := T) (α := α) (γ := γ) hX ha
  have ha2 : Continuous fun h => a h ^ 2 := ha.pow 2
  have hb2 : Continuous fun g => b g ^ 2 := hb.pow 2
  have c3 := conv_row (P := P) (K := K) (T := T) (α := α) (γ := γ) hX ha2
  have c4 := conv_col (P := P) (K := K) (T := T) (α := α) (γ := γ) hX hb2
  rw [c1, c3, c4]
  rw [c2] at hzero
  have hz : pairInt P X T (fun h => a h * tiltDens P X α h) (tiltDens P X γ) Real.exp = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hC.ne'
  -- centring
  obtain ⟨a₀, ha₀⟩ : ∃ z, z = ∫ h, a h * tiltDens P X α h ∂P := ⟨_, rfl⟩
  obtain ⟨b₀, hb₀⟩ : ∃ z, z = ∫ g, b g * tiltDens P X γ g ∂P := ⟨_, rfl⟩
  have hfa : Continuous fun h => a h - a₀ := ha.sub continuous_const
  have hfb : Continuous fun g => b g - b₀ := hb.sub continuous_const
  have hfa0 : ∫ h, (a h - a₀) * tiltDens P X α h ∂P = 0 := by
    have e : ∫ h, (a h - a₀) * tiltDens P X α h ∂P
        = ∫ h, a h * tiltDens P X α h ∂P - a₀ * ∫ h, tiltDens P X α h ∂P := by
      have i1 : Integrable (fun h => a h * tiltDens P X α h) P :=
        integrable_of_continuous P (ha.mul hρ₁)
      have i2 : Integrable (fun h => a₀ * tiltDens P X α h) P :=
        (integrable_of_continuous P hρ₁).const_mul a₀
      rw [← integral_const_mul, ← integral_sub i1 i2]
      exact integral_congr_pointwise (fun h => by ring)
    rw [e, integral_tiltDens (P := P) hX α, ← ha₀]
    ring
  have hfb0 : ∫ g, (b g - b₀) * tiltDens P X γ g ∂P = 0 := by
    have e : ∫ g, (b g - b₀) * tiltDens P X γ g ∂P
        = ∫ g, b g * tiltDens P X γ g ∂P - b₀ * ∫ g, tiltDens P X γ g ∂P := by
      have i1 : Integrable (fun g => b g * tiltDens P X γ g) P :=
        integrable_of_continuous P (hb.mul hρ₂)
      have i2 : Integrable (fun g => b₀ * tiltDens P X γ g) P :=
        (integrable_of_continuous P hρ₂).const_mul b₀
      rw [← integral_const_mul, ← integral_sub i1 i2]
      exact integral_congr_pointwise (fun g => by ring)
    rw [e, integral_tiltDens (P := P) hX γ, ← hb₀]
    ring
  have hvf0 : 0 ≤ ∫ h, (a h - a₀) ^ 2 * tiltDens P X α h ∂P :=
    integral_nonneg (fun h => mul_nonneg (sq_nonneg _) (tiltDens_nonneg (P := P) hX α h))
  have hvb0 : 0 ≤ ∫ g, (b g - b₀) ^ 2 * tiltDens P X γ g ∂P :=
    integral_nonneg (fun g => mul_nonneg (sq_nonneg _) (tiltDens_nonneg (P := P) hX γ g))
  have hTa : ‖ContinuousLinearMap.adjoint T‖ ≤ τ := by rw [adj_opnorm]; exact hT
  -- the bounds (A)–(D)
  have hZlow : dstarZ τ mb
      ≤ pairInt P X T (tiltDens P X α) (tiltDens P X γ) Real.exp :=
    pair_Z_ge hX hτ hTB T hT hα hγ
  have hMA : |pairInt P X T (fun h => (a h - a₀) * tiltDens P X α h) (tiltDens P X γ) Real.exp|
      ≤ dstarE τ M₂ σ mb c₂ * Real.sqrt (∫ h, (a h - a₀) ^ 2 * tiltDens P X α h ∂P) :=
    pair_M_abs hX hX1 hτ hM₂ hmb hc₂0 hσ hσ2 hTB hc₂ T hT hα hγ hfa hfa0
  have hMB : |pairInt P X T (tiltDens P X α) (fun g => (b g - b₀) * tiltDens P X γ g) Real.exp|
      ≤ dstarE τ M₂ σ mb c₂ * Real.sqrt (∫ g, (b g - b₀) ^ 2 * tiltDens P X γ g ∂P) := by
    rw [pairInt_swap]
    exact pair_M_abs hX hX1 hτ hM₂ hmb hc₂0 hσ hσ2 hTB hc₂ (ContinuousLinearMap.adjoint T) hTa
      hγ hα hfb hfb0
  have hSA : (1 - τ * mb) * Real.sqrt (∫ h, (a h - a₀) ^ 2 * tiltDens P X α h ∂P) ^ 2
      ≤ pairInt P X T (fun h => (a h - a₀) ^ 2 * tiltDens P X α h) (tiltDens P X γ) Real.exp := by
    rw [Real.sq_sqrt hvf0]
    exact pair_S_ge hX hX1 hτ hmb hTB T hT hγ hfa
  have hSB : (1 - τ * mb) * Real.sqrt (∫ g, (b g - b₀) ^ 2 * tiltDens P X γ g ∂P) ^ 2
      ≤ pairInt P X T (tiltDens P X α) (fun g => (b g - b₀) ^ 2 * tiltDens P X γ g) Real.exp := by
    rw [Real.sq_sqrt hvb0, pairInt_swap]
    exact pair_S_ge hX hX1 hτ hmb hTB (ContinuousLinearMap.adjoint T) hTa hα hfb
  have hNN : pairInt P X T (fun h => (a h - a₀) * tiltDens P X α h)
        (fun g => (b g - b₀) * tiltDens P X γ g) Real.exp
      ≤ (τ * M₂ + c₂ * τ ^ 2 * M₂)
        * (Real.sqrt (∫ h, (a h - a₀) ^ 2 * tiltDens P X α h ∂P)
          * Real.sqrt (∫ g, (b g - b₀) ^ 2 * tiltDens P X γ g ∂P)) :=
    pair_N_le hX hX1 hτ hM₂ hc₂0 hTB hc₂ T hT hα hγ hfa hfb hfa0 hfb0
  -- the expansions around the means
  have hE1 := expand_left (P := P) hX T ha hρ₂ a₀ α
  have hbρ : Continuous fun g => b g * tiltDens P X γ g := hb.mul hρ₂
  have hfaρ : Continuous fun h => (a h - a₀) * tiltDens P X α h := hfa.mul hρ₁
  have hE2a := expand_left (P := P) hX T ha hbρ a₀ α
  have hE2b := expand_right (P := P) hX T hρ₁ hb b₀ γ
  have hE2c := expand_right (P := P) hX T hfaρ hb b₀ γ
  have hE3 := expand_sq_left (P := P) hX T ha hρ₂ a₀ α
  have hE4 := expand_sq_right (P := P) hX T hρ₁ hb b₀ γ
  have hzero' : a₀ * pairInt P X T (tiltDens P X α) (tiltDens P X γ) Real.exp
      + pairInt P X T (fun h => (a h - a₀) * tiltDens P X α h) (tiltDens P X γ) Real.exp = 0 := by
    rw [← hE1]
    exact hz
  have he : 0 ≤ dstarE τ M₂ σ mb c₂ := by
    unfold dstarE
    have h1 : 0 ≤ τ * σ * mb := mul_nonneg (mul_nonneg hτ hσ) hmb
    have h2 : 0 ≤ c₂ * τ ^ 2 * M₂ / 2 :=
      div_nonneg (mul_nonneg (mul_nonneg hc₂0 (sq_nonneg τ)) hM₂) zero_le_two
    linarith
  have hn₀ : 0 ≤ τ * M₂ + c₂ * τ ^ 2 * M₂ :=
    add_nonneg (mul_nonneg hτ hM₂) (mul_nonneg (mul_nonneg hc₂0 (sq_nonneg τ)) hM₂)
  have hden' : 0 < 1 - τ * mb - dstarE τ M₂ σ mb c₂ ^ 2 / dstarZ τ mb := hden
  have key : a₀ * b₀ * pairInt P X T (tiltDens P X α) (tiltDens P X γ) Real.exp
        + a₀ * pairInt P X T (tiltDens P X α) (fun g => (b g - b₀) * tiltDens P X γ g) Real.exp
        + b₀ * pairInt P X T (fun h => (a h - a₀) * tiltDens P X α h) (tiltDens P X γ) Real.exp
        + pairInt P X T (fun h => (a h - a₀) * tiltDens P X α h)
            (fun g => (b g - b₀) * tiltDens P X γ g) Real.exp
      ≤ dstar τ M₂ σ mb c₂ / 2
        * ((a₀ ^ 2 * pairInt P X T (tiltDens P X α) (tiltDens P X γ) Real.exp
            + 2 * a₀ * pairInt P X T (fun h => (a h - a₀) * tiltDens P X α h) (tiltDens P X γ)
                Real.exp
            + pairInt P X T (fun h => (a h - a₀) ^ 2 * tiltDens P X α h) (tiltDens P X γ)
                Real.exp)
          + (b₀ ^ 2 * pairInt P X T (tiltDens P X α) (tiltDens P X γ) Real.exp
            + 2 * b₀ * pairInt P X T (tiltDens P X α) (fun g => (b g - b₀) * tiltDens P X γ g)
                Real.exp
            + pairInt P X T (tiltDens P X α) (fun g => (b g - b₀) ^ 2 * tiltDens P X γ g)
                Real.exp)) :=
    assemble (b₀ := b₀) hZ hZlow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) he hn₀ hMA hMB hSA hSB
      hNN hden' hzero'
  rw [hE2a, hE2b, hE2c, hE3, hE4]
  linarith [mul_le_mul_of_nonneg_left key hC.le]

#print axioms densFibreBound_of_densBounds

/-! ## 6. Densities near a linear tilt -/

/-- **The densities within `e^{±η}` of a linear tilt of norm at most `κ`.** -/
def nearTilt (X : Ω → E) (κ η : ℝ) : Set (Dens Ω) :=
  {θ | ∃ α : E, ‖α‖ ≤ κ ∧ ∀ g, Real.exp (-η) * Real.exp (inner ℝ α (X g)) ≤ θ.f g ∧
    θ.f g ≤ Real.exp η * Real.exp (inner ℝ α (X g))}

/-- **Moment bounds near a linear tilt**: `TiltBounds` at radius `κ` give `DensBounds` on
`nearTilt X κ η` with `M₂ e^{2η}` and `e^η (mb + e^η − 1)`. The second moment moves by the density
ratio at most `e^η` and the normaliser by at most `e^η`; the mean moves by
`∫ |⟪w, X⟫| |θ − e^{⟪α, X⟫}| ≤ ‖w‖ (e^η − 1) Z`.

DERIVED: `1` is the feature norm bound and `e⁰`; `0` is the sign of `η`, `M₂`, `mb`; `2` is the
square of `e^η` and the moment order. -/
theorem densBounds_nearTilt (hX : Continuous X) (hX1 : ∀ g, ‖X g‖ ≤ 1) {κ η M₂ mb : ℝ}
    (hη : 0 ≤ η) (hM₂ : 0 ≤ M₂) (hmb : 0 ≤ mb) (hTB : TiltBounds P X κ M₂ mb) :
    DensBounds P X (nearTilt X κ η) (Real.exp η ^ 2 * M₂) (Real.exp η * (mb + (Real.exp η - 1))) := by
  rintro θ ⟨α, hα, hθ⟩
  have hec : Continuous fun g => Real.exp (inner ℝ α (X g)) :=
    Real.continuous_exp.comp (continuous_const.inner hX)
  have he0 : 0 < Real.exp η := Real.exp_pos η
  have he1 : 1 ≤ Real.exp η := Real.one_le_exp hη
  have hprod : Real.exp η * Real.exp (-η) = 1 := by rw [← Real.exp_add]; simp
  -- the linear tilt is at most `e^η θ`
  have hle : ∀ g, Real.exp (inner ℝ α (X g)) ≤ Real.exp η * θ.f g := fun g => by
    have h1 := mul_le_mul_of_nonneg_left (hθ g).1 he0.le
    calc Real.exp (inner ℝ α (X g))
        = Real.exp η * (Real.exp (-η) * Real.exp (inner ℝ α (X g))) := by
          rw [← mul_assoc, hprod, one_mul]
      _ ≤ Real.exp η * θ.f g := h1
  have hZ : ∫ g, Real.exp (inner ℝ α (X g)) ∂P ≤ Real.exp η * ∫ g, θ.f g ∂P := by
    rw [← integral_const_mul]
    exact integral_mono (integrable_of_continuous P hec)
      (integrable_of_continuous P (continuous_const.mul θ.cont)) hle
  have hZ0 : 0 ≤ ∫ g, Real.exp (inner ℝ α (X g)) ∂P :=
    integral_nonneg fun g => (Real.exp_pos _).le
  obtain ⟨h2, hm⟩ := hTB α hα
  have hwX : ∀ (w : E) g, |inner ℝ w (X g)| ≤ ‖w‖ := fun w g =>
    (abs_real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg w, hX1 g, norm_nonneg (X g)])
  constructor
  · intro w
    have hcw : Continuous fun g => inner ℝ w (X g) ^ 2 := (continuous_const.inner hX).pow 2
    calc ∫ g, inner ℝ w (X g) ^ 2 * θ.f g ∂P
        ≤ ∫ g, Real.exp η * (inner ℝ w (X g) ^ 2 * Real.exp (inner ℝ α (X g))) ∂P :=
          integral_mono (integrable_of_continuous P (hcw.mul θ.cont))
            (integrable_of_continuous P (continuous_const.mul (hcw.mul hec))) fun g => by
              have := mul_le_mul_of_nonneg_left (hθ g).2 (sq_nonneg (inner ℝ w (X g)))
              linarith
      _ = Real.exp η * ∫ g, inner ℝ w (X g) ^ 2 * Real.exp (inner ℝ α (X g)) ∂P :=
          integral_const_mul _ _
      _ ≤ Real.exp η * (M₂ * ‖w‖ ^ 2 * ∫ g, Real.exp (inner ℝ α (X g)) ∂P) :=
          mul_le_mul_of_nonneg_left (h2 w) he0.le
      _ ≤ Real.exp η * (M₂ * ‖w‖ ^ 2 * (Real.exp η * ∫ g, θ.f g ∂P)) := by
          gcongr
      _ = Real.exp η ^ 2 * M₂ * ‖w‖ ^ 2 * ∫ g, θ.f g ∂P := by ring
  · intro w
    have hcw : Continuous fun g => inner ℝ w (X g) := continuous_const.inner hX
    have i1 : Integrable (fun g => inner ℝ w (X g) * Real.exp (inner ℝ α (X g))) P :=
      integrable_of_continuous P (hcw.mul hec)
    have i2 : Integrable (fun g => inner ℝ w (X g) * (θ.f g - Real.exp (inner ℝ α (X g)))) P :=
      integrable_of_continuous P (hcw.mul (θ.cont.sub hec))
    have hsplit : ∫ g, inner ℝ w (X g) * θ.f g ∂P
        = ∫ g, inner ℝ w (X g) * Real.exp (inner ℝ α (X g)) ∂P
          + ∫ g, inner ℝ w (X g) * (θ.f g - Real.exp (inner ℝ α (X g))) ∂P := by
      rw [← integral_add i1 i2]
      exact integral_congr_pointwise fun g => by ring
    have hdiff : ∀ g, |θ.f g - Real.exp (inner ℝ α (X g))|
        ≤ (Real.exp η - 1) * Real.exp (inner ℝ α (X g)) := fun g => by
      have hE := Real.exp_pos (inner ℝ α (X g))
      have hm1 : 1 - Real.exp (-η) ≤ Real.exp η - 1 := by
        nlinarith [sq_nonneg (Real.exp η - 1), Real.exp_pos (-η)]
      rw [abs_le]
      constructor
      · nlinarith [(hθ g).1]
      · nlinarith [(hθ g).2]
    have hR : |∫ g, inner ℝ w (X g) * (θ.f g - Real.exp (inner ℝ α (X g))) ∂P|
        ≤ ‖w‖ * (Real.exp η - 1) * ∫ g, Real.exp (inner ℝ α (X g)) ∂P := by
      have hI : ∫ g, |inner ℝ w (X g) * (θ.f g - Real.exp (inner ℝ α (X g)))| ∂P
          ≤ ∫ g, ‖w‖ * ((Real.exp η - 1) * Real.exp (inner ℝ α (X g))) ∂P :=
        integral_mono i2.abs
          (integrable_of_continuous P (continuous_const.mul (continuous_const.mul hec))) fun g => by
            rw [abs_mul]
            exact mul_le_mul (hwX w g) (hdiff g) (abs_nonneg _) (norm_nonneg _)
      have hE : ∫ g, ‖w‖ * ((Real.exp η - 1) * Real.exp (inner ℝ α (X g))) ∂P
          = ‖w‖ * (Real.exp η - 1) * ∫ g, Real.exp (inner ℝ α (X g)) ∂P := by
        rw [integral_const_mul, integral_const_mul]
        ring
      exact (abs_integral_le_integral_abs).trans (hI.trans hE.le)
    have hm' := hm w
    have hsum : |∫ g, inner ℝ w (X g) * θ.f g ∂P|
        ≤ (mb + (Real.exp η - 1)) * ‖w‖ * ∫ g, Real.exp (inner ℝ α (X g)) ∂P := by
      rw [hsplit]
      refine (abs_add_le _ _).trans ?_
      nlinarith [hm', hR]
    have hc0 : 0 ≤ (mb + (Real.exp η - 1)) * ‖w‖ := by
      have : 0 ≤ mb + (Real.exp η - 1) := by linarith
      positivity
    calc |∫ g, inner ℝ w (X g) * θ.f g ∂P|
        ≤ (mb + (Real.exp η - 1)) * ‖w‖ * ∫ g, Real.exp (inner ℝ α (X g)) ∂P := hsum
      _ ≤ (mb + (Real.exp η - 1)) * ‖w‖ * (Real.exp η * ∫ g, θ.f g ∂P) :=
          mul_le_mul_of_nonneg_left hZ hc0
      _ = Real.exp η * (mb + (Real.exp η - 1)) * ‖w‖ * ∫ g, θ.f g ∂P := by ring

#print axioms densBounds_nearTilt

/-! ## 7. Monotonicity -/

/-- **`DensBounds` is monotone in its constants.**

DERIVED: `0` is the sign of `∫ θ` and `‖w‖`; `2` is the moment order. -/
theorem densBounds_mono {A : Set (Dens Ω)} {M₂ mb M₂' mb' : ℝ} (H : DensBounds P X A M₂ mb)
    (hM : M₂ ≤ M₂') (hm : mb ≤ mb') : DensBounds P X A M₂' mb' := by
  intro θ hθ
  have hZ : 0 ≤ ∫ g, θ.f g ∂P := integral_nonneg fun g => (θ.pos g).le
  refine ⟨fun w => (H θ hθ).1 w |>.trans ?_, fun w => (H θ hθ).2 w |>.trans ?_⟩
  · have := mul_le_mul_of_nonneg_right hM (mul_nonneg (sq_nonneg ‖w‖) hZ)
    nlinarith
  · have := mul_le_mul_of_nonneg_right hm (mul_nonneg (norm_nonneg w) hZ)
    nlinarith

#print axioms densBounds_mono

/-- **`DensFibreBound` is monotone in its constant** (the right side integrates a non-negative
function).

DERIVED: no numeral. -/
theorem densFibreBound_mono {c c' τ : ℝ} {A : Set (Dens Ω)} (H : DensFibreBound P X c τ A)
    (hc : c ≤ c') : DensFibreBound P X c' τ A := by
  intro K T θ₁ θ₂ hK hT h₁ h₂ a b ha hb hz
  refine (H K T θ₁ θ₂ hK hT h₁ h₂ a b ha hb hz).trans ?_
  have hw : ∀ h g, 0 ≤ densWeight X K T θ₁ θ₂ h g := fun h g => by
    unfold densWeight
    exact mul_nonneg (mul_nonneg (mul_nonneg hK.le (Real.exp_pos _).le) (θ₁.pos h).le)
      (θ₂.pos g).le
  have hS : 0 ≤ ∫ h, a h ^ 2 * ∫ g, densWeight X K T θ₁ θ₂ h g ∂P ∂P
      + ∫ g, b g ^ 2 * ∫ h, densWeight X K T θ₁ θ₂ h g ∂P ∂P :=
    add_nonneg
      (integral_nonneg fun h => mul_nonneg (sq_nonneg _) (integral_nonneg fun g => hw h g))
      (integral_nonneg fun g => mul_nonneg (sq_nonneg _) (integral_nonneg fun h => hw h g))
  exact mul_le_mul_of_nonneg_right (by linarith) hS

#print axioms densFibreBound_mono

end MassGap.PairFibreDens
