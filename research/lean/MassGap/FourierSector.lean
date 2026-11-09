import Mathlib
import MassGap.LorentzConverse

/-!
# MassGap.FourierSector — the Fourier half of the inversion step: the momentum density

`LorentzConverse` leaves (iii), the inversion step: producing the Källén–Lehmann data from the
correlator needs Fourier inversion in `x` and Stieltjes inversion in `t`. This module builds the
Fourier half. At fixed `t > 0` the correlator `x ↦ C_u(t, x) = ⟪u, a^t U(x) u⟫` is the Fourier
transform of the tilted momentum marginal `M_t = tiltMom (nu J u) t`, the momentum push-forward of
`e^{−tE} dν(E, p)` (`MomentumSector.inner_powT_U_eq_nu`). If `C_u(t, ·)` is integrable on the
spatial slice, `M_t` has a continuous density with respect to `lam τ`, given by the inverse Fourier
transform, and the momentum marginal `m = momMarg J u` has a density with respect to `lam τ`. Declarations are in the namespace
`MassGap.FourierSector`.

DERIVED (module-wide): `0` the time component and the bottom of the rates; `1` the unit total mass
of a Gaussian and the unit step of a sequence; `2` the square, the Euclidean exponent and the
half-dimension of a Gaussian integral; `3` the spatial dimension, the four coordinates less the time;
`π`, `2π` and `(2π)^{−3}` the Fourier normalization. No number enters a clause.

## 1. Inversion for a finite measure (proved)

On a finite-dimensional real inner product space `V` with its volume, for a finite measure `μ` with
characteristic function `φ_μ(x) = ∫ e^{i⟪p, x⟫} dμ(p)`, put `ψ_μ(w) = φ_μ(2π w)` (`psiM`) and
`dens μ p = Re 𝓕ψ_μ(p)`.

* `gauss_smooth`: for `c > 0`, `∫ e^{−‖w‖²/c} e^{−2πi⟪w, p⟫} ψ_μ(w) dw = ∫ G_c(q − p) dμ(q)` with the
  Gaussian `G_c(v) = (πc)^{n/2} e^{−π² c ‖v‖²}` (`gk`, Fubini and the Gaussian Fourier transform).
* `tendsto_smooth`: if `ψ_μ` is integrable, the left side tends to `𝓕ψ_μ(p)` as `c → ∞`.
* `dens_spec`: `𝓕ψ_μ(p)` is real and `≥ 0` (a limit of the `≥ 0` reals `∫ G_c(q − p) dμ(q)`).
* `lintegral_smooth`, `lintegral_dens_le`: `∫ ∫ G_c(q − p) dμ(q) dp = μ(V)` (Tonelli, translation
  invariance, `∫ G_c = 1`), so by Fatou `∫ dens μ ≤ μ(V)`; `integrable_fourier_psiM`.
* `eq_withDensity`: `μ = dens μ · volume`. Fourier inversion (`Integrable.fourierInv_fourier_eq`) gives
  `𝓕⁻(𝓕ψ_μ) = ψ_μ`, so the characteristic functions agree (`Measure.ext_of_charFun`).
* `fourier_psiM`: `𝓕ψ_μ(p) = (2π)^{−n} ∫ e^{−i⟪x, p⟫} φ_μ(x) dx` (change of variables `x = 2π w`).

## 2. The momentum densities (proved, under integrability of the correlator)

`Sp τ` is the spatial slice as a Euclidean space (coordinates off `τ`); `emb τ : Sp τ → spatial τ`,
`embV τ`, `proj τ` the embedding and the projection; `lam_eq_map`: `lam τ` is the volume of `Sp τ`
carried to `p_τ = 0`. `corr J u t x = ⟪u, a^t U(emb x) u⟫` is `C_u(t, x)` on `Sp τ`, and
`dU J u t p = Re((2π)^{−3} ∫ e^{−i p·x} C_u(t, x) dx)` is `d_u(t, p)`.

* `tiltMom_eq_withDensity`: under `DyadicDini`, `t > 0` and `Integrable (corr J u t)`:
  `M_t = d_u(t, ·) · lam τ`, `d_u(t, ·)` continuous and `≥ 0`.
* `tiltMom_eq_momMarg`: `M_t = L_u(t, ·) · m`, `L_u(t, p) = secLaplace J u t p` (the disintegration).
* `momMarg_density`: `m ≪ lam τ`, `m = (dm/dλ) · lam τ`, and `L_u(t, p) · (dm/dλ)(p) = d_u(t, p)` for
  `lam τ`-almost every `p`. This is the density half of the first input of
  `LorentzStep.klJointRep_of_laplace`.
* On the tree, for `u` in the complex span of `DiniHolder.lipVecs`, with
  `C_u(t, x) = ⟪u, timeT t (realT x u)⟫`: `tree_corr_eq`, `tree_tiltMom_eq_withDensity`,
  `tree_momMarg_density`.

## 3. What remains (stated)

* `klJointRep_of_density`: `KLJointRep J u ρ` follows from `m ≪ lam τ`, the factorization
  `(dm/dλ)(p) = g(p) |klSec ρ p²|` (`lam τ`-a.e.) and the per-sector Laplace match
  `∫ e^{−tE} d(klSec ρ p²) = |klSec ρ p²| L_u(t, p)`. With §2 the density exists and equals
  `d_u(t, p) / L_u(t, p)` where `L_u(t, p) > 0`; what is left is the Stieltjes step: one `ρ` and one
  continuous `g`, `g(0) ≠ 0`, with `d_u(t, p) = g(p) ∫ e^{−tE} d(klSec ρ p²)(E)` for every `t > 0`,
  where `klSec ρ p²` is `ρ / (2E)` carried to the shell `E = shell s p²`, i.e. `L_u(·, p)` the shell
  Laplace transform of one `ρ` across `p`.

## What does not follow, plainly

* The integrability of `x ↦ C_u(t, x)` on the spatial slice is assumed (`hint`), not proved, on the
  tree as well as for a general `J`. The tree's clustering statements do not supply it:
  `ContinuumSchwinger.contS_cluster`, `ContinuumCluster.contS_cluster_of_fixedWindowDecay` and
  `FlowCapstone.FlowClusterAbs` are conditional (`UniformClustering`, `FixedWindowDecay`), run along
  dyadic shifts of the time direction `τ` rather than the slice `x`, and bound a connected kernel.
  Integrability on the three-dimensional slice is a rate statement, stronger than any of these.
* The hypothesis excludes some vectors (argued here, not proved in Lean). `C_u(t, x)` is the
  connected kernel plus the disconnected constant, so a vector with a vacuum component has a
  correlator that does not tend to zero, and `M_t` has an atom at `p = 0`. Then `hint` is false and
  `M_t` has no density, so §2 can apply only to vectors orthogonal to the vacuum, the setting of
  `LorentzStep.clay_zero_momentum_sectorKL`. That any non-zero vector of the Lipschitz span satisfies
  `hint` is not shown, so §2 is not shown non-vacuous on the tree.
* The Stieltjes step is not built: from `d_u(t, p)` (or `L_u(t, p)`) for all `t > 0` nothing here
  produces one `ρ` independent of `p`, nor the factorization of `dm/dλ` as `g(p) |klSec ρ p²|`.
  Stieltjes inversion is not in Mathlib at this pin. `klJointRep_of_density` takes both as hypotheses.
* The relation `L_u · dm/dλ = d_u` holds `lam τ`-almost everywhere; the density `dm/dλ` is a
  Radon–Nikodym derivative and is not shown continuous. `d_u(t, ·)` is continuous; `L_u(t, ·)` is only
  measurable, so `d_u / L_u` is not shown continuous.
* On the tree the results need `hpos`, `hcube` and hold on the span of `lipVecs`.

Foundational footprint only (`#print axioms` at the end).
-/

set_option autoImplicit false

namespace MassGap.FourierSector

open Real Filter Topology MeasureTheory Set
open scoped NNReal ENNReal FourierTransform RealInnerProductSpace
open MassGap.ShellJoint (JointData)
open MassGap.ShellTranslate (spatial phase mem_spatial)
open MassGap.ShellDensity (DyadicDini nu lam lamF)
open MassGap.ShellLorentz (klSec psq KLJointRep)
open MassGap.MomentumSector (lf momMarg sector secLaplace nuSwap map_swap_nuSwap
  momMarg_compProd_sector sector_Iio inner_powT_U_eq_nu powT_timeT_one)
open MassGap.LorentzConverse (tiltMom tiltDens measurable_tiltDens tiltDens_coe isFiniteMeasure_tilt
  nu_time nu_Iio0)
open MassGap.LorentzStep (klJointRep_of_laplace)
open MassGap.ContinuumTimeGroup (powT)

noncomputable section

/-! ## 1. Inversion for a finite measure -/

section Inversion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **The Gaussian kernel** `G_c(v) = (π c)^{n/2} e^{−π² c ‖v‖²}`, `n = dim V`: the inverse Fourier
transform of `e^{−‖w‖²/c}`. DERIVED: `2` the square and the half-dimension; `π` the Fourier
normalization. -/
def gk (c : ℝ) (v : V) : ℝ :=
  (π * c) ^ ((Module.finrank ℝ V : ℝ) / 2) * Real.exp (-(π ^ 2 * c) * ‖v‖ ^ 2)

/-- DERIVED: `2` the square and the half-dimension. -/
theorem continuous_gk (c : ℝ) : Continuous (gk (V := V) c) := by
  show Continuous fun v : V => (π * c) ^ ((Module.finrank ℝ V : ℝ) / 2)
    * Real.exp (-(π ^ 2 * c) * ‖v‖ ^ 2)
  fun_prop

/-- DERIVED: `0` the sign of the scale. -/
theorem gk_nonneg {c : ℝ} (hc : 0 ≤ c) (v : V) : 0 ≤ gk c v :=
  mul_nonneg (Real.rpow_nonneg (mul_nonneg pi_pos.le hc) _) (Real.exp_pos _).le

/-- **The Gaussian kernel is bounded by its peak.** DERIVED: `0` the sign of the scale; `2` the
square and the half-dimension. -/
theorem gk_le {c : ℝ} (hc : 0 ≤ c) (v : V) :
    gk c v ≤ (π * c) ^ ((Module.finrank ℝ V : ℝ) / 2) := by
  refine mul_le_of_le_one_right (Real.rpow_nonneg (mul_nonneg pi_pos.le hc) _) ?_
  refine Real.exp_le_one_iff.mpr ?_
  have h := mul_nonneg (mul_nonneg (sq_nonneg π) hc) (sq_nonneg ‖v‖)
  nlinarith

/-- **The Gaussian kernel has unit mass.** DERIVED: `1` the unit mass; `2` the square and the
half-dimension. -/
theorem integral_gk {c : ℝ} (hc : 0 < c) : ∫ v : V, gk c v = 1 := by
  have hb : 0 < π ^ 2 * c := mul_pos (pow_pos pi_pos 2) hc
  simp only [gk]
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm hb,
    ← Real.mul_rpow (mul_pos pi_pos hc).le (div_pos pi_pos hb).le]
  have e : π * c * (π / (π ^ 2 * c)) = 1 := by
    rw [mul_div_assoc', div_eq_one_iff_eq hb.ne']
    ring
  rw [e, Real.one_rpow]

/-- DERIVED: `1` the unit mass. -/
theorem integrable_gk {c : ℝ} (hc : 0 < c) : Integrable (gk (V := V) c) :=
  Integrable.of_integral_ne_zero (by rw [integral_gk hc]; exact one_ne_zero)

/-- **The Gaussian Fourier transform**: `∫ e^{−‖w‖²/c + 2πi⟪v, w⟫} dw = G_c(v)`. DERIVED: `2`, `4`
the square of `2πi`; `π` the Fourier normalization. -/
theorem integral_gauss_phase {c : ℝ} (hc : 0 < c) (v : V) :
    ∫ w : V, Complex.exp (-((c⁻¹ : ℝ) : ℂ) * ‖w‖ ^ 2 + (2 * π * Complex.I) * ⟪v, w⟫)
      = (gk c v : ℂ) := by
  have hb : 0 < (((c⁻¹ : ℝ) : ℂ)).re := by rw [Complex.ofReal_re]; exact inv_pos.mpr hc
  rw [show (gk c v : ℂ) = ((π * c : ℝ) : ℂ) ^ ((((Module.finrank ℝ V : ℝ) / 2 : ℝ)) : ℂ)
      * Complex.exp (((-(π ^ 2 * c) * ‖v‖ ^ 2 : ℝ)) : ℂ) by
    rw [gk, Complex.ofReal_mul, Complex.ofReal_cpow (mul_pos pi_pos hc).le, Complex.ofReal_exp]]
  refine (GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb (2 * π * Complex.I) v).trans ?_
  have h1 : (π : ℂ) / ((c⁻¹ : ℝ) : ℂ) = ((π * c : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv, div_inv_eq_mul, Complex.ofReal_mul]
  have h2 : ((Module.finrank ℝ V : ℂ) / 2) = ((((Module.finrank ℝ V : ℝ) / 2 : ℝ)) : ℂ) := by
    push_cast <;> ring
  have h3 : (2 * π * Complex.I) ^ 2 * (‖v‖ : ℂ) ^ 2 / (4 * ((c⁻¹ : ℝ) : ℂ))
      = (((-(π ^ 2 * c) * ‖v‖ ^ 2 : ℝ)) : ℂ) := by
    have h4 : ((4 : ℂ) * (c : ℂ)⁻¹)⁻¹ = (c : ℂ) * 4⁻¹ := by
      rw [mul_inv, inv_inv]
      exact mul_comm _ _
    rw [mul_pow, Complex.I_sq, Complex.ofReal_inv, div_eq_mul_inv, h4]
    push_cast
    ring
  rw [h1, h2, h3]

/-- **`ψ_μ(w) = φ_μ(2π w)`**, `φ_μ` the characteristic function: the inverse Fourier transform of `μ`
in Mathlib's normalization. DERIVED: `2π` the Fourier normalization. -/
def psiM (μ : Measure V) (w : V) : ℂ := charFun μ ((2 * π) • w)

/-- DERIVED: `2π` the Fourier normalization. -/
theorem continuous_psiM (μ : Measure V) [IsFiniteMeasure μ] : Continuous (psiM μ) :=
  continuous_charFun.comp (continuous_const_smul _)

/-- DERIVED: `2π` the Fourier normalization. -/
theorem integrable_phase_psiM (μ : Measure V) [IsFiniteMeasure μ] (hψ : Integrable (psiM μ))
    (p : V) :
    Integrable (fun w : V => Complex.exp (((-2 * π * ⟪w, p⟫ : ℝ) : ℂ) * Complex.I) • psiM μ w) := by
  have hc : Continuous fun w : V => Complex.exp (((-2 * π * ⟪w, p⟫ : ℝ) : ℂ) * Complex.I) := by
    fun_prop
  refine hψ.mono (hc.smul (continuous_psiM μ)).aestronglyMeasurable (Eventually.of_forall fun w => ?_)
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- **The Fubini integrand** `e^{−‖w‖²/c} e^{2πi⟪q − p, w⟫}`. DERIVED: `2π` the Fourier
normalization; `2` the square. -/
def gF (c : ℝ) (p w q : V) : ℂ :=
  ((Real.exp (-c⁻¹ * ‖w‖ ^ 2) : ℝ) : ℂ) * Complex.exp (((2 * π * ⟪q - p, w⟫ : ℝ) : ℂ) * Complex.I)

/-- DERIVED: `2` the square. -/
theorem continuous_gF (c : ℝ) (p : V) : Continuous fun z : V × V => gF c p z.1 z.2 := by
  simp only [gF]
  fun_prop

/-- **Gaussian smoothing is a Gaussian average of `μ`**: for `c > 0`,
`∫ e^{−‖w‖²/c} e^{−2πi⟪w, p⟫} ψ_μ(w) dw = ∫ G_c(q − p) dμ(q)`. DERIVED: `0` the sign of the scale;
`2π` the Fourier normalization; `2` the square. -/
theorem gauss_smooth (μ : Measure V) [IsFiniteMeasure μ] {c : ℝ} (hc : 0 < c) (p : V) :
    ∫ w : V, Complex.exp (-c⁻¹ * ‖w‖ ^ 2) •
        (Complex.exp (((-2 * π * ⟪w, p⟫ : ℝ) : ℂ) * Complex.I) • psiM μ w)
      = ((∫ q, gk c (q - p) ∂μ : ℝ) : ℂ) := by
  have hpt : ∀ w : V, Complex.exp (-c⁻¹ * ‖w‖ ^ 2) •
      (Complex.exp (((-2 * π * ⟪w, p⟫ : ℝ) : ℂ) * Complex.I) • psiM μ w) = ∫ q, gF c p w q ∂μ := by
    intro w
    rw [psiM, charFun_apply, smul_eq_mul, smul_eq_mul, ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [gF]
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have e1 : ⟪q, (2 * π) • w⟫ = 2 * π * ⟪q, w⟫ := real_inner_smul_right _ _ _
    have e2 : ⟪q - p, w⟫ = ⟪q, w⟫ - ⟪p, w⟫ := inner_sub_left _ _ _
    have e3 : ⟪w, p⟫ = ⟪p, w⟫ := real_inner_comm _ _
    rw [e1, e2, e3]
    push_cast
    ring
  have hG : Integrable (fun w : V => Real.exp (-c⁻¹ * ‖w‖ ^ 2)) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (inv_pos.mpr hc)]
    exact (Real.rpow_pos_of_pos (div_pos pi_pos (inv_pos.mpr hc)) _).ne'
  have hgF : ∀ w q : V, ‖gF c p w q‖ = Real.exp (-c⁻¹ * ‖w‖ ^ 2) := fun w q => by
    rw [gF, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
  have hint : Integrable (Function.uncurry (gF c p)) ((volume : Measure V).prod μ) :=
    Integrable.mono' (hG.comp_fst μ) (continuous_gF c p).aestronglyMeasurable
      (Eventually.of_forall fun z => (hgF z.1 z.2).le)
  have hinner : ∀ q : V, ∫ w, gF c p w q = (gk c (q - p) : ℂ) := fun q => by
    rw [← integral_gauss_phase hc (q - p)]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [gF]
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc _ = ∫ w, ∫ q, gF c p w q ∂μ := integral_congr_ae (Eventually.of_forall hpt)
    _ = ∫ q, ∫ w, gF c p w q ∂volume ∂μ := integral_integral_swap hint
    _ = ∫ q, (gk c (q - p) : ℂ) ∂μ := integral_congr_ae (Eventually.of_forall hinner)
    _ = _ := integral_complex_ofReal

/-- **The smoothing tends to the Fourier transform**: `∫ G_c(q − p) dμ(q) → 𝓕ψ_μ(p)` as `c → ∞`.
DERIVED: `0` the sign of the scale; `2π` the Fourier normalization. -/
theorem tendsto_smooth (μ : Measure V) [IsFiniteMeasure μ] (hψ : Integrable (psiM μ)) (p : V) :
    Tendsto (fun c : ℝ => ((∫ q, gk c (q - p) ∂μ : ℝ) : ℂ)) atTop (𝓝 (𝓕 (psiM μ) p)) := by
  have h : Tendsto (fun c : ℝ => ∫ w : V, Complex.exp (-c⁻¹ * ‖w‖ ^ 2) •
      (Complex.exp (((-2 * π * ⟪w, p⟫ : ℝ) : ℂ) * Complex.I) • psiM μ w)) atTop
      (𝓝 (𝓕 (psiM μ) p)) := by
    rw [Real.fourier_eq']
    exact Real.tendsto_integral_cexp_sq_smul (integrable_phase_psiM μ hψ p)
  refine h.congr' ?_
  filter_upwards [Ioi_mem_atTop 0] with c hc
  exact gauss_smooth μ hc p

/-- **The density** `Re 𝓕ψ_μ`. DERIVED: no numeral. -/
def dens (μ : Measure V) (p : V) : ℝ := (𝓕 (psiM μ) p).re

/-- **The Fourier transform of `ψ_μ` is real and `≥ 0`.** DERIVED: `0` the sign. -/
theorem dens_spec (μ : Measure V) [IsFiniteMeasure μ] (hψ : Integrable (psiM μ)) (p : V) :
    𝓕 (psiM μ) p = (dens μ p : ℂ) ∧ 0 ≤ dens μ p := by
  have h := tendsto_smooth μ hψ p
  have him := (Complex.continuous_im.tendsto _).comp h
  have hre := (Complex.continuous_re.tendsto _).comp h
  simp only [Function.comp_def, Complex.ofReal_im, Complex.ofReal_re] at him hre
  have h0 : (𝓕 (psiM μ) p).im = 0 := tendsto_nhds_unique him tendsto_const_nhds
  refine ⟨Complex.ext (by simp [dens]) (by simp [h0]), ?_⟩
  exact ge_of_tendsto hre ((eventually_ge_atTop 0).mono fun c hc =>
    integral_nonneg fun q => gk_nonneg hc _)

/-- DERIVED: `0` the sign of the scale. -/
theorem continuous_smooth (μ : Measure V) [IsFiniteMeasure μ] {c : ℝ} (hc : 0 ≤ c) :
    Continuous fun p : V => ∫ q, gk c (q - p) ∂μ :=
  continuous_of_dominated (bound := fun _ => (π * c) ^ ((Module.finrank ℝ V : ℝ) / 2))
    (fun p => ((continuous_gk c).comp (continuous_sub_right p)).aestronglyMeasurable)
    (fun _ => Eventually.of_forall fun _ =>
      (Real.norm_of_nonneg (gk_nonneg hc _)).le.trans (gk_le hc _))
    (integrable_const _)
    (Eventually.of_forall fun q => (continuous_gk c).comp (continuous_sub_left q))

/-- **Each smoothing has the mass of `μ`**: `∫ ∫ G_c(q − p) dμ(q) dp = μ(V)`. DERIVED: `0` the sign
of the scale; `1` the unit mass. -/
theorem lintegral_smooth (μ : Measure V) [IsFiniteMeasure μ] {c : ℝ} (hc : 0 < c) :
    ∫⁻ p, ENNReal.ofReal (∫ q, gk c (q - p) ∂μ) = μ univ := by
  have e1 : ∀ p : V, ENNReal.ofReal (∫ q, gk c (q - p) ∂μ)
      = ∫⁻ q, ENNReal.ofReal (gk c (q - p)) ∂μ := fun p =>
    ofReal_integral_eq_lintegral_ofReal
      (Integrable.of_bound ((continuous_gk c).comp (continuous_sub_right p)).aestronglyMeasurable _
        (Eventually.of_forall fun q =>
          (Real.norm_of_nonneg (gk_nonneg hc.le _)).le.trans (gk_le hc.le _)))
      (Eventually.of_forall fun q => gk_nonneg hc.le _)
  have hcz : Continuous fun z : V × V => gk c (z.2 - z.1) :=
    (continuous_gk c).comp (continuous_snd.sub continuous_fst)
  have hmz : Measurable fun z : V × V => ENNReal.ofReal (gk c (z.2 - z.1)) :=
    ENNReal.measurable_ofReal.comp hcz.measurable
  rw [lintegral_congr e1, lintegral_lintegral_swap
    (f := fun p q : V => ENNReal.ofReal (gk c (q - p))) hmz.aemeasurable]
  have e2 : ∀ q : V, ∫⁻ p, ENNReal.ofReal (gk c (q - p)) = 1 := fun q => by
    have hs : ∀ p : V, gk c (q - p) = gk c (-q + p) := fun p => by
      simp only [gk]
      rw [neg_add_eq_sub, norm_sub_rev]
    simp_rw [hs]
    rw [lintegral_add_left_eq_self (fun v => ENNReal.ofReal (gk c v)) (-q),
      ← ofReal_integral_eq_lintegral_ofReal (integrable_gk hc)
        (Eventually.of_forall (gk_nonneg hc.le)), integral_gk hc, ENNReal.ofReal_one]
  rw [lintegral_congr e2, lintegral_one]

/-- **Fatou**: `∫ dens μ ≤ μ(V)`. DERIVED: `1` the unit step of the sequence of scales. -/
theorem lintegral_dens_le (μ : Measure V) [IsFiniteMeasure μ] (hψ : Integrable (psiM μ)) :
    ∫⁻ p, ENNReal.ofReal (dens μ p) ≤ μ univ := by
  have hlim : ∀ p : V, Tendsto (fun n : ℕ => ENNReal.ofReal (∫ q, gk ((n : ℝ) + 1) (q - p) ∂μ))
      atTop (𝓝 (ENNReal.ofReal (dens μ p))) := by
    intro p
    have h := ((Complex.continuous_re.tendsto _).comp (tendsto_smooth μ hψ p)).comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    exact ENNReal.tendsto_ofReal h
  have e : (fun n : ℕ => ∫⁻ p, ENNReal.ofReal (∫ q, gk ((n : ℝ) + 1) (q - p) ∂μ))
      = fun _ => μ univ := funext fun n => lintegral_smooth μ (Nat.cast_add_one_pos n)
  calc ∫⁻ p, ENNReal.ofReal (dens μ p)
      = ∫⁻ p, liminf (fun n : ℕ => ENNReal.ofReal (∫ q, gk ((n : ℝ) + 1) (q - p) ∂μ)) atTop :=
        lintegral_congr fun p => ((hlim p).liminf_eq).symm
    _ ≤ liminf (fun n : ℕ => ∫⁻ p, ENNReal.ofReal (∫ q, gk ((n : ℝ) + 1) (q - p) ∂μ)) atTop :=
        lintegral_liminf_le fun n =>
          (ENNReal.measurable_ofReal.comp (continuous_smooth μ (by positivity)).measurable)
    _ = μ univ := by rw [e, liminf_const]

/-- DERIVED: no numeral. -/
theorem continuous_fourier_psiM (μ : Measure V) (hψ : Integrable (psiM μ)) :
    Continuous (𝓕 (psiM μ)) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hψ

/-- **The Fourier transform of `ψ_μ` is integrable.** DERIVED: `0` the sign. -/
theorem integrable_fourier_psiM (μ : Measure V) [IsFiniteMeasure μ] (hψ : Integrable (psiM μ)) :
    Integrable (𝓕 (psiM μ)) := by
  have hd : Continuous (dens μ) := Complex.continuous_re.comp (continuous_fourier_psiM μ hψ)
  have hi : Integrable (dens μ) :=
    (lintegral_ofReal_ne_top_iff_integrable hd.aestronglyMeasurable
      (Eventually.of_forall fun p => (dens_spec μ hψ p).2)).mp
      (ne_top_of_le_ne_top (measure_ne_top μ univ) (lintegral_dens_le μ hψ))
  have e : 𝓕 (psiM μ) = fun p => (dens μ p : ℂ) := funext fun p => (dens_spec μ hψ p).1
  rw [e]
  exact hi.ofReal

/-- **A finite measure with integrable characteristic function has the density `dens μ`**:
`μ = dens μ · volume`. DERIVED: `2π` the Fourier normalization. -/
theorem eq_withDensity (μ : Measure V) [IsFiniteMeasure μ] (hψ : Integrable (psiM μ)) :
    μ = (volume : Measure V).withDensity (fun p => ENNReal.ofReal (dens μ p)) := by
  have hd : Continuous (dens μ) := Complex.continuous_re.comp (continuous_fourier_psiM μ hψ)
  have hfin : ∫⁻ p, ENNReal.ofReal (dens μ p) ≠ ∞ :=
    ne_top_of_le_ne_top (measure_ne_top μ univ) (lintegral_dens_le μ hψ)
  show μ = (volume : Measure V).withDensity (fun p => ((dens μ p).toNNReal : ℝ≥0∞))
  haveI : IsFiniteMeasure ((volume : Measure V).withDensity
      (fun p => ((dens μ p).toNNReal : ℝ≥0∞))) := isFiniteMeasure_withDensity hfin
  refine Measure.ext_of_charFun (funext fun x => ?_)
  have hinv := hψ.fourierInv_fourier_eq (integrable_fourier_psiM μ hψ)
    (v := (2 * π)⁻¹ • x) (continuous_psiM μ).continuousAt
  have hv : psiM μ ((2 * π)⁻¹ • x) = charFun μ x := by
    rw [psiM, smul_smul, mul_inv_cancel₀ two_pi_pos.ne', one_smul]
  have hpt : ∀ v : V, Complex.exp (((2 * π * ⟪v, (2 * π)⁻¹ • x⟫ : ℝ) : ℂ) * Complex.I)
      • 𝓕 (psiM μ) v = (dens μ v).toNNReal • Complex.exp (((⟪v, x⟫ : ℝ) : ℂ) * Complex.I) := by
    intro v
    have hs := dens_spec μ hψ v
    rw [hs.1, real_inner_smul_right, mul_inv_cancel_left₀ two_pi_pos.ne', NNReal.smul_def,
      Real.coe_toNNReal _ hs.2, Complex.real_smul, smul_eq_mul]
    exact mul_comm _ _
  rw [← hv, ← hinv, Real.fourierInv_eq', charFun_apply,
    integral_withDensity_eq_integral_smul hd.measurable.real_toNNReal]
  exact integral_congr_ae (Eventually.of_forall hpt)

/-- **The density in closed form**: `𝓕ψ_μ(p) = (2π)^{−n} ∫ e^{−i⟪x, p⟫} φ_μ(x) dx`.
DERIVED: `2π` and `(2π)^{−n}` the Fourier normalization. -/
theorem fourier_psiM (μ : Measure V) (p : V) :
    𝓕 (psiM μ) p = (((2 * π) ^ Module.finrank ℝ V)⁻¹ : ℝ) •
      ∫ x : V, Complex.exp (-((⟪x, p⟫ : ℝ) : ℂ) * Complex.I) * charFun μ x := by
  have h := Measure.integral_comp_smul (volume : Measure V)
    (fun x : V => Complex.exp (-((⟪x, p⟫ : ℝ) : ℂ) * Complex.I) * charFun μ x) (2 * π)
  rw [abs_of_pos (inv_pos.mpr (pow_pos two_pi_pos _))] at h
  rw [← h, Real.fourier_eq']
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [psiM, smul_eq_mul, real_inner_smul_left]
  congr 2
  push_cast
  ring

end Inversion

/-! ## 2. The spatial slice -/

section Slice

variable {τ : Fin 4}

/-- **The spatial slice as a Euclidean space**: coordinates off the time slot `τ`. DERIVED: no
numeral (`EuclideanSpace` is the `L²` product). -/
abbrev Sp (τ : Fin 4) : Type := EuclideanSpace ℝ {j : Fin 4 // j ≠ τ}

/-- **The slice inside `Fin 4 → ℝ`**, zero in the time slot. DERIVED: `0` the time component. -/
def embV (τ : Fin 4) (x : Sp τ) : Fin 4 → ℝ := fun j => if h : j = τ then 0 else x ⟨j, h⟩

/-- **The slice as spatial vectors.** DERIVED: `0` the time component. -/
def emb (τ : Fin 4) (x : Sp τ) : spatial τ := ⟨embV τ x, mem_spatial (by simp [embV])⟩

/-- **The projection to the slice**: drop the time slot. DERIVED: no numeral. -/
def proj (τ : Fin 4) (p : Fin 4 → ℝ) : Sp τ :=
  WithLp.toLp 2 (fun j : {j : Fin 4 // j ≠ τ} => p j)

/-- DERIVED: `0` the time component. -/
theorem continuous_embV (τ : Fin 4) : Continuous (embV τ) := by
  refine continuous_pi fun j => ?_
  by_cases hj : j = τ
  · simp only [embV, dif_pos hj]
    exact continuous_const
  · simp only [embV, dif_neg hj]
    fun_prop

/-- DERIVED: no numeral. -/
theorem continuous_proj (τ : Fin 4) : Continuous (proj τ) := by
  show Continuous fun p : Fin 4 → ℝ => WithLp.toLp 2 (fun j : {j : Fin 4 // j ≠ τ} => p j)
  fun_prop

/-- DERIVED: no numeral. -/
theorem proj_embV (x : Sp τ) : proj τ (embV τ x) = x :=
  PiLp.ext fun i => dif_neg i.2

/-- DERIVED: `0` the time component. -/
theorem embV_proj {p : Fin 4 → ℝ} (hp : p τ = 0) : embV τ (proj τ p) = p := by
  funext j
  by_cases hj : j = τ
  · rw [hj, hp]
    exact dif_pos rfl
  · exact dif_neg hj

/-- **The phase on the slice is the Euclidean inner product**: `p · emb x = ⟪proj p, x⟫`. DERIVED:
`0` the time component. -/
theorem phase_emb (p : Fin 4 → ℝ) (x : Sp τ) : phase p (emb τ x) = ⟪proj τ p, x⟫ := by
  unfold phase
  refine (Fintype.sum_eq_add_sum_subtype_ne _ τ).trans ?_
  have h0 : ((emb τ x : spatial τ) : Fin 4 → ℝ) τ = 0 := dif_pos rfl
  rw [h0, mul_zero, zero_add, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : ((emb τ x : spatial τ) : Fin 4 → ℝ) i.1 = x i := dif_neg i.2
  rw [hi]
  show p i.1 * x i = inner ℝ (p i.1) (x i)
  rw [RCLike.inner_apply, conj_trivial]
  exact mul_comm _ _

/-- **The slice has dimension `3`.** DERIVED: `3` the spatial dimension. -/
theorem finrank_Sp (τ : Fin 4) : Module.finrank ℝ (Sp τ) = 3 := by
  rw [finrank_euclideanSpace]
  fin_cases τ <;> rfl

/-- **`lam τ` is the volume of the slice, carried to `p_τ = 0`.** DERIVED: `0` the time component;
`1` the unit mass of `δ₀`. -/
theorem lam_eq_map (τ : Fin 4) : lam τ = (volume : Measure (Sp τ)).map (embV τ) := by
  show Measure.pi (lamF τ) = _
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (continuous_embV τ).measurable (MeasurableSet.univ_pi hs),
    Fintype.prod_eq_mul_prod_subtype_ne _ τ]
  have hR : ∀ i : {j : Fin 4 // j ≠ τ}, lamF τ i.1 (s i.1) = volume (s i.1) := fun i => by
    rw [lamF, if_neg i.2]
  simp only [hR]
  rw [lamF, if_pos (rfl : τ = τ)]
  by_cases h0 : (0 : ℝ) ∈ s τ
  · have e : embV τ ⁻¹' Set.univ.pi s
        = WithLp.ofLp ⁻¹' Set.univ.pi (fun i : {j : Fin 4 // j ≠ τ} => s i.1) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      constructor
      · intro hx i
        simpa [embV, i.2] using hx i.1
      · intro hx j
        by_cases hj : j = τ
        · simpa [embV, hj] using h0
        · simpa [embV, hj] using hx ⟨j, hj⟩
    rw [e, Measure.dirac_apply_of_mem h0, one_mul,
      (PiLp.volume_preserving_ofLp {j : Fin 4 // j ≠ τ}).measure_preimage
        (MeasurableSet.univ_pi fun i => hs i.1).nullMeasurableSet, volume_pi_pi]
  · have e : embV τ ⁻¹' Set.univ.pi s = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_empty_iff_false, iff_false,
        not_forall]
      exact ⟨τ, by simpa [embV] using h0⟩
    rw [e, measure_empty, Measure.dirac_apply' _ (hs τ), Set.indicator_of_notMem h0, zero_mul]

/-- **A density on the slice, carried to `Fin 4 → ℝ`, is a density against `lam τ`.** DERIVED: no
numeral. -/
theorem map_withDensity_embV (τ : Fin 4) {f : Sp τ → ℝ≥0∞} (hf : Measurable f) :
    ((volume : Measure (Sp τ)).withDensity f).map (embV τ)
      = (lam τ).withDensity (fun p => f (proj τ p)) := by
  have hm := (continuous_embV τ).measurable
  ext A hA
  rw [Measure.map_apply hm hA, withDensity_apply _ hA, withDensity_apply _ (hm hA), lam_eq_map,
    setLIntegral_map (f := fun p => f (proj τ p)) hA (hf.comp (continuous_proj τ).measurable) hm]
  simp only [proj_embV]

/-- **The tilted marginal lives on `p_τ = 0`.** DERIVED: `0` the time component. -/
theorem tiltMom_time {ν : Measure (ℝ × (Fin 4 → ℝ))} (hτ : ∀ᵐ q ∂ν, q.2 τ = 0) (t : ℝ) :
    ∀ᵐ p ∂(tiltMom ν t), p τ = 0 := by
  rw [tiltMom, ae_map_iff measurable_snd.aemeasurable
    (measurableSet_eq_fun (measurable_pi_apply τ) measurable_const)]
  exact (withDensity_absolutelyContinuous _ _).ae_le hτ

/-- **A measure on `p_τ = 0` is the image of its slice projection.** DERIVED: `0` the time
component. -/
theorem map_proj_embV {M : Measure (Fin 4 → ℝ)} (hM : ∀ᵐ p ∂M, p τ = 0) :
    (M.map (proj τ)).map (embV τ) = M := by
  rw [Measure.map_map (continuous_embV τ).measurable (continuous_proj τ).measurable,
    Measure.map_congr (f := embV τ ∘ proj τ) (g := id) (hM.mono fun p hp => embV_proj hp),
    Measure.map_id]

/-- **The characteristic function of the projected tilted marginal is the transform of `ν`**:
`φ(x) = ∫ e^{−tE} e^{i p·emb x} dν`. DERIVED: no numeral. -/
theorem charFun_tilt (ν : Measure (ℝ × (Fin 4 → ℝ))) (t : ℝ) (x : Sp τ) :
    charFun ((tiltMom ν t).map (proj τ)) x = ∫ q, lf t (emb τ x) q ∂ν := by
  have hc : Continuous fun y : Sp τ => Complex.exp (((⟪y, x⟫ : ℝ) : ℂ) * Complex.I) := by
    fun_prop
  rw [charFun_apply, tiltMom, Measure.map_map (continuous_proj τ).measurable measurable_snd,
    integral_map ((continuous_proj τ).measurable.comp measurable_snd).aemeasurable
      hc.aestronglyMeasurable,
    integral_withDensity_eq_integral_smul (measurable_tiltDens t)]
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  show tiltDens t q • Complex.exp (((⟪proj τ q.2, x⟫ : ℝ) : ℂ) * Complex.I) = lf t (emb τ x) q
  rw [lf, phase_emb, NNReal.smul_def, Complex.real_smul]
  rfl

end Slice

/-! ## 3. The momentum densities -/

section Vector

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {τ : Fin 4} (J : JointData H (spatial τ))

/-- **The correlator on the slice** `C_u(t, x) = ⟪u, a^t U(emb x) u⟫`. DERIVED: no numeral. -/
def corr (u : H) (t : ℝ) (x : Sp τ) : ℂ := inner ℂ u (powT J.a t (J.R.U (emb τ x) u))

/-- **The tilted density** `d_u(t, p) = Re((2π)^{−3} ∫ e^{−i p·x} C_u(t, x) dx)`. DERIVED: `(2π)^{−3}`
the Fourier normalization, `3` the spatial dimension. -/
def dU (u : H) (t : ℝ) (p : Fin 4 → ℝ) : ℝ :=
  ((((2 * π) ^ 3)⁻¹ : ℝ) • ∫ x : Sp τ,
    Complex.exp (-((phase p (emb τ x) : ℝ) : ℂ) * Complex.I) * corr J u t x).re

/-- **The tilted marginal on the slice.** DERIVED: no numeral. -/
def tiltV (u : H) (t : ℝ) : Measure (Sp τ) := (tiltMom (nu J u) t).map (proj τ)

/-- DERIVED: `0` the sign of the time. -/
theorem isFiniteMeasure_tiltMom (u : H) {t : ℝ} (ht : 0 ≤ t) :
    IsFiniteMeasure (tiltMom (nu J u) t) := by
  haveI := isFiniteMeasure_tilt (nu J u) (nu_Iio0 J u) ht
  unfold tiltMom
  infer_instance

/-- **The characteristic function of the slice marginal is the correlator.** DERIVED: `0` the sign
of the time. -/
theorem charFun_tiltV {u : H} (hD : DyadicDini J u) {t : ℝ} (ht : 0 < t) :
    charFun (tiltV J u t) = corr J u t :=
  funext fun x => (charFun_tilt (nu J u) t x).trans (inner_powT_U_eq_nu J hD ht (emb τ x)).symm

/-- DERIVED: no numeral. -/
theorem tiltV_map (u : H) (t : ℝ) : (tiltV J u t).map (embV τ) = tiltMom (nu J u) t :=
  map_proj_embV (tiltMom_time (nu_time J u) t)

/-- **The tilted marginal has a continuous density** (`(1)`, `(2)`): under `DyadicDini`, `t > 0`
and integrability of `x ↦ C_u(t, x)` on the slice, `M_t = d_u(t, ·) · lam τ` with `d_u(t, ·)`
continuous and `≥ 0`. DERIVED: `0` the sign of the time and of the density. -/
theorem tiltMom_eq_withDensity {u : H} (hD : DyadicDini J u) {t : ℝ} (ht : 0 < t)
    (hint : Integrable (corr J u t)) :
    tiltMom (nu J u) t = (lam τ).withDensity (fun p => ENNReal.ofReal (dU J u t p)) ∧
      Continuous (dU J u t) ∧ ∀ p, 0 ≤ dU J u t p := by
  haveI := isFiniteMeasure_tiltMom J u ht.le
  haveI : IsFiniteMeasure (tiltV J u t) := by unfold tiltV; infer_instance
  have hψ : Integrable (psiM (tiltV J u t)) := by
    rw [← charFun_tiltV J hD ht] at hint
    exact hint.comp_smul two_pi_pos.ne'
  have hdens : ∀ p, dens (tiltV J u t) (proj τ p) = dU J u t p := fun p => by
    have e : ∀ x : Sp τ, ⟪x, proj τ p⟫ = phase p (emb τ x) := fun x => by
      rw [real_inner_comm, phase_emb]
    rw [dens, fourier_psiM, finrank_Sp, charFun_tiltV J hD ht, dU]
    simp_rw [e]
  have hd : Continuous (dens (tiltV J u t)) :=
    Complex.continuous_re.comp (continuous_fourier_psiM _ hψ)
  refine ⟨?_, (hd.comp (continuous_proj τ)).congr hdens, fun p => ?_⟩
  · have h1 := map_withDensity_embV τ (f := fun y => ENNReal.ofReal (dens (tiltV J u t) y))
      (ENNReal.measurable_ofReal.comp hd.measurable)
    rw [← eq_withDensity _ hψ, tiltV_map] at h1
    rw [h1]
    simp_rw [hdens]
  · rw [← hdens p]
    exact (dens_spec _ hψ (proj τ p)).2

/-- **The sector Laplace integrand is integrable** for almost every momentum. DERIVED: `0` the
bottom of the rates and the sign of the time; `1` the bound. -/
theorem integrable_sector_exp (u : H) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ p ∂(momMarg J u), Integrable (fun s => Real.exp (-(t * s))) (sector J u p) := by
  filter_upwards [sector_Iio J u] with p hp
  have hnn : ∀ᵐ s ∂(sector J u p), 0 ≤ s := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hp] with s hs
    exact not_lt.mp hs
  refine Integrable.of_bound
    (by fun_prop : Continuous fun s : ℝ => Real.exp (-(t * s))).aestronglyMeasurable 1 ?_
  filter_upwards [hnn] with s hs
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht hs))

/-- DERIVED: no numeral. -/
theorem measurable_secLaplace (u : H) (t : ℝ) : Measurable (secLaplace J u t) :=
  ((by fun_prop : Continuous fun s : ℝ => Real.exp (-(t * s))).stronglyMeasurable.integral_kernel
    (κ := sector J u)).measurable

/-- **The tilted marginal is `L_u(t, ·)` times the momentum marginal**: `M_t = L_u(t, ·) · m`.
DERIVED: `0` the sign of the time. -/
theorem tiltMom_eq_momMarg (u : H) {t : ℝ} (ht : 0 ≤ t) :
    tiltMom (nu J u) t
      = (momMarg J u).withDensity (fun p => ENNReal.ofReal (secLaplace J u t p)) := by
  have key : ∀ᵐ p ∂(momMarg J u), ∫⁻ s, ENNReal.ofReal (Real.exp (-(t * s))) ∂(sector J u p)
      = ENNReal.ofReal (secLaplace J u t p) := by
    filter_upwards [integrable_sector_exp J u ht] with p hp
    rw [secLaplace, ofReal_integral_eq_lintegral_ofReal hp
      (Eventually.of_forall fun s => (Real.exp_pos _).le)]
  ext A hA
  have hS : MeasurableSet (Prod.snd ⁻¹' A : Set (ℝ × (Fin 4 → ℝ))) := measurable_snd hA
  have hmt : Measurable fun q : ℝ × (Fin 4 → ℝ) => (tiltDens t q : ℝ≥0∞) :=
    (measurable_tiltDens t).coe_nnreal_ennreal
  rw [tiltMom, Measure.map_apply measurable_snd hA, withDensity_apply _ hS, withDensity_apply _ hA,
    ← map_swap_nuSwap J u, setLIntegral_map hS hmt measurable_swap]
  have e : (Prod.swap ⁻¹' (Prod.snd ⁻¹' A) : Set ((Fin 4 → ℝ) × ℝ)) = A ×ˢ univ := by
    ext z
    simp
  rw [e, ← momMarg_compProd_sector J u,
    Measure.setLIntegral_compProd (f := fun z => (tiltDens t z.swap : ℝ≥0∞))
      ((measurable_tiltDens t).comp measurable_swap).coe_nnreal_ennreal hA MeasurableSet.univ]
  refine lintegral_congr_ae ((ae_restrict_of_ae key).mono fun p hp => ?_)
  simp only [Measure.restrict_univ]
  rw [← hp]
  refine lintegral_congr fun s => ?_
  simp only [Prod.swap_prod_mk, tiltDens_coe]

/-- **The momentum marginal has a density, and `L_u · dm/dλ = d_u`**: under `DyadicDini`, `t > 0` and
integrability of the correlator, `m ≪ lam τ`, `m = (dm/dλ) · lam τ`, and
`L_u(t, p) (dm/dλ)(p) = d_u(t, p)` for `lam τ`-almost every `p`. DERIVED: `0` the sign of the time. -/
theorem momMarg_density {u : H} (hD : DyadicDini J u) {t : ℝ} (ht : 0 < t)
    (hint : Integrable (corr J u t)) :
    momMarg J u ≪ lam τ ∧
      momMarg J u = (lam τ).withDensity ((momMarg J u).rnDeriv (lam τ)) ∧
      ∀ᵐ p ∂(lam τ), ENNReal.ofReal (secLaplace J u t p) * (momMarg J u).rnDeriv (lam τ) p
        = ENNReal.ofReal (dU J u t p) := by
  obtain ⟨hT, hcont, -⟩ := tiltMom_eq_withDensity J hD ht hint
  have hTm := tiltMom_eq_momMarg J u ht.le
  have hL : Measurable fun p => ENNReal.ofReal (secLaplace J u t p) :=
    ENNReal.measurable_ofReal.comp (measurable_secLaplace J u t)
  have hpos : ∀ᵐ p ∂(momMarg J u), ENNReal.ofReal (secLaplace J u t p) ≠ 0 := by
    filter_upwards [integrable_sector_exp J u ht.le] with p hp
    exact (ENNReal.ofReal_pos.mpr (integral_exp_pos hp)).ne'
  have hac1 : momMarg J u ≪ tiltMom (nu J u) t := by
    rw [hTm]
    exact withDensity_absolutelyContinuous' hL.aemeasurable hpos
  have hac : momMarg J u ≪ lam τ := hac1.trans (by
    rw [hT]
    exact withDensity_absolutelyContinuous _ _)
  have hm : (lam τ).withDensity ((momMarg J u).rnDeriv (lam τ)) = momMarg J u :=
    Measure.withDensity_rnDeriv_eq _ _ hac
  refine ⟨hac, hm.symm, ?_⟩
  have h1 : (lam τ).withDensity
        ((momMarg J u).rnDeriv (lam τ) * fun p => ENNReal.ofReal (secLaplace J u t p))
      = (lam τ).withDensity (fun p => ENNReal.ofReal (dU J u t p)) := by
    rw [withDensity_mul _ (Measure.measurable_rnDeriv _ _) hL, hm, ← hTm, hT]
  have h2 := (withDensity_eq_iff_of_sigmaFinite
    ((Measure.measurable_rnDeriv _ _).mul hL).aemeasurable
    (ENNReal.measurable_ofReal.comp hcont.measurable).aemeasurable).mp h1
  filter_upwards [h2] with p hp
  exact (mul_comm _ _).trans hp

/-- **What is left is the Stieltjes step** (`(3)`): `KLJointRep` from the density of `m`, its
factorization `(dm/dλ)(p) = g(p) |klSec ρ p²|`, and the per-sector Laplace match with one `ρ`.
DERIVED: no numeral. -/
theorem klJointRep_of_density (u : H) (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {g : (Fin 4 → ℝ) → ℝ≥0} (hg : Continuous g) (hg0 : g 0 ≠ 0) (hac : momMarg J u ≪ lam τ)
    (hdens : (momMarg J u).rnDeriv (lam τ)
      =ᵐ[lam τ] fun p => (g p : ℝ≥0∞) * klSec ρ (psq p) univ)
    (hL : ∀ᵐ p ∂(momMarg J u), klSec ρ (psq p) univ ≠ ⊤ ∧ ∀ t : ℝ, 0 < t →
      ∫ s, Real.exp (-(t * s)) ∂(klSec ρ (psq p))
        = (klSec ρ (psq p) univ).toReal * secLaplace J u t p) :
    KLJointRep J u ρ := by
  refine klJointRep_of_laplace J u ρ hg hg0 ?_ hL
  rw [← withDensity_congr_ae hdens, Measure.withDensity_rnDeriv_eq _ _ hac]

end Vector

/-! ## 4. On the tree -/

section Tree

variable {N : ℕ}

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumFlow MassGap.ContinuumTimeGroup
  MassGap.ObserverOS MassGap.ObserverEnergyBox
open MassGap.ShellTranslate (realT)
open MassGap.ShellJoint (treeData)
open MassGap.DiniHolder (lipVecs dyadicDini_span)

variable (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
  (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
  (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)
  (hB : UniformBoundF hN (energy0 W D hD)) (τ : Fin 4) {r : ℝ}
  (hpp : (energy0 W D hD).PosPreserving τ r)

include hpos hcube in
/-- **The tree's slice correlator** is `⟪u, timeT t (realT (emb x) u)⟫`, `t ≥ 0`. DERIVED: `0` the
sign of the time; `1` the unit time. -/
theorem tree_corr_eq {u : FlowH hN (energy0 W D hD) hB τ hpp} {t : ℝ} (ht : 0 ≤ t) (x : Sp τ) :
    corr (treeData hN W hD hpos hcube hB τ hpp) u t x
      = inner ℂ u (timeT hN (energy0 W D hD) hB τ hpp t
          (realT hN W hD hpos hcube hB τ hpp (emb τ x) u)) :=
  congrArg (fun T : FlowH hN (energy0 W D hD) hB τ hpp →L[ℂ] FlowH hN (energy0 W D hD) hB τ hpp =>
      inner ℂ u (T ((treeData hN W hD hpos hcube hB τ hpp).R.U (emb τ x) u)))
    (powT_timeT_one hN _ hB τ hpp ht)

include hpos hcube in
/-- **The tree's tilted marginal has a continuous density**, for `u` in the Lipschitz span and `t > 0`,
if `x ↦ ⟪u, timeT t (realT (emb x) u)⟫` is integrable on the slice. DERIVED: `0` the sign of the
time and of the density. -/
theorem tree_tiltMom_eq_withDensity {u : FlowH hN (energy0 W D hD) hB τ hpp}
    (hu : u ∈ Submodule.span ℂ (lipVecs hN W D hD hB τ hpp)) {t : ℝ} (ht : 0 < t)
    (hint : Integrable fun x : Sp τ => inner ℂ u (timeT hN (energy0 W D hD) hB τ hpp t
      (realT hN W hD hpos hcube hB τ hpp (emb τ x) u))) :
    tiltMom (nu (treeData hN W hD hpos hcube hB τ hpp) u) t
        = (lam τ).withDensity
          (fun p => ENNReal.ofReal (dU (treeData hN W hD hpos hcube hB τ hpp) u t p)) ∧
      Continuous (dU (treeData hN W hD hpos hcube hB τ hpp) u t) ∧
      ∀ p, 0 ≤ dU (treeData hN W hD hpos hcube hB τ hpp) u t p :=
  tiltMom_eq_withDensity (treeData hN W hD hpos hcube hB τ hpp)
    (dyadicDini_span hN W hD hpos hcube hB τ hpp hu) ht
    (hint.congr (Eventually.of_forall fun x =>
      (tree_corr_eq hN W hD hpos hcube hB τ hpp ht.le x).symm))

include hpos hcube in
/-- **The tree's momentum marginal has a density, and `L_u · dm/dλ = d_u`**, under the same
integrability hypothesis. DERIVED: `0` the sign of the time. -/
theorem tree_momMarg_density {u : FlowH hN (energy0 W D hD) hB τ hpp}
    (hu : u ∈ Submodule.span ℂ (lipVecs hN W D hD hB τ hpp)) {t : ℝ} (ht : 0 < t)
    (hint : Integrable fun x : Sp τ => inner ℂ u (timeT hN (energy0 W D hD) hB τ hpp t
      (realT hN W hD hpos hcube hB τ hpp (emb τ x) u))) :
    momMarg (treeData hN W hD hpos hcube hB τ hpp) u ≪ lam τ ∧
      momMarg (treeData hN W hD hpos hcube hB τ hpp) u = (lam τ).withDensity
        ((momMarg (treeData hN W hD hpos hcube hB τ hpp) u).rnDeriv (lam τ)) ∧
      ∀ᵐ p ∂(lam τ), ENNReal.ofReal (secLaplace (treeData hN W hD hpos hcube hB τ hpp) u t p)
          * (momMarg (treeData hN W hD hpos hcube hB τ hpp) u).rnDeriv (lam τ) p
        = ENNReal.ofReal (dU (treeData hN W hD hpos hcube hB τ hpp) u t p) :=
  momMarg_density (treeData hN W hD hpos hcube hB τ hpp)
    (dyadicDini_span hN W hD hpos hcube hB τ hpp hu) ht
    (hint.congr (Eventually.of_forall fun x =>
      (tree_corr_eq hN W hD hpos hcube hB τ hpp ht.le x).symm))

end Tree

end

end MassGap.FourierSector

#print axioms MassGap.FourierSector.continuous_gk
#print axioms MassGap.FourierSector.gk_nonneg
#print axioms MassGap.FourierSector.gk_le
#print axioms MassGap.FourierSector.integral_gk
#print axioms MassGap.FourierSector.integrable_gk
#print axioms MassGap.FourierSector.integral_gauss_phase
#print axioms MassGap.FourierSector.continuous_psiM
#print axioms MassGap.FourierSector.integrable_phase_psiM
#print axioms MassGap.FourierSector.continuous_gF
#print axioms MassGap.FourierSector.gauss_smooth
#print axioms MassGap.FourierSector.tendsto_smooth
#print axioms MassGap.FourierSector.dens_spec
#print axioms MassGap.FourierSector.continuous_smooth
#print axioms MassGap.FourierSector.lintegral_smooth
#print axioms MassGap.FourierSector.lintegral_dens_le
#print axioms MassGap.FourierSector.continuous_fourier_psiM
#print axioms MassGap.FourierSector.integrable_fourier_psiM
#print axioms MassGap.FourierSector.eq_withDensity
#print axioms MassGap.FourierSector.fourier_psiM
#print axioms MassGap.FourierSector.continuous_embV
#print axioms MassGap.FourierSector.continuous_proj
#print axioms MassGap.FourierSector.proj_embV
#print axioms MassGap.FourierSector.embV_proj
#print axioms MassGap.FourierSector.phase_emb
#print axioms MassGap.FourierSector.finrank_Sp
#print axioms MassGap.FourierSector.lam_eq_map
#print axioms MassGap.FourierSector.map_withDensity_embV
#print axioms MassGap.FourierSector.tiltMom_time
#print axioms MassGap.FourierSector.map_proj_embV
#print axioms MassGap.FourierSector.charFun_tilt
#print axioms MassGap.FourierSector.isFiniteMeasure_tiltMom
#print axioms MassGap.FourierSector.charFun_tiltV
#print axioms MassGap.FourierSector.tiltV_map
#print axioms MassGap.FourierSector.tiltMom_eq_withDensity
#print axioms MassGap.FourierSector.integrable_sector_exp
#print axioms MassGap.FourierSector.measurable_secLaplace
#print axioms MassGap.FourierSector.tiltMom_eq_momMarg
#print axioms MassGap.FourierSector.momMarg_density
#print axioms MassGap.FourierSector.klJointRep_of_density
#print axioms MassGap.FourierSector.tree_corr_eq
#print axioms MassGap.FourierSector.tree_tiltMom_eq_withDensity
#print axioms MassGap.FourierSector.tree_momMarg_density
