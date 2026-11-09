import Mathlib
import MassGap.LorentzStep
import MassGap.KernRadial

/-!
# MassGap.LorentzConverse — toward the converse half of A3: the correlator fixes the joint measure

`LorentzStep` names three pieces missing for the converse of A3: (i) a bridge from the smeared
kernel to the correlator `⟪u, timeT t (realT x u)⟫`, (ii) joint Fourier–Laplace uniqueness on
rate × momentum, (iii) Stieltjes inversion. This module proves (ii) and (i), and reduces the
Källén–Lehmann form of the sectors to one transform identity of the kernel. Declarations are in the
namespace `MassGap.LorentzConverse`.

DERIVED (module-wide): `0` the bottom of the rates, the time component of a spatial vector and the
time origin; `1` the unit entry of a coordinate vector and the one factor of a one-factor monomial;
`Fin 4` the spacetime index. No number enters a clause.

## 1. Joint Fourier–Laplace uniqueness (proved)

For a finite measure `μ` on rate × momentum, `tiltMom μ t` is the momentum marginal of
`e^{−tE} dμ(E, p)`, and `rateOn μ A` is the rate marginal of `μ` on the momenta in `A`.

* `momentum_time`, `nu_time`: the momentum of every character has zero `τ` component, so `nu J u`
  lives on `p_τ = 0`. `klJoint_Iio`, `klJoint_time`: the same two support facts for `klJoint τ ρ g`.
* `tiltMom_eq`: equal transforms `∫ e^{−tE} e^{i p·x} dμ` at one `t ≥ 0` and every spatial `x` give
  equal tilted marginals (`Measure.ext_of_charFunDual` on `Fin 4 → ℝ`; a dual vector `L` is read as
  the spatial vector `xL τ L` on `p_τ = 0`).
* `laplace_rateOn`: `∫ e^{−tE} d(rateOn μ A) = (tiltMom μ t A).toReal`.
* `ext_laplace_fourier`: two finite measures on `[0, ∞) × {p_τ = 0}` with equal transforms for every
  `t > 0` and every spatial `x` are equal: the tilted marginals agree, so each `rateOn μ A` is fixed by
  its Laplace transform (`SmallClose.laplaceRep_unique`), so `μ` agrees with `μ'` on every rectangle
  (`Measure.ext_prod`).
* `nu_eq_of_inner`: under `DyadicDini`, the correlator `⟪u, a^t U(x) u⟫` (`t > 0`, all `x`) determines
  `nu J u`; `momMarg_eq_of_inner`, `sector_eq_of_inner`: it determines the momentum marginal and the
  sectors, as measures and as kernels, not only almost everywhere. This closes the item "the
  correlator does not yet determine the sectors" of `MomentumSector`.
* `nu_eq_klJoint_of_inner`, `sectorKL_of_inner`: if the correlator equals the transform of
  `klJoint τ ρ g` (finite), then `nu J u = klJoint τ ρ g` and `SectorKL J u ρ g`.
* On the tree, for `u`, `v` in the complex span of `DiniHolder.lipVecs`: `tree_nu_eq_of_inner`,
  `tree_sectorKL_of_inner`.

## 2. The bridge from the kernel to the correlator (proved)

* `continuous_kernF_shift`: `z ↦ S(θP ∪ shift_z Q)` is continuous on `ℝ⁴` for regular `P`, `Q`.
* `inner_gvecT_timeT`: for regular margin monomials `P`, `Q` and `t ≥ 0`,
  `⟪gvecT P, timeT t (gvecT Q)⟫ = S(θP ∪ shift_{t e_τ} Q)` (dyadic times from `stepT_gvecT`, every
  time by continuity of both sides).
* `inner_timeT_realT_gvecT`: for a regular monomial `P`, `u = gvecT P`, `t ≥ 0`, spatial `x`:
  `⟪u, timeT t (realT x u)⟫ = S(θP ∪ shift_{t e_τ + x} P)` (`DiniHolder.realT_gvecT`,
  `Mono.shift_shift`): the correlator is one function of the separation `t e_τ + x`.
* `kernF_single`: for a one-factor monomial `⟨1, ![A]⟩`, `S(θP ∪ shift_z P) = kern2 (θA) A z`; so
  `corr_eq_kern2`: the correlator is `kern2 (θA) A (t e_τ + x)`.
* `corr_symm`: under `KernRadial.O4Inv` on a class holding `A.1` and `(θA).1`, every orthogonal `R`
  that fixes the pair (`act R (θA) = θA`, `act R A = A`) is a symmetry of the correlator:
  `R (t e_τ + x) = t' e_τ + x'` gives `corr(t', x') = corr(t, x)` (`KernRadial.kern2_cov`).
* `corr_radial`: if `kern2 (θA) A` is `Radial`, the correlator depends on `t² + |x|²` alone.
* `tree_sectorKL_of_kernF`: for a Lipschitz regular monomial `P`, if
  `S(θP ∪ shift_{t e_τ + x} P) = ∫ e^{−tE} e^{i p·x} d(klJoint τ ρ g)` for `t > 0` and every `x`, then
  `SectorKL` holds at `gvecT P`. With (ii), A3 at `gvecT P` is exactly this one identity of the kernel.

## What does not follow, plainly

* (iii) is not proved and is still needed. (i) and (ii) reduce A3 at `gvecT P` to the identity of
  `tree_sectorKL_of_kernF`: the transform of `klJoint τ ρ g` must equal the kernel `S(θP ∪ shift_z P)`
  at `z = t e_τ + x`. Producing `ρ` and `g` from the kernel is the inversion step: Fourier inversion in
  `x` and Stieltjes inversion of the time transform, neither of which is in Mathlib at this pin, and
  neither of which is built here.
* The route through `KernRadial.kern2_radial` has no instance here: it needs `O(4)`-invariant test
  functions, and an invariant function supported in `{z_τ > r}`, `r ≥ 0`, vanishes (argued here, not
  proved in Lean). `corr_radial` takes `Radial` as a hypothesis and is not shown vacuous. Minkowski boosts
  and Lorentz covariance of the correlator are not covered. `corr_symm` transports covariance only under
  the orthogonal maps that fix the pair; a boost mixing `t` and `x` moves `A` off the positive-time
  half-space, so its image is a `kern2` value of non-margin fields, not a correlator of a vector.
* `corr_symm` needs `O4Inv` for the rotations that are not signed permutations; that rests on `pyth`
  invariance (`KernRadial`, "What does not follow").
* The uniqueness results are in `(t, x)` with `t > 0` and `x` spatial; they say nothing at a single
  momentum. The sectors are equal as kernels because they are the same construction applied to equal
  measures; `SectorKL` itself is not discharged for any composite vector.
* On the tree the results need `hpos`, `hcube` and hold on the span of `lipVecs`.

Foundational footprint only (`#print axioms` at the end).
-/

set_option autoImplicit false

namespace MassGap.LorentzConverse

open Real Filter Topology MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
open MassGap.BandShell (shell shell_nonneg)
open MassGap.ShellMeasure (rateMeasure)
open MassGap.ShellJoint (JointData jointMeasure tclamp UB Chars)
open MassGap.ShellTranslate (spatial phase mem_spatial)
open MassGap.ShellDensity (DyadicDini momentum momentum_eq zk pseq dy ej UB_zero rateMom nu lam lamF)
open MassGap.ShellLorentz (klSec psq klJoint klMap measurable_klMap)
open MassGap.MomentumSector (lf continuous_lf momMarg sector nuSwap SectorKL inner_powT_U_eq_nu
  powT_timeT_one)
open MassGap.ContinuumTimeGroup (powT)

noncomputable section

/-! ## 1. Joint Fourier–Laplace uniqueness -/

section Support

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {τ : Fin 4} (J : JointData H (spatial τ))

/-- **The momentum of a character has zero time component.** DERIVED: `0` the time component;
`1` the unit character value. -/
theorem momentum_time (χ : Chars J) : momentum J χ τ = 0 := by
  have hz : ∀ k : ℕ, zk J τ k χ = 1 := by
    intro k
    have e0 : ej τ τ = 0 := Subtype.ext (funext fun i => by
      show (if i = τ then (0 : ℝ) else if i = τ then 1 else 0) = 0
      split_ifs <;> rfl)
    have e : dy τ τ k = 0 := by
      rw [dy, e0, smul_zero]
    rw [zk, e, UB_zero, map_one]
  rw [momentum_eq J (K := 0) (fun k _ => by rw [hz k, Complex.one_re]; exact one_pos)]
  simp [pseq, hz]

/-- **`nu` lives on momenta with zero time component.** DERIVED: `0` the time component. -/
theorem nu_time (u : H) : ∀ᵐ q ∂(nu J u), q.2 τ = 0 := by
  rw [ae_iff]
  by_cases hm : AEMeasurable (rateMom J) ((jointMeasure J u).restrict {χ | 0 < (tclamp J χ).1})
  · have hs : MeasurableSet {q : ℝ × (Fin 4 → ℝ) | ¬ q.2 τ = 0} :=
      (measurableSet_eq_fun ((measurable_pi_apply τ).comp measurable_snd) measurable_const).compl
    rw [nu, Measure.map_apply_of_aemeasurable hm hs]
    have e : rateMom J ⁻¹' {q : ℝ × (Fin 4 → ℝ) | ¬ q.2 τ = 0} = ∅ := by
      ext χ
      simp [rateMom, momentum_time J χ]
    rw [e, measure_empty]
  · rw [nu, Measure.map_of_not_aemeasurable hm]
    rfl

end Support

/-- **`klJoint` lives on rates `≥ 0`.** DERIVED: `0` the bottom of the rates. -/
theorem klJoint_Iio (τ : Fin 4) (ρ : Measure ℝ) (g : (Fin 4 → ℝ) → ℝ≥0) :
    klJoint τ ρ g (Iio 0 ×ˢ univ) = 0 := by
  rw [klJoint, Measure.map_apply measurable_klMap (measurableSet_Iio.prod MeasurableSet.univ)]
  have e : klMap ⁻¹' (Iio (0 : ℝ) ×ˢ (univ : Set (Fin 4 → ℝ))) = ∅ := by
    ext q
    simp only [mem_preimage, klMap, mem_prod, mem_Iio, mem_univ, and_true, mem_empty_iff_false,
      iff_false, not_lt]
    exact shell_nonneg _ _
  rw [e, measure_empty]

/-- **`lam τ` is carried by `p_τ = 0`.** DERIVED: `0` the time momentum. -/
theorem lam_time_null (τ : Fin 4) : lam τ (Function.eval τ ⁻¹' ({0}ᶜ : Set ℝ)) = 0 := by
  unfold lam
  refine Measure.pi_eval_preimage_null _ ?_
  rw [lamF, if_pos rfl]
  simp

/-- **`klJoint` lives on momenta with zero time component.** DERIVED: `0` the time component. -/
theorem klJoint_time (τ : Fin 4) (ρ : Measure ℝ) [SigmaFinite ρ] (g : (Fin 4 → ℝ) → ℝ≥0) :
    ∀ᵐ q ∂(klJoint τ ρ g), q.2 τ = 0 := by
  have hs : MeasurableSet {q : ℝ × (Fin 4 → ℝ) | q.2 τ = 0} :=
    measurableSet_eq_fun ((measurable_pi_apply τ).comp measurable_snd) measurable_const
  rw [klJoint, ae_map_iff measurable_klMap.aemeasurable hs]
  have h : ∀ᵐ q ∂((lam τ).prod ρ), q.1 τ = 0 := by
    rw [ae_iff]
    have e : {q : (Fin 4 → ℝ) × ℝ | ¬ q.1 τ = 0}
        = (Function.eval τ ⁻¹' ({0}ᶜ : Set ℝ)) ×ˢ (univ : Set ℝ) := by
      ext q
      simp
    rw [e, Measure.prod_prod, lam_time_null, zero_mul]
  filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le h] with q hq
  exact hq

section Unique

variable {τ : Fin 4}

/-- **The tilt** `e^{−tE}` as a density. DERIVED: `0` the sign of the exponential. -/
def tiltDens (t : ℝ) (q : ℝ × (Fin 4 → ℝ)) : ℝ≥0 := ⟨Real.exp (-(t * q.1)), (Real.exp_pos _).le⟩

/-- DERIVED: no numeral. -/
theorem measurable_tiltDens (t : ℝ) : Measurable (tiltDens t) :=
  (Continuous.subtype_mk (Real.continuous_exp.comp (continuous_const.mul continuous_fst).neg)
    _).measurable

/-- DERIVED: `0` the sign of the exponential. -/
theorem tiltDens_coe (t : ℝ) (q : ℝ × (Fin 4 → ℝ)) :
    (tiltDens t q : ℝ≥0∞) = ENNReal.ofReal (Real.exp (-(t * q.1))) :=
  (ENNReal.ofReal_eq_coe_nnreal (Real.exp_pos _).le).symm

/-- **The tilted momentum marginal** `p ↦ ∫ e^{−tE} dμ(E, p)`. DERIVED: no numeral. -/
def tiltMom (μ : Measure (ℝ × (Fin 4 → ℝ))) (t : ℝ) : Measure (Fin 4 → ℝ) :=
  (μ.withDensity fun q => (tiltDens t q : ℝ≥0∞)).map Prod.snd

/-- **The rate marginal on the momenta of `A`.** DERIVED: no numeral. -/
def rateOn (μ : Measure (ℝ × (Fin 4 → ℝ))) (A : Set (Fin 4 → ℝ)) : Measure ℝ :=
  (μ.restrict (Prod.snd ⁻¹' A)).map Prod.fst

/-- DERIVED: no numeral. -/
instance isFiniteMeasure_rateOn (μ : Measure (ℝ × (Fin 4 → ℝ))) [IsFiniteMeasure μ]
    (A : Set (Fin 4 → ℝ)) : IsFiniteMeasure (rateOn μ A) := by
  unfold rateOn; infer_instance

/-- DERIVED: `0` the bottom of the rates. -/
theorem ae_rate_nonneg_of {μ : Measure (ℝ × (Fin 4 → ℝ))} (h0 : μ (Iio 0 ×ˢ univ) = 0) :
    ∀ᵐ q ∂μ, 0 ≤ q.1 := by
  rw [ae_iff]
  have e : {q : ℝ × (Fin 4 → ℝ) | ¬ 0 ≤ q.1} = Iio 0 ×ˢ univ := by
    ext q; simp
  rw [e]
  exact h0

/-- **The tilted measure is finite** on rates `≥ 0`. DERIVED: `0` the signs; `1` the bound of the
tilt. -/
theorem isFiniteMeasure_tilt (μ : Measure (ℝ × (Fin 4 → ℝ))) [IsFiniteMeasure μ]
    (h0 : μ (Iio 0 ×ˢ univ) = 0) {t : ℝ} (ht : 0 ≤ t) :
    IsFiniteMeasure (μ.withDensity fun q => (tiltDens t q : ℝ≥0∞)) := by
  refine isFiniteMeasure_withDensity (ne_top_of_le_ne_top (measure_ne_top μ univ) ?_)
  rw [← lintegral_one]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_rate_nonneg_of h0] with q hq
  rw [ENNReal.coe_le_one_iff, ← NNReal.coe_le_coe, NNReal.coe_one]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht hq))

/-- **A dual vector read as a spatial vector**: `x_j = L(e_j)` off the time slot. DERIVED: `0` the
time component; `1` the unit entry. -/
def xL (τ : Fin 4) (L : StrongDual ℝ (Fin 4 → ℝ)) : spatial τ :=
  ⟨fun j => if j = τ then 0 else L (fun k => if j = k then 1 else 0), mem_spatial (by simp)⟩

/-- **On `p_τ = 0` a dual vector is the phase of `xL`.** DERIVED: `0` the time component. -/
theorem dual_eq_phase (L : StrongDual ℝ (Fin 4 → ℝ)) {p : Fin 4 → ℝ} (hp : p τ = 0) :
    L p = phase p (xL τ L) := by
  rw [show L p = (L : (Fin 4 → ℝ) →ₗ[ℝ] ℝ) p from rfl, LinearMap.pi_apply_eq_sum_univ]
  unfold phase
  refine Finset.sum_congr rfl fun j _ => ?_
  show p j • L (fun k => if j = k then (1 : ℝ) else 0)
    = p j * (if j = τ then 0 else L (fun k => if j = k then (1 : ℝ) else 0))
  by_cases hj : j = τ
  · subst hj; simp [hp]
  · rw [if_neg hj, smul_eq_mul]

/-- **The tilted characteristic function is the transform** at `xL`. DERIVED: `0` the time
component. -/
theorem tilt_char_ae {μ : Measure (ℝ × (Fin 4 → ℝ))} (hτ : ∀ᵐ q ∂μ, q.2 τ = 0) (t : ℝ)
    (L : StrongDual ℝ (Fin 4 → ℝ)) :
    ∀ᵐ q ∂μ, tiltDens t q • Complex.exp ((L q.2 : ℂ) * Complex.I) = lf t (xL τ L) q := by
  filter_upwards [hτ] with q hq
  rw [lf, dual_eq_phase L hq, NNReal.smul_def, Complex.real_smul]
  rfl

/-- **Fourier uniqueness at one time**: equal transforms in `x` give equal tilted marginals.
DERIVED: `0` the bottom of the rates, the time component and the sign of the time. -/
theorem tiltMom_eq {μ μ' : Measure (ℝ × (Fin 4 → ℝ))} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (h0 : μ (Iio 0 ×ˢ univ) = 0) (h0' : μ' (Iio 0 ×ˢ univ) = 0)
    (hτ : ∀ᵐ q ∂μ, q.2 τ = 0) (hτ' : ∀ᵐ q ∂μ', q.2 τ = 0) {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ x : spatial τ, ∫ q, lf t x q ∂μ = ∫ q, lf t x q ∂μ') :
    tiltMom μ t = tiltMom μ' t := by
  haveI := isFiniteMeasure_tilt μ h0 ht
  haveI := isFiniteMeasure_tilt μ' h0' ht
  haveI : IsFiniteMeasure (tiltMom μ t) := by unfold tiltMom; infer_instance
  haveI : IsFiniteMeasure (tiltMom μ' t) := by unfold tiltMom; infer_instance
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  have hc : Continuous fun v : Fin 4 → ℝ => Complex.exp ((L v : ℂ) * Complex.I) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp L.continuous).mul continuous_const)
  rw [charFunDual_apply, charFunDual_apply, tiltMom, tiltMom,
    integral_map measurable_snd.aemeasurable hc.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable hc.aestronglyMeasurable,
    integral_withDensity_eq_integral_smul (measurable_tiltDens t),
    integral_withDensity_eq_integral_smul (measurable_tiltDens t),
    integral_congr_ae (tilt_char_ae hτ t L), integral_congr_ae (tilt_char_ae hτ' t L)]
  exact h (xL τ L)

/-- **The Laplace transform of `rateOn μ A` is the tilted marginal of `A`.** DERIVED: `0` the
bottom of the rates. -/
theorem laplace_rateOn (μ : Measure (ℝ × (Fin 4 → ℝ))) {A : Set (Fin 4 → ℝ)}
    (hA : MeasurableSet A) (t : ℝ) :
    ∫ s, Real.exp (-(t * s)) ∂(rateOn μ A) = (tiltMom μ t A).toReal := by
  have hc : Continuous fun s : ℝ => Real.exp (-(t * s)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id).neg
  rw [rateOn, integral_map measurable_fst.aemeasurable hc.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun q => (Real.exp_pos _).le)
      (hc.comp continuous_fst).aestronglyMeasurable,
    tiltMom, Measure.map_apply measurable_snd hA, withDensity_apply _ (measurable_snd hA)]
  congr 1
  refine lintegral_congr fun q => ?_
  rw [tiltDens_coe]

/-- **`rateOn` lives on rates `≥ 0`.** DERIVED: `0` the bottom of the rates. -/
theorem rateOn_Iio {μ : Measure (ℝ × (Fin 4 → ℝ))} (h0 : μ (Iio 0 ×ˢ univ) = 0)
    (A : Set (Fin 4 → ℝ)) : rateOn μ A (Iio 0) = 0 := by
  rw [rateOn, Measure.map_apply measurable_fst measurableSet_Iio,
    Measure.restrict_apply (measurable_fst measurableSet_Iio)]
  exact measure_mono_null inter_subset_left (by rw [← Set.prod_univ]; exact h0)

/-- **`rateOn` reads the rectangles.** DERIVED: no numeral. -/
theorem rateOn_apply (μ : Measure (ℝ × (Fin 4 → ℝ))) (A : Set (Fin 4 → ℝ))
    {B : Set ℝ} (hB : MeasurableSet B) : rateOn μ A B = μ (B ×ˢ A) := by
  rw [rateOn, Measure.map_apply measurable_fst hB, Measure.restrict_apply (measurable_fst hB),
    Set.prod_eq]

/-- **Joint Fourier–Laplace uniqueness on rate × momentum**: two finite measures on
`[0, ∞) × {p_τ = 0}` with equal transforms `∫ e^{−tE} e^{i p·x}` for every `t > 0` and every spatial
`x` are equal. DERIVED: `0` the bottom of the rates, the time component and the sign of the time. -/
theorem ext_laplace_fourier {μ μ' : Measure (ℝ × (Fin 4 → ℝ))} [IsFiniteMeasure μ]
    [IsFiniteMeasure μ'] (h0 : μ (Iio 0 ×ˢ univ) = 0) (h0' : μ' (Iio 0 ×ˢ univ) = 0)
    (hτ : ∀ᵐ q ∂μ, q.2 τ = 0) (hτ' : ∀ᵐ q ∂μ', q.2 τ = 0)
    (h : ∀ t : ℝ, 0 < t → ∀ x : spatial τ, ∫ q, lf t x q ∂μ = ∫ q, lf t x q ∂μ') : μ = μ' := by
  have hT : ∀ t : ℝ, 0 < t → tiltMom μ t = tiltMom μ' t := fun t ht =>
    tiltMom_eq h0 h0' hτ hτ' ht.le (h t ht)
  refine Measure.ext_prod fun {B} {A} hB hA => ?_
  have hR : rateOn μ A = rateOn μ' A := by
    refine SmallClose.laplaceRep_unique (rateOn_Iio h0 A) (rateOn_Iio h0' A) fun t ht => ?_
    rw [laplace_rateOn μ hA, laplace_rateOn μ' hA, hT t ht]
  rw [← rateOn_apply μ A hB, ← rateOn_apply μ' A hB, hR]

end Unique

section Correlator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  {τ : Fin 4} (J : JointData H (spatial τ)) (J' : JointData H' (spatial τ))

/-- **`nu` lives on rates `≥ 0`.** DERIVED: `0` the bottom of the rates. -/
theorem nu_Iio0 (u : H) : nu J u (Iio 0 ×ˢ univ) = 0 :=
  MassGap.ShellDensity.nu_Iio_prod J u 0 (MassGap.ShellMeasure.rateMeasure_Iio J.a u)

/-- **The correlator determines `nu`**: under `DyadicDini`, equal correlators `⟪u, a^t U(x) u⟫`
(`t > 0`, every spatial `x`) give equal joint measures. DERIVED: `0` the sign of the time. -/
theorem nu_eq_of_inner {u : H} {v : H'} (hu : DyadicDini J u) (hv : DyadicDini J' v)
    (h : ∀ t : ℝ, 0 < t → ∀ x : spatial τ,
      inner ℂ u (powT J.a t (J.R.U x u)) = inner ℂ v (powT J'.a t (J'.R.U x v))) :
    nu J u = nu J' v :=
  ext_laplace_fourier (nu_Iio0 J u) (nu_Iio0 J' v) (nu_time J u) (nu_time J' v)
    fun t ht x => by
      rw [← inner_powT_U_eq_nu J hu ht x, ← inner_powT_U_eq_nu J' hv ht x]
      exact h t ht x

/-- **The correlator determines the momentum marginal.** DERIVED: `0` the sign of the time. -/
theorem momMarg_eq_of_inner {u : H} {v : H'} (hu : DyadicDini J u) (hv : DyadicDini J' v)
    (h : ∀ t : ℝ, 0 < t → ∀ x : spatial τ,
      inner ℂ u (powT J.a t (J.R.U x u)) = inner ℂ v (powT J'.a t (J'.R.U x v))) :
    momMarg J u = momMarg J' v := by
  unfold momMarg nuSwap
  rw [nu_eq_of_inner J J' hu hv h]

/-- **The correlator determines the sectors**, as kernels. DERIVED: `0` the sign of the time. -/
theorem sector_eq_of_inner {u : H} {v : H'} (hu : DyadicDini J u) (hv : DyadicDini J' v)
    (h : ∀ t : ℝ, 0 < t → ∀ x : spatial τ,
      inner ℂ u (powT J.a t (J.R.U x u)) = inner ℂ v (powT J'.a t (J'.R.U x v))) :
    sector J u = sector J' v := by
  have e : nuSwap J u = nuSwap J' v := by
    unfold nuSwap
    rw [nu_eq_of_inner J J' hu hv h]
  unfold sector
  congr 1

/-- **A Källén–Lehmann transform fixes `nu`**: if the correlator equals the transform of a finite
`klJoint τ ρ g`, then `nu J u = klJoint τ ρ g`. DERIVED: `0` the sign of the time. -/
theorem nu_eq_klJoint_of_inner {u : H} (hu : DyadicDini J u) (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (g : (Fin 4 → ℝ) → ℝ≥0) [IsFiniteMeasure (klJoint τ ρ g)]
    (h : ∀ t : ℝ, 0 < t → ∀ x : spatial τ,
      inner ℂ u (powT J.a t (J.R.U x u)) = ∫ q, lf t x q ∂(klJoint τ ρ g)) :
    nu J u = klJoint τ ρ g :=
  ext_laplace_fourier (nu_Iio0 J u) (klJoint_Iio τ ρ g) (nu_time J u)
    (klJoint_time τ ρ g) fun t ht x => by
      rw [← inner_powT_U_eq_nu J hu ht x]
      exact h t ht x

/-- **The sector form from the transform**: `SectorKL J u ρ g`. DERIVED: `0` the sign of the time. -/
theorem sectorKL_of_inner {u : H} (hu : DyadicDini J u) (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {g : (Fin 4 → ℝ) → ℝ≥0} (hg : Measurable g) [IsFiniteMeasure (klJoint τ ρ g)]
    (h : ∀ t : ℝ, 0 < t → ∀ x : spatial τ,
      inner ℂ u (powT J.a t (J.R.U x u)) = ∫ q, lf t x q ∂(klJoint τ ρ g)) :
    SectorKL J u ρ g :=
  LorentzStep.sectorKL_of_klJoint J u ρ hg (nu_eq_klJoint_of_inner J hu ρ g h)

end Correlator

/-! ## 2. The bridge on the tree -/

section Tree

variable {N : ℕ}

open Matrix

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumFlow MassGap.ContinuumTimeGroup
  MassGap.OSPositivity MassGap.ObserverOS MassGap.ObserverEnergyBox
open MassGap.ShellTranslate (realT RMono Reg rShift spatial_time reg_pairFam pairFam_shift_right)
open MassGap.ShellJoint (treeData)
open MassGap.DiniHolder (lipVecs LipReg dyadicDini_span)
open MassGap.CompKernel (kern2 tVec continuous_tVec timeVec_eq_tVec inner_gvecT)
open MassGap.KernRadial (O4Inv act kern2_cov)
open MassGap.ShellLorentz (Radial nsq)

variable (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
  (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
  (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)
  (hB : UniformBoundF hN (energy0 W D hD)) (τ : Fin 4) {r : ℝ}
  (hpp : (energy0 W D hD).PosPreserving τ r)

include hpos hcube in
/-- **The kernel is continuous in the separation** of the right factor. DERIVED: `0` the
untranslated reflected block. -/
theorem continuous_kernF_shift {P Q : Mono N} (hP : Reg D P) (hQ : Reg D Q) :
    Continuous fun z : Fin 4 → ℝ => kernF hN (energy0 W D hD) τ P (Mono.shift z Q) := by
  have hR := reg_pairFam hD τ hP hQ
  have h := ShellTranslate.continuous_contSF_translate hN W hD hpos hcube (pairFam τ P Q)
    (fun x => (hR x).1) (fun x => (hR x).2)
  have hc : Continuous (fun z : Fin 4 → ℝ => fun x : Fin P.1 ⊕ Fin Q.1 =>
      Sum.elim (fun _ => (0 : Fin 4 → ℝ)) (fun _ => z) x) :=
    continuous_pi fun x => by
      cases x with
      | inl i => exact continuous_const
      | inr j => exact continuous_id
  refine (h.comp hc).congr fun z => ?_
  exact congrArg (fun G => contSF hN (energy0 W D hD) G) (pairFam_shift_right τ P Q z).symm

include hpos hcube in
/-- **The time matrix element of two regular vectors is the kernel at the time separation**:
`⟪gvecT P, timeT t (gvecT Q)⟫ = S(θP ∪ shift_{t e_τ} Q)`, `t ≥ 0`. DERIVED: `0` the sign of the
time and the base of the induction. -/
theorem inner_gvecT_timeT (P Q : MarginMono N τ r) (hP : Reg D P.1) (hQ : Reg D Q.1) {t : ℝ}
    (ht : 0 ≤ t) :
    inner ℂ (gvecT hN (energy0 W D hD) hB τ hpp P)
        (timeT hN (energy0 W D hD) hB τ hpp t (gvecT hN (energy0 W D hD) hB τ hpp Q))
      = (kernF hN (energy0 W D hD) τ P.1 (Mono.shift (tVec τ t) Q.1) : ℂ) := by
  have hit : ∀ (m k : ℕ) (Q' : MarginMono N τ r),
      (stepT hN (energy0 W D hD) hB τ hpp m ^ k) (gvecT hN (energy0 W D hD) hB τ hpp Q')
        = gvecT hN (energy0 W D hD) hB τ hpp ((MarginMono.shift hN τ m)^[k] Q') := by
    intro m k
    induction k with
    | zero => intro Q'; rfl
    | succ k ih =>
      intro Q'
      rw [pow_succ, ContinuousLinearMap.mul_apply, stepT_gvecT, ih, Function.iterate_succ_apply]
  obtain ⟨s, hdy, hs0, hst⟩ := KernelRate.exists_dyadic_tendsto hN ht
  have hL := ((continuous_kernF_shift hN W hD hpos hcube τ hP hQ).comp
    (continuous_tVec τ)).tendsto t |>.comp hst
  have hLc := (Complex.continuous_ofReal.tendsto _).comp hL
  have hs' : Tendsto s atTop (𝓝[Ici 0] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hst, Eventually.of_forall hs0⟩
  have hc := (continuousOn_timeT hN (energy0 W D hD) hB τ hpp
    (gvecT hN (energy0 W D hD) hB τ hpp Q) t ht).tendsto.comp hs'
  have hi : Continuous fun y : FlowH hN (energy0 W D hD) hB τ hpp =>
      inner ℂ (gvecT hN (energy0 W D hD) hB τ hpp P) y :=
    continuous_const.inner continuous_id
  have hR := (hi.tendsto _).comp hc
  refine tendsto_nhds_unique hR (hLc.congr fun m => ?_)
  obtain ⟨n, hn⟩ := hdy m
  have e : timeT hN (energy0 W D hD) hB τ hpp (s m) = stepT hN (energy0 W D hD) hB τ hpp m ^ n := by
    rw [hn, mul_comm (dySpacing N m) (n : ℝ), timeT_dyadic]
  show (kernF hN (energy0 W D hD) τ P.1 (Mono.shift (tVec τ (s m)) Q.1) : ℂ)
    = inner ℂ (gvecT hN (energy0 W D hD) hB τ hpp P)
        (timeT hN (energy0 W D hD) hB τ hpp (s m) (gvecT hN (energy0 W D hD) hB τ hpp Q))
  rw [e, hit, inner_gvecT, MarginMono.shift_iterate, timeVec_eq_tVec, hn, Int.cast_natCast]

include hpos hcube in
/-- **The bridge**: `⟪u, timeT t (realT x u)⟫ = S(θP ∪ shift_{t e_τ + x} P)` for `u = gvecT P`, `P`
regular, `t ≥ 0`, `x` spatial. DERIVED: `0` the sign of the time. -/
theorem inner_timeT_realT_gvecT (P : RMono N D τ r) {t : ℝ} (ht : 0 ≤ t) (x : spatial τ) :
    inner ℂ (gvecT hN (energy0 W D hD) hB τ hpp P.1)
        (timeT hN (energy0 W D hD) hB τ hpp t
          (realT hN W hD hpos hcube hB τ hpp x (gvecT hN (energy0 W D hD) hB τ hpp P.1)))
      = (kernF hN (energy0 W D hD) τ P.1.1 (Mono.shift (tVec τ t + (x : Fin 4 → ℝ)) P.1.1) : ℂ) := by
  rw [DiniHolder.realT_gvecT hN W hD hpos hcube hB τ hpp x P,
    inner_gvecT_timeT hN W hD hpos hcube hB τ hpp P.1 (rShift (x : Fin 4 → ℝ) (spatial_time x) P).1
      P.2 (rShift (x : Fin 4 → ℝ) (spatial_time x) P).2 ht]
  show (kernF hN (energy0 W D hD) τ P.1.1
      (Mono.shift (tVec τ t) (Mono.shift (x : Fin 4 → ℝ) P.1.1)) : ℂ) = _
  rw [Mono.shift_shift, add_comm (x : Fin 4 → ℝ)]

/-- **For one factor the kernel is `kern2`**: `S(θP ∪ shift_z P) = kern2 (θA) A z`,
`P = ⟨1, ![A]⟩`. DERIVED: `1` the one factor; `Fin 2` the two factors of the form. -/
theorem kernF_single (A : SField N) (z : Fin 4 → ℝ) :
    kernF hN (energy0 W D hD) τ ⟨1, ![A]⟩ (Mono.shift z ⟨1, ![A]⟩)
      = kern2 hN W hD (SField.refl τ A) A z := by
  unfold kernF kern2
  rw [← contSF_comp_equiv hN (energy0 W D hD) finSumFinEquiv]
  congr 1
  funext x
  rcases x with i | j
  · fin_cases i; rfl
  · fin_cases j; rfl

include hpos hcube in
/-- **The correlator of a one-factor monomial is `kern2` at the separation `t e_τ + x`.**
DERIVED: `0` the sign of the time; `1` the one factor. -/
theorem corr_eq_kern2 (P : RMono N D τ r) (A : SField N) (hPA : P.1.1 = ⟨1, ![A]⟩) {t : ℝ}
    (ht : 0 ≤ t) (x : spatial τ) :
    inner ℂ (gvecT hN (energy0 W D hD) hB τ hpp P.1)
        (timeT hN (energy0 W D hD) hB τ hpp t
          (realT hN W hD hpos hcube hB τ hpp x (gvecT hN (energy0 W D hD) hB τ hpp P.1)))
      = (kern2 hN W hD (SField.refl τ A) A (tVec τ t + (x : Fin 4 → ℝ)) : ℂ) := by
  rw [inner_timeT_realT_gvecT hN W hD hpos hcube hB τ hpp P ht x, hPA, kernF_single]

include hpos hcube in
/-- **`O(4)` covariance as a symmetry of the correlator**: under `O4Inv`, an orthogonal `R` fixing the
pair `(θA, A)` with `R (t e_τ + x) = t' e_τ + x'` gives `corr(t', x') = corr(t, x)`. DERIVED: `0` the
signs of the times; `1` the identity. -/
theorem corr_symm {Φs : Set (LField (MassGap.SUN.SU N))} (hO4 : O4Inv hN (energy0 W D hD) Φs)
    (P : RMono N D τ r) (A : SField N) (hPA : P.1.1 = ⟨1, ![A]⟩)
    (hθ : (SField.refl τ A).1 ∈ Φs) (hA : A.1 ∈ Φs)
    (hθu : UniformContinuous (SField.refl τ A).2.1) (hAu : UniformContinuous A.2.1)
    (R : Matrix (Fin 4) (Fin 4) ℝ) (hR : Rᵀ * R = 1)
    (hRθ : act R (SField.refl τ A) = SField.refl τ A) (hRA : act R A = A)
    {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') (x x' : spatial τ)
    (hz : R.mulVec (tVec τ t + (x : Fin 4 → ℝ)) = tVec τ t' + (x' : Fin 4 → ℝ)) :
    inner ℂ (gvecT hN (energy0 W D hD) hB τ hpp P.1)
        (timeT hN (energy0 W D hD) hB τ hpp t'
          (realT hN W hD hpos hcube hB τ hpp x' (gvecT hN (energy0 W D hD) hB τ hpp P.1)))
      = inner ℂ (gvecT hN (energy0 W D hD) hB τ hpp P.1)
        (timeT hN (energy0 W D hD) hB τ hpp t
          (realT hN W hD hpos hcube hB τ hpp x (gvecT hN (energy0 W D hD) hB τ hpp P.1))) := by
  rw [corr_eq_kern2 hN W hD hpos hcube hB τ hpp P A hPA ht' x',
    corr_eq_kern2 hN W hD hpos hcube hB τ hpp P A hPA ht x, ← hz]
  have h := kern2_cov hN W hD hO4 R hR (SField.refl τ A) A hθ hA hθu hAu (tVec τ t + (x : Fin 4 → ℝ))
  rw [hRθ, hRA] at h
  exact congrArg (fun y : ℝ => (y : ℂ)) h

include hpos hcube in
/-- **A radial kernel makes the correlator a function of `t² + |x|²`.** DERIVED: `0` the signs of the
times. -/
theorem corr_radial (P : RMono N D τ r) (A : SField N) (hPA : P.1.1 = ⟨1, ![A]⟩)
    (hrad : Radial (kern2 hN W hD (SField.refl τ A) A))
    {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') (x x' : spatial τ)
    (hn : nsq (tVec τ t + (x : Fin 4 → ℝ)) = nsq (tVec τ t' + (x' : Fin 4 → ℝ))) :
    inner ℂ (gvecT hN (energy0 W D hD) hB τ hpp P.1)
        (timeT hN (energy0 W D hD) hB τ hpp t
          (realT hN W hD hpos hcube hB τ hpp x (gvecT hN (energy0 W D hD) hB τ hpp P.1)))
      = inner ℂ (gvecT hN (energy0 W D hD) hB τ hpp P.1)
        (timeT hN (energy0 W D hD) hB τ hpp t'
          (realT hN W hD hpos hcube hB τ hpp x' (gvecT hN (energy0 W D hD) hB τ hpp P.1))) := by
  rw [corr_eq_kern2 hN W hD hpos hcube hB τ hpp P A hPA ht x,
    corr_eq_kern2 hN W hD hpos hcube hB τ hpp P A hPA ht' x', hrad _ _ hn]

include hpos hcube in
/-- **On the tree the correlator determines `nu`**, on the span of the Lipschitz-smeared vectors.
DERIVED: `0` the sign of the time; `1` the unit time. -/
theorem tree_nu_eq_of_inner {u v : FlowH hN (energy0 W D hD) hB τ hpp}
    (hu : u ∈ Submodule.span ℂ (lipVecs hN W D hD hB τ hpp))
    (hv : v ∈ Submodule.span ℂ (lipVecs hN W D hD hB τ hpp))
    (h : ∀ t : ℝ, 0 < t → ∀ x : spatial τ,
      inner ℂ u (timeT hN (energy0 W D hD) hB τ hpp t (realT hN W hD hpos hcube hB τ hpp x u))
        = inner ℂ v (timeT hN (energy0 W D hD) hB τ hpp t (realT hN W hD hpos hcube hB τ hpp x v))) :
    nu (treeData hN W hD hpos hcube hB τ hpp) u = nu (treeData hN W hD hpos hcube hB τ hpp) v := by
  refine nu_eq_of_inner _ _ (dyadicDini_span hN W hD hpos hcube hB τ hpp hu)
    (dyadicDini_span hN W hD hpos hcube hB τ hpp hv) fun t ht x => ?_
  have e : powT (treeData hN W hD hpos hcube hB τ hpp).a t = timeT hN (energy0 W D hD) hB τ hpp t :=
    powT_timeT_one hN _ hB τ hpp ht.le
  rw [e]
  exact h t ht x

include hpos hcube in
/-- **On the tree the transform identity gives the sector form**, on the span of the
Lipschitz-smeared vectors. DERIVED: `0` the sign of the time; `1` the unit time. -/
theorem tree_sectorKL_of_inner {u : FlowH hN (energy0 W D hD) hB τ hpp}
    (hu : u ∈ Submodule.span ℂ (lipVecs hN W D hD hB τ hpp)) (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {g : (Fin 4 → ℝ) → ℝ≥0} (hg : Measurable g) [IsFiniteMeasure (klJoint τ ρ g)]
    (h : ∀ t : ℝ, 0 < t → ∀ x : spatial τ,
      inner ℂ u (timeT hN (energy0 W D hD) hB τ hpp t (realT hN W hD hpos hcube hB τ hpp x u))
        = ∫ q, lf t x q ∂(klJoint τ ρ g)) :
    SectorKL (treeData hN W hD hpos hcube hB τ hpp) u ρ g := by
  refine sectorKL_of_inner _ (dyadicDini_span hN W hD hpos hcube hB τ hpp hu) ρ hg fun t ht x => ?_
  have e : powT (treeData hN W hD hpos hcube hB τ hpp).a t = timeT hN (energy0 W D hD) hB τ hpp t :=
    powT_timeT_one hN _ hB τ hpp ht.le
  rw [e]
  exact h t ht x

include hpos hcube in
/-- **A3 at a Lipschitz regular monomial is one identity of the kernel**: if
`S(θP ∪ shift_{t e_τ + x} P) = ∫ e^{−tE} e^{i p·x} d(klJoint τ ρ g)` for `t > 0` and every spatial `x`,
then `SectorKL` holds at `gvecT P`. DERIVED: `0` the sign of the time. -/
theorem tree_sectorKL_of_kernF (P : RMono N D τ r) (hP : LipReg D P.1.1) (ρ : Measure ℝ)
    [IsFiniteMeasure ρ] {g : (Fin 4 → ℝ) → ℝ≥0} (hg : Measurable g)
    [IsFiniteMeasure (klJoint τ ρ g)]
    (h : ∀ t : ℝ, 0 < t → ∀ x : spatial τ,
      (kernF hN (energy0 W D hD) τ P.1.1 (Mono.shift (tVec τ t + (x : Fin 4 → ℝ)) P.1.1) : ℂ)
        = ∫ q, lf t x q ∂(klJoint τ ρ g)) :
    SectorKL (treeData hN W hD hpos hcube hB τ hpp) (gvecT hN (energy0 W D hD) hB τ hpp P.1) ρ g :=
  tree_sectorKL_of_inner hN W hD hpos hcube hB τ hpp (Submodule.subset_span ⟨P, hP, rfl⟩) ρ hg
    fun t ht x => (inner_timeT_realT_gvecT hN W hD hpos hcube hB τ hpp P ht.le x).trans (h t ht x)

end Tree

end

end MassGap.LorentzConverse

#print axioms MassGap.LorentzConverse.momentum_time
#print axioms MassGap.LorentzConverse.nu_time
#print axioms MassGap.LorentzConverse.klJoint_Iio
#print axioms MassGap.LorentzConverse.lam_time_null
#print axioms MassGap.LorentzConverse.klJoint_time
#print axioms MassGap.LorentzConverse.measurable_tiltDens
#print axioms MassGap.LorentzConverse.tiltDens_coe
#print axioms MassGap.LorentzConverse.isFiniteMeasure_rateOn
#print axioms MassGap.LorentzConverse.ae_rate_nonneg_of
#print axioms MassGap.LorentzConverse.isFiniteMeasure_tilt
#print axioms MassGap.LorentzConverse.dual_eq_phase
#print axioms MassGap.LorentzConverse.tilt_char_ae
#print axioms MassGap.LorentzConverse.tiltMom_eq
#print axioms MassGap.LorentzConverse.laplace_rateOn
#print axioms MassGap.LorentzConverse.rateOn_Iio
#print axioms MassGap.LorentzConverse.rateOn_apply
#print axioms MassGap.LorentzConverse.ext_laplace_fourier
#print axioms MassGap.LorentzConverse.nu_Iio0
#print axioms MassGap.LorentzConverse.nu_eq_of_inner
#print axioms MassGap.LorentzConverse.momMarg_eq_of_inner
#print axioms MassGap.LorentzConverse.sector_eq_of_inner
#print axioms MassGap.LorentzConverse.nu_eq_klJoint_of_inner
#print axioms MassGap.LorentzConverse.sectorKL_of_inner
#print axioms MassGap.LorentzConverse.continuous_kernF_shift
#print axioms MassGap.LorentzConverse.inner_gvecT_timeT
#print axioms MassGap.LorentzConverse.inner_timeT_realT_gvecT
#print axioms MassGap.LorentzConverse.kernF_single
#print axioms MassGap.LorentzConverse.corr_eq_kern2
#print axioms MassGap.LorentzConverse.corr_symm
#print axioms MassGap.LorentzConverse.corr_radial
#print axioms MassGap.LorentzConverse.tree_nu_eq_of_inner
#print axioms MassGap.LorentzConverse.tree_sectorKL_of_inner
#print axioms MassGap.LorentzConverse.tree_sectorKL_of_kernF
