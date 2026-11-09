import Mathlib
import MassGap.DiniHolder
import MassGap.KernelRate

/-!
# MassGap.MomentumSector — the momentum-`p` sectors of the joint measure

`ShellDensity.nu J u` is the rate × momentum measure of a vector `u`: the joint (Gelfand) measure of
`ShellJoint`, off the kernel point `χ(a) = 0`, pushed to `(−log χ(a), p(χ))`. `ShellLorentz.KLJointRep`
asks that it be a Källén–Lehmann measure, one `ρ` for every momentum. This module cuts `nu J u` into
its momentum-`p` sectors, reads the Laplace transform of each sector off the time × space correlator
of `u`, and states what is left for the Källén–Lehmann step as one named property of the sectors.
Declarations are in the namespace `MassGap.MomentumSector`.

DERIVED (module-wide): `0` the bottom of the rates, the zero translation and the excluded kernel point;
`1` the unit time of `treeData`; `Fin 4` the spacetime index. No number enters a clause.

## 1. The sectors (proved)

`nuSwap J u = (nu J u).map swap` (momentum first). `momMarg J u` is its momentum marginal,
`(nu J u).map snd` (`momMarg_eq`), the push-forward of the joint measure on `χ(a) > 0` under the
momentum read (`momMarg_eq_momentum`, under `DyadicDini`). `sector J u = (nuSwap J u).condKernel`: a
Markov kernel from momenta to rates, so `p ↦ σ_p` is a measurable family of probability measures on the
rates. Mathlib's `Measure.condKernel` applies because ℝ is standard Borel.

* `momMarg_compProd_sector`: `momMarg ⊗ₘ σ = nuSwap`, i.e. `nu J u = ∫ σ_p dm(p)` read on rate ×
  momentum (`map_swap_nuSwap` turns it back).
* `sector_unique`: any finite kernel `κ` with `m ⊗ₘ κ = nuSwap` agrees with `σ` for `m`-almost every
  `p`. The sectors are defined only up to an `m`-null set of momenta, and they are unique there.
* `sector_Iio`: for `m`-almost every `p`, `σ_p (−∞, 0) = 0`.
* `sector_laplace_unique`: for `m`-almost every `p`, a finite measure on `[0, ∞)` with the same
  Laplace transform as `σ_p` is `σ_p` (`SmallClose.laplaceRep_unique`).

## 2. The Laplace transform of each sector (proved)

`secLaplace J u t p = ∫ e^{−tE} dσ_p(E)`. `lf t x (E, p) = e^{−tE} e^{i p·x}`.

* `powT_eq_cfc`: `a^t` is the inclusion of `cfc (clamp^t) a` from the joint algebra.
* `inner_powT_U_eq_nu`: under `DyadicDini`, for `t > 0` and every `x`,
  `⟪u, a^t U(x) u⟫ = ∫ e^{−tE} e^{i p·x} dν(E, p)`. The character of `a^t U(x)` is
  `χ(a)^t χ(U x)`; `χ(U x) = e^{i p(χ)·x}` almost everywhere (`ShellDensity.ae_char_eq_phase`);
  `χ(a)^t = e^{−t(−log χ(a))}` where `χ(a) > 0` and `0^t = 0` where not.
* `integral_nu_eq_double`: `∫ lf dν = ∫∫ e^{−tE} e^{i p·x} dσ_p(E) dm(p)` (Fubini on `m ⊗ₘ σ`;
  the integrand is bounded by `1` because `ν` lives on rates `≥ 0`, `ae_rate_nonneg`).
* `inner_powT_U_eq_sector`: `⟪u, a^t U(x) u⟫ = ∫ L_u(t, p) e^{i p·x} dm(p)`, `L_u(t, p) =
  secLaplace J u t p`: the spatial Fourier transform of the time correlator, read sector by sector.
  `re_inner_powT_eq_sector`: at `x = 0`, `Re⟪u, a^t u⟫ = ∫ L_u(t, p) dm(p)`.

On the tree (`treeData`, `a = timeT 1`, `U = realT`), with `powT_timeT_one`: `(timeT 1)^t = timeT t`:

* `inner_timeT_realT_eq_double`, `inner_timeT_realT_eq_sector`, `re_inner_timeT_realT_eq_double`:
  for `u` in the complex span of the Lipschitz-smeared vectors (`DiniHolder.lipVecs`; no Dini
  hypothesis, `DiniHolder.dyadicDini_span`) and `t > 0`:
  `Re⟪u, timeT t (realT x u)⟫ = Re ∫∫ e^{−tE} e^{i p·x} dσ_p(E) dm(p)`, and the complex identity
  without `Re`.
* `timeKernel_eq_sector`: for a Lipschitz regular monomial `P`, the time kernel of `CompKernel` is
  `C(t) = ∫ L_g(t, p) dm(p)`, `g = gvecT P` (`KernelRate.timeKernel_eq_inner_timeT` at `x = 0`).

## 3. What is left for A3 (stated)

`SectorKL J u ρ g`: the momentum marginal is `g(p) · |klSec ρ p²| · λ(dp)` and, for `m`-almost every
`p`, `|klSec ρ p²| · σ_p = klSec ρ p²`, `p² = psq p`. That is the Källén–Lehmann form of the sectors:
one `ρ` for every momentum, with the momentum profile `g`.

* `sector_kl_of_laplace`: the second clause follows from the Laplace transforms alone: if for
  `m`-almost every `p` the sector `klSec ρ p²` is finite and `∫ e^{−tE} d(klSec ρ p²) =
  |klSec ρ p²| · L_u(t, p)` for every `t > 0`, then `|klSec ρ p²| · σ_p = klSec ρ p²` there.

So A3 is: from the correlator `⟪u, timeT t (realT x u)⟫ = ∫ L_u(t, p) e^{i p·x} dm(p)` and Lorentz
(`O(4)`) invariance, read `m = g |klSec ρ p²| λ` and `|klSec ρ p²| L_u(t, p) = ∫ e^{−tE} d(klSec ρ p²)`
for one `ρ`. This is the Stieltjes step of `ShellLorentz` (c).

## What does not follow, plainly

* The sectors exist only for `m`-almost every `p`, unique there (`sector_unique`). Nothing is said
  at a single momentum, in particular not at `p = 0`, which is `m`-null whenever `m` has a density. The
  zero-momentum sector of `ShellDensity.ZeroDensity` is a limit of windowed averages; it is not
  identified with any `σ_p` here.
* `σ_p` is normalised (a probability measure). The physical sector is `(dm/dλ)(p) σ_p`; that `m`
  has a density with respect to `λ = lam τ` (Lebesgue in the three spatial directions, a point mass at `0`
  in direction `τ`) is not proved.
* The identity of §2 is the transform of `ν` in `(t, x)`. That this transform determines `ν` (joint
  Laplace–Fourier uniqueness on rate × momentum) is not proved: `sector_laplace_unique` is uniqueness
  per sector in `t` only, and the Fourier uniqueness in `x` that would recover `m` and each `L_u(·, p)`
  from the correlator is not used. So the correlator does not yet determine the sectors in Lean.
* `SectorKL` is not discharged; its equivalence with `ShellLorentz.KLJointRep` is
  `LorentzStep.klJointRep_iff`.
* On the tree the identities need `hpos`, `hcube` (for `realT`) and hold on the span of
  `lipVecs`, not on all of the regular sector (`DiniHolder`: `DyadicDini` is not closed under limits).

Foundational footprint only (`#print axioms` at the end).
-/

set_option autoImplicit false

namespace MassGap.MomentumSector

open Real Filter Topology MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
open MassGap.ShellMeasure (rateMeasure rateMeasure_Iio clamp continuous_clamp measurable_rate)
open MassGap.ShellJoint (JointData alg UB aB Chars jointMeasure tclamp continuous_tclamp gelfand_cfc
  coe_cfc_aB integral_complex op_G liftR)
open MassGap.ShellTranslate (spatial phase phase_zero)
open MassGap.ShellDensity (DyadicDini momentum rateMom nu nu_Iio_prod ae_char_eq_phase
  aemeasurable_momentum continuous_phase_exp lam)
open MassGap.ShellLorentz (klSec psq klSec_Iio)
open MassGap.ContinuumTimeGroup (powT)

noncomputable section

/-! ## 1. The sectors -/

section Generic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {τ : Fin 4} (J : JointData H (spatial τ))

/-- DERIVED: no numeral. -/
instance isFiniteMeasure_nu (u : H) : IsFiniteMeasure (nu J u) := by
  unfold nu; infer_instance

/-- **The joint measure, momentum first.** DERIVED: no numeral. -/
def nuSwap (u : H) : Measure ((Fin 4 → ℝ) × ℝ) := (nu J u).map Prod.swap

/-- DERIVED: no numeral. -/
instance isFiniteMeasure_nuSwap (u : H) : IsFiniteMeasure (nuSwap J u) := by
  unfold nuSwap; infer_instance

/-- **The momentum marginal** `m`. DERIVED: no numeral. -/
def momMarg (u : H) : Measure (Fin 4 → ℝ) := (nuSwap J u).fst

/-- DERIVED: no numeral. -/
instance isFiniteMeasure_momMarg (u : H) : IsFiniteMeasure (momMarg J u) := by
  unfold momMarg; infer_instance

/-- **The momentum-`p` sectors** `p ↦ σ_p`: the disintegration of `nu` along the momentum.
DERIVED: no numeral. -/
def sector (u : H) : Kernel (Fin 4 → ℝ) ℝ := (nuSwap J u).condKernel

/-- DERIVED: no numeral. -/
instance isMarkovKernel_sector (u : H) : IsMarkovKernel (sector J u) := by
  unfold sector; infer_instance

/-- **The marginal is the momentum push-forward of `nu`.** DERIVED: no numeral. -/
theorem momMarg_eq (u : H) : momMarg J u = (nu J u).map Prod.snd := by
  unfold momMarg nuSwap
  rw [Measure.fst_map_swap]
  rfl

/-- **The marginal is the momentum read of the joint measure** on `χ(a) > 0`. DERIVED: `0` the
excluded kernel point. -/
theorem momMarg_eq_momentum {u : H} (hD : DyadicDini J u) :
    momMarg J u = ((jointMeasure J u).restrict {χ | 0 < (tclamp J χ).1}).map (momentum J) := by
  have hm : AEMeasurable (rateMom J) ((jointMeasure J u).restrict {χ | 0 < (tclamp J χ).1}) :=
    (measurable_rate.comp (continuous_tclamp J).measurable).aemeasurable.prodMk
      (aemeasurable_momentum J hD).restrict
  rw [momMarg_eq, nu, AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hm]
  rfl

/-- **The disintegration**: `m ⊗ₘ σ = nuSwap`. DERIVED: no numeral. -/
theorem momMarg_compProd_sector (u : H) : momMarg J u ⊗ₘ sector J u = nuSwap J u := by
  unfold momMarg sector
  exact Measure.disintegrate _ _

/-- DERIVED: no numeral. -/
theorem map_swap_nuSwap (u : H) : (nuSwap J u).map Prod.swap = nu J u := by
  unfold nuSwap
  rw [Measure.map_map measurable_swap measurable_swap]
  have h : (Prod.swap ∘ Prod.swap : ℝ × (Fin 4 → ℝ) → ℝ × (Fin 4 → ℝ)) = id :=
    funext fun q => Prod.swap_swap q
  rw [h, Measure.map_id]

/-- **The sectors are unique almost everywhere in the momentum.** DERIVED: no numeral. -/
theorem sector_unique (u : H) (κ : Kernel (Fin 4 → ℝ) ℝ) [IsFiniteKernel κ]
    (h : momMarg J u ⊗ₘ κ = nuSwap J u) : ∀ᵐ p ∂(momMarg J u), κ p = sector J u p :=
  eq_condKernel_of_measure_eq_compProd κ h.symm

/-- **Almost every sector lives on rates `≥ 0`.** DERIVED: `0` the bottom of the rates. -/
theorem sector_Iio (u : H) : ∀ᵐ p ∂(momMarg J u), sector J u p (Iio 0) = 0 := by
  have hs : MeasurableSet ((univ : Set (Fin 4 → ℝ)) ×ˢ Iio (0 : ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Iio
  have h0 : nuSwap J u (univ ×ˢ Iio 0) = 0 := by
    unfold nuSwap
    rw [Measure.map_apply measurable_swap hs, preimage_swap_prod]
    exact nu_Iio_prod J u 0 (rateMeasure_Iio J.a u)
  rw [← momMarg_compProd_sector J u, Measure.compProd_apply hs] at h0
  have e : ∀ p : Fin 4 → ℝ, Prod.mk p ⁻¹' ((univ : Set (Fin 4 → ℝ)) ×ˢ Iio (0 : ℝ)) = Iio 0 :=
    fun p => mk_preimage_prod_right (mem_univ p)
  simp only [e] at h0
  filter_upwards [(lintegral_eq_zero_iff ((sector J u).measurable_coe measurableSet_Iio)).mp h0]
    with p hp
  exact hp

/-- **Each sector is fixed by its Laplace transform**, for almost every momentum. DERIVED: `0` the
bottom of the rates and the sign of the time. -/
theorem sector_laplace_unique (u : H) :
    ∀ᵐ p ∂(momMarg J u), ∀ (σ' : Measure ℝ) [IsFiniteMeasure σ'], σ' (Iio 0) = 0 →
      (∀ t : ℝ, 0 < t → ∫ s, Real.exp (-(t * s)) ∂σ' = ∫ s, Real.exp (-(t * s)) ∂(sector J u p)) →
      σ' = sector J u p := by
  filter_upwards [sector_Iio J u] with p hp σ' _ h0 h
  exact SmallClose.laplaceRep_unique h0 hp h

/-! ## 2. The Laplace transform of each sector -/

/-- **The Laplace transform of the sector** `L_u(t, p) = ∫ e^{−tE} dσ_p(E)`. DERIVED: no numeral. -/
def secLaplace (u : H) (t : ℝ) (p : Fin 4 → ℝ) : ℝ := ∫ s, Real.exp (-(t * s)) ∂(sector J u p)

end Generic

/-- **The time × space kernel** `e^{−tE} e^{i p·x}` on rate × momentum. DERIVED: no numeral. -/
def lf {τ : Fin 4} (t : ℝ) (x : spatial τ) (q : ℝ × (Fin 4 → ℝ)) : ℂ :=
  ((Real.exp (-(t * q.1)) : ℝ) : ℂ) * Complex.exp ((phase q.2 x : ℂ) * Complex.I)

/-- DERIVED: no numeral. -/
theorem continuous_lf {τ : Fin 4} (t : ℝ) (x : spatial τ) : Continuous (lf t x) :=
  (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul continuous_fst).neg)).mul
    ((continuous_phase_exp x).comp continuous_snd)

/-- **The power read through the clamp**: `clamp(y)^t`. DERIVED: no numeral. -/
def kpow (t y : ℝ) : ℝ := ((clamp y : Icc (0 : ℝ) 1) : ℝ) ^ t

/-- DERIVED: `0` the sign of the power. -/
theorem continuous_kpow {t : ℝ} (ht : 0 ≤ t) : Continuous (kpow t) :=
  (Real.continuous_rpow_const ht).comp (continuous_subtype_val.comp continuous_clamp)

section Generic2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {τ : Fin 4} (J : JointData H (spatial τ))

/-- **The power of the time step lies in the joint algebra.** DERIVED: `0` the sign of the power;
`0`, `1` the ends of the spectrum interval. -/
theorem powT_eq_cfc {t : ℝ} (ht : 0 ≤ t) :
    powT J.a t = ((cfc (kpow t) (aB J) : alg J) : H →L[ℂ] H) := by
  refine Eq.trans ?_ (coe_cfc_aB J (continuous_kpow ht)).symm
  unfold powT
  refine cfc_congr fun y hy => ?_
  have hy' := J.hsp hy
  show y ^ t = ((projIcc 0 1 zero_le_one y : Icc (0 : ℝ) 1) : ℝ) ^ t
  rw [projIcc_of_mem zero_le_one hy']

/-- **`nu` lives on rates `≥ 0`.** DERIVED: `0` the bottom of the rates. -/
theorem ae_rate_nonneg (u : H) : ∀ᵐ q ∂(nu J u), 0 ≤ q.1 := by
  rw [ae_iff]
  have e : {q : ℝ × (Fin 4 → ℝ) | ¬ 0 ≤ q.1} = Iio 0 ×ˢ univ := by
    ext q; simp
  rw [e]
  exact nu_Iio_prod J u 0 (rateMeasure_Iio J.a u)

/-- **The kernel is integrable**: bounded by `1` on `nu`. DERIVED: `0` the sign of the time; `1` the
bound. -/
theorem integrable_lf (u : H) {t : ℝ} (ht : 0 ≤ t) (x : spatial τ) : Integrable (lf t x) (nu J u) := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) (continuous_lf t x).aestronglyMeasurable ?_
  filter_upwards [ae_rate_nonneg J u] with q hq
  rw [lf, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht hq))

/-- **The time × space correlator is the transform of `nu`**: `⟪u, a^t U(x) u⟫ =
∫ e^{−tE} e^{i p·x} dν`, `t > 0`. DERIVED: `0` the excluded kernel point and the sign of the time. -/
theorem inner_powT_U_eq_nu {u : H} (hD : DyadicDini J u) {t : ℝ} (ht : 0 < t) (x : spatial τ) :
    inner ℂ u (powT J.a t (J.R.U x u)) = ∫ q, lf t x q ∂(nu J u) := by
  have hk := continuous_kpow ht.le
  have hop : powT J.a t (J.R.U x u) = ((cfc (kpow t) (aB J) * UB J x : alg J) : H →L[ℂ] H) u := by
    rw [powT_eq_cfc J ht.le]; rfl
  have hint : inner ℂ u (powT J.a t (J.R.U x u))
      = ∫ χ, gelfandStarTransform (alg J) (cfc (kpow t) (aB J) * UB J x) χ ∂(jointMeasure J u) := by
    rw [integral_complex, op_G, hop]
  let f : C(Chars J, ℝ) := ⟨fun χ => kpow t (χ (aB J)).re,
    hk.comp (Complex.continuous_re.comp (map_continuous (gelfandStarTransform (alg J) (aB J))))⟩
  have hg := gelfand_cfc J hk f (fun _ => rfl)
  have hpt : ∀ χ : Chars J, gelfandStarTransform (alg J) (cfc (kpow t) (aB J) * UB J x) χ
      = (((tclamp J χ : ℝ) ^ t : ℝ) : ℂ) * χ (UB J x) := by
    intro χ
    have h1 : χ (cfc (kpow t) (aB J)) = ((kpow t (χ (aB J)).re : ℝ) : ℂ) :=
      congrArg (fun F : C(Chars J, ℂ) => F χ) hg
    show χ (cfc (kpow t) (aB J) * UB J x) = _
    rw [map_mul, h1]
    rfl
  rw [hint, integral_congr_ae (Eventually.of_forall hpt)]
  have hS : MeasurableSet {χ : Chars J | 0 < (tclamp J χ).1} :=
    measurableSet_lt measurable_const (measurable_subtype_coe.comp (continuous_tclamp J).measurable)
  have hm : AEMeasurable (rateMom J) ((jointMeasure J u).restrict {χ | 0 < (tclamp J χ).1}) :=
    (measurable_rate.comp (continuous_tclamp J).measurable).aemeasurable.prodMk
      (aemeasurable_momentum J hD).restrict
  rw [nu, integral_map hm (continuous_lf t x).aestronglyMeasurable]
  have hz : ∫ χ in {χ : Chars J | 0 < (tclamp J χ).1},
        (((tclamp J χ : ℝ) ^ t : ℝ) : ℂ) * χ (UB J x) ∂(jointMeasure J u)
      = ∫ χ, (((tclamp J χ : ℝ) ^ t : ℝ) : ℂ) * χ (UB J x) ∂(jointMeasure J u) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun χ hχ => ?_
    have h0 : (tclamp J χ : ℝ) = 0 := le_antisymm (not_lt.mp hχ) (tclamp J χ).2.1
    rw [h0, Real.zero_rpow ht.ne', Complex.ofReal_zero, zero_mul]
  rw [← hz]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae (ae_char_eq_phase J hD x)] with χ hχ hph
  have hχ' : 0 < (tclamp J χ : ℝ) := hχ
  have e : (tclamp J χ : ℝ) ^ t = Real.exp (-(t * -Real.log (tclamp J χ : ℝ))) := by
    rw [Real.rpow_def_of_pos hχ']; congr 1; ring
  show (((tclamp J χ : ℝ) ^ t : ℝ) : ℂ) * χ (UB J x) = lf t x (rateMom J χ)
  rw [hph, e]
  rfl

/-- **The transform of `nu` is the double integral over the sectors**:
`∫ lf dν = ∫∫ e^{−tE} e^{i p·x} dσ_p(E) dm(p)`. DERIVED: `0` the sign of the time. -/
theorem integral_nu_eq_double (u : H) {t : ℝ} (ht : 0 ≤ t) (x : spatial τ) :
    ∫ q, lf t x q ∂(nu J u) = ∫ p, ∫ s, lf t x (s, p) ∂(sector J u p) ∂(momMarg J u) := by
  have hi := integrable_lf J u ht x
  rw [← map_swap_nuSwap J u] at hi ⊢
  have hi' : Integrable (fun q : (Fin 4 → ℝ) × ℝ => lf t x q.swap) (nuSwap J u) :=
    hi.comp_measurable measurable_swap
  rw [integral_map measurable_swap.aemeasurable (continuous_lf t x).aestronglyMeasurable]
  rw [← momMarg_compProd_sector J u] at hi' ⊢
  exact Measure.integral_compProd hi'

/-- **The transform of `nu`, sector by sector**: `∫ lf dν = ∫ L_u(t, p) e^{i p·x} dm(p)`.
DERIVED: `0` the sign of the time. -/
theorem integral_nu_eq_sector (u : H) {t : ℝ} (ht : 0 ≤ t) (x : spatial τ) :
    ∫ q, lf t x q ∂(nu J u)
      = ∫ p, (secLaplace J u t p : ℂ) * Complex.exp ((phase p x : ℂ) * Complex.I) ∂(momMarg J u) := by
  rw [integral_nu_eq_double J u ht x]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  show ∫ s, ((Real.exp (-(t * s)) : ℝ) : ℂ) * Complex.exp ((phase p x : ℂ) * Complex.I)
      ∂(sector J u p) = _
  rw [integral_mul_const, integral_complex_ofReal]
  rfl

/-- **The correlator is the spatial Fourier transform of the sectors' Laplace transforms**:
`⟪u, a^t U(x) u⟫ = ∫ L_u(t, p) e^{i p·x} dm(p)`, `t > 0`. DERIVED: `0` the sign of the time. -/
theorem inner_powT_U_eq_sector {u : H} (hD : DyadicDini J u) {t : ℝ} (ht : 0 < t) (x : spatial τ) :
    inner ℂ u (powT J.a t (J.R.U x u))
      = ∫ p, (secLaplace J u t p : ℂ) * Complex.exp ((phase p x : ℂ) * Complex.I) ∂(momMarg J u) :=
  (inner_powT_U_eq_nu J hD ht x).trans (integral_nu_eq_sector J u ht.le x)

/-- **At zero separation**: `Re⟪u, a^t u⟫ = ∫ L_u(t, p) dm(p)`, `t > 0`. DERIVED: `0` the zero
translation and the sign of the time. -/
theorem re_inner_powT_eq_sector {u : H} (hD : DyadicDini J u) {t : ℝ} (ht : 0 < t) :
    (inner ℂ u (powT J.a t u)).re = ∫ p, secLaplace J u t p ∂(momMarg J u) := by
  have h := inner_powT_U_eq_sector J hD ht 0
  rw [J.R.map_zero, one_apply_eq_self] at h
  have e : ∀ p : Fin 4 → ℝ, (secLaplace J u t p : ℂ)
      * Complex.exp ((phase p (0 : spatial τ) : ℂ) * Complex.I) = (secLaplace J u t p : ℂ) :=
    fun p => by rw [phase_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  simp only [e, integral_complex_ofReal] at h
  rw [h, Complex.ofReal_re]

/-! ## 3. What is left for A3 -/

/-- **The Källén–Lehmann form of the sectors** (stated, not discharged): the momentum marginal is
`g(p) |klSec ρ p²| λ(dp)` and almost every sector, rescaled by `|klSec ρ p²|`, is `klSec ρ p²`.
DERIVED: no numeral. -/
def SectorKL (u : H) (ρ : Measure ℝ) (g : (Fin 4 → ℝ) → ℝ≥0) : Prop :=
  momMarg J u = (lam τ).withDensity (fun p => (g p : ℝ≥0∞) * klSec ρ (psq p) univ) ∧
    ∀ᵐ p ∂(momMarg J u), klSec ρ (psq p) univ • sector J u p = klSec ρ (psq p)

/-- **The sector clause of `SectorKL` from the Laplace transforms alone.** DERIVED: `0` the bottom of
the rates and the sign of the time. -/
theorem sector_kl_of_laplace (u : H) (ρ : Measure ℝ)
    (h : ∀ᵐ p ∂(momMarg J u), klSec ρ (psq p) univ ≠ ⊤ ∧ ∀ t : ℝ, 0 < t →
      ∫ s, Real.exp (-(t * s)) ∂(klSec ρ (psq p))
        = (klSec ρ (psq p) univ).toReal * secLaplace J u t p) :
    ∀ᵐ p ∂(momMarg J u), klSec ρ (psq p) univ • sector J u p = klSec ρ (psq p) := by
  filter_upwards [h, sector_Iio J u] with p hp h0
  obtain ⟨hfin, hL⟩ := hp
  haveI : IsFiniteMeasure (klSec ρ (psq p)) := ⟨lt_top_iff_ne_top.mpr hfin⟩
  rw [← ENNReal.coe_toNNReal hfin, Measure.coe_nnreal_smul]
  refine SmallClose.laplaceRep_unique ?_ (klSec_Iio ρ _) fun t ht => ?_
  · rw [Measure.smul_apply, h0, smul_zero]
  · rw [integral_smul_nnreal_measure, hL t ht, NNReal.smul_def, ENNReal.coe_toNNReal_eq_toReal,
      smul_eq_mul]
    rfl

end Generic2

/-! ## 4. On the tree -/

section Tree

variable {N : ℕ}

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumFlow MassGap.ContinuumTimeGroup
  MassGap.ObserverOS MassGap.ObserverEnergyBox
open MassGap.ShellTranslate (realT RMono Reg)
open MassGap.ShellJoint (treeData)
open MassGap.DiniHolder (lipVecs LipReg dyadicDini_span)
open MassGap.CompKernel (timeKernel)

/-- **The unit-time step to the power `t` is the time translation by `t`**, `t ≥ 0`. DERIVED: `0`
the reference step and the sign of the time; `1` the unit time. -/
theorem powT_timeT_one (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4) {r : ℝ}
    (hpp : Φ.PosPreserving τ r) {t : ℝ} (ht : 0 ≤ t) :
    powT (timeT hN Φ hB τ hpp 1) t = timeT hN Φ hB τ hpp t := by
  have ha0 := dySpacing_pos (Nat.one_le_iff_ne_zero.mpr hN) 0
  have hc : 0 ≤ 1 / dySpacing N 0 := (one_div_pos.mpr ha0).le
  unfold timeT powT
  rw [← cfc_comp (fun y : ℝ => y ^ t) (fun y : ℝ => y ^ (1 / dySpacing N 0)) _
    (isSelfAdjoint_stepT hN Φ hB τ hpp 0) (Real.continuous_rpow_const ht).continuousOn
    (Real.continuous_rpow_const hc).continuousOn]
  refine cfc_congr fun y hy => ?_
  have hy0 : 0 ≤ y := (spectrum_stepT hN Φ hB τ hpp 0 hy).1
  show (y ^ (1 / dySpacing N 0)) ^ t = y ^ (t / dySpacing N 0)
  rw [← Real.rpow_mul hy0]
  congr 1
  ring

variable (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
  (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
  (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)
  (hB : UniformBoundF hN (energy0 W D hD)) (τ : Fin 4) {r : ℝ}
  (hpp : (energy0 W D hD).PosPreserving τ r)

include hpos hcube in
/-- **The tree's correlator, double-integral form**: `⟪u, timeT t (realT x u)⟫ =
∫∫ e^{−tE} e^{i p·x} dσ_p(E) dm(p)` on the span of the Lipschitz-smeared vectors, `t > 0`.
DERIVED: `0` the sign of the time; `1` the unit time. -/
theorem inner_timeT_realT_eq_double {u : FlowH hN (energy0 W D hD) hB τ hpp}
    (hu : u ∈ Submodule.span ℂ (lipVecs hN W D hD hB τ hpp)) {t : ℝ} (ht : 0 < t) (x : spatial τ) :
    inner ℂ u (timeT hN (energy0 W D hD) hB τ hpp t (realT hN W hD hpos hcube hB τ hpp x u))
      = ∫ p, ∫ s, lf t x (s, p) ∂(sector (treeData hN W hD hpos hcube hB τ hpp) u p)
          ∂(momMarg (treeData hN W hD hpos hcube hB τ hpp) u) := by
  have h := (inner_powT_U_eq_nu (treeData hN W hD hpos hcube hB τ hpp)
    (dyadicDini_span hN W hD hpos hcube hB τ hpp hu) ht x).trans
    (integral_nu_eq_double (treeData hN W hD hpos hcube hB τ hpp) u ht.le x)
  have e : powT (treeData hN W hD hpos hcube hB τ hpp).a t = timeT hN (energy0 W D hD) hB τ hpp t :=
    powT_timeT_one hN _ hB τ hpp ht.le
  rw [e] at h
  exact h

include hpos hcube in
/-- **The tree's correlator, sector form**: `⟪u, timeT t (realT x u)⟫ = ∫ L_u(t, p) e^{i p·x} dm(p)`.
DERIVED: `0` the sign of the time; `1` the unit time. -/
theorem inner_timeT_realT_eq_sector {u : FlowH hN (energy0 W D hD) hB τ hpp}
    (hu : u ∈ Submodule.span ℂ (lipVecs hN W D hD hB τ hpp)) {t : ℝ} (ht : 0 < t) (x : spatial τ) :
    inner ℂ u (timeT hN (energy0 W D hD) hB τ hpp t (realT hN W hD hpos hcube hB τ hpp x u))
      = ∫ p, (secLaplace (treeData hN W hD hpos hcube hB τ hpp) u t p : ℂ)
          * Complex.exp ((phase p x : ℂ) * Complex.I)
          ∂(momMarg (treeData hN W hD hpos hcube hB τ hpp) u) :=
  (inner_timeT_realT_eq_double hN W hD hpos hcube hB τ hpp hu ht x).trans
    ((integral_nu_eq_double (treeData hN W hD hpos hcube hB τ hpp) u ht.le x).symm.trans
      (integral_nu_eq_sector (treeData hN W hD hpos hcube hB τ hpp) u ht.le x))

include hpos hcube in
/-- **The real part**: `Re⟪u, timeT t (realT x u)⟫ = Re ∫∫ e^{−tE} e^{i p·x} dσ_p(E) dm(p)`.
DERIVED: `0` the sign of the time; `1` the unit time. -/
theorem re_inner_timeT_realT_eq_double {u : FlowH hN (energy0 W D hD) hB τ hpp}
    (hu : u ∈ Submodule.span ℂ (lipVecs hN W D hD hB τ hpp)) {t : ℝ} (ht : 0 < t) (x : spatial τ) :
    (inner ℂ u (timeT hN (energy0 W D hD) hB τ hpp t (realT hN W hD hpos hcube hB τ hpp x u))).re
      = (∫ p, ∫ s, lf t x (s, p) ∂(sector (treeData hN W hD hpos hcube hB τ hpp) u p)
          ∂(momMarg (treeData hN W hD hpos hcube hB τ hpp) u)).re :=
  congrArg Complex.re (inner_timeT_realT_eq_double hN W hD hpos hcube hB τ hpp hu ht x)

include hpos hcube in
/-- **The time kernel of a Lipschitz regular monomial, sector by sector**: `C(t) = ∫ L_g(t, p) dm(p)`,
`g = gvecT P`, `t > 0`. DERIVED: `0` the zero translation and the sign of the time; `1` the unit
time. -/
theorem timeKernel_eq_sector (P : RMono N D τ r) (hP : LipReg D P.1.1) {t : ℝ} (ht : 0 < t) :
    timeKernel hN W hD τ P.1.1 t
      = ∫ p, secLaplace (treeData hN W hD hpos hcube hB τ hpp)
          (gvecT hN (energy0 W D hD) hB τ hpp P.1) t p
          ∂(momMarg (treeData hN W hD hpos hcube hB τ hpp) (gvecT hN (energy0 W D hD) hB τ hpp P.1)) := by
  have hu : gvecT hN (energy0 W D hD) hB τ hpp P.1 ∈ Submodule.span ℂ (lipVecs hN W D hD hB τ hpp) :=
    Submodule.subset_span ⟨P, hP, rfl⟩
  have h := re_inner_powT_eq_sector (treeData hN W hD hpos hcube hB τ hpp)
    (dyadicDini_span hN W hD hpos hcube hB τ hpp hu) ht
  have e : powT (treeData hN W hD hpos hcube hB τ hpp).a t = timeT hN (energy0 W D hD) hB τ hpp t :=
    powT_timeT_one hN _ hB τ hpp ht.le
  rw [e] at h
  rw [KernelRate.timeKernel_eq_inner_timeT hN W hD hpos hcube τ hpp P.1 P.2 ht.le]
  exact h

end Tree

end

end MassGap.MomentumSector

#print axioms MassGap.MomentumSector.isFiniteMeasure_nu
#print axioms MassGap.MomentumSector.isMarkovKernel_sector
#print axioms MassGap.MomentumSector.momMarg_eq
#print axioms MassGap.MomentumSector.momMarg_eq_momentum
#print axioms MassGap.MomentumSector.momMarg_compProd_sector
#print axioms MassGap.MomentumSector.map_swap_nuSwap
#print axioms MassGap.MomentumSector.sector_unique
#print axioms MassGap.MomentumSector.sector_Iio
#print axioms MassGap.MomentumSector.sector_laplace_unique
#print axioms MassGap.MomentumSector.continuous_lf
#print axioms MassGap.MomentumSector.continuous_kpow
#print axioms MassGap.MomentumSector.powT_eq_cfc
#print axioms MassGap.MomentumSector.ae_rate_nonneg
#print axioms MassGap.MomentumSector.integrable_lf
#print axioms MassGap.MomentumSector.inner_powT_U_eq_nu
#print axioms MassGap.MomentumSector.integral_nu_eq_double
#print axioms MassGap.MomentumSector.integral_nu_eq_sector
#print axioms MassGap.MomentumSector.inner_powT_U_eq_sector
#print axioms MassGap.MomentumSector.re_inner_powT_eq_sector
#print axioms MassGap.MomentumSector.sector_kl_of_laplace
#print axioms MassGap.MomentumSector.powT_timeT_one
#print axioms MassGap.MomentumSector.inner_timeT_realT_eq_double
#print axioms MassGap.MomentumSector.inner_timeT_realT_eq_sector
#print axioms MassGap.MomentumSector.re_inner_timeT_realT_eq_double
#print axioms MassGap.MomentumSector.timeKernel_eq_sector
