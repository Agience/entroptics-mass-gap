import Mathlib
import MassGap.MomentumSector
import MassGap.ShellLorentz

/-!
# MassGap.LorentzStep — the forward half of the Euclidean Källén–Lehmann step (A3): the shell form and its sectors

A3 asks that a radial, reflection-positive two-point function be `∫ Δ_s dρ(s)` for one finite `ρ`, so
that each momentum sector is the shell measure `ShellLorentz.klSec ρ p²`. This module proves the
closed-form half: the free propagator in the mixed (time, momentum) representation is the shell form,
a superposition of shells has sectors `klSec ρ p²`, and the Källén–Lehmann joint measure is exactly
the sector form `MomentumSector.SectorKL`. Declarations are in the namespace `MassGap.LorentzStep`.

DERIVED (module-wide): `0` the zero momentum, the time origin and the signs; `1` the unit mass of a
normalised sector; `2` the two half-lines of the time axis and the factor `2√(s + p²)` of the shell
weight; `Fin 4` the spacetime index. No number enters a clause.

## 1. The free propagator in the mixed representation (proved)

* `free_mixed_fourier`: for `E > 0`, `∫ e^{−E|t|} e^{−ikt} dt = 2E/(k² + E²)` (the two half-lines,
  `integral_exp_mul_complex_Ioi` / `_Iic`).
* `free_propagator_fourier`: with `E = shell s p² = √(s + p²)`, `s + p² > 0`:
  `∫ e^{−E|t|}/(2E) · e^{−ikt} dt = 1/(k² + p² + s)`. The time Fourier transform of the shell form
  `e^{−|t|√(s + p²)}/(2√(s + p²))` is the four-dimensional Euclidean propagator `1/(k₀² + p² + s)`
  of mass² `s`, a function of `k₀² + p²` alone.
* `klSec_laplace`: `∫ e^{−tE} d(klSec ρ p²)(E) = ∫ e^{−t√(s + p²)}/(2√(s + p²)) dρ(s)` (as lower
  integrals; no finiteness needed): the sector of a superposition `∫ Δ_s dρ` is the superposition of
  shell forms. `free_laplace`: at `ρ = δ_{m²}` it is `e^{−t√(m² + p²)}/(2√(m² + p²))`, the sector of
  `ShellMeasure.free_kallenLehmann`.

## 2. The sectors of a superposition (proved)

`klKer ρ`: the kernel `p ↦ klSec ρ (psq p)`; `klNorm ρ`: its normalisation
`p ↦ |klSec ρ p²|⁻¹ · klSec ρ p²` (a finite kernel, mass `≤ 1`).

* `klJoint_rect`: `klJoint τ ρ g (B × A) = ∫_A g(p) · klSec ρ p² (B) dλ(p)`.
* `klJoint_swap`: if `m₀ = g |klSec ρ p²| λ` is finite, `(klJoint τ ρ g).swap = m₀ ⊗ₘ klNorm ρ`: the
  superposition disintegrates along the momentum into the normalised shell sectors.
* `sectorKL_of_klJoint`: `nu J u = klJoint τ ρ g` ⇒ `SectorKL J u ρ g`.
* `klJoint_of_sectorKL`: `SectorKL J u ρ g` ⇒ `nu J u = klJoint τ ρ g` (for measurable `g`).
* `klJointRep_iff`: `KLJointRep J u ρ ↔ ∃ g` continuous with `g(0) ≠ 0` and `SectorKL J u ρ g`.
  This closes the item "`SectorKL ⇔ KLJointRep` is not proved" of `MomentumSector`.
* `klJointRep_of_laplace`: the momentum marginal `m = g |klSec ρ p²| λ` and the per-sector Laplace
  match `∫ e^{−tE} d(klSec ρ p²) = |klSec ρ p²| · L_u(t, p)` (for `m`-almost every `p`, every `t > 0`)
  give `KLJointRep` (`MomentumSector.sector_kl_of_laplace` for the sector clause).

## 3. The Clay read through the sectors (proved, under the sector form)

* `clay_zero_momentum_sectorKL`: `clay_zero_momentum_kl` with `nu J u = klJoint τ ρ g` replaced by
  `SectorKL J u ρ g` (`g` continuous, `g(0) ≠ 0`).
* `clay_zero_momentum_laplace`: the same with `SectorKL` replaced by its two analytic inputs: the
  marginal density and the per-sector Laplace match with one `ρ`.

## What does not follow, plainly

* The converse direction of A3 is not proved: `O(4)` invariance (`KernRadial.O4Inv`,
  `kern2_radial`) plus the per-sector Laplace representations do not yet give, in Lean, one `ρ`
  independent of `p` with `|klSec ρ p²| L_u(t, p) = ∫ e^{−tE} d(klSec ρ p²)`, nor the marginal
  density `m = g |klSec ρ p²| λ`. The exact remaining step is the hypothesis pair of
  `klJointRep_of_laplace` for `u` in the Lipschitz span. The argued route: Fourier transform the
  correlator `⟪u, timeT t (realT x u)⟫ = ∫ L_u(t, p) e^{i p·x} dm(p)` in `(t, x)`; radiality of the
  four-dimensional transform (from `kern2_radial`, which is a statement about smeared kernels, not
  about this correlator) makes the time transform of `L_u(·, p)` a function of `k₀² + p²`
  (`free_propagator_fourier` is this for one shell); Stieltjes uniqueness then fixes one `ρ`. Three
  pieces are missing: (i) a bridge from `kern2` (the smeared `contSF` kernel) to the correlator of
  `u` in the Lipschitz span; (ii) joint Fourier–Laplace uniqueness on rate × momentum (Mathlib has
  `Measure.ext_of_charFun` for the Fourier half; the joint statement is not assembled); (iii) Stieltjes
  inversion, absent from Mathlib at this pin.
* `free_propagator_fourier` is the forward transform (shell form ↦ propagator). The inverse
  statement (propagator ↦ shell form) is Fourier inversion for an integrable continuous function
  with integrable transform; it is not stated here.
* `SectorKL` and `KLJointRep` are equivalent (`klJointRep_iff`); neither is discharged for any
  composite vector. `clay_zero_momentum_sectorKL` and `clay_zero_momentum_laplace` therefore run
  under that hypothesis, not under `O4Inv` alone.

Foundational footprint only (`#print axioms` at the end).
-/

set_option autoImplicit false

namespace MassGap.LorentzStep

open Real Filter Topology MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
open MassGap.BandShell (shell shell_nonneg SpecBottom)
open MassGap.ShellMeasure (klWeight measurable_klWeight measurable_shell freeRate free_kallenLehmann
  rateMeasure)
open MassGap.ShellJoint (JointData)
open MassGap.ShellTranslate (spatial)
open MassGap.ShellDensity (nu lam ZeroDensity)
open MassGap.ShellLorentz (klSec psq klDens klMap klJoint measurable_klMap continuous_shellP
  continuous_psq KLJointRep clay_zero_momentum_kl)
open MassGap.MomentumSector (SectorKL momMarg nuSwap sector map_swap_nuSwap sector_unique
  momMarg_compProd_sector secLaplace sector_kl_of_laplace)
open MassGap.ObserverOSReconstructionS (OSDataS)

noncomputable section

/-! ## 1. The free propagator in the mixed representation -/

/-- **The time Fourier transform of `e^{−E|t|}`** is `2E/(k² + E²)`, `E > 0`. DERIVED: `0` the time
origin and the sign of `E`; `2` the two half-lines. -/
theorem free_mixed_fourier {E : ℝ} (hE : 0 < E) (k : ℝ) :
    ∫ t : ℝ, Complex.exp (-(E : ℂ) * ((|t| : ℝ) : ℂ) - (k : ℂ) * (t : ℂ) * Complex.I)
      = 2 * (E : ℂ) / ((k : ℂ) ^ 2 + (E : ℂ) ^ 2) := by
  set f : ℝ → ℂ := fun t => Complex.exp (-(E : ℂ) * ((|t| : ℝ) : ℂ) - (k : ℂ) * (t : ℂ) * Complex.I)
    with hf
  set a : ℂ := -((E : ℂ) + (k : ℂ) * Complex.I) with ha
  set b : ℂ := (E : ℂ) - (k : ℂ) * Complex.I with hb
  have hare : a.re < 0 := by simp [ha, hE]
  have hbre : 0 < b.re := by simp [hb, hE]
  have eqI : EqOn (fun t : ℝ => Complex.exp (a * t)) f (Ioi 0) := by
    intro t ht
    have ht' : |t| = t := abs_of_pos ht
    simp only [hf, ha, ht']
    congr 1; ring
  have eqL : EqOn (fun t : ℝ => Complex.exp (b * t)) f (Iic 0) := by
    intro t ht
    have ht' : |t| = -t := abs_of_nonpos ht
    simp only [hf, hb, ht', Complex.ofReal_neg]
    congr 1; ring
  have iI : IntegrableOn f (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi hare 0).congr_fun eqI measurableSet_Ioi
  have iL : IntegrableOn f (Iic 0) :=
    (integrableOn_exp_mul_complex_Iic hbre 0).congr_fun eqL measurableSet_Iic
  have vI : ∫ t in Ioi (0 : ℝ), f t = 1 / ((E : ℂ) + (k : ℂ) * Complex.I) := by
    rw [← setIntegral_congr_fun measurableSet_Ioi eqI, integral_exp_mul_complex_Ioi hare 0]
    simp only [ha, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [div_neg, neg_div, neg_neg]
  have vL : ∫ t in Iic (0 : ℝ), f t = 1 / ((E : ℂ) - (k : ℂ) * Complex.I) := by
    rw [← setIntegral_congr_fun measurableSet_Iic eqL, integral_exp_mul_complex_Iic hbre 0]
    simp only [hb, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hsplit : ∫ t, f t = (∫ t in Iic (0 : ℝ), f t) + ∫ t in Ioi (0 : ℝ), f t := by
    rw [← setIntegral_union (Set.disjoint_left.mpr fun t h1 h2 => absurd (mem_Iic.mp h1)
      (not_le.mpr (mem_Ioi.mp h2))) measurableSet_Ioi iL iI, Iic_union_Ioi, Measure.restrict_univ]
  have h1 : (E : ℂ) - (k : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h2 : (E : ℂ) + (k : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hprod : ((E : ℂ) - (k : ℂ) * Complex.I) * ((E : ℂ) + (k : ℂ) * Complex.I)
      = (k : ℂ) ^ 2 + (E : ℂ) ^ 2 := by
    linear_combination (-(k : ℂ) ^ 2) * Complex.I_sq
  show ∫ t, f t = _
  rw [hsplit, vL, vI, div_add_div _ _ h1 h2, hprod]
  congr 1
  ring

/-- **The shell form is the four-dimensional propagator**: with `E = √(s + p²)`, `s + p² > 0`, the
time Fourier transform of `e^{−E|t|}/(2E)` is `1/(k² + p² + s)`. DERIVED: `0` the sign; `2` the shell
weight. -/
theorem free_propagator_fourier {s p2 : ℝ} (h : 0 < s + p2) (k : ℝ) :
    ∫ t : ℝ, Complex.exp (-((shell s p2 : ℝ) : ℂ) * ((|t| : ℝ) : ℂ) - (k : ℂ) * (t : ℂ) * Complex.I)
        / (2 * ((shell s p2 : ℝ) : ℂ))
      = 1 / ((k : ℂ) ^ 2 + (p2 : ℂ) + (s : ℂ)) := by
  have hE : 0 < shell s p2 := Real.sqrt_pos.mpr h
  have hE2 : shell s p2 ^ 2 = s + p2 := Real.sq_sqrt h.le
  have hEc : ((shell s p2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hE.ne'
  have hE2c : ((shell s p2 : ℝ) : ℂ) ^ 2 = (s : ℂ) + (p2 : ℂ) := by
    rw [← Complex.ofReal_pow, hE2, Complex.ofReal_add]
  rw [integral_div, free_mixed_fourier hE k, hE2c, div_right_comm,
    div_self (mul_ne_zero two_ne_zero hEc)]
  congr 1
  ring

/-- **The sector of a superposition is the superposition of shell forms**:
`∫ e^{−tE} d(klSec ρ p²) = ∫ e^{−t√(s + p²)}/(2√(s + p²)) dρ(s)`. DERIVED: `2` the shell weight. -/
theorem klSec_laplace (ρ : Measure ℝ) (p2 t : ℝ) :
    ∫⁻ E, ENNReal.ofReal (Real.exp (-(t * E))) ∂(klSec ρ p2)
      = ∫⁻ s, ENNReal.ofReal (Real.exp (-(t * shell s p2)) / (2 * shell s p2)) ∂ρ := by
  have hm : Measurable fun E : ℝ => ENNReal.ofReal (Real.exp (-(t * E))) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).measurable
  rw [klSec, lintegral_map hm (measurable_shell p2),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_klWeight p2)
      (show Measurable fun s => ENNReal.ofReal (Real.exp (-(t * shell s p2))) from
        hm.comp (measurable_shell p2))]
  refine lintegral_congr fun s => ?_
  simp only [Pi.mul_apply, Function.comp_apply, klWeight]
  rw [← ENNReal.ofReal_mul (div_nonneg zero_le_one (mul_nonneg zero_le_two (shell_nonneg s p2)))]
  congr 1
  ring

/-- **The free sector**: `∫ e^{−tE} d(freeRate m² p²) = e^{−t√(m² + p²)}/(2√(m² + p²))`.
DERIVED: `0` the sign; `2` the shell weight. -/
theorem free_laplace (m2 : ℝ) {p2 : ℝ} (hp : 0 ≤ p2) (t : ℝ) :
    ∫⁻ E, ENNReal.ofReal (Real.exp (-(t * E))) ∂(freeRate m2 p2)
      = ENNReal.ofReal (Real.exp (-(t * shell m2 p2)) / (2 * shell m2 p2)) := by
  rw [free_kallenLehmann m2 p2 hp]
  have h := klSec_laplace (Measure.dirac m2) p2 t
  rw [lintegral_dirac] at h
  exact h

/-! ## 2. The sectors of a superposition -/

/-- **A sector, set by set**: `klSec ρ p² (B) = ∫ 1_B(√(s + p²)) dρ(s)/(2√(s + p²))`.
DERIVED: no numeral. -/
theorem klSec_apply (ρ : Measure ℝ) (p2 : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    klSec ρ p2 B = ∫⁻ s, B.indicator 1 (shell s p2) * klWeight p2 s ∂ρ := by
  rw [klSec, Measure.map_apply (measurable_shell p2) hB,
    withDensity_apply _ (measurable_shell p2 hB), ← lintegral_indicator (measurable_shell p2 hB)]
  refine lintegral_congr fun s => ?_
  by_cases h : shell s p2 ∈ B <;> simp [Set.indicator_apply, h]

/-- DERIVED: `1`, `2` as in `klWeight`. -/
theorem measurable_klW : Measurable fun q : (Fin 4 → ℝ) × ℝ => klWeight (psq q.1) q.2 := by
  show Measurable fun q : (Fin 4 → ℝ) × ℝ => ENNReal.ofReal (1 / (2 * shell q.2 (psq q.1)))
  exact ENNReal.measurable_ofReal.comp ((continuous_shellP.measurable.const_mul 2).const_div 1)

/-- DERIVED: no numeral. -/
theorem measurable_klDens' {g : (Fin 4 → ℝ) → ℝ≥0} (hg : Measurable g) : Measurable (klDens g) :=
  (hg.comp measurable_fst).coe_nnreal_ennreal.mul measurable_klW

/-- **The sector is measurable in the momentum.** DERIVED: no numeral. -/
theorem measurable_klSec_apply (ρ : Measure ℝ) [SFinite ρ] {B : Set ℝ} (hB : MeasurableSet B) :
    Measurable fun p : Fin 4 → ℝ => klSec ρ (psq p) B := by
  have e : (fun p : Fin 4 → ℝ => klSec ρ (psq p) B)
      = fun p => ∫⁻ s, B.indicator 1 (shell s (psq p)) * klWeight (psq p) s ∂ρ :=
    funext fun p => klSec_apply ρ (psq p) hB
  rw [e]
  exact (show Measurable fun q : (Fin 4 → ℝ) × ℝ =>
      B.indicator 1 (shell q.2 (psq q.1)) * klWeight (psq q.1) q.2 from
    ((measurable_one.indicator hB).comp continuous_shellP.measurable).mul
      measurable_klW).lintegral_prod_right'

/-- **The sector mass** `|klSec ρ p²|`. DERIVED: no numeral. -/
def klMass (ρ : Measure ℝ) (p : Fin 4 → ℝ) : ℝ≥0∞ := klSec ρ (psq p) univ

/-- **The normalised shell sectors** `p ↦ |klSec ρ p²|⁻¹ · klSec ρ p²`. DERIVED: no numeral. -/
def klNorm (ρ : Measure ℝ) [IsFiniteMeasure ρ] : Kernel (Fin 4 → ℝ) ℝ where
  toFun p := (klMass ρ p)⁻¹ • klSec ρ (psq p)
  measurable' := Measure.measurable_of_measurable_coe _ fun B hB => by
    show Measurable fun p => ((klMass ρ p)⁻¹ • klSec ρ (psq p)) B
    simp only [Measure.smul_apply, smul_eq_mul]
    exact (measurable_klSec_apply ρ MeasurableSet.univ).inv.mul (measurable_klSec_apply ρ hB)

/-- DERIVED: no numeral. -/
theorem klNorm_apply (ρ : Measure ℝ) [IsFiniteMeasure ρ] (p : Fin 4 → ℝ) :
    klNorm ρ p = (klMass ρ p)⁻¹ • klSec ρ (psq p) := rfl

/-- DERIVED: `1` the unit mass. -/
theorem inv_mul_self_le_one (M : ℝ≥0∞) : M⁻¹ * M ≤ 1 := by
  rcases eq_or_ne M 0 with h0 | h0
  · simp [h0]
  rcases eq_or_ne M ⊤ with ht | ht
  · simp [ht]
  · exact (ENNReal.inv_mul_cancel h0 ht).le

/-- DERIVED: `1` the unit mass. -/
instance (ρ : Measure ℝ) [IsFiniteMeasure ρ] : IsFiniteKernel (klNorm ρ) :=
  ⟨⟨1, ENNReal.one_lt_top, fun p => by
    rw [klNorm_apply, Measure.smul_apply, smul_eq_mul]
    exact inv_mul_self_le_one _⟩⟩

/-- **The joint measure on a rectangle**: `klJoint τ ρ g (B × A) = ∫_A g(p) klSec ρ p² (B) dλ`.
DERIVED: no numeral. -/
theorem klJoint_rect (τ : Fin 4) (ρ : Measure ℝ) [IsFiniteMeasure ρ] {g : (Fin 4 → ℝ) → ℝ≥0}
    (hg : Measurable g) {A : Set (Fin 4 → ℝ)} {B : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    klJoint τ ρ g (B ×ˢ A) = ∫⁻ p in A, (g p : ℝ≥0∞) * klSec ρ (psq p) B ∂(lam τ) := by
  have hS : MeasurableSet (klMap ⁻¹' (B ×ˢ A)) := measurable_klMap (hB.prod hA)
  rw [klJoint, Measure.map_apply measurable_klMap (hB.prod hA), withDensity_apply _ hS,
    ← lintegral_indicator hS,
    lintegral_prod _ ((measurable_klDens' hg).indicator hS).aemeasurable, ← lintegral_indicator hA]
  refine lintegral_congr fun p => ?_
  by_cases hp : p ∈ A
  · rw [indicator_of_mem hp]
    show _ = (g p : ℝ≥0∞) * klSec ρ (psq p) B
    rw [klSec_apply ρ _ hB, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    refine lintegral_congr fun s => ?_
    by_cases hs : shell s (psq p) ∈ B <;> simp [Set.indicator_apply, klMap, klDens, hp, hs]
  · rw [indicator_of_notMem hp]
    have h0 : ∀ s, (klMap ⁻¹' (B ×ˢ A)).indicator (klDens g) (p, s) = 0 := fun s => by
      simp [Set.indicator_apply, klMap, hp]
    simp only [h0, lintegral_zero]

/-- DERIVED: no numeral. -/
theorem measurable_gMass (ρ : Measure ℝ) [IsFiniteMeasure ρ] {g : (Fin 4 → ℝ) → ℝ≥0}
    (hg : Measurable g) : Measurable fun p => (g p : ℝ≥0∞) * klMass ρ p :=
  hg.coe_nnreal_ennreal.mul (measurable_klSec_apply ρ MeasurableSet.univ)

/-- DERIVED: no numeral. -/
theorem kl_algebra {a M K : ℝ≥0∞} (hK : K ≤ M) (h : a * M ≠ ⊤) : a * M * (M⁻¹ * K) = a * K := by
  rcases eq_or_ne M 0 with h0 | h0
  · have hK0 : K = 0 := nonpos_iff_eq_zero.mp (hK.trans_eq h0)
    simp [h0, hK0]
  rcases eq_or_ne M ⊤ with ht | ht
  · have ha : a = 0 := by
      by_contra ha
      exact h (by rw [ht, ENNReal.mul_top ha])
    simp [ha]
  · rw [mul_assoc, ← mul_assoc M, ENNReal.mul_inv_cancel h0 ht, one_mul]

/-- **The superposition disintegrates into the normalised shell sectors**:
`(klJoint τ ρ g).swap = (g |klSec ρ p²| λ) ⊗ₘ klNorm ρ`, when the momentum marginal is finite.
DERIVED: no numeral. -/
theorem klJoint_swap (τ : Fin 4) (ρ : Measure ℝ) [IsFiniteMeasure ρ] {g : (Fin 4 → ℝ) → ℝ≥0}
    (hg : Measurable g)
    (hfin : (lam τ).withDensity (fun p => (g p : ℝ≥0∞) * klMass ρ p) univ ≠ ⊤) :
    (klJoint τ ρ g).map Prod.swap
      = (lam τ).withDensity (fun p => (g p : ℝ≥0∞) * klMass ρ p) ⊗ₘ klNorm ρ := by
  haveI : IsFiniteMeasure ((lam τ).withDensity (fun p => (g p : ℝ≥0∞) * klMass ρ p)) :=
    ⟨lt_top_iff_ne_top.mpr hfin⟩
  have hlt : ∀ᵐ p ∂(lam τ), (g p : ℝ≥0∞) * klMass ρ p < ⊤ := by
    refine ae_lt_top (measurable_gMass ρ hg) ?_
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hfin
  refine (Measure.ext_prod fun {A} {B} hA hB => ?_).symm
  rw [Measure.compProd_apply_prod hA hB, Measure.map_apply measurable_swap (hA.prod hB),
    preimage_swap_prod, klJoint_rect τ ρ hg hA hB,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_gMass ρ hg)
      ((klNorm ρ).measurable_coe hB) hA]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hlt] with p hp
  simp only [Pi.mul_apply, klNorm_apply, Measure.smul_apply, smul_eq_mul]
  exact kl_algebra (measure_mono (subset_univ B)) hp.ne

/-- **On the marginal, almost every sector mass is positive and finite.** DERIVED: `0` the zero
mass. -/
theorem ae_mass (τ : Fin 4) (ρ : Measure ℝ) [IsFiniteMeasure ρ] {g : (Fin 4 → ℝ) → ℝ≥0}
    (hg : Measurable g)
    (hfin : (lam τ).withDensity (fun p => (g p : ℝ≥0∞) * klMass ρ p) univ ≠ ⊤) :
    ∀ᵐ p ∂((lam τ).withDensity (fun p => (g p : ℝ≥0∞) * klMass ρ p)),
      klMass ρ p ≠ 0 ∧ klMass ρ p ≠ ⊤ := by
  have hlt : ∀ᵐ p ∂(lam τ), (g p : ℝ≥0∞) * klMass ρ p < ⊤ := by
    refine ae_lt_top (measurable_gMass ρ hg) ?_
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hfin
  rw [ae_withDensity_iff (measurable_gMass ρ hg)]
  filter_upwards [hlt] with p hp hne
  refine ⟨fun h0 => hne (by rw [h0, mul_zero]), fun ht => ?_⟩
  have ha : (g p : ℝ≥0∞) ≠ 0 := fun h => hne (by rw [h, zero_mul])
  exact hp.ne (by rw [ht, ENNReal.mul_top ha])

/-- **The normalised sectors have unit mass on the marginal.** DERIVED: `1` the unit mass. -/
theorem fst_compProd_klNorm (τ : Fin 4) (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {g : (Fin 4 → ℝ) → ℝ≥0} (hg : Measurable g)
    (hfin : (lam τ).withDensity (fun p => (g p : ℝ≥0∞) * klMass ρ p) univ ≠ ⊤) :
    ((lam τ).withDensity (fun p => (g p : ℝ≥0∞) * klMass ρ p) ⊗ₘ klNorm ρ).fst
      = (lam τ).withDensity (fun p => (g p : ℝ≥0∞) * klMass ρ p) := by
  haveI : IsFiniteMeasure ((lam τ).withDensity (fun p => (g p : ℝ≥0∞) * klMass ρ p)) :=
    ⟨lt_top_iff_ne_top.mpr hfin⟩
  ext A hA
  rw [Measure.fst_apply hA, ← Set.prod_univ, Measure.compProd_apply_prod hA MeasurableSet.univ,
    ← setLIntegral_one (μ := (lam τ).withDensity (fun p => (g p : ℝ≥0∞) * klMass ρ p)) A]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [ae_mass τ ρ hg hfin] with p hp
  rw [klNorm_apply, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hp.1 hp.2

section Vector

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {τ : Fin 4} (J : JointData H (spatial τ))

/-- **A Källén–Lehmann joint measure has Källén–Lehmann sectors**: `nu J u = klJoint τ ρ g` ⇒
`SectorKL J u ρ g`. DERIVED: no numeral. -/
theorem sectorKL_of_klJoint (u : H) (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {g : (Fin 4 → ℝ) → ℝ≥0} (hg : Measurable g) (hKL : nu J u = klJoint τ ρ g) :
    SectorKL J u ρ g := by
  have hfin : (lam τ).withDensity (fun p => (g p : ℝ≥0∞) * klMass ρ p) univ ≠ ⊤ := by
    have e : (lam τ).withDensity (fun p => (g p : ℝ≥0∞) * klMass ρ p) univ
        = nu J u (univ ×ˢ univ) := by
      rw [hKL, klJoint_rect τ ρ hg MeasurableSet.univ MeasurableSet.univ,
        withDensity_apply _ MeasurableSet.univ]
      rfl
    rw [e]
    exact measure_ne_top _ _
  have hswap : nuSwap J u
      = (lam τ).withDensity (fun p => (g p : ℝ≥0∞) * klMass ρ p) ⊗ₘ klNorm ρ := by
    unfold nuSwap
    rw [hKL]
    exact klJoint_swap τ ρ hg hfin
  have hfst : momMarg J u = (lam τ).withDensity (fun p => (g p : ℝ≥0∞) * klMass ρ p) := by
    unfold momMarg
    rw [hswap]
    exact fst_compProd_klNorm τ ρ hg hfin
  refine And.intro hfst ?_
  have hu := sector_unique J u (klNorm ρ) (by rw [hfst, ← hswap])
  have hae : ∀ᵐ p ∂(momMarg J u), klMass ρ p ≠ 0 ∧ klMass ρ p ≠ ⊤ := by
    rw [hfst]; exact ae_mass τ ρ hg hfin
  filter_upwards [hu, hae] with p hp hM
  show klMass ρ p • sector J u p = klSec ρ (psq p)
  rw [← hp, klNorm_apply, smul_smul, ENNReal.mul_inv_cancel hM.1 hM.2, one_smul]

/-- **Källén–Lehmann sectors make a Källén–Lehmann joint measure**: `SectorKL J u ρ g` ⇒
`nu J u = klJoint τ ρ g`. DERIVED: no numeral. -/
theorem klJoint_of_sectorKL (u : H) (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {g : (Fin 4 → ℝ) → ℝ≥0} (hg : Measurable g) (h : SectorKL J u ρ g) :
    nu J u = klJoint τ ρ g := by
  have hm := And.left h
  have hs := And.right h
  have hfin : (lam τ).withDensity (fun p => (g p : ℝ≥0∞) * klMass ρ p) univ ≠ ⊤ := by
    have e : (lam τ).withDensity (fun p => (g p : ℝ≥0∞) * klMass ρ p) = momMarg J u := hm.symm
    rw [e]
    exact measure_ne_top _ _
  have hae : ∀ᵐ p ∂(momMarg J u), klMass ρ p ≠ 0 ∧ klMass ρ p ≠ ⊤ := by
    have e : momMarg J u = (lam τ).withDensity (fun p => (g p : ℝ≥0∞) * klMass ρ p) := hm
    rw [e]; exact ae_mass τ ρ hg hfin
  have hk : sector J u =ᵐ[momMarg J u] klNorm ρ := by
    filter_upwards [hs, hae] with p hp hM
    rw [klNorm_apply]
    have hp' : klMass ρ p • sector J u p = klSec ρ (psq p) := hp
    rw [← hp', smul_smul, ENNReal.inv_mul_cancel hM.1 hM.2, one_smul]
  have hns : nuSwap J u = (klJoint τ ρ g).map Prod.swap := by
    rw [← momMarg_compProd_sector J u, Measure.compProd_congr hk, klJoint_swap τ ρ hg hfin]
    have e : momMarg J u = (lam τ).withDensity (fun p => (g p : ℝ≥0∞) * klMass ρ p) := hm
    rw [e]
  rw [← map_swap_nuSwap J u, hns, Measure.map_map measurable_swap measurable_swap]
  have e : (Prod.swap ∘ Prod.swap : ℝ × (Fin 4 → ℝ) → ℝ × (Fin 4 → ℝ)) = id :=
    funext fun q => Prod.swap_swap q
  rw [e, Measure.map_id]

/-- **The template is the sector form**: `KLJointRep J u ρ ↔ ∃ g` continuous, `g(0) ≠ 0`,
`SectorKL J u ρ g`. DERIVED: `0` the zero momentum. -/
theorem klJointRep_iff (u : H) (ρ : Measure ℝ) [IsFiniteMeasure ρ] :
    KLJointRep J u ρ ↔ ∃ g : (Fin 4 → ℝ) → ℝ≥0, Continuous g ∧ g 0 ≠ 0 ∧ SectorKL J u ρ g := by
  unfold KLJointRep
  constructor
  · rintro ⟨g, hg, hg0, hKL⟩
    exact ⟨g, hg, hg0, sectorKL_of_klJoint J u ρ hg.measurable hKL⟩
  · rintro ⟨g, hg, hg0, hS⟩
    exact ⟨g, hg, hg0, klJoint_of_sectorKL J u ρ hg.measurable hS⟩

/-- **The template from the marginal density and the per-sector Laplace match.** DERIVED: `0` the
zero momentum, the bottom of the rates and the sign of the time. -/
theorem klJointRep_of_laplace (u : H) (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {g : (Fin 4 → ℝ) → ℝ≥0} (hg : Continuous g) (hg0 : g 0 ≠ 0)
    (hm : momMarg J u = (lam τ).withDensity (fun p => (g p : ℝ≥0∞) * klSec ρ (psq p) univ))
    (hL : ∀ᵐ p ∂(momMarg J u), klSec ρ (psq p) univ ≠ ⊤ ∧ ∀ t : ℝ, 0 < t →
      ∫ s, Real.exp (-(t * s)) ∂(klSec ρ (psq p))
        = (klSec ρ (psq p) univ).toReal * secLaplace J u t p) :
    KLJointRep J u ρ :=
  (klJointRep_iff J u ρ).mpr ⟨g, hg, hg0, And.intro hm (sector_kl_of_laplace J u ρ hL)⟩

end Vector

/-! ## 3. The Clay read through the sectors -/

/-- **The Clay read under the sector form**: `clay_zero_momentum_kl` with `nu J u = klJoint τ ρ g`
replaced by `SectorKL J u ρ g`. DERIVED: `0` the zero momentum and the signs; `1` the unit step. -/
theorem clay_zero_momentum_sectorKL {τ : Fin 4} (X : OSDataS) (J : JointData X.H (spatial τ))
    (hJ : J.a = X.time 1) (u : X.H) (hu : inner ℂ X.vac u = 0) {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hρ0 : ρ (Iic 0) = 0) {g : (Fin 4 → ℝ) → ℝ≥0} (hg : Continuous g) (hg0 : g 0 ≠ 0) {M2 : ℝ}
    (hb : SpecBottom ρ M2) (hS : SectorKL J u ρ g) :
    ZeroDensity τ (nu J u) (klSec (g 0 • ρ) 0)
      ∧ klSec (g 0 • ρ) 0 (Iio X.gap) = 0 ∧ 0 < M2 ∧ X.gap ≤ Real.sqrt M2
      ∧ SpecBottom (klSec (g 0 • ρ) 0) (Real.sqrt M2)
      ∧ ∀ p2, 0 ≤ p2 → Real.sqrt p2 < shell M2 p2 :=
  clay_zero_momentum_kl X J hJ u hu hρ0 hg hg0 hb (klJoint_of_sectorKL J u ρ hg.measurable hS)

/-- **The Clay read under the marginal density and the per-sector Laplace match.** DERIVED: `0` the
zero momentum, the bottom of the rates and the signs; `1` the unit step. -/
theorem clay_zero_momentum_laplace {τ : Fin 4} (X : OSDataS) (J : JointData X.H (spatial τ))
    (hJ : J.a = X.time 1) (u : X.H) (hu : inner ℂ X.vac u = 0) {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hρ0 : ρ (Iic 0) = 0) {g : (Fin 4 → ℝ) → ℝ≥0} (hg : Continuous g) (hg0 : g 0 ≠ 0) {M2 : ℝ}
    (hb : SpecBottom ρ M2)
    (hm : momMarg J u = (lam τ).withDensity (fun p => (g p : ℝ≥0∞) * klSec ρ (psq p) univ))
    (hL : ∀ᵐ p ∂(momMarg J u), klSec ρ (psq p) univ ≠ ⊤ ∧ ∀ t : ℝ, 0 < t →
      ∫ s, Real.exp (-(t * s)) ∂(klSec ρ (psq p))
        = (klSec ρ (psq p) univ).toReal * secLaplace J u t p) :
    ZeroDensity τ (nu J u) (klSec (g 0 • ρ) 0)
      ∧ klSec (g 0 • ρ) 0 (Iio X.gap) = 0 ∧ 0 < M2 ∧ X.gap ≤ Real.sqrt M2
      ∧ SpecBottom (klSec (g 0 • ρ) 0) (Real.sqrt M2)
      ∧ ∀ p2, 0 ≤ p2 → Real.sqrt p2 < shell M2 p2 :=
  clay_zero_momentum_sectorKL X J hJ u hu hρ0 hg hg0 hb
    (And.intro hm (sector_kl_of_laplace J u ρ hL))

end

end MassGap.LorentzStep

#print axioms MassGap.LorentzStep.free_mixed_fourier
#print axioms MassGap.LorentzStep.free_propagator_fourier
#print axioms MassGap.LorentzStep.klSec_laplace
#print axioms MassGap.LorentzStep.free_laplace
#print axioms MassGap.LorentzStep.klSec_apply
#print axioms MassGap.LorentzStep.measurable_klW
#print axioms MassGap.LorentzStep.measurable_klDens'
#print axioms MassGap.LorentzStep.measurable_klSec_apply
#print axioms MassGap.LorentzStep.klNorm_apply
#print axioms MassGap.LorentzStep.inv_mul_self_le_one
#print axioms MassGap.LorentzStep.klJoint_rect
#print axioms MassGap.LorentzStep.measurable_gMass
#print axioms MassGap.LorentzStep.kl_algebra
#print axioms MassGap.LorentzStep.klJoint_swap
#print axioms MassGap.LorentzStep.ae_mass
#print axioms MassGap.LorentzStep.fst_compProd_klNorm
#print axioms MassGap.LorentzStep.sectorKL_of_klJoint
#print axioms MassGap.LorentzStep.klJoint_of_sectorKL
#print axioms MassGap.LorentzStep.klJointRep_iff
#print axioms MassGap.LorentzStep.klJointRep_of_laplace
#print axioms MassGap.LorentzStep.clay_zero_momentum_sectorKL
#print axioms MassGap.LorentzStep.clay_zero_momentum_laplace
