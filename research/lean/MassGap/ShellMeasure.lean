import Mathlib
import MassGap.ContinuumTimeGroup
import MassGap.BandShell

/-!
# MassGap.ShellMeasure — the time correlator of a reconstruction is a Laplace transform

`BandShell.shell_rate` reads the rate of a momentum sector once that sector is in Källén–Lehmann form
`∫ e^{−τ √(s + p²)} dρ_p(s)`. This module supplies the Euclidean half of that form, the half that needs
no Minkowski continuation: the time correlator of any vector under the tree's reconstructed time
semigroup is the Laplace transform of a finite positive measure on `[0, ∞)`, the measure being the
vector's own spectral measure. It then states the Källén–Lehmann step as one named template, proves
that a sector of that form feeds `shell_rate`, and load-tests both sides. Declarations are in the
namespace `MassGap.ShellMeasure`.

## What the tree has for the reconstruction

* `ContinuumTimeGroup`: the GNS space `FlowH` of the flowed reflection form, the positive self-adjoint
  transfer `stepT 0` with spectrum in `[0, 1]`, the real powers `powT a s = cfc (x ↦ x ^ s) a` and the
  time translations `timeT t = powT (stepT 0) (t / a₀)`, `a₀ = dySpacing N 0`.
* `ObserverOSReconstructionS.OSDataS`: Schwinger functions on `𝓢(E4)` (OS0, OS3) and, as data, a
  Hilbert space, vacuum, a semigroup of positive self-adjoint contractions and a gap. No spatial
  translations, momentum or joint spectrum of `(H, P)`.
* `FlowCovN.FlowCovLim ↔ CovC`: `O(4)` covariance of the continuum composite Schwinger functions.
* Mathlib (at this pin) has the continuous functional calculus and the Riesz–Markov–Kakutani theorem
  (`RealRMK.rieszMeasure`), but no spectral measure of an operator, no Bernstein–Widder theorem
  (`AbsolutelyMonotoneOn` is defined, the representation theorem is not) and no Källén–Lehmann
  theorem.

## 1. The spectral measure of a vector (proved)

For a self-adjoint bounded operator `a` with spectrum in `[0, 1]` and a vector `u`, `stateMap a u` is the
positive functional `f ↦ Re ⟪u, f(a) u⟫` on `C([0, 1])`, and `vecMeasure a u` its Riesz–Markov–Kakutani
measure. The identity below is stated without a self-adjointness hypothesis; for an operator that is not
self-adjoint `cfc` is `0` and both sides are `0`.

* `re_inner_cfc_eq_integral`: `Re ⟪u, g(a) u⟫ = ∫ g dμ_u` for every continuous `g : ℝ → ℝ`. This is the
  spectral theorem for one vector, proved from the continuous functional calculus and RMK.

## 2. The Laplace form of the time correlator (proved)

* `rateMeasure a u`: the push-forward of `μ_u` restricted to `(0, 1]` under `λ ↦ −log λ`, a finite
  measure on the rates `E ≥ 0` (`rateMeasure_Iio`). The rates are read from the vector; nothing is
  chosen.
* `re_inner_powT_eq_laplace`: `Re ⟪u, a^τ u⟫ = ∫ e^{−τE} d(rateMeasure a u)(E)` for `τ > 0`. The mass of
  `μ_u` at `λ = 0` (the kernel of `a`) contributes `0^τ = 0` and drops out.
* `LaplaceRep C`: `C` is, on `τ > 0`, the Laplace transform of a finite measure on `[0, ∞)`.
  `powT_laplaceRep`: every vector correlator of a positive contraction is `LaplaceRep`.
* `flow_time_laplace`: on the tree's reconstruction, `Re ⟪u, timeT t u⟫ = ∫ e^{−(t/a₀) E} dσ_u` for
  `t > 0`. This is the momentum-blind form: it is the Laplace representation of every vector of `FlowH`,
  in particular of a momentum-`p` vector once one is built.

## 3. Reflection positivity and the representation (proved, one direction)

* `ReflPos C`: `Σᵢⱼ cᵢ cⱼ C(tᵢ + tⱼ) ≥ 0` for every finite family of positive times; this is OS2 for a
  time correlator.
* `laplace_reflPos`: `LaplaceRep C → ReflPos C` (the elementary half of Bernstein–Widder:
  the double sum is `∫ (Σᵢ cᵢ e^{−tᵢE})² dσ`).
* `ReflPos.gram_two`: the Gram form at `(C(a + b), −C(2a))`, which is the `2 × 2` Gram minor times
  `C(2a)`: `C(2a) (C(2a) C(2b) − C(a + b)²) ≥ 0`.
* The converse, `ReflPos` with continuity and boundedness implies `LaplaceRep`, is the Bernstein–Widder
  theorem, proved for a bare function in `BernsteinWidder.bernsteinWidder`. Here its content is proved for every
  correlator that is already a vector correlator of a positive contraction semigroup (`powT_laplaceRep`).
  Identifying a momentum-`p` Schwinger function with such a vector correlator is not built here.

## 4. The Källén–Lehmann step (template, stated; connection proved)

* `klWeight p2 s = 1/(2 √(s + p²))`, `KallenLehmann σ ρ`: for every `p² ≥ 0` the rate measure of the
  momentum-`p` sector is `σ_p = shell(·, p²)_* (ρ / (2 shell))`, one `s`-measure `ρ` for all `p`.
* `KLTemplate σ`: such a finite `ρ` exists. This is the one named template hypothesis of this module.
  What it needs, plainly, none of it formalised: (i) spatial translations on the reconstruction space,
  a strongly continuous unitary group commuting with the time semigroup (OS reconstruction from the
  translation covariance of the Schwinger functions), and a momentum-`p` vector `u_p` with
  `C_p(τ) = ⟪u_p, e^{−τH} u_p⟫`; with these, §2 gives each `σ_p`; (ii) the joint spectral measure of
  `(H, P)` and its invariance under the Lorentz group, which is OS-II applied to `CovC` (the `O(4)`
  covariance, analytically continued); a Lorentz-invariant measure on the forward cone is a
  superposition of hyperboloids `E = √(s + p²)` with one `ρ`, which is Källén–Lehmann. Finiteness of
  `ρ` holds for time-smeared composites and is part of the template.
  The single-`ρ` form is the scalar (Lorentz-singlet) one; a composite with spin or tensor structure needs
  one `ρ` per invariant structure, which this template does not cover. `ρ` is also supported on `s ≥ 0`,
  which `KallenLehmann` does not itself require.
* `shell_rate_of_kl`: if the sector correlator is the Laplace transform of `σ_p` and `σ` has
  Källén–Lehmann form with `SpecBottom ρ M2`, `M2 + p² > 0`, then
  `−log C_p(τ)/τ → √(M2 + p²)`. This is `BandShell.shell_rate` applied to `ρ_p = ρ / (2 shell)`, whose
  bottom is the bottom of `ρ` (`specBottom_klDensity`).

## 5. Load tests (proved)

* Free field: `freeSector m2 p2 τ = e^{−τω}/(2ω)`, `ω = √(m² + p²)`, is `LaplaceRep` (`free_laplaceRep`)
  with rate measure `freeRate = δ_ω/(2ω)`, and `freeRate` has Källén–Lehmann form with `ρ = δ_{m²}`
  (`free_kallenLehmann`); `free_sector_rate` reads `√(m² + p²)` through `shell_rate_of_kl`.
* A non-reflection-positive kernel: `bumpKernel τ = τ e^{−τ}` violates the `2 × 2` Gram minor at the
  times `1/4, 1` (`bumpKernel_not_reflPos`), so it has no Laplace representation
  (`bumpKernel_not_laplace`).

Foundational footprint only (`#print axioms` at the end).
-/

namespace MassGap.ShellMeasure

open Real Filter Topology MeasureTheory Set
open scoped CompactlySupported
open MassGap.BandShell (shell bandProfile SpecBottom shell_mono shell_nonneg shell_rate
  specBottom_dirac)
open MassGap.ContinuumTimeGroup (powT)

noncomputable section

/-! ## 1. The spectral measure of a vector -/

section Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **The clamp** of the line onto `[0, 1]`. DERIVED: `0`, `1` the ends of the spectrum interval. -/
def clamp (x : ℝ) : Icc (0 : ℝ) 1 := projIcc 0 1 zero_le_one x

/-- DERIVED: no numeral. -/
theorem continuous_clamp : Continuous clamp := continuous_projIcc (h := zero_le_one)

/-- **The vector state** `f ↦ Re ⟪u, f(a) u⟫` on `C([0, 1])`, as a linear map.
DERIVED: `0`, `1` the ends of the spectrum interval. -/
def stateLin (a : E →L[ℂ] E) (u : E) : C_c(Icc (0 : ℝ) 1, ℝ) →ₗ[ℝ] ℝ where
  toFun f := (inner ℂ u (cfc (fun x => f (clamp x)) a u)).re
  map_add' f g := by
    have hf : ContinuousOn (fun x => f (clamp x)) (spectrum ℝ a) :=
      (f.continuous.comp continuous_clamp).continuousOn
    have hg : ContinuousOn (fun x => g (clamp x)) (spectrum ℝ a) :=
      (g.continuous.comp continuous_clamp).continuousOn
    simp only [CompactlySupportedContinuousMap.add_apply]
    rw [cfc_add a _ _ hf hg, ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
  map_smul' c f := by
    have hf : ContinuousOn (fun x => f (clamp x)) (spectrum ℝ a) :=
      (f.continuous.comp continuous_clamp).continuousOn
    simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [cfc_const_mul c _ a hf, ContinuousLinearMap.smul_apply, ← Complex.coe_smul,
      inner_smul_right, Complex.re_ofReal_mul]

/-- **The vector state is positive**: `f ≥ 0` gives `f(a) ≥ 0`, so `Re ⟪u, f(a) u⟫ ≥ 0`.
DERIVED: `0` the order's bottom; `1` the top of the interval. -/
def stateMap (a : E →L[ℂ] E) (u : E) : C_c(Icc (0 : ℝ) 1, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ (stateLin a u) fun f hf => by
    have h0 : 0 ≤ cfc (fun x => f (clamp x)) a := cfc_nonneg fun x _ => by
      simpa using (CompactlySupportedContinuousMap.le_def.mp hf (clamp x))
    have h1 := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp h0).re_inner_nonneg_right u
    show 0 ≤ (inner ℂ u (cfc (fun x => f (clamp x)) a u)).re
    simpa using h1

/-- **The spectral measure of `u`** for `a`: the Riesz–Markov–Kakutani measure of the vector state.
DERIVED: `0`, `1` the ends of the spectrum interval. -/
def vecMeasure (a : E →L[ℂ] E) (u : E) : Measure (Icc (0 : ℝ) 1) :=
  RealRMK.rieszMeasure (stateMap a u)

instance (a : E →L[ℂ] E) (u : E) : IsFiniteMeasure (vecMeasure a u) := by
  unfold vecMeasure; infer_instance

/-- **The spectral theorem for one vector**: `Re ⟪u, g(a) u⟫ = ∫ g dμ_u` for continuous `g`, when the
spectrum of `a` lies in `[0, 1]`. DERIVED: `0`, `1` the ends of the spectrum interval. -/
theorem re_inner_cfc_eq_integral {a : E →L[ℂ] E} (hsp : spectrum ℝ a ⊆ Icc 0 1) (u : E)
    {g : ℝ → ℝ} (hg : Continuous g) :
    (inner ℂ u (cfc g a u)).re = ∫ x, g x.1 ∂(vecMeasure a u) := by
  let G : C_c(Icc (0 : ℝ) 1, ℝ) :=
    ⟨⟨fun x => g x.1, hg.comp continuous_subtype_val⟩, HasCompactSupport.of_compactSpace _⟩
  have h1 := RealRMK.integral_rieszMeasure (stateMap a u) G
  have h2 : cfc (fun x => G (clamp x)) a = cfc g a := cfc_congr fun x hx => by
    show g (clamp x).1 = g x
    rw [clamp, projIcc_of_mem zero_le_one (hsp hx)]
  calc (inner ℂ u (cfc g a u)).re = (inner ℂ u (cfc (fun x => G (clamp x)) a u)).re := by rw [h2]
    _ = stateMap a u G := rfl
    _ = ∫ x, G x ∂(vecMeasure a u) := h1.symm
    _ = ∫ x, g x.1 ∂(vecMeasure a u) := rfl

/-! ## 2. The Laplace form of the time correlator -/

/-- **The rate measure** of `u`: the spectral measure on `(0, 1]` pushed to the rates `E = −log λ`.
DERIVED: `0` the excluded kernel point. -/
def rateMeasure (a : E →L[ℂ] E) (u : E) : Measure ℝ :=
  ((vecMeasure a u).restrict {x | 0 < x.1}).map (fun x => -Real.log x.1)

instance (a : E →L[ℂ] E) (u : E) : IsFiniteMeasure (rateMeasure a u) := by
  unfold rateMeasure; infer_instance

/-- DERIVED: no numeral. -/
theorem measurable_rate : Measurable (fun x : Icc (0 : ℝ) 1 => -Real.log x.1) :=
  (Real.measurable_log.comp measurable_subtype_coe).neg

/-- **The rates are non-negative**: `−log λ ≥ 0` on `(0, 1]`. DERIVED: `0` the sign. -/
theorem rateMeasure_Iio (a : E →L[ℂ] E) (u : E) : rateMeasure a u (Iio 0) = 0 := by
  unfold rateMeasure
  rw [Measure.map_apply measurable_rate measurableSet_Iio]
  have : (fun x : Icc (0 : ℝ) 1 => -Real.log x.1) ⁻¹' Iio 0 = ∅ := by
    ext x
    simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false, not_lt]
    exact neg_nonneg.mpr (Real.log_nonpos x.2.1 x.2.2)
  rw [this, measure_empty]

/-- **The time correlator is a Laplace transform**: `Re ⟪u, a^τ u⟫ = ∫ e^{−τE} dσ_u(E)` for `τ > 0`.
DERIVED: `0` the sign of `τ` and the kernel point. -/
theorem re_inner_powT_eq_laplace {a : E →L[ℂ] E} (hsp : spectrum ℝ a ⊆ Icc 0 1) (u : E) {τ : ℝ}
    (hτ : 0 < τ) :
    (inner ℂ u (powT a τ u)).re = ∫ E, Real.exp (-(τ * E)) ∂(rateMeasure a u) := by
  have hc : Continuous (fun x : ℝ => x ^ τ) := Real.continuous_rpow_const hτ.le
  have hrep := re_inner_cfc_eq_integral hsp u hc
  beta_reduce at hrep
  rw [show powT a τ = cfc (fun x : ℝ => x ^ τ) a from rfl, hrep]
  have hS : MeasurableSet {x : Icc (0 : ℝ) 1 | 0 < x.1} :=
    measurableSet_lt measurable_const measurable_subtype_coe
  have hint : Integrable (fun x : Icc (0 : ℝ) 1 => x.1 ^ τ) (vecMeasure a u) :=
    (hc.comp continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← integral_add_compl hS hint]
  have h0 : ∫ x in {x : Icc (0 : ℝ) 1 | 0 < x.1}ᶜ, x.1 ^ τ ∂(vecMeasure a u) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun x hx => by
      have hx0 : x.1 = 0 := le_antisymm (not_lt.mp hx) x.2.1
      rw [hx0, Real.zero_rpow hτ.ne']
  rw [h0, add_zero, rateMeasure, integral_map measurable_rate.aemeasurable
    (by fun_prop : Continuous fun E : ℝ => Real.exp (-(τ * E))).aestronglyMeasurable]
  refine setIntegral_congr_fun hS fun x hx => ?_
  show x.1 ^ τ = Real.exp (-(τ * -Real.log x.1))
  rw [Real.rpow_def_of_pos hx]
  congr 1
  ring

/-- **The Laplace form**: on `τ > 0`, `C` is `∫ e^{−τE} dσ` for a finite `σ` on `[0, ∞)`.
DERIVED: `0` the sign of `τ` and the bottom of the rates. -/
def LaplaceRep (C : ℝ → ℝ) : Prop :=
  ∃ σ : Measure ℝ, IsFiniteMeasure σ ∧ σ (Iio 0) = 0 ∧
    ∀ τ, 0 < τ → C τ = ∫ E, Real.exp (-(τ * E)) ∂σ

/-- **Every vector correlator of a positive contraction is a Laplace transform.**
DERIVED: `0`, `1` the ends of the spectrum interval. -/
theorem powT_laplaceRep {a : E →L[ℂ] E} (hsp : spectrum ℝ a ⊆ Icc 0 1) (u : E) :
    LaplaceRep (fun τ => (inner ℂ u (powT a τ u)).re) :=
  ⟨rateMeasure a u, inferInstance, rateMeasure_Iio a u,
    fun _ hτ => re_inner_powT_eq_laplace hsp u hτ⟩

end Spectral

section Flow

open MassGap.ContinuumFlow MassGap.ContinuumTimeGroup MassGap.ContinuumSchwinger

variable {N : ℕ}

/-- **The tree's reconstruction**: every vector's time correlator under `timeT` is the Laplace transform
of its rate measure, at time `t / a₀`. DERIVED: `0` the reference step and the sign of `t`; `1` the
least colour count; `4` in `Fin 4` the spacetime dimension. -/
theorem flow_time_laplace (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4) {r : ℝ}
    (hpos : Φ.PosPreserving τ r) (u : FlowH hN Φ hB τ hpos) {t : ℝ} (ht : 0 < t) :
    (inner ℂ u (timeT hN Φ hB τ hpos t u)).re
      = ∫ E, Real.exp (-(t / dySpacing N 0 * E)) ∂(rateMeasure (stepT hN Φ hB τ hpos 0) u) := by
  unfold timeT
  exact re_inner_powT_eq_laplace (spectrum_stepT hN Φ hB τ hpos 0) u
    (div_pos ht (dySpacing_pos (Nat.one_le_iff_ne_zero.mpr hN) 0))

end Flow

/-! ## 3. Reflection positivity -/

/-- **Reflection positivity of a time correlator** (OS2 at fixed momentum): the Gram sums over positive
times are non-negative. DERIVED: `0` the sign. -/
def ReflPos (C : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (c t : Fin n → ℝ), (∀ i, 0 < t i) → 0 ≤ ∑ i, ∑ j, c i * c j * C (t i + t j)

/-- DERIVED: `0` the sign; `1` the bound. -/
theorem integrable_exp_of_Iio {σ : Measure ℝ} [IsFiniteMeasure σ] (h : σ (Iio 0) = 0) {τ : ℝ}
    (hτ : 0 ≤ τ) : Integrable (fun E => Real.exp (-(τ * E))) σ := by
  have hae : ∀ᵐ E ∂σ, 0 ≤ E := by
    rw [ae_iff]
    have : {E : ℝ | ¬ 0 ≤ E} = Iio 0 := by ext E; simp [not_le]
    rw [this]; exact h
  refine (integrable_const (1 : ℝ)).mono'
    (by fun_prop : Continuous fun E : ℝ => Real.exp (-(τ * E))).aestronglyMeasurable ?_
  filter_upwards [hae] with E hE
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith)

/-- **A Laplace transform is reflection positive**: the Gram sum is `∫ (Σᵢ cᵢ e^{−tᵢE})² dσ ≥ 0`.
DERIVED: `0` the sign; `2` the square. -/
theorem laplace_reflPos {C : ℝ → ℝ} (hC : LaplaceRep C) : ReflPos C := by
  obtain ⟨σ, hfin, h0, hrep⟩ := hC
  intro n c t ht
  have hpt : ∀ E : ℝ, (∑ i, c i * Real.exp (-(t i * E))) ^ 2
      = ∑ i, ∑ j, c i * c j * Real.exp (-((t i + t j) * E)) := by
    intro E
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show -((t i + t j) * E) = -(t i * E) + -(t j * E) by ring, Real.exp_add]
    ring
  have hij : ∀ i j, Integrable (fun E => c i * c j * Real.exp (-((t i + t j) * E))) σ :=
    fun i j => (integrable_exp_of_Iio h0 (add_pos (ht i) (ht j)).le).const_mul _
  have key : ∑ i, ∑ j, c i * c j * C (t i + t j)
      = ∫ E, (∑ i, c i * Real.exp (-(t i * E))) ^ 2 ∂σ := by
    simp_rw [hpt]
    rw [integral_finsetSum Finset.univ fun i _ => integrable_finsetSum Finset.univ fun j _ => hij i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum Finset.univ fun j _ => hij i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, hrep _ (add_pos (ht i) (ht j))]
  rw [key]
  exact integral_nonneg fun E => sq_nonneg _

/-- **The `2 × 2` Gram minor** of a reflection-positive correlator:
`C(2a) (C(2a) C(2b) − C(a + b)²) ≥ 0`. DERIVED: `0` the sign; `2` the number of times and the square. -/
theorem ReflPos.gram_two {C : ℝ → ℝ} (h : ReflPos C) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ C (a + a) * (C (a + a) * C (b + b) - C (a + b) ^ 2) := by
  have h2 := h 2 ![C (a + b), -C (a + a)] ![a, b] (fun i => by fin_cases i <;> simp [ha, hb])
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h2
  rw [add_comm b a] at h2
  nlinarith [h2]

/-! ## 4. The Källén–Lehmann step -/

/-- DERIVED: no numeral. -/
theorem measurable_shell (p2 : ℝ) : Measurable (fun s => shell s p2) :=
  (Real.continuous_sqrt.comp (continuous_id.add continuous_const)).measurable

/-- **The relativistic density** `1/(2 √(s + p²))`. DERIVED: `1` the numerator; `2` the two roots
`±E` of the mass shell. -/
def klWeight (p2 s : ℝ) : ENNReal := ENNReal.ofReal (1 / (2 * shell s p2))

/-- DERIVED: `1`, `2` as in `klWeight`. -/
theorem measurable_klWeight (p2 : ℝ) : Measurable (klWeight p2) :=
  ENNReal.measurable_ofReal.comp (((measurable_shell p2).const_mul 2).const_div 1)

/-- **Källén–Lehmann form** of a family of sector rate measures: one `s`-measure `ρ` gives every
momentum sector, `σ_p = shell(·, p²)_* (ρ / (2 shell))`. DERIVED: `0` the sign of `p²`. -/
def KallenLehmann (σ : ℝ → Measure ℝ) (ρ : Measure ℝ) : Prop :=
  ∀ p2, 0 ≤ p2 → σ p2 = (ρ.withDensity (klWeight p2)).map (fun s => shell s p2)

/-- **The Källén–Lehmann template** (a named hypothesis, not discharged here): a finite `ρ` exists.
DERIVED: no numeral. -/
def KLTemplate (σ : ℝ → Measure ℝ) : Prop :=
  ∃ ρ : Measure ℝ, IsFiniteMeasure ρ ∧ KallenLehmann σ ρ

/-- **The density keeps the bottom and finiteness**: with `M2 + p² > 0`, `ρ / (2 shell)` is finite and
has the bottom of `ρ`. DERIVED: `0` the signs; `1`, `2` as in `klWeight`. -/
theorem specBottom_klDensity {ρ : Measure ℝ} [IsFiniteMeasure ρ] {M2 p2 : ℝ} (hb : SpecBottom ρ M2)
    (hM : 0 < M2 + p2) :
    IsFiniteMeasure (ρ.withDensity (klWeight p2)) ∧ SpecBottom (ρ.withDensity (klWeight p2)) M2 := by
  have hE0 : 0 < shell M2 p2 := Real.sqrt_pos.mpr hM
  have hshell : ∀ s, M2 ≤ s → 0 < shell s p2 := fun s hs => lt_of_lt_of_le hE0 (shell_mono p2 hs)
  have hbound : ∀ s, M2 ≤ s → klWeight p2 s ≤ ENNReal.ofReal (1 / (2 * shell M2 p2)) := by
    intro s hs
    exact ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le (by positivity)
      (by linarith [shell_mono p2 hs]))
  have hae : ∀ᵐ s ∂ρ, M2 ≤ s := by
    rw [ae_iff]
    have : {s : ℝ | ¬ M2 ≤ s} = Iio M2 := by ext s; simp [not_le]
    rw [this]; exact hb.1
  refine ⟨⟨?_⟩, (withDensity_absolutelyContinuous ρ _) hb.1, fun ε hε => ?_⟩
  · rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc ∫⁻ s, klWeight p2 s ∂ρ ≤ ∫⁻ _s, ENNReal.ofReal (1 / (2 * shell M2 p2)) ∂ρ :=
          lintegral_mono_ae (hae.mono fun s hs => hbound s hs)
      _ = ENNReal.ofReal (1 / (2 * shell M2 p2)) * ρ univ := lintegral_const _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  · have hEe : 0 < shell (M2 + ε) p2 := hshell _ (by linarith)
    rw [withDensity_apply _ measurableSet_Ico]
    calc (0 : ENNReal) < ENNReal.ofReal (1 / (2 * shell (M2 + ε) p2)) * ρ (Ico M2 (M2 + ε)) :=
          ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne' (hb.2 ε hε).ne'
      _ = ∫⁻ _s in Ico M2 (M2 + ε), ENNReal.ofReal (1 / (2 * shell (M2 + ε) p2)) ∂ρ :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ s in Ico M2 (M2 + ε), klWeight p2 s ∂ρ :=
          setLIntegral_mono (measurable_klWeight p2) fun s hs =>
            ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le (by linarith [hshell s hs.1])
              (by linarith [shell_mono p2 hs.2.le]))

/-- **A sector of Källén–Lehmann form feeds `shell_rate`**: its read tends to `√(M2 + p²)`.
DERIVED: `0` the signs and the sign of `τ`. -/
theorem shell_rate_of_kl {σ : ℝ → Measure ℝ} {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hkl : KallenLehmann σ ρ) {M2 p2 : ℝ} (hb : SpecBottom ρ M2) (hp : 0 ≤ p2) (hM : 0 < M2 + p2)
    {C : ℝ → ℝ} (hC : ∀ τ, 0 < τ → C τ = ∫ E, Real.exp (-(τ * E)) ∂(σ p2)) :
    Tendsto (fun τ => -Real.log (C τ) / τ) atTop (𝓝 (shell M2 p2)) := by
  obtain ⟨hfin, hb'⟩ := specBottom_klDensity hb hM
  have hCeq : ∀ τ, 0 < τ → C τ = bandProfile (ρ.withDensity (klWeight p2)) p2 τ := by
    intro τ hτ
    rw [hC τ hτ, hkl p2 hp, integral_map (measurable_shell p2).aemeasurable
      (by fun_prop : Continuous fun E : ℝ => Real.exp (-(τ * E))).aestronglyMeasurable]
    rfl
  refine (shell_rate hb' hM.le).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with τ hτ
  rw [hCeq τ hτ]

/-! ## 5. Load tests -/

/-- **The free momentum-`p` sector** `e^{−τω}/(2ω)`, `ω = √(m² + p²)`. DERIVED: `2` as in `klWeight`. -/
def freeSector (m2 p2 τ : ℝ) : ℝ := Real.exp (-(τ * shell m2 p2)) / (2 * shell m2 p2)

/-- **Its rate measure** `δ_ω/(2ω)`. DERIVED: `1`, `2` as in `klWeight`. -/
def freeRate (m2 p2 : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 / (2 * shell m2 p2)) • Measure.dirac (shell m2 p2)

instance (m2 p2 : ℝ) : IsFiniteMeasure (freeRate m2 p2) :=
  ⟨by simp [freeRate, ENNReal.ofReal_lt_top]⟩

/-- **The free sector is a Laplace transform.** DERIVED: `0` the sign; `1`, `2` as in `klWeight`. -/
theorem free_laplaceRep (m2 p2 : ℝ) : LaplaceRep (freeSector m2 p2) := by
  have hω : ¬ shell m2 p2 < 0 := not_lt.mpr (shell_nonneg m2 p2)
  refine ⟨freeRate m2 p2, inferInstance, by simp [freeRate, hω], fun τ _ => ?_⟩
  have hw : 0 ≤ 1 / (2 * shell m2 p2) := by have := shell_nonneg m2 p2; positivity
  rw [freeRate, integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hw, smul_eq_mul,
    freeSector]
  ring

/-- **The free sector has Källén–Lehmann form** with `ρ = δ_{m²}`. DERIVED: no numeral. -/
theorem free_kallenLehmann (m2 : ℝ) : KallenLehmann (freeRate m2) (Measure.dirac m2) := by
  intro p2 _
  rw [dirac_withDensity, Measure.map_smul, Measure.map_dirac' (measurable_shell p2)]
  rfl

/-- **The free sector's read through the Källén–Lehmann connection** is `√(m² + p²)`.
DERIVED: `0` the signs. -/
theorem free_sector_rate {m2 p2 : ℝ} (hp : 0 ≤ p2) (hM : 0 < m2 + p2) :
    Tendsto (fun τ => -Real.log (freeSector m2 p2 τ) / τ) atTop (𝓝 (shell m2 p2)) := by
  refine shell_rate_of_kl (free_kallenLehmann m2) (specBottom_dirac m2) hp hM fun τ _ => ?_
  have hw : 0 ≤ 1 / (2 * shell m2 p2) := by have := shell_nonneg m2 p2; positivity
  rw [freeRate, integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hw, smul_eq_mul,
    freeSector]
  ring

/-- **A kernel that is not reflection positive**: `τ e^{−τ}`, `−∂_E e^{−τE}` at `E = 1`, the derivative of
a point mass, not a positive superposition of decays. DERIVED: the decay rate `1` is a counterexample
choice, as are the test times. -/
def bumpKernel (τ : ℝ) : ℝ := τ * Real.exp (-τ)

/-- **It violates the `2 × 2` Gram minor** at the times `1/4` and `1`: `C(1/2) C(2) = e^{−5/2}` and
`C(5/4)² = (25/16) e^{−5/2}`. DERIVED: `1/4`, `1` the two test times (any two distinct positive times
work, by the arithmetic–geometric mean inequality); `1/2`, `2`, `5/4` their sums; `5/2 = 1/2 + 2` the
shared exponent; `25/16 = (5/4)²` the squared sum over the product `1/2 · 2 = 1`. -/
theorem bumpKernel_not_reflPos : ¬ ReflPos bumpKernel := by
  intro h
  have g := h.gram_two (a := 1 / 4) (b := 1) (by norm_num) (by norm_num)
  have e1 : bumpKernel (1 / 4 + 1 / 4) = 1 / 2 * Real.exp (-(1 / 2)) := by
    show (1 / 4 + 1 / 4 : ℝ) * Real.exp (-(1 / 4 + 1 / 4)) = 1 / 2 * Real.exp (-(1 / 2)); norm_num
  have e2 : bumpKernel (1 + 1) = 2 * Real.exp (-2) := by
    show (1 + 1 : ℝ) * Real.exp (-(1 + 1)) = 2 * Real.exp (-2); norm_num
  have e3 : bumpKernel (1 / 4 + 1) = 5 / 4 * Real.exp (-(5 / 4)) := by
    show (1 / 4 + 1 : ℝ) * Real.exp (-(1 / 4 + 1)) = 5 / 4 * Real.exp (-(5 / 4)); norm_num
  rw [e1, e2, e3] at g
  have hx : Real.exp (-(1 / 2)) * Real.exp (-2) = Real.exp (-(5 / 4)) * Real.exp (-(5 / 4)) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have hA := Real.exp_pos (-(1 / 2 : ℝ))
  have hB := Real.exp_pos (-(5 / 4 : ℝ))
  have hx' : Real.exp (-(1 / 2)) * (Real.exp (-(1 / 2)) * Real.exp (-2))
      = Real.exp (-(1 / 2)) * (Real.exp (-(5 / 4)) * Real.exp (-(5 / 4))) := by rw [hx]
  have hABB := mul_pos hA (mul_pos hB hB)
  nlinarith [g, hx', hABB]

/-- **So it has no Laplace representation.** DERIVED: no numeral. -/
theorem bumpKernel_not_laplace : ¬ LaplaceRep bumpKernel :=
  fun h => bumpKernel_not_reflPos (laplace_reflPos h)

end

end MassGap.ShellMeasure

#print axioms MassGap.ShellMeasure.re_inner_cfc_eq_integral
#print axioms MassGap.ShellMeasure.rateMeasure_Iio
#print axioms MassGap.ShellMeasure.re_inner_powT_eq_laplace
#print axioms MassGap.ShellMeasure.powT_laplaceRep
#print axioms MassGap.ShellMeasure.flow_time_laplace
#print axioms MassGap.ShellMeasure.laplace_reflPos
#print axioms MassGap.ShellMeasure.ReflPos.gram_two
#print axioms MassGap.ShellMeasure.specBottom_klDensity
#print axioms MassGap.ShellMeasure.shell_rate_of_kl
#print axioms MassGap.ShellMeasure.free_laplaceRep
#print axioms MassGap.ShellMeasure.free_kallenLehmann
#print axioms MassGap.ShellMeasure.free_sector_rate
#print axioms MassGap.ShellMeasure.bumpKernel_not_reflPos
#print axioms MassGap.ShellMeasure.bumpKernel_not_laplace
