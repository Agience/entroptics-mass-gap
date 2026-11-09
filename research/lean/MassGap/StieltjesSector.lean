import Mathlib
import MassGap.FourierSector

/-!
# MassGap.StieltjesSector — the Stieltjes half of the converse: one mass measure from the sectors

`LorentzConverse` and `FourierSector` leave the inversion step: from the sectors `σ_p` of a vector,
produce one measure `ρ` in the mass squared, independent of `p`, with `σ_p` the shell measure
`klSec ρ p²`. This module proves the measure-theoretic core. The input is one named hypothesis,
`StieltjesCov`, the consequence of rotation invariance: the transform `∫ 2E/(w + E²) dμ_p(E)` of the
sector is one function of `w + p²`. Declarations are in the namespace `MassGap.StieltjesSector`.

DERIVED (module-wide): `0` the bottom of the rates, of the supports and of the time integral; `1` the
numerator of the resolvent and the shell weight; `2` the square and the shell weight `2E`; `Fin 4` the
spacetime index. The step `1` off the threshold in `stieltjes_unique` is a choice inside the proof,
labelled there: any positive step serves. No number enters a statement.

## 1. Stieltjes uniqueness (proved)

`stj τ w = ∫ dτ(x)/(w + x)`, `lapE τ u = ∫ e^{−ux} dτ(x)`.

* `stj_eq_mix`: `stj τ w = ∫₀^∞ e^{−uw} L_τ(u) du` (Tonelli and `exp_lintegral`).
* `tiltSt`, `tiltSt_laplace`: `e^{−uc} L_τ(u) du` is a finite measure whose Laplace transform at `v` is
  `stj τ (c + v)`.
* `stieltjes_unique`: finite measures on `[0, ∞)` with one Stieltjes transform on `w > c` are equal:
  `SmallClose.laplaceRep_unique` is applied twice, with continuity of `L_τ` on `u > 0` between.
* `stieltjes_unique_shift`: the same on `[−c, ∞)`, on `z > c`.

Stieltjes inversion is not in Mathlib at this pin; uniqueness does not need it.

## 2. The change of variables (proved)

`massOf p² σ` is `2E dσ(E)` carried by `E ↦ E² − p²`, and `secStj σ w = ∫ 2E/(w + E²) dσ(E)`.

* `klSec_massOf`: on `E > 0`, `klSec (massOf p² σ) p² = σ`.
* `massOf_klSec`: on `s + p² > 0`, `massOf p² (klSec ρ p²) = ρ`.
* `klSec_injective`: one sector fixes `ρ`.
* `stj_massOf`: `stj (massOf p² σ) z = secStj σ (z − p²)`.
* `secStj_klSec`: `secStj (klSec ρ p²) w = stj ρ (w + p²)`.

## 3. One measure (proved, under `StieltjesCov`)

`ShellReg σ`: no mass at `E ≤ 0`, and `∫ 2E dσ < ∞`. `StieltjesCov S μ`: there is `Φ` with
`secStj (μ p) w = Φ(w + p²)` for `p ∈ S`, `w > 0`.

* `massOf_eq`: the mass measures of regular covariant sectors are one measure.
* `stieltjesCov_iff`: on a non-empty `S`, regular sectors satisfy `StieltjesCov` if and only if one
  finite `ρ`, with `ρ(−∞, −p²] = 0` for `p ∈ S`, gives `μ p = klSec ρ p²` for every `p ∈ S`. No lower
  bound on the rates beyond `E > 0` is an input: the support of `ρ` is part of the conclusion.

## 4. Into the Källén–Lehmann template (proved, under the same hypothesis)

* `sectorKL_of_stieltjes`: if `m = g c λ` and the rescaled sectors `c(p) σ_p` are regular and covariant
  on a set of full `λ` measure, there is one finite `ρ` with `SectorKL J u ρ g`.
* `klJointRep_of_stieltjes`: the same with `g` continuous, `g 0 ≠ 0`, into `KLJointRep J u ρ`.

The per-sector Laplace match of `LorentzStep.klJointRep_of_laplace` is not an input: it is replaced by
`StieltjesCov`.

## What does not follow, plainly

Assumed, and whether shown non-vacuous:

* `StieltjesCov` for the sectors of a vector. By `stieltjesCov_iff` it holds of the family
  `p ↦ klSec ρ p²` for every finite `ρ` on `s > 0`, so it is non-vacuous as a statement about families
  of measures. It is not shown for the sectors of any vector, on the tree or for a general `J`. Together
  with `ShellReg` it is equivalent to the conclusion (`stieltjesCov_iff`); `StieltjesCov` alone is weaker,
  since it does not exclude mass at `E ≤ 0` or an infinite first moment. This module moves the input from
  a measure identity to one identity of transforms, and does not derive it.
* `StieltjesCov` is not derived from rotation invariance. The bridge is the cosine transform in time:
  `∫₀^∞ 2 cos(kt) ∫ e^{−tE} dμ(E) dt = ∫ 2E/(k² + E²) dμ(E)` when `∫ dμ/E < ∞` (argued here, not proved
  in Lean), read as the four-dimensional Fourier transform of the correlator at `(k, p)`. That reading
  needs the correlator on all of `t ∈ ℝ` down to `t = 0`.
* The factorization `m = g c λ`, `hm`. `FourierSector.momMarg_density` gives `m ≪ λ` under its integrable
  correlator hypothesis, itself not shown for any non-zero vector; the split of `dm/dλ` into `g` and `c`,
  with `g` continuous and `g 0 ≠ 0`, is assumed and not shown for any vector.
* `ShellReg`: no mass at `E ≤ 0` and a finite first moment of `c σ_p`, for `λ`-almost every `p`.
  Non-vacuous for families (`shellReg_klSec`), not shown for any vector. `2E` vanishes at `E = 0`, so a
  zero-rate atom is invisible to `massOf`; the first moment is what makes `ρ` finite, which
  `LorentzStep.klJointRep_iff` requires.

Not concluded:

* A vector smeared at a strictly positive time fails `KLJointRep` whenever `m_a ≠ m_b` (argued here,
  not proved in Lean). For a sharp time `t₀ > 0` the sector carries the factor `e^{−2t₀E}`, and with two masses `a`,
  `b` the ratio of the shell weights at momentum `p` contains `e^{−2t₀(E_a − E_b)}`, which depends on `p`.
  So no `g(p)` with one `ρ` fits: `StieltjesCov` fails for `c σ_p`, and the time shift must be removed
  from the sector first. §3 is stated for any family, but its hypothesis `StieltjesCov` fails for such a
  shifted family; §4 is stated for the sectors themselves and does not apply to it. The same shift is why the cosine transform above is
  not available at `t₀ > 0`: the correlator is known only at times `≥ 2t₀`.
* `ρ(−∞, 0) = 0` and the absence of an atom at `s = 0` are not concluded: only `ρ(−∞, −p²] = 0` for
  `p ∈ S`. Hence the `hρ0` and `SpecBottom` inputs of `LorentzStep.clay_zero_momentum_sectorKL` stay open.
* Stieltjes inversion as a formula is not built; only uniqueness, and existence through `massOf`.
* Rotation invariance, `O4Inv`, Lorentz covariance and the passage from positive-time vectors to
  rotations are not touched. `SectorKL` is not discharged for any composite vector.

Foundational footprint only (`#print axioms` at the end).
-/

set_option autoImplicit false

namespace MassGap.StieltjesSector

open Real Filter Topology MeasureTheory Set
open scoped NNReal ENNReal
open MassGap.BandShell (shell shell_nonneg)
open MassGap.ShellMeasure (klWeight measurable_klWeight measurable_shell)
open MassGap.ShellJoint (JointData)
open MassGap.ShellTranslate (spatial)
open MassGap.ShellDensity (lam lamF)
open MassGap.ShellLorentz (klSec psq KLJointRep)
open MassGap.MomentumSector (momMarg sector SectorKL)
open MassGap.LorentzStep (klJointRep_iff)

noncomputable section

/-! ## 1. Uniqueness of the Stieltjes transform -/

/-- **The Laplace transform of a measure**, valued in `[0, ∞]`. DERIVED: no numeral. -/
def lapE (τ : Measure ℝ) (u : ℝ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Real.exp (-(u * x))) ∂τ

/-- **The Stieltjes transform** `∫ dτ(x) / (w + x)`, valued in `[0, ∞]`. DERIVED: `1` the numerator of
the resolvent. -/
def stj (τ : Measure ℝ) (w : ℝ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (1 / (w + x)) ∂τ

/-- DERIVED: `0` the bottom of the support. -/
theorem ae_nonneg_of_Iio {τ : Measure ℝ} (h0 : τ (Iio 0) = 0) : ∀ᵐ x ∂τ, 0 ≤ x := by
  refine ae_iff.mpr ?_
  have e : {x : ℝ | ¬ 0 ≤ x} = Iio 0 := by ext x; simp
  rw [e]; exact h0

/-- **The resolvent is a Laplace integral**: `∫₀^∞ e^{−ua} du = 1/a`. DERIVED: `0` the bottom of the
time integral and the sign of `a`; `1` the numerator. -/
theorem exp_lintegral {a : ℝ} (ha : 0 < a) :
    ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(u * a))) = ENNReal.ofReal (1 / a) := by
  have e : (fun u : ℝ => Real.exp (-(u * a))) = fun u => Real.exp (-a * u) := by
    funext u; congr 1; ring
  have hi : IntegrableOn (fun u : ℝ => Real.exp (-(u * a))) (Ioi 0) := by
    rw [e]; exact integrableOn_exp_mul_Ioi (by linarith) 0
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun u => (Real.exp_pos _).le), e,
    integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero, neg_div_neg_eq]

/-- DERIVED: no numeral. -/
theorem measurable_expP : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(q.1 * q.2))) :=
  ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp
    (continuous_fst.mul continuous_snd).neg).measurable

/-- DERIVED: no numeral. -/
theorem measurable_lapE (τ : Measure ℝ) [SFinite τ] : Measurable (lapE τ) :=
  measurable_expP.lintegral_prod_right' (ν := τ)

/-- **The Stieltjes transform is a Laplace transform of the Laplace transform** (Tonelli):
`∫ dτ(x)/(w + x) = ∫₀^∞ e^{−uw} L_τ(u) du`. DERIVED: `0` the bottom of the support and of the time
integral. -/
theorem stj_eq_mix {τ : Measure ℝ} [SFinite τ] (h0 : τ (Iio 0) = 0) {w : ℝ} (hw : 0 < w) :
    stj τ w = ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(u * w))) * lapE τ u := by
  have h1 : stj τ w = ∫⁻ x, (∫⁻ u in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(u * w))) * ENNReal.ofReal (Real.exp (-(u * x)))) ∂τ := by
    unfold stj
    refine lintegral_congr_ae ?_
    filter_upwards [ae_nonneg_of_Iio h0] with x hx
    rw [← exp_lintegral (by linarith : 0 < w + x)]
    refine lintegral_congr fun u => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2; ring
  have hm : AEMeasurable (Function.uncurry fun (x u : ℝ) =>
      ENNReal.ofReal (Real.exp (-(u * w))) * ENNReal.ofReal (Real.exp (-(u * x))))
      (τ.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine Measurable.aemeasurable ?_
    have a : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(q.2 * w))) :=
      measurable_expP.comp (measurable_snd.prodMk measurable_const)
    have b : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(q.2 * q.1))) :=
      measurable_expP.comp (measurable_snd.prodMk measurable_fst)
    exact a.mul b
  rw [h1]
  refine (lintegral_lintegral_swap hm).trans (lintegral_congr fun u => ?_)
  have hme : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-(u * x))) :=
    measurable_expP.comp (measurable_const.prodMk measurable_id)
  exact lintegral_const_mul _ hme

/-- **The Stieltjes mixing measure** `e^{−uc} L_τ(u) du` on `u > 0`. DERIVED: `0` the bottom of the
time integral. -/
def tiltSt (τ : Measure ℝ) (c : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity
    fun u => ENNReal.ofReal (Real.exp (-(u * c))) * lapE τ u

/-- DERIVED: no numeral. -/
theorem measurable_tiltDens (τ : Measure ℝ) [SFinite τ] (c : ℝ) :
    Measurable fun u => ENNReal.ofReal (Real.exp (-(u * c))) * lapE τ u :=
  (measurable_expP.comp (measurable_id.prodMk measurable_const)).mul (measurable_lapE τ)

/-- **The Stieltjes transform is finite at `w > 0`**. DERIVED: `0` the bottom of the support; `1` the
numerator. -/
theorem stj_ne_top {τ : Measure ℝ} [IsFiniteMeasure τ] (h0 : τ (Iio 0) = 0) {w : ℝ} (hw : 0 < w) :
    stj τ w ≠ ⊤ := by
  have hle : stj τ w ≤ ∫⁻ _, ENNReal.ofReal (1 / w) ∂τ := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_nonneg_of_Iio h0] with x hx
    exact ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le hw (by linarith))
  refine (lt_of_le_of_lt hle ?_).ne
  rw [lintegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/-- DERIVED: `0` the bottom of the support. -/
theorem tiltSt_univ {τ : Measure ℝ} [SFinite τ] (h0 : τ (Iio 0) = 0) {c : ℝ} (hc : 0 < c) :
    tiltSt τ c univ = stj τ c := by
  rw [tiltSt, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, stj_eq_mix h0 hc]

/-- DERIVED: no numeral. -/
theorem tiltSt_finite {τ : Measure ℝ} [IsFiniteMeasure τ] (h0 : τ (Iio 0) = 0) {c : ℝ}
    (hc : 0 < c) : IsFiniteMeasure (tiltSt τ c) :=
  ⟨by rw [tiltSt_univ h0 hc]; exact lt_top_iff_ne_top.mpr (stj_ne_top h0 hc)⟩

/-- DERIVED: `0` the bottom of the mixing variable. -/
theorem tiltSt_Iio (τ : Measure ℝ) (c : ℝ) : tiltSt τ c (Iio 0) = 0 := by
  have h : (volume.restrict (Ioi (0 : ℝ))) (Iio 0) = 0 := by
    rw [Measure.restrict_apply measurableSet_Iio]
    have e : Iio (0 : ℝ) ∩ Ioi 0 = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_empty_iff_false, iff_false, not_and,
        not_lt]; intro hx; exact hx.le
    rw [e, measure_empty]
  exact withDensity_absolutelyContinuous _ _ h

/-- **The Laplace transform of the mixing measure is the Stieltjes transform further out.**
DERIVED: `0` the bottom of the support and the sign of the shift. -/
theorem tiltSt_laplace {τ : Measure ℝ} [SFinite τ] (h0 : τ (Iio 0) = 0) {c v : ℝ} (hc : 0 < c)
    (hv : 0 < v) : ∫ u, Real.exp (-(v * u)) ∂(tiltSt τ c) = (stj τ (c + v)).toReal := by
  have hmr : Measurable fun u : ℝ => Real.exp (-(v * u)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).measurable
  have hme : Measurable fun u : ℝ => ENNReal.ofReal (Real.exp (-(v * u))) :=
    ENNReal.measurable_ofReal.comp hmr
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun u => (Real.exp_pos _).le)
    hmr.aestronglyMeasurable, tiltSt, lintegral_withDensity_eq_lintegral_mul _
    (measurable_tiltDens τ c) hme,
    stj_eq_mix h0 (by linarith : 0 < c + v)]
  congr 1
  refine lintegral_congr fun u => ?_
  simp only [Pi.mul_apply]
  rw [mul_right_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 3; ring

/-- **The real Laplace transform.** DERIVED: no numeral. -/
def lapR (τ : Measure ℝ) (u : ℝ) : ℝ := ∫ x, Real.exp (-(u * x)) ∂τ

/-- DERIVED: `0` the bottom of the support. -/
theorem lapR_eq (τ : Measure ℝ) (u : ℝ) : lapR τ u = (lapE τ u).toReal := by
  refine integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun u => (Real.exp_pos _).le) ?_
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).aestronglyMeasurable

/-- DERIVED: `0` the bottom of the support and of the time; `1` the bound of `e^{−ux}`. -/
theorem continuousOn_lapR {τ : Measure ℝ} [IsFiniteMeasure τ] (h0 : τ (Iio 0) = 0) :
    ContinuousOn (lapR τ) (Ioi 0) := by
  refine continuousOn_of_dominated (bound := fun _ => (1 : ℝ)) (fun u _ => ?_) (fun u hu => ?_)
    (integrable_const _) (Eventually.of_forall fun x => ?_)
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).aestronglyMeasurable
  · filter_upwards [ae_nonneg_of_Iio h0] with x hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg (le_of_lt hu) hx)
  · exact (Real.continuous_exp.comp (continuous_id.mul continuous_const).neg).continuousOn

/-- **Stieltjes uniqueness**: two finite measures on `[0, ∞)` with equal Stieltjes transforms on
`w > c`, `c ≥ 0`, are equal. The transform of `τ` is the Laplace transform of `L_τ(u) du`, so
`SmallClose.laplaceRep_unique` fixes `L_τ` almost everywhere, continuity fixes it on `u > 0`, and
`laplaceRep_unique` again fixes `τ`. DERIVED: `0` the bottom of the support; `1` the step off `c`,
any positive step serves. -/
theorem stieltjes_unique {τ τ' : Measure ℝ} [IsFiniteMeasure τ] [IsFiniteMeasure τ']
    (h0 : τ (Iio 0) = 0) (h0' : τ' (Iio 0) = 0) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ w, c < w → stj τ w = stj τ' w) : τ = τ' := by
  have hc1 : 0 < c + 1 := by linarith
  haveI := tiltSt_finite h0 hc1
  haveI := tiltSt_finite h0' hc1
  have e : tiltSt τ (c + 1) = tiltSt τ' (c + 1) :=
    SmallClose.laplaceRep_unique (tiltSt_Iio _ _) (tiltSt_Iio _ _) fun v hv => by
      rw [tiltSt_laplace h0 hc1 hv, tiltSt_laplace h0' hc1 hv, h _ (by linarith)]
  have hae := (withDensity_eq_iff_of_sigmaFinite (measurable_tiltDens τ (c + 1)).aemeasurable
    (measurable_tiltDens τ' (c + 1)).aemeasurable).mp e
  have hL : lapR τ =ᵐ[volume.restrict (Ioi (0 : ℝ))] lapR τ' := by
    filter_upwards [hae] with u hu
    rw [lapR_eq, lapR_eq, (ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
      ENNReal.ofReal_ne_top).mp hu]
  have hE := Measure.eqOn_open_of_ae_eq hL isOpen_Ioi (continuousOn_lapR h0) (continuousOn_lapR h0')
  exact SmallClose.laplaceRep_unique h0 h0' fun t ht => hE ht

/-- DERIVED: no numeral. -/
theorem stj_shift (ρ : Measure ℝ) (c w : ℝ) : stj (ρ.map (· + c)) w = stj ρ (w + c) := by
  have hm : Measurable fun x : ℝ => ENNReal.ofReal (1 / (w + x)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_const.add measurable_id))
  rw [stj, lintegral_map hm (by fun_prop : Measurable fun x : ℝ => x + c), stj]
  refine lintegral_congr fun x => ?_
  congr 2; ring

/-- **Stieltjes uniqueness on `[−c, ∞)`**: two finite measures on `[−c, ∞)`, with equal transforms on
`z > c`, are equal. DERIVED: `0` the bottom after the shift. -/
theorem stieltjes_unique_shift {ρ ρ' : Measure ℝ} [IsFiniteMeasure ρ] [IsFiniteMeasure ρ'] {c : ℝ}
    (h0 : ρ (Iio (-c)) = 0) (h0' : ρ' (Iio (-c)) = 0)
    (h : ∀ z, c < z → stj ρ z = stj ρ' z) : ρ = ρ' := by
  have hmc : Measurable fun x : ℝ => x + c := by fun_prop
  have hI : ∀ σ : Measure ℝ, σ (Iio (-c)) = 0 → (σ.map (· + c)) (Iio 0) = 0 := fun σ hσ => by
    rw [Measure.map_apply hmc measurableSet_Iio]
    have e : (fun x : ℝ => x + c) ⁻¹' Iio 0 = Iio (-c) := by
      ext x; simp only [mem_preimage, mem_Iio]; constructor <;> intro hx <;> linarith
    rw [e, hσ]
  haveI : IsFiniteMeasure (ρ.map (· + c)) := Measure.isFiniteMeasure_map _ _
  haveI : IsFiniteMeasure (ρ'.map (· + c)) := Measure.isFiniteMeasure_map _ _
  have e := stieltjes_unique (hI ρ h0) (hI ρ' h0') le_rfl fun w hw => by
    rw [stj_shift, stj_shift]; exact h _ (by linarith)
  have hb : ∀ σ : Measure ℝ, (σ.map (· + c)).map (· - c) = σ := fun σ => by
    rw [Measure.map_map (by fun_prop : Measurable fun x : ℝ => x - c) hmc]
    have i : (fun x : ℝ => x - c) ∘ (fun x : ℝ => x + c) = id := by
      funext x; simp
    rw [i, Measure.map_id]
  rw [← hb ρ, e, hb ρ']

/-! ## 2. The change of variables between the shell and the mass -/

/-- **The mass measure of a sector at `p²`**: `2E dσ(E)` carried by `E ↦ E² − p²`. DERIVED: `2` the
shell weight and the square. -/
def massOf (p2 : ℝ) (σ : Measure ℝ) : Measure ℝ :=
  (σ.withDensity fun E => ENNReal.ofReal (2 * E)).map fun E => E ^ 2 - p2

/-- DERIVED: `2` as in `massOf`. -/
theorem measurable_twoE : Measurable fun E : ℝ => ENNReal.ofReal (2 * E) :=
  ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_id)

/-- DERIVED: `2` the square. -/
theorem measurable_sqSub (p2 : ℝ) : Measurable fun E : ℝ => E ^ 2 - p2 :=
  (measurable_id.pow_const 2).sub_const p2

/-- DERIVED: `2` as in `massOf`. -/
theorem lintegral_massOf (p2 : ℝ) (σ : Measure ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ s, f s ∂(massOf p2 σ) = ∫⁻ E, ENNReal.ofReal (2 * E) * f (E ^ 2 - p2) ∂σ := by
  have hc : Measurable fun E : ℝ => f (E ^ 2 - p2) := hf.comp (measurable_sqSub p2)
  rw [massOf, lintegral_map hf (measurable_sqSub p2),
    lintegral_withDensity_eq_lintegral_mul _ measurable_twoE hc]
  rfl

/-- DERIVED: no numeral. -/
theorem lintegral_klSec (ρ : Measure ℝ) (p2 : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ E, f E ∂(klSec ρ p2) = ∫⁻ s, klWeight p2 s * f (shell s p2) ∂ρ := by
  have hc : Measurable fun s : ℝ => f (shell s p2) := hf.comp (measurable_shell p2)
  rw [klSec, lintegral_map hf (measurable_shell p2),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_klWeight p2) hc]
  rfl

/-- DERIVED: `0` the sign of `E`; `2` the square. -/
theorem shell_sq {E : ℝ} (hE : 0 ≤ E) (p2 : ℝ) : shell (E ^ 2 - p2) p2 = E := by
  unfold shell; rw [sub_add_cancel, Real.sqrt_sq hE]

/-- DERIVED: `0` the sign of `s + p²`; `2` the square. -/
theorem sq_shell {s p2 : ℝ} (h : 0 ≤ s + p2) : shell s p2 ^ 2 - p2 = s := by
  unfold shell; rw [Real.sq_sqrt h, add_sub_cancel_right]

/-- **The weights cancel**: `(1/(2E)) · 2E = 1` for `E > 0`. DERIVED: `0` the sign; `1`, `2` the shell
weight. -/
theorem weight_cancel {E : ℝ} (hE : 0 < E) :
    ENNReal.ofReal (1 / (2 * E)) * ENNReal.ofReal (2 * E) = 1 := by
  rw [← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel (by positivity), ENNReal.ofReal_one]

/-- DERIVED: `0` the bottom. -/
theorem ae_pos_of_Iic {σ : Measure ℝ} (h : σ (Iic 0) = 0) : ∀ᵐ E ∂σ, 0 < E := by
  refine ae_iff.mpr ?_
  have e : {x : ℝ | ¬ 0 < x} = Iic 0 := by ext x; simp
  rw [e]; exact h

/-- **Mass to shell**: a sector on `E > 0` is the Källén–Lehmann sector of its own mass measure.
DERIVED: `0` the bottom of the rates. -/
theorem klSec_massOf {σ : Measure ℝ} (h : σ (Iic 0) = 0) (p2 : ℝ) :
    klSec (massOf p2 σ) p2 = σ := by
  refine Measure.ext fun A hA => ?_
  have hi : Measurable (A.indicator (1 : ℝ → ℝ≥0∞)) := measurable_one.indicator hA
  have hk : Measurable fun s : ℝ => klWeight p2 s * A.indicator (1 : ℝ → ℝ≥0∞) (shell s p2) :=
    (measurable_klWeight p2).mul (hi.comp (measurable_shell p2))
  rw [← lintegral_indicator_one hA, lintegral_klSec _ _ hi, lintegral_massOf _ _ hk,
    ← lintegral_indicator_one hA]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_pos_of_Iic h] with E hE
  rw [shell_sq hE.le, klWeight, shell_sq hE.le, ← mul_assoc, mul_comm (ENNReal.ofReal (2 * E)),
    weight_cancel hE, one_mul]

/-- **Shell to mass**: the mass measure of `klSec ρ p²` is `ρ`, when `ρ` lives on `s + p² > 0`.
DERIVED: `0` the bottom of `s + p²`. -/
theorem massOf_klSec {ρ : Measure ℝ} {p2 : ℝ} (h : ∀ᵐ s ∂ρ, 0 < s + p2) :
    massOf p2 (klSec ρ p2) = ρ := by
  refine Measure.ext fun A hA => ?_
  have hi : Measurable (A.indicator (1 : ℝ → ℝ≥0∞)) := measurable_one.indicator hA
  have hk : Measurable fun E : ℝ =>
      ENNReal.ofReal (2 * E) * A.indicator (1 : ℝ → ℝ≥0∞) (E ^ 2 - p2) :=
    measurable_twoE.mul (hi.comp (measurable_sqSub p2))
  rw [← lintegral_indicator_one hA, lintegral_massOf _ _ hi, lintegral_klSec _ _ hk,
    ← lintegral_indicator_one hA]
  refine lintegral_congr_ae ?_
  filter_upwards [h] with s hs
  have hE : 0 < shell s p2 := Real.sqrt_pos.mpr hs
  rw [klWeight, ← mul_assoc, weight_cancel hE, one_mul]
  exact congrArg (A.indicator (1 : ℝ → ℝ≥0∞)) (sq_shell hs.le)

/-- **Injectivity of the shell map**: one sector fixes `ρ`. DERIVED: `0` the bottom of `s + p²`. -/
theorem klSec_injective {ρ ρ' : Measure ℝ} {p2 : ℝ} (h : ∀ᵐ s ∂ρ, 0 < s + p2)
    (h' : ∀ᵐ s ∂ρ', 0 < s + p2) (e : klSec ρ p2 = klSec ρ' p2) : ρ = ρ' := by
  rw [← massOf_klSec h, e, massOf_klSec h']

/-- **The Stieltjes transform of a sector in `w = k₀²`**: `∫ 2E / (w + E²) dσ(E)`. DERIVED: `2` the
shell weight and the square. -/
def secStj (σ : Measure ℝ) (w : ℝ) : ℝ≥0∞ := ∫⁻ E, ENNReal.ofReal (2 * E / (w + E ^ 2)) ∂σ

/-- **Mass Stieltjes is sector Stieltjes**, shifted by `p²`. DERIVED: `0` the bottom of the rates; `1`
the numerator; `2` the shell weight. -/
theorem stj_massOf {σ : Measure ℝ} (h : σ (Iic 0) = 0) (p2 z : ℝ) :
    stj (massOf p2 σ) z = secStj σ (z - p2) := by
  have hm : Measurable fun x : ℝ => ENNReal.ofReal (1 / (z + x)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_const.add measurable_id))
  rw [stj, lintegral_massOf _ _ hm, secStj]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_pos_of_Iic h] with E hE
  rw [← ENNReal.ofReal_mul (by positivity), mul_one_div]
  congr 2; ring

/-- **Sector Stieltjes of a Källén–Lehmann sector** is the mass Stieltjes transform at `w + p²`.
DERIVED: `0` the bottom of `s + p²`; `1`, `2` the shell weight. -/
theorem secStj_klSec {ρ : Measure ℝ} {p2 : ℝ} (h : ∀ᵐ s ∂ρ, 0 < s + p2) (w : ℝ) :
    secStj (klSec ρ p2) w = stj ρ (w + p2) := by
  have hm : Measurable fun E : ℝ => ENNReal.ofReal (2 * E / (w + E ^ 2)) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_const.mul measurable_id).div (measurable_const.add (measurable_id.pow_const 2)))
  rw [secStj, lintegral_klSec _ _ hm, stj]
  refine lintegral_congr_ae ?_
  filter_upwards [h] with s hs
  have hE : 0 < shell s p2 := Real.sqrt_pos.mpr hs
  have e : shell s p2 ^ 2 = s + p2 := by linarith [sq_shell hs.le]
  rw [klWeight, ← ENNReal.ofReal_mul (by positivity), e, ← mul_div_assoc, one_div_mul_cancel
    (by positivity)]
  congr 2; ring

/-! ## 3. One mass measure from covariant sectors -/

/-- **The regular sectors**: no mass at rates `E ≤ 0`, and a finite first moment. DERIVED: `0` the
bottom of the rates; `2` the shell weight. -/
def ShellReg (σ : Measure ℝ) : Prop :=
  σ (Iic 0) = 0 ∧ ∫⁻ E, ENNReal.ofReal (2 * E) ∂σ ≠ ⊤

/-- **The rotation-invariance consequence** (a named hypothesis): the transform in the time frequency
`w = k₀²` of each sector in `S` is one function `Φ` of `k₀² + p²`. For a rotation-invariant
two-point function, the mixed transform `∫ 2E/(k₀² + E²) dμ_p(E)` is the four-dimensional Fourier
transform at `(k₀, p)`, a function of `k₀² + |p|²` alone. DERIVED: `0` the bottom of `w`; `Fin 4` the
spacetime index. -/
def StieltjesCov (S : Set (Fin 4 → ℝ)) (μ : (Fin 4 → ℝ) → Measure ℝ) : Prop :=
  ∃ Φ : ℝ → ℝ≥0∞, ∀ p ∈ S, ∀ w, 0 < w → secStj (μ p) w = Φ (w + psq p)

/-- DERIVED: `2` the shell weight. -/
theorem massOf_finite {σ : Measure ℝ} (h : ShellReg σ) (p2 : ℝ) : IsFiniteMeasure (massOf p2 σ) := by
  refine ⟨?_⟩
  rw [massOf, Measure.map_apply (measurable_sqSub p2) MeasurableSet.univ, preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact lt_top_iff_ne_top.mpr h.2

/-- **The mass measure sits above `−p²`.** DERIVED: `0` the bottom of the rates; `2` the square. -/
theorem massOf_Iic {σ : Measure ℝ} (h : σ (Iic 0) = 0) (p2 : ℝ) :
    massOf p2 σ (Iic (-p2)) = 0 := by
  rw [massOf, Measure.map_apply (measurable_sqSub p2) measurableSet_Iic]
  refine withDensity_absolutelyContinuous _ _ ?_
  have hne : ∀ᵐ E ∂σ, E ≠ 0 := (ae_pos_of_Iic h).mono fun _ hE => hE.ne'
  refine measure_mono_null (fun E hE0 => ?_) (ae_iff.mp hne)
  have hle : E ^ 2 ≤ 0 := by
    have := (mem_preimage.mp hE0 : E ^ 2 - p2 ∈ Iic (-p2))
    simp only [mem_Iic] at this; linarith
  have h2 : E ^ 2 = 0 := le_antisymm hle (sq_nonneg E)
  have hz : E = 0 := by simpa using h2
  simpa using hz

/-- **The mass measures of covariant regular sectors agree.** Each has Stieltjes transform `Φ` on
`z > p²`, so two of them agree on `z > max p² p'²`, and `stieltjes_unique_shift` applies. DERIVED: `0`
the bottom of the rates and of `w`. -/
theorem massOf_eq {S : Set (Fin 4 → ℝ)} {μ : (Fin 4 → ℝ) → Measure ℝ} (hc : StieltjesCov S μ)
    (hr : ∀ p ∈ S, ShellReg (μ p)) {p p' : Fin 4 → ℝ} (hp : p ∈ S) (hp' : p' ∈ S) :
    massOf (psq p) (μ p) = massOf (psq p') (μ p') := by
  obtain ⟨Φ, hΦ⟩ := hc
  haveI := massOf_finite (hr p hp) (psq p)
  haveI := massOf_finite (hr p' hp') (psq p')
  have hq : ∀ q ∈ S, ∀ z, psq q < z → stj (massOf (psq q) (μ q)) z = Φ z := fun q hq z hz => by
    rw [stj_massOf (hr q hq).1, hΦ q hq _ (by linarith), sub_add_cancel]
  have hb : ∀ q ∈ S, psq q ≤ max (psq p) (psq p') →
      massOf (psq q) (μ q) (Iio (-max (psq p) (psq p'))) = 0 := fun q hq hle => by
    refine measure_mono_null (fun x hx => ?_) (massOf_Iic (hr q hq).1 (psq q))
    have := mem_Iio.mp hx
    exact mem_Iic.mpr (by linarith)
  refine stieltjes_unique_shift (hb p hp (le_max_left _ _)) (hb p' hp' (le_max_right _ _))
    fun z hz => ?_
  rw [hq p hp z (lt_of_le_of_lt (le_max_left _ _) hz),
    hq p' hp' z (lt_of_le_of_lt (le_max_right _ _) hz)]

/-- DERIVED: `0` the bottom of `s + p²`. -/
theorem ae_add_pos {ρ : Measure ℝ} {p2 : ℝ} (h : ρ (Iic (-p2)) = 0) : ∀ᵐ s ∂ρ, 0 < s + p2 := by
  refine ae_iff.mpr ?_
  have e : {s : ℝ | ¬ 0 < s + p2} = Iic (-p2) := by
    ext s; simp only [mem_setOf_eq, not_lt, mem_Iic]; constructor <;> intro hs <;> linarith
  rw [e]; exact h

/-- **The Källén–Lehmann sector of a finite `ρ` is regular.** DERIVED: `0` the bottom of `s + p²`. -/
theorem shellReg_klSec {ρ : Measure ℝ} [IsFiniteMeasure ρ] {p2 : ℝ} (h : ρ (Iic (-p2)) = 0) :
    ShellReg (klSec ρ p2) := by
  have hpos := ae_add_pos h
  constructor
  · rw [klSec, Measure.map_apply (measurable_shell p2) measurableSet_Iic]
    refine withDensity_absolutelyContinuous _ _ (measure_mono_null (fun s hs => ?_) h)
    have hs' : shell s p2 ≤ 0 := hs
    by_contra hn
    have : 0 < s + p2 := by
      have := mem_Iic.not.mp hn
      linarith
    exact absurd hs' (not_le.mpr (Real.sqrt_pos.mpr this))
  · have hm : ∫⁻ E, ENNReal.ofReal (2 * E) ∂(klSec ρ p2) = ρ univ := by
      rw [lintegral_klSec _ _ measurable_twoE, ← lintegral_one]
      refine lintegral_congr_ae ?_
      filter_upwards [hpos] with s hs
      exact weight_cancel (Real.sqrt_pos.mpr hs)
    rw [hm]; exact measure_ne_top _ _

/-- **The Stieltjes step, as an equivalence.** On a non-empty set `S` of momenta, sectors `μ p` are
regular and satisfy `StieltjesCov` if and only if one finite measure `ρ` on `s > −p²`, `p ∈ S`, gives
every sector as `klSec ρ p²`. DERIVED: `0` the bottom. -/
theorem stieltjesCov_iff {S : Set (Fin 4 → ℝ)} (hS : S.Nonempty) (μ : (Fin 4 → ℝ) → Measure ℝ) :
    (StieltjesCov S μ ∧ ∀ p ∈ S, ShellReg (μ p)) ↔
      ∃ ρ : Measure ℝ, IsFiniteMeasure ρ ∧ (∀ p ∈ S, ρ (Iic (-psq p)) = 0) ∧
        ∀ p ∈ S, klSec ρ (psq p) = μ p := by
  constructor
  · rintro ⟨hc, hr⟩
    obtain ⟨p₀, hp₀⟩ := hS
    have e : ∀ p ∈ S, massOf (psq p₀) (μ p₀) = massOf (psq p) (μ p) := fun p hp =>
      massOf_eq hc hr hp₀ hp
    refine ⟨massOf (psq p₀) (μ p₀), massOf_finite (hr p₀ hp₀) _, fun p hp => ?_, fun p hp => ?_⟩
    · rw [e p hp]; exact massOf_Iic (hr p hp).1 _
    · rw [e p hp]; exact klSec_massOf (hr p hp).1 _
  · rintro ⟨ρ, _, h0, hk⟩
    refine ⟨⟨stj ρ, fun p hp w _ => ?_⟩, fun p hp => ?_⟩
    · rw [← hk p hp, secStj_klSec (ae_add_pos (h0 p hp))]
    · rw [← hk p hp]; exact shellReg_klSec (h0 p hp)

/-! ## 4. Into `SectorKL` and `KLJointRep` -/

/-- DERIVED: no numeral. -/
theorem lam_ne_zero (τ : Fin 4) : lam τ ≠ 0 := by
  intro h
  have hu : lam τ univ = 0 := by rw [h]; rfl
  rw [lam, Measure.pi_univ, Finset.prod_eq_zero_iff] at hu
  obtain ⟨j, -, hj⟩ := hu
  unfold lamF at hj
  split_ifs at hj
  · simp at hj
  · simp at hj

section Vector

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {τ : Fin 4} (J : JointData H (spatial τ))

/-- **`SectorKL` from Stieltjes covariance.** Let the marginal be `m = g c λ` and let the rescaled
sectors `c(p) σ_p` be regular and covariant on a set `S` of full `λ` measure. Then there is one finite
`ρ` above `−p²` for `p ∈ S`, with `SectorKL J u ρ g`. DERIVED: `0` the bottom. -/
theorem sectorKL_of_stieltjes (u : H) {g c : (Fin 4 → ℝ) → ℝ≥0} {S : Set (Fin 4 → ℝ)}
    (hm : momMarg J u = (lam τ).withDensity fun p => (g p : ℝ≥0∞) * c p)
    (hS : ∀ᵐ p ∂(lam τ), p ∈ S)
    (hcov : StieltjesCov S fun p => c p • (sector J u p : Measure ℝ))
    (hreg : ∀ p ∈ S, ShellReg (c p • (sector J u p : Measure ℝ))) :
    ∃ ρ : Measure ℝ, IsFiniteMeasure ρ ∧ (∀ p ∈ S, ρ (Iic (-psq p)) = 0) ∧ SectorKL J u ρ g := by
  haveI : (ae (lam τ)).NeBot := ae_neBot.mpr (lam_ne_zero τ)
  obtain ⟨p₀, hp₀⟩ := hS.exists
  obtain ⟨ρ, hfin, h0, hk⟩ := (stieltjesCov_iff ⟨p₀, hp₀⟩ _).mp ⟨hcov, hreg⟩
  refine ⟨ρ, hfin, h0, ?_, ?_⟩
  · have hmass : ∀ p ∈ S, klSec ρ (psq p) univ = c p := fun p hp => by
      rw [hk p hp, Measure.coe_nnreal_smul_apply, measure_univ, mul_one]
    rw [hm]
    refine withDensity_congr_ae ?_
    filter_upwards [hS] with p hp
    rw [hmass p hp]
  · have hac : momMarg J u ≪ lam τ := by rw [hm]; exact withDensity_absolutelyContinuous _ _
    filter_upwards [hac.ae_le hS] with p hp
    rw [hk p hp, Measure.coe_nnreal_smul_apply, measure_univ, mul_one, Measure.coe_nnreal_smul]

/-- **`KLJointRep` from Stieltjes covariance.** The same with `g` continuous and `g 0 ≠ 0`.
DERIVED: `0` the zero momentum and the bottom. -/
theorem klJointRep_of_stieltjes (u : H) {g c : (Fin 4 → ℝ) → ℝ≥0} (hg : Continuous g) (hg0 : g 0 ≠ 0)
    {S : Set (Fin 4 → ℝ)}
    (hm : momMarg J u = (lam τ).withDensity fun p => (g p : ℝ≥0∞) * c p)
    (hS : ∀ᵐ p ∂(lam τ), p ∈ S)
    (hcov : StieltjesCov S fun p => c p • (sector J u p : Measure ℝ))
    (hreg : ∀ p ∈ S, ShellReg (c p • (sector J u p : Measure ℝ))) :
    ∃ ρ : Measure ℝ, IsFiniteMeasure ρ ∧ (∀ p ∈ S, ρ (Iic (-psq p)) = 0) ∧ KLJointRep J u ρ := by
  obtain ⟨ρ, hfin, h0, hk⟩ := sectorKL_of_stieltjes J u hm hS hcov hreg
  exact ⟨ρ, hfin, h0, (klJointRep_iff J u ρ).mpr ⟨g, hg, hg0, hk⟩⟩

end Vector

end

end MassGap.StieltjesSector

#print axioms MassGap.StieltjesSector.exp_lintegral
#print axioms MassGap.StieltjesSector.stj_eq_mix
#print axioms MassGap.StieltjesSector.tiltSt_laplace
#print axioms MassGap.StieltjesSector.stieltjes_unique
#print axioms MassGap.StieltjesSector.stieltjes_unique_shift
#print axioms MassGap.StieltjesSector.klSec_massOf
#print axioms MassGap.StieltjesSector.massOf_klSec
#print axioms MassGap.StieltjesSector.klSec_injective
#print axioms MassGap.StieltjesSector.stj_massOf
#print axioms MassGap.StieltjesSector.secStj_klSec
#print axioms MassGap.StieltjesSector.massOf_eq
#print axioms MassGap.StieltjesSector.shellReg_klSec
#print axioms MassGap.StieltjesSector.stieltjesCov_iff
#print axioms MassGap.StieltjesSector.sectorKL_of_stieltjes
#print axioms MassGap.StieltjesSector.klJointRep_of_stieltjes
