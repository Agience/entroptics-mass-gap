import Mathlib
import MassGap.ShiftSector

/-!
# MassGap.ShiftVector — the joint measure of a vector moved by the time semigroup

`ShiftSector` states the template `KLJointRepAt` for vectors at positive time and proves the obstruction
for families of measures. This module proves the identity behind the template, `nu(a^{t₀} v) =
e^{−2t₀E} · nu(v)`, on the full rate × momentum measure, and proves the obstruction at the level of a
vector. Declarations are in the namespace `MassGap.ShiftVector`.

DERIVED (module-wide): `0` the bottom of the rates, the zero shift and the zero momentum; `1` the unit
vector along one spatial direction and the bound of `e^{−x}`, `x ≥ 0`; `2` the shift `e^{−2t₀E}` (the
vector at time `t₀` enters its two-point function twice) and the square; `Fin 4` the spacetime index.
CHOSEN (inside the proof of `exists_two_psq` only): one spatial direction `j ≠ τ`; any spatial
direction serves, and it enters no statement. No chosen number enters a statement.

## 1. The vector identity (proved)

* `powT_mul_U`, `U_powT_apply`: `a^t` commutes with every translation, `t ≥ 0`: both lie in the
  commutative joint algebra (`MomentumSector.powT_eq_cfc`).
* `dyadicDini_powT`: `DyadicDini` passes from `v` to `a^{t₀} v`, with the factor `‖a^{t₀}‖²`.
* `inner_shift`: `⟪a^{t₀} v, a^t U(x) a^{t₀} v⟫ = ⟪v, a^{t + 2t₀} U(x) v⟫` (self-adjointness and the
  semigroup law `ContinuumTimeGroup.powT_add`).
* `tiltJ_eq_tiltDens`: `ShiftSector.tiltJ t₀` is the density `LorentzConverse.tiltDens (2t₀)`.
* `nu_powT`: under `DyadicDini v` and `t₀ ≥ 0`, `nu J (a^{t₀} v) = tiltJ t₀ (nu J v)`. Both sides have
  the transform `∫ e^{−(t + 2t₀)E} e^{i p·x} dν_v` for every `t > 0` and spatial `x`, and
  `LorentzConverse.ext_laplace_fourier` makes them equal. This is the joint identity, not only a
  marginal.
* `klJointRepAt_of_shift`: `KLJointRep J v ρ` gives `KLJointRepAt J (a^{t₀} v) ρ t₀`.

## 2. The vector obstruction (proved)

* `rect_ae`: two shifted Källén–Lehmann joint measures that agree give, for each measurable set `B` of
  rates, `g(p) (e^{−2tE} klSec ρ p²)(B) = g'(p) (e^{−2t'E} klSec ρ' p²)(B)` for `λ`-almost every `p`
  (`ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite`).
* `sector_eq_ae`: the same as measures, for `λ`-almost every `p`, when the `ρ` side has finite shell
  mass: the rational half-lines `(−∞, q)` and `univ` are countable, generate the Borel sets and form a
  π-system.
* `klSec_univ_ne_top`: a finite `ρ` with `ρ(−∞, m) = 0`, `m > 0`, has finite shell mass at every
  `p² ≥ 0`.
* `lam_open_ne_zero`, `exists_two_psq`: an open set around `0` holds two points of any `λ`-full set with
  different `p²`.
* `not_klJointRep_of_at`: if `u` satisfies `KLJointRepAt J u ρ t₀` with `t₀ > 0`, `ρ` finite with
  `ρ(−∞, m) = 0` for some `m > 0`, and `ρ` has atoms at `a ≠ b`, then `KLJointRep J u ρ'` fails for every
  s-finite `ρ'`. The two points come from `exists_two_psq` on `{g ≠ 0}`; at them the sectors are
  `ShiftSector.shift_not_kl`'s data.
* `shift_vector_not_kl`: if `v` satisfies `DyadicDini` and `KLJointRep J v ρ` with such a `ρ`, then for
  every `t₀ > 0` the vector `a^{t₀} v` satisfies `KLJointRep` for no s-finite `ρ'`.

Foundational footprint only (`#print axioms` at the end).

## What does not follow

Assumed, and whether shown non-vacuous:

* `DyadicDini J v` in `nu_powT`, `klJointRepAt_of_shift`, `shift_vector_not_kl`. It is the hypothesis of
  `MomentumSector.inner_powT_U_eq_nu`, used here to read both transforms. Non-vacuous: on the tree it
  holds on the complex span of `DiniHolder.lipVecs` (`DiniHolder.dyadicDini_span`). Whether the identity
  holds without it is not addressed.
* `KLJointRepAt J u ρ t₀` in `not_klJointRep_of_at` and `KLJointRep J v ρ` in `shift_vector_not_kl`: named
  hypotheses, not discharged for any composite vector (as in `ShiftSector`).
* On `ρ`: finite, `ρ(−∞, m) = 0` for some `m > 0`, two atoms. Non-vacuous: `ShiftSector.exRho`
  (atoms `1`, `4`, CHOSEN there) meets them with any `0 < m ≤ 1`. The gap `m > 0` is used for the finite shell mass in
  `sector_eq_ae` and for `a + p² > 0`; a `ρ` with mass reaching `0`, or without two atoms, is not
  treated.
* `SFinite ρ'`: the refuted template is refuted only for s-finite `ρ'`, the class on which
  `ShellLorentz.klJoint` is a product measure. This is plainly weaker than refuting it for every measure.

Not concluded:

* `t₀` is not read off a vector: the identity moves a given vector by a given `t₀`, and whether a
  vector satisfying `KLJointRepAt` is `a^{t₀}` of a vector satisfying `KLJointRep` is not addressed.
* `t₀ < 0` is not treated: `a^{t₀}` is not defined as an inverse here.
* Rotation invariance, `O4Inv`, Lorentz covariance and the passage from positive-time vectors to
  rotations are not touched. The bridge stays open.
-/

set_option autoImplicit false

namespace MassGap.ShiftVector

open Real Filter Topology MeasureTheory Set
open scoped NNReal ENNReal
open MassGap.BandShell (shell)
open MassGap.ShellMeasure (klWeight measurable_shell)
open MassGap.ShellJoint (JointData aB UB)
open MassGap.ShellTranslate (spatial)
open MassGap.ShellDensity (DyadicDini nu lam lamF dy)
open MassGap.ShellLorentz (klSec psq klJoint KLJointRep psq_nonneg continuous_psq klWeight_fin
  klSec_Iio)
open MassGap.MomentumSector (lf inner_powT_U_eq_nu powT_eq_cfc kpow)
open MassGap.LorentzConverse (ext_laplace_fourier nu_Iio0 nu_time tiltDens tiltDens_coe
  measurable_tiltDens isFiniteMeasure_tilt)
open MassGap.ContinuumTimeGroup (powT powT_add isSelfAdjoint_powT)
open MassGap.ShiftSector (expW expW_le_one shiftBy shiftBy_zero shiftBy_null tiltE tiltJ tiltE_apply
  tiltJ_def tiltJ_klJoint_rect measurable_tiltE_apply KLJointRepAt shift_not_kl)

noncomputable section

/-! ## 1. The vector identity -/

section Vector

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {τ : Fin 4} (J : JointData H (spatial τ))

/-- **The time power commutes with the translations.** DERIVED: `0` the sign of the power. -/
theorem powT_mul_U {t : ℝ} (ht : 0 ≤ t) (x : spatial τ) :
    powT J.a t * J.R.U x = J.R.U x * powT J.a t := by
  rw [powT_eq_cfc J ht]
  exact congrArg Subtype.val (mul_comm (cfc (kpow t) (aB J)) (UB J x))

/-- DERIVED: `0` the sign of the power. -/
theorem U_powT_apply {t : ℝ} (ht : 0 ≤ t) (x : spatial τ) (v : H) :
    J.R.U x (powT J.a t v) = powT J.a t (J.R.U x v) := by
  show (J.R.U x * powT J.a t) v = (powT J.a t * J.R.U x) v
  rw [powT_mul_U J ht x]

/-- **The Dini bound survives the time power.** DERIVED: `0` the sign of the power; `2` the square. -/
theorem dyadicDini_powT {v : H} (hD : DyadicDini J v) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    DyadicDini J (powT J.a t₀ v) := by
  intro j
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
    ((hD j).mul_left (‖powT J.a t₀‖ ^ 2))
  rw [U_powT_apply J ht₀, ← map_sub, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ((powT J.a t₀).le_opNorm _) 2

/-- **The shift on energy × momentum is the tilt by `2t₀`.** DERIVED: `2` as in `expW`. -/
theorem tiltJ_eq_tiltDens (t₀ : ℝ) (ν : Measure (ℝ × (Fin 4 → ℝ))) :
    tiltJ t₀ ν = ν.withDensity fun q => (tiltDens (2 * t₀) q : ℝ≥0∞) := by
  rw [tiltJ_def]
  congr 1
  funext q
  rw [tiltDens_coe]
  rfl

/-- **The correlator of the moved vector**: `⟪a^{t₀} v, a^t U(x) a^{t₀} v⟫ = ⟪v, a^{t + 2t₀} U(x) v⟫`.
DERIVED: `0` the signs of the powers; `2` the two factors `a^{t₀}`. -/
theorem inner_shift (v : H) {t₀ t : ℝ} (ht₀ : 0 ≤ t₀) (ht : 0 ≤ t) (x : spatial τ) :
    inner ℂ (powT J.a t₀ v) (powT J.a t (J.R.U x (powT J.a t₀ v)))
      = inner ℂ v (powT J.a (t + 2 * t₀) (J.R.U x v)) := by
  have e : powT J.a (t + 2 * t₀) = powT J.a t₀ * (powT J.a t * powT J.a t₀) := by
    rw [← powT_add J.hsp ht ht₀, ← powT_add J.hsp ht₀ (add_nonneg ht ht₀)]
    congr 1
    ring
  rw [U_powT_apply J ht₀, e]
  exact (isSelfAdjoint_powT (a := J.a) t₀).isSymmetric _ _

/-- **The joint measure of the moved vector**: `nu(a^{t₀} v) = e^{−2t₀E} · nu(v)`, `t₀ ≥ 0`.
DERIVED: `0` the sign of the time; `2` as in `expW`. -/
theorem nu_powT {v : H} (hD : DyadicDini J v) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    nu J (powT J.a t₀ v) = tiltJ t₀ (nu J v) := by
  have h2 : 0 ≤ 2 * t₀ := by positivity
  haveI : IsFiniteMeasure (tiltJ t₀ (nu J v)) := by
    rw [tiltJ_eq_tiltDens]
    exact isFiniteMeasure_tilt _ (nu_Iio0 J v) h2
  refine ext_laplace_fourier (nu_Iio0 J _) ((shiftBy_null measurable_fst).mpr (nu_Iio0 J v))
    (nu_time J _) ((withDensity_absolutelyContinuous _ _).ae_le (nu_time J v)) fun t ht x => ?_
  rw [← inner_powT_U_eq_nu J (dyadicDini_powT J hD ht₀) ht x, inner_shift J v ht₀ ht.le x,
    inner_powT_U_eq_nu J hD (by positivity) x, tiltJ_eq_tiltDens,
    integral_withDensity_eq_integral_smul (measurable_tiltDens _)]
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  have e : Real.exp (-((t + 2 * t₀) * q.1))
      = ((tiltDens (2 * t₀) q : ℝ≥0) : ℝ) * Real.exp (-(t * q.1)) := by
    show _ = Real.exp (-((2 * t₀) * q.1)) * _
    rw [← Real.exp_add]
    congr 1
    ring
  show lf (t + 2 * t₀) x q = tiltDens (2 * t₀) q • lf t x q
  unfold lf
  rw [NNReal.smul_def, Complex.real_smul, e, Complex.ofReal_mul, mul_assoc]

/-- **The template moves with the vector**: `KLJointRep` at `v` gives `KLJointRepAt` at `a^{t₀} v`.
DERIVED: `0` the sign of the time. -/
theorem klJointRepAt_of_shift {v : H} (hD : DyadicDini J v) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    {ρ : Measure ℝ} (h : KLJointRep J v ρ) : KLJointRepAt J (powT J.a t₀ v) ρ t₀ := by
  obtain ⟨g, hg, hg0, he⟩ := h
  exact ⟨g, hg, hg0, by rw [nu_powT J hD ht₀, he]⟩

end Vector

/-! ## 2. The vector obstruction -/

/-- **The shift does not raise the mass** of a measure on `[0, ∞)`, `t ≥ 0`. DERIVED: `0` the bottom;
`1` the bound of `e^{−x}`. -/
theorem tiltE_univ_le {σ : Measure ℝ} (h0 : σ (Iio 0) = 0) {t : ℝ} (ht : 0 ≤ t) :
    tiltE t σ univ ≤ σ univ := by
  rw [tiltE_apply _ _ MeasurableSet.univ, Measure.restrict_univ, ← lintegral_one]
  refine lintegral_mono_ae ?_
  have hae : ∀ᵐ E ∂σ, 0 ≤ E := by
    rw [ae_iff]
    have e : {E : ℝ | ¬ 0 ≤ E} = Iio 0 := by ext E; simp
    rw [e]
    exact h0
  filter_upwards [hae] with E hE
  exact expW_le_one ht hE

/-- **Finite shell mass**: a finite `ρ` above a positive `m` has `klSec ρ p²` finite at every
`p² ≥ 0`. DERIVED: `0` the signs; `1`, `2` as in `klWeight`. -/
theorem klSec_univ_ne_top {ρ : Measure ℝ} [IsFiniteMeasure ρ] {m : ℝ} (hm : 0 < m)
    (hρ : ρ (Iio m) = 0) {x : ℝ} (hx : 0 ≤ x) : klSec ρ x univ ≠ ⊤ := by
  rw [klSec, Measure.map_apply (measurable_shell x) MeasurableSet.univ, preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  refine ne_top_of_le_ne_top (klWeight_fin hm hρ) (lintegral_mono_ae ?_)
  have hae : ∀ᵐ s ∂ρ, m ≤ s := by
    rw [ae_iff]
    have e : {s : ℝ | ¬ m ≤ s} = Iio m := by ext s; simp
    rw [e]
    exact hρ
  filter_upwards [hae] with s hs
  have h0 : 0 < shell s 0 := by
    unfold shell
    exact Real.sqrt_pos.mpr (by linarith)
  have h1 : shell s 0 ≤ shell s x := by
    unfold shell
    exact Real.sqrt_le_sqrt (by linarith)
  unfold klWeight
  exact ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le (by positivity) (by linarith))

/-- **An atom lies above the bottom.** DERIVED: no numeral. -/
theorem atom_ge {ρ : Measure ℝ} {m a : ℝ} (hρ : ρ (Iio m) = 0) (ha : ρ {a} ≠ 0) : m ≤ a := by
  by_contra h
  have hlt : a < m := lt_of_not_ge h
  exact ha (measure_mono_null (singleton_subset_iff.mpr (show a ∈ Iio m from hlt)) hρ)

/-- **Disintegration on a rectangle**: equal shifted Källén–Lehmann joint measures have, for each
measurable `B`, equal weighted sector masses `λ`-almost everywhere. DERIVED: no numeral. -/
theorem rect_ae {τ : Fin 4} {ρ ρ' : Measure ℝ} [SFinite ρ] [SFinite ρ']
    {g g' : (Fin 4 → ℝ) → ℝ≥0} (hg : Measurable g) (hg' : Measurable g') {t t' : ℝ}
    (h : tiltJ t (klJoint τ ρ g) = tiltJ t' (klJoint τ ρ' g')) {B : Set ℝ} (hB : MeasurableSet B) :
    ∀ᵐ p ∂(lam τ), (g p : ℝ≥0∞) * tiltE t (klSec ρ (psq p)) B
      = (g' p : ℝ≥0∞) * tiltE t' (klSec ρ' (psq p)) B :=
  ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (hg.coe_nnreal_ennreal.mul (measurable_tiltE_apply t ρ hB))
    (hg'.coe_nnreal_ennreal.mul (measurable_tiltE_apply t' ρ' hB))
    fun A hA _ => (tiltJ_klJoint_rect τ ρ hg t hA hB).symm.trans
      ((congrArg (fun μ : Measure (ℝ × (Fin 4 → ℝ)) => μ (B ×ˢ A)) h).trans
        (tiltJ_klJoint_rect τ ρ' hg' t' hA hB))

/-- **Disintegration uniqueness**: equal shifted Källén–Lehmann joint measures have equal weighted
sectors `λ`-almost everywhere, when the `ρ` side has finite shell mass. DERIVED: `0` the sign of the
time. -/
theorem sector_eq_ae {τ : Fin 4} {ρ ρ' : Measure ℝ} [SFinite ρ] [SFinite ρ']
    {g g' : (Fin 4 → ℝ) → ℝ≥0} (hg : Measurable g) (hg' : Measurable g') {t t' : ℝ} (ht : 0 ≤ t)
    (hfin : ∀ p, klSec ρ (psq p) univ ≠ ⊤)
    (h : tiltJ t (klJoint τ ρ g) = tiltJ t' (klJoint τ ρ' g')) :
    ∀ᵐ p ∂(lam τ), (g p : ℝ≥0∞) • tiltE t (klSec ρ (psq p))
      = (g' p : ℝ≥0∞) • tiltE t' (klSec ρ' (psq p)) := by
  have hall : ∀ᵐ p ∂(lam τ), ∀ q : ℚ, (g p : ℝ≥0∞) * tiltE t (klSec ρ (psq p)) (Iio (q : ℝ))
      = (g' p : ℝ≥0∞) * tiltE t' (klSec ρ' (psq p)) (Iio (q : ℝ)) :=
    ae_all_iff.mpr fun q => rect_ae hg hg' h measurableSet_Iio
  filter_upwards [hall, rect_ae hg hg' h MeasurableSet.univ] with p hp hu
  haveI : IsFiniteMeasure ((g p : ℝ≥0∞) • tiltE t (klSec ρ (psq p))) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top
      (lt_of_le_of_lt (tiltE_univ_le (klSec_Iio ρ (psq p)) ht) (hfin p).lt_top)
  refine ext_of_generate_finite _ (BorelSpace.measurable_eq.trans Real.borel_eq_generateFrom_Iio_rat)
    Real.isPiSystem_Iio_rat (fun s hs => ?_) ?_
  · simp only [mem_iUnion, mem_singleton_iff] at hs
    obtain ⟨q, rfl⟩ := hs
    simp only [Measure.smul_apply, smul_eq_mul]
    exact hp q
  · simp only [Measure.smul_apply, smul_eq_mul]
    exact hu

/-- **`λ` charges every open set meeting `p_τ = 0`.** DERIVED: `0` the time momentum; `1` the mass of
`δ₀`. -/
theorem lam_open_ne_zero (τ : Fin 4) {W : Set (Fin 4 → ℝ)} (hW : IsOpen W) {w : Fin 4 → ℝ}
    (hw : w ∈ W) (hwτ : w τ = 0) : lam τ W ≠ 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW w hw
  intro h
  have hb : lam τ (Metric.ball w ε) = 0 := measure_mono_null hball h
  rw [lam, ball_pi _ hε, Measure.pi_pi, Finset.prod_eq_zero_iff] at hb
  obtain ⟨j, -, hj⟩ := hb
  unfold lamF at hj
  split_ifs at hj with hjτ
  · subst hjτ
    rw [Measure.dirac_apply_of_mem (by rw [hwτ]; exact Metric.mem_ball_self hε)] at hj
    exact one_ne_zero hj
  · exact (Metric.measure_ball_pos volume _ hε).ne' hj

/-- **Two values of `p²`**: an open set around `0` holds two points of a `λ`-full set with different
`p²`. DERIVED: `0` the origin and the time momentum; `1` the unit vector; `2` the square. -/
theorem exists_two_psq {τ : Fin 4} {P : (Fin 4 → ℝ) → Prop} (hP : ∀ᵐ p ∂(lam τ), P p)
    {V : Set (Fin 4 → ℝ)} (hV : IsOpen V) (h0 : (0 : Fin 4 → ℝ) ∈ V) :
    ∃ p q, P p ∧ P q ∧ p ∈ V ∧ q ∈ V ∧ psq p ≠ psq q := by
  obtain ⟨j, hj⟩ := exists_ne τ
  have hcont : Continuous fun s : ℝ => s • (Pi.single j (1 : ℝ) : Fin 4 → ℝ) :=
    continuous_id.smul continuous_const
  have hnhds : ∀ᶠ s in 𝓝 (0 : ℝ), s • (Pi.single j (1 : ℝ) : Fin 4 → ℝ) ∈ V :=
    (hcont.tendsto 0).eventually_mem (hV.mem_nhds (by rw [zero_smul]; exact h0))
  obtain ⟨s, hsV, hs⟩ :=
    ((hnhds.filter_mono nhdsWithin_le_nhds).and (eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
  have hs0 : (0 : ℝ) < s := hs
  have hzτ : (s • (Pi.single j (1 : ℝ) : Fin 4 → ℝ)) τ = 0 := by
    simp [Pi.single_apply, hj.symm]
  have hzj : (s • (Pi.single j (1 : ℝ) : Fin 4 → ℝ)) j = s := by simp
  have hpz : 0 < psq (s • (Pi.single j (1 : ℝ) : Fin 4 → ℝ)) := by
    have h1 : (s • (Pi.single j (1 : ℝ) : Fin 4 → ℝ)) j ^ 2
        ≤ psq (s • (Pi.single j (1 : ℝ) : Fin 4 → ℝ)) :=
      Finset.single_le_sum (f := fun i => (s • (Pi.single j (1 : ℝ) : Fin 4 → ℝ)) i ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    rw [hzj] at h1
    exact lt_of_lt_of_le (pow_pos hs0 2) h1
  obtain ⟨c, hc0, hcz⟩ := exists_between hpz
  have hpsq0 : psq 0 = 0 := by simp [psq]
  have hnull : lam τ {p | P p}ᶜ = 0 := by
    rw [compl_setOf]
    exact ae_iff.mp hP
  have hW1 : IsOpen (V ∩ psq ⁻¹' Iio c) := hV.inter (isOpen_Iio.preimage continuous_psq)
  have hW2 : IsOpen (V ∩ psq ⁻¹' Ioi c) := hV.inter (isOpen_Ioi.preimage continuous_psq)
  obtain ⟨p, ⟨hpV, hpc⟩, hpP⟩ := nonempty_of_measure_ne_zero
    (μ := lam τ) (s := (V ∩ psq ⁻¹' Iio c) ∩ {p | P p}) (by
      rw [measure_inter_conull hnull]
      exact lam_open_ne_zero τ hW1 ⟨h0, show psq 0 < c by rw [hpsq0]; exact hc0⟩ rfl)
  obtain ⟨q, ⟨hqV, hqc⟩, hqP⟩ := nonempty_of_measure_ne_zero
    (μ := lam τ) (s := (V ∩ psq ⁻¹' Ioi c) ∩ {p | P p}) (by
      rw [measure_inter_conull hnull]
      exact lam_open_ne_zero τ hW2 ⟨hsV, hcz⟩ hzτ)
  have hpc' : psq p < c := hpc
  have hqc' : c < psq q := hqc
  exact ⟨p, q, hpP, hqP, hpV, hqV, (hpc'.trans hqc').ne⟩

/-- DERIVED: `1` the unit scalar. -/
theorem measure_smul_cancel {μ ν : Measure ℝ} {c d : ℝ≥0∞} (hc : c ≠ 0) (hc' : c ≠ ⊤)
    (h : c • μ = d • ν) : μ = (c⁻¹ * d) • ν := by
  rw [mul_smul, ← h, smul_smul, ENNReal.inv_mul_cancel hc hc', one_smul]

section VectorObstruction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {τ : Fin 4} (J : JointData H (spatial τ))

/-- **The vector obstruction.** If `u` satisfies the template at `t₀ > 0` with a finite `ρ` above a
positive `m` that has atoms at `a ≠ b`, then `u` satisfies the time-zero template `KLJointRep` for no
s-finite `ρ'`. DERIVED: `0` the zero shift, the bottom and the sign of the time. -/
theorem not_klJointRep_of_at (u : H) {ρ : Measure ℝ} [IsFiniteMeasure ρ] {m a b t₀ : ℝ}
    (hm : 0 < m) (hρ : ρ (Iio m) = 0) (hab : a ≠ b) (ha : ρ {a} ≠ 0) (hb : ρ {b} ≠ 0)
    (ht₀ : 0 < t₀) (hAt : KLJointRepAt J u ρ t₀) (ρ' : Measure ℝ) [SFinite ρ'] :
    ¬ KLJointRep J u ρ' := by
  rintro ⟨g', hg', -, hrep⟩
  obtain ⟨g, hg, hg0, hat⟩ := hAt
  have hEq : tiltJ t₀ (klJoint τ ρ g) = tiltJ 0 (klJoint τ ρ' g') := by
    rw [← hat, hrep]
    exact (shiftBy_zero _ _).symm
  have hae := sector_eq_ae hg.measurable hg'.measurable ht₀.le
    (fun p => klSec_univ_ne_top hm hρ (psq_nonneg p)) hEq
  obtain ⟨p, q, hp, hq, hpV, hqV, hpq⟩ := exists_two_psq hae
    (isOpen_ne_fun hg (continuous_const : Continuous fun _ : Fin 4 → ℝ => (0 : ℝ≥0)))
    (show g 0 ≠ 0 from hg0)
  have e0 : ∀ σ : Measure ℝ, tiltE 0 σ = σ := fun σ => shiftBy_zero id σ
  rw [e0] at hp hq
  have hpV' : (g p : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hpV
  have hqV' : (g q : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hqV
  have ha' : 0 < a := hm.trans_le (atom_ge hρ ha)
  have hb' : 0 < b := hm.trans_le (atom_ge hρ hb)
  have hp0 := psq_nonneg p
  have hq0 := psq_nonneg q
  exact shift_not_kl hab hpq ht₀.ne' ha (measure_ne_top ρ _) hb (measure_ne_top ρ _)
    (by linarith) (by linarith) (by linarith) (by linarith) ρ' _ _
    (measure_smul_cancel hpV' ENNReal.coe_ne_top hp)
    (measure_smul_cancel hqV' ENNReal.coe_ne_top hq)

/-- **A moved two-atom vector leaves the time-zero template**: if `v` satisfies `DyadicDini` and
`KLJointRep J v ρ` with a finite `ρ` above a positive `m` with atoms at `a ≠ b`, then for `t₀ > 0` the
vector `a^{t₀} v` satisfies `KLJointRep` for no s-finite `ρ'`. DERIVED: `0` the bottom and the sign of
the time. -/
theorem shift_vector_not_kl {v : H} (hD : DyadicDini J v) {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    {m a b t₀ : ℝ} (hm : 0 < m) (hρ : ρ (Iio m) = 0) (hab : a ≠ b) (ha : ρ {a} ≠ 0)
    (hb : ρ {b} ≠ 0) (ht₀ : 0 < t₀) (hv : KLJointRep J v ρ) (ρ' : Measure ℝ) [SFinite ρ'] :
    ¬ KLJointRep J (powT J.a t₀ v) ρ' :=
  not_klJointRep_of_at J _ hm hρ hab ha hb ht₀ (klJointRepAt_of_shift J hD ht₀.le hv) ρ'

end VectorObstruction

end

end MassGap.ShiftVector

#print axioms MassGap.ShiftVector.powT_mul_U
#print axioms MassGap.ShiftVector.U_powT_apply
#print axioms MassGap.ShiftVector.dyadicDini_powT
#print axioms MassGap.ShiftVector.tiltJ_eq_tiltDens
#print axioms MassGap.ShiftVector.inner_shift
#print axioms MassGap.ShiftVector.nu_powT
#print axioms MassGap.ShiftVector.klJointRepAt_of_shift
#print axioms MassGap.ShiftVector.tiltE_univ_le
#print axioms MassGap.ShiftVector.klSec_univ_ne_top
#print axioms MassGap.ShiftVector.atom_ge
#print axioms MassGap.ShiftVector.rect_ae
#print axioms MassGap.ShiftVector.sector_eq_ae
#print axioms MassGap.ShiftVector.lam_open_ne_zero
#print axioms MassGap.ShiftVector.exists_two_psq
#print axioms MassGap.ShiftVector.measure_smul_cancel
#print axioms MassGap.ShiftVector.not_klJointRep_of_at
#print axioms MassGap.ShiftVector.shift_vector_not_kl
