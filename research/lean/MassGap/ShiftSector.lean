import Mathlib
import MassGap.StieltjesSector

/-!
# MassGap.ShiftSector — the Källén–Lehmann template for vectors at strictly positive time

Reconstruction is argued to supply vectors at positive time, carrying the factor `e^{−2t₀E}` on their
energy measure; the identity `nu(a^{t₀}v) = e^{−2t₀E}·nu(v)` is not proved here. With two masses that
factor leaves the form `g(p) · klSec ρ p²`. This module proves
the obstruction, states the corrected template, removes the shift, and carries the gap read through.
Declarations are in the namespace `MassGap.ShiftSector`.

DERIVED (module-wide): `0` the bottom of the rates, the zero time shift and the zero momentum; `1` the
unit of the density and the bound of `e^{−x}`, `x ≥ 0`; `2` the shift `e^{−2t₀E}` (a vector at time
`t₀` enters its two-point function twice) and the square; `Fin 4` the spacetime index. CHOSEN
(counterexample only): the atoms `1`, `4` of `exRho` (rates `1`, `2`), each of mass `1`; any two distinct positive
atoms serve (`shift_not_kl`). No chosen number enters a template or a consumer.

## 1. The obstruction (proved)

`expW t E = e^{−2tE}`; `shiftBy e t μ = e^{−2t e(a)} · μ`, with `tiltE` on energies and `tiltJ` on
energy × momentum.

* `shift_not_kl`: if `ρ` has atoms at `a ≠ b` of finite non-zero mass, above `−x` and `−y`, with
  `x ≠ y` and `t ≠ 0`, there is no `ρ'` and no scalars `c_x`, `c_y` with
  `e^{−2tE} klSec ρ z = c_z klSec ρ' z` at `z = x, y`. Two values of `p²` suffice, and `ρ'` is arbitrary.
* `shift_family_not_kl`: the same with one `g(p)` on a set holding two values of `p²`.
* `not_stieltjesCov_shift`: for finite `ρ` above `−p²`, the rescaled shifted family fails `StieltjesCov`.
* `exRho`, `exRho_not_kl`, `exRho_not_stieltjesCov`: the explicit case `ρ = δ₁ + δ₄`.
* `tilt_klSec_dirac`: with one atom the shifted sector is of the form `c klSec ρ`, so two atoms are
  needed.

## 2. The corrected template (stated, and tied to `KLJointRep`)

* `KLJointRepAt J u ρ t₀`: some continuous `g`, `g 0 ≠ 0`, with `nu J u = e^{−2t₀E} · klJoint τ ρ g`.
* `KLJointRepShift J u ρ`: the same for some `t₀ ≥ 0`.
* `klJointRepAt_zero`: `KLJointRepAt J u ρ 0 ↔ KLJointRep J u ρ`.

## 3. Shift removal (proved)

* `shiftBy_neg`, `shiftBy_neg'`, `shiftBy_eq_iff`: `e^{2t₀E}` inverts `e^{−2t₀E}`.
* `klJointRepAt_iff_shiftOff`: the template at `t₀` is the plain `klJoint` form of `e^{2t₀E} · nu`.
* `stieltjesCov_shift_iff`: §3 of `StieltjesSector` on the shift-removed family: it is regular and
  covariant if and only if the family itself is `e^{−2t₀E} klSec ρ p²`.
* `sectorShift_of_stieltjes`, `klJointRepAt_of_stieltjes`: §4 of `StieltjesSector`: if `m = g c λ` and
  `c(p) e^{2t₀E} σ_p` is regular and covariant on a set of full `λ` measure, the vector satisfies
  `KLJointRepAt` with one finite `ρ`.
* `nu_rect`, `tiltJ_klJoint_rect`: the two joint measures on rectangles.

## 4. The consumer (proved)

`e^{−2t₀E}` is strictly positive, so `shiftBy` keeps the null sets (`shiftBy_null`).

* `specBottom_tiltE`: the bottom of the spectrum of an energy measure is unchanged.
* `shell_rate_shift`: the read of the shifted sector still tends to `√(M2 + p²)`. No sign of `t` is
  used: the shift moves `τ` to `τ + 2t`, which does not change the rate.
* `windowed_tiltJ`, `zeroDensity_shift`: for `t ≥ 0`, the zero-momentum density of the shifted measure
  is the shifted density.
* `clay_zero_momentum_shift`: every conclusion of `ShellLorentz.clay_zero_momentum_kl`, under
  `nu J u = e^{−2t₀E} klJoint τ ρ g`, `t₀ ≥ 0`, with zero-momentum density `e^{−2t₀E} klSec (g(0)ρ) 0`.
  `clay_zero_momentum_shiftRep` states it under `KLJointRepShift`.

Foundational footprint only (`#print axioms` at the end).

## What does not follow

Assumed, and whether shown non-vacuous:

* `KLJointRepAt` and `KLJointRepShift` are hypotheses. They are not shown for any vector, on the tree
  or for a general `J`, at any `t₀`, beyond what `KLJointRep` gives at `t₀ = 0`, and `KLJointRep` itself
  is not discharged for any composite vector. No theorem here says a vector at time `t₀` has
  `nu` equal to `e^{−2t₀E}` times the `nu` of its time-zero vector. That identity is the reason for the
  template; it is argued, not proved.
* `StieltjesCov` for the shift-removed family, in `klJointRepAt_of_stieltjes`. Non-vacuous for
  families of measures: by `stieltjesCov_shift_iff` it holds of `e^{−2t₀E} klSec ρ p²` after removal. Not
  shown for the sectors of any vector. Removal does not help derive it: the cosine transform of
  `StieltjesSector` needs the correlator down to `t = 0`, and the correlator of a positive-time vector
  is known at `t ≥ 2t₀`; the sector `e^{2t₀E} σ_p` is the object that transform would read, and
  whether `e^{2t₀E} σ_p` has a finite first moment is not known, since `ShellReg` is assumed for it.
* The factorization `m = g c λ`, with `g` continuous and `g 0 ≠ 0`, as in `StieltjesSector`: assumed,
  not shown for any vector. Here `c(p)` is the mass of the shifted shell, not of the shift-removed sector.
* `ShellReg` of the shift-removed sectors, `hreg`: assumed. It is stronger than `ShellReg` of `σ_p`,
  because `e^{2t₀E}` grows. Non-vacuous for families only (`shellReg_klSec`).
* In `clay_zero_momentum_shift`: `hρ0`, `SpecBottom ρ M2`, `t₀ ≥ 0`, and the template. `ρ(−∞, 0] = 0`
  and the bottom are not concluded by the Stieltjes route, which gives only `ρ(−∞, −p²] = 0` for
  `p ∈ S`.

Not concluded:

* A vector statement of the obstruction. §1 is about families of measures: it is not proved that a
  vector satisfying `KLJointRepAt` with `t₀ > 0` and two atoms in `ρ` fails `KLJointRep`. That needs the
  uniqueness of the disintegration against `λ` and two values of `p²` in a set of positive `λ` measure.
* The obstruction for `ρ` without two atoms. `shift_not_kl` tests atoms. A continuous `ρ`, or one atom
  plus a continuum, is not treated, although the same ratio argument is expected to apply.
* `t₀` is not fixed by the data here: the template is existential, and whether `t₀` is unique for a
  given vector is not addressed. With one atom the shift is a scalar at each `p` (`tilt_klSec_dirac`).
* A sector form of the shifted template as an equivalence. `klJointRepAt_of_stieltjes` gives the
  sector-to-joint direction; the converse disintegration is not built.
* `shell_rate_shift` reads a sector of the form `e^{−2tE} klSec ρ p²`; the passage to `secLaplace` for a
  vector, with the normalization `c(p)`, is not built.
* Rotation invariance, `O4Inv`, Lorentz covariance and the passage from positive-time vectors to
  rotations are not touched. The bridge stays open.
-/

set_option autoImplicit false

namespace MassGap.ShiftSector

open Real Filter Topology MeasureTheory Set
open scoped NNReal ENNReal
open MassGap.BandShell (shell SpecBottom)
open MassGap.ShellMeasure (klWeight measurable_klWeight measurable_shell shell_rate_of_kl)
open MassGap.ShellJoint (JointData)
open MassGap.ShellTranslate (spatial)
open MassGap.ShellDensity (nu lam windowed windowed_Iio ZeroDensity zeroDensity_bottom nu_Iio_prod
  gap_sq_le_of_sector)
open MassGap.ShellGap (gap_rateBottom specBottom_klSector)
open MassGap.ShellLorentz (klSec psq klJoint klMap measurable_klMap continuous_shellP klDens
  KLJointRep kallenLehmann_klSec klJoint_bottom klJoint_zeroDensity klWeight_fin specBottom_smul
  klSec_Iio)
open MassGap.ObserverOSReconstructionS (OSDataS)
open MassGap.MomentumSector (momMarg sector nuSwap map_swap_nuSwap momMarg_compProd_sector)
open MassGap.LorentzStep (measurable_klDens' measurable_klW)
open MassGap.LorentzConverse (klJoint_Iio)
open MassGap.StieltjesSector (ShellReg StieltjesCov stieltjesCov_iff shellReg_klSec lintegral_klSec
  measurable_twoE ae_pos_of_Iic ae_nonneg_of_Iio shell_sq sq_shell lam_ne_zero)

noncomputable section

/-! ## 1. The shift -/

/-- **The time shift of an energy** `e^{−2tE}`. DERIVED: `2` a vector at time `t` enters the two-point
function twice. -/
def expW (t E : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(2 * t * E)))

/-- DERIVED: no numeral. -/
theorem measurable_expW (t : ℝ) : Measurable (expW t) :=
  ENNReal.measurable_ofReal.comp
    (by fun_prop : Continuous fun E : ℝ => Real.exp (-(2 * t * E))).measurable

/-- DERIVED: no numeral. -/
theorem expW_add (s t E : ℝ) : expW s E * expW t E = expW (s + t) E := by
  unfold expW
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2; ring

/-- DERIVED: `0` the zero shift; `1` the unit density. -/
theorem expW_zero (E : ℝ) : expW 0 E = 1 := by simp [expW]

/-- DERIVED: `0` the signs; `1` the bound of `e^{−x}`. -/
theorem expW_le_one {t E : ℝ} (ht : 0 ≤ t) (hE : 0 ≤ E) : expW t E ≤ 1 :=
  ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))

/-- **Two equal shifted products have equal exponents.** DERIVED: `0` the non-zero shift; `2` as in
`expW`. -/
theorem expW_cross {t : ℝ} (ht : t ≠ 0) {A B C D : ℝ}
    (h : expW t A * expW t B = expW t C * expW t D) : A + B = C + D := by
  unfold expW at h
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_eq_ofReal_iff (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le
      (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le, ← Real.exp_add,
    ← Real.exp_add, Real.exp_eq_exp] at h
  have h2 : (2 * t) * (A + B) = (2 * t) * (C + D) := by linarith
  exact mul_left_cancel₀ (mul_ne_zero two_ne_zero ht) h2

section Shift

variable {α : Type*} [MeasurableSpace α] {e : α → ℝ}

/-- **The shifted measure** `e^{−2t e(a)} · μ`. DERIVED: no numeral. -/
def shiftBy (e : α → ℝ) (t : ℝ) (μ : Measure α) : Measure α := μ.withDensity fun a => expW t (e a)

/-- DERIVED: no numeral. -/
theorem shiftBy_shiftBy (he : Measurable e) (s t : ℝ) (μ : Measure α) :
    shiftBy e s (shiftBy e t μ) = shiftBy e (t + s) μ := by
  have hf : ∀ r : ℝ, Measurable fun a => expW r (e a) := fun r => (measurable_expW r).comp he
  unfold shiftBy
  rw [← withDensity_mul _ (hf t) (hf s)]
  congr 1
  funext a
  exact expW_add t s (e a)

/-- DERIVED: `0` the zero shift. -/
theorem shiftBy_zero (e : α → ℝ) (μ : Measure α) : shiftBy e 0 μ = μ := by
  have h : (fun a => expW 0 (e a)) = 1 := by funext a; exact expW_zero _
  rw [shiftBy, h, withDensity_one]

/-- **Removing the shift**: `e^{2tE} e^{−2tE} μ = μ`. DERIVED: no numeral. -/
theorem shiftBy_neg (he : Measurable e) (t : ℝ) (μ : Measure α) :
    shiftBy e (-t) (shiftBy e t μ) = μ := by
  rw [shiftBy_shiftBy he, add_neg_cancel, shiftBy_zero]

/-- DERIVED: no numeral. -/
theorem shiftBy_neg' (he : Measurable e) (t : ℝ) (μ : Measure α) :
    shiftBy e t (shiftBy e (-t) μ) = μ := by
  rw [shiftBy_shiftBy he, neg_add_cancel, shiftBy_zero]

/-- **Shift removal as an equivalence.** DERIVED: no numeral. -/
theorem shiftBy_eq_iff (he : Measurable e) (t : ℝ) (μ ν : Measure α) :
    shiftBy e (-t) μ = ν ↔ μ = shiftBy e t ν :=
  ⟨fun h => by rw [← h, shiftBy_neg' he], fun h => by rw [h, shiftBy_neg he]⟩

/-- **The shift keeps the null sets.** DERIVED: `0` the null value. -/
theorem shiftBy_null (he : Measurable e) {t : ℝ} {μ : Measure α} {A : Set α} :
    shiftBy e t μ A = 0 ↔ μ A = 0 := by
  constructor
  · intro h
    have hac : shiftBy e (-t) (shiftBy e t μ) ≪ shiftBy e t μ :=
      withDensity_absolutelyContinuous _ _
    have := hac h
    rwa [shiftBy_neg he] at this
  · exact fun h => withDensity_absolutelyContinuous _ _ h

/-- DERIVED: no numeral. -/
theorem shiftBy_smul (t : ℝ) (c : ℝ≥0) (μ : Measure α) :
    shiftBy e t (c • μ) = c • shiftBy e t μ := by
  unfold shiftBy
  rw [← Measure.coe_nnreal_smul, withDensity_smul_measure, Measure.coe_nnreal_smul]

end Shift

/-- **The shift on energies.** DERIVED: no numeral. -/
abbrev tiltE (t : ℝ) (σ : Measure ℝ) : Measure ℝ := shiftBy id t σ

/-- **The shift on energy × momentum.** DERIVED: no numeral. -/
abbrev tiltJ (t : ℝ) (ν : Measure (ℝ × (Fin 4 → ℝ))) : Measure (ℝ × (Fin 4 → ℝ)) :=
  shiftBy Prod.fst t ν

/-- DERIVED: no numeral. -/
theorem tiltE_def (t : ℝ) (σ : Measure ℝ) : tiltE t σ = σ.withDensity (expW t) := rfl

/-- DERIVED: no numeral. -/
theorem tiltJ_def (t : ℝ) (ν : Measure (ℝ × (Fin 4 → ℝ))) :
    tiltJ t ν = ν.withDensity fun q => expW t q.1 := rfl

/-- DERIVED: no numeral. -/
theorem tiltE_smul (t : ℝ) (c : ℝ≥0) (σ : Measure ℝ) : tiltE t (c • σ) = c • tiltE t σ :=
  shiftBy_smul t c σ

/-- DERIVED: no numeral. -/
theorem tiltE_tiltE_neg (t : ℝ) (σ : Measure ℝ) : tiltE t (tiltE (-t) σ) = σ :=
  shiftBy_neg' measurable_id t σ

/-- DERIVED: no numeral. -/
theorem tiltE_apply (t : ℝ) (σ : Measure ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    tiltE t σ B = ∫⁻ E in B, expW t E ∂σ := by
  rw [tiltE_def, withDensity_apply _ hB]

/-- DERIVED: no numeral. -/
theorem tiltE_singleton (t : ℝ) (σ : Measure ℝ) (E : ℝ) : tiltE t σ {E} = expW t E * σ {E} := by
  rw [tiltE_def, withDensity_apply _ (measurableSet_singleton E), Measure.restrict_singleton,
    lintegral_smul_measure, lintegral_dirac, smul_eq_mul, mul_comm]

/-! ## 2. The obstruction -/

/-- **An atom of a shell sector** is the atom of `ρ` on that shell, weighted by `1/(2E)`. DERIVED: `0`
the sign of `E`; `2` the square. -/
theorem klSec_singleton (ρ : Measure ℝ) (x : ℝ) {E : ℝ} (hE : 0 < E) :
    klSec ρ x {E} = klWeight x (E ^ 2 - x) * ρ {E ^ 2 - x} := by
  have e : (fun s => shell s x) ⁻¹' {E} = {E ^ 2 - x} := by
    ext s
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro hs
      have hp : 0 < s + x := Real.sqrt_pos.mp (by rw [show Real.sqrt (s + x) = E from hs]; exact hE)
      rw [← hs, sq_shell hp.le]
    · intro hs
      rw [hs]; exact shell_sq hE.le x
  rw [klSec, Measure.map_apply (measurable_shell x) (measurableSet_singleton E), e,
    withDensity_apply _ (measurableSet_singleton _), Measure.restrict_singleton,
    lintegral_smul_measure, lintegral_dirac, smul_eq_mul, mul_comm]

/-- **One atom against one sector**: a shifted sector of the form `c klSec ρ'` fixes `c ρ'{s}`.
DERIVED: `0` the sign of `s + x`. -/
theorem atom_eq {ρ ρ' : Measure ℝ} {t x s : ℝ} {c : ℝ≥0∞} (hs : 0 < s + x)
    (h : tiltE t (klSec ρ x) = c • klSec ρ' x) :
    expW t (shell s x) * ρ {s} = c * ρ' {s} := by
  have hE : 0 < shell s x := Real.sqrt_pos.mpr hs
  have hq : shell s x ^ 2 - x = s := sq_shell hs.le
  have e := congrArg (fun μ : Measure ℝ => μ {shell s x}) h
  simp only [Measure.smul_apply, smul_eq_mul] at e
  rw [tiltE_singleton, klSec_singleton _ _ hE, klSec_singleton _ _ hE, hq] at e
  have hk0 : klWeight x s ≠ 0 := by
    rw [klWeight]; exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hkt : klWeight x s ≠ ⊤ := ENNReal.ofReal_ne_top
  refine (ENNReal.mul_right_inj hk0 hkt).mp ?_
  calc klWeight x s * (expW t (shell s x) * ρ {s})
      = expW t (shell s x) * (klWeight x s * ρ {s}) := by ring
    _ = c * (klWeight x s * ρ' {s}) := e
    _ = klWeight x s * (c * ρ' {s}) := by ring

/-- **The energy difference depends on the momentum**: `√(a + x) − √(b + x)` is injective in `x`, in
the form that two shells do not sum alike. With `P + Q = R + S` and `P² + Q² = R² + S²`, `(P − R)(P − S)`
vanishes. DERIVED: `0` the signs; `2` the square. -/
theorem sum_shell_ne {a b x y : ℝ} (hab : a ≠ b) (hxy : x ≠ y) (h1 : 0 ≤ a + x) (h2 : 0 ≤ b + y)
    (h3 : 0 ≤ b + x) (h4 : 0 ≤ a + y) : shell a x + shell b y ≠ shell b x + shell a y := by
  intro h
  have hP : shell a x ^ 2 = a + x := Real.sq_sqrt h1
  have hQ : shell b y ^ 2 = b + y := Real.sq_sqrt h2
  have hR : shell b x ^ 2 = b + x := Real.sq_sqrt h3
  have hS : shell a y ^ 2 = a + y := Real.sq_sqrt h4
  have hs : shell a x ^ 2 + shell b y ^ 2 = shell b x ^ 2 + shell a y ^ 2 := by
    rw [hP, hQ, hR, hS]; ring
  have hz : (shell a x - shell b x) * (shell a x - shell a y) = 0 := by
    linear_combination
      (shell a x - (shell a x + shell b y + shell b x + shell a y) / 2) * h + (1 / 2) * hs
  rcases mul_eq_zero.mp hz with hc | hc
  · have e : shell a x = shell b x := sub_eq_zero.mp hc
    rw [e] at hP
    exact hab (by linarith)
  · have e : shell a x = shell a y := sub_eq_zero.mp hc
    rw [e] at hP
    exact hxy (by linarith)

/-- **The obstruction.** Let `ρ` have atoms at `a ≠ b`, of finite non-zero mass, and let `x ≠ y` with
`a`, `b` above `−x` and `−y`, and `t ≠ 0`. There is no measure `ρ'` and no pair of scalars with
`e^{−2tE} klSec ρ z = c_z klSec ρ' z` at `z = x` and `z = y`. Cross-multiplying the four atom identities
removes `c` and `ρ'`, leaving `E_a(x) + E_b(y) = E_b(x) + E_a(y)`, which `sum_shell_ne` refutes.
`ρ'` is not assumed finite. DERIVED: `0` the non-zero shift and the signs. -/
theorem shift_not_kl {ρ : Measure ℝ} {a b x y t : ℝ} (hab : a ≠ b) (hxy : x ≠ y) (ht : t ≠ 0)
    (ha0 : ρ {a} ≠ 0) (hat : ρ {a} ≠ ⊤) (hb0 : ρ {b} ≠ 0) (hbt : ρ {b} ≠ ⊤)
    (hax : 0 < a + x) (hby : 0 < b + y) (hbx : 0 < b + x) (hay : 0 < a + y)
    (ρ' : Measure ℝ) (cx cy : ℝ≥0∞)
    (hx : tiltE t (klSec ρ x) = cx • klSec ρ' x) (hy : tiltE t (klSec ρ y) = cy • klSec ρ' y) :
    False := by
  have e1 := atom_eq hax hx
  have e2 := atom_eq hbx hx
  have e3 := atom_eq hay hy
  have e4 := atom_eq hby hy
  have key : expW t (shell a x) * expW t (shell b y) * (ρ {a} * ρ {b})
      = expW t (shell b x) * expW t (shell a y) * (ρ {a} * ρ {b}) := by
    calc expW t (shell a x) * expW t (shell b y) * (ρ {a} * ρ {b})
        = (expW t (shell a x) * ρ {a}) * (expW t (shell b y) * ρ {b}) := by ring
      _ = (cx * ρ' {a}) * (cy * ρ' {b}) := by rw [e1, e4]
      _ = (cx * ρ' {b}) * (cy * ρ' {a}) := by ring
      _ = (expW t (shell b x) * ρ {b}) * (expW t (shell a y) * ρ {a}) := by rw [e2, e3]
      _ = expW t (shell b x) * expW t (shell a y) * (ρ {a} * ρ {b}) := by ring
  have hc := (ENNReal.mul_left_inj (mul_ne_zero ha0 hb0) (ENNReal.mul_ne_top hat hbt)).mp key
  exact sum_shell_ne hab hxy hax.le hby.le hbx.le hay.le (expW_cross ht hc)

/-- **The obstruction with one profile `g(p)`**, on any set holding two values of `p²`. DERIVED: no
numeral. -/
theorem shift_family_not_kl {ρ : Measure ℝ} {a b t : ℝ} {S : Set (Fin 4 → ℝ)}
    {p q : Fin 4 → ℝ} (hp : p ∈ S) (hq : q ∈ S) (hab : a ≠ b) (hpq : psq p ≠ psq q) (ht : t ≠ 0)
    (ha0 : ρ {a} ≠ 0) (hat : ρ {a} ≠ ⊤) (hb0 : ρ {b} ≠ 0) (hbt : ρ {b} ≠ ⊤)
    (hax : 0 < a + psq p) (hby : 0 < b + psq q) (hbx : 0 < b + psq p) (hay : 0 < a + psq q) :
    ¬ ∃ (ρ' : Measure ℝ) (g : (Fin 4 → ℝ) → ℝ≥0),
      ∀ r ∈ S, tiltE t (klSec ρ (psq r)) = (g r : ℝ≥0∞) • klSec ρ' (psq r) := by
  rintro ⟨ρ', g, h⟩
  exact shift_not_kl hab hpq ht ha0 hat hb0 hbt hax hby hbx hay ρ' _ _ (h p hp) (h q hq)

/-- **The shift keeps regularity** for `t ≥ 0`: `e^{−2tE} ≤ 1` on `E > 0`. DERIVED: `0` the sign; `2`
the shell weight. -/
theorem shellReg_shift {σ : Measure ℝ} {t : ℝ} (ht : 0 ≤ t) (c : ℝ≥0) (h : ShellReg σ) :
    ShellReg (c • tiltE t σ) := by
  have hle : ∫⁻ E, ENNReal.ofReal (2 * E) ∂(tiltE t σ) ≤ ∫⁻ E, ENNReal.ofReal (2 * E) ∂σ := by
    rw [tiltE_def, lintegral_withDensity_eq_lintegral_mul _ (measurable_expW t) measurable_twoE]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_pos_of_Iic h.1] with E hE
    simp only [Pi.mul_apply]
    exact mul_le_of_le_one_left' (expW_le_one ht hE.le)
  constructor
  · rw [Measure.coe_nnreal_smul_apply, (shiftBy_null measurable_id).mpr h.1, mul_zero]
  · rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ne_top_of_le_ne_top h.2 hle)

/-- DERIVED: `0` the bottom of `s + p²`. -/
theorem atom_above {ρ : Measure ℝ} {a p2 : ℝ} (ha0 : ρ {a} ≠ 0) (h : ρ (Iic (-p2)) = 0) :
    0 < a + p2 := by
  by_contra hn
  refine ha0 (measure_mono_null ?_ h)
  rintro s rfl
  exact mem_Iic.mpr (by linarith [not_lt.mp hn])

/-- **`StieltjesCov` fails for the rescaled shifted family.** For finite `ρ` above `−p²` with two
atoms, `t > 0`, `c` non-vanishing, and `S` holding two values of `p²`, the family `c(p) e^{−2tE}
klSec ρ p²` is not covariant: regularity holds by `shellReg_shift`, so covariance would give one `ρ'`
through `stieltjesCov_iff`, against `shift_not_kl`. DERIVED: `0` the sign of the shift. -/
theorem not_stieltjesCov_shift {ρ : Measure ℝ} [IsFiniteMeasure ρ] {a b t : ℝ}
    {S : Set (Fin 4 → ℝ)} {p q : Fin 4 → ℝ} (hp : p ∈ S) (hq : q ∈ S) (hab : a ≠ b)
    (hpq : psq p ≠ psq q) (ht : 0 < t) (ha0 : ρ {a} ≠ 0) (hb0 : ρ {b} ≠ 0)
    (h0 : ∀ r ∈ S, ρ (Iic (-psq r)) = 0) {c : (Fin 4 → ℝ) → ℝ≥0} (hc : ∀ r ∈ S, c r ≠ 0) :
    ¬ StieltjesCov S fun r => c r • tiltE t (klSec ρ (psq r)) := by
  intro hcov
  obtain ⟨ρ', -, -, hk⟩ := (stieltjesCov_iff ⟨p, hp⟩ _).mp
    ⟨hcov, fun r hr => shellReg_shift ht.le _ (shellReg_klSec (h0 r hr))⟩
  have hk' : ∀ r ∈ S, tiltE t (klSec ρ (psq r))
      = (((c r)⁻¹ : ℝ≥0) : ℝ≥0∞) • klSec ρ' (psq r) := fun r hr => by
    rw [Measure.coe_nnreal_smul, hk r hr, smul_smul, inv_mul_cancel₀ (hc r hr), one_smul]
  exact shift_not_kl hab hpq ht.ne' ha0 (measure_ne_top _ _) hb0 (measure_ne_top _ _)
    (atom_above ha0 (h0 p hp)) (atom_above hb0 (h0 q hq)) (atom_above hb0 (h0 p hp))
    (atom_above ha0 (h0 q hq)) ρ' _ _ (hk' p hp) (hk' q hq)

/-- **With one atom there is no obstruction**: the shift on `klSec δ_s x` is the scalar `e^{−2tE}` at
the one energy. So the two atoms in `shift_not_kl` are needed. DERIVED: no numeral. -/
theorem tilt_klSec_dirac (s x t : ℝ) :
    tiltE t (klSec (Measure.dirac s) x) = expW t (shell s x) • klSec (Measure.dirac s) x := by
  refine Measure.ext fun A hA => ?_
  rw [tiltE_apply _ _ hA, ← lintegral_indicator hA,
    lintegral_klSec _ _ ((measurable_expW t).indicator hA), Measure.smul_apply, smul_eq_mul,
    ← lintegral_indicator_one hA, lintegral_klSec _ _ (measurable_one.indicator hA),
    lintegral_dirac, lintegral_dirac]
  by_cases h : shell s x ∈ A
  · rw [indicator_of_mem h, indicator_of_mem h, Pi.one_apply, mul_one, mul_comm]
  · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero, mul_zero]

/-- **The explicit two-atom `ρ`.** CHOSEN (counterexample): atoms `1`, `4`, masses `1`, `2`, unit
weights; any two distinct positive atoms serve. -/
def exRho : Measure ℝ := Measure.dirac 1 + Measure.dirac 4

instance : IsFiniteMeasure exRho := by unfold exRho; infer_instance

/-- CHOSEN: the atoms of `exRho`. -/
theorem exRho_one : exRho {1} = 1 := by
  rw [exRho, Measure.add_apply, Measure.dirac_apply_of_mem (mem_singleton _),
    Measure.dirac_apply' _ (measurableSet_singleton _),
    indicator_of_notMem (by norm_num : (4 : ℝ) ∉ ({1} : Set ℝ)), add_zero]

/-- CHOSEN: the atoms of `exRho`. -/
theorem exRho_four : exRho {4} = 1 := by
  rw [exRho, Measure.add_apply, Measure.dirac_apply_of_mem (mem_singleton (4 : ℝ)),
    Measure.dirac_apply' _ (measurableSet_singleton _),
    indicator_of_notMem (by norm_num : (1 : ℝ) ∉ ({4} : Set ℝ)), zero_add]

/-- **The explicit counterexample**: for `ρ = δ₁ + δ₄`, every `t ≠ 0` and any two values `x ≠ y` of
`p² ≥ 0`, no `ρ'`, `c_x`, `c_y` fit. DERIVED: `0` the signs. CHOSEN: `exRho`. -/
theorem exRho_not_kl {x y t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≠ y) (ht : t ≠ 0)
    (ρ' : Measure ℝ) (cx cy : ℝ≥0∞)
    (h1 : tiltE t (klSec exRho x) = cx • klSec ρ' x)
    (h2 : tiltE t (klSec exRho y) = cy • klSec ρ' y) : False :=
  shift_not_kl (a := 1) (b := 4) (by norm_num) hxy ht (by rw [exRho_one]; exact one_ne_zero)
    (by rw [exRho_one]; exact ENNReal.one_ne_top) (by rw [exRho_four]; exact one_ne_zero)
    (by rw [exRho_four]; exact ENNReal.one_ne_top) (by linarith) (by linarith) (by linarith)
    (by linarith) ρ' cx cy h1 h2

/-- DERIVED: `0` the sign of `p²`. -/
theorem exRho_Iic {p2 : ℝ} (hp : 0 ≤ p2) : exRho (Iic (-p2)) = 0 := by
  rw [exRho, Measure.add_apply, Measure.dirac_apply' _ measurableSet_Iic,
    Measure.dirac_apply' _ measurableSet_Iic,
    indicator_of_notMem (by simp only [mem_Iic, not_le]; linarith),
    indicator_of_notMem (by simp only [mem_Iic, not_le]; linarith), add_zero]

/-- **The explicit failure of `StieltjesCov`.** DERIVED: `0` the signs. CHOSEN: `exRho`. -/
theorem exRho_not_stieltjesCov {t : ℝ} (ht : 0 < t) {S : Set (Fin 4 → ℝ)} {p q : Fin 4 → ℝ}
    (hp : p ∈ S) (hq : q ∈ S) (hpq : psq p ≠ psq q) {c : (Fin 4 → ℝ) → ℝ≥0}
    (hc : ∀ r ∈ S, c r ≠ 0) :
    ¬ StieltjesCov S fun r => c r • tiltE t (klSec exRho (psq r)) :=
  not_stieltjesCov_shift (a := 1) (b := 4) hp hq (by norm_num) hpq ht
    (by rw [exRho_one]; exact one_ne_zero) (by rw [exRho_four]; exact one_ne_zero)
    (fun r _ => exRho_Iic (MassGap.ShellLorentz.psq_nonneg r)) hc

/-! ## 3. The corrected template and shift removal -/

/-- **The Stieltjes step on the shift-removed family.** On a non-empty `S`, the family
`e^{2tE} μ p` is regular and covariant if and only if one finite `ρ` above `−p²` gives
`μ p = e^{−2tE} klSec ρ p²`. DERIVED: `0` the bottom. -/
theorem stieltjesCov_shift_iff {S : Set (Fin 4 → ℝ)} (hS : S.Nonempty) (t : ℝ)
    (μ : (Fin 4 → ℝ) → Measure ℝ) :
    (StieltjesCov S (fun p => tiltE (-t) (μ p)) ∧ ∀ p ∈ S, ShellReg (tiltE (-t) (μ p))) ↔
      ∃ ρ : Measure ℝ, IsFiniteMeasure ρ ∧ (∀ p ∈ S, ρ (Iic (-psq p)) = 0) ∧
        ∀ p ∈ S, tiltE t (klSec ρ (psq p)) = μ p := by
  rw [stieltjesCov_iff hS]
  refine exists_congr fun ρ => and_congr_right fun _ => and_congr_right fun _ =>
    forall₂_congr fun p _ => ?_
  exact eq_comm.trans ((shiftBy_eq_iff measurable_id t _ _).trans eq_comm)

/-- **The joint integral of a Källén–Lehmann measure.** DERIVED: no numeral. -/
theorem lintegral_klJoint (τ : Fin 4) (ρ : Measure ℝ) [SFinite ρ] {g : (Fin 4 → ℝ) → ℝ≥0}
    (hg : Measurable g) {h : ℝ × (Fin 4 → ℝ) → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ q, h q ∂(klJoint τ ρ g)
      = ∫⁻ p, (g p : ℝ≥0∞) * ∫⁻ E, h (E, p) ∂(klSec ρ (psq p)) ∂(lam τ) := by
  have hc : Measurable fun q => h (klMap q) := hh.comp measurable_klMap
  rw [klJoint, lintegral_map hh measurable_klMap,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_klDens' hg) hc,
    lintegral_prod (klDens g * fun q => h (klMap q)) ((measurable_klDens' hg).mul hc).aemeasurable]
  refine lintegral_congr fun p => ?_
  have hE : Measurable fun E : ℝ => h (E, p) := hh.comp (measurable_id.prodMk measurable_const)
  have hk : Measurable fun s => klWeight (psq p) s * h (shell s (psq p), p) :=
    (measurable_klWeight _).mul (hE.comp (measurable_shell _))
  rw [lintegral_klSec _ _ hE, ← lintegral_const_mul _ hk]
  refine lintegral_congr fun s => ?_
  simp only [Pi.mul_apply, klDens, klMap, mul_assoc]

/-- **The shifted joint measure on a rectangle.** DERIVED: no numeral. -/
theorem tiltJ_klJoint_rect (τ : Fin 4) (ρ : Measure ℝ) [SFinite ρ] {g : (Fin 4 → ℝ) → ℝ≥0}
    (hg : Measurable g) (t : ℝ) {A : Set (Fin 4 → ℝ)} {B : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    tiltJ t (klJoint τ ρ g) (B ×ˢ A)
      = ∫⁻ p in A, (g p : ℝ≥0∞) * tiltE t (klSec ρ (psq p)) B ∂(lam τ) := by
  have hS := hB.prod hA
  have hf : Measurable fun q : ℝ × (Fin 4 → ℝ) => expW t q.1 :=
    (measurable_expW t).comp measurable_fst
  rw [tiltJ_def, withDensity_apply _ hS, ← lintegral_indicator hS,
    lintegral_klJoint τ ρ hg (hf.indicator hS), ← lintegral_indicator hA]
  refine lintegral_congr fun p => ?_
  by_cases hp : p ∈ A
  · rw [indicator_of_mem hp, tiltE_apply _ _ hB, ← lintegral_indicator hB]
    congr 1
    refine lintegral_congr fun E => ?_
    by_cases hE : E ∈ B
    · rw [indicator_of_mem (mk_mem_prod hE hp), indicator_of_mem hE]
    · rw [indicator_of_notMem (fun h => hE h.1), indicator_of_notMem hE]
  · simp [hp]

/-- **The shifted shell mass is measurable in the momentum.** DERIVED: no numeral. -/
theorem measurable_tiltE_apply (t : ℝ) (ρ : Measure ℝ) [SFinite ρ] {B : Set ℝ}
    (hB : MeasurableSet B) : Measurable fun p => tiltE t (klSec ρ (psq p)) B := by
  have e : ∀ p : Fin 4 → ℝ, tiltE t (klSec ρ (psq p)) B
      = ∫⁻ s, klWeight (psq p) s * B.indicator (expW t) (shell s (psq p)) ∂ρ := fun p => by
    rw [tiltE_apply _ _ hB, ← lintegral_indicator hB,
      lintegral_klSec _ _ ((measurable_expW t).indicator hB)]
  simp only [e]
  exact (measurable_klW.mul (((measurable_expW t).indicator hB).comp
    continuous_shellP.measurable)).lintegral_prod_right'

section Vector

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {τ : Fin 4} (J : JointData H (spatial τ))

/-- **The template at time `t₀`** (a named hypothesis): the joint measure of `u` is `e^{−2t₀E}` times
the Källén–Lehmann measure of `ρ` with a continuous profile `g`, `g(0) ≠ 0`. DERIVED: `0` the zero
momentum. -/
def KLJointRepAt (u : H) (ρ : Measure ℝ) (t₀ : ℝ) : Prop :=
  ∃ g : (Fin 4 → ℝ) → ℝ≥0, Continuous g ∧ g 0 ≠ 0 ∧ nu J u = tiltJ t₀ (klJoint τ ρ g)

/-- **The corrected template** (a named hypothesis): `KLJointRepAt` at some time `t₀ ≥ 0`. DERIVED: `0`
the sign of the time. -/
def KLJointRepShift (u : H) (ρ : Measure ℝ) : Prop := ∃ t₀ : ℝ, 0 ≤ t₀ ∧ KLJointRepAt J u ρ t₀

/-- **Time zero recovers the old template exactly.** DERIVED: `0` the zero shift. -/
theorem klJointRepAt_zero (u : H) (ρ : Measure ℝ) : KLJointRepAt J u ρ 0 ↔ KLJointRep J u ρ := by
  unfold KLJointRepAt KLJointRep
  simp only [shiftBy_zero]

/-- DERIVED: `0` the zero shift. -/
theorem klJointRepShift_of_rep (u : H) {ρ : Measure ℝ} (h : KLJointRep J u ρ) :
    KLJointRepShift J u ρ :=
  ⟨0, le_rfl, (klJointRepAt_zero J u ρ).mpr h⟩

/-- **The template at `t₀` is the old form of the shift-removed measure** `e^{2t₀E} · nu`. DERIVED: `0`
the zero momentum. -/
theorem klJointRepAt_iff_shiftOff (u : H) (ρ : Measure ℝ) (t₀ : ℝ) :
    KLJointRepAt J u ρ t₀ ↔ ∃ g : (Fin 4 → ℝ) → ℝ≥0, Continuous g ∧ g 0 ≠ 0 ∧
      tiltJ (-t₀) (nu J u) = klJoint τ ρ g := by
  unfold KLJointRepAt
  simp only [shiftBy_eq_iff measurable_fst]

/-- **The joint measure on a rectangle**, through the sectors. DERIVED: no numeral. -/
theorem nu_rect (u : H) {A : Set (Fin 4 → ℝ)} {B : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) : nu J u (B ×ˢ A) = ∫⁻ p in A, sector J u p B ∂(momMarg J u) := by
  rw [← map_swap_nuSwap J u, Measure.map_apply measurable_swap (hB.prod hA),
    Set.preimage_swap_prod, ← momMarg_compProd_sector J u, Measure.compProd_apply_prod hA hB]

/-- **The sectors of the shifted template from Stieltjes covariance.** If `m = g c λ` and the
shift-removed rescaled sectors are regular and covariant on a set `S` of full `λ` measure, there is one
finite `ρ` above `−p²` with `c(p) σ_p = e^{−2t₀E} klSec ρ p²` on `S`. DERIVED: `0` the bottom. -/
theorem sectorShift_of_stieltjes (u : H) {c : (Fin 4 → ℝ) → ℝ≥0} {S : Set (Fin 4 → ℝ)} {t₀ : ℝ}
    (hS : ∀ᵐ p ∂(lam τ), p ∈ S)
    (hcov : StieltjesCov S fun p => c p • tiltE (-t₀) (sector J u p))
    (hreg : ∀ p ∈ S, ShellReg (c p • tiltE (-t₀) (sector J u p))) :
    ∃ ρ : Measure ℝ, IsFiniteMeasure ρ ∧ (∀ p ∈ S, ρ (Iic (-psq p)) = 0) ∧
      ∀ p ∈ S, tiltE t₀ (klSec ρ (psq p)) = c p • (sector J u p : Measure ℝ) := by
  haveI : (ae (lam τ)).NeBot := ae_neBot.mpr (lam_ne_zero τ)
  obtain ⟨p₀, hp₀⟩ := hS.exists
  obtain ⟨ρ, hfin, h0, hk⟩ := (stieltjesCov_iff ⟨p₀, hp₀⟩ _).mp ⟨hcov, hreg⟩
  refine ⟨ρ, hfin, h0, fun p hp => ?_⟩
  rw [hk p hp, tiltE_smul, tiltE_tiltE_neg]

/-- **The shifted template from Stieltjes covariance.** The route of `StieltjesSector` §3 and §4, run
on `c(p) e^{2t₀E} σ_p`. The density of `m` against `g` is `c`, the mass of the shifted shell. DERIVED:
`0` the zero momentum and the bottom. -/
theorem klJointRepAt_of_stieltjes (u : H) {g c : (Fin 4 → ℝ) → ℝ≥0} (hg : Continuous g)
    (hg0 : g 0 ≠ 0) {S : Set (Fin 4 → ℝ)} {t₀ : ℝ}
    (hm : momMarg J u = (lam τ).withDensity fun p => (g p : ℝ≥0∞) * c p)
    (hS : ∀ᵐ p ∂(lam τ), p ∈ S)
    (hcov : StieltjesCov S fun p => c p • tiltE (-t₀) (sector J u p))
    (hreg : ∀ p ∈ S, ShellReg (c p • tiltE (-t₀) (sector J u p))) :
    ∃ ρ : Measure ℝ, IsFiniteMeasure ρ ∧ (∀ p ∈ S, ρ (Iic (-psq p)) = 0) ∧
      KLJointRepAt J u ρ t₀ := by
  obtain ⟨ρ, hfin, h0, hk⟩ := sectorShift_of_stieltjes J u hS hcov hreg
  refine ⟨ρ, hfin, h0, g, hg, hg0, ?_⟩
  have hgm : Measurable fun p => (g p : ℝ≥0∞) := (ENNReal.continuous_coe.comp hg).measurable
  have hd : Measurable fun p => (g p : ℝ≥0∞) * tiltE t₀ (klSec ρ (psq p)) univ :=
    hgm.mul (measurable_tiltE_apply t₀ ρ MeasurableSet.univ)
  have hmass : ∀ p ∈ S, tiltE t₀ (klSec ρ (psq p)) univ = c p := fun p hp => by
    rw [hk p hp, Measure.coe_nnreal_smul_apply, measure_univ, mul_one]
  have hm' : momMarg J u
      = (lam τ).withDensity fun p => (g p : ℝ≥0∞) * tiltE t₀ (klSec ρ (psq p)) univ := by
    rw [hm]
    refine withDensity_congr_ae ?_
    filter_upwards [hS] with p hp
    rw [hmass p hp]
  refine Measure.ext_prod fun {B A} hB hA => ?_
  rw [nu_rect J u hA hB, hm', setLIntegral_withDensity_eq_setLIntegral_mul _ hd
    ((sector J u).measurable_coe hB) hA, tiltJ_klJoint_rect τ ρ hg.measurable t₀ hA hB]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hS] with p hp
  simp only [Pi.mul_apply]
  rw [hk p hp, Measure.coe_nnreal_smul_apply, Measure.coe_nnreal_smul_apply, measure_univ, mul_one,
    mul_assoc]

end Vector

/-! ## 4. The consumer -/

/-- **The shift keeps the bottom of the spectrum.** DERIVED: `0` the null value. -/
theorem specBottom_tiltE (t : ℝ) (σ : Measure ℝ) (M : ℝ) :
    SpecBottom (tiltE t σ) M ↔ SpecBottom σ M := by
  have n : ∀ A : Set ℝ, tiltE t σ A = 0 ↔ σ A = 0 := fun A => shiftBy_null measurable_id
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(n _).mp h1, fun ε hε => pos_iff_ne_zero.mpr fun h0 => (h2 ε hε).ne' ((n _).mpr h0)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(n _).mpr h1, fun ε hε => pos_iff_ne_zero.mpr fun h0 => (h2 ε hε).ne' ((n _).mp h0)⟩

/-- **The shifted read has the same rate.** The read of `e^{−2tE} klSec ρ p²` at `τ` is the read of
`klSec ρ p²` at `τ + 2t`, and `(τ + 2t)/τ → 1`. DERIVED: `0` the signs and the limit of `2t/τ`; `1` the
limit of the ratio; `2` as in `expW`. -/
theorem shell_rate_shift {ρ : Measure ℝ} [IsFiniteMeasure ρ] {M2 p2 t : ℝ} (hb : SpecBottom ρ M2)
    (hp : 0 ≤ p2) (hM : 0 < M2 + p2) {C : ℝ → ℝ}
    (hC : ∀ τ, 0 < τ → C τ = ∫ E, Real.exp (-(τ * E)) ∂(tiltE t (klSec ρ p2))) :
    Tendsto (fun τ => -Real.log (C τ) / τ) atTop (𝓝 (shell M2 p2)) := by
  let C₀ : ℝ → ℝ := fun τ => ∫ E, Real.exp (-(τ * E)) ∂(klSec ρ p2)
  have h0 : Tendsto (fun τ => -Real.log (C₀ τ) / τ) atTop (𝓝 (shell M2 p2)) :=
    shell_rate_of_kl (kallenLehmann_klSec ρ) hb hp hM fun _ _ => rfl
  have hs : Tendsto (fun τ : ℝ => τ + 2 * t) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have h1 := h0.comp hs
  have hr : Tendsto (fun τ : ℝ => 1 + (2 * t) / τ) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
  have h2 := h1.mul hr
  rw [add_zero, mul_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0, eventually_gt_atTop (-(2 * t))] with τ hτ hτ'
  have hτ2 : τ + 2 * t ≠ 0 := by linarith
  have hCe : C τ = C₀ (τ + 2 * t) := by
    rw [hC τ hτ, tiltE_def, integral_withDensity_eq_integral_toReal_smul (measurable_expW t)
      (Eventually.of_forall fun E => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun E => ?_)
    simp only [expW, smul_eq_mul]
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, ← Real.exp_add]
    congr 1; ring
  simp only [Function.comp_apply]
  rw [hCe]
  field_simp

/-- **The window sees the shift.** DERIVED: `0` the zero momentum. -/
theorem windowed_tiltJ (ν : Measure (ℝ × (Fin 4 → ℝ))) (t ε : ℝ) :
    windowed (tiltJ t ν) ε = tiltE t (windowed ν ε) := by
  have hW : MeasurableSet ((univ : Set ℝ) ×ˢ Metric.ball (0 : Fin 4 → ℝ) ε) :=
    MeasurableSet.univ.prod Metric.isOpen_ball.measurableSet
  refine Measure.ext fun A hA => ?_
  rw [tiltE_apply _ _ hA, windowed, windowed, Measure.map_apply measurable_fst hA, tiltJ_def,
    restrict_withDensity hW, withDensity_apply _ (measurable_fst hA),
    setLIntegral_map hA (measurable_expW t) measurable_fst]

/-- **The zero-momentum density of a shifted measure is the shifted density**, for `t ≥ 0` on rates
`≥ 0`. The test function `e^{−2t|E|} f(E)` is bounded and continuous, and equals `e^{−2tE} f(E)` on the
support. DERIVED: `0` the bottom of the rates; `1` the bound of `e^{−x}`; `2` as in `expW`. -/
theorem zeroDensity_shift {τ : Fin 4} {ν : Measure (ℝ × (Fin 4 → ℝ))} {σ0 : Measure ℝ}
    (hσ : ZeroDensity τ ν σ0) (hν : ν (Iio 0 ×ˢ univ) = 0) (hσ0 : σ0 (Iio 0) = 0) {t : ℝ}
    (ht : 0 ≤ t) : ZeroDensity τ (tiltJ t ν) (tiltE t σ0) := by
  intro f hf hfb
  let e : ℝ → ℝ≥0 := fun E => Real.toNNReal (Real.exp (-(2 * t * |E|)))
  have hec : Continuous e := continuous_real_toNNReal.comp (by fun_prop)
  have he1 : ∀ E, e E ≤ 1 := fun E => by
    have h : Real.exp (-(2 * t * |E|)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    simpa [e] using h
  let f' : ℝ → ℝ≥0 := fun E => e E * f E
  have hfc : Continuous f' := hec.mul hf
  obtain ⟨B, hB⟩ := hfb
  have hfb' : BddAbove (range f') := ⟨B, by
    rintro _ ⟨x, rfl⟩
    calc e x * f x ≤ 1 * B := mul_le_mul' (he1 x) (hB ⟨x, rfl⟩)
      _ = B := one_mul _⟩
  have hfm : Measurable fun s : ℝ => (f s : ℝ≥0∞) := (ENNReal.continuous_coe.comp hf).measurable
  have key : ∀ μ : Measure ℝ, μ (Iio 0) = 0 →
      ∫⁻ s, (f s : ℝ≥0∞) ∂(tiltE t μ) = ∫⁻ s, (f' s : ℝ≥0∞) ∂μ := fun μ hμ => by
    rw [tiltE_def, lintegral_withDensity_eq_lintegral_mul _ (measurable_expW t) hfm]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_nonneg_of_Iio hμ] with E hE
    simp only [Pi.mul_apply, f', e, ENNReal.coe_mul]
    rw [abs_of_nonneg hE]
    rfl
  rw [key σ0 hσ0]
  refine (hσ f' hfc hfb').congr fun ε => ?_
  rw [windowed_tiltJ, key _ (windowed_Iio hν ε)]

/-- **The Clay read through the shifted template.** For joint data on the Clay object with time step
`X.time 1`, `u` in the vacuum complement, a finite `ρ` with `ρ (−∞, 0] = 0` and `SpecBottom ρ M2`, and
`nu J u = e^{−2t₀E} klJoint τ ρ g` with `t₀ ≥ 0`, every conclusion of `clay_zero_momentum_kl` holds with
the zero-momentum density `e^{−2t₀E} klSec (g(0) ρ) 0`. The null sets of `nu` are those of `klJoint`
(`shiftBy_null`), which puts the gap on the unshifted measure. DERIVED: `0` the zero momentum and the
signs; `1` the unit step; `2` the square. -/
theorem clay_zero_momentum_shift {τ : Fin 4} (X : OSDataS) (J : JointData X.H (spatial τ))
    (hJ : J.a = X.time 1) (u : X.H) (hu : inner ℂ X.vac u = 0) {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hρ0 : ρ (Iic 0) = 0) {g : (Fin 4 → ℝ) → ℝ≥0} (hg : Continuous g) (hg0 : g 0 ≠ 0) {M2 : ℝ}
    (hb : SpecBottom ρ M2) {t₀ : ℝ} (ht : 0 ≤ t₀) (hKL : nu J u = tiltJ t₀ (klJoint τ ρ g)) :
    ZeroDensity τ (nu J u) (tiltE t₀ (klSec (g 0 • ρ) 0))
      ∧ tiltE t₀ (klSec (g 0 • ρ) 0) (Iio X.gap) = 0 ∧ 0 < M2 ∧ X.gap ≤ Real.sqrt M2
      ∧ SpecBottom (tiltE t₀ (klSec (g 0 • ρ) 0)) (Real.sqrt M2)
      ∧ ∀ p2, 0 ≤ p2 → Real.sqrt p2 < shell M2 p2 := by
  have hr := gap_rateBottom X u hu
  rw [← hJ] at hr
  have hν := nu_Iio_prod J u X.gap hr
  rw [hKL] at hν
  have hν0 : klJoint τ ρ g (Iio X.gap ×ˢ univ) = 0 := (shiftBy_null measurable_fst).mp hν
  obtain ⟨b, hb0, hbρ⟩ := klJoint_bottom τ hρ0 hg hg0 X.gap_pos hν0
  have hσ := klJoint_zeroDensity τ hρ0 (klWeight_fin hb0 hbρ) hg
  have h0 := zeroDensity_bottom hσ hν0
  have hρ0' : (g 0 • ρ) (Iic 0) = 0 := by rw [Measure.smul_apply, hρ0, smul_zero]
  have hb' := specBottom_smul hg0 hb
  have hsq := gap_sq_le_of_sector X (kallenLehmann_klSec (g 0 • ρ)) hρ0' hb' h0
  have hgap := X.gap_pos
  have hM : 0 < M2 := lt_of_lt_of_le (pow_pos hgap 2) hsq
  have hM0 : 0 < M2 + 0 := by rw [add_zero]; exact hM
  have hsh : shell M2 0 = Real.sqrt M2 := by unfold shell; rw [add_zero]
  have hbot := specBottom_klSector (kallenLehmann_klSec (g 0 • ρ)) hb' le_rfl hM0
  rw [hsh] at hbot
  refine ⟨?_, (shiftBy_null measurable_id).mpr h0, hM, (Real.le_sqrt' hgap).mpr hsq,
    (specBottom_tiltE _ _ _).mpr hbot, fun p2 hp => ?_⟩
  · rw [hKL]
    exact zeroDensity_shift hσ (klJoint_Iio τ ρ g) (klSec_Iio _ _) ht
  · exact (MassGap.BandShell.gap_iff_band_excess (MassGap.BandShell.specBottom_dirac M2) hp
      (by linarith) (MassGap.BandShell.shell_rate (MassGap.BandShell.specBottom_dirac M2)
        (by linarith))).mp hM

/-- **The Clay read under `KLJointRepShift`.** DERIVED: `0` the zero momentum and the signs; `1` the
unit step. -/
theorem clay_zero_momentum_shiftRep {τ : Fin 4} (X : OSDataS) (J : JointData X.H (spatial τ))
    (hJ : J.a = X.time 1) (u : X.H) (hu : inner ℂ X.vac u = 0) {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hρ0 : ρ (Iic 0) = 0) {M2 : ℝ} (hb : SpecBottom ρ M2) (hT : KLJointRepShift J u ρ) :
    ∃ σ0 : Measure ℝ, ZeroDensity τ (nu J u) σ0 ∧ σ0 (Iio X.gap) = 0 ∧ 0 < M2
      ∧ X.gap ≤ Real.sqrt M2 ∧ SpecBottom σ0 (Real.sqrt M2) := by
  obtain ⟨t₀, ht, g, hg, hg0, hKL⟩ := hT
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := clay_zero_momentum_shift X J hJ u hu hρ0 hg hg0 hb ht hKL
  exact ⟨_, h1, h2, h3, h4, h5⟩

end

end MassGap.ShiftSector

#print axioms MassGap.ShiftSector.expW_cross
#print axioms MassGap.ShiftSector.shiftBy_shiftBy
#print axioms MassGap.ShiftSector.shiftBy_eq_iff
#print axioms MassGap.ShiftSector.shiftBy_null
#print axioms MassGap.ShiftSector.tiltE_singleton
#print axioms MassGap.ShiftSector.klSec_singleton
#print axioms MassGap.ShiftSector.atom_eq
#print axioms MassGap.ShiftSector.sum_shell_ne
#print axioms MassGap.ShiftSector.shift_not_kl
#print axioms MassGap.ShiftSector.shift_family_not_kl
#print axioms MassGap.ShiftSector.shellReg_shift
#print axioms MassGap.ShiftSector.not_stieltjesCov_shift
#print axioms MassGap.ShiftSector.tilt_klSec_dirac
#print axioms MassGap.ShiftSector.exRho_not_kl
#print axioms MassGap.ShiftSector.exRho_not_stieltjesCov
#print axioms MassGap.ShiftSector.stieltjesCov_shift_iff
#print axioms MassGap.ShiftSector.lintegral_klJoint
#print axioms MassGap.ShiftSector.tiltJ_klJoint_rect
#print axioms MassGap.ShiftSector.measurable_tiltE_apply
#print axioms MassGap.ShiftSector.klJointRepAt_zero
#print axioms MassGap.ShiftSector.klJointRepShift_of_rep
#print axioms MassGap.ShiftSector.klJointRepAt_iff_shiftOff
#print axioms MassGap.ShiftSector.nu_rect
#print axioms MassGap.ShiftSector.sectorShift_of_stieltjes
#print axioms MassGap.ShiftSector.klJointRepAt_of_stieltjes
#print axioms MassGap.ShiftSector.specBottom_tiltE
#print axioms MassGap.ShiftSector.shell_rate_shift
#print axioms MassGap.ShiftSector.windowed_tiltJ
#print axioms MassGap.ShiftSector.zeroDensity_shift
#print axioms MassGap.ShiftSector.clay_zero_momentum_shift
#print axioms MassGap.ShiftSector.clay_zero_momentum_shiftRep
