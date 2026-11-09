import Mathlib
import MassGap.SmallClose

/-!
# MassGap.KernelRate — the Laplace measure of the time kernel is the rate measure of the vector

`CompKernel.timeKernel_laplaceRep` gives the time kernel `C(t) = S(θP ∪ shift_{t e_τ} P)` of a regular
margin monomial one Laplace measure; `ShellMeasure.rateMeasure` gives the vector `g = gvecT P` one rate
measure. `CompKernel.timeKernel_dyadic` compares them at dyadic times only. This module compares them at
every time. Declarations are in the namespace `MassGap.KernelRate`.

* `exists_dyadic_tendsto`: every `t ≥ 0` is a limit of dyadic times `a_m n ≥ 0`.
* `timeKernel_eq_inner_timeT`: `C(t) = Re⟪g, timeT t g⟫` for every `t ≥ 0`: the dyadic identity, with
  `CompKernel.continuous_timeKernel` on the left and `ContinuumTimeGroup.continuousOn_timeT` on the right.
* `timeKernel_laplace_rate`: `C(t) = ∫ e^{−tx} d(ρ.map (· / a₀))(x)`, `t > 0`, `ρ = rateMeasure (stepT 0) g`.
* `kernel_measure_eq`: the representing measure of `C` is `ρ.map (· / a₀)` (`SmallClose.laplaceRep_unique`).
* `rate_eq_kernel_measure`: `ρ = σ.map (a₀ * ·)` (`SmallClose.measure_eq_rateMeasure`).

The time unit: `timeT t = (stepT 0)^(t / a₀)`, so `ρ` is carried by the rates of the step `stepT 0`, per
unit of `a₀`, and `σ` by the rates per unit of physical time `t`. A rate `E` of `ρ` is the rate `E / a₀`
of `σ`. No other factor enters.

## What does not follow, plainly

* This closes one clause: the rate measure of `gvecT P` is tied to the time kernel's measure. The
  measure is still not identified with `klSec ρ`, and the Stieltjes step and step (d) of `CompKernel`
  are untouched: there is one measure per monomial, on one time axis, at zero spatial separation.
* `hpos`, `hcube`, `Reg D P.1` and the margin `PosPreserving τ r` are inputs, as in `CompKernel`.

DERIVED (module-wide): `0` the time origin, the reference step and the bottom of the rates; `1` the
floor offset. No number enters a clause.

Foundational footprint only (`#print axioms` at the end).
-/

set_option autoImplicit false

namespace MassGap.KernelRate

open Filter Topology MeasureTheory Set
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumFlow MassGap.ContinuumTimeGroup
  MassGap.ObserverOS MassGap.ObserverEnergyBox
open MassGap.ShellTranslate (Reg)
open MassGap.ShellMeasure (rateMeasure rateMeasure_Iio flow_time_laplace)
open MassGap.CompKernel (timeKernel continuous_timeKernel timeKernel_dyadic)

noncomputable section

variable {N : ℕ} (hN : N ≠ 0)

include hN in
/-- **Every `t ≥ 0` is a limit of dyadic times** `a_m ⌊t / a_m⌋`. DERIVED: `0` the sign of the time; `1`
the floor offset. -/
theorem exists_dyadic_tendsto {t : ℝ} (ht : 0 ≤ t) :
    ∃ s : ℕ → ℝ, (∀ m, ∃ n : ℕ, s m = dySpacing N m * n) ∧ (∀ m, 0 ≤ s m) ∧ Tendsto s atTop (𝓝 t) := by
  have ha := dySpacing_pos (one_le_of_ne_zero hN)
  refine ⟨fun m => dySpacing N m * (⌊t / dySpacing N m⌋₊ : ℝ), fun m => ⟨_, rfl⟩,
    fun m => mul_nonneg (ha m).le (Nat.cast_nonneg _), ?_⟩
  have hle : ∀ m, dySpacing N m * (⌊t / dySpacing N m⌋₊ : ℝ) ≤ t := fun m => by
    have h1 := Nat.floor_le (div_nonneg ht (ha m).le)
    calc dySpacing N m * (⌊t / dySpacing N m⌋₊ : ℝ) ≤ dySpacing N m * (t / dySpacing N m) :=
          mul_le_mul_of_nonneg_left h1 (ha m).le
      _ = t := mul_div_cancel₀ t (ha m).ne'
  have hge : ∀ m, t - dySpacing N m ≤ dySpacing N m * (⌊t / dySpacing N m⌋₊ : ℝ) := fun m => by
    have h1 := Nat.lt_floor_add_one (t / dySpacing N m)
    have h2 := mul_lt_mul_of_pos_left h1 (ha m)
    rw [mul_div_cancel₀ t (ha m).ne'] at h2
    linarith
  have hlow : Tendsto (fun m => t - dySpacing N m) atTop (𝓝 t) := by
    simpa using (tendsto_const_nhds (x := t)).sub (tendsto_dySpacing N)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds hge hle

variable (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
  (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
  (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)

/-- **The vector of a margin monomial** in the reconstruction of the observer's flow. DERIVED: no
numeral. -/
abbrev vec (τ : Fin 4) {r : ℝ} (hpp : (energy0 W D hD).PosPreserving τ r) (P : MarginMono N τ r) :
    FlowH hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ hpp :=
  gvecT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ hpp P

/-- **The rate measure of that vector**, under the reference step. DERIVED: `0` the reference step. -/
abbrev rate (τ : Fin 4) {r : ℝ} (hpp : (energy0 W D hD).PosPreserving τ r) (P : MarginMono N τ r) :
    Measure ℝ :=
  rateMeasure (stepT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ hpp 0)
    (vec hN W hD hpos hcube τ hpp P)

/-- **The time kernel is the matrix element of `timeT` at every time `t ≥ 0`**: the dyadic identity
and continuity of both sides. DERIVED: `0` the sign of the time. -/
theorem timeKernel_eq_inner_timeT (τ : Fin 4) {r : ℝ} (hpp : (energy0 W D hD).PosPreserving τ r)
    (P : MarginMono N τ r) (hP : Reg D P.1) {t : ℝ} (ht : 0 ≤ t) :
    timeKernel hN W hD τ P.1 t
      = (inner ℂ (vec hN W hD hpos hcube τ hpp P)
          (timeT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ hpp t
            (vec hN W hD hpos hcube τ hpp P))).re := by
  set hB := uniformBoundF_energy0 hN W D hD hpos hcube
  set g := vec hN W hD hpos hcube τ hpp P
  obtain ⟨s, hdy, hs0, hst⟩ := exists_dyadic_tendsto hN ht
  have hL := (continuous_timeKernel hN W hD hpos hcube τ hP).tendsto t |>.comp hst
  have hs' : Tendsto s atTop (𝓝[Ici 0] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hst, Eventually.of_forall hs0⟩
  have hc := (continuousOn_timeT hN (energy0 W D hD) hB τ hpp g t ht).tendsto.comp hs'
  have hi : Continuous fun y : FlowH hN (energy0 W D hD) hB τ hpp => (inner ℂ g y).re :=
    Complex.continuous_re.comp (continuous_const.inner continuous_id)
  have hR := (hi.tendsto _).comp hc
  refine tendsto_nhds_unique hL (hR.congr fun m => ?_)
  obtain ⟨n, hn⟩ := hdy m
  show (inner ℂ g (timeT hN (energy0 W D hD) hB τ hpp (s m) g)).re = timeKernel hN W hD τ P.1 (s m)
  rw [hn, timeKernel_dyadic hN W hD hpos hcube τ hpp P m n, mul_comm (dySpacing N m) (n : ℝ),
    timeT_dyadic]

/-- **The rate measure in the unit of `t` is a Laplace measure of the time kernel.** DERIVED: `0` the
reference step and the sign of the time. -/
theorem timeKernel_laplace_rate (τ : Fin 4) {r : ℝ} (hpp : (energy0 W D hD).PosPreserving τ r)
    (P : MarginMono N τ r) (hP : Reg D P.1) {t : ℝ} (ht : 0 < t) :
    timeKernel hN W hD τ P.1 t
      = ∫ x, Real.exp (-(t * x)) ∂((rate hN W hD hpos hcube τ hpp P).map fun E => E / dySpacing N 0) := by
  rw [timeKernel_eq_inner_timeT hN W hD hpos hcube τ hpp P hP ht.le,
    flow_time_laplace _ _ _ _ _ _ ht,
    integral_map (by fun_prop) (by fun_prop)]
  refine integral_congr_ae (Eventually.of_forall fun E => ?_)
  show Real.exp (-(t / dySpacing N 0 * E)) = Real.exp (-(t * (E / dySpacing N 0)))
  congr 2
  ring

/-- **The representing measure of the time kernel is the rate measure of the vector**, each rate `E`
read as `E / a₀`. DERIVED: `0` the reference step, the sign of the time and the bottom of the rates. -/
theorem kernel_measure_eq (τ : Fin 4) {r : ℝ} (hpp : (energy0 W D hD).PosPreserving τ r)
    (P : MarginMono N τ r) (hP : Reg D P.1) {σ : Measure ℝ} [IsFiniteMeasure σ] (h0 : σ (Iio 0) = 0)
    (hr : ∀ t, 0 < t → timeKernel hN W hD τ P.1 t = ∫ x, Real.exp (-(t * x)) ∂σ) :
    σ = (rate hN W hD hpos hcube τ hpp P).map fun E => E / dySpacing N 0 := by
  have ha := dySpacing_pos (one_le_of_ne_zero hN) 0
  have hm : Measurable fun E : ℝ => E / dySpacing N 0 := by fun_prop
  refine SmallClose.laplaceRep_unique h0 ?_ fun t ht =>
    (hr t ht).symm.trans (timeKernel_laplace_rate hN W hD hpos hcube τ hpp P hP ht)
  rw [Measure.map_apply hm measurableSet_Iio]
  refine measure_mono_null (fun E hE => ?_) (rateMeasure_Iio _ _)
  have hE' : E / dySpacing N 0 < 0 := hE
  have h := (div_lt_iff₀ ha).mp hE'
  rw [zero_mul] at h
  exact h

/-- **The rate measure of the vector is the representing measure of the time kernel**, each rate `x`
read as `a₀ x`. DERIVED: `0` the reference step, the sign of the time and the bottom of the rates. -/
theorem rate_eq_kernel_measure (τ : Fin 4) {r : ℝ} (hpp : (energy0 W D hD).PosPreserving τ r)
    (P : MarginMono N τ r) (hP : Reg D P.1) {σ : Measure ℝ} [IsFiniteMeasure σ] (h0 : σ (Iio 0) = 0)
    (hr : ∀ t, 0 < t → timeKernel hN W hD τ P.1 t = ∫ x, Real.exp (-(t * x)) ∂σ) :
    rate hN W hD hpos hcube τ hpp P = σ.map fun x => dySpacing N 0 * x := by
  have ha := dySpacing_pos (one_le_of_ne_zero hN) 0
  have hm : Measurable fun x : ℝ => dySpacing N 0 * x := by fun_prop
  refine (SmallClose.measure_eq_rateMeasure
    (spectrum_stepT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ hpp 0)
    (vec hN W hD hpos hcube τ hpp P) ?_ fun s hs => ?_).symm
  · rw [Measure.map_apply hm measurableSet_Iio]
    refine measure_mono_null (fun x hx => ?_) h0
    have hx' : dySpacing N 0 * x < 0 := hx
    exact (pos_iff_neg_of_mul_neg hx').mp ha
  · have hst : 0 < s * dySpacing N 0 := mul_pos hs ha
    have e := timeKernel_eq_inner_timeT hN W hD hpos hcube τ hpp P hP hst.le
    have hT : powT (stepT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ hpp 0) s
        = timeT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ hpp
            (s * dySpacing N 0) := by
      unfold timeT
      rw [mul_div_cancel_right₀ s ha.ne']
    rw [hT, ← e, hr _ hst, integral_map hm.aemeasurable (by fun_prop)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show Real.exp (-(s * dySpacing N 0 * x)) = Real.exp (-(s * (dySpacing N 0 * x)))
    rw [mul_assoc]

end

end MassGap.KernelRate

#print axioms MassGap.KernelRate.exists_dyadic_tendsto
#print axioms MassGap.KernelRate.timeKernel_eq_inner_timeT
#print axioms MassGap.KernelRate.timeKernel_laplace_rate
#print axioms MassGap.KernelRate.kernel_measure_eq
#print axioms MassGap.KernelRate.rate_eq_kernel_measure
