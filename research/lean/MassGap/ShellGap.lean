import Mathlib
import MassGap.ShellMeasure
import MassGap.ClayFull

/-!
# MassGap.ShellGap — the Clay gap is the bottom of the rate measure

`ShellMeasure` reads the time correlator of a vector under a positive contraction `a` as the Laplace
transform of its rate measure `σ_u = rateMeasure a u`. This module ties that read to the Clay object,
`ObserverOSReconstructionS.OSDataS`, and shows that the gap clause of `OSDataS` and the bottom of the
rate measure are one statement. Declarations are in the namespace `MassGap.ShellGap`.

## 1. The time of an `OSDataS` is the functional calculus of its unit step (proved)

`OSDataS.time` is an abstract semigroup of self-adjoint contractions with `time 0 = 1`, the law
`time (s + t) = time s * time t` on `s, t ≥ 0`, and strong continuity on `[0, ∞)` (`time_cont`).

* `time_nonneg`: `time t = time (t/2) * time (t/2)` with `time (t/2)` self-adjoint, so `time t ≥ 0`.
* `spectrum_time`: positivity and `‖time t‖ ≤ 1` put the spectrum in `[0, 1]`.
* `time_dyadic`: `time ((1/2)^m) = powT (time 1) ((1/2)^m)`, by uniqueness of positive square roots
  (`ContinuumTimeGroup.eq_powT_of_sq`); `time_dyadic_mul` extends it to `n (1/2)^m` by the semigroup
  law and `powT_nat_mul`.
* `time_eq_powT`: `time t = powT (time 1) t` for every `t ≥ 0`. For `t > 0` the dyadics
  `⌈t 2^k⌉ / 2^k` decrease to `t`; `time_cont` carries the left side along them, norm continuity of
  `powT` on `s > 0` (`continuousAt_powT`) the right side.
* `time_laplaceRep`: every vector correlator `t ↦ Re ⟪u, time t u⟫` of an `OSDataS` is a Laplace
  transform, its measure the rate measure of `u` for `time 1`.

The clause used is `time_cont`, which `OSDataS` carries, and which the tree's instance
`observerOSDataS` meets (`ContinuumTimeGroup.continuousOn_timeT`). Plainly, it is not the weakest
clause: positivity alone orders the semigroup, `time (s + t) = time (s/2) time t time (s/2) ≤
time s`, so `time t` sits between the norm-convergent dyadic powers above and below it and is fixed
without any continuity. That sandwich argument is not formalised here.

## 2. The gap is the bottom of the rate measure (proved)

On the operator level, for a self-adjoint `a` with spectrum in `[0, 1]`, a vector `u` and any real `g`:

* `rateBottom_of_bound`: `‖a^t u‖ ≤ e^{−g t} ‖u‖` for all `t ≥ 0` gives `σ_u (−∞, g) = 0`. The
  correlator `∫ e^{−τE} dσ_u = ‖a^{τ/2} u‖²` is at most `e^{−gτ} ‖u‖²`; Markov's inequality at
  `g' < g` bounds `σ_u (−∞, g']` by `e^{−τ(g − g')} ‖u‖² → 0`.
* `bound_of_rateBottom`: `σ_u (−∞, g) = 0` gives the bound: `‖a^t u‖² = ∫ e^{−2tE} dσ_u ≤
  e^{−2tg} σ_u(ℝ)` and `σ_u(ℝ) ≤ ‖u‖²` (`rateMeasure_real_univ_le`).
* `bound_iff_rateBottom`: the two together.
* `rate_bottom_sharp`: if `σ_u` has bottom exactly `m` (`BandShell.SpecBottom`), the bound holds at
  `m` and fails at every `g > m`: the best decay rate of `u` is the bottom of its rate measure.

On an `OSDataS` (`X.time t = powT (X.time 1) t`):

* `gap_rateBottom`: every `u` orthogonal to the vacuum has `σ_u (−∞, X.gap) = 0`.
* `time_bound_of_rateBottom`, `gap_iff_rateBottom`: a uniform rate `g` on the vacuum complement
  holds exactly when every rate measure there vanishes below `g`. This is `time_gap` read as a
  spectral bottom; the quadratic-form gap `ClayFull.HamiltonianGap` is stated separately, and no theorem
  here links the two.
* `gap_le_of_specBottom`: a vector of the complement with rate bottom `m` has `X.gap ≤ m`.

## 3. The Källén–Lehmann sector at zero momentum (proved, given the Källén–Lehmann assumptions)

* `specBottom_klSector`: a family in Källén–Lehmann form with `SpecBottom ρ M2` has sector bottoms
  `SpecBottom (σ p²) (√(M2 + p²))` when `M2 + p² > 0`.
* `clay_gap_sq_le` and `clay_zero_momentum` take two assumptions that are not discharged here. (a) A finite
  measure `ρ` exists with `KallenLehmann σ ρ`, `SpecBottom ρ M2` and `ρ (Iic 0) = 0` (the open `KLTemplate`).
  (b) The rate measure of a vector `u` of the vacuum complement is the zero-momentum sector,
  `rateMeasure (X.time 1) u = σ 0`; building the momentum-`0` vector is the open half of `KLTemplate`.
  Given (a) and (b), `clay_gap_sq_le` proves `X.gap² ≤ M2`. The support clause `ρ (Iic 0) = 0` is needed:
  `klWeight 0 s = 1/(2√s)` is `0` at `s ≤ 0` in Lean's division, so mass of `ρ` there does not reach `σ 0`
  (physically the weight diverges at `s = 0`, `p = 0`). Given the same assumptions, `clay_zero_momentum`
  proves: `0 < M2` (from `gap_pos` and `X.gap² ≤ M2`), `X.gap ≤ √M2`, the decay of `u` at rate `√M2`, the
  correlator's read `−log C(τ)/τ → √M2` (`ShellMeasure.shell_rate_of_kl`), and, for every `p²`,
  `√p² < √(M2 + p²)` (`BandShell.gap_iff_band_excess`; this last clause uses only `0 < M2`). These results
  do not construct `ρ` or the vector `u`; they do not by themselves show that the Clay object has a
  Källén–Lehmann sector. Plainly, assumption (b) cannot hold for a physical vector of the vacuum
  complement in a translation-invariant continuum theory: such a vector has no exactly
  translation-invariant component, so its rate measure is not the zero-momentum sector `σ 0`. The
  sector `σ 0` is the density at `p = 0` of the joint spectral measure of `(H, P)`, which
  `ShellJoint.jointMeasure` builds for one vector (see `ShellJoint.hσ_forces_zero_momentum_vector`).
  This is argued, not formalised.

## 4. Load tests (proved)

* `scalar_rate_bottom`: the free single mode `a = e^{−m}`, `m ≥ 0`, has `‖a^t u‖ = e^{−mt} ‖u‖`; its
  rate measure vanishes below `m` and charges `(−∞, g)` for every `g > m`.
* `identity_no_gap`: the mode at `m = 0` (the identity, a second vacuum) has a rate measure touching
  `0`, and no rate `g > 0` holds; `no_gap_of_rate_touches_zero`: no `OSDataS` has a complement vector
  whose rate measure touches `0`.
* `free_zero_specBottom`: the free Källén–Lehmann sector `freeRate m² 0` has bottom `√m²`.

Foundational footprint only (`#print axioms` at the end).
-/

namespace MassGap.ShellGap

open Real Filter Topology MeasureTheory Set
open MassGap.BandShell (shell bandProfile SpecBottom shell_mono shell_nonneg shell_rate
  specBottom_dirac gap_iff_band_excess)
open MassGap.ContinuumTimeGroup (powT powT_zero powT_add powT_nat_mul powT_nonneg isSelfAdjoint_powT
  norm_powT_le_one continuousAt_powT eq_powT_of_sq)
open MassGap.ShellMeasure (rateMeasure vecMeasure rateMeasure_Iio re_inner_powT_eq_laplace
  re_inner_cfc_eq_integral measurable_rate LaplaceRep powT_laplaceRep integrable_exp_of_Iio
  KallenLehmann klWeight measurable_klWeight measurable_shell specBottom_klDensity shell_rate_of_kl
  freeRate free_kallenLehmann)
open MassGap.ObserverOSReconstructionS (OSDataS)

noncomputable section

/-! ## 2a. The operator level -/

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {a : E →L[ℂ] E}

/-- **The spectrum of a positive contraction lies in `[0, 1]`.** DERIVED: `0` the order's bottom;
`1` the norm bound. -/
theorem spectrum_Icc_of_nonneg {b : E →L[ℂ] E} (h0 : 0 ≤ b) (h1 : ‖b‖ ≤ 1) :
    spectrum ℝ b ⊆ Icc 0 1 := by
  intro k hk
  refine ⟨spectrum_nonneg_of_nonneg h0 hk, ?_⟩
  have hmem : k ∈ Metric.closedBall (0 : ℝ) (‖b‖ * ‖(1 : E →L[ℂ] E)‖) :=
    spectrum.subset_closedBall_norm_mul (𝕜 := ℝ) b hk
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hmem
  have h2 : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := by
    simpa [ContinuousLinearMap.one_def] using ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := E)
  have h3 : ‖b‖ * ‖(1 : E →L[ℂ] E)‖ ≤ 1 := by
    calc ‖b‖ * ‖(1 : E →L[ℂ] E)‖ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 1 := mul_one _
  exact (le_abs_self k).trans (hmem.trans h3)

/-- **The correlator at twice the time is a squared norm**: `‖a^t u‖² = Re ⟪u, a^{t+t} u⟫`.
DERIVED: `0` the sign of `t`; `2` the square. -/
theorem sq_norm_powT_apply (hsp : spectrum ℝ a ⊆ Icc 0 1) {t : ℝ} (ht : 0 ≤ t) (u : E) :
    ‖powT a t u‖ ^ 2 = (inner ℂ u (powT a (t + t) u)).re := by
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (isSelfAdjoint_powT (a := a) t)
  rw [powT_add hsp ht ht, ContinuousLinearMap.mul_apply]
  have h := hsym u (powT a t u)
  simp only [ContinuousLinearMap.coe_coe] at h
  rw [← h]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) (powT a t u)).symm

/-- **The rate measure has mass at most `‖u‖²`**: its total mass is the spectral mass off the kernel,
and the spectral measure's total mass is `Re ⟪u, u⟫`. DERIVED: `1` the constant function; `2` the
square. -/
theorem rateMeasure_real_univ_le (ha : IsSelfAdjoint a) (hsp : spectrum ℝ a ⊆ Icc 0 1) (u : E) :
    (rateMeasure a u).real univ ≤ ‖u‖ ^ 2 := by
  have hv : (vecMeasure a u).real univ = ‖u‖ ^ 2 := by
    have h := re_inner_cfc_eq_integral hsp u (continuous_const (y := (1 : ℝ)))
    beta_reduce at h
    rw [cfc_const_one ℝ a ha, ContinuousLinearMap.one_apply, integral_const, smul_eq_mul,
      mul_one] at h
    rw [← h]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) u
  rw [← hv]
  refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
  unfold rateMeasure
  rw [Measure.map_apply measurable_rate MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, univ_inter]
  exact measure_mono (subset_univ _)

/-- **A decay bound puts nothing below its rate**: `‖a^t u‖ ≤ e^{−gt} ‖u‖` for all `t ≥ 0` gives
`σ_u (−∞, g) = 0`. DERIVED: `0` the signs and the vanishing limit; `1` the step `1/(n + 1)` below
`g`; `2` the halved time and the square. -/
theorem rateBottom_of_bound (hsp : spectrum ℝ a ⊆ Icc 0 1) (u : E) {g : ℝ}
    (hb : ∀ t, 0 ≤ t → ‖powT a t u‖ ≤ Real.exp (-(g * t)) * ‖u‖) :
    rateMeasure a u (Iio g) = 0 := by
  set σ := rateMeasure a u with hσ
  haveI : IsFiniteMeasure σ := by rw [hσ]; infer_instance
  have hint : ∀ τ, 0 ≤ τ → Integrable (fun E => Real.exp (-(τ * E))) σ :=
    fun τ hτ => integrable_exp_of_Iio (rateMeasure_Iio a u) hτ
  -- the correlator is at most `e^{−gτ} ‖u‖²`
  have hcorr : ∀ τ, 0 < τ → ∫ E, Real.exp (-(τ * E)) ∂σ ≤ Real.exp (-(g * τ)) * ‖u‖ ^ 2 := by
    intro τ hτ
    have h2 := sq_norm_powT_apply hsp (half_pos hτ).le u
    rw [add_halves] at h2
    rw [← re_inner_powT_eq_laplace hsp u hτ, ← h2]
    have hn := hb (τ / 2) (half_pos hτ).le
    calc ‖powT a (τ / 2) u‖ ^ 2 ≤ (Real.exp (-(g * (τ / 2))) * ‖u‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = Real.exp (-(g * τ)) * ‖u‖ ^ 2 := by
          rw [mul_pow, ← Real.exp_nat_mul]
          congr 2
          push_cast
          ring
  -- Markov below each `g' < g`
  have hIic : ∀ g', g' < g → σ (Iic g') = 0 := by
    intro g' hg'
    have hle : ∀ τ, 0 < τ → σ.real (Iic g') ≤ Real.exp (-(τ * (g - g'))) * ‖u‖ ^ 2 := by
      intro τ hτ
      have hm := mul_meas_ge_le_integral_of_nonneg (μ := σ)
        (Eventually.of_forall fun E => (Real.exp_pos (-(τ * E))).le) (hint τ hτ.le)
        (Real.exp (-(τ * g')))
      have hsub : Iic g' ⊆ {E | Real.exp (-(τ * g')) ≤ Real.exp (-(τ * E))} := by
        intro E hE
        simp only [mem_setOf_eq, Real.exp_le_exp]
        have : E ≤ g' := hE
        nlinarith
      have hmono : σ.real (Iic g') ≤ σ.real {E | Real.exp (-(τ * g')) ≤ Real.exp (-(τ * E))} :=
        measureReal_mono hsub
      have hpos := Real.exp_pos (-(τ * g'))
      have h1 : Real.exp (-(τ * g')) * σ.real (Iic g') ≤ Real.exp (-(g * τ)) * ‖u‖ ^ 2 :=
        (mul_le_mul_of_nonneg_left hmono hpos.le).trans (hm.trans (hcorr τ hτ))
      have h2 : Real.exp (-(g * τ)) = Real.exp (-(τ * g')) * Real.exp (-(τ * (g - g'))) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [h2, mul_assoc] at h1
      exact le_of_mul_le_mul_left h1 hpos
    have hlim : Tendsto (fun τ => Real.exp (-(τ * (g - g'))) * ‖u‖ ^ 2) atTop (𝓝 0) := by
      have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.atTop_mul_const (sub_pos.mpr hg'))).mul_const (‖u‖ ^ 2)
      simpa [Function.comp_def] using h
    have h0 : σ.real (Iic g') ≤ 0 :=
      ge_of_tendsto hlim (eventually_gt_atTop 0 |>.mono fun τ hτ => hle τ hτ)
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
      (le_antisymm h0 measureReal_nonneg)
  have hU : Iio g = ⋃ n : ℕ, Iic (g - 1 / ((n : ℝ) + 1)) := by
    ext E
    simp only [mem_Iio, mem_iUnion, mem_Iic]
    constructor
    · intro hE
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hE)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  rw [hU]
  exact measure_iUnion_null fun n => hIic _ (by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith)

/-- **Nothing below the rate gives the decay bound**: `σ_u (−∞, g) = 0` gives
`‖a^t u‖ ≤ e^{−gt} ‖u‖` for all `t ≥ 0`. DERIVED: `0` the time origin and the signs; `1` the
identity; `2` the doubled time and the square. -/
theorem bound_of_rateBottom (ha : IsSelfAdjoint a) (hsp : spectrum ℝ a ⊆ Icc 0 1) (u : E) {g : ℝ}
    (h0 : rateMeasure a u (Iio g) = 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖powT a t u‖ ≤ Real.exp (-(g * t)) * ‖u‖ := by
  rcases ht.eq_or_lt with h | htp
  · rw [← h, powT_zero ha, ContinuousLinearMap.one_apply, mul_zero, neg_zero, Real.exp_zero,
      one_mul]
  set σ := rateMeasure a u with hσ
  haveI : IsFiniteMeasure σ := by rw [hσ]; infer_instance
  have hτ : 0 < t + t := by linarith
  have hae : ∀ᵐ E ∂σ, g ≤ E := by
    rw [ae_iff]
    have : {E : ℝ | ¬ g ≤ E} = Iio g := by ext E; simp [not_le]
    rw [this]; exact h0
  have hint : ∫ E, Real.exp (-((t + t) * E)) ∂σ ≤ Real.exp (-((t + t) * g)) * σ.real univ := by
    calc ∫ E, Real.exp (-((t + t) * E)) ∂σ ≤ ∫ _E, Real.exp (-((t + t) * g)) ∂σ :=
          integral_mono_ae (integrable_exp_of_Iio (rateMeasure_Iio a u) hτ.le)
            (integrable_const _) (hae.mono fun E hE => Real.exp_le_exp.mpr (by nlinarith))
      _ = Real.exp (-((t + t) * g)) * σ.real univ := by
          rw [integral_const, smul_eq_mul, mul_comm]
  have hsq : ‖powT a t u‖ ^ 2 ≤ (Real.exp (-(g * t)) * ‖u‖) ^ 2 := by
    rw [sq_norm_powT_apply hsp ht u, re_inner_powT_eq_laplace hsp u hτ]
    refine hint.trans ?_
    have hU := rateMeasure_real_univ_le ha hsp u
    calc Real.exp (-((t + t) * g)) * σ.real univ ≤ Real.exp (-((t + t) * g)) * ‖u‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hU (Real.exp_pos _).le
      _ = (Real.exp (-(g * t)) * ‖u‖) ^ 2 := by
          rw [mul_pow, ← Real.exp_nat_mul]
          congr 2
          push_cast
          ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- **Decay rate ⇔ rate-measure bottom**, for one vector and any real `g`. DERIVED: `0` the signs. -/
theorem bound_iff_rateBottom (ha : IsSelfAdjoint a) (hsp : spectrum ℝ a ⊆ Icc 0 1) (u : E) (g : ℝ) :
    (∀ t, 0 ≤ t → ‖powT a t u‖ ≤ Real.exp (-(g * t)) * ‖u‖) ↔ rateMeasure a u (Iio g) = 0 :=
  ⟨rateBottom_of_bound hsp u, fun h _ ht => bound_of_rateBottom ha hsp u h ht⟩

/-- **The best decay rate is the bottom of the rate measure**: with `SpecBottom σ_u m` the bound holds
at `m` and fails at every `g > m`. DERIVED: `0` the signs. -/
theorem rate_bottom_sharp (ha : IsSelfAdjoint a) (hsp : spectrum ℝ a ⊆ Icc 0 1) (u : E) {m : ℝ}
    (hb : SpecBottom (rateMeasure a u) m) :
    (∀ t, 0 ≤ t → ‖powT a t u‖ ≤ Real.exp (-(m * t)) * ‖u‖)
      ∧ ∀ g, m < g → ¬ ∀ t, 0 ≤ t → ‖powT a t u‖ ≤ Real.exp (-(g * t)) * ‖u‖ := by
  refine ⟨fun t ht => bound_of_rateBottom ha hsp u hb.1 ht, fun g hg hbd => ?_⟩
  have h0 := rateBottom_of_bound hsp u hbd
  have hp := hb.2 (g - m) (sub_pos.mpr hg)
  rw [add_sub_cancel] at hp
  have : rateMeasure a u (Ico m g) ≤ rateMeasure a u (Iio g) :=
    measure_mono fun E hE => hE.2
  rw [h0] at this
  exact (lt_of_lt_of_le hp this).false

end Operator

/-! ## 1. The time of an `OSDataS` is the functional calculus of its unit step -/

section OS

variable (X : OSDataS)

/-- DERIVED: `0` the sign of `t`. -/
theorem time_isSelfAdjoint {t : ℝ} (ht : 0 ≤ t) : IsSelfAdjoint (X.time t) :=
  (X.time_selfAdjoint t ht).1

/-- **Each time translation is positive**: the square of the self-adjoint `time (t/2)`.
DERIVED: `0` the order's bottom and the sign of `t`; `2` the halving. -/
theorem time_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ X.time t := by
  have h := X.time_add (t / 2) (t / 2) (by linarith) (by linarith)
  rw [add_halves] at h
  rw [h]
  exact (time_isSelfAdjoint X (by linarith : (0 : ℝ) ≤ t / 2)).mul_self_nonneg

/-- DERIVED: `0`, `1` the ends of the spectrum interval. -/
theorem spectrum_time {t : ℝ} (ht : 0 ≤ t) : spectrum ℝ (X.time t) ⊆ Icc 0 1 :=
  spectrum_Icc_of_nonneg (time_nonneg X ht) (X.time_selfAdjoint t ht).2

/-- **The dyadic roots are the functional-calculus roots**: `time ((1/2)^m) = (time 1)^{(1/2)^m}`.
DERIVED: `1/2` the dyadic ratio; `1` the unit step; `0` the first root. -/
theorem time_dyadic (m : ℕ) : X.time ((1 / 2 : ℝ) ^ m) = powT (X.time 1) ((1 / 2 : ℝ) ^ m) :=
  eq_powT_of_sq (time_isSelfAdjoint X zero_le_one) (spectrum_time X zero_le_one)
    (fun m => X.time ((1 / 2 : ℝ) ^ m)) (by simp) (fun m => time_nonneg X (by positivity))
    (fun m => by
      show X.time ((1 / 2 : ℝ) ^ (m + 1)) * X.time ((1 / 2 : ℝ) ^ (m + 1)) = X.time ((1 / 2 : ℝ) ^ m)
      rw [← X.time_add _ _ (by positivity) (by positivity)]
      congr 1
      rw [pow_succ]
      ring) m

/-- DERIVED: `0` the sign of `q`; `1` the successor. -/
theorem time_nat_mul {q : ℝ} (hq : 0 ≤ q) (n : ℕ) : X.time (n * q) = X.time q ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_mul, pow_zero, X.time_zero]
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, X.time_add _ _ (mul_nonneg (Nat.cast_nonneg n) hq) hq, ih,
      pow_succ]

/-- **The dyadic times**: `time (n (1/2)^m) = (time 1)^{n (1/2)^m}`. DERIVED: `1/2` the dyadic ratio;
`1` the unit step. -/
theorem time_dyadic_mul (m n : ℕ) :
    X.time (n * (1 / 2 : ℝ) ^ m) = powT (X.time 1) (n * (1 / 2 : ℝ) ^ m) := by
  rw [time_nat_mul X (by positivity), time_dyadic,
    ← powT_nat_mul (time_isSelfAdjoint X zero_le_one) (spectrum_time X zero_le_one) (by positivity)]

/-- **The Clay object's time is the functional calculus of its unit step**: `time t = (time 1)^t` for
every `t ≥ 0`. DERIVED: `0` the time origin; `1` the unit step and the ceiling's excess; `1/2` the
dyadic ratio. -/
theorem time_eq_powT {t : ℝ} (ht : 0 ≤ t) : X.time t = powT (X.time 1) t := by
  rcases ht.eq_or_lt with h0 | htp
  · rw [← h0, X.time_zero, powT_zero (time_isSelfAdjoint X zero_le_one)]
  have hsp := spectrum_time X zero_le_one
  let d : ℕ → ℝ := fun k => (⌈t / (1 / 2 : ℝ) ^ k⌉₊ : ℝ) * (1 / 2 : ℝ) ^ k
  have hq : ∀ k : ℕ, (0 : ℝ) < (1 / 2 : ℝ) ^ k := fun k => by positivity
  have hlo : ∀ k, t ≤ d k := fun k => by
    have h := Nat.le_ceil (t / (1 / 2 : ℝ) ^ k)
    rwa [div_le_iff₀ (hq k)] at h
  have hhi : ∀ k, d k ≤ t + (1 / 2 : ℝ) ^ k := fun k => by
    have h := Nat.ceil_lt_add_one (div_nonneg ht (hq k).le)
    have h2 := mul_lt_mul_of_pos_right h (hq k)
    rw [add_mul, div_mul_cancel₀ t (hq k).ne', one_mul] at h2
    exact h2.le
  have hd : Tendsto d atTop (𝓝 t) := by
    have hup : Tendsto (fun k : ℕ => t + (1 / 2 : ℝ) ^ k) atTop (𝓝 t) := by
      simpa using tendsto_const_nhds.add
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup hlo hhi
  ext y
  have hL : Tendsto (fun k => X.time (d k) y) atTop (𝓝 (X.time t y)) :=
    (X.time_cont y t ht).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hd, Eventually.of_forall fun k => ht.trans (hlo k)⟩)
  have hR : Tendsto (fun k => powT (X.time 1) (d k) y) atTop (𝓝 (powT (X.time 1) t y)) :=
    ((continuousAt_powT hsp htp).clm_apply continuousAt_const).tendsto.comp hd
  have heq : (fun k => X.time (d k) y) = fun k => powT (X.time 1) (d k) y := by
    funext k
    show X.time ((⌈t / (1 / 2 : ℝ) ^ k⌉₊ : ℝ) * (1 / 2 : ℝ) ^ k) y
      = powT (X.time 1) ((⌈t / (1 / 2 : ℝ) ^ k⌉₊ : ℝ) * (1 / 2 : ℝ) ^ k) y
    rw [time_dyadic_mul]
  rw [heq] at hL
  exact tendsto_nhds_unique hL hR

/-- **Every vector correlator of an `OSDataS` is a Laplace transform**, of the rate measure of the
vector for the unit step. DERIVED: `0` the sign of `t`; `1` the unit step. -/
theorem time_laplaceRep (u : X.H) : LaplaceRep (fun t => (inner ℂ u (X.time t u)).re) := by
  obtain ⟨σ, hf, h0, hrep⟩ := powT_laplaceRep (spectrum_time X zero_le_one) u
  exact ⟨σ, hf, h0, fun τ hτ => by
    beta_reduce
    rw [time_eq_powT X hτ.le]
    exact hrep τ hτ⟩

/-! ## 2b. The gap clause as a spectral bottom -/

/-- **The Clay gap bounds every rate measure of the vacuum complement from below**:
`σ_u (−∞, X.gap) = 0`. DERIVED: `0` the vanishing pairing and the sign of `t`; `1` the unit step. -/
theorem gap_rateBottom (u : X.H) (hu : inner ℂ X.vac u = 0) :
    rateMeasure (X.time 1) u (Iio X.gap) = 0 :=
  rateBottom_of_bound (spectrum_time X zero_le_one) u fun t ht => by
    rw [← time_eq_powT X ht]; exact X.time_gap t ht u hu

/-- **A rate-measure bottom gives the semigroup bound.** DERIVED: `0` the sign of `t`; `1` the unit
step. -/
theorem time_bound_of_rateBottom {g : ℝ} (u : X.H) (h : rateMeasure (X.time 1) u (Iio g) = 0)
    {t : ℝ} (ht : 0 ≤ t) : ‖X.time t u‖ ≤ Real.exp (-(g * t)) * ‖u‖ := by
  rw [time_eq_powT X ht]
  exact bound_of_rateBottom (time_isSelfAdjoint X zero_le_one) (spectrum_time X zero_le_one) u h ht

/-- **Gap ⇔ spectral bottom on the vacuum complement**, for any real rate `g`. DERIVED: `0` the
vanishing pairing and the sign of `t`; `1` the unit step. -/
theorem gap_iff_rateBottom (g : ℝ) :
    (∀ t, 0 ≤ t → ∀ u : X.H, inner ℂ X.vac u = 0 → ‖X.time t u‖ ≤ Real.exp (-(g * t)) * ‖u‖)
      ↔ ∀ u : X.H, inner ℂ X.vac u = 0 → rateMeasure (X.time 1) u (Iio g) = 0 := by
  constructor
  · intro h u hu
    exact rateBottom_of_bound (spectrum_time X zero_le_one) u fun t ht => by
      rw [← time_eq_powT X ht]; exact h t ht u hu
  · intro h t ht u hu
    exact time_bound_of_rateBottom X u (h u hu) ht

/-- **The gap is at most the rate bottom of any complement vector.** DERIVED: `0` the vanishing
pairing; `1` the unit step. -/
theorem gap_le_of_specBottom (u : X.H) (hu : inner ℂ X.vac u = 0) {m : ℝ}
    (hb : SpecBottom (rateMeasure (X.time 1) u) m) : X.gap ≤ m := by
  by_contra hlt'
  have hlt := not_le.mp hlt'
  refine (rate_bottom_sharp (time_isSelfAdjoint X zero_le_one) (spectrum_time X zero_le_one) u hb).2
    X.gap hlt fun t ht => ?_
  rw [← time_eq_powT X ht]
  exact X.time_gap t ht u hu

end OS

/-! ## 3. The Källén–Lehmann sector -/

/-- **The sector bottom is the shell of `ρ`'s bottom**: Källén–Lehmann form with `SpecBottom ρ M2`
and `M2 + p² > 0` gives `SpecBottom (σ p²) (√(M2 + p²))`. DERIVED: `0` the signs; `2` the square
`δ = ε²` that keeps the shell within `ε`. -/
theorem specBottom_klSector {σ : ℝ → Measure ℝ} {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hkl : KallenLehmann σ ρ) {M2 p2 : ℝ} (hb : SpecBottom ρ M2) (hp : 0 ≤ p2)
    (hM : 0 < M2 + p2) : SpecBottom (σ p2) (shell M2 p2) := by
  obtain ⟨_, hb'⟩ := specBottom_klDensity hb hM
  rw [hkl p2 hp]
  refine ⟨?_, fun ε hε => ?_⟩
  · rw [Measure.map_apply (measurable_shell p2) measurableSet_Iio]
    have : (fun s => shell s p2) ⁻¹' Iio (shell M2 p2) = Iio M2 := by
      ext s
      simp only [mem_preimage, mem_Iio, shell]
      rw [Real.sqrt_lt_sqrt_iff_of_pos hM]
      constructor <;> intro h <;> linarith
    rw [this]; exact hb'.1
  · rw [Measure.map_apply (measurable_shell p2) measurableSet_Ico]
    refine lt_of_lt_of_le (hb'.2 (ε ^ 2) (by positivity)) (measure_mono fun s hs => ?_)
    obtain ⟨h1, h2⟩ := hs
    simp only [mem_preimage, mem_Ico]
    refine ⟨shell_mono p2 h1, ?_⟩
    have hpos : 0 < M2 + ε ^ 2 + p2 := by nlinarith
    have hlt : shell s p2 < shell (M2 + ε ^ 2) p2 := by
      unfold shell
      rw [Real.sqrt_lt_sqrt_iff_of_pos hpos]
      linarith
    have hadd := MassGap.BandShell.shell_add_le hM.le (sq_nonneg ε)
    rw [Real.sqrt_sq hε.le] at hadd
    exact lt_of_lt_of_le hlt hadd

/-- **The Clay gap bounds `ρ`'s bottom at zero momentum**: if the rate measure of a vector of the
vacuum complement is the zero-momentum sector of a Källén–Lehmann family whose `ρ` has no mass on
`s ≤ 0`, then `X.gap² ≤ M2`. DERIVED: `0` the zero momentum, the vanishing pairing and the support
bound; `1` the unit step; `2` the square. -/
theorem clay_gap_sq_le (X : OSDataS) (u : X.H) (hu : inner ℂ X.vac u = 0)
    {σ : ℝ → Measure ℝ} {ρ : Measure ℝ} [IsFiniteMeasure ρ] (hkl : KallenLehmann σ ρ)
    (hρ0 : ρ (Iic 0) = 0) {M2 : ℝ} (hb : SpecBottom ρ M2)
    (hσ : rateMeasure (X.time 1) u = σ 0) : X.gap ^ 2 ≤ M2 := by
  by_contra hlt'
  have hlt := not_le.mp hlt'
  have hg := X.gap_pos
  have h0 := gap_rateBottom X u hu
  rw [hσ, hkl 0 le_rfl, Measure.map_apply (measurable_shell 0) measurableSet_Iio,
    withDensity_apply_eq_zero (measurable_klWeight 0)] at h0
  -- the set `[M2, gap²)` has positive `ρ`-mass and lies, off `s ≤ 0`, in the zero set above
  have hp := hb.2 (X.gap ^ 2 - M2) (sub_pos.mpr hlt)
  rw [add_sub_cancel] at hp
  have hsub : Ico M2 (X.gap ^ 2) ⊆
      ({s | klWeight 0 s ≠ 0} ∩ (fun s => shell s 0) ⁻¹' Iio X.gap) ∪ Iic 0 := by
    intro s hs
    rcases le_or_gt s 0 with hs0 | hs0
    · exact Or.inr hs0
    · have hsh : 0 < shell s 0 := by unfold shell; rw [add_zero]; exact Real.sqrt_pos.mpr hs0
      refine Or.inl (Set.mem_inter ?_ ?_)
      · simp only [mem_setOf_eq, klWeight, ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact one_div_pos.mpr (mul_pos two_pos hsh)
      · simp only [mem_preimage, mem_Iio, shell, add_zero]
        rw [Real.sqrt_lt' hg]
        exact hs.2
  have := (measure_mono (μ := ρ) hsub).trans (measure_union_le (μ := ρ) _ _)
  rw [h0, hρ0, add_zero] at this
  exact (lt_of_lt_of_le hp this).false

/-- **The zero-momentum read of the Clay object**: under the hypotheses of `clay_gap_sq_le`, the band
mass is positive, the Clay gap is at most `√M2`, the vector decays at the rate `√M2`, its correlator's
read tends to `√M2`, and every momentum sector has band excess. DERIVED: `0` the zero momentum, the
signs and the vanishing pairing; `1` the unit step; `2` the square. -/
theorem clay_zero_momentum (X : OSDataS) (u : X.H) (hu : inner ℂ X.vac u = 0)
    {σ : ℝ → Measure ℝ} {ρ : Measure ℝ} [IsFiniteMeasure ρ] (hkl : KallenLehmann σ ρ)
    (hρ0 : ρ (Iic 0) = 0) {M2 : ℝ} (hb : SpecBottom ρ M2)
    (hσ : rateMeasure (X.time 1) u = σ 0) :
    0 < M2 ∧ X.gap ≤ Real.sqrt M2
      ∧ (∀ t, 0 ≤ t → ‖X.time t u‖ ≤ Real.exp (-(Real.sqrt M2 * t)) * ‖u‖)
      ∧ Tendsto (fun τ => -Real.log ((inner ℂ u (X.time τ u)).re) / τ) atTop (𝓝 (Real.sqrt M2))
      ∧ ∀ p2, 0 ≤ p2 → Real.sqrt p2 < shell M2 p2 := by
  have hsq := clay_gap_sq_le X u hu hkl hρ0 hb hσ
  have hg := X.gap_pos
  have hM : 0 < M2 := lt_of_lt_of_le (pow_pos hg 2) hsq
  have hM0 : 0 < M2 + 0 := by rw [add_zero]; exact hM
  have hsh : shell M2 0 = Real.sqrt M2 := by unfold shell; rw [add_zero]
  have hbot := specBottom_klSector hkl hb le_rfl hM0
  rw [← hσ, hsh] at hbot
  refine ⟨hM, gap_le_of_specBottom X u hu hbot, fun t ht => time_bound_of_rateBottom X u hbot.1 ht,
    ?_, fun p2 hp => ?_⟩
  · have h := shell_rate_of_kl hkl hb le_rfl hM0 (C := fun τ => (inner ℂ u (X.time τ u)).re)
      (fun τ hτ => by
        rw [time_eq_powT X hτ.le, re_inner_powT_eq_laplace (spectrum_time X zero_le_one) u hτ, hσ])
    rwa [hsh] at h
  · exact (gap_iff_band_excess (specBottom_dirac M2) hp (by linarith)
      (shell_rate (specBottom_dirac M2) (by linarith))).mp hM

/-! ## 4. Load tests -/

section Load

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **The free single mode** `a = e^{−m}` as a scalar operator: `‖a^t u‖ = e^{−mt} ‖u‖`.
DERIVED: `m` is the mode's rate, a free variable of the test, not a chosen value. -/
theorem norm_powT_scalar (m t : ℝ) (u : E) :
    ‖powT (algebraMap ℝ (E →L[ℂ] E) (Real.exp (-m))) t u‖ = Real.exp (-(m * t)) * ‖u‖ := by
  unfold powT
  rw [cfc_algebraMap, ← Real.exp_mul, Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  congr 2
  ring

/-- DERIVED: `0` the sign of `m`; `1` the top of the spectrum interval. -/
theorem spectrum_scalar {m : ℝ} (hm : 0 ≤ m) :
    spectrum ℝ (algebraMap ℝ (E →L[ℂ] E) (Real.exp (-m))) ⊆ Icc 0 1 := fun x hx => by
  rw [Set.mem_singleton_iff.mp (CFC.spectrum_algebraMap_subset _ hx)]
  exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩

/-- **The free mode's rate bottom is its rate**: the rate measure vanishes below `m` and charges
`(−∞, g)` for every `g > m`, for every `u ≠ 0`. DERIVED: `0` the signs and the zero vector. -/
theorem scalar_rate_bottom {m : ℝ} (hm : 0 ≤ m) {u : E} (hu : u ≠ 0) :
    rateMeasure (algebraMap ℝ (E →L[ℂ] E) (Real.exp (-m))) u (Iio m) = 0
      ∧ ∀ g, m < g → rateMeasure (algebraMap ℝ (E →L[ℂ] E) (Real.exp (-m))) u (Iio g) ≠ 0 := by
  have ha : IsSelfAdjoint (algebraMap ℝ (E →L[ℂ] E) (Real.exp (-m))) :=
    cfc_predicate_algebraMap (A := E →L[ℂ] E) _
  have hsp := spectrum_scalar (E := E) hm
  refine ⟨(bound_iff_rateBottom ha hsp u m).mp fun t _ => (norm_powT_scalar m t u).le,
    fun g hg h => ?_⟩
  have hb := (bound_iff_rateBottom ha hsp u g).mpr h 1 zero_le_one
  rw [norm_powT_scalar, mul_one, mul_one] at hb
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have := le_of_mul_le_mul_right hb hun
  rw [Real.exp_le_exp] at this
  linarith

/-- **A rate measure touching `0` has no gap**: at `m = 0` the mode is the identity, a second vacuum;
its rate measure charges `(−∞, g)` for every `g > 0` and no rate `g > 0` holds.
DERIVED: `0` the mode's rate (the degenerate case) and the signs. -/
theorem identity_no_gap {u : E} (hu : u ≠ 0) :
    (∀ g, 0 < g → rateMeasure (algebraMap ℝ (E →L[ℂ] E) (Real.exp (-0))) u (Iio g) ≠ 0)
      ∧ ∀ g, 0 < g → ¬ ∀ t, 0 ≤ t →
        ‖powT (algebraMap ℝ (E →L[ℂ] E) (Real.exp (-0))) t u‖ ≤ Real.exp (-(g * t)) * ‖u‖ := by
  have ha : IsSelfAdjoint (algebraMap ℝ (E →L[ℂ] E) (Real.exp (-0))) :=
    cfc_predicate_algebraMap (A := E →L[ℂ] E) _
  have hsp := spectrum_scalar (E := E) (le_refl (0 : ℝ))
  have h := (scalar_rate_bottom (le_refl (0 : ℝ)) hu).2
  exact ⟨h, fun g hg hb => h g hg ((bound_iff_rateBottom ha hsp u g).mp hb)⟩

/-- **No `OSDataS` has a complement vector whose rate measure touches `0`.** DERIVED: `0` the
vanishing pairing and the touching point; `1` the unit step. -/
theorem no_gap_of_rate_touches_zero (X : OSDataS) (u : X.H) (hu : inner ℂ X.vac u = 0)
    (h : ∀ g, 0 < g → rateMeasure (X.time 1) u (Iio g) ≠ 0) : False :=
  h X.gap X.gap_pos (gap_rateBottom X u hu)

/-- **The free Källén–Lehmann sector at zero momentum has bottom `√m²`.** DERIVED: `0` the zero
momentum and the sign. -/
theorem free_zero_specBottom {m2 : ℝ} (hm : 0 < m2) : SpecBottom (freeRate m2 0) (shell m2 0) :=
  specBottom_klSector (free_kallenLehmann m2) (specBottom_dirac m2) le_rfl (by rw [add_zero]; exact hm)

end Load

end

end MassGap.ShellGap

#print axioms MassGap.ShellGap.spectrum_Icc_of_nonneg
#print axioms MassGap.ShellGap.sq_norm_powT_apply
#print axioms MassGap.ShellGap.rateMeasure_real_univ_le
#print axioms MassGap.ShellGap.rateBottom_of_bound
#print axioms MassGap.ShellGap.bound_of_rateBottom
#print axioms MassGap.ShellGap.bound_iff_rateBottom
#print axioms MassGap.ShellGap.rate_bottom_sharp
#print axioms MassGap.ShellGap.time_nonneg
#print axioms MassGap.ShellGap.spectrum_time
#print axioms MassGap.ShellGap.time_dyadic
#print axioms MassGap.ShellGap.time_dyadic_mul
#print axioms MassGap.ShellGap.time_eq_powT
#print axioms MassGap.ShellGap.time_laplaceRep
#print axioms MassGap.ShellGap.gap_rateBottom
#print axioms MassGap.ShellGap.time_bound_of_rateBottom
#print axioms MassGap.ShellGap.gap_iff_rateBottom
#print axioms MassGap.ShellGap.gap_le_of_specBottom
#print axioms MassGap.ShellGap.specBottom_klSector
#print axioms MassGap.ShellGap.clay_gap_sq_le
#print axioms MassGap.ShellGap.clay_zero_momentum
#print axioms MassGap.ShellGap.norm_powT_scalar
#print axioms MassGap.ShellGap.scalar_rate_bottom
#print axioms MassGap.ShellGap.identity_no_gap
#print axioms MassGap.ShellGap.no_gap_of_rate_touches_zero
#print axioms MassGap.ShellGap.free_zero_specBottom
#print axioms MassGap.ShellGap.time_isSelfAdjoint
#print axioms MassGap.ShellGap.time_nat_mul
#print axioms MassGap.ShellGap.spectrum_scalar
