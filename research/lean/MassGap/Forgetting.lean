import Mathlib
import MassGap.Aperture

/-!
# The six faces of forgetting at a finite aperture (PAPER §4, §6)

Through a finite aperture the propagator has finitely many modes, so the autocorrelation is a finite
exponential sum `C τ = ∑_{k∈s} P k (μ k)^τ` ([E, §9]). "The flow forgets" has several equivalent
faces; the load-bearing ones are:

  (i)   Λ            the Cesàro quadratic mean `(1/N) ∑_{τ<N} ‖C τ‖² → 0` (weakest, read directly)
  (ii)  `C τ → 0`    the reach-freeze monotone (`finite_flow_decays`, `Aperture.lean`)
  (iii) margin       the weight-carrying radius is `< 1`
  (iv)  exp decay    `‖C τ‖ ≤ (∑‖P‖) ρ^τ`, `ρ < 1` (`finite_sum_margin_bound`)
  (v)   summable     `∑_τ ‖C τ‖ < ∞` (finite correlation length)

This module states Λ and proves the forward cycle `margin ⟹ (C → 0) ∧ summable ∧ Λ`
(`bridge_forward`), together with the foil that a persistent unit-circle mode fails Λ
(`persistent_not_forgets`): the abelian massless current is the unique violation.

The converse `Λ ⟹ margin` is the finite Wiener mean-square step: for a finite exponential sum the Cesàro
mean of `‖C‖²` equals the squared weight carried by the unit-circle modes, so it vanishes exactly when no
persistent mode carries weight. It is the read-level characterisation of forgetting, supplied by the
companion instrument [E]. The gap uses only the forward direction proved here (`margin ⟹ C → 0`), so the
converse is not an input to the reduction.
-/

open Filter Topology

namespace MassGap

variable {ι : Type*}

/-- **Face (i), Axiom Λ (forgetting).** The Cesàro quadratic mean of the autocorrelation vanishes:
`(1/N) ∑_{τ<N} ‖C τ‖² → 0`. The weakest face, read straight off the screen. -/
def Forgets (C : ℕ → ℂ) : Prop :=
  Tendsto (fun N : ℕ => (∑ τ ∈ Finset.range N, ‖C τ‖ ^ 2) / (N : ℝ)) atTop (𝓝 0)

/-- **Face (v): margin ⟹ summable (finite correlation length).** A finite exponential sum whose modes
share a margin `ρ < 1` is absolutely summable: `∑_τ ‖C τ‖ < ∞`, a finite integral correlation
length. -/
theorem flow_summable (s : Finset ι) (P μ : ι → ℂ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hμ : ∀ k ∈ s, ‖μ k‖ ≤ ρ) :
    Summable (fun τ => ‖∑ k ∈ s, P k * (μ k) ^ τ‖) := by
  have hgeo : Summable (fun τ : ℕ => (∑ k ∈ s, ‖P k‖) * ρ ^ τ) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  exact Summable.of_nonneg_of_le (fun τ => norm_nonneg _)
    (fun τ => finite_sum_margin_bound s P μ ρ hμ τ) hgeo

/-- **Face (i) from (iii): margin ⟹ Λ (the flow forgets).** With a spectral margin `ρ < 1` the
Cesàro quadratic mean of the autocorrelation vanishes: the gap is the read-level forgetting. The
squared correlator is dominated by a geometric series in `ρ²`, whose partial sums are bounded, so the
Cesàro average tends to zero. -/
theorem forgets_of_margin (s : Finset ι) (P μ : ι → ℂ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hμ : ∀ k ∈ s, ‖μ k‖ ≤ ρ) :
    Forgets (fun τ => ∑ k ∈ s, P k * (μ k) ^ τ) := by
  have hMnn : 0 ≤ ∑ k ∈ s, ‖P k‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hρ2nn : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  have hρ2 : ρ ^ 2 < 1 := by
    nlinarith [mul_nonneg hρ0 (show (0 : ℝ) ≤ 1 - ρ by linarith), hρ1]
  have hgeo : Summable (fun τ : ℕ => (∑ k ∈ s, ‖P k‖) ^ 2 * (ρ ^ 2) ^ τ) :=
    (summable_geometric_of_lt_one hρ2nn hρ2).mul_left _
  have hle : ∀ τ, ‖∑ k ∈ s, P k * (μ k) ^ τ‖ ^ 2 ≤ (∑ k ∈ s, ‖P k‖) ^ 2 * (ρ ^ 2) ^ τ := by
    intro τ
    have h := finite_sum_margin_bound s P μ ρ hμ τ
    have hMρ : 0 ≤ (∑ k ∈ s, ‖P k‖) * ρ ^ τ := mul_nonneg hMnn (pow_nonneg hρ0 τ)
    calc ‖∑ k ∈ s, P k * (μ k) ^ τ‖ ^ 2
        ≤ ((∑ k ∈ s, ‖P k‖) * ρ ^ τ) ^ 2 := by
            nlinarith [mul_le_mul h h (norm_nonneg (∑ k ∈ s, P k * (μ k) ^ τ)) hMρ]
      _ = (∑ k ∈ s, ‖P k‖) ^ 2 * (ρ ^ 2) ^ τ := by rw [mul_pow, pow_right_comm]
  have hsq : Summable (fun τ => ‖∑ k ∈ s, P k * (μ k) ^ τ‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun τ => sq_nonneg _) hle hgeo
  exact hsq.hasSum.tendsto_sum_nat.div_atTop tendsto_natCast_atTop_atTop

/-- **The forward cycle of the bridge.** A spectral margin `ρ < 1` (face (iii)) delivers the weaker
faces at once: the flow decays (`C τ → 0`, face (ii)), has a finite correlation length (summable,
face (v)), and forgets (Λ, face (i)). -/
theorem bridge_forward (s : Finset ι) (P μ : ι → ℂ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hμ : ∀ k ∈ s, ‖μ k‖ ≤ ρ) :
    Tendsto (fun τ => ‖∑ k ∈ s, P k * (μ k) ^ τ‖) atTop (𝓝 0) ∧
      Summable (fun τ => ‖∑ k ∈ s, P k * (μ k) ^ τ‖) ∧
      Forgets (fun τ => ∑ k ∈ s, P k * (μ k) ^ τ) :=
  ⟨finite_flow_decays s P μ ρ hρ0 hρ1 hμ, flow_summable s P μ ρ hρ0 hρ1 hμ,
   forgets_of_margin s P μ ρ hρ0 hρ1 hμ⟩

/-- **The foil: a persistent unit-circle mode fails Λ.** A single mode `C τ = P μ^τ` on the unit
circle (`‖μ‖ = 1`, `P ≠ 0`) has constant magnitude `‖C τ‖ = ‖P‖`, so its Cesàro mean is `‖P‖² > 0`:
the flow does not forget. This is the abelian foil, the massless persistent current, the unique
violation of Λ. -/
theorem persistent_not_forgets (P μ : ℂ) (hμ : ‖μ‖ = 1) (hP : P ≠ 0) :
    ¬ Forgets (fun τ => P * μ ^ τ) := by
  intro h
  have hconst : Tendsto (fun N : ℕ => (∑ τ ∈ Finset.range N, ‖P * μ ^ τ‖ ^ 2) / (N : ℝ)) atTop
      (𝓝 (‖P‖ ^ 2)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hterm : ∀ τ, ‖P * μ ^ τ‖ ^ 2 = ‖P‖ ^ 2 := fun τ => by
      rw [norm_mul, norm_pow, hμ, one_pow, mul_one]
    rw [Finset.sum_congr rfl (fun τ _ => hterm τ), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_comm, mul_div_assoc, div_self hNne, mul_one]
  have hP0 : ‖P‖ ^ 2 = 0 := (tendsto_nhds_unique h hconst).symm
  exact hP (norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hP0))

end MassGap
