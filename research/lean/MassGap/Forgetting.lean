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

## THE CONVERSE IS PROVED HERE, and it needed no instrument

`Λ` is the WEAKEST face — a Cesàro average, not a pointwise bound at every coupling — so the converse
is what makes it sufficient rather than merely necessary.

`forgets_forces_zero_net_weight` is that converse: **if the flow forgets, then at every `ζ` on the
unit circle the modes sitting at `ζ` sum to zero.** Modes may lie on the circle, but only in
cancelling combinations; a single uncancelled one is `persistent_not_forgets`, which the general
statement contains as the one-mode case.

**It is finite-dimensional algebra plus one application of Cauchy–Schwarz**, and it is proved in this
file with a foundational-only footprint. An earlier note in this header said the converse was
"supplied by the companion instrument"; it is not, and does not need to be.

**The route is not the Wiener mean-square one.** That route expands `‖C τ‖²` as a double sum and
computes its Cesàro limit exactly. `forgets_forces_zero_net_weight` never computes that limit:
`cesaro_extract` averages `C` against `ζ^{-τ}` to converge on the net weight at `ζ`, and
`cesaro_norm_sq_le` bounds that average's squared norm by the very Cesàro mean of `‖C‖²` that `Λ`
sends to zero. The two limits meet at zero. A previous version of this note described the Wiener
route as the proof; it was a description of a different, longer argument.
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


/-! ## The converse, and it is algebra rather than a read

`persistent_not_forgets` refutes Λ for ONE mode on the unit circle. The general converse is the
statement that Λ forces every unit-circle value to carry zero NET weight — modes may sit on the
circle, but only in cancelling combinations. The module docstring deferred this to the companion
instrument; it does not need one.

**The usual route computes the Cesàro limit of `‖C τ‖²` exactly (the finite Wiener mean-square
theorem). This does not.** Instead it extracts the weight at a single value `ζ` by averaging `C`
against `ζ^{-τ}`, and bounds that average by Cauchy–Schwarz against the very quantity Λ says goes to
zero:

    ‖(1/N) ∑_{τ<N} C τ · ζ^{-τ}‖²  ≤  (1/N) ∑_{τ<N} ‖C τ‖²  →  0,

while the left-hand side converges to the net weight at `ζ`. So the net weight is zero, and no limit
of `‖C‖²` ever has to be computed.

`ζ⁻¹` is used rather than the conjugate throughout. On the unit circle they agree, and the inverse
keeps every step inside field algebra: `μ · ζ⁻¹ = 1 ↔ μ = ζ` needs only `ζ ≠ 0`.
-/

/-- **A CESÀRO GEOMETRIC MEAN VANISHES OFF ONE.** For `‖z‖ ≤ 1` with `z ≠ 1` the partial sums
`∑_{τ<N} z^τ` are BOUNDED — `geom_sum_eq` puts them at `(z^N − 1)/(z − 1)`, of norm at most
`2/‖z − 1‖` — so their Cesàro average tends to zero.

DERIVED: the `2` is `‖z^N‖ + ‖1‖ ≤ 1 + 1`, the triangle inequality at `‖z‖ ≤ 1`. Not a chosen
constant. -/
theorem cesaro_geom_tendsto_zero {z : ℂ} (hz1 : ‖z‖ ≤ 1) (hz : z ≠ 1) :
    Tendsto (fun N : ℕ => (∑ τ ∈ Finset.range N, z ^ τ) / (N : ℂ)) atTop (𝓝 0) := by
  have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr hsub
  have hbd : ∀ N : ℕ, ‖(∑ τ ∈ Finset.range N, z ^ τ) / (N : ℂ)‖ ≤ (2 / ‖z - 1‖) / (N : ℝ) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    have hnum : ‖z ^ N - 1‖ ≤ 2 := by
      have h1 : ‖z ^ N‖ ≤ 1 := by
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) hz1
      have h2 : ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      rw [norm_one] at h2
      linarith
    rw [geom_sum_eq hz, norm_div, norm_div, Complex.norm_natCast]
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    gcongr
  refine squeeze_zero_norm hbd ?_
  exact tendsto_const_div_atTop_nhds_zero_nat _

#print axioms cesaro_geom_tendsto_zero

/-- On the unit circle, `μ · ζ⁻¹ = 1` says exactly `μ = ζ`. Field algebra, no conjugation. -/
theorem mul_inv_eq_one_iff_eq {μ ζ : ℂ} (hζ : ζ ≠ 0) : μ * ζ⁻¹ = 1 ↔ μ = ζ := by
  constructor
  · intro h
    field_simp at h
    exact h
  · rintro rfl
    exact mul_inv_cancel₀ hζ

#print axioms mul_inv_eq_one_iff_eq

open scoped Classical in
/-- **THE WEIGHT AT ONE VALUE IS EXTRACTED BY A CESÀRO AVERAGE.**

`(1/N) ∑_{τ<N} C τ · ζ^{-τ} → ∑_{k : μ k = ζ} P k`. Every mode off `ζ` contributes a geometric
average that dies (`cesaro_geom_tendsto_zero`); every mode at `ζ` contributes `1` at every `τ`. -/
theorem cesaro_extract (s : Finset ι) (P μ : ι → ℂ) (hμ : ∀ k ∈ s, ‖μ k‖ ≤ 1)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    Tendsto (fun N : ℕ =>
        (∑ τ ∈ Finset.range N, (∑ k ∈ s, P k * (μ k) ^ τ) * (ζ⁻¹) ^ τ) / (N : ℂ))
      atTop (𝓝 (∑ k ∈ s.filter (fun k => μ k = ζ), P k)) := by
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hζ
    exact zero_ne_one hζ
  have hζinv : ‖ζ⁻¹‖ = 1 := by
    rw [norm_inv, hζ, inv_one]
  -- swap the two sums and pull the coefficient out
  have hrw : ∀ N : ℕ,
      (∑ τ ∈ Finset.range N, (∑ k ∈ s, P k * (μ k) ^ τ) * (ζ⁻¹) ^ τ) / (N : ℂ)
        = ∑ k ∈ s, P k * ((∑ τ ∈ Finset.range N, (μ k * ζ⁻¹) ^ τ) / (N : ℂ)) := by
    intro N
    have h1 : ∀ τ : ℕ, (∑ k ∈ s, P k * (μ k) ^ τ) * (ζ⁻¹) ^ τ
        = ∑ k ∈ s, P k * (μ k * ζ⁻¹) ^ τ := by
      intro τ
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [mul_pow]
      ring
    simp only [h1]
    rw [Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.mul_sum, mul_div_assoc]
  simp only [hrw]
  have hterm : ∀ k ∈ s, Tendsto
      (fun N : ℕ => P k * ((∑ τ ∈ Finset.range N, (μ k * ζ⁻¹) ^ τ) / (N : ℂ)))
      atTop (𝓝 (if μ k = ζ then P k else 0)) := by
    intro k hk
    by_cases hmk : μ k = ζ
    · rw [if_pos hmk]
      have hone : μ k * ζ⁻¹ = 1 := (mul_inv_eq_one_iff_eq hζ0).mpr hmk
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hNne : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
      rw [hone]
      simp [hNne]
    · rw [if_neg hmk]
      have hne : μ k * ζ⁻¹ ≠ 1 := fun hc => hmk ((mul_inv_eq_one_iff_eq hζ0).mp hc)
      have hnorm : ‖μ k * ζ⁻¹‖ ≤ 1 := by
        rw [norm_mul, hζinv, mul_one]
        exact hμ k hk
      simpa using (cesaro_geom_tendsto_zero hnorm hne).const_mul (P k)
  have hsum := tendsto_finset_sum s hterm
  simpa [Finset.sum_filter] using hsum

#print axioms cesaro_extract

/-- **THE AVERAGE IS CONTROLLED BY THE QUANTITY Λ SENDS TO ZERO.** Cauchy–Schwarz on the range:
`‖(1/N)∑ C·w‖² ≤ (1/N)∑‖C‖²` whenever `‖w‖ ≤ 1`.

DERIVED: the `2`s are squares; `sq_sum_le_card_mul_sum_sq` supplies the `N`. -/
theorem cesaro_norm_sq_le (C w : ℕ → ℂ) (hw : ∀ τ, ‖w τ‖ ≤ 1) (N : ℕ) :
    ‖(∑ τ ∈ Finset.range N, C τ * w τ) / (N : ℂ)‖ ^ 2
      ≤ (∑ τ ∈ Finset.range N, ‖C τ‖ ^ 2) / (N : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h1 : ‖∑ τ ∈ Finset.range N, C τ * w τ‖ ≤ ∑ τ ∈ Finset.range N, ‖C τ‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun τ _ => ?_))
    rw [norm_mul]
    calc ‖C τ‖ * ‖w τ‖ ≤ ‖C τ‖ * 1 :=
          mul_le_mul_of_nonneg_left (hw τ) (norm_nonneg _)
      _ = ‖C τ‖ := mul_one _
  have h2 : (∑ τ ∈ Finset.range N, ‖C τ‖) ^ 2
      ≤ (N : ℝ) * ∑ τ ∈ Finset.range N, ‖C τ‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range N) (f := fun τ => ‖C τ‖)
    simpa using this
  have h3 : ‖∑ τ ∈ Finset.range N, C τ * w τ‖ ^ 2
      ≤ (N : ℝ) * ∑ τ ∈ Finset.range N, ‖C τ‖ ^ 2 :=
    le_trans (pow_le_pow_left₀ (norm_nonneg _) h1 2) h2
  rw [norm_div, Complex.norm_natCast, div_pow, div_le_div_iff₀ (by positivity) hNpos]
  calc ‖∑ τ ∈ Finset.range N, C τ * w τ‖ ^ 2 * (N : ℝ)
      ≤ ((N : ℝ) * ∑ τ ∈ Finset.range N, ‖C τ‖ ^ 2) * (N : ℝ) :=
        mul_le_mul_of_nonneg_right h3 hNpos.le
    _ = (∑ τ ∈ Finset.range N, ‖C τ‖ ^ 2) * (N : ℝ) ^ 2 := by ring

#print axioms cesaro_norm_sq_le

open scoped Classical in
/-- **THE CONVERSE: Λ FORCES EVERY UNIT-CIRCLE VALUE TO CARRY ZERO NET WEIGHT.**

If the flow forgets, then at every `ζ` on the unit circle the modes sitting at `ζ` sum to zero. Modes
may lie on the circle, but only in cancelling combinations — a single uncancelled one is
`persistent_not_forgets`, which this contains as the case of one mode.

**No Wiener mean-square limit is computed.** `cesaro_extract` converges to the net weight,
`cesaro_norm_sq_le` bounds it by what Λ sends to zero, and the two limits meet at zero.

This is the step this file's header once deferred to a companion instrument. It does not need one:
it is finite-dimensional algebra plus one application of Cauchy–Schwarz. -/
theorem forgets_forces_zero_net_weight (s : Finset ι) (P μ : ι → ℂ)
    (hμ : ∀ k ∈ s, ‖μ k‖ ≤ 1) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (h : Forgets (fun τ => ∑ k ∈ s, P k * (μ k) ^ τ)) :
    ∑ k ∈ s.filter (fun k => μ k = ζ), P k = 0 := by
  set C : ℕ → ℂ := fun τ => ∑ k ∈ s, P k * (μ k) ^ τ with hC
  set L : ℂ := ∑ k ∈ s.filter (fun k => μ k = ζ), P k with hL
  have hζ0 : ζ ≠ 0 := by
    intro hc
    rw [hc, norm_zero] at hζ
    exact zero_ne_one hζ
  have hw : ∀ τ : ℕ, ‖(ζ⁻¹) ^ τ‖ ≤ 1 := by
    intro τ
    rw [norm_pow, norm_inv, hζ, inv_one, one_pow]
  -- the average converges to the net weight, so its squared norm converges to ‖L‖²
  have hA : Tendsto (fun N : ℕ => ‖(∑ τ ∈ Finset.range N, C τ * (ζ⁻¹) ^ τ) / (N : ℂ)‖ ^ 2)
      atTop (𝓝 (‖L‖ ^ 2)) :=
    ((cesaro_extract s P μ hμ hζ).norm).pow 2
  -- and it is dominated by the Cesàro mean of ‖C‖², which Λ sends to zero
  have hle : ∀ N : ℕ, ‖(∑ τ ∈ Finset.range N, C τ * (ζ⁻¹) ^ τ) / (N : ℂ)‖ ^ 2
      ≤ (∑ τ ∈ Finset.range N, ‖C τ‖ ^ 2) / (N : ℝ) :=
    fun N => cesaro_norm_sq_le C (fun τ => (ζ⁻¹) ^ τ) hw N
  have hsq : ‖L‖ ^ 2 ≤ 0 :=
    le_of_tendsto_of_tendsto' hA h hle
  have : ‖L‖ = 0 := by nlinarith [norm_nonneg L]
  exact norm_eq_zero.mp this

#print axioms forgets_forces_zero_net_weight


/-! ## Closing the cycle: Λ ⟺ margin

`forgets_forces_zero_net_weight` says the unit-circle weight CANCELS. To turn that into a margin the
cancellation has to be ruled out, and two conditions do it: the modes are DISTINCT, so each
unit-circle value is carried by at most one of them, and the weights are NONZERO, so that one cannot
cancel against itself.

Both are conditions on the presentation rather than on the flow. A finite exponential sum can always
be put in this form by collecting equal modes and discarding zero weights — the sum is unchanged, so
nothing is assumed about the flow at all. They are stated as hypotheses rather than performed as a
normalisation because performing it would add a construction and prove the same thing.

With them, `bridge_forward` and `margin_of_forgets` close the cycle at the WEAKEST face:
`forgets_iff_margin`. Λ is not merely implied by a spectral margin — for a finite exponential sum it
IS one.
-/

open scoped Classical in
/-- **EVERY MODE IS STRICTLY INSIDE THE DISC.** If the flow forgets and the modes are distinct with
nonzero weights, none of them can sit on the unit circle: the converse would make its weight the
whole net weight at that value, and the net weight is zero. -/
theorem norm_lt_one_of_forgets (s : Finset ι) (P μ : ι → ℂ)
    (hμ1 : ∀ k ∈ s, ‖μ k‖ ≤ 1)
    (hinj : ∀ k ∈ s, ∀ l ∈ s, μ k = μ l → k = l)
    (hP : ∀ k ∈ s, P k ≠ 0)
    (h : Forgets (fun τ => ∑ k ∈ s, P k * (μ k) ^ τ))
    {k₀ : ι} (hk₀ : k₀ ∈ s) : ‖μ k₀‖ < 1 := by
  rcases lt_or_eq_of_le (hμ1 k₀ hk₀) with hlt | heq
  · exact hlt
  · exfalso
    have hnet := forgets_forces_zero_net_weight s P μ hμ1 heq h
    have hfil : s.filter (fun k => μ k = μ k₀) = {k₀} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hk, hmk⟩
        exact hinj k hk k₀ hk₀ hmk
      · rintro rfl
        exact ⟨hk₀, rfl⟩
    rw [hfil, Finset.sum_singleton] at hnet
    exact hP k₀ hk₀ hnet

#print axioms norm_lt_one_of_forgets

/-- **AND THEREFORE THEY SHARE A MARGIN.** Finitely many moduli, each below one, have a maximum below
one — `Finset.sup'` on a nonempty index set, and the empty case is vacuous at `ρ = 0`.

DERIVED: `1` is the unit circle and `0` is the vacuous witness; neither is a chosen level. -/
theorem margin_of_forgets (s : Finset ι) (P μ : ι → ℂ)
    (hμ1 : ∀ k ∈ s, ‖μ k‖ ≤ 1)
    (hinj : ∀ k ∈ s, ∀ l ∈ s, μ k = μ l → k = l)
    (hP : ∀ k ∈ s, P k ≠ 0)
    (h : Forgets (fun τ => ∑ k ∈ s, P k * (μ k) ^ τ)) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ k ∈ s, ‖μ k‖ ≤ ρ := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, le_rfl, by norm_num, fun k hk => absurd hk (Finset.notMem_empty k)⟩
  · refine ⟨s.sup' hne (fun k => ‖μ k‖), ?_, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := hne
      exact le_trans (norm_nonneg (μ k)) (Finset.le_sup' (fun k => ‖μ k‖) hk)
    · rw [Finset.sup'_lt_iff]
      exact fun k hk => norm_lt_one_of_forgets s P μ hμ1 hinj hP h hk
    · exact fun k hk => Finset.le_sup' (fun k => ‖μ k‖) hk

#print axioms margin_of_forgets

/-- **Λ ⟺ MARGIN.** The cycle of faces, closed at the weakest one.

`bridge_forward` gives the forward direction and `margin_of_forgets` the converse, so for a finite
exponential sum with distinct modes and nonzero weights, forgetting is not merely implied by a
spectral margin — **it IS one**.

That is what makes Λ worth having as a criterion: it is a Cesàro average, the weakest thing one can
read off a flow, and it is equivalent to the strongest thing one can say about its spectrum. -/
theorem forgets_iff_margin (s : Finset ι) (P μ : ι → ℂ)
    (hμ1 : ∀ k ∈ s, ‖μ k‖ ≤ 1)
    (hinj : ∀ k ∈ s, ∀ l ∈ s, μ k = μ l → k = l)
    (hP : ∀ k ∈ s, P k ≠ 0) :
    Forgets (fun τ => ∑ k ∈ s, P k * (μ k) ^ τ)
      ↔ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ k ∈ s, ‖μ k‖ ≤ ρ := by
  constructor
  · exact margin_of_forgets s P μ hμ1 hinj hP
  · rintro ⟨ρ, hρ0, hρ1, hρ⟩
    exact forgets_of_margin s P μ ρ hρ0 hρ1 hρ

#print axioms forgets_iff_margin

/-- **AND THE WHOLE CYCLE FROM Λ.** Forgetting delivers decay, summability — a finite correlation
length — and the margin itself. Every face of the bridge from the weakest one. -/
theorem bridge_from_forgets (s : Finset ι) (P μ : ι → ℂ)
    (hμ1 : ∀ k ∈ s, ‖μ k‖ ≤ 1)
    (hinj : ∀ k ∈ s, ∀ l ∈ s, μ k = μ l → k = l)
    (hP : ∀ k ∈ s, P k ≠ 0)
    (h : Forgets (fun τ => ∑ k ∈ s, P k * (μ k) ^ τ)) :
    Tendsto (fun τ => ‖∑ k ∈ s, P k * (μ k) ^ τ‖) atTop (𝓝 0) ∧
      Summable (fun τ => ‖∑ k ∈ s, P k * (μ k) ^ τ‖) ∧
      ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ k ∈ s, ‖μ k‖ ≤ ρ := by
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := margin_of_forgets s P μ hμ1 hinj hP h
  exact ⟨finite_flow_decays s P μ ρ hρ0 hρ1 hρ, flow_summable s P μ ρ hρ0 hρ1 hρ,
    ⟨ρ, hρ0, hρ1, hρ⟩⟩

#print axioms bridge_from_forgets


/-! ## The cycle is complete: decay ⟺ Λ ⟺ margin

`bridge_forward` runs margin ⟹ decay ⟹ … one way round. With `margin_of_forgets` the return arrow
exists, and one more step closes it at the remaining face: **a decaying flow forgets**, because the
Cesàro mean of a null sequence is null (`Filter.Tendsto.cesaro`). So for a finite exponential sum
with distinct modes and nonzero weights the three faces are the SAME statement.

**Why that matters beyond bookkeeping.** `Complete.ym_mass_gap_of_substrate` concludes, as its first
conjunct, exactly

    ∀ β, Tendsto (fun τ => ‖∑ k ∈ (ymModelAt N).s β, (ymModelAt N).P β k * ((ymModelAt N).m β k)^τ‖)
      atTop (𝓝 0)

— a finite exponential sum over `(ymModelAt N).s β`, tending to zero. That is face (ii). Under the
two presentation conditions it upgrades to a spectral MARGIN, hence to summability, hence to a finite
correlation length. **The flagship's own conclusion is therefore stronger than it reads**: decay of
the correlator is not weaker than a gap, it is a gap.

The conditions are on the presentation, not the physics — collect equal modes, discard zero weights —
but they are not discharged here for `ymModelAt`, because nothing in the tree establishes that its
modes are distinct or its weights nonzero. That is stated, not assumed.
-/

/-- **A DECAYING FLOW FORGETS.** The Cesàro mean of a null sequence is null, and `‖C τ‖ → 0` gives
`‖C τ‖² → 0`. Face (ii) ⟹ face (i), with no structure on `C` at all. -/
theorem forgets_of_decay {C : ℕ → ℂ} (h : Tendsto (fun τ => ‖C τ‖) atTop (𝓝 0)) :
    Forgets C := by
  have hsq : Tendsto (fun τ => ‖C τ‖ ^ 2) atTop (𝓝 0) := by
    simpa using h.pow 2
  -- `cesaro` produces `n⁻¹ * ∑`; `Forgets` is written `∑ / n`.
  exact hsq.cesaro.congr (fun n => by ring)

#print axioms forgets_of_decay

/-- **DECAY IS EQUIVALENT TO FORGETTING**, for any flow at all in one direction and for a finite
exponential sum in the other. -/
theorem decay_iff_forgets (s : Finset ι) (P μ : ι → ℂ)
    (hμ1 : ∀ k ∈ s, ‖μ k‖ ≤ 1)
    (hinj : ∀ k ∈ s, ∀ l ∈ s, μ k = μ l → k = l)
    (hP : ∀ k ∈ s, P k ≠ 0) :
    Tendsto (fun τ => ‖∑ k ∈ s, P k * (μ k) ^ τ‖) atTop (𝓝 0)
      ↔ Forgets (fun τ => ∑ k ∈ s, P k * (μ k) ^ τ) := by
  constructor
  · exact forgets_of_decay
  · intro h
    obtain ⟨ρ, hρ0, hρ1, hρ⟩ := margin_of_forgets s P μ hμ1 hinj hP h
    exact finite_flow_decays s P μ ρ hρ0 hρ1 hρ

#print axioms decay_iff_forgets

/-- **AND TO THE MARGIN.** The three faces collapse to one statement.

`Complete.ym_mass_gap_of_substrate`'s first conjunct is the left-hand side at the genuine Wilson
model, so under the two presentation conditions that conclusion already carries a spectral margin. -/
theorem decay_iff_margin (s : Finset ι) (P μ : ι → ℂ)
    (hμ1 : ∀ k ∈ s, ‖μ k‖ ≤ 1)
    (hinj : ∀ k ∈ s, ∀ l ∈ s, μ k = μ l → k = l)
    (hP : ∀ k ∈ s, P k ≠ 0) :
    Tendsto (fun τ => ‖∑ k ∈ s, P k * (μ k) ^ τ‖) atTop (𝓝 0)
      ↔ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ k ∈ s, ‖μ k‖ ≤ ρ :=
  (decay_iff_forgets s P μ hμ1 hinj hP).trans (forgets_iff_margin s P μ hμ1 hinj hP)

#print axioms decay_iff_margin

/-- **THE WHOLE BRIDGE, FROM DECAY.** What the flagship concludes, upgraded: decay of the correlator
delivers summability — a finite integral correlation length — and the spectral margin itself. -/
theorem bridge_from_decay (s : Finset ι) (P μ : ι → ℂ)
    (hμ1 : ∀ k ∈ s, ‖μ k‖ ≤ 1)
    (hinj : ∀ k ∈ s, ∀ l ∈ s, μ k = μ l → k = l)
    (hP : ∀ k ∈ s, P k ≠ 0)
    (h : Tendsto (fun τ => ‖∑ k ∈ s, P k * (μ k) ^ τ‖) atTop (𝓝 0)) :
    Summable (fun τ => ‖∑ k ∈ s, P k * (μ k) ^ τ‖) ∧
      Forgets (fun τ => ∑ k ∈ s, P k * (μ k) ^ τ) ∧
      ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ k ∈ s, ‖μ k‖ ≤ ρ := by
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := (decay_iff_margin s P μ hμ1 hinj hP).mp h
  exact ⟨flow_summable s P μ ρ hρ0 hρ1 hρ, forgets_of_decay h, ⟨ρ, hρ0, hρ1, hρ⟩⟩

#print axioms bridge_from_decay


/-! ## Removing the presentation conditions

`decay_iff_margin` assumes the modes are distinct and the weights nonzero. Those are conditions on
how the sum is WRITTEN, and any finite exponential sum can be rewritten to satisfy them: collect the
weights sharing a mode, then drop the modes whose collected weight is zero. The sum is unchanged, so
nothing is assumed about the flow.

**The conclusion has to change, and that is the point.** After collecting, the margin is about the
EFFECTIVE modes — the values carrying nonzero collected weight. It cannot be about the original `μ k`,
and the reason is the cancellation the converse already exposed: `P = (1, −1)` with `μ = (1, 1)` has
`C τ = 0` at every `τ`, so it decays, forgets, and has every face — while both its modes sit ON the
unit circle. A margin over the original modes would be FALSE there.

So the unconditional statement is `decay_iff_effective_margin`, and the earlier hypothesis-carrying
forms are the special case where collecting changes nothing.
-/

open scoped Classical in
/-- The weight the presentation puts at one value. -/
noncomputable def collectedWeight (s : Finset ι) (P μ : ι → ℂ) (ζ : ℂ) : ℂ :=
  ∑ k ∈ s.filter (fun k => μ k = ζ), P k

open scoped Classical in
/-- **COLLECTING EQUAL MODES LEAVES THE SUM ALONE.** Fibrewise summation over the image, with `μ k`
replaced by `ζ` inside each fibre because that is what the fibre says. -/
theorem collect_modes (s : Finset ι) (P μ : ι → ℂ) (τ : ℕ) :
    ∑ k ∈ s, P k * (μ k) ^ τ
      = ∑ ζ ∈ s.image μ, collectedWeight s P μ ζ * ζ ^ τ := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun k hk => Finset.mem_image_of_mem μ hk)
    (fun k => P k * (μ k) ^ τ)]
  refine Finset.sum_congr rfl (fun ζ _ => ?_)
  unfold collectedWeight
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [(Finset.mem_filter.mp hk).2]

#print axioms collect_modes

/-- A finite set of moduli all below one has a common margin, and conversely. -/
theorem margin_iff_all_lt_one (T : Finset ℂ) :
    (∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ ζ ∈ T, ‖ζ‖ ≤ ρ) ↔ ∀ ζ ∈ T, ‖ζ‖ < 1 := by
  constructor
  · rintro ⟨ρ, _, hρ1, hρ⟩ ζ hζ
    exact lt_of_le_of_lt (hρ ζ hζ) hρ1
  · intro h
    rcases T.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, le_rfl, by norm_num, fun ζ hζ => absurd hζ (Finset.notMem_empty ζ)⟩
    · refine ⟨T.sup' hne (fun ζ => ‖ζ‖), ?_, ?_, ?_⟩
      · obtain ⟨ζ, hζ⟩ := hne
        exact le_trans (norm_nonneg ζ) (Finset.le_sup' (fun ζ => ‖ζ‖) hζ)
      · rw [Finset.sup'_lt_iff]
        exact h
      · exact fun ζ hζ => Finset.le_sup' (fun ζ => ‖ζ‖) hζ

#print axioms margin_iff_all_lt_one

open scoped Classical in
/-- **THE EQUIVALENCE, WITH NO CONDITION ON THE PRESENTATION.**

A finite exponential sum inside the closed disc decays **iff every value carrying nonzero collected
weight is strictly inside it**. No distinctness and no nonvanishing is assumed; collecting supplies
both, and the conclusion is about the effective modes because it cannot be about the written ones.

This is the form that applies to `Complete.ym_mass_gap_of_substrate`'s first conjunct without any
unproved assumption about how `ymModelAt` presents its spectrum. -/
theorem decay_iff_effective_margin (s : Finset ι) (P μ : ι → ℂ)
    (hμ1 : ∀ k ∈ s, ‖μ k‖ ≤ 1) :
    Tendsto (fun τ => ‖∑ k ∈ s, P k * (μ k) ^ τ‖) atTop (𝓝 0)
      ↔ ∀ ζ ∈ s.image μ, collectedWeight s P μ ζ ≠ 0 → ‖ζ‖ < 1 := by
  set T : Finset ℂ := (s.image μ).filter (fun ζ => collectedWeight s P μ ζ ≠ 0) with hT
  -- the collected presentation has the same sum, on the trimmed index set
  have hsum : ∀ τ : ℕ, ∑ k ∈ s, P k * (μ k) ^ τ
      = ∑ ζ ∈ T, collectedWeight s P μ ζ * ζ ^ τ := by
    intro τ
    rw [collect_modes s P μ τ, hT]
    refine (Finset.sum_filter_of_ne (fun ζ _ hne => ?_)).symm
    intro hz
    exact hne (by rw [hz, zero_mul])
  have hμT : ∀ ζ ∈ T, ‖ζ‖ ≤ 1 := by
    intro ζ hζ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hζ).1
    exact hμ1 k hk
  have hinjT : ∀ ζ ∈ T, ∀ ξ ∈ T, ζ = ξ → ζ = ξ := fun _ _ _ _ h => h
  have hPT : ∀ ζ ∈ T, collectedWeight s P μ ζ ≠ 0 :=
    fun ζ hζ => (Finset.mem_filter.mp hζ).2
  have hiff := decay_iff_margin T (collectedWeight s P μ) id hμT hinjT hPT
  simp only [id] at hiff
  rw [show (fun τ : ℕ => ‖∑ k ∈ s, P k * (μ k) ^ τ‖)
      = fun τ : ℕ => ‖∑ ζ ∈ T, collectedWeight s P μ ζ * ζ ^ τ‖ from funext (fun τ => by
    rw [hsum τ])]
  rw [hiff, margin_iff_all_lt_one T]
  constructor
  · intro h ζ hζ hne
    exact h ζ (Finset.mem_filter.mpr ⟨hζ, hne⟩)
  · intro h ζ hζ
    exact h ζ (Finset.mem_filter.mp hζ).1 (Finset.mem_filter.mp hζ).2

#print axioms decay_iff_effective_margin

/-- **THE CANCELLING FOIL, EXHIBITED.** `P = (1, −1)` at `μ = (1, 1)`: the flow is identically zero,
so it decays and forgets, while BOTH modes sit on the unit circle. The margin cannot be about the
written modes, and this is why.

DERIVED: `1` and `−1` are the two weights and `1` the shared mode; nothing is a magnitude. -/
theorem cancelling_modes_decay_on_the_circle :
    Tendsto (fun τ => ‖∑ k ∈ (Finset.univ : Finset (Fin 2)),
        (![(1 : ℂ), -1] k) * (![(1 : ℂ), 1] k) ^ τ‖) atTop (𝓝 0) := by
  have hzero : ∀ τ : ℕ, ∑ k ∈ (Finset.univ : Finset (Fin 2)),
      (![(1 : ℂ), -1] k) * (![(1 : ℂ), 1] k) ^ τ = 0 := by
    intro τ
    simp [Fin.sum_univ_two]
  simpa [hzero] using tendsto_const_nhds (α := ℝ) (x := (0 : ℝ)) (f := atTop (α := ℕ))

#print axioms cancelling_modes_decay_on_the_circle

end MassGap
