import Mathlib
import MassGap.Aperture

/-!
# MassGap.Forgetting — equivalent conditions on a finite exponential sum

Throughout, `C τ = ∑_{k ∈ s} P k · (μ k)^τ` for a `Finset ι` and two functions `P`, `μ : ι → ℂ`. The
conditions compared are:

  (i)   `Forgets C`  the Cesàro quadratic mean `(1/N) ∑_{τ<N} ‖C τ‖² → 0`
  (ii)  `C τ → 0`    (`Aperture.finite_flow_decays`)
  (iii) margin       `∃ ρ < 1, ∀ k ∈ s, ‖μ k‖ ≤ ρ`
  (iv)  exp decay    `‖C τ‖ ≤ (∑‖P‖) ρ^τ` (`Aperture.finite_sum_margin_bound`)
  (v)   summable     `∑_τ ‖C τ‖ < ∞`

## The forward direction

`flow_summable` and `forgets_of_margin` derive (v) and (i) from (iii), and `bridge_forward` packages
them with (ii). `persistent_not_forgets` is the negative case: a single mode of unit modulus with
nonzero weight has constant `‖C τ‖`, so its Cesàro mean is `‖P‖² > 0` and (i) fails.

## The converse

`forgets_forces_zero_net_weight`: if (i) holds then at every `ζ` of unit modulus the modes sitting at
`ζ` have weights summing to zero. Modes may lie on the unit circle, but only in cancelling
combinations; `persistent_not_forgets` is the one-mode case.

The route does not compute the Cesàro limit of `‖C τ‖²`. `cesaro_extract` averages `C` against
`ζ^{-τ}` and converges to the net weight at `ζ`; `cesaro_norm_sq_le` bounds that average's squared
norm by the Cesàro mean of `‖C‖²`, which (i) sends to zero. `ζ⁻¹` is used rather than the conjugate:
on the unit circle they agree, and the inverse keeps every step in field algebra, since
`μ · ζ⁻¹ = 1 ↔ μ = ζ` needs only `ζ ≠ 0`.

## Closing the cycle

`norm_lt_one_of_forgets` and `margin_of_forgets` turn the cancellation statement into (iii), under
two hypotheses on the presentation: the modes are distinct (`hinj`) and the weights nonzero (`hP`).
`forgets_iff_margin`, `decay_iff_forgets`, `decay_iff_margin`, `bridge_from_forgets` and
`bridge_from_decay` are the resulting equivalences; `forgets_of_decay` supplies (ii) ⟹ (i) with no
structure on `C` at all.

## Removing the presentation hypotheses

`collectedWeight` and `collect_modes` rewrite the sum over the image of `μ`, collecting weights at
equal modes; `decay_iff_effective_margin` is the equivalence with no hypothesis on the presentation,
stated about the values carrying nonzero collected weight rather than about the written `μ k`. It
cannot be stated about the written ones: `cancelling_modes_decay_on_the_circle` exhibits
`P = (1, −1)` at `μ = (1, 1)`, where `C` is identically zero while both written modes have unit
modulus.
-/

open Filter Topology

namespace MassGap

variable {ι : Type*}

/-- Condition (i) as a `Prop` on an arbitrary sequence `C : ℕ → ℂ`: the Cesàro mean of `‖C τ‖²`
converges to `0` along `atTop`.

A statement about an average, so it permits `‖C τ‖` to be large on a set of density zero; it does not
imply `C τ → 0` for an arbitrary `C`, and the converse direction below needs the exponential-sum
form.

DERIVED: the exponent `2` is the square whose average is taken, which is what makes the Cauchy–Schwarz
step of `cesaro_norm_sq_le` available. `0` is the limit point. -/
def Forgets (C : ℕ → ℂ) : Prop :=
  Tendsto (fun N : ℕ => (∑ τ ∈ Finset.range N, ‖C τ‖ ^ 2) / (N : ℝ)) atTop (𝓝 0)

/-- If every mode satisfies `‖μ k‖ ≤ ρ` with `0 ≤ ρ < 1`, then `τ ↦ ‖∑ₖ P k (μ k)^τ‖` is summable.
`Aperture.finite_sum_margin_bound` dominates it by `(∑ₖ ‖P k‖) · ρ^τ`, which is summable as a
geometric series.

`P` is unconstrained: no sign, no bound, and the empty `s` is allowed.

DERIVED: `0` is the lower bound on `ρ` in `hρ0`, which the geometric series needs, and `1` is its
strict upper bound, which is what makes the series converge. -/
theorem flow_summable (s : Finset ι) (P μ : ι → ℂ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hμ : ∀ k ∈ s, ‖μ k‖ ≤ ρ) :
    Summable (fun τ => ‖∑ k ∈ s, P k * (μ k) ^ τ‖) := by
  have hgeo : Summable (fun τ : ℕ => (∑ k ∈ s, ‖P k‖) * ρ ^ τ) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  exact Summable.of_nonneg_of_le (fun τ => norm_nonneg _)
    (fun τ => finite_sum_margin_bound s P μ ρ hμ τ) hgeo

/-- If every mode satisfies `‖μ k‖ ≤ ρ` with `0 ≤ ρ < 1`, then `Forgets (fun τ => ∑ₖ P k (μ k)^τ)`.
The squared norm is dominated by `(∑ₖ ‖P k‖)² · (ρ²)^τ`, a geometric series in `ρ² < 1`, so the
partial sums converge; dividing a convergent sequence by `N → ∞` sends it to `0`.

DERIVED: `0` is the lower bound on `ρ` and the limit point in `Forgets`. `1` is the strict upper
bound on `ρ`; the proof squares it to `ρ² < 1`, which is the same bound applied to the square
`Forgets` averages. -/
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

/-- From a margin `0 ≤ ρ < 1` on the modes, the three conclusions at once: `‖C τ‖ → 0`, summability
of `τ ↦ ‖C τ‖`, and `Forgets C`. The conjunction of `Aperture.finite_flow_decays`, `flow_summable`
and `forgets_of_margin` at the same hypotheses.

DERIVED: `0` is the lower bound on `ρ` and the limit point of the first conjunct; `1` is the strict
upper bound on `ρ`. All are the three components'. -/
theorem bridge_forward (s : Finset ι) (P μ : ι → ℂ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hμ : ∀ k ∈ s, ‖μ k‖ ≤ ρ) :
    Tendsto (fun τ => ‖∑ k ∈ s, P k * (μ k) ^ τ‖) atTop (𝓝 0) ∧
      Summable (fun τ => ‖∑ k ∈ s, P k * (μ k) ^ τ‖) ∧
      Forgets (fun τ => ∑ k ∈ s, P k * (μ k) ^ τ) :=
  ⟨finite_flow_decays s P μ ρ hρ0 hρ1 hμ, flow_summable s P μ ρ hρ0 hρ1 hμ,
   forgets_of_margin s P μ ρ hρ0 hρ1 hμ⟩

/-- For `‖μ‖ = 1` and `P ≠ 0`, `¬ Forgets (fun τ => P * μ ^ τ)`. Every term has
`‖P μ^τ‖² = ‖P‖²`, so the Cesàro mean is the constant `‖P‖²`; uniqueness of limits would force
`‖P‖² = 0`, contradicting `hP`.

A single mode, not a sum: `forgets_forces_zero_net_weight` is the general statement, of which this is
the one-mode case.

DERIVED: `1` is the modulus `μ` is required to have — the unit circle, where the powers neither grow
nor decay. `0` is the value `P` is required to differ from, without which the constant mean would be
`0` and `Forgets` would hold. -/
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


/-! ## The converse

`persistent_not_forgets` refutes (i) for one mode of unit modulus. The general converse is
`forgets_forces_zero_net_weight`: (i) forces every value of unit modulus to carry zero net weight, so
modes may sit on the unit circle only in cancelling combinations.

The route extracts the weight at a single `ζ` by averaging `C` against `ζ^{-τ}` and bounds that
average by Cauchy–Schwarz against the quantity (i) sends to zero:

    ‖(1/N) ∑_{τ<N} C τ · ζ^{-τ}‖²  ≤  (1/N) ∑_{τ<N} ‖C τ‖²  →  0,

while the left-hand side converges to the net weight at `ζ`. No Cesàro limit of `‖C‖²` is computed.

`ζ⁻¹` is used rather than the conjugate throughout. On the unit circle they agree, and the inverse
keeps every step in field algebra: `μ · ζ⁻¹ = 1 ↔ μ = ζ` needs only `ζ ≠ 0`.
-/

/-- For `‖z‖ ≤ 1` with `z ≠ 1`, the Cesàro average `(∑_{τ<N} z^τ)/N` converges to `0`. `geom_sum_eq`
puts the partial sum at `(z^N − 1)/(z − 1)`, whose norm is at most `2/‖z − 1‖` because
`‖z^N‖ ≤ 1`; dividing a bounded quantity by `N → ∞` sends it to zero.

`z ≠ 1` is essential: at `z = 1` the partial sum is `N` and the average is the constant `1`.

DERIVED: `1` is the upper bound on `‖z‖`, the value `z` is required to differ from, and the unit in
`z - 1`; the three are the same number, and it is the only point of the closed disc where the
conclusion fails. `0` is the limit point. The bound `2` appears in the proof, as
`‖z^N‖ + ‖1‖ ≤ 1 + 1` by the triangle inequality, and not in the statement. -/
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

/-- For `ζ ≠ 0`, `μ * ζ⁻¹ = 1 ↔ μ = ζ`. Field algebra in both directions; no conjugation and no
condition on `‖ζ‖`.

DERIVED: `0` is the value `ζ` is required to differ from, which is what makes `ζ⁻¹` a genuine
inverse; `1` is the product's value, the multiplicative identity of `ℂ`. -/
theorem mul_inv_eq_one_iff_eq {μ ζ : ℂ} (hζ : ζ ≠ 0) : μ * ζ⁻¹ = 1 ↔ μ = ζ := by
  constructor
  · intro h
    field_simp at h
    exact h
  · rintro rfl
    exact mul_inv_cancel₀ hζ

#print axioms mul_inv_eq_one_iff_eq

open scoped Classical in
/-- For modes inside the closed unit disc and `‖ζ‖ = 1`,

    (1/N) ∑_{τ<N} (∑ₖ P k (μ k)^τ) · (ζ⁻¹)^τ  →  ∑_{k ∈ s, μ k = ζ} P k.

Swapping the two sums turns each term into `P k · (μ k ζ⁻¹)^τ`. A mode at `ζ` has
`μ k ζ⁻¹ = 1` (`mul_inv_eq_one_iff_eq`) and contributes `P k` at every `N`; a mode off `ζ` has
`‖μ k ζ⁻¹‖ ≤ 1` and `μ k ζ⁻¹ ≠ 1`, so `cesaro_geom_tendsto_zero` sends its contribution to `0`.

The limit is the net weight at `ζ`, a sum over the fibre, so cancelling modes contribute nothing.

DERIVED: `1` is the upper bound on each `‖μ k‖`, the modulus `ζ` is required to have, and the value
`μ k ζ⁻¹` takes exactly at the modes sitting at `ζ`; the second is what makes `‖ζ⁻¹‖ = 1` and hence
keeps `‖μ k ζ⁻¹‖ ≤ 1`. -/
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

/-- For any `C`, `w : ℕ → ℂ` with `‖w τ‖ ≤ 1` at every `τ`, and any `N`,

    ‖(∑_{τ<N} C τ · w τ)/N‖²  ≤  (∑_{τ<N} ‖C τ‖²)/N.

The triangle inequality drops `w`, and `sq_sum_le_card_mul_sum_sq` — Cauchy–Schwarz against the
constant one — supplies `(∑‖C τ‖)² ≤ N · ∑‖C τ‖²`. The case `N = 0` is closed by `simp`, both sides
being `0`.

`C` and `w` are arbitrary; no exponential-sum structure is used.

DERIVED: `1` is the bound on each `‖w τ‖`, which is what lets `w` be dropped. The two exponents `2`
are the squares Cauchy–Schwarz relates, and the `N` dividing both sides is the range's cardinality,
supplied by `sq_sum_le_card_mul_sum_sq`. -/
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
/-- For modes inside the closed unit disc, `‖ζ‖ = 1`, and `Forgets (fun τ => ∑ₖ P k (μ k)^τ)`, the
weights at `ζ` sum to zero: `∑_{k ∈ s, μ k = ζ} P k = 0`.

`cesaro_extract` makes the squared norm of the averaged sequence converge to `‖L‖²`, where `L` is
that sum; `cesaro_norm_sq_le` at `w τ = (ζ⁻¹)^τ` bounds it termwise by the Cesàro mean of `‖C‖²`,
which the hypothesis sends to `0`. Comparing the two limits gives `‖L‖² ≤ 0`.

The conclusion is about the fibre sum, not about individual weights: a mode of unit modulus is
permitted when another cancels it.

DERIVED: `1` is the upper bound on each `‖μ k‖` and the modulus `ζ` is required to have; `0` is the
value the fibre sum is shown to take, and the limit point inside `Forgets`. -/
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


/-! ## Closing the cycle

`forgets_forces_zero_net_weight` says the weight at a unit-modulus value cancels. Ruling out the
cancellation takes two hypotheses: the modes are distinct (`hinj`), so each value is carried by at
most one of them, and the weights are nonzero (`hP`), so that one cannot cancel against itself.

Both are conditions on the presentation rather than on the sum. Any finite exponential sum can be put
in this form by collecting equal modes and discarding zero weights, which
`decay_iff_effective_margin` does; here they are hypotheses.
-/

open scoped Classical in
/-- Under `Forgets`, distinct modes (`hinj`) and nonzero weights (`hP`), every mode of `s` satisfies
`‖μ k₀‖ < 1`.

If `‖μ k₀‖ = 1` then `forgets_forces_zero_net_weight` applies at `ζ = μ k₀`; distinctness makes the
fibre the singleton `{k₀}`, so the net weight is `P k₀`, which `hP` says is nonzero.

DERIVED: `1` is the upper bound each `‖μ k‖` is assumed to satisfy and the strict bound concluded —
the boundary case `‖μ k₀‖ = 1` is exactly what the two presentation hypotheses exclude. `0` is the
value each weight is required to differ from. -/
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

/-- Under the same hypotheses, there is a `ρ` with `0 ≤ ρ < 1` and `‖μ k‖ ≤ ρ` at every `k ∈ s`. The
witness is `s.sup' hne (fun k => ‖μ k‖)`; finitely many moduli each below `1`, by
`norm_lt_one_of_forgets`, have a maximum below `1`. For empty `s` the witness is `0` and the
universal condition is vacuous.

Finiteness of `s` is what makes the supremum attained and therefore strictly below `1`; an infinite
family of moduli each below `1` need have no such margin.

DERIVED: `1` is the upper bound each `‖μ k‖` is assumed to satisfy and the strict upper bound
concluded of `ρ`. `0` is the value each weight is required to differ from, the lower bound asserted
of `ρ`, and the witness taken when `s` is empty; that last choice is arbitrary among nonnegative
reals below `1`, the condition on it being vacuous. -/
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

/-- For a finite exponential sum with modes in the closed unit disc, distinct, and with nonzero
weights: `Forgets C ↔ ∃ ρ, 0 ≤ ρ < 1 ∧ ∀ k ∈ s, ‖μ k‖ ≤ ρ`. `margin_of_forgets` one way,
`forgets_of_margin` the other.

The two presentation hypotheses are used only in the forward direction; `forgets_of_margin` needs
neither.

DERIVED: `1` is the upper bound each `‖μ k‖` is assumed to satisfy and the strict upper bound on `ρ`.
`0` is the value each weight is required to differ from and the lower bound on `ρ`. -/
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

/-- From `Forgets` and the two presentation hypotheses: `‖C τ‖ → 0`, summability of `τ ↦ ‖C τ‖`, and
the margin. `margin_of_forgets` produces the margin, then `Aperture.finite_flow_decays` and
`flow_summable` at it.

DERIVED: `1` is the upper bound each `‖μ k‖` is assumed to satisfy and the strict upper bound on `ρ`.
`0` is the value each weight is required to differ from, the limit point of the first conjunct, and
the lower bound on `ρ`. -/
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


/-! ## The remaining arrow

`forgets_of_decay` closes the cycle at the last condition: (ii) ⟹ (i), because the Cesàro mean of a
null sequence is null. With `margin_of_forgets` the three conditions (i), (ii), (iii) are then
equivalent for a finite exponential sum with distinct modes and nonzero weights
(`decay_iff_forgets`, `decay_iff_margin`).

`Complete.ym_mass_gap_of_substrate`'s first conjunct has the form of (ii) at
`(ymModelAt N).s β`, so `decay_iff_margin` would upgrade it to a margin — under the two presentation
hypotheses, which nothing in the tree establishes for `ymModelAt`.
-/

/-- `Tendsto (fun τ => ‖C τ‖) atTop (𝓝 0) → Forgets C`, for an arbitrary `C : ℕ → ℂ`. Squaring
preserves the limit, and `Filter.Tendsto.cesaro` averages it; the `congr` step reconciles `cesaro`'s
`n⁻¹ * ∑` with `Forgets`'s `∑ / n`.

No structure on `C` is used: no exponential-sum form, no finiteness, no hypothesis on any mode.

DERIVED: `0` is the limit point, in the hypothesis and inside `Forgets`; the exponent `2` is
`Forgets`'s own square. -/
theorem forgets_of_decay {C : ℕ → ℂ} (h : Tendsto (fun τ => ‖C τ‖) atTop (𝓝 0)) :
    Forgets C := by
  have hsq : Tendsto (fun τ => ‖C τ‖ ^ 2) atTop (𝓝 0) := by
    simpa using h.pow 2
  -- `cesaro` produces `n⁻¹ * ∑`; `Forgets` is written `∑ / n`.
  exact hsq.cesaro.congr (fun n => by ring)

#print axioms forgets_of_decay

/-- For a finite exponential sum with modes in the closed unit disc, distinct, and with nonzero
weights: `‖C τ‖ → 0 ↔ Forgets C`. `forgets_of_decay` one way — which holds for any `C` — and
`margin_of_forgets` followed by `Aperture.finite_flow_decays` the other.

The three hypotheses are used only in the reverse direction.

DERIVED: `1` is the upper bound each `‖μ k‖` is assumed to satisfy; `0` is the value each weight is
required to differ from and the limit point on the left. -/
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

/-- Under the same hypotheses, `‖C τ‖ → 0 ↔ ∃ ρ, 0 ≤ ρ < 1 ∧ ∀ k ∈ s, ‖μ k‖ ≤ ρ`.
`decay_iff_forgets` composed with `forgets_iff_margin`.

`Complete.ym_mass_gap_of_substrate`'s first conjunct has the form of the left-hand side; applying
this to it requires the two presentation hypotheses, which are not discharged anywhere in this
module.

DERIVED: `1` is the upper bound each `‖μ k‖` is assumed to satisfy and the strict upper bound on `ρ`;
`0` is the value each weight is required to differ from, the limit point on the left, and the lower
bound on `ρ`. -/
theorem decay_iff_margin (s : Finset ι) (P μ : ι → ℂ)
    (hμ1 : ∀ k ∈ s, ‖μ k‖ ≤ 1)
    (hinj : ∀ k ∈ s, ∀ l ∈ s, μ k = μ l → k = l)
    (hP : ∀ k ∈ s, P k ≠ 0) :
    Tendsto (fun τ => ‖∑ k ∈ s, P k * (μ k) ^ τ‖) atTop (𝓝 0)
      ↔ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ k ∈ s, ‖μ k‖ ≤ ρ :=
  (decay_iff_forgets s P μ hμ1 hinj hP).trans (forgets_iff_margin s P μ hμ1 hinj hP)

#print axioms decay_iff_margin

/-- From `‖C τ‖ → 0` and the two presentation hypotheses: summability of `τ ↦ ‖C τ‖`, `Forgets C`,
and the margin. `decay_iff_margin` produces the margin, then `flow_summable` at it and
`forgets_of_decay` directly.

DERIVED: `1` is the upper bound each `‖μ k‖` is assumed to satisfy and the strict upper bound on `ρ`;
`0` is the value each weight is required to differ from, the limit point in the hypothesis, and the
lower bound on `ρ`. -/
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


/-! ## Removing the presentation hypotheses

`decay_iff_margin` assumes the modes distinct and the weights nonzero. Those are conditions on how
the sum is written, and any finite exponential sum can be rewritten to satisfy them: collect the
weights sharing a mode (`collect_modes`), then drop the values whose collected weight is zero. The
sum is unchanged.

The conclusion changes with the rewriting. After collecting, the margin is about the values carrying
nonzero collected weight, not about the written `μ k`:
`cancelling_modes_decay_on_the_circle` has `C` identically zero while both written modes have unit
modulus, so a margin over the written modes would be false there.

`decay_iff_effective_margin` is the form with no hypothesis on the presentation.
-/

open scoped Classical in
/-- The total weight the presentation places at a value `ζ`: `∑_{k ∈ s, μ k = ζ} P k`. Zero when no
mode sits at `ζ`, and possibly zero when several cancel.

DERIVED: no numeral. `s`, `P`, `μ` and `ζ` are the caller's. -/
noncomputable def collectedWeight (s : Finset ι) (P μ : ι → ℂ) (ζ : ℂ) : ℂ :=
  ∑ k ∈ s.filter (fun k => μ k = ζ), P k

open scoped Classical in
/-- `∑_{k ∈ s} P k (μ k)^τ = ∑_{ζ ∈ s.image μ} collectedWeight s P μ ζ · ζ^τ`, at every `τ`.
`Finset.sum_fiberwise_of_maps_to` over the image, with `μ k` rewritten to `ζ` inside each fibre
because membership in the fibre says exactly that.

An identity, so the sum is unchanged by the rewriting; the index set changes from `s` to the image of
`μ`.

DERIVED: no numeral. -/
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

/-- For a `Finset ℂ`: `(∃ ρ, 0 ≤ ρ < 1 ∧ ∀ ζ ∈ T, ‖ζ‖ ≤ ρ) ↔ ∀ ζ ∈ T, ‖ζ‖ < 1`. Forward by
transitivity; backward by `Finset.sup'` on a nonempty `T`, with `0` as the witness when `T` is
empty.

Finiteness is what makes the two equivalent; for an infinite set of complex numbers the right side
does not give the left.

DERIVED: `1` is the strict upper bound on each modulus and on `ρ`; `0` is the lower bound on `ρ` and
the witness taken when `T` is empty, where the condition on it is vacuous. -/
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
/-- For modes in the closed unit disc and no other hypothesis:

    ‖∑ₖ P k (μ k)^τ‖ → 0  ↔  ∀ ζ ∈ s.image μ, collectedWeight s P μ ζ ≠ 0 → ‖ζ‖ < 1.

`collect_modes` rewrites the sum over the filtered image `T` of values with nonzero collected weight,
where the index is `id` and so distinct by construction and the weights nonzero by the filter, so
`decay_iff_margin` applies; `margin_iff_all_lt_one` converts the margin into the pointwise form.

No distinctness and no nonvanishing is assumed of the written presentation. The conclusion is about
the values carrying nonzero collected weight, which is what it must be:
`cancelling_modes_decay_on_the_circle` refutes the same statement about the written modes.

DERIVED: `1` is the upper bound each `‖μ k‖` is assumed to satisfy and the strict bound on each
effective mode; `0` is the limit point on the left and the value a collected weight must differ from
for its value to be constrained. -/
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

/-- At `P = ![1, -1]` and `μ = ![1, 1]` over `Fin 2`, the sum is `0` at every `τ`, so
`‖∑ₖ P k (μ k)^τ‖ → 0`.

Both written modes have modulus `1`, so a margin over the written modes would be false here. This is
why `decay_iff_effective_margin` is stated about collected weights, and why `decay_iff_margin` needs
its nonvanishing hypothesis.

DERIVED: `2` in `Fin 2` is the number of modes, the fewest that can cancel. `1` and `-1` are the two
weights, chosen to sum to zero, and `1` is the shared mode, chosen on the unit circle so that the
powers neither grow nor decay. `0` is the limit point. Nothing is a magnitude. -/
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
