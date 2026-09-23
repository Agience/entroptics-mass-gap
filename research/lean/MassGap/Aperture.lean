import Mathlib
import MassGap.ReachFreeze
import MassGap.Bounds

/-!
# MassGap.Aperture — decay of a finite exponential sum, and three companion facts

The object throughout is a finite sum `∑ k ∈ s, P k · (μ k)^τ` with `s : Finset ι` and
`P μ : ι → ℂ`. Read as an autocorrelation at Euclidean time `τ`, `s` indexes the modes visible through
an aperture and `μ k` their per-step eigenvalues; the statements themselves impose nothing but
finiteness of `s`.

* `finite_sum_margin_bound` — the sum is at most `(∑ ‖P k‖) · ρ^τ` whenever every `‖μ k‖ ≤ ρ`.
* `finite_flow_decays` and `gap_at_finite_F` — with `ρ < 1` (equivalently `ρ = e^{-κ}`, `κ > 0`, via
  `margin_iff_rate_pos`) the norm of the sum tends to `0`. Neither statement carries a rate.
* `UniformSpectralMargin`, `uniform_margin_of_intensive_radius`, `gap_uniform_in_F` — a single margin
  serving every dimension `F`. Note the shape of `gap_uniform_in_F`'s conclusion: the bound variable
  `κ` occurs only in `0 < κ`, not in the `Tendsto` clause after the `∧`.
* `uniform_margin_solvable` — `fun _ => Real.tanh b` satisfies `UniformSpectralMargin` for `0 < b`,
  using `ising_transfer` from `MassGap.Bounds`.
* `no_interior_transition` — a continuous strictly positive function on a compact interval has a
  positive lower bound, by `IsCompact.exists_isMinOn`.
* `gap_refinement_invariant` — the real identity `-(s/δ) · log (m^{1/s}) = -(1/δ) · log m`.
* `gap_of_confinement` — `gap_at_finite_F` specialised at `κ = κ₀ - μ`, given `μ < κ₀`.
-/

namespace MassGap

/-- If `‖μ k‖ ≤ ρ` for every `k ∈ s`, then `‖∑ k ∈ s, P k * (μ k)^τ‖ ≤ (∑ k ∈ s, ‖P k‖) * ρ^τ`.
Triangle inequality, then `norm_mul` and `norm_pow`, then `gcongr` on each term. Holds for every `τ`
and every `ρ` satisfying the hypothesis; `s` may be empty, in which case both sides are `0`.

DERIVED: no numeral. -/
theorem finite_sum_margin_bound {ι : Type*} (s : Finset ι) (P μ : ι → ℂ)
    (ρ : ℝ) (hμ : ∀ k ∈ s, ‖μ k‖ ≤ ρ) (τ : ℕ) :
    ‖∑ k ∈ s, P k * (μ k) ^ τ‖ ≤ (∑ k ∈ s, ‖P k‖) * ρ ^ τ := by
  calc ‖∑ k ∈ s, P k * (μ k) ^ τ‖
      ≤ ∑ k ∈ s, ‖P k * (μ k) ^ τ‖ := norm_sum_le _ _
    _ = ∑ k ∈ s, ‖P k‖ * ‖μ k‖ ^ τ := by
          refine Finset.sum_congr rfl (fun k _ => ?_); rw [norm_mul, norm_pow]
    _ ≤ ∑ k ∈ s, ‖P k‖ * ρ ^ τ := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          gcongr
          exact hμ k hk
    _ = (∑ k ∈ s, ‖P k‖) * ρ ^ τ := by rw [Finset.sum_mul]

/-- With `0 ≤ ρ < 1` and every `‖μ k‖ ≤ ρ` on `s`, the norm of the finite sum tends to `0` as
`τ → ∞`. `finite_sum_margin_bound` gives the geometric envelope and `excess_tendsto_zero_of_geom`
(from `MassGap.ReachFreeze`) drives it to zero. The conclusion is convergence to `0`, with no rate
attached.

DERIVED: `0` in `hρ0` is the floor `ρ^τ` needs to stay nonnegative under the envelope; `1` in `hρ1` is
the strict margin that makes `ρ^τ` vanish; `0` in the conclusion is that limit. -/
theorem finite_flow_decays {ι : Type*} (s : Finset ι) (P μ : ι → ℂ)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hμ : ∀ k ∈ s, ‖μ k‖ ≤ ρ) :
    Filter.Tendsto (fun τ => ‖∑ k ∈ s, P k * (μ k) ^ τ‖) Filter.atTop (nhds 0) :=
  excess_tendsto_zero_of_geom hρ0 hρ1 (fun _ => norm_nonneg _)
    (fun τ => finite_sum_margin_bound s P μ ρ hμ τ)

/-- `Real.exp (-κ) < 1 ↔ 0 < κ`. Both directions, by rewriting `1` as `exp 0` and using strict
monotonicity of `exp`. This is what lets a margin `ρ` and a rate `κ` be used interchangeably below.

DERIVED: `1` is `exp 0`, the value the margin must sit strictly below; `0` is the matching threshold
on the rate. -/
theorem margin_iff_rate_pos {κ : ℝ} : Real.exp (-κ) < 1 ↔ 0 < κ := by
  rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero], Real.exp_lt_exp]
  constructor <;> intro h <;> linarith

/-- `finite_flow_decays` with the margin written as `exp (-κ)`: for `0 < κ` and every `‖μ k‖ ≤ exp (-κ)`
on `s`, the norm of the finite sum tends to `0`. The margin hypotheses are supplied by
`Real.exp_nonneg` and `margin_iff_rate_pos`. The conclusion states convergence only; `κ` does not
appear in it, so no decay rate is concluded.

DERIVED: `0` in `hκ` is the threshold `margin_iff_rate_pos` converts into `exp (-κ) < 1`; `0` in the
conclusion is the limit. -/
theorem gap_at_finite_F {ι : Type*} (s : Finset ι) (P μ : ι → ℂ) {κ : ℝ}
    (hκ : 0 < κ) (hμ : ∀ k ∈ s, ‖μ k‖ ≤ Real.exp (-κ)) :
    Filter.Tendsto (fun τ => ‖∑ k ∈ s, P k * (μ k) ^ τ‖) Filter.atTop (nhds 0) :=
  finite_flow_decays s P μ (Real.exp (-κ)) (Real.exp_nonneg _) (margin_iff_rate_pos.mpr hκ) hμ

/-! ## Closing `F → ∞`: the intensive spectral radius

`gap_at_finite_F` gives a gap at each fixed `F`, but the rate could in principle degrade as modes are
added. It does not degrade when the dominant magnitude is **intensive**: one `r < 1`, independent of
`F`, bounding `‖μ₁(F)‖` at every dimension. The counting floor `κ₀ = ¼ln3` (`Floor.lean`) is
dimension-free, so it does not dilute as modes are added; at the solvable point the radius is
`‖μ₁‖ = tanh b < 1`, set by the local transfer, not the size (`ising_transfer`). -/

/-- The predicate: `∃ κ, 0 < κ ∧ ∀ F, μ₁ F ≤ exp (-κ)`. One rate, chosen before `F`, bounding the
sequence `μ₁ : ℕ → ℝ` at every index. `μ₁ F` is a real, not a norm, so the predicate constrains it
only from above.

DERIVED: `0` is the positivity the rate must have for `exp (-κ)` to be a strict margin
(`margin_iff_rate_pos`). -/
def UniformSpectralMargin (μ₁ : ℕ → ℝ) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ F, μ₁ F ≤ Real.exp (-κ)

/-- If `0 < r < 1` and `μ₁ F ≤ r` for every `F`, then `UniformSpectralMargin μ₁`, with witness
`κ = -log r`. `Real.log_neg` makes that positive and `Real.exp_log` turns `exp (-(-log r))` back into
`r`. The witness is exhibited, so the rate is determined by `r` rather than merely asserted to exist.

DERIVED: `0` in `hr0` is what `Real.log` needs to be inverted by `exp`; `1` in `hr1` is what makes
`log r` negative, hence `κ` positive. -/
theorem uniform_margin_of_intensive_radius
    (μ₁ : ℕ → ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hbound : ∀ F, μ₁ F ≤ r) :
    UniformSpectralMargin μ₁ := by
  refine ⟨-Real.log r, ?_, fun F => ?_⟩
  · have hlog : Real.log r < 0 := Real.log_neg hr0 hr1
    linarith
  · rw [neg_neg, Real.exp_log hr0]; exact hbound F

/-- Given `UniformSpectralMargin μ₁` and `‖μ F k‖ ≤ μ₁ F` for every `k ∈ s F`, produces
`∃ κ, 0 < κ ∧ ∀ F, Tendsto (fun τ => ‖∑ k ∈ s F, P F k * (μ F k)^τ‖) atTop (nhds 0)`: at every `F` the
sum's norm tends to `0`. The existentially bound `κ` occurs only in the conjunct `0 < κ`; it does not
appear in the `Tendsto` clause, so the statement does not assert a rate common to all `F`, only that
each `F` decays and that some positive `κ` exists.

DERIVED: `0` in `0 < κ` is the rate threshold carried out of `UniformSpectralMargin`; `0` in `nhds 0`
is the limit each sum's norm reaches. -/
theorem gap_uniform_in_F {ι : Type*}
    (s : ℕ → Finset ι) (P μ : ℕ → ι → ℂ) (μ₁ : ℕ → ℝ)
    (hmargin : UniformSpectralMargin μ₁)
    (hdom : ∀ F, ∀ k ∈ s F, ‖μ F k‖ ≤ μ₁ F) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ F,
      Filter.Tendsto (fun τ => ‖∑ k ∈ s F, P F k * (μ F k) ^ τ‖) Filter.atTop (nhds 0) := by
  obtain ⟨κ, hκ, hbnd⟩ := hmargin
  exact ⟨κ, hκ, fun F => gap_at_finite_F (s F) (P F) (μ F) hκ
    (fun k hk => le_trans (hdom F k hk) (hbnd F))⟩

/-- The constant sequence `fun _ => Real.tanh b` satisfies `UniformSpectralMargin` for `0 < b`.
`uniform_margin_of_intensive_radius` is applied with `r = tanh b`: positivity comes from
`sinh b > 0` for `b > 0`, and `tanh b < 1` from `ising_transfer` in `MassGap.Bounds`. The sequence is
constant in `F`, so the uniformity is immediate.

DERIVED: `0` in `hb` is what makes `exp (-b) < exp b`, hence `sinh b` and `tanh b` positive; it is the
only use of the hypothesis. -/
theorem uniform_margin_solvable (b : ℝ) (hb : 0 < b) :
    UniformSpectralMargin (fun _ => Real.tanh b) := by
  apply uniform_margin_of_intensive_radius (r := Real.tanh b)
  · rw [Real.tanh_eq_sinh_div_cosh]
    apply div_pos _ (Real.cosh_pos b)
    rw [Real.sinh_eq]
    have h1 : Real.exp (-b) < Real.exp b := Real.exp_lt_exp.mpr (by linarith)
    linarith [Real.exp_pos b, Real.exp_pos (-b)]
  · exact ising_transfer b
  · intro _; exact le_refl _

/-! ## The crossover: no interior transition (compactness)

The gap `Δ(β)` is positive at every coupling (the finite compact configuration screen has a spectral
gap at each coupling: a smooth strictly-positive Gibbs measure on a compact connected manifold gives
`Δ > 0`) and continuous in the coupling. On a compact coupling interval a continuous positive function
attains a positive minimum, so the gap is bounded below by a positive constant across the whole
crossover: it cannot close in the interior. -/

/-- A function `Δ` continuous on `Set.Icc a b` (with `a ≤ b`) and strictly positive on it has a
positive uniform lower bound there: `∃ c, 0 < c ∧ ∀ β ∈ Icc a b, c ≤ Δ β`. The witness is `Δ β₀` at the
minimiser given by `IsCompact.exists_isMinOn`. Stated for a compact interval; `hab` is what makes it
nonempty, and nothing is claimed outside `Icc a b`.

DERIVED: the `0`s are the pointwise positivity assumed on the interval and the positivity of the
uniform bound that follows from it, the latter being the value of `Δ` at the minimiser. -/
theorem no_interior_transition {Δ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn Δ (Set.Icc a b)) (hpos : ∀ β ∈ Set.Icc a b, 0 < Δ β) :
    ∃ c : ℝ, 0 < c ∧ ∀ β ∈ Set.Icc a b, c ≤ Δ β := by
  obtain ⟨β₀, hβ₀, hmin⟩ :=
    IsCompact.exists_isMinOn isCompact_Icc (Set.nonempty_Icc.mpr hab) hcont
  exact ⟨Δ β₀, hpos β₀ hβ₀, fun β hβ => isMinOn_iff.mp hmin β hβ⟩

/-! ## Refinement invariance of `-(1/δ) log m`

Refining by a factor `s` sends the step `δ ↦ δ/s` and the per-step eigenvalue `m ↦ m^{1/s}`. The
identity below records that the combination `-(1/δ) log m` is unchanged by that substitution. It is an
identity between real expressions; no operator or limit appears. -/
/-- `-(s/δ) * log (m ^ (1/s)) = -(1/δ) * log m` for positive `δ`, `s` and `m`. `Real.log_rpow` needs
`0 < m` to pull the exponent out, and `field_simp` clears the denominators `δ` and `s`, which `hδ` and
`hs` keep nonzero. An equality of real expressions, stated for a single refinement factor `s`.

DERIVED: the three `0`s are the positivity of `δ`, `s` and `m`; `1` in `m ^ (1/s)` is the numerator of
the refinement exponent, and `1` in `1/δ` is the single step the rate is taken per. -/
theorem gap_refinement_invariant {δ m s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (hm : 0 < m) :
    -(s / δ) * Real.log (m ^ ((1 : ℝ) / s)) = -(1 / δ) * Real.log m := by
  rw [Real.log_rpow hm]
  field_simp

/-- `gap_at_finite_F` specialised at `κ = κ₀ - μ`. Given two reals with `μ < κ₀`, and every mode on
the finite index set `s` bounded by `‖m k‖ ≤ exp (-(κ₀ - μ))`, the norm of `∑ k ∈ s, P k * (m k)^τ`
tends to `0` as `τ → ∞`. `κ₀` and `μ` are arbitrary reals; no counting floor or tension is defined
here, and the conclusion is convergence to zero without a stated rate.

DERIVED: `0` is the limit the sum's norm reaches; the rate `κ₀ - μ` handed to `gap_at_finite_F` is
positive by `hconf`, which is the numeral-free form of that same threshold. -/
theorem gap_of_confinement {ι : Type*} (s : Finset ι) (P m : ι → ℂ) (κ₀ μ : ℝ)
    (hconf : μ < κ₀)
    (hread : ∀ k ∈ s, ‖m k‖ ≤ Real.exp (-(κ₀ - μ))) :
    Filter.Tendsto (fun τ => ‖∑ k ∈ s, P k * (m k) ^ τ‖) Filter.atTop (nhds 0) :=
  gap_at_finite_F s P m (κ := κ₀ - μ) (by linarith) hread

end MassGap
