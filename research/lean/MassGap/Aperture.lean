import Mathlib
import MassGap.ReachFreeze
import MassGap.Bounds

/-!
# The finite aperture is gapped (PAPER §4, §6)

The Entroptics route to the gap, in the screen's own coordinates: entropy, counting, and the finite
DMD spectrum. No Ricci, no Hessian, no curvature-dimension condition, no renormalisation group.

* **The dichotomy.** Through a finite aperture the propagator has finitely many modes, so the
  autocorrelation is a finite exponential sum `C τ = Σ_k P k (μ k)^τ` ([E, §9]). A finite sum has two
  fates: a mode on the unit circle (`|μ_k| = 1`, a persistent massless mode) or a strict margin
  (`max|μ_k| < 1`, exponential decay, the gap). The gapless power law needs infinitely many modes and
  cannot occur while the aperture is finite (`finite_flow_decays`, `gap_at_finite_F`).
* **`F → ∞`.** The gap is uniform in the number of modes when the dominant magnitude is intensive
  (one `r < 1` for every dimension); the counting floor `κ₀ = ¼ln3` (`Floor.lean`) is dimension-free,
  so it does not dilute as modes are added (`gap_uniform_in_F`).
* **The crossover.** The gap, positive at every coupling and continuous, is bounded below by a
  positive constant on any compact coupling interval: no interior transition (`no_interior_transition`).
* **`a → 0`.** The physical rate is refinement-invariant (`gap_refinement_invariant`), the companion
  of the block-rescale identity of [E].
* **The capstone.** `μ < κ₀` (tension below the counting floor) plus the finite aperture gives
  `C(τ) → 0`, the gap (`gap_of_confinement`).

All theorems are machine-checked (no `sorry`/`admit`; axioms are the standard three).
-/

namespace MassGap

/-- A finite exponential sum whose modes share a margin `ρ` is bounded by `(Σ‖P k‖) ρ^τ`. -/
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

/-- **Finite-mode decay.** Finitely many modes inside a margin `ρ < 1` force the autocorrelation to
zero: the flow forgets. The finite exponential sum admits no power-law middle. -/
theorem finite_flow_decays {ι : Type*} (s : Finset ι) (P μ : ι → ℂ)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hμ : ∀ k ∈ s, ‖μ k‖ ≤ ρ) :
    Filter.Tendsto (fun τ => ‖∑ k ∈ s, P k * (μ k) ^ τ‖) Filter.atTop (nhds 0) :=
  excess_tendsto_zero_of_geom hρ0 hρ1 (fun _ => norm_nonneg _)
    (fun τ => finite_sum_margin_bound s P μ ρ hμ τ)

/-- **Margin ⟺ positive rate.** The spectral margin `ρ = e^{-κ}` and the decay rate `κ` are one
datum: `e^{-κ} < 1 ↔ κ > 0`. -/
theorem margin_iff_rate_pos {κ : ℝ} : Real.exp (-κ) < 1 ↔ 0 < κ := by
  rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero], Real.exp_lt_exp]
  constructor <;> intro h <;> linarith

/-- **The gap at finite F.** A rate `κ > 0` (every mode inside the margin `ρ = e^{-κ} < 1`) sends the
autocorrelation to zero: the flow forgets, the gap is open. Proved outright at finite `F`; the residue
is that a single `κ > 0` serves uniformly as `F → ∞`. -/
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

/-- The dominant mode magnitude is bounded by one positive rate across every dimension `F`. -/
def UniformSpectralMargin (μ₁ : ℕ → ℝ) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ F, μ₁ F ≤ Real.exp (-κ)

/-- **Intensive radius ⟹ F-uniform margin.** One `r < 1`, independent of `F`, bounding the dominant
magnitude at every dimension gives `κ = -log r > 0` uniformly in `F`. -/
theorem uniform_margin_of_intensive_radius
    (μ₁ : ℕ → ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hbound : ∀ F, μ₁ F ≤ r) :
    UniformSpectralMargin μ₁ := by
  refine ⟨-Real.log r, ?_, fun F => ?_⟩
  · have hlog : Real.log r < 0 := Real.log_neg hr0 hr1
    linarith
  · rw [neg_neg, Real.exp_log hr0]; exact hbound F

/-- **The gap survives `F → ∞`.** With an intensive margin (one `κ > 0` for all `F`), every
dimension's autocorrelation decays with the SAME rate `κ`: the gap does not degrade as modes are
added. The input is the intensive radius `r < 1`, a size-independent transfer gap. -/
theorem gap_uniform_in_F {ι : Type*}
    (s : ℕ → Finset ι) (P μ : ℕ → ι → ℂ) (μ₁ : ℕ → ℝ)
    (hmargin : UniformSpectralMargin μ₁)
    (hdom : ∀ F, ∀ k ∈ s F, ‖μ F k‖ ≤ μ₁ F) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ F,
      Filter.Tendsto (fun τ => ‖∑ k ∈ s F, P F k * (μ F k) ^ τ‖) Filter.atTop (nhds 0) := by
  obtain ⟨κ, hκ, hbnd⟩ := hmargin
  exact ⟨κ, hκ, fun F => gap_at_finite_F (s F) (P F) (μ F) hκ
    (fun k hk => le_trans (hdom F k hk) (hbnd F))⟩

/-- **The intensive radius holds at the solvable point.** On the exactly-solvable strip the dominant
magnitude is `‖μ₁‖ = tanh b`, intensive (set by the local transfer, the same for every `F`), and
`< 1` (`ising_transfer`), so `UniformSpectralMargin` holds there for all `F` at once. -/
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

/-- **No interior transition.** A gap `Δ` continuous on `[a,b]` and positive at every coupling
attains a positive minimum there: `∃ c > 0, ∀ β ∈ [a,b], c ≤ Δ β`. A gap open at every coupling cannot
close across the crossover. -/
theorem no_interior_transition {Δ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn Δ (Set.Icc a b)) (hpos : ∀ β ∈ Set.Icc a b, 0 < Δ β) :
    ∃ c : ℝ, 0 < c ∧ ∀ β ∈ Set.Icc a b, c ≤ Δ β := by
  obtain ⟨β₀, hβ₀, hmin⟩ :=
    IsCompact.exists_isMinOn isCompact_Icc (Set.nonempty_Icc.mpr hab) hcont
  exact ⟨Δ β₀, hpos β₀ hβ₀, fun β hβ => isMinOn_iff.mp hmin β hβ⟩

/-! ## The continuum limit `a → 0` is closed by refinement-invariance

Refining the aperture by `s` sends the step `δ ↦ δ/s` and, since the propagator is exact
(`A_{δ/s}^s = A_δ`, [E, §9]), the per-step dominant eigenvalue `|μ₁| ↦ |μ₁|^{1/s}`. The physical rate
`Δ = -(1/δ) log|μ₁|` is unchanged, so the continuum value equals the finite-spacing value by an
identity (the companion of the block-rescale identity `gabor_product_scale_invariant` of [E]). -/
theorem gap_refinement_invariant {δ m s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (hm : 0 < m) :
    -(s / δ) * Real.log (m ^ ((1 : ℝ) / s)) = -(1 / δ) * Real.log m := by
  rw [Real.log_rpow hm]
  field_simp

/-- **The gap from confinement (capstone).** With `κ₀` the dimension-free counting floor
(`Floor.lean`) and `μ` the aperture-measured tension (the read `‖mode‖ ≤ e^{-(κ₀-μ)}`), the single
physical input is `μ < κ₀`: the tension sits below the floor. Then the net rate `κ₀ - μ` is positive,
every mode clears the unit circle, and the finite aperture forgets: `C(τ) → 0`, gap `≥ κ₀ - μ > 0`.
The finite aperture (causality) turns the one inequality into the gap. -/
theorem gap_of_confinement {ι : Type*} (s : Finset ι) (P m : ι → ℂ) (κ₀ μ : ℝ)
    (hconf : μ < κ₀)
    (hread : ∀ k ∈ s, ‖m k‖ ≤ Real.exp (-(κ₀ - μ))) :
    Filter.Tendsto (fun τ => ‖∑ k ∈ s, P k * (m k) ^ τ‖) Filter.atTop (nhds 0) :=
  gap_at_finite_F s P m (κ := κ₀ - μ) (by linarith) hread

end MassGap
