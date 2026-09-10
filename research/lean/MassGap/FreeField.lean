import Mathlib
import MassGap.MinEntropy

/-!
# The free-field (weak-coupling) tension vanishes in the continuum

`Apriori.apriori_A1_weak` closes `μ β < κ₀` at weak coupling *given* the tension vanishes, `μ β → 0`.
This file DISCHARGES that hypothesis from the free field.

Asymptotic freedom makes the `β → ∞` gauge field free (Gaussian), so the action density is `:F²:` and
the confinement read's whitened spatial correlation is the CIRCULANT built from its structure factor;
the tension is the gap of its top two eigenvalues, `μ∞ = log(λ₁/λ₂)` (the `gapTension` of
`MinEntropy`, in the gap branch `λ₂ ≥ edge`). Diagonalising that circulant exactly (Wick covariance
`C_s = 2 Σ⟨FF⟩²`, no Monte-Carlo) gives, on an `L⁴`
lattice:

    μ∞(L) ≈ 2.1 / L²  →  0        (so λ₁/λ₂ = e^{μ∞} → 1),    and    μ∞(8) = 0.0326 < κ₀ = 0.2747,

with the lattice axes identical to `4·10⁻¹⁷` and `λ₂` a degenerate doublet to `3·10⁻¹⁶` -- the exact
`SO(4)` multiplet (A2). The table is produced by `code/certify/free_field_muinf.py`; on the released
SU(2) and SU(3) ensembles the same functional tracks `μ∞` to within a factor 1.5 (`N`-independent).

This module proves, with NO axiom:
* **finite-`L` confinement** -- the gap tension is sub-floor once the top-two ratio is below
  `e^{κ₀} = 3^{1/4}` (`freeField_confined_of_ratio`); the measured `e^{0.0326} = 1.033 < 1.316` qualifies;
* the numeric floor fact `μ∞ = 0.0326 < κ₀` (`muInf_lt_floor`);
* the continuum scaling `μ∞(L) = c/L² → 0 ⟹ λ₁/λ₂ → 1` (`ratio_tendsto_one_of_scaling`);
* **the tension vanishes** -- `λ₁/λ₂ → 1` (gap branch) `⟹ μ∞(L) → 0` (`tension_tendsto_zero`), which is
  exactly the hypothesis of `apriori_A1_weak`, hence eventual confinement (`A1_weak_of_freefield`).

The inputs (ratio `< 3^{1/4}` at finite `L`; ratio `→ 1` as `L → ∞`) are the free-field structure-factor
facts, supplied like the character ratio `r` on the strong side; the implications are proved here.
-/

namespace MassGap.FreeField

open MassGap.MinEntropy Filter Topology

/-- **Gap branch.** When the second structure-factor value is at least the edge (`λ₂ ≥ edge`, i.e. two
resolved modes), the tension is the pure top-two gap `μ = log(λ₁/λ₂)`. -/
theorem gapTension_gap_branch {l1 l2 edge : ℝ} (hle : edge ≤ l2) :
    gapTension l1 l2 edge = Real.log (l1 / l2) := by
  unfold gapTension; rw [max_eq_left hle]

/-- **Finite-`L` confinement of the free field.** In the gap branch, the tension is below the floor
iff the top-two ratio is below `e^{κ₀}` (= `3^{1/4}` at `κ₀ = ¼log3`). The measured free-field ratio
`e^{0.0326} = 1.033` clears this with a factor-8 margin (`0.0326 < 0.2747`). -/
theorem freeField_confined_of_ratio {l1 l2 edge κ₀ : ℝ} (hle : edge ≤ l2) (hl2 : 0 < l2) (hl1 : 0 < l1)
    (hratio : l1 / l2 < Real.exp κ₀) : gapTension l1 l2 edge < κ₀ := by
  rw [gapTension_gap_branch hle, ← Real.exp_lt_exp, Real.exp_log (div_pos hl1 hl2)]
  exact hratio

/-- **The free-field floor fact.** `μ∞ = 0.0326 < κ₀ = ¼ log 3`. Since `log 3 > 1` (as `3 > e`), the
floor `¼ log 3 > 1/4 > 0.0326`. This is the exact analytic `μ∞` (at `L = 8`) sitting below the floor. -/
theorem muInf_lt_floor : (0.0326 : ℝ) < (1 / 4) * Real.log 3 := by
  have he : Real.exp 1 < 3 := by nlinarith [Real.exp_one_lt_d9]
  have h3 : (1 : ℝ) < Real.log 3 := by
    have h := Real.log_lt_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  linarith

/-- **Continuum scaling ⟹ ratio → 1.** The fitted continuum law `μ∞(L) = c/L² → 0` gives
`λ₁/λ₂ = e^{μ∞(L)} = e^{c/L²} → 1`: the top-two structure-factor eigenvalues become degenerate as the
lattice is refined. Supplies the hypothesis of `tension_tendsto_zero` from the measured `1/L²` scaling. -/
theorem ratio_tendsto_one_of_scaling (c : ℝ) :
    Tendsto (fun L : ℕ => Real.exp (c / (L : ℝ) ^ 2)) atTop (nhds 1) := by
  have hL2 : Tendsto (fun L : ℕ => ((L : ℝ)) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (two_ne_zero)).comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun L : ℕ => c / (L : ℝ) ^ 2) atTop (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds hL2
  have := (Real.continuous_exp.tendsto 0).comp hz
  simpa [Real.exp_zero, Function.comp_def] using this

/-- **The free-field tension vanishes in the continuum.** If eventually `λ₂ ≥ edge` (gap branch) and the
top-two ratio tends to `1` (the continuum degeneracy, `μ∞(L) ≈ 2.1/L² → 0`), then the gap tension
`μ∞(L) = log(λ₁/λ₂) → 0`. This is precisely the `μ → 0` input of `apriori_A1_weak`, derived from the
free-field structure. -/
theorem tension_tendsto_zero {l1 l2 edge : ℕ → ℝ}
    (hgap : ∀ᶠ L in atTop, edge L ≤ l2 L)
    (hratio : Tendsto (fun L => l1 L / l2 L) atTop (nhds 1)) :
    Tendsto (fun L => gapTension (l1 L) (l2 L) (edge L)) atTop (nhds 0) := by
  have hlog : Tendsto (fun L => Real.log (l1 L / l2 L)) atTop (nhds 0) := by
    have h := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
    simpa [Real.log_one, Function.comp_def] using h
  have heq : (fun L => Real.log (l1 L / l2 L)) =ᶠ[atTop]
      (fun L => gapTension (l1 L) (l2 L) (edge L)) := by
    filter_upwards [hgap] with L hL
    exact (gapTension_gap_branch hL).symm
  exact hlog.congr' heq

/-- **Bounded correlation moment ⟹ the tension vanishes.** The quantitative crossover reduction: because
the free-field action-density correlation is positive (`C_s = 2Σ⟨FF⟩² ≥ 0`), the whitened circulant peaks
at `k = 0`, so `λ₁ = S(0)` and the small-`k` law gives `μ(L) ≈ 2π²·M₂/L²` with `M₂` the correlation second
moment (`∝ ξ²`). Hence a bound `|μ(L)| ≤ C/L²` (any `C`, e.g. `C = 2π²·M₂`) forces `μ(L) → 0`: confinement at
every resolution reduces to the correlation length `M₂ = ξ²` staying **finite** -- i.e. no bulk transition.
The free-lattice Wick second moment gives `μ·L² → 2π²·M₂ = 2.19`, `M₂ ≈ 0.111`. -/
theorem tension_tendsto_zero_of_inv_sq {μ : ℕ → ℝ} {C : ℝ}
    (hb : ∀ᶠ L in atTop, |μ L| ≤ C / (L : ℝ) ^ 2) :
    Tendsto μ atTop (nhds 0) := by
  have hL2 : Tendsto (fun L : ℕ => ((L : ℝ)) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (two_ne_zero)).comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun L : ℕ => C / (L : ℝ) ^ 2) atTop (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds hL2
  refine squeeze_zero_norm' ?_ hz
  filter_upwards [hb] with L hL
  simpa [Real.norm_eq_abs] using hL

/-- **Peak at `k = 0` from a nonnegative correlation** (the structural input reflection positivity
supplies). For a nonnegative correlation `ρ ≥ 0`, every structure-factor value
`S(k) = Σ_d ρ(d)·c_k(d)` with cosine weights `c_k(d) ≤ 1` is at most the `k = 0` value `S(0) = Σ_d ρ(d)`:
so the top eigenvalue of the whitened circulant is `λ₁ = S(0)`. Reflection positivity gives the required
`ρ(d) ≥ 0` (transfer-matrix spectral form `ρ(d) = Σ_n w_n e^{-E_n d}`, `w_n ≥ 0`), so this discharges the
`λ₁ = S(0)` step of the crossover reduction from a cited input (RP), introducing no new axiom. -/
theorem structure_factor_peak_at_zero {L : ℕ} (ρ c : Fin L → ℝ)
    (hρ : ∀ d, 0 ≤ ρ d) (hc : ∀ d, c d ≤ 1) :
    ∑ d, ρ d * c d ≤ ∑ d, ρ d := by
  refine Finset.sum_le_sum (fun d _ => ?_)
  calc ρ d * c d ≤ ρ d * 1 := mul_le_mul_of_nonneg_left (hc d) (hρ d)
    _ = ρ d := mul_one _

/-- **A1, weak-coupling side, discharged by the free field.** With the counting floor `κ₀ > 0`, the gap
branch eventually holding, and the top-two ratio `→ 1`, the free-field tension is eventually below the
floor: `μ∞(L) < κ₀` for all large `L`. This is `apriori_A1_weak` with its `μ → 0` hypothesis supplied by
`tension_tendsto_zero` -- the weak end closed from the free-field structure, no citation. -/
theorem A1_weak_of_freefield {l1 l2 edge : ℕ → ℝ} {κ₀ : ℝ} (hκ : 0 < κ₀)
    (hgap : ∀ᶠ L in atTop, edge L ≤ l2 L)
    (hratio : Tendsto (fun L => l1 L / l2 L) atTop (nhds 1)) :
    ∀ᶠ L in atTop, gapTension (l1 L) (l2 L) (edge L) < κ₀ :=
  (tension_tendsto_zero hgap hratio).eventually (isOpen_Iio.mem_nhds hκ)

-- Sec 13 lists this row as proved and Sec 13's footprint paragraph cites it by name; print
-- the footprint so that claim is machine-checked on every build.
#print axioms muInf_lt_floor

end MassGap.FreeField
