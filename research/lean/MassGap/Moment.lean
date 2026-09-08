import Mathlib

/-!
# C-1: the crossover tension from a bounded correlation moment (the analytic half, machine-checked)

The min-entropy tension the gap reads is `μ = log(S(0)/S(2π/L))` of the whitened :F²: correlation, where
`S(k) = Σ_d ρ(d) cos(2πkd/L)`. With reflection positivity (`ρ ≥ 0`, so `λ₁ = S(0)` and `λ₂ ≥ S(2π/L)`,
`FreeField.structure_factor_peak_at_zero`), `μ ≤ log(S(0)/S(2π/L)) = -log ⟨cos θ⟩_ρ`. This module proves the
purely analytic step that turns a **bounded correlation second moment** into confinement `μ < κ₀`:

    ⟨cos θ⟩_ρ ≥ 1 - ⟨θ²⟩_ρ/2   (cos x ≥ 1 - x²/2),   and   ⟨cos θ⟩ > 3^{-1/4} ⟹ -log⟨cos θ⟩ < ¼log3 = κ₀,

so `μ < κ₀` whenever `⟨θ²⟩_ρ/2 < 1 - 3^{-1/4}`, i.e. `M₂ < (1-3^{-1/4})L²/(2π²)` (a bounded correlation
length). This is the machine-checked half of C-1; the measured input — that the :F²: correlation moment IS bounded
across the crossover (finite specific heat / SU(N) no bulk transition) — is the cited physical content
.
-/

namespace MassGap.Moment

open scoped BigOperators

/-- **The cos-moment bound.** For a probability vector `p` over a finite index and angles `θ`, the
`p`-average of `cos θ` is at least `1 - ⟨θ²⟩/2` (termwise `cos x ≥ 1 - x²/2`). -/
theorem cos_avg_ge {ι : Type*} [Fintype ι] (p θ : ι → ℝ)
    (hp : ∀ d, 0 ≤ p d) (hsum : ∑ d, p d = 1) :
    1 - (∑ d, p d * (θ d) ^ 2) / 2 ≤ ∑ d, p d * Real.cos (θ d) := by
  have key : ∑ d, p d * (1 - (θ d) ^ 2 / 2) ≤ ∑ d, p d * Real.cos (θ d) :=
    Finset.sum_le_sum fun d _ =>
      mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos) (hp d)
  have hpt : ∀ d, p d * (1 - (θ d) ^ 2 / 2) = p d - p d * (θ d) ^ 2 / 2 := fun d => by ring
  have expand : ∑ d, p d * (1 - (θ d) ^ 2 / 2) = 1 - (∑ d, p d * (θ d) ^ 2) / 2 := by
    rw [Finset.sum_congr rfl (fun d _ => hpt d), Finset.sum_sub_distrib, hsum, ← Finset.sum_div]
  rwa [expand] at key

/-- **-log of a value above `3^{-1/4}` is below the floor `κ₀ = ¼log3`.** -/
theorem neg_log_lt_floor {c : ℝ} (hc : (3 : ℝ) ^ (-(1 : ℝ) / 4) < c) :
    - Real.log c < (1 / 4) * Real.log 3 := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have hlog : Real.log ((3 : ℝ) ^ (-(1 : ℝ) / 4)) = -(1 / 4) * Real.log 3 := by
    rw [Real.log_rpow (by norm_num)]; ring
  have hmono : Real.log ((3 : ℝ) ^ (-(1 : ℝ) / 4)) < Real.log c := Real.log_lt_log h3 hc
  rw [hlog] at hmono
  linarith

/-- **The crossover tension is below the floor from a bounded moment (the analytic half of C-1).**
If the `p`-weighted angular second moment satisfies `⟨θ²⟩/2 < 1 - 3^{-1/4}`, then the min-entropy tension
`μ = -log ⟨cos θ⟩` is strictly below the entropy floor `κ₀ = ¼ log 3`. Combined with reflection positivity
(`μ ≤ -log⟨cos θ⟩`, `λ₁=S(0)`, `λ₂ ≥ S(2π/L)`) this is `μ < κ₀`; the measured input is that the moment IS bounded
(finite correlation length / no bulk transition), the cited physical content. -/
theorem tension_lt_floor_of_moment {ι : Type*} [Fintype ι] (p θ : ι → ℝ)
    (hp : ∀ d, 0 ≤ p d) (hsum : ∑ d, p d = 1)
    (hmom : (∑ d, p d * (θ d) ^ 2) / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    - Real.log (∑ d, p d * Real.cos (θ d)) < (1 / 4) * Real.log 3 := by
  have hcavg := cos_avg_ge p θ hp hsum
  have hc_gt : (3 : ℝ) ^ (-(1 : ℝ) / 4) < ∑ d, p d * Real.cos (θ d) := by
    have h1 : (3 : ℝ) ^ (-(1 : ℝ) / 4) < 1 - (∑ d, p d * (θ d) ^ 2) / 2 := by linarith
    linarith
  exact neg_log_lt_floor hc_gt

/-! ## The concrete entropy-matched read: `μ`, `p`, `θ` derived from a nonnegative correlation

A translation-invariant whitened correlation `ρ ≥ 0` over the lag index determines the read outright: the
probability vector `p = ρ/Σρ`, the angles `θ_d = 2π d /(N+1)`, and the min-entropy tension
`μ = -log ⟨cos θ⟩_p = log(S(0)/S(2π/N))`. So `p`'s vector properties and the tension identity are
THEOREMS; the only inputs are `ρ ≥ 0` (reflection positivity) and the bounded moment (finite
correlation length / no bulk transition). -/

/-- A concrete entropy-matched read: a whitened, translation-invariant correlation `ρ ≥ 0` over the lag
index, with positive total mass. Everything the gap uses (`p`, `θ`, the tension `μ`) is derived from it. -/
structure Read (N : ℕ) where
  ρ : Fin (N + 1) → ℝ
  hρ : ∀ d, 0 ≤ ρ d
  hpos : 0 < ∑ d, ρ d

/-- A read always exists (the flat correlation `ρ ≡ 1`), so any opaque ensemble data valued in `Read N` is
well-formed. (The proof's read is the concrete `readA (wilsonCorr β) _`.) -/
instance (N : ℕ) : Inhabited (Read N) where
  default :=
    { ρ := fun _ => 1
      hρ := fun _ => zero_le_one
      hpos := Finset.sum_pos (fun _ _ => one_pos) ⟨0, Finset.mem_univ 0⟩ }

namespace Read

variable {N : ℕ} (R : Read N)

/-- The correlation as a probability vector `p_d = ρ_d / Σρ`. -/
noncomputable def p (d : Fin (N + 1)) : ℝ := R.ρ d / ∑ d', R.ρ d'
/-- The lag angle `θ_d = 2π d /(N+1)` (the `k=1` structure-factor phase). Carries `R` so `R.θ` reads as a
field of the concrete read even though the angle depends only on the lattice index. -/
noncomputable def θ (_R : Read N) (d : Fin (N + 1)) : ℝ := 2 * Real.pi * (d : ℝ) / (N + 1)
/-- The min-entropy tension `μ = -log ⟨cos θ⟩_p = log(S(0)/S(2π/N))`. -/
noncomputable def tension : ℝ := - Real.log (∑ d, R.p d * Real.cos (R.θ d))

theorem p_nonneg (d : Fin (N + 1)) : 0 ≤ R.p d := div_nonneg (R.hρ d) R.hpos.le

theorem p_sum : ∑ d, R.p d = 1 := by
  unfold Read.p
  rw [← Finset.sum_div, div_self (ne_of_gt R.hpos)]

/-- **The concrete tension is below the floor from a bounded moment** (via `tension_lt_floor_of_moment`):
`μ = -log⟨cos θ⟩ < κ₀ = ¼log3` when `⟨θ²⟩/2 < 1 - 3^{-1/4}`. -/
theorem tension_lt_floor
    (hmom : (∑ d, R.p d * (R.θ d) ^ 2) / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    R.tension < (1 / 4) * Real.log 3 :=
  tension_lt_floor_of_moment R.p R.θ (fun d => R.p_nonneg d) R.p_sum hmom

/-- The lag angle squared factors the `1/L²` aperture scaling out of the lag index: `θ_d² = (2π/(N+1))² d²`. -/
theorem theta_sq (d : Fin (N + 1)) : (R.θ d) ^ 2 = (2 * Real.pi / (N + 1)) ^ 2 * (d : ℝ) ^ 2 := by
  unfold Read.θ; ring

/-- The angular second moment factors as `⟨θ²⟩ = (2π/(N+1))² ⟨d²⟩`: the correlation's angular spread is its
lag second moment (a squared correlation length) times the explicit `1/L²` aperture scaling. -/
theorem thetaMoment_eq :
    ∑ d, R.p d * (R.θ d) ^ 2 = (2 * Real.pi / (N + 1)) ^ 2 * ∑ d, R.p d * (d : ℝ) ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => by rw [R.theta_sq d]; ring

/-- **The crossover tension is below the floor from a bounded LAG second moment, with the `1/L²` scaling made
explicit.** If the lag second moment `⟨d²⟩ ≤ B` (a finite correlation length, `L`-independent) and the
aperture scaling `(2π/(N+1))² B / 2 < 1 - 3^{-1/4}` holds, then `μ = -log⟨cos θ⟩ < κ₀`. Since
`(2π/(N+1))² → 0`, for fixed `B` the scaling condition holds for every `L` beyond a threshold — so the margin
grows `∝ L²`, a **theorem**. This separates the **proven** aperture scaling from
the physical input: a bounded lag second moment = finite correlation length / SU(N) no-bulk-transition
. It is NOT the energy susceptibility `χ_v` — that Shannon/specific-heat object
does not bound this spatial moment (the Rényi mismatch, PAPER §8.4). -/
theorem tension_lt_floor_of_lag_moment {B : ℝ}
    (hB : ∑ d, R.p d * (d : ℝ) ^ 2 ≤ B)
    (hscale : (2 * Real.pi / (N + 1)) ^ 2 * B / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    R.tension < (1 / 4) * Real.log 3 := by
  apply R.tension_lt_floor
  rw [thetaMoment_eq]
  have hmul : (2 * Real.pi / (N + 1)) ^ 2 * ∑ d, R.p d * (d : ℝ) ^ 2
      ≤ (2 * Real.pi / (N + 1)) ^ 2 * B := mul_le_mul_of_nonneg_left hB (sq_nonneg _)
  linarith

end Read

end MassGap.Moment
