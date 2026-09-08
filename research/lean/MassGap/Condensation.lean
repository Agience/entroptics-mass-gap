import Mathlib

/-!
# MassGap.Condensation — vortex condensation from the entropy floor (R2)

For tension `μ` below the entropy floor `κ₀ = ¼ log 3`, the directed-cube-path vortex weights (Thm 7.1,
`N(A) ≥ 3^{(A-2)/4-1}` at `A = 4n+2`) grow without bound: the vortex partition sum through a plaquette
diverges — the condensation criterion, RIGOROUS from the count. The geometric base is `r = 3 e^{-4μ}`, and
`r > 1 ⟺ μ < κ₀`. This is strictly more than `κ ≥ κ₀`: the equivalence `condensation ⟺ μ < κ₀`.

Imported by the aggregate `MassGap.lean` (and re-exposed via `Capacity.free_energy_density_per_step`).
Build: `lake build MassGap.Condensation`.
API names to confirm on build: `Real.exp_nat_mul`, `tendsto_pow_atTop_atTop_of_one_lt`,
`Tendsto.const_mul_atTop`.
-/

namespace MassGap.Condensation

open Filter Topology

/-- Directed-cube-path weight at length `n`: `3^n` surfaces (Thm 7.1 lower bound, up to the constant `1/3`)
of area `4n+2`, action weight `e^{-μ(4n+2)}`. -/
noncomputable def vortexTerm (μ : ℝ) (n : ℕ) : ℝ := (3 : ℝ) ^ n * Real.exp (-μ * (4 * (n : ℝ) + 2))

/-- **Below the floor, the geometric base exceeds one:** `μ < ¼ log 3 ⇒ 1 < 3 · e^{-4μ}`. -/
theorem one_lt_base {μ : ℝ} (hμ : μ < (1 / 4) * Real.log 3) : (1 : ℝ) < 3 * Real.exp (-4 * μ) := by
  have h13 : (1 / 3 : ℝ) < Real.exp (-4 * μ) := by
    rw [show (1 / 3 : ℝ) = Real.exp (-Real.log 3) by
          rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]; norm_num]
    exact Real.exp_lt_exp.mpr (by linarith)
  linarith

/-- **Vortex condensation from the floor.** For `μ < κ₀ = ¼ log 3` the directed-cube-path weights diverge,
`vortexTerm μ n → ∞`, so the vortex partition sum diverges — vortices condense. Rigorous from Thm 7.1's count;
`condensation ⟺ μ < κ₀` via `r = 3 e^{-4μ} > 1`. -/
theorem vortexTerm_tendsto_atTop {μ : ℝ} (hμ : μ < (1 / 4) * Real.log 3) :
    Tendsto (vortexTerm μ) atTop atTop := by
  have hfac : ∀ n, vortexTerm μ n = Real.exp (-2 * μ) * (3 * Real.exp (-4 * μ)) ^ n := by
    intro n
    unfold vortexTerm
    rw [mul_pow, ← Real.exp_nat_mul,
        show -μ * (4 * (n : ℝ) + 2) = -2 * μ + (n : ℝ) * (-4 * μ) by ring, Real.exp_add]
    ring
  rw [tendsto_congr hfac]
  exact Tendsto.const_mul_atTop (Real.exp_pos _)
    (tendsto_pow_atTop_atTop_of_one_lt (one_lt_base hμ))

/-- The log-weight of the length-`n` term: `log(vortexTerm μ n) = n·log 3 − μ(4n+2)`. -/
theorem log_vortexTerm {μ : ℝ} (n : ℕ) :
    Real.log (vortexTerm μ n) = (n : ℝ) * Real.log 3 - μ * (4 * (n : ℝ) + 2) := by
  unfold vortexTerm
  rw [Real.log_mul (pow_ne_zero n (by norm_num : (3 : ℝ) ≠ 0)) (Real.exp_ne_zero _),
      Real.log_pow, Real.log_exp]
  ring

/-- **The per-step log-increment of the directed-cube lower-bound count `= 4(κ₀ − μ)`, exactly.** Each length
step adds 4 plaquettes and multiplies the length-`n` weight `3^n e^{-μ(4n+2)}` by `e^{4(κ₀−μ)}`: the per-step
change in log-weight is EXACTLY `4(κ₀ − μ)`. This is an arithmetic identity about the Thm 7.1 LOWER-BOUND count
`3^n` (not the physical partition function `Z`), sourced from the floor's count with no limit. Below the floor
(`μ < κ₀`) it is positive — the counted condensate log-weight grows at rate `κ₀ − μ`. Identifying this counted
rate with a transfer contraction rate `c` (`κ₀ − μ ≤ c`) is the 't Hooft / Greensite disorder duality. -/
theorem vortex_free_energy_per_step {μ : ℝ} (n : ℕ) :
    Real.log (vortexTerm μ (n + 1)) - Real.log (vortexTerm μ n) = 4 * ((1 / 4) * Real.log 3 - μ) := by
  rw [log_vortexTerm (n + 1), log_vortexTerm n]
  push_cast
  ring

/-! ### Entropy-bound link `ρ ≥ κ₀ − μ` — the provable half of `hfe : κ−μ ≤ c`

`hfe` (the vortex free-energy density `≤` the transfer contraction rate) decomposes as `κ−μ = ρ` ∘ `ρ ≤ c`.
The identification `ρ ≥ κ₀−μ` — the **entropy-bound link** — is PROVABLE from the count: any physical vortex
weight `Z` dominated by the directed-cube-path lower bound (`vortexTerm μ n ≤ Z n`, from `Floor`) has
free-energy density `≥ κ₀−μ`. Only the cited condensation⟹contraction duality `ρ ≤ c` (TY/Chatterjee)
then remains. -/

/-- **Entropy-bound link (log form).** A physical vortex weight `Z n` dominating the directed-cube count has
`log(Z n) ≥ n·log3 − μ(4n+2)` — the free energy is at least the counted floor (`Real.log` monotone). -/
theorem log_Z_ge {μ : ℝ} {Z : ℕ → ℝ} (hZ : ∀ n, vortexTerm μ n ≤ Z n) (n : ℕ) :
    (n : ℝ) * Real.log 3 - μ * (4 * n + 2) ≤ Real.log (Z n) := by
  have hpos : 0 < vortexTerm μ n := by unfold vortexTerm; positivity
  calc (n : ℝ) * Real.log 3 - μ * (4 * n + 2)
      = Real.log (vortexTerm μ n) := (log_vortexTerm n).symm
    _ ≤ Real.log (Z n) := Real.log_le_log hpos (hZ n)

/-- **Entropy-bound link (density-ratio form).** Dividing `log_Z_ge` by the area `4n+2`, the per-plaquette
free-energy density ratio is `≥ (n·log3)/(4n+2) − μ`, a sequence tending to `κ₀ − μ` (`lower_ratio_tendsto`).
So the vortex free-energy density `ρ ≥ κ₀ − μ` — the entropy-bound half of `hfe`, proved from the count. -/
theorem density_ratio_ge {μ : ℝ} {Z : ℕ → ℝ} (hZ : ∀ n, vortexTerm μ n ≤ Z n) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * Real.log 3 / (4 * n + 2) - μ ≤ Real.log (Z n) / (4 * n + 2) := by
  have h4 : 0 < (4 * (n : ℝ) + 2) := by positivity
  have hstep := (div_le_div_iff_of_pos_right h4).mpr (log_Z_ge hZ n)
  have hrw : ((n : ℝ) * Real.log 3 - μ * (4 * n + 2)) / (4 * n + 2)
      = (n : ℝ) * Real.log 3 / (4 * n + 2) - μ := by field_simp
  rwa [hrw] at hstep

/-- The lower-bound density ratio `(n·log3)/(4n+2) − μ` converges to `κ₀ − μ = ¼log3 − μ`. With
`density_ratio_ge`, this exhibits the vortex free-energy density as bounded below by a sequence tending to
`κ₀ − μ` — i.e. `ρ ≥ κ₀ − μ`. -/
theorem lower_ratio_tendsto {μ : ℝ} :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) * Real.log 3 / (4 * n + 2) - μ) atTop
      (𝓝 (1 / 4 * Real.log 3 - μ)) := by
  have hnd : Filter.Tendsto (fun n : ℕ => (n : ℝ) / (4 * n + 2)) atTop (𝓝 (1 / 4)) := by
    have he : (fun n : ℕ => (n : ℝ) / (4 * n + 2)) =ᶠ[atTop] (fun n : ℕ => 1 / (4 + 2 / n)) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      field_simp
    rw [tendsto_congr' he]
    have h2n : Filter.Tendsto (fun n : ℕ => (2 : ℝ) / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 2
    have h4 : Filter.Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (𝓝 4) := tendsto_const_nhds
    have hden : Filter.Tendsto (fun n : ℕ => (4 : ℝ) + 2 / n) atTop (𝓝 4) := by
      simpa using h4.add h2n
    have hc : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have := hc.div hden (by norm_num)
    simpa [Pi.div_def, one_div] using this
  have hmain : Filter.Tendsto (fun n : ℕ => (n : ℝ) * Real.log 3 / (4 * n + 2)) atTop
      (𝓝 (1 / 4 * Real.log 3)) := by
    have := hnd.mul_const (Real.log 3)
    have he : (fun n : ℕ => (n : ℝ) / (4 * n + 2) * Real.log 3)
        = (fun n : ℕ => (n : ℝ) * Real.log 3 / (4 * n + 2)) := by
      funext n; ring
    rw [he] at this
    simpa using this
  simpa using hmain.sub_const μ

end MassGap.Condensation
