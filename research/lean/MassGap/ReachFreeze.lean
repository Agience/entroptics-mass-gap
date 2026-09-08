import Mathlib

/-!
# The reach-freeze reduction (PAPER Sec 6)

The gap reduces to a positive per-step contraction of the entropy-rate excess. Let `sigma : ℕ → ℝ`
be the excess along the reach axis (nonnegative, PAPER Sec 6), and suppose the finite self-sourcing
screen supplies a fixed positive contraction: for some `c` with `0 < c ≤ 1`,

    sigma (n+1) ≤ (1 - c) * sigma n   for every reach step n.

From that hypothesis alone this file certifies:

* `excess_geometric`         : `sigma n ≤ (1 - c)^n * sigma 0`      (geometric decay)
* `excess_exp_bound`         : `sigma n ≤ exp (-c * n) * sigma 0`   (decay at rate ≥ c)
* `excess_tendsto_zero`      : `sigma ⟶ 0`                          (a_IR = 0)
* `gap_from_contraction`     : the three together, so `Delta ≥ c > 0`.
* `excess_tendsto_zero_of_geom` : the DMD-spectral form (`sigma n ≤ C ρⁿ`, `ρ < 1`).
* `confines_of_tension_lt_floor` : tension below the floor gives negative vortex free energy.

The single input is `0 < c`, supplied by the self-sourcing tiling (PAPER Sec 5) when the
centre-vortex tension stays below the floor, `μ < κ₀` (`Floor.lean` certifies `κ₀ = (1/4) log 3`).
Downstream of `c > 0` the gap is elementary real analysis, recorded here.
-/

namespace MassGap

variable {sigma : ℕ → ℝ} {c : ℝ}

/-- **Geometric decay from a one-step contraction.** If `sigma (n+1) ≤ (1-c) sigma n` and
`c ≤ 1`, then `sigma n ≤ (1-c)^n * sigma 0`. -/
theorem excess_geometric (hc1 : c ≤ 1)
    (hstep : ∀ n, sigma (n + 1) ≤ (1 - c) * sigma n) :
    ∀ n, sigma n ≤ (1 - c) ^ n * sigma 0 := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      have h1c : (0 : ℝ) ≤ 1 - c := by linarith
      calc sigma (k + 1) ≤ (1 - c) * sigma k := hstep k
        _ ≤ (1 - c) * ((1 - c) ^ k * sigma 0) := by
              exact mul_le_mul_of_nonneg_left ih h1c
        _ = (1 - c) ^ (k + 1) * sigma 0 := by ring

/-- **Decay at rate at least `c`.** The geometric ratio `1-c` is below `exp (-c)`, so the excess is
bounded by `exp (-c n) * sigma 0`: the exponential decay rate is `≥ c`, i.e. `Delta ≥ c`. -/
theorem excess_exp_bound (hc1 : c ≤ 1)
    (hstep : ∀ n, sigma (n + 1) ≤ (1 - c) * sigma n) (hσ0 : 0 ≤ sigma 0) :
    ∀ n, sigma n ≤ Real.exp (-c * n) * sigma 0 := by
  intro n
  have hgeo := excess_geometric hc1 hstep n
  have h1c : (0 : ℝ) ≤ 1 - c := by linarith
  have h1 : 1 - c ≤ Real.exp (-c) := by
    have := Real.add_one_le_exp (-c); linarith
  have h2 : (1 - c) ^ n ≤ (Real.exp (-c)) ^ n := by gcongr
  have h3 : (Real.exp (-c)) ^ n = Real.exp (-c * n) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hle : (1 - c) ^ n ≤ Real.exp (-c * n) := by rw [← h3]; exact h2
  calc sigma n ≤ (1 - c) ^ n * sigma 0 := hgeo
    _ ≤ Real.exp (-c * n) * sigma 0 := by exact mul_le_mul_of_nonneg_right hle hσ0

/-- **The excess tends to zero (`a_IR = 0`).** A positive contraction sends the excess to `0`, so the
aperture is band-limited and the reach freezes. -/
theorem excess_tendsto_zero (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hstep : ∀ n, sigma (n + 1) ≤ (1 - c) * sigma n)
    (hσnn : ∀ n, 0 ≤ sigma n) :
    Filter.Tendsto sigma Filter.atTop (nhds 0) := by
  have hub := excess_geometric hc1 hstep
  have h1c : (0 : ℝ) ≤ 1 - c := by linarith
  have hlt : (1 - c) < 1 := by linarith
  have hpow : Filter.Tendsto (fun n => (1 - c) ^ n * sigma 0) Filter.atTop (nhds 0) := by
    have hz := tendsto_pow_atTop_nhds_zero_of_lt_one h1c hlt
    simpa using hz.mul_const (sigma 0)
  exact squeeze_zero hσnn hub hpow

/-- **The reduction (PAPER Sec 6), assembled.** Given a nonnegative entropy-rate excess and a
positive per-step contraction `c`, the excess decays exponentially at rate `≥ c`, tends to zero
(`a_IR = 0`), and `c > 0`. Hence the gap `Delta ≥ c > 0`. The hypotheses are the sole inputs; `c > 0`
is supplied by the self-sourcing screen (`μ < κ₀`). -/
theorem gap_from_contraction (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hσnn : ∀ n, 0 ≤ sigma n)
    (hstep : ∀ n, sigma (n + 1) ≤ (1 - c) * sigma n) :
    (∀ n, sigma n ≤ Real.exp (-c * n) * sigma 0) ∧
      Filter.Tendsto sigma Filter.atTop (nhds 0) ∧ 0 < c :=
  ⟨excess_exp_bound hc1 hstep (hσnn 0),
   excess_tendsto_zero hc0 hc1 hstep hσnn, hc0⟩

/-- **Floor and tension give confinement.** The centre-vortex free-energy density is `F_v = μ - κ`
(tension minus entropy). With the floor `κ₀ ≤ κ` (`Floor.lean`) and the tension below the floor,
`μ < κ₀`, the free energy is negative, so vortices condense and the theory confines. -/
theorem confines_of_tension_lt_floor {μ κ κ₀ : ℝ} (hfloor : κ₀ ≤ κ) (htension : μ < κ₀) :
    μ - κ < 0 := by linarith

/-- **Spectral (DMD-native) form of the decay.** If the excess is dominated by a geometric sequence
`σ n ≤ C ρⁿ` with `0 ≤ ρ < 1`, it tends to zero (`a_IR = 0`). Here `ρ` is the DMD/Koopman spectral
radius on the excess (`ρ = e^{-Δ}`, so `ρ < 1 ↔ Δ > 0`), which is what `rates().dominant` reads. It
asks only for the spectral radius, so it is insensitive to non-normal transients (the constant `C`
absorbs them). -/
theorem excess_tendsto_zero_of_geom {σ : ℕ → ℝ} {C ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hσnn : ∀ n, 0 ≤ σ n) (hbound : ∀ n, σ n ≤ C * ρ ^ n) :
    Filter.Tendsto σ Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun n => C * ρ ^ n) Filter.atTop (nhds 0) := by
    have hz := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
    simpa using hz.const_mul C
  exact squeeze_zero hσnn hbound hpow

end MassGap
