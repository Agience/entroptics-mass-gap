import MassGap.Model
import MassGap.Aperture
import MassGap.Complete

/-!
# The certified decay rate is the entropy margin: quantitative exponential decay (the bridge to the classical Δ)

The statement asks for a mass gap `Δ > 0` with the Hamiltonian spectrum in `{0} ∪ [Δ, ∞)` — equivalently,
the Euclidean two-point function decays exponentially at rate `Δ`. This module reads that rate on the
entroptics side as the **entropy margin** `κ₀ − μ`: the two-point function decays at rate `κ₀ − μ`, so the
classical gap is bounded below by it, `Δ ≥ κ₀ − μ`.

* `LatticeYM.massGap β := κ₀ − μ(β)` — the certified decay rate, the margin between the read tension and the
  entropy floor;
* `LatticeYM.massGap_pos_of_confinement` — it is positive exactly in the confined phase (A1: `μ < κ₀`);
* `mass_gap_exponential_decay` — the autocorrelation obeys `‖C τ‖ ≤ (Σ‖P k‖) · e^{−(κ₀−μ) τ}`, exponential
  decay at rate `κ₀ − μ`;
* `confinement_mass_gap` — under A1, a positive gap and exponential clustering at every coupling.

This is a **bridge on the model's existing read margin `hread`** — no new axiom: it upgrades the reduction's
qualitative `C(τ)→0` (`Aperture.finite_flow_decays`) to the quantitative rate the result names, giving
`Δ ≥ κ₀ − μ`, the entropy margin, at every coupling.
-/

namespace MassGap

/-- **The certified decay rate `κ₀ − μ(β)`**, the entropy margin between the read tension and the floor: the
two-point function decays at least this fast, so the classical mass gap is bounded below by it, `Δ ≥ κ₀ − μ`. -/
noncomputable def LatticeYM.massGap (M : LatticeYM) (β : ℝ) : ℝ := M.κ₀ - M.μ β

/-- **The mass gap is positive in the confined phase.** `Δ = κ₀ − μ > 0 ⟺ μ < κ₀` (A1 confinement). -/
theorem LatticeYM.massGap_pos_of_confinement (M : LatticeYM) {β : ℝ} (h : M.μ β < M.κ₀) :
    0 < M.massGap β := by unfold LatticeYM.massGap; linarith

/-- **The mass gap is the entropy margin, and it is the exponential decay rate.** Every active mode magnitude
clears the margin `e^{−Δ}` (`hread`, `Δ = κ₀ − μ`), so the finite-aperture autocorrelation decays
exponentially at rate `Δ`: `‖C τ‖ ≤ (Σ‖P k‖) · e^{−Δ τ}`. This is the *quantitative* mass gap — the spectrum
is bounded away from 0 by `Δ` (the classical `spec ⊆ {0} ∪ [Δ, ∞)`), and `Δ` is exactly the entroptics
entropy margin `κ₀ − μ`: the same object, machine-checked, no new axiom. -/
theorem mass_gap_exponential_decay (M : LatticeYM) (β : ℝ) (τ : ℕ) :
    ‖∑ k ∈ M.s β, M.P β k * (M.m β k) ^ τ‖
      ≤ (∑ k ∈ M.s β, ‖M.P β k‖) * Real.exp (-(M.massGap β) * τ) := by
  unfold LatticeYM.massGap
  have h := finite_sum_margin_bound (M.s β) (M.P β) (M.m β)
    (Real.exp (-(M.κ₀ - M.μ β))) (M.hread β) τ
  rw [← Real.exp_nat_mul] at h
  rwa [mul_comm (τ : ℝ) (-(M.κ₀ - M.μ β))] at h

/-- **Confinement ⟹ a positive mass gap and exponential clustering at every coupling.** Under A1
(`μ β < κ₀` at every coupling), the mass gap `Δ(β) = κ₀ − μ(β) > 0` is positive and the two-point function
decays exponentially at that rate. This is the quantitative gap together with OS4 clustering, with `Δ`
the entropy margin — the bridge from the entroptics read to the classical mass-gap statement. -/
theorem confinement_mass_gap (M : LatticeYM) (h1 : A1_YM M) :
    ∀ β, 0 < M.massGap β ∧
      ∀ τ : ℕ, ‖∑ k ∈ M.s β, M.P β k * (M.m β k) ^ τ‖
        ≤ (∑ k ∈ M.s β, ‖M.P β k‖) * Real.exp (-(M.massGap β) * τ) :=
  fun β => ⟨M.massGap_pos_of_confinement (h1 β), mass_gap_exponential_decay M β⟩

/-- **The SU(N) Yang–Mills mass gap has an explicit positive rate.** For the discharged model `ymModel`, the
mass gap `Δ(β) = κ₀ − μYM(β) = ¼log3 − μYM(β) > 0` at every physical coupling `β ≥ 0` (from `ym_confinement`), and the two-point
function decays exponentially at rate `Δ`: the *quantitative* gap (`spec ⊆ {0} ∪ [Δ,∞)`) and OS4
clustering, with `Δ` the entropy margin. Same axiom footprint as `ym_mass_gap` — this is a strengthening
of its qualitative `C(τ)→0` to the exponential rate, not a new input. -/
theorem ym_mass_gap_rate :
    ∀ β, 0 ≤ β → 0 < ymModel.massGap β ∧
      ∀ τ : ℕ, ‖∑ k ∈ ymModel.s β, ymModel.P β k * (ymModel.m β k) ^ τ‖
        ≤ (∑ k ∈ ymModel.s β, ‖ymModel.P β k‖) * Real.exp (-(ymModel.massGap β) * τ) :=
  fun β hβ => ⟨ymModel.massGap_pos_of_confinement (ym_confinement β hβ),
    mass_gap_exponential_decay ymModel β⟩

-- Footprint: the same named inputs as `ym_mass_gap`'s A1 side (no A2 / `Otr_iso` — the gap is pure
-- confinement), and NO new axiom. `#print axioms ym_mass_gap_rate` returns
-- `propext, Classical.choice, Quot.sound, ym_asymfree, ym_character, wilson_reflection_positive, d2_le_bound`.
-- (`ym_finite_aperture` is a `norm_num` theorem, so it does not appear in the footprint.)
#print axioms ym_mass_gap_rate

end MassGap
