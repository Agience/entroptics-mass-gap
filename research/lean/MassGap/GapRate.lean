import MassGap.Model
import MassGap.Aperture
import MassGap.Complete

/-!
# MassGap.GapRate — the difference `κ₀ - μ β` as a named decay rate

Defines `LatticeYM.massGap β := M.κ₀ - M.μ β` and restates the geometric bound of `MassGap.Model` in
terms of it, with the exponent written as `Real.exp (-(massGap β) * τ)` rather than
`Real.exp (-(massGap β)) ^ τ`.

Contents:
* `LatticeYM.massGap` — the difference between the floor field `κ₀` and the tension read `μ β`.
* `LatticeYM.massGap_pos_of_confinement` — `M.μ β < M.κ₀` gives `0 < M.massGap β`, by `linarith`.
* `mass_gap_exponential_decay` — for every `β` and every lag `τ : ℕ`,
  `‖∑ k ∈ M.s β, M.P β k * M.m β k ^ τ‖ ≤ (∑ k ∈ M.s β, ‖M.P β k‖) * exp (-(M.massGap β) * τ)`.
  Takes no hypothesis beyond the structure's own `hread` field.
* `confinement_mass_gap` — under `A1_YM M`, the conjunction of positivity and that bound at every
  coupling.
* `ym_mass_gap_rate` — the same conjunction for `ymModelAt N`, at every `β` with `0 ≤ β`, from the
  hypothesis `∀ β, 0 ≤ β → μYMAt N β < κ₀YM`.

Scope: `massGap` is a definition, not an existence claim — its positivity comes only from a
confinement hypothesis supplied by the caller. `ym_mass_gap_rate` takes that hypothesis for
`ymModelAt N` and does not prove it; it is restricted to `0 ≤ β`.
-/

namespace MassGap

/-- The difference `M.κ₀ - M.μ β` between the floor field and the tension read at coupling `β`, as a
real-valued function of `β`. A definition only: nothing here asserts it is positive.

DERIVED: no numeral occurs. Both terms are fields of `LatticeYM`. -/
noncomputable def LatticeYM.massGap (M : LatticeYM) (β : ℝ) : ℝ := M.κ₀ - M.μ β

/-- `M.μ β < M.κ₀` gives `0 < M.massGap β`. Unfolds the definition and closes by `linarith`; the
implication is stated in one direction only.

DERIVED: the one numeral is the `0` in `0 < M.massGap β`, the strict positivity of the
difference. -/
theorem LatticeYM.massGap_pos_of_confinement (M : LatticeYM) {β : ℝ} (h : M.μ β < M.κ₀) :
    0 < M.massGap β := by unfold LatticeYM.massGap; linarith

/-- The mode expansion is bounded by `exp (-(massGap β) * τ)` times the summed weight norms. For any
`M : LatticeYM`, coupling `β` and lag `τ : ℕ`,
`‖∑ k ∈ M.s β, M.P β k * M.m β k ^ τ‖ ≤ (∑ k ∈ M.s β, ‖M.P β k‖) * Real.exp (-(M.massGap β) * τ)`.
The proof is `Aperture.finite_sum_margin_bound` at ratio `Real.exp (-(M.κ₀ - M.μ β))` with the
structure field `M.hread` as its magnitude hypothesis, then `Real.exp_nat_mul` and `mul_comm` to move
the lag from an exponent on the ratio into the argument of the exponential.

Scope: no confinement hypothesis appears, so `M.massGap β` here may be zero or negative and the
right-hand side need not decay. Positivity is `LatticeYM.massGap_pos_of_confinement`, and the
combined statement is `confinement_mass_gap`.

DERIVED: no numeral occurs in the statement. `τ` is the lag, `M.massGap β` the rate. -/
theorem mass_gap_exponential_decay (M : LatticeYM) (β : ℝ) (τ : ℕ) :
    ‖∑ k ∈ M.s β, M.P β k * (M.m β k) ^ τ‖
      ≤ (∑ k ∈ M.s β, ‖M.P β k‖) * Real.exp (-(M.massGap β) * τ) := by
  unfold LatticeYM.massGap
  have h := finite_sum_margin_bound (M.s β) (M.P β) (M.m β)
    (Real.exp (-(M.κ₀ - M.μ β))) (M.hread β) τ
  rw [← Real.exp_nat_mul] at h
  rwa [mul_comm (τ : ℝ) (-(M.κ₀ - M.μ β))] at h

/-- From `A1_YM M`, at every coupling `β`: `0 < M.massGap β`, and the exponential bound of
`mass_gap_exponential_decay` at every lag. The pairing of the previous two theorems, with `A1_YM M`
supplying `M.μ β < M.κ₀` at each `β`.

Scope: `A1_YM M` is a hypothesis. The bound is at fixed lattice data — `β` ranges over all reals,
but nothing here varies the lattice spacing or the volume.

DERIVED: the one numeral is the `0` in `0 < M.massGap β`. -/
theorem confinement_mass_gap (M : LatticeYM) (h1 : A1_YM M) :
    ∀ β, 0 < M.massGap β ∧
      ∀ τ : ℕ, ‖∑ k ∈ M.s β, M.P β k * (M.m β k) ^ τ‖
        ≤ (∑ k ∈ M.s β, ‖M.P β k‖) * Real.exp (-(M.massGap β) * τ) :=
  fun β => ⟨M.massGap_pos_of_confinement (h1 β), mass_gap_exponential_decay M β⟩

/-- The same conjunction for `ymModelAt N`. Given `N : ℕ` and the hypothesis
`hconf : ∀ β, 0 ≤ β → μYMAt N β < κ₀YM`, then for every `β` with `0 ≤ β`: `0 < (ymModelAt N).massGap β`,
and the exponential bound of `mass_gap_exponential_decay` at every lag `τ : ℕ`. Obtained by applying
the two preceding theorems to `ymModelAt N`.

Scope: `hconf` is a hypothesis, restricted to `0 ≤ β`; both conclusions carry the same restriction.
`N` is unconstrained — no lower bound on the gauge group rank is imposed.

DERIVED: the only numeral is `0`, appearing as the lower bound on the coupling in `0 ≤ β` (in the
hypothesis and again in the conclusion) and as the strict lower bound on the gap. `κ₀YM` and
`μYMAt N` are named elsewhere and contribute no literal here. -/
theorem ym_mass_gap_rate (N : ℕ) (hconf : ∀ β, 0 ≤ β → μYMAt N β < κ₀YM) :
    ∀ β, 0 ≤ β → 0 < (ymModelAt N).massGap β ∧
      ∀ τ : ℕ, ‖∑ k ∈ (ymModelAt N).s β, (ymModelAt N).P β k * ((ymModelAt N).m β k) ^ τ‖
        ≤ (∑ k ∈ (ymModelAt N).s β, ‖(ymModelAt N).P β k‖)
            * Real.exp (-((ymModelAt N).massGap β) * τ) :=
  fun β hβ => ⟨(ymModelAt N).massGap_pos_of_confinement (hconf β hβ),
    mass_gap_exponential_decay (ymModelAt N) β⟩

-- Axiom footprint: `#print axioms ym_mass_gap_rate` returns
-- `propext, Classical.choice, Quot.sound, wilson_reflection_positive_at`.
-- No isotropy input appears; the statement uses only the confinement hypothesis `hconf`.
#print axioms ym_mass_gap_rate

end MassGap
