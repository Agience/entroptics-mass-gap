import Mathlib
import MassGap.Apriori

/-!
# MassGap.Model — the lattice Yang-Mills model interface

`MassGap.Apriori` states two propositions over abstract data: `A1 μ κ₀ : ∀ β, μ β < κ₀` and
`A2 R : ∀ d d', R d = R d'`. This module names that data as the objects of a lattice `SU(N)` gauge
theory, bundles it into the structure `LatticeYM`, and re-expresses the two propositions as
predicates `A1_YM` and `A2_YM` on a single value of that structure.

Contents:
* `LatticeYM` — a mode index type `Idx`, an orientation type `Dir`, the coupling-indexed active mode
  set `s : ℝ → Finset Idx`, the weights `P` and magnitudes `m` of the finite exponential expansion
  `C τ = ∑ P k * m k ^ τ`, the tension read `μ : ℝ → ℝ`, the directional read `R : Dir → ℝ`, the
  floor `κ₀`, the multiplicity density `κ`, and two hypothesis fields: `hfloor : κ₀ ≤ κ` and
  `hread`, which bounds every active mode magnitude at coupling `β` by `exp (-(κ₀ - μ β))`.
* `A1_YM`, `A2_YM` — the two propositions instantiated at the structure's fields.
* `geometric_bound_of_mode_bound` — a finite mode sum whose magnitudes are bounded by `E` satisfies
  `‖∑ P k * m k ^ τ‖ ≤ (∑ ‖P k‖) * E ^ τ`.
* `mass_gap_rate_of_model` — from `A1_YM`, both `0 < κ₀ - μ β` and that geometric bound at
  `E = exp (-(κ₀ - μ β))`.
* `mass_gap_ratio_lt_one` — from `A1_YM`, `exp (-(κ₀ - μ β)) < 1`.
* `mass_gap_of_model` — `existence_and_gap_from_apriori` applied to the structure's fields, giving
  convergence of the correlation to `0`, `μ β - κ < 0`, and direction-independence of `R`.

Scope. The structure takes `Idx, Dir, s, P, m, μ, R, κ₀, κ` as data; no realisation of them from the
`SU(N)` Wilson measure is constructed here. `hfloor` and `hread` are fields, so they are assumed of
any `LatticeYM` supplied. `A1_YM` and `A2_YM` are explicit hypotheses of every theorem below that
uses them.
-/

namespace MassGap

/-- The lattice Yang-Mills model interface: the abstract data consumed by
`existence_and_gap_from_apriori`, named as the objects of a lattice `SU(N)` gauge theory and indexed
by the coupling `β`. Two fields are hypotheses (`hfloor`, `hread`), so constructing a value of this
structure assumes them.

DERIVED: no numeral occurs in the fields; `hread`'s bound is `exp (-(κ₀ - μ β))`, built from the two
named fields, and `hfloor` compares two of them. -/
structure LatticeYM where
  /-- Mode index type of the entropy-matched correlation read. -/
  Idx : Type
  /-- Orientation type of the directional read. -/
  Dir : Type
  /-- Active modes above the noise floor at coupling `β`. -/
  s : ℝ → Finset Idx
  /-- Mode weights `P_k(β)` of the finite exponential sum `C(τ) = ∑ P_k m_k^τ`. -/
  P : ℝ → Idx → ℂ
  /-- Mode magnitudes `m_k(β)` (DMD / transfer-matrix eigenvalues). -/
  m : ℝ → Idx → ℂ
  /-- The centre-vortex tension read `μ(β)`. -/
  μ : ℝ → ℝ
  /-- The directional (orientation) read `R`. -/
  R : Dir → ℝ
  /-- The entropy floor `κ₀ = ¼ log 3` (`Floor.floor_pos`). -/
  κ₀ : ℝ
  /-- The vortex multiplicity density `κ`, with the floor below it. -/
  κ : ℝ
  /-- The entropy floor sits below the multiplicity density. -/
  hfloor : κ₀ ≤ κ
  /-- At every coupling `β`, every active mode magnitude is bounded by `exp (-(κ₀ - μ β))`. A
  hypothesis field; `Apriori.hread_of_dominant` is one way to produce it. -/
  hread : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-(κ₀ - μ β))

/-- `A1` at the model's fields: `∀ β, M.μ β < M.κ₀`, the tension read strictly below the floor at
every coupling. A `Prop`, not a theorem; it is supplied as a hypothesis wherever it is used.

DERIVED: no numeral occurs; both sides are fields of the structure. -/
def A1_YM (M : LatticeYM) : Prop := A1 M.μ M.κ₀

/-- `A2` at the model's fields: `∀ d d', M.R d = M.R d'`, the directional read taking the same value
in every direction. A `Prop`, not a theorem; it is supplied as a hypothesis wherever it is used.

DERIVED: no numeral occurs; the statement compares two values of one field. -/
def A2_YM (M : LatticeYM) : Prop := A2 M.R

/-- A finite mode expansion with bounded magnitudes obeys a geometric bound. Over a `Finset` `s` of
mode indices with weights `P : Idx → ℂ` and magnitudes `m : Idx → ℂ`, given `0 ≤ E` and `‖m k‖ ≤ E`
for every `k ∈ s`, the expansion satisfies
`‖∑ k ∈ s, P k * m k ^ τ‖ ≤ (∑ k ∈ s, ‖P k‖) * E ^ τ` at every lag `τ : ℕ`. Proved by `norm_sum_le`
followed by a termwise `pow_le_pow_left₀`.

Scope: the bound holds for any `0 ≤ E`, including `E ≥ 1`, so on its own it is not a decay
statement; strictness is the caller's, for instance via `E = exp (-(κ₀ - μ β))` with `μ β < κ₀`. The
statement mentions no `LatticeYM`, so it serves the model level and the Wilson level alike; those
two differ only in where the magnitude bound comes from.

DERIVED: the one numeral is the `0` in `0 ≤ E`, which is what makes `E ^ τ` monotone in `E`. `τ` is
the lag and `E` the caller's bound; no numeral is a model constant. -/
theorem geometric_bound_of_mode_bound {Idx : Type*} (s : Finset Idx) (P m : Idx → ℂ) (E : ℝ)
    (hE : 0 ≤ E) (hm : ∀ k ∈ s, ‖m k‖ ≤ E) (τ : ℕ) :
    ‖∑ k ∈ s, P k * (m k) ^ τ‖ ≤ (∑ k ∈ s, ‖P k‖) * E ^ τ := by
  calc ‖∑ k ∈ s, P k * (m k) ^ τ‖ ≤ ∑ k ∈ s, ‖P k * (m k) ^ τ‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ s, ‖P k‖ * E ^ τ := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hm k hk) τ) (norm_nonneg _)
    _ = (∑ k ∈ s, ‖P k‖) * E ^ τ := by rw [← Finset.sum_mul]

#print axioms geometric_bound_of_mode_bound

/-- Geometric decay of the mode expansion at rate `κ₀ - μ β`. From `A1_YM M` and a coupling `β`,
the conclusion is a conjunction: `0 < M.κ₀ - M.μ β`, and at every lag `τ : ℕ`

    ‖∑ k ∈ M.s β, M.P β k * M.m β k ^ τ‖ ≤ (∑ k ∈ M.s β, ‖M.P β k‖) * exp (-(M.κ₀ - M.μ β)) ^ τ.

The first component is `sub_pos.mpr` applied to `A1_YM` at `β`; the second is
`geometric_bound_of_mode_bound` at `E = Real.exp (-(M.κ₀ - M.μ β))`, whose magnitude hypothesis is
the structure field `M.hread`.

Scope: `β` is a fixed argument, so this is a statement at one coupling; it says nothing about
uniformity in the lattice spacing. `M.hread` is a field of `LatticeYM` and is assumed rather than
derived.

DERIVED: the one numeral is the `0` in `0 < M.κ₀ - M.μ β`, the strict positivity of the difference.
`κ₀` and `μ β` are fields of the structure; no number is introduced here. -/
theorem mass_gap_rate_of_model (M : LatticeYM) (h1 : A1_YM M) (β : ℝ) :
    0 < M.κ₀ - M.μ β ∧
      ∀ τ : ℕ, ‖∑ k ∈ M.s β, M.P β k * (M.m β k) ^ τ‖
        ≤ (∑ k ∈ M.s β, ‖M.P β k‖) * Real.exp (-(M.κ₀ - M.μ β)) ^ τ := by
  exact ⟨sub_pos.mpr (h1 β),
    fun τ => geometric_bound_of_mode_bound (M.s β) (M.P β) (M.m β) _
      (Real.exp_pos _).le (fun k hk => M.hread β k hk) τ⟩

#print axioms mass_gap_rate_of_model

/-- The decay constant is strictly below one. From `A1_YM M` and a coupling `β`,
`Real.exp (-(M.κ₀ - M.μ β)) < 1`, via `Real.exp_lt_one_iff` applied to the positive difference
`M.κ₀ - M.μ β`. The ratio form of the same content as `mass_gap_rate_of_model`, and the form
`ZeroMode.gap_phys_of_fixed_screen` consumes.

DERIVED: the one numeral is the `1` bounding the exponential; it is `Real.exp 0`, the value the
exponential would take at a zero margin, so the strict inequality is exactly
`0 < M.κ₀ - M.μ β`. -/
theorem mass_gap_ratio_lt_one (M : LatticeYM) (h1 : A1_YM M) (β : ℝ) :
    Real.exp (-(M.κ₀ - M.μ β)) < 1 := by
  have hgap : 0 < M.κ₀ - M.μ β := sub_pos.mpr (h1 β)
  exact Real.exp_lt_one_iff.mpr (by linarith)

#print axioms mass_gap_ratio_lt_one

/-- The three conclusions of `existence_and_gap_from_apriori`, at the model's fields. From `A1_YM M`
and `A2_YM M`, a triple conjunction: at every coupling `β` the norm of the mode expansion tends to
`0` along `atTop`; at every `β`, `M.μ β - M.κ < 0`; and `M.R d = M.R d'` for all directions `d, d'`.
The proof applies `existence_and_gap_from_apriori` to `M.s, M.P, M.m, M.κ₀, M.κ, M.μ, M.R, M.hfloor`,
the two hypotheses, and `M.hread`.

Scope: the first component is convergence to zero with no rate attached; the rate at a fixed
coupling is `mass_gap_rate_of_model`. `A1_YM M` and `A2_YM M` are hypotheses here.

DERIVED: two numerals, both `0` — the limit point in `nhds 0`, and the strict upper bound in
`M.μ β - M.κ < 0`. Neither is a chosen scale. -/
theorem mass_gap_of_model (M : LatticeYM) (h1 : A1_YM M) (h2 : A2_YM M) :
    (∀ β, Filter.Tendsto
        (fun τ => ‖∑ k ∈ M.s β, M.P β k * (M.m β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
      (∀ β, M.μ β - M.κ < 0) ∧
      (∀ d d', M.R d = M.R d') :=
  existence_and_gap_from_apriori M.s M.P M.m M.κ₀ M.κ M.μ M.R M.hfloor h1 h2 M.hread

end MassGap
