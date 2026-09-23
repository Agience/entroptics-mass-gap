import MassGap.CellPerturb

/-!
# MassGap.CellCouple — quadratic-form bounds for a coupling written as a sum over bonds

`CellSpectrum.gap_of_form_perturbation` takes a decoupled `A` with gap `μ` and a residual bound

    hδ : ∀ v, |v ⬝ᵥ (B *ᵥ v) - v ⬝ᵥ (A *ᵥ v)| ≤ δ * (v ⬝ᵥ v)      hδμ : 2 * δ < μ

and gives `B` the gap `μ - 2δ`. This file bounds such residuals when `B - A = ∑ b ∈ s, V b` is a sum
of per-bond matrices, in two families of shapes.

## Absolute bounds: the cost is charged against `v ⬝ᵥ v`

`straddle_form_bound` bounds one bond's form by `2 * |lam| * (v ⬝ᵥ v)`, by `CellPerturb.adj_form_bound`
applied to `(-lam) • Adj jmax`. `dotProduct_sum_mulVec` splits a sum's form into per-bond forms, and
`coupling_form_le_bondCount` sums the per-bond bounds to `s.card * q * (v ⬝ᵥ v)`.
`coupling_form_extensive` is the converse direction: if a single vector lowers every bond's form by
at least `a`, every admissible `δ` satisfies `s.card * a ≤ δ`. `bondCount_lt_of_budget` and
`form_perturbation_reaches_finitely_many` then combine `s.card * a ≤ δ` with `2 * δ < μ` to bound
`s.card` by `μ / (2 * a)` when `0 < a`. `gap_of_bond_coupling` is
`gap_of_form_perturbation` with the residual supplied by `coupling_form_le_bondCount`.

## Relative bounds: the cost is charged against a local part

`relative_coupling_form_sum` sums per-bond bounds of the form `-c * (v ⬝ᵥ (A b *ᵥ v)) ≤ v ⬝ᵥ (V b *ᵥ v)`
with the same `c` on both sides, so no `s.card` appears. `relative_of_absolute_form_bound` converts an
absolute cost `q` plus a margin `m` into such a bound at `c = q / m`; `relative_of_local_bound` does
the same charging against an arbitrary nominated quantity `loc`. `relative_sum_of_absolute_bonds` and
`relative_sum_of_local_bonds` are the summed forms, `relative_of_dominated_locals` transports a bound
against `∑ A b` to one against a dominating `Afull`, and `relative_full_of_absolute_bonds` /
`relative_full_of_local_bonds` compose the two. `gap_of_relative_bonds` feeds the result to
`CellSpectrum.coupled_gap_of_relative_coupling_bound`, concluding the gap `(1 - q / m) * mform`.

`shared_locals_force_shrinking_margin` is the constraint on the relative route: if every bond is
charged against the SAME local part `A₀` and the sum is dominated by an `Afull` of form at most
`M * (v ⬝ᵥ v)`, then `s.card * m ≤ M`, so a uniform `m` shrinks like `1 / s.card`.

## The chain instance

`flux2` is the two-state flux label, `bondCouple N a b` the diagonal cross term `-a * flux * flux` on
bond `b` of a chain of `N + 1` cells, and `allExc N` the all-excited configuration.
`bondCouple_form` evaluates one bond's form at that configuration to `-a`, `chain_coupling_extensive`
concludes `N * a ≤ δ` for any `δ` bounding the summed form, and `chain_budget_fails` combines that
with `form_perturbation_reaches_finitely_many`.

Scope: everything here is about quadratic forms of real matrices at a single vector or on a
subspace; no operator norms, spectra or eigenvalues appear except in `gap_of_relative_bonds` and
`gap_of_bond_coupling`, which pass them straight to `CellSpectrum`. The identification of `V b` with
a straddling plaquette's magnetic term is a reading, not a theorem here: the matrices are arguments.
In `relative_full_of_local_bonds` and `relative_full_of_absolute_bonds` the apportionment
`∑ A b ≤ Afull` is a hypothesis.
-/

namespace MassGap.CellEnclosure

open scoped Matrix
open Matrix

/-! ### One bond: an absolute form bound from `CellPerturb.adj_form_bound` -/

/-- `|v ⬝ᵥ (((-lam) • Adj jmax) *ᵥ v)| ≤ 2 * |lam| * (v ⬝ᵥ v)` for any real `lam` and any vector.
The scalar is pulled out of the form, and `CellPerturb.adj_form_bound` — AM–GM against the row and
column sums of the `0`/`1` path-graph adjacency — supplies the remaining factor.

Scope: `lam` is unconstrained in sign, and the bound uses no spectral information about `Adj jmax`.
This is one matrix, not a sum.

DERIVED: `2` is `adj_form_bound`'s own constant, the maximum degree of the path-graph adjacency —
two neighbours per interior vertex. -/
theorem straddle_form_bound (jmax : ℕ) (lam : ℝ) (v : Fin (dim jmax) → ℝ) :
    |v ⬝ᵥ (((-lam) • Adj jmax) *ᵥ v)| ≤ 2 * |lam| * (v ⬝ᵥ v) := by
  have hvv : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  have hsm : v ⬝ᵥ (((-lam) • Adj jmax) *ᵥ v) = (-lam) * (v ⬝ᵥ (Adj jmax *ᵥ v)) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  rw [hsm, abs_mul, abs_neg]
  have hb := adj_form_bound jmax v
  nlinarith [abs_nonneg lam, abs_nonneg (v ⬝ᵥ (Adj jmax *ᵥ v))]

/-! ### Sums over bonds: the upper bound, and when it is attained -/

section BondDecomposition

variable {ι : Type*} [Fintype ι] {β : Type*} [DecidableEq β]

/-- `v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v) = ∑ b ∈ s, v ⬝ᵥ (V b *ᵥ v)`: the quadratic form is additive in the
matrix. Proved by induction on the `Finset`, using `Matrix.add_mulVec` and `dotProduct_add`.

DERIVED: no numeral appears in the statement. -/
theorem dotProduct_sum_mulVec (s : Finset β) (V : β → Matrix ι ι ℝ) (v : ι → ℝ) :
    v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v) = ∑ b ∈ s, v ⬝ᵥ (V b *ᵥ v) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro b s' hb ih
    rw [Finset.sum_insert hb, Matrix.add_mulVec, dotProduct_add, ih, Finset.sum_insert hb]

/-- If `|v ⬝ᵥ (V b *ᵥ v)| ≤ q * (v ⬝ᵥ v)` at every `b ∈ s`, then
`|v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v)| ≤ s.card * q * (v ⬝ᵥ v)`. The form is split by
`dotProduct_sum_mulVec`, the triangle inequality applied, and the constant sum evaluated.

Scope: the bound is proportional to the number of bonds. `coupling_form_extensive` gives the
matching lower bound when one vector is extremal on every bond at once.

DERIVED: no numeral appears in the statement; `s.card` is the bond count and `q` the caller's
per-bond cost. -/
theorem coupling_form_le_bondCount (s : Finset β) (V : β → Matrix ι ι ℝ) (q : ℝ) (v : ι → ℝ)
    (hq : ∀ b ∈ s, |v ⬝ᵥ (V b *ᵥ v)| ≤ q * (v ⬝ᵥ v)) :
    |v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v)| ≤ (s.card : ℝ) * q * (v ⬝ᵥ v) := by
  rw [dotProduct_sum_mulVec]
  calc |∑ b ∈ s, v ⬝ᵥ (V b *ᵥ v)|
      ≤ ∑ b ∈ s, |v ⬝ᵥ (V b *ᵥ v)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b ∈ s, q * (v ⬝ᵥ v) := Finset.sum_le_sum hq
    _ = (s.card : ℝ) * q * (v ⬝ᵥ v) := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- Given a single vector `v` with `0 < v ⬝ᵥ v` such that `v ⬝ᵥ (V b *ᵥ v) ≤ -a * (v ⬝ᵥ v)` at every
`b ∈ s`, any `δ` with `|v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v)| ≤ δ * (v ⬝ᵥ v)` satisfies `s.card * a ≤ δ`. The
per-bond bounds sum to `-(s.card * a * (v ⬝ᵥ v))`, which `neg_le_abs` compares with the assumed
bound; dividing by `v ⬝ᵥ v` finishes.

Scope: `a` is not assumed nonnegative — at a negative `a` both hypothesis and conclusion weaken
together. The hypothesis needs ONE vector extremal on every bond simultaneously, which a coupling
diagonal in a product basis has and `bondCouple_form` supplies for the chain.

DERIVED: `0` is the strict lower bound on `v ⬝ᵥ v`, required so it can be divided out. -/
theorem coupling_form_extensive (s : Finset β) (V : β → Matrix ι ι ℝ) {a δ : ℝ}
    (v : ι → ℝ) (hv : 0 < v ⬝ᵥ v)
    (hbond : ∀ b ∈ s, v ⬝ᵥ (V b *ᵥ v) ≤ -a * (v ⬝ᵥ v))
    (hδ : |v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v)| ≤ δ * (v ⬝ᵥ v)) :
    (s.card : ℝ) * a ≤ δ := by
  rw [dotProduct_sum_mulVec] at hδ
  have hsum : ∑ b ∈ s, v ⬝ᵥ (V b *ᵥ v) ≤ -((s.card : ℝ) * a * (v ⬝ᵥ v)) := by
    calc ∑ b ∈ s, v ⬝ᵥ (V b *ᵥ v)
        ≤ ∑ _b ∈ s, -a * (v ⬝ᵥ v) := Finset.sum_le_sum hbond
      _ = -((s.card : ℝ) * a * (v ⬝ᵥ v)) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hneg := neg_le_abs (∑ b ∈ s, v ⬝ᵥ (V b *ᵥ v))
  have h2 : (s.card : ℝ) * a * (v ⬝ᵥ v) ≤ δ * (v ⬝ᵥ v) := by linarith
  exact le_of_mul_le_mul_right h2 hv

/-- If `-c * (v ⬝ᵥ (A b *ᵥ v)) ≤ v ⬝ᵥ (V b *ᵥ v)` at every `b ∈ s`, then
`-c * (v ⬝ᵥ ((∑ b ∈ s, A b) *ᵥ v)) ≤ v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v)`. Both sides are split by
`dotProduct_sum_mulVec` and the per-bond inequalities added.

The same `c` appears on both sides and `s.card` does not occur, because each bond's cost is charged
against its own `A b` rather than against a quantity shared between bonds.

Scope: the sign of `c` is not used; the inequality is summed as given. The `A b` are arbitrary
matrices supplied by the caller.

DERIVED: no numeral appears in the statement. -/
theorem relative_coupling_form_sum (s : Finset β) (V A : β → Matrix ι ι ℝ) {c : ℝ} (v : ι → ℝ)
    (hrel : ∀ b ∈ s, -c * (v ⬝ᵥ (A b *ᵥ v)) ≤ v ⬝ᵥ (V b *ᵥ v)) :
    -c * (v ⬝ᵥ ((∑ b ∈ s, A b) *ᵥ v)) ≤ v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v) := by
  rw [dotProduct_sum_mulVec, dotProduct_sum_mulVec, Finset.mul_sum]
  exact Finset.sum_le_sum hrel

#print axioms relative_coupling_form_sum

/-- From an absolute bound `|v ⬝ᵥ (V *ᵥ v)| ≤ q * (v ⬝ᵥ v)` with `0 ≤ q`, and a margin
`m * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)` with `0 < m`, it follows that
`-(q / m) * (v ⬝ᵥ (A *ᵥ v)) ≤ v ⬝ᵥ (V *ᵥ v)`. The coefficient `-(q / m)` is nonpositive, so applying
it to the margin reverses that inequality, and the result is exactly the lower half of the absolute
bound.

`straddle_form_bound` is one source of `q`; `CellSpectrum.diag_form_margin` is one source of `m`.
Both are hypotheses here.

DERIVED: `0` occurs twice, as the lower bound on the cost `q` and the strict lower bound on the
margin `m`; the latter is what allows division by `m`. The constant `q / m` is the ratio of the two
supplied quantities. -/
theorem relative_of_absolute_form_bound {V A : Matrix ι ι ℝ} {q m : ℝ} (hq : 0 ≤ q)
    (hm : 0 < m) (v : ι → ℝ)
    (habs : |v ⬝ᵥ (V *ᵥ v)| ≤ q * (v ⬝ᵥ v))
    (hA : m * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)) :
    -(q / m) * (v ⬝ᵥ (A *ᵥ v)) ≤ v ⬝ᵥ (V *ᵥ v) := by
  have hlow := (abs_le.mp habs).1
  have hcoef : -(q / m) ≤ 0 := neg_nonpos.mpr (div_nonneg hq hm.le)
  have hstep : -(q / m) * (v ⬝ᵥ (A *ᵥ v)) ≤ -(q / m) * (m * (v ⬝ᵥ v)) :=
    mul_le_mul_of_nonpos_left hA hcoef
  have heq : -(q / m) * (m * (v ⬝ᵥ v)) = -(q * (v ⬝ᵥ v)) := by
    field_simp
  rw [heq] at hstep
  linarith

#print axioms relative_of_absolute_form_bound

/-- `relative_of_absolute_form_bound` with `v ⬝ᵥ v` replaced by an arbitrary real `loc`: from
`|v ⬝ᵥ (V *ᵥ v)| ≤ q * loc` with `0 ≤ q`, and `δ * loc ≤ v ⬝ᵥ (A *ᵥ v)` with `0 < δ`, it follows that
`-(q / δ) * (v ⬝ᵥ (A *ᵥ v)) ≤ v ⬝ᵥ (V *ᵥ v)`.

The proof never uses what `loc` is, so the caller may nominate any quantity — for instance the mass
carried on one bond's own links, which lets the cost vanish where that mass does. A bound charged
against a shared quantity is the case `shared_locals_force_shrinking_margin` constrains.

Scope: `loc` is unconstrained, including in sign.

DERIVED: `0` occurs twice, as the lower bound on the cost `q` and the strict lower bound on the
margin `δ`, the latter allowing division by `δ`. -/
theorem relative_of_local_bound {V A : Matrix ι ι ℝ} {q δ loc : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ)
    (v : ι → ℝ)
    (habs : |v ⬝ᵥ (V *ᵥ v)| ≤ q * loc)
    (hA : δ * loc ≤ v ⬝ᵥ (A *ᵥ v)) :
    -(q / δ) * (v ⬝ᵥ (A *ᵥ v)) ≤ v ⬝ᵥ (V *ᵥ v) := by
  have hlow := (abs_le.mp habs).1
  have hcoef : -(q / δ) ≤ 0 := neg_nonpos.mpr (div_nonneg hq hδ.le)
  have hstep : -(q / δ) * (v ⬝ᵥ (A *ᵥ v)) ≤ -(q / δ) * (δ * loc) :=
    mul_le_mul_of_nonpos_left hA hcoef
  have heq : -(q / δ) * (δ * loc) = -(q * loc) := by
    field_simp
  rw [heq] at hstep
  linarith

#print axioms relative_of_local_bound

/-- With a per-bond quantity `loc : β → ℝ`, given `|v ⬝ᵥ (V b *ᵥ v)| ≤ q * loc b` and
`δ * loc b ≤ v ⬝ᵥ (A b *ᵥ v)` at every `b ∈ s`, with `0 ≤ q` and `0 < δ`, the summed bound is
`-(q / δ) * (v ⬝ᵥ ((∑ b ∈ s, A b) *ᵥ v)) ≤ v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v)`. It is
`relative_of_local_bound` per bond, summed by `relative_coupling_form_sum`.

`s.card` does not appear, and the `loc b` may differ from bond to bond — the case
`shared_locals_force_shrinking_margin` leaves open.

DERIVED: `0` occurs twice, as the lower bound on `q` and the strict lower bound on `δ`. -/
theorem relative_sum_of_local_bonds (s : Finset β) (V A : β → Matrix ι ι ℝ) (loc : β → ℝ)
    {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ) (v : ι → ℝ)
    (habs : ∀ b ∈ s, |v ⬝ᵥ (V b *ᵥ v)| ≤ q * loc b)
    (hmar : ∀ b ∈ s, δ * loc b ≤ v ⬝ᵥ (A b *ᵥ v)) :
    -(q / δ) * (v ⬝ᵥ ((∑ b ∈ s, A b) *ᵥ v)) ≤ v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v) :=
  relative_coupling_form_sum s V A v
    (fun b hb => relative_of_local_bound hq hδ v (habs b hb) (hmar b hb))

#print axioms relative_sum_of_local_bonds


/-- From the same per-bond costs `coupling_form_le_bondCount` consumes — `|v ⬝ᵥ (V b *ᵥ v)| ≤ q * (v ⬝ᵥ v)`
with `0 ≤ q` — together with per-bond margins `m * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A b *ᵥ v)` with `0 < m`, the
summed bound is

    -(q / m) * (v ⬝ᵥ ((∑ b ∈ s, A b) *ᵥ v)) ≤ v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v).

It is `relative_of_absolute_form_bound` per bond, summed by `relative_coupling_form_sum`. `s.card`
does not appear; the difference from `coupling_form_le_bondCount` is what the cost is charged
against.

Scope: here every bond's margin is against the same `v ⬝ᵥ v`, which is the hypothesis shape
`shared_locals_force_shrinking_margin` constrains. The `A b` are whatever matrices the caller
supplies; nothing here identifies them with the local parts of a particular operator, and nothing
here proves `∑ b ∈ s, A b` is dominated by any full operator.

DERIVED: `0` occurs twice, as the lower bound on the cost `q` and the strict lower bound on the
margin `m`. -/
theorem relative_sum_of_absolute_bonds (s : Finset β) (V A : β → Matrix ι ι ℝ) {q m : ℝ}
    (hq : 0 ≤ q) (hm : 0 < m) (v : ι → ℝ)
    (habs : ∀ b ∈ s, |v ⬝ᵥ (V b *ᵥ v)| ≤ q * (v ⬝ᵥ v))
    (hmar : ∀ b ∈ s, m * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A b *ᵥ v)) :
    -(q / m) * (v ⬝ᵥ ((∑ b ∈ s, A b) *ᵥ v)) ≤ v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v) :=
  relative_coupling_form_sum s V A v
    (fun b hb => relative_of_absolute_form_bound hq hm v (habs b hb) (hmar b hb))

#print axioms relative_sum_of_absolute_bonds

/-- Given `0 ≤ c`, a relative bound `-c * (v ⬝ᵥ (Aloc *ᵥ v)) ≤ v ⬝ᵥ (V *ᵥ v)` and a domination
`v ⬝ᵥ (Aloc *ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)`, it follows that `-c * (v ⬝ᵥ (A *ᵥ v)) ≤ v ⬝ᵥ (V *ᵥ v)`. The
coefficient `-c` is nonpositive, so domination moves the left side down and the inequality survives.

Scope: `hdom` is a hypothesis at the single vector `v`. Nothing here constructs `Aloc` or proves it
is dominated by `A`; for a physical coupling that would be an apportionment of each link's energy
among the plaquettes containing it.

DERIVED: `0` is the lower bound on `c`, which is what makes the coefficient nonpositive and so fixes
the direction of the final step. -/
theorem relative_of_dominated_locals {V A Aloc : Matrix ι ι ℝ} {c : ℝ} (hc : 0 ≤ c) (v : ι → ℝ)
    (hrel : -c * (v ⬝ᵥ (Aloc *ᵥ v)) ≤ v ⬝ᵥ (V *ᵥ v))
    (hdom : v ⬝ᵥ (Aloc *ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)) :
    -c * (v ⬝ᵥ (A *ᵥ v)) ≤ v ⬝ᵥ (V *ᵥ v) := by
  have hstep : -c * (v ⬝ᵥ (A *ᵥ v)) ≤ -c * (v ⬝ᵥ (Aloc *ᵥ v)) :=
    mul_le_mul_of_nonpos_left hdom (neg_nonpos.mpr hc)
  linarith

#print axioms relative_of_dominated_locals

/-- `relative_sum_of_local_bonds` followed by `relative_of_dominated_locals`: with per-bond costs
`q * loc b`, per-bond margins `δ * loc b`, `0 ≤ q`, `0 < δ`, and the domination
`v ⬝ᵥ ((∑ b ∈ s, A b) *ᵥ v) ≤ v ⬝ᵥ (Afull *ᵥ v)`, the conclusion is
`-(q / δ) * (v ⬝ᵥ (Afull *ᵥ v)) ≤ v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v)`.

The constant is `q / δ` and carries no bond count. `CellSpectrum.coupled_gap_of_relative_coupling_bound`
consumes a bound of exactly this shape.

Scope: `loc`, the `A b` and `Afull` are all the caller's, and the domination `hdom` is a hypothesis
at the single vector `v`.

DERIVED: `0` occurs twice, as the lower bound on `q` and the strict lower bound on `δ`. -/
theorem relative_full_of_local_bonds (s : Finset β) (V A : β → Matrix ι ι ℝ) (loc : β → ℝ)
    (Afull : Matrix ι ι ℝ) {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ) (v : ι → ℝ)
    (habs : ∀ b ∈ s, |v ⬝ᵥ (V b *ᵥ v)| ≤ q * loc b)
    (hmar : ∀ b ∈ s, δ * loc b ≤ v ⬝ᵥ (A b *ᵥ v))
    (hdom : v ⬝ᵥ ((∑ b ∈ s, A b) *ᵥ v) ≤ v ⬝ᵥ (Afull *ᵥ v)) :
    -(q / δ) * (v ⬝ᵥ (Afull *ᵥ v)) ≤ v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v) :=
  relative_of_dominated_locals (div_nonneg hq hδ.le) v
    (relative_sum_of_local_bonds s V A loc hq hδ v habs hmar) hdom

#print axioms relative_full_of_local_bonds

/-- `relative_sum_of_absolute_bonds` followed by `relative_of_dominated_locals`: with per-bond costs
`q * (v ⬝ᵥ v)`, per-bond margins `m * (v ⬝ᵥ v)`, `0 ≤ q`, `0 < m`, and the domination
`v ⬝ᵥ ((∑ b ∈ s, A b) *ᵥ v) ≤ v ⬝ᵥ (Afull *ᵥ v)`, the conclusion is
`-(q / m) * (v ⬝ᵥ (Afull *ᵥ v)) ≤ v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v)`.

Neither the statement nor the proof mentions `s.card`. It is the input
`CellSpectrum.coupled_gap_of_relative_coupling_bound` takes, and `gap_of_relative_bonds` makes that
composition.

Scope: every bond's margin is against the same `v ⬝ᵥ v`, the case
`shared_locals_force_shrinking_margin` constrains. `hdom` is a hypothesis at the single vector `v`.

DERIVED: `0` occurs twice, as the lower bound on `q` and the strict lower bound on `m`. -/
theorem relative_full_of_absolute_bonds (s : Finset β) (V A : β → Matrix ι ι ℝ)
    (Afull : Matrix ι ι ℝ) {q m : ℝ} (hq : 0 ≤ q) (hm : 0 < m) (v : ι → ℝ)
    (habs : ∀ b ∈ s, |v ⬝ᵥ (V b *ᵥ v)| ≤ q * (v ⬝ᵥ v))
    (hmar : ∀ b ∈ s, m * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A b *ᵥ v))
    (hdom : v ⬝ᵥ ((∑ b ∈ s, A b) *ᵥ v) ≤ v ⬝ᵥ (Afull *ᵥ v)) :
    -(q / m) * (v ⬝ᵥ (Afull *ᵥ v)) ≤ v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v) :=
  relative_of_dominated_locals (div_nonneg hq hm.le) v
    (relative_sum_of_absolute_bonds s V A hq hm v habs hmar) hdom

#print axioms relative_full_of_absolute_bonds

/-- Suppose every bond is charged against the SAME local part `A₀`: `m * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A₀ *ᵥ v)`,
the constant sum `∑ _b ∈ s, A₀` is dominated in form by `Afull`, and `v ⬝ᵥ (Afull *ᵥ v) ≤ M * (v ⬝ᵥ v)`.
Then `s.card * m ≤ M`. The constant sum evaluates to `s.card` copies of `A₀`'s form, and dividing by
`0 < v ⬝ᵥ v` gives the bound.

So a uniform margin over bonds sharing one local part is at most `M / s.card`, and `q / m` in
`relative_sum_of_absolute_bonds` then grows with the bond count. The hypotheses of the relative route
are satisfiable at a bond-count-independent `q / m` only when the local parts differ between bonds,
which is the case `relative_sum_of_local_bonds` covers.

DERIVED: `0` is the strict lower bound on `v ⬝ᵥ v`, required so it can be divided out. -/
theorem shared_locals_force_shrinking_margin (s : Finset β) (A₀ Afull : Matrix ι ι ℝ) {m M : ℝ}
    (v : ι → ℝ) (hv : 0 < v ⬝ᵥ v)
    (hmar : m * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A₀ *ᵥ v))
    (hdom : v ⬝ᵥ ((∑ _b ∈ s, A₀) *ᵥ v) ≤ v ⬝ᵥ (Afull *ᵥ v))
    (hfull : v ⬝ᵥ (Afull *ᵥ v) ≤ M * (v ⬝ᵥ v)) :
    (s.card : ℝ) * m ≤ M := by
  rw [dotProduct_sum_mulVec, Finset.sum_const, nsmul_eq_mul] at hdom
  have hcard : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
  have hstep : (s.card : ℝ) * (m * (v ⬝ᵥ v)) ≤ (s.card : ℝ) * (v ⬝ᵥ (A₀ *ᵥ v)) :=
    mul_le_mul_of_nonneg_left hmar hcard
  have h2 : (s.card : ℝ) * m * (v ⬝ᵥ v) ≤ M * (v ⬝ᵥ v) := by nlinarith
  exact le_of_mul_le_mul_right h2 hv

#print axioms shared_locals_force_shrinking_margin

/-- `CellSpectrum.coupled_gap_of_relative_coupling_bound` with its coupling bound supplied by
`relative_full_of_absolute_bonds`. Given per-bond costs `q` and margins `m` on a subspace `W` of
codimension at most one, a form floor `mform` for `H₀` on `W`, the domination
`∑ b ∈ s, A b ≤ H₀` on `W`, `0 ≤ q`, `0 < m`, `q / m < 1` and `0 < (1 - q / m) * mform`, the
Hermitian `H₀ + ∑ b ∈ s, V b` satisfies
`(1 - q / m) * mform ≤ hH.eigenvalues i - hH.eigenvalues i₀` for every `i ≠ i₀`, where `i₀` indexes a
nonpositive eigenvalue.

The bond set appears in the hypotheses and not in the conclusion's constant.

Scope: `hmar` requires the margin `m` against the same `x ⬝ᵥ x` at every bond, which is the shape
`shared_locals_force_shrinking_margin` bounds by `M / s.card` when the local parts coincide. The
subspace condition `N ≤ Module.finrank ℝ W + 1` and the existence of a nonpositive eigenvalue are
hypotheses.

DERIVED: `0` occurs four times — the lower bound on `q`, the strict lower bound on `m`, the strict
lower bound on the gap `(1 - q / m) * mform`, and the upper bound on the eigenvalue at `i₀`. `1`
occurs four times — the threshold `q / m < 1`, the `1 -` in the gap hypothesis, the `+ 1` in the
codimension condition, and the `1 -` in the conclusion; all four are
`coupled_gap_of_relative_coupling_bound`'s own. -/
theorem gap_of_relative_bonds {N : ℕ} (s : Finset β) (V A : β → Matrix (Fin N) (Fin N) ℝ)
    (H₀ : Matrix (Fin N) (Fin N) ℝ) (hH : (H₀ + ∑ b ∈ s, V b).IsHermitian)
    {q m mform : ℝ} (hq : 0 ≤ q) (hm : 0 < m) (hlt : q / m < 1)
    (hgap : 0 < (1 - q / m) * mform)
    (W : Submodule ℝ (Fin N → ℝ)) (hW : N ≤ Module.finrank ℝ W + 1)
    (hform0 : ∀ x ∈ W, mform * (x ⬝ᵥ x) ≤ x ⬝ᵥ (H₀ *ᵥ x))
    (habs : ∀ x ∈ W, ∀ b ∈ s, |x ⬝ᵥ (V b *ᵥ x)| ≤ q * (x ⬝ᵥ x))
    (hmar : ∀ x ∈ W, ∀ b ∈ s, m * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A b *ᵥ x))
    (hdom : ∀ x ∈ W, x ⬝ᵥ ((∑ b ∈ s, A b) *ᵥ x) ≤ x ⬝ᵥ (H₀ *ᵥ x))
    {i₀ : Fin N} (hi₀ : hH.eigenvalues i₀ ≤ 0) {i : Fin N} (hi : i ≠ i₀) :
    (1 - q / m) * mform ≤ hH.eigenvalues i - hH.eigenvalues i₀ :=
  coupled_gap_of_relative_coupling_bound H₀ (∑ b ∈ s, V b) hH hlt hgap W hW hform0
    (fun x hx => relative_full_of_absolute_bonds s V A H₀ hq hm x (habs x hx) (hmar x hx) (hdom x hx))
    hi₀ hi

#print axioms gap_of_relative_bonds




end BondDecomposition

/-! ### Combining an extensive lower bound on `δ` with the budget `2 * δ < μ` -/

/-- For `0 < a`, `n * a ≤ δ` and `2 * δ < μ`, it follows that `(n : ℝ) < μ / (2 * a)`. Multiplying
out the division by the positive `2 * a` reduces it to `2 * (n * a) ≤ 2 * δ < μ`.

Scope: `0 < a` is required — at `a = 0` the hypothesis `n * a ≤ δ` constrains nothing and the
division is undefined. This is arithmetic on the two hypotheses; no matrix or lattice appears.

DERIVED: `0` is the strict lower bound on `a`; `2` occurs twice, as the factor in the budget
`2 * δ < μ` and in the resulting divisor `2 * a`, both inherited from
`CellSpectrum.gap_of_form_perturbation`'s hypothesis shape. -/
theorem bondCount_lt_of_budget {n : ℕ} {a δ μ : ℝ} (ha : 0 < a)
    (hext : (n : ℝ) * a ≤ δ) (hbud : 2 * δ < μ) : (n : ℝ) < μ / (2 * a) := by
  have h : (n : ℝ) * (2 * a) = 2 * ((n : ℝ) * a) := by ring
  rw [lt_div_iff₀ (by linarith : (0 : ℝ) < 2 * a), h]
  linarith

/-- For every real `μ` and every `a` with `0 < a`, there is an `N₀ : ℕ` such that for all `n ≥ N₀`
and every `δ` with `n * a ≤ δ`, the budget `2 * δ < μ` fails. `N₀` is any natural above
`μ / (2 * a)`, and `bondCount_lt_of_budget` supplies the contradiction.

Scope: a statement about the two numerical hypotheses; it says nothing about any operator's
spectrum. `0 < a` is required, and `μ` is unconstrained in sign.

DERIVED: `0` is the strict lower bound on `a`; `2` is the factor in the budget `2 * δ < μ`,
inherited from `CellSpectrum.gap_of_form_perturbation`. -/
theorem form_perturbation_reaches_finitely_many (a μ : ℝ) (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ δ : ℝ, (n : ℝ) * a ≤ δ → ¬ (2 * δ < μ) := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (μ / (2 * a))
  refine ⟨N₀, fun n hn δ hδ hbud => ?_⟩
  have hlt := bondCount_lt_of_budget ha hδ hbud
  have hcast : (N₀ : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  linarith

/-! ### A chain instance satisfying the extensive lower bound

`N + 1` two-state cells in a row — the `j = 0, 1/2` truncation `CellSpectrum.Hcell2` uses — with a
diagonal cross term on each of the `N` bonds. The all-excited configuration is extremal on every bond
at once, which is the hypothesis `coupling_form_extensive` consumes. -/

/-- `flux2 : Fin 2 → ℝ`, sending index `0` to `0` and index `1` to `1`: the flux label of a two-state
cell, `0` at the vacuum `j = 0` and `1` at the excited `j = 1/2`.

DERIVED: `2` is the number of states in the truncation, the size of the index type; the index `0` is
the vacuum state and its value `0` the vacuum flux; `1` is the flux at the other state. These are the
character indices themselves, not a parametrisation. -/
def flux2 : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1

lemma flux2_one : flux2 1 = 1 := by
  unfold flux2
  rw [if_neg (by decide : ¬ ((1 : Fin 2) = 0))]

/-- The diagonal matrix on configurations `Fin (N + 1) → Fin 2` whose entry at `s` is
`-a * (flux2 (s b.castSucc) * flux2 (s b.succ))`: the cross term on bond `b`, coupling the two cells
it joins through their fluxes.

The shape is that of a shared link's electric cross term: a link carried by two neighbouring cells
contributes `(n_c - n_{c+1}) ^ 2 = n_c ^ 2 + n_{c+1} ^ 2 - 2 * n_c * n_{c+1}`, whose squares are
one-cell and belong to the decoupled part, leaving `-2 * n_c * n_{c+1}`. The depth `a` carries that
factor together with the electric scale, so no unit is fixed here.

Scope: the matrix is diagonal, so every configuration is an eigenvector and `bondCouple_form`
evaluates its form exactly.

DERIVED: `2` occurs twice, as the two-state truncation `Fin 2` in the domain and codomain of a
configuration; `1` occurs twice, as the `+ 1` in the cell count `Fin (N + 1)` in each of those, which
makes `N` bonds join `N + 1` cells. -/
noncomputable def bondCouple (N : ℕ) (a : ℝ) (b : Fin N) :
    Matrix (Fin (N + 1) → Fin 2) (Fin (N + 1) → Fin 2) ℝ :=
  Matrix.diagonal fun s => -a * (flux2 (s b.castSucc) * flux2 (s b.succ))

/-- The configuration `fun _ => 1` on `Fin (N + 1) → Fin 2`: every cell at the excited state. Since
each bond term is a product of two fluxes and `flux2` is largest at index `1`, this configuration is
extremal on every bond at once, which is what `coupling_form_extensive` requires of a single vector.

DERIVED: `1` is the excited index every cell is put at; `1` also appears as the `+ 1` in the cell
count `Fin (N + 1)`, and `2` is the size of the two-state truncation. -/
def allExc (N : ℕ) : Fin (N + 1) → Fin 2 := fun _ => 1

lemma single_dotProduct_self {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι) :
    (Pi.single x (1 : ℝ)) ⬝ᵥ (Pi.single x (1 : ℝ)) = 1 := by
  simp only [dotProduct]
  rw [Finset.sum_eq_single x
    (fun i _ hi => by rw [Pi.single_eq_of_ne hi]; ring)
    (fun h => absurd (Finset.mem_univ x) h)]
  rw [Pi.single_eq_same]; norm_num

lemma single_diagonal_form {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) (x : ι) :
    (Pi.single x (1 : ℝ)) ⬝ᵥ (Matrix.diagonal d *ᵥ (Pi.single x (1 : ℝ))) = d x := by
  simp only [dotProduct]
  rw [Finset.sum_eq_single x
    (fun i _ hi => by rw [Matrix.mulVec_diagonal, Pi.single_eq_of_ne hi]; ring)
    (fun h => absurd (Finset.mem_univ x) h)]
  rw [Matrix.mulVec_diagonal, Pi.single_eq_same]; ring

/-- `(Pi.single (allExc N) 1) ⬝ᵥ (bondCouple N a b *ᵥ (Pi.single (allExc N) 1)) = -a` at every bond
`b`. `single_diagonal_form` reads off the diagonal entry at `allExc N`, where both fluxes are `1` by
`flux2_one`, leaving `-a * (1 * 1)`.

The value does not depend on `b`, which is what makes the configuration extremal on every bond
simultaneously.

DERIVED: `1` occurs twice, as the scalar of the basis vector `Pi.single (allExc N) 1` on each side of
the quadratic form. -/
theorem bondCouple_form (N : ℕ) (a : ℝ) (b : Fin N) :
    (Pi.single (allExc N) (1 : ℝ)) ⬝ᵥ
        (bondCouple N a b *ᵥ (Pi.single (allExc N) (1 : ℝ))) = -a := by
  rw [bondCouple, single_diagonal_form]
  simp only [allExc, flux2_one]
  ring

/-- If `δ` bounds the summed coupling's form at every vector —
`|v ⬝ᵥ ((∑ b : Fin N, bondCouple N a b) *ᵥ v)| ≤ δ * (v ⬝ᵥ v)` — then `(N : ℝ) * a ≤ δ`. It is
`coupling_form_extensive` at the vector `Pi.single (allExc N) 1`, whose own form is `1` by
`single_dotProduct_self` and which lowers every bond by exactly `a` by `bondCouple_form`.

Scope: no hypothesis on the sign of `a` or `δ`. The hypothesis `hδ` is required at every vector, but
only one is used.

DERIVED: `1` is the `+ 1` in the cell count `Fin (N + 1)`; `2` is the size of the two-state
truncation `Fin 2`. -/
theorem chain_coupling_extensive (N : ℕ) {a δ : ℝ}
    (hδ : ∀ v : (Fin (N + 1) → Fin 2) → ℝ,
      |v ⬝ᵥ ((∑ b : Fin N, bondCouple N a b) *ᵥ v)| ≤ δ * (v ⬝ᵥ v)) :
    (N : ℝ) * a ≤ δ := by
  have hself := single_dotProduct_self (allExc N)
  have h := coupling_form_extensive (a := a) (δ := δ) (Finset.univ : Finset (Fin N)) (bondCouple N a)
    (Pi.single (allExc N) (1 : ℝ)) (by rw [hself]; norm_num)
    (fun b _ => by rw [bondCouple_form, hself]; linarith)
    (hδ _)
  simpa using h

/-- For every real `μ` and every `a` with `0 < a`, there is an `N₀ : ℕ` such that for all `N ≥ N₀`,
no `δ` bounding the chain coupling's form at every vector satisfies `2 * δ < μ`. It composes
`chain_coupling_extensive` with `form_perturbation_reaches_finitely_many`.

Scope: the conclusion is about the hypothesis `2 * δ < μ` of
`CellSpectrum.gap_of_form_perturbation` for this particular coupling; it makes no statement about the
spectrum of the coupled operator.

DERIVED: `0` is the strict lower bound on `a`; `1` is the `+ 1` in the cell count `Fin (N + 1)`; `2`
occurs twice, as the size of the two-state truncation `Fin 2` and as the factor in the budget
`2 * δ < μ`. -/
theorem chain_budget_fails (μ a : ℝ) (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ δ : ℝ,
      (∀ v : (Fin (N + 1) → Fin 2) → ℝ,
        |v ⬝ᵥ ((∑ b : Fin N, bondCouple N a b) *ᵥ v)| ≤ δ * (v ⬝ᵥ v)) → ¬ (2 * δ < μ) := by
  obtain ⟨N₀, hN₀⟩ := form_perturbation_reaches_finitely_many a μ ha
  exact ⟨N₀, fun N hN δ hδ => hN₀ N hN δ (chain_coupling_extensive N hδ)⟩

/-! ### The gap from the absolute bond bound -/

/-- `CellSpectrum.gap_of_form_perturbation` with its residual supplied by
`coupling_form_le_bondCount`. Given a Hermitian `B` split as `A + ∑ b ∈ s, V b`, per-bond costs
`|v ⬝ᵥ (V b *ᵥ v)| ≤ q * (v ⬝ᵥ v)`, the budget `2 * (s.card * q) < μ`, a form floor `t` for `A` on a
subspace `W` of codimension at most one, and a vector `ψ ≠ 0` with `ψ ⬝ᵥ (A *ᵥ ψ) ≤ (t - μ) * (ψ ⬝ᵥ ψ)`,
there is an index `i₀` with
`hB.eigenvalues i₀ + (μ - 2 * (s.card * q)) ≤ hB.eigenvalues i` for every `i ≠ i₀`.

The gap in the conclusion decreases with the bond count `s.card`, and
`bondCount_lt_of_budget` bounds the `s.card` for which the budget hypothesis can hold.

DERIVED: `2` occurs twice, as the factor in the budget hypothesis and again in the gap
`μ - 2 * (s.card * q)`, both `gap_of_form_perturbation`'s own; `1` is the `+ 1` in the codimension
condition `N ≤ Module.finrank ℝ W + 1`; `0` is the value `ψ` is assumed to differ from. -/
theorem gap_of_bond_coupling {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℝ} (hB : B.IsHermitian)
    {β : Type*} [DecidableEq β] (s : Finset β) (V : β → Matrix (Fin N) (Fin N) ℝ)
    {q t μ : ℝ} (hsplit : B = A + ∑ b ∈ s, V b)
    (hq : ∀ b ∈ s, ∀ v : Fin N → ℝ, |v ⬝ᵥ (V b *ᵥ v)| ≤ q * (v ⬝ᵥ v))
    (hbud : 2 * ((s.card : ℝ) * q) < μ)
    (W : Submodule ℝ (Fin N → ℝ)) (hW : N ≤ Module.finrank ℝ W + 1)
    (hker : ∀ x ∈ W, t * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x))
    (ψ : Fin N → ℝ) (hψ : ψ ≠ 0) (hray : ψ ⬝ᵥ (A *ᵥ ψ) ≤ (t - μ) * (ψ ⬝ᵥ ψ)) :
    ∃ i₀, ∀ i, i ≠ i₀ →
      hB.eigenvalues i₀ + (μ - 2 * ((s.card : ℝ) * q)) ≤ hB.eigenvalues i := by
  refine gap_of_form_perturbation hB hbud (fun v => ?_) W hW hker ψ hψ hray
  have hd : v ⬝ᵥ (B *ᵥ v) - v ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v) := by
    rw [hsplit, Matrix.add_mulVec, dotProduct_add]; ring
  rw [hd]
  exact coupling_form_le_bondCount s V q v (fun b hb => hq b hb v)

#print axioms straddle_form_bound
#print axioms coupling_form_le_bondCount
#print axioms coupling_form_extensive
#print axioms bondCount_lt_of_budget
#print axioms form_perturbation_reaches_finitely_many
#print axioms chain_coupling_extensive
#print axioms chain_budget_fails
#print axioms gap_of_bond_coupling

end MassGap.CellEnclosure
