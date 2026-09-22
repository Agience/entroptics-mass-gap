import MassGap.CellPerturb

/-!
# MassGap.CellCouple — the coupled-cell residual `δ`, and the volume it cannot reach

## The scalar this file is about

`CellSpectrum.gap_of_form_perturbation` reduces "the coupled transfer is gapped" to ONE inequality:
given a decoupled `A` with gap `μ` and

    hδμ : 2 * δ < μ        hδ : ∀ v, |v ⬝ᵥ (B *ᵥ v) - v ⬝ᵥ (A *ᵥ v)| ≤ δ * (v ⬝ᵥ v)

the coupled `B` keeps a gap `μ - 2δ`. Its own docstring says the development does not supply `δ`, and
that "that bound IS the coupled-cell residual". This file supplies it, and the answer is negative for
the volume-uniform statement: `δ` is bounded, by the elementary technique the cell already uses, and
the bound is EXTENSIVE in the number of cells while the budget `μ/2` is a fixed number.

## What the coupling is

Kogut–Susskind is `∑_links E² − λ ∑_plaquettes tr U_p`. Partition the links into cells. The electric
term is one-link, so any such partition decouples it exactly. What is left is the plaquettes whose
four links do not all lie in one cell, and in the character basis `tr U_p` is the nearest-neighbour
hopping on that plaquette's own flux — `CellPerturb.Adj`, the very path-graph adjacency the single
cell is built from. So the residual is

    B − A = −λ ∑_{p straddling} Adj_p ,

a sum of LOCAL terms, one per bond of the cell adjacency graph.

## The two halves, and why they close the question

* `straddle_form_bound`: one straddling plaquette costs `2|λ|` in quadratic form — `adj_form_bound`
  verbatim, the same AM–GM against the row and column sums, no spectral input. So `δ` CAN be bounded
  by that technique. It is not a Weyl inequality and it is not a measurement.
* `coupling_form_le_bondCount`: `n` bonds cost at most `n·q`. That is the whole of what summing gives.
* `coupling_form_extensive`: the summed bound is NOT slack. If one vector lowers every bond by `a`,
  then `δ ≥ n·a` for every admissible `δ`. Attaining the sum needs only a single configuration that
  is extremal on each bond at once, which any diagonal (shared-link) coupling has and a product of
  per-bond extremal states supplies in general.
* `form_perturbation_reaches_finitely_many` / `chain_budget_fails`: `n·a ≤ δ` and `2δ < μ` force
  `n < μ/(2a)`. The bond count is therefore BOUNDED, and a volume-uniform gap needs it unbounded.

So the route closes at a finite volume for every `μ` and every nonzero per-bond depth. That is not a
defect of the bound: `coupling_form_extensive` shows the linear growth is real, not an artifact of the
triangle inequality. What fails is norm perturbation applied to a many-body operator, which is the
classical reason a spectral gap in the volume needs a cluster expansion rather than an operator-norm
estimate — `CellSpectrum.coupling_form_add` already names this and stops one step short of proving it.

`chain_coupling_extensive` makes it non-vacuous on a concrete chain: `N+1` two-state cells with the
shared-link cross term on each of the `N` bonds, where the all-excited configuration is extremal on
every bond simultaneously and `δ ≥ N·a` follows with no hypothesis beyond `a ≥ 0`.

WHAT THIS DOES NOT SAY. It says nothing against the gap itself. `δ` extensive means the METHOD cannot
see the gap, not that the gap is absent; measured on the same chain (`certify/cell_chain_coupling.py`)
the coupled spectral gap stays at the single-cell value while `δ` grows linearly in the cell count.
-/

namespace MassGap.CellEnclosure

open scoped Matrix
open Matrix

/-! ### One bond: the form bound, by the cell's own AM–GM -/

/-- **A straddling plaquette costs `2|λ|` in quadratic form.** The magnetic term of a plaquette whose
links are split between two cells is `−λ · Adj` in the character basis, and `adj_form_bound` — pure
AM–GM against the row and column sums of the 0/1 path-graph adjacency — bounds its form by
`2|λ|‖v‖²`. So the answer to "can `δ` be bounded by the same technique as `CellPerturb`" is yes, per
bond, with the same constant `2` and no spectral input. -/
theorem straddle_form_bound (jmax : ℕ) (lam : ℝ) (v : Fin (dim jmax) → ℝ) :
    |v ⬝ᵥ (((-lam) • Adj jmax) *ᵥ v)| ≤ 2 * |lam| * (v ⬝ᵥ v) := by
  have hvv : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  have hsm : v ⬝ᵥ (((-lam) • Adj jmax) *ᵥ v) = (-lam) * (v ⬝ᵥ (Adj jmax *ᵥ v)) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  rw [hsm, abs_mul, abs_neg]
  have hb := adj_form_bound jmax v
  nlinarith [abs_nonneg lam, abs_nonneg (v ⬝ᵥ (Adj jmax *ᵥ v))]

/-! ### Many bonds: the sum, and that the sum is attained -/

section BondDecomposition

variable {ι : Type*} [Fintype ι] {β : Type*} [DecidableEq β]

/-- The quadratic form of a sum of couplings is the sum of their forms. -/
theorem dotProduct_sum_mulVec (s : Finset β) (V : β → Matrix ι ι ℝ) (v : ι → ℝ) :
    v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v) = ∑ b ∈ s, v ⬝ᵥ (V b *ᵥ v) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro b s' hb ih
    rw [Finset.sum_insert hb, Matrix.add_mulVec, dotProduct_add, ih, Finset.sum_insert hb]

/-- **Upper bound: `n` bonds at form cost `q` each give `δ ≤ n·q`.** The triangle inequality applied
to the bond decomposition — the whole of what the per-bond technique yields at the volume, and the
number `gap_of_form_perturbation` would have to fit inside `μ/2`. -/
theorem coupling_form_le_bondCount (s : Finset β) (V : β → Matrix ι ι ℝ) (q : ℝ) (v : ι → ℝ)
    (hq : ∀ b ∈ s, |v ⬝ᵥ (V b *ᵥ v)| ≤ q * (v ⬝ᵥ v)) :
    |v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v)| ≤ (s.card : ℝ) * q * (v ⬝ᵥ v) := by
  rw [dotProduct_sum_mulVec]
  calc |∑ b ∈ s, v ⬝ᵥ (V b *ᵥ v)|
      ≤ ∑ b ∈ s, |v ⬝ᵥ (V b *ᵥ v)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b ∈ s, q * (v ⬝ᵥ v) := Finset.sum_le_sum hq
    _ = (s.card : ℝ) * q * (v ⬝ᵥ v) := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Lower bound: the summed cost is not slack.** If ONE vector lowers every bond's form by at least
`a`, then every `δ` admissible in `gap_of_form_perturbation`'s `hδ` satisfies `δ ≥ n·a` with `n` the
bond count. So the linear growth in `coupling_form_le_bondCount` is a property of the coupling, not of
the triangle inequality: no sharper form bound can avoid it. `a ≥ 0` is NOT assumed and is not needed:
at a negative depth both the hypothesis and the conclusion weaken together.

A single vector extremal on every bond at once is what a coupling diagonal in a product basis always
has — the shared-link electric term is of that kind — and what a product of per-bond extremal states
supplies whenever the bond terms act on distinct factors, which is the straddling-plaquette case. -/
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

/-- **⭐ THE RELATIVE BOUND DOES NOT COUNT BONDS.** If every bond's coupling is bounded below by
`−c` times the form of its OWN unperturbed part — rather than by `−c` times the global `‖x‖²` — then
the sum obeys the same bound against the summed unperturbed part, **with the same `c`**. There is no
`s.card` on the right.

This is the non-extensive companion of `CellSpectrum.coupling_form_add`, and the contrast is the
point: `coupling_form_le_bondCount` gives `n·q` because each bond is charged against the whole
vector, while here each bond is charged against the energy it sits on and the charges add on both
sides. `coupling_form_extensive` shows the `n·a` growth is real for the ABSOLUTE bound; it says
nothing about this one.

DERIVED: no numeral. The sign of `c` is not used — the inequality sums whatever it is. -/
theorem relative_coupling_form_sum (s : Finset β) (V A : β → Matrix ι ι ℝ) {c : ℝ} (v : ι → ℝ)
    (hrel : ∀ b ∈ s, -c * (v ⬝ᵥ (A b *ᵥ v)) ≤ v ⬝ᵥ (V b *ᵥ v)) :
    -c * (v ⬝ᵥ ((∑ b ∈ s, A b) *ᵥ v)) ≤ v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v) := by
  rw [dotProduct_sum_mulVec, dotProduct_sum_mulVec, Finset.mul_sum]
  exact Finset.sum_le_sum hrel

#print axioms relative_coupling_form_sum

/-- **⭐ AN ABSOLUTE BOND BOUND PLUS A LOCAL MARGIN IS A RELATIVE BOND BOUND**, with `c = q / m`.

This is the conversion the cell already has both halves of: `straddle_form_bound` supplies the
absolute cost `q` per bond by AM–GM with no spectral input, and `CellSpectrum.diag_form_margin`
supplies the local margin `m` from the excited Casimir. Nothing new is measured.

DERIVED: `q / m` is the ratio of the two supplied constants, not a choice; the `0`s are the
sign conditions those constants must meet for the division to run the right way. -/
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

/-- **⭐ THE SAME, AGAINST THE BOND'S OWN LOCAL MASS.** `relative_of_absolute_form_bound` charges the
cost against the global `v ⊙ v`; this charges it against any quantity `loc` the caller nominates.
The proof never uses what the mass is, so the generalisation is free — and it is the one that
matters, because `shared_locals_force_shrinking_margin` says the relative route degenerates exactly
when every bond is charged against the same thing.

For a straddling plaquette `loc` is the mass carried on its OWN four links. Its cost vanishes with
that mass — the magnetic term is off-diagonal in the flux basis, so on a definite-flux state with no
flux on those links both sides are `0` — where a global margin `m > 0` would be false there.

DERIVED: `q / δ` is the ratio of the two supplied constants; the `0`s are the sign conditions that
make the division run the right way. -/
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

/-- **⭐⭐ AND SUMMING THEM KEEPS ONE CONSTANT, WITH THE MASSES ALL DIFFERENT.**

Each bond carries its own `loc b`: its cost is `q·loc b` and its margin `δ·loc b`. The summed bound
is `−(q/δ)` against the summed local parts — **no `s.card`, and no single mass shared between
bonds.** This is the hypothesis shape `shared_locals_force_shrinking_margin` leaves open, and the
one the lattice presents.

Set the three side by side, all from per-bond data:

* `coupling_form_le_bondCount` — global mass, absolute: `n·q`. Extensive, and
  `coupling_form_extensive` shows that is real.
* `relative_sum_of_absolute_bonds` — global mass, relative: `q/m`, but `m` must hold on every bond
  against the whole vector, which `shared_locals_force_shrinking_margin` collapses to `M/n`.
* **this one** — own mass, relative: `q/δ`, and the masses differ, so nothing collapses.

DERIVED: the `0`s are the sign conditions on `q` and `δ`; no other numeral. -/
theorem relative_sum_of_local_bonds (s : Finset β) (V A : β → Matrix ι ι ℝ) (loc : β → ℝ)
    {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ) (v : ι → ℝ)
    (habs : ∀ b ∈ s, |v ⬝ᵥ (V b *ᵥ v)| ≤ q * loc b)
    (hmar : ∀ b ∈ s, δ * loc b ≤ v ⬝ᵥ (A b *ᵥ v)) :
    -(q / δ) * (v ⬝ᵥ ((∑ b ∈ s, A b) *ᵥ v)) ≤ v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v) :=
  relative_coupling_form_sum s V A v
    (fun b hb => relative_of_local_bound hq hδ v (habs b hb) (hmar b hb))

#print axioms relative_sum_of_local_bonds


/-- **⭐⭐ SO THE SUMMED COST CARRIES NO BOND COUNT.** From the SAME per-bond inputs that
`coupling_form_le_bondCount` consumes — an absolute cost `q` on each bond — together with a local
margin `m` on each bond, the summed coupling obeys

    −(q/m) · ⟨v, (∑ A_b) v⟩ ≤ ⟨v, (∑ V_b) v⟩

and **`s.card` does not appear**. Set beside `coupling_form_le_bondCount`'s `n·q·⟨v,v⟩`, the two
differ only in what the cost is charged against: the global vector, or the energy each bond sits on.

`coupling_form_extensive` shows the `n·a` growth of the ABSOLUTE bound is real and not an artifact of
the triangle inequality. It is equally not a statement about this one — and
`form_perturbation_reaches_finitely_many` caps the bond count only for the absolute route.

**⛔ WHAT IS STILL MISSING.** The `A b` here are whatever local parts the caller supplies, and for
the physical Kogut–Susskind coupling they must (i) be the electric terms of the bond's own links and
(ii) sum to at most the full electric term. Links are shared between plaquettes, so (ii) needs each
link's energy apportioned among the plaquettes containing it — a factor set by the COORDINATION
NUMBER, not by the volume. That apportionment is not proved here. -/
theorem relative_sum_of_absolute_bonds (s : Finset β) (V A : β → Matrix ι ι ℝ) {q m : ℝ}
    (hq : 0 ≤ q) (hm : 0 < m) (v : ι → ℝ)
    (habs : ∀ b ∈ s, |v ⬝ᵥ (V b *ᵥ v)| ≤ q * (v ⬝ᵥ v))
    (hmar : ∀ b ∈ s, m * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A b *ᵥ v)) :
    -(q / m) * (v ⬝ᵥ ((∑ b ∈ s, A b) *ᵥ v)) ≤ v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v) :=
  relative_coupling_form_sum s V A v
    (fun b hb => relative_of_absolute_form_bound hq hm v (habs b hb) (hmar b hb))

#print axioms relative_sum_of_absolute_bonds

/-- **⭐ LOCAL PARTS THAT DO NOT OVER-COUNT CARRY THE BOUND TO THE FULL OPERATOR.** A relative bound
against the summed local parts becomes one against the whole unperturbed operator as soon as the
locals are dominated by it in form. The coefficient is negative, so domination pushes the left side
DOWN and the inequality survives.

This is the apportionment link, and it is where the lattice's incidence enters rather than its size.
For Kogut–Susskind, giving each plaquette a sixth of the electric energy of its own four links makes
the sum over ALL plaquettes return each link exactly once — in four dimensions a link lies in six
plaquettes — so the sum over the STRADDLING ones is at most the full electric term. The factor is the
COORDINATION NUMBER and does not move with the volume, which is the whole difference from
`coupling_form_le_bondCount`, whose factor is the bond count.

DERIVED: the `0` is the sign condition on `c`, which is what makes domination push the left
side down rather than up. No other numeral. -/
theorem relative_of_dominated_locals {V A Aloc : Matrix ι ι ℝ} {c : ℝ} (hc : 0 ≤ c) (v : ι → ℝ)
    (hrel : -c * (v ⬝ᵥ (Aloc *ᵥ v)) ≤ v ⬝ᵥ (V *ᵥ v))
    (hdom : v ⬝ᵥ (Aloc *ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)) :
    -c * (v ⬝ᵥ (A *ᵥ v)) ≤ v ⬝ᵥ (V *ᵥ v) := by
  have hstep : -c * (v ⬝ᵥ (A *ᵥ v)) ≤ -c * (v ⬝ᵥ (Aloc *ᵥ v)) :=
    mul_le_mul_of_nonpos_left hdom (neg_nonpos.mpr hc)
  linarith

#print axioms relative_of_dominated_locals

/-- **⭐⭐⭐ AND TO THE FULL OPERATOR.** With the apportionment `∑ A_b ≤ A`, the per-bond local data
bounds the whole coupling relative to the whole unperturbed operator by `q/δ`.

**This is the statement the straddling plaquette has to meet**, and every quantity in it is local:
`q` is the bond's cost coefficient, `δ` its margin coefficient, `loc b` the mass on its own links,
and the apportionment is the coordination count. Feed the result to
`CellSpectrum.coupled_gap_of_relative_coupling_bound` for the gap `(1 − q/δ)·mform`.

DERIVED: the `0`s are the sign conditions on `q` and `δ`; no other numeral. -/
theorem relative_full_of_local_bonds (s : Finset β) (V A : β → Matrix ι ι ℝ) (loc : β → ℝ)
    (Afull : Matrix ι ι ℝ) {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ) (v : ι → ℝ)
    (habs : ∀ b ∈ s, |v ⬝ᵥ (V b *ᵥ v)| ≤ q * loc b)
    (hmar : ∀ b ∈ s, δ * loc b ≤ v ⬝ᵥ (A b *ᵥ v))
    (hdom : v ⬝ᵥ ((∑ b ∈ s, A b) *ᵥ v) ≤ v ⬝ᵥ (Afull *ᵥ v)) :
    -(q / δ) * (v ⬝ᵥ (Afull *ᵥ v)) ≤ v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v) :=
  relative_of_dominated_locals (div_nonneg hq hδ.le) v
    (relative_sum_of_local_bonds s V A loc hq hδ v habs hmar) hdom

#print axioms relative_full_of_local_bonds

/-- **⭐⭐ THE WHOLE NON-EXTENSIVE CHAIN, IN ONE STATEMENT.** From the per-bond inputs the cell
already supplies — an absolute cost `q` on each bond and a local margin `m` on each bond — together
with the apportionment `∑ A_b ≤ A`, the full coupling is bounded relative to the full unperturbed
operator by `q/m`. **No bond count occurs anywhere**, in the statement or the proof.

Set against `coupling_form_le_bondCount` (`n·q`) and `coupling_form_extensive` (`n·a` is attained),
this is the same per-bond data yielding a volume-independent constant, because the cost is charged
against the energy each bond sits on instead of against the global vector.

Feed the result to `CellSpectrum.coupled_gap_of_relative_coupling_bound`, which needs `q/m < 1` and
returns the gap `(1 − q/m)·m` — again with no bond count.

DERIVED: the `0`s are the sign conditions on `q` and `m`; no other numeral. -/
theorem relative_full_of_absolute_bonds (s : Finset β) (V A : β → Matrix ι ι ℝ)
    (Afull : Matrix ι ι ℝ) {q m : ℝ} (hq : 0 ≤ q) (hm : 0 < m) (v : ι → ℝ)
    (habs : ∀ b ∈ s, |v ⬝ᵥ (V b *ᵥ v)| ≤ q * (v ⬝ᵥ v))
    (hmar : ∀ b ∈ s, m * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A b *ᵥ v))
    (hdom : v ⬝ᵥ ((∑ b ∈ s, A b) *ᵥ v) ≤ v ⬝ᵥ (Afull *ᵥ v)) :
    -(q / m) * (v ⬝ᵥ (Afull *ᵥ v)) ≤ v ⬝ᵥ ((∑ b ∈ s, V b) *ᵥ v) :=
  relative_of_dominated_locals (div_nonneg hq hm.le) v
    (relative_sum_of_absolute_bonds s V A hq hm v habs hmar) hdom

#print axioms relative_full_of_absolute_bonds

/-- **⛔⭐ THE CONTROL: SHARED LOCALS PUT THE BOND COUNT BACK.**

If every bond is charged against the SAME local part `A₀`, the apportionment forces
`s.card · m ≤ M`, so a uniform margin `m` shrinks like `1/n` and `q/m` is extensive again. **The
relative bound is therefore not automatically non-extensive**: it buys nothing unless the local
parts are genuinely different from one another.

That is the requirement the lattice meets and the reason the route can work there — each straddling
plaquette is charged against the electric energy of ITS OWN four links, and distinct plaquettes
charge distinct links up to the fixed coordination multiplicity. It is a fact about the incidence,
to be proved rather than assumed, and this theorem is what makes the requirement explicit.

DERIVED: the `0` is the sign condition on the vector's own form, needed to divide it out at
the end. No other numeral. -/
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

/-- **⭐⭐⭐ THE VOLUME-UNIFORM GAP FROM PER-BOND DATA.** The chain, composed: per-bond costs `q`,
per-bond local margins `m`, the apportionment `∑ A_b ≤ H₀`, and `q/m < 1` give the spectral gap

    (1 − q/m) · mform

for the COUPLED operator `H₀ + ∑ V_b`. **The bond set occurs in the hypotheses and nowhere in the
conclusion's constant.** Contrast `bondCount_lt_of_budget`, which caps the bond count for the
absolute route at `μ/(2a)`.

**⛔ Read `shared_locals_force_shrinking_margin` before instantiating.** A uniform `m` over bonds
sharing one local part collapses to `M/s.card`, which puts the bond count straight back into `q/m`.
The hypotheses here are satisfiable at a volume-independent `q/m` only when the local parts are
genuinely distinct.

DERIVED: `1` is `coupled_gap_of_relative_coupling_bound`'s threshold, forced there rather than
chosen here; the `0`s are the sign conditions on `q`, `m` and the gap. No numeral of this
theorem's own. -/
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

/-! ### The budget is a fixed number, so the bond count it admits is finite -/

/-- **The budget caps the bond count.** At a STRICTLY POSITIVE per-bond depth `a` — load-bearing, and the conclusion is false without it — an extensive residual `n·a ≤ δ` and the hypothesis `2δ < μ`
of `gap_of_form_perturbation` together force `n < μ/(2a)`. Nothing about the lattice enters: this is
the arithmetic of the two hypotheses, and it is where the route ends. -/
theorem bondCount_lt_of_budget {n : ℕ} {a δ μ : ℝ} (ha : 0 < a)
    (hext : (n : ℝ) * a ≤ δ) (hbud : 2 * δ < μ) : (n : ℝ) < μ / (2 * a) := by
  have h : (n : ℝ) * (2 * a) = 2 * ((n : ℝ) * a) := by ring
  rw [lt_div_iff₀ (by linarith : (0 : ℝ) < 2 * a), h]
  linarith

/-- **The form-perturbation route reaches only finitely many volumes.** For every gap `μ` and every
strictly positive per-bond depth `a` there is a bond count `N₀` past which NO `δ` consistent with the
extensive lower bound satisfies `2δ < μ`. A volume-uniform gap needs the hypothesis at every volume,
so this closes `gap_of_form_perturbation` as a route to `product_volume_gap`'s coupled counterpart. -/
theorem form_perturbation_reaches_finitely_many (a μ : ℝ) (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ δ : ℝ, (n : ℝ) * a ≤ δ → ¬ (2 * δ < μ) := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (μ / (2 * a))
  refine ⟨N₀, fun n hn δ hδ hbud => ?_⟩
  have hlt := bondCount_lt_of_budget ha hδ hbud
  have hcast : (N₀ : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  linarith

/-! ### A concrete chain, so the negative is not vacuous

`N+1` two-state cells in a row (the `j = 0, 1/2` truncation `CellSpectrum.Hcell2` already uses), with
the shared-link electric cross term on each of the `N` bonds. The all-excited configuration is
extremal on every bond at once, which is what `coupling_form_extensive` asks for. -/

/-- The flux label of a two-state cell: `0` at the vacuum `j = 0`, `1` at the excited `j = 1/2`.

DERIVED: these are the character indices themselves (`i = 2j ∈ {0, 1}` in `CellEnclosure.dim 0 + 1`),
not a parametrisation. The shared-link energy is a function of the fluxes, so the flux is what the
coupling reads. -/
def flux2 : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1

lemma flux2_one : flux2 1 = 1 := by
  unfold flux2
  rw [if_neg (by decide : ¬ ((1 : Fin 2) = 0))]

/-- The shared-link cross term on bond `b` of a chain of `N+1` two-state cells, at depth `a`.

DERIVED: the SHAPE is the cross term of the shared link's electric energy. A link carried by two
neighbouring plaquettes has energy `(n_c − n_{c+1})² = n_c² + n_{c+1}² − 2 n_c n_{c+1}`; the squares
are one-cell and belong to the decoupled part, so the entire two-cell content is `−2 n_c n_{c+1}`.
`a` carries that `2` together with the electric scale rather than fixing a unit here, so the theorems
below hold at whatever depth the group and the coupling produce. `Fin 2` is the two-state truncation
`Hcell2`, `Fin (N+1)` the cells and `Fin N` the bonds between them. -/
noncomputable def bondCouple (N : ℕ) (a : ℝ) (b : Fin N) :
    Matrix (Fin (N + 1) → Fin 2) (Fin (N + 1) → Fin 2) ℝ :=
  Matrix.diagonal fun s => -a * (flux2 (s b.castSucc) * flux2 (s b.succ))

/-- The all-excited configuration: every cell at the first excited character state.

DERIVED: `flux2` is largest at `1` and each bond term is a product of two fluxes, so putting every
cell at `1` extremises every bond AT ONCE. That simultaneity, not the value, is what
`coupling_form_extensive` consumes — and it is why the bond costs add instead of competing. -/
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

/-- Every bond is lowered by exactly `a` at the all-excited configuration. -/
theorem bondCouple_form (N : ℕ) (a : ℝ) (b : Fin N) :
    (Pi.single (allExc N) (1 : ℝ)) ⬝ᵥ
        (bondCouple N a b *ᵥ (Pi.single (allExc N) (1 : ℝ))) = -a := by
  rw [bondCouple, single_diagonal_form]
  simp only [allExc, flux2_one]
  ring

/-- **The chain's residual is extensive: `δ ≥ N·a` at `N` bonds.** The all-excited configuration
lowers all `N` bonds at once, so any `δ` bounding the coupled form must carry the whole sum — with no
hypothesis on the depth at all. Together with `form_perturbation_reaches_finitely_many` this is the
negative result: the residual grows with the volume while the budget `μ/2` does not. -/
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

/-- **No fixed budget survives the chain.** For every gap `μ` and every strictly positive per-bond
depth `a`, there is a cell count past which `gap_of_form_perturbation`'s hypothesis `2δ < μ` is
unsatisfiable for the chain coupling. The coupled volume gap does not follow from a quadratic-form
perturbation of the decoupled product, at any budget. -/
theorem chain_budget_fails (μ a : ℝ) (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ δ : ℝ,
      (∀ v : (Fin (N + 1) → Fin 2) → ℝ,
        |v ⬝ᵥ ((∑ b : Fin N, bondCouple N a b) *ᵥ v)| ≤ δ * (v ⬝ᵥ v)) → ¬ (2 * δ < μ) := by
  obtain ⟨N₀, hN₀⟩ := form_perturbation_reaches_finitely_many a μ ha
  exact ⟨N₀, fun N hN δ hδ => hN₀ N hN δ (chain_coupling_extensive N hδ)⟩

/-! ### The positive half, stated so the two can be compared at one glance -/

/-- **The coupled gap from a bond decomposition.** `gap_of_form_perturbation` with the residual
supplied by the bond bound: `n` bonds at form cost `q` each give the coupled matrix a gap
`μ − 2nq`, provided `2nq < μ`. This is the theorem the route wanted, with the missing scalar filled
in — and `bondCount_lt_of_budget` says its hypothesis holds for only finitely many `n`. -/
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
