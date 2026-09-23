import MassGap.CellEnclosure

/-!
# MassGap.CellTail — the pivot recurrence as a function of its seed

`CellEnclosure.pivotSeq d s lam` runs the backward recurrence `p(i) = (d(i) − s) − lam²/p(i+1)` on
`Fin (n+1)` from the seed `p(last) = d(last) − s`. That seed omits the subtraction
`lam²/p(last+1)` that a longer index range would contribute, so it is the largest seed the recurrence
can be started from; `tail_seed_le_trunc_seed` states that comparison.

This module generalises the recurrence over its seed, as `pivotSeqFrom d s lam seed`, and proves:

* `step_mono` — one step `q ↦ (d − s) − lam²/q` is monotone increasing in `q` on the positives.
* `pivotSeqFrom_mono` and `pivotSeqFrom_mono_above` — a smaller seed gives a pointwise smaller
  sequence, globally where the smaller sequence is everywhere positive, and above a cut `k` where it
  is positive only there. Monotonicity propagates through positive pivots only, and the positive
  region is an upper segment, so the `_above` form is the one with the weaker hypothesis.
* `pos_of_pos_of_le` and `pos_above_of_tail` — positivity transfers from the sequence seeded by a
  lower bound to the sequence seeded by anything larger.
* `pivotSeqFrom_ge_of_selfconsistent` and `pivotSeqFrom_pos_of_selfconsistent` — under
  `lam² ≤ eps * (d i − s − eps)` at every index above the cut and `eps ≤ seed`, every pivot at or
  above the cut is at least `eps`, hence positive. The seed is otherwise unconstrained.
* `pivots_nonneg_of_block_and_tail` — combining the tail bound above the cut with a finite sign
  check `hbelow` below it gives `∀ i ≠ m, 0 ≤ pivotSeq d s lam i`, the shape
  `gap_of_ldl_one_neg_pivot` consumes.

Scope: every statement lives inside one `Fin (n+1)` and quantifies over `n`; nothing is transported
between index types, and no relation between two truncations is stated or used. The self-consistency
hypothesis `hcons` is an input, not a result — `certify/cell_pivot_certificate.tail_start` is the
numerical routine that solves `eps·(d(m+1) − s − eps) ≥ lam²` for the least cut, and `hbelow` is a
finite sign check the caller supplies.

DERIVED: `n + 1` is the arity of the index type, a backward recurrence needing a last element to
start from; `2` is the exponent in `lam^2`, the off-diagonal entered twice by the
completing-the-square factorisation; `0` is the positivity threshold on pivots, on `eps` and on
`seed`-derived quantities. No numeral is a magnitude.

Foundational footprint only (`#print axioms` at the end).
-/

namespace MassGap.CellTail

open MassGap.CellEnclosure

variable {n : ℕ}

/-- The backward pivot recurrence on `Fin (n+1)` from an arbitrary seed at the last index: the value
at `Fin.last n` is `seed`, and at `i.castSucc` it is `(d i.castSucc - s) - lam^2 / p(i.succ)`. Built
with `Fin.reverseInduction`. `CellEnclosure.pivotSeq d s lam` is this at the seed
`d (Fin.last n) - s`, as `pivotSeq_eq_from` records.

Total: no positivity is required of the seed or of any pivot, so a division by zero returns `0` under
Lean's convention and the lemmas below carry positivity as hypotheses where they need it.

DERIVED: `n + 1` is the arity of the index type — a backward recurrence needs a last element to start
from, so the sequence is over a nonempty `Fin`; `2` is the exponent in `lam^2`, the off-diagonal
entered twice by the completing-the-square factorisation. Neither is a magnitude. -/
noncomputable def pivotSeqFrom (d : Fin (n+1) → ℝ) (s lam seed : ℝ) : Fin (n+1) → ℝ :=
  Fin.reverseInduction seed (fun i pnext => (d i.castSucc - s) - lam^2 / pnext)

@[simp] lemma pivotSeqFrom_last (d : Fin (n+1) → ℝ) (s lam seed : ℝ) :
    pivotSeqFrom d s lam seed (Fin.last n) = seed := by
  simp [pivotSeqFrom]

lemma pivotSeqFrom_castSucc (d : Fin (n+1) → ℝ) (s lam seed : ℝ) (i : Fin n) :
    pivotSeqFrom d s lam seed i.castSucc
      = (d i.castSucc - s) - lam^2 / (pivotSeqFrom d s lam seed i.succ) := by
  simp [pivotSeqFrom]

/-- `CellEnclosure.pivotSeq d s lam = pivotSeqFrom d s lam (d (Fin.last n) - s)`, by `rfl`. It
identifies the truncating seed so that the seed-parametrised lemmas below apply to `pivotSeq`
directly.

DERIVED: `n + 1` is the arity of the index type. -/
lemma pivotSeq_eq_from (d : Fin (n+1) → ℝ) (s lam : ℝ) :
    pivotSeq d s lam = pivotSeqFrom d s lam (d (Fin.last n) - s) := rfl

/-- One step of the recurrence is monotone in the pivot above it: from `0 < a` and `a ≤ b`,
`(d - s) - lam^2 / a ≤ (d - s) - lam^2 / b`. Positivity of `a` is what makes
`div_le_div_of_nonneg_left` applicable; `0 < b` follows from it.

DERIVED: `0` is the positivity threshold on `a`; `2` is the exponent in `lam^2`. -/
lemma step_mono {a b d s lam : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (d - s) - lam^2 / a ≤ (d - s) - lam^2 / b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have : lam^2 / b ≤ lam^2 / a := by
    apply div_le_div_of_nonneg_left (by positivity) ha hab
  linarith

/-- The recurrence is monotone in its seed: from `a ≤ b` and `0 < pivotSeqFrom d s lam a i` at every
index `i`, the conclusion is `pivotSeqFrom d s lam a i ≤ pivotSeqFrom d s lam b i` at every `i`. By
`Fin.reverseInduction`, with `step_mono` at each step.

Positivity is required of the sequence seeded by the smaller value at every index, which is the
hypothesis `pivotSeqFrom_mono_above` weakens to an upper segment.

DERIVED: `n + 1` is the arity of the index type; `0` is the positivity threshold on the pivots of
the lower-seeded sequence. -/
theorem pivotSeqFrom_mono (d : Fin (n+1) → ℝ) (s lam : ℝ) {a b : ℝ} (hab : a ≤ b)
    (hpos : ∀ i, 0 < pivotSeqFrom d s lam a i) :
    ∀ i, pivotSeqFrom d s lam a i ≤ pivotSeqFrom d s lam b i := by
  intro i
  induction i using Fin.reverseInduction with
  | last => simpa using hab
  | cast i ih =>
      rw [pivotSeqFrom_castSucc, pivotSeqFrom_castSucc]
      exact step_mono (hpos i.succ) ih

/-- Positivity transfers from the smaller seed to the larger: under the hypotheses of
`pivotSeqFrom_mono`, `0 < pivotSeqFrom d s lam b i` at every index `i`. Immediate from `hpos i` and
the monotonicity bound.

DERIVED: `n + 1` is the arity of the index type; `0` is the positivity threshold on the pivots of
both sequences. -/
theorem pos_of_pos_of_le (d : Fin (n+1) → ℝ) (s lam : ℝ) {a b : ℝ} (hab : a ≤ b)
    (hpos : ∀ i, 0 < pivotSeqFrom d s lam a i) (i : Fin (n+1)) :
    0 < pivotSeqFrom d s lam b i :=
  lt_of_lt_of_le (hpos i) (pivotSeqFrom_mono d s lam hab hpos i)

/-- `(d - s) - lam^2 / pnext ≤ d - s` whenever `0 < pnext`. A pivot computed with a further
subtraction is at most the truncating value `d - s`, since `lam^2 / pnext` is nonnegative.

Stated on real numbers alone; `d`, `s`, `lam` and `pnext` are unrelated to any particular index here.

DERIVED: `0` is the positivity threshold on `pnext`; `2` is the exponent in `lam^2`. -/
lemma tail_seed_le_trunc_seed {d s lam pnext : ℝ} (h : 0 < pnext) :
    (d - s) - lam^2 / pnext ≤ d - s := by
  have : 0 ≤ lam^2 / pnext := by positivity
  linarith

/-- Monotonicity in the seed above a cut `k : Fin (n+1)`: from `a ≤ b` and
`0 < pivotSeqFrom d s lam a i` for every `i` with `k ≤ i`, the conclusion is
`pivotSeqFrom d s lam a i ≤ pivotSeqFrom d s lam b i` for every such `i`. By `Fin.reverseInduction`,
with `Fin.castSucc_le_succ` carrying the cut hypothesis to the index above.

Both the hypothesis and the conclusion are restricted to indices at or above `k`. Monotonicity in the
seed propagates only through positive pivots, since a negative pivot reverses the direction of
`q ↦ lam^2 / q`, so no conclusion is drawn below the cut.

DERIVED: `n + 1` is the arity of the index type; `0` is the positivity threshold on the pivots of
the lower-seeded sequence above the cut. -/
theorem pivotSeqFrom_mono_above (d : Fin (n+1) → ℝ) (s lam : ℝ) {a b : ℝ} (hab : a ≤ b)
    (k : Fin (n+1)) (hpos : ∀ i, k ≤ i → 0 < pivotSeqFrom d s lam a i) :
    ∀ i, k ≤ i → pivotSeqFrom d s lam a i ≤ pivotSeqFrom d s lam b i := by
  intro i
  induction i using Fin.reverseInduction with
  | last => intro _; simpa using hab
  | cast i ih =>
      intro hki
      have hsucc : k ≤ i.succ := le_trans hki (le_of_lt Fin.castSucc_lt_succ)
      rw [pivotSeqFrom_castSucc, pivotSeqFrom_castSucc]
      exact step_mono (hpos i.succ hsucc) (ih hsucc)

/-- Positivity above a cut transfers from a lower seed to a larger one: from `seedLo ≤ seedTrue` and
`0 < pivotSeqFrom d s lam seedLo i` for every `i` with `k ≤ i`, the conclusion is
`0 < pivotSeqFrom d s lam seedTrue i` for every such `i`. It composes `hposLo` with
`pivotSeqFrom_mono_above`.

Nothing here identifies `seedTrue` with any particular quantity; it is any real number at or above
`seedLo`.

DERIVED: `n + 1` is the arity of the index type; `0` is the positivity threshold on the pivots of
both sequences above the cut. -/
theorem pos_above_of_tail (d : Fin (n+1) → ℝ) (s lam seedLo seedTrue : ℝ)
    (hle : seedLo ≤ seedTrue) (k : Fin (n+1))
    (hposLo : ∀ i, k ≤ i → 0 < pivotSeqFrom d s lam seedLo i) :
    ∀ i, k ≤ i → 0 < pivotSeqFrom d s lam seedTrue i := fun i hki =>
  lt_of_lt_of_le (hposLo i hki) (pivotSeqFrom_mono_above d s lam hle k hposLo i hki)

/-- Every pivot at or above a cut is at least `eps`. The hypotheses are `0 < eps`, the
self-consistency bound `hcons : lam^2 ≤ eps * (d i.castSucc - s - eps)` at every `i` with
`k ≤ i.castSucc`, and `eps ≤ seed`; the conclusion is `eps ≤ pivotSeqFrom d s lam seed i` for every
`i` with `k ≤ i`.

One step: if the pivot above is at least `eps` then `lam^2 / p ≤ lam^2 / eps ≤ d i - s - eps`, so
`(d i - s) - lam^2 / p ≥ eps`. Downward induction by `Fin.reverseInduction` does the rest. The seed
is constrained only by `eps ≤ seed`.

`hcons` is a hypothesis, not a consequence: `certify/cell_pivot_certificate.tail_start` is the
routine that finds the least cut at which it holds, using `d i = i(i+2)/4` growing quadratically
while `lam` is fixed. The statement lives inside a single `Fin (n+1)` and says nothing relating two
index ranges.

DERIVED: `n + 1` is the arity of the index type; `0` is the positivity threshold on `eps`; `2` is
the exponent in `lam^2`. -/
theorem pivotSeqFrom_ge_of_selfconsistent (d : Fin (n+1) → ℝ) (s lam eps : ℝ) (heps : 0 < eps)
    (k : Fin (n+1))
    (hcons : ∀ i : Fin n, k ≤ i.castSucc → lam^2 ≤ eps * (d i.castSucc - s - eps))
    {seed : ℝ} (hseed : eps ≤ seed) :
    ∀ i, k ≤ i → eps ≤ pivotSeqFrom d s lam seed i := by
  intro i
  induction i using Fin.reverseInduction with
  | last => intro _; simpa using hseed
  | cast i ih =>
      intro hki
      rw [pivotSeqFrom_castSucc]
      -- the index above is still above the cut, so the inductive hypothesis applies there
      have hnext : eps ≤ pivotSeqFrom d s lam seed i.succ :=
        ih (le_trans hki (Fin.castSucc_le_succ i))
      have hd : lam^2 / eps ≤ d i.castSucc - s - eps := by
        have h := hcons i hki
        -- the `div_le_iff` family gained a `₀` suffix for `GroupWithZero`; accept either spelling
        -- rather than pin this proof to one Mathlib revision
        first
          | rw [div_le_iff₀ heps]
          | rw [div_le_iff heps]
        nlinarith [h]
      have h1 : lam^2 / (pivotSeqFrom d s lam seed i.succ) ≤ lam^2 / eps :=
        div_le_div_of_nonneg_left (sq_nonneg lam) heps hnext
      linarith

/-- Positivity above the cut, from the same hypotheses as `pivotSeqFrom_ge_of_selfconsistent`:
`0 < pivotSeqFrom d s lam seed i` for every `i` with `k ≤ i`, by composing `0 < eps` with that
lemma's bound. This is the shape `pos_above_of_tail` consumes.

DERIVED: `n + 1` is the arity of the index type; `0` is the positivity threshold on `eps` and the
level the pivots are shown to exceed; `2` is the exponent in `lam^2`. -/
theorem pivotSeqFrom_pos_of_selfconsistent (d : Fin (n+1) → ℝ) (s lam eps : ℝ) (heps : 0 < eps)
    (k : Fin (n+1))
    (hcons : ∀ i : Fin n, k ≤ i.castSucc → lam^2 ≤ eps * (d i.castSucc - s - eps))
    {seed : ℝ} (hseed : eps ≤ seed) :
    ∀ i, k ≤ i → 0 < pivotSeqFrom d s lam seed i := fun i hki =>
  lt_of_lt_of_le heps (pivotSeqFrom_ge_of_selfconsistent d s lam eps heps k hcons hseed i hki)

/-- `∀ i ≠ m, 0 ≤ pivotSeq d s lam i`, the shape `gap_of_ldl_one_neg_pivot` consumes, assembled from
a check below a cut and an inequality above it. The hypotheses are `0 < eps`, a cut `k` and an
excepted index `m`, the self-consistency bound `hcons` at every index at or above the cut, the seed
condition `hseed : eps ≤ d (Fin.last n) - s`, and `hbelow`, which gives `0 ≤ pivotSeq d s lam i` for
every `i < k` other than `m`.

The proof splits on `i < k` or `k ≤ i`: below the cut it is `hbelow`, above it is
`pivotSeqFrom_ge_of_selfconsistent` read through `pivotSeq_eq_from`.

Nothing is assumed relating different index ranges. The statement is inside one `Fin (n+1)` and is
quantified over `n`, so each `n` carries its own instance with its own `eps` and cut.

DERIVED: `n + 1` is the arity of the index type; `0` is the positivity threshold on `eps` and the
lower bound asserted on the pivots; `2` is the exponent in `lam^2`. -/
theorem pivots_nonneg_of_block_and_tail (d : Fin (n+1) → ℝ) (s lam eps : ℝ) (heps : 0 < eps)
    (k m : Fin (n+1))
    (hcons : ∀ i : Fin n, k ≤ i.castSucc → lam^2 ≤ eps * (d i.castSucc - s - eps))
    (hseed : eps ≤ d (Fin.last n) - s)
    (hbelow : ∀ i, i < k → i ≠ m → 0 ≤ pivotSeq d s lam i) :
    ∀ i, i ≠ m → 0 ≤ pivotSeq d s lam i := by
  intro i hi
  rcases lt_or_ge i k with hik | hik
  · exact hbelow i hik hi
  · rw [pivotSeq_eq_from]
    exact le_of_lt (lt_of_lt_of_le heps
      (pivotSeqFrom_ge_of_selfconsistent d s lam eps heps k hcons hseed i hik))

#print axioms pivots_nonneg_of_block_and_tail
#print axioms pivotSeqFrom_mono
#print axioms pos_of_pos_of_le
#print axioms pivotSeqFrom_mono_above
#print axioms pos_above_of_tail
#print axioms pivotSeqFrom_ge_of_selfconsistent
#print axioms pivotSeqFrom_pos_of_selfconsistent

end MassGap.CellTail
