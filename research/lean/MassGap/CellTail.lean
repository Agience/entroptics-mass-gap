import MassGap.CellEnclosure

/-!
# MassGap.CellTail — the truncation tail, bounded rather than dropped

`CellEnclosure.pivotSeq` runs the backward recurrence `p(i) = (d(i) − s) − lam²/p(i+1)` from the seed
`p(last) = d(last) − s`. That seed is the TRUNCATION: the physical cell continues past `last`, and the
true pivot there is `d(last) − s − lam²/p(last+1)`, which is SMALLER. Truncation therefore drops a
subtraction, and a dropped subtraction makes every pivot below it too large — the error runs in the one
direction that could report a positive pivot where the real cell has a negative one.

WHAT THIS FILE PROVES. The recurrence is monotone in its seed: a smaller seed gives a pointwise smaller
sequence, provided the smaller one stays positive where it is used. So running the recurrence from a
LOWER BOUND on the true pivot at `last` produces a lower bound on the true pivots at every index — and
wherever that bound is positive, the true pivot is positive too.

That is what turns the certificate from a statement about `HcellR jmax lam` into a statement about the
cell it truncates: "positive except at one index" for the bounding sequence gives "at most one
eigenvalue below `s`" for the real one, which is the hypothesis `gap_of_ldl_one_neg_pivot` consumes.

The arithmetic side — that a self-consistent lower bound `p(i) ≥ d(i) − s − eps` exists at all, and
where it starts — is `certify/cell_pivot_certificate.tail_start`: it closes when
`eps·(d(m+1) − s − eps) ≥ lam²`, and since `d(i) = i(i+2)/4` grows quadratically while `lam` is fixed,
it closes at `m ≤ 6` across the whole crossover coupling range.

Foundational footprint only (`#print axioms` at the end).
-/

namespace MassGap.CellTail

open MassGap.CellEnclosure

variable {n : ℕ}

/-- The pivot recurrence from an ARBITRARY seed at the last index.

`pivotSeq` is this at the truncating seed `d(last) − s`. Taking the seed as a parameter is what lets a
lower bound on the true pivot at `last` be propagated downward.

DERIVED: `n+1` is the arity of the index type — a backward recurrence needs a last element to start
from, so the sequence is over a NONEMPTY `Fin`; and `2` is the exponent in `lam^2`, which is the
off-diagonal entered twice by the completing-the-square factorisation, not a magnitude. -/
noncomputable def pivotSeqFrom (d : Fin (n+1) → ℝ) (s lam seed : ℝ) : Fin (n+1) → ℝ :=
  Fin.reverseInduction seed (fun i pnext => (d i.castSucc - s) - lam^2 / pnext)

@[simp] lemma pivotSeqFrom_last (d : Fin (n+1) → ℝ) (s lam seed : ℝ) :
    pivotSeqFrom d s lam seed (Fin.last n) = seed := by
  simp [pivotSeqFrom]

lemma pivotSeqFrom_castSucc (d : Fin (n+1) → ℝ) (s lam seed : ℝ) (i : Fin n) :
    pivotSeqFrom d s lam seed i.castSucc
      = (d i.castSucc - s) - lam^2 / (pivotSeqFrom d s lam seed i.succ) := by
  simp [pivotSeqFrom]

/-- `pivotSeq` is the recurrence at the truncating seed — the definition, restated so the tail results
below apply to it directly. -/
lemma pivotSeq_eq_from (d : Fin (n+1) → ℝ) (s lam : ℝ) :
    pivotSeq d s lam = pivotSeqFrom d s lam (d (Fin.last n) - s) := rfl

/-- **One step of the recurrence is monotone in the pivot above it.**
`q ↦ (d − s) − lam²/q` rises with `q` on the positives: a larger pivot above subtracts less. -/
lemma step_mono {a b d s lam : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (d - s) - lam^2 / a ≤ (d - s) - lam^2 / b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have : lam^2 / b ≤ lam^2 / a := by
    apply div_le_div_of_nonneg_left (by positivity) ha hab
  linarith

/-- **The recurrence is monotone in its seed.** A smaller seed gives a pointwise smaller sequence,
provided the smaller sequence stays positive — which is where the division is defined and where the
step above is monotone.

This is the whole tail argument: seed the recurrence with a LOWER BOUND on the true pivot at `last`,
and every index below is a lower bound on the true pivot there. -/
theorem pivotSeqFrom_mono (d : Fin (n+1) → ℝ) (s lam : ℝ) {a b : ℝ} (hab : a ≤ b)
    (hpos : ∀ i, 0 < pivotSeqFrom d s lam a i) :
    ∀ i, pivotSeqFrom d s lam a i ≤ pivotSeqFrom d s lam b i := by
  intro i
  induction i using Fin.reverseInduction with
  | last => simpa using hab
  | cast i ih =>
      rw [pivotSeqFrom_castSucc, pivotSeqFrom_castSucc]
      exact step_mono (hpos i.succ) ih

/-- **Positivity transfers upward from the bounding sequence.** If the sequence seeded by the lower
bound is positive at an index, so is the one seeded by anything larger.

Read with `a` the tail bound and `b` the cell's true pivot at `last`: wherever the computed bounding
sequence is positive, the physical cell's pivot is positive. -/
theorem pos_of_pos_of_le (d : Fin (n+1) → ℝ) (s lam : ℝ) {a b : ℝ} (hab : a ≤ b)
    (hpos : ∀ i, 0 < pivotSeqFrom d s lam a i) (i : Fin (n+1)) :
    0 < pivotSeqFrom d s lam b i :=
  lt_of_lt_of_le (hpos i) (pivotSeqFrom_mono d s lam hab hpos i)

/-- **The truncating seed is the largest one**, which is why truncation is optimistic: the true pivot
at `last` is `d(last) − s − lam²/p(last+1)`, and for a positive pivot above it that is strictly less
than `d(last) − s`. Stated as the inequality the tail bound supplies. -/
lemma tail_seed_le_trunc_seed {d s lam pnext : ℝ} (h : 0 < pnext) :
    (d - s) - lam^2 / pnext ≤ d - s := by
  have : 0 ≤ lam^2 / pnext := by positivity
  linarith

/-- **Monotonicity ABOVE a cut**, which is the form the certificate actually needs.

The global version above assumes the bounding sequence is positive at *every* index. The certificate's
sequences are not: the whole point of the sign analysis is that one pivot (or, at strong coupling,
several) is negative. Monotonicity in the seed propagates downward only through positive pivots — a
negative pivot flips the direction of `lam²/q` — so the conclusion is available exactly on the
positive region, and that region is an upper segment.

So: assume positivity only from `k` upward, and conclude only from `k` upward. -/
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

/-- **Positivity of the physical cell's pivots above the cut.** With `seedLo` a lower bound on the
cell's true pivot at `last`, every index at or above `k` where the computed bounding sequence is
positive has a positive pivot in the cell itself.

This is what the certificate's sign analysis needs transported: the negative pivots are counted below
`k`, and everything above them is positive in the real cell and not merely in its truncation. -/
theorem pos_above_of_tail (d : Fin (n+1) → ℝ) (s lam seedLo seedTrue : ℝ)
    (hle : seedLo ≤ seedTrue) (k : Fin (n+1))
    (hposLo : ∀ i, k ≤ i → 0 < pivotSeqFrom d s lam seedLo i) :
    ∀ i, k ≤ i → 0 < pivotSeqFrom d s lam seedTrue i := fun i hki =>
  lt_of_lt_of_le (hposLo i hki) (pivotSeqFrom_mono_above d s lam hle k hposLo i hki)

/-- **The tail stays above `eps` — whatever the seed, and however deep the truncation.**

This is the Lean side of `cell_pivot_certificate.tail_start`, and it is what makes the tail argument
independent of where one truncates.

The self-consistency hypothesis is `lam² ≤ eps·(dᵢ − s − eps)` above the cut. Read it as: the Casimir
diagonal has grown far enough past the shift that the coupling can no longer push a pivot below `eps`.
Since `dᵢ = i(i+2)/4` grows quadratically while `lam` is fixed, it holds for every index past some
`m` — and `tail_start` returns the least such `m`, derived per coupling rather than chosen.

Given it, ONE step of the recurrence cannot fall below `eps`: if the pivot above is at least `eps`
then `lam²/p ≤ lam²/eps ≤ dᵢ − s − eps`, so `(dᵢ − s) − lam²/p ≥ eps`. Downward induction does the
rest, and the SEED only has to clear `eps` — it is not otherwise constrained.

**Why this is the truncation-independent statement.** A deeper truncation seeds the same recurrence
higher up. Its pivots at the tail indices are therefore also `≥ eps` by this lemma, with no reference
to how deep it goes; so the bound one truncation computes is a bound for every deeper one. That is
what `pos_above_of_tail` then propagates downward into the certified region. -/
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

/-- **Positivity of the tail**, the form `pos_above_of_tail` consumes. Immediate from the bound. -/
theorem pivotSeqFrom_pos_of_selfconsistent (d : Fin (n+1) → ℝ) (s lam eps : ℝ) (heps : 0 < eps)
    (k : Fin (n+1))
    (hcons : ∀ i : Fin n, k ≤ i.castSucc → lam^2 ≤ eps * (d i.castSucc - s - eps))
    {seed : ℝ} (hseed : eps ≤ seed) :
    ∀ i, k ≤ i → 0 < pivotSeqFrom d s lam seed i := fun i hki =>
  lt_of_lt_of_le heps (pivotSeqFrom_ge_of_selfconsistent d s lam eps heps k hcons hseed i hki)

/-- **The inertia hypothesis, from a FINITE block check plus the tail inequality.**

This is the join the certificate was missing. `gap_of_ldl_one_neg_pivot` consumes
`hp : ∀ i ≠ m, 0 ≤ p i` — a statement about EVERY index. The certificate can only ever check finitely
many, and `cell_pivot_certificate` checks a block and then argues about the rest. Here the argument
becomes the proof:

* ABOVE the cut `k`, positivity is not checked at all — it follows from the self-consistency
  inequality `lam² ≤ eps·(dᵢ − s − eps)`, which `tail_start` solves for the least such cut, via
  `pivotSeqFrom_ge_of_selfconsistent`;
* BELOW the cut, the pivots are a finite list and `hbelow` is the certificate's own sign check.

So the hypothesis is assembled from a finite computation and one inequality, with nothing assumed
about the indices between. Note what is NOT needed: any relation between truncations. The statement
lives entirely inside one `Fin (n+1)` and holds at every `n` — a deeper truncation satisfies its own
instance with the same `eps` and the same cut, which is what makes the bound truncation-independent
without ever transporting across index types. -/
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
