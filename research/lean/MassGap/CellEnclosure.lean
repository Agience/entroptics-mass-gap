import Mathlib
import MassGap.Complete

/-!
# MassGap.CellEnclosure — the truncated single-plaquette matrix and an LDLᵀ certificate

Three groups of declarations.

**The matrix.** `Hcell jmax lam` is the symmetric tridiagonal matrix over `ℚ` of size
`dim jmax = 2 * jmax + 1`, with `i(i+2)/4` on the diagonal and `-lam` on both first off-diagonals.
Written in the character index `i = 2j`, so the diagonal is the `SU(2)` Casimir `j(j+1)`.
`Hcell_transpose` proves it equal to its own transpose.

**Arithmetic about `κ₀YM`.** `cell_clears_floor` gives `exp (-gap) ≤ 3 ^ (-1/4)` from `κ₀YM ≤ gap`,
and `cell_lt_one` gives `exp (-gap) < 1` from the same hypothesis. `κ₀YM_le_half` bounds
`κ₀YM ≤ 1/2`, and `twoState_gap_clears_floor` gives `κ₀YM ≤ 2√(9/64 + lam²)` at every real `lam`.
These are inequalities between real numbers; none of them mentions a matrix or an eigenvalue.

**The LDLᵀ machinery.** `posSemidef_of_ldl` states that a real matrix factoring as
`Lᵀ · diagonal d · L` with `d` nonnegative is positive semidefinite. `Lbi e` is the unit
lower-bidiagonal factor with multipliers `e`, `Lbi_apply` splits its entry into two indicators, and
`ldl_entry` computes `(Lbi e)ᵀ · diagonal p · (Lbi e)` entrywise, exhibiting it as symmetric
tridiagonal. `pivotSeq` and `multSeq` are the backward pivot recurrence
`p(last) = d(last) − s`, `p(i) = (d i − s) − lam²/p(i+1)` and the multipliers `e i = −lam/p i`;
`multSeq_pivot`, `pivotSeq_recurD`, `pivotSeq_hrecO` and `pivotSeq_hrecD_sum` are the recurrence
identities, each conditional on the relevant pivot being nonzero.

Scope: the LDLᵀ group is stated for arbitrary real matrices and arbitrary sequences `d`, `s`, `lam`,
with no connection to `Hcell` made in any statement — `Hcell` is over `ℚ` and the LDLᵀ lemmas are
over `ℝ`. No declaration here computes an eigenvalue, counts pivot signs, or asserts that any pivot
sequence is nonzero.
-/

namespace MassGap.CellEnclosure

open scoped Matrix

/-- The number of retained character states at truncation `jmax`: `2 * jmax + 1`. The states are
`j = 0, 1/2, …, jmax`, indexed by `i = 2j` running over `{0, …, 2 * jmax}`.

An `abbrev`, so it unfolds in the type `Fin (dim jmax)` without a rewrite.

DERIVED: `2` is the doubling in the index `i = 2j`, which makes the half-integer spins integral. `1`
counts the state `j = 0`, so the range `{0, …, 2 * jmax}` has `2 * jmax + 1` members; neither
numeral is a choice. -/
abbrev dim (jmax : ℕ) : ℕ := 2 * jmax + 1

/-- The `dim jmax`-square matrix over `ℚ` with `(i * (i + 2))/4` at `(i, i)`, `-lam` at every pair of
indices differing by one, and `0` elsewhere. In the character index `i = 2j` the diagonal is the
`SU(2)` Casimir `j(j+1)`, and the off-diagonal is the nearest-neighbour coupling.

Entries are exact rationals, so no rounding enters. The matrix is a finite truncation: nothing
relates it to an untruncated operator.

DERIVED: `2` and `4` come from `j(j+1) = i(i+2)/4` under `i = 2j`, so they are the substitution's,
not chosen; `1` is the index difference that defines nearest-neighbour, in both orders; `0` is the
value at every other entry. -/
noncomputable def Hcell (jmax : ℕ) (lam : ℚ) : Matrix (Fin (dim jmax)) (Fin (dim jmax)) ℚ :=
  Matrix.of fun i j =>
    if i = j then ((i.val : ℚ) * (i.val + 2)) / 4
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -lam
    else 0

/-- `(Hcell jmax lam)ᵀ = Hcell jmax lam`. Entrywise: the diagonal case is symmetric by `rfl`, and the
off-diagonal guard `i + 1 = j ∨ j + 1 = i` is invariant under swapping the two indices, by
`or_comm`.

Transposition over `ℚ`, so this is symmetry; the conjugation of Hermiticity is trivial here.

DERIVED: no numeral. Every literal belongs to `Hcell` and is carried through its definition. -/
theorem Hcell_transpose (jmax : ℕ) (lam : ℚ) : (Hcell jmax lam)ᵀ = Hcell jmax lam := by
  ext i j
  simp only [Matrix.transpose_apply, Hcell, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij; rfl
  · rw [if_neg (show ¬ j = i from fun h => hij h.symm), if_neg hij]
    exact if_congr or_comm rfl rfl

/-- For any real `gap` with `κ₀YM ≤ gap`, `Real.exp (-gap) ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4)`. The right
side is rewritten as `exp (-κ₀YM)` — this is where `κ₀YM = (1/4) log 3` is used — and the conclusion
is monotonicity of `exp` applied to `-gap ≤ -κ₀YM`.

`gap` is an arbitrary real subject only to the hypothesis. The statement does not mention a matrix,
an eigenvalue or `Hcell`, and nothing here establishes that any particular gap satisfies `h`.

DERIVED: `3` is the base of the constant `κ₀YM` exponentiates, and `-(1)/4` its exponent, so the `1`
and `4` are the reciprocal weight in `(1/4) log 3`; `3 ^ (-(1)/4)` is exactly `exp (-κ₀YM)`, which is
what the proof's rewrite establishes. -/
theorem cell_clears_floor {gap : ℝ} (h : κ₀YM ≤ gap) :
    Real.exp (-gap) ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
  have h3 : (3 : ℝ) ^ (-(1 : ℝ) / 4) = Real.exp (-κ₀YM) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]; unfold κ₀YM; congr 1; ring
  rw [h3]
  exact Real.exp_le_exp.mpr (by linarith)

/-- For any real `gap` with `κ₀YM ≤ gap`, `Real.exp (-gap) < 1`. `κ₀YM_pos` makes `gap` positive, so
`-gap < 0` and `exp (-gap) < exp 0 = 1`.

The strict positivity of `κ₀YM` is what the proof consumes; the hypothesis `κ₀YM ≤ gap` is stronger
than needed, since `0 < gap` alone would do.

DERIVED: `1` is the value of `exp` at `0`, the upper bound asserted; it is the only numeral. -/
theorem cell_lt_one {gap : ℝ} (h : κ₀YM ≤ gap) : Real.exp (-gap) < 1 := by
  have hpos : 0 < gap := lt_of_lt_of_le κ₀YM_pos h
  calc Real.exp (-gap) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

/-- `κ₀YM ≤ 1 / 2`. The proof first identifies `κ₀YM = (1/4) * Real.log 3`, by taking `-log` of the
identity `3 ^ (-(1)/4) = exp (-κ₀YM)`, and then uses `Real.log_le_sub_one_of_pos` in the form
`log 3 ≤ 3 - 1 = 2`.

A numeric upper bound, not the value: `κ₀YM` is strictly below `1/2`, and this states only the
non-strict inequality.

DERIVED: `1` and `2` are the numerator and denominator of the bound, obtained by halving the crude
estimate `log 3 ≤ 2` against the weight `1/4`; that estimate is `log x ≤ x - 1` at `x = 3`, so the
bound is `(1/4) * 2` and neither numeral is chosen independently. -/
theorem κ₀YM_le_half : κ₀YM ≤ 1 / 2 := by
  have hlog : Real.log 3 ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h3 : (3 : ℝ) ^ (-(1 : ℝ) / 4) = Real.exp (-κ₀YM) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]; unfold κ₀YM; congr 1; ring
  have : κ₀YM = (1 / 4) * Real.log 3 := by
    have := congrArg (fun t => -Real.log t) h3
    simp only [Real.log_exp] at this
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 3)] at this
    linarith [this]
  rw [this]; linarith

/-- `κ₀YM ≤ 2 * Real.sqrt (9 / 64 + lam ^ 2)`, for every real `lam`. From
`√(9/64 + lam²) ≥ √(9/64) = 3/8` by monotonicity of the square root, together with
`κ₀YM_le_half`, giving `κ₀YM ≤ 1/2 ≤ 3/4 ≤ 2√(9/64 + lam²)`.

Scope: an inequality between `κ₀YM` and a real expression in `lam`. It mentions no matrix and no
eigenvalue, and nothing here identifies `2√(9/64 + lam²)` with the spectral gap of any matrix. The
expression is the gap of the two-state truncation `[[0, −lam], [−lam, 3/4]]`, whose eigenvalues are
`3/8 ± √(9/64 + lam²)`, but that eigenvalue computation is not performed in this file.

DERIVED: `2` multiplies the square root because a symmetric `2 × 2` matrix's two eigenvalues are its
mean plus and minus the same radius, so the gap is twice that radius; the exponent `2` squares `lam`.
`9 / 64` is `(3/8)²`, the square of half the two-state diagonal entry `3/4`, and `3/4` is the Casimir
at `j = 1/2`; so `9` and `64` are that square and not independent choices. -/
theorem twoState_gap_clears_floor (lam : ℝ) : κ₀YM ≤ 2 * Real.sqrt (9 / 64 + lam ^ 2) := by
  have h38 : Real.sqrt (9 / 64 : ℝ) = 3 / 8 := by
    rw [show (9 / 64 : ℝ) = (3 / 8) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hmono : Real.sqrt (9 / 64 : ℝ) ≤ Real.sqrt (9 / 64 + lam ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg lam])
  rw [h38] at hmono
  have hk := κ₀YM_le_half
  linarith

/-! ## The LDLᵀ factorisation machinery

Declarations about the completing-the-square factorisation `T = Lᵀ · diagonal d · L` of a symmetric
tridiagonal real matrix. `posSemidef_of_ldl` reads a nonnegative pivot diagonal as positive
semidefiniteness of `T`; `Lbi`, `Lbi_apply` and `ldl_entry` give the unit lower-bidiagonal factor and
compute the product entrywise.

Everything in this subsection is over `ℝ` and stated for arbitrary matrices and sequences. No
statement refers to `Hcell`, to a shift `Hcell − s • I`, or to an eigenvalue. -/

open Matrix in
/-- A real square matrix `T` equal to `Lᵀ * Matrix.diagonal d * L`, with every `d i` nonnegative, is
positive semidefinite. `Matrix.posSemidef_diagonal_iff` gives `diagonal d` positive semidefinite, and
`PosSemidef.conjTranspose_mul_mul_same` transports it along `L`, the conjugate transpose coinciding
with the transpose over `ℝ`.

`T`, `L` and `d` are arbitrary: `L` need not be invertible or triangular, and no relation to `Hcell`
or to a shift is assumed or concluded.

DERIVED: `0` is the lower bound each pivot `d i` must meet; it is the only numeral, and it is exactly
the property that makes `diagonal d` positive semidefinite. -/
theorem posSemidef_of_ldl {n : ℕ} (T L : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hT : T = Lᵀ * Matrix.diagonal d * L) : T.PosSemidef := by
  have hD : (Matrix.diagonal d).PosSemidef := (Matrix.posSemidef_diagonal_iff).2 hd
  have hLT : (L)ᴴ = Lᵀ := by ext i j; simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hpsd := hD.conjTranspose_mul_mul_same L
  rw [hLT] at hpsd
  rwa [hT]

/-- The unit lower-bidiagonal matrix with multipliers `e`: `1` at `(i, i)`, `e i` at `(i, i - 1)`,
and `0` elsewhere. `ldl_entry` computes `(Lbi e)ᵀ · diagonal p · (Lbi e)` and exhibits it as the
symmetric tridiagonal matrix whose pivots are `p`.

`e` is arbitrary. Being unit triangular, `Lbi e` is invertible for every `e`.

DERIVED: `1` is the diagonal entry, which is what makes the factor unit triangular; `0` is the entry
at every index pair other than the diagonal and the first subdiagonal; the index offset `1` in
`j.val + 1 = i.val` is what places `e i` on that subdiagonal. -/
def Lbi {n : ℕ} (e : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if j = i then 1 else if j.val + 1 = i.val then e i else 0

/-- `(Lbi e) a b` rewritten as a sum of two indicators: `1` when `a = b`, plus `e a` when
`a.val = b.val + 1`. The two guards are mutually exclusive, so the sum has at most one nonzero term;
the case analysis is closed by `omega` on the index values.

The nested `if` of `Lbi` is replaced by an additive form, which is what lets `ldl_entry` distribute
the matrix product over the sum.

DERIVED: `1` is the diagonal value and, separately, the index offset selecting the subdiagonal; `0`
is the value of each indicator off its own guard. All are `Lbi`'s, restated. -/
lemma Lbi_apply {n : ℕ} (e : Fin n → ℝ) (a b : Fin n) :
    (Lbi e) a b = (if a = b then (1:ℝ) else 0) + (if a.val = b.val + 1 then e a else 0) := by
  unfold Lbi
  simp only [Matrix.of_apply]
  by_cases h1 : a = b
  · have hv : a.val = b.val := by rw [h1]
    rw [if_pos h1.symm, if_pos h1, if_neg (show ¬ a.val = b.val + 1 by omega)]; ring
  · have hba : ¬ b = a := fun h => h1 h.symm
    rw [if_neg hba, if_neg h1]
    by_cases h2 : a.val = b.val + 1
    · rw [if_pos h2, if_pos (show b.val + 1 = a.val by omega)]; ring
    · rw [if_neg h2, if_neg (show ¬ b.val + 1 = a.val by omega)]; ring

/-- Two nested `if`s over a `0` default commute: `if A then (if B then x else 0) else 0` equals
`if B then (if A then x else 0) else 0`, for any real `x` and any decidable `A`, `B`. By `split_ifs`.

Used in `ldl_entry` to re-key a sum by the inner guard so that `Finset.sum_ite_eq'` can collapse it.

DERIVED: `0` is the default value on both sides, and the fact that it is the same on both branches is
what makes the two nestings interchangeable. -/
lemma ite_ite_comm {A B : Prop} [Decidable A] [Decidable B] (x : ℝ) :
    (if A then (if B then x else 0) else 0) = (if B then (if A then x else 0) else 0) := by
  split_ifs <;> rfl

/-- The entry of `(Lbi e)ᵀ * Matrix.diagonal p * (Lbi e)` at `(i, j)`, as a sum of four indicator
terms: `p i` on the diagonal, `p i * e i` one below it, `e j * p j` one above it, and the correction
`∑ₖ [k = i+1 ∧ k = j+1] eₖ * (pₖ * eₖ)`, which is nonzero only at `i = j`. Proved by expanding
`Matrix.mul_apply`, rewriting both factors with `Lbi_apply`, and collapsing each sum with
`Finset.sum_ite_eq'`.

So the product is symmetric tridiagonal with pivots `p` and multipliers `e`. The correction is
written as a sum rather than evaluated, because it is empty at the last index; the two off-diagonal
terms are written in opposite factor orders, matching the two transposed occurrences of `Lbi e`.

DERIVED: `0` is the value of each indicator off its own guard; the index offsets `1` place the
sub-diagonal, super-diagonal and correction terms one step from the diagonal. All belong to `Lbi`'s
bidiagonal structure. -/
theorem ldl_entry {n : ℕ} (p e : Fin n → ℝ) (i j : Fin n) :
    ((Lbi e)ᵀ * Matrix.diagonal p * (Lbi e)) i j
      = (if i = j then p i else 0) + (if i.val = j.val + 1 then p i * e i else 0)
        + (if j.val = i.val + 1 then e j * p j else 0)
        + ∑ k, (if k.val = i.val + 1 ∧ k.val = j.val + 1 then e k * (p k * e k) else 0) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp_rw [Matrix.transpose_apply, Matrix.diagonal_mul, Lbi_apply, add_mul, mul_add,
    Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    ite_ite_comm, Finset.sum_ite_eq' Finset.univ i, Finset.sum_ite_eq' Finset.univ j,
    Finset.mem_univ, if_true, ← ite_and]
  ring

/-! ### The pivot and multiplier sequences

The LDLᵀ pivots as explicit functions of a diagonal `d`, a shift `s` and a coupling `lam`, via the
backward recurrence `p(last) = d(last) − s`, `p(i) = (d i − s) − lam²/p(i+1)` (`pivotSeq`), with
multipliers `e i = −lam / p i` (`multSeq`).

`pivotSeq_recurD` and `multSeq_pivot` are the diagonal and off-diagonal recurrence identities, and
`pivotSeq_hrecD_sum`, `pivotSeq_hrecO` restate them in the shape `ldl_entry` produces. Each is
conditional on the relevant pivot being nonzero, passed in as a hypothesis; no statement here
establishes that any pivot is nonzero, or determines the sign of any pivot. `d`, `s` and `lam` are
arbitrary reals. -/

/-- The backward pivot sequence on `Fin (n + 1)`, built by `Fin.reverseInduction`: the value at
`Fin.last n` is `d (Fin.last n) - s`, and at `i.castSucc` it is `(d i.castSucc - s) - lam² / p i.succ`.

Defined unconditionally. Division in `ℝ` by `0` returns `0`, so the recurrence is total even where a
pivot vanishes; the lemmas that read it back take a nonvanishing hypothesis.

DERIVED: `1` in `Fin (n + 1)` makes the index type nonempty, which the reverse induction needs for
its base case at `Fin.last n`. The exponent `2` squares `lam` because the correction is the product
of the off-diagonal entry with itself, divided by the next pivot. -/
noncomputable def pivotSeq {n : ℕ} (d : Fin (n+1) → ℝ) (s lam : ℝ) : Fin (n+1) → ℝ :=
  Fin.reverseInduction (d (Fin.last n) - s) (fun i pnext => (d i.castSucc - s) - lam^2 / pnext)

@[simp] lemma pivotSeq_last {n : ℕ} (d : Fin (n+1) → ℝ) (s lam : ℝ) :
    pivotSeq d s lam (Fin.last n) = d (Fin.last n) - s := by
  simp [pivotSeq]

lemma pivotSeq_castSucc {n : ℕ} (d : Fin (n+1) → ℝ) (s lam : ℝ) (i : Fin n) :
    pivotSeq d s lam i.castSucc = (d i.castSucc - s) - lam^2 / (pivotSeq d s lam i.succ) := by
  simp [pivotSeq]

/-- The multiplier sequence `e i = -lam / pivotSeq d s lam i` on `Fin (n + 1)`.

Total: where the pivot is `0`, the multiplier is `0` by the convention on division in `ℝ`.

DERIVED: `1` in `Fin (n + 1)` is `pivotSeq`'s index type, carried unchanged; the definition
introduces no literal of its own. -/
noncomputable def multSeq {n : ℕ} (d : Fin (n+1) → ℝ) (s lam : ℝ) : Fin (n+1) → ℝ :=
  fun i => -lam / pivotSeq d s lam i

/-- `-lam = multSeq d s lam i * pivotSeq d s lam i`, provided the pivot at `i` is nonzero. Unfolds
`multSeq` and clears the division with `field_simp`.

The hypothesis `hp` is essential: at a vanishing pivot both sides of the product are `0` while `-lam`
need not be.

DERIVED: `0` is the value the pivot is required to differ from in `hp`. `1` in `Fin (n + 1)` is
`pivotSeq`'s index type. -/
lemma multSeq_pivot {n : ℕ} (d : Fin (n+1) → ℝ) (s lam : ℝ) (i : Fin (n+1))
    (hp : pivotSeq d s lam i ≠ 0) :
    -lam = multSeq d s lam i * pivotSeq d s lam i := by
  unfold multSeq; field_simp

/-- `d i.castSucc - s = pivotSeq d s lam i.castSucc + (multSeq d s lam i.succ)² * pivotSeq d s lam i.succ`,
provided the pivot at `i.succ` is nonzero. Rewrites by `pivotSeq_castSucc`, unfolds `multSeq`, and
clears the division.

This is the diagonal half of the factorisation: the shifted diagonal entry is the pivot plus the
contribution the next multiplier makes to it. Stated for `i : Fin n`, so it does not reach the last
index, where there is no next pivot.

DERIVED: `0` is the value the next pivot is required to differ from in `hp`. The exponent `2` squares
the multiplier, matching the correction term of `ldl_entry`, where `e` appears on both sides of the
pivot. `1` in `Fin (n + 1)` is the index type of `d` and of the sequences. -/
lemma pivotSeq_recurD {n : ℕ} (d : Fin (n+1) → ℝ) (s lam : ℝ) (i : Fin n)
    (hp : pivotSeq d s lam i.succ ≠ 0) :
    d i.castSucc - s =
      pivotSeq d s lam i.castSucc + (multSeq d s lam i.succ)^2 * pivotSeq d s lam i.succ := by
  rw [pivotSeq_castSucc]; unfold multSeq; field_simp; ring

/-- `multSeq_pivot` restated with all pivots assumed nonzero and with an index hypothesis
`j.val = i.val + 1` that the conclusion does not use: `-lam = multSeq d s lam j * pivotSeq d s lam j`.
The body is `multSeq_pivot` at `j`.

The unused index hypothesis is there to match the shape an off-diagonal rewrite consumes; the
conclusion holds at every `j` under `hnz`.

DERIVED: `0` is the value every pivot is required to differ from in `hnz`. The offset `1` in
`j.val = i.val + 1` names the first subdiagonal, the position this identity is used at. `1` in
`Fin (n + 1)` is the index type. -/
lemma pivotSeq_hrecO {n : ℕ} (d : Fin (n+1) → ℝ) (s lam : ℝ)
    (hnz : ∀ i : Fin (n+1), pivotSeq d s lam i ≠ 0) (i j : Fin (n+1)) (_ : j.val = i.val + 1) :
    -lam = multSeq d s lam j * pivotSeq d s lam j :=
  multSeq_pivot d s lam j (hnz j)

/-- `pivotSeq_recurD` restated with the correction written as the indicator sum `ldl_entry` produces:
with every pivot nonzero,

    d i - s = pivotSeq d s lam i + ∑ₖ [k.val = i.val + 1] eₖ * (pₖ * eₖ).

By `Fin.lastCases`. At `Fin.last n` the sum is empty, because no index exceeds the last, and the
identity is `pivotSeq_last`; at `i.castSucc` the sum collapses to its `i.succ` term by
`Finset.sum_eq_single` and the identity is `pivotSeq_recurD`.

DERIVED: `0` is the value every pivot is required to differ from in `hnz`, and the default value of
the summand off its guard. The offset `1` in `k.val = i.val + 1` selects the next index, so the sum
has exactly one term below the last index and none at it. `1` in `Fin (n + 1)` is the index type. -/
lemma pivotSeq_hrecD_sum {n : ℕ} (d : Fin (n+1) → ℝ) (s lam : ℝ)
    (hnz : ∀ i : Fin (n+1), pivotSeq d s lam i ≠ 0) (i : Fin (n+1)) :
    d i - s = pivotSeq d s lam i + ∑ k, if k.val = i.val + 1 then
      multSeq d s lam k * (pivotSeq d s lam k * multSeq d s lam k) else 0 := by
  induction i using Fin.lastCases with
  | last =>
    have hsum : (∑ k : Fin (n+1), if k.val = (Fin.last n).val + 1 then
        multSeq d s lam k * (pivotSeq d s lam k * multSeq d s lam k) else 0) = 0 := by
      apply Finset.sum_eq_zero; intro k _
      rw [if_neg]; have := k.isLt; simp only [Fin.val_last]; omega
    rw [hsum, pivotSeq_last]; ring
  | cast i' =>
    have hsum : (∑ k : Fin (n+1), if k.val = (i'.castSucc).val + 1 then
        multSeq d s lam k * (pivotSeq d s lam k * multSeq d s lam k) else 0)
        = multSeq d s lam i'.succ * (pivotSeq d s lam i'.succ * multSeq d s lam i'.succ) := by
      rw [Finset.sum_eq_single i'.succ]
      · rw [if_pos]; simp [Fin.val_succ]
      · intro k _ hk; rw [if_neg]; intro hc; apply hk
        apply Fin.ext; simp only [Fin.val_succ, Fin.val_castSucc] at hc ⊢; omega
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum]
    have hrec := pivotSeq_recurD d s lam i' (hnz i'.succ)
    rw [hrec]; ring

end MassGap.CellEnclosure
