import Mathlib
import MassGap.Existence

/-!
# MassGap.Measure — counting resolved modes, and subsequential limits of bounded real families

Two pieces of arithmetic, combined.

**The count.** `resolvedDim s ev edge` is the number of indices `k ∈ s` with `edge < ev k`, as a
`Finset.card`. `resolvedDim_le_of_signal` bounds it by the size of any set covering those indices;
`ir_count_spacing_indep` bounds the number of naturals `n < N` with `(n : ℝ) < c` by `⌈c⌉₊`,
independently of `N`; `resolvedDim_le_of_gap` combines the two, and `uniform_resolvedDim` and
`uniform_resolvedDim_of_gap` state them over a family indexed by `a`. `index_lt_of_sorted_count` and
`os_gap_of_sorted_count` run the implication the other way, from a bound on the count to a bound on
the index, using the hypothesis `hsorted` that `ev` is nonincreasing.

**The limit.** `tight_of_uniform_resolved` takes a real sequence `Q` with `0 ≤ Q n` and
`Q n ≤ resolvedDim … * B`, and a uniform bound on that dimension, and produces a convergent
subsequence with limit in `[0, K * B]`, through `Existence.tight_limit_rp`. `tight_of_gap_signal`,
`tight_of_gap_ir` and `tight_vector_of_gap_ir` are the same over the two count routes and over a
countable family of sequences; `continuum_limit_of_gap` adds two invariance hypotheses `hEuc` and
`hPerm` and carries them to the limit through `Existence.invariant_limit_of_action`.

`LatticeYMFamily` bundles the hypotheses of `continuum_limit_of_gap` as a structure;
`continuum_of_family` applies it. `familyOfSortedCount` builds such a structure from `hsorted` and a
count bound instead of from the index bound `os_gap`, and `continuum_of_sorted_count` is the
composition.

## Scope

Every statement is about `Finset.card`, real sequences and filters. No statement mentions a lattice,
a gauge group, a correlation function, a spacing, a spectral gap, a Schwinger function or a
renormalisation; `ev`, `edge`, `c`, `B`, `Q`, `Na`, `actE` and `actP` are arbitrary, and the
intended readings — eigenvalues, a noise edge, an infrared cutoff, a per-mode bound, reflected forms,
a mode count, and Euclidean and permutation actions — enter only through the names.

The limits obtained are subsequential: a strictly monotone `φ` and a limit along it. Nothing asserts
convergence of the full sequence, and `actE`, `actP` are arbitrary functions with no group structure
required of `G` or `P`.
-/

namespace MassGap.Measure

open MassGap Filter
open scoped Classical

/-- The number of indices `k` in the `Finset` `s` with `edge < ev k`, as a `Finset.card`. `ι` is any
type, `ev : ι → ℝ` any function and `edge` any real; the strict inequality means an index at exactly
`edge` is not counted.

DERIVED: no numeral. `s`, `ev` and `edge` are the caller's. -/
noncomputable def resolvedDim {ι : Type*} (s : Finset ι) (ev : ι → ℝ) (edge : ℝ) : ℕ :=
  (s.filter (fun k => edge < ev k)).card

/-- If a `Finset` `sig` of cardinality at most `K` contains every `k ∈ s` with `edge < ev k`, then
`resolvedDim s ev edge ≤ K`. The filtered set is a subset of `sig` by `hcover`, so
`Finset.card_le_card` applies.

`sig` is supplied by the caller and may be much larger than the filtered set; the bound is by `K`,
not by the count of covered indices.

DERIVED: no numeral. `K` is the caller's bound, a variable. -/
theorem resolvedDim_le_of_signal {ι : Type*} (s : Finset ι) (ev : ι → ℝ) (edge : ℝ)
    {K : ℕ} (sig : Finset ι) (hcard : sig.card ≤ K)
    (hcover : ∀ k ∈ s, edge < ev k → k ∈ sig) :
    resolvedDim s ev edge ≤ K := by
  refine le_trans (Finset.card_le_card ?_) hcard
  intro k hk
  rw [Finset.mem_filter] at hk
  exact hcover k hk.1 hk.2

/-- `resolvedDim_le_of_signal` applied at every index `n` of a family: if at each `n` the set `sig n`
has cardinality at most `K` and covers the supra-edge indices of `s n`, then
`resolvedDim (s n) (ev n) (edge n) ≤ K` for every `n`.

The same `K` at every `n`, which is what makes the bound uniform; the sets `sig n` may differ.

DERIVED: no numeral. `K` is the caller's uniform bound. -/
theorem uniform_resolvedDim {ι : Type*} {K : ℕ}
    (s : ℕ → Finset ι) (ev : ℕ → ι → ℝ) (edge : ℕ → ℝ)
    (sig : ℕ → Finset ι) (hcard : ∀ n, (sig n).card ≤ K)
    (hcover : ∀ n, ∀ k ∈ s n, edge n < ev n k → k ∈ sig n) :
    ∀ n, resolvedDim (s n) (ev n) (edge n) ≤ K :=
  fun n => resolvedDim_le_of_signal (s n) (ev n) (edge n) (sig n) (hcard n) (hcover n)

/-! ### A count that does not depend on the range

When the index set is `Finset.range N` and the covering condition is an index cutoff `(n : ℝ) < c`,
the covering set can be taken to be the indices below `c`, whose cardinality is at most `⌈c⌉₊`
whatever `N` is. That supplies the uniform `K` of `uniform_resolvedDim` without the caller choosing
one. -/

/-- The number of `n < N` with `(n : ℝ) < c` is at most `⌈c⌉₊`, for every `N`. Every such `n` lies in
`Finset.range ⌈c⌉₊` by `Nat.le_ceil`, so `Finset.card_le_card` against that range gives the bound.

The bound does not mention `N`, which is what makes it uniform over a family of ranges in
`uniform_resolvedDim_of_gap`.

DERIVED: no numeral. `c` is the caller's cutoff and `⌈c⌉₊` the least natural at or above it, so the
ceiling is what makes a real cutoff into a cardinality bound. -/
theorem ir_count_spacing_indep {c : ℝ} (N : ℕ) :
    ((Finset.range N).filter (fun n : ℕ => (n : ℝ) < c)).card ≤ ⌈c⌉₊ := by
  rw [← Finset.card_range ⌈c⌉₊]
  refine Finset.card_le_card (fun n hn => ?_)
  rw [Finset.mem_filter] at hn
  rw [Finset.mem_range]
  exact_mod_cast lt_of_lt_of_le hn.2 (Nat.le_ceil c)
/-- From a bound on the count to a bound on the index. If `ev` is nonincreasing (`hsorted`) and at
most `c` of its first `N` values exceed `edge` (`hcount`), then every `n < N` with `edge < ev n`
satisfies `(n : ℝ) < c`.

The ordering is what connects the two. A value above `edge` at index `n` forces every earlier index
to be above `edge` as well, so `Finset.range (n + 1)` embeds in the filtered set and the count is at
least `n + 1`; `linarith` against `hcount` then gives `(n : ℝ) < c`.

This runs in the opposite direction to `resolvedDim_le_of_gap`, which goes from an index bound to a
count bound. Without `hsorted` the two are not interchangeable.

DERIVED: no numeral. `c`, `edge` and `N` are the caller's, and `hcount` casts a `ℕ`-valued
cardinality into `ℝ` to compare it with `c`. The successor `n + 1` appears in the proof, where it is
the number of indices at or before `n`, and not in the statement. -/
theorem index_lt_of_sorted_count {ev : ℕ → ℝ} {edge c : ℝ} (N : ℕ)
    (hsorted : ∀ m n : ℕ, m ≤ n → ev n ≤ ev m)
    (hcount : ((resolvedDim (Finset.range N) ev edge : ℕ) : ℝ) ≤ c) :
    ∀ n ∈ Finset.range N, edge < ev n → (n : ℝ) < c := by
  intro n hn hedge
  -- every index at or below `n` is also above the edge, by the ordering
  have hsub : Finset.range (n + 1) ⊆ (Finset.range N).filter (fun m => edge < ev m) := by
    intro m hm
    rw [Finset.mem_range] at hm
    rw [Finset.mem_range] at hn
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    exact lt_of_lt_of_le hedge (hsorted m n (by omega))
  have hcard : n + 1 ≤ resolvedDim (Finset.range N) ev edge := by
    have := Finset.card_le_card hsub
    simpa [resolvedDim, Finset.card_range] using this
  have : ((n : ℝ) + 1) ≤ ((resolvedDim (Finset.range N) ev edge : ℕ) : ℝ) := by
    exact_mod_cast hcard
  linarith [this, hcount]

#print axioms index_lt_of_sorted_count

/-- `index_lt_of_sorted_count` applied at every index `a` of a family: from `ev a` nonincreasing and
its supra-edge count bounded by `c` at each `a`, the index bound `(n : ℝ) < c` holds at each `a`.

The same shape as the `os_gap` field of `LatticeYMFamily`, which is how `familyOfSortedCount` uses
it. The bound `c` and the edge are the same at every `a`; the ranges `Na a` may differ.

DERIVED: no numeral. `c`, `edge` and `Na` are the caller's. -/
theorem os_gap_of_sorted_count {ev : ℕ → ℕ → ℝ} {edge c : ℝ} (Na : ℕ → ℕ)
    (hsorted : ∀ a, ∀ m n : ℕ, m ≤ n → ev a n ≤ ev a m)
    (hcount : ∀ a, ((resolvedDim (Finset.range (Na a)) (ev a) edge : ℕ) : ℝ) ≤ c) :
    ∀ a, ∀ n ∈ Finset.range (Na a), edge < ev a n → (n : ℝ) < c :=
  fun a => index_lt_of_sorted_count (Na a) (hsorted a) (hcount a)

#print axioms os_gap_of_sorted_count


/-- If every `n < N` with `edge < ev n` satisfies `(n : ℝ) < c`, then
`resolvedDim (Finset.range N) ev edge ≤ ⌈c⌉₊`. `resolvedDim_le_of_signal` with the covering set taken
to be the indices below `c`, whose cardinality `ir_count_spacing_indep` bounds.

The bound does not mention `N`, so it is the same at every range. `hir` is a hypothesis: nothing here
establishes that any particular `ev` satisfies it.

DERIVED: no numeral. `c` is the caller's cutoff and `⌈c⌉₊` the ceiling that turns it into a
cardinality bound, both carried from `ir_count_spacing_indep`. -/
theorem resolvedDim_le_of_gap {ev : ℕ → ℝ} {edge c : ℝ} (N : ℕ)
    (hir : ∀ n ∈ Finset.range N, edge < ev n → (n : ℝ) < c) :
    resolvedDim (Finset.range N) ev edge ≤ ⌈c⌉₊ :=
  resolvedDim_le_of_signal (Finset.range N) ev edge
    ((Finset.range N).filter (fun n : ℕ => (n : ℝ) < c)) (ir_count_spacing_indep N)
    (fun k hk hedge => Finset.mem_filter.mpr ⟨hk, hir k hk hedge⟩)

/-- `resolvedDim_le_of_gap` at every index `a` of a family: from the index bound `hir` at each `a`,
`resolvedDim (Finset.range (Na a)) (ev a) edge ≤ ⌈c⌉₊` at each `a`.

The bound is the same natural number at every `a`, independent of `Na a`, which is the uniformity
`tight_of_gap_ir` consumes.

DERIVED: no numeral. `c` and `⌈c⌉₊` are `resolvedDim_le_of_gap`'s, carried unchanged. -/
theorem uniform_resolvedDim_of_gap {ev : ℕ → ℕ → ℝ} {edge c : ℝ} (Na : ℕ → ℕ)
    (hir : ∀ a, ∀ n ∈ Finset.range (Na a), edge < ev a n → (n : ℝ) < c) :
    ∀ a, resolvedDim (Finset.range (Na a)) (ev a) edge ≤ ⌈c⌉₊ :=
  fun a => resolvedDim_le_of_gap (Na a) (hir a)

/-- For a real sequence `Q` with `0 ≤ Q n`, `0 ≤ B`, `Q n ≤ resolvedDim (s n) (ev n) (edge n) * B`,
and that dimension bounded by `K` at every `n`, there exist `q ∈ [0, K * B]`, a strictly monotone
`φ : ℕ → ℕ`, and convergence of `Q ∘ φ` to `q`.

The two bounds compose to `Q n ≤ K * B` uniformly, and `Existence.tight_limit_rp` extracts the
convergent subsequence from a bounded nonnegative sequence.

Subsequential: `Q` itself need not converge. The index type `ι` and the data `s`, `ev`, `edge` enter
only through `hQ` and `hres`.

DERIVED: `0` is the lower bound on each `Q n` in `hrp`, on `B` in `hB`, and on the limit `q` in the
conclusion — the last is inherited from the first, since a limit of nonnegatives is nonnegative. `K`
and `B` are the caller's. -/
theorem tight_of_uniform_resolved {ι : Type*} {Q : ℕ → ℝ} {K : ℕ} {B : ℝ}
    (s : ℕ → Finset ι) (ev : ℕ → ι → ℝ) (edge : ℕ → ℝ)
    (hrp : ∀ n, 0 ≤ Q n) (hB : 0 ≤ B)
    (hQ : ∀ n, Q n ≤ (resolvedDim (s n) (ev n) (edge n) : ℝ) * B)
    (hres : ∀ n, resolvedDim (s n) (ev n) (edge n) ≤ K) :
    ∃ q, 0 ≤ q ∧ q ≤ (K : ℝ) * B ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (Q ∘ φ) atTop (nhds q) := by
  refine tight_limit_rp hrp (fun n => le_trans (hQ n) ?_)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hres n) hB

/-- `tight_of_uniform_resolved` with its `hres` hypothesis supplied by `uniform_resolvedDim`: given
covering sets `sig n` of cardinality at most `K`, the same conclusion — a limit `q ∈ [0, K * B]` along
a strictly monotone subsequence.

The covering route to the uniform bound; `tight_of_gap_ir` is the index-cutoff route to the same
shape.

DERIVED: `0` is the lower bound on each `Q n`, on `B`, and on the limit. `K` and `B` are the
caller's. -/
theorem tight_of_gap_signal {ι : Type*} {Q : ℕ → ℝ} {K : ℕ} {B : ℝ}
    (s : ℕ → Finset ι) (ev : ℕ → ι → ℝ) (edge : ℕ → ℝ) (sig : ℕ → Finset ι)
    (hcard : ∀ n, (sig n).card ≤ K)
    (hcover : ∀ n, ∀ k ∈ s n, edge n < ev n k → k ∈ sig n)
    (hrp : ∀ n, 0 ≤ Q n) (hB : 0 ≤ B)
    (hQ : ∀ n, Q n ≤ (resolvedDim (s n) (ev n) (edge n) : ℝ) * B) :
    ∃ q, 0 ≤ q ∧ q ≤ (K : ℝ) * B ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (Q ∘ φ) atTop (nhds q) :=
  tight_of_uniform_resolved s ev edge hrp hB hQ
    (uniform_resolvedDim s ev edge sig hcard hcover)

/-- `tight_of_uniform_resolved` with its `hres` hypothesis supplied by `uniform_resolvedDim_of_gap`:
from the index cutoff `hir`, nonnegativity of `Q` and `B`, and `hQ`, there is a limit
`q ∈ [0, ⌈c⌉₊ * B]` along a strictly monotone subsequence.

Here the uniform bound is `⌈c⌉₊`, computed from `c` rather than supplied by the caller; `hir` is the
only input that constrains `ev`.

DERIVED: `0` is the lower bound on each `Q a`, on `B`, and on the limit. `c` is the caller's index
cutoff, and `⌈c⌉₊` the ceiling carried from `uniform_resolvedDim_of_gap`. -/
theorem tight_of_gap_ir {Q : ℕ → ℝ} {ev : ℕ → ℕ → ℝ} {edge c B : ℝ} (Na : ℕ → ℕ)
    (hir : ∀ a, ∀ n ∈ Finset.range (Na a), edge < ev a n → (n : ℝ) < c)
    (hrp : ∀ a, 0 ≤ Q a) (hB : 0 ≤ B)
    (hQ : ∀ a, Q a ≤ (resolvedDim (Finset.range (Na a)) (ev a) edge : ℝ) * B) :
    ∃ q, 0 ≤ q ∧ q ≤ (⌈c⌉₊ : ℝ) * B ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (Q ∘ φ) atTop (nhds q) :=
  tight_of_uniform_resolved (fun a => Finset.range (Na a)) ev (fun _ => edge) hrp hB hQ
    (uniform_resolvedDim_of_gap Na hir)

/-- The vector form: for a countable index type `J` and a family of real sequences `Q j`, each
nonnegative and bounded by `resolvedDim … * B`, with the index cutoff `hir`, there is a single
strictly monotone `φ` along which every `Q j` converges, to a limit `q j ∈ [0, ⌈c⌉₊ * B]`.

`uniform_resolvedDim_of_gap` supplies `|Q j a| ≤ ⌈c⌉₊ * B` uniformly in both `j` and `a`;
`Existence.tight_limit_vector` diagonalises over the countable `J` to get one subsequence for all of
them, and `Existence.rp_of_tight_limit_vector` carries nonnegativity to each limit.

`Countable J` is what makes a single common subsequence available; the statement gives no rate and no
uniformity of convergence in `j`.

DERIVED: `0` is the lower bound on each `Q j a`, on `B`, and on each limit `q j`. `c` and `⌈c⌉₊` are
`uniform_resolvedDim_of_gap`'s. -/
theorem tight_vector_of_gap_ir {J : Type*} [Countable J] {Q : J → ℕ → ℝ}
    {ev : ℕ → ℕ → ℝ} {edge c B : ℝ} (Na : ℕ → ℕ)
    (hir : ∀ a, ∀ n ∈ Finset.range (Na a), edge < ev a n → (n : ℝ) < c)
    (hrp : ∀ j a, 0 ≤ Q j a) (hB : 0 ≤ B)
    (hQ : ∀ j a, Q j a ≤ (resolvedDim (Finset.range (Na a)) (ev a) edge : ℝ) * B) :
    ∃ q : J → ℝ, (∀ j, 0 ≤ q j) ∧ (∀ j, q j ≤ (⌈c⌉₊ : ℝ) * B) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j, Tendsto (fun k => Q j (φ k)) atTop (nhds (q j)) := by
  have h0 : 0 ≤ (⌈c⌉₊ : ℝ) * B := mul_nonneg (Nat.cast_nonneg _) hB
  have hbnd : ∀ j a, |Q j a| ≤ (⌈c⌉₊ : ℝ) * B := by
    intro j a
    rw [abs_le]
    refine ⟨by linarith [hrp j a], le_trans (hQ j a) ?_⟩
    refine mul_le_mul_of_nonneg_right ?_ hB
    exact_mod_cast uniform_resolvedDim_of_gap Na hir a
  obtain ⟨q, hq, φ, hmono, htend⟩ := tight_limit_vector (Q := Q) (C := (⌈c⌉₊ : ℝ) * B) hbnd
  exact ⟨q, rp_of_tight_limit_vector hrp htend, fun j => (abs_le.mp (hq j)).2, φ, hmono, htend⟩

/-- `tight_vector_of_gap_ir` with two invariance hypotheses added and carried to the limit. Given
`hir`, `hrp`, `hB`, `hQ` as before, plus `hEuc : Q (actE g j) a = Q j a` and
`hPerm : Q (actP σ j) a = Q j a` at every index, there are a strictly monotone `φ` and a limit `q`
with, for every `j`:

* `Q j (φ k) → q j`;
* `|q j| ≤ ⌈c⌉₊ * B`;
* `0 ≤ q j`;
* `q (actE g j) = q j` for every `g`;
* `q (actP σ j) = q j` for every `σ`.

The two invariances transfer by `Existence.invariant_limit_of_action`: an equality holding along the
whole sequence holds of its limit.

`G` and `P` are bare types and `actE`, `actP` bare functions — no group structure, no composition
law and no continuity is required or used, so the invariance transferred is exactly the pointwise
equality assumed.

DERIVED: `0` is the lower bound on each `Q j a`, on `B`, and on each limit `q j`. `c` and `⌈c⌉₊` are
carried from `uniform_resolvedDim_of_gap`. -/
theorem continuum_limit_of_gap {G P J : Type*} [Countable J]
    {Q : J → ℕ → ℝ} {ev : ℕ → ℕ → ℝ} {edge c B : ℝ} (Na : ℕ → ℕ)
    (actE : G → J → J) (actP : P → J → J)
    (hir : ∀ a, ∀ n ∈ Finset.range (Na a), edge < ev a n → (n : ℝ) < c)
    (hrp : ∀ j a, 0 ≤ Q j a) (hB : 0 ≤ B)
    (hQ : ∀ j a, Q j a ≤ (resolvedDim (Finset.range (Na a)) (ev a) edge : ℝ) * B)
    (hEuc : ∀ g j a, Q (actE g j) a = Q j a)
    (hPerm : ∀ σ j a, Q (actP σ j) a = Q j a) :
    ∃ (q : J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ j, Tendsto (fun k => Q j (φ k)) atTop (nhds (q j))) ∧
      (∀ j, |q j| ≤ (⌈c⌉₊ : ℝ) * B) ∧
      (∀ j, 0 ≤ q j) ∧
      (∀ g j, q (actE g j) = q j) ∧
      (∀ σ j, q (actP σ j) = q j) := by
  have hbnd : ∀ j a, |Q j a| ≤ (⌈c⌉₊ : ℝ) * B := by
    intro j a
    rw [abs_le]
    refine ⟨by linarith [hrp j a, mul_nonneg (Nat.cast_nonneg (⌈c⌉₊)) hB],
      le_trans (hQ j a) (mul_le_mul_of_nonneg_right ?_ hB)⟩
    exact_mod_cast uniform_resolvedDim_of_gap Na hir a
  obtain ⟨q, hq, φ, hmono, htend⟩ := tight_limit_vector (Q := Q) (C := (⌈c⌉₊ : ℝ) * B) hbnd
  exact ⟨q, φ, hmono, htend, hq, rp_of_tight_limit_vector hrp htend,
    invariant_limit_of_action htend actE hEuc, invariant_limit_of_action htend actP hPerm⟩

/-! ### The hypotheses as a structure

`continuum_limit_of_gap` takes its inputs loose. `LatticeYMFamily` bundles exactly the same data and
hypotheses into one structure, and `continuum_of_family` applies the theorem to a value of it. The
field names record the intended reading; the structure itself is a tuple of types, functions, reals
and inequalities. -/

/-- The data and hypotheses of `continuum_limit_of_gap`, as a structure: a countable type `J`, two
bare types `G` and `P` with actions on `J`, a range function `Na : ℕ → ℕ`, values `ev : ℕ → ℕ → ℝ`,
a family of real sequences `Q : J → ℕ → ℝ`, three reals `edge`, `c`, `B`, and the six hypotheses
`hB`, `os_rp`, `os_gap`, `os_form`, `os_euc`, `os_perm`.

Nothing in the structure is a lattice, a gauge field or a Schwinger function; every field is one of
the objects just listed, and every hypothesis is an inequality or an equality between reals. In
particular `os_gap` is assumed, not derived — `familyOfSortedCount` is the alternative constructor
that derives it from a count bound.

DERIVED: `0` is the lower bound on `B` in `hB` and on each `Q j a` in `os_rp`; it is the only
numeral in the structure. -/
structure LatticeYMFamily where
  /-- The index type of the family of sequences. -/
  J : Type
  /-- `J` is countable, which is what lets one subsequence serve every `j`. -/
  [countable : Countable J]
  /-- A type and an action of it on `J`, whose invariance `os_euc` asserts. No group structure. -/
  G : Type
  actE : G → J → J
  /-- A second type and action on `J`, whose invariance `os_perm` asserts. No group structure. -/
  P : Type
  actP : P → J → J
  /-- The upper end of the index range counted at each `a`. -/
  Na : ℕ → ℕ
  /-- The values compared against `edge` at each `a`. -/
  ev : ℕ → ℕ → ℝ
  /-- The family of real sequences whose limit is taken. -/
  Q : J → ℕ → ℝ
  /-- The threshold `ev` is compared against, the index cutoff, and the per-index factor. -/
  edge : ℝ
  c : ℝ
  B : ℝ
  hB : 0 ≤ B
  /-- Every `Q j a` is nonnegative. -/
  os_rp : ∀ j a, 0 ≤ Q j a
  /-- The index cutoff: an index below `Na a` whose value exceeds `edge` is below `c`. Assumed, not
  derived; `familyOfSortedCount` builds it from an ordering and a count instead. -/
  os_gap : ∀ a, ∀ n ∈ Finset.range (Na a), edge < ev a n → (n : ℝ) < c
  /-- Each `Q j a` is bounded by the resolved dimension at `a` times `B`. -/
  os_form : ∀ j a, Q j a ≤ (resolvedDim (Finset.range (Na a)) (ev a) edge : ℝ) * B
  /-- `Q` is invariant under `actE` in its first argument, at every index. -/
  os_euc : ∀ g j a, Q (actE g j) a = Q j a
  /-- `Q` is invariant under `actP` in its first argument, at every index. -/
  os_perm : ∀ σ j a, Q (actP σ j) a = Q j a

/-- Builds a `LatticeYMFamily` whose `os_gap` field is derived rather than supplied. In place of the
index cutoff it takes

* `hsorted` — each `ev a` is nonincreasing;
* `hcount` — at most `c` of the first `Na a` values exceed `edge`, at every `a`;

and fills `os_gap` with `os_gap_of_sorted_count Na hsorted hcount`. Every other field is passed
through unchanged.

So a caller who can bound the count, rather than locate the indices, can still build the structure.
`hsorted` is what makes the two interchangeable and is required.

DERIVED: `0` is the lower bound on `B` in `hB` and on each `Q j a` in `os_rp`, both carried from the
caller into the corresponding fields; the definition introduces no numeral of its own. -/
noncomputable def familyOfSortedCount
    (J : Type) [Countable J] (G : Type) (actE : G → J → J) (P : Type) (actP : P → J → J)
    (Na : ℕ → ℕ) (ev : ℕ → ℕ → ℝ) (Q : J → ℕ → ℝ) (edge c B : ℝ) (hB : 0 ≤ B)
    (hsorted : ∀ a, ∀ m n : ℕ, m ≤ n → ev a n ≤ ev a m)
    (hcount : ∀ a, ((resolvedDim (Finset.range (Na a)) (ev a) edge : ℕ) : ℝ) ≤ c)
    (os_rp : ∀ j a, 0 ≤ Q j a)
    (os_form : ∀ j a, Q j a ≤ (resolvedDim (Finset.range (Na a)) (ev a) edge : ℝ) * B)
    (os_euc : ∀ g j a, Q (actE g j) a = Q j a)
    (os_perm : ∀ σ j a, Q (actP σ j) a = Q j a) : LatticeYMFamily where
  J := J
  G := G
  actE := actE
  P := P
  actP := actP
  Na := Na
  ev := ev
  Q := Q
  edge := edge
  c := c
  B := B
  hB := hB
  os_rp := os_rp
  os_gap := os_gap_of_sorted_count Na hsorted hcount
  os_form := os_form
  os_euc := os_euc
  os_perm := os_perm

/-- `continuum_limit_of_gap` applied to the fields of a `LatticeYMFamily`. For any `F` there are a
strictly monotone `φ` and a limit `q : F.J → ℝ` with joint convergence of every `F.Q j` along `φ`,
`|q j| ≤ ⌈F.c⌉₊ * F.B`, `0 ≤ q j`, and invariance of `q` under `F.actE` and `F.actP`.

The `Countable F.J` instance is taken from the structure's own field.

DERIVED: `0` is the lower bound on each limit `q j`, inherited from the `os_rp` field. `F.c` and its
ceiling are the structure's, as is `F.B`. -/
theorem continuum_of_family (F : LatticeYMFamily) :
    ∃ (q : F.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ j, Tendsto (fun k => F.Q j (φ k)) atTop (nhds (q j))) ∧
      (∀ j, |q j| ≤ (⌈F.c⌉₊ : ℝ) * F.B) ∧
      (∀ j, 0 ≤ q j) ∧
      (∀ g j, q (F.actE g j) = q j) ∧
      (∀ σ j, q (F.actP σ j) = q j) :=
  haveI := F.countable
  continuum_limit_of_gap F.Na F.actE F.actP F.os_gap F.os_rp F.hB F.os_form F.os_euc F.os_perm

/-- `continuum_of_family` composed with `familyOfSortedCount`: from `hsorted`, `hcount`, `os_rp`,
`os_form`, `os_euc` and `os_perm`, there are a strictly monotone `φ` and a limit `q` with joint
convergence, `|q j| ≤ ⌈c⌉₊ * B`, `0 ≤ q j`, and invariance under `actE` and `actP`.

The same conclusion as `continuum_limit_of_gap`, reached from a count bound and an ordering instead
of from the index cutoff `hir`.

DERIVED: `0` is the lower bound on `B` in `hB`, on each `Q j a` in `os_rp`, and on each limit `q j`.
`c` is the caller's count bound and `⌈c⌉₊` its ceiling, carried through
`os_gap_of_sorted_count` and `uniform_resolvedDim_of_gap`. -/
theorem continuum_of_sorted_count
    (J : Type) [Countable J] (G : Type) (actE : G → J → J) (P : Type) (actP : P → J → J)
    (Na : ℕ → ℕ) (ev : ℕ → ℕ → ℝ) (Q : J → ℕ → ℝ) (edge c B : ℝ) (hB : 0 ≤ B)
    (hsorted : ∀ a, ∀ m n : ℕ, m ≤ n → ev a n ≤ ev a m)
    (hcount : ∀ a, ((resolvedDim (Finset.range (Na a)) (ev a) edge : ℕ) : ℝ) ≤ c)
    (os_rp : ∀ j a, 0 ≤ Q j a)
    (os_form : ∀ j a, Q j a ≤ (resolvedDim (Finset.range (Na a)) (ev a) edge : ℝ) * B)
    (os_euc : ∀ g j a, Q (actE g j) a = Q j a)
    (os_perm : ∀ σ j a, Q (actP σ j) a = Q j a) :
    ∃ (q : J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ j, Tendsto (fun k => Q j (φ k)) atTop (nhds (q j))) ∧
      (∀ j, |q j| ≤ (⌈c⌉₊ : ℝ) * B) ∧
      (∀ j, 0 ≤ q j) ∧
      (∀ g j, q (actE g j) = q j) ∧
      (∀ σ j, q (actP σ j) = q j) :=
  continuum_of_family (familyOfSortedCount J G actE P actP Na ev Q edge c B hB
    hsorted hcount os_rp os_form os_euc os_perm)

#print axioms continuum_of_sorted_count


end MassGap.Measure
