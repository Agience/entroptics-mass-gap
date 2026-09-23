import Mathlib

/-!
# Closed conditions on real sequences pass to their limits (PAPER §11)

Eight statements about sequences of reals indexed by `ℕ`, and families of such sequences. They are
the analytic shape of "an Osterwalder–Schrader condition is closed, so it survives the `a → 0`
limit", with `n : ℕ` standing for the lattice-spacing index and `Q n` for the value of a reflected
Schwinger form at that spacing.

* `rp_survives_limit` — a convergent sequence of nonnegative reals has a nonnegative limit.
* `tight_limit_rp` — a sequence confined to `[0, C]` has a subsequence converging to some `q` with
  `0 ≤ q ≤ C`.
* `tight_limit_vector` — a countably indexed family of sequences, each bounded in absolute value by
  a common `C`, has one subsequence along which every component converges, with `|q j| ≤ C`.
* `rp_of_tight_limit_vector` — componentwise nonnegativity passes to that joint limit.
* `symmetry_survives_limit`, `invariant_limit_of_action`, `os1_euclidean_survives`,
  `os3_symmetry_survives` — a reindexing of the index type that leaves every `Q j n` unchanged
  leaves the limit `q` unchanged, by uniqueness of limits.

Scope: every statement here is about real sequences. No Schwinger function, measure, lattice, test
function or reflection operator appears in any of them; the uniform bound `C` and the
finite-spacing nonnegativity are hypotheses supplied by the caller. The index `n` ranges over `ℕ`
with `Filter.atTop`, and nothing encodes a spacing `a` or its vanishing.
-/

namespace MassGap

/-- If `Q : ℕ → ℝ` is nonnegative at every index and converges to `q` along `Filter.atTop`, then
`0 ≤ q`. This is `ge_of_tendsto'` applied to the two hypotheses, and it is the statement that
`[0, ∞)` is closed.

Scope: `Q` and `q` are reals; nothing identifies `Q n` with a reflected form or `n` with a lattice
spacing.

DERIVED: `0` occurs twice, as the lower bound on each `Q n` and as the lower bound concluded for the
limit `q`. -/
theorem rp_survives_limit {Q : ℕ → ℝ} {q : ℝ}
    (hnn : ∀ n, 0 ≤ Q n) (hlim : Filter.Tendsto Q Filter.atTop (nhds q)) :
    0 ≤ q :=
  ge_of_tendsto' hlim hnn

/-!
## Subsequential limits of bounded sequences (PAPER §11)

Sequential compactness of `Set.Icc`, and of a countable product of copies of `Set.Icc`, in the form
used to extract a limit from a uniformly bounded family. The bound `C` is a hypothesis in both
statements below; nothing here derives one.
-/

/-- If `Q : ℕ → ℝ` satisfies `0 ≤ Q n` and `Q n ≤ C` at every `n`, there exist a real `q` with
`0 ≤ q` and `q ≤ C`, and a strictly monotone `φ : ℕ → ℕ` with `Q ∘ φ` converging to `q`. The proof
notes that every `Q n` lies in `Set.Icc (0 : ℝ) C` and applies `isCompact_Icc.tendsto_subseq`.

Scope: the conclusion is subsequential — nothing asserts that `Q` itself converges, and the limit
point is not claimed unique. `C` is a hypothesis, not constructed; if `C < 0` the two hypotheses are
jointly unsatisfiable and the statement is vacuous.

DERIVED: `0` occurs twice, as the lower bound on each `Q n` and as the lower bound on the limit `q`.
`C` is a bound variable, not a literal. -/
theorem tight_limit_rp {Q : ℕ → ℝ} {C : ℝ}
    (hrp : ∀ n, 0 ≤ Q n) (hbdd : ∀ n, Q n ≤ C) :
    ∃ q, 0 ≤ q ∧ q ≤ C ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ Filter.Tendsto (Q ∘ φ) Filter.atTop (nhds q) := by
  have hmem : ∀ n, Q n ∈ Set.Icc (0 : ℝ) C := fun n => ⟨hrp n, hbdd n⟩
  obtain ⟨q, hq, φ, hmono, htend⟩ := isCompact_Icc.tendsto_subseq hmem
  exact ⟨q, hq.1, hq.2, φ, hmono, htend⟩

/-- For a `Countable` index type `J` and a family `Q : J → ℕ → ℝ` with `|Q j n| ≤ C` for all `j` and
`n`, there exist `q : J → ℝ` with `|q j| ≤ C` and a single strictly monotone `φ : ℕ → ℕ` such that
`fun k => Q j (φ k)` converges to `q j` for every `j`. The proof places each `fun j => Q j n` in
`Set.pi Set.univ (fun _ => Set.Icc (-C) C)`, applies the `tendsto_subseq` of `isCompact_univ_pi`,
and reads off componentwise convergence with `tendsto_pi_nhds`.

Scope: `Countable J` is required — it is what makes the product sequentially compact — so this does
not extend to an uncountable family. The subsequence `φ` is common to all components; the bound `C`
is uniform in both `j` and `n` by hypothesis, and is not constructed here.

DERIVED: no numeral appears in the statement; `C` and `-C` are the bound variable and its
negation. -/
theorem tight_limit_vector {J : Type*} [Countable J] {Q : J → ℕ → ℝ} {C : ℝ}
    (hbdd : ∀ j n, |Q j n| ≤ C) :
    ∃ q : J → ℝ, (∀ j, |q j| ≤ C) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j, Filter.Tendsto (fun k => Q j (φ k)) Filter.atTop (nhds (q j)) := by
  have hmem : ∀ n, (fun j => Q j n) ∈ Set.pi Set.univ (fun _ : J => Set.Icc (-C) C) :=
    fun n j _ => abs_le.mp (hbdd j n)
  obtain ⟨q, hq, φ, hmono, htend⟩ :=
    (isCompact_univ_pi (fun _ : J => isCompact_Icc)).tendsto_subseq hmem
  exact ⟨q, fun j => abs_le.mpr (hq j (Set.mem_univ j)), φ, hmono,
    fun j => tendsto_pi_nhds.mp htend j⟩

/-- Given any `φ : ℕ → ℕ` along which each component of `Q : J → ℕ → ℝ` converges to `q j`, and
`0 ≤ Q j n` for all `j` and `n`, every limit satisfies `0 ≤ q j`. It is `rp_survives_limit` applied
componentwise to `fun k => Q j (φ k)`.

Scope: `φ` is an arbitrary function `ℕ → ℕ`; strict monotonicity is not required, because the
hypothesis is convergence of the composed sequence rather than of `Q` itself. `J` carries no
countability assumption here.

DERIVED: `0` occurs twice, as the lower bound on each `Q j n` and as the lower bound concluded on
each `q j`. -/
theorem rp_of_tight_limit_vector {J : Type*} {Q : J → ℕ → ℝ} {q : J → ℝ} {φ : ℕ → ℕ}
    (hrp : ∀ j n, 0 ≤ Q j n)
    (htend : ∀ j, Filter.Tendsto (fun k => Q j (φ k)) Filter.atTop (nhds (q j))) :
    ∀ j, 0 ≤ q j :=
  fun j => rp_survives_limit (fun k => hrp j (φ k)) (htend j)

/-!
## Reindexings that fix every term fix the limit (OS1, OS3)

Four statements, all reducible to uniqueness of limits: a map on the index type that leaves every
`Q j n` unchanged leaves `q` unchanged. The last three differ from `symmetry_survives_limit` only in
packaging the reindexing as a family parameterised by a further type.
-/

/-- Given `φ : ℕ → ℕ` along which each `fun k => Q j (φ k)` converges to `q j`, and a map
`τ : J → J` with `Q (τ j) n = Q j n` for all `j` and `n`, the limit satisfies `q (τ j) = q j`. The
sequences `fun k => Q (τ j) (φ k)` and `fun k => Q j (φ k)` are equal by `funext`, so
`tendsto_nhds_unique` identifies their limits.

Scope: `τ` is an arbitrary function on `J` — not assumed injective, surjective or involutive — and
the invariance hypothesis is an equality at every index and every `n`.

DERIVED: no numeral appears in the statement. -/
theorem symmetry_survives_limit {J : Type*} {Q : J → ℕ → ℝ} {q : J → ℝ} {φ : ℕ → ℕ}
    (htend : ∀ j, Filter.Tendsto (fun k => Q j (φ k)) Filter.atTop (nhds (q j)))
    (τ : J → J) (hinv : ∀ j n, Q (τ j) n = Q j n) :
    ∀ j, q (τ j) = q j := by
  intro j
  refine tendsto_nhds_unique (htend (τ j)) ?_
  have heq : (fun k => Q (τ j) (φ k)) = (fun k => Q j (φ k)) := funext fun k => hinv j (φ k)
  rw [heq]; exact htend j

/-- `symmetry_survives_limit` applied pointwise to a family of reindexings: given
`act : G → J → J` with `Q (act g j) n = Q j n` for all `g`, `j` and `n`, the limit satisfies
`q (act g j) = q j` for all `g` and `j`.

Scope: `G` is a bare `Type*`. It carries no `Group` instance, and `act` is not required to satisfy
any action law — no identity, no compatibility with multiplication. The statement is a family of
independent instances of `symmetry_survives_limit`, one per `g`.

DERIVED: no numeral appears in the statement. -/
theorem invariant_limit_of_action {G J : Type*} {Q : J → ℕ → ℝ} {q : J → ℝ} {φ : ℕ → ℕ}
    (htend : ∀ j, Filter.Tendsto (fun k => Q j (φ k)) Filter.atTop (nhds (q j)))
    (act : G → J → J) (hinv : ∀ g j n, Q (act g j) n = Q j n) :
    ∀ g j, q (act g j) = q j :=
  fun g => symmetry_survives_limit htend (act g) (fun j => hinv g j)

/-- `invariant_limit_of_action` under the name used for OS1: given `act : E → J → J` leaving every
`Q j n` invariant, the limit satisfies `q (act g j) = q j`.

Scope: `E` is a bare `Type*` with no group, topological or Euclidean structure, and `act` is an
arbitrary function. The statement is identical to `invariant_limit_of_action` up to the name of the
parameter type; identifying `E` with a Euclidean group and discharging `hinv` at finite spacing both
happen at the call site, not here.

DERIVED: no numeral appears in the statement. -/
theorem os1_euclidean_survives {E J : Type*} {Q : J → ℕ → ℝ} {q : J → ℝ} {φ : ℕ → ℕ}
    (htend : ∀ j, Filter.Tendsto (fun k => Q j (φ k)) Filter.atTop (nhds (q j)))
    (act : E → J → J) (hinv : ∀ g j n, Q (act g j) n = Q j n) :
    ∀ g j, q (act g j) = q j :=
  invariant_limit_of_action htend act hinv

/-- `invariant_limit_of_action` under the name used for OS3: given `act : Perm → J → J` leaving
every `Q j n` invariant, the limit satisfies `q (act σ j) = q j`.

Scope: `Perm` is a bare `Type*` — it is not `Equiv.Perm` of anything, carries no group structure,
and `act σ` is not required to be a bijection. The statement is identical to
`invariant_limit_of_action` up to the name of the parameter type.

DERIVED: no numeral appears in the statement. -/
theorem os3_symmetry_survives {Perm J : Type*} {Q : J → ℕ → ℝ} {q : J → ℝ} {φ : ℕ → ℕ}
    (htend : ∀ j, Filter.Tendsto (fun k => Q j (φ k)) Filter.atTop (nhds (q j)))
    (act : Perm → J → J) (hinv : ∀ σ j n, Q (act σ j) n = Q j n) :
    ∀ σ j, q (act σ j) = q j :=
  invariant_limit_of_action htend act hinv

end MassGap
