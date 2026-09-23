import Mathlib

/-!
# MassGap.Floor — the number `(1/4) log 3`, and a count of ternary words

Two independent groups of results, sharing only the number `3`.

**Arithmetic about `(1/4) log 3`.** `log_three_pos` and `floor_pos` give `0 < Real.log 3` and
`0 < (1/4) * Real.log 3`. `density_ratio` gives `((n : ℝ) - 1) / (4 * n + 2) → 1/4` and
`floor_density_limit` multiplies it by `Real.log 3` to give
`((n : ℝ) - 1) * log 3 / (4 * n + 2) → (1/4) * log 3`. These are facts about real sequences; the
coefficients `4` and `2` are written into the statements and nothing derives them.

**Counting maps `Fin k → Fin 3`.** `directed_paths_card` is `Fintype.card (Fin k → Fin 3) = 3 ^ k`.
`cubePos s i a` counts how many of the first `i` entries of `s` equal `a`, so each `s` gives a
sequence of points of `Fin 3 → ℕ`; `cubeConfig s` is the `Finset` of the first `k + 1` such points.
`cubeConfig_injective` shows `cubeConfig` is injective — recovered from `cubePos_sum_le`, which says
the `i`-th point has coordinate sum `i`, so the set determines the ordered sequence — and
`directed_surface_count` concludes that the image of `cubeConfig` has cardinality exactly `3 ^ k`.

Scope: no statement in this file mentions a surface, an area, a plaquette, a vortex, an entropy or a
coupling. `Fin 3 → ℕ` is an index type with three coordinates and no embedding into a lattice is
defined. The counting results are equalities, not lower bounds.
-/

open Filter Topology

namespace MassGap

/-- The type of functions `Fin k → Fin 3` has cardinality `3 ^ k`. The standard count of words of
length `k` over a three-letter alphabet, discharged by `simp`.

DERIVED: `3` is the size of the codomain `Fin 3` and, necessarily, the base of the power; the two
occurrences are the same number. `k` is the argument. -/
theorem directed_paths_card (k : ℕ) : Fintype.card (Fin k → Fin 3) = 3 ^ k := by
  simp

/-- `0 < Real.log 3`, from `Real.log_pos` and `1 < 3`.

DERIVED: `3` is the argument of the logarithm, the alphabet size the rest of the file counts over;
`0` is the sign asserted. -/
theorem log_three_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)

/-- `0 < (1 / 4 : ℝ) * Real.log 3`: a positive rational times `log_three_pos`.

The statement is the positivity of one real number. It carries no parameter, so nothing in it is
independent of, or dependent on, a coupling.

DERIVED: `1` and `4` are the numerator and denominator of the coefficient, written into the
statement; `3` is the argument of the logarithm; `0` is the sign asserted. -/
theorem floor_pos : 0 < (1 / 4 : ℝ) * Real.log 3 :=
  mul_pos (by norm_num) log_three_pos

/-- The real sequence `n ↦ ((n : ℝ) - 1) / (4 * n + 2)` converges to `1/4` along `atTop`. Proved by
rewriting it, eventually in `n`, as `1/4 - 3 / (8 * n + 4)` and sending the second term to `0`.

A statement about a sequence of rationals cast to `ℝ`; the coefficients are literals of the statement
and are not derived from any geometry.

DERIVED: `1` is subtracted in the numerator, `4` and `2` are the coefficient and offset of the
denominator, and `1 / 4` is the limit — the ratio of the leading coefficients `1` and `4` of
numerator and denominator, so the limit's two numerals are forced by the other three. -/
theorem density_ratio :
    Tendsto (fun n : ℕ => ((n : ℝ) - 1) / (4 * (n : ℝ) + 2)) atTop (𝓝 (1 / 4)) := by
  have hden : Tendsto (fun n : ℕ => 8 * (n : ℝ) + 4) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 4
      (Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop)
  have hz : Tendsto (fun n : ℕ => 3 / (8 * (n : ℝ) + 4)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hden
  have hcongr : (fun n : ℕ => ((n : ℝ) - 1) / (4 * (n : ℝ) + 2))
      =ᶠ[atTop] (fun n : ℕ => 1 / 4 - 3 / (8 * (n : ℝ) + 4)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h4 : (4 * (n : ℝ) + 2) ≠ 0 := by positivity
    have h8 : (8 * (n : ℝ) + 4) ≠ 0 := by positivity
    field_simp
    ring
  rw [Filter.tendsto_congr' hcongr]
  simpa using tendsto_const_nhds.sub hz

/-- The real sequence `n ↦ ((n : ℝ) - 1) * Real.log 3 / (4 * n + 2)` converges to
`(1 / 4) * Real.log 3` along `atTop`. It is `density_ratio` multiplied by the constant `Real.log 3`.

DERIVED: `1`, `4` and `2` are `density_ratio`'s, carried across the multiplication — the subtracted
unit, the denominator's coefficient and its offset, and the `1 / 4` of the limit. `3` is the argument
of the logarithm, the constant factor, appearing once in the sequence and once in the limit. -/
theorem floor_density_limit :
    Tendsto (fun n : ℕ => ((n : ℝ) - 1) * Real.log 3 / (4 * (n : ℝ) + 2))
      atTop (𝓝 ((1 / 4 : ℝ) * Real.log 3)) := by
  have h := density_ratio.mul_const (Real.log 3)
  simpa [div_mul_eq_mul_div] using h

/-! ### The injection from words to position sets

`directed_paths_card` counts the `3 ^ k` functions `Fin k → Fin 3`. This section shows that the map
`cubeConfig`, sending such a function to the *set* of its `k + 1` partial-count vectors, is injective,
so the image also has `3 ^ k` elements.

The recovery argument: `cubePos s i` records how many of the first `i` entries of `s` take each of
the three values, so its coordinate sum is `i` whenever `i ≤ k` (`cubePos_sum_le`). The sum therefore
labels each element of the set with its index, which recovers the ordered sequence from the
unordered set; `cubePos_succ` then reads off each entry of `s` as the coordinate that increments.

Everything here is about `Fin k → Fin 3` and `Finset (Fin 3 → ℕ)`. No surface, area or lattice
embedding is defined in this file, and the conclusion reached is an equality of cardinalities. -/

open Finset

/-- The partial-count vector of `s : Fin k → Fin 3` at `i : ℕ`: the `a`-th coordinate is the number
of indices `j < i` with `s j = a`, as a `Finset.card`.

`i` ranges over all of `ℕ`, not over `Fin k`; for `i ≥ k` the filter saturates and the vector is
constant in `i`.

DERIVED: `3` is the alphabet size, appearing as the codomain of `s` and as the index type of the
result; both occurrences are the same number. -/
def cubePos {k : ℕ} (s : Fin k → Fin 3) (i : ℕ) : Fin 3 → ℕ :=
  fun a => (univ.filter (fun j : Fin k => (j : ℕ) < i ∧ s j = a)).card

/-- The coordinates of `cubePos s i` sum to the number of indices of `Fin k` below `i`. The fibres of
`s` partition that filtered set, so this is `Finset.card_eq_sum_card_fiberwise`.

Stated for every `i : ℕ`, with no relation between `i` and `k` assumed.

DERIVED: `3` is the alphabet size, in the codomain of `s`; it is the only numeral, and the summation
index `a` ranges over `Fin 3`. -/
theorem cubePos_sum {k : ℕ} (s : Fin k → Fin 3) (i : ℕ) :
    ∑ a, cubePos s i a = (univ.filter (fun j : Fin k => (j : ℕ) < i)).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (fun (x : Fin k) _ => mem_univ (s x))]
  exact Finset.sum_congr rfl fun a _ => by rw [cubePos, Finset.filter_filter]

/-- For `i ≤ k`, the set of `j : Fin k` with `(j : ℕ) < i` has cardinality `i`. Induction on `i`; the
successor step inserts the element `⟨n, hi⟩`, which is where the hypothesis `i ≤ k` is spent.

The bound `i ≤ k` is required: above `k` the cardinality stalls at `k`.

DERIVED: no numeral. `i` and `k` are the arguments. -/
theorem card_filter_val_lt {k i : ℕ} (hi : i ≤ k) :
    (univ.filter (fun j : Fin k => (j : ℕ) < i)).card = i := by
  classical
  induction i with
  | zero => simp
  | succ n ih =>
    have hsplit : (univ.filter (fun j : Fin k => (j : ℕ) < n + 1))
        = insert (⟨n, hi⟩ : Fin k) (univ.filter (fun j : Fin k => (j : ℕ) < n)) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · intro hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · exact Or.inr h
        · exact Or.inl (Fin.ext h)
      · rintro (rfl | hj)
        · exact Nat.lt_succ_self n
        · exact Nat.lt_succ_of_lt hj
    rw [hsplit, Finset.card_insert_of_notMem (by simp), ih (Nat.le_of_succ_le hi)]

/-- For `i ≤ k`, the coordinates of `cubePos s i` sum to `i`. `cubePos_sum` followed by
`card_filter_val_lt`.

This is what makes `cubeConfig` invertible: the coordinate sum is the index, so an element of the
unordered set announces its own position in the sequence. Holds only for `i ≤ k`.

DERIVED: `3` is the alphabet size, in the codomain of `s`; no other numeral. -/
theorem cubePos_sum_le {k : ℕ} (s : Fin k → Fin 3) {i : ℕ} (hi : i ≤ k) :
    ∑ a, cubePos s i a = i := by
  rw [cubePos_sum, card_filter_val_lt hi]

/-- Advancing the index by one increments exactly the coordinate named by `s j`:
`cubePos s (j + 1) a = cubePos s j a + (if s j = a then 1 else 0)`, for `j : Fin k` and `a : Fin 3`.
The filtered set splits as a disjoint union of the strictly-smaller indices and the singleton `{j}`.

DERIVED: `3` is the alphabet size, the type of `a` and the codomain of `s`. `1` is the index
increment and the value of the indicator when `s j = a`; `0` is its value otherwise. -/
theorem cubePos_succ {k : ℕ} (s : Fin k → Fin 3) (j : Fin k) (a : Fin 3) :
    cubePos s ((j : ℕ) + 1) a = cubePos s (j : ℕ) a + (if s j = a then 1 else 0) := by
  classical
  simp only [cubePos]
  have hsplit : (univ.filter (fun i : Fin k => (i : ℕ) < (j : ℕ) + 1 ∧ s i = a))
      = (univ.filter (fun i : Fin k => (i : ℕ) < (j : ℕ) ∧ s i = a))
        ∪ (univ.filter (fun i : Fin k => i = j ∧ s i = a)) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · rintro ⟨hlt, hsa⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
      · exact Or.inl ⟨h, hsa⟩
      · exact Or.inr ⟨Fin.ext h, hsa⟩
    · rintro (⟨h, hsa⟩ | ⟨rfl, hsa⟩)
      · exact ⟨Nat.lt_succ_of_lt h, hsa⟩
      · exact ⟨Nat.lt_succ_self _, hsa⟩
  rw [hsplit, Finset.card_union_of_disjoint]
  · congr 1
    by_cases hja : s j = a
    · rw [if_pos hja]
      rw [Finset.card_eq_one]
      refine ⟨j, ?_⟩
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨rfl, _⟩; rfl
      · rintro rfl; exact ⟨rfl, hja⟩
    · rw [if_neg hja, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro i _ ⟨rfl, hsa⟩
      exact hja hsa
  · rw [Finset.disjoint_left]
    rintro i h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    obtain ⟨rfl, _⟩ := h2
    exact Nat.lt_irrefl _ h1.1

/-- The image `Finset` of `cubePos s` over `Finset.range (k + 1)`: the set of partial-count vectors
of `s` at the indices `0, …, k`. A `Finset (Fin 3 → ℕ)`, so the order of the sequence is discarded —
`cubeConfig_injective` is the statement that nothing is lost by discarding it.

DERIVED: `1` makes `range (k + 1)` run through `k` inclusive, so the set carries the initial vector
at `0` as well as one vector per entry of `s`. `3` is the alphabet size, in the codomain of `s` and
in the index type of the elements. -/
noncomputable def cubeConfig {k : ℕ} (s : Fin k → Fin 3) : Finset (Fin 3 → ℕ) :=
  (range (k + 1)).image (cubePos s)

/-- `cubeConfig` is injective on `Fin k → Fin 3`. Two steps: equal images force `cubePos s i` and
`cubePos t i` to agree for every `i ≤ k`, matched by coordinate sum via `cubePos_sum_le`; then
`cubePos_succ` at each `j : Fin k` forces `s j = t j`.

DERIVED: no numeral of this declaration's. `3` and the `k + 1` of the index range are `cubeConfig`'s,
carried through its type. -/
theorem cubeConfig_injective {k : ℕ} : Function.Injective (@cubeConfig k) := by
  classical
  intro s t hst
  -- Step A: the position sequences agree on `[0, k]`.
  have hA : ∀ i, i ≤ k → cubePos s i = cubePos t i := by
    intro i hi
    have hmem : cubePos s i ∈ cubeConfig t := by
      rw [← hst, cubeConfig]
      exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hi))
    rw [cubeConfig, Finset.mem_image] at hmem
    obtain ⟨i', hi', heq⟩ := hmem
    have hi'k : i' ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')
    have hsum : (i : ℕ) = i' := by
      have := cubePos_sum_le s hi
      have := cubePos_sum_le t hi'k
      rw [heq] at *
      omega
    subst hsum
    exact heq.symm
  -- Step B: recover the path from the position sequence.
  funext j
  have hj1 : (j : ℕ) + 1 ≤ k := j.2
  have hsucc_s := cubePos_succ s j (s j)
  have hsucc_t := cubePos_succ t j (s j)
  rw [if_pos rfl] at hsucc_s
  have e1 : cubePos s ((j : ℕ) + 1) (s j) = cubePos t ((j : ℕ) + 1) (s j) := by rw [hA _ hj1]
  have e2 : cubePos s (j : ℕ) (s j) = cubePos t (j : ℕ) (s j) := by
    rw [hA _ (Nat.le_of_succ_le hj1)]
  have key : cubePos t (j : ℕ) (s j) + (if t j = s j then 1 else 0)
      = cubePos t (j : ℕ) (s j) + 1 := by
    rw [← hsucc_t, ← e1, hsucc_s, e2]
  have : (if t j = s j then 1 else 0) = 1 := by omega
  by_cases h : t j = s j
  · exact h.symm
  · rw [if_neg h] at this; exact absurd this (by norm_num)

/-- The image of `cubeConfig` over all of `Fin k → Fin 3` has exactly `3 ^ k` elements:
`Finset.card_image_of_injective` at `cubeConfig_injective`, then `directed_paths_card`.

An equality of cardinalities of `Finset`s. The counted objects are position sets in `Fin 3 → ℕ`;
nothing in the statement associates them with a surface, an area or a lattice.

DERIVED: `3` is the alphabet size and the base of the power, carried from `directed_paths_card`,
where the two occurrences are already the same number. -/
theorem directed_surface_count {k : ℕ} :
    (Finset.univ.image (@cubeConfig k)).card = 3 ^ k := by
  rw [Finset.card_image_of_injective _ cubeConfig_injective, Finset.card_univ, directed_paths_card]

#print axioms cubeConfig_injective
#print axioms directed_surface_count

end MassGap
