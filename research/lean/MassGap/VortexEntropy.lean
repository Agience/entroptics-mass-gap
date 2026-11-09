import Mathlib
import MassGap.WilsonHypercubic

/-!
# MassGap.VortexEntropy — cube-boundary surfaces through a plaquette: `3^k` of area `4k + 6`, entropy `¼ ln 3` per unit area

A directed cube path `s : Fin k → Fin 3` visits `k + 1` unit cubes of a three-dimensional sublattice.
The union of those cubes has a boundary: the faces with exactly one owner. This module counts those surfaces, measures
their area, places them as plaquette sets of the four-dimensional periodic lattice through one fixed
plaquette, and reads the entropy density of the family.

## The count (namespace `MassGap.VortexEntropy`)

* `directed_paths_card`: `3 ^ k` paths.
* `cubeConfig s`: the set of the `k + 1` cubes visited; `cubeConfig_injective`, from the coordinate
  sum labelling each cube with its index (`cubePos_sum_le`); `directed_surface_count`.

## The area (`MassGap.VortexEntropy.CubeArea`)

* `boundaryFaces C`: the faces with exactly one owner in `C`, the mod-2 boundary of the union (closed by construction; closedness is not proved here).
* `boundary_card_eq`: `|∂(cubeConfig s)| = 6(k + 1) − 2k = 4k + 6`.
* `boundaryFaces_cubeConfig_injective`: distinct paths bound distinct surfaces.

## The lattice (`MassGap.VortexEntropy.SurfaceEmbed`)

* `plaqSurface n s : Finset (Plaq 4 n)`, the surface in one time slice of `Site 4 n`;
  `card_plaqSurface`, `plaqSurface_injective` while `k + 1 < n`.
* `origin_face_mem_boundary`, `basePlaq_mem_plaqSurface`: every one of these surfaces contains the
  plaquette `basePlaq n`, the low face of the cube at the origin.
* **`closed_surfaces_through_plaquette`** (the name says closed; what is proved is cube boundaries): for `k + 1 < n`, a family of `3 ^ k` distinct plaquette
  sets of `Site 4 n`, each of `4k + 6` plaquettes, each containing `basePlaq n`.

## The density and the threshold

* `floorTerm μ k = 3^k e^{−μ(4k+6)}`; `kappa0_is_the_surface_entropy_density`:
  `log(3^k)/|∂| → ¼ ln 3`.
* **`floorTerm_summable_iff`**: `Σ_k 3^k e^{−μ(4k+6)}` converges iff `¼ ln 3 < μ`. At a cost `μ` per
  unit area at or below the entropy density the sum over these surfaces through one plaquette
  diverges; above it, it converges.
* `junction_of_floor_count`: a weight `Z k ≥ floorTerm μ k` with `log Z k/(4k+6) ≤ c` forces
  `¼ ln 3 − μ ≤ c`.

DERIVED (module-wide): `3` the directions of a step of a cube path in a three-dimensional
sublattice, the cardinality of `Fin 3`; `4k + 6 = 6(k + 1) − 2k`, six faces per cube less two per
shared face; `¼ = lim k/(4k + 6)`; `4` the dimension of the lattice `Site 4 n`; `1` the unit step and
the owner count of a boundary face; `2` the owner count of a shared face; `0` the origin and the time
slice of the embedding.

## What does not follow

* No surface here is weighted by a gauge field. `μ` is a number supplied by the caller; nothing in
  this module relates it to the Wilson action, the twisted partition functions or a coupling.
* Divergence of the surface sum at `μ ≤ ¼ ln 3` is the breakdown of the dilute-surface (Peierls)
  expansion at that cost. It is not condensation of vortices, and it bounds no twisted ratio.
* The surfaces are boundaries of unions of unit cubes (faces with exactly one owner); closedness is by construction and not proved (no even-degree or cycle lemma here).
* The family is the directed one, a lower bound on all cube-boundary surfaces through the plaquette; every
  surface lies in one time slice of a three-dimensional sublattice.

`#print axioms` for the declarations are inline and at the end.
-/


open Filter Topology

namespace MassGap.VortexEntropy

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

end MassGap.VortexEntropy



namespace MassGap.VortexEntropy.CubeArea

open Finset

/-- A unit cube, named by its low corner.

DERIVED: `3` is the dimension the directed cube-path of `lean` lives in — `Fin 3` is the
step alphabet `directed_paths_card` counts over, so the ambient dimension is that alphabet's
arity and not a separate choice. -/
abbrev Cube : Type := Fin 3 → ℕ

/-- A face, named by the axis it is perpendicular to and its low corner. This is the same
`(normal, site)` naming `WilsonBridge.Plaq3` uses for a plaquette.

DERIVED: both `3`s are `Cube`'s dimension — the axis ranges over it and the corner is a point of
it. Nothing new is introduced here. -/
abbrev Face : Type := Fin 3 × (Fin 3 → ℕ)

/-- One unit step along axis `a`.

DERIVED: `1` is the unit of the lattice — a cube-path advances one cube per step, which is what
`cubePos_succ` already states coordinatewise; `3` is `Cube`'s dimension. -/
def step (a : Fin 3) (x : Cube) : Cube := Function.update x a (x a + 1)

theorem step_self (a : Fin 3) (x : Cube) : step a x a = x a + 1 := by
  simp [step]

theorem step_other {a b : Fin 3} (h : b ≠ a) (x : Cube) : step a x b = x b := by
  simp [step, h]

/-- `∑ b, step a x b = (∑ b, x b) + 1`: one step raises the coordinate sum by exactly one. The
summand at `a` rises by one and every other is unchanged, so `Finset.add_sum_erase` splits it off.

This is what makes the adjacency argument work: the coordinate sum measures position along a path.

DERIVED: `1` is the unit lattice step, `step`'s own increment; `3` is the dimension. -/
theorem sum_step (a : Fin 3) (x : Cube) : ∑ b, step a x b = (∑ b, x b) + 1 := by
  classical
  rw [← Finset.add_sum_erase _ _ (mem_univ a), ← Finset.add_sum_erase _ x (mem_univ a)]
  rw [step_self]
  have : ∑ b ∈ univ.erase a, step a x b = ∑ b ∈ univ.erase a, x b := by
    refine Finset.sum_congr rfl (fun b hb => ?_)
    exact step_other (Finset.ne_of_mem_erase hb) x
  rw [this]
  ring

/-- The faces of the unit cube at `x`: on each axis `a`, the low face `(a, x)` and the high face
`(a, step a x)`, collected by `Finset.biUnion` over the axes.

DERIVED: `3` is `Cube`'s dimension, the number of axes the union runs over. The pair on each axis is
the two sides of a cube along it; the resulting total of six is `card_faces`, not part of this
definition. -/
def faces (x : Cube) : Finset Face :=
  (univ : Finset (Fin 3)).biUnion (fun a => {(a, x), (a, step a x)})

theorem mem_faces {f : Face} {x : Cube} :
    f ∈ faces x ↔ ∃ a : Fin 3, f = (a, x) ∨ f = (a, step a x) := by
  classical
  simp [faces, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]

/-- `(faces x).card = 6`. `Finset.card_biUnion` needs the axis families disjoint, which holds on the
first component alone; each family has two elements because a step changes that axis's coordinate, so
the low and high faces differ.

DERIVED: `6` is `2` per axis times `3` axes — the two sides of a cube along one axis, and the
dimension. Neither factor is a magnitude. -/
theorem card_faces (x : Cube) : (faces x).card = 6 := by
  classical
  rw [faces, Finset.card_biUnion]
  · have h : ∀ a : Fin 3, ({(a, x), (a, step a x)} : Finset Face).card = 2 := by
      intro a
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]
      simp only [Finset.mem_singleton, Prod.mk.injEq, true_and]
      intro hx
      have := congrArg (fun y : Cube => y a) hx
      simp [step_self] at this
    simp [h]
  · -- Faces on different axes are distinct in their first component alone, so the two-element
    -- families are disjoint without looking at the corners at all.
    intro a _ b _ hab
    refine Finset.disjoint_left.mpr ?_
    intro f hf hf'
    have ha : f.1 = a := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with h | h <;> rw [h]
    have hb : f.1 = b := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hf'
      rcases hf' with h | h <;> rw [h]
    exact hab (by rw [← ha, hb])

theorem step_injective (a : Fin 3) : Function.Injective (step a) := by
  intro x y h
  funext b
  by_cases hb : b = a
  · subst hb
    have := congrArg (fun z : Cube => z b) h
    simp only [step_self] at this
    omega
  · have := congrArg (fun z : Cube => z b) h
    simpa [step_other hb] using this

/-- Two cubes carrying a common face are equal, or one is a single step from the other along one
axis. The axis is read off the face's first component, so both descriptions use the same axis, and
the four cases on the corner close by `step_injective` or by equality of corners.

DERIVED: `3` is the dimension, the range of the axis; the unit step is inside `step` and the
statement carries no literal. -/
theorem step_rel_of_shares {x y : Cube} {f : Face} (hx : f ∈ faces x) (hy : f ∈ faces y) :
    x = y ∨ (∃ a, y = step a x) ∨ (∃ a, x = step a y) := by
  obtain ⟨a, ha⟩ := mem_faces.mp hx
  obtain ⟨b, hb⟩ := mem_faces.mp hy
  -- the axis is read off the face's first component, so the two descriptions use the same axis
  have hab : a = b := by
    rcases ha with h | h <;> rcases hb with h' | h' <;>
      · have := congrArg Prod.fst (h.symm.trans h'); simpa using this
  subst hab
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact Or.inl (by
      have := congrArg Prod.snd (ha.symm.trans hb); simpa using this)
  · exact Or.inr (Or.inr (by
      have := congrArg Prod.snd (ha.symm.trans hb)
      exact ⟨a, by simpa using this⟩))
  · exact Or.inr (Or.inl (by
      have := congrArg Prod.snd (ha.symm.trans hb)
      exact ⟨a, by simpa using this.symm⟩))
  · exact Or.inl (by
      have := congrArg Prod.snd (ha.symm.trans hb)
      exact step_injective a (by simpa using this))

/-- Two distinct cubes carrying a common face have coordinate sums differing by exactly one:
`step_rel_of_shares` puts one a step from the other, and `sum_step` moves the sum by one.

Along a directed path `cubePos_sum_le` makes the coordinate sum the index, so only consecutive
cubes can share a face. That is what `sharedFaces_eq_crossFaces` consumes.

DERIVED: `1` is the unit lattice step, carried from `sum_step`; `3` is the dimension. -/
theorem sum_dist_one_of_shares {x y : Cube} {f : Face}
    (hx : f ∈ faces x) (hy : f ∈ faces y) (hne : x ≠ y) :
    (∑ b, x b) + 1 = (∑ b, y b) ∨ (∑ b, y b) + 1 = (∑ b, x b) := by
  rcases step_rel_of_shares hx hy with h | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact absurd h hne
  · exact Or.inl (sum_step a x).symm
  · exact Or.inr (sum_step a y).symm

/-- `cubePos s (j + 1) = step (s j) (cubePos s j)`: `cubePos_succ` as an equation between cubes
rather than coordinate by coordinate. By `funext` and a case split on whether the coordinate is
`s j`.

DERIVED: `1` is the index increment, one step of the path; `3` is the dimension, the range of the
step alphabet. -/
theorem cubePos_succ_eq_step {k : ℕ} (s : Fin k → Fin 3) (j : Fin k) :
    MassGap.VortexEntropy.cubePos s ((j : ℕ) + 1) = step (s j) (MassGap.VortexEntropy.cubePos s (j : ℕ)) := by
  funext a
  rw [MassGap.VortexEntropy.cubePos_succ s j a]
  by_cases h : s j = a
  · subst h
    simp [step_self]
  · have h' : a ≠ s j := fun hh => h hh.symm
    simp [step_other h', h]

/-- The face `(s j, cubePos s (j+1))` lies in `faces (cubePos s j) ∩ faces (cubePos s (j+1))`: it is
the high face of the `j`-th cube along the step's axis and the low face of the `(j+1)`-th.

With `sum_dist_one_of_shares` ruling out non-consecutive pairs, this pins the shared faces to the `k`
consecutive pairs.

DERIVED: `1` is the index increment, one step; `3` is the dimension. -/
theorem shares_succ {k : ℕ} (s : Fin k → Fin 3) (j : Fin k) :
    ((s j : Fin 3), MassGap.VortexEntropy.cubePos s ((j : ℕ) + 1))
      ∈ faces (MassGap.VortexEntropy.cubePos s (j : ℕ)) ∩ faces (MassGap.VortexEntropy.cubePos s ((j : ℕ) + 1)) := by
  classical
  refine Finset.mem_inter.mpr ⟨?_, ?_⟩
  · exact mem_faces.mpr ⟨s j, Or.inr (by rw [cubePos_succ_eq_step])⟩
  · exact mem_faces.mpr ⟨s j, Or.inl rfl⟩

/-- `step a x = step b x → a = b`: the axis is recoverable from the result, since only the stepped
coordinate changes.

DERIVED: `3` is the dimension, the range of the two axes; no other numeral. -/
theorem step_axis_inj {a b : Fin 3} {x : Cube} (h : step a x = step b x) : a = b := by
  by_contra hne
  have h1 : step a x a = step b x a := congrArg (fun z : Cube => z a) h
  rw [step_self, step_other hne] at h1
  omega

/-- A cube carrying the face `f` is either `f.2` itself or the cube one step back along `f.1`:
`x = f.2 ∨ step f.1 x = f.2`. Directly from `mem_faces`.

DERIVED: `3` is the dimension. The `1` and `2` in `f.1`, `f.2` are the projections of `Face` onto its
axis and its corner, not numbers. -/
theorem cube_of_face {f : Face} {x : Cube} (h : f ∈ faces x) :
    x = f.2 ∨ step f.1 x = f.2 := by
  obtain ⟨a, ha⟩ := mem_faces.mp h
  rcases ha with ha | ha
  · left; rw [ha]
  · right; rw [ha]

/-- For any `Finset Cube` and any face, the owners number at most two:
`(C.filter (fun x => f ∈ faces x)).card ≤ 2`. By `cube_of_face` an owner is the corner itself or a
step back along the axis, and `step_injective` makes the second unique, so the owners sit inside a
two-element insert.

DERIVED: `2` is the number of cubes a face can lie between — one at its corner, one a step back — and
is derived here rather than assumed. `3` is the dimension. -/
theorem card_cubes_with_face_le_two (C : Finset Cube) (f : Face) :
    (C.filter (fun x => f ∈ faces x)).card ≤ 2 := by
  classical
  have hsub : C.filter (fun x => f ∈ faces x)
      ⊆ insert f.2 (C.filter (fun x => step f.1 x = f.2)) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rcases cube_of_face hx.2 with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hx.1, h⟩)
  have h1 : (C.filter (fun x => step f.1 x = f.2)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    exact step_injective f.1 (ha.2.trans hb.2.symm)
  calc (C.filter (fun x => f ∈ faces x)).card
      ≤ (insert f.2 (C.filter (fun x => step f.1 x = f.2))).card := Finset.card_le_card hsub
    _ ≤ (C.filter (fun x => step f.1 x = f.2)).card + 1 := Finset.card_insert_le _ _
    _ ≤ 2 := by omega

#print axioms cube_of_face
#print axioms card_cubes_with_face_le_two

/-- `cubePos s` is injective on `Finset.range (k + 1)`: equal positions have equal coordinate sums,
and `cubePos_sum_le` makes that sum the index.

So the path never revisits a cube, which is what makes `6(k+1)` a count rather than an over-count.

DERIVED: `1` in `range (k + 1)` makes the range run through `k` inclusive, the `k + 1` positions of a
`k`-step path. `3` is the dimension. -/
theorem cubePos_injOn {k : ℕ} (s : Fin k → Fin 3) :
    Set.InjOn (MassGap.VortexEntropy.cubePos s) (Finset.range (k + 1)) := by
  intro i hi j hj hij
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hi' := MassGap.VortexEntropy.cubePos_sum_le s hik
  have hj' := MassGap.VortexEntropy.cubePos_sum_le s hjk
  rw [hij] at hi'
  omega

/-- `(cubeConfig s).card = k + 1`: the image of a map injective on `range (k + 1)`, by
`Finset.card_image_of_injOn` at `cubePos_injOn`.

DERIVED: `1` is the `+1` of `range (k + 1)`, so the count is the number of cubes of a `k`-step path;
`3` is the dimension. -/
theorem card_cubeConfig {k : ℕ} (s : Fin k → Fin 3) :
    (MassGap.VortexEntropy.cubeConfig s).card = k + 1 := by
  classical
  rw [MassGap.VortexEntropy.cubeConfig, Finset.card_image_of_injOn (cubePos_injOn s), Finset.card_range]

#print axioms cubePos_injOn
#print axioms card_cubeConfig

/-- The face the `j`-th step crosses: `(s j, cubePos s (j + 1))`, the one shared by cube `j` and cube
`j + 1`. `crossFace_shared` proves it is shared and `crossFace_injective` that these `k` faces are
distinct.

DERIVED: `1` is the index increment — `cubePos_succ` advances the index by one per step, so
`j + 1` names the cube the `j`-th step lands on and nothing is chosen. `3` is `Cube`'s dimension, the
arity of the step alphabet `Fin 3`. -/
def crossFace {k : ℕ} (s : Fin k → Fin 3) (j : Fin k) : Face :=
  ((s j : Fin 3), MassGap.VortexEntropy.cubePos s ((j : ℕ) + 1))

/-- `crossFace s` is injective on `Fin k`. Distinctness comes from the second component alone: the
crossed face is named by the cube the step lands on, and `cubePos_injOn` says the path never lands on
the same cube twice. The axis is never compared.

DERIVED: `3` is the dimension; the index increment inside `crossFace` is that definition's. -/
theorem crossFace_injective {k : ℕ} (s : Fin k → Fin 3) : Function.Injective (crossFace s) := by
  intro i j hij
  have h2 : MassGap.VortexEntropy.cubePos s ((i : ℕ) + 1) = MassGap.VortexEntropy.cubePos s ((j : ℕ) + 1) :=
    congrArg Prod.snd hij
  have hi : (i : ℕ) + 1 ∈ Finset.range (k + 1) := by
    have := i.isLt; simp only [Finset.mem_range]; omega
  have hj : (j : ℕ) + 1 ∈ Finset.range (k + 1) := by
    have := j.isLt; simp only [Finset.mem_range]; omega
  have := cubePos_injOn s hi hj h2
  exact Fin.ext (by omega)

/-- `crossFace s j ∈ faces (cubePos s j) ∩ faces (cubePos s (j+1))`: `shares_succ` restated on
`crossFace`, so the two halves of the count speak about the same object. The body is that theorem.

DERIVED: `1` is the index increment, one step; `3` is the dimension. -/
theorem crossFace_shared {k : ℕ} (s : Fin k → Fin 3) (j : Fin k) :
    crossFace s j ∈ faces (MassGap.VortexEntropy.cubePos s (j : ℕ))
      ∩ faces (MassGap.VortexEntropy.cubePos s ((j : ℕ) + 1)) :=
  shares_succ s j

/-- `(Finset.univ.image (crossFace s)).card = k`: the image of an injective map on `Fin k`, by
`crossFace_injective` and `Fintype.card_fin`.

DERIVED: `3` is the dimension. The cardinality `k` is the number of steps, not a literal. -/
theorem card_crossFaces {k : ℕ} (s : Fin k → Fin 3) :
    (Finset.univ.image (crossFace s)).card = k := by
  classical
  rw [Finset.card_image_of_injective _ (crossFace_injective s), Finset.card_univ,
    Fintype.card_fin]

/-- A face carried by both `x` and `step a x` is `(a, step a x)`. Four cases from `cube_of_face` on
each side; two are impossible because they would equate cubes whose coordinate sums differ by one,
and of the remaining two `step_axis_inj` fixes the axis and `step_injective` the corner.

So adjacent cubes share exactly one face, and it is the one the step crosses — the half of
`|shared| = k` saying no consecutive pair contributes two.

DERIVED: `3` is the dimension; the unit step is inside `step` and the statement carries no
literal. -/
theorem shared_face_eq {a : Fin 3} {x : Cube} {f : Face}
    (hx : f ∈ faces x) (hy : f ∈ faces (step a x)) : f = (a, step a x) := by
  have hsx : (∑ b, step a x b) = (∑ b, x b) + 1 := sum_step a x
  rcases cube_of_face hx with h1 | h1 <;> rcases cube_of_face hy with h2 | h2
  · -- x = f.2 and step a x = f.2 : the two cubes coincide, impossible by the sum
    exfalso; rw [← h1] at h2; rw [h2] at hsx; omega
  · -- x = f.2 and step f.1 (step a x) = f.2 : sums move up twice and land back, impossible
    exfalso
    have := sum_step f.1 (step a x)
    rw [h2, ← h1] at this; omega
  · -- step f.1 x = f.2 and step a x = f.2 : The case. The axis and the corner both follow.
    have haxis : f.1 = a := step_axis_inj (h1.trans h2.symm)
    have : f = (f.1, f.2) := rfl
    rw [this, haxis, ← h2]
  · -- step f.1 x = f.2 and step f.1 (step a x) = f.2 : the two cubes coincide, impossible
    exfalso
    have hxy : x = step a x := step_injective f.1 (h1.trans h2.symm)
    rw [← hxy] at hsx; omega

#print axioms shared_face_eq

/-- Counting incident (cube, face) pairs two ways:
`∑_{x ∈ C} (faces x).card = ∑_{f ∈ C.biUnion faces} (C.filter (fun x => f ∈ faces x)).card`. Each
side is the same indicator summed over the product, exchanged by `Finset.sum_comm`.

Pure `Finset` bookkeeping for an arbitrary `C`; no geometry enters until the two sides are evaluated.

DERIVED: no numeral. `3` is the dimension, carried by the types `Cube` and `Face`. -/
theorem incidence_double_count (C : Finset Cube) :
    ∑ x ∈ C, (faces x).card
      = ∑ f ∈ C.biUnion faces, (C.filter (fun x => f ∈ faces x)).card := by
  classical
  have hL : ∀ x ∈ C, (faces x).card
      = ∑ f ∈ C.biUnion faces, (if f ∈ faces x then 1 else 0) := by
    intro x hx
    rw [← Finset.card_filter]
    congr 1
    rw [Finset.filter_mem_eq_inter]
    exact (Finset.inter_eq_right.mpr
      (fun f hf => Finset.mem_biUnion.mpr ⟨x, hx, hf⟩)).symm
  rw [Finset.sum_congr rfl hL, Finset.sum_comm]
  exact Finset.sum_congr rfl (fun f _ => (Finset.card_filter _ _).symm)

/-- `∑_{x ∈ cubeConfig s} (faces x).card = 6 * (k + 1)`: `card_faces` makes every summand `6` and
`card_cubeConfig` counts the summands.

DERIVED: `6` is the number of faces of a cube, `card_faces`'s; `1` is the `+1` of `k + 1`, the number
of cubes, `card_cubeConfig`'s; `3` is the dimension. -/
theorem incidence_left {k : ℕ} (s : Fin k → Fin 3) :
    ∑ x ∈ MassGap.VortexEntropy.cubeConfig s, (faces x).card = 6 * (k + 1) := by
  classical
  rw [Finset.sum_congr rfl (fun x _ => card_faces x), Finset.sum_const, card_cubeConfig,
    smul_eq_mul]
  ring

/-- A face of `C.biUnion faces` has at least one and at most two owners. The lower bound is that such
a face belongs to some cube of `C`; the upper is `card_cubes_with_face_le_two`.

This is what makes the right-hand side of the double count split as `|B| + |shared|`.

DERIVED: `1` is the least number of owners a face of the union has, since it lies in some cube's face
set; `2` is `card_cubes_with_face_le_two`'s bound; `3` is the dimension. -/
theorem owners_one_or_two (C : Finset Cube) {f : Face} (hf : f ∈ C.biUnion faces) :
    1 ≤ (C.filter (fun x => f ∈ faces x)).card
      ∧ (C.filter (fun x => f ∈ faces x)).card ≤ 2 := by
  classical
  refine ⟨?_, card_cubes_with_face_le_two C f⟩
  obtain ⟨x, hxC, hxf⟩ := Finset.mem_biUnion.mp hf
  exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hxC, hxf⟩⟩

/-- Given that every face of `C.biUnion faces` has one or two owners, and that exactly `sharedCount`
of them have two, the double count reads
`∑_{x ∈ C} (faces x).card = (C.biUnion faces).card + sharedCount`.

The owner count of each face splits as `1 + (1 if shared)`; summing the constant gives `|B|` and
summing the indicator gives the shared count.

`sharedCount` is a parameter, so the arithmetic is separated from the geometry; `card_sharedFaces`
supplies it as `k` at the cube-path configuration.

DERIVED: `1` is the owner every face of the union has, and the extra owner a shared face has; `2` is
the owner count that marks a face as shared; `3` is the dimension. -/
theorem boundary_card_of_shared (C : Finset Cube) (sharedCount : ℕ)
    (hall : ∀ f ∈ C.biUnion faces, (C.filter (fun x => f ∈ faces x)).card = 1
      ∨ (C.filter (fun x => f ∈ faces x)).card = 2)
    (hshared : ((C.biUnion faces).filter
      (fun f => (C.filter (fun x => f ∈ faces x)).card = 2)).card = sharedCount) :
    ∑ x ∈ C, (faces x).card = (C.biUnion faces).card + sharedCount := by
  rw [incidence_double_count C, ← hshared]
  -- Every face carries one owner plus, when it is shared, one more.  Summing that split over the
  -- touched faces gives `|B|` from the ones and the shared count from the indicators.
  have key : ∀ f ∈ C.biUnion faces,
      (C.filter (fun x => f ∈ faces x)).card
        = 1 + (if (C.filter (fun x => f ∈ faces x)).card = 2 then 1 else 0) := by
    intro f hf
    rcases hall f hf with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
  have hcf : (∑ f ∈ C.biUnion faces,
        (if (C.filter (fun x => f ∈ faces x)).card = 2 then 1 else 0))
      = ((C.biUnion faces).filter
        (fun f => (C.filter (fun x => f ∈ faces x)).card = 2)).card :=
    (Finset.card_filter _ _).symm
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
    hcf]

#print axioms owners_one_or_two
#print axioms boundary_card_of_shared

/-- A face carried by two cubes of the path, one a step from the other, lies in the image of
`crossFace s`. The coordinate sum identifies both cubes' indices and forces the second to be the
first plus one; `step_axis_inj` identifies the step's axis with `s` at that index, and
`shared_face_eq` names the face.

DERIVED: `3` is the dimension; the index increment is `cubePos_succ_eq_step`'s. -/
theorem crossFace_of_step {k : ℕ} (s : Fin k → Fin 3) {x : Cube} {a : Fin 3} {f : Face}
    (hx : x ∈ MassGap.VortexEntropy.cubeConfig s) (hy : step a x ∈ MassGap.VortexEntropy.cubeConfig s)
    (hxf : f ∈ faces x) (hyf : f ∈ faces (step a x)) :
    f ∈ Finset.univ.image (crossFace s) := by
  classical
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, hjy⟩ := Finset.mem_image.mp hy
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  -- the coordinate sum is the index, and a step raises it by one, so `j = i + 1`
  have hsi : ∑ b, x b = i := by rw [← hix]; exact MassGap.VortexEntropy.cubePos_sum_le s hik
  have hsj : ∑ b, step a x b = j := by rw [← hjy]; exact MassGap.VortexEntropy.cubePos_sum_le s hjk
  have hji : j = i + 1 := by rw [← hsj, sum_step a x, hsi]
  have hik' : i < k := by omega
  refine Finset.mem_image.mpr ⟨⟨i, hik'⟩, Finset.mem_univ _, ?_⟩
  -- the axis of the step is the path's own step at `i`
  have hsucc : MassGap.VortexEntropy.cubePos s (i + 1) = step (s ⟨i, hik'⟩) (MassGap.VortexEntropy.cubePos s i) :=
    cubePos_succ_eq_step s ⟨i, hik'⟩
  have hstep : step a x = step (s ⟨i, hik'⟩) x := by
    rw [← hjy, hji, hsucc, hix]
  have haxis : a = s ⟨i, hik'⟩ := step_axis_inj hstep
  show ((s ⟨i, hik'⟩ : Fin 3), MassGap.VortexEntropy.cubePos s (i + 1)) = f
  rw [shared_face_eq hxf hyf, ← hjy, hji, haxis]

/-- The two-owner faces of `cubeConfig s` are exactly the image of `crossFace s`.

Forward: two owners are a step apart (`step_rel_of_shares`), the pair is consecutive through the
coordinate sum (`sum_dist_one_of_shares`), and `crossFace_of_step` names the face. Backward: each
crossed face has two distinct owners on the path (`crossFace_shared`, `cubePos_injOn`), and
`card_cubes_with_face_le_two` caps the count at two.

DERIVED: `2` is the owner count that marks a face as shared, `card_cubes_with_face_le_two`'s bound;
`3` is the dimension. -/
theorem sharedFaces_eq_crossFaces {k : ℕ} (s : Fin k → Fin 3) :
    ((MassGap.VortexEntropy.cubeConfig s).biUnion faces).filter
        (fun f => ((MassGap.VortexEntropy.cubeConfig s).filter (fun x => f ∈ faces x)).card = 2)
      = Finset.univ.image (crossFace s) := by
  classical
  ext f
  constructor
  · intro hf
    obtain ⟨hfB, hf2⟩ := Finset.mem_filter.mp hf
    have h1 : 1 < ((MassGap.VortexEntropy.cubeConfig s).filter (fun x => f ∈ faces x)).card := by omega
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h1
    obtain ⟨hxC, hxf⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyC, hyf⟩ := Finset.mem_filter.mp hy
    rcases step_rel_of_shares hxf hyf with h | ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact absurd h hxy
    · exact crossFace_of_step s hxC hyC hxf hyf
    · exact crossFace_of_step s hyC hxC hyf hxf
  · intro hf
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hf
    have hjm : MassGap.VortexEntropy.cubePos s (j : ℕ) ∈ MassGap.VortexEntropy.cubeConfig s :=
      Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by have := j.isLt; omega))
    have hj1m : MassGap.VortexEntropy.cubePos s ((j : ℕ) + 1) ∈ MassGap.VortexEntropy.cubeConfig s :=
      Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by have := j.isLt; omega))
    obtain ⟨hin0, hin1⟩ := Finset.mem_inter.mp (crossFace_shared s j)
    -- the two owners are distinct: the path never revisits a cube
    have hne : MassGap.VortexEntropy.cubePos s (j : ℕ) ≠ MassGap.VortexEntropy.cubePos s ((j : ℕ) + 1) := by
      intro h
      have hi : (j : ℕ) ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by have := j.isLt; omega)
      have hi1 : (j : ℕ) + 1 ∈ Finset.range (k + 1) :=
        Finset.mem_range.mpr (by have := j.isLt; omega)
      have := cubePos_injOn s hi hi1 h
      omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨_, hjm, hin0⟩, ?_⟩
    have hle := card_cubes_with_face_le_two (MassGap.VortexEntropy.cubeConfig s) (crossFace s j)
    have hge : 1 < ((MassGap.VortexEntropy.cubeConfig s).filter
        (fun x => crossFace s j ∈ faces x)).card :=
      Finset.one_lt_card.mpr ⟨_, Finset.mem_filter.mpr ⟨hjm, hin0⟩, _,
        Finset.mem_filter.mpr ⟨hj1m, hin1⟩, hne⟩
    omega

/-- The two-owner faces of `cubeConfig s` number exactly `k`: `sharedFaces_eq_crossFaces` followed by
`card_crossFaces`.

DERIVED: `2` is the owner count marking a face as shared; `3` is the dimension. The count `k` is the
number of steps, not a literal. -/
theorem card_sharedFaces {k : ℕ} (s : Fin k → Fin 3) :
    (((MassGap.VortexEntropy.cubeConfig s).biUnion faces).filter
      (fun f => ((MassGap.VortexEntropy.cubeConfig s).filter (fun x => f ∈ faces x)).card = 2)).card = k := by
  rw [sharedFaces_eq_crossFaces s, card_crossFaces s]

/-- **The boundary of a cube configuration**: the faces with exactly one owner. A face with two
owners is interior — the two cubes cancel across it — and `owners_one_or_two` says there is no third
case, so this really is the surface of the union.

DERIVED: `1` is the arity of the owner count, not a magnitude: `owners_one_or_two` proves every face
of the configuration has one owner or two, so "exactly one" is the complement of "shared" and the
only other case there is. -/
noncomputable def boundaryFaces (C : Finset Cube) : Finset Face :=
  (C.biUnion faces).filter (fun f => (C.filter (fun x => f ∈ faces x)).card = 1)

/-- `(boundaryFaces (cubeConfig s)).card = 4 * k + 6`, for every `s : Fin k → Fin 3`.

Four inputs, each a theorem of this file:

* `card_faces` — a cube has six faces, two per axis.
* `card_cubeConfig` — the path visits `k + 1` distinct cubes.
* `card_cubes_with_face_le_two` and `owners_one_or_two` — every touched face has one or two owners.
* `card_sharedFaces` — the two-owner faces number exactly `k`.

`incidence_left` evaluates the double count's left side as `6(k+1)`, `boundary_card_of_shared` reads
its right side as `|B| + k`, so `|B| = 5k + 6`; splitting `B` into one-owner and two-owner faces
drops the shared ones once more, leaving `4k + 6`.

DERIVED: `4` is `6 − 2`, the six faces of a cube less twice the one shared per step, so it is the two
counts above and not a chosen coefficient. `6` is the face count of a cube, from `card_faces`; `2` is
the owner count of a shared face; `1` is the owner count of a boundary face, inside `boundaryFaces`;
`3` is the dimension. -/
theorem boundary_card_eq {k : ℕ} (s : Fin k → Fin 3) :
    (boundaryFaces (MassGap.VortexEntropy.cubeConfig s)).card = 4 * k + 6 := by
  classical
  rw [boundaryFaces]
  set C := MassGap.VortexEntropy.cubeConfig s with hC
  set B := C.biUnion faces with hB
  -- the double count fixes `|B|`
  have hdc : ∑ x ∈ C, (faces x).card = B.card + k := by
    refine boundary_card_of_shared C k (fun f hf => ?_) (card_sharedFaces s)
    have := owners_one_or_two C hf
    omega
  have hleft : ∑ x ∈ C, (faces x).card = 6 * (k + 1) := incidence_left s
  -- and the one-owner and two-owner faces exhaust it
  have hsplit : (B.filter (fun f => (C.filter (fun x => f ∈ faces x)).card = 1)).card
      + (B.filter (fun f => ¬ (C.filter (fun x => f ∈ faces x)).card = 1)).card = B.card :=
    Finset.filter_card_add_filter_neg_card_eq_card _
  have hflip : B.filter (fun f => ¬ (C.filter (fun x => f ∈ faces x)).card = 1)
      = B.filter (fun f => (C.filter (fun x => f ∈ faces x)).card = 2) := by
    refine Finset.filter_congr (fun f hf => ?_)
    have := owners_one_or_two C hf
    constructor
    · intro h; omega
    · intro h; omega
  rw [hflip, card_sharedFaces s] at hsplit
  omega

#print axioms crossFace_of_step
#print axioms sharedFaces_eq_crossFaces
#print axioms card_sharedFaces
#print axioms boundary_card_eq

/-! ### Distinct paths give distinct boundaries

`directed_surface_count` counts cube configurations. `boundaryFaces_cubeConfig_injective`
shows the boundary map does not collapse two configurations onto one face-set, so the count of `3 ^ k`
transfers to the boundaries, each of cardinality `4 * k + 6`. -/

/-- Whatever the configuration, the cubes carrying `(a, step a p)` lie in `{step a p, p}` — the
corner itself and the cube one step back. `cube_of_face` and `step_injective`.

DERIVED: `3` is the dimension; the statement carries no literal, the unit step being inside `step`. -/
theorem owners_subset_pair (C : Finset Cube) (a : Fin 3) (p : Cube) :
    C.filter (fun y => ((a, step a p) : Face) ∈ faces y) ⊆ {step a p, p} := by
  classical
  intro y hy
  rw [Finset.mem_filter] at hy
  rcases cube_of_face hy.2 with h | h
  · exact Finset.mem_insert.mpr (Or.inl h)
  · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (step_injective a h))

/-- `f ∈ boundaryFaces C ↔ f ∈ C.biUnion faces ∧ (C.filter (fun x => f ∈ faces x)).card = 1`, by
`Finset.mem_filter`: membership in the boundary unfolded once.

DERIVED: `1` is the owner count a boundary face has, `boundaryFaces`'s own; `3` is the dimension. -/
theorem mem_boundaryFaces_iff (C : Finset Cube) (f : Face) :
    f ∈ boundaryFaces C
      ↔ f ∈ C.biUnion faces ∧ (C.filter (fun x => f ∈ faces x)).card = 1 :=
  Finset.mem_filter

/-- `p ≠ step a p`: a step never returns to where it started, because `sum_step` raises the
coordinate sum.

DERIVED: `3` is the dimension; the unit step is inside `step` and the statement carries no
literal. -/
theorem ne_step (a : Fin 3) (p : Cube) : p ≠ step a p := by
  intro hpx
  have hs := sum_step a p
  rw [← hpx] at hs
  omega

/-- If a configuration holds both ends of a step, the face between them is not on its boundary: the
two cubes are distinct (`ne_step`) and both own the face, so the owner count exceeds one.

DERIVED: `1` is the owner count a boundary face has, from `boundaryFaces` via
`mem_boundaryFaces_iff`; `3` is the dimension. -/
theorem not_mem_boundaryFaces_of_both {C : Finset Cube} {a : Fin 3} {p : Cube}
    (hp : p ∈ C) (hq : step a p ∈ C) : ((a, step a p) : Face) ∉ boundaryFaces C := by
  classical
  have hfp : ((a, step a p) : Face) ∈ faces p := mem_faces.mpr ⟨a, Or.inr rfl⟩
  have hfq : ((a, step a p) : Face) ∈ faces (step a p) := mem_faces.mpr ⟨a, Or.inl rfl⟩
  have hge : 1 < (C.filter (fun y => ((a, step a p) : Face) ∈ faces y)).card :=
    Finset.one_lt_card.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hfp⟩, step a p,
      Finset.mem_filter.mpr ⟨hq, hfq⟩, ne_step a p⟩
  intro hmem
  have h1 := ((mem_boundaryFaces_iff C _).mp hmem).2
  omega

/-- If a configuration holds one end of a step and the face between the two ends is not on its
boundary, it holds the other end too. `owners_one_or_two` makes the owner count one or two, the
hypothesis rules out one, and `owners_subset_pair` then forces the owner set to be exactly
`{step a p, p}`.

The recovery step `mem_of_boundary_eq_aux` runs on.

DERIVED: `2` is the owner count a non-boundary face of the union has, and `1` the count a boundary
face has; `3` is the dimension. -/
theorem mem_of_not_mem_boundaryFaces {C : Finset Cube} {a : Fin 3} {p : Cube}
    (hp : p ∈ C) (hnb : ((a, step a p) : Face) ∉ boundaryFaces C) : step a p ∈ C := by
  classical
  have hfp : ((a, step a p) : Face) ∈ faces p := mem_faces.mpr ⟨a, Or.inr rfl⟩
  have hfB : ((a, step a p) : Face) ∈ C.biUnion faces := Finset.mem_biUnion.mpr ⟨p, hp, hfp⟩
  obtain ⟨h1, h2⟩ := owners_one_or_two C hfB
  have hcard : (C.filter (fun y => ((a, step a p) : Face) ∈ faces y)).card = 2 := by
    rcases Nat.lt_or_ge (C.filter (fun y => ((a, step a p) : Face) ∈ faces y)).card 2 with hlt | hge
    · exact absurd ((mem_boundaryFaces_iff C _).mpr ⟨hfB, by omega⟩) hnb
    · omega
  have hpair : ({step a p, p} : Finset Cube).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (by simp)
  have heq : C.filter (fun y => ((a, step a p) : Face) ∈ faces y) = {step a p, p} :=
    Finset.eq_of_subset_of_card_le (owners_subset_pair C a p) (by rw [hcard]; exact hpair)
  have hmem : step a p ∈ C.filter (fun y => ((a, step a p) : Face) ∈ faces y) := by
    rw [heq]; exact Finset.mem_insert_self _ _
  exact (Finset.mem_filter.mp hmem).1

/-- If two paths have equal boundaries, every cube of the first configuration is a cube of the
second. Induction on the coordinate sum: at sum `0` the cube is the origin, which every configuration
contains; at sum `i + 1` the cube is a step from one of sum `i`, which the inductive hypothesis puts
in the second configuration, and the face between them is not on the first boundary
(`not_mem_boundaryFaces_of_both`) hence not on the second, so
`mem_of_not_mem_boundaryFaces` supplies the cube.

DERIVED: `3` is the dimension; the induction's `0` and `i + 1` are `Nat.rec`'s and the unit step is
inside `step`. The statement itself carries no literal. -/
theorem mem_of_boundary_eq_aux {k : ℕ} (s t : Fin k → Fin 3)
    (h : boundaryFaces (MassGap.VortexEntropy.cubeConfig s) = boundaryFaces (MassGap.VortexEntropy.cubeConfig t)) :
    ∀ n : ℕ, ∀ x : Cube, (∑ b, x b) = n → x ∈ MassGap.VortexEntropy.cubeConfig s → x ∈ MassGap.VortexEntropy.cubeConfig t := by
  classical
  intro n
  induction n with
  | zero =>
    intro x hsum _
    -- coordinate sum zero is the origin, and every path starts there
    have hx0 : x = MassGap.VortexEntropy.cubePos t 0 := by
      funext a
      have hxa : x a = 0 := (Finset.sum_eq_zero_iff.mp hsum) a (Finset.mem_univ a)
      rw [hxa, MassGap.VortexEntropy.cubePos]
      simp
    rw [hx0]
    exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (Nat.succ_pos k))
  | succ i ih =>
    intro x hsum hxs
    obtain ⟨m, hm, hmx⟩ := Finset.mem_image.mp hxs
    have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hmi : m = i + 1 := by
      rw [← MassGap.VortexEntropy.cubePos_sum_le s hmk, hmx, hsum]
    subst hmi
    have hik : i < k := by omega
    have hxstep : x = step (s ⟨i, hik⟩) (MassGap.VortexEntropy.cubePos s i) := by
      rw [← hmx]; exact cubePos_succ_eq_step s ⟨i, hik⟩
    have hps : MassGap.VortexEntropy.cubePos s i ∈ MassGap.VortexEntropy.cubeConfig s :=
      Finset.mem_image_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_of_lt hik))
    have hpsum : (∑ b, MassGap.VortexEntropy.cubePos s i b) = i := MassGap.VortexEntropy.cubePos_sum_le s (le_of_lt hik)
    have hpt : MassGap.VortexEntropy.cubePos s i ∈ MassGap.VortexEntropy.cubeConfig t := ih _ hpsum hps
    have hxs' : step (s ⟨i, hik⟩) (MassGap.VortexEntropy.cubePos s i) ∈ MassGap.VortexEntropy.cubeConfig s := hxstep ▸ hxs
    have hnotL := not_mem_boundaryFaces_of_both hps hxs'
    rw [h] at hnotL
    rw [hxstep]
    exact mem_of_not_mem_boundaryFaces hpt hnotL

/-- `fun s => boundaryFaces (cubeConfig s)` is injective on `Fin k → Fin 3`.
`mem_of_boundary_eq_aux` in both directions makes the two configurations equal, and
`cubeConfig_injective` descends to the step sequences.

Stronger than distinctness of configurations: the boundary map does not collapse two of them.

DERIVED: `3` is the dimension, the range of the step alphabet; no other numeral. -/
theorem boundaryFaces_cubeConfig_injective {k : ℕ} :
    Function.Injective (fun s : Fin k → Fin 3 => boundaryFaces (MassGap.VortexEntropy.cubeConfig s)) := by
  intro s t h
  refine MassGap.VortexEntropy.cubeConfig_injective ?_
  ext x
  exact ⟨fun hx => mem_of_boundary_eq_aux s t h _ x rfl hx,
    fun hx => mem_of_boundary_eq_aux t s h.symm _ x rfl hx⟩

/-- There is a `Finset (Finset Face)` of cardinality `3 ^ k` every member of which has cardinality
`4 * k + 6`. The witness is the image of `fun s => boundaryFaces (cubeConfig s)`; its cardinality is
`directed_paths_card` transported along `boundaryFaces_cubeConfig_injective`, and the member
cardinality is `boundary_card_eq`.

A statement about `Finset`s of faces. It says nothing about an entropy density or a limit; the
quotient `(k log 3)/(4k + 6)` is `floor_density_limit`'s, reindexed.

DERIVED: `3` is the dimension and the base of the count — the same number, since the step alphabet is
`Fin 3`. `4` and `6` are `boundary_card_eq`'s, the six faces of a cube less twice the one shared per
step. -/
theorem directed_surfaces_count_and_area {k : ℕ} :
    ∃ S : Finset (Finset Face), S.card = 3 ^ k ∧ ∀ F ∈ S, F.card = 4 * k + 6 := by
  classical
  refine ⟨Finset.univ.image (fun s : Fin k → Fin 3 => boundaryFaces (MassGap.VortexEntropy.cubeConfig s)),
    ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ boundaryFaces_cubeConfig_injective, Finset.card_univ,
      MassGap.VortexEntropy.directed_paths_card]
  · intro F hF
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hF
    exact boundary_card_eq s

#print axioms owners_subset_pair
#print axioms not_mem_boundaryFaces_of_both
#print axioms mem_of_not_mem_boundaryFaces
#print axioms mem_of_boundary_eq_aux
#print axioms boundaryFaces_cubeConfig_injective
#print axioms directed_surfaces_count_and_area

#print axioms incidence_double_count
#print axioms incidence_left

#print axioms crossFace_injective
#print axioms crossFace_shared
#print axioms card_crossFaces

#print axioms step_injective
#print axioms card_faces
#print axioms step_rel_of_shares
#print axioms sum_dist_one_of_shares
#print axioms cubePos_succ_eq_step
#print axioms shares_succ

end MassGap.VortexEntropy.CubeArea



namespace MassGap.VortexEntropy.SurfaceEmbed

open MassGap.VortexEntropy.CubeArea MassGap.WilsonHypercubic

/-- The plane a face normal names: the two axes the normal is not, in cyclic order, as a pair in
`Fin 4 × Fin 4`.

Both components land in the first three axes, since the offsets are reduced mod `3`; the fourth axis
is never produced.

DERIVED: `3` is the sublattice dimension, and the modulus the cyclic order runs in. `1` and `2` are
the two offsets from the normal, which pick out the other two axes of that sublattice. `4` is the
physical dimension the pair is read inside. -/
def planeOf (a : Fin 3) : Fin 4 × Fin 4 :=
  (⟨((a : ℕ) + 1) % 3, by omega⟩, ⟨((a : ℕ) + 2) % 3, by omega⟩)

/-- `planeOf` is injective: the normal is recoverable from the first component of the plane, since
`a ↦ (a + 1) % 3` is injective on `Fin 3`. -/
theorem planeOf_injective : Function.Injective planeOf := by
  intro a b hab
  have h1 : ((a : ℕ) + 1) % 3 = ((b : ℕ) + 1) % 3 := congrArg (fun p => (p.1 : ℕ)) hab
  have ha := a.isLt
  have hb := b.isLt
  exact Fin.ext (by omega)

/-- A cube corner placed in the box: the first three coordinates are the cube coordinates reduced
mod `n`, the fourth is `0`.

The reduction is what makes this total on all of `Cube`; it is faithful only below `n`, which is what
`siteOf_inj_of_lt` requires. `NeZero n` is needed for the box to be inhabited.

DERIVED: `3` is the sublattice dimension, the number of coordinates carried over. `4` is the physical
dimension of the target `Site 4 n`. `0` is the fourth coordinate: the construction fixes one time
slice rather than choosing among them. -/
def siteOf (n : ℕ) [NeZero n] (x : Cube) : Site 4 n :=
  fun μ => if h : (μ : ℕ) < 3 then ⟨x ⟨(μ : ℕ), h⟩ % n, Nat.mod_lt _ (NeZero.pos n)⟩
           else ⟨0, NeZero.pos n⟩

/-- `siteOf n` is injective on cube corners whose every coordinate is below `n`: under that
hypothesis the periodic reduction is the identity, so equal placements have equal coordinates.

Both corners must satisfy the bound; the conclusion is equality in `Cube`, the full three-coordinate
function, not just on the coordinates the site records.

DERIVED: `n` is the box extent and the modulus; the statement carries no numeral of its own. -/
theorem siteOf_inj_of_lt {n : ℕ} [NeZero n] {x y : Cube}
    (hx : ∀ a, x a < n) (hy : ∀ a, y a < n) (h : siteOf n x = siteOf n y) : x = y := by
  funext a
  have ha : (a : ℕ) < 3 := a.isLt
  have hcong := congrFun h ⟨(a : ℕ), by omega⟩
  have hval := congrArg Fin.val hcong
  simp only [siteOf, ha, dif_pos] at hval
  rw [Nat.mod_eq_of_lt (hx _), Nat.mod_eq_of_lt (hy _)] at hval
  simpa using hval

/-- A face becomes a plaquette: its normal becomes the plane `planeOf f.1`, its corner the site
`siteOf n f.2`.

DERIVED: `4` is the dimension of the physical lattice, fixed by the target type `Plaq 4 n`. It is the
only numeral in the statement; the sublattice dimension enters through `Face` and `planeOf`. -/
def faceToPlaq (n : ℕ) [NeZero n] (f : Face) : Plaq 4 n := (planeOf f.1, siteOf n f.2)

/-- `faceToPlaq n` is injective on faces whose corners have every coordinate below `n`.

The two components separate: `planeOf_injective` recovers the normal, `siteOf_inj_of_lt` recovers
the corner. The bound is required of both faces, and it is a hypothesis about the corners only. -/
theorem faceToPlaq_inj_on {n : ℕ} [NeZero n] {f g : Face}
    (hf : ∀ a, f.2 a < n) (hg : ∀ a, g.2 a < n)
    (h : faceToPlaq n f = faceToPlaq n g) : f = g := by
  have h1 : planeOf f.1 = planeOf g.1 := congrArg Prod.fst h
  have h2 : siteOf n f.2 = siteOf n g.2 := congrArg Prod.snd h
  exact Prod.ext (planeOf_injective h1) (siteOf_inj_of_lt hf hg h2)

/-! ### The path stays in the box -/

/-- Every coordinate of the `i`-th cube on a path is at most `i`, for `i ≤ k`.

The coordinate sum is exactly `i` (`cubePos_sum_le`), and a single term of a sum of naturals is
at most the sum. The bound is on each coordinate separately, not on their sum.

DERIVED: `3` is the step alphabet `Fin 3` of the cube path; it is the only numeral in the
statement. -/
theorem cubePos_coord_le {k : ℕ} (s : Fin k → Fin 3) {i : ℕ} (hi : i ≤ k) (a : Fin 3) :
    MassGap.VortexEntropy.cubePos s i a ≤ i := by
  classical
  have hsum : ∑ b, MassGap.VortexEntropy.cubePos s i b = i := MassGap.VortexEntropy.cubePos_sum_le s hi
  have hle : MassGap.VortexEntropy.cubePos s i a ≤ ∑ b, MassGap.VortexEntropy.cubePos s i b :=
    Finset.single_le_sum (f := fun b => MassGap.VortexEntropy.cubePos s i b)
      (fun b _ => Nat.zero_le _) (Finset.mem_univ a)
  omega

/-- Every coordinate of every corner used by a face of a `k`-step path's configuration is at most
`k + 1`.

A cube of the configuration sits at coordinates at most `k` by `cubePos_coord_le`, and a face is
either that cube's own corner or the corner one step along an axis, which adds at most one. The bound
is uniform over the path, the cube index and the axis.

DERIVED: `3` is the step alphabet `Fin 3`. `1` is the single step a face's corner may sit beyond its
cube's, which is where the `k + 1` comes from. -/
theorem face_corner_le {k : ℕ} (s : Fin k → Fin 3) {f : Face} {x : Cube}
    (hx : x ∈ MassGap.VortexEntropy.cubeConfig s) (hf : f ∈ faces x) (a : Fin 3) :
    f.2 a ≤ k + 1 := by
  classical
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hbase : MassGap.VortexEntropy.cubePos s i a ≤ k := le_trans (cubePos_coord_le s hik a) hik
  obtain ⟨b, hb⟩ := mem_faces.mp hf
  rcases hb with rfl | rfl
  · show MassGap.VortexEntropy.cubePos s i a ≤ k + 1
    omega
  · show step b (MassGap.VortexEntropy.cubePos s i) a ≤ k + 1
    by_cases hab : a = b
    · subst hab
      rw [step_self]
      omega
    · rw [step_other hab]
      omega

/-! ### The surfaces, over plaquettes -/

/-- The image of a directed path's boundary faces under `faceToPlaq n`, as a
`Finset (Plaq 4 n)`.

Taking an image can collapse elements; `card_plaqSurface` is what recovers the size, and it needs the
box hypothesis. `noncomputable` because the image is taken classically.

DERIVED: `3` is the step alphabet `Fin k → Fin 3` of the path, and `4` is the physical dimension of
the target plaquettes. Both are inherited from `faceToPlaq` and the path type; neither is chosen
here. -/
noncomputable def plaqSurface (n : ℕ) [NeZero n] {k : ℕ} (s : Fin k → Fin 3) :
    Finset (Plaq 4 n) :=
  (boundaryFaces (MassGap.VortexEntropy.cubeConfig s)).image (faceToPlaq n)

/-- Under `hk : k + 1 < n`, every coordinate of every boundary face's corner is below `n`.

`face_corner_le` bounds the corner by `k + 1`, and `hk` puts that below `n`. This is the hypothesis
`faceToPlaq_inj_on` consumes, produced for the faces a surface actually uses.

DERIVED: `1` is the single step in `k + 1`, the reach of a face beyond its cube. `3` is the step
alphabet `Fin 3` of the path. -/
theorem boundary_corner_lt {n k : ℕ} (hk : k + 1 < n) (s : Fin k → Fin 3)
    {f : Face} (hf : f ∈ boundaryFaces (MassGap.VortexEntropy.cubeConfig s)) (a : Fin 3) :
    f.2 a < n := by
  classical
  have hfB : f ∈ (MassGap.VortexEntropy.cubeConfig s).biUnion faces := (Finset.mem_filter.mp hf).1
  obtain ⟨x, hx, hfx⟩ := Finset.mem_biUnion.mp hfB
  have := face_corner_le s hx hfx a
  omega

/-- A `k`-step path's plaquette surface has exactly `4 * k + 6` elements, given `k + 1 < n`.

The image has the same size as the source because `faceToPlaq n` is injective on the boundary faces
(`boundary_corner_lt` supplies the bound, `faceToPlaq_inj_on` the injectivity), and
`CubeArea.boundary_card_eq` gives the source's size. The box hypothesis is what rules out two faces
wrapping onto the same plaquette.

DERIVED: `4` and `6` are the boundary-face count of a `k`-step cube path, carried over from
`CubeArea.boundary_card_eq`, and `4` is also the physical dimension in `Plaq 4 n`. `1` is the step in
`k + 1`. `3` is the step alphabet `Fin 3`. -/
theorem card_plaqSurface {n k : ℕ} [NeZero n] (hk : k + 1 < n) (s : Fin k → Fin 3) :
    (plaqSurface n s).card = 4 * k + 6 := by
  classical
  rw [plaqSurface, Finset.card_image_of_injOn, boundary_card_eq s]
  intro f hf g hg h
  exact faceToPlaq_inj_on (boundary_corner_lt hk s hf) (boundary_corner_lt hk s hg) h

/-- `plaqSurface n` is injective on `Fin k → Fin 3`, given `k + 1 < n`.

`CubeArea.boundaryFaces_cubeConfig_injective` transported along the embedding: equal images force
equal boundary-face sets, because `faceToPlaq_inj_on` is available on both sides under the box
hypothesis, and distinct boundaries come from distinct paths.

DERIVED: `1` is the step in `k + 1`, and `3` is the step alphabet `Fin 3` of the paths. -/
theorem plaqSurface_injective {n k : ℕ} [NeZero n] (hk : k + 1 < n) :
    Function.Injective (fun s : Fin k → Fin 3 => plaqSurface n s) := by
  classical
  intro s t h
  have h' : plaqSurface n s = plaqSurface n t := h
  refine boundaryFaces_cubeConfig_injective ?_
  show boundaryFaces (MassGap.VortexEntropy.cubeConfig s) = boundaryFaces (MassGap.VortexEntropy.cubeConfig t)
  ext f
  constructor
  · intro hf
    have himg : faceToPlaq n f ∈ plaqSurface n t := by
      rw [← h']; exact Finset.mem_image_of_mem _ hf
    obtain ⟨g, hg, hgf⟩ := Finset.mem_image.mp himg
    have := faceToPlaq_inj_on (boundary_corner_lt hk t hg) (boundary_corner_lt hk s hf) hgf
    exact this ▸ hg
  · intro hf
    have himg : faceToPlaq n f ∈ plaqSurface n s := by
      rw [h']; exact Finset.mem_image_of_mem _ hf
    obtain ⟨g, hg, hgf⟩ := Finset.mem_image.mp himg
    have := faceToPlaq_inj_on (boundary_corner_lt hk s hg) (boundary_corner_lt hk t hf) hgf
    exact this ▸ hg

/-- Given `k + 1 < n`, there is a `Finset (Finset (Plaq 4 n))` of size `3 ^ k` whose every member
has exactly `4 * k + 6` elements.

The witness is the image of the path space under `plaqSurface n`: `plaqSurface_injective` gives its
size via `directed_paths_card`, and `card_plaqSurface` gives each member's.

Scope: this is an existence statement about one box, at a `k` the box is large enough for. It does
not say the family is unique, maximal, or contained in any physical vortex family.

DERIVED: `3` is the step alphabet `Fin 3` of the paths, so `3 ^ k` is the path count. `4` and `6` are
the boundary-face count of a `k`-step path, and `4` is also the physical dimension in `Plaq 4 n`. `1`
is the step in `k + 1`. -/
theorem directed_plaq_surfaces_count_and_area {n k : ℕ} [NeZero n] (hk : k + 1 < n) :
    ∃ S : Finset (Finset (Plaq 4 n)),
      S.card = 3 ^ k ∧ ∀ F ∈ S, F.card = 4 * k + 6 := by
  classical
  refine ⟨Finset.univ.image (fun s : Fin k → Fin 3 => plaqSurface n s), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (plaqSurface_injective hk), Finset.card_univ,
      MassGap.VortexEntropy.directed_paths_card]
  · intro F hF
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hF
    exact card_plaqSurface hk s

/-- If a family `V` of plaquette sets contains `plaqSurface n s` for every `k`-step path `s`, and
`k + 1 < n`, then `3 ^ k ≤ V.card`.

The image of the path space is a subset of `V` and has size `3 ^ k` by `plaqSurface_injective` and
`directed_paths_card`, so `Finset.card_le_card` finishes.

Scope: the containment `hsub` is a hypothesis. Nothing here shows that a family of physical vortex
surfaces contains the directed ones, and `V` is otherwise arbitrary.

DERIVED: `3` is the step alphabet `Fin 3` of the paths, so `3 ^ k` is their count. `4` is the physical
dimension in `Plaq 4 n`. `1` is the step in `k + 1`. -/
theorem three_pow_le_card_of_plaq_subfamily {n k : ℕ} [NeZero n] (hk : k + 1 < n)
    (V : Finset (Finset (Plaq 4 n)))
    (hsub : ∀ s : Fin k → Fin 3, plaqSurface n s ∈ V) :
    3 ^ k ≤ V.card := by
  classical
  have himg : Finset.univ.image (fun s : Fin k → Fin 3 => plaqSurface n s) ⊆ V := by
    intro F hF
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hF
    exact hsub s
  calc 3 ^ k = (Finset.univ.image (fun s : Fin k → Fin 3 => plaqSurface n s)).card := by
        rw [Finset.card_image_of_injective _ (plaqSurface_injective hk), Finset.card_univ,
          MassGap.VortexEntropy.directed_paths_card]
    _ ≤ V.card := Finset.card_le_card himg

/-- The count bound at every `k` at once, along a `k`-indexed sequence of boxes: given extents `n k`
with `k + 1 < n k`, and families `V k` each containing the `k`-step directed surfaces in its own box,
`3 ^ k ≤ (V k).card` for every `k`.

`three_pow_le_card_of_plaq_subfamily` applied at each `k`.

Scope: the box is indexed by `k`, and it has to be — the embedding is injective only while
`k + 1 < n`, so no single extent supports the bound at every `k`. Each `V k` lives in its own box and
the statement relates none of them to any other; `hsub` is a hypothesis at every `k`. This is the
shape `hM : ∀ k, 3 ^ k ≤ M k` takes for a consumer that passes to a `k → ∞` limit.

DERIVED: `3` is the step alphabet `Fin 3` of the paths. `4` is the physical dimension in
`Plaq 4 (n k)`. `1` is the step in `k + 1 < n k`. -/
theorem three_pow_le_card_along_boxes (n : ℕ → ℕ) [∀ k, NeZero (n k)]
    (hn : ∀ k, k + 1 < n k)
    (V : ∀ k, Finset (Finset (Plaq 4 (n k))))
    (hsub : ∀ k (s : Fin k → Fin 3), plaqSurface (n k) s ∈ V k) :
    ∀ k, 3 ^ k ≤ (V k).card :=
  fun k => three_pow_le_card_of_plaq_subfamily (hn k) (V k) (hsub k)

#print axioms three_pow_le_card_along_boxes

#print axioms planeOf_injective
#print axioms siteOf_inj_of_lt
#print axioms faceToPlaq_inj_on
#print axioms cubePos_coord_le
#print axioms face_corner_le
#print axioms boundary_corner_lt
#print axioms card_plaqSurface
#print axioms plaqSurface_injective
#print axioms directed_plaq_surfaces_count_and_area
#print axioms three_pow_le_card_of_plaq_subfamily

end MassGap.VortexEntropy.SurfaceEmbed



namespace MassGap.VortexEntropy

open Filter Topology

/-- The counted weight at `k` steps: `(3 : ℝ) ^ k * Real.exp (-μ * (4 * k + 6))`. The first factor is
the number of directed cube paths `Fin k → Fin 3`, which `directed_surface_count` computes; the
second is `exp (-μ * A)` at `A` the common boundary area of the surfaces those paths bound, which
`CubeArea.boundary_card_eq` computes. `floor_count_injection` and `floorTerm_exponent_is_the_area`
state those two identifications.

Scope: `μ` is an arbitrary real, of either sign; `floorTerm μ k` is strictly positive at every `μ`
and `k`.

DERIVED: `3` is the branching factor of a directed cube path, the cardinality of `Fin 3` at each of
the `k` steps. `4` and `6` are the boundary area `4 * k + 6`, equal to `4 * (k + 1) + 2`: six faces
per cube over `k + 1` cubes, less two per shared face over the `k` shared ones. -/
noncomputable def floorTerm (μ : ℝ) (k : ℕ) : ℝ := (3 : ℝ) ^ k * Real.exp (-μ * (4 * (k : ℝ) + 6))

/-- For every directed cube path `s : Fin k → Fin 3`,
`(CubeArea.boundaryFaces (cubeConfig s)).card = 4 * k + 6` as a real. It is
`CubeArea.boundary_card_eq` cast to `ℝ`, which is the form `floorTerm`'s exponent is written in.

Scope: the equality holds for every `s` — the area does not depend on which path is taken — which is
what makes a single exponent correct for the whole family of `3 ^ k` surfaces.

DERIVED: `3` is the branching factor, the cardinality of `Fin 3` at each step; `4` and `6` are the
boundary area `4 * k + 6`, from `CubeArea.boundary_card_eq`. -/
theorem floorTerm_exponent_is_the_area {k : ℕ} (s : Fin k → Fin 3) :
    ((MassGap.VortexEntropy.CubeArea.boundaryFaces (MassGap.VortexEntropy.cubeConfig s)).card : ℝ) = 4 * (k : ℝ) + 6 := by
  rw [MassGap.VortexEntropy.CubeArea.boundary_card_eq s]
  push_cast
  ring

/-- `floorTerm μ k = (Finset.univ.image (@cubeConfig k)).card * Real.exp (-μ * (4 * k + 6))`: the
first factor of `floorTerm` is the cardinality of the image of `cubeConfig`, by
`MassGap.VortexEntropy.directed_surface_count`. So a weight dominating the counted family's weight dominates
`floorTerm`.

Scope: an identity, holding at every real `μ` and every `k`.

DERIVED: `4` and `6` are the boundary area `4 * k + 6`, carried over from `floorTerm`. The `3` is
not written here — it has been replaced by the cardinality expression this theorem equates it to. -/
theorem floor_count_injection (μ : ℝ) (k : ℕ) :
    floorTerm μ k
      = ((Finset.univ.image (@MassGap.VortexEntropy.cubeConfig k)).card : ℝ) * Real.exp (-μ * (4 * (k : ℝ) + 6)) := by
  unfold floorTerm
  rw [MassGap.VortexEntropy.directed_surface_count]
  push_cast
  ring

/-- `Real.log (floorTerm μ k) = k * Real.log 3 - μ * (4 * k + 6)`. Both factors of `floorTerm` are
nonzero — a power of `3` and an exponential — so `Real.log_mul` applies, and `Real.log_pow` and
`Real.log_exp` evaluate the two pieces.

DERIVED: `3` is the base of the counted factor, whose logarithm appears; `4` and `6` are the
boundary area `4 * k + 6`, carried over from `floorTerm`. -/
theorem log_floorTerm {μ : ℝ} (k : ℕ) :
    Real.log (floorTerm μ k) = (k : ℝ) * Real.log 3 - μ * (4 * (k : ℝ) + 6) := by
  unfold floorTerm
  rw [Real.log_mul (pow_ne_zero k (by norm_num : (3 : ℝ) ≠ 0)) (Real.exp_ne_zero _),
      Real.log_pow, Real.log_exp]
  ring

/-- `fun k : ℕ => k * Real.log 3 / (4 * k + 6) - μ` tends to `1 / 4 * Real.log 3 - μ` along
`Filter.atTop`. The proof rewrites `k / (4k + 6)` as `1 / (4 + 6/k)` eventually, sends `6/k → 0`, and
multiplies the resulting limit `1/4` by `Real.log 3` before subtracting the constant `μ`.

Scope: the limit is over the natural-number index `k`; `μ` is a constant real subtracted throughout.

DERIVED: `3` is the base of the logarithm, the branching factor of a directed cube path, appearing in
both the sequence and the limit; `4` and `6` are the boundary area `4 * k + 6` in the denominator;
`1` and the second `4` are the limit `1 / 4` of `k / (4 * k + 6)`, the reciprocal area per step. -/
theorem floor_ratio_tendsto {μ : ℝ} :
    Tendsto (fun k : ℕ => (k : ℝ) * Real.log 3 / (4 * (k : ℝ) + 6) - μ) atTop
      (𝓝 (1 / 4 * Real.log 3 - μ)) := by
  have hnd : Tendsto (fun k : ℕ => (k : ℝ) / (4 * (k : ℝ) + 6)) atTop (𝓝 (1 / 4)) := by
    have he : (fun k : ℕ => (k : ℝ) / (4 * (k : ℝ) + 6)) =ᶠ[atTop]
        (fun k : ℕ => 1 / (4 + 6 / (k : ℝ))) := by
      filter_upwards [eventually_gt_atTop 0] with k hk
      have hne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
      field_simp
    rw [tendsto_congr' he]
    have h6 : Tendsto (fun k : ℕ => (6 : ℝ) / (k : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 6
    have hden : Tendsto (fun k : ℕ => (4 : ℝ) + 6 / (k : ℝ)) atTop (𝓝 4) := by
      simpa using (tendsto_const_nhds (x := (4 : ℝ))).add h6
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have := hc.div hden (by norm_num)
    simpa [Pi.div_def, one_div] using this
  have hmain : Tendsto (fun k : ℕ => (k : ℝ) * Real.log 3 / (4 * (k : ℝ) + 6)) atTop
      (𝓝 (1 / 4 * Real.log 3)) := by
    have := hnd.mul_const (Real.log 3)
    have he : (fun k : ℕ => (k : ℝ) / (4 * (k : ℝ) + 6) * Real.log 3)
        = (fun k : ℕ => (k : ℝ) * Real.log 3 / (4 * (k : ℝ) + 6)) := by
      funext k; ring
    rw [he] at this
    simpa using this
  simpa using hmain.sub_const μ

/-- For any family of directed cube paths `s : ∀ k : ℕ, Fin k → Fin 3`,

    Real.log (3 ^ k) / (CubeArea.boundaryFaces (cubeConfig (s k))).card  →  1 / 4 * Real.log 3

along `Filter.atTop`. The numerator is `Real.log_pow`, giving `k * log 3`; the denominator is
`CubeArea.boundary_card_eq`, giving `4 * k + 6`; the limit is `floor_ratio_tendsto` at `μ = 0`.

Scope: the family `s` is arbitrary and unused beyond typing — the ratio is the same whichever path
is taken at each `k`, because every one of them bounds a surface of the same area. The numerator is
the logarithm of the count `3 ^ k` rather than of a cardinality expression.

DERIVED: the first `3` is the branching factor, the cardinality of `Fin 3` at each step; the second
`3` is the base of the counted family `3 ^ k`; `1` and `4` are the limiting reciprocal area per
step, and the final `3` is the base of the logarithm in the limit. -/
theorem kappa0_is_the_surface_entropy_density (s : ∀ k : ℕ, Fin k → Fin 3) :
    Tendsto (fun k : ℕ => Real.log ((3 : ℝ) ^ k)
        / ((MassGap.VortexEntropy.CubeArea.boundaryFaces (MassGap.VortexEntropy.cubeConfig (s k))).card : ℝ))
      atTop (𝓝 (1 / 4 * Real.log 3)) := by
  have he : (fun k : ℕ => Real.log ((3 : ℝ) ^ k)
        / ((MassGap.VortexEntropy.CubeArea.boundaryFaces (MassGap.VortexEntropy.cubeConfig (s k))).card : ℝ))
      = (fun k : ℕ => (k : ℝ) * Real.log 3 / (4 * (k : ℝ) + 6)) := by
    funext k
    rw [Real.log_pow, MassGap.VortexEntropy.CubeArea.boundary_card_eq (s k)]
    push_cast
    ring_nf
  rw [he]
  simpa using floor_ratio_tendsto (μ := 0)

#print axioms kappa0_is_the_surface_entropy_density

/-- Given `floorTerm μ k ≤ Z k` at every `k`, and `Real.log (Z k) / (4 * k + 6) ≤ c` at every `k > 0`,
it follows that `1 / 4 * Real.log 3 - μ ≤ c`.

The proof takes the limit of `floor_ratio_tendsto` against the eventual bound: at `k > 0`,
`log (floorTerm μ k) ≤ log (Z k)` by monotonicity of the logarithm (`floorTerm μ k` is strictly
positive), `log_floorTerm` expands the left side, and dividing by the positive `4 * k + 6` gives
`k log 3 / (4k+6) - μ ≤ log (Z k) / (4k+6) ≤ c`.

Scope: `Z` need not be positive or monotone; only the domination `floorTerm μ k ≤ Z k` is used, and
it forces `Z k > 0`. `hdual` is required only at `k > 0`, which is all the `atTop` filter needs.

DERIVED: `0` is the lower bound on `k` in `hdual`, excluding the degenerate index; `4` and `6` are
the boundary area `4 * k + 6` in the denominator; `1` and the second `4` are the limiting reciprocal
area per step; `3` is the base of the logarithm, the branching factor. -/
theorem junction_of_floor_count {μ c : ℝ} {Z : ℕ → ℝ}
    (hZ : ∀ k, floorTerm μ k ≤ Z k)
    (hdual : ∀ k, 0 < k → Real.log (Z k) / (4 * (k : ℝ) + 6) ≤ c) :
    1 / 4 * Real.log 3 - μ ≤ c := by
  refine le_of_tendsto floor_ratio_tendsto ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hpos : 0 < floorTerm μ k := by unfold floorTerm; positivity
  have hlog : (k : ℝ) * Real.log 3 - μ * (4 * (k : ℝ) + 6) ≤ Real.log (Z k) := by
    calc (k : ℝ) * Real.log 3 - μ * (4 * (k : ℝ) + 6)
        = Real.log (floorTerm μ k) := (log_floorTerm k).symm
      _ ≤ Real.log (Z k) := Real.log_le_log hpos (hZ k)
  have h6 : 0 < (4 * (k : ℝ) + 6) := by positivity
  have hdiv : (k : ℝ) * Real.log 3 / (4 * (k : ℝ) + 6) - μ ≤ Real.log (Z k) / (4 * (k : ℝ) + 6) := by
    have hstep := (div_le_div_iff_of_pos_right h6).mpr hlog
    have hrw : ((k : ℝ) * Real.log 3 - μ * (4 * (k : ℝ) + 6)) / (4 * (k : ℝ) + 6)
        = (k : ℝ) * Real.log 3 / (4 * (k : ℝ) + 6) - μ := by field_simp
    rwa [hrw] at hstep
  exact le_trans hdiv (hdual k hk)

/-! ### Supplying `hZ` from a cardinality bound `3 ^ k ≤ M k` -/

/-- If `3 ^ k ≤ M k` at every `k`, then `floorTerm μ k ≤ M k * Real.exp (-μ * (4 * k + 6))`. The
exponential factor is common to both sides and nonnegative, so the inequality reduces to the cast of
`hM`.

Scope: `M : ℕ → ℕ`, so the bound is on a natural-number count; `μ` may have either sign, since only
nonnegativity of the exponential is used.

DERIVED: `3` is the branching factor of a directed cube path, the count `floorTerm` carries; `4` and
`6` are the boundary area `4 * k + 6` in the shared exponential. -/
theorem floorTerm_le_weighted {μ : ℝ} {M : ℕ → ℕ} (hM : ∀ k, 3 ^ k ≤ M k) (k : ℕ) :
    floorTerm μ k ≤ (M k : ℝ) * Real.exp (-μ * (4 * (k : ℝ) + 6)) := by
  unfold floorTerm
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
  exact_mod_cast hM k

/-- If `ι : (Fin k → Fin 3) → S` is injective and lands in a `Finset S` called `V`, then
`3 ^ k ≤ V.card`. The image of `Finset.univ` under `ι` is a subset of `V` with cardinality
`Fintype.card (Fin k → Fin 3) = 3 ^ k`, by `Finset.card_image_of_injective` and
`MassGap.VortexEntropy.directed_paths_card`.

Scope: `S` is an arbitrary type with decidable equality; nothing ties it to surfaces, faces or a
lattice. Both injectivity and the containment are hypotheses.

DERIVED: the first `3` is the cardinality of `Fin 3`, the branching at each step of the domain
`Fin k → Fin 3`; the second `3` is the resulting count `3 ^ k`. -/
theorem three_pow_le_card_of_embeds {k : ℕ} {S : Type} [DecidableEq S]
    (V : Finset S) (ι : (Fin k → Fin 3) → S) (hι : Function.Injective ι)
    (hsub : ∀ p, ι p ∈ V) : 3 ^ k ≤ V.card := by
  have himg : Finset.univ.image ι ⊆ V := by
    intro s hs
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hs
    exact hsub p
  calc 3 ^ k = (Finset.univ.image ι).card := by
        rw [Finset.card_image_of_injective _ hι, Finset.card_univ, MassGap.VortexEntropy.directed_paths_card]
    _ ≤ V.card := Finset.card_le_card himg

/-- `three_pow_le_card_of_embeds` at the map `CubeArea.boundaryFaces ∘ cubeConfig`: if every directed
cube path's boundary surface belongs to a `Finset (Finset CubeArea.Face)` called `V`, then
`3 ^ k ≤ V.card`. Injectivity of the map is discharged internally by
`CubeArea.boundaryFaces_cubeConfig_injective`, which recovers each cube from the boundary through the
face its step crosses, so the only hypothesis left to the caller is the containment `hsub`.

Scope: `V` is a family of surfaces — sets of faces — not of cube positions.
`CubeArea.Face` is `Fin 3 × (Fin 3 → ℕ)`, a face of a three-dimensional sublattice, so `hsub` is a
statement about three-dimensional surfaces; no embedding into four-dimensional plaquettes appears
here.

DERIVED: the first `3` is the cardinality of `Fin 3`, the branching at each step of the directed
path `s : Fin k → Fin 3`; the second `3` is the resulting count `3 ^ k`. -/
theorem three_pow_le_card_of_directed_surfaces {k : ℕ}
    (V : Finset (Finset MassGap.VortexEntropy.CubeArea.Face))
    (hsub : ∀ s : Fin k → Fin 3,
      MassGap.VortexEntropy.CubeArea.boundaryFaces (MassGap.VortexEntropy.cubeConfig s) ∈ V) :
    3 ^ k ≤ V.card :=
  three_pow_le_card_of_embeds V _ MassGap.VortexEntropy.CubeArea.boundaryFaces_cubeConfig_injective hsub

#print axioms three_pow_le_card_of_directed_surfaces

/-- If every member of `V : Finset (Finset CubeArea.Face)` is the boundary surface of some directed
cube path `s : Fin k → Fin 3`, then every member has cardinality `4 * k + 6`. The proof destructures
the hypothesis and applies `CubeArea.boundary_card_eq`.

This is what makes a single exponent `exp (-μ * (4 * k + 6))` correct for the whole family rather
than a mixture over different areas.

Scope: the hypothesis is that every member of `V` arises from some path — the converse containment of
`three_pow_le_card_of_directed_surfaces`'s `hsub`. The two together say `V` is exactly the family of
directed boundaries.

DERIVED: `3` is the branching factor, the cardinality of `Fin 3` at each step; `4` and `6` are the
boundary area `4 * k + 6`. -/
theorem directed_surfaces_all_have_area {k : ℕ}
    (V : Finset (Finset MassGap.VortexEntropy.CubeArea.Face))
    (hV : ∀ F ∈ V, ∃ s : Fin k → Fin 3, F = MassGap.VortexEntropy.CubeArea.boundaryFaces (MassGap.VortexEntropy.cubeConfig s)) :
    ∀ F ∈ V, F.card = 4 * k + 6 := by
  intro F hF
  obtain ⟨s, rfl⟩ := hV F hF
  exact MassGap.VortexEntropy.CubeArea.boundary_card_eq s

#print axioms directed_surfaces_all_have_area


/-! ### Through one fixed plaquette -/

/-- The cube at the origin is in every configuration: `cubePos s 0` is the zero vector.
DERIVED: `0` the origin, the index of the first cube; `3` the step directions of a cube path, the
dimension of its sublattice. -/
theorem zero_mem_cubeConfig {k : ℕ} (s : Fin k → Fin 3) : (fun _ : Fin 3 => (0 : ℕ)) ∈ cubeConfig s := by
  have h : cubePos s 0 = fun _ => 0 := by funext b; simp [cubePos]
  rw [cubeConfig, Finset.mem_image]
  exact ⟨0, by simp, h⟩

/-- **The low faces of the origin cube are on every boundary.** The only cube with the face `(a, 0)`
is the origin cube: the high face of a cube `y` along `a` has corner coordinate `y a + 1 ≠ 0`.
DERIVED: `0` the origin; `1` the owner count of a boundary face; `3` the step directions of a cube
path, the dimension of its sublattice. -/
theorem origin_face_mem_boundary {k : ℕ} (s : Fin k → Fin 3) (a : Fin 3) :
    ((a, fun _ => 0) : CubeArea.Face) ∈ CubeArea.boundaryFaces (cubeConfig s) := by
  classical
  have h0 := zero_mem_cubeConfig s
  have hf : ((a, fun _ => 0) : CubeArea.Face) ∈ CubeArea.faces (fun _ => 0) :=
    CubeArea.mem_faces.mpr ⟨a, Or.inl rfl⟩
  rw [CubeArea.mem_boundaryFaces_iff]
  refine ⟨Finset.mem_biUnion.mpr ⟨_, h0, hf⟩, ?_⟩
  rw [Finset.card_eq_one]
  refine ⟨fun _ => 0, ?_⟩
  ext y
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hy⟩
    rcases CubeArea.mem_faces.mp hy with ⟨b, hb | hb⟩
    · exact (congrArg Prod.snd hb).symm
    · exfalso
      have h1 : b = a := (congrArg Prod.fst hb).symm
      subst h1
      have h2 := congrArg (fun f : CubeArea.Face => f.2 b) hb
      simp only [CubeArea.step_self] at h2
      omega
  · rintro rfl
    exact ⟨h0, hf⟩

open MassGap.WilsonHypercubic in
/-- **The base plaquette**: the low face of the origin cube along the first axis, placed in `Site 4 n`.
DERIVED: `0` the first axis and the origin; `4` the lattice dimension. -/
def basePlaq (n : ℕ) [NeZero n] : Plaq 4 n := SurfaceEmbed.faceToPlaq n (0, fun _ => 0)

/-- Every directed surface contains the base plaquette. -/
theorem basePlaq_mem_plaqSurface (n : ℕ) [NeZero n] {k : ℕ} (s : Fin k → Fin 3) :
    basePlaq n ∈ SurfaceEmbed.plaqSurface n s :=
  Finset.mem_image_of_mem _ (origin_face_mem_boundary s 0)

open MassGap.WilsonHypercubic in
/-- **`3^k` cube-boundary surfaces of area `4k + 6` through one plaquette of the four-dimensional lattice.**
For `k + 1 < n` there is a family of `3 ^ k` distinct plaquette sets of `Site 4 n`, each with exactly
`4k + 6` plaquettes and each containing `basePlaq n`.
DERIVED: `3` the step directions; `4k + 6` the boundary count; `1` the reach of a face beyond its cube;
`4` the lattice dimension. -/
theorem closed_surfaces_through_plaquette {n k : ℕ} [NeZero n] (hk : k + 1 < n) :
    ∃ S : Finset (Finset (Plaq 4 n)),
      S.card = 3 ^ k ∧ ∀ F ∈ S, F.card = 4 * k + 6 ∧ basePlaq n ∈ F := by
  classical
  refine ⟨Finset.univ.image (fun s : Fin k → Fin 3 => SurfaceEmbed.plaqSurface n s), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (SurfaceEmbed.plaqSurface_injective hk), Finset.card_univ,
      directed_paths_card]
  · intro F hF
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hF
    exact ⟨SurfaceEmbed.card_plaqSurface hk s, basePlaq_mem_plaqSurface n s⟩

/-! ### The convergence threshold of the surface sum -/

/-- `floorTerm` is geometric: `3^k e^{−μ(4k+6)} = e^{−6μ} (3 e^{−4μ})^k`.
DERIVED: `3`, `4`, `6` as in `floorTerm`. -/
theorem floorTerm_eq_geom (μ : ℝ) (k : ℕ) :
    floorTerm μ k = Real.exp (-μ * 6) * (3 * Real.exp (-μ * 4)) ^ k := by
  unfold floorTerm
  have he : Real.exp (-μ * (4 * (k : ℝ) + 6)) = Real.exp (-μ * 6) * Real.exp (-μ * 4) ^ k := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    ring_nf
  rw [he, mul_pow]
  ring

/-- **The surface sum converges exactly above the entropy density**: `Σ_k 3^k e^{−μ(4k+6)}` is
summable iff `¼ ln 3 < μ`.
DERIVED: `3` the step directions; `4` the area added per step; `¼` its reciprocal; `6` the area at
`k = 0`, a common factor. -/
theorem floorTerm_summable_iff {μ : ℝ} : Summable (floorTerm μ) ↔ 1 / 4 * Real.log 3 < μ := by
  have he : floorTerm μ = fun k : ℕ => Real.exp (-μ * 6) * (3 * Real.exp (-μ * 4)) ^ k :=
    funext (floorTerm_eq_geom μ)
  rw [he, summable_mul_left_iff (Real.exp_pos _).ne', summable_geometric_iff_norm_lt_one,
    Real.norm_of_nonneg (by positivity)]
  have h3 : (3 : ℝ) * Real.exp (-μ * 4) = Real.exp (Real.log 3 - 4 * μ) := by
    rw [Real.exp_sub, Real.exp_log (by norm_num), div_eq_mul_inv, ← Real.exp_neg]
    ring_nf
  rw [h3, Real.exp_lt_one_iff]
  constructor <;> intro h <;> linarith

/-- **At or below the entropy density the surface sum through one plaquette diverges.**
DERIVED: as in `floorTerm_summable_iff`: `3` the step directions, `¼` the reciprocal of the area `4`
added per step. -/
theorem not_summable_of_le {μ : ℝ} (h : μ ≤ 1 / 4 * Real.log 3) : ¬ Summable (floorTerm μ) := by
  rw [floorTerm_summable_iff]
  exact not_lt.mpr h

#print axioms zero_mem_cubeConfig
#print axioms origin_face_mem_boundary
#print axioms basePlaq_mem_plaqSurface
#print axioms closed_surfaces_through_plaquette
#print axioms floorTerm_eq_geom
#print axioms floorTerm_summable_iff
#print axioms not_summable_of_le
#print axioms floorTerm_exponent_is_the_area
#print axioms floor_count_injection
#print axioms log_floorTerm
#print axioms floor_ratio_tendsto
#print axioms junction_of_floor_count
#print axioms floorTerm_le_weighted
#print axioms three_pow_le_card_of_embeds

end MassGap.VortexEntropy
