import MassGap.Floor

/-!
# MassGap.CubeArea — the boundary face-count of a directed cube-path

A `Cube` is a point of `Fin 3 → ℕ`, its low corner; a `Face` is a pair `(axis, corner)`; `faces x` is
the six-element `Finset` of a cube's faces, and `boundaryFaces C` the faces of `C` with exactly one
owner.

`boundary_card_eq` is the main statement: for `s : Fin k → Fin 3`, the configuration
`Floor.cubeConfig s` has `(boundaryFaces (cubeConfig s)).card = 4 * k + 6`. The double count behind
it is

    |∂C| = 6(k+1) − 2·(#shared faces) = 6(k+1) − 2k = 4k + 6.

The inputs:

* `card_faces` — a cube has six faces, two per axis over three axes.
* `card_cubeConfig` — the path visits `k + 1` distinct cubes, from `cubePos_injOn`, which is
  `Floor.cubePos_sum_le` reading the coordinate sum as the index.
* `card_cubes_with_face_le_two` — a face has at most two owners, from `cube_of_face` and
  `step_injective`.
* `card_sharedFaces` — the shared faces are exactly the `k` crossed ones, via
  `sharedFaces_eq_crossFaces`. The forward inclusion runs through `step_rel_of_shares`,
  `sum_dist_one_of_shares` (the coordinate sum forces sharing to be between consecutive cubes) and
  `shared_face_eq`; the backward one through `crossFace_shared` and `cubePos_injOn`.
* `incidence_double_count` and `boundary_card_of_shared` — the `Finset` bookkeeping, with the shared
  count left as a parameter so the arithmetic is separate from the geometry.

`boundaryFaces_cubeConfig_injective` then shows distinct step sequences give distinct boundaries, by
recovering the configuration from its boundary one coordinate-sum level at a time
(`mem_of_boundary_eq_aux`, using `not_mem_boundaryFaces_of_both` and
`mem_of_not_mem_boundaryFaces`). `directed_surfaces_count_and_area` combines it with
`Floor.directed_paths_card`: there is a `Finset` of `3 ^ k` face-sets, each of cardinality
`4 * k + 6`.

Scope: everything is `Finset` combinatorics over `Fin 3 → ℕ`. No statement mentions a lattice gauge
theory, an entropy, a coupling or a gap.

DERIVED THROUGHOUT: `3` is the dimension the cube-path lives in, which is `Fin 3`, the step alphabet
`Floor.directed_paths_card` counts over. `6` is the number of faces of a cube, `2` per axis over `3`
axes. `2` is how many cubes a shared face belongs to. `1` is the unit lattice step. None is a
magnitude; each is the arity of something the definitions already name.
-/

namespace MassGap.CubeArea

open Finset

/-- A unit cube, named by its low corner.

DERIVED: `3` is the dimension the directed cube-path of `Floor.lean` lives in — `Fin 3` is the
step alphabet `Floor.directed_paths_card` counts over, so the ambient dimension is that alphabet's
arity and not a separate choice. -/
abbrev Cube : Type := Fin 3 → ℕ

/-- A face, named by the axis it is perpendicular to and its low corner. This is the same
`(normal, site)` naming `WilsonBridge.Plaq3` uses for a plaquette.

DERIVED: both `3`s are `Cube`'s dimension — the axis ranges over it and the corner is a point of
it. Nothing new is introduced here. -/
abbrev Face : Type := Fin 3 × (Fin 3 → ℕ)

/-- One unit step along axis `a`.

DERIVED: `1` is the UNIT of the lattice — a cube-path advances one cube per step, which is what
`Floor.cubePos_succ` already states coordinatewise; `3` is `Cube`'s dimension. -/
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
  · -- Faces on different axes are distinct in their FIRST component alone, so the two-element
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
  -- the axis is read off the face's first component, so the two descriptions use the SAME axis
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

Along a directed path `Floor.cubePos_sum_le` makes the coordinate sum the index, so only consecutive
cubes can share a face. That is what `sharedFaces_eq_crossFaces` consumes.

DERIVED: `1` is the unit lattice step, carried from `sum_step`; `3` is the dimension. -/
theorem sum_dist_one_of_shares {x y : Cube} {f : Face}
    (hx : f ∈ faces x) (hy : f ∈ faces y) (hne : x ≠ y) :
    (∑ b, x b) + 1 = (∑ b, y b) ∨ (∑ b, y b) + 1 = (∑ b, x b) := by
  rcases step_rel_of_shares hx hy with h | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact absurd h hne
  · exact Or.inl (sum_step a x).symm
  · exact Or.inr (sum_step a y).symm

/-- `cubePos s (j + 1) = step (s j) (cubePos s j)`: `Floor.cubePos_succ` as an equation between cubes
rather than coordinate by coordinate. By `funext` and a case split on whether the coordinate is
`s j`.

DERIVED: `1` is the index increment, one step of the path; `3` is the dimension, the range of the
step alphabet. -/
theorem cubePos_succ_eq_step {k : ℕ} (s : Fin k → Fin 3) (j : Fin k) :
    MassGap.cubePos s ((j : ℕ) + 1) = step (s j) (MassGap.cubePos s (j : ℕ)) := by
  funext a
  rw [MassGap.cubePos_succ s j a]
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
    ((s j : Fin 3), MassGap.cubePos s ((j : ℕ) + 1))
      ∈ faces (MassGap.cubePos s (j : ℕ)) ∩ faces (MassGap.cubePos s ((j : ℕ) + 1)) := by
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
and `Floor.cubePos_sum_le` makes that sum the index.

So the path never revisits a cube, which is what makes `6(k+1)` a count rather than an over-count.

DERIVED: `1` in `range (k + 1)` makes the range run through `k` inclusive, the `k + 1` positions of a
`k`-step path. `3` is the dimension. -/
theorem cubePos_injOn {k : ℕ} (s : Fin k → Fin 3) :
    Set.InjOn (MassGap.cubePos s) (Finset.range (k + 1)) := by
  intro i hi j hj hij
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hi' := MassGap.cubePos_sum_le s hik
  have hj' := MassGap.cubePos_sum_le s hjk
  rw [hij] at hi'
  omega

/-- `(Floor.cubeConfig s).card = k + 1`: the image of a map injective on `range (k + 1)`, by
`Finset.card_image_of_injOn` at `cubePos_injOn`.

DERIVED: `1` is the `+1` of `range (k + 1)`, so the count is the number of cubes of a `k`-step path;
`3` is the dimension. -/
theorem card_cubeConfig {k : ℕ} (s : Fin k → Fin 3) :
    (MassGap.cubeConfig s).card = k + 1 := by
  classical
  rw [MassGap.cubeConfig, Finset.card_image_of_injOn (cubePos_injOn s), Finset.card_range]

#print axioms cubePos_injOn
#print axioms card_cubeConfig

/-- The face the `j`-th step crosses: `(s j, cubePos s (j + 1))`, the one shared by cube `j` and cube
`j + 1`. `crossFace_shared` proves it is shared and `crossFace_injective` that these `k` faces are
distinct.

DERIVED: `1` is the index increment — `Floor.cubePos_succ` advances the index by one per step, so
`j + 1` names the cube the `j`-th step lands on and nothing is chosen. `3` is `Cube`'s dimension, the
arity of the step alphabet `Fin 3`. -/
def crossFace {k : ℕ} (s : Fin k → Fin 3) (j : Fin k) : Face :=
  ((s j : Fin 3), MassGap.cubePos s ((j : ℕ) + 1))

/-- `crossFace s` is injective on `Fin k`. Distinctness comes from the second component alone: the
crossed face is named by the cube the step lands on, and `cubePos_injOn` says the path never lands on
the same cube twice. The axis is never compared.

DERIVED: `3` is the dimension; the index increment inside `crossFace` is that definition's. -/
theorem crossFace_injective {k : ℕ} (s : Fin k → Fin 3) : Function.Injective (crossFace s) := by
  intro i j hij
  have h2 : MassGap.cubePos s ((i : ℕ) + 1) = MassGap.cubePos s ((j : ℕ) + 1) :=
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
    crossFace s j ∈ faces (MassGap.cubePos s (j : ℕ))
      ∩ faces (MassGap.cubePos s ((j : ℕ) + 1)) :=
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
  · -- step f.1 x = f.2 and step a x = f.2 : THE case. The axis and the corner both follow.
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
    ∑ x ∈ MassGap.cubeConfig s, (faces x).card = 6 * (k + 1) := by
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
    (hx : x ∈ MassGap.cubeConfig s) (hy : step a x ∈ MassGap.cubeConfig s)
    (hxf : f ∈ faces x) (hyf : f ∈ faces (step a x)) :
    f ∈ Finset.univ.image (crossFace s) := by
  classical
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, hjy⟩ := Finset.mem_image.mp hy
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  -- the coordinate sum is the index, and a step raises it by one, so `j = i + 1`
  have hsi : ∑ b, x b = i := by rw [← hix]; exact MassGap.cubePos_sum_le s hik
  have hsj : ∑ b, step a x b = j := by rw [← hjy]; exact MassGap.cubePos_sum_le s hjk
  have hji : j = i + 1 := by rw [← hsj, sum_step a x, hsi]
  have hik' : i < k := by omega
  refine Finset.mem_image.mpr ⟨⟨i, hik'⟩, Finset.mem_univ _, ?_⟩
  -- the axis of the step is the path's own step at `i`
  have hsucc : MassGap.cubePos s (i + 1) = step (s ⟨i, hik'⟩) (MassGap.cubePos s i) :=
    cubePos_succ_eq_step s ⟨i, hik'⟩
  have hstep : step a x = step (s ⟨i, hik'⟩) x := by
    rw [← hjy, hji, hsucc, hix]
  have haxis : a = s ⟨i, hik'⟩ := step_axis_inj hstep
  show ((s ⟨i, hik'⟩ : Fin 3), MassGap.cubePos s (i + 1)) = f
  rw [shared_face_eq hxf hyf, ← hjy, hji, haxis]

/-- The two-owner faces of `cubeConfig s` are exactly the image of `crossFace s`.

Forward: two owners are a step apart (`step_rel_of_shares`), the pair is consecutive through the
coordinate sum (`sum_dist_one_of_shares`), and `crossFace_of_step` names the face. Backward: each
crossed face has two distinct owners on the path (`crossFace_shared`, `cubePos_injOn`), and
`card_cubes_with_face_le_two` caps the count at two.

DERIVED: `2` is the owner count that marks a face as shared, `card_cubes_with_face_le_two`'s bound;
`3` is the dimension. -/
theorem sharedFaces_eq_crossFaces {k : ℕ} (s : Fin k → Fin 3) :
    ((MassGap.cubeConfig s).biUnion faces).filter
        (fun f => ((MassGap.cubeConfig s).filter (fun x => f ∈ faces x)).card = 2)
      = Finset.univ.image (crossFace s) := by
  classical
  ext f
  constructor
  · intro hf
    obtain ⟨hfB, hf2⟩ := Finset.mem_filter.mp hf
    have h1 : 1 < ((MassGap.cubeConfig s).filter (fun x => f ∈ faces x)).card := by omega
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h1
    obtain ⟨hxC, hxf⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyC, hyf⟩ := Finset.mem_filter.mp hy
    rcases step_rel_of_shares hxf hyf with h | ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact absurd h hxy
    · exact crossFace_of_step s hxC hyC hxf hyf
    · exact crossFace_of_step s hyC hxC hyf hxf
  · intro hf
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hf
    have hjm : MassGap.cubePos s (j : ℕ) ∈ MassGap.cubeConfig s :=
      Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by have := j.isLt; omega))
    have hj1m : MassGap.cubePos s ((j : ℕ) + 1) ∈ MassGap.cubeConfig s :=
      Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by have := j.isLt; omega))
    obtain ⟨hin0, hin1⟩ := Finset.mem_inter.mp (crossFace_shared s j)
    -- the two owners are distinct: the path never revisits a cube
    have hne : MassGap.cubePos s (j : ℕ) ≠ MassGap.cubePos s ((j : ℕ) + 1) := by
      intro h
      have hi : (j : ℕ) ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by have := j.isLt; omega)
      have hi1 : (j : ℕ) + 1 ∈ Finset.range (k + 1) :=
        Finset.mem_range.mpr (by have := j.isLt; omega)
      have := cubePos_injOn s hi hi1 h
      omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨_, hjm, hin0⟩, ?_⟩
    have hle := card_cubes_with_face_le_two (MassGap.cubeConfig s) (crossFace s j)
    have hge : 1 < ((MassGap.cubeConfig s).filter
        (fun x => crossFace s j ∈ faces x)).card :=
      Finset.one_lt_card.mpr ⟨_, Finset.mem_filter.mpr ⟨hjm, hin0⟩, _,
        Finset.mem_filter.mpr ⟨hj1m, hin1⟩, hne⟩
    omega

/-- The two-owner faces of `cubeConfig s` number exactly `k`: `sharedFaces_eq_crossFaces` followed by
`card_crossFaces`.

DERIVED: `2` is the owner count marking a face as shared; `3` is the dimension. The count `k` is the
number of steps, not a literal. -/
theorem card_sharedFaces {k : ℕ} (s : Fin k → Fin 3) :
    (((MassGap.cubeConfig s).biUnion faces).filter
      (fun f => ((MassGap.cubeConfig s).filter (fun x => f ∈ faces x)).card = 2)).card = k := by
  rw [sharedFaces_eq_crossFaces s, card_crossFaces s]

/-- **The boundary of a cube configuration**: the faces with exactly one owner. A face with two
owners is interior — the two cubes cancel across it — and `owners_one_or_two` says there is no third
case, so this really is the surface of the union.

DERIVED: `1` is the ARITY of the owner count, not a magnitude: `owners_one_or_two` proves every face
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
    (boundaryFaces (MassGap.cubeConfig s)).card = 4 * k + 6 := by
  classical
  rw [boundaryFaces]
  set C := MassGap.cubeConfig s with hC
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

`Floor.directed_surface_count` counts cube configurations. `boundaryFaces_cubeConfig_injective`
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
    (h : boundaryFaces (MassGap.cubeConfig s) = boundaryFaces (MassGap.cubeConfig t)) :
    ∀ n : ℕ, ∀ x : Cube, (∑ b, x b) = n → x ∈ MassGap.cubeConfig s → x ∈ MassGap.cubeConfig t := by
  classical
  intro n
  induction n with
  | zero =>
    intro x hsum _
    -- coordinate sum zero is the origin, and every path starts there
    have hx0 : x = MassGap.cubePos t 0 := by
      funext a
      have hxa : x a = 0 := (Finset.sum_eq_zero_iff.mp hsum) a (Finset.mem_univ a)
      rw [hxa, MassGap.cubePos]
      simp
    rw [hx0]
    exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (Nat.succ_pos k))
  | succ i ih =>
    intro x hsum hxs
    obtain ⟨m, hm, hmx⟩ := Finset.mem_image.mp hxs
    have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hmi : m = i + 1 := by
      rw [← MassGap.cubePos_sum_le s hmk, hmx, hsum]
    subst hmi
    have hik : i < k := by omega
    have hxstep : x = step (s ⟨i, hik⟩) (MassGap.cubePos s i) := by
      rw [← hmx]; exact cubePos_succ_eq_step s ⟨i, hik⟩
    have hps : MassGap.cubePos s i ∈ MassGap.cubeConfig s :=
      Finset.mem_image_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_of_lt hik))
    have hpsum : (∑ b, MassGap.cubePos s i b) = i := MassGap.cubePos_sum_le s (le_of_lt hik)
    have hpt : MassGap.cubePos s i ∈ MassGap.cubeConfig t := ih _ hpsum hps
    have hxs' : step (s ⟨i, hik⟩) (MassGap.cubePos s i) ∈ MassGap.cubeConfig s := hxstep ▸ hxs
    have hnotL := not_mem_boundaryFaces_of_both hps hxs'
    rw [h] at hnotL
    rw [hxstep]
    exact mem_of_not_mem_boundaryFaces hpt hnotL

/-- `fun s => boundaryFaces (cubeConfig s)` is injective on `Fin k → Fin 3`.
`mem_of_boundary_eq_aux` in both directions makes the two configurations equal, and
`Floor.cubeConfig_injective` descends to the step sequences.

Stronger than distinctness of configurations: the boundary map does not collapse two of them.

DERIVED: `3` is the dimension, the range of the step alphabet; no other numeral. -/
theorem boundaryFaces_cubeConfig_injective {k : ℕ} :
    Function.Injective (fun s : Fin k → Fin 3 => boundaryFaces (MassGap.cubeConfig s)) := by
  intro s t h
  refine MassGap.cubeConfig_injective ?_
  ext x
  exact ⟨fun hx => mem_of_boundary_eq_aux s t h _ x rfl hx,
    fun hx => mem_of_boundary_eq_aux t s h.symm _ x rfl hx⟩

/-- There is a `Finset (Finset Face)` of cardinality `3 ^ k` every member of which has cardinality
`4 * k + 6`. The witness is the image of `fun s => boundaryFaces (cubeConfig s)`; its cardinality is
`Floor.directed_paths_card` transported along `boundaryFaces_cubeConfig_injective`, and the member
cardinality is `boundary_card_eq`.

A statement about `Finset`s of faces. It says nothing about an entropy density or a limit; the
quotient `(k log 3)/(4k + 6)` is `Floor.floor_density_limit`'s, reindexed.

DERIVED: `3` is the dimension and the base of the count — the same number, since the step alphabet is
`Fin 3`. `4` and `6` are `boundary_card_eq`'s, the six faces of a cube less twice the one shared per
step. -/
theorem directed_surfaces_count_and_area {k : ℕ} :
    ∃ S : Finset (Finset Face), S.card = 3 ^ k ∧ ∀ F ∈ S, F.card = 4 * k + 6 := by
  classical
  refine ⟨Finset.univ.image (fun s : Fin k → Fin 3 => boundaryFaces (MassGap.cubeConfig s)),
    ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ boundaryFaces_cubeConfig_injective, Finset.card_univ,
      MassGap.directed_paths_card]
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

end MassGap.CubeArea
