import MassGap.CubeArea

/-!
# `Z₂`-closedness of the boundary of a cube configuration

The file's endpoint is `edge_parity_all`: for any `C : Finset Cube`, any axis `c : Fin 3` and any
cube `w`, the number of faces of `boundaryFaces C` whose edge set contains `(c, w)` is even. That is
the `Z₂` condition `∂∂ = 0` — a parity statement about edges, not a topological one — and it holds
with no hypothesis on where `C` sits in `ℕ³`.

The proof is a double count over incident (cube, face) pairs, set up by
`incidence_double_count_filter`. Counting by cube, every term is even: `cube_edge_even` says an edge
lies in exactly two of a cube's six faces, or in none. Counting by face, each face contributes its
owner count, which `CubeArea.owners_one_or_two` puts at one or two, so modulo two the face sum counts
exactly the one-owner faces — which is `boundaryFaces C` by definition. Summing over cubes rather
than around the edge is what removes any need for absent neighbours to exist: a cube not in `C`
simply does not appear in the sum.

The supporting geometry: `rot1` and `rot2` name the two axes a face spans, as `+1` and `+2` modulo
three, and are mutually inverse (`rot1_rot2`, `rot2_rot1`), distinct from their argument (`rot1_ne`,
`rot2_ne`) and from each other (`rot1_ne_rot2`); `univ_eq_rot` says `c`, `rot1 c`, `rot2 c` exhaust
the axes. `faceEdges f` lists a face's four edges, `mem_faceEdges_rot1` and `mem_faceEdges_rot2`
identify which of them run along `c`, and `not_mem_faceEdges_axis` rules out faces whose normal is
neither rotation. `corners_distinct` separates the four corners an edge along `c` can sit at.

The file also carries three membership results for `boundaryFaces` itself:
`mem_boundaryFaces_iff_floor` (a face whose own coordinate is zero is on the boundary exactly when
its single possible owner is in `C`), `mem_boundaryFaces_iff_xor` (a face between two cubes is on
the boundary exactly when exactly one of them is in `C`), and `origin_face_mem_boundary` (all three
low faces of the origin cube lie on the boundary of every directed path's configuration).

Scope: `Cube` is indexed by `Fin 3`, so everything here is three-dimensional. `step` raises a
coordinate, which is why the floor `ℕ³` has no cube behind a zero coordinate.
-/

namespace MassGap.CubeArea

open Finset

/-- `step a (step b x) = step b (step a x)` for axes `a b : Fin 3` and a cube `x`. If `a = b` the two
sides are the same term; otherwise the two updates touch different coordinates and the result is
checked coordinatewise.

DERIVED: `3` appears twice, as the axis type of `a` and of `b` — the dimension `Cube` is indexed
by. -/
theorem step_comm (a b : Fin 3) (x : Cube) : step a (step b x) = step b (step a x) := by
  by_cases hab : a = b
  · subst hab; rfl
  · funext c
    by_cases hca : c = a
    · rw [hca, step_self]
      simp only [step_other hab]
      rw [step_self]
    · by_cases hcb : c = b
      · rw [hcb]
        simp only [step_other (Ne.symm hab), step_self]
      · simp only [step_other hca, step_other hcb]

#print axioms step_comm

/-! ### Boundary membership: the floor case, the two-cube case, and the origin -/


/-- For a cube `y` whose coordinate along the axis `a` is zero, `(a, y) ∈ boundaryFaces C` if and
only if `y ∈ C`. Such a face has only one possible owner: the other candidate would be a cube one
step back along `a`, and `step` raises that coordinate, so nothing maps to `y` there. The proof
shows the owner filter is `{y}` when `y ∈ C`, giving cardinality one, and conversely extracts `y`
from the `biUnion`.

Scope: the hypothesis `y a = 0` is what makes the owner unique — at a positive coordinate the face
has two candidate owners and `mem_boundaryFaces_iff_xor` applies instead.

DERIVED: `3` is the axis type `Fin 3`, the dimension; `0` is the coordinate value along `a` that
puts the face on the floor. -/
theorem mem_boundaryFaces_iff_floor (C : Finset Cube) (a : Fin 3) (y : Cube) (hy : y a = 0) :
    ((a, y) : Face) ∈ boundaryFaces C ↔ y ∈ C := by
  classical
  have hfy : ((a, y) : Face) ∈ faces y := mem_faces.mpr ⟨a, Or.inl rfl⟩
  have honly : ∀ z ∈ C.filter (fun z => ((a, y) : Face) ∈ faces z), z = y := by
    intro z hz
    rcases cube_of_face (Finset.mem_filter.mp hz).2 with h | h
    · exact h
    · exfalso
      have hstep := congrArg (fun v : Cube => v a) h
      simp only [step_self] at hstep
      omega
  constructor
  · intro hmem
    obtain ⟨hfB, hcard⟩ := (mem_boundaryFaces_iff C _).mp hmem
    obtain ⟨z, hzC, hzf⟩ := Finset.mem_biUnion.mp hfB
    have : z = y := honly z (Finset.mem_filter.mpr ⟨hzC, hzf⟩)
    exact this ▸ hzC
  · intro hyC
    refine (mem_boundaryFaces_iff C _).mpr ⟨Finset.mem_biUnion.mpr ⟨y, hyC, hfy⟩, ?_⟩
    have : C.filter (fun z => ((a, y) : Face) ∈ faces z) = {y} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hyC, hfy⟩, honly⟩
    rw [this]
    exact Finset.card_singleton _

#print axioms mem_boundaryFaces_iff_floor

/-- `(a, step a p) ∈ boundaryFaces C` if and only if `p ∈ C ↔ ¬ (step a p ∈ C)` — that is, exactly
one of the two cubes is in `C`. `CubeArea.owners_subset_pair` limits the owners to `{p, step a p}`
and `CubeArea.ne_step` says they are distinct, so the owner count is one precisely in the exclusive
case; the proof enumerates the four combinations.

Scope: this covers a face written as the low face of `step a p`, so the cube behind it exists.
`mem_boundaryFaces_iff_floor` covers the faces on the floor, where it does not.

DERIVED: `3` is the axis type `Fin 3`, the dimension. -/
theorem mem_boundaryFaces_iff_xor (C : Finset Cube) (a : Fin 3) (p : Cube) :
    ((a, step a p) : Face) ∈ boundaryFaces C ↔ ((p ∈ C) ↔ ¬ (step a p ∈ C)) := by
  classical
  have hfp : ((a, step a p) : Face) ∈ faces p := mem_faces.mpr ⟨a, Or.inr rfl⟩
  have hfq : ((a, step a p) : Face) ∈ faces (step a p) := mem_faces.mpr ⟨a, Or.inl rfl⟩
  constructor
  · intro hmem
    obtain ⟨hfB, hcard⟩ := (mem_boundaryFaces_iff C _).mp hmem
    by_cases hp : p ∈ C
    · by_cases hq : step a p ∈ C
      · exfalso
        have hge : 1 < (C.filter (fun y => ((a, step a p) : Face) ∈ faces y)).card :=
          Finset.one_lt_card.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hfp⟩, step a p,
            Finset.mem_filter.mpr ⟨hq, hfq⟩, ne_step a p⟩
        omega
      · exact ⟨fun _ => hq, fun _ => hp⟩
    · by_cases hq : step a p ∈ C
      · exact ⟨fun h => absurd h hp, fun h => absurd hq h⟩
      · exfalso
        obtain ⟨x, hxC, hxf⟩ := Finset.mem_biUnion.mp hfB
        have := owners_subset_pair C a p (Finset.mem_filter.mpr ⟨hxC, hxf⟩)
        rcases Finset.mem_insert.mp this with h | h
        · exact hq (h ▸ hxC)
        · exact hp ((Finset.mem_singleton.mp h) ▸ hxC)
  · intro hxor
    have hone : (C.filter (fun y => ((a, step a p) : Face) ∈ faces y)) = {p} ∨
        (C.filter (fun y => ((a, step a p) : Face) ∈ faces y)) = {step a p} := by
      by_cases hp : p ∈ C
      · have hq : ¬ (step a p ∈ C) := hxor.mp hp
        left
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨Finset.mem_filter.mpr ⟨hp, hfp⟩, ?_⟩
        intro y hy
        rcases Finset.mem_insert.mp (owners_subset_pair C a p hy) with h | h
        · exact absurd (h ▸ (Finset.mem_filter.mp hy).1) hq
        · exact Finset.mem_singleton.mp h
      · have hq : step a p ∈ C := by
          by_contra hq
          exact hp (hxor.mpr hq)
        right
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨Finset.mem_filter.mpr ⟨hq, hfq⟩, ?_⟩
        intro y hy
        rcases Finset.mem_insert.mp (owners_subset_pair C a p hy) with h | h
        · exact h
        · exact absurd ((Finset.mem_singleton.mp h) ▸ (Finset.mem_filter.mp hy).1) hp
    refine (mem_boundaryFaces_iff C _).mpr ⟨?_, ?_⟩
    · rcases hone with h | h
      · exact Finset.mem_biUnion.mpr ⟨p, by
          have : p ∈ C.filter (fun y => ((a, step a p) : Face) ∈ faces y) := by
            rw [h]; exact Finset.mem_singleton_self p
          exact (Finset.mem_filter.mp this).1, hfp⟩
      · exact Finset.mem_biUnion.mpr ⟨step a p, by
          have : step a p ∈ C.filter (fun y => ((a, step a p) : Face) ∈ faces y) := by
            rw [h]; exact Finset.mem_singleton_self _
          exact (Finset.mem_filter.mp this).1, hfq⟩
    · rcases hone with h | h <;> rw [h] <;> exact Finset.card_singleton _

#print axioms mem_boundaryFaces_iff_xor

/-- For every directed cube path `s : Fin k → Fin 3` and every axis `a : Fin 3`, the face
`(a, cubePos s 0)` lies in `boundaryFaces (cubeConfig s)`. `cubePos s 0` is the origin cube, all of
whose coordinates are zero, so `mem_boundaryFaces_iff_floor` applies at each axis; membership of the
origin in `cubeConfig s` follows from `Nat.succ_pos`.

Since `a` ranges over all three axes, the same three faces lie on the boundary whatever the path
does after its start.

DERIVED: the first `3` is the branching factor of the path `s : Fin k → Fin 3`; the second is the
axis type of `a`, the same dimension; `0` is the index of the path's starting cube in `cubePos`. -/
theorem origin_face_mem_boundary {k : ℕ} (s : Fin k → Fin 3) (a : Fin 3) :
    ((a, MassGap.cubePos s 0) : Face) ∈ boundaryFaces (MassGap.cubeConfig s) := by
  classical
  have hzero : MassGap.cubePos s 0 a = 0 := by
    rw [MassGap.cubePos]; simp
  exact (mem_boundaryFaces_iff_floor _ a _ hzero).mpr
    (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (Nat.succ_pos k)))

#print axioms origin_face_mem_boundary

/-! ### Closedness at every edge, by summing over cubes

`boundaryFaces C` is the `Z₂` sum of the cubes' own boundaries: a face of the configuration has one
or two owners (`CubeArea.owners_one_or_two`), and modulo two the two-owner faces cancel, leaving
exactly the boundary. A single cube's boundary is closed because each of its twelve edges lies in
exactly two of its six faces (`cube_edge_even`). Every cube appearing in the sum is a whole cube, so
no absent neighbour has to be assumed, wherever the configuration sits. -/

/-- The next axis round: `rot1 c = (c + 1) % 3`, as an element of `Fin 3`. Together with `rot2` it
names the two axes a face with normal `c` spans; `rot2_rot1` and `rot1_rot2` make the two mutually
inverse, so neither order is preferred.

DERIVED: `3` occurs three times — as the argument type, as the result type, and as the modulus of the
rotation; all three are `Cube`'s dimension. `1` is the offset, the smaller of the two offsets that
are neither `0` nor a multiple of the dimension. -/
def rot1 (c : Fin 3) : Fin 3 := ⟨((c : ℕ) + 1) % 3, by omega⟩

/-- The axis two steps round: `rot2 c = (c + 2) % 3`, as an element of `Fin 3`. It is inverse to
`rot1` by `rot2_rot1` and `rot1_rot2`.

DERIVED: `3` occurs three times — argument type, result type and modulus — all `Cube`'s dimension.
`2` is the offset, the larger of the two offsets that are neither `0` nor a multiple of the
dimension. -/
def rot2 (c : Fin 3) : Fin 3 := ⟨((c : ℕ) + 2) % 3, by omega⟩

theorem rot2_rot1 (c : Fin 3) : rot2 (rot1 c) = c := by
  apply Fin.ext; have := c.isLt; simp [rot1, rot2]; omega

theorem rot1_rot2 (c : Fin 3) : rot1 (rot2 c) = c := by
  apply Fin.ext; have := c.isLt; simp [rot1, rot2]; omega

theorem rot1_ne (c : Fin 3) : rot1 c ≠ c := by
  intro h; have := c.isLt; have := congrArg Fin.val h; simp [rot1] at this; omega

theorem rot2_ne (c : Fin 3) : rot2 c ≠ c := by
  intro h; have := c.isLt; have := congrArg Fin.val h; simp [rot2] at this; omega

theorem rot1_ne_rot2 (c : Fin 3) : rot1 c ≠ rot2 c := by
  intro h; have := c.isLt; have := congrArg Fin.val h; simp [rot1, rot2] at this; omega

/-- The four edges of a face `f`, as a `Finset (Fin 3 × Cube)`: the two along `rot1 f.1` (at `f.2`
and a step along `rot2 f.1`) and the two along `rot2 f.1` (at `f.2` and a step along `rot1 f.1`). An
edge is recorded as its axis together with the cube corner it starts from.

Scope: the face's own normal `f.1` never appears as an edge axis — a face spans the two axes its
normal is not, which `not_mem_faceEdges_axis` records.

DERIVED: `3` is `Cube`'s dimension, the axis component of an edge. The four listed entries are two
axes times the two positions along the other axis; the count is an arity of the construction, not a
literal in the statement. -/
def faceEdges (f : Face) : Finset (Fin 3 × Cube) :=
  {(rot1 f.1, f.2), (rot2 f.1, step (rot1 f.1) f.2),
   (rot1 f.1, step (rot2 f.1) f.2), (rot2 f.1, f.2)}

theorem mem_faceEdges {f : Face} {e : Fin 3 × Cube} :
    e ∈ faceEdges f ↔ e = (rot1 f.1, f.2) ∨ e = (rot2 f.1, step (rot1 f.1) f.2)
      ∨ e = (rot1 f.1, step (rot2 f.1) f.2) ∨ e = (rot2 f.1, f.2) := by
  classical
  simp [faceEdges]

#print axioms rot2_rot1
#print axioms rot1_ne_rot2
#print axioms mem_faceEdges

theorem rot1_rot1 (c : Fin 3) : rot1 (rot1 c) = rot2 c := by
  apply Fin.ext; have := c.isLt; simp [rot1, rot2]

theorem rot2_rot2 (c : Fin 3) : rot2 (rot2 c) = rot1 c := by
  apply Fin.ext; have := c.isLt; simp [rot1, rot2]; omega

/-- `(univ : Finset (Fin 3)) = {c, rot1 c, rot2 c}` for every `c`, by `decide`. The three axes are
exhausted by `c` and its two rotations, which is what lets `cube_edge_even` split a sum over axes
into exactly three named terms.

DERIVED: `3` appears twice, as the axis type of `c` and as the type of the `Finset` being
described — `Cube`'s dimension both times. -/
theorem univ_eq_rot (c : Fin 3) : (univ : Finset (Fin 3)) = {c, rot1 c, rot2 c} := by
  revert c; decide

/-- The four cubes `x`, `step (rot1 c) x`, `step (rot2 c) x` and `step (rot1 c) (step (rot2 c) x)`
are pairwise distinct, stated as a six-fold conjunction — one inequality per unordered pair. These
are the four corners at which an edge along `c` can sit relative to `x`. The proof uses
`CubeArea.ne_step`, `CubeArea.sum_step`, `CubeArea.step_injective` and `rot1_ne_rot2`.

DERIVED: `3` is the axis type of `c`, `Cube`'s dimension. -/
theorem corners_distinct (c : Fin 3) (x : Cube) :
    x ≠ step (rot1 c) x ∧ x ≠ step (rot2 c) x
      ∧ x ≠ step (rot1 c) (step (rot2 c) x)
      ∧ step (rot1 c) x ≠ step (rot2 c) x
      ∧ step (rot1 c) x ≠ step (rot1 c) (step (rot2 c) x)
      ∧ step (rot2 c) x ≠ step (rot1 c) (step (rot2 c) x) := by
  have hne := rot1_ne_rot2 c
  refine ⟨ne_step _ _, ne_step _ _, ?_, ?_, ?_, ?_⟩
  · intro h
    have h1 := sum_step (rot1 c) (step (rot2 c) x)
    have h2 := sum_step (rot2 c) x
    rw [← h] at h1
    omega
  · intro h
    have hco := congrArg (fun v : Cube => v (rot1 c)) h
    simp only [step_self] at hco
    rw [step_other hne x] at hco
    omega
  · intro h
    exact (ne_step (rot2 c) x) (step_injective (rot1 c) h)
  · exact ne_step _ _

#print axioms rot1_rot1
#print axioms corners_distinct

/-- If `a ≠ rot1 c` and `a ≠ rot2 c`, then `(c, w) ∉ faceEdges (a, y)` for any cubes `y`, `w`. The
edges of a face with normal `a` run along `rot1 a` and `rot2 a`; if one of those equalled `c` then
applying `rot2_rot1` or `rot1_rot2` would make `a` a rotation of `c`, contradicting a hypothesis. The
proof splits on the four entries of `faceEdges`.

Scope: the conclusion is for every `y` and `w` — the position of the face is irrelevant, only its
normal.

DERIVED: `3` appears twice, as the axis type of `c` and `a` and as the axis component of the edge
pair — `Cube`'s dimension both times. -/
theorem not_mem_faceEdges_axis {c a : Fin 3} (h1 : a ≠ rot1 c) (h2 : a ≠ rot2 c) (y w : Cube) :
    ((c, w) : Fin 3 × Cube) ∉ faceEdges (a, y) := by
  intro hm
  rcases mem_faceEdges.mp hm with h | h | h | h
  · exact h2 (by have hc : c = rot1 a := congrArg Prod.fst h
                 rw [hc, rot2_rot1])
  · exact h1 (by have hc : c = rot2 a := congrArg Prod.fst h
                 rw [hc, rot1_rot2])
  · exact h2 (by have hc : c = rot1 a := congrArg Prod.fst h
                 rw [hc, rot2_rot1])
  · exact h1 (by have hc : c = rot2 a := congrArg Prod.fst h
                 rw [hc, rot1_rot2])

/-- `(c, w) ∈ faceEdges (rot1 c, y)` if and only if `w = step (rot2 c) y` or `w = y`: a face with
normal `rot1 c` carries exactly two edges along `c`, at `y` and one step along `rot2 c`. The proof
unfolds `faceEdges` using `rot1_rot1` and `rot2_rot1` and discards the two entries whose axis is
`rot2 c`, which differs from `c`.

DERIVED: `3` appears twice, as the axis type of `c` and as the axis component of the edge pair. -/
theorem mem_faceEdges_rot1 (c : Fin 3) (y w : Cube) :
    ((c, w) : Fin 3 × Cube) ∈ faceEdges (rot1 c, y) ↔ w = step (rot2 c) y ∨ w = y := by
  classical
  have h3 : ¬ (c = rot2 c) := fun h => (rot2_ne c) h.symm
  simp [faceEdges, rot1_rot1, rot2_rot1, Prod.ext_iff, h3]

/-- `(c, w) ∈ faceEdges (rot2 c, y)` if and only if `w = y` or `w = step (rot1 c) y`: a face with
normal `rot2 c` carries exactly two edges along `c`, at `y` and one step along `rot1 c`. The proof
unfolds `faceEdges` using `rot2_rot2` and `rot1_rot2`.

DERIVED: `3` appears twice, as the axis type of `c` and as the axis component of the edge pair. -/
theorem mem_faceEdges_rot2 (c : Fin 3) (y w : Cube) :
    ((c, w) : Fin 3 × Cube) ∈ faceEdges (rot2 c, y) ↔ w = y ∨ w = step (rot1 c) y := by
  classical
  have h3 : ¬ (c = rot1 c) := fun h => (rot1_ne c) h.symm
  simp [faceEdges, rot2_rot2, rot1_rot2, Prod.ext_iff, h3]

/-- The families `fun a => {(a, x), (a, step a x)}` are pairwise disjoint as `a` ranges over the
axes: every face in the `a`-family has first component `a`, so two families with different normals
share nothing. This is what lets `Finset.sum_biUnion` split a sum over `faces x` into three
per-axis terms.

DERIVED: `3` appears three times, as the index type of the pairwise-disjointness, its coercion to a
`Set`, and the axis type of `a` — `Cube`'s dimension each time. -/
theorem faces_pairwiseDisjoint (x : Cube) :
    Set.PairwiseDisjoint (↑(univ : Finset (Fin 3)) : Set (Fin 3))
      (fun a : Fin 3 => ({(a, x), (a, step a x)} : Finset Face)) := by
  intro a _ b _ hab
  simp only [Function.onFun]
  refine Finset.disjoint_left.mpr ?_
  intro f hf hf'
  have ha : f.1 = a := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with h | h <;> rw [h]
  have hb : f.1 = b := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf'
    rcases hf' with h | h <;> rw [h]
  exact hab (by rw [← ha, hb])

theorem sum_pair_faces (a : Fin 3) (x : Cube) (F : Face → ℕ) :
    ∑ f ∈ ({(a, x), (a, step a x)} : Finset Face), F f = F (a, x) + F (a, step a x) := by
  classical
  rw [Finset.sum_insert (by simp [Prod.ext_iff, ne_step a x]), Finset.sum_singleton]

#print axioms not_mem_faceEdges_axis
#print axioms mem_faceEdges_rot1
#print axioms mem_faceEdges_rot2
#print axioms faces_pairwiseDisjoint

/-- For any cube `x`, axis `c` and cube `w`, the number of faces of `x` whose edge set contains
`(c, w)` is even: `((faces x).filter (fun f => (c, w) ∈ faceEdges f)).card % 2 = 0`.

The proof splits `faces x` over the three axes by `faces_pairwiseDisjoint` and `univ_eq_rot`. The
two faces with normal `c` contribute nothing (`not_mem_faceEdges_axis`); of the two with normal
`rot1 c` exactly one carries the edge, and likewise for `rot2 c`, by `mem_faceEdges_rot1` and
`mem_faceEdges_rot2` together with `corners_distinct`. The count is therefore two when the edge
belongs to the cube and zero otherwise.

Scope: the conclusion is a parity, not the exact count; and it holds for every `w`, including cubes
far from `x`, with no case on where `x` sits.

DERIVED: `3` appears twice, as the axis type of `c` and as the axis component of the edge pair; `2`
is the modulus of the parity; `0` is the residue asserted. -/
theorem cube_edge_even (x : Cube) (c : Fin 3) (w : Cube) :
    ((faces x).filter (fun f => ((c, w) : Fin 3 × Cube) ∈ faceEdges f)).card % 2 = 0 := by
  classical
  obtain ⟨d01, d02, d03, d12, d13, d23⟩ := corners_distinct c x
  have e01 := d01.symm; have e02 := d02.symm; have e03 := d03.symm
  have e12 := d12.symm; have e13 := d13.symm; have e23 := d23.symm
  have hcomm : step (rot2 c) (step (rot1 c) x) = step (rot1 c) (step (rot2 c) x) :=
    step_comm _ _ _
  have hc1 : c ≠ rot1 c := Ne.symm (rot1_ne c)
  have hc2 : c ≠ rot2 c := Ne.symm (rot2_ne c)
  rw [Finset.card_filter, faces, Finset.sum_biUnion (faces_pairwiseDisjoint x), univ_eq_rot c]
  simp only [sum_pair_faces]
  rw [Finset.sum_insert (by simp [hc1, hc2]),
    Finset.sum_insert (by simp [rot1_ne_rot2 c]), Finset.sum_singleton]
  rw [if_neg (not_mem_faceEdges_axis hc1 hc2 x w),
    if_neg (not_mem_faceEdges_axis hc1 hc2 (step c x) w)]
  simp only [mem_faceEdges_rot1, mem_faceEdges_rot2, hcomm]
  -- Four corners, and everything else. In each case one face of each pair carries the edge.
  by_cases hw0 : w = x
  · subst hw0; simp [d01, d02, d03, e01, e02, e03]
  by_cases hw1 : w = step (rot1 c) x
  · subst hw1; simp [d12, d13, e01, e12, e13]
  by_cases hw2 : w = step (rot2 c) x
  · subst hw2; simp [d23, e02, e12, d12, e23]
  by_cases hw3 : w = step (rot1 c) (step (rot2 c) x)
  · subst hw3; simp [e03, e13, e23]
  · simp [hw0, hw1, hw2, hw3]

#print axioms cube_edge_even

/-- For a decidable predicate `P` on faces,
`∑ x ∈ C, ((faces x).filter P).card = ∑ f ∈ (C.biUnion faces).filter P, (C.filter (fun x => f ∈ faces x)).card`.
Both sides count the incident (cube, face) pairs of `C` whose face satisfies `P`, the left by cube
and the right by face. The proof rewrites each left-hand term as a sum of indicators over the
right-hand index set and swaps the order with `Finset.sum_comm`.

Scope: this is `CubeArea.incidence_double_count` restricted by `P`; with `P` trivially true it
reduces to that statement.

DERIVED: no numeral appears in the statement. -/
theorem incidence_double_count_filter (C : Finset Cube) (P : Face → Prop) [DecidablePred P] :
    ∑ x ∈ C, ((faces x).filter P).card
      = ∑ f ∈ (C.biUnion faces).filter P, (C.filter (fun x => f ∈ faces x)).card := by
  classical
  have hL : ∀ x ∈ C, ((faces x).filter P).card
      = ∑ f ∈ (C.biUnion faces).filter P, (if f ∈ faces x then 1 else 0) := by
    intro x hx
    rw [← Finset.card_filter]
    congr 1
    ext f
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hf, hP⟩
      exact ⟨⟨Finset.mem_biUnion.mpr ⟨x, hx, hf⟩, hP⟩, hf⟩
    · rintro ⟨⟨_, hP⟩, hf⟩
      exact ⟨hf, hP⟩
  rw [Finset.sum_congr rfl hL, Finset.sum_comm]
  exact Finset.sum_congr rfl (fun f _ => (Finset.card_filter _ _).symm)

#print axioms incidence_double_count_filter

/-- For any `C : Finset Cube`, axis `c` and cube `w`,
`((boundaryFaces C).filter (fun f => (c, w) ∈ faceEdges f)).card % 2 = 0`: every edge lies in an even
number of the boundary's faces. This is the `Z₂` condition `∂∂ = 0`.

The proof counts the incident (cube, face) pairs of `C` whose face carries `(c, w)` in two ways,
using `incidence_double_count_filter`. By cube, every term is even by `cube_edge_even`, so the total
is even. By face, each term is the owner count, which `CubeArea.owners_one_or_two` puts at one or
two; modulo two only the one-owner faces survive, and those are exactly `boundaryFaces C`.

Scope: there is no hypothesis on `C` — no interior condition, no assumption that neighbouring cubes
exist, and no case on where `C` sits in `ℕ³`. Absent cubes simply do not appear in the sum. The
conclusion is a parity, not the exact number of incident boundary faces.

DERIVED: `3` appears twice, as the axis type of `c` and as the axis component of the edge pair; `2`
is the modulus of the parity; `0` is the residue asserted. -/
theorem edge_parity_all (C : Finset Cube) (c : Fin 3) (w : Cube) :
    ((boundaryFaces C).filter
      (fun f => ((c, w) : Fin 3 × Cube) ∈ faceEdges f)).card % 2 = 0 := by
  classical
  -- by cube: every term is even
  have hleft : (∑ x ∈ C, ((faces x).filter
      (fun f => ((c, w) : Fin 3 × Cube) ∈ faceEdges f)).card) % 2 = 0 := by
    rw [Finset.sum_nat_mod,
      Finset.sum_congr rfl (fun x _ => cube_edge_even x c w)]
    simp
  rw [incidence_double_count_filter C (fun f => ((c, w) : Fin 3 × Cube) ∈ faceEdges f)] at hleft
  -- by face: modulo two the owner counts count the one-owner faces, which are the boundary
  have hmod : (∑ f ∈ (C.biUnion faces).filter
        (fun f => ((c, w) : Fin 3 × Cube) ∈ faceEdges f),
        (C.filter (fun x => f ∈ faces x)).card) % 2
      = (((C.biUnion faces).filter (fun f => ((c, w) : Fin 3 × Cube) ∈ faceEdges f)).filter
        (fun f => (C.filter (fun x => f ∈ faces x)).card = 1)).card % 2 := by
    rw [Finset.sum_nat_mod]
    congr 1
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl (fun f hf => ?_)
    have h12 := owners_one_or_two C (Finset.mem_filter.mp hf).1
    by_cases h : (C.filter (fun x => f ∈ faces x)).card = 1
    · simp [h]
    · have h2 : (C.filter (fun x => f ∈ faces x)).card = 2 := by omega
      simp [h2, h]
  have hswap : ((C.biUnion faces).filter (fun f => ((c, w) : Fin 3 × Cube) ∈ faceEdges f)).filter
      (fun f => (C.filter (fun x => f ∈ faces x)).card = 1)
      = (boundaryFaces C).filter (fun f => ((c, w) : Fin 3 × Cube) ∈ faceEdges f) := by
    rw [boundaryFaces, Finset.filter_filter, Finset.filter_filter]
    exact Finset.filter_congr (fun f _ => by tauto)
  rw [hmod, hswap] at hleft
  exact hleft

#print axioms edge_parity_all

end MassGap.CubeArea
