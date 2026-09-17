import MassGap.CubeArea

/-!
# The boundary of a cube configuration is CLOSED

**WHY THIS FILE EXISTS.** Theorem 7.1 begins "boundaries of cube-paths are closed vortex surfaces",
and `CubeArea` proves everything about those boundaries EXCEPT that word: they are distinct
(`boundaryFaces_cubeConfig_injective`) and each has exactly `4k+6` faces (`boundary_card_eq`), but
nothing said the face set has no edge of its own. A surface with a free edge is not a vortex
worldsheet, so the entropy floor's count would be over the wrong objects.

**WHAT CLOSED MEANS HERE, and it is a parity statement, not a topological one.** The boundary is
closed when every edge lies in an EVEN number of the boundary's faces — the `Z₂` condition
`∂∂ = 0`, which is what a centre-vortex surface needs and all it needs.

**THE PROOF IS A DOUBLE COUNT, AND IT HOLDS AT EVERY EDGE** — `edge_parity_all`, with no interior
hypothesis and no case on where the configuration sits in `ℕ³`.

Fix an edge and count the incident (cube, face) pairs of `C` whose face carries that edge, two ways.

* **By cube.** Each cube contributes an EVEN number, because each of a cube's twelve edges lies in
  exactly two of its six faces and every other edge in none (`cube_edge_even`). That needs no
  picture: a face spans the two axes its normal is NOT, so the faces carrying an edge along `c` are
  the two with normal `rot1 c` and the two with normal `rot2 c`; of each pair exactly one carries the
  edge, since the pair sits at opposite ends of that normal.
* **By face.** Each face contributes its owner count, which is one or two (`owners_one_or_two`). So
  modulo two the face sum counts exactly the ONE-owner faces — and those are `∂C` by definition.

Hence `|∂C ∩ {faces carrying the edge}|` is even. Written the short way: `∂C` is the `Z₂` sum of the
cubes' own boundaries, so `∂∂C = Σ_x ∂∂x`, and each single cube's boundary is closed.

**WHY IT IS SUMMED THIS WAY.** Summing AROUND an edge instead needs the four cubes surrounding it to
exist, and against the floor of `ℕ³` some of them do not. Summing over cubes never mentions a cube
that is absent — it simply does not appear in the sum. There is no second route here and no interior
case: the earlier four-cycle proof was superseded by this one and removed.

DERIVED: `2` is the number of faces of one cube meeting one of its edges, and the number of owners a
face can have; `6` is `2` sides times the `3` axes; `3` is the dimension. None is chosen.
-/

namespace MassGap.CubeArea

open Finset

/-- Steps along two axes commute: they update different coordinates, and along the same axis both
sides are the same term. -/
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

/-! ### The fixed plaquette -/


/-- **A FACE ON THE FLOOR HAS EXACTLY ONE POSSIBLE OWNER.** `origin_face_mem_boundary` generalised
from the origin to any point whose coordinate along the face's own axis is zero: nothing sits one
step back from there, because a step RAISES that coordinate and `0` is not a successor. So such a
face is on the boundary exactly when its one owner is in the configuration.

This is what fixes the plaquette every counted surface passes through. -/
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

/-- **A FACE IS ON THE BOUNDARY EXACTLY WHEN ITS TWO CUBES DISAGREE.** The face between `p` and
`step a p` has those two as its only possible owners (`owners_subset_pair`), and they are distinct
(`ne_step`), so it has one owner precisely when one of them is in `C` and the other is not.

This is the bridge from the `Finset` definition of `boundaryFaces` to a two-valued statement. With
`mem_boundaryFaces_iff_floor` for the faces that have no cube behind them, it decides boundary
membership for every face of a configuration. -/
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

/-- **EVERY DIRECTED SURFACE PASSES THROUGH THE SAME THREE FACES.** Theorem 7.1 counts closed
surfaces "through a fixed plaquette", and this is that fixedness: the three low faces of the origin
cube are on the boundary of EVERY directed path's configuration, whatever the path does afterwards.

It is `mem_boundaryFaces_iff_floor` at the origin, whose every coordinate is zero, together with the
fact that every path starts at the origin cube.

Together with `edge_parity_all` (closed) and `boundary_card_eq` (area `4k+6`), this is the third and
last property Theorem 7.1's family asks of each surface. -/
theorem origin_face_mem_boundary {k : ℕ} (s : Fin k → Fin 3) (a : Fin 3) :
    ((a, MassGap.cubePos s 0) : Face) ∈ boundaryFaces (MassGap.cubeConfig s) := by
  classical
  have hzero : MassGap.cubePos s 0 a = 0 := by
    rw [MassGap.cubePos]; simp
  exact (mem_boundaryFaces_iff_floor _ a _ hzero).mpr
    (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (Nat.succ_pos k)))

#print axioms origin_face_mem_boundary

/-! ### Closedness at EVERY edge, by summing over cubes rather than around edges

`∂C` is the `Z₂` sum of the cubes' own boundaries: a face of the configuration has one or two owners
(`owners_one_or_two`), and modulo two the two-owner ones cancel, leaving exactly the boundary. So
`∂∂C = Σ_x ∂∂x`, and a SINGLE CUBE's boundary is closed for a reason with no geometry in it — each of
its twelve edges lies in exactly two of its six faces. Every cube in the sum is a whole cube, so
nothing is ever missing, wherever the configuration sits. -/

/-- The next axis round, and the one after. `rot1` and `rot2` are mutually inverse, which is what
makes "the two axes a face spans" nameable without choosing an order.

DERIVED: `3` is `Cube`'s dimension, so it is the modulus of "the next axis round" and not a
magnitude. `1` and `2` are the only two offsets that are neither `0` nor a multiple of `3` — i.e. the
two axes a face with this normal spans. Nothing is chosen: the pair `(rot1, rot2)` exhausts them. -/
def rot1 (c : Fin 3) : Fin 3 := ⟨((c : ℕ) + 1) % 3, by omega⟩

/-- The axis two steps round.

DERIVED: `3` is `Cube`'s dimension and so the modulus; `2` is the second of the only two offsets that
are neither `0` nor a multiple of it, `rot1` being the first. -/
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

/-- **THE FOUR EDGES OF A FACE.** A face spans the two axes its normal is not; its edges run along
those two, one pair at the corner and one pair a step along the other axis.

DERIVED: `3` is `Cube`'s dimension. The four edges are `2` axes times the `2` sides along each — an
arity, and the same `4` that `card_faces` and `boundary_card_eq` are built from. -/
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

/-- The three axes ARE `c` and its two rotations — which is why an edge along `c` meets exactly the
faces whose normal is one of the other two. -/
theorem univ_eq_rot (c : Fin 3) : (univ : Finset (Fin 3)) = {c, rot1 c, rot2 c} := by
  revert c; decide

/-- The four corners of the cube `x` at which an edge along `c` can sit. -/
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

/-- **A FACE WHOSE NORMAL IS NEITHER ROTATION OF `c` CARRIES NO `c`-EDGE.** A face's edges run along
the two axes its normal is not; if the normal is `a`, those are `rot1 a` and `rot2 a`, and asking one
of them to be `c` forces `a` to be a rotation of `c`. -/
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

/-- The two `c`-edges of a face with normal `rot1 c`: the near one and the one a step along `rot2 c`.
-/
theorem mem_faceEdges_rot1 (c : Fin 3) (y w : Cube) :
    ((c, w) : Fin 3 × Cube) ∈ faceEdges (rot1 c, y) ↔ w = step (rot2 c) y ∨ w = y := by
  classical
  have h3 : ¬ (c = rot2 c) := fun h => (rot2_ne c) h.symm
  simp [faceEdges, rot1_rot1, rot2_rot1, Prod.ext_iff, h3]

/-- The two `c`-edges of a face with normal `rot2 c`: the near one and the one a step along `rot1 c`.
-/
theorem mem_faceEdges_rot2 (c : Fin 3) (y w : Cube) :
    ((c, w) : Fin 3 × Cube) ∈ faceEdges (rot2 c, y) ↔ w = y ∨ w = step (rot1 c) y := by
  classical
  have h3 : ¬ (c = rot1 c) := fun h => (rot1_ne c) h.symm
  simp [faceEdges, rot2_rot2, rot1_rot2, Prod.ext_iff, h3]

/-- Faces on different axes are disjoint families, in their normal alone. -/
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

/-- **A SINGLE CUBE'S BOUNDARY IS CLOSED**, and this is the whole geometric content of `∂∂ = 0`.

Each of the cube's twelve edges lies in exactly TWO of its six faces, and every other edge in none.
The reason needs no picture: a face spans the two axes its normal is not, so the faces carrying an
edge along `c` are the two with normal `rot1 c` and the two with normal `rot2 c`; of each pair exactly
one carries the edge, because the pair's two faces sit at opposite ends of that normal and their
`c`-edges are disjoint. So the count is `2` when the edge belongs to the cube and `0` otherwise —
even either way, with no case on where the cube sits. -/
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

/-- **THE DOUBLE COUNT, RESTRICTED TO THE FACES THAT MATTER.** `incidence_double_count` counts every
incident (cube, face) pair; this counts only the pairs whose face satisfies `P`. Same bookkeeping,
same proof, and it is what turns a per-cube parity into a parity of the boundary. -/
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

/-- **`∂C` IS CLOSED AT EVERY EDGE.** No interior hypothesis, no four-cycle, no case on where the
configuration sits in `ℕ³`.

The argument is `∂∂ = 0` read as a double count. Fix an edge and count the incident (cube, face)
pairs of `C` whose face carries that edge, two ways. By cube, each contributes an EVEN number
(`cube_edge_even`: two of its six faces, or none). By face, each face contributes its owner count,
which `owners_one_or_two` puts at one or two — so modulo two the face sum counts exactly the faces
with ONE owner, and those are precisely `∂C`. An even number equals `|∂C ∩ {faces carrying the
edge}|` mod two, which is the statement.

Nothing is assumed to exist: the cubes that are absent simply do not appear in the sum. -/
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
