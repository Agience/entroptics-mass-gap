import MassGap.CubeClosed

/-!
# MassGap.CubeConnected — the boundary of a cube-path is connected

`boundary_connected` states that for every directed cube-path `s : Fin k → Fin 3`, every face of
`boundaryFaces (cubeConfig s)` is reachable from the face `((0 : Fin 3), cubePos s 0)` under
`Relation.ReflTransGen (FaceAdj (boundaryFaces (cubeConfig s)))`, where two faces are adjacent when
they share an edge and both lie in the boundary.

Connectedness is the fourth of the four conditions `VortexFamily` uses to define its counted family;
the other three — closed, of area `4k+6`, through a fixed plaquette — are established elsewhere.
Without it a family of that area admits unions of unit-cube boundaries, each closed because every
link lies in two or four of them, whose components may sit anywhere in the box, and the count `N(A)`
then grows faster in `k` than `hdual`'s fixed density bound allows.

## How the descent runs

A directed path visits exactly one cube at each coordinate sum `0 … k` (`cubePos_sum_le`,
restated here as `mem_cubeConfig_iff`), and each step advances the whole cube by one `step`
(`cubePos_step`). Three consequences carry the argument:

* A face of `xᵢ` has at most one other owner, whose coordinate sum is `i ± 1`, so that owner can only
  be `xᵢ₋₁` or `xᵢ₊₁`. Hence at most two of a cube's six faces are off the boundary — the one it was
  entered through and the one it leaves by. `high_mem_boundary` and `low_mem_boundary` are the two
  membership statements.
* Two faces of one cube with different normals share an edge, whatever their corners
  (`sharesEdge_low_low`, `sharesEdge_low_high`, `sharesEdge_high_high`), so any boundary face of a
  cube reaches a chosen low face of that cube in at most two hops (`reach_low_of_mem_faces`); the
  two-hop case is the opposite face, the only pair of a cube's faces sharing no edge.
* The low face of `xᵢ` on axis `a` and the low face of `xᵢ₋₁` on the same axis share an edge whenever
  `a` is not the axis of the step between them (`sharesEdge_ladder`). Two axes are not, and at most
  one of those is the previous step's axis, so a rung always exists.

`reach_origin_face` is the strong induction on the path index that descends rung by rung to `x₀`,
whose low face on axis `0` is the fixed plaquette's preimage; `boundary_connected` is that statement
with the relation reversed, by `reflTransGen_faceAdj_symm`.

DERIVED: `3` is the dimension and the number of axes; `6 = 2 * 3` is the number of faces of a cube;
`2` is the number of owners a face can have and the number of a cube's faces that can be off the
boundary; `1` is the index increment along the path; `0` is the origin index and the origin face's
axis. None is chosen.
-/

namespace MassGap.CubeArea

open Finset

/-! ### The third axis -/

/-- The axis that is neither `a` nor `d`, as `(3 - a - d) % 3` on `Fin 3`. The `% 3` only makes the
definition total; when `a ≠ d` the natural subtraction already lands in range, because the three axis
indices sum to `3`. At `a = d` the value is unconstrained and the lemmas below all carry `a ≠ d`.

DERIVED: every `3` is `Cube`'s dimension — the axis count, the sum `0 + 1 + 2` of the three indices,
and the modulus. The formula is forced by the dimension. -/
def third (a d : Fin 3) : Fin 3 := ⟨(3 - (a : ℕ) - (d : ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩

theorem third_ne_left {a d : Fin 3} (h : a ≠ d) : third a d ≠ a := by
  revert h; revert a d; decide

theorem third_ne_right {a d : Fin 3} (h : a ≠ d) : third a d ≠ d := by
  revert h; revert a d; decide

theorem third_comm (a d : Fin 3) : third a d = third d a := by
  revert a d; decide

/-- `third a (third a d) = d` when `a ≠ d`: naming the third axis twice returns the axis started
from. By `decide` over the finitely many pairs.

DERIVED: `3` is `Cube`'s dimension, the axis count. -/
theorem third_third {a d : Fin 3} (h : a ≠ d) : third a (third a d) = d := by
  revert h; revert a d; decide

theorem third_rot1 (a : Fin 3) : third a (rot1 a) = rot2 a := by
  revert a; decide

theorem third_rot2 (a : Fin 3) : third a (rot2 a) = rot1 a := by
  revert a; decide

theorem eq_rot_of_ne {a d : Fin 3} (h : d ≠ a) : d = rot1 a ∨ d = rot2 a := by
  revert h; revert a d; decide

#print axioms third_ne_left
#print axioms third_third
#print axioms eq_rot_of_ne

/-! ### Which edges a face carries, uniformly in the axis -/

/-- For `d ≠ a`, an edge `(d, w)` lies in `faceEdges (a, y)` exactly when `w = y` or
`w = step (third a d) y`: a face with normal `a` carries, along each axis other than `a`, exactly two
edges — the one at its own corner and the one a step along the remaining axis. Proved by splitting
`d` into the two rotations of `a` via `eq_rot_of_ne` and applying `mem_faceEdges_rot1` and
`mem_faceEdges_rot2`.

Stating it through `third` rather than through a named rotation is what lets the four adjacency
lemmas below be proved once each rather than per rotation case.

DERIVED: `3` is `Cube`'s dimension, the axis count. -/
theorem mem_faceEdges_iff {a d : Fin 3} (hd : d ≠ a) (y w : Cube) :
    ((d, w) : Fin 3 × Cube) ∈ faceEdges (a, y) ↔ w = y ∨ w = step (third a d) y := by
  rcases eq_rot_of_ne hd with rfl | rfl
  · -- normal `a` is `rot2` of the edge direction, and the remaining axis is `rot1` of it
    have hax : faceEdges ((a, y) : Face) = faceEdges ((rot2 (rot1 a), y) : Face) := by
      rw [rot2_rot1]
    rw [hax, mem_faceEdges_rot2 (rot1 a) y w, rot1_rot1 a, third_rot1 a]
  · have hax : faceEdges ((a, y) : Face) = faceEdges ((rot1 (rot2 a), y) : Face) := by
      rw [rot1_rot2]
    rw [hax, mem_faceEdges_rot1 (rot2 a) y w, rot2_rot2 a, third_rot2 a]
    exact Or.comm

#print axioms mem_faceEdges_iff

/-! ### Which faces share an edge

Four shapes are needed and each is witnessed by one named edge, along the axis that is neither of the
two in play. Nothing here is a case analysis on position: the witness is written down and checked. -/

/-- Two faces share an edge: `(faceEdges f ∩ faceEdges g).Nonempty`. This is `VortexFamily.SurfAdj`
read in three dimensions.

DERIVED: no numeral appears in the statement. -/
def SharesEdge (f g : Face) : Prop := (faceEdges f ∩ faceEdges g).Nonempty

theorem SharesEdge.symm {f g : Face} (h : SharesEdge f g) : SharesEdge g f := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, by rw [Finset.mem_inter] at he ⊢; exact ⟨he.2, he.1⟩⟩

/-- The two low faces of a cube on different axes share an edge. The witness is `(third a b, x)`,
the edge at the shared corner running along the axis that is neither `a` nor `b`; membership on both
sides is `mem_faceEdges_iff` with `w = y`.

DERIVED: `3` is `Cube`'s dimension, the axis count. -/
theorem sharesEdge_low_low {a b : Fin 3} (h : a ≠ b) (x : Cube) :
    SharesEdge ((a, x) : Face) ((b, x) : Face) := by
  refine ⟨(third a b, x), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · exact (mem_faceEdges_iff (third_ne_left h) x x).mpr (Or.inl rfl)
  · exact (mem_faceEdges_iff (third_ne_right h) x x).mpr (Or.inl rfl)

/-- A cube's low face on axis `a` and its high face on a different axis `b` share an edge. The
witness is `(third a b, step b x)`, reached from the first face by `third_third` and lying at the
second face's own corner.

DERIVED: `3` is `Cube`'s dimension, the axis count. -/
theorem sharesEdge_low_high {a b : Fin 3} (h : a ≠ b) (x : Cube) :
    SharesEdge ((a, x) : Face) ((b, step b x) : Face) := by
  refine ⟨(third a b, step b x), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · refine (mem_faceEdges_iff (third_ne_left h) x _).mpr (Or.inr ?_)
    rw [third_third h]
  · exact (mem_faceEdges_iff (third_ne_right h) _ _).mpr (Or.inl rfl)

/-- The two high faces of a cube on different axes share an edge: the one at the far corner
`step a (step b x)`, which the two steps reach in either order, by `step_comm` and `third_comm`.

DERIVED: `3` is `Cube`'s dimension, the axis count. -/
theorem sharesEdge_high_high {a b : Fin 3} (h : a ≠ b) (x : Cube) :
    SharesEdge ((a, step a x) : Face) ((b, step b x) : Face) := by
  refine ⟨(third a b, step a (step b x)), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · refine (mem_faceEdges_iff (third_ne_left h) _ _).mpr (Or.inr ?_)
    rw [third_third h, step_comm]
  · refine (mem_faceEdges_iff (third_ne_right h) _ _).mpr (Or.inr ?_)
    rw [third_comm a b, third_third (Ne.symm h)]

/-- The rung: the low face on axis `a` of a cube and the low face on the same axis of the cube one
step along `b ≠ a` share an edge, the witness being `(third a b, step b x)`. The two faces are
parallel and offset within their own plane, so they meet along the edge between them. This is the
step `reach_origin_face` uses to descend from `xᵢ` to `xᵢ₋₁`.

DERIVED: `3` is `Cube`'s dimension, the axis count. -/
theorem sharesEdge_ladder {a b : Fin 3} (h : a ≠ b) (x : Cube) :
    SharesEdge ((a, x) : Face) ((a, step b x) : Face) := by
  refine ⟨(third a b, step b x), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · refine (mem_faceEdges_iff (third_ne_left h) x _).mpr (Or.inr ?_)
    rw [third_third h]
  · exact (mem_faceEdges_iff (third_ne_left h) _ _).mpr (Or.inl rfl)

#print axioms sharesEdge_low_low
#print axioms sharesEdge_low_high
#print axioms sharesEdge_high_high
#print axioms sharesEdge_ladder

/-! ### One cube per coordinate sum

`cubePos_sum_le` says the `i`-th cube of the path has coordinate sum exactly `i`, so the
configuration meets each sum once. A cube's neighbour in the configuration differs in sum by one and
can therefore only be its predecessor or its successor on the path. `mem_cubeConfig_iff` states
membership in those terms, and `cubePos_step` states that one step of the path is one `step` of the
whole cube.

DERIVED: `3` is `Cube`'s dimension; `1` is the index increment along the path.
-/

variable {k : ℕ}

/-- `cubePos s ((j : ℕ) + 1) = step (s j) (cubePos s j)`: one index of the path advances the whole
cube by one `step` along the axis `s j`. Proved coordinatewise from `cubePos_succ`, splitting on
whether the coordinate is the step axis.

DERIVED: `3` is `Cube`'s dimension; `1` is the index increment. -/
theorem cubePos_step (s : Fin k → Fin 3) (j : Fin k) :
    MassGap.cubePos s ((j : ℕ) + 1) = step (s j) (MassGap.cubePos s (j : ℕ)) := by
  funext a
  rw [MassGap.cubePos_succ s j a]
  by_cases hja : s j = a
  · rw [if_pos hja, hja, step_self]
  · rw [if_neg hja, step_other (fun h => hja h.symm)]
    omega

/-- `y ∈ cubeConfig s` exactly when `∑ b, y b ≤ k` and `cubePos s (∑ b, y b) = y`: membership is
decided by the coordinate sum, which identifies the one index of the path that could carry `y`.

DERIVED: `3` is `Cube`'s dimension. -/
theorem mem_cubeConfig_iff (s : Fin k → Fin 3) (y : Cube) :
    y ∈ MassGap.cubeConfig s ↔ (∑ b, y b) ≤ k ∧ MassGap.cubePos s (∑ b, y b) = y := by
  classical
  constructor
  · intro hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [MassGap.cubePos_sum_le s hik]
    exact ⟨hik, rfl⟩
  · rintro ⟨hle, heq⟩
    rw [← heq]
    exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hle))

theorem cubePos_mem (s : Fin k → Fin 3) {i : ℕ} (hi : i ≤ k) :
    MassGap.cubePos s i ∈ MassGap.cubeConfig s :=
  Finset.mem_image_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hi))

theorem sum_step_cubePos (s : Fin k → Fin 3) {i : ℕ} (hi : i ≤ k) (a : Fin 3) :
    (∑ b, step a (MassGap.cubePos s i) b) = i + 1 := by
  rw [sum_step, MassGap.cubePos_sum_le s hi]

#print axioms cubePos_step
#print axioms mem_cubeConfig_iff

/-! ### Which faces of the path are on the boundary

At most two of a cube's six faces are off the boundary: the one it was entered through and the one it
leaves by. The two theorems below give the corresponding membership statements, each conditional on
the relevant step's axis differing from the face's normal.

DERIVED: `2` is the number of faces that can be off the boundary, one per adjacent cube on the path;
`6 = 2 * 3` is a cube's face count; `3` is `Cube`'s dimension. -/

/-- `(a, step a (cubePos s i))` is in `boundaryFaces (cubeConfig s)` provided no step of the path
leaving index `i` is along `a`. Through `mem_boundaryFaces_iff_xor`, the cube `cubePos s i` is in
the configuration while `step a (cubePos s i)` is not: any member with that coordinate sum would have
to be `cubePos s (i+1)`, and `cubePos_step` with `step_axis_inj` would then make `a` the step axis,
contradicting `hne`.

DERIVED: `3` is `Cube`'s dimension. -/
theorem high_mem_boundary (s : Fin k → Fin 3) {i : ℕ} (hi : i ≤ k) (a : Fin 3)
    (hne : ∀ j : Fin k, (j : ℕ) = i → s j ≠ a) :
    ((a, step a (MassGap.cubePos s i)) : Face) ∈ boundaryFaces (MassGap.cubeConfig s) := by
  classical
  refine (mem_boundaryFaces_iff_xor _ a _).mpr ?_
  have hin : MassGap.cubePos s i ∈ MassGap.cubeConfig s := cubePos_mem s hi
  have hout : step a (MassGap.cubePos s i) ∉ MassGap.cubeConfig s := by
    intro hmem
    obtain ⟨hle, heq⟩ := (mem_cubeConfig_iff s _).mp hmem
    rw [sum_step_cubePos s hi a] at hle heq
    have hik : i < k := by omega
    have := cubePos_step s ⟨i, hik⟩
    simp only at this
    rw [this] at heq
    exact hne ⟨i, hik⟩ rfl (step_axis_inj heq)
  exact ⟨fun _ => hout, fun _ => hin⟩

/-- `(a, cubePos s i)` is in `boundaryFaces (cubeConfig s)` provided no step of the path arriving at
index `i` is along `a`. The proof splits on whether the `a`-coordinate is `0`: if it is,
`mem_boundaryFaces_iff_floor` applies, since nothing sits one step back from the floor of `ℕ³`;
otherwise the cube one step back exists and is shown not to be in the configuration, by the same sum
argument as `high_mem_boundary`.

At `i = 0` the hypothesis `hne` is vacuous, so every low face of the origin cube is on the boundary.

DERIVED: `3` is `Cube`'s dimension; `1` is the index decrement to the previous cube. -/
theorem low_mem_boundary (s : Fin k → Fin 3) {i : ℕ} (hi : i ≤ k) (a : Fin 3)
    (hne : ∀ j : Fin k, (j : ℕ) + 1 = i → s j ≠ a) :
    ((a, MassGap.cubePos s i) : Face) ∈ boundaryFaces (MassGap.cubeConfig s) := by
  classical
  have hin : MassGap.cubePos s i ∈ MassGap.cubeConfig s := cubePos_mem s hi
  by_cases hzero : MassGap.cubePos s i a = 0
  · exact (mem_boundaryFaces_iff_floor _ a _ hzero).mpr hin
  -- there IS a cube one step back; it is not in the configuration
  obtain ⟨p, hp⟩ : ∃ p : Cube, step a p = MassGap.cubePos s i := by
    refine ⟨Function.update (MassGap.cubePos s i) a (MassGap.cubePos s i a - 1), ?_⟩
    funext b
    by_cases hba : b = a
    · subst hba
      rw [step_self, Function.update_apply, if_pos rfl]
      omega
    · rw [step_other hba, Function.update_apply, if_neg hba]
  rw [← hp]
  refine (mem_boundaryFaces_iff_xor _ a p).mpr ?_
  have hpout : p ∉ MassGap.cubeConfig s := by
    intro hmem
    obtain ⟨hle, heq⟩ := (mem_cubeConfig_iff s p).mp hmem
    -- `p` has sum `i - 1`, so it would have to be the path's `(i-1)`-th cube
    have hsum : (∑ b, p b) + 1 = i := by
      have := sum_step a p
      rw [hp, MassGap.cubePos_sum_le s hi] at this
      omega
    have hik : (∑ b, p b) < k := by omega
    have hstep := cubePos_step s ⟨∑ b, p b, hik⟩
    simp only at hstep
    rw [heq, hsum] at hstep
    rw [← hp] at hstep
    exact hne ⟨∑ b, p b, hik⟩ hsum (step_axis_inj hstep.symm)
  rw [hp]
  exact ⟨fun h => absurd h hpout, fun h => absurd hin h⟩

#print axioms high_mem_boundary
#print axioms low_mem_boundary

/-! ### The descent

Two boundary faces are adjacent when they share an edge and both lie in the boundary, which is
`FaceAdj`. Every boundary face of `xᵢ` reaches the low face of `xᵢ` on a chosen axis in at most two
hops, that low face crosses the rung to `xᵢ₋₁`, and the descent ends at `x₀`, whose low face on axis
`0` is the fixed plaquette's preimage.

DERIVED: `2` is the hop bound inside one cube; `0` is the origin index and the origin face's axis;
`3` is `Cube`'s dimension. -/

/-- Adjacency inside a set of faces: both faces lie in `B` and they share an edge. This is
`VortexFamily.SurfAdj` read in three dimensions.

DERIVED: no numeral appears in the statement. -/
def FaceAdj (B : Finset Face) (f g : Face) : Prop := f ∈ B ∧ g ∈ B ∧ SharesEdge f g

theorem FaceAdj.symm {B : Finset Face} {f g : Face} (h : FaceAdj B f g) : FaceAdj B g f :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

theorem reflTransGen_faceAdj_symm {B : Finset Face} {f g : Face}
    (h : Relation.ReflTransGen (FaceAdj B) f g) : Relation.ReflTransGen (FaceAdj B) g f := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head hstep.symm ih

/-- Any face of the cube `x` that lies in `B` reaches `(a, x)` under `ReflTransGen (FaceAdj B)`,
given that both `(a, x)` and `(d, x)` are in `B` for some `d ≠ a`. The proof splits `f` by
`mem_faces` into a low or high face with some normal `c`: zero hops if it is `(a, x)` itself, one hop
by `sharesEdge_low_low` or `sharesEdge_low_high` if `c ≠ a`, and two hops through `(d, x)` if `f` is
`(a, step a x)`, the face opposite the target and the only one sharing no edge with it.

DERIVED: `3` is `Cube`'s dimension, the axis count. -/
theorem reach_low_of_mem_faces {B : Finset Face} {x : Cube} {a d : Fin 3} (had : a ≠ d)
    (hA : ((a, x) : Face) ∈ B) (hD : ((d, x) : Face) ∈ B)
    {f : Face} (hfB : f ∈ B) (hf : f ∈ faces x) :
    Relation.ReflTransGen (FaceAdj B) f ((a, x) : Face) := by
  obtain ⟨c, hc⟩ := mem_faces.mp hf
  rcases hc with rfl | rfl
  · by_cases hca : c = a
    · subst hca; exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨hfB, hA, sharesEdge_low_low hca x⟩
  · by_cases hca : c = a
    · -- the opposite face: go round through the other low face
      subst hca
      refine Relation.ReflTransGen.head ⟨hfB, hD, ?_⟩
        (Relation.ReflTransGen.single ⟨hD, hA, sharesEdge_low_low (Ne.symm had) x⟩)
      exact (sharesEdge_low_high (Ne.symm had) x).symm
    · exact Relation.ReflTransGen.single ⟨hfB, hA,
        (sharesEdge_low_high (fun h => hca h.symm) x).symm⟩

#print axioms reach_low_of_mem_faces

/-- Converts the arriving-step condition from the single index `i - 1` to the quantified form
`low_mem_boundary` takes: from `∀ hk, 0 < i → s ⟨i - 1, hk⟩ ≠ a` it produces
`∀ j : Fin k, (j : ℕ) + 1 = i → s j ≠ a`. Only the one step that arrives at `i` is ever examined,
since `(j : ℕ) + 1 = i` pins `j` to `i - 1`.

DERIVED: `3` is `Cube`'s dimension; `1` is the index decrement to the arriving step; `0` is the
lower bound on `i` that makes `i - 1` a genuine predecessor. -/
theorem low_hne_of (s : Fin k → Fin 3) {i : ℕ} {a : Fin 3}
    (h : ∀ (hk : i - 1 < k), 0 < i → s ⟨i - 1, hk⟩ ≠ a) :
    ∀ j : Fin k, (j : ℕ) + 1 = i → s j ≠ a := by
  intro j hj
  have h2 : i - 1 = (j : ℕ) := by omega
  have h3 : i - 1 < k := by rw [h2]; exact j.isLt
  have hres := h h3 (by omega)
  rwa [show (⟨i - 1, h3⟩ : Fin k) = j from Fin.ext h2] at hres

/-- Every boundary face of a cube on the path reaches `((0 : Fin 3), cubePos s 0)` under
`ReflTransGen (FaceAdj (boundaryFaces (cubeConfig s)))`. Strong induction on the cube's index `i`.

At `i = 0` every low face of the origin cube is on the boundary, by `low_mem_boundary` with a vacuous
hypothesis, and `reach_low_of_mem_faces` at axes `0` and `1` finishes. At `i' + 1`, the two axes
other than the entry axis give boundary low faces; one of them is also not the previous step's axis,
by `rot1_ne_rot2`, and that axis `a` is the rung. `reach_low_of_mem_faces` reaches `(a, cubePos s
(i'+1))` inside the cube, `sharesEdge_ladder` crosses to `(a, cubePos s i')`, and the inductive
hypothesis applies there.

DERIVED: `3` is `Cube`'s dimension; `0` is the origin index and the origin face's axis; `1` is the
index increment and the second axis used at the origin. -/
theorem reach_origin_face (s : Fin k → Fin 3) :
    ∀ i, i ≤ k → ∀ f ∈ boundaryFaces (MassGap.cubeConfig s), f ∈ faces (MassGap.cubePos s i) →
      Relation.ReflTransGen (FaceAdj (boundaryFaces (MassGap.cubeConfig s))) f
        (((0 : Fin 3), MassGap.cubePos s 0) : Face) := by
  classical
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi f hfB hf
    match hzero : i with
    | 0 =>
      subst hzero
      -- at the origin every low face is on the boundary: nothing sits one step back from zero
      have hlow : ∀ c : Fin 3, ((c, MassGap.cubePos s 0) : Face)
          ∈ boundaryFaces (MassGap.cubeConfig s) := fun c =>
        low_mem_boundary s (Nat.zero_le k) c (fun j hj => absurd hj (by omega))
      exact reach_low_of_mem_faces (show (0 : Fin 3) ≠ 1 by decide)
        (hlow 0) (hlow 1) hfB hf
    | i' + 1 =>
      subst hzero
      have hik : i' < k := by omega
      have hi' : i' ≤ k := by omega
      -- the axis the path entered `x_{i'+1}` by
      have hstep : MassGap.cubePos s (i' + 1)
          = step (s ⟨i', hik⟩) (MassGap.cubePos s i') := cubePos_step s ⟨i', hik⟩
      -- the two axes that are not the entry axis; both give boundary low faces of `x_{i'+1}`
      have hlow : ∀ c : Fin 3, c ≠ s ⟨i', hik⟩ →
          ((c, MassGap.cubePos s (i' + 1)) : Face) ∈ boundaryFaces (MassGap.cubeConfig s) := by
        intro c hc
        refine low_mem_boundary s hi c ?_
        intro j hj
        have hjv : (j : ℕ) = i' := by omega
        rw [show j = (⟨i', hik⟩ : Fin k) from Fin.ext hjv]
        exact fun h => hc h.symm
      -- pick the rung axis: not the entry axis, and not the previous entry axis
      have hpick : ∃ a : Fin 3, a ≠ s ⟨i', hik⟩ ∧
          (∀ j : Fin k, (j : ℕ) + 1 = i' → s j ≠ a) := by
        by_cases h1 : ∀ j : Fin k, (j : ℕ) + 1 = i' → s j ≠ rot1 (s ⟨i', hik⟩)
        · exact ⟨rot1 (s ⟨i', hik⟩), rot1_ne _, h1⟩
        · refine ⟨rot2 (s ⟨i', hik⟩), rot2_ne _, ?_⟩
          push_neg at h1
          obtain ⟨j0, hj0, hs0⟩ := h1
          intro j hj hcon
          have hjv : (j : ℕ) = (j0 : ℕ) := by omega
          rw [show j = j0 from Fin.ext hjv, hs0] at hcon
          exact (rot1_ne_rot2 _) hcon
      obtain ⟨a, hane, haprev⟩ := hpick
      -- the other low face of `x_{i'+1}`, for the two-hop case
      have hdne : third a (s ⟨i', hik⟩) ≠ s ⟨i', hik⟩ := third_ne_right hane
      have hAD : a ≠ third a (s ⟨i', hik⟩) := fun h => (third_ne_left hane) h.symm
      -- inside the cube, reach the low face on `a`
      have hin : Relation.ReflTransGen (FaceAdj (boundaryFaces (MassGap.cubeConfig s))) f
          ((a, MassGap.cubePos s (i' + 1)) : Face) :=
        reach_low_of_mem_faces hAD (hlow a hane) (hlow _ hdne) hfB hf
      -- cross the rung to the same low face of `x_{i'}`
      have hprevB : ((a, MassGap.cubePos s i') : Face)
          ∈ boundaryFaces (MassGap.cubeConfig s) := low_mem_boundary s hi' a haprev
      have hrung : FaceAdj (boundaryFaces (MassGap.cubeConfig s))
          ((a, MassGap.cubePos s (i' + 1)) : Face) ((a, MassGap.cubePos s i') : Face) := by
        refine ⟨hlow a hane, hprevB, ?_⟩
        have := sharesEdge_ladder hane (MassGap.cubePos s i')
        rw [← hstep] at this
        exact this.symm
      refine hin.trans (Relation.ReflTransGen.head hrung ?_)
      exact ih i' (by omega) hi' _ hprevB (mem_faces.mpr ⟨a, Or.inl rfl⟩)

#print axioms reach_origin_face

/-- Every face of `boundaryFaces (cubeConfig s)` is reachable from `((0 : Fin 3), cubePos s 0)` under
`ReflTransGen (FaceAdj (boundaryFaces (cubeConfig s)))`, so the boundary of a cube-path is connected
from that face. A boundary face belongs to some cube of the configuration, `reach_origin_face` runs
the descent, and `reflTransGen_faceAdj_symm` reverses it.

DERIVED: `3` is `Cube`'s dimension; `0` is the origin index and the origin face's axis. -/
theorem boundary_connected (s : Fin k → Fin 3) :
    ∀ f ∈ boundaryFaces (MassGap.cubeConfig s),
      Relation.ReflTransGen (FaceAdj (boundaryFaces (MassGap.cubeConfig s)))
        (((0 : Fin 3), MassGap.cubePos s 0) : Face) f := by
  classical
  intro f hf
  obtain ⟨x, hx, hfx⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hf).1
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  exact reflTransGen_faceAdj_symm (reach_origin_face s i hik f hf hfx)

#print axioms boundary_connected

end MassGap.CubeArea
