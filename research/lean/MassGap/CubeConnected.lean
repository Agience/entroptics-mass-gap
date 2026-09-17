import MassGap.CubeClosed

/-!
# The boundary of a cube-path is CONNECTED

**WHY THIS FILE EXISTS.** `VortexFamily` defines the counted family by four conditions, and three of
them are theorems already: closed, of area `4k+6`, through a fixed plaquette. The fourth is
connectedness, and it is not decoration. Without it the family admits a union of unit-cube boundaries
— closed, since every link lies in two or four of them — whose pieces may sit anywhere in the box. At
area `4k+6` that is one anchored piece plus about `2k/3` floating ones in a box of about `k⁴` sites,
so `log N / (4k+6)` grows like `(log k)/2`. `hdual` asks for a FIXED bound on that density, so against
the larger family it is unsatisfiable and every theorem taking it is vacuous. Connectedness is what
makes the density bounded, and it is what Theorem 7.1's `N(A)` always meant.

**THE PROOF, and it is a descent on the path's own index.** A directed path visits exactly one cube
at each coordinate sum `0 … k` (`cubePos_sum`), which is the fact the whole argument runs on:

* A face of `xᵢ` has at most one other owner, and that owner has coordinate sum `i ± 1`, so it can
  only be `xᵢ₋₁` or `xᵢ₊₁`. Hence AT MOST TWO of a cube's six faces are off the boundary — the one it
  was entered through and the one it leaves by.
* Two faces of one cube with DIFFERENT normals share an edge, whatever their corners
  (`faceAdj_of_ne_axis`). So the boundary faces of one cube are connected to each other: four or more
  of six remain, spread over three axes, so two different axes are always represented.
* The low face of `xᵢ` on axis `a` and the low face of `xᵢ₋₁` on the same axis share an edge whenever
  `a` is not the axis of the step between them (`faceAdj_ladder`). Two axes are not, and at most one
  of those is the axis of the PREVIOUS step, so at least one rung always exists.

Descending rung by rung reaches `x₀`, whose low face on axis `0` is the fixed plaquette's preimage.

DERIVED: `3` is the dimension and the number of axes; `6 = 2 × 3` the faces of a cube; `2` the owners
a face can have and the faces of a cube that can be off the boundary. None is chosen.
-/

namespace MassGap.CubeArea

open Finset

/-! ### The third axis -/

/-- The axis that is neither `a` nor `d`. The `% 3` only makes the definition total; at `a ≠ d` the
subtraction already lands in range, because the three axes sum to `3`.

DERIVED: every `3` here is `Cube`'s dimension. `0 + 1 + 2 = 3` is why the remaining axis is the
difference, so the formula is forced by the dimension and is not a fitted expression. -/
def third (a d : Fin 3) : Fin 3 := ⟨(3 - (a : ℕ) - (d : ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩

theorem third_ne_left {a d : Fin 3} (h : a ≠ d) : third a d ≠ a := by
  revert h; revert a d; decide

theorem third_ne_right {a d : Fin 3} (h : a ≠ d) : third a d ≠ d := by
  revert h; revert a d; decide

theorem third_comm (a d : Fin 3) : third a d = third d a := by
  revert a d; decide

/-- Naming the third axis twice returns the one you started from. -/
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

/-- **A FACE'S EDGES, WITHOUT NAMING A ROTATION.** A face with normal `a` carries, along each axis
`d ≠ a`, exactly two edges: the one at its own corner and the one a step along the remaining axis.
`mem_faceEdges_rot1` and `mem_faceEdges_rot2` are the two halves of this; saying it with `third`
removes the choice of which rotation is which, which is what lets the adjacency lemmas below be
stated once instead of per case. -/
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

Four shapes are needed and each is witnessed by ONE named edge, along the axis that is neither of the
two in play. Nothing here is a case analysis on position: the witness is written down and checked. -/

/-- Two faces share an edge. This is `SurfAdj` read in three dimensions. -/
def SharesEdge (f g : Face) : Prop := (faceEdges f ∩ faceEdges g).Nonempty

theorem SharesEdge.symm {f g : Face} (h : SharesEdge f g) : SharesEdge g f := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, by rw [Finset.mem_inter] at he ⊢; exact ⟨he.2, he.1⟩⟩

/-- **THE TWO LOW FACES OF A CUBE ON DIFFERENT AXES SHARE AN EDGE** — the one at the shared corner
running along the axis that is neither. -/
theorem sharesEdge_low_low {a b : Fin 3} (h : a ≠ b) (x : Cube) :
    SharesEdge ((a, x) : Face) ((b, x) : Face) := by
  refine ⟨(third a b, x), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · exact (mem_faceEdges_iff (third_ne_left h) x x).mpr (Or.inl rfl)
  · exact (mem_faceEdges_iff (third_ne_right h) x x).mpr (Or.inl rfl)

/-- **A LOW FACE AND A HIGH FACE ON DIFFERENT AXES SHARE AN EDGE.** -/
theorem sharesEdge_low_high {a b : Fin 3} (h : a ≠ b) (x : Cube) :
    SharesEdge ((a, x) : Face) ((b, step b x) : Face) := by
  refine ⟨(third a b, step b x), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · refine (mem_faceEdges_iff (third_ne_left h) x _).mpr (Or.inr ?_)
    rw [third_third h]
  · exact (mem_faceEdges_iff (third_ne_right h) _ _).mpr (Or.inl rfl)

/-- **THE TWO HIGH FACES OF A CUBE ON DIFFERENT AXES SHARE AN EDGE** — the far corner's, which the
two steps reach in either order. -/
theorem sharesEdge_high_high {a b : Fin 3} (h : a ≠ b) (x : Cube) :
    SharesEdge ((a, step a x) : Face) ((b, step b x) : Face) := by
  refine ⟨(third a b, step a (step b x)), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · refine (mem_faceEdges_iff (third_ne_left h) _ _).mpr (Or.inr ?_)
    rw [third_third h, step_comm]
  · refine (mem_faceEdges_iff (third_ne_right h) _ _).mpr (Or.inr ?_)
    rw [third_comm a b, third_third (Ne.symm h)]

/-- **THE RUNG.** The low face on axis `a` of a cube, and the low face on the SAME axis of the cube
one step along `b ≠ a`, share an edge. This is what carries the descent from `xᵢ` to `xᵢ₋₁`: the two
faces are parallel and offset within their own plane, so they meet along the edge between them. -/
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

The single fact the whole descent runs on. `cubePos_sum_le` says the `i`-th cube has coordinate sum
exactly `i`, so the configuration meets each sum once — and therefore a cube's neighbour in the
configuration, which differs in sum by one, can only be its predecessor or its successor on the path.
-/

variable {k : ℕ}

/-- The path advances by one `step`, as a whole cube rather than coordinatewise. -/
theorem cubePos_step (s : Fin k → Fin 3) (j : Fin k) :
    MassGap.cubePos s ((j : ℕ) + 1) = step (s j) (MassGap.cubePos s (j : ℕ)) := by
  funext a
  rw [MassGap.cubePos_succ s j a]
  by_cases hja : s j = a
  · rw [if_pos hja, hja, step_self]
  · rw [if_neg hja, step_other (fun h => hja h.symm)]
    omega

/-- Membership in the configuration is decided by the coordinate sum alone. -/
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
leaves by. Everything else is on the boundary, and that is what the descent has to walk on. -/

/-- **THE HIGH FACES.** `(a, step a xᵢ)` is on the boundary unless the path leaves `xᵢ` along `a`. -/
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

/-- **THE LOW FACES.** `(a, xᵢ)` is on the boundary unless the path entered `xᵢ` along `a`. At `i = 0`
it is always on the boundary, because nothing sits one step back from the floor of `ℕ³`. -/
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

Two faces of the boundary are adjacent when they share an edge. Every boundary face of `x_i` reaches
the low face of `x_i` on a chosen axis in at most two hops, that low face steps down the rung to
`x_{i-1}`, and the descent ends at `x_0`, whose low face on axis `0` is the fixed plaquette. -/

/-- Adjacency inside a set of faces. This is `VortexFamily.SurfAdj` read in three dimensions. -/
def FaceAdj (B : Finset Face) (f g : Face) : Prop := f ∈ B ∧ g ∈ B ∧ SharesEdge f g

theorem FaceAdj.symm {B : Finset Face} {f g : Face} (h : FaceAdj B f g) : FaceAdj B g f :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

theorem reflTransGen_faceAdj_symm {B : Finset Face} {f g : Face}
    (h : Relation.ReflTransGen (FaceAdj B) f g) : Relation.ReflTransGen (FaceAdj B) g f := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head hstep.symm ih

/-- **ANY BOUNDARY FACE OF A CUBE REACHES A CHOSEN LOW FACE OF THAT CUBE**, in at most two hops. One
hop if the normals differ; two through the other low face if the face is the one OPPOSITE the target,
which is the only pair of a cube's faces that does not share an edge. -/
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

/-- The low face of `x_i` on axis `a` is on the boundary as soon as the path did not ENTER `x_i`
along `a`, and that condition only ever looks at the single step that arrives. -/
theorem low_hne_of (s : Fin k → Fin 3) {i : ℕ} {a : Fin 3}
    (h : ∀ (hk : i - 1 < k), 0 < i → s ⟨i - 1, hk⟩ ≠ a) :
    ∀ j : Fin k, (j : ℕ) + 1 = i → s j ≠ a := by
  intro j hj
  have h2 : i - 1 = (j : ℕ) := by omega
  have h3 : i - 1 < k := by rw [h2]; exact j.isLt
  have hres := h h3 (by omega)
  rwa [show (⟨i - 1, h3⟩ : Fin k) = j from Fin.ext h2] at hres

/-- **EVERY BOUNDARY FACE REACHES THE ORIGIN CUBE'S LOW FACE ON AXIS `0`.** Strong induction on the
index of a cube carrying the face: inside the cube, reach a low face whose axis is not the one the
path entered by; then cross the rung to the same low face of the previous cube, which exists because
two axes are not the entry axis and at most one of those is the previous entry axis. -/
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
      -- pick the rung axis: not the entry axis, and not the PREVIOUS entry axis
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

/-- **THE BOUNDARY OF A CUBE-PATH IS CONNECTED**, from the origin cube's low face on axis `0`. -/
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
