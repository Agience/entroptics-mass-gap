import MassGap.CubeClosed

/-!
# MassGap.CubeBranch — a branched family of cube configurations, counted and measured

`CubeArea` counts directed cube-paths: `3 ^ k` of them, each bounding a distinct face-set of
cardinality `4k + 6`. This module counts a larger family and measures it on the same scale.

## The family

`config d k σ τ` is a spine of `(d+1)k + 1` steps, given by the direction sequence `σ`, together with
one extra cube per block: in each of the `k` blocks of `d + 1` consecutive spine steps, the extra cube
hangs off the spine cube at position `τ m < d` inside the block, on the axis `branchDir` forces. The
parameter set is `(Fin ((d+1)k+1) → Fin 3) × (Fin k → Fin d)`, of cardinality
`3 ^ ((d+1)k+1) · d ^ k`.

`card_config` gives `(d+2)k + 2` cubes per member and `boundary_card_config` gives
`4((d+2)k+2) + 2` boundary faces.

## Why the area is `4n + 2`

`config_isTree` shows every cube but the origin is reached by exactly one step from exactly one other
cube of the configuration, so the configuration is an `IsCubeTree` and `card_sharedFaces_tree` makes
the shared-face count `n − 1`. `boundary_card_tree` then runs `CubeArea.boundary_card_of_shared`,
which is already stated for an arbitrary `Finset Cube`, giving `6n = |∂C| + 2(n−1)`, that is
`|∂C| = 4n + 2`. At a path, `n = k + 1` and this is `CubeArea.boundary_card_eq`'s `4k + 6`, so the
two families sit on the same area scale.

## The forced axis

`branchDir σ i` is `rot1 (spineDir σ i)` unless that equals `spineDir σ (i+1)`, in which case it is
`rot2 (spineDir σ i)`. The two facts the tree property needs follow with no case analysis on the
directions: `branchDir_ne_self` (from `rot1_ne`, `rot2_ne`) keeps the extra cube off the spine, and
`branchDir_ne_next` (from `rot1_ne_rot2`) stops the next spine cube from acquiring a second parent.
`branch_child_not_mem` and `no_two_parents` are where those are spent.

## Injectivity and the density

`eq_of_boundaryFaces_eq` shows the boundary map is injective on arbitrary configurations, with no
hypothesis — `CubeArea.boundaryFaces_cubeConfig_injective` freed of the path. `config_injective` then
recovers the parameters from the configuration, spine first (`top_unique`, `spine_eq_of_eq`,
`sigma_eq_of_eq`) and block positions second (`tau_eq_of_eq`), so
`branched_surfaces_count_and_area` counts distinct face-sets.

`branch_density_limit` computes `log(count)/area → ((d+1)log 3 + log d)/(4(d+2))` through
`tendsto_affine_ratio` and `log_branch_count`. `branch_density_gt_floor` proves that limit exceeds
`(1/4) log 3` exactly when `3 < d`; `branch_density_eq_floor_at_three` is the equality at `d = 3`,
and `branch_floor_ten` the instance at `d = 10`.

## Scope

`branched_surfaces_count_and_area` (count and cardinality), `branched_surfaces_closed` (every edge
lies in an even number of boundary faces) and `branched_origin_face_mem_boundary` are proved.
Connectedness of these face-sets is not: `CubeConnected.boundary_connected` descends on a path's own
indexing, which holds exactly one cube at each coordinate sum, and these configurations hold two at
the layers carrying an extra cube.

Everything is `Finset` combinatorics over `Fin 3 → ℕ`, plus real limits. No statement mentions a
vortex, an entropy density or a gap.

DERIVED throughout: `3` is the dimension and the step alphabet's arity, `6` the faces of a cube, `2`
the owners of a shared face, and `4 = 6 − 2` the area a one-parent cube adds. `d` and `k` are free
parameters: every `d` gives a theorem, and `3 < d` gives one whose density exceeds `(1/4) log 3`.
-/

namespace MassGap.CubeBranch

open Finset MassGap MassGap.CubeArea

/-! ### The boundary determines the configuration

`CubeArea.mem_of_boundary_eq_aux` recovers a cube-path from its boundary by an induction on the
path's own indexing. The same recovery holds for an arbitrary finite configuration and needs no
indexing: `CubeClosed.mem_boundaryFaces_iff_floor` decides membership on the floor `y 0 = 0`, and
`CubeClosed.mem_boundaryFaces_iff_xor` propagates it one step at a time. So two configurations with
the same boundary are equal, and any family counted by its cubes is counted by its boundaries. -/

/-- If two configurations have the same boundary, they agree on every cube of height `n` along axis
`0`. Induction on `n`: at `0` the two boundary criteria on the floor coincide, and at `n + 1` the
cube is a step along axis `0` from one of height `n`, where `mem_boundaryFaces_iff_xor` relates the
two memberships to the same boundary face.

DERIVED: `0` is the axis the induction runs along and the height of the base case; which axis is a
naming freedom. `3` is the dimension, carried by `Cube`. -/
theorem mem_iff_of_boundary_eq {C D : Finset Cube} (h : boundaryFaces C = boundaryFaces D) :
    ∀ n : ℕ, ∀ y : Cube, y 0 = n → (y ∈ C ↔ y ∈ D) := by
  intro n
  induction n with
  | zero =>
    intro y hy
    rw [← mem_boundaryFaces_iff_floor C 0 y hy, ← mem_boundaryFaces_iff_floor D 0 y hy, h]
  | succ m ih =>
    intro y hy
    obtain ⟨p, hp0, hstep⟩ : ∃ p : Cube, p 0 = m ∧ step 0 p = y := by
      refine ⟨fun c => if c = 0 then m else y c, by simp, ?_⟩
      funext c
      by_cases hc : c = 0
      · subst hc
        rw [step_self]
        simp [hy]
      · rw [step_other hc]
        simp [hc]
    have hC := mem_boundaryFaces_iff_xor C 0 p
    have hD := mem_boundaryFaces_iff_xor D 0 p
    rw [hstep] at hC hD
    have hpi := ih p hp0
    have hb : ((0 : Fin 3), y) ∈ boundaryFaces C ↔ ((0 : Fin 3), y) ∈ boundaryFaces D := by rw [h]
    tauto

/-- `boundaryFaces C = boundaryFaces D → C = D`, for arbitrary `Finset Cube`s.
`mem_iff_of_boundary_eq` at each cube's own height along axis `0`.

No hypothesis on the configurations: `CubeArea.boundaryFaces_cubeConfig_injective` freed of the path.

DERIVED: `0` is the axis `mem_iff_of_boundary_eq` runs along; `3` is the dimension. -/
theorem eq_of_boundaryFaces_eq {C D : Finset Cube} (h : boundaryFaces C = boundaryFaces D) :
    C = D := by
  ext y
  exact mem_iff_of_boundary_eq h (y 0) y rfl

#print axioms eq_of_boundaryFaces_eq

/-! ### Trees, and why a tree's area is `4n+2` -/

/-- A `Prop`-valued structure on a `Finset Cube` and a cube `r`: `r` is in the configuration, nothing
in the configuration steps into `r`, every other cube of it is stepped into from inside it, and a
cube of it has at most one parent in it.

A directed cube-path is the case with a single leaf; `config_isTree` proves the branched family
satisfies it.

DERIVED: `3` is the dimension, the range of the step axes; no other numeral. -/
structure IsCubeTree (C : Finset Cube) (r : Cube) : Prop where
  /-- the root is in the configuration -/
  root_mem : r ∈ C
  /-- nothing in the configuration steps into the root -/
  root_no_parent : ∀ (a : Fin 3) (p : Cube), p ∈ C → step a p ≠ r
  /-- every other cube is stepped into from inside the configuration -/
  parent_exists : ∀ c ∈ C, c ≠ r → ∃ (a : Fin 3) (p : Cube), p ∈ C ∧ step a p = c
  /-- and only once: a cube of the configuration has at most one parent in it -/
  parent_unique : ∀ (a b : Fin 3) (p q : Cube), p ∈ C → q ∈ C → step a p ∈ C →
      step a p = step b q → a = b ∧ p = q

/-- The faces of `C` carried by exactly two cubes: the interior ones. The same filter
`CubeArea.sharedFaces_eq_crossFaces` uses, named here for an arbitrary configuration.

DERIVED: `2` is the number of cubes a face can belong to
(`CubeArea.card_cubes_with_face_le_two`), so "two owners" is the complement of "on the boundary" and
not a chosen cut. `3` is the dimension. -/
noncomputable def sharedFaces (C : Finset Cube) : Finset Face :=
  (C.biUnion faces).filter (fun f => (C.filter (fun x => f ∈ faces x)).card = 2)

/-- A shared face has both of its possible owners in `C`: the corner `f.2` itself, and some `p ∈ C`
with `step f.1 p = f.2`. Each half by contradiction — without one of them the owner set would have at
most one element, against the shared face's count of two.

DERIVED: `2` is the owner count of a shared face, `sharedFaces`'s; `1` is the bound the contradiction
derives. `3` is the dimension, and the `1`, `2` in `f.1`, `f.2` are `Face`'s projections. -/
theorem shared_owners {C : Finset Cube} {f : Face} (hf : f ∈ sharedFaces C) :
    f.2 ∈ C ∧ ∃ p ∈ C, step f.1 p = f.2 := by
  classical
  rw [sharedFaces, Finset.mem_filter] at hf
  have hcard := hf.2
  constructor
  · by_contra hn
    have hsub : C.filter (fun x => f ∈ faces x) ⊆ C.filter (fun x => step f.1 x = f.2) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      rcases cube_of_face hx.2 with h | h
      · exact absurd (h ▸ hx.1) hn
      · exact ⟨hx.1, h⟩
    have h1 : (C.filter (fun x => step f.1 x = f.2)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_filter] at ha hb
      exact step_injective f.1 (ha.2.trans hb.2.symm)
    have := Finset.card_le_card hsub
    omega
  · by_contra hn
    push_neg at hn
    have hsub : C.filter (fun x => f ∈ faces x) ⊆ {f.2} := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rcases cube_of_face hx.2 with h | h
      · exact Finset.mem_singleton.mpr h
      · exact absurd h (hn x hx.1)
    have hle := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hle
    omega

/-- For an `IsCubeTree C r`, `(sharedFaces C).card + 1 = C.card`.

The map `f ↦ f.2` is a bijection from the shared faces onto `C.erase r`: a shared face names a cube
of `C` together with its parent (`shared_owners`), and `root_no_parent` keeps it off the root; the
cube determines the face because `parent_unique` fixes the axis; and every non-root cube is hit
because `parent_exists` gives it a parent, whose shared face has two owners by
`card_cubes_with_face_le_two` and `ne_step`.

DERIVED: `1` is the single cube — the root — that the shared faces do not name, so the count is one
short of the cube count. `2` is the owner count of a shared face; `3` is the dimension. -/
theorem card_sharedFaces_tree {C : Finset Cube} {r : Cube} (h : IsCubeTree C r) :
    (sharedFaces C).card + 1 = C.card := by
  classical
  have hbij : (sharedFaces C).card = (C.erase r).card := by
    refine Finset.card_bij (fun f _ => f.2) ?_ ?_ ?_
    · intro f hf
      obtain ⟨hf2, p, hp, hstep⟩ := shared_owners hf
      refine Finset.mem_erase.mpr ⟨?_, hf2⟩
      intro hfr
      exact h.root_no_parent f.1 p hp (by rw [hstep, hfr])
    · intro f hf g hg hfg
      obtain ⟨hf2, p, hp, hpstep⟩ := shared_owners hf
      obtain ⟨hg2, q, hq, hqstep⟩ := shared_owners hg
      have hin : step f.1 p ∈ C := by rw [hpstep]; exact hf2
      have heq : step f.1 p = step g.1 q := by rw [hpstep, hqstep, hfg]
      obtain ⟨ha, _⟩ := h.parent_unique f.1 g.1 p q hp hq hin heq
      exact Prod.ext ha hfg
    · intro c hc
      obtain ⟨hcr, hcC⟩ := Finset.mem_erase.mp hc
      obtain ⟨a, p, hp, hstep⟩ := h.parent_exists c hcC hcr
      refine ⟨(a, c), ?_, rfl⟩
      rw [sharedFaces, Finset.mem_filter]
      have hfc : ((a, c) : Face) ∈ faces c := mem_faces.mpr ⟨a, Or.inl rfl⟩
      have hfp : ((a, c) : Face) ∈ faces p := mem_faces.mpr ⟨a, Or.inr (by rw [hstep])⟩
      refine ⟨Finset.mem_biUnion.mpr ⟨c, hcC, hfc⟩, ?_⟩
      have hne : c ≠ p := by
        intro hh
        exact ne_step a p (hstep.trans hh).symm
      have hlow : 1 < (C.filter (fun x => ((a, c) : Face) ∈ faces x)).card :=
        Finset.one_lt_card.mpr ⟨c, Finset.mem_filter.mpr ⟨hcC, hfc⟩, p,
          Finset.mem_filter.mpr ⟨hp, hfp⟩, hne⟩
      have hhigh := card_cubes_with_face_le_two C ((a, c) : Face)
      omega
  rw [hbij, Finset.card_erase_of_mem h.root_mem]
  have hpos : 1 ≤ C.card := Finset.card_pos.mpr ⟨r, h.root_mem⟩
  omega

/-- For an `IsCubeTree C r`, `(boundaryFaces C).card = 4 * C.card + 2`.

`CubeArea.boundary_card_of_shared` gives `6n = |B| + (n−1)` using `card_sharedFaces_tree`, and
splitting `B` into one-owner and two-owner faces drops the shared ones once more, so
`|∂C| = |B| − (n−1) = 6n − 2(n−1) = 4n + 2`.

At a directed path `n = k + 1` and this is `CubeArea.boundary_card_eq`'s `4k + 6`, so the two
families sit on the same area scale.

DERIVED: `4` is `6 − 2`, the faces of a cube less twice the one shared with its parent; `2` is
`2 · 1`, twice the root's missing parent, so it is `card_sharedFaces_tree`'s `1` doubled. Neither is
chosen. `3` is the dimension. -/
theorem boundary_card_tree {C : Finset Cube} {r : Cube} (h : IsCubeTree C r) :
    (boundaryFaces C).card = 4 * C.card + 2 := by
  classical
  have hshared := card_sharedFaces_tree h
  have hdc : ∑ x ∈ C, (faces x).card = (C.biUnion faces).card + (sharedFaces C).card :=
    boundary_card_of_shared C _ (fun f hf => by have := owners_one_or_two C hf; omega) rfl
  have hleft : ∑ x ∈ C, (faces x).card = 6 * C.card := by
    rw [Finset.sum_congr rfl (fun x _ => card_faces x), Finset.sum_const, smul_eq_mul,
      Nat.mul_comm]
  have hsplit : (boundaryFaces C).card + (sharedFaces C).card = (C.biUnion faces).card := by
    have h1 : ((C.biUnion faces).filter
          (fun f => (C.filter (fun x => f ∈ faces x)).card = 1)).card
        + ((C.biUnion faces).filter
          (fun f => ¬ (C.filter (fun x => f ∈ faces x)).card = 1)).card
        = (C.biUnion faces).card :=
      Finset.filter_card_add_filter_neg_card_eq_card _
    have hflip : (C.biUnion faces).filter (fun f => ¬ (C.filter (fun x => f ∈ faces x)).card = 1)
        = sharedFaces C := by
      rw [sharedFaces]
      refine Finset.filter_congr (fun f hf => ?_)
      have := owners_one_or_two C hf
      constructor
      · intro hh; omega
      · intro hh; omega
    rw [hflip] at h1
    rw [boundaryFaces]
    exact h1
  omega

#print axioms card_sharedFaces_tree
#print axioms boundary_card_tree

/-! ### Reading one coordinate of a step -/

/-- `step a x c = x c + (if c = a then 1 else 0)`: a step raises exactly its own coordinate, by one.
Case split on `c = a`.

DERIVED: `1` is the unit lattice step, `step`'s increment, and `0` the increment on every other
coordinate. `3` is the dimension. -/
theorem step_val (a : Fin 3) (x : Cube) (c : Fin 3) :
    step a x c = x c + (if c = a then 1 else 0) := by
  by_cases h : c = a
  · subst h; simp [step_self]
  · simp [step_other h, h]

/-- If `step a (step u x) = step b (step w x)` with `w ≠ u`, then `a = w` and `b = u`, so the common
cube is `x` raised by one on each of the two axes. Reading the `w` and `u` coordinates of both sides
through `step_val` forces each equality in turn.

This is the only shape in which a cube could be reached from two different parents two steps from a
common cube; `branch_child_not_mem` shows that cube is absent from the configuration.

DERIVED: `3` is the dimension; the unit steps are inside `step` and the statement carries no
literal. -/
theorem step_pair_eq {x : Cube} {u w a b : Fin 3} (hwu : w ≠ u)
    (h : step a (step u x) = step b (step w x)) : a = w ∧ b = u := by
  have hw : x w + (if w = a then 1 else 0) = x w + 1 + (if w = b then 1 else 0) := by
    have h1 : step a (step u x) w = x w + (if w = a then 1 else 0) := by
      rw [step_val, step_other hwu]
    have h2 : step b (step w x) w = x w + 1 + (if w = b then 1 else 0) := by
      rw [step_val, step_self]
    rw [← h1, ← h2, h]
  have haw : a = w := by
    by_contra hne
    rw [if_neg (fun hh : w = a => hne hh.symm)] at hw
    split_ifs at hw <;> omega
  refine ⟨haw, ?_⟩
  have hu : x u + 1 + (if u = a then 1 else 0) = x u + (if u = b then 1 else 0) := by
    have h1 : step a (step u x) u = x u + 1 + (if u = a then 1 else 0) := by
      rw [step_val, step_self]
    have h2 : step b (step w x) u = x u + (if u = b then 1 else 0) := by
      rw [step_val, step_other (Ne.symm hwu)]
    rw [← h1, ← h2, h]
  by_contra hne
  have h1 : ¬ (u = a) := by rw [haw]; exact fun hh => hwu hh.symm
  have h2 : ¬ (u = b) := fun hh => hne hh.symm
  rw [if_neg h1, if_neg h2] at hu
  omega

/-! ### The family: a spine with one extra cube per block -/

/-- The spine direction at step `j`, total in `j`: `σ ⟨j, h⟩` when `j < N`, and `0` otherwise.

The value past the end is never read — `spineDir_lt` is the only fact used of it and speaks about
indices inside the range.

DERIVED: `0` is `Fin 3`'s first element, standing in past the end of the range, not a magnitude. `3`
is the dimension, the arity of the step alphabet. -/
def spineDir {N : ℕ} (σ : Fin N → Fin 3) (j : ℕ) : Fin 3 :=
  if h : j < N then σ ⟨j, h⟩ else 0

/-- `spineDir σ j = σ ⟨j, h⟩` when `j < N`: the `dif_pos` branch of the definition.

DERIVED: `3` is the dimension; no numeral of this declaration's own. -/
theorem spineDir_lt {N : ℕ} (σ : Fin N → Fin 3) {j : ℕ} (h : j < N) :
    spineDir σ j = σ ⟨j, h⟩ := dif_pos h

/-- The axis the extra cube hangs on at spine index `i`: `rot1 (spineDir σ i)`, unless that equals
`spineDir σ (i+1)`, in which case `rot2 (spineDir σ i)`.

The two facts the tree property needs follow with no case analysis on the directions:
`branchDir_ne_self` from `rot1_ne` and `rot2_ne`, `branchDir_ne_next` from `rot1_ne_rot2`.

DERIVED: `1` is one spine step ahead — the extra cube and the next spine cube share a coordinate sum,
so the next direction is what this axis must avoid. `3` is the dimension. -/
def branchDir {N : ℕ} (σ : Fin N → Fin 3) (i : ℕ) : Fin 3 :=
  if rot1 (spineDir σ i) = spineDir σ (i + 1) then rot2 (spineDir σ i) else rot1 (spineDir σ i)

/-- `branchDir σ i ≠ spineDir σ i`: the extra cube's axis differs from the spine's own, by `rot1_ne`
on one branch and `rot2_ne` on the other. This is what keeps the extra cube off the spine.

DERIVED: `3` is the dimension; no numeral of this declaration's own. -/
theorem branchDir_ne_self {N : ℕ} (σ : Fin N → Fin 3) (i : ℕ) :
    branchDir σ i ≠ spineDir σ i := by
  rw [branchDir]
  split_ifs with h
  · exact rot2_ne _
  · exact rot1_ne _

/-- `branchDir σ i ≠ spineDir σ (i + 1)`: the extra cube's axis differs from the next spine
direction. On the `rot2` branch this is `rot1_ne_rot2`; on the other it is the branch condition
itself. This is what stops the next spine cube from acquiring a second parent.

DERIVED: `1` is one spine step ahead, `branchDir`'s own; `3` is the dimension. -/
theorem branchDir_ne_next {N : ℕ} (σ : Fin N → Fin 3) (i : ℕ) :
    branchDir σ i ≠ spineDir σ (i + 1) := by
  rw [branchDir]
  split_ifs with h
  · rw [← h]; exact (rot1_ne_rot2 _).symm
  · exact h

/-- The extra cube hung on the spine at index `i`: `step (branchDir σ i) (cubePos σ i)`, one step off
the spine cube on the forced axis.

DERIVED: `3` is `Cube`'s dimension, the step alphabet `Floor.directed_paths_card` counts over. The
unit step is `CubeArea.step`'s; this definition introduces no numeral. -/
noncomputable def branchCube {N : ℕ} (σ : Fin N → Fin 3) (i : ℕ) : Cube :=
  step (branchDir σ i) (cubePos σ i)

/-- The spine index the `m`-th block's extra cube hangs on: `(d + 1) * m + τ m`.

DERIVED: `1` makes the block's length `d + 1` spine steps, so the `m`-th block starts at `(d+1)m`;
the extra `+1` step is what leaves the top layer to the spine alone (`top_unique`). The position
`τ m < d` inside the block is the family's parameter, and the `d` choices are what `d ^ k` counts. -/
def branchIdx (d : ℕ) {k : ℕ} (τ : Fin k → Fin d) (m : Fin k) : ℕ :=
  (d + 1) * (m : ℕ) + (τ m : ℕ)

/-- The configuration: the spine `cubeConfig σ`, which has `(d+1)k + 2` cubes, united with the image
of the `k` extra cubes, one per block. `card_config` evaluates the total as `(d+2)k + 2`.

DERIVED: `3` is `Cube`'s dimension. `1` appears twice in `(d + 1) * k + 1`: as the block length
`d + 1` in spine steps, so that `k` blocks take `(d+1)k` of them, and as the one further step that
leaves the top layer to the spine alone (`top_unique`), which is what makes the spine recoverable. -/
noncomputable def config (d k : ℕ) (σ : Fin ((d + 1) * k + 1) → Fin 3) (τ : Fin k → Fin d) :
    Finset Cube :=
  cubeConfig σ ∪ (Finset.univ.image (fun m => branchCube σ (branchIdx d τ m)))

/-! ### Where the extra cubes sit -/

/-- For `a < k` and `u < d`, `(d + 1) * a + u + 2 ≤ (d + 1) * k`: the extra cube of a block, and the
spine cube after it, still leave room below the top.

DERIVED: `1` is the block length's `+1`, `branchIdx`'s; `2` is the extra cube plus the spine cube
one step on, the two positions that must stay below the top. -/
theorem idx_top (d : ℕ) {k a u : ℕ} (ha : a < k) (hu : u < d) :
    (d + 1) * a + u + 2 ≤ (d + 1) * k := by
  have h1 : (d + 1) * (a + 1) ≤ (d + 1) * k := Nat.mul_le_mul (le_refl _) ha
  rw [Nat.mul_succ] at h1
  omega

/-- For `u < d` and `a < b`, `(d + 1) * a + u + 2 ≤ (d + 1) * b + v`: two extra cubes in different
blocks are at least two spine steps apart, whatever position `v` the later one takes.

This is what keeps one block's extra cube from interfering with the next block's.

DERIVED: `1` is the block length's `+1`; `2` is the gap in spine steps the block structure
guarantees, which is what `branch_child_not_mem` spends. -/
theorem idx_gap (d a b u v : ℕ) (hu : u < d) (hab : a < b) :
    (d + 1) * a + u + 2 ≤ (d + 1) * b + v := by
  have h1 : (d + 1) * (a + 1) ≤ (d + 1) * b := Nat.mul_le_mul (le_refl _) hab
  rw [Nat.mul_succ] at h1
  omega

/-- `branchIdx d τ m + 2 ≤ (d + 1) * k`: every extra cube's spine index leaves two steps below the
top. `idx_top` at `m.2` and `(τ m).2`.

DERIVED: `2` is the extra cube plus the spine cube one step on, `idx_top`'s; `1` is the block
length's `+1`. -/
theorem branchIdx_top (d : ℕ) {k : ℕ} (τ : Fin k → Fin d) (m : Fin k) :
    branchIdx d τ m + 2 ≤ (d + 1) * k :=
  idx_top d m.2 (τ m).2

/-- Equal spine indices force equal block indices and equal positions inside the block. Trichotomy on
the block indices, with `idx_gap` ruling out both strict cases and `omega` splitting the remaining
equality.

So the block and the position are recoverable from `branchIdx`, which is what `branchCube_inj` and
`tau_eq_of_eq` consume.

DERIVED: `1` is the block length's `+1`, `branchIdx`'s; no other numeral. -/
theorem branchIdx_eq (d : ℕ) {k : ℕ} (τ τ' : Fin k → Fin d) {m m' : Fin k}
    (h : branchIdx d τ m = branchIdx d τ' m') : m = m' ∧ (τ m : ℕ) = (τ' m' : ℕ) := by
  rw [branchIdx, branchIdx] at h
  rcases lt_trichotomy (m : ℕ) (m' : ℕ) with hlt | heq | hgt
  · exact absurd h (by have := idx_gap d m m' (τ m) (τ' m') (τ m).2 hlt; omega)
  · refine ⟨Fin.ext heq, ?_⟩
    rw [heq] at h
    omega
  · exact absurd h (by have := idx_gap d m' m (τ' m') (τ m) (τ' m').2 hgt; omega)

/-! ### Levels: the coordinate sum names the layer -/

/-- `∑ a, branchCube σ i a = i + 1`: the extra cube at spine index `i` sits one layer above the spine
cube there. `sum_step` on `Floor.cubePos_sum_le`.

DERIVED: `1` is the one step the extra cube hangs by, `sum_step`'s; `3` is the dimension. -/
theorem sum_branchCube {N : ℕ} (σ : Fin N → Fin 3) {i : ℕ} (hi : i ≤ N) :
    ∑ a, branchCube σ i a = i + 1 := by
  rw [branchCube, sum_step, cubePos_sum_le σ hi]

/-- `cubePos σ (j + 1) = step (spineDir σ j) (cubePos σ j)` for `j < N`: the spine cube one step on,
written as a step. `spineDir_lt` followed by `CubeArea.cubePos_succ_eq_step`.

DERIVED: `1` is the index increment, one spine step; `3` is the dimension. -/
theorem spine_succ {N : ℕ} (σ : Fin N → Fin 3) {j : ℕ} (h : j < N) :
    cubePos σ (j + 1) = step (spineDir σ j) (cubePos σ j) := by
  rw [spineDir_lt σ h]
  exact cubePos_succ_eq_step σ ⟨j, h⟩

/-- `branchCube σ i ≠ cubePos σ j`: no extra cube is a spine cube. The coordinate sums force
`j = i + 1`, and both cubes are then one step from `cubePos σ i` on axes that
`branchDir_ne_self` separates, so `step_axis_inj` gives the contradiction.

DERIVED: `1` is the layer the extra cube sits above its spine cube, from `sum_branchCube`; `3` is the
dimension. -/
theorem branchCube_ne_cubePos {N : ℕ} (σ : Fin N → Fin 3) {i j : ℕ} (hi : i + 1 ≤ N) (hj : j ≤ N) :
    branchCube σ i ≠ cubePos σ j := by
  intro hEq
  have hlvl : i + 1 = j := by
    have h1 := sum_branchCube σ (Nat.le_of_succ_le hi)
    have h2 := cubePos_sum_le σ hj
    rw [hEq, h2] at h1
    omega
  subst hlvl
  rw [branchCube, spine_succ σ (Nat.lt_of_succ_le hi)] at hEq
  exact branchDir_ne_self σ i (step_axis_inj hEq)

/-- Membership in `config d k σ τ` unfolded: `y` is a spine cube at some index at most
`(d+1)k + 1`, or the extra cube of some block. `Finset.mem_union` and `Finset.mem_image` on both
sides.

DERIVED: `1` is the block length's `+1` and the extra top spine step, `config`'s; `3` is the
dimension. -/
theorem mem_config_iff (d k : ℕ) (σ : Fin ((d + 1) * k + 1) → Fin 3) (τ : Fin k → Fin d)
    (y : Cube) :
    y ∈ config d k σ τ ↔
      (∃ j, j ≤ (d + 1) * k + 1 ∧ cubePos σ j = y)
        ∨ (∃ m : Fin k, branchCube σ (branchIdx d τ m) = y) := by
  classical
  rw [config, Finset.mem_union, cubeConfig, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro (⟨j, hj, hy⟩ | ⟨m, -, hy⟩)
    · exact Or.inl ⟨j, Nat.lt_succ_iff.mp (Finset.mem_range.mp hj), hy⟩
    · exact Or.inr ⟨m, hy⟩
  · rintro (⟨j, hj, hy⟩ | ⟨m, hy⟩)
    · exact Or.inl ⟨j, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj), hy⟩
    · exact Or.inr ⟨m, Finset.mem_univ m, hy⟩

/-- Every cube of the configuration has coordinate sum at most `(d+1)k + 1`, and is either the spine
cube at that sum or the extra cube of some block hanging one step above its spine index.
`mem_config_iff` with the coordinate sum evaluated by `Floor.cubePos_sum_le` or `sum_branchCube`.

The coordinate sum names the layer, which is what `config_isTree` and `top_unique` use to compare
cubes without an indexing.

DERIVED: `1` is the block length's `+1` and the extra top spine step, and separately the one layer
the extra cube sits above its spine index; `3` is the dimension. -/
theorem config_cases (d k : ℕ) (σ : Fin ((d + 1) * k + 1) → Fin 3) (τ : Fin k → Fin d) {y : Cube}
    (hy : y ∈ config d k σ τ) :
    (∑ a, y a) ≤ (d + 1) * k + 1 ∧
      (cubePos σ (∑ a, y a) = y ∨
        ∃ m : Fin k, branchCube σ (branchIdx d τ m) = y ∧ branchIdx d τ m + 1 = ∑ a, y a) := by
  rcases (mem_config_iff d k σ τ y).mp hy with ⟨j, hj, hyj⟩ | ⟨m, hym⟩
  · have hs : ∑ a, y a = j := by rw [← hyj]; exact cubePos_sum_le σ hj
    rw [hs]
    exact ⟨hj, Or.inl hyj⟩
  · have htop := branchIdx_top d τ m
    have hle : branchIdx d τ m ≤ (d + 1) * k + 1 := by omega
    have hs : ∑ a, y a = branchIdx d τ m + 1 := by
      rw [← hym]; exact sum_branchCube σ hle
    rw [hs]
    exact ⟨by omega, Or.inr ⟨m, hym, rfl⟩⟩

/-- `step (branchDir σ (branchIdx d τ m)) (cubePos σ (branchIdx d τ m + 1)) ∉ config d k σ τ`: the
cube that would be reachable both from the spine and from a block's extra cube is absent.

Its coordinate sum is `branchIdx d τ m + 2`, so `config_cases` leaves two possibilities: the spine
cube at that layer, which `branchDir_ne_next` and `step_axis_inj` exclude, or another block's extra
cube, which `idx_gap` excludes because blocks are two spine steps apart.

DERIVED: `2` is the layer above the extra cube's spine index and the block gap, `idx_gap`'s; `1` is
the block length's `+1` and the single spine step; `3` is the dimension. -/
theorem branch_child_not_mem (d k : ℕ) (σ : Fin ((d + 1) * k + 1) → Fin 3) (τ : Fin k → Fin d)
    (m : Fin k) :
    step (branchDir σ (branchIdx d τ m)) (cubePos σ (branchIdx d τ m + 1)) ∉ config d k σ τ := by
  intro hmem
  have htop := branchIdx_top d τ m
  have hle1 : branchIdx d τ m + 1 ≤ (d + 1) * k + 1 := by omega
  have hlt1 : branchIdx d τ m + 1 < (d + 1) * k + 1 := by omega
  have hsum : ∑ a, step (branchDir σ (branchIdx d τ m)) (cubePos σ (branchIdx d τ m + 1)) a
      = branchIdx d τ m + 2 := by
    rw [sum_step, cubePos_sum_le σ hle1]
  obtain ⟨-, hcase⟩ := config_cases d k σ τ hmem
  rw [hsum] at hcase
  rcases hcase with hspine | ⟨m', hm', hlvl'⟩
  · rw [spine_succ σ hlt1] at hspine
    exact branchDir_ne_next σ (branchIdx d τ m) (step_axis_inj hspine).symm
  · have hidx : branchIdx d τ m' = branchIdx d τ m + 1 := by omega
    rcases eq_or_ne m' m with rfl | hne
    · omega
    · rcases lt_or_gt_of_ne (fun hh : (m' : ℕ) = (m : ℕ) => hne (Fin.ext hh)) with hlt | hgt
      · have := idx_gap d m' m (τ m') (τ m) (τ m').2 hlt
        rw [branchIdx, branchIdx] at hidx
        omega
      · have := idx_gap d m m' (τ m) (τ m') (τ m).2 hgt
        rw [branchIdx, branchIdx] at hidx
        omega

/-! ### The configuration is a tree -/

/-- `cubePos σ 0 ∈ config d k σ τ`: the origin cube is in every member of the family, being the spine
cube at index `0`.

DERIVED: `0` is the spine index of the origin, `Floor.cubePos`'s base point; `1` is `config`'s block
length and top step; `3` is the dimension. -/
theorem config_root_mem (d k : ℕ) (σ : Fin ((d + 1) * k + 1) → Fin 3) (τ : Fin k → Fin d) :
    cubePos σ 0 ∈ config d k σ τ := by
  rw [mem_config_iff]
  exact Or.inl ⟨0, Nat.zero_le _, rfl⟩

/-- The one pair of cubes that could share a child — the spine cube one step past a block's index and
that block's extra cube — does not: if their steps agree and the common child is in the
configuration, `step_pair_eq` and `branchDir_ne_self` identify the child as
`branch_child_not_mem`'s, which is absent.

DERIVED: `1` is the single spine step past the block index, and `config`'s block length and top step;
`3` is the dimension. -/
theorem no_two_parents (d k : ℕ) (σ : Fin ((d + 1) * k + 1) → Fin 3) (τ : Fin k → Fin d)
    (m : Fin k) {a b : Fin 3}
    (heq : step a (cubePos σ (branchIdx d τ m + 1)) = step b (branchCube σ (branchIdx d τ m)))
    (hin : step a (cubePos σ (branchIdx d τ m + 1)) ∈ config d k σ τ) : False := by
  have htop := branchIdx_top d τ m
  have hlt : branchIdx d τ m < (d + 1) * k + 1 := by omega
  have hp := spine_succ σ hlt
  rw [hp, branchCube] at heq
  obtain ⟨haw, -⟩ := step_pair_eq (branchDir_ne_self σ (branchIdx d τ m)) heq
  rw [haw] at hin
  exact branch_child_not_mem d k σ τ m hin

/-- `IsCubeTree (config d k σ τ) (cubePos σ 0)`: all four fields.

The root has no parent because a step raises the coordinate sum above `0`. Every other cube has one:
a spine cube from the previous spine cube, an extra cube from its own spine cube. Uniqueness splits
on `config_cases` for both candidate parents — two spine cubes coincide by layer, two extra cubes by
`branchIdx`, and the mixed cases are `no_two_parents`.

The forced axis (`branchDir_ne_self`, `branchDir_ne_next`) and the two-step block gap (`idx_gap`) are
what the mixed cases spend.

DERIVED: `0` is the root's spine index and the coordinate sum there; `1` is `config`'s block length
and top step; `3` is the dimension. -/
theorem config_isTree (d k : ℕ) (σ : Fin ((d + 1) * k + 1) → Fin 3) (τ : Fin k → Fin d) :
    IsCubeTree (config d k σ τ) (cubePos σ 0) := by
  refine ⟨config_root_mem d k σ τ, ?_, ?_, ?_⟩
  · intro a p _ hcontra
    have h0 : ∑ b, cubePos σ 0 b = 0 := cubePos_sum_le σ (Nat.zero_le _)
    have h1 : ∑ b, step a p b = (∑ b, p b) + 1 := sum_step a p
    rw [hcontra, h0] at h1
    omega
  · intro c hc hcr
    rcases (mem_config_iff d k σ τ c).mp hc with ⟨j, hj, hcj⟩ | ⟨m, hcm⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · exact absurd hcj.symm hcr
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        refine ⟨spineDir σ j', cubePos σ j', ?_, ?_⟩
        · rw [mem_config_iff]; exact Or.inl ⟨j', by omega, rfl⟩
        · rw [← hcj]; exact (spine_succ σ (by omega)).symm
    · have htop := branchIdx_top d τ m
      refine ⟨branchDir σ (branchIdx d τ m), cubePos σ (branchIdx d τ m), ?_, ?_⟩
      · rw [mem_config_iff]; exact Or.inl ⟨branchIdx d τ m, by omega, rfl⟩
      · rw [← hcm, branchCube]
  · intro a b p q hp hq hin heq
    obtain ⟨-, hpc⟩ := config_cases d k σ τ hp
    obtain ⟨-, hqc⟩ := config_cases d k σ τ hq
    have hlvl : (∑ x, p x) = (∑ x, q x) := by
      have h1 := sum_step a p
      have h2 := sum_step b q
      rw [heq] at h1
      omega
    rcases hpc with hps | ⟨mp, hmp, hlp⟩ <;> rcases hqc with hqs | ⟨mq, hmq, hlq⟩
    · have hpq : p = q := hps.symm.trans (by rw [hlvl]; exact hqs)
      subst hpq
      exact ⟨step_axis_inj heq, rfl⟩
    · exfalso
      have hpe : p = cubePos σ (branchIdx d τ mq + 1) := by
        rw [← hps, hlvl, hlq]
      rw [hpe] at heq hin
      rw [← hmq] at heq
      exact no_two_parents d k σ τ mq heq hin
    · exfalso
      have hqe : q = cubePos σ (branchIdx d τ mp + 1) := by
        rw [← hqs, ← hlvl, hlp]
      rw [hqe] at heq
      rw [← hmp] at heq hin
      exact no_two_parents d k σ τ mp heq.symm (heq ▸ hin)
    · have hidx : branchIdx d τ mp = branchIdx d τ mq := by omega
      have hpq : p = q := by rw [← hmp, ← hmq, hidx]
      subst hpq
      exact ⟨step_axis_inj heq, rfl⟩

#print axioms config_isTree

/-! ### How many cubes, and how much area -/

/-- `fun m => branchCube σ (branchIdx d τ m)` is injective on `Fin k`: equal extra cubes have equal
coordinate sums, hence equal spine indices by `sum_branchCube`, hence equal blocks by
`branchIdx_eq`.

DERIVED: `1` is `config`'s block length and top step; `3` is the dimension. -/
theorem branchCube_inj (d k : ℕ) (σ : Fin ((d + 1) * k + 1) → Fin 3) (τ : Fin k → Fin d) :
    Function.Injective (fun m : Fin k => branchCube σ (branchIdx d τ m)) := by
  intro m m' hmm
  simp only at hmm
  have htop := branchIdx_top d τ m
  have htop' := branchIdx_top d τ m'
  have h1 := sum_branchCube σ (show branchIdx d τ m ≤ (d + 1) * k + 1 by omega)
  have h2 := sum_branchCube σ (show branchIdx d τ m' ≤ (d + 1) * k + 1 by omega)
  rw [hmm, h2] at h1
  exact (branchIdx_eq d τ τ (show branchIdx d τ m = branchIdx d τ m' by omega)).1

/-- `(config d k σ τ).card = (d + 2) * k + 2`: the `(d+1)k + 2` spine cubes and the `k` extra ones,
the union disjoint by `branchCube_ne_cubePos` and the second summand counted by `branchCube_inj`.

DERIVED: `2` in `(d + 2)` is `(d + 1) + 1`, the block's spine cubes plus its extra cube, so it is
`branchIdx`'s block length raised by the one extra cube. The trailing `2` is `config`'s two spine
cubes above the last block — the top step and its endpoint. `1` is the block length's `+1`; `3` is
the dimension. -/
theorem card_config (d k : ℕ) (σ : Fin ((d + 1) * k + 1) → Fin 3) (τ : Fin k → Fin d) :
    (config d k σ τ).card = (d + 2) * k + 2 := by
  classical
  have hdisj : Disjoint (cubeConfig σ)
      (Finset.univ.image (fun m : Fin k => branchCube σ (branchIdx d τ m))) := by
    rw [Finset.disjoint_right]
    intro y hy hy2
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hy
    rw [cubeConfig, Finset.mem_image] at hy2
    obtain ⟨j, hj, hji⟩ := hy2
    have htop := branchIdx_top d τ m
    exact branchCube_ne_cubePos σ (by omega)
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hji.symm
  rw [config, Finset.card_union_of_disjoint hdisj, card_cubeConfig,
    Finset.card_image_of_injective _ (branchCube_inj d k σ τ), Finset.card_univ,
    Fintype.card_fin]
  ring

/-- `(boundaryFaces (config d k σ τ)).card = 4 * ((d + 2) * k + 2) + 2`: `boundary_card_tree` at
`config_isTree`, with the cube count from `card_config`.

DERIVED: `4` and the trailing `2` are `boundary_card_tree`'s — six faces per cube less twice the one
shared with a parent, and twice the root's missing parent. `(d + 2) * k + 2` is `card_config`'s cube
count. `1` is `config`'s block length; `3` is the dimension. -/
theorem boundary_card_config (d k : ℕ) (σ : Fin ((d + 1) * k + 1) → Fin 3) (τ : Fin k → Fin d) :
    (boundaryFaces (config d k σ τ)).card = 4 * ((d + 2) * k + 2) + 2 := by
  rw [boundary_card_tree (config_isTree d k σ τ), card_config]

/-! ### Distinct parameters give distinct surfaces -/

/-- A cube of the configuration whose coordinate sum is `(d+1)k + 1` is the top spine cube: by
`config_cases` the only alternative is an extra cube, and `branchIdx_top` puts every one of those at
least two layers lower.

This is what makes the spine recoverable from the cube set, top down.

DERIVED: `1` is `config`'s block length and its top spine step, the latter being what leaves this
layer to the spine alone; `3` is the dimension. -/
theorem top_unique (d k : ℕ) (σ : Fin ((d + 1) * k + 1) → Fin 3) (τ : Fin k → Fin d) {y : Cube}
    (hy : y ∈ config d k σ τ) (hlvl : (∑ a, y a) = (d + 1) * k + 1) :
    y = cubePos σ ((d + 1) * k + 1) := by
  obtain ⟨-, hc⟩ := config_cases d k σ τ hy
  rw [hlvl] at hc
  rcases hc with h | ⟨m, -, hm⟩
  · exact h.symm
  · exfalso
    have := branchIdx_top d τ m
    omega

/-- If two configurations are equal, their spine cubes agree at every depth `i` below the top:
`cubePos σ ((d+1)k + 1 - i) = cubePos σ' ((d+1)k + 1 - i)`.

Induction on `i`. At `0` both are the unique top-layer cube (`top_unique`). At `i + 1` the two
candidates step to the same already-identified cube, so `config_isTree`'s `parent_unique` identifies
them.

The counterpart for the branched family of what `CubeArea.mem_of_boundary_eq_aux` does for a path.

DERIVED: `1` is `config`'s block length and top step, and the induction's step; `3` is the
dimension. -/
theorem spine_eq_of_eq (d k : ℕ) (σ σ' : Fin ((d + 1) * k + 1) → Fin 3) (τ τ' : Fin k → Fin d)
    (h : config d k σ τ = config d k σ' τ') :
    ∀ i : ℕ, i ≤ (d + 1) * k + 1 →
      cubePos σ ((d + 1) * k + 1 - i) = cubePos σ' ((d + 1) * k + 1 - i) := by
  intro i
  induction i with
  | zero =>
    intro _
    have hmem : cubePos σ ((d + 1) * k + 1) ∈ config d k σ' τ' := by
      rw [← h, mem_config_iff]
      exact Or.inl ⟨(d + 1) * k + 1, le_refl _, rfl⟩
    have hl : (∑ a, cubePos σ ((d + 1) * k + 1) a) = (d + 1) * k + 1 :=
      cubePos_sum_le σ (le_refl _)
    simpa using top_unique d k σ' τ' hmem hl
  | succ n ih =>
    intro hn
    have hih := ih (by omega)
    have hj1 : (d + 1) * k + 1 - n = ((d + 1) * k + 1 - (n + 1)) + 1 := by omega
    rw [hj1] at hih
    have hjlt : (d + 1) * k + 1 - (n + 1) < (d + 1) * k + 1 := by omega
    have hpin : cubePos σ ((d + 1) * k + 1 - (n + 1)) ∈ config d k σ τ := by
      rw [mem_config_iff]; exact Or.inl ⟨_, by omega, rfl⟩
    have hqin : cubePos σ' ((d + 1) * k + 1 - (n + 1)) ∈ config d k σ τ := by
      rw [h, mem_config_iff]; exact Or.inl ⟨_, by omega, rfl⟩
    have hcin : step (spineDir σ ((d + 1) * k + 1 - (n + 1)))
        (cubePos σ ((d + 1) * k + 1 - (n + 1))) ∈ config d k σ τ := by
      rw [← spine_succ σ hjlt, mem_config_iff]
      exact Or.inl ⟨_, by omega, rfl⟩
    have heq : step (spineDir σ ((d + 1) * k + 1 - (n + 1)))
          (cubePos σ ((d + 1) * k + 1 - (n + 1)))
        = step (spineDir σ' ((d + 1) * k + 1 - (n + 1)))
          (cubePos σ' ((d + 1) * k + 1 - (n + 1))) := by
      rw [← spine_succ σ hjlt, ← spine_succ σ' hjlt]
      exact hih
    exact ((config_isTree d k σ τ).parent_unique _ _ _ _ hpin hqin hcin heq).2

/-- `spine_eq_of_eq` reindexed from depth to spine index: equal configurations have equal spine cubes
at every index up to `(d+1)k + 1`.

DERIVED: `1` is `config`'s block length and top step; `3` is the dimension. -/
theorem cubePos_eq_of_eq (d k : ℕ) (σ σ' : Fin ((d + 1) * k + 1) → Fin 3) (τ τ' : Fin k → Fin d)
    (h : config d k σ τ = config d k σ' τ') :
    ∀ j, j ≤ (d + 1) * k + 1 → cubePos σ j = cubePos σ' j := by
  intro j hj
  have hds := spine_eq_of_eq d k σ σ' τ τ' h ((d + 1) * k + 1 - j) (by omega)
  have hrw : (d + 1) * k + 1 - ((d + 1) * k + 1 - j) = j := by omega
  rwa [hrw] at hds

/-- Equal configurations have equal spine direction sequences. At each index the spine cubes agree
there and one step on (`cubePos_eq_of_eq`), so `spine_succ` and `step_axis_inj` identify the
directions.

DERIVED: `1` is `config`'s block length and top step, and the single spine step; `3` is the
dimension. -/
theorem sigma_eq_of_eq (d k : ℕ) (σ σ' : Fin ((d + 1) * k + 1) → Fin 3) (τ τ' : Fin k → Fin d)
    (h : config d k σ τ = config d k σ' τ') : σ = σ' := by
  funext jj
  have h1 := cubePos_eq_of_eq d k σ σ' τ τ' h (jj : ℕ) (le_of_lt jj.2)
  have h2 := cubePos_eq_of_eq d k σ σ' τ τ' h ((jj : ℕ) + 1) jj.2
  rw [spine_succ σ jj.2, spine_succ σ' jj.2, h1] at h2
  have h3 := step_axis_inj h2
  rw [spineDir_lt σ jj.2, spineDir_lt σ' jj.2] at h3
  simpa using h3

/-- At a fixed spine, equal configurations have equal block positions. Each extra cube of one lies in
the other; it is not a spine cube (`branchCube_ne_cubePos`), so it is an extra cube there, and
`sum_branchCube` with `branchIdx_eq` identifies the block and the position.

DERIVED: `1` is `config`'s block length and top step; `3` is the dimension. -/
theorem tau_eq_of_eq (d k : ℕ) (σ : Fin ((d + 1) * k + 1) → Fin 3) (τ τ' : Fin k → Fin d)
    (h : config d k σ τ = config d k σ τ') : τ = τ' := by
  funext m
  have htop := branchIdx_top d τ m
  have hmem : branchCube σ (branchIdx d τ m) ∈ config d k σ τ' := by
    rw [← h, mem_config_iff]; exact Or.inr ⟨m, rfl⟩
  rcases (mem_config_iff d k σ τ' _).mp hmem with ⟨j, hj, hji⟩ | ⟨m', hm'⟩
  · exact absurd hji.symm (branchCube_ne_cubePos σ (by omega) hj)
  · have htop' := branchIdx_top d τ' m'
    have h1 := sum_branchCube σ (show branchIdx d τ m ≤ (d + 1) * k + 1 by omega)
    have h2 := sum_branchCube σ (show branchIdx d τ' m' ≤ (d + 1) * k + 1 by omega)
    rw [hm', h1] at h2
    obtain ⟨hmm, hval⟩ :=
      branchIdx_eq d τ τ' (show branchIdx d τ m = branchIdx d τ' m' by omega)
    subst hmm
    exact Fin.ext hval

/-- `fun p => config d k p.1 p.2` is injective on
`(Fin ((d+1)k+1) → Fin 3) × (Fin k → Fin d)`: `sigma_eq_of_eq` recovers the spine and
`tau_eq_of_eq` the block positions.

DERIVED: `1` is `config`'s block length and top step; `3` is the dimension. The `1` and `2` in `p.1`,
`p.2` are the projections of the parameter pair, not numbers. -/
theorem config_injective (d k : ℕ) :
    Function.Injective
      (fun p : (Fin ((d + 1) * k + 1) → Fin 3) × (Fin k → Fin d) => config d k p.1 p.2) := by
  rintro ⟨σ, τ⟩ ⟨σ', τ'⟩ hcfg
  simp only at hcfg
  have hs : σ = σ' := sigma_eq_of_eq d k σ σ' τ τ' hcfg
  subst hs
  have ht : τ = τ' := tau_eq_of_eq d k σ τ τ' hcfg
  subst ht
  rfl

/-- `fun p => boundaryFaces (config d k p.1 p.2)` is injective: `eq_of_boundaryFaces_eq` turns equal
boundaries into equal configurations, and `config_injective` into equal parameters.

DERIVED: `1` is `config`'s block length and top step; `3` is the dimension; the `1` and `2` in `p.1`,
`p.2` are the parameter pair's projections. -/
theorem boundary_config_injective (d k : ℕ) :
    Function.Injective
      (fun p : (Fin ((d + 1) * k + 1) → Fin 3) × (Fin k → Fin d) =>
        boundaryFaces (config d k p.1 p.2)) :=
  fun _ _ hbd => config_injective d k (eq_of_boundaryFaces_eq hbd)

/-! ### The count, and the area, together -/

/-- There is a `Finset (Finset Face)` of cardinality `3 ^ ((d+1)k+1) * d ^ k` every member of which
has cardinality `4 * ((d+2)k + 2) + 2`. The witness is the image of
`fun p => boundaryFaces (config d k p.1 p.2)`, counted by `boundary_config_injective` and measured by
`boundary_card_config`.

The branched counterpart of `CubeArea.directed_surfaces_count_and_area`. At `d = 3` the count is
`3 ^ ((d+2)k+1)` over the same cardinality, which is the path count at the path density.

DERIVED: `3` is the dimension and the base of the direction count — the same number, since the step
alphabet is `Fin 3`. `1` in the exponent is `config`'s block length and top step. `4` and the
trailing `2` are `boundary_card_tree`'s; `(d+2)k + 2` is `card_config`'s cube count. -/
theorem branched_surfaces_count_and_area (d k : ℕ) :
    ∃ S : Finset (Finset Face),
      S.card = 3 ^ ((d + 1) * k + 1) * d ^ k ∧ ∀ F ∈ S, F.card = 4 * ((d + 2) * k + 2) + 2 := by
  classical
  refine ⟨Finset.univ.image
    (fun p : (Fin ((d + 1) * k + 1) → Fin 3) × (Fin k → Fin d) =>
      boundaryFaces (config d k p.1 p.2)), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (boundary_config_injective d k), Finset.card_univ]
    simp
  · intro F hF
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hF
    exact boundary_card_config d k p.1 p.2

/-- Every edge lies in an even number of the boundary's faces:
`((boundaryFaces (config d k σ τ)).filter (fun f => (c, w) ∈ faceEdges f)).card % 2 = 0`. The body is
`CubeClosed.edge_parity_all`, which is already stated for an arbitrary configuration.

This is closedness in the edge-parity sense. Connectedness is a separate property and is not proved
for this family.

DERIVED: `2` is the modulus — an edge is shared by two faces of a closed surface — and `0` the
residue asserted. `1` is `config`'s block length and top step; `3` is the dimension. -/
theorem branched_surfaces_closed (d k : ℕ) (σ : Fin ((d + 1) * k + 1) → Fin 3) (τ : Fin k → Fin d)
    (c : Fin 3) (w : Cube) :
    ((boundaryFaces (config d k σ τ)).filter (fun f => (c, w) ∈ faceEdges f)).card % 2 = 0 :=
  edge_parity_all (config d k σ τ) c w

/-- Each of the origin cube's three low faces lies on every member's boundary:
`((a, cubePos σ 0) : Face) ∈ boundaryFaces (config d k σ τ)`. The origin is in every member
(`config_root_mem`) and its coordinates are `0`, so `CubeClosed.mem_boundaryFaces_iff_floor` applies.

So all the boundaries in the family share those three faces.

DERIVED: `0` is the origin's spine index and the value of each of its coordinates; `1` is `config`'s
block length and top step; `3` is the dimension, hence the number of low faces. -/
theorem branched_origin_face_mem_boundary (d k : ℕ) (σ : Fin ((d + 1) * k + 1) → Fin 3)
    (τ : Fin k → Fin d) (a : Fin 3) :
    ((a, cubePos σ 0) : Face) ∈ boundaryFaces (config d k σ τ) := by
  have hzero : cubePos σ 0 a = 0 := by rw [MassGap.cubePos]; simp
  exact (mem_boundaryFaces_iff_floor _ a _ hzero).mpr (config_root_mem d k σ τ)

#print axioms branched_surfaces_count_and_area
#print axioms branched_surfaces_closed
#print axioms branched_origin_face_mem_boundary

/-! ### The density, and the floor it raises -/

/-- For reals `A`, `B`, `C`, `D` with `0 < C` and `0 ≤ D`, the sequence
`k ↦ (A·k + B)/(C·k + D)` converges to `A / C`. Rewritten, eventually in `k`, as
`A/C + (BC − AD)/(C(Ck + D))`, whose second term tends to `0`.

`Floor.density_ratio` is the case `A = 1`, `B = −1`, `C = 4`, `D = 2`; here the coefficients carry
logarithms.

DERIVED: `0` is the strict lower bound on `C`, which the division requires, and the lower bound on
`D`, which keeps the denominator eventually positive. `A`, `B`, `C`, `D` are the caller's. -/
theorem tendsto_affine_ratio {A B C D : ℝ} (hC : 0 < C) (hD : 0 ≤ D) :
    Filter.Tendsto (fun k : ℕ => (A * (k : ℝ) + B) / (C * (k : ℝ) + D)) Filter.atTop
      (nhds (A / C)) := by
  have h0 : Filter.Tendsto (fun k : ℕ => C * (k : ℝ) + D) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop D
      (Filter.Tendsto.const_mul_atTop hC tendsto_natCast_atTop_atTop)
  have hden : Filter.Tendsto (fun k : ℕ => C * (C * (k : ℝ) + D)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hC h0
  have hz : Filter.Tendsto (fun k : ℕ => (B * C - A * D) / (C * (C * (k : ℝ) + D)))
      Filter.atTop (nhds 0) := Filter.Tendsto.div_atTop tendsto_const_nhds hden
  have hcongr : (fun k : ℕ => (A * (k : ℝ) + B) / (C * (k : ℝ) + D))
      =ᶠ[Filter.atTop] (fun k : ℕ => A / C + (B * C - A * D) / (C * (C * (k : ℝ) + D))) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with k hk
    have hk' : (0 : ℝ) < (k : ℕ) := by exact_mod_cast hk
    have h1 : (0 : ℝ) < C * (k : ℝ) + D := by nlinarith
    field_simp
    ring
  rw [Filter.tendsto_congr' hcongr]
  simpa using tendsto_const_nhds.add hz

/-- For `0 < d`, `log (3 ^ ((d+1)k+1) * d ^ k) = ((d + 1) log 3 + log d) · k + log 3`. `Real.log_mul`
and `Real.log_pow`, then `ring`.

The numerator of the density, as an affine function of `k`.

DERIVED: `0` is the strict lower bound on `d` in `hd`, needed so `log d` is the logarithm of a
positive number. `3` is the direction count and `1` is `config`'s block length and top step, both
carried from `branched_surfaces_count_and_area`'s cardinality. -/
theorem log_branch_count (d k : ℕ) (hd : 0 < d) :
    Real.log ((3 ^ ((d + 1) * k + 1) * d ^ k : ℕ) : ℝ)
      = (((d : ℝ) + 1) * Real.log 3 + Real.log d) * (k : ℝ) + Real.log 3 := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  push_cast
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- `(((d+1) log 3 + log d)·k + log 3) / (4(d+2)·k + 10) → ((d+1) log 3 + log d)/(4(d+2))`.
`tendsto_affine_ratio` at `A = (d+1) log 3 + log d`, `B = log 3`, `C = 4(d+2)`, `D = 10`.

The numerator is `log_branch_count`'s and the denominator is `area_eq`'s, so this is the limit of
`log(count)/area` along `k`. It holds at every `d`, including `d = 0`, where `log 0 = 0` in Mathlib's
convention.

DERIVED: `1` and `3` in the numerator are `log_branch_count`'s. `4` and `2` in `4(d+2)` are
`boundary_card_config`'s coefficient and the `+2` of the cube count. `10` is `4 * 2 + 2`, the
constant term of `4((d+2)k+2)+2`, so it is those same numerals and not a chosen value. -/
theorem branch_density_limit (d : ℕ) :
    Filter.Tendsto
      (fun k : ℕ => ((((d : ℝ) + 1) * Real.log 3 + Real.log d) * (k : ℝ) + Real.log 3)
        / (4 * ((d : ℝ) + 2) * (k : ℝ) + 10))
      Filter.atTop
      (nhds (((((d : ℝ) + 1) * Real.log 3 + Real.log d)) / (4 * ((d : ℝ) + 2)))) := by
  have hC : (0 : ℝ) < 4 * ((d : ℝ) + 2) := by positivity
  exact tendsto_affine_ratio (A := ((d : ℝ) + 1) * Real.log 3 + Real.log d) (B := Real.log 3)
    (C := 4 * ((d : ℝ) + 2)) (D := 10) hC (by norm_num)

/-- `((4 * ((d+2)k + 2) + 2 : ℕ) : ℝ) = 4(d+2)·k + 10`: the boundary cardinality cast to `ℝ` and
expanded as an affine function of `k`. `push_cast` and `ring`.

DERIVED: `4` and the trailing `2` are `boundary_card_config`'s, and the inner `2`s are
`card_config`'s. `10` is `4 * 2 + 2`, the constant term, so it is those numerals combined. -/
theorem area_eq (d k : ℕ) :
    ((4 * ((d + 2) * k + 2) + 2 : ℕ) : ℝ) = 4 * ((d : ℝ) + 2) * (k : ℝ) + 10 := by
  push_cast
  ring

/-- For `3 < d`, `(1/4) log 3 < ((d+1) log 3 + log d) / (4(d+2))`. Clearing the positive denominator,
the inequality reduces by `nlinarith` to `log 3 < log d`, which is `Real.log_lt_log`.

The comparison turns on `log 3 < log d` alone: the extra cube adds `4` to the area, the same as a
spine step, and `log d` to the count against a spine step's `log 3`.
`branch_density_eq_floor_at_three` is the boundary case.

DERIVED: `3` is the strict lower bound on `d` in `hd`, and the direction count inside both
logarithms; the two coincide, which is why `d = 3` is the boundary. `1` and `4` on the left spell the
constant `(1/4) log 3`; `1` in `(d+1)` and `4`, `2` in `4(d+2)` are the density's, from
`log_branch_count` and `area_eq`. -/
theorem branch_density_gt_floor (d : ℕ) (hd : 3 < d) :
    (1 / 4 : ℝ) * Real.log 3
      < (((d : ℝ) + 1) * Real.log 3 + Real.log d) / (4 * ((d : ℝ) + 2)) := by
  have hdr : (3 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlog : Real.log 3 < Real.log d := Real.log_lt_log (by norm_num) hdr
  have hC : (0 : ℝ) < 4 * ((d : ℝ) + 2) := by positivity
  rw [lt_div_iff₀ hC]
  nlinarith [hlog]

/-- `(1/4) log 3 = ((3 + 1) log 3 + log 3) / (4 * (3 + 2))`: at `d = 3` the two densities coincide.
By `ring`, since `(4 log 3 + log 3)/20 = 5 log 3 / 20`.

The boundary case of `branch_density_gt_floor`, and the negative control: at `d = 3` the family has
`3^((d+1)k+1)·3^k = 3^((d+2)k+1)` members over the same cardinality, which is the path count at the
path density, so nothing is gained.

DERIVED: `3` is the value of `d` substituted, which equals the direction count, and the argument of
every logarithm — that coincidence is what makes the two sides equal. `1` and `4` on the left spell
`(1/4) log 3`; `1` in `(3 + 1)` and `4`, `2` in `4 * (3 + 2)` are the density's, at `d = 3`. -/
theorem branch_density_eq_floor_at_three :
    (1 / 4 : ℝ) * Real.log 3 = ((3 + 1) * Real.log 3 + Real.log 3) / (4 * (3 + 2)) := by
  ring

/-- `(1/4) log 3 < (11 log 3 + log 10) / 48`: `branch_density_gt_floor` at `d = 10`, with `norm_num`
evaluating `d + 1 = 11` and `4(d + 2) = 48`.

An inequality between two real numbers. The instance at `d = 10`; no statement here says that value
of `d` maximises the density.

DERIVED: `10` is the value of `d` substituted, so `11` is `d + 1` and `48` is `4(d + 2)`; neither is
chosen independently, and `10` inside the logarithm is the same `d`. `1` and `4` on the left spell
`(1/4) log 3`, and `3` is the direction count. -/
theorem branch_floor_ten :
    (1 / 4 : ℝ) * Real.log 3 < (11 * Real.log 3 + Real.log 10) / 48 := by
  have h := branch_density_gt_floor 10 (by norm_num)
  norm_num at h
  exact h

#print axioms branch_density_limit
#print axioms branch_density_gt_floor
#print axioms branch_floor_ten

end MassGap.CubeBranch
