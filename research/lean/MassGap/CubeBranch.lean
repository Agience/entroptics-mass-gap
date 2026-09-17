import MassGap.CubeClosed

/-!
# A RICHER counted family: the entropy floor above `¼ log 3`

**WHY THIS FILE EXISTS.** `Floor` + `CubeArea` bound the centre-vortex surface entropy density by
exhibiting DIRECTED CUBE-PATHS: `3ᵏ` of them (`Floor.directed_paths_card`), each bounding a distinct
closed surface (`CubeArea.boundaryFaces_cubeConfig_injective`) of area exactly `4k+6`
(`CubeArea.boundary_card_eq`). That gives `κ₀ ≥ (¼) log 3 = 0.274653`.

Paths are not the only surfaces of that area, and `κ₀` is a limsup over ALL closed connected
surfaces, so counting a STRICTLY RICHER subfamily gives a strictly larger lower bound on the SAME
quantity. This file counts one.

**THE FAMILY: a path with one extra cube per block.** Take a directed cube-path (the SPINE) of
`(d+1)k+1` steps and, in each of the `k` blocks of `d+1` consecutive steps, hang ONE extra cube off a
spine cube of the block — `d` choices of which cube inside the block, in an axis forced by the
construction. The counted set is then

    (spine directions) × (block positions)   of cardinality   `3^((d+1)k+1) · d^k`,

every member has `(d+2)k+2` cubes, and every member's boundary has `4((d+2)k+2)+2` faces.

**WHY THE AREA IS STILL `4n+2`.** Every cube but the origin has EXACTLY ONE face-neighbour below it
(`config_isTree`), so the configuration is a TREE and the shared-face count is `n−1`. The double
count `CubeArea.boundary_card_of_shared` — which was already stated for an arbitrary `Finset Cube` —
then reads `6n = |∂C| + 2(n−1)`, i.e. `|∂C| = 4n+2`. For a path `n = k+1` and this is `4k+6`, so the
two families are measured on one and the same scale.

**WHAT THE EXTRA CUBE BUYS.** Per block the family has `3^(d+1)·d` members costing `d+2` cubes, i.e.
`4(d+2)` of area, against the path's `3^(d+2)` members at the same cost. The density is therefore

    `((d+1)·log 3 + log d) / (4(d+2))`   against   `(d+2)·log 3 / (4(d+2)) = ¼ log 3`,

and the first exceeds the second exactly when `log d > log 3`, i.e. when `d > 3`
(`branch_density_gt_floor`). At `d = 10` — where the density is largest — this is

    `κ₀ ≥ (11 log 3 + log 10)/48 = 0.2997358…  >  0.2746531… = ¼ log 3`.

`d ≤ 3` is the negative control and it fails as it must: at `d = 3` the count `3^(d+1)·d = 3^(d+2)`
is EXACTLY the path count over the same cubes, and the density is exactly `¼ log 3`.

**THE FORCED AXIS.** The extra cube at spine index `i` is `stepᵦ` of the spine cube, with
`β = rot1 (sᵢ)` unless that equals `sᵢ₊₁`, in which case `β = rot2 (sᵢ)`. Both facts the tree
property needs — `β ≠ sᵢ` and `β ≠ sᵢ₊₁` — are then immediate from `rot1_ne`, `rot2_ne` and
`rot1_ne_rot2`, with no case analysis on the directions. `β ≠ sᵢ` keeps the extra cube off the spine;
`β ≠ sᵢ₊₁` is what stops the NEXT spine cube from acquiring a second parent, and dropping it really
does break the tree (checked by `certify/floor_branch_family.py`'s negative control).

**WHAT IS PROVED HERE AND WHAT IS NOT.** `branched_surfaces_count_and_area` (the count and the area)
and `branched_surfaces_closed` (closed) are proved; CONNECTEDNESS of these boundaries is NOT.
`CubeConnected.boundary_connected` descends on the path's own indexing — a directed path holds
exactly ONE cube at each coordinate sum, which is the fact its whole argument runs on — and a tree
holds two at the layers carrying an extra cube. Every boundary this family produces IS connected
(checked over the whole parameter set at small `(d,k)` and by sampling at `d = 10`, `k ≤ 8`, in
`certify/floor_branch_family.py`), so the missing piece is the Lean and not the geometry. Until it is
written this raises the COUNTED floor and does not yet replace `CubeConnected`'s input to
`VortexFamily`.

**WHAT IT DOES NOT REACH.** The front-capped transfer-matrix certificate
(`certify/floor_ladder_exact.py`) puts the true floor at `κ₀ ≥ 0.455483`, and an exactly-solvable
ceiling on the same tree family — free ternary trees, `w = (1+x⁴w)³`, critical at `x⁴ = 4/27` — is
`(3log 3 − 2log 2)/4 = 0.477386`. So `0.2997358` is a fifth of the way from the path floor to what
the ladder already certifies numerically, and the remaining distance is a COUNTING problem: directed
lattice site-trees have the same `4n+2` area law (`boundary_card_tree`, proved here for ALL of them)
and are measured to grow like `5.2ⁿ`, but no closed form counts them.

DERIVED throughout: `3` is the dimension and the step alphabet's arity, `6` the faces of a cube, `2`
the owners of a face, `4 = 6 − 2` the area a one-parent cube adds. `d` is a free parameter of the
family, not a fitted constant: every `d` gives a theorem and `d > 3` gives one that beats the path.
-/

namespace MassGap.CubeBranch

open Finset MassGap MassGap.CubeArea

/-! ### The boundary determines the configuration

`CubeArea.mem_of_boundary_eq_aux` recovers a cube-PATH from its boundary by an induction that uses
the path's own indexing. The same recovery holds for an ARBITRARY finite configuration and needs no
indexing at all: `CubeClosed.mem_boundaryFaces_iff_floor` decides membership on the floor `y 0 = 0`,
and `CubeClosed.mem_boundaryFaces_iff_xor` propagates it one step at a time. So two configurations
with the same boundary are the same configuration, and any family whatever is counted by its
surfaces as soon as it is counted by its cubes. -/

/-- Membership at height `n` along axis `0`, decided by the boundary. -/
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

/-- **THE BOUNDARY MAP IS INJECTIVE ON CONFIGURATIONS**, with no hypothesis on the configurations.
This is `CubeArea.boundaryFaces_cubeConfig_injective` freed of the path. -/
theorem eq_of_boundaryFaces_eq {C D : Finset Cube} (h : boundaryFaces C = boundaryFaces D) :
    C = D := by
  ext y
  exact mem_iff_of_boundary_eq h (y 0) y rfl

#print axioms eq_of_boundaryFaces_eq

/-! ### Trees, and why a tree's area is `4n+2` -/

/-- **A DIRECTED CUBE-TREE rooted at `r`.** Every cube but `r` is reached by exactly one step from
exactly one other cube of the configuration, and nothing steps into `r`. A directed cube-PATH is the
special case with one leaf. -/
structure IsCubeTree (C : Finset Cube) (r : Cube) : Prop where
  /-- the root is in the configuration -/
  root_mem : r ∈ C
  /-- nothing in the configuration steps into the root -/
  root_no_parent : ∀ (a : Fin 3) (p : Cube), p ∈ C → step a p ≠ r
  /-- every other cube is stepped into from inside the configuration -/
  parent_exists : ∀ c ∈ C, c ≠ r → ∃ (a : Fin 3) (p : Cube), p ∈ C ∧ step a p = c
  /-- and only once: a cube OF the configuration has at most one parent in it -/
  parent_unique : ∀ (a b : Fin 3) (p q : Cube), p ∈ C → q ∈ C → step a p ∈ C →
      step a p = step b q → a = b ∧ p = q

/-- The faces of `C` carried by two cubes — the interior ones.

DERIVED: `2` is the number of cubes a face can belong to (`CubeArea.card_cubes_with_face_le_two`),
so "two owners" is the complement of "on the boundary" and not a chosen cut. -/
noncomputable def sharedFaces (C : Finset Cube) : Finset Face :=
  (C.biUnion faces).filter (fun f => (C.filter (fun x => f ∈ faces x)).card = 2)

/-- A shared face carries its corner AND a cube one step behind it — both in `C`. -/
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

/-- **A TREE HAS `n−1` SHARED FACES.** The map `f ↦ f.2` is a bijection from the shared faces onto
the non-root cubes: a shared face names a cube of `C` together with its parent (`shared_owners`), the
cube determines the face because `parent_unique` fixes the axis, and every non-root cube names one
because `parent_exists` gives it a parent. -/
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

/-- **THE AREA OF A TREE'S BOUNDARY IS `4n+2`.** The double count
`CubeArea.boundary_card_of_shared` gives `6n = |B| + (n−1)` and the boundary drops the shared faces
once more, so `|∂C| = |B| − (n−1) = 6n − 2(n−1) = 4n+2`. For a directed path `n = k+1` and this is
`CubeArea.boundary_card_eq`'s `4k+6`: the two families sit on the same area scale, which is what
makes their densities comparable. -/
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

/-- A step raises exactly its own coordinate, by one. -/
theorem step_val (a : Fin 3) (x : Cube) (c : Fin 3) :
    step a x c = x c + (if c = a then 1 else 0) := by
  by_cases h : c = a
  · subst h; simp [step_self]
  · simp [step_other h, h]

/-- **THE TWO-STEP CLASH.** If a cube is reached both by stepping `a` from `step u x` and by
stepping `b` from `step w x`, with `w ≠ u`, then the two steps are forced: `a = w` and `b = u`, so
the cube is `x + e_u + e_w`. This is the only way a cube of the tree could acquire a second parent,
and `branch_child_not_mem` shows that cube is not in the configuration. -/
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

/-- The spine direction at step `j`, total in `j`.

DERIVED: the value past the end is junk and never read — `spineDir_lt` is the only fact used and it
speaks about indices inside the range. `0` is `Fin 3`'s own first element, not a magnitude. -/
def spineDir {N : ℕ} (σ : Fin N → Fin 3) (j : ℕ) : Fin 3 :=
  if h : j < N then σ ⟨j, h⟩ else 0

theorem spineDir_lt {N : ℕ} (σ : Fin N → Fin 3) {j : ℕ} (h : j < N) :
    spineDir σ j = σ ⟨j, h⟩ := dif_pos h

/-- **THE FORCED AXIS OF THE EXTRA CUBE.** `rot1` of the spine's own direction, unless that is the
NEXT spine direction, in which case `rot2`. Both facts the tree property needs follow with no case
analysis on the directions: `branchDir_ne_self` keeps the extra cube off the spine and
`branchDir_ne_next` stops the next spine cube from acquiring a second parent.

DERIVED: `1` is one spine step ahead — the extra cube and the next spine cube are the two cubes of
the same coordinate sum, so "the next direction" is what the axis must avoid. -/
def branchDir {N : ℕ} (σ : Fin N → Fin 3) (i : ℕ) : Fin 3 :=
  if rot1 (spineDir σ i) = spineDir σ (i + 1) then rot2 (spineDir σ i) else rot1 (spineDir σ i)

theorem branchDir_ne_self {N : ℕ} (σ : Fin N → Fin 3) (i : ℕ) :
    branchDir σ i ≠ spineDir σ i := by
  rw [branchDir]
  split_ifs with h
  · exact rot2_ne _
  · exact rot1_ne _

theorem branchDir_ne_next {N : ℕ} (σ : Fin N → Fin 3) (i : ℕ) :
    branchDir σ i ≠ spineDir σ (i + 1) := by
  rw [branchDir]
  split_ifs with h
  · rw [← h]; exact (rot1_ne_rot2 _).symm
  · exact h

/-- The extra cube hung on the spine at index `i`: one step off the spine cube, on the forced axis.

DERIVED: `3` is `Cube`'s dimension — the step alphabet `Floor.directed_paths_card` counts over — and
one step is the lattice unit, the same one `CubeArea.step` already names. -/
noncomputable def branchCube {N : ℕ} (σ : Fin N → Fin 3) (i : ℕ) : Cube :=
  step (branchDir σ i) (cubePos σ i)

/-- The spine index the `m`-th block's extra cube hangs on.

DERIVED: `d+1` is the block's length in spine steps, so the `m`-th block starts at `(d+1)m`; the
position `τ m < d` inside it is the family's own choice, and `d` of them is what the count `d^k`
counts. -/
def branchIdx (d : ℕ) {k : ℕ} (τ : Fin k → Fin d) (m : Fin k) : ℕ :=
  (d + 1) * (m : ℕ) + (τ m : ℕ)

/-- **THE CONFIGURATION.** The spine's `(d+1)k+2` cubes together with one extra cube per block.

DERIVED: `3` is `Cube`'s dimension; `d+1` is the block's length in spine steps, so `k` blocks take
`(d+1)k` of them and the `+1` is the one further step that leaves the top layer to the spine alone
(`top_unique`), which is what makes the spine recoverable. `2` is nothing chosen — it is the arity of
the parameter pair (directions, positions). -/
noncomputable def config (d k : ℕ) (σ : Fin ((d + 1) * k + 1) → Fin 3) (τ : Fin k → Fin d) :
    Finset Cube :=
  cubeConfig σ ∪ (Finset.univ.image (fun m => branchCube σ (branchIdx d τ m)))

/-! ### Where the extra cubes sit -/

/-- The extra cube of a block, and the one after it, still leave two spine steps at the top. -/
theorem idx_top (d : ℕ) {k a u : ℕ} (ha : a < k) (hu : u < d) :
    (d + 1) * a + u + 2 ≤ (d + 1) * k := by
  have h1 : (d + 1) * (a + 1) ≤ (d + 1) * k := Nat.mul_le_mul (le_refl _) ha
  rw [Nat.mul_succ] at h1
  omega

/-- **EXTRA CUBES ARE AT LEAST TWO SPINE STEPS APART**, which is what keeps each block's cube from
interfering with the next block's. -/
theorem idx_gap (d a b u v : ℕ) (hu : u < d) (hab : a < b) :
    (d + 1) * a + u + 2 ≤ (d + 1) * b + v := by
  have h1 : (d + 1) * (a + 1) ≤ (d + 1) * b := Nat.mul_le_mul (le_refl _) hab
  rw [Nat.mul_succ] at h1
  omega

theorem branchIdx_top (d : ℕ) {k : ℕ} (τ : Fin k → Fin d) (m : Fin k) :
    branchIdx d τ m + 2 ≤ (d + 1) * k :=
  idx_top d m.2 (τ m).2

/-- The block index and the position inside it are both recoverable from the spine index. -/
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

theorem sum_branchCube {N : ℕ} (σ : Fin N → Fin 3) {i : ℕ} (hi : i ≤ N) :
    ∑ a, branchCube σ i a = i + 1 := by
  rw [branchCube, sum_step, cubePos_sum_le σ hi]

/-- The spine cube one step on, written as a step. -/
theorem spine_succ {N : ℕ} (σ : Fin N → Fin 3) {j : ℕ} (h : j < N) :
    cubePos σ (j + 1) = step (spineDir σ j) (cubePos σ j) := by
  rw [spineDir_lt σ h]
  exact cubePos_succ_eq_step σ ⟨j, h⟩

/-- **AN EXTRA CUBE IS NEVER A SPINE CUBE.** Both sit one step from the same spine cube, on
different axes (`branchDir_ne_self`). -/
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

/-- **EVERY CUBE IS NAMED BY ITS OWN COORDINATE SUM**: it is either the spine cube of that layer or
the block cube hung one step below it. -/
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

/-- **THE CUBE THAT WOULD HAVE TWO PARENTS IS NOT THERE.** The only way a cube of this configuration
could be reached both from the spine and from a block's extra cube is `x + e_u + e_w`
(`step_pair_eq`); it is not the next spine cube because `branchDir_ne_next` separates the axes, and
it is not another block's extra cube because blocks are two steps apart (`idx_gap`). -/
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

/-- The origin cube is in every member of the family: every spine starts there. -/
theorem config_root_mem (d k : ℕ) (σ : Fin ((d + 1) * k + 1) → Fin 3) (τ : Fin k → Fin d) :
    cubePos σ 0 ∈ config d k σ τ := by
  rw [mem_config_iff]
  exact Or.inl ⟨0, Nat.zero_le _, rfl⟩

/-- **NO CUBE HAS TWO PARENTS**, stated at the one pair that could: a spine cube and the extra cube
hung one step below it. -/
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

/-- **THE COUNTED CONFIGURATION IS A DIRECTED CUBE-TREE.** This is the whole geometric content of
the construction: the forced axis (`branchDir_ne_self`, `branchDir_ne_next`) and the two-step gap
between blocks (`idx_gap`) are exactly what stop any cube from acquiring a second parent. -/
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

/-- **THE CUBE COUNT**: `(d+1)k+2` spine cubes and `k` extra ones. -/
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

/-- **THE AREA OF EVERY MEMBER**: `4n+2` at `n = (d+2)k+2`. -/
theorem boundary_card_config (d k : ℕ) (σ : Fin ((d + 1) * k + 1) → Fin 3) (τ : Fin k → Fin d) :
    (boundaryFaces (config d k σ τ)).card = 4 * ((d + 2) * k + 2) + 2 := by
  rw [boundary_card_tree (config_isTree d k σ τ), card_config]

/-! ### Distinct parameters give distinct surfaces -/

/-- The top layer holds only the spine: every extra cube sits at least two steps below it. -/
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

/-- **THE SPINE IS RECOVERED FROM THE TOP DOWN.** The unique cube of the top layer is the spine's
last, and every cube of the tree has a unique parent, so the whole spine is determined by the cube
set — the step `CubeArea.mem_of_boundary_eq_aux` does for a path. -/
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

theorem cubePos_eq_of_eq (d k : ℕ) (σ σ' : Fin ((d + 1) * k + 1) → Fin 3) (τ τ' : Fin k → Fin d)
    (h : config d k σ τ = config d k σ' τ') :
    ∀ j, j ≤ (d + 1) * k + 1 → cubePos σ j = cubePos σ' j := by
  intro j hj
  have hds := spine_eq_of_eq d k σ σ' τ τ' h ((d + 1) * k + 1 - j) (by omega)
  have hrw : (d + 1) * k + 1 - ((d + 1) * k + 1 - j) = j := by omega
  rwa [hrw] at hds

theorem sigma_eq_of_eq (d k : ℕ) (σ σ' : Fin ((d + 1) * k + 1) → Fin 3) (τ τ' : Fin k → Fin d)
    (h : config d k σ τ = config d k σ' τ') : σ = σ' := by
  funext jj
  have h1 := cubePos_eq_of_eq d k σ σ' τ τ' h (jj : ℕ) (le_of_lt jj.2)
  have h2 := cubePos_eq_of_eq d k σ σ' τ τ' h ((jj : ℕ) + 1) jj.2
  rw [spine_succ σ jj.2, spine_succ σ' jj.2, h1] at h2
  have h3 := step_axis_inj h2
  rw [spineDir_lt σ jj.2, spineDir_lt σ' jj.2] at h3
  simpa using h3

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

/-- **DISTINCT PARAMETERS GIVE DISTINCT CONFIGURATIONS.** -/
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

/-- **DISTINCT PARAMETERS GIVE DISTINCT SURFACES**, by `eq_of_boundaryFaces_eq`. -/
theorem boundary_config_injective (d k : ℕ) :
    Function.Injective
      (fun p : (Fin ((d + 1) * k + 1) → Fin 3) × (Fin k → Fin d) =>
        boundaryFaces (config d k p.1 p.2)) :=
  fun _ _ hbd => config_injective d k (eq_of_boundaryFaces_eq hbd)

/-! ### The count, and the area, together -/

/-- **THE BRANCHED ANALOGUE OF `CubeArea.directed_surfaces_count_and_area`.** There are
`3^((d+1)k+1) · d^k` distinct surfaces, each of area exactly `4((d+2)k+2)+2`. At `d = 3` the count is
`3^((d+2)k+1)` over exactly that area — the directed-path density, which is the negative control. At
`d > 3` it is strictly larger. -/
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

/-- **AND EVERY ONE OF THEM IS CLOSED.** `CubeClosed.edge_parity_all` was already stated for an
arbitrary configuration, so nothing new is needed: every edge lies in an even number of the
boundary's faces. -/
theorem branched_surfaces_closed (d k : ℕ) (σ : Fin ((d + 1) * k + 1) → Fin 3) (τ : Fin k → Fin d)
    (c : Fin 3) (w : Cube) :
    ((boundaryFaces (config d k σ τ)).filter (fun f => (c, w) ∈ faceEdges f)).card % 2 = 0 :=
  edge_parity_all (config d k σ τ) c w

/-- **AND EVERY ONE OF THEM PASSES THROUGH THE SAME FIXED PLAQUETTE.** The origin cube is in every
member (`config_root_mem`) and its low faces sit on the floor of `ℕ³`, so
`CubeClosed.mem_boundaryFaces_iff_floor` puts all three of them on every boundary. This is
`CubeClosed.origin_face_mem_boundary` for the branched family — the third of the four properties
Theorem 7.1's `N(A)` asks of each surface, the fourth being connectedness. -/
theorem branched_origin_face_mem_boundary (d k : ℕ) (σ : Fin ((d + 1) * k + 1) → Fin 3)
    (τ : Fin k → Fin d) (a : Fin 3) :
    ((a, cubePos σ 0) : Face) ∈ boundaryFaces (config d k σ τ) := by
  have hzero : cubePos σ 0 a = 0 := by rw [MassGap.cubePos]; simp
  exact (mem_boundaryFaces_iff_floor _ a _ hzero).mpr (config_root_mem d k σ τ)

#print axioms branched_surfaces_count_and_area
#print axioms branched_surfaces_closed
#print axioms branched_origin_face_mem_boundary

/-! ### The density, and the floor it raises -/

/-- An affine ratio converges to the ratio of its leading coefficients. `Floor.density_ratio` is the
case `A = 1, B = −1, C = 4, D = 2`; here both coefficients carry logarithms. -/
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

/-- The log of the family's count, evaluated. -/
theorem log_branch_count (d k : ℕ) (hd : 0 < d) :
    Real.log ((3 ^ ((d + 1) * k + 1) * d ^ k : ℕ) : ℝ)
      = (((d : ℝ) + 1) * Real.log 3 + Real.log d) * (k : ℝ) + Real.log 3 := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  push_cast
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- **THE DENSITY OF THE BRANCHED FAMILY.** `log(count) / area → ((d+1)log 3 + log d)/(4(d+2))`. -/
theorem branch_density_limit (d : ℕ) :
    Filter.Tendsto
      (fun k : ℕ => ((((d : ℝ) + 1) * Real.log 3 + Real.log d) * (k : ℝ) + Real.log 3)
        / (4 * ((d : ℝ) + 2) * (k : ℝ) + 10))
      Filter.atTop
      (nhds (((((d : ℝ) + 1) * Real.log 3 + Real.log d)) / (4 * ((d : ℝ) + 2)))) := by
  have hC : (0 : ℝ) < 4 * ((d : ℝ) + 2) := by positivity
  exact tendsto_affine_ratio (A := ((d : ℝ) + 1) * Real.log 3 + Real.log d) (B := Real.log 3)
    (C := 4 * ((d : ℝ) + 2)) (D := 10) hC (by norm_num)

/-- The area the density is taken over, as a real number: `4n+2` at `n = (d+2)k+2`. -/
theorem area_eq (d k : ℕ) :
    ((4 * ((d + 2) * k + 2) + 2 : ℕ) : ℝ) = 4 * ((d : ℝ) + 2) * (k : ℝ) + 10 := by
  push_cast
  ring

/-- **THE BRANCHED FLOOR BEATS `¼ log 3` EXACTLY WHEN `d > 3`.** The whole comparison reduces to
`log 3 < log d`: the extra cube costs `4` of area, the same as a spine step, and buys `log d` of
entropy against the spine step's `log 3`. `d ≤ 3` is the negative control. -/
theorem branch_density_gt_floor (d : ℕ) (hd : 3 < d) :
    (1 / 4 : ℝ) * Real.log 3
      < (((d : ℝ) + 1) * Real.log 3 + Real.log d) / (4 * ((d : ℝ) + 2)) := by
  have hdr : (3 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlog : Real.log 3 < Real.log d := Real.log_lt_log (by norm_num) hdr
  have hC : (0 : ℝ) < 4 * ((d : ℝ) + 2) := by positivity
  rw [lt_div_iff₀ hC]
  nlinarith [hlog]

/-- **AT `d = 3` THE TWO DENSITIES ARE EQUAL** — the negative control, in Lean. The family is then
`3^((d+1)k+1)·3^k = 3^((d+2)k+1)` surfaces over the same `4((d+2)k+2)+2` of area, which is the
directed-path count at the directed-path density. Nothing is gained, and nothing should be. -/
theorem branch_density_eq_floor_at_three :
    (1 / 4 : ℝ) * Real.log 3 = ((3 + 1) * Real.log 3 + Real.log 3) / (4 * (3 + 2)) := by
  ring

/-- **THE NEW FLOOR, AT THE BEST `d`.** `d = 10` maximises `((d+1)log 3 + log d)/(4(d+2))`, giving

    `κ₀ ≥ (11 log 3 + log 10)/48 = 0.29973583…`,

against `Floor`'s `¼ log 3 = 0.27465307…`. -/
theorem branch_floor_ten :
    (1 / 4 : ℝ) * Real.log 3 < (11 * Real.log 3 + Real.log 10) / 48 := by
  have h := branch_density_gt_floor 10 (by norm_num)
  norm_num at h
  exact h

#print axioms branch_density_limit
#print axioms branch_density_gt_floor
#print axioms branch_floor_ten

end MassGap.CubeBranch
