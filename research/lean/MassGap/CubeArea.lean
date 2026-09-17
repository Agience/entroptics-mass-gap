import MassGap.Floor

/-!
# The area of a directed cube-path's boundary

**WHY THIS FILE EXISTS.** `κ₀ = ¼log3` is the only thing in the development that bounds the mass gap
from BELOW, and it decomposes into two halves:

* `log 3` — the branching of a directed cube-path, three choices per step. PROVED, by
  `Floor.directed_paths_card`.
* `¼` — the `1/4` of `(n−1)log3/(4n+2) → ¼log3` (`Floor.floor_density_limit`). The `4` is the AREA
  per step, and it was **assumed**: written as a literal into `VortexCount.floorTerm` and derived
  nowhere.

That matters structurally, not cosmetically. Classical pure Yang–Mills carries no dimensionful
parameter, so a mass can only arise by dimensional transmutation — a PURE NUMBER becoming a scale.
A fitted constant anywhere in the chain would therefore be a smuggled scale, i.e. assuming the thing
being proved. `κ₀` being a counting number is the transmutation step, and a counting number with an
unproved coefficient is not yet one.

**WHAT IS PROVED HERE.** The double count behind `4k+6`:

    |∂C| = 6(k+1) − 2·(#shared faces) = 6(k+1) − 2k = 4k+6

for `C` the `k+1` cubes of a directed path. Its hard input already exists: `Floor.cubePos_sum_le`
gives the `i`-th cube coordinate-sum exactly `i`, which forces face-adjacency to mean CONSECUTIVE —
two cubes can share a face only if their positions differ by one unit in one coordinate, and that
moves the coordinate sum by exactly one.

DERIVED THROUGHOUT: `3` is the spatial dimension the cube-path lives in, `6` is the number of faces
of a cube (`2` per axis, `3` axes), and `2` is how many cubes a shared face belongs to. None is a
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

/-- A step raises the coordinate sum by exactly one. This is what makes the adjacency argument work:
the coordinate sum is a distance along the path. -/
theorem sum_step (a : Fin 3) (x : Cube) : ∑ b, step a x b = (∑ b, x b) + 1 := by
  classical
  rw [← Finset.add_sum_erase _ _ (mem_univ a), ← Finset.add_sum_erase _ x (mem_univ a)]
  rw [step_self]
  have : ∑ b ∈ univ.erase a, step a x b = ∑ b ∈ univ.erase a, x b := by
    refine Finset.sum_congr rfl (fun b hb => ?_)
    exact step_other (Finset.ne_of_mem_erase hb) x
  rw [this]
  ring

/-- The six faces of a unit cube: on each axis, the low face at `x` and the high face at `step a x`.

DERIVED: `3` is `Cube`'s dimension, and the six of `card_faces` is `2` per axis times that — the
`2` being the two sides of a cube along one axis. Neither is a magnitude. -/
def faces (x : Cube) : Finset Face :=
  (univ : Finset (Fin 3)).biUnion (fun a => {(a, x), (a, step a x)})

theorem mem_faces {f : Face} {x : Cube} :
    f ∈ faces x ↔ ∃ a : Fin 3, f = (a, x) ∨ f = (a, step a x) := by
  classical
  simp [faces, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]

/-- **A cube has six faces.** `2` per axis (low and high), `3` axes — and the two on one axis are
distinct because a step changes that axis's coordinate. -/
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

/-- **Sharing a face means being one step apart.** Two cubes with a common face are either equal or
differ by a single unit step along one axis — nothing else can happen, because a face names its axis
and its corner, and the corner is either the cube or its step. -/
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

/-- **THE ADJACENCY FACT THE AREA COUNT NEEDS.** Two cubes sharing a face have coordinate sums
differing by exactly one. Along a directed path `Floor.cubePos_sum_le` makes the coordinate sum the
INDEX, so this says: only CONSECUTIVE cubes of the path can share a face. That is the step the area
identity `6(k+1) − 2k = 4k+6` turns on, and the reason it is true in `ℕ³` with no further geometry. -/
theorem sum_dist_one_of_shares {x y : Cube} {f : Face}
    (hx : f ∈ faces x) (hy : f ∈ faces y) (hne : x ≠ y) :
    (∑ b, x b) + 1 = (∑ b, y b) ∨ (∑ b, y b) + 1 = (∑ b, x b) := by
  rcases step_rel_of_shares hx hy with h | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact absurd h hne
  · exact Or.inl (sum_step a x).symm
  · exact Or.inr (sum_step a y).symm

/-- The path's `(j+1)`-th cube IS the `j`-th stepped along `s j` — `Floor.cubePos_succ` read as an
equation between cubes rather than coordinatewise. -/
theorem cubePos_succ_eq_step {k : ℕ} (s : Fin k → Fin 3) (j : Fin k) :
    MassGap.cubePos s ((j : ℕ) + 1) = step (s j) (MassGap.cubePos s (j : ℕ)) := by
  funext a
  rw [MassGap.cubePos_succ s j a]
  by_cases h : s j = a
  · subst h
    simp [step_self]
  · have h' : a ≠ s j := fun hh => h hh.symm
    simp [step_other h', h]

/-- **Consecutive cubes of a directed path DO share a face** — the one the step crosses. With
`sum_dist_one_of_shares` this pins the sharing to consecutive pairs exactly: `k` of them. -/
theorem shares_succ {k : ℕ} (s : Fin k → Fin 3) (j : Fin k) :
    ((s j : Fin 3), MassGap.cubePos s ((j : ℕ) + 1))
      ∈ faces (MassGap.cubePos s (j : ℕ)) ∩ faces (MassGap.cubePos s ((j : ℕ) + 1)) := by
  classical
  refine Finset.mem_inter.mpr ⟨?_, ?_⟩
  · exact mem_faces.mpr ⟨s j, Or.inr (by rw [cubePos_succ_eq_step])⟩
  · exact mem_faces.mpr ⟨s j, Or.inl rfl⟩

/-- A step along one axis is not a step along another: the axis is recoverable from the result. -/
theorem step_axis_inj {a b : Fin 3} {x : Cube} (h : step a x = step b x) : a = b := by
  by_contra hne
  have h1 : step a x a = step b x a := congrArg (fun z : Cube => z a) h
  rw [step_self, step_other hne] at h1
  omega

/-- A face names its own two possible owners: the cube at its corner, and the cube one step back
along its axis. Nothing else can carry it. -/
theorem cube_of_face {f : Face} {x : Cube} (h : f ∈ faces x) :
    x = f.2 ∨ step f.1 x = f.2 := by
  obtain ⟨a, ha⟩ := mem_faces.mp h
  rcases ha with ha | ha
  · left; rw [ha]
  · right; rw [ha]

/-- **A FACE BELONGS TO AT MOST TWO CUBES.** This is the `2` of the double count `6(k+1) − 2k`, and
it is derived rather than assumed: by `cube_of_face` an owner is either the corner itself or a step
back along the axis, and `step_injective` makes the second unique. A cube has two sides along each
axis for the same reason, which is why the same `2` appears in `card_faces`. -/
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

/-- **The path visits `k+1` DISTINCT cubes.** Two positions with the same coordinates would have the
same coordinate sum, and `Floor.cubePos_sum_le` makes that sum the index. So the path never revisits
a cube — which is what makes `6(k+1)` the total face count rather than an over-count. -/
theorem cubePos_injOn {k : ℕ} (s : Fin k → Fin 3) :
    Set.InjOn (MassGap.cubePos s) (Finset.range (k + 1)) := by
  intro i hi j hj hij
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hi' := MassGap.cubePos_sum_le s hik
  have hj' := MassGap.cubePos_sum_le s hjk
  rw [hij] at hi'
  omega

/-- The cube configuration has exactly `k+1` elements. -/
theorem card_cubeConfig {k : ℕ} (s : Fin k → Fin 3) :
    (MassGap.cubeConfig s).card = k + 1 := by
  classical
  rw [MassGap.cubeConfig, Finset.card_image_of_injOn (cubePos_injOn s), Finset.card_range]

#print axioms cubePos_injOn
#print axioms card_cubeConfig

/-- The face the `j`-th step crosses: the one shared by cube `j` and cube `j+1`.

DERIVED: `1` is the step — `Floor.cubePos_succ` advances the index by one per step, so `j+1` names
the cube the `j`-th step lands on and nothing is chosen. `3` is `Cube`'s dimension, the arity of the
step alphabet `Fin 3`. -/
def crossFace {k : ℕ} (s : Fin k → Fin 3) (j : Fin k) : Face :=
  ((s j : Fin 3), MassGap.cubePos s ((j : ℕ) + 1))

/-- **THE `k` CROSSING FACES ARE DISTINCT.** This is the `k` of `6(k+1) − 2k`. Distinctness comes
from the SECOND component alone: the crossed face is named by the cube the step lands on, and
`cubePos_injOn` says the path never lands on the same cube twice. The axis never has to be compared. -/
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

/-- Each crossing face really is shared by the two cubes it names — `shares_succ`, restated on
`crossFace` so the two halves of the count speak about the same object. -/
theorem crossFace_shared {k : ℕ} (s : Fin k → Fin 3) (j : Fin k) :
    crossFace s j ∈ faces (MassGap.cubePos s (j : ℕ))
      ∩ faces (MassGap.cubePos s ((j : ℕ) + 1)) :=
  shares_succ s j

/-- The `k` crossing faces, as a `Finset`, with its cardinality. -/
theorem card_crossFaces {k : ℕ} (s : Fin k → Fin 3) :
    (Finset.univ.image (crossFace s)).card = k := by
  classical
  rw [Finset.card_image_of_injective _ (crossFace_injective s), Finset.card_univ,
    Fintype.card_fin]

/-- **ADJACENT CUBES SHARE EXACTLY ONE FACE, AND IT IS THE ONE THE STEP CROSSES.** With
`sum_dist_one_of_shares` ruling out every non-adjacent pair, this is the other half of `|shared| = k`:
each consecutive pair contributes one face and no pair contributes two.

The four cases close on sums and injectivity alone — `step_axis_inj` for the axis, `step_injective`
for the corner, and the coordinate sum for the two impossible ones. -/
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

/-- **THE DOUBLE COUNT.** Count incident (cube, face) pairs two ways: by cube, giving `6` each, and
by face, giving that face's number of owners. This is the identity the area argument turns on, and it
is pure `Finset` bookkeeping — no geometry enters until the two sides are evaluated. -/
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

/-- **The left-hand side, evaluated: a path of `k+1` cubes carries `6(k+1)` incidences.** -/
theorem incidence_left {k : ℕ} (s : Fin k → Fin 3) :
    ∑ x ∈ MassGap.cubeConfig s, (faces x).card = 6 * (k + 1) := by
  classical
  rw [Finset.sum_congr rfl (fun x _ => card_faces x), Finset.sum_const, card_cubeConfig,
    smul_eq_mul]
  ring

/-- **EVERY FACE OF THE CONFIGURATION HAS ONE OR TWO OWNERS.** The upper half is
`card_cubes_with_face_le_two`; the lower is that a face of `C.biUnion faces` is a face of something.
So the right-hand side of the double count is `|B| + |shared|`, which is what turns the identity into
an area. -/
theorem owners_one_or_two (C : Finset Cube) {f : Face} (hf : f ∈ C.biUnion faces) :
    1 ≤ (C.filter (fun x => f ∈ faces x)).card
      ∧ (C.filter (fun x => f ∈ faces x)).card ≤ 2 := by
  classical
  refine ⟨?_, card_cubes_with_face_le_two C f⟩
  obtain ⟨x, hxC, hxf⟩ := Finset.mem_biUnion.mp hf
  exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hxC, hxf⟩⟩

/-- **THE AREA IDENTITY, REDUCED TO THE SHARED COUNT.** Splitting the faces by how many cubes own
them, the double count reads `6(k+1) = |B| + |shared|`, where `B` is every face the configuration
touches and `shared` those with two owners. The BOUNDARY is `B` minus `shared`, so

    |∂C| = |B| − |shared| = (6(k+1) − |shared|) − |shared| = 6(k+1) − 2|shared|,

and with `|shared| = k` — `card_crossFaces` for the lower bound, `sum_dist_one_of_shares` and
`shared_face_eq` for the upper — that is `6k + 6 − 2k = 4k + 6`.

Stated with `|shared|` as a parameter so the arithmetic is separated from the geometry: everything
above is proved, and what this consumes is the one count. -/
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

/-- A face carried by two cubes of the path, one a step from the other, IS one of the `k` crossed
faces. The step's axis is recovered by `step_axis_inj` and its index by the coordinate sum, so no
choice of labelling enters. -/
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

/-- **THE SHARED FACES ARE EXACTLY THE `k` CROSSED ONES.** Forward: two owners must be a step apart
(`step_rel_of_shares`), the pair must be consecutive (`sum_dist_one_of_shares`, through the coordinate
sum), and the face they share is the crossed one (`shared_face_eq`). Backward: each crossed face has
its two distinct owners on the path (`crossFace_shared`, `cubePos_injOn`), and `≤ 2` caps it.

This is where `|shared| = k` stops being an assumption. -/
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

/-- **THE SHARED COUNT IS `k`.** -/
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

/-- **THE AREA IDENTITY: `|∂C| = 4k + 6`.**  Every constant in it is now a theorem of this file:

* `6`  — `card_faces`: a cube has six sides (two per axis).
* `k+1` — `card_cubeConfig`: the path visits `k+1` distinct cubes.
* `2`  — `card_cubes_with_face_le_two`: a face has at most two owners.
* `k`  — `card_sharedFaces`: the shared faces are exactly the `k` crossed ones.

Double counting gives `6(k+1) = |B| + k`, so `|B| = 5k + 6`, and the boundary drops the shared ones
once more: `|∂C| = |B| − k = 4k + 6`.

This closes the last free constant in the ENTROPY FLOOR, which is the only thing in the development
that bounds the gap from below — so it is the one that had to be derived. (What is still marked
`CHOSEN:` elsewhere is the read aperture `16`, the coupling scale `73/100`, a positive offset, and
`WilsonBridge`'s 3-D sublattice; none of them enters `κ₀`.) `VortexCount.floorTerm` ASSUMED the area of a
`k`-step directed vortex surface was `4k + 6`; with the `4` derived, the entropy floor's
`κ₀ = ¼ log 3` has its `¼` — one unit of `log 3` of directional entropy per four units of area. -/
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

/-! ### Distinct paths give distinct SURFACES

`Floor.directed_surface_count` counts cube CONFIGURATIONS. The entropy floor wants surfaces: the
boundaries. Since the boundary map could in principle collapse two configurations onto one surface,
the count only transfers if it is injective — which is proved here, so the `3ᵏ` is a count of
distinct surfaces, each of area `4k+6`. -/

/-- **A FACE NAMES ITS OWN TWO CANDIDATE OWNERS.** Whatever the configuration, the cubes carrying
`(a, step a p)` lie in `{step a p, p}` — the corner itself and the cube one step back. -/
theorem owners_subset_pair (C : Finset Cube) (a : Fin 3) (p : Cube) :
    C.filter (fun y => ((a, step a p) : Face) ∈ faces y) ⊆ {step a p, p} := by
  classical
  intro y hy
  rw [Finset.mem_filter] at hy
  rcases cube_of_face hy.2 with h | h
  · exact Finset.mem_insert.mpr (Or.inl h)
  · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (step_injective a h))

/-- Membership in the boundary, unfolded once. -/
theorem mem_boundaryFaces_iff (C : Finset Cube) (f : Face) :
    f ∈ boundaryFaces C
      ↔ f ∈ C.biUnion faces ∧ (C.filter (fun x => f ∈ faces x)).card = 1 :=
  Finset.mem_filter

/-- A step never returns to where it started: the coordinate sum rises. -/
theorem ne_step (a : Fin 3) (p : Cube) : p ≠ step a p := by
  intro hpx
  have hs := sum_step a p
  rw [← hpx] at hs
  omega

/-- **A CROSSED FACE IS INTERIOR.** If a configuration holds both ends of a step, the face between
them has two owners, so it is not on the boundary. -/
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

/-- **AND THE CONVERSE, WHICH IS THE RECOVERY STEP.** If a configuration holds one end of a step and
the face between them is NOT on its boundary, it holds the other end too — because the face's only
possible owners are those two cubes (`owners_subset_pair`), and a face off the boundary has two. -/
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

/-- The step from `n` to `n+1`: a cube of the first path is a cube of the second, by induction on the
coordinate sum. The crossed face is interior on the left, so by the hypothesis it is interior on the
right; the predecessor is already known to be present there, so the cube itself must be too. -/
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

/-- **DISTINCT DIRECTED PATHS GIVE DISTINCT SURFACES.** Not just distinct cube configurations: the
boundary map itself is injective on them, so no two paths bound the same surface. -/
theorem boundaryFaces_cubeConfig_injective {k : ℕ} :
    Function.Injective (fun s : Fin k → Fin 3 => boundaryFaces (MassGap.cubeConfig s)) := by
  intro s t h
  refine MassGap.cubeConfig_injective ?_
  ext x
  exact ⟨fun hx => mem_of_boundary_eq_aux s t h _ x rfl hx,
    fun hx => mem_of_boundary_eq_aux t s h.symm _ x rfl hx⟩

/-- **THEOREM 7.1, WHOLE.** There are `3ᵏ` distinct surfaces of area exactly `4k+6` arising as
boundaries of directed cube-paths. The count is `Floor.directed_paths_card` transported along the
injection `boundaryFaces_cubeConfig_injective`; the area is `boundary_card_eq`. Together they give
the entropy density `(k log 3)/(4k+6) → ¼ log 3 = κ₀` with no constant supplied at any point. -/
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
