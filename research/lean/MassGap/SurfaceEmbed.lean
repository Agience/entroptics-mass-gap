import MassGap.CubeArea
import MassGap.WilsonHypercubic

/-!
# MassGap.SurfaceEmbed — directed cube surfaces as plaquettes of the 4-D lattice

`CubeArea` counts `3ᵏ` distinct surfaces of area `4k+6`, over a 3-D sublattice: a `CubeArea.Face` is
a pair `(axis, corner)` with the corner in `ℕ³`. A surface on the physical lattice is a
`Finset (Plaq 4 n)`. This module supplies a map between the two types and transports both counts
along it.

The map. `planeOf` sends a face normal in `Fin 3` to the pair of remaining axes, taken in cyclic
order and read inside `Fin 4`. `siteOf` places a cube corner in the box, reducing the three cube
coordinates mod `n` and setting the fourth to `0`. `faceToPlaq` pairs them, and `plaqSurface` is the
image of a directed path's boundary faces under it.

The transported results:

* `card_plaqSurface` — a `k`-step path's plaquette surface has exactly `4 * k + 6` plaquettes;
* `plaqSurface_injective` — distinct paths give distinct plaquette surfaces;
* `directed_plaq_surfaces_count_and_area` — both together, as a family of `3 ^ k` surfaces each of
  that size;
* `three_pow_le_card_of_plaq_subfamily` — any family containing all of them has at least `3 ^ k`
  members;
* `three_pow_le_card_along_boxes` — the same bound at every `k`, along a sequence of boxes.

Scope: the box. `Site 4 n` is periodic, with coordinates in `Fin n`. A `k`-step cube path reaches
coordinate `k` and its faces reach `k + 1`, so `siteOf` is faithful, and the embedding injective,
while `k + 1 < n`. Every theorem below carries that hypothesis explicitly. One fixed `n` therefore
covers only the `k` below it, which is why `three_pow_le_card_along_boxes` indexes the box by `k`:
that is the shape a `k → ∞` consumer such as `VortexCount.junction_of_physical_count` takes.

Scope: the slice. `siteOf` sets the fourth coordinate to `0`, so every surface built here lies in one
time slice and the plaquettes it contains all have a plane drawn from the first three axes.

Scope: containment. `three_pow_le_card_of_plaq_subfamily` takes the containment of the directed
surfaces in `V` as a hypothesis; nothing here proves that a physical vortex family contains them.
-/

namespace MassGap.SurfaceEmbed

open MassGap.CubeArea MassGap.WilsonHypercubic

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

The coordinate sum is exactly `i` (`Floor.cubePos_sum_le`), and a single term of a sum of naturals is
at most the sum. The bound is on each coordinate separately, not on their sum.

DERIVED: `3` is the step alphabet `Fin 3` of the cube path; it is the only numeral in the
statement. -/
theorem cubePos_coord_le {k : ℕ} (s : Fin k → Fin 3) {i : ℕ} (hi : i ≤ k) (a : Fin 3) :
    MassGap.cubePos s i a ≤ i := by
  classical
  have hsum : ∑ b, MassGap.cubePos s i b = i := MassGap.cubePos_sum_le s hi
  have hle : MassGap.cubePos s i a ≤ ∑ b, MassGap.cubePos s i b :=
    Finset.single_le_sum (f := fun b => MassGap.cubePos s i b)
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
    (hx : x ∈ MassGap.cubeConfig s) (hf : f ∈ faces x) (a : Fin 3) :
    f.2 a ≤ k + 1 := by
  classical
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hbase : MassGap.cubePos s i a ≤ k := le_trans (cubePos_coord_le s hik a) hik
  obtain ⟨b, hb⟩ := mem_faces.mp hf
  rcases hb with rfl | rfl
  · show MassGap.cubePos s i a ≤ k + 1
    omega
  · show step b (MassGap.cubePos s i) a ≤ k + 1
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
  (boundaryFaces (MassGap.cubeConfig s)).image (faceToPlaq n)

/-- Under `hk : k + 1 < n`, every coordinate of every boundary face's corner is below `n`.

`face_corner_le` bounds the corner by `k + 1`, and `hk` puts that below `n`. This is the hypothesis
`faceToPlaq_inj_on` consumes, produced for the faces a surface actually uses.

DERIVED: `1` is the single step in `k + 1`, the reach of a face beyond its cube. `3` is the step
alphabet `Fin 3` of the path. -/
theorem boundary_corner_lt {n k : ℕ} (hk : k + 1 < n) (s : Fin k → Fin 3)
    {f : Face} (hf : f ∈ boundaryFaces (MassGap.cubeConfig s)) (a : Fin 3) :
    f.2 a < n := by
  classical
  have hfB : f ∈ (MassGap.cubeConfig s).biUnion faces := (Finset.mem_filter.mp hf).1
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
  show boundaryFaces (MassGap.cubeConfig s) = boundaryFaces (MassGap.cubeConfig t)
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
size via `Floor.directed_paths_card`, and `card_plaqSurface` gives each member's.

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
      MassGap.directed_paths_card]
  · intro F hF
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hF
    exact card_plaqSurface hk s

/-- If a family `V` of plaquette sets contains `plaqSurface n s` for every `k`-step path `s`, and
`k + 1 < n`, then `3 ^ k ≤ V.card`.

The image of the path space is a subset of `V` and has size `3 ^ k` by `plaqSurface_injective` and
`Floor.directed_paths_card`, so `Finset.card_le_card` finishes.

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
          MassGap.directed_paths_card]
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

end MassGap.SurfaceEmbed
