import MassGap.CubeArea
import MassGap.WilsonHypercubic

/-!
# The directed surfaces, as plaquettes of the 4-D lattice

**WHY THIS FILE EXISTS.** `CubeArea` counts `3ᵏ` distinct surfaces of area `4k+6`, but they are
surfaces of the 3-D sublattice: a `CubeArea.Face` is `(axis, corner)` in `ℕ³`. The vortex family the
entropy floor is a statement about lives on the 4-D lattice, where a surface is a set of
`WilsonHypercubic.Plaq 4 n`. Until the two are the same type, "the directed surfaces are a sub-family
of the closed vortex surfaces" cannot be written down, let alone assumed — which is what
`VortexCount`'s count injection needed and did not have.

**WHAT IS PROVED HERE.** An embedding `faceToPlaq` of 3-D faces into 4-D plaquettes — the plane
spanned by the two axes the face's normal is not, at the face's corner, in the time-zero slice — and
its injectivity on any region fitting inside the box. Transporting `CubeArea`'s two results along it:

* `plaqSurface_injective` — distinct directed paths give distinct PLAQUETTE surfaces;
* `card_plaqSurface` — each carries exactly `4k+6` plaquettes.

So `3ᵏ` distinct surfaces of area `4k+6`, stated over the physical lattice's own plaquette
type (`directed_plaq_surfaces_count_and_area`).

**WHAT THE BOX COSTS, and it is the only hypothesis.** `Site 4 n` is periodic: coordinates live in
`Fin n`. A cube-path of `k` steps reaches coordinate `k`, and its faces reach `k+1`, so the embedding
is injective exactly while `k + 1 < n` — the path must fit in the box without wrapping. That is not a
tuning parameter: it is the statement that the surfaces being counted are distinct AS SUBSETS OF THIS
BOX, and it fails only when they are wrapped onto each other. Every theorem below carries it
explicitly.

DERIVED THROUGHOUT: `3` is the dimension of the cube-path's sublattice, `4` the dimension of the
physical lattice, `2` the number of directions a plane needs. The `+1` and `+2` in `planeOf` are the
two axes other than the normal, taken in cyclic order so the pair is a plane and not a degenerate
one. None is a magnitude.
-/

namespace MassGap.SurfaceEmbed

open MassGap.CubeArea MassGap.WilsonHypercubic

/-- The 4-D plane a 3-D face's normal names: the two axes the normal is not, in cyclic order.

DERIVED: `3` is the sublattice dimension the cyclic order runs in; `1` and `2` are the two OTHER
axes, which is what a plane perpendicular to the third consists of. `4` is the physical dimension the
result is read in — the directions are the same three, viewed inside it. -/
def planeOf (a : Fin 3) : Fin 4 × Fin 4 :=
  (⟨((a : ℕ) + 1) % 3, by omega⟩, ⟨((a : ℕ) + 2) % 3, by omega⟩)

/-- The normal is recoverable from the plane, so distinct normals give distinct planes. -/
theorem planeOf_injective : Function.Injective planeOf := by
  intro a b hab
  have h1 : ((a : ℕ) + 1) % 3 = ((b : ℕ) + 1) % 3 := congrArg (fun p => (p.1 : ℕ)) hab
  have ha := a.isLt
  have hb := b.isLt
  exact Fin.ext (by omega)

/-- The corner of a face, placed in the time-zero slice of the 4-D box.

DERIVED: `3` is the sublattice dimension — the first three directions carry the cube-path's
coordinates and the fourth is the time slice the surface sits in, which is `0` because the
construction fixes one slice rather than choosing among them. -/
def siteOf (n : ℕ) [NeZero n] (x : Cube) : Site 4 n :=
  fun μ => if h : (μ : ℕ) < 3 then ⟨x ⟨(μ : ℕ), h⟩ % n, Nat.mod_lt _ (NeZero.pos n)⟩
           else ⟨0, NeZero.pos n⟩

/-- Inside the box the placement is faithful: coordinates below `n` survive the periodic reduction. -/
theorem siteOf_inj_of_lt {n : ℕ} [NeZero n] {x y : Cube}
    (hx : ∀ a, x a < n) (hy : ∀ a, y a < n) (h : siteOf n x = siteOf n y) : x = y := by
  funext a
  have ha : (a : ℕ) < 3 := a.isLt
  have hcong := congrFun h ⟨(a : ℕ), by omega⟩
  have hval := congrArg Fin.val hcong
  simp only [siteOf, ha, dif_pos] at hval
  rw [Nat.mod_eq_of_lt (hx _), Nat.mod_eq_of_lt (hy _)] at hval
  simpa using hval

/-- **A 3-D FACE AS A 4-D PLAQUETTE.**

DERIVED: `4` is the dimension of the physical lattice the Wilson action is written on
(`WilsonHypercubic`), and `3` is the sublattice the cube-path lives in. Neither is chosen here —
both are already fixed by the objects this map runs between. -/
def faceToPlaq (n : ℕ) [NeZero n] (f : Face) : Plaq 4 n := (planeOf f.1, siteOf n f.2)

/-- The embedding is faithful on faces whose corners fit in the box. -/
theorem faceToPlaq_inj_on {n : ℕ} [NeZero n] {f g : Face}
    (hf : ∀ a, f.2 a < n) (hg : ∀ a, g.2 a < n)
    (h : faceToPlaq n f = faceToPlaq n g) : f = g := by
  have h1 : planeOf f.1 = planeOf g.1 := congrArg Prod.fst h
  have h2 : siteOf n f.2 = siteOf n g.2 := congrArg Prod.snd h
  exact Prod.ext (planeOf_injective h1) (siteOf_inj_of_lt hf hg h2)

/-! ### The path stays in the box -/

/-- Each coordinate of the `i`-th cube is at most `i`: the coordinate SUM is `i`
(`Floor.cubePos_sum_le`) and the other coordinates are not negative. -/
theorem cubePos_coord_le {k : ℕ} (s : Fin k → Fin 3) {i : ℕ} (hi : i ≤ k) (a : Fin 3) :
    MassGap.cubePos s i a ≤ i := by
  classical
  have hsum : ∑ b, MassGap.cubePos s i b = i := MassGap.cubePos_sum_le s hi
  have hle : MassGap.cubePos s i a ≤ ∑ b, MassGap.cubePos s i b :=
    Finset.single_le_sum (f := fun b => MassGap.cubePos s i b)
      (fun b _ => Nat.zero_le _) (Finset.mem_univ a)
  omega

/-- Every corner the configuration's faces use is at most `k+1` from the origin, so a box with
`k + 1 < n` holds the whole surface without wrapping. -/
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

/-- **THE DIRECTED SURFACE, AS A SET OF PLAQUETTES OF THE 4-D LATTICE.**

DERIVED: `3` is the step alphabet of the path (`Fin 3`, `Floor.directed_paths_card`'s own) and `4`
the physical dimension. Both are inherited from `faceToPlaq`; nothing is chosen at this definition. -/
noncomputable def plaqSurface (n : ℕ) [NeZero n] {k : ℕ} (s : Fin k → Fin 3) :
    Finset (Plaq 4 n) :=
  (boundaryFaces (MassGap.cubeConfig s)).image (faceToPlaq n)

/-- The boundary's faces all fit in a box with `k + 1 < n`. -/
theorem boundary_corner_lt {n k : ℕ} (hk : k + 1 < n) (s : Fin k → Fin 3)
    {f : Face} (hf : f ∈ boundaryFaces (MassGap.cubeConfig s)) (a : Fin 3) :
    f.2 a < n := by
  classical
  have hfB : f ∈ (MassGap.cubeConfig s).biUnion faces := (Finset.mem_filter.mp hf).1
  obtain ⟨x, hx, hfx⟩ := Finset.mem_biUnion.mp hfB
  have := face_corner_le s hx hfx a
  omega

/-- **THE AREA SURVIVES THE EMBEDDING.** `4k+6` plaquettes, because the embedding is injective on
exactly the faces this surface uses. -/
theorem card_plaqSurface {n k : ℕ} [NeZero n] (hk : k + 1 < n) (s : Fin k → Fin 3) :
    (plaqSurface n s).card = 4 * k + 6 := by
  classical
  rw [plaqSurface, Finset.card_image_of_injOn, boundary_card_eq s]
  intro f hf g hg h
  exact faceToPlaq_inj_on (boundary_corner_lt hk s hf) (boundary_corner_lt hk s hg) h

/-- **DISTINCT PATHS GIVE DISTINCT PLAQUETTE SURFACES.** `CubeArea.boundaryFaces_cubeConfig_injective`
transported along the embedding: the images differ because the embedding is faithful on the faces
either surface uses, so a common image would force a common boundary. -/
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

/-- **THEOREM 7.1 OVER THE PHYSICAL LATTICE.** In any 4-D box large enough to hold a `k`-step path,
there are `3ᵏ` distinct surfaces of plaquettes, each of area exactly `4k+6`. This is the
statement `VortexCount`'s count injection needs, at the type the vortex family has. -/
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

/-- **AND THE COUNT INJECTION, OVER PLAQUETTES.** If the physical vortex family `V` contains the
directed surfaces, it has at least `3ᵏ` members. Both of the hypotheses
`VortexCount.three_pow_le_card_of_embeds` could not previously discharge — the map and its
injectivity — are theorems here; what is left is the containment, which is the physics. -/
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

/-- **THE COUNT INJECTION NEEDS THE BOX TO GROW, AND THIS IS WHERE THAT BECOMES VISIBLE.**

`VortexCount.junction_of_physical_count` consumes `hM : ∀ k, 3^k ≤ M k` — a bound at EVERY `k`,
because the free-energy density it extracts is a `k → ∞` limit. The embedding above is injective only
while `k + 1 < n`. No fixed box satisfies both: at `k = n` the surfaces wrap and stop being distinct
subsets.

So the count injection is stated along a SEQUENCE of boxes, one per `k`, each large enough to hold
its own path. That is not a weakening introduced here — the vortex free-energy density is a
thermodynamic-limit quantity, so a `k`-indexed family of boxes is what the physical statement was
always about. It does mean the junction's `hM` cannot be discharged inside one finite volume, which
is the same wall the infinite-volume question hits elsewhere in this development, reached here from
the combinatorial side. -/
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
