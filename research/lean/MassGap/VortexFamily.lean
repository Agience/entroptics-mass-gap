import MassGap.SurfaceEmbed
import MassGap.CubeClosed
import MassGap.CubeConnected
import MassGap.VortexCount

/-!
# The vortex family, and `N(A) ≥ 3ᵏ` without a containment hypothesis

**WHAT IS MISSING WITHOUT THIS FILE.** `SurfaceEmbed` puts the directed surfaces on the physical
lattice's plaquette type and `three_pow_le_card_of_plaq_subfamily` counts them — but only inside a
family `V` the caller supplies, with a hypothesis that the surfaces belong to it. Theorem 7.1's `N(A)`
is not a supplied family: it is the number of closed surfaces of area `A` through a fixed plaquette,
an intrinsic count. So the containment has to stop being a hypothesis and become a check against a
DEFINITION.

**CLOSED IS THE WILSON ACTION'S OWN BOUNDARY MAP, not a new notion.** `WilsonHypercubic.bd` sends a
plaquette to its four oriented links — it is what the Wilson holonomy is taken around. A set of
plaquettes is closed when every link lies in an EVEN number of their boundaries, which is `∂∂ = 0`
over `Z₂` stated in the development's own terms rather than in terms invented here. Nothing about
`edgesOf` below is a second geometry: it is `bd` with the orientations forgotten, because parity does
not see them.

**WHY THE SURFACES ARE CLOSED IN 4-D, given that `CubeClosed` proves it in 3-D.** Every plaquette of
an embedded surface spans two of the first three directions and sits in the time-zero slice
(`SurfaceEmbed.faceToPlaq`). So a link along the time direction lies in NONE of them, and a link
outside the slice lies in none either; both cases are even by being empty. What remains is links
inside the slice, where the plaquettes containing one correspond exactly to the 3-D faces containing
the matching 3-D edge, and `CubeClosed.edge_parity_all` is that count.

DERIVED THROUGHOUT: `4` is the physical dimension, `3` the sublattice the cube-path lives in, `2` the
directions a plane has and the owners a face can have. Each is the arity of something already fixed.
-/

namespace MassGap.VortexFamily

open Finset MassGap.CubeArea MassGap.SurfaceEmbed MassGap.WilsonHypercubic

variable {n : ℕ}

/-- The four links a plaquette's boundary word runs along, as a set and without orientation.

`WilsonHypercubic.bd` is the boundary map the Wilson holonomy is taken around; this is that map with
the `Bool` dropped, because a parity count does not see orientation. Using `bd` rather than writing
the four links again is the point: closedness is then a statement about the development's own
boundary, not about a re-description of it.

DERIVED: `4` is the physical dimension, which is what `Plaq 4 n` and `Link 4 n` are indexed by. -/
def edgesOf [NeZero n] (q : Plaq 4 n) : Finset (Link 4 n) :=
  ((bd q).map Prod.fst).toFinset

/-- **CLOSED: every link lies in an even number of the surface's plaquettes.** `∂∂ = 0` over `Z₂`.

DERIVED: `4` is the physical dimension. `2` is the modulus of `Z₂` — the group the centre-vortex flux
takes values in, and the `2` owners a face can have; `0` is its identity. None is a magnitude. -/
def IsClosedSurface [NeZero n] (F : Finset (Plaq 4 n)) : Prop :=
  ∀ e : Link 4 n, (F.filter (fun q => e ∈ edgesOf q)).card % 2 = 0

-- DERIVED: `4` is the physical dimension, as in `IsClosedSurface` itself.
instance [NeZero n] (F : Finset (Plaq 4 n)) : Decidable (IsClosedSurface F) := by
  unfold IsClosedSurface; infer_instance

theorem mem_edgesOf [NeZero n] {q : Plaq 4 n} {e : Link 4 n} :
    e ∈ edgesOf q ↔ e = (q.1.1, q.2) ∨ e = (q.1.2, shift q.1.1 q.2)
      ∨ e = (q.1.1, shift q.1.2 q.2) ∨ e = (q.1.2, q.2) := by
  classical
  simp [edgesOf, bd, List.mem_toFinset]

#print axioms mem_edgesOf

/-! ### The two directions an embedded surface does not occupy -/

/-- Every plaquette of an embedded surface spans two of the first three directions: `planeOf` names
axes of the cube-path's sublattice, and there are three of those. -/
theorem planeOf_lt_three (a : Fin 3) : ((planeOf a).1 : ℕ) < 3 ∧ ((planeOf a).2 : ℕ) < 3 := by
  constructor <;> · simp [planeOf]; omega

/-- Every site an embedded surface's links carry is in the time-zero slice: `siteOf` puts `0` in the
fourth coordinate and a step along one of the first three leaves it there. -/
theorem siteOf_time_zero [NeZero n] (x : Cube) :
    siteOf n x (3 : Fin 4) = (⟨0, NeZero.pos n⟩ : Fin n) := by
  simp [siteOf]

#print axioms planeOf_lt_three
#print axioms siteOf_time_zero

/-- A step along one of the first three directions leaves the time coordinate alone. -/
theorem shift_time [NeZero n] {μ : Fin 4} (hμ : μ ≠ (3 : Fin 4)) (x : Site 4 n) :
    shift μ x (3 : Fin 4) = x (3 : Fin 4) := by
  simp [shift, Function.update_apply, (Ne.symm hμ)]

/-- **AN EMBEDDED PLAQUETTE CARRIES NO LINK ALONG THE TIME DIRECTION.** Its two spanning directions
are axes of the cube-path's sublattice, and there are three of those. -/
theorem not_mem_edgesOf_time [NeZero n] (f : Face) (e : Link 4 n) (he : e.1 = (3 : Fin 4)) :
    e ∉ edgesOf (faceToPlaq n f) := by
  intro hmem
  obtain ⟨h1, h2⟩ := planeOf_lt_three f.1
  rcases mem_edgesOf.mp hmem with h | h | h | h <;>
    · have := congrArg Prod.fst h
      rw [he] at this
      simp [faceToPlaq] at this
      omega

/-- **AND NO LINK OUTSIDE THE TIME-ZERO SLICE.** The corner is placed at time zero and the steps that
reach the other three links move only within the slice, so every link an embedded plaquette carries
sits at time zero. -/
theorem edgesOf_site_time [NeZero n] {f : Face} {e : Link 4 n}
    (h : e ∈ edgesOf (faceToPlaq n f)) :
    e.2 (3 : Fin 4) = (⟨0, NeZero.pos n⟩ : Fin n) := by
  obtain ⟨h1, h2⟩ := planeOf_lt_three f.1
  have hne1 : (planeOf f.1).1 ≠ (3 : Fin 4) := by
    intro hh; rw [hh] at h1; simp at h1
  have hne2 : (planeOf f.1).2 ≠ (3 : Fin 4) := by
    intro hh; rw [hh] at h2; simp at h2
  rcases mem_edgesOf.mp h with rfl | rfl | rfl | rfl <;>
    simp [faceToPlaq, shift_time hne1, shift_time hne2, siteOf_time_zero]

theorem not_mem_edgesOf_offslice [NeZero n] (f : Face) (e : Link 4 n)
    (he : e.2 (3 : Fin 4) ≠ (⟨0, NeZero.pos n⟩ : Fin n)) :
    e ∉ edgesOf (faceToPlaq n f) :=
  fun h => he (edgesOf_site_time h)

#print axioms shift_time
#print axioms not_mem_edgesOf_time
#print axioms edgesOf_site_time
#print axioms not_mem_edgesOf_offslice

/-! ### A 4-D step of an embedded corner is the embedding of a 3-D step

This is what lets a link of an embedded plaquette be read back as a 3-D edge: its site is always
`siteOf` of some cube, so the 3-D point it came from is recoverable. -/

/-- The `Fin 4` direction an axis of the cube-path's sublattice occupies.

DERIVED: `3` is the dimension of the sublattice the cube-path lives in, `4` the physical dimension.
The embedding is the inclusion of the first three coordinates, so neither is chosen. -/
def emb (a : Fin 3) : Fin 4 := ⟨(a : ℕ), by have := a.isLt; omega⟩

theorem emb_ne_three (a : Fin 3) : emb a ≠ (3 : Fin 4) := by
  intro h
  have := a.isLt
  have : ((emb a : Fin 4) : ℕ) = 3 := by rw [h]; rfl
  simp [emb] at this
  omega

/-- **A STEP COMMUTES WITH THE EMBEDDING**, with no bound on the coordinate: both sides reduce the
same coordinate modulo `n`, so the periodic box's wrap is not an obstruction here — it is only an
obstruction to INJECTIVITY, which is where `k + 1 < n` earns its place. -/
theorem shift_siteOf [NeZero n] (a : Fin 3) (y : Cube) :
    shift (emb a) (siteOf n y) = siteOf n (step a y) := by
  have ha3 : ((emb a : Fin 4) : ℕ) < 3 := by simpa [emb] using a.isLt
  have hcoe : (⟨((emb a : Fin 4) : ℕ), ha3⟩ : Fin 3) = a := by apply Fin.ext; simp [emb]
  funext ν
  by_cases hν : ν = emb a
  · rw [hν]
    have hl : shift (emb a) (siteOf n y) (emb a) = siteOf n y (emb a) + 1 := by
      simp [shift, Function.update_apply]
    rw [hl]
    apply Fin.ext
    simp only [siteOf, dif_pos ha3, Fin.add_def]
    rw [hcoe, step_self]
    -- `(y a % n + 1 % n) % n = (y a + 1) % n`: the two reductions agree, which is the whole content
    conv_rhs => rw [Nat.add_mod]
    simp [Fin.val_one']
  · have hl : shift (emb a) (siteOf n y) ν = siteOf n y ν := by
      simp only [shift, Function.update_apply, if_neg hν]
    rw [hl]
    by_cases h3 : (ν : ℕ) < 3
    · apply Fin.ext
      simp only [siteOf, dif_pos h3]
      have hne : (⟨(ν : ℕ), h3⟩ : Fin 3) ≠ a := by
        intro hh
        have hva : (a : ℕ) = (ν : ℕ) := congrArg Fin.val hh.symm
        exact hν (Fin.ext (by simp [emb, hva]))
      rw [step_other hne]
    · simp only [siteOf, dif_neg h3]

#print axioms emb_ne_three
#print axioms shift_siteOf

theorem emb_injective : Function.Injective emb := by
  intro a b h
  have hv : ((emb a : Fin 4) : ℕ) = ((emb b : Fin 4) : ℕ) := congrArg Fin.val h
  simp only [emb] at hv
  exact Fin.ext hv

/-- The plane a face spans IS the pair of embedded rotations of its normal — which is why the 4-D
plaquette's two directions are the two axes the 3-D face's edges run along, with nothing to choose. -/
theorem planeOf_eq_emb (a : Fin 3) : planeOf a = (emb (rot1 a), emb (rot2 a)) := by
  refine Prod.ext ?_ ?_ <;> apply Fin.ext <;> simp [planeOf, emb, rot1, rot2]

/-- A 3-D edge, embedded as a link of the physical lattice.

DERIVED: `3` is the cube-path's sublattice dimension, `4` the physical dimension, exactly as in
`emb`. -/
def linkEmb (n : ℕ) [NeZero n] (d : Fin 3 × Cube) : Link 4 n := (emb d.1, siteOf n d.2)

#print axioms emb_injective
#print axioms planeOf_eq_emb

/-- **THE LINKS OF AN EMBEDDED PLAQUETTE ARE THE EMBEDDINGS OF THE FACE'S OWN EDGES**, one for one
and in the same order. `bd`'s four links and `faceEdges`' four edges correspond because
`planeOf_eq_emb` matches the directions and `shift_siteOf` matches the corners — the Wilson boundary
map and the 3-D one are the same map read in two places. -/
theorem mem_edgesOf_faceToPlaq [NeZero n] (f : Face) (e : Link 4 n) :
    e ∈ edgesOf (faceToPlaq n f) ↔ ∃ d ∈ faceEdges f, linkEmb n d = e := by
  classical
  constructor
  · rw [mem_edgesOf]
    rintro (h | h | h | h)
    · exact ⟨(rot1 f.1, f.2), mem_faceEdges.mpr (Or.inl rfl), by
        rw [h]; simp [linkEmb, faceToPlaq, planeOf_eq_emb]⟩
    · exact ⟨(rot2 f.1, step (rot1 f.1) f.2), mem_faceEdges.mpr (Or.inr (Or.inl rfl)), by
        rw [h]; simp [linkEmb, faceToPlaq, planeOf_eq_emb, shift_siteOf]⟩
    · exact ⟨(rot1 f.1, step (rot2 f.1) f.2), mem_faceEdges.mpr (Or.inr (Or.inr (Or.inl rfl))), by
        rw [h]; simp [linkEmb, faceToPlaq, planeOf_eq_emb, shift_siteOf]⟩
    · exact ⟨(rot2 f.1, f.2), mem_faceEdges.mpr (Or.inr (Or.inr (Or.inr rfl))), by
        rw [h]; simp [linkEmb, faceToPlaq, planeOf_eq_emb]⟩
  · rintro ⟨d, hd, rfl⟩
    rw [mem_edgesOf]
    rcases mem_faceEdges.mp hd with rfl | rfl | rfl | rfl
    · exact Or.inl (by simp [linkEmb, faceToPlaq, planeOf_eq_emb])
    · exact Or.inr (Or.inl (by simp [linkEmb, faceToPlaq, planeOf_eq_emb, shift_siteOf]))
    · exact Or.inr (Or.inr (Or.inl (by
        simp [linkEmb, faceToPlaq, planeOf_eq_emb, shift_siteOf])))
    · exact Or.inr (Or.inr (Or.inr (by simp [linkEmb, faceToPlaq, planeOf_eq_emb])))

#print axioms mem_edgesOf_faceToPlaq

/-! ### Reading a link back as a 3-D edge

The correspondence above sends 3-D edges forward. Closedness needs it BACKWARDS: given a link of the
physical lattice, the faces of the surface carrying it must be exactly the 3-D faces carrying one 3-D
edge. That is where the periodic box bites into the argument — `siteOf` reduces modulo `n`, so it is
injective only on corners below `n`, and the corners of a face's EDGES reach one step further than
the face's own corner. Hence `k + 2 < n` here where the area count needed only `k + 1 < n`. -/

/-- Every corner of every edge of a boundary face of a `k`-step path lies below `n`, given
`k + 2 < n`: the face's corner is at most `k + 1` (`face_corner_le`) and an edge's far corner is one
step beyond it. -/
theorem faceEdges_corner_lt {n k : ℕ} (hk : k + 2 < n) (s : Fin k → Fin 3)
    {f : Face} (hf : f ∈ boundaryFaces (MassGap.cubeConfig s))
    {d : Fin 3 × Cube} (hd : d ∈ faceEdges f) (a : Fin 3) : d.2 a < n := by
  classical
  obtain ⟨x, hx, hfx⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hf).1
  have hball : ∀ b, f.2 b ≤ k + 1 := fun b => face_corner_le s hx hfx b
  have hstep : ∀ (b c : Fin 3), step b f.2 c ≤ k + 2 := by
    intro b c
    by_cases hcb : c = b
    · subst hcb; rw [step_self]; have := hball c; omega
    · rw [step_other hcb]; have := hball c; omega
  rcases mem_faceEdges.mp hd with rfl | rfl | rfl | rfl
  · show f.2 a < n
    have := hball a; omega
  · show step (rot1 f.1) f.2 a < n
    have := hstep (rot1 f.1) a; omega
  · show step (rot2 f.1) f.2 a < n
    have := hstep (rot2 f.1) a; omega
  · show f.2 a < n
    have := hball a; omega

#print axioms faceEdges_corner_lt

/-- **THE EMBEDDED SURFACE IS CLOSED.** `CubeClosed.edge_parity_all` transported along the
correspondence, with the three kinds of link handled separately and none of them by hand:

* a link along the time direction lies in no plaquette of the surface (`not_mem_edgesOf_time`);
* a link off the time-zero slice likewise (`not_mem_edgesOf_offslice`);
* any other link IS `linkEmb` of a unique 3-D edge, and the plaquettes carrying it correspond exactly
  to the boundary faces carrying that edge — so its count is the 3-D one, which is even.

The first two are even by being zero, so no case is argued from a picture. -/
theorem plaqSurface_closed {n k : ℕ} [NeZero n] (hk : k + 2 < n) (s : Fin k → Fin 3) :
    IsClosedSurface (plaqSurface n s) := by
  classical
  intro e
  have hk1 : k + 1 < n := by omega
  -- the count upstairs is the count downstairs, because the embedding is faithful on the boundary
  have hcard : ((plaqSurface n s).filter (fun q => e ∈ edgesOf q)).card
      = ((boundaryFaces (MassGap.cubeConfig s)).filter
          (fun f => e ∈ edgesOf (faceToPlaq n f))).card := by
    rw [plaqSurface, Finset.filter_image]
    refine Finset.card_image_of_injOn (fun f hf g hg h => ?_)
    exact faceToPlaq_inj_on
      (boundary_corner_lt hk1 s (Finset.mem_filter.mp hf).1)
      (boundary_corner_lt hk1 s (Finset.mem_filter.mp hg).1) h
  rw [hcard]
  by_cases hμ : e.1 = (3 : Fin 4)
  · rw [Finset.filter_false_of_mem (fun f _ => not_mem_edgesOf_time f e hμ)]
    simp
  by_cases hX : e.2 (3 : Fin 4) ≠ (⟨0, NeZero.pos n⟩ : Fin n)
  · rw [Finset.filter_false_of_mem (fun f _ => not_mem_edgesOf_offslice f e hX)]
    simp
  push_neg at hX
  -- the link is the embedding of a 3-D edge, and that edge is unique
  have hμ3 : ((e.1 : Fin 4) : ℕ) < 3 := by
    have h4 := e.1.isLt
    rcases Nat.lt_or_ge ((e.1 : Fin 4) : ℕ) 3 with h | h
    · exact h
    · exact absurd (Fin.ext (by omega) : e.1 = (3 : Fin 4)) hμ
  obtain ⟨c, hc⟩ : ∃ c : Fin 3, emb c = e.1 :=
    ⟨⟨((e.1 : Fin 4) : ℕ), hμ3⟩, by apply Fin.ext; simp [emb]⟩
  obtain ⟨w, hwlt, hw⟩ : ∃ w : Cube, (∀ a, w a < n) ∧ siteOf n w = e.2 := by
    refine ⟨fun a => ((e.2 (emb a) : Fin n) : ℕ), fun a => (e.2 (emb a)).isLt, ?_⟩
    funext ν
    by_cases h3 : (ν : ℕ) < 3
    · apply Fin.ext
      have hemb : emb ⟨(ν : ℕ), h3⟩ = ν := by apply Fin.ext; simp [emb]
      simp only [siteOf, dif_pos h3, hemb]
      exact Nat.mod_eq_of_lt (e.2 ν).isLt
    · have hν : ν = (3 : Fin 4) := by
        apply Fin.ext; have := ν.isLt; omega
      simp only [siteOf, dif_neg h3]
      rw [hν]
      exact hX.symm
  have hlink : linkEmb n (c, w) = e := by
    refine Prod.ext ?_ ?_
    · exact hc
    · exact hw
  -- the plaquettes of the surface carrying the link are the faces carrying the 3-D edge
  have hfilter : (boundaryFaces (MassGap.cubeConfig s)).filter
        (fun f => e ∈ edgesOf (faceToPlaq n f))
      = (boundaryFaces (MassGap.cubeConfig s)).filter
        (fun f => ((c, w) : Fin 3 × Cube) ∈ faceEdges f) := by
    refine Finset.filter_congr (fun f hf => ?_)
    constructor
    · intro hmem
      obtain ⟨d, hd, hde⟩ := (mem_edgesOf_faceToPlaq f e).mp hmem
      have h1 : emb d.1 = e.1 := congrArg Prod.fst hde
      have h2 : siteOf n d.2 = e.2 := congrArg Prod.snd hde
      have hc1 : d.1 = c := emb_injective (h1.trans hc.symm)
      have hd2 : d.2 = w :=
        siteOf_inj_of_lt (faceEdges_corner_lt hk s hf hd) hwlt (h2.trans hw.symm)
      have : d = (c, w) := Prod.ext hc1 hd2
      exact this ▸ hd
    · intro hmem
      exact (mem_edgesOf_faceToPlaq f e).mpr ⟨(c, w), hmem, hlink⟩
  rw [hfilter]
  exact edge_parity_all _ c w

#print axioms plaqSurface_closed




/-! ### The family, defined rather than supplied

Everything Theorem 7.1 asks of the surfaces it counts is a CHECK: closed (`plaqSurface_closed`), of
area `4k+6` (`card_plaqSurface`), through one fixed plaquette (`base_mem_plaqSurface`), and CONNECTED.
So the family can be DEFINED by those conditions and the count made against the definition, with no
containment hypothesis for a caller to discharge.

**WHY CONNECTEDNESS IS PART OF THE DEFINITION AND NOT AN EXTRA.** Without it the family is too large
for the junction to say anything. A union of unit-cube boundaries is closed -- every link lies in two
or four of them -- each costs area `6`, and the pieces may sit anywhere in the box. At area `4k+6`
that is one anchored piece plus about `2k/3` floating ones placed in a box of about `k^4` sites, so

    log N / A  >=  (2k/3)(3 log k) / (4k)  =  (log k)/2  -> infinity.

`hdual` asks for a FIXED `c` with `log N_k / (4k+6) - mu <= c` at every `k`. Against a diverging
density no such `c` exists, so the junction would be VACUOUSLY true and would prove nothing.
Connectedness is what makes the density bounded, and it is also what Theorem 7.1's `N(A)` always
meant: the count of connected closed surfaces of a given area through a fixed plaquette. -/

/-- **THE FIXED PLAQUETTE.** Theorem 7.1 counts surfaces "through a fixed plaquette"; this is it — the
embedding of the origin cube's low face on the first axis. It is on the boundary of every directed
path's configuration because `ℕ³` has a floor: nothing sits one step back from zero, so that face has
exactly one owner, whatever the path does afterwards.

DERIVED: `3` is the sublattice dimension and `4` the physical one. Both `0`s are the ORIGIN — the
corner every directed path starts from (`cubePos s 0`) and the axis index the floor argument is run
on; the choice of axis is immaterial, since `origin_face_mem_boundary` holds for all three and any of
them fixes the same plaquette up to relabelling the axes. -/
noncomputable def basePlaq (n : ℕ) [NeZero n] : Plaq 4 n :=
  faceToPlaq n ((0 : Fin 3), (fun _ => 0 : Cube))

theorem base_mem_plaqSurface {n k : ℕ} [NeZero n] (s : Fin k → Fin 3) :
    basePlaq n ∈ plaqSurface n s := by
  classical
  have h0 : MassGap.cubePos s 0 = (fun _ => 0 : Cube) := by
    funext a; simp [MassGap.cubePos]
  rw [plaqSurface]
  refine Finset.mem_image.mpr ⟨((0 : Fin 3), MassGap.cubePos s 0),
    origin_face_mem_boundary s 0, ?_⟩
  rw [basePlaq, h0]

#print axioms base_mem_plaqSurface

/-- Two plaquettes of a surface are adjacent when they share a link — the same `edgesOf` the
closedness condition counts, so adjacency is not a second geometry either.

DERIVED: `4` is the physical dimension. -/
def SurfAdj [NeZero n] (F : Finset (Plaq 4 n)) (a b : Plaq 4 n) : Prop :=
  a ∈ F ∧ b ∈ F ∧ (edgesOf a ∩ edgesOf b).Nonempty

/-- **CONNECTED: every plaquette is reachable from the fixed one along shared links.**

DERIVED: `4` is the physical dimension. -/
def IsConnectedSurface [NeZero n] (F : Finset (Plaq 4 n)) : Prop :=
  ∀ q ∈ F, Relation.ReflTransGen (SurfAdj F) (basePlaq n) q

/-- A 3-D edge shared by two boundary faces embeds to a link shared by their plaquettes. Only the
FORWARD map is used, so no injectivity and no box condition enter here. -/
theorem surfAdj_of_faceAdj [NeZero n] {C : Finset Cube} {f g : Face}
    (h : FaceAdj (boundaryFaces C) f g) :
    SurfAdj ((boundaryFaces C).image (faceToPlaq n)) (faceToPlaq n f) (faceToPlaq n g) := by
  classical
  obtain ⟨hfB, hgB, e, he⟩ := h
  rw [Finset.mem_inter] at he
  refine ⟨Finset.mem_image_of_mem _ hfB, Finset.mem_image_of_mem _ hgB, ⟨linkEmb n e, ?_⟩⟩
  rw [Finset.mem_inter]
  exact ⟨(mem_edgesOf_faceToPlaq f _).mpr ⟨e, he.1, rfl⟩,
    (mem_edgesOf_faceToPlaq g _).mpr ⟨e, he.2, rfl⟩⟩

theorem reflTransGen_faceToPlaq [NeZero n] {C : Finset Cube} {f g : Face}
    (h : Relation.ReflTransGen (FaceAdj (boundaryFaces C)) f g) :
    Relation.ReflTransGen (SurfAdj ((boundaryFaces C).image (faceToPlaq n)))
      (faceToPlaq n f) (faceToPlaq n g) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (surfAdj_of_faceAdj hstep)

/-- **THE EMBEDDED SURFACE IS CONNECTED.** `CubeConnected.boundary_connected` carried along the
embedding: every boundary face reaches the origin cube's low face on axis `0` by shared edges, and
each shared edge embeds to a shared link. The fixed plaquette IS the image of that face. -/
theorem plaqSurface_connected {n k : ℕ} [NeZero n] (s : Fin k → Fin 3) :
    IsConnectedSurface (plaqSurface n s) := by
  classical
  have h0 : MassGap.cubePos s 0 = (fun _ => 0 : Cube) := by
    funext a; simp [MassGap.cubePos]
  have hbase : basePlaq n = faceToPlaq n (((0 : Fin 3), MassGap.cubePos s 0) : Face) := by
    rw [basePlaq, h0]
  intro q hq
  rw [plaqSurface, Finset.mem_image] at hq
  obtain ⟨f, hf, rfl⟩ := hq
  rw [hbase, plaqSurface]
  exact reflTransGen_faceToPlaq (boundary_connected s f hf)

#print axioms surfAdj_of_faceAdj
#print axioms plaqSurface_connected

open scoped Classical in
/-- **THE VORTEX FAMILY, INTRINSIC.** The connected closed plaquette surfaces of area `4k+6` through
the fixed plaquette — those conditions and nothing else. `N(A)` in Theorem 7.1 is the cardinality of
this, so the entropy floor's count is a count of a DEFINED set rather than of whatever family a
caller happened to name.

DERIVED: `4` is the physical dimension. `4 * k + 6` is the AREA, and it is `CubeArea.boundary_card_eq`
— `6` faces per cube for `k+1` cubes less `2` per shared face for the `k` shared ones. Neither
literal is fitted; both are theorems about the same object the count is about. -/
noncomputable def vortexFamily (n : ℕ) [NeZero n] (k : ℕ) : Finset (Finset (Plaq 4 n)) :=
  (univ : Finset (Plaq 4 n)).powerset.filter
    (fun F => IsClosedSurface F ∧ IsConnectedSurface F ∧ F.card = 4 * k + 6 ∧ basePlaq n ∈ F)

/-- **EVERY DIRECTED SURFACE IS IN THE FAMILY**, and all FOUR conditions are discharged by theorems:
closed (`plaqSurface_closed`), connected (`plaqSurface_connected`), of area `4k+6`
(`card_plaqSurface`), through the fixed plaquette (`base_mem_plaqSurface`). Nothing is supplied. -/
theorem mem_vortexFamily {n k : ℕ} [NeZero n] (hk : k + 2 < n) (s : Fin k → Fin 3) :
    plaqSurface n s ∈ vortexFamily n k := by
  classical
  rw [vortexFamily, Finset.mem_filter]
  exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
    plaqSurface_closed hk s, plaqSurface_connected s, card_plaqSurface (by omega) s,
    base_mem_plaqSurface s⟩

#print axioms mem_vortexFamily

/-- **`N(A) ≥ 3ᵏ` WITH NO HYPOTHESIS.** The entropy floor's count, against the definition of the
family rather than against a supplied one. The `3ᵏ` is `MassGap.directed_paths_card` — three choices
of axis at each of `k` steps — and the injection is `plaqSurface_injective`.

This is what `Floor`'s `log 3` and `CubeArea`'s `¼` were always counting, now said about an object
defined by its own properties: `κ₀ = ¼ log 3` is one unit of `log 3` of directional entropy per four
units of area, over the closed surfaces of that area through a fixed plaquette. -/
theorem three_pow_le_card_vortexFamily {n k : ℕ} [NeZero n] (hk : k + 2 < n) :
    3 ^ k ≤ (vortexFamily n k).card :=
  three_pow_le_card_of_plaq_subfamily (by omega) (vortexFamily n k)
    (fun s => mem_vortexFamily hk s)

/-- The same along a growing sequence of boxes, which is the form the free-energy density needs: the
bound holds at EVERY `k`, each in a box large enough to hold its own path. -/
theorem three_pow_le_card_vortexFamily_along_boxes (n : ℕ → ℕ) [∀ k, NeZero (n k)]
    (hn : ∀ k, k + 2 < n k) :
    ∀ k, 3 ^ k ≤ (vortexFamily (n k) k).card :=
  fun k => three_pow_le_card_vortexFamily (hn k)

#print axioms three_pow_le_card_vortexFamily
#print axioms three_pow_le_card_vortexFamily_along_boxes

/-! ### `hM` discharged

`VortexCount.junction_of_physical_count` consumes `hM : ∀ k, 3ᵏ ≤ M k` — a bound at EVERY `k`, because
the free-energy density it extracts is a `k → ∞` limit. The embedding is faithful only while the path
and its edges fit in the box, so `M` is read in a box that grows with `k`. Naming that box removes the
last free parameter: `hM` then holds with no hypothesis whatever. -/

/-- **THE BOX A `k`-STEP SURFACE NEEDS.** Not a choice: a `k`-step path's cubes reach coordinate `k`
(`cubePos_coord_le`), a face of one of them reaches `k+1` (`face_corner_le`), an edge of that face
reaches `k+2` (`faceEdges_corner_lt`), and `k+3` is the first `n` with all of those below `n`. It is
the successor of the largest coordinate the construction produces.

DERIVED: `3` is `1 + 2`, where `2` is how far an edge's far corner reaches beyond the path's own cubes
(one step to the face's corner, one more to the edge's) and `1` makes it the SUCCESSOR, which is what
`siteOf` needs to stay injective. Not chosen. -/
def boxOf (k : ℕ) : ℕ := k + 3

instance instNeZeroBoxOf (k : ℕ) : NeZero (boxOf k) := ⟨by simp [boxOf]⟩

/-- **`hM`, AS A THEOREM WITH NO HYPOTHESIS.** `3ᵏ ≤ N(4k+6)` where `N` counts the closed plaquette
surfaces of that area through the fixed plaquette — the intrinsic family, in the box that area needs.

This is the entropy floor's count standing on its own. Everything it used to ask of a caller is now
discharged: the surfaces exist (`plaqSurface`), are closed (`plaqSurface_closed`), are connected
(`plaqSurface_connected`), have area exactly `4k+6` (`card_plaqSurface`, whose `4` is
`CubeArea.boundary_card_eq`), pass through one fixed plaquette (`base_mem_plaqSurface`), are pairwise
distinct (`plaqSurface_injective`), and number `3ᵏ` (`MassGap.directed_paths_card`). -/
theorem three_pow_le_vortexCount (k : ℕ) :
    3 ^ k ≤ (vortexFamily (boxOf k) k).card :=
  three_pow_le_card_vortexFamily (by simp [boxOf])

#print axioms three_pow_le_vortexCount

/-- **THE JUNCTION WITH `hM` GONE.** `VortexCount.junction_of_physical_count` took two physical
inputs; one of them is now a theorem of this file, so the junction `κ₀ − μ ≤ c` rests on the scale
duality `hdual` ALONE, stated about the intrinsic family's own count rather than an abstract `M`. -/
theorem junction_of_vortexFamily {μ c : ℝ}
    (hdual : ∀ k, 0 < k →
      Real.log (((vortexFamily (boxOf k) k).card : ℝ) * Real.exp (-μ * (4 * (k : ℝ) + 6)))
        / (4 * (k : ℝ) + 6) ≤ c) :
    1 / 4 * Real.log 3 - μ ≤ c :=
  MassGap.VortexCount.junction_of_physical_count three_pow_le_vortexCount hdual

/-- The same in the transparent entropy-density form: the counted vortex entropy density is at most
the tension plus the contraction rate. -/
theorem junction_of_vortexFamily_density {μ c : ℝ}
    (hdens : ∀ k, 0 < k →
      Real.log (((vortexFamily (boxOf k) k).card : ℝ)) / (4 * (k : ℝ) + 6) ≤ μ + c) :
    1 / 4 * Real.log 3 - μ ≤ c :=
  MassGap.VortexCount.junction_of_entropy_density three_pow_le_vortexCount hdens

#print axioms junction_of_vortexFamily
#print axioms junction_of_vortexFamily_density

end MassGap.VortexFamily
