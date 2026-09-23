import MassGap.SurfaceEmbed
import MassGap.CubeClosed
import MassGap.CubeConnected
import MassGap.VortexCount

/-!
# MassGap.VortexFamily — an intrinsically defined vortex family, and `3^k ≤ N(4k+6)`

`SurfaceEmbed` places the directed surfaces on the physical lattice's plaquette type and
`three_pow_le_card_of_plaq_subfamily` counts them inside a family `V` the caller supplies, under a
hypothesis that the surfaces belong to it. This module defines the family instead —
`vortexFamily n k`, the connected closed plaquette surfaces of area `4k+6` through the fixed
plaquette `basePlaq n` — and discharges the containment as four theorems, so
`three_pow_le_vortexCount` states `3 ^ k ≤ (vortexFamily (boxOf k) k).card` with no hypothesis.

Closedness is stated through the Wilson action's own boundary map: `WilsonHypercubic.bd` sends a
plaquette to its four oriented links, `edgesOf` is that map with the orientations dropped, since a
parity count does not see them, and `IsClosedSurface F` says every link lies in an even number of
`F`'s boundaries — `∂∂ = 0` over `Z₂`. `SurfAdj` uses the same `edgesOf`.

`plaqSurface_closed` transports `CubeClosed.edge_parity_all` from three dimensions to four. Every
plaquette of an embedded surface spans two of the first three directions and sits in the time-zero
slice (`SurfaceEmbed.faceToPlaq`), so a link along the time direction lies in none of them
(`not_mem_edgesOf_time`) and a link off the slice in none either (`not_mem_edgesOf_offslice`); both
counts are even by being zero. For the remaining links, `mem_edgesOf_faceToPlaq` matches the
plaquettes carrying a link with the faces carrying the corresponding 3-D edge.

`plaqSurface_connected` transports `CubeConnected.boundary_connected` the same way, forward only.

The box condition tightens from `k + 1 < n` to `k + 2 < n` here: `siteOf` reduces modulo `n` and so
is injective only on corners below `n`, and the corners of a face's edges reach one step beyond the
face's own corner (`faceEdges_corner_lt`). `boxOf k = k + 3` is the smallest `n` meeting it.

DERIVED throughout: `4` is the physical dimension, `3` the dimension of the sublattice the cube-path
lives in, `2` the number of directions a plane spans, the number of owners a face can have, and the
modulus of `Z₂`; `0` is its identity, the origin, and the time-zero slice; `6` is the face count of a
cube and `4k+6` the area `CubeArea.boundary_card_eq` gives. Each is the arity of something already
fixed.
-/

namespace MassGap.VortexFamily

open Finset MassGap.CubeArea MassGap.SurfaceEmbed MassGap.WilsonHypercubic

variable {n : ℕ}

/-- The four links a plaquette's boundary word runs along, as a `Finset` and without orientation:
`WilsonHypercubic.bd q` with the `Bool` dropped. It is the boundary map the Wilson holonomy is taken
around, so closedness below is a condition on that map rather than on a separate description of the
geometry.

DERIVED: `4` is the physical dimension, which is what `Plaq 4 n` and `Link 4 n` are indexed by. -/
def edgesOf [NeZero n] (q : Plaq 4 n) : Finset (Link 4 n) :=
  ((bd q).map Prod.fst).toFinset

/-- A set of plaquettes is closed when every link of the lattice lies in an even number of their
boundaries: `(F.filter (fun q => e ∈ edgesOf q)).card % 2 = 0` at every `e`. This is `∂∂ = 0` over
`Z₂`.

DERIVED: `4` is the physical dimension; `2` is the modulus of `Z₂`, the group the centre-vortex flux
takes values in, and equally the number of owners a face can have; `0` is its identity. None is a
magnitude. -/
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

/-- Both directions `planeOf a` names are below `3`: they are axes of the cube-path's sublattice, of
which there are three. By `simp` and `omega`.

DERIVED: `3` is the dimension of the sublattice, so it bounds both axis indices; `1` and `2` are the
product projections. -/
theorem planeOf_lt_three (a : Fin 3) : ((planeOf a).1 : ℕ) < 3 ∧ ((planeOf a).2 : ℕ) < 3 := by
  constructor <;> · simp [planeOf]; omega

/-- `siteOf n x (3 : Fin 4) = 0`: the embedding places every cube at time zero, since `siteOf` sets
the fourth coordinate to `0`.

DERIVED: `3` is the index of the fourth coordinate, the time direction, in `Fin 4`; `4` is the
physical dimension; `0` is the time-zero slice. -/
theorem siteOf_time_zero [NeZero n] (x : Cube) :
    siteOf n x (3 : Fin 4) = (⟨0, NeZero.pos n⟩ : Fin n) := by
  simp [siteOf]

#print axioms planeOf_lt_three
#print axioms siteOf_time_zero

/-- `shift μ x (3 : Fin 4) = x (3 : Fin 4)` whenever `μ ≠ 3`: a step along any direction but the
time direction leaves the time coordinate unchanged.

DERIVED: `4` is the physical dimension; `3` is the index of the time direction in `Fin 4`. -/
theorem shift_time [NeZero n] {μ : Fin 4} (hμ : μ ≠ (3 : Fin 4)) (x : Site 4 n) :
    shift μ x (3 : Fin 4) = x (3 : Fin 4) := by
  simp [shift, Function.update_apply, (Ne.symm hμ)]

/-- A link whose direction is the time direction lies in no `edgesOf (faceToPlaq n f)`. The
plaquette's two spanning directions are `planeOf f.1`, both below `3` by `planeOf_lt_three`, and
`mem_edgesOf` gives the four links' directions as those two.

DERIVED: `4` is the physical dimension; `3` is the index of the time direction; `1` is the product
projection selecting a link's direction. -/
theorem not_mem_edgesOf_time [NeZero n] (f : Face) (e : Link 4 n) (he : e.1 = (3 : Fin 4)) :
    e ∉ edgesOf (faceToPlaq n f) := by
  intro hmem
  obtain ⟨h1, h2⟩ := planeOf_lt_three f.1
  rcases mem_edgesOf.mp hmem with h | h | h | h <;>
    · have := congrArg Prod.fst h
      rw [he] at this
      simp [faceToPlaq] at this
      omega

/-- Every link of `edgesOf (faceToPlaq n f)` has time coordinate `0`. The plaquette's corner is
placed at time zero by `siteOf_time_zero`, and the steps reaching the other three links are along
directions other than the time one, so `shift_time` leaves the coordinate alone.

DERIVED: `4` is the physical dimension; `3` is the index of the time direction; `0` is the time-zero
slice; `2` is the product projection selecting a link's site. -/
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

/-- `shift (emb a) (siteOf n y) = siteOf n (step a y)`: a step commutes with the embedding. No bound
on the coordinate is needed, since both sides reduce the same coordinate modulo `n`; the periodic
wrap obstructs injectivity of `siteOf`, not this identity.

DERIVED: `3` is the sublattice dimension the axis `a` ranges over. -/
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
    -- `(y a % n + 1 % n) % n = (y a + 1) % n`: the two modular reductions agree
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

/-- `planeOf a = (emb (rot1 a), emb (rot2 a))`: the plane a face with normal `a` spans is the pair of
embedded rotations of `a`, so the plaquette's two directions are the two axes the face's edges run
along.

DERIVED: `3` is the sublattice dimension; `1` and `2` label the two rotations and the two product
components. -/
theorem planeOf_eq_emb (a : Fin 3) : planeOf a = (emb (rot1 a), emb (rot2 a)) := by
  refine Prod.ext ?_ ?_ <;> apply Fin.ext <;> simp [planeOf, emb, rot1, rot2]

/-- A 3-D edge, embedded as a link of the physical lattice.

DERIVED: `3` is the cube-path's sublattice dimension and `4` the physical dimension, exactly as in
`emb`; `1` and `2` are the product projections selecting the edge's axis and its corner. -/
def linkEmb (n : ℕ) [NeZero n] (d : Fin 3 × Cube) : Link 4 n := (emb d.1, siteOf n d.2)

#print axioms emb_injective
#print axioms planeOf_eq_emb

/-- `e ∈ edgesOf (faceToPlaq n f) ↔ ∃ d ∈ faceEdges f, linkEmb n d = e`: the links of an embedded
plaquette are exactly the embeddings of the face's own edges. `bd`'s four links match `faceEdges`'
four edges one for one, `planeOf_eq_emb` matching the directions and `shift_siteOf` the corners.

DERIVED: `4` is the physical dimension the links live in. -/
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
edge. That is where the periodic box cuts into the argument — `siteOf` reduces modulo `n`, so it is
injective only on corners below `n`, and the corners of a face's EDGES reach one step further than
the face's own corner. Hence `k + 2 < n` here where the area count needed only `k + 1 < n`. -/

/-- Every coordinate of every corner of every edge of a boundary face of a `k`-step path is below
`n`, given `k + 2 < n`. The face's own corner is at most `k + 1` by `face_corner_le`, and an edge's
far corner is one `step` beyond it, hence at most `k + 2`.

DERIVED: `2` is how far an edge's far corner reaches beyond the path's cubes — one step to the
face's corner and one more to the edge's; `3` is the sublattice dimension; `1` and `2` are also the
product projections on `Fin 3 × Cube`. -/
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

/-- `IsClosedSurface (plaqSurface n s)` for every `k`-step path `s`, given `k + 2 < n`. It is
`CubeClosed.edge_parity_all` transported along `mem_edgesOf_faceToPlaq`, the count upstairs matching
the count downstairs because `faceToPlaq_inj_on` applies under `k + 1 < n`. Three kinds of link are
treated:

* a link along the time direction lies in no plaquette of the surface (`not_mem_edgesOf_time`);
* a link off the time-zero slice likewise (`not_mem_edgesOf_offslice`);
* any other link is `linkEmb` of a 3-D edge, unique by `emb_injective` and `siteOf_inj_of_lt`, and
  the plaquettes carrying it correspond to the boundary faces carrying that edge.

The first two counts are zero, hence even.

DERIVED: `2` in `k + 2 < n` is how far an edge's far corner reaches beyond the path's cubes; `3` is
the sublattice dimension. -/
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

Each of the four conditions Theorem 7.1 asks of the surfaces it counts is a check the embedded
surfaces pass: closed (`plaqSurface_closed`), connected (`plaqSurface_connected`), of area `4k+6`
(`card_plaqSurface`), and through one fixed plaquette (`base_mem_plaqSurface`). `vortexFamily` is
defined by those conditions, so the count is made against a definition rather than against a
supplied family.

Connectedness is one of the four. Dropping it admits unions of unit-cube boundaries, each closed
because every link lies in two or four of them and each of area `6`, with components placed anywhere
in the box; at area `4k+6` that is one anchored component plus about `2k/3` unanchored ones in a box
of about `k^4` sites, giving

    log N / A  ≥  (2k/3)(3 log k) / (4k)  =  (log k)/2,

which grows with `k`, whereas `hdual` asks for a fixed `c` with `log N_k / (4k+6) - μ ≤ c` at every
`k`. -/

/-- The fixed plaquette the family's surfaces pass through: the embedding of the origin cube's low
face on axis `0`. It lies on the boundary of every directed path's configuration, since nothing sits
one step back from zero in `ℕ³`, so that face has exactly one owner whatever the path does after.

DERIVED: `3` is the sublattice dimension and `4` the physical one. Both `0`s are the origin — the
corner every directed path starts from, `cubePos s 0`, and the axis index the floor argument runs
on. `origin_face_mem_boundary` holds for all three axes, and any of them fixes the same plaquette up
to relabelling. -/
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

/-- Two plaquettes of `F` are adjacent when both lie in `F` and `edgesOf a ∩ edgesOf b` is nonempty —
the same `edgesOf` the closedness condition counts, so adjacency uses no second geometry.

DERIVED: `4` is the physical dimension. -/
def SurfAdj [NeZero n] (F : Finset (Plaq 4 n)) (a b : Plaq 4 n) : Prop :=
  a ∈ F ∧ b ∈ F ∧ (edgesOf a ∩ edgesOf b).Nonempty

/-- A set of plaquettes is connected when every member is reachable from `basePlaq n` under
`Relation.ReflTransGen (SurfAdj F)`, that is along shared links inside `F`.

DERIVED: `4` is the physical dimension. -/
def IsConnectedSurface [NeZero n] (F : Finset (Plaq 4 n)) : Prop :=
  ∀ q ∈ F, Relation.ReflTransGen (SurfAdj F) (basePlaq n) q

/-- A 3-D edge shared by two boundary faces embeds to a link shared by their plaquettes: from
`FaceAdj (boundaryFaces C) f g` follows
`SurfAdj ((boundaryFaces C).image (faceToPlaq n)) (faceToPlaq n f) (faceToPlaq n g)`, with witness
`linkEmb n e`. Only the forward direction of `mem_edgesOf_faceToPlaq` is used, so no injectivity and
no box condition enter.

DERIVED: no numeral appears in the statement; the physical dimension `4` is inside `SurfAdj`. -/
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

/-- `IsConnectedSurface (plaqSurface n s)` for every path `s`, with no box condition. It is
`CubeConnected.boundary_connected` carried along the embedding by `reflTransGen_faceToPlaq`: every
boundary face is reachable from the origin cube's low face on axis `0`, each shared edge embeds to a
shared link, and `basePlaq n` is the image of that face since `cubePos s 0` is the origin.

DERIVED: `3` is the sublattice dimension the path's steps range over. -/
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
/-- The vortex family: the subsets of `Plaq 4 n` that are closed (`IsClosedSurface`), connected
(`IsConnectedSurface`), of cardinality `4 * k + 6`, and contain `basePlaq n`. `N(A)` of Theorem 7.1
is the cardinality of this set, so the count below is against a definition rather than a supplied
family.

DERIVED: `4` is the physical dimension. `4 * k + 6` is the area, and it is
`CubeArea.boundary_card_eq` — `6` faces per cube for `k+1` cubes, less `2` per shared face for the
`k` shared ones. Neither literal is fitted. -/
noncomputable def vortexFamily (n : ℕ) [NeZero n] (k : ℕ) : Finset (Finset (Plaq 4 n)) :=
  (univ : Finset (Plaq 4 n)).powerset.filter
    (fun F => IsClosedSurface F ∧ IsConnectedSurface F ∧ F.card = 4 * k + 6 ∧ basePlaq n ∈ F)

/-- `plaqSurface n s ∈ vortexFamily n k` for every `k`-step path `s`, given `k + 2 < n`. All four
membership conditions are theorems: `plaqSurface_closed`, `plaqSurface_connected`,
`card_plaqSurface` for the area, and `base_mem_plaqSurface` for the fixed plaquette. No containment
is assumed.

DERIVED: `2` in `k + 2 < n` is how far an edge's far corner reaches beyond the path's cubes, the
condition `plaqSurface_closed` needs; `3` is the sublattice dimension. -/
theorem mem_vortexFamily {n k : ℕ} [NeZero n] (hk : k + 2 < n) (s : Fin k → Fin 3) :
    plaqSurface n s ∈ vortexFamily n k := by
  classical
  rw [vortexFamily, Finset.mem_filter]
  exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
    plaqSurface_closed hk s, plaqSurface_connected s, card_plaqSurface (by omega) s,
    base_mem_plaqSurface s⟩

#print axioms mem_vortexFamily

/-- `3 ^ k ≤ (vortexFamily n k).card` given `k + 2 < n`, with no containment hypothesis. It is
`three_pow_le_card_of_plaq_subfamily` at `vortexFamily n k`, the membership supplied by
`mem_vortexFamily`. The count `3 ^ k` is `MassGap.directed_paths_card` — three choices of axis at
each of `k` steps — and the surfaces are distinct by `plaqSurface_injective`.

This is the count behind `κ₀YM = ¼ log 3`: one unit of `log 3` of directional entropy per four units
of area, over the connected closed surfaces of that area through a fixed plaquette.

DERIVED: `3` is the sublattice dimension, hence the number of axis choices per step; `2` in
`k + 2 < n` is the box condition `mem_vortexFamily` needs. -/
theorem three_pow_le_card_vortexFamily {n k : ℕ} [NeZero n] (hk : k + 2 < n) :
    3 ^ k ≤ (vortexFamily n k).card :=
  three_pow_le_card_of_plaq_subfamily (by omega) (vortexFamily n k)
    (fun s => mem_vortexFamily hk s)

/-- `3 ^ k ≤ (vortexFamily (n k) k).card` at every `k`, for any sequence of box sizes `n` with
`k + 2 < n k`. This is the form the free-energy density consumes, each `k` read in a box large
enough for its own path.

DERIVED: `3` is the number of axis choices per step; `2` in `k + 2 < n k` is the box condition. -/
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

/-- The box a `k`-step surface needs: `k + 3`. A `k`-step path's cubes reach coordinate `k`
(`cubePos_coord_le`), a face of one reaches `k + 1` (`face_corner_le`), an edge of that face reaches
`k + 2` (`faceEdges_corner_lt`), and `k + 3` is the smallest `n` with all of those below `n`.

DERIVED: `3` is `1 + 2`, where `2` is how far an edge's far corner reaches beyond the path's cubes —
one step to the face's corner, one more to the edge's — and `1` makes it the successor, which is what
`siteOf` needs to stay injective. -/
def boxOf (k : ℕ) : ℕ := k + 3

instance instNeZeroBoxOf (k : ℕ) : NeZero (boxOf k) := ⟨by simp [boxOf]⟩

/-- `3 ^ k ≤ (vortexFamily (boxOf k) k).card` at every `k`, with no hypothesis: the box condition
`k + 2 < k + 3` holds by `simp`. This is the shape `VortexCount.junction_of_physical_count` takes as
`hM`.

Every condition is discharged by a theorem: the surfaces exist (`plaqSurface`), are closed
(`plaqSurface_closed`), are connected (`plaqSurface_connected`), have cardinality `4k+6`
(`card_plaqSurface`, whose `4` is `CubeArea.boundary_card_eq`), contain the fixed plaquette
(`base_mem_plaqSurface`), are pairwise distinct (`plaqSurface_injective`), and number `3 ^ k`
(`MassGap.directed_paths_card`).

DERIVED: `3` is the number of axis choices per step of the path. -/
theorem three_pow_le_vortexCount (k : ℕ) :
    3 ^ k ≤ (vortexFamily (boxOf k) k).card :=
  three_pow_le_card_vortexFamily (by simp [boxOf])

#print axioms three_pow_le_vortexCount

/-- `1 / 4 * Real.log 3 - μ ≤ c` from `hdual` alone: for every `k > 0`,
`log ((vortexFamily (boxOf k) k).card * exp (-μ * (4k + 6))) / (4k + 6) ≤ c`. It is
`VortexCount.junction_of_physical_count` with `three_pow_le_vortexCount` supplying its count
hypothesis, so `hdual` is the only input, stated about this family's own cardinality.

DERIVED: `0` is the lower bound on `k` the scale duality is asserted above; `4 * k + 6` is the area,
`CubeArea.boundary_card_eq`'s; `1 / 4 * log 3` is `κ₀YM`, one unit of `log 3` of directional entropy
per four units of area. -/
theorem junction_of_vortexFamily {μ c : ℝ}
    (hdual : ∀ k, 0 < k →
      Real.log (((vortexFamily (boxOf k) k).card : ℝ) * Real.exp (-μ * (4 * (k : ℝ) + 6)))
        / (4 * (k : ℝ) + 6) ≤ c) :
    1 / 4 * Real.log 3 - μ ≤ c :=
  MassGap.VortexCount.junction_of_physical_count three_pow_le_vortexCount hdual

/-- The same conclusion `1 / 4 * Real.log 3 - μ ≤ c` from the entropy-density form of the
hypothesis: `log ((vortexFamily (boxOf k) k).card) / (4k + 6) ≤ μ + c` for every `k > 0`. It is
`VortexCount.junction_of_entropy_density` with `three_pow_le_vortexCount`.

DERIVED: `0` is the lower bound on `k`; `4 * k + 6` is the area; `1 / 4 * log 3` is `κ₀YM`. -/
theorem junction_of_vortexFamily_density {μ c : ℝ}
    (hdens : ∀ k, 0 < k →
      Real.log (((vortexFamily (boxOf k) k).card : ℝ)) / (4 * (k : ℝ) + 6) ≤ μ + c) :
    1 / 4 * Real.log 3 - μ ≤ c :=
  MassGap.VortexCount.junction_of_entropy_density three_pow_le_vortexCount hdens

#print axioms junction_of_vortexFamily
#print axioms junction_of_vortexFamily_density

end MassGap.VortexFamily
