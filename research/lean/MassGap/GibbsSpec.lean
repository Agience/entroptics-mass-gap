import Mathlib
import MassGap.WilsonLattice
import MassGap.WilsonAction

/-!
# MassGap.GibbsSpec — the finite-volume Gibbs specification on the infinite lattice

A Gibbs *specification* is the family of finite-volume conditional measures, one for each finite
volume `Λ` of links and each configuration `ω` fixed outside it. It is the object the DLR equations
are stated about. Every other measure in `MassGap` lives on a finite periodic lattice with its own
partition function; this module's measures live on the infinite lattice `ILink = Fin 4 × (Fin 4 → ℤ)`.

## What the specification is

For a finite `Λ : Finset ILink` the inside variables range over `VConf G Λ = ↥Λ → G` and the outside
is held at `ω : IConf G`. `splice Λ u ω` puts the two together. The energy is

    actionOn φ (boundaryPlaqs Λ) (splice Λ u ω)

and `spec φ β Λ μ f ω = (∫ f(splice) e^{−βS}) / (∫ e^{−βS})` against product Haar over `↥Λ`.

## `boundaryPlaqs` against `plaqsIn`

`boundaryPlaqs Λ` is the set of plaquettes with at least one link in `Λ`; `plaqsIn Λ` is the set
with all four links in `Λ`. Summing over `plaqsIn` gives the free-boundary energy. DLR consistency
needs the energy to split, for `Λ ⊆ Λ'`, as

    (plaquettes the inner volume owns) + (a remainder that does not read the inner variables),

and `links_not_mem_of_mem_sdiff` is that statement for `boundaryPlaqs`: a plaquette of
`boundaryPlaqs Λ' \ boundaryPlaqs Λ` has no link in `Λ`. `plaqsIn_split_not_local` exhibits a nested
pair and a plaquette of `plaqsIn Λ' \ plaqsIn Λ` that does read a link of `Λ`, so the same split
fails there, and `boundaryPlaqs_ne_plaqsIn` shows the two sets differ on a one-link volume.

## What the module proves

* `actionBC_split` — the `Λ'` energy of a spliced configuration is the `Λ` energy plus a remainder
  evaluated at the outside configuration alone. Everything below rests on it.
* `part_pos` — the partition function is strictly positive, so the normalisation is legitimate.
* `dlr_consistent` — the DLR compatibility relation: for `Λ ⊆ Λ'`, integrating the `Λ` kernel
  against the `Λ'` kernel returns the `Λ'` kernel. Proved by decomposing the product measure over
  `↥Λ'` into the `Λ` block and its complement (`measurePreserving_piEquivPiSubtypeProd`), Fubini on
  that product, and `actionBC_split` to take the remainder out of the inner integral.
* `wilson_dlr_consistent` — the same for the `SU(N)` Wilson density on the infinite
  four-dimensional lattice, against probability Haar, at every `N ≠ 0` and every real `β`.

## Two propositions stated but not proved here

`ExistsGibbsMeasure` and `TranslationCovariant` are `Prop`-valued definitions with no theorem in
this file. The first says some probability measure on `IConf G` satisfies the DLR equations against
this specification; deriving it needs compactness of `IConf G` and a weak-* limit. The second says
the specification commutes with lattice translation.

Foundational footprint only (`#print axioms` at the end).
Build: `python code/lean_build.py build MassGap.GibbsSpec`.
-/

namespace MassGap.GibbsSpec

open MeasureTheory
open MassGap.LatticeGauge MassGap.WilsonLattice

/-! ## Part 0 — the infinite-lattice skeleton

Duplicated from the shared skeleton so this file stands alone; identical names and types.
`MassGap.InfiniteLattice` exports the same four declarations with the same bodies, and all of them
are `abbrev`s, so the two copies are reducibly defeq and interchangeable wherever both are in scope.
`MassGap.WilsonGibbs` states this file's conclusions against `DLRLimit`'s measure on that footing,
and `WilsonGibbs.ibd_eq` records that the boundary words agree by `rfl`.

`plaqsIn` is the one pair that is not interchangeable by unfolding: this file's filters
`boundaryPlaqs Λ` by a `List.all` over `ilinks`, `InfiniteLattice`'s filters a site-image candidate
set by `linksOf q ⊆ Λ`, and the two are equal only extensionally.
`MassGap.WilsonGibbs.gibbsSpec_plaqsIn_eq` is that equality. -/

/-- A site of the infinite four-dimensional lattice: one integer coordinate per direction.

DERIVED: the declaration's type carries no numeral; the `4` in the body is the number of spacetime
directions, the dimension of the Clay statement and the same `d` that `WilsonHypercubic` is
instantiated at for the Clay instance (`bd (d := 4)` in `AreaLaw`). It is an index range, not an
extent: each of the four coordinates runs over all of `ℤ`. -/
abbrev ISite : Type := Fin 4 → ℤ

/-- A link: a direction paired with a site.

DERIVED: the declaration's type carries no numeral; the `4` in the body is the dimension, the range
of a link's direction index. The same constant as in `ISite`, not a second one. -/
abbrev ILink : Type := Fin 4 × ISite

/-- A plaquette: an ordered pair of directions spanning its plane, paired with a site.

DERIVED: the declaration's type carries no numeral; both `4`s in the body are the dimension,
written twice because a plane is spanned by an ordered pair of directions, as
`WilsonHypercubic.Plaq` also records. -/
abbrev IPlaq : Type := (Fin 4 × Fin 4) × ISite

/-- A configuration: a group element on every link of the infinite lattice. `G` is arbitrary
here; the Wilson section below instantiates it at `SUN.SU N`. -/
abbrev IConf (G : Type) : Type := ILink → G

/-- One lattice step forward in direction `μ`: add `1` to that coordinate and leave the rest.

DERIVED: `4` is the dimension, the range of the direction index `μ`. The `1` in the body is one
lattice step, the definition of a neighbouring site rather than a length — no lattice spacing
appears in this file. It mirrors `WilsonHypercubic.shift`, whose step is the same. -/
def ishift (μ : Fin 4) (x : ISite) : ISite := Function.update x μ (x μ + 1)

/-- One lattice step backward in direction `μ`, the inverse of `ishift` (`iunshift_ishift`).

DERIVED: `4` is the dimension, the range of the direction index `μ`. The `1` in the body is the same
unit step as `ishift`'s, taken the other way. Neither is a parameter. -/
def iunshift (μ : Fin 4) (x : ISite) : ISite := Function.update x μ (x μ - 1)

theorem iunshift_ishift (μ : Fin 4) (x : ISite) : iunshift μ (ishift μ x) = x := by
  funext j
  by_cases h : j = μ
  · subst h
    show Function.update (ishift j x) j ((ishift j x) j - 1) j = x j
    rw [Function.update_self]
    show Function.update x j (x j + 1) j - 1 = x j
    rw [Function.update_self]
    omega
  · show Function.update (ishift μ x) μ ((ishift μ x) μ - 1) j = x j
    rw [Function.update_of_ne h]
    show Function.update x μ (x μ + 1) j = x j
    rw [Function.update_of_ne h]

/-- The plaquette boundary word, mirroring `WilsonHypercubic.bd` on the infinite lattice:
`U_μ(x) · U_ν(x+μ̂) · U_μ(x+ν̂)⁻¹ · U_ν(x)⁻¹`, as a list of link-orientation pairs. -/
def ibd (q : IPlaq) : List (ILink × Bool) :=
  [((q.1.1, q.2), true), ((q.1.2, ishift q.1.1 q.2), true),
   ((q.1.1, ishift q.1.2 q.2), false), ((q.1.2, q.2), false)]

/-- The links a plaquette reads, in boundary-word order: the first components of `ibd q`. -/
def ilinks (q : IPlaq) : List ILink := (ibd q).map Prod.fst

theorem ilinks_eq (q : IPlaq) :
    ilinks q = [(q.1.1, q.2), (q.1.2, ishift q.1.1 q.2),
                (q.1.1, ishift q.1.2 q.2), (q.1.2, q.2)] := rfl

theorem head_mem_ilinks (q : IPlaq) : (q.1.1, q.2) ∈ ilinks q := by
  rw [ilinks_eq]; simp

/-! ## Part 1 — the plaquettes a finite volume touches -/

/-- A finite superset of the plaquettes reading a given link. A plaquette `((a,b),y)` reads the
link `(μ,x)` only if `a = μ` or `b = μ`, and only at `y = x` or `y = x − ν̂` for some direction `ν`,
so sixteen candidates per link suffice. `mem_touching` is the containment; it is what makes
`boundaryPlaqs` a `Finset` at all, `IPlaq` being infinite.

DERIVED: the declaration carries no numeral. In the body `4` is the dimension, the range of `ν`,
and the four candidates listed in the braces are two pair-positions against two base sites, which
do not scale with the dimension. `mem_touching` proves the superset is large enough, so nothing
downstream depends on the count. -/
def touching (l : ILink) : Finset IPlaq :=
  Finset.univ.biUnion (fun ν : Fin 4 =>
    ({((l.1, ν), l.2), ((ν, l.1), l.2),
      ((l.1, ν), iunshift ν l.2), ((ν, l.1), iunshift ν l.2)} : Finset IPlaq))

theorem mem_touching {l : ILink} {q : IPlaq} (h : l ∈ ilinks q) : q ∈ touching l := by
  obtain ⟨⟨a, b⟩, y⟩ := q
  simp only [ilinks, ibd, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at h
  rcases h with h | h | h | h
  · subst h
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, by simp⟩
  · subst h
    refine Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, ?_⟩
    simp [iunshift_ishift]
  · subst h
    refine Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, ?_⟩
    simp [iunshift_ishift]
  · subst h
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, by simp⟩

/-- The plaquettes with at least one link in `Λ`: the plaquette set of a finite volume with a
boundary condition. Finite because each lies in `touching l` for one of the finitely many `l ∈ Λ`. -/
def boundaryPlaqs (Λ : Finset ILink) : Finset IPlaq :=
  (Λ.biUnion touching).filter (fun q => ((ilinks q).any (fun l => decide (l ∈ Λ))) = true)

theorem mem_boundaryPlaqs {Λ : Finset ILink} {q : IPlaq} :
    q ∈ boundaryPlaqs Λ ↔ ∃ l ∈ ilinks q, l ∈ Λ := by
  constructor
  · intro h
    have h2 := (Finset.mem_filter.mp h).2
    rw [List.any_eq_true] at h2
    obtain ⟨l, hl, hd⟩ := h2
    exact ⟨l, hl, of_decide_eq_true hd⟩
  · rintro ⟨l, hl, hlΛ⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨l, hlΛ, mem_touching hl⟩, ?_⟩
    rw [List.any_eq_true]
    exact ⟨l, hl, decide_eq_true hlΛ⟩

/-- The plaquettes with all four links in `Λ`: the free-boundary plaquette set, a subset of
`boundaryPlaqs Λ` (`plaqsIn_subset_boundaryPlaqs`). -/
def plaqsIn (Λ : Finset ILink) : Finset IPlaq :=
  (boundaryPlaqs Λ).filter (fun q => ((ilinks q).all (fun l => decide (l ∈ Λ))) = true)

theorem mem_plaqsIn {Λ : Finset ILink} {q : IPlaq} :
    q ∈ plaqsIn Λ ↔ ∀ l ∈ ilinks q, l ∈ Λ := by
  constructor
  · intro h
    have h2 := (Finset.mem_filter.mp h).2
    rw [List.all_eq_true] at h2
    exact fun l hl => of_decide_eq_true (h2 l hl)
  · intro h
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact mem_boundaryPlaqs.mpr ⟨(q.1.1, q.2), head_mem_ilinks q, h _ (head_mem_ilinks q)⟩
    · rw [List.all_eq_true]
      exact fun l hl => decide_eq_true (h l hl)

theorem plaqsIn_subset_boundaryPlaqs (Λ : Finset ILink) : plaqsIn Λ ⊆ boundaryPlaqs Λ :=
  Finset.filter_subset _ _

theorem boundaryPlaqs_mono {Λ Λ' : Finset ILink} (h : Λ ⊆ Λ') :
    boundaryPlaqs Λ ⊆ boundaryPlaqs Λ' := by
  intro q hq
  obtain ⟨l, hl, hlΛ⟩ := mem_boundaryPlaqs.mp hq
  exact mem_boundaryPlaqs.mpr ⟨l, hl, h hlΛ⟩

/-- The locality fact the DLR split rests on: a plaquette in `boundaryPlaqs Λ' \ boundaryPlaqs Λ`
reads no link of `Λ`. Immediate from the definition of `boundaryPlaqs`; the corresponding statement
for `plaqsIn` is refuted by `plaqsIn_split_not_local`. -/
theorem links_not_mem_of_mem_sdiff {Λ Λ' : Finset ILink} {q : IPlaq}
    (hq : q ∈ boundaryPlaqs Λ' \ boundaryPlaqs Λ) : ∀ l ∈ ilinks q, l ∉ Λ := by
  intro l hl hlΛ
  exact (Finset.mem_sdiff.mp hq).2 (mem_boundaryPlaqs.mpr ⟨l, hl, hlΛ⟩)

/-! ### Controls: the two plaquette sets are different, and only one of them splits -/

/-- The origin of `ISite`: the constant-zero coordinate function.

DERIVED: the declaration's type carries no numeral; the `0` in the body is the zero of `ℤ` in every
direction, not a magnitude. CHOSEN: that the controls below are stated at the origin rather than at
another site. Every construction they use (`ibd`, `ilinks`, `boundaryPlaqs`, `plaqsIn`) is defined
uniformly in the base site, so they read the same at any site under relabelling by `ishift`. -/
def osite : ISite := fun _ => 0

/-- The plane-`(0,1)` plaquette at the origin.

DERIVED: the declaration's type carries no numeral. The `0` and `1` in the body are direction
indices naming the plane spanned by the first two directions — the same plane
`PlaqVariance.clayPlaq` is built on (`((0, 1), fun _ => 0)`), which is the plaquette `corrClay`
reads. -/
def q01 : IPlaq := ((0, 1), osite)

/-- The one-link volume holding `q01`'s first link.

DERIVED: the declaration's type carries no numeral. In the body `0` is a direction index and `4` the
dimension it ranges over. The index follows from `q01`: `ilinks_eq` makes `q01`'s first link
`(q01.1.1, q01.2)`, which is `((0 : Fin 4), osite)`. -/
def linkSet : Finset ILink := {((0 : Fin 4), osite)}

theorem q01_link0 : ((0 : Fin 4), osite) ∈ ilinks q01 := by
  rw [ilinks_eq]; simp [q01]

theorem q01_link3 : ((1 : Fin 4), osite) ∈ ilinks q01 := by
  rw [ilinks_eq]; simp [q01]

theorem q01_mem_boundaryPlaqs : q01 ∈ boundaryPlaqs linkSet :=
  mem_boundaryPlaqs.mpr ⟨((0 : Fin 4), osite), q01_link0, Finset.mem_singleton_self _⟩

/-- `boundaryPlaqs linkSet` is nonempty: the one-link volume `linkSet` already touches `q01`. So
`actionOn φ (boundaryPlaqs Λ)` is not a sum over the empty set for every `Λ`, and the kernel below
is not the free product measure for every `Λ`. -/
theorem boundaryPlaqs_nonempty : (boundaryPlaqs linkSet).Nonempty :=
  ⟨q01, q01_mem_boundaryPlaqs⟩

/-- `boundaryPlaqs linkSet ≠ plaqsIn linkSet`. On the one-link volume `linkSet`, `boundaryPlaqs`
contains `q01` and `plaqsIn` does not, because `q01` also reads the link `((1 : Fin 4), osite)`,
which `linkSet` does not hold. -/
theorem boundaryPlaqs_ne_plaqsIn : boundaryPlaqs linkSet ≠ plaqsIn linkSet := by
  intro hEq
  have hb : q01 ∈ boundaryPlaqs linkSet := q01_mem_boundaryPlaqs
  rw [hEq] at hb
  have hmem := mem_plaqsIn.mp hb _ q01_link3
  rw [linkSet, Finset.mem_singleton] at hmem
  exact absurd (congrArg Prod.fst hmem) (by decide)

/-- The `plaqsIn` analogue of `links_not_mem_of_mem_sdiff` is false: there exist a nested pair
`Λ ⊆ Λ'`, a plaquette `q ∈ plaqsIn Λ' \ plaqsIn Λ` and a link `l ∈ ilinks q` with `l ∈ Λ`. So the
remainder of a `plaqsIn` energy is not in general a function of the outside variables. The witnesses
are `linkSet`, `(ilinks q01).toFinset` and `q01`. -/
theorem plaqsIn_split_not_local :
    ∃ (Λ Λ' : Finset ILink) (q : IPlaq) (l : ILink),
      Λ ⊆ Λ' ∧ q ∈ plaqsIn Λ' \ plaqsIn Λ ∧ l ∈ ilinks q ∧ l ∈ Λ := by
  refine ⟨linkSet, (ilinks q01).toFinset, q01, ((0 : Fin 4), osite), ?_, ?_, q01_link0, ?_⟩
  · intro x hx
    rw [linkSet, Finset.mem_singleton] at hx
    subst hx
    exact List.mem_toFinset.mpr q01_link0
  · refine Finset.mem_sdiff.mpr ⟨mem_plaqsIn.mpr (fun l hl => List.mem_toFinset.mpr hl), ?_⟩
    intro hc
    have hmem := mem_plaqsIn.mp hc _ q01_link3
    rw [linkSet, Finset.mem_singleton] at hmem
    exact absurd (congrArg Prod.fst hmem) (by decide)
  · exact Finset.mem_singleton_self _

/-! ## Part 2 — the splice -/

section Splice

variable {G : Type}

/-- Configurations on a finite volume: a group element on each link of `Λ`, indexed by the
subtype `↥Λ`. -/
abbrev VConf (G : Type) (Λ : Finset ILink) : Type := ↥Λ → G

/-- The splice: follow the inside configuration `u` on `Λ` and the outside configuration `ω` off
it. The same piecewise construction `HalfLineTransfer.detBy_inter` uses to intersect determination
sets, here with the inside variables carried on the subtype `↥Λ`. -/
def splice (Λ : Finset ILink) (u : VConf G Λ) (ω : IConf G) : IConf G :=
  fun l => if h : l ∈ Λ then u ⟨l, h⟩ else ω l

theorem splice_mem {Λ : Finset ILink} {u : VConf G Λ} {ω : IConf G} {l : ILink} (h : l ∈ Λ) :
    splice Λ u ω l = u ⟨l, h⟩ := dif_pos h

theorem splice_not_mem {Λ : Finset ILink} {u : VConf G Λ} {ω : IConf G} {l : ILink} (h : l ∉ Λ) :
    splice Λ u ω l = ω l := dif_neg h

theorem splice_congr_right {Λ : Finset ILink} (u : VConf G Λ) {ω ω' : IConf G}
    (h : ∀ l ∉ Λ, ω l = ω' l) : splice Λ u ω = splice Λ u ω' := by
  funext l
  by_cases hl : l ∈ Λ
  · rw [splice_mem hl, splice_mem hl]
  · rw [splice_not_mem hl, splice_not_mem hl]; exact h l hl

/-- Gluing an inner volume's configuration into an outer one: follow `u` on the links of `Λ` and
`u'` on the rest of `Λ'`. The inclusion `Λ ⊆ Λ'` is taken but not read. -/
def vglue {Λ Λ' : Finset ILink} (_hsub : Λ ⊆ Λ') (u : VConf G Λ) (u' : VConf G Λ') : VConf G Λ' :=
  fun l => if h : l.1 ∈ Λ then u ⟨l.1, h⟩ else u' l

/-- Splicing twice on nested volumes composes: splicing `u` on `Λ` into the `Λ'`-splice of `u'`
is the `Λ'`-splice of `vglue hsub u u'`. -/
theorem splice_nested {Λ Λ' : Finset ILink} (hsub : Λ ⊆ Λ')
    (u : VConf G Λ) (u' : VConf G Λ') (ω : IConf G) :
    splice Λ u (splice Λ' u' ω) = splice Λ' (vglue hsub u u') ω := by
  funext l
  by_cases h1 : l ∈ Λ
  · have h1' : l ∈ Λ' := hsub h1
    simp [splice, vglue, h1, h1']
  · by_cases h2 : l ∈ Λ'
    · simp [splice, vglue, h1, h2]
    · simp [splice, h1, h2]

variable [MeasurableSpace G]

theorem measurable_splice_left (Λ : Finset ILink) (ω : IConf G) :
    Measurable (fun u : VConf G Λ => splice Λ u ω) := by
  refine measurable_pi_lambda _ (fun l => ?_)
  by_cases h : l ∈ Λ
  · have he : (fun u : VConf G Λ => splice Λ u ω l) = fun u => u ⟨l, h⟩ :=
      funext fun _ => splice_mem h
    rw [he]; exact measurable_pi_apply _
  · have he : (fun u : VConf G Λ => splice Λ u ω l) = fun _ => ω l :=
      funext fun _ => splice_not_mem h
    rw [he]; exact measurable_const

theorem measurable_splice_right (Λ : Finset ILink) (u : VConf G Λ) :
    Measurable (fun ω : IConf G => splice Λ u ω) := by
  refine measurable_pi_lambda _ (fun l => ?_)
  by_cases h : l ∈ Λ
  · have he : (fun ω : IConf G => splice Λ u ω l) = fun _ => u ⟨l, h⟩ :=
      funext fun _ => splice_mem h
    rw [he]; exact measurable_const
  · have he : (fun ω : IConf G => splice Λ u ω l) = fun ω => ω l :=
      funext fun _ => splice_not_mem h
    rw [he]; exact measurable_pi_apply _

theorem measurable_splice_prod (Λ : Finset ILink) :
    Measurable (fun z : IConf G × VConf G Λ => splice Λ z.2 z.1) := by
  refine measurable_pi_lambda _ (fun l => ?_)
  by_cases h : l ∈ Λ
  · have he : (fun z : IConf G × VConf G Λ => splice Λ z.2 z.1 l) = fun z => z.2 ⟨l, h⟩ :=
      funext fun _ => splice_mem h
    rw [he]; exact (measurable_pi_apply _).comp measurable_snd
  · have he : (fun z : IConf G × VConf G Λ => splice Λ z.2 z.1 l) = fun z => z.1 l :=
      funext fun _ => splice_not_mem h
    rw [he]; exact (measurable_pi_apply _).comp measurable_fst

end Splice

/-! ## Part 3 — the finite-volume action with a boundary condition -/

section Action

variable {G : Type} [Group G]

/-- The ordered plaquette holonomy on the infinite lattice: `wilsonHol` at the boundary word
`ibd`. -/
noncomputable def ihol (q : IPlaq) (U : IConf G) : G := wilsonHol ibd q U

/-- The holonomy reads only the plaquette's own links: configurations agreeing on `ilinks q` give
the same `ihol q`. -/
theorem ihol_congr (q : IPlaq) (U V : IConf G) (h : ∀ l ∈ ilinks q, U l = V l) :
    ihol q U = ihol q V := by
  unfold ihol wilsonHol
  congr 1
  refine List.map_congr_left (fun lo hlo => ?_)
  have hmem : lo.1 ∈ ilinks q := List.mem_map.mpr ⟨lo, hlo, rfl⟩
  rw [h lo.1 hmem]

/-- The energy of a finite set of plaquettes: the density `φ` summed over their holonomies. -/
noncomputable def actionOn (φ : G → ℝ) (S : Finset IPlaq) (U : IConf G) : ℝ :=
  ∑ q ∈ S, φ (ihol q U)

theorem actionOn_congr (φ : G → ℝ) (S : Finset IPlaq) (U V : IConf G)
    (h : ∀ q ∈ S, ∀ l ∈ ilinks q, U l = V l) : actionOn φ S U = actionOn φ S V :=
  Finset.sum_congr rfl (fun q hq => by rw [ihol_congr q U V (h q hq)])

theorem actionOn_split (φ : G → ℝ) {Λ Λ' : Finset ILink} (hsub : Λ ⊆ Λ') (U : IConf G) :
    actionOn φ (boundaryPlaqs Λ') U
      = actionOn φ (boundaryPlaqs Λ) U + actionOn φ (boundaryPlaqs Λ' \ boundaryPlaqs Λ) U := by
  unfold actionOn
  rw [add_comm]
  exact (Finset.sum_sdiff (boundaryPlaqs_mono hsub)).symm

/-- The energy over `boundaryPlaqs Λ' \ boundaryPlaqs Λ` does not read the inside variables: it
takes the same value at `splice Λ u v` as at `v`, for every `u`. -/
theorem actionOn_sdiff_indep (φ : G → ℝ) {Λ Λ' : Finset ILink}
    (u : VConf G Λ) (v : IConf G) :
    actionOn φ (boundaryPlaqs Λ' \ boundaryPlaqs Λ) (splice Λ u v)
      = actionOn φ (boundaryPlaqs Λ' \ boundaryPlaqs Λ) v :=
  actionOn_congr φ _ _ _ (fun _ hq l hl => splice_not_mem (links_not_mem_of_mem_sdiff hq l hl))

/-- For `Λ ⊆ Λ'`, the outer energy of a spliced configuration splits as the inner energy plus a
remainder that is a function of the outside configuration `v` alone. This is what makes the family
`spec` a specification rather than a collection of unrelated measures. The corresponding split with
`plaqsIn` in place of `boundaryPlaqs` is refuted by `plaqsIn_split_not_local`. -/
theorem actionBC_split (φ : G → ℝ) {Λ Λ' : Finset ILink} (hsub : Λ ⊆ Λ')
    (u : VConf G Λ) (v : IConf G) :
    actionOn φ (boundaryPlaqs Λ') (splice Λ u v)
      = actionOn φ (boundaryPlaqs Λ) (splice Λ u v)
        + actionOn φ (boundaryPlaqs Λ' \ boundaryPlaqs Λ) v := by
  rw [actionOn_split φ hsub, actionOn_sdiff_indep φ u v]

theorem actionOn_nonneg {φ : G → ℝ} (hφ0 : ∀ g, 0 ≤ φ g) (S : Finset IPlaq) (U : IConf G) :
    0 ≤ actionOn φ S U := Finset.sum_nonneg (fun _ _ => hφ0 _)

theorem actionOn_le {φ : G → ℝ} (hφ2 : ∀ g, φ g ≤ 2) (S : Finset IPlaq) (U : IConf G) :
    actionOn φ S U ≤ (S.card : ℝ) * 2 := by
  unfold actionOn
  calc ∑ q ∈ S, φ (ihol q U) ≤ ∑ _q ∈ S, (2 : ℝ) := Finset.sum_le_sum (fun _ _ => hφ2 _)
    _ = (S.card : ℝ) * 2 := by rw [Finset.sum_const, nsmul_eq_mul]

end Action

/-! ## Part 4 — the specification kernel

Two measure-theoretic tools are restated here rather than imported from `ActionSplit`, so this
module's import list stays at `Mathlib`, `WilsonLattice` and `WilsonAction`. -/

/-- A measurable real function bounded in absolute value by `C` is integrable against a finite
measure. -/
theorem integrable_of_bounded {γ : Type} [MeasurableSpace γ] (m : Measure γ) [IsFiniteMeasure m]
    {g : γ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ z, |g z| ≤ C) : Integrable g m :=
  Integrable.mono' (integrable_const C) hg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hC z)

/-- Change of variables along a measure-preserving map `f`: the `m`-integral of `H ∘ f` is the
`m'`-integral of `H`, for `H` measurable. -/
theorem integral_comp_of_mp {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    {m : Measure α} {m' : Measure β} {f : α → β} (hf : MeasurePreserving f m m')
    {H : β → ℝ} (hH : Measurable H) : (∫ x, H (f x) ∂m) = ∫ y, H y ∂m' := by
  have h1 : (∫ y, H y ∂(Measure.map f m)) = ∫ x, H (f x) ∂m :=
    integral_map hf.measurable.aemeasurable hH.aestronglyMeasurable
  rw [← h1, hf.map_eq]

section Kernel

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

theorem measurable_ihol (q : IPlaq) : Measurable (ihol (G := G) q) :=
  measurable_wilsonHol ibd q

theorem measurable_actionOn {φ : G → ℝ} (hφ : Measurable φ) (S : Finset IPlaq) :
    Measurable (actionOn φ S) := by
  unfold actionOn
  exact Finset.measurable_sum S (fun q _ => hφ.comp (measurable_ihol q))

/-- The Boltzmann weight of the finite volume `Λ` with boundary condition `ω`: `exp` of `-β`
times the energy of `boundaryPlaqs Λ` at `splice Λ u ω`. -/
noncomputable def wt (φ : G → ℝ) (β : ℝ) (Λ : Finset ILink) (u : VConf G Λ) (ω : IConf G) : ℝ :=
  Real.exp (-β * actionOn φ (boundaryPlaqs Λ) (splice Λ u ω))

theorem wt_pos (φ : G → ℝ) (β : ℝ) (Λ : Finset ILink) (u : VConf G Λ) (ω : IConf G) :
    0 < wt φ β Λ u ω := Real.exp_pos _

theorem wt_le {φ : G → ℝ} (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (Λ : Finset ILink) (u : VConf G Λ) (ω : IConf G) :
    wt φ β Λ u ω ≤ Real.exp (|β| * (((boundaryPlaqs Λ).card : ℝ) * 2)) := by
  unfold wt
  rw [Real.exp_le_exp]
  have h1 : -β * actionOn φ (boundaryPlaqs Λ) (splice Λ u ω)
      ≤ |β| * actionOn φ (boundaryPlaqs Λ) (splice Λ u ω) :=
    mul_le_mul_of_nonneg_right (neg_le_abs β) (actionOn_nonneg hφ0 _ _)
  have h2 : |β| * actionOn φ (boundaryPlaqs Λ) (splice Λ u ω)
      ≤ |β| * (((boundaryPlaqs Λ).card : ℝ) * 2) :=
    mul_le_mul_of_nonneg_left (actionOn_le hφ2 _ _) (abs_nonneg β)
  linarith

theorem measurable_wt_left {φ : G → ℝ} (hφ : Measurable φ) (β : ℝ) (Λ : Finset ILink)
    (ω : IConf G) : Measurable (fun u : VConf G Λ => wt φ β Λ u ω) := by
  unfold wt
  exact Real.continuous_exp.measurable.comp
    (((measurable_actionOn hφ (boundaryPlaqs Λ)).comp (measurable_splice_left Λ ω)).const_mul (-β))

theorem measurable_wt_prod {φ : G → ℝ} (hφ : Measurable φ) (β : ℝ) (Λ : Finset ILink) :
    Measurable (fun z : IConf G × VConf G Λ => wt φ β Λ z.2 z.1) := by
  unfold wt
  exact Real.continuous_exp.measurable.comp
    (((measurable_actionOn hφ (boundaryPlaqs Λ)).comp (measurable_splice_prod Λ)).const_mul (-β))

/-- The product measure over the links of a finite volume. Instantiated at probability Haar in
the Wilson section; `μ` is an arbitrary measure on `G` here. -/
noncomputable def vol (μ : Measure G) (Λ : Finset ILink) : Measure (VConf G Λ) :=
  Measure.pi (fun _ : ↥Λ => μ)

instance isProbabilityMeasure_vol (μ : Measure G) [IsProbabilityMeasure μ] (Λ : Finset ILink) :
    IsProbabilityMeasure (vol μ Λ) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : ↥Λ => μ)))

/-- The partition function of the volume `Λ` with boundary condition `ω`: the integral of `wt`
over `vol μ Λ`. -/
noncomputable def part (φ : G → ℝ) (β : ℝ) (Λ : Finset ILink) (μ : Measure G) (ω : IConf G) : ℝ :=
  ∫ u, wt φ β Λ u ω ∂(vol μ Λ)

/-- The unnormalised expectation of `f` in the volume `Λ` with boundary condition `ω`: the
integral of `f (splice Λ u ω) * wt φ β Λ u ω` over `vol μ Λ`. -/
noncomputable def num (φ : G → ℝ) (β : ℝ) (Λ : Finset ILink) (μ : Measure G)
    (f : IConf G → ℝ) (ω : IConf G) : ℝ :=
  ∫ u, f (splice Λ u ω) * wt φ β Λ u ω ∂(vol μ Λ)

/-- The specification kernel `γ_Λ(f | ω)` as `num / part`: the Gibbs expectation of `f` in the
finite volume `Λ` with the configuration outside `Λ` held at `ω`. Mirrors
`LatticeGauge.System.expect`, whose numerator and partition function it reproduces on this
geometry. -/
noncomputable def spec (φ : G → ℝ) (β : ℝ) (Λ : Finset ILink) (μ : Measure G)
    (f : IConf G → ℝ) (ω : IConf G) : ℝ :=
  num φ β Λ μ f ω / part φ β Λ μ ω

theorem integrable_wt {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ] (ω : IConf G) :
    Integrable (fun u : VConf G Λ => wt φ β Λ u ω) (vol μ Λ) :=
  integrable_of_bounded _ (measurable_wt_left hφ β Λ ω)
    (fun u => by rw [abs_of_pos (wt_pos φ β Λ u ω)]; exact wt_le hφ0 hφ2 β Λ u ω)

/-- The partition function is strictly positive, at every volume, coupling and boundary
condition, for a measurable density `φ` with values in `[0, 2]` and a probability measure `μ`. Same
shape as `WilsonReal.wilsonSystem_partition_pos` in the finite periodic theory.

DERIVED: `0` is the `0 ≤ φ g` of `hφ0` and the strict lower bound in the conclusion. `2` is the
`φ g ≤ 2` of `hφ2`, the range of the Wilson density (`WilsonAction.wilsonDensity_le_two`), used
through `wt_le` to bound the integrand. -/
theorem part_pos {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ] (ω : IConf G) :
    0 < part φ β Λ μ ω := by
  unfold part
  rw [integral_pos_iff_support_of_nonneg (fun u => (wt_pos φ β Λ u ω).le)
      (integrable_wt hφ hφ0 hφ2 β Λ μ ω)]
  have hsupp : Function.support (fun u : VConf G Λ => wt φ β Λ u ω) = Set.univ :=
    Set.eq_univ_of_forall (fun u => Function.mem_support.mpr (wt_pos φ β Λ u ω).ne')
  rw [hsupp, measure_univ]
  exact one_pos

theorem integrable_num {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    {f : IConf G → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ U, |f U| ≤ C) (ω : IConf G) :
    Integrable (fun u : VConf G Λ => f (splice Λ u ω) * wt φ β Λ u ω) (vol μ Λ) := by
  have hCnn : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hC (fun _ => 1))
  refine integrable_of_bounded _ ((hf.comp (measurable_splice_left Λ ω)).mul
    (measurable_wt_left hφ β Λ ω)) (C := C * Real.exp (|β| * (((boundaryPlaqs Λ).card : ℝ) * 2)))
    (fun u => ?_)
  rw [abs_mul, abs_of_pos (wt_pos φ β Λ u ω)]
  exact mul_le_mul (hC _) (wt_le hφ0 hφ2 β Λ u ω) (wt_pos φ β Λ u ω).le hCnn

/-- The kernel is normalised: `spec φ β Λ μ (fun _ => 1) ω = 1`, so the constant observable has
expectation one.

DERIVED: `1` is the constant observable and the value it takes under the kernel. `0` and `2` are
`hφ0` and `hφ2`, the range `[0, 2]` required of the density, which is what `part_pos` needs to
divide by the partition function. -/
theorem spec_one {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ] (ω : IConf G) :
    spec φ β Λ μ (fun _ => (1 : ℝ)) ω = 1 := by
  unfold spec num
  simp only [one_mul]
  show part φ β Λ μ ω / part φ β Λ μ ω = 1
  exact div_self (part_pos hφ hφ0 hφ2 β Λ μ ω).ne'

/-- The kernel reads its boundary condition only outside `Λ`: two boundary conditions agreeing
off `Λ` give the same value. Stated with no hypothesis on `φ`, `β` or `μ`. -/
theorem spec_congr_off (φ : G → ℝ) (β : ℝ) (Λ : Finset ILink) (μ : Measure G)
    (f : IConf G → ℝ) {ω ω' : IConf G} (h : ∀ l ∉ Λ, ω l = ω' l) :
    spec φ β Λ μ f ω = spec φ β Λ μ f ω' := by
  have hs : ∀ u : VConf G Λ, splice Λ u ω = splice Λ u ω' := fun u => splice_congr_right u h
  unfold spec num part wt
  simp only [hs]

theorem abs_num_le {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    {f : IConf G → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ U, |f U| ≤ C) (ω : IConf G) :
    |num φ β Λ μ f ω| ≤ C * part φ β Λ μ ω := by
  have hint1 := integrable_num hφ hφ0 hφ2 β Λ μ hf hC ω
  have hint2 := (integrable_wt hφ hφ0 hφ2 β Λ μ ω).const_mul C
  have h0 : |num φ β Λ μ f ω| ≤ ∫ u, |f (splice Λ u ω) * wt φ β Λ u ω| ∂(vol μ Λ) := by
    unfold num
    simpa [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := vol μ Λ)
        (fun u : VConf G Λ => f (splice Λ u ω) * wt φ β Λ u ω)
  have h1 : (∫ u, |f (splice Λ u ω) * wt φ β Λ u ω| ∂(vol μ Λ))
      ≤ ∫ u, C * wt φ β Λ u ω ∂(vol μ Λ) := by
    refine integral_mono hint1.abs hint2 (fun u => ?_)
    rw [abs_mul, abs_of_pos (wt_pos φ β Λ u ω)]
    exact mul_le_mul_of_nonneg_right (hC _) (wt_pos φ β Λ u ω).le
  have h2 : (∫ u, C * wt φ β Λ u ω ∂(vol μ Λ)) = C * part φ β Λ μ ω := integral_const_mul _ _
  linarith

theorem abs_spec_le {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    {f : IConf G → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ U, |f U| ≤ C) (ω : IConf G) :
    |spec φ β Λ μ f ω| ≤ C := by
  have hZ := part_pos hφ hφ0 hφ2 β Λ μ ω
  unfold spec
  rw [abs_div, abs_of_pos hZ]
  exact (div_le_iff₀ hZ).mpr (abs_num_le hφ hφ0 hφ2 β Λ μ hf hC ω)

/-! ### The kernel is measurable in the boundary condition -/

theorem measurable_num_right {φ : G → ℝ} (hφ : Measurable φ) (β : ℝ) (Λ : Finset ILink)
    (μ : Measure G) [IsProbabilityMeasure μ] {f : IConf G → ℝ} (hf : Measurable f) :
    Measurable (fun v : IConf G => num φ β Λ μ f v) := by
  have hjoint : Measurable (fun z : IConf G × VConf G Λ =>
      f (splice Λ z.2 z.1) * wt φ β Λ z.2 z.1) :=
    (hf.comp (measurable_splice_prod Λ)).mul (measurable_wt_prod hφ β Λ)
  exact (hjoint.stronglyMeasurable.integral_prod_right' (ν := vol μ Λ)).measurable

theorem measurable_part_right {φ : G → ℝ} (hφ : Measurable φ) (β : ℝ) (Λ : Finset ILink)
    (μ : Measure G) [IsProbabilityMeasure μ] :
    Measurable (fun v : IConf G => part φ β Λ μ v) :=
  ((measurable_wt_prod hφ β Λ).stronglyMeasurable.integral_prod_right'
    (ν := vol μ Λ)).measurable

theorem measurable_spec_right {φ : G → ℝ} (hφ : Measurable φ) (β : ℝ) (Λ : Finset ILink)
    (μ : Measure G) [IsProbabilityMeasure μ] {f : IConf G → ℝ} (hf : Measurable f) :
    Measurable (fun v : IConf G => spec φ β Λ μ f v) :=
  (measurable_num_right hφ β Λ μ hf).div (measurable_part_right hφ β Λ μ)

end Kernel

/-! ## Part 5 — DLR consistency

For `Λ ⊆ Λ'` the product measure over `↥Λ'` splits into the block of links inside `Λ` and the block
outside it. `measurePreserving_piEquivPiSubtypeProd` does the splitting, `subEquivIn` identifies the
inside block with `↥Λ`, and `actionBC_split` takes the remainder out of the inner integral. -/

section DLR

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

/-- The links of `Λ'` lying outside `Λ`, as a subtype of `↥Λ'`. -/
abbrev OutIdx (Λ Λ' : Finset ILink) : Type := {l : ↥Λ' // l.1 ∉ Λ}

/-- The links of `Λ'` lying inside `Λ`, as a subtype of `↥Λ'`. Written with a double negation so
that it is literally the complement of `OutIdx` under
`MeasurableEquiv.piEquivPiSubtypeProd`'s predicate. -/
abbrev InIdx (Λ Λ' : Finset ILink) : Type := {l : ↥Λ' // ¬ (l.1 ∉ Λ)}

/-- The measurable equivalence splitting a `Λ'`-configuration into its outside-of-`Λ` and
inside-of-`Λ` blocks. -/
noncomputable def eSplit (G : Type) [MeasurableSpace G] (Λ Λ' : Finset ILink) :
    VConf G Λ' ≃ᵐ ((OutIdx Λ Λ' → G) × (InIdx Λ Λ' → G)) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ↥Λ' => G) (fun l : ↥Λ' => l.1 ∉ Λ)

theorem eSplit_symm_apply (Λ Λ' : Finset ILink)
    (x : OutIdx Λ Λ' → G) (y : InIdx Λ Λ' → G) (l : ↥Λ') :
    (eSplit G Λ Λ').symm (x, y) l = if h : l.1 ∉ Λ then x ⟨l, h⟩ else y ⟨l, h⟩ := rfl

/-- The inside block of `Λ'` is in bijection with the index set of `Λ`, given `Λ ⊆ Λ'`. -/
def subEquivIn {Λ Λ' : Finset ILink} (hsub : Λ ⊆ Λ') : InIdx Λ Λ' ≃ ↥Λ where
  toFun l := ⟨l.1.1, not_not.mp l.2⟩
  invFun l := ⟨⟨l.1, hsub l.2⟩, not_not.mpr l.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Transporting a `Λ`-configuration onto the inside block of `Λ'` along `subEquivIn`, as a
measurable equivalence. -/
noncomputable def toIn {Λ Λ' : Finset ILink} (hsub : Λ ⊆ Λ') :
    VConf G Λ ≃ᵐ (InIdx Λ Λ' → G) :=
  (MeasurableEquiv.piCongrLeft (fun _ : ↥Λ => G) (subEquivIn hsub)).symm

theorem toIn_apply {Λ Λ' : Finset ILink} (hsub : Λ ⊆ Λ') (u : VConf G Λ) (j : InIdx Λ Λ') :
    toIn (G := G) hsub u j = u (subEquivIn hsub j) := rfl

theorem measurePreserving_toIn {Λ Λ' : Finset ILink} (hsub : Λ ⊆ Λ')
    (μ : Measure G) [IsProbabilityMeasure μ] :
    MeasurePreserving (toIn (G := G) hsub) (vol μ Λ)
      (Measure.pi (fun _ : InIdx Λ Λ' => μ)) := by
  have h : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : ↥Λ => G) (subEquivIn hsub))
      (Measure.pi (fun _ : InIdx Λ Λ' => μ)) (vol μ Λ) := by
    simpa [vol] using
      measurePreserving_piCongrLeft (μ := fun _ : ↥Λ => μ)
        (subEquivIn (Λ := Λ) (Λ' := Λ') hsub)
  exact MeasurePreserving.symm _ h

/-- The boundary condition the outer variables present to the inner volume: the `Λ'`-splice with
the inside block filled by the group identity.

DERIVED: the declaration carries no numeral. The `1` in the body is the identity of `G`, `Group G`
being the only structure in scope. Its value does not reach the conclusions: `splice_eSplit` shows
the inner splice writes over the whole inside block, so any filler gives the same result. -/
noncomputable def vout {Λ Λ' : Finset ILink} (x : OutIdx Λ Λ' → G) (ω : IConf G) : IConf G :=
  splice Λ' ((eSplit G Λ Λ').symm (x, fun _ => 1)) ω

/-- The two splices agree: assembling the outer block `x` with a `Λ`-configuration `u` and
splicing into `ω` over `Λ'` gives the same configuration as splicing `u` into `vout x ω` over
`Λ`. -/
theorem splice_eSplit {Λ Λ' : Finset ILink} (hsub : Λ ⊆ Λ')
    (x : OutIdx Λ Λ' → G) (u : VConf G Λ) (ω : IConf G) :
    splice Λ' ((eSplit G Λ Λ').symm (x, toIn hsub u)) ω = splice Λ u (vout x ω) := by
  funext l
  by_cases h1 : l ∈ Λ
  · have h1' : l ∈ Λ' := hsub h1
    have hL : splice Λ' ((eSplit G Λ Λ').symm (x, toIn hsub u)) ω l
        = (eSplit G Λ Λ').symm (x, toIn hsub u) ⟨l, h1'⟩ := splice_mem h1'
    have hR : splice Λ u (vout x ω) l = u ⟨l, h1⟩ := splice_mem h1
    rw [hL, hR, eSplit_symm_apply, dif_neg (not_not_intro h1)]
    rfl
  · by_cases h2 : l ∈ Λ'
    · have hL : splice Λ' ((eSplit G Λ Λ').symm (x, toIn hsub u)) ω l
          = (eSplit G Λ Λ').symm (x, toIn hsub u) ⟨l, h2⟩ := splice_mem h2
      have hR : splice Λ u (vout x ω) l = vout x ω l := splice_not_mem h1
      have hR2 : vout x ω l
          = (eSplit G Λ Λ').symm (x, (fun _ => 1 : InIdx Λ Λ' → G)) ⟨l, h2⟩ := splice_mem h2
      rw [hL, hR, hR2, eSplit_symm_apply, eSplit_symm_apply, dif_pos h1, dif_pos h1]
    · have hL : splice Λ' ((eSplit G Λ Λ').symm (x, toIn hsub u)) ω l = ω l := splice_not_mem h2
      have hR : splice Λ u (vout x ω) l = vout x ω l := splice_not_mem h1
      have hR2 : vout x ω l = ω l := splice_not_mem h2
      rw [hL, hR, hR2]

/-- The Boltzmann weight factorises into the inner weight `wt φ β Λ u (vout x ω)` and a factor
depending on `x` and `ω` but not on `u`. This is `actionBC_split` in multiplicative form, and it is
what `num_outer` integrates. -/
theorem wt_eSplit {φ : G → ℝ} {Λ Λ' : Finset ILink} (hsub : Λ ⊆ Λ') (β : ℝ)
    (x : OutIdx Λ Λ' → G) (u : VConf G Λ) (ω : IConf G) :
    wt φ β Λ' ((eSplit G Λ Λ').symm (x, toIn hsub u)) ω
      = wt φ β Λ u (vout x ω)
        * Real.exp (-β * actionOn φ (boundaryPlaqs Λ' \ boundaryPlaqs Λ) (vout x ω)) := by
  unfold wt
  rw [splice_eSplit hsub x u ω, actionBC_split φ hsub u (vout x ω), mul_add, Real.exp_add]

/-- The outer unnormalised expectation written as an integral over the outer block alone: for
`Λ ⊆ Λ'` and `h` measurable with `|h| ≤ C`, `num φ β Λ' μ h ω` is the integral over `x` of the
remainder factor times `num φ β Λ μ h (vout x ω)`.

DERIVED: `0` is the `0 ≤ φ g` of `hφ0`. `2` is the `φ g ≤ 2` of `hφ2`, the range required of the
density, which enters through `wt_le` to make the joint integrand integrable. The observable's bound
is the variable `C`; no numerical bound on `h` is fixed. -/
theorem num_outer {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (μ : Measure G) [IsProbabilityMeasure μ]
    {Λ Λ' : Finset ILink} (hsub : Λ ⊆ Λ')
    {h : IConf G → ℝ} (hh : Measurable h) {C : ℝ} (hC : ∀ U, |h U| ≤ C) (ω : IConf G) :
    num φ β Λ' μ h ω
      = ∫ x, Real.exp (-β * actionOn φ (boundaryPlaqs Λ' \ boundaryPlaqs Λ) (vout x ω))
              * num φ β Λ μ h (vout x ω) ∂(Measure.pi (fun _ : OutIdx Λ Λ' => μ)) := by
  have hmp0 := measurePreserving_piEquivPiSubtypeProd (fun _ : ↥Λ' => μ)
    (fun l : ↥Λ' => l.1 ∉ Λ)
  have hmp : MeasurePreserving (eSplit G Λ Λ') (vol μ Λ')
      ((Measure.pi fun _ : OutIdx Λ Λ' => μ).prod (Measure.pi fun _ : InIdx Λ Λ' => μ)) := hmp0
  have hmps := MeasurePreserving.symm (eSplit G Λ Λ') hmp
  have hFm : Measurable (fun u' : VConf G Λ' => h (splice Λ' u' ω) * wt φ β Λ' u' ω) :=
    (hh.comp (measurable_splice_left Λ' ω)).mul (measurable_wt_left hφ β Λ' ω)
  have hCnn : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hC (fun _ => 1))
  have hFb : ∀ u' : VConf G Λ',
      |h (splice Λ' u' ω) * wt φ β Λ' u' ω|
        ≤ C * Real.exp (|β| * (((boundaryPlaqs Λ').card : ℝ) * 2)) := by
    intro u'
    rw [abs_mul, abs_of_pos (wt_pos φ β Λ' u' ω)]
    exact mul_le_mul (hC _) (wt_le hφ0 hφ2 β Λ' u' ω) (wt_pos φ β Λ' u' ω).le hCnn
  have hint : Integrable
      (fun z => h (splice Λ' ((eSplit G Λ Λ').symm z) ω) * wt φ β Λ' ((eSplit G Λ Λ').symm z) ω)
      ((Measure.pi fun _ : OutIdx Λ Λ' => μ).prod (Measure.pi fun _ : InIdx Λ Λ' => μ)) :=
    integrable_of_bounded _ (hFm.comp (eSplit G Λ Λ').symm.measurable) (fun z => hFb _)
  have step1 : num φ β Λ' μ h ω
      = ∫ z, h (splice Λ' ((eSplit G Λ Λ').symm z) ω) * wt φ β Λ' ((eSplit G Λ Λ').symm z) ω
          ∂((Measure.pi fun _ : OutIdx Λ Λ' => μ).prod (Measure.pi fun _ : InIdx Λ Λ' => μ)) :=
    (hmps.integral_comp' (fun u' : VConf G Λ' => h (splice Λ' u' ω) * wt φ β Λ' u' ω)).symm
  have hpt : ∀ x : OutIdx Λ Λ' → G,
      (∫ y, h (splice Λ' ((eSplit G Λ Λ').symm (x, y)) ω)
          * wt φ β Λ' ((eSplit G Λ Λ').symm (x, y)) ω
          ∂(Measure.pi fun _ : InIdx Λ Λ' => μ))
        = Real.exp (-β * actionOn φ (boundaryPlaqs Λ' \ boundaryPlaqs Λ) (vout x ω))
            * num φ β Λ μ h (vout x ω) := by
    intro x
    have hPm : Measurable (fun y : InIdx Λ Λ' → G =>
        ((x, y) : (OutIdx Λ Λ' → G) × (InIdx Λ Λ' → G))) := by fun_prop
    have hHm : Measurable (fun y : InIdx Λ Λ' → G =>
        h (splice Λ' ((eSplit G Λ Λ').symm (x, y)) ω)
          * wt φ β Λ' ((eSplit G Λ Λ').symm (x, y)) ω) :=
      hFm.comp ((eSplit G Λ Λ').symm.measurable.comp hPm)
    rw [← integral_comp_of_mp (measurePreserving_toIn hsub μ) hHm]
    have hrw : ∀ u : VConf G Λ,
        h (splice Λ' ((eSplit G Λ Λ').symm (x, toIn hsub u)) ω)
            * wt φ β Λ' ((eSplit G Λ Λ').symm (x, toIn hsub u)) ω
          = Real.exp (-β * actionOn φ (boundaryPlaqs Λ' \ boundaryPlaqs Λ) (vout x ω))
            * (h (splice Λ u (vout x ω)) * wt φ β Λ u (vout x ω)) := by
      intro u
      rw [splice_eSplit hsub x u ω, wt_eSplit hsub β x u ω]
      ring
    have hstep : (∫ u, h (splice Λ' ((eSplit G Λ Λ').symm (x, toIn hsub u)) ω)
          * wt φ β Λ' ((eSplit G Λ Λ').symm (x, toIn hsub u)) ω ∂(vol μ Λ))
        = ∫ u, Real.exp (-β * actionOn φ (boundaryPlaqs Λ' \ boundaryPlaqs Λ) (vout x ω))
            * (h (splice Λ u (vout x ω)) * wt φ β Λ u (vout x ω)) ∂(vol μ Λ) :=
      integral_congr_ae (Filter.Eventually.of_forall hrw)
    rw [hstep]
    exact integral_const_mul _ _
  rw [step1, integral_prod _ hint]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

/-- Averaging the inner kernel against the inner weight returns the inner numerator:
`num φ β Λ μ (spec φ β Λ μ f) v = num φ β Λ μ f v`. The inner kernel does not read the inner
variables (`spec_congr_off`), so it comes out of the integral and cancels the partition function it
is divided by.

DERIVED: `0` is the `0 ≤ φ g` of `hφ0` and `2` the `φ g ≤ 2` of `hφ2`, the range required of the
density so that `part_pos` gives a nonzero divisor. `f` carries no bound here. -/
theorem num_spec_eq_num {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    (f : IConf G → ℝ) (v : IConf G) :
    num φ β Λ μ (fun w => spec φ β Λ μ f w) v = num φ β Λ μ f v := by
  have hZ : part φ β Λ μ v ≠ 0 := (part_pos hφ hφ0 hφ2 β Λ μ v).ne'
  have hconst : ∀ u : VConf G Λ, spec φ β Λ μ f (splice Λ u v) = spec φ β Λ μ f v := fun u =>
    spec_congr_off φ β Λ μ f (fun l hl => splice_not_mem hl)
  have hpt : ∀ u : VConf G Λ,
      spec φ β Λ μ f (splice Λ u v) * wt φ β Λ u v
        = spec φ β Λ μ f v * wt φ β Λ u v := fun u => by rw [hconst u]
  have h1 : num φ β Λ μ (fun w => spec φ β Λ μ f w) v
      = ∫ u, spec φ β Λ μ f v * wt φ β Λ u v ∂(vol μ Λ) := by
    unfold num
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have h2 : (∫ u, spec φ β Λ μ f v * wt φ β Λ u v ∂(vol μ Λ))
      = spec φ β Λ μ f v * part φ β Λ μ v := integral_const_mul _ _
  rw [h1, h2]
  unfold spec
  rw [div_mul_eq_mul_div, mul_div_assoc, div_self hZ, mul_one]

/-- The DLR compatibility relation as a `Prop`: for nested volumes `Λ ⊆ Λ'` and every measurable
`f` with `|f| ≤ 1`, integrating the inner kernel against the outer kernel returns the outer kernel.

DERIVED: `1` is a normalisation, not a bound on the model. `|f| ≤ 1` names the unit ball of bounded
measurable observables, and `abs_spec_le` returns the same bound on `spec φ β Λ μ f`, so the inner
kernel is itself an admissible `f` for the outer one. `num` is linear in `f` and `part` does not
mention `f`, so the relation at any other finite bound `B > 0` is this one applied to `f / B`. -/
def DLRConsistent (φ : G → ℝ) (β : ℝ) (μ : Measure G) : Prop :=
  ∀ (Λ Λ' : Finset ILink), Λ ⊆ Λ' → ∀ (f : IConf G → ℝ), Measurable f →
    (∀ U, |f U| ≤ 1) → ∀ ω : IConf G,
      spec φ β Λ' μ (fun v => spec φ β Λ μ f v) ω = spec φ β Λ' μ f ω

/-- The specification is DLR-consistent, for every measurable density `φ` with values in
`[0, 2]`, every real coupling and every probability measure `μ` on `G`.

DERIVED: `0` is the `0 ≤ φ g` of `hφ0` and `2` the `φ g ≤ 2` of `hφ2` — the range of the Wilson
density (`WilsonAction.wilsonDensity_le_two`), which is what `part_pos`, `abs_spec_le` and
`num_outer` each require. The `1` of `DLRConsistent`'s observable bound is documented there. -/
theorem dlr_consistent {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (μ : Measure G) [IsProbabilityMeasure μ] : DLRConsistent φ β μ := by
  intro Λ Λ' hsub f hf hf1 ω
  have hgm : Measurable (fun v : IConf G => spec φ β Λ μ f v) :=
    measurable_spec_right hφ β Λ μ hf
  have hg1 : ∀ v : IConf G, |spec φ β Λ μ f v| ≤ 1 := fun v =>
    abs_spec_le hφ hφ0 hφ2 β Λ μ hf hf1 v
  have hpt : ∀ x : OutIdx Λ Λ' → G,
      Real.exp (-β * actionOn φ (boundaryPlaqs Λ' \ boundaryPlaqs Λ) (vout x ω))
          * num φ β Λ μ (fun v => spec φ β Λ μ f v) (vout x ω)
        = Real.exp (-β * actionOn φ (boundaryPlaqs Λ' \ boundaryPlaqs Λ) (vout x ω))
          * num φ β Λ μ f (vout x ω) := fun x => by
    rw [num_spec_eq_num hφ hφ0 hφ2 β Λ μ f (vout x ω)]
  have key : num φ β Λ' μ (fun v => spec φ β Λ μ f v) ω = num φ β Λ' μ f ω := by
    rw [num_outer hφ hφ0 hφ2 β μ hsub hgm hg1 ω, num_outer hφ hφ0 hφ2 β μ hsub hf hf1 ω]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  show num φ β Λ' μ (fun v => spec φ β Λ μ f v) ω / part φ β Λ' μ ω
      = num φ β Λ' μ f ω / part φ β Λ' μ ω
  rw [key]

end DLR

/-! ## Part 6 — the `SU(N)` Wilson specification -/

section Wilson

open MassGap.CompactGauge MassGap.WilsonAction

variable {N : ℕ}

/-- The Wilson specification on the infinite four-dimensional lattice is DLR-consistent, at every
`N ≠ 0` and every real coupling. The plaquette density is `WilsonAction.wilsonDensity`, that is
`1 − Re tr U / N`; the single-link measure is probability Haar on `SUN.SU N`; the plaquette set of a
finite volume is `boundaryPlaqs`, so the conditioning is on a boundary condition rather than on a
free boundary.

DERIVED: `0` is the `N ≠ 0` of `hN`, which `wilsonDensity_nonneg` and `wilsonDensity_le_two` both
require. The `[0, 2]` range they supply is `dlr_consistent`'s hypothesis. -/
theorem wilson_dlr_consistent (hN : N ≠ 0) (β : ℝ) :
    DLRConsistent (wilsonDensity (N := N)) β (probHaar (MassGap.SUN.SU N)) :=
  dlr_consistent measurable_wilsonDensity (wilsonDensity_nonneg hN) (wilsonDensity_le_two hN) β _

/-- The Wilson partition function in a finite volume with a boundary condition is strictly
positive, at every `N ≠ 0`, every real coupling, every finite volume and every boundary condition.

DERIVED: `0` is the `N ≠ 0` of `hN` and the strict lower bound in the conclusion. -/
theorem wilson_part_pos (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink)
    (ω : IConf (MassGap.SUN.SU N)) :
    0 < part (wilsonDensity (N := N)) β Λ (probHaar (MassGap.SUN.SU N)) ω :=
  part_pos measurable_wilsonDensity (wilsonDensity_nonneg hN) (wilsonDensity_le_two hN) β Λ _ ω

end Wilson

/-! ### Two propositions stated as definitions, with no theorem in this file -/

section NotReached

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

/-- A probability measure on infinite-volume configurations compatible with the specification:
its expectation of every measurable `f` with `|f| ≤ 1` is the `P`-average of the finite-volume
conditional expectations, at every finite volume. This is the DLR equation for a measure;
`DLRConsistent` is the compatibility of the kernels with one another.

DERIVED: `1` is the same normalisation as in `DLRConsistent`. `|f| ≤ 1` is the unit ball of bounded
observables, which is what makes both integrals against `P` finite; by linearity of the integral in
`f`, the condition at any other finite bound `B > 0` is this one applied to `f / B`. -/
def IsGibbsMeasure (φ : G → ℝ) (β : ℝ) (μ : Measure G) (P : Measure (IConf G)) : Prop :=
  IsProbabilityMeasure P ∧
    ∀ (Λ : Finset ILink) (f : IConf G → ℝ), Measurable f → (∀ U, |f U| ≤ 1) →
      (∫ U, f U ∂P) = ∫ U, spec φ β Λ μ f U ∂P

/-- The proposition that a measure satisfying `IsGibbsMeasure` exists. It is a definition; no
 theorem in this file proves or refutes it. `dlr_consistent` gives consistency of the specification;
producing a measure needs compactness of `IConf G` in the product topology and a weak-* limit of the
finite-volume kernels along an exhausting sequence of volumes. -/
def ExistsGibbsMeasure (φ : G → ℝ) (β : ℝ) (μ : Measure G) : Prop :=
  ∃ P : Measure (IConf G), IsGibbsMeasure φ β μ P

/-- Translation of the lattice by one step in direction `d`, acting on links: the direction is
kept and the site moved by `ishift`.

DERIVED: `4` is the dimension, the range of the translation direction `d`. The step itself is
`ishift`'s unit step, documented there. -/
def tshift (d : Fin 4) (l : ILink) : ILink := (l.1, ishift d l.2)

/-- The proposition that the specification commutes with lattice translation: translating the
volume, the observable and the boundary condition together leaves the kernel's value unchanged. It
is a definition; no theorem in this file proves or refutes it. This is the covariance an
infinite-volume limit would need to be a translation-invariant state.

DERIVED: `4` is the dimension, the range of the quantifier over translation directions `d`. -/
def TranslationCovariant (φ : G → ℝ) (β : ℝ) (μ : Measure G) : Prop :=
  ∀ (d : Fin 4) (Λ : Finset ILink) (f : IConf G → ℝ) (ω : IConf G),
    spec φ β (Λ.image (tshift d)) μ (fun U => f (fun l => U (tshift d l))) ω
      = spec φ β Λ μ f (fun l => ω (tshift d l))

end NotReached

#print axioms iunshift_ishift
#print axioms mem_touching
#print axioms mem_boundaryPlaqs
#print axioms mem_plaqsIn
#print axioms boundaryPlaqs_mono
#print axioms links_not_mem_of_mem_sdiff
#print axioms boundaryPlaqs_nonempty
#print axioms boundaryPlaqs_ne_plaqsIn
#print axioms plaqsIn_split_not_local
#print axioms splice_nested
#print axioms measurable_splice_left
#print axioms measurable_splice_right
#print axioms measurable_splice_prod
#print axioms ihol_congr
#print axioms actionOn_split
#print axioms actionOn_sdiff_indep
#print axioms actionBC_split
#print axioms part_pos
#print axioms spec_one
#print axioms spec_congr_off
#print axioms abs_spec_le
#print axioms measurable_spec_right
#print axioms splice_eSplit
#print axioms wt_eSplit
#print axioms num_outer
#print axioms num_spec_eq_num
#print axioms dlr_consistent
#print axioms wilson_dlr_consistent
#print axioms wilson_part_pos

end MassGap.GibbsSpec
