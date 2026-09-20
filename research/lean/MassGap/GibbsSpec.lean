import Mathlib
import MassGap.WilsonLattice
import MassGap.WilsonAction

/-!
# MassGap.GibbsSpec — the finite-volume Gibbs specification on the infinite lattice

A Gibbs *specification* is the family of finite-volume conditional measures, one for each finite
volume `Λ` of links and each configuration `ω` fixed outside it. It is the object the DLR equations
are about, and it is what the tree lacked: every measure in `MassGap` up to now lives on a finite
periodic lattice with its own partition function, so there is nothing for an infinite-volume limit
to be a limit *of*.

## What the specification is

For a finite `Λ : Finset ILink` the inside variables range over `VConf G Λ = ↥Λ → G` and the outside
is held at `ω : IConf G`. `splice Λ u ω` puts the two together. The energy is

    actionOn φ (boundaryPlaqs Λ) (splice Λ u ω)

and `spec φ β Λ μ f ω = (∫ f(splice) e^{−βS}) / (∫ e^{−βS})` against product Haar over `↥Λ`.

## Why `boundaryPlaqs` and not `plaqsIn`

`boundaryPlaqs Λ` is the set of plaquettes with **at least one** link in `Λ`; `plaqsIn Λ` is the set
with **all four** links in `Λ`. Summing over `plaqsIn` gives the free-boundary theory, and it is NOT
a specification: DLR consistency needs the energy to split, for `Λ ⊆ Λ'`, as

    (plaquettes the inner volume owns) + (a remainder that does not read the inner variables),

and `links_not_mem_of_mem_sdiff` is exactly that for `boundaryPlaqs` — a plaquette of
`boundaryPlaqs Λ' \ boundaryPlaqs Λ` has NO link in `Λ`, by the definition of `boundaryPlaqs`.
`plaqsIn_split_not_local` exhibits a nested pair and a plaquette of `plaqsIn Λ' \ plaqsIn Λ` that
DOES read a link of `Λ`, so the same split fails there; `boundaryPlaqs_ne_plaqsIn` shows the two sets
are not equal, so the distinction is not vacuous.

## What is proved

* `actionBC_split` — the load-bearing lemma: the `Λ'` energy of a spliced configuration is the `Λ`
  energy plus a remainder evaluated at the outside configuration alone.
* `part_pos` — the partition function is strictly positive, so the normalisation is legitimate.
* `dlr_consistent` — **the DLR compatibility relation**: for `Λ ⊆ Λ'`, integrating the `Λ` kernel
  against the `Λ'` kernel returns the `Λ'` kernel. Proved by decomposing the product measure over
  `↥Λ'` into the `Λ` block and its complement (`measurePreserving_piEquivPiSubtypeProd`), Fubini on
  that product, and `actionBC_split` to take the remainder out of the inner integral.
* `wilson_dlr_consistent` — the same for the genuine `SU(N)` Wilson density on the infinite
  four-dimensional lattice, against probability Haar.

## What is NOT proved

`ExistsGibbsMeasure` — that some probability measure on `IConf G` satisfies the DLR equations
against this specification. A specification is consistent by the above; producing a measure needs
compactness of `IConf G` and a weak-* limit, which is not here.
`TranslationCovariant` — that the specification commutes with lattice translation.

Foundational footprint only (`#print axioms` at the end).
Build: `python code/lean_build.py build MassGap.GibbsSpec`.
-/

namespace MassGap.GibbsSpec

open MeasureTheory
open MassGap.LatticeGauge MassGap.WilsonLattice

/-! ## Part 0 — the infinite-lattice skeleton

Duplicated from the shared skeleton so this file stands alone; identical names and types. -/

/-- A site of the infinite four-dimensional lattice: one integer coordinate per direction.

DERIVED: `4` is the number of spacetime directions — the dimension of the Clay statement, the same
`d` that `WilsonHypercubic` is instantiated at for the Clay instance (`bd (d := 4)` in `AreaLaw`).
It is an index range, not an extent: each of the four coordinates runs over all of `ℤ`. -/
abbrev ISite : Type := Fin 4 → ℤ

/-- A link: a direction and a site.

DERIVED: `4` is the dimension again — the direction index of a link runs over the four spacetime
directions. Same constant as in `ISite`, not a second one. -/
abbrev ILink : Type := Fin 4 × ISite

/-- A plaquette: an ordered pair of directions spanning its plane, and a site.

DERIVED: both `4`s are the dimension, written twice because a plane in `d` dimensions is spanned by
an ordered PAIR of directions, as `WilsonHypercubic.Plaq` also records. The dimension used twice,
not a separate constant. -/
abbrev IPlaq : Type := (Fin 4 × Fin 4) × ISite

/-- A configuration: a group element on every link of the infinite lattice. -/
abbrev IConf (G : Type) : Type := ILink → G

/-- One lattice step forward in direction `μ`.

DERIVED: `1` is one lattice step — the definition of a neighbouring site, not a length (the lattice
spacing appears nowhere in this file). `4` is the dimension, the range of the direction index.
Mirrors `WilsonHypercubic.shift`, whose `1` is the same step. -/
def ishift (μ : Fin 4) (x : ISite) : ISite := Function.update x μ (x μ + 1)

/-- One lattice step backward in direction `μ`.

DERIVED: the same unit step as `ishift`, taken the other way, so that `iunshift_ishift` holds; `4`
is the dimension. Neither digit is a parameter. -/
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

/-- **The plaquette boundary word**, mirroring `WilsonHypercubic.bd` on the infinite lattice:
`U_μ(x) · U_ν(x+μ̂) · U_μ(x+ν̂)⁻¹ · U_ν(x)⁻¹`. -/
def ibd (q : IPlaq) : List (ILink × Bool) :=
  [((q.1.1, q.2), true), ((q.1.2, ishift q.1.1 q.2), true),
   ((q.1.1, ishift q.1.2 q.2), false), ((q.1.2, q.2), false)]

/-- The four links a plaquette reads. -/
def ilinks (q : IPlaq) : List ILink := (ibd q).map Prod.fst

theorem ilinks_eq (q : IPlaq) :
    ilinks q = [(q.1.1, q.2), (q.1.2, ishift q.1.1 q.2),
                (q.1.1, ishift q.1.2 q.2), (q.1.2, q.2)] := rfl

theorem head_mem_ilinks (q : IPlaq) : (q.1.1, q.2) ∈ ilinks q := by
  rw [ilinks_eq]; simp

/-! ## Part 1 — the plaquettes a finite volume touches -/

/-- **A finite superset of the plaquettes reading a given link.** A plaquette `((a,b),y)` reads the
link `(μ,x)` only if `a = μ` or `b = μ`, and only at `y = x` or `y = x − ν̂` for one of the four
directions `ν`; so sixteen candidates per link suffice. This is what makes `boundaryPlaqs` a
`Finset` at all — `IPlaq` is infinite.

DERIVED: `4` is the dimension — `ν` ranges over the spacetime directions, and the sixteen candidates
are those four directions against the four placements listed in the braces, so the count is the
dimension twice over and not a chosen bound. `mem_touching` proves the superset is big enough, so
nothing downstream rests on the number. -/
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

/-- **The plaquettes with at least one link in `Λ`** — the plaquette set of a finite volume WITH a
boundary condition. Finite because each is `touching` one of the finitely many links of `Λ`. -/
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

/-- **The plaquettes with all four links in `Λ`** — the FREE-boundary plaquette set. -/
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

/-- **The locality fact the DLR split rests on**: a plaquette that touches `Λ'` but not `Λ` reads NO
link of `Λ`. Immediate from the definition of `boundaryPlaqs`, and false for `plaqsIn`. -/
theorem links_not_mem_of_mem_sdiff {Λ Λ' : Finset ILink} {q : IPlaq}
    (hq : q ∈ boundaryPlaqs Λ' \ boundaryPlaqs Λ) : ∀ l ∈ ilinks q, l ∉ Λ := by
  intro l hl hlΛ
  exact (Finset.mem_sdiff.mp hq).2 (mem_boundaryPlaqs.mpr ⟨l, hl, hlΛ⟩)

/-! ### Negative controls: the two plaquette sets are different, and only one is local -/

/-- The origin.

DERIVED: `0` is the zero of `ℤ` in every direction — the origin is the constant-zero site, the
base point of `ISite`, not a magnitude. CHOSEN: that the negative controls below are stated AT the
origin rather than at some other site. That costs nothing: every construction they use (`ibd`,
`ilinks`, `boundaryPlaqs`, `plaqsIn`) is defined uniformly in the base site, so the controls read
the same at any site under relabelling by `ishift`. -/
def osite : ISite := fun _ => 0

/-- The plane-`(0,1)` plaquette at the origin.

DERIVED: `0` and `1` are direction INDICES, not magnitudes — they name the plane spanned by the
first two of the four directions. It is the same plane `PlaqVariance.clayPlaq` is built on
(`((0, 1), fun _ => 0)`), which is the plaquette `corrClay` reads, so the control here and the Clay
observable are stated on the same plane rather than on two unrelated ones. -/
def q01 : IPlaq := ((0, 1), osite)

/-- The one-link volume holding the plaquette's first link.

DERIVED: `0` is a direction index and `4` is the dimension it ranges over. The index is not picked:
`ilinks_eq` makes `q01`'s first link `(q01.1.1, q01.2)`, which is `((0 : Fin 4), osite)`, so the
volume is forced by `q01`. -/
def linkSet : Finset ILink := {((0 : Fin 4), osite)}

theorem q01_link0 : ((0 : Fin 4), osite) ∈ ilinks q01 := by
  rw [ilinks_eq]; simp [q01]

theorem q01_link3 : ((1 : Fin 4), osite) ∈ ilinks q01 := by
  rw [ilinks_eq]; simp [q01]

theorem q01_mem_boundaryPlaqs : q01 ∈ boundaryPlaqs linkSet :=
  mem_boundaryPlaqs.mpr ⟨((0 : Fin 4), osite), q01_link0, Finset.mem_singleton_self _⟩

/-- **The energy is not a sum over the empty set.** Even a single-link volume touches a plaquette,
so `actionOn φ (boundaryPlaqs Λ)` is not identically zero by construction and the kernel below is
not the free product measure in disguise. -/
theorem boundaryPlaqs_nonempty : (boundaryPlaqs linkSet).Nonempty :=
  ⟨q01, q01_mem_boundaryPlaqs⟩

/-- **The two plaquette sets really are different.** On a one-link volume `boundaryPlaqs` holds the
plane-`(0,1)` plaquette at the origin and `plaqsIn` does not, because that plaquette also reads the
link `(1, 0)`. So choosing between them is a choice with content. -/
theorem boundaryPlaqs_ne_plaqsIn : boundaryPlaqs linkSet ≠ plaqsIn linkSet := by
  intro hEq
  have hb : q01 ∈ boundaryPlaqs linkSet := q01_mem_boundaryPlaqs
  rw [hEq] at hb
  have hmem := mem_plaqsIn.mp hb _ q01_link3
  rw [linkSet, Finset.mem_singleton] at hmem
  exact absurd (congrArg Prod.fst hmem) (by decide)

/-- **The free-boundary plaquette set does not split.** There is a nested pair `Λ ⊆ Λ'` and a
plaquette of `plaqsIn Λ' \ plaqsIn Λ` that READS a link of `Λ` — so the remainder of a `plaqsIn`
energy is not a function of the outside variables and the DLR argument has nothing to factor.
Compare `links_not_mem_of_mem_sdiff`, where no such plaquette exists. -/
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

/-- Configurations on a finite volume. -/
abbrev VConf (G : Type) (Λ : Finset ILink) : Type := ↥Λ → G

/-- **The splice**: follow the inside configuration `u` on `Λ` and the outside configuration `ω`
off it. The same piecewise construction `HalfLineTransfer.detBy_inter` uses to intersect
determination sets, here with the inside variables carried on the subtype `↥Λ`. -/
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

/-- Gluing an inner volume's configuration into an outer one. -/
def vglue {Λ Λ' : Finset ILink} (_hsub : Λ ⊆ Λ') (u : VConf G Λ) (u' : VConf G Λ') : VConf G Λ' :=
  fun l => if h : l.1 ∈ Λ then u ⟨l.1, h⟩ else u' l

/-- **Splicing twice on nested volumes composes**: splicing `u` on `Λ` into the `Λ'`-splice of `u'`
is the `Λ'`-splice of the glued configuration. -/
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

/-- The ordered plaquette holonomy on the infinite lattice. -/
noncomputable def ihol (q : IPlaq) (U : IConf G) : G := wilsonHol ibd q U

/-- **The holonomy reads only the plaquette's own four links.** -/
theorem ihol_congr (q : IPlaq) (U V : IConf G) (h : ∀ l ∈ ilinks q, U l = V l) :
    ihol q U = ihol q V := by
  unfold ihol wilsonHol
  congr 1
  refine List.map_congr_left (fun lo hlo => ?_)
  have hmem : lo.1 ∈ ilinks q := List.mem_map.mpr ⟨lo, hlo, rfl⟩
  rw [h lo.1 hmem]

/-- The energy of a set of plaquettes. -/
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

/-- The remainder does not read the inside variables. -/
theorem actionOn_sdiff_indep (φ : G → ℝ) {Λ Λ' : Finset ILink}
    (u : VConf G Λ) (v : IConf G) :
    actionOn φ (boundaryPlaqs Λ' \ boundaryPlaqs Λ) (splice Λ u v)
      = actionOn φ (boundaryPlaqs Λ' \ boundaryPlaqs Λ) v :=
  actionOn_congr φ _ _ _ (fun _ hq l hl => splice_not_mem (links_not_mem_of_mem_sdiff hq l hl))

/-- **THE LOAD-BEARING LEMMA.** For `Λ ⊆ Λ'`, the outer energy of a spliced configuration splits as
the inner energy plus a remainder that is a function of the OUTSIDE configuration alone. This is
what makes the family `spec` a specification rather than a collection of unrelated measures; with
`plaqsIn` in place of `boundaryPlaqs` it is false (`plaqsIn_split_not_local`). -/
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

Two small measure-theoretic tools, copied verbatim from `ActionSplit` so this file does not import
that 100 kB module for them. -/

/-- A bounded measurable real function is integrable against a finite measure. -/
theorem integrable_of_bounded {γ : Type} [MeasurableSpace γ] (m : Measure γ) [IsFiniteMeasure m]
    {g : γ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ z, |g z| ≤ C) : Integrable g m :=
  Integrable.mono' (integrable_const C) hg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hC z)

/-- Change of variables along a measure-preserving map. -/
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

/-- The Boltzmann weight of the finite volume `Λ` with the boundary condition `ω`. -/
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

/-- Product Haar over the links of a finite volume. -/
noncomputable def vol (μ : Measure G) (Λ : Finset ILink) : Measure (VConf G Λ) :=
  Measure.pi (fun _ : ↥Λ => μ)

instance isProbabilityMeasure_vol (μ : Measure G) [IsProbabilityMeasure μ] (Λ : Finset ILink) :
    IsProbabilityMeasure (vol μ Λ) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : ↥Λ => μ)))

/-- The partition function of the volume `Λ` with boundary condition `ω`. -/
noncomputable def part (φ : G → ℝ) (β : ℝ) (Λ : Finset ILink) (μ : Measure G) (ω : IConf G) : ℝ :=
  ∫ u, wt φ β Λ u ω ∂(vol μ Λ)

/-- The unnormalised expectation of `f` in the volume `Λ` with boundary condition `ω`. -/
noncomputable def num (φ : G → ℝ) (β : ℝ) (Λ : Finset ILink) (μ : Measure G)
    (f : IConf G → ℝ) (ω : IConf G) : ℝ :=
  ∫ u, f (splice Λ u ω) * wt φ β Λ u ω ∂(vol μ Λ)

/-- **The specification kernel** `γ_Λ(f | ω)`: the Gibbs expectation of `f` in the finite volume `Λ`
with the configuration outside `Λ` held at `ω`. Mirrors `LatticeGauge.System.expect`. -/
noncomputable def spec (φ : G → ℝ) (β : ℝ) (Λ : Finset ILink) (μ : Measure G)
    (f : IConf G → ℝ) (ω : IConf G) : ℝ :=
  num φ β Λ μ f ω / part φ β Λ μ ω

theorem integrable_wt {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ] (ω : IConf G) :
    Integrable (fun u : VConf G Λ => wt φ β Λ u ω) (vol μ Λ) :=
  integrable_of_bounded _ (measurable_wt_left hφ β Λ ω)
    (fun u => by rw [abs_of_pos (wt_pos φ β Λ u ω)]; exact wt_le hφ0 hφ2 β Λ u ω)

/-- **The partition function is strictly positive**, so the normalisation is legitimate. Same shape
as `WilsonReal.wilsonSystem_partition_pos` in the finite theory. -/
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

/-- **`⟨1⟩ = 1`** — the kernel is a probability kernel. -/
theorem spec_one {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ] (ω : IConf G) :
    spec φ β Λ μ (fun _ => (1 : ℝ)) ω = 1 := by
  unfold spec num
  simp only [one_mul]
  show part φ β Λ μ ω / part φ β Λ μ ω = 1
  exact div_self (part_pos hφ hφ0 hφ2 β Λ μ ω).ne'

/-- **The kernel reads its boundary condition only outside `Λ`.** -/
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

/-- The links of `Λ'` lying outside `Λ`. -/
abbrev OutIdx (Λ Λ' : Finset ILink) : Type := {l : ↥Λ' // l.1 ∉ Λ}

/-- The links of `Λ'` lying inside `Λ`. -/
abbrev InIdx (Λ Λ' : Finset ILink) : Type := {l : ↥Λ' // ¬ (l.1 ∉ Λ)}

/-- The splitting of a `Λ'`-configuration into its outside-of-`Λ` and inside-of-`Λ` blocks. -/
noncomputable def eSplit (G : Type) [MeasurableSpace G] (Λ Λ' : Finset ILink) :
    VConf G Λ' ≃ᵐ ((OutIdx Λ Λ' → G) × (InIdx Λ Λ' → G)) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ↥Λ' => G) (fun l : ↥Λ' => l.1 ∉ Λ)

theorem eSplit_symm_apply (Λ Λ' : Finset ILink)
    (x : OutIdx Λ Λ' → G) (y : InIdx Λ Λ' → G) (l : ↥Λ') :
    (eSplit G Λ Λ').symm (x, y) l = if h : l.1 ∉ Λ then x ⟨l, h⟩ else y ⟨l, h⟩ := rfl

/-- The inside block of `Λ'` is the index set of `Λ`. -/
def subEquivIn {Λ Λ' : Finset ILink} (hsub : Λ ⊆ Λ') : InIdx Λ Λ' ≃ ↥Λ where
  toFun l := ⟨l.1.1, not_not.mp l.2⟩
  invFun l := ⟨⟨l.1, hsub l.2⟩, not_not.mpr l.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Transporting a `Λ`-configuration onto the inside block of `Λ'`. -/
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

/-- The boundary condition the outer variables present to the inner volume: the `Λ'`-splice with the
inside block set to the identity, which the inner splice overwrites anyway.

DERIVED: `1` is the group identity of `G`, not a number — `Group G` is the only structure in scope
and `fun _ => 1` is its unit. Its value is immaterial, which `splice_eSplit` proves: the inner
splice writes over the whole inside block, so any filler would give the same result. -/
noncomputable def vout {Λ Λ' : Finset ILink} (x : OutIdx Λ Λ' → G) (ω : IConf G) : IConf G :=
  splice Λ' ((eSplit G Λ Λ').symm (x, fun _ => 1)) ω

/-- **The two splices agree**: assembling the outer block `x` with a `Λ`-configuration `u` and
splicing into `ω` over `Λ'` is the same as splicing `u` into `vout x ω` over `Λ`. -/
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

/-- **The Boltzmann weight factorises** into the inner weight and a factor the inner variables do
not enter. This is `actionBC_split` in multiplicative form, and it is the whole DLR mechanism. -/
theorem wt_eSplit {φ : G → ℝ} {Λ Λ' : Finset ILink} (hsub : Λ ⊆ Λ') (β : ℝ)
    (x : OutIdx Λ Λ' → G) (u : VConf G Λ) (ω : IConf G) :
    wt φ β Λ' ((eSplit G Λ Λ').symm (x, toIn hsub u)) ω
      = wt φ β Λ u (vout x ω)
        * Real.exp (-β * actionOn φ (boundaryPlaqs Λ' \ boundaryPlaqs Λ) (vout x ω)) := by
  unfold wt
  rw [splice_eSplit hsub x u ω, actionBC_split φ hsub u (vout x ω), mul_add, Real.exp_add]

/-- **The outer unnormalised expectation, conditioned on the outer block.** -/
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

/-- **Averaging the inner kernel against the inner weight returns the inner numerator.** The inner
kernel does not read the inner variables, so it comes out of the integral and cancels the partition
function it is divided by. -/
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

/-- **The DLR compatibility relation** — the defining property of a specification: for nested
volumes, integrating the inner kernel against the outer kernel gives the outer kernel back.

DERIVED: `1` is a NORMALISATION, not a bound on the model — `|f| ≤ 1` names the unit ball of
bounded measurable observables, which is what makes the inner kernel integrable against the outer
one (`abs_spec_le` returns the same bound, and that closure is the point of stating it). No
generality is lost: `num` is linear in `f` and `part` does not mention `f` at all, so the relation
at any other finite bound `B > 0` is this one applied to `f / B`. -/
def DLRConsistent (φ : G → ℝ) (β : ℝ) (μ : Measure G) : Prop :=
  ∀ (Λ Λ' : Finset ILink), Λ ⊆ Λ' → ∀ (f : IConf G → ℝ), Measurable f →
    (∀ U, |f U| ≤ 1) → ∀ ω : IConf G,
      spec φ β Λ' μ (fun v => spec φ β Λ μ f v) ω = spec φ β Λ' μ f ω

/-- **The specification is DLR-consistent.** -/
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

/-! ## Part 6 — the genuine `SU(N)` Wilson specification, and what is NOT reached -/

section Wilson

open MassGap.CompactGauge MassGap.WilsonAction

variable {N : ℕ}

/-- **The Wilson specification on the infinite four-dimensional lattice is DLR-consistent.** The
plaquette density is `WilsonAction.wilsonDensity` — the genuine `1 − Re tr U / N`, not a label — the
single-link measure is probability Haar on `SU(N)`, and the plaquette set of a finite volume is
`boundaryPlaqs`, so the conditioning is a real boundary condition. -/
theorem wilson_dlr_consistent (hN : N ≠ 0) (β : ℝ) :
    DLRConsistent (wilsonDensity (N := N)) β (probHaar (MassGap.SUN.SU N)) :=
  dlr_consistent measurable_wilsonDensity (wilsonDensity_nonneg hN) (wilsonDensity_le_two hN) β _

/-- **The Wilson partition function in a finite volume with a boundary condition is positive.** -/
theorem wilson_part_pos (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink)
    (ω : IConf (MassGap.SUN.SU N)) :
    0 < part (wilsonDensity (N := N)) β Λ (probHaar (MassGap.SUN.SU N)) ω :=
  part_pos measurable_wilsonDensity (wilsonDensity_nonneg hN) (wilsonDensity_le_two hN) β Λ _ ω

end Wilson

/-! ### What this module does not reach, as propositions rather than prose -/

section NotReached

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

/-- A probability measure on infinite-volume configurations that is compatible with the
specification: its expectation of every bounded observable is the average of the finite-volume
conditional expectations. This is the DLR equation for a MEASURE, as opposed to `DLRConsistent`
which is the compatibility of the KERNELS with one another.

DERIVED: `1` is the same normalisation as in `DLRConsistent` — `|f| ≤ 1` is the unit ball of bounded
observables, which is what makes both integrals against `P` finite. It is not a bound on the model,
and by linearity of the integral in `f` the condition at any other finite bound `B > 0` is this one
applied to `f / B`. -/
def IsGibbsMeasure (φ : G → ℝ) (β : ℝ) (μ : Measure G) (P : Measure (IConf G)) : Prop :=
  IsProbabilityMeasure P ∧
    ∀ (Λ : Finset ILink) (f : IConf G → ℝ), Measurable f → (∀ U, |f U| ≤ 1) →
      (∫ U, f U ∂P) = ∫ U, spec φ β Λ μ f U ∂P

/-- **NOT PROVED HERE.** That such a measure exists. Consistency of the specification is proved
(`dlr_consistent`); producing a measure needs compactness of `IConf G` in the product topology and a
weak-* limit of the finite-volume kernels along an exhausting sequence of volumes, neither of which
is in this file. -/
def ExistsGibbsMeasure (φ : G → ℝ) (β : ℝ) (μ : Measure G) : Prop :=
  ∃ P : Measure (IConf G), IsGibbsMeasure φ β μ P

/-- Translation of the lattice by one step in direction `μ`, on links.

DERIVED: `4` is the dimension — the translation direction `d` ranges over the four spacetime
directions. The step itself is `ishift`'s unit step and is declared there. -/
def tshift (d : Fin 4) (l : ILink) : ILink := (l.1, ishift d l.2)

/-- **NOT PROVED HERE.** That the specification commutes with lattice translation — the covariance
that makes an infinite-volume limit a translation-invariant state.

DERIVED: `4` is the dimension — the property is quantified over all four translation directions, so
the numeral is the range of the quantifier and nothing is selected by it. -/
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
