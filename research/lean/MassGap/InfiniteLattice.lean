import Mathlib
import MassGap.WilsonHypercubic

/-!
# MassGap.InfiniteLattice — the infinite four-dimensional lattice, its configuration space, and the
local algebra

`WilsonHypercubic.Site d n = Fin d → Fin n` is finite and periodic. This module gives the
corresponding types over `ℤ` in four directions, the configuration space they index, its topology and
measurable structure, and the algebra of observables that read finitely many links.

## Contents

* Part 1 — `ISite`, `ILink`, `IPlaq`, `IConf`, and the instances saying the index types are infinite,
  countable and decidable.
* Part 2 — `ishift` and `ibd`, mirroring `WilsonHypercubic.shift` and `WilsonHypercubic.bd` with `ℤ`
  in place of `Fin n`, and `linksOf`.
* Part 3 — the configuration space is compact (`compactSpace_IConf`, from `Pi.compactSpace`),
  Hausdorff and second countable, and a continuous function on it is bounded.
* Part 4 — the product measurable structure, and `borelSpace_IConf`, which is where the countability
  of `ILink` is spent: `Pi.borelSpace` wants a countable index, and `Pi.compactSpace` does not.
* Part 5 — `IsLocalOn`, `localAlg` and `quasiLocalAlg`.
* Part 6 — `plaqsIn`, the plaquettes whose whole boundary word lies in a finite volume.
* Part 7 — plaquette terms are members of the local algebra of any volume containing them.
* Part 8 — `finMod`, `siteMod`, `linkMod`, `plaqMod` and `wilsonHol_periodic`: a configuration on the
  periodic lattice, pulled back along coordinatewise reduction, has the finite lattice's holonomies.

## Conventions

A finite volume is a `Finset ILink`, not a `Finset ISite`: the configuration space is indexed by
links, `IsLocalOn` is agreement on links, and `plaqsIn` turns a set of links into a set of
plaquettes. Everything downstream is stated against that choice, and a site-indexed volume would have
to name a link convention to mean anything.

`ibd` mirrors `WilsonHypercubic.bd` letter for letter and `ishift` mirrors `WilsonHypercubic.shift`,
so `WilsonLattice.wilsonHol` reads the same loop on both lattices; `ibd_map_linkMod` is the proof
that the mirroring is exact rather than typographical.

## Scope

This module defines no measure, no action and no state. `localAlg` and `quasiLocalAlg` are
`Subalgebra ℝ (IConf G → ℝ)`; nothing here constructs a functional on either, and nothing here is
stated at a particular group.
-/

namespace MassGap.InfiniteLattice

open MassGap MassGap.WilsonLattice

/-! ## Part 1 — the lattice

Four directions, `ℤ` in each. The types mirror `WilsonHypercubic.Site`, `Link` and `Plaq` with the
periodic coordinate replaced by the integers. -/

/-- Sites of the infinite four-dimensional lattice.

DERIVED: `4` is the number of spacetime directions, the range of a site's coordinate index. It is an
index range, not an extent: each of the four coordinates runs over all of `ℤ`. -/
abbrev ISite : Type := Fin 4 → ℤ

/-- A link: a direction and the site it is based at.

DERIVED: `4` is the dimension again — the range of a link's direction index, the same constant as in
`ISite`. -/
abbrev ILink : Type := Fin 4 × ISite

/-- A plaquette: an ordered pair of directions and a base site.

DERIVED: both `4`s are the dimension. It appears twice because a plane is spanned by an ordered pair
of directions, so the plane index is `Fin 4 × Fin 4` — one constant used twice, not two
constants. -/
abbrev IPlaq : Type := (Fin 4 × Fin 4) × ISite

/-- A configuration assigns a group element to every link. `G` is unconstrained here; the group
structure is asked for only where it is used.

DERIVED: no numeral appears in the statement. -/
abbrev IConf (G : Type) : Type := ILink → G

#print axioms MassGap.InfiniteLattice.ISite
#print axioms MassGap.InfiniteLattice.ILink
#print axioms MassGap.InfiniteLattice.IPlaq
#print axioms MassGap.InfiniteLattice.IConf

/-- There are infinitely many sites.

DERIVED: the type `Infinite ISite` carries no numeral. The `0` in the term is a direction index: the
injection sends `k : ℤ` to the site constant in every direction, and `congrFun h 0` evaluates it at
one direction to recover `k`. Any other direction would prove the same injectivity. -/
instance instInfiniteISite : Infinite ISite :=
  Infinite.of_injective (fun k : ℤ => (fun _ => k : ISite)) (fun _ _ h => congrFun h 0)

#print axioms MassGap.InfiniteLattice.instInfiniteISite

/-- There are infinitely many links, so no `Fintype` instance is available on `ILink`.

DERIVED: the type carries no numeral. In the term, `4` is the dimension — the range of the direction
index — and `0` is a direction index: the injection embeds the sites as the links pointing in one
fixed direction, and any of the four would do, since it is infinitude of the sites that is being
transported. -/
instance instInfiniteILink : Infinite ILink :=
  Infinite.of_injective (fun x : ISite => ((0 : Fin 4), x)) (fun _ _ h => by simpa using h)

#print axioms MassGap.InfiniteLattice.instInfiniteILink

/-- The links are countable, by instance search. Compactness of the configuration space does not
need this; `borelSpace_IConf` does.

DERIVED: no numeral appears in the statement. -/
theorem countable_ILink : Countable ILink := inferInstance

#print axioms MassGap.InfiniteLattice.countable_ILink

/-- The sites are countable too.

DERIVED: no numeral appears in the statement. -/
theorem countable_ISite : Countable ISite := inferInstance

#print axioms MassGap.InfiniteLattice.countable_ISite

/-- Equality of links is decidable: the direction index ranges over a `Fintype` and `ℤ` has
decidable equality, so the site function type does too. `Finset.filter` and `List.toFinset` below are
computable because of this rather than through a classical instance.

DERIVED: no numeral appears in the statement; the definition is `inferInstance`. -/
def decEqILink : DecidableEq ILink := inferInstance

#print axioms MassGap.InfiniteLattice.decEqILink

/-- Equality of plaquettes is decidable, for the same reason.

DERIVED: no numeral appears in the statement. -/
def decEqIPlaq : DecidableEq IPlaq := inferInstance

#print axioms MassGap.InfiniteLattice.decEqIPlaq

/-! ## Part 2 — the plaquette boundary word

`ishift` and `ibd` are `WilsonHypercubic.shift` and `WilsonHypercubic.bd` with `ℤ` in place of
`Fin n`: the same four letters in the same order with the same orientations, so
`WilsonLattice.wilsonHol` reads the same loop. -/

/-- Translate a site one step in direction `μ`. Mirrors `WilsonHypercubic.shift`, with no wrap.

DERIVED: `4` is the dimension, the range of the direction argument. `1` is one lattice step — what
makes the result the neighbouring site — and is added in `ℤ`, so nothing wraps. -/
def ishift (μ : Fin 4) (x : ISite) : ISite :=
  Function.update x μ (x μ + 1)

#print axioms MassGap.InfiniteLattice.ishift

/-- The plaquette boundary word `U_μ(x) · U_ν(x+μ̂) · U_μ(x+ν̂)⁻¹ · U_ν(x)⁻¹`, as a list of links
paired with orientations.

The `Bool` is the orientation — `true` traverses the link forwards, `false` inverts it — and
`WilsonLattice.wilsonHol` turns the word into the ordered product. Identical in shape to
`WilsonHypercubic.bd`; only the site type differs.

DERIVED: the digits in `q.1.1`, `q.1.2` and `q.2` are projections out of `IPlaq`, selecting the two
directions of the plane and the base site. No other numeral appears. -/
def ibd (q : IPlaq) : List (ILink × Bool) :=
  let μ := q.1.1
  let ν := q.1.2
  let x := q.2
  [((μ, x), true), ((ν, ishift μ x), true),
   ((μ, ishift ν x), false), ((ν, x), false)]

#print axioms MassGap.InfiniteLattice.ibd

/-- The boundary word written out, for rewriting. True by `rfl`.

DERIVED: `1` and `2` are the product projections out of `IPlaq` — `q.1.1` and `q.1.2` the two
spanning directions, `q.2` the base site — exactly as in `ibd`. No other numeral appears. -/
theorem ibd_def (q : IPlaq) :
    ibd q = [((q.1.1, q.2), true), ((q.1.2, ishift q.1.1 q.2), true),
             ((q.1.1, ishift q.1.2 q.2), false), ((q.1.2, q.2), false)] := rfl

#print axioms MassGap.InfiniteLattice.ibd_def

/-- The word has four letters — a plaquette is a square, and the word is its four sides.

DERIVED: `4` is the length of the list, the number of sides of a square. It is not the dimension,
although the two happen to agree here. -/
theorem ibd_length (q : IPlaq) : (ibd q).length = 4 := rfl

#print axioms MassGap.InfiniteLattice.ibd_length

/-- The links the word names, in order.

DERIVED: `1` and `2` are the product projections out of `IPlaq` — `q.1.1` and `q.1.2` the two
spanning directions, `q.2` the base site — exactly as in `ibd`. No other numeral appears. -/
theorem ibd_links (q : IPlaq) :
    (ibd q).map Prod.fst
      = [(q.1.1, q.2), (q.1.2, ishift q.1.1 q.2),
         (q.1.1, ishift q.1.2 q.2), (q.1.2, q.2)] := rfl

#print axioms MassGap.InfiniteLattice.ibd_links

/-- The orientations: two forwards then two backwards, so the loop closes.

DERIVED: no numeral appears in the statement; the list is of `Bool`. -/
theorem ibd_orientations (q : IPlaq) :
    (ibd q).map Prod.snd = [true, true, false, false] := rfl

#print axioms MassGap.InfiniteLattice.ibd_orientations

/-- The holonomy is the ordered product `U_μ(x) · U_ν(x+μ̂) · U_μ(x+ν̂)⁻¹ · U_ν(x)⁻¹`, written out
so that the loop can be read without unfolding `wilsonHol`.

DERIVED: `1` and `2` are the product projections out of `IPlaq` — `q.1.1` and `q.1.2` the two
spanning directions, `q.2` the base site — exactly as in `ibd`. No other numeral appears. -/
theorem wilsonHol_ibd {G : Type} [Group G] (q : IPlaq) (U : IConf G) :
    wilsonHol ibd q U
      = U (q.1.1, q.2) * (U (q.1.2, ishift q.1.1 q.2)
          * ((U (q.1.1, ishift q.1.2 q.2))⁻¹ * (U (q.1.2, q.2))⁻¹)) := by
  simp [wilsonHol, ibd_def]

#print axioms MassGap.InfiniteLattice.wilsonHol_ibd

/-- A degenerate plane contributes nothing, exactly as in `WilsonHypercubic.bd_diag_hol_one`: with
`μ = ν` the word retraces itself and the holonomy is the identity. So `IPlaq` may carry every ordered
pair of directions without excluding the diagonal.

DERIVED: `4` is the dimension, the range of `μ`. `1` is the identity element of the group `G`, not a
number. -/
theorem ibd_diag_hol_one {G : Type} [Group G] (μ : Fin 4) (x : ISite) (U : IConf G) :
    wilsonHol ibd ((μ, μ), x) U = 1 := by
  simp [wilsonHol, ibd_def]

#print axioms MassGap.InfiniteLattice.ibd_diag_hol_one

/-- The links a single plaquette reads, as a `Finset`, obtained from the word by `List.toFinset`.

DERIVED: no numeral appears in the statement. -/
def linksOf (q : IPlaq) : Finset ILink := ((ibd q).map Prod.fst).toFinset

#print axioms MassGap.InfiniteLattice.linksOf

/-- A plaquette reads at most four links — at most, because `linksOf` deduplicates and a degenerate
plane names fewer.

DERIVED: `4` is the length of the boundary word, which bounds the cardinality of the set of links the
word names. -/
theorem linksOf_card_le (q : IPlaq) : (linksOf q).card ≤ 4 := by
  refine le_trans (List.toFinset_card_le _) ?_
  simp [ibd_def]

#print axioms MassGap.InfiniteLattice.linksOf_card_le

/-- Membership in `linksOf`, in the form the boundary-word lemmas produce.

DERIVED: no numeral appears in the statement. -/
theorem mem_linksOf {q : IPlaq} {l : ILink} : l ∈ linksOf q ↔ l ∈ (ibd q).map Prod.fst :=
  List.mem_toFinset

#print axioms MassGap.InfiniteLattice.mem_linksOf

/-- The base link of a plaquette is one of its own links — the `linksOf` fact `mem_plaqsIn` needs.

DERIVED: the digits in `q.1.1` and `q.2` are projections out of `IPlaq`, selecting the first
direction and the base site. No other numeral appears. -/
theorem base_mem_linksOf (q : IPlaq) : (q.1.1, q.2) ∈ linksOf q := by
  simp [linksOf, ibd_def]

#print axioms MassGap.InfiniteLattice.base_mem_linksOf

/-! ## Part 3 — the configuration space is compact

`IConf G = ILink → G` carries the product topology. Compactness is what puts a sequence of
finite-volume measures on one fixed space rather than on a growing family of spaces, so that a weak-*
limit point is available; it is also what lets `bounded_of_continuous` hold without a separate
boundedness hypothesis. -/

section Space

variable {G : Type} [TopologicalSpace G]

/-- The configuration space is compact when the group is. `Pi.compactSpace` fires on
`IConf G = ILink → G` with no countability, no metrizability and no choice of topology beyond the
product topology already on the function type; the index set may be any type.

DERIVED: no numeral appears in the statement. -/
theorem compactSpace_IConf [CompactSpace G] : CompactSpace (IConf G) := inferInstance

#print axioms MassGap.InfiniteLattice.compactSpace_IConf

/-- The same, stated on `Set.univ` — the form `IsCompact.bddAbove` and the Riesz representation
 theorem take.

DERIVED: no numeral appears in the statement. -/
theorem isCompact_univ_IConf [CompactSpace G] :
    IsCompact (Set.univ : Set (IConf G)) := isCompact_univ

#print axioms MassGap.InfiniteLattice.isCompact_univ_IConf

/-- The configuration space is Hausdorff when the group is.

DERIVED: no numeral appears in the statement. -/
theorem t2Space_IConf [T2Space G] : T2Space (IConf G) := inferInstance

#print axioms MassGap.InfiniteLattice.t2Space_IConf

/-- A product over a countable index of second-countable spaces is second countable; over an
uncountable index it need not be. This is the hypothesis `borelSpace_IConf` needs, and the reason
`countable_ILink` is proved above.

DERIVED: no numeral appears in the statement. -/
theorem secondCountable_IConf [SecondCountableTopology G] :
    SecondCountableTopology (IConf G) := inferInstance

#print axioms MassGap.InfiniteLattice.secondCountable_IConf

/-- The configuration space is nonempty whenever the group is. Stated at its own type variable `H`,
so it carries no topology and no other structure.

DERIVED: no numeral appears in the statement. -/
theorem nonempty_IConf {H : Type} [Nonempty H] : Nonempty (IConf H) := inferInstance

#print axioms MassGap.InfiniteLattice.nonempty_IConf

/-- Evaluation at one link is continuous. Cylinder functions are built from these, so this is the
continuity every local observable rests on.

DERIVED: no numeral appears in the statement. -/
theorem continuous_coord (l : ILink) : Continuous (fun U : IConf G => U l) := continuous_apply l

#print axioms MassGap.InfiniteLattice.continuous_coord

/-- A continuous real function on a compact configuration space is bounded in absolute value.
Requires `CompactSpace G`. The witness is built as `|a| + |b|` from the bounds of the range, so it is
nonnegative; the statement itself asserts only existence.

DERIVED: no numeral appears in the statement; `C` is existentially quantified. -/
theorem bounded_of_continuous [CompactSpace G] {F : IConf G → ℝ} (hF : Continuous F) :
    ∃ C : ℝ, ∀ U, |F U| ≤ C := by
  obtain ⟨b, hb⟩ := (isCompact_range hF).bddAbove
  obtain ⟨a, ha⟩ := (isCompact_range hF).bddBelow
  refine ⟨|a| + |b|, fun U => ?_⟩
  have h1 : F U ≤ b := hb (Set.mem_range_self U)
  have h2 : a ≤ F U := ha (Set.mem_range_self U)
  have h3 : -|a| ≤ a := neg_abs_le a
  have h4 : b ≤ |b| := le_abs_self b
  have h5 : (0 : ℝ) ≤ |a| := abs_nonneg a
  have h6 : (0 : ℝ) ≤ |b| := abs_nonneg b
  exact abs_le.mpr ⟨by linarith, by linarith⟩

#print axioms MassGap.InfiniteLattice.bounded_of_continuous

end Space

/-! ## Part 4 — the measurable structure

The measurable space on `IConf G` is `MeasurableSpace.pi`. With a countable index and a second
countable group it coincides with the Borel structure of the product topology, so "measurable" and
"Borel" name the same thing here and a continuous observable is measurable. -/

section Measure

variable {G : Type} [MeasurableSpace G]

/-- Evaluation at one link is measurable, read off the product `MeasurableSpace.pi` instance.

DERIVED: no numeral appears in the statement. -/
theorem measurable_coord (l : ILink) : Measurable (fun U : IConf G => U l) :=
  measurable_pi_apply l

#print axioms MassGap.InfiniteLattice.measurable_coord

/-- The product measurable structure is the Borel structure of the product topology. Needs the index
countable (`countable_ILink`) and the group second countable and Borel; without those the product
σ-algebra can be strictly smaller than the Borel σ-algebra of the product topology, and "Borel
measure" would name a different object from "cylinder measure".

DERIVED: no numeral appears in the statement. -/
theorem borelSpace_IConf [TopologicalSpace G] [SecondCountableTopology G] [BorelSpace G] :
    BorelSpace (IConf G) := inferInstance

#print axioms MassGap.InfiniteLattice.borelSpace_IConf

/-- A continuous observable is measurable, through `borelSpace_IConf`. This is what lets a
continuous local observable be integrated against a Borel measure on the configuration space.

DERIVED: no numeral appears in the statement. -/
theorem measurable_of_continuous [TopologicalSpace G] [SecondCountableTopology G] [BorelSpace G]
    {F : IConf G → ℝ} (hF : Continuous F) : Measurable F := by
  haveI : BorelSpace (IConf G) := borelSpace_IConf
  exact hF.measurable

#print axioms MassGap.InfiniteLattice.measurable_of_continuous

end Measure

/-! ## Part 5 — finite volumes and the local algebra

A finite volume is a `Finset ILink`. An observable is local in a volume when the volume's links
determine it — the same notion as `ReflectionPositivity.hol_congr_on_support`, which says a plaquette
holonomy is determined by the links its own word names, and as the locality clause of
`LogConvex.localObs`. `localAlg` asks for continuity in addition; the measurability and boundedness
clauses of `localObs` are then recovered by `measurable_of_continuous` and `bounded_of_continuous`
rather than assumed. -/

section Local

variable {G : Type}

/-- `F` is determined by the links in `S`: two configurations that agree on `S` are given the same
value, whatever they do on the infinitely many links outside it.

DERIVED: no numeral appears in the statement. -/
def IsLocalOn (S : Finset ILink) (F : IConf G → ℝ) : Prop :=
  ∀ U V : IConf G, (∀ l ∈ S, U l = V l) → F U = F V

#print axioms MassGap.InfiniteLattice.IsLocalOn

/-- Locality in a bigger volume is a weaker requirement.

DERIVED: no numeral appears in the statement. -/
theorem IsLocalOn.mono {S T : Finset ILink} {F : IConf G → ℝ} (h : S ⊆ T) (hF : IsLocalOn S F) :
    IsLocalOn T F := fun U V hUV => hF U V (fun l hl => hUV l (h hl))

#print axioms MassGap.InfiniteLattice.IsLocalOn.mono

/-- A product of local observables is local on the union of their volumes.

Note the shadowing in the binders: the section variable `G : Type` is what `IConf G` refers to, since
the binder type is elaborated before `F` and `G` are introduced, while the second observable is then
also called `G`. Both factors are real-valued functions on the configuration space of the section's
group.

DERIVED: no numeral appears in the statement. -/
theorem IsLocalOn.mul {S T : Finset ILink} {F G : IConf G → ℝ}
    (hF : IsLocalOn S F) (hG : IsLocalOn T G) : IsLocalOn (S ∪ T) (F * G) := by
  classical
  intro U V h
  show F U * G U = F V * G V
  rw [hF U V (fun l hl => h l (Finset.mem_union_left _ hl)),
    hG U V (fun l hl => h l (Finset.mem_union_right _ hl))]

#print axioms MassGap.InfiniteLattice.IsLocalOn.mul


/-- The restriction of a configuration to a volume, as a function on the subtype `{l // l ∈ S}`.

DERIVED: the only numeral is the `1` of `l.1`, the projection selecting a subtype element's
value. -/
def restrict (S : Finset ILink) (U : IConf G) : {l : ILink // l ∈ S} → G := fun l => U l.1

#print axioms MassGap.InfiniteLattice.restrict

/-- Anything that factors through the restriction to `S` is local in `S`.

DERIVED: no numeral appears in the statement. -/
theorem isLocalOn_comp_restrict (S : Finset ILink) (f : ({l : ILink // l ∈ S} → G) → ℝ) :
    IsLocalOn S (fun U => f (restrict S U)) := by
  intro U V h
  have : restrict S U = restrict S V := funext fun l => h l.1 l.2
  simp [this]

#print axioms MassGap.InfiniteLattice.isLocalOn_comp_restrict

section LocalTop

variable [TopologicalSpace G]

/-- The restriction map is continuous — each of its coordinates is a coordinate of `IConf G`.

DERIVED: no numeral appears in the statement. -/
theorem continuous_restrict (S : Finset ILink) : Continuous (restrict (G := G) S) :=
  continuous_pi fun l => continuous_apply l.1

#print axioms MassGap.InfiniteLattice.continuous_restrict

/-- The observables of a finite volume: the functions that are continuous and determined by the
links in `S`. A unital `Subalgebra ℝ (IConf G → ℝ)` — closed under `+` and `*`, containing the
constants and the real scalars.

Continuity rather than measurability with a bound carries the definition because the configuration
space is compact: `bounded_of_continuous` and `measurable_of_continuous` recover the other two
clauses of `LogConvex.localObs`, and continuity is what a weak-* limit of states is tested against.

DERIVED: no numeral appears in the statement; `one_mem'` and `zero_mem'` are field names of
`Subalgebra`, not numerals. -/
def localAlg (S : Finset ILink) : Subalgebra ℝ (IConf G → ℝ) where
  carrier := {F | Continuous F ∧ IsLocalOn S F}
  mul_mem' := by
    rintro F H ⟨hFc, hFl⟩ ⟨hHc, hHl⟩
    exact ⟨hFc.mul hHc, fun U V h => by
      show F U * H U = F V * H V
      rw [hFl U V h, hHl U V h]⟩
  one_mem' := ⟨continuous_const, fun _ _ _ => rfl⟩
  add_mem' := by
    rintro F H ⟨hFc, hFl⟩ ⟨hHc, hHl⟩
    exact ⟨hFc.add hHc, fun U V h => by
      show F U + H U = F V + H V
      rw [hFl U V h, hHl U V h]⟩
  zero_mem' := ⟨continuous_const, fun _ _ _ => rfl⟩
  algebraMap_mem' := fun r => ⟨continuous_const, fun _ _ _ => rfl⟩

#print axioms MassGap.InfiniteLattice.localAlg

/-- Membership in the local algebra, unfolded. True by `Iff.rfl`.

DERIVED: no numeral appears in the statement. -/
theorem mem_localAlg {S : Finset ILink} {F : IConf G → ℝ} :
    F ∈ localAlg S ↔ Continuous F ∧ IsLocalOn S F := Iff.rfl

#print axioms MassGap.InfiniteLattice.mem_localAlg

/-- Every member of `localAlg S` is continuous — the first clause, projected out. A function of
finitely many coordinates need not be continuous, so this does not follow from locality, and it is
what gives a space on which a weak-* limit of states can act.

DERIVED: no numeral appears in the statement. -/
theorem localAlg_continuous {S : Finset ILink} {F : IConf G → ℝ} (hF : F ∈ localAlg S) :
    Continuous F := hF.1

#print axioms MassGap.InfiniteLattice.localAlg_continuous

/-- And every member is local in `S` — the second clause, projected out.

DERIVED: no numeral appears in the statement. -/
theorem localAlg_isLocalOn {S : Finset ILink} {F : IConf G → ℝ} (hF : F ∈ localAlg S) :
    IsLocalOn S F := hF.2

#print axioms MassGap.InfiniteLattice.localAlg_isLocalOn

/-- Enlarging the volume can only add observables. This is what makes the family directed by
inclusion, hence its union an algebra.

DERIVED: no numeral appears in the statement. -/
theorem localAlg_mono {S T : Finset ILink} (h : S ⊆ T) : localAlg (G := G) S ≤ localAlg T := by
  rintro F ⟨hFc, hFl⟩
  exact ⟨hFc, hFl.mono h⟩

#print axioms MassGap.InfiniteLattice.localAlg_mono

/-- On a compact configuration space every member of `localAlg S` is bounded, by
`bounded_of_continuous`, so the boundedness clause of `localObs` is recovered rather than assumed.

DERIVED: no numeral appears in the statement; `C` is existentially quantified. -/
theorem localAlg_bounded [CompactSpace G] {S : Finset ILink} {F : IConf G → ℝ}
    (hF : F ∈ localAlg S) : ∃ C : ℝ, ∀ U, |F U| ≤ C :=
  bounded_of_continuous hF.1

#print axioms MassGap.InfiniteLattice.localAlg_bounded

/-- And measurable, by `measurable_of_continuous`, so it can be integrated against a Borel measure
on the configuration space. Requires the group second countable and Borel.

DERIVED: no numeral appears in the statement. -/
theorem localAlg_measurable [MeasurableSpace G] [SecondCountableTopology G] [BorelSpace G]
    {S : Finset ILink} {F : IConf G → ℝ} (hF : F ∈ localAlg S) : Measurable F :=
  measurable_of_continuous hF.1

#print axioms MassGap.InfiniteLattice.localAlg_measurable

/-- The observables local in some finite volume: continuous, with the volume existentially
quantified. A unital `Subalgebra ℝ (IConf G → ℝ)`, closed under products and sums because two
observables can be put in the union of their volumes by `IsLocalOn.mono`.

DERIVED: no numeral appears in the statement; `one_mem'` and `zero_mem'` are field names of
`Subalgebra`, and `∅` is the empty volume witnessing locality of a constant. -/
def quasiLocalAlg : Subalgebra ℝ (IConf G → ℝ) where
  carrier := {F | Continuous F ∧ ∃ S : Finset ILink, IsLocalOn S F}
  mul_mem' := by
    rintro F H ⟨hFc, S, hFl⟩ ⟨hHc, T, hHl⟩
    refine ⟨hFc.mul hHc, S ∪ T, fun U V h => ?_⟩
    show F U * H U = F V * H V
    rw [(hFl.mono Finset.subset_union_left) U V h,
        (hHl.mono Finset.subset_union_right) U V h]
  one_mem' := ⟨continuous_const, ∅, fun _ _ _ => rfl⟩
  add_mem' := by
    rintro F H ⟨hFc, S, hFl⟩ ⟨hHc, T, hHl⟩
    refine ⟨hFc.add hHc, S ∪ T, fun U V h => ?_⟩
    show F U + H U = F V + H V
    rw [(hFl.mono Finset.subset_union_left) U V h,
        (hHl.mono Finset.subset_union_right) U V h]
  zero_mem' := ⟨continuous_const, ∅, fun _ _ _ => rfl⟩
  algebraMap_mem' := fun r => ⟨continuous_const, ∅, fun _ _ _ => rfl⟩

#print axioms MassGap.InfiniteLattice.quasiLocalAlg

/-- Membership in the quasi-local algebra, unfolded. True by `Iff.rfl`.

DERIVED: no numeral appears in the statement. -/
theorem mem_quasiLocalAlg {F : IConf G → ℝ} :
    F ∈ quasiLocalAlg ↔ Continuous F ∧ ∃ S : Finset ILink, IsLocalOn S F := Iff.rfl

#print axioms MassGap.InfiniteLattice.mem_quasiLocalAlg

/-- Every finite volume's algebra sits inside it.

DERIVED: no numeral appears in the statement. -/
theorem localAlg_le_quasiLocalAlg (S : Finset ILink) :
    localAlg (G := G) S ≤ quasiLocalAlg := by
  rintro F ⟨hFc, hFl⟩
  exact ⟨hFc, S, hFl⟩

#print axioms MassGap.InfiniteLattice.localAlg_le_quasiLocalAlg

/-- A continuous function of one link's value is an observable local in the singleton volume `{l}`:
the generating example, and the shape of a cylinder function.

DERIVED: no numeral appears in the statement; `{l}` is a singleton `Finset`, not a cardinality. -/
theorem coordObs_mem_localAlg (l : ILink) {f : G → ℝ} (hf : Continuous f) :
    (fun U : IConf G => f (U l)) ∈ localAlg {l} :=
  ⟨hf.comp (continuous_apply l), fun U V h => by
    show f (U l) = f (V l)
    rw [h l (Finset.mem_singleton_self l)]⟩

#print axioms MassGap.InfiniteLattice.coordObs_mem_localAlg

end LocalTop

end Local

/-! ## Part 6 — the plaquettes of a finite volume

`IPlaq` is infinite; a finite volume touches finitely many. `plaqsIn S` is the finite set of
plaquettes whose whole boundary word lies in `S`, which is the condition under which a plaquette's
contribution to an action is a function of the volume's links alone. -/

section Plaquettes

/-- The plaquettes of a volume: those all of whose boundary links lie in `S`.

Finite by construction. A plaquette all of whose links lie in `S` has its base link in `S`, so its
base site is one of the finitely many sites `S` mentions, and the plane index ranges over a
`Fintype`; the filter cuts that product down. `mem_plaqsIn` shows the candidate set makes no
difference to membership.

DERIVED: both `4`s are the dimension — the range of each of the two direction indices of a plane.
They are finiteness scaffolding: `mem_plaqsIn` characterises membership as `linksOf q ⊆ S`, with no
reference to them. -/
def plaqsIn (S : Finset ILink) : Finset IPlaq :=
  (((Finset.univ : Finset (Fin 4 × Fin 4)) ×ˢ (S.image Prod.snd)).filter
    (fun q => ∀ l ∈ (ibd q).map Prod.fst, l ∈ S))

#print axioms MassGap.InfiniteLattice.plaqsIn

/-- A plaquette is in the volume exactly when the volume contains every link it reads. The candidate
set in the definition of `plaqsIn` plays no part in the characterisation.

DERIVED: no numeral appears in the statement. -/
theorem mem_plaqsIn {S : Finset ILink} {q : IPlaq} : q ∈ plaqsIn S ↔ linksOf q ⊆ S := by
  constructor
  · intro h l hl
    exact (Finset.mem_filter.mp h).2 l (mem_linksOf.mp hl)
  · intro h
    refine Finset.mem_filter.mpr ⟨?_, fun l hl => h (mem_linksOf.mpr hl)⟩
    refine Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr ⟨(q.1.1, q.2), h (base_mem_linksOf q), rfl⟩

#print axioms MassGap.InfiniteLattice.mem_plaqsIn

/-- Growing the volume can only add plaquettes — what an increasing exhaustion of the lattice by
finite volumes needs.

DERIVED: no numeral appears in the statement. -/
theorem plaqsIn_mono {S T : Finset ILink} (h : S ⊆ T) : plaqsIn S ⊆ plaqsIn T := by
  intro q hq
  exact mem_plaqsIn.mpr ((mem_plaqsIn.mp hq).trans h)

#print axioms MassGap.InfiniteLattice.plaqsIn_mono

/-- The same, as `Monotone`.

DERIVED: no numeral appears in the statement. -/
theorem monotone_plaqsIn : Monotone plaqsIn := fun _ _ h => plaqsIn_mono h

#print axioms MassGap.InfiniteLattice.monotone_plaqsIn

/-- Every plaquette of a volume reads only the volume's links — the forward direction of
`mem_plaqsIn`, named.

DERIVED: no numeral appears in the statement. -/
theorem linksOf_subset_of_mem_plaqsIn {S : Finset ILink} {q : IPlaq} (hq : q ∈ plaqsIn S) :
    linksOf q ⊆ S := mem_plaqsIn.mp hq

#print axioms MassGap.InfiniteLattice.linksOf_subset_of_mem_plaqsIn

/-- The underlying set of `plaqsIn S`, as a set comprehension rather than read off the `Finset`; with
`finite_plaqs_of_volume` below, this says the plaquettes a finite volume touches are a finite set of
an infinite type.

DERIVED: no numeral appears in the statement. -/
theorem coe_plaqsIn (S : Finset ILink) :
    (plaqsIn S : Set IPlaq) = {q : IPlaq | linksOf q ⊆ S} := by
  ext q
  simpa using mem_plaqsIn

#print axioms MassGap.InfiniteLattice.coe_plaqsIn

theorem finite_plaqs_of_volume (S : Finset ILink) : {q : IPlaq | linksOf q ⊆ S}.Finite := by
  rw [← coe_plaqsIn S]
  exact (plaqsIn S).finite_toSet

#print axioms MassGap.InfiniteLattice.finite_plaqs_of_volume

/-- At most sixteen plaquettes per link of the volume: every plaquette of `S` bases at a site `S`
mentions, and there are sixteen ordered planes through a site.

DERIVED: `16` is `Fintype.card (Fin 4 × Fin 4)`, the number of ordered pairs of directions in four
dimensions. It is counted from the dimension rather than chosen, and the bound is not claimed to be
attained. -/
theorem plaqsIn_card_le (S : Finset ILink) : (plaqsIn S).card ≤ 16 * S.card := by
  refine le_trans (Finset.card_filter_le _ _) ?_
  have h : (((Finset.univ : Finset (Fin 4 × Fin 4)) ×ˢ (S.image Prod.snd))).card
      = 16 * (S.image Prod.snd).card := by
    simp [Finset.card_product]
  rw [h]
  exact Nat.mul_le_mul le_rfl (Finset.card_image_le)

#print axioms MassGap.InfiniteLattice.plaqsIn_card_le

/-- Every plaquette belongs to the volume of its own links, so the volumes exhaust the plaquettes.

DERIVED: no numeral appears in the statement. -/
theorem mem_plaqsIn_linksOf (q : IPlaq) : q ∈ plaqsIn (linksOf q) :=
  mem_plaqsIn.mpr (Finset.Subset.refl _)

#print axioms MassGap.InfiniteLattice.mem_plaqsIn_linksOf

end Plaquettes

/-! ## Part 7 — plaquette terms are local observables

`ReflectionPositivity.hol_congr_on_support` proves, for the finite lattice and `SU N`, that a
plaquette's holonomy reads only the links its own word names. The same argument works here for any
group, and it is what puts a plaquette term of a finite-volume action in that volume's local
algebra. -/

section Terms

variable {G : Type} [Group G]

/-- A plaquette's holonomy reads only the links in its own boundary word — the infinite-lattice,
any-group form of `ReflectionPositivity.hol_congr_on_support`. Requires only `Group G`.

DERIVED: no numeral appears in the statement. -/
theorem ihol_congr_on_support (q : IPlaq) (U V : IConf G)
    (h : ∀ l ∈ (ibd q).map Prod.fst, U l = V l) :
    wilsonHol ibd q U = wilsonHol ibd q V := by
  unfold wilsonHol
  congr 1
  refine List.map_congr_left ?_
  intro lo hlo
  have : U lo.1 = V lo.1 := h lo.1 (List.mem_map_of_mem hlo)
  rw [this]

#print axioms MassGap.InfiniteLattice.ihol_congr_on_support

/-- So a plaquette term is local in any volume containing the plaquette. `φ` is arbitrary: no
continuity and no measurability is asked of it here.

DERIVED: no numeral appears in the statement. -/
theorem isLocalOn_plaqTerm {S : Finset ILink} {q : IPlaq} (hq : q ∈ plaqsIn S) (φ : G → ℝ) :
    IsLocalOn S (fun U : IConf G => φ (wilsonHol ibd q U)) := by
  intro U V h
  have hsub := linksOf_subset_of_mem_plaqsIn hq
  have hUV : wilsonHol ibd q U = wilsonHol ibd q V :=
    ihol_congr_on_support q U V fun l hl => h l (hsub (mem_linksOf.mpr hl))
  show φ (wilsonHol ibd q U) = φ (wilsonHol ibd q V)
  rw [hUV]

#print axioms MassGap.InfiniteLattice.isLocalOn_plaqTerm

/-- A sum of plaquette terms over any finite set of plaquettes inside the volume is local in it —
the shape of a finite-volume action. `T` is a separate `Finset IPlaq`, required by `hT` to sit inside
`plaqsIn S` but not required to exhaust it.

DERIVED: no numeral appears in the statement. -/
theorem isLocalOn_plaqSum (S : Finset ILink) (T : Finset IPlaq) (hT : ∀ q ∈ T, q ∈ plaqsIn S)
    (φ : G → ℝ) :
    IsLocalOn S (fun U : IConf G => ∑ q ∈ T, φ (wilsonHol ibd q U)) := by
  intro U V h
  exact Finset.sum_congr rfl fun q hq => isLocalOn_plaqTerm (hT q hq) φ U V h

#print axioms MassGap.InfiniteLattice.isLocalOn_plaqSum

section TermsTop

variable [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G]

/-- The ordered product of link-dependent step factors is continuous, by induction on the word — the
continuity counterpart of `WilsonLattice.measurable_stepListProd`. Requires `ContinuousMul G` and
`ContinuousInv G`.

DERIVED: the digits in `lo.1` and `lo.2` are projections out of the pair `ILink × Bool`, selecting
the link and its orientation. No other numeral appears. -/
theorem continuous_stepListProd (w : List (ILink × Bool)) :
    Continuous (fun U : IConf G => (w.map (fun lo => if lo.2 then U lo.1 else (U lo.1)⁻¹)).prod) := by
  induction w with
  | nil => simp only [List.map_nil, List.prod_nil]; exact continuous_const
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons]
    refine Continuous.mul ?_ ih
    by_cases ha : a.2 = true
    · have he : (fun U : IConf G => if a.2 then U a.1 else (U a.1)⁻¹) = fun U => U a.1 :=
        funext fun U => if_pos ha
      rw [he]; exact continuous_apply a.1
    · have he : (fun U : IConf G => if a.2 then U a.1 else (U a.1)⁻¹) = fun U => (U a.1)⁻¹ :=
        funext fun U => if_neg ha
      rw [he]; exact (continuous_apply a.1).inv

#print axioms MassGap.InfiniteLattice.continuous_stepListProd

/-- The plaquette holonomy is continuous in the configuration.

DERIVED: no numeral appears in the statement. -/
theorem continuous_wilsonHol_ibd (q : IPlaq) :
    Continuous (wilsonHol (G := G) ibd q) := continuous_stepListProd (ibd q)

#print axioms MassGap.InfiniteLattice.continuous_wilsonHol_ibd

/-- A plaquette term with continuous `φ` is a member of `localAlg S` for any volume `S` containing
its plaquette: continuous by `continuous_wilsonHol_ibd`, local by `isLocalOn_plaqTerm`. This is what
a finite-volume action is assembled from.

DERIVED: no numeral appears in the statement. -/
theorem plaqTerm_mem_localAlg {S : Finset ILink} {q : IPlaq} (hq : q ∈ plaqsIn S) {φ : G → ℝ}
    (hφ : Continuous φ) : (fun U : IConf G => φ (wilsonHol ibd q U)) ∈ localAlg S :=
  ⟨hφ.comp (continuous_wilsonHol_ibd q), isLocalOn_plaqTerm hq φ⟩

#print axioms MassGap.InfiniteLattice.plaqTerm_mem_localAlg

/-- And so is any finite sum of them inside the volume: the finite-volume action of a volume is an
element of that volume's local algebra.

DERIVED: no numeral appears in the statement. -/
theorem plaqSum_mem_localAlg (S : Finset ILink) (T : Finset IPlaq) (hT : ∀ q ∈ T, q ∈ plaqsIn S)
    {φ : G → ℝ} (hφ : Continuous φ) :
    (fun U : IConf G => ∑ q ∈ T, φ (wilsonHol ibd q U)) ∈ localAlg S :=
  ⟨continuous_finsetSum T fun q _ => hφ.comp (continuous_wilsonHol_ibd q),
    isLocalOn_plaqSum S T hT φ⟩

#print axioms MassGap.InfiniteLattice.plaqSum_mem_localAlg

end TermsTop

/-- The plaquette holonomy is measurable in the configuration — `WilsonLattice.measurable_wilsonHol`
at this boundary word. Requires `MeasurableMul₂ G` and `MeasurableInv G`.

DERIVED: no numeral appears in the statement; the subscript in `MeasurableMul₂` is part of a name. -/
theorem measurable_wilsonHol_ibd [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (q : IPlaq) : Measurable (wilsonHol (G := G) ibd q) :=
  measurable_wilsonHol ibd q

#print axioms MassGap.InfiniteLattice.measurable_wilsonHol_ibd

end Terms

/-! ## Part 8 — the periodic sector

Reducing each coordinate modulo the extent maps the infinite lattice onto `WilsonHypercubic`'s and
commutes with the unit shift (`siteMod_ishift`), so it carries boundary words to boundary words
(`ibd_map_linkMod`). Pulling a finite-lattice configuration back along it reproduces the finite
lattice's holonomies exactly (`wilsonHol_periodic`).

The map goes this way — a finite configuration pulls back to a periodic infinite one — because that
is the direction that is a function: a periodic configuration is an infinite one, while an infinite
configuration has no canonical periodisation. Nothing here maps `IConf G` down to the finite lattice,
and `wilsonHol_periodic` is an equality of holonomies at configurations in the image of
`pullback`. -/

section Periodic

variable {m : ℕ}

/-- One coordinate, reduced modulo the extent: the representative of `k` in `Fin (m + 1)`.

Written as `Int.emod` followed by `Int.toNat` rather than as a cast. `Fin (m + 1)` carries no
`IntCast` instance in this Mathlib, so the ascription `((k : ℤ) : Fin (m + 1))` does not elaborate
and the reduction cannot be written `↑k`. The bound on the value comes from `Int.emod_nonneg` and
`Int.emod_lt_of_pos`; equivariance under a unit step is a separate lemma, `finMod_add_one`, proved
from `Fin.val_add` and `Int.add_emod` rather than from `Int.cast_add`.

DERIVED: `1` is the successor in `m + 1` — the extent is written as a successor so that it is
positive by construction, which is what `Int.emod_lt_of_pos` needs and what makes `Fin (m + 1)`
inhabited. `0` is the lower end of the residue range supplied by `Int.emod_nonneg`, which is what
lets `Int.toNat` be applied without loss. Neither is a lattice parameter; the extent is `m`. -/
def finMod (m : ℕ) (k : ℤ) : Fin (m + 1) :=
  ⟨(k % ((m : ℤ) + 1)).toNat, by
    have hpos : (0 : ℤ) < (m : ℤ) + 1 := by positivity
    have h0 : (0 : ℤ) ≤ k % ((m : ℤ) + 1) := Int.emod_nonneg k hpos.ne'
    have h1 : k % ((m : ℤ) + 1) < (m : ℤ) + 1 := Int.emod_lt_of_pos k hpos
    have h2 : ((k % ((m : ℤ) + 1)).toNat : ℤ) < ((m + 1 : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg h0]; push_cast; exact h1
    exact_mod_cast h2⟩

#print axioms MassGap.InfiniteLattice.finMod

/-- The reduction takes a unit step to a unit step, which is what makes the periodic lattice a
quotient of this one rather than a truncation of it.

DERIVED: the first `1` is the unit step taken in `ℤ` before reducing, the second is the unit step
taken in `Fin (m + 1)` after reducing, and the `1` in `m + 1` is the successor writing the extent.
The same numeral in three types. -/
theorem finMod_add_one (m : ℕ) (k : ℤ) : finMod m (k + 1) = finMod m k + 1 := by
  have hpos : (0 : ℤ) < (m : ℤ) + 1 := by positivity
  have h0 : (0 : ℤ) ≤ k % ((m : ℤ) + 1) := Int.emod_nonneg k hpos.ne'
  have h1 : (0 : ℤ) ≤ (k + 1) % ((m : ℤ) + 1) := Int.emod_nonneg (k + 1) hpos.ne'
  apply Fin.ext
  rw [Fin.val_add, Fin.val_one']
  show ((k + 1) % ((m : ℤ) + 1)).toNat
      = ((k % ((m : ℤ) + 1)).toNat + 1 % (m + 1)) % (m + 1)
  have hcast : (((k + 1) % ((m : ℤ) + 1)).toNat : ℤ)
      = ((((k % ((m : ℤ) + 1)).toNat + 1 % (m + 1)) % (m + 1) : ℕ) : ℤ) := by
    push_cast [Int.toNat_of_nonneg h0, Int.toNat_of_nonneg h1]
    rw [Int.add_emod k 1]
  exact_mod_cast hcast

#print axioms MassGap.InfiniteLattice.finMod_add_one

/-- A site of the infinite lattice, read modulo the extent in every direction.

The extent is written `m + 1` rather than a bare `n` with `[NeZero n]`, because that is the form the
`Fin` arithmetic in `finMod` is stated in. No generality is lost: every positive extent is of this
form.

DERIVED: `4` is the dimension, carried unchanged from `ISite` into `WilsonHypercubic.Site`; `1` is
the successor writing the extent as a positive number, as in `finMod`. Neither is chosen — the extent
itself is the parameter `m`. -/
def siteMod (m : ℕ) (x : ISite) : WilsonHypercubic.Site 4 (m + 1) := fun μ => finMod m (x μ)

#print axioms MassGap.InfiniteLattice.siteMod

/-- The reduction commutes with the unit shift: `siteMod m (ishift μ x) = shift μ (siteMod m x)`.
This is what makes the mirroring of `WilsonHypercubic.shift` by `ishift` exact rather than
typographical. The on-axis case is `finMod_add_one`; the off-axis case is `Function.update` at a
different direction.

DERIVED: `4` is the dimension, the range of the direction `μ`. It is the only numeral in the
statement; the extent enters through the implicit parameter `m`. -/
theorem siteMod_ishift (μ : Fin 4) (x : ISite) :
    siteMod m (ishift μ x) = WilsonHypercubic.shift μ (siteMod m x) := by
  funext ν
  by_cases h : ν = μ
  · subst h
    have e1 : siteMod m (ishift ν x) ν = finMod m (x ν + 1) := by simp [siteMod, ishift]
    have e2 : WilsonHypercubic.shift ν (siteMod m x) ν = finMod m (x ν) + 1 := by
      simp [WilsonHypercubic.shift, siteMod]
    rw [e1, e2, finMod_add_one]
  · simp [siteMod, ishift, WilsonHypercubic.shift, h]

#print axioms MassGap.InfiniteLattice.siteMod_ishift

/-- A link, read modulo the extent. The direction component is carried across untouched, so the
reduction is `siteMod`'s alone.

DERIVED: `4` is the dimension and `1` is the successor writing the extent, both exactly as in
`siteMod`; `1` and `2` are also the product projections `l.1`, the direction, and `l.2`, the
site. -/
def linkMod (m : ℕ) (l : ILink) : WilsonHypercubic.Link 4 (m + 1) := (l.1, siteMod m l.2)

#print axioms MassGap.InfiniteLattice.linkMod

/-- A plaquette, read modulo the extent. The pair of directions spanning the plane is carried across
untouched.

DERIVED: `4` is the dimension and `1` is the successor writing the extent, both exactly as in
`siteMod`; `1` and `2` are also the product projections `q.1`, the spanning pair, and `q.2`, the
base site. -/
def plaqMod (m : ℕ) (q : IPlaq) : WilsonHypercubic.Plaq 4 (m + 1) := (q.1, siteMod m q.2)

#print axioms MassGap.InfiniteLattice.plaqMod

/-- Boundary words map to boundary words: mapping `linkMod` over `ibd q` and keeping the
orientations gives `WilsonHypercubic.bd` of `plaqMod m q`. `ibd` and `WilsonHypercubic.bd` are the
same four letters with the same orientations, and `siteMod_ishift` is what carries one to the other.

DERIVED: `4` is the dimension, supplied to `WilsonHypercubic.bd` as `d`; `1` is the successor
writing the extent, supplied as `n := m + 1`, both as in `siteMod`; `1` and `2` are also the
product projections `lo.1`, the link, and `lo.2`, its orientation. -/
theorem ibd_map_linkMod (q : IPlaq) :
    (ibd q).map (fun lo => (linkMod m lo.1, lo.2))
      = WilsonHypercubic.bd (d := 4) (n := m + 1) (plaqMod m q) := by
  simp [ibd_def, WilsonHypercubic.bd, linkMod, plaqMod, siteMod_ishift]

#print axioms MassGap.InfiniteLattice.ibd_map_linkMod

/-- A configuration on the periodic lattice, pulled back along `linkMod`, has exactly the finite
lattice's plaquette holonomies. Follows from `ibd_map_linkMod` by `List.map_map`. Stated for any
`Group G`, with no measure and no action; the reduction map plays the part a permutation plays in a
reindexing lemma.

DERIVED: the two `4`s are the dimension, once in the type of `W` and once as `d` in the finite
boundary word; the two `1`s are the successor writing the extent `m + 1`, in the same two places. -/
theorem wilsonHol_periodic {G : Type} [Group G] (q : IPlaq)
    (W : WilsonHypercubic.Link 4 (m + 1) → G) :
    wilsonHol ibd q (fun l => W (linkMod m l))
      = wilsonHol (WilsonHypercubic.bd (d := 4) (n := m + 1)) (plaqMod m q) W := by
  unfold wilsonHol
  rw [← ibd_map_linkMod (m := m) q, List.map_map]
  rfl

#print axioms MassGap.InfiniteLattice.wilsonHol_periodic

/-- The pullback of a finite-lattice configuration, as a map of configuration spaces.

DERIVED: `4` is the dimension and `1` is the successor writing the extent, both carried in from
`linkMod`, which is the only place they do any work here. -/
def pullback {G : Type} (m : ℕ) (W : WilsonHypercubic.Link 4 (m + 1) → G) : IConf G :=
  fun l => W (linkMod m l)

#print axioms MassGap.InfiniteLattice.pullback

/-- `pullback` is continuous: each coordinate of the image is a coordinate of the source, evaluated
at `linkMod m l`.

DERIVED: no numeral appears in the statement. -/
theorem continuous_pullback {G : Type} [TopologicalSpace G] :
    Continuous (pullback (G := G) m) :=
  continuous_pi fun l => continuous_apply (linkMod m l)

#print axioms MassGap.InfiniteLattice.continuous_pullback

end Periodic

end MassGap.InfiniteLattice
