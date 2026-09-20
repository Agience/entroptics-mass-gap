import Mathlib
import MassGap.WilsonHypercubic

/-!
# MassGap.InfiniteLattice — the infinite four-dimensional lattice, its configuration space, and the
local algebra

## Why this file exists

`WilsonHypercubic.Site d n = Fin d → Fin n` is finite and periodic, `sysWilson`'s action is a finite
sum over a `Finset` of plaquettes, and `partition` integrates its exponential. Every infinite-volume
statement in the tree is therefore a limit of finite-volume NUMBERS: `InfiniteVolume.lean` extracts a
convergent subsequence of correlations, and `HalfLineTransfer` shows that a genuine half-line of time
levels needs infinitely many of them. There is no state, no measure, and no algebra of observables on
an infinite lattice anywhere for those limits to be limits OF.

This file supplies the first third of one: the index set, the configuration space, the fact that the
configuration space is COMPACT, the measurable structure on it, and the algebra of observables that
read finitely many links.

## Compactness is the load-bearing fact

`IConf G = ILink → G` is a product of copies of a compact group over an infinite index set, so
Tychonoff makes it compact (`compactSpace_IConf`). That single fact is why an infinite-volume limit
exists at all: a sequence of finite-volume states is a sequence of probability measures on ONE fixed
compact space rather than a sequence of measures on a growing family of different spaces, and a
weak-* limit point is then available. Nothing else in this file is as important.

`ILink` is countable (`countable_ILink`). Tychonoff does not need that — `Pi.compactSpace` is
unconditional — but the Borel structure does: `Pi.borelSpace` wants a countable index, and so does
second countability. `borelSpace_IConf` is where countability is actually spent, and it is what makes
"Borel measure on the configuration space" and "product of the Borel structures" the same thing.

## Index conventions

`ibd` mirrors `WilsonHypercubic.bd` (`WilsonHypercubic.lean:66`) letter for letter with `ℤ` in place
of `Fin n`, and `ishift` mirrors `WilsonHypercubic.shift` (`:58`). The finite theory is then a
restriction of this one in the strict sense of `wilsonHol_periodic`: reduce every coordinate mod `n`,
pull a finite-lattice configuration back along that map, and the infinite lattice's plaquette
holonomies ARE the finite lattice's.

## A finite volume is a `Finset ILink`

The choice is made once, here, and everything downstream is stated against it. A volume is a finite
set of LINKS, not of sites: the configuration space is indexed by links, locality is agreement on
links, and `plaqsIn` turns a volume into the finite set of plaquettes whose whole boundary word lies
inside it. A `Finset ISite` would have to name a link convention to mean anything, and naming it here
would make two conventions where one is needed.

## What is NOT here

No measure. No action. No Gibbs state, no DLR equation, no limit. This file is the space those live
on and the observables they are tested against; the state and the dynamics are the other two pieces.
-/

namespace MassGap.InfiniteLattice

open MassGap MassGap.WilsonLattice

/-! ## Part 1 — the lattice

Four dimensions, `ℤ` in each, exactly as in the Clay statement. The types mirror
`WilsonHypercubic.Site`/`Link`/`Plaq` with the periodic coordinate replaced by the integers. -/

/-- Sites of the infinite four-dimensional lattice.

DERIVED: `4` is the number of spacetime directions — the dimension of the Clay statement, the same
`d` that `WilsonHypercubic` is instantiated at for the Clay instance (`bd (d := 4)` in `AreaLaw`).
It is an index range, not an extent: each of the four coordinates runs over all of `ℤ`. -/
abbrev ISite : Type := Fin 4 → ℤ

/-- A link: a direction and the site it is based at.

DERIVED: `4` is the dimension again — the direction index of a link runs over the four spacetime
directions, mirroring `WilsonHypercubic.Link` at `d = 4`. Same constant as in `ISite`. -/
abbrev ILink : Type := Fin 4 × ISite

/-- A plaquette: an ordered pair of directions and a base site.

DERIVED: both `4`s are the dimension, written twice because a plane in `d` dimensions is spanned by
an ordered PAIR of directions — the same reason `WilsonHypercubic.Plaq` carries a pair rather than a
normal. The dimension used twice, not a separate constant. -/
abbrev IPlaq : Type := (Fin 4 × Fin 4) × ISite

/-- A configuration assigns a group element to every link. -/
abbrev IConf (G : Type) : Type := ILink → G

#print axioms MassGap.InfiniteLattice.ISite
#print axioms MassGap.InfiniteLattice.ILink
#print axioms MassGap.InfiniteLattice.IPlaq
#print axioms MassGap.InfiniteLattice.IConf

/-- **The lattice is infinite** — which is the whole point, and the one difference from
`WilsonHypercubic.card_link`'s `d · n^d`.

DERIVED: `0` is a direction INDEX, not a site or a magnitude. The injection sends `k : ℤ` to the
constant site, and `congrFun h 0` evaluates it at one direction to recover `k`; the first of the
four directions is evaluated because some direction must be, and any other would prove the same
injectivity. -/
instance instInfiniteISite : Infinite ISite :=
  Infinite.of_injective (fun k : ℤ => (fun _ => k : ISite)) (fun _ _ h => congrFun h 0)

#print axioms MassGap.InfiniteLattice.instInfiniteISite

/-- There are infinitely many links, so no `Fintype` argument is available anywhere below.

DERIVED: `4` is the dimension, the range of a link's direction index; `0` is a direction index — the
injection embeds the sites as the links pointing in one fixed direction, and the first of the four
is as good as any other, since infinitude of the sites is what is being transported. -/
instance instInfiniteILink : Infinite ILink :=
  Infinite.of_injective (fun x : ISite => ((0 : Fin 4), x)) (fun _ _ h => by simpa using h)

#print axioms MassGap.InfiniteLattice.instInfiniteILink

/-- **The links are countable.** Not needed for compactness — Tychonoff is unconditional — but needed
for the Borel structure on the configuration space to be the product Borel structure, which is what
`borelSpace_IConf` below spends it on. -/
theorem countable_ILink : Countable ILink := inferInstance

#print axioms MassGap.InfiniteLattice.countable_ILink

/-- The sites are countable too. -/
theorem countable_ISite : Countable ISite := inferInstance

#print axioms MassGap.InfiniteLattice.countable_ISite

/-- Equality of links is decidable: `Fin 4` is a `Fintype` and `ℤ` has decidable equality, so the
function type does too. `Finset.filter` and `List.toFinset` below are computable because of this,
rather than by a classical instance.

DERIVED: the definition is `inferInstance` and carries no numeral of its own; the `4` is in this
note, and it is the dimension — the direction index of a link, whose finiteness is what makes the
function type decidable. -/
def decEqILink : DecidableEq ILink := inferInstance

#print axioms MassGap.InfiniteLattice.decEqILink

/-- Equality of plaquettes is decidable, for the same reason. -/
def decEqIPlaq : DecidableEq IPlaq := inferInstance

#print axioms MassGap.InfiniteLattice.decEqIPlaq

/-! ## Part 2 — the plaquette boundary word

`ishift` and `ibd` are `WilsonHypercubic.shift` (`:58`) and `WilsonHypercubic.bd` (`:66`) with `ℤ` in
place of `Fin n`. The word is the same four letters in the same order with the same orientations, so
`WilsonLattice.wilsonHol` reads the same loop. -/

/-- Translate a site one step in direction `μ`. Mirrors `WilsonHypercubic.shift` with no wrap.

DERIVED: `1` is one lattice step — the definition of a neighbouring site, not a length. -/
def ishift (μ : Fin 4) (x : ISite) : ISite :=
  Function.update x μ (x μ + 1)

#print axioms MassGap.InfiniteLattice.ishift

/-- **The plaquette boundary word**: `U_μ(x) · U_ν(x+μ̂) · U_μ(x+ν̂)⁻¹ · U_ν(x)⁻¹`.

The `Bool` is the orientation — `true` traverses the link forwards, `false` inverts it — and
`WilsonLattice.wilsonHol` turns the word into the ordered product. Identical in shape to
`WilsonHypercubic.bd`; only the site type differs. -/
def ibd (q : IPlaq) : List (ILink × Bool) :=
  let μ := q.1.1
  let ν := q.1.2
  let x := q.2
  [((μ, x), true), ((ν, ishift μ x), true),
   ((μ, ishift ν x), false), ((ν, x), false)]

#print axioms MassGap.InfiniteLattice.ibd

/-- The boundary word written out, for rewriting. -/
theorem ibd_def (q : IPlaq) :
    ibd q = [((q.1.1, q.2), true), ((q.1.2, ishift q.1.1 q.2), true),
             ((q.1.1, ishift q.1.2 q.2), false), ((q.1.2, q.2), false)] := rfl

#print axioms MassGap.InfiniteLattice.ibd_def

/-- **Four letters** — a plaquette is a square, and the word is its four sides. -/
theorem ibd_length (q : IPlaq) : (ibd q).length = 4 := rfl

#print axioms MassGap.InfiniteLattice.ibd_length

/-- The links the word names, in order. -/
theorem ibd_links (q : IPlaq) :
    (ibd q).map Prod.fst
      = [(q.1.1, q.2), (q.1.2, ishift q.1.1 q.2),
         (q.1.1, ishift q.1.2 q.2), (q.1.2, q.2)] := rfl

#print axioms MassGap.InfiniteLattice.ibd_links

/-- The orientations: two forwards then two backwards, so the loop closes. -/
theorem ibd_orientations (q : IPlaq) :
    (ibd q).map Prod.snd = [true, true, false, false] := rfl

#print axioms MassGap.InfiniteLattice.ibd_orientations

/-- **The holonomy is the ordered Wilson loop** `U_μ(x) · U_ν(x+μ̂) · U_μ(x+ν̂)⁻¹ · U_ν(x)⁻¹`,
written out so that a reader can check the loop without unfolding `wilsonHol`. -/
theorem wilsonHol_ibd {G : Type} [Group G] (q : IPlaq) (U : IConf G) :
    wilsonHol ibd q U
      = U (q.1.1, q.2) * (U (q.1.2, ishift q.1.1 q.2)
          * ((U (q.1.1, ishift q.1.2 q.2))⁻¹ * (U (q.1.2, q.2))⁻¹)) := by
  simp [wilsonHol, ibd_def]

#print axioms MassGap.InfiniteLattice.wilsonHol_ibd

/-- **A degenerate plane contributes nothing**, exactly as in `WilsonHypercubic.bd_diag_hol_one`:
with `μ = ν` the word retraces itself and the holonomy is the identity. So the plaquette type may
carry all ordered pairs without excluding the diagonal. -/
theorem ibd_diag_hol_one {G : Type} [Group G] (μ : Fin 4) (x : ISite) (U : IConf G) :
    wilsonHol ibd ((μ, μ), x) U = 1 := by
  simp [wilsonHol, ibd_def]

#print axioms MassGap.InfiniteLattice.ibd_diag_hol_one

/-- The links a single plaquette reads, as a finite set. -/
def linksOf (q : IPlaq) : Finset ILink := ((ibd q).map Prod.fst).toFinset

#print axioms MassGap.InfiniteLattice.linksOf

/-- A plaquette reads at most four links. -/
theorem linksOf_card_le (q : IPlaq) : (linksOf q).card ≤ 4 := by
  refine le_trans (List.toFinset_card_le _) ?_
  simp [ibd_def]

#print axioms MassGap.InfiniteLattice.linksOf_card_le

/-- Membership in `linksOf`, in the form the boundary-word lemmas produce. -/
theorem mem_linksOf {q : IPlaq} {l : ILink} : l ∈ linksOf q ↔ l ∈ (ibd q).map Prod.fst :=
  List.mem_toFinset

#print axioms MassGap.InfiniteLattice.mem_linksOf

/-- The base link of a plaquette is one of its own links — the `linksOf` fact `plaqsIn` needs. -/
theorem base_mem_linksOf (q : IPlaq) : (q.1.1, q.2) ∈ linksOf q := by
  simp [linksOf, ibd_def]

#print axioms MassGap.InfiniteLattice.base_mem_linksOf

/-! ## Part 3 — the configuration space is compact

The single most important statement in this module. Everything an infinite-volume limit needs — a
weak-* limit point of finite-volume states, tightness for free, a Riesz representation for a positive
functional on the local algebra — comes from here. -/

section Space

variable {G : Type} [TopologicalSpace G]

/-- **Tychonoff.** A product of compact spaces over ANY index set is compact, so the configuration
space of the infinite lattice is compact. Mathlib's `Pi.compactSpace` fires on
`IConf G = ILink → G` with no countability, no metrizability and no choice of topology beyond the
product topology, which is the instance already on the function type. -/
theorem compactSpace_IConf [CompactSpace G] : CompactSpace (IConf G) := inferInstance

#print axioms MassGap.InfiniteLattice.compactSpace_IConf

/-- Stated on the set, which is the form `IsCompact.bddAbove`, Prokhorov and the Riesz theorem want. -/
theorem isCompact_univ_IConf [CompactSpace G] :
    IsCompact (Set.univ : Set (IConf G)) := isCompact_univ

#print axioms MassGap.InfiniteLattice.isCompact_univ_IConf

/-- The configuration space is Hausdorff when the group is. -/
theorem t2Space_IConf [T2Space G] : T2Space (IConf G) := inferInstance

#print axioms MassGap.InfiniteLattice.t2Space_IConf

/-- **Where countability is spent.** A product over a COUNTABLE index of second-countable spaces is
second countable; over an uncountable index it is not. This is the hypothesis `borelSpace_IConf`
below needs, and it is why `countable_ILink` is proved above. -/
theorem secondCountable_IConf [SecondCountableTopology G] :
    SecondCountableTopology (IConf G) := inferInstance

#print axioms MassGap.InfiniteLattice.secondCountable_IConf

/-- The configuration space is nonempty whenever the group is — so `exists_forall_le` style
arguments on it have something to be applied to. -/
theorem nonempty_IConf {H : Type} [Nonempty H] : Nonempty (IConf H) := inferInstance

#print axioms MassGap.InfiniteLattice.nonempty_IConf

/-- **Every coordinate is continuous.** The evaluation `U ↦ U l` at one link; cylinder functions are
built from these, so this is the continuity every local observable ultimately rests on. -/
theorem continuous_coord (l : ILink) : Continuous (fun U : IConf G => U l) := continuous_apply l

#print axioms MassGap.InfiniteLattice.continuous_coord

/-- **A continuous function on the configuration space is bounded** — a consequence of compactness,
not an extra hypothesis. `LogConvex.localObs` carries boundedness as a separate clause because its
configuration space is not assumed compact; here it comes for free, which is why the local algebra
below asks only for continuity and locality. -/
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

The measurable space on `IConf G` is the product one, and with a countable index and a second
countable group it IS the Borel structure of the product topology. So "measurable" and "Borel" are
the same word here, and a continuous observable is measurable. -/

section Measure

variable {G : Type} [MeasurableSpace G]

/-- **Every coordinate is measurable.** The product `MeasurableSpace.pi` instance, read off. -/
theorem measurable_coord (l : ILink) : Measurable (fun U : IConf G => U l) :=
  measurable_pi_apply l

#print axioms MassGap.InfiniteLattice.measurable_coord

/-- **The product measurable structure is the Borel structure.** Needs the index to be countable
(`countable_ILink`) and the group to be second countable; without either, the product σ-algebra is
strictly smaller than the Borel σ-algebra of the product topology and "Borel measure" would name a
different object from "cylinder measure". -/
theorem borelSpace_IConf [TopologicalSpace G] [SecondCountableTopology G] [BorelSpace G] :
    BorelSpace (IConf G) := inferInstance

#print axioms MassGap.InfiniteLattice.borelSpace_IConf

/-- **So a continuous observable is measurable** — the bridge the other two modules need in order to
integrate a continuous local observable against a measure. -/
theorem measurable_of_continuous [TopologicalSpace G] [SecondCountableTopology G] [BorelSpace G]
    {F : IConf G → ℝ} (hF : Continuous F) : Measurable F := by
  haveI : BorelSpace (IConf G) := borelSpace_IConf
  exact hF.measurable

#print axioms MassGap.InfiniteLattice.measurable_of_continuous

end Measure

/-! ## Part 5 — finite volumes and the local algebra

A finite volume is a `Finset ILink`. An observable is LOCAL in a volume when the volume's links
determine it — the same notion as `ReflectionPositivity.hol_congr_on_support` (`:233`), which says a
plaquette holonomy is determined by the links its own word names, and the third clause of
`LogConvex.localObs` (`:119`), which says an observable is determined by the blocks it reads. The
other two clauses of `localObs` — measurability and boundedness — are not repeated: on a compact
space continuity supplies both (`bounded_of_continuous`, `measurable_of_continuous`). -/

section Local

variable {G : Type}

/-- **Locality**: `F` is determined by the links in `S`. Two configurations that agree on `S` are
given the same value, whatever they do on the infinitely many links outside it. -/
def IsLocalOn (S : Finset ILink) (F : IConf G → ℝ) : Prop :=
  ∀ U V : IConf G, (∀ l ∈ S, U l = V l) → F U = F V

#print axioms MassGap.InfiniteLattice.IsLocalOn

/-- Locality in a bigger volume is a weaker requirement. -/
theorem IsLocalOn.mono {S T : Finset ILink} {F : IConf G → ℝ} (h : S ⊆ T) (hF : IsLocalOn S F) :
    IsLocalOn T F := fun U V hUV => hF U V (fun l hl => hUV l (h hl))

#print axioms MassGap.InfiniteLattice.IsLocalOn.mono

/-- The restriction of a configuration to a volume. -/
def restrict (S : Finset ILink) (U : IConf G) : {l : ILink // l ∈ S} → G := fun l => U l.1

#print axioms MassGap.InfiniteLattice.restrict

/-- Anything that factors through the restriction to `S` is local in `S`. -/
theorem isLocalOn_comp_restrict (S : Finset ILink) (f : ({l : ILink // l ∈ S} → G) → ℝ) :
    IsLocalOn S (fun U => f (restrict S U)) := by
  intro U V h
  have : restrict S U = restrict S V := funext fun l => h l.1 l.2
  simp [this]

#print axioms MassGap.InfiniteLattice.isLocalOn_comp_restrict

section LocalTop

variable [TopologicalSpace G]

/-- The restriction map is continuous — each of its coordinates is a coordinate of `IConf G`. -/
theorem continuous_restrict (S : Finset ILink) : Continuous (restrict (G := G) S) :=
  continuous_pi fun l => continuous_apply l.1

#print axioms MassGap.InfiniteLattice.continuous_restrict

/-- **The observables of a finite volume**: continuous, and determined by the links in `S`. A unital
subalgebra of the real-valued functions on configuration space — closed under `+`, `*` and the real
scalars, containing the constants.

Continuity rather than measurability-plus-a-bound is the right carrier here because the space is
compact: `bounded_of_continuous` and `measurable_of_continuous` recover the other two clauses of
`LogConvex.localObs`, and continuity is what a weak-* limit of states is tested against. -/
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

/-- Membership in the local algebra, unfolded. -/
theorem mem_localAlg {S : Finset ILink} {F : IConf G → ℝ} :
    F ∈ localAlg S ↔ Continuous F ∧ IsLocalOn S F := Iff.rfl

#print axioms MassGap.InfiniteLattice.mem_localAlg

/-- **Every local observable is continuous** — by construction, and it is the clause that makes the
definition the right one: a function of finitely many coordinates need NOT be continuous, so
locality alone would not give a space on which a weak-* limit of states acts. -/
theorem localAlg_continuous {S : Finset ILink} {F : IConf G → ℝ} (hF : F ∈ localAlg S) :
    Continuous F := hF.1

#print axioms MassGap.InfiniteLattice.localAlg_continuous

/-- And every local observable is local. -/
theorem localAlg_isLocalOn {S : Finset ILink} {F : IConf G → ℝ} (hF : F ∈ localAlg S) :
    IsLocalOn S F := hF.2

#print axioms MassGap.InfiniteLattice.localAlg_isLocalOn

/-- **Monotone in the volume**: enlarging the volume can only add observables. This is what makes the
family directed, hence its union an algebra. -/
theorem localAlg_mono {S T : Finset ILink} (h : S ⊆ T) : localAlg (G := G) S ≤ localAlg T := by
  rintro F ⟨hFc, hFl⟩
  exact ⟨hFc, hFl.mono h⟩

#print axioms MassGap.InfiniteLattice.localAlg_mono

/-- On a compact configuration space every local observable is bounded, so the `localObs` clause is
recovered rather than assumed. -/
theorem localAlg_bounded [CompactSpace G] {S : Finset ILink} {F : IConf G → ℝ}
    (hF : F ∈ localAlg S) : ∃ C : ℝ, ∀ U, |F U| ≤ C :=
  bounded_of_continuous hF.1

#print axioms MassGap.InfiniteLattice.localAlg_bounded

/-- And measurable, so it can be integrated against any Borel measure on the space. -/
theorem localAlg_measurable [MeasurableSpace G] [SecondCountableTopology G] [BorelSpace G]
    {S : Finset ILink} {F : IConf G → ℝ} (hF : F ∈ localAlg S) : Measurable F :=
  measurable_of_continuous hF.1

#print axioms MassGap.InfiniteLattice.localAlg_measurable

/-- **The local algebra of the whole lattice**: the observables local in SOME finite volume. The
union of a directed family of subalgebras, and an algebra because two observables can be put in the
union of their volumes. This is the algebra an infinite-volume state is a functional on. -/
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

/-- Membership in the quasi-local algebra, unfolded. -/
theorem mem_quasiLocalAlg {F : IConf G → ℝ} :
    F ∈ quasiLocalAlg ↔ Continuous F ∧ ∃ S : Finset ILink, IsLocalOn S F := Iff.rfl

#print axioms MassGap.InfiniteLattice.mem_quasiLocalAlg

/-- Every finite volume's algebra sits inside it. -/
theorem localAlg_le_quasiLocalAlg (S : Finset ILink) :
    localAlg (G := G) S ≤ quasiLocalAlg := by
  rintro F ⟨hFc, hFl⟩
  exact ⟨hFc, S, hFl⟩

#print axioms MassGap.InfiniteLattice.localAlg_le_quasiLocalAlg

/-- Every coordinate function is a local observable: composing a continuous function on the group
with one link's evaluation gives an observable local in `{l}`. The generating example, and the shape
every cylinder function has. -/
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
plaquettes whose WHOLE boundary word lies in `S`, which is exactly the condition under which the
plaquette's contribution to an action is a function of the volume's links alone. -/

section Plaquettes

/-- **The plaquettes of a volume**: those all of whose boundary links lie in `S`.

Finite by construction: a plaquette all of whose links are in `S` has its base link in `S`, so its
base SITE is one of the finitely many sites `S` mentions, and there are `16` ordered planes.

DERIVED: `4` is the dimension, and the `16` is that dimension twice — an ordered plane is a pair of
directions, so `Fin 4 × Fin 4` has `4 × 4` elements. Neither is a cut: the product is only the
finiteness scaffolding, and `mem_plaqsIn` shows membership is exactly `linksOf q ⊆ S`, with no
dependence on the candidate set. -/
def plaqsIn (S : Finset ILink) : Finset IPlaq :=
  (((Finset.univ : Finset (Fin 4 × Fin 4)) ×ˢ (S.image Prod.snd)).filter
    (fun q => ∀ l ∈ (ibd q).map Prod.fst, l ∈ S))

#print axioms MassGap.InfiniteLattice.plaqsIn

/-- **Membership**: a plaquette is in the volume exactly when the volume contains every link it
reads. The candidate set in the definition is scaffolding for finiteness and nothing else. -/
theorem mem_plaqsIn {S : Finset ILink} {q : IPlaq} : q ∈ plaqsIn S ↔ linksOf q ⊆ S := by
  constructor
  · intro h l hl
    exact (Finset.mem_filter.mp h).2 l (mem_linksOf.mp hl)
  · intro h
    refine Finset.mem_filter.mpr ⟨?_, fun l hl => h (mem_linksOf.mpr hl)⟩
    refine Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr ⟨(q.1.1, q.2), h (base_mem_linksOf q), rfl⟩

#print axioms MassGap.InfiniteLattice.mem_plaqsIn

/-- **Monotone in the volume.** Growing the box can only add plaquettes — the fact an increasing
exhaustion of the lattice by finite volumes needs. -/
theorem plaqsIn_mono {S T : Finset ILink} (h : S ⊆ T) : plaqsIn S ⊆ plaqsIn T := by
  intro q hq
  exact mem_plaqsIn.mpr ((mem_plaqsIn.mp hq).trans h)

#print axioms MassGap.InfiniteLattice.plaqsIn_mono

/-- The same, as `Monotone`. -/
theorem monotone_plaqsIn : Monotone plaqsIn := fun _ _ h => plaqsIn_mono h

#print axioms MassGap.InfiniteLattice.monotone_plaqsIn

/-- Its elements are local: every plaquette of a volume reads only the volume's links. -/
theorem linksOf_subset_of_mem_plaqsIn {S : Finset ILink} {q : IPlaq} (hq : q ∈ plaqsIn S) :
    linksOf q ⊆ S := mem_plaqsIn.mp hq

#print axioms MassGap.InfiniteLattice.linksOf_subset_of_mem_plaqsIn

/-- **Finiteness, stated on the set** rather than inferred from the `Finset`: the plaquettes a finite
volume touches are a finite set of an infinite type. -/
theorem coe_plaqsIn (S : Finset ILink) :
    (plaqsIn S : Set IPlaq) = {q : IPlaq | linksOf q ⊆ S} := by
  ext q
  simpa using mem_plaqsIn

#print axioms MassGap.InfiniteLattice.coe_plaqsIn

theorem finite_plaqs_of_volume (S : Finset ILink) : {q : IPlaq | linksOf q ⊆ S}.Finite := by
  rw [← coe_plaqsIn S]
  exact (plaqsIn S).finite_toSet

#print axioms MassGap.InfiniteLattice.finite_plaqs_of_volume

/-- **At most `16` plaquettes per link**: `16 = 4 · 4` ordered planes through a site, and every
plaquette of `S` bases at a site `S` mentions.

DERIVED: `16` is `Fintype.card (Fin 4 × Fin 4)` — the number of ordered planes in four dimensions,
matching `WilsonHypercubic.card_plaq` at `d = 4`. It is counted, not chosen. -/
theorem plaqsIn_card_le (S : Finset ILink) : (plaqsIn S).card ≤ 16 * S.card := by
  refine le_trans (Finset.card_filter_le _ _) ?_
  have h : (((Finset.univ : Finset (Fin 4 × Fin 4)) ×ˢ (S.image Prod.snd))).card
      = 16 * (S.image Prod.snd).card := by
    simp [Finset.card_product]
  rw [h]
  exact Nat.mul_le_mul le_rfl (Finset.card_image_le)

#print axioms MassGap.InfiniteLattice.plaqsIn_card_le

/-- Every plaquette belongs to the volume of its own links, so the volumes exhaust the plaquettes. -/
theorem mem_plaqsIn_linksOf (q : IPlaq) : q ∈ plaqsIn (linksOf q) :=
  mem_plaqsIn.mpr (Finset.Subset.refl _)

#print axioms MassGap.InfiniteLattice.mem_plaqsIn_linksOf

end Plaquettes

/-! ## Part 7 — plaquette terms are local observables

`ReflectionPositivity.hol_congr_on_support` (`:233`) proved, for the finite lattice and `SU N`, that a
plaquette's holonomy reads only the links its own word names. The same proof works verbatim here for
any group, and it is what makes a plaquette term of a finite-volume action an element of that
volume's local algebra. -/

section Terms

variable {G : Type} [Group G]

/-- **A plaquette's holonomy reads only the links in its own boundary word** — the infinite-lattice,
any-group form of `ReflectionPositivity.hol_congr_on_support`. -/
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

/-- So a plaquette term is local in any volume containing the plaquette. -/
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
the shape of a finite-volume action, so the action of a volume is an observable of that volume. -/
theorem isLocalOn_plaqSum (S : Finset ILink) (T : Finset IPlaq) (hT : ∀ q ∈ T, q ∈ plaqsIn S)
    (φ : G → ℝ) :
    IsLocalOn S (fun U : IConf G => ∑ q ∈ T, φ (wilsonHol ibd q U)) := by
  intro U V h
  exact Finset.sum_congr rfl fun q hq => isLocalOn_plaqTerm (hT q hq) φ U V h

#print axioms MassGap.InfiniteLattice.isLocalOn_plaqSum

section TermsTop

variable [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G]

/-- The ordered product of link-dependent step factors is continuous — the continuity mirror of
`WilsonLattice.measurable_stepListProd`, by the same list induction. -/
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

/-- **The plaquette holonomy is continuous** in the configuration. -/
theorem continuous_wilsonHol_ibd (q : IPlaq) :
    Continuous (wilsonHol (G := G) ibd q) := continuous_stepListProd (ibd q)

#print axioms MassGap.InfiniteLattice.continuous_wilsonHol_ibd

/-- **A plaquette term is an observable of any volume containing its plaquette** — continuous and
local, so a member of `localAlg`. This is the statement a finite-volume action is assembled from. -/
theorem plaqTerm_mem_localAlg {S : Finset ILink} {q : IPlaq} (hq : q ∈ plaqsIn S) {φ : G → ℝ}
    (hφ : Continuous φ) : (fun U : IConf G => φ (wilsonHol ibd q U)) ∈ localAlg S :=
  ⟨hφ.comp (continuous_wilsonHol_ibd q), isLocalOn_plaqTerm hq φ⟩

#print axioms MassGap.InfiniteLattice.plaqTerm_mem_localAlg

/-- And so is any finite sum of them inside the volume: the finite-volume action of a volume is an
element of that volume's local algebra. -/
theorem plaqSum_mem_localAlg (S : Finset ILink) (T : Finset IPlaq) (hT : ∀ q ∈ T, q ∈ plaqsIn S)
    {φ : G → ℝ} (hφ : Continuous φ) :
    (fun U : IConf G => ∑ q ∈ T, φ (wilsonHol ibd q U)) ∈ localAlg S :=
  ⟨continuous_finsetSum T fun q _ => hφ.comp (continuous_wilsonHol_ibd q),
    isLocalOn_plaqSum S T hT φ⟩

#print axioms MassGap.InfiniteLattice.plaqSum_mem_localAlg

end TermsTop

/-- The plaquette holonomy is measurable in the configuration — `WilsonLattice.measurable_wilsonHol`
at this boundary word. -/
theorem measurable_wilsonHol_ibd [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (q : IPlaq) : Measurable (wilsonHol (G := G) ibd q) :=
  measurable_wilsonHol ibd q

#print axioms MassGap.InfiniteLattice.measurable_wilsonHol_ibd

end Terms

/-! ## Part 8 — the finite periodic lattice is a restriction of this one

Reducing each coordinate mod the extent maps the infinite lattice onto `WilsonHypercubic`'s one and
commutes with the unit shift, so it carries boundary words to boundary words. Pulling a finite-volume
configuration back along it therefore reproduces the finite lattice's holonomies exactly: the finite
theory is the periodic sector of this one, not a different object with a similar name.

The map goes THIS way — finite configurations pull back to (periodic) infinite ones — because it is
the direction that is a function: a periodic configuration is an infinite one, while an infinite
configuration has no canonical periodisation (restricting to a fundamental domain would have to
choose one, and the choice would not commute with `ibd` at the boundary). That is the whole cost:
`wilsonHol_periodic` is an equality of holonomies on the periodic sector, and nothing here claims a
map from `IConf G` down to the finite lattice. -/

section Periodic

variable {m : ℕ}

/-- **One coordinate, reduced modulo the extent**: the representative of `k` in `[0, m]`.

Built by hand rather than as a cast, and that is the whole cost of this part. `Fin (m + 1)` carries
no `IntCast` in this Mathlib — the ascription `((k : ℤ) : Fin (m + 1))` does not elaborate — so
reduction cannot be written as `↑k` and its `+1`-equivariance cannot be `Int.cast_add`. It is
`Int.emod` followed by `Int.toNat`, with the bound proved from `Int.emod_nonneg` and
`Int.emod_lt_of_pos`, and the equivariance proved from `Fin.val_add` and `Int.add_emod`.

DERIVED: both digits are modulus bookkeeping, not lattice parameters. `1` is the successor in
`m + 1`: the extent is written as a successor so that it is positive by construction, which is what
`Int.emod_lt_of_pos` needs and what makes `Fin (m + 1)` inhabited. `0` is the lower end of the
residue range, supplied by `Int.emod_nonneg`, which is what lets `Int.toNat` be applied without
loss. Neither says anything about the lattice; the extent itself is the parameter `m`. -/
def finMod (m : ℕ) (k : ℤ) : Fin (m + 1) :=
  ⟨(k % ((m : ℤ) + 1)).toNat, by
    have hpos : (0 : ℤ) < (m : ℤ) + 1 := by positivity
    have h0 : (0 : ℤ) ≤ k % ((m : ℤ) + 1) := Int.emod_nonneg k hpos.ne'
    have h1 : k % ((m : ℤ) + 1) < (m : ℤ) + 1 := Int.emod_lt_of_pos k hpos
    have h2 : ((k % ((m : ℤ) + 1)).toNat : ℤ) < ((m + 1 : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg h0]; push_cast; exact h1
    exact_mod_cast h2⟩

#print axioms MassGap.InfiniteLattice.finMod

/-- **The reduction takes a unit step to a unit step** — periodically, which is exactly what makes
the periodic lattice a quotient of this one rather than a truncation of it. -/
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

The extent is written `m + 1` rather than a bare `n` with `[NeZero n]` because that is the form the
`Fin` arithmetic above is stated in, and no generality is lost: every positive extent is of this
form, and `InfiniteVolume` already indexes the Clay lattice by `N + 1` for the same reason.

DERIVED: `4` is the dimension, carried unchanged from `ISite` into `WilsonHypercubic.Site`; `1` is
the successor in `m + 1`, which is how a positive extent is written here, as the paragraph above
says. Neither is chosen — the dimension is the Clay problem's and the extent is the parameter `m`. -/
def siteMod (m : ℕ) (x : ISite) : WilsonHypercubic.Site 4 (m + 1) := fun μ => finMod m (x μ)

#print axioms MassGap.InfiniteLattice.siteMod

/-- **The reduction commutes with the unit shift** — `ishift` mirrors `WilsonHypercubic.shift`, and
this is the proof that the mirroring is exact rather than typographical. -/
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

/-- A link, read modulo the extent.

DERIVED: `4` is the dimension and `1` is the successor in `m + 1`, both exactly as in `siteMod`;
the direction component is carried across untouched, so the reduction is `siteMod`'s alone. -/
def linkMod (m : ℕ) (l : ILink) : WilsonHypercubic.Link 4 (m + 1) := (l.1, siteMod m l.2)

#print axioms MassGap.InfiniteLattice.linkMod

/-- A plaquette, read modulo the extent.

DERIVED: `4` is the dimension and `1` is the successor in `m + 1`, both exactly as in `siteMod`;
the pair of directions spanning the plane is carried across untouched. -/
def plaqMod (m : ℕ) (q : IPlaq) : WilsonHypercubic.Plaq 4 (m + 1) := (q.1, siteMod m q.2)

#print axioms MassGap.InfiniteLattice.plaqMod

/-- **Boundary words map to boundary words.** `ibd` and `WilsonHypercubic.bd` are the same four
letters with the same orientations, and the reduction carries one to the other. -/
theorem ibd_map_linkMod (q : IPlaq) :
    (ibd q).map (fun lo => (linkMod m lo.1, lo.2))
      = WilsonHypercubic.bd (d := 4) (n := m + 1) (plaqMod m q) := by
  simp [ibd_def, WilsonHypercubic.bd, linkMod, plaqMod, siteMod_ishift]

#print axioms MassGap.InfiniteLattice.ibd_map_linkMod

/-- **The finite theory is the periodic sector of this one.** A configuration on the periodic
`(m+1)^4` lattice, pulled back to the infinite lattice, has exactly the finite lattice's plaquette
holonomies — the `wilsonSymmetry`-style reindexing, with the reduction map in place of a
permutation. -/
theorem wilsonHol_periodic {G : Type} [Group G] (q : IPlaq)
    (W : WilsonHypercubic.Link 4 (m + 1) → G) :
    wilsonHol ibd q (fun l => W (linkMod m l))
      = wilsonHol (WilsonHypercubic.bd (d := 4) (n := m + 1)) (plaqMod m q) W := by
  unfold wilsonHol
  rw [← ibd_map_linkMod (m := m) q, List.map_map]
  rfl

#print axioms MassGap.InfiniteLattice.wilsonHol_periodic

/-- The pullback of a finite-lattice configuration, as a map of configuration spaces.

DERIVED: `4` is the dimension and `1` is the successor in `m + 1`, both carried in from `linkMod`,
which is the only place the numerals do any work here. -/
def pullback {G : Type} (m : ℕ) (W : WilsonHypercubic.Link 4 (m + 1) → G) : IConf G :=
  fun l => W (linkMod m l)

#print axioms MassGap.InfiniteLattice.pullback

/-- It is continuous, so the periodic sector is a compact subset of the configuration space. -/
theorem continuous_pullback {G : Type} [TopologicalSpace G] :
    Continuous (pullback (G := G) m) :=
  continuous_pi fun l => continuous_apply (linkMod m l)

#print axioms MassGap.InfiniteLattice.continuous_pullback

end Periodic

end MassGap.InfiniteLattice
