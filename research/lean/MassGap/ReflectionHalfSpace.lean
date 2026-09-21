import Mathlib
import MassGap.HalfSpaceAlgebra
import MassGap.ReflectionShift
import MassGap.WilsonTransferReduction
import MassGap.CrossingIntegration
import MassGap.ActionSplit
import MassGap.GibbsSpec

/-!
# MassGap.ReflectionHalfSpace — which reflection pairs with which half-space

## ⛔ The pairing was wrong

`HalfSpaceAlgebra.posHalf τ p = {l | p ≤ l.2 τ}` takes `p` as the **plane**.
`LatticeReflection.ireflSite τ c x` sends `x_τ` to `c − x_τ`, so `c` is the **reflection constant**
and the plane it fixes is at `c/2` — its own docstring says so.

So the reflection about `c` carries `{x_τ ≥ p}` into `{x_τ ≤ c − p}`, and that is the COMPLEMENTARY
half only when

    c = 2p.

Every statement of the form `ReflPositiveOn (latticeReflection τ c) (halfSpaceAlg τ c)` therefore
asks for positivity of a pairing that is **not the reflection pairing** unless `c = 0`: at `c ≠ 2p`
the map is a mirror composed with a translation, `F` and `θF` sit in two half-spaces that are not
mirror images about a common plane, and Osterwalder–Schrader positivity has no reason to hold of it.

`reflection_exchanges_halves` is the correct pairing, and `image_half_is_c_sub_p` is why no other
one works.

## What this changes

The open obligation B3 is

    ReflPositiveOn (latticeReflection τ (2*p)) (halfSpaceAlg τ p) ν

and not the `c`-with-`c` form. **This does not make it easier** — it makes it the right statement.
An attempt against the old form would have been trying to prove something false.

## ⚠ And the parity is now visible

`c = 2p` is EVEN, so the pairing `image_half_is_c_sub_p` describes is the even reflection constant —
matching `ReflectStrong`, which records that the even constant (site reflection) and the odd one
(link reflection) are different problems, the odd one needing `0 ≤ β` with
`CharacterExpansion.NegControl.su3_kernel_nonneg_iff` refuting it at `β < 0`.

**⛔ BUT `halfSpaceAlg τ p` PAIRS WITH THE ODD CONSTANT TOO**, and
`reflPositive_of_tendsto_halfSpaceAlg_odd` proves it does — reflection positivity at
`latticeReflection τ (2p-1)` on that same algebra.

What settles the pairing is CONTAINMENT, not equality, and no lemma here states an equality in either
case. `reflection_exchanges_halves` is a `⊆`: at `c = 2p` the image of `posHalf τ p` lands in
`negHalf τ p`, PROPERLY — a `τ`-link reflects about `c - 1`, so it lands at `≤ p - 1` and the
`τ`-link based at `p` is never hit. At `c = 2p-1` the image lands in `{x_τ ≤ p-1}`, again properly,
the `τ` part reaching only `≤ p - 2`. `image_half_is_c_sub_p` is stated for a NON-`τ` link alone, so it
describes one part of the image and not the whole of it.

**WHAT DISTINGUISHES THE TWO** is that the odd image is DISJOINT from `posHalf τ p`, where the even
image meets it at `x_τ = p`. So the plane sitting at a half-integer is no obstruction: the algebra is
indexed by the integer `p` and the reflection by the constant, and the two indices need not agree.
-/

namespace MassGap.ReflectionHalfSpace

open MassGap.InfiniteLattice MassGap.LatticeReflection MassGap.HalfSpaceAlgebra

/-! ## 1. The negative half -/

/-- **THE HALF-SPACE ON THE OTHER SIDE OF THE PLANE `p`.** A link counts as below the plane when its
base is, which for a `τ`-link spanning `[x_τ, x_τ+1]` is the end nearer the plane.

DERIVED: `4` is the spacetime dimension; `p` is the caller's plane. -/
def negHalf (τ : Fin 4) (p : ℤ) : Set ILink := {l | l.2 τ ≤ p}

/-! ## 2. ⭐ The correct pairing -/

/-- **⭐ THE REFLECTION AT CONSTANT `2p` EXCHANGES THE HALVES AT PLANE `p`.**

Both cases of the direction split land below the plane: a `τ`-link reflects about `2p − 1` and lands
at `2p − 1 − x_τ ≤ p − 1`; any other link reflects about `2p` and lands at `2p − x_τ ≤ p`.

This is the geometric content Osterwalder–Schrader positivity is stated against: `θ` must carry the
positive half-space algebra into the negative one.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`, forced by `ireflSite`'s own
parametrisation; the `1` is `ireflLink`'s link length; `4` is the dimension. -/
theorem reflection_exchanges_halves (τ : Fin 4) (p : ℤ) {l : ILink} (hl : l ∈ posHalf τ p) :
    ireflLink τ (2 * p) l ∈ negHalf τ p := by
  have hp : p ≤ l.2 τ := hl
  show (ireflLink τ (2 * p) l).2 τ ≤ p
  by_cases h : l.1 = τ
  · simp only [ireflLink, if_pos h, ireflSite_axis]
    omega
  · simp only [ireflLink, if_neg h, ireflSite_axis]
    omega

#print axioms reflection_exchanges_halves

/-- **⛔ AND NO OTHER CONSTANT DOES.** The reflection at `c` carries the plane-`p` half-space into
`{x_τ ≤ c − p}`, exactly. So it is the complementary half iff `c − p = p`.

Stated on a non-`τ` link, where the base shift does not enter and the image is exact rather than an
inequality — which is what makes this a characterisation and not a bound.

DERIVED: `4` is the dimension; `c` and `p` are the caller's. -/
theorem image_half_is_c_sub_p (τ : Fin 4) (c : ℤ) {l : ILink} (h : l.1 ≠ τ) :
    (ireflLink τ c l).2 τ = c - l.2 τ := by
  simp only [ireflLink, if_neg h, ireflSite_axis]

#print axioms image_half_is_c_sub_p

/-- **⛔ THE MISMATCHED PAIRING PUTS THE IMAGE IN THE WRONG PLACE.** At `c = p` with `p < 0`, a link
of the plane-`p` half-space reflects to `p − x_τ`, which is at most `p − p = 0` and is **still above
the plane**, so `θ` does not leave the positive half at all.

The negative control for `reflection_exchanges_halves`: pairing `latticeReflection τ c` with
`halfSpaceAlg τ c` is not a weaker statement, it is a different and wrong one.

CHOSEN: `p = -1` and the base site at `x_τ = -1` are the simplest witness with `p < 0`; the direction
`μ ≠ τ` avoids the base shift. Neither carries another role. DERIVED: `4` is the dimension. -/
theorem mismatched_pairing_stays_positive {τ μ : Fin 4} (hμ : μ ≠ τ) :
    (ireflLink τ (-1) (μ, fun _ => (-1 : ℤ))).2 τ ∈ {x : ℤ | (-1 : ℤ) ≤ x} := by
  have h := image_half_is_c_sub_p τ (-1) (l := (μ, fun _ => (-1 : ℤ))) hμ
  show (-1 : ℤ) ≤ (ireflLink τ (-1) (μ, fun _ => (-1 : ℤ))).2 τ
  rw [h]
  norm_num

#print axioms mismatched_pairing_stays_positive

/-! ## ⭐ 3. The reflection as a permutation, and its fixed set -/

/-- **THE REFLECTION, AS A PERMUTATION OF THE LINKS.** `ActionSplit.pairing_nonneg_of_shared_block`
consumes `θ : Equiv.Perm ι`, so the involution has to be packaged.

DERIVED: no numeral of its own; `c` is the caller's reflection constant. -/
def ireflPerm (τ : Fin 4) (c : ℤ) : Equiv.Perm ILink :=
  (MassGap.LatticeReflection.ireflLink_involutive τ c).toPerm _

@[simp] theorem ireflPerm_apply (τ : Fin 4) (c : ℤ) (l : ILink) :
    ireflPerm τ c l = MassGap.LatticeReflection.ireflLink τ c l := rfl

#print axioms ireflPerm

/-- **⛔ NO `τ`-LINK IS FIXED AT AN EVEN CONSTANT.** A `τ`-link reflects about `2p - 1`, so being fixed
would need `2p - 1 - x_τ = x_τ`, i.e. `2x_τ = 2p - 1` — odd equals even, impossible over `ℤ`.

This is what makes the shared block clean: the plane carries no `τ`-link, so the time-direction links
split without remainder into the two halves.

DERIVED: the `2` is the plane-to-constant conversion and the `1` is `ireflLink`'s link length; `4` is
the dimension. -/
theorem no_tau_link_fixed (τ : Fin 4) (p : ℤ) {l : ILink} (hτ : l.1 = τ) :
    MassGap.LatticeReflection.ireflLink τ (2 * p) l ≠ l := by
  intro h
  have hax : (MassGap.LatticeReflection.ireflLink τ (2 * p) l).2 τ = l.2 τ := by rw [h]
  simp only [MassGap.LatticeReflection.ireflLink, if_pos hτ,
    MassGap.LatticeReflection.ireflSite_axis] at hax
  omega

#print axioms no_tau_link_fixed

/-- **AND A NON-`τ` LINK IS FIXED EXACTLY ON THE PLANE.** It reflects about `2p`, so `2p - x_τ = x_τ`
iff `x_τ = p`.

With `no_tau_link_fixed` this determines the shared block `R` of the Osterwalder–Seiler split: the
non-`τ` links whose base sits on the plane, and nothing else.

DERIVED: the `2` is the plane-to-constant conversion; `4` is the dimension. -/
theorem nonTau_fixed_iff (τ : Fin 4) (p : ℤ) {l : ILink} (hτ : l.1 ≠ τ) :
    MassGap.LatticeReflection.ireflLink τ (2 * p) l = l ↔ l.2 τ = p := by
  constructor
  · intro h
    have hax : (MassGap.LatticeReflection.ireflLink τ (2 * p) l).2 τ = l.2 τ := by rw [h]
    simp only [MassGap.LatticeReflection.ireflLink, if_neg hτ,
      MassGap.LatticeReflection.ireflSite_axis] at hax
    omega
  · intro h
    have : MassGap.LatticeReflection.ireflSite τ (2 * p) l.2 = l.2 := by
      funext j
      by_cases hj : j = τ
      · subst hj
        rw [MassGap.LatticeReflection.ireflSite_axis, h]
        omega
      · simp [MassGap.LatticeReflection.ireflSite, hj]
    simp only [MassGap.LatticeReflection.ireflLink, if_neg hτ, this]

#print axioms nonTau_fixed_iff

/-! ## ⭐ 3b. The dagger, and the reflection AS A TWIST -/

section Twist

variable {G : Type} [Group G]

/-- **THE COORDINATE TWIST OF THE REFLECTION** on `ℤ⁴` — invert on `τ`-links, leave the rest alone.
The infinite-lattice counterpart of `ActionSplit.axisDagger`.

DERIVED: no numeral of its own; `τ` is the caller's reflected direction. -/
def ilinkDagger (τ : Fin 4) : ILink → G → G :=
  fun l u => if l.1 = τ then u⁻¹ else u

/-- **⭐ THE `ℤ⁴` REFLECTION IS A TWIST — DEFINITIONALLY**, exactly as
`ActionSplit.reflConf_eq_twist` says of the finite lattice.

`ActionSplit.twist e σ U i = σ i (U (e i))`, and `LatticeReflection.ireflConf` moves the base by
`ireflLink` and inverts precisely on `τ`-links. So `ActionSplit`'s machinery — including
`pairing_nonneg_of_shared_block`, the Osterwalder–Seiler split — is stated about this object and not
merely about an analogue of it.

**⚠ The shape matching is not the theorem.** What `pairing_nonneg_of_shared_block` still needs here
is the factorisation of the Wilson weight (`hO`, `hW`), which nothing supplies.

DERIVED: no numeral of its own. -/
theorem ireflConf_eq_twist [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]
    (τ : Fin 4) (c : ℤ) (U : MassGap.InfiniteLattice.IConf G) :
    MassGap.LatticeReflection.ireflConf τ c U
      = MassGap.ActionSplit.twist (ireflPerm τ c) (ilinkDagger (G := G) τ) U := rfl

#print axioms ireflConf_eq_twist

/-- **AND THE DAGGER IS THE IDENTITY OFF THE `τ`-LINKS**, which is `hσR`: by `no_tau_link_fixed` the
shared block carries no `τ`-link, so the twist acts trivially on it.

DERIVED: no numeral of its own. -/
theorem ilinkDagger_eq_self_of_ne (τ : Fin 4) {l : ILink} (h : l.1 ≠ τ) (u : G) :
    ilinkDagger τ l u = u := by
  simp [ilinkDagger, h]

#print axioms ilinkDagger
#print axioms ilinkDagger_eq_self_of_ne

end Twist

section DaggerMeasure

open MeasureTheory MassGap.CompactGauge

/-- **⭐ THE DAGGER PRESERVES HAAR** — `ActionSplit`'s `hσ`.

On a `τ`-link the twist is group inversion, elsewhere the identity, and Haar on a compact group is
inversion-invariant. This is `ActionSplit.axisDagger_measurePreserving`'s argument verbatim; that
proof is `Measure.measurePreserving_inv` and knows nothing about which lattice the link came from.

DERIVED: no numeral of its own; `4` is the dimension carried by `ILink`. -/
theorem ilinkDagger_measurePreserving {N : ℕ} (τ : Fin 4) (l : ILink) :
    MeasurePreserving (ilinkDagger (G := MassGap.SUN.SU N) τ l)
      (probHaar (MassGap.SUN.SU N)) (probHaar (MassGap.SUN.SU N)) := by
  by_cases h : l.1 = τ
  · have hf : ilinkDagger (G := MassGap.SUN.SU N) τ l = fun u => u⁻¹ := by
      funext u; simp [ilinkDagger, h]
    rw [hf]
    exact Measure.measurePreserving_inv (probHaar (MassGap.SUN.SU N))
  · have hf : ilinkDagger (G := MassGap.SUN.SU N) τ l = id := by
      funext u; simp [ilinkDagger, h]
    rw [hf]
    exact MeasurePreserving.id (probHaar (MassGap.SUN.SU N))

#print axioms ilinkDagger_measurePreserving

end DaggerMeasure

/-! ## ⭐ 3c. The blocks `ActionSplit.pairing_nonneg_of_local` consumes -/

section Blocks

open MassGap.LatticeReflection

variable (τ : Fin 4) (p : ℤ) (Λ : Finset ILink)

/-- **THE POSITIVE HALF OF THE BOX** — the links the reflection moves DOWN in the `τ` coordinate.

Classifying by the reflection's own action rather than by a hand-written inequality is what makes the
three blocks disjoint by trichotomy, with no case split on the link's direction.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`; `4` is the dimension. -/
def iblkS : Finset ILink :=
  Λ.filter (fun l => (ireflLink τ (2 * p) l).2 τ < l.2 τ)

/-- **THE NEGATIVE HALF** — moved UP.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`, as in `iblkS`; `4` is the dimension. -/
def iblkT : Finset ILink :=
  Λ.filter (fun l => l.2 τ < (ireflLink τ (2 * p) l).2 τ)

/-- **THE SHARED BLOCK** — not moved in the `τ` coordinate.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`, as in `iblkS`; `4` is the dimension. -/
def iblkR : Finset ILink :=
  Λ.filter (fun l => (ireflLink τ (2 * p) l).2 τ = l.2 τ)

#print axioms iblkS

/-- The three blocks are pairwise disjoint, by trichotomy on `ℤ`. -/
theorem iblkS_disjoint_iblkT : Disjoint (iblkS τ p Λ) (iblkT τ p Λ) := by
  refine Finset.disjoint_left.2 fun l hS hT => ?_
  simp only [iblkS, iblkT, Finset.mem_filter] at hS hT
  omega

theorem iblkS_disjoint_iblkR : Disjoint (iblkS τ p Λ) (iblkR τ p Λ) := by
  refine Finset.disjoint_left.2 fun l hS hR => ?_
  simp only [iblkS, iblkR, Finset.mem_filter] at hS hR
  omega

theorem iblkT_disjoint_iblkR : Disjoint (iblkT τ p Λ) (iblkR τ p Λ) := by
  refine Finset.disjoint_left.2 fun l hT hR => ?_
  simp only [iblkT, iblkR, Finset.mem_filter] at hT hR
  omega

#print axioms iblkS_disjoint_iblkT

/-- **⭐ THE REFLECTION FIXES THE SHARED BLOCK POINTWISE** — this is `ActionSplit`'s `hθR`.

The `τ`-link case is VACUOUS: a fixed `τ`-coordinate would need `2x_τ = 2p - 1`. The non-`τ` case is
`nonTau_fixed_iff`. So classifying by the `τ`-coordinate alone already forces the whole link fixed.

DERIVED: the `2` is the plane-to-constant conversion; `4` is the dimension. -/
theorem irefl_eq_self_of_mem_iblkR {l : ILink} (hl : l ∈ iblkR τ p Λ) :
    ireflLink τ (2 * p) l = l := by
  simp only [iblkR, Finset.mem_filter] at hl
  by_cases hτ : l.1 = τ
  · exfalso
    have := hl.2
    simp only [ireflLink, if_pos hτ, ireflSite_axis] at this
    omega
  · refine (nonTau_fixed_iff τ p hτ).2 ?_
    have := hl.2
    simp only [ireflLink, if_neg hτ, ireflSite_axis] at this
    omega

#print axioms irefl_eq_self_of_mem_iblkR

/-- **⭐ AND IT CARRIES THE POSITIVE HALF INTO THE NEGATIVE ONE** — `ActionSplit`'s `hθST`, given a box
stable under the reflection.

The inequality flips because the reflection is an involution, so the image's image is the original.

DERIVED: the `2` is the plane-to-constant conversion; `4` is the dimension. -/
theorem irefl_mem_iblkT_of_mem_iblkS
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ) {l : ILink} (hl : l ∈ iblkS τ p Λ) :
    ireflLink τ (2 * p) l ∈ iblkT τ p Λ := by
  simp only [iblkS, Finset.mem_filter] at hl
  simp only [iblkT, Finset.mem_filter]
  refine ⟨hΛ l hl.1, ?_⟩
  rw [ireflLink_involutive τ (2 * p) l]
  exact hl.2

#print axioms irefl_mem_iblkT_of_mem_iblkS

end Blocks

/-! ## ⭐ 3d. Transport to the box — the index `ActionSplit` actually takes -/

section Box

open MassGap.LatticeReflection

variable {τ : Fin 4} {p : ℤ} {Λ : Finset ILink}

/-- **THE REFLECTION, AS A MAP OF THE BOX.** `ActionSplit.cvol` carries `[Fintype ι]`, so the index
must be finite: the instantiation runs at the box as a subtype and not at `ILink`, which is infinite.

A reflection-STABLE box carries the reflection to itself, which is the hypothesis this takes.

DERIVED: `c` is the caller's reflection constant, no longer pinned to an even `2p`; `4` is the
dimension. -/
def ireflBox {c : ℤ} (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) : ↥Λ → ↥Λ :=
  fun l => ⟨ireflLink τ c l.1, hΛ l.1 l.2⟩

theorem ireflBox_involutive {c : ℤ} (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) :
    Function.Involutive (ireflBox (τ := τ) (c := c) hΛ) := by
  intro l
  refine Subtype.ext ?_
  simpa [ireflBox] using ireflLink_involutive τ c l.1

/-- **AND SO IT IS A PERMUTATION OF THE BOX** — the `θ` at the index `ActionSplit` takes.

DERIVED: no numeral of its own. -/
def ireflBoxPerm {c : ℤ} (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) : Equiv.Perm ↥Λ :=
  (ireflBox_involutive hΛ).toPerm _

@[simp] theorem ireflBoxPerm_coe {c : ℤ} (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) (l : ↥Λ) :
    ((ireflBoxPerm hΛ l : ↥Λ) : ILink) = ireflLink τ c l.1 := rfl

#print axioms ireflBoxPerm

/-- **A BOX CLOSED UNDER THE REFLECTION, BY CONSTRUCTION.** Union a finite set of links with its
reflected image.

Every lemma of the odd chain carries `hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ`, and until now the only way
to produce one was to check it link by link. This produces it for ANY starting set, so a witness box
can be specified by the plaquettes it must contain rather than by the links it happens to have.

DERIVED: no numeral of its own; `c` is the caller's reflection constant and `4` is the dimension. -/
def reflClosure (τ : Fin 4) (c : ℤ) (Λ : Finset ILink) : Finset ILink :=
  Λ ∪ Λ.image (ireflLink τ c)

#print axioms reflClosure

theorem subset_reflClosure (τ : Fin 4) (c : ℤ) (Λ : Finset ILink) : Λ ⊆ reflClosure τ c Λ :=
  Finset.subset_union_left

#print axioms subset_reflClosure

/-- **AND IT IS CLOSED.** A link of `Λ` reflects into the image; a link of the image reflects back
into `Λ`, because `ireflLink` is an involution. No case split on direction and no arithmetic.

DERIVED: no numeral of its own; `c` is the caller's reflection constant and `4` is the dimension. -/
theorem reflClosure_closed (τ : Fin 4) (c : ℤ) (Λ : Finset ILink) :
    ∀ l ∈ reflClosure τ c Λ, ireflLink τ c l ∈ reflClosure τ c Λ := by
  intro l hl
  rcases Finset.mem_union.mp hl with h | h
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
  · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp h
    refine Finset.mem_union_left _ ?_
    rw [ireflLink_involutive τ c m]
    exact hm

#print axioms reflClosure_closed

/-- The three blocks, at the box index. Same classification as `iblkS`/`iblkT`/`iblkR` — the
reflection moves a link's `τ` coordinate DOWN, UP, or not at all.

DERIVED: the `2` is the plane-to-constant conversion; `4` is the dimension. -/
def boxS (τ : Fin 4) (p : ℤ) (Λ : Finset ILink) : Finset ↥Λ :=
  Finset.univ.filter (fun l : ↥Λ => (ireflLink τ (2 * p) l.1).2 τ < l.1.2 τ)

/-- The negative half at the box index.

DERIVED: the `2` is the plane-to-constant conversion; `4` is the dimension. -/
def boxT (τ : Fin 4) (p : ℤ) (Λ : Finset ILink) : Finset ↥Λ :=
  Finset.univ.filter (fun l : ↥Λ => l.1.2 τ < (ireflLink τ (2 * p) l.1).2 τ)

/-- The shared block at the box index.

DERIVED: the `2` is the plane-to-constant conversion; `4` is the dimension. -/
def boxR (τ : Fin 4) (p : ℤ) (Λ : Finset ILink) : Finset ↥Λ :=
  Finset.univ.filter (fun l : ↥Λ => (ireflLink τ (2 * p) l.1).2 τ = l.1.2 τ)

theorem boxS_disjoint_boxT : Disjoint (boxS τ p Λ) (boxT τ p Λ) := by
  refine Finset.disjoint_left.2 fun l hS hT => ?_
  simp only [boxS, boxT, Finset.mem_filter] at hS hT
  omega

theorem boxS_disjoint_boxR : Disjoint (boxS τ p Λ) (boxR τ p Λ) := by
  refine Finset.disjoint_left.2 fun l hS hR => ?_
  simp only [boxS, boxR, Finset.mem_filter] at hS hR
  omega

theorem boxT_disjoint_boxR : Disjoint (boxT τ p Λ) (boxR τ p Λ) := by
  refine Finset.disjoint_left.2 fun l hT hR => ?_
  simp only [boxT, boxR, Finset.mem_filter] at hT hR
  omega

/-- **⭐ `hθR` AT THE BOX INDEX.** Transported from `irefl_eq_self_of_mem_iblkR` by `Subtype.ext`.

DERIVED: no numeral of its own. -/
theorem ireflBoxPerm_eq_self_of_mem_boxR (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {l : ↥Λ} (hl : l ∈ boxR τ p Λ) : ireflBoxPerm hΛ l = l := by
  simp only [boxR, Finset.mem_filter] at hl
  refine Subtype.ext ?_
  rw [ireflBoxPerm_coe]
  by_cases hτ : l.1.1 = τ
  · exfalso
    have := hl.2
    simp only [ireflLink, if_pos hτ, ireflSite_axis] at this
    omega
  · refine (nonTau_fixed_iff τ p hτ).2 ?_
    have := hl.2
    simp only [ireflLink, if_neg hτ, ireflSite_axis] at this
    omega

/-- **⭐ `hθST` AT THE BOX INDEX.**

DERIVED: no numeral of its own. -/
theorem ireflBoxPerm_mem_boxT_of_mem_boxS (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {l : ↥Λ} (hl : l ∈ boxS τ p Λ) : ireflBoxPerm hΛ l ∈ boxT τ p Λ := by
  simp only [boxS, Finset.mem_filter] at hl
  simp only [boxT, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [ireflBoxPerm_coe, ireflLink_involutive τ (2 * p) l.1]
  exact hl.2

#print axioms ireflBoxPerm_eq_self_of_mem_boxR
#print axioms ireflBoxPerm_mem_boxT_of_mem_boxS

/-- **NO `τ`-LINK LIES IN THE SHARED BLOCK**, at the box index — the transported
`no_tau_link_fixed`, and what makes the dagger trivial there.

DERIVED: no numeral of its own. -/
theorem boxR_ne_tau {l : ↥Λ} (hl : l ∈ boxR τ p Λ) : l.1.1 ≠ τ := by
  simp only [boxR, Finset.mem_filter] at hl
  intro hτ
  have := hl.2
  simp only [ireflLink, if_pos hτ, ireflSite_axis] at this
  omega

#print axioms boxR_ne_tau

/-- **A `τ`-LINK AT THE PLANE GOES DOWN.** Based at `x_τ = p` it reflects to `p - 1`, so it lands in
the POSITIVE block `boxS` and never in the shared one.

This is the boundary case the action split turns on: a plaquette in a `(τ, ν)` plane based at the
plane has its `τ`-links here and its transverse link in `boxR`, so it sits entirely inside
`S ∪ R` — which is what `hOloc` needs of the half-action.

DERIVED: the `2` is the plane-to-constant conversion and the `1` is `ireflLink`'s link length; `4` is
the dimension. -/
theorem tau_link_at_plane_moves_down {l : ILink} (hτ : l.1 = τ) (hp : l.2 τ = p) :
    (ireflLink τ (2 * p) l).2 τ < l.2 τ := by
  simp only [ireflLink, if_pos hτ, ireflSite_axis]
  omega

#print axioms tau_link_at_plane_moves_down

/-- **AND A NON-`τ` LINK AT THE PLANE IS FIXED**, hence in the shared block. The companion of the
previous lemma: together they say the plane carries transverse links only, and the time-direction
links at the plane belong to the positive half.

DERIVED: the `2` is the plane-to-constant conversion; `4` is the dimension. -/
theorem nonTau_link_at_plane_fixed {l : ILink} (hτ : l.1 ≠ τ) (hp : l.2 τ = p) :
    (ireflLink τ (2 * p) l).2 τ = l.2 τ := by
  simp only [ireflLink, if_neg hτ, ireflSite_axis]
  omega

#print axioms nonTau_link_at_plane_fixed

end Box

/-! ## ⭐ 3d′. Every plaquette lies on ONE side of the plane -/

section Plaquette

open MassGap.LatticeReflection

/-- The `τ` coordinate of a shifted site: up by one in direction `τ`, unchanged otherwise.

DERIVED: the `1` is `ishift`'s lattice step; `4` is the dimension. -/
theorem ishift_coord (μ τ : Fin 4) (x : MassGap.GibbsSpec.ISite) :
    (MassGap.GibbsSpec.ishift μ x) τ = if μ = τ then x τ + 1 else x τ := by
  by_cases h : μ = τ
  · subst h; simp [MassGap.GibbsSpec.ishift]
  · simp [MassGap.GibbsSpec.ishift, Ne.symm h, h]

/-- The reflected `τ` coordinate in closed form: a `τ`-link reflects about `2p - 1` because the link
occupies the segment `[x, x+e_τ]`, everything else about `2p`. Shared by the two directed lemmas.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`, the `1` is `ireflLink`'s link length,
and `4` is the dimension. -/
theorem irefl_coord (τ : Fin 4) (p : ℤ) (l : MassGap.InfiniteLattice.ILink) :
    (ireflLink τ (2 * p) l).2 τ = if l.1 = τ then 2 * p - 1 - l.2 τ else 2 * p - l.2 τ := by
  by_cases h : l.1 = τ
  · simp [ireflLink, if_pos h, ireflSite_axis]
  · simp [ireflLink, if_neg h, ireflSite_axis]

/-- **A PLAQUETTE BASED AT OR ABOVE THE PLANE HAS ALL FOUR LINKS IN `S ∪ R`.** `(irefl l).2 τ ≤ l.2 τ`
is exactly membership of the positive half together with the shared block — moved DOWN, or fixed.

This is the DIRECTED form, and it is the one the half-action needs: which side a plaquette belongs to
is decided by its base's `τ` coordinate against the plane, not merely that it belongs to one of them.

The delicate case is a `τ`-link, which reflects about `2p - 1`: it moves down exactly when
`x_τ ≥ p`, because `2x_τ ≥ 2p - 1` has no room between the integers.

**⛔ AND IT NEEDS NO NON-DEGENERACY HYPOTHESIS — the linter caught the author assuming otherwise.**
The first version carried `μ ≠ ν`, and the unreachable-tactic linter reported the fallback never
fired. It is right: on THIS side every case closes, degenerate included. A `τ`-link at `a ≥ p`
reflects to `2p - 1 - a ≤ a`; a non-`τ` link of a plaquette based at `a` sits at `a` or `a + 1`,
both `≥ p`, and reflects to `2p - b ≤ b`. The asymmetry is real — only `plaq_links_ge_of_lt` breaks,
and only at `μ = ν = τ` with `x_τ = p - 1`. An unused hypothesis would have been a false statement
about what the result costs.

DERIVED: the `2` is the plane-to-constant conversion, the `1`s are `ireflLink`'s link length and
`ishift`'s step, and `4` is the dimension. Nothing is chosen. -/
theorem plaq_links_le_of_le (τ : Fin 4) (p : ℤ) (q : MassGap.GibbsSpec.IPlaq)
    (hq : p ≤ q.2 τ) :
    ∀ l ∈ MassGap.GibbsSpec.ilinks q, (ireflLink τ (2 * p) l).2 τ ≤ l.2 τ := by
  intro l hl
  rw [MassGap.GibbsSpec.ilinks_eq] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  by_cases h1 : q.1.1 = τ <;> by_cases h2 : q.1.2 = τ <;>
    rcases hl with rfl | rfl | rfl | rfl <;>
    simp only [irefl_coord, ishift_coord, h1, h2, if_true, if_false] <;>
    omega

#print axioms plaq_links_le_of_le

/-- **AND A PLAQUETTE BASED BELOW THE PLANE HAS ALL FOUR LINKS IN `T ∪ R`** — the mirror statement,
moved UP or fixed.

**⛔ HERE IS WHERE DEGENERACY ACTUALLY BREAKS IT, AND THAT WAS MEASURED, NOT ARGUED.** At
`μ = ν = τ` and `x_τ = p - 1` the conclusion is FALSE: the link `(τ, x)` sits at `p - 1` and moves UP
to `p`, while `(τ, x + e_τ)` sits at `p` and moves DOWN to `p - 1`, so that plaquette straddles with
links strictly on both sides.

`hne` never appears in the tactic script, so the unreachable-tactic linter cannot say whether it is
load-bearing — `omega` reads it from the context. Removing it and rebuilding is the only test, and
that build fails here with two `omega could not prove the goal`s, one per degenerate `τ`-link, while
`plaq_links_le_of_le` stays clean. The asymmetry between the two sides is real.

DERIVED: as `plaq_links_le_of_le`. -/
theorem plaq_links_ge_of_lt (τ : Fin 4) (p : ℤ) (q : MassGap.GibbsSpec.IPlaq)
    (hne : q.1.1 ≠ q.1.2) (hq : q.2 τ < p) :
    ∀ l ∈ MassGap.GibbsSpec.ilinks q, l.2 τ ≤ (ireflLink τ (2 * p) l).2 τ := by
  intro l hl
  rw [MassGap.GibbsSpec.ilinks_eq] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  by_cases h1 : q.1.1 = τ <;> by_cases h2 : q.1.2 = τ <;>
    rcases hl with rfl | rfl | rfl | rfl <;>
    simp only [irefl_coord, ishift_coord, h1, h2, if_true, if_false] <;>
    omega

#print axioms plaq_links_ge_of_lt

/-- **⭐ EVERY PLAQUETTE SITS ENTIRELY ON ONE SIDE, TOGETHER WITH THE PLANE.** The undirected
corollary: no plaquette straddles with links strictly on both sides, which is what `ActionSplit`'s
`hOloc` and `hWloc` require of the action's two halves.

DERIVED: as `plaq_links_le_of_le`. -/
theorem plaq_links_one_side (τ : Fin 4) (p : ℤ) (q : MassGap.GibbsSpec.IPlaq)
    (hne : q.1.1 ≠ q.1.2) :
    -- `hne` is consumed by the NEGATIVE branch only; see `plaq_links_le_of_le`.
    (∀ l ∈ MassGap.GibbsSpec.ilinks q, (ireflLink τ (2 * p) l).2 τ ≤ l.2 τ) ∨
      (∀ l ∈ MassGap.GibbsSpec.ilinks q, l.2 τ ≤ (ireflLink τ (2 * p) l).2 τ) := by
  by_cases hq : q.2 τ < p
  · exact Or.inr (plaq_links_ge_of_lt τ p q hne hq)
  · exact Or.inl (plaq_links_le_of_le τ p q (not_lt.mp hq))

#print axioms plaq_links_one_side

end Plaquette

/-! ## ⭐ 3d″. The plaquettes of the positive half, and the links they read -/

section HalfPlaq

open MassGap.LatticeReflection

/-- **THE PLANE PLAQUETTES.** Transverse to `τ` and based exactly AT the plane, so every one of
their links is fixed by the reflection — they lie in the shared block `R`.

**⛔ THEY MUST NOT BE IN EITHER HALF-ACTION.** The reflection FIXES them (`2p - p = p`), so it does
not carry them from one half to the other; a factorisation `h(U) · h(ΘU)` would count them twice.
They belong to the plane weight, which is exactly what `ActionSplit.plqZero` is for on the torus.
This is invisible to `iplqPlus_links_mem` — a plane plaquette does read `S ∪ R` — and shows up only in
the covariance step.

DERIVED: no numeral of its own; `τ`, `p` and `Λ` are the caller's, and `4` is the dimension. -/
def iplqZero (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Finset MassGap.GibbsSpec.IPlaq :=
  (MassGap.GibbsSpec.plaqsIn Λ).filter
    (fun q => q.1.1 ≠ q.1.2 ∧ q.1.1 ≠ τ ∧ q.1.2 ≠ τ ∧ q.2 τ = p)

/-- **ALL THE PLAQUETTES THE ACTION SUMS OVER** at this box — inside it and non-degenerate. The three
groups below partition exactly this.

DERIVED: no numeral of its own; `Λ` is the caller's and `4` is the dimension. -/
def iplqAll (Λ : Finset MassGap.InfiniteLattice.ILink) : Finset MassGap.GibbsSpec.IPlaq :=
  (MassGap.GibbsSpec.plaqsIn Λ).filter (fun q => q.1.1 ≠ q.1.2)

/-- **THE PLAQUETTES THE POSITIVE HALF-ACTION SUMS OVER.** Inside the box, non-degenerate, not in the
plane, based at or above it. The `ℤ⁴` counterpart of `ActionSplit.plqPlus`.

Degenerate plaquettes are filtered out rather than assumed away, because a `Finset IPlaq` carries no
`μ < ν` side condition and `plaq_links_ge_of_lt` is false without it. The whole diagonal `μ = ν` is
dropped, not just `μ = ν = τ`: its holonomy is the identity (`InfiniteLattice.ibd_diag_hol_one`), so
for the Wilson density it contributes `wilsonDensity 1 = 0` and dropping it changes nothing. For a
general `φ` it would shift the action by a constant per diagonal plaquette.

DERIVED: no numeral of its own; `τ`, `p` and `Λ` are the caller's, and `4` is the dimension. -/
def iplqPlus (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Finset MassGap.GibbsSpec.IPlaq :=
  (MassGap.GibbsSpec.plaqsIn Λ).filter
    (fun q => q.1.1 ≠ q.1.2 ∧ ¬ (q.1.1 ≠ τ ∧ q.1.2 ≠ τ ∧ q.2 τ = p) ∧ p ≤ q.2 τ)

/-- **AND ITS MIRROR** — the plaquettes the NEGATIVE half-action sums over, below the plane.

DERIVED: no numeral of its own; `τ`, `p` and `Λ` are the caller's, and `4` is the dimension. -/
def iplqMinus (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Finset MassGap.GibbsSpec.IPlaq :=
  (MassGap.GibbsSpec.plaqsIn Λ).filter
    (fun q => q.1.1 ≠ q.1.2 ∧ ¬ (q.1.1 ≠ τ ∧ q.1.2 ≠ τ ∧ q.2 τ = p) ∧ q.2 τ < p)

theorem mem_iplqPlus {τ : Fin 4} {p : ℤ} {Λ : Finset MassGap.InfiniteLattice.ILink}
    {q : MassGap.GibbsSpec.IPlaq} :
    q ∈ iplqPlus τ p Λ ↔
      q ∈ MassGap.GibbsSpec.plaqsIn Λ ∧ q.1.1 ≠ q.1.2 ∧
        ¬ (q.1.1 ≠ τ ∧ q.1.2 ≠ τ ∧ q.2 τ = p) ∧ p ≤ q.2 τ := by
  simp only [iplqPlus, Finset.mem_filter]

theorem mem_iplqMinus {τ : Fin 4} {p : ℤ} {Λ : Finset MassGap.InfiniteLattice.ILink}
    {q : MassGap.GibbsSpec.IPlaq} :
    q ∈ iplqMinus τ p Λ ↔
      q ∈ MassGap.GibbsSpec.plaqsIn Λ ∧ q.1.1 ≠ q.1.2 ∧
        ¬ (q.1.1 ≠ τ ∧ q.1.2 ≠ τ ∧ q.2 τ = p) ∧ q.2 τ < p := by
  simp only [iplqMinus, Finset.mem_filter]

#print axioms mem_iplqPlus

theorem iplqPlus_disjoint_iplqMinus (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Disjoint (iplqPlus τ p Λ) (iplqMinus τ p Λ) := by
  refine Finset.disjoint_left.2 fun q hP hM => ?_
  exact absurd (mem_iplqMinus.mp hM).2.2.2 (not_lt.mpr (mem_iplqPlus.mp hP).2.2.2)

#print axioms iplqPlus_disjoint_iplqMinus

/-- **⭐ THE REFLECTION CARRIES THE POSITIVE HALF ONTO THE NEGATIVE ONE.** The `ℤ⁴` counterpart of
`ActionSplit.reflPlaq_plus_mem_minus`, and what makes `h(ΘU)` the other half-action.

Three branches, and the third is where excluding the plane plaquettes pays: for a transverse
plaquette the image's base sits at `2p - x_τ`, which is `< p` only when `x_τ > p`. At `x_τ = p` the
plaquette is its own image — that is `iplqZero`, and it is excluded from `iplqPlus` for precisely this
reason.

The `plaqsIn` half is a hypothesis rather than a conclusion: it holds whenever `Λ` is stable under
the link reflection, which is the same `hΛ` that `irefl_box_pairing_nonneg` already takes.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`, the `1` is `ireflPlaq`'s link-length
offset, and `4` is the dimension. -/
theorem ireflPlaq_mem_iplqMinus (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    {q : MassGap.GibbsSpec.IPlaq} (hq : q ∈ iplqPlus τ p Λ)
    (hmem : ireflPlaq τ (2 * p) q ∈ MassGap.GibbsSpec.plaqsIn Λ) :
    ireflPlaq τ (2 * p) q ∈ iplqMinus τ p Λ := by
  obtain ⟨_, hne, hnz, hge⟩ := mem_iplqPlus.mp hq
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  simp only at hne hnz hge
  rw [mem_iplqMinus]
  by_cases hμ : μ = τ
  · subst hμ
    refine ⟨hmem, ?_, ?_, ?_⟩
    · simpa [ireflPlaq] using fun h => hne h.symm
    · simp [ireflPlaq]
    · simp only [ireflPlaq, ireflSite_axis, reduceIte]
      omega
  · by_cases hν : ν = τ
    · subst hν
      refine ⟨hmem, ?_, ?_, ?_⟩
      · simpa [ireflPlaq, hμ] using fun h => hμ h.symm
      · simp [ireflPlaq, hμ]
      · simp only [ireflPlaq, if_neg hμ, ireflSite_axis, reduceIte]
        omega
    · have hxp : x τ ≠ p := fun h => hnz ⟨hμ, hν, h⟩
      refine ⟨hmem, ?_, ?_, ?_⟩
      · simpa [ireflPlaq, hμ, hν] using hne
      · simp only [ireflPlaq, if_neg hμ, if_neg hν, ireflSite_axis]
        rintro ⟨-, -, hz⟩
        omega
      · simp only [ireflPlaq, if_neg hμ, if_neg hν, ireflSite_axis]
        omega

#print axioms ireflPlaq_mem_iplqMinus

/-- **THE TWO `ishift`s ARE THE SAME FUNCTION**, and saying so is what lets the reflection lemmas
reach a goal produced by `GibbsSpec.ilinks_eq`.

`GibbsSpec` and `InfiniteLattice` are import-isolated and each defines `ISite` and `ishift` for
itself, with identical bodies. They are still two constants: a rewrite stated on one does not fire on
the other, and NOTHING IN A GOAL DISPLAY SHOWS IT — both print as `ishift`. What showed it here was
the unused-simp-argument linter naming three lemmas at once that plainly applied.

DERIVED: no numeral of its own; `4` is the dimension. -/
theorem gibbs_ishift_eq :
    (MassGap.GibbsSpec.ishift : Fin 4 → MassGap.GibbsSpec.ISite → MassGap.GibbsSpec.ISite)
      = MassGap.InfiniteLattice.ishift := rfl

#print axioms gibbs_ishift_eq

/-- **AND THE TWO `iunshift`s ARE THE SAME MAP**, for the same reason: identical bodies in two
isolated namespaces are still two constants, and nothing in a goal display tells them apart — both
print as `iunshift`. A lemma proved about one is inert on the other.

DERIVED: no numeral of its own; `4` is the dimension. -/
theorem gibbs_iunshift_eq :
    (MassGap.GibbsSpec.iunshift : Fin 4 → MassGap.GibbsSpec.ISite → MassGap.GibbsSpec.ISite)
      = MassGap.ReflectionShift.iunshift := rfl

#print axioms gibbs_iunshift_eq

/-- **EVERY LINK OF THE IMAGE PLAQUETTE IS A REFLECTED LINK OF THE ORIGINAL.**

Stated as "reflecting it again lands back in the original's links", which is the same thing by
involutivity and is the form the box transport consumes.

The ORDER differs — the mirror reverses the loop, which is the same fact `ihol_ireflConf` reads as
conjugacy rather than equality. `plaqsIn` asks only that every link be in the box, so order is not
something this has to track.

**⛔ IT IS FALSE FOR A `τ`-ALIGNED DEGENERATE PLAQUETTE, and the prover found that, not the author.**
`q = ((τ, τ), x)` has links at `x_τ` and `x_τ + 1`, covering `[x, x + 2e_τ]`; their reflections cover
`[c - 2 - x_τ, c - x_τ]`, based at `c - 2 - x_τ`. `ireflPlaq` puts the image base at `c - 1 - x_τ` —
off by one — so the image's links are NOT the reflections of the original's. The build left exactly
that one case open, with `ireflSite τ (c-1) (ishift τ (ireflSite τ (c-1) x))` against `ishift τ x`,
and it reduces to `x_τ - 1` against `x_τ + 1`.

`ireflPlaq` is not wrong where it is used: `ihol_ireflConf` holds for that plaquette anyway, with
`g = 1`, because a degenerate loop retraces itself and BOTH holonomies are the identity. The torus
has the same feature, which is why `ActionSplit.plqDeg` is a group of its own and is excluded from
the action split. The hypothesis below is exactly `plqDeg`'s complement, and `iplqPlus` excludes the
whole diagonal, so it costs nothing at the call site.

DERIVED: the `1` is `ireflPlaq`'s link-length offset; `4` is the dimension. -/
theorem ireflLink_mem_ilinks (τ : Fin 4) (c : ℤ) (q : MassGap.GibbsSpec.IPlaq)
    (hdeg : ¬ (q.1.1 = τ ∧ q.1.2 = τ)) {l : MassGap.InfiniteLattice.ILink}
    (hl : l ∈ MassGap.GibbsSpec.ilinks (ireflPlaq τ c q)) :
    ireflLink τ c l ∈ MassGap.GibbsSpec.ilinks q := by
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  rw [MassGap.GibbsSpec.ilinks_eq] at hl ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
  by_cases hμ : μ = τ <;> by_cases hν : ν = τ
  · exact absurd ⟨hμ, hν⟩ hdeg
  all_goals
    simp only [ireflPlaq, hμ, hν, reduceIte] at hl
    rcases hl with rfl | rfl | rfl | rfl <;>
      simp [ireflLink, hμ, hν, gibbs_ishift_eq, ireflSite_ireflSite, ireflSite_ireflSite_pred,
        ireflSite_ishift_of_ne, ishift_ireflSite_axis]

#print axioms ireflLink_mem_ilinks

/-- **⭐ A REFLECTION-STABLE BOX CONTAINS THE IMAGE PLAQUETTE.** This discharges the `hmem`
hypothesis of `ireflPlaq_mem_iplqMinus` from the SAME `hΛ` that `irefl_box_pairing_nonneg` already
takes — no new assumption enters.

DERIVED: no numeral of its own; `4` is the dimension. -/
theorem ireflPlaq_mem_plaqsIn (τ : Fin 4) (c : ℤ) {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) {q : MassGap.GibbsSpec.IPlaq}
    (hdeg : ¬ (q.1.1 = τ ∧ q.1.2 = τ)) (hq : q ∈ MassGap.GibbsSpec.plaqsIn Λ) :
    ireflPlaq τ c q ∈ MassGap.GibbsSpec.plaqsIn Λ := by
  rw [MassGap.GibbsSpec.mem_plaqsIn]
  intro l hl
  have h1 : ireflLink τ c l ∈ Λ :=
    MassGap.GibbsSpec.mem_plaqsIn.mp hq _ (ireflLink_mem_ilinks τ c q hdeg hl)
  have h2 := hΛ _ h1
  rwa [ireflLink_involutive τ c l] at h2

#print axioms ireflPlaq_mem_plaqsIn

/-- **⭐ AND SO THE REFLECTION MAPS THE POSITIVE HALF INTO THE NEGATIVE ONE OUTRIGHT** — no leftover
hypothesis. This is `ActionSplit.reflPlaq_plus_mem_minus` on `ℤ⁴`.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`; `4` is the dimension. -/
theorem ireflPlaq_maps_plus_to_minus (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ) {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ iplqPlus τ p Λ) :
    ireflPlaq τ (2 * p) q ∈ iplqMinus τ p Λ :=
  ireflPlaq_mem_iplqMinus τ p Λ hq
    (ireflPlaq_mem_plaqsIn τ (2 * p) hΛ
      (fun h => (mem_iplqPlus.mp hq).2.1 (h.1.trans h.2.symm)) (mem_iplqPlus.mp hq).1)

#print axioms ireflPlaq_maps_plus_to_minus

/-- **AND EVERY LINK OF ONE LIES IN `S ∪ R`.** This is the step `ReflectionStrong.actPlus_local`
consumes on the torus (`plaq_links_le`): it is what makes the positive half-action an observable of
the positive half, hence what lets the half Boltzmann factor be absorbed into the observable.

DERIVED: no numeral of its own; `4` is the dimension. -/
theorem iplqPlus_links_mem (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    {q : MassGap.GibbsSpec.IPlaq} (hq : q ∈ iplqPlus τ p Λ)
    {l : MassGap.InfiniteLattice.ILink} (hl : l ∈ MassGap.GibbsSpec.ilinks q) (h : l ∈ Λ) :
    (⟨l, h⟩ : ↥Λ) ∈ boxS τ p Λ ∪ boxR τ p Λ := by
  obtain ⟨_, _, _, hge⟩ := mem_iplqPlus.mp hq
  have hle := plaq_links_le_of_le τ p q hge l hl
  simp only [Finset.mem_union, boxS, boxR, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

#print axioms iplqPlus_links_mem

/-- The links of a positive-half plaquette ARE in the box — the side condition
`iplqPlus_links_mem` asks for, read off the `plaqsIn` filter. -/
theorem iplqPlus_link_mem_box (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    {q : MassGap.GibbsSpec.IPlaq} (hq : q ∈ iplqPlus τ p Λ)
    {l : MassGap.InfiniteLattice.ILink} (hl : l ∈ MassGap.GibbsSpec.ilinks q) : l ∈ Λ :=
  MassGap.GibbsSpec.mem_plaqsIn.mp (mem_iplqPlus.mp hq).1 l hl

#print axioms iplqPlus_link_mem_box

end HalfPlaq

/-! ## ⭐ 3d″a. The three groups partition the box -/

section Partition

open MassGap.LatticeReflection

theorem mem_iplqZero {τ : Fin 4} {p : ℤ} {Λ : Finset MassGap.InfiniteLattice.ILink}
    {q : MassGap.GibbsSpec.IPlaq} :
    q ∈ iplqZero τ p Λ ↔
      q ∈ MassGap.GibbsSpec.plaqsIn Λ ∧ q.1.1 ≠ q.1.2 ∧
        (q.1.1 ≠ τ ∧ q.1.2 ≠ τ ∧ q.2 τ = p) := by
  simp only [iplqZero, Finset.mem_filter]

theorem mem_iplqAll {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq} :
    q ∈ iplqAll Λ ↔ q ∈ MassGap.GibbsSpec.plaqsIn Λ ∧ q.1.1 ≠ q.1.2 := by
  simp only [iplqAll, Finset.mem_filter]

#print axioms mem_iplqZero

theorem iplqZero_disjoint_iplqPlus (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Disjoint (iplqZero τ p Λ) (iplqPlus τ p Λ) := by
  refine Finset.disjoint_left.2 fun q hZ hP => ?_
  exact (mem_iplqPlus.mp hP).2.2.1 (mem_iplqZero.mp hZ).2.2

theorem iplqZero_disjoint_iplqMinus (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Disjoint (iplqZero τ p Λ) (iplqMinus τ p Λ) := by
  refine Finset.disjoint_left.2 fun q hZ hM => ?_
  exact (mem_iplqMinus.mp hM).2.2.1 (mem_iplqZero.mp hZ).2.2

/-- **⭐ THE THREE GROUPS PARTITION THE BOX'S PLAQUETTES.** Every non-degenerate plaquette of the box
is in the plane, above it, or below it — and in exactly one of the three.

DERIVED: no numeral of its own; `4` is the dimension. -/
theorem iplq_union (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    iplqZero τ p Λ ∪ iplqPlus τ p Λ ∪ iplqMinus τ p Λ = iplqAll Λ := by
  ext q
  simp only [Finset.mem_union, mem_iplqZero, mem_iplqPlus, mem_iplqMinus, mem_iplqAll]
  constructor
  · rintro ((⟨h, hne, -⟩ | ⟨h, hne, -⟩) | ⟨h, hne, -⟩) <;> exact ⟨h, hne⟩
  · rintro ⟨h, hne⟩
    by_cases hz : q.1.1 ≠ τ ∧ q.1.2 ≠ τ ∧ q.2 τ = p
    · exact Or.inl (Or.inl ⟨h, hne, hz⟩)
    · by_cases hge : p ≤ q.2 τ
      · exact Or.inl (Or.inr ⟨h, hne, hz, hge⟩)
      · exact Or.inr ⟨h, hne, hz, not_le.mp hge⟩

#print axioms iplq_union

/-- **⭐ AND SO THE ACTION SPLITS** into a plane part and the two halves. With
`action_iplqPlus_ireflConf` this is the factorisation
`exp(-βS) = exp(-βA₀) · exp(-βA₊(U)) · exp(-βA₊(ΘU))` — a weight reading the shared block only,
times an observable times its own reflection, which is exactly what
`ActionSplit.pairing_nonneg_of_local` consumes.

DERIVED: no numeral of its own; `4` is the dimension. -/
theorem actionOn_split_three {G : Type} [Group G] (φ : G → ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (U : MassGap.GibbsSpec.IConf G) :
    MassGap.GibbsSpec.actionOn φ (iplqAll Λ) U
      = MassGap.GibbsSpec.actionOn φ (iplqZero τ p Λ) U
        + MassGap.GibbsSpec.actionOn φ (iplqPlus τ p Λ) U
        + MassGap.GibbsSpec.actionOn φ (iplqMinus τ p Λ) U := by
  unfold MassGap.GibbsSpec.actionOn
  rw [← iplq_union τ p Λ,
    Finset.sum_union (Finset.disjoint_union_left.2
      ⟨iplqZero_disjoint_iplqMinus τ p Λ, iplqPlus_disjoint_iplqMinus τ p Λ⟩),
    Finset.sum_union (iplqZero_disjoint_iplqPlus τ p Λ)]

#print axioms actionOn_split_three

end Partition

/-! ## ⭐ 3d‴a. The reflection is a BIJECTION between the two halves -/

section Bijection

open MassGap.LatticeReflection

/-- **THE MIRROR OF `ireflPlaq_mem_iplqMinus`** — the reflection carries the negative half back onto
the positive one. Needed because the action identity reindexes a sum, which wants a bijection, not
just a map.

Its third branch needs no non-plane hypothesis: below the plane `x_τ < p` already forces
`2p - x_τ > p`, so the image cannot land ON the plane.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`, the `1` is `ireflPlaq`'s link-length
offset, and `4` is the dimension. -/
theorem ireflPlaq_mem_iplqPlus (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    {q : MassGap.GibbsSpec.IPlaq} (hq : q ∈ iplqMinus τ p Λ)
    (hmem : ireflPlaq τ (2 * p) q ∈ MassGap.GibbsSpec.plaqsIn Λ) :
    ireflPlaq τ (2 * p) q ∈ iplqPlus τ p Λ := by
  obtain ⟨_, hne, _, hlt⟩ := mem_iplqMinus.mp hq
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  simp only at hne hlt
  rw [mem_iplqPlus]
  by_cases hμ : μ = τ
  · subst hμ
    refine ⟨hmem, ?_, ?_, ?_⟩
    · simpa [ireflPlaq] using fun h => hne h.symm
    · simp [ireflPlaq]
    · simp only [ireflPlaq, ireflSite_axis, reduceIte]
      omega
  · by_cases hν : ν = τ
    · subst hν
      refine ⟨hmem, ?_, ?_, ?_⟩
      · simpa [ireflPlaq, hμ] using fun h => hμ h.symm
      · simp [ireflPlaq, hμ]
      · simp only [ireflPlaq, if_neg hμ, ireflSite_axis, reduceIte]
        omega
    · refine ⟨hmem, ?_, ?_, ?_⟩
      · simpa [ireflPlaq, hμ, hν] using hne
      · simp only [ireflPlaq, if_neg hμ, if_neg hν, ireflSite_axis]
        rintro ⟨-, -, hz⟩
        omega
      · simp only [ireflPlaq, if_neg hμ, if_neg hν, ireflSite_axis]
        omega

#print axioms ireflPlaq_mem_iplqPlus

/-- The negative half maps back into the positive one outright, on the same `hΛ`.

DERIVED: the `2` is the plane-to-constant conversion; `4` is the dimension. -/
theorem ireflPlaq_maps_minus_to_plus (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ) {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ iplqMinus τ p Λ) :
    ireflPlaq τ (2 * p) q ∈ iplqPlus τ p Λ :=
  ireflPlaq_mem_iplqPlus τ p Λ hq
    (ireflPlaq_mem_plaqsIn τ (2 * p) hΛ
      (fun h => (mem_iplqMinus.mp hq).2.1 (h.1.trans h.2.symm)) (mem_iplqMinus.mp hq).1)

#print axioms ireflPlaq_maps_minus_to_plus

end Bijection

/-! ## ⭐ 3d‴b. The reflected positive half-action IS the negative half-action -/

section Covariance

open MassGap.LatticeReflection MassGap.WilsonLattice

variable {G : Type} [Group G]

/-- **THE TWO `ibd`s ARE THE SAME WORD**, so `GibbsSpec.ihol` is the holonomy `ihol_ireflConf` talks
about. The same import-isolation bridge as `gibbs_ishift_eq`, for the same reason: identical bodies
in two isolated namespaces are still two constants.

DERIVED: no numeral of its own; `4` is the dimension. -/
theorem gibbs_ihol_eq (q : MassGap.GibbsSpec.IPlaq) (U : MassGap.GibbsSpec.IConf G) :
    MassGap.GibbsSpec.ihol q U = wilsonHol MassGap.InfiniteLattice.ibd q U := rfl

#print axioms gibbs_ihol_eq

/-- **⭐ THE REFLECTED POSITIVE HALF-ACTION IS THE NEGATIVE HALF-ACTION.**

This is what makes `exp(-βS)` factor as `w(U|R) · h(U) · h(ΘU)` — the shape
`ActionSplit.pairing_nonneg_of_local` consumes, and the `ℤ⁴` counterpart of
`ActionSplit.sum_plqMinus_eq_plus_refl`.

It does NOT go through a `LatticeGauge.Symmetry`, and cannot: the mirrored holonomy is only
CONJUGATE to the image plaquette's (`ihol_ireflConf`). What carries the sum is that `φ` is a CLASS
FUNCTION — true of the Wilson density (`WilsonAction.wilsonDensity_conj`) — together with the
reflection being a bijection `iplqPlus ↔ iplqMinus`.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`; `4` is the dimension. -/
theorem action_iplqPlus_ireflConf (φ : G → ℝ) (hφ : ∀ g h : G, φ (g * h * g⁻¹) = φ h)
    (τ : Fin 4) (p : ℤ) {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ) (U : MassGap.GibbsSpec.IConf G) :
    MassGap.GibbsSpec.actionOn φ (iplqPlus τ p Λ) (ireflConf τ (2 * p) U)
      = MassGap.GibbsSpec.actionOn φ (iplqMinus τ p Λ) U := by
  unfold MassGap.GibbsSpec.actionOn
  refine Finset.sum_nbij' (i := fun q => ireflPlaq τ (2 * p) q)
    (j := fun q => ireflPlaq τ (2 * p) q)
    (fun a ha => ireflPlaq_maps_plus_to_minus τ p hΛ ha)
    (fun b hb => ireflPlaq_maps_minus_to_plus τ p hΛ hb)
    (fun a _ => ireflPlaq_involutive τ (2 * p) a)
    (fun b _ => ireflPlaq_involutive τ (2 * p) b)
    (fun a _ => ?_)
  obtain ⟨g, hg⟩ := ihol_ireflConf τ (2 * p) a U
  rw [gibbs_ihol_eq, gibbs_ihol_eq, hg, hφ]

#print axioms action_iplqPlus_ireflConf

/-- **THE REFLECTION PRESERVES NON-DEGENERACY**, hence maps `iplqAll` into itself on a stable box.

At `μ = τ` the image plane is `(ν, τ)` with `ν ≠ τ`; at `ν = τ` it is `(τ, μ)` with `μ ≠ τ`;
otherwise it is `(μ, ν)` unchanged. In every case a non-diagonal plane stays non-diagonal.

DERIVED: `c` is the caller's reflection constant, no longer pinned to an even `2p`; `4` is the
dimension. -/
theorem ireflPlaq_mem_iplqAll (τ : Fin 4) (c : ℤ) {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ iplqAll Λ) : ireflPlaq τ c q ∈ iplqAll Λ := by
  obtain ⟨hin, hne⟩ := mem_iplqAll.mp hq
  refine mem_iplqAll.mpr ⟨ireflPlaq_mem_plaqsIn τ c hΛ
    (fun h => hne (h.1.trans h.2.symm)) hin, ?_⟩
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  simp only at hne
  by_cases hμ : μ = τ
  · subst hμ
    simpa [ireflPlaq] using fun h => hne h.symm
  · by_cases hν : ν = τ
    · subst hν
      simpa [ireflPlaq, hμ] using fun h => hμ h.symm
    · simpa [ireflPlaq, hμ, hν] using hne

#print axioms ireflPlaq_mem_iplqAll

/-- **⭐ THE FULL ACTION IS INVARIANT UNDER THE REFLECTION.** The covariance machinery used the other
way: there `ireflPlaq` carried `iplqPlus` onto `iplqMinus`; here it carries `iplqAll` onto itself.

Same three ingredients — `ihol_ireflConf`, `φ` a class function, and `ireflPlaq` a bijection of the
index set, which on a reflection-stable box it is by involutivity.

DERIVED: `c` is the caller's reflection constant, no longer pinned to an even `2p`; `4` is the
dimension. -/
theorem action_iplqAll_ireflConf (φ : G → ℝ) (hφ : ∀ g h : G, φ (g * h * g⁻¹) = φ h)
    (τ : Fin 4) (c : ℤ) {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) (U : MassGap.GibbsSpec.IConf G) :
    MassGap.GibbsSpec.actionOn φ (iplqAll Λ) (ireflConf τ c U)
      = MassGap.GibbsSpec.actionOn φ (iplqAll Λ) U := by
  unfold MassGap.GibbsSpec.actionOn
  refine Finset.sum_nbij' (i := fun q => ireflPlaq τ c q)
    (j := fun q => ireflPlaq τ c q)
    (fun a ha => ireflPlaq_mem_iplqAll τ c hΛ ha)
    (fun b hb => ireflPlaq_mem_iplqAll τ c hΛ hb)
    (fun a _ => ireflPlaq_involutive τ c a)
    (fun b _ => ireflPlaq_involutive τ c b)
    (fun a _ => ?_)
  obtain ⟨g, hg⟩ := ihol_ireflConf τ c a U
  rw [gibbs_ihol_eq, gibbs_ihol_eq, hg, hφ]

#print axioms action_iplqAll_ireflConf

end Covariance

/-! ## ⭐ 3d‴. The half-action at a box, and its Boltzmann factor -/

section HalfAction

open MassGap.LatticeReflection

variable {G : Type} [Group G]

/-- **THE POSITIVE HALF-ACTION AT A BOX.** The Wilson action restricted to the plaquettes of
`iplqPlus`, read off a finite-volume configuration spliced into a background.

The background `ω` is inert: every plaquette summed over has all four links inside `Λ`
(`iplqPlus_link_mem_box`), so `splice` never consults it. It is carried rather than fixed because
`GibbsSpec.actionOn` is stated on `IConf G` and the finite-volume configuration lives on `↥Λ`.

DERIVED: no numeral of its own; `φ`, `τ`, `p`, `Λ` and `ω` are the caller's, and `4` is the
dimension. -/
noncomputable def iactPlus (φ : G → ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) : ℝ :=
  MassGap.GibbsSpec.actionOn φ (iplqPlus τ p Λ) (MassGap.GibbsSpec.splice Λ u ω)

/-- **⭐ THE HALF-ACTION READS `S ∪ R`** — the `ℤ⁴` counterpart of `ReflectionStrong.actPlus_local`,
and the reason the half Boltzmann factor can be absorbed into the observable.

The two hypotheses are kept apart rather than merged over the union because this is verbatim the
`hOloc` of `ActionSplit.pairing_nonneg_of_local`, which is where it is going.

DERIVED: no numeral of its own; `4` is the dimension. -/
theorem iactPlus_local (φ : G → ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u v : MassGap.GibbsSpec.VConf G Λ)
    (hS : ∀ l ∈ boxS τ p Λ, u l = v l) (hR : ∀ l ∈ boxR τ p Λ, u l = v l) :
    iactPlus φ τ p Λ ω u = iactPlus φ τ p Λ ω v := by
  refine MassGap.GibbsSpec.actionOn_congr φ _ _ _ (fun q hq l hl => ?_)
  have hlΛ : l ∈ Λ := iplqPlus_link_mem_box τ p Λ hq hl
  rw [MassGap.GibbsSpec.splice_mem hlΛ, MassGap.GibbsSpec.splice_mem hlΛ]
  rcases Finset.mem_union.mp (iplqPlus_links_mem τ p Λ hq hl hlΛ) with h | h
  · exact hS _ h
  · exact hR _ h

#print axioms iactPlus_local

/-- **THE HALF-SPACE BOLTZMANN FACTOR AT A BOX.** `ReflectionStrong.halfBoltz` on `ℤ⁴`.

DERIVED: no numeral of its own; the sign is the Gibbs convention `e^{-β S}` and `β` is the caller's.
-/
noncomputable def ihalfBoltz (φ : G → ℝ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) : ℝ :=
  Real.exp (-β * iactPlus φ τ p Λ ω u)

/-- **AND SO DOES THE FACTOR** — `exp` of a function of `S ∪ R` alone. Again in `hOloc`'s shape. -/
theorem ihalfBoltz_local (φ : G → ℝ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u v : MassGap.GibbsSpec.VConf G Λ)
    (hS : ∀ l ∈ boxS τ p Λ, u l = v l) (hR : ∀ l ∈ boxR τ p Λ, u l = v l) :
    ihalfBoltz φ β τ p Λ ω u = ihalfBoltz φ β τ p Λ ω v := by
  simp only [ihalfBoltz, iactPlus_local φ τ p Λ ω u v hS hR]

#print axioms ihalfBoltz_local

/-- **THE FACTOR IS STRICTLY POSITIVE**, which is what keeps the dressing from collapsing an
observable to zero and is `hWnn` for the plane weight built the same way. -/
theorem ihalfBoltz_pos (φ : G → ℝ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) :
    0 < ihalfBoltz φ β τ p Λ ω u :=
  Real.exp_pos _

#print axioms ihalfBoltz_pos

/-- **THE DRESSED OBSERVABLE** — the map that will carry the Gibbs pairing to the split pairing on
`ℤ⁴`, exactly as `ReflectionStrong.dressed` does on the torus.

DERIVED: no numeral of its own; the product is the dressing and `4` is the dimension. -/
noncomputable def idressed (φ : G → ℝ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (F : MassGap.GibbsSpec.VConf G Λ → ℝ) : MassGap.GibbsSpec.VConf G Λ → ℝ :=
  fun u => F u * ihalfBoltz φ β τ p Λ ω u

/-- **⭐ AND THE DRESSED OBSERVABLE STILL READS `S ∪ R`** — `hOloc` for the dressed observable,
given `hOloc` for the bare one. This is `ReflectionStrong.dressed_mem`'s locality half. -/
theorem idressed_local (φ : G → ℝ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    {F : MassGap.GibbsSpec.VConf G Λ → ℝ}
    (hF : ∀ u v : MassGap.GibbsSpec.VConf G Λ, (∀ l ∈ boxS τ p Λ, u l = v l) →
      (∀ l ∈ boxR τ p Λ, u l = v l) → F u = F v)
    (u v : MassGap.GibbsSpec.VConf G Λ)
    (hS : ∀ l ∈ boxS τ p Λ, u l = v l) (hR : ∀ l ∈ boxR τ p Λ, u l = v l) :
    idressed φ β τ p Λ ω F u = idressed φ β τ p Λ ω F v := by
  simp only [idressed, hF u v hS hR, ihalfBoltz_local φ β τ p Λ ω u v hS hR]

#print axioms idressed_local

end HalfAction

/-! ## ⭐ 3d‴c. The plane weight, which reads the shared block only -/

section PlaneWeight

open MassGap.LatticeReflection

/-- The links of a plane plaquette are in the box — read off the `plaqsIn` filter. -/
theorem iplqZero_link_mem_box (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    {q : MassGap.GibbsSpec.IPlaq} (hq : q ∈ iplqZero τ p Λ)
    {l : MassGap.InfiniteLattice.ILink} (hl : l ∈ MassGap.GibbsSpec.ilinks q) : l ∈ Λ :=
  MassGap.GibbsSpec.mem_plaqsIn.mp (mem_iplqZero.mp hq).1 l hl

/-- **⭐ EVERY LINK OF A PLANE PLAQUETTE IS FIXED BY THE REFLECTION**, so the whole group lives in the
shared block `boxR`. This is what makes the plane weight a `hWloc` weight.

Both spanning directions are transverse to `τ`, so no link of the plaquette points along `τ`, and
neither `ishift μ` nor `ishift ν` moves the `τ` coordinate — so all four links sit at the plane, where
a transverse link is fixed.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`; `4` is the dimension. -/
theorem iplqZero_links_mem (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    {q : MassGap.GibbsSpec.IPlaq} (hq : q ∈ iplqZero τ p Λ)
    {l : MassGap.InfiniteLattice.ILink} (hl : l ∈ MassGap.GibbsSpec.ilinks q) (h : l ∈ Λ) :
    (⟨l, h⟩ : ↥Λ) ∈ boxR τ p Λ := by
  obtain ⟨_, _, hμ, hν, hx⟩ := mem_iplqZero.mp hq
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  simp only at hμ hν hx
  rw [MassGap.GibbsSpec.ilinks_eq] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  simp only [boxR, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hl with rfl | rfl | rfl | rfl <;>
    simp only [irefl_coord, ishift_coord, hμ, hν, if_false] <;> omega

#print axioms iplqZero_links_mem

variable {G : Type} [Group G]

/-- **THE PLANE ACTION AT A BOX** — the Wilson action over the plane plaquettes alone.

DERIVED: no numeral of its own; `φ`, `τ`, `p`, `Λ` and `ω` are the caller's, and `4` is the
dimension. -/
noncomputable def iactZero (φ : G → ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) : ℝ :=
  MassGap.GibbsSpec.actionOn φ (iplqZero τ p Λ) (MassGap.GibbsSpec.splice Λ u ω)

/-- **⭐ THE PLANE ACTION READS `R` ALONE** — verbatim `hWloc`'s shape, one hypothesis over the shared
block and nothing else.

DERIVED: no numeral of its own; `4` is the dimension. -/
theorem iactZero_local (φ : G → ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u v : MassGap.GibbsSpec.VConf G Λ) (hR : ∀ l ∈ boxR τ p Λ, u l = v l) :
    iactZero φ τ p Λ ω u = iactZero φ τ p Λ ω v := by
  refine MassGap.GibbsSpec.actionOn_congr φ _ _ _ (fun q hq l hl => ?_)
  have hlΛ : l ∈ Λ := iplqZero_link_mem_box τ p Λ hq hl
  rw [MassGap.GibbsSpec.splice_mem hlΛ, MassGap.GibbsSpec.splice_mem hlΛ]
  exact hR _ (iplqZero_links_mem τ p Λ hq hl hlΛ)

#print axioms iactZero_local

/-- **THE PLANE WEIGHT** — the `W` of `ActionSplit.pairing_nonneg_of_local`, on `ℤ⁴`.

DERIVED: no numeral of its own; the sign is the Gibbs convention `e^{-βS}` and `β` is the caller's.
-/
noncomputable def iplaneWeight (φ : G → ℝ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) : ℝ :=
  Real.exp (-β * iactZero φ τ p Λ ω u)

/-- **`hWloc` FOR THE PLANE WEIGHT.** -/
theorem iplaneWeight_local (φ : G → ℝ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u v : MassGap.GibbsSpec.VConf G Λ) (hR : ∀ l ∈ boxR τ p Λ, u l = v l) :
    iplaneWeight φ β τ p Λ ω u = iplaneWeight φ β τ p Λ ω v := by
  simp only [iplaneWeight, iactZero_local φ τ p Λ ω u v hR]

/-- **`hWnn` FOR THE PLANE WEIGHT** — free, it is an exponential. -/
theorem iplaneWeight_nonneg (φ : G → ℝ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) :
    0 ≤ iplaneWeight φ β τ p Λ ω u :=
  (Real.exp_pos _).le

#print axioms iplaneWeight_local

#print axioms iplaneWeight_nonneg

end PlaneWeight

/-! ## ⭐ 3d‴d. The bound `C`, and measurability -/

section Bounds

open MassGap.LatticeReflection

/-- **THE EXPONENTIAL OF A BOUNDED ACTION IS BOUNDED.** The `ℤ⁴` counterpart of
`ActionSplit.abs_exp_actSum_le`.

DERIVED: the `2` is the range of the Wilson density (`WilsonAction.wilsonDensity_le_two` and
`wilsonDensity_nonneg`), carried in as `hφ0`/`hφ2`; the cardinality is the plaquette group's own.
Nothing is chosen. -/
theorem abs_exp_neg_actionOn_le {G : Type} [Group G] {φ : G → ℝ}
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (S : Finset MassGap.GibbsSpec.IPlaq) (U : MassGap.GibbsSpec.IConf G) :
    |Real.exp (-β * MassGap.GibbsSpec.actionOn φ S U)| ≤ Real.exp (|β| * ((S.card : ℝ) * 2)) := by
  rw [abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.mpr ?_
  calc -β * MassGap.GibbsSpec.actionOn φ S U
      ≤ |(-β) * MassGap.GibbsSpec.actionOn φ S U| := le_abs_self _
    _ = |β| * |MassGap.GibbsSpec.actionOn φ S U| := by rw [abs_mul, abs_neg]
    _ ≤ |β| * ((S.card : ℝ) * 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [abs_of_nonneg (MassGap.GibbsSpec.actionOn_nonneg hφ0 S U)]
        exact MassGap.GibbsSpec.actionOn_le hφ2 S U

#print axioms abs_exp_neg_actionOn_le

variable {G : Type} [Group G]

/-- The half Boltzmann factor is bounded. -/
theorem ihalfBoltz_abs_le {φ : G → ℝ} (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf G) (u : MassGap.GibbsSpec.VConf G Λ) :
    |ihalfBoltz φ β τ p Λ ω u| ≤ Real.exp (|β| * (((iplqPlus τ p Λ).card : ℝ) * 2)) :=
  abs_exp_neg_actionOn_le hφ0 hφ2 β _ _

/-- The plane weight is bounded. -/
theorem iplaneWeight_abs_le {φ : G → ℝ} (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf G) (u : MassGap.GibbsSpec.VConf G Λ) :
    |iplaneWeight φ β τ p Λ ω u| ≤ Real.exp (|β| * (((iplqZero τ p Λ).card : ℝ) * 2)) :=
  abs_exp_neg_actionOn_le hφ0 hφ2 β _ _

/-- **A DRESSED OBSERVABLE IS BOUNDED** when the bare one is. -/
theorem idressed_abs_le {φ : G → ℝ} (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf G) {F : MassGap.GibbsSpec.VConf G Λ → ℝ} {CF : ℝ}
    (hF : ∀ u, |F u| ≤ CF) (u : MassGap.GibbsSpec.VConf G Λ) :
    |idressed φ β τ p Λ ω F u| ≤ CF * Real.exp (|β| * (((iplqPlus τ p Λ).card : ℝ) * 2)) := by
  rw [idressed, abs_mul]
  exact mul_le_mul (hF u) (ihalfBoltz_abs_le hφ0 hφ2 β τ p Λ ω u) (abs_nonneg _)
    (le_trans (abs_nonneg _) (hF u))

#print axioms idressed_abs_le

/-- **⭐ `hC`'s SHAPE, ONCE AND FOR ALL**: a bounded weight times a bounded observable times that
observable at ANY other point is bounded by the product of the three bounds. The reflection enters
only as "some other point", so nothing about it needs to be known here.

DERIVED: no numeral; the bound is the product of the caller's two. -/
theorem abs_weight_obs_obs_le {α : Type} {W O : α → ℝ} {CW CO : ℝ}
    (hW : ∀ u, |W u| ≤ CW) (hO : ∀ u, |O u| ≤ CO) (f : α → α) (u : α) :
    |W u * O u * O (f u)| ≤ CW * CO * CO := by
  rw [abs_mul, abs_mul]
  refine mul_le_mul ?_ (hO (f u)) (abs_nonneg _) ?_
  · exact mul_le_mul (hW u) (hO u) (abs_nonneg _) (le_trans (abs_nonneg _) (hW u))
  · exact mul_nonneg (le_trans (abs_nonneg _) (hW u)) (le_trans (abs_nonneg _) (hO u))

#print axioms abs_weight_obs_obs_le

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

/-- The half-action is measurable in the finite-volume configuration. -/
theorem measurable_iactPlus {φ : G → ℝ} (hφ : Measurable φ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G) :
    Measurable (iactPlus φ τ p Λ ω) :=
  (MassGap.GibbsSpec.measurable_actionOn hφ _).comp
    (MassGap.GibbsSpec.measurable_splice_left Λ ω)

/-- The plane action is measurable in the finite-volume configuration. -/
theorem measurable_iactZero {φ : G → ℝ} (hφ : Measurable φ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G) :
    Measurable (iactZero φ τ p Λ ω) :=
  (MassGap.GibbsSpec.measurable_actionOn hφ _).comp
    (MassGap.GibbsSpec.measurable_splice_left Λ ω)

theorem measurable_ihalfBoltz {φ : G → ℝ} (hφ : Measurable φ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G) :
    Measurable (ihalfBoltz φ β τ p Λ ω) :=
  Real.measurable_exp.comp ((measurable_iactPlus hφ τ p Λ ω).const_mul _)

theorem measurable_iplaneWeight {φ : G → ℝ} (hφ : Measurable φ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G) :
    Measurable (iplaneWeight φ β τ p Λ ω) :=
  Real.measurable_exp.comp ((measurable_iactZero hφ τ p Λ ω).const_mul _)

theorem measurable_idressed {φ : G → ℝ} (hφ : Measurable φ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    {F : MassGap.GibbsSpec.VConf G Λ → ℝ} (hF : Measurable F) :
    Measurable (idressed φ β τ p Λ ω F) :=
  hF.mul (measurable_ihalfBoltz hφ β τ p Λ ω)

#print axioms measurable_idressed

#print axioms measurable_iplaneWeight

end Bounds

/-! ## ⭐ 3e. The Osterwalder–Seiler split on `ℤ⁴`, at a box -/

section Split

open MeasureTheory MassGap.CompactGauge MassGap.LatticeReflection

variable {N : ℕ} {τ : Fin 4} {p : ℤ} {Λ : Finset ILink}

/-- **⭐ THE OSTERWALDER–SEILER SPLIT ON `ℤ⁴`.** Reflection positivity of the pairing at a
reflection-stable box, from `ActionSplit.pairing_nonneg_of_local`.

**Every structural hypothesis is discharged here** by the pieces above: the blocks
`boxS`/`boxT`/`boxR` and their disjointness, `θ = ireflBoxPerm`, `hθR`, `hθST`, the dagger as `σ`,
`hσR` (from `boxR_ne_tau`: the shared block carries no `τ`-link, so the twist is trivial on it) and
`hσ` (Haar is inversion-invariant).

**⚠ WHAT IT STILL TAKES IS WILSON-SPECIFIC AND IS NOT SUPPLIED ANYWHERE**: that the observable reads
only `S ∪ R`, that the weight reads only `R` and is nonnegative, and that the integrand is bounded.
For the Wilson measure those come from DRESSING — absorbing the half Boltzmann weight into the
observable, as `ReflectionStrong.dressed_mem` does on the torus — and nothing here does that.

So this is the `ℤ⁴` counterpart of `ReflectionStrong.wilson_pairing_nonneg_module`'s inner step, with
the geometry discharged and the measure-theoretic content open.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`; `4` is the dimension. -/
theorem irefl_box_pairing_nonneg
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    (O : (↥Λ → MassGap.SUN.SU N) → ℝ) (hOm : Measurable O)
    (hOloc : ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxS τ p Λ, U i = V i) → (∀ i ∈ boxR τ p Λ, U i = V i) → O U = O V)
    (W : (↥Λ → MassGap.SUN.SU N) → ℝ) (hWm : Measurable W) (hWnn : ∀ U, 0 ≤ W U)
    (hWloc : ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxR τ p Λ, U i = V i) → W U = W V)
    (C : ℝ)
    (hC : ∀ U, |W U * O U *
      O (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
        (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) U)| ≤ C) :
    0 ≤ ∫ U, W U * O U *
      O (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
        (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) U)
      ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))) :=
  MassGap.ActionSplit.pairing_nonneg_of_local
    (probHaar (MassGap.SUN.SU N))
    (boxS τ p Λ) (boxT τ p Λ) (boxR τ p Λ)
    boxS_disjoint_boxT boxS_disjoint_boxR boxT_disjoint_boxR
    (ireflBoxPerm hΛ)
    (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1)
    (fun l => ilinkDagger_measurePreserving τ l.1)
    (fun _ hi => ireflBoxPerm_eq_self_of_mem_boxR hΛ hi)
    (fun _ hi u => ilinkDagger_eq_self_of_ne τ (boxR_ne_tau hi) u)
    (fun _ hi => ireflBoxPerm_mem_boxT_of_mem_boxS hΛ hi)
    (fun _ => 1)
    O hOm hOloc W hWm hWnn hWloc C hC

#print axioms irefl_box_pairing_nonneg

/-- **THE ABSTRACT TWIST AND THE CONCRETE REFLECTION AGREE ON THE BOX.**

`ActionSplit` works with `twist θ σ`, a relabelling-plus-fibre-map on the index type; the lattice
works with `ireflConf`, a relabelling-plus-inversion on configurations. They are the same thing
INSIDE `Λ`, and they need not agree outside it — every plaquette the action sums over has all four
links in the box, so nothing outside is ever read.

DERIVED: `c` is the caller's reflection constant, no longer pinned to an even `2p`; `4` is the
dimension. -/
theorem splice_twist_eq_ireflConf {c : ℤ} (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ)
    {l : ILink} (hl : l ∈ Λ) :
    MassGap.GibbsSpec.splice Λ
        (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
          (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) u) ω l
      = ireflConf τ c (MassGap.GibbsSpec.splice Λ u ω) l := by
  have himg : ireflLink τ c l ∈ Λ := hΛ l hl
  rw [MassGap.GibbsSpec.splice_mem hl]
  have hperm : (ireflBoxPerm hΛ ⟨l, hl⟩ : ↥Λ) = ⟨ireflLink τ c l, himg⟩ :=
    Subtype.ext (ireflBoxPerm_coe hΛ ⟨l, hl⟩)
  simp only [MassGap.ActionSplit.twist, hperm, ireflConf, ilinkDagger,
    MassGap.GibbsSpec.splice_mem himg]

#print axioms splice_twist_eq_ireflConf

/-- **THE REFLECTED HALF-ACTION AT THE BOX IS THE NEGATIVE HALF-ACTION.** `iactPlus` composed with
the abstract twist, identified through `action_iplqPlus_ireflConf`.

DERIVED: the `2` is the plane-to-constant conversion; `4` is the dimension. -/
theorem iactPlus_twist (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφ : ∀ g h, φ (g * h * g⁻¹) = φ h)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ) :
    iactPlus φ τ p Λ ω
        (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
          (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) u)
      = MassGap.GibbsSpec.actionOn φ (iplqMinus τ p Λ) (MassGap.GibbsSpec.splice Λ u ω) := by
  have h1 : iactPlus φ τ p Λ ω
      (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
        (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) u)
      = MassGap.GibbsSpec.actionOn φ (iplqPlus τ p Λ)
          (ireflConf τ (2 * p) (MassGap.GibbsSpec.splice Λ u ω)) :=
    MassGap.GibbsSpec.actionOn_congr φ _ _ _
      (fun q hq l hl => splice_twist_eq_ireflConf hΛ ω u (iplqPlus_link_mem_box τ p Λ hq hl))
  rw [h1]
  exact action_iplqPlus_ireflConf φ hφ τ p hΛ _

#print axioms iactPlus_twist

/-- **⭐⭐ THE GIBBS WEIGHT OF THE BOX IS A PLANE WEIGHT TIMES AN OBSERVABLE TIMES ITS REFLECTION.**

`e^{-βA(U)} = W(U) · h(U) · h(ΘU)`. This is the whole point of the split, and the exact shape
`ActionSplit.pairing_nonneg_of_local` consumes.

It is the product of two facts proved separately: the action splits into three groups
(`actionOn_split_three`), and the reflection carries the positive group onto the negative one
(`action_iplqPlus_ireflConf`, which needs `φ` to be a class function because the mirrored holonomy is
only CONJUGATE to the image plaquette's).

DERIVED: no numeral of its own; the sign is the Gibbs convention and `4` is the dimension. -/
theorem gibbs_weight_factors (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφ : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ) :
    Real.exp (-β * MassGap.GibbsSpec.actionOn φ (iplqAll Λ) (MassGap.GibbsSpec.splice Λ u ω))
      = iplaneWeight φ β τ p Λ ω u * ihalfBoltz φ β τ p Λ ω u
        * ihalfBoltz φ β τ p Λ ω
            (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
              (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) u) := by
  rw [actionOn_split_three φ τ p Λ]
  simp only [iplaneWeight, ihalfBoltz]
  rw [iactPlus_twist hΛ hφ ω u]
  simp only [iactZero, iactPlus]
  rw [mul_add, mul_add, Real.exp_add, Real.exp_add]

#print axioms gibbs_weight_factors

/-- **⭐⭐ REFLECTION POSITIVITY OF THE WILSON PAIRING ON `ℤ⁴`, AT A REFLECTION-STABLE BOX.**

Every hypothesis of `irefl_box_pairing_nonneg` discharged. What the caller supplies is only what is
genuinely about the theory rather than about the reflection:

* `φ` measurable, with `0 ≤ φ ≤ 2` — the Wilson density's own range
  (`WilsonAction.wilsonDensity_nonneg`, `wilsonDensity_le_two`);
* `F` measurable, bounded, and reading `S ∪ R` — an observable of the positive half.

The reflection contributes `hΛ` alone: the box is stable under the link reflection. Everything else
— the blocks, the dagger, the plane weight, the dressing, the bound — is proved here.

**⛔ `hφ` IS NOT DECORATION.** The mirrored holonomy is only CONJUGATE to the image plaquette's
(`ihol_ireflConf`), so the half-action covariance holds for a CLASS FUNCTION and for nothing weaker.
The Wilson density is one; a general `φ` is not.

DERIVED: the `2`s are the plane-to-constant conversion `c = 2p` and the Wilson density's ceiling;
`4` is the dimension. Nothing is chosen. -/
theorem irefl_box_wilson_pairing_nonneg
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    {F : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ → ℝ} (hFm : Measurable F)
    (hFloc : ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxS τ p Λ, U i = V i) → (∀ i ∈ boxR τ p Λ, U i = V i) → F U = F V)
    {CF : ℝ} (hFb : ∀ u, |F u| ≤ CF) :
    0 ≤ ∫ U, iplaneWeight φ β τ p Λ ω U * idressed φ β τ p Λ ω F U
        * idressed φ β τ p Λ ω F
            (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
              (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) U)
      ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))) :=
  irefl_box_pairing_nonneg hΛ
    (idressed φ β τ p Λ ω F) (measurable_idressed hφm β τ p Λ ω hFm)
    (fun U V hS hR => idressed_local φ β τ p Λ ω hFloc U V hS hR)
    (iplaneWeight φ β τ p Λ ω) (measurable_iplaneWeight hφm β τ p Λ ω)
    (iplaneWeight_nonneg φ β τ p Λ ω)
    (fun U V hR => iplaneWeight_local φ β τ p Λ ω U V hR)
    _
    (fun U => abs_weight_obs_obs_le
      (iplaneWeight_abs_le hφ0 hφ2 β τ p Λ ω)
      (idressed_abs_le hφ0 hφ2 β τ p Λ ω hFb) _ U)

#print axioms irefl_box_wilson_pairing_nonneg

/-- **THE FREE-BOUNDARY WEIGHT OF A BOX.**

**⛔ IT IS NOT `GibbsSpec.wt`, AND THE DIFFERENCE IS THE WHOLE POINT.** `wt` sums over
`boundaryPlaqs Λ` — every plaquette with SOME link in `Λ`. Those straddling the edge read the
boundary condition `ω` outside the box, and they do not split: a plaquette with links on both sides
of the box EDGE belongs to neither half of the reflection.

Reflection positivity is a statement about the FREE-boundary measure, which sums over `iplqAll Λ` —
every link inside. That is not a weakening chosen for convenience, it is what the Osterwalder–Seiler
argument proves; the DLR kernel with an arbitrary `ω` has no reason to be reflection positive.

`ω` is carried and inert: every plaquette of `iplqAll` has all four links in `Λ`, so `splice` never
consults it.

DERIVED: no numeral of its own; the sign is the Gibbs convention and `4` is the dimension. -/
noncomputable def wtFree {G : Type} [Group G] (φ : G → ℝ) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) : ℝ :=
  Real.exp (-β * MassGap.GibbsSpec.actionOn φ (iplqAll Λ) (MassGap.GibbsSpec.splice Λ u ω))

theorem wtFree_pos {G : Type} [Group G] (φ : G → ℝ) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) : 0 < wtFree φ β Λ ω u := Real.exp_pos _

#print axioms wtFree_pos

/-- **⭐⭐ THE REFLECTION PAIRING OF A HALF-SPACE OBSERVABLE IS NONNEGATIVE IN THE FREE-BOUNDARY
MEASURE.**

`0 ≤ ∫ F(U) · F(ΘU) · e^{-βA(U)}` — reflection positivity in the form the OS reconstruction wants,
with the Gibbs weight itself rather than a weight already split by hand.

The rearrangement is the content of `gibbs_weight_factors`:
`F(U) · F(ΘU) · e^{-βA(U)} = W(U) · (F·h)(U) · (F·h)(ΘU)`, and `F·h` is exactly `idressed`.

DERIVED: the `2`s are the plane-to-constant conversion and the Wilson density's ceiling; `4` is the
dimension. Nothing is chosen. -/
theorem wtFree_refl_pairing_nonneg
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    {F : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ → ℝ} (hFm : Measurable F)
    (hFloc : ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxS τ p Λ, U i = V i) → (∀ i ∈ boxR τ p Λ, U i = V i) → F U = F V)
    {CF : ℝ} (hFb : ∀ u, |F u| ≤ CF) :
    0 ≤ ∫ U, F U *
        F (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
            (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) U)
        * wtFree φ β Λ ω U
      ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))) := by
  have hfun : (fun U : ↥Λ → MassGap.SUN.SU N => F U *
      F (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
          (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) U)
      * wtFree φ β Λ ω U)
      = fun U => iplaneWeight φ β τ p Λ ω U * idressed φ β τ p Λ ω F U
          * idressed φ β τ p Λ ω F
              (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
                (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) U) := by
    funext U
    rw [wtFree, gibbs_weight_factors hΛ hφc β ω U]
    simp only [idressed]
    ring
  rw [hfun]
  exact irefl_box_wilson_pairing_nonneg hΛ hφm hφ0 hφ2 β ω hFm hFloc hFb

#print axioms wtFree_refl_pairing_nonneg

/-- The free weight is bounded, by the same argument as `GibbsSpec.wt_le` over a smaller plaquette
set.

DERIVED: the `2` is the Wilson density's ceiling, carried in as `hφ2`; the cardinality is the
plaquette set's own. -/
theorem wtFree_le {G : Type} [Group G] {φ : G → ℝ} (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) :
    |wtFree φ β Λ ω u| ≤ Real.exp (|β| * (((iplqAll Λ).card : ℝ) * 2)) :=
  abs_exp_neg_actionOn_le hφ0 hφ2 β _ _

theorem measurable_wtFree {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [MeasurableInv G] {φ : G → ℝ} (hφ : Measurable φ) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G) :
    Measurable (wtFree φ β Λ ω) :=
  Real.measurable_exp.comp
    (((MassGap.GibbsSpec.measurable_actionOn hφ (iplqAll Λ)).comp
      (MassGap.GibbsSpec.measurable_splice_left Λ ω)).const_mul (-β))

#print axioms measurable_wtFree

/-- **THE FREE-BOUNDARY PARTITION FUNCTION OF A BOX.**

DERIVED: no numeral of its own; the measure is product Haar over the box's links. -/
noncomputable def partFree {φ : MassGap.SUN.SU N → ℝ} (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) : ℝ :=
  ∫ u, wtFree φ β Λ ω u ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N)))

/-- **THE PARTITION FUNCTION IS STRICTLY POSITIVE**, so the normalisation is legitimate. Exactly
`GibbsSpec.part_pos`'s argument, over the free plaquette set: the integrand is strictly positive
everywhere, so its support is the whole space, which the probability measure gives measure one.

DERIVED: the `2` is the Wilson density's ceiling; `4` is the dimension. -/
theorem partFree_pos {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    0 < partFree (φ := φ) β Λ ω := by
  unfold partFree
  rw [integral_pos_iff_support_of_nonneg (fun u => (wtFree_pos φ β Λ ω u).le)
    (MassGap.GibbsSpec.integrable_of_bounded _ (measurable_wtFree hφm β Λ ω)
      (wtFree_le hφ0 hφ2 β Λ ω))]
  have hsupp : Function.support (wtFree φ β Λ ω) = Set.univ :=
    Set.eq_univ_of_forall (fun u => Function.mem_support.mpr (wtFree_pos φ β Λ ω u).ne')
  rw [hsupp, measure_univ]
  exact one_pos

#print axioms partFree_pos

/-- **THE FREE-BOUNDARY EXPECTATION OF A BOX** — the normalised state whose limit Chain B's endpoint
takes.

DERIVED: no numeral of its own. -/
noncomputable def specFree {φ : MassGap.SUN.SU N → ℝ} (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (f : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ → ℝ) : ℝ :=
  (∫ u, f u * wtFree φ β Λ ω u ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))))
    / partFree (φ := φ) β Λ ω

/-- **⭐⭐ REFLECTION POSITIVITY OF THE FREE-BOUNDARY STATE OF A BOX.**

`0 ≤ ⟨F · (F ∘ Θ)⟩_Λ`, normalised — which is `InfiniteReflection.ReflPositiveOn`'s content at one
finite volume, and the thing `reflPositive_of_tendsto` transports to the limit.

The numerator is `wtFree_refl_pairing_nonneg`; the denominator is `partFree_pos`.

DERIVED: the `2`s are the plane-to-constant conversion and the Wilson density's ceiling; `4` is the
dimension. Nothing is chosen. -/
theorem specFree_refl_nonneg
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    {F : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ → ℝ} (hFm : Measurable F)
    (hFloc : ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxS τ p Λ, U i = V i) → (∀ i ∈ boxR τ p Λ, U i = V i) → F U = F V)
    {CF : ℝ} (hFb : ∀ u, |F u| ≤ CF) :
    0 ≤ specFree (φ := φ) β Λ ω
      (fun u => F u * F (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
        (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) u)) := by
  refine div_nonneg ?_ (partFree_pos hφm hφ0 hφ2 β Λ ω).le
  exact wtFree_refl_pairing_nonneg hΛ hφm hφ0 hφ2 hφc β ω hFm hFloc hFb

#print axioms specFree_refl_nonneg

/-- **⭐⭐ REFLECTION POSITIVITY OF THE FREE-BOUNDARY STATE, FOR AN OBSERVABLE OF THE LATTICE.**

`0 ≤ ⟨f · (f ∘ Θ)⟩_Λ` where `f` is a function of the WHOLE configuration and `Θ` is the concrete
lattice reflection `ireflConf` — which is the form `InfiniteReflection.ReflPositiveOn` asks for, and
the last step before `reflPositive_of_tendsto` can be applied.

**⛔ `hfΛ` (LOCALITY TO THE BOX) IS LOAD-BEARING AND IS NOT A CONVENIENCE.**
`splice_twist_eq_ireflConf` says the abstract twist and `ireflConf` agree ON `Λ` and says nothing off
it — they need not agree there. An `f` that could see outside the box would distinguish the two and
the identification would fail.

That is exactly why `InfiniteReflection.reflPositive_of_tendsto` holds its submodule `A` FIXED across
the volumes: `A` must be observables local to ONE fixed finite region of the positive half, and every
box past some point contains it. A half-space algebra that grew with the volume would have no limit
to transport to.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`; `4` is the dimension. -/
theorem specFree_refl_nonneg_of_local
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    {f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ}
    (hfm : Measurable (fun u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ =>
      f (MassGap.GibbsSpec.splice Λ u ω)))
    (hfΛ : ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
      (∀ l ∈ Λ, U l = V l) → f U = f V)
    (hfloc : ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxS τ p Λ, U i = V i) → (∀ i ∈ boxR τ p Λ, U i = V i) →
      f (MassGap.GibbsSpec.splice Λ U ω) = f (MassGap.GibbsSpec.splice Λ V ω))
    {CF : ℝ} (hfb : ∀ u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ,
      |f (MassGap.GibbsSpec.splice Λ u ω)| ≤ CF) :
    0 ≤ specFree (φ := φ) β Λ ω
      (fun u => f (MassGap.GibbsSpec.splice Λ u ω)
        * f (ireflConf τ (2 * p) (MassGap.GibbsSpec.splice Λ u ω))) := by
  have hkey : ∀ u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ,
      f (ireflConf τ (2 * p) (MassGap.GibbsSpec.splice Λ u ω))
        = f (MassGap.GibbsSpec.splice Λ
            (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
              (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) u) ω) := by
    intro u
    exact (hfΛ _ _ (fun l hl => splice_twist_eq_ireflConf hΛ ω u hl)).symm
  simp only [hkey]
  exact specFree_refl_nonneg hΛ hφm hφ0 hφ2 hφc β ω hfm hfloc hfb

#print axioms specFree_refl_nonneg_of_local

/-! ## ⭐ 3g. The free-boundary expectation is a STATE -/

section StateAlgebra

open MeasureTheory MassGap.CompactGauge MassGap.LatticeReflection

/-- A bounded measurable observable against the free weight is integrable — bounded times bounded on
a probability space.

DERIVED: the `2` is the Wilson density's ceiling, carried in as `hφ2`; the cardinality is the
plaquette set's own. -/
theorem integrable_numFree {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    {F : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ → ℝ} (hFm : Measurable F)
    {CF : ℝ} (hFb : ∀ u, |F u| ≤ CF) :
    Integrable (fun u => F u * wtFree φ β Λ ω u)
      (MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))) := by
  refine MassGap.GibbsSpec.integrable_of_bounded _ (hFm.mul (measurable_wtFree hφm β Λ ω))
    (C := CF * Real.exp (|β| * (((iplqAll Λ).card : ℝ) * 2))) (fun u => ?_)
  rw [abs_mul]
  exact mul_le_mul (hFb u) (wtFree_le hφ0 hφ2 β Λ ω u) (abs_nonneg _)
    (le_trans (abs_nonneg _) (hFb u))

#print axioms integrable_numFree

/-- **ADDITIVITY.** -/
theorem specFree_add {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    {F G : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ → ℝ}
    (hFm : Measurable F) {CF : ℝ} (hFb : ∀ u, |F u| ≤ CF)
    (hGm : Measurable G) {CG : ℝ} (hGb : ∀ u, |G u| ≤ CG) :
    specFree (φ := φ) β Λ ω (fun u => F u + G u)
      = specFree (φ := φ) β Λ ω F + specFree (φ := φ) β Λ ω G := by
  unfold specFree
  rw [← add_div]
  congr 1
  rw [← integral_add (integrable_numFree hφm hφ0 hφ2 β Λ ω hFm hFb)
    (integrable_numFree hφm hφ0 hφ2 β Λ ω hGm hGb)]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun u => by ring))

#print axioms specFree_add

/-- **HOMOGENEITY.** -/
theorem specFree_smul {φ : MassGap.SUN.SU N → ℝ} (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (c : ℝ)
    (F : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ → ℝ) :
    specFree (φ := φ) β Λ ω (fun u => c * F u) = c * specFree (φ := φ) β Λ ω F := by
  unfold specFree
  rw [← mul_div_assoc]
  congr 1
  simp only [mul_assoc]
  rw [integral_const_mul]

#print axioms specFree_smul

/-- **NORMALISATION** — the partition function divided by itself.

DERIVED: the `1`s are the constant observable's value and the normalised result. -/
theorem specFree_one {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    specFree (φ := φ) β Λ ω (fun _ => 1) = 1 := by
  unfold specFree
  have h : (∫ u, (1 : ℝ) * wtFree φ β Λ ω u
      ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))))
      = partFree (φ := φ) β Λ ω := by
    unfold partFree
    exact integral_congr_ae (Filter.Eventually.of_forall (fun u => one_mul _))
  rw [h]
  exact div_self (partFree_pos hφm hφ0 hφ2 β Λ ω).ne'

#print axioms specFree_one

/-- **POSITIVITY** — the free weight is strictly positive everywhere, so a pointwise nonnegative
observable has a nonnegative integral, and the denominator is positive.

DERIVED: the `0` is the sign asserted. -/
theorem specFree_nonneg {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    {F : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ → ℝ} (hF : ∀ u, 0 ≤ F u) :
    0 ≤ specFree (φ := φ) β Λ ω F := by
  refine div_nonneg ?_ (partFree_pos hφm hφ0 hφ2 β Λ ω).le
  exact integral_nonneg (fun u => mul_nonneg (hF u) (wtFree_pos φ β Λ ω u).le)

#print axioms specFree_nonneg

/-- The observable a continuous lattice function induces on the box, measurable and bounded because
the configuration space is compact. -/
theorem boxObs_measurable {Λ : Finset MassGap.InfiniteLattice.ILink}
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    Measurable (fun u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ =>
      f (MassGap.GibbsSpec.splice Λ u ω)) :=
  f.continuous.measurable.comp (MassGap.GibbsSpec.measurable_splice_left Λ ω)

theorem boxObs_bounded {Λ : Finset MassGap.InfiniteLattice.ILink}
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    ∃ C : ℝ, ∀ u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ,
      |f (MassGap.GibbsSpec.splice Λ u ω)| ≤ C := by
  obtain ⟨C, hC⟩ := MassGap.InfiniteLattice.bounded_of_continuous f.continuous
  exact ⟨C, fun u => hC _⟩

#print axioms boxObs_bounded

/-- **⭐⭐ THE FREE-BOUNDARY STATE OF A BOX.** The finite-volume object whose limit Chain B's endpoint
takes, as a `DLRLimit.State` — the exact type `InfiniteReflection.reflPositive_of_tendsto` consumes.

All four fields come from the section above: additivity and homogeneity from `integral_add` and
`integral_const_mul` through `integrable_numFree`, positivity from the weight being strictly positive
everywhere, normalisation from `partFree / partFree`.

DERIVED: no numeral of its own; the `2` in the hypotheses is the Wilson density's ceiling. -/
noncomputable def stateFree {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) where
  toFun := fun f => specFree (φ := φ) β Λ ω (fun u => f (MassGap.GibbsSpec.splice Λ u ω))
  map_add' := by
    intro f g
    obtain ⟨CF, hCF⟩ := boxObs_bounded (Λ := Λ) ω f
    obtain ⟨CG, hCG⟩ := boxObs_bounded (Λ := Λ) ω g
    exact specFree_add hφm hφ0 hφ2 β Λ ω (boxObs_measurable ω f) hCF
      (boxObs_measurable ω g) hCG
  map_smul' := by
    intro c f
    exact specFree_smul β Λ ω c (fun u => f (MassGap.GibbsSpec.splice Λ u ω))
  nonneg' := by
    intro f hf
    exact specFree_nonneg hφm hφ0 hφ2 β Λ ω (fun u => hf _)
  one' := specFree_one hφm hφ0 hφ2 β Λ ω

#print axioms stateFree

@[simp] theorem stateFree_apply {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    stateFree hφm hφ0 hφ2 β Λ ω f
      = specFree (φ := φ) β Λ ω (fun u => f (MassGap.GibbsSpec.splice Λ u ω)) := rfl

/-- **⭐⭐ REFLECTION POSITIVITY OF THE FINITE-VOLUME STATE, IN `InfiniteReflection`'s OWN FORM.**

`ReflPositiveOn (latticeReflection τ (2p)) A (stateFree …)` — the hypothesis
`InfiniteReflection.reflPositive_of_tendsto` transports to the limit. Everything below it is proved:
the box pairing, the factorisation of the Gibbs weight, the normalisation, and the locality lift.

**⛔ `A` IS A PARAMETER, AND THAT IS NOT LAZINESS.** `reflPositive_of_tendsto` requires `A` held FIXED
across the volumes — a half-space algebra that grew with the volume would have no limit to transport
to. So the caller that chooses the exhausting sequence of boxes is the one that must choose `A`, and
`A` must be observables local to ONE fixed finite region of the positive half. Constructing it here
would pin it to a single `Λ` and defeat the purpose.

`hAloc` is locality to the box (needed because the abstract twist and `ireflConf` agree only ON `Λ`)
and `hAhalf` is the half-space reading that `ActionSplit`'s `hOloc` asks for.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`, the `0` is the sign asserted; `4` is
the dimension. -/
theorem reflPositiveOn_stateFree
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (A : Submodule ℝ C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hAloc : ∀ f ∈ A, ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
      (∀ l ∈ Λ, U l = V l) → f U = f V)
    (hAhalf : ∀ f ∈ A, ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxS τ p Λ, U i = V i) → (∀ i ∈ boxR τ p Λ, U i = V i) →
      f (MassGap.GibbsSpec.splice Λ U ω) = f (MassGap.GibbsSpec.splice Λ V ω)) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) A
      (stateFree hφm hφ0 hφ2 β Λ ω) := by
  intro f hf
  obtain ⟨CF, hCF⟩ := boxObs_bounded (Λ := Λ) ω f
  have hkey := specFree_refl_nonneg_of_local hΛ hφm hφ0 hφ2 hφc β ω
    (boxObs_measurable ω f) (hAloc f hf) (hAhalf f hf) hCF
  show (0 : ℝ) ≤ specFree (φ := φ) β Λ ω
    (fun u => ((MassGap.LatticeReflection.latticeReflection τ (2 * p)).θ f * f)
      (MassGap.GibbsSpec.splice Λ u ω))
  have heq : (fun u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ =>
      ((MassGap.LatticeReflection.latticeReflection τ (2 * p)).θ f * f)
        (MassGap.GibbsSpec.splice Λ u ω))
      = fun u => f (MassGap.GibbsSpec.splice Λ u ω)
          * f (MassGap.LatticeReflection.ireflConf τ (2 * p)
                (MassGap.GibbsSpec.splice Λ u ω)) := by
    funext u
    exact mul_comm _ _
  rw [heq]
  exact hkey

#print axioms reflPositiveOn_stateFree

/-- **⭐⭐ CHAIN B'S ENDPOINT, CONDITIONAL ON CONVERGENCE ALONE.**

Reflection positivity of the INFINITE-VOLUME state, from a family of reflection-stable boxes whose
free-boundary states converge. Every other hypothesis is discharged inside: the box pairing, the
Osterwalder–Seiler split, the covariance of the half-action, the plane weight, the bound, the
measurability, the normalisation and the locality lift.

**⛔ WHAT THIS DOES AND DOES NOT SAY.** It does NOT construct the limit state and does not prove any
sequence converges. `htend` is the whole remaining obligation on this route, and it is real analysis:
the free-boundary states of an exhausting sequence must converge on the fixed algebra `A`. What the
theorem buys is that NOTHING ELSE is outstanding — no second positivity assumption, no axiom, no
hypothesis on the filter beyond `NeBot`.

`A` is held FIXED across the volumes, which is what makes the statement usable and is why `hAloc` is
quantified over the family: observables local to one fixed finite region of the positive half are
local to every box that contains it.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`; `4` is the dimension. -/
theorem reflPositive_limit_of_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot] (τ : Fin 4) (p : ℤ)
    (box : ι → Finset MassGap.InfiniteLattice.ILink)
    (hbox : ∀ i, ∀ lk ∈ box i, ireflLink τ (2 * p) lk ∈ box i)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (A : Submodule ℝ C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hAloc : ∀ i, ∀ f ∈ A, ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
      (∀ lk ∈ box i, U lk = V lk) → f U = f V)
    (hAhalf : ∀ i, ∀ f ∈ A, ∀ U V : ↥(box i) → MassGap.SUN.SU N,
      (∀ j ∈ boxS τ p (box i), U j = V j) → (∀ j ∈ boxR τ p (box i), U j = V j) →
      f (MassGap.GibbsSpec.splice (box i) U ω) = f (MassGap.GibbsSpec.splice (box i) V ω))
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun i => stateFree hφm hφ0 hφ2 β (box i) ω f) l (nhds (ν f))) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) A ν :=
  MassGap.InfiniteReflection.reflPositive_of_tendsto htend _ A
    (Filter.Eventually.of_forall (fun i =>
      reflPositiveOn_stateFree (hbox i) hφm hφ0 hφ2 hφc β ω A (hAloc i) (hAhalf i)))

#print axioms reflPositive_limit_of_tendsto

/-- **⭐⭐⭐ REFLECTION POSITIVITY OF AN INFINITE-VOLUME STATE OF THE WILSON MEASURE ON `ℤ⁴`.**

No convergence hypothesis. **`htend` is not analysis, it is COMPACTNESS.**
`DLRLimit.exists_limit_state` supplies, for ANY `NeBot` filter and ANY family of states, an
ultrafilter refining it together with a state to which EVERY observable converges — one compact
interval per observable, which is Banach–Alaoglu done by hand. So no sequence has to be shown to
converge; the limit exists along a refinement, which is all `reflPositive_of_tendsto` ever needed.

What the caller supplies is structural, not open: a family of boxes each STABLE under the link
reflection, and a fixed submodule `A` of observables local to the boxes and reading the positive
half. The Wilson density satisfies `hφm`, `hφ0`, `hφ2` and `hφc` (`WilsonAction.wilsonDensity_*`).

**⛔ WHAT IS AND IS NOT CLAIMED.** The limit is SUBSEQUENTIAL — along an ultrafilter refining `l` —
in exactly the sense `DLRLimit` and `InfiniteVolume` are throughout. It is not claimed to be THE DLR
state, nor to be translation invariant: that is `ShiftCompat` and a separate obligation. What is
claimed is reflection positivity of the limit, on `A`, with no named axiom.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`; `4` is the dimension. -/
theorem reflPositive_limit_exists
    {ι : Type*} (l : Filter ι) [l.NeBot] (τ : Fin 4) (p : ℤ)
    (box : ι → Finset MassGap.InfiniteLattice.ILink)
    (hbox : ∀ i, ∀ lk ∈ box i, ireflLink τ (2 * p) lk ∈ box i)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (A : Submodule ℝ C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hAloc : ∀ i, ∀ f ∈ A, ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
      (∀ lk ∈ box i, U lk = V lk) → f U = f V)
    (hAhalf : ∀ i, ∀ f ∈ A, ∀ U V : ↥(box i) → MassGap.SUN.SU N,
      (∀ j ∈ boxS τ p (box i), U j = V j) → (∀ j ∈ boxR τ p (box i), U j = V j) →
      f (MassGap.GibbsSpec.splice (box i) U ω) = f (MassGap.GibbsSpec.splice (box i) V ω)) :
    ∃ (u : Ultrafilter ι) (ν : MassGap.DLRLimit.State
        (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))),
      (u : Filter ι) ≤ l ∧
      (∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
        Filter.Tendsto (fun i => stateFree hφm hφ0 hφ2 β (box i) ω f)
          (u : Filter ι) (nhds (ν f))) ∧
      MassGap.InfiniteReflection.ReflPositiveOn
        (MassGap.LatticeReflection.latticeReflection τ (2 * p)) A ν := by
  obtain ⟨u, ν, hle, htend⟩ :=
    MassGap.DLRLimit.exists_limit_state l (fun i => stateFree hφm hφ0 hφ2 β (box i) ω)
  haveI : (u : Filter ι).NeBot := u.neBot'
  exact ⟨u, ν, hle, htend,
    reflPositive_limit_of_tendsto τ p box hbox hφm hφ0 hφ2 hφc β ω A hAloc hAhalf ν htend⟩

#print axioms reflPositive_limit_exists

/-- **THE HALF-SPACE OBSERVABLES OF A FIXED REGION**, as a `Submodule ℝ C(X, ℝ)` — the type
`ReflPositiveOn` asks for.

`InfiniteLattice.localAlg` is a `Subalgebra ℝ (IConf G → ℝ)`, over RAW functions. That is the right
notion and the wrong type, which is why this exists.

DERIVED: no numeral of its own; `R₀` is the caller's fixed region and `4` is the dimension. -/
def localSubmodule (R₀ : Finset MassGap.InfiniteLattice.ILink) :
    Submodule ℝ C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ) where
  carrier := {f | ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
    (∀ lk ∈ R₀, U lk = V lk) → f U = f V}
  add_mem' := by
    intro f g hf hg U V h
    show f U + g U = f V + g V
    rw [hf U V h, hg U V h]
  zero_mem' := by intro U V _; rfl
  smul_mem' := by
    intro c f hf U V h
    show c * f U = c * f V
    rw [hf U V h]

theorem mem_localSubmodule {R₀ : Finset MassGap.InfiniteLattice.ILink}
    {f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)} :
    f ∈ localSubmodule R₀ ↔ ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
      (∀ lk ∈ R₀, U lk = V lk) → f U = f V := Iff.rfl

#print axioms localSubmodule

/-- **⭐⭐⭐ REFLECTION POSITIVITY OF AN INFINITE-VOLUME STATE, ON A GENUINE HALF-SPACE ALGEBRA.**

`reflPositive_limit_exists` with the submodule supplied rather than assumed, so the statement cannot
be satisfied by `⊥`. The caller fixes a finite region `R₀` of links lying AT OR ABOVE the plane, and
the boxes grow around it.

**⛔ THE ORDER IS THE POINT.** `R₀` is fixed FIRST and every box contains it. That is what
`reflPositive_of_tendsto` needs of a submodule held fixed across volumes, and it is why the two
hypotheses come for free: locality to the box because `R₀` is inside it, and the half-space reading
because every link of `R₀` lands in `boxS ∪ boxR`.

**⛔ AND `localSubmodule R₀` IS NOT THE HALF-SPACE ALGEBRA.**
`HalfSpaceAlgebra.halfSpaceAlg τ p` is a DIRECTED UNION over all finite supports in the positive
half; `localSubmodule R₀` is ONE fixed finite support, and positivity on it is strictly weaker.
**`reflPositive_limit_on_halfSpaceAlg` below delivers the union**, by trading the `∀ i` quantifier for
an eventual one (`InfiniteReflection.reflPositive_of_eventually_pointwise`) and choosing the fixed
region PER OBSERVABLE. What it asks of the caller in exchange is an exhaustion hypothesis on the box
family, which this statement lacks.

**⛔ AND AT `R₀ = ∅` THE SUBMODULE IS EXACTLY THE CONSTANTS.** The carrier reads `∀ U V, f U = f V`
there, and every hypothesis is vacuously satisfied. So excluding `⊥` is not enough on its own; the
content comes from `R₀` being nonempty AND from the convergence clause, which is what ties `ν` to the
Wilson measure. No declaration in this tree yet exhibits a NON-CONSTANT member of `localSubmodule`.
`halfSpaceAlg` does not have this defect — `HalfSpaceAlgebra.halfLinkObs_mem` puts `halfLinkObs l f`
in it for every link `l` of the half-space and every `f : C(G, ℝ)`, which is non-constant as soon as
`f` is — and that is a second reason to prefer the statement below.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`; `4` is the dimension. -/
theorem reflPositive_limit_on_half_space
    {ι : Type*} (l : Filter ι) [l.NeBot] (τ : Fin 4) (p : ℤ)
    (R₀ : Finset MassGap.InfiniteLattice.ILink)
    (hR₀ : ∀ lk ∈ R₀, (ireflLink τ (2 * p) lk).2 τ ≤ lk.2 τ)
    (box : ι → Finset MassGap.InfiniteLattice.ILink)
    (hsub : ∀ i, R₀ ⊆ box i)
    (hbox : ∀ i, ∀ lk ∈ box i, ireflLink τ (2 * p) lk ∈ box i)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    ∃ (u : Ultrafilter ι) (ν : MassGap.DLRLimit.State
        (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))),
      (u : Filter ι) ≤ l ∧
      (∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
        Filter.Tendsto (fun i => stateFree hφm hφ0 hφ2 β (box i) ω f)
          (u : Filter ι) (nhds (ν f))) ∧
      MassGap.InfiniteReflection.ReflPositiveOn
        (MassGap.LatticeReflection.latticeReflection τ (2 * p)) (localSubmodule R₀) ν := by
  obtain ⟨u, ν, hle, htend, hrp⟩ :=
    reflPositive_limit_exists l τ p box hbox hφm hφ0 hφ2 hφc β ω (localSubmodule R₀)
      (fun i f hf U V h => hf U V (fun lk hlk => h lk (hsub i hlk)))
      (fun i f hf U V hS hR => by
        refine hf _ _ (fun lk hlk => ?_)
        have hlΛ : lk ∈ box i := hsub i hlk
        rw [MassGap.GibbsSpec.splice_mem hlΛ, MassGap.GibbsSpec.splice_mem hlΛ]
        rcases lt_or_eq_of_le (hR₀ lk hlk) with hlt | heq
        · exact hS _ (by simp only [boxS, Finset.mem_filter, Finset.mem_univ, true_and]; exact hlt)
        · exact hR _ (by simp only [boxR, Finset.mem_filter, Finset.mem_univ, true_and]; exact heq))
  exact ⟨u, ν, hle, htend, hrp⟩

#print axioms reflPositive_limit_on_half_space

/-! ## 6′. ⭐⭐⭐ B3 on the DIRECTED UNION -/

/-- **EVERY LINK OF THE POSITIVE HALF REFLECTS TO OR BELOW ITSELF.**
`reflection_exchanges_halves` puts the image at or below the plane and membership puts the link at or
above it, so the two orderings compose. This is exactly the `hR₀` that
`reflPositive_limit_on_half_space` has to ASSUME — for a half-space support it is a theorem.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`; `4` is the dimension. -/
theorem irefl_le_self_of_posHalf (τ : Fin 4) (p : ℤ) {lk : ILink} (hlk : lk ∈ posHalf τ p) :
    (ireflLink τ (2 * p) lk).2 τ ≤ lk.2 τ := by
  have h1 : (ireflLink τ (2 * p) lk).2 τ ≤ p := reflection_exchanges_halves τ p hlk
  have h2 : p ≤ lk.2 τ := hlk
  omega

#print axioms irefl_le_self_of_posHalf

/-- **⭐⭐ REFLECTION POSITIVITY OF THE FINITE-VOLUME STATE AT ONE MEMBER OF THE DIRECTED UNION.**

`reflPositiveOn_stateFree` needs a submodule every member of which is local to the box, and
`halfSpaceAlg` is not one. But a MEMBER of `halfSpaceAlg` carries its own finite support `S`, so the
fixed region that fits it is `localSubmodule S` — chosen per observable instead of once for the whole
algebra. That is the whole of the trick.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`, the `0` is the sign asserted; `4` is
the dimension. -/
theorem stateFree_refl_nonneg_of_halfSpace_support
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (S : Finset ILink) (hS : ↑S ⊆ posHalf τ p) (hSΛ : S ⊆ Λ)
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hf : ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
      (∀ lk ∈ S, U lk = V lk) → f U = f V) :
    0 ≤ stateFree hφm hφ0 hφ2 β Λ ω
      ((MassGap.LatticeReflection.latticeReflection τ (2 * p)).θ f * f) :=
  reflPositiveOn_stateFree hΛ hφm hφ0 hφ2 hφc β ω (localSubmodule S)
    (fun g hg U V h => hg U V (fun lk hlk => h lk (hSΛ hlk)))
    (fun g hg U V hSb hRb => by
      refine hg _ _ (fun lk hlk => ?_)
      have hlΛ : lk ∈ Λ := hSΛ hlk
      rw [MassGap.GibbsSpec.splice_mem hlΛ, MassGap.GibbsSpec.splice_mem hlΛ]
      rcases lt_or_eq_of_le
          (irefl_le_self_of_posHalf τ p (hS (Finset.mem_coe.mpr hlk))) with hlt | heq
      · exact hSb _ (by simp only [boxS, Finset.mem_filter, Finset.mem_univ, true_and]; exact hlt)
      · exact hRb _ (by simp only [boxR, Finset.mem_filter, Finset.mem_univ, true_and]; exact heq))
    f hf

#print axioms stateFree_refl_nonneg_of_halfSpace_support

/-- **THE ALL-IDENTITY BOUNDARY CONDITION IS SYMMETRIC ABOUT EVERY MIRROR AT ONCE.**
`ireflConf` inverts on `τ`-links and does nothing elsewhere, and `1⁻¹ = 1`, so the constant
configuration is fixed for EVERY constant — which is what lets one boundary condition serve two
families with different mirrors.

DERIVED: the `1` is the group identity; `4` is the dimension. -/
theorem ireflConf_one (τ : Fin 4) (c : ℤ) :
    MassGap.LatticeReflection.ireflConf τ c
        (1 : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) = 1 := by
  funext l
  by_cases h : l.1 = τ <;>
    simp [MassGap.LatticeReflection.ireflConf, h]

#print axioms ireflConf_one

/-- **⭐⭐ THE HALF-SPACE ALGEBRA IS MORE THAN THE CONSTANTS, AT `SU(3)`.**

`HalfSpaceAlgebra.halfLinkObs_mem` cannot show this on its own: it is quantified over an arbitrary
`f : C(G, ℝ)`, and a constant `f` gives a constant member. What is needed is a SEPARATING function
and a pair it separates. `Re tr` is the function; `CrossingIntegration.trace_gNeg` computes
`Re tr gNeg = -1` against `Re tr 1 = 3` for the pair.

**⛔ WHY IT MATTERS.** Without it every theorem about `halfSpaceAlg` admits the reading in which the
algebra is one-dimensional and the conclusion is empty — and at `SU 0` and `SU 1` that reading is the
true one, because the group is a singleton. This rules it out at `N = 3`, which is the group Clay's
problem names. For other `N` no separating pair is constructed here.

DERIVED: the `3` is `SU(3)`'s rank and the value of `Re tr 1`; the `-1` is `trace_gNeg`'s computed
value; `4` is the dimension. -/
theorem halfSpaceAlg_has_nonconstant (τ : Fin 4) (p : ℤ) :
    ∃ F ∈ MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU 3) τ p,
      ∃ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU 3), F U ≠ F V := by
  classical
  set l₀ : MassGap.InfiniteLattice.ILink := ((0 : Fin 4), fun _ => p) with hl₀
  have hmem : l₀ ∈ MassGap.HalfSpaceAlgebra.posHalf τ p := le_refl p
  set f : C(MassGap.SUN.SU 3, ℝ) :=
    ⟨fun g => (Matrix.trace (g : Matrix (Fin 3) (Fin 3) ℂ)).re,
      Complex.continuous_re.comp continuous_subtype_val.matrix_trace⟩ with hf
  refine ⟨MassGap.HalfSpaceAlgebra.halfLinkObs l₀ f,
    MassGap.HalfSpaceAlgebra.halfLinkObs_mem τ p hmem f,
    1, (fun _ => MassGap.CrossingIntegration.gNeg), ?_⟩
  have h1 : MassGap.HalfSpaceAlgebra.halfLinkObs l₀ f
      (1 : MassGap.GibbsSpec.IConf (MassGap.SUN.SU 3)) = 3 := by
    show (Matrix.trace (((1 : MassGap.SUN.SU 3) : Matrix (Fin 3) (Fin 3) ℂ))).re = 3
    simp
  have h2 : MassGap.HalfSpaceAlgebra.halfLinkObs l₀ f
      (fun _ => MassGap.CrossingIntegration.gNeg) = -1 :=
    MassGap.CrossingIntegration.trace_gNeg
  rw [h1, h2]
  norm_num

#print axioms halfSpaceAlg_has_nonconstant

/-- **⛔⛔ NO NON-EMPTY FINITE BOX IS STABLE UNDER TWO ADJACENT MIRRORS.**

This is why the even and the odd reflection invariance cannot come from one box family, and so why
`wilson_transferData_of_common_limit` has to assume something that relates two families.

The argument is three steps and each is now a citation rather than prose.
`ReflectionShift.ireflLink_comp_succ` composes the two mirrors into ONE link shift, so a doubly
stable box is shift-stable; the orbit of any member stays inside it; and the orbit is injective
because `InfiniteShift.ishift_iterate` moves the `τ` coordinate by the step count. An infinite
injective image inside a `Finset` is the contradiction.

**⛔ WHAT THIS DOES AND DOES NOT RULE OUT.** It rules out getting both invariances from a single
FINITE-VOLUME box statement. It says nothing against some other route to odd-constant invariance of
the infinite-volume state that is not a box statement at all.

DERIVED: the `1` is the mirror separation, which is what makes the composite a single lattice step;
`4` is the dimension. -/
theorem eq_empty_of_stable_two_mirrors (τ : Fin 4) (a : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (h0 : ∀ l ∈ Λ, ireflLink τ a l ∈ Λ)
    (h1 : ∀ l ∈ Λ, ireflLink τ (a + 1) l ∈ Λ) :
    Λ = ∅ := by
  by_contra hne
  obtain ⟨l, hl⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hshift : ∀ m ∈ Λ, MassGap.InfiniteShift.ishiftLink τ m ∈ Λ := by
    intro m hm
    rw [← MassGap.ReflectionShift.ireflLink_comp_succ τ a m]
    exact h1 _ (h0 m hm)
  have horb : ∀ k : ℕ, (MassGap.InfiniteShift.ishiftLink τ)^[k] l ∈ Λ := by
    intro k
    induction k with
    | zero => simpa using hl
    | succ i ih =>
        rw [Function.iterate_succ_apply']
        exact hshift _ ih
  have hinj : Function.Injective
      (fun k : ℕ => (MassGap.InfiniteShift.ishiftLink τ)^[k] l) := by
    intro k m hkm
    have h := congrArg (fun q : MassGap.InfiniteLattice.ILink => q.2 τ) hkm
    simp only [MassGap.InfiniteShift.ishiftLink_iterate,
      MassGap.InfiniteShift.ishift_iterate] at h
    omega
  have hsub : Set.range (fun k : ℕ => (MassGap.InfiniteShift.ishiftLink τ)^[k] l)
      ⊆ (Λ : Set MassGap.InfiniteLattice.ILink) := by
    rintro x ⟨k, rfl⟩
    exact horb k
  exact (Set.infinite_range_of_injective hinj) (Λ.finite_toSet.subset hsub)

#print axioms eq_empty_of_stable_two_mirrors

/-! ### ⭐ The ODD constant's block structure — the even one with the fixed set flipped -/

/-- **THE POSITIVE HALF AT AN ARBITRARY CONSTANT** — the links the reflection moves DOWN.

`iblkS` is this at `c = 2p`. Classifying by the reflection's own action rather than by an inequality
written out by hand is what makes the three blocks DISJOINT by trichotomy, with no case split on the
link's direction, and that argument never looks at the parity of `c`.

**⛔ DISJOINTNESS IS PARITY-FREE; BEING A HALF-SPACE IS NOT.** A `τ`-link reflects about `c - 1` and
a transverse one about `c`, so they enter `ioblkS` at `2x_τ > c - 1` and `2x_τ > c`. Those two
thresholds coincide only when `2x_τ ≠ c` can be assumed — that is, only at ODD `c`. At even `c` the
gap is real: a plaquette of `ioplqPlus` can have a boundary link in `ioblkR`, and the even chain's own
locality lemma `iplqPlus_links_mem` concludes `boxS ∪ boxR` rather than `boxS` for precisely this
reason. **Any locality statement built on these blocks must carry `c` odd.**

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
def ioblkS (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Finset MassGap.InfiniteLattice.ILink :=
  Λ.filter (fun l => (ireflLink τ c l).2 τ < l.2 τ)

/-- **THE NEGATIVE HALF** — moved UP.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
def ioblkT (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Finset MassGap.InfiniteLattice.ILink :=
  Λ.filter (fun l => l.2 τ < (ireflLink τ c l).2 τ)

/-- **THE SHARED BLOCK** — not moved in the `τ` coordinate.

**⛔ ITS CONTENT FLIPS WITH THE PARITY OF `c`.** At an even constant it holds TRANSVERSE links lying
in the plane and the twist does not invert them; at an odd one it holds the AXIS links straddling the
mirror and the twist DOES (`odd_tau_fixed_iff`,
`LatticeReflection.ireflConf_inverts_fixed_axis_link`). The definition is the same either way, which
is the point of classifying by the reflection's action.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
def ioblkR (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Finset MassGap.InfiniteLattice.ILink :=
  Λ.filter (fun l => (ireflLink τ c l).2 τ = l.2 τ)

#print axioms ioblkS

/-- The three are pairwise disjoint, by trichotomy on `ℤ`.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ioblk_disjoint (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Disjoint (ioblkS τ c Λ) (ioblkT τ c Λ)
      ∧ Disjoint (ioblkS τ c Λ) (ioblkR τ c Λ)
      ∧ Disjoint (ioblkT τ c Λ) (ioblkR τ c Λ) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine Finset.disjoint_left.2 fun l h1 h2 => ?_ <;>
      simp only [ioblkS, ioblkT, ioblkR, Finset.mem_filter] at h1 h2 <;>
        omega

#print axioms ioblk_disjoint

/-- **AND THEY EXHAUST THE BOX.** Every link falls in exactly one, again by trichotomy.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ioblk_union (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    ioblkS τ c Λ ∪ ioblkT τ c Λ ∪ ioblkR τ c Λ = Λ := by
  classical
  ext l
  simp only [Finset.mem_union, ioblkS, ioblkT, ioblkR, Finset.mem_filter]
  constructor
  · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
  · intro hl
    rcases lt_trichotomy ((ireflLink τ c l).2 τ) (l.2 τ) with h | h | h
    · exact Or.inl (Or.inl ⟨hl, h⟩)
    · exact Or.inr ⟨hl, h⟩
    · exact Or.inl (Or.inr ⟨hl, h⟩)

#print axioms ioblk_union

/-- **THE REFLECTION SWAPS THE TWO HALVES**, at any constant — it is an involution, so a link moved
down has an image moved up and back again.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ireflLink_ioblkS_mem_ioblkT (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) {l : MassGap.InfiniteLattice.ILink}
    (hl : l ∈ ioblkS τ c Λ) : ireflLink τ c l ∈ ioblkT τ c Λ := by
  simp only [ioblkS, Finset.mem_filter] at hl
  simp only [ioblkT, Finset.mem_filter]
  refine ⟨hΛ l hl.1, ?_⟩
  rw [ireflLink_involutive τ c l]
  exact hl.2

#print axioms ireflLink_ioblkS_mem_ioblkT

/-- **AND BACK AGAIN.** `Finset.sum_nbij'` needs the map in both directions, and the partner above
supplies only one.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ireflLink_ioblkT_mem_ioblkS (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) {l : MassGap.InfiniteLattice.ILink}
    (hl : l ∈ ioblkT τ c Λ) : ireflLink τ c l ∈ ioblkS τ c Λ := by
  simp only [ioblkT, Finset.mem_filter] at hl
  simp only [ioblkS, Finset.mem_filter]
  refine ⟨hΛ l hl.1, ?_⟩
  rw [ireflLink_involutive τ c l]
  exact hl.2

#print axioms ireflLink_ioblkT_mem_ioblkS

/-- **⭐ A LINK OF THE SHARED BLOCK IS FIXED OUTRIGHT, NOT MERELY IN ITS `τ` COORDINATE.**

`ireflSite` touches the `τ` coordinate and nothing else, so a link the reflection leaves at the same
`τ` height is left alone entirely. True at EVERY constant — the parity enters nowhere.

This is the `hθR` every downstream pairing lemma takes: `ActionSplit.pairing_nonneg_of_local` needs
the reflection to fix the shared block pointwise before it can integrate over it.

DERIVED: the `1` is `ireflLink`'s link-length offset; `c` is the caller's constant; `4` is the
dimension. -/
theorem irefl_eq_self_of_coord_eq (τ : Fin 4) (c : ℤ)
    {l : MassGap.InfiniteLattice.ILink}
    (hcoord : (ireflLink τ c l).2 τ = l.2 τ) : ireflLink τ c l = l := by
  refine Prod.ext rfl ?_
  by_cases h : l.1 = τ
  · show (if l.1 = τ then ireflSite τ (c - 1) l.2 else ireflSite τ c l.2) = l.2
    rw [if_pos h]
    simp only [ireflLink, if_pos h, ireflSite_axis] at hcoord
    funext j
    by_cases hj : j = τ
    · subst hj
      simp only [ireflSite, Function.update_self]
      omega
    · simp [ireflSite, Function.update_of_ne hj]
  · show (if l.1 = τ then ireflSite τ (c - 1) l.2 else ireflSite τ c l.2) = l.2
    rw [if_neg h]
    simp only [ireflLink, if_neg h, ireflSite_axis] at hcoord
    funext j
    by_cases hj : j = τ
    · subst hj
      simp only [ireflSite, Function.update_self]
      omega
    · simp [ireflSite, Function.update_of_ne hj]

#print axioms irefl_eq_self_of_coord_eq

/-- The block form, which is how a caller usually has it. -/
theorem irefl_eq_self_of_mem_ioblkR (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {l : MassGap.InfiniteLattice.ILink}
    (hl : l ∈ ioblkR τ c Λ) : ireflLink τ c l = l :=
  irefl_eq_self_of_coord_eq τ c (Finset.mem_filter.mp hl).2

#print axioms irefl_eq_self_of_mem_ioblkR

/-! ### The same three blocks at the BOX SUBTYPE index -/

/-- **THE POSITIVE HALF AT THE BOX INDEX.** `ioblkS` is over `ILink`; every locality hypothesis
downstream is over `↥Λ`, so both indexings are needed. `boxS` is this at `c = 2p`.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
def oboxS (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) : Finset ↥Λ :=
  Finset.univ.filter (fun l : ↥Λ => (ireflLink τ c l.1).2 τ < l.1.2 τ)

/-- The negative half at the box index.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
def oboxT (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) : Finset ↥Λ :=
  Finset.univ.filter (fun l : ↥Λ => l.1.2 τ < (ireflLink τ c l.1).2 τ)

/-- The shared block at the box index.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
def oboxR (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) : Finset ↥Λ :=
  Finset.univ.filter (fun l : ↥Λ => (ireflLink τ c l.1).2 τ = l.1.2 τ)

#print axioms oboxS

/-- The two indexings of the positive block agree: `ioblkS` filters `Λ`, `oboxS` filters the subtype
with the same predicate.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem mem_oboxS_of_mem_ioblkS (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {l : MassGap.InfiniteLattice.ILink}
    (hl : l ∈ ioblkS τ c Λ) :
    (⟨l, (Finset.mem_filter.mp hl).1⟩ : ↥Λ) ∈ oboxS τ c Λ :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2⟩

#print axioms mem_oboxS_of_mem_ioblkS

/-- **⭐ THE BOX PERMUTATION FIXES THE SHARED BLOCK POINTWISE** — `hθR`, at the index the pairing
lemmas use.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ireflBoxPerm_eq_self_of_mem_oboxR (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) {l : ↥Λ} (hl : l ∈ oboxR τ c Λ) :
    ireflBoxPerm hΛ l = l := by
  refine Subtype.ext ?_
  rw [ireflBoxPerm_coe]
  exact irefl_eq_self_of_coord_eq τ c
    (by simpa only [oboxR, Finset.mem_filter, Finset.mem_univ, true_and] using hl)

#print axioms ireflBoxPerm_eq_self_of_mem_oboxR

/-- **AND CARRIES THE POSITIVE HALF INTO THE NEGATIVE ONE** — `hSmap`, at the box index.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ireflBoxPerm_mem_oboxT_of_mem_oboxS (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) {l : ↥Λ} (hl : l ∈ oboxS τ c Λ) :
    ireflBoxPerm hΛ l ∈ oboxT τ c Λ := by
  simp only [oboxS, Finset.mem_filter, Finset.mem_univ, true_and] at hl
  simp only [oboxT, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [ireflBoxPerm_coe, ireflLink_involutive τ c l.1]
  exact hl

#print axioms ireflBoxPerm_mem_oboxT_of_mem_oboxS

/-- **AND BACK.** The reverse membership, which the mirror bijection needs for its inverse.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ireflBoxPerm_mem_oboxS_of_mem_oboxT (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) {l : ↥Λ} (hl : l ∈ oboxT τ c Λ) :
    ireflBoxPerm hΛ l ∈ oboxS τ c Λ := by
  simp only [oboxT, Finset.mem_filter, Finset.mem_univ, true_and] at hl
  simp only [oboxS, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [ireflBoxPerm_coe, ireflLink_involutive τ c l.1]
  exact hl

#print axioms ireflBoxPerm_mem_oboxS_of_mem_oboxT

/-- **⭐ THE MIRROR BIJECTION BETWEEN THE TWO HALF-BLOCKS.**

The reflection carries the negative half onto the positive one and back, and since `ireflBoxPerm` is
an `Equiv.Perm` built from an involution, the two directions are each other's inverse with no
computation. The `ℤ⁴` counterpart of `OddLagSplit.mirrorEquivTS`.

**⛔ THIS IS ONLY THE RELABELLING.** The transport of CONFIGURATIONS carries the dagger as well —
the reflection inverts on `τ`-links — and that is what makes the transport measure-preserving only
because Haar is inversion-invariant.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
def omirrorEquivTS (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) :
    ↥(oboxT τ c Λ) ≃ ↥(oboxS τ c Λ) where
  toFun := fun l => ⟨ireflBoxPerm hΛ l.1, ireflBoxPerm_mem_oboxS_of_mem_oboxT τ c hΛ l.2⟩
  invFun := fun l => ⟨ireflBoxPerm hΛ l.1, ireflBoxPerm_mem_oboxT_of_mem_oboxS τ c hΛ l.2⟩
  left_inv := fun l => Subtype.ext (ireflBox_involutive hΛ l.1)
  right_inv := fun l => Subtype.ext (ireflBox_involutive hΛ l.1)

#print axioms omirrorEquivTS

/-- **⭐ THE MIRROR'S VARIABLE, WRITTEN AS A VARIABLE OF THE POSITIVE HALF.**

The relabelling is `omirrorEquivTS`; the twist is the dagger the reflection puts on `τ`-links — the
same `σ` that `ireflConf` carries, restricted to the mirror block. The `ℤ⁴` counterpart of
`OddLagSplit.mirrorT`.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
noncomputable def omirrorT (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ)
    (y : ↥(oboxS τ c Λ) → MassGap.SUN.SU N) : ↥(oboxT τ c Λ) → MassGap.SUN.SU N :=
  fun l => if ((l : ↥Λ) : MassGap.InfiniteLattice.ILink).1 = τ
    then (y (omirrorEquivTS τ c hΛ l))⁻¹
    else y (omirrorEquivTS τ c hΛ l)

#print axioms omirrorT

/-- **⭐⭐ THE TRANSPORT IS MEASURE-PRESERVING.**

Relabelling by a bijection of index sets and inverting on some coordinates. Haar is
inversion-invariant, so every coordinate map preserves its factor, and
`OddLagSplit.measurePreserving_relabel_twist` — abstract in both index types — assembles them.

**⛔ THE DAGGER IS THE WHOLE CONTENT.** Without inversion-invariance of Haar the negative half could
not be moved onto the positive one at all, and the odd pairing would never become two evaluations of
one function of the half.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem measurePreserving_omirrorT (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) :
    MeasureTheory.MeasurePreserving (omirrorT (N := N) τ c hΛ)
      (MassGap.ActionSplit.cvol ↥(oboxS τ c Λ) (probHaar (MassGap.SUN.SU N)))
      (MassGap.ActionSplit.cvol ↥(oboxT τ c Λ) (probHaar (MassGap.SUN.SU N))) := by
  have hσ : ∀ l : ↥(oboxT τ c Λ), MeasureTheory.MeasurePreserving
      (fun u : MassGap.SUN.SU N =>
        if ((l : ↥Λ) : MassGap.InfiniteLattice.ILink).1 = τ then u⁻¹ else u)
      (probHaar (MassGap.SUN.SU N)) (probHaar (MassGap.SUN.SU N)) := by
    intro l
    by_cases h : ((l : ↥Λ) : MassGap.InfiniteLattice.ILink).1 = τ
    · simpa [h] using
        MeasureTheory.Measure.measurePreserving_inv (probHaar (MassGap.SUN.SU N))
    · have hid : (fun u : MassGap.SUN.SU N =>
          if ((l : ↥Λ) : MassGap.InfiniteLattice.ILink).1 = τ then u⁻¹ else u) = id := by
        funext u
        simp [h]
      rw [hid]
      exact MeasureTheory.MeasurePreserving.id _
  exact MassGap.OddLagSplit.measurePreserving_relabel_twist
    (probHaar (MassGap.SUN.SU N)) (omirrorEquivTS τ c hΛ)
    (fun l u => if ((l : ↥Λ) : MassGap.InfiniteLattice.ILink).1 = τ then u⁻¹ else u) hσ

#print axioms measurePreserving_omirrorT


/-- The three box-subtype blocks are pairwise disjoint, by trichotomy on `ℤ`.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem obox_disjoint (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Disjoint (oboxR τ c Λ) (oboxS τ c Λ)
      ∧ Disjoint (oboxR τ c Λ) (oboxT τ c Λ)
      ∧ Disjoint (oboxS τ c Λ) (oboxT τ c Λ) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine Finset.disjoint_left.2 fun l h1 h2 => ?_ <;>
      simp only [oboxS, oboxT, oboxR, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2 <;>
        omega

#print axioms obox_disjoint

/-- **AND THEY COVER THE BOX.** Stated over the SUBTYPE, which is what
`OddLagSplit.integral_three_block` needs: its cover hypothesis is over the whole index type, and on
`ℤ⁴` that can only be `↥Λ` — `ILink` itself is infinite and no finite family covers it.

**⛔ THIS IS WHY THE BOX-SUBTYPE BLOCKS EXIST.** `ioblkS/T/R` over `ILink` cannot satisfy it at any
box.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem obox_cover (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (i : ↥Λ) : i ∈ oboxR τ c Λ ∨ i ∈ oboxS τ c Λ ∨ i ∈ oboxT τ c Λ := by
  simp only [oboxR, oboxS, oboxT, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases lt_trichotomy ((ireflLink τ c i.1).2 τ) (i.1.2 τ) with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

#print axioms obox_cover

/-- **⭐⭐ THE BOX INTEGRAL, AS THREE NESTED INTEGRALS OVER THE BLOCKS.**

One integral over configurations of the box, rewritten as an iterated integral over the shared
block's variables, the positive half's, and the negative half's — **with the integrand still free to
couple all three**. That last point is what distinguishes this from a product factorisation, and it
is exactly what the straddling term needs: it reads all three blocks at once, so no factor of it is a
function of one block alone.

**⛔ THERE IS NOTHING TO PROVE HERE.** `OddLagSplit.integral_three_block` is abstract in the index
type and the fibre; this supplies the instance. Its two combinatorial inputs are `obox_disjoint` and
`obox_cover`, and its index MUST be the box subtype, because the cover hypothesis quantifies over the
whole index type and `ILink` is infinite.

This is the `ℤ⁴` counterpart of `OddLagSplit.integral_oblk_three_block`, and the largest analytic
step of the odd chain — obtained without repeating any analysis.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem integral_obox_three_block (τ : Fin 4) (c : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (F : (↥Λ → MassGap.SUN.SU N) → ℝ) (hFm : Measurable F) {C : ℝ}
    (hC : ∀ U, |F U| ≤ C) :
    (∫ U, F U ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))))
      = ∫ g, (∫ x, (∫ y, F (MassGap.OddLagSplit.join3
                (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
                (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
                (obox_cover τ c Λ) g x y)
              ∂(MassGap.ActionSplit.cvol ↥(oboxT τ c Λ) (probHaar (MassGap.SUN.SU N))))
            ∂(MassGap.ActionSplit.cvol ↥(oboxS τ c Λ) (probHaar (MassGap.SUN.SU N))))
          ∂(MassGap.ActionSplit.cvol ↥(oboxR τ c Λ) (probHaar (MassGap.SUN.SU N))) :=
  MassGap.OddLagSplit.integral_three_block (probHaar (MassGap.SUN.SU N))
    (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
    (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
    (obox_cover τ c Λ) F hFm hC

#print axioms integral_obox_three_block

/-- Measurability in the third slot of `join3`, with the first two held fixed.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem measurable_obox_join3_right (τ : Fin 4) (c : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (g : ↥(oboxR τ c Λ) → MassGap.SUN.SU N)
    (x : ↥(oboxS τ c Λ) → MassGap.SUN.SU N) :
    Measurable (fun y : ↥(oboxT τ c Λ) → MassGap.SUN.SU N =>
      MassGap.OddLagSplit.join3 (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
        (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
        (obox_cover τ c Λ) g x y) :=
  (MassGap.OddLagSplit.measurable_join3 (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
      (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
      (obox_cover τ c Λ)).comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))

#print axioms measurable_obox_join3_right

/-- Measurability in the SECOND slot of `join3`, with the first and third held fixed — the sibling of
`measurable_obox_join3_right`, at the slot the positive half occupies.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem measurable_obox_join3_mid (τ : Fin 4) (c : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (g : ↥(oboxR τ c Λ) → MassGap.SUN.SU N)
    (y : ↥(oboxT τ c Λ) → MassGap.SUN.SU N) :
    Measurable (fun x : ↥(oboxS τ c Λ) → MassGap.SUN.SU N =>
      MassGap.OddLagSplit.join3 (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
        (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
        (obox_cover τ c Λ) g x y) :=
  (MassGap.OddLagSplit.measurable_join3 (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
      (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
      (obox_cover τ c Λ)).comp
    (measurable_const.prodMk (measurable_id.prodMk measurable_const))

#print axioms measurable_obox_join3_mid

/-- **⭐⭐⭐ THE ITERATED INTEGRAL, WITH BOTH HALVES ON THE POSITIVE BLOCK.**

    ∫ over the box  =  ∫_R ∫_S ∫_S

The third integral has been moved from the negative block to the positive one by the mirror
transport, so the two half-variables are INDEPENDENT DRAWS FROM THE SAME SPACE.

**⛔ THIS IS THE SHAPE THE CROSSING KERNEL TAKES.**
`CrossingIntegration.wilson_crossing_pairing_nonneg` asks for exactly
`∫_Γ ∫_Ω ∫_Ω a(x)·a(y)·exp(β·hsRe(X(g·x), X(y)))` — one integral over the shared block and two over
the same half. Getting here is what the three-block factorisation and the mirror transport are for,
and it is why the pairing becomes two evaluations of ONE function of the half rather than a coupling
of two different spaces.

The `ℤ⁴` counterpart of `OddLagSplit.integral_oblk_mirror`.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem integral_obox_mirror (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ)
    (F : (↥Λ → MassGap.SUN.SU N) → ℝ) (hFm : Measurable F) {C : ℝ}
    (hC : ∀ U, |F U| ≤ C) :
    (∫ U, F U ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))))
      = ∫ g, (∫ x, (∫ y, F (MassGap.OddLagSplit.join3
                (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
                (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
                (obox_cover τ c Λ) g x (omirrorT τ c hΛ y))
              ∂(MassGap.ActionSplit.cvol ↥(oboxS τ c Λ) (probHaar (MassGap.SUN.SU N))))
            ∂(MassGap.ActionSplit.cvol ↥(oboxS τ c Λ) (probHaar (MassGap.SUN.SU N))))
          ∂(MassGap.ActionSplit.cvol ↥(oboxR τ c Λ) (probHaar (MassGap.SUN.SU N))) := by
  rw [integral_obox_three_block τ c Λ F hFm hC]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun g => ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  exact (MassGap.ActionSplit.integral_comp_of_mp (measurePreserving_omirrorT τ c hΛ)
    (hFm.comp (measurable_obox_join3_right τ c Λ g x))).symm

#print axioms integral_obox_mirror

/-- **THE PLAQUETTES READING THE POSITIVE HALF** — those the reflection moves DOWN.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
def ioplqPlus (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Finset MassGap.GibbsSpec.IPlaq :=
  (iplqAll Λ).filter (fun q => (ireflPlaq τ c q).2 τ < q.2 τ)

/-- **AND THEIR MIRROR** — moved UP.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
def ioplqMinus (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Finset MassGap.GibbsSpec.IPlaq :=
  (iplqAll Λ).filter (fun q => q.2 τ < (ireflPlaq τ c q).2 τ)

/-- **THE PLAQUETTES WHOSE BASE IS NOT MOVED** in the `τ` coordinate.

**⛔ "STRADDLING" IS THE ODD READING ONLY.** At an EVEN constant this set is the PLANE plaquettes,
which straddle nothing — all four of their links lie in the shared block. At an odd constant there is
no plane, and the set is the axis plaquettes based one step below the mirror, which genuinely cross
it. The definition is the same; the geometry is not.

**⛔ IT IS THE ONLY PLACE THE SHARED BLOCK APPEARS**, and at an ODD constant the shared block is
axis links the twist INVERTS (`odd_tau_fixed_iff`,
`LatticeReflection.ireflConf_inverts_fixed_axis_link`). That is why the odd pairing is an integral
against a kernel: `OddLagSplit.actCrossO` is the periodic counterpart and carries the same role.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
def ioplqCross (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Finset MassGap.GibbsSpec.IPlaq :=
  (iplqAll Λ).filter (fun q => (ireflPlaq τ c q).2 τ = q.2 τ)

#print axioms ioplqPlus

/-- The three plaquette classes are pairwise disjoint, by trichotomy on `ℤ`.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ioplq_disjoint (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Disjoint (ioplqPlus τ c Λ) (ioplqMinus τ c Λ)
      ∧ Disjoint (ioplqPlus τ c Λ) (ioplqCross τ c Λ)
      ∧ Disjoint (ioplqMinus τ c Λ) (ioplqCross τ c Λ) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine Finset.disjoint_left.2 fun q h1 h2 => ?_ <;>
      simp only [ioplqPlus, ioplqMinus, ioplqCross, Finset.mem_filter] at h1 h2 <;>
        omega

#print axioms ioplq_disjoint

/-- **AND THEY EXHAUST THE ACTION'S PLAQUETTES.** `iplqAll` is the plaquette set of `wtFree`, the
FREE-BOUNDARY weight — not of `GibbsSpec.wt`, whose specification sums over `boundaryPlaqs` and for
which `plaqsIn` is provably not local (`GibbsSpec.plaqsIn_split_not_local`). That is the weight this
split plugs into, and the distinction is the whole point of `wtFree` existing.

⚠ `iplqAll` also drops the diagonal `μ = ν`. Harmless for the Wilson density, whose degenerate
holonomy is the identity; for a general `φ` it shifts the action by `φ 1` per diagonal plaquette.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ioplq_union (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    ioplqPlus τ c Λ ∪ ioplqMinus τ c Λ ∪ ioplqCross τ c Λ = iplqAll Λ := by
  classical
  ext q
  simp only [Finset.mem_union, ioplqPlus, ioplqMinus, ioplqCross, Finset.mem_filter]
  constructor
  · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
  · intro hq
    rcases lt_trichotomy ((ireflPlaq τ c q).2 τ) (q.2 τ) with h | h | h
    · exact Or.inl (Or.inl ⟨hq, h⟩)
    · exact Or.inr ⟨hq, h⟩
    · exact Or.inl (Or.inr ⟨hq, h⟩)

#print axioms ioplq_union

/-- **⭐ AT AN ODD CONSTANT EVERY STRADDLING PLAQUETTE HAS A `τ` DIRECTION.**

A TRANSVERSE plaquette reflects about `c` itself, so its base is unmoved only when `2x_τ = c` —
impossible for odd `c`. Only AXIS plaquettes, which reflect about `c - 1`, can straddle.

**⛔ THIS IS WHAT MAKES THE CROSSING WORD WELL DEFINED.** Every cross plaquette having a `τ`
direction means it has exactly ONE boundary link in the positive half — the transverse link one step
up — so the word can be indexed by the cross plaquettes themselves, one block each. At an even
constant the set is the plane plaquettes, all of whose links lie in the shared block, and no such
indexing exists.

DERIVED: the `2` and the `1` make the constant odd, which is the entire content; `4` is the
dimension. -/
theorem ioplqCross_axis (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) : q.1.1 = τ ∨ q.1.2 = τ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  simp only [ioplqCross, Finset.mem_filter] at hq
  have h := hq.2
  simp only [ireflPlaq, if_neg h1, if_neg h2, ireflSite_axis] at h
  omega

#print axioms ioplqCross_axis

/-- **⭐⭐ THE ODD ACTION SPLIT.** The action over the box's non-degenerate plaquettes is the
positive part, plus its mirror, plus the straddling part — with nothing left over.

    A = A₊ + A₋ + A_cross

**⛔ THE STRADDLING PART IS WHERE THE DIFFICULTY LIVES.** At an EVEN constant the analogous
decomposition (`actionOn_split_three`) has a PLANE part reading only the shared block, the twist acts
trivially on it, and the Gibbs weight factors as `W · h(U) · h(ΘU)` — a square. At an ODD constant the
shared block is axis links the twist INVERTS, so `A_cross` does not factor that way and its
exponential has to be integrated against the crossing kernel
(`CrossingIntegration.wilson_crossing_pairing_nonneg`), which is what needs `0 ≤ β`.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ioplq_actionOn_split {G : Type} [Group G] (φ : G → ℝ) (τ : Fin 4) (c : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (U : MassGap.GibbsSpec.IConf G) :
    MassGap.GibbsSpec.actionOn φ (iplqAll Λ) U
      = MassGap.GibbsSpec.actionOn φ (ioplqPlus τ c Λ) U
        + MassGap.GibbsSpec.actionOn φ (ioplqMinus τ c Λ) U
        + MassGap.GibbsSpec.actionOn φ (ioplqCross τ c Λ) U := by
  unfold MassGap.GibbsSpec.actionOn
  rw [← ioplq_union τ c Λ,
    Finset.sum_union (Finset.disjoint_union_left.2
      ⟨(ioplq_disjoint τ c Λ).2.1, (ioplq_disjoint τ c Λ).2.2⟩),
    Finset.sum_union (ioplq_disjoint τ c Λ).1]

#print axioms ioplq_actionOn_split

/-- **AT AN ODD CONSTANT, HEIGHT `p` IS ENOUGH TO BE IN THE POSITIVE HALF** — for a `τ`-link and a
transverse link alike.

**⛔ THIS IS WHERE THE PARITY IS LOAD-BEARING.** A `τ`-link needs `2x_τ > c - 1 = 2p - 2` and a
transverse one `2x_τ > c = 2p - 1`; between `2p-2` and `2p-1` there is no even number, so both
conditions read `x_τ ≥ p`. At an EVEN constant they separate and no single height works, which is
why the even chain's locality lemma lands in `boxS ∪ boxR` rather than `boxS`.

DERIVED: the `2` is the plane-to-constant conversion and the `1` the half-step, together making the
constant odd — which is the content; `4` is the dimension. -/
theorem ioblkS_of_le_coord (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {l : MassGap.InfiniteLattice.ILink}
    (hl : l ∈ Λ) (hp : p ≤ l.2 τ) : l ∈ ioblkS τ (2 * p - 1) Λ := by
  simp only [ioblkS, Finset.mem_filter]
  refine ⟨hl, ?_⟩
  by_cases h : l.1 = τ
  · simp only [ireflLink, if_pos h, ireflSite_axis]
    omega
  · simp only [ireflLink, if_neg h, ireflSite_axis]
    omega

#print axioms ioblkS_of_le_coord

/-- **A POSITIVE PLAQUETTE IS BASED AT HEIGHT `p` OR ABOVE**, in all three branches of `ireflPlaq`.
The axis branches use the `c - 1` offset and the transverse one uses `c`; at an odd constant both
reduce to the same cut.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem ioplqPlus_base_ge (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqPlus τ (2 * p - 1) Λ) : p ≤ q.2 τ := by
  simp only [ioplqPlus, Finset.mem_filter] at hq
  have h := hq.2
  by_cases h1 : q.1.1 = τ
  · simp only [ireflPlaq, if_pos h1, ireflSite_axis] at h
    omega
  · by_cases h2 : q.1.2 = τ
    · simp only [ireflPlaq, if_neg h1, if_pos h2, ireflSite_axis] at h
      omega
    · simp only [ireflPlaq, if_neg h1, if_neg h2, ireflSite_axis] at h
      omega

#print axioms ioplqPlus_base_ge

/-- **⭐⭐ THE POSITIVE ODD ACTION READS THE POSITIVE HALF ALONE.**

Every boundary link of a plaquette in `ioplqPlus τ (2p-1) Λ` lies in `ioblkS τ (2p-1) Λ` — **not** in
`ioblkS ∪ ioblkR`, which is the best the even chain can say (`iplqPlus_links_mem`). The shared block
does not appear in the positive action at all.

`ilinks_eq` puts the four boundary links at `x`, `ishift μ x`, `ishift ν x` and `x`, and only a shift
along `τ` moves the `τ` coordinate — so they sit at height `x_τ` or `x_τ + 1`, and
`ioplqPlus_base_ge` puts `x_τ` at `p` or above.

**⛔ ODD CONSTANT ONLY.** `ioblkS_of_le_coord` is where that is used and where it cannot be dropped.
The `ℤ⁴` counterpart of `OddLagSplit.oplaq_links_plus`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem ioplqPlus_links_mem (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqPlus τ (2 * p - 1) Λ) {l : MassGap.InfiniteLattice.ILink}
    (hl : l ∈ MassGap.GibbsSpec.ilinks q) : l ∈ ioblkS τ (2 * p - 1) Λ := by
  have hbase : p ≤ q.2 τ := ioplqPlus_base_ge τ p hq
  have hqall : q ∈ iplqAll Λ := (Finset.mem_filter.mp hq).1
  have hin : l ∈ Λ :=
    (MassGap.GibbsSpec.mem_plaqsIn.mp (mem_iplqAll.mp hqall).1) l hl
  refine ioblkS_of_le_coord τ p hin ?_
  have hshift : ∀ μ : Fin 4, p ≤ (MassGap.InfiniteLattice.ishift μ q.2) τ := by
    intro μ
    by_cases hm : τ = μ
    · subst hm
      simp only [MassGap.InfiniteLattice.ishift, Function.update_self]
      omega
    · simp only [MassGap.InfiniteLattice.ishift, Function.update_of_ne hm]
      exact hbase
  rw [MassGap.GibbsSpec.ilinks_eq] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · exact hbase
  · exact hshift q.1.1
  · exact hshift q.1.2
  · exact hbase

#print axioms ioplqPlus_links_mem

/-- **A STRADDLING PLAQUETTE SITS ONE STEP BELOW THE MIRROR.** At `c = 2p-1` the mirror is at
`p - 1/2`, and an axis plaquette's base is unmoved exactly at `x_τ = p - 1`.

DERIVED: the `2` and the `1`s are the odd constant and `ireflPlaq`'s axis offset; `4` is the
dimension. -/
theorem ioplqCross_base (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) : q.2 τ = p - 1 := by
  simp only [ioplqCross, Finset.mem_filter] at hq
  have h := hq.2
  rcases ioplqCross_axis τ p (Finset.mem_filter.mpr hq) with h1 | h2
  · simp only [ireflPlaq, if_pos h1, ireflSite_axis] at h
    omega
  · by_cases h1 : q.1.1 = τ
    · simp only [ireflPlaq, if_pos h1, ireflSite_axis] at h
      omega
    · simp only [ireflPlaq, if_neg h1, if_pos h2, ireflSite_axis] at h
      omega

#print axioms ioplqCross_base

/-- **THE POSITIVE HALF'S LINK AT A STRADDLING PLAQUETTE.** The transverse link one step above the
base — the only one of the four that lies in `ioblkS`.

The other three are: two `τ`-links at the base, which the mirror FIXES, and the transverse link at
the base, which it sends below. `ioplqCross_axis` is what guarantees a `τ` direction exists to step
along.

DERIVED: no numeral of its own; `4` is the dimension. -/
def osLinkOf (τ : Fin 4) (q : MassGap.GibbsSpec.IPlaq) : MassGap.InfiniteLattice.ILink :=
  if q.1.1 = τ then (q.1.2, MassGap.GibbsSpec.ishift q.1.1 q.2)
  else (q.1.1, MassGap.GibbsSpec.ishift q.1.2 q.2)

#print axioms osLinkOf

/-- **⭐⭐ AND IT LIES IN THE POSITIVE HALF.**

A cross plaquette is based at `p - 1` (`ioplqCross_base`), so stepping once along `τ` lands at `p`,
which `ioblkS_of_le_coord` accepts. **Exactly one of the four boundary links is in `ioblkS`**, which
is what lets the crossing word carry one block per straddling plaquette.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem osLinkOf_mem_ioblkS (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) :
    osLinkOf τ q ∈ ioblkS τ (2 * p - 1) Λ := by
  have hbase : q.2 τ = p - 1 := ioplqCross_base τ p hq
  have hqall : q ∈ iplqAll Λ := (Finset.mem_filter.mp hq).1
  have hlinks := MassGap.GibbsSpec.mem_plaqsIn.mp (mem_iplqAll.mp hqall).1
  have hstep : ∀ μ : Fin 4, μ = τ →
      (MassGap.GibbsSpec.ishift μ q.2) τ = p := by
    intro μ hμ
    subst hμ
    simp only [MassGap.GibbsSpec.ishift, Function.update_self]
    omega
  by_cases h1 : q.1.1 = τ
  · have hmem : osLinkOf τ q ∈ MassGap.GibbsSpec.ilinks q := by
      rw [MassGap.GibbsSpec.ilinks_eq]
      simp only [osLinkOf, if_pos h1]
      simp
    refine ioblkS_of_le_coord τ p (hlinks _ hmem) ?_
    simp only [osLinkOf, if_pos h1]
    rw [hstep q.1.1 h1]
  · have h2 : q.1.2 = τ := (ioplqCross_axis τ p hq).resolve_left h1
    have hmem : osLinkOf τ q ∈ MassGap.GibbsSpec.ilinks q := by
      rw [MassGap.GibbsSpec.ilinks_eq]
      simp only [osLinkOf, if_neg h1]
      simp
    refine ioblkS_of_le_coord τ p (hlinks _ hmem) ?_
    simp only [osLinkOf, if_neg h1]
    rw [hstep q.1.2 h2]

#print axioms osLinkOf_mem_ioblkS

/-- The half-link is in the box. `ioblkS` is a filter of `Λ`, so this is its first component.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem osLinkOf_mem_box (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) : osLinkOf τ q ∈ Λ :=
  (Finset.mem_filter.mp (osLinkOf_mem_ioblkS τ p hq)).1

#print axioms osLinkOf_mem_box

/-- **AND IT IS IN THE POSITIVE BLOCK AT THE BOX INDEX.** Same inequality as `ioblkS`, carried to the
subtype the mirror factorisation's integrals run over.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem osLinkOf_mem_oboxS (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) :
    (⟨osLinkOf τ q, osLinkOf_mem_box τ p hq⟩ : ↥Λ) ∈ oboxS τ (2 * p - 1) Λ :=
  mem_oboxS_of_mem_ioblkS τ (2 * p - 1) (osLinkOf_mem_ioblkS τ p hq)

#print axioms osLinkOf_mem_oboxS

/-- **⭐ ONE STRADDLING PLAQUETTE, ONE POSITIVE-HALF LINK.**

The map the crossing word is built along: each straddling plaquette contributes exactly one block,
namely the half's variable at its own `osLinkOf`. `ioplqCross_axis` and `osLinkOf_mem_ioblkS` are
what make this well defined — at an even constant there is no such map, because a plane plaquette has
no link in the positive half at all.

The `ℤ⁴` counterpart of `OddLagSplit.sIdx`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
def osIdx (τ : Fin 4) (p : ℤ) {Λ : Finset MassGap.InfiniteLattice.ILink}
    (k : ↥(ioplqCross τ (2 * p - 1) Λ)) : ↥(oboxS τ (2 * p - 1) Λ) :=
  ⟨⟨osLinkOf τ k.1, osLinkOf_mem_box τ p k.2⟩, osLinkOf_mem_oboxS τ p k.2⟩

#print axioms osIdx

/-- **⭐⭐ THE WORD THE CROSSING INTEGRATION READS.**

The direct sum, over the straddling plaquettes, of the positive half's link at each — relabelled to a
`Fin` because that is the type `CrossingIntegration.wilson_crossing_pairing_nonneg` takes for its
word `X`.

**⛔ ONE BLOCK PER STRADDLING PLAQUETTE**, and `osIdx` is what makes that indexing exist. At an even
constant there is no such word: the cross set is the plane plaquettes, none of which has a link in
the positive half.

The `ℤ⁴` counterpart of `OddLagSplit.crossWord`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension; the matrix size is
`Fintype.card (Fin N × ioplqCross)`, a count. -/
noncomputable def ocrossWord (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (u : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N) :
    Matrix (Fin (Fintype.card (Fin N × ↥(ioplqCross τ (2 * p - 1) Λ))))
      (Fin (Fintype.card (Fin N × ↥(ioplqCross τ (2 * p - 1) Λ)))) ℂ :=
  (Matrix.blockDiagonal (fun k : ↥(ioplqCross τ (2 * p - 1) Λ) =>
      ((u (osIdx τ p k) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ))).submatrix
    (Fintype.equivFin (Fin N × ↥(ioplqCross τ (2 * p - 1) Λ))).symm
    (Fintype.equivFin (Fin N × ↥(ioplqCross τ (2 * p - 1) Λ))).symm

#print axioms ocrossWord

/-- **AND ITS CROSS FORM IS THE SUM OVER THE STRADDLING PLAQUETTES.**

`OddLagSplit.hsRe_blockDiagonal_fin` is abstract in the block index and the matrix size, so this is
that lemma pointed at this family — the relabelling to `Fin` is invisible to the cross form.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem hsRe_ocrossWord (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (u v : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N) :
    MassGap.CharacterExpansion.hsRe (ocrossWord τ p u) (ocrossWord τ p v)
      = ∑ k : ↥(ioplqCross τ (2 * p - 1) Λ),
          MassGap.CharacterExpansion.hsRe
            ((u (osIdx τ p k) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
            ((v (osIdx τ p k) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) :=
  MassGap.OddLagSplit.hsRe_blockDiagonal_fin _ _

#print axioms hsRe_ocrossWord

/-- **⭐⭐ `hXinv`: THE WORD DOES NOT SEE THE PLANE GAUGE.**

`OddLagSplit.planeAct` conjugates each half-link by its own pair of shared-block variables, and
`hsRe_ocrossWord` has already reduced the cross form to a sum of per-block cross forms — so
`CrossingIntegration.hsRe_conj` absorbs the conjugation one block at a time.

This is the hypothesis `CrossingIntegration.wilson_crossing_pairing_nonneg` calls `hXinv`.

**⛔ IT HOLDS FOR ANY `A` AND `B`, AND THAT CUTS BOTH WAYS.** The invariance is a property of
conjugation, not of which straddling links the assignment picks, so it is available before the plane
assignment exists — and a mistake in that assignment could not be caught here. What the assignment
must get right is the SUM IDENTITY, where the actual straddling links appear and where a wrong choice
would show up.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem hsRe_ocrossWord_planeAct (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (A B : ↥(oboxS τ (2 * p - 1) Λ) → ↥(oboxR τ (2 * p - 1) Λ))
    (g : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (u v : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N) :
    MassGap.CharacterExpansion.hsRe
        (ocrossWord τ p (MassGap.OddLagSplit.planeAct A B g u))
        (ocrossWord τ p (MassGap.OddLagSplit.planeAct A B g v))
      = MassGap.CharacterExpansion.hsRe (ocrossWord τ p u) (ocrossWord τ p v) := by
  rw [hsRe_ocrossWord, hsRe_ocrossWord]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact MassGap.CrossingIntegration.hsRe_conj
    (g (A (osIdx τ p k))) (g (B (osIdx τ p k))) (u (osIdx τ p k)) (v (osIdx τ p k))

#print axioms hsRe_ocrossWord_planeAct

/-- **THE STRADDLING PLAQUETTE'S BASE `τ`-LINK IS IN THE BOX.** It is a boundary link of the
plaquette in both orientations of the plane — first in the list when the plane leads with `τ`, fourth
when it trails — so `GibbsSpec.mem_plaqsIn` places it in `Λ`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem baseTauLink_mem_box (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) :
    ((τ, q.2) : MassGap.InfiniteLattice.ILink) ∈ Λ := by
  have hqall : q ∈ iplqAll Λ := (Finset.mem_filter.mp hq).1
  have hlinks := MassGap.GibbsSpec.mem_plaqsIn.mp (mem_iplqAll.mp hqall).1
  refine hlinks _ ?_
  rw [MassGap.GibbsSpec.ilinks_eq]
  rcases ioplqCross_axis τ p hq with h1 | h2
  · rw [← h1]
    simp
  · rw [← h2]
    simp

#print axioms baseTauLink_mem_box

/-- **⭐ EVERY `τ`-LINK BASED AT `p - 1` IS IN THE SHARED BLOCK** at an odd constant: it reflects to
`(2p-1) - 1 - (p-1) = p - 1`, so the mirror at `p - 1/2` leaves it where it is.

**ONE INCLUSION ONLY.** That the shared block contains NOTHING ELSE is a separate statement, not
proved here; `odd_nonTau_not_fixed` is the nearest thing to it and is about `ireflLink l ≠ l` rather
than about `oboxR`.

This is the general fact; a straddling plaquette's base link is one instance of it, and the family of
boxes the limit lift runs over needs it to know its shared block is inhabited at all.

DERIVED: the `2` and the `1`s are the odd constant and `ireflLink`'s link-length offset; `4` is the
dimension. -/
theorem tauLink_mem_oboxR (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {x : MassGap.GibbsSpec.ISite}
    (hx : x τ = p - 1) (hmem : ((τ, x) : MassGap.InfiniteLattice.ILink) ∈ Λ) :
    (⟨(τ, x), hmem⟩ : ↥Λ) ∈ oboxR τ (2 * p - 1) Λ := by
  have hval : (ireflLink τ (2 * p - 1) ((τ, x) : MassGap.InfiniteLattice.ILink)).2 τ
      = 2 * p - 1 - 1 - x τ := by
    simp [ireflLink]
  simp only [oboxR, Finset.mem_filter, Finset.mem_univ, true_and, hval]
  omega

#print axioms tauLink_mem_oboxR

/-- **AND SO THE STRADDLING PLAQUETTE'S BASE `τ`-LINK IS**, since `ioplqCross_base` puts it at
`p - 1`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem baseTauLink_mem_oboxR (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) :
    (⟨(τ, q.2), baseTauLink_mem_box τ p hq⟩ : ↥Λ) ∈ oboxR τ (2 * p - 1) Λ :=
  tauLink_mem_oboxR τ p (ioplqCross_base τ p hq) (baseTauLink_mem_box τ p hq)

#print axioms baseTauLink_mem_oboxR

/-- **THE TRANSVERSE DIRECTION OF A STRADDLING PLAQUETTE** — the one that is not the axis.

The `ℤ⁴` counterpart of `OddLagSplit.cDir`, and the same definition: `ioplqCross_axis` says one of the
two plane directions is `τ`, so this picks the other.

DERIVED: `4` is the dimension; the projections are structure fields. -/
def ocDir (τ : Fin 4) (q : MassGap.GibbsSpec.IPlaq) : Fin 4 :=
  if q.1.1 = τ then q.1.2 else q.1.1

#print axioms ocDir

/-- **AND IT IS NOT THE AXIS.** Either branch: if the first direction is `τ` the second differs from
it by non-degeneracy, and otherwise the first is not `τ` by the case.

**NON-DEGENERACY IS THE WHOLE HYPOTHESIS** — no box, no constant, no reflection. The plaquette need
not lie in any `Λ`.

DERIVED: no numeral of its own; `4` is the dimension. -/
theorem ocDir_ne (τ : Fin 4) {q : MassGap.GibbsSpec.IPlaq} (hnd : q.1.1 ≠ q.1.2) :
    ocDir τ q ≠ τ := by
  show (if q.1.1 = τ then q.1.2 else q.1.1) ≠ τ
  by_cases h1 : q.1.1 = τ
  · rw [if_pos h1]
    exact fun hc => hnd (h1.trans hc.symm)
  · rw [if_neg h1]
    exact h1

#print axioms ocDir_ne

/-- **THE STRADDLING PLAQUETTE'S SECOND `τ`-LINK** — one transverse step along from the base one.

The `ℤ⁴` counterpart of `OddLagSplit.bLinkOf`. Together with `(τ, q.2)` these are the two links the
mirror fixes, and they are the plane gauge that acts on the half.

DERIVED: no numeral of its own; `4` is the dimension. -/
def obLinkOf (τ : Fin 4) (q : MassGap.GibbsSpec.IPlaq) : MassGap.InfiniteLattice.ILink :=
  (τ, MassGap.GibbsSpec.ishift (ocDir τ q) q.2)

#print axioms obLinkOf

/-- **THE MIRROR'S TRANSVERSE LINK** — the one at the base, which the reflection sends to height `p`.

The `ℤ⁴` counterpart of `OddLagSplit.tLinkOf`. **⛔ AND IT TESTS NOTHING ABOUT THE PLANE.** On the
torus `tLinkOf` tests which of the two fixed planes the plaquette sits at, because the two transverse
links exchange roles between them. `ℤ⁴` has ONE mirror, so there is nothing to test — the only case
split left is `ocDir`'s, which picks the transverse direction and is not about the reflection.

DERIVED: no numeral of its own; `4` is the dimension. -/
def otLinkOf (τ : Fin 4) (q : MassGap.GibbsSpec.IPlaq) : MassGap.InfiniteLattice.ILink :=
  (ocDir τ q, q.2)

#print axioms otLinkOf

/-- The second `τ`-link is a boundary link of the plaquette in both orientations of the plane — third
in the list when the plane leads with `τ`, second when it trails — so `GibbsSpec.mem_plaqsIn` places
it in `Λ`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem obLinkOf_mem_box (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) : obLinkOf τ q ∈ Λ := by
  have hlinks := MassGap.GibbsSpec.mem_plaqsIn.mp
    (mem_iplqAll.mp (Finset.mem_filter.mp hq).1).1
  refine hlinks _ ?_
  rw [MassGap.GibbsSpec.ilinks_eq]
  by_cases h1 : q.1.1 = τ
  · simp only [obLinkOf, ocDir, if_pos h1]
    rw [← h1]
    simp
  · have h2 : q.1.2 = τ := (ioplqCross_axis τ p hq).resolve_left h1
    simp only [obLinkOf, ocDir, if_neg h1]
    rw [← h2]
    simp

#print axioms obLinkOf_mem_box

/-- **AND THE SECOND `τ`-LINK IS ALSO IN THE SHARED BLOCK.** Its base is one TRANSVERSE step from
`q.2`, which `ishift_coord` leaves at `p - 1`, so it reflects exactly as the base one does.

DERIVED: the `2` and the `1`s are the odd constant and `ireflLink`'s link-length offset; `4` is the
dimension. -/
theorem obLinkOf_mem_oboxR (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) :
    (⟨obLinkOf τ q, obLinkOf_mem_box τ p hq⟩ : ↥Λ) ∈ oboxR τ (2 * p - 1) Λ := by
  have hbase : q.2 τ = p - 1 := ioplqCross_base τ p hq
  have hstep : (MassGap.GibbsSpec.ishift (ocDir τ q) q.2) τ = q.2 τ := by
    rw [ishift_coord, if_neg (ocDir_ne τ (mem_iplqAll.mp (Finset.mem_filter.mp hq).1).2)]
  have hval : (ireflLink τ (2 * p - 1) (obLinkOf τ q)).2 τ
      = 2 * p - 1 - 1 - (MassGap.GibbsSpec.ishift (ocDir τ q) q.2) τ := by
    simp [obLinkOf, ireflLink]
  simp only [oboxR, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hval]
  show 2 * p - 1 - 1 - (MassGap.GibbsSpec.ishift (ocDir τ q) q.2) τ
      = (MassGap.GibbsSpec.ishift (ocDir τ q) q.2) τ
  rw [hstep]
  omega

#print axioms obLinkOf_mem_oboxR

/-- The mirror's transverse link is in the box, by the same boundary-word argument — fourth in the
boundary word when `q.1.1 = τ`, first otherwise.

Like `ocDir_ne`, this needs no reflection, and the branch is on `q.1.1 = τ` rather than on which
direction is the axis: at a general plaquette of `iplqAll` neither need be `τ`, and both branches
land on a boundary link regardless. `iplqAll` membership is the whole hypothesis.

DERIVED: no numeral of its own; `4` is the dimension. -/
theorem otLinkOf_mem_box (τ : Fin 4)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ iplqAll Λ) : otLinkOf τ q ∈ Λ := by
  have hlinks := MassGap.GibbsSpec.mem_plaqsIn.mp (mem_iplqAll.mp hq).1
  refine hlinks _ ?_
  rw [MassGap.GibbsSpec.ilinks_eq]
  by_cases h1 : q.1.1 = τ
  · simp only [otLinkOf, ocDir, if_pos h1]
    simp
  · simp only [otLinkOf, ocDir, if_neg h1]
    simp

#print axioms otLinkOf_mem_box

/-- **AND IT IS IN THE NEGATIVE BLOCK.** A transverse link reflects about `c` rather than `c - 1`, so
its image sits at `(2p-1) - (p-1) = p`, strictly above its own height `p - 1`.

**⛔ THIS IS THE ASYMMETRY THAT MAKES THE ODD CONSTANT HARD.** With the three memberships above, the
straddling plaquette has a link in `S`, a link in `T`, and two in `R`, and
`ocross_links_distinct` shows the four are distinct — so its contribution is a genuine cross term
between the two halves and cannot be written as a square, which is exactly what the even constant
gives.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem otLinkOf_mem_oboxT (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) :
    (⟨otLinkOf τ q, otLinkOf_mem_box τ (Finset.mem_filter.mp hq).1⟩ : ↥Λ) ∈ oboxT τ (2 * p - 1) Λ := by
  have hbase : q.2 τ = p - 1 := ioplqCross_base τ p hq
  have hne : (otLinkOf τ q).1 ≠ τ := ocDir_ne τ (mem_iplqAll.mp (Finset.mem_filter.mp hq).1).2
  have hval : (ireflLink τ (2 * p - 1) (otLinkOf τ q)).2 τ = 2 * p - 1 - (otLinkOf τ q).2 τ :=
    image_half_is_c_sub_p τ (2 * p - 1) hne
  simp only [oboxT, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hval]
  show q.2 τ < 2 * p - 1 - q.2 τ
  omega

#print axioms otLinkOf_mem_oboxT

/-- **⭐⭐ ONE FORMULA FOR EVERY STRADDLING PLAQUETTE.**

The plaquette's `Re tr` is the cross form of its `τ`-links acting on the positive half's link, against
the mirror's link:

    Re tr (hol q U) = hsRe (U(A) · U(S) · U(B)⁻¹) (U(T))

with `A = (τ, q.2)`, `B = obLinkOf`, `S = osLinkOf`, `T = otLinkOf`. This is the identification
`CrossingIntegration` states as its remaining task and does not perform: its `hsRe (X (act g x)) (X y)`
is this, with `act` the gauge action of the two `τ`-links.

**⛔ THE RIGHT-HAND SIDE IS THE SAME IN BOTH ORIENTATIONS OF THE PLANE**, by construction of `ocDir`;
only the WORD's direction differs, and `Re tr` does not see inversion. The second branch's
`group` then `re_trace_inv` IS `OddLagSplit.re_tr_hol_swap`'s argument, inlined — `ℤ⁴` does not avoid
that work, it just does not need it as a separate canonicalisation step. What `ℤ⁴` does avoid is
`invLink`, which existed only to put the torus's TWO mirror planes into one handedness, and there is
one mirror here.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem re_tr_hol_ocross (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ)
    (U : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    (Matrix.trace ((MassGap.GibbsSpec.ihol q U : MassGap.SUN.SU N)
        : Matrix (Fin N) (Fin N) ℂ)).re
      = MassGap.CharacterExpansion.hsRe
          (((U (τ, q.2) * U (osLinkOf τ q) * (U (obLinkOf τ q))⁻¹ : MassGap.SUN.SU N)
            : Matrix (Fin N) (Fin N) ℂ))
          ((U (otLinkOf τ q) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := by
  rw [gibbs_ihol_eq, MassGap.InfiniteLattice.wilsonHol_ibd,
    MassGap.CrossingIntegration.hsRe_coe_eq, ← gibbs_ishift_eq]
  by_cases h1 : q.1.1 = τ
  · have hos : osLinkOf τ q = (q.1.2, MassGap.GibbsSpec.ishift q.1.1 q.2) := if_pos h1
    have hob : obLinkOf τ q = (τ, MassGap.GibbsSpec.ishift q.1.2 q.2) := by
      simp only [obLinkOf, ocDir, if_pos h1]
    have hot : otLinkOf τ q = (q.1.2, q.2) := by
      simp only [otLinkOf, ocDir, if_pos h1]
    rw [hos, hob, hot, ← h1]
    have hw : (U (q.1.1, q.2) * (U (q.1.2, MassGap.GibbsSpec.ishift q.1.1 q.2)
          * ((U (q.1.1, MassGap.GibbsSpec.ishift q.1.2 q.2))⁻¹ * (U (q.1.2, q.2))⁻¹))
        : MassGap.SUN.SU N)
        = U (q.1.1, q.2) * U (q.1.2, MassGap.GibbsSpec.ishift q.1.1 q.2)
            * (U (q.1.1, MassGap.GibbsSpec.ishift q.1.2 q.2))⁻¹ * (U (q.1.2, q.2))⁻¹ := by
      group
    rw [hw]
  · have h2 : q.1.2 = τ := (ioplqCross_axis τ p hq).resolve_left h1
    have hos : osLinkOf τ q = (q.1.1, MassGap.GibbsSpec.ishift q.1.2 q.2) := if_neg h1
    have hob : obLinkOf τ q = (τ, MassGap.GibbsSpec.ishift q.1.1 q.2) := by
      simp only [obLinkOf, ocDir, if_neg h1]
    have hot : otLinkOf τ q = (q.1.1, q.2) := by
      simp only [otLinkOf, ocDir, if_neg h1]
    rw [hos, hob, hot, ← h2]
    have hw : (U (q.1.1, q.2) * (U (q.1.2, MassGap.GibbsSpec.ishift q.1.1 q.2)
          * ((U (q.1.1, MassGap.GibbsSpec.ishift q.1.2 q.2))⁻¹ * (U (q.1.2, q.2))⁻¹))
        : MassGap.SUN.SU N)
        = (U (q.1.2, q.2) * U (q.1.1, MassGap.GibbsSpec.ishift q.1.2 q.2)
            * (U (q.1.2, MassGap.GibbsSpec.ishift q.1.1 q.2))⁻¹
            * (U (q.1.1, q.2))⁻¹)⁻¹ := by
      group
    rw [hw, MassGap.OddLagSplit.re_trace_inv]

#print axioms re_tr_hol_ocross

/-- The half-link's DIRECTION is the plaquette's transverse one — in both orientations, because
`ocDir` and `osLinkOf` split on the same condition into matching branches. No hypothesis needed.

DERIVED: `4` is the dimension. -/
theorem osLinkOf_dir (τ : Fin 4) (q : MassGap.GibbsSpec.IPlaq) :
    (osLinkOf τ q).1 = ocDir τ q := by
  by_cases h1 : q.1.1 = τ
  · simp only [osLinkOf, ocDir, if_pos h1]
  · simp only [osLinkOf, ocDir, if_neg h1]

#print axioms osLinkOf_dir

/-- And its BASE is one `τ` step up from the plaquette's. Here the orientation matters: the shifted
direction is `q.1.1` in one branch and `q.1.2` in the other, and `ioplqCross_axis` says whichever it
is equals `τ`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem osLinkOf_base (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) :
    (osLinkOf τ q).2 = MassGap.GibbsSpec.ishift τ q.2 := by
  unfold osLinkOf
  by_cases h1 : q.1.1 = τ
  · rw [if_pos h1, h1]
  · have h2 : q.1.2 = τ := (ioplqCross_axis τ p hq).resolve_left h1
    rw [if_neg h1, h2]

#print axioms osLinkOf_base

/-- **⭐ THE FOUR ROLES ARE FOUR DISTINCT LINKS.**

Without this, "one link in `S`, one in `T`, two in `R`" is not a count. Two mechanisms cover all six
pairs: `ocDir_ne` separates the two `τ`-links from the two transverse ones by DIRECTION, and a
one-step shift separates within each pair by BASE — the `τ`-links at `q.2` and `ishift (ocDir) q.2`,
the transverse ones at `q.2` and `ishift τ q.2`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. The one-step shift that
separates each pair lives in `osLinkOf` and `obLinkOf`, not in this statement. -/
theorem ocross_links_distinct (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) :
    ((τ, q.2) : MassGap.InfiniteLattice.ILink) ≠ obLinkOf τ q ∧
      ((τ, q.2) : MassGap.InfiniteLattice.ILink) ≠ osLinkOf τ q ∧
      ((τ, q.2) : MassGap.InfiniteLattice.ILink) ≠ otLinkOf τ q ∧
      obLinkOf τ q ≠ osLinkOf τ q ∧
      obLinkOf τ q ≠ otLinkOf τ q ∧
      osLinkOf τ q ≠ otLinkOf τ q := by
  have hdir : ocDir τ q ≠ τ := ocDir_ne τ (mem_iplqAll.mp (Finset.mem_filter.mp hq).1).2
  have hos1 : (osLinkOf τ q).1 = ocDir τ q := osLinkOf_dir τ q
  have hos2 : (osLinkOf τ q).2 = MassGap.GibbsSpec.ishift τ q.2 := osLinkOf_base τ p hq
  have hself : ∀ (μ : Fin 4) (x : MassGap.GibbsSpec.ISite),
      (MassGap.GibbsSpec.ishift μ x) μ = x μ + 1 := by
    intro μ x
    simp only [MassGap.GibbsSpec.ishift, Function.update_self]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h2 : q.2 = MassGap.GibbsSpec.ishift (ocDir τ q) q.2 := congrArg Prod.snd h
    have h3 := congrFun h2 (ocDir τ q)
    rw [hself] at h3
    omega
  · intro h
    exact hdir ((congrArg Prod.fst h).trans hos1).symm
  · intro h
    have h1 : τ = ocDir τ q := congrArg Prod.fst h
    exact hdir h1.symm
  · intro h
    exact hdir ((congrArg Prod.fst h).trans hos1).symm
  · intro h
    have h1 : τ = ocDir τ q := congrArg Prod.fst h
    exact hdir h1.symm
  · intro h
    have h2 : (osLinkOf τ q).2 = q.2 := congrArg Prod.snd h
    rw [hos2] at h2
    have h3 := congrFun h2 τ
    rw [hself] at h3
    omega

#print axioms ocross_links_distinct

/-- **THE CONVERSE OF `ioplqCross_base`.** An axis plaquette based one step below the mirror is
straddling.

Taken with `ioplqCross_base` and `ioplqCross_axis` this is a characterisation: the straddling set at
an odd constant is exactly the plaquettes with a `τ` direction based at `p - 1`. **BOTH orientations
of the plane are covered**, which matters because `ioplqCross` contains both copies of every
geometric plaquette and `sum_re_tr_ioplqCross` relies on that.

DERIVED: the `2` and the `1`s are the odd constant and `ireflPlaq`'s axis offset; `4` is the
dimension. -/
theorem mem_ioplqCross_of_base (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ iplqAll Λ) (hax : q.1.1 = τ ∨ q.1.2 = τ) (hbase : q.2 τ = p - 1) :
    q ∈ ioplqCross τ (2 * p - 1) Λ := by
  refine Finset.mem_filter.mpr ⟨hq, ?_⟩
  show (ireflPlaq τ (2 * p - 1) q).2 τ = q.2 τ
  by_cases h1 : q.1.1 = τ
  · simp only [ireflPlaq, if_pos h1, ireflSite_axis]
    omega
  · have h2 : q.1.2 = τ := hax.resolve_left h1
    simp only [ireflPlaq, if_neg h1, if_pos h2, ireflSite_axis]
    omega

#print axioms mem_ioplqCross_of_base

/-- **THE CONVERSE OF `ioplqPlus_base_ge`.** A plaquette based at or above the plane is positive — in
all three branches of `ireflPlaq`, and with no hypothesis on direction.

The axis branches reflect about `c - 1` and the transverse one about `c`; at an odd constant
`p ≤ x_τ` clears both, which is the same collapse `ioblkS_of_le_coord` performs on links.

DERIVED: the `2` and the `1` make the constant odd — which is what lets one cut serve all three
branches; `4` is the dimension. -/
theorem mem_ioplqPlus_of_base (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ iplqAll Λ) (hbase : p ≤ q.2 τ) :
    q ∈ ioplqPlus τ (2 * p - 1) Λ := by
  refine Finset.mem_filter.mpr ⟨hq, ?_⟩
  show (ireflPlaq τ (2 * p - 1) q).2 τ < q.2 τ
  by_cases h1 : q.1.1 = τ
  · simp only [ireflPlaq, if_pos h1, ireflSite_axis]
    omega
  · by_cases h2 : q.1.2 = τ
    · simp only [ireflPlaq, if_neg h1, if_pos h2, ireflSite_axis]
      omega
    · simp only [ireflPlaq, if_neg h1, if_neg h2, ireflSite_axis]
      omega

#print axioms mem_ioplqPlus_of_base

/-- The base site of the witness box's straddling plaquette — one `τ` step below the mirror at
`p - 1/2`.

CHOSEN: all four coordinates are set to `p - 1`. Only the `τ` one is forced — `ioplqCross_base` fixes
it at `p - 1` and nothing constrains the other three, so they are set equal for brevity. `4` is the
dimension. -/
def ocrossSite (p : ℤ) : MassGap.GibbsSpec.ISite := fun _ => p - 1

#print axioms ocrossSite

/-- The witness box's STRADDLING plaquette — based one step below the mirror.

DERIVED: no numeral of its own; `4` is the dimension. -/
def ocrossPlaq (τ ν : Fin 4) (p : ℤ) : MassGap.GibbsSpec.IPlaq := ((τ, ν), ocrossSite p)

/-- And its POSITIVE one — the same plane, one `τ` step up, based at `p`.

**⛔ WITHOUT THIS THE CONTROL COVERS HALF THE SPLIT.** A box holding only a straddling plaquette has
`ioplqPlus` empty, so every statement about the positive half-action is true and empty there.

DERIVED: no numeral of its own; `4` is the dimension. -/
def oplusPlaq (τ ν : Fin 4) (p : ℤ) : MassGap.GibbsSpec.IPlaq :=
  ((τ, ν), MassGap.GibbsSpec.ishift τ (ocrossSite p))

#print axioms ocrossPlaq
#print axioms oplusPlaq

/-- **THE WITNESS BOX** — the boundary links of one straddling plaquette and one positive plaquette,
closed under the reflection.

`reflClosure` supplies the closure, so the box is specified by the plaquettes it must carry rather
than by the links it happens to have.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
def ocrossBox (τ ν : Fin 4) (p : ℤ) : Finset MassGap.InfiniteLattice.ILink :=
  reflClosure τ (2 * p - 1)
    ((MassGap.GibbsSpec.ilinks (ocrossPlaq τ ν p)).toFinset ∪
      (MassGap.GibbsSpec.ilinks (oplusPlaq τ ν p)).toFinset)

#print axioms ocrossBox

/-- **AND IT IS REFLECTION-CLOSED** — the `hΛ` every lemma of the odd chain carries. One application
of `reflClosure_closed`; no case split on direction and no arithmetic.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem ocrossBox_refl_closed (τ ν : Fin 4) (p : ℤ) :
    ∀ l ∈ ocrossBox τ ν p, ireflLink τ (2 * p - 1) l ∈ ocrossBox τ ν p :=
  reflClosure_closed τ (2 * p - 1) _

#print axioms ocrossBox_refl_closed

theorem ocrossPlaq_links_mem (τ ν : Fin 4) (p : ℤ) {l : MassGap.InfiniteLattice.ILink}
    (hl : l ∈ MassGap.GibbsSpec.ilinks (ocrossPlaq τ ν p)) : l ∈ ocrossBox τ ν p :=
  subset_reflClosure τ (2 * p - 1) _
    (Finset.mem_union_left _ (List.mem_toFinset.mpr hl))

theorem oplusPlaq_links_mem (τ ν : Fin 4) (p : ℤ) {l : MassGap.InfiniteLattice.ILink}
    (hl : l ∈ MassGap.GibbsSpec.ilinks (oplusPlaq τ ν p)) : l ∈ ocrossBox τ ν p :=
  subset_reflClosure τ (2 * p - 1) _
    (Finset.mem_union_right _ (List.mem_toFinset.mpr hl))

#print axioms ocrossPlaq_links_mem
#print axioms oplusPlaq_links_mem

/-- **⭐⭐ THE STRADDLING SET IS NOT ALWAYS EMPTY.**

**⛔ WITHOUT THIS THE WHOLE CROSSING CHAIN WOULD BE VACUOUS.** `sum_re_tr_ioplqCross`,
`hsRe_ocrossWord_planeAct`, `ocrossWord` and every membership above are statements ABOUT
`ioplqCross`; each is true and empty when that set is.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem ocrossBox_cross_nonempty (τ ν : Fin 4) (hν : ν ≠ τ) (p : ℤ) :
    ocrossPlaq τ ν p ∈ ioplqCross τ (2 * p - 1) (ocrossBox τ ν p) :=
  mem_ioplqCross_of_base τ p
    (mem_iplqAll.mpr ⟨MassGap.GibbsSpec.mem_plaqsIn.mpr
      (fun l hl => ocrossPlaq_links_mem τ ν p hl), fun h => hν h.symm⟩)
    (Or.inl rfl) rfl

#print axioms ocrossBox_cross_nonempty

/-- **⭐⭐ AND NEITHER IS THE POSITIVE SET.**

**⛔ THIS IS THE HALF THE FIRST WITNESS MISSED.** With only a straddling plaquette in the box
`ioplqPlus` is empty, and then `actionOn_ioplqPlus_ojoin` reads `0 = 0` and two of
`wtFree_odd_paired`'s three factors read `exp 0 = 1` — true, and about nothing.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem ocrossBox_plus_nonempty (τ ν : Fin 4) (hν : ν ≠ τ) (p : ℤ) :
    oplusPlaq τ ν p ∈ ioplqPlus τ (2 * p - 1) (ocrossBox τ ν p) := by
  refine mem_ioplqPlus_of_base τ p
    (mem_iplqAll.mpr ⟨MassGap.GibbsSpec.mem_plaqsIn.mpr
      (fun l hl => oplusPlaq_links_mem τ ν p hl), fun h => hν h.symm⟩) ?_
  show p ≤ (MassGap.GibbsSpec.ishift τ (ocrossSite p)) τ
  simp only [MassGap.GibbsSpec.ishift, Function.update_self]
  show p ≤ (p - 1) + 1
  omega

#print axioms ocrossBox_plus_nonempty

/-- **⭐ AND THE SHARED BLOCK IS INHABITED**, which is what `sum_re_tr_ioplqCross` and
`re_tr_hol_oblock` need before they can be used at all: both take a default
`dflt : ↥(oboxR τ (2p-1) Λ)` as an explicit parameter, so a box with an empty shared block admits no
application of either.

The straddling plaquette's base `τ`-link supplies it — which is the same fact
`baseTauLink_mem_oboxR` states, read as an existence claim.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem ocrossBox_oboxR_nonempty (τ ν : Fin 4) (hν : ν ≠ τ) (p : ℤ) :
    (oboxR τ (2 * p - 1) (ocrossBox τ ν p)).Nonempty :=
  ⟨⟨(τ, (ocrossPlaq τ ν p).2), baseTauLink_mem_box τ p (ocrossBox_cross_nonempty τ ν hν p)⟩,
    baseTauLink_mem_oboxR τ p (ocrossBox_cross_nonempty τ ν hν p)⟩

#print axioms ocrossBox_oboxR_nonempty

/-- **⭐ AND SO IS THE POSITIVE BLOCK**, which is the space the crossing integration integrates over
and the domain of both half-variables.

**⛔ EMPTY THERE WOULD MAKE THE WHOLE PAIRING AN IDENTITY BETWEEN TWO FIXED REALS**: `x` and `y`
would both be the unique empty function, `oddHalfA` a constant, and `integrand_odd_eq` true and
about nothing.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem ocrossBox_oboxS_nonempty (τ ν : Fin 4) (hν : ν ≠ τ) (p : ℤ) :
    (oboxS τ (2 * p - 1) (ocrossBox τ ν p)).Nonempty :=
  ⟨⟨osLinkOf τ (ocrossPlaq τ ν p),
      osLinkOf_mem_box τ p (ocrossBox_cross_nonempty τ ν hν p)⟩,
    osLinkOf_mem_oboxS τ p (ocrossBox_cross_nonempty τ ν hν p)⟩

#print axioms ocrossBox_oboxS_nonempty

/-- **A NONEMPTY HALF-SPACE SUPPORT INSIDE THE WITNESS BOX** — the straddling plaquette's own
half-link, and nothing else.

**⛔ WITHOUT THIS THE OBSERVABLE HALF OF `integrand_odd_eq` IS UNWITNESSED.** That lemma takes a
support `S` with `↑S ⊆ posHalf τ p` and `S ⊆ Λ`; at `S = ∅` its hypothesis `hf` reads
`∀ U V, f U = f V`, so `f` is constant, `obs_ojoin_local` and `obs_ireflConf_ojoin` both read
`c = c`, and only the weight half of the identity carries content.

DERIVED: no numeral of its own; `4` is the dimension. -/
def ocrossSupp (τ ν : Fin 4) (p : ℤ) : Finset MassGap.InfiniteLattice.ILink :=
  {osLinkOf τ (ocrossPlaq τ ν p)}

#print axioms ocrossSupp

/-- And it is nonempty — which is the point of it.

DERIVED: no numeral; `4` is the dimension. -/
theorem ocrossSupp_nonempty (τ ν : Fin 4) (p : ℤ) : (ocrossSupp τ ν p).Nonempty :=
  Finset.singleton_nonempty _

#print axioms ocrossSupp_nonempty

/-- It lies in the positive half — at height exactly `p`, since `osLinkOf` steps one `τ` up from a
base at `p - 1`.

DERIVED: no numeral of its own — the odd constant enters only through the proof's appeal to
`osLinkOf_base`; `4` is the dimension. -/
theorem ocrossSupp_subset_posHalf (τ ν : Fin 4) (hν : ν ≠ τ) (p : ℤ) :
    ↑(ocrossSupp τ ν p) ⊆ posHalf τ p := by
  intro l hl
  rw [Finset.mem_coe, ocrossSupp, Finset.mem_singleton] at hl
  subst hl
  show p ≤ (osLinkOf τ (ocrossPlaq τ ν p)).2 τ
  rw [osLinkOf_base τ p (ocrossBox_cross_nonempty τ ν hν p)]
  show p ≤ (MassGap.GibbsSpec.ishift τ (ocrossSite p)) τ
  simp only [MassGap.GibbsSpec.ishift, Function.update_self]
  show p ≤ (p - 1) + 1
  omega

#print axioms ocrossSupp_subset_posHalf

/-- And it lies in the box, being a boundary link of a plaquette the box was built around.

DERIVED: no numeral of its own — the odd constant enters only through the proof; `4` is the
dimension. -/
theorem ocrossSupp_subset_box (τ ν : Fin 4) (hν : ν ≠ τ) (p : ℤ) :
    ocrossSupp τ ν p ⊆ ocrossBox τ ν p := by
  intro l hl
  rw [ocrossSupp, Finset.mem_singleton] at hl
  subst hl
  exact osLinkOf_mem_box τ p (ocrossBox_cross_nonempty τ ν hν p)

#print axioms ocrossSupp_subset_box


/-- **THE ASSIGNMENT, RUN BACKWARDS — FIRST `τ`-LINK.** A half-link at height `p` is the far
transverse link of the plaquette based one `τ` step down, whose first `τ`-link sits at that base.

**⛔ NO `if`.** `OddLagSplit.planeARaw` tests which of the torus's two straddling levels the link sits
at; `ℤ⁴` has one mirror, so there is one case. A link this map is wrong about — a `τ`-link, or one no
straddling plaquette of `Λ` owns — is caught by `oplanePick`, not by a test here.

DERIVED: no numeral of its own; `4` is the dimension. -/
def oplaneARaw (τ : Fin 4) (l : MassGap.InfiniteLattice.ILink) :
    MassGap.InfiniteLattice.ILink :=
  (τ, MassGap.GibbsSpec.iunshift τ l.2)

#print axioms oplaneARaw

/-- **AND THE SECOND** — one transverse step along, in the half-link's own direction.

DERIVED: no numeral of its own; `4` is the dimension. -/
def oplaneBRaw (τ : Fin 4) (l : MassGap.InfiniteLattice.ILink) :
    MassGap.InfiniteLattice.ILink :=
  (τ, MassGap.GibbsSpec.ishift l.1 (MassGap.GibbsSpec.iunshift τ l.2))

#print axioms oplaneBRaw

/-- **THE MEMBERSHIP GATE.** `ioblkR` is a filter of `Λ`, not of the whole lattice, so a backward
assignment cannot simply return a link — it must return one `Λ` contains and the mirror fixes. This
takes the raw link when both hold and the caller's default otherwise.

**⛔ THE DEFAULT IS NEVER THE VALUE THAT MATTERS.** `oplaneA_osIdx` and `oplaneB_osIdx` show the raw
link passes the gate at every half-link the crossing word actually reads. Everywhere else the gauge
acts by conjugation on a variable the word does not read, which is why the periodic proof could get
away with a constant.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
noncomputable def oplanePick (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    (m : MassGap.InfiniteLattice.ILink) : ↥(oboxR τ (2 * p - 1) Λ) :=
  if h : m ∈ Λ then
    (if h2 : (⟨m, h⟩ : ↥Λ) ∈ oboxR τ (2 * p - 1) Λ then ⟨⟨m, h⟩, h2⟩ else dflt)
  else dflt

#print axioms oplanePick

/-- When the gate passes, the pick is the raw link.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem oplanePick_of_mem (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    {m : MassGap.InfiniteLattice.ILink} (h : m ∈ Λ)
    (h2 : (⟨m, h⟩ : ↥Λ) ∈ oboxR τ (2 * p - 1) Λ) :
    (oplanePick τ p dflt m).1.1 = m := by
  simp only [oplanePick, dif_pos h, dif_pos h2]

#print axioms oplanePick_of_mem

/-- **⭐ THE PLANE ASSIGNMENT**, in the types `OddLagSplit.planeAct` takes: a map from the positive
half's index set to the shared block's.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
noncomputable def oplaneA (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    (l : ↥(oboxS τ (2 * p - 1) Λ)) : ↥(oboxR τ (2 * p - 1) Λ) :=
  oplanePick τ p dflt (oplaneARaw τ l.1.1)

#print axioms oplaneA

/-- The second one, likewise.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
noncomputable def oplaneB (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    (l : ↥(oboxS τ (2 * p - 1) Λ)) : ↥(oboxR τ (2 * p - 1) Λ) :=
  oplanePick τ p dflt (oplaneBRaw τ l.1.1)

#print axioms oplaneB

/-- **⭐⭐ AND IT IS RIGHT WHERE THE WORD READS IT.** At the half-link of a straddling plaquette, the
backward map returns that plaquette's own base `τ`-link — `iunshift` undoes the `τ` step `osLinkOf`
took — and `baseTauLink_mem_oboxR` clears the gate.

**⛔ THIS IS WHERE A WRONG ASSIGNMENT WOULD SHOW UP.** `hsRe_ocrossWord_planeAct` holds for ANY `A`
and `B`, so it could not catch a mistake here; this lemma and the sum identity can.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem oplaneA_osIdx (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    (k : ↥(ioplqCross τ (2 * p - 1) Λ)) :
    (oplaneA τ p dflt (osIdx τ p k)).1.1
      = ((τ, (k : MassGap.GibbsSpec.IPlaq).2) : MassGap.InfiniteLattice.ILink) := by
  have hraw : oplaneARaw τ (osIdx τ p k).1.1
      = ((τ, (k : MassGap.GibbsSpec.IPlaq).2) : MassGap.InfiniteLattice.ILink) := by
    show ((τ, MassGap.GibbsSpec.iunshift τ (osLinkOf τ (k : MassGap.GibbsSpec.IPlaq)).2)
      : MassGap.InfiniteLattice.ILink) = (τ, (k : MassGap.GibbsSpec.IPlaq).2)
    rw [osLinkOf_base τ p k.2, MassGap.GibbsSpec.iunshift_ishift]
  show (oplanePick τ p dflt (oplaneARaw τ (osIdx τ p k).1.1)).1.1 = _
  rw [hraw]
  exact oplanePick_of_mem τ p dflt (baseTauLink_mem_box τ p k.2)
    (baseTauLink_mem_oboxR τ p k.2)

#print axioms oplaneA_osIdx

/-- **AND SO IS THE SECOND.** The transverse step is taken in the half-link's own direction, which
`osLinkOf_dir` identifies with the plaquette's `ocDir` — so the result is exactly `obLinkOf`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem oplaneB_osIdx (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    (k : ↥(ioplqCross τ (2 * p - 1) Λ)) :
    (oplaneB τ p dflt (osIdx τ p k)).1.1 = obLinkOf τ (k : MassGap.GibbsSpec.IPlaq) := by
  have hraw : oplaneBRaw τ (osIdx τ p k).1.1 = obLinkOf τ (k : MassGap.GibbsSpec.IPlaq) := by
    show ((τ, MassGap.GibbsSpec.ishift (osLinkOf τ (k : MassGap.GibbsSpec.IPlaq)).1
        (MassGap.GibbsSpec.iunshift τ (osLinkOf τ (k : MassGap.GibbsSpec.IPlaq)).2))
      : MassGap.InfiniteLattice.ILink)
      = (τ, MassGap.GibbsSpec.ishift (ocDir τ (k : MassGap.GibbsSpec.IPlaq))
          (k : MassGap.GibbsSpec.IPlaq).2)
    rw [osLinkOf_dir, osLinkOf_base τ p k.2, MassGap.GibbsSpec.iunshift_ishift]
  show (oplanePick τ p dflt (oplaneBRaw τ (osIdx τ p k).1.1)).1.1 = _
  rw [hraw]
  exact oplanePick_of_mem τ p dflt (obLinkOf_mem_box τ p k.2)
    (obLinkOf_mem_oboxR τ p k.2)

#print axioms oplaneB_osIdx

/-- **THE MIRROR CARRIES THE STRADDLING PLAQUETTE'S NEGATIVE LINK ONTO ITS POSITIVE ONE.**

Both are transverse links in the same direction, based one `τ` step apart at `p - 1` and `p`, and the
reflection about `p - 1/2` exchanges exactly those two heights. That the bases DIFFER is the content:
the mirror moves the base, and `iunshift`/`ishift` is how far. The `ℤ⁴` counterpart of
`OddLagSplit.reflLink_tLinkOf`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem ireflLink_otLinkOf (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) :
    ireflLink τ (2 * p - 1) (otLinkOf τ q) = osLinkOf τ q := by
  have hbase : q.2 τ = p - 1 := ioplqCross_base τ p hq
  have hsite : ireflSite τ (2 * p - 1) q.2 = MassGap.GibbsSpec.ishift τ q.2 := by
    show Function.update q.2 τ (2 * p - 1 - q.2 τ) = Function.update q.2 τ (q.2 τ + 1)
    have harith : 2 * p - 1 - q.2 τ = q.2 τ + 1 := by omega
    rw [harith]
  have hos : osLinkOf τ q = (ocDir τ q, MassGap.GibbsSpec.ishift τ q.2) := by
    rw [← osLinkOf_dir τ q, ← osLinkOf_base τ p hq]
  rw [hos]
  show ((ocDir τ q, if ocDir τ q = τ then ireflSite τ (2 * p - 1 - 1) q.2
      else ireflSite τ (2 * p - 1) q.2) : MassGap.InfiniteLattice.ILink)
    = (ocDir τ q, MassGap.GibbsSpec.ishift τ q.2)
  rw [if_neg (ocDir_ne τ (mem_iplqAll.mp (Finset.mem_filter.mp hq).1).2), hsite]

#print axioms ireflLink_otLinkOf

/-- The three-block configuration, named. `integral_obox_mirror` already integrates against exactly
this; giving it a name is what lets the straddling sum be stated without repeating the three
disjointness proofs and the cover.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
noncomputable def ojoin (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (g : ↥(oboxR τ c Λ) → MassGap.SUN.SU N) (x : ↥(oboxS τ c Λ) → MassGap.SUN.SU N)
    (y : ↥(oboxT τ c Λ) → MassGap.SUN.SU N) : ↥Λ → MassGap.SUN.SU N :=
  MassGap.OddLagSplit.join3 (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
    (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
    (obox_cover τ c Λ) g x y

#print axioms ojoin

/-- `ojoin` folded, for rewriting under a binder. `integral_obox_mirror` states its integrand with
`join3` spelled out, and `rw` cannot refold that under the three integral binders because the block
variables are bound there, so `simp only` does it with this.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ojoin_def (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (g : ↥(oboxR τ c Λ) → MassGap.SUN.SU N) (x : ↥(oboxS τ c Λ) → MassGap.SUN.SU N)
    (y : ↥(oboxT τ c Λ) → MassGap.SUN.SU N) :
    MassGap.OddLagSplit.join3 (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
        (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
        (obox_cover τ c Λ) g x y
      = ojoin τ c Λ g x y := rfl

#print axioms ojoin_def

theorem ojoin_mem_R (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (g : ↥(oboxR τ c Λ) → MassGap.SUN.SU N) (x : ↥(oboxS τ c Λ) → MassGap.SUN.SU N)
    (y : ↥(oboxT τ c Λ) → MassGap.SUN.SU N) {l : ↥Λ} (hl : l ∈ oboxR τ c Λ) :
    ojoin τ c Λ g x y l = g ⟨l, hl⟩ :=
  MassGap.OddLagSplit.join3_mem_R (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
    (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
    (obox_cover τ c Λ) g x y hl

theorem ojoin_mem_S (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (g : ↥(oboxR τ c Λ) → MassGap.SUN.SU N) (x : ↥(oboxS τ c Λ) → MassGap.SUN.SU N)
    (y : ↥(oboxT τ c Λ) → MassGap.SUN.SU N) {l : ↥Λ} (hl : l ∈ oboxS τ c Λ) :
    ojoin τ c Λ g x y l = x ⟨l, hl⟩ :=
  MassGap.OddLagSplit.join3_mem_S (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
    (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
    (obox_cover τ c Λ) g x y hl

theorem ojoin_mem_T (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (g : ↥(oboxR τ c Λ) → MassGap.SUN.SU N) (x : ↥(oboxS τ c Λ) → MassGap.SUN.SU N)
    (y : ↥(oboxT τ c Λ) → MassGap.SUN.SU N) {l : ↥Λ} (hl : l ∈ oboxT τ c Λ) :
    ojoin τ c Λ g x y l = y ⟨l, hl⟩ :=
  MassGap.OddLagSplit.join3_mem_T (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
    (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
    (obox_cover τ c Λ) g x y hl

#print axioms ojoin_mem_R
#print axioms ojoin_mem_S
#print axioms ojoin_mem_T

/-- **AND THE MIRROR'S VARIABLE THERE IS THE SECOND HALF-VARIABLE, UNTWISTED.** The straddling
plaquette's negative link is TRANSVERSE, so the dagger branch of `omirrorT` is not taken — the
reflection inverts only on `τ`-links.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem omirrorT_otLinkOf (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p - 1) l ∈ Λ)
    (y : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (k : ↥(ioplqCross τ (2 * p - 1) Λ)) :
    omirrorT τ (2 * p - 1) hΛ y
        ⟨⟨otLinkOf τ (k : MassGap.GibbsSpec.IPlaq), otLinkOf_mem_box τ (Finset.mem_filter.mp k.2).1⟩,
          otLinkOf_mem_oboxT τ p k.2⟩
      = y (osIdx τ p k) := by
  have hne : (otLinkOf τ (k : MassGap.GibbsSpec.IPlaq)).1 ≠ τ :=
    ocDir_ne τ (mem_iplqAll.mp (Finset.mem_filter.mp k.2).1).2
  have heq : omirrorEquivTS τ (2 * p - 1) hΛ
        ⟨⟨otLinkOf τ (k : MassGap.GibbsSpec.IPlaq), otLinkOf_mem_box τ (Finset.mem_filter.mp k.2).1⟩,
          otLinkOf_mem_oboxT τ p k.2⟩
      = osIdx τ p k :=
    Subtype.ext (Subtype.ext (ireflLink_otLinkOf τ p k.2))
  show (if (otLinkOf τ (k : MassGap.GibbsSpec.IPlaq)).1 = τ
      then (y (omirrorEquivTS τ (2 * p - 1) hΛ
        ⟨⟨otLinkOf τ (k : MassGap.GibbsSpec.IPlaq), otLinkOf_mem_box τ (Finset.mem_filter.mp k.2).1⟩,
          otLinkOf_mem_oboxT τ p k.2⟩))⁻¹
      else y (omirrorEquivTS τ (2 * p - 1) hΛ
        ⟨⟨otLinkOf τ (k : MassGap.GibbsSpec.IPlaq), otLinkOf_mem_box τ (Finset.mem_filter.mp k.2).1⟩,
          otLinkOf_mem_oboxT τ p k.2⟩)) = y (osIdx τ p k)
  rw [if_neg hne, heq]

#print axioms omirrorT_otLinkOf

/-- **⭐⭐ ONE BLOCK'S CONTRIBUTION, IN THE CROSSING INTEGRATION'S VARIABLES.**

At the configuration assembled from the three block variables, a straddling plaquette reads the cross
form of the gauge-acted positive-half variable against the mirror's — and the mirror's, transported,
IS the second half-variable.

**⛔ ALL FOUR LINKS PASS THROUGH `splice`.** On the torus the blocks filter the whole lattice and the
join is already a configuration; here they filter `Λ`, so the holonomy sees the join against a
boundary condition. Every one of the four is inside `Λ` — `baseTauLink_mem_box`, `obLinkOf_mem_box`,
`osLinkOf_mem_box`, `otLinkOf_mem_box` — so `ω` is never read and the identity is independent of it.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem re_tr_hol_oblock (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p - 1) l ∈ Λ)
    (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (g : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (x y : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (k : ↥(ioplqCross τ (2 * p - 1) Λ)) :
    (Matrix.trace ((MassGap.GibbsSpec.ihol (k : MassGap.GibbsSpec.IPlaq)
        (MassGap.GibbsSpec.splice Λ
          (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y)) ω)
        : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re
      = MassGap.CharacterExpansion.hsRe
          ((MassGap.OddLagSplit.planeAct (oplaneA τ p dflt) (oplaneB τ p dflt) g x
              (osIdx τ p k) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
          ((y (osIdx τ p k) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := by
  rw [re_tr_hol_ocross τ p k.2,
    MassGap.GibbsSpec.splice_mem (baseTauLink_mem_box τ p k.2),
    MassGap.GibbsSpec.splice_mem (osLinkOf_mem_box τ p k.2),
    MassGap.GibbsSpec.splice_mem (obLinkOf_mem_box τ p k.2),
    MassGap.GibbsSpec.splice_mem (otLinkOf_mem_box τ (Finset.mem_filter.mp k.2).1),
    ojoin_mem_R τ (2 * p - 1) Λ g x _ (baseTauLink_mem_oboxR τ p k.2),
    ojoin_mem_S τ (2 * p - 1) Λ g x _ (osLinkOf_mem_oboxS τ p k.2),
    ojoin_mem_R τ (2 * p - 1) Λ g x _ (obLinkOf_mem_oboxR τ p k.2),
    ojoin_mem_T τ (2 * p - 1) Λ g x _ (otLinkOf_mem_oboxT τ p k.2),
    omirrorT_otLinkOf τ p hΛ y k]
  have hA : (⟨⟨((τ, (k : MassGap.GibbsSpec.IPlaq).2) : MassGap.InfiniteLattice.ILink),
        baseTauLink_mem_box τ p k.2⟩, baseTauLink_mem_oboxR τ p k.2⟩
        : ↥(oboxR τ (2 * p - 1) Λ))
      = oplaneA τ p dflt (osIdx τ p k) :=
    Subtype.ext (Subtype.ext (oplaneA_osIdx τ p dflt k).symm)
  have hB : (⟨⟨obLinkOf τ (k : MassGap.GibbsSpec.IPlaq), obLinkOf_mem_box τ p k.2⟩,
        obLinkOf_mem_oboxR τ p k.2⟩ : ↥(oboxR τ (2 * p - 1) Λ))
      = oplaneB τ p dflt (osIdx τ p k) :=
    Subtype.ext (Subtype.ext (oplaneB_osIdx τ p dflt k).symm)
  rw [hA, hB]
  rfl

#print axioms re_tr_hol_oblock

/-- **⭐⭐⭐ THE WHOLE STRADDLING SUM IS ONE CROSS FORM.**

`ioplqCross` indexes the blocks directly, so the sum over the `Finset` is the sum over the block
index, and `hsRe_ocrossWord` folds it into a single `hsRe`. Both orientations of every geometric
plaquette appear and both carry the same number; the direct sum simply has the block twice.

**⛔ THIS IS THE STEP `hXinv` COULD NOT CHECK.** `hsRe_ocrossWord_planeAct` holds for any assignment;
this identity is where `oplaneA` and `oplaneB` have to be the plaquette's own `τ`-links, and a wrong
choice would fail here.

With `integral_obox_mirror` this puts the odd-constant pairing in exactly the shape
`CrossingIntegration.wilson_crossing_pairing_nonneg` takes.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem sum_re_tr_ioplqCross (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p - 1) l ∈ Λ)
    (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (g : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (x y : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N) :
    (∑ q ∈ ioplqCross τ (2 * p - 1) Λ,
        (Matrix.trace ((MassGap.GibbsSpec.ihol q
          (MassGap.GibbsSpec.splice Λ
            (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y)) ω)
          : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re)
      = MassGap.CharacterExpansion.hsRe
          (ocrossWord τ p (MassGap.OddLagSplit.planeAct
            (oplaneA τ p dflt) (oplaneB τ p dflt) g x))
          (ocrossWord τ p y) := by
  rw [← Finset.sum_coe_sort (ioplqCross τ (2 * p - 1) Λ)
    (fun q => (Matrix.trace ((MassGap.GibbsSpec.ihol q
      (MassGap.GibbsSpec.splice Λ
        (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y)) ω)
      : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re), hsRe_ocrossWord]
  exact Finset.sum_congr rfl
    (fun k _ => re_tr_hol_oblock τ p hΛ dflt ω g x y k)

#print axioms sum_re_tr_ioplqCross

/-- **EVERY COORDINATE OF THE WORD IS BOUNDED BY ONE** — `hXb`. Each is a unitary entry on a diagonal
block or `0` off one, and `OddLagSplit.entry_blockDiagonal_fin_norm_le_one` is abstract in the block
index, so the `ℤ⁴` family needs no argument of its own.

DERIVED: `1` is the bound a unitary entry carries (`SUN.unitary_entry_norm_le_one`), not a chosen
cut; the `2` and the `1` in the constant make it odd. `4` is the dimension.-/
theorem abs_coord_ocrossWord_le_one (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (c : MassGap.CharacterExpansion.Coord
      (Fintype.card (Fin N × ↥(ioplqCross τ (2 * p - 1) Λ))))
    (u : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N) :
    |MassGap.CharacterExpansion.coord c (ocrossWord τ p u)| ≤ 1 :=
  MassGap.OddLagSplit.abs_coord_le_one_of_entries
    (fun i j => MassGap.OddLagSplit.entry_blockDiagonal_fin_norm_le_one
      (fun k => u (osIdx τ p k)) i j) c

#print axioms abs_coord_ocrossWord_le_one

/-- And every entry is measurable in the half-variable — the same abstract lemma.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem measurable_entry_ocrossWord (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (i j : Fin (Fintype.card (Fin N × ↥(ioplqCross τ (2 * p - 1) Λ)))) :
    Measurable (fun u : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N =>
      ocrossWord τ p u i j) :=
  MassGap.OddLagSplit.measurable_entry_blockDiagonal_fin
    (fun (u : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
      (k : ↥(ioplqCross τ (2 * p - 1) Λ)) => u (osIdx τ p k))
    (fun _ => measurable_pi_apply _) i j

#print axioms measurable_entry_ocrossWord

/-- **AND SO IS EVERY COORDINATE** — `hXm`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem measurable_coord_ocrossWord (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (c : MassGap.CharacterExpansion.Coord
      (Fintype.card (Fin N × ↥(ioplqCross τ (2 * p - 1) Λ)))) :
    Measurable (fun u : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N =>
      MassGap.CharacterExpansion.coord c (ocrossWord τ p u)) :=
  MassGap.OddLagSplit.measurable_coord_of_entries _ (measurable_entry_ocrossWord τ p) c

#print axioms measurable_coord_ocrossWord

/-- **⭐ THE STRADDLING FACTOR, IN THE CROSSING ENGINE'S VARIABLES.**

`wilsonDensity W = 1 − (1/N)·Re tr W`, so the straddling part of the action is its own cardinality
minus `1/N` times the sum of the words' real traces — and `sum_re_tr_ioplqCross` makes that sum one
cross form.

**⛔ IT IS AN ALGEBRAIC IDENTITY AND CARRIES NO `β`.** The SIGN is what its consumer will use: because
the trace enters negatively, `e^{−β·S_cross} = e^{−β·card} · e^{(β/N)·(cross form)}`, so the exponent
reaching the kernel is `β/N` and `0 ≤ β` becomes
`CrossingIntegration.wilson_crossing_pairing_nonneg`'s `hβ`. That condition is physics, not
bookkeeping — `CrossingIntegration.NegControl.su3_kernel_nonneg_iff` shows the Wilson cross kernel
fails to be positive-semidefinite at negative coupling — but it is stated where it is used, not
here.

The `ℤ⁴` counterpart of `OddLagSplit.actCrossO_eq_trace_sum`.

DERIVED: `1` is the value of `wilsonDensity` at zero trace and the numerator of `1/N`; `N` is the
rank. Both come from `WilsonAction.wilsonDensity`, not from here. `4` is the dimension.-/
theorem iactCross_eq_trace_sum (τ : Fin 4) (c : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (U : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    MassGap.GibbsSpec.actionOn MassGap.WilsonAction.wilsonDensity (ioplqCross τ c Λ) U
      = ((ioplqCross τ c Λ).card : ℝ)
        - (1 / (N : ℝ)) * ∑ q ∈ ioplqCross τ c Λ,
            (Matrix.trace ((MassGap.GibbsSpec.ihol q U : MassGap.SUN.SU N)
              : Matrix (Fin N) (Fin N) ℂ)).re := by
  unfold MassGap.GibbsSpec.actionOn
  have hterm : ∀ q ∈ ioplqCross τ c Λ,
      MassGap.WilsonAction.wilsonDensity (MassGap.GibbsSpec.ihol q U)
        = 1 - (1 / (N : ℝ))
          * (Matrix.trace ((MassGap.GibbsSpec.ihol q U : MassGap.SUN.SU N)
              : Matrix (Fin N) (Fin N) ℂ)).re := fun q _ => rfl
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    mul_one, Finset.mul_sum]

#print axioms iactCross_eq_trace_sum

/-! ### The odd crossing structure on `ℤ⁴`, and how it differs from the torus

Everything `CrossingIntegration.wilson_crossing_pairing_nonneg` asks about the GEOMETRY is now here:
the four link roles (`(τ, q.2)`, `obLinkOf`, `osLinkOf`, `otLinkOf`), the per-plaquette identity
`re_tr_hol_ocross`, the assignment `oplaneA`/`oplaneB` with `oplaneA_osIdx`/`oplaneB_osIdx`, the word
`ocrossWord` with `hXinv` (`hsRe_ocrossWord_planeAct`), and the sum identity
`sum_re_tr_ioplqCross`. `OddLagSplit.planeAct_measurePreserving` and `measurable_uncurry_planeAct`
are abstract in `{ι κ}` and apply at these index types unchanged.

**EASIER HERE THAN ON THE TORUS.** `OddLagSplit.planeARaw` tests TWO straddling levels, `1` and `m`,
because a periodic lattice has two mirror planes. They are disjoint only when `1 ≠ m`, which is the
`2 ≤ m` hypothesis, and at `m = 1` a single link is owned by two plaquettes with different plane
links so no assignment exists at all. **`ℤ⁴` has ONE mirror**: a transverse link at height `p` is the
far link of the plaquette based at `p - 1`, `oplaneARaw` carries no case split, and there is no
analogue of `2 ≤ m`. The same collapse removes `invLink` and `uplane`, which existed only to put the
torus's two planes into one handedness. The ORIENTATION reconciliation is a separate matter and does
not collapse: `re_tr_hol_ocross` inlines it in its second branch, where
`OddLagSplit.re_tr_hol_swap`'s `group` and `re_trace_inv` reappear.

**HARDER HERE IN ONE RESPECT.** The periodic blocks filter the whole lattice, so an assignment may
return any fixed default and its membership in `oblkR` is automatic. `oboxR` filters `Λ`, so a
default must lie in `Λ`, and for a half-link that is the `osLinkOf` of no straddling plaquette OF `Λ`
the owning plaquette's `τ`-links need not be in `Λ` either. Hence `oplanePick`, which decides
membership, and a default carried as an explicit parameter — the requirement sits in the signature
rather than in a hidden nonemptiness assumption. The same layer appears in `re_tr_hol_oblock`, where
the joined configuration reaches the holonomy through `GibbsSpec.splice`.

What remains is analytic, not geometric: the Wilson density in terms of `hsRe` at `β' = β/N`, the
observable as a function of the half, the word's coordinate measurability and bound, and then the
kernel. -/

/-! ### ⛔ Why the even pairing route does not extend to the odd constant

`ActionSplit.pairing_nonneg_of_local` is the engine of the even chain, and it takes two hypotheses
the odd constant breaks. Naming them here so the next attempt does not find out by trying.

**`hσR : ∀ i ∈ R, ∀ u, σ i u = u`** — the twist acts trivially on the shared block. `σ` on a
`τ`-link is `ilinkDagger τ`, which is INVERSION, and at an odd constant the shared block is exactly
the `τ`-links straddling the mirror (`odd_tau_fixed_iff`). So `σ` inverts there rather than fixing:
`LatticeReflection.ireflConf_inverts_fixed_axis_link`. Inversion is the identity only on elements
with `g = g⁻¹`, which `SU(3)` contains but is not made of.

**`hWloc : ∀ U V, (∀ i ∈ R, U i = V i) → W U = W V`** — the weight reads `R` alone. Here
`W = e^{-βA_cross}` reads the STRADDLING plaquettes, and those touch all three blocks: a cross
plaquette `((τ,ν), x)` based at `x_τ = p-1` reads two links in `ioblkR`, one in `ioblkS` at height
`p`, and one in `ioblkT` at height `p-1`.

Neither is a technicality that a sharper statement removes; they are the geometry of a mirror that
cuts links rather than passing between them. **The odd route is
`CrossingIntegration.wilson_crossing_pairing_nonneg`**, which asks for neither: it integrates the
shared block out against a positive-semidefinite kernel instead of factoring it out as a constant,
and that is where `0 ≤ β` enters. `OddLagSplit` does not reuse the even route either, for these
reasons. -/

/-- **THE REFLECTION CARRIES THE POSITIVE PLAQUETTES ONTO THE NEGATIVE ONES.** By involutivity, as
for the links: a plaquette whose base the reflection moves down has an image whose base it moves up.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ireflPlaq_ioplqPlus_mem_ioplqMinus (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqPlus τ c Λ) : ireflPlaq τ c q ∈ ioplqMinus τ c Λ := by
  simp only [ioplqPlus, Finset.mem_filter] at hq
  simp only [ioplqMinus, Finset.mem_filter]
  refine ⟨ireflPlaq_mem_iplqAll τ c hΛ hq.1, ?_⟩
  rw [ireflPlaq_involutive τ c q]
  exact hq.2

#print axioms ireflPlaq_ioplqPlus_mem_ioplqMinus

/-- **AND BACK AGAIN**, which is what the bijection in the covariance proof needs on both sides.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ireflPlaq_ioplqMinus_mem_ioplqPlus (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqMinus τ c Λ) : ireflPlaq τ c q ∈ ioplqPlus τ c Λ := by
  simp only [ioplqMinus, Finset.mem_filter] at hq
  simp only [ioplqPlus, Finset.mem_filter]
  refine ⟨ireflPlaq_mem_iplqAll τ c hΛ hq.1, ?_⟩
  rw [ireflPlaq_involutive τ c q]
  exact hq.2

#print axioms ireflPlaq_ioplqMinus_mem_ioplqPlus

/-- **⭐⭐ THE ODD COVARIANCE: `A₊(ΘU) = A₋(U)`.**

The reflection is a bijection from the positive plaquettes to the negative ones, and on each the
mirrored holonomy is CONJUGATE to the image's, which a class function does not see. Exactly
`action_iplqPlus_ireflConf`'s argument at a free constant.

**⛔ AND THE STRADDLING TERM PAIRS WITH NOTHING.** It has an identity of its own —
`ioplqCross_actionOn_ireflConf` proves `A_cross(ΘU) = A_cross(U)` — but no identity carrying it to a
DIFFERENT block, because the reflection maps it to itself. That, with the twist inverting the axis
links it reads, is why the odd case needs `0 ≤ β` and the even case does not.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ioplqPlus_actionOn_ireflConf {G : Type} [Group G] (φ : G → ℝ)
    (hφ : ∀ g h : G, φ (g * h * g⁻¹) = φ h) (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) (U : MassGap.GibbsSpec.IConf G) :
    MassGap.GibbsSpec.actionOn φ (ioplqPlus τ c Λ) (ireflConf τ c U)
      = MassGap.GibbsSpec.actionOn φ (ioplqMinus τ c Λ) U := by
  unfold MassGap.GibbsSpec.actionOn
  refine Finset.sum_nbij' (i := fun q => ireflPlaq τ c q)
    (j := fun q => ireflPlaq τ c q)
    (fun a ha => ireflPlaq_ioplqPlus_mem_ioplqMinus τ c hΛ ha)
    (fun b hb => ireflPlaq_ioplqMinus_mem_ioplqPlus τ c hΛ hb)
    (fun a _ => ireflPlaq_involutive τ c a)
    (fun b _ => ireflPlaq_involutive τ c b)
    (fun a _ => ?_)
  obtain ⟨g, hg⟩ := ihol_ireflConf τ c a U
  rw [gibbs_ihol_eq, gibbs_ihol_eq, hg, hφ]

#print axioms ioplqPlus_actionOn_ireflConf

/-- **THE STRADDLING PLAQUETTES ARE MAPPED TO THEMSELVES.** A base the reflection does not move stays
unmoved under the image, by involutivity.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ireflPlaq_ioplqCross_mem_ioplqCross (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ c Λ) : ireflPlaq τ c q ∈ ioplqCross τ c Λ := by
  simp only [ioplqCross, Finset.mem_filter] at hq
  simp only [ioplqCross, Finset.mem_filter]
  refine ⟨ireflPlaq_mem_iplqAll τ c hΛ hq.1, ?_⟩
  rw [ireflPlaq_involutive τ c q]
  exact hq.2.symm

#print axioms ireflPlaq_ioplqCross_mem_ioplqCross

/-- **⭐ THE STRADDLING ACTION DOES NOT SEE THE REFLECTION.** Same bijection argument as the
covariance, with `ioplqCross` mapped to itself instead of to a mirror partner.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ioplqCross_actionOn_ireflConf {G : Type} [Group G] (φ : G → ℝ)
    (hφ : ∀ g h : G, φ (g * h * g⁻¹) = φ h) (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) (U : MassGap.GibbsSpec.IConf G) :
    MassGap.GibbsSpec.actionOn φ (ioplqCross τ c Λ) (ireflConf τ c U)
      = MassGap.GibbsSpec.actionOn φ (ioplqCross τ c Λ) U := by
  unfold MassGap.GibbsSpec.actionOn
  refine Finset.sum_nbij' (i := fun q => ireflPlaq τ c q)
    (j := fun q => ireflPlaq τ c q)
    (fun a ha => ireflPlaq_ioplqCross_mem_ioplqCross τ c hΛ ha)
    (fun b hb => ireflPlaq_ioplqCross_mem_ioplqCross τ c hΛ hb)
    (fun a _ => ireflPlaq_involutive τ c a)
    (fun b _ => ireflPlaq_involutive τ c b)
    (fun a _ => ?_)
  obtain ⟨g, hg⟩ := ihol_ireflConf τ c a U
  rw [gibbs_ihol_eq, gibbs_ihol_eq, hg, hφ]

#print axioms ioplqCross_actionOn_ireflConf

/-- **AND THE MIRROR: `A₋(ΘU) = A₊(U)`.** The same bijection with the two block memberships swapped.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ioplqMinus_actionOn_ireflConf {G : Type} [Group G] (φ : G → ℝ)
    (hφ : ∀ g h : G, φ (g * h * g⁻¹) = φ h) (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) (U : MassGap.GibbsSpec.IConf G) :
    MassGap.GibbsSpec.actionOn φ (ioplqMinus τ c Λ) (ireflConf τ c U)
      = MassGap.GibbsSpec.actionOn φ (ioplqPlus τ c Λ) U := by
  unfold MassGap.GibbsSpec.actionOn
  refine Finset.sum_nbij' (i := fun q => ireflPlaq τ c q)
    (j := fun q => ireflPlaq τ c q)
    (fun a ha => ireflPlaq_ioplqMinus_mem_ioplqPlus τ c hΛ ha)
    (fun b hb => ireflPlaq_ioplqPlus_mem_ioplqMinus τ c hΛ hb)
    (fun a _ => ireflPlaq_involutive τ c a)
    (fun b _ => ireflPlaq_involutive τ c b)
    (fun a _ => ?_)
  obtain ⟨g, hg⟩ := ihol_ireflConf τ c a U
  rw [gibbs_ihol_eq, gibbs_ihol_eq, hg, hφ]

#print axioms ioplqMinus_actionOn_ireflConf

/-- **⭐⭐ THE ODD SPLIT, IN THE FORM THE PAIRING ARGUMENT CONSUMES.**

    A(U) = A₊(U) + A₊(ΘU) + A_cross(U)

— the SAME `A₊` on both of the first two summands, which is what exponentiates to
`e^{-βA(U)} = h(U) · h(ΘU) · W(U)` with `h = e^{-βA₊}` and `W = e^{-βA_cross}`. The `ℤ⁴`
counterpart of `OddLagSplit.action_eq_split_odd`.

**⛔ WHAT IS NOT WORTH STATING.** That the whole action is reflection-invariant is already
`action_iplqAll_ireflConf`, at a free constant, and re-deriving it through this partition adds
nothing and produces a less usable normal form. The content here is the PAIRED shape, and it comes
from `ioplqPlus_actionOn_ireflConf` — which whole-action invariance does not imply.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem iodd_action_paired {G : Type} [Group G] (φ : G → ℝ)
    (hφ : ∀ g h : G, φ (g * h * g⁻¹) = φ h) (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) (U : MassGap.GibbsSpec.IConf G) :
    MassGap.GibbsSpec.actionOn φ (iplqAll Λ) U
      = MassGap.GibbsSpec.actionOn φ (ioplqPlus τ c Λ) U
        + MassGap.GibbsSpec.actionOn φ (ioplqPlus τ c Λ) (ireflConf τ c U)
        + MassGap.GibbsSpec.actionOn φ (ioplqCross τ c Λ) U := by
  rw [ioplq_actionOn_split φ τ c Λ U, ioplqPlus_actionOn_ireflConf φ hφ τ c hΛ U]

#print axioms iodd_action_paired

/-- **⭐⭐ THE BOLTZMANN WEIGHT IN PAIRED FORM.**

    Wᵧᵣᶒᵣ = h(U) · h(ΘU) · W_cross(U),   h = e^{−βA₊},  W_cross = e^{−βA_cross}

`iodd_action_paired` splits the action three ways; exponentiating turns that sum into this product,
which is the shape `CrossingIntegration.wilson_crossing_pairing_nonneg` consumes.

**⛔ THIS IS WHERE THE ODD CASE PARTS FROM THE EVEN ONE.** At an EVEN constant the third factor reads
the shared block alone, so it comes out of both inner integrals and the pairing is a SQUARE. At an
ODD constant `A_cross` sums over plaquettes touching all three blocks (`otLinkOf_mem_oboxT` beside
`osLinkOf_mem_oboxS`), so `W_cross` cannot be factored out and the pairing is an integral against a
kernel — which is exactly why `0 ≤ β` becomes unavoidable.

The `ℤ⁴` counterpart of `OddLagSplit.boltz_eq_paired_cross`.

DERIVED: no numeral of its own; `c` is the caller's reflection constant and `4` is the dimension. -/
theorem wtFree_odd_paired {G : Type} [Group G] (φ : G → ℝ)
    (hφ : ∀ g h : G, φ (g * h * g⁻¹) = φ h) (τ : Fin 4) (c : ℤ) (β : ℝ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ)
    (ω : MassGap.GibbsSpec.IConf G) (u : MassGap.GibbsSpec.VConf G Λ) :
    wtFree φ β Λ ω u
      = Real.exp (-β * MassGap.GibbsSpec.actionOn φ (ioplqPlus τ c Λ)
            (MassGap.GibbsSpec.splice Λ u ω))
        * Real.exp (-β * MassGap.GibbsSpec.actionOn φ (ioplqPlus τ c Λ)
            (MassGap.LatticeReflection.ireflConf τ c (MassGap.GibbsSpec.splice Λ u ω)))
        * Real.exp (-β * MassGap.GibbsSpec.actionOn φ (ioplqCross τ c Λ)
            (MassGap.GibbsSpec.splice Λ u ω)) := by
  have hsum : ∀ a b d : ℝ, -β * (a + b + d) = -β * a + -β * b + -β * d := by
    intro a b d
    ring
  show Real.exp (-β * MassGap.GibbsSpec.actionOn φ (iplqAll Λ)
      (MassGap.GibbsSpec.splice Λ u ω)) = _
  rw [iodd_action_paired φ hφ τ c hΛ (MassGap.GibbsSpec.splice Λ u ω), hsum,
    Real.exp_add, Real.exp_add]

#print axioms wtFree_odd_paired

/-- **⭐⭐ THE POSITIVE HALF-ACTION IS A FUNCTION OF THE POSITIVE HALF ALONE.**

Change the shared block and the mirror block however you like; the positive part of the action does
not move. `ioplqPlus_links_mem` is the whole content — every boundary link of a positive plaquette is
in `ioblkS`, **`S` only and not `S ∪ R`**, which is where the odd constant is SHARPER than the even
one and is what makes this true at all.

This is what lets `h(U) = e^{−βA₊(U)}` in `wtFree_odd_paired` be the `a : Ω → ℝ` that
`CrossingIntegration.wilson_crossing_pairing_nonneg` takes: a function of the half, not of the whole
configuration.

The `ℤ⁴` counterpart of `OddLagSplit.actPlusO_local`.

DERIVED: the `2` and the `1` make the constant odd — which is what collapses the two locality
thresholds into one; `4` is the dimension. -/
theorem actionOn_ioplqPlus_ojoin (φ : MassGap.SUN.SU N → ℝ) (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (g g' : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (x : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (y y' : ↥(oboxT τ (2 * p - 1) Λ) → MassGap.SUN.SU N) :
    MassGap.GibbsSpec.actionOn φ (ioplqPlus τ (2 * p - 1) Λ)
        (MassGap.GibbsSpec.splice Λ (ojoin τ (2 * p - 1) Λ g x y) ω)
      = MassGap.GibbsSpec.actionOn φ (ioplqPlus τ (2 * p - 1) Λ)
        (MassGap.GibbsSpec.splice Λ (ojoin τ (2 * p - 1) Λ g' x y') ω) := by
  refine MassGap.GibbsSpec.actionOn_congr φ _ _ _ (fun q hq l hl => ?_)
  have hS : l ∈ ioblkS τ (2 * p - 1) Λ := ioplqPlus_links_mem τ p hq hl
  have hlΛ : l ∈ Λ := (Finset.mem_filter.mp hS).1
  rw [MassGap.GibbsSpec.splice_mem hlΛ, MassGap.GibbsSpec.splice_mem hlΛ,
    ojoin_mem_S τ (2 * p - 1) Λ g x y (mem_oboxS_of_mem_ioblkS τ (2 * p - 1) hS),
    ojoin_mem_S τ (2 * p - 1) Λ g' x y' (mem_oboxS_of_mem_ioblkS τ (2 * p - 1) hS)]

#print axioms actionOn_ioplqPlus_ojoin

/-- **⭐⭐⭐ AND THE MIRROR FACTOR IS THE SAME FUNCTION AT THE SECOND HALF-VARIABLE.**

`wtFree_odd_paired` writes the weight as `h(U) · h(ΘU) · W_cross(U)`. `actionOn_ioplqPlus_ojoin` makes
the first factor a function of `x` alone; this makes the second the same function of `y`.

**⛔ THE TWO DAGGERS CANCEL, AND NOTHING ELSE IS NEEDED.** `ireflConf` inverts on `τ`-links and
`omirrorT` carries the same dagger, so on the positive block the reflected configuration reads `y`
outright — `inv_inv`, with no appeal to conjugation invariance of `φ` and no trace identity. Off the
`τ`-links neither inverts and the two agree directly.

**THIS IS WHAT MAKES THE PAIRING TWO EVALUATIONS OF ONE FUNCTION.** Both inner integrals now run over
`oboxS` against the same measure and read the same `a : Ω → ℝ`, which is the shape
`CrossingIntegration.wilson_crossing_pairing_nonneg` consumes. Without the dagger on `omirrorT` the
negative half could not be moved onto the positive one at all.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem ireflConf_ojoin_eq_on_ioblkS (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p - 1) l ∈ Λ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (g g' : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (x y : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (y' : ↥(oboxT τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    {l : MassGap.InfiniteLattice.ILink} (hS : l ∈ ioblkS τ (2 * p - 1) Λ) :
    MassGap.LatticeReflection.ireflConf τ (2 * p - 1)
        (MassGap.GibbsSpec.splice Λ
          (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y)) ω) l
      = MassGap.GibbsSpec.splice Λ (ojoin τ (2 * p - 1) Λ g' y y') ω l := by
  have hlΛ : l ∈ Λ := (Finset.mem_filter.mp hS).1
  have hlS : (⟨l, hlΛ⟩ : ↥Λ) ∈ oboxS τ (2 * p - 1) Λ :=
    mem_oboxS_of_mem_ioblkS τ (2 * p - 1) hS
  have hrΛ : ireflLink τ (2 * p - 1) l ∈ Λ := hΛ l hlΛ
  have hrT : (⟨ireflLink τ (2 * p - 1) l, hrΛ⟩ : ↥Λ) ∈ oboxT τ (2 * p - 1) Λ :=
    ireflBoxPerm_mem_oboxT_of_mem_oboxS τ (2 * p - 1) hΛ hlS
  have heq : omirrorEquivTS τ (2 * p - 1) hΛ
        ⟨⟨ireflLink τ (2 * p - 1) l, hrΛ⟩, hrT⟩
      = ⟨⟨l, hlΛ⟩, hlS⟩ :=
    Subtype.ext (Subtype.ext (MassGap.LatticeReflection.ireflLink_involutive τ (2 * p - 1) l))
  have hmir : omirrorT τ (2 * p - 1) hΛ y ⟨⟨ireflLink τ (2 * p - 1) l, hrΛ⟩, hrT⟩
      = if l.1 = τ then (y ⟨⟨l, hlΛ⟩, hlS⟩)⁻¹ else y ⟨⟨l, hlΛ⟩, hlS⟩ := by
    simp only [omirrorT, MassGap.LatticeReflection.ireflLink_fst, heq]
  simp only [MassGap.LatticeReflection.ireflConf]
  rw [MassGap.GibbsSpec.splice_mem hlΛ,
    ojoin_mem_S τ (2 * p - 1) Λ g' y y' hlS,
    MassGap.GibbsSpec.splice_mem hrΛ,
    ojoin_mem_T τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y) hrT,
    hmir]
  by_cases hτ : l.1 = τ
  · rw [if_pos hτ, if_pos hτ, inv_inv]
  · rw [if_neg hτ, if_neg hτ]

#print axioms ireflConf_ojoin_eq_on_ioblkS

/-- **AND SO THE MIRROR FACTOR OF THE ACTION IS THE SAME FUNCTION AT THE SECOND HALF-VARIABLE.**

`actionOn_congr` with `ioplqPlus_links_mem`: a positive plaquette reads only links of `ioblkS`, and
on those the reflected configuration IS the plain one at `y`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem actionOn_ioplqPlus_ireflConf_ojoin (φ : MassGap.SUN.SU N → ℝ) (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p - 1) l ∈ Λ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (g g' : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (x y : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (y' : ↥(oboxT τ (2 * p - 1) Λ) → MassGap.SUN.SU N) :
    MassGap.GibbsSpec.actionOn φ (ioplqPlus τ (2 * p - 1) Λ)
        (MassGap.LatticeReflection.ireflConf τ (2 * p - 1)
          (MassGap.GibbsSpec.splice Λ
            (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y)) ω))
      = MassGap.GibbsSpec.actionOn φ (ioplqPlus τ (2 * p - 1) Λ)
        (MassGap.GibbsSpec.splice Λ (ojoin τ (2 * p - 1) Λ g' y y') ω) :=
  MassGap.GibbsSpec.actionOn_congr φ _ _ _
    (fun q hq l hl => ireflConf_ojoin_eq_on_ioblkS τ p hΛ ω g g' x y y'
      (ioplqPlus_links_mem τ p hq hl))

#print axioms actionOn_ioplqPlus_ireflConf_ojoin

/-- **⭐⭐ A HALF-SPACE-SUPPORTED OBSERVABLE IS A FUNCTION OF THE POSITIVE HALF ALONE.**

Change the shared block and the mirror block however you like; an observable whose support lies in
`posHalf τ p` does not move.

**⛔ AND THIS IS WHERE THE PARITY PAYS AGAIN.** `ioblkS_of_le_coord` sends ANY link of `Λ` at height
`≥ p` into the positive block — `τ`-link or transverse — because a `τ`-link needs `2x > 2p-2`, a
transverse one `2x > 2p-1`, and no even number lies between. At an EVEN constant the two thresholds
separate and a half-space-supported observable can reach the shared block, so this statement would be
false as written.

DERIVED: the `2` and the `1` make the constant odd, which is what collapses the two thresholds; `4`
is the dimension. -/
theorem obs_ojoin_local (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (g g' : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (x : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (y y' : ↥(oboxT τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (S : Finset MassGap.InfiniteLattice.ILink) (hS : ↑S ⊆ posHalf τ p) (hSΛ : S ⊆ Λ)
    (f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ)
    (hf : ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
      (∀ lk ∈ S, U lk = V lk) → f U = f V) :
    f (MassGap.GibbsSpec.splice Λ (ojoin τ (2 * p - 1) Λ g x y) ω)
      = f (MassGap.GibbsSpec.splice Λ (ojoin τ (2 * p - 1) Λ g' x y') ω) := by
  refine hf _ _ (fun lk hlk => ?_)
  have hlΛ : lk ∈ Λ := hSΛ hlk
  have hSb : lk ∈ ioblkS τ (2 * p - 1) Λ :=
    ioblkS_of_le_coord τ p hlΛ (hS (Finset.mem_coe.mpr hlk))
  rw [MassGap.GibbsSpec.splice_mem hlΛ, MassGap.GibbsSpec.splice_mem hlΛ,
    ojoin_mem_S τ (2 * p - 1) Λ g x y (mem_oboxS_of_mem_ioblkS τ (2 * p - 1) hSb),
    ojoin_mem_S τ (2 * p - 1) Λ g' x y' (mem_oboxS_of_mem_ioblkS τ (2 * p - 1) hSb)]

#print axioms obs_ojoin_local

/-- **⭐⭐⭐ AND ITS REFLECTION IS THE SAME OBSERVABLE AT THE SECOND HALF-VARIABLE.**

`Θf` evaluated at the configuration assembled with the mirror transport is `f` evaluated at `y` — the
same statement `actionOn_ioplqPlus_ireflConf_ojoin` makes for the action, from the same pointwise
lemma, because both read only links of `ioblkS`.

**⛔ THIS IS THE STEP THAT MAKES THE PAIRING A PAIRING.** `ν(ΘF · F)` becomes an integral of
`a(x) · a(y)` against a kernel in `x` and `y` — two independent draws from ONE space, read by ONE
function. Without the dagger on `omirrorT` the mirror's variables could not be moved onto the
positive block and there would be no such `a`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem obs_ireflConf_ojoin (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p - 1) l ∈ Λ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (g g' : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (x y : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (y' : ↥(oboxT τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (S : Finset MassGap.InfiniteLattice.ILink) (hS : ↑S ⊆ posHalf τ p) (hSΛ : S ⊆ Λ)
    (f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ)
    (hf : ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
      (∀ lk ∈ S, U lk = V lk) → f U = f V) :
    f (MassGap.LatticeReflection.ireflConf τ (2 * p - 1)
        (MassGap.GibbsSpec.splice Λ
          (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y)) ω))
      = f (MassGap.GibbsSpec.splice Λ (ojoin τ (2 * p - 1) Λ g' y y') ω) :=
  hf _ _ (fun lk hlk => ireflConf_ojoin_eq_on_ioblkS τ p hΛ ω g g' x y y'
    (ioblkS_of_le_coord τ p (hSΛ hlk) (hS (Finset.mem_coe.mpr hlk))))

#print axioms obs_ireflConf_ojoin

/-- **⭐⭐⭐ THE STRADDLING FACTOR IS A CONSTANT TIMES THE CROSSING KERNEL.**

    e^{−β·A_cross} = e^{−β·card} · e^{(β/N)·hsRe(X(g·x), X(y))}

`iactCross_eq_trace_sum` turns the straddling action into its cardinality minus `1/N` times a sum of
real traces, and `sum_re_tr_ioplqCross` turns that sum into ONE cross form of the crossing word. What
is left is exactly the kernel `CrossingIntegration.wilson_crossing_pairing_nonneg` integrates.

**⛔ IT IS AN IDENTITY AND CARRIES NO HYPOTHESIS ON `β`** — it holds at every real `β` and asserts no
nonnegativity. What it fixes is the SIGN: `wilsonDensity` enters the action with a minus on the
trace, so `e^{−βA_cross}` carries `+β/N` on the cross form, and the exponent reaching the kernel is
`β/N` rather than `−β/N`. That is what makes `0 ≤ β` the right condition where the kernel is finally
applied — `CrossingIntegration.NegControl.su3_kernel_nonneg_iff` shows the Wilson cross kernel fails
to be positive-semidefinite below zero — but the condition is stated there, not here.

DERIVED: the `2` and the `1` make the constant odd; `N` is the rank, from
`WilsonAction.wilsonDensity` and not chosen here; `4` is the dimension. -/
theorem exp_cross_ojoin (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p - 1) l ∈ Λ)
    (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (β : ℝ)
    (g : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (x y : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N) :
    Real.exp (-β * MassGap.GibbsSpec.actionOn MassGap.WilsonAction.wilsonDensity
        (ioplqCross τ (2 * p - 1) Λ)
        (MassGap.GibbsSpec.splice Λ
          (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y)) ω))
      = Real.exp (-β * ((ioplqCross τ (2 * p - 1) Λ).card : ℝ))
        * Real.exp ((β / (N : ℝ)) * MassGap.CharacterExpansion.hsRe
            (ocrossWord τ p (MassGap.OddLagSplit.planeAct
              (oplaneA τ p dflt) (oplaneB τ p dflt) g x))
            (ocrossWord τ p y)) := by
  rw [iactCross_eq_trace_sum τ (2 * p - 1) Λ
      (MassGap.GibbsSpec.splice Λ
        (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y)) ω),
    sum_re_tr_ioplqCross τ p hΛ dflt ω g x y]
  have harith : ∀ C H : ℝ, -β * (C - (1 / (N : ℝ)) * H)
      = -β * C + (β / (N : ℝ)) * H := by
    intro C H
    ring
  rw [harith, Real.exp_add]

#print axioms exp_cross_ojoin

/-- **⭐⭐ THE OBSERVABLE THE CROSSING INTEGRATION TAKES** — its `a : Ω → ℝ`, a function of the
POSITIVE HALF alone.

The observable times the positive half-weight, read at the configuration assembled with the
constant-one gauge on the other two blocks.

**⛔ THE TWO FACTORS IGNORE THOSE REFERENCE VALUES FOR DIFFERENT REASONS.** The WEIGHT factor ignores
them unconditionally — `actionOn_ioplqPlus_ojoin` carries no hypothesis, because
`ioplqPlus_links_mem` puts every link a positive plaquette reads in `ioblkS`. The OBSERVABLE factor
ignores them only when `f` has half-space support, which is `obs_ojoin_local`'s hypothesis and which
this definition does NOT require — `f` here is arbitrary, so at a general `f` the first factor does
depend on the choice. Callers that need the choice to be immaterial must supply that support.

No inhabitant of `oboxR` or `oboxT` is needed either way: `1` is `Pi.one`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. The `1`s in the body are
the group identity. -/
noncomputable def oddHalfA (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (β : ℝ)
    (f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ)
    (x : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N) : ℝ :=
  f (MassGap.GibbsSpec.splice Λ (ojoin τ (2 * p - 1) Λ 1 x 1) ω)
    * Real.exp (-β * MassGap.GibbsSpec.actionOn MassGap.WilsonAction.wilsonDensity
        (ioplqPlus τ (2 * p - 1) Λ)
        (MassGap.GibbsSpec.splice Λ (ojoin τ (2 * p - 1) Λ 1 x 1) ω))

#print axioms oddHalfA

/-- The configuration `oddHalfA` reads, as a measurable function of the half-variable.

DERIVED: the `2` and the `1` of the constant make it odd; the two other `1`s are the group identity,
the constant-one gauge on the shared and mirror blocks; `4` is the dimension. -/
theorem measurable_oddHalfA_conf (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    Measurable (fun x : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N =>
      MassGap.GibbsSpec.splice Λ (ojoin τ (2 * p - 1) Λ 1 x 1) ω) :=
  (MassGap.GibbsSpec.measurable_splice_left Λ ω).comp
    (measurable_obox_join3_mid τ (2 * p - 1) Λ 1 1)

#print axioms measurable_oddHalfA_conf

/-- **`ham` — the observable is measurable**, given that `f` is.

**⛔ IT CANNOT BE UNCONDITIONAL.** `oddHalfA` takes an arbitrary `f`, so measurability of `f` is a
hypothesis here where the torus twin gets it from `aObs`'s concrete definition
(`OddLagSplit.measurable_aHalf`).

DERIVED: no numeral of its own — the odd constant reaches this only through `oddHalfA`'s body; `4`
is the dimension. -/
theorem measurable_oddHalfA (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (β : ℝ)
    {f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ} (hfm : Measurable f) :
    Measurable (oddHalfA (Λ := Λ) τ p ω β f) :=
  (hfm.comp (measurable_oddHalfA_conf τ p ω)).mul
    ((((MassGap.GibbsSpec.measurable_actionOn
        MassGap.WilsonAction.measurable_wilsonDensity
        (ioplqPlus τ (2 * p - 1) Λ)).comp
      (measurable_oddHalfA_conf τ p ω)).const_mul (-β)).exp)

#print axioms measurable_oddHalfA

/-- **`hab` — the observable is bounded**, given that `f` is.

The positive half-weight is bounded because the Wilson density lies in `[0, 2]`
(`abs_exp_neg_actionOn_le`), so the bound is the observable's own times a factor set by the number of
positive plaquettes and the coupling. **Nothing is chosen** — both are the caller's.

DERIVED: the `2` is the range of the Wilson density (`WilsonAction.wilsonDensity_le_two`), the
cardinality is the positive plaquette set's own, and the `2` and `1` of the constant make it odd; `4`
is the dimension. The `0`s are the one in `N ≠ 0` and the sign in `0 ≤ CF`.-/
theorem abs_oddHalfA_le (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (β : ℝ) (hN : N ≠ 0)
    {f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ} {CF : ℝ} (hCF : 0 ≤ CF)
    (hfb : ∀ U, |f U| ≤ CF)
    (x : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N) :
    |oddHalfA τ p ω β f x|
      ≤ CF * Real.exp (|β| * (((ioplqPlus τ (2 * p - 1) Λ).card : ℝ) * 2)) := by
  rw [oddHalfA, abs_mul]
  refine mul_le_mul (hfb _) ?_ (abs_nonneg _) hCF
  exact abs_exp_neg_actionOn_le (MassGap.WilsonAction.wilsonDensity_nonneg hN)
    (MassGap.WilsonAction.wilsonDensity_le_two hN) β _ _

#print axioms abs_oddHalfA_le


/-- **⭐⭐⭐ THE PAIRING INTEGRAND, IN THE CROSSING INTEGRATION'S VARIABLES.**

    f(ΘU) · f(U) · W(U)  =  const · (a(x) · a(y) · e^{(β/N)·hsRe(X(g·x), X(y))})

pointwise, at the configuration assembled from the three block variables with the mirror transport.
Every factor has been identified: `obs_ireflConf_ojoin` and `obs_ojoin_local` for the observable,
`actionOn_ioplqPlus_ireflConf_ojoin` and `actionOn_ioplqPlus_ojoin` for the two half-weights, and
`exp_cross_ojoin` for the straddling factor.

**⛔ IT IS NOT YET THE CONSUMER'S INTEGRAND.**
`CrossingIntegration.wilson_crossing_pairing_nonneg` takes `a x * a y * exp (β * hsRe …)` — no
constant factor, and `β` multiplying `hsRe` directly. So the consumer is instantiated at
`β' = β/N` and the constant is pulled out first. The parenthesisation here puts the constant
OUTERMOST AND LEFTMOST for exactly that reason, matching `OddLagSplit.oddIntegrand_join`, so
`integral_const_mul` fires with no reassociation.

**⛔ THE TWO HALVES ARE READ BY THE SAME FUNCTION.** `a` appears once at `x` and once at `y`, not two
different functions of two different spaces — that is what `omirrorT`'s dagger bought, and it is what
makes the pairing a pairing rather than a coupling.

DERIVED: the `2` and the `1` make the constant odd; `N` is the rank; `4` is the dimension. -/
theorem integrand_odd_eq (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p - 1) l ∈ Λ)
    (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (β : ℝ)
    (S : Finset MassGap.InfiniteLattice.ILink) (hS : ↑S ⊆ posHalf τ p) (hSΛ : S ⊆ Λ)
    (f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ)
    (hf : ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
      (∀ lk ∈ S, U lk = V lk) → f U = f V)
    (g : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (x y : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N) :
    f (MassGap.LatticeReflection.ireflConf τ (2 * p - 1)
        (MassGap.GibbsSpec.splice Λ
          (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y)) ω))
      * f (MassGap.GibbsSpec.splice Λ
          (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y)) ω)
      * wtFree MassGap.WilsonAction.wilsonDensity β Λ ω
          (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y))
      = Real.exp (-β * ((ioplqCross τ (2 * p - 1) Λ).card : ℝ))
        * (oddHalfA τ p ω β f x * oddHalfA τ p ω β f y
          * Real.exp ((β / (N : ℝ)) * MassGap.CharacterExpansion.hsRe
              (ocrossWord τ p (MassGap.OddLagSplit.planeAct
                (oplaneA τ p dflt) (oplaneB τ p dflt) g x))
              (ocrossWord τ p y))) := by
  rw [wtFree_odd_paired MassGap.WilsonAction.wilsonDensity
      (fun a b => MassGap.WilsonAction.wilsonDensity_conj a b) τ (2 * p - 1) β hΛ ω
      (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y)),
    obs_ireflConf_ojoin τ p hΛ ω g 1 x y 1 S hS hSΛ f hf,
    obs_ojoin_local τ p ω g 1 x (omirrorT τ (2 * p - 1) hΛ y) 1 S hS hSΛ f hf,
    actionOn_ioplqPlus_ojoin MassGap.WilsonAction.wilsonDensity τ p ω g 1 x
      (omirrorT τ (2 * p - 1) hΛ y) 1,
    actionOn_ioplqPlus_ireflConf_ojoin MassGap.WilsonAction.wilsonDensity τ p hΛ ω g 1 x y 1,
    exp_cross_ojoin τ p hΛ dflt ω β g x y]
  unfold oddHalfA
  ring

#print axioms integrand_odd_eq

/-- **THE PAIRING INTEGRAND ON THE BOX** — `f(ΘU)·f(U)` against the free-boundary Wilson weight.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
noncomputable def oddPairIntegrand (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (β : ℝ)
    (f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ)
    (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ) : ℝ :=
  f (MassGap.LatticeReflection.ireflConf τ (2 * p - 1) (MassGap.GibbsSpec.splice Λ u ω))
    * f (MassGap.GibbsSpec.splice Λ u ω)
    * wtFree MassGap.WilsonAction.wilsonDensity β Λ ω u

#print axioms oddPairIntegrand

/-- The pairing integrand is measurable, given that `f` is. The reflection is CONTINUOUS
(`LatticeReflection.continuous_ireflConf`), so the reflected factor costs nothing beyond composing.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem measurable_oddPairIntegrand (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (β : ℝ)
    {f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ} (hfm : Measurable f) :
    Measurable (oddPairIntegrand (Λ := Λ) τ p ω β f) :=
  ((hfm.comp (((MassGap.LatticeReflection.continuous_ireflConf τ
        (2 * p - 1)).measurable).comp
      (MassGap.GibbsSpec.measurable_splice_left Λ ω))).mul
    (hfm.comp (MassGap.GibbsSpec.measurable_splice_left Λ ω))).mul
    (measurable_wtFree MassGap.WilsonAction.measurable_wilsonDensity β Λ ω)

#print axioms measurable_oddPairIntegrand

/-- The integrand is bounded — two copies of the observable's bound times the weight's, which is
`wtFree_le` and rests on the Wilson density lying in `[0, 2]`.

DERIVED: the `2` is the range of the Wilson density (`WilsonAction.wilsonDensity_le_two`) and the
cardinality is the box's own plaquette set — neither is chosen; the `0` is the sign in `N ≠ 0` and
`0 ≤ CF`; `4` is the dimension. -/
theorem abs_oddPairIntegrand_le (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (β : ℝ) (hN : N ≠ 0)
    {f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ} {CF : ℝ} (hCF : 0 ≤ CF)
    (hfb : ∀ U, |f U| ≤ CF)
    (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ) :
    |oddPairIntegrand τ p ω β f u|
      ≤ CF * CF * Real.exp (|β| * (((iplqAll Λ).card : ℝ) * 2)) := by
  rw [oddPairIntegrand, abs_mul, abs_mul]
  refine mul_le_mul (mul_le_mul (hfb _) (hfb _) (abs_nonneg _) hCF) ?_ (abs_nonneg _)
    (by positivity)
  exact wtFree_le (MassGap.WilsonAction.wilsonDensity_nonneg hN)
    (MassGap.WilsonAction.wilsonDensity_le_two hN) β Λ ω u

#print axioms abs_oddPairIntegrand_le

/-- **⭐⭐⭐ THE ODD-CONSTANT PAIRING INTEGRAL IS NONNEGATIVE, AT FINITE VOLUME.**

    0 ≤ ∫ f(ΘU) · f(U) · W(U)

for `f` supported in the positive half-space. This is Osterwalder--Seiler reflection positivity at a
LINK reflection — the mirror at `p - 1/2` that cuts `τ`-links in half — on `ℤ⁴`, and it is the
half-step the even chain cannot reach: `ActionSplit.pairing_nonneg_of_local` needs the twist to act
trivially on the shared block and the residual weight to read that block alone, and an odd constant
breaks both.

The proof is the SAME ARGUMENT as `OddLagSplit.odd_crossing_integral_nonneg`, re-derived here — that
lemma is the torus statement and carries `hm : n = 2 * m` and `2 ≤ m`, so it cannot be applied.
`integral_obox_mirror` puts both half-variables on `oboxS`, `integrand_odd_eq` identifies the
integrand, `integral_const_mul` takes the constant out through all three integrals, and
`CrossingIntegration.wilson_crossing_pairing_nonneg` — abstract in the group, the space and the word
— closes it.

**⛔ `0 ≤ β` IS USED ONCE, ON THE LAST LINE**, as `0 ≤ β/N`. Everything before it is an identity.
`CrossingIntegration.NegControl.su3_kernel_nonneg_iff` shows the Wilson cross kernel is not
positive-semidefinite below zero, so the hypothesis is the sign of the coupling, not an artefact.

DERIVED: the `2` and the `1` make the constant odd; the `0` is the sign asserted and the one in
`N ≠ 0`; `N` is the rank, from `wilsonDensity`; `4` is the dimension. -/
theorem odd_pairing_integral_nonneg (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p - 1) l ∈ Λ)
    (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) {β : ℝ} (hβ : 0 ≤ β) (hN : N ≠ 0)
    (S : Finset MassGap.InfiniteLattice.ILink) (hS : ↑S ⊆ posHalf τ p) (hSΛ : S ⊆ Λ)
    {f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ} (hfm : Measurable f)
    (hf : ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
      (∀ lk ∈ S, U lk = V lk) → f U = f V)
    {CF : ℝ} (hCF : 0 ≤ CF) (hfb : ∀ U, |f U| ≤ CF) :
    0 ≤ ∫ u, oddPairIntegrand τ p ω β f u
      ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))) := by
  rw [integral_obox_mirror τ (2 * p - 1) hΛ (oddPairIntegrand τ p ω β f)
    (measurable_oddPairIntegrand τ p ω β hfm)
    (abs_oddPairIntegrand_le τ p ω β hN hCF hfb)]
  simp only [ojoin_def]
  have hy : ∀ (g : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
      (x : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N),
      (∫ y, oddPairIntegrand τ p ω β f
          (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y))
        ∂(MassGap.ActionSplit.cvol ↥(oboxS τ (2 * p - 1) Λ)
          (probHaar (MassGap.SUN.SU N))))
      = Real.exp (-β * ((ioplqCross τ (2 * p - 1) Λ).card : ℝ))
        * ∫ y, (oddHalfA τ p ω β f x * oddHalfA τ p ω β f y
            * Real.exp ((β / (N : ℝ)) * MassGap.CharacterExpansion.hsRe
                (ocrossWord τ p (MassGap.OddLagSplit.planeAct
                  (oplaneA τ p dflt) (oplaneB τ p dflt) g x))
                (ocrossWord τ p y)))
          ∂(MassGap.ActionSplit.cvol ↥(oboxS τ (2 * p - 1) Λ)
            (probHaar (MassGap.SUN.SU N))) := by
    intro g x
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall
      (fun y => integrand_odd_eq τ p hΛ dflt ω β S hS hSΛ f hf g x y))
  have hx : ∀ g : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N,
      (∫ x, (∫ y, oddPairIntegrand τ p ω β f
            (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y))
          ∂(MassGap.ActionSplit.cvol ↥(oboxS τ (2 * p - 1) Λ)
            (probHaar (MassGap.SUN.SU N))))
        ∂(MassGap.ActionSplit.cvol ↥(oboxS τ (2 * p - 1) Λ)
          (probHaar (MassGap.SUN.SU N))))
      = Real.exp (-β * ((ioplqCross τ (2 * p - 1) Λ).card : ℝ))
        * ∫ x, (∫ y, (oddHalfA τ p ω β f x * oddHalfA τ p ω β f y
              * Real.exp ((β / (N : ℝ)) * MassGap.CharacterExpansion.hsRe
                  (ocrossWord τ p (MassGap.OddLagSplit.planeAct
                    (oplaneA τ p dflt) (oplaneB τ p dflt) g x))
                  (ocrossWord τ p y)))
            ∂(MassGap.ActionSplit.cvol ↥(oboxS τ (2 * p - 1) Λ)
              (probHaar (MassGap.SUN.SU N))))
          ∂(MassGap.ActionSplit.cvol ↥(oboxS τ (2 * p - 1) Λ)
            (probHaar (MassGap.SUN.SU N))) := by
    intro g
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => hy g x))
  have hstep : (∫ g, (∫ x, (∫ y, oddPairIntegrand τ p ω β f
            (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y))
          ∂(MassGap.ActionSplit.cvol ↥(oboxS τ (2 * p - 1) Λ)
            (probHaar (MassGap.SUN.SU N))))
        ∂(MassGap.ActionSplit.cvol ↥(oboxS τ (2 * p - 1) Λ)
          (probHaar (MassGap.SUN.SU N))))
      ∂(MassGap.ActionSplit.cvol ↥(oboxR τ (2 * p - 1) Λ)
        (probHaar (MassGap.SUN.SU N))))
      = Real.exp (-β * ((ioplqCross τ (2 * p - 1) Λ).card : ℝ))
        * ∫ g, (∫ x, (∫ y, (oddHalfA τ p ω β f x * oddHalfA τ p ω β f y
                * Real.exp ((β / (N : ℝ)) * MassGap.CharacterExpansion.hsRe
                    (ocrossWord τ p (MassGap.OddLagSplit.planeAct
                      (oplaneA τ p dflt) (oplaneB τ p dflt) g x))
                    (ocrossWord τ p y)))
              ∂(MassGap.ActionSplit.cvol ↥(oboxS τ (2 * p - 1) Λ)
                (probHaar (MassGap.SUN.SU N))))
            ∂(MassGap.ActionSplit.cvol ↥(oboxS τ (2 * p - 1) Λ)
              (probHaar (MassGap.SUN.SU N))))
          ∂(MassGap.ActionSplit.cvol ↥(oboxR τ (2 * p - 1) Λ)
            (probHaar (MassGap.SUN.SU N))) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun g => hx g))
  rw [hstep]
  refine mul_nonneg (Real.exp_nonneg _) ?_
  exact MassGap.CrossingIntegration.wilson_crossing_pairing_nonneg
    (MassGap.ActionSplit.cvol ↥(oboxR τ (2 * p - 1) Λ) (probHaar (MassGap.SUN.SU N)))
    (MassGap.ActionSplit.cvol ↥(oboxS τ (2 * p - 1) Λ) (probHaar (MassGap.SUN.SU N)))
    (MassGap.OddLagSplit.measurable_uncurry_planeAct
      (oplaneA τ p dflt) (oplaneB τ p dflt))
    (fun g => MassGap.OddLagSplit.planeAct_measurePreserving
      (oplaneA τ p dflt) (oplaneB τ p dflt) g)
    (fun g h u => MassGap.OddLagSplit.planeAct_mul
      (oplaneA τ p dflt) (oplaneB τ p dflt) g h u)
    (ocrossWord τ p)
    (measurable_coord_ocrossWord τ p)
    (fun c v => abs_coord_ocrossWord_le_one τ p c v)
    (fun g u v => hsRe_ocrossWord_planeAct τ p
      (oplaneA τ p dflt) (oplaneB τ p dflt) g u v)
    (measurable_oddHalfA τ p ω β hfm) (by positivity)
    (fun x => abs_oddHalfA_le τ p ω β hN hCF hfb x)
    (by positivity)

#print axioms odd_pairing_integral_nonneg

/-- **⭐⭐⭐ THE FREE-BOUNDARY STATE OF A BOX IS REFLECTION POSITIVE AT THE ODD CONSTANT.**

    0 ≤ ⟨Θf · f⟩_Λ

for `f` supported in the positive half-space — `InfiniteReflection.ReflPositiveOn`'s content at one
finite volume, at the mirror `p - 1/2` that CUTS `τ`-links.

`odd_pairing_integral_nonneg` is the numerator and `partFree_pos` the denominator; the observable's
bound is `InfiniteLattice.bounded_of_continuous`, since `IConf` is a product of compact groups and a
continuous real function on it is bounded outright.

**⛔ IT CARRIES THREE RESTRICTIONS THE EVEN COUNTERPART DOES NOT**, and they are not bookkeeping.
`stateFree_refl_nonneg_of_halfSpace_support` is general in `φ` under `hφm`/`hφ0`/`hφ2`/`hφc`, needs no
condition on `N`, and asks nothing of the box beyond reflection-closure. This one:

* takes `dflt : ↥(oboxR τ (2p-1) Λ)`, so **the box's SHARED BLOCK must be nonempty**. At an odd
  constant that block is exactly the `τ`-links based at `p - 1`, and a reflection-closed box built
  from transverse links alone satisfies `hΛ` with `oboxR = ∅`, where this theorem cannot be stated at
  all;
* hard-wires `φ` to `WilsonAction.wilsonDensity`, because the crossing kernel is the Wilson one; and
* takes `hN : N ≠ 0`.

**⛔ AND THE EVEN ROUTE FAILS UNDER EXACTLY THE FIRST OF THOSE, NOT IN GENERAL.**
`ActionSplit.pairing_nonneg_of_local` needs `hσR` — the twist trivial on the shared block — and
`hWloc` — the residual weight reading that block alone. When `oboxR` is NONEMPTY both fail at an odd
constant: the shared block is the `τ`-links, where the twist is INVERSION
(`LatticeReflection.ireflConf_inverts_fixed_axis_link`), and the weight reads straddling plaquettes
touching all three blocks (`osLinkOf_mem_oboxS` beside `otLinkOf_mem_oboxT`). When it is EMPTY both
hold vacuously — `ioplqCross` is empty too, so the residual weight is `1` — and the even route works
while this theorem does not apply. **The two conditions are the same condition.** Neither direction is
formalised here; this paragraph is a reading of the two hypothesis sets, not a theorem, and
`eq_empty_of_stable_two_mirrors` is what a proved no-go in this file looks like.

DERIVED: the `2` and the `1` make the constant odd; the `0` is the sign asserted and the one in
`N ≠ 0`; `4` is the dimension. -/
theorem stateFree_odd_refl_nonneg (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p - 1) l ∈ Λ)
    (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) {β : ℝ} (hβ : 0 ≤ β) (hN : N ≠ 0)
    (S : Finset MassGap.InfiniteLattice.ILink) (hS : ↑S ⊆ posHalf τ p) (hSΛ : S ⊆ Λ)
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hf : ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
      (∀ lk ∈ S, U lk = V lk) → f U = f V) :
    0 ≤ stateFree MassGap.WilsonAction.measurable_wilsonDensity
        (MassGap.WilsonAction.wilsonDensity_nonneg hN)
        (MassGap.WilsonAction.wilsonDensity_le_two hN) β Λ ω
        ((MassGap.LatticeReflection.latticeReflection τ (2 * p - 1)).θ f * f) := by
  obtain ⟨CF, hCF⟩ := MassGap.InfiniteLattice.bounded_of_continuous f.continuous
  have hCF0 : 0 ≤ CF := le_trans (abs_nonneg _) (hCF 1)
  rw [stateFree_apply]
  unfold specFree
  refine div_nonneg ?_ (partFree_pos MassGap.WilsonAction.measurable_wilsonDensity
    (MassGap.WilsonAction.wilsonDensity_nonneg hN)
    (MassGap.WilsonAction.wilsonDensity_le_two hN) β Λ ω).le
  have hrw : ∀ u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ,
      ((MassGap.LatticeReflection.latticeReflection τ (2 * p - 1)).θ f * f)
          (MassGap.GibbsSpec.splice Λ u ω)
        * wtFree MassGap.WilsonAction.wilsonDensity β Λ ω u
      = oddPairIntegrand τ p ω β f u := fun _ => rfl
  rw [integral_congr_ae (Filter.Eventually.of_forall hrw)]
  exact odd_pairing_integral_nonneg τ p hΛ dflt ω hβ hN S hS hSΛ
    f.continuous.measurable hf hCF0 hCF

#print axioms stateFree_odd_refl_nonneg

/-- **`Re tr` AT THE WITNESS BOX'S OWN HALF-LINK** — an observable supported exactly on
`ocrossSupp`.

CHOSEN: `3` is SU(3)'s rank. Nothing in this definition forces it — `Re tr` reads any `SU N` — but
`ocrossObs_nonconstant` needs `CrossingIntegration.trace_gNeg`, which exists at `3`. `4` is the
dimension. -/
noncomputable def ocrossObs (τ ν : Fin 4) (p : ℤ) :
    C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU 3), ℝ) :=
  MassGap.HalfSpaceAlgebra.halfLinkObs (osLinkOf τ (ocrossPlaq τ ν p))
    ⟨fun g => (Matrix.trace (g : Matrix (Fin 3) (Fin 3) ℂ)).re,
      Complex.continuous_re.comp continuous_subtype_val.matrix_trace⟩

#print axioms ocrossObs

/-- It reads that link and nothing else — the `hf` `odd_pairing_integral_nonneg` takes.

CHOSEN: `3` is inherited from `ocrossObs` and is not forced here. `4` is the dimension. -/
theorem ocrossObs_local (τ ν : Fin 4) (p : ℤ)
    (U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU 3))
    (h : ∀ lk ∈ ocrossSupp τ ν p, U lk = V lk) :
    ocrossObs τ ν p U = ocrossObs τ ν p V := by
  have hmem : osLinkOf τ (ocrossPlaq τ ν p) ∈ ocrossSupp τ ν p :=
    Finset.mem_singleton_self _
  show (Matrix.trace ((U (osLinkOf τ (ocrossPlaq τ ν p)) : MassGap.SUN.SU 3)
      : Matrix (Fin 3) (Fin 3) ℂ)).re
    = (Matrix.trace ((V (osLinkOf τ (ocrossPlaq τ ν p)) : MassGap.SUN.SU 3)
      : Matrix (Fin 3) (Fin 3) ℂ)).re
  rw [h _ hmem]

#print axioms ocrossObs_local

/-- **⭐ AND IT IS NOT CONSTANT** — at SU(3), `Re tr 1 = 3` against `Re tr gNeg = -1`.

**⛔ WITHOUT THIS THE OBSERVABLE HALF OF THE KEYSTONE IS DECORATIVE.** `odd_pairing_integral_nonneg`
assumes only `N ≠ 0`, and at `N = 1` the group `SU 1` is a singleton, so `IConf` is a singleton,
EVERY observable is constant, and the conclusion holds with `0 ≤ β` never used. The theorem is true
for a trivial reason on a member of its own hypothesis set. This says the non-trivial case is real:
at SU(3) the integrand genuinely varies with the half-variable, which is the only case the Clay
problem is about.

DERIVED: `3` is SU(3)'s rank, and here it IS forced — `trace_gNeg` is what separates the two
configurations, and it exists at `3`. `4` is the dimension. The `1` and `-1` of the proof are the
trace of the identity and `trace_gNeg`'s computed value; neither is in the statement. -/
theorem ocrossObs_nonconstant (τ ν : Fin 4) (p : ℤ) :
    ∃ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU 3),
      ocrossObs τ ν p U ≠ ocrossObs τ ν p V := by
  refine ⟨1, (fun _ => MassGap.CrossingIntegration.gNeg), ?_⟩
  have h1 : ocrossObs τ ν p 1 = 3 := by
    show (Matrix.trace (((1 : MassGap.SUN.SU 3) : Matrix (Fin 3) (Fin 3) ℂ))).re = 3
    simp
  have h2 : ocrossObs τ ν p (fun _ => MassGap.CrossingIntegration.gNeg) = -1 :=
    MassGap.CrossingIntegration.trace_gNeg
  rw [h1, h2]
  norm_num

#print axioms ocrossObs_nonconstant

/-- **⭐⭐⭐ THE KEYSTONE, AT A BOX AND AN OBSERVABLE THAT EXIST.**

Every hypothesis of `odd_pairing_integral_nonneg` discharged at once, with no hypothesis left open
but `0 ≤ β` and `ν ≠ τ`:

* `hΛ` — `ocrossBox_refl_closed`;
* `dflt` — `ocrossBox_oboxR_nonempty`, so the SHARED BLOCK is inhabited and the theorem can be
  stated at all;
* `S`, `hS`, `hSΛ` — `ocrossSupp` with `ocrossSupp_subset_posHalf` and `ocrossSupp_subset_box`;
* `f`, `hfm`, `hf`, `hfb` — `ocrossObs`, continuous hence measurable, local by `ocrossObs_local`,
  bounded by `InfiniteLattice.bounded_of_continuous`.

**⛔ THIS IS WHAT THE WITNESS LEMMAS ARE FOR.** Separately they say four sets are inhabited;
composed, they say the keystone's hypothesis set is. And `ocrossBox_cross_nonempty`,
`ocrossBox_plus_nonempty`, `ocrossBox_oboxS_nonempty` and `ocrossObs_nonconstant` say the conclusion
is not empty at it — straddling plaquettes exist, positive plaquettes exist, the integration space is
not a point, and the observable is not constant.

CHOSEN: `3` is inherited from `ocrossObs`; `odd_pairing_integral_nonneg` is general in `N` under
`N ≠ 0` and every other input here is `N`-free, so this instance is narrower than what it proves — it
is pinned at `3` so that `ocrossObs_nonconstant` applies to the same observable.
DERIVED: the first `0` is the sign of the coupling and the second the sign asserted; `4` is the
dimension. -/
theorem ocrossBox_odd_pairing_nonneg (τ ν : Fin 4) (hν : ν ≠ τ) (p : ℤ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU 3)) {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ ∫ u, oddPairIntegrand (N := 3) τ p ω β (ocrossObs τ ν p) u
      ∂(MassGap.ActionSplit.cvol ↥(ocrossBox τ ν p) (probHaar (MassGap.SUN.SU 3))) := by
  obtain ⟨d, hd⟩ := ocrossBox_oboxR_nonempty τ ν hν p
  obtain ⟨CF, hCF⟩ :=
    MassGap.InfiniteLattice.bounded_of_continuous (ocrossObs τ ν p).continuous
  exact odd_pairing_integral_nonneg (N := 3) τ p (ocrossBox_refl_closed τ ν p)
    ⟨d, hd⟩ ω hβ (by norm_num) (ocrossSupp τ ν p)
    (ocrossSupp_subset_posHalf τ ν hν p) (ocrossSupp_subset_box τ ν hν p)
    (ocrossObs τ ν p).continuous.measurable (ocrossObs_local τ ν p)
    (le_trans (abs_nonneg _) (hCF 1)) hCF

#print axioms ocrossBox_odd_pairing_nonneg

/-- **⭐⭐⭐ REFLECTION POSITIVITY AT THE ODD CONSTANT, ON THE HALF-SPACE ALGEBRA.**

The limit of the free-boundary states over any reflection-closed exhausting family is reflection
positive at the mirror `p - 1/2`, on the whole half-space algebra.

**IT IS NOT `reflPositive_of_tendsto_halfSpaceAlg` AT A DIFFERENT CONSTANT.** It is strictly
narrower: it adds `hR`, adds `0 ≤ β`, adds `hN : N ≠ 0`, and replaces the abstract class function
`φ` — which includes `φ = 0`, the free theory — by `WilsonAction.wilsonDensity`, because the crossing
kernel is the Wilson one. It drops `hφc`, which the odd route never needs. And `B3` is this file's
name for the EVEN statement (`HalfSpaceReflPositive`), which this does not instantiate.

`InfiniteReflection.reflPositive_of_eventually_pointwise` does the transport: a member of
`halfSpaceAlg` carries its own finite support `S`, `hexh` puts `S` inside the box eventually, and
`stateFree_odd_refl_nonneg` gives the sign at each such box. **The support is chosen per observable,
not once for the algebra** — `halfSpaceAlg` is a directed union and is local to no single box.

**⛔ IT CARRIES `hR`, WHICH THE EVEN LIFT DOES NOT.** The box must have a NONEMPTY shared block,
because `stateFree_odd_refl_nonneg` takes an inhabitant of it. At an odd constant that block CONTAINS
the `τ`-links based at `p - 1` (`tauLink_mem_oboxR`; that it contains nothing else is not proved
here, though `odd_nonTau_not_fixed` is most of it), so a family built only from transverse links
satisfies `hbox` and fails `hR`. **Reading the two hypothesis sets** — not a theorem, and neither
direction is formalised — that is also the condition under which the EVEN route would work, so it may
be no gap at all; but it is a real hypothesis and a family has to meet it.

**IT IS EVENTUAL, NOT UNIVERSAL**, because a cube of radius `n` centred on the constant contains no
site at height `p - 1` until `n ≥ |p|`. At `p = 0` that is every `n` and the universal form would
hold; at other `p` it would not, so the eventual form is what a statement over all `p` can carry.
`symCube_oboxR_nonempty` discharges it.

**⛔ AND AT `N ≤ 1` THE CONCLUSION IS EMPTY** — `SU 1` is a singleton, so `halfSpaceAlg` is the
constants and `ReflPositiveOn` says nothing. `halfSpaceAlg_has_nonconstant` is the witness at
SU(3).

DERIVED: the `2` and the `1` make the constant odd; the `0` is the sign of the coupling and the one
in `N ≠ 0`; `4` is the dimension. -/
theorem reflPositive_of_tendsto_halfSpaceAlg_odd
    {ι : Type*} {l : Filter ι} [l.NeBot] (τ : Fin 4) (p : ℤ)
    (box : ι → Finset MassGap.InfiniteLattice.ILink)
    (hbox : ∀ i, ∀ lk ∈ box i, ireflLink τ (2 * p - 1) lk ∈ box i)
    (hR : ∀ᶠ i in l, (oboxR τ (2 * p - 1) (box i)).Nonempty)
    (hexh : ∀ S : Finset MassGap.InfiniteLattice.ILink, ∀ᶠ i in l, S ⊆ box i)
    {β : ℝ} (hβ : 0 ≤ β) (hN : N ≠ 0)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun i => stateFree MassGap.WilsonAction.measurable_wilsonDensity
        (MassGap.WilsonAction.wilsonDensity_nonneg hN)
        (MassGap.WilsonAction.wilsonDensity_le_two hN) β (box i) ω f) l (nhds (ν f))) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p - 1))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν := by
  refine MassGap.InfiniteReflection.reflPositive_of_eventually_pointwise htend _ _ ?_
  intro f hf
  obtain ⟨S, hS, hfloc⟩ := MassGap.HalfSpaceAlgebra.mem_halfSpaceAlg.mp hf
  refine ((hexh S).and hR).mono (fun i hi => ?_)
  obtain ⟨d, hd⟩ := hi.2
  exact stateFree_odd_refl_nonneg (Λ := box i) τ p (hbox i) ⟨d, hd⟩ ω hβ hN S hS hi.1 f hfloc

#print axioms reflPositive_of_tendsto_halfSpaceAlg_odd



/-- **AT AN ODD CONSTANT NO TRANSVERSE LINK IS FIXED.** A non-`τ` link reflects about `c` itself, so
fixing it needs `2x_τ = c`, which an odd `c` cannot satisfy.

This is the exact mirror of `no_tau_link_fixed`, which says the same of `τ`-links at an EVEN
constant.

DERIVED: the `2` is the plane-to-constant conversion and the `1` the half-step, together making the
constant odd — which is the whole content; `4` is the dimension. -/
theorem odd_nonTau_not_fixed (τ : Fin 4) (p : ℤ) {l : MassGap.InfiniteLattice.ILink}
    (h : l.1 ≠ τ) : ireflLink τ (2 * p - 1) l ≠ l := by
  intro heq
  have hcoord : (ireflLink τ (2 * p - 1) l).2 τ = l.2 τ := by rw [heq]
  rw [image_half_is_c_sub_p τ (2 * p - 1) h] at hcoord
  omega

#print axioms odd_nonTau_not_fixed

/-- **AND AN AXIS LINK IS FIXED EXACTLY WHEN IT STRADDLES THE MIRROR.** A `τ`-link reflects about
`c - 1 = 2p - 2`, so it is fixed exactly at base `p - 1` — the link spanning `[p-1, p]`, which is the
one the mirror at `p - 1/2` cuts in half.

**⛔ AND THE DAGGER INVERTS ON IT.** `ireflConf` inverts on `τ`-links, so unlike the even case the
twist does NOT act trivially on the shared block. That is why the odd pairing is an integral against
a kernel rather than a square, and why it needs `0 ≤ β`.

DERIVED: the `2` is the plane-to-constant conversion, the `1`s are the half-step and `ireflLink`'s
link length; `4` is the dimension. -/
theorem odd_tau_fixed_iff (τ : Fin 4) (p : ℤ) {l : MassGap.InfiniteLattice.ILink}
    (h : l.1 = τ) : ireflLink τ (2 * p - 1) l = l ↔ l.2 τ = p - 1 := by
  constructor
  · intro heq
    have hcoord : (ireflLink τ (2 * p - 1) l).2 τ = l.2 τ := by rw [heq]
    simp only [ireflLink, if_pos h, ireflSite_axis] at hcoord
    omega
  · intro hx
    refine Prod.ext rfl ?_
    show (if l.1 = τ then ireflSite τ (2 * p - 1 - 1) l.2 else ireflSite τ (2 * p - 1) l.2) = l.2
    rw [if_pos h]
    funext j
    by_cases hj : j = τ
    · subst hj
      simp only [ireflSite, Function.update_self]
      omega
    · simp [ireflSite, Function.update_of_ne hj]

#print axioms odd_tau_fixed_iff

/-! ### A box family that is reflection-stable AND exhausting -/

/-- The coordinate cube of radius `n` centred at the REFLECTION CONSTANT `c`, in every coordinate.

`c` is the constant, not the plane — the mirror it names sits at `c / 2`. Centring the cube on `c`
rather than on the plane is what makes `symCube` stable for free.

DERIVED: `4` is the spacetime dimension, `ILink`'s own; `c` and `n` are the caller's constant and
radius. The pair `(direction, site)` a link is comes from `×ˢ` and carries no numeral. -/
noncomputable def coordCube (c : ℤ) (n : ℕ) : Finset MassGap.InfiniteLattice.ILink :=
  Finset.univ ×ˢ Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (c - n) (c + n))

/-- **THE SYMMETRISED CUBE.** The cube together with its mirror image — stable by construction, and
still finite.

DERIVED: `c` is the caller's reflection constant; `n` is the caller's radius; `4` is the
dimension. -/
noncomputable def symCube (τ : Fin 4) (c : ℤ) (n : ℕ) : Finset MassGap.InfiniteLattice.ILink :=
  coordCube c n ∪ (coordCube c n).image (ireflLink τ c)

/-- **THE SYMMETRISED CUBE IS THE REFLECTION CLOSURE OF THE PLAIN ONE.** Same construction, stated
once: `reflClosure` unions a set with its reflected image, which is what `symCube` does to
`coordCube`.

DERIVED: `c` is the caller's reflection constant; `n` is the radius; `4` is the dimension. -/
theorem symCube_eq_reflClosure (τ : Fin 4) (c : ℤ) (n : ℕ) :
    symCube τ c n = reflClosure τ c (coordCube c n) := rfl

#print axioms symCube_eq_reflClosure

/-- **IT IS REFLECTION-STABLE** — `hbox`, discharged. `reflClosure_closed`, at the plain cube: a
member reflects into the image part, and a member of the image part reflects back by involutivity.

DERIVED: `c` is the caller's reflection constant, no longer pinned to an even `2p`; `4` is the
dimension. -/
theorem symCube_refl_stable (τ : Fin 4) (c : ℤ) (n : ℕ) :
    ∀ lk ∈ symCube τ c n, ireflLink τ c lk ∈ symCube τ c n :=
  reflClosure_closed τ c (coordCube c n)

#print axioms symCube_refl_stable

/-- **AND IT EXHAUSTS** — `hexh`, discharged. A `Finset` of links has finitely many coordinates, so
they are bounded, so it sits inside every large enough cube.

DERIVED: `n` is the radius; `4` is the dimension. -/
theorem symCube_exhausts (τ : Fin 4) (c : ℤ) (S : Finset MassGap.InfiniteLattice.ILink) :
    ∀ᶠ n : ℕ in Filter.atTop, S ⊆ symCube τ c n := by
  classical
  set M : ℕ := S.sup (fun lk => Finset.univ.sup (fun j : Fin 4 => (lk.2 j).natAbs)) with hM
  refine Filter.eventually_atTop.2 ⟨M + c.natAbs, fun n hn lk hlk => ?_⟩
  refine Finset.mem_union_left _ ?_
  refine Finset.mem_product.2 ⟨Finset.mem_univ _, Fintype.mem_piFinset.2 (fun j => ?_)⟩
  have hin : (lk.2 j).natAbs
      ≤ Finset.univ.sup (fun k : Fin 4 => (lk.2 k).natAbs) :=
    Finset.le_sup (f := fun k : Fin 4 => (lk.2 k).natAbs) (Finset.mem_univ j)
  have houter : Finset.univ.sup (fun k : Fin 4 => (lk.2 k).natAbs) ≤ M := by
    rw [hM]
    exact Finset.le_sup
      (f := fun m : MassGap.InfiniteLattice.ILink =>
        Finset.univ.sup (fun k : Fin 4 => (m.2 k).natAbs)) hlk
  have h1 : (lk.2 j).natAbs ≤ M := le_trans hin houter
  exact Finset.mem_Icc.2 ⟨by omega, by omega⟩

#print axioms symCube_exhausts

/-- **⭐ AND THE CUBE FAMILY MEETS `hR`.** Eventually the cube reaches height `p - 1`, and then its
`τ`-link there is in the shared block.

`ocrossSite p` is the site all of whose coordinates are `p - 1`; only its `τ` one matters here.

**⛔ WHY EVENTUAL.** `coordCube` admits sites with every coordinate in `Icc (c-n) (c+n)` at
`c = 2p-1`, so height `p - 1` is in range exactly when `n ≥ |p|`. At `p = 0` that holds at every `n`,
including `n = 0`; at other `p` the cube is genuinely too small at first. A statement over all `p`
therefore has to be eventual, though it is not sharp at every `p`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem symCube_oboxR_nonempty (τ : Fin 4) (p : ℤ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (oboxR τ (2 * p - 1) (symCube τ (2 * p - 1) n)).Nonempty := by
  refine (symCube_exhausts τ (2 * p - 1)
    {((τ, ocrossSite p) : MassGap.InfiniteLattice.ILink)}).mono (fun n hn => ?_)
  have hmem : ((τ, ocrossSite p) : MassGap.InfiniteLattice.ILink) ∈ symCube τ (2 * p - 1) n :=
    hn (Finset.mem_singleton_self _)
  exact ⟨⟨_, hmem⟩, tauLink_mem_oboxR τ p rfl hmem⟩

#print axioms symCube_oboxR_nonempty

/-- The same at the ODD constant, where `hR` transports the same way.

DERIVED: the `2` and the `1` make the constant odd; the two `0`s are the sign of the coupling and
the one in `N ≠ 0`; `4` is the dimension. -/
theorem wilson_reflPositive_odd_of_tendsto (τ : Fin 4) (p : ℤ) (hN : N ≠ 0)
    {β : ℝ} (hβ : 0 ≤ β)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (l : Filter ℕ) [l.NeBot] (hl : l ≤ Filter.atTop)
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p - 1) n) ω f)
        l (nhds (ν f))) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p - 1))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν :=
  reflPositive_of_tendsto_halfSpaceAlg_odd τ p (symCube τ (2 * p - 1))
    (fun n => symCube_refl_stable τ (2 * p - 1) n)
    (Filter.Eventually.filter_mono hl (symCube_oboxR_nonempty τ p))
    (fun S => Filter.Eventually.filter_mono hl (symCube_exhausts τ (2 * p - 1) S))
    hβ hN ω ν htend

#print axioms wilson_reflPositive_odd_of_tendsto

/-- **⭐⭐⭐ B3 AT THE ODD CONSTANT, AT THE CUBE FAMILY — ONE CONVERGENCE HYPOTHESIS AND NOTHING
ELSE.**

`symCube_refl_stable` is `hbox`, `symCube_exhausts` is `hexh`, `symCube_oboxR_nonempty` is `hR`. What
is left is the thermodynamic limit itself and the sign of the coupling.

**⛔ NOTHING IS KNOWN TO SATISFY `htend` AS STATED.** Compactness gives convergence along a refining
ULTRAFILTER for free — `DLRLimit.exists_limit_state` — and not along `atTop`;
`wilson_reflPositive_limit_exists_odd` below is the unconditional form, and this one is for a caller
who already has an `atTop` limit.

**⛔ AND AT `N ≤ 1` THE CONCLUSION IS EMPTY**, as for the abstract form above.

DERIVED: the `2` and the `1` make the constant odd; the `0` is the sign of the coupling and the one
in `N ≠ 0`; `4` is the dimension. -/
theorem reflPositive_symCube_odd (τ : Fin 4) (p : ℤ)
    {β : ℝ} (hβ : 0 ≤ β) (hN : N ≠ 0)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n : ℕ => stateFree MassGap.WilsonAction.measurable_wilsonDensity
        (MassGap.WilsonAction.wilsonDensity_nonneg hN)
        (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p - 1) n) ω f)
        Filter.atTop (nhds (ν f))) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p - 1))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν :=
  wilson_reflPositive_odd_of_tendsto τ p hN hβ ω ν Filter.atTop le_rfl htend

#print axioms reflPositive_symCube_odd

/-- **⭐⭐⭐ AND A LIMIT STATE WITH ODD REFLECTION POSITIVITY EXISTS, UNCONDITIONALLY.**

No convergence hypothesis. `DLRLimit.exists_limit_state` gives a refining ULTRAFILTER along which the
free-boundary states converge — compactness, no uniqueness — and
`reflPositive_of_tendsto_halfSpaceAlg_odd` is filter-generic, so `hR` and `hexh` transport by
`Filter.Eventually.filter_mono`. The `ℤ⁴` odd counterpart of `wilson_reflPositive_limit_exists`.

**⛔ IT IS AN ULTRAFILTER, NOT `atTop`.** Compactness cannot give convergence along `atTop` itself;
that is the thermodynamic limit and is not proved anywhere here. What this removes is the need to
ASSUME a limit exists at all.

**⛔ AND AT `N ≤ 1` THE CONCLUSION IS EMPTY** — `SU 1` is a singleton, so `halfSpaceAlg` is the
constants. `halfSpaceAlg_has_nonconstant` is the witness at SU(3).

DERIVED: the `2` and the `1` make the constant odd; the `0` is the sign of the coupling and the one
in `N ≠ 0`; `4` is the dimension. -/
theorem wilson_reflPositive_limit_exists_odd (τ : Fin 4) (p : ℤ) (hN : N ≠ 0)
    {β : ℝ} (hβ : 0 ≤ β) (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    ∃ (u : Ultrafilter ℕ) (ν : MassGap.DLRLimit.State
        (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))),
      (∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
        Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p - 1) n) ω f)
          (u : Filter ℕ) (nhds (ν f))) ∧
      MassGap.InfiniteReflection.ReflPositiveOn
        (MassGap.LatticeReflection.latticeReflection τ (2 * p - 1))
        (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν := by
  obtain ⟨u, ν, hle, htend⟩ :=
    MassGap.DLRLimit.exists_limit_state Filter.atTop
      (fun n : ℕ => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
        MassGap.WilsonAction.measurable_wilsonDensity
        (MassGap.WilsonAction.wilsonDensity_nonneg hN)
        (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p - 1) n) ω)
  haveI : (u : Filter ℕ).NeBot := u.neBot'
  refine ⟨u, ν, htend, ?_⟩
  exact reflPositive_of_tendsto_halfSpaceAlg_odd τ p (symCube τ (2 * p - 1))
    (fun n => symCube_refl_stable τ (2 * p - 1) n)
    (Filter.Eventually.filter_mono hle (symCube_oboxR_nonempty τ p))
    (fun S => Filter.Eventually.filter_mono hle (symCube_exhausts τ (2 * p - 1) S))
    hβ hN ω ν htend

#print axioms wilson_reflPositive_limit_exists_odd

/-- **⭐⭐⭐ THE TRANSFER OPERATOR IS POSITIVE — `hposOdd` DISCHARGED.**

`WilsonTransferReduction.positiveTransfer_iff_odd_reflPositive` is an EQUIVALENCE: the transfer data
assembled from the state facts is a positive transfer **exactly when** the state is reflection
positive at the ODD constant on the same algebra. `reflPositive_symCube_odd` supplies that side, so
the composition is one line.

**⛔ `hposOdd` WAS THE OPEN HYPOTHESIS OF THE WHOLE OPERATOR SIDE.** It is now a consequence of the
thermodynamic limit and `0 ≤ β`, with no assumption about the transfer operator anywhere.

**⛔ `hpos` AND `htend` ARE ABOUT DIFFERENT FAMILIES, AND THEY CANNOT BE THE SAME ONE.** `hpos` is
reflection positivity at `2p`, which the even chain gets from `symCube τ (2 * p)`; `htend` here is
convergence of `symCube τ (2 * p - 1)`. **No nonempty box is stable under both mirrors** —
`eq_empty_of_stable_two_mirrors` proves exactly that — so no single family discharges both, and the
two limits agreeing is an assumption this statement leaves implicit in sharing `ν`.
`wilson_transferData_of_common_limit` is the form that makes that assumption visible, and
`wilson_transferData_of_thermodynamic_limit` discharges it by interleaving the two shapes into
`mixCube`, whose even and odd subsequences converge to one state automatically.
`wilson_positiveTransfer_of_mixCube_limit` below is this theorem in that form, and
`wilson_positiveTransfer_of_common_subsequential_limit` is the weakest of the three — it asks only
that the two families share a state, along filters that need not agree.

**⛔ AND AT `N ≤ 1` THE CONCLUSION IS EMPTY.** `hN : N ≠ 0` is not enough for the carrier to be
non-trivial: at `N = 1` the group `SU 1` is a singleton, so `IConf` is, so `halfSpaceAlg` is the
constants and `PositiveTransfer` holds of a one-dimensional space. `halfSpaceAlg_has_nonconstant`
supplies the witness at SU(3), which is the case the Clay problem is about.

DERIVED: the `2` and the `1` make the odd constant; the `2` alone is the plane-to-constant conversion
`c = 2p`; the `0` is the sign of the coupling and the one in `N ≠ 0`; `4` is the dimension. -/
theorem wilson_positiveTransfer_of_odd_limit (τ : Fin 4) (p : ℤ)
    {β : ℝ} (hβ : 0 ≤ β) (hN : N ≠ 0)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν)
    (hnu : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f)
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n : ℕ => stateFree MassGap.WilsonAction.measurable_wilsonDensity
        (MassGap.WilsonAction.wilsonDensity_nonneg hN)
        (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p - 1) n) ω f)
        Filter.atTop (nhds (ν f))) :
    MassGap.GNSHilbert.PositiveTransfer
      (MassGap.WilsonTransferReduction.transferData_of_state_facts τ p ν hinv hpos hnu) :=
  (MassGap.WilsonTransferReduction.positiveTransfer_iff_odd_reflPositive τ p ν hinv hpos hnu).mpr
    (reflPositive_symCube_odd τ p hβ hN ω ν htend)

#print axioms wilson_positiveTransfer_of_odd_limit

/-- **⭐⭐ REFLECTION POSITIVITY ON `halfSpaceAlg`, GIVEN CONVERGENCE.** The `_of_tendsto` half of
the pair below, so the limit theorem and `reflection_facts_on_halfSpaceAlg` share one proof.

The observable's own support picks the fixed region, `hexh` puts that support inside the box
eventually, and `InfiniteReflection.reflPositive_of_eventually_pointwise` is what accepts an
eventual hypothesis in place of a uniform one.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`; `4` is the dimension. The `0` is the sign in `0 ≤ φ`.-/
theorem reflPositive_of_tendsto_halfSpaceAlg
    {ι : Type*} {l : Filter ι} [l.NeBot] (τ : Fin 4) (p : ℤ)
    (box : ι → Finset MassGap.InfiniteLattice.ILink)
    (hbox : ∀ i, ∀ lk ∈ box i, ireflLink τ (2 * p) lk ∈ box i)
    (hexh : ∀ S : Finset MassGap.InfiniteLattice.ILink, ∀ᶠ i in l, S ⊆ box i)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun i => stateFree hφm hφ0 hφ2 β (box i) ω f) l (nhds (ν f))) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν := by
  refine MassGap.InfiniteReflection.reflPositive_of_eventually_pointwise htend _ _ ?_
  intro f hf
  obtain ⟨S, hS, hfloc⟩ := MassGap.HalfSpaceAlgebra.mem_halfSpaceAlg.mp hf
  refine (hexh S).mono (fun i hi => ?_)
  exact stateFree_refl_nonneg_of_halfSpace_support (Λ := box i) (hbox i)
    hφm hφ0 hφ2 hφc β ω S hS hi f hfloc

#print axioms reflPositive_of_tendsto_halfSpaceAlg

/-- Reflection positivity at the EVEN constant from convergence of the even cube family along ANY
filter refining `atTop` — a subsequential limit is enough, because `hexh` transports by
`Filter.Eventually.filter_mono`.

DERIVED: the `2` is the plane-to-constant conversion; the `0` is the one in `N ≠ 0`; `4` is the
dimension. -/
theorem wilson_reflPositive_even_of_tendsto (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (l : Filter ℕ) [l.NeBot] (hl : l ≤ Filter.atTop)
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p) n) ω f)
        l (nhds (ν f))) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν :=
  reflPositive_of_tendsto_halfSpaceAlg τ p (symCube τ (2 * p))
    (fun n => symCube_refl_stable τ (2 * p) n)
    (fun S => Filter.Eventually.filter_mono hl (symCube_exhausts τ (2 * p) S))
    MassGap.WilsonAction.measurable_wilsonDensity
    (MassGap.WilsonAction.wilsonDensity_nonneg hN)
    (MassGap.WilsonAction.wilsonDensity_le_two hN)
    (fun g h => MassGap.WilsonAction.wilsonDensity_conj g h) β ω ν htend

#print axioms wilson_reflPositive_even_of_tendsto

/-- **⭐⭐⭐ B3, ON `halfSpaceAlg` ITSELF.**

    ReflPositiveOn (latticeReflection τ (2*p)) (halfSpaceAlg τ p) ν

— the statement this module's header names as the open obligation, on the DIRECTED UNION and not on
one fixed finite region. The submodule is supplied, not assumed, so `⊥` cannot satisfy it; it
contains the constants (`one_mem_halfSpaceAlg`) and every `halfLinkObs` of a link in the positive
half (`HalfSpaceAlgebra.halfLinkObs_mem`).

**⛔ THAT LAST LEMMA DOES NOT SHOW IT IS MORE THAN THE CONSTANTS.** `halfLinkObs_mem` is quantified
over an arbitrary `f : C(G, ℝ)`, and a constant `f` gives a constant member. Non-constancy needs a
SEPARATING `f` — which is exactly what `HalfSpaceAlgebra.shift_moves_halfLinkObs` takes as a
hypothesis rather than discharging. **`halfSpaceAlg_has_nonconstant` above supplies one**, at SU(3),
by `Re tr` against `CrossingIntegration.trace_gNeg`.

**⛔ AND IT IS FALSE AT `N ≤ 1`**: `SU 0` and `SU 1` are singletons, so `IConf (SU N)` is a singleton
and every observable is constant. No statement in this file carries `2 ≤ N`, so all of them admit
that case, and `halfSpaceAlg_has_nonconstant` is stated at `3` for that reason.

**What the caller now supplies is `hexh`, and it is not a positivity assumption.** Every finite set
of links must eventually lie inside the box — a property of the box family alone, satisfiable by any
increasing exhaustion of `ℤ⁴`. It replaces the fixed region `R₀` of
`reflPositive_limit_on_half_space`, and it is the hypothesis that statement was missing.

**⛔ STILL SUBSEQUENTIAL, AND STILL NOT TRANSLATION INVARIANT.** The limit is along an ultrafilter
refining `l`, as everywhere in `DLRLimit`. Translation invariance is `ShiftCompat` and a separate
obligation; `ReflectionShift.nu_T_of_reflection_invariant` is the route to it, since one translation
is the composite of the reflections at `2p` and `2p - 1`.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`; `4` is the dimension. The `0` is the sign in `0 ≤ φ`.-/
theorem reflPositive_limit_on_halfSpaceAlg
    {ι : Type*} (l : Filter ι) [l.NeBot] (τ : Fin 4) (p : ℤ)
    (box : ι → Finset MassGap.InfiniteLattice.ILink)
    (hbox : ∀ i, ∀ lk ∈ box i, ireflLink τ (2 * p) lk ∈ box i)
    (hexh : ∀ S : Finset MassGap.InfiniteLattice.ILink, ∀ᶠ i in l, S ⊆ box i)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    ∃ (u : Ultrafilter ι) (ν : MassGap.DLRLimit.State
        (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))),
      (u : Filter ι) ≤ l ∧
      (∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
        Filter.Tendsto (fun i => stateFree hφm hφ0 hφ2 β (box i) ω f)
          (u : Filter ι) (nhds (ν f))) ∧
      MassGap.InfiniteReflection.ReflPositiveOn
        (MassGap.LatticeReflection.latticeReflection τ (2 * p))
        (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν := by
  obtain ⟨u, ν, hle, htend⟩ :=
    MassGap.DLRLimit.exists_limit_state l (fun i => stateFree hφm hφ0 hφ2 β (box i) ω)
  haveI : (u : Filter ι).NeBot := u.neBot'
  exact ⟨u, ν, hle, htend,
    reflPositive_of_tendsto_halfSpaceAlg τ p box hbox
      (fun S => ((hexh S).filter_mono hle)) hφm hφ0 hφ2 hφc β ω ν htend⟩

#print axioms reflPositive_limit_on_halfSpaceAlg

/-- **THE FREE WEIGHT IS REFLECTION INVARIANT.** The action over `iplqAll` sees only links inside the
box, and there the abstract twist IS `ireflConf`, which the action does not see.

DERIVED: `c` is the caller's reflection constant, no longer pinned to an even `2p`; `4` is the
dimension. -/
theorem wtFree_twist {c : ℤ} (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ) :
    wtFree φ β Λ ω
        (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
          (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) u)
      = wtFree φ β Λ ω u := by
  unfold wtFree
  congr 2
  have h1 : MassGap.GibbsSpec.actionOn φ (iplqAll Λ)
      (MassGap.GibbsSpec.splice Λ
        (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
          (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) u) ω)
      = MassGap.GibbsSpec.actionOn φ (iplqAll Λ)
          (ireflConf τ c (MassGap.GibbsSpec.splice Λ u ω)) :=
    MassGap.GibbsSpec.actionOn_congr φ _ _ _
      (fun q hq l hl => splice_twist_eq_ireflConf hΛ ω u
        (MassGap.GibbsSpec.mem_plaqsIn.mp (mem_iplqAll.mp hq).1 l hl))
  rw [h1, action_iplqAll_ireflConf φ hφc τ c hΛ]

#print axioms wtFree_twist

/-- **⭐⭐ THE FREE-BOUNDARY STATE DOES NOT SEE THE REFLECTION.**

`IsReflectionInvariant` at one box, which `InfiniteReflection.isReflectionInvariant_of_tendsto` transports to the
limit. Unlike positivity this is asserted on ALL observables, where it is the true statement.

Change of variables along the measure-preserving twist, with the weight invariant by `wtFree_twist`.
`hfΛ` enters for the same reason as everywhere else: the twist and `ireflConf` agree only on the box.

DERIVED: `c` is the caller's reflection constant, no longer pinned to an even `2p`; `4` is the
dimension. -/
theorem specFree_reflection_invariant {c : ℤ}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    {f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ}
    (hfm : Measurable (fun u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ =>
      f (MassGap.GibbsSpec.splice Λ u ω)))
    (hagree : ∀ u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ,
      f (ireflConf τ c (MassGap.GibbsSpec.splice Λ u ω))
        = f (MassGap.GibbsSpec.splice Λ
            (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
              (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) u) ω)) :
    specFree (φ := φ) β Λ ω
        (fun u => f (ireflConf τ c (MassGap.GibbsSpec.splice Λ u ω)))
      = specFree (φ := φ) β Λ ω (fun u => f (MassGap.GibbsSpec.splice Λ u ω)) := by
  unfold specFree
  congr 1
  set θ := MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
    (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) with hθ
  have hmp : MeasureTheory.MeasurePreserving θ
      (MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N)))
      (MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))) :=
    MassGap.ActionSplit.twist_measurePreserving _ _ _
      (fun l => ilinkDagger_measurePreserving τ l.1)
  have hw : ∀ v, wtFree φ β Λ ω (θ v) = wtFree φ β Λ ω v :=
    fun v => wtFree_twist hΛ hφc β ω v
  have hrw : (fun u => f (ireflConf τ c (MassGap.GibbsSpec.splice Λ u ω))
      * wtFree φ β Λ ω u)
      = fun u => (fun v => f (MassGap.GibbsSpec.splice Λ v ω) * wtFree φ β Λ ω v) (θ u) := by
    funext u
    have h1 : f (ireflConf τ c (MassGap.GibbsSpec.splice Λ u ω))
        = f (MassGap.GibbsSpec.splice Λ (θ u) ω) := hagree u
    show f (ireflConf τ c (MassGap.GibbsSpec.splice Λ u ω)) * wtFree φ β Λ ω u
      = f (MassGap.GibbsSpec.splice Λ (θ u) ω) * wtFree φ β Λ ω (θ u)
    rw [h1, hw u]
  rw [hrw]
  exact MassGap.GibbsSpec.integral_comp_of_mp hmp (hfm.mul (measurable_wtFree hφm β Λ ω))

#print axioms specFree_reflection_invariant

/-- A reflection-stable box has a reflection-stable COMPLEMENT — by involutivity. -/
theorem not_mem_of_not_mem_box {c : ℤ} (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ)
    {l : ILink} (hl : l ∉ Λ) : ireflLink τ c l ∉ Λ := by
  intro hmem
  exact hl (by simpa [ireflLink_involutive τ c l] using hΛ _ hmem)

/-- **⭐ WITH A REFLECTION-SYMMETRIC BOUNDARY CONDITION THE TWO AGREE EVERYWHERE**, not only on the
box — which is what `IsReflectionInvariant` needs, since it quantifies over ALL observables.

Inside the box this is `splice_twist_eq_ireflConf`. Outside it, the box's complement is stable too,
so the splice reads `ω` on both sides and `hω` closes it.

It is satisfiable: the identity configuration is reflection-symmetric, because the dagger inverts `1`
to `1`. So this is a genuine condition on the boundary condition, not a vacuous one.

DERIVED: `c` is the caller's reflection constant, no longer pinned to an even `2p`; `4` is the
dimension. -/
theorem splice_twist_eq_ireflConf_everywhere {c : ℤ}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ)
    {ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)}
    (hω : ireflConf τ c ω = ω)
    (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ) :
    MassGap.GibbsSpec.splice Λ
        (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
          (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) u) ω
      = ireflConf τ c (MassGap.GibbsSpec.splice Λ u ω) := by
  funext l
  by_cases hl : l ∈ Λ
  · exact splice_twist_eq_ireflConf hΛ ω u hl
  · have himg : ireflLink τ c l ∉ Λ := not_mem_of_not_mem_box hΛ hl
    rw [MassGap.GibbsSpec.splice_not_mem hl]
    show ω l = _
    simp only [ireflConf, MassGap.GibbsSpec.splice_not_mem himg]
    conv_lhs => rw [← hω]
    simp only [ireflConf]

#print axioms splice_twist_eq_ireflConf_everywhere

/-- **⭐⭐ THE FREE-BOUNDARY STATE DOES NOT SEE THE REFLECTION**, on ALL observables —
`InfiniteReflection.IsReflectionInvariant`, which `invariant_of_tendsto` transports to the limit.

Unlike positivity this is asserted on every observable, where it is the true statement — and that is
exactly why the boundary condition has to be symmetric.

DERIVED: `c` is the caller's reflection constant, no longer pinned to an even `2p`; `4` is the
dimension. The `0` is the sign in `0 ≤ φ`.-/
theorem stateFree_reflection_invariant {c : ℤ}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    {ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)}
    (hω : ireflConf τ c ω = ω) :
    MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ c)
      (stateFree hφm hφ0 hφ2 β Λ ω) := by
  intro f
  exact specFree_reflection_invariant hΛ hφm hφc β ω (boxObs_measurable ω f)
    (fun u => congrArg f (splice_twist_eq_ireflConf_everywhere hΛ hω u).symm)

#print axioms stateFree_reflection_invariant

/-- **⭐⭐⭐ BOTH REFLECTION PROPERTIES OF THE INFINITE-VOLUME STATE, TOGETHER.**

`IsReflectionInvariant` AND `ReflPositiveOn` for the same limit state, along the same ultrafilter.
These are two of the three facts `WilsonTransferReduction` says the infinite-volume state owes:

    hinv : IsReflectionInvariant (latticeReflection τ (2*p)) ν      ← here
    hpos : ReflPositiveOn (latticeReflection τ (2*p)) A ν          ← here
    hnu  : ∀ f, ν (ishiftObsL τ f) = ν f                          ← NOT here

**⛔ THE THIRD IS A DIFFERENT ARGUMENT AND IS NOT CLAIMED.** Translation invariance does not follow
from the reflection, and the finite-volume free state is not translation invariant — the box breaks
it. That is `B2-shift`, and it stays open.

What the caller supplies remains structural: a finite region at or above the plane, reflection-stable
boxes containing it, a REFLECTION-SYMMETRIC boundary condition (the identity configuration is one),
and the Wilson density's own four properties.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`; `4` is the dimension. The `0` is the sign in `0 ≤ φ`.-/
theorem reflection_facts_of_limit
    {ι : Type*} (l : Filter ι) [l.NeBot] (τ : Fin 4) (p : ℤ)
    (R₀ : Finset MassGap.InfiniteLattice.ILink)
    (hR₀ : ∀ lk ∈ R₀, (ireflLink τ (2 * p) lk).2 τ ≤ lk.2 τ)
    (box : ι → Finset MassGap.InfiniteLattice.ILink)
    (hsub : ∀ i, R₀ ⊆ box i)
    (hbox : ∀ i, ∀ lk ∈ box i, ireflLink τ (2 * p) lk ∈ box i)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    {ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)}
    (hω : MassGap.LatticeReflection.ireflConf τ (2 * p) ω = ω) :
    ∃ (u : Ultrafilter ι) (ν : MassGap.DLRLimit.State
        (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))),
      (u : Filter ι) ≤ l ∧
      (∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
        Filter.Tendsto (fun i => stateFree hφm hφ0 hφ2 β (box i) ω f)
          (u : Filter ι) (nhds (ν f))) ∧
      MassGap.InfiniteReflection.IsReflectionInvariant
        (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν ∧
      MassGap.InfiniteReflection.ReflPositiveOn
        (MassGap.LatticeReflection.latticeReflection τ (2 * p)) (localSubmodule R₀) ν := by
  obtain ⟨u, ν, hle, htend, hrp⟩ :=
    reflPositive_limit_exists l τ p box hbox hφm hφ0 hφ2 hφc β ω (localSubmodule R₀)
      (fun i f hf U V h => hf U V (fun lk hlk => h lk (hsub i hlk)))
      (fun i f hf U V hS hR => by
        refine hf _ _ (fun lk hlk => ?_)
        have hlΛ : lk ∈ box i := hsub i hlk
        rw [MassGap.GibbsSpec.splice_mem hlΛ, MassGap.GibbsSpec.splice_mem hlΛ]
        rcases lt_or_eq_of_le (hR₀ lk hlk) with hlt | heq
        · exact hS _ (by simp only [boxS, Finset.mem_filter, Finset.mem_univ, true_and]; exact hlt)
        · exact hR _ (by simp only [boxR, Finset.mem_filter, Finset.mem_univ, true_and]; exact heq))
  haveI : (u : Filter ι).NeBot := u.neBot'
  refine ⟨u, ν, hle, htend, ?_, hrp⟩
  exact MassGap.InfiniteReflection.isReflectionInvariant_of_tendsto htend _
    (Filter.Eventually.of_forall (fun i =>
      stateFree_reflection_invariant (hbox i) hφm hφ0 hφ2 hφc β hω))

#print axioms reflection_facts_of_limit

/-- **⭐⭐⭐ B3 FOR THE WILSON MEASURE, AT A CONCRETE BOX FAMILY, WITH NO STRUCTURAL HYPOTHESIS LEFT.**

Everything above is stated for an abstract `φ : SU N → ℝ` with four properties — a class that also
contains `φ = 0`, the free theory — and for an assumed box family. This runs the chain once with
neither: `φ` is `WilsonAction.wilsonDensity` and the boxes are `symCube`, so the only hypotheses left
are the coupling `β`, the boundary configuration `ω`, and `N ≠ 0`.

The four density properties are `WilsonAction.measurable_wilsonDensity`, `wilsonDensity_nonneg`,
`wilsonDensity_le_two` and `wilsonDensity_conj`; the first needs nothing, the middle two need
`N ≠ 0`, the last nothing.

**⛔ `N ≠ 0` IS NOT ENOUGH FOR THE CARRIER TO BE NON-TRIVIAL.** At `N = 1` the group is a singleton,
so `IConf (SU 1)` is a singleton and `halfSpaceAlg` is the constants; the statement is then true and
empty. Non-triviality needs `2 ≤ N` and a separating function, neither of which this tree proves.

**⛔ AND THE LIMIT IS SUBSEQUENTIAL.** Along an ultrafilter refining `atTop`, as everywhere in
`DLRLimit`. No sequence is shown to converge, and none has to be:
`DLRLimit.exists_limit_state` is compactness.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`; `4` is the dimension. The `0` is the one in `N ≠ 0`.-/
theorem wilson_reflPositive_limit_exists (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    ∃ (u : Ultrafilter ℕ) (ν : MassGap.DLRLimit.State
        (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))),
      (∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
        Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p) n) ω f)
          (u : Filter ℕ) (nhds (ν f))) ∧
      MassGap.InfiniteReflection.ReflPositiveOn
        (MassGap.LatticeReflection.latticeReflection τ (2 * p))
        (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν := by
  obtain ⟨u, ν, -, htend, hpos⟩ :=
    reflPositive_limit_on_halfSpaceAlg (ι := ℕ) Filter.atTop τ p (symCube τ (2 * p))
      (fun n => symCube_refl_stable τ (2 * p) n) (fun S => symCube_exhausts τ (2 * p) S)
      MassGap.WilsonAction.measurable_wilsonDensity
      (MassGap.WilsonAction.wilsonDensity_nonneg hN)
      (MassGap.WilsonAction.wilsonDensity_le_two hN)
      (fun g h => MassGap.WilsonAction.wilsonDensity_conj g h) β ω
  exact ⟨u, ν, htend, hpos⟩

#print axioms wilson_reflPositive_limit_exists

/-! ## 6″. ⭐⭐⭐ What the operator side still owes -/



/-- **⭐⭐⭐ BOTH REFLECTION FACTS OF THE LIMIT STATE, ON THE HALF-SPACE ALGEBRA.**

`reflection_facts_of_limit` in the form `WilsonTransferReduction` actually consumes: positivity on
`halfSpaceAlg τ p` rather than on one fixed finite region. Invariance is unchanged —
`isReflectionInvariant_of_tendsto` over `stateFree_reflection_invariant` — and is why the boundary
condition must be reflection symmetric.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`; `4` is the dimension. The `0` is the sign in `0 ≤ φ`.-/
theorem reflection_facts_on_halfSpaceAlg
    {ι : Type*} (l : Filter ι) [l.NeBot] (τ : Fin 4) (p : ℤ)
    (box : ι → Finset MassGap.InfiniteLattice.ILink)
    (hbox : ∀ i, ∀ lk ∈ box i, ireflLink τ (2 * p) lk ∈ box i)
    (hexh : ∀ S : Finset MassGap.InfiniteLattice.ILink, ∀ᶠ i in l, S ⊆ box i)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    {ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)}
    (hω : MassGap.LatticeReflection.ireflConf τ (2 * p) ω = ω) :
    ∃ (u : Ultrafilter ι) (ν : MassGap.DLRLimit.State
        (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))),
      (u : Filter ι) ≤ l ∧
      (∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
        Filter.Tendsto (fun i => stateFree hφm hφ0 hφ2 β (box i) ω f)
          (u : Filter ι) (nhds (ν f))) ∧
      MassGap.InfiniteReflection.IsReflectionInvariant
        (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν ∧
      MassGap.InfiniteReflection.ReflPositiveOn
        (MassGap.LatticeReflection.latticeReflection τ (2 * p))
        (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν := by
  obtain ⟨u, ν, hle, htend⟩ :=
    MassGap.DLRLimit.exists_limit_state l (fun i => stateFree hφm hφ0 hφ2 β (box i) ω)
  haveI : (u : Filter ι).NeBot := u.neBot'
  refine ⟨u, ν, hle, htend, ?_,
    reflPositive_of_tendsto_halfSpaceAlg τ p box hbox
      (fun S => ((hexh S).filter_mono hle)) hφm hφ0 hφ2 hφc β ω ν htend⟩
  exact MassGap.InfiniteReflection.isReflectionInvariant_of_tendsto htend _
    (Filter.Eventually.of_forall (fun i =>
      stateFree_reflection_invariant (hbox i) hφm hφ0 hφ2 hφc β hω))

#print axioms reflection_facts_on_halfSpaceAlg

/-- **⭐⭐⭐ THE TRANSFER DATA OF AN INFINITE-VOLUME WILSON STATE, FROM REFLECTION FACTS ALONE.**

`WilsonTransferReduction.transferData_of_state_facts` takes three facts about the state. Two of them
`reflection_facts_on_halfSpaceAlg` supplies. The third, `hnu`, is translation invariance, and
`ReflectionShift.nu_T_of_reflection_invariant` derives it from reflection invariance at two ADJACENT
constants — one translation is two reflections.

**⛔ SO THE OPERATOR SIDE NOW OWES EXACTLY ONE FACT: `hinvOdd`** — reflection invariance of the
state at `2p - 1`, the ODD constant, which is the LINK reflection. Everything else is discharged.

**⛔⛔ AND THAT ONE FACT IS TRANSLATION INVARIANCE UNDER ANOTHER NAME.**
`ReflectionShift.reflection_invariant_succ_iff_nu_T` proves that, given `hinv`, `hinvOdd` and `hnu`
imply each other. Counting hypotheses makes this look like a reduction and it is not one: what
changed is the KIND of statement outstanding, not its difficulty. Do not report this as progress on
`hnu`.

What the change of kind is worth: `hinvOdd` is the same shape as `stateFree_reflection_invariant`,
which this file proves at finite volume at EVERY constant, whereas `hnu` has no finite-volume
counterpart at all — the box breaks translation invariance. It is an EQUALITY, so the `0 ≤ β`
restriction that makes the odd reflection a separate problem for `ReflPositiveOn`
(`CharacterExpansion.NegControl.su3_kernel_nonneg_iff`) does not touch it, and it transports to a
limit by `InfiniteReflection.isReflectionInvariant_of_tendsto`, the same lemma the even case uses.

**⛔ AND ONE BOX FAMILY CANNOT GIVE BOTH** — `eq_empty_of_stable_two_mirrors`. So the route needs
two families, one symmetric about each mirror, shown to have a common limit, which is the
boundary-independence argument and not an escape from it.
**`wilson_transferData_of_thermodynamic_limit` below discharges `hinvOdd` and re-parks the debt
there**, as a single convergence hypothesis; prefer it to this definition, whose `ν` is a free
parameter and therefore admits degenerate states.

**⛔ AND `ν` IS AN ARBITRARY STATE HERE, SO THE RESULT CAN BE RANK ONE.** Evaluation at the
all-identity configuration satisfies all three hypotheses at EVERY constant, even and odd, because
`ireflConf` inverts only on `τ`-links and `1⁻¹ = 1`; its form is `F ↦ F(1)·H(1)`, whose GNS space is
`ℝ`, whose transfer operator is the identity, and which has no gap. `TransferData`'s only
non-degeneracy field is `vac_norm`, and that holds there too. So this produces the OBJECT the
operator side needs and says nothing about its SPECTRUM — which is `TransferGap.GapAt`, carried
separately and still open. Tying `ν` to the Wilson measure is what
`reflection_facts_on_halfSpaceAlg`'s conjoined `Tendsto` clause does, and this definition does not
carry it.

DERIVED: the `2` and the `1` are the plane-to-constant conversion and the mirror separation; `4` is
the dimension. -/
noncomputable def transferData_of_reflection_facts (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hinvOdd : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p - 1)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν) :
    MassGap.Transfer.TransferData
      ↥(MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) :=
  MassGap.WilsonTransferReduction.transferData_of_state_facts τ p ν hinv hpos
    (fun f => MassGap.ReflectionShift.nu_T_of_reflection_invariant τ (2 * p - 1) ν hinvOdd
      (by rw [sub_add_cancel]; exact hinv) f)

#print axioms transferData_of_reflection_facts

/-- **⭐⭐⭐ THE WHOLE OPERATOR SIDE, FROM ONE ANALYTIC FACT AND NOTHING ELSE.**

Every structural hypothesis is discharged inside. `φ` is the Wilson density, the boundary condition
is the all-identity configuration (symmetric about every mirror by `ireflConf_one`), and the boxes
are `symCube` at each of the two constants — reflection-stable by `symCube_refl_stable` and
exhausting by `symCube_exhausts`. Positivity comes from `reflPositive_of_tendsto_halfSpaceAlg`,
invariance at each constant from `stateFree_reflection_invariant` at that constant, and translation
invariance from `ReflectionShift.nu_T_of_reflection_invariant`.

**⛔ WHAT IS ASSUMED IS EXACTLY ONE THING: THAT THE TWO FAMILIES CONVERGE TO THE SAME STATE.**
`hEven` and `hOdd` name the same `ν`. That is boundary independence of the infinite-volume limit, and
it is the open problem — not a technicality. It cannot be avoided by a cleverer box family:
`eq_empty_of_stable_two_mirrors` proves that a finite box stable under the mirrors at `2p` and
`2p - 1` is empty. So two families are forced **as long as the odd invariance is to come from a
finite-volume box statement**, and something must then identify their limits.

The two families also differ by a diagonal translation of their centre, not only by the mirror,
because `coordCube c n` is centred at `c` in every coordinate. The hypothesis is therefore boundary
independence across two differently-centred exhaustions.

Note also that convergence here is along `atTop` itself, not along a refining ultrafilter. Compactness
gives the latter for free (`DLRLimit.exists_limit_state`) but cannot give a COMMON limit for two
different families, which is why the hypothesis is stated as genuine convergence.

**⛔ AND THIS PRODUCES THE OBJECT, NOT A GAP.** `TransferData` carries no spectral content; the gap
is `TransferGap.GapAt` and is carried separately. At `N ≤ 1` the carrier is the constants and the
result is empty.

DERIVED: the `2` and the `1` are the plane-to-constant conversion and the mirror separation; `4` is
the dimension. The `0` is the one in `N ≠ 0`.-/
noncomputable def wilson_transferData_of_common_limit (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (hEven : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p) n) 1 f)
        Filter.atTop (nhds (ν f)))
    (hOdd : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p - 1) n) 1 f)
        Filter.atTop (nhds (ν f))) :
    MassGap.Transfer.TransferData
      ↥(MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) :=
  transferData_of_reflection_facts τ p ν
    (MassGap.InfiniteReflection.isReflectionInvariant_of_tendsto hEven _
      (Filter.Eventually.of_forall (fun n =>
        stateFree_reflection_invariant (symCube_refl_stable τ (2 * p) n)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN)
          (fun g h => MassGap.WilsonAction.wilsonDensity_conj g h) β
          (ireflConf_one τ (2 * p)))))
    (MassGap.InfiniteReflection.isReflectionInvariant_of_tendsto hOdd _
      (Filter.Eventually.of_forall (fun n =>
        stateFree_reflection_invariant (symCube_refl_stable τ (2 * p - 1) n)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN)
          (fun g h => MassGap.WilsonAction.wilsonDensity_conj g h) β
          (ireflConf_one τ (2 * p - 1)))))
    (reflPositive_of_tendsto_halfSpaceAlg τ p (symCube τ (2 * p))
      (fun n => symCube_refl_stable τ (2 * p) n)
      (fun S => symCube_exhausts τ (2 * p) S)
      MassGap.WilsonAction.measurable_wilsonDensity
      (MassGap.WilsonAction.wilsonDensity_nonneg hN)
      (MassGap.WilsonAction.wilsonDensity_le_two hN)
      (fun g h => MassGap.WilsonAction.wilsonDensity_conj g h) β 1 ν hEven)

#print axioms wilson_transferData_of_common_limit

/-- **THE TWO BOX SHAPES, INTERLEAVED INTO ONE SEQUENCE.** Even steps carry the mirror at `2p`, odd
steps the mirror at `2p + 1`, each at half the step index so both shapes still grow without bound.

DERIVED: the `2`s are the plane-to-constant conversion, the interleaving period and the halved
index; the `1` is the mirror separation; the `0` is the parity test `n % 2 = 0`; `4` is the
dimension. -/
noncomputable def mixCube (τ : Fin 4) (p : ℤ) (n : ℕ) : Finset MassGap.InfiniteLattice.ILink :=
  if n % 2 = 0 then symCube τ (2 * p) (n / 2) else symCube τ (2 * p - 1) (n / 2)

theorem mixCube_even (τ : Fin 4) (p : ℤ) (k : ℕ) :
    mixCube τ p (2 * k) = symCube τ (2 * p) k := by
  have h1 : (2 * k) % 2 = 0 := by omega
  have h2 : (2 * k) / 2 = k := by omega
  simp [mixCube, h1, h2]

#print axioms mixCube_even

theorem mixCube_odd (τ : Fin 4) (p : ℤ) (k : ℕ) :
    mixCube τ p (2 * k + 1) = symCube τ (2 * p - 1) k := by
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  simp [mixCube, h1, h2]

#print axioms mixCube_odd

/-- **THE EVEN SUBSEQUENCE OF `mixCube` IS THE EVEN CUBE FAMILY.** Stated as a lemma rather than
derived inside a proof because the forms below need it in a STATEMENT.

DERIVED: the `2`s are the plane-to-constant conversion and the interleaving period; the `0` is the
one in `N ≠ 0`; the `1` is the all-identity boundary condition; `4` is the dimension. -/
theorem tendsto_symCube_even_of_mixCube (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f))) :
    ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p) n) 1 f)
        Filter.atTop (nhds (ν f)) := by
  have hdouble : Filter.Tendsto (fun k : ℕ => 2 * k) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)
  intro f
  have h := (htend f).comp hdouble
  simp only [Function.comp_def, mixCube_even] at h
  exact h

#print axioms tendsto_symCube_even_of_mixCube

/-- **AND THE ODD SUBSEQUENCE IS THE ODD ONE.**

DERIVED: the `2`s are the plane-to-constant conversion and the interleaving period, the `1` the
mirror separation; the `0` is the one in `N ≠ 0`; the other `1` is the all-identity boundary
condition; `4` is the dimension. -/
theorem tendsto_symCube_odd_of_mixCube (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f))) :
    ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p - 1) n) 1 f)
        Filter.atTop (nhds (ν f)) := by
  have hdoubleSucc : Filter.Tendsto (fun k : ℕ => 2 * k + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)
  intro f
  have h := (htend f).comp hdoubleSucc
  simp only [Function.comp_def, mixCube_odd] at h
  exact h

#print axioms tendsto_symCube_odd_of_mixCube

/-- **⭐⭐ THE EVEN CONSTANT FROM THE INTERLEAVED FAMILY.** The even subsequence of `mixCube` IS
`symCube τ (2 * p)`, so one convergence hypothesis about `mixCube` gives the even-constant reflection
positivity.

DERIVED: the `2`s are the plane-to-constant conversion and the interleaving period; `4` is the
dimension. The `0` is the one in `N ≠ 0` and the `1` is the all-identity boundary condition. -/
theorem wilson_reflPositive_even_of_mixCube (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f))) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν :=
  wilson_reflPositive_even_of_tendsto τ p hN β 1 ν Filter.atTop le_rfl
    (tendsto_symCube_even_of_mixCube τ p hN β ν htend)

#print axioms wilson_reflPositive_even_of_mixCube

/-- **⭐⭐ AND THE ODD CONSTANT FROM THE SAME ONE.** The odd subsequence is `symCube τ (2 * p - 1)`.

DERIVED: the `2`s are the plane-to-constant conversion and the interleaving period, the `1` the
mirror separation; the `0` is the sign of the coupling; `4` is the dimension. -/
theorem wilson_reflPositive_odd_of_mixCube (τ : Fin 4) (p : ℤ) (hN : N ≠ 0)
    {β : ℝ} (hβ : 0 ≤ β)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f))) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p - 1))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν :=
  wilson_reflPositive_odd_of_tendsto τ p hN hβ 1 ν Filter.atTop le_rfl
    (tendsto_symCube_odd_of_mixCube τ p hN β ν htend)

#print axioms wilson_reflPositive_odd_of_mixCube


/-- **⛔ INTERLEAVING BUYS NOTHING UNDER COMPACTNESS.** Along any ultrafilter, `mixCube` is
eventually equal to one of the two box shapes, so an ultrafilter limit of the interleaved sequence is
a limit of a single shape and carries a single reflection constant.

**⛔ IT IS NOT A NO-GO, AND IT SAYS NOTHING ABOUT THE TWO SEPARATE FAMILIES.**
`wilson_reflPositive_limit_exists` and `wilson_reflPositive_limit_exists_odd` each produce a limit
state without mentioning `mixCube`, and nothing here forbids those two states from being equal — if
the DLR state were unique they would be. What this rules out is one specific attempt: reaching both
constants by taking an ultrafilter limit of the interleaved sequence. `atTop` works there
(`wilson_positiveTransfer_of_mixCube_limit`) precisely because it meets both parity classes
cofinally, which is convergence rather than compactness.

The `∨` is `Ultrafilter.mem_or_compl_mem`, the "at least one" half. Exclusivity is true and is
neither proved nor needed.

DERIVED: the `2`s are the plane-to-constant conversion, the interleaving period and the halved index,
the `1` the mirror separation; `4` is the dimension. The `0` of the parity test is in the proof, not
in the statement. -/
theorem mixCube_ultrafilter_sees_one_parity (τ : Fin 4) (p : ℤ) (u : Ultrafilter ℕ) :
    (∀ᶠ n in (u : Filter ℕ), mixCube τ p n = symCube τ (2 * p) (n / 2))
      ∨ (∀ᶠ n in (u : Filter ℕ), mixCube τ p n = symCube τ (2 * p - 1) (n / 2)) := by
  rcases u.mem_or_compl_mem {n : ℕ | n % 2 = 0} with h | h
  · refine Or.inl (Filter.Eventually.mono h (fun n hn => ?_))
    have hn' : n % 2 = 0 := hn
    show (if n % 2 = 0 then symCube τ (2 * p) (n / 2) else symCube τ (2 * p - 1) (n / 2))
      = symCube τ (2 * p) (n / 2)
    rw [if_pos hn']
  · refine Or.inr (Filter.Eventually.mono h (fun n hn => ?_))
    have hn' : ¬ (n % 2 = 0) := hn
    show (if n % 2 = 0 then symCube τ (2 * p) (n / 2) else symCube τ (2 * p - 1) (n / 2))
      = symCube τ (2 * p - 1) (n / 2)
    rw [if_neg hn']

#print axioms mixCube_ultrafilter_sees_one_parity



/-- **THE STATE IS REFLECTION-INVARIANT, AT WHATEVER CONSTANT THE FAMILY IS CLOSED UNDER.**

Each finite-volume state is invariant because the all-identity boundary condition is fixed by every
mirror (`ireflConf_one`) and the Wilson density is conjugation-invariant, and invariance passes to
limits. Generic in the constant, so it serves both `2p` and `2p - 1`.

DERIVED: `c` is the caller's reflection constant; the `0` is the one in `N ≠ 0`; the `1` is the
all-identity boundary condition; `4` is the dimension. -/
theorem wilson_reflInvariant_of_tendsto (τ : Fin 4) (c : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (l : Filter ℕ) [l.NeBot]
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ c n) 1 f)
        l (nhds (ν f))) :
    MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ c) ν :=
  MassGap.InfiniteReflection.isReflectionInvariant_of_tendsto htend _
    (Filter.Eventually.of_forall (fun n =>
      stateFree_reflection_invariant (symCube_refl_stable τ c n)
        MassGap.WilsonAction.measurable_wilsonDensity
        (MassGap.WilsonAction.wilsonDensity_nonneg hN)
        (MassGap.WilsonAction.wilsonDensity_le_two hN)
        (fun g h => MassGap.WilsonAction.wilsonDensity_conj g h) β (ireflConf_one τ c)))

#print axioms wilson_reflInvariant_of_tendsto

/-- **AND THE STATE DOES NOT SEE A TRANSLATION** — `hnu`, from the two invariances.

`ReflectionShift.nu_T_of_reflection_invariant`: a translation is the composite of the mirrors at `a`
and `a + 1`, so invariance under both adjacent mirrors IS translation invariance. Here `a = 2p - 1`,
so the two mirrors are the odd and the even one, and each family supplies its own.

**⛔ NO SINGLE FAMILY GIVES BOTH** — `eq_empty_of_stable_two_mirrors`. That is why this takes two
convergence hypotheses and not one.

DERIVED: the `2` is the plane-to-constant conversion and the `1` the mirror separation; the `0` is
the one in `N ≠ 0`; the other `1` is the all-identity boundary condition; `4` is the dimension. -/
theorem wilson_nu_T_of_tendsto (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (lE lO : Filter ℕ) [lE.NeBot] [lO.NeBot]
    (hEven : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p) n) 1 f)
        lE (nhds (ν f)))
    (hOdd : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p - 1) n) 1 f)
        lO (nhds (ν f))) :
    ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f := by
  have hEvenInv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p - 1 + 1)) ν := by
    rw [show (2 * p - 1 + 1 : ℤ) = 2 * p from by ring]
    exact wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν lE hEven
  exact MassGap.ReflectionShift.nu_T_of_reflection_invariant τ (2 * p - 1) ν
    (wilson_reflInvariant_of_tendsto τ (2 * p - 1) hN β ν lO hOdd) hEvenInv

#print axioms wilson_nu_T_of_tendsto

/-- **⭐⭐⭐ `PositiveTransfer` FROM TWO CONVERGENCE FACTS AND NOTHING ELSE.**

The two cube families need only share ONE state, and they may reach it along DIFFERENT filters. Each
filter refines `atTop` solely so that `hexh` and `hR` transport; nothing else about it is used. The
reflection invariance and the translation invariance are DISCHARGED here, not assumed —
`wilson_reflInvariant_of_tendsto` at each constant and `wilson_nu_T_of_tendsto` from the pair — so
what is left is two limits, two filter refinements, `0 ≤ β` and `N ≠ 0`.

**⛔ WHAT IS OPEN IS THAT THE TWO LIMITS CAN BE CHOSEN EQUAL.** Compactness already hands each family
a subsequential limit with its own reflection constant — `wilson_reflPositive_limit_exists`
unconditionally, `wilson_reflPositive_limit_exists_odd` under `0 ≤ β` — and nothing identifies the
two states. `eq_empty_of_stable_two_mirrors` shows no single family carries both constants, so the
two families are forced. Convergence along `atTop` is one sufficient condition
(`wilson_positiveTransfer_of_mixCube_limit`); uniqueness of the DLR state would be another. Neither
is proved here.

**⛔ AND AT `N ≤ 1` IT HOLDS OF A ONE-DIMENSIONAL CARRIER.** `halfSpaceAlg_has_nonconstant` is the
witness at SU(3).

DERIVED: the `2` is the plane-to-constant conversion and the `1` the mirror separation; the `0` is
the sign of the coupling and the one in `N ≠ 0`; the other `1` is the all-identity boundary
condition; `4` is the dimension. -/
theorem wilson_positiveTransfer_of_common_subsequential_limit (τ : Fin 4) (p : ℤ) (hN : N ≠ 0)
    {β : ℝ} (hβ : 0 ≤ β)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (lE lO : Filter ℕ) [lE.NeBot] [lO.NeBot]
    (hlE : lE ≤ Filter.atTop) (hlO : lO ≤ Filter.atTop)
    (hEven : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p) n) 1 f)
        lE (nhds (ν f)))
    (hOdd : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p - 1) n) 1 f)
        lO (nhds (ν f))) :
    MassGap.GNSHilbert.PositiveTransfer
      (MassGap.WilsonTransferReduction.transferData_of_state_facts τ p ν
        (wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν lE hEven)
        (wilson_reflPositive_even_of_tendsto τ p hN β 1 ν lE hlE hEven)
        (wilson_nu_T_of_tendsto τ p hN β ν lE lO hEven hOdd)) :=
  (MassGap.WilsonTransferReduction.positiveTransfer_iff_odd_reflPositive τ p ν
      (wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν lE hEven)
      (wilson_reflPositive_even_of_tendsto τ p hN β 1 ν lE hlE hEven)
      (wilson_nu_T_of_tendsto τ p hN β ν lE lO hEven hOdd)).mpr
    (wilson_reflPositive_odd_of_tendsto τ p hN hβ 1 ν lO hlO hOdd)

#print axioms wilson_positiveTransfer_of_common_subsequential_limit

/-- **THE TWO SHIFT OPERATORS ARE THE SAME MAP.** `HalfSpaceAlgebra.ishiftObsCM` and
`ReflectionShift.ishiftObsL` have identical bodies — precomposition with `InfiniteShift.ishiftConf` —
in two namespaces, so a lemma proved about one is inert on the other and nothing in a goal display
tells them apart. The same bridge `gibbs_ishift_eq` records for `ishift`.

**⛔ IT IS LOAD-BEARING.** `shift_no_finite_order_on_halfSpaceAlg` is about the first;
`TransferData.T` is built by `TransferAssembly.restrictT` from the second. Without this the step
between them is an unrecorded coincidence.

DERIVED: no numeral of its own; `4` is the dimension. -/
theorem ishiftObsCM_eq_ishiftObsL (τ : Fin 4) :
    (MassGap.HalfSpaceAlgebra.ishiftObsCM (G := MassGap.SUN.SU N) τ)
      = MassGap.ReflectionShift.ishiftObsL τ := rfl

#print axioms ishiftObsCM_eq_ishiftObsL

/-- **⭐⭐ THE TRANSFER OPERATOR MOVES SOMETHING, ON THIS CARRIER.**

The assembled data's `T` is not the identity on `halfSpaceAlg`: `shift_no_finite_order_on_halfSpaceAlg`
at `k = 1` supplies a member the shift moves, and `TransferAssembly.restrictT_coe` carries that
through the restriction.

**⛔ SO `GNSHilbert.positiveTransfer_of_T_eq_id` DOES NOT REACH THIS CARRIER**, where it discharges
`PositiveTransfer` for every other `TransferData` in the tree. Positivity here is
`wilson_positiveTransfer_of_common_subsequential_limit`'s to supply, and it is a real condition.

**⛔ AND IT IS NOT `TransferMovesSomething`.** Motion in the ALGEBRA is not motion in the GNS
QUOTIENT: `opT [F] = [F]` whenever `T F - F` lies in the null space of the form, and nothing here
rules that out. `HalfSpaceAlgebra.shift_no_finite_order_on_halfSpaceAlg` carries the same caveat.

**⛔ AND IT NEEDS A SEPARATING FUNCTION ON THE GROUP**, which is a real hypothesis: at `SU 0` and
`SU 1` the group is a singleton and none exists. `CrossingIntegration.trace_gNeg` supplies one at
`SU(3)`, where `Re tr` separates `gNeg` from the identity.

DERIVED: the `2` is the plane-to-constant conversion; the `1` is the single shift step; `4` is the
dimension. -/
theorem transferData_of_state_facts_T_ne_id (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν)
    (hnu : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f)
    {f : C(MassGap.SUN.SU N, ℝ)} {g₀ g₁ : MassGap.SUN.SU N} (hf : f g₀ ≠ f g₁) :
    ∃ F : ↥(MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p),
      (MassGap.WilsonTransferReduction.transferData_of_state_facts τ p ν hinv hpos hnu).T F
        ≠ F := by
  obtain ⟨F, hFmem, hFne⟩ :=
    MassGap.HalfSpaceAlgebra.shift_no_finite_order_on_halfSpaceAlg τ p hf (k := 1) one_pos
  refine ⟨⟨F, hFmem⟩, fun h => hFne ?_⟩
  rw [Function.iterate_one]
  exact congrArg Subtype.val h

#print axioms transferData_of_state_facts_T_ne_id

/-- **⭐⭐⭐ `PositiveTransfer` FROM ONE CONVERGENCE HYPOTHESIS, AT ONE FAMILY.**

`wilson_positiveTransfer_of_common_subsequential_limit` at `lE = lO = atTop`, with the two
convergence facts read off the interleaved family's even and odd subsequences. Both reflection
constants therefore come from ONE hypothesis, and the reflection and translation invariances are
discharged as they are there.

**⛔ WHY INTERLEAVING IS NEEDED AT ALL.** `eq_empty_of_stable_two_mirrors` proves no nonempty box is
stable under two adjacent mirrors, so `symCube τ (2 * p)` and `symCube τ (2 * p - 1)` are different
families and assuming both converge to one state would be an assumption. Subsequences of one
convergent sequence converge to one limit for free — but only along a filter meeting both parity
classes cofinally, which `mixCube_ultrafilter_sees_one_parity` shows an ultrafilter does not.

**⛔ AND AT `N ≤ 1` IT HOLDS OF A ONE-DIMENSIONAL CARRIER.** `halfSpaceAlg_has_nonconstant` is the
witness at SU(3).

DERIVED: the `2`s are the plane-to-constant conversion and the interleaving period, the `1` the
mirror separation; the `0` is the sign of the coupling and the one in `N ≠ 0`; the other `1` is the
all-identity boundary condition; `4` is the dimension. -/
theorem wilson_positiveTransfer_of_mixCube_limit (τ : Fin 4) (p : ℤ) (hN : N ≠ 0)
    {β : ℝ} (hβ : 0 ≤ β)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f))) :
    MassGap.GNSHilbert.PositiveTransfer
      (MassGap.WilsonTransferReduction.transferData_of_state_facts τ p ν
        (wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν Filter.atTop (tendsto_symCube_even_of_mixCube τ p hN β ν htend))
        (wilson_reflPositive_even_of_tendsto τ p hN β 1 ν Filter.atTop le_rfl (tendsto_symCube_even_of_mixCube τ p hN β ν htend))
        (wilson_nu_T_of_tendsto τ p hN β ν Filter.atTop Filter.atTop (tendsto_symCube_even_of_mixCube τ p hN β ν htend) (tendsto_symCube_odd_of_mixCube τ p hN β ν htend))) :=
  wilson_positiveTransfer_of_common_subsequential_limit τ p hN hβ ν
    Filter.atTop Filter.atTop le_rfl le_rfl (tendsto_symCube_even_of_mixCube τ p hN β ν htend) (tendsto_symCube_odd_of_mixCube τ p hN β ν htend)

#print axioms wilson_positiveTransfer_of_mixCube_limit

/-- **⭐⭐⭐ THE OPERATOR SIDE FROM ONE CONVERGENCE HYPOTHESIS, AND IT IS THE STANDARD ONE.**

`wilson_transferData_of_common_limit` asks that two families converge to the SAME state, which reads
like a uniqueness assumption. It is not one. Interleaving the two box shapes into a single sequence
makes the sharing automatic: if `mixCube` converges, its even and odd subsequences converge to the
same limit because they are subsequences of one convergent sequence.

**⛔ SO WHAT THE OPERATOR SIDE OWES IS EXISTENCE OF THE THERMODYNAMIC LIMIT** along one exhausting
family of boxes with the all-identity boundary condition — the canonical hypothesis of lattice gauge
theory, not a technicality of this construction and not a uniqueness claim.

Compactness gives convergence along a refining ULTRAFILTER for free
(`DLRLimit.exists_limit_state`); what it does not give is convergence along `atTop` itself, and the
difference is exactly what is assumed here.

**⛔ AND IT PRODUCES THE OBJECT, NOT A GAP.** `TransferData` carries no spectral content. At
`N ≤ 1` the carrier is the constants and the result is empty.

DERIVED: the `2` is the plane-to-constant conversion; `4` is the dimension. The `0` is the one in `N ≠ 0` and the `1` is the all-identity boundary condition.-/
noncomputable def wilson_transferData_of_thermodynamic_limit
    (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f))) :
    MassGap.Transfer.TransferData
      ↥(MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) := by
  have hdouble : Filter.Tendsto (fun k : ℕ => 2 * k) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)
  have hdoubleSucc : Filter.Tendsto (fun k : ℕ => 2 * k + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)
  refine wilson_transferData_of_common_limit τ p hN β ν (fun f => ?_) (fun f => ?_)
  · have h := (htend f).comp hdouble
    simp only [Function.comp_def, mixCube_even] at h
    exact h
  · have h := (htend f).comp hdoubleSucc
    simp only [Function.comp_def, mixCube_odd] at h
    exact h

#print axioms wilson_transferData_of_thermodynamic_limit

/-- **⭐⭐⭐ THE OPERATOR-SIDE GAP FROM A PURELY FINITE-VOLUME INEQUALITY.**

For every `F` in the half-space algebra, eventually along the box family, with each box subtracting
ITS OWN mean:

    ⟨θ_{2p-2} F · F⟩ₙ - ⟨F⟩ₙ⟨θ_{2p-2} F⟩ₙ  ≤  r² · ( ⟨θ_{2p} F · F⟩ₙ - ⟨F⟩ₙ⟨θ_{2p} F⟩ₙ )

where `⟨·⟩ₙ` is `stateFree` at `box n` with the all-identity boundary condition. Then the
infinite-volume transfer data has a gap at `r`.

**⛔ NOTHING IN THE HYPOTHESIS MENTIONS THE LIMIT STATE.** That is the point of this form. Both
sides are CONNECTED two-point functions of one explicit finite integral — `stateFree` is `specFree`
normalised, and `specFree` is a ratio of two Bochner integrals of `wtFree` over the box's product
Haar measure. `InfiniteReflection.state_pairing_subtracted` is what makes the two ends meet: the
vacuum-subtracted pairing IS the connected correlator, so each box's connected pairing converges to
the limit state's term by term.

**⛔ AND THERE IS NO SIDE CONDITION TO DROP.** At `F = 1` both sides are `0`, so the collapse that
makes an UNSUBTRACTED decay hypothesis contradictory — `1 ≤ r²`, whence
`TransferGap.gapAt_of_one_le_sq` gives the conclusion for free — cannot arise here. The subtraction
is built into the statement rather than carried as a premise.

**⛔ IT IS STILL THE MASS GAP.** Nothing here makes the hypothesis true. It says the connected
two-step reflection pairing decays by `r²` against the connected zero-step one, uniformly in the
volume. That is exponential clustering, and it is the physics.

DERIVED: the `2`s are the plane-to-constant conversion and the two-step separation, the `1` is the
all-identity boundary condition; `4` is the dimension. The `0` is the one in `N ≠ 0`.-/
theorem gapAt_of_finite_volume_connected (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) (r : ℝ)
    (box : ℕ → Finset MassGap.InfiniteLattice.ILink)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν)
    (hnu : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f)
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) β (box n) 1 f) Filter.atTop (nhds (ν f)))
    (hfin : ∀ F ∈ MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p,
      ∀ᶠ n in Filter.atTop,
        stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) β (box n) 1 (MassGap.LatticeReflection.ireflObs τ (2 * p - 2) F * F)
            - stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) β (box n) 1 F * stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) β (box n) 1 (MassGap.LatticeReflection.ireflObs τ (2 * p - 2) F)
          ≤ r ^ 2 * (stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) β (box n) 1 (MassGap.LatticeReflection.ireflObs τ (2 * p) F * F)
            - stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) β (box n) 1 F * stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) β (box n) 1 (MassGap.LatticeReflection.ireflObs τ (2 * p) F))) :
    MassGap.TransferGap.GapAt
      (MassGap.WilsonTransferReduction.transferData_of_state_facts τ p ν hinv hpos hnu) r :=
  (MassGap.WilsonTransferReduction.gapAt_iff_subtracted_pairing τ p ν hinv hpos hnu r).mpr
    (MassGap.InfiniteReflection.connected_pairing_le_of_eventually htend
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.LatticeReflection.latticeReflection τ (2 * p - 2))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) r hfin)

#print axioms gapAt_of_finite_volume_connected

end StateAlgebra

end Split

/-! ## 4. The obligation, stated correctly -/

section Obligation

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]

/-- **B3, IN THE FORM THAT IS NOT FALSE BY CONSTRUCTION.** The reflection constant must be twice the
plane.

Nothing here supplies it. What is supplied is the shape: an attempt against
`ReflPositiveOn (latticeReflection τ c) (halfSpaceAlg τ c)` would be attempting a statement whose
geometry does not hold.

DERIVED: the `2` is `reflection_exchanges_halves`'s plane-to-constant conversion; `4` is the
dimension. -/
def HalfSpaceReflPositive (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G)) : Prop :=
  MassGap.InfiniteReflection.ReflPositiveOn
    (MassGap.LatticeReflection.latticeReflection τ (2 * p))
    (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := G) τ p) ν

end Obligation

end MassGap.ReflectionHalfSpace
