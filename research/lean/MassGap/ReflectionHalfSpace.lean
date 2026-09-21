import Mathlib
import MassGap.HalfSpaceAlgebra
import MassGap.ReflectionShift
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

`c = 2p` is EVEN, so the pairing that makes sense here is the even reflection constant — matching
`ReflectStrong`, which records that the even constant (site reflection) and the odd one (link
reflection) are different problems, the odd one needing `0 ≤ β` with
`CharacterExpansion.NegControl.su3_kernel_nonneg_iff` refuting it at `β < 0`. The odd case
corresponds to a plane at a half-integer, which `posHalf` — indexed by an integer — cannot express.
**So `halfSpaceAlg` as defined reaches only the even reflections.**
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

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`; `4` is the dimension. -/
def ireflBox (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ) : ↥Λ → ↥Λ :=
  fun l => ⟨ireflLink τ (2 * p) l.1, hΛ l.1 l.2⟩

theorem ireflBox_involutive (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ) :
    Function.Involutive (ireflBox (τ := τ) (p := p) hΛ) := by
  intro l
  refine Subtype.ext ?_
  simpa [ireflBox] using ireflLink_involutive τ (2 * p) l.1

/-- **AND SO IT IS A PERMUTATION OF THE BOX** — the `θ` at the index `ActionSplit` takes.

DERIVED: no numeral of its own. -/
def ireflBoxPerm (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ) : Equiv.Perm ↥Λ :=
  (ireflBox_involutive hΛ).toPerm _

@[simp] theorem ireflBoxPerm_coe (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ) (l : ↥Λ) :
    ((ireflBoxPerm hΛ l : ↥Λ) : ILink) = ireflLink τ (2 * p) l.1 := rfl

#print axioms ireflBoxPerm

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

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`; `4` is the dimension. -/
theorem ireflPlaq_mem_iplqAll (τ : Fin 4) (p : ℤ) {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ) {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ iplqAll Λ) : ireflPlaq τ (2 * p) q ∈ iplqAll Λ := by
  obtain ⟨hin, hne⟩ := mem_iplqAll.mp hq
  refine mem_iplqAll.mpr ⟨ireflPlaq_mem_plaqsIn τ (2 * p) hΛ
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

DERIVED: the `2` is the plane-to-constant conversion; `4` is the dimension. -/
theorem action_iplqAll_ireflConf (φ : G → ℝ) (hφ : ∀ g h : G, φ (g * h * g⁻¹) = φ h)
    (τ : Fin 4) (p : ℤ) {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ) (U : MassGap.GibbsSpec.IConf G) :
    MassGap.GibbsSpec.actionOn φ (iplqAll Λ) (ireflConf τ (2 * p) U)
      = MassGap.GibbsSpec.actionOn φ (iplqAll Λ) U := by
  unfold MassGap.GibbsSpec.actionOn
  refine Finset.sum_nbij' (i := fun q => ireflPlaq τ (2 * p) q)
    (j := fun q => ireflPlaq τ (2 * p) q)
    (fun a ha => ireflPlaq_mem_iplqAll τ p hΛ ha)
    (fun b hb => ireflPlaq_mem_iplqAll τ p hΛ hb)
    (fun a _ => ireflPlaq_involutive τ (2 * p) a)
    (fun b _ => ireflPlaq_involutive τ (2 * p) b)
    (fun a _ => ?_)
  obtain ⟨g, hg⟩ := ihol_ireflConf τ (2 * p) a U
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

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`; `4` is the dimension. -/
theorem splice_twist_eq_ireflConf (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ)
    {l : ILink} (hl : l ∈ Λ) :
    MassGap.GibbsSpec.splice Λ
        (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
          (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) u) ω l
      = ireflConf τ (2 * p) (MassGap.GibbsSpec.splice Λ u ω) l := by
  have himg : ireflLink τ (2 * p) l ∈ Λ := hΛ l hl
  rw [MassGap.GibbsSpec.splice_mem hl]
  have hperm : (ireflBoxPerm hΛ ⟨l, hl⟩ : ↥Λ) = ⟨ireflLink τ (2 * p) l, himg⟩ :=
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

**⛔ AND `localSubmodule R₀` IS NOT THE HALF-SPACE ALGEBRA, WHICH MATTERS FOR WHAT THIS CLOSES.**
`HalfSpaceAlgebra.halfSpaceAlg τ c` is a DIRECTED UNION over all finite supports in the positive
half; `localSubmodule R₀` is ONE fixed finite support. Reflection positivity on the second is
strictly weaker, and this method cannot reach the first, because `hAloc` is quantified `∀ i` rather
than eventually — an observable whose support escapes `box i` breaks it. No lemma relating the two
exists in this tree.

**⛔ AND AT `R₀ = ∅` THE SUBMODULE IS EXACTLY THE CONSTANTS.** The carrier reads `∀ U V, f U = f V`
there, and every hypothesis is vacuously satisfied. So excluding `⊥` is not enough on its own; the
content comes from `R₀` being nonempty AND from the convergence clause, which is what ties `ν` to the
Wilson measure. No declaration in this tree yet exhibits a NON-CONSTANT member of `localSubmodule`.

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

/-- **THE FREE WEIGHT IS REFLECTION INVARIANT.** The action over `iplqAll` sees only links inside the
box, and there the abstract twist IS `ireflConf`, which the action does not see.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`; `4` is the dimension. -/
theorem wtFree_twist (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
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
          (ireflConf τ (2 * p) (MassGap.GibbsSpec.splice Λ u ω)) :=
    MassGap.GibbsSpec.actionOn_congr φ _ _ _
      (fun q hq l hl => splice_twist_eq_ireflConf hΛ ω u
        (MassGap.GibbsSpec.mem_plaqsIn.mp (mem_iplqAll.mp hq).1 l hl))
  rw [h1, action_iplqAll_ireflConf φ hφc τ p hΛ]

#print axioms wtFree_twist

/-- **⭐⭐ THE FREE-BOUNDARY STATE DOES NOT SEE THE REFLECTION.**

`IsReflectionInvariant` at one box, which `InfiniteReflection.isReflectionInvariant_of_tendsto` transports to the
limit. Unlike positivity this is asserted on ALL observables, where it is the true statement.

Change of variables along the measure-preserving twist, with the weight invariant by `wtFree_twist`.
`hfΛ` enters for the same reason as everywhere else: the twist and `ireflConf` agree only on the box.

DERIVED: the `2` is the plane-to-constant conversion; `4` is the dimension. -/
theorem specFree_reflection_invariant
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    {f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ}
    (hfm : Measurable (fun u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ =>
      f (MassGap.GibbsSpec.splice Λ u ω)))
    (hagree : ∀ u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ,
      f (ireflConf τ (2 * p) (MassGap.GibbsSpec.splice Λ u ω))
        = f (MassGap.GibbsSpec.splice Λ
            (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
              (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) u) ω)) :
    specFree (φ := φ) β Λ ω
        (fun u => f (ireflConf τ (2 * p) (MassGap.GibbsSpec.splice Λ u ω)))
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
  have hrw : (fun u => f (ireflConf τ (2 * p) (MassGap.GibbsSpec.splice Λ u ω))
      * wtFree φ β Λ ω u)
      = fun u => (fun v => f (MassGap.GibbsSpec.splice Λ v ω) * wtFree φ β Λ ω v) (θ u) := by
    funext u
    have h1 : f (ireflConf τ (2 * p) (MassGap.GibbsSpec.splice Λ u ω))
        = f (MassGap.GibbsSpec.splice Λ (θ u) ω) := hagree u
    show f (ireflConf τ (2 * p) (MassGap.GibbsSpec.splice Λ u ω)) * wtFree φ β Λ ω u
      = f (MassGap.GibbsSpec.splice Λ (θ u) ω) * wtFree φ β Λ ω (θ u)
    rw [h1, hw u]
  rw [hrw]
  exact MassGap.GibbsSpec.integral_comp_of_mp hmp (hfm.mul (measurable_wtFree hφm β Λ ω))

#print axioms specFree_reflection_invariant

/-- A reflection-stable box has a reflection-stable COMPLEMENT — by involutivity. -/
theorem not_mem_of_not_mem_box (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {l : ILink} (hl : l ∉ Λ) : ireflLink τ (2 * p) l ∉ Λ := by
  intro hmem
  exact hl (by simpa [ireflLink_involutive τ (2 * p) l] using hΛ _ hmem)

/-- **⭐ WITH A REFLECTION-SYMMETRIC BOUNDARY CONDITION THE TWO AGREE EVERYWHERE**, not only on the
box — which is what `IsReflectionInvariant` needs, since it quantifies over ALL observables.

Inside the box this is `splice_twist_eq_ireflConf`. Outside it, the box's complement is stable too,
so the splice reads `ω` on both sides and `hω` closes it.

It is satisfiable: the identity configuration is reflection-symmetric, because the dagger inverts `1`
to `1`. So this is a genuine condition on the boundary condition, not a vacuous one.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`; `4` is the dimension. -/
theorem splice_twist_eq_ireflConf_everywhere
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)}
    (hω : ireflConf τ (2 * p) ω = ω)
    (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ) :
    MassGap.GibbsSpec.splice Λ
        (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
          (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) u) ω
      = ireflConf τ (2 * p) (MassGap.GibbsSpec.splice Λ u ω) := by
  funext l
  by_cases hl : l ∈ Λ
  · exact splice_twist_eq_ireflConf hΛ ω u hl
  · have himg : ireflLink τ (2 * p) l ∉ Λ := not_mem_of_not_mem_box hΛ hl
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

DERIVED: the `2` is the plane-to-constant conversion; `4` is the dimension. -/
theorem stateFree_reflection_invariant
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    {ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)}
    (hω : ireflConf τ (2 * p) ω = ω) :
    MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
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

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`; `4` is the dimension. -/
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
