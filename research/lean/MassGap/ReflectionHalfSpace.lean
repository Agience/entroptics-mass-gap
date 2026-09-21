import Mathlib
import MassGap.HalfSpaceAlgebra
import MassGap.ReflectionShift

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

/-! ## 3. The obligation, stated correctly -/

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
