import Mathlib
import MassGap.InfiniteReflection
import MassGap.InfiniteLattice

/-!
# MassGap.LatticeReflection — the reflection of the infinite lattice, as a `Reflection`

`InfiniteReflection` proves that reflection positivity on a submodule and reflection invariance both
pass to a limit state, and builds a `Transfer.ReflForm` from them — but against an ABSTRACT
`Reflection`, constructing none. **This file constructs the lattice instance.**

## The convention is `Reflect`'s, over `ℤ`, INCLUDING THE DAGGER

`MassGap.Reflect` reflects the torus by `x_τ ↦ c − x_τ` (`reflSite`), links by

    reflLink τ c (μ, x) = (μ, if μ = τ then reflSite τ (c−1) x else reflSite τ c x)

— the base shift by one because a `τ`-link spans `[x_τ, x_τ+1]` so its mirror spans
`[c−1−x_τ, c−x_τ]` — and **configurations with an inverse on the `τ`-links**:

    reflConf τ c U = fun l => if l.1 = τ then (U (reflLink τ c l))⁻¹ else U (reflLink τ c l).

`Reflect`'s own docstring is explicit about why the inverse is not optional: *"A `τ`-link is
traversed BACKWARDS by the mirrored loop, so the reflection carries a DAGGER on those links …
**Without it the action is not invariant** … This is exactly the `†` that appears in the
Osterwalder–Seiler time reflection."*

`ireflConf` below carries it, which is why this file needs `[Group G]` and `[ContinuousInv G]` where
`InfiniteShift` needed neither: the shift permutes links, the reflection reverses them.

**What `Fin n` supplied and `ℤ` does not is periodicity.** The reflection map does not need it —
`c − x` and `c − 1 − x` are subtraction, which `ℤ` has. Every POSITIVITY theorem stated about the
reflection upstream does need it, and none of them is transported here; see the limits below.

## What this delivers

`latticeReflection τ c : InfiniteReflection.Reflection (IConf G)` — all four fields proved. So for a
reflection-positive, reflection-invariant state on `IConf G` and a half-space submodule,
`InfiniteReflection.stateReflForm` gives a `Transfer.ReflForm`, and hence `GNSHilbert`'s Hilbert
space and vacuum.

**Not the operator.** `GNSHilbert.opT` is defined against a full `Transfer.TransferData`, not against
a `ReflForm`; a form alone does not lift an operator, and no `TransferData` exists here.

## ⚠ What is NOT delivered, stated precisely

**No Wilson state is shown reflection-positive for this reflection**, and the gap is wider than a
change of lattice:

* `Complete.wilson_reflection_positive_at` is not a statement about a form at all — it asserts
  nonnegativity of the correlation SEQUENCE `wilsonCorrAt`. The form-level fact is
  `ReflectStrong.wilsonGibbsReflForm`'s `form_nonneg`, which lives on the SLAB algebra
  `localObs (blkS τ a m) (blkR τ a m)` of a PERIODIC lattice, at `n = 2*m`, and at the EVEN
  reflection constant `a + a`.
* `ReflectStrong` records that the site reflection (`c` even) and the link reflection (`c` odd) are
  different problems, that the odd case is `OddLagSplit`'s with a different three-block
  decomposition, and that it genuinely needs `0 ≤ β` — with
  `CharacterExpansion.NegControl.su3_kernel_nonneg_iff` refuting it at `β < 0`.

`latticeReflection τ c` ranges over every `c : ℤ`, **including the parities for which finite-volume
positivity is known to fail**. So supplying `ReflPositiveOn` here is not a translation of an existing
result: it needs a half-space statement where the tree has a slab statement, on `ℤ` where the tree
has `Fin n`, and with a parity restriction this file does not impose.

**And `TransferData` is further off than two fields.** Beyond `T_symm` and `T_contract` it needs the
shift and the form on the SAME carrier: `InfiniteShift.ishiftObs` acts on plain functions and its
results are stated against `InfiniteLattice.quasiLocalAlg`, while `stateReflForm` needs a submodule
of `C(IConf G, ℝ)`. That common carrier, the bundling of `ishiftObs`, and the fact that `ireflObs`
preserves it are three further open items.
-/

namespace MassGap.LatticeReflection

open MassGap.InfiniteLattice MassGap.InfiniteReflection

/-! ## 1. Sites -/

/-- **REFLECTION OF ONE COORDINATE**, `x_τ ↦ c − x_τ`, every other coordinate fixed.

`c` is the reflection constant, not a position: the fixed set of `x ↦ c − x` is where `2x = c`, so
the plane sits at `c/2` and `c` sweeps the family of reflections in direction `τ`. This is
`Reflect.reflSite` with `Fin n` replaced by `ℤ`.

DERIVED: `4` is the spacetime dimension, the constant `InfiniteLattice.ISite` and `ILink` are built
on — the direction index's range, not an extent. `c` and `τ` are the caller's and the subtraction is
`ℤ`'s. -/
def ireflSite (τ : Fin 4) (c : ℤ) (x : ISite) : ISite := Function.update x τ (c - x τ)

@[simp] theorem ireflSite_axis (τ : Fin 4) (c : ℤ) (x : ISite) :
    ireflSite τ c x τ = c - x τ := by simp [ireflSite]

/-- **IT IS AN INVOLUTION**: `c − (c − a) = a`.

DERIVED: `4` is the dimension, as in `ireflSite`. -/
theorem ireflSite_involutive (τ : Fin 4) (c : ℤ) :
    Function.Involutive (ireflSite τ c) := by
  intro x
  funext j
  by_cases h : j = τ
  · subst h
    simp [ireflSite, sub_sub_cancel]
  · simp [ireflSite, Function.update_of_ne h]

#print axioms ireflSite_involutive

/-! ## 2. Links, where the base shifts by one -/

/-- **REFLECTION OF A LINK.** A link in direction `τ` spans `[x_τ, x_τ+1]`, so its mirror spans
`[c−1−x_τ, c−x_τ]` and is based at `c−1−x_τ`; a link in any other direction is based at the mirror of
its own base.

DERIVED: the `1` is the length of a link in lattice steps — the offset between its two ends, exactly
`Reflect.reflLink`'s and for the same reason. `4` is the dimension, as in `ireflSite`. -/
def ireflLink (τ : Fin 4) (c : ℤ) (l : ILink) : ILink :=
  (l.1, if l.1 = τ then ireflSite τ (c - 1) l.2 else ireflSite τ c l.2)

/-- The reflection does not change a link's DIRECTION, only its base. Used wherever the dagger's
case split has to be matched on both sides.

DERIVED: `4` is the dimension. -/
@[simp] theorem ireflLink_fst (τ : Fin 4) (c : ℤ) (l : ILink) :
    (ireflLink τ c l).1 = l.1 := rfl

/-- **IT IS AN INVOLUTION**, hence a bijection of the link set.

DERIVED: the `1` is `ireflLink`'s link length; `4` is the dimension. -/
theorem ireflLink_involutive (τ : Fin 4) (c : ℤ) :
    Function.Involutive (ireflLink τ c) := by
  intro l
  obtain ⟨μ, x⟩ := l
  by_cases h : μ = τ
  · simp [ireflLink, h, ireflSite_involutive τ (c - 1) x]
  · simp [ireflLink, h, ireflSite_involutive τ c x]

#print axioms ireflLink_involutive

/-! ## 3. Configurations, and the dagger -/

section Conf

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G]

/-- **REFLECTION OF A CONFIGURATION, WITH THE DAGGER.** A `τ`-link is traversed backwards by the
mirrored loop, so its group element is inverted; links in other directions are not.

This is `Reflect.reflConf`, and the inverse is the `†` of the Osterwalder–Seiler time reflection.
Dropping it would leave a map that is still an involution of the link set but under which the Wilson
action is not invariant, so nothing downstream would hold.

DERIVED: `4` is the dimension. -/
def ireflConf (τ : Fin 4) (c : ℤ) (U : IConf G) : IConf G :=
  fun l => if l.1 = τ then (U (ireflLink τ c l))⁻¹ else U (ireflLink τ c l)

omit [ContinuousInv G] in
/-- **STILL AN INVOLUTION** — the double inverse cancels on `τ`-links, and `ireflLink_fst` is what
lets the two case splits line up.

DERIVED: `4` is the dimension. -/
theorem ireflConf_involutive (τ : Fin 4) (c : ℤ) :
    Function.Involutive (ireflConf (G := G) τ c) := by
  intro U
  funext l
  by_cases h : l.1 = τ
  · simp only [ireflConf, ireflLink_fst, if_pos h, inv_inv, ireflLink_involutive τ c l]
  · simp only [ireflConf, ireflLink_fst, if_neg h, ireflLink_involutive τ c l]

#print axioms ireflConf_involutive

/-- Continuous: each output coordinate is an input coordinate, inverted or not, and inversion is
continuous.

DERIVED: `4` is the dimension. -/
theorem continuous_ireflConf (τ : Fin 4) (c : ℤ) :
    Continuous (ireflConf (G := G) τ c) := by
  refine continuous_pi fun l => ?_
  by_cases h : l.1 = τ
  · simp only [ireflConf, if_pos h]
    exact (continuous_apply (ireflLink τ c l)).inv
  · simp only [ireflConf, if_neg h]
    exact continuous_apply (ireflLink τ c l)

#print axioms continuous_ireflConf

/-- The configuration reflection, bundled.

DERIVED: `4` is the dimension. -/
def ireflConfCM (τ : Fin 4) (c : ℤ) : C(IConf G, IConf G) :=
  ⟨ireflConf τ c, continuous_ireflConf τ c⟩

end Conf

/-! ## 4. Observables, and the `Reflection` -/

section Obs

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]

/-- **REFLECTION OF AN OBSERVABLE**, by precomposition. Linear because precomposition is.

DERIVED: `4` is the dimension. -/
def ireflObs (τ : Fin 4) (c : ℤ) : C(IConf G, ℝ) →ₗ[ℝ] C(IConf G, ℝ) where
  toFun F := F.comp (ireflConfCM τ c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [CompactSpace G] in
@[simp] theorem ireflObs_apply (τ : Fin 4) (c : ℤ) (F : C(IConf G, ℝ)) (U : IConf G) :
    ireflObs τ c F U = F (ireflConf τ c U) := rfl

/-- **⭐ THE INFINITE LATTICE'S REFLECTION, AS A `Reflection`.** Precomposition is linear, respects
the product and fixes the constant whatever it precomposes with; involutivity is `ireflConf`'s, where
the dagger does its work.

DERIVED: `4` is the dimension. -/
def latticeReflection (τ : Fin 4) (c : ℤ) : Reflection (IConf G) where
  θ := ireflObs τ c
  θ_mul _ _ := rfl
  θ_one := rfl
  θ_involutive F := by
    ext U
    show F (ireflConf τ c (ireflConf τ c U)) = F U
    rw [ireflConf_involutive τ c U]

#print axioms latticeReflection

/-! ## 5. It is not the trivial reflection — when the group is not trivial -/

/-- **THE REFLECTION MOVES A LINK.** At `c = 1` the link based at the origin in a direction other
than `τ` reflects to the link based at the site with `x_τ = 1`.

A direction `μ ≠ τ` is used so the dagger does not enter: this is a statement about the link map
alone, and `ireflLink` is the same with or without the inverse.

CHOSEN: `c = 1` and the base site `0` are a witness, the simplest pair at which `c − x_τ ≠ x_τ`.
`ireflSite_axis` makes the same statement at every `c` with `2·x_τ ≠ c`. Neither carries another
role. DERIVED: `4` is the dimension. -/
theorem ireflLink_moves_a_link {τ μ : Fin 4} (hμ : μ ≠ τ) :
    ireflLink τ 1 (μ, fun _ => (0 : ℤ)) ≠ (μ, fun _ => (0 : ℤ)) := by
  intro h
  have hsnd : ireflSite τ 1 (fun _ => (0 : ℤ)) = (fun _ => (0 : ℤ)) := by
    have hcomp : (ireflLink τ 1 (μ, fun _ => (0 : ℤ))).2
        = ireflSite τ 1 (fun _ => (0 : ℤ)) := by
      show (if μ = τ then _ else _) = _
      rw [if_neg hμ]
    rw [← hcomp, h]
  have hcoord := congrFun hsnd τ
  rw [ireflSite_axis] at hcoord
  omega

#print axioms ireflLink_moves_a_link

omit [CompactSpace G] in
/-- **⛔ AND MOVING A LINK IS NOT ENOUGH** to make `latticeReflection` differ from
`InfiniteReflection.trivialReflection`: if the gauge group is a subsingleton then `IConf G` is too,
every observable is constant, and `ireflObs` IS the identity however many links move.

Stated because the obvious reading of `ireflLink_moves_a_link` is that the reflection is non-trivial,
and that reading is wrong without a hypothesis on the group. `GNSHilbert` makes the same point about
`N = 1`, where the gauge group is trivial and every observable is constant.

DERIVED: `4` is the dimension; no magnitude is chosen. -/
theorem ireflObs_eq_id_of_subsingleton [Subsingleton G] (τ : Fin 4) (c : ℤ)
    (F : C(IConf G, ℝ)) : ireflObs (G := G) τ c F = F := by
  ext U
  show F (ireflConf τ c U) = F U
  congr 1
  funext l
  exact Subsingleton.elim _ _

#print axioms ireflObs_eq_id_of_subsingleton

end Obs

end MassGap.LatticeReflection
