import Mathlib
import MassGap.TransferAssembly
import MassGap.ReflectionShift
import MassGap.HalfSpaceAlgebra

/-!
# MassGap.WilsonTransferReduction — the transfer operator, reduced to three facts about the state

## What this does

`TransferAssembly.assembleTransferData` takes nine inputs. **Six of them are about the lattice and
the maps, and all six are discharged here**; the three that survive are about the MEASURE.

| input | discharged by |
|---|---|
| `C : ShiftCompat R ν` | `shiftCompat_of_nu_T` — from `nu_T` alone; the other three fields are `ReflectionShift`'s |
| `hstable` | `HalfSpaceAlgebra.halfSpaceAlg_shift_stable` |
| `hone` | `HalfSpaceAlgebra.one_mem_halfSpaceAlg` |
| `hTone` | `ishiftObsL_one` — precomposition fixes the constant |
| `hTnorm` | `norm_comp_le` — precomposition cannot enlarge a supremum |
| `hθnorm` | `norm_comp_le` |

**What remains is exactly three**, and each is a property of the infinite-volume state:

    hinv : IsReflectionInvariant (latticeReflection τ (2*p)) ν
    hpos : ReflPositiveOn (latticeReflection τ (2*p)) (halfSpaceAlg τ p) ν
    hnu  : ∀ f, ν (ishiftObsL τ f) = ν f

**The `2*p` is forced.** `halfSpaceAlg` is indexed by the PLANE and `latticeReflection` by the
reflection CONSTANT, whose plane sits at half of it, so the reflection exchanging the halves at plane
`p` is the one at constant `2p` — `ReflectionHalfSpace.reflection_exchanges_halves`. Pairing `c` with
`c` is the reflection pairing only at `c = 0`.

`transferData_of_state_facts` is the statement: given those three, a full `Transfer.TransferData` on
the half-space algebra, and hence — through `GNSHilbert` and `OpTBridge.reconstruct_from_opT` — a
Hilbert space, a vacuum, a bounded self-adjoint operator and `H = −log T`.

## ⚠ What it does not do

**It supplies none of the three.** No Wilson state on `IConf G` is exhibited with any of them:
`WilsonDLR` builds an infinite-volume Gibbs MEASURE, not a `DLRLimit.State` carrying these
properties, and `ReflPositiveOn` is discharged nowhere in the tree.

**And it does not give a gap.** Even with all three, `OpTBridge.reconstruct_from_opT` still needs the
two spectral hypotheses, which are the mass gap in operator form. This reduction is about the
CONSTRUCTION of the operator, not about its spectrum.

So the honest reading: C1's operator half was a list of nine obligations of two different kinds, and
it is now a list of three, all of one kind.
-/

namespace MassGap.WilsonTransferReduction

open MassGap.InfiniteLattice MassGap.InfiniteReflection
open MassGap.SchwarzIteration MassGap.TransferAssembly
open MassGap.LatticeReflection MassGap.InfiniteShift MassGap.ReflectionShift
open MassGap.HalfSpaceAlgebra

/-! ## 1. Precomposition cannot enlarge a supremum -/

/-- **A CONTINUOUS OBSERVABLE PULLED BACK IS NO LARGER.** `‖F ∘ g‖ ≤ ‖F‖`, because the supremum over
the image is a supremum over a subset.

Surjectivity of `g` is not needed and is not assumed — the inequality runs in the one direction the
assembly consumes.

DERIVED: no numeral. -/
theorem norm_comp_le {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (F : C(X, ℝ)) (g : C(X, X)) : ‖F.comp g‖ ≤ ‖F‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg F)).mpr
    (fun x => F.norm_coe_le_norm (g x))

#print axioms norm_comp_le

/-! ## 2. The lattice-side inputs -/

section Lattice

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]
  [Nonempty G]

/-- **`hTone`** — the shift fixes the constant observable, because precomposition does.

DERIVED: the `1` is the constant observable. -/
theorem ishiftObsL_one (τ : Fin 4) : ishiftObsL (G := G) τ 1 = 1 := rfl

/-- **`hTnorm`** — the shift does not enlarge the supremum norm. -/
theorem norm_ishiftObsL_le (τ : Fin 4) (f : C(IConf G, ℝ)) :
    ‖ishiftObsL (G := G) τ f‖ ≤ ‖f‖ :=
  norm_comp_le f ⟨ishiftConf τ, continuous_ishiftConf τ⟩

#print axioms norm_ishiftObsL_le

/-- **`hθnorm`** — nor does the reflection. -/
theorem norm_ireflObs_le (τ : Fin 4) (c : ℤ) (f : C(IConf G, ℝ)) :
    ‖ireflObs (G := G) τ c f‖ ≤ ‖f‖ :=
  norm_comp_le f (ireflConfCM τ c)

#print axioms norm_ireflObs_le

/-- **⭐ `ShiftCompat` FROM `nu_T` ALONE.** The other three fields are `ReflectionShift`'s:
`ishiftObsL_mul` is `T_mul`, `ishiftObsL_iunshiftObs` is `T_S`, and `ireflObs_ishiftObs` is
`theta_T` — the reflection carrying the forward shift to the backward one.

DERIVED: `4` is the spacetime dimension; no other numeral. -/
def shiftCompat_of_nu_T (τ : Fin 4) (c : ℤ) (ν : MassGap.DLRLimit.State (IConf G))
    (hnu : ∀ f : C(IConf G, ℝ), ν (ishiftObsL τ f) = ν f) :
    ShiftCompat (latticeReflection τ c) ν where
  T := ishiftObsL τ
  S := iunshiftObs τ
  T_mul := ishiftObsL_mul τ
  T_S := ishiftObsL_iunshiftObs τ
  theta_T := ireflObs_ishiftObs τ c
  nu_T := hnu

/-! ## 3. ⭐ The reduction -/

/-- **⭐ A FULL `TransferData` FROM THREE FACTS ABOUT THE STATE.**

Every lattice-side input of `TransferAssembly.assembleTransferData` is discharged: the shift is an
endomorphism of the half-space algebra (`halfSpaceAlg_shift_stable`), the constant is in it
(`one_mem_halfSpaceAlg`) and is fixed by the shift, and neither the shift nor the reflection enlarges
the supremum norm.

**The three that remain are all about the measure**, and none is supplied anywhere in the tree.

DERIVED: `4` is the spacetime dimension; no other numeral. -/
noncomputable def transferData_of_state_facts (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G))
    (hinv : IsReflectionInvariant (latticeReflection τ (2 * p)) ν)
    (hpos : ReflPositiveOn (latticeReflection τ (2 * p)) (halfSpaceAlg (G := G) τ p) ν)
    (hnu : ∀ f : C(IConf G, ℝ), ν (ishiftObsL τ f) = ν f) :
    MassGap.Transfer.TransferData ↥(halfSpaceAlg (G := G) τ p) :=
  assembleTransferData (latticeReflection τ (2 * p)) ν (halfSpaceAlg τ p) hinv hpos
    (shiftCompat_of_nu_T τ (2 * p) ν hnu)
    (fun f hf => halfSpaceAlg_shift_stable τ p hf)
    (one_mem_halfSpaceAlg τ p)
    (ishiftObsL_one τ)
    (norm_ishiftObsL_le τ)
    (norm_ireflObs_le τ (2 * p))

#print axioms transferData_of_state_facts

end Lattice

end MassGap.WilsonTransferReduction
