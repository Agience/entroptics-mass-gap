import Mathlib
import MassGap.TransferAssembly
import MassGap.GNSHilbert
import MassGap.TransferGap
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

**It supplies none of the three here.** `WilsonDLR` builds an infinite-volume Gibbs MEASURE, not a
`DLRLimit.State` carrying these properties.

**⛔ BUT TWO OF THE THREE ARE DISCHARGED DOWNSTREAM.**
`ReflectionHalfSpace.wilson_reflPositive_limit_exists` gives `ReflPositiveOn` at `2 * p` on
`halfSpaceAlg τ p` for a Wilson limit state, at every real `β` and with no structural hypothesis
left; `reflection_facts_on_halfSpaceAlg` adds `IsReflectionInvariant` alongside it. What remains is
`hnu`, and `ReflectionShift.reflection_invariant_succ_iff_nu_T` shows it is equivalent to reflection
invariance at the adjacent constant.

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

/-! ## 2′. ⭐⭐ The half-step: positivity of the transfer operator -/

/-- **⭐⭐⭐ THE TRANSFER OPERATOR'S POSITIVITY IS REFLECTION POSITIVITY AT THE PRECEDING CONSTANT.**

`GNSHilbert.PositiveTransfer` asks `0 ≤ ν (θ_c F · T F)`. That quantity IS the reflection pairing at
`c - 1`:

    θ_c F = T (θ_{c-1} F)                    `ReflectionShift.ireflObs_succ_eq_shiftObs_ireflObs`
    θ_c F · T F = T (θ_{c-1} F · F)          `ishiftObsL_mul`
    ν (T G) = ν G                           `hnu`

**⛔ SO THE "HALF-STEP" IS THE ODD REFLECTION, AND THAT IS WHY IT IS A SEPARATE PROBLEM.** With `c`
even, `c - 1` is odd: the LINK reflection, whose mirror sits at the half-integer `p - 1/2`. That
mirror carries `{x_τ ≥ p}` INTO `{x_τ ≤ p - 1}`, which is exactly the set-complement of
`posHalf τ p`, so the pairing is the geometrically correct one and nothing has to be re-indexed. Into
rather than onto: a `τ`-link based at `p - 1` straddles the mirror and is in the complement without
being in the image.

**⛔ `2p + 1` WOULD BE THE WRONG CONSTANT**, and not by a little: it sends a link based at `p` to
`p + 1` or fixes it, both still inside `posHalf τ p`, so it does not exchange the halves at all. It
pairs with `halfSpaceAlg τ (p + 1)`. `HalfSpaceAlgebra`'s remark that `posHalf` cannot express a
half-integer plane is about the MIRROR, not the algebra — `halfSpaceAlg τ p` serves both the mirror
at `p` and the mirror at `p - 1/2`.

**⛔ THE THEOREM ITSELF IS COUPLING-FREE; DISCHARGING `hposOdd` IS NOT.** This identity holds for
every state and mentions no `β`, and `hposOdd` is satisfiable coupling-free — evaluation at the
all-identity configuration satisfies it at every constant. What needs `0 ≤ β` is discharging
`hposOdd` for the `SU(3)` WILSON measure through the cross kernel:
`CharacterExpansion.NegControl.su3_kernel_nonneg_iff` is an IFF on the kernel that argument
integrates, so it refutes that route below zero. It refutes the kernel's nonnegativity, not
reflection positivity itself.

**What this buys:** `GNSCompare.gapAt_of_positiveTransfer_of_rayleigh` takes `PositiveTransfer` plus a
Rayleigh bound and returns `TransferGap.GapAt`. This supplies the first of the two. The Rayleigh
bound is the gap itself and is untouched.

DERIVED: the `1` is the mirror separation, which is the half-step; the `0` is the sign asserted; `4`
is the dimension. -/
theorem positiveTransfer_pairing_eq (τ : Fin 4) (c : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G))
    (hnu : ∀ f : C(IConf G, ℝ), ν (ishiftObsL τ f) = ν f)
    (F : C(IConf G, ℝ)) :
    ν (ireflObs τ c F * ishiftObsL τ F) = ν (ireflObs τ (c - 1) F * F) := by
  have hrefl : ireflObs τ c F = ishiftObsL τ (ireflObs τ (c - 1) F) := by
    have h := MassGap.ReflectionShift.ireflObs_succ_eq_shiftObs_ireflObs τ (c - 1) F
    rwa [sub_add_cancel] at h
  rw [hrefl, ← ishiftObsL_mul, hnu]

#print axioms positiveTransfer_pairing_eq

/-- **⭐⭐ AND SO `PositiveTransfer` FOLLOWS FROM THE ODD REFLECTION POSITIVITY.**

Stated on the pairing rather than on a `TransferData`, so it can be used before the data is
assembled. `A` is the same algebra on both sides — no re-indexing — because the mirror at `c - 1`
exchanges exactly the halves the mirror at `c` does not.

DERIVED: the `1` is the mirror separation; the `0` is the sign asserted; `4` is the dimension. -/
theorem positiveTransfer_pairing_nonneg (τ : Fin 4) (c : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G)) (A : Submodule ℝ C(IConf G, ℝ))
    (hnu : ∀ f : C(IConf G, ℝ), ν (ishiftObsL τ f) = ν f)
    (hposPred : ReflPositiveOn (latticeReflection τ (c - 1)) A ν)
    {F : C(IConf G, ℝ)} (hF : F ∈ A) :
    0 ≤ ν (ireflObs τ c F * ishiftObsL τ F) := by
  rw [positiveTransfer_pairing_eq τ c ν hnu F]
  exact hposPred F hF

#print axioms positiveTransfer_pairing_nonneg

/-- **⭐⭐⭐ AND THE GAP CONDITION IS THE PAIRING TWO CONSTANTS BACK.**

The same computation one step further. `theta_T` turns `θ_c (T F)` into `S (θ_c F)`, which is
`θ_{c-1} F`, and the half-step identity then drops it to `c - 2`:

    ν (θ_c (T F) · T F) = ν (θ_{c-2} F · F).

**⛔ SO `TransferGap.GapAt` ON THE ASSEMBLED DATA READS**

    ν (θ_{2p-2} F · F)  ≤  r² · ν (θ_{2p} F · F)

for every `F` in the algebra with `ν (θ_{2p} F · 1) = 0`. **Both constants are EVEN and they are TWO
apart** — the lag-two ratio the gap side measures, written in the operator side's own objects. It is
a ratio of two reflection pairings and nothing else: no spectrum, no operator norm, no Hilbert space.

This is a restatement, not a proof. What it buys is that the remaining spectral obligation is now a
statement about the SAME kind of quantity the rest of this development already produces, rather than
about `Tq` on a completion.

DERIVED: the `1` is the mirror separation and the `2` twice it; `4` is the dimension. -/
theorem gapAt_pairing_eq (τ : Fin 4) (c : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G))
    (hnu : ∀ f : C(IConf G, ℝ), ν (ishiftObsL τ f) = ν f)
    (F : C(IConf G, ℝ)) :
    ν (ireflObs τ c (ishiftObsL τ F) * ishiftObsL τ F)
      = ν (ireflObs τ (c - 2) F * F) := by
  rw [MassGap.ReflectionShift.ireflObs_ishiftObs,
    ← MassGap.ReflectionShift.ireflObs_pred_eq_unshift,
    positiveTransfer_pairing_eq τ (c - 1) ν hnu F,
    show c - 1 - 1 = c - 2 from by ring]

#print axioms gapAt_pairing_eq


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

/-- **⭐⭐⭐ THE ASSEMBLED DATA IS A POSITIVE TRANSFER, GIVEN THE ODD REFLECTION POSITIVITY.**

`assembleTransferData` sets `form := stateFormFun` and `T := restrictT`, so `D.form x (D.T x)` is
literally `ν (θ_{2p} x · T x)` — the pairing `positiveTransfer_pairing_nonneg` bounds. This lands the
odd-constant reflection positivity on the predicate
`GNSCompare.gapAt_of_positiveTransfer_of_rayleigh` consumes.

**⛔ WHAT IS NOW BETWEEN HERE AND A GAP.** That lemma takes `PositiveTransfer` AND a Rayleigh bound
`⟨Tᵨ y, y⟩ ≤ Λ ‖y‖²` on the vacuum complement, and returns `TransferGap.GapAt D Λ`. This supplies the
first. **The Rayleigh bound is the mass gap itself and nothing here touches it.**

**⛔ AND `hposOdd` IS NOT FREE.** It is reflection positivity at an ODD constant — the link
reflection — which is an INEQUALITY and therefore does need `0 ≤ β`:
`CharacterExpansion.NegControl.su3_kernel_nonneg_iff` refutes the kernel's nonnegativity below zero.
`ReflectionHalfSpace`'s positivity chain is built at `2 * p` throughout and does not produce it. Its
ANALOGUE of `boxR_ne_tau` fails at an odd constant — the theorem itself hardwires `2 * p`, so it has
no odd instantiation — and that is why the chain cannot simply be re-indexed the way the invariance
chain was. The deeper reason is that the shared block flips: at an even constant it is the TRANSVERSE
links on the plane with the dagger trivial, at an odd one the AXIS links with the dagger inverting,
which `OddLagSplit` calls the whole difference from the even-lag case.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`, the `1` is the half-step; `4` is the
dimension. -/
theorem positiveTransfer_of_state_facts (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G))
    (hinv : IsReflectionInvariant (latticeReflection τ (2 * p)) ν)
    (hpos : ReflPositiveOn (latticeReflection τ (2 * p)) (halfSpaceAlg (G := G) τ p) ν)
    (hnu : ∀ f : C(IConf G, ℝ), ν (ishiftObsL τ f) = ν f)
    (hposOdd : ReflPositiveOn (latticeReflection τ (2 * p - 1))
      (halfSpaceAlg (G := G) τ p) ν) :
    MassGap.GNSHilbert.PositiveTransfer
      (transferData_of_state_facts τ p ν hinv hpos hnu) := by
  intro x
  exact positiveTransfer_pairing_nonneg τ (2 * p) ν _ hnu hposOdd x.2

#print axioms positiveTransfer_of_state_facts

/-- **⭐⭐⭐ AND THE TWO ARE THE SAME FACT.**

`positiveTransfer_pairing_eq` is an EQUALITY of reals, so the implication runs both ways: the
assembled data is a positive transfer **exactly when** the state is reflection positive at the odd
constant, on the same algebra.

That is the strongest available certificate that `hposOdd` is not an overshoot and not a
re-indexing — an overshoot would give only one direction. Whatever discharges either side discharges
the other, and anything that refutes one refutes the other.

DERIVED: the `2` is the plane-to-constant conversion `c = 2p`, the `1` is the half-step; `4` is the
dimension. -/
theorem positiveTransfer_iff_odd_reflPositive (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G))
    (hinv : IsReflectionInvariant (latticeReflection τ (2 * p)) ν)
    (hpos : ReflPositiveOn (latticeReflection τ (2 * p)) (halfSpaceAlg (G := G) τ p) ν)
    (hnu : ∀ f : C(IConf G, ℝ), ν (ishiftObsL τ f) = ν f) :
    MassGap.GNSHilbert.PositiveTransfer
        (transferData_of_state_facts τ p ν hinv hpos hnu)
      ↔ ReflPositiveOn (latticeReflection τ (2 * p - 1)) (halfSpaceAlg (G := G) τ p) ν := by
  constructor
  · intro hP F hF
    have h : (0 : ℝ) ≤ ν (ireflObs τ (2 * p) F * ishiftObsL τ F) := hP ⟨F, hF⟩
    rwa [positiveTransfer_pairing_eq τ (2 * p) ν hnu F] at h
  · intro hposOdd
    exact positiveTransfer_of_state_facts τ p ν hinv hpos hnu hposOdd

#print axioms positiveTransfer_iff_odd_reflPositive

/-- **⭐⭐⭐ THE GAP CONDITION, AS AN INEQUALITY BETWEEN TWO REFLECTION PAIRINGS.**

`TransferGap.GapAt` on the assembled data, unfolded. For every `F` in the half-space algebra whose
reflection pairing with the vacuum vanishes:

    ν (θ_{2p-2} F · F)  ≤  r² · ν (θ_{2p} F · F)

**⛔ WHY THIS IS THE STATEMENT TO ATTACK.** `GNSCompare.gapAt_of_positiveTransfer_of_rayleigh` is a
SUFFICIENT route to `GapAt`, not the obligation: its Rayleigh hypothesis lives on
`GNS D.toReflForm`, a COMPLETION, and every consumer of the gap takes `GapAt` itself. This form lives
on the ALGEBRA, before any completion, and mentions no spectrum, no operator norm and no Hilbert
space — only the state and two reflections.

It is an `↔`, so nothing is given up by working with it.

**⛔ WHAT IT IS NOT.** It is not a shape fact: the flat profile arguments
(`FlatProfileAllApertures`) cap shape and representability arguments at `1`, and this is a statement
about the actual limit state rather than about a profile. It is not a compression, so the argument
that a measured spectrum can only LOWER-bound the top eigenvalue does not apply. And it is not the
periodic-shift statement `HalfLineTransfer.no_rate_of_shift_transfer` refutes, because the carrier is
`ℤ⁴`, where `HalfSpaceAlgebra.shift_no_finite_order_on_halfSpaceAlg` shows the shift has infinite
order.

**⛔ IT IS STILL UNPROVED, AND IT IS STILL THE MASS GAP.** Nothing here makes it true.

DERIVED: the `2`s are the plane-to-constant conversion and the two-step separation; `4` is the
dimension. -/
theorem gapAt_iff_pairing (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G))
    (hinv : IsReflectionInvariant (latticeReflection τ (2 * p)) ν)
    (hpos : ReflPositiveOn (latticeReflection τ (2 * p)) (halfSpaceAlg (G := G) τ p) ν)
    (hnu : ∀ f : C(IConf G, ℝ), ν (ishiftObsL τ f) = ν f) (r : ℝ) :
    MassGap.TransferGap.GapAt (transferData_of_state_facts τ p ν hinv hpos hnu) r
      ↔ ∀ F ∈ halfSpaceAlg (G := G) τ p,
          ν (ireflObs τ (2 * p) F * 1) = 0 →
          ν (ireflObs τ (2 * p - 2) F * F) ≤ r ^ 2 * ν (ireflObs τ (2 * p) F * F) := by
  constructor
  · intro h F hF hvac
    have hx : ν (ireflObs τ (2 * p) (ishiftObsL τ F) * ishiftObsL τ F)
        ≤ r ^ 2 * ν (ireflObs τ (2 * p) F * F) := h ⟨F, hF⟩ hvac
    rwa [gapAt_pairing_eq τ (2 * p) ν hnu F] at hx
  · intro h x hvac
    have hx := h (x : C(IConf G, ℝ)) x.2 hvac
    rw [← gapAt_pairing_eq τ (2 * p) ν hnu (x : C(IConf G, ℝ))] at hx
    exact hx

#print axioms gapAt_iff_pairing

/-- **THE SIDE CONDITION IS ORDINARY VACUUM SUBTRACTION.** `θ F · 1` is `θ F`, and `hinv` says the
state does not see the reflection, so `ν (θ_{2p} F · 1) = ν F`. The premise was never about the
reflection.

DERIVED: the `2` is the plane-to-constant conversion; `4` is the dimension. -/
theorem gapAt_iff_pairing_of_mean_zero (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G))
    (hinv : IsReflectionInvariant (latticeReflection τ (2 * p)) ν)
    (hpos : ReflPositiveOn (latticeReflection τ (2 * p)) (halfSpaceAlg (G := G) τ p) ν)
    (hnu : ∀ f : C(IConf G, ℝ), ν (ishiftObsL τ f) = ν f) (r : ℝ) :
    MassGap.TransferGap.GapAt (transferData_of_state_facts τ p ν hinv hpos hnu) r
      ↔ ∀ F ∈ halfSpaceAlg (G := G) τ p, ν F = 0 →
          ν (ireflObs τ (2 * p - 2) F * F) ≤ r ^ 2 * ν (ireflObs τ (2 * p) F * F) := by
  have hmean : ∀ F : C(IConf G, ℝ), ν (ireflObs τ (2 * p) F * 1) = ν F := by
    intro F
    rw [mul_one]
    exact hinv F
  rw [gapAt_iff_pairing τ p ν hinv hpos hnu r]
  constructor
  · intro h F hF hz
    exact h F hF (by rw [hmean]; exact hz)
  · intro h F hF hz
    exact h F hF (by rw [← hmean]; exact hz)

#print axioms gapAt_iff_pairing_of_mean_zero

/-- **⭐⭐⭐ AND WITH THE SUBTRACTION BUILT IN, THERE IS NO SIDE CONDITION AT ALL.**

`F - ν F • 1` lies in the algebra — a submodule containing `1` — and has zero expectation; at
`ν F = 0` it IS `F`. So the gap condition is equivalent to the inequality holding at the SUBTRACTED
observable, for every `F` in the algebra, with no premise to lose track of.

**⛔ THIS IS THE FORM TO ATTACK.** The object is the CONNECTED two-point function by construction
rather than by hypothesis, so the `F = 1` collapse that makes the unsubtracted statement
contradictory cannot occur: at `F = 1` the subtracted observable is `0` and both sides are `0`.

DERIVED: the `2`s are the plane-to-constant conversion and the two-step separation; `4` is the
dimension. -/
theorem gapAt_iff_subtracted_pairing (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G))
    (hinv : IsReflectionInvariant (latticeReflection τ (2 * p)) ν)
    (hpos : ReflPositiveOn (latticeReflection τ (2 * p)) (halfSpaceAlg (G := G) τ p) ν)
    (hnu : ∀ f : C(IConf G, ℝ), ν (ishiftObsL τ f) = ν f) (r : ℝ) :
    MassGap.TransferGap.GapAt (transferData_of_state_facts τ p ν hinv hpos hnu) r
      ↔ ∀ F ∈ halfSpaceAlg (G := G) τ p,
          ν (ireflObs τ (2 * p - 2) (F - ν F • 1) * (F - ν F • 1))
            ≤ r ^ 2 * ν (ireflObs τ (2 * p) (F - ν F • 1) * (F - ν F • 1)) := by
  have hsubmem : ∀ F ∈ halfSpaceAlg (G := G) τ p,
      (F - ν F • (1 : C(IConf G, ℝ))) ∈ halfSpaceAlg (G := G) τ p := by
    intro F hF
    exact Submodule.sub_mem _ hF (Submodule.smul_mem _ _ (one_mem_halfSpaceAlg τ p))
  have hsubzero : ∀ F : C(IConf G, ℝ), ν (F - ν F • (1 : C(IConf G, ℝ))) = 0 := by
    intro F
    rw [ν.map_sub, ν.map_smul, ν.one']
    ring
  rw [gapAt_iff_pairing_of_mean_zero τ p ν hinv hpos hnu r]
  constructor
  · intro h F hF
    exact h _ (hsubmem F hF) (hsubzero F)
  · intro h F hF hz
    have hsub : F - ν F • (1 : C(IConf G, ℝ)) = F := by
      rw [hz]
      simp
    have := h F hF
    rwa [hsub] at this

#print axioms gapAt_iff_subtracted_pairing

end Lattice

end MassGap.WilsonTransferReduction
