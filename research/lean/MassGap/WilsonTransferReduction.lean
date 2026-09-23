import Mathlib
import MassGap.TransferAssembly
import MassGap.GNSHilbert
import MassGap.TransferGap
import MassGap.ReflectionShift
import MassGap.HalfSpaceAlgebra

/-!
# MassGap.WilsonTransferReduction — the transfer operator, reduced to three facts about the state

## What this module builds

`TransferAssembly.assembleTransferData` takes nine inputs. Six are discharged here from facts about
the lattice and the maps:

| input | discharged by |
|---|---|
| `C : ShiftCompat R ν` | `shiftCompat_of_nu_T`, from `nu_T` alone; the other three fields come from `ReflectionShift` |
| `hstable` | `HalfSpaceAlgebra.halfSpaceAlg_shift_stable` |
| `hone` | `HalfSpaceAlgebra.one_mem_halfSpaceAlg` |
| `hTone` | `ishiftObsL_one` |
| `hTnorm` | `norm_comp_le` |
| `hθnorm` | `norm_comp_le` |

The three that remain are properties of the state:

    hinv : IsReflectionInvariant (latticeReflection τ (2 * p)) ν
    hpos : ReflPositiveOn (latticeReflection τ (2 * p)) (halfSpaceAlg τ p) ν
    hnu  : ∀ f, ν (ishiftObsL τ f) = ν f

`halfSpaceAlg` is indexed by the plane and `latticeReflection` by the reflection constant, whose
plane sits at half of it, so the reflection exchanging the halves at plane `p` is the one at
constant `2 * p` (`ReflectionHalfSpace.reflection_exchanges_halves`). Pairing `c` with `c` is the
reflection pairing only at `c = 0`.

`transferData_of_state_facts` assembles a `Transfer.TransferData` on the half-space algebra from
those three.

The remaining declarations rewrite the operator-side predicates as statements about reflection
pairings of the state:
* `positiveTransfer_pairing_eq` — `ν (θ_c F · T F) = ν (θ_{c-1} F · F)`, at every state satisfying
  `hnu`.
* `positiveTransfer_pairing_nonneg`, `positiveTransfer_of_state_facts`,
  `positiveTransfer_iff_odd_reflPositive` — `GNSHilbert.PositiveTransfer` of the assembled data
  holds exactly when the state is reflection positive at the odd constant `2 * p - 1` on the same
  algebra.
* `gapAt_pairing_eq`, `gapAt_iff_pairing`, `gapAt_iff_pairing_of_mean_zero`,
  `gapAt_iff_subtracted_pairing` — `TransferGap.GapAt` of the assembled data holds exactly when
  `ν (θ_{2p-2} F' · F') ≤ r ^ 2 * ν (θ_{2p} F' · F')` at the mean-subtracted `F' = F - ν F • 1`, for
  every `F` in the algebra.
* `gapAt_of_subtracted_pairing_nondegenerate` — it suffices to check that inequality where the
  lag-zero subtracted pairing is strictly positive.

Scope.
* None of `hinv`, `hpos`, `hnu` is supplied here. `WilsonDLR` builds an infinite-volume Gibbs
  measure, not a `DLRLimit.State` carrying them.
  `ReflectionHalfSpace.wilson_reflPositive_limit_exists` gives `ReflPositiveOn` at `2 * p` on
  `halfSpaceAlg τ p` for a Wilson limit state at every real `β`, and
  `reflection_facts_on_halfSpaceAlg` adds `IsReflectionInvariant`;
  `ReflectionShift.reflection_invariant_succ_iff_nu_T` relates `hnu` to reflection invariance at the
  adjacent constant.
* `hposOdd` in `positiveTransfer_of_state_facts` is reflection positivity at an odd constant, the
  link reflection. `ReflectionHalfSpace`'s positivity chain is stated at `2 * p` throughout and its
  analogue of `boxR_ne_tau` hardwires that constant, so it has no odd instantiation. At an even
  constant the shared block is the transverse links on the plane with the dagger trivial; at an odd
  one it is the axis links with the dagger inverting.
  `CharacterExpansion.NegControl.su3_kernel_nonneg_iff` is an iff on the cross kernel, so the route
  through that kernel is refuted below `β = 0`.
* Nothing here proves a gap. `OpTBridge.reconstruct_from_opT` takes two spectral hypotheses beyond
  the assembled data, and `GNSCompare.gapAt_of_positiveTransfer_of_rayleigh` takes a Rayleigh bound
  on a completion; neither is supplied.
-/

namespace MassGap.WilsonTransferReduction

open MassGap.InfiniteLattice MassGap.InfiniteReflection
open MassGap.SchwarzIteration MassGap.TransferAssembly
open MassGap.LatticeReflection MassGap.InfiniteShift MassGap.ReflectionShift
open MassGap.HalfSpaceAlgebra

/-! ## 1. Precomposition cannot enlarge a supremum -/

/-- `‖F.comp g‖ ≤ ‖F‖` for `F : C(X, ℝ)` and `g : C(X, X)` on a nonempty compact space: the supremum
over the image is a supremum over a subset. Via `ContinuousMap.norm_le` and
`ContinuousMap.norm_coe_le_norm`.

Scope: `g` is not assumed surjective, so the inequality holds in one direction only.

DERIVED: no numeral occurs in the statement. -/
theorem norm_comp_le {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (F : C(X, ℝ)) (g : C(X, X)) : ‖F.comp g‖ ≤ ‖F‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg F)).mpr
    (fun x => F.norm_coe_le_norm (g x))

#print axioms norm_comp_le

/-! ## 2. The lattice-side inputs -/

section Lattice

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]
  [Nonempty G]

/-- `ishiftObsL τ 1 = 1`, by `rfl`: precomposition fixes the constant observable. This is
`assembleTransferData`'s `hTone`.

DERIVED: `4` is the spacetime dimension `τ` indexes; `1` is the constant observable, on both sides
of the equation. -/
theorem ishiftObsL_one (τ : Fin 4) : ishiftObsL (G := G) τ 1 = 1 := rfl

/-- `‖ishiftObsL τ f‖ ≤ ‖f‖`: the shift does not enlarge the supremum norm, since it is
precomposition with the continuous `ishiftConf τ`. This is `assembleTransferData`'s `hTnorm`.

DERIVED: the one numeral is the `4` of `Fin 4`, the spacetime dimension `τ` indexes. -/
theorem norm_ishiftObsL_le (τ : Fin 4) (f : C(IConf G, ℝ)) :
    ‖ishiftObsL (G := G) τ f‖ ≤ ‖f‖ :=
  norm_comp_le f ⟨ishiftConf τ, continuous_ishiftConf τ⟩

#print axioms norm_ishiftObsL_le

/-- `‖ireflObs τ c f‖ ≤ ‖f‖`: the reflection does not enlarge the supremum norm either, being
precomposition with `ireflConfCM τ c`. This is `assembleTransferData`'s `hθnorm`.

DERIVED: the one numeral is the `4` of `Fin 4`, the spacetime dimension `τ` indexes; `c` is the
caller's reflection constant. -/
theorem norm_ireflObs_le (τ : Fin 4) (c : ℤ) (f : C(IConf G, ℝ)) :
    ‖ireflObs (G := G) τ c f‖ ≤ ‖f‖ :=
  norm_comp_le f (ireflConfCM τ c)

#print axioms norm_ireflObs_le

/-- A `ShiftCompat (latticeReflection τ c) ν` built from the single hypothesis
`hnu : ∀ f, ν (ishiftObsL τ f) = ν f`. The other three fields come from `ReflectionShift`:
`ishiftObsL_mul` supplies `T_mul`, `ishiftObsL_iunshiftObs` supplies `T_S`, and
`ireflObs_ishiftObs` supplies `theta_T`, the reflection carrying the forward shift to the backward
one.

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

/-! ## 2′. The transfer operator's positivity, as a reflection pairing -/

/-- `ν (ireflObs τ c F * ishiftObsL τ F) = ν (ireflObs τ (c - 1) F * F)`, for any state `ν`
satisfying `hnu` and any `F`. The chain is

    θ_c F = T (θ_{c-1} F)          `ReflectionShift.ireflObs_succ_eq_shiftObs_ireflObs`
    θ_c F · T F = T (θ_{c-1} F · F)   `ishiftObsL_mul`
    ν (T G) = ν G                  `hnu`.

The left-hand side is the quantity `GNSHilbert.PositiveTransfer` asserts nonnegative.

Scope. The identity is an equality of reals holding at every state with `hnu` and mentions no
coupling. With `c` even, `c - 1` is odd — the link reflection, whose mirror sits at the half-integer
`p - 1/2` and carries `{x_τ ≥ p}` into `{x_τ ≤ p - 1}`, the set-complement of `posHalf τ p`. Into
rather than onto: a `τ`-link based at `p - 1` straddles the mirror and lies in the complement
without being in the image. The constant `2 * p + 1` does not exchange the halves at all — it sends
a link based at `p` to `p + 1` or fixes it, both inside `posHalf τ p` — and pairs with
`halfSpaceAlg τ (p + 1)` instead. `halfSpaceAlg τ p` serves both the mirror at `p` and the mirror at
`p - 1/2`; the half-integer appears in the mirror, not in the algebra's index.

DERIVED: `4` is the spacetime dimension `τ` indexes; `1` is the mirror separation, one step back
from `c`, which is what the shift contributes. `c` is the caller's constant. -/
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

/-- `0 ≤ ν (ireflObs τ c F * ishiftObsL τ F)` for `F` in a submodule `A`, given `hnu` and
`ReflPositiveOn (latticeReflection τ (c - 1)) A ν`. The previous identity followed by the positivity
hypothesis at `c - 1`.

Scope: stated on the pairing rather than on a `TransferData`, so it applies before the data is
assembled. `A` is the same submodule on both sides; no re-indexing occurs.

DERIVED: `4` is the spacetime dimension `τ` indexes; `1` is the mirror separation between `c` and
the constant the positivity hypothesis is stated at; `0` is the lower bound asserted. -/
theorem positiveTransfer_pairing_nonneg (τ : Fin 4) (c : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G)) (A : Submodule ℝ C(IConf G, ℝ))
    (hnu : ∀ f : C(IConf G, ℝ), ν (ishiftObsL τ f) = ν f)
    (hposPred : ReflPositiveOn (latticeReflection τ (c - 1)) A ν)
    {F : C(IConf G, ℝ)} (hF : F ∈ A) :
    0 ≤ ν (ireflObs τ c F * ishiftObsL τ F) := by
  rw [positiveTransfer_pairing_eq τ c ν hnu F]
  exact hposPred F hF

#print axioms positiveTransfer_pairing_nonneg

/-- `ν (ireflObs τ c (ishiftObsL τ F) * ishiftObsL τ F) = ν (ireflObs τ (c - 2) F * F)`, given
`hnu`. One step further than `positiveTransfer_pairing_eq`: `theta_T` turns `θ_c (T F)` into
`S (θ_c F) = θ_{c-1} F`, and the half-step identity drops the constant again to `c - 2`.

Applied at `c = 2 * p`, both constants are even and two apart, so the left-hand side of the gap
inequality is a reflection pairing at `2 * p - 2`.

DERIVED: `4` is the spacetime dimension `τ` indexes; `2` is the separation between the two
constants, two applications of the one-step drop that `positiveTransfer_pairing_eq` performs. -/
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


/-! ## 3. The assembled data -/

/-- A `Transfer.TransferData ↥(halfSpaceAlg τ p)` from three facts about the state: reflection
invariance at `2 * p`, reflection positivity at `2 * p` on the half-space algebra, and shift
invariance `hnu`. Every other input of `TransferAssembly.assembleTransferData` is supplied here —
`shiftCompat_of_nu_T` for the compatibility data, `halfSpaceAlg_shift_stable` for stability,
`one_mem_halfSpaceAlg` and `ishiftObsL_one` for the constant, and `norm_ishiftObsL_le` and
`norm_ireflObs_le` for the norm bounds.

Scope: the three state hypotheses are taken, not proved.

DERIVED: `4` is the spacetime dimension `τ` indexes; `2` converts the plane `p` to the reflection
constant `2 * p`, since `latticeReflection` is indexed by the constant whose mirror plane sits at
half of it. -/
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

/-- `GNSHilbert.PositiveTransfer (transferData_of_state_facts τ p ν hinv hpos hnu)`, given in
addition `hposOdd : ReflPositiveOn (latticeReflection τ (2 * p - 1)) (halfSpaceAlg τ p) ν`.
`assembleTransferData` sets `form := stateFormFun` and `T := restrictT`, so `D.form x (D.T x)` is
`ν (θ_{2p} x · T x)`, which `positiveTransfer_pairing_nonneg` bounds below by `0`.

Scope. `hposOdd` is a hypothesis at an odd reflection constant, the link reflection, and is not
supplied here; `ReflectionHalfSpace`'s positivity chain is stated at `2 * p` and its analogue of
`boxR_ne_tau` hardwires that constant, so it has no odd instantiation. The blocks differ: at an even
constant the shared block is the transverse links on the plane with the dagger trivial, at an odd
one the axis links with the dagger inverting, which is `OddLagSplit`'s subject.
`GNSCompare.gapAt_of_positiveTransfer_of_rayleigh` consumes `PositiveTransfer` together with a
Rayleigh bound `⟨T y, y⟩ ≤ Λ ‖y‖ ^ 2` on the vacuum complement; only the first is supplied here.

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

/-- `GNSHilbert.PositiveTransfer (transferData_of_state_facts τ p ν hinv hpos hnu)` holds if and
only if `ReflPositiveOn (latticeReflection τ (2 * p - 1)) (halfSpaceAlg τ p) ν`. Both directions go
through `positiveTransfer_pairing_eq`, which is an equality of reals, so neither side is stronger
than the other.

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

/-- `TransferGap.GapAt` on the assembled data, unfolded into reflection pairings:
`GapAt (transferData_of_state_facts τ p ν hinv hpos hnu) r` holds if and only if, for every `F` in
`halfSpaceAlg τ p` with `ν (ireflObs τ (2 * p) F * 1) = 0`,

    ν (ireflObs τ (2 * p - 2) F * F) ≤ r ^ 2 * ν (ireflObs τ (2 * p) F * F).

Both directions rewrite by `gapAt_pairing_eq` at `c = 2 * p`.

Scope. This is a statement on the algebra, before any completion; it mentions no spectrum, no
operator norm and no Hilbert space, only the state and two reflections. It is about a particular
state `ν`, not about a profile, so the flat-profile results such as `FlatProfileAllApertures` are
different statements. The carrier is `ℤ⁴`, where
`HalfSpaceAlgebra.shift_no_finite_order_on_halfSpaceAlg` gives the shift infinite order, so the
periodic-shift obstruction `HalfLineTransfer.no_rate_of_shift_transfer` does not apply. The
equivalence gives no bound on `r`; nothing here proves either side.

DERIVED: `4` is the spacetime dimension `τ` indexes; `2` appears three times — as the plane-to-constant
conversion in `2 * p`, as the separation `2 * p - 2` between the two reflection constants, and as
the exponent on `r`, which is `GapAt`'s own degree. `1` is the constant observable in the side
condition, and `0` the value that side condition asserts. -/
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

/-- The same equivalence with the side condition written as `ν F = 0`. Multiplying by the constant
is the identity and `hinv` says the state does not see the reflection, so
`ν (ireflObs τ (2 * p) F * 1) = ν F`.

DERIVED: `4` is the spacetime dimension `τ` indexes; `2` is the plane-to-constant conversion in
`2 * p`, the separation in `2 * p - 2`, and the exponent on `r`; `0` is the value of `ν F` in the
side condition. -/
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

/-- The same equivalence with the subtraction built in and no side condition: `GapAt … r` holds if
and only if, for every `F ∈ halfSpaceAlg τ p`,

    ν (θ_{2p-2} F' · F') ≤ r ^ 2 * ν (θ_{2p} F' · F'),   where `F' = F - ν F • 1`.

`F'` lies in the algebra, which is a submodule containing `1`, and has `ν F' = 0`; at `ν F = 0` it
is `F` itself.

Scope: the quantity bounded is the connected pairing by construction rather than by hypothesis. At
`F = 1` the subtracted observable is `0` and both sides are `0`.

DERIVED: `4` is the spacetime dimension `τ` indexes; `2` is the plane-to-constant conversion, the
separation `2 * p - 2` between the two reflection constants, and the exponent on `r`; `1` is the
constant observable subtracted against. -/
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

/-- It suffices to check the pairing inequality where the lag-zero subtracted pairing is strictly
positive: if the inequality of `gapAt_iff_subtracted_pairing` holds at every `F ∈ halfSpaceAlg τ p`
with `0 < ν (ireflObs τ (2 * p) (F - ν F • 1) * (F - ν F • 1))`, then `GapAt … r` holds. In the
degenerate branch `form_nonneg` and `T_contract` put both sides at `0`, so the inequality holds at
every `r`.

Scope. The content at a non-degenerate observable is unchanged, and the reverse implication is
immediate, so this weakens a hypothesis rather than establishing a bound. The observables removed
are those the form annihilates, the same null space that separates `D.T ≠ 1` from
`ClayAssembly.TransferMovesSomething`. The argument is `TransferGap.gapAt_of_nondegenerate`'s,
repeated in these coordinates rather than invoked, because the translation between a carrier element
and a mean-subtracted observable is what `gapAt_iff_subtracted_pairing` performs.

DERIVED: the `2`s are the plane-to-constant conversion, the two-step separation and the form's own
degree, as in `gapAt_iff_subtracted_pairing`; the `0` is the sign asserted and the mean subtracted;
the `1` is the constant observable; `4` is the dimension. -/
theorem gapAt_of_subtracted_pairing_nondegenerate (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G))
    (hinv : IsReflectionInvariant (latticeReflection τ (2 * p)) ν)
    (hpos : ReflPositiveOn (latticeReflection τ (2 * p)) (halfSpaceAlg (G := G) τ p) ν)
    (hnu : ∀ f : C(IConf G, ℝ), ν (ishiftObsL τ f) = ν f) (r : ℝ)
    (h : ∀ F ∈ halfSpaceAlg (G := G) τ p,
      0 < ν (ireflObs τ (2 * p) (F - ν F • 1) * (F - ν F • 1)) →
      ν (ireflObs τ (2 * p - 2) (F - ν F • 1) * (F - ν F • 1))
        ≤ r ^ 2 * ν (ireflObs τ (2 * p) (F - ν F • 1) * (F - ν F • 1))) :
    MassGap.TransferGap.GapAt (transferData_of_state_facts τ p ν hinv hpos hnu) r := by
  refine (gapAt_iff_subtracted_pairing τ p ν hinv hpos hnu r).mpr (fun F hF => ?_)
  have hsub : (F - ν F • (1 : C(IConf G, ℝ))) ∈ halfSpaceAlg (G := G) τ p :=
    Submodule.sub_mem _ hF (Submodule.smul_mem _ _ (one_mem_halfSpaceAlg τ p))
  set D := transferData_of_state_facts τ p ν hinv hpos hnu with hD
  have hnn : 0 ≤ ν (ireflObs τ (2 * p) (F - ν F • (1 : C(IConf G, ℝ)))
      * (F - ν F • (1 : C(IConf G, ℝ)))) :=
    D.form_nonneg ⟨F - ν F • (1 : C(IConf G, ℝ)), hsub⟩
  rcases lt_or_eq_of_le hnn with hp | hz
  · exact h F hF hp
  · have hxx : D.form ⟨F - ν F • (1 : C(IConf G, ℝ)), hsub⟩
        ⟨F - ν F • (1 : C(IConf G, ℝ)), hsub⟩ = 0 := hz.symm
    have hcontr := D.T_contract ⟨F - ν F • (1 : C(IConf G, ℝ)), hsub⟩
    rw [hxx] at hcontr
    rw [← hz, mul_zero,
      ← gapAt_pairing_eq τ (2 * p) ν hnu (F - ν F • (1 : C(IConf G, ℝ)))]
    exact hcontr

#print axioms gapAt_of_subtracted_pairing_nondegenerate

end Lattice

end MassGap.WilsonTransferReduction
