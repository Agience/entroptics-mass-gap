import Mathlib
import MassGap.SchwarzIteration

/-!
# MassGap.TransferAssembly — a full `TransferData`, from a state and a reflection

## What this is

`Transfer.TransferData` is the object `GNSHilbert` turns into a Hilbert space with a bounded
self-adjoint transfer operator fixing the vacuum, and `Reconstruction` turns into `H = −log T`. It has
six fields. This file builds one, `assembleTransferData`, and **every field is discharged** from:

| input | what it is |
|---|---|
| `R : Reflection X` | the time reflection — `LatticeReflection.latticeReflection` |
| `ν : State X` | an infinite-volume state — `DLRLimit.exists_infinite_volume_gibbs_state` |
| `A : Submodule ℝ C(X,ℝ)` | the half-space algebra — `HalfSpaceAlgebra.halfSpaceAlg` |
| `hinv`, `hpos` | the state is reflection-invariant and **reflection-positive on `A`** |
| `C : ShiftCompat R ν` | the shift, its inverse, and their compatibility with `θ` and `ν` |
| `hstable` | `A` is forward-shift stable — `HalfSpaceAlgebra.halfSpaceAlg_shift_stable` |
| `hone`, `hTone` | the constant is in `A` and the shift fixes it |
| `hTnorm`, `hθnorm` | neither map increases the supremum norm |

**`T_symm` and `T_contract` are not among the inputs.** They are proved, by `form_shift_symm` and
`contract_of_bounded_orbit`.

## ⚠ The one input that is not available

**`hpos` — reflection positivity of an infinite-volume Wilson state on the half-space algebra.**
Everything else on that list is either built in the tree or is a routine property of precomposition.
`hpos` is not, and `LatticeReflection`'s header says why the gap is wider than a change of lattice:
the tree's finite-volume positivity is about a correlation SEQUENCE, on a SLAB, of a PERIODIC
lattice, at the EVEN reflection constant, and needs `0 ≤ β`.

So this file does not prove the Yang–Mills transfer operator exists. **What it does is reduce that
claim to one hypothesis**, with the rest of the assembly machine-checked, so that anyone supplying
`hpos` gets the Hilbert space, the operator and the Hamiltonian without further work.

## ⚠ And `ShiftCompat` forces the shift to be invertible

`T_S` gives `T ∘ S = id`; applying `θ` to `theta_T` and using involutivity gives `T = θ ∘ S ∘ θ`, and
chasing once more gives `S ∘ T = id`. **So `S` is a two-sided inverse and `T` is bijective on
`C(X,ℝ)`.** That is not in tension with `HalfSpaceAlgebra`: the shift is invertible on the FULL
algebra of `IConf G` (because `ishiftConf` is a bijection, `ℤ` having no boundary), while the
half-space algebra is only FORWARD-stable. `assembleTransferData` uses both facts, in different
places — invertibility for `T_symm`, forward stability for the carrier — and they are consistent
precisely because the lattice is infinite. On a half-line of `ℕ` the shift would not be invertible and
`ShiftCompat` would be unsatisfiable.

`shift_inverse_is_two_sided` proves the derivation rather than leaving it as a remark.
-/

namespace MassGap.TransferAssembly

open MassGap.InfiniteReflection MassGap.DLRLimit MassGap.SchwarzIteration

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-! ## 1. What `ShiftCompat` already forces -/

/-- **THE BACKWARD SHIFT IS A TWO-SIDED INVERSE.** `T_S` only asks `T ∘ S = id`; together with
`theta_T` and involutivity of `θ` it gives `S ∘ T = id` as well.

Proved rather than remarked, because it is the fact that makes `ShiftCompat` unsatisfiable on a
half-LINE and satisfiable on `ℤ`: the hypotheses quietly demand an invertible translation, and that
demand should be visible.

DERIVED: no numeral. -/
theorem shift_inverse_is_two_sided {R : Reflection X} {ν : State X} (C : ShiftCompat R ν)
    (f : C(X, ℝ)) : C.S (C.T f) = f := by
  have hTf : ∀ g : C(X, ℝ), C.T g = R.θ (C.S (R.θ g)) := by
    intro g
    have h := C.theta_T g
    calc C.T g = R.θ (R.θ (C.T g)) := (R.θ_involutive _).symm
      _ = R.θ (C.S (R.θ g)) := by rw [h]
  have hkey : ∀ g : C(X, ℝ), R.θ g = C.S (R.θ (C.S g)) := by
    intro g
    have h := C.theta_T (C.S g)
    rw [C.T_S] at h
    exact h
  calc C.S (C.T f) = C.S (R.θ (C.S (R.θ f))) := by rw [hTf]
    _ = R.θ (R.θ f) := (hkey (R.θ f)).symm
    _ = f := R.θ_involutive f

#print axioms shift_inverse_is_two_sided

/-! ## 2. The shift, restricted to the half-space algebra -/

/-- The forward shift as an endomorphism of the half-space algebra. `hstable` is exactly
`HalfSpaceAlgebra.halfSpaceAlg_shift_stable`.

DERIVED: no numeral. -/
def restrictT {R : Reflection X} {ν : State X} (C : ShiftCompat R ν)
    (A : Submodule ℝ C(X, ℝ)) (hstable : ∀ f ∈ A, C.T f ∈ A) : ↥A →ₗ[ℝ] ↥A where
  toFun f := ⟨C.T (f : C(X, ℝ)), hstable _ f.2⟩
  map_add' f g := by
    apply Subtype.ext
    exact map_add C.T _ _
  map_smul' r f := by
    apply Subtype.ext
    exact map_smul C.T _ _

@[simp] theorem restrictT_coe {R : Reflection X} {ν : State X} (C : ShiftCompat R ν)
    (A : Submodule ℝ C(X, ℝ)) (hstable : ∀ f ∈ A, C.T f ∈ A) (f : ↥A) :
    ((restrictT C A hstable f : ↥A) : C(X, ℝ)) = C.T (f : C(X, ℝ)) := rfl

/-- **ITERATING THE RESTRICTION IS RESTRICTING THE ITERATE**, which is what lets the orbit bound —
stated on `C(X, ℝ)` — be read on the submodule.

DERIVED: no numeral. -/
theorem restrictT_iterate {R : Reflection X} {ν : State X} (C : ShiftCompat R ν)
    (A : Submodule ℝ C(X, ℝ)) (hstable : ∀ f ∈ A, C.T f ∈ A) (f : ↥A) (n : ℕ) :
    (((⇑(restrictT C A hstable))^[n] f : ↥A) : C(X, ℝ)) = (⇑C.T)^[n] (f : C(X, ℝ)) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply' (⇑(restrictT C A hstable)) k,
        Function.iterate_succ_apply' (⇑C.T) k, restrictT_coe, ih]

#print axioms restrictT_iterate

/-! ## 3. ⭐ The assembly -/

/-- **⭐ A FULL `Transfer.TransferData`, EVERY FIELD DISCHARGED.**

`T_symm` is `form_shift_symm`; `T_contract` is `contract_of_bounded_orbit` fed by
`orbit_bounded_of_state`; the form and `vac_norm` are `InfiniteReflection`'s. Nothing is assumed
about the operator beyond what `ShiftCompat` states, and nothing about the form beyond `hpos`.

**So `GNSHilbert` and `Reconstruction` apply**: this yields a Hilbert space, a unit vacuum, a bounded
self-adjoint `T` fixing it, and hence `H = −log T` with `H ≥ 0` once a spectral gap is supplied.

**`hpos` is the one input the tree cannot currently supply** — see the module header. This is a
reduction, not a construction.

DERIVED: no numeral. The bound `‖1‖ * ‖1‖` fed to `contract_of_bounded_orbit` is
`orbit_bounded_of_state`'s, computed from the caller's vector rather than chosen. -/
noncomputable def assembleTransferData (R : Reflection X) (ν : State X)
    (A : Submodule ℝ C(X, ℝ))
    (hinv : IsReflectionInvariant R ν) (hpos : ReflPositiveOn R A ν)
    (C : ShiftCompat R ν) (hstable : ∀ f ∈ A, C.T f ∈ A)
    (hone : (1 : C(X, ℝ)) ∈ A) (hTone : C.T 1 = 1)
    (hTnorm : ∀ f : C(X, ℝ), ‖C.T f‖ ≤ ‖f‖) (hθnorm : ∀ f : C(X, ℝ), ‖R.θ f‖ ≤ ‖f‖) :
    MassGap.Transfer.TransferData ↥A where
  toReflForm := stateReflForm R ν A hinv hpos
  T := restrictT C A hstable
  vac := ⟨1, hone⟩
  T_symm x y := form_shift_symm C (x : C(X, ℝ)) (y : C(X, ℝ))
  T_contract x := by
    refine contract_of_bounded_orbit (stateReflForm R ν A hinv hpos)
      (⇑(restrictT C A hstable)) (fun y z => form_shift_symm C _ _) x
      (‖(x : C(X, ℝ))‖ * ‖(x : C(X, ℝ))‖) (fun n => ?_)
    show ν (R.θ ((((⇑(restrictT C A hstable))^[n] x : ↥A)) : C(X, ℝ))
        * ((((⇑(restrictT C A hstable))^[n] x : ↥A)) : C(X, ℝ))) ≤ _
    rw [restrictT_iterate]
    exact orbit_bounded_of_state ν R hTnorm hθnorm (x : C(X, ℝ)) n
  T_vac := by
    apply Subtype.ext
    exact hTone
  vac_norm := stateReflForm_vac_norm R ν A hinv hpos hone

#print axioms assembleTransferData

end MassGap.TransferAssembly
