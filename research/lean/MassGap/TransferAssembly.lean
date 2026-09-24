import Mathlib
import MassGap.SchwarzIteration

/-!
# MassGap.TransferAssembly — a full `TransferData`, from a state and a reflection

## What this is

`Transfer.TransferData` is the object `GNSHilbert` turns into a Hilbert space with a bounded
self-adjoint transfer operator fixing the vacuum, and `Reconstruction` turns into `H = −log T`. It has
six fields. `assembleTransferData` constructs one, discharging every field from these inputs:

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

`T_symm` and `T_contract` are not inputs: they are proved inside the construction, by
`form_shift_symm` and by `contract_of_bounded_orbit` fed by `orbit_bounded_of_state`.

## Scope of the inputs

`assembleTransferData` takes every item above as a hypothesis; it constructs none of them. `hpos` in
particular — reflection positivity of the state on `A` — is supplied by the caller. The tree's own
reflection-positivity results are of a different shape: as `LatticeReflection`'s header records, they
are about a correlation sequence, on a slab, of a periodic lattice, at the even reflection constant,
and under `0 ≤ β`. Given all the inputs, the output is a `Transfer.TransferData`, and `GNSHilbert`
and `Reconstruction` apply to it.

## `ShiftCompat` forces the shift to be invertible

`T_S` gives `T ∘ S = id`; applying `θ` to `theta_T` and using involutivity gives `T = θ ∘ S ∘ θ`, and
chasing once more gives `S ∘ T = id`. `shift_inverse_is_two_sided` states that second identity, so
`S` is a two-sided inverse of `T` on `C(X, ℝ)`.

Invertibility on the full algebra and forward stability of the half-space algebra are separate
conditions, and `assembleTransferData` uses each in its own place: invertibility through `T_symm`,
forward stability through `hstable` as the carrier's closure property. For `IConf G` the shift is
invertible on the full algebra because `ishiftConf` is a bijection, `ℤ` having no boundary, while
`HalfSpaceAlgebra` is forward-stable only. On a half-line indexed by `ℕ` the shift has no inverse, so
`ShiftCompat` has no instance there.

DERIVED: two numerals occur in the statements below. `1` is the constant function of `C(X, ℝ)`, taken
as the vacuum vector and fixed by the shift. `0` is the value of the inner product against that
vector on the vacuum complement, and hence of the state's one-point function there.
-/

namespace MassGap.TransferAssembly

open MassGap.InfiniteReflection MassGap.DLRLimit MassGap.SchwarzIteration

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-! ## 1. What `ShiftCompat` already forces -/

/-- `C.S (C.T f) = f` for every `f : C(X, ℝ)`, given a `ShiftCompat R ν`. The structure field `T_S`
asks only for `T ∘ S = id`; combined with `theta_T` and involutivity of `R.θ`, this gives the other
composite as well, so `C.S` is a two-sided inverse of `C.T` and both are bijections of `C(X, ℝ)`.

`ShiftCompat` therefore implies an invertible translation, which is a condition on the index set: it
holds for `ℤ` and has no instance on a half-line indexed by `ℕ`.

DERIVED: no numeral appears in the statement. -/
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

/-- The forward shift `C.T` restricted to a submodule `A` that it preserves, as an `ℝ`-linear
endomorphism of `↥A`. `hstable : ∀ f ∈ A, C.T f ∈ A` is the only property of `A` used; additivity and
homogeneity are inherited from `C.T` through `Subtype.ext`. For the half-space algebra, `hstable` is
`HalfSpaceAlgebra.halfSpaceAlg_shift_stable`.

DERIVED: the only numeral is the `2` of `f.2` in the construction, the projection selecting a
subtype element’s membership proof. -/
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

/-- The `n`-th iterate of `restrictT C A hstable` agrees with the `n`-th iterate of `C.T` under the
coercion `↥A → C(X, ℝ)`, for every `f : ↥A` and every `n : ℕ`. Proved by induction on `n` using
`restrictT_coe`. This is what lets `orbit_bounded_of_state`, which is stated on `C(X, ℝ)`, be applied
to orbits of the restricted map.

DERIVED: no numeral appears in the statement; `n` is universally quantified. -/
theorem restrictT_iterate {R : Reflection X} {ν : State X} (C : ShiftCompat R ν)
    (A : Submodule ℝ C(X, ℝ)) (hstable : ∀ f ∈ A, C.T f ∈ A) (f : ↥A) (n : ℕ) :
    (((⇑(restrictT C A hstable))^[n] f : ↥A) : C(X, ℝ)) = (⇑C.T)^[n] (f : C(X, ℝ)) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply' (⇑(restrictT C A hstable)) k,
        Function.iterate_succ_apply' (⇑C.T) k, restrictT_coe, ih]

#print axioms restrictT_iterate

/-! ## 3. The assembly -/

/-- A `Transfer.TransferData ↥A` built from a reflection `R`, a state `ν`, a submodule `A` and the
shift data `C`, with all six fields discharged.

The inputs are: `hinv`, invariance of `ν` under `R.θ`; `hpos`, reflection positivity of `ν` on `A`;
`C : ShiftCompat R ν`, the forward and backward shifts with their compatibility with `R.θ` and `ν`;
`hstable`, closure of `A` under `C.T`; `hone`, membership of the constant function `1` in `A`;
`hTone : C.T 1 = 1`; and `hTnorm`, `hθnorm`, stating that neither `C.T` nor `R.θ` increases the
supremum norm.

The fields are filled as follows. `toReflForm` and `vac_norm` are `stateReflForm` and
`stateReflForm_vac_norm`; `T` is `restrictT C A hstable`; `vac` is the constant function `1`, in `A`
by `hone`; `T_vac` is `hTone`; `T_symm` is `form_shift_symm`; and `T_contract` is
`contract_of_bounded_orbit`, whose orbit bound is supplied by `orbit_bounded_of_state` through
`restrictT_iterate`. Since the result is a `TransferData`, `GNSHilbert` and `Reconstruction` apply
to it.

Every item in the argument list is a hypothesis; none is constructed here, `hpos` included.

DERIVED: `1` is the constant function of `C(X, ℝ)`, taken as the vacuum vector and required by
`hTone` to be fixed by the shift. The orbit bound `‖1‖ * ‖1‖` appears only in the construction, where
it is `orbit_bounded_of_state`'s value at the caller's vector rather than a chosen level. -/
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

/-- **The assembled form at a translated observable IS the state's reflected two-point function.**

`assembleTransferData`'s form is `ν (R.θ F * H)` and its `T` is `restrictT C A hstable`, so

    D.form x ((D.T ^ n) x)  =  ν (R.θ x * (C.T)^[n] x)

with both sides read on the underlying continuous functions. `Module.End.pow_apply` moves from the
operator power to the function iterate and `restrictT_iterate` strips the submodule coercion.

**This is the identification the relative route needed.**
`ClayCapstone.clay_gap_of_two_point_decay` reduces the Clay spectral statement to decay of
`D.form x ((D.T ^ (2 * n)) x)` against `D.form x x`; this says that quantity is the state's pairing
of `R.θ x` with `x` translated `2 * n` steps — a two-point function at a separation growing with
`n`, compared against the same pairing at separation zero. Both sides are now objects a correlation
estimate speaks about, rather than objects of the GNS construction.

What remains is to put a strong-coupling bound on the right-hand side at the Wilson data.
`GaugeInvariantAlgebra.stateFree_pairing_abs_le` bounds a pairing of exactly this shape for plaquette
observables, but it is stated at `stateFree` on a box rather than at the limiting state `ν`, and for
the reflected plaquette rather than for a translate — so the two are not yet the same statement.

DERIVED: `1` is the unit observable, carried in unchanged from `assembleTransferData`'s own `hone`
and `hTone` — the algebra contains the constants and the translation fixes them. `n` is the
caller's. -/
theorem assembleTransferData_form_pow (R : Reflection X) (ν : State X)
    (A : Submodule ℝ C(X, ℝ))
    (hinv : IsReflectionInvariant R ν) (hpos : ReflPositiveOn R A ν)
    (C : ShiftCompat R ν) (hstable : ∀ f ∈ A, C.T f ∈ A)
    (hone : (1 : C(X, ℝ)) ∈ A) (hTone : C.T 1 = 1)
    (hTnorm : ∀ f : C(X, ℝ), ‖C.T f‖ ≤ ‖f‖) (hθnorm : ∀ f : C(X, ℝ), ‖R.θ f‖ ≤ ‖f‖)
    (x : ↥A) (n : ℕ) :
    (assembleTransferData R ν A hinv hpos C hstable hone hTone hTnorm hθnorm).form x
        (((assembleTransferData R ν A hinv hpos C hstable hone hTone hTnorm hθnorm).T ^ n) x)
      = ν (R.θ (x : C(X, ℝ)) * (⇑C.T)^[n] (x : C(X, ℝ))) := by
  show ν (R.θ (x : C(X, ℝ)) * ((((restrictT C A hstable) ^ n) x : ↥A) : C(X, ℝ))) = _
  rw [Module.End.pow_apply, restrictT_iterate]

#print axioms assembleTransferData_form_pow

/-- **The inner product against the vacuum vector IS the state's one-point function.**

`vacGNS` is the class of the constant `1`, so the inner product against it is the form at `1`, which
is `ν (R.θ 1 * x)`; `Reflection.θ_one` fixes the constant and the product collapses.

DERIVED: `1` is the constant observable the vacuum is the class of, and the value `θ` fixes it at. -/
theorem inner_vacGNS_mk (R : Reflection X) (ν : State X) (A : Submodule ℝ C(X, ℝ))
    (hinv : IsReflectionInvariant R ν) (hpos : ReflPositiveOn R A ν)
    (C : ShiftCompat R ν) (hstable : ∀ f ∈ A, C.T f ∈ A)
    (hone : (1 : C(X, ℝ)) ∈ A) (hTone : C.T 1 = 1)
    (hTnorm : ∀ f : C(X, ℝ), ‖C.T f‖ ≤ ‖f‖) (hθnorm : ∀ f : C(X, ℝ), ‖R.θ f‖ ≤ ‖f‖)
    (x : ↥A) :
    (inner ℝ
        (assembleTransferData R ν A hinv hpos C hstable hone hTone hTnorm hθnorm).vacGNS
        (MassGap.Transfer.GNS.mk
          (assembleTransferData R ν A hinv hpos C hstable hone hTone hTnorm hθnorm).toReflForm
          x) : ℝ)
      = ν (x : C(X, ℝ)) := by
  rw [MassGap.Transfer.TransferData.vacGNS, MassGap.Transfer.GNS.inner_mk]
  show ν (R.θ (1 : C(X, ℝ)) * (x : C(X, ℝ))) = ν (x : C(X, ℝ))
  rw [R.θ_one, one_mul]

#print axioms inner_vacGNS_mk

/-- **On the vacuum complement the state's one-point function vanishes.** Immediate from
`inner_vacGNS_mk`.

DERIVED: `0` is the value of the inner product on the complement, and hence of the one-point
function; `1` is the constant observable, carried in unchanged from `assembleTransferData`'s `hone`
and `hTone`. -/
theorem nu_eq_zero_of_vac_orth (R : Reflection X) (ν : State X) (A : Submodule ℝ C(X, ℝ))
    (hinv : IsReflectionInvariant R ν) (hpos : ReflPositiveOn R A ν)
    (C : ShiftCompat R ν) (hstable : ∀ f ∈ A, C.T f ∈ A)
    (hone : (1 : C(X, ℝ)) ∈ A) (hTone : C.T 1 = 1)
    (hTnorm : ∀ f : C(X, ℝ), ‖C.T f‖ ≤ ‖f‖) (hθnorm : ∀ f : C(X, ℝ), ‖R.θ f‖ ≤ ‖f‖)
    (x : ↥A)
    (h : (inner ℝ
        (assembleTransferData R ν A hinv hpos C hstable hone hTone hTnorm hθnorm).vacGNS
        (MassGap.Transfer.GNS.mk
          (assembleTransferData R ν A hinv hpos C hstable hone hTone hTnorm hθnorm).toReflForm
          x) : ℝ) = 0) :
    ν (x : C(X, ℝ)) = 0 :=
  (inner_vacGNS_mk R ν A hinv hpos C hstable hone hTone hTnorm hθnorm x).symm.trans h

#print axioms nu_eq_zero_of_vac_orth

/-- **On the vacuum complement, subtracting the mean does nothing.**

This is what reconciles the two shapes. The strong-coupling estimates are stated on
`f - ⟨f⟩ • 1`, with the mean subtracted explicitly; the obligation in
`ClayCapstone.gaugeInv_clay_gap_of_state_decay` instead restricts to observables whose class lies in
the vacuum complement. `nu_eq_zero_of_vac_orth` says the mean is already zero there, so the two
statements are about the same observable.

DERIVED: `0` is the vanishing one-point function; `1` is the unit observable carrying the
subtraction. -/
theorem sub_mean_eq_self_of_vac_orth (R : Reflection X) (ν : State X)
    (A : Submodule ℝ C(X, ℝ))
    (hinv : IsReflectionInvariant R ν) (hpos : ReflPositiveOn R A ν)
    (C : ShiftCompat R ν) (hstable : ∀ f ∈ A, C.T f ∈ A)
    (hone : (1 : C(X, ℝ)) ∈ A) (hTone : C.T 1 = 1)
    (hTnorm : ∀ f : C(X, ℝ), ‖C.T f‖ ≤ ‖f‖) (hθnorm : ∀ f : C(X, ℝ), ‖R.θ f‖ ≤ ‖f‖)
    (x : ↥A)
    (h : (inner ℝ
        (assembleTransferData R ν A hinv hpos C hstable hone hTone hTnorm hθnorm).vacGNS
        (MassGap.Transfer.GNS.mk
          (assembleTransferData R ν A hinv hpos C hstable hone hTone hTnorm hθnorm).toReflForm
          x) : ℝ) = 0) :
    (x : C(X, ℝ)) - ν (x : C(X, ℝ)) • (1 : C(X, ℝ)) = (x : C(X, ℝ)) := by
  rw [nu_eq_zero_of_vac_orth R ν A hinv hpos C hstable hone hTone hTnorm hθnorm x h,
    zero_smul, sub_zero]

#print axioms sub_mean_eq_self_of_vac_orth

end MassGap.TransferAssembly
