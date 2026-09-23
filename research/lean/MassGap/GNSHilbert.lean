import Mathlib
import MassGap.OSPositivity
import MassGap.HalfLineTransfer

/-!
# MassGap.GNSHilbert — a complete complex Hilbert space and a unit vacuum from a reflection form

`Transfer.GNS` turns a `Transfer.ReflForm` into a real inner product space, and
`ReflectionStrong.wilsonGibbsReflForm` is such a form on the Wilson Gibbs measure. This module adds
completeness and complex scalars.

`Transfer.GNS P` carries no `CompleteSpace` instance. `OSPositivity.cform` is the sesquilinear
complexification of a `PreForm`, with conjugate symmetry, sesquilinearity and a nonnegative diagonal
proved there, and `OSPositivity.cform_eq_osPairing` identifies it with the complex Gibbs pairing
`⟨conj (F ∘ Θ) * G⟩`; what `OSPositivity` does not do is place a `Module ℂ` instance on the pair
type, which this module does.

No quotient is taken. `PreInnerProductSpace.Core` asks only for semidefiniteness, and
`UniformSpace.Completion` Hausdorffifies and completes in one step, so the null space is collapsed
there. `MomentMeasure` uses the same pattern.

## Contents

1. `Pre P` — the pair module `A × A` as a complex vector space, with `Pre.core` the semi-inner
   product built from `cform` and `Pre.norm_mul_norm` relating the seminorm to the two components.
2. `H P` — its completion, complex and complete (`complete_H`); `inner_coe` identifies the inner
   product of two classes with `cform`.
3. `Omega P v` — `v` in the real component and `0` in the imaginary one. `norm_Omega` gives
   `‖Ω‖ = 1` from `P.form v v = 1`, `Omega_ne_zero` and `nontrivial_H` follow.
4. `cT`, `cTL`, `opT` — a `Transfer.TransferData A` complexified and extended to the completion,
   with `norm_opT_le_one`, `isSelfAdjoint_opT`, `opT_Omega`, `opT_eq_id_of_T_eq_id`,
   `norm_Omega_vac` and `nontrivial_H_of_transferData`. Each closes from `TransferData`'s own
   fields.
   `PositiveTransfer D` is `∀ x, 0 ≤ D.form x (D.T x)`, stated before the completion;
   `re_inner_opT_nonneg` carries it to the whole completion, `positiveTransfer_of_T_eq_id` proves it
   when `T` is the identity, and `positiveTransfer_of_gram` proves it from a linear `S` with
   `form x (T x) = form (S x) (S x)`.
5. `ymH`, `ymOmega`, `ymOmega_norm`, `ymOmega_ne_zero`, `nontrivial_ymH`, `complete_ymH` — the
   Wilson instance of the space and the vacuum, at every real `β` with no coupling hypothesis, from
   `wilsonGibbsReflForm` and `wilsonGibbsReflForm_vac_norm`.
6. `shiftSlab_eq_id`, `shift_descends_to_id` — on the premise `SlabShiftStable`, at `n = 2 * m` with
   `2 ≤ m`, the slab shift acts as the identity on the slab algebra and `opT` is the identity on
   `H`.
7. `trivialTransfer`, `positiveTransfer_trivial`, `ym_target_discharged_trivially` — a
   `TransferData` on the Wilson slab algebra with `T = LinearMap.id`, needing no premise, and the
   six-clause statement it satisfies.
8. `ym_inner_eq_osPairing` — the inner product of `ymH` is one Gibbs expectation of the complex OS
   integrand at the site reflection `reflConf τ (a + a)`.

## Scope

* `wilsonGibbsReflForm` lives on a slab of a periodic lattice at fixed spacing. Nothing here is
  about infinite volume, the continuum or a half-space, and `OSPositivity`'s separations from OS3
  stand.
* `nontrivial_ymH` says the space is nonzero. It does not say the dimension exceeds one, and no
  such statement is made here; nothing in the tree exhibits a non-constant slab observable. At
  `N = 1` the gauge group is trivial (`SimpleGroup.subsingleton_SU_one`), every observable is
  constant, and both `SlabShiftStable` and `SlabShiftContractive` hold, so Part 6's theorems have a
  model. At `N ≥ 2` neither premise is decided in this tree.
* `ym_target_discharged_trivially` shows the five clauses "unit vacuum, self-adjoint, contraction,
  vacuum fixed, positive" are satisfied by `T = LinearMap.id` on the Wilson slab algebra, so they do
  not by themselves pin `T` to a time translation. `shift_descends_to_id` shows that pinning `T` to
  the slab shift, on its own stability premise and at this geometry, gives the identity operator on
  `H`; if the premise fails there is no descended operator. `PeriodicRayleigh.const_of_slabShiftStable`
  is the module-level form of the same statement, and `HalfLineTransfer.shiftObs_pow_period` an
  independent one.
* `PositiveTransfer` does not follow from contractivity, which bounds `|λ|` and says nothing about
  the sign of `λ`. It is reflection positivity about a half-integer time plane.
  `WilsonTransferReduction.positiveTransfer_iff_odd_reflPositive` makes it equivalent to reflection
  positivity at the odd constant `2 * p - 1` on the half-space algebra, and
  `ReflectionHalfSpace.wilson_positiveTransfer_of_common_subsequential_limit` supplies that side
  from `N ≠ 0`, `0 ≤ β`, two filters refining `atTop`, and the two cube families converging along
  them to one state at the all-identity boundary condition. `0 ≤ β` is load-bearing:
  `CharacterExpansion.NegControl.su3_kernel_nonneg_iff` refutes the cross kernel's positive
  semidefiniteness below zero. `N ≠ 0` does not exclude `N = 1`, where `SU 1` is a singleton and
  `halfSpaceAlg` is the constants.
* `ReflectionHalfSpace.transferData_of_state_facts_T_ne_id` proves `T ≠ 1` on the half-space
  carrier, given a function on the group separating two elements;
  `HaarVariance.reTr_flipEl_ne_reTr_one` supplies one at `SU (m + 2)`, `Re tr` reading `m + 2` at
  the identity against `m - 2` at `flipEl m`. At `SU 0` and `SU 1` no such function exists.
  `ReflectionHalfSpace.halfSpaceAlg_has_nonconstant` separates configurations by an observable and
  has a different type.
* Motion in the algebra is not motion in the completion: `opT [F] = [F]` whenever `T F - F` lies in
  the null space of the form, so `T ≠ 1` does not give `ClayAssembly.TransferMovesSomething`.
* `WilsonTransferReduction.transferData_of_state_facts` is a `def` parameterised by three unproved
  facts about a state. `ReflectionHalfSpace.reflection_facts_on_halfSpaceAlg` supplies two of them
  for one state; `WilsonState` records that `wilsonStateAt` is not shown to satisfy any.
* No Hamiltonian is constructed here. `Reconstruction.hamiltonian` uses Mathlib's `cfc` and needs
  `-Real.log` continuous on `spectrum ℝ T`, that is `0 ∉ spectrum T`; positivity and injectivity of
  `T` do not give that, and a contraction on an infinite-dimensional space can be injective with `0`
  in its spectrum, as multiplication by `x` on `L²[0, 1]` is.
-/

namespace MassGap.GNSHilbert

open MassGap MassGap.Transfer MassGap.OSPositivity
open MassGap.LogConvex MassGap.WilsonHypercubic MassGap.ReflectionStrong
open MassGap.ActionSplit

/-! ## Part 1 — the pair module as a complex vector space

`OSPositivity.cscal` is the complex scalar action on a pair of real vectors, defined there without a
`Module ℂ` instance. Here it becomes one, on a type synonym carrying the form as a parameter, so the
seminorm attaches to a type remembering which form produced it — the same device as
`MomentMeasure.Pre`.
-/

section Abstract

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

set_option linter.unusedVariables false in
/-- The complexification of the observable module: a type synonym for `A × A` carrying the form as
a parameter, so that the seminorm below attaches to a type remembering which form produced it.

DERIVED: no numeral occurs. -/
def Pre (P : Transfer.ReflForm A) : Type _ := A × A

namespace Pre

variable {P : Transfer.ReflForm A}

instance instAddCommGroup (P : Transfer.ReflForm A) : AddCommGroup (Pre P) :=
  inferInstanceAs (AddCommGroup (A × A))

/-- The complex scalar action on `Pre P`, which is `OSPositivity.cscal` transported along the type
synonym.

DERIVED: no numeral occurs. -/
instance instSMul (P : Transfer.ReflForm A) : SMul ℂ (Pre P) :=
  ⟨fun c z => (cscal c (z : A × A) : Pre P)⟩

@[simp] theorem smul_fst (c : ℂ) (z : Pre P) :
    ((c • z : Pre P) : A × A).1 = c.re • (z : A × A).1 + (-c.im) • (z : A × A).2 := rfl

@[simp] theorem smul_snd (c : ℂ) (z : Pre P) :
    ((c • z : Pre P) : A × A).2 = c.re • (z : A × A).2 + c.im • (z : A × A).1 := rfl

@[simp] theorem add_fst (z w : Pre P) :
    ((z + w : Pre P) : A × A).1 = (z : A × A).1 + (w : A × A).1 := rfl

@[simp] theorem add_snd (z w : Pre P) :
    ((z + w : Pre P) : A × A).2 = (z : A × A).2 + (w : A × A).2 := rfl

@[simp] theorem zero_fst : ((0 : Pre P) : A × A).1 = (0 : A) := rfl

@[simp] theorem zero_snd : ((0 : Pre P) : A × A).2 = (0 : A) := rfl

/-- A pair of real observables read as one complex vector: `x` the real part, `y` the imaginary
part.

DERIVED: no numeral occurs. -/
def ofPair (P : Transfer.ReflForm A) (x y : A) : Pre P := (x, y)

@[simp] theorem ofPair_fst (x y : A) : ((ofPair P x y : Pre P) : A × A).1 = x := rfl

@[simp] theorem ofPair_snd (x y : A) : ((ofPair P x y : Pre P) : A × A).2 = y := rfl

/-- Componentwise extensionality for `Pre P`, routed through `Prod.mk.eta` rather than `Prod`'s
extensionality lemma.

DERIVED: no numeral occurs; `.1` and `.2` are the product projections. -/
theorem ext {z w : Pre P} (h1 : (z : A × A).1 = (w : A × A).1)
    (h2 : (z : A × A).2 = (w : A × A).2) : z = w := by
  have h3 : @Eq (A × A) z w := by
    have e : (((z : A × A).1, (z : A × A).2) : A × A) = ((w : A × A).1, (w : A × A).2) := by
      rw [h1, h2]
    simpa using e
  exact h3

/-- `Module ℂ (Pre P)`, from the scalar action above. Six field identities, each a
real-linear-combination identity whose coefficients agree by `module` once `Complex.mul_re` and
`Complex.mul_im` are unfolded.

DERIVED: no numeral occurs in the statement; the `1` in the `one_smul` field is the complex
unit. -/
instance instModule (P : Transfer.ReflForm A) : Module ℂ (Pre P) where
  one_smul z := by
    refine ext ?_ ?_ <;> simp
  mul_smul c d z := by
    refine ext ?_ ?_ <;>
      simp only [smul_fst, smul_snd, Complex.mul_re, Complex.mul_im] <;> module
  smul_zero c := by
    refine ext ?_ ?_ <;> simp
  smul_add c z w := by
    refine ext ?_ ?_ <;> simp only [smul_fst, smul_snd, add_fst, add_snd] <;> module
  add_smul c d z := by
    refine ext ?_ ?_ <;> simp only [smul_fst, smul_snd, Complex.add_re, Complex.add_im,
      add_fst, add_snd] <;> module
  zero_smul z := by
    refine ext ?_ ?_ <;> simp

/-- The complex semi-inner product on `Pre P`, with `OSPositivity.cform` as the pairing.
Conjugate-symmetric by `cform_conj_symm`, semidefinite by `cform_diag_re_nonneg`, which is
`P.form_nonneg` on each component, and sesquilinear by `cform_add_left` and `cform_smul_left`.

Scope: definiteness is not claimed and is not needed; the completion collapses the null vectors.

DERIVED: no numeral occurs. -/
@[reducible] noncomputable def core (P : Transfer.ReflForm A) : PreInnerProductSpace.Core ℂ (Pre P) where
  inner z w := cform P.toPreForm (z : A × A) (w : A × A)
  conj_inner_symm z w := (cform_conj_symm P.toPreForm (z : A × A) (w : A × A)).symm
  re_inner_nonneg z := by simpa using cform_diag_re_nonneg P (z : A × A)
  add_left z w u := cform_add_left P.toPreForm (z : A × A) (w : A × A) (u : A × A)
  smul_left z w c := cform_smul_left P.toPreForm c (z : A × A) (w : A × A)

noncomputable instance instSeminormed (P : Transfer.ReflForm A) : SeminormedAddCommGroup (Pre P) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℂ (Pre P) _ _ _ (core P)

noncomputable instance instInnerProductSpace (P : Transfer.ReflForm A) :
    InnerProductSpace ℂ (Pre P) :=
  InnerProductSpace.ofCore (core P)

@[simp] theorem inner_def (z w : Pre P) :
    inner ℂ z w = cform P.toPreForm (z : A × A) (w : A × A) := rfl

/-- `‖z‖ * ‖z‖ = P.form z.1 z.1 + P.form z.2 z.2`: the seminorm squared is the sum of the form on
the two components, from `InnerProductSpace.norm_sq_eq_re_inner` and the definition of `cform`.

DERIVED: no numeral occurs; `.1` and `.2` are the product projections. -/
theorem norm_mul_norm (z : Pre P) :
    ‖z‖ * ‖z‖ = P.form (z : A × A).1 (z : A × A).1 + P.form (z : A × A).2 (z : A × A).2 := by
  have h : ‖z‖ ^ 2 = RCLike.re (inner ℂ z z) := InnerProductSpace.norm_sq_eq_re_inner _
  rw [pow_two] at h
  rw [h, inner_def]
  simp

end Pre

/-! ## Part 2 — the Hilbert space

`UniformSpace.Completion` of a seminormed inner product space is a complete complex inner product
space; Mathlib supplies the `NormedAddCommGroup`, `InnerProductSpace ℂ` and `CompleteSpace`
instances. Its Hausdorffification takes the place of `Transfer.GNS`'s quotient by the null space.
-/

/-- The Hilbert space `UniformSpace.Completion (Pre P)`: complex, complete, with Mathlib supplying
the `NormedAddCommGroup`, `InnerProductSpace ℂ` and `CompleteSpace` instances. The Hausdorffification
takes the place of a quotient by the null space.

DERIVED: no numeral occurs. -/
abbrev H (P : Transfer.ReflForm A) : Type _ := UniformSpace.Completion (Pre P)

/-- `CompleteSpace (H P)`, by `inferInstance`. Recorded as a theorem so it appears in the audit
rather than only in the instance cache.

DERIVED: no numeral occurs. -/
theorem complete_H (P : Transfer.ReflForm A) : CompleteSpace (H P) := inferInstance

/-- `inner ℂ (z : H P) (w : H P) = cform P.toPreForm z w`: the inner product of two classes in the
completion is the complexified form of their representatives.

DERIVED: no numeral occurs. -/
@[simp] theorem inner_coe (P : Transfer.ReflForm A) (z w : Pre P) :
    inner ℂ ((z : H P)) ((w : H P)) = cform P.toPreForm (z : A × A) (w : A × A) := by
  rw [UniformSpace.Completion.inner_coe]
  rfl

/-! ## Part 3 — the vacuum

`Omega P v` is `v` in the real component and `0` in the imaginary one. Its norm is `1` when the form
normalises `v`, which is a hypothesis in this part and is supplied at the Wilson instance by
`ReflectionStrong.wilsonGibbsReflForm_vac_norm`, at every real `β` and with no further premise.
-/

/-- The vacuum vector: the class in `H P` of the pair `(v, 0)`.

DERIVED: the one numeral is `0`, the imaginary component of a real observable. -/
noncomputable def Omega (P : Transfer.ReflForm A) (v : A) : H P :=
  ((Pre.ofPair P v (0 : A) : Pre P) : H P)

/-- `‖Omega P v‖ = 1` from `P.form v v = 1`. The seminorm of the pair `(v, 0)` squares to
`P.form v v + P.form 0 0 = 1` by `Pre.norm_mul_norm`, and `UniformSpace.Completion.norm_coe` carries
that to the completion.

DERIVED: the `1` is the hypothesis's own; at Yang–Mills it is the total mass of a probability
measure, through `Transfer.reflForm_one_one`. -/
theorem norm_Omega (P : Transfer.ReflForm A) {v : A} (hv : P.form v v = 1) :
    ‖Omega P v‖ = 1 := by
  have hc : ‖Omega P v‖ = ‖(Pre.ofPair P v (0 : A) : Pre P)‖ :=
    UniformSpace.Completion.norm_coe _
  have hsq : ‖(Pre.ofPair P v (0 : A) : Pre P)‖ * ‖(Pre.ofPair P v (0 : A) : Pre P)‖ = 1 := by
    rw [Pre.norm_mul_norm]
    simp only [Pre.ofPair_fst, Pre.ofPair_snd]
    rw [hv, Transfer.PreForm.form_zero_left P.toPreForm (0 : A)]
    ring
  rw [hc]
  nlinarith [norm_nonneg (Pre.ofPair P v (0 : A) : Pre P)]

/-- `Omega P v ≠ 0` from `P.form v v = 1`: a vector of norm one is not the zero vector.

DERIVED: the `1` is `norm_Omega`'s; `0` is the zero vector. -/
theorem Omega_ne_zero (P : Transfer.ReflForm A) {v : A} (hv : P.form v v = 1) :
    Omega P v ≠ (0 : H P) := by
  intro h
  have h1 := norm_Omega P hv
  rw [h, norm_zero] at h1
  exact absurd h1 (by norm_num)

/-- `Nontrivial (H P)` from `P.form v v = 1`, witnessed by `Omega P v` and `0`.

DERIVED: the `1` in `P.form v v = 1` is `norm_Omega`'s hypothesis, the normalisation of the state. -/
theorem nontrivial_H (P : Transfer.ReflForm A) {v : A} (hv : P.form v v = 1) :
    Nontrivial (H P) :=
  ⟨⟨Omega P v, 0, Omega_ne_zero P hv⟩⟩

/-! ## Part 4 — the transfer operator, abstractly

Every statement in this part follows from `Transfer.TransferData`'s own fields, with no further
hypothesis. Part 6 examines the Wilson instance.
-/

section Operator

variable (D : Transfer.TransferData A)

/-- The time translation complexified: `D.T` applied to each component of a pair. Complex linearity
follows from real linearity of `D.T` on each component.

DERIVED: no numeral occurs. -/
noncomputable def cT : Pre D.toReflForm →ₗ[ℂ] Pre D.toReflForm where
  toFun z := Pre.ofPair D.toReflForm (D.T (z : A × A).1) (D.T (z : A × A).2)
  map_add' z w := by refine Pre.ext ?_ ?_ <;> simp [map_add]
  map_smul' c z := by refine Pre.ext ?_ ?_ <;> simp [map_add, map_smul]

@[simp] theorem cT_fst (z : Pre D.toReflForm) :
    ((cT D z : Pre D.toReflForm) : A × A).1 = D.T (z : A × A).1 := rfl

@[simp] theorem cT_snd (z : Pre D.toReflForm) :
    ((cT D z : Pre D.toReflForm) : A × A).2 = D.T (z : A × A).2 := rfl

/-- `‖cT D z‖ ≤ 1 * ‖z‖`, from `D.T_contract` on each component through `Pre.norm_mul_norm`.

DERIVED: the `1` is the contraction constant `T_contract` gives, not a chosen bound. -/
theorem norm_cT_le (z : Pre D.toReflForm) : ‖cT D z‖ ≤ 1 * ‖z‖ := by
  rw [one_mul]
  have h : ‖cT D z‖ * ‖cT D z‖ ≤ ‖z‖ * ‖z‖ := by
    rw [Pre.norm_mul_norm, Pre.norm_mul_norm, cT_fst, cT_snd]
    have h1 := D.T_contract (z : A × A).1
    have h2 := D.T_contract (z : A × A).2
    linarith
  nlinarith [norm_nonneg (cT D z), norm_nonneg z]

/-- `cT D` bundled as a continuous linear map on `Pre D.toReflForm`, with `norm_cT_le` supplying
the bound through `LinearMap.mkContinuous`.

DERIVED: the `1` is `norm_cT_le`'s constant. -/
noncomputable def cTL : Pre D.toReflForm →L[ℂ] Pre D.toReflForm :=
  LinearMap.mkContinuous (cT D) 1 (norm_cT_le D)

@[simp] theorem cTL_apply (z : Pre D.toReflForm) : cTL D z = cT D z := rfl

/-- The transfer operator on the Hilbert space: the continuous extension of `cTL D` to the
completion.

DERIVED: no numeral occurs. -/
noncomputable def opT : H D.toReflForm →L[ℂ] H D.toReflForm := (cTL D).completion

@[simp] theorem opT_coe (z : Pre D.toReflForm) :
    opT D ((z : H D.toReflForm)) = ((cTL D z : Pre D.toReflForm) : H D.toReflForm) :=
  ContinuousLinearMap.completion_apply_coe _ _

/-- `‖opT D‖ ≤ 1`, by `ContinuousLinearMap.opNorm_le_bound` and induction on the completion, the
dense case being `norm_cT_le`.

Scope: this is contractivity, which follows from `TransferData.T_contract`. It says nothing about
the sign of any eigenvalue and is not a gap statement.

DERIVED: the `1` is `norm_cT_le`'s contraction constant. -/
theorem norm_opT_le_one : ‖opT D‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_le (continuous_norm.comp (opT D).continuous)
        (continuous_const.mul continuous_norm)
  | ih z =>
      simpa [cTL, UniformSpace.Completion.norm_coe] using norm_cT_le D z

/-- `cform D.toPreForm (cT D z) w = cform D.toPreForm z (cT D w)`: the complexified translation is
symmetric for the complex form, from `D.T_symm` on the four component pairings.

DERIVED: no numeral occurs. -/
theorem cform_cT (z w : Pre D.toReflForm) :
    cform D.toPreForm ((cT D z : Pre D.toReflForm) : A × A) (w : A × A)
      = cform D.toPreForm (z : A × A) ((cT D w : Pre D.toReflForm) : A × A) := by
  refine ceq ?_ ?_
  · simp only [cform_re, cT_fst, cT_snd]
    rw [D.T_symm (z : A × A).1 (w : A × A).1, D.T_symm (z : A × A).2 (w : A × A).2]
  · simp only [cform_im, cT_fst, cT_snd]
    rw [D.T_symm (z : A × A).1 (w : A × A).2, D.T_symm (z : A × A).2 (w : A × A).1]

/-- `IsSelfAdjoint (opT D)`, via `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric` and induction
on the completion in both arguments; the dense case is `cform_cT`.

DERIVED: no numeral occurs. -/
theorem isSelfAdjoint_opT : IsSelfAdjoint (opT D) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp =>
      refine isClosed_eq ?_ ?_
      · exact Continuous.inner ((opT D).continuous.comp continuous_fst) continuous_snd
      · exact Continuous.inner continuous_fst ((opT D).continuous.comp continuous_snd)
  | ih z w =>
      simp only [ContinuousLinearMap.coe_coe, opT_coe, inner_coe, cTL_apply]
      exact cform_cT D z w

/-- `opT D (Omega D.toReflForm D.vac) = Omega D.toReflForm D.vac`: the vacuum is fixed, from the
structure field `D.T_vac` on the real component and linearity on the imaginary one.

DERIVED: no numeral occurs in the statement; the `0` imaginary component is inside `Omega`. -/
theorem opT_Omega : opT D (Omega D.toReflForm D.vac) = Omega D.toReflForm D.vac := by
  rw [Omega, opT_coe]
  congr 1
  refine Pre.ext ?_ ?_
  · simpa using D.T_vac
  · simp

/-- If `D.T x = x` at every `x`, then `opT D x = x` at every `x` in the completion, by density and
continuity.

DERIVED: no numeral occurs. -/
theorem opT_eq_id_of_T_eq_id (hT : ∀ x : A, D.T x = x) (x : H D.toReflForm) : opT D x = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (opT D).continuous continuous_id
  | ih z =>
      rw [opT_coe]
      congr 1
      refine Pre.ext ?_ ?_
      · simpa using hT ((z : A × A).1)
      · simpa using hT ((z : A × A).2)

/-- `‖Omega D.toReflForm D.vac‖ = 1` for any `TransferData`, since `vac_norm` is one of its fields.
`norm_Omega` at that field.

DERIVED: the `1` is `TransferData.vac_norm`'s. -/
theorem norm_Omega_vac : ‖Omega D.toReflForm D.vac‖ = 1 :=
  norm_Omega D.toReflForm D.vac_norm

/-- `Nontrivial (H D.toReflForm)` for any `TransferData`, from `nontrivial_H` at the `vac_norm`
field.

Scope: `norm_opT_le_one`, `isSelfAdjoint_opT`, `opT_Omega` and `re_inner_opT_nonneg` all hold on the
zero space, so this is what distinguishes them from vacuous statements.

DERIVED: no numeral of its own; the `1` it rests on is `vac_norm`'s. -/
theorem nontrivial_H_of_transferData : Nontrivial (H D.toReflForm) :=
  nontrivial_H D.toReflForm D.vac_norm

/-! ### Positivity of the transfer operator

`PositiveTransfer` does not follow from `TransferData`'s fields: contractivity bounds `|λ| ≤ 1` and
says nothing about the sign of `λ`. It is reflection positivity about a half-integer time plane.
`re_inner_opT_nonneg` carries it from the module to the whole completion.

It holds whenever `T` is the identity (`positiveTransfer_of_T_eq_id`), which covers Part 6's slab
carrier on its own premise and Part 7's `trivialTransfer`. It does not cover the half-space carrier,
where `ReflectionHalfSpace.transferData_of_state_facts_T_ne_id` proves `T ≠ 1` given a separating
function on the group; see the module header for how `PositiveTransfer` is obtained there.
-/

/-- `PositiveTransfer D`: the proposition `∀ x : A, 0 ≤ D.form x (D.T x)`, positivity of the
transfer operator stated on the module, before the completion. A `Prop`; it does not follow from
`TransferData`'s fields.

DERIVED: the one numeral is `0`, the lower bound that makes the statement a positivity. -/
def PositiveTransfer (D : Transfer.TransferData A) : Prop :=
  ∀ x : A, 0 ≤ D.form x (D.T x)

/-- `PositiveTransfer D → 0 ≤ RCLike.re (inner ℂ x (opT D x))` at every `x` in the completion, by
density and continuity, the dense case adding the hypothesis on the two components.

DERIVED: the `0` of `0 ≤ …` is positivity itself. -/
theorem re_inner_opT_nonneg (h : PositiveTransfer D) (x : H D.toReflForm) :
    0 ≤ RCLike.re (inner ℂ x (opT D x)) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
      refine isClosed_le continuous_const ?_
      exact (RCLike.continuous_re).comp
        (Continuous.inner continuous_id ((opT D).continuous))
  | ih z =>
      simp only [opT_coe, cTL_apply, inner_coe]
      have h1 := h (z : A × A).1
      have h2 := h (z : A × A).2
      simpa [cform_re, cT_fst, cT_snd] using add_nonneg h1 h2

/-- `(∀ x, D.T x = x) → PositiveTransfer D`, since the conclusion is then `D.form_nonneg`, which is
the structure's reflection positivity.

Scope: this covers the carriers where `T` is the identity — Part 6's slab `TransferData` on its own
premise, and Part 7's `trivialTransfer` unconditionally. It does not cover the half-space carrier,
where `ReflectionHalfSpace.transferData_of_state_facts_T_ne_id` proves `T ≠ 1` given a separating
function on the group; there `PositiveTransfer` is obtained instead from
`ReflectionHalfSpace.wilson_positiveTransfer_of_common_subsequential_limit` through
`WilsonTransferReduction.positiveTransfer_iff_odd_reflPositive`.

DERIVED: no numeral occurs in the statement; the `0` is inside `PositiveTransfer`. -/
theorem positiveTransfer_of_T_eq_id (hT : ∀ x : A, D.T x = x) : PositiveTransfer D := by
  intro x
  rw [hT x]
  exact D.form_nonneg x

#print axioms positiveTransfer_of_T_eq_id

/-- `PositiveTransfer D` from a linear `S : A →ₗ[ℝ] A` with `D.form x (D.T x) = D.form (S x) (S x)`
at every `x`: the conclusion is then `D.form_nonneg (S x)`.

Scope. Linearity of `S` is load-bearing: with an arbitrary function the equation could be solved
pointwise wherever the form takes the required value, and the hypothesis would restate the
conclusion. The same content on the `L²` slab carrier is `SlabTransferAdjoint.SlabGramVia`, a
`FiniteGram` condition on the kernel whose sufficient half is proved there and which that module
reports as open.

DERIVED: no numeral occurs in the statement; the `0` is inside `PositiveTransfer`. -/
theorem positiveTransfer_of_gram (S : A →ₗ[ℝ] A)
    (hS : ∀ x : A, D.form x (D.T x) = D.form (S x) (S x)) : PositiveTransfer D := by
  intro x
  rw [hS x]
  exact D.form_nonneg (S x)

#print axioms positiveTransfer_of_gram

end Operator

end Abstract

/-! ## Part 5 — the Wilson instance of the space and the vacuum

`ReflectionStrong.wilsonGibbsReflForm` is a `Transfer.ReflForm` on the Wilson Gibbs measure at every
real `β`, and `wilsonGibbsReflForm_vac_norm` normalises the constant observable, so the space and
the vacuum are available with no further premise.
-/

section Wilson

variable {d n N : ℕ} [NeZero n]

/-- `H` at `ReflectionStrong.wilsonGibbsReflForm`: a complete complex inner product space whose
inner product is the complex Gibbs reflection pairing of the Wilson measure, at every real `β`.

DERIVED: the `2` in `n = 2 * m` is the two mirror planes of an even extent and the `0` in
`0 < m` is nonemptiness of the slab; both are the reflection geometry's, neither is chosen. `τ`, `a`, `m` and `β` are the caller's. -/
noncomputable abbrev ymH (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m)
    (hm0 : 0 < m) (β : ℝ) :=
  H (wilsonGibbsReflForm hN τ a m hm hm0 β)

/-- `Omega` at `wilsonGibbsReflForm` and the constant observable `1`.

DERIVED: `1` is the constant observable, whose imaginary component `Omega` sets to `0`; `2` in
`n = 2 * m` is the two mirror planes of an even extent and `0` in `0 < m` is nonemptiness of the
slab, both the reflection geometry's; `0` also appears in `N ≠ 0`, the nontriviality of the gauge
group. -/
noncomputable def ymOmega (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m)
    (hm0 : 0 < m) (β : ℝ) : ymH hN τ a m hm hm0 β :=
  Omega (wilsonGibbsReflForm hN τ a m hm hm0 β) ⟨fun _ => (1 : ℝ), one_mem_localObs⟩

/-- `‖ymOmega hN τ a m hm hm0 β‖ = 1` at every real `β`, with no coupling hypothesis:
`norm_Omega` at `ReflectionStrong.wilsonGibbsReflForm_vac_norm`.

DERIVED: `1` is the norm asserted, which is the total mass of a probability measure through
`Transfer.reflForm_one_one`; `2` in `n = 2 * m` is the two mirror planes of an even extent, `0` in
`0 < m` is nonemptiness of the slab, and `0` in `N ≠ 0` is nontriviality of the gauge group. -/
theorem ymOmega_norm (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m)
    (hm0 : 0 < m) (β : ℝ) : ‖ymOmega hN τ a m hm hm0 β‖ = 1 :=
  norm_Omega _ (wilsonGibbsReflForm_vac_norm hN τ a m hm hm0 β)

/-- `ymOmega hN τ a m hm hm0 β ≠ 0`, from `Omega_ne_zero` at the same normalisation theorem.

DERIVED: the `2` in `n = 2 * m` is the two mirror planes of an even extent and the `0` in
`0 < m` is nonemptiness of the slab; both are the reflection geometry's, neither is chosen. -/
theorem ymOmega_ne_zero (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m)
    (hm0 : 0 < m) (β : ℝ) : ymOmega hN τ a m hm hm0 β ≠ 0 :=
  Omega_ne_zero _ (wilsonGibbsReflForm_vac_norm hN τ a m hm hm0 β)

/-- `Nontrivial (ymH hN τ a m hm hm0 β)`, from `nontrivial_H` at the same normalisation theorem.

Scope: nonzero, not of dimension above one; no statement about the dimension is made here.

DERIVED: the `2` in `n = 2 * m` is the two mirror planes of an even extent and the `0` in
`0 < m` is nonemptiness of the slab; both are the reflection geometry's, neither is chosen. -/
theorem nontrivial_ymH (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m)
    (hm0 : 0 < m) (β : ℝ) : Nontrivial (ymH hN τ a m hm hm0 β) :=
  nontrivial_H _ (wilsonGibbsReflForm_vac_norm hN τ a m hm hm0 β)

/-- `CompleteSpace (ymH hN τ a m hm hm0 β)`, from `complete_H`.

DERIVED: the `2` in `n = 2 * m` is the two mirror planes of an even extent and the `0` in
`0 < m` is nonemptiness of the slab; both are the reflection geometry's, neither is chosen. -/
theorem complete_ymH (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m)
    (hm0 : 0 < m) (β : ℝ) : CompleteSpace (ymH hN τ a m hm hm0 β) :=
  complete_H _

end Wilson

/-! ## Part 6 — the slab shift, descended

`OSPositivity.wilsonSlabTransfer` is the only `Transfer.TransferData` on the Wilson slab algebra in
this tree; its `T` is `WilsonTransfer.shiftObs` restricted to the slab on the premise
`OSPositivity.SlabShiftStable`. `HalfLineTransfer.shiftObs_eq_self_of_shift_stable` says the shift
acts as the identity on every shift-stable submodule of the slab algebra once `n = 2 * m` with
`2 ≤ m`, and under the premise the slab algebra is such a submodule of itself. The two results below
carry that to the operator on the completion.
-/

section ShiftIsEmpty

variable {d n N m : ℕ} [NeZero n]

/-- Under `SlabShiftStable N τ a m`, at `n = 2 * m` with `2 ≤ m`, `shiftSlab τ a m hstab F = F` for
every `F` in the slab algebra. `HalfLineTransfer.shiftObs_eq_self_of_shift_stable` at
`M = localObs (blkS τ a m) (blkR τ a m)`, which is a shift-stable submodule of itself under the
premise.

DERIVED: `2 ≤ m` is `HalfLineTransfer`'s own sharp threshold — `blkR_shift_stable_of_extent_two`
shows it fails at `n = 2` — not a chosen bound. The `2` in `n = 2 * m` is the two mirror planes of
an even extent. -/
theorem shiftSlab_eq_id (τ : Fin d) (a : Fin n) (hm : n = 2 * m) (hm2 : 2 ≤ m)
    (hstab : SlabShiftStable N τ a m)
    (F : ↥(localObs (Ω := MassGap.SUN.SU N) (blkS τ a m) (blkR τ a m))) :
    shiftSlab τ a m hstab F = F := by
  refine Subtype.ext ?_
  show MassGap.WilsonTransfer.shiftObs τ F.1 = F.1
  exact MassGap.HalfLineTransfer.shiftObs_eq_self_of_shift_stable τ a m hm hm2
    (M := localObs (Ω := MassGap.SUN.SU N) (blkS τ a m) (blkR τ a m))
    (fun G hG => hG) (fun G hG => hstab G hG) F.2

/-- `opT (wilsonSlabTransfer hN τ a m hm hm0 β hstab hcon) x = x` at every `x`, under
`SlabShiftStable` and `SlabShiftContractive`, at `n = 2 * m` with `2 ≤ m`. `opT_eq_id_of_T_eq_id`
applied to `shiftSlab_eq_id`.

Scope: `OSPositivity.wilsonSlabTransfer` is the only `TransferData` on the Wilson slab algebra in
this tree and its `T` is the slab shift, so on its own stability premise the descended operator is
the identity. `HalfLineTransfer.shiftObs_pow_period` — the shift has order `n`, hence is an isometry
on every quotient — is a separate statement of the same kind, and
`PeriodicRayleigh.const_of_slabShiftStable` is its module-level form.

DERIVED: `2 ≤ m` and the `2` in `n = 2 * m` are `shiftSlab_eq_id`'s; the `0` in `0 < m` is
nonemptiness of the slab. -/
theorem shift_descends_to_id (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (hm : n = 2 * m) (hm2 : 2 ≤ m)
    (hm0 : 0 < m) (β : ℝ)
    (hstab : SlabShiftStable N τ a m) (hcon : SlabShiftContractive N τ a m β)
    (x : H (wilsonSlabTransfer hN τ a m hm hm0 β hstab hcon).toReflForm) :
    opT (wilsonSlabTransfer hN τ a m hm hm0 β hstab hcon) x = x :=
  opT_eq_id_of_T_eq_id _ (fun F => shiftSlab_eq_id τ a hm hm2 hstab F) x

end ShiftIsEmpty

/-! ## Part 7 — the same clauses at `T = LinearMap.id`

The shape

    a complex Hilbert space `H`, a unit vector `Ω`, and a positive self-adjoint contraction `T` on
    `H` with `T Ω = Ω`

is satisfied by `T = 1`. `trivialTransfer` is a `Transfer.TransferData` on the Wilson slab algebra
with that `T`, needing no premise — not `SlabShiftStable`, not `SlabShiftContractive`, and no
reflection positivity beyond what `wilsonGibbsReflForm` proves.
`ym_target_discharged_trivially` collects the five clauses together with a sixth stating that the
operator is the identity map.
-/

section TrivialWitness

variable {d n N : ℕ} [NeZero n]

/-- A `Transfer.TransferData` on the Wilson slab algebra with `T := LinearMap.id`, needing no
premise. Every field but `toReflForm` is `rfl` or `le_refl`; `toReflForm` is
`ReflectionStrong.wilsonGibbsReflForm` and `vac_norm` its normalisation theorem. By contrast
`OSPositivity.wilsonSlabTransfer` requires `SlabShiftStable` and `SlabShiftContractive` to put the
shift in that field.

DERIVED: `1` is the constant observable serving as `vac`; `2` in `n = 2 * m` is the two mirror
planes of an even extent, `0` in `0 < m` is nonemptiness of the slab, and `0` in `N ≠ 0` is
nontriviality of the gauge group. -/
noncomputable def trivialTransfer (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ) :
    Transfer.TransferData
      ↥(localObs (Ω := MassGap.SUN.SU N) (blkS τ a m) (blkR τ a m)) where
  toReflForm := wilsonGibbsReflForm hN τ a m hm hm0 β
  T := LinearMap.id
  vac := ⟨fun _ => (1 : ℝ), one_mem_localObs⟩
  T_symm _ _ := rfl
  T_contract _ := le_refl _
  T_vac := rfl
  vac_norm := wilsonGibbsReflForm_vac_norm hN τ a m hm hm0 β

/-- `PositiveTransfer (trivialTransfer hN τ a m hm hm0 β)`, directly from that structure's
`form_nonneg`. So `PositiveTransfer` has a true instance on a Wilson carrier.

DERIVED: `2` in `n = 2 * m` is the two mirror planes of an even extent, `0` in `0 < m` is
nonemptiness of the slab, and `0` in `N ≠ 0` is nontriviality of the gauge group. The `0` of the
positivity is inside `PositiveTransfer`. -/
theorem positiveTransfer_trivial (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ) :
    PositiveTransfer (trivialTransfer hN τ a m hm hm0 β) :=
  fun x => (trivialTransfer hN τ a m hm hm0 β).form_nonneg x

/-- Six conjuncts about `trivialTransfer`, with no premise beyond the lattice geometry: the vacuum
has norm `1`, `opT` is self-adjoint, `‖opT‖ ≤ 1`, `opT` fixes the vacuum,
`0 ≤ re (inner x (opT x))` at every `x`, and `opT x = x` at every `x`.

Scope: the first five are the shape "unit vacuum, self-adjoint positive contraction fixing the
vacuum", and the sixth identifies the operator as the identity, so that shape alone does not pin
`T` to a time translation.

DERIVED: `1` is the vacuum's norm (from `vac_norm`) and the contraction bound (from `norm_cT_le`);
`0` is the lower bound in the positivity clause, the `0 < m` nonemptiness of the slab, and the
`N ≠ 0` nontriviality of the gauge group; `2` in `n = 2 * m` is the two mirror planes of an even
extent. -/
theorem ym_target_discharged_trivially (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ) :
    ‖Omega (trivialTransfer hN τ a m hm hm0 β).toReflForm
        (trivialTransfer hN τ a m hm hm0 β).vac‖ = 1
      ∧ IsSelfAdjoint (opT (trivialTransfer hN τ a m hm hm0 β))
      ∧ ‖opT (trivialTransfer hN τ a m hm hm0 β)‖ ≤ 1
      ∧ opT (trivialTransfer hN τ a m hm hm0 β)
          (Omega (trivialTransfer hN τ a m hm hm0 β).toReflForm
            (trivialTransfer hN τ a m hm hm0 β).vac)
        = Omega (trivialTransfer hN τ a m hm hm0 β).toReflForm
            (trivialTransfer hN τ a m hm hm0 β).vac
      ∧ (∀ x, 0 ≤ RCLike.re (inner ℂ x (opT (trivialTransfer hN τ a m hm hm0 β) x)))
      ∧ (∀ x, opT (trivialTransfer hN τ a m hm hm0 β) x = x) :=
  ⟨norm_Omega_vac _, isSelfAdjoint_opT _, norm_opT_le_one _, opT_Omega _,
    re_inner_opT_nonneg _ (positiveTransfer_trivial hN τ a m hm hm0 β),
    opT_eq_id_of_T_eq_id _ (fun _ => rfl)⟩

end TrivialWitness

/-! ## Part 8 — the inner product as a Gibbs expectation

`OSPositivity.cform_eq_osPairing` identifies `cform` at `wilsonGibbsReflForm` with one Gibbs
expectation of `conj (F ∘ Θ) * G`. Composing with `inner_coe` says the same of the inner product of
`ymH`.
-/

section Identification

variable {d n N : ℕ} [NeZero n]

/-- The inner product of two local observables in `ymH`, written as one Gibbs expectation of the
complex OS integrand at the site reflection `reflConf τ (a + a)`, at every real `β`:
`inner_coe` composed with `OSPositivity.cform_eq_osPairing`. The result is the real part plus
`Complex.I` times the imaginary part of `ReflectPositive.EW N β` applied to
`conj (F ∘ Θ) * G`.

DERIVED: `Complex.I` is the imaginary unit, not a magnitude; `2` in `n = 2 * m` is the two mirror
planes of an even extent, `0` in `0 < m` is nonemptiness of the slab, and `0` in `N ≠ 0` is
nontriviality of the gauge group. The reflection constant `a + a` is `wilsonGibbsReflForm`'s
own. -/
theorem ym_inner_eq_osPairing (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ)
    {F G : (Link d n → MassGap.SUN.SU N) → ℂ}
    (hF : F ∈ localObsC (blkS τ a m) (blkR τ a m))
    (hG : G ∈ localObsC (blkS τ a m) (blkR τ a m)) :
    inner ℂ
        ((Pre.ofPair (wilsonGibbsReflForm hN τ a m hm hm0 β)
            ⟨reObs F, hF.1⟩ ⟨imObs F, hF.2⟩ : Pre _) : ymH hN τ a m hm hm0 β)
        ((Pre.ofPair (wilsonGibbsReflForm hN τ a m hm hm0 β)
            ⟨reObs G, hG.1⟩ ⟨imObs G, hG.2⟩ : Pre _) : ymH hN τ a m hm hm0 β)
      = ((MassGap.ReflectPositive.EW N β
            (fun U => ((starRingEnd ℂ) (F (MassGap.Reflect.reflConf τ (a + a) U)) * G U).re) : ℝ) : ℂ)
        + ((MassGap.ReflectPositive.EW N β
            (fun U => ((starRingEnd ℂ) (F (MassGap.Reflect.reflConf τ (a + a) U)) * G U).im) : ℝ) : ℂ)
          * Complex.I := by
  rw [inner_coe]
  exact cform_eq_osPairing hN τ a m hm hm0 β hF hG

end Identification

section Audit
#print axioms Pre
#print axioms Pre.instModule
#print axioms Pre.core
#print axioms Pre.instInnerProductSpace
#print axioms Pre.norm_mul_norm
#print axioms H
#print axioms complete_H
#print axioms inner_coe
#print axioms Omega
#print axioms norm_Omega
#print axioms Omega_ne_zero
#print axioms nontrivial_H
#print axioms cT
#print axioms norm_cT_le
#print axioms cTL
#print axioms opT
#print axioms norm_opT_le_one
#print axioms cform_cT
#print axioms isSelfAdjoint_opT
#print axioms opT_Omega
#print axioms opT_eq_id_of_T_eq_id
#print axioms norm_Omega_vac
#print axioms nontrivial_H_of_transferData
#print axioms PositiveTransfer
#print axioms re_inner_opT_nonneg
#print axioms positiveTransfer_of_T_eq_id
#print axioms ymH
#print axioms ymOmega
#print axioms ymOmega_norm
#print axioms ymOmega_ne_zero
#print axioms nontrivial_ymH
#print axioms complete_ymH
#print axioms shiftSlab_eq_id
#print axioms shift_descends_to_id
#print axioms trivialTransfer
#print axioms positiveTransfer_trivial
#print axioms ym_target_discharged_trivially
#print axioms ym_inner_eq_osPairing
end Audit

end MassGap.GNSHilbert
