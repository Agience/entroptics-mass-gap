import Mathlib
import MassGap.OSPositivity
import MassGap.HalfLineTransfer

/-!
# MassGap.GNSHilbert — a complete complex Hilbert space, and a unit vacuum vector, from the Wilson
Gibbs reflection form

**WHAT THIS FILE ADDS.** `Transfer.GNS` turns a `Transfer.ReflForm` into an `InnerProductSpace ℝ`,
and `ReflectionStrong.wilsonGibbsReflForm` is such a form on the genuine Wilson Gibbs measure. Two
things were missing from that and are supplied here.

*Completeness.* `Transfer.GNS P` carries no `CompleteSpace` instance and no proof of one; a
`NormedAddCommGroup` with an inner product is a PRE-Hilbert space, not a Hilbert space. The tree does
build ONE complete space already — `MomentMeasure.H`, the completion of `ℂ[X]` under a moment form —
but `MomentMeasure.MomentData` has no instance anywhere in the tree, so nothing connects it to the
Wilson measure. `WightmanData.WightmanQFTData` takes `CompleteSpace` as a FIELD a caller supplies.
This file is the first complete space built from the Wilson Gibbs measure.

*Complex scalars.* `wilsonGibbsReflForm` is real and bilinear; a quantum mechanical Hilbert space is
complex. `OSPositivity.cform` is the sesquilinear complexification of an arbitrary `PreForm`, with
conjugate symmetry, sesquilinearity and a nonnegative diagonal already proved, and
`OSPositivity.cform_eq_osPairing` identifies it with the genuine complex Gibbs pairing
`⟨conj(F ∘ Θ) · G⟩` rather than with an analogue of it. What `OSPositivity` deliberately did NOT do is
place a `Module ℂ` instance on the pair type, so `cform` could not be handed to Mathlib as an inner
product. This file places that instance and hands it over.

## The route, and why it is this one

`MomentMeasure` established the pattern in this tree: `PreInnerProductSpace.Core` asks only for
SEMIdefiniteness, and `UniformSpace.Completion` Hausdorffifies and completes in one step, so the null
space is quotiented for free. No quotient is taken here and `Transfer.GNS`'s quotient is not used:
`Pre P` is the pair module itself, `H P` is its completion, and Mathlib supplies
`NormedAddCommGroup`, `InnerProductSpace ℂ` and `CompleteSpace` on the completion.

## What is delivered

1. **The space.** `H P` for any `Transfer.ReflForm P`, and `ymH` at the Wilson instance. It is
   COMPLEX, with `cform` as the inner product. `complete_H` records completeness.
2. **The vacuum.** `Omega P v` is the class of `v` in the real part and `0` in the imaginary part.
   `norm_Omega` proves `‖Ω‖ = 1` from `P.form v v = 1` — and `ReflectionStrong`'s
   `wilsonGibbsReflForm_vac_norm` supplies exactly that for the constant observable, at every real
   `β`, with no premise about the dynamics. So `ymOmega_norm` needs only `N ≠ 0` and the lattice
   geometry `n = 2m`, `0 < m` — no coupling condition, no stability, no contractivity —
   `ymOmega_ne_zero` follows, and
   `nontrivial_ymH` says the Yang–Mills slab Hilbert space is not the zero space. **The
   anti-vacuity statement is `nontrivial_ymH`, and it is proved, not assumed.**
3. **The operator, abstractly.** Any `Transfer.TransferData A` descends to `opT`, a self-adjoint
   contraction on `H` fixing `Ω`. Everything about `opT` closes with no hypothesis beyond
   `TransferData`'s own fields.
4. **The operator, at Yang–Mills: IT DOES NOT CLOSE, AND THIS FILE SAYS WHY RATHER THAN HIDING IT.**
   The only `TransferData` on the Wilson slab algebra in the tree is `OSPositivity.wilsonSlabTransfer`,
   whose `T` is the lattice shift and which takes `OSPositivity.SlabShiftStable` as a premise.
   `shift_descends_to_id` proves that ON THAT PREMISE, at `n = 2m` with `2 ≤ m`, `opT` is the IDENTITY
   operator on `H` — because `HalfLineTransfer.shiftObs_eq_self_of_shift_stable` forces the shift to
   act as the identity on any shift-stable submodule of the slab algebra. So the premise does not buy
   a time evolution; it buys `T = 1`. If instead the premise is FALSE, the theorem is vacuous and
   there is no descended operator at all — either horn leaves the Wilson time translation absent from
   `H`, which is the point.

   `PeriodicRayleigh.const_of_slabShiftStable` is the same obstruction one level down, on the
   observable module: under `SlabShiftStable` every observable of the slab algebra is constant. What
   is added here is the consequence for the completed Hilbert space, which did not exist to state it
   on.

   This is stated because the target "a positive self-adjoint contraction `T` with `T Ω = Ω`" is
   SATISFIED BY `T = 1` on any Hilbert space whatever. A theorem of that shape is worth nothing
   unless `T` is pinned to the Wilson time translation, and `shift_descends_to_id` is the proof that
   pinning it to the shift, on this periodic lattice, yields the identity. `HalfLineTransfer`'s
   `shiftObs_pow_period` is the independent half of the same obstruction.

## The reduction — what is missing, named and proved to suffice

`PositiveTransfer D` (`∀ x, 0 ≤ ⟨x, T x⟩` before the completion) is the ONE hypothesis separating the
descended contraction from a positive operator, and `re_inner_opT_nonneg` proves it suffices on the
whole completion. In general it is a real, refutable condition — it does not follow from
contractivity, which bounds `|λ|` and says nothing about the sign of `λ`, and a negative eigenvalue is
what an oscillating correlator looks like. It is reflection positivity about a HALF-INTEGER time
plane, exactly as `Transfer`'s header says.

**On a carrier where the translation is trivial it is a theorem for a cheap reason.**
`positiveTransfer_of_T_eq_id` proves it outright whenever `T = 1`, from `form_nonneg`; Part 6 shows
the slab `TransferData` has `T = 1` on its own premise, and Part 7 exhibits an unconditional one that
does.

**⛔ THAT IS NO LONGER THE WHOLE STORY, BECAUSE A CARRIER ON WHICH `T` IS NOT THE IDENTITY NOW
EXISTS.** `ReflectionHalfSpace.transferData_of_state_facts_T_ne_id` proves it: for every positive
`k`, `HalfSpaceAlgebra.shift_no_finite_order_on_halfSpaceAlg` exhibits a member of `halfSpaceAlg`
that `k` shifts move, and at `k = 1` that carries through `TransferAssembly.restrictT` to the
assembled `T`. So `positiveTransfer_of_T_eq_id` does not reach
`WilsonTransferReduction.transferData_of_state_facts`, and `PositiveTransfer` there is a real
condition rather than a formality.

**⛔ THE ALGEBRA IS WHAT EXISTS; THE `TransferData` IS NOT AN OBJECT THE TREE HAS.**
`transferData_of_state_facts` is a `def` parameterised by three unproved facts about a state, and
`WilsonState` says twice that nothing is shown to satisfy any of them. What follows is about that
`def` applied to hypotheses, not about an object in hand.

**⛔ AND MOTION IN THE ALGEBRA IS NOT MOTION IN THE GNS QUOTIENT.** `opT [F] = [F]` whenever
`T F - F` lies in the null space of the form, and nothing shows otherwise for this carrier. Part 6's
trap is stated at `opT`, not at `T`, and `shift_no_finite_order_on_halfSpaceAlg` carries the same
caveat. `T ≠ 1` does not give `TransferMovesSomething`.

**⛔ AND IT NEEDS A SEPARATING FUNCTION ON THE GROUP**, which is a real hypothesis: `SU 0` and `SU 1`
are singletons and none exists. `CrossingIntegration.trace_gNeg` supplies one at `SU(3)`. Nothing in
the tree composes that with `halfSpaceAlg_has_nonconstant`, which separates CONFIGURATIONS rather
than group elements and does not discharge this.

**AND `PositiveTransfer` IS DISCHARGED THERE, BY A DIFFERENT ROUTE.**
`WilsonTransferReduction.positiveTransfer_iff_odd_reflPositive` makes it EQUIVALENT to reflection
positivity at the ODD constant `2p - 1` on the same algebra — the link reflection, whose mirror cuts
`τ`-links in half — and `ReflectionHalfSpace.wilson_positiveTransfer_of_common_subsequential_limit`
supplies that side, from `N ≠ 0`, `0 ≤ β`, two filters refining `atTop`, and the two cube families
converging along them to ONE state, at the all-identity boundary condition. That is SUFFICIENT and
is not known to be necessary: the only equivalence in the chain is with odd reflection positivity,
so another route to that would discharge `PositiveTransfer` without any limit. **`0 ≤ β` is not
bookkeeping**: `CharacterExpansion.NegControl.su3_kernel_nonneg_iff` shows the Wilson cross kernel is
not positive-semidefinite below zero. **And `N ≠ 0` does not exclude `N = 1`**, where `SU 1` is a
singleton, `halfSpaceAlg` is the constants and the whole statement is empty.

A HAMILTONIAN IS NOT CONSTRUCTED. `-log T` is not built and no nonnegative-spectrum generator is
claimed. Positivity and injectivity of `T` are both insufficient: what `Reconstruction.hamiltonian`
(which does use Mathlib's `cfc`) needs to return anything but junk is `-Real.log` continuous on
`spectrum ℝ T`, i.e. `0 ∉ spectrum T`, and a contraction on an infinite-dimensional space generically
has `0` in its spectrum while remaining injective — multiplication by `x` on `L²[0,1]` is the
standard example. Then `-log T` is unbounded and is not an element of the algebra at all.

## What this file does NOT claim

No infinite volume, no continuum, no half-space: `wilsonGibbsReflForm` lives on a SLAB of a periodic
lattice at fixed spacing, and `OSPositivity`'s list of separations from OS3 stands unchanged.
`nontrivial_ymH` says the space is nonzero; it does NOT say it has dimension above one, and no such
statement is made. Nothing in the tree exhibits a NON-CONSTANT slab observable, so nothing here can
rule out `H` being one-dimensional. That matters for Part 6: at `N = 1` the gauge group is trivial
(`SimpleGroup.subsingleton_SU_one`), every observable is constant, `SlabShiftStable` and
`SlabShiftContractive` both hold, and Part 6's theorems have a model — so they are not vacuously
true, and they are also not about anything. At `N ≥ 2` the tree decides neither premise.

`PeriodicRayleigh.const_of_slabShiftStable` and `Spectral2`'s header already record the module-level
form of Part 6's obstruction. What is new here is only that it now has a Hilbert space to be stated
on.

No incomplete proofs. Foundational footprint only (`#print axioms` at the end).
Build: `python research/code/lean_build.py build MassGap.GNSHilbert`.
-/

namespace MassGap.GNSHilbert

open MassGap MassGap.Transfer MassGap.OSPositivity
open MassGap.LogConvex MassGap.WilsonHypercubic MassGap.ReflectionStrong
open MassGap.ActionSplit

/-! ## Part 1 — the pair module as a complex vector space

`OSPositivity.cscal` is the complex scalar action on a pair of real vectors, written there WITHOUT a
`Module ℂ` instance so that nothing downstream could pick it up silently. Here it becomes one, on a
type synonym carrying the form, so that the seminorm below is attached to a type that remembers which
form produced it. That is `MomentMeasure.Pre`'s device and it is used for the same reason.
-/

section Abstract

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

set_option linter.unusedVariables false in
/-- **The complexification of the observable module**, as a type that remembers the form.

DERIVED: no numeral. -/
def Pre (P : Transfer.ReflForm A) : Type _ := A × A

namespace Pre

variable {P : Transfer.ReflForm A}

instance instAddCommGroup (P : Transfer.ReflForm A) : AddCommGroup (Pre P) :=
  inferInstanceAs (AddCommGroup (A × A))

/-- The complex scalar action, which is `OSPositivity.cscal` and nothing else. -/
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

/-- **A PAIR OF REAL OBSERVABLES, READ AS ONE COMPLEX VECTOR.** `x` is the real part and `y` the
imaginary part.

DERIVED: no numeral. -/
def ofPair (P : Transfer.ReflForm A) (x y : A) : Pre P := (x, y)

@[simp] theorem ofPair_fst (x y : A) : ((ofPair P x y : Pre P) : A × A).1 = x := rfl

@[simp] theorem ofPair_snd (x y : A) : ((ofPair P x y : Pre P) : A × A).2 = y := rfl

/-- Componentwise extensionality, proved through `Prod.mk.eta` so it does not depend on the spelling
of `Prod`'s extensionality lemma. -/
theorem ext {z w : Pre P} (h1 : (z : A × A).1 = (w : A × A).1)
    (h2 : (z : A × A).2 = (w : A × A).2) : z = w := by
  have h3 : @Eq (A × A) z w := by
    have e : (((z : A × A).1, (z : A × A).2) : A × A) = ((w : A × A).1, (w : A × A).2) := by
      rw [h1, h2]
    simpa using e
  exact h3

/-- **THE PAIR MODULE IS A COMPLEX VECTOR SPACE.** Six identities, each a real-linear-combination
identity whose coefficients agree by `ring` once `Complex.mul_re` and `Complex.mul_im` are unfolded.

DERIVED: no numeral; the `1` in `one_smul` is the complex unit. -/
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

/-- **THE COMPLEX SEMI-INNER PRODUCT.** Conjugate-symmetric by `cform_conj_symm`, semidefinite by
`cform_diag_re_nonneg` — which is `P.form_nonneg` on each component and nothing else — and
sesquilinear by `cform_add_left` / `cform_smul_left`. Definiteness is NOT claimed and is not needed:
the completion quotients the null vectors out.

DERIVED: no numeral. -/
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

/-- **THE SEMINORM SQUARED IS THE FORM ON THE TWO COMPONENTS.**

DERIVED: no numeral. -/
theorem norm_mul_norm (z : Pre P) :
    ‖z‖ * ‖z‖ = P.form (z : A × A).1 (z : A × A).1 + P.form (z : A × A).2 (z : A × A).2 := by
  have h : ‖z‖ ^ 2 = RCLike.re (inner ℂ z z) := InnerProductSpace.norm_sq_eq_re_inner _
  rw [pow_two] at h
  rw [h, inner_def]
  simp

end Pre

/-! ## Part 2 — the Hilbert space

`UniformSpace.Completion` of a seminormed inner product space is a complete complex inner product
space: Mathlib supplies the `NormedAddCommGroup`, the `InnerProductSpace ℂ` and the `CompleteSpace`.
The Hausdorffification is what takes the place of `Transfer.GNS`'s quotient by the null space.
-/

/-- **THE HILBERT SPACE.** Complex, complete, and built from the form rather than postulated.

DERIVED: no numeral. -/
abbrev H (P : Transfer.ReflForm A) : Type _ := UniformSpace.Completion (Pre P)

/-- Completeness, recorded as a theorem so that it is visible in the audit rather than only in an
instance cache. -/
theorem complete_H (P : Transfer.ReflForm A) : CompleteSpace (H P) := inferInstance

/-- The inner product of two observable classes is the complex Gibbs pairing. -/
@[simp] theorem inner_coe (P : Transfer.ReflForm A) (z w : Pre P) :
    inner ℂ ((z : H P)) ((w : H P)) = cform P.toPreForm (z : A × A) (w : A × A) := by
  rw [UniformSpace.Completion.inner_coe]
  rfl

/-! ## Part 3 — the vacuum

`Omega P v` is `v` in the real component and `0` in the imaginary one. Its norm is `1` exactly when
the form normalises `v`, which is a hypothesis here and a THEOREM at Yang–Mills
(`ReflectionStrong.wilsonGibbsReflForm_vac_norm`, at every real `β`, with no premise).
-/

/-- **THE VACUUM VECTOR.**

DERIVED: the `0` is the imaginary component of a real observable, not a chosen value. -/
noncomputable def Omega (P : Transfer.ReflForm A) (v : A) : H P :=
  ((Pre.ofPair P v (0 : A) : Pre P) : H P)

/-- **THE VACUUM IS A UNIT VECTOR**, from `P.form v v = 1` and nothing else.

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

/-- **THE VACUUM IS NOT THE ZERO VECTOR.** This is the anti-vacuity statement: a Hilbert space whose
distinguished vector is `0` would satisfy a badly stated theorem and be worth nothing.

DERIVED: the `1` is `norm_Omega`'s; `0` is the zero vector. -/
theorem Omega_ne_zero (P : Transfer.ReflForm A) {v : A} (hv : P.form v v = 1) :
    Omega P v ≠ (0 : H P) := by
  intro h
  have h1 := norm_Omega P hv
  rw [h, norm_zero] at h1
  exact absurd h1 (by norm_num)

/-- **SO THE HILBERT SPACE IS NOT THE ZERO SPACE.**

DERIVED: the `1` in `P.form v v = 1` is `norm_Omega`'s hypothesis, the normalisation of the state. -/
theorem nontrivial_H (P : Transfer.ReflForm A) {v : A} (hv : P.form v v = 1) :
    Nontrivial (H P) :=
  ⟨⟨Omega P v, 0, Omega_ne_zero P hv⟩⟩

/-! ## Part 4 — the transfer operator, abstractly

Every statement in this part closes from `Transfer.TransferData`'s own fields, with no further
hypothesis. Part 6 is where the Yang–Mills instance is examined, and where it fails.
-/

section Operator

variable (D : Transfer.TransferData A)

/-- **THE TIME TRANSLATION, COMPLEXIFIED.** Componentwise; complex linearity is real linearity of
`D.T` on each component.

DERIVED: no numeral. -/
noncomputable def cT : Pre D.toReflForm →ₗ[ℂ] Pre D.toReflForm where
  toFun z := Pre.ofPair D.toReflForm (D.T (z : A × A).1) (D.T (z : A × A).2)
  map_add' z w := by refine Pre.ext ?_ ?_ <;> simp [map_add]
  map_smul' c z := by refine Pre.ext ?_ ?_ <;> simp [map_add, map_smul]

@[simp] theorem cT_fst (z : Pre D.toReflForm) :
    ((cT D z : Pre D.toReflForm) : A × A).1 = D.T (z : A × A).1 := rfl

@[simp] theorem cT_snd (z : Pre D.toReflForm) :
    ((cT D z : Pre D.toReflForm) : A × A).2 = D.T (z : A × A).2 := rfl

/-- **THE COMPLEXIFIED TRANSLATION IS A CONTRACTION.** `D.T_contract` on each component.

DERIVED: the `1` is the contraction constant `T_contract` gives, not a chosen bound. -/
theorem norm_cT_le (z : Pre D.toReflForm) : ‖cT D z‖ ≤ 1 * ‖z‖ := by
  rw [one_mul]
  have h : ‖cT D z‖ * ‖cT D z‖ ≤ ‖z‖ * ‖z‖ := by
    rw [Pre.norm_mul_norm, Pre.norm_mul_norm, cT_fst, cT_snd]
    have h1 := D.T_contract (z : A × A).1
    have h2 := D.T_contract (z : A × A).2
    linarith
  nlinarith [norm_nonneg (cT D z), norm_nonneg z]

/-- The complexified translation as a bounded operator on the pre-Hilbert space.

DERIVED: the `1` is `norm_cT_le`'s constant. -/
noncomputable def cTL : Pre D.toReflForm →L[ℂ] Pre D.toReflForm :=
  LinearMap.mkContinuous (cT D) 1 (norm_cT_le D)

@[simp] theorem cTL_apply (z : Pre D.toReflForm) : cTL D z = cT D z := rfl

/-- **THE TRANSFER OPERATOR ON THE HILBERT SPACE.** The unique continuous extension of the
complexified time translation to the completion.

DERIVED: no numeral. -/
noncomputable def opT : H D.toReflForm →L[ℂ] H D.toReflForm := (cTL D).completion

@[simp] theorem opT_coe (z : Pre D.toReflForm) :
    opT D ((z : H D.toReflForm)) = ((cTL D z : Pre D.toReflForm) : H D.toReflForm) :=
  ContinuousLinearMap.completion_apply_coe _ _

/-- **`‖T‖ ≤ 1` — THE TRANSFER OPERATOR IS A CONTRACTION.** Normalisation, not gap: the Gibbs measure
is a probability measure.

DERIVED: the `1` is `norm_cT_le`'s contraction constant. -/
theorem norm_opT_le_one : ‖opT D‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_le (continuous_norm.comp (opT D).continuous)
        (continuous_const.mul continuous_norm)
  | ih z =>
      simpa [cTL, UniformSpace.Completion.norm_coe] using norm_cT_le D z

/-- **THE COMPLEXIFIED TRANSLATION IS SYMMETRIC FOR THE COMPLEX FORM**, from `D.T_symm` on the four
component pairings. This is where reflection positivity is doing its work: the reflection exchanges
the two half-lines, so translating one is translating the other. -/
theorem cform_cT (z w : Pre D.toReflForm) :
    cform D.toPreForm ((cT D z : Pre D.toReflForm) : A × A) (w : A × A)
      = cform D.toPreForm (z : A × A) ((cT D w : Pre D.toReflForm) : A × A) := by
  refine ceq ?_ ?_
  · simp only [cform_re, cT_fst, cT_snd]
    rw [D.T_symm (z : A × A).1 (w : A × A).1, D.T_symm (z : A × A).2 (w : A × A).2]
  · simp only [cform_im, cT_fst, cT_snd]
    rw [D.T_symm (z : A × A).1 (w : A × A).2, D.T_symm (z : A × A).2 (w : A × A).1]

/-- **THE TRANSFER OPERATOR IS SELF-ADJOINT.** -/
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

/-- **`T Ω = Ω` — THE VACUUM IS FIXED.** From `D.T_vac` and linearity at the imaginary component,
not from any gap.

DERIVED: the `0` is the imaginary component of the real constant observable, not a value. -/
theorem opT_Omega : opT D (Omega D.toReflForm D.vac) = Omega D.toReflForm D.vac := by
  rw [Omega, opT_coe]
  congr 1
  refine Pre.ext ?_ ?_
  · simpa using D.T_vac
  · simp

/-- **IF THE TRANSLATION IS THE IDENTITY BEFORE THE COMPLETION, IT IS THE IDENTITY AFTER IT.**
Density and continuity. Part 6 is what this is for. -/
theorem opT_eq_id_of_T_eq_id (hT : ∀ x : A, D.T x = x) (x : H D.toReflForm) : opT D x = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (opT D).continuous continuous_id
  | ih z =>
      rw [opT_coe]
      congr 1
      refine Pre.ext ?_ ?_
      · simpa using hT ((z : A × A).1)
      · simpa using hT ((z : A × A).2)

/-- **THE VACUUM IS A UNIT VECTOR AT YANG–MILLS-INDEPENDENT GENERALITY**, since `vac_norm` is a field
of `TransferData`.

DERIVED: the `1` is `TransferData.vac_norm`'s. -/
theorem norm_Omega_vac : ‖Omega D.toReflForm D.vac‖ = 1 :=
  norm_Omega D.toReflForm D.vac_norm

/-- **SO EVERY `TransferData` YIELDS A NONZERO HILBERT SPACE**, with no hypothesis at all. Stated
because `norm_opT_le_one`, `isSelfAdjoint_opT`, `opT_Omega` and `re_inner_opT_nonneg` would all hold
on the ZERO space — they are not anti-vacuous individually, and this is what makes them so.

DERIVED: no numeral of its own; the `1` it rests on is `vac_norm`'s. -/
theorem nontrivial_H_of_transferData : Nontrivial (H D.toReflForm) :=
  nontrivial_H D.toReflForm D.vac_norm

/-! ### The reduction: positivity of the transfer operator

`PositiveTransfer` is not a consequence of `TransferData`'s fields: contractivity bounds `|λ| ≤ 1` and
says nothing about the SIGN of `λ`, and a negative eigenvalue is what an oscillating correlator looks
like. It is reflection positivity about a HALF-INTEGER time plane — a second application of the same
physics. `re_inner_opT_nonneg` proves it suffices on the whole completion.

It is nevertheless a THEOREM whenever `T = 1` (`positiveTransfer_of_T_eq_id`), and every Wilson
`TransferData` the tree has is of that kind, so at Yang–Mills today this is not the open item. See the
module header.
-/

/-- **THE OPEN PROP.** Positivity of the transfer operator, stated before the completion.

DERIVED: the `0` of `0 ≤ …` is positivity itself. -/
def PositiveTransfer (D : Transfer.TransferData A) : Prop :=
  ∀ x : A, 0 ≤ D.form x (D.T x)

/-- **THE REDUCTION, PROVED TO SUFFICE.** `PositiveTransfer D` gives positivity of `opT` on the whole
Hilbert space, by density and continuity.

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

/-- **AND `PositiveTransfer` IS A THEOREM WHENEVER `T` IS THE IDENTITY** — it is then `form_nonneg`,
which is reflection positivity and already proved.

This is why the hypothesis is a real condition only for a NON-TRIVIAL translation. Part 6 shows the
slab `TransferData` has `T = 1` on its own premise, and Part 7 exhibits an unconditional one that
does; `PositiveTransfer` is discharged for both by this theorem.

**⛔ IT DOES NOT COVER THE HALF-SPACE CARRIER.** `ReflectionHalfSpace.transferData_of_state_facts_T_ne_id`
proves `T ≠ 1` there, at a separating function on the group, so this proof is unavailable.
`PositiveTransfer` is discharged there instead by
`ReflectionHalfSpace.wilson_positiveTransfer_of_common_subsequential_limit`, through the equivalence
`WilsonTransferReduction.positiveTransfer_iff_odd_reflPositive`.

DERIVED: the `0` of `0 ≤ …` is positivity itself. -/
theorem positiveTransfer_of_T_eq_id (hT : ∀ x : A, D.T x = x) : PositiveTransfer D := by
  intro x
  rw [hT x]
  exact D.form_nonneg x

#print axioms positiveTransfer_of_T_eq_id

/-- **⭐ AND FROM A SQUARE ROOT OF THE STEP, WHICH IS WHERE THE PHYSICS PUTS IT.** If the transfer
step factors through the form — `form x (T x) = form (S x) (S x)` for a LINEAR `S` — then
`PositiveTransfer` is immediate from `form_nonneg`, which is reflection positivity and is already
proved.

**This is what makes positivity structural rather than an extra assumption.** A transfer operator is
positive because it is a half-step composed with its adjoint; the obligation is then to exhibit the
half-step, not to assume an inequality. The tree names the same content on the `L²` slab carrier as
`SlabTransferAdjoint.SlabGramVia` — a `FiniteGram` condition on the kernel, whose sufficient half is
proved and which is reported OPEN there.

**⚠ Linearity of `S` is load-bearing.** With an arbitrary function the equation could be solved
pointwise wherever the form takes the required value, and the statement would restate positivity
rather than reduce it.

DERIVED: the `0` of `0 ≤ …` is positivity itself; no magnitude. -/
theorem positiveTransfer_of_gram (S : A →ₗ[ℝ] A)
    (hS : ∀ x : A, D.form x (D.T x) = D.form (S x) (S x)) : PositiveTransfer D := by
  intro x
  rw [hS x]
  exact D.form_nonneg (S x)

#print axioms positiveTransfer_of_gram

end Operator

end Abstract

/-! ## Part 5 — the Yang–Mills instance of the SPACE and the VACUUM

`ReflectionStrong.wilsonGibbsReflForm` is a `Transfer.ReflForm` on the genuine Wilson Gibbs measure at
EVERY REAL `β`, and `wilsonGibbsReflForm_vac_norm` normalises the constant observable. So the space
and the vacuum close at Yang–Mills with no premise at all.
-/

section Wilson

variable {d n N : ℕ} [NeZero n]

/-- **THE YANG–MILLS SLAB HILBERT SPACE.** A complete complex inner product space whose inner product
is the complex Gibbs reflection pairing of the genuine Wilson measure.

DERIVED: the `2` in `n = 2 * m` is the two mirror planes of an even extent and the `0` in
`0 < m` is nonemptiness of the slab; both are the reflection geometry's, neither is chosen. `τ`, `a`, `m` and `β` are the caller's. -/
noncomputable abbrev ymH (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m)
    (hm0 : 0 < m) (β : ℝ) :=
  H (wilsonGibbsReflForm hN τ a m hm hm0 β)

/-- **THE YANG–MILLS VACUUM**, the class of the constant observable `1`.

DERIVED: the `1` is the constant observable and the `0` beside it is its imaginary component. DERIVED: the `2` in `n = 2 * m` is the two mirror planes of an even extent and the `0` in
`0 < m` is nonemptiness of the slab; both are the reflection geometry's, neither is chosen. -/
noncomputable def ymOmega (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m)
    (hm0 : 0 < m) (β : ℝ) : ymH hN τ a m hm hm0 β :=
  Omega (wilsonGibbsReflForm hN τ a m hm hm0 β) ⟨fun _ => (1 : ℝ), one_mem_localObs⟩

/-- **THE YANG–MILLS VACUUM IS A UNIT VECTOR, AT EVERY REAL COUPLING, WITH NO PREMISE.**

DERIVED: the `1`s are the constant observable and the total mass of a probability measure, both
`Transfer.reflForm_one_one`'s through `wilsonGibbsReflForm_vac_norm`. DERIVED: the `2` in `n = 2 * m` is the two mirror planes of an even extent and the `0` in
`0 < m` is nonemptiness of the slab; both are the reflection geometry's, neither is chosen. -/
theorem ymOmega_norm (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m)
    (hm0 : 0 < m) (β : ℝ) : ‖ymOmega hN τ a m hm hm0 β‖ = 1 :=
  norm_Omega _ (wilsonGibbsReflForm_vac_norm hN τ a m hm hm0 β)

/-- **THE YANG–MILLS VACUUM IS NOT THE ZERO VECTOR.**

DERIVED: the `2` in `n = 2 * m` is the two mirror planes of an even extent and the `0` in
`0 < m` is nonemptiness of the slab; both are the reflection geometry's, neither is chosen. -/
theorem ymOmega_ne_zero (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m)
    (hm0 : 0 < m) (β : ℝ) : ymOmega hN τ a m hm hm0 β ≠ 0 :=
  Omega_ne_zero _ (wilsonGibbsReflForm_vac_norm hN τ a m hm hm0 β)

/-- **THE YANG–MILLS SLAB HILBERT SPACE IS NOT THE ZERO SPACE.** The anti-vacuity statement.

DERIVED: the `2` in `n = 2 * m` is the two mirror planes of an even extent and the `0` in
`0 < m` is nonemptiness of the slab; both are the reflection geometry's, neither is chosen. -/
theorem nontrivial_ymH (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m)
    (hm0 : 0 < m) (β : ℝ) : Nontrivial (ymH hN τ a m hm hm0 β) :=
  nontrivial_H _ (wilsonGibbsReflForm_vac_norm hN τ a m hm hm0 β)

/-- **COMPLETENESS AT YANG–MILLS.**

DERIVED: the `2` in `n = 2 * m` is the two mirror planes of an even extent and the `0` in
`0 < m` is nonemptiness of the slab; both are the reflection geometry's, neither is chosen. -/
theorem complete_ymH (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m)
    (hm0 : 0 < m) (β : ℝ) : CompleteSpace (ymH hN τ a m hm hm0 β) :=
  complete_H _

end Wilson

/-! ## Part 6 — the Yang–Mills instance of the OPERATOR, and why it is empty

The only `Transfer.TransferData` on the Wilson slab algebra in the tree is
`OSPositivity.wilsonSlabTransfer`, whose `T` is `WilsonTransfer.shiftObs` restricted to the slab on
the premise `OSPositivity.SlabShiftStable`. That premise does not buy a time evolution.
`HalfLineTransfer.shiftObs_eq_self_of_shift_stable` says every shift-stable submodule of the slab
algebra is acted on by the shift as the IDENTITY once `n = 2m` with `2 ≤ m`, and the slab algebra is
such a submodule of itself under the premise. So the descended operator is `1`.
-/

section ShiftIsEmpty

variable {d n N m : ℕ} [NeZero n]

/-- **ON ITS OWN STABILITY PREMISE THE SLAB SHIFT IS THE IDENTITY ON THE SLAB ALGEBRA.**

`HalfLineTransfer.shiftObs_eq_self_of_shift_stable` at `M = localObs (blkS τ a m) (blkR τ a m)`.

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

/-- **SO THE DESCENDED TRANSFER OPERATOR IS THE IDENTITY ON THE HILBERT SPACE.**

This is the finding, not a defect of the construction. The target "a positive self-adjoint
contraction `T` on `H` with `T Ω = Ω`" is satisfied by `T = 1` on ANY Hilbert space, so a theorem of
that shape says nothing unless `T` is pinned to the Wilson time translation. Pinned to the shift, on
a lattice periodic in `τ`, at the geometry `wilsonGibbsReflForm` lives at, it IS `1`.
`HalfLineTransfer.shiftObs_pow_period` — the shift has order `n`, so it is an isometry on every
quotient — is the independent second half of the same obstruction, and
`PeriodicRayleigh.const_of_slabShiftStable` states the module-level form of this one.

DERIVED: `2 ≤ m` and the `2` in `n = 2 * m` are `shiftSlab_eq_id`'s; the `0` in `0 < m` is
nonemptiness of the slab. -/
theorem shift_descends_to_id (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (hm : n = 2 * m) (hm2 : 2 ≤ m)
    (hm0 : 0 < m) (β : ℝ)
    (hstab : SlabShiftStable N τ a m) (hcon : SlabShiftContractive N τ a m β)
    (x : H (wilsonSlabTransfer hN τ a m hm hm0 β hstab hcon).toReflForm) :
    opT (wilsonSlabTransfer hN τ a m hm hm0 β hstab hcon) x = x :=
  opT_eq_id_of_T_eq_id _ (fun F => shiftSlab_eq_id τ a hm hm2 hstab F) x

end ShiftIsEmpty

/-! ## Part 7 — the target statement, discharged unconditionally and worthlessly, by `T = 1`

`WitnessVacuity` is this tree's idiom: a claim otherwise made in prose is machine-checked instead. The
claim here is that

    "a complex Hilbert space `H`, a unit vector `Ω`, and a positive self-adjoint contraction `T` on
     `H` with `T Ω = Ω`"

is NOT, by itself, a statement about Yang–Mills, because `T = 1` satisfies every clause of it.
`trivialTransfer` is the witness: a `Transfer.TransferData` on the genuine Wilson slab algebra
needing NO premise at all — not `SlabShiftStable`, not `SlabShiftContractive`, not reflection
positivity beyond what `wilsonGibbsReflForm` already proves — whose `T` is the identity.
`ym_target_discharged_trivially` then collects the five clauses AND the sixth fact that makes them
worthless: the operator is the identity map.

So none of the four properties is what is missing. What is missing is that `T` be the TIME
TRANSLATION, and Part 6 is what happens when it is required to be.
-/

section TrivialWitness

variable {d n N : ℕ} [NeZero n]

/-- **THE IDENTITY IS A `Transfer.TransferData` ON THE WILSON SLAB ALGEBRA, WITH NO PREMISE.**

Every field but `toReflForm` is `rfl` or `le_refl`; `toReflForm` is `ReflectionStrong`'s genuine Gibbs
reflection form and `vac_norm` is its normalisation theorem. Compare `OSPositivity.wilsonSlabTransfer`,
which needs two premises to put the SHIFT here.

DERIVED: the `1` is the constant observable. DERIVED: the `2` in `n = 2 * m` is the two mirror planes of an even extent and the `0` in
`0 < m` is nonemptiness of the slab; both are the reflection geometry's, neither is chosen. -/
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

/-- **THE OPEN HYPOTHESIS IS DISCHARGED FOR THE IDENTITY** — by `form_nonneg`, which is reflection
positivity and already proved. So `PositiveTransfer` is not trivially FALSE either; it is a genuine
open hypothesis with a true instance.

DERIVED: the `0` of `0 ≤ …` is positivity itself. DERIVED: the `2` in `n = 2 * m` is the two mirror planes of an even extent and the `0` in
`0 < m` is nonemptiness of the slab; both are the reflection geometry's, neither is chosen. -/
theorem positiveTransfer_trivial (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ) :
    PositiveTransfer (trivialTransfer hN τ a m hm hm0 β) :=
  fun x => (trivialTransfer hN τ a m hm hm0 β).form_nonneg x

/-- **EVERY CLAUSE OF THE TARGET, AT YANG–MILLS, WITH NO PREMISE — AND THE OPERATOR IS THE IDENTITY.**

The first five conjuncts are the target: a unit vacuum, a self-adjoint operator, a contraction, the
vacuum fixed, and positivity. The sixth says what the operator is. Read together they are the reason
the target cannot be the statement of the Clay clause on its own.

DERIVED: the `1`s are `vac_norm`'s and `norm_cT_le`'s contraction constant; the `0` of `0 ≤ …` is
positivity itself. DERIVED: the `2` in `n = 2 * m` is the two mirror planes of an even extent and the `0` in
`0 < m` is nonemptiness of the slab; both are the reflection geometry's, neither is chosen. -/
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

/-! ## Part 8 — the inner product IS the complex Gibbs pairing, not a model of it

`OSPositivity.cform_eq_osPairing` identifies `cform` on `wilsonGibbsReflForm` with one Gibbs
expectation of `conj(F ∘ Θ) · G`. Composing it with `inner_coe` says the same of the inner product of
the Hilbert space built here, so the space is the Wilson measure's and not an analogue of it.
-/

section Identification

variable {d n N : ℕ} [NeZero n]

/-- **THE INNER PRODUCT OF THE YANG–MILLS HILBERT SPACE IS ONE GIBBS EXPECTATION OF THE COMPLEX OS
INTEGRAND**, at the site reflection `Θ = reflConf τ (a + a)`, at every real `β`.

DERIVED: `Complex.I` is the imaginary unit, not a value. DERIVED: the `2` in `n = 2 * m` is the two mirror planes of an even extent and the `0` in
`0 < m` is nonemptiness of the slab; both are the reflection geometry's, neither is chosen. -/
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
