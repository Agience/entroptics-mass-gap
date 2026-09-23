import Mathlib
import MassGap.SlabKernelOperator

/-!
# MassGap.SlabTransferAdjoint — the adjoint of a kernel operator, and the quadratic form

`SlabKernelOperator` builds `slabTransfer`, a bounded map `L²(slab t+1) →L[ℝ] L²(slab t)` from the
kernel `slabKernel`. This module computes the adjoint of a kernel operator, gives a symmetry
criterion for self-adjointness, reduces operator positivity to a Gram condition, and evaluates the
quadratic form at a constant kernel.

## Part 1 — the adjoint is the transposed kernel

`adjoint_kernelCLM` : `(T_K)† = T_{Kᵀ}` with `Kᵀ y x = K x y`. One Fubini
(`integral_integral_swap`) against a dominating function built from `|f| ⊗ |g|`; both measures are
probability measures and `K` is bounded, so the integrand is dominated by `C · |g| ⊗ |f|`, which is
integrable because an `L²` function on a probability space is `L¹`.

`isSelfAdjoint_kernelCLM_of_symm` is the consequence for a symmetric kernel on one space.
`adjoint_slabTransfer` is the adjoint identity at the Wilson slab kernel. The self-adjointness
criterion is not instantiated there: `slabTransfer` is not an endomorphism at `n ≥ 2`, and no
statement in the tree decides whether `slabKernel` is symmetric.
`MassGap.SliceTransferSelfAdjoint` carries the criterion to `SliceTransfer.transferKernel`, which is
proved symmetric.

## Part 2 — `T† ∘ T`

`isSelfAdjoint_adjointComp` and `inner_adjointComp_self_nonneg` hold for every bounded operator
between any two real Hilbert spaces, with no hypothesis on `T` and none relating the two spaces.
`adjointComp_zero_eq_zero` and `isSelfAdjoint_adjointComp_zero` are the control: the zero operator
satisfies both, so a self-adjoint positive operator obtained this way carries no information about
`T`.

## Part 3 — operator positivity as a Gram condition

`FiniteGram K` is the finite square `K x y = ∑ᵢ Aᵢ x · Aᵢ y`.

* `FiniteGram.symm` — a Gram kernel is symmetric, so symmetry is necessary. `slabKernel` carries the
  whole intra-slice weight of slice `t` and none of slice `t+1`
  (`slabKernel_eq_intra_mul_inter` exhibits a factor not mentioning the second argument) and its
  temporal plaquette sum reads the axis links, which belong to slab `t` alone. Removing that
  asymmetry is temporal gauge, which is `SliceTransfer`'s hypothesis `hg` and is discharged nowhere.
* `inner_kernelCLM_self_eq_sum_sq_of_gram` — on a Gram kernel the quadratic form is `∑ᵢ (∫ Aᵢ f)²`,
  hence `inner_kernelCLM_self_nonneg_of_gram`. The Gram index is finite, so the interchange is
  `integral_finsetSum` and no Fubini is needed.

`SlabGramVia` states the same condition at the Wilson slab, through an explicit measurable
identification `e` of the two slab configuration spaces, since the tree has no canonical one.
`slabGramVia_symm` and `inner_slabPulled_self_nonneg_of_gram` are its necessary and sufficient
halves. No statement here or in the tree establishes `SlabGramVia`.

## Part 4 — a uniform lower bound on the kernel

`inner_kernelCLM_self_ge_of_nonneg` : with `c ≤ K` pointwise and `f ≥ 0` almost everywhere,
`c · (∫f)² ≤ ⟨f, T f⟩`. The hypothesis `f ≥ 0` is used in the pointwise step and is not removed
here.

`inner_kernelCLM_self_of_const` computes the form exactly at `K ≡ 1`: `⟨f, T f⟩ = (∫f)²`, which
vanishes on the whole mean-zero subspace although the pointwise lower bound there is `1`, the
largest a kernel bounded by `1` can have. `kernelCLM_apply_of_const` identifies the operator as the
rank-one averaging map `f ↦ (∫f) · 1`, and `zero_mem_spectrum_of_apply_eq_zero` turns any nonzero
mean-zero vector into `0 ∈ spectrum`.

So a uniform positive lower bound on the kernel does not by itself place `0` outside the spectrum.
The proved instance is at the constant `1`; no declaration covers other constants.

At the Wilson slab this is conditional. `slabCap_beta_zero` gives pointwise lower bound `1` at
`β = 0`, and `zero_mem_spectrum_slabNormal_of_beta_zero` places `0` in the spectrum of `slabNormal`
on the hypothesis that a nonzero mean-zero `L²` vector exists. That hypothesis fails when
`L²(slabHaar)` is at most one-dimensional, which `N = 1` or an empty slab would give; no statement
here says those are the only ways it fails, and no nonconstant slab observable is exhibited. The
abstract half (`kernelCLM_apply_eq_zero_of_const` with `zero_mem_spectrum_of_apply_eq_zero`) needs
no such hypothesis on any probability space carrying such a vector.

## Part 5 — the constant observable

`KernelStochastic K ν` (`∀ x, ∫ K x · = 1`) is sufficient for `T 1 = 1`
(`kernelCLM_oneLp_eq_oneLp`); the converse is not proved, and would be weaker, since `T 1 = 1`
constrains the row integral at almost every `x` rather than at every `x`. `coeFn_kernelCLM_oneLp`
computes `T 1` as the row integral.

At the Wilson slab kernel the row integral is at most `1` for `0 ≤ β` (`slabTransfer_oneLp_le_one`)
and at least `slabCap⁻¹` (`SlabKernelOperator.le_kernelCLM_one`), so `T 1` lies in
`[slabCap⁻¹, 1]`. That interval contains `1`, so those two bounds do not determine whether the
constant is an eigenvector, and no statement here determines it at any `β > 0`.
`slabKernelStochastic_beta_zero` proves the eigenvector equality at `β = 0`.

## The degenerate regimes

`SlabKernelOperator` names three regimes where `slabKernel ≡ 1` and `slabTransfer` is the rank-one
averaging map: `slabPlaqCount = 0` (that is, `d ≤ 1`), `β = 0`, and `N = 1`. The statements here
behave differently across them:

* Part 1's adjoint identity and Part 2's `T†T` results hold there and everywhere else, being true
  for every bounded kernel and every bounded operator.
* Part 3's Gram sufficiency holds there and is not vacuous: `finiteGram_one` proves `K ≡ 1` is the
  rank-one Gram at `A₀ ≡ 1`. `finiteGram_zero` is the matching control — `FiniteGram` admits
  `k = 0`, whose empty sum is the zero kernel — so `FiniteGram` alone is satisfied by an operator
  that moves nothing.
* Part 4's evaluation is about the degenerate regime and is sharpest there.
* Part 5's eigenvector equality is proved only there.
* `slabKernel_eq_intra_mul_inter` and its two supporting lemmas hold there, where the kernel is
  constant and the factorisation reads `1 = 1 * 1`.

## Scope

`slabTransfer` has no spectrum at `n ≥ 2`, where it is not an endomorphism; the spectral statements
here are about `slabNormal = T† ∘ T`, which is one. No statement connects any of this to
`GNSHilbert.ymH`, no statement proves `slabKernel` asymmetric —
`slabKernel_eq_intra_mul_inter` exhibits a factor independent of the second argument, and whether
the kernel depends on either argument is `SliceTrace`'s open coupling question — and no Hamiltonian
`-log T` is built.

The names used here that appear nowhere else in the tree are `ContinuousLinearMap.adjoint`,
`adjoint_inner_left`, `adjoint_inner_right`, `star_eq_adjoint`, `ext_inner_left`,
`Integrable.mul_prod`, `real_inner_self_eq_norm_sq`, `integral_mul_const` and `integral_finsetSum`;
`integral_integral_swap` and `spectrum.mem_iff` have compiled corroboration elsewhere. At the
v4.31.0 pin, `integral_mul_right` and `Integrable.prod_mul` do not exist — `integral_mul_const` and
`Integrable.mul_prod` do, and because `Integrable` unfolds to an `And`, the error for the wrong name
reports `And.prod_mul` — and `integral_finset_sum` is deprecated in favour of `integral_finsetSum`.

Build: `python research/code/lean_build.py build MassGap.SlabTransferAdjoint`.
-/

namespace MassGap.SlabTransferAdjoint

open MeasureTheory
open MassGap MassGap.SliceTrace MassGap.SlabKernelOperator
open MassGap.WilsonAction MassGap.WilsonHypercubic MassGap.CompactGauge
open MassGap.SliceTransfer MassGap.WilsonLattice

/-! ## Part 0 — the real `L²` pairing as an integral

One helper, used by everything below. `MeasureTheory.L2.inner_def` gives the pairing as an integral
of inner products of the values; over `ℝ` that inner product is multiplication. -/

section Pairing

variable {X : Type*} [MeasurableSpace X]

/-- The real `L²` inner product is the integral of the product.

DERIVED: the `2` is the `L²` exponent — the one exponent at which Mathlib's `Lp` carries an inner
product. It is not a chosen parameter. -/
theorem real_inner_Lp (μ : Measure X) (f g : Lp ℝ 2 μ) :
    (inner ℝ f g : ℝ) = ∫ x, (f : X → ℝ) x * (g : X → ℝ) x ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  have hmul : (inner ℝ ((f : X → ℝ) x) ((g : X → ℝ) x) : ℝ)
      = (f : X → ℝ) x * (g : X → ℝ) x := by
    rw [RCLike.inner_apply]; simp [mul_comm]
  exact hmul

end Pairing

/-! ## Part 1 — the adjoint of a bounded kernel operator

The whole content is one Fubini. The integrand `g(x) · K(x,y) · f(y)` is not bounded — `f` and `g`
are only `L²` — so `ActionSplit.integrable_of_bounded` does not apply and the dominating function is
built instead from the product of the two `L¹` envelopes, which is where the probability
normalisation is used a second time (an `L²` function on a probability space is `L¹`). -/

section Adjoint

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The transposed kernel. `Kᵀ y x = K x y`.

DERIVED: no numeral. -/
def kernelTranspose (K : X → Y → ℝ) : Y → X → ℝ := fun y x => K x y

/-- The transpose of a jointly measurable kernel is jointly measurable.

DERIVED: no numeral. -/
theorem measurable_kernelTranspose {K : X → Y → ℝ} (hK : Measurable (Function.uncurry K)) :
    Measurable (Function.uncurry (kernelTranspose K)) := hK.comp measurable_swap

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- The transpose carries the same uniform bound.

DERIVED: `C` is the caller's kernel bound; no numeral of this file's own. -/
theorem abs_kernelTranspose_le {K : X → Y → ℝ} {C : ℝ} (hKb : ∀ x y, |K x y| ≤ C) :
    ∀ y x, |kernelTranspose K y x| ≤ C := fun y x => hKb x y

/-- The pairing of the operator's image, as an iterated integral. No Fubini here — this is the
definition of the `L²` pairing with the operator's value substituted.

DERIVED: the `2`s are the `L²` exponent; the `0` is the sign condition `hC0` places on the kernel
bound `C`. -/
theorem inner_kernelCLM_left (K : X → Y → ℝ) (C : ℝ) (hK : Measurable (Function.uncurry K))
    (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (f : Lp ℝ 2 ν) (g : Lp ℝ 2 μ) :
    (inner ℝ (kernelCLM K C hK hC0 hKb μ ν f) g : ℝ)
      = ∫ x, ∫ y, (g : X → ℝ) x * (K x y * (f : Y → ℝ) y) ∂ν ∂μ := by
  rw [real_inner_Lp]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_kernelCLM K C hK hC0 hKb μ ν f] with x hx
  rw [hx, integral_const_mul]
  unfold kernelFun
  ring

/-- The product integrand is integrable. The only genuinely new measure-theoretic input of this
file. `|g(x) · K(x,y) · f(y)| ≤ C · |g(x)| · |f(y)|`, and the right-hand side is a product of two
`L¹` functions on two probability spaces.

DERIVED: the `2`s are the `L²` exponent; `C` is the caller's kernel bound. -/
theorem integrable_kernel_pair {K : X → Y → ℝ} {C : ℝ} (hK : Measurable (Function.uncurry K))
    (hKb : ∀ x y, |K x y| ≤ C) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (f : Lp ℝ 2 ν) (g : Lp ℝ 2 μ) :
    Integrable (Function.uncurry
      (fun (x : X) (y : Y) => (g : X → ℝ) x * (K x y * (f : Y → ℝ) y))) (μ.prod ν) := by
  show Integrable
    (fun z : X × Y => (g : X → ℝ) z.1 * (K z.1 z.2 * (f : Y → ℝ) z.2)) (μ.prod ν)
  have hgi : Integrable (fun x => |(g : X → ℝ) x|) μ :=
    ((Lp.memLp g).integrable one_le_two).abs
  have hfi : Integrable (fun y => |(f : Y → ℝ) y|) ν :=
    ((Lp.memLp f).integrable one_le_two).abs
  have hprod : Integrable
      (fun z : X × Y => |(g : X → ℝ) z.1| * |(f : Y → ℝ) z.2|) (μ.prod ν) :=
    hgi.mul_prod hfi
  have hm : StronglyMeasurable
      (fun z : X × Y => (g : X → ℝ) z.1 * (K z.1 z.2 * (f : Y → ℝ) z.2)) :=
    ((Lp.stronglyMeasurable g).comp_measurable measurable_fst).mul
      (hK.stronglyMeasurable.mul ((Lp.stronglyMeasurable f).comp_measurable measurable_snd))
  refine Integrable.mono' (hprod.const_mul C) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  calc |(g : X → ℝ) z.1| * (|K z.1 z.2| * |(f : Y → ℝ) z.2|)
      = (|(g : X → ℝ) z.1| * |(f : Y → ℝ) z.2|) * |K z.1 z.2| := by ring
    _ ≤ (|(g : X → ℝ) z.1| * |(f : Y → ℝ) z.2|) * C :=
        mul_le_mul_of_nonneg_left (hKb _ _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = C * (|(g : X → ℝ) z.1| * |(f : Y → ℝ) z.2|) := by ring

/-- The adjoint of a kernel operator is the operator of the transposed kernel.

It identifies `T†` concretely rather than asserting that it exists, which turns self-adjointness of
`T` into symmetry of `K`.

DERIVED: the `2`s are the `L²` exponent; the `0` is the sign condition `hC0` places on `C`; `C` is
the caller's kernel bound. -/
theorem adjoint_kernelCLM (K : X → Y → ℝ) (C : ℝ) (hK : Measurable (Function.uncurry K))
    (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ContinuousLinearMap.adjoint (kernelCLM K C hK hC0 hKb μ ν)
      = kernelCLM (kernelTranspose K) C (measurable_kernelTranspose hK) hC0
          (abs_kernelTranspose_le hKb) ν μ := by
  refine ContinuousLinearMap.ext (fun g => ?_)
  refine ext_inner_left ℝ (fun v => ?_)
  rw [ContinuousLinearMap.adjoint_inner_right,
    inner_kernelCLM_left K C hK hC0 hKb μ ν v g]
  have hR : (inner ℝ v (kernelCLM (kernelTranspose K) C (measurable_kernelTranspose hK) hC0
        (abs_kernelTranspose_le hKb) ν μ g) : ℝ)
      = ∫ y, ∫ x, (g : X → ℝ) x * (K x y * (v : Y → ℝ) y) ∂μ ∂ν := by
    rw [real_inner_Lp]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_kernelCLM (kernelTranspose K) C (measurable_kernelTranspose hK) hC0
      (abs_kernelTranspose_le hKb) ν μ g] with y hy
    rw [hy]
    simp only [kernelFun, kernelTranspose]
    have hstep : (∫ x, (g : X → ℝ) x * (K x y * (v : Y → ℝ) y) ∂μ)
        = (∫ x, K x y * (g : X → ℝ) x ∂μ) * (v : Y → ℝ) y := by
      have h0 : (∫ x, (g : X → ℝ) x * (K x y * (v : Y → ℝ) y) ∂μ)
          = ∫ x, (K x y * (g : X → ℝ) x) * (v : Y → ℝ) y ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
      rw [h0, integral_mul_const]
    rw [hstep]
    ring
  rw [hR]
  exact integral_integral_swap (integrable_kernel_pair hK hKb μ ν v g)

/-- The operator is determined by the kernel, the proof arguments being irrelevant.

DERIVED: the `2`s are the `L²` exponent; the `0` is the sign condition `hC0` places on the kernel
bound `C`. -/
theorem kernelCLM_congr {K K' : X → Y → ℝ} {C : ℝ} (hK : Measurable (Function.uncurry K))
    (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C)
    (hK' : Measurable (Function.uncurry K')) (hKb' : ∀ x y, |K' x y| ≤ C)
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : K = K') :
    kernelCLM K C hK hC0 hKb μ ν = kernelCLM K' C hK' hC0 hKb' μ ν := by
  subst h; rfl

end Adjoint

section SelfAdjoint

variable {X : Type*} [MeasurableSpace X]

/-- A symmetric kernel gives a self-adjoint operator. On one space, self-adjointness is exactly
kernel symmetry, through `adjoint_kernelCLM`.

DERIVED: the `2`s are the `L²` exponent; the `0` is the sign condition `hC0` places on `C`; `C` is
the caller's kernel bound. -/
theorem isSelfAdjoint_kernelCLM_of_symm (K : X → X → ℝ) (C : ℝ)
    (hK : Measurable (Function.uncurry K)) (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C)
    (μ : Measure X) [IsProbabilityMeasure μ] (hsymm : ∀ x y, K x y = K y x) :
    IsSelfAdjoint (kernelCLM K C hK hC0 hKb μ μ) := by
  have hstar : star (kernelCLM K C hK hC0 hKb μ μ)
      = ContinuousLinearMap.adjoint (kernelCLM K C hK hC0 hKb μ μ) :=
    ContinuousLinearMap.star_eq_adjoint _
  have hT : kernelTranspose K = K := by
    funext y x
    exact hsymm x y
  show star (kernelCLM K C hK hC0 hKb μ μ) = _
  rw [hstar, adjoint_kernelCLM K C hK hC0 hKb μ μ]
  exact kernelCLM_congr (measurable_kernelTranspose hK) hC0 (abs_kernelTranspose_le hKb)
    hK hKb μ μ hT

end SelfAdjoint

/-! ## Part 2 — `T† ∘ T`, and the record that it is free

Everything in this section holds for every bounded operator between any two real Hilbert spaces,
with no hypothesis whatever. `adjointComp_zero_eq_zero` is the control: the zero operator satisfies
all of it. A "positive self-adjoint operator" produced this way is therefore not evidence about the
dynamics — it is `GNSHilbert.ym_target_discharged_trivially` again. -/

section Free

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- `T† ∘ T` is self-adjoint — for every `T`, with no premise.

DERIVED: no numeral. -/
theorem isSelfAdjoint_adjointComp (T : E →L[ℝ] F) :
    IsSelfAdjoint ((ContinuousLinearMap.adjoint T).comp T) := by
  have hstar : star ((ContinuousLinearMap.adjoint T).comp T)
      = ContinuousLinearMap.adjoint ((ContinuousLinearMap.adjoint T).comp T) :=
    ContinuousLinearMap.star_eq_adjoint _
  show star ((ContinuousLinearMap.adjoint T).comp T) = _
  rw [hstar]
  refine ContinuousLinearMap.ext (fun x => ?_)
  refine ext_inner_left ℝ (fun v => ?_)
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]

/-- The quadratic form of `T† ∘ T` is the squared norm of the image — again with no premise.

DERIVED: the `2` is the exponent of a squared norm, forced by the polarisation it comes from. -/
theorem inner_adjointComp_self (T : E →L[ℝ] F) (f : E) :
    (inner ℝ f (((ContinuousLinearMap.adjoint T).comp T) f) : ℝ) = ‖T f‖ ^ 2 := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  exact real_inner_self_eq_norm_sq _

/-- `T† ∘ T` is a positive operator — with no premise, which is exactly the point.

DERIVED: the `0` is the sign asserted. -/
theorem inner_adjointComp_self_nonneg (T : E →L[ℝ] F) (f : E) :
    0 ≤ (inner ℝ f (((ContinuousLinearMap.adjoint T).comp T) f) : ℝ) := by
  rw [inner_adjointComp_self]
  positivity

/-- The control. At `T = 0` the composite is the zero operator, so the two theorems above are
satisfied by an operator that moves nothing. They carry no information about `T`.

DERIVED: the `0`s are the zero operator, which is the degenerate witness. -/
theorem adjointComp_zero_eq_zero :
    (ContinuousLinearMap.adjoint (0 : E →L[ℝ] F)).comp (0 : E →L[ℝ] F) = 0 := by
  simp

/-- The same control, as the satisfied conjunction.

DERIVED: the `0`s are the zero operator. -/
theorem isSelfAdjoint_adjointComp_zero :
    IsSelfAdjoint ((ContinuousLinearMap.adjoint (0 : E →L[ℝ] F)).comp (0 : E →L[ℝ] F))
      ∧ ∀ f : E, 0 ≤ (inner ℝ f (((ContinuousLinearMap.adjoint (0 : E →L[ℝ] F)).comp
          (0 : E →L[ℝ] F)) f) : ℝ) :=
  ⟨isSelfAdjoint_adjointComp 0, fun f => inner_adjointComp_self_nonneg 0 f⟩

end Free

/-! ## Part 3 — operator positivity: the finite Osterwalder–Seiler square

The classical argument for `0 ≤ ⟨f, T f⟩` is that `T = A* A`. Stated for a finite family it needs no
Fubini, and it has a necessary half that is the useful one here: a Gram kernel is symmetric. -/

section Gram

variable {X : Type*} [MeasurableSpace X]

/-- The finite gram condition — `K` is a finite sum of squares of bounded measurable functions.
This is `T = A* A` with a finite index, which is the shape a reflection-positivity Gram matrix
delivers.

DERIVED: no numeral; `k` and `CA` are existentially quantified. -/
def FiniteGram (K : X → X → ℝ) : Prop :=
  ∃ (k : ℕ) (A : Fin k → X → ℝ) (CA : ℝ),
    (∀ i, Measurable (A i)) ∧ (∀ i x, |A i x| ≤ CA) ∧ ∀ x y, K x y = ∑ i, A i x * A i y

/-- A gram kernel is symmetric — the necessary half. Any kernel that is not symmetric admits no
`A* A` representation at all, finite or otherwise, so the Osterwalder–Seiler route is closed for it
until the asymmetry is removed.

DERIVED: no numeral. -/
theorem FiniteGram.symm {K : X → X → ℝ} (h : FiniteGram K) (x y : X) : K x y = K y x := by
  obtain ⟨k, A, CA, _, _, hK⟩ := h
  rw [hK, hK]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- The quadratic form of a gram kernel is a sum of squares. The Osterwalder–Seiler positivity
argument at a finite Gram index, with `integral_finsetSum` in place of Fubini.

DERIVED: the `2`s are the `L²` exponent and, in `^ 2`, the square the argument produces; the `0` is
the sign condition `hC0` places on `C`; `C` and `CA` are the caller's bounds. -/
theorem inner_kernelCLM_self_eq_sum_sq_of_gram (K : X → X → ℝ) (C : ℝ)
    (hK : Measurable (Function.uncurry K)) (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C)
    (μ : Measure X) [IsProbabilityMeasure μ]
    {k : ℕ} (A : Fin k → X → ℝ) (CA : ℝ) (hAm : ∀ i, Measurable (A i))
    (hAb : ∀ i x, |A i x| ≤ CA) (hKA : ∀ x y, K x y = ∑ i, A i x * A i y)
    (f : Lp ℝ 2 μ) :
    (inner ℝ f (kernelCLM K C hK hC0 hKb μ μ f) : ℝ)
      = ∑ i, (∫ x, A i x * (f : X → ℝ) x ∂μ) ^ 2 := by
  have hfi : Integrable (f : X → ℝ) μ := (Lp.memLp f).integrable one_le_two
  have hAf : ∀ i, Integrable (fun x => A i x * (f : X → ℝ) x) μ := by
    intro i
    refine hfi.bdd_mul (c := CA) (hAm i).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => ?_))
    simpa [Real.norm_eq_abs] using hAb i x
  have hpt : ∀ x, kernelFun K μ (f : X → ℝ) x
      = ∑ i, A i x * (∫ y, A i y * (f : X → ℝ) y ∂μ) := by
    intro x
    unfold kernelFun
    have h1 : ∀ y, K x y * (f : X → ℝ) y = ∑ i, A i x * (A i y * (f : X → ℝ) y) := by
      intro y
      rw [hKA x y, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [integral_congr_ae (Filter.Eventually.of_forall h1),
      integral_finsetSum Finset.univ (fun i _ => (hAf i).const_mul (A i x))]
    exact Finset.sum_congr rfl (fun i _ => integral_const_mul _ _)
  rw [real_inner_Lp]
  have he : (fun x => (f : X → ℝ) x
      * ((kernelCLM K C hK hC0 hKb μ μ f : Lp ℝ 2 μ) : X → ℝ) x)
      =ᵐ[μ] fun x => ∑ i, (∫ y, A i y * (f : X → ℝ) y ∂μ) * (A i x * (f : X → ℝ) x) := by
    filter_upwards [coeFn_kernelCLM K C hK hC0 hKb μ μ f] with x hx
    rw [hx, hpt x, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [integral_congr_ae he,
    integral_finsetSum Finset.univ
      (fun i _ => (hAf i).const_mul (∫ y, A i y * (f : X → ℝ) y ∂μ))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_const_mul]
  ring

/-- The zero kernel is a gram kernel — the anti-vacuity control for Part 3, in the shape
`adjointComp_zero_eq_zero` has for Part 2. `FiniteGram` admits `k = 0`, whose empty sum is `0`, so
`FiniteGram` alone is satisfied by an operator that moves nothing and the sufficiency theorem below
has a trivial model. This is why Part 3 is a reduction.

DERIVED: the `0`s are the kernel's value and the empty Gram index; neither is chosen. -/
theorem finiteGram_zero : FiniteGram (fun _ _ : X => (0 : ℝ)) :=
  ⟨0, fun _ _ => 0, 0, fun i => measurable_const, fun i x => by simp, fun x y => by simp⟩

/-- The constant kernel is a gram kernel, with the single factor `A₀ ≡ 1`. This is the second
control: the one kernel `SlabKernelOperator` proves the Wilson slab kernel equals in its three
degenerate regimes is already Gram, so Part 3's sufficiency is nonvacuous exactly where it says
nothing about the dynamics.

DERIVED: the `1`s are the kernel's constant value, the single Gram factor and the Gram index's
cardinality; the `0` is the sign in the bound. -/
theorem finiteGram_one : FiniteGram (fun _ _ : X => (1 : ℝ)) :=
  ⟨1, fun _ _ => 1, 1, fun i => measurable_const, fun i x => by simp, fun x y => by simp⟩

/-- A gram kernel gives a positive operator — the sufficient half, proved.

DERIVED: the `0` is the sign asserted; the `2`s as above. -/
theorem inner_kernelCLM_self_nonneg_of_gram (K : X → X → ℝ) (C : ℝ)
    (hK : Measurable (Function.uncurry K)) (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C)
    (μ : Measure X) [IsProbabilityMeasure μ]
    {k : ℕ} (A : Fin k → X → ℝ) (CA : ℝ) (hAm : ∀ i, Measurable (A i))
    (hAb : ∀ i x, |A i x| ≤ CA) (hKA : ∀ x y, K x y = ∑ i, A i x * A i y)
    (f : Lp ℝ 2 μ) :
    0 ≤ (inner ℝ f (kernelCLM K C hK hC0 hKb μ μ f) : ℝ) := by
  rw [inner_kernelCLM_self_eq_sum_sq_of_gram K C hK hC0 hKb μ A CA hAm hAb hKA f]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- The sufficient half, stated on the `Prop` itself. This is the declaration a caller holding
`FiniteGram K` consumes; the previous one takes the square's data unpacked.

DERIVED: the `0` is the sign asserted; the `2`s are the `L²` exponent. -/
theorem inner_kernelCLM_self_nonneg_of_finiteGram (K : X → X → ℝ) (C : ℝ)
    (hK : Measurable (Function.uncurry K)) (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C)
    (μ : Measure X) [IsProbabilityMeasure μ] (h : FiniteGram K) (f : Lp ℝ 2 μ) :
    0 ≤ (inner ℝ f (kernelCLM K C hK hC0 hKb μ μ f) : ℝ) := by
  obtain ⟨k, A, CA, hAm, hAb, hKA⟩ := h
  exact inner_kernelCLM_self_nonneg_of_gram K C hK hC0 hKb μ A CA hAm hAb hKA f

end Gram

/-! ## Part 4 — the Doeblin lower bound, and the proof that it does not reach the spectrum -/

section Doeblin

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A pointwise lower bound on the kernel, transferred to the quadratic form on the positive cone.
With `c ≤ K` pointwise and `0 ≤ f` almost everywhere, `c · (∫f)² ≤ ⟨f, T f⟩`.

The hypothesis `0 ≤ᵐ f` is where the proof's pointwise step lives: `c · f y ≤ K x y · f y` reverses
on `{f < 0}`. No statement here removes it, and no kernel and no `f` refuting the conclusion without
it is exhibited.

The bound is not a spectral statement. `inner_kernelCLM_self_of_const` below exhibits a kernel
satisfying `1 ≤ K` at which both sides are `(∫f)²`, which is `0` on the whole mean-zero subspace.

DERIVED: the `0`s are the signs tested; the `2` in `^ 2` is the square of the mass of `f`, produced
by the argument; the `2`s in `Lp ℝ 2` are the `L²` exponent; `c` is the caller's lower bound. -/
theorem inner_kernelCLM_self_ge_of_nonneg (K : X → X → ℝ) (C : ℝ)
    (hK : Measurable (Function.uncurry K)) (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C)
    (μ : Measure X) [IsProbabilityMeasure μ] {c : ℝ} (hc : ∀ x y, c ≤ K x y)
    (f : Lp ℝ 2 μ) (hf : 0 ≤ᵐ[μ] (f : X → ℝ)) :
    c * (∫ x, (f : X → ℝ) x ∂μ) ^ 2
      ≤ (inner ℝ f (kernelCLM K C hK hC0 hKb μ μ f) : ℝ) := by
  have hfi : Integrable (f : X → ℝ) μ := (Lp.memLp f).integrable one_le_two
  have hin : ∀ x, c * (∫ y, (f : X → ℝ) y ∂μ) ≤ kernelFun K μ (f : X → ℝ) x := by
    intro x
    unfold kernelFun
    rw [← integral_const_mul]
    refine integral_mono_ae (hfi.const_mul c) (integrable_row_mul hK hKb hfi x) ?_
    filter_upwards [hf] with y hy
    exact mul_le_mul_of_nonneg_right (hc x y) hy
  have hprodint : Integrable (fun x => kernelFun K μ (f : X → ℝ) x * (f : X → ℝ) x) μ := by
    refine hfi.bdd_mul (c := C * ‖f‖) (stronglyMeasurable_kernelFun hK f).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => ?_))
    simpa [Real.norm_eq_abs] using abs_kernelFun_le hK hC0 hKb f x
  have hrepr : (fun x => (f : X → ℝ) x
      * ((kernelCLM K C hK hC0 hKb μ μ f : Lp ℝ 2 μ) : X → ℝ) x)
      =ᵐ[μ] fun x => kernelFun K μ (f : X → ℝ) x * (f : X → ℝ) x := by
    filter_upwards [coeFn_kernelCLM K C hK hC0 hKb μ μ f] with x hx
    rw [hx]
    ring
  have hlow : ∀ᵐ x ∂μ, (c * ∫ y, (f : X → ℝ) y ∂μ) * (f : X → ℝ) x
      ≤ kernelFun K μ (f : X → ℝ) x * (f : X → ℝ) x := by
    filter_upwards [hf] with x hx
    exact mul_le_mul_of_nonneg_right (hin x) hx
  rw [real_inner_Lp, integral_congr_ae hrepr]
  calc c * (∫ x, (f : X → ℝ) x ∂μ) ^ 2
      = ∫ x, (c * ∫ y, (f : X → ℝ) y ∂μ) * (f : X → ℝ) x ∂μ := by
        rw [integral_const_mul]; ring
    _ ≤ ∫ x, kernelFun K μ (f : X → ℝ) x * (f : X → ℝ) x ∂μ :=
        integral_mono_ae (hfi.const_mul _) hprodint hlow

/-- A constant kernel gives the rank-one averaging map. `T f = (∫ f) · 1`.

DERIVED: the `1`s are the kernel's constant value and `oneLp`'s; the `2`s are the `L²` exponent; the
`0` is the sign condition `hC0` places on the kernel bound `C`. -/
theorem kernelCLM_apply_of_const (K : X → Y → ℝ) (C : ℝ) (hK : Measurable (Function.uncurry K))
    (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hK1 : ∀ x y, K x y = 1) (f : Lp ℝ 2 ν) :
    kernelCLM K C hK hC0 hKb μ ν f = (∫ y, (f : Y → ℝ) y ∂ν) • oneLp μ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_kernelCLM K C hK hC0 hKb μ ν f,
    Lp.coeFn_smul (∫ y, (f : Y → ℝ) y ∂ν) (oneLp μ),
    (memLp_const (1 : ℝ) (μ := μ) (p := 2)).coeFn_toLp] with x h1 h2 h3
  rw [h1, h2]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show ((oneLp μ : Lp ℝ 2 μ) : X → ℝ) x = (1 : ℝ) from h3, mul_one]
  unfold kernelFun
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  show K x y * (f : Y → ℝ) y = (f : Y → ℝ) y
  rw [hK1, one_mul]

/-- A constant kernel kills every mean-zero vector.

DERIVED: the `0`s are the vanishing mass and the zero vector; the `1` is the kernel's value; the
`2` is the `L²` exponent. -/
theorem kernelCLM_apply_eq_zero_of_const (K : X → Y → ℝ) (C : ℝ)
    (hK : Measurable (Function.uncurry K)) (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C)
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hK1 : ∀ x y, K x y = 1) (f : Lp ℝ 2 ν) (hf0 : (∫ y, (f : Y → ℝ) y ∂ν) = 0) :
    kernelCLM K C hK hC0 hKb μ ν f = 0 := by
  rw [kernelCLM_apply_of_const K C hK hC0 hKb μ ν hK1 f, hf0, zero_smul]

/-- The quadratic form of the constant kernel is exactly the squared mass. `⟨f, T f⟩ = (∫f)²`.

It is nonnegative — so the constant kernel is operator-positive — and it vanishes on the whole
mean-zero subspace, although `1 ≤ K` holds with the largest constant a kernel bounded by `1` can
have. A Doeblin bound therefore does not by itself give a spectral statement.

DERIVED: the `1` is the kernel's constant value; the `2` in `^ 2` is the square produced by the
argument; the `2`s in `Lp ℝ 2` are the `L²` exponent; the `0` is the sign condition `hC0` places on
the kernel bound `C`. -/
theorem inner_kernelCLM_self_of_const (K : X → X → ℝ) (C : ℝ)
    (hK : Measurable (Function.uncurry K)) (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C)
    (μ : Measure X) [IsProbabilityMeasure μ] (hK1 : ∀ x y, K x y = 1) (f : Lp ℝ 2 μ) :
    (inner ℝ f (kernelCLM K C hK hC0 hKb μ μ f) : ℝ) = (∫ x, (f : X → ℝ) x ∂μ) ^ 2 := by
  rw [real_inner_Lp]
  have h : (fun x => (f : X → ℝ) x
      * ((kernelCLM K C hK hC0 hKb μ μ f : Lp ℝ 2 μ) : X → ℝ) x)
      =ᵐ[μ] fun x => (∫ y, (f : X → ℝ) y ∂μ) * (f : X → ℝ) x := by
    filter_upwards [coeFn_kernelCLM K C hK hC0 hKb μ μ f] with x hx
    rw [hx]
    unfold kernelFun
    rw [integral_congr_ae (Filter.Eventually.of_forall
      (fun y => by rw [hK1, one_mul] : ∀ y, K x y * (f : X → ℝ) y = (f : X → ℝ) y))]
    ring
  rw [integral_congr_ae h, integral_const_mul]
  ring

end Doeblin

section Spectrum

/-- A nonzero vector in the kernel puts `0` in the spectrum. Injectivity is what a unit gives;
this is its contrapositive, and it is the step `GNSHilbert`'s header says a Hamiltonian needs and
that positivity alone does not supply.

DERIVED: the `0`s are the spectral point and the zero vector, both forced by the statement. -/
theorem zero_mem_spectrum_of_apply_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (T : E →L[ℝ] E) (f : E) (hf : f ≠ 0) (hTf : T f = 0) :
    (0 : ℝ) ∈ spectrum ℝ T := by
  rw [spectrum.mem_iff, map_zero, zero_sub]
  intro hu
  obtain ⟨u, hu'⟩ := hu
  have h2 := congrArg (fun A : E →L[ℝ] E => A f) u.inv_mul
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at h2
  rw [hu', ContinuousLinearMap.neg_apply, hTf, neg_zero, map_zero] at h2
  exact hf h2.symm

end Spectrum

/-! ## Part 5 — the constant observable, and whether it is the vacuum -/

section Vacuum

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The stochastic condition — every row of the kernel integrates to one. This is exactly the
normalisation `SliceTrace` records the slab kernel as not having.

DERIVED: the `1` is the total mass a stochastic row must carry. -/
def KernelStochastic (K : X → Y → ℝ) (ν : Measure Y) : Prop := ∀ x, (∫ y, K x y ∂ν) = 1

/-- The image of the constant observable is the row integral.

DERIVED: the `2`s are the `L²` exponent; `oneLp`'s `1` is the constant observable's value; the `0`
is the sign condition `hC0` places on the kernel bound `C`. -/
theorem coeFn_kernelCLM_oneLp (K : X → Y → ℝ) (C : ℝ) (hK : Measurable (Function.uncurry K))
    (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ((kernelCLM K C hK hC0 hKb μ ν (oneLp ν) : Lp ℝ 2 μ) : X → ℝ)
      =ᵐ[μ] fun x => ∫ y, K x y ∂ν := by
  filter_upwards [coeFn_kernelCLM K C hK hC0 hKb μ ν (oneLp ν)] with x hx
  rw [hx]
  unfold kernelFun
  refine integral_congr_ae ?_
  filter_upwards [(memLp_const (1 : ℝ) (μ := ν) (p := 2)).coeFn_toLp] with y hy
  rw [show ((oneLp ν : Lp ℝ 2 ν) : Y → ℝ) y = (1 : ℝ) from hy]
  ring

/-- A stochastic kernel fixes the constant observable — the constant is then an eigenvector with
eigenvalue one, i.e. a vacuum.

DERIVED: the `1`s are the stochastic normalisation and `oneLp`'s value; the `2`s are the `L²`
exponent; the `0` is the sign condition `hC0` places on the kernel bound `C`. -/
theorem kernelCLM_oneLp_eq_oneLp (K : X → Y → ℝ) (C : ℝ) (hK : Measurable (Function.uncurry K))
    (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hst : KernelStochastic K ν) :
    kernelCLM K C hK hC0 hKb μ ν (oneLp ν) = oneLp μ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_kernelCLM_oneLp K C hK hC0 hKb μ ν,
    (memLp_const (1 : ℝ) (μ := μ) (p := 2)).coeFn_toLp] with x h1 h2
  rw [h1, show ((oneLp μ : Lp ℝ 2 μ) : X → ℝ) x = (1 : ℝ) from h2]
  exact hst x

/-- A sub-stochastic kernel makes the constant a supersolution, not an eigenvector.

DERIVED: the `1`s are the kernel's cap and the bound asserted; the `2`s are the `L²` exponent; the
`0` is the sign condition `hC0` places on the kernel bound `C`. -/
theorem kernelCLM_oneLp_le_one (K : X → Y → ℝ) (C : ℝ) (hK : Measurable (Function.uncurry K))
    (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hK1 : ∀ x y, K x y ≤ 1) :
    ∀ᵐ x ∂μ, ((kernelCLM K C hK hC0 hKb μ ν (oneLp ν) : Lp ℝ 2 μ) : X → ℝ) x ≤ 1 := by
  filter_upwards [coeFn_kernelCLM_oneLp K C hK hC0 hKb μ ν] with x hx
  rw [hx]
  have hint : Integrable (K x) ν := (memLp_row hK hKb ν x).integrable one_le_two
  have hmono : (∫ y, K x y ∂ν) ≤ ∫ _y : Y, (1 : ℝ) ∂ν :=
    integral_mono hint (integrable_const (1 : ℝ)) (fun y => hK1 x y)
  simpa using hmono

end Vacuum

/-! ## Part 6 — at the Wilson slab kernel

Everything below is an instantiation, plus two facts about `slabKernel` itself: the factor that does
not mention the second argument, and the exact value of the cap at zero coupling. -/

section Wilson

variable {d n N : ℕ} [NeZero n]

/-- The adjoint of the slab transfer operator, identified concretely: it is the kernel operator
of the transposed slab kernel, mapping `L²(slab t)` back to `L²(slab t+1)`.

DERIVED: the `1` in `t + 1` is `SliceTrace.slabKernel`'s time step; the `2`s are the `L²` exponent;
the `0` of `hN : N ≠ 0` is `wilsonDensity_nonneg`'s own hypothesis. -/
theorem adjoint_slabTransfer (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n) :
    ContinuousLinearMap.adjoint (slabTransfer (d := d) (n := n) hN τ β t)
      = kernelCLM (kernelTranspose (slabKernel (N := N) τ β t))
          (slabCap (d := d) (n := n) τ β t)
          (measurable_kernelTranspose (measurable_slabKernel_uncurry τ β t))
          (le_of_lt (slabCap_pos τ β t))
          (abs_kernelTranspose_le (abs_slabKernel_le hN τ β t))
          (slabHaar (N := N) τ (t + 1)) (slabHaar (N := N) τ t) :=
  adjoint_kernelCLM _ _ _ _ _ _ _

/-- The endomorphism `T† ∘ T`, on `L²` of the slab at `t+1`. `slabTransfer` is not an endomorphism
at `n ≥ 2` and has no spectrum; this does.

DERIVED: the `1` in `t + 1` is `slabKernel`'s time step; the `2`s are the `L²` exponent; the `0` is
the value `N` is required to differ from in `hN`. -/
noncomputable def slabNormal (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n) :
    Lp ℝ 2 (slabHaar (N := N) τ (t + 1)) →L[ℝ] Lp ℝ 2 (slabHaar (N := N) τ (t + 1)) :=
  (ContinuousLinearMap.adjoint (slabTransfer (d := d) (n := n) hN τ β t)).comp
    (slabTransfer (d := d) (n := n) hN τ β t)

/-- `slabNormal` is self-adjoint. `isSelfAdjoint_adjointComp` at `slabTransfer`; that lemma has no
premise, so the conclusion holds for every bounded operator, and `adjointComp_zero_eq_zero` is the
control showing the zero operator satisfies it too.

DERIVED: as `slabNormal`'s — the `1` in `t + 1` is `slabKernel`'s time step, the `2`s are the `L²`
exponent, and the `0` is the value `N` is required to differ from in `hN`. -/
theorem isSelfAdjoint_slabNormal (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n) :
    IsSelfAdjoint (slabNormal (d := d) (n := n) hN τ β t) :=
  isSelfAdjoint_adjointComp _

/-- The quadratic form of `slabNormal` is the squared norm of the image.

DERIVED: the `2` in `^ 2` is the square of a norm and the `2`s in `Lp ℝ 2` are the `L²` exponent;
the `1` in `t + 1` is `slabKernel`'s time step; the `0` is the value `N` is required to differ from
in `hN`. -/
theorem inner_slabNormal_self (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n)
    (f : Lp ℝ 2 (slabHaar (N := N) τ (t + 1))) :
    (inner ℝ f (slabNormal (d := d) (n := n) hN τ β t f) : ℝ)
      = ‖slabTransfer (d := d) (n := n) hN τ β t f‖ ^ 2 :=
  inner_adjointComp_self _ f

/-- `slabNormal` is a positive operator.

DERIVED: the `0` is the sign asserted and the value `N` is required to differ from in `hN`; the `1`
in `t + 1` is `slabKernel`'s time step; the `2`s are the `L²` exponent. -/
theorem inner_slabNormal_self_nonneg (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n)
    (f : Lp ℝ 2 (slabHaar (N := N) τ (t + 1))) :
    0 ≤ (inner ℝ f (slabNormal (d := d) (n := n) hN τ β t f) : ℝ) :=
  inner_adjointComp_self_nonneg _ f

/-- At nonnegative coupling the form of `slabNormal` is bounded by the squared norm. With the
previous theorem this places the form in `[0, ‖f‖²]`, which is the interval a contraction's
spectrum would have to live in. It is still not a spectral statement: no eigenvalue, no gap, and
Part 4 shows `0` can be in the spectrum with all of this holding.

DERIVED: the `2` in `^ 2` is a squared norm and the `2`s in `Lp ℝ 2` are the `L²` exponent; the `0`
of `hβ` is the sign of the coupling and is also the value `N` is required to differ from in `hN`;
the `1` in `t + 1` is `slabKernel`'s time step. -/
theorem inner_slabNormal_self_le (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (hβ : 0 ≤ β) (t : Fin n)
    (f : Lp ℝ 2 (slabHaar (N := N) τ (t + 1))) :
    (inner ℝ f (slabNormal (d := d) (n := n) hN τ β t f) : ℝ) ≤ ‖f‖ ^ 2 := by
  rw [inner_slabNormal_self]
  have h1 : ‖slabTransfer (d := d) (n := n) hN τ β t f‖ ≤ ‖f‖ := by
    calc ‖slabTransfer (d := d) (n := n) hN τ β t f‖
        ≤ ‖slabTransfer (d := d) (n := n) hN τ β t‖ * ‖f‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖f‖ :=
          mul_le_mul_of_nonneg_right (norm_slabTransfer_le_one hN τ β hβ t) (norm_nonneg f)
      _ = ‖f‖ := one_mul _
  have h0 : 0 ≤ ‖slabTransfer (d := d) (n := n) hN τ β t f‖ := norm_nonneg _
  nlinarith [h1, h0]

/-! ### The slab kernel's own asymmetry, exhibited

`SliceTrace`'s second difference between `slabKernel` and `SliceTransfer.transferKernel` is that the
former carries the whole intra-slice weight of slice `t` and the latter half at each argument. The
two lemmas below turn that into a theorem: the intra-slice factor does not read the second argument
at all. With `FiniteGram.symm` — a Gram kernel is symmetric — this is why the Osterwalder–Seiler
square cannot be pointed at `slabKernel` as it stands. -/

/-- A spatial plaquette of slice `t` reads only the spatial links at time `t`.
`SliceTransfer.intra_links_mem` in the shape `action_on_congr_of_support` consumes — the sharper
support than `SliceTrace.intra_support`, which allows time `t+1` as well.

Vacuous when `intraPlaq τ t = ∅`, which is the intra-slice half of `SlabKernelOperator`'s
`slabPlaqCount τ t = 0` regime (`d ≤ 1`).

DERIVED: no numeral. -/
theorem intra_support_slice (τ : Fin d) (t : Fin n) :
    ∀ q ∈ intraPlaq (d := d) (n := n) τ t, ∀ l ∈ (bd q).map Prod.fst,
      l ∈ sliceLinks (d := d) (n := n) τ t := by
  intro q hq l hl
  obtain ⟨lo, hlo, rfl⟩ := List.mem_map.mp hl
  exact intra_links_mem hq lo hlo

/-- The intra-slice action of a patched configuration does not read the second slab.

Two mechanisms give it. At `n ≥ 2` it is the intra-slice restriction: `intra_support_slice` confines
the plaquettes to time `t`. At `n = 1`, `t + 1 = t` and `SliceTrace.patch` resolves `s = t` first, so
`B` is never consulted for any link, and the statement carries nothing about the intra-slice cut.
Both sides are the empty sum when `intraPlaq τ t = ∅`.

DERIVED: the `1` in `t + 1` is `SliceTrace.patch`'s time step. -/
theorem intraSliceAction_patch_indep (τ : Fin d) (t : Fin n)
    (A : SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
    (B B' : SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N) :
    intraSliceAction τ t (regroup (timeOf τ) (patch (N := N) τ A B))
      = intraSliceAction τ t (regroup (timeOf τ) (patch (N := N) τ A B')) := by
  unfold intraSliceAction
  refine MassGap.ReflectionPositivity.action_on_congr_of_support
    (bd (d := d) (n := n)) (wilsonDensity (N := N)) (intraPlaq τ t)
    (sliceLinks (d := d) (n := n) τ t) (intra_support_slice τ t) _ _ (fun l hl => ?_)
  have ht : timeOf τ l = t := (mem_sliceLinks.mp hl).2
  rw [regroup_apply (timeOf τ) (patch (N := N) τ A B) l ht,
    regroup_apply (timeOf τ) (patch (N := N) τ A B') l ht]
  simp [patch]

/-- The slab kernel factors, with one factor blind to the second argument. The first factor is
the intra-slice weight of slice `t`; it is written at the filler configuration and does not mention
`B` at all. The second factor is the temporal coupling.

An identity, not a refutation of symmetry. In all three degenerate regimes it carries nothing: at
`β = 0`, at `slabPlaqCount τ t = 0` (that is, `d ≤ 1`) and at `N = 1` the kernel is constantly `1`
(`SlabKernelOperator.slabKernel_beta_zero`, `slabKernel_eq_one_of_plaqCount_zero`), so this reads
`1 = 1 * 1`, both factors are constant, and the kernel is symmetric. A factor blind to the second
argument is consistent with a constant kernel; whether the kernel depends on either argument is
`SliceTrace`'s coupling question.

DERIVED: the `1` written as the filler value is `SliceTrace.patch`'s group identity, never read
(`slabWeight_local` is what says so); the `1` in `t + 1` is `slabKernel`'s time step. -/
theorem slabKernel_eq_intra_mul_inter (τ : Fin d) (β : ℝ) (t : Fin n)
    (A : SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
    (B : SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N) :
    slabKernel (N := N) τ β t A B
      = Real.exp (-β * intraSliceAction τ t
            (regroup (timeOf τ) (patch (N := N) τ A (fun _ => 1))))
        * Real.exp (-β * ∑ q ∈ (interPlaq (d := d) (n := n) τ t).filter
              (fun q => q.1.1 ≠ q.1.2),
            wilsonDensity (wilsonHol (bd (d := d) (n := n)) q
              (regroup (timeOf τ) (patch (N := N) τ A B)))) := by
  unfold slabKernel slabWeight
  rw [intraSliceAction_patch_indep τ t A B (fun _ => 1)]

/-! ### The reduction for operator positivity, at Yang–Mills

`slabTransfer` is not an endomorphism at `n ≥ 2`, so `0 ≤ ⟨f, T f⟩` is not even a statement about
it. The condition below is the statement it becomes once an identification `e` of the two slab
configuration spaces is supplied — and the tree supplies none, which is itself part of the gap. -/

/-- The slab kernel pulled back to one space along a map `e` of the slab at `t` to the slab at
`t+1`.

DERIVED: the `1` in `t + 1` is `slabKernel`'s time step. -/
noncomputable def slabKernelPulled (τ : Fin d) (β : ℝ) (t : Fin n)
    (e : (SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
        → (SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N)) :
    (SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
      → (SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N) → ℝ :=
  fun A A' => slabKernel (N := N) τ β t A (e A')

/-- The pulled-back kernel is jointly measurable when `e` is.

DERIVED: the `1` in `t + 1` is `slabKernel`'s time step. -/
theorem measurable_slabKernelPulled (τ : Fin d) (β : ℝ) (t : Fin n)
    {e : (SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
        → (SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N)} (he : Measurable e) :
    Measurable (Function.uncurry (slabKernelPulled (N := N) τ β t e)) := by
  have h2 : Measurable (fun p : ((SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
      × (SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)) =>
      ((p.1, e p.2) : (SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
        × (SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N))) :=
    measurable_fst.prodMk (he.comp measurable_snd)
  have h1 := (measurable_slabKernel_uncurry (N := N) τ β t).comp h2
  exact h1

/-- The pulled-back kernel keeps the slab cap as a uniform bound.

DERIVED: the `0` of `hN : N ≠ 0` is `wilsonDensity_nonneg`'s own hypothesis; the `1` in `t + 1` is
`slabKernel`'s time step. -/
theorem abs_slabKernelPulled_le (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n)
    (e : (SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
        → (SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N)) :
    ∀ A A', |slabKernelPulled (N := N) τ β t e A A'| ≤ slabCap (d := d) (n := n) τ β t :=
  fun A A' => abs_slabKernel_le hN τ β t A (e A')

/-- The Osterwalder–Seiler square condition at the Wilson slab kernel, read through an
identification `e` of the two slab configuration spaces, as a `Prop`.

No statement in this file or in the tree establishes it. The tree's reflection results —
`ReflectionStrong.wilsonGibbsReflForm`'s `form_nonneg` and
`Complete.wilson_reflection_positive_at_even` — are nonnegativity of a Gibbs pairing of observables
on the full link configuration space, with the reflection `Θ` acting there and the Boltzmann weight
and partition function included. Neither is a Gram representation of `slabKernel`, which is a bare
Haar-measure kernel between two single slabs; `SlabKernelOperator` states the mismatch.

`FiniteGram.symm` adds a condition about `slabKernel` alone: a Gram kernel is symmetric, so this
`Prop` entails `slabGramVia_symm`, and no statement in the tree decides `slabKernel`'s symmetry. In
the three degenerate regimes the kernel is constant, hence symmetric, and this `Prop` holds there
(`finiteGram_one`).

DERIVED: the `1` in `t + 1` is `slabKernel`'s time step. -/
def SlabGramVia (τ : Fin d) (β : ℝ) (t : Fin n)
    (e : (SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
        → (SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N)) : Prop :=
  FiniteGram (slabKernelPulled (N := N) τ β t e)

/-- The necessary half of the reduction. If the square condition holds, the pulled-back kernel
is symmetric. Contrapositively, exhibiting an asymmetry refutes it.

DERIVED: the `1` in `t + 1` is `slabKernel`'s time step. -/
theorem slabGramVia_symm {τ : Fin d} {β : ℝ} {t : Fin n}
    {e : (SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
        → (SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N)}
    (h : SlabGramVia (N := N) τ β t e) (A A' : SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N) :
    slabKernelPulled (N := N) τ β t e A A' = slabKernelPulled (N := N) τ β t e A' A :=
  FiniteGram.symm h A A'

/-- The sufficient half of the reduction, proved. The square condition gives operator positivity
of the pulled-back slab transfer operator on one space.

DERIVED: the `0` is the sign asserted and the value `N` is required to differ from in `hN`; the `1`
in `t + 1` is `slabKernel`'s time step; the `2`s are the `L²` exponent; `CA` is the caller's bound
on the square's factors. -/
theorem inner_slabPulled_self_nonneg_of_gram (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n)
    {e : (SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
        → (SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N)} (he : Measurable e)
    {k : ℕ} (A : Fin k → (SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N) → ℝ) (CA : ℝ)
    (hAm : ∀ i, Measurable (A i)) (hAb : ∀ i x, |A i x| ≤ CA)
    (hKA : ∀ x y, slabKernelPulled (N := N) τ β t e x y = ∑ i, A i x * A i y)
    (f : Lp ℝ 2 (slabHaar (N := N) τ t)) :
    0 ≤ (inner ℝ f (kernelCLM (slabKernelPulled (N := N) τ β t e)
        (slabCap (d := d) (n := n) τ β t) (measurable_slabKernelPulled τ β t he)
        (le_of_lt (slabCap_pos τ β t)) (abs_slabKernelPulled_le hN τ β t e)
        (slabHaar (N := N) τ t) (slabHaar (N := N) τ t) f) : ℝ) :=
  inner_kernelCLM_self_nonneg_of_gram _ _ _ _ _ _ A CA hAm hAb hKA f

/-- The sufficient half, consuming `SlabGramVia` itself. This is the declaration that closes the
reduction: whoever proves the open `Prop` gets operator positivity of the pulled-back slab transfer
operator with nothing further to supply.

DERIVED: the `0` is the sign asserted and the value `N` is required to differ from in `hN`; the `1`
in `t + 1` is `slabKernel`'s time step; the `2`s are the `L²` exponent. -/
theorem inner_slabPulled_self_nonneg_of_slabGramVia (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n)
    {e : (SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
        → (SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N)} (he : Measurable e)
    (h : SlabGramVia (N := N) τ β t e) (f : Lp ℝ 2 (slabHaar (N := N) τ t)) :
    0 ≤ (inner ℝ f (kernelCLM (slabKernelPulled (N := N) τ β t e)
        (slabCap (d := d) (n := n) τ β t) (measurable_slabKernelPulled τ β t he)
        (le_of_lt (slabCap_pos τ β t)) (abs_slabKernelPulled_le hN τ β t e)
        (slabHaar (N := N) τ t) (slabHaar (N := N) τ t) f) : ℝ) :=
  inner_kernelCLM_self_nonneg_of_finiteGram _ _ _ _ _ _ h f

/-! ### The degenerate regime, and what it refutes

At `β = 0` the slab kernel is constantly `1` (`SliceTrace`'s `slabKernel_beta_zero`, carried by
`SlabKernelOperator`), the slab cap is exactly `1`, and the Doeblin constant `slabCap⁻¹` is
therefore `1` — the largest value it can take for a kernel bounded by one. The operator is
nonetheless rank one and annihilates every mean-zero vector. -/

omit [NeZero n] in
/-- The slab cap is exactly one at zero coupling, so the Doeblin constant there is `1`.

DERIVED: the `0` is the coupling being set; the `1` is `Real.exp 0`. Neither is chosen. -/
theorem slabCap_beta_zero (τ : Fin d) (t : Fin n) :
    slabCap (d := d) (n := n) τ 0 t = 1 := by
  simp [slabCap]

/-- At zero coupling the slab transfer operator is the rank-one averaging map.

DERIVED: the `0` is the coupling; the `1` in `t + 1` is `slabKernel`'s time step; the `2`s are the
`L²` exponent. -/
theorem slabTransfer_apply_of_beta_zero (hN : N ≠ 0) (τ : Fin d) (t : Fin n)
    (f : Lp ℝ 2 (slabHaar (N := N) τ (t + 1))) :
    slabTransfer (d := d) (n := n) hN τ 0 t f
      = (∫ B, (f : _ → ℝ) B ∂(slabHaar (N := N) τ (t + 1))) • oneLp (slabHaar (N := N) τ t) :=
  kernelCLM_apply_of_const _ _ _ _ _ _ _ (fun A B => slabKernel_beta_zero τ t A B) f

/-- At zero coupling `slabNormal` annihilates every mean-zero vector.

DERIVED: the `0`s are the coupling, the vanishing mass, the zero vector and the value `N` is
required to differ from in `hN`; the `1` in `t + 1` is `slabKernel`'s time step; the `2`s are the
`L²` exponent. -/
theorem slabNormal_apply_eq_zero_of_beta_zero (hN : N ≠ 0) (τ : Fin d) (t : Fin n)
    (f : Lp ℝ 2 (slabHaar (N := N) τ (t + 1)))
    (hf0 : (∫ B, (f : _ → ℝ) B ∂(slabHaar (N := N) τ (t + 1))) = 0) :
    slabNormal (d := d) (n := n) hN τ 0 t f = 0 := by
  unfold slabNormal
  rw [ContinuousLinearMap.comp_apply, slabTransfer_apply_of_beta_zero hN τ t f, hf0, zero_smul,
    map_zero]

/-- The refutation. At zero coupling, with the Doeblin constant equal to `1` and `slabNormal`
self-adjoint, positive and a contraction, `0` is still in the spectrum as soon as a nonzero
mean-zero `L²` vector exists. A uniform positive lower bound on the kernel therefore does not
deliver `0 ∉ spectrum`, and `H = -log T` does not follow from it.

The hypothesis `h` is the only thing standing between this and an unconditional statement, and it
fails exactly when the slab configuration space carries no nonconstant `L²` function — which is the
`N = 1` regime `SlabKernelOperator`'s header names, where `SU N` is trivial and `L²` is one
dimensional. **It is not discharged here and the tree does not discharge it**: exhibiting a
nonconstant slab observable is the same open question `GNSHilbert`'s header records.

DERIVED: the `0`s are the coupling, the spectral point, the vanishing mass in `h` and the value `N`
is required to differ from in `hN`; the `2` is the `L²` exponent; the `1` in `t + 1` is
`slabKernel`'s time step. -/
theorem zero_mem_spectrum_slabNormal_of_beta_zero (hN : N ≠ 0) (τ : Fin d) (t : Fin n)
    (h : ∃ f : Lp ℝ 2 (slabHaar (N := N) τ (t + 1)), f ≠ 0
        ∧ (∫ B, (f : _ → ℝ) B ∂(slabHaar (N := N) τ (t + 1))) = 0) :
    (0 : ℝ) ∈ spectrum ℝ (slabNormal (d := d) (n := n) hN τ 0 t) := by
  obtain ⟨f, hf, hf0⟩ := h
  exact zero_mem_spectrum_of_apply_eq_zero _ f hf
    (slabNormal_apply_eq_zero_of_beta_zero hN τ t f hf0)

/-! ### The vacuum at the Wilson slab kernel -/

/-- At nonnegative coupling the constant observable is a supersolution. `T 1 ≤ 1` almost
everywhere. With `slabCap_inv_le_slabTransfer_oneLp`, which bounds the same image below by
`slabCap⁻¹ > 0`, the constant is moved into `[slabCap⁻¹, 1]`. That interval contains `1`, so these
two bounds leave open whether the constant is an eigenvector, and this file settles that at no
`β > 0`. What settles it is `KernelStochastic`, proved here only at `β = 0`.

DERIVED: the `1`s are the kernel's cap at `0 ≤ β`, the bound asserted and the time step in `t + 1`;
the `0` of `hβ` is the sign of the coupling and the value `N` is required to differ from in `hN`;
the `2` is the `L²` exponent. -/
theorem slabTransfer_oneLp_le_one (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (hβ : 0 ≤ β) (t : Fin n) :
    ∀ᵐ A ∂(slabHaar (N := N) τ t),
      ((slabTransfer (d := d) (n := n) hN τ β t (oneLp (slabHaar (N := N) τ (t + 1)))
        : Lp ℝ 2 (slabHaar (N := N) τ t)) : _ → ℝ) A ≤ 1 :=
  kernelCLM_oneLp_le_one _ _ _ _ _ _ _
    (fun A B => le_trans (le_abs_self _) (abs_slabKernel_le_one hN τ β hβ t A B))

/-- The constant observable is moved off zero, uniformly. The Wilson instance of
`SlabKernelOperator.le_kernelCLM_one` at the slab kernel's own Doeblin constant. With
`slabTransfer_oneLp_le_one` this places `T 1` in `[slabCap⁻¹, 1]` at `0 ≤ β`. That interval contains
`1`, so it leaves open whether the constant is an eigenvector; what settles that is
`KernelStochastic`, which is proved only at `β = 0`.

DERIVED: the `1` in `t + 1` is `slabKernel`'s time step; the `0` is the value `N` is required to
differ from in `hN`; the `2` is the `L²` exponent; `slabCap⁻¹` is `slabWeight_bounds`'s own lower
bound, not a chosen level. -/
theorem slabCap_inv_le_slabTransfer_oneLp (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n) :
    ∀ᵐ A ∂(slabHaar (N := N) τ t),
      (slabCap (d := d) (n := n) τ β t)⁻¹
        ≤ ((slabTransfer (d := d) (n := n) hN τ β t (oneLp (slabHaar (N := N) τ (t + 1)))
          : Lp ℝ 2 (slabHaar (N := N) τ t)) : _ → ℝ) A :=
  le_kernelCLM_one _ _ _ _ _ _ _ (slabCap_inv_le_slabKernel hN τ β t)

/-- At zero coupling the slab kernel is stochastic — the degenerate positive control for the
normalisation `SliceTrace` records as absent.

DERIVED: the `0` is the coupling; the `1` is the total mass of a probability measure. -/
theorem slabKernelStochastic_beta_zero (τ : Fin d) (t : Fin n) :
    KernelStochastic (slabKernel (N := N) τ 0 t) (slabHaar (N := N) τ (t + 1)) := by
  intro A
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun B => slabKernel_beta_zero τ t A B))]
  simp

/-- At zero coupling the constant observable is an eigenvector with eigenvalue one. This is the
only regime in which the tree proves `T Ω = Ω`, and it is a degenerate one: the operator there is
the rank-one averaging map (`slabTransfer_apply_of_beta_zero`), and the one endomorphism in sight,
`slabNormal`, then has `0` in its spectrum as soon as a nonzero mean-zero vector exists
(`zero_mem_spectrum_slabNormal_of_beta_zero`). No spectrum of `slabTransfer` itself is computed or
claimed: at `n ≥ 2` it is not an endomorphism and has none, and no multiplicity is claimed for
`slabNormal`'s `0` either.

DERIVED: the `0` is the coupling; the `1`s are `oneLp`'s value and the eigenvalue. -/
theorem slabTransfer_oneLp_of_beta_zero (hN : N ≠ 0) (τ : Fin d) (t : Fin n) :
    slabTransfer (d := d) (n := n) hN τ 0 t (oneLp (slabHaar (N := N) τ (t + 1)))
      = oneLp (slabHaar (N := N) τ t) :=
  kernelCLM_oneLp_eq_oneLp _ _ _ _ _ _ _ (slabKernelStochastic_beta_zero τ t)

end Wilson

/-! ## Axiom footprints -/

#print axioms real_inner_Lp
#print axioms kernelTranspose
#print axioms measurable_kernelTranspose
#print axioms abs_kernelTranspose_le
#print axioms inner_kernelCLM_left
#print axioms integrable_kernel_pair
#print axioms adjoint_kernelCLM
#print axioms kernelCLM_congr
#print axioms isSelfAdjoint_kernelCLM_of_symm
#print axioms isSelfAdjoint_adjointComp
#print axioms inner_adjointComp_self
#print axioms inner_adjointComp_self_nonneg
#print axioms adjointComp_zero_eq_zero
#print axioms isSelfAdjoint_adjointComp_zero
#print axioms FiniteGram
#print axioms FiniteGram.symm
#print axioms inner_kernelCLM_self_eq_sum_sq_of_gram
#print axioms finiteGram_zero
#print axioms finiteGram_one
#print axioms inner_kernelCLM_self_nonneg_of_gram
#print axioms inner_kernelCLM_self_nonneg_of_finiteGram
#print axioms inner_kernelCLM_self_ge_of_nonneg
#print axioms kernelCLM_apply_of_const
#print axioms kernelCLM_apply_eq_zero_of_const
#print axioms inner_kernelCLM_self_of_const
#print axioms zero_mem_spectrum_of_apply_eq_zero
#print axioms KernelStochastic
#print axioms coeFn_kernelCLM_oneLp
#print axioms kernelCLM_oneLp_eq_oneLp
#print axioms kernelCLM_oneLp_le_one
#print axioms adjoint_slabTransfer
#print axioms slabNormal
#print axioms isSelfAdjoint_slabNormal
#print axioms inner_slabNormal_self
#print axioms inner_slabNormal_self_nonneg
#print axioms inner_slabNormal_self_le
#print axioms intra_support_slice
#print axioms intraSliceAction_patch_indep
#print axioms slabKernel_eq_intra_mul_inter
#print axioms slabKernelPulled
#print axioms measurable_slabKernelPulled
#print axioms abs_slabKernelPulled_le
#print axioms SlabGramVia
#print axioms slabGramVia_symm
#print axioms inner_slabPulled_self_nonneg_of_gram
#print axioms inner_slabPulled_self_nonneg_of_slabGramVia
#print axioms slabCap_beta_zero
#print axioms slabTransfer_apply_of_beta_zero
#print axioms slabNormal_apply_eq_zero_of_beta_zero
#print axioms zero_mem_spectrum_slabNormal_of_beta_zero
#print axioms slabTransfer_oneLp_le_one
#print axioms slabCap_inv_le_slabTransfer_oneLp
#print axioms slabKernelStochastic_beta_zero
#print axioms slabTransfer_oneLp_of_beta_zero

end MassGap.SlabTransferAdjoint
