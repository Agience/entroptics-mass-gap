import Mathlib
import MassGap.SlabKernelOperator

/-!
# MassGap.SlabTransferAdjoint — the adjoint of a kernel operator, and the quadratic form

`SlabKernelOperator` builds the bounded kernel operator `kernelCLM`. This module computes the
adjoint of a kernel operator, gives a symmetry criterion for self-adjointness, reduces operator
positivity to a Gram condition, and evaluates the quadratic form at a constant kernel.

## Part 1 — the adjoint is the transposed kernel

`adjoint_kernelCLM` : `(T_K)† = T_{Kᵀ}` with `Kᵀ y x = K x y`. One Fubini
(`integral_integral_swap`) against a dominating function built from `|f| ⊗ |g|`; both measures are
probability measures and `K` is bounded, so the integrand is dominated by `C · |g| ⊗ |f|`, which is
integrable because an `L²` function on a probability space is `L¹`.

`isSelfAdjoint_kernelCLM_of_symm` is the consequence for a symmetric kernel on one space.

## Part 2 — `T† ∘ T`

`isSelfAdjoint_adjointComp` and `inner_adjointComp_self_nonneg` hold for every bounded operator
between any two real Hilbert spaces, with no hypothesis on `T` and none relating the two spaces.
`adjointComp_zero_eq_zero` and `isSelfAdjoint_adjointComp_zero` are the control: the zero operator
satisfies both, so a self-adjoint positive operator obtained this way carries no information about
`T`.

## Part 3 — operator positivity as a Gram condition

`FiniteGram K` is the finite square `K x y = ∑ᵢ Aᵢ x · Aᵢ y`.

* `FiniteGram.symm` — a Gram kernel is symmetric, so symmetry is necessary.
* `inner_kernelCLM_self_eq_sum_sq_of_gram` — on a Gram kernel the quadratic form is `∑ᵢ (∫ Aᵢ f)²`,
  hence `inner_kernelCLM_self_nonneg_of_gram`. The Gram index is finite, so the interchange is
  `integral_finsetSum` and no Fubini is needed.

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

The abstract statement (`kernelCLM_apply_eq_zero_of_const` with
`zero_mem_spectrum_of_apply_eq_zero`) takes a nonzero mean-zero vector as a hypothesis.

## Part 5 — the constant observable

`KernelStochastic K ν` (`∀ x, ∫ K x · = 1`) is sufficient for `T 1 = 1`
(`kernelCLM_oneLp_eq_oneLp`); the converse is not proved, and would be weaker, since `T 1 = 1`
constrains the row integral at almost every `x` rather than at every `x`. `coeFn_kernelCLM_oneLp`
computes `T 1` as the row integral.

`kernelCLM_oneLp_le_one` bounds `T 1` above by `1` when `K ≤ 1`.

## Scope

`finiteGram_one` proves `K ≡ 1` is the rank-one Gram at `A₀ ≡ 1`. `finiteGram_zero` is the matching
control — `FiniteGram` admits `k = 0`, whose empty sum is the zero kernel — so `FiniteGram` alone
is satisfied by an operator that moves nothing. No statement connects any of this to
`GNSHilbert.ymH`, and no Hamiltonian `-log T` is built.

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
open MassGap.WilsonLattice

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
control: Part 3's sufficiency is nonvacuous at the constant kernel, where it says nothing about
dynamics.

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

/-- The stochastic condition — every row of the kernel integrates to one.

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

end MassGap.SlabTransferAdjoint
