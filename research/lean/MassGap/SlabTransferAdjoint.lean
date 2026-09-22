import Mathlib
import MassGap.SlabKernelOperator

/-!
# MassGap.SlabTransferAdjoint — the adjoint, the quadratic form, and what the Doeblin bound is worth

`SlabKernelOperator` built `slabTransfer`, a bounded map `L²(slab t+1) →L[ℝ] L²(slab t)`, and closed
with four explicit refusals: not self-adjoint, not operator-positive, no spectrum, no Hamiltonian.
This file takes each of those in turn on the `L²` route alone, and the one-line summary is:
it makes the first two into sharp, checkable conditions on the KERNEL, and proves that one specific
tool proposed for the last two cannot supply them.

* **First (self-adjointness).** Not reached for `slabTransfer`, which is not an endomorphism at
  `n ≥ 2` and whose kernel's symmetry the tree does not decide. What is reached is the ADJOINT
  identity at `slabTransfer` (`adjoint_slabTransfer`), a self-adjointness criterion equivalent to
  kernel symmetry, and self-adjointness of `slabNormal = T† ∘ T`, which is free for every operator.
  `MassGap.SliceTransferSelfAdjoint` carries the criterion to `SliceTransfer.transferKernel`, the
  tree's one kernel that IS proved symmetric, and gets a concrete self-adjoint operator there.
* **Second (operator positivity).** Not reached. Reduced to a named `Prop` (`SlabGramVia`) with
  both halves proved: necessary (`slabGramVia_symm`) and sufficient
  (`inner_slabPulled_self_nonneg_of_slabGramVia`). Reported as OPEN.
* **Third (`0 ∉ spectrum`, hence a Hamiltonian).** Not reached, and the Doeblin bound
  `SlabKernelOperator` flagged is proved NOT to supply it — conditionally at Yang–Mills, on the
  existence of a nonzero mean-zero `L²` vector, which is itself undischarged. No impossibility
  proof of any kind is offered: what is refuted is one route, not the target.
* **Fourth (the vacuum).** Settled negatively only at the level of "the two bounds available do not
  decide it"; the eigenvector equality is proved at `β = 0` and neither proved nor refuted
  elsewhere.

## What is proved

**Part 1 — the adjoint is a kernel operator, and it is the TRANSPOSED kernel.**
`adjoint_kernelCLM` : `(T_K)† = T_{Kᵀ}` where `Kᵀ y x = K x y`. The proof is one Fubini
(`integral_integral_swap`) against a dominating function built from `|f| ⊗ |g|`; both measures are
probability measures and `K` is bounded, so the product integrand is dominated by `C · |g| ⊗ |f|`,
which is integrable because an `L²` function on a probability space is `L¹`. From it,
`isSelfAdjoint_kernelCLM_of_symm` : a SYMMETRIC kernel on ONE space gives a self-adjoint operator.
The adjoint identity is instantiated at the Wilson slab kernel (`adjoint_slabTransfer`); the
self-adjointness criterion is NOT, and cannot be — `slabTransfer` is not an endomorphism at `n ≥ 2`
and `slabKernel`'s symmetry is neither proved nor refuted anywhere. `MassGap.SliceTransferSelfAdjoint`
carries the criterion to the tree's one kernel that IS proved symmetric,
`SliceTransfer.transferKernel`.

**Part 2 — `T† ∘ T` is self-adjoint and positive, AND THAT IS FREE.**
`isSelfAdjoint_adjointComp` and `inner_adjointComp_self_nonneg` carry NO hypothesis on `T` and no
hypothesis relating the two spaces: they hold for every bounded operator between any two real
Hilbert spaces. `adjointComp_zero_eq_zero` and `isSelfAdjoint_adjointComp_zero` are the control —
the zero operator satisfies both, so "self-adjoint positive operator" obtained this way discharges
nothing. This is `GNSHilbert.ym_target_discharged_trivially` in the present setting and it is
recorded as such rather than presented as a result.

**Part 3 — operator positivity, and the exact reduction.**
`FiniteGram K` is the finite Osterwalder–Seiler square: `K x y = ∑ᵢ Aᵢ x · Aᵢ y`. Two theorems:

* `FiniteGram.symm` — a Gram kernel IS SYMMETRIC. This is a NECESSARY condition, and it is the
  sharp statement of why the reflection route cannot be pointed at `slabKernel` as it stands:
  `slabKernel` carries the WHOLE intra-slice weight of slice `t` and none of slice `t+1`
  (`slabKernel_eq_intra_mul_inter`, below, exhibits the factor that does not mention the second
  argument), and its temporal plaquette sum reads the AXIS links, which belong to slab `t` alone.
  Any `A* A` representation forces symmetry, so no such representation of `slabKernel` exists
  unless that asymmetry is removed first. Removing it is temporal gauge, which is
  `SliceTransfer`'s hypothesis `hg` and is discharged nowhere in the tree.
* `inner_kernelCLM_self_eq_sum_sq_of_gram` — on a Gram kernel the quadratic form IS the sum of
  squares `∑ᵢ (∫ Aᵢ f)²`, hence `inner_kernelCLM_self_nonneg_of_gram`. This is SUFFICIENT, it is
  proved, and it needs no Fubini at all: the Gram index is finite, so the interchange is
  `integral_finsetSum`.

`SlabGramVia` is the same condition at Yang–Mills, stated through an explicit measurable
identification `e` of the two slab configuration spaces (the tree has no canonical one), with
`slabGramVia_symm` and `inner_slabPulled_self_nonneg_of_gram` as its necessary and sufficient
halves. **It is introduced as OPEN. Nothing in this file proves it and nothing in the tree does.**

**Part 4 — what the Doeblin bound gives, and what it provably does not.**
`inner_kernelCLM_self_ge_of_nonneg` : with `c ≤ K` pointwise and `f ≥ 0` almost everywhere,
`c · (∫f)² ≤ ⟨f, T f⟩`. **The bound is not a spectral statement**, and whether the hypothesis
`f ≥ 0` can be dropped is not settled here — the proof's pointwise step reverses without it and no
counterexample is constructed. `inner_kernelCLM_self_of_const` computes the form exactly when `K ≡ 1`:
`⟨f, T f⟩ = (∫f)²`, which VANISHES on the whole mean-zero subspace although the Doeblin constant
there is `1`, the largest it can be. `kernelCLM_apply_of_const` shows the operator is then the
rank-one averaging map `f ↦ (∫f) · 1`, and `zero_mem_spectrum_of_apply_eq_zero` turns any nonzero
mean-zero vector into `0 ∈ spectrum`. So:

> A uniform positive lower bound on the kernel does NOT put `0` outside the spectrum — not even at
> the constant `1`, the largest a kernel bounded by `1` can have — and therefore does not deliver
> `H = -log T`.

The proved instance is at the constant `1`; no declaration here covers other constants, and the
statement is about the ROUTE, not about `0 ∉ spectrum` being unattainable by other means.

**At Yang–Mills it is CONDITIONAL, and the condition is not discharged.** `slabCap_beta_zero` gives
Doeblin constant exactly `1` at `β = 0`, and `zero_mem_spectrum_slabNormal_of_beta_zero` puts `0`
in the spectrum of the one self-adjoint operator in sight — **on the hypothesis that a nonzero
mean-zero `L²` vector exists.** That hypothesis fails when `L²(slabHaar)` is at most one
dimensional, which is what `N = 1` (trivial gauge group) or an empty slab would give; that those
are the only ways it fails is NOT proved here and not proved in the tree, and exhibiting a
nonconstant slab observable is the same open question `GNSHilbert`'s header records. The abstract
half (`kernelCLM_apply_eq_zero_of_const` with `zero_mem_spectrum_of_apply_eq_zero`) is
unconditional on any probability space that carries such a vector; no concrete such space is
constructed here either.

**Part 5 — the constant observable is NOT the vacuum.**
`KernelStochastic K ν` (`∀ x, ∫ K x · = 1`) is proved SUFFICIENT for `T 1 = 1`
(`kernelCLM_oneLp_eq_oneLp`) — one direction only; the converse is not proved and would in any case
be weaker, since `T 1 = 1` constrains the row integral at almost every `x` and not at every `x`.
`coeFn_kernelCLM_oneLp` computes `T 1` as the row integral. At
the Wilson slab kernel the row integral is bounded above by `1` at `0 ≤ β`
(`slabTransfer_oneLp_le_one`) and below by `slabCap⁻¹` (`SlabKernelOperator.le_kernelCLM_one`), so
`1` is moved into `[slabCap⁻¹, 1]`. **That interval contains `1`, so the two bounds do not decide
whether the constant is an eigenvector** — and nothing here does, at any `β > 0`.
`slabKernelStochastic_beta_zero` proves the eigenvector equality at `β = 0`, the degenerate regime,
and nothing proves or refutes it anywhere else. The
normalisation that would fix it divides the kernel by its own row integral, which is a Doob
`h`-transform; the `h` that keeps the operator symmetric is the top eigenfunction, and producing one
is a Perron–Frobenius or Krein–Rutman statement. **Nothing in the tree produces one, and whether
Mathlib at the pin has one was NOT checked here** — that would need elaborating a candidate name on
the build host, which this file does only for the names it actually uses.

## The degenerate-regime check, run on every statement here

`SlabKernelOperator` names three regimes where `slabKernel ≡ 1` and `slabTransfer` is the rank-one
averaging map: `slabPlaqCount = 0` (i.e. `d ≤ 1`), `β = 0`, and `N = 1`. Every theorem below was
checked against them, and the outcome is not uniform:

* Part 1's adjoint identity and Part 2's `T†T` results are TRUE and EMPTY there — they are true for
  every bounded kernel and every bounded operator respectively, degenerate or not.
* Part 3's Gram sufficiency is TRUE and NONVACUOUS there — `finiteGram_one` proves `K ≡ 1` is the
  rank-one Gram `A₀ ≡ 1` — which is exactly why it is reported as a REDUCTION and not as progress:
  the one kernel the tree can prove is Gram is the constant one. `finiteGram_zero` is the matching
  anti-vacuity control: `FiniteGram` admits `k = 0`, whose empty sum is the ZERO kernel, so
  `FiniteGram` on its own is satisfied by an operator that moves nothing.
* Part 4's negative result IS ABOUT the degenerate regime and is sharpest there: it is the proof
  that the Doeblin route fails, and it fails at the best possible constant.
* Part 5's vacuum statement HOLDS ONLY in the degenerate regime.
* `slabKernel_eq_intra_mul_inter` and its two supporting lemmas are true there and their STATED
  SIGNIFICANCE is empty there — the kernel is constant, so the factorisation reads `1 = 1 * 1` and
  exhibits nothing. Their docstrings say so.

Every statement whose truth or whose content depends on a degenerate regime says so in its own
docstring.

## What this does NOT claim

* **No spectrum of `slabTransfer`.** At `n ≥ 2` it is not an endomorphism and has no spectrum;
  the spectral statements here are about `slabNormal = T† ∘ T`, which is one, and they are the
  free ones plus one negative result.
* **No bridge to `GNSHilbert.ymH`.** `SlabKernelOperator`'s fourfold mismatch stands untouched.
* **No proof that `slabKernel` is asymmetric.** `slabKernel_eq_intra_mul_inter` exhibits a factor
  independent of the second argument; proving the kernel actually DEPENDS on either argument is
  `SliceTrace`'s open coupling question and is not touched here.
* **No Hamiltonian.** `-log T` is not built, `0 ∉ spectrum` is not proved for anything, and Part 4
  is the proof that the tool proposed for it cannot supply it.

## The external footprint, and how it was checked

The names this file uses that appear NOWHERE ELSE in the tree are
`ContinuousLinearMap.adjoint`, `adjoint_inner_left`, `adjoint_inner_right`, `star_eq_adjoint`,
`ext_inner_left`, `Integrable.mul_prod`, `real_inner_self_eq_norm_sq`, `integral_mul_const` and
`integral_finsetSum`; `integral_integral_swap` and `spectrum.mem_iff` have compiled corroboration
elsewhere in the tree. **None of them was recalled: each was elaborated on the build host at
v4.31.0**, and the `#print axioms` block at the end is what reports the result. Two names that were
guessed WRONG and are recorded here rather than quietly fixed: `integral_mul_right` does not exist
at the pin (`integral_mul_const` does); `Integrable.prod_mul` does not exist at the pin
(`Integrable.mul_prod` does — and because `Integrable` unfolds to an `And`, the error for the wrong
name names `And.prod_mul`, which is worth knowing); and `integral_finset_sum` is deprecated in
favour of `integral_finsetSum`.

No `sorry`, no new axioms. Foundational footprint only (`#print axioms` at the end).
Build: `python research/code/lean_build.py build MassGap.SlabTransferAdjoint`.
-/

namespace MassGap.SlabTransferAdjoint

open MeasureTheory
open MassGap MassGap.SliceTrace MassGap.SlabKernelOperator
open MassGap.WilsonAction MassGap.WilsonHypercubic MassGap.CompactGauge
open MassGap.SliceTransfer MassGap.WilsonLattice

/-! ## Part 0 — the real `L²` pairing as an integral

One helper, used by everything below. `MeasureTheory.L2.inner_def` gives the pairing as an integral
of inner products of the VALUES; over `ℝ` that inner product is multiplication. -/

section Pairing

variable {X : Type*} [MeasurableSpace X]

/-- **THE REAL `L²` INNER PRODUCT IS THE INTEGRAL OF THE PRODUCT.**

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

The whole content is one Fubini. The integrand `g(x) · K(x,y) · f(y)` is NOT bounded — `f` and `g`
are only `L²` — so `ActionSplit.integrable_of_bounded` does not apply and the dominating function is
built instead from the product of the two `L¹` envelopes, which is where the probability
normalisation is used a second time (an `L²` function on a probability space is `L¹`). -/

section Adjoint

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- **THE TRANSPOSED KERNEL.** `Kᵀ y x = K x y`.

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

/-- **THE PAIRING OF THE OPERATOR'S IMAGE, AS AN ITERATED INTEGRAL.** No Fubini here — this is the
definition of the `L²` pairing with the operator's value substituted.

DERIVED: the `2`s are the `L²` exponent. -/
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

/-- **THE PRODUCT INTEGRAND IS INTEGRABLE.** The only genuinely new measure-theoretic input of this
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

/-- **THE ADJOINT OF A KERNEL OPERATOR IS THE OPERATOR OF THE TRANSPOSED KERNEL.**

This is the statement `SlabKernelOperator` did not make. It identifies `T†` CONCRETELY, rather than
asserting it exists, and it is what turns "is `T` self-adjoint?" into "is `K` symmetric?".

DERIVED: the `2`s are the `L²` exponent; `C` is the caller's kernel bound. -/
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

/-- **THE OPERATOR IS DETERMINED BY THE KERNEL**, the proof arguments being irrelevant.

DERIVED: the `2`s are the `L²` exponent. -/
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

/-- **A SYMMETRIC KERNEL GIVES A SELF-ADJOINT OPERATOR.** This is the answer to the first question
`SlabKernelOperator` left open, on one space: self-adjointness is EXACTLY kernel symmetry, through
`adjoint_kernelCLM`.

DERIVED: the `2`s are the `L²` exponent; `C` is the caller's kernel bound. -/
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

Everything in this section holds for EVERY bounded operator between any two real Hilbert spaces,
with no hypothesis whatever. `adjointComp_zero_eq_zero` is the control: the zero operator satisfies
all of it. A "positive self-adjoint operator" produced this way is therefore not evidence about the
dynamics — it is `GNSHilbert.ym_target_discharged_trivially` again. -/

section Free

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **`T† ∘ T` IS SELF-ADJOINT — FOR EVERY `T`, WITH NO PREMISE.**

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

/-- **THE QUADRATIC FORM OF `T† ∘ T` IS THE SQUARED NORM OF THE IMAGE** — again with no premise.

DERIVED: the `2` is the exponent of a squared norm, forced by the polarisation it comes from. -/
theorem inner_adjointComp_self (T : E →L[ℝ] F) (f : E) :
    (inner ℝ f (((ContinuousLinearMap.adjoint T).comp T) f) : ℝ) = ‖T f‖ ^ 2 := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  exact real_inner_self_eq_norm_sq _

/-- **`T† ∘ T` IS A POSITIVE OPERATOR** — with no premise, which is exactly the point.

DERIVED: the `0` is the sign asserted. -/
theorem inner_adjointComp_self_nonneg (T : E →L[ℝ] F) (f : E) :
    0 ≤ (inner ℝ f (((ContinuousLinearMap.adjoint T).comp T) f) : ℝ) := by
  rw [inner_adjointComp_self]
  positivity

/-- **THE CONTROL.** At `T = 0` the composite is the zero operator, so the two theorems above are
satisfied by an operator that moves nothing. They carry no information about `T`.

DERIVED: the `0`s are the zero operator, which IS the degenerate witness. -/
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

The classical argument for `0 ≤ ⟨f, T f⟩` is that `T = A* A`. Stated for a FINITE family it needs no
Fubini, and it has a necessary half that is the useful one here: a Gram kernel is symmetric. -/

section Gram

variable {X : Type*} [MeasurableSpace X]

/-- **THE FINITE GRAM CONDITION** — `K` is a finite sum of squares of bounded measurable functions.
This is `T = A* A` with a finite index, which is the shape a reflection-positivity Gram matrix
delivers.

DERIVED: no numeral; `k` and `CA` are existentially quantified. -/
def FiniteGram (K : X → X → ℝ) : Prop :=
  ∃ (k : ℕ) (A : Fin k → X → ℝ) (CA : ℝ),
    (∀ i, Measurable (A i)) ∧ (∀ i x, |A i x| ≤ CA) ∧ ∀ x y, K x y = ∑ i, A i x * A i y

/-- **A GRAM KERNEL IS SYMMETRIC — THE NECESSARY HALF.** Any kernel that is not symmetric admits no
`A* A` representation at all, finite or otherwise, so the Osterwalder–Seiler route is closed for it
until the asymmetry is removed.

DERIVED: no numeral. -/
theorem FiniteGram.symm {K : X → X → ℝ} (h : FiniteGram K) (x y : X) : K x y = K y x := by
  obtain ⟨k, A, CA, _, _, hK⟩ := h
  rw [hK, hK]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- **THE QUADRATIC FORM OF A GRAM KERNEL IS A SUM OF SQUARES.** The whole Osterwalder–Seiler
positivity argument, at a finite Gram index, with `integral_finsetSum` in place of Fubini.

DERIVED: the `2`s are the `L²` exponent and, in `^ 2`, the square the argument produces; `C` and
`CA` are the caller's bounds. -/
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

/-- **THE ZERO KERNEL IS A GRAM KERNEL** — the anti-vacuity control for Part 3, in the shape
`adjointComp_zero_eq_zero` has for Part 2. `FiniteGram` admits `k = 0`, whose empty sum is `0`, so
`FiniteGram` alone is satisfied by an operator that moves nothing and the sufficiency theorem below
has a trivial model. This is why Part 3 is reported as a REDUCTION.

DERIVED: the `0`s are the kernel's value and the empty Gram index; neither is chosen. -/
theorem finiteGram_zero : FiniteGram (fun _ _ : X => (0 : ℝ)) :=
  ⟨0, fun _ _ => 0, 0, fun i => measurable_const, fun i x => by simp, fun x y => by simp⟩

/-- **THE CONSTANT KERNEL IS A GRAM KERNEL**, with the single factor `A₀ ≡ 1`. This is the SECOND
control: the one kernel `SlabKernelOperator` proves the Wilson slab kernel equals in its three
degenerate regimes is already Gram, so Part 3's sufficiency is nonvacuous exactly where it says
nothing about the dynamics.

DERIVED: the `1`s are the kernel's constant value, the single Gram factor and the Gram index's
cardinality; the `0` is the sign in the bound. -/
theorem finiteGram_one : FiniteGram (fun _ _ : X => (1 : ℝ)) :=
  ⟨1, fun _ _ => 1, 1, fun i => measurable_const, fun i x => by simp, fun x y => by simp⟩

/-- **A GRAM KERNEL GIVES A POSITIVE OPERATOR — THE SUFFICIENT HALF, PROVED.**

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

/-- **THE SUFFICIENT HALF, STATED ON THE `Prop` ITSELF.** This is the declaration a caller holding
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

/-- **THE DOEBLIN BOUND ON THE QUADRATIC FORM, ON THE POSITIVE CONE ONLY.** With `c ≤ K` pointwise
and `0 ≤ f` almost everywhere, `c · (∫f)² ≤ ⟨f, T f⟩`.

**THE HYPOTHESIS `0 ≤ᵐ f` IS WHERE THE PROOF SPENDS ITS ONLY NON-ROUTINE STEP**, and nothing here
shows the conclusion survives without it: the pointwise inequality `c · f y ≤ K x y · f y` reverses
on `{f < 0}`, and this file exhibits no kernel and no `f` for which the conclusion fails. **That is
a gap in the evidence and it is left as one.** What IS proved about the bound is weaker and
different: `inner_kernelCLM_self_of_const` below exhibits a kernel satisfying `1 ≤ K` on which the
bound is VACUOUS — both sides are `(∫f)²`, which is `0` on the whole mean-zero subspace.

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

/-- **A CONSTANT KERNEL GIVES THE RANK-ONE AVERAGING MAP.** `T f = (∫ f) · 1`.

DERIVED: the `1`s are the kernel's constant value and `oneLp`'s; the `2`s are the `L²` exponent. -/
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

/-- **A CONSTANT KERNEL KILLS EVERY MEAN-ZERO VECTOR.**

DERIVED: the `0`s are the vanishing mass and the zero vector; the `1` is the kernel's value; the
`2` is the `L²` exponent. -/
theorem kernelCLM_apply_eq_zero_of_const (K : X → Y → ℝ) (C : ℝ)
    (hK : Measurable (Function.uncurry K)) (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C)
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hK1 : ∀ x y, K x y = 1) (f : Lp ℝ 2 ν) (hf0 : (∫ y, (f : Y → ℝ) y ∂ν) = 0) :
    kernelCLM K C hK hC0 hKb μ ν f = 0 := by
  rw [kernelCLM_apply_of_const K C hK hC0 hKb μ ν hK1 f, hf0, zero_smul]

/-- **THE QUADRATIC FORM OF THE CONSTANT KERNEL IS EXACTLY THE SQUARED MASS.** `⟨f, T f⟩ = (∫f)²`.

It is nonnegative — so the constant kernel IS operator-positive — and it vanishes on the whole
mean-zero subspace, although `1 ≤ K` holds with the largest constant a kernel bounded by `1` can
have. **This is the refutation of "a Doeblin bound gives a spectral statement".**

DERIVED: the `1` is the kernel's constant value; the `2` in `^ 2` is the square produced by the
argument; the `2`s in `Lp ℝ 2` are the `L²` exponent. -/
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

/-- **A NONZERO VECTOR IN THE KERNEL PUTS `0` IN THE SPECTRUM.** Injectivity is what a unit gives;
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

/-- **THE STOCHASTIC CONDITION** — every row of the kernel integrates to one. This is exactly the
normalisation `SliceTrace` records the slab kernel as NOT having.

DERIVED: the `1` is the total mass a stochastic row must carry. -/
def KernelStochastic (K : X → Y → ℝ) (ν : Measure Y) : Prop := ∀ x, (∫ y, K x y ∂ν) = 1

/-- **THE IMAGE OF THE CONSTANT OBSERVABLE IS THE ROW INTEGRAL.**

DERIVED: the `2`s are the `L²` exponent; `oneLp`'s `1` is the constant observable's value. -/
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

/-- **A STOCHASTIC KERNEL FIXES THE CONSTANT OBSERVABLE** — the constant is then an eigenvector with
eigenvalue one, i.e. a vacuum.

DERIVED: the `1`s are the stochastic normalisation and `oneLp`'s value; the `2`s are the `L²`
exponent. -/
theorem kernelCLM_oneLp_eq_oneLp (K : X → Y → ℝ) (C : ℝ) (hK : Measurable (Function.uncurry K))
    (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hst : KernelStochastic K ν) :
    kernelCLM K C hK hC0 hKb μ ν (oneLp ν) = oneLp μ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_kernelCLM_oneLp K C hK hC0 hKb μ ν,
    (memLp_const (1 : ℝ) (μ := μ) (p := 2)).coeFn_toLp] with x h1 h2
  rw [h1, show ((oneLp μ : Lp ℝ 2 μ) : X → ℝ) x = (1 : ℝ) from h2]
  exact hst x

/-- **A SUB-STOCHASTIC KERNEL MAKES THE CONSTANT A SUPERSOLUTION, NOT AN EIGENVECTOR.**

DERIVED: the `1`s are the kernel's cap and the bound asserted; the `2`s are the `L²` exponent. -/
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

/-- **THE ADJOINT OF THE SLAB TRANSFER OPERATOR**, identified concretely: it is the kernel operator
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

/-- **THE ONE ENDOMORPHISM IN SIGHT**: `T† ∘ T`, on `L²` of the slab at `t+1`. `slabTransfer` is not
an endomorphism at `n ≥ 2` and has no spectrum; this does.

DERIVED: the `1` in `t + 1` is `slabKernel`'s time step; the `2`s are the `L²` exponent. -/
noncomputable def slabNormal (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n) :
    Lp ℝ 2 (slabHaar (N := N) τ (t + 1)) →L[ℝ] Lp ℝ 2 (slabHaar (N := N) τ (t + 1)) :=
  (ContinuousLinearMap.adjoint (slabTransfer (d := d) (n := n) hN τ β t)).comp
    (slabTransfer (d := d) (n := n) hN τ β t)

/-- `slabNormal` is self-adjoint. **THIS IS FREE** — `isSelfAdjoint_adjointComp` has no premise, and
`adjointComp_zero_eq_zero` is the control. It is recorded because it is the only self-adjointness
available, not because it is evidence.

DERIVED: as `slabNormal`'s. -/
theorem isSelfAdjoint_slabNormal (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n) :
    IsSelfAdjoint (slabNormal (d := d) (n := n) hN τ β t) :=
  isSelfAdjoint_adjointComp _

/-- The quadratic form of `slabNormal` is the squared norm of the image. **Also free.**

DERIVED: the `2` in `^ 2` is the square of a norm. -/
theorem inner_slabNormal_self (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n)
    (f : Lp ℝ 2 (slabHaar (N := N) τ (t + 1))) :
    (inner ℝ f (slabNormal (d := d) (n := n) hN τ β t f) : ℝ)
      = ‖slabTransfer (d := d) (n := n) hN τ β t f‖ ^ 2 :=
  inner_adjointComp_self _ f

/-- `slabNormal` is a positive operator. **Also free.**

DERIVED: the `0` is the sign asserted. -/
theorem inner_slabNormal_self_nonneg (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n)
    (f : Lp ℝ 2 (slabHaar (N := N) τ (t + 1))) :
    0 ≤ (inner ℝ f (slabNormal (d := d) (n := n) hN τ β t f) : ℝ) :=
  inner_adjointComp_self_nonneg _ f

/-- **AT NONNEGATIVE COUPLING THE FORM OF `slabNormal` IS BOUNDED BY THE SQUARED NORM.** With the
previous theorem this places the form in `[0, ‖f‖²]`, which is the interval a contraction's
spectrum would have to live in. It is still not a spectral statement: no eigenvalue, no gap, and
Part 4 shows `0` can be in the spectrum with all of this holding.

DERIVED: the `2` in `^ 2` is a squared norm; the `0` of `hβ` is the sign of the coupling. -/
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
former carries the WHOLE intra-slice weight of slice `t` and the latter half at each argument. The
two lemmas below turn that into a theorem: the intra-slice factor does not read the second argument
at all. With `FiniteGram.symm` — a Gram kernel is symmetric — this is why the Osterwalder–Seiler
square cannot be pointed at `slabKernel` as it stands. -/

/-- **A SPATIAL PLAQUETTE OF SLICE `t` READS ONLY THE SPATIAL LINKS AT TIME `t`.**
`SliceTransfer.intra_links_mem` in the shape `action_on_congr_of_support` consumes — the sharper
support than `SliceTrace.intra_support`, which allows time `t+1` as well.

VACUOUS when `intraPlaq τ t = ∅`, which is the intra-slice half of `SlabKernelOperator`'s
`slabPlaqCount τ t = 0` regime (`d ≤ 1`).

DERIVED: no numeral. -/
theorem intra_support_slice (τ : Fin d) (t : Fin n) :
    ∀ q ∈ intraPlaq (d := d) (n := n) τ t, ∀ l ∈ (bd q).map Prod.fst,
      l ∈ sliceLinks (d := d) (n := n) τ t := by
  intro q hq l hl
  obtain ⟨lo, hlo, rfl⟩ := List.mem_map.mp hl
  exact intra_links_mem hq lo hlo

/-- **THE INTRA-SLICE ACTION OF A PATCHED CONFIGURATION DOES NOT READ THE SECOND SLAB.**

TRUE FOR TWO DIFFERENT REASONS, AND ONLY ONE OF THEM IS THE INTENDED ONE. At `n ≥ 2` it is the
intra-slice restriction: `intra_support_slice` confines the plaquettes to time `t`. At `n = 1`,
`t + 1 = t` and `SliceTrace.patch` resolves `s = t` first, so `B` is never consulted for ANY link
and the statement says nothing about the intra-slice cut. It is also EMPTY when
`intraPlaq τ t = ∅`, both sides being the empty sum.

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

/-- **THE SLAB KERNEL FACTORS, WITH ONE FACTOR BLIND TO THE SECOND ARGUMENT.** The first factor is
the intra-slice weight of slice `t`; it is written at the filler configuration and does not mention
`B` at all. The second factor is the temporal coupling.

This is the structural reason to doubt symmetry, stated as an identity rather than as prose.
**IT IS AN IDENTITY AND NOT A REFUTATION, AND ITS CONTENT IS EMPTY IN ALL THREE DEGENERATE
REGIMES:** at `β = 0`, at `slabPlaqCount τ t = 0` (i.e. `d ≤ 1`) and at `N = 1` the kernel is
constantly `1` (`SlabKernelOperator.slabKernel_beta_zero`,
`slabKernel_eq_one_of_plaqCount_zero`), so this reads `1 = 1 * 1`, both factors are constant, and
the kernel IS symmetric. A factor blind to the second argument is consistent with a constant
kernel; turning it into an asymmetry needs the coupling question `SliceTrace` names as open.

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

/-- **THE SLAB KERNEL PULLED BACK TO ONE SPACE** along a map `e` of the slab at `t` to the slab at
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

DERIVED: the `0` of `hN : N ≠ 0` is `wilsonDensity_nonneg`'s own hypothesis. -/
theorem abs_slabKernelPulled_le (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n)
    (e : (SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
        → (SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N)) :
    ∀ A A', |slabKernelPulled (N := N) τ β t e A A'| ≤ slabCap (d := d) (n := n) τ β t :=
  fun A A' => abs_slabKernel_le hN τ β t A (e A')

/-- **OPEN.** The Osterwalder–Seiler square condition at the Wilson slab kernel, read through an
identification `e` of the two slab configuration spaces.

**NOTHING IN THIS FILE PROVES IT AND NOTHING IN THE TREE DOES.** What the tree's reflection
machinery proves is `ReflectionStrong.wilsonGibbsReflForm`'s `form_nonneg` and
`Complete.wilson_reflection_positive_at_even` — nonnegativity of a GIBBS pairing of observables on
the FULL link configuration space, with the reflection `Θ` acting there and the Boltzmann weight
and partition function included. Neither is a Gram representation of `slabKernel`, which is a bare
Haar-measure kernel between two single slabs; `SlabKernelOperator`'s fourfold mismatch is the
statement of why, and `FiniteGram.symm` above adds a fifth REQUIREMENT that is about `slabKernel`
alone: a Gram kernel is symmetric, so this `Prop` entails `slabGramVia_symm`, and `slabKernel`'s
symmetry is itself undecided in the tree. `slabKernel_eq_intra_mul_inter` is the structural reason
to doubt it, not a refutation — the kernel is constant, hence symmetric, in the three degenerate
regimes, where this `Prop` therefore HOLDS (`finiteGram_one`).

DERIVED: no numeral. -/
def SlabGramVia (τ : Fin d) (β : ℝ) (t : Fin n)
    (e : (SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
        → (SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N)) : Prop :=
  FiniteGram (slabKernelPulled (N := N) τ β t e)

/-- **THE NECESSARY HALF OF THE REDUCTION.** If the square condition holds, the pulled-back kernel
is symmetric. Contrapositively, exhibiting an asymmetry refutes it.

DERIVED: no numeral. -/
theorem slabGramVia_symm {τ : Fin d} {β : ℝ} {t : Fin n}
    {e : (SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
        → (SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N)}
    (h : SlabGramVia (N := N) τ β t e) (A A' : SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N) :
    slabKernelPulled (N := N) τ β t e A A' = slabKernelPulled (N := N) τ β t e A' A :=
  FiniteGram.symm h A A'

/-- **THE SUFFICIENT HALF OF THE REDUCTION, PROVED.** The square condition gives operator positivity
of the pulled-back slab transfer operator on one space.

DERIVED: the `0` is the sign asserted; the `2`s are the `L²` exponent; `CA` is the caller's bound
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

/-- **THE SUFFICIENT HALF, CONSUMING `SlabGramVia` ITSELF.** This is the declaration that closes the
reduction: whoever proves the open `Prop` gets operator positivity of the pulled-back slab transfer
operator with nothing further to supply.

DERIVED: the `0` is the sign asserted; the `2`s are the `L²` exponent. -/
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
/-- **THE SLAB CAP IS EXACTLY ONE AT ZERO COUPLING**, so the Doeblin constant there is `1`.

DERIVED: the `0` is the coupling being set; the `1` is `Real.exp 0`. Neither is chosen. -/
theorem slabCap_beta_zero (τ : Fin d) (t : Fin n) :
    slabCap (d := d) (n := n) τ 0 t = 1 := by
  simp [slabCap]

/-- **AT ZERO COUPLING THE SLAB TRANSFER OPERATOR IS THE RANK-ONE AVERAGING MAP.**

DERIVED: the `0` is the coupling; the `1` in `t + 1` is `slabKernel`'s time step; the `2`s are the
`L²` exponent. -/
theorem slabTransfer_apply_of_beta_zero (hN : N ≠ 0) (τ : Fin d) (t : Fin n)
    (f : Lp ℝ 2 (slabHaar (N := N) τ (t + 1))) :
    slabTransfer (d := d) (n := n) hN τ 0 t f
      = (∫ B, (f : _ → ℝ) B ∂(slabHaar (N := N) τ (t + 1))) • oneLp (slabHaar (N := N) τ t) :=
  kernelCLM_apply_of_const _ _ _ _ _ _ _ (fun A B => slabKernel_beta_zero τ t A B) f

/-- **AT ZERO COUPLING `slabNormal` ANNIHILATES EVERY MEAN-ZERO VECTOR.**

DERIVED: the `0`s are the coupling, the vanishing mass and the zero vector. -/
theorem slabNormal_apply_eq_zero_of_beta_zero (hN : N ≠ 0) (τ : Fin d) (t : Fin n)
    (f : Lp ℝ 2 (slabHaar (N := N) τ (t + 1)))
    (hf0 : (∫ B, (f : _ → ℝ) B ∂(slabHaar (N := N) τ (t + 1))) = 0) :
    slabNormal (d := d) (n := n) hN τ 0 t f = 0 := by
  unfold slabNormal
  rw [ContinuousLinearMap.comp_apply, slabTransfer_apply_of_beta_zero hN τ t f, hf0, zero_smul,
    map_zero]

/-- **THE REFUTATION.** At zero coupling, with the Doeblin constant equal to `1` and `slabNormal`
self-adjoint, positive and a contraction, `0` is STILL in the spectrum as soon as a nonzero
mean-zero `L²` vector exists. A uniform positive lower bound on the kernel therefore does not
deliver `0 ∉ spectrum`, and `H = -log T` does not follow from it.

The hypothesis `h` is the only thing standing between this and an unconditional statement, and it
fails exactly when the slab configuration space carries no nonconstant `L²` function — which is the
`N = 1` regime `SlabKernelOperator`'s header names, where `SU N` is trivial and `L²` is one
dimensional. **It is not discharged here and the tree does not discharge it**: exhibiting a
nonconstant slab observable is the same open question `GNSHilbert`'s header records.

DERIVED: the `0`s are the coupling and the spectral point; the `2` is the `L²` exponent. -/
theorem zero_mem_spectrum_slabNormal_of_beta_zero (hN : N ≠ 0) (τ : Fin d) (t : Fin n)
    (h : ∃ f : Lp ℝ 2 (slabHaar (N := N) τ (t + 1)), f ≠ 0
        ∧ (∫ B, (f : _ → ℝ) B ∂(slabHaar (N := N) τ (t + 1))) = 0) :
    (0 : ℝ) ∈ spectrum ℝ (slabNormal (d := d) (n := n) hN τ 0 t) := by
  obtain ⟨f, hf, hf0⟩ := h
  exact zero_mem_spectrum_of_apply_eq_zero _ f hf
    (slabNormal_apply_eq_zero_of_beta_zero hN τ t f hf0)

/-! ### The vacuum at the Wilson slab kernel -/

/-- **AT NONNEGATIVE COUPLING THE CONSTANT OBSERVABLE IS A SUPERSOLUTION.** `T 1 ≤ 1` almost
everywhere. With `slabCap_inv_le_slabTransfer_oneLp`, which bounds the same image below by
`slabCap⁻¹ > 0`, the constant is moved into `[slabCap⁻¹, 1]`. **That interval contains `1`, so
these two bounds do not decide whether the constant is an eigenvector, and this file does not decide
it at any `β > 0`.** What would decide it is `KernelStochastic`, proved here only at `β = 0`.

DERIVED: the `1`s are the kernel's cap at `0 ≤ β` and the bound asserted; the `0` of `hβ` is the
sign of the coupling. -/
theorem slabTransfer_oneLp_le_one (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (hβ : 0 ≤ β) (t : Fin n) :
    ∀ᵐ A ∂(slabHaar (N := N) τ t),
      ((slabTransfer (d := d) (n := n) hN τ β t (oneLp (slabHaar (N := N) τ (t + 1)))
        : Lp ℝ 2 (slabHaar (N := N) τ t)) : _ → ℝ) A ≤ 1 :=
  kernelCLM_oneLp_le_one _ _ _ _ _ _ _
    (fun A B => le_trans (le_abs_self _) (abs_slabKernel_le_one hN τ β hβ t A B))

/-- **THE CONSTANT OBSERVABLE IS MOVED OFF ZERO, UNIFORMLY.** The Wilson instance of
`SlabKernelOperator.le_kernelCLM_one` at the slab kernel's own Doeblin constant. With
`slabTransfer_oneLp_le_one` this places `T 1` in `[slabCap⁻¹, 1]` at `0 ≤ β`. **That interval
contains `1`, so it does NOT decide whether the constant is an eigenvector**; what decides it is
`KernelStochastic`, which is proved only at `β = 0`.

DERIVED: the `1` in `t + 1` is `slabKernel`'s time step; `slabCap⁻¹` is `slabWeight_bounds`'s own
lower bound, not a chosen level. -/
theorem slabCap_inv_le_slabTransfer_oneLp (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n) :
    ∀ᵐ A ∂(slabHaar (N := N) τ t),
      (slabCap (d := d) (n := n) τ β t)⁻¹
        ≤ ((slabTransfer (d := d) (n := n) hN τ β t (oneLp (slabHaar (N := N) τ (t + 1)))
          : Lp ℝ 2 (slabHaar (N := N) τ t)) : _ → ℝ) A :=
  le_kernelCLM_one _ _ _ _ _ _ _ (slabCap_inv_le_slabKernel hN τ β t)

/-- **AT ZERO COUPLING THE SLAB KERNEL IS STOCHASTIC** — the degenerate positive control for the
normalisation `SliceTrace` records as absent.

DERIVED: the `0` is the coupling; the `1` is the total mass of a probability measure. -/
theorem slabKernelStochastic_beta_zero (τ : Fin d) (t : Fin n) :
    KernelStochastic (slabKernel (N := N) τ 0 t) (slabHaar (N := N) τ (t + 1)) := by
  intro A
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun B => slabKernel_beta_zero τ t A B))]
  simp

/-- **AT ZERO COUPLING THE CONSTANT OBSERVABLE IS AN EIGENVECTOR WITH EIGENVALUE ONE.** This is the
ONLY regime in which the tree proves `T Ω = Ω`, and it is a degenerate one: the operator there is
the rank-one averaging map (`slabTransfer_apply_of_beta_zero`), and the ONE endomorphism in sight,
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
