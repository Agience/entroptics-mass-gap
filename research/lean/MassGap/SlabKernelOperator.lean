import Mathlib
import MassGap.SliceTrace
import MassGap.PlaqVariance

/-!
# MassGap.SlabKernelOperator — the slab kernel as a bounded operator on `L²`

This file turns a bounded jointly measurable kernel between two probability spaces into a
`ContinuousLinearMap` between the corresponding `L²` spaces, and defines the per-slab Haar measure
`slabHaar` on the slab configuration spaces of `SliceTrace`.

The argument uses no integral-operator development: no Schatten, Hilbert–Schmidt or trace class is
named anywhere below. What it uses is that each configuration space is a finite power of a compact
group carrying a probability measure and that the kernel is bounded, after which the estimate is
Cauchy–Schwarz in `MeasureTheory.L2`. The external lemmas are `MemLp.of_bound`,
`Lp.norm_le_of_ae_bound`, `abs_real_inner_le_norm`, `L2.inner_def` and
`StronglyMeasurable.integral_prod_right'`; the remainder is integral algebra (`integral_congr_ae`,
`integral_add`, `integral_const_mul`, `integral_mono`, `integral_nonneg_of_ae`) and the `Lp`
coercion lemmas. The file imports all of Mathlib.

## Part 1, abstract

For measurable spaces `X`, `Y` with probability measures `μ`, `ν` and a kernel `K : X → Y → ℝ` that
is jointly measurable and satisfies `|K x y| ≤ C`:

* `abs_kernelFun_le` — for `f` in `L²(ν)`, `|∫ K x y f y dν| ≤ C ‖f‖₂` at every `x`, not merely at
  almost every `x`. The kernel row is itself an `L²(ν)` vector of norm at most `C`
  (`Lp.norm_le_of_ae_bound` at a probability measure), and `abs_real_inner_le_norm` is
  Cauchy–Schwarz. The image is therefore a bounded function.
* `kernelCLM` — the induced map `L²(ν) →L[ℝ] L²(μ)`, with `norm_kernelCLM_le : ‖kernelCLM‖ ≤ C`.
* `norm_kernelCLM_le_of_bound` — the operator norm is at most any uniform bound on the kernel, not
  only the constant the operator was constructed with, so a sharper bound applies to an operator
  already built.
* `kernelCLM_nonneg` — a nonnegative kernel gives a positivity-preserving operator: a nonnegative
  input has a nonnegative image.
* `kernelCLM_ne_zero` — if `K` is bounded below by some `ε > 0` then the operator is not the zero
  operator. Its value on the constant observable is bounded below by `ε` (`le_kernelCLM_one`), and a
  probability measure's almost-everywhere filter is not the bottom filter. This also excludes a
  trivial domain.

Measurability of `x ↦ ∫ K x y f y dν` is `StronglyMeasurable.integral_prod_right'`, the only
Fubini-flavoured input.

## Part 2, the slab measure

* `slabHaar τ t` — the product Haar measure on one slab's links, with
  `isProbabilityMeasure_slabHaar`.
* `slabVol_eq_pi_slabHaar` — `SliceTrace.slabVol` is the `Fin n`-indexed product of the `slabHaar`.
  It is a `rfl`.
* `continuous_regroup_patch` — the map from a pair of slab configurations at `t` and `t + 1` to the
  regrouped patched full configuration is continuous. Continuity passes through `patch` and `regroup`
  because the branch tests in `patch` read the time index of the link being served and not the
  configuration.

## Scope

* No symmetry and no operator positivity. `kernelCLM_nonneg` is positivity preservation — a
  nonnegative function has a nonnegative image — which is a different statement from `0 ≤ ⟨x, T x⟩`,
  the shape of `GNSHilbert.PositiveTransfer`.
* No spectrum, no gap and no Hamiltonian. The results are norm bounds; `-log T` is not built.

Foundational footprint only (`#print axioms` at the end).
Build: `python research/code/lean_build.py build MassGap.SlabKernelOperator`.
-/

namespace MassGap.SlabKernelOperator

open MeasureTheory
open MassGap MassGap.SliceTrace MassGap.WilsonAction MassGap.WilsonHypercubic
open MassGap.CompactGauge MassGap.WilsonLattice

/-! ## Part 1 — a bounded measurable kernel on probability spaces induces a bounded operator

Nothing in this part mentions the lattice. The standing assumptions are that both measures are
probability measures — finiteness is what the estimates use, and the unit normalisation removes the
measure factors from the constants — and that the kernel is bounded and jointly measurable. -/

section Abstract

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The kernel acting on a function: `kernelFun K ν f x = ∫ y, K x y * f y ∂ν`. No hypothesis on
`K`, `ν` or `f` is required to write it down; integrability is supplied by the callers.

DERIVED: no numeral. -/
noncomputable def kernelFun (K : X → Y → ℝ) (ν : Measure Y) (f : Y → ℝ) (x : X) : ℝ :=
  ∫ y, K x y * f y ∂ν

variable {K : X → Y → ℝ} {C : ℝ} {μ : Measure X} {ν : Measure Y}

/-- A row of a bounded kernel is an `L²` vector. Given joint measurability of `K` and the uniform
bound `|K x y| ≤ C`, the function `K x` is in `MemLp _ 2 ν` at every `x`. The measure is only
required to be finite here, not a probability measure; the proof is `MemLp.of_bound`.

DERIVED: the `2` is the `L²` exponent — the one exponent at which Mathlib's `Lp` carries an inner
product, which is what Cauchy–Schwarz is used through. It is not a chosen parameter. -/
theorem memLp_row (hK : Measurable (Function.uncurry K)) (hKb : ∀ x y, |K x y| ≤ C)
    (ν : Measure Y) [IsFiniteMeasure ν] (x : X) : MemLp (K x) 2 ν := by
  have hm : Measurable (K x) := hK.comp measurable_prodMk_left
  refine MemLp.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall (fun y => ?_))
  simpa [Real.norm_eq_abs] using hKb x y

/-- The kernel row times an integrable function is integrable. `f` is assumed integrable for `ν` and
`K` bounded by `C`, and the product is bounded times integrable (`Integrable.bdd_mul`). No
finiteness assumption on `ν` is needed.

DERIVED: no numeral. -/
theorem integrable_row_mul (hK : Measurable (Function.uncurry K)) (hKb : ∀ x y, |K x y| ≤ C)
    {f : Y → ℝ} (hf : Integrable f ν) (x : X) :
    Integrable (fun y => K x y * f y) ν := by
  have hm : Measurable (K x) := hK.comp measurable_prodMk_left
  refine hf.bdd_mul (c := C) hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun y => ?_))
  simpa [Real.norm_eq_abs] using hKb x y

/-- The pointwise Cauchy–Schwarz bound: `|kernelFun K ν f x| ≤ C * ‖f‖` at every `x`, not merely at
almost every `x`. The kernel row is an `L²(ν)` vector of norm at most `C` — this is where `ν` being
a probability measure is used, since `Lp.norm_le_of_ae_bound` otherwise carries a factor of the
total mass — the pairing with `f` is the `L²` inner product, and `abs_real_inner_le_norm` bounds it.

DERIVED: the `2` is the `L²` exponent, as in `memLp_row`. The `0` is the sign tested in
`hC0 : 0 ≤ C`, required by `Lp.norm_le_of_ae_bound`. `C` is the caller's kernel bound. -/
theorem abs_kernelFun_le (hK : Measurable (Function.uncurry K)) (hC0 : 0 ≤ C)
    (hKb : ∀ x y, |K x y| ≤ C) [IsProbabilityMeasure ν] (f : Lp ℝ 2 ν) (x : X) :
    |kernelFun K ν (f : Y → ℝ) x| ≤ C * ‖f‖ := by
  have hrow : MemLp (K x) 2 ν := memLp_row hK hKb ν x
  set R : Lp ℝ 2 ν := hrow.toLp (K x) with hR
  have hcoe : (R : Y → ℝ) =ᵐ[ν] K x := hrow.coeFn_toLp
  have hinner : (inner ℝ R f : ℝ) = kernelFun K ν (f : Y → ℝ) x := by
    rw [L2.inner_def]
    unfold kernelFun
    refine integral_congr_ae ?_
    filter_upwards [hcoe] with y hy
    have hmul : (inner ℝ ((R : Y → ℝ) y) ((f : Y → ℝ) y) : ℝ)
        = (R : Y → ℝ) y * (f : Y → ℝ) y := by
      rw [RCLike.inner_apply]; simp [mul_comm]
    rw [hmul, hy]
  have hnormR : ‖R‖ ≤ C := by
    have hb : ∀ᵐ y ∂ν, ‖(R : Y → ℝ) y‖ ≤ C := by
      filter_upwards [hcoe] with y hy
      rw [hy]
      simpa [Real.norm_eq_abs] using hKb x y
    have h := Lp.norm_le_of_ae_bound (f := R) hC0 hb
    have hmu : measureUnivNNReal ν = 1 := by simp [measureUnivNNReal]
    rw [hmu] at h
    simpa using h
  calc |kernelFun K ν (f : Y → ℝ) x| = |(inner ℝ R f : ℝ)| := by rw [hinner]
    _ ≤ ‖R‖ * ‖f‖ := abs_real_inner_le_norm _ _
    _ ≤ C * ‖f‖ := mul_le_mul_of_nonneg_right hnormR (norm_nonneg f)

/-- The image `x ↦ ∫ K x y * f y ∂ν` is strongly measurable, from
`StronglyMeasurable.integral_prod_right'`. This needs joint measurability of `K` and `SFinite ν`,
and it is the only Fubini-flavoured input in the file.

DERIVED: the `2` is the `L²` exponent. -/
theorem stronglyMeasurable_kernelFun (hK : Measurable (Function.uncurry K))
    [SFinite ν] (f : Lp ℝ 2 ν) : StronglyMeasurable (kernelFun K ν (f : Y → ℝ)) :=
  StronglyMeasurable.integral_prod_right'
    (hK.stronglyMeasurable.mul ((Lp.stronglyMeasurable f).comp_measurable measurable_snd))

/-- The image is in `L²(μ)`: it is a strongly measurable function bounded by `C * ‖f‖` on a finite
measure space. The bound is `abs_kernelFun_le`'s, so it is uniform in `x`. `μ` need only be finite;
`ν` must be a probability measure, because `abs_kernelFun_le` requires that.

DERIVED: the `2`s are the `L²` exponent. The `0` is the sign tested in `hC0 : 0 ≤ C`. -/
theorem memLp_kernelFun (hK : Measurable (Function.uncurry K)) (hC0 : 0 ≤ C)
    (hKb : ∀ x y, |K x y| ≤ C) (μ : Measure X) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (f : Lp ℝ 2 ν) : MemLp (kernelFun K ν (f : Y → ℝ)) 2 μ := by
  refine MemLp.of_bound (stronglyMeasurable_kernelFun hK f).aestronglyMeasurable (C * ‖f‖)
    (Filter.Eventually.of_forall (fun x => ?_))
  simpa [Real.norm_eq_abs] using abs_kernelFun_le hK hC0 hKb f x

/-- The operator as a bare `LinearMap` `Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 μ`. It carries the kernel, the bound
`C` and the two proofs as explicit arguments, so two different bounds give two different terms.
Additivity and homogeneity are linearity of the integral, moved across the almost-everywhere classes
with `Lp.ext`; integrability of each row product comes from `integrable_row_mul`. Both measures are
probability measures here.

DERIVED: the `2`s are the `L²` exponent. The `0` is the sign tested in `hC0 : 0 ≤ C`. -/
noncomputable def kernelLM (K : X → Y → ℝ) (C : ℝ) (hK : Measurable (Function.uncurry K))
    (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 μ where
  toFun f := (memLp_kernelFun hK hC0 hKb μ f).toLp _
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [(memLp_kernelFun hK hC0 hKb μ (f + g)).coeFn_toLp,
      Lp.coeFn_add ((memLp_kernelFun hK hC0 hKb μ f).toLp _)
        ((memLp_kernelFun hK hC0 hKb μ g).toLp _),
      (memLp_kernelFun hK hC0 hKb μ f).coeFn_toLp,
      (memLp_kernelFun hK hC0 hKb μ g).coeFn_toLp] with x h1 h2 h3 h4
    rw [h1, h2]
    simp only [Pi.add_apply]
    rw [h3, h4]
    have hf : Integrable (fun y => K x y * (f : Y → ℝ) y) ν :=
      integrable_row_mul hK hKb ((Lp.memLp f).integrable one_le_two) x
    have hg : Integrable (fun y => K x y * (g : Y → ℝ) y) ν :=
      integrable_row_mul hK hKb ((Lp.memLp g).integrable one_le_two) x
    unfold kernelFun
    rw [← integral_add hf hg]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add f g] with y hy
    rw [hy]
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [(memLp_kernelFun hK hC0 hKb μ (c • f)).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_kernelFun hK hC0 hKb μ f).toLp _),
      (memLp_kernelFun hK hC0 hKb μ f).coeFn_toLp] with x h1 h2 h3
    rw [RingHom.id_apply]
    rw [h1, h2]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h3]
    unfold kernelFun
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c f] with y hy
    rw [hy]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- The linear map's value, as a function, agrees `μ`-almost everywhere with `kernelFun K ν f`. It
is `MemLp.coeFn_toLp` at `memLp_kernelFun`, and it is what every later `filter_upwards` rewrites
through.

DERIVED: the `2`s are the `L²` exponent. The `0` is the sign tested in `hC0 : 0 ≤ C`. -/
theorem coeFn_kernelLM (hK : Measurable (Function.uncurry K)) (hC0 : 0 ≤ C)
    (hKb : ∀ x y, |K x y| ≤ C) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (f : Lp ℝ 2 ν) :
    ((kernelLM K C hK hC0 hKb μ ν f : Lp ℝ 2 μ) : X → ℝ)
      =ᵐ[μ] kernelFun K ν (f : Y → ℝ) :=
  (memLp_kernelFun hK hC0 hKb μ f).coeFn_toLp

/-- The operator as a `ContinuousLinearMap` `Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 μ`, built from `kernelLM` by
`LinearMap.mkContinuous` with the constant `C`. Continuity comes from the pointwise bound
`abs_kernelFun_le` promoted to an `L²(μ)` norm bound by `Lp.norm_le_of_ae_bound`, where `μ` being a
probability measure removes the total-mass factor.

DERIVED: the `2`s are the `L²` exponent; the `0` is the sign tested in `hC0 : 0 ≤ C`. `C` is the
caller's kernel bound. -/
noncomputable def kernelCLM (K : X → Y → ℝ) (C : ℝ) (hK : Measurable (Function.uncurry K))
    (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous (kernelLM K C hK hC0 hKb μ ν) C (fun f => by
    have hb : ∀ᵐ x ∂μ, ‖((kernelLM K C hK hC0 hKb μ ν f : Lp ℝ 2 μ) : X → ℝ) x‖ ≤ C * ‖f‖ := by
      filter_upwards [coeFn_kernelLM hK hC0 hKb μ ν f] with x hx
      rw [hx]
      simpa [Real.norm_eq_abs] using abs_kernelFun_le hK hC0 hKb f x
    have h := Lp.norm_le_of_ae_bound (f := kernelLM K C hK hC0 hKb μ ν f)
      (mul_nonneg hC0 (norm_nonneg f)) hb
    have hmu : measureUnivNNReal μ = 1 := by simp [measureUnivNNReal]
    rw [hmu] at h
    simpa using h)

/-- The operator norm of `kernelCLM` is at most the constant `C` it was built with. It is
`LinearMap.mkContinuous_norm_le` applied to that construction.

DERIVED: the statement's only numeral is the `0` in `hC0 : 0 ≤ C`; the `2`s in the operator's type
are the `L²` exponent. `C` is the caller's kernel bound. -/
theorem norm_kernelCLM_le (K : X → Y → ℝ) (C : ℝ) (hK : Measurable (Function.uncurry K))
    (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ‖kernelCLM K C hK hC0 hKb μ ν‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC0 _

/-- The operator's value, as a function, agrees `μ`-almost everywhere with `kernelFun K ν f`. It is
`coeFn_kernelLM` transported along the definition of `kernelCLM`.

DERIVED: the `2`s are the `L²` exponent. The `0` is the sign tested in `hC0 : 0 ≤ C`. -/
theorem coeFn_kernelCLM (K : X → Y → ℝ) (C : ℝ) (hK : Measurable (Function.uncurry K))
    (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (f : Lp ℝ 2 ν) :
    ((kernelCLM K C hK hC0 hKb μ ν f : Lp ℝ 2 μ) : X → ℝ)
      =ᵐ[μ] kernelFun K ν (f : Y → ℝ) :=
  coeFn_kernelLM hK hC0 hKb μ ν f

/-- The operator norm of `kernelCLM K C …` is at most any second uniform bound `C'` on the same
kernel, with `0 ≤ C'`. `norm_kernelCLM_le` is this at `C' = C`. The separate statement lets a
sharper bound be applied to an operator already constructed with a weaker one. The proof is
`ContinuousLinearMap.opNorm_le_bound` on `abs_kernelFun_le` restated at `C'`.

DERIVED: the `2`s are the `L²` exponent; the `0`s are the signs tested in `hC0 : 0 ≤ C` and
`hC'0 : 0 ≤ C'`. `C` and `C'` are the caller's kernel bounds. -/
theorem norm_kernelCLM_le_of_bound (K : X → Y → ℝ) (C : ℝ) (hK : Measurable (Function.uncurry K))
    (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {C' : ℝ} (hC'0 : 0 ≤ C')
    (hKb' : ∀ x y, |K x y| ≤ C') :
    ‖kernelCLM K C hK hC0 hKb μ ν‖ ≤ C' := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC'0 (fun f => ?_)
  have hb : ∀ᵐ x ∂μ,
      ‖((kernelCLM K C hK hC0 hKb μ ν f : Lp ℝ 2 μ) : X → ℝ) x‖ ≤ C' * ‖f‖ := by
    filter_upwards [coeFn_kernelCLM K C hK hC0 hKb μ ν f] with x hx
    rw [hx]
    simpa [Real.norm_eq_abs] using abs_kernelFun_le hK hC'0 hKb' f x
  have h := Lp.norm_le_of_ae_bound (f := kernelCLM K C hK hC0 hKb μ ν f)
    (mul_nonneg hC'0 (norm_nonneg f)) hb
  have hmu : measureUnivNNReal μ = 1 := by simp [measureUnivNNReal]
  rw [hmu] at h
  simpa using h

/-! ### Anti-vacuity

An operator that is zero, or bounded only because its domain is trivial, satisfies everything above.
The statements below rule both out. They take a strictly positive lower bound on the kernel, which
is an extra hypothesis and does not follow from the upper bound. -/

/-- The constant function `1` as an `L²(ν)` vector, via `memLp_const` at a probability measure. It
is the test vector used by `le_kernelCLM_one` and `kernelCLM_ne_zero`.

DERIVED: the `1` is the constant function's value, not a level. The `2` is the `L²` exponent. -/
noncomputable def oneLp (ν : Measure Y) [IsProbabilityMeasure ν] : Lp ℝ 2 ν :=
  (memLp_const (1 : ℝ)).toLp _

/-- With a pointwise nonnegative kernel, an almost-everywhere nonnegative `f` has an
almost-everywhere nonnegative image, by `integral_nonneg_of_ae` under the coercion lemma
`coeFn_kernelCLM`. This is positivity preservation on functions, a different statement from
positivity of the operator in the sense of `Transfer.PositiveTransfer` (`0 ≤ ⟨x, T x⟩`), which is
not claimed.

DERIVED: the `0`s are the signs tested — in `hC0 : 0 ≤ C`, in `hKpos`, in the hypothesis on `f` and
in the conclusion. The `2`s are the `L²` exponent. -/
theorem kernelCLM_nonneg (K : X → Y → ℝ) (C : ℝ) (hK : Measurable (Function.uncurry K))
    (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hKpos : ∀ x y, 0 ≤ K x y)
    (f : Lp ℝ 2 ν) (hf : 0 ≤ᵐ[ν] (f : Y → ℝ)) :
    0 ≤ᵐ[μ] ((kernelCLM K C hK hC0 hKb μ ν f : Lp ℝ 2 μ) : X → ℝ) := by
  filter_upwards [coeFn_kernelCLM K C hK hC0 hKb μ ν f] with x hx
  rw [hx]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hf] with y hy
  exact mul_nonneg (hKpos x y) hy

/-- Under a uniform lower bound `ε ≤ K x y`, the image of `oneLp ν` is at least `ε` at
`μ`-almost every `x`. The kernel action at `oneLp` is `∫ y, K x y ∂ν` and `integral_mono` against
the constant `ε` gives the bound; `ν` being a probability measure is what makes `∫ ε ∂ν = ε`. No
sign hypothesis is placed on `ε` here.

DERIVED: the `1` is `oneLp`'s constant, and it is also the total mass of `ν` that turns `∫ ε ∂ν`
into `ε`; the `0` is the sign tested in `hC0 : 0 ≤ C`. The `2`s are the `L²` exponent. `ε` is the
caller's lower bound. -/
theorem le_kernelCLM_one (K : X → Y → ℝ) (C : ℝ) (hK : Measurable (Function.uncurry K))
    (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {ε : ℝ} (hKlb : ∀ x y, ε ≤ K x y) :
    ∀ᵐ x ∂μ, ε ≤ ((kernelCLM K C hK hC0 hKb μ ν (oneLp ν) : Lp ℝ 2 μ) : X → ℝ) x := by
  filter_upwards [coeFn_kernelCLM K C hK hC0 hKb μ ν (oneLp ν)] with x hx
  rw [hx]
  have hK1 : kernelFun K ν ((oneLp ν : Lp ℝ 2 ν) : Y → ℝ) x = ∫ y, K x y ∂ν := by
    unfold kernelFun
    refine integral_congr_ae ?_
    filter_upwards [(memLp_const (1 : ℝ) (μ := ν) (p := 2)).coeFn_toLp] with y hy
    rw [show ((oneLp ν : Lp ℝ 2 ν) : Y → ℝ) y = (1 : ℝ) from hy]
    ring
  rw [hK1]
  have hint : Integrable (K x) ν := (memLp_row hK hKb ν x).integrable one_le_two
  have hmono : ∫ _y : Y, ε ∂ν ≤ ∫ y, K x y ∂ν :=
    integral_mono (integrable_const ε) hint (fun y => hKlb x y)
  simpa using hmono

/-- With a uniform lower bound `ε ≤ K x y` at some `ε > 0`, `kernelCLM` is not the zero operator.
If it were, its value at `oneLp ν` would vanish `μ`-almost everywhere, while `le_kernelCLM_one`
puts that value at or above `ε` on a set of full measure; a probability measure's
almost-everywhere filter is not the bottom filter, so the two cannot both hold. This also excludes a
trivial domain, since the zero space admits only the zero operator.

DERIVED: the `0`s are the sign tested in `hC0 : 0 ≤ C`, the strict sign in `hε : 0 < ε`, and the
operator being excluded in `≠ 0`. The `2`s are the `L²` exponent. `ε` is the caller's. -/
theorem kernelCLM_ne_zero (K : X → Y → ℝ) (C : ℝ) (hK : Measurable (Function.uncurry K))
    (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {ε : ℝ} (hε : 0 < ε)
    (hKlb : ∀ x y, ε ≤ K x y) :
    kernelCLM K C hK hC0 hKb μ ν ≠ 0 := by
  intro hzero
  have hval : (kernelCLM K C hK hC0 hKb μ ν) (oneLp ν) = 0 := by rw [hzero]; rfl
  have hae : ∀ᵐ x ∂μ, ((kernelCLM K C hK hC0 hKb μ ν (oneLp ν) : Lp ℝ 2 μ) : X → ℝ) x = 0 := by
    rw [hval]
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x _
    simp
  have hcontra : ∀ᵐ _x ∂μ, False := by
    filter_upwards [hae, le_kernelCLM_one K C hK hC0 hKb μ ν hKlb] with x h0 hlb
    rw [h0] at hlb
    exact absurd hlb (not_le.mpr hε)
  exact hcontra.exists.elim (fun _ h => h)

end Abstract

/-! ## Part 2 — the Wilson slab kernel

The configuration of the links at time `t` and the configuration of the links at time `t + 1` each
range over a finite product of copies of `SU N`, which is compact, and each carries the product of the
probability Haar measure. -/

section Wilson

variable {d n N : ℕ} [NeZero n]

/-- The product Haar measure on one slab's links: `Measure.pi` of `probHaar (SU N)` over
`SlabIdx τ t`. `SliceTrace.slabVol` is the product of these over all times; this is the single
factor, and it is what a kernel between two slabs integrates against.

DERIVED: no numeral. -/
noncomputable def slabHaar (τ : Fin d) (t : Fin n) :
    Measure (SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N) :=
  Measure.pi fun _ => probHaar (MassGap.SUN.SU N)

/-- `slabHaar` is a probability measure, being a finite product of probability Haar measures. It
discharges the `IsProbabilityMeasure` side conditions that Part 1 imposes on kernels between slabs,
so it is listed in the axiom footprint block with the rest.

DERIVED: no numeral. -/
instance isProbabilityMeasure_slabHaar (τ : Fin d) (t : Fin n) :
    IsProbabilityMeasure (slabHaar (N := N) τ t) := by
  unfold slabHaar; infer_instance

omit [NeZero n] in
/-- `slabVol τ` is the `Fin n`-indexed product of the `slabHaar τ t`, so `slabHaar τ t` is exactly
one factor of it. The proof is `rfl`. The `[NeZero n]` instance is omitted for this declaration.

DERIVED: no numeral. -/
theorem slabVol_eq_pi_slabHaar (τ : Fin d) :
    slabVol (d := d) (n := n) (N := N) τ
      = Measure.pi fun t : Fin n => slabHaar (N := N) τ t := rfl

/-- The map sending a pair of slab configurations at `t` and `t + 1` to the regrouped patched full
configuration is continuous. `patch`'s branch tests read the time of the link being served and not
the configuration, so each coordinate of the result is a coordinate projection of one of the two
arguments or the constant identity, and `continuous_pi` closes it.

DERIVED: the `1` in `t + 1` is the time step — one slice on, `Fin n` addition, which wraps. It is
inherited from `SliceTrace`, not chosen here. -/
theorem continuous_regroup_patch (τ : Fin d) (t : Fin n) :
    Continuous (fun p : ((SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N) ×
        (SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N)) =>
      regroup (timeOf τ) (patch (N := N) τ p.1 p.2)) := by
  refine continuous_pi (fun l => ?_)
  simp only [regroup, patch]
  split_ifs with h1 h2
  · exact (continuous_apply _).comp continuous_fst
  · exact (continuous_apply _).comp continuous_snd
  · exact continuous_const

end Wilson

/-! ## Axiom footprints -/

#print axioms kernelFun
#print axioms memLp_row
#print axioms integrable_row_mul
#print axioms abs_kernelFun_le
#print axioms stronglyMeasurable_kernelFun
#print axioms memLp_kernelFun
#print axioms kernelLM
#print axioms coeFn_kernelLM
#print axioms kernelCLM
#print axioms norm_kernelCLM_le
#print axioms norm_kernelCLM_le_of_bound
#print axioms coeFn_kernelCLM
#print axioms oneLp
#print axioms kernelCLM_nonneg
#print axioms le_kernelCLM_one
#print axioms kernelCLM_ne_zero
#print axioms slabHaar
#print axioms isProbabilityMeasure_slabHaar
#print axioms slabVol_eq_pi_slabHaar
#print axioms continuous_regroup_patch

end MassGap.SlabKernelOperator
