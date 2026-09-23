import Mathlib
import MassGap.SliceTrace
import MassGap.PlaqVariance

/-!
# MassGap.SlabKernelOperator — the slab kernel as a bounded operator on `L²`

`SliceTrace` defines `slabKernel`, the slice-to-slice kernel whose cyclic integral is the partition
function. This file turns a bounded jointly measurable kernel between two probability spaces into a
`ContinuousLinearMap` between the corresponding `L²` spaces, and applies that to `slabKernel`.

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

## Part 2, at the Wilson slab kernel

`slabKernel τ β t` is `SliceTrace`'s object.

* `continuous_slabKernel_uncurry` — it is jointly continuous in its two slab arguments, hence
  jointly measurable (`measurable_slabKernel_uncurry`). Continuity passes through `patch` and
  `regroup` because the branch tests in `patch` read the time index of the link being served and not
  the configuration.
* `abs_slabKernel_le` / `slabCap_inv_le_slabKernel` — it lies between `exp (-|β| · 2 · P)` and
  `exp (|β| · 2 · P)`, where `P = slabPlaqCount τ t` counts exactly the plaquettes `slabWeight` sums
  over. The inputs are `WilsonAction.wilsonDensity_nonneg` and `wilsonDensity_le_two`. `[0, 2P]`
  contains the slab energy and is not its range: the upper end needs every plaquette holonomy at
  `-I`, which for odd `N` is not in `SU N`.
* `abs_slabKernel_le_one` and `norm_slabTransfer_le_one` — at `0 ≤ β` the operator is a contraction.
  `slabWeight` is `e^{-βS}` with `S ≥ 0`, so at nonnegative coupling it is at most `1`, and
  `norm_kernelCLM_le_of_bound` carries that to the operator already built. `slabCap` discards the
  sign of `β` and is exponentially larger in the slab's plaquette count, hence in the volume.
* `slabTransfer` — the `ContinuousLinearMap` `L²(slab t+1) →L[ℝ] L²(slab t)` induced by
  `slabKernel τ β t`, with `norm_slabTransfer_le`, `norm_slabTransfer_le_one`,
  `slabTransfer_nonneg` and `slabTransfer_ne_zero`.
* `slabVol_eq_pi_slabHaar` — the per-slab measure used here is the factor of `SliceTrace.slabVol`
  that `partition_eq_cycleIntegral` integrates against. It is a `rfl`, and it is the only statement
  in this file relating the operator to the partition function.

## Parameter values at which the statements are empty or collapse

* `slabPlaqCount τ t = 0` — `slabKernel_eq_one_of_plaqCount_zero`: the kernel is constantly `1`, so
  `slabTransfer` is the rank-one averaging map `f ↦ (∫ f) · 1`. This is the case at `d ≤ 1`, where
  `intraPlaq` is empty and every plaquette of `interPlaq` is diagonal, so the filter empties it.
* `β = 0` — `slabKernel_beta_zero`: the same collapse and the same rank-one operator.
* `N = 1` — `SimpleGroup.subsingleton_SU_one` makes the gauge group trivial, so every holonomy is
  `1`, `wilsonDensity` is `0` and the kernel is constantly `1`. The configuration space is a single
  point and `L²` is one dimensional. `hN : N ≠ 0` does not exclude this, and it is not formalised
  here.
* `d = 0` — `Fin 0` is empty, so there is no `τ` and every Part 2 statement is an empty
  quantification.
* `n = 1` — `t + 1 = t` in `Fin 1`, so the two slab index types coincide and `slabTransfer` is an
  endomorphism; `SliceTrace` records that `slabKernel` there ignores its second argument.

## Scope

* `slabTransfer` is an endomorphism only at `n = 1`. For `n ≥ 2` the types `SlabIdx τ t` and
  `SlabIdx τ (t+1)` are distinct, so it is a bounded map between two different Hilbert spaces. They
  are canonically isomorphic by time translation, but no such identification is made here, and
  nothing below mentions a power or a composite of `slabTransfer`.
  `SliceTrace.cycle_kernel_prod_split` exhibits the cut of the cyclic integral.
* No symmetry and no operator positivity. `SliceTrace`'s header lists the differences between
  `slabKernel` and `SliceTransfer.transferKernel`; the symmetry and positive-semidefiniteness proved
  of the latter are not transported here. `kernelCLM_nonneg` is positivity preservation — a
  nonnegative function has a nonnegative image — which is a different statement from `0 ≤ ⟨x, T x⟩`,
  the shape of `GNSHilbert.PositiveTransfer`.
* No spectrum, no gap and no Hamiltonian. The results are norm bounds; `-log T` is not built.
* No relation to `GNSHilbert.ymH`. `ymH` is the completion of the complexification of
  `↥(LogConvex.localObs (blkS τ a m) (blkR τ a m))` under the Gibbs reflection form
  `Transfer.reflForm`, the Gibbs expectation of `(F ∘ reflConf) · G` with Boltzmann weight and
  division by the partition function. A member of `localObs S R` is a bounded measurable function on
  the full link configuration space `Link d n → SU N` determined by its values on `S ∪ R`, so the
  carrier is local to a band of time slices cut by `ActionSplit.blkS` and `blkR` relative to the
  reflection plane. `slabTransfer` acts on `L²` of one slab's links against the unweighted product
  Haar measure. Four differences: (i) the underlying type is `SlabIdx τ t → SU N`, a fibre of the
  link set, where `localObs`'s is `Link d n → SU N` with a locality clause; (ii) the measure is
  Haar, not the Gibbs measure, and the GNS form reflects one argument through `Θ` before pairing;
  (iii) `ymH` is a completion under a semidefinite form, so its vectors are classes modulo that
  form's null space, and nothing relates that null space to `L²`-almost-everywhere equality;
  (iv) `ymH` exists only at `n = 2 * m` with `0 < m` and is indexed by a reflection plane `a` and a
  half-extent `m`, while `slabTransfer` needs only `[NeZero n]` and is indexed by a time `t : Fin n`.
* Nothing here shows the kernel couples its two arguments. A kernel constant in its second argument
  satisfies every theorem in this file, and at the parameter values listed above the kernel is
  constant in both. What `slabTransfer_ne_zero` rules out is that the operator is zero.
* The lower bound degenerates in the volume. `slabCap⁻¹ = exp (-|β| · 2 · slabPlaqCount τ t)` is a
  Doeblin constant that shrinks exponentially in the slab's plaquette count, so it supports no claim
  uniform in the volume.

Foundational footprint only (`#print axioms` at the end).
Build: `python research/code/lean_build.py build MassGap.SlabKernelOperator`.
-/

namespace MassGap.SlabKernelOperator

open MeasureTheory
open MassGap MassGap.SliceTrace MassGap.WilsonAction MassGap.WilsonHypercubic
open MassGap.CompactGauge MassGap.SliceTransfer MassGap.WilsonLattice

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
sharper bound be applied to an operator already constructed with a weaker one; `slabTransfer` and
`norm_slabTransfer_le_one` are that case. The proof is
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
The statements below rule both out. They take a strictly positive LOWER bound on the kernel, which
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

`SliceTrace.slabKernel τ β t` is a real-valued function of a configuration of the links at time `t`
and a configuration of the links at time `t + 1`. Both configuration spaces are finite products of
copies of `SU N`, which is compact, and both carry the product of the probability Haar measure. The
kernel is built from `WilsonAction.wilsonDensity` through `Real.exp`, so it is continuous, and its
logarithm is bounded in absolute value by a plaquette count times `|β|`. Part 1 then applies with
no further input. -/

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
discharges every `IsProbabilityMeasure` side condition that Part 1 imposes on the Part 2
statements, so it is listed in the axiom footprint block with the rest.

DERIVED: no numeral. -/
instance isProbabilityMeasure_slabHaar (τ : Fin d) (t : Fin n) :
    IsProbabilityMeasure (slabHaar (N := N) τ t) := by
  unfold slabHaar; infer_instance

omit [NeZero n] in
/-- `slabVol τ` is the `Fin n`-indexed product of the `slabHaar τ t`. `partition_eq_cycleIntegral`
integrates the cyclic product of kernels against `slabVol τ`, so the measure this file's operator is
built on is exactly one factor of it. The proof is `rfl`, and this is the only statement here
relating the operator to the partition function. The `[NeZero n]` instance is omitted for this
declaration.

DERIVED: no numeral. -/
theorem slabVol_eq_pi_slabHaar (τ : Fin d) :
    slabVol (d := d) (n := n) (N := N) τ
      = Measure.pi fun t : Fin n => slabHaar (N := N) τ t := rfl

/-- The map sending a pair of slab configurations at `t` and `t + 1` to the regrouped patched full
configuration is continuous. `patch`'s branch tests read the time of the link being served and not
the configuration, so each coordinate of the result is a coordinate projection of one of the two
arguments or the constant identity, and `continuous_pi` closes it.

DERIVED: the `1` in `t + 1` is `SliceTrace.slabKernel`'s own time step — one slice on, `Fin n`
addition, which wraps. It is inherited from that file, not chosen here. -/
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

/-- `slabKernel τ β t` is continuous as a function of the pair of slab configurations at `t` and
`t + 1`. It unfolds to a product of two exponentials of finite sums of `wilsonDensity` at plaquette
holonomies, each of which is continuous in the assembled configuration by
`continuous_regroup_patch` and `PlaqVariance.continuous_wilsonHol`.

DERIVED: the `1` in `t + 1` is `SliceTrace.slabKernel`'s own time step — one slice on, `Fin n`
addition, which wraps. It is inherited from that file, not chosen here. -/
theorem continuous_slabKernel_uncurry (τ : Fin d) (β : ℝ) (t : Fin n) :
    Continuous (fun p : ((SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N) ×
        (SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N)) =>
      slabKernel (N := N) τ β t p.1 p.2) := by
  have hreg := continuous_regroup_patch (N := N) τ t
  simp only [slabKernel, slabWeight, intraSliceAction]
  refine Continuous.mul ?_ ?_
  · exact Real.continuous_exp.comp (continuous_const.mul
      (continuous_finsetSum _ (fun q _ =>
        continuous_wilsonDensity.comp
          ((MassGap.PlaqVariance.continuous_wilsonHol bd q).comp hreg))))
  · exact Real.continuous_exp.comp (continuous_const.mul
      (continuous_finsetSum _ (fun q _ =>
        continuous_wilsonDensity.comp
          ((MassGap.PlaqVariance.continuous_wilsonHol bd q).comp hreg))))

/-- The uncurried slab kernel is measurable. `SU N` carries the Borel σ-algebra of its own topology
(`MassGap.SUN`), so `continuous_slabKernel_uncurry` gives measurability, which is the hypothesis
Part 1 takes.

DERIVED: the `1` in the implicit domain type `SlabIdx τ (t + 1) → SU N` is
`SliceTrace.slabKernel`'s own time step — one slice on, `Fin n` addition, which wraps. It is
inherited from that file, not chosen here. -/
theorem measurable_slabKernel_uncurry (τ : Fin d) (β : ℝ) (t : Fin n) :
    Measurable (Function.uncurry (slabKernel (N := N) τ β t)) :=
  (continuous_slabKernel_uncurry τ β t).measurable

/-- The plaquette count of one slab: the cardinality of `intraPlaq τ t` plus the cardinality of the
non-degenerate part of `interPlaq τ t`. These are exactly the two `Finset`s `SliceTrace.slabWeight`
sums over, which is what makes `slabCap` a bound and not merely an inequality.

DERIVED: no numeral. Both cardinalities are the lattice's own. -/
def slabPlaqCount (τ : Fin d) (t : Fin n) : ℕ :=
  (intraPlaq (d := d) (n := n) τ t).card
    + ((interPlaq (d := d) (n := n) τ t).filter (fun q => q.1.1 ≠ q.1.2)).card

/-- The uniform bound on the slab kernel: `exp (|β| * (2 * slabPlaqCount τ t))`. It is symmetric in
the sign of `β` and grows exponentially in the slab's plaquette count.

⛔ Reading a magnitude off this number requires carrying the convention. `β` is `sysWilson`'s, and
the plaquette sum runs over the ordered pair type, which counts each plane twice (`SliceTrace`'s
header, via `PlaqCount.boltz_eq_std`), so this `β` is half the standard Wilson coupling and this
count is twice the standard plaquette count. The inequalities below are correct against the tree's
own sums, but they are not in the standard normalisation.

DERIVED: the `2` is `WilsonAction.wilsonDensity_le_two`'s cap on one plaquette's Wilson density —
`|Re tr U| ≤ N` read back — and the count is the lattice's. Nothing here is chosen. -/
noncomputable def slabCap (τ : Fin d) (β : ℝ) (t : Fin n) : ℝ :=
  Real.exp (|β| * (2 * (slabPlaqCount (d := d) (n := n) τ t : ℝ)))

/-- The two-sided bound on the slab weight: `slabCap⁻¹ ≤ slabWeight τ β t U ≤ slabCap`, at every
full link configuration `U` and every real `β`. The total Wilson energy of the slab lies in
`[0, 2 · slabPlaqCount τ t]` by `wilsonDensity_nonneg` and `wilsonDensity_le_two`, so the exponent
`-β · S` has absolute value at most `|β| · 2 · slabPlaqCount τ t` and `Real.exp_le_exp` gives both
sides.

DERIVED: the only numeral in the statement is the `0` of `hN : N ≠ 0`, which is
`wilsonDensity_nonneg`'s and `wilsonDensity_le_two`'s own hypothesis, ruling out the degenerate
`1 / N` normalisation and not an empty gauge group. The `2` that appears in the proof is
`wilsonDensity_le_two`'s and reaches the statement only inside `slabCap`. -/
theorem slabWeight_bounds (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n)
    (U : Link d n → MassGap.SUN.SU N) :
    (slabCap (d := d) (n := n) τ β t)⁻¹ ≤ slabWeight (N := N) τ β t U
      ∧ slabWeight (N := N) τ β t U ≤ slabCap (d := d) (n := n) τ β t := by
  set M : ℝ := (slabPlaqCount (d := d) (n := n) τ t : ℝ) with hM
  set S1 : ℝ := ∑ q ∈ intraPlaq (d := d) (n := n) τ t,
      wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U) with hS1
  set S2 : ℝ := ∑ q ∈ (interPlaq (d := d) (n := n) τ t).filter (fun q => q.1.1 ≠ q.1.2),
      wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U) with hS2
  have hS1n : 0 ≤ S1 := Finset.sum_nonneg (fun q _ => wilsonDensity_nonneg hN _)
  have hS2n : 0 ≤ S2 := Finset.sum_nonneg (fun q _ => wilsonDensity_nonneg hN _)
  have hS1b : S1 ≤ 2 * ((intraPlaq (d := d) (n := n) τ t).card : ℝ) := by
    calc S1 ≤ ∑ _q ∈ intraPlaq (d := d) (n := n) τ t, (2 : ℝ) :=
          Finset.sum_le_sum (fun q _ => wilsonDensity_le_two hN _)
      _ = 2 * ((intraPlaq (d := d) (n := n) τ t).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hS2b : S2 ≤ 2 * ((((interPlaq (d := d) (n := n) τ t).filter
      (fun q => q.1.1 ≠ q.1.2)).card : ℝ)) := by
    calc S2 ≤ ∑ _q ∈ (interPlaq (d := d) (n := n) τ t).filter (fun q => q.1.1 ≠ q.1.2), (2 : ℝ) :=
          Finset.sum_le_sum (fun q _ => wilsonDensity_le_two hN _)
      _ = 2 * ((((interPlaq (d := d) (n := n) τ t).filter
              (fun q => q.1.1 ≠ q.1.2)).card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hw : slabWeight (N := N) τ β t U = Real.exp (-β * (S1 + S2)) := by
    simp only [slabWeight, intraSliceAction, ← hS1, ← hS2, ← Real.exp_add]
    congr 1
    ring
  have hsum : S1 + S2 ≤ 2 * M := by
    rw [hM, slabPlaqCount]
    push_cast
    linarith
  have habs : |(-β) * (S1 + S2)| ≤ |β| * (2 * M) := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ S1 + S2)]
    exact mul_le_mul_of_nonneg_left hsum (abs_nonneg β)
  have hcap : slabCap (d := d) (n := n) τ β t = Real.exp (|β| * (2 * M)) := by
    rw [slabCap, hM]
  constructor
  · rw [hw, hcap, ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (abs_le.mp habs).1
  · rw [hw, hcap]
    exact Real.exp_le_exp.mpr (abs_le.mp habs).2

omit [NeZero n] in
/-- The cap is positive, at every `β` and `t`, because it is an exponential. This is what lets
`slabCap⁻¹` be used as a strictly positive lower bound. The `[NeZero n]` instance is omitted for
this declaration.

DERIVED: the `0` is the sign tested; `Real.exp_pos` supplies it. -/
theorem slabCap_pos (τ : Fin d) (β : ℝ) (t : Fin n) :
    0 < slabCap (d := d) (n := n) τ β t := Real.exp_pos _

/-- `|slabKernel τ β t A B| ≤ slabCap τ β t` at every pair of slab configurations, so the bound is
uniform in both arguments. The kernel is positive (`slabKernel_pos`), so the absolute value is the
value, and `slabWeight_bounds` supplies the upper side.

DERIVED: the `1` in `t + 1` is `SliceTrace.slabKernel`'s time step. The `0` of `hN : N ≠ 0` is
`wilsonDensity_nonneg`'s and `wilsonDensity_le_two`'s own hypothesis, ruling out the degenerate
`1 / N` normalisation. It does not rule out a trivial gauge group: `SU 0` is the one-element group
and `SUN` carries `Nonempty (SU n)` at every `n`. -/
theorem abs_slabKernel_le (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n)
    (A : SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
    (B : SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N) :
    |slabKernel (N := N) τ β t A B| ≤ slabCap (d := d) (n := n) τ β t := by
  rw [abs_of_pos (slabKernel_pos τ β t A B)]
  exact (slabWeight_bounds hN τ β t _).2

/-- `slabCap τ β t⁻¹ ≤ slabKernel τ β t A B` at every pair of slab configurations, so the kernel has
a positive lower bound uniform in both arguments. It is the lower half of `slabWeight_bounds`, and
it is what discharges `kernelCLM_ne_zero`'s hypothesis at `slabTransfer_ne_zero`. The constant
shrinks exponentially in `slabPlaqCount τ t`.

DERIVED: the `1` in `t + 1` is `SliceTrace.slabKernel`'s time step. The `0` of `hN : N ≠ 0` is
`wilsonDensity_nonneg`'s and `wilsonDensity_le_two`'s own hypothesis, ruling out the degenerate
`1 / N` normalisation. It does not rule out a trivial gauge group: `SU 0` is the one-element group
and `SUN` carries `Nonempty (SU n)` at every `n`. -/
theorem slabCap_inv_le_slabKernel (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n)
    (A : SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
    (B : SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N) :
    (slabCap (d := d) (n := n) τ β t)⁻¹ ≤ slabKernel (N := N) τ β t A B :=
  (slabWeight_bounds hN τ β t _).1

/-- At `0 ≤ β` the slab weight is at most `1`, at every full link configuration. The slab energy is
nonnegative (`wilsonDensity_nonneg`), so the exponent `-β · S` is nonpositive and
`Real.exp_le_one_iff` applies to each of the two factors. The bound carries no plaquette count,
unlike `slabCap`, which symmetrises in the sign of `β`. It holds at nonnegative coupling only; `β`
is not universally quantified past `hβ`.

DERIVED: the `1` is the value of `exp` at `0`; the `0` of `hβ` is the sign of the coupling and the
`0` of `hN : N ≠ 0` is `wilsonDensity_nonneg`'s own hypothesis. Nothing is chosen. -/
theorem slabWeight_le_one (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (hβ : 0 ≤ β) (t : Fin n)
    (U : Link d n → MassGap.SUN.SU N) :
    slabWeight (N := N) τ β t U ≤ 1 := by
  have h1 : (0:ℝ) ≤ ∑ q ∈ intraPlaq (d := d) (n := n) τ t,
      wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U) :=
    Finset.sum_nonneg (fun q _ => wilsonDensity_nonneg hN _)
  have h2 : (0:ℝ) ≤ ∑ q ∈ (interPlaq (d := d) (n := n) τ t).filter (fun q => q.1.1 ≠ q.1.2),
      wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U) :=
    Finset.sum_nonneg (fun q _ => wilsonDensity_nonneg hN _)
  have e1 : Real.exp (-β * ∑ q ∈ intraPlaq (d := d) (n := n) τ t,
      wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hβ h1])
  have e2 : Real.exp (-β * ∑ q ∈ (interPlaq (d := d) (n := n) τ t).filter
      (fun q => q.1.1 ≠ q.1.2),
      wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hβ h2])
  simp only [slabWeight, intraSliceAction]
  refine le_trans (mul_le_mul e1 e2 (Real.exp_pos _).le zero_le_one) ?_
  norm_num

/-- At `0 ≤ β` the slab kernel is bounded by `1`, uniformly in both slab arguments. The kernel is
positive, so the absolute value is the value, and `slabWeight_le_one` supplies the bound.

DERIVED: the `1` on the right is `slabWeight_le_one`'s and is `Real.exp 0`; the `1` in `t + 1` is
`SliceTrace.slabKernel`'s time step; the `0`s are the signs tested in `hN : N ≠ 0` and
`hβ : 0 ≤ β`. -/
theorem abs_slabKernel_le_one (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (hβ : 0 ≤ β) (t : Fin n)
    (A : SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
    (B : SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N) :
    |slabKernel (N := N) τ β t A B| ≤ 1 := by
  rw [abs_of_pos (slabKernel_pos τ β t A B)]
  exact slabWeight_le_one hN τ β hβ t _

/-! ### The collapsing parameter values

The module header lists the parameter values at which the statements above hold with no content.
Two of them are settled outright below: in each the kernel is the constant `1`, so the induced
operator is the rank-one averaging map. -/

/-- At `β = 0` the slab kernel is the constant `1`, at every pair of slab configurations. Both
exponents carry a factor of `β`, so both exponentials are `Real.exp 0`.

DERIVED: the `0` is the coupling being set and the `1` is `Real.exp 0`; neither is a chosen level.
The `1` in `t + 1` is `SliceTrace.slabKernel`'s time step. -/
theorem slabKernel_beta_zero (τ : Fin d) (t : Fin n)
    (A : SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
    (B : SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N) :
    slabKernel (N := N) τ 0 t A B = 1 := by
  simp [slabKernel, slabWeight, intraSliceAction]

/-- If `slabPlaqCount τ t = 0` then the slab kernel is the constant `1`, at every `β` and every pair
of slab configurations. A zero sum of two cardinalities makes both `Finset`s empty
(`Finset.card_eq_zero`), so both sums in `slabWeight` are empty and both exponentials are
`Real.exp 0`. This is the case at `d ≤ 1`.

DERIVED: the `0` is the count being zero and the `1` is `Real.exp 0`; neither is chosen. The `1` in
`t + 1` is `SliceTrace.slabKernel`'s time step. -/
theorem slabKernel_eq_one_of_plaqCount_zero (τ : Fin d) (β : ℝ) (t : Fin n)
    (h : slabPlaqCount (d := d) (n := n) τ t = 0)
    (A : SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
    (B : SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N) :
    slabKernel (N := N) τ β t A B = 1 := by
  have hc := h
  rw [slabPlaqCount] at hc
  have h1 : (intraPlaq (d := d) (n := n) τ t).card = 0 := by omega
  have h2 : ((interPlaq (d := d) (n := n) τ t).filter
      (fun q => q.1.1 ≠ q.1.2)).card = 0 := by omega
  rw [Finset.card_eq_zero] at h1 h2
  simp [slabKernel, slabWeight, intraSliceAction, h1, h2]

/-- The slab transfer operator: `kernelCLM` at `slabKernel τ β t` with the bound `slabCap τ β t`. It
is a `ContinuousLinearMap` from `L²` of the slab at `t + 1` to `L²` of the slab at `t`, against the
product Haar probability measures `slabHaar`. Its source and target are different types except at
`n = 1`, so it is not an endomorphism in general, and no power or composite of it is formed
anywhere in this file.

DERIVED: the `2`s are the `L²` exponent; the `1` in `t + 1` is `SliceTrace.slabKernel`'s time step;
the `0` of `hN : N ≠ 0` is `wilsonDensity_nonneg`'s own hypothesis and rules out the `1 / N`
normalisation, not a trivial gauge group. -/
noncomputable def slabTransfer (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n) :
    Lp ℝ 2 (slabHaar (N := N) τ (t + 1)) →L[ℝ] Lp ℝ 2 (slabHaar (N := N) τ t) :=
  kernelCLM (slabKernel (N := N) τ β t) (slabCap (d := d) (n := n) τ β t)
    (measurable_slabKernel_uncurry τ β t) (le_of_lt (slabCap_pos τ β t))
    (abs_slabKernel_le hN τ β t) (slabHaar τ t) (slabHaar τ (t + 1))

/-- `‖slabTransfer hN τ β t‖ ≤ slabCap τ β t`, at every real `β`. It is `norm_kernelCLM_le` at the
constant `slabTransfer` was built with. The bound grows exponentially in `slabPlaqCount τ t`.

DERIVED: the statement's only numeral is the `0` of `hN : N ≠ 0`, `wilsonDensity_nonneg`'s own
hypothesis. The `2` inside `slabCap` is `wilsonDensity_le_two`'s. -/
theorem norm_slabTransfer_le (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n) :
    ‖slabTransfer (d := d) (n := n) hN τ β t‖ ≤ slabCap (d := d) (n := n) τ β t :=
  norm_kernelCLM_le _ _ _ _ _ _ _

/-- At `0 ≤ β` the slab transfer operator is a contraction: `‖slabTransfer hN τ β t‖ ≤ 1`. The
kernel bound `abs_slabKernel_le_one` is carried to the already-constructed operator by
`norm_kernelCLM_le_of_bound`, so no rebuilding at a smaller constant is needed. The bound carries no
plaquette count, so it does not degrade with the volume, where `norm_slabTransfer_le` is
exponentially larger and holds at every sign of `β`. It is a norm bound, and states nothing about
the spectrum or self-adjointness.

DERIVED: the `1` is `abs_slabKernel_le_one`'s and is `Real.exp 0`; the `0` of `hβ` is the sign of
the coupling and the `0` of `hN : N ≠ 0` is `wilsonDensity_nonneg`'s own hypothesis. -/
theorem norm_slabTransfer_le_one (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (hβ : 0 ≤ β) (t : Fin n) :
    ‖slabTransfer (d := d) (n := n) hN τ β t‖ ≤ 1 :=
  norm_kernelCLM_le_of_bound _ _ _ _ _ _ _ zero_le_one (abs_slabKernel_le_one hN τ β hβ t)

/-- An almost-everywhere nonnegative `f` on the slab at `t + 1` has an almost-everywhere nonnegative
image on the slab at `t`. It is `kernelCLM_nonneg` at `slabKernel_pos`. This is positivity
preservation on functions, not positivity of the operator in the sense `0 ≤ ⟨x, T x⟩`.

DERIVED: the `0`s are the signs tested — in `hN : N ≠ 0`, in the hypothesis on `f` and in the
conclusion. The `2`s are the `L²` exponent and the `1` in `t + 1` is `SliceTrace.slabKernel`'s time
step. -/
theorem slabTransfer_nonneg (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n)
    (f : Lp ℝ 2 (slabHaar (N := N) τ (t + 1)))
    (hf : 0 ≤ᵐ[slabHaar (N := N) τ (t + 1)] (f : _ → ℝ)) :
    0 ≤ᵐ[slabHaar (N := N) τ t]
      ((slabTransfer (d := d) (n := n) hN τ β t f : Lp ℝ 2 (slabHaar (N := N) τ t)) : _ → ℝ) :=
  kernelCLM_nonneg _ _ _ _ _ _ _ (fun A B => le_of_lt (slabKernel_pos τ β t A B)) f hf

/-- `slabTransfer hN τ β t` is not the zero operator, at every real `β`. It is `kernelCLM_ne_zero`
at the strictly positive lower bound `slabCap_inv_le_slabKernel`, whose positivity is
`slabCap_pos`. That lower bound comes from `wilsonDensity_le_two` capping the slab energy above.
The statement rules out only that the operator vanishes; it does not show the kernel couples its two
arguments.

DERIVED: the `0`s are the sign tested in `hN : N ≠ 0` and the operator excluded in `≠ 0`. -/
theorem slabTransfer_ne_zero (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n) :
    slabTransfer (d := d) (n := n) hN τ β t ≠ 0 :=
  kernelCLM_ne_zero _ _ _ _ _ _ _ (inv_pos.mpr (slabCap_pos τ β t))
    (slabCap_inv_le_slabKernel hN τ β t)

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
#print axioms continuous_slabKernel_uncurry
#print axioms measurable_slabKernel_uncurry
#print axioms slabPlaqCount
#print axioms slabCap
#print axioms slabWeight_bounds
#print axioms slabCap_pos
#print axioms abs_slabKernel_le
#print axioms slabCap_inv_le_slabKernel
#print axioms slabWeight_le_one
#print axioms abs_slabKernel_le_one
#print axioms slabKernel_beta_zero
#print axioms slabKernel_eq_one_of_plaqCount_zero
#print axioms slabTransfer
#print axioms norm_slabTransfer_le
#print axioms norm_slabTransfer_le_one
#print axioms slabTransfer_nonneg
#print axioms slabTransfer_ne_zero

end MassGap.SlabKernelOperator
