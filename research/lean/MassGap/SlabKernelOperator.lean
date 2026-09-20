import Mathlib
import MassGap.SliceTrace
import MassGap.PlaqVariance

/-!
# MassGap.SlabKernelOperator — the slab kernel induces a BOUNDED operator on `L²`

`SliceTrace` produced `slabKernel`, the slice-to-slice kernel whose cyclic integral is the partition
function, and `GNSHilbert` recorded it as "a bare real-valued kernel with no normalisation and no
L2-boundedness in the tree", adding that "Mathlib v4.31.0 has no integral-operator machinery". That
second clause is not tested here and does not need to be: whether or not such a development exists at
the pin, NONE IS USED BELOW. No Schatten class, no Hilbert–Schmidt class, no trace class and no
integral-operator file is named anywhere in this file. What is used is that the configuration space
is a finite power of a COMPACT group carrying a PROBABILITY measure and that the kernel is BOUNDED,
at which point Cauchy–Schwarz in `MeasureTheory.L2` is the whole argument. The lemmas it runs on —
`MemLp.of_bound`, `Lp.norm_le_of_ae_bound`, `abs_real_inner_le_norm`, `L2.inner_def` and
`StronglyMeasurable.integral_prod_right'` — were checked to exist at v4.31.0 by elaborating them on
the build host, not recalled.

## What is proved

**Part 1, abstract.** For measurable spaces `X`, `Y` with PROBABILITY measures `μ`, `ν` and a kernel
`K : X → Y → ℝ` that is jointly measurable and satisfies `|K x y| ≤ C`:

* `abs_kernelFun_le` — for `f` in `L²(ν)`, `|∫ K x y f y dν| ≤ C ‖f‖₂` for EVERY `x`, not merely
  almost every `x`. The kernel row is itself an `L²(ν)` vector of norm at most `C`
  (`Lp.norm_le_of_ae_bound` at a probability measure), and `abs_real_inner_le_norm` is
  Cauchy–Schwarz. So the image is a BOUNDED function, which is stronger than what `L²(μ)` needs.
* `kernelCLM` — the induced map `L²(ν) →L[ℝ] L²(μ)`, a genuine `ContinuousLinearMap`, with
  `norm_kernelCLM_le : ‖kernelCLM‖ ≤ C`.
* `norm_kernelCLM_le_of_bound` — the operator norm is at most ANY uniform bound on the kernel, not
  only the one the operator was constructed with. This is what lets a sharper bound be applied to an
  operator that is already built.
* `kernelCLM_nonneg` — a nonnegative kernel gives a positivity-preserving operator.
* `kernelCLM_ne_zero` — **the anti-vacuity statement.** If `K` is bounded BELOW by some `ε > 0` then
  the operator is not the zero operator: its value on the constant observable is bounded below by `ε`
  (`le_kernelCLM_one`), and a probability measure has a nonempty almost-everywhere filter, so it
  cannot be almost-everywhere zero. Neither the domain nor the operator is trivial.

Measurability of `x ↦ ∫ K x y f y dν` is `StronglyMeasurable.integral_prod_right'`, which is the only
Fubini-flavoured input and is in Mathlib at the pin. `MemLp.of_bound` and `Lp.norm_le_of_ae_bound`
are the two finite-measure facts. Those, with `abs_real_inner_le_norm` and `L2.inner_def`, are the
whole of the NON-ROUTINE external footprint; the rest is ordinary integral algebra
(`integral_congr_ae`, `integral_add`, `integral_const_mul`, `integral_mono`, `integral_nonneg_of_ae`)
and the `Lp` coercion lemmas. The file imports all of Mathlib, as `GNSHilbert` does, so the import
line pins nothing — what pins the claim is that these names elaborate at v4.31.0 on the build host.

**Part 2, at the Wilson slab kernel.** `slabKernel τ β t` is the object `SliceTrace` built.

* `continuous_slabKernel_uncurry` — it is jointly CONTINUOUS in its two slab arguments, hence
  jointly measurable (`measurable_slabKernel_uncurry`). Continuity passes through `patch` and
  `regroup` because the branch tests in `patch` do not depend on the configuration, only on the time
  index of the link being served.
* `abs_slabKernel_le` / `slabCap_inv_le_slabKernel` — it lies between `exp (-|β| · 2 · P)` and
  `exp (|β| · 2 · P)`, where `P = slabPlaqCount τ t` counts exactly the plaquettes `slabWeight` sums
  over, from `WilsonAction.wilsonDensity_nonneg` and `wilsonDensity_le_two` alone. `[0, 2P]` is a
  CONTAINING interval for the slab energy and not its range: the upper end needs every plaquette
  holonomy at `-I`, which for odd `N` is not in `SU N` at all.
* `abs_slabKernel_le_one` and `norm_slabTransfer_le_one` — **at `0 ≤ β` the operator is a
  CONTRACTION.** `slabWeight` is `e^{-βS}` with `S ≥ 0`, so at nonnegative coupling it is at most
  `1`, and `norm_kernelCLM_le_of_bound` carries that to the operator already built. This is the
  bound a spectral argument would consume. `slabCap` discards the sign of `β` and is exponentially
  larger in the slab's plaquette count, hence in the volume.
* `slabTransfer` — the `ContinuousLinearMap` `L²(slab t+1) →L[ℝ] L²(slab t)` induced by
  `slabKernel τ β t`, with `norm_slabTransfer_le`, `norm_slabTransfer_le_one`,
  `slabTransfer_nonneg` and `slabTransfer_ne_zero`.
* `slabVol_eq_pi_slabHaar` — the per-slab measure used here is the factor of `SliceTrace.slabVol`
  that `partition_eq_cycleIntegral` integrates against. It is the only statement in this file
  connecting the operator to the partition function, and it is a `rfl`.

## The degenerate regimes, named

Every theorem below is TRUE in each of these and says nothing in any of them. Two have controls
here; the rest are named because naming them is the report.

* **`slabPlaqCount τ t = 0`** — `slabKernel_eq_one_of_plaqCount_zero`: the kernel is CONSTANTLY `1`,
  so `slabTransfer` is the rank-one averaging map `f ↦ (∫ f) · 1`. This is the case at `d ≤ 1`, where
  `intraPlaq` is empty and every plaquette of `interPlaq` is diagonal so the filter empties it.
* **`β = 0`** — `slabKernel_beta_zero`: the same collapse and the same rank-one operator.
* **`N = 1`** — `SimpleGroup.subsingleton_SU_one` makes the gauge group trivial, so every holonomy is
  `1`, `wilsonDensity` is `0` and the kernel is constantly `1` again. The configuration space is a
  single point and `L²` is one dimensional. `hN : N ≠ 0` does NOT exclude this. Not formalised here.
* **`d = 0`** — `Fin 0` is empty, so there is no `τ` and every Part 2 statement is an empty
  quantification.
* **`n = 1`** — `t + 1 = t` in `Fin 1`, so the two slab index types COINCIDE and `slabTransfer` IS an
  endomorphism; `SliceTrace` records that `slabKernel` there ignores its second argument entirely.
  What the next section says about the two spaces being different is a statement about `n ≥ 2`.

## What this does NOT claim, named exactly

* **At `n ≥ 2` it is not an endomorphism, and the typing is not the real obstruction.**
  `slabKernel τ β t` maps the slab at `t+1` to the slab at `t`, and for `n ≥ 2` the types
  `SlabIdx τ t` and `SlabIdx τ (t+1)` are distinct, so `slabTransfer` is a bounded map between two
  different Hilbert spaces. They are nonetheless canonically isomorphic — time translation — so the
  typing is an inconvenience and not the obstruction. The obstruction to composing the cycle into one
  operator is one Fubini per intermediate variable, and that is not done here;
  `SliceTrace.cycle_kernel_prod_split` exhibits the cut and nothing more. Nothing below mentions a
  power of `slabTransfer`. At `n = 1` the types coincide and this bullet does not apply.
* **It is not self-adjoint and not positive.** `SliceTrace`'s header lists three separate differences
  between `slabKernel` and `SliceTransfer.transferKernel`, and the symmetry and
  positive-semidefiniteness proved of the latter are not transported to the former. Nothing here
  transports them either. `kernelCLM_nonneg` is POSITIVITY PRESERVATION (a nonnegative function goes
  to a nonnegative function), which is a different statement from positivity of the operator
  (`0 ≤ ⟨x, T x⟩`, which is `GNSHilbert.PositiveTransfer`'s shape) and does not imply it.
* **No spectrum, no gap, no Hamiltonian.** A norm bound is not a spectral statement. `-log T` is not
  built. At `n ≥ 2` `slabTransfer` is not an endomorphism, so it has no spectrum to be about; at
  `n = 1` it is one, and its spectrum is not computed here either.
* **It does not reach `GNSHilbert.ymH`, and the mismatch is fourfold.** `ymH` is the completion of
  the complexification of `↥(LogConvex.localObs (blkS τ a m) (blkR τ a m))` under the Gibbs
  reflection form `Transfer.reflForm`, which is the Gibbs expectation of `(F ∘ reflConf) · G` —
  Boltzmann weight and division by the partition function included. A member of `localObs S R` is a
  bounded measurable function on the FULL link configuration space `Link d n → SU N` that is
  DETERMINED by its values on `S ∪ R`; that locality clause is part of the carrier, so the module is
  local to a band of time slices, `ActionSplit.blkS` and `blkR` being cut by the time coordinate
  relative to the reflection plane. `slabTransfer` acts on `L²` of ONE slab's links against the
  unweighted product HAAR measure. The four differences: (i) the underlying type is
  `SlabIdx τ t → SU N`, a fibre of the link set, where `localObs`'s is `Link d n → SU N` with a
  locality clause — the two bands are cut by different decompositions and neither carrier is the
  other; (ii) the measure is Haar, not the Gibbs measure, and the GNS form additionally reflects one
  argument through `Θ` before pairing; (iii) `ymH` is a completion under a SEMIdefinite form, so its
  vectors are classes modulo that form's null space, and nothing in the tree relates that null space
  to `L²`-almost-everywhere equality in either direction; (iv) the parameters do not line up — `ymH`
  exists only at `n = 2 * m` with `0 < m` and is indexed by a reflection plane `a` and a half-extent
  `m`, while `slabTransfer` needs only `[NeZero n]` and is indexed by a time `t : Fin n`. No bridge
  is asserted here. Anything of the shape "`slabTransfer` descends to `ymH`" would need a common
  object these two are both built from, and the tree has none.
* **It does not show the kernel couples its two arguments.** `SliceTrace` names that as open and it
  stays open. A kernel constant in its second argument satisfies every theorem in this file — and in
  the degenerate regimes listed above the kernel IS constant in both arguments. What is ruled out is
  only that the operator is ZERO.
* **The lower bound degenerates in the volume.** `slabCap⁻¹ = exp (-|β| · 2 · slabPlaqCount τ t)` is
  a Doeblin constant and it shrinks exponentially in the slab's plaquette count. `SliceTrace`'s
  header says the same of the only minorisation its objects support. It suffices to prove the
  operator nonzero and it suffices for nothing that must be uniform in the volume.

Foundational footprint only (`#print axioms` at the end).
Build: `python research/code/lean_build.py build MassGap.SlabKernelOperator`.
-/

namespace MassGap.SlabKernelOperator

open MeasureTheory
open MassGap MassGap.SliceTrace MassGap.WilsonAction MassGap.WilsonHypercubic
open MassGap.CompactGauge MassGap.SliceTransfer MassGap.WilsonLattice

/-! ## Part 1 — a bounded measurable kernel on probability spaces induces a bounded operator

Nothing in this part is about the lattice. The two standing assumptions are that both measures are
probability measures — FINITENESS is what the argument uses, and the unit normalisation only removes
the measure factors from the constants — and that the kernel is bounded and jointly measurable. -/

section Abstract

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- **The kernel acting on a function.** `(T f)(x) = ∫ K x y · f y dν`.

DERIVED: no numeral. -/
noncomputable def kernelFun (K : X → Y → ℝ) (ν : Measure Y) (f : Y → ℝ) (x : X) : ℝ :=
  ∫ y, K x y * f y ∂ν

variable {K : X → Y → ℝ} {C : ℝ} {μ : Measure X} {ν : Measure Y}

/-- **A ROW OF A BOUNDED KERNEL IS AN `L²` VECTOR.** On a finite measure a bounded measurable
function lies in every `Lᵖ`; this is the instance at `p = 2`.

DERIVED: the `2` is the `L²` exponent — the one exponent at which Mathlib's `Lp` carries an inner
product, which is what Cauchy–Schwarz is used through. It is not a chosen parameter. -/
theorem memLp_row (hK : Measurable (Function.uncurry K)) (hKb : ∀ x y, |K x y| ≤ C)
    (ν : Measure Y) [IsFiniteMeasure ν] (x : X) : MemLp (K x) 2 ν := by
  have hm : Measurable (K x) := hK.comp measurable_prodMk_left
  refine MemLp.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall (fun y => ?_))
  simpa [Real.norm_eq_abs] using hKb x y

/-- **The kernel row times an integrable function is integrable.**

DERIVED: no numeral. -/
theorem integrable_row_mul (hK : Measurable (Function.uncurry K)) (hKb : ∀ x y, |K x y| ≤ C)
    {f : Y → ℝ} (hf : Integrable f ν) (x : X) :
    Integrable (fun y => K x y * f y) ν := by
  have hm : Measurable (K x) := hK.comp measurable_prodMk_left
  refine hf.bdd_mul (c := C) hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun y => ?_))
  simpa [Real.norm_eq_abs] using hKb x y

/-- **THE POINTWISE CAUCHY–SCHWARZ BOUND.** At EVERY `x` — not almost every `x` — the kernel action
is bounded by `C · ‖f‖₂`. The kernel row is an `L²(ν)` vector of norm at most `C`, because `ν` is a
probability measure and the row is bounded by `C`; the pairing is then the `L²` inner product and
`abs_real_inner_le_norm` is Cauchy–Schwarz.

This is the whole of the "integral-operator machinery" the tree was said to be missing.

DERIVED: the `2`s are the `L²` exponent, as in `memLp_row`. `C` is the caller's kernel bound. -/
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

/-- **THE IMAGE IS MEASURABLE.** The only Fubini-flavoured input, and it is in Mathlib at the pin.

DERIVED: the `2` is the `L²` exponent. -/
theorem stronglyMeasurable_kernelFun (hK : Measurable (Function.uncurry K))
    [SFinite ν] (f : Lp ℝ 2 ν) : StronglyMeasurable (kernelFun K ν (f : Y → ℝ)) :=
  StronglyMeasurable.integral_prod_right'
    (hK.stronglyMeasurable.mul ((Lp.stronglyMeasurable f).comp_measurable measurable_snd))

/-- **THE IMAGE IS IN `L²(μ)`**, because it is a bounded measurable function on a finite measure
space. The bound is `abs_kernelFun_le`'s, so it is uniform in `x`.

DERIVED: the `2`s are the `L²` exponent. -/
theorem memLp_kernelFun (hK : Measurable (Function.uncurry K)) (hC0 : 0 ≤ C)
    (hKb : ∀ x y, |K x y| ≤ C) (μ : Measure X) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (f : Lp ℝ 2 ν) : MemLp (kernelFun K ν (f : Y → ℝ)) 2 μ := by
  refine MemLp.of_bound (stronglyMeasurable_kernelFun hK f).aestronglyMeasurable (C * ‖f‖)
    (Filter.Eventually.of_forall (fun x => ?_))
  simpa [Real.norm_eq_abs] using abs_kernelFun_le hK hC0 hKb f x

/-- **THE OPERATOR, AS A LINEAR MAP.** Linearity is linearity of the integral, moved across the
almost-everywhere classes with `Lp.ext`.

DERIVED: the `2`s are the `L²` exponent. -/
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

/-- The linear map's value is the kernel action, almost everywhere.

DERIVED: the `2`s are the `L²` exponent. -/
theorem coeFn_kernelLM (hK : Measurable (Function.uncurry K)) (hC0 : 0 ≤ C)
    (hKb : ∀ x y, |K x y| ≤ C) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (f : Lp ℝ 2 ν) :
    ((kernelLM K C hK hC0 hKb μ ν f : Lp ℝ 2 μ) : X → ℝ)
      =ᵐ[μ] kernelFun K ν (f : Y → ℝ) :=
  (memLp_kernelFun hK hC0 hKb μ f).coeFn_toLp

/-- **THE OPERATOR, AS A `ContinuousLinearMap`.** The operator norm is at most the kernel's uniform
bound. No integral-operator machinery, no Schatten class, no trace class.

DERIVED: the `2`s are the `L²` exponent; `C` is the caller's kernel bound. -/
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

/-- **THE OPERATOR NORM BOUND.** `‖T‖ ≤ sup |K|`.

DERIVED: the `2`s are the `L²` exponent; `C` is the caller's kernel bound. -/
theorem norm_kernelCLM_le (K : X → Y → ℝ) (C : ℝ) (hK : Measurable (Function.uncurry K))
    (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ‖kernelCLM K C hK hC0 hKb μ ν‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC0 _

/-- The operator's value is the kernel action, almost everywhere.

DERIVED: the `2`s are the `L²` exponent. -/
theorem coeFn_kernelCLM (K : X → Y → ℝ) (C : ℝ) (hK : Measurable (Function.uncurry K))
    (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (f : Lp ℝ 2 ν) :
    ((kernelCLM K C hK hC0 hKb μ ν f : Lp ℝ 2 μ) : X → ℝ)
      =ᵐ[μ] kernelFun K ν (f : Y → ℝ) :=
  coeFn_kernelLM hK hC0 hKb μ ν f

/-- **THE OPERATOR NORM IS BOUNDED BY ANY UNIFORM BOUND ON THE KERNEL**, not only by the constant the
operator happens to have been constructed with. `norm_kernelCLM_le` is this at `C' = C`; the point of
the separate statement is that a SHARPER bound discovered afterwards can be applied to the operator
already built, without rebuilding it. The Wilson contraction bound at nonnegative coupling is exactly
that situation.

DERIVED: the `2`s are the `L²` exponent; `C` and `C'` are the caller's kernel bounds. -/
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

An operator that is zero, or bounded only because its domain is trivial, would satisfy everything
above. The two statements below rule both out, and they need a LOWER bound on the kernel — which is
a genuine hypothesis, not a consequence of the upper one. -/

/-- **THE CONSTANT OBSERVABLE**, as an `L²(ν)` vector.

DERIVED: the `1` is the constant function's value — the unit of the algebra, the vacuum's
representative, not a level. The `2` is the `L²` exponent. -/
noncomputable def oneLp (ν : Measure Y) [IsProbabilityMeasure ν] : Lp ℝ 2 ν :=
  (memLp_const (1 : ℝ)).toLp _

/-- **THE OPERATOR IS POSITIVITY PRESERVING** when the kernel is nonnegative. This is NOT positivity
of the operator in the sense of `Transfer.PositiveTransfer`; see the module header.

DERIVED: the `0`s are the sign tested, forced by the statement. The `2`s are the `L²` exponent. -/
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

/-- **THE OPERATOR MOVES THE CONSTANT OBSERVABLE OFF ZERO.** With a strictly positive lower bound on
the kernel, the image of the constant observable is bounded below by that same constant almost
everywhere — the measure of the second space being one is what turns the lower bound into the bound
on the integral.

DERIVED: the `1` is `oneLp`'s constant and, through `measure_univ`, the total mass of a probability
measure; `ε` is the caller's lower bound. The `2`s are the `L²` exponent. -/
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

/-- **THE OPERATOR IS NOT THE ZERO OPERATOR** — the anti-vacuity statement. A strictly positive
kernel forces the image of the constant observable off zero, and a probability measure's
almost-everywhere filter is not the bottom filter, so "almost everywhere `0`" and "everywhere at
least `ε`" cannot both hold.

This also rules out a trivial DOMAIN: the zero space admits only the zero operator.

DERIVED: the `0` is the operator being excluded; `ε` and its positivity are the caller's. The `2`s
are the `L²` exponent. -/
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
and a configuration of the links at time `t+1`. Both configuration spaces are finite products of
copies of `SU N`, which is compact, and both carry the product of the probability Haar measure. The
kernel is built from `WilsonAction.wilsonDensity` through `Real.exp`, so it is continuous and its
logarithm is bounded by a plaquette count. Part 1 then applies with nothing further. -/

section Wilson

variable {d n N : ℕ} [NeZero n]

/-- **THE PRODUCT HAAR MEASURE ON ONE SLAB'S LINKS.** `SliceTrace.slabVol` is the product of these
over all times; this is the single factor, which is what a kernel between two slabs integrates
against.

DERIVED: no numeral. -/
noncomputable def slabHaar (τ : Fin d) (t : Fin n) :
    Measure (SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N) :=
  Measure.pi fun _ => probHaar (MassGap.SUN.SU N)

/-- The per-slab measure is a probability measure: a finite product of probability Haar measures.
This is what every `IsProbabilityMeasure` side condition in Part 2 is discharged by, so it is listed
in the axiom footprint block with the rest.

DERIVED: no numeral. -/
instance isProbabilityMeasure_slabHaar (τ : Fin d) (t : Fin n) :
    IsProbabilityMeasure (slabHaar (N := N) τ t) := by
  unfold slabHaar; infer_instance

omit [NeZero n] in
/-- **THE PER-SLAB MEASURE IS THE FACTOR OF `SliceTrace.slabVol`.** `partition_eq_cycleIntegral`
integrates the cyclic product of kernels against `slabVol τ`, and `slabVol τ` is the product over
times of exactly the measure this file's operator is built on. It is a `rfl`, and it is the only
statement here connecting the operator to the partition function.

DERIVED: no numeral. -/
theorem slabVol_eq_pi_slabHaar (τ : Fin d) :
    slabVol (d := d) (n := n) (N := N) τ
      = Measure.pi fun t : Fin n => slabHaar (N := N) τ t := rfl

/-- **THE ASSEMBLED PATCHED CONFIGURATION IS CONTINUOUS IN THE TWO SLAB ARGUMENTS.** `patch`'s branch
tests read the time of the link being served and not the configuration, so each coordinate of the
assembled configuration is a coordinate projection of one of the two arguments, or the constant
identity.

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

/-- **THE SLAB KERNEL IS JOINTLY CONTINUOUS.**

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

/-- **THE SLAB KERNEL IS JOINTLY MEASURABLE.** `SU N` carries the Borel σ-algebra of its own topology
(`MassGap.SUN`), so continuity gives measurability.

DERIVED: the `1` in `t + 1` is `SliceTrace.slabKernel`'s own time step — one slice on, `Fin n`
addition, which wraps. It is inherited from that file, not chosen here. -/
theorem measurable_slabKernel_uncurry (τ : Fin d) (β : ℝ) (t : Fin n) :
    Measurable (Function.uncurry (slabKernel (N := N) τ β t)) :=
  (continuous_slabKernel_uncurry τ β t).measurable

/-- **THE PLAQUETTE COUNT OF ONE SLAB**: the intra-slice plaquettes of slice `t` plus the
non-degenerate temporal plaquettes based at `t` — exactly the two `Finset`s `SliceTrace.slabWeight`
sums over.

DERIVED: no numeral; both cardinalities are the lattice's own. -/
def slabPlaqCount (τ : Fin d) (t : Fin n) : ℕ :=
  (intraPlaq (d := d) (n := n) τ t).card
    + ((interPlaq (d := d) (n := n) τ t).filter (fun q => q.1.1 ≠ q.1.2)).card

/-- **THE UNIFORM BOUND ON THE SLAB KERNEL.**

DERIVED: the `2` is `WilsonAction.wilsonDensity_le_two`'s cap on ONE plaquette's Wilson density —
`|Re tr U| ≤ N` read back — and the count is the lattice's. Nothing here is chosen.

A READER EVALUATING THIS NUMBER MUST CARRY THE CONVENTION. `β` is `sysWilson`'s and the plaquette
sum runs over the ORDERED pair type, which counts each plane twice
(`SliceTrace`'s header, via `PlaqCount.boltz_eq_std`), so this `β` is half the standard Wilson
coupling and this count is twice the standard plaquette count. The inequality is correct against
the tree's own sums; a magnitude read off it is not in the standard normalisation. -/
noncomputable def slabCap (τ : Fin d) (β : ℝ) (t : Fin n) : ℝ :=
  Real.exp (|β| * (2 * (slabPlaqCount (d := d) (n := n) τ t : ℝ)))

/-- **THE TWO-SIDED BOUND ON THE SLAB WEIGHT.** The total Wilson energy of a slab lies in
`[0, 2 · #plaquettes]` by `wilsonDensity_nonneg` and `wilsonDensity_le_two`, so `e^{-βS}` lies
between the reciprocal cap and the cap.

DERIVED: the `2` is `wilsonDensity_le_two`'s; the `0` of `hN : N ≠ 0` is `wilsonDensity_nonneg`'s
own hypothesis, ruling out the degenerate `1 / N` normalisation and NOT an empty gauge group. -/
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
/-- The cap is positive.

DERIVED: the `0` is the sign tested; `Real.exp_pos` supplies it. -/
theorem slabCap_pos (τ : Fin d) (β : ℝ) (t : Fin n) :
    0 < slabCap (d := d) (n := n) τ β t := Real.exp_pos _

/-- **THE SLAB KERNEL IS BOUNDED ABOVE, UNIFORMLY IN BOTH ARGUMENTS.**

DERIVED: the `1` in `t + 1` is `SliceTrace.slabKernel`'s time step; the `0` of `hN : N ≠ 0` is
`wilsonDensity_nonneg`'s and `wilsonDensity_le_two`'s own hypothesis, ruling out the degenerate
`1 / N` normalisation. It does NOT rule out an empty gauge group: `SU 0` is the ONE-element group
and `SUN` carries `Nonempty (SU n)` at every `n`. -/
theorem abs_slabKernel_le (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n)
    (A : SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
    (B : SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N) :
    |slabKernel (N := N) τ β t A B| ≤ slabCap (d := d) (n := n) τ β t := by
  rw [abs_of_pos (slabKernel_pos τ β t A B)]
  exact (slabWeight_bounds hN τ β t _).2

/-- **THE SLAB KERNEL IS BOUNDED BELOW BY A POSITIVE CONSTANT, UNIFORMLY IN BOTH ARGUMENTS.** This is
what makes the induced operator nonzero; it is a real hypothesis and does not follow from the upper
bound.

DERIVED: the `1` in `t + 1` is `SliceTrace.slabKernel`'s time step; the `0` of `hN : N ≠ 0` is
`wilsonDensity_nonneg`'s and `wilsonDensity_le_two`'s own hypothesis, ruling out the degenerate
`1 / N` normalisation. It does NOT rule out an empty gauge group: `SU 0` is the ONE-element group
and `SUN` carries `Nonempty (SU n)` at every `n`. -/
theorem slabCap_inv_le_slabKernel (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n)
    (A : SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
    (B : SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N) :
    (slabCap (d := d) (n := n) τ β t)⁻¹ ≤ slabKernel (N := N) τ β t A B :=
  (slabWeight_bounds hN τ β t _).1

/-- **AT NONNEGATIVE COUPLING THE SLAB WEIGHT IS AT MOST ONE.** `slabCap` symmetrises in the sign of
`β` and therefore throws this away: the slab energy is NONNEGATIVE (`wilsonDensity_nonneg`), so at
`0 ≤ β` the exponent `-β·S` is nonpositive and `e^{-βS} ≤ 1` with no plaquette count in it at all.

DERIVED: the `1` is the value of `exp` at `0` and the `0`s are the signs tested; the `0` of
`hN : N ≠ 0` is `wilsonDensity_nonneg`'s own hypothesis. Nothing is chosen. -/
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

/-- **AT NONNEGATIVE COUPLING THE SLAB KERNEL IS BOUNDED BY ONE.**

DERIVED: the `1` is `slabWeight_le_one`'s; the `1` in `t + 1` is `SliceTrace.slabKernel`'s time step;
the `0`s are the signs tested. -/
theorem abs_slabKernel_le_one (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (hβ : 0 ≤ β) (t : Fin n)
    (A : SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
    (B : SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N) :
    |slabKernel (N := N) τ β t A B| ≤ 1 := by
  rw [abs_of_pos (slabKernel_pos τ β t A B)]
  exact slabWeight_le_one hN τ β hβ t _

/-! ### Controls for the degenerate regimes

The module header lists the parameter values at which every theorem here is true and empty. Two of
them are settled outright below: in each the kernel is the CONSTANT `1`, so the induced operator is
the rank-one averaging map and nothing in this file says anything about it. -/

/-- **AT ZERO COUPLING THE KERNEL IS CONSTANTLY ONE.**

DERIVED: the `0` is the coupling being set and the `1` is `Real.exp 0`; neither is a chosen level.
The `1` in `t + 1` is `SliceTrace.slabKernel`'s time step. -/
theorem slabKernel_beta_zero (τ : Fin d) (t : Fin n)
    (A : SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
    (B : SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N) :
    slabKernel (N := N) τ 0 t A B = 1 := by
  simp [slabKernel, slabWeight, intraSliceAction]

/-- **A SLAB WITH NO PLAQUETTES HAS A CONSTANT KERNEL.** This is the case at `d ≤ 1`, and it is the
sharpest way to say that the theorems below can be about nothing.

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

/-- **THE SLAB TRANSFER OPERATOR.** A bounded linear map from `L²` of the slab at `t+1` to `L²` of
the slab at `t`, against the product Haar probability measures. It is NOT an endomorphism — the two
slab index types differ — and no power of it is formed anywhere.

DERIVED: the `2`s are the `L²` exponent; the `1` in `t + 1` is `SliceTrace.slabKernel`'s time step;
the `0` of `hN : N ≠ 0` is `wilsonDensity_nonneg`'s own hypothesis and rules out the `1 / N`
normalisation, not an empty gauge group. -/
noncomputable def slabTransfer (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n) :
    Lp ℝ 2 (slabHaar (N := N) τ (t + 1)) →L[ℝ] Lp ℝ 2 (slabHaar (N := N) τ t) :=
  kernelCLM (slabKernel (N := N) τ β t) (slabCap (d := d) (n := n) τ β t)
    (measurable_slabKernel_uncurry τ β t) (le_of_lt (slabCap_pos τ β t))
    (abs_slabKernel_le hN τ β t) (slabHaar τ t) (slabHaar τ (t + 1))

/-- **THE SLAB TRANSFER OPERATOR IS BOUNDED, WITH AN EXPLICIT NORM BOUND** — the answer to the
question this file was written for.

DERIVED: as `slabTransfer`'s. -/
theorem norm_slabTransfer_le (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n) :
    ‖slabTransfer (d := d) (n := n) hN τ β t‖ ≤ slabCap (d := d) (n := n) τ β t :=
  norm_kernelCLM_le _ _ _ _ _ _ _

/-- **AT NONNEGATIVE COUPLING THE SLAB TRANSFER OPERATOR IS A CONTRACTION.** This is the bound that
matters: it carries no plaquette count, so it does not degrade with the volume, and `‖T‖ ≤ 1` is the
shape any later spectral statement would consume. `norm_slabTransfer_le` is the sign-blind bound and
is exponentially larger.

It is still only a norm bound. It says nothing about the spectrum, nothing about self-adjointness,
and — with the degenerate regimes the header lists — nothing about whether `T` moves anything.

DERIVED: the `1` is `abs_slabKernel_le_one`'s and is `Real.exp 0`; the `0` of `hβ` is the sign of the
coupling, which is what the bound is about; the rest as `slabTransfer`'s. -/
theorem norm_slabTransfer_le_one (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (hβ : 0 ≤ β) (t : Fin n) :
    ‖slabTransfer (d := d) (n := n) hN τ β t‖ ≤ 1 :=
  norm_kernelCLM_le_of_bound _ _ _ _ _ _ _ zero_le_one (abs_slabKernel_le_one hN τ β hβ t)

/-- **THE SLAB TRANSFER OPERATOR IS POSITIVITY PRESERVING.** Not to be confused with positivity of
the operator; see the module header.

DERIVED: the `0`s are the sign tested; the rest as `slabTransfer`'s. -/
theorem slabTransfer_nonneg (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t : Fin n)
    (f : Lp ℝ 2 (slabHaar (N := N) τ (t + 1)))
    (hf : 0 ≤ᵐ[slabHaar (N := N) τ (t + 1)] (f : _ → ℝ)) :
    0 ≤ᵐ[slabHaar (N := N) τ t]
      ((slabTransfer (d := d) (n := n) hN τ β t f : Lp ℝ 2 (slabHaar (N := N) τ t)) : _ → ℝ) :=
  kernelCLM_nonneg _ _ _ _ _ _ _ (fun A B => le_of_lt (slabKernel_pos τ β t A B)) f hf

/-- **THE SLAB TRANSFER OPERATOR IS NOT THE ZERO OPERATOR** — the anti-vacuity statement at
Yang–Mills. The kernel's uniform positive lower bound is what supplies it, and that lower bound is
`wilsonDensity_le_two` read in the other direction.

DERIVED: the `0` is the operator excluded; the rest as `slabTransfer`'s. -/
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
