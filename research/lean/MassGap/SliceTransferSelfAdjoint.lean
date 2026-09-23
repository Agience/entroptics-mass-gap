import Mathlib
import MassGap.SlabTransferAdjoint

/-!
# MassGap.SliceTransferSelfAdjoint — the operator on `L²` induced by `SliceTransfer.transferKernel`

Builds a bounded self-adjoint endomorphism of `Lp ℝ 2 (sliceHaar ι N)` from the slice-to-slice kernel
`SliceTransfer.transferKernel b s V W = exp (-s V / 2) * exp (b * sliceForm V W) * exp (-s W / 2)`,
by supplying the boundedness and measurability that `SlabKernelOperator.kernelCLM` requires and the
symmetry that `SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm` consumes.

## Part 1 — the cross form

`abs_hsRe_le` bounds `|hsRe A B|` by `N` for two `SU N` elements, through
`CrossingIntegration.hsRe_coe_eq` (which rewrites it as `Re tr (A B⁻¹)`) and
`WilsonAction.abs_re_trace_le`. `continuous_reTrace` and `continuous_hsRe_pair` give joint
continuity of the same expression, `continuous_sliceForm` sums it over the slice, and
`abs_sliceForm_le` bounds the sum by `Fintype.card ι * N`.

## Part 2 — the kernel

`transferCap ι N b Cs = exp Cs * exp (|b| * (card ι * N))`, positive by `transferCap_pos`.
`abs_transferKernel_le` bounds the kernel by it uniformly in both arguments, given only
`|s V| ≤ Cs`. `continuous_transferKernel_uncurry` and `measurable_transferKernel_uncurry` give joint
continuity and measurability when `s` is continuous.

## Part 3 — the operator

`sliceHaar ι N` is the product Haar probability measure on one slice's configurations.
`transferCLM b s Cs hs hsb` is `kernelCLM` at that kernel and cap, an endomorphism of
`Lp ℝ 2 (sliceHaar ι N)` — the same space at both ends, unlike
`SlabKernelOperator.slabTransfer`. `norm_transferCLM_le` bounds its norm by `transferCap`,
`isSelfAdjoint_transferCLM` and `adjoint_transferCLM` record self-adjointness (unconditionally, from
`SliceTransfer.transferKernel_symm`), and `transferCLM_ne_zero` rules out the zero operator by
bounding the kernel below by `(transferCap ι N b Cs)⁻¹`.

Scope: `b` is an arbitrary real — no sign hypothesis is used anywhere, so self-adjointness holds at
every `b`. The intra-slice function `s` is a parameter with two hypotheses, continuity and the
uniform bound `Cs`; no statement instantiates it at `SliceTransfer.intraSliceAction`. The results
are about `transferKernel`, not about `SliceTrace.slabKernel`, and nothing here relates the operator
to a partition function. Positivity of the operator, its spectrum, and any Hamiltonian are outside
the file: `SliceTransfer.transferKernel_psd` is a finite-family statement and is not used here.
Degenerate parameters are admitted — `N = 1`, `ι` empty, `b = 0` with constant `s` all satisfy every
hypothesis. Axiom footprints are printed at the end of the file.
-/

namespace MassGap.SliceTransferSelfAdjoint

open MeasureTheory
open MassGap MassGap.SliceTransfer MassGap.CharacterExpansion MassGap.CompactGauge
open MassGap.SlabKernelOperator MassGap.SlabTransferAdjoint

section Slice

variable {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Part 1 — bounds and continuity for `hsRe` and `sliceForm` -/

/-- `|hsRe a b| ≤ N` for `a b : MassGap.SUN.SU N`, read through their matrix coercions.
`CrossingIntegration.hsRe_coe_eq` rewrites the cross form as `Re (trace (a * b⁻¹))`, and
`WilsonAction.abs_re_trace_le` bounds the real trace of an `SU N` element by `N`.

Scope: the bound is the rank `N` itself, attained at `a = b`; it is not strict.

DERIVED: no numeral appears in the statement. `N` is the group's rank, a bound variable, and the
bound comes from `WilsonAction.abs_re_trace_le`. -/
theorem abs_hsRe_le (a b : MassGap.SUN.SU N) :
    |hsRe ((a : Matrix (Fin N) (Fin N) ℂ)) ((b : Matrix (Fin N) (Fin N) ℂ))| ≤ (N : ℝ) := by
  rw [MassGap.CrossingIntegration.hsRe_coe_eq]
  exact MassGap.WilsonAction.abs_re_trace_le _

/-- `fun g : MassGap.SUN.SU N => (Matrix.trace g).re` is continuous: the subtype inclusion is
continuous, `Matrix.trace` is continuous, and `Complex.re` is continuous. This is the step
`WilsonAction.continuous_wilsonDensity` also takes.

DERIVED: no numeral appears in the statement. -/
theorem continuous_reTrace :
    Continuous (fun g : MassGap.SUN.SU N => (Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re) :=
  Complex.continuous_re.comp continuous_subtype_val.matrix_trace

/-- `fun p => hsRe p.1 p.2` is continuous on `MassGap.SUN.SU N × MassGap.SUN.SU N` — jointly, not
separately. The proof rewrites it through `CrossingIntegration.hsRe_coe_eq` as
`fun p => (trace (p.1 * p.2⁻¹)).re` and composes `continuous_reTrace` with continuity of
multiplication and inversion in the topological group.

DERIVED: no numeral appears in the statement. -/
theorem continuous_hsRe_pair :
    Continuous (fun p : MassGap.SUN.SU N × MassGap.SUN.SU N =>
      hsRe ((p.1 : Matrix (Fin N) (Fin N) ℂ)) ((p.2 : Matrix (Fin N) (Fin N) ℂ))) := by
  have h : (fun p : MassGap.SUN.SU N × MassGap.SUN.SU N =>
      hsRe ((p.1 : Matrix (Fin N) (Fin N) ℂ)) ((p.2 : Matrix (Fin N) (Fin N) ℂ)))
      = fun p : MassGap.SUN.SU N × MassGap.SUN.SU N =>
        (Matrix.trace (((p.1 * p.2⁻¹ : MassGap.SUN.SU N)) : Matrix (Fin N) (Fin N) ℂ)).re := by
    funext p
    exact MassGap.CrossingIntegration.hsRe_coe_eq p.1 p.2
  rw [h]
  exact continuous_reTrace.comp (continuous_fst.mul (continuous_inv.comp continuous_snd))

/-- `fun p => sliceForm p.1 p.2` is jointly continuous on
`(ι → MassGap.SUN.SU N) × (ι → MassGap.SUN.SU N)`. `sliceForm` unfolds to a `Finset` sum over `ι` of
`hsRe` at the two configurations' values at each link, so `continuous_finsetSum` reduces it to
`continuous_hsRe_pair` composed with the coordinate projections. `[Fintype ι]` is what makes the sum
finite.

DERIVED: no numeral appears in the statement. -/
theorem continuous_sliceForm :
    Continuous (fun p : ((ι → MassGap.SUN.SU N) × (ι → MassGap.SUN.SU N)) =>
      sliceForm p.1 p.2) := by
  unfold sliceForm
  refine continuous_finsetSum _ (fun l _ => ?_)
  have hproj : Continuous (fun p : ((ι → MassGap.SUN.SU N) × (ι → MassGap.SUN.SU N)) =>
      ((p.1 l, p.2 l) : MassGap.SUN.SU N × MassGap.SUN.SU N)) :=
    ((continuous_apply l).comp continuous_fst).prodMk ((continuous_apply l).comp continuous_snd)
  have h := continuous_hsRe_pair.comp hproj
  exact h

omit [DecidableEq ι] in
/-- `|sliceForm V W| ≤ Fintype.card ι * N` at every pair of slice configurations. The triangle
inequality `Finset.abs_sum_le_sum_abs` reduces it to `abs_hsRe_le` at each link, and the resulting
constant sum is `Fintype.card ι * N`.

Scope: the bound is uniform in `V` and `W` and grows linearly in both the link count and the rank.

DERIVED: no numeral appears in the statement. `Fintype.card ι` is the slice's link count and `N` the
group's rank; both are determined by the parameters, neither is chosen. -/
theorem abs_sliceForm_le (V W : ι → MassGap.SUN.SU N) :
    |sliceForm V W| ≤ (Fintype.card ι : ℝ) * (N : ℝ) := by
  unfold sliceForm
  calc |∑ l : ι, hsRe ((V l : Matrix (Fin N) (Fin N) ℂ)) ((W l : Matrix (Fin N) (Fin N) ℂ))|
      ≤ ∑ l : ι, |hsRe ((V l : Matrix (Fin N) (Fin N) ℂ)) ((W l : Matrix (Fin N) (Fin N) ℂ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l : ι, (N : ℝ) := Finset.sum_le_sum (fun l _ => abs_hsRe_le _ _)
    _ = (Fintype.card ι : ℝ) * (N : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

end Slice

/-! ## Part 2 — a uniform cap on `transferKernel`, and its continuity -/

section Kernel

variable {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The constant `Real.exp Cs * Real.exp (|b| * (Fintype.card ι * N))`, used as the uniform cap on
`transferKernel b s` when `|s V| ≤ Cs`. The first factor absorbs the two intra-slice exponentials,
whose exponents are each at least `-Cs / 2`; the second absorbs the cross term through
`abs_sliceForm_le`.

Scope: `Cs` is the caller's bound on `s`, not derived here, and `b` may have either sign — the cap
uses `|b|`.

DERIVED: no numeral appears in the definition or its type. `Cs`, `b`, `Fintype.card ι` and `N` are
all parameters. -/
noncomputable def transferCap (ι : Type) [Fintype ι] (N : ℕ) (b Cs : ℝ) : ℝ :=
  Real.exp Cs * Real.exp (|b| * ((Fintype.card ι : ℝ) * (N : ℝ)))

omit [DecidableEq ι] in
/-- `0 < transferCap ι N b Cs` at every `b` and `Cs`: a product of two exponentials, closed by
`positivity`. Used to supply the nonnegativity `kernelCLM` requires of its bound, and the reciprocal
lower bound in `transferCLM_ne_zero`.

DERIVED: `0` is the lower bound asserted; `Real.exp_pos` supplies it. No other numeral appears in
the statement. -/
theorem transferCap_pos (b Cs : ℝ) : 0 < transferCap ι N b Cs := by
  unfold transferCap
  positivity

/-- Given `|s V| ≤ Cs` at every configuration, `|transferKernel b s V W| ≤ transferCap ι N b Cs`
uniformly in `V` and `W`. The absolute value is removed by `SliceTransfer.transferKernel_pos`, the
two intra-slice exponentials are combined and bounded by `exp Cs`, and the cross exponential is
bounded using `abs_sliceForm_le`.

Scope: `s` is only assumed bounded here — continuity is not needed for this statement. `b` may have
either sign.

DERIVED: no numeral appears in the statement. `Cs` is the caller's bound on `s`; the halving of the
intra-slice weight lives inside `transferKernel`'s own definition, not in this statement. -/
theorem abs_transferKernel_le (b : ℝ) (s : (ι → MassGap.SUN.SU N) → ℝ) (Cs : ℝ)
    (hsb : ∀ V, |s V| ≤ Cs) (V W : ι → MassGap.SUN.SU N) :
    |transferKernel b s V W| ≤ transferCap ι N b Cs := by
  rw [abs_of_pos (transferKernel_pos b s V W)]
  unfold transferKernel transferCap
  have h1 : Real.exp (-(s V) / 2) * Real.exp (-(s W) / 2) ≤ Real.exp Cs := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hV := (abs_le.mp (hsb V)).1
    have hW := (abs_le.mp (hsb W)).1
    linarith
  have h2 : Real.exp (b * sliceForm V W)
      ≤ Real.exp (|b| * ((Fintype.card ι : ℝ) * (N : ℝ))) := by
    refine Real.exp_le_exp.mpr ?_
    calc b * sliceForm V W ≤ |b * sliceForm V W| := le_abs_self _
      _ = |b| * |sliceForm V W| := abs_mul _ _
      _ ≤ |b| * ((Fintype.card ι : ℝ) * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left (abs_sliceForm_le V W) (abs_nonneg b)
  calc Real.exp (-(s V) / 2) * Real.exp (b * sliceForm V W) * Real.exp (-(s W) / 2)
      = (Real.exp (-(s V) / 2) * Real.exp (-(s W) / 2)) * Real.exp (b * sliceForm V W) := by ring
    _ ≤ Real.exp Cs * Real.exp (|b| * ((Fintype.card ι : ℝ) * (N : ℝ))) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le

/-- `fun p => transferKernel b s p.1 p.2` is jointly continuous whenever `s` is continuous. The
kernel unfolds to a product of three exponentials; the outer two are `Real.exp` composed with `s`
halved on each argument, and the middle one with `continuous_sliceForm`.

Scope: continuity of `s` is the only hypothesis — no bound on `s` is needed for this statement.

DERIVED: no numeral appears in the statement. The division by two of each intra-slice exponent lives
inside `transferKernel`'s definition. -/
theorem continuous_transferKernel_uncurry (b : ℝ) (s : (ι → MassGap.SUN.SU N) → ℝ)
    (hs : Continuous s) :
    Continuous (fun p : ((ι → MassGap.SUN.SU N) × (ι → MassGap.SUN.SU N)) =>
      transferKernel b s p.1 p.2) := by
  unfold transferKernel
  exact (((Real.continuous_exp.comp (((hs.comp continuous_fst).neg).div_const 2))).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_sliceForm))).mul
    (Real.continuous_exp.comp (((hs.comp continuous_snd).neg).div_const 2))

/-- `Function.uncurry (transferKernel b s)` is measurable whenever `s` is continuous — the
measurability of `continuous_transferKernel_uncurry`. This is the hypothesis
`SlabKernelOperator.kernelCLM` consumes.

DERIVED: no numeral appears in the statement. -/
theorem measurable_transferKernel_uncurry (b : ℝ) (s : (ι → MassGap.SUN.SU N) → ℝ)
    (hs : Continuous s) :
    Measurable (Function.uncurry (transferKernel b s)) :=
  (continuous_transferKernel_uncurry b s hs).measurable

end Kernel

/-! ## Part 3 — the induced operator on `L²`, its norm, adjoint and non-vanishing -/

section Operator

variable {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The product Haar measure on one slice's configurations `ι → MassGap.SUN.SU N`, as
`Measure.pi (fun _ => probHaar (MassGap.SUN.SU N))`. This is the measure both `L²` spaces of
`transferCLM` are taken against.

DERIVED: no numeral appears in the statement. -/
noncomputable def sliceHaar (ι : Type) [Fintype ι] (N : ℕ) :
    Measure (ι → MassGap.SUN.SU N) := Measure.pi fun _ => probHaar (MassGap.SUN.SU N)

/-- `sliceHaar ι N` is a probability measure: a finite product of probability measures, resolved by
 instance search after unfolding. This is what lets constants sit in `L²` and what
`SlabKernelOperator.kernelCLM` needs of both measures.

DERIVED: no numeral appears in the statement; total mass one is inside `IsProbabilityMeasure`. -/
instance isProbabilityMeasure_sliceHaar : IsProbabilityMeasure (sliceHaar ι N) := by
  unfold sliceHaar; infer_instance

/-- The continuous linear endomorphism of `Lp ℝ 2 (sliceHaar ι N)` induced by
`transferKernel b s`, as `SlabKernelOperator.kernelCLM` at that kernel with bound
`transferCap ι N b Cs`. Measurability comes from `measurable_transferKernel_uncurry`,
nonnegativity of the bound from `transferCap_pos`, and the pointwise bound from
`abs_transferKernel_le`.

Scope: domain and codomain are the same space, since both measures passed to `kernelCLM` are
`sliceHaar ι N`. The intra-slice function `s` is the caller's, carrying the hypotheses `hs`
(continuous) and `hsb` (bounded by `Cs`); both appear in the term, so operators built from different
proofs of the same facts are distinct terms.

DERIVED: `2` occurs twice, as the exponent of the `Lp` space at the domain and at the codomain. No
other numeral appears in the statement. -/
noncomputable def transferCLM (b : ℝ) (s : (ι → MassGap.SUN.SU N) → ℝ) (Cs : ℝ)
    (hs : Continuous s) (hsb : ∀ V, |s V| ≤ Cs) :
    Lp ℝ 2 (sliceHaar ι N) →L[ℝ] Lp ℝ 2 (sliceHaar ι N) :=
  kernelCLM (transferKernel b s) (transferCap ι N b Cs)
    (measurable_transferKernel_uncurry b s hs) (le_of_lt (transferCap_pos b Cs))
    (abs_transferKernel_le b s Cs hsb) (sliceHaar ι N) (sliceHaar ι N)

/-- `‖transferCLM b s Cs hs hsb‖ ≤ transferCap ι N b Cs`: the operator norm is bounded by the same
uniform cap as the kernel, by `SlabKernelOperator.norm_kernelCLM_le`. That bound is available
because `sliceHaar` is a probability measure.

Scope: an upper bound only — no lower bound on the norm is stated here, and
`transferCLM_ne_zero` is the separate statement that the operator is nonzero.

DERIVED: no numeral appears in the statement. -/
theorem norm_transferCLM_le (b : ℝ) (s : (ι → MassGap.SUN.SU N) → ℝ) (Cs : ℝ)
    (hs : Continuous s) (hsb : ∀ V, |s V| ≤ Cs) :
    ‖transferCLM b s Cs hs hsb‖ ≤ transferCap ι N b Cs :=
  norm_kernelCLM_le _ _ _ _ _ _ _

/-- `IsSelfAdjoint (transferCLM b s Cs hs hsb)`, at every real `b`, every bounded continuous `s` and
every `ι`, `N`. It is `SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm` fed with
`SliceTransfer.transferKernel_symm b s`, which holds with no hypothesis because `transferKernel`
splits the intra-slice weight evenly between its two arguments.

Scope: no sign condition on `b` is used — the hypothesis `0 ≤ b` that
`SliceTransfer.transferKernel_psd` requires is about positivity and plays no part here. This is
self-adjointness of the operator induced by `transferKernel`; it says nothing about
`SliceTrace.slabKernel` or about any partition function. It is also not a spectral statement: no
spectrum, eigenvalue or gap is asserted.

DERIVED: no numeral appears in the statement. -/
theorem isSelfAdjoint_transferCLM (b : ℝ) (s : (ι → MassGap.SUN.SU N) → ℝ) (Cs : ℝ)
    (hs : Continuous s) (hsb : ∀ V, |s V| ≤ Cs) :
    IsSelfAdjoint (transferCLM b s Cs hs hsb) :=
  isSelfAdjoint_kernelCLM_of_symm _ _ _ _ _ _ (transferKernel_symm b s)

/-- `ContinuousLinearMap.adjoint (transferCLM b s Cs hs hsb) = transferCLM b s Cs hs hsb`: the
adjoint is the operator itself, as an equation between continuous linear maps. It is
`isSelfAdjoint_transferCLM` transported across `ContinuousLinearMap.star_eq_adjoint`.

DERIVED: no numeral appears in the statement. -/
theorem adjoint_transferCLM (b : ℝ) (s : (ι → MassGap.SUN.SU N) → ℝ) (Cs : ℝ)
    (hs : Continuous s) (hsb : ∀ V, |s V| ≤ Cs) :
    ContinuousLinearMap.adjoint (transferCLM b s Cs hs hsb) = transferCLM b s Cs hs hsb := by
  have h := isSelfAdjoint_transferCLM b s Cs hs hsb
  rw [← ContinuousLinearMap.star_eq_adjoint]
  exact h

/-- `transferCLM b s Cs hs hsb ≠ 0`. The proof supplies `SlabKernelOperator.kernelCLM_ne_zero` with
the strictly positive lower bound `(transferCap ι N b Cs)⁻¹` on the kernel: each intra-slice
exponential is at least `exp (-Cs / 2)` and the cross exponential at least
`exp (-(|b| * (card ι * N)))`, and those reciprocate the cap exactly.

Scope: this also rules out the degenerate reading in which the `L²` space is zero, since a zero space
admits only the zero operator. It is a non-vanishing statement, not a lower bound on the norm.

DERIVED: `0` is the operator the conclusion excludes. No other numeral appears in the statement. -/
theorem transferCLM_ne_zero (b : ℝ) (s : (ι → MassGap.SUN.SU N) → ℝ) (Cs : ℝ)
    (hs : Continuous s) (hsb : ∀ V, |s V| ≤ Cs) :
    transferCLM b s Cs hs hsb ≠ 0 := by
  refine kernelCLM_ne_zero _ _ _ _ _ _ _ (inv_pos.mpr (transferCap_pos (ι := ι) (N := N) b Cs))
    (fun V W => ?_)
  have h1 : Real.exp (-Cs) ≤ Real.exp (-(s V) / 2) * Real.exp (-(s W) / 2) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hV := (abs_le.mp (hsb V)).2
    have hW := (abs_le.mp (hsb W)).2
    linarith
  have h2 : Real.exp (-(|b| * ((Fintype.card ι : ℝ) * (N : ℝ))))
      ≤ Real.exp (b * sliceForm V W) := by
    refine Real.exp_le_exp.mpr ?_
    have hle : -(|b| * ((Fintype.card ι : ℝ) * (N : ℝ))) ≤ b * sliceForm V W := by
      have habs : |b * sliceForm V W| ≤ |b| * ((Fintype.card ι : ℝ) * (N : ℝ)) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_sliceForm_le V W) (abs_nonneg b)
      exact (abs_le.mp habs).1
    exact hle
  have hcap : (transferCap ι N b Cs)⁻¹
      = Real.exp (-Cs) * Real.exp (-(|b| * ((Fintype.card ι : ℝ) * (N : ℝ)))) := by
    unfold transferCap
    rw [mul_inv, ← Real.exp_neg, ← Real.exp_neg]
  rw [hcap]
  unfold transferKernel
  calc Real.exp (-Cs) * Real.exp (-(|b| * ((Fintype.card ι : ℝ) * (N : ℝ))))
      ≤ (Real.exp (-(s V) / 2) * Real.exp (-(s W) / 2)) * Real.exp (b * sliceForm V W) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le
          (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = Real.exp (-(s V) / 2) * Real.exp (b * sliceForm V W) * Real.exp (-(s W) / 2) := by ring

end Operator

/-! ## Axiom footprints -/

#print axioms abs_hsRe_le
#print axioms continuous_reTrace
#print axioms continuous_hsRe_pair
#print axioms continuous_sliceForm
#print axioms abs_sliceForm_le
#print axioms transferCap
#print axioms transferCap_pos
#print axioms abs_transferKernel_le
#print axioms continuous_transferKernel_uncurry
#print axioms measurable_transferKernel_uncurry
#print axioms sliceHaar
#print axioms isProbabilityMeasure_sliceHaar
#print axioms transferCLM
#print axioms norm_transferCLM_le
#print axioms isSelfAdjoint_transferCLM
#print axioms adjoint_transferCLM
#print axioms transferCLM_ne_zero

end MassGap.SliceTransferSelfAdjoint
