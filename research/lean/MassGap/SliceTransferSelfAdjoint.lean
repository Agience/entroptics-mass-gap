import Mathlib
import MassGap.SlabTransferAdjoint

/-!
# MassGap.SliceTransferSelfAdjoint — a CONCRETE self-adjoint bounded operator on `L²`, from the
tree's own Osterwalder–Seiler slice kernel

`SlabTransferAdjoint` proved the criterion — a symmetric bounded measurable kernel on one
probability space induces a self-adjoint bounded operator on `L²` — and then could not apply it to
`SliceTrace.slabKernel`, whose symmetry the tree neither proves nor refutes. This file applies it to
the kernel the tree DOES prove symmetric.

`SliceTransfer.transferKernel b s V W = e^{-s(V)/2} · e^{b · sliceForm V W} · e^{-s(W)/2}` is the
Osterwalder–Seiler slice-to-slice kernel in temporal gauge, and `SliceTransfer.transferKernel_symm`
proves `T(V,W) = T(W,V)` with no hypothesis at all — the intra-slice factor is split evenly between
the two arguments, which is exactly what `slabKernel` does not do.

## What is proved

* `abs_hsRe_le` — `|Re tr (A Bᴴ)| ≤ N` for two `SU N` elements. `CrossingIntegration.hsRe_coe_eq`
  rewrites the cross form as `Re tr (A B⁻¹)` and `WilsonAction.abs_re_trace_le` is the bound. This
  is the only genuinely new estimate here.
* `continuous_hsRe_pair`, `continuous_sliceForm`, `continuous_transferKernel_uncurry` — joint
  continuity, hence joint measurability, on the compact group. The cross form is continuous because
  it is `Re ∘ trace` of a group word, and `WilsonAction.continuous_wilsonDensity`'s own proof is the
  template.
* `abs_transferKernel_le` — `|T(V,W)| ≤ transferCap ι N b Cs`, uniform, given only a bound `Cs` on
  the intra-slice function `s`.
* **`transferCLM` and `isSelfAdjoint_transferCLM`** — the induced operator on `L²` of one slice's
  configurations against the product Haar probability measure, and **it is self-adjoint**. It is a
  genuine `ContinuousLinearMap` on a genuine Hilbert space, with `norm_transferCLM_le`.

## What this does NOT claim, named exactly

* **It is not the Wilson partition function's kernel.** `SliceTrace`'s header lists THREE
  differences between `slabKernel` and `transferKernel` — the axis links, the unsplit intra-slice
  weight, and the plaquette-count constant with the ordered-`Plaq` double counting — and removing
  the first is a change of variables in temporal gauge, which is `SliceTransfer`'s hypothesis `hg`
  and is discharged nowhere in the tree. **So this self-adjoint operator is not yet known to be the
  one whose trace is `Z`.** `SliceTrace.partition_eq_cycleIntegral` is about `slabKernel`, not this.
* **`s` is the caller's.** The intra-slice function is a parameter with two hypotheses (continuous,
  bounded). Instantiating it at `SliceTransfer.intraSliceAction` restricted to a slice is not done
  here; `SliceTransfer.intra_links_mem` is what says the restriction is well defined.
* **NOT POSITIVE.** `SliceTransfer.transferKernel_psd` proves the FINITE positive-semidefiniteness
  `0 ≤ ∑ᵢⱼ zᵢzⱼ T(Vᵢ,Vⱼ)` at `0 ≤ b`, which is positive-definiteness of the kernel as a function.
  That is NOT `0 ≤ ⟨f, T f⟩` for `f ∈ L²`: passing from finite families to an integral is a limit,
  and no limit is taken here. `SlabTransferAdjoint.FiniteGram` is the form that DOES give the
  integral statement with no limit, and `transferKernel` is not of that form — it is an infinite
  series of them. **The route is named and sized rather than walked:**
  `CharacterExpansion.hsRe_pow` writes `hsRe A B ^ k` as a FINITE sum of paired products
  `∑_α mono α A · mono α B`, and `CharacterExpansion.hasSum_wilsonWeight_paired` sums those with
  coefficients `b^k/k!`, nonnegative at `0 ≤ b`. Each partial sum is therefore a
  `SlabTransferAdjoint.FiniteGram` kernel, so `inner_kernelCLM_self_nonneg_of_finiteGram` applies to
  it; what is missing is (i) a uniform bound on `|mono α|` over `SU N`, and (ii) a uniform tail
  estimate for the exponential series on the bounded range `|sliceForm| ≤ card ι · N`, after which
  positivity passes to the limit because the quadratic form is continuous in the kernel's sup norm
  on a probability space. Neither is proved here.
* **No spectrum, no gap, no Hamiltonian.** Self-adjointness and a norm bound are not spectral
  statements, and `SlabTransferAdjoint`'s Part 4 is the proof that a Doeblin bound will not close
  that gap either.

## The degenerate regimes

* **`b = 0` and `s` constant** — the kernel is constant, so the operator is the rank-one averaging
  map and self-adjointness is `SlabTransferAdjoint.finiteGram_one`'s regime again. Self-adjointness
  here is NOT evidence against that: `transferKernel_symm` holds at every `b` and every `s`, so the
  theorem is not true only because of degeneracy — but neither does it rule degeneracy out.
* **`N = 1`** — `SU 1` is trivial, `hsRe` is constant and `L²` is one dimensional.
* **`ι` empty** — `sliceForm` is the empty sum, the configuration space is a point, `L²` is one
  dimensional and every operator on it is self-adjoint.

Self-adjointness is a property of the KERNEL's symmetry and is stated for every `b`, `s`, `ι`, `N`;
it does not distinguish the degenerate regimes from the others and is not claimed to.

No `sorry`, no new axioms. Foundational footprint only (`#print axioms` at the end).
Build: `python research/code/lean_build.py build MassGap.SliceTransferSelfAdjoint`.
-/

namespace MassGap.SliceTransferSelfAdjoint

open MeasureTheory
open MassGap MassGap.SliceTransfer MassGap.CharacterExpansion MassGap.CompactGauge
open MassGap.SlabKernelOperator MassGap.SlabTransferAdjoint

section Slice

variable {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Part 1 — the cross form is bounded and continuous on the group -/

/-- **`Re tr (A Bᴴ)` IS BOUNDED BY THE RANK.** `hsRe_coe_eq` says the cross form of two `SU N`
elements is the `Re tr` of the group word `A B⁻¹`, and `abs_re_trace_le` bounds that by `N`.

DERIVED: `N` is the rank, from `WilsonAction.abs_re_trace_le`; nothing is chosen. -/
theorem abs_hsRe_le (a b : MassGap.SUN.SU N) :
    |hsRe ((a : Matrix (Fin N) (Fin N) ℂ)) ((b : Matrix (Fin N) (Fin N) ℂ))| ≤ (N : ℝ) := by
  rw [MassGap.CrossingIntegration.hsRe_coe_eq]
  exact MassGap.WilsonAction.abs_re_trace_le _

/-- `Re tr` is continuous on the group — `WilsonAction.continuous_wilsonDensity`'s own step.

DERIVED: no numeral. -/
theorem continuous_reTrace :
    Continuous (fun g : MassGap.SUN.SU N => (Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re) :=
  Complex.continuous_re.comp continuous_subtype_val.matrix_trace

/-- **THE CROSS FORM IS JOINTLY CONTINUOUS.** Through `hsRe_coe_eq` it is `Re tr` of a group word,
and the group is topological.

DERIVED: no numeral. -/
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

/-- **THE AGGREGATED CROSS FORM IS JOINTLY CONTINUOUS.**

DERIVED: no numeral. -/
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
/-- **THE AGGREGATED CROSS FORM IS BOUNDED BY THE SLICE SIZE TIMES THE RANK.**

DERIVED: `Fintype.card ι` is the slice's own link count and `N` is the rank, from `abs_hsRe_le`.
Neither is chosen. -/
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

/-! ## Part 2 — the transfer kernel is bounded and continuous -/

section Kernel

variable {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **THE UNIFORM BOUND ON THE TRANSFER KERNEL.**

DERIVED: the `2` inside `transferKernel` is its own even split of the intra-slice factor between the
two arguments, and the two halves recombine to `Cs`; `Fintype.card ι` and `N` are the slice's link
count and the rank, from `abs_sliceForm_le`. `Cs` is the caller's bound on `s`. Nothing is chosen
here. -/
noncomputable def transferCap (ι : Type) [Fintype ι] (N : ℕ) (b Cs : ℝ) : ℝ :=
  Real.exp Cs * Real.exp (|b| * ((Fintype.card ι : ℝ) * (N : ℝ)))

omit [DecidableEq ι] in
/-- The cap is positive, hence nonnegative.

DERIVED: the `0` is the sign asserted; `Real.exp_pos` supplies it. -/
theorem transferCap_pos (b Cs : ℝ) : 0 < transferCap ι N b Cs := by
  unfold transferCap
  positivity

/-- **THE TRANSFER KERNEL IS BOUNDED, UNIFORMLY IN BOTH ARGUMENTS.**

DERIVED: the `2` is `transferKernel`'s own even split; `Cs` is the caller's bound on `s`. -/
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

/-- **THE TRANSFER KERNEL IS JOINTLY CONTINUOUS** whenever the intra-slice function is.

DERIVED: the `2` is `transferKernel`'s own even split of the intra-slice factor. -/
theorem continuous_transferKernel_uncurry (b : ℝ) (s : (ι → MassGap.SUN.SU N) → ℝ)
    (hs : Continuous s) :
    Continuous (fun p : ((ι → MassGap.SUN.SU N) × (ι → MassGap.SUN.SU N)) =>
      transferKernel b s p.1 p.2) := by
  unfold transferKernel
  exact (((Real.continuous_exp.comp (((hs.comp continuous_fst).neg).div_const 2))).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_sliceForm))).mul
    (Real.continuous_exp.comp (((hs.comp continuous_snd).neg).div_const 2))

/-- **THE TRANSFER KERNEL IS JOINTLY MEASURABLE.**

DERIVED: no numeral of its own. -/
theorem measurable_transferKernel_uncurry (b : ℝ) (s : (ι → MassGap.SUN.SU N) → ℝ)
    (hs : Continuous s) :
    Measurable (Function.uncurry (transferKernel b s)) :=
  (continuous_transferKernel_uncurry b s hs).measurable

end Kernel

/-! ## Part 3 — the operator, and it is self-adjoint -/

section Operator

variable {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **THE PRODUCT HAAR MEASURE ON ONE SLICE'S CONFIGURATIONS.**

DERIVED: no numeral. -/
noncomputable def sliceHaar (ι : Type) [Fintype ι] (N : ℕ) :
    Measure (ι → MassGap.SUN.SU N) := Measure.pi fun _ => probHaar (MassGap.SUN.SU N)

/-- It is a probability measure: a finite product of probability Haar measures.

DERIVED: no numeral. -/
instance isProbabilityMeasure_sliceHaar : IsProbabilityMeasure (sliceHaar ι N) := by
  unfold sliceHaar; infer_instance

/-- **THE SLICE TRANSFER OPERATOR.** A bounded linear ENDOMORPHISM of `L²` of one slice's
configurations — unlike `SlabKernelOperator.slabTransfer`, whose two spaces differ. The intra-slice
function `s` is the caller's, with the two hypotheses `hs` (continuous) and `hsb` (bounded).

DERIVED: the `2`s are the `L²` exponent; the cap is `abs_transferKernel_le`'s. -/
noncomputable def transferCLM (b : ℝ) (s : (ι → MassGap.SUN.SU N) → ℝ) (Cs : ℝ)
    (hs : Continuous s) (hsb : ∀ V, |s V| ≤ Cs) :
    Lp ℝ 2 (sliceHaar ι N) →L[ℝ] Lp ℝ 2 (sliceHaar ι N) :=
  kernelCLM (transferKernel b s) (transferCap ι N b Cs)
    (measurable_transferKernel_uncurry b s hs) (le_of_lt (transferCap_pos b Cs))
    (abs_transferKernel_le b s Cs hsb) (sliceHaar ι N) (sliceHaar ι N)

/-- **THE SLICE TRANSFER OPERATOR IS BOUNDED, WITH AN EXPLICIT NORM BOUND.**

DERIVED: as `transferCLM`'s. -/
theorem norm_transferCLM_le (b : ℝ) (s : (ι → MassGap.SUN.SU N) → ℝ) (Cs : ℝ)
    (hs : Continuous s) (hsb : ∀ V, |s V| ≤ Cs) :
    ‖transferCLM b s Cs hs hsb‖ ≤ transferCap ι N b Cs :=
  norm_kernelCLM_le _ _ _ _ _ _ _

/-- **THE SLICE TRANSFER OPERATOR IS SELF-ADJOINT.** This is the statement `SlabKernelOperator`
refused for `slabTransfer` and `SlabTransferAdjoint` could only make conditional on kernel symmetry:
here the symmetry is a theorem (`SliceTransfer.transferKernel_symm`, no hypothesis), so the
conclusion is unconditional.

It holds at EVERY real `b` — the sign condition `0 ≤ b` that `transferKernel_psd` needs is a
POSITIVITY hypothesis and self-adjointness does not use it.

**It is self-adjointness of THIS kernel, which is not `SliceTrace.slabKernel` and is not yet known
to be the kernel whose cyclic trace is `Z`.** The three differences are `SliceTrace`'s and the
first of them needs temporal gauge, a hypothesis in `SliceTransfer` and a theorem nowhere.

DERIVED: no numeral of its own. -/
theorem isSelfAdjoint_transferCLM (b : ℝ) (s : (ι → MassGap.SUN.SU N) → ℝ) (Cs : ℝ)
    (hs : Continuous s) (hsb : ∀ V, |s V| ≤ Cs) :
    IsSelfAdjoint (transferCLM b s Cs hs hsb) :=
  isSelfAdjoint_kernelCLM_of_symm _ _ _ _ _ _ (transferKernel_symm b s)

/-- **THE ADJOINT, IDENTIFIED CONCRETELY**: the operator is its own adjoint, not merely equal to
some adjoint.

DERIVED: no numeral of its own. -/
theorem adjoint_transferCLM (b : ℝ) (s : (ι → MassGap.SUN.SU N) → ℝ) (Cs : ℝ)
    (hs : Continuous s) (hsb : ∀ V, |s V| ≤ Cs) :
    ContinuousLinearMap.adjoint (transferCLM b s Cs hs hsb) = transferCLM b s Cs hs hsb := by
  have h := isSelfAdjoint_transferCLM b s Cs hs hsb
  rw [← ContinuousLinearMap.star_eq_adjoint]
  exact h

/-- **THE OPERATOR IS NOT THE ZERO OPERATOR.** The kernel is bounded below by the reciprocal cap, so
`SlabKernelOperator.kernelCLM_ne_zero` applies. Anti-vacuity for the domain as well: the zero space
admits only the zero operator.

DERIVED: the `0` is the operator excluded; the lower bound is `abs_transferKernel_le`'s cap read in
the other direction, via strict positivity of `transferKernel`. -/
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
