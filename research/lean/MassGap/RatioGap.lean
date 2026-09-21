import Mathlib
import MassGap.SmallCouplingGap

/-!
# MassGap.RatioGap — vary the argument, and the constant moves while the shape does not

`SmallCouplingGap` bounds a kernel's action on mean-zero functions by its deviation from a centre,
and evaluates the reach: the derived contraction holds only for `β < L/|ι|`, inversely proportional
to the number of links in the slice. Its own docstring leaves the threshold constant `L` free and
says why: *"improving the constant moves the threshold, it does not change what the threshold is
proportional to."*

**That is an assertion about all future improvements, and this file tests it by making one.**

## The test

Centre the kernel at the LOW END of its range and the deviation is `hi − lo`; centre it at the
MIDPOINT and the deviation is `(hi − lo)/2`, half as large. That is a strictly better argument on the
same data — the sharpening `SmallCouplingGap` §4 establishes for the slice weight, applied here to a
general two-sided bound. It changes the separation condition from `hi < 2·lo` to `hi < 3·lo`, and at
the real kernel it changes `cap² < 2` to `cap² < 3`.

**And `threshold_shape` shows that changes nothing that matters.** For every constant `L`,

    2·(Cs + β·|ι|) < L   ↔   β < (L − 2·Cs) / (2·|ι|),

so the endpoint centre gives `L = log 2`, the midpoint centre gives `L = log 3`, and both give a
threshold inversely proportional to `|ι|`. The numerator moved by `log(3/2)`; the `1/|ι|` did not
move at all.

**So `SmallCouplingGap`'s claim survives a real attempt to break it**, and that is what this file is
for. It is a stability check on a negative result, not a new route to a gap.

## Why that is worth a file

A negative result derived from one argument invites the reply *"then use a better argument"*. The
reply is reasonable and it has to be answered by trying, not by asserting. Here the better argument
exists, is strictly better, is proved better, and moves the threshold by a constant factor while the
volume dependence is untouched. **The `1/|ι|` is therefore a property of the DATUM — a two-sided
bound on the kernel, which is exponential in `|ι|` because `transferCap = exp(Cs + |b|·|ι|·N)` — and
not of either argument built on it.**

That is the finding, and it is narrower than "no positivity argument can work". See the limits below.

## What the theorems here actually are

**Integral inequalities, not spectral theory.** `rayleigh_const_ge` bounds a double integral;
`rayleigh_meanZero_le` and `rayleigh_meanZero_le_of_norm_le_one` bound a quadratic form. None of them
mentions an operator, an eigenvalue or a spectrum, and none is proved from min–max.

The quadratic form on mean-zero functions is the quantity min–max would bound the second eigenvalue
by, **if** the kernel operator were self-adjoint and compact and the top eigenvalue isolated. This
file assumes none of that and proves none of it. `TwoSided` carries no symmetry hypothesis; the
tree's symmetry theorem (`SliceTransfer.transferKernel_symm`) is not used here; and nothing in the
tree establishes compactness of `transferCLM` or that its spectrum has an isolated top. **So the
separation conditions below are conditions on an integral inequality, and calling them a spectral
gap would be a claim this file does not make.**

## ⚠ Limits, stated exactly

* **Nothing here concludes `TransferGap.GapAt`**, and neither does `SmallCouplingGap` — its own §
  header says only that `GapAt` "is not vacuous as a hypothesis".
* **`separates_iff_*` are arithmetic equivalences**, proved by `linarith`, between two inequalities
  on reals. Both sides of the estimate they compare are slack, so failing the condition implies
  nothing about any spectrum.
* **Two centres are not all centres.** What is proved is that one specific improvement moves only the
  constant. A third argument could in principle do better, and this file does not exclude that; it
  removes the cheapest reason to expect it.
-/

namespace MassGap.RatioGap

open MeasureTheory

/-! ## 1. The datum: a two-sided bound, and the two ways to centre it -/

/-- **A TWO-SIDED BOUND ON A KERNEL**, named so that what the argument consumes is visible in the
statement rather than spread across hypotheses. **No symmetry is assumed** — see the module header on
why that rules out reading anything here spectrally.

DERIVED: no numeral; `lo` and `hi` are the caller's. -/
structure TwoSided {X : Type*} (K : X → X → ℝ) (lo hi : ℝ) : Prop where
  /-- Every entry is at least `lo`. -/
  lo_le : ∀ V W, lo ≤ K V W
  /-- Every entry is at most `hi`. -/
  le_hi : ∀ V W, K V W ≤ hi

/-- **CENTRED AT THE LOW END**, the deviation is the full width. This is the naive reading of a
two-sided bound and it is the one the sharper centre below beats.

DERIVED: no numeral. -/
theorem TwoSided.abs_sub_lo_le {X : Type*} {K : X → X → ℝ} {lo hi : ℝ}
    (h : TwoSided K lo hi) (V W : X) : |K V W - lo| ≤ hi - lo := by
  have hlo := h.lo_le V W
  have hhi := h.le_hi V W
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

#print axioms TwoSided.abs_sub_lo_le

/-- **CENTRED AT THE MIDPOINT, THE DEVIATION IS HALVED.** Strictly better than
`TwoSided.abs_sub_lo_le` whenever `lo < hi`, and this is the improvement the whole file is a test of.

It is `SmallCouplingGap`'s own sharpening — `two_point_spread_le` and `abs_sliceWeight_sub_cosh_le`
make the same move for the slice weight — read here at the level of a general two-sided bound, where
it is the elementary fact that the midpoint of an interval is the point furthest from both ends by
the least amount.

DERIVED: the `2`s are the midpoint and the half-width of an interval, not chosen tolerances. -/
theorem TwoSided.abs_sub_mid_le {X : Type*} {K : X → X → ℝ} {lo hi : ℝ}
    (h : TwoSided K lo hi) (V W : X) :
    |K V W - (lo + hi) / 2| ≤ (hi - lo) / 2 := by
  have hlo := h.lo_le V W
  have hhi := h.le_hi V W
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

#print axioms TwoSided.abs_sub_mid_le

/-- **AND IT IS STRICTLY BETTER**, not merely no worse — the negative control for using it.

DERIVED: the `2` is the half-width's; the strictness is `lo < hi`. -/
theorem midpoint_is_strictly_better {lo hi : ℝ} (h : lo < hi) :
    (hi - lo) / 2 < hi - lo := by linarith

#print axioms midpoint_is_strictly_better

/-! ## 2. What a centred bound gives on mean-zero functions -/

/-- **THE CONSTANT FUNCTION ALREADY SEES `lo`.** On a probability measure `∫∫K ≥ lo`.

This is the quantity a Rayleigh quotient at the constant vector would be. It is stated and proved as
a double integral, with no operator in sight, and the module header says why that distinction is kept.

DERIVED: `lo` is the caller's; the unit mass is `IsProbabilityMeasure`'s. -/
theorem rayleigh_const_ge {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {K : X → X → ℝ} {lo hi : ℝ} (h : TwoSided K lo hi)
    (hKi : ∀ V, Integrable (fun W => K V W) μ)
    (hrow : Integrable (fun V => ∫ W, K V W ∂μ) μ) :
    lo ≤ ∫ V, (∫ W, K V W ∂μ) ∂μ := by
  have hinner : ∀ V, lo ≤ ∫ W, K V W ∂μ := by
    intro V
    simpa using integral_mono (integrable_const lo) (hKi V) (fun W => h.lo_le V W)
  simpa using integral_mono (integrable_const lo) hrow hinner

#print axioms rayleigh_const_ge

/-- **THE QUADRATIC FORM ON MEAN-ZERO FUNCTIONS, AT ANY CENTRE.** The centre enters only through the
deviation `δ`, which is why the two centres above can be compared by substituting into one theorem.

DERIVED: no numeral. The exponent `2` is the `L¹` norm appearing once for each copy of `f`. -/
theorem meanZero_form_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {K : X → X → ℝ} {c : X → ℝ} {δ : ℝ}
    (hK : ∀ V W, |K V W - c V| ≤ δ)
    (hKm : ∀ V, AEStronglyMeasurable (fun W => K V W) μ)
    {f : X → ℝ} (hf : Integrable f μ) (hmean : (∫ x, f x ∂μ) = 0)
    (hprod : Integrable (fun V => f V * ∫ W, K V W * f W ∂μ) μ) :
    |∫ V, f V * (∫ W, K V W * f W ∂μ) ∂μ| ≤ δ * (∫ x, |f x| ∂μ) ^ 2 := by
  have hrow : ∀ V, |∫ W, K V W * f W ∂μ| ≤ δ * ∫ x, |f x| ∂μ :=
    fun V => MassGap.SmallCouplingGap.kernel_contracts_on_mean_zero hK hKm hf hmean V
  have hpt : ∀ V, |f V * ∫ W, K V W * f W ∂μ| ≤ (δ * ∫ x, |f x| ∂μ) * |f V| := by
    intro V
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hrow V) (abs_nonneg _)
  calc |∫ V, f V * (∫ W, K V W * f W ∂μ) ∂μ|
      ≤ ∫ V, |f V * ∫ W, K V W * f W ∂μ| ∂μ := by
        rw [← Real.norm_eq_abs]
        simpa using norm_integral_le_integral_norm (μ := μ)
          (fun V => f V * ∫ W, K V W * f W ∂μ)
    _ ≤ ∫ V, (δ * ∫ x, |f x| ∂μ) * |f V| ∂μ :=
        integral_mono hprod.abs (hf.abs.const_mul _) hpt
    _ = δ * (∫ x, |f x| ∂μ) ^ 2 := by
        rw [integral_const_mul]
        ring

#print axioms meanZero_form_le

/-- **AND IN `L²`, WHICH IS THE NORMALISATION THE COMPARISON NEEDS.** Cauchy–Schwarz on a probability
measure turns the `L¹` factor into the `L²` one:
`(∫|f|)² ≤ ∫|f|² = ∫f² ≤ 1`, via `SmallCouplingGap.sq_integral_le_integral_sq`.

Without this step the bound above is an `L¹` statement being compared with an `L²` normalisation, and
the comparison would not be like for like.

DERIVED: the `1` is the unit `L²` normalisation the caller supplies; the `2`s are squares. -/
theorem meanZero_form_le_of_norm_le_one {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {K : X → X → ℝ} {c : X → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hK : ∀ V W, |K V W - c V| ≤ δ)
    (hKm : ∀ V, AEStronglyMeasurable (fun W => K V W) μ)
    {f : X → ℝ} (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hmean : (∫ x, f x ∂μ) = 0) (hnorm : (∫ x, f x ^ 2 ∂μ) ≤ 1)
    (hprod : Integrable (fun V => f V * ∫ W, K V W * f W ∂μ) μ) :
    |∫ V, f V * (∫ W, K V W * f W ∂μ) ∂μ| ≤ δ := by
  have habs2 : Integrable (fun x => |f x| ^ 2) μ := by
    simpa [sq_abs] using hf2
  have hcs : (∫ x, |f x| ∂μ) ^ 2 ≤ ∫ x, |f x| ^ 2 ∂μ :=
    MassGap.SmallCouplingGap.sq_integral_le_integral_sq hf.abs habs2
  have hsq : (∫ x, |f x| ^ 2 ∂μ) = ∫ x, f x ^ 2 ∂μ := by
    simp [sq_abs]
  have hle : (∫ x, |f x| ∂μ) ^ 2 ≤ 1 := by
    rw [hsq] at hcs
    linarith
  calc |∫ V, f V * (∫ W, K V W * f W ∂μ) ∂μ|
      ≤ δ * (∫ x, |f x| ∂μ) ^ 2 := meanZero_form_le hK hKm hf hmean hprod
    _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hle hδ
    _ = δ := mul_one δ

#print axioms meanZero_form_le_of_norm_le_one

/-! ## 3. The two separation conditions the two centres give -/

/-- **ENDPOINT CENTRE: separation needs the kernel within a factor of TWO of itself.**

DERIVED: the `2` is the arithmetic of `hi − lo < lo`, not a chosen tolerance. -/
theorem separates_iff_hi_lt_two_lo {lo hi : ℝ} : hi - lo < lo ↔ hi < 2 * lo := by
  constructor <;> intro h <;> linarith

#print axioms separates_iff_hi_lt_two_lo

/-- **MIDPOINT CENTRE: a factor of THREE.** The strictly better argument buys a strictly weaker
condition, which is what makes the comparison in §5 a real test rather than a restatement.

DERIVED: the `2` is the half-width; the `3` is what `(hi − lo)/2 < lo` rearranges to. Neither is
chosen. -/
theorem separates_iff_hi_lt_three_lo {lo hi : ℝ} : (hi - lo) / 2 < lo ↔ hi < 3 * lo := by
  constructor <;> intro h <;> linarith

#print axioms separates_iff_hi_lt_three_lo

/-- A reciprocal pair of bounds turns either condition into one on the cap, at the factor `A`.

DERIVED: `A` is the caller's factor — `2` from the endpoint centre, `3` from the midpoint. -/
theorem cap_condition {c A : ℝ} (hc : 0 < c) : c < A * c⁻¹ ↔ c ^ 2 < A := by
  rw [show A * c⁻¹ = A / c by ring, lt_div_iff₀ hc, sq]

#print axioms cap_condition

/-! ## 4. And each is a linear condition on the exponent -/

/-- The cap is a single exponential — `rfl`-level against `SliceTransferSelfAdjoint.transferCap`.

DERIVED: no numeral of its own. -/
theorem transferCap_eq (ι : Type) [Fintype ι] (N : ℕ) (b Cs : ℝ) :
    MassGap.SliceTransferSelfAdjoint.transferCap ι N b Cs
      = Real.exp Cs * Real.exp (|b| * ((Fintype.card ι : ℝ) * (N : ℝ))) := rfl

#print axioms transferCap_eq

/-- **`cap² < A` IS LINEAR IN THE EXPONENT**, at every positive factor `A` — so the endpoint centre
(`A = 2`) and the midpoint centre (`A = 3`) differ only in `log A`.

DERIVED: the `2` is the square of the cap; `A` and `log A` are the caller's factor. -/
theorem cap_sq_lt_iff (v Nr b Cs A : ℝ) (hA : 0 < A) :
    (Real.exp Cs * Real.exp (|b| * (v * Nr))) ^ 2 < A
      ↔ 2 * (Cs + |b| * (v * Nr)) < Real.log A := by
  rw [← Real.exp_add, sq, ← Real.exp_add,
    show Cs + |b| * (v * Nr) + (Cs + |b| * (v * Nr)) = 2 * (Cs + |b| * (v * Nr)) by ring]
  constructor
  · intro h
    have h2 := Real.log_lt_log (Real.exp_pos _) h
    rwa [Real.log_exp] at h2
  · intro h
    calc Real.exp (2 * (Cs + |b| * (v * Nr)))
        < Real.exp (Real.log A) := Real.exp_lt_exp.mpr h
      _ = A := Real.exp_log hA

#print axioms cap_sq_lt_iff

/-- **THE RANK CANCELS**, as in `SmallCouplingGap.reach_is_inverse_in_slice_size`: the `N` of
`b = β/N` meets the `N` of `|sliceForm| ≤ |ι|·N`.

The extra hypothesis `0 ≤ β` is not slack borrowed from the sibling: `transferCap` carries `|b|`
where `deviation_lt_one_iff` carries a bare `b`, so the absolute value has to be discharged here and
the sibling never had one.

DERIVED: the `2` is `cap_sq_lt_iff`'s square; `L` is the caller's threshold constant. -/
theorem rank_cancels {β Cs v Nr L : ℝ} (hβ : 0 ≤ β) (hN : 0 < Nr) :
    2 * (Cs + |β / Nr| * (v * Nr)) < L ↔ 2 * (Cs + β * v) < L := by
  have hshape : |β / Nr| * (v * Nr) = β * v := by
    rw [abs_div, abs_of_nonneg hβ, abs_of_pos hN]
    field_simp
  rw [hshape]

#print axioms rank_cancels

/-! ## 5. ⭐ The test, and its result -/

/-- **⭐ THE THRESHOLD IS `1/|ι|` FOR EVERY CONSTANT `L`.**

This is the statement the file exists to make, and `L` is free on purpose — exactly as it is free in
`SmallCouplingGap.reach_is_inverse_in_slice_size`, and for the same reason. The endpoint centre
supplies `L = log 2`, the midpoint centre supplies `L = log 3`, and **any future sharpening supplies
some other `L` and lands here too.**

The numerator is what an argument can move. The `1/(2·v)` is what it cannot.

DERIVED: the `2`s are `cap_sq_lt_iff`'s square, carried through the rearrangement. `L` is the
caller's and nothing about it is chosen here. -/
theorem threshold_shape {β Cs v L : ℝ} (hv : 0 < v) :
    2 * (Cs + β * v) < L ↔ β < (L - 2 * Cs) / (2 * v) := by
  rw [lt_div_iff₀ (by linarith : (0 : ℝ) < 2 * v)]
  constructor <;> intro h <;> linarith

#print axioms threshold_shape

/-- **THE ENDPOINT CENTRE'S THRESHOLD.**

DERIVED: `log 2` is `separates_iff_hi_lt_two_lo`'s factor read through `cap_sq_lt_iff`. -/
theorem threshold_at_endpoint_centre {β Cs v : ℝ} (hv : 0 < v) :
    2 * (Cs + β * v) < Real.log 2 ↔ β < (Real.log 2 - 2 * Cs) / (2 * v) :=
  threshold_shape hv

#print axioms threshold_at_endpoint_centre

/-- **THE MIDPOINT CENTRE'S THRESHOLD — a different numerator, the same `1/v`.**

DERIVED: `log 3` is `separates_iff_hi_lt_three_lo`'s factor read through `cap_sq_lt_iff`. -/
theorem threshold_at_midpoint_centre {β Cs v : ℝ} (hv : 0 < v) :
    2 * (Cs + β * v) < Real.log 3 ↔ β < (Real.log 3 - 2 * Cs) / (2 * v) :=
  threshold_shape hv

#print axioms threshold_at_midpoint_centre

/-- **⭐ SO THE BETTER ARGUMENT IS BETTER, AND BY A BOUNDED AMOUNT.** The midpoint centre admits
strictly more couplings than the endpoint centre at every slice size — the improvement is real — and
the ratio of the two thresholds is `log 3 / log 2` at `Cs = 0`, a constant, **independent of `v`**.

An improvement that multiplied the threshold by a constant cannot rescue a threshold that is
proportional to `1/v`, and this is that statement.

DERIVED: `log 2` and `log 3` are the two centres' factors; the `2`s are the square and the
rearrangement. Nothing is chosen. -/
theorem midpoint_admits_strictly_more {Cs v : ℝ} (hv : 0 < v) :
    (Real.log 2 - 2 * Cs) / (2 * v) < (Real.log 3 - 2 * Cs) / (2 * v) := by
  have h2v : (0 : ℝ) < 2 * v := by linarith
  have hlog : Real.log 2 < Real.log 3 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [div_lt_div_iff₀ h2v h2v]
  nlinarith [hlog, h2v]

#print axioms midpoint_admits_strictly_more

/-! ## 6. Anti-vacuity, in both directions -/

/-- **THE THRESHOLD IS NOT EMPTY**, and not only in the free case. `Cs = 1/4` is a genuine bound on a
non-zero intra-slice action, and at one link `β = 1/20` still qualifies against `log 2`.

The earlier witness used `Cs = 0`, which forces `s ≡ 0` — the free theory — and so exhibited only the
degenerate sub-family. This one does not.

CHOSEN: `Cs = 1/4`, `v = 1` and `β = 1/20` are a witness with room to spare against `log 2 ≈ 0.6931`;
`Cs` is deliberately non-zero so the witness is not the free case, and none of the three carries any
other role. -/
theorem threshold_is_satisfiable :
    2 * ((1 / 4 : ℝ) + (1 / 20) * 1) < Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

#print axioms threshold_is_satisfiable

/-- **⛔ AND IT IS GENUINELY LOST IN THE VOLUME, AT EVERY CONSTANT `L`.** At any fixed positive
coupling there is a slice size past which the condition fails — and because `L` is free, this covers
the endpoint centre, the midpoint centre and every sharpening that supplies some other `L`.

DERIVED: no numeral of its own; the `2` is `threshold_shape`'s and `L` is the caller's. -/
theorem threshold_fails_at_large_slices {β Cs L : ℝ} (hβ : 0 < β) :
    ∃ v : ℝ, 0 < v ∧ ¬ (2 * (Cs + β * v) < L) := by
  obtain ⟨v, hv⟩ := exists_gt (max ((L - 2 * Cs) / (2 * β)) 0)
  refine ⟨v, lt_of_le_of_lt (le_max_right _ _) hv, ?_⟩
  rw [not_lt]
  have hvb : (L - 2 * Cs) / (2 * β) < v := lt_of_le_of_lt (le_max_left _ _) hv
  rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * β)] at hvb
  linarith

#print axioms threshold_fails_at_large_slices

end MassGap.RatioGap
