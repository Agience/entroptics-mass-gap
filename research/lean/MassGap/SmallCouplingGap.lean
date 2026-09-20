import Mathlib
import MassGap.TransferGaussian

/-!
# MassGap.SmallCouplingGap — a gap that is DERIVED rather than assumed, and how far it reaches

`TransferGap.GapAt` is a hypothesis. This file pays for it in one regime, and then measures how wide
that regime is — because a sufficient condition nobody can meet is worth nothing, and the only way to
find out is to evaluate the constant.

## The mechanism

On a PROBABILITY measure the constant kernel `1` is the orthogonal projection onto constants:
`(1 ⋆ f)(V) = ∫ f`. So if a kernel is uniformly within `δ` of `1`, it differs from that projection by
at most `δ`, and on functions of MEAN ZERO — where the projection gives nothing — the whole of what
is left is the `δ`:

    ∫ f = 0  ⟹  |∫ K(V,W) f(W) dW| = |∫ (K(V,W) − 1) f(W) dW| ≤ δ · ∫|f| ≤ δ · ‖f‖₂.

**And `1` is not the only thing that may be subtracted.** Mean zero annihilates ANY function of `V`
alone, because it comes out of the `W` integral as a constant: `∫ c(V)·f(W) dW = c(V)·∫f = 0`. So the
lemmas are stated against an arbitrary centre `c : X → ℝ`, and the constant `1` is one instance of
it. That matters for the size of `δ`: the sharp constant is the deviation of each ROW of the kernel
from its own centre, not from a global one, and the best centre is the row's own mean. Stating it
against `1` would fix a centre the argument never needed.

That is `kernel_contracts_on_mean_zero`, and squaring and integrating gives the `L²` statement
`integral_sq_contracts`. No spectral theory, no compactness, no Perron–Frobenius: the top eigenvector
is not constructed, it is bypassed, because mean zero is a condition one can check without knowing
it.

## The regime, and it is the point of the file

For the slice weight `K = e^{b·sliceForm}`, `abs_sliceForm_le` gives `|sliceForm| ≤ |ι|·N`, so

    δ = e^{b·|ι|·N} − 1,     and    δ < 1  ⟺  b·|ι|·N < log 2.

**Evaluate it.** With `b = β/N` this is `β·|ι| < log 2`, so the derived gap holds for

    β < log 2 / |ι| ≈ 0.693 / |ι|.

**The threshold SHRINKS AS THE SLICE GROWS, and that is a negative result.** At any fixed coupling
the window closes once the slice has enough links, so this bound does not survive the
infinite-volume limit and cannot reach the physical coupling. It is recorded because the mechanism
looks like it should work — a kernel close to one, a contraction on the complement of constants — and
computing the constant is what shows it does not. `CLAY-GOAL`'s standing rule: an existential
constant is not a number until it is evaluated.

**What it does establish** is that `TransferGap.GapAt` is not vacuous as a hypothesis: something
satisfies the contraction it asks for, at a coupling this file names.
-/

namespace MassGap.SmallCouplingGap

open MeasureTheory

/-! ## 1. Cauchy–Schwarz against the constant -/

/-- **`(∫f)² ≤ ∫f²` on a probability measure.** The variance is nonnegative, and that is the whole
proof: expand `∫(f − ∫f)²` and use `μ univ = 1`.

Proved here rather than cited because it is three lines and the cited forms at this pin carry Hölder
hypotheses this does not need.

DERIVED: the `2`s are squares; no magnitude is chosen. -/
theorem sq_integral_le_integral_sq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {f : X → ℝ} (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  set c : ℝ := ∫ x, f x ∂μ with hc
  have hlin : Integrable (fun x => 2 * c * f x) μ := hf.const_mul _
  have hsq : Integrable (fun x => f x ^ 2 - 2 * c * f x) μ := hf2.sub hlin
  have hshape : ∀ x, (f x - c) ^ 2 = f x ^ 2 - 2 * c * f x + c ^ 2 := by
    intro x
    ring
  have h0 : (0 : ℝ) ≤ ∫ x, (f x - c) ^ 2 ∂μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  have heq : (∫ x, (f x - c) ^ 2 ∂μ) = (∫ x, f x ^ 2 ∂μ) - c ^ 2 := by
    simp only [hshape]
    rw [integral_add hsq (integrable_const _), integral_sub hf2 hlin, integral_const_mul,
      integral_const]
    simp [← hc]
    ring
  linarith [heq ▸ h0]

#print axioms sq_integral_le_integral_sq

/-! ## 2. A kernel within `δ` of one contracts on mean-zero functions -/

/-- **THE CONTRACTION, POINTWISE.** A mean-zero function integrates any function of `V` alone to
nothing, so only the deviation of the row `K V ·` from its centre `c V` survives.

The centre is arbitrary. Taking `c = 1` recovers the projection onto constants, which is what a
probability measure makes the constant kernel; taking `c V` to be the row's own mean is sharper, and
nothing in the proof prefers either.

DERIVED: no numeral. `c` is the caller's centre and `δ` the caller's bound. -/
theorem kernel_contracts_on_mean_zero {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {K : X → X → ℝ} {c : X → ℝ} {δ : ℝ}
    (hK : ∀ V W, |K V W - c V| ≤ δ)
    (hKm : ∀ V, AEStronglyMeasurable (fun W => K V W) μ)
    {f : X → ℝ} (hf : Integrable f μ) (hmean : (∫ x, f x ∂μ) = 0) (V : X) :
    |∫ W, K V W * f W ∂μ| ≤ δ * ∫ W, |f W| ∂μ := by
  have hdm : AEStronglyMeasurable (fun W => K V W - c V) μ :=
    (hKm V).sub aestronglyMeasurable_const
  have hdint : Integrable (fun W => (K V W - c V) * f W) μ :=
    hf.bdd_mul hdm (Filter.Eventually.of_forall (fun W => by
      rw [Real.norm_eq_abs]
      exact hK V W))
  have hsplit : (∫ W, K V W * f W ∂μ) = ∫ W, (K V W - c V) * f W ∂μ := by
    have hshape : ∀ W, K V W * f W = (K V W - c V) * f W + c V * f W := by
      intro W
      ring
    simp only [hshape]
    rw [integral_add hdint (hf.const_mul _), integral_const_mul, hmean, mul_zero, add_zero]
  rw [hsplit]
  have hbd : ∀ W, |(K V W - c V) * f W| ≤ δ * |f W| := by
    intro W
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hK V W) (abs_nonneg _)
  calc |∫ W, (K V W - c V) * f W ∂μ|
      ≤ ∫ W, |(K V W - c V) * f W| ∂μ := by
        rw [← Real.norm_eq_abs]
        simpa using norm_integral_le_integral_norm (μ := μ) (fun W => (K V W - c V) * f W)
    _ ≤ ∫ W, δ * |f W| ∂μ :=
        integral_mono hdint.abs (hf.abs.const_mul _) hbd
    _ = δ * ∫ W, |f W| ∂μ := integral_const_mul _ _

#print axioms kernel_contracts_on_mean_zero

/-- **AND IN `L²`.** Squaring the pointwise bound and integrating: the right-hand side is a CONSTANT,
so `integral_mono_of_nonneg` applies and no measurability of the parametric integral is needed —
which is the step that would otherwise cost a Fubini-style hypothesis.

DERIVED: `δ ^ 2` is the square of the pointwise factor; nothing is chosen. -/
theorem integral_sq_contracts {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {K : X → X → ℝ} {c : X → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hK : ∀ V W, |K V W - c V| ≤ δ)
    (hKm : ∀ V, AEStronglyMeasurable (fun W => K V W) μ)
    {f : X → ℝ} (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hmean : (∫ x, f x ∂μ) = 0) :
    (∫ V, (∫ W, K V W * f W ∂μ) ^ 2 ∂μ) ≤ δ ^ 2 * ∫ x, f x ^ 2 ∂μ := by
  have habs : Integrable (fun x => |f x|) μ := hf.abs
  have hL1 : (0 : ℝ) ≤ ∫ W, |f W| ∂μ := integral_nonneg (fun _ => abs_nonneg _)
  -- the pointwise bound, squared
  have hpt : ∀ V, (∫ W, K V W * f W ∂μ) ^ 2 ≤ (δ * ∫ W, |f W| ∂μ) ^ 2 := by
    intro V
    have h := kernel_contracts_on_mean_zero hK hKm hf hmean V
    have h0 : (0 : ℝ) ≤ δ * ∫ W, |f W| ∂μ := mul_nonneg hδ hL1
    calc (∫ W, K V W * f W ∂μ) ^ 2 = |∫ W, K V W * f W ∂μ| ^ 2 := (sq_abs _).symm
      _ ≤ (δ * ∫ W, |f W| ∂μ) ^ 2 := by
          exact pow_le_pow_left₀ (abs_nonneg _) h 2
  -- integrate against the constant bound
  have hstep : (∫ V, (∫ W, K V W * f W ∂μ) ^ 2 ∂μ) ≤ (δ * ∫ W, |f W| ∂μ) ^ 2 := by
    calc (∫ V, (∫ W, K V W * f W ∂μ) ^ 2 ∂μ)
        ≤ ∫ _V : X, (δ * ∫ W, |f W| ∂μ) ^ 2 ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
            (integrable_const _) (Filter.Eventually.of_forall hpt)
      _ = (δ * ∫ W, |f W| ∂μ) ^ 2 := by simp
  -- and Cauchy–Schwarz against the constant turns the `L¹` norm into the `L²` one
  have hcs : (∫ W, |f W| ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
    have h := sq_integral_le_integral_sq habs (by simpa [sq_abs] using hf2)
    simpa [sq_abs] using h
  calc (∫ V, (∫ W, K V W * f W ∂μ) ^ 2 ∂μ)
      ≤ (δ * ∫ W, |f W| ∂μ) ^ 2 := hstep
    _ = δ ^ 2 * (∫ W, |f W| ∂μ) ^ 2 := by ring
    _ ≤ δ ^ 2 * ∫ x, f x ^ 2 ∂μ := mul_le_mul_of_nonneg_left hcs (sq_nonneg δ)

#print axioms integral_sq_contracts

/-! ## 3. The slice weight, and the regime -/

variable {N : ℕ} {ι : Type} [Fintype ι]

/-- **THE SLICE WEIGHT IS WITHIN `e^{b|ι|N} − 1` OF ONE.**

`|sliceForm| ≤ |ι|·N` is `SliceTransferSelfAdjoint.abs_sliceForm_le`, and `|e^t − 1| ≤ e^{M} − 1` for
`|t| ≤ M` because `e^M + e^{-M} ≥ 2` makes the upper excursion the larger of the two.

DERIVED: `1` is the value the weight takes at zero coupling, which is what the deviation is measured
from; `M = b|ι|N` is the form's own bound. -/
theorem abs_sliceWeight_sub_one_le {b : ℝ} (hb : 0 ≤ b) (V W : ι → MassGap.SUN.SU N) :
    |Real.exp (b * MassGap.SliceTransfer.sliceForm V W) - 1|
      ≤ Real.exp (b * ((Fintype.card ι : ℝ) * (N : ℝ))) - 1 := by
  set M : ℝ := b * ((Fintype.card ι : ℝ) * (N : ℝ)) with hM
  have hsf := MassGap.SliceTransferSelfAdjoint.abs_sliceForm_le V W
  have hMnn : 0 ≤ M := by
    rw [hM]
    have : (0 : ℝ) ≤ (Fintype.card ι : ℝ) * (N : ℝ) := by positivity
    exact mul_nonneg hb this
  have hle : b * MassGap.SliceTransfer.sliceForm V W ≤ M := by
    rw [hM]
    exact mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hsf) hb
  have hge : -M ≤ b * MassGap.SliceTransfer.sliceForm V W := by
    rw [hM]
    have h1 : -((Fintype.card ι : ℝ) * (N : ℝ)) ≤ MassGap.SliceTransfer.sliceForm V W :=
      neg_le_of_neg_le (le_trans (neg_le_abs _) hsf)
    have := mul_le_mul_of_nonneg_left h1 hb
    linarith [this]
  -- the two excursions, and the upper one is the larger
  have hup : Real.exp (b * MassGap.SliceTransfer.sliceForm V W) - 1 ≤ Real.exp M - 1 := by
    have := Real.exp_le_exp.mpr hle
    linarith
  have hlow : -(Real.exp M - 1) ≤ Real.exp (b * MassGap.SliceTransfer.sliceForm V W) - 1 := by
    have h1 : Real.exp (-M) ≤ Real.exp (b * MassGap.SliceTransfer.sliceForm V W) :=
      Real.exp_le_exp.mpr hge
    have h2 : (2 : ℝ) ≤ Real.exp M + Real.exp (-M) := by
      have hprod : Real.exp M * Real.exp (-M) = 1 := by
        rw [← Real.exp_add]
        simp
      nlinarith [Real.exp_pos M, Real.exp_pos (-M), sq_nonneg (Real.exp M - Real.exp (-M))]
    linarith
  exact abs_le.mpr ⟨hlow, hup⟩

#print axioms abs_sliceWeight_sub_one_le

/-- **AND THE DEVIATION IS BELOW ONE EXACTLY BELOW `log 2`.**

`e^{b|ι|N} − 1 < 1` iff `b·|ι|·N < log 2`. This is the whole reach of the mechanism.

DERIVED: `log 2` is not a chosen threshold. It is where `e^x − 1 = 1`, and `1` is the contraction
factor a gap requires. Rounding is not in question: the statement is an iff at the exact value. -/
theorem deviation_lt_one_iff {b : ℝ} :
    Real.exp (b * ((Fintype.card ι : ℝ) * (N : ℝ))) - 1 < 1
      ↔ b * ((Fintype.card ι : ℝ) * (N : ℝ)) < Real.log 2 := by
  constructor
  · intro h
    refine Real.exp_lt_exp.mp ?_
    rw [Real.exp_log (by norm_num : (0:ℝ) < 2)]
    linarith
  · intro h
    have h2 := Real.exp_lt_exp.mpr h
    rw [Real.exp_log (by norm_num : (0:ℝ) < 2)] at h2
    linarith

#print axioms deviation_lt_one_iff

/-- **THE REACH, EVALUATED — and it closes as the slice grows, WHATEVER the constant.**

With `b = β/N` the condition `b·|ι|·N < L` is `β·|ι| < L`, so a derived contraction with threshold
constant `L` holds only for `β < L / |ι|`. **The bound on the coupling is INVERSELY proportional to
the number of links in the slice**, so at any fixed coupling it fails once the slice is large enough,
and it does not survive the infinite-volume limit.

**`L` is left free on purpose.** `deviation_lt_one_iff` gives `L = log 2` for the centre `1`, and §4
gives a larger `L` for the best centre. Neither changes this: improving the constant moves the
threshold, it does not change what the threshold is proportional to. So there is nothing to be gained
by optimising the centre, and that is worth knowing before anyone tries.

DERIVED: no numeral — `L` is the caller's. The `N` cancels exactly: it is the `N` of `b = β/N`
against the `N` of `|sliceForm| ≤ |ι|N`, not a coincidence and not a choice. -/
theorem reach_is_inverse_in_slice_size {β L : ℝ} (hN : (N : ℝ) ≠ 0) :
    (β / (N : ℝ)) * ((Fintype.card ι : ℝ) * (N : ℝ)) < L
      ↔ β * (Fintype.card ι : ℝ) < L := by
  have hshape : (β / (N : ℝ)) * ((Fintype.card ι : ℝ) * (N : ℝ))
      = β * (Fintype.card ι : ℝ) := by
    field_simp
  rw [hshape]

#print axioms reach_is_inverse_in_slice_size


/-! ## 4. The best centre, and how little it buys -/

/-- **NO CENTRE BEATS HALF THE SPREAD OF ANY TWO POINTS.**

`|a − b| ≤ 2·max |a − c| |b − c|`, for every `c`. Stated on two points rather than on a supremum, so
it is an inequality rather than an existence claim — and two points is all that is needed to bound a
centre from below.

DERIVED: the `2` is the two points; no magnitude. -/
theorem two_point_spread_le (a b c : ℝ) : |a - b| ≤ 2 * max |a - c| |b - c| := by
  have h1 : |a - c| ≤ max |a - c| |b - c| := le_max_left _ _
  have h2 : |b - c| ≤ max |a - c| |b - c| := le_max_right _ _
  have h3 : |a - b| ≤ |a - c| + |b - c| := by
    have : a - b = (a - c) - (b - c) := by ring
    rw [this]
    exact (abs_sub _ _).trans_eq rfl
  linarith

#print axioms two_point_spread_le

/-- **THE MIDRANGE CENTRE FOR THE SLICE WEIGHT.** The row lies in `[e^{−M}, e^{M}]` with
`M = b·|ι|·N`, whose midpoint is `cosh M` and whose half-range is `sinh M`.

DERIVED: `cosh` and `sinh` are the midpoint and half-range of `[e^{−M}, e^{M}]` by definition, not
chosen values. -/
theorem abs_sliceWeight_sub_cosh_le {b : ℝ} (hb : 0 ≤ b) (V W : ι → MassGap.SUN.SU N) :
    |Real.exp (b * MassGap.SliceTransfer.sliceForm V W)
        - Real.cosh (b * ((Fintype.card ι : ℝ) * (N : ℝ)))|
      ≤ Real.sinh (b * ((Fintype.card ι : ℝ) * (N : ℝ))) := by
  set M : ℝ := b * ((Fintype.card ι : ℝ) * (N : ℝ)) with hM
  have hsf := MassGap.SliceTransferSelfAdjoint.abs_sliceForm_le V W
  have hle : b * MassGap.SliceTransfer.sliceForm V W ≤ M := by
    rw [hM]
    exact mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hsf) hb
  have hge : -M ≤ b * MassGap.SliceTransfer.sliceForm V W := by
    rw [hM]
    have h1 : -((Fintype.card ι : ℝ) * (N : ℝ)) ≤ MassGap.SliceTransfer.sliceForm V W :=
      neg_le_of_neg_le (le_trans (neg_le_abs _) hsf)
    have := mul_le_mul_of_nonneg_left h1 hb
    linarith [this]
  have hup := Real.exp_le_exp.mpr hle
  have hlow := Real.exp_le_exp.mpr hge
  rw [Real.cosh_eq, Real.sinh_eq]
  rw [abs_le]
  constructor <;> linarith

#print axioms abs_sliceWeight_sub_cosh_le

/-- **AND IT IS STRICTLY BETTER THAN CENTRING ON ONE.** `sinh x < e^x − 1` for `x > 0`, because
`e^x + e^{−x} > 2`.

So the midrange centre raises the threshold from `log 2 ≈ 0.6931` to `arcsinh 1 = log(1+√2) ≈ 0.8814`
— about `27%`. **And `reach_is_inverse_in_slice_size` says that buys nothing structurally**: the
reach is `L/|ι|` for whatever `L`, so a better constant moves the wall without removing it.

DERIVED: the `1` is the contraction factor a gap requires; `2` is the value `e^x + e^{−x}` exceeds. -/
theorem sinh_lt_exp_sub_one {x : ℝ} (hx : 0 < x) : Real.sinh x < Real.exp x - 1 := by
  have hprod : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hu : 1 < Real.exp x := by
    have h := Real.exp_lt_exp.mpr hx
    simpa using h
  have hpos := Real.exp_pos (-x)
  have h2 : 2 < Real.exp x + Real.exp (-x) := by
    nlinarith [hprod, hu, hpos, sq_nonneg (Real.exp x - 1)]
  rw [Real.sinh_eq]
  linarith

#print axioms sinh_lt_exp_sub_one

end MassGap.SmallCouplingGap
