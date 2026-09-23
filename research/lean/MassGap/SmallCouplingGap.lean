import Mathlib
import MassGap.TransferGaussian

/-!
# MassGap.SmallCouplingGap — an L² contraction for a kernel near a centre, and its regime

## The mechanism

On a probability measure, a mean-zero `f` annihilates any function of `V` alone, since it leaves the
`W` integral as a constant: `∫ c(V)·f(W) dW = c(V)·∫f = 0`. So only the deviation of each row
`K V ·` from its centre `c V` survives:

    ∫ f = 0  ⟹  |∫ K(V,W) f(W) dW| = |∫ (K(V,W) − c(V)) f(W) dW| ≤ δ · ∫|f| ≤ δ · ‖f‖₂.

That is `kernel_contracts_on_mean_zero`; squaring and integrating gives `integral_sq_contracts`,
`(∫ V, (∫ W, K V W · f W)^2) ≤ δ^2 · ∫ f^2`. The centre `c : X → ℝ` is a free argument, so `c = 1`
(the projection onto constants on a probability measure) and the row's own midrange are both
instances. No spectral theory enters: mean zero is a condition on `f` that does not require knowing
the kernel's top eigenvector.

These are statements about an integral kernel on a probability space. Nothing here constructs a
`Transfer.TransferData` or concludes `TransferGap.GapAt`.

## The regime

For the slice weight `K = e^{b·sliceForm}`, `SliceTransferSelfAdjoint.abs_sliceForm_le` gives
`|sliceForm| ≤ |ι|·N`, so `abs_sliceWeight_sub_one_le` puts the deviation from the centre `1` at
`δ = e^{b·|ι|·N} − 1`, and `deviation_lt_one_iff` is the exact equivalence
`δ < 1 ⟺ b·|ι|·N < log 2`.

`reach_is_inverse_in_slice_size` rewrites the condition at `b = β/N`: for any threshold constant `L`,
`(β/N)·(|ι|·N) < L ↔ β·|ι| < L`. The `N` cancels, so the admissible coupling is `β < L/|ι|`, inversely
proportional to the slice size, whatever `L` is.

## The best centre

§4 measures how much a different centre buys. `two_point_spread_le` bounds any centre from below by
half the spread of two points; `abs_sliceWeight_sub_cosh_le` takes the midrange centre `cosh M` with
half-range `sinh M` for `M = b·|ι|·N`; and `sinh_lt_exp_sub_one` shows `sinh x < e^x − 1` for `x > 0`,
so the midrange centre is strictly the better of the two. By `reach_is_inverse_in_slice_size` this
changes `L` and leaves the `L/|ι|` shape of the reach unchanged.
-/

namespace MassGap.SmallCouplingGap

open MeasureTheory

/-! ## 1. Cauchy–Schwarz against the constant -/

/-- `(∫ f)^2 ≤ ∫ f^2` on a probability measure, for `f` with `f` and `f^2` integrable. The proof
expands `∫ (f − ∫f)^2` as `∫f^2 − (∫f)^2` using `integral_const` at total mass `1`, and reads off
nonnegativity of the variance. Stated with explicit integrability hypotheses rather than through a
Hölder form.

DERIVED: all three `2`s are the same square — `f^2` in the integrability hypothesis and on the right,
and the square of the integral on the left; the inequality is the nonnegativity of the second central
moment. -/
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

/-- For a mean-zero integrable `f` and a kernel whose rows stay within `δ` of a centre `c`,
`|∫ W, K V W · f W| ≤ δ · ∫ W, |f W|`, at every `V`. The mean-zero hypothesis removes the `c V` term
from the integral, leaving the deviation, which is bounded pointwise by `δ · |f W|`.

The centre `c : X → ℝ` is a free argument: `c = 1` recovers the projection onto constants on a
probability measure, and the row's own midrange is another instance. `δ` is not required nonnegative
here; `hK` forces it so whenever `X` is inhabited.

DERIVED: `0` is the mean of `f`, the value that makes `∫ c V * f W ∂μ` vanish and so removes the
centre from the bound. `c` is the caller's centre and `δ` the caller's row bound. -/
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

/-- The `L²` form: under the same hypotheses plus `0 ≤ δ` and integrability of `f^2`,
`(∫ V, (∫ W, K V W · f W)^2) ≤ δ^2 · ∫ x, f x^2`. The pointwise bound of
`kernel_contracts_on_mean_zero` is squared, integrated against a constant right-hand side (so
`integral_mono_of_nonneg` suffices and no measurability of the parametric integral is needed), and
`sq_integral_le_integral_sq` converts the `L¹` norm of `f` into its `L²` norm.

DERIVED: `0` in `hδ` is what lets the pointwise bound be squared in the right direction; `0` in
`hmean` is the mean of `f`; the `2`s are all the same square — the squared inner integral, the squared
row bound `δ^2`, and `f^2` on the right. -/
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

/-- For `0 ≤ b`, the slice weight stays within `e^{M} − 1` of `1`, where `M = b·|ι|·N`:
`|exp (b · sliceForm V W) − 1| ≤ exp (b · (|ι| · N)) − 1`. `|sliceForm| ≤ |ι|·N` is
`SliceTransferSelfAdjoint.abs_sliceForm_le`, and the upper excursion dominates the lower because
`e^M + e^{−M} ≥ 2`. This supplies `hK` for `kernel_contracts_on_mean_zero` at the centre `1`.

DERIVED: `0` in `hb` is the sign `b` needs for the form's bound to survive multiplication; both `1`s
are the same centre, the value `exp (b · sliceForm)` takes when the form vanishes, so the statement
measures the row's deviation from it. -/
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

/-- `exp (b · (|ι| · N)) − 1 < 1 ↔ b · (|ι| · N) < Real.log 2`, for every real `b`, positive or not.
Both directions by `Real.exp_lt_exp` with `Real.exp_log` at `2`. An exact equivalence, not a rounded
threshold.

DERIVED: the first `1` is the centre the deviation is measured from; the second `1` is the ceiling the
deviation must clear for `integral_sq_contracts` to contract; `2` is `exp` of the resulting threshold,
i.e. the solution of `e^x − 1 = 1`. -/
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

/-- At `b = β/N`, the threshold condition loses its `N`:
`(β / N) · (|ι| · N) < L ↔ β · |ι| < L`, for any real `L` and any `N` with `(N : ℝ) ≠ 0`. The left
side is rewritten by `field_simp`, so the equivalence is an identity of the two sides rather than an
inequality argument. Read as a bound on `β`, it reads `β < L / |ι|` for whatever threshold constant
`L` a centre produces: the admissible coupling is inversely proportional to the slice size, and
changing the centre changes `L` without changing that shape.

DERIVED: `0` in `hN` is what `field_simp` needs to cancel the `N` of `b = β/N` against the `N` of
`|sliceForm| ≤ |ι|·N`. `L` is the caller's threshold. -/
theorem reach_is_inverse_in_slice_size {β L : ℝ} (hN : (N : ℝ) ≠ 0) :
    (β / (N : ℝ)) * ((Fintype.card ι : ℝ) * (N : ℝ)) < L
      ↔ β * (Fintype.card ι : ℝ) < L := by
  have hshape : (β / (N : ℝ)) * ((Fintype.card ι : ℝ) * (N : ℝ))
      = β * (Fintype.card ι : ℝ) := by
    field_simp
  rw [hshape]

#print axioms reach_is_inverse_in_slice_size


/-! ## 4. The best centre, and how little it buys -/

/-- `|a − b| ≤ 2 · max |a − c| |b − c|`, for all reals `a`, `b`, `c`. Triangle inequality on
`a − b = (a − c) − (b − c)`, with each term bounded by the maximum. Read as a lower bound on any
centre `c`: it cannot be closer than half the spread to both points at once. Stated on two points, so
it is an inequality rather than an existence claim over a supremum.

DERIVED: `2` is the number of terms the triangle inequality splits into, one per point, each bounded
by the same maximum. -/
theorem two_point_spread_le (a b c : ℝ) : |a - b| ≤ 2 * max |a - c| |b - c| := by
  have h1 : |a - c| ≤ max |a - c| |b - c| := le_max_left _ _
  have h2 : |b - c| ≤ max |a - c| |b - c| := le_max_right _ _
  have h3 : |a - b| ≤ |a - c| + |b - c| := by
    have : a - b = (a - c) - (b - c) := by ring
    rw [this]
    exact (abs_sub _ _).trans_eq rfl
  linarith

#print axioms two_point_spread_le

/-- For `0 ≤ b`, the slice weight stays within `sinh M` of `cosh M`, where `M = b·|ι|·N`:
`|exp (b · sliceForm V W) − cosh M| ≤ sinh M`. The row lies in `[e^{−M}, e^{M}]` by
`abs_sliceForm_le`, and that interval has midpoint `cosh M` and half-range `sinh M` by
`Real.cosh_eq` and `Real.sinh_eq`. This is the alternative `hK` for `kernel_contracts_on_mean_zero`,
at the midrange centre rather than at `1`.

DERIVED: `0` in `hb` is the sign `b` needs for the form's bound to survive multiplication. `cosh` and
`sinh` are the midpoint and half-range of `[e^{−M}, e^{M}]` by definition. -/
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

/-- `Real.sinh x < Real.exp x − 1` for `0 < x`, since `e^x + e^{−x} > 2` there. So at any positive
`M` the midrange half-range of `abs_sliceWeight_sub_cosh_le` is strictly smaller than the deviation
from `1` that `abs_sliceWeight_sub_one_le` gives: the midrange centre is the better of the two, and
raises the threshold constant `L` that `reach_is_inverse_in_slice_size` divides by `|ι|`.

DERIVED: `0` in `hx` is what makes `e^x > 1` and hence the strict inequality; `1` is the centre
`abs_sliceWeight_sub_one_le` uses, so `exp x − 1` is that lemma's bound at `x = M`. -/
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
