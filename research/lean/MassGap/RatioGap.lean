import Mathlib
import MassGap.SmallCouplingGap

/-!
# MassGap.RatioGap — two centres for a two-sided kernel bound, and the threshold each gives

A `TwoSided K lo hi` is the statement that every entry of `K : X → X → ℝ` lies in `[lo, hi]`. Two
ways of centring it are compared.

* `TwoSided.abs_sub_lo_le` centres at `lo` and gives deviation `hi − lo`.
* `TwoSided.abs_sub_mid_le` centres at `(lo + hi)/2` and gives deviation `(hi − lo)/2`.
* `midpoint_is_strictly_better` is `(hi − lo)/2 < hi − lo` whenever `lo < hi`.

`meanZero_form_le` turns a deviation bound `δ` into `|∫ f·(Kf)| ≤ δ·(∫|f|)²` for mean-zero `f`, and
`meanZero_form_le_of_norm_le_one` converts the `L¹` factor to `L²` by Cauchy–Schwarz, giving
`|∫ f·(Kf)| ≤ δ` when `∫ f² ≤ 1`. `rayleigh_const_ge` is the companion at the constant function:
`lo ≤ ∫∫K` on a probability measure.

The two centres give two separation conditions — `separates_iff_hi_lt_two_lo` (`hi < 2·lo`) and
`separates_iff_hi_lt_three_lo` (`hi < 3·lo`) — which `cap_condition` and `cap_sq_lt_iff` turn into
`cap² < A` and then into a linear condition on the exponent. `transferCap_eq` identifies the cap with
`exp Cs · exp (|b|·|ι|·N)`, `rank_cancels` cancels the `N` of `b = β/N` against the `N` in the
exponent, and `threshold_shape` rearranges the result: for every constant `L`,

    2·(Cs + β·v) < L   ↔   β < (L − 2·Cs) / (2·v),

so the coupling threshold is inversely proportional to `v` at every `L`.
`threshold_at_endpoint_centre` and `threshold_at_midpoint_centre` are the instances at `L = log 2`
and `L = log 3`, `midpoint_admits_strictly_more` compares them, `threshold_is_satisfiable` exhibits a
point satisfying the first, and `threshold_fails_at_large_slices` shows that at any fixed positive
`β` and any `L` some positive `v` fails the condition.

## Scope

These are inequalities between integrals and between real numbers. No statement mentions an operator,
an eigenvalue or a spectrum, and none is proved from a min–max principle. `TwoSided` carries no
symmetry hypothesis, so the kernel it describes need not be symmetric, and the quadratic form on
mean-zero functions is not tied here to a second eigenvalue of anything.

`separates_iff_hi_lt_two_lo` and `separates_iff_hi_lt_three_lo` are `linarith` equivalences between
two inequalities on reals. What is compared is two centres, so the results fix the threshold constant
that each of those two produces and nothing about any other centre.
-/

namespace MassGap.RatioGap

open MeasureTheory

/-! ## 1. The datum: a two-sided bound, and the two ways to centre it -/

/-- A `Prop`-valued structure on a kernel `K : X → X → ℝ` and two reals: every entry is at least `lo`
and at most `hi`. Named so that what the arguments below consume is one hypothesis rather than
several.

No symmetry, measurability, positivity or continuity of `K` is assumed, and `X` carries no structure
beyond being a type. Nothing requires `lo ≤ hi`, although the two fields together force it when `X`
is nonempty.

DERIVED: no numeral; `lo` and `hi` are the caller's. -/
structure TwoSided {X : Type*} (K : X → X → ℝ) (lo hi : ℝ) : Prop where
  /-- Every entry is at least `lo`. -/
  lo_le : ∀ V W, lo ≤ K V W
  /-- Every entry is at most `hi`. -/
  le_hi : ∀ V W, K V W ≤ hi

/-- Centred at the low end, the deviation is the full width: `|K V W - lo| ≤ hi - lo` at every pair
of arguments. Both sides of `abs_le` are `linarith` from the two fields of `TwoSided`.

DERIVED: no numeral. `lo` and `hi` are the structure's. -/
theorem TwoSided.abs_sub_lo_le {X : Type*} {K : X → X → ℝ} {lo hi : ℝ}
    (h : TwoSided K lo hi) (V W : X) : |K V W - lo| ≤ hi - lo := by
  have hlo := h.lo_le V W
  have hhi := h.le_hi V W
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

#print axioms TwoSided.abs_sub_lo_le

/-- Centred at the midpoint, the deviation is the half-width:
`|K V W - (lo + hi)/2| ≤ (hi - lo)/2` at every pair of arguments. Same `linarith` proof as
`TwoSided.abs_sub_lo_le`, at the other centre.

The same move `SmallCouplingGap`'s `two_point_spread_le` and `abs_sliceWeight_sub_cosh_le` make for
the slice weight, stated here for a general two-sided bound.

DERIVED: the two `2`s are the midpoint of an interval and its half-width; both are forced by the
interval `[lo, hi]` and neither is a chosen tolerance. -/
theorem TwoSided.abs_sub_mid_le {X : Type*} {K : X → X → ℝ} {lo hi : ℝ}
    (h : TwoSided K lo hi) (V W : X) :
    |K V W - (lo + hi) / 2| ≤ (hi - lo) / 2 := by
  have hlo := h.lo_le V W
  have hhi := h.le_hi V W
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

#print axioms TwoSided.abs_sub_mid_le

/-- `(hi - lo) / 2 < hi - lo` whenever `lo < hi`. One `linarith` step; the strict hypothesis is what
makes the conclusion strict rather than non-strict.

So the midpoint deviation is strictly smaller than the endpoint deviation on any nondegenerate
interval — the control for preferring `TwoSided.abs_sub_mid_le`.

DERIVED: the `2` is the half-width's, carried from `TwoSided.abs_sub_mid_le`; it is the only
numeral, and the strictness comes from the hypothesis `lo < hi`. -/
theorem midpoint_is_strictly_better {lo hi : ℝ} (h : lo < hi) :
    (hi - lo) / 2 < hi - lo := by linarith

#print axioms midpoint_is_strictly_better

/-! ## 2. What a centred bound gives on mean-zero functions -/

/-- On a probability measure, `lo ≤ ∫ V, (∫ W, K V W ∂μ) ∂μ`. Twice `integral_mono` against the
constant `lo`, using the `lo_le` field of `TwoSided`; the two integrability hypotheses `hKi` and
`hrow` are what let the comparison be made on each integral.

A double integral, not an operator applied to a constant vector; no eigenvalue or Rayleigh quotient
appears in the statement. `hi` enters only through the `TwoSided` argument and plays no part in the
conclusion.

DERIVED: no numeral. `lo` and `hi` are the caller's, and the unit total mass used by the two
`integral_mono` steps comes from `IsProbabilityMeasure`, not from a literal in the statement. -/
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

/-- For `f` integrable with `∫ f = 0`, and a kernel whose deviation from a centre `c` is at most `δ`
everywhere,

    |∫ V, f V * (∫ W, K V W * f W ∂μ) ∂μ|  ≤  δ * (∫ x, |f x| ∂μ) ^ 2.

`SmallCouplingGap.kernel_contracts_on_mean_zero` bounds the inner integral by `δ · ∫|f|` at each `V`;
multiplying by `|f V|` and integrating gives the outer factor.

The centre `c` enters only through `δ`, which is what lets the two centres above be compared by
substituting into this one statement. `c` may depend on `V`, and no symmetry or positivity of `K` is
used.

DERIVED: `0` is the mean `f` is required to have, in `hmean`. The exponent `2` counts the two copies
of `f` in the double integral, one from each factor, each contributing a `∫|f|`; it is not a
tolerance. -/
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

/-- The same bound with the `L¹` factor removed: under the extra hypotheses `0 ≤ δ` and
`∫ f² ≤ 1`,

    |∫ V, f V * (∫ W, K V W * f W ∂μ) ∂μ|  ≤  δ.

`SmallCouplingGap.sq_integral_le_integral_sq` — Cauchy–Schwarz on a probability measure — gives
`(∫|f|)² ≤ ∫|f|² = ∫ f² ≤ 1`, and `hδ` is what lets the bound be multiplied through by it.

This is the form in which the deviation is compared with an `L²` normalisation, so the two sides are
measured in the same norm.

DERIVED: `0` is the lower bound on `δ` in `hδ` and the mean `f` is required to have in `hmean`. `1`
is the `L²` normalisation the caller supplies in `hnorm`, and it is what makes the right-hand side
`δ` alone. The exponents `2` are squares of `f`, in `hf2` and `hnorm`. -/
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

/-- `hi - lo < lo ↔ hi < 2 * lo`, for reals. Both directions by `linarith`.

The endpoint deviation falls below `lo` exactly when the kernel's range is within a factor of two of
itself.

DERIVED: `2` is what `hi − lo < lo` rearranges to; it is the arithmetic of moving `lo` across the
inequality, not a chosen tolerance. -/
theorem separates_iff_hi_lt_two_lo {lo hi : ℝ} : hi - lo < lo ↔ hi < 2 * lo := by
  constructor <;> intro h <;> linarith

#print axioms separates_iff_hi_lt_two_lo

/-- `(hi - lo) / 2 < lo ↔ hi < 3 * lo`, for reals. Both directions by `linarith`.

The midpoint deviation falls below `lo` under a strictly weaker condition than the endpoint
deviation does: a factor of three rather than two.

DERIVED: `2` is the half-width from `TwoSided.abs_sub_mid_le`; `3` is what `(hi − lo)/2 < lo`
rearranges to once that half is cleared. Neither is chosen. -/
theorem separates_iff_hi_lt_three_lo {lo hi : ℝ} : (hi - lo) / 2 < lo ↔ hi < 3 * lo := by
  constructor <;> intro h <;> linarith

#print axioms separates_iff_hi_lt_three_lo

/-- For `0 < c` and any real `A`: `c < A * c⁻¹ ↔ c ^ 2 < A`. Rewrites `A * c⁻¹` as `A / c` and
clears the division by `lt_div_iff₀`.

The form in which a separation condition stated on a reciprocal pair of bounds becomes a condition on
the square of the cap. `A` is unrestricted in sign; positivity of `c` is what the division needs.

DERIVED: `0` is the strict lower bound on `c` in `hc`, which the division requires. The exponent `2`
is the square produced by multiplying the inequality through by `c`. `A` is the caller's factor —
`2` when it comes from `separates_iff_hi_lt_two_lo` and `3` from
`separates_iff_hi_lt_three_lo` — and is a variable here, not a literal. -/
theorem cap_condition {c A : ℝ} (hc : 0 < c) : c < A * c⁻¹ ↔ c ^ 2 < A := by
  rw [show A * c⁻¹ = A / c by ring, lt_div_iff₀ hc, sq]

#print axioms cap_condition

/-! ## 4. And each is a linear condition on the exponent -/

/-- `SliceTransferSelfAdjoint.transferCap ι N b Cs = Real.exp Cs * Real.exp (|b| * (|ι| * N))`, by
`rfl`. Records that the cap is a single exponential whose exponent is linear in the slice size
`Fintype.card ι` and in the rank `N`.

DERIVED: no numeral of this declaration's; every constant is `transferCap`'s and is carried through
the definitional equality. -/
theorem transferCap_eq (ι : Type) [Fintype ι] (N : ℕ) (b Cs : ℝ) :
    MassGap.SliceTransferSelfAdjoint.transferCap ι N b Cs
      = Real.exp Cs * Real.exp (|b| * ((Fintype.card ι : ℝ) * (N : ℝ))) := rfl

#print axioms transferCap_eq

/-- For any reals `v`, `Nr`, `b`, `Cs` and any `A > 0`:

    (exp Cs * exp (|b| * (v * Nr))) ^ 2 < A   ↔   2 * (Cs + |b| * (v * Nr)) < Real.log A.

The square of the product of exponentials is one exponential at twice the exponent, and `exp` is
strictly monotone with `exp (log A) = A`.

So the condition is linear in the exponent at every positive `A`, and two different factors differ
only through `log A`. `hA` is needed for `Real.exp_log`.

DERIVED: `0` is the strict lower bound on `A` in `hA`. The exponent `2` squares the cap, and the
factor `2` on the right is that same square moved into the exponent, so the two are one numeral.
`A` and `log A` are the caller's factor, variables rather than literals. -/
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

/-- For `0 ≤ β` and `0 < Nr`: `2 * (Cs + |β / Nr| * (v * Nr)) < L ↔ 2 * (Cs + β * v) < L`. The
identity `|β/Nr| * (v * Nr) = β * v` is established by `abs_div` and the two sign hypotheses, then
rewritten.

The rank `Nr` appearing in `b = β / Nr` cancels against the `Nr` in the exponent, leaving a condition
in `β` and `v` alone. Both sign hypotheses are consumed by the absolute value: `transferCap` carries
`|b|` rather than a bare `b`, so `hβ` is what removes it.

DERIVED: `0` is the lower bound on `β` in `hβ` and the strict lower bound on `Nr` in `hN`; both are
spent discharging the absolute value. `2` is `cap_sq_lt_iff`'s square moved into the exponent,
carried unchanged on both sides. `L` is the caller's threshold constant, a variable. -/
theorem rank_cancels {β Cs v Nr L : ℝ} (hβ : 0 ≤ β) (hN : 0 < Nr) :
    2 * (Cs + |β / Nr| * (v * Nr)) < L ↔ 2 * (Cs + β * v) < L := by
  have hshape : |β / Nr| * (v * Nr) = β * v := by
    rw [abs_div, abs_of_nonneg hβ, abs_of_pos hN]
    field_simp
  rw [hshape]

#print axioms rank_cancels

/-! ## 5. The threshold, as a condition on the coupling -/

/-- For `0 < v` and any reals `β`, `Cs`, `L`:

    2 * (Cs + β * v) < L   ↔   β < (L - 2 * Cs) / (2 * v).

`lt_div_iff₀` at `0 < 2 * v`, then `linarith` in both directions.

`L` is a variable, so the shape holds at every threshold constant: the numerator depends on `L` and
`Cs`, and the denominator is `2 * v` regardless. `threshold_at_endpoint_centre` and
`threshold_at_midpoint_centre` are the two instances used here.

DERIVED: `0` is the strict lower bound on `v` in `hv`, which the division requires. The three `2`s
are one numeral, `cap_sq_lt_iff`'s square, carried through the rearrangement — it multiplies the
exponent on the left and appears in the numerator and denominator on the right. `L` is the caller's
threshold constant. -/
theorem threshold_shape {β Cs v L : ℝ} (hv : 0 < v) :
    2 * (Cs + β * v) < L ↔ β < (L - 2 * Cs) / (2 * v) := by
  rw [lt_div_iff₀ (by linarith : (0 : ℝ) < 2 * v)]
  constructor <;> intro h <;> linarith

#print axioms threshold_shape

/-- `threshold_shape` at `L = Real.log 2`:
`2 * (Cs + β * v) < log 2 ↔ β < (log 2 - 2 * Cs) / (2 * v)`, for `0 < v`. The body is
`threshold_shape hv`.

DERIVED: `0` is the strict lower bound on `v`. The three `2`s outside the logarithm are
`threshold_shape`'s single square. The `2` inside `Real.log 2` is
`separates_iff_hi_lt_two_lo`'s factor, read through `cap_sq_lt_iff`, so it is the endpoint centre's
and is not chosen here. -/
theorem threshold_at_endpoint_centre {β Cs v : ℝ} (hv : 0 < v) :
    2 * (Cs + β * v) < Real.log 2 ↔ β < (Real.log 2 - 2 * Cs) / (2 * v) :=
  threshold_shape hv

#print axioms threshold_at_endpoint_centre

/-- `threshold_shape` at `L = Real.log 3`:
`2 * (Cs + β * v) < log 3 ↔ β < (log 3 - 2 * Cs) / (2 * v)`, for `0 < v`. The body is
`threshold_shape hv`, the same as `threshold_at_endpoint_centre`; only the constant differs, and the
denominator `2 * v` is unchanged.

DERIVED: `0` is the strict lower bound on `v`. The three `2`s outside the logarithm are
`threshold_shape`'s single square. `3` inside `Real.log 3` is
`separates_iff_hi_lt_three_lo`'s factor, read through `cap_sq_lt_iff`, so it is the midpoint centre's
and is not chosen here. -/
theorem threshold_at_midpoint_centre {β Cs v : ℝ} (hv : 0 < v) :
    2 * (Cs + β * v) < Real.log 3 ↔ β < (Real.log 3 - 2 * Cs) / (2 * v) :=
  threshold_shape hv

#print axioms threshold_at_midpoint_centre

/-- `(log 2 - 2 * Cs) / (2 * v) < (log 3 - 2 * Cs) / (2 * v)` for every `Cs` and every `0 < v`. Both
sides share the denominator, so `div_lt_div_iff₀` reduces it to `log 2 < log 3`, which is
`Real.log_lt_log`.

The midpoint centre's threshold exceeds the endpoint centre's at every `v`. The two denominators are
identical, so the difference is in the numerator alone and does not depend on `v`.

DERIVED: `0` is the strict lower bound on `v`. The `2`s outside the logarithms are
`threshold_shape`'s single square, appearing in both numerators and both denominators. `2` inside
`log 2` and `3` inside `log 3` are the endpoint and midpoint centres' factors, from
`separates_iff_hi_lt_two_lo` and `separates_iff_hi_lt_three_lo`. Nothing is chosen. -/
theorem midpoint_admits_strictly_more {Cs v : ℝ} (hv : 0 < v) :
    (Real.log 2 - 2 * Cs) / (2 * v) < (Real.log 3 - 2 * Cs) / (2 * v) := by
  have h2v : (0 : ℝ) < 2 * v := by linarith
  have hlog : Real.log 2 < Real.log 3 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [div_lt_div_iff₀ h2v h2v]
  nlinarith [hlog, h2v]

#print axioms midpoint_admits_strictly_more

/-! ## 6. Anti-vacuity, in both directions -/

/-- `2 * ((1/4 : ℝ) + (1/20) * 1) < Real.log 2`. The left side is `0.6`, and
`Real.log_two_gt_d9` bounds `log 2` below by a rational above it.

A point satisfying `threshold_at_endpoint_centre`'s left-hand condition, so that condition is not
vacuous. The value of `Cs` is nonzero, so the witness is not the free case.

CHOSEN: `Cs = 1/4`, `v = 1` and `β = 1/20` are a witness with room against `log 2 ≈ 0.6931`; `Cs` is
deliberately nonzero, `v = 1` is one link, and none of the three carries any other role. The leading
`2` is `threshold_shape`'s square, not part of the witness, and `2` inside `Real.log 2` is the
endpoint centre's factor. -/
theorem threshold_is_satisfiable :
    2 * ((1 / 4 : ℝ) + (1 / 20) * 1) < Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

#print axioms threshold_is_satisfiable

/-- For every `Cs`, every `L`, and every `β > 0`, there is a `v > 0` with
`¬ (2 * (Cs + β * v) < L)`. The witness is any `v` above `max ((L - 2*Cs)/(2*β)) 0`, supplied by
`exists_gt`.

So at a fixed positive coupling the condition fails at some positive slice size. `L` is universally
quantified, so this covers every threshold constant, including `log 2` and `log 3`.

DERIVED: `0` is the strict lower bound on `β` in `hβ` and the strict lower bound asserted of the
witness `v`. `2` is `threshold_shape`'s square, carried unchanged. `L` and `Cs` are the caller's. -/
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
