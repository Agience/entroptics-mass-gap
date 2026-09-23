import MassGap.Moment

/-!
# MassGap.Sharp — a tangent-line lower bound on the cosine average

Lower bounds on `⟨cos θ⟩` in terms of the second moment `⟨θ²⟩`, for a `Moment.Read N`.

The chain is elementary real analysis. `mul_cos_lt_sin` proves `x·cos x < sin x` on `(0, π)`;
`sinc_strictAntiOn` turns it into strict antitonicity of `sin x / x` on `Ioc 0 π`; `cos_ge_tangent`
uses that to prove the pointwise inequality

    cos A + (sin A / (2A))·(A² − x²)  ≤  cos x        for `x ∈ [0, π]`, `A ∈ (0, π)`,

which is the tangent line to `t ↦ cos √t` at `t = A²`, written in `x`. `circ_angle_le_pi` shows the
lag angle stays in `[0, π]`, so the pointwise bound can be averaged termwise. `cos_avg_ge_tangent` is
that average, and `cos_avg_ge_cos_rms` is its specialisation to `A = √⟨θ²⟩`, where the correction
term vanishes:

    cos √⟨θ²⟩  ≤  ⟨cos θ⟩.

Equality in `cos_ge_tangent` holds pointwise at `x = A`. No declaration in this file exhibits a
distribution attaining `cos_avg_ge_cos_rms`, and none states that a larger lower bound is
unavailable; both theorems are one-directional inequalities.

`cos_avg_ge_cos_rms` requires the second moment to be nonnegative and strictly below `π²`, supplied
as the hypotheses `hnn` and `hlt`.

DERIVED: no numeral in this file is a magnitude. `π` is the half-turn the lag angle lives on —
`circ_angle_le_pi` proves `θ_d ≤ π` from `circLag d` being at most half the periodic extent — and
the `2` in `sin A / (2A)` is the derivative of `x ↦ x²`, the chain-rule factor of the substitution
`t = x²`. The `2` in `2π/(N+1)` is the full turn, and the `1` in `N + 1` is the number of lags, the
cardinality of `Fin (N + 1)`.
-/

namespace MassGap.Sharp

open Real Set

/-- `x * Real.cos x < Real.sin x` for `0 < x < π`. A trichotomy on `x` against `π/2`: below it,
`Real.lt_tan` gives `x < tan x` and `cos x > 0` clears the denominator; at it, the left side is `0`
and the right is `1`; above it, `cos x < 0` while `sin x > 0`.

Strict throughout, and stated on the open interval — it fails at `x = 0`, where both sides are `0`.
No numeric estimate is used.

DERIVED: `0` is the strict lower bound on `x`; it is the only numeral. `π` is the half-turn and the
upper endpoint, beyond which the sine changes sign and the inequality fails. -/
theorem mul_cos_lt_sin {x : ℝ} (hx : 0 < x) (hxπ : x < π) : x * Real.cos x < Real.sin x := by
  rcases lt_trichotomy x (π / 2) with h | h | h
  · -- first quarter-turn: `x < tan x`, and `cos x > 0` clears the denominator
    have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h⟩
    have htan : x < Real.tan x := Real.lt_tan hx h
    rw [Real.tan_eq_sin_div_cos] at htan
    calc x * Real.cos x < (Real.sin x / Real.cos x) * Real.cos x :=
          (mul_lt_mul_of_pos_right htan hcos)
      _ = Real.sin x := by field_simp
  · -- exactly at the quarter-turn the cosine vanishes and the sine is one
    subst h
    rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
    norm_num
  · -- past the quarter-turn the cosine is negative and the sine is still positive
    have hcos : Real.cos x < 0 := by
      refine Real.cos_neg_of_pi_div_two_lt_of_lt h ?_
      linarith [Real.pi_pos]
    have hsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx hxπ
    nlinarith

/-- `fun x => Real.sin x / x` is strictly antitone on `Set.Ioc 0 π`. From
`strictAntiOn_of_deriv_neg`: the derivative is `(cos x · x − sin x)/x²`, whose numerator is negative
by `mul_cos_lt_sin` and whose denominator is positive.

Stated on the half-open interval, so `0` is excluded — the quotient is not defined there — while `π`
is included.

DERIVED: `0` is the excluded left endpoint of `Ioc 0 π`; `π` is the included right endpoint, the
half-turn on which `mul_cos_lt_sin` holds. -/
theorem sinc_strictAntiOn : StrictAntiOn (fun x => Real.sin x / x) (Ioc 0 π) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioc 0 π) ?_ ?_
  · refine ContinuousOn.div Real.continuous_sin.continuousOn continuousOn_id ?_
    intro x hx
    exact ne_of_gt hx.1
  · intro x hx
    rw [interior_Ioc] at hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have hd : HasDerivAt (fun x => Real.sin x / x)
        ((Real.cos x * x - Real.sin x * 1) / x ^ 2) x :=
      (Real.hasDerivAt_sin x).div (hasDerivAt_id x) hx0
    rw [hd.deriv]
    have hnum : Real.cos x * x - Real.sin x * 1 < 0 := by
      have := mul_cos_lt_sin hx.1 hx.2
      nlinarith
    have hden : (0 : ℝ) < x ^ 2 := by positivity
    exact div_neg_of_neg_of_pos hnum hden

#print axioms sinc_strictAntiOn

/-- For `0 < A < π` and `0 ≤ x ≤ π`,

    cos A + (sin A / (2A)) · (A² − x²)  ≤  cos x.

The tangent line to `t ↦ cos √t` at `t = A²`, written in the variable `x`. Proof: `f y = cos y + λy²`
with `λ = sin A/(2A)` has `f' y = y·(sin A/A − sin y/y)`, and `sinc_strictAntiOn` makes that
nonpositive below `A` and nonnegative above it, so `f` is antitone on `[0, A]` and monotone on
`[A, π]` and attains its minimum over `[0, π]` at `A`.

Equality holds at `x = A`, where the correction term vanishes. The hypothesis `A < π` is strict
because `sin A > 0` is needed for `λ > 0`; `x` may be either endpoint.

DERIVED: `0` is the strict lower bound on `A` and the lower bound on `x`. `2` in `sin A / (2A)` is
the derivative of `y ↦ y²`, the chain-rule factor of the substitution `t = y²`, and the two
exponents `2` are that substitution's squares. `π` is the half-turn, the range on which
`sinc_strictAntiOn` holds and hence the widest interval this argument covers. -/
theorem cos_ge_tangent {A x : ℝ} (hA : 0 < A) (hAπ : A < π)
    (hx : 0 ≤ x) (hxπ : x ≤ π) :
    Real.cos A + (Real.sin A / (2 * A)) * (A ^ 2 - x ^ 2) ≤ Real.cos x := by
  have hsinA : 0 < Real.sin A := Real.sin_pos_of_pos_of_lt_pi hA hAπ
  set lam : ℝ := Real.sin A / (2 * A) with hlamdef
  have hlampos : 0 < lam := by rw [hlamdef]; positivity
  set f : ℝ → ℝ := fun y => Real.cos y + lam * y ^ 2 with hfdef
  have hderiv : ∀ y : ℝ, HasDerivAt f (-Real.sin y + lam * (2 * y)) y := by
    intro y
    have h2 : HasDerivAt (fun y : ℝ => lam * y ^ 2) (lam * (2 * y)) y := by
      simpa using (hasDerivAt_pow 2 y).const_mul lam
    exact (Real.hasDerivAt_cos y).add h2
  have hdiff : Differentiable ℝ f := fun y => (hderiv y).differentiableAt
  -- the derivative is `y·(sin A/A − sin y/y)`, so its sign is decided by `sinc_strictAntiOn`
  have hlow : ∀ y : ℝ, 0 < y → y < A → deriv f y ≤ 0 := by
    intro y hy0 hyA
    have hyπ : y ≤ π := le_of_lt (lt_trans hyA hAπ)
    have hcmp : Real.sin A / A < Real.sin y / y :=
      sinc_strictAntiOn ⟨hy0, hyπ⟩ ⟨hA, le_of_lt hAπ⟩ hyA
    have hmul : (Real.sin A / A) * y < Real.sin y := by
      have := mul_lt_mul_of_pos_right hcmp hy0
      rwa [div_mul_cancel₀ _ (ne_of_gt hy0)] at this
    rw [(hderiv y).deriv]
    have hrw : lam * (2 * y) = (Real.sin A / A) * y := by
      rw [hlamdef]; field_simp
    rw [hrw]; linarith
  have hhigh : ∀ y : ℝ, A < y → y < π → 0 ≤ deriv f y := by
    intro y hAy hyπ
    have hcmp : Real.sin y / y < Real.sin A / A :=
      sinc_strictAntiOn ⟨hA, le_of_lt hAπ⟩ ⟨lt_trans hA hAy, le_of_lt hyπ⟩ hAy
    have hy0 : 0 < y := lt_trans hA hAy
    have hmul : Real.sin y < (Real.sin A / A) * y := by
      have := mul_lt_mul_of_pos_right hcmp hy0
      rwa [div_mul_cancel₀ _ (ne_of_gt hy0)] at this
    rw [(hderiv y).deriv]
    have hrw : lam * (2 * y) = (Real.sin A / A) * y := by
      rw [hlamdef]; field_simp
    rw [hrw]; linarith
  have hdist : lam * (A ^ 2 - x ^ 2) = lam * A ^ 2 - lam * x ^ 2 := by ring
  rcases le_total x A with hxA | hAx
  · -- below the tangent point the function falls, so `f A ≤ f x`
    have hanti : AntitoneOn f (Icc 0 A) :=
      antitoneOn_of_deriv_nonpos (convex_Icc 0 A) hdiff.continuous.continuousOn
        (fun y hy => (hdiff y).differentiableWithinAt)
        (fun y hy => by rw [interior_Icc] at hy; exact hlow y hy.1 hy.2)
    have hkey := hanti (Set.mem_Icc.mpr ⟨hx, hxA⟩)
      (Set.mem_Icc.mpr ⟨le_of_lt hA, le_refl A⟩) hxA
    simp only [hfdef] at hkey
    linarith
  · -- above it the function rises, so again `f A ≤ f x`
    have hmono : MonotoneOn f (Icc A π) :=
      monotoneOn_of_deriv_nonneg (convex_Icc A π) hdiff.continuous.continuousOn
        (fun y hy => (hdiff y).differentiableWithinAt)
        (fun y hy => by rw [interior_Icc] at hy; exact hhigh y hy.1 hy.2)
    have hkey := hmono (Set.mem_Icc.mpr ⟨le_refl A, le_of_lt hAπ⟩)
      (Set.mem_Icc.mpr ⟨hAx, hxπ⟩) hAx
    simp only [hfdef] at hkey
    linarith

#print axioms cos_ge_tangent

open MassGap.Moment

/-- For every `d : Fin (N + 1)`, `2 * π * circLag d / ((N : ℝ) + 1) ≤ π`. The natural-number fact
`2 * circLag d ≤ N + 1` — which is `Moment.circLag` being the minimum of `d` and `N + 1 − d`, closed
by `omega` — cast to `ℝ` and divided through.

This is what lets `cos_ge_tangent` be applied termwise in `cos_avg_ge_tangent`, with no side
condition left for the caller.

DERIVED: `2` is the full turn in `2π`, the circumference the lag angle is measured on. `1` is the
`+1` of `Fin (N + 1)`, the number of lags, appearing in the type of `d` and as the denominator's
offset; the bound `π` is half the turn, which is why the factor `2` and the minimum in `circLag`
cancel. -/
theorem circ_angle_le_pi {N : ℕ} (d : Fin (N + 1)) :
    2 * Real.pi * (circLag d : ℝ) / ((N : ℝ) + 1) ≤ π := by
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hnat : 2 * circLag d ≤ N + 1 := by
    have := d.isLt
    simp only [circLag]
    omega
  have hreal : 2 * (circLag d : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hnat
  rw [div_le_iff₀ hNpos]
  nlinarith [Real.pi_pos]

/-- For a `Moment.Read N` and any `0 < A < π`,

    cos A + (sin A/(2A))·(A² − ⟨θ²⟩)  ≤  ⟨cos θ⟩,

where `⟨θ²⟩` is `(2π/(N+1))² · ∑_d p d · circLag d ²` and `⟨cos θ⟩` is `∑_d p d · cos (θ d)`.

`cos_ge_tangent` is applied to each lag, using `circ_angle_le_pi` for the range condition and
`R.p_nonneg` to keep the inequality under multiplication by the weight; summing and using `R.p_sum`
(the weights sum to `1`) collects the constant term and pulls the common factor `(2π/(N+1))²` out of
the moment.

The bound holds simultaneously for every admissible `A`; the statement quantifies over `A` and
selects none.

DERIVED: `0` is the strict lower bound on `A`. `2` in `sin A / (2A)` is the chain-rule factor from
`cos_ge_tangent`, and the exponents `2` are that lemma's squares and the square of the lag. `2` in
`2π/(N + 1)` is the full turn, and `1` is the `+1` of `Fin (N + 1)`, the number of lags, appearing
in the summation index type and in the denominator. `π` is the half-turn, the upper limit on `A`. -/
theorem cos_avg_ge_tangent {N : ℕ} (R : Read N) {A : ℝ} (hA : 0 < A) (hAπ : A < π) :
    Real.cos A + (Real.sin A / (2 * A))
        * (A ^ 2 - (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * (∑ d, R.p d * (circLag d : ℝ) ^ 2))
      ≤ ∑ d, R.p d * Real.cos (R.θ d) := by
  set lam : ℝ := Real.sin A / (2 * A) with hlamdef
  have key : ∀ d : Fin (N + 1),
      R.p d * (Real.cos A
          + lam * (A ^ 2 - (2 * Real.pi * (circLag d : ℝ) / ((N : ℝ) + 1)) ^ 2))
        ≤ R.p d * Real.cos (R.θ d) := by
    intro d
    rw [R.cos_theta_circ d]
    refine mul_le_mul_of_nonneg_left ?_ (R.p_nonneg d)
    refine cos_ge_tangent hA hAπ ?_ (circ_angle_le_pi d)
    positivity
  have hsum := Finset.sum_le_sum (fun d (_ : d ∈ Finset.univ) => key d)
  have hexp : ∑ d, R.p d * (Real.cos A
        + lam * (A ^ 2 - (2 * Real.pi * (circLag d : ℝ) / ((N : ℝ) + 1)) ^ 2))
      = Real.cos A + lam
          * (A ^ 2 - (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * (∑ d, R.p d * (circLag d : ℝ) ^ 2)) := by
    have hpt : ∀ d : Fin (N + 1),
        R.p d * (Real.cos A
            + lam * (A ^ 2 - (2 * Real.pi * (circLag d : ℝ) / ((N : ℝ) + 1)) ^ 2))
          = R.p d * (Real.cos A + lam * A ^ 2)
            - (lam * (2 * Real.pi / ((N : ℝ) + 1)) ^ 2) * (R.p d * (circLag d : ℝ) ^ 2) :=
      fun d => by ring
    rw [Finset.sum_congr rfl (fun d _ => hpt d), Finset.sum_sub_distrib, ← Finset.sum_mul,
      R.p_sum, one_mul, ← Finset.mul_sum]
    ring
  rwa [hexp] at hsum

#print axioms cos_avg_ge_tangent

/-- For a `Moment.Read N` whose second moment `⟨θ²⟩ = (2π/(N+1))² · ∑_d p d · circLag d ²` is
nonnegative (`hnn`) and strictly below `π²` (`hlt`),

    cos √⟨θ²⟩  ≤  ⟨cos θ⟩.

`cos_avg_ge_tangent` at `A = √⟨θ²⟩`, where `A² = ⟨θ²⟩` and the correction term is exactly `0`. The
proof splits on whether the moment vanishes: at `0` the conclusion reads `1 ≤ ⟨cos θ⟩`, which
`Moment.Read.cos_avg_ge_circ` already gives and which needs no tangent; above `0`, `hlt` supplies
`A < π` through `Real.sqrt_lt_sqrt`.

Both hypotheses are about the moment, not about the distribution: `hlt` is what keeps `A` inside the
interval `cos_ge_tangent` is proved on. The statement is a lower bound; nothing here exhibits a read
attaining it.

DERIVED: `0` is the lower bound on the moment in `hnn`. `2` in `2π/(N + 1)` is the full turn, `1` is
the `+1` of `Fin (N + 1)`, the number of lags, and the exponents `2` square the lag and the moment's
prefactor. `π ^ 2` in `hlt` is the square of the half-turn, so the hypothesis says the
root-mean-square lag angle stays inside the half-turn, which is the range `cos_ge_tangent` covers. -/
theorem cos_avg_ge_cos_rms {N : ℕ} (R : Read N)
    (hnn : 0 ≤ (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * (∑ d, R.p d * (circLag d : ℝ) ^ 2))
    (hlt : (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * (∑ d, R.p d * (circLag d : ℝ) ^ 2) < π ^ 2) :
    Real.cos (Real.sqrt ((2 * Real.pi / ((N : ℝ) + 1)) ^ 2
        * (∑ d, R.p d * (circLag d : ℝ) ^ 2)))
      ≤ ∑ d, R.p d * Real.cos (R.θ d) := by
  have hge := R.cos_avg_ge_circ
  rcases eq_or_lt_of_le hnn with hzero | hpos
  · -- a vanishing moment is a read with all its mass at zero lag: the bound reads `1 ≤ ⟨cos θ⟩`,
    -- which is what `cos_avg_ge_circ` already gives there. No tangent is needed.
    rw [← hzero, Real.sqrt_zero, Real.cos_zero]
    linarith
  · have hA : 0 < Real.sqrt ((2 * Real.pi / ((N : ℝ) + 1)) ^ 2
        * (∑ d, R.p d * (circLag d : ℝ) ^ 2)) := Real.sqrt_pos.mpr hpos
    have hAπ : Real.sqrt ((2 * Real.pi / ((N : ℝ) + 1)) ^ 2
        * (∑ d, R.p d * (circLag d : ℝ) ^ 2)) < π := by
      have hstep := Real.sqrt_lt_sqrt (le_of_lt hpos) hlt
      rwa [Real.sqrt_sq (le_of_lt Real.pi_pos)] at hstep
    have hA2 : Real.sqrt ((2 * Real.pi / ((N : ℝ) + 1)) ^ 2
          * (∑ d, R.p d * (circLag d : ℝ) ^ 2)) ^ 2
        = (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * (∑ d, R.p d * (circLag d : ℝ) ^ 2) :=
      Real.sq_sqrt (le_of_lt hpos)
    have hkey := cos_avg_ge_tangent R hA hAπ
    rw [hA2, sub_self, mul_zero, add_zero] at hkey
    exact hkey

#print axioms cos_avg_ge_cos_rms

end MassGap.Sharp
