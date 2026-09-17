import MassGap.Moment

/-!
# The sharp cosine-moment bound

The confinement criterion reaches the entropy floor through a lower bound on the cosine average in
terms of the second moment of the lag angle. Everywhere else in the development that step is taken
with `Real.one_sub_sq_div_two_le_cos` — `1 − x²/2 ≤ cos x` — which is a THEOREM but not the SHARP
bound, and the slack it inserts is the one quantity in the whole chain that was chosen rather than
derived.

This file removes the choice. Given only the second moment `m = ⟨θ²⟩`, the largest lower bound on
`⟨cos θ⟩` that any argument can supply is

    ⟨cos θ⟩  ≥  cos √m                                     (`cos_avg_ge_cos_rms`)

and it is attained, by the point mass at `θ = √m`. So no further sharpening is possible at
second-moment order; what is lost beyond this is information the second moment does not carry.

THE ROUTE. `t ↦ cos √t` is convex on `[0, π²]`, so Jensen applies in the variable `t = θ²`. Convexity
is taken through the tangent line rather than the second derivative, which keeps `√` out of every
differentiation: the tangent at `A` is a lower bound for `cos` exactly when `sin x / x` is decreasing,
and that is `x·cos x < sin x`, which is `Real.lt_tan` on the first half-turn and a sign check on the
second.

DERIVED: nothing in this file is a magnitude. `π` is the half-turn the lag angle lives on
(`Moment.circLag` bounds `circLag d ≤ (N+1)/2`, so `θ_d ≤ π`), and the `2` in `sin A / (2A)` is the
derivative of `x ↦ x²`.
-/

namespace MassGap.Sharp

open Real Set

/-- **`x·cos x < sin x` on the open half-turn.** The inequality behind the monotonicity of
`sin x / x`, and the only analytic input this file takes.

On `(0, π/2)` it is `Real.lt_tan` cleared of its denominator; at `π/2` the left side is `0` and the
right is `1`; on `(π/2, π)` the cosine has turned negative while the sine has not, so the left side
is negative and the right positive. No estimate is made anywhere. -/
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

/-- **`sin x / x` is strictly decreasing across the half-turn** — the monotone form of
`mul_cos_lt_sin`, since `(sin x / x)' = (x·cos x − sin x)/x²`. -/
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

/-- **The tangent line to `cos` in the variable `x²`, as a pointwise lower bound.**

    cos A + (sin A / (2A)) · (A² − x²)  ≤  cos x        for `x ∈ [0, π]`, `A ∈ (0, π)`

This is convexity of `t ↦ cos √t` stated where it is used, and it is what makes the second-moment
bound sharp: equality holds at `x = A`, so the bound cannot be raised.

The proof is that `φ(x) = cos x + λx²` with `λ = sin A/(2A)` has `φ'(x) = x·(sin A/A − sin x/x)`, and
`sin x / x` is decreasing by `mul_cos_lt_sin`, so `φ` falls to `A` and rises after it. -/
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

/-- **The lag angle never leaves the half-turn.** `circLag d = min d (N+1−d)` is at most half the
periodic extent, so `θ = 2π·circLag d/(N+1) ≤ π`. This is what lets `cos_ge_tangent` be applied
termwise without a side condition to discharge at the caller. -/
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

/-- **THE SHARP COSINE-MOMENT BOUND.**

    cos A + (sin A/(2A))·(A² − ⟨θ²⟩)  ≤  ⟨cos θ⟩        for every `A ∈ (0, π)`

`Moment.Read.cos_avg_ge_circ` is the case of this bound in the limit `A → 0`, where the tangent to
`t ↦ cos √t` at the origin is `1 − t/2`. Every other `A` gives a strictly better bound at moments
near `A²`, and taking `A = √⟨θ²⟩` gives the best one available from the second moment at all:
`⟨cos θ⟩ ≥ cos √⟨θ²⟩`, which is attained by the point mass at `θ = √⟨θ²⟩`.

So this is where the second-moment route stops. What is lost past this point is information the
second moment does not carry, not slack in the argument — and the comparison constant the confinement
criterion carries is, after this, the sharp one rather than a chosen one. -/
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

/-- **THE BEST BOUND THE SECOND MOMENT CAN GIVE.**

    cos √⟨θ²⟩  ≤  ⟨cos θ⟩

Take the tangent at the root-mean-square angle itself: there `A² = ⟨θ²⟩`, the correction term in
`cos_avg_ge_tangent` vanishes identically, and what is left is Jensen's inequality for the convex
function `t ↦ cos √t`.

This is the end of the line for second-moment arguments. The bound is attained — by the point mass at
`θ = √⟨θ²⟩` — so it cannot be raised by any argument that reads the distribution only through its
second moment. Anything sharper must read something else. -/
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
