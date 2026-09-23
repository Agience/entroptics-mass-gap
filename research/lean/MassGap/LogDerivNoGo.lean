import Mathlib
import MassGap.PowerTail

/-!
# MassGap.LogDerivNoGo — what a relative derivative bound forces

Four groups of results about a bound of the shape `|f'| ≤ K · f`.

## 1. A relative bound based at a zero forces vanishing

`vanishes_of_relative_deriv_bound_from_zero` — a nonnegative `f` on `[0, b]`, differentiable on
`(0, b)`, with `|f'| ≤ K f` there and `f 0 = 0`, is identically zero on `[0, b]`. Grönwall in the
direction that needs no integral: `f(x) e^{-Kx}` has nonpositive derivative, so it is antitone from
the value `0`, and `f ≥ 0` closes it from below. `K` is an arbitrary real, positive or not.

## 2. The same applied to `wilsonCorrAt`

`per_lag_bound_from_zero_forces_vanishing` — the same hypotheses for
`β ↦ wilsonCorrAt N β d` on `[0, b]`, at a lag with `1 ≤ Moment.circLag d`, give
`wilsonCorrAt N x d = 0` throughout. The zero at `β = 0` is
`PowerTail.wilsonCorrAt_at_zero_coupling`. Nonnegativity is a hypothesis the caller supplies rather
than being taken from a reflection-positivity result.

## 3. The two-term torus profile

`torusProfile lam M n = lam^n + lam^(M−n)`, the shape a transfer operator on a circle of extent `M`
gives. `torusProfile_midpoint` evaluates it at `M = 2n` as `2·lam^n`. `midpoint_relative_deriv` is
the algebraic identity

    (2 · (n · lam^(n−1) · L)) / torusProfile lam (2n) n = n · L / lam,

for `0 < lam` and `0 < n`. `L` is a free real standing in for `lam'`; nothing is differentiated in
the statement. `no_uniform_bound_on_torus_profile` reads the `n` factor off it: for fixed `lam > 0`
and `L ≠ 0`, no real `K` bounds the absolute value of that quotient at every `n`.

## 4. An aggregate bound that does hold

`l1_moment_bounded_by_mass` — for `0 ≤ lam < 1` and `0 < n`,

    ∑_{d<n} d·lam^d ≤ (lam/(1−lam)²) · ∑_{d<n} lam^d.

The constant carries neither `n` nor a lag. It is a statement about geometric partial sums: the
numerator is bounded by the full series `lam/(1−lam)²` and the denominator is at least the `d = 0`
term. The identification of either side with a derivative or with a correlation is the caller's.

Nothing here evaluates `wilsonCorrAt` at any lag beyond §2's use of
`PowerTail.wilsonCorrAt_at_zero_coupling`, and §3's profile is an arbitrary two-term expression, not
a claim about `wilsonCorrAt`.
-/

namespace MassGap.LogDerivNoGo

open Finset

/-! ## 1. A relative derivative bound based at a zero forces vanishing -/

/-- A nonnegative `f`, continuous on `Set.Icc 0 b`, differentiable on `Set.Ioo 0 b` with
`|deriv f x| ≤ K * f x` there, and vanishing at `0`, is identically zero on `Set.Icc 0 b`. The
auxiliary `g x = f x · exp (-(K x))` has derivative `(f' − K f) e^{−Kx} ≤ 0`, so
`antitoneOn_of_deriv_nonpos` makes it antitone from `g 0 = 0`; `f ≥ 0` and `exp > 0` close it from
below. `K` is an arbitrary real, and `b` need only satisfy `0 ≤ b`.

DERIVED: the `0`s are all the same base point of the interval — the left endpoint of `Icc 0 b` and
`Ioo 0 b`, the point where `f` is assumed to vanish, the floor in `0 ≤ f x` and `0 ≤ b`, and the
value concluded throughout. -/
theorem vanishes_of_relative_deriv_bound_from_zero {f : ℝ → ℝ} {K b : ℝ} (hb : 0 ≤ b)
    (hcont : ContinuousOn f (Set.Icc 0 b))
    (hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) b, HasDerivAt f (deriv f x) x)
    (hbound : ∀ x ∈ Set.Ioo (0 : ℝ) b, |deriv f x| ≤ K * f x)
    (hnn : ∀ x ∈ Set.Icc (0 : ℝ) b, 0 ≤ f x)
    (hzero : f 0 = 0) :
    ∀ x ∈ Set.Icc (0 : ℝ) b, f x = 0 := by
  set g : ℝ → ℝ := fun x => f x * Real.exp (-(K * x)) with hg
  have hlin : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -(K * y)) (-K) x := by
    intro x
    have hid := (hasDerivAt_id x).const_mul K
    simp only [id_eq, mul_one] at hid
    exact hid.neg
  have hexpd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Real.exp (-(K * y)))
      (Real.exp (-(K * x)) * -K) x := fun x => (hlin x).exp
  have hgcont : ContinuousOn g (Set.Icc 0 b) :=
    hcont.mul (Real.continuous_exp.comp (by fun_prop)).continuousOn
  have hganti : AntitoneOn g (Set.Icc 0 b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 b) hgcont ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx
      exact ((hderiv x hx).mul (hexpd x)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hd : HasDerivAt g (deriv f x * Real.exp (-(K * x))
          + f x * (Real.exp (-(K * x)) * -K)) x := (hderiv x hx).mul (hexpd x)
      rw [hd.deriv]
      have hle : deriv f x ≤ K * f x := le_of_abs_le (hbound x hx)
      have hexp : 0 < Real.exp (-(K * x)) := Real.exp_pos _
      nlinarith [hexp, hle]
  intro x hx
  have hx0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) b := ⟨le_rfl, hb⟩
  have hgle : g x ≤ g 0 := hganti hx0 hx hx.1
  have hg0 : g 0 = 0 := by simp [hg, hzero]
  have hexp : 0 < Real.exp (-(K * x)) := Real.exp_pos _
  have hfle : f x * Real.exp (-(K * x)) ≤ 0 := by rw [hg0] at hgle; exact hgle
  have hfnn := hnn x hx
  nlinarith [hexp, hfle, hfnn]

#print axioms vanishes_of_relative_deriv_bound_from_zero

/-! ## 2. The Wilson correlation has such a zero off contact -/

/-- `vanishes_of_relative_deriv_bound_from_zero` instantiated at `f = fun β => wilsonCorrAt N β d`.
At a lag with `1 ≤ Moment.circLag d`, a relative derivative bound `|ρ_d'| ≤ K ρ_d` holding on
`Set.Ioo 0 b` forces `wilsonCorrAt N x d = 0` on all of `Set.Icc 0 b`. The value at zero coupling is
`PowerTail.wilsonCorrAt_at_zero_coupling`; the interval must start at `0` for that to apply.

Nonnegativity is taken as the hypothesis `hnn` rather than from a reflection-positivity result, so
the caller supplies whichever nonnegativity they have.

DERIVED: the `1` in `Fin (N + 1)` is the lag index's range, one more than the extent `N`; the `1` in
`hd` is `PowerTail.wilsonCorrAt_at_zero_coupling`'s own threshold, excluding the contact lag; the
`0`s are the left endpoint of the interval, the coupling at which the correlation vanishes, the floor
in `0 ≤ b` and `0 ≤ wilsonCorrAt`, and the value concluded throughout. -/
theorem per_lag_bound_from_zero_forces_vanishing {N : ℕ} {d : Fin (N + 1)} {K b : ℝ}
    (hd : 1 ≤ Moment.circLag d) (hb : 0 ≤ b)
    (hcont : ContinuousOn (fun β => MassGap.wilsonCorrAt N β d) (Set.Icc 0 b))
    (hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) b,
      HasDerivAt (fun β => MassGap.wilsonCorrAt N β d)
        (deriv (fun β => MassGap.wilsonCorrAt N β d) x) x)
    (hbound : ∀ x ∈ Set.Ioo (0 : ℝ) b,
      |deriv (fun β => MassGap.wilsonCorrAt N β d) x| ≤ K * MassGap.wilsonCorrAt N x d)
    (hnn : ∀ x ∈ Set.Icc (0 : ℝ) b, 0 ≤ MassGap.wilsonCorrAt N x d) :
    ∀ x ∈ Set.Icc (0 : ℝ) b, MassGap.wilsonCorrAt N x d = 0 :=
  vanishes_of_relative_deriv_bound_from_zero hb hcont hderiv hbound hnn
    (MassGap.PowerTail.wilsonCorrAt_at_zero_coupling N d hd)

#print axioms per_lag_bound_from_zero_forces_vanishing

/-! ## 3. The two-term torus profile -/

/-- `lam ^ n + lam ^ (M − n)`, the two-term shape a transfer operator on a circle of extent `M`
gives, one term running each way round. `M − n` is natural subtraction, so it truncates at zero for
`n > M`.

DERIVED: no numeral. `lam` is the decay factor, `n` the lag and `M` the extent. -/
noncomputable def torusProfile (lam : ℝ) (M n : ℕ) : ℝ := lam ^ n + lam ^ (M - n)

/-- At the midpoint of the circle the two arms coincide: `torusProfile lam (2n) n = 2 · lam^n`,
since `2n − n = n`. An identity for every real `lam` and every `n`.

DERIVED: the `2` in `2 * n` places the lag at the midpoint of a circle of extent `2n`; the `2` on the
right is the number of arms that coincide there. -/
theorem torusProfile_midpoint (lam : ℝ) (n : ℕ) :
    torusProfile lam (2 * n) n = 2 * lam ^ n := by
  unfold torusProfile
  rw [show 2 * n - n = n by omega]
  ring

/-- The algebraic identity `(2 · (n · lam^(n−1) · L)) / torusProfile lam (2n) n = n · L / lam`, for
`0 < lam` and `0 < n`. Read against the power rule, the left side is `ρ'/ρ` for `ρ = 2 lam^n` with
`L` in the place of `lam'`; but `L` is a free real and nothing in the statement differentiates
anything. The `n` on the right is what `no_uniform_bound_on_torus_profile` exploits.

DERIVED: `0` in `hlam` is what lets `lam` be cancelled from the quotient, and `0` in `hn` is what
makes `n − 1` the ordinary predecessor; the `2` in `2 * n` places the lag at the midpoint and the
leading `2` is the coefficient `torusProfile_midpoint` produces there; the `1` in `n − 1` is the power
rule's offset, cancelled against one factor of `lam`. -/
theorem midpoint_relative_deriv {lam L : ℝ} (hlam : 0 < lam) {n : ℕ} (hn : 0 < n) :
    ((2 : ℝ) * ((n : ℝ) * lam ^ (n - 1) * L)) / torusProfile lam (2 * n) n
      = (n : ℝ) * L / lam := by
  rw [torusProfile_midpoint]
  have hne : lam ≠ 0 := ne_of_gt hlam
  have hsplit : lam ^ n = lam ^ (n - 1) * lam := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  rw [hsplit]
  field_simp

#print axioms midpoint_relative_deriv

/-- For fixed `lam > 0` and `L ≠ 0`, and any real `K`, there is an `n > 0` at which the midpoint
quotient exceeds `K` in absolute value. `midpoint_relative_deriv` reduces the quotient to
`n · L / lam`, and `exists_nat_gt` supplies an `n` past `K / (|L| / lam)`. `K` is refuted one `lam`
at a time: the `n` produced depends on `lam`, `L` and `K`. The hypothesis `L ≠ 0` is what makes the
quotient grow at all.

DERIVED: `0` in `hlam` is the positivity of the decay factor and `0` in `hL` the value `L` must
avoid; `0 < n` excludes the degenerate lag; the `2` in `2 * n` places the lag at the midpoint and the
leading `2` is `torusProfile_midpoint`'s coefficient; the `1` in `n − 1` is the power rule's
offset. -/
theorem no_uniform_bound_on_torus_profile {lam L : ℝ} (hlam : 0 < lam) (hL : L ≠ 0) (K : ℝ) :
    ∃ n : ℕ, 0 < n ∧
      K < |((2 : ℝ) * ((n : ℝ) * lam ^ (n - 1) * L)) / torusProfile lam (2 * n) n| := by
  have hratio : 0 < |L| / lam := div_pos (abs_pos.mpr hL) hlam
  obtain ⟨n, hn⟩ := exists_nat_gt (max (K / (|L| / lam)) 1)
  have hn1 : (1 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hnpos : 0 < n := by exact_mod_cast lt_trans zero_lt_one hn1
  refine ⟨n, hnpos, ?_⟩
  rw [midpoint_relative_deriv hlam hnpos, abs_div, abs_mul, Nat.abs_cast, abs_of_pos hlam]
  have hd : K / (|L| / lam) < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  rw [div_lt_iff₀ hratio] at hd
  calc K < (n : ℝ) * (|L| / lam) := hd
    _ = (n : ℝ) * |L| / lam := by ring

#print axioms no_uniform_bound_on_torus_profile

/-! ## 4. An aggregate bound on the geometric partial sums -/

/-- For `0 ≤ lam < 1` and `0 < n`,
`∑_{d ∈ range n} d · lam^d ≤ (lam/(1−lam)²) · ∑_{d ∈ range n} lam^d`. The numerator is bounded by the
full series `∑' d, d·lam^d = lam/(1−lam)²` (`tsum_coe_mul_geometric_of_norm_lt_one`), and the
denominator is at least `1`, since the `d = 0` term is `lam^0`. The constant carries neither `n` nor
a lag. It is written on `∑ d·lam^d` rather than `∑ d·lam^{d−1}` to avoid a natural-number
subtraction. A statement about geometric partial sums; nothing identifies either side with a
derivative or a correlation.

DERIVED: `0` in `hlam0` is the floor making the powers nonnegative; `1` in `hlam1` is the radius of
convergence the summability needs; `0` in `hn` is what puts the `d = 0` term in `range n`, which is
the `1` the denominator is bounded below by; the `2` is the exponent in the closed form
`∑' d, d·lam^d = lam/(1−lam)²`; the `1` in `1 − lam` is that closed form's own. -/
theorem l1_moment_bounded_by_mass {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ range n, (d : ℝ) * lam ^ d
      ≤ (lam / (1 - lam) ^ 2) * ∑ d ∈ range n, lam ^ d := by
  have h1lam : 0 < 1 - lam := by linarith
  have hK : 0 ≤ lam / (1 - lam) ^ 2 := div_nonneg hlam0 (le_of_lt (pow_pos h1lam 2))
  have hnorm : ‖lam‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hlam0]
  -- the denominator is at least the contact term
  have hmass : (1 : ℝ) ≤ ∑ d ∈ range n, lam ^ d := by
    have hmem : (0 : ℕ) ∈ range n := mem_range.mpr hn
    have hnn : ∀ d ∈ range n, (0 : ℝ) ≤ lam ^ d := fun d _ => pow_nonneg hlam0 d
    calc (1 : ℝ) = lam ^ (0 : ℕ) := by simp
      _ ≤ ∑ d ∈ range n, lam ^ d := single_le_sum hnn hmem
  -- the numerator, against the full geometric moment series
  have hsummable : Summable (fun d : ℕ => (d : ℝ) * lam ^ d) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
  have hnn : ∀ d : ℕ, (0 : ℝ) ≤ (d : ℝ) * lam ^ d :=
    fun d => mul_nonneg (Nat.cast_nonneg d) (pow_nonneg hlam0 d)
  have hval : ∑' d : ℕ, (d : ℝ) * lam ^ d = lam / (1 - lam) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hnorm
  have hnum : ∑ d ∈ range n, (d : ℝ) * lam ^ d ≤ lam / (1 - lam) ^ 2 := by
    rw [← hval]
    exact hsummable.sum_le_tsum (range n) (fun d _ => hnn d)
  calc ∑ d ∈ range n, (d : ℝ) * lam ^ d
      ≤ lam / (1 - lam) ^ 2 := hnum
    _ = (lam / (1 - lam) ^ 2) * 1 := by ring
    _ ≤ (lam / (1 - lam) ^ 2) * ∑ d ∈ range n, lam ^ d :=
        mul_le_mul_of_nonneg_left hmass hK

#print axioms l1_moment_bounded_by_mass

end MassGap.LogDerivNoGo
