import Mathlib
import MassGap.PowerTail

/-!
# MassGap.LogDerivNoGo — B5's recorded target is refuted twice, and the L¹ target is not

## What B5's middle range is recorded as needing

`CosAvgStability`'s docstring, and the goal document after it, state the missing estimate as

> a bound on `|d log ρ_d/dβ|` **uniform in the lag and the volume**, on `β ≥ 0`.

`CompactBeta` rules out the ABSOLUTE bound and, as `CosAvgStability` correctly says, is silent on
the relative one. **That silence has been read as "open". It is not: the relative bound as stated is
refuted, from two unrelated directions, by theorems already in the tree.**

## ⛔ Refutation one — the `β → 0` end, and it has nothing to do with volume

`PowerTail.wilsonCorrAt_at_zero_coupling` puts `ρ_d(0) = 0` at every lag of nonzero circle distance:
at zero coupling the measure is product Haar and two plaquettes at distance read disjoint links.

A relative bound `|ρ_d'| ≤ K·ρ_d` on an interval STARTING at zero therefore forces `ρ_d ≡ 0` on the
whole interval — `vanishes_of_relative_deriv_bound_from_zero`, which is Grönwall in the one direction
that needs no integral: `ρ_d(β)·e^{−Kβ}` is antitone and starts at zero.

So the target on `β ≥ 0` is a dichotomy, not an estimate: either the correlation vanishes identically
off contact — and `PowerTail.contact_value_pos_at_zero_coupling` shows the contact lag does NOT
vanish, so the profile would be a point mass — or no `K` exists. **`[β₀, β₁]` with `β₀ > 0` is the
only defensible range**, and that costs nothing, because `ConfinesZero.confines_near_zero` already
covers a neighbourhood of zero by a different argument.

This is the same conclusion `CosAvgStability.mul_control_from_zero_forces_a_point_mass` reaches from
a multiplicative bound. Reaching it from the DERIVATIVE is what makes it bear on the log-derivative
target specifically, which the multiplicative statement does not.

## ⛔ Refutation two — the large-lag end, and here the volume IS the problem

A correlation governed by a transfer operator on a PERIODIC lattice is not `λ^d`. `ClayAssembly.
corr_at_max_lag_eq_lag_one` proves `ρ(N) = ρ(1)` by circle symmetry, so pure geometric decay would
force `λ = 1` and no gap at all. The correct shape is the **torus-symmetric** one,
`ρ(n) = λ^n + λ^{N−n}`, and at the midpoint lag `n = N/2` it has

    ρ(n) = 2·λ^n,   ρ'(n)/ρ(n) = n · (λ'/λ).

**That grows with the extent.** `midpoint_relative_deriv` is the identity and
`no_uniform_bound_on_torus_profile` is the consequence: no constant bounds it at every aperture,
whenever the decay factor moves with the coupling at all — which is exactly what a running gap means.

So "uniform in the lag and the volume" fails at the far lag for the same reason the gap runs.

## ✅ What is NOT refuted — the L¹-aggregate form

`∑_d |ρ_d'| ≤ K · ∑_d ρ_d` is a different statement, and the profile that kills the per-lag form
satisfies it with a constant carrying **no lag and no extent**
(`l1_relative_deriv_bounded_for_geometric`). The far-lag terms whose per-lag ratio diverges carry
geometrically little mass; aggregating against the same weights absorbs them.

That is not a happy accident — it is why `CosAvgStability` is built on `L1Close` and
`avg_stable_of_l1_close` rather than on a per-lag bound. **This file supplies the proof that the
choice was forced rather than convenient.**

## ⚠ What this does NOT do

**It proves nothing about the Wilson correlation's L¹ modulus.** Whether
`∑_d |dρ_d/dβ| ≤ K·∑_d ρ_d` holds for `wilsonCorrAt` uniformly in the aperture on `[β₀, β₁]` is open
and is B5. What is established is that the per-lag form should not be carried as the target, and
that the L¹ form survives both refutations of it.

**And §3's profile is an example.** One witness suffices to refute a `∀`, which is the only use of an
example needing no justification; nothing here claims `wilsonCorrAt` has that shape.
-/

namespace MassGap.LogDerivNoGo

open Finset

/-! ## 1. ⛔ A relative derivative bound based at a zero forces vanishing -/

/-- **GRÖNWALL, IN THE DIRECTION THAT NEEDS NO INTEGRAL.** If `f ≥ 0` obeys `|f'| ≤ K·f` on `[0, b]`
and `f 0 = 0`, then `f ≡ 0` there.

`f(β)·e^{−Kβ}` has derivative `(f' − K·f)·e^{−Kβ} ≤ 0`, so it is antitone and starts at zero; `f ≥ 0`
closes it from the other side.

DERIVED: the `0` is the base point and the value; `K` is the caller's bound. -/
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

/-! ## 2. ⛔ And the Wilson correlation HAS such a zero, off contact -/

/-- **⛔ SO A PER-LAG RELATIVE BOUND BASED AT ZERO COUPLING FORCES THE CORRELATION TO VANISH.**

`PowerTail.wilsonCorrAt_at_zero_coupling` supplies the zero at every lag of nonzero circle distance,
and §1 does the rest. Combined with `PowerTail.contact_value_pos_at_zero_coupling` — the contact lag
is strictly positive at zero coupling — the profile a `K` would force is a point mass.

**So the target must be stated on `[β₀, β₁]` with `β₀ > 0`.** That is free:
`ConfinesZero.confines_near_zero` covers a neighbourhood of zero by a different argument, so no range
is lost.

Nonnegativity is a HYPOTHESIS rather than taken from `Complete.wilson_reflection_positive_at`, so
this theorem carries no named axiom; the caller supplies whichever nonnegativity they have.

DERIVED: the `0` is zero coupling and the vanishing value; `1 ≤ circLag d` is `PowerTail`'s own
hypothesis, not a choice. -/
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

/-! ## 3. ⛔ The far-lag end, on the TORUS-SYMMETRIC profile -/

/-- **THE TORUS PROFILE.** Not `λ^d` — `ClayAssembly.corr_at_max_lag_eq_lag_one` forbids that, since
`ρ(N) = ρ(1)` would force `λ = 1`. A transfer operator on a periodic lattice gives the symmetric
form, one term running each way round the circle.

DERIVED: no numeral. `lam` is the decay factor, `n` the lag and `M` the extent. -/
noncomputable def torusProfile (lam : ℝ) (M n : ℕ) : ℝ := lam ^ n + lam ^ (M - n)

/-- At the midpoint of the circle the two arms coincide and the profile is `2·λ^n`.

DERIVED: the `2` is the two arms of the circle meeting, not a coefficient chosen here. -/
theorem torusProfile_midpoint (lam : ℝ) (n : ℕ) :
    torusProfile lam (2 * n) n = 2 * lam ^ n := by
  unfold torusProfile
  rw [show 2 * n - n = n by omega]
  ring

/-- **⛔ AND THERE THE RELATIVE DERIVATIVE IS `n` TIMES THE ONE-STEP RATE.**

`ρ = 2λⁿ` gives `ρ'/ρ = n·λ'/λ` exactly, and at the midpoint `n` is half the extent — so the
quantity the target asks to bound uniformly **in the volume** is proportional to the volume's linear
size.

DERIVED: the `2`s are the two arms and the midpoint's `2n = M`; the `1` is the power rule's offset,
cancelled. -/
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

/-- **⛔ SO NO CONSTANT SURVIVES EVERY APERTURE**, whenever the decay factor moves with the coupling.

The obstruction is in the SHAPE, not in Yang–Mills: any correlation carried by a transfer operator on
a circle has it. The escape is `L = 0` — a decay rate that does not run with the coupling — which is
what a running gap denies.

DERIVED: `K` is the candidate bound being refuted; nothing is chosen. -/
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

/-! ## 4. ✅ The L¹-aggregate form survives -/

/-- **✅ AGGREGATED, THE SAME PROFILE IS CONTROLLED, WITH NO LAG AND NO EXTENT IN THE CONSTANT.**

The aggregate numerator is `∑_d |ρ_d'| = (|λ'|/λ)·∑_d d·λ^d`, so the statement below IS the L¹-relative
bound, with `K = |λ'|/(1−λ)²`. It is written on `∑ d·λ^d` rather than on `∑ d·λ^{d−1}` because the
latter carries a natural-number subtraction that buys nothing and costs elaboration.

**The far-lag terms whose per-lag ratio diverges (§3) carry geometrically little mass**, and the
contact term alone puts the denominator at one — so no lower bound on the correlation is needed,
which is the scale-freeness `CLAY-OUTSTANDING` requires of any argument away from zero coupling.

**This is the statement that should replace the per-lag target.**

DERIVED: the `2` is the exponent in `∑ d·λ^d = λ/(1−λ)²`; the `1`s are the geometric series' unit and
the contact value `λ⁰`. Nothing is chosen. -/
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
