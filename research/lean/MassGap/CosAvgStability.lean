import Mathlib
import MassGap.FlatProfileAllApertures
import MassGap.LagTwoBound
import MassGap.LagTwoSix
import MassGap.FreeFieldLagTwoSix

/-!
# MassGap.CosAvgStability — the criterion under multiplicative and `L¹`-relative control

`CompactBeta` records two facts about the substrate side of the finite-grid route:

1. `clay_covariance_constant_not_aperture_uniform` — the unconditional Lipschitz constant is
   extensive. `cov_bound_extensive` gives `|Cov(O,S)| ≤ 4M·#Plaq`, and at the Clay reads the
   aperture is the extent, so `#Plaq = 16(N+1)⁴`. Evaluated, that is `L = 8192` at extent four and
   `93312` at extent six, hence `1.2e7` and `1.4e8` grid points over `β ∈ [0,3]`.
2. `profile_to_moment_not_uniformly_lipschitz` — normalising does not remove that. An additive
   sup-norm perturbation `t` in the raw profile moves `d2At` by `t/(1+t)·((N+1)/2)²`.

Both concern an additive perturbation, and the second concerns `d2At`. This file records what
happens to `cosAvgEven` — the quantity `ApertureRoute` reads — under a multiplicative one, where the
modulus is `2(K-1)/(2-K)`, carrying no aperture, extent or volume.

## Where the difference comes from

`d2At` weights lag `d` by `circLag d ^ 2`, which grows with the extent and supplies the `((N+1)/2)²`
above. `cosAvgEven` weights it by `cos θ_d`, which lies in `[-1, 1]` at every aperture.
`avg_stable_of_mul_close` isolates this: the modulus is proportional to the weight's sup-norm `W`, so
a bounded weight gives a bounded modulus, and the two criteria are not interchangeable for this
purpose.

`WilsonAnalytic.expect_hasDerivAt` gives `d⟨O⟩/dβ = -Cov(O,S)`, so multiplicative control over a step
is a bound on the logarithmic derivative `|d log ρ_d/dβ|`, while `cov_bound_extensive` bounds the
absolute one. The extensivity result is about the absolute bound and says nothing about the relative
one.

## Scope

On the criterion side this replaces "a modulus of continuity in `β` uniform in `N`" by a quantity
with no `N` in it. `confines_at_of_grid_point_and_mul_control` is the usable form: one grid point
clearing the floor by a margin `m`, plus multiplicative control `K` with `2(K-1)/(2-K) ≤ m`, gives
the criterion at every coupling the control reaches. At zero coupling the point mass gives
`cosAvgEven a 0 = 1`, so `m = 1 - 3^{-1/4} = 0.2401` and the admissible `K` is
`(2+2m)/(2+m) = 1.1072`: the profile may move by `10.7%` multiplicatively and the criterion
survives. Both are rounded away from the claim: `1.1073` would put the modulus at `0.240394` against
a margin of `0.2401643` and violate the inequality it is quoted under.

The middle interval remains open. The input it needs is a bound on `|d log ρ_d/dβ|` uniform in the
lag and the volume, a dynamical estimate that is not in the tree.

DERIVED: no numeral here is a magnitude. `1` and `2` in `1 ≤ K` and `K < 2` are the identity
perturbation and the point where the denominator `2 - K` of the modulus vanishes — the latter is
forced by the algebra (`(K-1)·P` must stay under the total mass `P` for the perturbed denominator to
remain positive), not chosen. The `2` in the numerator is the two terms of the quotient rule. `0` is
the contact lag and the positivity of the total mass. The floor `3 ^ (-(1:ℝ)/4)` is
`ApertureRoute`'s own constant, carried through unchanged.

## What the `flagship_…` statements cover

`MassGap.FlagshipScope`, the tree's own adversarial audit and deliberately not imported, measures
`ApertureRoute.flagship_of_confinement_at_an_aperture`. `flagship_for_bogus` derives the whole
conclusion (gap, non-triviality, `SO(4)`, OS0–OS3) for an object with no read, no correlation, no
gauge group and no lattice in it, tension the constant `0`; and `gap_summand_is_manufactured` shows
the gap clause's correlation there is a one-mode sequence whose magnitude is defined as its own
bound.

So the content of each `flagship_…` statement below sits at its `ConfinesAtAnAperture` hypothesis —
a statement about `cosAvgEven` of `readEven`, hence about `wilsonCorrAt` at an even aperture of at
least four — and the `FlagshipAt` step is packaging.
-/

namespace MassGap.CosAvgStability

open MassGap MassGap.EvenAperture MassGap.ApertureRoute MassGap.ConfinesZero

/-! ## 1. The abstract inequality -/

/-- A weighted average is stable under a multiplicative perturbation, with no volume factor. If `σ`
and `ρ` agree to within a multiplicative `K` at every index, the weighted averages `(∑ σ·w)/(∑ σ)`
and `(∑ ρ·w)/(∑ ρ)` differ by at most `2W(K-1)/(2-K)`, where `W` bounds `|w|`.

The index type is `Fin n` and `n` does not appear in the conclusion: the bound is proportional to the
weight's sup-norm and to the perturbation alone.

DERIVED: `1 ≤ K` is the identity perturbation, `K < 2` is where the perturbed total mass could
vanish, and the `2` in the numerator counts the two terms the quotient rule produces. `0 ≤ ρ d`,
`0 < ∑ d, ρ d` and `0 ≤ W` are sign conditions. -/
theorem avg_stable_of_mul_close {n : ℕ} (ρ σ w : Fin n → ℝ) (K W : ℝ)
    (hρ : ∀ d, 0 ≤ ρ d) (hP : 0 < ∑ d, ρ d)
    (hK1 : 1 ≤ K) (hK2 : K < 2)
    (hup : ∀ d, σ d ≤ K * ρ d)
    (hlo : ∀ d, ρ d ≤ K * σ d)
    (hW : 0 ≤ W) (hw : ∀ d, |w d| ≤ W) :
    |(∑ d, σ d * w d) / (∑ d, σ d) - (∑ d, ρ d * w d) / (∑ d, ρ d)|
      ≤ 2 * W * (K - 1) / (2 - K) := by
  have hK0 : (0 : ℝ) < K := by linarith
  have h2K : (0 : ℝ) < 2 - K := by linarith
  have hKm1 : (0 : ℝ) ≤ K - 1 := by linarith
  -- the pointwise error is relative
  have he : ∀ d, |σ d - ρ d| ≤ (K - 1) * ρ d := by
    intro d
    refine abs_le.mpr ⟨?_, ?_⟩
    · nlinarith [hlo d, hρ d, mul_nonneg (sq_nonneg (K - 1)) (hρ d), hK0]
    · nlinarith [hup d]
  set P := ∑ d, ρ d with hPdef
  set S := ∑ d, σ d with hSdef
  set N := ∑ d, ρ d * w d with hNdef
  set M := ∑ d, σ d * w d with hMdef
  -- the three sum bounds
  have hSP : S - P = ∑ d, (σ d - ρ d) := by
    rw [hSdef, hPdef, ← Finset.sum_sub_distrib]
  have hMN : M - N = ∑ d, (σ d - ρ d) * w d := by
    rw [hMdef, hNdef, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun d _ => by ring)
  have hB : |S - P| ≤ (K - 1) * P := by
    rw [hSP]
    calc |∑ d, (σ d - ρ d)| ≤ ∑ d, |σ d - ρ d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d, (K - 1) * ρ d := Finset.sum_le_sum (fun d _ => he d)
      _ = (K - 1) * P := by rw [hPdef, Finset.mul_sum]
  have hA : |M - N| ≤ (K - 1) * P * W := by
    rw [hMN]
    calc |∑ d, (σ d - ρ d) * w d| ≤ ∑ d, |(σ d - ρ d) * w d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d, ((K - 1) * ρ d) * W := by
            refine Finset.sum_le_sum (fun d _ => ?_)
            rw [abs_mul]
            exact mul_le_mul (he d) (hw d) (abs_nonneg _) (mul_nonneg hKm1 (hρ d))
      _ = (K - 1) * P * W := by
            rw [← Finset.sum_mul, ← Finset.mul_sum, hPdef]
            try ring
  have hNb : |N| ≤ W * P := by
    rw [hNdef]
    calc |∑ d, ρ d * w d| ≤ ∑ d, |ρ d * w d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d, ρ d * W := by
            refine Finset.sum_le_sum (fun d _ => ?_)
            rw [abs_mul, abs_of_nonneg (hρ d)]
            exact mul_le_mul_of_nonneg_left (hw d) (hρ d)
      _ = W * P := by
            rw [← Finset.sum_mul, hPdef, mul_comm]
            try ring
  -- the perturbed total mass stays positive
  have hSge : (2 - K) * P ≤ S := by
    have := (abs_le.mp hB).1
    linarith
  have hS0 : 0 < S := by nlinarith [hSge, mul_pos h2K hP]
  -- the quotient rule, exactly
  have hkey : M / S - N / P = (P * (M - N) - (S - P) * N) / (S * P) := by
    field_simp
    ring
  -- the numerator, bounded two-sidedly so no triangle-inequality name is needed
  have hPu : |P * (M - N)| ≤ P * ((K - 1) * P * W) := by
    rw [abs_mul, abs_of_pos hP]
    exact mul_le_mul_of_nonneg_left hA (le_of_lt hP)
  have hvN : |(S - P) * N| ≤ ((K - 1) * P) * (W * P) := by
    rw [abs_mul]
    exact mul_le_mul hB hNb (abs_nonneg _) (mul_nonneg hKm1 (le_of_lt hP))
  have hXb : |P * (M - N) - (S - P) * N| ≤ 2 * (K - 1) * P ^ 2 * W := by
    have h1 := abs_le.mp hPu
    have h2 := abs_le.mp hvN
    refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  -- and the division
  rw [hkey, abs_div, abs_of_pos (mul_pos hS0 hP),
    div_le_div_iff₀ (mul_pos hS0 hP) h2K]
  have hSP2 : (2 - K) * P * P ≤ S * P := mul_le_mul_of_nonneg_right hSge (le_of_lt hP)
  have hcoef : (0 : ℝ) ≤ 2 * W * (K - 1) := by positivity
  have hR : 2 * W * (K - 1) * ((2 - K) * P * P) ≤ 2 * W * (K - 1) * (S * P) :=
    mul_le_mul_of_nonneg_left hSP2 hcoef
  have hL : |P * (M - N) - (S - P) * N| * (2 - K)
      ≤ (2 * (K - 1) * P ^ 2 * W) * (2 - K) :=
    mul_le_mul_of_nonneg_right hXb (le_of_lt h2K)
  nlinarith [hL, hR]

#print axioms avg_stable_of_mul_close

/-! ## 2. On the Wilson criterion -/

/-- The cosine average in raw profile terms, with the weight separated from the coupling. It is the
identity `ConfinesZero.continuous_cosAvgEven` establishes inside its own proof, named here so it can
be applied.

DERIVED: `0` is the clamp `max β 0` that `readEven` imposes on the coupling, and the base point
`readEven a 0` at which the lag angles are taken. -/
theorem cosAvgEven_raw (a : EvenAp) (β : ℝ) :
    cosAvgEven a β
      = (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d * Real.cos ((readEven a 0).θ d))
        / (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d) := by
  have hsumeq : (∑ d', (readEven a β).ρ d')
      = ∑ d', MassGap.wilsonCorrAt a.1 (max β 0) d' := rfl
  show ∑ d, (readEven a β).p d * Real.cos ((readEven a β).θ d) = _
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  show (readEven a β).ρ d / (∑ d', (readEven a β).ρ d') * Real.cos ((readEven a β).θ d) = _
  rw [div_mul_eq_mul_div, readEven_rho, readEven_theta, hsumeq]

#print axioms cosAvgEven_raw

/-- The criterion moves by at most `2(K-1)/(2-K)` when the profile moves by a multiplicative `K`,
with no aperture, extent or volume in the modulus. It is `avg_stable_of_mul_close` at `W = 1`, `W = 1`
being available because the criterion's weight is a cosine.

The positivity of the total mass comes from `wilson_reflection_positive_at_even`, so this does not
consume the named axiom.

DERIVED: `1 ≤ K` and `K < 2` are `avg_stable_of_mul_close`'s own range for the perturbation, the `2`
in the numerator is its quotient-rule factor, and `0` is the coupling clamp `max β 0`. -/
theorem cosAvgEven_stable_of_mul_close (a : EvenAp) (β₁ β₂ K : ℝ)
    (hK1 : 1 ≤ K) (hK2 : K < 2)
    (hup : ∀ d, MassGap.wilsonCorrAt a.1 (max β₂ 0) d
      ≤ K * MassGap.wilsonCorrAt a.1 (max β₁ 0) d)
    (hlo : ∀ d, MassGap.wilsonCorrAt a.1 (max β₁ 0) d
      ≤ K * MassGap.wilsonCorrAt a.1 (max β₂ 0) d) :
    |cosAvgEven a β₂ - cosAvgEven a β₁| ≤ 2 * (K - 1) / (2 - K) := by
  have hrp := MassGap.wilson_reflection_positive_at_even a.1 a.2.choose a.2.choose_spec.1
    a.2.choose_spec.2 (le_max_right β₁ 0)
  rw [cosAvgEven_raw a β₁, cosAvgEven_raw a β₂]
  have h := avg_stable_of_mul_close
    (fun d => MassGap.wilsonCorrAt a.1 (max β₁ 0) d)
    (fun d => MassGap.wilsonCorrAt a.1 (max β₂ 0) d)
    (fun d => Real.cos ((readEven a 0).θ d)) K 1
    hrp.1 hrp.2 hK1 hK2 hup hlo zero_le_one
    (fun d => Real.abs_cos_le_one _)
  simpa using h

#print axioms cosAvgEven_stable_of_mul_close

/-- One grid point plus multiplicative control gives the criterion. If the cosine average clears the
entropy floor by a margin `m` at one coupling, and the profile at a second coupling is within a
multiplicative `K` of the first with `2(K-1)/(2-K) ≤ m`, then the criterion holds at the second
coupling.

Applied at `β₁ = 0`, where `ConfinesZero.cosAvgEven_at_zero` gives the value exactly `1`, the margin
is `m = 1 - 3^{-1/4} = 0.2401` and the admissible `K` is `(2+2m)/(2+m) = 1.1072`, so the profile may
move by `10.7%` multiplicatively. A theorem bounding that motion would be a bound on
`|d log ρ_d/dβ|`, which is not in the tree.

DERIVED: `1 ≤ K` and `K < 2` are `avg_stable_of_mul_close`'s range, the `2` in `2 * (K - 1) / (2 - K)`
its quotient-rule factor, `3 ^ (-(1 : ℝ) / 4)` is `ApertureRoute`'s floor, and `0` is the coupling
clamp `max β 0`. -/
theorem confines_at_of_grid_point_and_mul_control (a : EvenAp) (β₁ β₂ K m : ℝ)
    (hK1 : 1 ≤ K) (hK2 : K < 2)
    (hmod : 2 * (K - 1) / (2 - K) ≤ m)
    (hgrid : (3 : ℝ) ^ (-(1 : ℝ) / 4) + m < cosAvgEven a β₁)
    (hup : ∀ d, MassGap.wilsonCorrAt a.1 (max β₂ 0) d
      ≤ K * MassGap.wilsonCorrAt a.1 (max β₁ 0) d)
    (hlo : ∀ d, MassGap.wilsonCorrAt a.1 (max β₁ 0) d
      ≤ K * MassGap.wilsonCorrAt a.1 (max β₂ 0) d) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β₂ := by
  have hstab := cosAvgEven_stable_of_mul_close a β₁ β₂ K hK1 hK2 hup hlo
  have hlow := (abs_le.mp hstab).1
  linarith

#print axioms confines_at_of_grid_point_and_mul_control

/-! ## 3. Multiplicative control does not contain the conclusion -/

/-- Multiplicative control is satisfied by a gapless profile. The constant family `ρ ≡ 1` meets it at
every `K ≥ 1` and every pair of couplings while being equal at every lag, so the hypothesis of
`confines_at_of_grid_point_and_mul_control` does not contain the criterion it concludes.

Two neighbouring routes fail this check. `substrate_lt_of_tension_lt_floor` takes `μ < κ₀` as its
hypothesis, and by `ApertureRoute.confines_iff_pos_and_tension_lt_floor` that hypothesis is
confinement at the aperture and coupling in question (`DiffractionNoGo`).
`WeakArm.no_uniform_quartic_constant_of_vanishing_rate` needs a rate bounded away from zero uniformly
in the coupling and the aperture, which is the gap itself.

DERIVED: `1` is the constant family's value and the identity perturbation, and `0` is the strict
positivity the family is required to have at every lag; `K` is a variable. -/
theorem mul_control_does_not_imply_decay {n : ℕ} (K : ℝ) (hK : 1 ≤ K) :
    ∃ ρ : ℝ → Fin n → ℝ,
      (∀ β d, 0 < ρ β d) ∧
      (∀ β₁ β₂ d, ρ β₂ d ≤ K * ρ β₁ d) ∧
      (∀ β₁ β₂ d, ρ β₁ d ≤ K * ρ β₂ d) ∧
      (∀ β : ℝ, ∀ d e : Fin n, ρ β d = ρ β e) := by
  refine ⟨fun _ _ => 1, fun _ _ => one_pos, ?_, ?_, fun _ _ _ => rfl⟩
  · intro _ _ _; simpa using hK
  · intro _ _ _; simpa using hK

#print axioms mul_control_does_not_imply_decay

/-! ## 4. The constant, evaluated at zero coupling -/

/-- The admissible multiplicative perturbation at zero coupling is `1.1072`: its modulus
`2(K-1)/(2-K)` fits inside the margin `1 - 3^{-1/4}`.

CHOSEN: `1.1072` is rounded down, away from the claim that this `K` is admissible. The exact
supremum is `(2+2m)/(2+m) = 1.10720834…` at `m = 1 - 3^{-1/4} = 0.24016431…`; `1.1073` would put the
modulus at `0.240394`, above the margin. The bracket on the floor `3 ^ (-(1 : ℝ) / 4)` is
`LagTwoBound.floor_bounds`, and the `2`s are the quotient-rule factor and the denominator `2 - K`. -/
theorem admissible_K_at_zero_coupling :
    2 * ((1.1072 : ℝ) - 1) / (2 - 1.1072) ≤ 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
  have h := MassGap.LagTwoBound.floor_bounds
  have hnum : 2 * ((1.1072 : ℝ) - 1) / (2 - 1.1072) < 0.240164 := by norm_num
  linarith [h.2]

#print axioms admissible_K_at_zero_coupling

/-- A pointwise multiplicative bound based at zero coupling forces a point mass.
`PowerTail.wilsonCorrAt_at_zero_coupling` puts the profile at zero coupling at exactly zero on every
lag of nonzero circle distance, so `ρ_d(β) ≤ K · ρ_d(0) = 0` forces `ρ_d(β) = 0` there, whatever `K`
is. The hypothesis is met only where the correlation vanishes at every nonzero lag.

The `L¹`-relative hypothesis of section 5 has no such degeneracy, because it measures the change
against the total mass rather than against the value at the same lag, and the total mass at zero
coupling is the contact value, which `contact_value_pos_at_zero_coupling` puts strictly above zero.

DERIVED: `0` is zero coupling and the value the profile takes off the contact lag; `1` is the circle
distance at which that vanishing begins. -/
theorem mul_control_from_zero_forces_a_point_mass {N : ℕ} {K : ℝ} {β : ℝ}
    (hup : ∀ d : Fin (N + 1), MassGap.wilsonCorrAt N β d ≤ K * MassGap.wilsonCorrAt N 0 d)
    (hnn : ∀ d : Fin (N + 1), 0 ≤ MassGap.wilsonCorrAt N β d) :
    ∀ d : Fin (N + 1), 1 ≤ Moment.circLag d → MassGap.wilsonCorrAt N β d = 0 := by
  intro d hd
  have hz := MassGap.PowerTail.wilsonCorrAt_at_zero_coupling N d hd
  have h := hup d
  rw [hz, mul_zero] at h
  exact le_antisymm h (hnn d)

#print axioms mul_control_from_zero_forces_a_point_mass

/-! ## 5. The `L¹`-relative form -/

/-- The same stability from an `L¹`-relative hypothesis, with a smaller modulus. Instead of
controlling each lag against its own value, control the total change against the total mass:
`∑ |σ - ρ| ≤ ε · ∑ ρ`. Then the weighted averages differ by at most `2Wε/(1-ε)`.

`n` does not appear, as in `avg_stable_of_mul_close`, and the denominator is `1 - ε` rather than
`2 - K`. Pointwise multiplicative closeness implies this hypothesis with `ε = K - 1`.

DERIVED: `ε < 1` is where the perturbed total mass could vanish, forced by the algebra rather than
chosen; the `2` in the numerator counts the two terms the quotient rule produces. `0 ≤ ρ d`,
`0 < ∑ d, ρ d`, `0 ≤ ε` and `0 ≤ W` are sign conditions. -/
theorem avg_stable_of_l1_close {n : ℕ} (ρ σ w : Fin n → ℝ) (ε W : ℝ)
    (hρ : ∀ d, 0 ≤ ρ d) (hP : 0 < ∑ d, ρ d)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hl1 : ∑ d, |σ d - ρ d| ≤ ε * ∑ d, ρ d)
    (hW : 0 ≤ W) (hw : ∀ d, |w d| ≤ W) :
    |(∑ d, σ d * w d) / (∑ d, σ d) - (∑ d, ρ d * w d) / (∑ d, ρ d)|
      ≤ 2 * W * ε / (1 - ε) := by
  have h1ε : (0 : ℝ) < 1 - ε := by linarith
  set P := ∑ d, ρ d with hPdef
  set S := ∑ d, σ d with hSdef
  set N := ∑ d, ρ d * w d with hNdef
  set M := ∑ d, σ d * w d with hMdef
  have hSP : S - P = ∑ d, (σ d - ρ d) := by
    rw [hSdef, hPdef, ← Finset.sum_sub_distrib]
  have hMN : M - N = ∑ d, (σ d - ρ d) * w d := by
    rw [hMdef, hNdef, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun d _ => by ring)
  have hB : |S - P| ≤ ε * P := by
    rw [hSP]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) hl1
  have hA : |M - N| ≤ ε * P * W := by
    rw [hMN]
    have hstep : ∑ d, |(σ d - ρ d) * w d| ≤ (∑ d, |σ d - ρ d|) * W := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun d _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hw d) (abs_nonneg _)
    have hl1W : (∑ d, |σ d - ρ d|) * W ≤ (ε * P) * W :=
      mul_le_mul_of_nonneg_right hl1 hW
    calc |∑ d, (σ d - ρ d) * w d| ≤ ∑ d, |(σ d - ρ d) * w d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ (∑ d, |σ d - ρ d|) * W := hstep
      _ ≤ ε * P * W := hl1W
  have hNb : |N| ≤ W * P := by
    rw [hNdef]
    calc |∑ d, ρ d * w d| ≤ ∑ d, |ρ d * w d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d, ρ d * W := by
            refine Finset.sum_le_sum (fun d _ => ?_)
            rw [abs_mul, abs_of_nonneg (hρ d)]
            exact mul_le_mul_of_nonneg_left (hw d) (hρ d)
      _ = W * P := by
            rw [← Finset.sum_mul, hPdef, mul_comm]
            try ring
  have hSge : (1 - ε) * P ≤ S := by
    have := (abs_le.mp hB).1
    linarith
  have hS0 : 0 < S := by nlinarith [hSge, mul_pos h1ε hP]
  have hkey : M / S - N / P = (P * (M - N) - (S - P) * N) / (S * P) := by
    field_simp
    ring
  have hPu : |P * (M - N)| ≤ P * (ε * P * W) := by
    rw [abs_mul, abs_of_pos hP]
    exact mul_le_mul_of_nonneg_left hA (le_of_lt hP)
  have hvN : |(S - P) * N| ≤ (ε * P) * (W * P) := by
    rw [abs_mul]
    exact mul_le_mul hB hNb (abs_nonneg _) (mul_nonneg hε0 (le_of_lt hP))
  have hXb : |P * (M - N) - (S - P) * N| ≤ 2 * ε * P ^ 2 * W := by
    have h1 := abs_le.mp hPu
    have h2 := abs_le.mp hvN
    refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  rw [hkey, abs_div, abs_of_pos (mul_pos hS0 hP),
    div_le_div_iff₀ (mul_pos hS0 hP) h1ε]
  have hSP2 : (1 - ε) * P * P ≤ S * P := mul_le_mul_of_nonneg_right hSge (le_of_lt hP)
  have hcoef : (0 : ℝ) ≤ 2 * W * ε := by positivity
  have hR : 2 * W * ε * ((1 - ε) * P * P) ≤ 2 * W * ε * (S * P) :=
    mul_le_mul_of_nonneg_left hSP2 hcoef
  have hL : |P * (M - N) - (S - P) * N| * (1 - ε)
      ≤ (2 * ε * P ^ 2 * W) * (1 - ε) :=
    mul_le_mul_of_nonneg_right hXb (le_of_lt h1ε)
  nlinarith [hL, hR]

#print axioms avg_stable_of_l1_close

/-- The criterion under `L¹`-relative control: `avg_stable_of_l1_close` at `W = 1`, available
because the criterion's weight is a cosine. The positivity of the total mass comes from
`wilson_reflection_positive_at_even`, so this does not consume the named axiom.

DERIVED: `0 ≤ ε` and `ε < 1` are `avg_stable_of_l1_close`'s range, the `2` in `2 * ε / (1 - ε)` its
quotient-rule factor, and `0` is also the coupling clamp `max β 0`. -/
theorem cosAvgEven_stable_of_l1_close (a : EvenAp) (β₁ β₂ ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hl1 : ∑ d, |MassGap.wilsonCorrAt a.1 (max β₂ 0) d - MassGap.wilsonCorrAt a.1 (max β₁ 0) d|
      ≤ ε * ∑ d, MassGap.wilsonCorrAt a.1 (max β₁ 0) d) :
    |cosAvgEven a β₂ - cosAvgEven a β₁| ≤ 2 * ε / (1 - ε) := by
  have hrp := MassGap.wilson_reflection_positive_at_even a.1 a.2.choose a.2.choose_spec.1
    a.2.choose_spec.2 (le_max_right β₁ 0)
  rw [cosAvgEven_raw a β₁, cosAvgEven_raw a β₂]
  have h := avg_stable_of_l1_close
    (fun d => MassGap.wilsonCorrAt a.1 (max β₁ 0) d)
    (fun d => MassGap.wilsonCorrAt a.1 (max β₂ 0) d)
    (fun d => Real.cos ((readEven a 0).θ d)) ε 1
    hrp.1 hrp.2 hε0 hε1 hl1 zero_le_one
    (fun d => Real.abs_cos_le_one _)
  simpa using h

#print axioms cosAvgEven_stable_of_l1_close

/-- One grid point plus `L¹`-relative control gives the criterion: a coupling `β₁` whose cosine
average clears the floor by `m`, and `L¹`-relative motion `ε` with `2ε/(1-ε) ≤ m`, give the criterion
at `β₂`.

DERIVED: `0 ≤ ε` and `ε < 1` are the range, the `2` in `2 * ε / (1 - ε)` the quotient-rule factor,
`3 ^ (-(1 : ℝ) / 4)` the floor, and `0` the coupling clamp `max β 0`. -/
theorem confines_at_of_grid_point_and_l1_control (a : EvenAp) (β₁ β₂ ε m : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hmod : 2 * ε / (1 - ε) ≤ m)
    (hgrid : (3 : ℝ) ^ (-(1 : ℝ) / 4) + m < cosAvgEven a β₁)
    (hl1 : ∑ d, |MassGap.wilsonCorrAt a.1 (max β₂ 0) d - MassGap.wilsonCorrAt a.1 (max β₁ 0) d|
      ≤ ε * ∑ d, MassGap.wilsonCorrAt a.1 (max β₁ 0) d) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β₂ := by
  have hstab := cosAvgEven_stable_of_l1_close a β₁ β₂ ε hε0 hε1 hl1
  have hlow := (abs_le.mp hstab).1
  linarith

#print axioms confines_at_of_grid_point_and_l1_control

/-- The criterion at every coupling whose profile has moved by under `10.72%` of the contact value,
measured in `L¹` against the zero-coupling profile.

At zero coupling the profile is a point mass at the contact lag
(`PowerTail.wilsonCorrAt_at_zero_coupling`, `contact_value_pos_at_zero_coupling`), so the total mass
`∑ ρ_d(0)` is the contact value `ρ_0(0)`, strictly positive, and the hypothesis says the total change
in the profile since zero coupling is at most `10.72%` of it. That quantity is not identically zero,
unlike the pointwise multiplicative hypothesis, which
`mul_control_from_zero_forces_a_point_mass` meets at no positive coupling whose correlation is
anywhere nonzero. `l1_control_from_zero_holds_near_zero` shows this hypothesis met on a
neighbourhood of zero coupling.

`ConfinesZero.cosAvgEven_at_zero` gives the cosine average exactly `1` at zero coupling, so the whole
margin `1 - 3^{-1/4}` is available.

CHOSEN: `0.1072` and `0.240164` are rounded down, away from the claim that this `ε` is admissible.
The exact supremum is `m/(2+m) = 0.10720822…` at the certified margin `m = 0.240164`; `0.1073` would
put the modulus at `0.2403943`, above the margin. The bracket on the floor `3 ^ (-(1 : ℝ) / 4)` is
`LagTwoBound.floor_bounds`, and `0` is also the coupling clamp `max β 0`. -/
theorem confines_at_of_l1_control_from_zero (a : EvenAp) (β : ℝ)
    (hl1 : ∑ d, |MassGap.wilsonCorrAt a.1 (max β 0) d - MassGap.wilsonCorrAt a.1 (max (0 : ℝ) 0) d|
      ≤ 0.1072 * ∑ d, MassGap.wilsonCorrAt a.1 (max (0 : ℝ) 0) d) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β := by
  refine confines_at_of_grid_point_and_l1_control a 0 β 0.1072 0.240164
    (by norm_num) (by norm_num) (by norm_num) ?_ hl1
  rw [cosAvgEven_at_zero a]
  have h := MassGap.LagTwoBound.floor_bounds
  linarith [h.2]

#print axioms confines_at_of_l1_control_from_zero

/-- The hypothesis of `confines_at_of_l1_control_from_zero` is met on a neighbourhood of zero
coupling.

The `L¹` distance from the zero-coupling profile is continuous in the coupling
(`continuous_wilsonCorrAt`) and vanishes at zero coupling, while the right-hand side is a fixed
positive number — `10.72%` of the contact value, positive by `wilson_reflection_positive_at_even` —
so the inequality holds on a ball.

Scope: the radius is existential and no value is named for it. Supplying one for all of `[0, ∞)` is
B5.

DERIVED: `0` is zero coupling, the clamp `max β 0`, and the sign of the radius `b`; `0.1072` is
`confines_at_of_l1_control_from_zero`'s constant, carried unchanged. -/
theorem l1_control_from_zero_holds_near_zero (a : EvenAp) :
    ∃ b > 0, ∀ β : ℝ, |β| < b →
      ∑ d, |MassGap.wilsonCorrAt a.1 (max β 0) d - MassGap.wilsonCorrAt a.1 (max (0 : ℝ) 0) d|
        ≤ 0.1072 * ∑ d, MassGap.wilsonCorrAt a.1 (max (0 : ℝ) 0) d := by
  have hclamp : Continuous (fun β : ℝ => max β 0) := continuous_id.max continuous_const
  have hcont : Continuous (fun β : ℝ =>
      ∑ d, |MassGap.wilsonCorrAt a.1 (max β 0) d
        - MassGap.wilsonCorrAt a.1 (max (0 : ℝ) 0) d|) :=
    continuous_finsetSum _ (fun d _ =>
      (((continuous_wilsonCorrAt a.1 d).comp hclamp).sub continuous_const).abs)
  have hrp := MassGap.wilson_reflection_positive_at_even a.1 a.2.choose a.2.choose_spec.1
    a.2.choose_spec.2 (le_max_right (0 : ℝ) 0)
  have hpos : (0 : ℝ) < 0.1072 * ∑ d, MassGap.wilsonCorrAt a.1 (max (0 : ℝ) 0) d := by
    have h := hrp.2
    linarith
  have hat0 : (∑ d, |MassGap.wilsonCorrAt a.1 (max (0 : ℝ) 0) d
      - MassGap.wilsonCorrAt a.1 (max (0 : ℝ) 0) d|)
      < 0.1072 * ∑ d, MassGap.wilsonCorrAt a.1 (max (0 : ℝ) 0) d := by
    simpa using hpos
  have hev : ∀ᶠ β in nhds (0 : ℝ),
      (∑ d, |MassGap.wilsonCorrAt a.1 (max β 0) d
        - MassGap.wilsonCorrAt a.1 (max (0 : ℝ) 0) d|)
        < 0.1072 * ∑ d, MassGap.wilsonCorrAt a.1 (max (0 : ℝ) 0) d :=
    hcont.continuousAt (gt_mem_nhds hat0)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨b, hb, hball⟩ := hev
  refine ⟨b, hb, fun β hβ => le_of_lt (hball ?_)⟩
  simpa [Real.dist_eq] using hβ

#print axioms l1_control_from_zero_holds_near_zero

/-- The criterion on a neighbourhood of zero coupling, reached through
`confines_at_of_l1_control_from_zero`, so the radius is tied to how far the profile has moved in `L¹`
relative to the contact value.

`ConfinesZero.confines_near_zero` gives a neighbourhood too, from continuity of the cosine average
alone. The two agree where they overlap; the `L¹` route additionally extends to every coupling the
`L¹` control reaches.

DERIVED: `0` is zero coupling and the sign of the radius `b`, and `3 ^ (-(1 : ℝ) / 4)` is
`ApertureRoute`'s floor. -/
theorem confines_near_zero_via_l1 (a : EvenAp) :
    ∃ b > 0, ∀ β : ℝ, |β| < b → (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β := by
  obtain ⟨b, hb, h⟩ := l1_control_from_zero_holds_near_zero a
  exact ⟨b, hb, fun β hβ => confines_at_of_l1_control_from_zero a β (h β hβ)⟩

#print axioms confines_near_zero_via_l1

/-! ## 6. The finite-grid route, and the flagship from two named hypotheses -/

/-- `L¹`-relative closeness of the profile at `β₂` to the profile at `β₁`, named so the grid
statements below read. The coupling is clamped at `max · 0` as `readEven` clamps it.

DERIVED: no numeral is a magnitude. `0` is the clamp `EvenAperture.readEven_eq_at_zero` imposes;
`ε` is a variable. -/
def L1Close (a : EvenAp) (β₁ β₂ ε : ℝ) : Prop :=
  ∑ d, |MassGap.wilsonCorrAt a.1 (max β₂ 0) d - MassGap.wilsonCorrAt a.1 (max β₁ 0) d|
    ≤ ε * ∑ d, MassGap.wilsonCorrAt a.1 (max β₁ 0) d

#print axioms L1Close

/-- The finite-grid route stated in `cosAvgEven`. Certify the cosine average at each of a family of
couplings, each clearing the floor by a margin `m`; control the `L¹`-relative motion of the profile
inside each cell by `ε` with `2ε/(1-ε) ≤ m`; and the criterion holds at every coupling the cells
cover.

`ι` is an arbitrary `Sort*`: the argument does not need the grid to be finite, so finiteness is not
assumed.

Scope: this converts the middle interval from a `∀ β` estimate into a list of certified values plus
a modulus. Each `cosAvgEven a (grid i)` is a Haar integral over `SU(3)` on the whole lattice, and by
the compression argument in `CompactBeta` a Monte Carlo value can refute such a bound and not
establish one. The modulus between cells carries no volume, unlike `CompactBeta`'s extensive
Lipschitz constant.

DERIVED: `0 ≤ ε` and `ε < 1` are `avg_stable_of_l1_close`'s range, the `2` in `2 * ε / (1 - ε)` its
quotient-rule factor, `3 ^ (-(1 : ℝ) / 4)` is `ApertureRoute`'s floor, and `0` is also the coupling
clamp. `S`, `m`, `ε` and the grid are variables. -/
theorem confines_on_set_of_grid {ι : Sort*} (a : EvenAp) (grid : ι → ℝ) (ε m : ℝ) (S : Set ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hmod : 2 * ε / (1 - ε) ≤ m)
    (hvals : ∀ i, (3 : ℝ) ^ (-(1 : ℝ) / 4) + m < cosAvgEven a (grid i))
    (hcover : ∀ β ∈ S, ∃ i, L1Close a (grid i) β ε) :
    ∀ β ∈ S, (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β := by
  intro β hβ
  obtain ⟨i, hi⟩ := hcover β hβ
  exact confines_at_of_grid_point_and_l1_control a (grid i) β ε m hε0 hε1 hmod (hvals i) hi

#print axioms confines_on_set_of_grid

/-- `ApertureRoute.ConfinesAtAnAperture` from two hypotheses, at an arbitrary even aperture:

* a grid on `[0, B]` — certified values of the cosine average, each clearing the floor by `m`, with
  the cells covered to `L¹`-relative accuracy `ε` satisfying `2ε/(1-ε) ≤ m`;
* a far arm on `[B, ∞)` — the criterion at every coupling above the cut.

The negative half-line needs nothing: `ConfinesZero.cosAvgEven_eq_one_of_nonpos` clamps it, so the
cosine average is exactly `1` there and `floor_lt_one` clears the floor. That is the clamp `readEven`
imposes rather than an assumption made here.

`FreeFieldLagTwoSix.confines_of_arms_six` assembles the same two halves at extent six through the
lag-two reduction. This assembles them at any even aperture through `cosAvgEven`, with the middle
half a list rather than a `∀ β` statement.

DERIVED: `0` is the bottom of the coupling range and the clamp; `0 ≤ ε`, `ε < 1` and the `2` in
`2 * ε / (1 - ε)` are `avg_stable_of_l1_close`'s range and quotient-rule factor; and
`3 ^ (-(1 : ℝ) / 4)` is `ApertureRoute`'s floor. `B`, `ε`, `m` and the grid are variables. -/
theorem confines_of_grid_and_far_arm {ι : Sort*} (a : EvenAp) (grid : ι → ℝ) (ε m B : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hmod : 2 * ε / (1 - ε) ≤ m)
    (hvals : ∀ i, (3 : ℝ) ^ (-(1 : ℝ) / 4) + m < cosAvgEven a (grid i))
    (hcover : ∀ β : ℝ, 0 ≤ β → β ≤ B → ∃ i, L1Close a (grid i) β ε)
    (hfar : ∀ β : ℝ, B ≤ β → (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β) :
    ApertureRoute.ConfinesAtAnAperture := by
  refine ⟨a, fun β => ?_⟩
  rcases le_total β 0 with hle | hnn
  · rw [cosAvgEven_eq_one_of_nonpos a hle]
    exact floor_lt_one
  · rcases le_total β B with hmid | hge
    · exact confines_on_set_of_grid a grid ε m {x : ℝ | 0 ≤ x ∧ x ≤ B} hε0 hε1 hmod hvals
        (fun x hx => hcover x hx.1 hx.2) β ⟨hnn, hmid⟩
    · exact hfar β hge

#print axioms confines_of_grid_and_far_arm

/-- `ApertureRoute.FlagshipAt` applied to `confines_of_grid_and_far_arm`, through
`ApertureRoute.flagship_of_confinement_at_an_aperture` — gap, non-triviality, `SO(4)` and the
continuum object. The content is the `ConfinesAtAnAperture` argument; see the header.

DERIVED: the numerals are `confines_of_grid_and_far_arm`'s own — `0 ≤ ε`, `ε < 1`, the `2` in
`2 * ε / (1 - ε)`, the floor `3 ^ (-(1 : ℝ) / 4)`, and `0` as the bottom of the coupling range. -/
theorem flagship_of_grid_and_far_arm {ι : Sort*} (a : EvenAp) (grid : ι → ℝ) (ε m B : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hmod : 2 * ε / (1 - ε) ≤ m)
    (hvals : ∀ i, (3 : ℝ) ^ (-(1 : ℝ) / 4) + m < cosAvgEven a (grid i))
    (hcover : ∀ β : ℝ, 0 ≤ β → β ≤ B → ∃ i, L1Close a (grid i) β ε)
    (hfar : ∀ β : ℝ, B ≤ β → (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β) :
    ApertureRoute.FlagshipAt
      (confines_of_grid_and_far_arm a grid ε m B hε0 hε1 hmod hvals hcover hfar) :=
  ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_grid_and_far_arm

/-- The grid and cover hypotheses of `confines_of_grid_and_far_arm` hold together on an interval.
The one-point grid `{0}` clears the floor by the full margin, because
`ConfinesZero.cosAvgEven_at_zero` puts the cosine average at exactly `1` there, and
`l1_control_from_zero_holds_near_zero` covers `[0, B]` for small enough `B`.

Scope: `B` here is existential and small. The far-arm hypothesis is not addressed.

DERIVED: `0.240164` is the certified margin under `1 - 3^{-1/4}` and `0.1072` the `ε` that fits
inside it, both as in `confines_at_of_l1_control_from_zero` and both rounded away from the claim.
The `2` is the halving that puts `B` strictly inside the radius the continuity argument supplies,
`3 ^ (-(1 : ℝ) / 4)` is the floor, and `0` is zero coupling and the sign of `B`. -/
theorem grid_hypotheses_are_met_near_zero (a : EvenAp) :
    ∃ B : ℝ, 0 < B ∧
      (∀ _i : Unit, (3 : ℝ) ^ (-(1 : ℝ) / 4) + 0.240164 < cosAvgEven a 0) ∧
      (∀ β : ℝ, 0 ≤ β → β ≤ B → ∃ _i : Unit, L1Close a 0 β 0.1072) := by
  obtain ⟨b, hb, hball⟩ := l1_control_from_zero_holds_near_zero a
  refine ⟨b / 2, by linarith, fun _ => ?_, fun β hβ0 hβB => ⟨(), ?_⟩⟩
  · rw [cosAvgEven_at_zero a]
    have h := MassGap.LagTwoBound.floor_bounds
    linarith [h.2]
  · exact hball β (by rw [abs_of_nonneg hβ0]; linarith)

#print axioms grid_hypotheses_are_met_near_zero

/-! ## 7. An arbitrary reference profile, and the full assembly at extent six -/

/-- The criterion from `L¹`-closeness to any reference profile whose own cosine average clears the
floor. The reference `r` need not be a Wilson profile at any coupling: it is any nonnegative profile
with positive total mass whose average, taken against the lag angles of `readEven a 0`, exceeds the
floor by `m`.

Both arms of B5 are instances. The near arm takes `r` to be the zero-coupling profile, a point mass
at the contact lag with average exactly `1` (`ConfinesZero.cosAvgEven_at_zero`); the far arm takes
`r` to be the free-field profile `(fsCorr6 d)²`, whose average at extent six is
`64165878255868/65459706282889 = 0.98023…` (`freeRefSix_avg_eq`).

DERIVED: `r`, `ε` and `m` are variables. `0 ≤ r d`, `0 < ∑ d, r d` and `0 ≤ ε` are sign conditions,
`ε < 1` and the `2` in `2 * ε / (1 - ε)` are `avg_stable_of_l1_close`'s range and quotient-rule
factor, `3 ^ (-(1 : ℝ) / 4)` is `ApertureRoute`'s floor, `0` is also the coupling clamp `max β 0` and
the base point `readEven a 0`, and the `1` in `Fin (a.1 + 1)` is the lag arity. -/
theorem confines_at_of_l1_close_to_reference (a : EvenAp) (β : ℝ) (r : Fin (a.1 + 1) → ℝ)
    (ε m : ℝ)
    (hr : ∀ d, 0 ≤ r d) (hrP : 0 < ∑ d, r d)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hmod : 2 * ε / (1 - ε) ≤ m)
    (hval : (3 : ℝ) ^ (-(1 : ℝ) / 4) + m
      < (∑ d, r d * Real.cos ((readEven a 0).θ d)) / (∑ d, r d))
    (hl1 : ∑ d, |MassGap.wilsonCorrAt a.1 (max β 0) d - r d| ≤ ε * ∑ d, r d) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β := by
  rw [cosAvgEven_raw a β]
  have h := avg_stable_of_l1_close r
    (fun d => MassGap.wilsonCorrAt a.1 (max β 0) d)
    (fun d => Real.cos ((readEven a 0).θ d)) ε 1
    hr hrP hε0 hε1 hl1 zero_le_one (fun d => Real.abs_cos_le_one _)
  have hlow := (abs_le.mp h).1
  have hmod' : 2 * 1 * ε / (1 - ε) ≤ m := by
    have : 2 * (1 : ℝ) * ε = 2 * ε := by ring
    rw [this]; exact hmod
  linarith

#print axioms confines_at_of_l1_close_to_reference

/-- The assembly at extent six: a grid for the middle interval and the lag-two ratio for the far
arm.

The two halves take different reductions:

* the middle goes through `cosAvgEven`, where the modulus between grid cells carries no volume
  (`avg_stable_of_l1_close`) while `CompactBeta`'s Lipschitz constant is extensive;
* the far arm goes through the lag-two reduction, where `FreeFieldLagTwoSix.epsMaxSix = 24/25` lets
  the Gaussian be `96%` wrong. An `L¹` bound on the whole profile against the free-field reference
  admits only `9.9%` — the free-field cosine average at extent six is `0.98023…`, so the margin over
  the floor is `0.2204` and `m/(2+m)` is `0.0992`. The lag-two route is `9.7×` more tolerant there,
  reading one ratio with `65.6×` of room rather than the whole profile.

`hfar` is what `FreeFieldLagTwoSix.effective_lag_two_bound_six` produces from
`EffectiveGaussianLagTwoSix`.

DERIVED: `5` is the aperture — `wilsonCorrAt 5` is the extent-six torus — and `2` and `0` are the
lags the far-arm ratio relates, `0` being also the bottom of the coupling range and the clamp.
`0 ≤ ε`, `ε < 1` and the `2` in `2 * ε / (1 - ε)` are `avg_stable_of_l1_close`'s range and
quotient-rule factor, and `3 ^ (-(1 : ℝ) / 4)` is `ApertureRoute`'s floor. `B`, `ε`, `m`, `K` and the
grid are variables. -/
theorem confines_of_grid_and_lag_two_far_arm_six {ι : Sort*} (grid : ι → ℝ) (ε m B K : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hmod : 2 * ε / (1 - ε) ≤ m)
    (hvals : ∀ i, (3 : ℝ) ^ (-(1 : ℝ) / 4) + m < cosAvgEven ConfinesZero.ap6 (grid i))
    (hcover : ∀ β : ℝ, 0 ≤ β → β ≤ B → ∃ i, L1Close ConfinesZero.ap6 (grid i) β ε)
    (hK : K < MassGap.LagTwoSix.lagTwoThresholdSix)
    (hfar : ∀ β : ℝ, B ≤ β →
      MassGap.wilsonCorrAt 5 (max β 0) 2 ≤ K * MassGap.wilsonCorrAt 5 (max β 0) 0) :
    ApertureRoute.ConfinesAtAnAperture :=
  confines_of_grid_and_far_arm ConfinesZero.ap6 grid ε m B hε0 hε1 hmod hvals hcover
    (fun β hβ => MassGap.LagTwoSix.confines_extent_six_of_lag_two_ratio hK (hfar β hβ))

#print axioms confines_of_grid_and_lag_two_far_arm_six

/-- `ApertureRoute.FlagshipAt` applied to `confines_of_grid_and_lag_two_far_arm_six`: gap,
non-triviality, `SO(4)` and the continuum object, from a grid on `[0,B]` and the lag-two bound above
it. The content is the `ConfinesAtAnAperture` argument; see the header.

DERIVED: the numerals are `confines_of_grid_and_lag_two_far_arm_six`'s own — `5` the aperture of the
extent-six torus, `2` and `0` the lags the far-arm ratio relates, `0 ≤ ε`, `ε < 1`, the `2` in
`2 * ε / (1 - ε)`, and the floor `3 ^ (-(1 : ℝ) / 4)`. -/
theorem flagship_of_grid_and_lag_two_far_arm_six {ι : Sort*} (grid : ι → ℝ) (ε m B K : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hmod : 2 * ε / (1 - ε) ≤ m)
    (hvals : ∀ i, (3 : ℝ) ^ (-(1 : ℝ) / 4) + m < cosAvgEven ConfinesZero.ap6 (grid i))
    (hcover : ∀ β : ℝ, 0 ≤ β → β ≤ B → ∃ i, L1Close ConfinesZero.ap6 (grid i) β ε)
    (hK : K < MassGap.LagTwoSix.lagTwoThresholdSix)
    (hfar : ∀ β : ℝ, B ≤ β →
      MassGap.wilsonCorrAt 5 (max β 0) 2 ≤ K * MassGap.wilsonCorrAt 5 (max β 0) 0) :
    ApertureRoute.FlagshipAt
      (confines_of_grid_and_lag_two_far_arm_six grid ε m B K hε0 hε1 hmod hvals hcover hK hfar) :=
  ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_grid_and_lag_two_far_arm_six

/-! ## 8. The free-field reference at extent six, evaluated -/

/-- The lag angle at extent six, unfolded. `Moment.Read.θ` discards its read, so this holds by
`rfl`; it is stated so the generic reduction below can be applied to a profile that is not a Wilson
correlation.

DERIVED: `Fin 6` is the extent-six lag index, `5` the aperture, and `2 * Real.pi * d / (5 + 1)` the
lag angle `Moment.Read.θ` defines; `0` is the base coupling at which the angles are read. -/
theorem theta_six (d : Fin 6) :
    (readEven ConfinesZero.ap6 0).θ d = 2 * Real.pi * ((d : ℕ) : ℝ) / (((5 : ℕ) : ℝ) + 1) := rfl

#print axioms theta_six

/-- The extent-six weighted average of an arbitrary symmetric profile.
`ConfinesZero.cosAvgEven_extent_six` computes this for the Wilson profile; the reference route needs
it for a profile that is not one, so the same cosines are applied to an arbitrary `r` with the circle
symmetry carried as the hypotheses `r 5 = r 1` and `r 4 = r 2` rather than proved from
`MomentShape.wilsonCorrAt_neg`.

DERIVED: `Fin 6` is the extent-six lag index and `0`, `1`, `2`, `3`, `4`, `5` are its lags, at which
the cosines are `1, ½, −½, −1, −½, ½`; the hypotheses `r 5 = r 1` and `r 4 = r 2` are the circle
fold, and the coefficients `2 * r 1` and `2 * r 2` in the denominator are the multiplicities that
fold produces. `0` is also the base coupling `readEven ConfinesZero.ap6 0` the angles are read at.
No magnitude is chosen. -/
theorem sixAvg_of_symmetric (r : Fin 6 → ℝ) (h5 : r 5 = r 1) (h4 : r 4 = r 2) :
    (∑ d, r d * Real.cos ((readEven ConfinesZero.ap6 0).θ d)) / (∑ d, r d)
      = (r 0 + r 1 - r 2 - r 3) / (r 0 + 2 * r 1 + 2 * r 2 + r 3) := by
  simp only [theta_six]
  simp only [Fin.sum_univ_six]
  have hd : ((5 : ℕ) : ℝ) + 1 = 6 := by norm_num
  have v0 : (((0 : Fin 6) : ℕ) : ℝ) = 0 := by norm_num
  have v1 : (((1 : Fin 6) : ℕ) : ℝ) = 1 := by norm_num
  have v2 : (((2 : Fin 6) : ℕ) : ℝ) = 2 := by norm_num
  have v3 : (((3 : Fin 6) : ℕ) : ℝ) = 3 := by norm_num
  have v4 : (((4 : Fin 6) : ℕ) : ℝ) = 4 := by norm_num
  have v5 : (((5 : Fin 6) : ℕ) : ℝ) = 5 := by norm_num
  have c0 : Real.cos (2 * Real.pi * (0 : ℝ) / 6) = 1 := by norm_num
  have c1 : Real.cos (2 * Real.pi * (1 : ℝ) / 6) = 1 / 2 := by
    have h : 2 * Real.pi * (1 : ℝ) / 6 = Real.pi / 3 := by ring
    rw [h, Real.cos_pi_div_three]
  have c2 : Real.cos (2 * Real.pi * (2 : ℝ) / 6) = -(1 / 2) := by
    have h : 2 * Real.pi * (2 : ℝ) / 6 = Real.pi - Real.pi / 3 := by ring
    rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]
  have c3 : Real.cos (2 * Real.pi * (3 : ℝ) / 6) = -1 := by
    have h : 2 * Real.pi * (3 : ℝ) / 6 = Real.pi := by ring
    rw [h, Real.cos_pi]
  have c4 : Real.cos (2 * Real.pi * (4 : ℝ) / 6) = -(1 / 2) := by
    have h : 2 * Real.pi * (4 : ℝ) / 6 = Real.pi + Real.pi / 3 := by ring
    rw [h, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]
    ring
  have c5 : Real.cos (2 * Real.pi * (5 : ℝ) / 6) = 1 / 2 := by
    have h : 2 * Real.pi * (5 : ℝ) / 6 = 2 * Real.pi - Real.pi / 3 := by ring
    rw [h, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi, Real.cos_pi_div_three]
    ring
  rw [hd, v0, v1, v2, v3, v4, v5, c0, c1, c2, c3, c4, c5, h5, h4]
  congr 1 <;> ring

#print axioms sixAvg_of_symmetric

/-- The free-field reference profile at extent six: Wick's square of the exact lattice propagator
sum, `ρ_d = (fsCorr6 d)²`.

DERIVED: every entry is `FreeFieldLagTwoSix.fsCorr6` at that lag, squared — `fsCorr6_zero`,
`fsCorr6_one`, `fsCorr6_two`, `fsCorr6_three` and the circle fold `fsCorr6_fold`, which are
`decide`-checked against the exact rational kernel. `freeRefSix_eq_fsCorr_sq` ties this spelling to
those theorems so the numerals are not a second source. The `2` is Wick's square and `Fin 6` is the
extent-six lag index. -/
noncomputable def freeRefSix (d : Fin 6) : ℝ :=
  if (d : ℕ) = 0 then 933332400 ^ 2
  else if (d : ℕ) = 1 ∨ (d : ℕ) = 5 then 128163984 ^ 2
  else if (d : ℕ) = 2 ∨ (d : ℕ) = 4 then 21150000 ^ 2
  else 7678032 ^ 2

#print axioms freeRefSix

/-- `freeRefSix` is Wick's square of `fsCorr6` at every lag, so the numerals in its definition are
checked against the tree's own exact values.

DERIVED: `0`, `1`, `2`, `3`, `4` and `5` are the six lags of `Fin 6`, and the exponent `2` is Wick's
square. -/
theorem freeRefSix_eq_fsCorr_sq :
    freeRefSix 0 = ((MassGap.FreeFieldLagTwoSix.fsCorr6 0 : ℤ) : ℝ) ^ 2 ∧
    freeRefSix 1 = ((MassGap.FreeFieldLagTwoSix.fsCorr6 1 : ℤ) : ℝ) ^ 2 ∧
    freeRefSix 2 = ((MassGap.FreeFieldLagTwoSix.fsCorr6 2 : ℤ) : ℝ) ^ 2 ∧
    freeRefSix 3 = ((MassGap.FreeFieldLagTwoSix.fsCorr6 3 : ℤ) : ℝ) ^ 2 ∧
    freeRefSix 4 = ((MassGap.FreeFieldLagTwoSix.fsCorr6 4 : ℤ) : ℝ) ^ 2 ∧
    freeRefSix 5 = ((MassGap.FreeFieldLagTwoSix.fsCorr6 5 : ℤ) : ℝ) ^ 2 := by
  have h4 : MassGap.FreeFieldLagTwoSix.fsCorr6 4 = 21150000 :=
    (MassGap.FreeFieldLagTwoSix.fsCorr6_fold).1.trans MassGap.FreeFieldLagTwoSix.fsCorr6_two
  have h5 : MassGap.FreeFieldLagTwoSix.fsCorr6 5 = 128163984 :=
    (MassGap.FreeFieldLagTwoSix.fsCorr6_fold).2.trans MassGap.FreeFieldLagTwoSix.fsCorr6_one
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [freeRefSix, MassGap.FreeFieldLagTwoSix.fsCorr6_zero,
      MassGap.FreeFieldLagTwoSix.fsCorr6_one, MassGap.FreeFieldLagTwoSix.fsCorr6_two,
      MassGap.FreeFieldLagTwoSix.fsCorr6_three, h4, h5]

#print axioms freeRefSix_eq_fsCorr_sq

/-- Every entry of `freeRefSix` is nonnegative, each being a square.

DERIVED: `0 ≤ freeRefSix d` is the conclusion and `Fin 6` the extent-six lag index. -/
theorem freeRefSix_nonneg (d : Fin 6) : 0 ≤ freeRefSix d := by
  fin_cases d <;> norm_num [freeRefSix]

#print axioms freeRefSix_nonneg

/-- The total mass of `freeRefSix` is strictly positive, which is `avg_stable_of_l1_close`'s `hP`.

DERIVED: `0 < ∑ d, freeRefSix d` is the conclusion and the only numeral in the statement. -/
theorem freeRefSix_sum_pos : 0 < ∑ d, freeRefSix d := by
  simp only [Fin.sum_univ_six]
  norm_num [freeRefSix]

#print axioms freeRefSix_sum_pos

/-- The free-field cosine average at extent six, exactly:

    (ρ₀ + ρ₁ − ρ₂ − ρ₃) / (ρ₀ + 2ρ₁ + 2ρ₂ + ρ₃)
      = 887029101009119232 / 904914979654657536
      = 64165878255868 / 65459706282889  =  0.98023474…

The profile shape is `1, 0.018856, 0.000514, 0.0000677`; the lag-one value `0.018856` is the number
`NonnegArm`'s positive control settles on.

DERIVED: `887029101009119232 / 904914979654657536` is the unreduced quotient `sixAvg_of_symmetric`
produces from `freeRefSix`, whose entries `freeRefSix_eq_fsCorr_sq` ties to
`FreeFieldLagTwoSix.fsCorr6`; `0` is the base coupling `readEven ConfinesZero.ap6 0` the angles are
read at. Nothing is chosen. -/
theorem freeRefSix_avg_eq :
    (∑ d, freeRefSix d * Real.cos ((readEven ConfinesZero.ap6 0).θ d)) / (∑ d, freeRefSix d)
      = (887029101009119232 : ℝ) / 904914979654657536 := by
  rw [sixAvg_of_symmetric freeRefSix (by norm_num [freeRefSix]) (by norm_num [freeRefSix])]
  norm_num [freeRefSix]

#print axioms freeRefSix_avg_eq

/-- The free-field average clears the entropy floor by more than `0.22`.

CHOSEN: `0.22` is rounded down, away from the claim that this much margin is available. The exact
margin is `0.98023474… − 0.75983568… = 0.22039905…`, and `LagTwoBound.floor_bounds` brackets the
floor `3 ^ (-(1 : ℝ) / 4)` above by `0.759836`. `0` is also the base coupling the angles are read
at. -/
theorem freeRefSix_clears_floor :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) + 0.22
      < (∑ d, freeRefSix d * Real.cos ((readEven ConfinesZero.ap6 0).θ d))
        / (∑ d, freeRefSix d) := by
  rw [freeRefSix_avg_eq]
  have h := MassGap.LagTwoBound.floor_bounds
  have hq : (0.979836 : ℝ) < (887029101009119232 : ℝ) / 904914979654657536 := by norm_num
  linarith [h.2]

#print axioms freeRefSix_clears_floor

/-- The far arm in the same shape as the middle: the criterion at any coupling whose profile stays
within `9.9%` in `L¹` of the free-field reference.

With the near arm (`confines_at_of_l1_control_from_zero`, `10.72%` of the contact value) this states
B5 as one condition: the Wilson profile stays close, in `L¹` relative to total mass, to an explicitly
known reference at every coupling — a point mass near zero coupling, the exact free-field profile far
out, and certified grid values between. `confines_of_l1_close_to_either_end` assembles the two ends.

CHOSEN: `0.099` and `0.22` are rounded down. `2ε/(1−ε) ≤ 0.22` needs `ε ≤ 0.0990990…`, so `0.099` is
admissible and `0.0992` is not — `0.0992` gives `0.2202486`, above the certified margin `0.22`,
though under the exact margin `0.2203990`, so the two roundings are not interchangeable. `5` is the
aperture of the extent-six torus, `3 ^ (-(1 : ℝ) / 4)` is the floor, and `0` is the coupling clamp
`max β 0`.

Against the Gaussian remainder the comparison runs the other way:
`FreeFieldLagTwoSix.epsMaxSix = 24/25` lets that be `96%` wrong, the lag-two route reading one ratio
with `65.6×` of room rather than the whole profile against an absolute margin of `0.22`. Against an
`L¹` hypothesis `cosAvgEven` admits `0.099` where lag two admits about `0.031`, so which reduction is
the more tolerant depends on the shape of the hypothesis available. -/
theorem confines_at_of_l1_close_to_free_field_six (β : ℝ)
    (hl1 : ∑ d, |MassGap.wilsonCorrAt 5 (max β 0) d - freeRefSix d|
      ≤ 0.099 * ∑ d, freeRefSix d) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven ConfinesZero.ap6 β :=
  confines_at_of_l1_close_to_reference ConfinesZero.ap6 β freeRefSix 0.099 0.22
    freeRefSix_nonneg freeRefSix_sum_pos (by norm_num) (by norm_num) (by norm_num)
    freeRefSix_clears_floor hl1

#print axioms confines_at_of_l1_close_to_free_field_six

/-! ## 9. Contact dominance: the criterion from the contact share alone -/

/-- The lag angle, unfolded at an arbitrary even aperture. `Moment.Read.θ` discards its read, so
this holds by `rfl`.

DERIVED: `2 * Real.pi * d / (a.1 + 1)` is the lag angle `Moment.Read.θ` defines, the `1` being the
lag arity's offset; `0` is the base coupling at which the angles are read. -/
theorem theta_eq (a : EvenAp) (d : Fin (a.1 + 1)) :
    (readEven a 0).θ d = 2 * Real.pi * ((d : ℕ) : ℝ) / (((a.1 : ℕ) : ℝ) + 1) := rfl

#print axioms theta_eq

/-- The contact lag sits at angle zero, so its cosine is one. It is the only lag whose weight is
known without computing a cosine, which is what makes `cosAvgEven_ge_contact` hold at every even
aperture.

DERIVED: `0` is the contact lag and the base coupling; `1` is `Real.cos 0`. -/
theorem cos_theta_zero (a : EvenAp) :
    Real.cos ((readEven a 0).θ (0 : Fin (a.1 + 1))) = 1 := by
  rw [theta_eq a 0]
  norm_num

#print axioms cos_theta_zero

/-- The cosine average is at least `(2ρ₀ − S)/S`, where `ρ₀` is the contact value and `S` the total
mass. Every lag contributes at least `−ρ_d` and the contact lag contributes `+ρ₀`, so the numerator
is at least `ρ₀ − (S − ρ₀)`. No shape fact, log-convexity, lag structure or extent enters — only
`|cos| ≤ 1`, `cos 0 = 1` and the nonnegativity half of reflection positivity.

The proof is that `d ↦ ρ_d(1 + cos θ_d)` is nonnegative termwise, so the sum is at least its contact
term `2ρ₀`, and that sum is `S + ∑ ρ_d cos θ_d`.

DERIVED: the `2` is the contact lag's own weight `1 + cos 0`, and `0` is the contact lag and the
coupling clamp `max β 0`. -/
theorem cosAvgEven_ge_contact (a : EvenAp) (β : ℝ) :
    (2 * MassGap.wilsonCorrAt a.1 (max β 0) 0
        - ∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d)
      / (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d)
      ≤ cosAvgEven a β := by
  have hrp := MassGap.wilson_reflection_positive_at_even a.1 a.2.choose a.2.choose_spec.1
    a.2.choose_spec.2 (le_max_right β 0)
  have hS := hrp.2
  have hterm : ∀ d : Fin (a.1 + 1), 0 ≤ MassGap.wilsonCorrAt a.1 (max β 0) d
      * (1 + Real.cos ((readEven a 0).θ d)) := by
    intro d
    refine mul_nonneg (hrp.1 d) ?_
    have := (abs_le.mp (Real.abs_cos_le_one ((readEven a 0).θ d))).1
    linarith
  have hsingle := Finset.single_le_sum
    (f := fun d : Fin (a.1 + 1) => MassGap.wilsonCorrAt a.1 (max β 0) d
      * (1 + Real.cos ((readEven a 0).θ d)))
    (fun d _ => hterm d) (Finset.mem_univ (0 : Fin (a.1 + 1)))
  have hsplit : (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d
        * (1 + Real.cos ((readEven a 0).θ d)))
      = (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d)
        + ∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d * Real.cos ((readEven a 0).θ d) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun d _ => by ring)
  rw [cos_theta_zero a, hsplit] at hsingle
  rw [cosAvgEven_raw a β, div_le_div_iff₀ hS hS]
  nlinarith [hsingle, hS]

#print axioms cosAvgEven_ge_contact

/-- The criterion from contact dominance alone:

    (1 + c) · S  <  2 · ρ₀        ⟹        c < cosAvgEven a β

at every even aperture, where `c = 3^{-1/4}`, `ρ₀` is the contact value and `S` the total mass.

Equivalently the off-contact mass is under `(1−c)/(1+c)` of the contact value, or the off-contact
share of the total is under `(1−c)/2`. No lag structure is used, so this applies at apertures for
which the tree states no other criterion.

DERIVED: `2` is the contact lag's own weight `1 + cos 0`; `3 ^ (-(1 : ℝ) / 4)` is `ApertureRoute`'s
floor, `e^{-κ₀}` at `κ₀ = ¼log3`; and `0` is the contact lag and the coupling clamp `max β 0`. -/
theorem confines_at_of_contact_dominance (a : EvenAp) (β : ℝ)
    (h : (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d)
      < 2 * MassGap.wilsonCorrAt a.1 (max β 0) 0) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β := by
  have hrp := MassGap.wilson_reflection_positive_at_even a.1 a.2.choose a.2.choose_spec.1
    a.2.choose_spec.2 (le_max_right β 0)
  have hS := hrp.2
  have hge := cosAvgEven_ge_contact a β
  have hlt : (3 : ℝ) ^ (-(1 : ℝ) / 4)
      < (2 * MassGap.wilsonCorrAt a.1 (max β 0) 0
          - ∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d)
        / (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d) := by
    rw [lt_div_iff₀ hS]
    linarith
  linarith

#print axioms confines_at_of_contact_dominance

/-- The contact threshold squared is `LagTwoBound.lagTwoThreshold`, by `rfl`. The off-contact to
contact ratio this file admits is `(1−c)/(1+c)` and `lagTwoThreshold` is its square, because the
lag-two route substitutes `ρ(1) ≤ √(ρ(0)ρ(2))` and then works in `v = √(ρ(2)/ρ(0))`, where the
admissible root is `(1−c)/(1+c)`. Contact dominance works in the mass directly.

DERIVED: `3 ^ (-(1 : ℝ) / 4)` is the floor `c`, the `1`s are the numerator and denominator offsets of
`(1−c)/(1+c)`, and the exponent `2` is the square `lagTwoThreshold` carries. -/
theorem contact_threshold_sq_eq_lagTwoThreshold :
    ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4))) ^ 2
      = MassGap.LagTwoBound.lagTwoThreshold := rfl

#print axioms contact_threshold_sq_eq_lagTwoThreshold

/-- The numeric form of contact dominance: an off-contact share under `12%` of the total mass
suffices, at every even aperture.

CHOSEN: `0.12` is rounded down, away from the claim that this share is sufficient. The exact
threshold is `(1−c)/2 = 0.12008215…`, and `LagTwoBound.floor_bounds` brackets the floor
`3 ^ (-(1 : ℝ) / 4)` above by `0.759836`. Equivalently the contact value carries at least `88%` of
the mass. `0` is the contact lag and the coupling clamp `max β 0`, and the `1` is the lag arity's
offset in `Fin (a.1 + 1)`.

Against the other routes: for the free-field profile at extent six the off-contact share is
`0.038808/1.038808 = 0.037357`, a margin of `3.2×`, against `65.6×` for the lag-two route at the same
extent. Contact dominance holds at every even aperture with no shape facts, no lag structure and no
extent-specific criterion, and it is a single scalar to certify rather than a profile. -/
theorem confines_at_of_off_contact_share_small (a : EvenAp) (β : ℝ)
    (h : (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d)
        - MassGap.wilsonCorrAt a.1 (max β 0) 0
      < 0.12 * ∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β := by
  have hrp := MassGap.wilson_reflection_positive_at_even a.1 a.2.choose a.2.choose_spec.1
    a.2.choose_spec.2 (le_max_right β 0)
  have hS := hrp.2
  have hc := MassGap.LagTwoBound.floor_bounds
  refine confines_at_of_contact_dominance a β ?_
  have hgap : (0 : ℝ) < (0.76 - (3 : ℝ) ^ (-(1 : ℝ) / 4))
      * (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d) :=
    mul_pos (by linarith [hc.2]) hS
  nlinarith [h, hgap]

#print axioms confines_at_of_off_contact_share_small

/-! ## 10. Where the gauge group enters

C3 reads "any compact simple gauge group `G`" and the tree's row says `SU(3)`. Two different threes
appear, and only one is the colour count.

The floor's three is geometric. `Floor.directed_paths_card` counts directed cube-paths: the origin
cube followed by `k` steps, each a choice in `{+x, +y, +z}`, so `Fintype.card (Fin k → Fin 3)`. That
is a lattice-geometry fact in four dimensions and mentions no gauge group. `κ₀ = ¼ log 3` is its
density and `3^{-1/4} = e^{-κ₀}` is the floor, so the bar the criterion clears is the same for every
gauge group.

The colour count enters in the correlation: `WilsonBridge.corrClay` is
`corrHyper (d := 4) 3 n 0 1 2`, and that three is `Nc`. `corrHyper` takes `Nc` as a parameter, so
the generic object exists and `corrClay` is its `Nc = 3` instance.

The statements below are the ones above with the floor as a variable rather than `3^{-1/4}`, and
their proofs are unchanged, none of them having used the floor's value. Carrying `Nc` through the
correlation and its reflection positivity is a separate matter from the bar.

DERIVED: `c` is a variable standing for the floor; `0 < c` and `c < 1` are what
`ConfinesZero.floor_pos` and `floor_lt_one` prove of the actual one, carried as hypotheses so the
statements do not name it.
-/

/-- The base of the floor is the directed-step count rather than the colour count.
`Floor.directed_paths_card` counts maps `Fin k → Fin 3`, the `k` steps of a directed cube-path each
choosing from `{+x, +y, +z}`. This records that the `3` in `3^{-1/4}` is the cardinality of that
type.

DERIVED: `3` is `Fintype.card (Fin 3)`, the number of forward directions a cube-path step may
take. -/
theorem floor_base_is_directed_step_count :
    (Fintype.card (Fin 3) : ℝ) = 3 := by simp

#print axioms floor_base_is_directed_step_count

/-- Contact dominance at an arbitrary floor: `confines_at_of_contact_dominance` with `c` a variable.
The proof does not use the floor's value.

DERIVED: `2` is the contact lag's own weight `1 + cos 0`, the `1` is the offset in `1 + c`, and `0`
is the contact lag and the coupling clamp `max β 0`. `c` is a variable. -/
theorem confines_at_of_contact_dominance_floor (a : EvenAp) (β c : ℝ)
    (h : (1 + c) * (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d)
      < 2 * MassGap.wilsonCorrAt a.1 (max β 0) 0) :
    c < cosAvgEven a β := by
  have hrp := MassGap.wilson_reflection_positive_at_even a.1 a.2.choose a.2.choose_spec.1
    a.2.choose_spec.2 (le_max_right β 0)
  have hS := hrp.2
  have hge := cosAvgEven_ge_contact a β
  have hlt : c < (2 * MassGap.wilsonCorrAt a.1 (max β 0) 0
          - ∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d)
        / (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d) := by
    rw [lt_div_iff₀ hS]
    linarith
  linarith

#print axioms confines_at_of_contact_dominance_floor

/-- `L¹` stability against a reference at an arbitrary floor: `confines_at_of_l1_close_to_reference`
with `c` a variable. The proof is the same.

DERIVED: `0 ≤ r d`, `0 < ∑ d, r d` and `0 ≤ ε` are sign conditions, `ε < 1` and the `2` in
`2 * ε / (1 - ε)` are `avg_stable_of_l1_close`'s range and quotient-rule factor, and `0` is also the
coupling clamp `max β 0` and the base point `readEven a 0`; the `1` in `Fin (a.1 + 1)` is the lag
arity. `c`, `r`, `ε` and `m` are variables. -/
theorem confines_at_of_l1_close_to_reference_floor (a : EvenAp) (β c : ℝ)
    (r : Fin (a.1 + 1) → ℝ) (ε m : ℝ)
    (hr : ∀ d, 0 ≤ r d) (hrP : 0 < ∑ d, r d)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hmod : 2 * ε / (1 - ε) ≤ m)
    (hval : c + m < (∑ d, r d * Real.cos ((readEven a 0).θ d)) / (∑ d, r d))
    (hl1 : ∑ d, |MassGap.wilsonCorrAt a.1 (max β 0) d - r d| ≤ ε * ∑ d, r d) :
    c < cosAvgEven a β := by
  rw [cosAvgEven_raw a β]
  have h := avg_stable_of_l1_close r
    (fun d => MassGap.wilsonCorrAt a.1 (max β 0) d)
    (fun d => Real.cos ((readEven a 0).θ d)) ε 1
    hr hrP hε0 hε1 hl1 zero_le_one (fun d => Real.abs_cos_le_one _)
  have hlow := (abs_le.mp h).1
  have hmod' : 2 * 1 * ε / (1 - ε) ≤ m := by
    have : 2 * (1 : ℝ) * ε = 2 * ε := by ring
    rw [this]; exact hmod
  linarith

#print axioms confines_at_of_l1_close_to_reference_floor

/-- `confines_at_of_contact_dominance_floor` at `c = 3 ^ (-(1 : ℝ) / 4)` recovers
`confines_at_of_contact_dominance`, so the parametric form loses nothing at the actual floor.

DERIVED: `3 ^ (-(1 : ℝ) / 4)` is the floor, the `1` the offset in `1 + c`, the `2` the contact lag's
weight `1 + cos 0`, and `0` the contact lag and the coupling clamp. -/
theorem contact_dominance_floor_specialises (a : EvenAp) (β : ℝ)
    (h : (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d)
      < 2 * MassGap.wilsonCorrAt a.1 (max β 0) 0) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β :=
  confines_at_of_contact_dominance_floor a β _ h

#print axioms contact_dominance_floor_specialises

/-! ## 11. Where each sufficient condition's hypothesis is met

`mul_control_from_zero_forces_a_point_mass` records a hypothesis in this file that no positive
coupling satisfies. The same check for the rest:

| condition | hypothesis met |
|---|---|
| `confines_at_of_l1_control_from_zero` | `l1_control_from_zero_holds_near_zero` — on a neighbourhood of zero coupling |
| `confines_of_grid_and_far_arm` | `grid_hypotheses_are_met_near_zero` — both hypotheses jointly, on an interval |
| `confines_at_of_off_contact_share_small` | `contact_dominance_holds_at_zero_coupling`, below |
| `confines_at_of_l1_close_to_free_field_six` | no such theorem — see the note after it |

For the last, the Wilson profile being within `9.9%` in `L¹` of the exact free-field profile at large
coupling is the weak-coupling statement itself, so a satisfiability theorem for it would be the far
arm. The reference has positive total mass and the distance to it is a continuous quantity, and
`FreeFieldLagTwoSix.EffectiveGaussianLagTwoSix` is the tree's more tolerant form of the same demand.
-/

/-- Contact dominance holds at zero coupling, so `confines_at_of_off_contact_share_small`'s
hypothesis is met somewhere. At zero coupling the profile is a point mass at the contact lag —
`PowerTail.wilsonCorrAt_at_zero_coupling` kills every lag of nonzero circle distance and
`contact_value_pos_at_zero_coupling` keeps the contact value strictly positive — so the off-contact
mass is exactly `0`, and `0 < 0.12 · ρ₀`.

DERIVED: `0.12` is the constant `confines_at_of_off_contact_share_small` carries, rounded down from
`(1−c)/2`; `0` is the off-contact mass at zero coupling, the contact lag, and the coupling itself. -/
theorem contact_dominance_holds_at_zero_coupling (a : EvenAp) :
    (∑ d, MassGap.wilsonCorrAt a.1 (max (0 : ℝ) 0) d)
        - MassGap.wilsonCorrAt a.1 (max (0 : ℝ) 0) 0
      < 0.12 * ∑ d, MassGap.wilsonCorrAt a.1 (max (0 : ℝ) 0) d := by
  have hz : max (0 : ℝ) 0 = 0 := max_self 0
  rw [hz]
  have hsum : (∑ d, MassGap.wilsonCorrAt a.1 (0 : ℝ) d) = MassGap.wilsonCorrAt a.1 0 0 := by
    refine Finset.sum_eq_single (0 : Fin (a.1 + 1)) (fun d _ hd => ?_) (fun h => ?_)
    · exact MassGap.PowerTail.wilsonCorrAt_at_zero_coupling a.1 d (one_le_circLag hd)
    · exact absurd (Finset.mem_univ (0 : Fin (a.1 + 1))) h
  have hpos : 0 < MassGap.wilsonCorrAt a.1 0 0 :=
    MassGap.PowerTail.contact_value_pos_at_zero_coupling a.1
  rw [hsum]
  linarith

#print axioms contact_dominance_holds_at_zero_coupling

/-- The criterion at zero coupling through the contact-dominance route, which exercises the whole
chain rather than the hypothesis alone. `ConfinesZero.confines_at_zero` reaches the same conclusion
by a different argument, the point mass giving cosine average exactly `1` there.

DERIVED: `3 ^ (-(1 : ℝ) / 4)` is `ApertureRoute`'s floor and `0` is zero coupling. -/
theorem confines_at_zero_via_contact_dominance (a : EvenAp) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a 0 :=
  confines_at_of_off_contact_share_small a 0 (contact_dominance_holds_at_zero_coupling a)

#print axioms confines_at_zero_via_contact_dominance

/-! ## 12. Monotonicity in the coupling, and what the measured data says about it

Every route above splits the coupling axis and pays for the middle with a grid of certified values,
an `L¹` modulus, or both. One hypothesis removes the middle: if the lag-two ratio `ρ(2)/ρ(0)` is
non-decreasing in `β`, then its value anywhere below the cut is at most its value at the cut, which
the far arm bounds. `confines_of_monotone_ratio_six` is that reduction.

The hypothesis is contradicted by the tree's own measured data.
`research/data/9_2_dat_confinement_cos.csv` reads the cosine average across the coupling and it is
not monotone — it falls to an interior minimum and then rises:

    β        0.50   1.00   1.60   2.00   2.20   2.30   2.40   2.50   2.60
    cos_avg  1.0014 0.9981 0.9957 0.9921 0.9867 0.9863 0.9895 0.9905 0.9907
                                                 ^min   ^rises from here

`9_1_dat_d2_bound.csv` reads the profile's circular second moment on the same couplings and agrees
from the other side: it peaks at `β = 2.20` (`0.19211`) and falls to `0.13637` by `2.60`, a drop of
`8.0σ` of the last point's own error. A spread that rises and then falls is a cosine average that
falls and then rises, so the two files are the same fact read twice. The profile re-concentrates
above the crossover, and no functional of it that increases with the spread — the lag-two ratio
included — is monotone in the coupling.

Two limits on how far the data reads. The estimator returns `1.0014` and `1.0006` at the two smallest
couplings, above the analytic maximum of `1`, so its noise is of order `10⁻³` and smaller
differences are not differences. And the interior minimum sits at `0.9863` against the floor
`0.759836`, a margin of `+0.2265` where the total available margin is `0.2402`, so at the tightest
coupling it measures the criterion spends about `6%` of its room; that is where a grid would have to
be finest.

The tree carries no `β`-monotonicity of the correlation and no correlation inequality — `Griffiths`,
`Ginibre` and `FKG` occur in no module. The positivity it does carry is a different statement:
`CharacterExpansion.wilson_kernel_nonneg` says `∑ᵢⱼ zᵢzⱼ e^{β⟨Aᵢ,Aⱼ⟩} ≥ 0`, positive-definiteness in
the configuration variables at fixed `β`, while monotonicity would need `Cov(O, S) ≥ 0`, about the
`β`-derivative of an expectation.

The reduction below is kept because it says what the middle interval costs, namely what monotonicity
would have removed.

DERIVED: `5` is the aperture — `wilsonCorrAt 5` is the extent-six torus — and `2` and `0` are the
lags the ratio relates. `B` and `K` are variables.
-/

/-- Monotonicity of the lag-two ratio plus the far arm gives `ConfinesAtAnAperture` at extent six,
with no middle interval.

The monotonicity hypothesis is cross-multiplied, so no division and no positivity of the denominator
enters it: `ρ(2,β₁)·ρ(0,β₂) ≤ ρ(2,β₂)·ρ(0,β₁)` says `ρ(2)/ρ(0)` is non-decreasing, stated where both
sides are defined regardless. Below the cut the ratio is at most its value at the cut; at and above
the cut the far arm bounds it. So the bound holds at every nonnegative coupling, which is
`LagTwoRatioSix`.

Scope: the measured data in the section note above contradicts `hmono`.

DERIVED: `5` is the aperture of the extent-six torus, `2` and `0` are the lags the ratio relates,
and `0 ≤ B` and `0 ≤ β₁` are sign conditions. `K` and `B` are variables. -/
theorem confines_of_monotone_ratio_six {K B : ℝ} (hB : 0 ≤ B)
    (hK : K < MassGap.LagTwoSix.lagTwoThresholdSix)
    (hmono : ∀ β₁ β₂ : ℝ, 0 ≤ β₁ → β₁ ≤ β₂ →
      MassGap.wilsonCorrAt 5 β₁ 2 * MassGap.wilsonCorrAt 5 β₂ 0
        ≤ MassGap.wilsonCorrAt 5 β₂ 2 * MassGap.wilsonCorrAt 5 β₁ 0)
    (hfar : ∀ β : ℝ, B ≤ β →
      MassGap.wilsonCorrAt 5 β 2 ≤ K * MassGap.wilsonCorrAt 5 β 0) :
    ApertureRoute.ConfinesAtAnAperture := by
  refine MassGap.LagTwoSix.confines_of_lagTwoRatioSix ⟨K, hK, fun β hβ => ?_⟩
  rcases le_total B β with hge | hle
  · exact hfar β hge
  · -- below the cut: push the ratio up to the cut, where the far arm already bounds it
    have hcut := hfar B le_rfl
    have hmo := hmono β B hβ hle
    have h0B : 0 < MassGap.wilsonCorrAt 5 B 0 :=
      MassGap.PlaqVariance.corrClay_zero_pos 5 B
    have h0b : 0 < MassGap.wilsonCorrAt 5 β 0 :=
      MassGap.PlaqVariance.corrClay_zero_pos 5 β
    have hstep : MassGap.wilsonCorrAt 5 B 2 * MassGap.wilsonCorrAt 5 β 0
        ≤ (K * MassGap.wilsonCorrAt 5 B 0) * MassGap.wilsonCorrAt 5 β 0 :=
      mul_le_mul_of_nonneg_right hcut (le_of_lt h0b)
    have hchain : MassGap.wilsonCorrAt 5 β 2 * MassGap.wilsonCorrAt 5 B 0
        ≤ (K * MassGap.wilsonCorrAt 5 β 0) * MassGap.wilsonCorrAt 5 B 0 := by
      calc MassGap.wilsonCorrAt 5 β 2 * MassGap.wilsonCorrAt 5 B 0
          ≤ MassGap.wilsonCorrAt 5 B 2 * MassGap.wilsonCorrAt 5 β 0 := hmo
        _ ≤ (K * MassGap.wilsonCorrAt 5 B 0) * MassGap.wilsonCorrAt 5 β 0 := hstep
        _ = (K * MassGap.wilsonCorrAt 5 β 0) * MassGap.wilsonCorrAt 5 B 0 := by ring
    exact le_of_mul_le_mul_right hchain h0B

#print axioms confines_of_monotone_ratio_six

/-- `ApertureRoute.FlagshipAt` applied to `confines_of_monotone_ratio_six`, so what monotonicity
would convert the far arm into is visible end to end. The content is the `ConfinesAtAnAperture`
argument; see the header.

DERIVED: the numerals are `confines_of_monotone_ratio_six`'s own — `5` the aperture of the
extent-six torus, `2` and `0` the lags the ratio relates, and `0 ≤ B` a sign condition. -/
theorem flagship_of_monotone_ratio_six {K B : ℝ} (hB : 0 ≤ B)
    (hK : K < MassGap.LagTwoSix.lagTwoThresholdSix)
    (hmono : ∀ β₁ β₂ : ℝ, 0 ≤ β₁ → β₁ ≤ β₂ →
      MassGap.wilsonCorrAt 5 β₁ 2 * MassGap.wilsonCorrAt 5 β₂ 0
        ≤ MassGap.wilsonCorrAt 5 β₂ 2 * MassGap.wilsonCorrAt 5 β₁ 0)
    (hfar : ∀ β : ℝ, B ≤ β →
      MassGap.wilsonCorrAt 5 β 2 ≤ K * MassGap.wilsonCorrAt 5 β 0) :
    ApertureRoute.FlagshipAt (confines_of_monotone_ratio_six hB hK hmono hfar) :=
  ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_monotone_ratio_six

/-! ## 13. The two computed ends, and the disjunction they give

Two couplings have their cosine average known exactly rather than measured:

* zero coupling — `ConfinesZero.cosAvgEven_at_zero` gives exactly `1`, the profile being a point mass
  at the contact lag. Margin over the floor: `1 − 0.7598357 = 0.2401643`.
* the free-field limit — `freeRefSix_avg_eq` gives exactly
  `887029101009119232/904914979654657536 = 0.9802347`. Margin: `0.2203991`.

The two margins differ by `0.0198`, the smaller belonging to the free field, so the criterion is
tighter at the weak-coupling end. Each end spends under a tenth of the room between `1` and the
floor.

For the criterion to fail at some coupling, the cosine average there must fall below the floor — a
drop of at least `0.2204` from the free-field value and `0.2402` from the zero-coupling value. By
`avg_stable_of_l1_close` a drop of `m` needs the profile to move by `ε` in `L¹` with
`2ε/(1−ε) ≥ m`, so a drop of `0.22` needs `ε ≥ 0.0991`. A failure therefore requires the profile to
sit more than `9.9%` away, in `L¹` relative to total mass, from both computed ends at once.

`confines_of_l1_close_to_either_end` is the contrapositive: staying near either end at each coupling,
not necessarily the same end at different couplings, suffices.

DERIVED: `0.1072` and `0.099` are the two admissible `ε`, each rounded down from `m/(2+m)` at its own
end's certified margin, as in `confines_at_of_l1_control_from_zero` and
`confines_at_of_l1_close_to_free_field_six`. Nothing new is chosen here.
-/

/-- `ConfinesAtAnAperture` at extent six if the profile stays near either computed end, taken per
coupling.

The disjunction is per coupling: a profile may be near the point mass for small `β` and near the free
field for large `β`, and need not be near both at once. It may not, at any coupling, be more than
`10.72%` in `L¹` from the zero-coupling profile and more than `9.9%` from the free-field one.

This puts the arms of §5 and §8 together with no middle interval.

DERIVED: `5` is the aperture of the extent-six torus; `0` is zero coupling, the clamp `max β 0`, and
the leading digit of the two constants `0.1072` and `0.099`, which are
`confines_at_of_l1_control_from_zero`'s and `confines_at_of_l1_close_to_free_field_six`'s, carried
unchanged. -/
theorem confines_of_l1_close_to_either_end
    (hcover : ∀ β : ℝ, 0 ≤ β →
      (∑ d, |MassGap.wilsonCorrAt 5 (max β 0) d
          - MassGap.wilsonCorrAt 5 (max (0 : ℝ) 0) d|
        ≤ 0.1072 * ∑ d, MassGap.wilsonCorrAt 5 (max (0 : ℝ) 0) d)
      ∨ (∑ d, |MassGap.wilsonCorrAt 5 (max β 0) d - freeRefSix d|
        ≤ 0.099 * ∑ d, freeRefSix d)) :
    ApertureRoute.ConfinesAtAnAperture := by
  refine ⟨ConfinesZero.ap6, fun β => ?_⟩
  rcases le_total β 0 with hle | hnn
  · rw [cosAvgEven_eq_one_of_nonpos _ hle]
    exact floor_lt_one
  · rcases hcover β hnn with hnear | hfar
    · exact confines_at_of_l1_control_from_zero ConfinesZero.ap6 β hnear
    · exact confines_at_of_l1_close_to_free_field_six β hfar

#print axioms confines_of_l1_close_to_either_end

/-- `ApertureRoute.FlagshipAt` applied to `confines_of_l1_close_to_either_end`. The content is the
`ConfinesAtAnAperture` argument; see the header.

DERIVED: the numerals are `confines_of_l1_close_to_either_end`'s own — `5` the aperture of the
extent-six torus, and `0` zero coupling, the clamp, and the leading digit of `0.1072` and
`0.099`. -/
theorem flagship_of_l1_close_to_either_end
    (hcover : ∀ β : ℝ, 0 ≤ β →
      (∑ d, |MassGap.wilsonCorrAt 5 (max β 0) d
          - MassGap.wilsonCorrAt 5 (max (0 : ℝ) 0) d|
        ≤ 0.1072 * ∑ d, MassGap.wilsonCorrAt 5 (max (0 : ℝ) 0) d)
      ∨ (∑ d, |MassGap.wilsonCorrAt 5 (max β 0) d - freeRefSix d|
        ≤ 0.099 * ∑ d, freeRefSix d)) :
    ApertureRoute.FlagshipAt (confines_of_l1_close_to_either_end hcover) :=
  ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_l1_close_to_either_end

/-- The free-field end has the smaller margin over the floor, by `0.0198`. Both values are proved
rather than measured: `1` at zero coupling (`ConfinesZero.cosAvgEven_at_zero`) and
`887029101009119232/904914979654657536` in the free-field limit (`freeRefSix_avg_eq`).

DERIVED: `887029101009119232 / 904914979654657536` is `freeRefSix_avg_eq`'s value, carried unchanged;
`3 ^ (-(1 : ℝ) / 4)` is the floor, subtracted on both sides; and the other `1` is the zero-coupling
cosine average. -/
theorem free_field_end_is_tighter :
    (887029101009119232 : ℝ) / 904914979654657536 - (3 : ℝ) ^ (-(1 : ℝ) / 4)
      < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
  have h : (887029101009119232 : ℝ) / 904914979654657536 < 1 := by norm_num
  linarith

#print axioms free_field_end_is_tighter

/-! ## 14. The free-field value as an infimum

The hypothesis named below is that the free-field limit is the infimum of `cosAvgEven ap6` over the
whole nonnegative half-line, not merely its endpoint. It gives `ConfinesAtAnAperture` immediately,
because that value clears the floor by `0.2204` (`freeRefSix_clears_floor`), with no grid, no modulus
and no interior values.

What the measured files do and do not say about it. `9_2_dat_confinement_cos.csv` bottoms at `0.9863`
at `β = 2.30`. That file is SU(2) at `L = 16` — `ym_crossover_confinement_of_grid.py` hard-codes
`L = 16` and `ym_confinement_of_cos_average.py` takes `L = CG.L` — and it is the all-component
whitened density read. `freeRefSix_avg_eq`'s `0.9802347` is the extent-six, single-channel free-field
value of `corrClay`. The two differ in extent and in channel, and `free_field_lag_two_ratio.py` warns
against reading one extent's free-field number against another extent's obligation.

Matched at each row's own extent the comparison runs the other way. Against
`8_6_dat_free_field_muinf.csv`'s `λ₁/λ₀` at the row's own `L`, 23 of the 43 rows of
`9_3_dat_substrate_of_aperture.csv` have the measured cosine average below its own extent's
free-field value — the `L = 16` minimum by `0.0052` — and every `SU(3)` row is below.
`8_6_dat_free_field_measured.csv`'s `mu_over_muinf` column exceeds `1` in 20 of 28 rows, as
`PAPER.md` §8.6 reports.

Those rows are a different object from `cosAvgEven ap6`: an all-component whitened density on
`L³×2L`, not single-channel `corrClay` on `L⁴`. No `SU(3)` `L⁴`-symmetric ensemble is in the store,
so the matching measurement has not been taken, and the analogous statement for the multi-channel
read is false on the rows above.

Measuring the matching object needs `cosAvgEven` on a single-channel `SU(3)` `L⁴` ensemble at extent
six. The store (`d:\data\entroptics-lattice`) holds `SU(3)` only as `L³×2L`; the script that
generates the right geometry is `lag_two_ratio_refutation_probe.py`, which builds `6⁴`
configurations itself, and extending it to report `cosAvgEven` would decide the hypothesis.

Against §12's monotonicity hypothesis, which the measured spread contradicts, this one says only
that the curve may never sink below where it ends.

DERIVED: the numerator and denominator are `freeRefSix_avg_eq`'s, carried unchanged; no new numeral.
-/

/-- The free-field value is a lower bound for `cosAvgEven ConfinesZero.ap6` at every nonnegative
coupling. Named as a `Prop` so the hypothesis is one line, as `MonomialsSeparateFinitely` is.

DERIVED: `887029101009119232/904914979654657536` is `freeRefSix_avg_eq`'s value, carried unchanged
and not retyped — that theorem computes it from `freeRefSix`, whose entries `freeRefSix_eq_fsCorr_sq`
ties to `FreeFieldLagTwoSix.fsCorr6`. `0` is the bottom of the coupling range, and `2` is the lag
`cosAvgEven`'s aperture `ap6` carries. No magnitude is chosen here. -/
def FreeFieldIsTheInfimum : Prop :=
  ∀ β : ℝ, 0 ≤ β →
    (887029101009119232 : ℝ) / 904914979654657536 ≤ cosAvgEven ConfinesZero.ap6 β

#print axioms FreeFieldIsTheInfimum

/-- `FreeFieldIsTheInfimum` gives `ConfinesAtAnAperture` at extent six. The free-field value clears
the floor by `0.2204`, so a curve that never sinks below it never reaches the floor, and the
negative half-line is handled by the `readEven` clamp. -/
theorem confines_of_free_field_infimum (h : FreeFieldIsTheInfimum) :
    ApertureRoute.ConfinesAtAnAperture := by
  refine ⟨ConfinesZero.ap6, fun β => ?_⟩
  rcases le_total β 0 with hle | hnn
  · rw [cosAvgEven_eq_one_of_nonpos _ hle]
    exact floor_lt_one
  · have hge := h β hnn
    have hc := MassGap.LagTwoBound.floor_bounds
    have hq : (0.979836 : ℝ) < (887029101009119232 : ℝ) / 904914979654657536 := by norm_num
    linarith [hc.2]

#print axioms confines_of_free_field_infimum

/-- `ApertureRoute.FlagshipAt` applied to `confines_of_free_field_infimum`. The content is the
`ConfinesAtAnAperture` argument; see the header. -/
theorem flagship_of_free_field_infimum (h : FreeFieldIsTheInfimum) :
    ApertureRoute.FlagshipAt (confines_of_free_field_infimum h) :=
  ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_free_field_infimum

/-- `FreeFieldIsTheInfimum`'s inequality holds at zero coupling, where
`ConfinesZero.cosAvgEven_at_zero` puts the average at exactly `1`. It is the one coupling at which
the hypothesis is settled.

DERIVED: `887029101009119232 / 904914979654657536` is `freeRefSix_avg_eq`'s value, carried unchanged,
and `0` is zero coupling. -/
theorem freeFieldIsTheInfimum_at_zero :
    (887029101009119232 : ℝ) / 904914979654657536 ≤ cosAvgEven ConfinesZero.ap6 0 := by
  rw [cosAvgEven_at_zero]
  norm_num

#print axioms freeFieldIsTheInfimum_at_zero

end MassGap.CosAvgStability
