import Mathlib
import MassGap.FlatProfileAllApertures
import MassGap.LagTwoBound
import MassGap.LagTwoSix
import MassGap.FreeFieldLagTwoSix

/-!
# MassGap.CosAvgStability — the criterion is volume-free under MULTIPLICATIVE control

`CompactBeta` closes the finite-grid route on the substrate side, and its two blockers are exact:

1. `clay_covariance_constant_not_aperture_uniform` — the only unconditional Lipschitz constant is
   EXTENSIVE. `cov_bound_extensive` gives `|Cov(O,S)| ≤ 4M·#Plaq`, and at the Clay reads the
   aperture IS the extent, so `#Plaq = 16(N+1)⁴`. Evaluated, that is `L = 8192` at extent four and
   `93312` at extent six, hence `1.2e7` and `1.4e8` grid points over `β ∈ [0,3]`.
2. `profile_to_moment_not_uniformly_lipschitz` — normalising does not save it. An ADDITIVE sup-norm
   perturbation `t` in the raw profile moves `d2At` by `t/(1+t)·((N+1)/2)²`.

**Both are statements about an ADDITIVE perturbation, and blocker 2 is a statement about `d2At`.**
This file records what happens to `cosAvgEven` — the quantity `ApertureRoute` actually reads — under
a MULTIPLICATIVE one, and the answer is different in kind: the modulus is `2(K-1)/(2-K)`, with **no
aperture, no extent and no volume in it at all**.

## Why the two differ, stated so it is not mistaken for a trick

`d2At` weights lag `d` by `circLag d ^ 2`, which is UNBOUNDED and grows with the extent — that is
what supplies the `((N+1)/2)²` in blocker 2. `cosAvgEven` weights it by `cos θ_d`, which lies in
`[-1, 1]` at every aperture. `avg_stable_of_mul_close` isolates exactly this: the modulus is
proportional to the weight's sup-norm `W`, so a bounded weight gives a bounded modulus, and the two
criteria are not interchangeable for this purpose.

The multiplicative hypothesis is the natural one for a correlator, and it is the natural one for
this problem specifically: `WilsonAnalytic.expect_hasDerivAt` gives `d⟨O⟩/dβ = -Cov(O,S)`, so
multiplicative control over a step is a bound on the LOGARITHMIC derivative `|d log ρ_d/dβ|`, while
`cov_bound_extensive` is a bound on the ABSOLUTE one. Blocker 1 is the statement that the absolute
bound is extensive. It says nothing about the relative bound.

## What this does and does not do

It **does** replace, on the criterion side, "a modulus of continuity in `β` uniform in `N`" by a
quantity with no `N` in it. `confines_at_of_grid_point_and_mul_control` is the usable form: one grid
point clearing the floor by a margin `m`, plus multiplicative control `K` with
`2(K-1)/(2-K) ≤ m`, gives the criterion at every coupling the control reaches. At the margin the
point mass at zero coupling supplies — `cosAvgEven a 0 = 1`, so `m = 1 - 3^{-1/4} = 0.2401` — the
admissible `K` is `(2+2m)/(2+m) = 1.1072`, so the profile may move by `10.7%` multiplicatively and
the criterion survives. Both are rounded AWAY from the claim: `1.1073` would put the modulus at
`0.240394` against a margin of `0.2401643` and violate the very inequality it is quoted under.

It does **not** close the middle interval. The remaining input is a bound on `|d log ρ_d/dβ|`
uniform in the lag and the volume, which is a dynamical estimate and is not in the tree. What has
changed is which estimate is being asked for: an ABSOLUTE Lipschitz bound is proved extensive and
therefore useless here, and a RELATIVE one is not — `CompactBeta` rules out the first and is silent
on the second.

DERIVED: no numeral here is a magnitude. `1` and `2` in `1 ≤ K` and `K < 2` are the identity
perturbation and the point where the denominator `2 - K` of the modulus vanishes — the latter is
forced by the algebra (`(K-1)·P` must stay under the total mass `P` for the perturbed denominator to
remain positive), not chosen. The `2` in the numerator is the two terms of the quotient rule. `0` is
the contact lag and the positivity of the total mass. The floor `3 ^ (-(1:ℝ)/4)` is
`ApertureRoute`'s own constant, carried through unchanged.
## ⚠ WHAT THE FLAGSHIP IS WORTH

`MassGap.FlagshipScope` — the tree's own adversarial audit, deliberately not imported — measures
`ApertureRoute.flagship_of_confinement_at_an_aperture`. `flagship_for_bogus` proves the WHOLE
conclusion (gap, non-triviality, `SO(4)`, OS0–OS3) for an object with **no read, no correlation, no
gauge group and no lattice in it**, tension the constant `0`; and `gap_summand_is_manufactured` shows
the gap clause's "correlation" is a one-mode sequence whose magnitude is DEFINED as its own bound.

**So the content sits at `ConfinesAtAnAperture`** — a statement about `cosAvgEven` of `readEven`,
hence about the genuine `wilsonCorrAt` at an even aperture ≥ 4 — and the `FlagshipAt` step is
packaging. Every `flagship_…` below should be read that way.

-/

namespace MassGap.CosAvgStability

open MassGap MassGap.EvenAperture MassGap.ApertureRoute MassGap.ConfinesZero

/-! ## 1. The abstract inequality -/

/-- **A WEIGHTED AVERAGE IS STABLE UNDER MULTIPLICATIVE PERTURBATION, WITH NO VOLUME FACTOR.**

If `σ` and `ρ` agree to within a multiplicative `K` at every index, the weighted averages
`(∑ σ·w)/(∑ σ)` and `(∑ ρ·w)/(∑ ρ)` differ by at most `2W(K-1)/(2-K)`, where `W` bounds `|w|`.

The index type is `Fin n` and `n` does not appear in the conclusion. That is the whole point: the
bound is proportional to the weight's sup-norm and to the perturbation, and to nothing else.

DERIVED: `1 ≤ K` is the identity perturbation, `K < 2` is where the perturbed total mass could
vanish, and the `2` in the numerator counts the two terms the quotient rule produces. -/
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

/-- The cosine average in raw profile terms, with the weight separated from the coupling. The same
identity `ConfinesZero.continuous_cosAvgEven` establishes inside its own proof; named here so it can
be applied. -/
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

/-- **THE CRITERION MOVES BY AT MOST `2(K-1)/(2-K)` WHEN THE PROFILE MOVES BY `K`.**

No aperture, no extent, no volume. This is `avg_stable_of_mul_close` at `W = 1`, and `W = 1` is
available because the criterion's weight is a cosine.

The positivity of the total mass comes from `wilson_reflection_positive_at_even`, the PROVED
theorem, so this does not consume the named axiom. -/
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

/-- **ONE GRID POINT PLUS MULTIPLICATIVE CONTROL GIVES THE CRITERION.**

This is the usable form. If the cosine average clears the entropy floor by a margin `m` at one
coupling, and the profile at a second coupling is within a multiplicative `K` of the first with
`2(K-1)/(2-K) ≤ m`, then the criterion holds at the second coupling too.

Applied at `β₁ = 0`, where `ConfinesZero.cosAvgEven_at_zero` gives the value exactly `1`, the margin
is `m = 1 - 3^{-1/4} = 0.2401` and the admissible `K` is `(2+2m)/(2+m) = 1.1072` — so the profile
may move by `10.7%` multiplicatively and the criterion survives. What is missing is a theorem that
it moves by no more than that, which is a bound on `|d log ρ_d/dβ|` and is not in the tree. -/
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

/-! ## 3. The route is not circular, and that is the point -/

/-- **MULTIPLICATIVE CONTROL IS NOT THE MASS GAP.**

This is the check the two closed routes fail, and it is why they are closed:

* the APERTURE route — `substrate_lt_of_tension_lt_floor` takes `μ < κ₀` as its HYPOTHESIS, and by
  `ApertureRoute.confines_iff_pos_and_tension_lt_floor` that hypothesis IS confinement at the
  aperture and coupling in question (`DiffractionNoGo`);
* the ENVELOPE route — `WeakArm.no_uniform_quartic_constant_of_vanishing_rate` needs a rate bounded
  away from zero uniformly in the coupling AND the aperture, and that quantity IS the gap.

Each assumes its own conclusion. Multiplicative control does not: the constant family `ρ ≡ 1`
satisfies it at every `K ≥ 1`, at every pair of couplings, and has no decay at any lag. So the
hypothesis of `confines_at_of_grid_point_and_mul_control` is strictly weaker than what it concludes,
and the grid point is doing real work rather than smuggling the answer in.

The witness is easy, and that is not a defect — the question is whether the hypothesis CONTAINS the
conclusion, and one gapless profile meeting it answers that.

DERIVED: `1` is the constant family's value and the identity perturbation; `K` is a variable. -/
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

/-! ## 4. The constant, made concrete at zero coupling -/

/-- **THE ADMISSIBLE PERTURBATION AT ZERO COUPLING IS `1.1072`**, and the margin it must fit inside
is `1 - 3^{-1/4}`.

CHOSEN, and rounded DOWN — away from the claim, which asserts this `K` is admissible. The exact
supremum is `(2+2m)/(2+m) = 1.10720834…` at `m = 1 - 3^{-1/4} = 0.24016431…`; `1.1073` would put the
modulus at `0.240394`, ABOVE the margin, and violate the very inequality it would be quoted under.
The bracket is `LagTwoBound.floor_bounds`. -/
theorem admissible_K_at_zero_coupling :
    2 * ((1.1072 : ℝ) - 1) / (2 - 1.1072) ≤ 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
  have h := MassGap.LagTwoBound.floor_bounds
  have hnum : 2 * ((1.1072 : ℝ) - 1) / (2 - 1.1072) < 0.240164 := by norm_num
  linarith [h.2]

#print axioms admissible_K_at_zero_coupling

/-- **THE POINTWISE MULTIPLICATIVE HYPOTHESIS CANNOT BE BASED AT ZERO COUPLING.**

`PowerTail.wilsonCorrAt_at_zero_coupling` puts the profile at zero coupling at EXACTLY zero on every
lag of nonzero circle distance — it is a point mass at the contact lag. So `ρ_d(β) ≤ K · ρ_d(0) = 0`
forces `ρ_d(β) = 0` there, whatever `K` is. The hypothesis is met only where the correlation
vanishes at every nonzero lag, which on `[0, ∞)` is zero coupling itself.

**This is why section 5 exists.** A multiplicative bound needs a base point whose profile is nowhere
zero, and the one base point the tree evaluates is exactly the one that fails that. The `L¹`-relative
hypothesis below has no such degeneracy, because it measures the change against the TOTAL mass rather
than against the value at the same lag — and the total mass at zero coupling is the contact value,
which `contact_value_pos_at_zero_coupling` puts strictly above zero.

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

/-! ## 5. The `L¹`-relative form, which has no degeneracy -/

/-- **THE SAME STABILITY FROM A STRICTLY WEAKER HYPOTHESIS**, and with a better modulus.

Instead of controlling each lag against ITS OWN value — which is vacuous wherever that value is zero
— control the TOTAL change against the TOTAL mass: `∑ |σ - ρ| ≤ ε · ∑ ρ`. Then the weighted averages
differ by at most `2Wε/(1-ε)`.

`n` does not appear, exactly as in `avg_stable_of_mul_close`, and the modulus is smaller — `1 - ε`
rather than `2 - K` in the denominator. Pointwise multiplicative closeness IMPLIES this hypothesis
with `ε = K - 1`, so nothing is lost by preferring it.

DERIVED: `ε < 1` is where the perturbed total mass could vanish, forced by the algebra rather than
chosen; the `2` in the numerator counts the two terms the quotient rule produces. -/
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

/-- **THE CRITERION UNDER `L¹`-RELATIVE CONTROL.** `avg_stable_of_l1_close` at `W = 1`, available
because the criterion's weight is a cosine. Runs on the PROVED reflection positivity. -/
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

/-- **ONE GRID POINT PLUS `L¹`-RELATIVE CONTROL GIVES THE CRITERION.** The form to use. -/
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

/-- **CONFINEMENT AT EVERY COUPLING WHOSE PROFILE HAS MOVED BY UNDER `10.72%` OF THE CONTACT VALUE.**

The concrete instance, non-degenerate, with every constant evaluated. At zero coupling the profile is
a point mass at the contact lag (`PowerTail.wilsonCorrAt_at_zero_coupling`,
`contact_value_pos_at_zero_coupling`), so the total mass `∑ ρ_d(0)` IS the contact value `ρ_0(0)`,
strictly positive — and the hypothesis reads: **the total change in the profile since zero coupling
is at most `10.72%` of the contact value.** That is a condition on a quantity that is not identically
zero, unlike the pointwise multiplicative one, which `mul_control_from_zero_forces_a_point_mass`
shows is met at no positive coupling whose correlation is anywhere nonzero.

`ConfinesZero.cosAvgEven_at_zero` gives the cosine average exactly `1` at zero coupling, so the whole
margin `1 - 3^{-1/4}` is available to spend.

CHOSEN, and rounded DOWN — away from the claim, which asserts this `ε` is admissible. The exact
supremum is `m/(2+m) = 0.10720822…` at the certified margin `m = 0.240164`; `0.1073` would put the
modulus at `0.2403943`, ABOVE the margin, and violate the inequality it would be quoted under. The
bracket on the floor is `LagTwoBound.floor_bounds`. -/
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

/-- **AND THE HYPOTHESIS IS ACTUALLY MET — on a neighbourhood of zero coupling.**

A sufficient condition whose hypothesis nothing satisfies proves nothing, so the hypothesis gets a
theorem of its own. `mul_control_from_zero_forces_a_point_mass` is what happens when that check is
skipped; this is the check passing for the `L¹` form.

The `L¹` distance from the zero-coupling profile is continuous in the coupling
(`continuous_wilsonCorrAt`) and vanishes at zero coupling, while the right-hand side is a FIXED
positive number — `10.72%` of the contact value, positive by
`wilson_reflection_positive_at_even`. So the inequality holds on a ball.

The radius is existential and nothing here names a value for it: that is exactly the quantity a
dynamical estimate would have to supply, and supplying it for all of `[0, ∞)` is B5. What this
theorem establishes is that the target is a real one. -/
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

/-- **CONFINEMENT NEAR ZERO COUPLING, WITH THE MECHANISM NAMED.**

`ConfinesZero.confines_near_zero` already gives a neighbourhood, from bare continuity of the cosine
average. This derives the same conclusion through `confines_at_of_l1_control_from_zero`, so the
radius is tied to an explicit and physically meaningful quantity — how far the profile has moved in
`L¹` relative to the contact value — rather than to an unnamed modulus of a composite. The two agree
where they overlap; what this adds is that the SAME inequality extends to every coupling the `L¹`
control reaches, which bare continuity does not give. -/
theorem confines_near_zero_via_l1 (a : EvenAp) :
    ∃ b > 0, ∀ β : ℝ, |β| < b → (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β := by
  obtain ⟨b, hb, h⟩ := l1_control_from_zero_holds_near_zero a
  exact ⟨b, hb, fun β hβ => confines_at_of_l1_control_from_zero a β (h β hβ)⟩

#print axioms confines_near_zero_via_l1

/-! ## 6. The finite-grid route, and the flagship from two named hypotheses -/

/-- `L¹`-relative closeness of the profile at `β₂` to the profile at `β₁`, named so the grid
statements below read. The coupling is clamped at `max · 0` exactly as `readEven` clamps it.

DERIVED: no numeral is a magnitude. `0` is the clamp `EvenAperture.readEven_eq_at_zero` imposes;
`ε` is a variable. -/
def L1Close (a : EvenAp) (β₁ β₂ ε : ℝ) : Prop :=
  ∑ d, |MassGap.wilsonCorrAt a.1 (max β₂ 0) d - MassGap.wilsonCorrAt a.1 (max β₁ 0) d|
    ≤ ε * ∑ d, MassGap.wilsonCorrAt a.1 (max β₁ 0) d

#print axioms L1Close

/-- **THE FINITE-GRID ROUTE, IN THE CRITERION VARIABLE.**

Certify the cosine average at each of a family of couplings, each clearing the floor by a margin `m`;
control the `L¹`-relative motion of the profile inside each cell by `ε` with `2ε/(1-ε) ≤ m`; and the
criterion holds at every coupling the cells cover.

`ι` is arbitrary — the grid may be finite, and for the route to be a computation it should be — but
nothing in the argument needs that, so nothing here assumes it.

**What this changes and what it does not.** It converts the middle interval from a `∀ β` estimate
into a FINITE list of certified values plus a modulus, which is a different kind of task. It does
NOT make that task easy: each `cosAvgEven a (grid i)` is a Haar integral over `SU(3)` on the whole
lattice, and by the compression argument in `CompactBeta` a Monte Carlo value can REFUTE such a
bound and never establish one. What the grid buys is that the modulus between cells is now
volume-free, which `CompactBeta`'s extensive Lipschitz constant was not. -/
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

/-- **THE FLAGSHIP FROM TWO NAMED HYPOTHESES.**

This is the finish line stated once, at an arbitrary even aperture, and it is the whole of what is
open:

* a **grid** on `[0, B]` — finitely many certified values of the cosine average, each clearing the
  floor by `m`, with the cells covered to `L¹`-relative accuracy `ε` satisfying `2ε/(1-ε) ≤ m`;
* a **far arm** on `[B, ∞)` — the criterion at every coupling above the cut.

The negative half-line is free: `ConfinesZero.cosAvgEven_eq_one_of_nonpos` clamps it, so the cosine
average is exactly `1` there and `floor_lt_one` clears the floor. Nothing has to be supplied below
zero coupling, and that is the clamp `readEven` imposes, not an assumption made here.

Compare `FreeFieldLagTwoSix.confines_of_arms_six`, which assembles the same two halves at extent SIX
through the lag-two reduction. This assembles them at ANY even aperture through `cosAvgEven` itself,
and the middle half is a finite list rather than a `∀ β` statement.

DERIVED: `0` is the bottom of the coupling range and the clamp; `B`, `ε`, `m` and the grid are all
variables, which is what makes this a reduction rather than a claim. -/
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

/-- **AND THE CLAY FLAGSHIP FROM THE SAME TWO HYPOTHESES**, through
`ApertureRoute.flagship_of_confinement_at_an_aperture` — the gap, non-triviality, `SO(4)` and the
continuum object. Nothing else is interposed. -/
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

/-- **THE ASSEMBLY'S TWO HYPOTHESES ARE JOINTLY SATISFIABLE.**

A reduction whose hypotheses cannot be met together reduces nothing — the same check that
`mul_control_from_zero_forces_a_point_mass` records failing for the pointwise multiplicative form.
Here both hold at once on a genuine interval: the one-point grid `{0}` clears the floor by the full
margin, because `ConfinesZero.cosAvgEven_at_zero` puts the cosine average at exactly `1` there, and
`l1_control_from_zero_holds_near_zero` covers `[0, B]` for `B` small enough.

This does NOT extend to large `B`, and that is exactly the open problem — but it establishes that
`confines_of_grid_and_far_arm` is a reduction with content rather than an implication from an empty
hypothesis.

DERIVED: `0.240164` is the certified margin under `1 - 3^{-1/4}` and `0.1072` the `ε` that fits
inside it, both as in `confines_at_of_l1_control_from_zero` and both rounded away from the claim.
The `2` is the halving that puts `B` strictly inside the radius the continuity argument supplies. -/
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

/-- **THE CRITERION FROM `L¹`-CLOSENESS TO ANY REFERENCE PROFILE WHOSE OWN AVERAGE CLEARS THE FLOOR.**

The general form. The reference `r` need not be a Wilson profile at any coupling — it is any
nonnegative profile with positive total mass whose cosine average clears the floor by `m`. Both arms
of B5 are instances:

* the NEAR arm takes `r` to be the zero-coupling profile, a point mass at the contact lag, average
  exactly `1` (`ConfinesZero.cosAvgEven_at_zero`);
* the FAR arm would take `r` to be the free-field profile `(fsCorr6 d)²`, whose average at extent six
  is `64165878255868/65459706282889 = 0.98023…`.

DERIVED: nothing here is a numeral. `r`, `ε` and `m` are variables and the floor is
`ApertureRoute`'s own constant. -/
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

/-- **THE FULL ASSEMBLY AT EXTENT SIX: a grid for the middle, the Gaussian remainder for the far
arm.**

The two halves do NOT want the same reduction, and that is a finding rather than a convenience:

* the MIDDLE goes through `cosAvgEven`, where the modulus between grid cells is volume-free
  (`avg_stable_of_l1_close`) while `CompactBeta`'s Lipschitz constant is extensive;
* the FAR arm goes through the LAG-TWO reduction, where `FreeFieldLagTwoSix.epsMaxSix = 24/25` lets
  the Gaussian be `96%` wrong. An `L¹` bound on the whole profile against the free-field reference
  would admit only `9.9%` — the free-field cosine average at extent six is `0.98023…`, so the margin
  over the floor is `0.2204` and `m/(2+m)` is `0.0992`. The lag-two route is `9.7×` more tolerant
  there, because it reads ONE ratio with `65.6×` of room rather than the whole profile.

So this takes the far arm in the form the tree already states it (`hfar` is exactly what
`FreeFieldLagTwoSix.effective_lag_two_bound_six` produces from `EffectiveGaussianLagTwoSix`) and the
middle in the form that is now volume-free. Both hypotheses are the tree's own named open items and
nothing else is interposed.

DERIVED: `5` is the APERTURE — `wilsonCorrAt 5` is the extent-six torus — `2` and `0` are the lags
the far-arm ratio relates, and `0` is also the bottom of the coupling range. `B`, `ε`, `m`, `K` and
the grid are variables. -/
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

/-- **AND THE CLAY FLAGSHIP FROM THOSE TWO.** The gap, non-triviality, `SO(4)` and the continuum
object, from a finite grid on `[0,B]` and the Gaussian remainder above it. -/
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

/-- The lag angle at extent six, unfolded. `Moment.Read.θ` discards its read, so this is definitional
— stated so the generic reduction below can be applied to a profile that is not a Wilson
correlation. -/
theorem theta_six (d : Fin 6) :
    (readEven ConfinesZero.ap6 0).θ d = 2 * Real.pi * ((d : ℕ) : ℝ) / (((5 : ℕ) : ℝ) + 1) := rfl

#print axioms theta_six

/-- **THE EXTENT-SIX WEIGHTED AVERAGE OF AN ARBITRARY SYMMETRIC PROFILE.**

`ConfinesZero.cosAvgEven_extent_six` computes this for the WILSON profile. The reference route needs
it for a profile that is not one, so the same cosines — `1, ½, −½, −1, −½, ½` — are applied to an
arbitrary `r` with the circle symmetry `r 5 = r 1`, `r 4 = r 2` carried as a hypothesis instead of
proved from `MomentShape.wilsonCorrAt_neg`.

DERIVED: the numerals are the six lag indices of `Fin 6` and the multiplicities the fold produces;
`6` is the extent and `5` the aperture. No magnitude. -/
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

/-- **THE FREE-FIELD REFERENCE PROFILE AT EXTENT SIX.** Wick's square of the exact lattice
propagator sum, `ρ_d = (fsCorr6 d)²`.

DERIVED: every entry is `FreeFieldLagTwoSix.fsCorr6` at that lag, squared — `fsCorr6_zero`,
`fsCorr6_one`, `fsCorr6_two`, `fsCorr6_three` and the circle fold `fsCorr6_fold`, which are
`decide`-checked against the exact rational kernel. `freeRefSix_eq_fsCorr_sq` ties this spelling to
those theorems so the numerals are not a second source. The `2` is Wick's square. -/
noncomputable def freeRefSix (d : Fin 6) : ℝ :=
  if (d : ℕ) = 0 then 933332400 ^ 2
  else if (d : ℕ) = 1 ∨ (d : ℕ) = 5 then 128163984 ^ 2
  else if (d : ℕ) = 2 ∨ (d : ℕ) = 4 then 21150000 ^ 2
  else 7678032 ^ 2

#print axioms freeRefSix

/-- The spelling above IS Wick's square of `fsCorr6`, at every lag. Stated so the numerals in
`freeRefSix` are checked against the tree's own exact values rather than trusted. -/
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

/-- Every entry is nonnegative. -/
theorem freeRefSix_nonneg (d : Fin 6) : 0 ≤ freeRefSix d := by
  fin_cases d <;> norm_num [freeRefSix]

#print axioms freeRefSix_nonneg

/-- And the total mass is strictly positive. -/
theorem freeRefSix_sum_pos : 0 < ∑ d, freeRefSix d := by
  simp only [Fin.sum_univ_six]
  norm_num [freeRefSix]

#print axioms freeRefSix_sum_pos

/-- **THE FREE-FIELD CONE AVERAGE AT EXTENT SIX, EXACTLY.**

    (ρ₀ + ρ₁ − ρ₂ − ρ₃) / (ρ₀ + 2ρ₁ + 2ρ₂ + ρ₃)
      = 887029101009119232 / 904914979654657536
      = 64165878255868 / 65459706282889  =  0.98023474…

The profile shape is `1, 0.018856, 0.000514, 0.0000677` — the lag-one value `0.018856` is the same
number `NonnegArm`'s positive control settles on, which is a consistency check rather than a
coincidence. -/
theorem freeRefSix_avg_eq :
    (∑ d, freeRefSix d * Real.cos ((readEven ConfinesZero.ap6 0).θ d)) / (∑ d, freeRefSix d)
      = (887029101009119232 : ℝ) / 904914979654657536 := by
  rw [sixAvg_of_symmetric freeRefSix (by norm_num [freeRefSix]) (by norm_num [freeRefSix])]
  norm_num [freeRefSix]

#print axioms freeRefSix_avg_eq

/-- **AND IT CLEARS THE ENTROPY FLOOR BY MORE THAN `0.22`.**

CHOSEN, and rounded DOWN — away from the claim, which asserts this much margin is available. The
exact margin is `0.98023474… − 0.75983568… = 0.22039905…`; `0.22` is under it and
`LagTwoBound.floor_bounds` brackets the floor above by `0.759836`. -/
theorem freeRefSix_clears_floor :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) + 0.22
      < (∑ d, freeRefSix d * Real.cos ((readEven ConfinesZero.ap6 0).θ d))
        / (∑ d, freeRefSix d) := by
  rw [freeRefSix_avg_eq]
  have h := MassGap.LagTwoBound.floor_bounds
  have hq : (0.979836 : ℝ) < (887029101009119232 : ℝ) / 904914979654657536 := by norm_num
  linarith [h.2]

#print axioms freeRefSix_clears_floor

/-- **THE FAR ARM IN THE SAME SHAPE AS THE MIDDLE: stay within `9.9%` in `L¹` of the free field.**

With the near arm (`confines_at_of_l1_control_from_zero`, `10.72%` of the contact value) this puts
the WHOLE of B5 in one sentence: **the Wilson profile stays close, in `L¹` relative to total mass, to
an explicitly known reference at every coupling** — a point mass near zero coupling, the exact
free-field profile far out, and certified grid values between.

CHOSEN, and rounded DOWN: `2ε/(1−ε) ≤ 0.22` needs `ε ≤ 0.0990990…`, and `0.099` is under it while
`0.0992` is NOT — `0.0992` gives `0.2202486`, above the certified margin `0.22`. It IS under the
exact margin `0.2203990`, so the two roundings must not be mixed.

**This is not the far arm to use for the Gaussian remainder.** `FreeFieldLagTwoSix.epsMaxSix = 24/25`
lets that be `96%` wrong, because the lag-two route reads ONE ratio with `65.6×` of room rather than
the whole profile against an absolute margin of `0.22`. Against an `L¹` hypothesis the comparison
reverses — `cosAvgEven` admits `0.099` where lag two admits about `0.031` — so which reduction wins
depends on the SHAPE of the hypothesis available, not on the reduction alone. -/
theorem confines_at_of_l1_close_to_free_field_six (β : ℝ)
    (hl1 : ∑ d, |MassGap.wilsonCorrAt 5 (max β 0) d - freeRefSix d|
      ≤ 0.099 * ∑ d, freeRefSix d) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven ConfinesZero.ap6 β :=
  confines_at_of_l1_close_to_reference ConfinesZero.ap6 β freeRefSix 0.099 0.22
    freeRefSix_nonneg freeRefSix_sum_pos (by norm_num) (by norm_num) (by norm_num)
    freeRefSix_clears_floor hl1

#print axioms confines_at_of_l1_close_to_free_field_six

/-! ## 9. Contact dominance: the criterion with no shape facts and no aperture -/

/-- The lag angle, unfolded at an arbitrary even aperture. `Moment.Read.θ` discards its read. -/
theorem theta_eq (a : EvenAp) (d : Fin (a.1 + 1)) :
    (readEven a 0).θ d = 2 * Real.pi * ((d : ℕ) : ℝ) / (((a.1 : ℕ) : ℝ) + 1) := rfl

#print axioms theta_eq

/-- The contact lag sits at angle zero, so its cosine is one. This is the only lag whose weight is
known without computing a cosine, and it is what makes the bound below aperture-uniform. -/
theorem cos_theta_zero (a : EvenAp) :
    Real.cos ((readEven a 0).θ (0 : Fin (a.1 + 1))) = 1 := by
  rw [theta_eq a 0]
  norm_num

#print axioms cos_theta_zero

/-- **THE COSINE AVERAGE IS AT LEAST `(2ρ₀ − S)/S`**, where `ρ₀` is the contact value and `S` the
total mass.

Every lag contributes at least `−ρ_d`, and the contact lag contributes exactly `+ρ₀`, so the
numerator is at least `ρ₀ − (S − ρ₀)`. No shape fact, no log-convexity, no lag structure and no
extent enters — only `|cos| ≤ 1`, `cos 0 = 1` and the nonnegativity half of reflection positivity.

The proof is the observation that `d ↦ ρ_d(1 + cos θ_d)` is nonnegative termwise, so the whole sum
is at least its contact term `2ρ₀`, and that sum is `S + ∑ ρ_d cos θ_d`. -/
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

/-- **THE CRITERION FROM CONTACT DOMINANCE ALONE.**

    (1 + c) · S  <  2 · ρ₀        ⟹        c < cosAvgEven a β

at EVERY even aperture, where `c = 3^{-1/4}`, `ρ₀` is the contact value and `S` the total mass.

Equivalently: the off-contact mass is under `(1−c)/(1+c)` of the contact value, or the off-contact
SHARE of the total is under `(1−c)/2`. Nothing about the lag structure is used, so this holds at
apertures for which the tree states no criterion at all.

DERIVED: `2` is the contact lag's own weight `1 + cos 0`; the floor is `ApertureRoute`'s constant. -/
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

/-- **THE CONTACT THRESHOLD IS THE SQUARE ROOT OF THE EXTENT-FOUR LAG-TWO THRESHOLD**, exactly.

`LagTwoBound.lagTwoThreshold = ((1−c)/(1+c))²` and the off-contact-to-contact ratio this file admits
is `(1−c)/(1+c)`. The two are the same constant at different powers, and the reason is structural
rather than numerical: `lagTwoThreshold` is the SQUARE because the lag-two route substitutes
`ρ(1) ≤ √(ρ(0)ρ(2))` and then works in `v = √(ρ(2)/ρ(0))`, where the admissible root is exactly
`(1−c)/(1+c)`. Contact dominance works in the mass directly and never takes that square root. -/
theorem contact_threshold_sq_eq_lagTwoThreshold :
    ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4))) ^ 2
      = MassGap.LagTwoBound.lagTwoThreshold := rfl

#print axioms contact_threshold_sq_eq_lagTwoThreshold

/-- **AND THE NUMERIC FORM: an off-contact share under `12%` of the total suffices**, at every even
aperture.

CHOSEN, and rounded DOWN — away from the claim, which asserts this share is sufficient. The exact
threshold is `(1−c)/2 = 0.12008215…`; `LagTwoBound.floor_bounds` brackets `c` above by `0.759836`,
so `0.12` is under it with room. Equivalently the contact value must carry at least `88%` of the
mass.

**Where this sits against the other routes.** For the free-field profile at extent six the
off-contact share is `0.038808/1.038808 = 0.037357`, a margin of `3.2×` — against `65.6×` for the
lag-two route at the same extent. So contact dominance is much the weakest of the three sufficient
conditions. What it has instead is that it holds at EVERY even aperture with no shape facts, no lag
structure and no extent-specific criterion, so it applies where nothing else in the tree does, and
it is a single scalar to certify rather than a profile. -/
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

/-! ## 10. The criterion does not know the gauge group

C3 reads "any compact simple gauge group `G`" and the tree's row says `SU(3)`. It is worth being
exact about WHERE the three enters, because there are two different threes and only one of them is
the colour count.

**The floor's three is geometric.** `Floor.directed_paths_card` counts directed cube-paths: the
origin cube followed by `k` steps, each a choice in `{+x, +y, +z}` — `Fintype.card (Fin k → Fin 3)`.
That is a lattice-geometry fact in four dimensions and mentions no gauge group. `κ₀ = ¼ log 3` is its
density and `3^{-1/4} = e^{-κ₀}` is the floor. **So the bar the criterion clears is the same for every
gauge group.**

The colour count enters somewhere else entirely: `WilsonBridge.corrClay` is
`corrHyper (d := 4) 3 n 0 1 2`, and THAT three is `Nc`. `corrHyper` takes `Nc` as a parameter, so the
generic object already exists and `corrClay` is its `Nc = 3` instance.

**What follows is that the criterion machinery is floor-parametric.** The theorems below are the
same ones as above with the floor as a VARIABLE rather than `3^{-1/4}`, and their proofs are
unchanged — none of them ever used the floor's value. So if another group gave a different floor the
machinery would run at that floor, and C3's real gap is carrying `Nc` through the correlation and its
reflection positivity, not re-deriving the bar.

DERIVED: `c` is a variable standing for the floor; `0 < c` and `c < 1` are what
`ConfinesZero.floor_pos` and `floor_lt_one` prove of the actual one, carried as hypotheses so the
statements do not name it.
-/

/-- **THE BASE OF THE FLOOR IS THE DIRECTED-STEP COUNT**, not the colour count.
`Floor.directed_paths_card` counts maps `Fin k → Fin 3`, the `k` steps of a directed cube-path each
choosing from `{+x, +y, +z}`. This records that the `3` in `3^{-1/4}` is the cardinality of THAT
type. -/
theorem floor_base_is_directed_step_count :
    (Fintype.card (Fin 3) : ℝ) = 3 := by simp

#print axioms floor_base_is_directed_step_count

/-- **CONTACT DOMINANCE AT AN ARBITRARY FLOOR.** `confines_at_of_contact_dominance` with the floor a
variable; the proof never looked at its value. -/
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

/-- **`L¹` STABILITY AGAINST A REFERENCE, AT AN ARBITRARY FLOOR.**
`confines_at_of_l1_close_to_reference` with the floor a variable. Same proof. -/
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

/-- **AND THE TWO ARE THE SAME STATEMENTS AT THE ACTUAL FLOOR**, so nothing is lost by using the
parametric forms. Recorded so the specialisation is checkable rather than assumed. -/
theorem contact_dominance_floor_specialises (a : EvenAp) (β : ℝ)
    (h : (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d)
      < 2 * MassGap.wilsonCorrAt a.1 (max β 0) 0) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β :=
  confines_at_of_contact_dominance_floor a β _ h

#print axioms contact_dominance_floor_specialises

/-! ## 11. Satisfiability, for every sufficient condition in this file

A sufficient condition whose hypothesis nothing satisfies proves nothing.
`mul_control_from_zero_forces_a_point_mass` is what that failure looks like when the check is
skipped, so the check is applied to the rest here.

| condition | hypothesis met? |
|---|---|
| `confines_at_of_l1_control_from_zero` | `l1_control_from_zero_holds_near_zero` — on a neighbourhood of zero coupling |
| `confines_of_grid_and_far_arm` | `grid_hypotheses_are_met_near_zero` — both hypotheses jointly, on an interval |
| `confines_at_of_off_contact_share_small` | `contact_dominance_holds_at_zero_coupling`, below |
| `confines_at_of_l1_close_to_free_field_six` | **OPEN, and that is the point** — see the note after it |

**The far arm's hypothesis is the one that is not settled**, and its being unsettled is not the same
defect. The Wilson profile being within `9.9%` in `L¹` of the exact free-field profile at large
coupling IS the weak-coupling statement, so a satisfiability theorem for it would BE the far arm.
What can be said is that it is not absurd — the reference has positive total mass and the distance to
it is a continuous quantity — and that `FreeFieldLagTwoSix.EffectiveGaussianLagTwoSix` is the tree's
own, more tolerant, form of the same demand.
-/

/-- **CONTACT DOMINANCE HOLDS AT ZERO COUPLING**, so
`confines_at_of_off_contact_share_small`'s hypothesis is met somewhere.

At zero coupling the profile is a point mass at the contact lag —
`PowerTail.wilsonCorrAt_at_zero_coupling` kills every lag of nonzero circle distance and
`contact_value_pos_at_zero_coupling` keeps the contact value strictly positive — so the off-contact
mass is exactly `0`, and `0 < 0.12 · ρ₀`.

DERIVED: `0.12` is the constant `confines_at_of_off_contact_share_small` carries, rounded down from
`(1−c)/2`; `0` is the off-contact mass at zero coupling. -/
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

/-- **AND THEREFORE THE CRITERION HOLDS AT ZERO COUPLING BY THAT ROUTE**, which checks the whole
chain rather than the hypothesis alone. It agrees with `ConfinesZero.confines_at_zero`, reached by a
different argument — the point mass gives cosine average exactly `1` there — so the two routes are
consistent where they overlap. -/
theorem confines_at_zero_via_contact_dominance (a : EvenAp) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a 0 :=
  confines_at_of_off_contact_share_small a 0 (contact_dominance_holds_at_zero_coupling a)

#print axioms confines_at_zero_via_contact_dominance

/-! ## 12. What MONOTONICITY in the coupling would buy: the whole middle interval

Every route above splits the coupling axis and pays for the middle — a grid of certified values, or
an `L¹` modulus, or both. **One hypothesis removes the middle entirely**: if the lag-two ratio
`ρ(2)/ρ(0)` is non-decreasing in `β`, then its value anywhere below the cut is at most its value AT
the cut, which the far arm already bounds. No grid, no modulus, no certified interior values.

`confines_of_monotone_ratio_six` is that reduction, and it is stated because the reduction is true
and worth having. **But the hypothesis is CONTRADICTED by the tree's own measured data, so this is
not a route to attack.** That is recorded here rather than left for someone to rediscover.

**THE MEASUREMENT.** `research/data/9_2_dat_confinement_cos.csv` reads the cosine average across the
coupling and it is NOT monotone — it falls to an interior minimum and then rises again:

    β        0.50   1.00   1.60   2.00   2.20   2.30   2.40   2.50   2.60
    cos_avg  1.0014 0.9981 0.9957 0.9921 0.9867 0.9863 0.9895 0.9905 0.9907
                                                 ^min   ^rises from here

`9_1_dat_d2_bound.csv` reads the profile's circular second moment on the same couplings and agrees
from the other side: it PEAKS at `β = 2.20` (`0.19211`) and falls to `0.13637` by `2.60`, a drop of
`8.0σ` of the last point's own error. A spread that rises and then falls is a cosine average that
falls and then rises; the two files are the same fact read twice.

So the profile RE-CONCENTRATES above the crossover, and no functional of it that increases with the
spread — the lag-two ratio included — is monotone in the coupling. **Monotonicity is not merely
unproved here; it is refuted by measurement**, which is the one thing measurement is allowed to do.

**WHAT THE DATA DOES NOT DO.** It does not establish B5, and per the standing rule nothing measured
can. Two caveats bound how far it should be read. The estimator returns `1.0014` and `1.0006` at the
two smallest couplings, above the analytic maximum of `1`, so its noise is of order `10⁻³` and
differences smaller than that are not differences. And the interior minimum sits at `0.9863` against
the floor `0.759836` — a margin of `+0.2265` where the total available margin is `0.2402` — so at the
tightest coupling it measures, the criterion spends about `6%` of its room. That is a reason to
believe B5 rather than a proof of it, and it says where a grid would have to be finest.

**WHAT THE TREE HAS TOWARDS PROVING MONOTONICITY: nothing**, which is now moot. There is no
`β`-monotonicity of the correlation anywhere, and no correlation inequality — `Griffiths`, `Ginibre`
and `FKG` do not occur in any module.

**AND THE POSITIVITY THE TREE DOES HAVE IS A DIFFERENT STATEMENT**, which is worth recording
because the resemblance invites the attempt. `CharacterExpansion.wilson_kernel_nonneg` says
`∑ᵢⱼ zᵢzⱼ e^{β⟨Aᵢ,Aⱼ⟩} ≥ 0` — positive-definiteness in the CONFIGURATION variables, at fixed `β`.
Monotonicity would need `Cov(O, S) ≥ 0`, about the `β`-derivative of an expectation. Different
objects, and the first does not supply the second.

**So the theorem below stands and its hypothesis does not.** It is kept because a reduction is worth
knowing even when its input fails: it says exactly how much the middle interval costs, namely
everything that monotonicity would have bought.

DERIVED: `5` is the APERTURE — `wilsonCorrAt 5` is the extent-six torus — and `2` and `0` are the
lags the ratio relates. `B` and `K` are variables.
-/

/-- **MONOTONICITY PLUS THE FAR ARM GIVES B5 AT EXTENT SIX, with no middle interval.**

The monotonicity hypothesis is cross-multiplied so no division and no positivity of the denominator
enters it: `ρ(2,β₁)·ρ(0,β₂) ≤ ρ(2,β₂)·ρ(0,β₁)` is `ρ(2)/ρ(0)` non-decreasing, stated where both
sides are defined regardless.

Below the cut the ratio is at most its value at the cut; at and above the cut the far arm bounds it.
So the bound holds at every nonnegative coupling, which is `LagTwoRatioSix`. -/
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

/-- **AND THE FLAGSHIP FROM THE SAME TWO.** Stated so the value of monotonicity is visible end to
end: it converts the far arm alone into the Clay flagship. -/
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

/-! ## 13. Both ends are computed, and they clear by comparable margins

Two couplings have their cosine average known exactly rather than measured:

* **zero coupling** — `ConfinesZero.cosAvgEven_at_zero` gives exactly `1`, the profile being a point
  mass at the contact lag. Margin over the floor: `1 − 0.7598357 = 0.2401643`.
* **the free-field limit** — `freeRefSix_avg_eq` gives exactly
  `887029101009119232/904914979654657536 = 0.9802347`. Margin: `0.2203991`.

**The two margins differ by `0.0198`**, and the SMALLER belongs to the free field. So the criterion is
tighter at the weak-coupling end than at the strong-coupling end, and neither end is close to
failing: each spends under a tenth of the room between `1` and the floor.

**What that costs a failure.** For B5 to fail at some coupling, the cosine average there must fall
below the floor — a drop of at least `0.2204` from the free-field value and `0.2402` from the
zero-coupling value. By `avg_stable_of_l1_close` a drop of `m` needs the profile to move by `ε` in
`L¹` with `2ε/(1−ε) ≥ m`, so a drop of `0.22` needs `ε ≥ 0.0991`. **A failure therefore requires the
profile to sit more than `9.9%` away, in `L¹` relative to total mass, from BOTH computable ends at
once.**

`confines_of_l1_close_to_either_end` is the contrapositive, and it is the sharpest unconditional
statement of B5's remaining content this file can make: staying near EITHER end at each coupling —
they need not be the same end at different couplings — is enough.

DERIVED: `0.1072` and `0.099` are the two admissible `ε`, each rounded DOWN from `m/(2+m)` at its own
end's certified margin, as in `confines_at_of_l1_control_from_zero` and
`confines_at_of_l1_close_to_free_field_six`. Nothing new is chosen here.
-/

/-- **B5 HOLDS IF THE PROFILE STAYS NEAR EITHER COMPUTABLE END, at each coupling separately.**

The disjunction is per coupling: a profile may be near the point mass for small `β`, near the free
field for large `β`, and it need never be near both at once. What it may NOT do, at any coupling, is
be far from both — and `9.9%` in `L¹` is how far "far" has to be.

This is the two arms of §5 and §8 put together with nothing in between, which is the point: the
middle interval costs nothing when every coupling is within reach of one end or the other. -/
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

/-- **AND THE CLAY FLAGSHIP FROM THAT ONE HYPOTHESIS.** -/
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

/-- **THE FREE-FIELD END IS THE TIGHTER OF THE TWO**, by `0.0198`.

Both margins are proved, not measured: `1` at zero coupling and
`887029101009119232/904914979654657536` in the free-field limit. Recorded because it says which end
a sharpening should be aimed at, and because the ORDER is the opposite of what the strong-coupling
expansion's reach would suggest. -/
theorem free_field_end_is_tighter :
    (887029101009119232 : ℝ) / 904914979654657536 - (3 : ℝ) ^ (-(1 : ℝ) / 4)
      < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
  have h : (887029101009119232 : ℝ) / 904914979654657536 < 1 := by norm_num
  linarith

#print axioms free_field_end_is_tighter

/-! ## 14. The free field as the INFIMUM — what monotonicity should have been

Monotonicity failed because the profile re-concentrates above the crossover (§12). But the data that
refutes it points at a different hypothesis, and this one it does not refute.

**The measured minimum sits ABOVE the free-field value.** `9_2_dat_confinement_cos.csv` bottoms at
`0.9863` at `β = 2.30`, and `freeRefSix_avg_eq` computes the free-field limit exactly as
`0.9802347`. The minimum is `0.0061` ABOVE the limit — about six times the estimator's own noise,
which the `1.0014` at the smallest coupling puts at `~10⁻³`. So across every coupling it measures,
the cosine average never goes below its own asymptote.

**That is the hypothesis to name:** the free-field limit is the infimum over the whole half-line, not
merely the endpoint. It implies B5 immediately, because the limit clears the floor by `0.2204`
(`freeRefSix_clears_floor`) — no grid, no modulus, no interior values.

**And unlike monotonicity it is not refuted.** Monotonicity said the curve may never turn; this says
only that it may never sink below where it ends. The measured turn at `β ≈ 2.3` violates the first
and is consistent with the second. Per the standing rule, that consistency is NOT evidence — data may
refute and never establish — but the distinction between "refuted" and "not refuted" decides which
hypothesis is worth an attack, and this is the one.

DERIVED: the numerator and denominator are `freeRefSix_avg_eq`'s, carried unchanged; no new numeral.
-/

/-- **THE FREE-FIELD LIMIT IS THE INFIMUM.** Named as a `Prop` so what is assumed is one line.

Compare `MonomialsSeparateFinitely`: a named obligation is worth more than a paragraph, and this one
is the successor to the monotonicity hypothesis §12 refutes.

DERIVED: `887029101009119232/904914979654657536` is `freeRefSix_avg_eq`'s value, carried unchanged
and not retyped — that theorem computes it from `freeRefSix`, whose entries `freeRefSix_eq_fsCorr_sq`
ties to `FreeFieldLagTwoSix.fsCorr6`. `0` is the bottom of the coupling range, and `2` is the lag
`cosAvgEven`'s aperture `ap6` carries. No magnitude is chosen here. -/
def FreeFieldIsTheInfimum : Prop :=
  ∀ β : ℝ, 0 ≤ β →
    (887029101009119232 : ℝ) / 904914979654657536 ≤ cosAvgEven ConfinesZero.ap6 β

#print axioms FreeFieldIsTheInfimum

/-- **AND IT GIVES B5 OUTRIGHT.** The free-field value clears the floor by `0.2204`, so a curve that
never sinks below it never reaches the floor. The negative half-line is the `readEven` clamp. -/
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

/-- **AND THE CLAY FLAGSHIP FROM IT.** One hypothesis, one line, the whole statement. -/
theorem flagship_of_free_field_infimum (h : FreeFieldIsTheInfimum) :
    ApertureRoute.FlagshipAt (confines_of_free_field_infimum h) :=
  ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_free_field_infimum

/-- **IT HOLDS AT ZERO COUPLING**, where the average is exactly `1`. A named obligation wants a check
that something satisfies it; this is the one coupling where that is settled outright. -/
theorem freeFieldIsTheInfimum_at_zero :
    (887029101009119232 : ℝ) / 904914979654657536 ≤ cosAvgEven ConfinesZero.ap6 0 := by
  rw [cosAvgEven_at_zero]
  norm_num

#print axioms freeFieldIsTheInfimum_at_zero

end MassGap.CosAvgStability
