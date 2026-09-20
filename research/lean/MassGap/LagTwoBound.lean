import MassGap.ConfinesZero
import MassGap.ContactFloor

/-!
# MassGap.LagTwoBound — `ConfinesAtAnAperture` at extent four is ONE ratio

`ConfinesZero.confines_extent_four_of_lag_two_small` reduces `ApertureRoute.ConfinesAtAnAperture`
at the smallest even aperture to

    (1 + c)² ρ(2)  <  (1 − c)² ρ(0),        c = 3^{−1/4},  ρ = wilsonCorrAt 3 (max β 0)

and `ConfinesSharp.confines_extent_four_iff` says that criterion is exact. This file puts it in
RATIO form — the shape a quantitative bound on the second lag is actually produced in — and settles
what the tree's own quantities do to it.

## What is proved here

* `lagTwoThreshold` — the derived number `((1 − c)/(1 + c))²`, with `c = 3^{−1/4}` read off
  `Complete.κ₀YM` (`Complete.lean:324`); `Floor.lean` carries the same value only unnamed, inside `floor_pos`. `lagTwoThreshold_gt` / `lagTwoThreshold_lt` bracket it between `0.018623` and
  `0.018625`; the bracket REPORTS a derived quantity and is not a chosen magnitude. The chain is
  `floor_pow_four` (`c⁴ = 1/3`, `rpow` algebra alone) → `floor_sq_bounds` → `floor_bounds`.

* `lag_two_criterion_of_ratio` — `ρ(2) ≤ K ρ(0)` with `K < lagTwoThreshold` gives the criterion at
  that coupling. The strictness is free: `PlaqVariance.corrClay_zero_pos` is `0 < ρ(0)` at EVERY real
  coupling and every extent, so a NON-strict ratio bound suffices and the denominator never has to
  be assumed away.

* `confines_of_lag_two_ratio` — **the target bridge.** One hypothesis,

      ∀ β ≥ 0,  wilsonCorrAt 3 β 2  ≤  K · wilsonCorrAt 3 β 0,    K < lagTwoThreshold

  gives `ApertureRoute.ConfinesAtAnAperture` outright, and with it everything
  `ApertureRoute.flagship_of_confinement_at_an_aperture` carries. One lag, one ratio, one inequality.

* `contact_relative_constant_too_large` — **the contact-relative route cannot supply it, and not
  narrowly.** `ContactFloor.contact_relative_unconditional` gives `ρ(d) ≤ C ρ(0)/circLag(d)⁴`, which
  at `circLag 2 = 2` is `ρ(2) ≤ (C/16) ρ(0)`, so that route would close B5 outright if
  `C < 16 · lagTwoThreshold < 0.298`. The `C` the proof constructs is `coreConst(16·4, b)·S/δ`
  (`StrongArm.contact_relative_on_strong_arm`), and `le_coreConst` puts its first factor alone at
  `128` or more — before `S ≥ 1` and before dividing by a floor `δ ≤ ρ(0)`.

* `exists_cut_lag_two_ratio` — **the ratio bound IS proved on a derived interval `[0, b]`**, with the
  ratio constant a free parameter: for every `K > 0` there is a cut `b > 0` with `ρ(2) ≤ K ρ(0)` on
  `[0, b]`. Numerator from `StrongCoupling.corrClay_abs_le_coreConst_mul_rate_pow` at
  `k = 1 < circLag 2`, denominator from `ContactFloor.corrClay_zero_ge`'s `e^{−128β}·ρ(0)|_{β=0}`.
  No numeral is named for `b`.

* `confines_below_derived_cut` — hence `3^{−1/4} < cosAvgEven ap4 β` on `(−∞, b]`.

## What is NOT proved, stated exactly

`(b, ∞)` is open, `b` the cut above. Both quantitative inputs fail there, for opposite reasons: the
rate is unbounded above in the coupling at every degree (`StrongArm.coreRate_exceeds`, `∀ M, ∃ β ≥ 0,
M < coreRate K β`), so the numerator's estimate leaves the range where it says anything, and the
denominator's floor `e^{−128β}·ρ(0)|_{β=0}` degrades to nothing. Nothing else in the
tree bounds `ρ(2)/ρ(0)` at large coupling, and `ShapeNoGo.shape_facts_do_not_imply_confinement`
proves the coupling-free shape facts cannot close it on their own — at extent four those facts are
nonnegativity, circle symmetry and `ρ(1)² ≤ ρ(0)ρ(2)`, and the last one bounds `ρ(2)` from BELOW.
`LogConvex.corrClay_log_convex` needs both lag arguments strictly under the half `m = 2`, so the
pair `(1, 2)` that would give `ρ(2)² ≤ ρ(1)ρ(3)` is not available at this extent.

DERIVED: `3^{−1/4}` is `Floor`'s; `4` is the smallest even extent `EvenAp` admits; `circLag 2 = 2` at
that extent is `Moment.circLag`'s own value; `16·4` and `128` are `StrongCoupling.touchDeg_bd_le`
against `WilsonAction.wilsonDensity_le_two`. No statement below depends on a chosen magnitude.
-/

namespace MassGap.LagTwoBound

open MassGap MassGap.ApertureRoute MassGap.StrongCoupling

/-! ## 1. The threshold, and where it sits on the line -/

/-- `c⁴ = 1/3` at `c = 3^{−1/4}`. Pure `rpow` algebra: the exponent `(−1/4)·4` is `−1`. -/
theorem floor_pow_four : ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ (4 : ℕ) = 1 / 3 := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have h1 : ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ (4 : ℕ)
      = ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ (((4 : ℕ) : ℝ)) := (Real.rpow_natCast _ 4).symm
  have h2 : ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ (((4 : ℕ) : ℝ))
      = (3 : ℝ) ^ ((-(1 : ℝ) / 4) * ((4 : ℕ) : ℝ)) := (Real.rpow_mul h3 _ _).symm
  have h4 : (-(1 : ℝ) / 4) * ((4 : ℕ) : ℝ) = -(1 : ℝ) := by norm_num
  rw [h1, h2, h4, Real.rpow_neg h3, Real.rpow_one]
  norm_num

#print axioms floor_pow_four

/-- `c² = 3^{−1/2}`, bracketed. `(c²)² = 1/3` and `c² > 0` pin it between two rationals. -/
theorem floor_sq_bounds :
    0.5773501 < ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2
      ∧ ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 < 0.5773505 := by
  set c : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hcdef
  have hc0 : 0 < c := by rw [hcdef]; exact MassGap.ConfinesZero.floor_pos
  have h4 : c ^ (4 : ℕ) = 1 / 3 := by rw [hcdef]; exact floor_pow_four
  have hs0 : 0 < c ^ 2 := by positivity
  have hs2 : (c ^ 2) ^ 2 = 1 / 3 := by rw [← h4]; ring
  constructor
  · nlinarith [hs2, hs0]
  · nlinarith [hs2, hs0, sq_nonneg (c ^ 2 - 0.5773505)]

#print axioms floor_sq_bounds

/-- `3^{−1/4}` itself, bracketed, from the bracket on its square. -/
theorem floor_bounds :
    0.759835 < (3 : ℝ) ^ (-(1 : ℝ) / 4) ∧ (3 : ℝ) ^ (-(1 : ℝ) / 4) < 0.759836 := by
  obtain ⟨hlo, hhi⟩ := floor_sq_bounds
  set c : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hcdef
  have hc0 : 0 < c := by rw [hcdef]; exact MassGap.ConfinesZero.floor_pos
  constructor
  · nlinarith [hlo, hc0]
  · nlinarith [hhi, hc0, sq_nonneg (c - 0.759836)]

#print axioms floor_bounds

/-- **THE THRESHOLD ON THE LAG-TWO RATIO.** `ρ(2)/ρ(0)` strictly below this number is exactly what
log-convexity carries into `ConfinesZero.confines_extent_four_of_lag_two_small`: the quadratic
`(1+c)t² + 2ct − (1−c)` has discriminant `4` identically, so its positive root is `(1−c)/(1+c)` and
the criterion's own threshold on `t² = ρ(2)/ρ(0)` is that root squared. Nothing is chosen.

DERIVED, digit by digit, because this is the one number in the file that decides anything.

* `3` and `4` together are the floor `c = 3^{−1/4}`, which is `e^{−κ₀}` for the entropy floor
  `κ₀ = ¼ log 3` (`Reconstruction.exp_neg_κ0` is that identity — the file is `GappedExample.lean`, whose namespace is `MassGap.Reconstruction`). Both come from the directed-path
  count in `Floor.lean`: the number of directed cube paths is `3^k`, which is where the `3` is, and
  the per-area normalisation `((n−1) log 3)/(4n+2)` converges to `(1/4) log 3`, which is where the
  `4` is. Neither is fitted and neither is read off data; they are counted.
* The two `1`s are the `1 − c` and `1 + c` of that quadratic — the coefficients the log-convexity
  identity `((1−c)ρ₀ − (1+c)ρ₂)² − 4c²ρ₀ρ₂ = ((1−c)²ρ₀ − (1+c)²ρ₂)(ρ₀ − ρ₂)` produces, not a
  normalisation anyone imposed.
* `2` is the square. The criterion is a bound on `t = √(ρ(2)/ρ(0))`, so the bound on the RATIO is
  the positive root squared; the same `2` is the lag index in `ρ(2)`.
* `0` is the lag index in `ρ(0)`, the contact value the ratio is normalised by.

The threshold is therefore exact rather than a cut: `lagTwoThreshold_gt` and `lagTwoThreshold_lt`
bracket it between `0.018623` and `0.018625` for a reader, but the decision is made by the closed
form above, and the bracketing rationals decide nothing. -/
noncomputable def lagTwoThreshold : ℝ :=
  ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4))) ^ 2

#print axioms lagTwoThreshold

theorem lagTwoThreshold_pos : 0 < lagTwoThreshold := by
  have hc0 : 0 < (3 : ℝ) ^ (-(1 : ℝ) / 4) := MassGap.ConfinesZero.floor_pos
  have hc1 : (3 : ℝ) ^ (-(1 : ℝ) / 4) < 1 := MassGap.ConfinesZero.floor_lt_one
  unfold lagTwoThreshold
  exact pow_pos (div_pos (by linarith) (by linarith)) 2

#print axioms lagTwoThreshold_pos

/-- The threshold is above `0.018623` — the only direction a user of the bridge needs. -/
theorem lagTwoThreshold_gt : 0.018623 < lagTwoThreshold := by
  obtain ⟨hlo, hhi⟩ := floor_bounds
  have hc0 : 0 < (3 : ℝ) ^ (-(1 : ℝ) / 4) := MassGap.ConfinesZero.floor_pos
  unfold lagTwoThreshold
  set c : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hcdef
  have hden : (0 : ℝ) < (1 + c) ^ 2 := by nlinarith [hc0]
  rw [div_pow, lt_div_iff₀ hden]
  nlinarith [hhi, hc0, sq_nonneg (c - 0.759835)]

#print axioms lagTwoThreshold_gt

/-- And below `0.018625`, so the bracket is two-sided. -/
theorem lagTwoThreshold_lt : lagTwoThreshold < 0.018625 := by
  obtain ⟨hlo, hhi⟩ := floor_bounds
  have hc0 : 0 < (3 : ℝ) ^ (-(1 : ℝ) / 4) := MassGap.ConfinesZero.floor_pos
  unfold lagTwoThreshold
  set c : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hcdef
  have hden : (0 : ℝ) < (1 + c) ^ 2 := by nlinarith [hc0]
  rw [div_pow, div_lt_iff₀ hden]
  nlinarith [hlo, hc0, mul_pos (sub_pos.2 hhi) hc0]

#print axioms lagTwoThreshold_lt

/-! ## 2. The ratio form of the exact criterion -/

/-- **THE RATIO IMPLIES THE CRITERION**, at every real coupling. -/
theorem lag_two_criterion_of_ratio {β K : ℝ} (hK : K < lagTwoThreshold)
    (h : MassGap.wilsonCorrAt 3 β 2 ≤ K * MassGap.wilsonCorrAt 3 β 0) :
    (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 * MassGap.wilsonCorrAt 3 β 2
      < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 * MassGap.wilsonCorrAt 3 β 0 := by
  have hρ0 : 0 < MassGap.wilsonCorrAt 3 β 0 := by
    rw [MassGap.StrongArm.wilsonCorrAt_eq_corrClay]
    exact MassGap.PlaqVariance.corrClay_zero_pos 3 β
  unfold lagTwoThreshold at hK
  set c : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hcdef
  have hc0 : 0 < c := by rw [hcdef]; exact MassGap.ConfinesZero.floor_pos
  have hne : (1 : ℝ) + c ≠ 0 := ne_of_gt (by linarith)
  have hsq : (0 : ℝ) < (1 + c) ^ 2 := by nlinarith [hc0]
  have hcancel : (1 + c) * ((1 - c) / (1 + c)) = 1 - c := by
    field_simp
  calc (1 + c) ^ 2 * MassGap.wilsonCorrAt 3 β 2
      ≤ (1 + c) ^ 2 * (K * MassGap.wilsonCorrAt 3 β 0) :=
        mul_le_mul_of_nonneg_left h hsq.le
    _ < (1 + c) ^ 2 * (((1 - c) / (1 + c)) ^ 2 * MassGap.wilsonCorrAt 3 β 0) :=
        mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right hK hρ0) hsq
    _ = ((1 + c) * ((1 - c) / (1 + c))) ^ 2 * MassGap.wilsonCorrAt 3 β 0 := by ring
    _ = (1 - c) ^ 2 * MassGap.wilsonCorrAt 3 β 0 := by rw [hcancel]

#print axioms lag_two_criterion_of_ratio

/-- **THE TARGET BRIDGE.** A lag-two ratio bound at every nonnegative coupling, with `K` strictly
below the derived `lagTwoThreshold`, gives `ApertureRoute.ConfinesAtAnAperture` outright.

The negative half-line is free: `readEven` clamps at `max β 0`, so the hypothesis is only ever read
at a nonnegative coupling. -/
theorem confines_of_lag_two_ratio (K : ℝ) (hK : K < lagTwoThreshold)
    (h : ∀ β : ℝ, 0 ≤ β → MassGap.wilsonCorrAt 3 β 2 ≤ K * MassGap.wilsonCorrAt 3 β 0) :
    ApertureRoute.ConfinesAtAnAperture :=
  ⟨MassGap.ConfinesZero.ap4, fun β =>
    MassGap.ConfinesZero.confines_extent_four_of_lag_two_small β
      (lag_two_criterion_of_ratio hK (h (max β 0) (le_max_right β 0)))⟩

#print axioms confines_of_lag_two_ratio

/-! ## 3. What the contact-relative route can and cannot supply -/

/-- The lag-two instance of `circLag` at extent four, machine-checked. -/
theorem circLag_two : Moment.circLag (2 : Fin (3 + 1)) = 2 := by decide

#print axioms circLag_two

/-- **THE ASSEMBLED CONSTANT IS AT LEAST `128`** below the rate-one threshold. `le_corePrefactor`
is `128 ≤ corePrefactor`, and `1 − coreRate` is at most one on `β ≥ 0`, so dividing by it cannot
shrink the numerator. -/
theorem le_coreConst (K : ℕ) {β : ℝ} (hβ : 0 ≤ β) (hr : coreRate K β < 1) :
    128 ≤ coreConst K β := by
  have hP : (128 : ℝ) ≤ corePrefactor K β := le_corePrefactor K hβ
  have hr0 : (0 : ℝ) ≤ coreRate K β := coreRate_nonneg K hβ
  have hden : (0 : ℝ) < 1 - coreRate K β := by linarith
  unfold coreConst
  rw [le_div_iff₀ hden]
  nlinarith [hP, hr0]

#print axioms le_coreConst

/-- **THE CONTACT-RELATIVE ROUTE MISSES THE BAR BY OVER FOUR HUNDRED.** To close B5 at extent four
through `ContactFloor.contact_relative_unconditional` the constant would have to satisfy
`C < 16·lagTwoThreshold`, which is below `0.298`. The constant that proof builds is
`coreConst(16·4, b)·S/δ` with `S ≥ 1` (its own `L = 1` instance) and `δ` a FLOOR on `ρ(0)`, so it is
at least `coreConst(16·4, b)` — and that factor alone is at least `128`.

This is a statement about the constant the existing proof produces, not about the existential in
`contact_relative_unconditional`; no refutation of that statement is claimed. -/
theorem contact_relative_constant_too_large {b : ℝ} (hb : 0 ≤ b)
    (hr : coreRate (16 * 4) b < 1) :
    16 * lagTwoThreshold < coreConst (16 * 4) b := by
  have h1 := lagTwoThreshold_lt
  have h2 : (128 : ℝ) ≤ coreConst (16 * 4) b := le_coreConst (16 * 4) hb hr
  linarith

#print axioms contact_relative_constant_too_large

/-! ## 4. The ratio bound, PROVED, on a derived coupling interval -/

/-- **THE LAG-TWO RATIO BOUND ON `[0, b]`, AT ANY CONSTANT.** For every `K > 0` there is a cut
`b > 0` with

    wilsonCorrAt 3 β 2  ≤  K · wilsonCorrAt 3 β 0        for all `0 ≤ β ≤ b`.

The numerator is `StrongCoupling.corrClay_abs_le_coreConst_mul_rate_pow` at `k = 1`, admissible
because `circLag 2 = 2`, made coupling-uniform on the interval by `StrongArm.coreConst_mono_beta`.
The denominator is `ContactFloor.corrClay_zero_ge`, `e^{−128β}·ρ(0)|_{β=0} ≤ ρ(0)` at every `β ≥ 0`,
here read at the single extent four. The cut is whatever continuity of
`β ↦ coreRate(16·4, β)·e^{128β}` at its zero supplies inside `StrongArm.exists_strong_arm_cut`'s
interval: no numeral is named for it, and none could be, since `ρ(0)|_{β=0}` enters through
`PlaqVariance.corrClay_zero_pos`, which is non-constructive. -/
theorem exists_cut_lag_two_ratio (K : ℝ) (hK : 0 < K) :
    ∃ b : ℝ, 0 < b ∧ ∀ β : ℝ, 0 ≤ β → β ≤ b →
      MassGap.wilsonCorrAt 3 β 2 ≤ K * MassGap.wilsonCorrAt 3 β 0 := by
  obtain ⟨b₀, hb₀, hr₀⟩ := MassGap.StrongArm.exists_strong_arm_cut
  set A : ℝ := coreConst (16 * 4) b₀ with hAdef
  have hA128 : (128 : ℝ) ≤ A := by rw [hAdef]; exact le_coreConst (16 * 4) hb₀.le hr₀
  have hA0 : 0 < A := by linarith
  set D : ℝ := MassGap.WilsonBridge.corrClay (3 + 1) 0 0 with hDdef
  have hD0 : 0 < D := by rw [hDdef]; exact MassGap.PlaqVariance.corrClay_zero_pos 3 0
  have hcont : Continuous
      (fun β : ℝ => A * (coreRate (16 * 4) β * Real.exp (128 * β))) := by
    have h1 : Continuous (fun β : ℝ => Real.exp (128 * β)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    exact continuous_const.mul ((continuous_coreRate (16 * 4)).mul h1)
  have hzero : A * (coreRate (16 * 4) 0 * Real.exp (128 * 0)) < K * D := by
    rw [coreRate_at_zero]
    have hz : A * (0 * Real.exp (128 * 0)) = 0 := by ring
    rw [hz]
    exact mul_pos hK hD0
  have htend : Filter.Tendsto (fun β : ℝ => A * (coreRate (16 * 4) β * Real.exp (128 * β)))
      (nhds 0) (nhds (A * (coreRate (16 * 4) 0 * Real.exp (128 * 0)))) :=
    hcont.continuousAt
  have hev : ∀ᶠ x in nhds (0 : ℝ),
      A * (coreRate (16 * 4) x * Real.exp (128 * x)) < K * D :=
    htend.eventually_lt_const hzero
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨min b₀ (ε / 2), lt_min hb₀ (by linarith), ?_⟩
  intro β hβ0 hβb
  have hβb₀ : β ≤ b₀ := le_trans hβb (min_le_left _ _)
  have hβε : β < ε := lt_of_le_of_lt (le_trans hβb (min_le_right _ _)) (by linarith)
  have hf : A * (coreRate (16 * 4) β * Real.exp (128 * β)) < K * D := by
    refine hball ?_
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hβ0]
    exact hβε
  have hrβ : coreRate (16 * 4) β ≤ coreRate (16 * 4) b₀ :=
    MassGap.StrongArm.coreRate_mono_beta (16 * 4) hβ0 hβb₀
  have hrβ1 : coreRate (16 * 4) β < 1 := lt_of_le_of_lt hrβ hr₀
  have hrnn : (0 : ℝ) ≤ coreRate (16 * 4) β := coreRate_nonneg (16 * 4) hβ0
  have hAβ : coreConst (16 * 4) β ≤ A := by
    rw [hAdef]; exact MassGap.StrongArm.coreConst_mono_beta (16 * 4) hβ0 hβb₀ hr₀
  have hbnd := corrClay_abs_le_coreConst_mul_rate_pow 3 hβ0 hrβ1 (2 : Fin (3 + 1)) 1
    (by rw [circLag_two]; norm_num)
  have hstep : MassGap.wilsonCorrAt 3 β 2 ≤ A * coreRate (16 * 4) β := by
    rw [MassGap.StrongArm.wilsonCorrAt_eq_corrClay]
    calc MassGap.WilsonBridge.corrClay (3 + 1) β 2
        ≤ |MassGap.WilsonBridge.corrClay (3 + 1) β 2| := le_abs_self _
      _ ≤ coreConst (16 * 4) β * coreRate (16 * 4) β ^ 1 := hbnd
      _ = coreConst (16 * 4) β * coreRate (16 * 4) β := by ring
      _ ≤ A * coreRate (16 * 4) β := mul_le_mul_of_nonneg_right hAβ hrnn
  have hfloor : Real.exp (-(128 * β)) * D ≤ MassGap.wilsonCorrAt 3 β 0 := by
    rw [MassGap.StrongArm.wilsonCorrAt_eq_corrClay, hDdef]
    exact MassGap.ContactFloor.corrClay_zero_ge 3 hβ0
  have hcancel : Real.exp (128 * β) * Real.exp (-(128 * β)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hkey : A * coreRate (16 * 4) β ≤ K * (Real.exp (-(128 * β)) * D) := by
    have hmul : (A * (coreRate (16 * 4) β * Real.exp (128 * β))) * Real.exp (-(128 * β))
        ≤ (K * D) * Real.exp (-(128 * β)) :=
      mul_le_mul_of_nonneg_right hf.le (Real.exp_pos _).le
    have hlhs : (A * (coreRate (16 * 4) β * Real.exp (128 * β))) * Real.exp (-(128 * β))
        = A * coreRate (16 * 4) β := by
      calc (A * (coreRate (16 * 4) β * Real.exp (128 * β))) * Real.exp (-(128 * β))
          = A * coreRate (16 * 4) β * (Real.exp (128 * β) * Real.exp (-(128 * β))) := by ring
        _ = A * coreRate (16 * 4) β := by rw [hcancel, mul_one]
    have hrhs : (K * D) * Real.exp (-(128 * β)) = K * (Real.exp (-(128 * β)) * D) := by ring
    rw [hlhs, hrhs] at hmul
    exact hmul
  have hlast : K * (Real.exp (-(128 * β)) * D) ≤ K * MassGap.wilsonCorrAt 3 β 0 :=
    mul_le_mul_of_nonneg_left hfloor hK.le
  linarith

#print axioms exists_cut_lag_two_ratio

/-- **CONFINEMENT AT EXTENT FOUR BELOW A DERIVED CUT.** `3^{−1/4} < cosAvgEven ap4 β` for every
`β ≤ b`, with `b > 0` the cut `exists_cut_lag_two_ratio` produces at half the derived threshold. The
`1/2` is a device for strictness, not a magnitude: any constant strictly inside `lagTwoThreshold`
gives the same statement.

WHAT IS OPEN: `(b, ∞)`. See this file's header for why both quantitative inputs fail there. -/
theorem confines_below_derived_cut :
    ∃ b : ℝ, 0 < b ∧ ∀ β : ℝ, β ≤ b →
      (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven MassGap.ConfinesZero.ap4 β := by
  have hT := lagTwoThreshold_pos
  obtain ⟨b, hb, h⟩ := exists_cut_lag_two_ratio (lagTwoThreshold / 2) (by linarith)
  refine ⟨b, hb, fun β hβ => ?_⟩
  refine MassGap.ConfinesZero.confines_extent_four_of_lag_two_small β ?_
  exact lag_two_criterion_of_ratio (by linarith)
    (h (max β 0) (le_max_right β 0) (max_le hβ hb.le))

#print axioms confines_below_derived_cut

end MassGap.LagTwoBound
