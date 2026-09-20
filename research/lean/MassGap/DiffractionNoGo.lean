import MassGap.LagTwoSix

/-!
# MassGap.DiffractionNoGo — the diffraction ceiling cannot close B5, at either small even extent

`Moment.Read.substrate_lt_of_tension_lt_floor` caps the substrate ratio
`(∑ p_d circLag(d)²)/(N+1)²` at `(1 − 3^{−1/4})/8` whenever the tension clears the entropy floor,
and `Moment.Read.tension_ge_floor_of_substrate` is its contrapositive. This file settles what that
pair can do for `ApertureRoute.ConfinesAtAnAperture`, and the answer is nothing — including the
combination across two extents, the APERTURE DIFFERENTIAL, which is what this file was written to
investigate and which section 1.1 disposes of separately from sections 3 and 4.

## 1. The direction it runs in

`substrate_lt_of_tension_lt_floor` takes `R.tension < ¼log3` as a HYPOTHESIS, and by
`ApertureRoute.confines_iff_pos_and_tension_lt_floor` that hypothesis, together with the positivity
guard the theorem also requires, IS confinement at the aperture and coupling in question. So the
ceiling is a CONSEQUENCE of what B5 exists to establish, never an input to it.
`ceiling_of_confines_four` and `ceiling_of_confines_six` state that consequence in closed form; they
are recorded as what the diffraction bound gives, and they are the reason it cannot be used the other
way round.

### 1.1 The aperture differential, and why conjoining two extents changes nothing

The motivating idea was that the ceiling is a fixed number while the substrate is divided by `(N+1)²`
and `circLag` changes with extent, so ONE correlation read at extent four and at extent six faces TWO
different constraints, and the pair might give what neither gives alone. It does not, and the reason
is the shape of the target rather than the arithmetic of the two constraints.

`ApertureRoute.ConfinesAtAnAperture` is `∃ a : EvenAp, ∀ β, 3^{−1/4} < cosAvgEven a β` — EXISTENTIAL
over apertures. One confining aperture discharges it. Now put that beside section 1: every ceiling
instance carries `htens`, confinement at ITS OWN aperture, as a hypothesis. So the two horns are:

* confinement holds at some aperture — then `ConfinesAtAnAperture` is already discharged by that
  aperture, and the ceiling, at either extent or both, is redundant; or
* confinement holds at no aperture — then NO ceiling instance fires at ANY extent, so there is
  nothing to conjoin. The extent-four constraint and the extent-six constraint are both vacuously
  unavailable, and a conjunction of two unavailable premises is unavailable.

The differential therefore has no horn on which it can act, and this is independent of how the two
cleared inequalities in section 2 compare. Sections 3 and 4 are a SEPARATE and weaker result — they
show that even if one were handed the ceiling at a single extent as a free premise, it would still
not deliver the criterion. Neither section subsumes the other, and the differential is closed here
rather than there.

## 2. What the ceiling says, written out

The substrate ratio at extent four (`circLag = 0,1,2,1`) and at extent six (`circLag = 0,1,2,3,2,1`)
are `(2ρ(1)+4ρ(2))/(16·Z₄)` and `(2ρ(1)+8ρ(2)+9ρ(3))/(36·Z₆)`, with `Z₄ = ρ(0)+2ρ(1)+ρ(2)` and
`Z₆ = ρ(0)+2ρ(1)+2ρ(2)+ρ(3)` the reads' total masses. Clearing the denominators — inlined inside
`ceiling_of_confines_four` and `ceiling_of_confines_six`, which are one-directional implications
carrying their own `hpos` and `htens`, not biconditionals — turns `substrate < (1−3^{−1/4})/8` into
one linear inequality with no aperture in it. The clearing is exact at both extents:
`8·num₄ − 16(1−c)Z₄ = 16·[(2c−1)ρ(1) + (1+c)ρ(2) − (1−c)ρ(0)]` and
`8·num₆ − 36(1−c)Z₆ = 4·[(18c−14)ρ(1) + (18c−2)ρ(2) + 9(1+c)ρ(3) − 9(1−c)ρ(0)]`. The aperture is
absent from the result because `N` is pinned to `3` and `5` and the two cleared inequalities have
structurally different coefficients — `16` against `36` in the denominator, weights `2,4` against
`2,8,9` — so nothing cancels in the sense `Complete.surplus_ge`'s `hcancel` means, which is the
`(N+1)²` absorbed into the DEFINITION of the substrate ratio. With `c = 3^{−1/4}`:

    extent four:   (2c − 1)·ρ(1) + (1 + c)·ρ(2)                       <  (1 − c)·ρ(0)
    extent six:   (18c − 14)·ρ(1) + (18c − 2)·ρ(2) + 9(1 + c)·ρ(3)    <  9(1 − c)·ρ(0)

Set these beside `ConfinesSharp.confines_extent_four_iff` and `confines_extent_six_iff`:

    extent four:       2c·ρ(1) +          (1 + c)·ρ(2)               <  (1 − c)·ρ(0)
    extent six:   9(2c − 1)·ρ(1) + 9(1 + 2c)·ρ(2) + 9(1 + c)·ρ(3)     <  9(1 − c)·ρ(0)

No coefficient of the ceiling is LARGER, and three are strictly smaller: by `1` on `ρ(1)` at extent
four, and by `5` on `ρ(1)` and `11` on `ρ(2)` at extent six. On `ρ(2)` at extent four and on `ρ(3)` at
extent six the two agree exactly, at `1 + c` and `9(1 + c)`. Since the correlation is nonnegative,
that is enough: the criterion implies the ceiling and never the reverse
(`criterion_implies_ceiling_four`, `criterion_implies_ceiling_six`). It is not an accident of these
two extents. The ceiling is the criterion with each lag cosine `cos(πd/m)` replaced by the UPPER bound
`1 − 2d²/m²` — `cos x ≤ 1 − (2/π²)x²`, the one inequality `Moment.Read.cos_avg_le_circ` spends — and
replacing a cosine by something larger is exactly what makes the ceiling the weaker of the two.

## 3. The refutation

The gap between the two is not a margin to be tightened away; it admits profiles, and it admits them
against the FULL uniform premise set rather than a convenient subset of it.

**At extent four the geometric mode does NOT witness this, and that is worth stating because it is
the trap.** `ρ(d) = (1/5)^{circLag d}` clears the ceiling and fails the criterion, and it is
log-convex with equality — but `SlabQuadratic.wilson_quadratic` gives `2ρ(1)² ≤ ρ(2)² + ρ(0)ρ(2)` at
every real `β` with no hypothesis, and the geometric mode fails it, `2/25` against `26/625`, by a
factor `1.9231`. Log-convexity with equality is not enough at extent four; the quadratic binds
strictly harder and `SpectralFour.missing_inequalities_independent` says it does not follow from the
rest. The witness carried here is `(ρ(0), ρ(1), ρ(2)) = (1, 4/25, 1/20)`, which satisfies all four
conjuncts of `SpectralFour.FourRepresentable` and still refutes.

At extent six the geometric mode `(1/4)^{circLag d}` — that is `(1, 1/4, 1/16, 1/64, 1/16, 1/4)` —
does witness it, at a lag-two ratio of `1/16` above `LagTwoSix.lagTwoThresholdSix`, and it survives
the extent-six facts as well: it is `Hankel`-PSD on levels `{0,1,2}` (sitting on the boundary, with
two vanishing minors), and it meets `MomentShape.corrClay_even_antitone`,
`WeakArm.wilsonCorrAt_le_at_zero` and `LagTwoSix.lag_three_le_lag_two`. The tree states no quadratic
and no `ρ(2) ≤ ρ(1)` at aperture five, so nothing there bites the way the extent-four quadratic does.

The size of the shortfall, computed rather than proved here. Holding `ρ(1)` at the quadratic's own
boundary `ρ(1) = √((ρ(2)² + ρ(2))/2)`, the extent-four window in which the ceiling HOLDS and the
criterion FAILS is `ρ(2)/ρ(0) ∈ (0.029696, 0.076534)` — nonempty, with the chosen `1/20` inside it.
The ceiling's own lag-two bar is therefore `0.076534`, a factor `2.577` above the criterion's
`0.029696` and `4.109` above `lagTwoThreshold = 0.0186240`. At extent six, on the geometric family,
the criterion's root is `0.211990` and the ceiling's is `0.361779`, and the chosen `1/4` lies between
them.

## 4. What this does NOT claim

It does not claim the substrate route is useless. The route that runs the other way,
`Moment.Read.tension_lt_floor_of_circ_moment` and `Complete.confinement_at_of_substrate_sharp`, is
sound and gives confinement from a substrate ratio below `substrateThreshold = arccos(3^{−1/4})²/(2π)²
≈ 0.0126877`. Reduced to a lag-two statement, that SUFFICIENT threshold is `0.0104826` at extent four
against the geometric cone `(1, v, v²)`, and `0.0195132` at extent six against the flat-tail cone
`(1, v, v², v²)` — the cone `lagTwoThresholdSix` itself uses, not the one behind `lagTwoThreshold`.
Both sit below the exact criterion's `0.0186240` and `0.0337959`, so it is the weaker route at both
extents, and it stays weaker at extent six under the geometric cone too (`0.0309317 < 0.0337959`).
Those numbers are computed, not proved here; the two exact ones are `LagTwoBound` and `LagTwoSix`'s
own.

Nor does it refute anything about the massless configuration: `Read.tension_ge_floor_of_substrate`
genuinely excludes a substrate ratio at or above the ceiling, which is a refutation tool and is used
as one. The statement here is only that a refutation tool does not establish.

## 5. The obligation is unchanged

`LagTwoSix.LagTwoRatioSix` remains the target and no new reduction is minted: a lag-two ratio bound
`ρ(2) ≤ K·ρ(0)` at every nonnegative coupling with `K < lagTwoThresholdSix`. Nothing below weakens it
and nothing below supplies it.

DERIVED throughout: `c = 3^{−1/4} = e^{−κ₀}` with `κ₀ = ¼log3` counted off directed cube paths in
`Floor.lean`; `8` is the constant of `Moment.Read.cos_avg_le_circ`; `16` and `36` are the squared
extents `4²` and `6²`; the lag weights `1, 4, 9` are `Moment.circLag` squared at those extents; `9`
is `36/4`, the extent-six denominator's surviving factor after the clearing divides through by `4`.
The witnesses are CHOSEN — any point strictly inside the refuting window works, they are round
rationals inside it, and `not_ceilingClosesFour` / `not_ceilingClosesSix` are existentials, so no
magnitude is asserted. The windows are NOT the same kind of object at the two extents and are not
quoted as one:

* **extent four**, on the triple with `ρ(1)` at the quadratic boundary: `ρ(2)/ρ(0) ∈ (0.029696,
  0.076534)`, and `1/20 = 0.05` is inside. The geometric family is not used here at all, because the
  quadratic excludes it — see section 3.
* **extent six**, on the geometric family `ρ(d) = λ^{circLag d}`: `λ ∈ (0.211990, 0.361779)`, the
  criterion's root and the ceiling's root on that family, and `1/4` is inside.

`LagTwoSix.vSix = 0.183837` is NOT an endpoint of either window. It is the criterion's root on the
FLAT-TAIL profile `(1, v, v², v²)`, a different family from the geometric one the extent-six witness
comes from, and quoting it here would be comparing two profiles as though they were one.

Foundational footprint only (`#print axioms` on every declaration, and again in the audit section).
Build: `python research/code/lean_build.py build MassGap.DiffractionNoGo`.
-/

namespace MassGap.DiffractionNoGo

open scoped BigOperators

/-! ## 0. The circle distances at the two smallest even extents -/

/-- `circLag` at extent four: `0, 1, 2, 1`. Machine-checked, not asserted. -/
theorem clag_four :
    Moment.circLag (0 : Fin (3 + 1)) = 0 ∧ Moment.circLag (1 : Fin (3 + 1)) = 1 ∧
      Moment.circLag (2 : Fin (3 + 1)) = 2 ∧ Moment.circLag (3 : Fin (3 + 1)) = 1 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

#print axioms clag_four

/-- `circLag` at extent six: `0, 1, 2, 3, 2, 1`. -/
theorem clag_six :
    Moment.circLag (0 : Fin (5 + 1)) = 0 ∧ Moment.circLag (1 : Fin (5 + 1)) = 1 ∧
      Moment.circLag (2 : Fin (5 + 1)) = 2 ∧ Moment.circLag (3 : Fin (5 + 1)) = 3 ∧
      Moment.circLag (4 : Fin (5 + 1)) = 2 ∧ Moment.circLag (5 : Fin (5 + 1)) = 1 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

#print axioms clag_six

/-! ## 1. The read's mass and second moment in closed form -/

/-- The total mass at extent four, folded by circle symmetry. -/
theorem rho_sum_four (R : Moment.Read 3) (hsym : R.ρ 3 = R.ρ 1) :
    ∑ d, R.ρ d = R.ρ 0 + 2 * R.ρ 1 + R.ρ 2 := by
  rw [Fin.sum_univ_four, hsym]; ring

#print axioms rho_sum_four

/-- The circle second moment at extent four: weights `0, 1, 4, 1`. -/
theorem rho_moment_four (R : Moment.Read 3) (hsym : R.ρ 3 = R.ρ 1) :
    ∑ d, R.ρ d * (Moment.circLag d : ℝ) ^ 2 = 2 * R.ρ 1 + 4 * R.ρ 2 := by
  obtain ⟨h0, h1, h2, h3⟩ := clag_four
  rw [Fin.sum_univ_four, h0, h1, h2, h3, hsym]
  push_cast
  ring

#print axioms rho_moment_four

/-- The substrate ratio's numerator at extent four, in the read's own probability weights. -/
theorem substrate_num_four (R : Moment.Read 3) (hsym : R.ρ 3 = R.ρ 1) :
    ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2
      = (2 * R.ρ 1 + 4 * R.ρ 2) / (R.ρ 0 + 2 * R.ρ 1 + R.ρ 2) := by
  have hsplit : ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2
      = (∑ d, R.ρ d * (Moment.circLag d : ℝ) ^ 2) / (∑ d, R.ρ d) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    simp only [Moment.Read.p]
    ring
  rw [hsplit, rho_moment_four R hsym, rho_sum_four R hsym]

#print axioms substrate_num_four

/-- The total mass at extent six, folded by circle symmetry. -/
theorem rho_sum_six (R : Moment.Read 5) (hs1 : R.ρ 5 = R.ρ 1) (hs2 : R.ρ 4 = R.ρ 2) :
    ∑ d, R.ρ d = R.ρ 0 + 2 * R.ρ 1 + 2 * R.ρ 2 + R.ρ 3 := by
  rw [Fin.sum_univ_six, hs1, hs2]; ring

#print axioms rho_sum_six

/-- The circle second moment at extent six: weights `0, 1, 4, 9, 4, 1`. -/
theorem rho_moment_six (R : Moment.Read 5) (hs1 : R.ρ 5 = R.ρ 1) (hs2 : R.ρ 4 = R.ρ 2) :
    ∑ d, R.ρ d * (Moment.circLag d : ℝ) ^ 2
      = 2 * R.ρ 1 + 8 * R.ρ 2 + 9 * R.ρ 3 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := clag_six
  rw [Fin.sum_univ_six, h0, h1, h2, h3, h4, h5, hs1, hs2]
  push_cast
  ring

#print axioms rho_moment_six

/-- The substrate ratio's numerator at extent six, in the read's own probability weights. -/
theorem substrate_num_six (R : Moment.Read 5) (hs1 : R.ρ 5 = R.ρ 1) (hs2 : R.ρ 4 = R.ρ 2) :
    ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2
      = (2 * R.ρ 1 + 8 * R.ρ 2 + 9 * R.ρ 3)
          / (R.ρ 0 + 2 * R.ρ 1 + 2 * R.ρ 2 + R.ρ 3) := by
  have hsplit : ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2
      = (∑ d, R.ρ d * (Moment.circLag d : ℝ) ^ 2) / (∑ d, R.ρ d) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    simp only [Moment.Read.p]
    ring
  rw [hsplit, rho_moment_six R hs1 hs2, rho_sum_six R hs1 hs2]

#print axioms substrate_num_six

/-! ## 2. THE DIFFRACTION CEILING IS A CONSEQUENCE OF CONFINEMENT, NOT AN INPUT TO IT

Both theorems below carry `R.tension < ¼log3` as a hypothesis. By
`ApertureRoute.confines_iff_pos_and_tension_lt_floor` that hypothesis together with the positivity
guard is exactly the confinement condition at the aperture, so these state what confinement GIVES.
Using them to obtain confinement would assume the conclusion. -/

/-- **WHAT THE DIFFRACTION CEILING GIVES AT EXTENT FOUR**, in closed form.

`Moment.Read.substrate_lt_of_tension_lt_floor` with the extent-four substrate ratio substituted and
the denominator cleared. Read the hypotheses: a tension below the floor and a positive cosine
average, which is confinement at this aperture.

DERIVED: `16` is `4²`, the squared extent; `8` is the constant of `Moment.Read.cos_avg_le_circ`; the
coefficients `2c − 1`, `1 + c` and `1 − c` come out of clearing `Z₄ = ρ(0)+2ρ(1)+ρ(2)`. -/
theorem ceiling_of_confines_four (R : Moment.Read 3) (hsym : R.ρ 3 = R.ρ 1)
    (hpos : 0 < ∑ d, R.p d * Real.cos (R.θ d))
    (htens : R.tension < (1 / 4) * Real.log 3) :
    (2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1) * R.ρ 1
        + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * R.ρ 2
      < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * R.ρ 0 := by
  have hcap := R.substrate_lt_of_tension_lt_floor hpos htens
  have hZ0 : (0 : ℝ) < R.ρ 0 + 2 * R.ρ 1 + R.ρ 2 := by
    rw [← rho_sum_four R hsym]; exact R.hpos
  rw [substrate_num_four R hsym, div_div,
    div_lt_div_iff₀ (mul_pos hZ0 (by positivity)) (by norm_num : (0 : ℝ) < 8)] at hcap
  norm_num at hcap
  nlinarith [hcap]

#print axioms ceiling_of_confines_four

/-- **WHAT THE DIFFRACTION CEILING GIVES AT EXTENT SIX**, in closed form, cleared of ninths.

DERIVED: `36` is `6²`; `9` is that denominator's surviving factor after dividing through by `4`, not
a magnitude; the lag weights `1, 4, 9` are `circLag²`. -/
theorem ceiling_of_confines_six (R : Moment.Read 5) (hs1 : R.ρ 5 = R.ρ 1) (hs2 : R.ρ 4 = R.ρ 2)
    (hpos : 0 < ∑ d, R.p d * Real.cos (R.θ d))
    (htens : R.tension < (1 / 4) * Real.log 3) :
    (18 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 14) * R.ρ 1
        + (18 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 2) * R.ρ 2
        + (9 + 9 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * R.ρ 3
      < (9 - 9 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * R.ρ 0 := by
  have hcap := R.substrate_lt_of_tension_lt_floor hpos htens
  have hZ0 : (0 : ℝ) < R.ρ 0 + 2 * R.ρ 1 + 2 * R.ρ 2 + R.ρ 3 := by
    rw [← rho_sum_six R hs1 hs2]; exact R.hpos
  rw [substrate_num_six R hs1 hs2, div_div,
    div_lt_div_iff₀ (mul_pos hZ0 (by positivity)) (by norm_num : (0 : ℝ) < 8)] at hcap
  norm_num at hcap
  nlinarith [hcap]

#print axioms ceiling_of_confines_six

/-! ## 3. The ceiling is implied by the exact criterion, and is therefore never stronger -/

/-- **THE EXACT CRITERION IMPLIES THE CEILING AT EXTENT FOUR.** The criterion is
`ConfinesSharp.confines_extent_four_iff`'s right-hand side; the ceiling differs from it only by
carrying `2c − 1` where the criterion carries `2c`, so a nonnegative first lag settles it.

Consequence: the ceiling can never decide a case the criterion does not already decide. -/
theorem criterion_implies_ceiling_four {r₀ r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁)
    (h : 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) * r₁ + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₂
        < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀) :
    (2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1) * r₁ + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₂
      < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀ := by
  nlinarith [h, h₁]

#print axioms criterion_implies_ceiling_four

/-- **THE EXACT CRITERION IMPLIES THE CEILING AT EXTENT SIX.** Here the criterion carries `9(2c−1)`
and `9(1+2c)` where the ceiling carries `18c − 14` and `18c − 2`: the ceiling is short by `5` on the
first lag and by `11` on the second, so two nonnegative lags settle it. -/
theorem criterion_implies_ceiling_six {r₀ r₁ r₂ r₃ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂)
    (h : (2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1) * r₁
          + (1 + 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₂
          + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₃
        < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀) :
    (18 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 14) * r₁
        + (18 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 2) * r₂
        + (9 + 9 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₃
      < (9 - 9 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀ := by
  nlinarith [h, h₁, h₂]

#print axioms criterion_implies_ceiling_six

/-! ## 4. THE REFUTATION: the ceiling does not imply the criterion, at either extent

`CeilingClosesFour` and `CeilingClosesSix` are the single-extent implications a diffraction argument
would have to supply — the ceiling, plus the uniform facts the tree proves at that extent, delivering
the exact criterion. Both are refuted.

What is and is not granted, stated so the strength of each refutation is readable. At extent four the
premise list is `SpectralFour.FourRepresentable` in full, which is everything the tree proves of the
extent-four triple at `β ≥ 0`, so the refutation there is against the complete set. At extent six the
premise list is `MomentShape.Shape 6 3`'s three non-trivial instances; the witness additionally
satisfies `ShapeNoGo`'s `Hankel` 3×3 PSD condition, `MomentShape.corrClay_even_antitone`,
`WeakArm.wilsonCorrAt_le_at_zero` and `LagTwoSix.lag_three_le_lag_two`, checked numerically rather
than carried as premises, so granting those too would not rescue the implication.

These refutations are NOT what closes the aperture differential — section 1.1 does that, and does it
for a different reason. -/

/-- The implication a diffraction argument would have to supply at extent four: the ceiling, together
with EVERY coupling-uniform fact the tree proves of the extent-four triple, giving the exact
criterion.

The premise list is `SpectralFour.FourRepresentable` verbatim — nonnegativity, `ρ(2) ≤ ρ(1)`, the
log-convexity instance `ρ(1)² ≤ ρ(0)ρ(2)`, and the quadratic `2ρ(1)² ≤ ρ(2)² + ρ(0)ρ(2)` — and that
is deliberate: `SlabQuadratic.wilsonSpectral` discharges all four at every `β ≥ 0`, so an implication
refuted against THIS list is refuted against everything a diffraction argument may help itself to.
Granting less would refute a weaker implication and prove nothing about the route.

`MomentShape.Shape 4 2` alone supplies only the third of the four. `LinkGram.wilson_lag_two_le_lag_one`
supplies the second and `SlabQuadratic.wilson_quadratic` the fourth, and the fourth is INDEPENDENT of
the others — `SpectralFour.missing_inequalities_independent` — so omitting it is not harmless.

DERIVED: no literal here is chosen and none is a level. `3`, `1` and `4` are the floor `c = 3^{−1/4}`
carried in by name from `Floor.lean`. The `2` in `2c` and in `2r₁²` is the criterion's own coefficient
on `ρ(1)`, which `SpectralFour.FourRepresentable` also carries; `1 ± c` are the criterion's remaining
coefficients and `2c−1` is the ceiling's, from section 2's clearing of
`(2ρ(1)+4ρ(2))/(16·Z₄)` in which `16 = 4²` is the squared extent and `2, 4` are `Moment.circLag`
squared. `0` is a sign and the exponent `2` is a square. -/
def CeilingClosesFour : Prop :=
  ∀ r₀ r₁ r₂ : ℝ, 0 < r₀ → 0 ≤ r₁ → 0 ≤ r₂ → r₁ ^ 2 ≤ r₀ * r₂ →
    r₂ ≤ r₁ → 2 * r₁ ^ 2 ≤ r₂ ^ 2 + r₀ * r₂ →
    ((2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1) * r₁ + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₂
      < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀) →
    (2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) * r₁ + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₂
      < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀)

#print axioms CeilingClosesFour

/-- **THE CEILING DOES NOT CLOSE B5 AT EXTENT FOUR, and the witness satisfies every uniform fact.**

The triple `(ρ(0), ρ(1), ρ(2)) = (1, 4/25, 1/20)` is `FourRepresentable` — nonnegative,
`ρ(2) ≤ ρ(1)`, log-convex (`16/625 ≤ 1/20`), and inside the quadratic with `32/625 ≤ 21/400`. It
clears the diffraction ceiling and fails the exact criterion outright, at a lag-two ratio of `1/20`,
more than TWICE `LagTwoBound.lagTwoThreshold`.

So the ceiling is not a bound that needs sharpening; it admits the very configurations B5 has to
exclude. Note what the witness is NOT: it is not a slow mode. `ZeroMode.lam_pow_lt_of_tension` asks
`λ^{n/2} < 0.360246`, and this triple's lag-two ratio is `0.05`, inside that by a factor above seven.
The ceiling and the criterion are simply different bars.

**THE GEOMETRIC MODE DOES NOT WORK HERE, and the reason is the point.** `ρ(d) = (1/5)^{circLag d}`
clears the ceiling and fails the criterion, but it VIOLATES `SlabQuadratic.wilson_quadratic`:
`2(1/5)² = 2/25` against `(1/25)² + 1·(1/25) = 26/625`, false by a factor `1.9231`. So it is not a
possible Wilson correlation at any `β`, and refuting the implication with it would refute a strawman.
Log-convexity with equality is NOT enough at extent four; the quadratic is the binding constraint and
it is not implied by the other three.

DERIVED: `4/25` is the largest `ρ(1)` the quadratic permits at `ρ(2) = 1/20` rounded DOWN to a
rational — `√(21/800) = 0.1620`, so `0.16` sits inside with `32/625 ≤ 21/400` to spare, and rounding
down rounds AGAINST the refutation. CHOSEN: `1/20` for `ρ(2)`, a round rational inside the refuting
window `(0.0296959, 0.0765343)` that the quadratic arm opens; the statement is an existential, so no
magnitude is asserted. -/
theorem not_ceilingClosesFour : ¬ CeilingClosesFour := by
  intro h
  have hc := MassGap.LagTwoBound.floor_bounds
  have hceil : (2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1) * (4 / 25)
        + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * (1 / 20)
      < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * 1 := by
    linarith [hc.1, hc.2]
  have := h 1 (4 / 25) (1 / 20) one_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hceil
  linarith [hc.1, hc.2]

#print axioms not_ceilingClosesFour

/-- **THE WITNESS, AS AN EXISTENTIAL, WITH ITS LAG-TWO RATIO.** The same profile, stated so the
number that matters is visible: it satisfies the diffraction ceiling, fails the exact criterion, and
its lag-two ratio is above TWICE the threshold B5 needs. `LagTwoBound.lagTwoThreshold_lt` supplies
the comparison.

The triple is carried with its FULL `FourRepresentable` premise set, so the existential asserts a
configuration the Wilson correlation could actually take, not merely one the ceiling fails to reach.

DERIVED: `1/20` is the lag-two ratio, since `ρ(0) = 1`. The `2` is the factor being reported, not a
chosen tolerance. -/
theorem ceiling_admits_lag_two_above_threshold :
    ∃ r₀ r₁ r₂ : ℝ, 0 < r₀ ∧ 0 ≤ r₁ ∧ 0 ≤ r₂ ∧ r₁ ^ 2 ≤ r₀ * r₂ ∧
      r₂ ≤ r₁ ∧ 2 * r₁ ^ 2 ≤ r₂ ^ 2 + r₀ * r₂ ∧
      ((2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1) * r₁ + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₂
        < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀) ∧
      ¬ (2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) * r₁ + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₂
        < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀) ∧
      2 * MassGap.LagTwoBound.lagTwoThreshold < r₂ / r₀ := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have hT := MassGap.LagTwoBound.lagTwoThreshold_lt
  refine ⟨1, 4 / 25, 1 / 20, one_pos, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, ?_, ?_, ?_⟩
  · linarith [hc.1, hc.2]
  · rw [not_lt]; linarith [hc.1, hc.2]
  · rw [show (1 : ℝ) / 20 / 1 = 1 / 20 by norm_num]; linarith [hT]

#print axioms ceiling_admits_lag_two_above_threshold

/-- `lagTwoThresholdSix < 1/16`, from `LagTwoSix.vSix_root` alone. Needed to say where the extent-six
witness sits relative to the bar; the true value is `0.0337959`, so this is a loose bracket used only
for a comparison, and it rounds AWAY from the claim.

DERIVED: `1/16` is the extent-six witness rate `1/4` squared. Nothing is fitted. -/
theorem lagTwoThresholdSix_lt_sixteenth : MassGap.LagTwoSix.lagTwoThresholdSix < 1 / 16 := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have hroot := MassGap.LagTwoSix.vSix_root
  have hv0 := MassGap.LagTwoSix.vSix_pos
  have hv : MassGap.LagTwoSix.vSix < 1 / 4 := by
    nlinarith [hroot, hv0, hc.1, hc.2]
  rw [MassGap.LagTwoSix.lagTwoThresholdSix]
  nlinarith [hv, hv0]

#print axioms lagTwoThresholdSix_lt_sixteenth

/-- The implication a diffraction argument would have to supply at extent six. The three
log-convexity instances are the ones `LagTwoSix.lagTwoThresholdSix_sharp` exhibits at half-extent
three — `(0,1)`, `(0,2)` and `(1,2)`, the last two folded through `ρ(4) = ρ(2)`.

DERIVED: no literal here is chosen and none is a level. `3`, `1` and `4` are the floor `c = 3^{−1/4}`
carried in by name from `Floor.lean`. `18`, `14`, `2` and `9` are the extent-six ceiling's cleared
coefficients — `(18c−14)`, `(18c−2)`, `9(1+c)` and `9(1−c)` — produced by section 2's denominator
clearing from the substrate ratio `(2ρ(1)+8ρ(2)+9ρ(3))/(36·Z₆)`, in which `36 = 6²` is the squared
extent and `2, 8, 9` are `Moment.circLag` squared; the `9` here is `36/4`, that denominator's
surviving factor after the clearing divides through by `4`. `0` is a sign and the exponent `2` is a
square. -/
def CeilingClosesSix : Prop :=
  ∀ r₀ r₁ r₂ r₃ : ℝ, 0 < r₀ → 0 ≤ r₁ → 0 ≤ r₂ → 0 ≤ r₃ →
    r₁ ^ 2 ≤ r₀ * r₂ → r₂ ^ 2 ≤ r₀ * r₂ → r₃ ^ 2 ≤ r₂ ^ 2 →
    ((18 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 14) * r₁
        + (18 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 2) * r₂
        + (9 + 9 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₃
      < (9 - 9 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀) →
    ((2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1) * r₁
        + (1 + 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₂
        + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₃
      < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀)

#print axioms CeilingClosesSix

/-- **THE CEILING DOES NOT CLOSE B5 AT EXTENT SIX EITHER.** The witness is the geometric mode
`(1/4)^{circLag d}`, that is `(1, 1/4, 1/16, 1/64)`, which meets all three log-convexity instances
available at half-extent three (the first with equality) and sits at a lag-two ratio of `1/16`, above
`lagTwoThresholdSix` by `lagTwoThresholdSix_lt_sixteenth`.

The extent-six relief `LagTwoSix.lagTwoThreshold_lt_lagTwoThresholdSix` reports — a factor `1.81` on
the bar — therefore does not come from the ceiling and is not enlarged by it.

CHOSEN: `1/4`, a round number inside `(0.211990, 0.361779)` — the criterion's root and the ceiling's
root on the GEOMETRIC family `ρ(d) = λ^{circLag d}`, which is the family this witness belongs to. Both
endpoints are roots of cubics in `λ`: `(2c−1)λ + (1+2c)λ² + (1+c)λ³ = 1−c` for the criterion and
`(18c−14)λ + (18c−2)λ² + 9(1+c)λ³ = 9(1−c)` for the ceiling. `LagTwoSix.vSix = 0.183837` is the
criterion's root on the FLAT-TAIL family `(1, v, v², v²)` and is not an endpoint here. The statement
is an existential. -/
theorem not_ceilingClosesSix : ¬ CeilingClosesSix := by
  intro h
  have hc := MassGap.LagTwoBound.floor_bounds
  have hceil : (18 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 14) * (1 / 4)
        + (18 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 2) * (1 / 16)
        + (9 + 9 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * (1 / 64)
      < (9 - 9 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * 1 := by
    linarith [hc.1, hc.2]
  have := h 1 (1 / 4) (1 / 16) (1 / 64) one_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hceil
  linarith [hc.1, hc.2]

#print axioms not_ceilingClosesSix

/-- **THE EXTENT-SIX WITNESS, AS AN EXISTENTIAL, WITH ITS LAG-TWO RATIO.** -/
theorem ceiling_admits_lag_two_above_threshold_six :
    ∃ r₀ r₁ r₂ r₃ : ℝ, 0 < r₀ ∧ 0 ≤ r₁ ∧ 0 ≤ r₂ ∧ 0 ≤ r₃ ∧
      r₁ ^ 2 ≤ r₀ * r₂ ∧ r₂ ^ 2 ≤ r₀ * r₂ ∧ r₃ ^ 2 ≤ r₂ ^ 2 ∧
      ((18 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 14) * r₁
          + (18 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 2) * r₂
          + (9 + 9 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₃
        < (9 - 9 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀) ∧
      ¬ ((2 * (3 : ℝ) ^ (-(1 : ℝ) / 4) - 1) * r₁
          + (1 + 2 * (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₂
          + (1 + (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₃
        < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * r₀) ∧
      MassGap.LagTwoSix.lagTwoThresholdSix < r₂ / r₀ := by
  have hc := MassGap.LagTwoBound.floor_bounds
  have hT := lagTwoThresholdSix_lt_sixteenth
  refine ⟨1, 1 / 4, 1 / 16, 1 / 64, one_pos, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · linarith [hc.1, hc.2]
  · rw [not_lt]; linarith [hc.1, hc.2]
  · rw [show (1 : ℝ) / 16 / 1 = 1 / 16 by norm_num]; exact hT

#print axioms ceiling_admits_lag_two_above_threshold_six

/-! ## 5. Footprints -/

section Audit
#print axioms clag_four
#print axioms clag_six
#print axioms rho_sum_four
#print axioms rho_moment_four
#print axioms substrate_num_four
#print axioms rho_sum_six
#print axioms rho_moment_six
#print axioms substrate_num_six
#print axioms ceiling_of_confines_four
#print axioms ceiling_of_confines_six
#print axioms criterion_implies_ceiling_four
#print axioms criterion_implies_ceiling_six
#print axioms CeilingClosesFour
#print axioms not_ceilingClosesFour
#print axioms ceiling_admits_lag_two_above_threshold
#print axioms lagTwoThresholdSix_lt_sixteenth
#print axioms CeilingClosesSix
#print axioms not_ceilingClosesSix
#print axioms ceiling_admits_lag_two_above_threshold_six
end Audit

end MassGap.DiffractionNoGo
