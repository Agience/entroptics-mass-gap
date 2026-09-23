import Mathlib
import MassGap.Forgetting

/-!
# MassGap.CertifiedGap — an attenuation bound that survives a stated numerical band

`entroptics.reads.attenuation_interval` computes, from a correlation matrix and an upper bound
`band` on `‖C_read − C_true‖₂`, an interval `[α_lo, α_hi]` for the attenuation
`α = log λ₁ − log(max λ₂ edge)`, and reports `certified = α_lo > 0`. This module states the
arithmetic of that report in Lean.

Throughout, unprimed `lam1`, `lam2` are the read eigenvalues, primed `lam1'`, `lam2'` are the true
ones, `d` is the band, and `edge` is a strictly positive noise floor supplied by the caller. Every
declaration carries `hedge : 0 < edge`.

## What the declarations state

* `attenuation lam1 lam2 edge` is `Real.log lam1 - Real.log (max lam2 edge)`.
* `attenuation_ge_of_band` — from `|lam1' - lam1| ≤ d`, `|lam2' - lam2| ≤ d` and `0 < lam1 - d`, the
  true attenuation is at least `attenuation (lam1 - d) (lam2 + d) edge`, the endpoint computed from
  the read. Monotonicity of `Real.log` in the numerator and against it in the denominator.
* `certificate_iff_arith` — under `0 < edge` and `0 < lam1`, `0 < attenuation lam1 lam2 edge` is
  equivalent to `max lam2 edge < lam1`, so checking the certificate evaluates no logarithm.
* `attenuation_pos_of_certified` — the previous two composed: the arithmetic check at the read's
  endpoints gives `0 < attenuation lam1' lam2' edge`.
* `ratio_lt_one_of_certified` and `ratio_nonneg` — the same certificate as
  `0 ≤ max lam2' edge / lam1' < 1`, the shape `Forgetting.forgets_of_margin` consumes.
* `forgets_of_certified_gap` and `bridge_of_certified_gap` — that margin passed to
  `MassGap.forgets_of_margin` and `MassGap.bridge_forward` for a finite mode sum
  `τ ↦ ∑ k ∈ s, P k * μ k ^ τ`.
* `certificate_fails_when_band_swallows_gap` — `lam1 - d ≤ max (lam2 + d) edge` implies the negation
  of the certificate. It is `not_lt.mpr`, generic on a linear order; it exhibits no values at which
  the hypothesis holds.

## Hypotheses this module does not prove

Weyl's inequality is not proved here: the band appears only as the hypotheses
`|lam1' - lam1| ≤ d` and `|lam2' - lam2| ≤ d`, which a caller must supply. The step from the spectral
ratio to the individual modes is likewise a hypothesis, `hmodes : ∀ k ∈ s, ‖μ k‖ ≤ max lam2' edge / lam1'`,
and is a statement about the model rather than about the arithmetic here. Nothing in this module
concerns the provenance of the band, so a band that is a confidence statement yields a conclusion of
that status and a band that is an arithmetic error bound yields one of that status.

DERIVED: the numerals in the statements are `0` — the positivity thresholds on `edge`, `lam1`,
`lam1 - d` and the attenuation, the nonnegativity of the margin, and the limit point in
`bridge_of_certified_gap` — and `1`, the value the contraction factor must fall strictly below.
-/

namespace MassGap.CertifiedGap

open Filter Topology

/-- The attenuation of a spectral read: `Real.log lam1 - Real.log (max lam2 edge)`, the log-ratio of
the top eigenvalue to the larger of the second eigenvalue and the noise edge. Defined for all real
arguments; no positivity is imposed at the definition, so the lemmas below carry it as hypotheses.

DERIVED: no numeral appears in the statement. `edge` is the caller's floor and `lam1`, `lam2` are
the read's own values. -/
noncomputable def attenuation (lam1 lam2 edge : ℝ) : ℝ :=
  Real.log lam1 - Real.log (max lam2 edge)

#print axioms attenuation

/-- The band propagates to the attenuation. Given `0 < edge`, `0 < lam1 - d` and the two band
hypotheses `|lam1' - lam1| ≤ d`, `|lam2' - lam2| ≤ d`, the conclusion is
`attenuation (lam1 - d) (lam2 + d) edge ≤ attenuation lam1' lam2' edge`: the true attenuation is at
least the endpoint computed from the read's values shifted by the band.

The proof uses only one side of each band hypothesis — `lam1 - d ≤ lam1'` and `lam2' ≤ lam2 + d` —
together with `Real.log_le_log` and `max_le_max`. `0 < edge` is what makes both logarithm arguments
positive.

DERIVED: `0` is the positivity threshold on `edge` and on `lam1 - d`; `d` is the caller's band. -/
theorem attenuation_ge_of_band {lam1 lam2 lam1' lam2' edge d : ℝ}
    (hedge : 0 < edge) (hpos : 0 < lam1 - d)
    (h1 : |lam1' - lam1| ≤ d) (h2 : |lam2' - lam2| ≤ d) :
    attenuation (lam1 - d) (lam2 + d) edge ≤ attenuation lam1' lam2' edge := by
  unfold attenuation
  have h1' : lam1 - d ≤ lam1' := by
    have := (abs_le.mp h1).1
    linarith
  have h2' : lam2' ≤ lam2 + d := by
    have := (abs_le.mp h2).2
    linarith
  have hnum : Real.log (lam1 - d) ≤ Real.log lam1' :=
    Real.log_le_log hpos h1'
  have hden : Real.log (max lam2' edge) ≤ Real.log (max (lam2 + d) edge) := by
    refine Real.log_le_log (lt_of_lt_of_le hedge (le_max_right _ _)) ?_
    exact max_le_max h2' le_rfl
  linarith

#print axioms attenuation_ge_of_band

/-- Positivity of the attenuation is an inequality between the numbers themselves. Under
`0 < edge` and `0 < lam1`, `0 < attenuation lam1 lam2 edge ↔ max lam2 edge < lam1`. It is
`sub_pos` followed by `Real.log_lt_log_iff`, whose two positivity side conditions are exactly the
hypotheses. Checking the right-hand side evaluates no logarithm.

DERIVED: `0` is the positivity threshold on `edge`, on `lam1`, and the level the attenuation is
compared against. -/
theorem certificate_iff_arith {lam1 lam2 edge : ℝ} (hedge : 0 < edge) (hlam1 : 0 < lam1) :
    0 < attenuation lam1 lam2 edge ↔ max lam2 edge < lam1 := by
  unfold attenuation
  rw [sub_pos]
  exact Real.log_lt_log_iff (lt_of_lt_of_le hedge (le_max_right _ _)) hlam1

#print axioms certificate_iff_arith

/-- The arithmetic check at the read's endpoints gives a positive true attenuation. From `0 < edge`,
`0 < lam1 - d`, the certificate `max (lam2 + d) edge < lam1 - d`, and the two band hypotheses, the
conclusion is `0 < attenuation lam1' lam2' edge`. It is `certificate_iff_arith` at the shifted
endpoints composed with `attenuation_ge_of_band`.

DERIVED: `0` is the positivity threshold on `edge` and on `lam1 - d`, and the level the true
attenuation is shown to exceed. -/
theorem attenuation_pos_of_certified {lam1 lam2 lam1' lam2' edge d : ℝ}
    (hedge : 0 < edge) (hpos : 0 < lam1 - d)
    (hcert : max (lam2 + d) edge < lam1 - d)
    (h1 : |lam1' - lam1| ≤ d) (h2 : |lam2' - lam2| ≤ d) :
    0 < attenuation lam1' lam2' edge :=
  lt_of_lt_of_le ((certificate_iff_arith hedge hpos).mpr hcert)
    (attenuation_ge_of_band hedge hpos h1 h2)

#print axioms attenuation_pos_of_certified

/-- The certificate as a contraction factor: under the same hypotheses,
`max lam2' edge / lam1' < 1`. The ratio is formed from the true values; `0 < lam1'` follows from the
band hypothesis and `0 < lam1 - d`. Obtained by reading `attenuation_pos_of_certified` back through
`certificate_iff_arith` and dividing. This is the shape `Forgetting.forgets_of_margin` consumes.

DERIVED: `0` is the positivity threshold on `edge` and on `lam1 - d`; `1` is the level a contraction
factor must fall strictly below. -/
theorem ratio_lt_one_of_certified {lam1 lam2 lam1' lam2' edge d : ℝ}
    (hedge : 0 < edge) (hpos : 0 < lam1 - d)
    (hcert : max (lam2 + d) edge < lam1 - d)
    (h1 : |lam1' - lam1| ≤ d) (h2 : |lam2' - lam2| ≤ d) :
    max lam2' edge / lam1' < 1 := by
  have hlam1' : 0 < lam1' := by
    have := (abs_le.mp h1).1
    linarith
  have hden : 0 < max lam2' edge := lt_of_lt_of_le hedge (le_max_right _ _)
  have hatt := attenuation_pos_of_certified hedge hpos hcert h1 h2
  have hlt : max lam2' edge < lam1' := (certificate_iff_arith hedge hlam1').mp hatt
  exact (div_lt_one hlam1').mpr hlt

#print axioms ratio_lt_one_of_certified

/-- The margin is nonnegative: `0 ≤ max lam2' edge / lam1'` whenever `0 < edge` and `0 < lam1'`.
Numerator and denominator are both positive, so `div_nonneg` applies. Together with
`ratio_lt_one_of_certified` this is the pair of side conditions `forgets_of_margin` requires.

DERIVED: `0` is the positivity threshold on `edge` and on `lam1'`, and the lower bound asserted on
the ratio. -/
theorem ratio_nonneg {lam1' lam2' edge : ℝ} (hedge : 0 < edge) (hlam1' : 0 < lam1') :
    0 ≤ max lam2' edge / lam1' :=
  div_nonneg (le_of_lt (lt_of_lt_of_le hedge (le_max_right _ _))) hlam1'.le

#print axioms ratio_nonneg

/-- The chain ending at `MassGap.Forgets`. For a finite index set `s` and mode data `P μ : ι → ℂ`,
the hypotheses `0 < edge`, `0 < lam1 - d`, the certificate `max (lam2 + d) edge < lam1 - d`, the two
band hypotheses, and `hmodes : ∀ k ∈ s, ‖μ k‖ ≤ max lam2' edge / lam1'` give
`MassGap.Forgets (fun τ => ∑ k ∈ s, P k * μ k ^ τ)`. It is `MassGap.forgets_of_margin` at the margin
`max lam2' edge / lam1'`, with `ratio_nonneg` and `ratio_lt_one_of_certified` as its side
conditions.

`hmodes` relates the individual modes to the spectral ratio and is a hypothesis, not a consequence
of the arithmetic above it. The conclusion is about this one mode sum, not about any operator.

DERIVED: `0` is the positivity threshold on `edge` and on `lam1 - d`. -/
theorem forgets_of_certified_gap {ι : Type*} (s : Finset ι) (P μ : ι → ℂ)
    {lam1 lam2 lam1' lam2' edge d : ℝ}
    (hedge : 0 < edge) (hpos : 0 < lam1 - d)
    (hcert : max (lam2 + d) edge < lam1 - d)
    (h1 : |lam1' - lam1| ≤ d) (h2 : |lam2' - lam2| ≤ d)
    (hmodes : ∀ k ∈ s, ‖μ k‖ ≤ max lam2' edge / lam1') :
    MassGap.Forgets (fun τ => ∑ k ∈ s, P k * (μ k) ^ τ) := by
  have hlam1' : 0 < lam1' := by
    have := (abs_le.mp h1).1
    linarith
  exact MassGap.forgets_of_margin s P μ (max lam2' edge / lam1')
    (ratio_nonneg hedge hlam1')
    (ratio_lt_one_of_certified hedge hpos hcert h1 h2) hmodes

#print axioms forgets_of_certified_gap

/-- The same hypotheses as `forgets_of_certified_gap`, with the fuller conclusion of
`MassGap.bridge_forward`: the norms `τ ↦ ‖∑ k ∈ s, P k * μ k ^ τ‖` tend to `0` along `atTop`, are
summable, and the sum satisfies `MassGap.Forgets`. Instantiated at the same margin
`max lam2' edge / lam1'`.

DERIVED: `0` is the positivity threshold on `edge` and on `lam1 - d`, and the limit point in the
`Tendsto` conjunct. -/
theorem bridge_of_certified_gap {ι : Type*} (s : Finset ι) (P μ : ι → ℂ)
    {lam1 lam2 lam1' lam2' edge d : ℝ}
    (hedge : 0 < edge) (hpos : 0 < lam1 - d)
    (hcert : max (lam2 + d) edge < lam1 - d)
    (h1 : |lam1' - lam1| ≤ d) (h2 : |lam2' - lam2| ≤ d)
    (hmodes : ∀ k ∈ s, ‖μ k‖ ≤ max lam2' edge / lam1') :
    Tendsto (fun τ => ‖∑ k ∈ s, P k * (μ k) ^ τ‖) atTop (𝓝 0) ∧
      Summable (fun τ => ‖∑ k ∈ s, P k * (μ k) ^ τ‖) ∧
      MassGap.Forgets (fun τ => ∑ k ∈ s, P k * (μ k) ^ τ) := by
  have hlam1' : 0 < lam1' := by
    have := (abs_le.mp h1).1
    linarith
  exact MassGap.bridge_forward s P μ (max lam2' edge / lam1')
    (ratio_nonneg hedge hlam1')
    (ratio_lt_one_of_certified hedge hpos hcert h1 h2) hmodes

#print axioms bridge_of_certified_gap

/-- The certificate's negation, from the opposite inequality: `lam1 - d ≤ max (lam2 + d) edge`
implies `¬ (max (lam2 + d) edge < lam1 - d)`. It is `not_lt.mpr` on the reals, so it holds for any
values whatever and uses nothing about eigenvalues, bands or attenuation. It records that the
certificate is a strict inequality and so fails once the band closes the separation; it does not
exhibit values at which that happens.

DERIVED: no numeral appears in the statement. -/
theorem certificate_fails_when_band_swallows_gap {lam1 lam2 edge d : ℝ}
    (h : lam1 - d ≤ max (lam2 + d) edge) :
    ¬ (max (lam2 + d) edge < lam1 - d) :=
  not_lt.mpr h

#print axioms certificate_fails_when_band_swallows_gap

end MassGap.CertifiedGap
