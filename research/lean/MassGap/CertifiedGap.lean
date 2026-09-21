import Mathlib
import MassGap.Forgetting

/-!
# MassGap.CertifiedGap — a positive gap that survives a stated numerical band

`entroptics.reads.attenuation_interval` computes, from a correlation matrix and an upper bound
`band` on `‖C_read − C_true‖₂`, an interval `[α_lo, α_hi]` for the attenuation
`α = log λ₁ − log(max λ₂ edge)`, and reports `certified = α_lo > 0`.

**That is a derived implication, not a fit**, and it had no Lean counterpart. This file is that
counterpart.

## Why the shape matters

Every other route to the gap in this tree asks for a bound on a physical quantity — a far-share
envelope, a second moment, a lag-two ratio — uniform in coupling and aperture. Those are the
statements nothing supplies.

This one asks for something different in kind: **an upper bound on the numerical error of a
computation.** Weyl's inequality then does the rest, exactly. For a statistical estimate the band is
a confidence statement and the conclusion inherits that status. For a DETERMINISTIC computation the
band is an arithmetic error bound, and the conclusion is a theorem.

## What is proved, and what is assumed

* `attenuation_ge_of_band` — the propagation. Given `|λᵢ_read − λᵢ_true| ≤ d`, the true attenuation is
  at least the read's lower endpoint. Monotonicity of `log`, twice, and nothing else.
* `certificate_iff_arith` — **the certificate is a comparison of numbers, not of logarithms.**
  `α_lo > 0 ↔ max (λ₂ + d) edge < λ₁ − d`. That is what a checker evaluates.
* `ratio_lt_one_of_certified` — the certificate as a contraction factor `< 1`, which is the form
  `Forgetting.forgets_of_margin` consumes.
* `forgets_of_certified_gap` — the chain, ending at `Forgets`.

**Weyl's inequality itself is the HYPOTHESIS `|λᵢ_read − λᵢ_true| ≤ d`, not a theorem here.** It is
the standard perturbation bound for self-adjoint operators and the Python docstring cites it by name;
stating it as a hypothesis keeps the arithmetic separate from the operator theory, and the arithmetic
is what the certificate actually runs on.

**And the modes-to-ratio step is a hypothesis too.** That every mode's modulus is bounded by the
spectral ratio is a statement about the model, not about the arithmetic, so `forgets_of_certified_gap`
takes it as `hmodes` rather than assuming it silently.
-/

namespace MassGap.CertifiedGap

open Filter Topology

/-- The attenuation a spectral read reports: the log-ratio of the top eigenvalue to the larger of the
second and the noise edge.

DERIVED: no numeral. `edge` is the caller's floor and the two `λ` are the read's own. -/
noncomputable def attenuation (lam1 lam2 edge : ℝ) : ℝ :=
  Real.log lam1 - Real.log (max lam2 edge)

#print axioms attenuation

/-- **THE BAND PROPAGATES, EXACTLY.**

If the true eigenvalues lie within `d` of the read ones, the true attenuation is at least the
endpoint the read computes from `λ₁ − d` and `λ₂ + d`. Monotonicity of `log` in the numerator and
against it in the denominator; nothing is given away.

DERIVED: no numeral; `d` is the caller's band. -/
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

/-- **THE CERTIFICATE IS A COMPARISON OF NUMBERS.** `α > 0` says exactly that the top eigenvalue
exceeds the larger of the second and the edge — no logarithm is evaluated to check it.

This is the form a certifier runs, and stating it as an `iff` is what makes the logarithm in
`attenuation` a presentation rather than a computation. -/
theorem certificate_iff_arith {lam1 lam2 edge : ℝ} (hedge : 0 < edge) (hlam1 : 0 < lam1) :
    0 < attenuation lam1 lam2 edge ↔ max lam2 edge < lam1 := by
  unfold attenuation
  rw [sub_pos]
  exact Real.log_lt_log_iff (lt_of_lt_of_le hedge (le_max_right _ _)) hlam1

#print axioms certificate_iff_arith

/-- **A CERTIFIED BAND GIVES A POSITIVE TRUE ATTENUATION.** The arithmetic check at the read's
endpoints transfers to the truth. -/
theorem attenuation_pos_of_certified {lam1 lam2 lam1' lam2' edge d : ℝ}
    (hedge : 0 < edge) (hpos : 0 < lam1 - d)
    (hcert : max (lam2 + d) edge < lam1 - d)
    (h1 : |lam1' - lam1| ≤ d) (h2 : |lam2' - lam2| ≤ d) :
    0 < attenuation lam1' lam2' edge :=
  lt_of_lt_of_le ((certificate_iff_arith hedge hpos).mpr hcert)
    (attenuation_ge_of_band hedge hpos h1 h2)

#print axioms attenuation_pos_of_certified

/-- **AND THEREFORE A CONTRACTION FACTOR STRICTLY BELOW ONE.**

`max λ₂ edge / λ₁ < 1` is the certificate in the shape a margin argument consumes. Stated on the
ratio rather than on the logarithm because that is what gets compared to `1`. -/
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

/-- and the ratio is never negative, so it is a legitimate margin. -/
theorem ratio_nonneg {lam1' lam2' edge : ℝ} (hedge : 0 < edge) (hlam1' : 0 < lam1') :
    0 ≤ max lam2' edge / lam1' :=
  div_nonneg (le_of_lt (lt_of_lt_of_le hedge (le_max_right _ _))) hlam1'.le

#print axioms ratio_nonneg

/-- **THE CHAIN, ENDING AT FORGETTING.**

A stated numerical band, an arithmetic certificate at the read's endpoints, and the modes bounded by
the spectral ratio — and the flow forgets, hence decays, hence has a finite correlation length.

`hmodes` is the modelling step and is named rather than assumed: it says the flow's modes are
governed by the spectral ratio the certificate bounds. The rest is arithmetic.

DERIVED: no numeral in the statement; every constant is the caller's. -/
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

/-- **AND THE WHOLE BRIDGE FROM IT** — decay, summability and the margin, from a numerical band. -/
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

/-- **NEGATIVE CONTROL: a band that swallows the gap certifies nothing.**

With `d` large enough that `λ₁ − d ≤ max (λ₂ + d) edge`, the certificate fails — and it must, because
the truth is then consistent with no gap at all. Stated so the certificate is known to be refutable
rather than a formality that always passes. -/
theorem certificate_fails_when_band_swallows_gap {lam1 lam2 edge d : ℝ}
    (h : lam1 - d ≤ max (lam2 + d) edge) :
    ¬ (max (lam2 + d) edge < lam1 - d) :=
  not_lt.mpr h

#print axioms certificate_fails_when_band_swallows_gap

end MassGap.CertifiedGap
