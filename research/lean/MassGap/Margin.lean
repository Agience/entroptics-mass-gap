import MassGap.ReachFreeze
import MassGap.Floor

/-!
# MassGap.Margin — the read margin as a chain of real inequalities

Two theorems about real numbers. Both are `Real.exp_le_exp` steps over a `linarith` chain; neither
mentions a lattice, an operator or a spectrum.

* `band_of_contraction` — from `c ≤ Δ`, concludes `exp (-Δ) ≤ exp (-c)`.
* `margin_of_contraction` — from `κ₀ ≤ κ`, `κ - μ ≤ c` and `c ≤ Δ`, concludes
  `exp (-Δ) ≤ exp (-(κ₀ - μ))`.

The names read the variables as a mass gap `Δ`, a contraction rate `c`, an entropy floor `κ₀`, a
counting rate `κ` and a vortex free-energy density `μ`, but the statements quantify over arbitrary
reals: nothing here defines any of those quantities or supplies any of the three hypotheses. The
hypotheses are the interface a caller must discharge.

`margin_of_contraction` concludes the margin `e^{-Δ} ≤ e^{-(κ₀-μ)}`. The stronger ceiling
`e^{-Δ} ≤ 3^{-1/4} = e^{-κ₀}` requires `Δ ≥ κ₀` and is not concluded here.
-/

namespace MassGap

/-- Antitone exponential on the two reals `c ≤ Δ`: `exp (-Δ) ≤ exp (-c)`. Read as a band limit, a
dominant mode of magnitude `e^{-Δ}` whose exponent clears a contraction rate `c` decays at least as
fast as `e^{-c}`. Both `c` and `Δ` are implicit and unconstrained beyond `hgap`.

DERIVED: no numeral. -/
theorem band_of_contraction {Δ c : ℝ} (hgap : c ≤ Δ) : Real.exp (-Δ) ≤ Real.exp (-c) :=
  Real.exp_le_exp.mpr (by linarith)

/-- Chains three real inequalities through the antitone exponential. From

* `hfloor : κ₀ ≤ κ`,
* `hfe : κ - μ ≤ c`, and
* `hgap : c ≤ Δ`,

`linarith` gives `κ₀ - μ ≤ Δ`, hence `exp (-Δ) ≤ exp (-(κ₀ - μ))`. All five variables are implicit
reals with no further constraint, and all three hypotheses are used. The reading of `κ₀` as an entropy
floor, `μ` as a vortex free-energy density and `Δ` as a transfer gap is the caller's; the statement
neither defines those quantities nor discharges any of the three inputs.

DERIVED: no numeral. -/
theorem margin_of_contraction {κ₀ κ μ c Δ : ℝ}
    (hfloor : κ₀ ≤ κ) (hfe : κ - μ ≤ c) (hgap : c ≤ Δ) :
    Real.exp (-Δ) ≤ Real.exp (-(κ₀ - μ)) :=
  Real.exp_le_exp.mpr (by linarith)

/-! **Scope.** `margin_of_contraction` concludes `e^{−Δ} ≤ e^{−(κ₀−μ)}`. The stronger ceiling
`e^{−Δ} ≤ 3^{−1/4} = e^{−κ₀}` needs `Δ ≥ κ₀`, i.e. the contraction to clear the full rate `κ` rather than
the difference `κ−μ`. No declaration in this file concludes it. -/

end MassGap
