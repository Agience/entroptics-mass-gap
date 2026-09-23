import Mathlib
import MassGap.Complete
import MassGap.PowerTail

/-!
# MassGap.Spectral2 — a `Spectral.PeriodicSpectralForm` for `wilsonCorrAt (M+1) 0`

`Complete.WilsonSpectral N β` unfolds to
`Nonempty (Spectral.PeriodicSpectralForm (N+1) (wilsonCorrAt N β))`. This file constructs one
inhabitant of that type, at coupling `β = 0` and at every extent parameter `M`, and applies
`Complete.ym_wilson_decay_to_half_period` to it.

`contactForm M` is the witness: one mode (`Idx := Unit`), weight the lag-zero correlation value
`wilsonCorrAt (M+1) 0 0`, and decay factor `lam = 0`. Its `hrep` obligation splits on `d = 0`: at
lag zero `0 ^ 0 = 1` reproduces the weight, and at every other lag `0 ^ d = 0` matches
`PowerTail.wilsonCorrAt_at_zero_coupling`, which gives `wilsonCorrAt (M+1) 0 d = 0` whenever
`1 ≤ Moment.circLag d`. Nonnegativity of the weight comes from
`PlaqVariance.corrClay_zero_pos (M+1) 0`, restated as `contactForm_weight_pos`.

`one_le_circLag_of_ne_zero` is the arithmetic the split needs: a nonzero `d : Fin (M+2)` has circular
lag at least one. `wilsonSpectral_at_zero_coupling` wraps `contactForm` in `Nonempty`.
`wilson_decay_at_zero_coupling` feeds `contactForm M` to
`MassGap.ym_wilson_decay_to_half_period`, discharging that theorem's mode-gap hypothesis from
`Real.exp_pos`, and obtains a bound on `wilsonCorrAt (M+1) 0 d` for `2 * d ≤ M + 2`.

Scope: every statement here fixes the coupling at `0`. Nothing is stated at nonzero `β`, and the
witness has a single mode at decay factor `0`, so the bound in `wilson_decay_at_zero_coupling` is
not a measurement of any decay rate. No transfer operator is constructed or diagonalised; the form
is built by evaluating the correlation. Axiom footprint is recorded by the `#print axioms` line
after each declaration.
-/

namespace MassGap.Spectral2

open MassGap

/-- For `d : Fin (M + 2)` with `d ≠ 0`, `1 ≤ Moment.circLag d`. Unfolding `circLag` as a `min` and
using `le_min_iff`, the two branches are `1 ≤ d` (from `d ≠ 0`) and `1 ≤ M + 2 - d` (from
`d < M + 2`), both closed by `omega`.

Scope: the extent is `M + 2`, so it is at least two and the modulus is never degenerate; the
hypothesis `d ≠ 0` is equality in `Fin (M + 2)`, not on the underlying natural number.

DERIVED: `2` is the `+ 2` in the index type `Fin (M + 2)`, which forces the extent to be at least
two; `0` is the value `d` is assumed to differ from; `1` is the lower bound concluded for
`Moment.circLag d`. -/
theorem one_le_circLag_of_ne_zero {M : ℕ} {d : Fin (M + 2)} (hd : d ≠ 0) :
    1 ≤ Moment.circLag d := by
  have hlt : (d : ℕ) < M + 2 := d.isLt
  have hpos : 0 < (d : ℕ) := by
    rcases Nat.eq_zero_or_pos (d : ℕ) with h | h
    · exact absurd (Fin.ext h) hd
    · exact h
  simp only [Moment.circLag, le_min_iff]
  omega

/-- A `Spectral.PeriodicSpectralForm (M + 2) (MassGap.wilsonCorrAt (M + 1) 0)`: one mode indexed by
`Unit`, weight the lag-zero correlation `wilsonCorrAt (M + 1) 0 0`, and decay factor `lam = 0`.

The four side conditions are discharged as follows. `hw` is
`PlaqVariance.corrClay_zero_pos (M + 1) 0` weakened to `≤`. `hlam0` and `hlam1` are `0 ≤ 0` and
`0 ≤ 1`. `hrep` splits on `d = 0`: at lag zero `simp` closes it via `0 ^ 0 = 1`, and at `d ≠ 0`
`PowerTail.wilsonCorrAt_at_zero_coupling` gives `wilsonCorrAt (M + 1) 0 d = 0` while `zero_pow`
kills both `lam ^ d` and `lam ^ (M + 2 - d)`.

Scope: the coupling is fixed at `0`. With `lam = 0` the form has no mode at a positive decay factor,
so it exhibits no exponential tail; it is a contact term. `M` is unconstrained, so this exists at
every extent of the form `M + 2`.

DERIVED: `2` is the period `M + 2` of the spectral form; `1` is the aperture argument `M + 1` of
`wilsonCorrAt`; `0` is the coupling at which the correlation is taken. Inside the body, `Unit` gives
one mode; the weight is the correlation's own lag-zero value; and `lam = 0` is the only decay factor
for which `lam ^ d + lam ^ (M + 2 - d)` vanishes at every nonzero lag while still reproducing the
weight at lag zero. -/
noncomputable def contactForm (M : ℕ) :
    Spectral.PeriodicSpectralForm (M + 2) (MassGap.wilsonCorrAt (M + 1) 0) where
  Idx := Unit
  w := fun _ => MassGap.wilsonCorrAt (M + 1) 0 0
  lam := fun _ => 0
  hw := fun _ => (MassGap.PlaqVariance.corrClay_zero_pos (M + 1) 0).le
  hlam0 := fun _ => le_refl 0
  hlam1 := fun _ => zero_le_one
  hrep := fun d => by
    by_cases hd : d = 0
    · subst hd
      simp
    · have hzero : MassGap.wilsonCorrAt (M + 1) 0 d = 0 :=
        MassGap.PowerTail.wilsonCorrAt_at_zero_coupling (M + 1) d (one_le_circLag_of_ne_zero hd)
      have hd1 : (d : ℕ) ≠ 0 := by
        intro h
        exact hd (Fin.ext h)
      have hd2 : M + 2 - (d : ℕ) ≠ 0 := by
        have := d.isLt
        omega
      rw [hzero]
      simp [zero_pow hd1, zero_pow hd2]

#print axioms contactForm

/-- `MassGap.WilsonSpectral (M + 1) 0` holds at every `M`, witnessed by `contactForm M`. The proof is
the anonymous constructor of `Nonempty`.

Scope: the coupling argument is the literal `0`. Nothing here is stated at a nonzero coupling.

DERIVED: `1` is the aperture argument `M + 1` of `WilsonSpectral`; `0` is the coupling. -/
theorem wilsonSpectral_at_zero_coupling (M : ℕ) : MassGap.WilsonSpectral (M + 1) 0 :=
  ⟨contactForm M⟩

#print axioms wilsonSpectral_at_zero_coupling

/-- The single weight of `contactForm M` is strictly positive: `0 < (contactForm M).w ()`. It is
definitionally `wilsonCorrAt (M + 1) 0 0`, so the proof is
`PlaqVariance.corrClay_zero_pos (M + 1) 0` unchanged. Consequently the form is not the zero form and
its `hrep` identity is not `0 = 0` at lag zero.

DERIVED: `0` is the lower bound in the strict inequality; the arguments `M + 1` and `0` inside
`contactForm M` are not part of this statement, which names only `contactForm M` and `()`. -/
theorem contactForm_weight_pos (M : ℕ) : 0 < (contactForm M).w () :=
  MassGap.PlaqVariance.corrClay_zero_pos (M + 1) 0

#print axioms contactForm_weight_pos

/-- `MassGap.ym_wilson_decay_to_half_period` applied to `contactForm M`. For `d : Fin (M + 2)` with
`2 * d ≤ M + 2`,
`wilsonCorrAt (M + 1) 0 d ≤ 2 * (∑ k, (contactForm M).w k) * exp (-(κ₀YM - μYMAt (M + 1) 0)) ^ d`.

The mode-gap hypothesis of that theorem is discharged by `fun _ _ => (Real.exp_pos _).le`, since
`contactForm`'s only decay factor is `0` and an exponential is positive. The lag restriction
`2 * d ≤ M + 2` is carried through from the theorem being applied and confines `d` to at most half
the period.

Scope: the coupling is `0` throughout, and the left-hand side vanishes at every `d ≠ 0`, so the
inequality is slack away from contact and measures no decay rate. The exponent base
`exp (-(κ₀YM - μYMAt (M + 1) 0))` is whatever `Complete` defines those two constants to be; nothing
here evaluates or bounds it.

DERIVED: `2` occurs four times — the period `M + 2` in the index type, the factor `2` and the bound
`M + 2` in `hhalf`, and the leading factor `2` in the conclusion, which is
`ym_wilson_decay_to_half_period`'s own two-term periodic shape. `1` occurs twice, as the aperture
argument `M + 1` of `wilsonCorrAt` and of `μYMAt`. `0` occurs twice, as the coupling argument of
each. Nothing numeric is chosen here. -/
theorem wilson_decay_at_zero_coupling (M : ℕ) (d : Fin (M + 2))
    (hhalf : 2 * (d : ℕ) ≤ M + 2) :
    MassGap.wilsonCorrAt (M + 1) 0 d
      ≤ 2 * (∑ k, (contactForm M).w k)
          * Real.exp (-(MassGap.κ₀YM - MassGap.μYMAt (M + 1) 0)) ^ (d : ℕ) :=
  MassGap.ym_wilson_decay_to_half_period (contactForm M)
    (fun _ _ => (Real.exp_pos _).le) d hhalf

#print axioms wilson_decay_at_zero_coupling

end MassGap.Spectral2
