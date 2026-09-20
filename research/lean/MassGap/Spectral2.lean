import Mathlib
import MassGap.Complete
import MassGap.PowerTail

/-!
# MassGap.Spectral2 — the first `Complete.WilsonSpectral`

`Complete.WilsonSpectral N β` is `Nonempty (Spectral.PeriodicSpectralForm (N+1) (wilsonCorrAt N β))`
— a `def ... : Prop` that, until this file, nothing in the tree produced. Its own docstring records
that it is assumed. This file produces one, at `β = 0`, and says precisely how far that reaches.

## What is proved

`wilsonSpectral_at_zero_coupling`: `WilsonSpectral (M+1) 0` at every aperture `M`, with the
foundational axioms only. The witness is `contactForm`: `Idx := Unit`, `w = ρ(0)`, `λ = 0`.

* `PowerTail.wilsonCorrAt_at_zero_coupling` — at `β = 0` the connected correlation VANISHES at every
  lag but zero, because the state is product Haar and the two plaquettes read disjoint link sets;
* `PlaqVariance.corrClay_zero_pos` — the lag-zero value is strictly positive at every real coupling
  and every extent, so the weight is nonnegative and not zero;
* `λ = 0` reproduces both: `0^0 = 1` carries the contact term and `0^d = 0` kills every other lag.

`wilson_decay_at_zero_coupling` then discharges `Complete.ym_wilson_decay_to_half_period` outright at
`β = 0`: a bound on the genuine `wilsonCorrAt` with NO remaining hypothesis, which is the first time
that theorem has been applied to the Wilson correlation rather than stated about a supplied form.

## What this does NOT do, stated because the surrounding docstrings are easy to over-read

It is the FREE point. `λ = 0` is a pure contact term with no transfer dynamics, so this witness
carries no gap and no coupling dependence. What it settles is that `WilsonSpectral` is a satisfiable
property of the real correlation rather than an empty one, and — the other way round — that holding
`WilsonSpectral` at a coupling is on its own worth nothing: a correlation with no structure at all
has it. The content of the open obligation is `WilsonSpectral N β` at `β > 0`, and nothing here
moves it.

It is also not a transfer-operator construction. `Transfer.periodicSpectralForm_of_transfer` is the
route that would produce these forms from an operator, and it consumes a `Transfer.TransferData`,
which needs a time-translation endomorphism of the observable module and a finite-dimensional GNS
space — neither of which exists in the tree. This witness is built by evaluating the correlation,
not by diagonalising anything.

Foundational footprint only (`#print axioms` at the end).
Build: `python research/code/lean_build.py build MassGap.Spectral2`.
-/

namespace MassGap.Spectral2

open MassGap

/-- **At zero coupling every lag but zero has circle distance at least one.** The arithmetic behind
the case split below: `circLag d = min d (n − d)`, and a nonzero `d : Fin (M+2)` has both entries at
least one. -/
theorem one_le_circLag_of_ne_zero {M : ℕ} {d : Fin (M + 2)} (hd : d ≠ 0) :
    1 ≤ Moment.circLag d := by
  have hlt : (d : ℕ) < M + 2 := d.isLt
  have hpos : 0 < (d : ℕ) := by
    rcases Nat.eq_zero_or_pos (d : ℕ) with h | h
    · exact absurd (Fin.ext h) hd
    · exact h
  simp only [Moment.circLag, le_min_iff]
  omega

/-- **THE CONTACT SPECTRAL FORM OF THE FREE WILSON CORRELATION.**

At `β = 0` the four-dimensional `SU(3)` Wilson correlation is a pure contact term, and a contact term
IS a periodic spectral form: all the weight on one mode, at decay factor zero.

DERIVED: no numeral is chosen. `Unit` is one mode because the correlation has one nonzero lag; the
weight is the correlation's own lag-zero value, not a level; and `λ = 0` is forced — it is the only
decay factor for which `λ^d + λ^{n−d}` vanishes at every lag the correlation vanishes at, since
`0^0 = 1` and `0^d = 0` for `d ≠ 0`. -/
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

/-- **THE FIRST `Complete.WilsonSpectral`.**

`WilsonSpectral` has been a `def ... : Prop` with no producer since it was written, and its own
docstring says it is assumed. This is a producer, at the free point, with the foundational axioms
only and at every aperture. -/
theorem wilsonSpectral_at_zero_coupling (M : ℕ) : MassGap.WilsonSpectral (M + 1) 0 :=
  ⟨contactForm M⟩

#print axioms wilsonSpectral_at_zero_coupling

/-- **The witness is not the degenerate one.** Its single weight is strictly positive, so the form is
not the zero form and `hrep` is a real identity rather than `0 = 0` at every lag. -/
theorem contactForm_weight_pos (M : ℕ) : 0 < (contactForm M).w () :=
  MassGap.PlaqVariance.corrClay_zero_pos (M + 1) 0

#print axioms contactForm_weight_pos

/-- **`Complete.ym_wilson_decay_to_half_period`, DISCHARGED AT `β = 0`.**

That theorem bounds the genuine `wilsonCorrAt` out to half the period, given a periodic spectral form
and a gap on its contributing modes. Both are now available at the free point: the form is
`contactForm`, and its only mode sits at `λ = 0`, which clears any nonnegative bound. So the
conclusion holds with no hypothesis left.

What it is worth: the first application of that theorem to the Wilson correlation rather than a
statement about a form someone supplies. What it is not worth: at `λ = 0` the bound is slack by an
unbounded margin and the correlation is zero off contact anyway, so no decay rate is being measured.

DERIVED: nothing numeric is chosen. The `2` and the exponent are `Spectral.periodic_decay_le`'s — the
two terms of the periodic shape and the lag — and `κ₀YM`, `μYMAt` are `Complete`'s own. -/
theorem wilson_decay_at_zero_coupling (M : ℕ) (d : Fin (M + 2))
    (hhalf : 2 * (d : ℕ) ≤ M + 2) :
    MassGap.wilsonCorrAt (M + 1) 0 d
      ≤ 2 * (∑ k, (contactForm M).w k)
          * Real.exp (-(MassGap.κ₀YM - MassGap.μYMAt (M + 1) 0)) ^ (d : ℕ) :=
  MassGap.ym_wilson_decay_to_half_period (contactForm M)
    (fun _ _ => (Real.exp_pos _).le) d hhalf

#print axioms wilson_decay_at_zero_coupling

end MassGap.Spectral2
