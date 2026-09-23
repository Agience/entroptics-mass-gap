import Mathlib

/-!
# MassGap.CentreDominance — the perimeter-over-area limit

One theorem about real sequences. If a per-area free energy is written as a constant `σZ` minus `c`
times a perimeter/area ratio, and that ratio tends to zero, the free energy tends to `σZ`.

The content is the limit itself. Nothing in the statement is specific to gauge theory: a caller
supplies the identification of `σZ` with a centre string tension, of `c` with the size of the
non-centre contribution, and of `P n / A n` with a loop's perimeter-to-area ratio.

Imported by the `MassGap` aggregate (`MassGap.lean`).
-/

namespace MassGap.CentreDominance

open Filter

/-- If `P n / A n` tends to `0`, then `σZ - c * (P n / A n)` tends to `σZ`.

`σZ` and `c` are arbitrary reals, bound outside the hypothesis: neither is required to be positive,
and `A` is allowed to vanish because division is total in `ℝ`. The sequences `A` and `P` enter only
through their ratio.

DERIVED: `0` is the limit of the perimeter/area ratio assumed in `hPA`, and is the only numeral in
the statement. -/
theorem string_tension_eq_centre {σZ c : ℝ} {A P : ℕ → ℝ}
    (hPA : Tendsto (fun n => P n / A n) atTop (nhds 0)) :
    Tendsto (fun n => σZ - c * (P n / A n)) atTop (nhds σZ) := by
  simpa using tendsto_const_nhds.sub (hPA.const_mul c)

#print axioms string_tension_eq_centre

end MassGap.CentreDominance
