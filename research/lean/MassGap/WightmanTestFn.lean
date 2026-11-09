import Mathlib

/-!
# MassGap.WightmanTestFn — Euclidean spacetime and its Schwartz test functions

`E4` is Euclidean spacetime `ℝ⁴` and `TestFn` the real Schwartz functions on it, the index set the
tempered Osterwalder–Schrader functionals of `ObserverOSTempered` are smeared against. Both are
Mathlib abbreviations; the module states nothing else.
-/

namespace MassGap.WightmanData

/-- Euclidean spacetime `ℝ⁴`.

DERIVED: `4` is the dimension of spacetime — the Clay problem's own. It is the number of
coordinates, not a cutoff or a resolution; `EuclideanSpace ℝ (Fin 4)` is all of `ℝ⁴`. -/
abbrev E4 : Type := EuclideanSpace ℝ (Fin 4)

/-- Real Schwartz test functions on `E4`.

DERIVED: no numeral occurs; the dimension is inside `E4`. -/
abbrev TestFn : Type := SchwartzMap E4 ℝ

end MassGap.WightmanData
