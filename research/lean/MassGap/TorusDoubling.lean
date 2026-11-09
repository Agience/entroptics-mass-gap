import Mathlib
import MassGap.SUN
import MassGap.WilsonAction
import MassGap.RectWilson
import MassGap.ZoomSelfScale

/-!
# MassGap.TorusDoubling — the doubling defect for every compact group and every dimension

The seed `ZoomSelfScale.defectW N β n = 16 log ZR(n) − log ZR(2n)` is stated on the periodic 4-torus
with the `SU(N)` Wilson action. This module states it for a compact group `G`, a dimension `d` and a
plaquette density `φ : G → ℝ`.

* `TSite d n = Fin d → Fin n`, `TLink d n = Fin d × TSite d n`,
  `TPlaq d n = (Fin d × Fin d) × TSite d n`: the periodic `n^d` torus in the tree's convention
  (ordered pairs of directions, each plane counted twice, the diagonal included).
* `tshift i x` steps `x` once in direction `i` by `finRotate n`, and `tbd q` is the boundary word
  `U_i(x) U_j(x+i) U_i(x+j)⁻¹ U_j(x)⁻¹`. These are `RectWilson.rshift` and `RectWilson.rbd` with
  `Fin 4` replaced by `Fin d` and the extents made equal.
* `sysT G d n φ = WilsonLattice.wilsonSystem (tbd d n) φ`, a `LatticeGauge.System G`, and
  `ZT G d φ β n` its partition function against `CompactGauge.probHaar G` on every link.
* `defectWG G d φ β n = 2^d log ZT(n) − log ZT(2n)`; `2^d` is the number of side-`n` tori in the
  side-`2n` torus.
* `SeedFrequentG G d φ`: frequently in `β`, some `2ᵇ`, `b ≥ 1`, has `defectWG ≤ 1/1000`.

**At `SU(N)`, `d = 4`, `φ = wilsonDensity` these are the tree's objects.** `ZT_four_eq` is
`ZT = ZR (fun _ => n)` by `rfl`; and `defectWG_four_eq` gives `defectWG = defectW`.

Nothing in the definitions uses that `φ` is a class function or that `G` is non-abelian; the Wilson
action of a unitary representation is one choice of `φ` (`1 − Re tr/dim` up to normalisation).
-/

namespace MassGap.TorusDoubling

open MeasureTheory Filter MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.CompactGauge

/-! ## The periodic `n^d` torus -/

section Geometry

variable (d n : ℕ)

/-- Sites of the periodic torus of side `n` in dimension `d`. -/
abbrev TSite : Type := Fin d → Fin n

/-- Links: a direction and the site the link leaves. -/
abbrev TLink : Type := Fin d × TSite d n

/-- Plaquettes: an ordered pair of directions and a site. -/
abbrev TPlaq : Type := (Fin d × Fin d) × TSite d n

variable {d n}

/-- One step in direction `i`, periodically. -/
def tshift (i : Fin d) (x : TSite d n) : TSite d n := Function.update x i (finRotate n (x i))

variable (d n)

/-- The plaquette boundary word `U_i(x) U_j(x+i) U_i(x+j)⁻¹ U_j(x)⁻¹`. -/
def tbd (q : TPlaq d n) : List (TLink d n × Bool) :=
  [((q.1.1, q.2), true), ((q.1.2, tshift q.1.1 q.2), true),
   ((q.1.1, tshift q.1.2 q.2), false), ((q.1.2, q.2), false)]

end Geometry

/-! ## The Wilson system, its partition function and the doubling defect -/

section System

variable (G : Type) [Group G] [MeasurableSpace G]

/-- The lattice gauge system on the `n^d` torus with plaquette density `φ`. -/
noncomputable def sysT (d n : ℕ) (φ : G → ℝ) : System G := wilsonSystem (tbd d n) φ

variable {G}

/-- The holonomy of the plaquette `((i, j), x)`. -/
theorem hol_eq {d n : ℕ} (φ : G → ℝ) (U : TLink d n → G) (i j : Fin d) (x : TSite d n) :
    (sysT G d n φ).hol ((i, j), x) U
      = U (i, x) * U (j, tshift i x) * (U (i, tshift j x))⁻¹ * (U (j, x))⁻¹ := by
  simp [sysT, wilsonSystem, wilsonHol, tbd, mul_assoc]

/-- A degenerate plaquette has holonomy `1`. -/
theorem hol_diag {d n : ℕ} (φ : G → ℝ) (U : TLink d n → G) (i : Fin d) (x : TSite d n) :
    (sysT G d n φ).hol ((i, i), x) U = 1 := by
  rw [hol_eq]; group

end System

section Defect

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [Nonempty G] [MeasurableSpace G] [BorelSpace G]

/-- The partition function on the `n^d` torus at coupling `β`, Haar on every link. -/
noncomputable def ZT (d : ℕ) (φ : G → ℝ) (β : ℝ) (n : ℕ) : ℝ :=
  (sysT G d n φ).partition (probHaar G) β

/-- **The doubling defect** `2^d log ZT(n) − log ZT(2n)`. DERIVED: `2^d` is the number of copies of
the side-`n` torus in the side-`2n` torus; `2` the doubling. -/
noncomputable def defectWG (d : ℕ) (φ : G → ℝ) (β : ℝ) (n : ℕ) : ℝ :=
  2 ^ d * Real.log (ZT G d φ β n) - Real.log (ZT G d φ β (2 * n))

/-- **The frequent seed**: frequently in `β`, some power of two `2ᵇ`, `b ≥ 1`, has doubling defect
at most `1/1000`. DERIVED: `1/1000` the sharp seed of `DoublingSharp`; `1 ≤ b` makes `2ᵇ` even and
at least `2`. -/
def SeedFrequentG (d : ℕ) (φ : G → ℝ) : Prop :=
  ∃ᶠ β in atTop, ∃ b : ℕ, 1 ≤ b ∧ defectWG G d φ β (2 ^ b) ≤ 1 / 1000

end Defect

/-! ## At `SU(N)` in four dimensions: the tree's seed -/

section Four

/-- At `SU(N)`, `d = 4` and the Wilson density, `ZT` is `RectWilson.ZR` at constant extents. -/
theorem ZT_four_eq (N : ℕ) (β : ℝ) (n : ℕ) :
    ZT (SUN.SU N) 4 WilsonAction.wilsonDensity β n = RectWilson.ZR (fun _ => n) N β := rfl

/-- At `SU(N)`, `d = 4` and the Wilson density, `defectWG` is `ZoomSelfScale.defectW`. DERIVED:
`2⁴ = 16`. -/
theorem defectWG_four_eq (N : ℕ) (β : ℝ) (n : ℕ) :
    defectWG (SUN.SU N) 4 WilsonAction.wilsonDensity β n = ZoomSelfScale.defectW N β n := by
  unfold defectWG ZoomSelfScale.defectW
  rw [ZT_four_eq, ZT_four_eq]
  norm_num

end Four

end MassGap.TorusDoubling

#print axioms MassGap.TorusDoubling.hol_diag
#print axioms MassGap.TorusDoubling.ZT_four_eq
#print axioms MassGap.TorusDoubling.defectWG_four_eq
