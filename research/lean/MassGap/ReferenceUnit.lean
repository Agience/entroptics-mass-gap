import Mathlib
import MassGap.MeasuredTower

/-!
# MassGap.ReferenceUnit — the reference coupling of the spacing is a unit, not a parameter

The dyadic spacing `ClayTreeG.dySpacingG G k = aRunG G 1 / 2^(k+1)` is read at the reference coupling `1`. This
module shows that the measured tower does not depend on that choice: the spacing read at any positive reference
coupling `β₁` gives the same towers, with the unit `c` of the band rescaled by `aRunG G 1 / aRunG G β₁`. Since the
unit is existential in `MeasuredTower.MeasTowerG`, for `MeasTowerG` the reference coupling fixes a unit of length
and nothing else. The schedule `schedAlongG` and the per-step gap ratio `2 log 2 / aRunG G 1` also read
`dySpacingG`; their invariance is not shown here.
Declarations are in the namespace `MassGap.ReferenceUnit`.

* `spacingAt G β₁ k = aRunG G β₁ / 2^(k+1)`, `BandAt`, `MeasTowerAt`: the spacing, band and tower read at the
  reference coupling `β₁`; at `β₁ = 1` they are `dySpacingG`, `BandG`, `MeasTowerG` (`measTowerAt_one`).
* `bandAt_rescale`: the band at `β₁` and unit `c` is the band at `β₂` and unit `c · aRunG β₁ / aRunG β₂`.
* `measTowerAt_iff`: the towers at two positive reference couplings coincide.
* `measTowerG_iff_at`: `MeasTowerG G βs` holds exactly when the tower at any one positive reference coupling does.

DERIVED (module-wide): `2` the dyadic halving and the band's dyadic ratio; `1` the first halving and the
reference coupling of `dySpacingG`; `0` the signs.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ReferenceUnit

open Filter Topology
open scoped ENNReal
open MassGap MassGap.ClayTreeG MassGap.MeasuredTower

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] [GaugeSimple G]

/-- **The dyadic spacing read at the reference coupling `β₁`.** DERIVED: `2` the halving; `1` the first
halving. -/
def spacingAt (β₁ : ℝ) (k : ℕ) : ℝ := GaugeRunning.aRunG G β₁ / 2 ^ (k + 1)

/-- **The band of step `k` at unit `c`, read at the reference coupling `β₁`.** DERIVED: `2` the dyadic ratio. -/
def BandAt (β₁ c : ℝ) (k : ℕ) (β : ℝ) : Prop :=
  ENNReal.ofReal (c * spacingAt G β₁ k) ≤ mUG G β ∧ mUG G β ≤ ENNReal.ofReal (2 * c * spacingAt G β₁ k)

/-- **The measured tower read at the reference coupling `β₁`.** DERIVED: `0` the sign of the unit. -/
def MeasTowerAt (β₁ : ℝ) (βs : ℕ → ℝ) : Prop :=
  Tendsto βs atTop atTop ∧ ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, BandAt G β₁ c k (βs k)

variable {G}

/-- **At the reference coupling `1` the tower is `MeasTowerG`.** DERIVED: `1` the reference of
`dySpacingG`. -/
theorem measTowerAt_one (βs : ℕ → ℝ) : MeasTowerAt G 1 βs ↔ MeasTowerG G βs := Iff.rfl

/-- **Changing the reference coupling rescales the unit.** DERIVED: `0` the signs. -/
theorem bandAt_rescale {β₁ β₂ : ℝ} (h₂ : 0 < β₂) (c : ℝ) (k : ℕ) (β : ℝ) :
    BandAt G β₁ c k β ↔
      BandAt G β₂ (c * GaugeRunning.aRunG G β₁ / GaugeRunning.aRunG G β₂) k β := by
  have ha : GaugeRunning.aRunG G β₂ ≠ 0 := (aRunG_pos G h₂).ne'
  have e1 : c * spacingAt G β₁ k
      = c * GaugeRunning.aRunG G β₁ / GaugeRunning.aRunG G β₂ * spacingAt G β₂ k := by
    unfold spacingAt; field_simp
  have e2 : 2 * c * spacingAt G β₁ k
      = 2 * (c * GaugeRunning.aRunG G β₁ / GaugeRunning.aRunG G β₂) * spacingAt G β₂ k := by
    unfold spacingAt; field_simp
  unfold BandAt
  rw [e1, e2]

/-- **The towers at two positive reference couplings coincide.** DERIVED: `0` the signs. -/
theorem measTowerAt_iff {β₁ β₂ : ℝ} (h₁ : 0 < β₁) (h₂ : 0 < β₂) (βs : ℕ → ℝ) :
    MeasTowerAt G β₁ βs ↔ MeasTowerAt G β₂ βs := by
  have p₁ := aRunG_pos G h₁
  have p₂ := aRunG_pos G h₂
  constructor
  · rintro ⟨hT, c, hc, hb⟩
    exact ⟨hT, c * GaugeRunning.aRunG G β₁ / GaugeRunning.aRunG G β₂, by positivity,
      hb.mono fun k hk => (bandAt_rescale h₂ c k (βs k)).mp hk⟩
  · rintro ⟨hT, c, hc, hb⟩
    exact ⟨hT, c * GaugeRunning.aRunG G β₂ / GaugeRunning.aRunG G β₁, by positivity,
      hb.mono fun k hk => (bandAt_rescale h₁ c k (βs k)).mp hk⟩

/-- **The measured tower does not depend on the reference coupling**: `MeasTowerG G βs` holds exactly when the
tower read at any positive reference coupling does. DERIVED: `0` the sign; `1` the reference of
`dySpacingG`. -/
theorem measTowerG_iff_at {β₁ : ℝ} (h₁ : 0 < β₁) (βs : ℕ → ℝ) :
    MeasTowerG G βs ↔ MeasTowerAt G β₁ βs :=
  (measTowerAt_one βs).symm.trans (measTowerAt_iff one_pos h₁ βs)

end MassGap.ReferenceUnit

#print axioms MassGap.ReferenceUnit.measTowerAt_one
#print axioms MassGap.ReferenceUnit.bandAt_rescale
#print axioms MassGap.ReferenceUnit.measTowerAt_iff
#print axioms MassGap.ReferenceUnit.measTowerG_iff_at
