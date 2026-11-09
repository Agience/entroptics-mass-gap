import Mathlib
import MassGap.MeasuredTower
import MassGap.FlowG
import MassGap.ObserverOSG
import MassGap.AxisInvG

/-!
# MassGap.SchedAlong — the schedule properties along every coupling tower

`MeasuredTower.schedAlongG G βs` is the schedule with spacing `dySpacingG G k` and state
`periodicStateG G (βs k)`. The four schedule properties read by the flowed reconstruction and the observer
over `G` hold at every `βs : ℕ → ℝ`: each is a property of `periodicStateG G β` at every real `β`, read at
`β = βs k`, and of the dyadic spacing, which does not depend on `βs`.

* `schedTransInv_alongG`: `ClayWiringG.SchedTransInv (schedAlongG G βs)`, from
  `ShiftInvG.periodicStateG_shift` and `ShiftInvG.site_dySpacingG`.
* `schedOS_alongG`: `FlowG.SchedOS (schedAlongG G βs)`, adding `ReflInvG.periodicStateG_reflInvariant`,
  `ReflPosG.periodicStateG_rp_zero` and `ShiftInvG.dySpacingG_mul_pow`.
* `schedShiftInv_alongG`: `ObserverOSG.SchedShiftInv (schedAlongG G βs)`.
* `schedAxisInv_alongG`: `SymPlaqG.SchedAxisInv (schedAlongG G βs)`, from `AxisInvG.periodicStateG_axis`.

The module sits below `ClayGFinal` and `MeasuredSpacing`, so both read these facts at a tower. Declarations
are in the namespace `MassGap.MeasuredSpacing`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the plane of reflection positivity; `2` the dyadic ratio of the spacing.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.MeasuredSpacing

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ClayTreeG MassGap.FlowG MassGap.MeasuredTower

section Sched

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] [GaugeSimple G]

/-- **Every tower's schedule is dyadically translation invariant.** DERIVED: `2` the dyadic ratio. -/
theorem schedTransInv_alongG (βs : ℕ → ℝ) : ClayWiringG.SchedTransInv (schedAlongG G βs) := by
  intro ι _ F j k hk p
  have hs : site ((schedAlongG G βs).a j) p
      = site ((schedAlongG G βs).a k) (scaleSite (2 ^ (k - j)) p) := ShiftInvG.site_dySpacingG G hk p
  rw [hs]
  exact ShiftInvG.latSG_translate (schedAlongG G βs) k
    (fun τ f => ShiftInvG.periodicStateG_shift G (βs k) τ f) F _

/-- **Every tower's schedule carries the four schedule properties of the flowed reconstruction.**
DERIVED: `0` the plane. -/
theorem schedOS_alongG (βs : ℕ → ℝ) : SchedOS (schedAlongG G βs) :=
  ⟨schedTransInv_alongG G βs, fun k τ c => ReflInvG.periodicStateG_reflInvariant G (βs k) τ c,
    fun k τ X hX => ReflPosG.periodicStateG_rp_zero G (βs k) τ X hX,
    fun _ _ hmk => ShiftInvG.dySpacingG_mul_pow G hmk⟩

/-- **Every tower's schedule is shift invariant.** DERIVED: no numeral. -/
theorem schedShiftInv_alongG (βs : ℕ → ℝ) : ObserverOSG.SchedShiftInv (schedAlongG G βs) :=
  fun k τ F => ShiftInvG.periodicStateG_shift G (βs k) τ F

/-- **Every tower's schedule is invariant under the relabelling of the axes.** DERIVED: no numeral. -/
theorem schedAxisInv_alongG (βs : ℕ → ℝ) : SymPlaqG.SchedAxisInv (schedAlongG G βs) :=
  fun k e F => AxisInvG.periodicStateG_axis G (βs k) e F

end Sched

end MassGap.MeasuredSpacing

end

#print axioms MassGap.MeasuredSpacing.schedTransInv_alongG
#print axioms MassGap.MeasuredSpacing.schedOS_alongG
#print axioms MassGap.MeasuredSpacing.schedShiftInv_alongG
#print axioms MassGap.MeasuredSpacing.schedAxisInv_alongG
