import Mathlib
import MassGap.RunningCrossover
import MassGap.ZoomStep
import MassGap.ReadPos
import MassGap.ExistClose

/-!
# MassGap.OneLoopInput — the one-loop running as one named, cited input, and everything else from it

This module states the running of the coupling as one input in the shape of `ZoomStep`, proves what follows, and
makes the dependence of the whole chain on it explicit. Declarations are in the namespace `MassGap.OneLoopInput`.

`OneLoopZoom N` is a cited perturbative input in the shape of the zoom step. It is not a proof of the zoom step and
it is not a theorem about the lattice Wilson measure at finite `β`. It is the whole non-abelian content of the bridge
along this route: restating the running in this form discharges nothing. What is cited is asymptotic freedom (Gross–
Wilczek 1973, Politzer 1973), a statement about the running of the renormalized coupling at small `g²`. The inequality
on the doubling defect, at every window and down to the small-coupling anchor, is more than that citation says (see
"What does not follow").

## 1. The coefficient (proved arithmetic, cited split)

* `gluonCoeff = spinTerm − orbitalTerm = 4 − 1/3 = 11/3` (`gluonCoeff_eq`): the split of `FluctSheet`, cited
  (Nielsen–Olesen). The spin term antiscreens, the orbital term screens.
* `b0 h = (11/3) h/(16π²)` for dual Coxeter number `h`, the `g`-convention coefficient. `b0_eq_b0G`: at `SU(N)` it is
  `GaugeRunning.b0G`, the coefficient already in the tree. `b0_abelian`: `h = 0` (pure `U(1)`) gives `0`.
* `stdStep N = 2 · (2N) · b0 N · log 2 = 11 N² log 2/(12π²)` (`stdStep_eq`): the rise of the standard `β = 2N/g²` per
  halving of the spacing. `2N` from `β = 2N/g²`, the other `2` from `d(1/g²)/d log μ = 2 b₀`, `log 2` from one doubling.
* `leanStep N = stdStep N / 2 = 11 N² log 2/(24π²)` (`leanStep_eq`). The coupling of `CouplingTower.windowCoupling` is
  the Lean coupling, each plane counted twice, so the standard `β` is twice it (`GaugeRunning.aRunG`,
  `RectWilson`). `leanStep_eq_runStepG`: at `SU(N)` this is `RunningCrossover.runStepG`, the step of `aOneG_sub_step`.
  It is the step on the window coupling; `stdStep N` in that place would be off by the plane orderings.
* `stdStep_pos`, `leanStep_pos`: positive for `N ≥ 2`. `oneLoopStep_abelian`: `RunningCrossover.oneLoopStep 0 d T = 0`.
* `log2_div_stdStep`, `log2_div_leanStep`, `aOne_SU`: `log 2/c` is `12π²/(11N²)` in the standard coupling and
  `24π²/(11N²)` in the Lean coupling, the rate of `RunningCrossover.aOneG`.

## 2. The shift map (proved)

`shiftMap c β = max (β − c) 0`. `shiftMap_noFixedAbove`: `c > 0` gives `ZoomStep.NoFixedAbove`.
`not_noFixedAbove_shiftMap`: `c ≤ 0` fails it; at `c = 0` the map is the identity on `β ≥ 0`
(`shiftMap_zero`), every point is fixed.

## 3. The named input (cited, not proved)

For a reading `g` and a step `c`:

* `OneLoopZoomOf g c`, the weakest form the chain reads: past some level `β₀`, frequently as `β → ∞`, a reaching zoom
  path from `β` drops by exactly `c` at every coupling at or above `β₀`. Below `β₀` the path is free.
* `OneLoopMapOf g c`, the structural form: one map with no fixed point above `0`, equal to `β − c` past `β₀`.
* `OneLoopZoom N`, `OneLoopMap N`: these at `windowCoupling N` and `leanStep N`.
* `OneLoopShift N`: the literal map `max (β − c) 0` at every `β ≥ 0`. `oneLoopMap_of_shift`: it is the strongest of
  the three. `shift_forces_flat`: it forces `D(β, w + 1) = 0` at every `β ∈ [0, c]`, since the map lands on `β = 0`,
  where the defect is `0`. So the literal form asks the defect to vanish exactly on an interval of positive length;
  on a finite torus the strong-coupling expansion carries wrapping surfaces at every `β > 0` (argued), so it is
  expected to be false, and the named input is not this form.
* `OneLoopAbove N β₀`: the comparison alone, `D(β, w + 1) ≤ D(β − c, w)` at `β ≥ β₀`. This is the part in the
  citation's domain when `β₀` is large; it carries no reach.

## 4. What the input gives (proved)

* `oneLoopZoomOf_of_map`, `oneLoopMap_of_shift`: shift ⇒ map ⇒ path form.
* `zoomReach_of_oneLoopZoom`: `OneLoopZoom N ⇒ ZoomStep.ZoomReach N`. `strongEnd_of_oneLoopZoom`:
  `OneLoopZoom N ⇒ CouplingTower.StrongEnd N`. `vanishes_of_oneLoopMap`: the map form gives the vanishing read at
  every `β ≥ 0`.
* `vanishes_add_nsmul`, `strongEnd_of_oneLoopAbove`: `OneLoopAbove N β₀` with the vanishing read at one point
  `x ≥ 0`, `x + c ≥ β₀`, gives it at `x + n c` for all `n`, so `StrongEnd N`. `strongEnd_of_oneLoopAbove_low`:
  at `β₀ ≤ c` the point `x = 0` serves. So the large-`β` comparison is separated from one read at the bottom of its
  range.
* The count. `doublings_count`: `n = ⌈(β − b)/c⌉₊` is the number of steps from `β ≥ b` to the level `b`:
  `β − n c ≤ b < β − n c + c`. `iterate_shift`, `reach_count`: a map equal to `β − c` past `β₀ ≤ b` has
  `φ^[n] β = β − n c` there. `window_read`: `D(β, w + n) ≤ D(φ^[n] β, w)`. `window_bounds`:
  `e^{(β−b) log 2/c} ≤ 2^n < 2 e^{(β−b) log 2/c}`. `window_bounds_std`: in the standard coupling the window grows as
  `e^{12π²(β−b)/(11N²)}`, the asymptotic-freedom scaling, proved arithmetic; `window_bounds_lean`: the same in the
  Lean coupling at rate `24π²/(11N²)`. It is a statement about `n`, not a measured correlation length.

## 5. Tests (proved)

* Abelian. `not_oneLoopZoomOf_of_nonpos`, `not_oneLoopZoomOf_abelian`: at `c ≤ 0` the input fails for every reading,
  because a path that does not drop stays above its start. So at the `U(1)` coefficient `0` it gives nothing,
  consistent with `PhotonStall.photon_not_strongEnd` and with `RunningCrossover.abelian_no_exit`.
* Stall. `not_oneLoopZoomOf_of_stall`: a reading stalled on a ray fails it at every `c`, through
  `ZoomStep.stall_not_frequently`.
* Non-vacuity. `massiveToy_oneLoopZoom`: `ZoomStep.massiveToy` meets it at `c = 1`.
* Unread coefficient. `strongEnd_of_oneLoopZoomOf`: the chain consumes only `OneLoopZoomOf (windowCoupling N) c` at
  some `c`, and by `not_oneLoopZoomOf_of_nonpos` that `c` is positive. The value `11/3`, the `2N` and the `16π²` enter
  the count of §4 and not the implication to `StrongEnd N`.

## 6. The Clay chain with the input in place (proved, conditional)

* `clayStatement_of_oneLoop`: `OneLoopZoom N` and the residual `ReadPos.ReflFloorAt N βs (2 log 2) ∧ ExistAlong N βs`,
  frequently near `0⁺` along every coupling tower, give `ClayStatementOf (SU N)`.
* `clayStatement_of_oneLoop_open`: the same with `ExistClose.OpenClose` in place of `ExistAlong`.
* `clayStatement_of_oneLoop_tower`: the same with `MeasTowerG` in place of `ReflFloorAt`.
* `clayStatement_of_oneLoopAbove`: `OneLoopAbove N β₀`, one vanishing read at `x`, and the residual.

`clayStatement_of_oneLoop`, `clayStatement_of_oneLoop_open` and `clayStatement_of_oneLoopAbove` are vacuous: each
input gives `StrongEnd N`, under which `ReflFloor.not_floor_residual` refutes the `ReflFloorAt` residual. The
non-vacuous form is `clayStatement_of_oneLoop_tower`.

Inputs remaining besides `OneLoopZoom N`, all along every tower frequently near `0⁺`: `ReflFloorAt` (the window floor
on the reflected tensor read and the mirror-defect bound), and in `OpenClose` the class moments, the two-point kernel
with its asymptotic-freedom coefficient, non-Gaussianity, the Ward identity, `CompOSG` of the composites and
`ApproxAlong`.

## What does not follow

* `OneLoopZoom N` itself. Nothing here proves it, or `ZoomStep.ZoomReach N`, or `StrongEnd N`, for the Wilson measure.
* The domain. The citation concerns `g² → 0`, large `β`. `OneLoopZoom N` also asserts a reaching path through the
  band below `β₀` (the crossover, `RunningCrossover` §3), where one-loop running says nothing. That part is not
  cited; the input carries it as a bare existence. `OneLoopAbove` separates it: its reach is the hypothesis of one
  vanishing read at the bottom of the range.
* The prefactor. One-loop running is a statement about a coupling, and the input is an inequality on `D` with
  prefactor `1`. The only four-dimensional exact comparison in the tree carries a factor `4 = 2^{d−2}`
  (`OneStepZoom.stack_step`), and `OneStepZoom.stack_zoomStepMap_iff` shows what absorbing it asks. Whether the Wilson
  defect meets the inequality at exactly `c` with no prefactor, at every window `w ≥ 1`, is not decided, and no
  perturbative citation decides it.
* The correlation length. `window_bounds_std` counts doublings of the shift. It says nothing about a mass until the
  input and the remaining inputs are supplied.
* The remaining Clay inputs of §6. None is touched. `AFCoefficientG`, inside `OpenClose`, asks the asymptotic-freedom
  coefficient of the two-point kernel on the state, which `OneLoopZoom N` does not supply.

DERIVED (module-wide): `4` and `1/3` the spin and orbital terms (cited split, `FluctSheet`); `11/3 = 4 − 1/3`; `16π²`
the loop measure; `2N` from `β = 2N/g²`; the outer `2` of `stdStep` from `d(1/g²)/d log μ = 2 b₀`; `2` in `log 2` the
one doubling; `2` in `leanStep` the plane orderings; `48 = 3 · 16`; `12π² = 48π²/4` from `2 · 2N · b₀`, and
`24π² = 2 · 12π²` the plane orderings; `0` the trivial coupling and the signs; `1` the least window and the step.
CHOSEN (test only): the step `1` of `massiveToy` is `ZoomStep`'s.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.OneLoopInput

open Filter Topology Real
open MassGap.SUN (SU)
open MassGap.GaugeRunning (b0G b0G_SU)
open MassGap.RunningCrossover (runStepG aOneG oneLoopStep kG kG_mul_runStep runStepG_eq kG_pos)
open MassGap.CouplingTower (windowCoupling StrongEnd CouplingTower windowCoupling_nonneg windowCoupling_zero)
open MassGap.StrongAnchor (Vanishes vanishes_zero)
open MassGap.ZoomStep (ZoomStepMap NoFixedAbove ZoomPath Reaches ZoomReachOf ZoomReach)

/-! ## 1. The coefficient -/

/-- **The spin term** of the gluon one-loop coefficient. DERIVED: cited, `FluctSheet` (Nielsen–Olesen). -/
def spinTerm : ℝ := 4

/-- **The orbital term** of the gluon one-loop coefficient. DERIVED: cited, `FluctSheet` (Nielsen–Olesen). -/
def orbitalTerm : ℝ := 1 / 3

/-- **The gluon coefficient**: spin minus orbital. DERIVED: the signs are antiscreening and screening. -/
def gluonCoeff : ℝ := spinTerm - orbitalTerm

/-- **`4 − 1/3 = 11/3`.** DERIVED: the split above; COMPUTED: `11/3 = 4 − 1/3` from `spinTerm` and
`orbitalTerm`. -/
theorem gluonCoeff_eq : gluonCoeff = 11 / 3 := by unfold gluonCoeff spinTerm orbitalTerm; norm_num

/-- **The loop measure** `16π²`. DERIVED: the one-loop integral in four dimensions. -/
def loopMeasure : ℝ := 16 * π ^ 2

/-- **The one-loop coefficient** at dual Coxeter number `h`, `g`-convention. DERIVED: the two factors above. -/
def b0 (h : ℝ) : ℝ := gluonCoeff * h / loopMeasure

/-- DERIVED: `48 = 3 · 16`; `11` the numerator of `gluonCoeff_eq`. -/
theorem b0_eq (h : ℝ) : b0 h = 11 * h / (48 * π ^ 2) := by
  unfold b0 loopMeasure
  rw [gluonCoeff_eq]
  have hp : π ≠ 0 := pi_ne_zero
  field_simp
  ring

/-- **The abelian coefficient is `0`** (pure `U(1)`, `h = 0`, no matter). DERIVED: `0` the dual Coxeter number. -/
theorem b0_abelian : b0 0 = 0 := by simp [b0]

/-- **The abelian step of `RunningCrossover` is `0`.** DERIVED: `0` the dual Coxeter number. -/
theorem oneLoopStep_abelian (d T : ℝ) : oneLoopStep 0 d T = 0 := by simp [oneLoopStep]

/-- **The rise of the standard coupling `β = 2N/g²` per halving of the spacing.** DERIVED: `2N` from `β = 2N/g²`;
the outer `2` from `d(1/g²)/d log μ = 2 b₀`; `2` in `log 2` one doubling. -/
def stdStep (N : ℕ) : ℝ := 2 * (2 * (N : ℝ)) * b0 N * Real.log 2

/-- **`c_N = 11 N² log 2/(12π²)`.** DERIVED: `12 = 48/4`; `11` the numerator of `gluonCoeff_eq`. -/
theorem stdStep_eq (N : ℕ) : stdStep N = 11 * (N : ℝ) ^ 2 * Real.log 2 / (12 * π ^ 2) := by
  unfold stdStep
  rw [b0_eq]
  have hp : π ≠ 0 := pi_ne_zero
  field_simp
  ring

/-- **The step on the Lean coupling**, the coupling of `windowCoupling`. DERIVED: `2` the orderings of a plane
(`GaugeRunning.aRunG`): the standard coupling is twice the Lean coupling. -/
def leanStep (N : ℕ) : ℝ := stdStep N / 2

/-- DERIVED: `24 = 2 · 12`; `11` the numerator of `gluonCoeff_eq`. -/
theorem leanStep_eq (N : ℕ) : leanStep N = 11 * (N : ℝ) ^ 2 * Real.log 2 / (24 * π ^ 2) := by
  unfold leanStep
  rw [stdStep_eq]
  have hp : π ≠ 0 := pi_ne_zero
  field_simp
  ring

/-- **Positivity at `N ≥ 2`.** DERIVED: `0` the sign; `2` the least rank. -/
theorem stdStep_pos {N : ℕ} (hN : 2 ≤ N) : 0 < stdStep N := by
  rw [stdStep_eq]
  have hl := Real.log_pos (one_lt_two : (1 : ℝ) < 2)
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hp := pi_pos
  positivity

/-- **Positivity at `N ≥ 2`.** DERIVED: `0` the sign; `2` the least rank. -/
theorem leanStep_pos {N : ℕ} (hN : 2 ≤ N) : 0 < leanStep N := by
  have := stdStep_pos hN
  unfold leanStep
  linarith

/-- **`log 2/c_N = 12π²/(11N²)`.** DERIVED: `stdStep_eq`, whose `11` and `12` these are. -/
theorem log2_div_stdStep {N : ℕ} (hN : 2 ≤ N) :
    Real.log 2 / stdStep N = 12 * π ^ 2 / (11 * (N : ℝ) ^ 2) := by
  rw [stdStep_eq]
  have hl := (Real.log_pos (one_lt_two : (1 : ℝ) < 2)).ne'
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hp : π ≠ 0 := pi_ne_zero
  field_simp

/-- **The same rate in the Lean coupling is `24π²/(11N²)`.** DERIVED: `leanStep_eq`, whose `11` and
`24` these are. -/
theorem log2_div_leanStep {N : ℕ} (hN : 2 ≤ N) :
    Real.log 2 / leanStep N = 24 * π ^ 2 / (11 * (N : ℝ) ^ 2) := by
  rw [leanStep_eq]
  have hl := (Real.log_pos (one_lt_two : (1 : ℝ) < 2)).ne'
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hp : π ≠ 0 := pi_ne_zero
  field_simp

section SU

variable (N : ℕ) [NeZero N] [Fact (2 ≤ N)]

/-- **The coefficient is the tree's.** DERIVED: `h^∨ = N`. -/
theorem b0_eq_b0G : b0 N = b0G (SU N) := by rw [b0_eq, b0G_SU]

/-- **The step on the Lean coupling is `RunningCrossover.runStepG`**, the step of `aOneG_sub_step`.
DERIVED: `d = N`, `T = 1/2`. -/
theorem leanStep_eq_runStepG : leanStep N = runStepG (SU N) := by
  rw [runStepG_eq]
  have hd : MassGap.GaugeRunning.dG (SU N) = (N : ℝ) := rfl
  have hT : MassGap.GaugeRunning.TG (SU N) = 1 / 2 := rfl
  rw [hd, hT, ← b0_eq_b0G]
  unfold leanStep stdStep
  ring

/-- **The one-loop spacing at `SU(N)` decays at the rate `log 2/c`.** DERIVED: `kG_mul_runStep`. -/
theorem aOne_SU (β : ℝ) : aOneG (SU N) β = Real.exp (-(Real.log 2 / leanStep N * β)) := by
  have hc : runStepG (SU N) ≠ 0 := (MassGap.RunningCrossover.runStepG_pos (SU N)).ne'
  have hk := kG_mul_runStep (SU N)
  have e : kG (SU N) / 2 = Real.log 2 / runStepG (SU N) := by
    rw [eq_div_iff hc]
    linarith
  unfold aOneG
  rw [leanStep_eq_runStepG, ← e]
  congr 1
  ring

end SU

/-! ## 2. The shift map -/

/-- **The one-loop shift** `β ↦ max (β − c) 0`. DERIVED: `0` the trivial coupling. -/
def shiftMap (c β : ℝ) : ℝ := max (β - c) 0

/-- DERIVED: `0` the sign. -/
theorem shiftMap_nonneg (c β : ℝ) : 0 ≤ shiftMap c β := le_max_right _ _

/-- **A positive step has no fixed point above `0`.** DERIVED: `0` the trivial coupling. -/
theorem shiftMap_noFixedAbove {c : ℝ} (hc : 0 < c) : NoFixedAbove (shiftMap c) :=
  ⟨(continuous_id.sub continuous_const).max continuous_const, fun x hx => max_lt (by linarith) hx⟩

/-- **At step `0` the shift is the identity on `β ≥ 0`.** DERIVED: `0` the abelian coefficient. -/
theorem shiftMap_zero {β : ℝ} (hβ : 0 ≤ β) : shiftMap 0 β = β := by
  simp [shiftMap, hβ]

/-- **A step `c ≤ 0` has a point that does not drop**: `NoFixedAbove` fails. DERIVED: `1` a point above `0`. -/
theorem not_noFixedAbove_shiftMap {c : ℝ} (hc : c ≤ 0) : ¬ NoFixedAbove (shiftMap c) := by
  intro h
  have h1 := h.2 1 one_pos
  have h2 : (1 : ℝ) - c ≤ shiftMap c 1 := le_max_left _ _
  linarith

/-! ## 3. The named input -/

/-- **The running in path form on a reading `g`**: past a level `β₀`, frequently as `β → ∞`, a reaching zoom path
from `β` drops by exactly `c` at every coupling at or above `β₀`. DERIVED: `0` the start; `1` the step. -/
def OneLoopZoomOf (g : ℝ → ℕ → ℝ) (c : ℝ) : Prop :=
  ∃ β₀ : ℝ, ∃ᶠ β in atTop, ∃ βs : ℕ → ℝ, βs 0 = β ∧ ZoomPath g βs ∧ Reaches βs ∧
    ∀ k : ℕ, β₀ ≤ βs k → βs (k + 1) = βs k - c

/-- **The running in map form on a reading `g`**: one zoom map with no fixed point above `0`, equal to `β − c` past
a level `β₀`. DERIVED: no numeral. -/
def OneLoopMapOf (g : ℝ → ℕ → ℝ) (c : ℝ) : Prop :=
  ∃ φ : ℝ → ℝ, ZoomStepMap g φ ∧ NoFixedAbove φ ∧ ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β → φ β = β - c

/-- **The one-loop zoom** (the named input). Cited: asymptotic freedom, Gross–Wilczek 1973, Politzer 1973; perturbative,
valid as `g² → 0`. This is the running written in the shape of the zoom step, on the Wilson window coupling, at the
step `leanStep N` of the Lean coupling. It is not a theorem about the lattice Wilson measure at finite `β`, it is not
proved here or anywhere in the tree, and it is the whole non-abelian content of this route. It also asserts the reach
through the crossover, which the citation does not cover (module docstring). DERIVED: `leanStep N`. -/
def OneLoopZoom (N : ℕ) : Prop := OneLoopZoomOf (windowCoupling N) (leanStep N)

/-- **The one-loop zoom in map form.** Cited in the same sense as `OneLoopZoom`, and at least as strong.
DERIVED: `leanStep N`. -/
def OneLoopMap (N : ℕ) : Prop := OneLoopMapOf (windowCoupling N) (leanStep N)

/-- **The literal shift at every `β ≥ 0`.** Stronger than `OneLoopMap`, and it forces the defect to vanish exactly
on `[0, c]` (`shift_forces_flat`), so it is not the named input. DERIVED: `leanStep N`. -/
def OneLoopShift (N : ℕ) : Prop := ZoomStepMap (windowCoupling N) (shiftMap (leanStep N))

/-- **The comparison above a level.** Cited in its domain when `β₀` is large: no reach is asserted.
DERIVED: `1` the least window and the step. -/
def OneLoopAbove (N : ℕ) (β₀ : ℝ) : Prop :=
  ∀ β : ℝ, β₀ ≤ β → ∀ w : ℕ, 1 ≤ w → windowCoupling N β (w + 1) ≤ windowCoupling N (β - leanStep N) w

/-! ## 4. What the input gives -/

/-- **The map form gives the path form.** DERIVED: `0` the sign of `β`. -/
theorem oneLoopZoomOf_of_map {g : ℝ → ℕ → ℝ} {c : ℝ} (h : OneLoopMapOf g c) : OneLoopZoomOf g c := by
  obtain ⟨φ, hm, hfix, β₀, hs⟩ := h
  refine ⟨β₀, ((eventually_ge_atTop 0).mono fun β hβ => ?_).frequently⟩
  refine ⟨fun k => φ^[k] β, rfl, ZoomStep.zoomPath_of_map hm hβ,
    ZoomStep.reaches_of_noFixedAbove hm.1 hfix hβ, fun k hk => ?_⟩
  simp only [Function.iterate_succ_apply']
  exact hs _ hk

/-- **The literal shift gives the map form.** DERIVED: `2` the least rank. -/
theorem oneLoopMap_of_shift {N : ℕ} (hN : 2 ≤ N) (h : OneLoopShift N) : OneLoopMap N :=
  ⟨shiftMap (leanStep N), h, shiftMap_noFixedAbove (leanStep_pos hN), leanStep N, fun β hβ =>
    max_eq_left (by linarith)⟩

/-- **The literal shift forces the defect flat on `[0, c]`**: past the first window the defect there is exactly `0`,
since the map lands on `β = 0`. DERIVED: `0` the ultralocal coupling; `1` the least window. -/
theorem shift_forces_flat {N : ℕ} (hN : N ≠ 0) (h : OneLoopShift N) {β : ℝ} (h0 : 0 ≤ β) (hβ : β ≤ leanStep N)
    {w : ℕ} (hw : 1 ≤ w) : windowCoupling N β (w + 1) = 0 := by
  have h1 := h.2 β h0 w hw
  have e : shiftMap (leanStep N) β = 0 := max_eq_right (by linarith)
  rw [e, windowCoupling_zero] at h1
  exact le_antisymm h1 (windowCoupling_nonneg hN h0 (by omega))

/-- **The chain reads the reach**: the input at any step gives `ZoomStep.ZoomReach`. DERIVED: no numeral. -/
theorem zoomReach_of_oneLoopZoomOf {N : ℕ} {c : ℝ} (h : OneLoopZoomOf (windowCoupling N) c) : ZoomReach N := by
  obtain ⟨_, h⟩ := h
  exact h.mono fun _ ⟨βs, h0, hp, hr, _⟩ => ⟨βs, h0, hp, hr⟩

/-- **`OneLoopZoom N` gives `ZoomStep.ZoomReach N`.** DERIVED: no numeral. -/
theorem zoomReach_of_oneLoopZoom {N : ℕ} (h : OneLoopZoom N) : ZoomReach N := zoomReach_of_oneLoopZoomOf h

/-- **The input at any step gives the strong end**: the implication reads no value of `c`. DERIVED: `0` the
excluded rank. -/
theorem strongEnd_of_oneLoopZoomOf {N : ℕ} (hN : N ≠ 0) {c : ℝ} (h : OneLoopZoomOf (windowCoupling N) c) :
    StrongEnd N :=
  ZoomStep.strongEnd_of_zoomReach hN (zoomReach_of_oneLoopZoomOf h)

/-- **`OneLoopZoom N` gives the strong end.** DERIVED: `0` the excluded rank. -/
theorem strongEnd_of_oneLoopZoom {N : ℕ} (hN : N ≠ 0) (h : OneLoopZoom N) : StrongEnd N :=
  strongEnd_of_oneLoopZoomOf hN h

/-- **The map form gives the vanishing read at every `β ≥ 0`.** DERIVED: `0` the sign and the excluded rank. -/
theorem vanishes_of_oneLoopMap {N : ℕ} (hN : N ≠ 0) (h : OneLoopMap N) {β : ℝ} (hβ : 0 ≤ β) : Vanishes N β := by
  obtain ⟨φ, hm, hfix, _⟩ := h
  exact ZoomStep.vanishes_of_wilsonZoomStep hN ⟨φ, hm, hfix⟩ hβ

/-- **One step passes the vanishing read up.** DERIVED: `0` the limit and the signs; `1` the least window. -/
theorem vanishes_of_step {N : ℕ} (hN : N ≠ 0) {β β' : ℝ} (hβ : 0 ≤ β)
    (hs : ∀ w : ℕ, 1 ≤ w → windowCoupling N β (w + 1) ≤ windowCoupling N β' w) (hv : Vanishes N β') :
    Vanishes N β := by
  have ht : Tendsto (fun w => windowCoupling N β (w + 1)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hv ?_ ?_
    · exact Eventually.of_forall fun w => windowCoupling_nonneg hN hβ (by omega)
    · filter_upwards [eventually_ge_atTop 1] with w hw
      exact hs w hw
  exact (tendsto_add_atTop_iff_nat 1).mp ht

/-- **The comparison carries one vanishing read up the whole lattice `x + n c`.** DERIVED: `0` the sign and the
excluded rank; `1` the step. -/
theorem vanishes_add_nsmul {N : ℕ} (hN : 2 ≤ N) {β₀ x : ℝ} (h : OneLoopAbove N β₀) (hx : 0 ≤ x)
    (hle : β₀ ≤ x + leanStep N) (hv : Vanishes N x) (n : ℕ) : Vanishes N (x + n * leanStep N) := by
  have hc := leanStep_pos hN
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    have hn : (0 : ℝ) ≤ n * leanStep N := by positivity
    have e : x + ((n + 1 : ℕ) : ℝ) * leanStep N - leanStep N = x + n * leanStep N := by push_cast; ring
    have hβ : β₀ ≤ x + ((n + 1 : ℕ) : ℝ) * leanStep N := by push_cast; nlinarith
    refine vanishes_of_step (by omega) (by positivity) (fun w hw => ?_) ih
    have := h _ hβ w hw
    rwa [e] at this

/-- **The comparison and one vanishing read give the strong end.** The comparison may sit at large `β`; the read at
the bottom of its range is what it does not supply. DERIVED: `0` the sign; `2` the least rank. -/
theorem strongEnd_of_oneLoopAbove {N : ℕ} (hN : 2 ≤ N) {β₀ x : ℝ} (h : OneLoopAbove N β₀) (hx : 0 ≤ x)
    (hle : β₀ ≤ x + leanStep N) (hv : Vanishes N x) : StrongEnd N := by
  have hc := leanStep_pos hN
  refine frequently_atTop.mpr fun a => ?_
  obtain ⟨n, hn⟩ := exists_nat_ge ((a - x) / leanStep N)
  refine ⟨x + n * leanStep N, ?_, vanishes_add_nsmul hN h hx hle hv n⟩
  have := (div_le_iff₀ hc).mp hn
  linarith

/-- **At `β₀ ≤ c` the comparison alone gives the strong end**, from the read `D(0, ·) = 0`. DERIVED: `0` the
ultralocal coupling; `2` the least rank. -/
theorem strongEnd_of_oneLoopAbove_low {N : ℕ} (hN : 2 ≤ N) {β₀ : ℝ} (h : OneLoopAbove N β₀)
    (hle : β₀ ≤ leanStep N) : StrongEnd N :=
  strongEnd_of_oneLoopAbove hN h le_rfl (by linarith) vanishes_zero

/-! ### The count of doublings -/

/-- **The number of doublings from `β` to the level `b`** is `⌈(β − b)/c⌉₊`. DERIVED: `0` the sign. -/
theorem doublings_count {b c β : ℝ} (hc : 0 < c) (hb : b ≤ β) :
    β - (⌈(β - b) / c⌉₊ : ℝ) * c ≤ b ∧ b < β - (⌈(β - b) / c⌉₊ : ℝ) * c + c := by
  have h0 : 0 ≤ (β - b) / c := div_nonneg (by linarith) hc.le
  have h1 := mul_le_mul_of_nonneg_right (Nat.le_ceil ((β - b) / c)) hc.le
  have h2 := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one h0) hc
  rw [div_mul_cancel₀ _ hc.ne'] at h1
  rw [add_mul, div_mul_cancel₀ _ hc.ne', one_mul] at h2
  exact ⟨by linarith, by linarith⟩

/-- **The iterates follow the shift while they stay above `β₀`.** DERIVED: `0` the start; `1` the step. -/
theorem iterate_shift {φ : ℝ → ℝ} {β₀ c : ℝ} (hs : ∀ x : ℝ, β₀ ≤ x → φ x = x - c) (β : ℝ) :
    ∀ k : ℕ, (∀ j : ℕ, j < k → β₀ ≤ β - j * c) → φ^[k] β = β - k * c := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro h
    have hk := ih fun j hj => h j (by omega)
    rw [Function.iterate_succ_apply', hk, hs _ (h k (by omega))]
    push_cast
    ring

/-- **A map equal to the shift past `β₀ ≤ b` reaches the level `b` in `⌈(β − b)/c⌉₊` steps.** DERIVED: `0` the
sign; `1` the step. -/
theorem reach_count {φ : ℝ → ℝ} {β₀ b c β : ℝ} (hc : 0 < c) (hs : ∀ x : ℝ, β₀ ≤ x → φ x = x - c) (hb₀ : β₀ ≤ b)
    (hb : b ≤ β) :
    φ^[⌈(β - b) / c⌉₊] β = β - (⌈(β - b) / c⌉₊ : ℝ) * c ∧ φ^[⌈(β - b) / c⌉₊] β ≤ b := by
  obtain ⟨h1, h2⟩ := doublings_count hc hb
  have e := iterate_shift hs β ⌈(β - b) / c⌉₊ fun j hj => by
    have hj' : ((j : ℝ) + 1) ≤ (⌈(β - b) / c⌉₊ : ℝ) := by exact_mod_cast hj
    have := mul_le_mul_of_nonneg_right hj' hc.le
    rw [add_mul, one_mul] at this
    linarith
  exact ⟨e, by rw [e]; exact h1⟩

/-- **The window comparison along the map**: `D(β, w + n) ≤ D(φ^[n] β, w)`. DERIVED: `0` the sign; `1` the least
window. -/
theorem window_read {g : ℝ → ℕ → ℝ} {φ : ℝ → ℝ} (h : ZoomStepMap g φ) {β : ℝ} (hβ : 0 ≤ β) (n w : ℕ)
    (hw : 1 ≤ w) : g β (w + n) ≤ g (φ^[n] β) w :=
  ZoomStep.path_le (ZoomStep.zoomPath_of_map h hβ) n w hw

/-- **The window reached**: `e^{(β−b) log 2/c} ≤ 2^n < 2 e^{(β−b) log 2/c}` at `n = ⌈(β − b)/c⌉₊`.
DERIVED: `2` the doubling. -/
theorem window_bounds {b c β : ℝ} (hc : 0 < c) (hb : b ≤ β) :
    Real.exp ((β - b) * (Real.log 2 / c)) ≤ (2 : ℝ) ^ ⌈(β - b) / c⌉₊ ∧
      (2 : ℝ) ^ ⌈(β - b) / c⌉₊ < 2 * Real.exp ((β - b) * (Real.log 2 / c)) := by
  have hl := Real.log_pos (one_lt_two : (1 : ℝ) < 2)
  have h0 : 0 ≤ (β - b) / c := div_nonneg (by linarith) hc.le
  have h2 : ((2 : ℝ) ^ ⌈(β - b) / c⌉₊) = Real.exp ((⌈(β - b) / c⌉₊ : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log two_pos]
  have e : (β - b) * (Real.log 2 / c) = (β - b) / c * Real.log 2 := by ring
  rw [h2, e]
  constructor
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (Nat.le_ceil _) hl.le)
  · have hlt := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one h0) hl
    rw [add_mul, one_mul] at hlt
    calc Real.exp ((⌈(β - b) / c⌉₊ : ℝ) * Real.log 2)
        < Real.exp ((β - b) / c * Real.log 2 + Real.log 2) := Real.exp_lt_exp.mpr hlt
      _ = 2 * Real.exp ((β - b) / c * Real.log 2) := by
          rw [Real.exp_add, Real.exp_log two_pos]; ring

/-- **The asymptotic-freedom scaling in the standard coupling** (proved arithmetic): the window grows as
`e^{12π²(β−b)/(11N²)}`. DERIVED: `log2_div_stdStep`, whose `11` and `12` these are. -/
theorem window_bounds_std {N : ℕ} (hN : 2 ≤ N) {b β : ℝ} (hb : b ≤ β) :
    Real.exp ((β - b) * (12 * π ^ 2 / (11 * (N : ℝ) ^ 2))) ≤ (2 : ℝ) ^ ⌈(β - b) / stdStep N⌉₊ ∧
      (2 : ℝ) ^ ⌈(β - b) / stdStep N⌉₊ < 2 * Real.exp ((β - b) * (12 * π ^ 2 / (11 * (N : ℝ) ^ 2))) := by
  rw [← log2_div_stdStep hN]
  exact window_bounds (stdStep_pos hN) hb

/-- **The same in the Lean coupling**, at twice the rate. DERIVED: `log2_div_leanStep`, whose `11` and
`24` these are. -/
theorem window_bounds_lean {N : ℕ} (hN : 2 ≤ N) {b β : ℝ} (hb : b ≤ β) :
    Real.exp ((β - b) * (24 * π ^ 2 / (11 * (N : ℝ) ^ 2))) ≤ (2 : ℝ) ^ ⌈(β - b) / leanStep N⌉₊ ∧
      (2 : ℝ) ^ ⌈(β - b) / leanStep N⌉₊ < 2 * Real.exp ((β - b) * (24 * π ^ 2 / (11 * (N : ℝ) ^ 2))) := by
  rw [← log2_div_leanStep hN]
  exact window_bounds (leanStep_pos hN) hb

/-! ## 5. Tests -/

/-- **A step `c ≤ 0` fails for every reading**: a path that does not drop stays above its start, so it cannot reach.
This is the `U(1)` coefficient `0`, and matter with `b₀ < 0`. DERIVED: `1` a level above `0`. -/
theorem not_oneLoopZoomOf_of_nonpos (g : ℝ → ℕ → ℝ) {c : ℝ} (hc : c ≤ 0) : ¬ OneLoopZoomOf g c := by
  rintro ⟨β₀, h⟩
  obtain ⟨β, ⟨βs, h0, -, hr, hs⟩, hβ⟩ := (h.and_eventually (eventually_ge_atTop (max β₀ 1))).exists
  have hβ₀ : β₀ ≤ β := le_trans (le_max_left _ _) hβ
  have h1 : 1 ≤ β := le_trans (le_max_right _ _) hβ
  have key : ∀ k, β ≤ βs k := by
    intro k
    induction k with
    | zero => exact h0.ge
    | succ k ih =>
      rw [hs k (hβ₀.trans ih)]
      linarith
  obtain ⟨k, hk⟩ := hr 1 one_pos
  have := key k
  linarith

/-- **The `U(1)` step gives nothing.** DERIVED: `0` the abelian coefficient. -/
theorem not_oneLoopZoomOf_abelian (g : ℝ → ℕ → ℝ) (d T : ℝ) : ¬ OneLoopZoomOf g (oneLoopStep 0 d T) :=
  not_oneLoopZoomOf_of_nonpos g (oneLoopStep_abelian d T).le

/-- **A reading stalled on a ray fails the input at every step.** DERIVED: `0` the signs. -/
theorem not_oneLoopZoomOf_of_stall {g : ℝ → ℕ → ℝ} {b₀ s : ℝ} (hb₀ : 0 < b₀) (hs : 0 < s)
    (hstall : ∀ β : ℝ, b₀ ≤ β → ∀ w : ℕ, g β w = s)
    (hvan : ∀ β : ℝ, 0 ≤ β → β < b₀ → Tendsto (g β) atTop (𝓝 0)) (c : ℝ) : ¬ OneLoopZoomOf g c := by
  rintro ⟨_, h⟩
  exact ZoomStep.stall_not_frequently hb₀ hs hstall hvan (h.mono fun _ ⟨βs, h0, hp, hr, _⟩ => ⟨βs, h0, hp, hr⟩)

/-- **The input is inhabited on a free massive-type reading.** CHOSEN: the step `1` of `ZoomStep.massiveToy`. -/
theorem massiveToy_oneLoopZoom : OneLoopZoomOf ZoomStep.massiveToy 1 :=
  oneLoopZoomOf_of_map ⟨ZoomStep.unitShift, ZoomStep.massiveToy_step, ZoomStep.unitShift_noFixedAbove, 1,
    fun β hβ => max_eq_left (by linarith)⟩

/-! ## 6. The Clay chain with the input in place -/

section Clay

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

open MassGap.ClayStatementG (ClayStatementOf)
open MassGap.MeasuredTower (MeasTowerG)
open MassGap.ConstantPhysicsLine (ExistAlong)
open MassGap.ReadPos (ReflFloorAt)

/-- **The root at `SU(N)` from the one-loop zoom.** `OneLoopZoom N` and, at window couplings arbitrarily close to
`0⁺`, `ReflFloorAt N βs (2 log 2)` and `ExistAlong N βs` along every coupling tower. DERIVED: `0` the limit `0⁺`;
`2` the band ratio. Inherited: `log 2` the window rate. -/
theorem clayStatement_of_oneLoop (hZ : OneLoopZoom N)
    (hR : ∃ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      ReflFloorAt N βs (2 * Real.log 2) ∧ ExistAlong N βs) :
    ClayStatementOf (SU N) :=
  ReadPos.clayStatement_of_strongEnd_floor (strongEnd_of_oneLoopZoom (NeZero.ne N) hZ) hR

/-- **The root from the one-loop zoom, with every proved existence clause removed**: `ExistClose.OpenClose` in place
of `ExistAlong`. DERIVED: `0` the limit `0⁺`; `2` the band ratio. Inherited: `log 2` the window rate. -/
theorem clayStatement_of_oneLoop_open (hZ : OneLoopZoom N)
    (hR : ∃ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      ReflFloorAt N βs (2 * Real.log 2) ∧ ExistClose.OpenClose N βs) :
    ClayStatementOf (SU N) :=
  clayStatement_of_oneLoop hZ (hR.mono fun _ h βs hT =>
    ⟨(h βs hT).1, ExistClose.existAlong_of_openClose (h βs hT).2⟩)

/-- **The root from the one-loop zoom with the measured tower.** DERIVED: `0` the limit `0⁺`. -/
theorem clayStatement_of_oneLoop_tower (hZ : OneLoopZoom N)
    (hR : ∃ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      MeasTowerG (SU N) βs ∧ ExistClose.OpenClose N βs) :
    ClayStatementOf (SU N) :=
  ExistClose.clayStatement_of_strongEnd_open' (strongEnd_of_oneLoopZoom (NeZero.ne N) hZ) hR

/-- **The root from the comparison alone and one vanishing read**: the part of the input inside the citation's domain
is named apart from the read at the bottom of its range. DERIVED: `0` the limit `0⁺` and the sign; `2` the band
ratio. Inherited: `log 2` the window rate. -/
theorem clayStatement_of_oneLoopAbove {β₀ x : ℝ} (hA : OneLoopAbove N β₀) (hx : 0 ≤ x)
    (hle : β₀ ≤ x + leanStep N) (hv : Vanishes N x)
    (hR : ∃ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      ReflFloorAt N βs (2 * Real.log 2) ∧ ExistClose.OpenClose N βs) :
    ClayStatementOf (SU N) :=
  ReadPos.clayStatement_of_strongEnd_floor (strongEnd_of_oneLoopAbove (Fact.out : 2 ≤ N) hA hx hle hv)
    (hR.mono fun _ h βs hT => ⟨(h βs hT).1, ExistClose.existAlong_of_openClose (h βs hT).2⟩)

end Clay

end MassGap.OneLoopInput

end

#print axioms MassGap.OneLoopInput.gluonCoeff_eq
#print axioms MassGap.OneLoopInput.b0_eq
#print axioms MassGap.OneLoopInput.b0_abelian
#print axioms MassGap.OneLoopInput.oneLoopStep_abelian
#print axioms MassGap.OneLoopInput.stdStep_eq
#print axioms MassGap.OneLoopInput.leanStep_eq
#print axioms MassGap.OneLoopInput.stdStep_pos
#print axioms MassGap.OneLoopInput.leanStep_pos
#print axioms MassGap.OneLoopInput.log2_div_stdStep
#print axioms MassGap.OneLoopInput.log2_div_leanStep
#print axioms MassGap.OneLoopInput.b0_eq_b0G
#print axioms MassGap.OneLoopInput.leanStep_eq_runStepG
#print axioms MassGap.OneLoopInput.aOne_SU
#print axioms MassGap.OneLoopInput.shiftMap_nonneg
#print axioms MassGap.OneLoopInput.shiftMap_noFixedAbove
#print axioms MassGap.OneLoopInput.shiftMap_zero
#print axioms MassGap.OneLoopInput.not_noFixedAbove_shiftMap
#print axioms MassGap.OneLoopInput.oneLoopZoomOf_of_map
#print axioms MassGap.OneLoopInput.oneLoopMap_of_shift
#print axioms MassGap.OneLoopInput.shift_forces_flat
#print axioms MassGap.OneLoopInput.zoomReach_of_oneLoopZoomOf
#print axioms MassGap.OneLoopInput.zoomReach_of_oneLoopZoom
#print axioms MassGap.OneLoopInput.strongEnd_of_oneLoopZoomOf
#print axioms MassGap.OneLoopInput.strongEnd_of_oneLoopZoom
#print axioms MassGap.OneLoopInput.vanishes_of_oneLoopMap
#print axioms MassGap.OneLoopInput.vanishes_of_step
#print axioms MassGap.OneLoopInput.vanishes_add_nsmul
#print axioms MassGap.OneLoopInput.strongEnd_of_oneLoopAbove
#print axioms MassGap.OneLoopInput.strongEnd_of_oneLoopAbove_low
#print axioms MassGap.OneLoopInput.doublings_count
#print axioms MassGap.OneLoopInput.iterate_shift
#print axioms MassGap.OneLoopInput.reach_count
#print axioms MassGap.OneLoopInput.window_read
#print axioms MassGap.OneLoopInput.window_bounds
#print axioms MassGap.OneLoopInput.window_bounds_std
#print axioms MassGap.OneLoopInput.window_bounds_lean
#print axioms MassGap.OneLoopInput.not_oneLoopZoomOf_of_nonpos
#print axioms MassGap.OneLoopInput.not_oneLoopZoomOf_abelian
#print axioms MassGap.OneLoopInput.not_oneLoopZoomOf_of_stall
#print axioms MassGap.OneLoopInput.massiveToy_oneLoopZoom
#print axioms MassGap.OneLoopInput.clayStatement_of_oneLoop
#print axioms MassGap.OneLoopInput.clayStatement_of_oneLoop_open
#print axioms MassGap.OneLoopInput.clayStatement_of_oneLoop_tower
#print axioms MassGap.OneLoopInput.clayStatement_of_oneLoopAbove
