import Mathlib
import MassGap.ApertureThing
import MassGap.BandUpper

/-!
# MassGap.StepPeriodic — the reflected read of the step states is a covariance of the periodic state

`BandUpper` names two links between the proved reflection-positivity facts and its window upper bound
`BandUpper.WindowUpper`. This module reads the first: how the reflected read `ApertureThing.gK` of the step
states relates to `FocusZoom.stateCov` of `GaugeWilson.periodicStateG (SU N) β`. Declarations are in the
namespace `MassGap.StepPeriodic`.

## 1. The step state is the periodic state (proved, `rfl`)

* `stateK_eq_periodicStateG`: `ContinuumSchwinger.stateK hN k` is `periodicStateG (SU N) (dyBeta k)`, by
  definition. `stateK` is the dyadic schedule `dyBeta` of the periodic state; `stateAlong βs k` is the same
  state along any tower.

## 2. The reflected read at any coupling (proved)

* `gP β X m := periodicStateG (SU N) β (θX · T_{2m e₀} X)`, `θ = ireflObs 0 0`; `gK_eq_gP`: `gK k = gP (dyBeta k)`.
* `reflShiftP`: the reflection form of `periodicStateG (SU N) β` with the time step is an
  `ApertureThing.ReflShift` at every `β`, so `periodic_far_ge`, the log-convexity of
  `ApertureThing.stateK_far_ge`, holds for the periodic state at the coupling of any tower step, not only on
  the dyadic schedule.

## 3. The exact identification (proved)

* `gP_conn`: for the centred observable `connP β X = X − ν(X)·1` (`ν` the periodic state at `β`),
  `gP β (connP β X) m = stateCov ν (θX) (T_{2m e₀} X)`. Only translation invariance of `ν` enters; the
  reflection invariance is not needed. `gK_connObs_eq_stateCov` is the same at the step states.

So the identification holds exactly after centring, and it is a covariance of `θX` with a translate of `X`,
not of `X` with a translate of `X`.

## 4. The composition (proved)

* `windowUpper_of_reads`: along a tower `βs`, if eventually some half-space `X` has a positive contact read
  `g(0)`, a window-scale floor `g(0) e^{−2 m₁ U/2^k} ≤ g(m₁)` of its centred reflected read, and the
  reflected covariance `stateCov ν (θX) (T_{2m e₀} X)` is dominated in absolute value by the tensor
  covariance at a separation of sup-norm `2m`, then `WindowUpper N βs U`.

## What does not follow, plainly

* The identification with the tensor reading of the target is not an equality. `BandUpper` needs
  `|g m| ≤ |stateCov ν (E x) (E (x + z_m))|` with `E = tensorEnergyG` on both sides; `gP_conn` gives
  `stateCov ν (θX) (T X)`. For this to be the diagonal tensor covariance, `θX` would have to be a translate of
  `X = tensorEnergyG y`. Argued from the geometry, not formalised (up to the orientation sign of each plaquette): every time reflection moves the
  `(0,1)`-plaquette, which extends in time, to base `ρy − e₀`, and the `(2,3)`-plaquette to base `ρy`, so
  `θ(tensorEnergyG y)` is `P₀₁(ρy − e₀) − P₂₃(ρy)`, not a tensor reading at one site; the same holds for a
  reflection along any axis, since each axis lies in one of the two planes. The domination hypothesis of
  `windowUpper_of_reads` is therefore a hypothesis, not discharged: it is the mixed-to-diagonal part of link 1.
* Link 2, the floor of one reflected read at the window scale from the tower's defining free-energy read
  (`CouplingTower.windowCoupling`), is not touched. No theorem found bounds a reflected read of the periodic
  state below in terms of the window coupling.
  This module
  reduces `WindowUpper` to the domination hypothesis (1′) and the window-scale floor (link 2); neither is
  discharged.

DERIVED (module-wide): `0` the plane `x₀ = 0`, the time axis, the contact gap and the signs; `1` the unit
time step and the least gap index; `2` the two lattice steps of one reflected gap and the window base. No
constant is inherited in this module.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.StepPeriodic

open Filter Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.JointRP
  MassGap.ApertureThing
open MassGap.MeasuredTower
open MassGap.MeasuredSpacing (mU mUG_SU)

variable {N : ℕ} [NeZero N]

/-! ## 1. The step state -/

/-- **The step state is the periodic state at the dyadic coupling**, by definition. DERIVED: no numeral. -/
theorem stateK_eq_periodicStateG (k : ℕ) :
    stateK (NeZero.ne N) k
      = GaugeWilson.periodicStateG (MassGap.SUN.SU N) (dyBeta (one_le_of_ne_zero (NeZero.ne N)) k) :=
  rfl

/-! ## 2. The reflected read at any coupling -/

/-- **The periodic state is translation invariant** at every coupling. DERIVED: `0` the placeholder step
index of the constant tower. -/
theorem periodic_transObs (β : ℝ) (x : ISite) (F : C(Cfg N, ℝ)) :
    GaugeWilson.periodicStateG (MassGap.SUN.SU N) β (transObs x F)
      = GaugeWilson.periodicStateG (MassGap.SUN.SU N) β F :=
  MassGap.ContinuumNontrivial.stateAlong_transObs (NeZero.ne N) (fun _ => β) 0 x F

/-- **The time-reflection form of the periodic state at `β`** about `x₀ = 0`. DERIVED: `0` the plane and
the axis. -/
abbrev bP (β : ℝ) : C(Cfg N, ℝ) →ₗ[ℝ] C(Cfg N, ℝ) →ₗ[ℝ] ℝ :=
  rform (GaugeWilson.periodicStateG (MassGap.SUN.SU N) β) (LatticeReflection.ireflObs 0 0)

/-- **The reflected read of the periodic state at gap `2m`**: `ν_β (θX · T_{2m e₀} X)`. DERIVED: `0` the
plane; `2` the two steps of one gap. -/
def gP (β : ℝ) (X : C(Cfg N, ℝ)) (m : ℕ) : ℝ :=
  GaugeWilson.periodicStateG (MassGap.SUN.SU N) β
    (LatticeReflection.ireflObs 0 0 X * transObs ((2 * m) • eT) X)

/-- **The step read is the periodic read at the dyadic coupling.** DERIVED: no numeral. -/
theorem gK_eq_gP (k : ℕ) (X : C(Cfg N, ℝ)) (m : ℕ) :
    gK k X m = gP (dyBeta (one_le_of_ne_zero (NeZero.ne N)) k) X m :=
  rfl

/-- **The time step is symmetric for the periodic reflection form.** DERIVED: `0` the plane. -/
theorem bP_shift (β : ℝ) (x y : C(Cfg N, ℝ)) : bP β (tStep x) y = bP β x (tStep y) := by
  simp only [bP, rform_apply, tStep]
  rw [ireflObs_transObs, ireflSite_eT]
  have e : transObs (-eT) (LatticeReflection.ireflObs 0 0 x) * y
      = transObs (-eT) (LatticeReflection.ireflObs 0 0 x * transObs eT y) := by
    rw [transObs_mul, transObs_transObs, neg_add_cancel, transObs_zero]
  rw [e, periodic_transObs]

/-- **The periodic reflection form with the time step is a `ReflShift`** at every coupling. DERIVED: `0`
the plane and the placeholder step index. -/
theorem reflShiftP (β : ℝ) :
    ReflShift (bP (N := N) β) (HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0) tStep where
  symm x y := refl_pair_symm (GaugeWilson.periodicStateG (MassGap.SUN.SU N) β) 0
    (PeriodicState.periodicState_reflInvariant (NeZero.ne N) β 0 0) x y
  pos x hx := stateAlong_rp (NeZero.ne N) (fun _ => β) 0 0 x hx
  maps _ hx := tStep_mem hx
  shift x y := bP_shift β x y

/-- **The gap read is the periodic reflected read at gap `2m`.** DERIVED: `2` the two steps. -/
theorem gapRead_eq_P (β : ℝ) (X : C(Cfg N, ℝ)) (m : ℕ) : gapRead (bP β) tStep X m = gP β X m := by
  unfold gapRead
  rw [shift_pow (reflShiftP β) X ((tStep ^ m) X) m]
  have e : (tStep (N := N) ^ m) ((tStep ^ m) X) = (tStep ^ (2 * m)) X := by
    rw [two_mul, pow_add, Module.End.mul_apply]
  rw [e, tStep_pow]
  rfl

/-- **The outside from the inside, at every coupling**: for `X` in the positive half-space algebra and
`m₁ ≤ m`, `gP β X m₁ ^ m ≤ gP β X m ^ m₁ · gP β X 0 ^ (m − m₁)`. DERIVED: `0` the plane and the contact
gap. -/
theorem periodic_far_ge (β : ℝ) {X : C(Cfg N, ℝ)}
    (hX : X ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0) {m₁ m : ℕ} (hm : m₁ ≤ m) :
    gP β X m₁ ^ m ≤ gP β X m ^ m₁ * gP β X 0 ^ (m - m₁) := by
  have h := gapRead_far_ge (reflShiftP β) hX hm
  simpa only [gapRead_eq_P] using h

/-! ## 3. The exact identification -/

/-- **The centred observable at `β`**: `X − ν_β(X)·1`. DERIVED: `1` the constant observable. -/
def connP (β : ℝ) (X : C(Cfg N, ℝ)) : C(Cfg N, ℝ) :=
  X - GaugeWilson.periodicStateG (MassGap.SUN.SU N) β X • (1 : C(Cfg N, ℝ))

/-- The centred observable of a half-space observable is a half-space observable. DERIVED: `0` the
plane. -/
theorem connP_mem (β : ℝ) {X : C(Cfg N, ℝ)}
    (hX : X ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0) :
    connP β X ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 :=
  Submodule.sub_mem _ hX (Submodule.smul_mem _ _ one_mem_halfSpace)

/-- **The centred reflected read is a covariance of the periodic state**:
`gP β (connP β X) m = stateCov ν_β (θX) (T_{2m e₀} X)`. Only translation invariance enters. DERIVED: `0`
the plane; `2` the two steps of one gap; `1` the constant observable. -/
theorem gP_conn (β : ℝ) (X : C(Cfg N, ℝ)) (m : ℕ) :
    gP β (connP β X) m = FocusZoom.stateCov (GaugeWilson.periodicStateG (MassGap.SUN.SU N) β)
      (LatticeReflection.ireflObs 0 0 X) (transObs ((2 * m) • eT) X) := by
  unfold gP connP FocusZoom.stateCov
  set ν := GaugeWilson.periodicStateG (MassGap.SUN.SU N) β with hν
  set c := ν X with hc
  set a := LatticeReflection.ireflObs 0 0 X with ha
  set b := transObs ((2 * m) • eT) X with hb
  have h1 : LatticeReflection.ireflObs (G := MassGap.SUN.SU N) 0 0 (1 : C(Cfg N, ℝ)) = 1 := rfl
  have h2 : transObs (G := MassGap.SUN.SU N) ((2 * m) • eT) (1 : C(Cfg N, ℝ)) = 1 := rfl
  rw [map_sub, map_sub, map_smul, map_smul, h1, h2, ← ha, ← hb]
  have e : (a - c • (1 : C(Cfg N, ℝ))) * (b - c • 1) = a * b - c • a - c • b + (c * c) • 1 := by
    ext U
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul]
    ring
  have hbν : ν b = c := periodic_transObs β _ X
  rw [e, ν.map_add, ν.map_sub, ν.map_sub, ν.map_smul, ν.map_smul, ν.map_smul, ν.map_one, hbν]
  ring

/-- **The same at the step states**: `gK k (connObs k X) m` is the covariance of `θX` and `T_{2m e₀} X` in
the periodic state at `dyBeta k`. DERIVED: `0` the plane; `2` the two steps of one gap. -/
theorem gK_connObs_eq_stateCov (k : ℕ) (X : C(Cfg N, ℝ)) (m : ℕ) :
    gK k (connObs k X) m = FocusZoom.stateCov
      (GaugeWilson.periodicStateG (MassGap.SUN.SU N) (dyBeta (one_le_of_ne_zero (NeZero.ne N)) k))
      (LatticeReflection.ireflObs 0 0 X) (transObs ((2 * m) • eT) X) :=
  gP_conn _ X m

/-! ## 4. The composition -/

/-- **The window upper bound from one reflected read at the window scale.** Along a tower `βs`, if
eventually some half-space observable `X` has, for its centred reflected read `g = gP (βs k) (connP (βs k) X)`,
`g(0) > 0` and `g(0) e^{−2 m₁ U/2^k} ≤ g(m₁)` (`m₁ ≥ 1`), and the reflected covariance
`stateCov ν (θX) (T_{2m e₀} X)` is dominated by the tensor covariance at separations `z_m` of sup-norm `2m`,
then `WindowUpper N βs U`. The domination is a hypothesis (the mixed-to-diagonal part of link 1); the floor is
link 2. DERIVED: `2` the two steps of one gap and the window base; `1` the least gap index; `0` the contact
gap and the signs. -/
theorem windowUpper_of_reads [Fact (2 ≤ N)] {βs : ℕ → ℝ} {U : ℝ}
    (h : ∀ᶠ k in atTop, ∃ X : C(Cfg N, ℝ),
      X ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 ∧ ∃ m₁ : ℕ, 1 ≤ m₁ ∧
      0 < gP (βs k) (connP (βs k) X) 0 ∧
      gP (βs k) (connP (βs k) X) 0 * Real.exp (-(2 * m₁ * (U / 2 ^ k))) ≤ gP (βs k) (connP (βs k) X) m₁ ∧
      ∃ (x : ISite) (z : ℕ → ISite), (∀ m, snormG (z m) = 2 * m) ∧ ∀ m,
        |FocusZoom.stateCov (GaugeWilson.periodicStateG (MassGap.SUN.SU N) (βs k))
            (LatticeReflection.ireflObs 0 0 X) (transObs ((2 * m) • eT) X)| ≤
          |FocusZoom.stateCov (GaugeWilson.periodicStateG (MassGap.SUN.SU N) (βs k))
            (tensorEnergyG (MassGap.SUN.SU N) x) (tensorEnergyG (MassGap.SUN.SU N) (x + z m))|) :
    BandUpper.WindowUpper N βs U := by
  filter_upwards [h] with k ⟨X, hX, m₁, hm₁, hg0, hfl, x, z, hz, hdom⟩
  set g : ℕ → ℝ := gP (βs k) (connP (βs k) X) with hg
  have hm1r : (0 : ℝ) < m₁ := by exact_mod_cast hm₁
  have hg1 : 0 < g m₁ := lt_of_lt_of_le (mul_pos hg0 (Real.exp_pos _)) hfl
  have hlc : ∀ m, m₁ ≤ m → g m₁ ^ m ≤ g m ^ m₁ * g 0 ^ (m - m₁) := fun m hm =>
    periodic_far_ge (βs k) (connP_mem (βs k) hX) hm
  have hread : ∀ m, |g m| ≤ |FocusZoom.stateCov (GaugeWilson.periodicStateG (MassGap.SUN.SU N) (βs k))
      (tensorEnergyG (MassGap.SUN.SU N) x) (tensorEnergyG (MassGap.SUN.SU N) (x + z m))| := fun m => by
    rw [hg, gP_conn]
    exact hdom m
  have hM := BandUpper.measMassOfG_le_of_logConvex x hz hm₁ hg0 hg1 hlc hread
  rw [← mUG_SU]
  refine le_trans hM (ENNReal.ofReal_le_ofReal ?_)
  have hlog := Real.log_le_log (mul_pos hg0 (Real.exp_pos _)) hfl
  rw [Real.log_mul hg0.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  rw [div_le_iff₀ (by positivity), Real.log_div hg0.ne' hg1.ne']
  linarith

end MassGap.StepPeriodic

end

#print axioms MassGap.StepPeriodic.stateK_eq_periodicStateG
#print axioms MassGap.StepPeriodic.periodic_transObs
#print axioms MassGap.StepPeriodic.gK_eq_gP
#print axioms MassGap.StepPeriodic.bP_shift
#print axioms MassGap.StepPeriodic.reflShiftP
#print axioms MassGap.StepPeriodic.gapRead_eq_P
#print axioms MassGap.StepPeriodic.periodic_far_ge
#print axioms MassGap.StepPeriodic.connP_mem
#print axioms MassGap.StepPeriodic.gP_conn
#print axioms MassGap.StepPeriodic.gK_connObs_eq_stateCov
#print axioms MassGap.StepPeriodic.windowUpper_of_reads
