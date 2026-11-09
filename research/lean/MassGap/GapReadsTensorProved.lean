import Mathlib
import MassGap.WeakEndProved
import MassGap.ObsLead
import MassGap.ObserverFlowSeed

/-!
# MassGap.GapReadsTensorProved — a periodic Clay gap makes the tensor reading decay at its rate

`CouplingTower.GapReadsTensor N` asks: at every `β ≥ 0`, a periodic Clay gap at rate `r`
(`PeriodicContent.PeriodicClayGapAt 0 0`, the gauge-invariant transfer along the time axis with the
mirror plane at `0`) gives `ofReal (−log r) ≤ mU β`, the measured mass of the tensor reading
`tensorEnergy x = P₀₁(x) − P₂₃(x)` of the same periodic state. This module proves it, with standard
axioms only.

## What is proved

* **`gapReadsTensor`**: `CouplingTower.GapReadsTensor N` for every `N ≠ 0`.
* `decaysAt_tensor`: `GapAt` at the periodic time-axis data at rate `0 < r ≤ 1` gives
  `SubstrateDecode.DecaysAt (periodicState hN β) tensorEnergy (−log r)`, prefactor `32 / r`.
* `confinedAt`, `measuredTower_of_ends`, `measuredTower_of_strongEnd`: the consumers
  `CouplingTower.confinedAt_of_gapReadsTensor`, `CouplingTower.measuredTower_of_ends` and
  `WeakEndProved.measuredTower_of_strongEnd` with the link `hG` discharged.

## The route

1. Time axis (`cov_time`). `TransferGap.clustering_sq` at the data `D = periodicGaugeInvData 0 0 hN β`,
   with `y` the plaquette density at `q` and `x` the one at `b` (both based at time `≥ 0`, so in the
   gauge-invariant half-space algebra). The form is `D.form a c = ν(θa · c)`, `θ = ireflObs 0 0`, and
   `T` is the unit time shift (`restrictT` of `ishiftObsL 0`), so the clustered quantity is the
   covariance of the density at the reflected plaquette `ireflPlaq 0 0 q`
   (`GaugeInvariantAlgebra.ireflObs_iplaqObs`) and the density at `b` moved `n` steps
   (`GaugeInvariantAlgebra.ishiftObsL_iterate_iplaqObs`). The two form values on the right are at most
   `4` and `16` (sup norms: a density lies in `[0, 2]`, and `vacProj x = x − ν(θx)·1`), so
   `|Cov| ≤ 8 rⁿ`.
2. Translation (`cov_trans`): `ContinuumField.state_transObs` with `PeriodicState.periodicState_shift`
   and `ObserverFlowSeed.transObs_plaqField`; a covariance of two densities depends only on their
   offset.
3. Axis permutation (`cov_axis`, `iaxisObs_plaqField`): `ContinuumHypercubic.periodicState_axis` and
   `ObsLead.plaqG_iaxis`. The swap of `0` and `μ` carries the density of plane `(ρ, σ)` at `y` to the
   density of plane `(e ρ, e σ)` at `iaxisSite e y`, whose time coordinate is `y μ`.
4. Every separation (`cov_plaq`): for `z` pick `μ` with `|z μ| = ‖z‖∞`; for `z μ < 0` swap the two
   arguments of the covariance and translate. Moving the first density to time `−1` puts it at a
   reflected plaquette based at time `≥ 0` (`LatticeReflection.ireflPlaq_involutive`), and the second at
   time `‖z‖∞ − 1`, so `|Cov| ≤ 8 r^{‖z‖∞ − 1} = (8/r) r^{‖z‖∞}`; at `z μ = 0` the covariance is at most
   `8` outright. The four plane pairs of `tensorEnergy` give the prefactor `4 · 8/r`, and
   `e^{−(−log r)‖z‖∞} = r^{‖z‖∞}`.

Every plane pair is covered, so the bound reads the density correlations of all six planes, not only
`(0, 1)` and `(2, 3)`. Neither `0 ≤ β` nor `2 ≤ N` is used: the transfer data and both symmetries of
the periodic state hold at every coupling and every `N ≠ 0`.

DERIVED (module-wide): `0` the time axis, the mirror plane and the origin; `2 * 0` the reflection
constant of the mirror plane at `0`; `1` the unit step and the offset of the first density below the
plane; `2` the bound of a plaquette density; `4 = 2 · 2` and `16 = 4 · 4` the form bounds; `8 = 2 · 4`
the covariance bound and `64 = 4 · 16`; `32 = 4 · 8` the four plane pairs of the tensor reading;
`1/1000` the seed of the consumers.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.GapReadsTensorProved

open Filter
open scoped ENNReal NNReal
open MassGap MassGap.ZoomSelfScale MassGap.MeasuredTower MassGap.MeasuredSpacing MassGap.ClayTreeG
  MassGap.FlowG MassGap.TimeGroupG MassGap.PeriodicReduceG MassGap.FlowClusterG
open MassGap.FocusZoom (stateCov)
open MassGap.PeriodicState (periodicState periodicGaugeInvData periodicState_shift)
open MassGap.GaugeInvariantAlgebra (iplaqObs gaugeInvHalfSpaceAlg)
open MassGap.ObserverEnergyMoments (plaqField)
open MassGap.StrongFiniteSize (snorm)
open MassGap.SubstrateDecode (DecaysAt tensorEnergy le_measMassOf)
open MassGap.CouplingTower (StrongEnd WeakEnd CouplingTower GapReadsTensor UVConverges ConfinedAt)

variable {N : ℕ}

/-! ## 1. Covariance algebra and the sup-norm bound -/

section Algebra

/-- The covariance is symmetric. DERIVED: no numeral. -/
theorem stateCov_comm (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (f g : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    stateCov ν f g = stateCov ν g f := by
  unfold stateCov
  rw [mul_comm f g, mul_comm (ν f)]

/-- The covariance of two differences. DERIVED: no numeral. -/
theorem stateCov_sub_sub (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (f g h k : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    stateCov ν (f - g) (h - k)
      = stateCov ν f h - stateCov ν f k - stateCov ν g h + stateCov ν g k := by
  unfold stateCov
  rw [sub_mul, mul_sub, mul_sub]
  simp only [MassGap.DLRLimit.State.map_sub]
  ring

/-- A covariance is at most twice the product of the sup norms. DERIVED: `2` the two terms of the
covariance. -/
theorem abs_stateCov_le (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (f g : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    |stateCov ν f g| ≤ 2 * (‖f‖ * ‖g‖) := by
  unfold stateCov
  have h1 : |ν (f * g)| ≤ ‖f‖ * ‖g‖ := (ν.abs_le_norm (f * g)).trans (norm_mul_le f g)
  have h2 : |ν f * ν g| ≤ ‖f‖ * ‖g‖ := by
    rw [abs_mul]
    exact mul_le_mul (ν.abs_le_norm f) (ν.abs_le_norm g) (abs_nonneg _) (norm_nonneg _)
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- A plaquette density is at most `2` in sup norm. DERIVED: `2` the range of the Wilson density;
`0` the excluded rank. -/
theorem norm_iplaqObs_le (hN : N ≠ 0) (q : MassGap.GibbsSpec.IPlaq) :
    ‖iplaqObs (N := N) q‖ ≤ 2 :=
  (ContinuousMap.norm_le _ (by norm_num)).mpr fun U => by
    have h0 := MassGap.WilsonAction.wilsonDensity_nonneg hN
      (MassGap.GibbsSpec.ihol (G := MassGap.SUN.SU N) q U)
    have h2 := MassGap.WilsonAction.wilsonDensity_le_two hN
      (MassGap.GibbsSpec.ihol (G := MassGap.SUN.SU N) q U)
    show ‖MassGap.WilsonAction.wilsonDensity (MassGap.GibbsSpec.ihol (G := MassGap.SUN.SU N) q U)‖ ≤ 2
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h2

#print axioms norm_iplaqObs_le

/-- The covariance of two plaquette densities is at most `8`. DERIVED: `8 = 2 · 2 · 2`. -/
theorem abs_stateCov_plaq_le (hN : N ≠ 0)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (a b : MassGap.GibbsSpec.IPlaq) :
    |stateCov ν (plaqField (N := N) a).1 (plaqField (N := N) b).1| ≤ 8 := by
  have ha := norm_iplaqObs_le hN a
  have hb := norm_iplaqObs_le hN b
  have h := abs_stateCov_le ν (iplaqObs (N := N) a) (iplaqObs (N := N) b)
  have hab : ‖iplaqObs (N := N) a‖ * ‖iplaqObs (N := N) b‖ ≤ 2 * 2 :=
    mul_le_mul ha hb (norm_nonneg _) (by norm_num)
  exact h.trans (by linarith)

end Algebra

/-! ## 2. The time axis: the clustering bound as a covariance of plaquette densities -/

section Time

/-- The iterated plaquette translation moves the base site by the iterated site translation.
DERIVED: `1` the projection onto the plane. -/
theorem ishiftPlaq_iterate (μ : Fin 4) (k : ℕ) (q : MassGap.GibbsSpec.IPlaq) :
    (MassGap.InfiniteShift.ishiftPlaq μ)^[k] q
      = (q.1, (MassGap.InfiniteLattice.ishift μ)^[k] q.2) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    rfl

/-- `k` unit steps along `μ` add `k` to the `μ` coordinate. DERIVED: `1` the unit step. -/
theorem ishift_iterate_eq (μ : Fin 4) (k : ℕ) (x : MassGap.GibbsSpec.ISite) :
    (MassGap.InfiniteLattice.ishift μ)^[k] x = Function.update x μ (x μ + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold MassGap.InfiniteLattice.ishift
    rw [Function.update_self, Function.update_idem]
    congr 1
    push_cast
    ring

/-- **The clustering bound at the plaquette densities.** At rate `0 ≤ r` with `GapAt` at the periodic
time-axis data, for plaquettes `q`, `b` based at time `≥ 0` and every lag `n`: the covariance of the
density at the reflected plaquette `ireflPlaq 0 0 q` and the density at `b` moved `n` steps along the
time axis is at most `8 rⁿ`.

`TransferGap.clustering_sq` at `x = P_b`, `y = P_q`: the form is `ν(θa · c)` and `T` the unit shift, so
its left side is the squared covariance; `D.form y y ≤ 4` and `D.form (vacProj x) (vacProj x) ≤ 16`.

DERIVED: `0` the time axis, the mirror plane and the lower end of `r`; `2 * 0` the reflection constant;
`8 = √64`, `64 = 4 · 16`; `4 = 2 · 2`, `16 = 4 · 4` the form bounds from `‖P‖ ≤ 2`. -/
theorem cov_time (hN : N ≠ 0) (β : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hg : MassGap.TransferGap.GapAt (periodicGaugeInvData 0 0 hN β) r)
    (q b : MassGap.GibbsSpec.IPlaq) (hq : 0 ≤ q.2 0) (hb : 0 ≤ b.2 0) (n : ℕ) :
    |stateCov (periodicState hN β)
        (iplaqObs (N := N) (MassGap.LatticeReflection.ireflPlaq 0 (2 * 0) q))
        (iplaqObs (N := N) ((MassGap.InfiniteShift.ishiftPlaq 0)^[n] b))| ≤ 8 * r ^ n := by
  let y : ↥(gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) 0 0) :=
    ⟨iplaqObs q, MassGap.GaugeInvariantAlgebra.iplaqObs_mem_gaugeInvHalfSpaceAlg_of_le q 0 0 hq⟩
  let x : ↥(gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) 0 0) :=
    ⟨iplaqObs b, MassGap.GaugeInvariantAlgebra.iplaqObs_mem_gaugeInvHalfSpaceAlg_of_le b 0 0 hb⟩
  have hform : ∀ a c : ↥(gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) 0 0),
      (periodicGaugeInvData 0 0 hN β).form a c
        = periodicState hN β (MassGap.LatticeReflection.ireflObs 0 (2 * 0)
            (a : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
            * (c : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))) := fun _ _ => rfl
  have hθ1 : MassGap.LatticeReflection.ireflObs 0 (2 * 0)
      (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) = 1 := by
    ext U; rfl
  have hTn : ∀ k : ℕ,
      ((((periodicGaugeInvData 0 0 hN β).T ^ k) x :
          ↥(gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) 0 0)) :
          C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
        = (⇑(MassGap.ReflectionShift.ishiftObsL 0))^[k] (iplaqObs (N := N) b) := by
    intro k
    rw [Module.End.pow_apply]
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  have h1 : (periodicGaugeInvData 0 0 hN β).form y (((periodicGaugeInvData 0 0 hN β).T ^ n) x)
      = periodicState hN β (iplaqObs (N := N) (MassGap.LatticeReflection.ireflPlaq 0 (2 * 0) q)
          * iplaqObs (N := N) ((MassGap.InfiniteShift.ishiftPlaq 0)^[n] b)) := by
    rw [hform, hTn]
    show periodicState hN β (MassGap.LatticeReflection.ireflObs 0 (2 * 0) (iplaqObs (N := N) q)
        * (⇑(MassGap.ReflectionShift.ishiftObsL 0))^[n] (iplaqObs (N := N) b)) = _
    rw [MassGap.GaugeInvariantAlgebra.ireflObs_iplaqObs,
      MassGap.GaugeInvariantAlgebra.ishiftObsL_iterate_iplaqObs]
  have h2 : (periodicGaugeInvData 0 0 hN β).form y (periodicGaugeInvData 0 0 hN β).vac
      = periodicState hN β (iplaqObs (N := N) (MassGap.LatticeReflection.ireflPlaq 0 (2 * 0) q)) := by
    show periodicState hN β (MassGap.LatticeReflection.ireflObs 0 (2 * 0) (iplaqObs (N := N) q)
        * 1) = _
    rw [mul_one, MassGap.GaugeInvariantAlgebra.ireflObs_iplaqObs]
  have h3 : (periodicGaugeInvData 0 0 hN β).form (periodicGaugeInvData 0 0 hN β).vac x
      = periodicState hN β (iplaqObs (N := N) ((MassGap.InfiniteShift.ishiftPlaq 0)^[n] b)) := by
    show periodicState hN β (MassGap.LatticeReflection.ireflObs 0 (2 * 0)
        (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) * iplaqObs (N := N) b) = _
    rw [hθ1, one_mul, ← MassGap.GaugeInvariantAlgebra.ishiftObsL_iterate_iplaqObs,
      MassGap.GaugeInvariantAlgebra.state_iterate_shift_eq _ 0 (periodicState_shift hN β 0)]
  have hbd : ∀ a c : ↥(gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) 0 0),
      |(periodicGaugeInvData 0 0 hN β).form a c|
        ≤ ‖(a : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))‖
          * ‖(c : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))‖ := by
    intro a c
    rw [hform]
    exact ((periodicState hN β).abs_le_norm _).trans ((norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (MassGap.WilsonTransferReduction.norm_ireflObs_le 0 (2 * 0) _)
        (norm_nonneg _)))
  have hone : ‖(1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))‖ ≤ 1 :=
    (ContinuousMap.norm_le _ zero_le_one).mpr fun _ => by simp
  have hy : ‖(y : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))‖ ≤ 2 := norm_iplaqObs_le hN q
  have hx : ‖(x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))‖ ≤ 2 := norm_iplaqObs_le hN b
  have hyy : (periodicGaugeInvData 0 0 hN β).form y y ≤ 4 :=
    (le_abs_self _).trans ((hbd y y).trans
      (by nlinarith [norm_nonneg (y : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))]))
  have hc : |(periodicGaugeInvData 0 0 hN β).form x (periodicGaugeInvData 0 0 hN β).vac| ≤ 2 := by
    refine (hbd x _).trans ?_
    show ‖(x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))‖
        * ‖(1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))‖ ≤ 2
    nlinarith [norm_nonneg (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)),
      norm_nonneg (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))]
  have hvp : ‖((MassGap.TransferGap.vacProj (periodicGaugeInvData 0 0 hN β) x :
      ↥(gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) 0 0)) :
      C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))‖ ≤ 4 := by
    show ‖(x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
        - (periodicGaugeInvData 0 0 hN β).form x (periodicGaugeInvData 0 0 hN β).vac
          • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))‖ ≤ 4
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    nlinarith [abs_nonneg ((periodicGaugeInvData 0 0 hN β).form x (periodicGaugeInvData 0 0 hN β).vac),
      norm_nonneg (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))]
  have hvv : (periodicGaugeInvData 0 0 hN β).form
      (MassGap.TransferGap.vacProj (periodicGaugeInvData 0 0 hN β) x)
      (MassGap.TransferGap.vacProj (periodicGaugeInvData 0 0 hN β) x) ≤ 16 :=
    (le_abs_self _).trans ((hbd _ _).trans (by nlinarith [norm_nonneg ((MassGap.TransferGap.vacProj
      (periodicGaugeInvData 0 0 hN β) x : ↥(gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) 0 0)) :
      C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))]))
  have hcl := MassGap.TransferGap.clustering_sq (periodicGaugeInvData 0 0 hN β) hr hg n x y
  rw [h1, h2, h3] at hcl
  have hsq : (stateCov (periodicState hN β)
        (iplaqObs (N := N) (MassGap.LatticeReflection.ireflPlaq 0 (2 * 0) q))
        (iplaqObs (N := N) ((MassGap.InfiniteShift.ishiftPlaq 0)^[n] b))) ^ 2 ≤ (8 * r ^ n) ^ 2 := by
    unfold stateCov
    calc _ ≤ _ := hcl
      _ ≤ r ^ (2 * n) * (4 * 16) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hyy hvv
            ((periodicGaugeInvData 0 0 hN β).form_nonneg _) (by norm_num)) (pow_nonneg hr _)
      _ = (8 * r ^ n) ^ 2 := by ring
  exact abs_le_of_sq_le_sq hsq (by positivity)

#print axioms cov_time

end Time

/-! ## 3. Translation and axis permutation -/

section Symmetry

/-- **A covariance of two densities depends only on their offset.** DERIVED: no numeral. -/
theorem cov_trans (hN : N ≠ 0) (β : ℝ) (pa pb : Fin 4 × Fin 4) (y y' v : MassGap.GibbsSpec.ISite) :
    stateCov (periodicState hN β) (plaqField (N := N) (pa, y)).1 (plaqField (N := N) (pb, y')).1
      = stateCov (periodicState hN β) (plaqField (N := N) (pa, y + v)).1
          (plaqField (N := N) (pb, y' + v)).1 := by
  rw [← MassGap.ObserverFlowSeed.transObs_plaqField, ← MassGap.ObserverFlowSeed.transObs_plaqField]
  have hsh : ∀ (τ : Fin 4) (F : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)),
      periodicState hN β (MassGap.ReflectionShift.ishiftObsL τ F) = periodicState hN β F :=
    fun τ F => periodicState_shift hN β τ F
  unfold stateCov
  rw [← MassGap.ContinuumField.transObs_mul, MassGap.ContinuumField.state_transObs hsh,
    MassGap.ContinuumField.state_transObs hsh, MassGap.ContinuumField.state_transObs hsh]

#print axioms cov_trans

/-- **The relabelling of axes carries a density to the density of the relabelled plaquette.**
DERIVED: no numeral. -/
theorem iaxisObs_plaqField (e : Equiv.Perm (Fin 4)) (ρ σ : Fin 4) (y : MassGap.GibbsSpec.ISite) :
    MassGap.ContinuumHypercubic.iaxisObs e (plaqField (N := N) ((ρ, σ), y)).1
      = (plaqField (N := N) ((e ρ, e σ), MassGap.ContinuumHypercubic.iaxisSite e y)).1 := by
  ext U
  show (plaqField (N := N) ((ρ, σ), y)).1 (MassGap.ContinuumHypercubic.iaxisConf e U)
    = (plaqField (N := N) ((e ρ, e σ), MassGap.ContinuumHypercubic.iaxisSite e y)).1 U
  rw [MassGap.ObsLead.plaqField_eq, MassGap.ObsLead.plaqField_eq, MassGap.ObsLead.plaqG_iaxis]

#print axioms iaxisObs_plaqField

/-- **A covariance is unchanged by a relabelling of axes.** DERIVED: no numeral. -/
theorem cov_axis (hN : N ≠ 0) (β : ℝ) (e : Equiv.Perm (Fin 4))
    (F H : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    stateCov (periodicState hN β) F H
      = stateCov (periodicState hN β) (MassGap.ContinuumHypercubic.iaxisObs e F)
          (MassGap.ContinuumHypercubic.iaxisObs e H) := by
  unfold stateCov
  rw [← MassGap.ContinuumHypercubic.iaxisObs_mul, MassGap.ContinuumHypercubic.periodicState_axis,
    MassGap.ContinuumHypercubic.periodicState_axis, MassGap.ContinuumHypercubic.periodicState_axis]

#print axioms cov_axis

/-- The sup norm is unchanged by negation. DERIVED: no numeral. -/
theorem snorm_neg (z : MassGap.GibbsSpec.ISite) : snorm (-z) = snorm z := by
  unfold snorm
  congr 1
  funext i
  rw [Pi.neg_apply, Int.natAbs_neg]

end Symmetry

/-! ## 4. Every separation -/

section Separation

/-- **Time separation `s`, any planes.** With `GapAt` at rate `0 < r ≤ 1`: the covariance of the
density of plane `pa` at the origin and the density of plane `pb` at a site of time coordinate `s` is at
most `(8/r) rˢ`.

At `s = 0` the bound `8` holds outright. At `s ≥ 1` translate by `−e₀`: the first density sits at time
`−1`, the reflection of a plaquette based at time `≥ 0`, and the second at time `s − 1`, the iterate
`s − 1` of a plaquette based at time `0`; `cov_time` gives `8 r^{s−1}`.

DERIVED: `0` the time axis and the origin; `−1` the offset below the mirror plane; `2 * 0` the
reflection constant; `8` the bound of `cov_time`; `1` the step absorbed into `8/r`. -/
theorem cov_sep_time (hN : N ≠ 0) (β : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hg : MassGap.TransferGap.GapAt (periodicGaugeInvData 0 0 hN β) r)
    (pa pb : Fin 4 × Fin 4) (w : MassGap.GibbsSpec.ISite) (s : ℕ) (hw : w 0 = s) :
    |stateCov (periodicState hN β) (plaqField (N := N) (pa, 0)).1 (plaqField (N := N) (pb, w)).1|
      ≤ 8 / r * r ^ s := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · refine (abs_stateCov_plaq_le hN _ _ _).trans ?_
    rw [pow_zero, mul_one, le_div_iff₀ hr0]
    linarith
  set t : MassGap.GibbsSpec.ISite := fun j => if j = 0 then (-1 : ℤ) else 0 with ht
  rw [cov_trans hN β pa pb 0 w t, zero_add]
  have hqA := MassGap.LatticeReflection.ireflPlaq_involutive 0 (2 * 0) (pa, t)
  have hq : 0 ≤ (MassGap.LatticeReflection.ireflPlaq 0 (2 * 0) (pa, t)).2 0 := by
    unfold MassGap.LatticeReflection.ireflPlaq
    split_ifs <;> simp [MassGap.LatticeReflection.ireflSite_axis, ht]
  have hb : 0 ≤ ((pb, Function.update (w + t) 0 0) : MassGap.GibbsSpec.IPlaq).2 0 := by simp
  have hbB : (MassGap.InfiniteShift.ishiftPlaq 0)^[s - 1] ((pb, Function.update (w + t) 0 0) :
      MassGap.GibbsSpec.IPlaq) = (pb, w + t) := by
    rw [ishiftPlaq_iterate, ishift_iterate_eq]
    congr 1
    funext j
    by_cases hj : j = 0
    · subst hj
      simp [Function.update_self, ht, hw]
      omega
    · simp [Function.update_of_ne hj]
  have hcore := cov_time hN β hr0.le hg _ _ hq hb (s - 1)
  rw [hqA, hbB] at hcore
  have hpow : r ^ s = r ^ (s - 1) * r := by rw [← pow_succ, Nat.sub_add_cancel hs]
  have heq : 8 / r * r ^ s = 8 * r ^ (s - 1) := by
    calc 8 / r * r ^ s = r ^ (s - 1) * (8 / r * r) := by rw [hpow]; ring
      _ = r ^ (s - 1) * 8 := by rw [div_mul_cancel₀ 8 hr0.ne']
      _ = 8 * r ^ (s - 1) := by ring
  rw [heq]
  exact hcore

#print axioms cov_sep_time

/-- **Direction `μ` carrying the sup norm, `z μ ≥ 0`.** Translate the first density to the origin and
relabel the axes by the swap of `0` and `μ`. DERIVED: `0` the time axis and the origin. -/
theorem cov_plaq_dir (hN : N ≠ 0) (β : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hg : MassGap.TransferGap.GapAt (periodicGaugeInvData 0 0 hN β) r)
    (pa pb : Fin 4 × Fin 4) (x z : MassGap.GibbsSpec.ISite) (μ : Fin 4) (hμ : z μ = snorm z) :
    |stateCov (periodicState hN β) (plaqField (N := N) (pa, x)).1 (plaqField (N := N) (pb, x + z)).1|
      ≤ 8 / r * r ^ snorm z := by
  have e1 : x + -x = 0 := add_neg_cancel x
  have e2 : x + z + -x = z := by abel
  rw [cov_trans hN β pa pb x (x + z) (-x), e1, e2]
  rw [cov_axis hN β (Equiv.swap 0 μ), iaxisObs_plaqField, iaxisObs_plaqField]
  have h0 : MassGap.ContinuumHypercubic.iaxisSite (Equiv.swap 0 μ) (0 : MassGap.GibbsSpec.ISite)
      = 0 := by
    funext j; rfl
  rw [h0]
  refine cov_sep_time hN β hr0 hr1 hg _ _ _ (snorm z) ?_
  show z ((Equiv.swap 0 μ).symm 0) = _
  rw [Equiv.symm_swap, Equiv.swap_apply_left]
  exact hμ

#print axioms cov_plaq_dir

/-- **Every separation, any planes.** With `GapAt` at rate `0 < r ≤ 1`, the covariance of two
plaquette densities at offset `z` is at most `(8/r) r^{‖z‖∞}`. Pick `μ` with `|z μ| = ‖z‖∞`; at
`z μ < 0` swap the arguments. DERIVED: `0` the sign of `z μ`; `8` as in `cov_sep_time`. -/
theorem cov_plaq (hN : N ≠ 0) (β : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hg : MassGap.TransferGap.GapAt (periodicGaugeInvData 0 0 hN β) r)
    (pa pb : Fin 4 × Fin 4) (x z : MassGap.GibbsSpec.ISite) :
    |stateCov (periodicState hN β) (plaqField (N := N) (pa, x)).1 (plaqField (N := N) (pb, x + z)).1|
      ≤ 8 / r * r ^ snorm z := by
  obtain ⟨μ, -, hμ⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun i : Fin 4 => (z i).natAbs)
  have hs : snorm z = (z μ).natAbs := hμ
  rcases le_or_gt 0 (z μ) with h | h
  · exact cov_plaq_dir hN β hr0 hr1 hg pa pb x z μ (by rw [hs, Int.natAbs_of_nonneg h])
  · rw [stateCov_comm]
    have hd := cov_plaq_dir hN β hr0 hr1 hg pb pa (x + z) (-z) μ (by
      rw [snorm_neg, hs, Pi.neg_apply, ← Int.natAbs_neg, Int.natAbs_of_nonneg (show (0 : ℤ) ≤ -z μ by omega)])
    rwa [add_neg_cancel_right, snorm_neg] at hd

#print axioms cov_plaq

/-- **The tensor reading decays at the gap rate.** With `GapAt` at the periodic time-axis data at rate
`0 < r ≤ 1`, `DecaysAt (periodicState hN β) tensorEnergy (−log r)` with prefactor `4 · 8/r`: the
covariance of two tensor readings is a signed sum of four density covariances (`stateCov_sub_sub`),
each at most `(8/r) r^{‖z‖∞}` (`cov_plaq`), and `e^{−(−log r)‖z‖∞} = r^{‖z‖∞}`.

DERIVED: `4` the plane pairs of two tensor readings; `8` as in `cov_plaq`; `0`, `1` the bounds of
`r`. -/
theorem decaysAt_tensor (hN : N ≠ 0) (β : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hg : MassGap.TransferGap.GapAt (periodicGaugeInvData 0 0 hN β) r) :
    DecaysAt (periodicState hN β) tensorEnergy (-Real.log r) := by
  refine ⟨4 * (8 / r), fun x z => ?_⟩
  have hexp : Real.exp (-(-Real.log r * (snorm z : ℝ))) = r ^ snorm z := by
    rw [neg_mul, neg_neg, ← Real.rpow_def_of_pos hr0, Real.rpow_natCast]
  rw [hexp]
  unfold tensorEnergy
  rw [stateCov_sub_sub]
  have h1 := cov_plaq hN β hr0 hr1 hg ((0 : Fin 4), (1 : Fin 4)) ((0 : Fin 4), (1 : Fin 4)) x z
  have h2 := cov_plaq hN β hr0 hr1 hg ((0 : Fin 4), (1 : Fin 4)) ((2 : Fin 4), (3 : Fin 4)) x z
  have h3 := cov_plaq hN β hr0 hr1 hg ((2 : Fin 4), (3 : Fin 4)) ((0 : Fin 4), (1 : Fin 4)) x z
  have h4 := cov_plaq hN β hr0 hr1 hg ((2 : Fin 4), (3 : Fin 4)) ((2 : Fin 4), (3 : Fin 4)) x z
  rw [abs_le] at h1 h2 h3 h4 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

#print axioms decaysAt_tensor

end Separation

/-! ## 5. The link, and its consumers -/

section Link

/-- **`GapReadsTensor N`, proved.** A periodic Clay gap at rate `r` is `GapAt` at the periodic
time-axis data (`WeakCouplingWindow.gapAt_of_periodicClayGapAt`), with `0 < r < 1`; `decaysAt_tensor`
and `SubstrateDecode.le_measMassOf` give `ofReal (−log r) ≤ mU β`. DERIVED: `0` the time axis, the
mirror plane and the sign of `−log r`; `1` the upper end of `r`. -/
theorem gapReadsTensor [NeZero N] : GapReadsTensor N := by
  intro β _ r hcl
  have hg := MassGap.WeakCouplingWindow.gapAt_of_periodicClayGapAt 0 0 (NeZero.ne N) hcl
  obtain ⟨hr0, hr1, -⟩ := hcl
  exact le_measMassOf (neg_nonneg.mpr (Real.log_nonpos hr0.le hr1.le))
    (decaysAt_tensor (NeZero.ne N) β hr0 hr1.le hg)

#print axioms gapReadsTensor

/-- **(IR) in the basin**: `ConfinedAt N u₀ (log 2)` at every `u₀ ≤ 1/1000`,
`CouplingTower.confinedAt_of_gapReadsTensor` with the link proved. DERIVED: `2` the least rank and
`log 2` the rate; `1/1000` the seed. -/
theorem confinedAt [NeZero N] (hN2 : 2 ≤ N) {u₀ : ℝ} (hu : u₀ ≤ 1 / 1000) :
    ConfinedAt N u₀ (Real.log 2) :=
  MassGap.CouplingTower.confinedAt_of_gapReadsTensor hN2 gapReadsTensor hu

#print axioms confinedAt

/-- **The ends and (UV) give a coupling tower that is a measured tower, with the per-step gap**:
`CouplingTower.measuredTower_of_ends` with the link proved. DERIVED: `1/1000` the seed; `log 2` the
window rate; `0` the signs; `2` the least rank. -/
theorem measuredTower_of_ends [NeZero N] [Fact (2 ≤ N)] {u₀ : ℝ} (hu0 : 0 < u₀)
    (hu : u₀ ≤ 1 / 1000) (hS : StrongEnd N) (hW : WeakEnd N u₀)
    (hUV : ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ∃ μ : ℝ, UVConverges N βs id μ) :
    ∃ βs : ℕ → ℝ, CouplingTower N u₀ βs id ∧ MeasTowerG (MassGap.SUN.SU N) βs ∧
      ∀ᶠ k in atTop, ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        TransferGap.GapAt (periodicGaugeInvDataG (MassGap.SUN.SU N) 0 0 (βs k)) r ∧
        2 * Real.log 2 / GaugeRunning.aRunG (MassGap.SUN.SU N) 1
          ≤ -Real.log r / dySpacingG (MassGap.SUN.SU N) k :=
  MassGap.CouplingTower.measuredTower_of_ends hu0 hu hS hW gapReadsTensor hUV

#print axioms measuredTower_of_ends

/-- **(S) and (UV) give a measured coupling tower with the per-step gap**:
`WeakEndProved.measuredTower_of_strongEnd` with the link proved; (W) is discharged there. DERIVED:
`1/1000` the seed; `log 2` the window rate; `0` the signs; `2` the least rank. -/
theorem measuredTower_of_strongEnd [NeZero N] [Fact (2 ≤ N)] {u₀ : ℝ} (hu0 : 0 < u₀)
    (hu : u₀ ≤ 1 / 1000) (hS : StrongEnd N)
    (hUV : ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ∃ μ : ℝ, UVConverges N βs id μ) :
    ∃ βs : ℕ → ℝ, CouplingTower N u₀ βs id ∧ MeasTowerG (MassGap.SUN.SU N) βs ∧
      ∀ᶠ k in atTop, ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        TransferGap.GapAt (periodicGaugeInvDataG (MassGap.SUN.SU N) 0 0 (βs k)) r ∧
        2 * Real.log 2 / GaugeRunning.aRunG (MassGap.SUN.SU N) 1
          ≤ -Real.log r / dySpacingG (MassGap.SUN.SU N) k :=
  MassGap.WeakEndProved.measuredTower_of_strongEnd hu0 hu hS gapReadsTensor hUV

#print axioms measuredTower_of_strongEnd

end Link

end MassGap.GapReadsTensorProved
