import Mathlib
import MassGap.ShortDistanceY
import MassGap.SimpleGroup

noncomputable section

/-!
# MassGap.NOneVacuity — at `N = 1` the connected functions vanish and Y and the three-point
condition fail

`SU(1)` has one element (`SimpleGroup.subsingleton_SU_one`), so the configuration space of `ℤ⁴` has
one point (`subsingleton_iconf_one`). On a one-point space every state is evaluation at the point
(`state_apply_of_subsingleton`), every centred observable is `0` (`cen_eq_zero_of_subsingleton`),
and every connected function and `ThreePointN.sepRatio` is `0`.

* `latticeTwoPoint_one`: `ShortDistanceY.latticeTwoPoint 1 hN β r = 0` at every `β`, `r`;
* `not_wilsonLatticeAF_one`: `¬ ShortDistanceY.WilsonLatticeAF 1 hN` — `FamilyAF` needs
  `|0 − C| ≤ ε` for some `C > 0` and every `ε > 0`;
* `sepRatio_tripleObs_one`, `cum3_tripleObs_one`: the three-point statistic and the connected
  three-point function of the block composites are `0`;
* `not_wilsonThreePointSeparation_one`: `¬ ThreePointN.WilsonThreePointSeparation 1 hN`.

So the hypotheses `WilsonLatticeAF` and `WilsonThreePointSeparation` of
`ShortDistanceY.wilson_yang_mills_separated` are false at `N = 1` and carry content only at
`2 ≤ N`.
-/

namespace MassGap.NOneVacuity

open MassGap Filter

section Subsingleton

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Subsingleton X]

/-- **On a one-point space a state is evaluation at the point.** `f = f x · 1`, and the state is
linear and normalised.

DERIVED: `1` is the unit observable. -/
theorem state_apply_of_subsingleton (ν : MassGap.DLRLimit.State X) (f : C(X, ℝ)) (x : X) :
    ν f = f x := by
  have hf : f = (f x) • (1 : C(X, ℝ)) := by
    ext y
    rw [Subsingleton.elim y x]
    simp
  calc ν f = ν ((f x) • (1 : C(X, ℝ))) := by rw [← hf]
    _ = f x := by rw [ν.map_smul, ν.map_one, mul_one]

#print axioms state_apply_of_subsingleton

/-- **On a one-point space every centred observable is `0`.**

DERIVED: `0` is the zero observable. -/
theorem cen_eq_zero_of_subsingleton (ν : MassGap.DLRLimit.State X) (f : C(X, ℝ)) :
    ThreePointN.cen ν f = 0 := by
  unfold ThreePointN.cen
  ext x
  have h := state_apply_of_subsingleton ν f x
  simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
    smul_eq_mul, mul_one, ContinuousMap.zero_apply]
  rw [h, sub_self]

#print axioms cen_eq_zero_of_subsingleton

/-- DERIVED: `0` is the value. -/
theorem cov2_eq_zero_of_subsingleton (ν : MassGap.DLRLimit.State X) (A B : C(X, ℝ)) :
    ThreePointN.cov2 ν A B = 0 := by
  unfold ThreePointN.cov2
  rw [cen_eq_zero_of_subsingleton ν A, cen_eq_zero_of_subsingleton ν B, zero_mul, ν.map_zero]

#print axioms cov2_eq_zero_of_subsingleton

/-- DERIVED: `0` is the value. -/
theorem cum3_eq_zero_of_subsingleton (ν : MassGap.DLRLimit.State X) (A B C : C(X, ℝ)) :
    ThreePointN.cum3 ν A B C = 0 := by
  unfold ThreePointN.cum3
  rw [cen_eq_zero_of_subsingleton ν A, cen_eq_zero_of_subsingleton ν B,
    cen_eq_zero_of_subsingleton ν C]
  simp only [zero_mul, MassGap.DLRLimit.State.map_zero]

#print axioms cum3_eq_zero_of_subsingleton

/-- DERIVED: `0` is the value; `2` is `sepRatio`'s square. -/
theorem sepRatio_eq_zero_of_subsingleton (ν : MassGap.DLRLimit.State X) (A B C : C(X, ℝ)) :
    ThreePointN.sepRatio ν A B C = 0 := by
  unfold ThreePointN.sepRatio
  rw [cum3_eq_zero_of_subsingleton ν A B C, zero_pow two_ne_zero, zero_div]

#print axioms sepRatio_eq_zero_of_subsingleton

end Subsingleton

/-- **The configuration space of `SU(1)` on `ℤ⁴` has one point.**

DERIVED: `1` is the rank; `4` is the spacetime dimension, through `GibbsSpec.IConf`. -/
theorem subsingleton_iconf_one : Subsingleton (MassGap.GibbsSpec.IConf (MassGap.SUN.SU 1)) :=
  ⟨fun U V => funext fun l =>
    @Subsingleton.elim _ MassGap.SimpleGroup.subsingleton_SU_one (U l) (V l)⟩

#print axioms subsingleton_iconf_one

/-- **At `N = 1` the lattice two-point function is `0`** at every coupling and separation.

DERIVED: `1` is the rank; `0` is the value. -/
theorem latticeTwoPoint_one (hN : (1 : ℕ) ≠ 0) (β r : ℝ) :
    ShortDistanceY.latticeTwoPoint 1 hN β r = 0 := by
  haveI := subsingleton_iconf_one
  unfold ShortDistanceY.latticeTwoPoint
  rw [cov2_eq_zero_of_subsingleton (MassGap.PeriodicState.periodicState hN β), zero_div]

#print axioms latticeTwoPoint_one

/-- **Requirement Y fails on the Wilson family at `N = 1`.** `FamilyAF` of the zero family asks for
`C > 0` with `|0 − C| ≤ ε` at some coupling for every `ε > 0`; `ε = C/2` refutes it.

DERIVED: `1` is the rank; `2` in `C/2` and `δ/2` halves a positive number; `8` and the square are
`FamilyAF`'s; `0` is the value of the family. -/
theorem not_wilsonLatticeAF_one (hN : (1 : ℕ) ≠ 0) : ¬ ShortDistanceY.WilsonLatticeAF 1 hN := by
  intro h
  unfold ShortDistanceY.WilsonLatticeAF ShortDistanceY.FamilyAF at h
  obtain ⟨C, hC, hunif⟩ := h
  obtain ⟨δ, hδ, hr⟩ := hunif (C / 2) (half_pos hC)
  obtain ⟨β, hβ⟩ := (hr (δ / 2) (half_pos hδ) (half_lt_self hδ)).exists
  rw [latticeTwoPoint_one, mul_zero, zero_mul, zero_sub, abs_neg, abs_of_pos hC] at hβ
  linarith

#print axioms not_wilsonLatticeAF_one

/-- **At `N = 1` the three-point statistic of the block composites is `0`.**

DERIVED: `1` is the rank; `0`, `1`, `2` index the three blocks; `0` is the value. -/
theorem sepRatio_tripleObs_one (hN : (1 : ℕ) ≠ 0) (ℓ D β : ℝ) :
    ThreePointN.sepRatio (MassGap.PeriodicState.periodicState hN β)
      (ThreePointN.tripleObs 1 ℓ D β 0) (ThreePointN.tripleObs 1 ℓ D β 1)
      (ThreePointN.tripleObs 1 ℓ D β 2) = 0 := by
  haveI := subsingleton_iconf_one
  exact sepRatio_eq_zero_of_subsingleton _ _ _ _

#print axioms sepRatio_tripleObs_one

/-- **At `N = 1` the connected three-point function of the block composites is `0`.**

DERIVED: `1` is the rank; `0`, `1`, `2` index the three blocks; `0` is the value. -/
theorem cum3_tripleObs_one (hN : (1 : ℕ) ≠ 0) (ℓ D β : ℝ) :
    ThreePointN.cum3 (MassGap.PeriodicState.periodicState hN β)
      (ThreePointN.tripleObs 1 ℓ D β 0) (ThreePointN.tripleObs 1 ℓ D β 1)
      (ThreePointN.tripleObs 1 ℓ D β 2) = 0 := by
  haveI := subsingleton_iconf_one
  exact cum3_eq_zero_of_subsingleton _ _ _ _

#print axioms cum3_tripleObs_one

/-- **The three-point condition fails at `N = 1`**: it asks for `c > 0` below `sepRatio`, which is
`0` at every coupling.

DERIVED: `1` is the rank; `0` is the strict lower bound on `c`. -/
theorem not_wilsonThreePointSeparation_one (hN : (1 : ℕ) ≠ 0) :
    ¬ ThreePointN.WilsonThreePointSeparation 1 hN := by
  intro h
  unfold ThreePointN.WilsonThreePointSeparation at h
  obtain ⟨ℓ, D, c, _, _, hc, hev⟩ := h
  obtain ⟨β, hβ⟩ := hev.exists
  rw [sepRatio_tripleObs_one hN ℓ D β] at hβ
  linarith

#print axioms not_wilsonThreePointSeparation_one

end MassGap.NOneVacuity
