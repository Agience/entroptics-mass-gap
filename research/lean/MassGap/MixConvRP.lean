import Mathlib
import MassGap.ReflAvg

/-!
# MassGap.MixConvRP — the convergence of the mixed readings from reflection positivity

`ReflAvg.clayStatementAt_SU_reflAvg` takes `hMC : MixConvF hN2 W (fR N) (bR N) z r`: along `ultra`,
the mixed reading `mixLatC` of every composite monomial `P` of the averaged composites `CbR N z`
against every margin monomial `Q` of the observer converges. This module proves `hMC` from `CompOS`,
the observer's moment bound `hU` and `hphys`, and gives the capstone without it.

## 1. The lattice Cauchy–Schwarz bound

`mixLatC_sq_le`: for composites that are reflection covariant on the lattice at the plane `τ`
(`JointRP.ReflCovLat C τ`), at every step `k` at which the smeared composite monomial `P` and the
flowed monomial `Q` lie in the half-space algebra of `x_τ = 0`,
`mixLatC(P, Q)² ≤ |latC(ΘP ∪ P)| · |latSF(ΘQ ∪ Q)|`. Proof: `JointRP.latJointC` at `P' = P`, `t = 0`,
`c = s·e_Q` is `0 ≤ rReadC(P,P) − 2s·rMixC(P,Q) + s²·latSF(ΘQ ∪ Q)` for every `s`, so
`rMixC² ≤ rReadC(P,P) · latSF(ΘQ ∪ Q)` (`CompositeLink.sq_le_of_quad`); under covariance
`rMixC = sgnC · mixLatC` and `rReadC = sgnC · latC(pairC P P)` (`rMixC_of_cov`, `rReadC_of_cov`),
with `sgnC² = 1`.

## 2. Bounded along `ultra`, hence convergent

* `exists_tendsto_ultra_of_ultra`: a real sequence bounded on a set of `ultra` converges along `ultra`.
* `mixConvF_of_cov`: at any tensor and bare fields with `ReflCovLat (CbF f bareO z) 0`, `CompOS` and
  `hU`, `hphys` give `MixConvF`. Both factors of the bound are bounded along `ultra`:
  `latC(ΘP ∪ P)` converges along `ultra` (`CompOS.1`, `adm_pairC`), and `latSF(ΘQ ∪ Q)` is
  eventually bounded (`ClaySUGap.uB`); the half-space memberships hold eventually
  (`eventually_cMono_mem` with `build_unifLocal`, `eventually_flow_mem` with
  `Flow.posPreserving_of_physRange`).
* `mixConvF_R`: `MixConvF hN2 W (fR N) (bR N) z r` from `CompOS (CbR N z)`, `hU`, `hphys`
  (`reflCovLat_CbR`).

## 3. The capstone

`clayStatementAt_SU_reflAvg'`: `ReflAvg.clayStatementAt_SU_reflAvg` with `hMC` discharged by
`mixConvF_R`. Its inputs: `hU`, `hphys` at one `r`, `hfar`, `z` with `hz`, `hzS`, `hzP`, `G`, `hK`,
`hAF`, `hObs`, `hWard`, `hCO`, `hA`; `hK`, `hWard` read `rhoD (fR N) z`, and `hCO`, `hA` the averaged
composites `CbR N z`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the plane, the empty time and the sign; `1` the unit sign and the unit
bound margin; `2` the cross-term factor and the square.
-/

noncomputable section

namespace MassGap.MixConvRP

open Filter
open scoped Topology

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP

variable {N : ℕ}

/-! ## 1. The lattice Cauchy–Schwarz bound -/

section Bound

/-- `sgnC² = 1`. DERIVED: `1` the unit; `2` the square. -/
theorem sgnC_sq (C : Composites N) (τ : Fin 4) (P : TMonoG C.Ix) : sgnC C τ P ^ 2 = 1 := by
  unfold sgnC
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← pow_mul, mul_comm, pow_mul]
  simp

/-- `|sgnC| = 1`. DERIVED: `1` the unit. -/
theorem abs_sgnC (C : Composites N) (τ : Fin 4) (P : TMonoG C.Ix) : |sgnC C τ P| = 1 := by
  have h := sgnC_sq C τ P
  have h2 : |sgnC C τ P| ^ 2 = 1 := by rw [sq_abs, h]
  have h0 := abs_nonneg (sgnC C τ P)
  exact le_antisymm (by nlinarith) (by nlinarith)

/-- **The reflected Cauchy–Schwarz bound at one step**: under half-space membership of `P` and `Q`,
`rMixC(P,Q)² ≤ latSF(ΘQ ∪ Q) · rReadC(P,P)` (`latJointC` at `P' = P`, `t = 0`, `c = s·e_Q`).

DERIVED: `0` the empty time; `2` the cross-term factor and the square. -/
theorem rMixC_sq_le (hN : N ≠ 0) (C : Composites N) (Φ : Flow N) (τ : Fin 4) (k : ℕ)
    (P : TMonoG C.Ix) (Q : Mono N)
    (hP : prodSmear (dySpacing N k) (cMono hN C k P)
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0)
    (hQ : prodSmear (dySpacing N k) (Φ.mono k Q)
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0) :
    rMixC hN C Φ τ k P Q ^ 2 ≤ latSF hN Φ k (pairFam τ Q Q) * rReadC hN C τ k P P := by
  have h : ∀ s : ℝ, 0 ≤ rReadC hN C τ k P P + 2 * s * (-rMixC hN C Φ τ k P Q)
      + s ^ 2 * latSF hN Φ k (pairFam τ Q Q) := fun s => by
    have hJ := latJointC hN C Φ τ k (fun _ : Unit => Q) P P 0 (Finsupp.single () s) hP hP
      (fun _ _ => hQ)
    simp only [xL_single, gForm_single] at hJ
    linarith
  have := sq_le_of_quad h
  rwa [neg_sq] at this

/-- **The lattice Cauchy–Schwarz bound of the mixed reading**: for reflection-covariant composites,
under half-space membership of `P` and `Q` at step `k`,
`mixLatC(P,Q)² ≤ |latC(ΘP ∪ P)| · |latSF(ΘQ ∪ Q)|`.

DERIVED: `2` the square. -/
theorem mixLatC_sq_le (hN : N ≠ 0) (C : Composites N) (Φ : Flow N) (τ : Fin 4)
    (hcov : ReflCovLat C τ) (k : ℕ) (P : TMonoG C.Ix) (Q : Mono N)
    (hP : prodSmear (dySpacing N k) (cMono hN C k P)
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0)
    (hQ : prodSmear (dySpacing N k) (Φ.mono k Q)
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0) :
    mixLatC hN C Φ τ k P Q ^ 2
      ≤ |latC hN C k (pairC C τ P P)| * |latSF hN Φ k (pairFam τ Q Q)| := by
  have h := rMixC_sq_le hN C Φ τ k P Q hP hQ
  rw [rMixC_of_cov hN C Φ τ hcov k P Q, rReadC_of_cov hN C τ hcov k P P, mul_pow,
    sgnC_sq, one_mul] at h
  calc mixLatC hN C Φ τ k P Q ^ 2
      ≤ latSF hN Φ k (pairFam τ Q Q) * (sgnC C τ P * latC hN C k (pairC C τ P P)) := h
    _ ≤ |latSF hN Φ k (pairFam τ Q Q) * (sgnC C τ P * latC hN C k (pairC C τ P P))| :=
        le_abs_self _
    _ = |latC hN C k (pairC C τ P P)| * |latSF hN Φ k (pairFam τ Q Q)| := by
        rw [abs_mul, abs_mul, abs_sgnC, one_mul, mul_comm]

end Bound

/-! ## 2. Bounded along `ultra`, hence convergent -/

section Conv

/-- **A real sequence bounded on a set of `ultra` converges along `ultra`.** DERIVED: no numeral. -/
theorem exists_tendsto_ultra_of_ultra (s : ℕ → ℝ) (B : ℝ)
    (h : ∀ᶠ k in (ultra : Filter ℕ), |s k| ≤ B) :
    ∃ x, Tendsto s (ultra : Filter ℕ) (𝓝 x) := by
  have hmem : Set.Icc (-B) B ∈ (Ultrafilter.map s ultra : Filter ℝ) := by
    rw [Ultrafilter.coe_map]
    exact Filter.mem_map.mpr (h.mono fun k hk => abs_le.mp hk)
  obtain ⟨x, _hx, hlim⟩ := isCompact_Icc.ultrafilter_le_nhds (Ultrafilter.map s ultra)
    (le_principal_iff.mpr hmem)
  refine ⟨x, ?_⟩
  have hmap : Filter.map s (ultra : Filter ℕ) ≤ 𝓝 x := by
    rw [← Ultrafilter.coe_map]
    exact hlim
  exact hmap

open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData MassGap.ReflAvg

/-- **`MixConvF` from lattice covariance, `CompOS` and the observer's bound.** At each pair `(P, Q)`
the mixed reading is bounded along `ultra` by `mixLatC_sq_le`: `latC(ΘP ∪ P)` converges along
`ultra` (`CompOS.1`, `adm_pairC`), `latSF(ΘQ ∪ Q)` is eventually bounded (`ClaySUGap.uB`), and the
half-space memberships hold eventually.

DERIVED: `0` the plane; `1` the unit bound margin. -/
theorem mixConvF_of_cov (hN2 : 2 ≤ N) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (Φ0 W).PhysRange r) (f : Idx4 → LField (MassGap.SUN.SU N))
    (bareO : Ix0 → LField (MassGap.SUN.SU N)) (z : Chan → ℕ → ℝ)
    (hcov : ReflCovLat (CbF f bareO z) 0)
    (hCO : CompOS (ne_zero_of_two_le hN2) (CbF f bareO z)) :
    MixConvF hN2 W f bareO z r := by
  intro P Q
  have hN := ne_zero_of_two_le hN2
  have hpos := Flow.posPreserving_of_physRange hN (Φ0 W) hphys 0
  have hUL := build_unifLocal (rhoD f z) (bareD f bareO)
  have hL := hCO.1 _ _ (adm_pairC (CbF f bareO z) P P)
  set x := contC hN (CbF f bareO z) (pairC (CbF f bareO z) 0 P.1 P.1)
  have hLb : ∀ᶠ k in (ultra : Filter ℕ),
      |latC hN (CbF f bareO z) k (pairC (CbF f bareO z) 0 P.1 P.1)| ≤ |x| + 1 := by
    have hball := hL.eventually (Metric.ball_mem_nhds x one_pos)
    filter_upwards [hball] with k hk
    rw [Real.dist_eq] at hk
    calc |latC hN (CbF f bareO z) k (pairC (CbF f bareO z) 0 P.1 P.1)|
        = |(latC hN (CbF f bareO z) k (pairC (CbF f bareO z) 0 P.1 P.1) - x) + x| := by
          rw [sub_add_cancel]
      _ ≤ |latC hN (CbF f bareO z) k (pairC (CbF f bareO z) 0 P.1 P.1) - x| + |x| :=
          abs_add_le _ _
      _ ≤ |x| + 1 := by linarith
  obtain ⟨D, hD⟩ := ClaySUGap.uB hN W hU (Fin Q.1.1 ⊕ Fin Q.1.1) (pairFam 0 Q.1 Q.1)
  have hDb : ∀ᶠ k in atTop, |latSF hN (Φ0 W) k (pairFam 0 Q.1 Q.1)| ≤ D := by
    have h0 := hD 0 (fun _ => 0)
    simp only [site_zero, TestFn.translate_zero, Prod.mk.eta] at h0
    exact h0
  have hev : ∀ᶠ k in atTop,
      prodSmear (dySpacing N k) (cMono hN (CbF f bareO z) k P.1)
          ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0
        ∧ prodSmear (dySpacing N k) ((Φ0 W).mono k Q.1)
          ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0
        ∧ |latSF hN (Φ0 W) k (pairFam 0 Q.1 Q.1)| ≤ D :=
    (eventually_cMono_mem hN (CbF f bareO z) hUL P).and
      ((eventually_flow_mem (Φ0 W) hpos Q).and hDb)
  refine exists_tendsto_ultra_of_ultra _ (Real.sqrt ((|x| + 1) * D)) ?_
  filter_upwards [hev.filter_mono ultra_le, hLb] with k hk hLk
  obtain ⟨hPk, hQk, hDk⟩ := hk
  refine Real.abs_le_sqrt ?_
  have hsq := mixLatC_sq_le hN (CbF f bareO z) (Φ0 W) 0 hcov k P.1 Q.1 hPk hQk
  exact hsq.trans (mul_le_mul hLk hDk (abs_nonneg _) (by positivity))

/-- **`MixConvF` at the averaged composites** from `CompOS (CbR N z)`, `hU` and `hphys`
(`reflCovLat_CbR`). DERIVED: `0` the plane. -/
theorem mixConvF_R (hN2 : 2 ≤ N) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (Φ0 W).PhysRange r) (z : Chan → ℕ → ℝ)
    (hCO : CompOS (ne_zero_of_two_le hN2) (CbR N z)) :
    MixConvF hN2 W (fR N) (bR N) z r :=
  mixConvF_of_cov hN2 W hU hphys (fR N) (bR N) z (reflCovLat_CbR z) hCO

end Conv

/-! ## 3. The capstone -/

section Capstone

open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData MassGap.ReflAvg

/-- **The SU capstone at the reflection-averaged composites, without `hJ` and `hMC`**:
`ReflAvg.clayStatementAt_SU_reflAvg` with `hMC` discharged by `mixConvF_R`.

The inputs: `hU`, `hphys` at one `r`, `hfar`, `z` with `hz`, `hzS`, `hzP`, `G`, `hK`, `hAF`, `hObs`,
`hWard`, `hCO`, `hA`; `hK`, `hWard` read `rhoD (fR N) z`, and `hCO`, `hA` the averaged composites
`CbR N z`.

DERIVED: `2` the least colour count and the limits of the scalar and pseudoscalar factors; `0` the
plane; `4` the dimension. -/
theorem clayStatementAt_SU_reflAvg' (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (z : Chan → ℕ → ℝ) (hz : ∀ c k, z c k ≠ 0)
    (hzS : Tendsto (fun k => z .sc k * dySpacing N k ^ 4) atTop (𝓝 2))
    (hzP : Tendsto (fun k => z .ps k * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) (rhoD (fR N) z) G)
    (hAF : AFCoefficient N G)
    (hObs : NonGaussLink.ObsThreePoint (ne_zero_of_two_le hN2) z)
    (hWard : WardT (ne_zero_of_two_le hN2) (rhoD (fR N) z))
    (hCO : CompOS (ne_zero_of_two_le hN2) (CbR N z))
    (hA : ApproxK (kernC (ne_zero_of_two_le hN2) (CbR N z) 0) (mixKR hN2 W z r) (gramF hN2 W r)) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  clayStatementAt_SU_reflAvg hN2 W ht hU hphys hfar z hz hzS hzP G hK hAF hObs hWard hCO hA
    (mixConvF_R hN2 W hU hphys z hCO)

end Capstone

end MassGap.MixConvRP

end

#print axioms MassGap.MixConvRP.sgnC_sq
#print axioms MassGap.MixConvRP.abs_sgnC
#print axioms MassGap.MixConvRP.rMixC_sq_le
#print axioms MassGap.MixConvRP.mixLatC_sq_le
#print axioms MassGap.MixConvRP.exists_tendsto_ultra_of_ultra
#print axioms MassGap.MixConvRP.mixConvF_of_cov
#print axioms MassGap.MixConvRP.mixConvF_R
#print axioms MassGap.MixConvRP.clayStatementAt_SU_reflAvg'
