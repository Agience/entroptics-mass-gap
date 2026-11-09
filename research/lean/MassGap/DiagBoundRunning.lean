import Mathlib
import MassGap.FieldDomination
import MassGap.DiagBoundProof
import MassGap.ExistencePoint
import MassGap.PointReadingRatio
import MassGap.ShortDistanceRunning

noncomputable section

/-!
# MassGap.DiagBoundRunning — what the route `RunningBelow` + `PointCubeLocal` → `hD` uses of the running

The route to `hD` (E at `zCanAlong hN βs O s₀ s₀`) through `ShortDistanceRunning.pointRatio_of_running_along`
and `PointReadingRatio.diagBoundSep_zCan_of_pointRatio_along` reads (R) at one pair of scales `(d', s₀)` and only
through the upper half of `ShortDistanceRunning.ratio_bounds`: `x(d') ≤ M · x(s₀)`, with
`x(s) = refReadingAlong hN βs O s s`. The positivity of `x(d')`, which the route also takes from (R), is the
reflection form (`FieldDomination.refReadingAlong_eventually_nonneg`). This module names the two one-sided
comparisons and places them.

* `ScaleUpAlong hN βs O s₀`: at every `0 < d < s₀`, one `M` with `x(d) ≤ M · x(s₀)` eventually in the step.
* `ScaleDownAlong hN βs O s₀`: at every `0 < d < s₀`, one `m` with `x(s₀) ≤ m · x(d)` eventually in the step.
* `scaleUp_of_running_along`, `scaleDown_of_running_along`: (R) gives both (the two halves of `ratio_bounds`).
* `pointRatio_of_scaleUp_along`, `diagBoundSep_of_scaleUp_pointCubeLocal_along`: `ScaleUpAlong` and
  `PointCubeLocalAlong` give `PointRatioAlong`, hence E. (R) is not used: no positivity of the reference reading,
  no logarithmic modulus.
* `diagBoundSep_of_scaleUp_smearCubeLocal_along`: `ScaleUpAlong` and `SmearCubeLocalAlong` give E.
* `scaleUp_of_diagBoundSep_along`: E at an eventually positive reference reading gives `ScaleUpAlong`, at the
  cube monomial `ContinuumNontrivial.sepCube 0 O hd d`. So the part of (R) that the route uses is a consequence
  of E itself.
* `smearCubeLocal_of_scaleDown_diagBoundSep_along`: E, `ScaleDownAlong` and the positivity of the reference
  reading give `SmearCubeLocalAlong`.
* `diagBoundSep_iff_scaleUp_smearCubeLocal_along`: under `ScaleDownAlong` and the positivity of the reference
  reading, E is `ScaleUpAlong ∧ SmearCubeLocalAlong`.
* `diagBoundSep_of_running_pointCubeLocal_along`: the route itself, (R) and `PointCubeLocalAlong` give E. Its
  inputs imply E, so the remainder `RunningBelowAlong ∧ PointCubeLocalAlong` is not weaker than E.

DERIVED (module-wide): `0` the reflection plane and the lower bound of a reading; `1` the one insertion of the cube
monomial and where `log` changes sign; `2` the halving `s₀/2`.
-/

namespace MassGap.DiagBoundRunning

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumCluster MassGap.ExistenceReduce MassGap.NonTrivialCanonical
  MassGap.ExistencePoint MassGap.ShortDistanceRunning MassGap.SmearedCubeLocal Filter

variable {N : ℕ}

/-! ## 1. The two one-sided comparisons -/

/-- **The cube reading at a smaller scale is bounded by the reference.** At every `0 < d < s₀` one `M` with
`refReadingAlong hN βs O d d k ≤ M · refReadingAlong hN βs O s₀ s₀ k` eventually in the step. -/
def ScaleUpAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (s₀ : ℝ) : Prop :=
  ∀ d : ℝ, 0 < d → d < s₀ → ∃ M : ℝ, ∀ᶠ k in atTop,
    refReadingAlong hN βs O d d k ≤ M * refReadingAlong hN βs O s₀ s₀ k

/-- **The reference is bounded by the cube reading at a smaller scale.** At every `0 < d < s₀` one `m` with
`refReadingAlong hN βs O s₀ s₀ k ≤ m · refReadingAlong hN βs O d d k` eventually in the step. -/
def ScaleDownAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (s₀ : ℝ) : Prop :=
  ∀ d : ℝ, 0 < d → d < s₀ → ∃ m : ℝ, ∀ᶠ k in atTop,
    refReadingAlong hN βs O s₀ s₀ k ≤ m * refReadingAlong hN βs O d d k

/-- `0 ≤ x ≤ M r` gives `xⁿ ≤ Mⁿ rⁿ`. -/
theorem pow_le_of_le_mul {x r M : ℝ} (n : ℕ) (hx : 0 ≤ x) (h : x ≤ M * r) :
    x ^ n ≤ M ^ n * r ^ n := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ hx h n

/-! ## 2. (R) gives both -/

/-- **(R) gives `ScaleUpAlong`**: the upper half of `ratio_bounds` at the pair `(d, s₀)`. -/
theorem scaleUp_of_running_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N))
    {s₀ K δ : ℝ} (hs₀1 : s₀ < 1) (hR : RunningBelowAlong hN βs O s₀ K δ) : ScaleUpAlong hN βs O s₀ := by
  intro d hd hds
  have hs₀ : 0 < s₀ := hd.trans hds
  refine ⟨Real.exp (runErr K δ d s₀) * (Real.log s₀ ^ 2 / Real.log d ^ 2), ?_⟩
  filter_upwards [hR d s₀ hd hds le_rfl] with k hrb
  have h := (ratio_bounds hd (hds.trans hs₀1) hs₀ hs₀1 hrb).1
  rwa [div_le_iff₀ hrb.2.1] at h

/-- **(R) gives `ScaleDownAlong`**: the lower half of `ratio_bounds` at the pair `(d, s₀)`. -/
theorem scaleDown_of_running_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N))
    {s₀ K δ : ℝ} (hs₀1 : s₀ < 1) (hR : RunningBelowAlong hN βs O s₀ K δ) :
    ScaleDownAlong hN βs O s₀ := by
  intro d hd hds
  have hs₀ : 0 < s₀ := hd.trans hds
  have hd1 : d < 1 := hds.trans hs₀1
  set m := Real.exp (-runErr K δ d s₀) * (Real.log s₀ ^ 2 / Real.log d ^ 2) with hm_def
  have hm : 0 < m := by
    have h1 := log_sq_pos hd hd1
    have h2 := log_sq_pos hs₀ hs₀1
    positivity
  refine ⟨m⁻¹, ?_⟩
  filter_upwards [hR d s₀ hd hds le_rfl] with k hrb
  have h := (ratio_bounds hd hd1 hs₀ hs₀1 hrb).2
  rw [le_div_iff₀ hrb.2.1] at h
  rw [inv_mul_eq_div, le_div_iff₀ hm, mul_comm]
  exact h

/-! ## 3. E from `ScaleUpAlong` and a one-scale comparison -/

/-- **`ScaleUpAlong` and `PointCubeLocalAlong` give `PointRatioAlong`.** -/
theorem pointRatio_of_scaleUp_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) {s₀ : ℝ}
    (hs₀ : 0 < s₀) (hU : ScaleUpAlong hN βs O s₀) (hL : PointCubeLocalAlong hN βs O s₀) :
    PointReadingRatio.PointRatioAlong hN βs O s₀ s₀ := by
  intro n L d hd
  set d' := min d (s₀ / 2) with hd'_def
  have hd' : 0 < d' := lt_min hd (by positivity)
  have hd's : d' < s₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨C, hC⟩ := hL n L d' hd' hd's
  obtain ⟨M, hM⟩ := hU d' hd' hd's
  refine ⟨max C 0 * M ^ n, ?_⟩
  filter_upwards [hC, hM, FieldDomination.refReadingAlong_eventually_nonneg hN βs O (ℓ := d') hd']
    with k hk hm hx p hp
  have hu := hk p (ContinuumSep.sepPos_mono hp (min_le_left d (s₀ / 2)))
  have ha : 0 ≤ dySpacing N k ^ (8 * n) :=
    pow_nonneg (dySpacing_pos (one_le_of_ne_zero hN) k).le _
  have hpow := pow_le_of_le_mul n hx hm
  calc _ ≤ C * dySpacing N k ^ (8 * n) * refReadingAlong hN βs O d' d' k ^ n := hu
    _ ≤ max C 0 * dySpacing N k ^ (8 * n) * refReadingAlong hN βs O d' d' k ^ n := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg ha (pow_nonneg hx n))
    _ ≤ max C 0 * dySpacing N k ^ (8 * n) * (M ^ n * refReadingAlong hN βs O s₀ s₀ k ^ n) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg (le_max_right _ _) ha)
    _ = max C 0 * M ^ n * dySpacing N k ^ (8 * n) * refReadingAlong hN βs O s₀ s₀ k ^ n := by ring

/-- **E from `ScaleUpAlong` and `PointCubeLocalAlong`.** -/
theorem diagBoundSep_of_scaleUp_pointCubeLocal_along (hN : N ≠ 0) (βs : ℕ → ℝ)
    (O : LField (MassGap.SUN.SU N)) {s₀ : ℝ} (hs₀ : 0 < s₀) (hU : ScaleUpAlong hN βs O s₀)
    (hL : PointCubeLocalAlong hN βs O s₀) :
    ContinuumSep.DiagBoundSepAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O s₀ s₀)) 0 :=
  PointReadingRatio.diagBoundSep_zCan_of_pointRatio_along hN βs O s₀ s₀
    (pointRatio_of_scaleUp_along hN βs O hs₀ hU hL)

/-- **E from `ScaleUpAlong` and `SmearCubeLocalAlong`.** -/
theorem diagBoundSep_of_scaleUp_smearCubeLocal_along (hN : N ≠ 0) (βs : ℕ → ℝ)
    (O : LField (MassGap.SUN.SU N)) {s₀ : ℝ} (hs₀ : 0 < s₀) (hU : ScaleUpAlong hN βs O s₀)
    (hL : SmearCubeLocalAlong hN βs O s₀) :
    ContinuumSep.DiagBoundSepAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O s₀ s₀)) 0 := by
  intro P
  obtain ⟨d, hd, hsep⟩ := P.2
  set d' := min d (s₀ / 2) with hd'_def
  have hd' : 0 < d' := lt_min hd (by positivity)
  have hd's : d' < s₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨C, hC⟩ := hL P.1 d' hd' hd's (ContinuumSep.sepPos_mono hsep (min_le_left d (s₀ / 2)))
  obtain ⟨M, hM⟩ := hU d' hd' hd's
  refine ⟨max (max C 0 * M ^ P.1.1) 0, ?_⟩
  filter_upwards [hC, hM, FieldDomination.refReadingAlong_eventually_nonneg hN βs O (ℓ := d') hd']
    with k hk hm hx
  show latSkRAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O s₀ s₀)) k
      (pairFam 0 P.1 P.1) ≤ _
  rw [latSkR_zCan_pair_along]
  refine DiagBoundProof.ratio_le _ ?_
  have hpow := pow_le_of_le_mul P.1.1 hx hm
  calc _ ≤ C * refReadingAlong hN βs O d' d' k ^ P.1.1 := hk
    _ ≤ max C 0 * refReadingAlong hN βs O d' d' k ^ P.1.1 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hx _)
    _ ≤ max C 0 * (M ^ P.1.1 * refReadingAlong hN βs O s₀ s₀ k ^ P.1.1) :=
        mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
    _ = max C 0 * M ^ P.1.1 * refReadingAlong hN βs O s₀ s₀ k ^ P.1.1 := by ring

/-! ## 4. E gives `ScaleUpAlong`, and with `ScaleDownAlong` the one-scale comparison -/

/-- **E gives `ScaleUpAlong`** at an eventually positive reference reading: E read at the cube monomial of
side `d` at margin `d`. -/
theorem scaleUp_of_diagBoundSep_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) {s₀ : ℝ}
    (hpos : ∀ᶠ k in atTop, 0 < refReadingAlong hN βs O s₀ s₀ k)
    (hE : ContinuumSep.DiagBoundSepAlong hN βs
      (Renorm.connectedAlong hN βs (zCanAlong hN βs O s₀ s₀)) 0) :
    ScaleUpAlong hN βs O s₀ := by
  intro d hd _
  obtain ⟨C, hC⟩ := hE (ContinuumNontrivial.sepCube 0 O hd d)
  refine ⟨C, ?_⟩
  filter_upwards [hC, hpos] with k hk hr
  have hk' : latSkRAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O s₀ s₀)) k
      (pairFam 0 (refMono O d d) (refMono O d d)) ≤ C := hk
  rw [latSkR_zCan_pair_along] at hk'
  have hu := DiagBoundProof.le_of_ratio _ hr hk'
  have h1 : refReadingAlong hN βs O s₀ s₀ k ^ (refMono O d d).1 = refReadingAlong hN βs O s₀ s₀ k :=
    pow_one _
  rw [h1] at hu
  exact hu

/-- **E, `ScaleDownAlong` and the positivity of the reference give `SmearCubeLocalAlong`.** -/
theorem smearCubeLocal_of_scaleDown_diagBoundSep_along (hN : N ≠ 0) (βs : ℕ → ℝ)
    (O : LField (MassGap.SUN.SU N)) {s₀ : ℝ} (hD : ScaleDownAlong hN βs O s₀)
    (hpos : ∀ᶠ k in atTop, 0 < refReadingAlong hN βs O s₀ s₀ k)
    (hE : ContinuumSep.DiagBoundSepAlong hN βs
      (Renorm.connectedAlong hN βs (zCanAlong hN βs O s₀ s₀)) 0) :
    SmearCubeLocalAlong hN βs O s₀ := by
  intro P d hd hds hsep
  obtain ⟨C, hC⟩ := hE ⟨P, d, hd, hsep⟩
  obtain ⟨m, hm⟩ := hD d hd hds
  refine ⟨max C 0 * m ^ P.1, ?_⟩
  filter_upwards [hC, hm, hpos] with k hk hmk hr
  have hk' : latSkRAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O s₀ s₀)) k
      (pairFam 0 P P) ≤ C := hk
  rw [latSkR_zCan_pair_along] at hk'
  have hu := DiagBoundProof.le_of_ratio _ hr hk'
  have hpow := pow_le_of_le_mul P.1 hr.le hmk
  calc _ ≤ C * refReadingAlong hN βs O s₀ s₀ k ^ P.1 := hu
    _ ≤ max C 0 * refReadingAlong hN βs O s₀ s₀ k ^ P.1 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hr.le _)
    _ ≤ max C 0 * (m ^ P.1 * refReadingAlong hN βs O d d k ^ P.1) :=
        mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
    _ = max C 0 * m ^ P.1 * refReadingAlong hN βs O d d k ^ P.1 := by ring

/-- **Under `ScaleDownAlong` and a positive reference, E is `ScaleUpAlong ∧ SmearCubeLocalAlong`.** -/
theorem diagBoundSep_iff_scaleUp_smearCubeLocal_along (hN : N ≠ 0) (βs : ℕ → ℝ)
    (O : LField (MassGap.SUN.SU N)) {s₀ : ℝ} (hs₀ : 0 < s₀) (hD : ScaleDownAlong hN βs O s₀)
    (hpos : ∀ᶠ k in atTop, 0 < refReadingAlong hN βs O s₀ s₀ k) :
    ContinuumSep.DiagBoundSepAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O s₀ s₀)) 0
      ↔ ScaleUpAlong hN βs O s₀ ∧ SmearCubeLocalAlong hN βs O s₀ :=
  ⟨fun hE => ⟨scaleUp_of_diagBoundSep_along hN βs O hpos hE,
      smearCubeLocal_of_scaleDown_diagBoundSep_along hN βs O hD hpos hE⟩,
    fun h => diagBoundSep_of_scaleUp_smearCubeLocal_along hN βs O hs₀ h.1 h.2⟩

/-! ## 5. The route -/

/-- **The route: (R) and `PointCubeLocalAlong` give E**, through `ScaleUpAlong`. -/
theorem diagBoundSep_of_running_pointCubeLocal_along (hN : N ≠ 0) (βs : ℕ → ℝ)
    (O : LField (MassGap.SUN.SU N)) {s₀ K δ : ℝ} (hs₀ : 0 < s₀) (hs₀1 : s₀ < 1)
    (hR : RunningBelowAlong hN βs O s₀ K δ) (hL : PointCubeLocalAlong hN βs O s₀) :
    ContinuumSep.DiagBoundSepAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O s₀ s₀)) 0 :=
  diagBoundSep_of_scaleUp_pointCubeLocal_along hN βs O hs₀ (scaleUp_of_running_along hN βs O hs₀1 hR) hL

/-- **The route at the couplings `dyBeta`**: `RunningBelow` and `PointCubeLocal` give `hD` of
`ExistenceReduce.clay_canonical` at `(t, ℓ) = (s₀, s₀)`. -/
theorem diagBoundSep_of_running_pointCubeLocal (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {s₀ K δ : ℝ}
    (hs₀ : 0 < s₀) (hs₀1 : s₀ < 1) (hR : RunningBelow hN O s₀ K δ) (hL : PointCubeLocal hN O s₀) :
    ContinuumSep.DiagBoundSep hN (Renorm.connected hN (zCan hN O s₀ s₀)) 0 :=
  diagBoundSep_of_running_pointCubeLocal_along hN (dyBeta (one_le_of_ne_zero hN)) O hs₀ hs₀1 hR hL

/-- **`hD` from `ScaleUp` and `PointCubeLocal` at the couplings `dyBeta`.** -/
theorem diagBoundSep_of_scaleUp_pointCubeLocal (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {s₀ : ℝ}
    (hs₀ : 0 < s₀) (hU : ScaleUpAlong hN (dyBeta (one_le_of_ne_zero hN)) O s₀)
    (hL : PointCubeLocal hN O s₀) :
    ContinuumSep.DiagBoundSep hN (Renorm.connected hN (zCan hN O s₀ s₀)) 0 :=
  diagBoundSep_of_scaleUp_pointCubeLocal_along hN (dyBeta (one_le_of_ne_zero hN)) O hs₀ hU hL

end MassGap.DiagBoundRunning

#print axioms MassGap.DiagBoundRunning.pow_le_of_le_mul
#print axioms MassGap.DiagBoundRunning.scaleUp_of_running_along
#print axioms MassGap.DiagBoundRunning.scaleDown_of_running_along
#print axioms MassGap.DiagBoundRunning.pointRatio_of_scaleUp_along
#print axioms MassGap.DiagBoundRunning.diagBoundSep_of_scaleUp_pointCubeLocal_along
#print axioms MassGap.DiagBoundRunning.diagBoundSep_of_scaleUp_smearCubeLocal_along
#print axioms MassGap.DiagBoundRunning.scaleUp_of_diagBoundSep_along
#print axioms MassGap.DiagBoundRunning.smearCubeLocal_of_scaleDown_diagBoundSep_along
#print axioms MassGap.DiagBoundRunning.diagBoundSep_iff_scaleUp_smearCubeLocal_along
#print axioms MassGap.DiagBoundRunning.diagBoundSep_of_running_pointCubeLocal_along
#print axioms MassGap.DiagBoundRunning.diagBoundSep_of_running_pointCubeLocal
#print axioms MassGap.DiagBoundRunning.diagBoundSep_of_scaleUp_pointCubeLocal
