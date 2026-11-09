import Mathlib
import MassGap.ContinuumField
import MassGap.ContinuumSchwinger
import MassGap.ContinuumSep
import MassGap.ExistencePoint
import MassGap.PointReadingRatio
import MassGap.ShortDistanceRunning

noncomputable section

/-!
# MassGap.SmearedCubeLocal — the one-scale comparison at the strength E reads

`ShortDistanceRunning.PointCubeLocalAlong` compares lattice point readings with the cube reading at the same
physical scale. The chain reads it only through E (`ContinuumSep.DiagBoundSepAlong` at `zCanAlong`), and E asks
for smeared readings: fields against bounded test functions of compact support. This module states the
one-scale comparison at that strength and places it in the capstone.

* `SmearCubeLocalAlong hN βs O s₀`: for every monomial `P` that is `d` above the plane and `d`-separated,
  `d < s₀`, one `C` with `latSkR(rho1)(θP ∪ P) ≤ C · x(d)^n` eventually, `x(d) = refReadingAlong hN βs O d d`
  and `n` the number of insertions of `P`.
* `latSkR_zCan_pair_along`: a reflected pair of `n` insertions reads `((1/√r)²)ⁿ` times its unit-strength
  reading.
* `diagBoundSep_zCan_of_smearCubeLocal_along`: (R) and `SmearCubeLocalAlong` give E at `zCanAlong hN βs O s₀ s₀`.
  (R) carries `x(d') ≤ M · x(s₀)` at `d' = min(d, s₀/2)`, as in `pointRatio_of_running_along`.
* `smearCubeLocal_of_diagBoundSep_along`: the converse under (R). (R) also carries `x(s₀) ≤ m⁻¹ · x(d)` (the
  lower half of `ratio_bounds`), so E at the reference gives the bound at every scale `d < s₀`.
* `smearCubeLocal_iff_diagBoundSep_along`: under (R), `SmearCubeLocalAlong` is E at the reference.
* `smearCubeLocal_of_pointCubeLocal_along`: under (R), `PointCubeLocalAlong` gives `SmearCubeLocalAlong`.
* `not_pointCubeLocal_of_unbounded`: a family whose point readings at one margin exceed every multiple of
  `a^{8n} x(d)^n` infinitely often fails `PointCubeLocalAlong`.

The converse of `smearCubeLocal_of_pointCubeLocal_along` fails. A reflection-positive lattice family can add to
an asymptotically free one an independent component of amplitude `a³` that is correlated only along lattice
lines: (R), E, N₃ and (P) are those of the base, since every smeared reading of the component is smaller than
the base's by a positive power of `a`, while its point reading at margin `d` exceeds `a⁸ x(d)` by `a^{−2}`.

DERIVED (module-wide): `0` the reflection plane and signs; `1` where `log` changes sign; `2` the two copies of a
monomial in a reflected pair, the square of `1/√r` and the halving `s₀/2`; `8` the canonical dimension count of
the point readings, as in `PointCubeLocalAlong`.
-/

namespace MassGap.SmearedCubeLocal

open Filter Topology MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumCluster MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ExistencePoint
  MassGap.ShortDistanceRunning

variable {N : ℕ}

/-! ## 1. The statement -/

/-- **The one-scale comparison on smeared readings.** For every monomial `P` that is `d` above the plane and
`d`-separated, at a margin `d < s₀`, one `C` bounds its unit-strength reflected diagonal by `C` times the
`n`-th power of the cube-pair reading at the same scale `d`, eventually in the step. -/
def SmearCubeLocalAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (s₀ : ℝ) : Prop :=
  ∀ (P : Mono N) (d : ℝ), 0 < d → d < s₀ → ContinuumSep.sepPos 0 d P → ∃ C : ℝ, ∀ᶠ k in atTop,
    latSkRAlong hN βs (rho1Along hN βs) k (pairFam 0 P P) ≤ C * refReadingAlong hN βs O d d k ^ P.1

/-- A reflected pair of `n` insertions at the canonical factor reads `((1/√r)²)ⁿ` times its unit-strength
reading. -/
theorem latSkR_zCan_pair_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) (k : ℕ)
    (P : Mono N) :
    latSkRAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) k (pairFam 0 P P)
      = ((1 / Real.sqrt (refReadingAlong hN βs O t ℓ k)) ^ 2) ^ P.1
          * latSkRAlong hN βs (rho1Along hN βs) k (pairFam 0 P P) := by
  rw [latSkR_zCan_eq_along, Fintype.card_sum, Fintype.card_fin, ← pow_mul, two_mul]

/-! ## 2. E from (R) and the one-scale comparison, and back -/

/-- **E from (R) and the one-scale comparison on smeared readings.** -/
theorem diagBoundSep_zCan_of_smearCubeLocal_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N))
    {s₀ K δ : ℝ} (hs₀ : 0 < s₀) (hs₀1 : s₀ < 1) (hR : RunningBelowAlong hN βs O s₀ K δ)
    (hL : SmearCubeLocalAlong hN βs O s₀) :
    ContinuumSep.DiagBoundSepAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O s₀ s₀)) 0 := by
  intro P
  obtain ⟨d, hd, hsep⟩ := P.2
  set d' := min d (s₀ / 2) with hd'_def
  have hd' : 0 < d' := lt_min hd (by positivity)
  have hd's : d' < s₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hd'1 : d' < 1 := hd's.trans hs₀1
  obtain ⟨C, hC⟩ := hL P.1 d' hd' hd's (ContinuumSep.sepPos_mono hsep (min_le_left d (s₀ / 2)))
  set M := Real.exp (ShortDistanceRunning.runErr K δ d' s₀) * (Real.log s₀ ^ 2 / Real.log d' ^ 2) with hM_def
  have hM : 0 ≤ M := by positivity
  refine ⟨max C 0 * M ^ P.1.1, ?_⟩
  filter_upwards [hC, hR d' s₀ hd' hd's le_rfl] with k hk hrb
  have hx := hrb.1
  have hx' := hrb.2.1
  have hratio := (ShortDistanceRunning.ratio_bounds hd' hd'1 hs₀ hs₀1 hrb).1
  have hxle : refReadingAlong hN βs O d' d' k ≤ M * refReadingAlong hN βs O s₀ s₀ k := by
    rwa [div_le_iff₀ hx'] at hratio
  rw [latSkR_zCan_pair_along]
  set r := refReadingAlong hN βs O s₀ s₀ k with hr_def
  set x := refReadingAlong hN βs O d' d' k with hx_def
  set u := latSkRAlong hN βs (rho1Along hN βs) k (pairFam 0 P.1 P.1) with hu_def
  set n := P.1.1 with hn_def
  have hs : (1 / Real.sqrt r) ^ 2 = r⁻¹ := by
    rw [div_pow, one_pow, Real.sq_sqrt hx'.le, one_div]
  rw [hs]
  have hu : u ≤ max C 0 * x ^ n :=
    hk.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hx.le _))
  have hpow : x ^ n ≤ (M * r) ^ n := pow_le_pow_left₀ hx.le hxle n
  have hu' : u ≤ max C 0 * (M * r) ^ n :=
    hu.trans (mul_le_mul_of_nonneg_left hpow (le_max_right _ _))
  have hinv : r⁻¹ ^ n * r ^ n = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hx'.ne', one_pow]
  calc r⁻¹ ^ n * u ≤ r⁻¹ ^ n * (max C 0 * (M * r) ^ n) :=
        mul_le_mul_of_nonneg_left hu' (pow_nonneg (inv_nonneg.mpr hx'.le) _)
    _ = max C 0 * M ^ n * (r⁻¹ ^ n * r ^ n) := by rw [mul_pow]; ring
    _ = max C 0 * M ^ n := by rw [hinv, mul_one]

/-- **The converse under (R)**: E at the reference gives the one-scale comparison at every `d < s₀`. -/
theorem smearCubeLocal_of_diagBoundSep_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N))
    {s₀ K δ : ℝ} (hs₀1 : s₀ < 1) (hR : RunningBelowAlong hN βs O s₀ K δ)
    (hE : ContinuumSep.DiagBoundSepAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O s₀ s₀)) 0) :
    SmearCubeLocalAlong hN βs O s₀ := by
  intro P d hd hds hsep
  have hs₀ : 0 < s₀ := hd.trans hds
  have hd1 : d < 1 := hds.trans hs₀1
  obtain ⟨C, hC⟩ := hE ⟨P, d, hd, hsep⟩
  set m := Real.exp (-ShortDistanceRunning.runErr K δ d s₀) * (Real.log s₀ ^ 2 / Real.log d ^ 2) with hm_def
  have hm : 0 < m := by
    have h1 := ShortDistanceRunning.log_sq_pos hd hd1
    have h2 := ShortDistanceRunning.log_sq_pos hs₀ hs₀1
    positivity
  refine ⟨max C 0 * m⁻¹ ^ P.1, ?_⟩
  filter_upwards [hC, hR d s₀ hd hds le_rfl] with k hk hrb
  have hk' : latSkRAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O s₀ s₀)) k
      (pairFam 0 P P) ≤ C := hk
  rw [latSkR_zCan_pair_along] at hk'
  have hx := hrb.1
  have hr := hrb.2.1
  have hlo := (ShortDistanceRunning.ratio_bounds hd hd1 hs₀ hs₀1 hrb).2
  set r := refReadingAlong hN βs O s₀ s₀ k with hr_def
  set x := refReadingAlong hN βs O d d k with hx_def
  set u := latSkRAlong hN βs (rho1Along hN βs) k (pairFam 0 P P) with hu_def
  set n := P.1 with hn_def
  have hs : (1 / Real.sqrt r) ^ 2 = r⁻¹ := by
    rw [div_pow, one_pow, Real.sq_sqrt hr.le, one_div]
  rw [hs] at hk'
  have hrle : r ≤ m⁻¹ * x := by
    rw [le_div_iff₀ hr] at hlo
    rw [inv_mul_eq_div, le_div_iff₀ hm, mul_comm]
    exact hlo
  have hinv : r ^ n * r⁻¹ ^ n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hr.ne', one_pow]
  have hrn : 0 ≤ r ^ n := pow_nonneg hr.le n
  have hu : u ≤ C * r ^ n := by
    calc u = r ^ n * (r⁻¹ ^ n * u) := by rw [← mul_assoc, hinv, one_mul]
      _ ≤ r ^ n * C := mul_le_mul_of_nonneg_left hk' hrn
      _ = C * r ^ n := mul_comm _ _
  have hpow : r ^ n ≤ (m⁻¹ * x) ^ n := pow_le_pow_left₀ hr.le hrle n
  calc u ≤ C * r ^ n := hu
    _ ≤ max C 0 * r ^ n := mul_le_mul_of_nonneg_right (le_max_left _ _) hrn
    _ ≤ max C 0 * (m⁻¹ * x) ^ n := mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
    _ = max C 0 * m⁻¹ ^ n * x ^ n := by rw [mul_pow]; ring

/-- **Under (R), the one-scale comparison on smeared readings is E at the reference.** -/
theorem smearCubeLocal_iff_diagBoundSep_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N))
    {s₀ K δ : ℝ} (hs₀ : 0 < s₀) (hs₀1 : s₀ < 1) (hR : RunningBelowAlong hN βs O s₀ K δ) :
    SmearCubeLocalAlong hN βs O s₀ ↔
      ContinuumSep.DiagBoundSepAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O s₀ s₀)) 0 :=
  ⟨diagBoundSep_zCan_of_smearCubeLocal_along hN βs O hs₀ hs₀1 hR,
    smearCubeLocal_of_diagBoundSep_along hN βs O hs₀1 hR⟩

/-- **Under (R), the point comparison gives the smeared one.** -/
theorem smearCubeLocal_of_pointCubeLocal_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N))
    {s₀ K δ : ℝ} (hs₀ : 0 < s₀) (hs₀1 : s₀ < 1) (hR : RunningBelowAlong hN βs O s₀ K δ)
    (hL : PointCubeLocalAlong hN βs O s₀) : SmearCubeLocalAlong hN βs O s₀ :=
  smearCubeLocal_of_diagBoundSep_along hN βs O hs₀1 hR
    (PointReadingRatio.diagBoundSep_zCan_of_pointRatio_along hN βs O s₀ s₀
      (pointRatio_of_running_along hN βs O hs₀ hs₀1 hR hL))

/-! ## 3. The capstones -/

/-! ## 4. The control for the point comparison -/

/-- **Unbounded point readings fail the point comparison.** If, at one list of fields and one margin
`d < s₀`, every multiple `C · a^{8n} · x(d)^n` is exceeded by some admissible point reading infinitely often in
the step, `PointCubeLocalAlong` fails. -/
theorem not_pointCubeLocal_of_unbounded (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) {s₀ : ℝ}
    (n : ℕ) (L : Fin n → LField (MassGap.SUN.SU N)) {d : ℝ} (hd : 0 < d) (hds : d < s₀)
    (hun : ∀ C : ℝ, ∃ᶠ k in atTop, ∃ p : Fin n → ISite,
      ContinuumSep.sepPos 0 d (ptMono L (fun i => site (dySpacing N k) (p i))) ∧
      C * dySpacing N k ^ (8 * n) * refReadingAlong hN βs O d d k ^ n
        < latSkRAlong hN βs (rho1Along hN βs) k
            (pairFam 0 (ptMono L (fun i => site (dySpacing N k) (p i)))
              (ptMono L (fun i => site (dySpacing N k) (p i))))) :
    ¬ PointCubeLocalAlong hN βs O s₀ := by
  intro h
  obtain ⟨C, hC⟩ := h n L d hd hds
  obtain ⟨k, ⟨p, hp, hlt⟩, hk⟩ := ((hun C).and_eventually hC).exists
  exact absurd (hk p hp) (not_le.mpr hlt)

end MassGap.SmearedCubeLocal

#print axioms MassGap.SmearedCubeLocal.latSkR_zCan_pair_along
#print axioms MassGap.SmearedCubeLocal.diagBoundSep_zCan_of_smearCubeLocal_along
#print axioms MassGap.SmearedCubeLocal.smearCubeLocal_of_diagBoundSep_along
#print axioms MassGap.SmearedCubeLocal.smearCubeLocal_iff_diagBoundSep_along
#print axioms MassGap.SmearedCubeLocal.smearCubeLocal_of_pointCubeLocal_along
#print axioms MassGap.SmearedCubeLocal.not_pointCubeLocal_of_unbounded
