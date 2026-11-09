import Mathlib
import MassGap.ExistencePoint

noncomputable section

/-!
# MassGap.PointReadingRatio — bounded canonical point readings as a ratio at unit field strength

`ExistencePoint.PointDiagSep hN (zCan hN O t ℓ)` bounds the canonical reflected point readings. `zCan` is one
number for every field, `1/√(refReading_k)`, so a family of `2n` insertions reads `refReading_k^{−n}` times its
unit-strength reading (`NonTrivialCanonical.latSkR_zCan_eq`). This module states the bound with no
normalisation and proves it is the same statement.

* `PointRatio hN O t ℓ`: for every list of fields `L` and margin `d > 0` one `C` with, eventually in the step,
  `latSkR (rho1) (θP_pt ∪ P_pt) ≤ C · a_k^{8n} · refReading_k^n` on every point configuration that is `d` above
  the plane and pairwise `d`-separated. At `n = 1` it reads `g_k(x) ≤ C · refReading_k`, `g_k` the unit-strength
  reflected lattice point correlator: the point correlator at physical margin `d` against the reference
  cube-pair reading at `(t, ℓ)`, with no power of the spacing left over.
* `pointDiagSep_zCan_of_pointRatio`: `PointRatio` gives `PointDiagSep` at `zCan`, with no positivity
  hypothesis (at a non-positive reference reading `zCan = 0` and every reading with an insertion is `0`).
* `pointRatio_of_pointDiagSep`: the converse at an eventually positive reference reading.
* `diagBoundSep_zCan_of_pointRatio`: `PointRatio` gives E (`DiagBoundSep` at `zCan`).

Controls. The massive and the massless free fields satisfy `PointRatio`: their reflected point correlator at
margin `d` and the cube-pair reading are fixed multiples of `a^{2Δ}`, the same power, so the ratio is a
continuum ratio. The generalised free field with Källén–Lehmann weight `μ^{γ_k}` on `[m, 1/a_k]`,
`γ_k → ∞`, fails it at `n = 1`: for `d < t` the ratio grows like `(t/d)^{2γ_k}`.
-/

namespace MassGap.PointReadingRatio

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumCluster MassGap.ExistenceReduce MassGap.NonTrivialCanonical
  MassGap.ExistencePoint Filter

variable {N : ℕ}

/-- **Bounded point-to-reference ratio at unit field strength.** For every list of fields `L` and every
margin `d > 0` there is one `C` such that, eventually in the step, every configuration of lattice points
whose physical points are `d` above the plane and pairwise `d`-separated has unit-strength reflected
diagonal at most `C · a_k^{8n} · refReading_k^n`.

DERIVED: `8` in `8 * n` is `a⁸ = a⁴ · a⁴`, one cell volume per smeared field of a reflected pair
(`ScaleNorm`), one cube pair `refReading_k` per point insertion; `0` the reflection plane. -/
def PointRatioAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) : Prop :=
  ∀ (n : ℕ) (L : Fin n → LField (MassGap.SUN.SU N)) (d : ℝ), 0 < d → ∃ C : ℝ, ∀ᶠ k in atTop,
    ∀ p : Fin n → ISite,
      ContinuumSep.sepPos 0 d (ptMono L (fun i => site (dySpacing N k) (p i))) →
      latSkRAlong hN βs (rho1Along hN βs) k
          (pairFam 0 (ptMono L (fun i => site (dySpacing N k) (p i)))
            (ptMono L (fun i => site (dySpacing N k) (p i))))
        ≤ C * dySpacing N k ^ (8 * n) * refReadingAlong hN βs O t ℓ k ^ n

/-- `PointRatio` at the couplings `dyBeta`: `PointRatioAlong` at `βs = dyBeta`.

DERIVED: no numeral beyond those of the statement. -/
def PointRatio (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) : Prop :=
  PointRatioAlong hN (dyBeta (one_le_of_ne_zero hN)) O t ℓ


/-- The canonical reading of a reflected point pair of `n` insertions is `(1/√r)^{2n}` times its
unit-strength reading. -/
theorem latSkR_zCan_point_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) (k n : ℕ)
    (L : Fin n → LField (MassGap.SUN.SU N)) (y : Fin n → (Fin 4 → ℝ)) :
    latSkRAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) k (pairFam 0 (ptMono L y) (ptMono L y))
      = ((1 / Real.sqrt (refReadingAlong hN βs O t ℓ k)) ^ 2) ^ n
          * latSkRAlong hN βs (rho1Along hN βs) k (pairFam 0 (ptMono L y) (ptMono L y)) := by
  rw [latSkR_zCan_eq_along, Fintype.card_sum, Fintype.card_fin, ← pow_mul]
  congr 2
  show n + n = 2 * n
  ring

/-- `latSkR_zCan_point` at the couplings `dyBeta`: `latSkR_zCan_point_along` at `βs = dyBeta`.

DERIVED: no numeral beyond those of the statement. -/
theorem latSkR_zCan_point (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) (k n : ℕ)
    (L : Fin n → LField (MassGap.SUN.SU N)) (y : Fin n → (Fin 4 → ℝ)) :
    latSkR hN (Renorm.connected hN (zCan hN O t ℓ)) k (pairFam 0 (ptMono L y) (ptMono L y))
      = ((1 / Real.sqrt (refReading hN O t ℓ k)) ^ 2) ^ n
          * latSkR hN (rho1 hN) k (pairFam 0 (ptMono L y) (ptMono L y)) :=
  latSkR_zCan_point_along hN (dyBeta (one_le_of_ne_zero hN)) O t ℓ k n L y


/-- **`PointRatio` gives `PointDiagSep` at the canonical factor.** -/
theorem pointDiagSep_zCan_of_pointRatio_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (h : PointRatioAlong hN βs O t ℓ) : PointDiagSepAlong hN βs (zCanAlong hN βs O t ℓ) := by
  intro n L d hd
  obtain ⟨C, hC⟩ := h n L d hd
  refine ⟨max C 0, ?_⟩
  filter_upwards [hC] with k hk p hp
  have hu := hk p hp
  rw [latSkR_zCan_point_along]
  set r := refReadingAlong hN βs O t ℓ k with hr_def
  set a := dySpacing N k
  set u := latSkRAlong hN βs (rho1Along hN βs) k
    (pairFam 0 (ptMono L (fun i => site a (p i))) (ptMono L (fun i => site a (p i))))
  have ha : 0 ≤ a := (dySpacing_pos (one_le_of_ne_zero hN) k).le
  by_cases hr : 0 < r
  · have hs : (1 / Real.sqrt r) ^ 2 = r⁻¹ := by
      rw [div_pow, one_pow, Real.sq_sqrt hr.le, one_div]
    rw [hs]
    have hrn : 0 < r ^ n := pow_pos hr n
    calc (r⁻¹) ^ n * u ≤ (r⁻¹) ^ n * (C * a ^ (8 * n) * r ^ n) :=
          mul_le_mul_of_nonneg_left hu (pow_nonneg (inv_nonneg.mpr hr.le) n)
      _ = C * a ^ (8 * n) := by
          rw [inv_pow]
          field_simp
      _ ≤ max C 0 * a ^ (8 * n) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg ha _)
  · have hs : Real.sqrt r = 0 := Real.sqrt_eq_zero'.mpr (le_of_not_gt hr)
    rw [hs, div_zero]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [pow_zero, one_mul, mul_zero] at hu ⊢
      rw [mul_one, mul_one] at hu
      simpa using hu.trans (le_max_left C 0)
    · rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_pow hn.ne', zero_mul]
      exact mul_nonneg (le_max_right _ _) (pow_nonneg ha _)

/-- `pointDiagSep_zCan_of_pointRatio` at the couplings `dyBeta`: `pointDiagSep_zCan_of_pointRatio_along` at `βs = dyBeta`.

DERIVED: no numeral beyond those of the statement. -/
theorem pointDiagSep_zCan_of_pointRatio (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (h : PointRatio hN O t ℓ) : PointDiagSep hN (zCan hN O t ℓ) :=
  pointDiagSep_zCan_of_pointRatio_along hN (dyBeta (one_le_of_ne_zero hN)) O t ℓ h


/-- **The converse at an eventually positive reference reading.** -/
theorem pointRatio_of_pointDiagSep (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (hpos : ∀ᶠ k in atTop, 0 < refReading hN O t ℓ k) (h : PointDiagSep hN (zCan hN O t ℓ)) :
    PointRatio hN O t ℓ := by
  intro n L d hd
  obtain ⟨C, hC⟩ := h n L d hd
  refine ⟨C, ?_⟩
  filter_upwards [hC, hpos] with k hk hr p hp
  have hc : latSkR hN (Renorm.connected hN (zCan hN O t ℓ)) k
      (pairFam 0 (ptMono L (fun i => site (dySpacing N k) (p i)))
        (ptMono L (fun i => site (dySpacing N k) (p i)))) ≤ C * dySpacing N k ^ (8 * n) :=
    hk p hp
  rw [latSkR_zCan_point] at hc
  set r := refReading hN O t ℓ k
  set a := dySpacing N k
  set u := latSkR hN (rho1 hN) k
    (pairFam 0 (ptMono L (fun i => site a (p i))) (ptMono L (fun i => site a (p i))))
  have hs : (1 / Real.sqrt r) ^ 2 = r⁻¹ := by
    rw [div_pow, one_pow, Real.sq_sqrt hr.le, one_div]
  rw [hs, inv_pow] at hc
  have hrn : 0 < r ^ n := pow_pos hr n
  have hu : u = r ^ n * ((r ^ n)⁻¹ * u) := by field_simp
  show u ≤ C * a ^ (8 * n) * r ^ n
  rw [hu]
  calc r ^ n * ((r ^ n)⁻¹ * u) ≤ r ^ n * (C * a ^ (8 * n)) :=
        mul_le_mul_of_nonneg_left hc hrn.le
    _ = C * a ^ (8 * n) * r ^ n := by ring

/-- **E from the unit-strength ratio.** `PointRatio` gives `DiagBoundSep` at `zCan`. -/
theorem diagBoundSep_zCan_of_pointRatio_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (h : PointRatioAlong hN βs O t ℓ) :
    ContinuumSep.DiagBoundSepAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) 0 :=
  diagBoundSep_of_pointDiagSep_along hN βs (zCanAlong hN βs O t ℓ) (zCanAlong_refl hN βs O t ℓ)
    (pointDiagSep_zCan_of_pointRatio_along hN βs O t ℓ h)

/-- `diagBoundSep_zCan_of_pointRatio` at the couplings `dyBeta`: `diagBoundSep_zCan_of_pointRatio_along` at `βs = dyBeta`.

DERIVED: no numeral beyond those of the statement. -/
theorem diagBoundSep_zCan_of_pointRatio (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (h : PointRatio hN O t ℓ) :
    ContinuumSep.DiagBoundSep hN (Renorm.connected hN (zCan hN O t ℓ)) 0 :=
  diagBoundSep_zCan_of_pointRatio_along hN (dyBeta (one_le_of_ne_zero hN)) O t ℓ h


end MassGap.PointReadingRatio

#print axioms MassGap.PointReadingRatio.latSkR_zCan_point
#print axioms MassGap.PointReadingRatio.pointDiagSep_zCan_of_pointRatio
#print axioms MassGap.PointReadingRatio.pointRatio_of_pointDiagSep
#print axioms MassGap.PointReadingRatio.diagBoundSep_zCan_of_pointRatio
