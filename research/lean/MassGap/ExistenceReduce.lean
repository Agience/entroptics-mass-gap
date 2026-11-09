import Mathlib
import MassGap.DoublingClay2
import MassGap.ClayReduce

noncomputable section

/-!
# MassGap.ExistenceReduce — the existence side of the pinned path at the strength the chain reads

`DoublingClay2.clay_of_WDelta2` takes E as `ContinuumSep.UniformBoundSep` and N, Y as
`ContinuumNontrivial.KernelConvergesSep` and `ShortDistanceY.AFShortDistance`. The chain reads E only as
`ContinuumSep.DiagBoundSep` and N with Y only as `ClayReduce.PairLowerBound`, and it forms its continuum
limits along an ultrafilter (`ContinuumSep`), so it needs bounds, not convergence.

* `clay_of_WDelta2_diag`: `WDelta2`, `DiagBoundSep` and `PairLowerBound` give
  `ClayRoutes.ClayContinuumPair` at window `5ℓ₀`. `ClayRoutes.clayContinuum_iff_pair` identifies it with
  `ClayContinuum` at any `UniformBoundSep` witness.
* Canonical normalisation. `refReading hN O t ℓ k` is the reflected cube-pair reading at unit field strength,
  and `zCan` the field-independent factor `1/√(refReading)`. With it the reference reading is exactly `1`
  (`latSkR_zCan`), so `PairLowerBound` holds as soon as the reference reading is positive
  (`pairLowerBound_canonical`). `PairLowerBound` therefore carries no information beyond that positivity: a
  Gaussian (trivial) limit satisfies it too. Non-triviality in the Clay sense has to come from Y.
* `clay_canonical`: `WDelta2`, `DiagBoundSep` at `zCan` and eventual positivity of the reference reading give
  `ClayContinuumPair` at `zCan`.
-/

namespace MassGap.ExistenceReduce

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger Filter

variable {N : ℕ}

/-- **The pinned path with E and N at the strength the chain reads.** -/
theorem clay_of_WDelta2_diag (hN2 : 2 ≤ N) (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) 0) {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀)
    (hW : DoublingClay2.WDelta2 N ℓ₀) (hP : ClayReduce.PairLowerBound hN Z 0) :
    ClayRoutes.ClayContinuumPair hN Z 0 hZ
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN (Renorm.connected hN Z) 0
        (Renorm.connected_reflCompat hN Z 0 hZ) hD) (5 * ℓ₀) :=
  ClayReduce.clay_continuum_of_diagBoundSep hN2 hN Z 0 hZ hD (by positivity)
    (DoublingClay2.fixedWindowDecay_of_WDelta2 hN hℓ hW) hP

/-- **The gap seed gives the tower gap along `dyBeta`**: `DoublingClay2.fixedWindowDecay_of_WDelta2` at
window `5ℓ₀` and `ContinuumCluster.towerGapAt_dyBeta_of_fixedWindowDecay`. -/
theorem towerGapAt_dyBeta_of_WDelta2 (hN2 : 2 ≤ N) (hN : N ≠ 0) {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀)
    (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ∃ M : ℝ, 0 < M ∧ ContinuumCluster.TowerGapAt hN 0 (dyBeta (one_le_of_ne_zero hN)) M := by
  obtain ⟨c, hc, hG⟩ := ContinuumCluster.towerGapAt_dyBeta_of_fixedWindowDecay hN2 hN 0
    (by positivity : (0 : ℝ) < 5 * ℓ₀) (DoublingClay2.fixedWindowDecay_of_WDelta2 hN hℓ hW)
  exact ⟨_, div_pos hc (by positivity), hG⟩

/-- The reference cube monomial. -/
def refMono (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) : Mono N :=
  ContinuumNontrivial.mono1 (O, ContinuumNontrivial.cubeTest t ℓ)

/-- The reflected reference cube-pair reading at unit field strength along the coupling tower `βs`. -/
def refReadingAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) (k : ℕ) :
    ℝ :=
  latSkRAlong hN βs (Renorm.connectedAlong hN βs (fun _ _ => 1)) k
    (pairFam 0 (refMono O t ℓ) (refMono O t ℓ))

/-- The reflected reference cube-pair reading at unit field strength: `refReadingAlong` at the
couplings `dyBeta`. -/
def refReading (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) (k : ℕ) : ℝ :=
  refReadingAlong hN (dyBeta (one_le_of_ne_zero hN)) O t ℓ k

/-- The canonical field-strength factor along `βs`, `1/√(refReadingAlong)`, the same for every
field. -/
def zCanAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) :
    ℕ → LField (MassGap.SUN.SU N) → ℝ :=
  fun k _ => 1 / Real.sqrt (refReadingAlong hN βs O t ℓ k)

/-- The canonical field-strength factor `1/√(refReading)`, the same for every field: `zCanAlong` at the
couplings `dyBeta`. -/
def zCan (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) :
    ℕ → LField (MassGap.SUN.SU N) → ℝ :=
  zCanAlong hN (dyBeta (one_le_of_ne_zero hN)) O t ℓ

theorem zCanAlong_refl (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) :
    ∀ k O', zCanAlong hN βs O t ℓ k (O'.refl 0) = zCanAlong hN βs O t ℓ k O' := fun _ _ => rfl

theorem zCan_refl (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) :
    ∀ k O', zCan hN O t ℓ k (O'.refl 0) = zCan hN O t ℓ k O' := fun _ _ => rfl

/-- **The reference reading along `βs` is exactly `1` at the canonical factor.** -/
theorem latSkR_zCan_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (k : ℕ) (hpos : 0 < refReadingAlong hN βs O t ℓ k) :
    latSkRAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) k
      (pairFam 0 (refMono O t ℓ) (refMono O t ℓ)) = 1 := by
  have h1 : ∀ k' (O' : LField (MassGap.SUN.SU N)),
      (Renorm.connectedAlong hN βs (fun _ _ => (1 : ℝ))).Z k' O' = 1 := fun _ _ => rfl
  have hz : ∀ k' (O' : LField (MassGap.SUN.SU N)),
      (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)).Z k' O'
        = 1 / Real.sqrt (refReadingAlong hN βs O t ℓ k') :=
    fun _ _ => rfl
  have hlat : refReadingAlong hN βs O t ℓ k
      = latSkAlong hN βs k (fun i => (Renorm.connectedAlong hN βs (fun _ _ => (1 : ℝ))).field k
          (pairFam 0 (refMono O t ℓ) (refMono O t ℓ) i)) := by
    unfold refReadingAlong latSkRAlong Renorm.pref
    simp only [h1, Finset.prod_const_one, one_mul]
  have hf : latSkAlong hN βs k (fun i => (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)).field k
      (pairFam 0 (refMono O t ℓ) (refMono O t ℓ) i)) = refReadingAlong hN βs O t ℓ k := by
    rw [hlat]; rfl
  have hcan : latSkRAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) k
        (pairFam 0 (refMono O t ℓ) (refMono O t ℓ))
      = (1 / Real.sqrt (refReadingAlong hN βs O t ℓ k)) ^ 2 * refReadingAlong hN βs O t ℓ k := by
    unfold latSkRAlong Renorm.pref
    rw [hf]
    simp only [hz]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin]
    rfl
  rw [hcan, div_pow, one_pow, Real.sq_sqrt hpos.le, one_div, inv_mul_cancel₀ hpos.ne']

/-- **The reference reading is exactly `1` at the canonical factor.** -/
theorem latSkR_zCan (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) (k : ℕ)
    (hpos : 0 < refReading hN O t ℓ k) :
    latSkR hN (Renorm.connected hN (zCan hN O t ℓ)) k
      (pairFam 0 (refMono O t ℓ) (refMono O t ℓ)) = 1 :=
  latSkR_zCan_along hN (dyBeta (one_le_of_ne_zero hN)) O t ℓ k hpos

/-- **`PairLowerBoundAlong` from the positivity of the reference reading along `βs` alone.** -/
theorem pairLowerBound_canonical_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N))
    {t ℓ : ℝ} (ht : 0 < t) (hpos : ∀ᶠ k in atTop, 0 < refReadingAlong hN βs O t ℓ k) :
    ClayReduce.PairLowerBoundAlong hN βs (zCanAlong hN βs O t ℓ) 0 :=
  ⟨O, t, ℓ, 1, ht, one_pos, hpos.mono fun k hk => (latSkR_zCan_along hN βs O t ℓ k hk).ge⟩

/-- **`PairLowerBound` from the positivity of the reference reading alone.** -/
theorem pairLowerBound_canonical (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {t ℓ : ℝ} (ht : 0 < t)
    (hpos : ∀ᶠ k in atTop, 0 < refReading hN O t ℓ k) :
    ClayReduce.PairLowerBound hN (zCan hN O t ℓ) 0 :=
  pairLowerBound_canonical_along hN (dyBeta (one_le_of_ne_zero hN)) O ht hpos

/-- **The pinned path at the canonical normalisation, along a coupling tower.** The tower gap
`ContinuumCluster.TowerGapAt hN 0 βs M` at `M > 0`, `DiagBoundSepAlong` at `zCanAlong` and eventual
positivity of the reference reading give `ClayContinuumPairAlong` at `zCanAlong`, at every window
`L > 0`. -/
theorem clay_canonical_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) {t ℓ : ℝ}
    (ht : 0 < t) (hpos : ∀ᶠ k in atTop, 0 < refReadingAlong hN βs O t ℓ k)
    (hD : ContinuumSep.DiagBoundSepAlong hN βs
      (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) 0)
    {M : ℝ} (hM : 0 < M) (hG : ContinuumCluster.TowerGapAt hN 0 βs M) {L : ℝ} (hL : 0 < L) :
    ClayRoutes.ClayContinuumPairAlong hN βs (zCanAlong hN βs O t ℓ) 0 (zCanAlong_refl hN βs O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep_along hN βs
        (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) 0
        (Renorm.connectedAlong_reflCompat hN βs (zCanAlong hN βs O t ℓ) 0
          (zCanAlong_refl hN βs O t ℓ)) hD) L :=
  ClayReduce.clay_continuum_of_diagBoundSep_towerGapAt hN βs (zCanAlong hN βs O t ℓ) 0
    (zCanAlong_refl hN βs O t ℓ) hD hM hG hL (pairLowerBound_canonical_along hN βs O ht hpos)

/-- **The pinned path at the canonical normalisation.** -/
theorem clay_canonical (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {t ℓ : ℝ}
    (ht : 0 < t) (hpos : ∀ᶠ k in atTop, 0 < refReading hN O t ℓ k)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (zCan hN O t ℓ)) 0) {ℓ₀ : ℝ}
    (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (zCan hN O t ℓ) 0 (zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN (Renorm.connected hN (zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (zCan hN O t ℓ) 0 (zCan_refl hN O t ℓ)) hD) (5 * ℓ₀) :=
  clay_of_WDelta2_diag hN2 hN (zCan hN O t ℓ) (zCan_refl hN O t ℓ) hD hℓ hW
    (pairLowerBound_canonical hN O ht hpos)

end MassGap.ExistenceReduce

#print axioms MassGap.ExistenceReduce.clay_of_WDelta2_diag
#print axioms MassGap.ExistenceReduce.latSkR_zCan
#print axioms MassGap.ExistenceReduce.pairLowerBound_canonical
#print axioms MassGap.ExistenceReduce.clay_canonical
#print axioms MassGap.ExistenceReduce.latSkR_zCan_along
#print axioms MassGap.ExistenceReduce.pairLowerBound_canonical_along
#print axioms MassGap.ExistenceReduce.clay_canonical_along
#print axioms MassGap.ExistenceReduce.towerGapAt_dyBeta_of_WDelta2
