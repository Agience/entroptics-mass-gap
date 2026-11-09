import Mathlib
import MassGap.ApertureBridge

/-!
# MassGap.ExistenceReduceOwn — the pinned path with each field read against its own reading

The pinned capstone is `clay_canonical_own`: `ClayRoutes.ClayContinuumPair` at the per-field factor `zOwn`.
`ExistenceReduce.zCan` divides every field by the plane-plaquette reading, so `DiagBoundSep` at `zCan` compares
every field with the plaquette; for a field `∼ p^s`, `s < 1` (`DiagBoundGram.sqrtPlaq`) that ratio grows like
`g₀^{4s−4}` along the asymptotically free tower (argued; Lean necessary condition
`DiagBoundGram.sqrtPlaq_ratio_of_diagBoundSep_planePlaq`). At `zOwn` each field is read against its own
reference reading, and no field is compared with another.

## Definitions

* `ownReadingAlong hN βs t ℓ k O' = max (refReadingAlong O') (refReadingAlong (θO'))`, `θ = LField.refl 0`:
  the reference cube-pair reading of `O'` at unit strength, symmetrised over the time reflection. It is
  reflection invariant (`ownReadingAlong_refl`), and at a reflection-fixed field it is that field's reading
  (`ownReadingAlong_of_refl_eq`).
* `zOwnAlong hN βs t ℓ k O' = 1/√(ownReadingAlong hN βs t ℓ k O')`; `zOwn` at the couplings `dyBeta`. It
  satisfies the reflection compatibility of `Renorm.ReflCompat` (`zOwnAlong_refl`). A field whose two readings
  are both `≤ 0` gets `Z = 0` (`zOwnAlong_eq_zero`).

## What is proved

* `latSkR_pairFam_connectedAlong`: at a reflection-compatible factor `Z`, a reflected pair `θP ∪ P` reads
  `(∏ᵢ Z(Oᵢ))²` times its unit-strength reading.
* `latSkR_zOwn_along`, `pairLowerBound_own_along`: at a reflection-fixed `O` with positive reference reading,
  the reference pair reads exactly `1` at `zOwn`, so `PairLowerBound` holds. `zOwnAlong_eq_zCanAlong`: at
  such an `O`, `zOwn` and `zCan` agree on `O`.
* `clay_canonical_own`: `WDelta2`, `DiagBoundSep` at `zOwn` and eventual positivity of the reference reading
  of a reflection-fixed `O` give `ClayContinuumPair` at `zOwn`, at window `5ℓ₀`.
* `planePlaq_refl`: the plane plaquette is reflection fixed. `clay_canonical_own_planePlaq_low`: `hpos` at the
  plane plaquette reduces to `∃ c > 0, PassageLow.RefPassageLow`, as for `zCan`.
* `pointDiagSep_zOwn_of_own_along`, `diagBoundSep_zOwn_of_own_along`, `diagBoundSep_zOwn_of_own`: the per-field
  remainder `ApertureBridge.ScaleUpOwnAlong ∧ ApertureBridge.PointCubeOwnAlong` at `s₀ > 0` gives `hD` at
  `zOwn hN s₀ s₀`. No positivity of any reading and no `ScaleDown` is used.
* `ownScale_of_diagBoundSep_zOwn_along`: the one-insertion content of `hD` at `zOwn`. At a field with
  eventually positive own reading, `hD` gives `x(O', d) ≤ C · m(O')` with `m(O') = ownReadingAlong … O'`: a
  comparison of the field with itself. The cross-field ratio `x(√p, d) ≤ C · x(p, s₀)` of `DiagBoundGram` is
  not among the one-insertion consequences.
* `scaleUpOwn_of_running`: (R) at every field gives `ScaleUpOwnAlong`.
* `clay_canonical_own_planePlaq`: at `N = 2`, `O = planePlaq 2`, `(t, ℓ) = (s₀, s₀)`: `RefPassageLow` at some
  `c > 0`, `ScaleUpOwnAlong`, `PointCubeOwnAlong` and `ApertureBridge.PhysDefect L (1/1000)` (equivalently
  `WDeltaRun.RunSeed 2`, `ApertureBridge.runSeed_iff_physDefect`) give a witness of `hD` at `zOwn` and the
  pinned `ClayContinuumPair` at window `5 · L/2`.

DERIVED (module-wide): `0` the time axis, the reflection plane and the lower end of a reading; `1` one
insertion and the unit reading; `2` the two copies of a monomial in a reflected pair, the square of `1/√m`
and the halving `s₀/2`; `8` the canonical dimension count of the point readings.

Foundational footprint only (`#print axioms` at the end).
-/

noncomputable section

namespace MassGap.ExistenceReduceOwn

open Filter MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumCluster MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ExistencePoint

variable {N : ℕ}

/-! ## 1. The per-field factor -/

/-- The time reflection is an involution on local fields. -/
theorem lfield_refl_refl (O : LField (MassGap.SUN.SU N)) : (O.refl 0).refl 0 = O :=
  Subtype.ext (ContinuousMap.ext (fun U => by
    show O.1 (LatticeReflection.ireflConf 0 0 (LatticeReflection.ireflConf 0 0 U)) = O.1 U
    rw [LatticeReflection.ireflConf_involutive 0 0 U]))

/-- **A field's own reference reading**, symmetrised over the time reflection:
`max (x(O')) (x(θO'))`, `x = refReadingAlong hN βs · t ℓ k`. -/
def ownReadingAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (t ℓ : ℝ) (k : ℕ) (O' : LField (MassGap.SUN.SU N)) : ℝ :=
  max (refReadingAlong hN βs O' t ℓ k) (refReadingAlong hN βs (O'.refl 0) t ℓ k)

/-- `ownReadingAlong` at the couplings `dyBeta`. -/
def ownReading (hN : N ≠ 0) (t ℓ : ℝ) (k : ℕ) (O' : LField (MassGap.SUN.SU N)) : ℝ :=
  ownReadingAlong hN (dyBeta (one_le_of_ne_zero hN)) t ℓ k O'

/-- **The per-field factor** `1/√(ownReadingAlong)`: each field against its own reading. -/
def zOwnAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (t ℓ : ℝ) : ℕ → LField (MassGap.SUN.SU N) → ℝ :=
  fun k O' => 1 / Real.sqrt (ownReadingAlong hN βs t ℓ k O')

/-- **The per-field factor** at the couplings `dyBeta`. -/
def zOwn (hN : N ≠ 0) (t ℓ : ℝ) : ℕ → LField (MassGap.SUN.SU N) → ℝ :=
  zOwnAlong hN (dyBeta (one_le_of_ne_zero hN)) t ℓ

theorem ownReadingAlong_refl (hN : N ≠ 0) (βs : ℕ → ℝ) (t ℓ : ℝ) (k : ℕ)
    (O' : LField (MassGap.SUN.SU N)) :
    ownReadingAlong hN βs t ℓ k (O'.refl 0) = ownReadingAlong hN βs t ℓ k O' := by
  unfold ownReadingAlong
  rw [lfield_refl_refl, max_comm]

theorem ownReadingAlong_of_refl_eq (hN : N ≠ 0) (βs : ℕ → ℝ) (t ℓ : ℝ) (k : ℕ)
    {O : LField (MassGap.SUN.SU N)} (hO : O.refl 0 = O) :
    ownReadingAlong hN βs t ℓ k O = refReadingAlong hN βs O t ℓ k := by
  unfold ownReadingAlong
  rw [hO, max_self]

/-- **`zOwn` is reflection compatible.** -/
theorem zOwnAlong_refl (hN : N ≠ 0) (βs : ℕ → ℝ) (t ℓ : ℝ) :
    ∀ k O', zOwnAlong hN βs t ℓ k (O'.refl 0) = zOwnAlong hN βs t ℓ k O' := by
  intro k O'
  show 1 / Real.sqrt (ownReadingAlong hN βs t ℓ k (O'.refl 0))
    = 1 / Real.sqrt (ownReadingAlong hN βs t ℓ k O')
  rw [ownReadingAlong_refl]

theorem zOwn_refl (hN : N ≠ 0) (t ℓ : ℝ) :
    ∀ k O', zOwn hN t ℓ k (O'.refl 0) = zOwn hN t ℓ k O' :=
  zOwnAlong_refl hN (dyBeta (one_le_of_ne_zero hN)) t ℓ

/-- **A field with no positive reading gets `Z = 0`.** -/
theorem zOwnAlong_eq_zero (hN : N ≠ 0) (βs : ℕ → ℝ) (t ℓ : ℝ) (k : ℕ) (O' : LField (MassGap.SUN.SU N))
    (h : ownReadingAlong hN βs t ℓ k O' ≤ 0) : zOwnAlong hN βs t ℓ k O' = 0 := by
  show 1 / Real.sqrt (ownReadingAlong hN βs t ℓ k O') = 0
  rw [Real.sqrt_eq_zero'.mpr h, div_zero]

theorem zOwnAlong_sq (hN : N ≠ 0) (βs : ℕ → ℝ) (t ℓ : ℝ) (k : ℕ) (O' : LField (MassGap.SUN.SU N))
    (hm : 0 ≤ ownReadingAlong hN βs t ℓ k O') :
    zOwnAlong hN βs t ℓ k O' ^ 2 = (ownReadingAlong hN βs t ℓ k O')⁻¹ := by
  show (1 / Real.sqrt (ownReadingAlong hN βs t ℓ k O')) ^ 2 = _
  rw [div_pow, one_pow, Real.sq_sqrt hm, one_div]

/-- **At a reflection-fixed field, `zOwn` and `zCan` agree on that field.** -/
theorem zOwnAlong_eq_zCanAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (t ℓ : ℝ) (k : ℕ)
    {O : LField (MassGap.SUN.SU N)} (hO : O.refl 0 = O) :
    zOwnAlong hN βs t ℓ k O = zCanAlong hN βs O t ℓ k O := by
  show 1 / Real.sqrt (ownReadingAlong hN βs t ℓ k O) = 1 / Real.sqrt (refReadingAlong hN βs O t ℓ k)
  rw [ownReadingAlong_of_refl_eq hN βs t ℓ k hO]

/-! ## 2. Readings at a field-dependent factor -/

/-- At connected renormalisation data with factor `Z`, a reading is the product of the factors times the
unit-strength reading. -/
theorem latSkR_connectedAlong_eq (hN : N ≠ 0) (βs : ℕ → ℝ) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (k : ℕ) {ι : Type} [Fintype ι] (F : ι → SField N) :
    latSkRAlong hN βs (Renorm.connectedAlong hN βs Z) k F
      = (∏ i, Z k (F i).1) * latSkRAlong hN βs (rho1Along hN βs) k F := by
  unfold latSkRAlong Renorm.pref
  have h1 : (∏ i, (rho1Along hN βs).Z k (F i).1) = 1 := Finset.prod_eq_one (fun _ _ => rfl)
  rw [h1, one_mul]
  rfl

/-- A reflected pair `θP ∪ P` at a reflection-compatible factor `Z` reads `(∏ᵢ Z(Oᵢ))²` times its
unit-strength reading. -/
theorem latSkR_pairFam_connectedAlong (hN : N ≠ 0) (βs : ℕ → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, Z k (O.refl 0) = Z k O) (k : ℕ)
    (P : Mono N) :
    latSkRAlong hN βs (Renorm.connectedAlong hN βs Z) k (pairFam 0 P P)
      = (∏ i, Z k (P.2 i).1) ^ 2 * latSkRAlong hN βs (rho1Along hN βs) k (pairFam 0 P P) := by
  rw [latSkR_connectedAlong_eq, Fintype.prod_sum_type]
  have h1 : ∀ i, Z k (pairFam 0 P P (Sum.inl i)).1 = Z k (P.2 i).1 := fun i => hZ k (P.2 i).1
  have h2 : ∀ i, Z k (pairFam 0 P P (Sum.inr i)).1 = Z k (P.2 i).1 := fun _ => rfl
  simp only [h1, h2]
  ring

/-! ## 3. The pair lower bound at a reflection-fixed reference -/

/-- **The reference pair reads exactly `1` at `zOwn`**, at a reflection-fixed field with positive reading. -/
theorem latSkR_zOwn_along (hN : N ≠ 0) (βs : ℕ → ℝ) {O : LField (MassGap.SUN.SU N)} (t ℓ : ℝ) (k : ℕ)
    (hO : O.refl 0 = O) (hpos : 0 < refReadingAlong hN βs O t ℓ k) :
    latSkRAlong hN βs (Renorm.connectedAlong hN βs (zOwnAlong hN βs t ℓ)) k
      (pairFam 0 (refMono O t ℓ) (refMono O t ℓ)) = 1 := by
  rw [latSkR_pairFam_connectedAlong hN βs _ (zOwnAlong_refl hN βs t ℓ)]
  show (∏ _i : Fin 1, zOwnAlong hN βs t ℓ k O) ^ 2 * refReadingAlong hN βs O t ℓ k = 1
  have hm : 0 ≤ ownReadingAlong hN βs t ℓ k O := by
    rw [ownReadingAlong_of_refl_eq hN βs t ℓ k hO]
    exact hpos.le
  rw [Fin.prod_univ_one, zOwnAlong_sq hN βs t ℓ k O hm, ownReadingAlong_of_refl_eq hN βs t ℓ k hO,
    inv_mul_cancel₀ hpos.ne']

/-- **`PairLowerBoundAlong` at `zOwn`** from a reflection-fixed field with eventually positive reading. -/
theorem pairLowerBound_own_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) {t ℓ : ℝ}
    (ht : 0 < t) (hO : O.refl 0 = O) (hpos : ∀ᶠ k in atTop, 0 < refReadingAlong hN βs O t ℓ k) :
    ClayReduce.PairLowerBoundAlong hN βs (zOwnAlong hN βs t ℓ) 0 :=
  ⟨O, t, ℓ, 1, ht, one_pos, hpos.mono fun k hk => (latSkR_zOwn_along hN βs t ℓ k hO hk).ge⟩

theorem pairLowerBound_own (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {t ℓ : ℝ} (ht : 0 < t)
    (hO : O.refl 0 = O) (hpos : ∀ᶠ k in atTop, 0 < refReading hN O t ℓ k) :
    ClayReduce.PairLowerBound hN (zOwn hN t ℓ) 0 :=
  pairLowerBound_own_along hN (dyBeta (one_le_of_ne_zero hN)) O ht hO hpos

/-! ## 4. The pinned path at the per-field factor -/

/-- **The pinned path at the per-field normalisation.** `WDelta2`, `DiagBoundSep` at `zOwn` and eventual
positivity of the reference reading of a reflection-fixed field `O` give `ClayContinuumPair` at `zOwn`. -/
theorem clay_canonical_own (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {t ℓ : ℝ}
    (ht : 0 < t) (hO : O.refl 0 = O) (hpos : ∀ᶠ k in atTop, 0 < refReading hN O t ℓ k)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (zOwn hN t ℓ)) 0) {ℓ₀ : ℝ}
    (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (zOwn hN t ℓ) 0 (zOwn_refl hN t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN (Renorm.connected hN (zOwn hN t ℓ)) 0
        (Renorm.connected_reflCompat hN (zOwn hN t ℓ) 0 (zOwn_refl hN t ℓ)) hD) (5 * ℓ₀) :=
  clay_of_WDelta2_diag hN2 hN (zOwn hN t ℓ) (zOwn_refl hN t ℓ) hD hℓ hW
    (pairLowerBound_own hN O ht hO hpos)

/-- **The plane plaquette is fixed by the time reflection** (`ExistencePosNonnull.ireflPlaq_q₀`). -/
theorem planePlaq_refl : (ExistencePosNonnull.planePlaq N).refl 0 = ExistencePosNonnull.planePlaq N :=
  Subtype.ext (by
    show LatticeReflection.ireflObs 0 0 (GaugeInvariantAlgebra.iplaqObs (N := N) ExistencePosNonnull.q₀)
      = GaugeInvariantAlgebra.iplaqObs (N := N) ExistencePosNonnull.q₀
    rw [GaugeInvariantAlgebra.ireflObs_iplaqObs, ExistencePosNonnull.ireflPlaq_q₀])

/-- **The pinned path at the plane plaquette with `hpos` reduced to the lower side of the passage**, at the
per-field factor. -/
theorem clay_canonical_own_planePlaq_low (hN2 : 2 ≤ N) (hN : N ≠ 0) {t ℓ : ℝ} (ht : 0 < t)
    (hℓ : 0 < ℓ) {M₀ : ℕ} (hM : 2 * (t + ℓ) < M₀ * AsymptoticScaling.aRun N 1)
    (hL : ∃ c : ℝ, 0 < c ∧ PassageLow.RefPassageLow hN M₀ (ExistencePosNonnull.planePlaq N) t ℓ c)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (zOwn hN t ℓ)) 0)
    {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (zOwn hN t ℓ) 0 (zOwn_refl hN t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN (Renorm.connected hN (zOwn hN t ℓ)) 0
        (Renorm.connected_reflCompat hN (zOwn hN t ℓ) 0 (zOwn_refl hN t ℓ)) hD) (5 * ℓ₀) := by
  obtain ⟨c, hc, hLc⟩ := hL
  exact clay_canonical_own hN2 hN _ ht planePlaq_refl
    (PassageLow.hpos_of_refPassageLow hN
      (TorusRefPosPlane.torusRefPos_of_sliceForm hN
        (SliceFormPlane.sliceForm_planePlaq hN2 hN ht hℓ hM)) hc hLc) hD hℓ₀ hW

/-! ## 5. `hD` at `zOwn` from the per-field remainder -/

/-- The arithmetic of the per-field bound: `∏ mᵢ⁻¹ · u ≤ c · ∏ max Mᵢ 0 · A` from
`u ≤ c A ∏ xᵢ`, `0 ≤ xᵢ ≤ Mᵢ rᵢ`, `0 ≤ rᵢ ≤ mᵢ`. -/
theorem prod_inv_mul_le {n : ℕ} (m x r M : Fin n → ℝ) (c A u : ℝ) (hc : 0 ≤ c) (hA : 0 ≤ A)
    (hr : ∀ i, 0 ≤ r i) (hrm : ∀ i, r i ≤ m i) (hx : ∀ i, 0 ≤ x i) (hxr : ∀ i, x i ≤ M i * r i)
    (hu : u ≤ c * A * ∏ i, x i) :
    (∏ i, (m i)⁻¹) * u ≤ (c * ∏ i, max (M i) 0) * A := by
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hr i).trans (hrm i)
  have hfac : ∀ i, (m i)⁻¹ * x i ≤ max (M i) 0 := by
    intro i
    have hxm : x i ≤ max (M i) 0 * m i :=
      calc x i ≤ M i * r i := hxr i
        _ ≤ max (M i) 0 * r i := mul_le_mul_of_nonneg_right (le_max_left _ _) (hr i)
        _ ≤ max (M i) 0 * m i := mul_le_mul_of_nonneg_left (hrm i) (le_max_right _ _)
    rcases (hm0 i).eq_or_lt with h0 | hpos
    · rw [← h0, inv_zero, zero_mul]
      exact le_max_right _ _
    · rw [inv_mul_le_iff₀ hpos, mul_comm]
      exact hxm
  calc (∏ i, (m i)⁻¹) * u ≤ (∏ i, (m i)⁻¹) * (c * A * ∏ i, x i) :=
        mul_le_mul_of_nonneg_left hu (Finset.prod_nonneg fun i _ => inv_nonneg.mpr (hm0 i))
    _ = c * A * ∏ i, ((m i)⁻¹ * x i) := by rw [Finset.prod_mul_distrib]; ring
    _ ≤ c * A * ∏ i, max (M i) 0 :=
        mul_le_mul_of_nonneg_left
          (Finset.prod_le_prod (fun i _ => mul_nonneg (inv_nonneg.mpr (hm0 i)) (hx i))
            (fun i _ => hfac i)) (mul_nonneg hc hA)
    _ = (c * ∏ i, max (M i) 0) * A := by ring

/-- **The per-field remainder gives bounded point readings at `zOwn`.** -/
theorem pointDiagSep_zOwn_of_own_along (hN : N ≠ 0) (βs : ℕ → ℝ) {s₀ : ℝ} (hs₀ : 0 < s₀)
    (hU : ApertureBridge.ScaleUpOwnAlong hN βs s₀) (hL : ApertureBridge.PointCubeOwnAlong hN βs s₀) :
    PointDiagSepAlong hN βs (zOwnAlong hN βs s₀ s₀) := by
  intro n L d hd
  set d' := min d (s₀ / 2) with hd'_def
  have hd' : 0 < d' := lt_min hd (by positivity)
  have hd's : d' < s₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨C, hC⟩ := hL n L d' hd' hd's
  choose M hM using fun i => hU (L i) d' hd' hd's
  refine ⟨max C 0 * ∏ i, max (M i) 0, ?_⟩
  have hMev : ∀ᶠ k in atTop, ∀ i,
      refReadingAlong hN βs (L i) d' d' k ≤ M i * refReadingAlong hN βs (L i) s₀ s₀ k :=
    Filter.eventually_all.mpr hM
  have hx0 : ∀ᶠ k in atTop, ∀ i, 0 ≤ refReadingAlong hN βs (L i) d' d' k :=
    Filter.eventually_all.mpr
      (fun i => FieldDomination.refReadingAlong_eventually_nonneg hN βs (L i) hd')
  have hr0 : ∀ᶠ k in atTop, ∀ i, 0 ≤ refReadingAlong hN βs (L i) s₀ s₀ k :=
    Filter.eventually_all.mpr
      (fun i => FieldDomination.refReadingAlong_eventually_nonneg hN βs (L i) hs₀)
  filter_upwards [hC, hMev, hx0, hr0] with k hk hm hx hr p hp
  have hu := hk p (ContinuumSep.sepPos_mono hp (min_le_left d (s₀ / 2)))
  have ha : 0 ≤ dySpacing N k ^ (8 * n) :=
    pow_nonneg (dySpacing_pos (one_le_of_ne_zero hN) k).le _
  have hu' := hu.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left C 0) ha) (Finset.prod_nonneg fun i _ => hx i))
  have hz : (∏ i : Fin n, zOwnAlong hN βs s₀ s₀ k (L i)) ^ 2
      = ∏ i : Fin n, (ownReadingAlong hN βs s₀ s₀ k (L i))⁻¹ := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun i _ =>
      zOwnAlong_sq hN βs s₀ s₀ k (L i) ((hr i).trans (le_max_left _ _)))
  rw [latSkR_pairFam_connectedAlong hN βs _ (zOwnAlong_refl hN βs s₀ s₀)]
  show (∏ i : Fin n, zOwnAlong hN βs s₀ s₀ k (L i)) ^ 2 * _ ≤ _
  rw [hz]
  exact prod_inv_mul_le (fun i => ownReadingAlong hN βs s₀ s₀ k (L i))
    (fun i => refReadingAlong hN βs (L i) d' d' k) (fun i => refReadingAlong hN βs (L i) s₀ s₀ k) M
    (max C 0) (dySpacing N k ^ (8 * n)) _ (le_max_right _ _) ha hr (fun _ => le_max_left _ _) hx hm hu'

/-- **`hD` at `zOwn` from the per-field remainder**, along `βs`. -/
theorem diagBoundSep_zOwn_of_own_along (hN : N ≠ 0) (βs : ℕ → ℝ) {s₀ : ℝ} (hs₀ : 0 < s₀)
    (hU : ApertureBridge.ScaleUpOwnAlong hN βs s₀) (hL : ApertureBridge.PointCubeOwnAlong hN βs s₀) :
    ContinuumSep.DiagBoundSepAlong hN βs (Renorm.connectedAlong hN βs (zOwnAlong hN βs s₀ s₀)) 0 :=
  diagBoundSep_of_pointDiagSep_along hN βs _ (zOwnAlong_refl hN βs s₀ s₀)
    (pointDiagSep_zOwn_of_own_along hN βs hs₀ hU hL)

/-- **`hD` at `zOwn` from the per-field remainder** at the couplings `dyBeta`. -/
theorem diagBoundSep_zOwn_of_own (hN : N ≠ 0) {s₀ : ℝ} (hs₀ : 0 < s₀)
    (hU : ApertureBridge.ScaleUpOwnAlong hN (dyBeta (one_le_of_ne_zero hN)) s₀)
    (hL : ApertureBridge.PointCubeOwnAlong hN (dyBeta (one_le_of_ne_zero hN)) s₀) :
    ContinuumSep.DiagBoundSep hN (Renorm.connected hN (zOwn hN s₀ s₀)) 0 :=
  diagBoundSep_zOwn_of_own_along hN (dyBeta (one_le_of_ne_zero hN)) hs₀ hU hL

/-- **The one-insertion content of `hD` at `zOwn` is a comparison of each field with itself.** At a field
with eventually positive own reading, `hD` gives `x(O', d) ≤ C · m(O')` at every `d > 0`. -/
theorem ownScale_of_diagBoundSep_zOwn_along (hN : N ≠ 0) (βs : ℕ → ℝ) {s₀ : ℝ}
    (O' : LField (MassGap.SUN.SU N)) (hpos : ∀ᶠ k in atTop, 0 < ownReadingAlong hN βs s₀ s₀ k O')
    (hE : ContinuumSep.DiagBoundSepAlong hN βs
      (Renorm.connectedAlong hN βs (zOwnAlong hN βs s₀ s₀)) 0) :
    ∀ d : ℝ, 0 < d → ∃ C : ℝ, ∀ᶠ k in atTop,
      refReadingAlong hN βs O' d d k ≤ C * ownReadingAlong hN βs s₀ s₀ k O' := by
  intro d hd
  obtain ⟨C, hC⟩ := hE (ContinuumNontrivial.sepCube 0 O' hd d)
  refine ⟨C, ?_⟩
  filter_upwards [hC, hpos] with k hk hm
  have hk' : latSkRAlong hN βs (Renorm.connectedAlong hN βs (zOwnAlong hN βs s₀ s₀)) k
      (pairFam 0 (refMono O' d d) (refMono O' d d)) ≤ C := hk
  rw [latSkR_pairFam_connectedAlong hN βs _ (zOwnAlong_refl hN βs s₀ s₀)] at hk'
  have h1 : (∏ _i : Fin 1, zOwnAlong hN βs s₀ s₀ k O') ^ 2 * refReadingAlong hN βs O' d d k ≤ C := hk'
  rw [Fin.prod_univ_one, zOwnAlong_sq hN βs s₀ s₀ k O' hm.le, inv_mul_le_iff₀ hm] at h1
  rw [mul_comm]
  exact h1

/-- **(R) at every field gives the per-field scale clause.** The implication is valid, but its hypothesis
cannot hold for every field: (R) fails for a field whose leading dimension is not `4` (e.g. a lattice
derivative of the plaquette), whose log readings run like `|2Δ − 8| · |log s|`. The capstone does not use it. -/
theorem scaleUpOwn_of_running (hN : N ≠ 0) (βs : ℕ → ℝ) {s₀ : ℝ} (hs₀1 : s₀ < 1)
    (hR : ∀ O : LField (MassGap.SUN.SU N), ∃ K δ : ℝ, ShortDistanceRunning.RunningBelowAlong hN βs O s₀ K δ) :
    ApertureBridge.ScaleUpOwnAlong hN βs s₀ := fun O => by
  obtain ⟨K, δ, h⟩ := hR O
  exact DiagBoundRunning.scaleUp_of_running_along hN βs O hs₀1 h

/-! ## 6. The capstone at the plane plaquette -/

/-- **The pinned path at the per-field normalisation from the typed remainders.** At `N = 2`,
`O = planePlaq 2`, `(t, ℓ) = (s₀, s₀)`, `0 < s₀`, `4 s₀ < M₀ · aRun 2 1`, `0 < L`: `RefPassageLow` at some
`c > 0` (`hpos`), `ScaleUpOwnAlong ∧ PointCubeOwnAlong` (`hD`) and `PhysDefect L (1/1000)` (`hW`) give a
witness of `hD` at `zOwn` and `ClayContinuumPair` at `zOwn`, at window `5 · L/2`. -/
theorem clay_canonical_own_planePlaq (hN : (2 : ℕ) ≠ 0) {M₀ : ℕ} {s₀ L : ℝ} (hs₀ : 0 < s₀)
    (hM : 2 * (s₀ + s₀) < M₀ * AsymptoticScaling.aRun 2 1) (hL : 0 < L)
    (hP : ∃ c : ℝ, 0 < c ∧ PassageLow.RefPassageLow hN M₀ (ExistencePosNonnull.planePlaq 2) s₀ s₀ c)
    (hU : ApertureBridge.ScaleUpOwnAlong hN (dyBeta (one_le_of_ne_zero hN)) s₀)
    (hC : ApertureBridge.PointCubeOwnAlong hN (dyBeta (one_le_of_ne_zero hN)) s₀)
    (hW : ApertureBridge.PhysDefect L (1 / 1000)) :
    ∃ hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (zOwn hN s₀ s₀)) 0,
      ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧
        ClayRoutes.ClayContinuumPair hN (zOwn hN s₀ s₀) 0 (zOwn_refl hN s₀ s₀)
          (ContinuumSep.pairBoundSep_of_diagBoundSep hN (Renorm.connected hN (zOwn hN s₀ s₀)) 0
            (Renorm.connected_reflCompat hN (zOwn hN s₀ s₀) 0 (zOwn_refl hN s₀ s₀)) hD) (5 * ℓ₀) := by
  have hD := diagBoundSep_zOwn_of_own hN hs₀ hU hC
  exact ⟨hD, L / 2, by positivity, clay_canonical_own_planePlaq_low le_rfl hN hs₀ hs₀ hM hP hD
    (by positivity) (ApertureBridge.wDelta2_two_of_physDefect hL hW (L / 2) (by linarith))⟩

end MassGap.ExistenceReduceOwn

end

#print axioms MassGap.ExistenceReduceOwn.lfield_refl_refl
#print axioms MassGap.ExistenceReduceOwn.ownReadingAlong_refl
#print axioms MassGap.ExistenceReduceOwn.ownReadingAlong_of_refl_eq
#print axioms MassGap.ExistenceReduceOwn.zOwnAlong_refl
#print axioms MassGap.ExistenceReduceOwn.zOwn_refl
#print axioms MassGap.ExistenceReduceOwn.zOwnAlong_eq_zero
#print axioms MassGap.ExistenceReduceOwn.zOwnAlong_sq
#print axioms MassGap.ExistenceReduceOwn.zOwnAlong_eq_zCanAlong
#print axioms MassGap.ExistenceReduceOwn.latSkR_connectedAlong_eq
#print axioms MassGap.ExistenceReduceOwn.latSkR_pairFam_connectedAlong
#print axioms MassGap.ExistenceReduceOwn.latSkR_zOwn_along
#print axioms MassGap.ExistenceReduceOwn.pairLowerBound_own_along
#print axioms MassGap.ExistenceReduceOwn.pairLowerBound_own
#print axioms MassGap.ExistenceReduceOwn.clay_canonical_own
#print axioms MassGap.ExistenceReduceOwn.planePlaq_refl
#print axioms MassGap.ExistenceReduceOwn.clay_canonical_own_planePlaq_low
#print axioms MassGap.ExistenceReduceOwn.prod_inv_mul_le
#print axioms MassGap.ExistenceReduceOwn.pointDiagSep_zOwn_of_own_along
#print axioms MassGap.ExistenceReduceOwn.diagBoundSep_zOwn_of_own_along
#print axioms MassGap.ExistenceReduceOwn.diagBoundSep_zOwn_of_own
#print axioms MassGap.ExistenceReduceOwn.ownScale_of_diagBoundSep_zOwn_along
#print axioms MassGap.ExistenceReduceOwn.scaleUpOwn_of_running
#print axioms MassGap.ExistenceReduceOwn.clay_canonical_own_planePlaq
