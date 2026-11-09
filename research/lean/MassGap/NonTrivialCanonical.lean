import Mathlib
import MassGap.ExistenceReduce

noncomputable section

/-!
# MassGap.NonTrivialCanonical — a separated three-point function of the pinned theory

`ExistenceReduce.clay_canonical` reads the theory through one field-independent factor
`zCan = 1/√(refReading)`, which makes the reflected reference cube pair read exactly `1`. Its conclusion
`ClayRoutes.ClayContinuumPair` is met by a Gaussian limit. This module states the connected three-point
lower bound on the pinned objects themselves (the cube-smeared fields at the dyadic steps `k`, under
`zCan`) and wires it into the capstone.

## The statement

`ThreePointCanonical hN O t ℓ F`, for a family `F` of three smeared fields: eventually in the step, the
canonically normalised three-point reading `latSkR (connected zCan) k F` is at least one `c > 0` in
absolute value.

* `latSkR_zCan_eq`: on any family of `n` fields, the canonical reading is `refReading_k^{−n/2}` times the
  unit-strength connected reading. The field factor is one number for every field, so the statement is
  renormalisation-free: `threePointCanonical_iff` writes it as `c · refReading_k³ ≤ (κ₃)_k²`, `κ₃` the
  unit-strength reading.
* Each connected smeared field has mean zero under `stateK hN k`
  (`ContinuumNontrivial.stateK_smear_connected`).

## What it gives

* `refPos_of_threePointCanonical`: the statement forces the reference reading to be eventually positive,
  which is the `hpos` of `clay_canonical` (at a non-positive reference reading `zCan` is `0` and every
  reading with an insertion is `0`).
* `le_abs_contS_of_threePointCanonical`: with the three-point reading eventually bounded (E on that
  family), the continuum three-point Schwinger function of the canonically normalised connected fields
  is non-zero. A Gaussian limit has every connected function of order three equal to `0`.
* `clay_canonical_threePoint`: `WDelta2`, `DiagBoundSep` at `zCan` and `ThreePointCanonical` give
  `ClayContinuumPair` at window `5ℓ₀` with no separate `hpos`, and, under the bound, a non-zero
  connected three-point continuum function.
* `CanonicalThreePoint hN O t ℓ` (three insertions of the reference field at pairwise separated supports,
  `SepThree`, satisfying `ThreePointCanonical`) is the named open statement; `ThreePointBound` is E on
  separated three-insertion families; `clay_canonical_nonGaussian` is the capstone from `WDelta2`,
  `DiagBoundSep`, `ThreePointBound` and `CanonicalThreePoint`.

## Controls

* The statement does not exclude a free massive field: the Wick square of a free massive field has a
  non-zero separated three-point function, and so does `F²` of a free massive vector. Excluding those
  needs the short-distance requirement Y (`ShortDistanceY.not_af_of_scalingForm`).
-/

namespace MassGap.NonTrivialCanonical

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.ExistenceReduce Filter
open scoped Topology

variable {N : ℕ}

/-- The connected renormalisation at unit field strength, the one `refReading` reads. -/
abbrev rho1 (hN : N ≠ 0) : Renorm N := Renorm.connected hN (fun _ _ => 1)

/-! ## Along a coupling tower

The statements of this module at any coupling sequence `βs`, at the dyadic spacing; at `βs = dyBeta`
they are the statements below. -/

/-- The connected renormalisation along `βs` at unit field strength, the one `refReadingAlong` reads. -/
abbrev rho1Along (hN : N ≠ 0) (βs : ℕ → ℝ) : Renorm N := Renorm.connectedAlong hN βs (fun _ _ => 1)

/-- **The canonical reading along `βs` of any family is a power of the reference reading times the
unit-strength reading.** -/
theorem latSkR_zCan_eq_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (k : ℕ) {ι : Type} [Fintype ι] (F : ι → SField N) :
    latSkRAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) k F
      = (1 / Real.sqrt (refReadingAlong hN βs O t ℓ k)) ^ Fintype.card ι
          * latSkRAlong hN βs (rho1Along hN βs) k F := by
  have h1 : ∀ k' (O' : LField (MassGap.SUN.SU N)), (rho1Along hN βs).Z k' O' = 1 := fun _ _ => rfl
  have hz : ∀ k' (O' : LField (MassGap.SUN.SU N)),
      (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)).Z k' O'
        = 1 / Real.sqrt (refReadingAlong hN βs O t ℓ k') :=
    fun _ _ => rfl
  unfold latSkRAlong Renorm.pref
  simp only [h1, hz, Finset.prod_const_one, one_mul, Finset.prod_const, Finset.card_univ]
  rfl

/-- **The three-point statement along `βs`.** For a family `F` of three smeared fields, the
canonically normalised connected reading along `βs` is eventually at least one `c > 0` in absolute
value. DERIVED: `3` the number of insertions, the least connected correlator that is non-zero only in an
interacting theory. -/
def ThreePointCanonicalAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (F : Fin 3 → SField N) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
    c ≤ |latSkRAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) k F|

/-- **It forces reference positivity along `βs`.** At a non-positive reference reading `√` returns
`0`, so `zCanAlong = 0` and the three-point reading is `0`. -/
theorem refPos_of_threePointCanonical_along (hN : N ≠ 0) (βs : ℕ → ℝ)
    (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) (F : Fin 3 → SField N)
    (h : ThreePointCanonicalAlong hN βs O t ℓ F) :
    ∀ᶠ k in atTop, 0 < refReadingAlong hN βs O t ℓ k := by
  obtain ⟨c, hc, hev⟩ := h
  filter_upwards [hev] with k hk
  by_contra hneg
  have hneg' : refReadingAlong hN βs O t ℓ k ≤ 0 := le_of_not_gt hneg
  rw [latSkR_zCan_eq_along, Real.sqrt_eq_zero'.mpr hneg', div_zero, Fintype.card_fin,
    zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_mul, abs_zero] at hk
  linarith

/-- **The continuum three-point function along `βs` is non-zero** under `ThreePointCanonicalAlong` and
an eventual bound on the same reading. -/
theorem le_abs_contS_of_threePointCanonical_along (hN : N ≠ 0) (βs : ℕ → ℝ)
    (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) (F : Fin 3 → SField N)
    (h : ThreePointCanonicalAlong hN βs O t ℓ F)
    (hB : ∃ C : ℝ, ∀ᶠ k in atTop,
      |latSkRAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) k F| ≤ C) :
    ∃ c : ℝ, 0 < c
      ∧ c ≤ |contSAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) F| := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨c, hc, hev⟩ := h
  obtain ⟨C, hC⟩ := hB
  obtain ⟨x, hx⟩ := exists_tendsto_ultra _ C hC
  have hlim : contSAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) F = x :=
    hx.limUnder_eq
  refine ⟨c, hc, ?_⟩
  rw [hlim]
  exact ge_of_tendsto hx.abs (hev.filter_mono ultra_le)

/-- **The capstone with a separated three-point function, along a coupling tower.** The tower gap
`ContinuumCluster.TowerGapAt hN 0 βs M` at `M > 0`, E as `DiagBoundSepAlong` at `zCanAlong`, and
`ThreePointCanonicalAlong` give `ClayContinuumPairAlong` at every window `L > 0`; with E on the
three-point family, the continuum connected three-point function along `βs` is non-zero. -/
theorem clay_canonical_threePoint_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N))
    {t ℓ : ℝ} (ht : 0 < t) (F : Fin 3 → SField N) (h3 : ThreePointCanonicalAlong hN βs O t ℓ F)
    (hD : ContinuumSep.DiagBoundSepAlong hN βs
      (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) 0)
    {M : ℝ} (hM : 0 < M) (hG : ContinuumCluster.TowerGapAt hN 0 βs M) {L : ℝ} (hL : 0 < L)
    (hB : ∃ C : ℝ, ∀ᶠ k in atTop,
      |latSkRAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) k F| ≤ C) :
    ClayRoutes.ClayContinuumPairAlong hN βs (zCanAlong hN βs O t ℓ) 0 (zCanAlong_refl hN βs O t ℓ)
        (ContinuumSep.pairBoundSep_of_diagBoundSep_along hN βs
          (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) 0
          (Renorm.connectedAlong_reflCompat hN βs (zCanAlong hN βs O t ℓ) 0
            (zCanAlong_refl hN βs O t ℓ)) hD) L
      ∧ contSAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) F ≠ 0 := by
  refine ⟨clay_canonical_along hN βs O ht
    (refPos_of_threePointCanonical_along hN βs O t ℓ F h3) hD hM hG hL, ?_⟩
  obtain ⟨c, hc, hle⟩ := le_abs_contS_of_threePointCanonical_along hN βs O t ℓ F h3 hB
  intro h0
  rw [h0, abs_zero] at hle
  linarith

/-! ## At the couplings `dyBeta` -/

/-- **The canonical reading of any family is a power of the reference reading times the unit-strength
reading.** `zCan` is the same number for every field. -/
theorem latSkR_zCan_eq (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) (k : ℕ) {ι : Type}
    [Fintype ι] (F : ι → SField N) :
    latSkR hN (Renorm.connected hN (zCan hN O t ℓ)) k F
      = (1 / Real.sqrt (refReading hN O t ℓ k)) ^ Fintype.card ι * latSkR hN (rho1 hN) k F :=
  latSkR_zCan_eq_along hN (dyBeta (one_le_of_ne_zero hN)) O t ℓ k F

/-- **The square of a canonical three-point reading**, at a positive reference reading. -/
theorem sq_latSkR_zCan_three_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) (k : ℕ)
    (F : Fin 3 → SField N) (hr : 0 < refReadingAlong hN βs O t ℓ k) :
    (latSkRAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) k F) ^ 2
      = (latSkRAlong hN βs (rho1Along hN βs) k F) ^ 2 / refReadingAlong hN βs O t ℓ k ^ 3 := by
  rw [latSkR_zCan_eq_along, Fintype.card_fin]
  set r := refReadingAlong hN βs O t ℓ k
  have hs : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  have hsq : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  field_simp
  rw [show Real.sqrt r ^ 6 = (Real.sqrt r ^ 2) ^ 3 by ring, hs]
  ring

/-- `sq_latSkR_zCan_three` at the couplings `dyBeta`: `sq_latSkR_zCan_three_along` at `βs = dyBeta`.

DERIVED: no numeral beyond those of the statement: `3` the number of insertions and the power
`(1/√r)^{3·2} = r^{-3}`; `2` the square. -/
theorem sq_latSkR_zCan_three(hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) (k : ℕ)
    (F : Fin 3 → SField N) (hr : 0 < refReading hN O t ℓ k) :
    (latSkR hN (Renorm.connected hN (zCan hN O t ℓ)) k F) ^ 2
      = (latSkR hN (rho1 hN) k F) ^ 2 / refReading hN O t ℓ k ^ 3 :=
  sq_latSkR_zCan_three_along hN (dyBeta (one_le_of_ne_zero hN)) O t ℓ k F hr


/-- **The pinned three-point statement.** For a family `F` of three smeared fields, the canonically
normalised connected reading is eventually at least one `c > 0` in absolute value. DERIVED: `3` the
number of insertions, as in `ThreePointCanonicalAlong`. -/
def ThreePointCanonical (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (F : Fin 3 → SField N) : Prop :=
  ThreePointCanonicalAlong hN (dyBeta (one_le_of_ne_zero hN)) O t ℓ F

/-- **It forces reference positivity** (the `hpos` of `clay_canonical`). At a non-positive reference
reading `√` returns `0`, so `zCan = 0` and the three-point reading is `0`. -/
theorem refPos_of_threePointCanonical (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (F : Fin 3 → SField N) (h : ThreePointCanonical hN O t ℓ F) :
    ∀ᶠ k in atTop, 0 < refReading hN O t ℓ k :=
  refPos_of_threePointCanonical_along hN (dyBeta (one_le_of_ne_zero hN)) O t ℓ F h

/-- **The renormalisation-free form.** `ThreePointCanonical` holds exactly when, eventually, the
reference reading is positive and the squared unit-strength three-point reading is at least
`c · refReading³`. -/
theorem threePointCanonical_iff_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (F : Fin 3 → SField N) :
    ThreePointCanonicalAlong hN βs O t ℓ F ↔
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, 0 < refReadingAlong hN βs O t ℓ k ∧
        c * refReadingAlong hN βs O t ℓ k ^ 3 ≤ (latSkRAlong hN βs (rho1Along hN βs) k F) ^ 2 := by
  constructor
  · intro h
    have hpos := refPos_of_threePointCanonical_along hN βs O t ℓ F h
    obtain ⟨c, hc, hev⟩ := h
    refine ⟨c ^ 2, by positivity, ?_⟩
    filter_upwards [hev, hpos] with k hk hr
    refine ⟨hr, ?_⟩
    have h2 : c ^ 2 ≤ (latSkRAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) k F) ^ 2 := by
      rw [← sq_abs (latSkRAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) k F)]
      exact pow_le_pow_left₀ hc.le hk 2
    rw [sq_latSkR_zCan_three_along hN βs O t ℓ k F hr, le_div_iff₀ (by positivity)] at h2
    exact h2
  · rintro ⟨c, hc, hev⟩
    refine ⟨Real.sqrt c, Real.sqrt_pos.mpr hc, ?_⟩
    filter_upwards [hev] with k ⟨hr, hk⟩
    have h2 : c ≤ (latSkRAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) k F) ^ 2 := by
      rw [sq_latSkR_zCan_three_along hN βs O t ℓ k F hr, le_div_iff₀ (by positivity)]
      exact hk
    calc Real.sqrt c
        ≤ Real.sqrt ((latSkRAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) k F) ^ 2) :=
          Real.sqrt_le_sqrt h2
      _ = |latSkRAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) k F| := Real.sqrt_sq_eq_abs _

/-- `threePointCanonical_iff` at the couplings `dyBeta`: `threePointCanonical_iff_along` at `βs = dyBeta`.

DERIVED: no numeral beyond those of the statement: `3` the number of insertions. -/
theorem threePointCanonical_iff(hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (F : Fin 3 → SField N) :
    ThreePointCanonical hN O t ℓ F ↔
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, 0 < refReading hN O t ℓ k ∧
        c * refReading hN O t ℓ k ^ 3 ≤ (latSkR hN (rho1 hN) k F) ^ 2 :=
  threePointCanonical_iff_along hN (dyBeta (one_le_of_ne_zero hN)) O t ℓ F


/-- The connected smeared field of step `k`: `smear a_k (O − ν_k(O)) f`. -/
def cfield (hN : N ≠ 0) (k : ℕ) (p : SField N) : C(Cfg N, ℝ) :=
  smear (dySpacing N k) (p.1.sub (stateK hN k p.1.1)).1 p.2

/-- **The continuum three-point function is non-zero.** Under `ThreePointCanonical` and an eventual
bound on the same reading (E on this family), the continuum Schwinger function of the three
canonically normalised connected fields is at least `c` in absolute value. -/
theorem le_abs_contS_of_threePointCanonical (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (F : Fin 3 → SField N) (h : ThreePointCanonical hN O t ℓ F)
    (hB : ∃ C : ℝ, ∀ᶠ k in atTop, |latSkR hN (Renorm.connected hN (zCan hN O t ℓ)) k F| ≤ C) :
    ∃ c : ℝ, 0 < c ∧ c ≤ |contS hN (Renorm.connected hN (zCan hN O t ℓ)) F| :=
  le_abs_contS_of_threePointCanonical_along hN (dyBeta (one_le_of_ne_zero hN)) O t ℓ F h hB

/-- **The pinned capstone with a separated three-point function.** `WDelta2`, E as `DiagBoundSep` at
`zCan`, and `ThreePointCanonical` give `ClayContinuumPair` at window `5ℓ₀` (reference positivity is no
longer a hypothesis); with E on the three-point family, the continuum connected three-point function of
the canonically normalised fields is non-zero. -/
theorem clay_canonical_threePoint (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N))
    {t ℓ : ℝ} (ht : 0 < t) (F : Fin 3 → SField N) (h3 : ThreePointCanonical hN O t ℓ F)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (zCan hN O t ℓ)) 0) {ℓ₀ : ℝ}
    (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀)
    (hB : ∃ C : ℝ, ∀ᶠ k in atTop, |latSkR hN (Renorm.connected hN (zCan hN O t ℓ)) k F| ≤ C) :
    ClayRoutes.ClayContinuumPair hN (zCan hN O t ℓ) 0 (zCan_refl hN O t ℓ)
        (ContinuumSep.pairBoundSep_of_diagBoundSep hN (Renorm.connected hN (zCan hN O t ℓ)) 0
          (Renorm.connected_reflCompat hN (zCan hN O t ℓ) 0 (zCan_refl hN O t ℓ)) hD) (5 * ℓ₀)
      ∧ contS hN (Renorm.connected hN (zCan hN O t ℓ)) F ≠ 0 := by
  obtain ⟨M, hM, hG⟩ := towerGapAt_dyBeta_of_WDelta2 hN2 hN hℓ hW
  exact clay_canonical_threePoint_along hN _ O ht F h3 hD hM hG (by positivity) hB

/-! ## The item-4 statement at separated supports -/

/-- Three test functions with pairwise separated supports: any two support points of different
insertions differ by at least `d > 0` in some coordinate. DERIVED: `3` the number of insertions;
`4` the dimension. -/
def SepThree (d : ℝ) (F : Fin 3 → SField N) : Prop :=
  0 < d ∧ ∀ i j : Fin 3, i ≠ j → ∀ y z : Fin 4 → ℝ, (F i).2.1 y ≠ 0 → (F j).2.1 z ≠ 0 →
    ∃ μ : Fin 4, d ≤ |y μ - z μ|

/-- **The named open statement (N₃ on the pinned theory).** Three insertions of the reference field
`O` at pairwise separated supports whose canonical connected three-point reading is eventually bounded
away from `0`. DERIVED: `3` the number of insertions. -/
def CanonicalThreePoint (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) : Prop :=
  ∃ (F : Fin 3 → SField N) (d : ℝ), (∀ i, (F i).1 = O) ∧ SepThree d F ∧ ThreePointCanonical hN O t ℓ F

/-- **E on separated three-point families** at `zCan`: every separated three-insertion reading is
eventually bounded. Part of (E_multi). DERIVED: `3` the number of insertions. -/
def ThreePointBound (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) : Prop :=
  ∀ (F : Fin 3 → SField N) (d : ℝ), SepThree d F →
    ∃ C : ℝ, ∀ᶠ k in atTop, |latSkR hN (Renorm.connected hN (zCan hN O t ℓ)) k F| ≤ C

/-- **The pinned capstone with item 4 in the N₃ form.** `WDelta2`, `DiagBoundSep` at `zCan`, the
separated three-point bound, and `CanonicalThreePoint` give `ClayContinuumPair` at window `5ℓ₀` together
with a separated family of three insertions of `O` whose continuum connected three-point function is
non-zero. Reference positivity (item 3) is not a hypothesis. -/
theorem clay_canonical_nonGaussian (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N))
    {t ℓ : ℝ} (ht : 0 < t) (h3 : CanonicalThreePoint hN O t ℓ)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (zCan hN O t ℓ)) 0) {ℓ₀ : ℝ}
    (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) (hE3 : ThreePointBound hN O t ℓ) :
    ClayRoutes.ClayContinuumPair hN (zCan hN O t ℓ) 0 (zCan_refl hN O t ℓ)
        (ContinuumSep.pairBoundSep_of_diagBoundSep hN (Renorm.connected hN (zCan hN O t ℓ)) 0
          (Renorm.connected_reflCompat hN (zCan hN O t ℓ) 0 (zCan_refl hN O t ℓ)) hD) (5 * ℓ₀)
      ∧ ∃ (F : Fin 3 → SField N) (d : ℝ), (∀ i, (F i).1 = O) ∧ SepThree d F ∧
          contS hN (Renorm.connected hN (zCan hN O t ℓ)) F ≠ 0 := by
  obtain ⟨F, d, hO, hs, h⟩ := h3
  obtain ⟨hcl, hne⟩ := clay_canonical_threePoint hN2 hN O ht F h hD hℓ hW (hE3 F d hs)
  exact ⟨hcl, F, d, hO, hs, hne⟩

end MassGap.NonTrivialCanonical

#print axioms MassGap.NonTrivialCanonical.latSkR_zCan_eq
#print axioms MassGap.NonTrivialCanonical.latSkR_zCan_eq_along
#print axioms MassGap.NonTrivialCanonical.refPos_of_threePointCanonical_along
#print axioms MassGap.NonTrivialCanonical.le_abs_contS_of_threePointCanonical_along
#print axioms MassGap.NonTrivialCanonical.clay_canonical_threePoint_along
#print axioms MassGap.NonTrivialCanonical.refPos_of_threePointCanonical
#print axioms MassGap.NonTrivialCanonical.threePointCanonical_iff
#print axioms MassGap.NonTrivialCanonical.le_abs_contS_of_threePointCanonical
#print axioms MassGap.NonTrivialCanonical.clay_canonical_threePoint
#print axioms MassGap.NonTrivialCanonical.clay_canonical_nonGaussian
