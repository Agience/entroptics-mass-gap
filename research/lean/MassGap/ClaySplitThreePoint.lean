import Mathlib
import MassGap.NonTrivialCanonical

noncomputable section

/-!
# MassGap.ClaySplitThreePoint — a three-point reading split across the reflection plane

`NonTrivialCanonical.clay_canonical_nonGaussian` takes E on every separated three-insertion family
(`ThreePointBound`) besides `DiagBoundSep`, because a separated three-point family need not be a
reflected pair. Split across the reflection plane, it is one: a family `θP ∪ Q` with `P`, `Q`
separated positive-time monomials is bounded by the reflected diagonals of `P` and `Q`
(`ContinuumSep.pairBoundSep_of_diagBoundSep`), which `DiagBoundSep` already bounds.

* `latSkR_comp_equiv`, `contS_comp_equiv`: lattice and continuum readings do not depend on how the
  family is indexed.
* `bound_split`: under `DiagBoundSep` at any reflection-compatible `Z`, every family `θP ∪ Q`, in any
  indexing, is eventually bounded. E on plane-split families is part of `DiagBoundSep`.
* `SplitThreePoint hN O t ℓ`: three insertions of `O`, one group reflected below the plane and the
  rest above it (`P.1.1 + Q.1.1 = 3`), whose canonical connected reading is eventually at least one
  `c > 0` in absolute value. `split_family` turns it into a `Fin 3` family with `SepThree` and
  `ThreePointCanonical`; `canonicalThreePoint_of_split` gives `CanonicalThreePoint`, so every control
  that refutes `CanonicalThreePoint` refutes it.
* `clay_of_splitThreePoint`: `WDelta2`, `DiagBoundSep` at `zCan` and `SplitThreePoint` give the conclusion of
  `clay_canonical_nonGaussian`: `ClayContinuumPair` at window `5ℓ₀` and a separated family of three
  insertions of `O` with non-zero continuum connected three-point function. `ThreePointBound` and the
  reference positivity are not hypotheses.

`SplitThreePoint` is satisfied by the Wick square of a free massive field, so the non-zero
three-point function is not Clay non-triviality; that needs the short-distance requirement
(`ShortDistanceY`).
-/

namespace MassGap.ClaySplitThreePoint

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.ExistenceReduce
  MassGap.NonTrivialCanonical Filter

variable {N : ℕ}

/-- **A lattice reading does not depend on the indexing of the family.** -/
theorem latSkR_comp_equiv (hN : N ≠ 0) (ρ : Renorm N) (k : ℕ) {ι ι' : Type} [Fintype ι]
    [Fintype ι'] (e : ι' ≃ ι) (F : ι → SField N) :
    latSkR hN ρ k (F ∘ e) = latSkR hN ρ k F := by
  unfold latSkR Renorm.pref latSk latS
  congr 1
  · exact Fintype.prod_equiv e _ _ (fun _ => rfl)
  · exact congrArg _ (Fintype.prod_equiv e _ _ (fun _ => rfl))

/-- **A continuum reading does not depend on the indexing of the family.** -/
theorem contS_comp_equiv (hN : N ≠ 0) (ρ : Renorm N) {ι ι' : Type} [Fintype ι] [Fintype ι']
    (e : ι' ≃ ι) (F : ι → SField N) :
    contS hN ρ (F ∘ e) = contS hN ρ F := by
  have h : (fun k => latSkR hN ρ k (F ∘ e)) = (fun k => latSkR hN ρ k F) :=
    funext fun k => latSkR_comp_equiv hN ρ k e F
  unfold contS
  rw [h]

/-! ## Along a coupling tower -/

/-- **E on plane-split families along `βs` is part of `DiagBoundSepAlong`.** Every family `θP ∪ Q`
of separated positive-time monomials, in any indexing, is eventually bounded. -/
theorem bound_split_along (hN : N ≠ 0) (βs : ℕ → ℝ) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hD : ContinuumSep.DiagBoundSepAlong hN βs (Renorm.connectedAlong hN βs Z) 0)
    (P Q : ContinuumSep.SepMono N 0) {ι : Type} [Fintype ι] (e : ι ≃ (Fin P.1.1 ⊕ Fin Q.1.1)) :
    ∃ C : ℝ, ∀ᶠ k in atTop,
      |latSkRAlong hN βs (Renorm.connectedAlong hN βs Z) k (pairFam 0 P.1 Q.1 ∘ e)| ≤ C := by
  obtain ⟨C, hC⟩ := ContinuumSep.pairBoundSep_of_diagBoundSep_along hN βs
    (Renorm.connectedAlong hN βs Z) 0 (Renorm.connectedAlong_reflCompat hN βs Z 0 hZ) hD P Q
  refine ⟨C, (hC 0 0).mono fun k hk => ?_⟩
  rw [latSkRAlong_comp_equiv hN βs (Renorm.connectedAlong hN βs Z) k e (pairFam 0 P.1 Q.1)]
  exact hk

/-- **The three-point lower bound along `βs`, split across the reflection plane.** Three insertions
of `O`, split as `θP ∪ Q` with `P`, `Q` separated positive-time monomials, whose canonical connected
reading along `βs` is eventually bounded away from `0`.

DERIVED: `3` the insertions of a three-point function, the lowest connected reading that vanishes on
every Gaussian state. -/
def SplitThreePointAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) :
    Prop :=
  ∃ (P Q : ContinuumSep.SepMono N 0), P.1.1 + Q.1.1 = 3 ∧
    (∀ x, (pairFam 0 P.1 Q.1 x).1 = O) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      c ≤ |latSkRAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) k
        (pairFam 0 P.1 Q.1)|

/-- A split three-point family along `βs` as a `Fin 3` family: its fields are `O`, it is `SepThree`,
and it satisfies `ThreePointCanonicalAlong`. -/
theorem split_family_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (h3 : SplitThreePointAlong hN βs O t ℓ) :
    ∃ (P Q : ContinuumSep.SepMono N 0) (e : Fin 3 ≃ (Fin P.1.1 ⊕ Fin Q.1.1)) (d : ℝ),
      (∀ i, (pairFam 0 P.1 Q.1 (e i)).1 = O) ∧ SepThree d (pairFam 0 P.1 Q.1 ∘ e) ∧
      ThreePointCanonicalAlong hN βs O t ℓ (pairFam 0 P.1 Q.1 ∘ e) := by
  obtain ⟨P, Q, hcard, hO, c, hc, hev⟩ := h3
  have hc' : Fintype.card (Fin P.1.1 ⊕ Fin Q.1.1) = 3 := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    exact hcard
  obtain ⟨e⟩ : Nonempty (Fin 3 ≃ (Fin P.1.1 ⊕ Fin Q.1.1)) :=
    ⟨(Fintype.equivFinOfCardEq hc').symm⟩
  obtain ⟨d, hd, hfam⟩ := ContinuumSep.famSep_pairFam_exists P.2 Q.2
  refine ⟨P, Q, e, d, fun i => hO (e i),
    ⟨hd, fun i j hij y z hy hz => hfam (e i) (e j) (e.injective.ne hij) y z hy hz⟩,
    ⟨c, hc, hev.mono fun k hk => ?_⟩⟩
  rw [latSkRAlong_comp_equiv hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) k e
    (pairFam 0 P.1 Q.1)]
  exact hk

/-- **The Clay statement from the split three-point bound, along a coupling tower.** The tower gap
`ContinuumCluster.TowerGapAt hN 0 βs M` at `M > 0`, `DiagBoundSepAlong` at `zCanAlong` and
`SplitThreePointAlong` give `ClayContinuumPairAlong` at every window `L > 0` and a separated family of
three insertions of `O` whose continuum connected three-point function along `βs` is non-zero. -/
theorem clay_of_splitThreePoint_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N))
    {t ℓ : ℝ} (ht : 0 < t) (h3 : SplitThreePointAlong hN βs O t ℓ)
    (hD : ContinuumSep.DiagBoundSepAlong hN βs
      (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) 0)
    {M : ℝ} (hM : 0 < M) (hG : ContinuumCluster.TowerGapAt hN 0 βs M) {L : ℝ} (hL : 0 < L) :
    ClayRoutes.ClayContinuumPairAlong hN βs (zCanAlong hN βs O t ℓ) 0 (zCanAlong_refl hN βs O t ℓ)
        (ContinuumSep.pairBoundSep_of_diagBoundSep_along hN βs
          (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) 0
          (Renorm.connectedAlong_reflCompat hN βs (zCanAlong hN βs O t ℓ) 0
            (zCanAlong_refl hN βs O t ℓ)) hD) L
      ∧ ∃ (F : Fin 3 → SField N) (d : ℝ), (∀ i, (F i).1 = O) ∧ SepThree d F ∧
          contSAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) F ≠ 0 := by
  obtain ⟨P, Q, e, d, hO, hs, h⟩ := split_family_along hN βs O t ℓ h3
  obtain ⟨hcl, hne⟩ := clay_canonical_threePoint_along hN βs O ht (pairFam 0 P.1 Q.1 ∘ e) h hD
    hM hG hL (bound_split_along hN βs (zCanAlong hN βs O t ℓ) (zCanAlong_refl hN βs O t ℓ) hD P Q e)
  exact ⟨hcl, pairFam 0 P.1 Q.1 ∘ e, d, hO, hs, hne⟩

/-! ## At the couplings `dyBeta` -/

/-- **E on plane-split families is part of `DiagBoundSep`.** Every family `θP ∪ Q` of separated
positive-time monomials, in any indexing, is eventually bounded. -/
theorem bound_split (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) 0) (P Q : ContinuumSep.SepMono N 0)
    {ι : Type} [Fintype ι] (e : ι ≃ (Fin P.1.1 ⊕ Fin Q.1.1)) :
    ∃ C : ℝ, ∀ᶠ k in atTop,
      |latSkR hN (Renorm.connected hN Z) k (pairFam 0 P.1 Q.1 ∘ e)| ≤ C := by
  obtain ⟨C, hC⟩ := ContinuumSep.pairBoundSep_of_diagBoundSep hN (Renorm.connected hN Z) 0
    (Renorm.connected_reflCompat hN Z 0 hZ) hD P Q
  refine ⟨C, (hC 0 0).mono fun k hk => ?_⟩
  rw [latSkR_comp_equiv hN (Renorm.connected hN Z) k e (pairFam 0 P.1 Q.1)]
  exact hk

/-- **The three-point lower bound, split across the reflection plane.** Three insertions of `O`, split as
`θP ∪ Q` with `P`, `Q` separated positive-time monomials, whose canonical connected reading is
eventually bounded away from `0`: `SplitThreePointAlong` at the couplings `dyBeta`. -/
def SplitThreePoint (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) : Prop :=
  SplitThreePointAlong hN (dyBeta (one_le_of_ne_zero hN)) O t ℓ

/-- A split three-point family as a `Fin 3` family: its fields are `O`, it is `SepThree`, and it
satisfies `ThreePointCanonical`. -/
theorem split_family (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (h3 : SplitThreePoint hN O t ℓ) :
    ∃ (P Q : ContinuumSep.SepMono N 0) (e : Fin 3 ≃ (Fin P.1.1 ⊕ Fin Q.1.1)) (d : ℝ),
      (∀ i, (pairFam 0 P.1 Q.1 (e i)).1 = O) ∧ SepThree d (pairFam 0 P.1 Q.1 ∘ e) ∧
      ThreePointCanonical hN O t ℓ (pairFam 0 P.1 Q.1 ∘ e) :=
  split_family_along hN (dyBeta (one_le_of_ne_zero hN)) O t ℓ h3

/-- **The split statement gives `CanonicalThreePoint`**, so every control that refutes the latter
refutes it. -/
theorem canonicalThreePoint_of_split (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (h3 : SplitThreePoint hN O t ℓ) : CanonicalThreePoint hN O t ℓ := by
  obtain ⟨P, Q, e, d, hO, hs, h⟩ := split_family hN O t ℓ h3
  exact ⟨pairFam 0 P.1 Q.1 ∘ e, d, hO, hs, h⟩

/-- **The Clay statement from the split three-point bound.** `WDelta2`,
`DiagBoundSep` at `zCan` and `SplitThreePoint` give `ClayContinuumPair` at window `5ℓ₀` and a
separated family of three insertions of `O` whose continuum connected three-point function is
non-zero: the conclusion of `clay_canonical_nonGaussian`, without `ThreePointBound` and without
reference positivity. -/
theorem clay_of_splitThreePoint (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {t ℓ : ℝ}
    (ht : 0 < t) (h3 : SplitThreePoint hN O t ℓ)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (zCan hN O t ℓ)) 0) {ℓ₀ : ℝ}
    (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (zCan hN O t ℓ) 0 (zCan_refl hN O t ℓ)
        (ContinuumSep.pairBoundSep_of_diagBoundSep hN (Renorm.connected hN (zCan hN O t ℓ)) 0
          (Renorm.connected_reflCompat hN (zCan hN O t ℓ) 0 (zCan_refl hN O t ℓ)) hD) (5 * ℓ₀)
      ∧ ∃ (F : Fin 3 → SField N) (d : ℝ), (∀ i, (F i).1 = O) ∧ SepThree d F ∧
          contS hN (Renorm.connected hN (zCan hN O t ℓ)) F ≠ 0 := by
  obtain ⟨M, hM, hG⟩ := towerGapAt_dyBeta_of_WDelta2 hN2 hN hℓ hW
  exact clay_of_splitThreePoint_along hN _ O ht h3 hD hM hG (by positivity)

end MassGap.ClaySplitThreePoint

#print axioms MassGap.ClaySplitThreePoint.latSkR_comp_equiv
#print axioms MassGap.ClaySplitThreePoint.contS_comp_equiv
#print axioms MassGap.ClaySplitThreePoint.bound_split
#print axioms MassGap.ClaySplitThreePoint.split_family
#print axioms MassGap.ClaySplitThreePoint.canonicalThreePoint_of_split
#print axioms MassGap.ClaySplitThreePoint.clay_of_splitThreePoint
#print axioms MassGap.ClaySplitThreePoint.bound_split_along
#print axioms MassGap.ClaySplitThreePoint.split_family_along
#print axioms MassGap.ClaySplitThreePoint.clay_of_splitThreePoint_along
