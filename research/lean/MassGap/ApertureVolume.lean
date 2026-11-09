import Mathlib
import MassGap.ApertureNearAll
import MassGap.TorusRefPosProof
import MassGap.LocalClosing
import MassGap.ApertureWindow

/-!
# MassGap.ApertureVolume — the volume clause from the windowed near bound

`ApertureFinal.clay_final` takes three inputs: `NearOwn` (near), `∃ c > 0, RefPassageLow` (far, volume) and
`PhysDefect L (1/1000)` (far, defect). This module proves the volume clause from a windowed near statement read in
the torus states, so the capstone takes two inputs.

## The windowed near statement

`NearWin hN βs M₀ s₀` is `ApertureNearAll.NearAll` with one more clause on the lattice points: for one depth `D`
per list and margin, constant in the level, every coordinate has `4 (|p i μ| + D) ≤ j`, `2(j + 1)` the torus
extent. Inside that window the supports and their reflections lie in a box of half-width `j/4`, so `ℤ⁴`-separation
is separation in the torus metric. It is `ApertureWindow.NearAllW` with the depth `D k = D` constant
(`nearAllW_of_nearWin`). `nearWin_of_nearAll`: the unwindowed statement implies it. `nearOwn_of_nearWin`: it
implies `NearOwn`, since along `periodicUltra` every fixed configuration is eventually inside the window.

The volume clause reads the torus `stateT hN M₀` at exactly `j = M₀ 2ᵏ`, so it needs the depth to stay below a
fixed fraction of `2ᵏ`; `NearAllW` lets `D k` be any function of `k`, and with `D k ≥ M₀ 2ᵏ/4` its window at
`stateT` is empty. A constant depth (the lattice size of a point field's support) is enough.

`NearWin` reads the torus states with the vacuum one-point subtraction (`rho1Along`), as `NearAll` does. Its
left side therefore contains the square of the torus-minus-vacuum one-point shift, `a⁸ (⟨O⟩_T − ⟨O⟩_∞)²` per point
pair; `NearWin` asserts that this term is also at most `C a⁸ R_∞`.

## The volume clause (proved)

* `own_le_const`: in a reflection- and shift-invariant state `ν`, the reflected pairing of the smeared field
  centred at `ν`'s own one-point function is at most the pairing centred at any constant `r`. The difference is
  `w² (r − ν(O))²`, `w` the cell weight of the test function.
* `refReadingS_le_vac`: so the torus reference reading `R_T` (own centring) is at most the same reading with
  the vacuum centring.
* `slabSub`, `slabForm`: the observables local on links in `0 ≤ x₀ ≤ M` form a submodule on which the torus
  state of extent `2(M + 1)` is reflection positive (`TorusRefPosProof.torusState_refl_mul_nonneg`); the reflected
  pairing is a `Transfer.ReflForm` on it.
* `vacReading_le_of_nearWin`: at `0 < t`, `0 ≤ ℓ`, `8(t + ℓ) < M₀ · aRun N 1`, `0 < s₀`, `NearWin` gives one
  `C ≥ 0` with, eventually in `k`, the vacuum-centred torus cube reading at most `C · R_∞(s₀, s₀)`. The cube
  field is a sum of point fields over the cube's lattice points (`ExistencePoint.smear_eq_sum_pt`); Cauchy–Schwarz
  in `slabForm` and `NearWin` at one field bound it, the count of points times `a⁴` staying below `(2R + 3)⁴`.
* `refPassageLow_of_nearWin`: `NearWin ⇒ ∃ c > 0, RefPassageLow` at `(t, ℓ) = (s₀, s₀)`.

The mass gap is not used. The image terms of the torus are part of what `NearWin` bounds, since `NearWin` is read
in the torus states themselves.

## The capstone

`clay_two`: at `N = 2`, `O = planePlaq 2`, `(t, ℓ) = (s₀, s₀)`, `0 < s₀`, `8(s₀ + s₀) < M₀ · aRun 2 1`, `0 < L`,
the two inputs `NearWin` (near) and `PhysDefect L (1/1000)` (far) give a witness of `hD` at `zOwn` and
`ClayContinuumPair` at `zOwn`, at window `5 · L/2`. `clay_two_far` takes `ApertureNearAll.Far L (1/15000)` in
place of `PhysDefect`.

DERIVED (module-wide): `0` the reflection plane and the time direction; `1` the single field and the sup bound of
the cube indicator; `2` the doubling and the reflection square; `3` the box rounding of
`ExistencePoint.mul_box_side_le`; `4` the dimension and the window ratio (differences at most half the half-extent);
`8 = 2 · 4` the window ratio times the spacing-to-half-side ratio `M₀ 2ᵏ a_k = M₀ aRun/2`, and `8 = 2 · 4` the
point-pair cell power; `15` the four slice doublings `8 + 4 + 2 + 1`; `1/1000` the `RunSeed` threshold.
-/

noncomputable section

namespace MassGap.ApertureVolume

open Filter MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumCluster MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ExistencePoint
  MassGap.TorusCapstone MassGap.PhysicalScaleSmall
open scoped Topology

variable {N : ℕ}

/-! ## 1. The windowed near statement -/

section Window

/-- **The near bound in every torus state, inside the window `4 (|p i μ| + D) ≤ j`.**

DERIVED: `4` the window ratio; `8 = 2 · 4` the point-pair cell power, the spacing exponent per field. -/
def NearWin (hN : N ≠ 0) (βs : ℕ → ℝ) (M₀ : ℕ) (s₀ : ℝ) : Prop :=
  ∀ (n : ℕ) (L : Fin n → LField (MassGap.SUN.SU N)) (d : ℝ), 0 < d → ∃ (C : ℝ) (D : ℕ),
    ∀ᶠ k in atTop, ∀ j : ℕ, M₀ * 2 ^ k ≤ j → ∀ p : Fin n → ISite,
      (∀ i μ, 4 * (|p i μ| + (D : ℤ)) ≤ (j : ℤ)) →
      ContinuumSep.sepPos 0 d (ptMono L (fun i => site (dySpacing N k) (p i))) →
      TorusCapstone.latSkRS (ApertureNearAll.torusAlong hN βs j) (rho1Along hN βs) k
          (pairFam 0 (ptMono L (fun i => site (dySpacing N k) (p i)))
            (ptMono L (fun i => site (dySpacing N k) (p i))))
        ≤ C * dySpacing N k ^ (8 * n) * ∏ i, refReadingAlong hN βs (L i) s₀ s₀ k

/-- The unwindowed statement implies the windowed one. -/
theorem nearWin_of_nearAll (hN : N ≠ 0) (βs : ℕ → ℝ) {M₀ : ℕ} {s₀ : ℝ}
    (h : ApertureNearAll.NearAll hN βs M₀ s₀) : NearWin hN βs M₀ s₀ := by
  intro n L d hd
  obtain ⟨C, hC⟩ := h n L d hd
  exact ⟨C, 0, hC.mono fun k hk j hj p _ hp => hk j hj p hp⟩

/-- `NearWin` is `ApertureWindow.NearAllW` with a depth constant in the level. -/
theorem nearAllW_of_nearWin (hN : N ≠ 0) (βs : ℕ → ℝ) {M₀ : ℕ} {s₀ : ℝ} (h : NearWin hN βs M₀ s₀) :
    ApertureWindow.NearAllW hN βs M₀ s₀ := by
  intro n L d hd
  obtain ⟨C, D, hC⟩ := h n L d hd
  exact ⟨C, fun _ => D, hC⟩

/-- **The windowed near bound gives `NearOwn`.** -/
theorem nearOwn_of_nearWin (hN : N ≠ 0) (βs : ℕ → ℝ) {M₀ : ℕ} {s₀ : ℝ} (h : NearWin hN βs M₀ s₀) :
    ApertureTwo.NearOwn hN βs s₀ := by
  intro n L d hd
  obtain ⟨C, D, hC⟩ := h n L d hd
  refine ⟨C, ?_⟩
  filter_upwards [hC] with k hk p hp
  have hev : ∀ᶠ j in ((PeriodicState.periodicUltra hN (βs k) : Ultrafilter ℕ) : Filter ℕ),
      M₀ * 2 ^ k ≤ j :=
    (eventually_ge_atTop _).filter_mono (PeriodicState.periodicUltra_le hN (βs k))
  have hw : ∀ᶠ j : ℕ in ((PeriodicState.periodicUltra hN (βs k) : Ultrafilter ℕ) : Filter ℕ),
      ∀ i μ, 4 * (|p i μ| + (D : ℤ)) ≤ (j : ℤ) :=
    (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun μ =>
      (eventually_ge_atTop (4 * (|p i μ| + (D : ℤ))).toNat).mono fun j hj =>
        (Int.self_le_toNat (4 * (|p i μ| + (D : ℤ)))).trans (by exact_mod_cast hj)).filter_mono
      (PeriodicState.periodicUltra_le hN (βs k))
  exact le_of_tendsto ((PeriodicState.tendsto_periodicState hN (βs k) _).const_mul _)
    ((hev.and hw).mono fun j hj => hk j hj.1 p hj.2 hp)

end Window

/-! ## 2. The own centring is the least -/

section Centring

/-- The reflected square of a field shifted by a constant. -/
theorem refl_sq_shift (ν : DLRLimit.State (Cfg N))
    (hinv : InfiniteReflection.IsReflectionInvariant
      (LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) 0 0) ν)
    (X : C(Cfg N, ℝ)) (p : ℝ) :
    ν (LatticeReflection.ireflObs 0 0 (X - p • (1 : C(Cfg N, ℝ))) * (X - p • (1 : C(Cfg N, ℝ))))
      = ν (LatticeReflection.ireflObs 0 0 X * X) - 2 * p * ν X + p ^ 2 := by
  have hθ : LatticeReflection.ireflObs (G := MassGap.SUN.SU N) 0 0 (X - p • (1 : C(Cfg N, ℝ)))
      = LatticeReflection.ireflObs 0 0 X - p • (1 : C(Cfg N, ℝ)) := by
    rw [map_sub, map_smul,
      show LatticeReflection.ireflObs (G := MassGap.SUN.SU N) 0 0 (1 : C(Cfg N, ℝ)) = 1 from rfl]
  have hX : ν (LatticeReflection.ireflObs 0 0 X) = ν X := hinv X
  have he : (LatticeReflection.ireflObs 0 0 X - p • (1 : C(Cfg N, ℝ))) * (X - p • (1 : C(Cfg N, ℝ)))
      = LatticeReflection.ireflObs 0 0 X * X + (-p) • LatticeReflection.ireflObs 0 0 X
        + (-p) • X + (p ^ 2) • (1 : C(Cfg N, ℝ)) := by
    ext U
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul]
    ring
  rw [hθ, he, ν.map_add, ν.map_add, ν.map_add, ν.map_smul, ν.map_smul, ν.map_smul, ν.map_one, hX]
  ring

/-- **The own centring gives the least reflected square.** -/
theorem own_le_const (ν : DLRLimit.State (Cfg N))
    (hinv : InfiniteReflection.IsReflectionInvariant
      (LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) 0 0) ν)
    (hsh : ∀ (τ : Fin 4) (F : C(Cfg N, ℝ)), ν (MassGap.ReflectionShift.ishiftObsL τ F) = ν F)
    {a : ℝ} (ha : 0 < a) (O : LField (MassGap.SUN.SU N)) (f : TestFn) (r : ℝ) :
    ν (LatticeReflection.ireflObs 0 0 (smear a (O.sub (ν O.1)).1 f) * smear a (O.sub (ν O.1)).1 f)
      ≤ ν (LatticeReflection.ireflObs 0 0 (smear a (O.sub r).1 f) * smear a (O.sub r).1 f) := by
  rw [LocalClosing.smear_sub_eq ha O (ν O.1) f, LocalClosing.smear_sub_eq ha O r f,
    refl_sq_shift ν hinv, refl_sq_shift ν hinv,
    LocalClosing.state_smear ν (fun x F => state_transObs hsh x F) ha O.1 f]
  nlinarith [sq_nonneg (r * LocalClosing.wsum a f - ν O.1 * LocalClosing.wsum a f)]

/-- **The torus reference reading is at most its vacuum-centred form.** -/
theorem refReadingS_le_vac (hN : N ≠ 0) (M₀ : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) (k : ℕ) :
    refReadingS (stateT hN M₀) O t ℓ k
      ≤ latSkRS (stateT hN M₀) (rho1Along hN (dyBeta (one_le_of_ne_zero hN))) k
          (pairFam 0 (refMono O t ℓ) (refMono O t ℓ)) := by
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  rw [TorusRefPosProof.refReadingS_stateT_eq, TorusRefPosProof.latSkRS_pairFam_eq hN _ _ 0
    (Renorm.connectedAlong_reflCompat hN _ (fun _ _ => 1) 0 (fun _ _ => rfl)) k]
  have e1 : ContinuumCluster.Yv (connectedS (stateT hN M₀) (fun _ _ => 1)) k (refMono O t ℓ)
      = smear (dySpacing N k) (O.sub (stateT hN M₀ k O.1)).1 (ContinuumNontrivial.cubeTest t ℓ) := by
    show (∏ _i : Fin 1, (1 : ℝ)) • (∏ _i : Fin 1,
      smear (dySpacing N k) (O.sub (stateT hN M₀ k O.1)).1 (ContinuumNontrivial.cubeTest t ℓ)) = _
    simp
  have e2 : ContinuumCluster.Yv (rho1Along hN (dyBeta (one_le_of_ne_zero hN))) k (refMono O t ℓ)
      = smear (dySpacing N k) (O.sub (stateAlong hN (dyBeta (one_le_of_ne_zero hN)) k O.1)).1
          (ContinuumNontrivial.cubeTest t ℓ) := by
    show (∏ _i : Fin 1, (1 : ℝ)) • (∏ _i : Fin 1,
      smear (dySpacing N k) (O.sub (stateAlong hN (dyBeta (one_le_of_ne_zero hN)) k O.1)).1
        (ContinuumNontrivial.cubeTest t ℓ)) = _
    simp
  rw [e1, e2]
  exact own_le_const (stateT hN M₀ k) (stateT_reflInvariant hN M₀ k 0 0) (stateT_shift hN M₀ k) ha O _ _

end Centring

/-! ## 3. Reflection positivity on a slab of the torus -/

section Slab

/-- The observables local on finitely many links in `0 ≤ x₀ ≤ M`. -/
def slabSub (M : ℕ) : Submodule ℝ C(Cfg N, ℝ) where
  carrier := {Y | ∃ T : Finset ILink, (↑T ⊆ HalfSpaceAlgebra.posHalf 0 0) ∧
    IsLocalOn T (Y : Cfg N → ℝ) ∧ ∀ l ∈ T, l.2 0 ≤ (M : ℤ)}
  zero_mem' := ⟨∅, by simp, fun _ _ _ => rfl, by simp⟩
  add_mem' := by
    rintro Y Z ⟨T, hT, hl, hd⟩ ⟨T', hT', hl', hd'⟩
    refine ⟨T ∪ T', ?_, ?_, ?_⟩
    · rw [Finset.coe_union]
      exact Set.union_subset hT hT'
    · intro U V h
      show Y U + Z U = Y V + Z V
      rw [hl U V (fun l hl0 => h l (Finset.mem_union_left _ hl0)),
        hl' U V (fun l hl0 => h l (Finset.mem_union_right _ hl0))]
    · intro l hl0
      rcases Finset.mem_union.mp hl0 with h | h
      · exact hd l h
      · exact hd' l h
  smul_mem' := by
    rintro r Y ⟨T, hT, hl, hd⟩
    refine ⟨T, hT, fun U V h => ?_, hd⟩
    show r * Y U = r * Y V
    rw [hl U V h]

/-- The torus state of extent `2(M + 1)` is reflection positive on the slab observables. -/
theorem slab_reflPositive (hN : N ≠ 0) (M : ℕ) (β : ℝ) :
    InfiniteReflection.ReflPositiveOn
      (LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) 0 0)
      (slabSub (N := N) M) (PeriodicState.torusState hN (2 * M + 1) β) := by
  rintro Y ⟨T, hT, hl, hd⟩
  exact TorusRefPosProof.torusState_refl_mul_nonneg hN M β Y T hT hl hd

/-- The reflected torus pairing on the slab observables. -/
def slabForm (hN : N ≠ 0) (M : ℕ) (β : ℝ) : Transfer.ReflForm ↥(slabSub (N := N) M) :=
  InfiniteReflection.stateReflForm (LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) 0 0)
    (PeriodicState.torusState hN (2 * M + 1) β) (slabSub M)
    (PeriodicState.torusState_reflInvariant hN _ _ 0 0) (slab_reflPositive hN M β)

end Slab

/-! ## 4. The cube reading from the point readings -/

section Cube

/-- **The vacuum-centred torus cube reading is bounded by the infinite-volume reference reading.** -/
theorem vacReading_le_of_nearWin (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {M₀ : ℕ} {t ℓ s₀ : ℝ}
    (ht : 0 < t) (hℓ : 0 ≤ ℓ) (hs₀ : 0 < s₀)
    (h8 : 8 * (t + ℓ) < M₀ * AsymptoticScaling.aRun N 1)
    (h : NearWin hN (dyBeta (one_le_of_ne_zero hN)) M₀ s₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      latSkRS (stateT hN M₀) (rho1Along hN (dyBeta (one_le_of_ne_zero hN))) k
          (pairFam 0 (refMono O t ℓ) (refMono O t ℓ))
        ≤ C * refReadingAlong hN (dyBeta (one_le_of_ne_zero hN)) O s₀ s₀ k := by
  classical
  set βs := dyBeta (one_le_of_ne_zero hN) with hβs
  set ρ := rho1Along hN βs with hρ
  have hR : ρ.ReflCompat 0 :=
    Renorm.connectedAlong_reflCompat hN βs (fun _ _ => 1) 0 (fun _ _ => rfl)
  obtain ⟨C, Dw, hC⟩ := h 1 (fun _ => O) t ht
  set f := ContinuumNontrivial.cubeTest t ℓ with hfdef
  set Rf := |t| + |ℓ| with hRf
  have hf : IsTest f.1 Rf 1 := ContinuumNontrivial.isTest_cubeTest t ℓ
  refine ⟨max C 0 * (1 * (2 * Rf + 3) ^ 4) ^ 2, mul_nonneg (le_max_right _ _) (sq_nonneg _), ?_⟩
  obtain ⟨S, hS⟩ := O.2.1
  obtain ⟨D, hD⟩ := exists_depth 0 S
  obtain ⟨D', hD'⟩ := PeriodicState.exists_depth_bound 0 0 S
  have ht1 : Tendsto (fun k => dySpacing N k * (D : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_dySpacing N).mul_const (D : ℝ)
  have hM2 : 2 * (t + ℓ) < M₀ * AsymptoticScaling.aRun N 1 := by linarith
  filter_upwards [hC, ht1.eventually (gt_mem_nhds ht),
    TorusRefPosProof.eventually_height_le hN (by linarith) hM2 D',
    (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos),
    FieldDomination.refReadingAlong_eventually_nonneg hN βs O (t := s₀) (ℓ := s₀) hs₀,
    TorusRefPosProof.eventually_height_le hN (t := 4 * t) (ℓ := 4 * ℓ) (by linarith) (by linarith)
      (4 * Dw)]
    with k hk hkD hdk hk1 hR0 hwk
  have ha : 0 < dySpacing N k := dySpacing_pos (one_le_of_ne_zero hN) k
  set a := dySpacing N k with ha_def
  set G : C(Cfg N, ℝ) := (O.sub (ρ.c k O)).1 with hG
  have hcube : ∀ y, f.1 y ≠ 0 → ∀ μ, t ≤ y μ ∧ y μ ≤ t + ℓ := by
    intro y hy
    have hy' : ContinuumNontrivial.cubeInd t ℓ y ≠ 0 := hy
    exact Set.mem_of_indicator_ne_zero hy'
  set S' : Finset ISite := (box ⌈Rf / a⌉₊).filter (fun x => f.1 (site a x) ≠ 0) with hS'
  have hYQ : ∀ x : ISite, ContinuumCluster.Yv ρ k (ptMono (fun _ : Fin 1 => O) (fun _ => site a x))
      = smear a G (ptTest (site a x)) := by
    intro x
    show (∏ _i : Fin 1, (1 : ℝ)) • (∏ _i : Fin 1, smear a G (ptTest (site a x))) = _
    simp
  have hYP : ContinuumCluster.Yv ρ k (refMono O t ℓ) = smear a G f := by
    show (∏ _i : Fin 1, (1 : ℝ)) • (∏ _i : Fin 1, smear a G f) = _
    simp
  have hexp : smear a G f = ∑ x ∈ S', f.1 (site a x) • smear a G (ptTest (site a x)) := by
    rw [smear_eq_sum_pt ha G f hf]
    exact (Finset.sum_filter_of_ne (p := fun x => f.1 (site a x) ≠ 0)
      (fun x _ hne h0 => hne (by rw [h0, zero_smul]))).symm
  -- every point field lies in the slab
  have hmem : ∀ x ∈ S', smear a G (ptTest (site a x)) ∈ slabSub (N := N) (M₀ * 2 ^ k) := by
    intro x hx
    have hx0 : f.1 (site a x) ≠ 0 := (Finset.mem_filter.mp hx).2
    have hKc : t + ℓ ≤ a * (⌈(t + ℓ) / a⌉₊ : ℝ) := by
      have h := Nat.le_ceil ((t + ℓ) / a)
      rw [div_le_iff₀ ha] at h
      linarith
    obtain ⟨T, hT, hloc, hdepth⟩ := TorusRefPosProof.smear_local_slab (D := D) (D' := D')
      (K := ⌈(t + ℓ) / a⌉₊) ha (isLocalOn_sub_const hS (ρ.c k O)) hD
      (fun l hl => by have := hD' l hl; omega) hkD.le hKc (ptTest (site a x))
      (fun y hy => by rw [eq_of_ptTest_ne hy]; exact hcube _ hx0 0)
    exact ⟨T, hT, hloc, fun l hl => le_trans (hdepth l hl) (by exact_mod_cast hdk)⟩
  -- every point of the cube lies in the window
  have hwin : ∀ x ∈ S', ∀ μ, 4 * (|x μ| + (Dw : ℤ)) ≤ ((M₀ * 2 ^ k : ℕ) : ℤ) := by
    intro x hx μ
    have hc := hcube _ (Finset.mem_filter.mp hx).2 μ
    have hc1 : t ≤ a * (x μ : ℝ) := hc.1
    have hc2 : a * (x μ : ℝ) ≤ t + ℓ := hc.2
    have hpos : (0 : ℝ) ≤ x μ := (pos_of_mul_pos_right (by linarith : 0 < a * (x μ : ℝ)) ha.le).le
    have h2 : 4 * (x μ : ℝ) ≤ (4 * t + 4 * ℓ) / a := by
      rw [le_div_iff₀ ha]
      nlinarith
    have h3 : 4 * (x μ : ℝ) ≤ ((⌈(4 * t + 4 * ℓ) / a⌉₊ : ℕ) : ℝ) := h2.trans (Nat.le_ceil _)
    have hz : 4 * x μ ≤ ((⌈(4 * t + 4 * ℓ) / a⌉₊ : ℕ) : ℤ) := by exact_mod_cast h3
    have hxz : (0 : ℤ) ≤ x μ := by exact_mod_cast hpos
    have hwk' : ((⌈(4 * t + 4 * ℓ) / a⌉₊ + 4 * Dw : ℕ) : ℤ) ≤ ((M₀ * 2 ^ k : ℕ) : ℤ) := by
      exact_mod_cast hwk
    rw [abs_of_nonneg hxz]
    push_cast at hwk' ⊢
    linarith
  -- the reflection form on the cube points
  let B := slabForm hN (M₀ * 2 ^ k) (βs k)
  let y : ↥S' → ↥(slabSub (N := N) (M₀ * 2 ^ k)) := fun x =>
    ⟨smear a G (ptTest (site a x.1)), hmem x.1 x.2⟩
  let cf : ISite → ℝ := fun x => f.1 (site a x)
  have hsum : ((∑ x : ↥S', cf x.1 • y x : ↥(slabSub (N := N) (M₀ * 2 ^ k))) : C(Cfg N, ℝ))
      = smear a G f := by
    rw [Submodule.coe_sum, hexp, ← Finset.sum_coe_sort S']
    rfl
  have hlat : latSkRS (stateT hN M₀) ρ k (pairFam 0 (refMono O t ℓ) (refMono O t ℓ))
      = B.form (∑ x : ↥S', cf x.1 • y x) (∑ x : ↥S', cf x.1 • y x) := by
    rw [TorusRefPosProof.latSkRS_pairFam_eq hN _ ρ 0 hR k, hYP]
    show _ = PeriodicState.torusState hN (2 * (M₀ * 2 ^ k) + 1) (βs k)
      (LatticeReflection.ireflObs 0 0
        ((∑ x : ↥S', cf x.1 • y x : ↥(slabSub (N := N) (M₀ * 2 ^ k))) : C(Cfg N, ℝ))
        * ((∑ x : ↥S', cf x.1 • y x : ↥(slabSub (N := N) (M₀ * 2 ^ k))) : C(Cfg N, ℝ)))
    rw [hsum]
    rfl
  -- the point bound
  have hpt : ∀ x : ↥S', B.form (y x) (y x)
      ≤ max C 0 * a ^ 8 * refReadingAlong hN βs O s₀ s₀ k := by
    intro x
    have e : B.form (y x) (y x)
        = latSkRS (ApertureNearAll.torusAlong hN βs (M₀ * 2 ^ k)) ρ k
          (pairFam 0 (ptMono (fun _ : Fin 1 => O) (fun _ => site a x.1))
            (ptMono (fun _ : Fin 1 => O) (fun _ => site a x.1))) := by
      rw [TorusRefPosProof.latSkRS_pairFam_eq hN _ ρ 0 hR k, hYQ]
      rfl
    rw [e]
    have hsep : ContinuumSep.sepPos 0 t (ptMono (fun _ : Fin 1 => O) (fun _ => site a x.1)) := by
      refine ⟨fun i z hz => ?_, fun i j hij => absurd (Subsingleton.elim (α := Fin 1) i j) hij⟩
      rw [eq_of_ptTest_ne hz]
      exact (hcube _ (Finset.mem_filter.mp x.2).2 0).1
    have hb := hk (M₀ * 2 ^ k) le_rfl (fun _ => x.1) (fun _ μ => hwin x.1 x.2 μ) hsep
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, mul_one] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg ha.le _)) hR0
  have hcf : ∀ x, cf x ^ 2 ≤ 1 := by
    intro x
    have h1 : |cf x| ≤ 1 := hf.2.1 _
    rw [← sq_abs]
    nlinarith [abs_nonneg (cf x)]
  have hterm : ∀ x : ↥S', B.form (cf x.1 • y x) (cf x.1 • y x)
      ≤ max C 0 * a ^ 8 * refReadingAlong hN βs O s₀ s₀ k := by
    intro x
    have e : B.form (cf x.1 • y x) (cf x.1 • y x) = cf x.1 ^ 2 * B.form (y x) (y x) := by
      rw [B.toPreForm.form_smul_left, B.toPreForm.form_smul_right]
      ring
    rw [e]
    have h0 : 0 ≤ B.form (y x) (y x) := B.form_nonneg _
    nlinarith [hcf x.1, hpt x, sq_nonneg (cf x.1)]
  -- counting the points
  have hcard : (S'.card : ℝ) * a ^ 4 ≤ (2 * Rf + 3) ^ 4 := by
    have h1 : (S'.card : ℝ) ≤ (2 * (⌈Rf / a⌉₊ : ℝ) + 1) ^ 4 := by
      have : S'.card ≤ (2 * ⌈Rf / a⌉₊ + 1) ^ 4 :=
        (Finset.card_filter_le _ _).trans (card_box _).le
      exact_mod_cast this
    have hRf0 : 0 ≤ Rf := by positivity
    have h2 := mul_box_side_le ha hk1.le hRf0
    calc (S'.card : ℝ) * a ^ 4 ≤ (2 * (⌈Rf / a⌉₊ : ℝ) + 1) ^ 4 * a ^ 4 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (a * (2 * (⌈Rf / a⌉₊ : ℝ) + 1)) ^ 4 := by ring
      _ ≤ (2 * Rf + 3) ^ 4 := pow_le_pow_left₀ (by positivity) h2 4
  -- assembling
  rw [hlat]
  refine (form_finset_sum_le B Finset.univ (fun x => cf x.1 • y x)).trans ?_
  rw [Finset.card_univ, Fintype.card_coe]
  have hsumle : ∑ x ∈ (Finset.univ : Finset ↥S'), B.form (cf x.1 • y x) (cf x.1 • y x)
      ≤ (S'.card : ℝ) * (max C 0 * a ^ 8 * refReadingAlong hN βs O s₀ s₀ k) := by
    refine (Finset.sum_le_sum (fun x _ => hterm x)).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  have hK0 : 0 ≤ max C 0 * refReadingAlong hN βs O s₀ s₀ k := mul_nonneg (le_max_right _ _) hR0
  have hsq : ((S'.card : ℝ) * a ^ 4) ^ 2 ≤ ((2 * Rf + 3) ^ 4) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ha.le _)) hcard 2
  calc (S'.card : ℝ) * ∑ x ∈ (Finset.univ : Finset ↥S'), B.form (cf x.1 • y x) (cf x.1 • y x)
      ≤ (S'.card : ℝ) * ((S'.card : ℝ) * (max C 0 * a ^ 8 * refReadingAlong hN βs O s₀ s₀ k)) :=
        mul_le_mul_of_nonneg_left hsumle (Nat.cast_nonneg _)
    _ = (max C 0 * refReadingAlong hN βs O s₀ s₀ k) * ((S'.card : ℝ) * a ^ 4) ^ 2 := by ring
    _ ≤ (max C 0 * refReadingAlong hN βs O s₀ s₀ k) * ((2 * Rf + 3) ^ 4) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hK0
    _ = max C 0 * (1 * (2 * Rf + 3) ^ 4) ^ 2 * refReadingAlong hN βs O s₀ s₀ k := by ring

/-- **The volume clause from the windowed near bound.** -/
theorem refPassageLow_of_nearWin (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {M₀ : ℕ} {s₀ : ℝ}
    (hs₀ : 0 < s₀) (h8 : 8 * (s₀ + s₀) < M₀ * AsymptoticScaling.aRun N 1)
    (h : NearWin hN (dyBeta (one_le_of_ne_zero hN)) M₀ s₀) :
    ∃ c : ℝ, 0 < c ∧ PassageLow.RefPassageLow hN M₀ O s₀ s₀ c := by
  obtain ⟨C, hC0, hC⟩ := vacReading_le_of_nearWin hN O hs₀ hs₀.le hs₀ h8 h
  have hc : (0 : ℝ) < 1 / (C + 1) := by positivity
  refine ⟨1 / (C + 1), hc, ?_⟩
  filter_upwards [hC, FieldDomination.refReadingAlong_eventually_nonneg hN
    (dyBeta (one_le_of_ne_zero hN)) O (t := s₀) (ℓ := s₀) hs₀] with k hk hR0
  have hle := (refReadingS_le_vac hN M₀ O s₀ s₀ k).trans hk
  show 1 / (C + 1) * refReadingS (stateT hN M₀) O s₀ s₀ k
    ≤ refReadingAlong hN (dyBeta (one_le_of_ne_zero hN)) O s₀ s₀ k
  calc 1 / (C + 1) * refReadingS (stateT hN M₀) O s₀ s₀ k
      ≤ 1 / (C + 1) * (C * refReadingAlong hN (dyBeta (one_le_of_ne_zero hN)) O s₀ s₀ k) :=
        mul_le_mul_of_nonneg_left hle hc.le
    _ ≤ refReadingAlong hN (dyBeta (one_le_of_ne_zero hN)) O s₀ s₀ k := by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith)]
        nlinarith

end Cube

/-! ## 5. The capstone with two inputs -/

section Capstone

/-- **The pinned path at `zOwn` from one near and one far statement.** -/
theorem clay_two (hN : (2 : ℕ) ≠ 0) {M₀ : ℕ} {s₀ L : ℝ} (hs₀ : 0 < s₀)
    (h8 : 8 * (s₀ + s₀) < M₀ * AsymptoticScaling.aRun 2 1) (hL : 0 < L)
    (hNear : NearWin hN (dyBeta (one_le_of_ne_zero hN)) M₀ s₀)
    (hW : ApertureBridge.PhysDefect L (1 / 1000)) :
    ∃ hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduceOwn.zOwn hN s₀ s₀)) 0,
      ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧
        ClayRoutes.ClayContinuumPair hN (ExistenceReduceOwn.zOwn hN s₀ s₀) 0
          (ExistenceReduceOwn.zOwn_refl hN s₀ s₀)
          (ContinuumSep.pairBoundSep_of_diagBoundSep hN
            (Renorm.connected hN (ExistenceReduceOwn.zOwn hN s₀ s₀)) 0
            (Renorm.connected_reflCompat hN (ExistenceReduceOwn.zOwn hN s₀ s₀) 0
              (ExistenceReduceOwn.zOwn_refl hN s₀ s₀)) hD) (5 * ℓ₀) :=
  ApertureFinal.clay_final hN hs₀ (by linarith) hL (nearOwn_of_nearWin hN _ hNear)
    (refPassageLow_of_nearWin hN _ hs₀ h8 hNear) hW

/-- **The capstone with the far input as four slice doublings**, `Far L (1/15000)`. -/
theorem clay_two_far (hN : (2 : ℕ) ≠ 0) {M₀ : ℕ} {s₀ L : ℝ} (hs₀ : 0 < s₀)
    (h8 : 8 * (s₀ + s₀) < M₀ * AsymptoticScaling.aRun 2 1) (hL : 0 < L)
    (hNear : NearWin hN (dyBeta (one_le_of_ne_zero hN)) M₀ s₀)
    (hF : ApertureNearAll.Far L (1 / 15000)) :
    ∃ hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduceOwn.zOwn hN s₀ s₀)) 0,
      ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧
        ClayRoutes.ClayContinuumPair hN (ExistenceReduceOwn.zOwn hN s₀ s₀) 0
          (ExistenceReduceOwn.zOwn_refl hN s₀ s₀)
          (ContinuumSep.pairBoundSep_of_diagBoundSep hN
            (Renorm.connected hN (ExistenceReduceOwn.zOwn hN s₀ s₀)) 0
            (Renorm.connected_reflCompat hN (ExistenceReduceOwn.zOwn hN s₀ s₀) 0
              (ExistenceReduceOwn.zOwn_refl hN s₀ s₀)) hD) (5 * ℓ₀) := by
  have hW := ApertureNearAll.physDefect_of_far hF
  rw [show (15 : ℝ) * (1 / 15000) = 1 / 1000 by norm_num] at hW
  exact clay_two hN hs₀ h8 hL hNear hW

end Capstone

end MassGap.ApertureVolume

end

#print axioms MassGap.ApertureVolume.nearWin_of_nearAll
#print axioms MassGap.ApertureVolume.nearAllW_of_nearWin
#print axioms MassGap.ApertureVolume.nearOwn_of_nearWin
#print axioms MassGap.ApertureVolume.refl_sq_shift
#print axioms MassGap.ApertureVolume.own_le_const
#print axioms MassGap.ApertureVolume.refReadingS_le_vac
#print axioms MassGap.ApertureVolume.slab_reflPositive
#print axioms MassGap.ApertureVolume.vacReading_le_of_nearWin
#print axioms MassGap.ApertureVolume.refPassageLow_of_nearWin
#print axioms MassGap.ApertureVolume.clay_two
#print axioms MassGap.ApertureVolume.clay_two_far
