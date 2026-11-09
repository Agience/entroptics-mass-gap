import Mathlib
import MassGap.TorusPassageProof
import MassGap.PeriodicState
import MassGap.ReflectionStrong

noncomputable section

/-!
# MassGap.TorusRefPosProof — the torus reference reading is a reflection square, nonnegative

`TorusCapstone.TorusRefPos hN M₀ O t ℓ` asks `0 < refReadingS (stateT hN M₀) O t ℓ k` eventually.
This module proves the nonnegative half and reduces the strict inequality to non-vanishing.

* `connectedS_reflCompat`: the connected renormalisation in a per-step state `σ` is reflection
  compatible when every `σ k` is invariant under the site reflection about `x_τ = 0`.
* `latSkRS_pairFam_eq`: in any per-step state, with reflection-compatible data,
  `latSkRS σ ρ k (θP ∪ Q) = σ k (θ Y_P · Y_Q)`, `Y = Yv ρ k`.
* `refReadingS_stateT_eq`: the torus reference reading is `stateT k (θY_k · Y_k)` with
  `Y_k = Yv (connectedS (stateT hN M₀) 1) k (refMono O t ℓ)`, the cube-smeared connected field.
* `smear_local_slab`: a field local on `S`, smeared at spacing `a` against a test function supported
  in times `[δ, δ']`, is local on a finite set of links lying in `x₀ ≥ 0` (once `a·D ≤ δ`, `D` the
  depth of `S` below the plane) and below `x₀ = K + D'` (once `δ' ≤ a·K`, `D'` the height of `S`).
* `torusState_refl_mul_nonneg`: on the torus of extent `2(M + 1)`, an observable local on links in
  `0 ≤ x₀ ≤ M` has `0 ≤ torusState (θY · Y)` (`ReflectionStrong.wilson_expect_nonneg_module` through
  `PeriodicState.torusObs_mem_localObs_even` at `p = 0`).
* `torusRefReading_nonneg`: for `0 < t`, `0 ≤ ℓ` and `2(t + ℓ) < M₀ · aRun N 1` (the cube lies
  within the half physical side), eventually `0 ≤ refReadingS (stateT hN M₀) O t ℓ k`, for every
  field `O`. The support of `Y_k` reaches `(t + ℓ)/a_k = 2ᵏ⁺¹(t + ℓ)/aRun N 1` above the plane, the
  half-extent is `M₀ 2ᵏ + 1`, and the gap `2ᵏ(M₀ − 2(t + ℓ)/aRun N 1)` grows past the fixed height of
  `O`'s support.
* `torusRefPos_iff_ne`: under the same conditions, `TorusRefPos hN M₀ O t ℓ` is eventual
  non-vanishing of the reading.
* `clay_canonical_refPassage_ne`: `TorusPassageProof.clay_canonical_refPassage` with `TorusRefPos`
  replaced by eventual non-vanishing of the torus reading.

What remains for `TorusRefPos` is the non-vanishing `refReadingS (stateT hN M₀) O t ℓ k ≠ 0`
eventually, at `O = planePlaq N`: one finite-dimensional statement per step (a Wilson expectation on
one finite torus of a continuous function of finitely many links). It is not proved here.
-/

namespace MassGap.TorusRefPosProof

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.TorusCapstone Filter
open scoped Topology

variable {N : ℕ}

/-! ## 1. The reading is a reflection pairing in any per-step state -/

section Generic

/-- The connected renormalisation in `σ` is reflection compatible when every `σ k` is reflection
invariant about `x_τ = 0`. -/
theorem connectedS_reflCompat (σ : ℕ → MassGap.DLRLimit.State (Cfg N))
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hσ : ∀ k, MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ 0) (σ k)) :
    (connectedS σ Z).ReflCompat τ :=
  fun k O => ⟨hZ k O, hσ k O.1⟩

/-- **A reflected renormalised reading in any per-step state is a reflection pairing of vectors.** -/
theorem latSkRS_pairFam_eq (hN : N ≠ 0) (σ : ℕ → MassGap.DLRLimit.State (Cfg N)) (ρ : Renorm N)
    (τ : Fin 4) (hR : ρ.ReflCompat τ) (k : ℕ) (P Q : Mono N) :
    latSkRS σ ρ k (pairFam τ P Q)
      = σ k (LatticeReflection.ireflObs τ 0 (ContinuumCluster.Yv ρ k P)
          * ContinuumCluster.Yv ρ k Q) := by
  have hfam : (fun x => ρ.field k (pairFam τ P Q x)) = pairFam τ (ρ.mono k P) (ρ.mono k Q) := by
    funext x
    cases x with
    | inl i =>
      show (((P.2 i).1.refl τ).sub (ρ.c k ((P.2 i).1.refl τ)), (P.2 i).2.reflect τ)
        = (((P.2 i).1.sub (ρ.c k (P.2 i).1)).refl τ, (P.2 i).2.reflect τ)
      rw [(hR k (P.2 i).1).2, LField.refl_sub]
    | inr j => rfl
  have hpref : ρ.pref k (pairFam τ P Q) = ρ.zmono k P * ρ.zmono k Q := by
    show (∏ x : Fin P.1 ⊕ Fin Q.1, ρ.Z k (pairFam τ P Q x).1)
      = (∏ i, ρ.Z k (P.2 i).1) * ∏ j, ρ.Z k (Q.2 j).1
    rw [Fintype.prod_sum_type]
    have h1 : (∏ i, ρ.Z k (pairFam τ P Q (Sum.inl i)).1) = ∏ i, ρ.Z k (P.2 i).1 :=
      Finset.prod_congr rfl (fun i _ => (hR k (P.2 i).1).1)
    exact congrArg (fun t => t * ∏ j, ρ.Z k (Q.2 j).1) h1
  show ρ.pref k (pairFam τ P Q) * latS (σ k) (dySpacing N k)
      (fun x => ρ.field k (pairFam τ P Q x)) = _
  rw [hpref, hfam, latS_pairFam _ (dySpacing_pos (one_le_of_ne_zero hN) k)]
  unfold ContinuumCluster.Yv
  rw [map_smul, smul_mul_smul_comm, (σ k).map_smul]

/-- **The torus reference reading is `stateT k (θY_k · Y_k)`.** -/
theorem refReadingS_stateT_eq (hN : N ≠ 0) (M₀ : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (k : ℕ) :
    refReadingS (stateT hN M₀) O t ℓ k
      = stateT hN M₀ k (LatticeReflection.ireflObs 0 0
            (ContinuumCluster.Yv (connectedS (stateT hN M₀) (fun _ _ => 1)) k
              (ExistenceReduce.refMono O t ℓ))
          * ContinuumCluster.Yv (connectedS (stateT hN M₀) (fun _ _ => 1)) k
              (ExistenceReduce.refMono O t ℓ)) :=
  latSkRS_pairFam_eq hN (stateT hN M₀) _ 0
    (connectedS_reflCompat _ _ 0 (fun _ _ => rfl) (fun k => stateT_reflInvariant hN M₀ k 0 0)) k
    _ _

end Generic

/-! ## 2. The support of a smeared field lies in a slab -/

section Slab

/-- **A smeared field reads a slab.** -/
theorem smear_local_slab {a : ℝ} (ha : 0 < a) {F : C(Cfg N, ℝ)} {S : Finset ILink}
    (hS : IsLocalOn S (F : Cfg N → ℝ)) {D D' K : ℕ}
    (hD : ∀ l ∈ S, -(l.2 0) ≤ (D : ℤ)) (hD' : ∀ l ∈ S, l.2 0 ≤ (D' : ℤ))
    {δ δ' : ℝ} (haD : a * D ≤ δ) (hK : δ' ≤ a * K) (f : TestFn)
    (hδ : ∀ y, f.1 y ≠ 0 → δ ≤ y 0 ∧ y 0 ≤ δ') :
    ∃ T : Finset ILink, (↑T ⊆ HalfSpaceAlgebra.posHalf 0 0)
      ∧ IsLocalOn T (smear a F f : Cfg N → ℝ) ∧ ∀ l ∈ T, l.2 0 ≤ ((K + D' : ℕ) : ℤ) := by
  obtain ⟨R, M, hf⟩ := f.2
  set B := (box ⌈R / a⌉₊).filter (fun x => f.1 (site a x) ≠ 0) with hB
  have hlo : ∀ x ∈ B, (D : ℤ) ≤ x 0 := by
    intro x hx
    have hx0 : f.1 (site a x) ≠ 0 := (Finset.mem_filter.mp hx).2
    have h1 : δ ≤ a * (x 0 : ℝ) := (hδ _ hx0).1
    have h2 : (D : ℝ) ≤ (x 0 : ℝ) := by
      rcases le_or_gt (D : ℝ) (x 0 : ℝ) with h | hlt
      · exact h
      · have := mul_lt_mul_of_pos_left hlt ha
        linarith
    exact_mod_cast h2
  have hhi : ∀ x ∈ B, x 0 ≤ (K : ℤ) := by
    intro x hx
    have hx0 : f.1 (site a x) ≠ 0 := (Finset.mem_filter.mp hx).2
    have h1 : a * (x 0 : ℝ) ≤ δ' := (hδ _ hx0).2
    have h2 : (x 0 : ℝ) ≤ (K : ℝ) := by
      rcases le_or_gt (x 0 : ℝ) (K : ℝ) with h | hlt
      · exact h
      · have := mul_lt_mul_of_pos_left hlt ha
        linarith
    exact_mod_cast h2
  refine ⟨B.biUnion (fun x => S.image (fun l : ILink => (l.1, l.2 + x))), ?_, ?_, ?_⟩
  · intro l hl
    obtain ⟨x, hx, hlx⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hl)
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hlx
    have h3 := hlo x hx
    have h4 := hD m hm
    show (0 : ℤ) ≤ (m.2 + x) 0
    rw [Pi.add_apply]
    omega
  · intro U V h
    rw [smear_eq_sum ha F f hf (Finset.Subset.refl _)]
    simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    by_cases h0 : f.1 (site a x) = 0
    · rw [h0, mul_zero, zero_mul, zero_mul]
    · congr 1
      exact isLocalOn_transObs hS x U V (fun l hl =>
        h l (Finset.mem_biUnion.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, h0⟩, hl⟩))
  · intro l hl
    obtain ⟨x, hx, hlx⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hlx
    have h3 := hhi x hx
    have h4 := hD' m hm
    show (m.2 + x) 0 ≤ ((K + D' : ℕ) : ℤ)
    rw [Pi.add_apply]
    push_cast
    omega

end Slab

/-! ## 3. Reflection positivity on the torus at the plane `x₀ = 0` -/

section TorusRP

/-- **Site-reflection positivity on one torus, at a stated depth.** -/
theorem torusState_refl_mul_nonneg (hN : N ≠ 0) (M : ℕ) (β : ℝ) (Y : C(Cfg N, ℝ))
    (T : Finset ILink) (hT : ↑T ⊆ HalfSpaceAlgebra.posHalf 0 0)
    (hloc : IsLocalOn T (Y : Cfg N → ℝ)) (hk : ∀ l ∈ T, l.2 0 ≤ (M : ℤ)) :
    0 ≤ PeriodicState.torusState hN (2 * M + 1) β (LatticeReflection.ireflObs 0 0 Y * Y) := by
  have hkS : ∀ l ∈ T, l.2 0 - 0 ≤ (M : ℤ) := fun l hl => by
    have := hk l hl
    omega
  have hrp := MassGap.ReflectionStrong.wilson_expect_nonneg_module hN (0 : Fin 4)
    (finMod (2 * M + 1) 0) (M + 1) (by omega) (by omega) β
    (PeriodicState.torusObs_mem_localObs_even M 0 0 Y T hT hloc hkS)
  have ha : finMod (2 * M + 1) (0 : ℤ) = finMod (2 * M + 1) 0 + finMod (2 * M + 1) 0 := by
    have h := PeriodicState.finMod_add (2 * M + 1) 0 0
    rwa [add_zero] at h
  show 0 ≤ MassGap.ReflectPositive.EW (d := 4) (n := 2 * M + 1 + 1) N β
    (PeriodicState.torusObs (2 * M + 1)
      ((MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) 0 0).θ Y * Y))
  rw [PeriodicState.torusObs_refl_mul, ha]
  exact hrp

end TorusRP

/-! ## 4. The torus reference reading is eventually nonnegative -/

section Nonneg

/-- The depth condition: eventually the cube's lattice height plus the field's height fits in the
half-extent. -/
theorem eventually_height_le (hN : N ≠ 0) {M₀ : ℕ} {t ℓ : ℝ} (htl : 0 ≤ t + ℓ)
    (hM : 2 * (t + ℓ) < M₀ * AsymptoticScaling.aRun N 1) (D' : ℕ) :
    ∀ᶠ k in atTop, ⌈(t + ℓ) / dySpacing N k⌉₊ + D' ≤ M₀ * 2 ^ k := by
  set A := AsymptoticScaling.aRun N 1 with hAdef
  have hA : 0 < A := by
    have h := dySpacing_pos (one_le_of_ne_zero hN) 0
    unfold dySpacing at h
    have h2 : (0 : ℝ) < 2 ^ (0 + 1) := by positivity
    exact (div_pos_iff_of_pos_right h2).mp h
  have hc : 0 < (M₀ : ℝ) - 2 * (t + ℓ) / A := by
    have : 2 * (t + ℓ) / A < M₀ := (div_lt_iff₀ hA).mpr hM
    linarith
  have hT : Tendsto (fun k : ℕ => (2 : ℝ) ^ k * ((M₀ : ℝ) - 2 * (t + ℓ) / A)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).atTop_mul_const hc
  filter_upwards [hT.eventually_ge_atTop ((D' : ℝ) + 1)] with k hk
  have hx : (t + ℓ) / dySpacing N k = 2 ^ k * (2 * (t + ℓ) / A) := by
    unfold dySpacing
    rw [← hAdef]
    field_simp
    ring
  have hceil : (⌈(t + ℓ) / dySpacing N k⌉₊ : ℝ) < (t + ℓ) / dySpacing N k + 1 :=
    Nat.ceil_lt_add_one (div_nonneg htl (dySpacing_pos (one_le_of_ne_zero hN) k).le)
  have e : (2 : ℝ) ^ k * ((M₀ : ℝ) - 2 * (t + ℓ) / A)
      = (M₀ : ℝ) * 2 ^ k - 2 ^ k * (2 * (t + ℓ) / A) := by ring
  have hR : ((⌈(t + ℓ) / dySpacing N k⌉₊ + D' : ℕ) : ℝ) ≤ ((M₀ * 2 ^ k : ℕ) : ℝ) := by
    rw [hx] at hceil ⊢
    push_cast
    linarith
  exact_mod_cast hR

/-- **The torus reference reading is eventually nonnegative**, for every field, once the cube lies
within the half physical side. -/
theorem torusRefReading_nonneg (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {M₀ : ℕ} {t ℓ : ℝ}
    (ht : 0 < t) (hℓ : 0 ≤ ℓ) (hM : 2 * (t + ℓ) < M₀ * AsymptoticScaling.aRun N 1) :
    ∀ᶠ k in atTop, 0 ≤ refReadingS (stateT hN M₀) O t ℓ k := by
  obtain ⟨S, hS⟩ := O.2.1
  obtain ⟨D, hD⟩ := exists_depth 0 S
  obtain ⟨D', hD'⟩ := PeriodicState.exists_depth_bound 0 0 S
  have ht1 : Tendsto (fun k => dySpacing N k * (D : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_dySpacing N).mul_const (D : ℝ)
  filter_upwards [ht1.eventually (gt_mem_nhds ht),
    eventually_height_le hN (by linarith) hM D'] with k hk hdk
  have ha : 0 < dySpacing N k := dySpacing_pos (one_le_of_ne_zero hN) k
  have hK : t + ℓ ≤ dySpacing N k * (⌈(t + ℓ) / dySpacing N k⌉₊ : ℝ) := by
    have h := Nat.le_ceil ((t + ℓ) / dySpacing N k)
    rw [div_le_iff₀ ha] at h
    linarith
  have hcube : ∀ y, (ContinuumNontrivial.cubeTest t ℓ).1 y ≠ 0 → t ≤ y 0 ∧ y 0 ≤ t + ℓ := by
    intro y hy
    have hy' : ContinuumNontrivial.cubeInd t ℓ y ≠ 0 := hy
    have hmem : y ∈ ContinuumNontrivial.timeCube t ℓ := Set.mem_of_indicator_ne_zero hy'
    exact hmem 0
  set c := stateT hN M₀ k O.1 with hc
  obtain ⟨T, hT, hloc, hdepth⟩ := smear_local_slab (D := D) (D' := D')
    (K := ⌈(t + ℓ) / dySpacing N k⌉₊) ha (isLocalOn_sub_const hS c) hD
    (fun l hl => by have := hD' l hl; omega) hk.le hK (ContinuumNontrivial.cubeTest t ℓ) hcube
  set Y := ContinuumCluster.Yv (connectedS (stateT hN M₀) (fun _ _ => 1)) k
    (ExistenceReduce.refMono O t ℓ) with hYdef
  have hY : Y = (connectedS (stateT hN M₀) (fun _ _ => (1 : ℝ))).zmono k
      (ExistenceReduce.refMono O t ℓ)
        • smear (dySpacing N k) (O.sub c).1 (ContinuumNontrivial.cubeTest t ℓ) := by
    show _ • (∏ _i : Fin 1, smear (dySpacing N k) (O.sub c).1 (ContinuumNontrivial.cubeTest t ℓ))
      = _
    rw [Fin.prod_univ_one]
  have hlocY : IsLocalOn T (Y : Cfg N → ℝ) := by
    intro U V h
    rw [hY, ContinuousMap.smul_apply, ContinuousMap.smul_apply]
    exact congrArg _ (hloc U V h)
  rw [refReadingS_stateT_eq]
  exact torusState_refl_mul_nonneg hN (M₀ * 2 ^ k) _ Y T hT hlocY
    (fun l hl => le_trans (hdepth l hl) (by exact_mod_cast hdk))

/-- **`TorusRefPos` is eventual non-vanishing of the torus reading**, under the cube condition. -/
theorem torusRefPos_iff_ne (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {M₀ : ℕ} {t ℓ : ℝ}
    (ht : 0 < t) (hℓ : 0 ≤ ℓ) (hM : 2 * (t + ℓ) < M₀ * AsymptoticScaling.aRun N 1) :
    TorusRefPos hN M₀ O t ℓ ↔ ∀ᶠ k in atTop, refReadingS (stateT hN M₀) O t ℓ k ≠ 0 := by
  constructor
  · intro h
    filter_upwards [h] with k hk
    exact hk.ne'
  · intro h
    filter_upwards [h, torusRefReading_nonneg hN O ht hℓ hM] with k hk hk0
    exact lt_of_le_of_ne hk0 (Ne.symm hk)

/-- **The pinned path with the torus input reduced to non-vanishing.**
`TorusPassageProof.clay_canonical_refPassage` with `TorusRefPos` replaced by eventual
`refReadingS (stateT hN M₀) O t ℓ k ≠ 0`, at `0 ≤ ℓ` and `2(t + ℓ) < M₀ · aRun N 1`. -/
theorem clay_canonical_refPassage_ne (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N))
    {t ℓ : ℝ} (ht : 0 < t) (hℓ : 0 ≤ ℓ) {M₀ : ℕ}
    (hM : 2 * (t + ℓ) < M₀ * AsymptoticScaling.aRun N 1)
    (hne : ∀ᶠ k in atTop, refReadingS (stateT hN M₀) O t ℓ k ≠ 0) {ε : ℝ} (hε : ε < 1)
    (hR : TorusPassageProof.RefPassage hN M₀ O t ℓ ε)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0)
    {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN O t ℓ) 0
      (ExistenceReduce.zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN
        (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (ExistenceReduce.zCan hN O t ℓ) 0
          (ExistenceReduce.zCan_refl hN O t ℓ)) hD) (5 * ℓ₀) :=
  TorusPassageProof.clay_canonical_refPassage hN2 hN O ht
    ((torusRefPos_iff_ne hN O ht hℓ hM).mpr hne) hε hR hD hℓ₀ hW

end Nonneg

end MassGap.TorusRefPosProof

#print axioms MassGap.TorusRefPosProof.connectedS_reflCompat
#print axioms MassGap.TorusRefPosProof.latSkRS_pairFam_eq
#print axioms MassGap.TorusRefPosProof.refReadingS_stateT_eq
#print axioms MassGap.TorusRefPosProof.smear_local_slab
#print axioms MassGap.TorusRefPosProof.torusState_refl_mul_nonneg
#print axioms MassGap.TorusRefPosProof.eventually_height_le
#print axioms MassGap.TorusRefPosProof.torusRefReading_nonneg
#print axioms MassGap.TorusRefPosProof.torusRefPos_iff_ne
#print axioms MassGap.TorusRefPosProof.clay_canonical_refPassage_ne
