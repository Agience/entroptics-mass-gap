import Mathlib
import MassGap.PairCorr
import MassGap.PairInterface
import MassGap.PairCount

noncomputable section

/-!
# MassGap.PairWeight — the Wilson fibre weight of two links is a tilted bilinear exponential

## What it gives

`wt_fibre_eq`: on the periodic lattice of extent `M + 1 ≥ 2`, for `0 ≤ β`, `l ≠ m` and a frozen
configuration `W`, the Wilson weight of `W[m ↦ h][l ↦ g]` is
`fibreWeight (realFeature N) K T α γ h g = K e^{⟪X h, T X g⟫ + ⟪α, X h⟫ + ⟪γ, X g⟫}` with `K > 0`,
`‖T‖ ≤ β n2`, `‖α‖, ‖γ‖ ≤ β (12 − n2)`, `n2 = PairCount.n2 M l m`.

## The route

`wt = e^{−β pairLocSum} e^{−β pairRestSum}` (`PairCorr.wt_split_pair`); `pairRestSum` reads neither
link (`PairCorr.pairRestSum_update_l`, `_m`) and goes into `K`. In `pairLocSum`,
`wilsonDensity = 1 − Re tr/N`. A diagonal plaquette has holonomy `1` (`PairCount.wilsonHol_diag`)
and contributes a constant. A non-diagonal plaquette visits each link once
(`PairCount.nodup_nondiag`), so its word splits as `s ++ (k, o) :: t` at any visited link `k`
(`list_split`) and its holonomy is a product of frozen factors and the one or two free factors.
The trace is cyclic (`reTr_rot`, `Matrix.trace_mul_comm`), `Re tr(U D)/N = ⟪X U, X D⁻¹⟫`
(`PairInterface.reTr_mul_eq_inner`) and `Re tr(U⁻¹ C)/N = ⟪X U, X C⟫` (`reTr_inv_mul`, through
`PairInterface.exists_isometry_inv` and `LinearIsometry.inner_map_map`). So its `Re tr/N` is
`⟪v, X g⟫` with `‖v‖ ≤ 1` when it visits `l` only (`reTr_hol_single`), `⟪w, X h⟫` when it visits `m`
only, and `⟪X h, T_p X g⟫` with `‖T_p‖ ≤ 1` when it visits both (`reTr_hol_pair`, through
`PairInterface.exists_isometry_mul_left/right/inv`). Summing: `T = β Σ T_p` over the `n2` pair
plaquettes; `γ = β Σ v` over the plaquettes visiting `l` only, at most `12 − n2` of them
(`PairCount.card_visit_nondiag_le`); `α` likewise at `m` (`PairCount.n2_symm`).
-/

namespace MassGap.PairWeight

open MeasureTheory
open MassGap.SUN (SU)
open MassGap.HeatBath (wt bdT)
open MassGap.WilsonLattice (wilsonHol)
open MassGap.WilsonAction (wilsonDensity)
open MassGap.PairInterface MassGap.PairCount

variable {N : ℕ}

/-! ## 1. Words that visit a link once -/

/-- A list whose first components have no repetition splits at any visited first component.

DERIVED: `1` in `Prod.fst` names the first projection. -/
private theorem list_split {α : Type} {w : List (α × Bool)} {k : α}
    (hnd : (w.map Prod.fst).Nodup) (hk : k ∈ w.map Prod.fst) :
    ∃ (o : Bool) (s t : List (α × Bool)), w = s ++ (k, o) :: t ∧
      k ∉ s.map Prod.fst ∧ k ∉ t.map Prod.fst := by
  obtain ⟨⟨k', o⟩, he, hek⟩ := List.mem_map.mp hk
  have hkk : k' = k := hek
  obtain ⟨s, t, hst⟩ := List.append_of_mem he
  have hnd' : (s.map Prod.fst ++ k :: t.map Prod.fst).Nodup := by
    rw [hst, List.map_append, List.map_cons, hkk] at hnd
    exact hnd
  obtain ⟨-, hnt, hdis⟩ := List.nodup_append.mp hnd'
  refine ⟨o, s, t, ?_, ?_, ?_⟩
  · rw [hst, hkk]
  · intro hs
    exact hdis k hs k (List.mem_cons.mpr (Or.inl rfl)) rfl
  · exact (List.nodup_cons.mp hnt).1

/-- DERIVED: `1` in `e.1` is the first projection. -/
private theorem ne_of_mem_not {α : Type} {s : List (α × Bool)} {k : α}
    (hk : k ∉ s.map Prod.fst) {e : α × Bool} (he : e ∈ s) : e.1 ≠ k :=
  fun h => hk (List.mem_map.mpr ⟨e, he, h⟩)

/-- The ordered product of a word split at one entry.

DERIVED: no numeral. -/
private theorem prod_split_eq {G : Type} [Group G] {α : Type} (f : α × Bool → G)
    (s t : List (α × Bool)) (e : α × Bool) :
    ((s ++ e :: t).map f).prod = (s.map f).prod * f e * (t.map f).prod := by
  rw [List.map_append, List.map_cons, List.prod_append, List.prod_cons, mul_assoc]

/-- Two configurations agreeing on the links of a word give the same ordered product.

DERIVED: `1`, `2` in `lo.1`, `lo.2` are projections. -/
private theorem prod_congr_links {α G : Type} [Group G] (V W : α → G) (s : List (α × Bool))
    (h : ∀ e ∈ s, V e.1 = W e.1) :
    (s.map (fun lo : α × Bool => if lo.2 then V lo.1 else (V lo.1)⁻¹)).prod
      = (s.map (fun lo : α × Bool => if lo.2 then W lo.1 else (W lo.1)⁻¹)).prod := by
  congr 1
  apply List.map_congr_left
  intro lo hlo
  simp only [h lo hlo]

/-! ## 2. Traces of products in `SU(N)` -/

/-- **Cyclicity of the real trace**: `Re tr(XYZ) = Re tr(Y(ZX))`.

DERIVED: no numeral. -/
private theorem reTr_rot (X Y Z : SU N) :
    (Matrix.trace ((X * Y * Z : SU N) : Matrix (Fin N) (Fin N) ℂ)).re
      = (Matrix.trace ((Y * (Z * X) : SU N) : Matrix (Fin N) (Fin N) ℂ)).re := by
  have e1 : ((X * Y * Z : SU N) : Matrix (Fin N) (Fin N) ℂ)
      = (X : Matrix (Fin N) (Fin N) ℂ)
        * ((Y : Matrix (Fin N) (Fin N) ℂ) * (Z : Matrix (Fin N) (Fin N) ℂ)) := by
    show (X : Matrix (Fin N) (Fin N) ℂ) * (Y : Matrix (Fin N) (Fin N) ℂ)
        * (Z : Matrix (Fin N) (Fin N) ℂ) = _
    exact Matrix.mul_assoc _ _ _
  have e2 : ((Y * (Z * X) : SU N) : Matrix (Fin N) (Fin N) ℂ)
      = ((Y : Matrix (Fin N) (Fin N) ℂ) * (Z : Matrix (Fin N) (Fin N) ℂ))
        * (X : Matrix (Fin N) (Fin N) ℂ) := by
    show (Y : Matrix (Fin N) (Fin N) ℂ)
        * ((Z : Matrix (Fin N) (Fin N) ℂ) * (X : Matrix (Fin N) (Fin N) ℂ)) = _
    exact (Matrix.mul_assoc _ _ _).symm
  rw [e1, e2, Matrix.trace_mul_comm]

/-- `Re tr(UD)/N = ⟪X U, X D⁻¹⟫` (`PairInterface.reTr_mul_eq_inner`).

DERIVED: no numeral. -/
private theorem reTr_mul (U D : SU N) :
    (Matrix.trace ((U * D : SU N) : Matrix (Fin N) (Fin N) ℂ)).re / (N : ℝ)
      = inner ℝ (realFeature N U) (realFeature N D⁻¹) :=
  reTr_mul_eq_inner N U D

/-- `Re tr(U⁻¹C)/N = ⟪X U, X C⟫`: inversion acts on the feature by an isometry.

DERIVED: no numeral. -/
private theorem reTr_inv_mul (U C : SU N) :
    (Matrix.trace ((U⁻¹ * C : SU N) : Matrix (Fin N) (Fin N) ℂ)).re / (N : ℝ)
      = inner ℝ (realFeature N U) (realFeature N C) := by
  obtain ⟨Ti, hTi⟩ := exists_isometry_inv N
  rw [reTr_mul, hTi U, hTi C, LinearIsometry.inner_map_map]

/-- **One free factor**: `Re tr(A g^{±1} B)/N` is a unit functional of `X g`.

DERIVED: `0` is the excluded rank; `1` is the norm bound. -/
private theorem reTr_sandwich_single (hN : N ≠ 0) (A B : SU N) (o : Bool) :
    ∃ v : FE N, ‖v‖ ≤ 1 ∧ ∀ g : SU N,
      (Matrix.trace ((A * (if o then g else g⁻¹) * B : SU N) : Matrix (Fin N) (Fin N) ℂ)).re
          / (N : ℝ)
        = inner ℝ v (realFeature N g) := by
  cases o
  · refine ⟨realFeature N (B * A), (norm_realFeature hN _).le, fun g => ?_⟩
    show (Matrix.trace ((A * g⁻¹ * B : SU N) : Matrix (Fin N) (Fin N) ℂ)).re / (N : ℝ) = _
    rw [reTr_rot, reTr_inv_mul, real_inner_comm]
  · refine ⟨realFeature N (B * A)⁻¹, (norm_realFeature hN _).le, fun g => ?_⟩
    show (Matrix.trace ((A * g * B : SU N) : Matrix (Fin N) (Fin N) ℂ)).re / (N : ℝ) = _
    rw [reTr_rot, reTr_mul, real_inner_comm]

/-- **The feature of a sandwich `P g^{±1} Q` is an isometric image of `X g`**
(`PairInterface.exists_isometry_mul_left/right/inv`).

DERIVED: no numeral. -/
private theorem feat_sandwich (P Q : SU N) (o : Bool) :
    ∃ T : FE N →ₗᵢ[ℝ] FE N, ∀ g : SU N,
      realFeature N (P * (if o then g else g⁻¹) * Q) = T (realFeature N g) := by
  obtain ⟨TL, hTL⟩ := exists_isometry_mul_left N P
  obtain ⟨TR, hTR⟩ := exists_isometry_mul_right N Q
  obtain ⟨TI, hTI⟩ := exists_isometry_inv N
  cases o
  · refine ⟨TL.comp (TR.comp TI), fun g => ?_⟩
    show realFeature N (P * g⁻¹ * Q) = TL (TR (TI (realFeature N g)))
    rw [mul_assoc, hTL, hTR, hTI]
  · refine ⟨TL.comp TR, fun g => ?_⟩
    show realFeature N (P * g * Q) = TL (TR (realFeature N g))
    rw [mul_assoc, hTL, hTR]

/-- `(P g^{±1} Q)⁻¹ = Q⁻¹ g^{∓1} P⁻¹`.

DERIVED: no numeral. -/
private theorem inv_sandwich (P Q g : SU N) (ol : Bool) :
    (P * (if ol then g else g⁻¹) * Q)⁻¹ = Q⁻¹ * (if (!ol) then g else g⁻¹) * P⁻¹ := by
  cases ol
  · show (P * g⁻¹ * Q)⁻¹ = Q⁻¹ * g * P⁻¹
    group
  · show (P * g * Q)⁻¹ = Q⁻¹ * g⁻¹ * P⁻¹
    group

/-- **Two free factors**: `Re tr(h^{±1} P g^{±1} Q)/N = ⟪X h, T X g⟫` with `‖T‖ ≤ 1`.

DERIVED: `1` is the norm bound. -/
private theorem reTr_pair_form (P Q : SU N) (om ol : Bool) :
    ∃ T : FE N →L[ℝ] FE N, ‖T‖ ≤ 1 ∧ ∀ h g : SU N,
      (Matrix.trace (((if om then h else h⁻¹) * (P * (if ol then g else g⁻¹) * Q) : SU N)
          : Matrix (Fin N) (Fin N) ℂ)).re / (N : ℝ)
        = inner ℝ (realFeature N h) (T (realFeature N g)) := by
  cases om
  · obtain ⟨T, hT⟩ := feat_sandwich P Q ol
    refine ⟨T.toContinuousLinearMap, T.norm_toContinuousLinearMap_le, fun h g => ?_⟩
    show (Matrix.trace ((h⁻¹ * (P * (if ol then g else g⁻¹) * Q) : SU N)
        : Matrix (Fin N) (Fin N) ℂ)).re / (N : ℝ)
      = inner ℝ (realFeature N h) (T (realFeature N g))
    rw [reTr_inv_mul, hT]
  · obtain ⟨T, hT⟩ := feat_sandwich Q⁻¹ P⁻¹ (!ol)
    refine ⟨T.toContinuousLinearMap, T.norm_toContinuousLinearMap_le, fun h g => ?_⟩
    show (Matrix.trace ((h * (P * (if ol then g else g⁻¹) * Q) : SU N)
        : Matrix (Fin N) (Fin N) ℂ)).re / (N : ℝ)
      = inner ℝ (realFeature N h) (T (realFeature N g))
    rw [reTr_mul, inv_sandwich, hT]

/-! ## 3. The plaquette traces -/

/-- **A non-diagonal plaquette visiting `l` and not `m` is a unit functional of `X g`.**

DERIVED: `4` is the spacetime dimension; `1` is the least `M`, the successor writing the extent and
the norm bound; `0` is the excluded rank; `1`, `2` in `p.1.1`, `p.1.2` are projections. -/
theorem reTr_hol_single (hN : N ≠ 0) {M : ℕ} (hM : 1 ≤ M) (p : WilsonHypercubic.Plaq 4 (M + 1))
    (hp : p.1.1 ≠ p.1.2) {l m : WilsonHypercubic.Link 4 (M + 1)}
    (hl : l ∈ (bdT M p).map Prod.fst) (hm : m ∉ (bdT M p).map Prod.fst)
    (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    ∃ v : FE N, ‖v‖ ≤ 1 ∧ ∀ h g : SU N,
      (Matrix.trace ((wilsonHol (bdT M) p (Function.update (Function.update W m h) l g) : SU N)
          : Matrix (Fin N) (Fin N) ℂ)).re / (N : ℝ)
        = inner ℝ v (realFeature N g) := by
  obtain ⟨o, s, t, hw, hs, ht⟩ := list_split (nodup_nondiag hM p hp) hl
  have hms : m ∉ s.map Prod.fst := fun h => hm (by
    rw [hw, List.map_append]
    exact List.mem_append.mpr (Or.inl h))
  have hmt : m ∉ t.map Prod.fst := fun h => hm (by
    rw [hw, List.map_append, List.map_cons]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h))))
  obtain ⟨A, hA⟩ : ∃ A : SU N, A = (s.map (fun lo : WilsonHypercubic.Link 4 (M + 1) × Bool =>
      if lo.2 then W lo.1 else (W lo.1)⁻¹)).prod := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : SU N, B = (t.map (fun lo : WilsonHypercubic.Link 4 (M + 1) × Bool =>
      if lo.2 then W lo.1 else (W lo.1)⁻¹)).prod := ⟨_, rfl⟩
  have hhol : ∀ h g : SU N, wilsonHol (bdT M) p (Function.update (Function.update W m h) l g)
      = A * (if o then g else g⁻¹) * B := by
    intro h g
    have hsV : (s.map (fun lo : WilsonHypercubic.Link 4 (M + 1) × Bool =>
        if lo.2 then Function.update (Function.update W m h) l g lo.1
        else (Function.update (Function.update W m h) l g lo.1)⁻¹)).prod = A := by
      rw [hA]
      exact prod_congr_links (Function.update (Function.update W m h) l g) W s (fun e he => by
        rw [Function.update_of_ne (ne_of_mem_not hs he), Function.update_of_ne (ne_of_mem_not hms he)])
    have htV : (t.map (fun lo : WilsonHypercubic.Link 4 (M + 1) × Bool =>
        if lo.2 then Function.update (Function.update W m h) l g lo.1
        else (Function.update (Function.update W m h) l g lo.1)⁻¹)).prod = B := by
      rw [hB]
      exact prod_congr_links (Function.update (Function.update W m h) l g) W t (fun e he => by
        rw [Function.update_of_ne (ne_of_mem_not ht he), Function.update_of_ne (ne_of_mem_not hmt he)])
    unfold wilsonHol
    rw [hw, prod_split_eq, hsV, htV]
    simp only [Function.update_self]
  obtain ⟨v, hv1, hv⟩ := reTr_sandwich_single hN A B o
  exact ⟨v, hv1, fun h g => by rw [hhol h g]; exact hv g⟩

#print axioms reTr_hol_single

/-- **A non-diagonal plaquette visiting both links is a contraction pairing of the two features.**

DERIVED: `4` is the spacetime dimension; `1` is the least `M`, the successor writing the extent and
the norm bound; `0` is the excluded rank; `1`, `2` in `p.1.1`, `p.1.2` are projections. -/
theorem reTr_hol_pair (hN : N ≠ 0) {M : ℕ} (hM : 1 ≤ M) (p : WilsonHypercubic.Plaq 4 (M + 1))
    (hp : p.1.1 ≠ p.1.2) {l m : WilsonHypercubic.Link 4 (M + 1)} (hlm : l ≠ m)
    (hl : l ∈ (bdT M p).map Prod.fst) (hm : m ∈ (bdT M p).map Prod.fst)
    (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    ∃ T : FE N →L[ℝ] FE N, ‖T‖ ≤ 1 ∧ ∀ h g : SU N,
      (Matrix.trace ((wilsonHol (bdT M) p (Function.update (Function.update W m h) l g) : SU N)
          : Matrix (Fin N) (Fin N) ℂ)).re / (N : ℝ)
        = inner ℝ (realFeature N h) (T (realFeature N g)) := by
  obtain ⟨om, s, t, hw, hs, ht⟩ := list_split (nodup_nondiag hM p hp) hm
  have hnd : (s.map Prod.fst ++ m :: t.map Prod.fst).Nodup := by
    have h0 := nodup_nondiag hM p hp
    rw [hw, List.map_append, List.map_cons] at h0
    exact h0
  obtain ⟨hnds, hndt', hdis⟩ := List.nodup_append.mp hnd
  have hndt : (t.map Prod.fst).Nodup := (List.nodup_cons.mp hndt').2
  have hlst : l ∈ s.map Prod.fst ∨ l ∈ t.map Prod.fst := by
    rw [hw, List.map_append, List.map_cons] at hl
    rcases List.mem_append.mp hl with h | h
    · exact Or.inl h
    · rcases List.mem_cons.mp h with h | h
      · exact absurd h hlm
      · exact Or.inr h
  rcases hlst with hls | hlt
  · -- `l` before `m` in the word
    obtain ⟨ol, s1, s2, hs12, hl1, hl2⟩ := list_split hnds hls
    have hlt : l ∉ t.map Prod.fst := fun h => hdis l hls l (List.mem_cons.mpr (Or.inr h)) rfl
    have hm1 : m ∉ s1.map Prod.fst := fun h => hs (by
      rw [hs12, List.map_append]
      exact List.mem_append.mpr (Or.inl h))
    have hm2 : m ∉ s2.map Prod.fst := fun h => hs (by
      rw [hs12, List.map_append, List.map_cons]
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h))))
    obtain ⟨S1, hS1⟩ : ∃ S : SU N, S = (s1.map (fun lo : WilsonHypercubic.Link 4 (M + 1) × Bool =>
        if lo.2 then W lo.1 else (W lo.1)⁻¹)).prod := ⟨_, rfl⟩
    obtain ⟨S2, hS2⟩ : ∃ S : SU N, S = (s2.map (fun lo : WilsonHypercubic.Link 4 (M + 1) × Bool =>
        if lo.2 then W lo.1 else (W lo.1)⁻¹)).prod := ⟨_, rfl⟩
    obtain ⟨T0, hT0⟩ : ∃ S : SU N, S = (t.map (fun lo : WilsonHypercubic.Link 4 (M + 1) × Bool =>
        if lo.2 then W lo.1 else (W lo.1)⁻¹)).prod := ⟨_, rfl⟩
    have hhol : ∀ h g : SU N, wilsonHol (bdT M) p (Function.update (Function.update W m h) l g)
        = S1 * (if ol then g else g⁻¹) * S2 * (if om then h else h⁻¹) * T0 := by
      intro h g
      have e1 : (s1.map (fun lo : WilsonHypercubic.Link 4 (M + 1) × Bool =>
          if lo.2 then Function.update (Function.update W m h) l g lo.1
          else (Function.update (Function.update W m h) l g lo.1)⁻¹)).prod = S1 := by
        rw [hS1]
        exact prod_congr_links (Function.update (Function.update W m h) l g) W s1 (fun e he => by
          rw [Function.update_of_ne (ne_of_mem_not hl1 he),
            Function.update_of_ne (ne_of_mem_not hm1 he)])
      have e2 : (s2.map (fun lo : WilsonHypercubic.Link 4 (M + 1) × Bool =>
          if lo.2 then Function.update (Function.update W m h) l g lo.1
          else (Function.update (Function.update W m h) l g lo.1)⁻¹)).prod = S2 := by
        rw [hS2]
        exact prod_congr_links (Function.update (Function.update W m h) l g) W s2 (fun e he => by
          rw [Function.update_of_ne (ne_of_mem_not hl2 he),
            Function.update_of_ne (ne_of_mem_not hm2 he)])
      have e3 : (t.map (fun lo : WilsonHypercubic.Link 4 (M + 1) × Bool =>
          if lo.2 then Function.update (Function.update W m h) l g lo.1
          else (Function.update (Function.update W m h) l g lo.1)⁻¹)).prod = T0 := by
        rw [hT0]
        exact prod_congr_links (Function.update (Function.update W m h) l g) W t (fun e he => by
          rw [Function.update_of_ne (ne_of_mem_not hlt he),
            Function.update_of_ne (ne_of_mem_not ht he)])
      unfold wilsonHol
      rw [hw, hs12, prod_split_eq, prod_split_eq, e1, e2, e3]
      simp only [Function.update_self, Function.update_of_ne hlm.symm]
    obtain ⟨T, hT1, hT⟩ := reTr_pair_form (T0 * S1) S2 om ol
    refine ⟨T, hT1, fun h g => ?_⟩
    rw [hhol h g, reTr_rot,
      show T0 * (S1 * (if ol then g else g⁻¹) * S2) = T0 * S1 * (if ol then g else g⁻¹) * S2 by
        simp only [mul_assoc]]
    exact hT h g
  · -- `l` after `m` in the word
    obtain ⟨ol, t1, t2, ht12, hl1, hl2⟩ := list_split hndt hlt
    have hls : l ∉ s.map Prod.fst := fun h => hdis l h l (List.mem_cons.mpr (Or.inr hlt)) rfl
    have hm1 : m ∉ t1.map Prod.fst := fun h => ht (by
      rw [ht12, List.map_append]
      exact List.mem_append.mpr (Or.inl h))
    have hm2 : m ∉ t2.map Prod.fst := fun h => ht (by
      rw [ht12, List.map_append, List.map_cons]
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h))))
    obtain ⟨S0, hS0⟩ : ∃ S : SU N, S = (s.map (fun lo : WilsonHypercubic.Link 4 (M + 1) × Bool =>
        if lo.2 then W lo.1 else (W lo.1)⁻¹)).prod := ⟨_, rfl⟩
    obtain ⟨T1, hT1d⟩ : ∃ S : SU N, S = (t1.map (fun lo : WilsonHypercubic.Link 4 (M + 1) × Bool =>
        if lo.2 then W lo.1 else (W lo.1)⁻¹)).prod := ⟨_, rfl⟩
    obtain ⟨T2, hT2d⟩ : ∃ S : SU N, S = (t2.map (fun lo : WilsonHypercubic.Link 4 (M + 1) × Bool =>
        if lo.2 then W lo.1 else (W lo.1)⁻¹)).prod := ⟨_, rfl⟩
    have hhol : ∀ h g : SU N, wilsonHol (bdT M) p (Function.update (Function.update W m h) l g)
        = S0 * (if om then h else h⁻¹) * (T1 * (if ol then g else g⁻¹) * T2) := by
      intro h g
      have e0 : (s.map (fun lo : WilsonHypercubic.Link 4 (M + 1) × Bool =>
          if lo.2 then Function.update (Function.update W m h) l g lo.1
          else (Function.update (Function.update W m h) l g lo.1)⁻¹)).prod = S0 := by
        rw [hS0]
        exact prod_congr_links (Function.update (Function.update W m h) l g) W s (fun e he => by
          rw [Function.update_of_ne (ne_of_mem_not hls he),
            Function.update_of_ne (ne_of_mem_not hs he)])
      have e1 : (t1.map (fun lo : WilsonHypercubic.Link 4 (M + 1) × Bool =>
          if lo.2 then Function.update (Function.update W m h) l g lo.1
          else (Function.update (Function.update W m h) l g lo.1)⁻¹)).prod = T1 := by
        rw [hT1d]
        exact prod_congr_links (Function.update (Function.update W m h) l g) W t1 (fun e he => by
          rw [Function.update_of_ne (ne_of_mem_not hl1 he),
            Function.update_of_ne (ne_of_mem_not hm1 he)])
      have e2 : (t2.map (fun lo : WilsonHypercubic.Link 4 (M + 1) × Bool =>
          if lo.2 then Function.update (Function.update W m h) l g lo.1
          else (Function.update (Function.update W m h) l g lo.1)⁻¹)).prod = T2 := by
        rw [hT2d]
        exact prod_congr_links (Function.update (Function.update W m h) l g) W t2 (fun e he => by
          rw [Function.update_of_ne (ne_of_mem_not hl2 he),
            Function.update_of_ne (ne_of_mem_not hm2 he)])
      unfold wilsonHol
      rw [hw, ht12, prod_split_eq, prod_split_eq, e0, e1, e2]
      simp only [Function.update_self, Function.update_of_ne hlm.symm]
    obtain ⟨T, hT1, hT⟩ := reTr_pair_form T1 (T2 * S0) om ol
    refine ⟨T, hT1, fun h g => ?_⟩
    rw [hhol h g, reTr_rot,
      show T1 * (if ol then g else g⁻¹) * T2 * S0 = T1 * (if ol then g else g⁻¹) * (T2 * S0) by
        simp only [mul_assoc]]
    exact hT h g

#print axioms reTr_hol_pair

/-! ## 4. The fibre weight -/

/-- **THE FIBRE WEIGHT OF TWO LINKS.**

DERIVED: `4` is the spacetime dimension; `1` is the least `M` (extent `2`) and the successor writing
the extent; `0` is the excluded rank, the lower end of `β` and the sign of `K`; `12` is
`PairCount.card_visit_nondiag_le`'s bound on the non-diagonal plaquettes visiting one link. -/
theorem wt_fibre_eq (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {M : ℕ} (hM : 1 ≤ M)
    {l m : WilsonHypercubic.Link 4 (M + 1)} (hlm : l ≠ m)
    (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    ∃ (K : ℝ) (T : FE N →L[ℝ] FE N) (α γ : FE N), 0 < K ∧ ‖T‖ ≤ β * (n2 M l m : ℝ) ∧
      ‖α‖ ≤ β * (12 - (n2 M l m : ℝ)) ∧ ‖γ‖ ≤ β * (12 - (n2 M l m : ℝ)) ∧
      ∀ h g : SU N, wt (bdT M) β (Function.update (Function.update W m h) l g)
        = fibreWeight (realFeature N) K T α γ h g := by
  -- the per-plaquette pairings, zero off their class
  have hTc : ∀ p : WilsonHypercubic.Plaq 4 (M + 1), ∃ T : FE N →L[ℝ] FE N, ‖T‖ ≤ 1 ∧
      (¬ (p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∈ (bdT M p).map Prod.fst) → T = 0) ∧
      ((p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∈ (bdT M p).map Prod.fst) →
        ∀ h g : SU N,
          (Matrix.trace ((wilsonHol (bdT M) p (Function.update (Function.update W m h) l g) : SU N)
              : Matrix (Fin N) (Fin N) ℂ)).re / (N : ℝ)
            = inner ℝ (realFeature N h) (T (realFeature N g))) := by
    intro p
    by_cases hc : p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∈ (bdT M p).map Prod.fst
    · obtain ⟨T, hT1, hT2⟩ := reTr_hol_pair hN hM p hc.1 hlm hc.2.1 hc.2.2 W
      exact ⟨T, hT1, fun hn => absurd hc hn, fun _ => hT2⟩
    · exact ⟨0, by simp, fun _ => rfl, fun hc' => absurd hc' hc⟩
  choose Tf hTf1 hTf0 hTf2 using hTc
  have hvc : ∀ p : WilsonHypercubic.Plaq 4 (M + 1), ∃ v : FE N, ‖v‖ ≤ 1 ∧
      (¬ (p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∉ (bdT M p).map Prod.fst) → v = 0) ∧
      ((p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∉ (bdT M p).map Prod.fst) →
        ∀ h g : SU N,
          (Matrix.trace ((wilsonHol (bdT M) p (Function.update (Function.update W m h) l g) : SU N)
              : Matrix (Fin N) (Fin N) ℂ)).re / (N : ℝ)
            = inner ℝ v (realFeature N g)) := by
    intro p
    by_cases hc : p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∉ (bdT M p).map Prod.fst
    · obtain ⟨v, hv1, hv2⟩ := reTr_hol_single hN hM p hc.1 hc.2.1 hc.2.2 W
      exact ⟨v, hv1, fun hn => absurd hc hn, fun _ => hv2⟩
    · exact ⟨0, by simp, fun _ => rfl, fun hc' => absurd hc' hc⟩
  choose vf hvf1 hvf0 hvf2 using hvc
  have hwc : ∀ p : WilsonHypercubic.Plaq 4 (M + 1), ∃ w : FE N, ‖w‖ ≤ 1 ∧
      (¬ (p.1.1 ≠ p.1.2 ∧ m ∈ (bdT M p).map Prod.fst ∧ l ∉ (bdT M p).map Prod.fst) → w = 0) ∧
      ((p.1.1 ≠ p.1.2 ∧ m ∈ (bdT M p).map Prod.fst ∧ l ∉ (bdT M p).map Prod.fst) →
        ∀ h g : SU N,
          (Matrix.trace ((wilsonHol (bdT M) p (Function.update (Function.update W m h) l g) : SU N)
              : Matrix (Fin N) (Fin N) ℂ)).re / (N : ℝ)
            = inner ℝ w (realFeature N h)) := by
    intro p
    by_cases hc : p.1.1 ≠ p.1.2 ∧ m ∈ (bdT M p).map Prod.fst ∧ l ∉ (bdT M p).map Prod.fst
    · obtain ⟨w, hw1, hw2⟩ := reTr_hol_single hN hM p hc.1 (l := m) (m := l) hc.2.1 hc.2.2 W
      refine ⟨w, hw1, fun hn => absurd hc hn, fun _ h g => ?_⟩
      rw [Function.update_comm hlm.symm h g W]
      exact hw2 g h
    · exact ⟨0, by simp, fun _ => rfl, fun hc' => absurd hc' hc⟩
  choose wf hwf1 hwf0 hwf2 using hwc
  -- the density of one plaquette of the pair locus
  have hwd : ∀ U : SU N,
      wilsonDensity U = 1 - (Matrix.trace (U : Matrix (Fin N) (Fin N) ℂ)).re / (N : ℝ) := by
    intro U
    unfold wilsonDensity
    ring
  have hpt : ∀ (h g : SU N) (p : WilsonHypercubic.Plaq 4 (M + 1)),
      (l ∈ (bdT M p).map Prod.fst ∨ m ∈ (bdT M p).map Prod.fst) →
      wilsonDensity (wilsonHol (bdT M) p (Function.update (Function.update W m h) l g))
        = (if p.1.1 = p.1.2 then wilsonDensity (1 : SU N) else 1)
          - (inner ℝ (realFeature N h) (Tf p (realFeature N g)) + inner ℝ (wf p) (realFeature N h)
            + inner ℝ (vf p) (realFeature N g)) := by
    intro h g p hq
    by_cases hd : p.1.1 = p.1.2
    · rw [if_pos hd, wilsonHol_diag M p hd, hTf0 p (fun hc => hc.1 hd), hwf0 p (fun hc => hc.1 hd),
        hvf0 p (fun hc => hc.1 hd), zero_apply, inner_zero_right, inner_zero_left, inner_zero_left]
      ring
    · rw [if_neg hd, hwd]
      by_cases hlp : l ∈ (bdT M p).map Prod.fst <;> by_cases hmp : m ∈ (bdT M p).map Prod.fst
      · rw [hTf2 p ⟨hd, hlp, hmp⟩ h g, hwf0 p (fun hc => hc.2.2 hlp),
          hvf0 p (fun hc => hc.2.2 hmp), inner_zero_left, inner_zero_left]
        ring
      · rw [hvf2 p ⟨hd, hlp, hmp⟩ h g, hTf0 p (fun hc => hmp hc.2.2),
          hwf0 p (fun hc => hmp hc.2.1), zero_apply, inner_zero_right, inner_zero_left]
        ring
      · rw [hwf2 p ⟨hd, hmp, hlp⟩ h g, hTf0 p (fun hc => hlp hc.2.1),
          hvf0 p (fun hc => hlp hc.2.1), zero_apply, inner_zero_right, inner_zero_left]
        ring
      · exact (hq.elim hlp hmp).elim
  -- the pair locus and the constant part
  obtain ⟨Q, hQ⟩ : ∃ Q : Finset (WilsonHypercubic.Plaq 4 (M + 1)),
      Q = Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
        l ∈ (bdT M p).map Prod.fst ∨ m ∈ (bdT M p).map Prod.fst) := ⟨_, rfl⟩
  obtain ⟨E0, hE0⟩ : ∃ E0 : ℝ, E0 = ∑ p ∈ Q,
      (if p.1.1 = p.1.2 then wilsonDensity (1 : SU N) else 1) := ⟨_, rfl⟩
  have hsum : ∀ h g : SU N,
      PairCorr.pairLocSum (bdT M) l m (Function.update (Function.update W m h) l g)
        = E0 - (inner ℝ (realFeature N h) ((∑ p ∈ Q, Tf p) (realFeature N g))
          + inner ℝ (∑ p ∈ Q, wf p) (realFeature N h)
          + inner ℝ (∑ p ∈ Q, vf p) (realFeature N g)) := by
    intro h g
    have e1 : PairCorr.pairLocSum (bdT M) l m (Function.update (Function.update W m h) l g)
        = ∑ p ∈ Q, ((if p.1.1 = p.1.2 then wilsonDensity (1 : SU N) else 1)
          - (inner ℝ (realFeature N h) (Tf p (realFeature N g))
            + inner ℝ (wf p) (realFeature N h) + inner ℝ (vf p) (realFeature N g))) := by
      unfold PairCorr.pairLocSum
      refine Finset.sum_congr (by subst hQ; convert rfl) (fun p hp => hpt h g p ?_)
      rw [hQ] at hp
      exact (Finset.mem_filter.mp hp).2
    rw [e1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← hE0,
      sum_apply, inner_sum, sum_inner, sum_inner]
  -- the norm bounds
  have hTn : ∀ p : WilsonHypercubic.Plaq 4 (M + 1), ‖Tf p‖
      ≤ if (p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∈ (bdT M p).map Prod.fst)
        then (1 : ℝ) else 0 := by
    intro p
    by_cases hc : p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∈ (bdT M p).map Prod.fst
    · rw [if_pos hc]
      exact hTf1 p
    · rw [if_neg hc, hTf0 p hc]
      exact norm_zero.le
  have hvn : ∀ p : WilsonHypercubic.Plaq 4 (M + 1), ‖vf p‖
      ≤ if (p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∉ (bdT M p).map Prod.fst)
        then (1 : ℝ) else 0 := by
    intro p
    by_cases hc : p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∉ (bdT M p).map Prod.fst
    · rw [if_pos hc]
      exact hvf1 p
    · rw [if_neg hc, hvf0 p hc]
      exact norm_zero.le
  have hwn : ∀ p : WilsonHypercubic.Plaq 4 (M + 1), ‖wf p‖
      ≤ if (p.1.1 ≠ p.1.2 ∧ m ∈ (bdT M p).map Prod.fst ∧ l ∉ (bdT M p).map Prod.fst)
        then (1 : ℝ) else 0 := by
    intro p
    by_cases hc : p.1.1 ≠ p.1.2 ∧ m ∈ (bdT M p).map Prod.fst ∧ l ∉ (bdT M p).map Prod.fst
    · rw [if_pos hc]
      exact hwf1 p
    · rw [if_neg hc, hwf0 p hc]
      exact norm_zero.le
  -- the plaquette counts
  have hcl : (Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
      p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∉ (bdT M p).map Prod.fst)).card
        + n2 M l m ≤ 12 := by
    have h1 := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
        p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst))
      (fun p : WilsonHypercubic.Plaq 4 (M + 1) => m ∈ (bdT M p).map Prod.fst)
    have e1 : (Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
          p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst)).filter
          (fun p : WilsonHypercubic.Plaq 4 (M + 1) => m ∈ (bdT M p).map Prod.fst)
        = Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
          p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∈ (bdT M p).map Prod.fst) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_assoc, iff_self]
    have e2 : (Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
          p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst)).filter
          (fun p : WilsonHypercubic.Plaq 4 (M + 1) => ¬ m ∈ (bdT M p).map Prod.fst)
        = Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
          p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∉ (bdT M p).map Prod.fst) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_assoc, iff_self]
    rw [e1, e2] at h1
    have h2 := card_visit_nondiag_le M l
    have h3 : (Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
        p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∈ (bdT M p).map Prod.fst)).card
          = n2 M l m := rfl
    omega
  have hcm : (Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
      p.1.1 ≠ p.1.2 ∧ m ∈ (bdT M p).map Prod.fst ∧ l ∉ (bdT M p).map Prod.fst)).card
        + n2 M l m ≤ 12 := by
    have h1 := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
        p.1.1 ≠ p.1.2 ∧ m ∈ (bdT M p).map Prod.fst))
      (fun p : WilsonHypercubic.Plaq 4 (M + 1) => l ∈ (bdT M p).map Prod.fst)
    have e1 : (Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
          p.1.1 ≠ p.1.2 ∧ m ∈ (bdT M p).map Prod.fst)).filter
          (fun p : WilsonHypercubic.Plaq 4 (M + 1) => l ∈ (bdT M p).map Prod.fst)
        = Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
          p.1.1 ≠ p.1.2 ∧ m ∈ (bdT M p).map Prod.fst ∧ l ∈ (bdT M p).map Prod.fst) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_assoc, iff_self]
    have e2 : (Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
          p.1.1 ≠ p.1.2 ∧ m ∈ (bdT M p).map Prod.fst)).filter
          (fun p : WilsonHypercubic.Plaq 4 (M + 1) => ¬ l ∈ (bdT M p).map Prod.fst)
        = Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
          p.1.1 ≠ p.1.2 ∧ m ∈ (bdT M p).map Prod.fst ∧ l ∉ (bdT M p).map Prod.fst) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_assoc, iff_self]
    rw [e1, e2] at h1
    have h2 := card_visit_nondiag_le M m
    have h3 : (Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
        p.1.1 ≠ p.1.2 ∧ m ∈ (bdT M p).map Prod.fst ∧ l ∈ (bdT M p).map Prod.fst)).card
          = n2 M m l := rfl
    have h4 := n2_symm M l m
    omega
  have hsumT : ‖∑ p ∈ Q, Tf p‖ ≤ (n2 M l m : ℝ) := by
    have hsub : Q.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
          p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∈ (bdT M p).map Prod.fst)
        ⊆ Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
          p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∈ (bdT M p).map Prod.fst) :=
      fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
    have hc := Finset.card_le_card hsub
    calc ‖∑ p ∈ Q, Tf p‖ ≤ ∑ p ∈ Q, ‖Tf p‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ Q, (if (p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst
            ∧ m ∈ (bdT M p).map Prod.fst) then (1 : ℝ) else 0) :=
          Finset.sum_le_sum (fun p _ => hTn p)
      _ = ((Q.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
            p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∈ (bdT M p).map Prod.fst)).card : ℝ) :=
          Finset.sum_boole _ _
      _ ≤ (n2 M l m : ℝ) := by exact_mod_cast hc
  have hsumV : ‖∑ p ∈ Q, vf p‖ ≤ ((Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
      p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∉ (bdT M p).map Prod.fst)).card : ℝ) := by
    have hsub : Q.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
          p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∉ (bdT M p).map Prod.fst)
        ⊆ Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
          p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∉ (bdT M p).map Prod.fst) :=
      fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
    have hc := Finset.card_le_card hsub
    calc ‖∑ p ∈ Q, vf p‖ ≤ ∑ p ∈ Q, ‖vf p‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ Q, (if (p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst
            ∧ m ∉ (bdT M p).map Prod.fst) then (1 : ℝ) else 0) :=
          Finset.sum_le_sum (fun p _ => hvn p)
      _ = ((Q.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
            p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∉ (bdT M p).map Prod.fst)).card : ℝ) :=
          Finset.sum_boole _ _
      _ ≤ _ := by exact_mod_cast hc
  have hsumW : ‖∑ p ∈ Q, wf p‖ ≤ ((Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
      p.1.1 ≠ p.1.2 ∧ m ∈ (bdT M p).map Prod.fst ∧ l ∉ (bdT M p).map Prod.fst)).card : ℝ) := by
    have hsub : Q.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
          p.1.1 ≠ p.1.2 ∧ m ∈ (bdT M p).map Prod.fst ∧ l ∉ (bdT M p).map Prod.fst)
        ⊆ Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
          p.1.1 ≠ p.1.2 ∧ m ∈ (bdT M p).map Prod.fst ∧ l ∉ (bdT M p).map Prod.fst) :=
      fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
    have hc := Finset.card_le_card hsub
    calc ‖∑ p ∈ Q, wf p‖ ≤ ∑ p ∈ Q, ‖wf p‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ Q, (if (p.1.1 ≠ p.1.2 ∧ m ∈ (bdT M p).map Prod.fst
            ∧ l ∉ (bdT M p).map Prod.fst) then (1 : ℝ) else 0) :=
          Finset.sum_le_sum (fun p _ => hwn p)
      _ = ((Q.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
            p.1.1 ≠ p.1.2 ∧ m ∈ (bdT M p).map Prod.fst ∧ l ∉ (bdT M p).map Prod.fst)).card : ℝ) :=
          Finset.sum_boole _ _
      _ ≤ _ := by exact_mod_cast hc
  have hclR : ((Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
      p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∉ (bdT M p).map Prod.fst)).card : ℝ)
        ≤ 12 - (n2 M l m : ℝ) := by
    have h : ((Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
        p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∉ (bdT M p).map Prod.fst)).card : ℝ)
          + (n2 M l m : ℝ) ≤ 12 := by exact_mod_cast hcl
    linarith
  have hcmR : ((Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
      p.1.1 ≠ p.1.2 ∧ m ∈ (bdT M p).map Prod.fst ∧ l ∉ (bdT M p).map Prod.fst)).card : ℝ)
        ≤ 12 - (n2 M l m : ℝ) := by
    have h : ((Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
        p.1.1 ≠ p.1.2 ∧ m ∈ (bdT M p).map Prod.fst ∧ l ∉ (bdT M p).map Prod.fst)).card : ℝ)
          + (n2 M l m : ℝ) ≤ 12 := by exact_mod_cast hcm
    linarith
  refine ⟨Real.exp (-β * E0) * Real.exp (-β * PairCorr.pairRestSum (bdT M) l m W),
    β • (∑ p ∈ Q, Tf p), β • (∑ p ∈ Q, wf p), β • (∑ p ∈ Q, vf p),
    mul_pos (Real.exp_pos _) (Real.exp_pos _), ?_, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg hβ]
    exact mul_le_mul_of_nonneg_left hsumT hβ
  · rw [norm_smul, Real.norm_of_nonneg hβ]
    exact mul_le_mul_of_nonneg_left (le_trans hsumW hcmR) hβ
  · rw [norm_smul, Real.norm_of_nonneg hβ]
    exact mul_le_mul_of_nonneg_left (le_trans hsumV hclR) hβ
  · intro h g
    rw [PairCorr.wt_split_pair (bdT M) β l m, PairCorr.pairRestSum_update_l,
      PairCorr.pairRestSum_update_m, hsum h g]
    unfold fibreWeight
    rw [smul_apply, real_inner_smul_right, real_inner_smul_left, real_inner_smul_left]
    generalize inner ℝ (realFeature N h) ((∑ p ∈ Q, Tf p) (realFeature N g)) = a
    generalize inner ℝ (∑ p ∈ Q, wf p) (realFeature N h) = b
    generalize inner ℝ (∑ p ∈ Q, vf p) (realFeature N g) = c
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring

#print axioms wt_fibre_eq

end MassGap.PairWeight
