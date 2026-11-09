import Mathlib
import MassGap.ChunkLinks

/-!
# MassGap.CrossTerm — the cross-term clause of `WilsonLinkPolymerCross`

`ChunkLinks.WilsonLinkPolymerCross` asks, for each pair of cells `i ≠ j`, for a geometry on the links
of a 4D torus of side `nC` and the cross-term bound
`|⟪P vᵢ, P vⱼ⟫| ≤ Kx · |Q (Inc bd) (act bd β) (pre S) (pre A) (pre U)| · ‖vᵢ‖ ‖vⱼ‖`.
This module shows that on the finite torus this clause, at a coupling with
`8 · kpCost 16 κ ≤ tau β`, forces the cross terms to vanish exactly beyond a fixed range, and that the
lower bound `QFloor` on the torus interaction is false. The Wilson-torus `PolymerCross` route to (B)
therefore carries no usable content; the (B) input of the bridge is `CellLinks.ScreenedCells`
(screening, `CellLinks.Screens`, with one `(Ke, ξ)` at every aperture `m` and zoom `k`), and
`CrossDecay` is `Screens` in another parametrisation.

## 1. The inputs (`CrossDecay`, `QFloor`, `crossDecay_iff_screens`)

* `CrossDecay P v d C κ' L r₀`: `|⟪P vᵢ, P vⱼ⟫| ≤ C e^{−κ'(d(i,j) L − r₀)} ‖vᵢ‖ ‖vⱼ‖` for `i ≠ j`.
* `QFloor Nc nC β c κ' M L r₀`: at every separation `D` a geometry on the links of the torus with the
  clauses of `WilsonLinkPolymerCross` at `d(i,j) = D`, and `|Q| ≥ c e^{−κ'(D L − r₀)}`.
* `crossDecay_iff_screens`: for `ξ, L ≠ 0`, `Screens P v d Ke ξ ℓ` holds if and only if
  `CrossDecay P v d (Ke e^{−κ' r₀}) κ' L r₀` with `κ' = ℓ/(ξ L)`. The bounds agree pointwise.

## 2. Exact vanishing of the interaction (`Z_sdiff_inactive`, `Z_union`, `Z_union_active`,
`Q_eq_zero_of_split`, `Q_eq_zero_of_far`)

* `Z_sdiff_inactive`: removing polymers of activity `0` leaves `Z` unchanged.
* `Z_union`, `Z_union_active`: `Z (X ∪ Y) = Z X · Z Y` for disjoint `X, Y` with no incompatible pair
  of active polymers across them.
* `Q_eq_zero_of_split`: with `Z > 0`, a set `C ⊆ S` that no active polymer of `S ∖ C` meets
  actively, containing the active polymers of `A ∩ S` and no active polymer of `U`, gives
  `Q S A U = 0`: the four partition functions of `Q` factor over `C` and `S ∖ C` and the logarithms
  cancel.
* `Q_eq_zero_of_far`: in a `MatchAt` gas on a finite site type `V` with the geometry of
  `MatchAt.cluster_sites`, `R > (|V| + 1)|V|` gives `Q meet w S A U = 0`. Every active polymer has
  `dset`-spread at most `|V|`; among the `|V| + 1` intervals `(j|V|, (j+1)|V|]`, `j ≤ |V|`, one holds
  no value of `dset`; the active polymers of `S` lying above it form `C`.

## 3. On the Wilson torus (`farRange`, `cross_zero_of_far`, `cross_zero_of_far_plaq`, `not_qFloor`)

* `farRange nC = (|V| + 1)|V|` with `V = Link 4 nC`.
* `cross_zero_of_far`: `WilsonLinkPolymerCross` with `β > 0`, `κ ≥ 0`, `8 · kpCost 16 κ ≤ tau β`
  gives `⟪P vᵢ, P vⱼ⟫ = 0` whenever `d(i,j) L − r₀ > farRange nC`: exact orthogonality beyond a range
  fixed by the torus side. The torus, its side `nC` and its coupling `β` are parameters of the clause,
  not the slab's; at a fixed `nC` the clause is exact orthogonality of the far cross terms, and
  `farRange nC` grows with `nC`.
* `cross_zero_of_far_plaq`: the same for `ChunkActivity.WilsonPolymerCross` (the overlap gas on
  plaquettes) with range `(|Plaq 4 nC| + 1)|Plaq 4 nC|`.
* `not_qFloor`: under the same coupling hypothesis, `c > 0` and `L > 0`, `QFloor` is false.
  `wilsonLinkPolymerCross_of_crossDecay` and `relFloorM_of_crossDecay_qFloor` take `QFloor` as a
  hypothesis; the second also takes the coupling hypothesis, so its hypotheses are inconsistent.
* `crossDecay_of_wilsonLinkPolymerCross`: `WilsonLinkPolymerCross` with `Kx ≥ 0` gives `CrossDecay`
  with `C = Kx M` at the KP rate `κ` (through `MatchAt.cluster_sites`).

## 4. The degenerate geometry (`Q_empty_A`, `wilsonLinkPolymerCross_of_cross_zero`,
`cross_zero_of_empty_A`)

With `A = ∅` every geometry clause holds (`ρ = 0`, `dset = R` constant, `U = Λ = ∅`) and `Q = 0`.
`wilsonLinkPolymerCross_of_cross_zero`: vanishing cross terms give the clause at every `Kx` and
`M ≥ 0`; `cross_zero_of_empty_A`: a witness with `A = ∅` forces the cross term to vanish.

## Strength

`cross_zero_of_far` and `not_qFloor` are proved at the real objects: the Wilson activities `act` on
the links of the 4D torus at any coupling meeting `8 · kpCost 16 κ ≤ tau β`. Nothing here proves
`Screens` (equivalently `CrossDecay`) for the Wilson slab pieces. The open content of (B) is
`CellLinks.ScreenedCells` with one `(ρc, Ke, ξ)` at every `m > 0` and `k ≥ K₀`, as stated at
`CellLinks` §2 and consumed by `CellLinks.BoxParams.relFloorM_of_screened`.

DERIVED (module-wide): `0` the empty families, the sign of the constants and the lowest interval;
`1` the KP constant `a = 1` of `polymerCross_of_wilsonLink` and the extra interval of the
pigeonhole; `4` the dimension, `8`, `16` as in `ChunkLinks`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.CrossTerm

open Finset MeasureTheory
open MassGap.StrongCoupling MassGap.PolymerCount MassGap.NoTransitionFlow MassGap.ChunkActivity
open MassGap.ChunkLinks

/-! ## 1. The inputs -/

section Inputs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- **Decay of the cross terms** at rate `κ'` per unit of `d(i,j) L − r₀`. -/
def CrossDecay (P : E →L[ℝ] E) (v : Fin n → E) (d : Fin n → Fin n → ℕ) (C κ' L r₀ : ℝ) : Prop :=
  ∀ i j, i ≠ j → |inner ℝ (P (v i)) (P (v j))|
    ≤ C * Real.exp (-(κ' * ((d i j : ℝ) * L - r₀))) * (‖v i‖ * ‖v j‖)

/-- **A floor on the Wilson torus interaction**: at every separation `D`, the geometry clauses of
`WilsonLinkPolymerCross` at `d(i,j) = D` and `|Q| ≥ c e^{−κ'(D L − r₀)}`. False under
`8 · kpCost 16 κ ≤ tau β` with `c, L > 0` (`not_qFloor`). DERIVED: Inherited from `ChunkLinks`:
`16 = 4 · 4` the plaquettes per link, `8 = 2 · 4`; `4` the dimension. -/
def QFloor (Nc nC : ℕ) [NeZero nC] (β c κ' M L r₀ : ℝ) : Prop :=
  ∀ D : ℕ, ∃ (ρ : WilsonHypercubic.Link 4 nC → WilsonHypercubic.Link 4 nC → ℝ)
    (dset : WilsonHypercubic.Link 4 nC → ℝ) (U A S : Finset (Finset (WilsonHypercubic.Link 4 nC)))
    (Λ : Finset (WilsonHypercubic.Link 4 nC)) (R : ℝ),
    (∀ x y, dset x ≤ dset y + ρ x y) ∧
    (∀ X, linkAct (Nc := Nc) (WilsonHypercubic.bd (d := 4) (n := nC)) β X ≠ 0 →
      ∀ x ∈ X, ∀ y ∈ X, ρ x y ≤ X.card) ∧
    (∀ Y ∈ U, linkAct (Nc := Nc) (WilsonHypercubic.bd (d := 4) (n := nC)) β Y ≠ 0 →
      ∀ y ∈ Y, dset y ≤ 0) ∧ (∀ y ∈ Λ, R ≤ dset y) ∧
    (∀ X ∈ A, (X ∩ Λ).Nonempty) ∧ (∀ X ∈ A, X ∉ U) ∧ (Λ.card : ℝ) ≤ M ∧
    (D : ℝ) * L - r₀ ≤ R ∧
    c * Real.exp (-(κ' * ((D : ℝ) * L - r₀)))
      ≤ |MatchAt.Q (Inc (WilsonHypercubic.bd (d := 4) (n := nC)))
        (act (Nc := Nc) (WilsonHypercubic.bd (d := 4) (n := nC)) β)
        (pre (supp (WilsonHypercubic.bd (d := 4) (n := nC))) S)
        (pre (supp (WilsonHypercubic.bd (d := 4) (n := nC))) A)
        (pre (supp (WilsonHypercubic.bd (d := 4) (n := nC))) U)|

/-- **`CrossDecay` is `Screens`**: for `ξ, L ≠ 0`, `Screens P v d Ke ξ ℓ` is
`CrossDecay P v d (Ke e^{−κ' r₀}) κ' L r₀` with `κ' = ℓ/(ξ L)`; the two bounds agree pointwise. -/
theorem crossDecay_iff_screens {P : E →L[ℝ] E} {v : Fin n → E} {d : Fin n → Fin n → ℕ}
    {Ke ξ ℓ L r₀ : ℝ} (hξ : ξ ≠ 0) (hL : L ≠ 0) :
    CellLinks.Screens P v d Ke ξ ℓ ↔
      CrossDecay P v d (Ke * Real.exp (-(ℓ / (ξ * L) * r₀))) (ℓ / (ξ * L)) L r₀ := by
  have key : ∀ m : ℕ, Ke * Real.exp (-((m : ℝ) * ℓ / ξ))
      = Ke * Real.exp (-(ℓ / (ξ * L) * r₀)) * Real.exp (-(ℓ / (ξ * L) * ((m : ℝ) * L - r₀))) := by
    intro m
    have e : ℓ / (ξ * L) * r₀ + ℓ / (ξ * L) * ((m : ℝ) * L - r₀) = (m : ℝ) * ℓ / ξ := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
        div_eq_div_iff (mul_ne_zero hξ hL) hξ]
      ring
    rw [mul_assoc, ← Real.exp_add, ← neg_add, e]
  unfold CellLinks.Screens CrossDecay
  refine forall_congr' fun i => forall_congr' fun j => forall_congr' fun _ => ?_
  rw [key]

end Inputs

/-! ## 2. Exact vanishing of the interaction -/

section Vanish

variable {Pol : Type*} [Fintype Pol] [DecidableEq Pol] {inc : Pol → Pol → Prop} [DecidableRel inc]
  {w : Pol → ℝ}

/-- **Inactive polymers do not count**: removing polymers of activity `0` leaves `Z` unchanged. -/
theorem Z_sdiff_inactive (hs : MatchAt.SymmRel inc) (T B : Finset Pol)
    (hB : ∀ γ ∈ B, γ ∈ T → w γ = 0) : MatchAt.Z inc w (T \ B) = MatchAt.Z inc w T := by
  induction B using Finset.induction_on with
  | empty => simp
  | @insert b B hb ih =>
    rw [sdiff_insert, ← ih (fun γ hγ hγT => hB γ (mem_insert_of_mem hγ) hγT)]
    by_cases hbm : b ∈ T \ B
    · rw [MatchAt.Z_rec hs hbm, hB b (mem_insert_self b B) (mem_sdiff.1 hbm).1, zero_mul, add_zero]
    · rw [erase_eq_of_notMem hbm]

/-- **`Z` factorises over a split with no incompatibility across it.** -/
theorem Z_union (hs : MatchAt.SymmRel inc) {Y : Finset Pol} :
    ∀ X : Finset Pol, Disjoint X Y → (∀ x ∈ X, ∀ y ∈ Y, ¬ inc x y) →
      MatchAt.Z inc w (X ∪ Y) = MatchAt.Z inc w X * MatchAt.Z inc w Y := by
  intro X
  induction X using Finset.strongInduction with
  | H X ih =>
    intro hXY hinc
    rcases X.eq_empty_or_nonempty with h | ⟨γ, hγ⟩
    · subst h
      rw [empty_union, MatchAt.Z_empty, one_mul]
    · have hγY : γ ∉ Y := disjoint_left.1 hXY hγ
      have hγU : γ ∈ X ∪ Y := mem_union_left Y hγ
      have e1 : (X ∪ Y).erase γ = X.erase γ ∪ Y := by
        ext x
        simp only [mem_erase, mem_union]
        constructor
        · rintro ⟨hne, hx | hx⟩
          · exact Or.inl ⟨hne, hx⟩
          · exact Or.inr hx
        · rintro (⟨hne, hx⟩ | hx)
          · exact ⟨hne, Or.inl hx⟩
          · exact ⟨fun e => hγY (by rw [← e]; exact hx), Or.inr hx⟩
      have e2 : (X.erase γ ∪ Y) \ MatchAt.nbr inc γ = (X.erase γ \ MatchAt.nbr inc γ) ∪ Y := by
        ext x
        simp only [mem_sdiff, mem_union]
        constructor
        · rintro ⟨hx | hx, hn⟩
          · exact Or.inl ⟨hx, hn⟩
          · exact Or.inr hx
        · rintro (⟨hx, hn⟩ | hx)
          · exact ⟨Or.inl hx, hn⟩
          · exact ⟨Or.inr hx, fun hn => hinc γ hγ x hx (mem_filter.1 hn).2.2⟩
      have hsub1 : X.erase γ ⊆ X := erase_subset γ X
      have hsub2 : X.erase γ \ MatchAt.nbr inc γ ⊆ X := sdiff_subset.trans hsub1
      rw [MatchAt.Z_rec hs hγU, e1, e2,
        ih _ (erase_ssubset hγ) (disjoint_of_subset_left hsub1 hXY)
          (fun x hx y hy => hinc x (hsub1 hx) y hy),
        ih _ (sdiff_subset.trans_ssubset (erase_ssubset hγ)) (disjoint_of_subset_left hsub2 hXY)
          (fun x hx y hy => hinc x (hsub2 hx) y hy),
        MatchAt.Z_rec hs hγ]
      ring

/-- **`Z` factorises when no active polymer of `X` is incompatible with an active one of `Y`.** -/
theorem Z_union_active (hs : MatchAt.SymmRel inc) {X Y : Finset Pol} (hXY : Disjoint X Y)
    (hinc : ∀ x ∈ X, ∀ y ∈ Y, w x ≠ 0 → w y ≠ 0 → ¬ inc x y) :
    MatchAt.Z inc w (X ∪ Y) = MatchAt.Z inc w X * MatchAt.Z inc w Y := by
  classical
  set B := (X ∪ Y).filter (fun γ => w γ = 0) with hB_def
  have hB : ∀ T : Finset Pol, ∀ γ ∈ B, γ ∈ T → w γ = 0 := fun _ γ hγ _ => (mem_filter.1 hγ).2
  have hact : ∀ {T : Finset Pol} {γ : Pol}, T ⊆ X ∪ Y → γ ∈ T \ B → w γ ≠ 0 := by
    intro T γ hT hγ hw
    exact (mem_sdiff.1 hγ).2 (mem_filter.2 ⟨hT (mem_sdiff.1 hγ).1, hw⟩)
  rw [← Z_sdiff_inactive hs (X ∪ Y) B (hB _), union_sdiff_distrib,
    Z_union hs (X \ B) (disjoint_of_subset_left sdiff_subset (disjoint_of_subset_right sdiff_subset hXY))
      (fun x hx y hy => hinc x (mem_sdiff.1 hx).1 y (mem_sdiff.1 hy).1
        (hact subset_union_left hx) (hact subset_union_right hy)),
    Z_sdiff_inactive hs X B (hB _), Z_sdiff_inactive hs Y B (hB _)]

/-- **The interaction vanishes across a split**: with `Z > 0`, a set `C ⊆ S` such that no active
polymer of `C` is incompatible with an active polymer of `S ∖ C`, every active polymer of `A` in `S`
lies in `C`, and no active polymer of `C` lies in `U`, gives `Q S A U = 0`. -/
theorem Q_eq_zero_of_split (hs : MatchAt.SymmRel inc) (hpos : ∀ T, 0 < MatchAt.Z inc w T)
    {S A U C : Finset Pol} (hC : C ⊆ S)
    (hinc : ∀ x ∈ C, ∀ y ∈ S, y ∉ C → w x ≠ 0 → w y ≠ 0 → ¬ inc x y)
    (hA : ∀ γ ∈ S, γ ∉ C → γ ∈ A → w γ = 0) (hU : ∀ γ ∈ C, γ ∈ U → w γ = 0) :
    MatchAt.Q inc w S A U = 0 := by
  obtain ⟨D, hD⟩ : ∃ D, D = S \ C := ⟨_, rfl⟩
  have hS : S = C ∪ D := by rw [hD]; exact (union_sdiff_of_subset hC).symm
  have hsplit : ∀ X Y : Finset Pol, X ⊆ C → Y ⊆ D →
      MatchAt.Z inc w (X ∪ Y) = MatchAt.Z inc w X * MatchAt.Z inc w Y := by
    intro X Y hX hY
    have hY' : ∀ {y}, y ∈ Y → y ∈ S ∧ y ∉ C := fun hy => by
      have := hY hy
      rw [hD] at this
      exact mem_sdiff.1 this
    refine Z_union_active hs (disjoint_of_subset_left hX (disjoint_of_subset_right hY ?_))
      (fun x hx y hy => hinc x (hX hx) y (hY' hy).1 (hY' hy).2)
    rw [hD]
    exact disjoint_sdiff
  have hDmem : ∀ {γ}, γ ∈ D → γ ∈ S ∧ γ ∉ C := fun hγ => by
    rw [hD] at hγ
    exact mem_sdiff.1 hγ
  have hDA : MatchAt.Z inc w (D \ A) = MatchAt.Z inc w D :=
    Z_sdiff_inactive hs D A fun γ hγA hγD => hA γ (hDmem hγD).1 (hDmem hγD).2 hγA
  have hCU : MatchAt.Z inc w (C \ U) = MatchAt.Z inc w C :=
    Z_sdiff_inactive hs C U fun γ hγU hγC => hU γ hγC hγU
  have hCUA : MatchAt.Z inc w ((C \ U) \ A) = MatchAt.Z inc w (C \ A) := by
    rw [sdiff_sdiff_comm]
    exact Z_sdiff_inactive hs (C \ A) U fun γ hγU hγ => hU γ (mem_sdiff.1 hγ).1 hγU
  have hDUA : MatchAt.Z inc w ((D \ U) \ A) = MatchAt.Z inc w (D \ U) :=
    Z_sdiff_inactive hs (D \ U) A fun γ hγA hγ =>
      hA γ (hDmem (mem_sdiff.1 hγ).1).1 (hDmem (mem_sdiff.1 hγ).1).2 hγA
  unfold MatchAt.Q
  rw [hS]
  simp only [union_sdiff_distrib]
  rw [hsplit C D subset_rfl subset_rfl, hsplit (C \ A) (D \ A) sdiff_subset sdiff_subset,
    hsplit (C \ U) (D \ U) sdiff_subset sdiff_subset,
    hsplit ((C \ U) \ A) ((D \ U) \ A) (sdiff_subset.trans sdiff_subset)
      (sdiff_subset.trans sdiff_subset),
    hDA, hCU, hCUA, hDUA,
    Real.log_mul (hpos C).ne' (hpos D).ne', Real.log_mul (hpos (C \ A)).ne' (hpos D).ne',
    Real.log_mul (hpos C).ne' (hpos (D \ U)).ne',
    Real.log_mul (hpos (C \ A)).ne' (hpos (D \ U)).ne']
  ring

end Vanish

section Far

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The interaction vanishes beyond a fixed range**: in a `MatchAt` gas on a finite site type `V`
with the geometry of `MatchAt.cluster_sites` (no disjointness of `A` and `U` needed),
`R > (|V| + 1)|V|` gives `Q meet w S A U = 0`. -/
theorem Q_eq_zero_of_far {w : Finset V → ℝ} {a κ : ℝ} (hM : MatchAt.MatchAt w a κ)
    {ρ : V → V → ℝ} {dset : V → ℝ} (hlip : ∀ x y, dset x ≤ dset y + ρ x y)
    (hdiam : ∀ X, w X ≠ 0 → ∀ x ∈ X, ∀ y ∈ X, ρ x y ≤ X.card)
    {U : Finset (Finset V)} (hcore : ∀ Y ∈ U, w Y ≠ 0 → ∀ y ∈ Y, dset y ≤ 0)
    {Λ : Finset V} {R : ℝ} (hΛ : ∀ y ∈ Λ, R ≤ dset y)
    {A : Finset (Finset V)} (hA : ∀ X ∈ A, (X ∩ Λ).Nonempty) (S : Finset (Finset V))
    (hR : ((Fintype.card V : ℝ) + 1) * Fintype.card V < R) :
    MatchAt.Q MatchAt.meet w S A U = 0 := by
  classical
  obtain ⟨sV, hsV⟩ : ∃ sV : ℝ, sV = Fintype.card V := ⟨_, rfl⟩
  rw [← hsV] at hR
  have hs0 : 0 ≤ sV := by rw [hsV]; exact Nat.cast_nonneg _
  -- every active polymer has `dset`-spread at most `|V|`
  have hspread : ∀ X, w X ≠ 0 → ∀ x ∈ X, ∀ y ∈ X, dset x ≤ dset y + sV := by
    intro X hX x hx y hy
    have h3 : (X.card : ℝ) ≤ sV := by rw [hsV]; exact_mod_cast card_le_univ X
    linarith [hlip x y, hdiam X hX x hx y hy]
  -- a gap: one of the `|V| + 1` intervals `(j|V|, (j+1)|V|]` holds no value of `dset`
  set J := (range (Fintype.card V + 1)).filter
    (fun j : ℕ => ∃ v : V, (j : ℝ) * sV < dset v ∧ dset v ≤ ((j : ℝ) + 1) * sV) with hJ
  have hJcard : J.card ≤ (univ : Finset V).card := by
    refine card_le_card_of_forall_subsingleton
      (fun (j : ℕ) (v : V) => (j : ℝ) * sV < dset v ∧ dset v ≤ ((j : ℝ) + 1) * sV)
      (fun j hj => ?_) (fun v _ => ?_)
    · obtain ⟨v, hv⟩ := (mem_filter.1 hj).2
      exact ⟨v, mem_univ v, hv⟩
    · intro j₁ hj₁ j₂ hj₂
      obtain ⟨-, h1a, h1b⟩ := hj₁
      obtain ⟨-, h2a, h2b⟩ := hj₂
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have hc : ((j₁ : ℝ) + 1) ≤ j₂ := by exact_mod_cast Nat.succ_le_of_lt h
        nlinarith [mul_le_mul_of_nonneg_right hc hs0]
      · have hc : ((j₂ : ℝ) + 1) ≤ j₁ := by exact_mod_cast Nat.succ_le_of_lt h
        nlinarith [mul_le_mul_of_nonneg_right hc hs0]
  have hlt : J.card < (range (Fintype.card V + 1)).card := by
    rw [card_range]
    rw [card_univ] at hJcard
    omega
  obtain ⟨j, hjr, hjJ⟩ := exists_mem_notMem_of_card_lt_card hlt
  have hjle : (j : ℝ) ≤ sV := by
    rw [hsV]
    exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hjr)
  have hgap : ∀ v : V, (j : ℝ) * sV < dset v → (j : ℝ) * sV + sV < dset v := by
    intro v h1
    by_contra h2
    rw [not_lt] at h2
    exact hjJ (mem_filter.2 ⟨hjr, v, h1, by linarith⟩)
  have ht0 : 0 ≤ (j : ℝ) * sV := mul_nonneg (Nat.cast_nonneg _) hs0
  have htR : (j : ℝ) * sV + sV < R := by nlinarith [mul_le_mul_of_nonneg_right hjle hs0]
  -- the active polymers of `S` above the gap
  set C := S.filter (fun X => w X ≠ 0 ∧ X.Nonempty ∧ ∀ x ∈ X, (j : ℝ) * sV < dset x) with hC
  refine Q_eq_zero_of_split MatchAt.meet_symm
    (fun T => MatchAt.Z_pos MatchAt.meet_symm (MatchAt.dob_of_matchAt hM) T)
    (C := C) (filter_subset _ _) ?_ ?_ ?_
  · intro x hx y hy hyC _ hwy hxy
    obtain ⟨z, hz⟩ : (x ∩ y).Nonempty := hxy
    rw [mem_inter] at hz
    have hzt := hgap z ((mem_filter.1 hx).2.2.2 z hz.1)
    obtain ⟨u, hu, hut⟩ : ∃ u ∈ y, dset u ≤ (j : ℝ) * sV := by
      by_contra hno
      simp only [not_exists, not_and, not_le] at hno
      exact hyC (mem_filter.2 ⟨hy, hwy, ⟨z, hz.2⟩, hno⟩)
    linarith [hspread y hwy z hz.2 u hu]
  · intro γ hγS hγC hγA
    by_contra hw
    obtain ⟨y, hy⟩ := hA γ hγA
    rw [mem_inter] at hy
    refine hγC (mem_filter.2 ⟨hγS, hw, ⟨y, hy.1⟩, fun x hx => ?_⟩)
    linarith [hspread γ hw y hy.1 x hx, hΛ y hy.2]
  · intro γ hγC hγU
    by_contra hw
    obtain ⟨-, -, ⟨x, hx⟩, hall⟩ := mem_filter.1 hγC
    linarith [hall x hx, hcore γ hγU hw x hx]

end Far

/-! ## 3. On the Wilson torus -/

/-- **The fixed range** `(|V| + 1)|V|` of the torus, `V = Link 4 nC`. -/
def farRange (nC : ℕ) : ℝ :=
  ((Fintype.card (WilsonHypercubic.Link 4 nC) : ℝ) + 1) * Fintype.card (WilsonHypercubic.Link 4 nC)

section Torus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- **`WilsonLinkPolymerCross` forces exact orthogonality beyond a fixed range**: with `β > 0`,
`κ ≥ 0` and `8 · kpCost 16 κ ≤ tau β`, every pair `i ≠ j` with `d(i,j) L − r₀ > farRange nC` has
`⟪P vᵢ, P vⱼ⟫ = 0`. -/
theorem cross_zero_of_far {Nc nC : ℕ} [NeZero nC] (hN : Nc ≠ 0) {β κ : ℝ} (hβ : 0 < β)
    (hκ : 0 ≤ κ) (hτ : 8 * kpCost 16 κ ≤ tau β) {P : E →L[ℝ] E} {v : Fin n → E}
    {d : Fin n → Fin n → ℕ} {Kx M L r₀ : ℝ} (h : WilsonLinkPolymerCross Nc nC β P v d Kx M L r₀)
    {i j : Fin n} (hij : i ≠ j) (hfar : farRange nC < (d i j : ℝ) * L - r₀) :
    inner ℝ (P (v i)) (P (v j)) = 0 := by
  obtain ⟨ρ, dset, U, A, S, Λ, R, h1, h2, h3, h4, h5, -, -, h8, h9⟩ := h i j hij
  have hR : ((Fintype.card (WilsonHypercubic.Link 4 nC) : ℝ) + 1)
      * Fintype.card (WilsonHypercubic.Link 4 nC) < R := hfar.trans_le h8
  have hQ := Q_eq_zero_of_far (matchAt_linkAct_of_tau (n := nC) hN hβ hκ hτ) h1 h2 h3 h4 h5 S hR
  rw [linkQ_eq _ linkSupp_nonempty_hypercubic] at hQ
  rw [hQ, abs_zero, mul_zero, zero_mul] at h9
  exact abs_nonpos_iff.1 h9

/-- **The same on the plaquette gas**: `ChunkActivity.WilsonPolymerCross` with `β > 0`, `κ ≥ 0` and
`kpCost zHyper4 κ ≤ tau β` gives `⟪P vᵢ, P vⱼ⟫ = 0` whenever
`d(i,j) L − r₀ > (|Plaq 4 nC| + 1)|Plaq 4 nC|`. -/
theorem cross_zero_of_far_plaq {Nc nC : ℕ} [NeZero nC] (hN : Nc ≠ 0) {β κ : ℝ} (hβ : 0 < β)
    (hκ : 0 ≤ κ) (hτ : kpCost zHyper4 κ ≤ tau β) {P : E →L[ℝ] E} {v : Fin n → E}
    {d : Fin n → Fin n → ℕ} {Kx M L r₀ : ℝ} (h : WilsonPolymerCross Nc nC β P v d Kx M L r₀)
    {i j : Fin n} (hij : i ≠ j)
    (hfar : ((Fintype.card (WilsonHypercubic.Plaq 4 nC) : ℝ) + 1)
      * Fintype.card (WilsonHypercubic.Plaq 4 nC) < (d i j : ℝ) * L - r₀) :
    inner ℝ (P (v i)) (P (v j)) = 0 := by
  obtain ⟨ρ, dset, U, A, S, Λ, R, h1, h2, h3, h4, h5, -, -, h8, h9⟩ := h i j hij
  have hQ := Q_eq_zero_of_far (matchAt_wilson_of_tau (n := nC) hN hβ hκ hτ) h1 h2 h3 h4 h5 S
    (hfar.trans_le h8)
  rw [hQ, abs_zero, mul_zero, zero_mul] at h9
  exact abs_nonpos_iff.1 h9

/-- **`QFloor` is false**: with `β > 0`, `κ ≥ 0`, `8 · kpCost 16 κ ≤ tau β`, `c > 0` and `L > 0`,
the separation `D` with `D L − r₀ > farRange nC` has `Q = 0`. -/
theorem not_qFloor {Nc nC : ℕ} [NeZero nC] (hN : Nc ≠ 0) {β κ c κ' M L r₀ : ℝ} (hβ : 0 < β)
    (hκ : 0 ≤ κ) (hτ : 8 * kpCost 16 κ ≤ tau β) (hc : 0 < c) (hL : 0 < L) :
    ¬ QFloor Nc nC β c κ' M L r₀ := by
  intro hQ
  obtain ⟨D, hD⟩ := exists_nat_gt ((farRange nC + r₀) / L)
  obtain ⟨ρ, dset, U, A, S, Λ, R, h1, h2, h3, h4, h5, -, -, h8, hq⟩ := hQ D
  rw [div_lt_iff₀ hL] at hD
  have hR : ((Fintype.card (WilsonHypercubic.Link 4 nC) : ℝ) + 1)
      * Fintype.card (WilsonHypercubic.Link 4 nC) < R := by
    have : farRange nC < R := by linarith
    exact this
  have h0 := Q_eq_zero_of_far (matchAt_linkAct_of_tau (n := nC) hN hβ hκ hτ) h1 h2 h3 h4 h5 S hR
  rw [linkQ_eq _ linkSupp_nonempty_hypercubic] at h0
  rw [h0, abs_zero] at hq
  exact absurd hq (not_le.2 (mul_pos hc (Real.exp_pos _)))

/-- **The clause from `CrossDecay` and `QFloor`** at a common rate `κ'`, `C ≥ 0`, `c > 0`, with
`Kx = C / c`. Vacuous at every coupling with `8 · kpCost 16 κ ≤ tau β` for some `κ ≥ 0` and at
`L > 0`: there `QFloor` is false (`not_qFloor`). -/
theorem wilsonLinkPolymerCross_of_crossDecay {Nc nC : ℕ} [NeZero nC] {β c C κ' M L r₀ : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) {P : E →L[ℝ] E} {v : Fin n → E} {d : Fin n → Fin n → ℕ}
    (hX : CrossDecay P v d C κ' L r₀) (hQ : QFloor Nc nC β c κ' M L r₀) :
    WilsonLinkPolymerCross Nc nC β P v d (C / c) M L r₀ := by
  intro i j hij
  obtain ⟨ρ, dset, U, A, S, Λ, R, h1, h2, h3, h4, h5, h6, h7, h8, hq⟩ := hQ (d i j)
  refine ⟨ρ, dset, U, A, S, Λ, R, h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
  have hvv : 0 ≤ ‖v i‖ * ‖v j‖ := by positivity
  calc |inner ℝ (P (v i)) (P (v j))|
      ≤ C * Real.exp (-(κ' * ((d i j : ℝ) * L - r₀))) * (‖v i‖ * ‖v j‖) := hX i j hij
    _ = C / c * (c * Real.exp (-(κ' * ((d i j : ℝ) * L - r₀)))) * (‖v i‖ * ‖v j‖) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (div_nonneg hC hc.le)) hvv

/-- **The clause gives the decay of the cross terms** at the KP rate `κ`, with `C = Kx M`. -/
theorem crossDecay_of_wilsonLinkPolymerCross {Nc nC : ℕ} [NeZero nC] (hN : Nc ≠ 0) {β κ : ℝ}
    (hβ : 0 < β) (hκ : 0 ≤ κ) (hτ : 8 * kpCost 16 κ ≤ tau β) {P : E →L[ℝ] E} {v : Fin n → E}
    {d : Fin n → Fin n → ℕ} {Kx M L r₀ : ℝ} (hKx : 0 ≤ Kx)
    (h : WilsonLinkPolymerCross Nc nC β P v d Kx M L r₀) :
    CrossDecay P v d (Kx * M) κ L r₀ := by
  intro i j hij
  obtain ⟨V, _, _, w, ρ, dset, U, A, S, Λ, R, hM, hlip, hdiam, hcore, hΛ, hA, hAU, hcard, hR, hx⟩ :=
    polymerCross_of_wilsonLink hN hβ hκ hτ h i j hij
  have hcl := MatchAt.cluster_sites hM hlip hdiam hcore hΛ hA hAU S
  have hM0 : 0 ≤ M := (Nat.cast_nonneg _).trans hcard
  have hvv : 0 ≤ ‖v i‖ * ‖v j‖ := by positivity
  have hexp : Real.exp (-(κ * R)) ≤ Real.exp (-(κ * ((d i j : ℝ) * L - r₀))) :=
    Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left hR hκ])
  have hstep : (Λ.card : ℝ) * 1 * Real.exp (-(κ * R))
      ≤ M * Real.exp (-(κ * ((d i j : ℝ) * L - r₀))) := by
    rw [mul_one]
    exact mul_le_mul hcard hexp (Real.exp_pos _).le hM0
  calc |inner ℝ (P (v i)) (P (v j))| ≤ Kx * |MatchAt.Q MatchAt.meet w S A U| * (‖v i‖ * ‖v j‖) := hx
    _ ≤ Kx * ((Λ.card : ℝ) * 1 * Real.exp (-(κ * R))) * (‖v i‖ * ‖v j‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcl hKx) hvv
    _ ≤ Kx * (M * Real.exp (-(κ * ((d i j : ℝ) * L - r₀)))) * (‖v i‖ * ‖v j‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hKx) hvv
    _ = Kx * M * Real.exp (-(κ * ((d i j : ℝ) * L - r₀))) * (‖v i‖ * ‖v j‖) := by ring

/-! ## 4. The degenerate geometry -/

/-- With `A = ∅` the interaction vanishes. -/
theorem Q_empty_A {Pol : Type*} [Fintype Pol] [DecidableEq Pol] (inc : Pol → Pol → Prop)
    [DecidableRel inc] (w : Pol → ℝ) (S U : Finset Pol) : MatchAt.Q inc w S ∅ U = 0 := by
  unfold MatchAt.Q
  simp

theorem pre_empty {Pol Pol' : Type*} [Fintype Pol] [DecidableEq Pol] [DecidableEq Pol']
    (g : Pol → Pol') : pre g (∅ : Finset Pol') = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  rw [mem_pre] at hx
  exact notMem_empty _ hx

/-- **Vanishing cross terms give the clause** at every `Kx` and `M ≥ 0`, through the geometry
`A = U = S = ∅`, `Λ = ∅`, `ρ = 0`, `dset = d(i,j) L − r₀`. -/
theorem wilsonLinkPolymerCross_of_cross_zero {Nc nC : ℕ} [NeZero nC] {β Kx M L r₀ : ℝ}
    (hM : 0 ≤ M) {P : E →L[ℝ] E} {v : Fin n → E} {d : Fin n → Fin n → ℕ}
    (h0 : ∀ i j, i ≠ j → inner ℝ (P (v i)) (P (v j)) = 0) :
    WilsonLinkPolymerCross Nc nC β P v d Kx M L r₀ := by
  intro i j hij
  refine ⟨fun _ _ => 0, fun _ => (d i j : ℝ) * L - r₀, ∅, ∅, ∅, ∅, (d i j : ℝ) * L - r₀,
    fun _ _ => by simp, fun X _ _ _ _ _ => Nat.cast_nonneg _, fun Y hY => absurd hY (notMem_empty Y),
    fun y hy => absurd hy (notMem_empty y), fun X hX => absurd hX (notMem_empty X),
    fun X hX => absurd hX (notMem_empty X), by simpa using hM, le_rfl, ?_⟩
  rw [h0 i j hij, pre_empty, Q_empty_A]
  simp

/-- **A witness with `A = ∅` forces the cross term to vanish.** -/
theorem cross_zero_of_empty_A {Nc nC : ℕ} [NeZero nC] {β Kx : ℝ} {P : E →L[ℝ] E} {v : Fin n → E}
    {i j : Fin n} {S U : Finset (Finset (WilsonHypercubic.Link 4 nC))}
    (h : |inner ℝ (P (v i)) (P (v j))| ≤ Kx * |MatchAt.Q (Inc (WilsonHypercubic.bd (d := 4) (n := nC)))
      (act (Nc := Nc) (WilsonHypercubic.bd (d := 4) (n := nC)) β)
      (pre (supp (WilsonHypercubic.bd (d := 4) (n := nC))) S)
      (pre (supp (WilsonHypercubic.bd (d := 4) (n := nC))) ∅)
      (pre (supp (WilsonHypercubic.bd (d := 4) (n := nC))) U)| * (‖v i‖ * ‖v j‖)) :
    inner ℝ (P (v i)) (P (v j)) = 0 := by
  rw [pre_empty, Q_empty_A, abs_zero, mul_zero, zero_mul] at h
  exact abs_nonpos_iff.1 h

end Torus

/-! ## 5. The consumer on the Wilson box -/

section Box

variable {N : ℕ} (X : CellLinks.BoxParams N) (hN : N ≠ 0)

/-- **(A) and (B) on the Wilson box through `PolymerCross`**, from `CrossDecay` at the KP rate `κ`
and `QFloor` of one Wilson torus gas at coupling `β` with `8 · kpCost 16 κ ≤ tau β`; the constant is
`Kx = C / c`. Its hypotheses are inconsistent: `hβ`, `hκ`, `hτ`, `hc`, `hL` make `QFloor` false
(`not_qFloor`). -/
theorem relFloorM_of_crossDecay_qFloor {r K₀ : ℕ} (hrK : r ≤ K₀) {Nc nC : ℕ} [NeZero nC]
    (hNc : Nc ≠ 0) {β ρc C c κ M L r₀ A' : ℝ} {p : ℕ} (hβ : 0 < β) (hτ : 8 * kpCost 16 κ ≤ tau β)
    (hρc : 0 < ρc) (hC : 0 ≤ C) (hc : 0 < c) (hM0 : 0 ≤ M) (hκ : 0 < κ) (hL : 0 < L)
    (hA : 0 ≤ A')
    (h1 : ρc ^ 2 + C / c * M * 1 * Real.exp (κ * r₀) * A' * UniformAperture.edgeSum p
      (NonAbelianForget.edgeRate (1 / (X.a₀ / 2 ^ r / (κ * L))) 0 (X.a₀ / 2 ^ r)) < 1)
    (hD : ∀ m, 0 < m → UniformAperture.ShellCount (CellLinks.boxDist X.μ m r) A' p)
    (hQ : QFloor Nc nC β c κ M L r₀)
    (hS : ∀ m (hm : 0 < m) k (hk : K₀ ≤ k) (g : Lp ℝ 2 (X.slab hN m k).π),
      inner ℝ g (SlabKernelOperator.oneLp (X.slab hN m k).π) = 0 →
      (∀ i, ‖(X.slab hN m k).P ((X.cellChain hN r m k (hrK.trans hk) hm).piece g i)‖ ^ 2
        ≤ ρc ^ 2 * ‖(X.cellChain hN r m k (hrK.trans hk) hm).piece g i‖ ^ 2) ∧
      CrossDecay (X.slab hN m k).P ((X.cellChain hN r m k (hrK.trans hk) hm).piece g)
        (CellLinks.boxDist X.μ m r) C κ L r₀) :
    SlabMeasure.RelFloorM (X.box.slab hN) (fun _ => UniformAperture.cellRate ρc
      (C / c * M * 1 * Real.exp (κ * r₀) * A' * UniformAperture.edgeSum p
        (NonAbelianForget.edgeRate (1 / (X.a₀ / 2 ^ r / (κ * L))) 0 (X.a₀ / 2 ^ r))))
      (fun _ => K₀) :=
  MatchAt.relFloorM_of_polymerCross X hN hrK hρc (div_nonneg hC hc.le) hM0 zero_le_one hκ hL hA h1
    hD fun m hm k hk g hg => ⟨(hS m hm k hk g hg).1,
      polymerCross_of_wilsonLink hNc hβ hκ.le hτ
        (wilsonLinkPolymerCross_of_crossDecay hc hC (hS m hm k hk g hg).2 hQ)⟩

end Box

#print axioms crossDecay_iff_screens
#print axioms Z_sdiff_inactive
#print axioms Z_union
#print axioms Z_union_active
#print axioms Q_eq_zero_of_split
#print axioms Q_eq_zero_of_far
#print axioms cross_zero_of_far
#print axioms cross_zero_of_far_plaq
#print axioms not_qFloor
#print axioms wilsonLinkPolymerCross_of_crossDecay
#print axioms crossDecay_of_wilsonLinkPolymerCross
#print axioms Q_empty_A
#print axioms pre_empty
#print axioms wilsonLinkPolymerCross_of_cross_zero
#print axioms cross_zero_of_empty_A
#print axioms relFloorM_of_crossDecay_qFloor

end MassGap.CrossTerm
