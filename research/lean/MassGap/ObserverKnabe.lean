import Mathlib
import MassGap.ObserverBox
import MassGap.HeatBathGapDecay

noncomputable section

/-!
# MassGap.ObserverKnabe — the Knabe step for Wilson plus an adjacent-plaquette coupling

`BoxPatch` turns the box local gap of Wilson into a global gap through the patch system of box
patches: conditional expectations at links sharing no plaquette commute, and the pairs at zero or unit
displacement carry an excess weight. For Wilson plus an adjacent-plaquette coupling the interaction
relation is `WeightedHeatBath.RAdj`: a common plaquette, or both links on one adjacent plaquette pair.
Such links are at most two steps apart in every coordinate (`near2_of_RAdj`). The excess weight
`|pairWeight − b|` on that window keeps the pair condition, and its row sums are at most
`5184 (n⁴ − (n − 2)⁴)`.
-/

namespace MassGap.ObserverKnabe

open MassGap.HeatBath (bdT SharePlaq)
open MassGap.BoxPatch (ovc ovSet ovc_eq ovc_le ovc_zero boxWeight pairWeight_box bd_site disp_cases
  sharePlaq_disp UnitStep prod_le_of_not_unit)
open MassGap.WeightedHeatBath (RAdj adjSet Touches)

/-! ## 1. Overlaps -/

section Overlap

variable {M : ℕ}

/-- **A translate by `d` keeps at least `n − d` of the window** (`BoxPatch.ovc_eq`).

DERIVED: `1` is the successor writing the extent. -/
theorem ovc_ge_sub (n : ℕ) (hnL : n ≤ M + 1) (d : Fin (M + 1)) : n - (d : ℕ) ≤ ovc n d := by
  rw [ovc_eq n hnL]
  have hsub : Finset.range (n - (d : ℕ))
      ⊆ (Finset.range n).filter (fun t => (t + (d : ℕ)) % (M + 1) < n) := by
    intro t ht
    rw [Finset.mem_range] at ht
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  simpa using Finset.card_le_card hsub

#print axioms ovc_ge_sub

/-- **The overlap is even**: `ovc n (−d) = ovc n d` (translation by `d` maps one overlap set onto the
other).

DERIVED: `1` is the successor writing the extent. -/
theorem ovc_neg (n : ℕ) (d : Fin (M + 1)) : ovc n (-d) = ovc n d := by
  unfold ovc
  have h : ovSet n (-d) = (ovSet n d).image (fun t => t + d) := by
    ext s
    simp only [ovSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hs, hs'⟩
      exact ⟨s + -d, ⟨hs', by rw [neg_add_cancel_right]; exact hs⟩, by rw [neg_add_cancel_right]⟩
    · rintro ⟨t, ⟨ht, ht'⟩, rfl⟩
      exact ⟨ht', by rw [add_neg_cancel_right]; exact ht⟩
  rw [h, Finset.card_image_of_injective _ (add_left_injective d)]

#print axioms ovc_neg

end Overlap

/-! ## 2. The interaction window -/

section Window

variable {M : ℕ}

/-- **A displacement within two steps in every coordinate**: each coordinate is `±e` with `e ≤ 2`. -/
def Near2 (δ : WilsonHypercubic.Site 4 (M + 1)) : Prop :=
  ∀ i, ∃ e : Fin (M + 1), (e : ℕ) ≤ 2 ∧ (δ i = e ∨ δ i = -e)

/-- `Near2` is decided classically. -/
noncomputable instance : DecidablePred (Near2 (M := M)) := Classical.decPred _

/-- `(1 : Fin (M + 1))` has value at most `1`.

DERIVED: `1` is the unit. -/
theorem val_one_le : ((1 : Fin (M + 1)) : ℕ) ≤ 1 := by
  rw [Fin.val_one']
  exact Nat.mod_le _ _

#print axioms val_one_le

/-- **The sum of two unit-or-zero steps is within two steps.**

DERIVED: `0`, `1`, `−1` are the steps; `2` is the reach. -/
theorem near2_add {a b : Fin (M + 1)} (ha : a = 0 ∨ a = 1 ∨ a = -1) (hb : b = 0 ∨ b = 1 ∨ b = -1) :
    ∃ e : Fin (M + 1), (e : ℕ) ≤ 2 ∧ (a + b = e ∨ a + b = -e) := by
  have h1 := val_one_le (M := M)
  have h11 : ((1 + 1 : Fin (M + 1)) : ℕ) ≤ 2 := by
    rw [Fin.val_add]
    exact (Nat.mod_le _ _).trans (by omega)
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact ⟨0, by simp, Or.inl (by simp)⟩
  · exact ⟨1, by omega, Or.inl (by simp)⟩
  · exact ⟨1, by omega, Or.inr (by simp)⟩
  · exact ⟨1, by omega, Or.inl (by simp)⟩
  · exact ⟨1 + 1, h11, Or.inl rfl⟩
  · exact ⟨0, by simp, Or.inl (by simp)⟩
  · exact ⟨1, by omega, Or.inr (by simp)⟩
  · exact ⟨0, by simp, Or.inl (by simp)⟩
  · exact ⟨1 + 1, h11, Or.inr (by rw [neg_add])⟩

#print axioms near2_add

/-- **Links interacting under Wilson plus an adjacent coupling are within two steps**: a common
plaquette gives a unit-or-zero displacement (`BoxPatch.disp_cases`); links on two adjacent plaquettes
are joined through their shared link, two such displacements.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem near2_of_RAdj {l l' : WilsonHypercubic.Link 4 (M + 1)} (h : RAdj (bdT M) l l') :
    Near2 (l'.2 - l.2) := by
  -- two links of one plaquette
  have same : ∀ (r : WilsonHypercubic.Plaq 4 (M + 1)) (a b : WilsonHypercubic.Link 4 (M + 1)),
      a ∈ (bdT M r).map Prod.fst → b ∈ (bdT M r).map Prod.fst → ∀ i,
        (b.2 - a.2) i = 0 ∨ (b.2 - a.2) i = 1 ∨ (b.2 - a.2) i = -1 :=
    fun r a b ha hb i => disp_cases (bd_site r ha) (bd_site r hb) i
  have zero : (0 : Fin (M + 1)) = 0 ∨ (0 : Fin (M + 1)) = 1 ∨ (0 : Fin (M + 1)) = -1 :=
    Or.inl rfl
  rcases h with ⟨r, hl, hl'⟩ | ⟨pq, hpq, hl, hl'⟩
  · intro i
    have := near2_add (same r l l' hl hl' i) zero
    simpa using this
  · simp only [adjSet, Finset.mem_filter, Finset.mem_univ, true_and] at hpq
    obtain ⟨-, k, hk1, hk2⟩ := hpq
    -- the displacement through the shared link `k`
    have via : ∀ (r r' : WilsonHypercubic.Plaq 4 (M + 1)),
        k ∈ (bdT M r).map Prod.fst → k ∈ (bdT M r').map Prod.fst →
        l ∈ (bdT M r).map Prod.fst → l' ∈ (bdT M r').map Prod.fst → Near2 (l'.2 - l.2) := by
      intro r r' hkr hkr' hlr hlr' i
      have e : (l'.2 - l.2) i = (l'.2 - k.2) i + (k.2 - l.2) i := by
        simp only [Pi.sub_apply]
        abel
      rw [e]
      exact near2_add (same r' k l' hkr' hlr' i) (same r l k hlr hkr i)
    unfold Touches at hl hl'
    rcases hl with hl | hl <;> rcases hl' with hl' | hl'
    · exact via pq.1 pq.1 hk1 hk1 hl hl'
    · exact via pq.1 pq.2 hk1 hk2 hl hl'
    · exact via pq.2 pq.1 hk2 hk1 hl hl'
    · exact via pq.2 pq.2 hk2 hk2 hl hl'

#print axioms near2_of_RAdj

/-- Zero and unit displacements are within two steps.

DERIVED: `0`, `1` are the steps. -/
theorem near2_of_zero_or_unit {δ : WilsonHypercubic.Site 4 (M + 1)} (h : δ = 0 ∨ UnitStep δ) :
    Near2 δ := by
  have h1 := val_one_le (M := M)
  rcases h with rfl | ⟨j, hz, hs⟩
  · exact fun _ => ⟨0, by simp, Or.inl rfl⟩
  · intro i
    by_cases hij : i = j
    · subst hij
      rcases hs with h | h
      · exact ⟨1, by omega, Or.inl h⟩
      · exact ⟨1, by omega, Or.inr h⟩
    · exact ⟨0, by simp, Or.inl (hz i hij)⟩

#print axioms near2_of_zero_or_unit

/-- **The overlap on the window is at least `(n − 2)⁴`** (`ovc_ge_sub`, `ovc_neg`).

DERIVED: `2` is the reach; `4` is the spacetime dimension; `1` is the successor writing the
extent. -/
theorem prod_ge_of_near2 (n : ℕ) (hnL : n ≤ M + 1) {δ : WilsonHypercubic.Site 4 (M + 1)}
    (h : Near2 δ) : (n - 2) ^ 4 ≤ ∏ k, ovc n (δ k) := by
  have hk : ∀ k, n - 2 ≤ ovc n (δ k) := by
    intro k
    obtain ⟨e, he, hδ⟩ := h k
    rcases hδ with hδ | hδ
    · rw [hδ]
      exact le_trans (by omega) (ovc_ge_sub n hnL e)
    · rw [hδ, ovc_neg]
      exact le_trans (by omega) (ovc_ge_sub n hnL e)
  calc (n - 2) ^ 4 = ∏ _k : Fin 4, (n - 2) := by simp
    _ ≤ ∏ k, ovc n (δ k) := Finset.prod_le_prod' fun k _ => hk k

#print axioms prod_ge_of_near2

/-- The values within two steps of zero, as a set of at most `6`.

DERIVED: `2` is the reach; `6 = 2 · 3`, the signs times the values `0, 1, 2`. -/
def near2Set : Finset (Fin (M + 1)) :=
  (Finset.univ.filter (fun e : Fin (M + 1) => (e : ℕ) ≤ 2))
    ∪ (Finset.univ.filter (fun e : Fin (M + 1) => (e : ℕ) ≤ 2)).image (fun e => -e)

/-- DERIVED: `6 = 3 + 3`; `3` values `0, 1, 2` up to `2`. -/
theorem card_near2Set_le : (near2Set (M := M)).card ≤ 6 := by
  have h3 : (Finset.univ.filter (fun e : Fin (M + 1) => (e : ℕ) ≤ 2)).card ≤ 3 := by
    have := Finset.card_le_card_of_injOn (fun e : Fin (M + 1) => (e : ℕ))
      (s := Finset.univ.filter (fun e : Fin (M + 1) => (e : ℕ) ≤ 2)) (t := Finset.range 3) (fun e he => by
        have := (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
        exact Finset.mem_coe.mpr (Finset.mem_range.mpr (show (e : ℕ) < 3 by omega))) (fun a _ b _ h => Fin.ext h)
    simpa using this
  unfold near2Set
  refine (Finset.card_union_le _ _).trans ?_
  have := Finset.card_image_le (s := Finset.univ.filter (fun e : Fin (M + 1) => (e : ℕ) ≤ 2))
    (f := fun e => -e)
  omega

#print axioms card_near2Set_le

/-- **At most `5184 = 4 · 6⁴` links are within two steps of a given link.**

DERIVED: `4` is the spacetime dimension; `6` is `card_near2Set_le`'s bound; `1` is the successor
writing the extent; `5184 = 4 · 6⁴`. -/
theorem card_near2_le (l : WilsonHypercubic.Link 4 (M + 1)) :
    (Finset.univ.filter (fun l' : WilsonHypercubic.Link 4 (M + 1) => Near2 (l'.2 - l.2))).card
      ≤ 5184 := by
  classical
  have hsub : Finset.univ.filter (fun l' : WilsonHypercubic.Link 4 (M + 1) => Near2 (l'.2 - l.2))
      ⊆ (Finset.univ : Finset (Fin 4)) ×ˢ
          ((Fintype.piFinset fun _ : Fin 4 => near2Set (M := M)).image (fun δ => δ + l.2)) := by
    intro l' hl'
    have hn := (Finset.mem_filter.mp hl').2
    refine Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr
      ⟨l'.2 - l.2, Fintype.mem_piFinset.mpr fun i => ?_, by simp⟩⟩
    obtain ⟨e, he, hδ⟩ := hn i
    unfold near2Set
    rcases hδ with hδ | hδ
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hδ]; exact he⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, hδ.symm⟩)
  have h6 := card_near2Set_le (M := M)
  calc _ ≤ _ := Finset.card_le_card hsub
    _ = 4 * ((Fintype.piFinset fun _ : Fin 4 => near2Set (M := M)).image (fun δ => δ + l.2)).card := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    _ ≤ 4 * (Fintype.piFinset fun _ : Fin 4 => near2Set (M := M)).card :=
        Nat.mul_le_mul_left 4 Finset.card_image_le
    _ = 4 * (near2Set (M := M)).card ^ 4 := by rw [Fintype.card_piFinset]; simp
    _ ≤ 4 * 6 ^ 4 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left h6 4)
    _ = 5184 := by norm_num

#print axioms card_near2_le

/-- `Near2` is symmetric.

DERIVED: no numeral. -/
theorem near2_neg {δ : WilsonHypercubic.Site 4 (M + 1)} (h : Near2 δ) : Near2 (-δ) := by
  intro i
  obtain ⟨e, he, hδ⟩ := h i
  refine ⟨e, he, ?_⟩
  rcases hδ with hδ | hδ
  · exact Or.inr (by rw [Pi.neg_apply, hδ])
  · exact Or.inl (by rw [Pi.neg_apply, hδ, neg_neg])

#print axioms near2_neg

end Window

/-! ## 3. The excess weight and the pair condition -/

section Excess

open MassGap.KnabeCriterion (pairWeight)
open MassGap.BoxPatch (bR)

variable {M : ℕ}

/-- **The excess weight of Wilson plus an adjacent coupling**: `|pairWeight − b|` within two steps,
`0` elsewhere and on the diagonal. -/
def adjExcess (n : ℕ) (l l' : WilsonHypercubic.Link 4 (M + 1)) : ℝ :=
  if l = l' then 0 else if Near2 (l'.2 - l.2) then |pairWeight (boxWeight (M := M) n) l l' - bR n| else 0

/-- **The pair condition**: a pair out of the window commutes (supplied as `hP` for every pair not
in `RAdj`) and has pair weight at most `b` (`BoxPatch.prod_le_of_not_unit`); a pair in the window is
within its excess.

DERIVED: `1` is the least box side; `2` is the two windows fitting in the circle; `4` is the
spacetime dimension. -/
theorem adj_pair_cond (n : ℕ) (hn : 1 ≤ n) (hL : 2 * n ≤ M + 1)
    {l l' : WilsonHypercubic.Link 4 (M + 1)} (hll : l ≠ l') {P : Prop}
    (hP : ¬ RAdj (bdT M) l l' → P) :
    (P ∧ pairWeight (boxWeight (M := M) n) l l' ≤ bR n)
      ∨ |pairWeight (boxWeight (M := M) n) l l' - bR n| ≤ adjExcess (M := M) n l l' := by
  by_cases hN : Near2 (l'.2 - l.2)
  · right
    unfold adjExcess
    rw [if_neg hll, if_pos hN]
  · left
    refine ⟨hP fun hR => hN (near2_of_RAdj hR), ?_⟩
    have h0 : l'.2 - l.2 ≠ 0 := fun h => hN (near2_of_zero_or_unit (Or.inl h))
    have hu : ¬ UnitStep (l'.2 - l.2) := fun h => hN (near2_of_zero_or_unit (Or.inr h))
    have hle := prod_le_of_not_unit n hn hL h0 hu
    have hbN : ((((n - 1) ^ 2 * n ^ 2 : ℕ)) : ℝ) = bR n := by
      unfold bR
      push_cast [Nat.cast_sub hn]
      ring
    rw [pairWeight_box, ← hbN]
    exact_mod_cast hle

#print axioms adj_pair_cond

/-- **One excess entry is at most `n⁴ − (n − 2)⁴`**: both the pair weight and `b = n²(n − 1)²` lie in
`[(n − 2)⁴, n⁴]` (`prod_ge_of_near2`, `BoxPatch.ovc_le`).

DERIVED: `2` is the reach and the least side; `4` is the spacetime dimension; `1` is the successor
writing the extent. -/
theorem adjExcess_le (n : ℕ) (hn : 2 ≤ n) (hL : 2 * n ≤ M + 1) (l l' : WilsonHypercubic.Link 4 (M + 1)) :
    adjExcess (M := M) n l l'
      ≤ if Near2 (l'.2 - l.2) then (n : ℝ) ^ 4 - ((n : ℝ) - 2) ^ 4 else 0 := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hgap : 0 ≤ (n : ℝ) ^ 4 - ((n : ℝ) - 2) ^ 4 := by
    have h1 : ((n : ℝ) - 2) ^ 4 ≤ (n : ℝ) ^ 4 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 4
    linarith
  unfold adjExcess
  split_ifs with h1 h2 h2
  · exact hgap
  · exact le_rfl
  · rw [pairWeight_box]
    have hlo : (((n - 2) ^ 4 : ℕ) : ℝ) ≤ ((∏ k : Fin 4, ovc n ((l'.2 - l.2) k) : ℕ) : ℝ) := by
      exact_mod_cast prod_ge_of_near2 n (by omega) h2
    have hhi : ((∏ k : Fin 4, ovc n ((l'.2 - l.2) k) : ℕ) : ℝ) ≤ (n : ℝ) ^ 4 := by
      have : ∏ k : Fin 4, ovc n ((l'.2 - l.2) k) ≤ n ^ 4 := by
        calc ∏ k : Fin 4, ovc n ((l'.2 - l.2) k) ≤ ∏ _k : Fin 4, n :=
              Finset.prod_le_prod' fun k _ => ovc_le n (by omega) _
          _ = n ^ 4 := by simp
      exact_mod_cast this
    have hcast : (((n - 2) ^ 4 : ℕ) : ℝ) = ((n : ℝ) - 2) ^ 4 := by
      push_cast [Nat.cast_sub hn]
      ring
    rw [hcast] at hlo
    have hb1 : ((n : ℝ) - 2) ^ 4 ≤ bR n := by
      unfold bR
      have : ((n : ℝ) - 2) ^ 2 ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      have h0 : 0 ≤ ((n : ℝ) - 2) ^ 2 := sq_nonneg _
      calc ((n : ℝ) - 2) ^ 4 = (((n : ℝ) - 2) ^ 2) ^ 2 := by ring
        _ ≤ ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 := pow_le_pow_left₀ h0 this 2
        _ = (n : ℝ) ^ 2 * ((n : ℝ) - 1) ^ 2 := by ring
    have hb2 : bR n ≤ (n : ℝ) ^ 4 := by
      unfold bR
      have : (n : ℝ) * ((n : ℝ) - 1) ≤ (n : ℝ) * (n : ℝ) := by nlinarith
      have h0 : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      calc (n : ℝ) ^ 2 * ((n : ℝ) - 1) ^ 2 = ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 := by ring
        _ ≤ ((n : ℝ) * (n : ℝ)) ^ 2 := pow_le_pow_left₀ h0 this 2
        _ = (n : ℝ) ^ 4 := by ring
    rw [abs_le]
    constructor <;> linarith
  · exact le_rfl

#print axioms adjExcess_le

/-- The excess weight is symmetric (`near2_neg`, `KnabeCriterion.pairWeight`).

DERIVED: no numeral. -/
theorem adjExcess_symm (n : ℕ) (l l' : WilsonHypercubic.Link 4 (M + 1)) :
    adjExcess (M := M) n l l' = adjExcess n l' l := by
  have hpw : pairWeight (boxWeight (M := M) n) l l' = pairWeight (boxWeight (M := M) n) l' l := by
    unfold pairWeight
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hiff : Near2 (l'.2 - l.2) ↔ Near2 (l.2 - l'.2) := by
    constructor
    · intro h
      have := near2_neg h
      rwa [neg_sub] at this
    · intro h
      have := near2_neg h
      rwa [neg_sub] at this
  unfold adjExcess
  by_cases h : l = l'
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]
    by_cases hN : Near2 (l'.2 - l.2)
    · rw [if_pos hN, if_pos (hiff.mp hN), hpw]
    · rw [if_neg hN, if_neg (fun h' => hN (hiff.mpr h'))]

#print axioms adjExcess_symm

/-- **Row sums of the excess**: at most `5184 (n⁴ − (n − 2)⁴)` (`adjExcess_le`, `card_near2_le`).

DERIVED: `5184` is `card_near2_le`'s bound; `2`, `4` as in `adjExcess_le`. -/
theorem adj_row (n : ℕ) (hn : 2 ≤ n) (hL : 2 * n ≤ M + 1) (l : WilsonHypercubic.Link 4 (M + 1)) :
    ∑ l', adjExcess (M := M) n l l' ≤ 5184 * ((n : ℝ) ^ 4 - ((n : ℝ) - 2) ^ 4) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hgap : 0 ≤ (n : ℝ) ^ 4 - ((n : ℝ) - 2) ^ 4 := by
    have h1 : ((n : ℝ) - 2) ^ 4 ≤ (n : ℝ) ^ 4 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 4
    linarith
  calc ∑ l', adjExcess (M := M) n l l'
      ≤ ∑ l', (if Near2 (l'.2 - l.2) then (n : ℝ) ^ 4 - ((n : ℝ) - 2) ^ 4 else 0) :=
        Finset.sum_le_sum fun l' _ => adjExcess_le n hn hL l l'
    _ = ((n : ℝ) ^ 4 - ((n : ℝ) - 2) ^ 4)
          * (Finset.univ.filter (fun l' : WilsonHypercubic.Link 4 (M + 1) =>
              Near2 (l'.2 - l.2))).card := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ((n : ℝ) ^ 4 - ((n : ℝ) - 2) ^ 4) * 5184 := by
        have h := card_near2_le l
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast h) hgap
    _ = 5184 * ((n : ℝ) ^ 4 - ((n : ℝ) - 2) ^ 4) := mul_comm _ _

#print axioms adj_row

/-- **Column sums of the excess** (`adjExcess_symm`, `adj_row`).

DERIVED: as `adj_row`; `5184` is `card_near2_le`'s bound. -/
theorem adj_col (n : ℕ) (hn : 2 ≤ n) (hL : 2 * n ≤ M + 1) (l' : WilsonHypercubic.Link 4 (M + 1)) :
    ∑ l, adjExcess (M := M) n l l' ≤ 5184 * ((n : ℝ) ^ 4 - ((n : ℝ) - 2) ^ 4) := by
  calc ∑ l, adjExcess (M := M) n l l' = ∑ l, adjExcess (M := M) n l' l :=
        Finset.sum_congr rfl fun l _ => adjExcess_symm n l l'
    _ ≤ _ := adj_row n hn hL l'

#print axioms adj_col

/-- The excess weight is non-negative.

DERIVED: `0` is the sign. -/
theorem adjExcess_nonneg (n : ℕ) (l l' : WilsonHypercubic.Link 4 (M + 1)) :
    0 ≤ adjExcess (M := M) n l l' := by
  unfold adjExcess
  split_ifs
  · exact le_rfl
  · exact abs_nonneg _
  · exact le_rfl

#print axioms adjExcess_nonneg

end Excess

/-! ## 4. The patch system and the global gap -/

section Patch

open MassGap.SUN (SU)
open MassGap.PeriodicState (torusObs)
open MassGap.KnabeCriterion (PatchSystem periodicGaugeInvSubmodule selfAdj_id_sub idem_id_sub
  comm_id_sub)
open MassGap.BoxPatch (bR bR_pos box_cover box_cover2)
open MassGap.HeatBath (restrictConf continuous_torusObs)
open MassGap.WeightedTorus (TorusWeight wCondExp wForm wForm_symm wForm_nonneg wCondExp_selfAdj
  wCondExp_idem wLift torusObs_wLift WBoxLocalGap)
open MassGap.ObserverBox (adjWeight)

variable {N : ℕ}

/-- **Conditional expectations of Wilson plus an adjacent coupling commute at non-interacting links**
(`WeightedHeatBath.wAvg_comm` for `wilsonAdjLocal`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem wCondExp_comm_adj (β lam : ℝ) (M : ℕ) {l l' : WilsonHypercubic.Link 4 (M + 1)} (hll : l ≠ l')
    (hs : ¬ RAdj (bdT M) l l') (x : ↥(periodicGaugeInvSubmodule (N := N) M)) :
    wCondExp (adjWeight β lam) M l (wCondExp (adjWeight β lam) M l' x)
      = wCondExp (adjWeight β lam) M l' (wCondExp (adjWeight β lam) M l x) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro U
  show MassGap.WeightedHeatBath.wAvg ((adjWeight (N := N) β lam).Φ M) l
      (torusObs M (wLift (adjWeight β lam) M l' (x : C(GibbsSpec.IConf (SU N), ℝ))))
      (restrictConf M U)
    = MassGap.WeightedHeatBath.wAvg ((adjWeight (N := N) β lam).Φ M) l'
      (torusObs M (wLift (adjWeight β lam) M l (x : C(GibbsSpec.IConf (SU N), ℝ))))
      (restrictConf M U)
  rw [torusObs_wLift, torusObs_wLift]
  exact MassGap.WeightedHeatBath.wAvg_comm
    (MassGap.WeightedHeatBath.wilsonAdjLocal (N := N) (bdT M) β lam) hll hs
    (continuous_torusObs M _) _

#print axioms wCondExp_comm_adj

/-- **The box patch system of Wilson plus an adjacent coupling** at extent index `j` and box side
`n` with `2 ≤ n ≤ j + 1`: `wForm`, `hₗ = id − E_l`, box patches, `a₁ = a₂ = n⁴`, `b = n²(n − 1)²`,
`e = 5184 (n⁴ − (n − 2)⁴)`.

DERIVED: `4` is the spacetime dimension and the exponent of `a₁`, `a₂`; `2 * j + 1` is the index of
the even-extent family and the `+ 1` its successor writing the extent; `2` is the least side;
`5184` is `card_near2_le`'s bound. -/
def adjPatchSystem (β lam : ℝ) (n j : ℕ) (hn : 2 ≤ n) (hj : n ≤ j + 1) : PatchSystem where
  E := ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))
  ι := WilsonHypercubic.Link 4 (2 * j + 1 + 1)
  κ := WilsonHypercubic.Site 4 (2 * j + 1 + 1)
  B := wForm (adjWeight β lam) j
  symm := wForm_symm (adjWeight β lam) j
  nonneg := wForm_nonneg (adjWeight β lam) j
  h := fun l => (LinearMap.id : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))
      →ₗ[ℝ] ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) - wCondExp (adjWeight β lam) (2 * j + 1) l
  selfAdj := fun l => selfAdj_id_sub _ _ (wCondExp_selfAdj (adjWeight β lam) j l)
  idem := fun l => idem_id_sub _ (wCondExp_idem (adjWeight β lam) (2 * j + 1) l)
  c := boxWeight n
  w := adjExcess n
  a₁ := (n : ℝ) ^ 4
  a₂ := (n : ℝ) ^ 4
  b := bR n
  e := 5184 * ((n : ℝ) ^ 4 - ((n : ℝ) - 2) ^ 4)
  cover := box_cover n (by omega)
  cover2 := box_cover2 n (by omega)
  pair := fun l l' hll => adj_pair_cond n (by omega) (by omega) hll
    (fun hs x => comm_id_sub _ _ (fun y => wCondExp_comm_adj β lam (2 * j + 1) hll hs y) x)
  w_nonneg := adjExcess_nonneg n
  row := adj_row n hn (by omega)
  col := adj_col n hn (by omega)

/-- **The global gap of the observer theory's heat-bath dynamics**, `SU(2)`, `β ≤ 1/200`,
`|λ| ≤ 1/20000`: at box side `n = 100000` and every extent index `j` with `n ≤ j + 1`, the patch
system has global gap `1/10` (`ObserverBox.obsBox_localGap`, `KnabeCriterion.globalGap_of_localGap`,
`globalGap_mono`).

DERIVED: `100000` is the box side; `1/10` is below the Knabe constant `(γ n⁴ − n⁴ + b − e)/b = 0.177…`
at `γ = 593/1000`; `2` is the rank. Inherited: `1/200`, `1/20000` (denominators `200`, `20000`) the
CHOSEN coupling window of `AdjacentFibre.fibreHyp_adj_single`. -/
theorem obs_globalGap {β lam : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 200) (hl : |lam| ≤ 1 / 20000)
    (j : ℕ) (hj : 100000 ≤ j + 1) :
    (adjPatchSystem (N := 2) β lam 100000 j (by norm_num) hj).GlobalGap (1 / 10) := by
  set S := adjPatchSystem (N := 2) β lam 100000 j (by norm_num) hj with hS
  have hb : 0 < S.b := bR_pos (by norm_num)
  have hloc : S.LocalGap (593 / 1000) := fun k x =>
    MassGap.ObserverBox.obsBox_localGap hβ0 hβ hl 100000 j hj k x
  refine S.globalGap_mono ?_ (S.globalGap_of_localGap hb hloc)
  show (1 : ℝ) / 10 ≤ (593 / 1000 * S.a₁ - S.a₂ + S.b - S.e) / S.b
  show (1 : ℝ) / 10 ≤ (593 / 1000 * ((100000 : ℕ) : ℝ) ^ 4 - ((100000 : ℕ) : ℝ) ^ 4 + bR 100000
    - 5184 * (((100000 : ℕ) : ℝ) ^ 4 - (((100000 : ℕ) : ℝ) - 2) ^ 4)) / bR 100000
  unfold bR
  norm_num

#print axioms obs_globalGap

/-! ## 5. Clustering of the observer theory from its dynamical gap -/

/-- The observer box side is at least `2`.

DERIVED: `2` is the least side; `100000` is the box side. -/
theorem two_le_side : 2 ≤ 100000 := by norm_num

/-- **The observer patch system** at box side `100000`, `SU(2)`.

DERIVED: `2` is the rank; `100000` is the box side. -/
def obsSys (β lam : ℝ) (j : ℕ) (hj : 100000 ≤ j + 1) : PatchSystem :=
  adjPatchSystem (N := 2) β lam 100000 j two_le_side hj

open MassGap.HeatBathGapDecay (Far nrm Titer cov_bound_exp H_form_le_card)

/-- **The neighbours of a link**: the links within two steps. -/
def obsNb (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1)) : Finset (WilsonHypercubic.Link 4 (M + 1)) :=
  Finset.univ.filter fun l' => Near2 (l'.2 - l.2)

/-- **The `hₗ` of the observer patch system commute off the neighbours** (`wCondExp_comm_adj`,
`near2_of_RAdj`).

DERIVED: `100000` is the box side; `2` is the rank and the least side. -/
theorem adj_hcomm (β lam : ℝ) (j : ℕ) (hj : 100000 ≤ j + 1) (l l' : WilsonHypercubic.Link 4 (2 * j + 1 + 1))
    (hl' : l' ∉ obsNb (2 * j + 1) l)
    (u : (obsSys β lam j hj).E) :
    (obsSys β lam j hj).B
      ((obsSys β lam j hj).h l'
          ((obsSys β lam j hj).h l u)
        - (obsSys β lam j hj).h l
          ((obsSys β lam j hj).h l' u))
      ((obsSys β lam j hj).h l'
          ((obsSys β lam j hj).h l u)
        - (obsSys β lam j hj).h l
          ((obsSys β lam j hj).h l' u)) = 0 := by
  have hN : ¬ Near2 (l'.2 - l.2) := fun h => hl' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hll : l ≠ l' := fun h => hN (by rw [h, sub_self]; exact near2_of_zero_or_unit (Or.inl rfl))
  have hR : ¬ RAdj (bdT (2 * j + 1)) l l' := fun h => hN (near2_of_RAdj h)
  have e := comm_id_sub _ _ (fun y => wCondExp_comm_adj (N := 2) β lam (2 * j + 1) hll hR y) u
  have e' : (obsSys β lam j hj).h l'
        ((obsSys β lam j hj).h l u)
      - (obsSys β lam j hj).h l
        ((obsSys β lam j hj).h l' u) = 0 := by
    rw [sub_eq_zero]
    exact e.symm
  rw [e']
  simp

#print axioms adj_hcomm

set_option maxHeartbeats 1000000 in
/-- **Exponential clustering of the observer theory, at fixed separation level**
(`HeatBathGapDecay.cov_bound_exp` on `adjPatchSystem`): for observables `f` read on `A` and `g` read
on `C`, `C` at neighbour level `k` from `A`, and the ergodic limit `L` of the lazy heat bath,
`|⟨f, g⟩ − L| ≤ s |C| ‖f‖ y⁻ᵏ e^{2 · 5184 y s} ‖g‖ + 20 e^{−s/20} |A| ‖f‖ ‖g‖` at every `y ≥ 1` and
every `s`. The neighbour count `5184` (`card_near2_le`), the commutation off the neighbours
(`wCondExp_comm_adj`, `near2_of_RAdj`) and the gap `1/10` (`obs_globalGap`) are proved; the ergodic
limit is the hypothesis `herg`, as in the Wilson chain.

DERIVED: `5184` is `card_near2_le`'s bound; `1/10` is `obs_globalGap`'s gap, `20 = 2/(1/10)` and
`1/20 = (1/10)/2`; `100000` is the box side; `2` is the rank and the commutator's two terms.
Inherited: `1/200`, `1/20000` (denominators `200`, `20000`) the CHOSEN coupling window of
`AdjacentFibre.fibreHyp_adj_single`. -/
theorem obs_cluster {β lam : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 200) (hl : |lam| ≤ 1 / 20000)
    (j : ℕ) (hj : 100000 ≤ j + 1)
    (A C : Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1)))
    (f g : (obsSys β lam j hj).E)
    (hf : ∀ l, l ∉ A → (obsSys β lam j hj).B
      ((obsSys β lam j hj).h l f)
      ((obsSys β lam j hj).h l f) = 0)
    (hg : ∀ l, l ∉ C → (obsSys β lam j hj).B
      ((obsSys β lam j hj).h l g)
      ((obsSys β lam j hj).h l g) = 0)
    (k : ℕ) (hfar : ∀ l ∈ C, Far (obsNb (2 * j + 1)) A k l) {L : ℝ}
    (herg : Filter.Tendsto (fun M => (obsSys β lam j hj).B
      (Titer (obsSys β lam j hj)
        (Fintype.card (WilsonHypercubic.Link 4 (2 * j + 1 + 1)) : ℝ) M f) g)
      Filter.atTop (nhds L))
    {y : ℝ} (hy : 1 ≤ y) (s : ℕ) :
    |(obsSys β lam j hj).B f g - L|
      ≤ s * C.card * (nrm (obsSys β lam j hj) f
          * ((y⁻¹) ^ k * Real.exp (2 * (5184 : ℕ) * y * s)))
          * nrm (obsSys β lam j hj) g
        + 2 / (1 / 10) * Real.exp (-(1 / 10 * s / 2))
          * (A.card * nrm (obsSys β lam j hj) f)
          * nrm (obsSys β lam j hj) g := by
  have hcard : 0 < Fintype.card (WilsonHypercubic.Link 4 (2 * j + 1 + 1)) := Fintype.card_pos
  have hc1 : (1 / 10 : ℝ) ≤ (Fintype.card (WilsonHypercubic.Link 4 (2 * j + 1 + 1)) : ℝ) := by
    have : (1 : ℝ) ≤ Fintype.card (WilsonHypercubic.Link 4 (2 * j + 1 + 1)) := by exact_mod_cast hcard
    linarith
  exact cov_bound_exp _ hcard (H_form_le_card _) (by norm_num) hc1 (obs_globalGap hβ0 hβ hl j hj)
    (obsNb (2 * j + 1)) (fun l => card_near2_le l) (adj_hcomm β lam j hj) hy A C f g hf hg k hfar
    herg s

#print axioms obs_cluster

end Patch

end MassGap.ObserverKnabe
