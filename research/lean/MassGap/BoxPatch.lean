import Mathlib
import MassGap.HeatBath

noncomputable section

/-!
# MassGap.BoxPatch — box patches in four dimensions, the heat-bath system, and the finite check

## What it gives

1. **Overlaps on a circle.** `ovc n d` counts the `t : Fin (M + 1)` with `t < n` and `t + d < n`
   (the overlap of the window `[0, n)` with its translate by `d`). With `2n ≤ M + 1`: `ovc n 0 = n`,
   `ovc n 1 = ovc n (−1) = n − 1`, and `ovc n d ≤ n − 2` for every other `d` (`ovc_zero`, `ovc_one`,
   `ovc_neg_one`, `ovc_far`).
2. **Box patches.** A patch is a corner `k` of the torus; the link `(μ, x)` lies in it when every
   coordinate of `x − k` is below `n` (`InBox`), weight `boxWeight n k l ∈ {0, 1}`. The pair weight of
   `l, l'` is `∏_μ ovc n ((l'.2 − l.2) μ)` (`pairWeight_box`); every link lies in `n⁴` patches
   (`box_cover`, `box_cover2`).
3. **Multiplicities.** With `b = n²(n − 1)²` (`bR`) and the excess weight `boxExcess` equal to
   `n²(2n − 1)` for another link at the same base site, `n²(n − 1)` at a unit displacement (`UnitStep`)
   and `0` otherwise: every pair `l ≠ l'` either shares no plaquette and has pair weight at most `b`,
   or has pair weight within `boxExcess l l'` of `b` (`box_pair_cond`); the excess weights have row
   and column sums at most `e = n²(38n − 35)` (`eR`, `box_row`, `box_col`). Links of a common
   plaquette sit at displacements with at most two non-zero entries, each `±1`
   (`sharePlaq_disp`), so their pair weight is at least `b` (`prod_ge_of_share`).
4. **The heat-bath system.** `boxHeatBath hN β n j` is a `KnabeCriterion.WilsonHeatBath` with the
   conditional expectations of `MassGap.HeatBath` and the box data, for `1 ≤ n ≤ j + 1`;
   `onePatch` is the one-patch system at every `j`, so `WilsonHeatBath hN β j` is inhabited
   (`wilsonHeatBath_nonempty`). Its Knabe constant is
   `boxKnabe n γ = (γn² − 40n + 36)/(n − 1)²` (`knabeConst_box`), positive exactly when
   `γ > (40n − 36)/n²` (`boxKnabe_pos_iff`).
5. **The finite check at box patches.** `BoxLocalGap hN β n γ`: every box patch operator
   `boxOp β n j k = Σ_l boxWeight n k l • (id − torusCondExp l)` has local gap `γ` for `torusForm`,
   at every `j` with `n ≤ j + 1`. `BoxPatchGap hN β n γ`: `2 ≤ n`, `γ > (40n − 36)/n²` and
   `BoxLocalGap`. `patchGapCheck_of_boxPatchGap`: `BoxPatchGap → KnabeCriterion.PatchGapCheck`;
   `boxFamily_check` names its family and `c₀ = boxKnabe n γ`.

An independent brute-force count on the tori `(n, L) ∈ {(2,4), (2,5), (2,6), (3,6), (3,7)}`, with the
pair weight counted box by box and the plaquettes over every ordered pair of directions, agrees with
`a₁`, `a₂`, the pair condition and the row bound; there the optimal excess sum
`Σ_{l' ≠ l} max(pw − b, 0)` equals `n²(38n − 35)`, so `e` is attained. Moving `b` by one either way, or
lowering `e` by one, fails the count.
-/

namespace MassGap.BoxPatch

open MassGap MassGap.HeatBath MassGap.KnabeCriterion
open MassGap.SUN (SU)
open MassGap.PeriodicState (torusObs)

/-! ## 1. Overlaps of a window with its translates -/

section Overlap

variable {M : ℕ}

/-- The `t : Fin (M + 1)` in the window `[0, n)` whose translate by `d` is in the window.

DERIVED: `1` is the successor writing the extent. -/
def ovSet (n : ℕ) (d : Fin (M + 1)) : Finset (Fin (M + 1)) :=
  Finset.univ.filter (fun t : Fin (M + 1) => (t : ℕ) < n ∧ ((t + d : Fin (M + 1)) : ℕ) < n)

/-- The overlap count `#ovSet n d`.

DERIVED: `1` is the successor writing the extent. -/
def ovc (n : ℕ) (d : Fin (M + 1)) : ℕ := (ovSet n d).card

/-- The overlap as a count over `range n` in `ℕ` (`Fin.val_add`, `Fin.sum_univ_eq_sum_range`).

DERIVED: `1` is the successor writing the extent. -/
theorem ovc_eq (n : ℕ) (hnL : n ≤ M + 1) (d : Fin (M + 1)) :
    ovc n d = ((Finset.range n).filter (fun t => (t + (d : ℕ)) % (M + 1) < n)).card := by
  have h1 : ovc n d = ∑ t : Fin (M + 1),
      (if (t : ℕ) < n ∧ ((t : ℕ) + (d : ℕ)) % (M + 1) < n then 1 else 0) := by
    unfold ovc ovSet
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Fin.val_add]
  have h2 : ((Finset.range n).filter (fun t => (t + (d : ℕ)) % (M + 1) < n)).card
      = ((Finset.range (M + 1)).filter (fun t => t < n ∧ (t + (d : ℕ)) % (M + 1) < n)).card := by
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h, h'⟩
      exact ⟨lt_of_lt_of_le h hnL, h, h'⟩
    · rintro ⟨_, h, h'⟩
      exact ⟨h, h'⟩
  rw [h1, h2, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun t => if t < n ∧ (t + (d : ℕ)) % (M + 1) < n then 1 else 0)
    (M + 1)

#print axioms ovc_eq

/-- `ovc n 0 = n` for `n ≤ M + 1`.

DERIVED: `0` is the zero translate; `1` is the successor writing the extent. -/
theorem ovc_zero (n : ℕ) (hnL : n ≤ M + 1) : ovc n (0 : Fin (M + 1)) = n := by
  rw [ovc_eq n hnL, Fin.val_zero, Finset.filter_true_of_mem, Finset.card_range]
  intro t ht
  rw [Finset.mem_range] at ht
  rw [add_zero, Nat.mod_eq_of_lt (show t < M + 1 by omega)]
  exact ht

#print axioms ovc_zero

/-- `ovc n 1 = n − 1` for `1 ≤ n` and `2n ≤ M + 1`.

DERIVED: `1` is the unit translate, the least box side, the unit loss and the successor writing the
extent; `2` is the two windows fitting in the circle. -/
theorem ovc_one (n : ℕ) (hn : 1 ≤ n) (hL : 2 * n ≤ M + 1) : ovc n (1 : Fin (M + 1)) = n - 1 := by
  have h1 : ((1 : Fin (M + 1)) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (show 1 < M + 1 by omega)]
  rw [ovc_eq (M := M) n (by omega), h1]
  have hset : (Finset.range n).filter (fun t => (t + 1) % (M + 1) < n) = Finset.range (n - 1) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨ht, h2⟩
      rw [Nat.mod_eq_of_lt (show t + 1 < M + 1 by omega)] at h2
      omega
    · intro ht
      refine ⟨by omega, ?_⟩
      rw [Nat.mod_eq_of_lt (show t + 1 < M + 1 by omega)]
      omega
  rw [hset, Finset.card_range]

#print axioms ovc_one

/-- `ovc n (−1) = n − 1` for `1 ≤ n` and `2n ≤ M + 1` (`Fin.coe_neg_one`).

DERIVED: `1` is the unit translate, the least box side, the unit loss and the successor writing the
extent; `2` is the two windows fitting in the circle. -/
theorem ovc_neg_one (n : ℕ) (hn : 1 ≤ n) (hL : 2 * n ≤ M + 1) :
    ovc n (-1 : Fin (M + 1)) = n - 1 := by
  rw [ovc_eq (M := M) n (by omega), Fin.coe_neg_one]
  have hset : (Finset.range n).filter (fun t => (t + M) % (M + 1) < n) = Finset.Ico 1 n := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨ht, h2⟩
      refine ⟨?_, ht⟩
      by_contra h0
      have ht0 : t = 0 := by omega
      rw [ht0, zero_add, Nat.mod_eq_of_lt (show M < M + 1 by omega)] at h2
      omega
    · rintro ⟨h0, ht⟩
      refine ⟨ht, ?_⟩
      rw [Nat.mod_eq_sub_mod (show t + M ≥ M + 1 by omega),
        Nat.mod_eq_of_lt (show t + M - (M + 1) < M + 1 by omega)]
      omega
  rw [hset, Nat.card_Ico]

#print axioms ovc_neg_one

/-- `ovc n d ≤ n − 2` for `d ∉ {0, 1, −1}`, `1 ≤ n` and `2n ≤ M + 1`: the translate meets the window
in `[0, n − d)` or in `[M + 1 − d, n)`, never both.

DERIVED: `0`, `1` and `−1` are the three translates excluded; `1` is also the least box side and the
successor writing the extent; `2` is the two windows fitting in the circle and the least distance of
a far translate. -/
theorem ovc_far (n : ℕ) (hn : 1 ≤ n) (hL : 2 * n ≤ M + 1) (d : Fin (M + 1)) (h0 : d ≠ 0)
    (h1 : d ≠ 1) (h2 : d ≠ -1) : ovc n d ≤ n - 2 := by
  have hd0 : (d : ℕ) ≠ 0 := fun h => h0 (Fin.ext (by rw [h, Fin.val_zero]))
  have hd1 : (d : ℕ) ≠ 1 := fun h => h1 (Fin.ext (by
    rw [h, Fin.val_one', Nat.mod_eq_of_lt (show 1 < M + 1 by omega)]))
  have hdM : (d : ℕ) ≠ M := fun h => h2 (Fin.ext (by rw [h, Fin.coe_neg_one]))
  have hdlt : (d : ℕ) < M + 1 := d.isLt
  rw [ovc_eq (M := M) n (by omega)]
  have hsub : (Finset.range n).filter (fun t => (t + (d : ℕ)) % (M + 1) < n)
      ⊆ Finset.range (n - (d : ℕ)) ∪ Finset.Ico (M + 1 - (d : ℕ)) n := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_range] at ht
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    rcases Nat.lt_or_ge (t + (d : ℕ)) (M + 1) with h | h
    · rw [Nat.mod_eq_of_lt h] at ht
      left
      omega
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (show t + (d : ℕ) - (M + 1) < M + 1 by omega)]
        at ht
      right
      omega
  calc ((Finset.range n).filter (fun t => (t + (d : ℕ)) % (M + 1) < n)).card
      ≤ (Finset.range (n - (d : ℕ)) ∪ Finset.Ico (M + 1 - (d : ℕ)) n).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.range (n - (d : ℕ))).card + (Finset.Ico (M + 1 - (d : ℕ)) n).card :=
        Finset.card_union_le _ _
    _ = (n - (d : ℕ)) + (n - (M + 1 - (d : ℕ))) := by rw [Finset.card_range, Nat.card_Ico]
    _ ≤ n - 2 := by omega

#print axioms ovc_far

/-- `ovc n d ≤ n` for `n ≤ M + 1`.

DERIVED: `1` is the successor writing the extent. -/
theorem ovc_le (n : ℕ) (hnL : n ≤ M + 1) (d : Fin (M + 1)) : ovc n d ≤ n := by
  rw [ovc_eq n hnL]
  exact (Finset.card_filter_le _ _).trans (Finset.card_range n).le

#print axioms ovc_le

/-- `ovc n d ≤ n − 1` for `d ≠ 0`.

DERIVED: `0` is the translate excluded; `1` is the least box side, the unit loss and the successor
writing the extent; `2` is the two windows fitting in the circle. -/
theorem ovc_ne_zero (n : ℕ) (hn : 1 ≤ n) (hL : 2 * n ≤ M + 1) (d : Fin (M + 1)) (h0 : d ≠ 0) :
    ovc n d ≤ n - 1 := by
  by_cases h1 : d = 1
  · exact le_of_eq (by rw [h1, ovc_one n hn hL])
  · by_cases h2 : d = -1
    · exact le_of_eq (by rw [h2, ovc_neg_one n hn hL])
    · exact (ovc_far n hn hL d h0 h1 h2).trans (by omega)

#print axioms ovc_ne_zero

end Overlap

/-! ## 2. Box weights and pair weights -/

section Box

variable {M : ℕ}

/-- **The box of side `n`**: every coordinate below `n`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
def InBox (n : ℕ) (v : WilsonHypercubic.Site 4 (M + 1)) : Prop := ∀ k, (v k : ℕ) < n

instance instDecidableInBox (n : ℕ) : DecidablePred (InBox (M := M) n) :=
  fun v => inferInstanceAs (Decidable (∀ k, (v k : ℕ) < n))

/-- **The box patch weight**: `1` when the link's base site lies in the box with corner `k`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent; `1` and `0` are
the indicator's values. -/
def boxWeight (n : ℕ) (k : WilsonHypercubic.Site 4 (M + 1)) (l : WilsonHypercubic.Link 4 (M + 1)) :
    ℝ :=
  if InBox n (l.2 - k) then 1 else 0

/-- The indicator of `v` and `v + δ` both in the box.

DERIVED: `4` is the spacetime dimension; `1` and `0` are the indicator's values. -/
def pairInd (n : ℕ) (δ v : WilsonHypercubic.Site 4 (M + 1)) : ℝ :=
  if InBox n v ∧ InBox n (v + δ) then 1 else 0

/-- The sites `v` with `v` and `v + δ` in the box form the product of the coordinate overlaps.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem filter_box_eq_piFinset (n : ℕ) (δ : WilsonHypercubic.Site 4 (M + 1)) :
    Finset.univ.filter (fun v : WilsonHypercubic.Site 4 (M + 1) => InBox n v ∧ InBox n (v + δ))
      = Fintype.piFinset (fun k => ovSet n (δ k)) := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, ovSet, InBox,
    Pi.add_apply]
  constructor
  · intro h k
    exact ⟨h.1 k, h.2 k⟩
  · intro h
    exact ⟨fun k => (h k).1, fun k => (h k).2⟩

#print axioms filter_box_eq_piFinset

/-- **The pair weight of two links is the product of the coordinate overlaps** at their base
displacement: `pairWeight (boxWeight n) l l' = ∏_μ ovc n ((l'.2 − l.2) μ)` (reindex the corners by
`k ↦ l.2 − k`, `Fintype.card_piFinset`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem pairWeight_box (n : ℕ) (l l' : WilsonHypercubic.Link 4 (M + 1)) :
    pairWeight (boxWeight (M := M) n) l l'
      = ((∏ k : Fin 4, ovc n ((l'.2 - l.2) k) : ℕ) : ℝ) := by
  have hpt : ∀ k : WilsonHypercubic.Site 4 (M + 1),
      boxWeight n k l * boxWeight n k l' = pairInd n (l'.2 - l.2) (l.2 - k) := by
    intro k
    have hk : l.2 - k + (l'.2 - l.2) = l'.2 - k := by abel
    unfold boxWeight pairInd
    rw [hk]
    by_cases h1 : InBox n (l.2 - k) <;> by_cases h2 : InBox n (l'.2 - k) <;> simp [h1, h2]
  have hsum : pairWeight (boxWeight (M := M) n) l l'
      = ∑ v : WilsonHypercubic.Site 4 (M + 1), pairInd n (l'.2 - l.2) v := by
    unfold pairWeight
    rw [Finset.sum_congr rfl (fun k _ => hpt k)]
    exact Equiv.sum_comp (Equiv.subLeft l.2) (pairInd n (l'.2 - l.2))
  rw [hsum]
  show ∑ v : WilsonHypercubic.Site 4 (M + 1),
      (if InBox n v ∧ InBox n (v + (l'.2 - l.2)) then (1 : ℝ) else 0)
    = ((∏ k : Fin 4, (ovSet n ((l'.2 - l.2) k)).card : ℕ) : ℝ)
  rw [Finset.sum_boole, filter_box_eq_piFinset, Fintype.card_piFinset]

#print axioms pairWeight_box

/-- **Squared cover weight** `a₂ = n⁴`: the pair weight of a link with itself.

DERIVED: `4` is the spacetime dimension and the exponent (one factor `n` per direction); `1` is the
successor writing the extent. -/
theorem box_cover2 (n : ℕ) (hnL : n ≤ M + 1) (l : WilsonHypercubic.Link 4 (M + 1)) :
    pairWeight (boxWeight (M := M) n) l l = (n : ℝ) ^ 4 := by
  rw [pairWeight_box, sub_self]
  have h : ∀ k : Fin 4, ovc (M := M) n ((0 : WilsonHypercubic.Site 4 (M + 1)) k) = n :=
    fun k => ovc_zero n hnL
  rw [Finset.prod_congr rfl (fun k _ => h k), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  exact Nat.cast_pow n 4

#print axioms box_cover2

/-- **Cover weight** `a₁ = n⁴`: every link lies in `n⁴` box patches (the weights are `0` or `1`, so
the cover weight is the squared one).

DERIVED: `4` is the spacetime dimension and the exponent; `1` is the successor writing the
extent. -/
theorem box_cover (n : ℕ) (hnL : n ≤ M + 1) (l : WilsonHypercubic.Link 4 (M + 1)) :
    ∑ k, boxWeight (M := M) n k l = (n : ℝ) ^ 4 := by
  rw [← box_cover2 n hnL l]
  unfold pairWeight
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold boxWeight
  split_ifs <;> norm_num

#print axioms box_cover

end Box

/-! ## 3. Products over the four directions -/

section ProdFour

/-- A product over `Fin 4` with every factor off `i` equal to `c` is `a i · c³`.

DERIVED: `4` is the spacetime dimension; `3` is the number of other directions. -/
theorem prod_single_coord (a : Fin 4 → ℕ) (c : ℕ) (i : Fin 4) (h : ∀ k, k ≠ i → a k = c) :
    ∏ k, a k = a i * c ^ 3 := by
  rw [Fintype.prod_eq_mul_prod_compl i a]
  congr 1
  have hc : ({i} : Finset (Fin 4))ᶜ.card = 3 := by
    have h' := Finset.card_add_card_compl ({i} : Finset (Fin 4))
    rw [Finset.card_singleton, Fintype.card_fin] at h'
    omega
  have h2 : ∏ k ∈ ({i} : Finset (Fin 4))ᶜ, a k = ∏ k ∈ ({i} : Finset (Fin 4))ᶜ, c :=
    Finset.prod_congr rfl (fun k hk =>
      h k (fun hki => (Finset.mem_compl.mp hk) (Finset.mem_singleton.mpr hki)))
  rw [h2, Finset.prod_const, hc]

#print axioms prod_single_coord

/-- A product over `Fin 4` with two factors at most `m` and all at most `c` is at most `m²c²`.

DERIVED: `4` is the spacetime dimension; `2` is the number of small factors and of the others. -/
theorem prod_le_two (a : Fin 4 → ℕ) {m c : ℕ} (i j : Fin 4) (hij : i ≠ j) (hi : a i ≤ m)
    (hj : a j ≤ m) (hle : ∀ k, a k ≤ c) : ∏ k, a k ≤ m ^ 2 * c ^ 2 := by
  rw [← Finset.prod_mul_prod_compl ({i, j} : Finset (Fin 4)) a]
  have hS : ({i, j} : Finset (Fin 4)).card = 2 := Finset.card_pair hij
  have hSc : ({i, j} : Finset (Fin 4))ᶜ.card = 2 := by
    have h' := Finset.card_add_card_compl ({i, j} : Finset (Fin 4))
    rw [hS, Fintype.card_fin] at h'
    omega
  have h1 : ∏ k ∈ ({i, j} : Finset (Fin 4)), a k ≤ m ^ 2 := by
    have h' := Finset.prod_le_pow_card ({i, j} : Finset (Fin 4)) a m (fun k hk => by
      rcases Finset.mem_insert.mp hk with hk' | hk'
      · rw [hk']
        exact hi
      · rw [Finset.mem_singleton.mp hk']
        exact hj)
    rwa [hS] at h'
  have h2 : ∏ k ∈ ({i, j} : Finset (Fin 4))ᶜ, a k ≤ c ^ 2 := by
    have h' := Finset.prod_le_pow_card ({i, j} : Finset (Fin 4))ᶜ a c (fun k _ => hle k)
    rwa [hSc] at h'
  exact Nat.mul_le_mul h1 h2

#print axioms prod_le_two

/-- `m²c² ≤ m^s c^t` for `m ≤ c`, `s ≤ 2`, `s + t = 4`.

DERIVED: `2` is the number of small factors allowed; `4` is the spacetime dimension. -/
theorem pow_mix {m c s t : ℕ} (hmc : m ≤ c) (hs : s ≤ 2) (hst : s + t = 4) :
    m ^ 2 * c ^ 2 ≤ m ^ s * c ^ t := by
  have ht : t = 2 - s + 2 := by omega
  calc m ^ 2 * c ^ 2 = m ^ s * (m ^ (2 - s) * c ^ 2) := by
        rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hs]
    _ ≤ m ^ s * (c ^ (2 - s) * c ^ 2) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hmc _))
    _ = m ^ s * c ^ t := by rw [← pow_add, ht]

#print axioms pow_mix

/-- A product over `Fin 4` with every factor at least `m ≤ c` and every factor off `{μ, ν}` equal to
`c` is at least `m²c²`.

DERIVED: `4` is the spacetime dimension; `2` is the number of directions of a plane. -/
theorem prod_ge_two (a : Fin 4 → ℕ) {m c : ℕ} (hmc : m ≤ c) (μ ν : Fin 4)
    (hge : ∀ k, m ≤ a k) (hoff : ∀ k, k ≠ μ → k ≠ ν → a k = c) :
    m ^ 2 * c ^ 2 ≤ ∏ k, a k := by
  have hoff' : ∀ k ∈ ({μ, ν} : Finset (Fin 4))ᶜ, a k = c := by
    intro k hk
    have hk' : k ∉ ({μ, ν} : Finset (Fin 4)) := Finset.mem_compl.mp hk
    refine hoff k (fun h => hk' ?_) (fun h => hk' ?_)
    · rw [h]
      exact Finset.mem_insert_self μ {ν}
    · rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self ν)
  have hS : ({μ, ν} : Finset (Fin 4)).card ≤ 2 := Finset.card_le_two
  have hsum : ({μ, ν} : Finset (Fin 4)).card + ({μ, ν} : Finset (Fin 4))ᶜ.card = 4 := by
    rw [Finset.card_add_card_compl, Fintype.card_fin]
  have h1 : m ^ ({μ, ν} : Finset (Fin 4)).card ≤ ∏ k ∈ ({μ, ν} : Finset (Fin 4)), a k :=
    Finset.pow_card_le_prod _ a m (fun k _ => hge k)
  have h2 : ∏ k ∈ ({μ, ν} : Finset (Fin 4))ᶜ, a k = c ^ ({μ, ν} : Finset (Fin 4))ᶜ.card := by
    rw [Finset.prod_congr rfl hoff', Finset.prod_const]
  rw [← Finset.prod_mul_prod_compl ({μ, ν} : Finset (Fin 4)) a, h2]
  calc m ^ 2 * c ^ 2
      ≤ m ^ ({μ, ν} : Finset (Fin 4)).card * c ^ ({μ, ν} : Finset (Fin 4))ᶜ.card :=
        pow_mix hmc hS hsum
    _ ≤ (∏ k ∈ ({μ, ν} : Finset (Fin 4)), a k) * c ^ ({μ, ν} : Finset (Fin 4))ᶜ.card :=
        Nat.mul_le_mul_right _ h1

#print axioms prod_ge_two

/-- `(n − 2) n³ ≤ (n − 1)² n²` in `ℕ`: `(m + 1)²(m + 2)² − m(m + 2)³ = (m + 2)²`.

DERIVED: `2` and `1` are the losses of a far and a unit translate; `3` and `2` count the unshifted
directions. -/
theorem key_ineq (n : ℕ) : (n - 2) * n ^ 3 ≤ (n - 1) ^ 2 * n ^ 2 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have h0 : n - 2 = 0 := by omega
    rw [h0, zero_mul]
    exact Nat.zero_le _
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have e1 : m + 2 - 2 = m := by omega
    have e2 : m + 2 - 1 = m + 1 := by omega
    rw [e1, e2]
    exact Nat.le.intro (show m * (m + 2) ^ 3 + (m + 2) ^ 2 = (m + 1) ^ 2 * (m + 2) ^ 2 by ring)

#print axioms key_ineq

end ProdFour

/-! ## 4. Displacements -/

section Geometry

variable {M : ℕ}

/-- **A unit displacement**: one coordinate `±1`, the others `0`.

DERIVED: `4` is the spacetime dimension; `1` is the unit step and the successor writing the extent;
`0` is the unmoved coordinate. -/
def UnitStep (δ : WilsonHypercubic.Site 4 (M + 1)) : Prop :=
  ∃ i, (∀ k, k ≠ i → δ k = 0) ∧ (δ i = 1 ∨ δ i = -1)

/-- `UnitStep` is decidable: its body, restated so instance search finds the `Fintype` and
`DecidableEq` instances of the sites.

DERIVED: `0` is the unmoved coordinate and `1` the unit step, the literals of `UnitStep` itself. -/
instance instDecidableUnitStep : DecidablePred (UnitStep (M := M)) := fun δ =>
  inferInstanceAs (Decidable (∃ i, (∀ k, k ≠ i → δ k = 0) ∧ (δ i = 1 ∨ δ i = -1)))

/-- At most `8` unit displacements: the image of `Fin 4 × {1, −1}` under `Pi.single`.

DERIVED: `8 = 4 · 2`, the directions times the two signs. -/
theorem card_unitStep_le : (Finset.univ.filter (UnitStep (M := M))).card ≤ 8 := by
  have hsub : Finset.univ.filter (UnitStep (M := M))
      ⊆ ((Finset.univ : Finset (Fin 4)) ×ˢ ({1, -1} : Finset (Fin (M + 1)))).image
          (fun p => (Pi.single p.1 p.2 : WilsonHypercubic.Site 4 (M + 1))) := by
    intro δ hδ
    obtain ⟨i, hz, hs⟩ := (Finset.mem_filter.mp hδ).2
    rw [Finset.mem_image]
    refine ⟨(i, δ i), ?_, ?_⟩
    · rw [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨Finset.mem_univ i, hs⟩
    · funext k
      show (Pi.single i (δ i) : WilsonHypercubic.Site 4 (M + 1)) k = δ k
      by_cases hk : k = i
      · rw [hk, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hk, hz k hk]
  calc (Finset.univ.filter (UnitStep (M := M))).card
      ≤ (((Finset.univ : Finset (Fin 4)) ×ˢ ({1, -1} : Finset (Fin (M + 1)))).image
          (fun p => (Pi.single p.1 p.2 : WilsonHypercubic.Site 4 (M + 1)))).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.univ : Finset (Fin 4)) ×ˢ ({1, -1} : Finset (Fin (M + 1)))).card :=
        Finset.card_image_le
    _ = 4 * ({1, -1} : Finset (Fin (M + 1))).card := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    _ ≤ 4 * 2 := Nat.mul_le_mul_left 4 Finset.card_le_two

#print axioms card_unitStep_le

/-- The negative of a unit displacement is one.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem unitStep_neg {δ : WilsonHypercubic.Site 4 (M + 1)} (h : UnitStep δ) : UnitStep (-δ) := by
  obtain ⟨i, hz, hs⟩ := h
  refine ⟨i, fun k hk => ?_, ?_⟩
  · rw [Pi.neg_apply, hz k hk, neg_zero]
  · rw [Pi.neg_apply]
    rcases hs with h | h
    · right
      rw [h]
    · left
      rw [h, neg_neg]

#print axioms unitStep_neg

/-- The base sites of the links of a plaquette are its base site and its two unit shifts.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem bd_site (q : WilsonHypercubic.Plaq 4 (M + 1)) {l : WilsonHypercubic.Link 4 (M + 1)}
    (h : l ∈ (bdT M q).map Prod.fst) :
    l.2 = q.2 ∨ l.2 = WilsonHypercubic.shift q.1.1 q.2 ∨ l.2 = WilsonHypercubic.shift q.1.2 q.2 := by
  simp only [bdT, WilsonHypercubic.bd, List.map_cons, List.map_nil, List.mem_cons,
    List.mem_nil_iff, or_false] at h
  rcases h with h | h | h | h <;> rw [h]
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inl rfl

#print axioms bd_site

/-- Each coordinate of `x`, `shift μ x`, `shift ν x` is `x k` or `x k + 1`, and `x k` off `{μ, ν}`.

DERIVED: `4` is the spacetime dimension; `1` is the unit step and the successor writing the
extent. -/
theorem site_cases {μ ν : Fin 4} {x s : WilsonHypercubic.Site 4 (M + 1)}
    (hs : s = x ∨ s = WilsonHypercubic.shift μ x ∨ s = WilsonHypercubic.shift ν x) (k : Fin 4) :
    (s k = x k ∨ s k = x k + 1) ∧ (k ≠ μ → k ≠ ν → s k = x k) := by
  rcases hs with rfl | rfl | rfl
  · exact ⟨Or.inl rfl, fun _ _ => rfl⟩
  · by_cases hk : k = μ
    · rw [hk]
      refine ⟨Or.inr ?_, fun h _ => absurd rfl h⟩
      show Function.update x μ (x μ + 1) μ = x μ + 1
      rw [Function.update_self]
    · have e : WilsonHypercubic.shift μ x k = x k := by
        show Function.update x μ (x μ + 1) k = x k
        rw [Function.update_of_ne hk]
      exact ⟨Or.inl e, fun _ _ => e⟩
  · by_cases hk : k = ν
    · rw [hk]
      refine ⟨Or.inr ?_, fun _ h => absurd rfl h⟩
      show Function.update x ν (x ν + 1) ν = x ν + 1
      rw [Function.update_self]
    · have e : WilsonHypercubic.shift ν x k = x k := by
        show Function.update x ν (x ν + 1) k = x k
        rw [Function.update_of_ne hk]
      exact ⟨Or.inl e, fun _ _ => e⟩

#print axioms site_cases

/-- The displacement between two such base sites has every coordinate in `{0, 1, −1}`.

DERIVED: `4` is the spacetime dimension; `0`, `1`, `−1` are the three differences of `x k` and
`x k + 1`. -/
theorem disp_cases {μ ν : Fin 4} {x s s' : WilsonHypercubic.Site 4 (M + 1)}
    (hs : s = x ∨ s = WilsonHypercubic.shift μ x ∨ s = WilsonHypercubic.shift ν x)
    (hs' : s' = x ∨ s' = WilsonHypercubic.shift μ x ∨ s' = WilsonHypercubic.shift ν x)
    (k : Fin 4) : (s' - s) k = 0 ∨ (s' - s) k = 1 ∨ (s' - s) k = -1 := by
  rw [Pi.sub_apply]
  rcases (site_cases hs k).1 with h | h <;> rcases (site_cases hs' k).1 with h' | h' <;>
    rw [h, h']
  · left
    exact sub_self _
  · right
    left
    exact add_sub_cancel_left _ _
  · right
    right
    exact sub_add_cancel_left _ _
  · left
    exact sub_self _

#print axioms disp_cases

/-- **Links of a common plaquette**: their base displacement vanishes off two directions and has
every coordinate in `{0, 1, −1}`.

DERIVED: `4` is the spacetime dimension; `0`, `1`, `−1` are the coordinate differences. -/
theorem sharePlaq_disp {l l' : WilsonHypercubic.Link 4 (M + 1)} (h : SharePlaq (bdT M) l l') :
    ∃ μ ν : Fin 4, (∀ k, k ≠ μ → k ≠ ν → (l'.2 - l.2) k = 0) ∧
      ∀ k, ((l'.2 - l.2) k = 0 ∨ (l'.2 - l.2) k = 1 ∨ (l'.2 - l.2) k = -1) := by
  obtain ⟨q, hq, hq'⟩ := h
  refine ⟨q.1.1, q.1.2, fun k hk1 hk2 => ?_,
    fun k => disp_cases (bd_site q hq) (bd_site q hq') k⟩
  rw [Pi.sub_apply, (site_cases (bd_site q hq') k).2 hk1 hk2,
    (site_cases (bd_site q hq) k).2 hk1 hk2, sub_self]

#print axioms sharePlaq_disp

/-- **Pair weight away from zero and unit displacements**: for `δ ≠ 0` not a unit displacement,
`∏_μ ovc n (δ μ) ≤ (n − 1)² n²` (two moved coordinates: `prod_le_two`; one far coordinate:
`ovc_far`, `key_ineq`).

DERIVED: `4` is the spacetime dimension; `0` is the zero displacement excluded; `1` is the least box
side, the successor writing the extent and the loss of a unit translate in `n − 1`; `2` is the two
windows fitting in the circle and, as exponents, the two directions at a unit loss and the two at
full overlap in `b = (n − 1)² n²`. -/
theorem prod_le_of_not_unit (n : ℕ) (hn : 1 ≤ n) (hL : 2 * n ≤ M + 1)
    {δ : WilsonHypercubic.Site 4 (M + 1)} (h0 : δ ≠ 0) (hu : ¬ UnitStep δ) :
    ∏ k, ovc n (δ k) ≤ (n - 1) ^ 2 * n ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, δ i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact h0 (funext hcon)
  by_cases h2 : ∃ j, j ≠ i ∧ δ j ≠ 0
  · obtain ⟨j, hji, hj⟩ := h2
    exact prod_le_two (fun k => ovc n (δ k)) i j (Ne.symm hji) (ovc_ne_zero n hn hL (δ i) hi)
      (ovc_ne_zero n hn hL (δ j) hj) (fun k => ovc_le n (by omega) (δ k))
  · push_neg at h2
    have hne1 : δ i ≠ 1 := fun h => hu ⟨i, h2, Or.inl h⟩
    have hne2 : δ i ≠ -1 := fun h => hu ⟨i, h2, Or.inr h⟩
    have hfar := ovc_far n hn hL (δ i) hi hne1 hne2
    have hprod : ∏ k, ovc n (δ k) = ovc n (δ i) * n ^ 3 :=
      prod_single_coord (fun k => ovc n (δ k)) n i (fun k hk => by
        show ovc n (δ k) = n
        rw [h2 k hk]
        exact ovc_zero (M := M) n (by omega))
    rw [hprod]
    calc ovc n (δ i) * n ^ 3 ≤ (n - 2) * n ^ 3 := Nat.mul_le_mul_right _ hfar
      _ ≤ (n - 1) ^ 2 * n ^ 2 := key_ineq n

#print axioms prod_le_of_not_unit

/-- **Pair weight of links of a common plaquette** is at least `(n − 1)² n²` (`sharePlaq_disp`,
`prod_ge_two`).

DERIVED: `4` is the spacetime dimension; `1` is the loss of a unit translate; `2` is the two
windows fitting in the circle and the two directions of a plane. -/
theorem prod_ge_of_share (n : ℕ) (hn : 1 ≤ n) (hL : 2 * n ≤ M + 1)
    {l l' : WilsonHypercubic.Link 4 (M + 1)} (hs : SharePlaq (bdT M) l l') :
    (n - 1) ^ 2 * n ^ 2 ≤ ∏ k, ovc n ((l'.2 - l.2) k) := by
  obtain ⟨μ, ν, hz, h01⟩ := sharePlaq_disp hs
  refine prod_ge_two (fun k => ovc n ((l'.2 - l.2) k)) (Nat.sub_le n 1) μ ν (fun k => ?_)
    (fun k hk1 hk2 => ?_)
  · show n - 1 ≤ ovc n ((l'.2 - l.2) k)
    rcases h01 k with h | h | h
    · rw [h, ovc_zero (M := M) n (by omega)]
      exact Nat.sub_le n 1
    · exact le_of_eq (by rw [h, ovc_one n hn hL])
    · exact le_of_eq (by rw [h, ovc_neg_one n hn hL])
  · show ovc n ((l'.2 - l.2) k) = n
    rw [hz k hk1 hk2]
    exact ovc_zero (M := M) n (by omega)

#print axioms prod_ge_of_share

end Geometry

/-! ## 5. Excess weights and the pair condition -/

section Excess

variable {M : ℕ}

/-- `b = n²(n − 1)²`, the pair weight of links at a displacement `e_μ − e_ν`.

DERIVED: `2` is the number of directions of the displacement moved and unmoved; `1` is the loss of a
unit translate. -/
def bR (n : ℕ) : ℝ := (n : ℝ) ^ 2 * ((n : ℝ) - 1) ^ 2

/-- `e = n²(38n − 35) = 3 · n²(2n − 1) + 32 · n²(n − 1)`: three other links at the same base, and
`4 · 8` links at a unit displacement.

DERIVED: `38 = 3 · 2 + 32` and `35 = 3 + 32`; `3` is the other directions, `32 = 4 · 8` the links
at a unit displacement. -/
def eR (n : ℕ) : ℝ := (n : ℝ) ^ 2 * (38 * (n : ℝ) - 35)

/-- **The excess weight**: `n²(2n − 1)` for another link at the same base site, `n²(n − 1)` at a unit
displacement, `0` otherwise.

DERIVED: `2n − 1 = (n⁴ − b)/n²` and `n − 1 = (n³(n − 1) − b)/n²`; `4` is the spacetime dimension;
`1` is the successor writing the extent. -/
def boxExcess (n : ℕ) (l l' : WilsonHypercubic.Link 4 (M + 1)) : ℝ :=
  if l = l' then 0
  else if l'.2 - l.2 = 0 then (n : ℝ) ^ 2 * (2 * n - 1)
  else if UnitStep (l'.2 - l.2) then (n : ℝ) ^ 2 * (n - 1)
  else 0

/-- The excess weight is symmetric (`unitStep_neg`, `neg_sub`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem boxExcess_symm (n : ℕ) (l l' : WilsonHypercubic.Link 4 (M + 1)) :
    boxExcess (M := M) n l l' = boxExcess n l' l := by
  unfold boxExcess
  have e2 : l.2 - l'.2 = -(l'.2 - l.2) := (neg_sub _ _).symm
  by_cases h1 : l = l'
  · rw [if_pos h1, if_pos h1.symm]
  · rw [if_neg h1, if_neg (Ne.symm h1)]
    by_cases h2 : l'.2 - l.2 = 0
    · have h2' : l.2 - l'.2 = 0 := by rw [e2, h2, neg_zero]
      rw [if_pos h2, if_pos h2']
    · have h2' : ¬ (l.2 - l'.2 = 0) := by
        rw [e2, neg_eq_zero]
        exact h2
      rw [if_neg h2, if_neg h2']
      by_cases h3 : UnitStep (l'.2 - l.2)
      · have h3' : UnitStep (l.2 - l'.2) := by
          rw [e2]
          exact unitStep_neg h3
        rw [if_pos h3, if_pos h3']
      · have h3' : ¬ UnitStep (l.2 - l'.2) := by
          rw [e2]
          intro h
          apply h3
          have h'' := unitStep_neg h
          rwa [neg_neg] at h''
        rw [if_neg h3, if_neg h3']

#print axioms boxExcess_symm

/-- The excess weight is non-negative for `1 ≤ n`.

DERIVED: `0` is the sign asserted; `1` is the least box side and the successor writing the extent;
`4` is the spacetime dimension. -/
theorem boxExcess_nonneg (n : ℕ) (hn : 1 ≤ n) (l l' : WilsonHypercubic.Link 4 (M + 1)) :
    0 ≤ boxExcess (M := M) n l l' := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold boxExcess
  split_ifs <;> first
    | exact le_refl 0
    | exact mul_nonneg (sq_nonneg _) (by linarith)

#print axioms boxExcess_nonneg

/-- The bound on the excess weight at a direction `ν` and a displacement `δ`: `boxExcess`'s value at
the zero displacement (nothing at `μ = ν`, where the second link is the first) plus its value at a
unit displacement.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. The body's values
are `boxExcess`'s. -/
def excessBound (n : ℕ) (μ ν : Fin 4) (δ : WilsonHypercubic.Site 4 (M + 1)) : ℝ :=
  (if δ = 0 then (if μ = ν then (0 : ℝ) else (n : ℝ) ^ 2 * (2 * n - 1)) else 0)
    + (if UnitStep δ then (n : ℝ) ^ 2 * (n - 1) else 0)

/-- The excess weight is at most `excessBound` at the displacement of the second link.

DERIVED: `1` is the least box side and the successor writing the extent; `4` is the spacetime
dimension. -/
theorem boxExcess_le_bound (n : ℕ) (hn : 1 ≤ n) (l : WilsonHypercubic.Link 4 (M + 1)) (ν : Fin 4)
    (y : WilsonHypercubic.Site 4 (M + 1)) :
    boxExcess n l (ν, y) ≤ excessBound n l.1 ν (y - l.2) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hB : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (n - 1) := mul_nonneg (sq_nonneg _) (by linarith)
  show (if l = (ν, y) then (0 : ℝ) else if y - l.2 = 0 then (n : ℝ) ^ 2 * (2 * n - 1)
      else if UnitStep (y - l.2) then (n : ℝ) ^ 2 * (n - 1) else 0)
    ≤ (if y - l.2 = 0 then (if l.1 = ν then (0 : ℝ) else (n : ℝ) ^ 2 * (2 * n - 1)) else 0)
      + (if UnitStep (y - l.2) then (n : ℝ) ^ 2 * (n - 1) else 0)
  by_cases h1 : l = (ν, y)
  · have h2 : y - l.2 = 0 := sub_eq_zero.mpr (congrArg Prod.snd h1).symm
    have h3 : l.1 = ν := congrArg Prod.fst h1
    rw [if_pos h1, if_pos h2, if_pos h3, zero_add]
    split_ifs <;> linarith
  · rw [if_neg h1]
    by_cases h2 : y - l.2 = 0
    · have h3 : ¬ l.1 = ν := fun h3 => h1 (Prod.ext h3 (sub_eq_zero.mp h2).symm)
      rw [if_pos h2, if_pos h2, if_neg h3]
      split_ifs <;> linarith
    · exact le_of_eq (by rw [if_neg h2, if_neg h2, zero_add])

#print axioms boxExcess_le_bound

/-- `Σ_ν (if μ = ν then 0 else A) = 3A` over the four directions.

DERIVED: `3` is the other directions; `4` is the spacetime dimension; `0` is the value on the
diagonal `μ = ν`. -/
theorem sum_ite_ne_eq (μ : Fin 4) (A : ℝ) :
    ∑ ν : Fin 4, (if μ = ν then (0 : ℝ) else A) = 3 * A := by
  have h1 : ∑ ν : Fin 4, (if μ = ν then (0 : ℝ) else A)
      = ∑ ν : Fin 4, (A - (if μ = ν then A else 0)) :=
    Finset.sum_congr rfl (fun ν _ => by by_cases h : μ = ν <;> simp [h])
  rw [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ μ), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

#print axioms sum_ite_ne_eq

/-- **Row sums of the excess weights**: `Σ_{l'} boxExcess n l l' ≤ n²(38n − 35)`: the three other
links at the same base, and in each of the four directions at most eight unit displacements
(`card_unitStep_le`).

DERIVED: `1` is the least box side and the successor writing the extent; `4` is the spacetime
dimension. -/
theorem box_row (n : ℕ) (hn : 1 ≤ n) (l : WilsonHypercubic.Link 4 (M + 1)) :
    ∑ l', boxExcess (M := M) n l l' ≤ eR n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hB : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (n - 1) := mul_nonneg (sq_nonneg _) (by linarith)
  have hδ : ∀ ν : Fin 4, ∑ δ : WilsonHypercubic.Site 4 (M + 1), excessBound n l.1 ν δ
      ≤ (if l.1 = ν then (0 : ℝ) else (n : ℝ) ^ 2 * (2 * n - 1)) + 8 * ((n : ℝ) ^ 2 * (n - 1)) := by
    intro ν
    unfold excessBound
    rw [Finset.sum_add_distrib]
    have h1 : ∑ δ : WilsonHypercubic.Site 4 (M + 1),
        (if δ = 0 then (if l.1 = ν then (0 : ℝ) else (n : ℝ) ^ 2 * (2 * n - 1)) else 0)
        = (if l.1 = ν then (0 : ℝ) else (n : ℝ) ^ 2 * (2 * n - 1)) :=
      (Finset.sum_ite_eq' Finset.univ (0 : WilsonHypercubic.Site 4 (M + 1))
        (fun _ => (if l.1 = ν then (0 : ℝ) else (n : ℝ) ^ 2 * (2 * n - 1)))).trans
        (if_pos (Finset.mem_univ _))
    have h2 : ∑ δ : WilsonHypercubic.Site 4 (M + 1),
        (if UnitStep δ then (n : ℝ) ^ 2 * (n - 1) else 0)
        = ((Finset.univ.filter (UnitStep (M := M))).card : ℝ) * ((n : ℝ) ^ 2 * (n - 1)) := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have h3 : ((Finset.univ.filter (UnitStep (M := M))).card : ℝ) ≤ 8 := by
      exact_mod_cast card_unitStep_le
    rw [h1, h2]
    have h4 := mul_le_mul_of_nonneg_right h3 hB
    linarith
  calc ∑ l', boxExcess (M := M) n l l'
      = ∑ ν : Fin 4, ∑ y : WilsonHypercubic.Site 4 (M + 1), boxExcess n l (ν, y) :=
        Fintype.sum_prod_type _
    _ ≤ ∑ ν : Fin 4, ∑ y : WilsonHypercubic.Site 4 (M + 1), excessBound n l.1 ν (y - l.2) :=
        Finset.sum_le_sum (fun ν _ => Finset.sum_le_sum (fun y _ => boxExcess_le_bound n hn l ν y))
    _ = ∑ ν : Fin 4, ∑ δ : WilsonHypercubic.Site 4 (M + 1), excessBound n l.1 ν δ :=
        Finset.sum_congr rfl (fun ν _ => Equiv.sum_comp (Equiv.subRight l.2) (excessBound n l.1 ν))
    _ ≤ ∑ ν : Fin 4,
          ((if l.1 = ν then (0 : ℝ) else (n : ℝ) ^ 2 * (2 * n - 1)) + 8 * ((n : ℝ) ^ 2 * (n - 1))) :=
        Finset.sum_le_sum (fun ν _ => hδ ν)
    _ = 3 * ((n : ℝ) ^ 2 * (2 * n - 1)) + 32 * ((n : ℝ) ^ 2 * (n - 1)) := by
        rw [Finset.sum_add_distrib, sum_ite_ne_eq l.1, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ = eR n := by
        unfold eR
        ring

#print axioms box_row

/-- **Column sums of the excess weights**: `Σ_l boxExcess n l l' ≤ n²(38n − 35)` (`boxExcess_symm`,
`box_row`).

DERIVED: `1` is the least box side and the successor writing the extent; `4` is the spacetime
dimension. -/
theorem box_col (n : ℕ) (hn : 1 ≤ n) (l' : WilsonHypercubic.Link 4 (M + 1)) :
    ∑ l, boxExcess (M := M) n l l' ≤ eR n := by
  rw [Finset.sum_congr rfl (fun l _ => boxExcess_symm n l l')]
  exact box_row n hn l'

#print axioms box_col

/-- **The pair condition at box patches.** For `l ≠ l'` and any `P` that follows from sharing no
plaquette: either `P` holds and the pair weight is at most `b`, or the pair weight is within
`boxExcess n l l'` of `b`. The proof takes the first branch exactly when the base displacement is
neither zero nor a unit step and the links share no plaquette; `boxHeatBath` takes `P` to be the
commutation of the two conditional expectations (`torusCondExp_comm`).

DERIVED: `1` is the least box side; `2` is the two windows fitting in the circle; `4` is the
spacetime dimension. -/
theorem box_pair_cond (n : ℕ) (hn : 1 ≤ n) (hL : 2 * n ≤ M + 1)
    {l l' : WilsonHypercubic.Link 4 (M + 1)} (hll : l ≠ l') {P : Prop}
    (hP : ¬ SharePlaq (bdT M) l l' → P) :
    (P ∧ pairWeight (boxWeight (M := M) n) l l' ≤ bR n)
      ∨ |pairWeight (boxWeight (M := M) n) l l' - bR n| ≤ boxExcess (M := M) n l l' := by
  have hpw := pairWeight_box (M := M) n l l'
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbN : ((((n - 1) ^ 2 * n ^ 2 : ℕ)) : ℝ) = bR n := by
    unfold bR
    push_cast [Nat.cast_sub hn]
    ring
  by_cases h0 : l'.2 - l.2 = 0
  · right
    have hprod : (∏ k : Fin 4, ovc n ((l'.2 - l.2) k)) = n ^ 4 := by
      rw [h0]
      have h : ∀ k : Fin 4, ovc (M := M) n ((0 : WilsonHypercubic.Site 4 (M + 1)) k) = n :=
        fun k => ovc_zero (M := M) n (by omega)
      rw [Finset.prod_congr rfl (fun k _ => h k), Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
    have hw : boxExcess (M := M) n l l' = (n : ℝ) ^ 2 * (2 * n - 1) := by
      unfold boxExcess
      rw [if_neg hll, if_pos h0]
    rw [hpw, hprod, hw, Nat.cast_pow]
    have e : (n : ℝ) ^ 4 - bR n = (n : ℝ) ^ 2 * (2 * n - 1) := by
      unfold bR
      ring
    rw [e]
    exact le_of_eq (abs_of_nonneg (mul_nonneg (sq_nonneg _) (by linarith)))
  · by_cases hu : UnitStep (l'.2 - l.2)
    · right
      obtain ⟨i, hz, hs⟩ := hu
      have hi : ovc (M := M) n ((l'.2 - l.2) i) = n - 1 := by
        rcases hs with h | h
        · rw [h]
          exact ovc_one n hn hL
        · rw [h]
          exact ovc_neg_one n hn hL
      have hprod : (∏ k : Fin 4, ovc n ((l'.2 - l.2) k)) = (n - 1) * n ^ 3 := by
        rw [← hi]
        exact prod_single_coord (fun k => ovc n ((l'.2 - l.2) k)) n i (fun k hk => by
          show ovc n ((l'.2 - l.2) k) = n
          rw [hz k hk]
          exact ovc_zero (M := M) n (by omega))
      have hw : boxExcess (M := M) n l l' = (n : ℝ) ^ 2 * (n - 1) := by
        unfold boxExcess
        rw [if_neg hll, if_neg h0, if_pos ⟨i, hz, hs⟩]
      rw [hpw, hprod, hw]
      push_cast [Nat.cast_sub hn]
      have e : ((n : ℝ) - 1) * (n : ℝ) ^ 3 - bR n = (n : ℝ) ^ 2 * (n - 1) := by
        unfold bR
        ring
      rw [e]
      exact le_of_eq (abs_of_nonneg (mul_nonneg (sq_nonneg _) (by linarith)))
    · have hle : (∏ k : Fin 4, ovc n ((l'.2 - l.2) k)) ≤ (n - 1) ^ 2 * n ^ 2 :=
        prod_le_of_not_unit n hn hL h0 hu
      have hleR : pairWeight (boxWeight (M := M) n) l l' ≤ bR n := by
        rw [hpw, ← hbN]
        exact_mod_cast hle
      by_cases hs : SharePlaq (bdT M) l l'
      · right
        have hge : (n - 1) ^ 2 * n ^ 2 ≤ ∏ k : Fin 4, ovc n ((l'.2 - l.2) k) :=
          prod_ge_of_share n hn hL hs
        have hgeR : bR n ≤ pairWeight (boxWeight (M := M) n) l l' := by
          rw [hpw, ← hbN]
          exact_mod_cast hge
        have hw : boxExcess (M := M) n l l' = 0 := by
          unfold boxExcess
          rw [if_neg hll, if_neg h0, if_neg hu]
        rw [hw, abs_nonpos_iff, sub_eq_zero]
        exact le_antisymm hleR hgeR
      · left
        exact ⟨hP hs, hleR⟩

#print axioms box_pair_cond

end Excess

/-! ## 6. The heat-bath system and the finite check -/

section Build

variable {N : ℕ}

/-- **The box-patch heat-bath system** at extent index `j`, box side `n` with `1 ≤ n ≤ j + 1`: the
conditional expectations `torusCondExp β (2j + 1)`, box patches of side `n` at every corner of the
torus of extent `2(j + 1)`, `a₁ = a₂ = n⁴`, `b = n²(n − 1)²`, `e = n²(38n − 35)`.

DERIVED: `4` is the spacetime dimension and the exponent of `a₁`, `a₂`; `2 * j + 1` is the index of
the even-extent family and the `+ 1` its successor writing the extent; `1` is the least box side;
`0` is the excluded rank in `hN`. -/
def boxHeatBath (hN : N ≠ 0) (β : ℝ) (n j : ℕ) (hn : 1 ≤ n) (hj : n ≤ j + 1) :
    WilsonHeatBath hN β j where
  κ := WilsonHypercubic.Site 4 (2 * j + 1 + 1)
  condExp := torusCondExp β (2 * j + 1)
  selfAdj := torusCondExp_selfAdj hN β j
  idem := torusCondExp_idem β (2 * j + 1)
  reads_not := torusCondExp_readsNot β j
  keeps := torusCondExp_keeps β j
  c := boxWeight n
  w := boxExcess n
  a₁ := (n : ℝ) ^ 4
  a₂ := (n : ℝ) ^ 4
  b := bR n
  e := eR n
  cover := box_cover n (by omega)
  cover2 := box_cover2 n (by omega)
  pair := fun l l' hll => box_pair_cond n hn (by omega) hll
    (fun hs x => torusCondExp_comm β (2 * j + 1) hll hs x)
  w_nonneg := boxExcess_nonneg n hn
  row := box_row n hn
  col := box_col n hn

/-- **The one-patch heat-bath system** at every extent index: one patch of weight `1` on every
link, `a₁ = a₂ = b = 1`, `e = 0`.

DERIVED: `1` is the single weight and the multiplicities; `0` is the excess; `2 * j + 1` is the
index of the even-extent family; `0` is the excluded rank in `hN`. -/
def onePatch (hN : N ≠ 0) (β : ℝ) (j : ℕ) : WilsonHeatBath hN β j where
  κ := Unit
  condExp := torusCondExp β (2 * j + 1)
  selfAdj := torusCondExp_selfAdj hN β j
  idem := torusCondExp_idem β (2 * j + 1)
  reads_not := torusCondExp_readsNot β j
  keeps := torusCondExp_keeps β j
  c := fun _ _ => 1
  w := fun _ _ => 0
  a₁ := 1
  a₂ := 1
  b := 1
  e := 0
  cover := fun _ => by simp
  cover2 := fun _ => by simp [pairWeight]
  pair := fun _ _ _ => Or.inr (by simp [pairWeight])
  w_nonneg := fun _ _ => le_refl 0
  row := fun _ => by simp
  col := fun _ => by simp

/-- **`WilsonHeatBath hN β j` is inhabited** at every coupling and extent index (`onePatch`).

DERIVED: `0` is the excluded rank in `hN`. -/
theorem wilsonHeatBath_nonempty (hN : N ≠ 0) (β : ℝ) (j : ℕ) :
    Nonempty (WilsonHeatBath hN β j) :=
  ⟨onePatch hN β j⟩

#print axioms wilsonHeatBath_nonempty

/-- The box-patch family: `boxHeatBath` from `j + 1 ≥ n` on, `onePatch` below.

DERIVED: `1` is the least box side and the successor in `j + 1`; `0` is the excluded rank in
`hN`. -/
def boxFamily (hN : N ≠ 0) (β : ℝ) (n : ℕ) (hn : 1 ≤ n) : ∀ j : ℕ, WilsonHeatBath hN β j :=
  fun j => if h : n ≤ j + 1 then boxHeatBath hN β n j hn h else onePatch hN β j

/-- From `j + 1 ≥ n` on, the family is the box-patch system.

DERIVED: `1` is the least box side and the successor in `j + 1`; `0` is the excluded rank in
`hN`. -/
theorem boxFamily_eq (hN : N ≠ 0) (β : ℝ) (n : ℕ) (hn : 1 ≤ n) (j : ℕ) (hj : n ≤ j + 1) :
    boxFamily hN β n hn j = boxHeatBath hN β n j hn hj := by
  unfold boxFamily
  exact dif_pos hj

#print axioms boxFamily_eq

/-- The Knabe constant at box patches: `(γn² − 40n + 36)/(n − 1)²`.

DERIVED: `40 = 38 + 2` and `36 = 35 + 1` from `γa₁ − a₂ + b − e` divided by `n²`; `2` is the
exponent; `1` is the loss of a unit translate. -/
def boxKnabe (n : ℕ) (γ : ℝ) : ℝ := (γ * (n : ℝ) ^ 2 - 40 * n + 36) / ((n : ℝ) - 1) ^ 2

/-- `(γn⁴ − n⁴ + b − e)/b = (γn² − 40n + 36)/(n − 1)²`: numerator and denominator share the factor
`n²`, non-zero for `1 ≤ n`.

DERIVED: `4` is the exponent of `a₁ = a₂ = n⁴`; `1` is the least box side. The right side's
coefficients are `boxKnabe`'s. -/
theorem knabe_box_eq {n : ℕ} (hn : 1 ≤ n) (γ : ℝ) :
    (γ * (n : ℝ) ^ 4 - (n : ℝ) ^ 4 + bR n - eR n) / bR n = boxKnabe n γ := by
  have hn0 : (n : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr (by omega))
  have h1 : γ * (n : ℝ) ^ 4 - (n : ℝ) ^ 4 + bR n - eR n
      = (n : ℝ) ^ 2 * (γ * (n : ℝ) ^ 2 - 40 * n + 36) := by
    unfold bR eR
    ring
  rw [h1]
  unfold bR boxKnabe
  exact mul_div_mul_left _ _ hn0

#print axioms knabe_box_eq

/-- **The Knabe constant of the box-patch system** is `boxKnabe n γ`.

DERIVED: `1` is the least box side and the successor in `j + 1`; `0` is the excluded rank in
`hN`. -/
theorem knabeConst_box (hN : N ≠ 0) (β : ℝ) (n j : ℕ) (hn : 1 ≤ n) (hj : n ≤ j + 1) (γ : ℝ) :
    (boxHeatBath hN β n j hn hj).toPatchSystem.knabeConst γ = boxKnabe n γ :=
  knabe_box_eq hn γ

#print axioms knabeConst_box

/-- **The threshold**: for `2 ≤ n`, `boxKnabe n γ > 0` exactly when `γ > (40n − 36)/n²`.

DERIVED: `2` is the least side with `b > 0` and the exponent of `n²`; `40`, `36` as in `boxKnabe`;
`0` is the sign. -/
theorem boxKnabe_pos_iff {n : ℕ} (hn : 2 ≤ n) (γ : ℝ) :
    0 < boxKnabe n γ ↔ (40 * (n : ℝ) - 36) / (n : ℝ) ^ 2 < γ := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < ((n : ℝ) - 1) ^ 2 := pow_pos (by linarith) 2
  have hsq : 0 < (n : ℝ) ^ 2 := pow_pos (by linarith) 2
  unfold boxKnabe
  rw [div_pos_iff_of_pos_right hd, div_lt_iff₀ hsq]
  constructor <;> intro h <;> linarith

#print axioms boxKnabe_pos_iff

/-- `b = n²(n − 1)² > 0` for `2 ≤ n`.

DERIVED: `2` is the least side with `b > 0`; `0` is the sign. -/
theorem bR_pos {n : ℕ} (hn : 2 ≤ n) : 0 < bR n := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold bR
  exact mul_pos (pow_pos (by linarith) 2) (pow_pos (by linarith) 2)

#print axioms bR_pos

/-- **The box patch operator** `A_k = Σ_l boxWeight n k l • (id − torusCondExp β (2j + 1) l)` at the
corner `k`, on the periodic gauge-invariant observables at extent `2(j + 1)`.

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent. -/
def boxOp (β : ℝ) (n j : ℕ) (k : WilsonHypercubic.Site 4 (2 * j + 1 + 1)) :
    ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))
      →ₗ[ℝ] ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)) :=
  patchOp (boxWeight n)
    (fun l => (LinearMap.id : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))
      →ₗ[ℝ] ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) - torusCondExp β (2 * j + 1) l) k

/-- **The local gap at box patches**: at every extent index `j` with `n ≤ j + 1`, every box patch
operator `A = boxOp β n j k` has `γ · torusForm(A x, x) ≤ torusForm(A x, A x)` for every periodic
gauge-invariant `x`.

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `1` is the successor in `j + 1`; `0` is the excluded rank in
`hN`. -/
def BoxLocalGap (hN : N ≠ 0) (β : ℝ) (n : ℕ) (γ : ℝ) : Prop :=
  ∀ j : ℕ, n ≤ j + 1 → ∀ (k : WilsonHypercubic.Site 4 (2 * j + 1 + 1))
    (x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))),
    γ * torusForm hN β j (boxOp β n j k x) x
      ≤ torusForm hN β j (boxOp β n j k x) (boxOp β n j k x)

/-- **The finite check at box patches**: `2 ≤ n`, `γ > (40n − 36)/n²`, and the local gap `γ` at every
box patch operator, uniformly in the extent index.

DERIVED: `2` is the least side with `b > 0` and the exponent of `n²`; `40`, `36` are the threshold's
coefficients; `0` is the excluded rank in `hN`. -/
def BoxPatchGap (hN : N ≠ 0) (β : ℝ) (n : ℕ) (γ : ℝ) : Prop :=
  2 ≤ n ∧ (40 * (n : ℝ) - 36) / (n : ℝ) ^ 2 < γ ∧ BoxLocalGap hN β n γ

/-- **The box family and its Knabe constant.** Under `BoxPatchGap hN β n γ`, a family of heat-bath
systems has, for all large `j`, `0 < b`, Knabe constant at least `boxKnabe n γ` and patch gap `γ`: the
content of `patchGapCheck_of_boxPatchGap` with `c₀ = boxKnabe n γ` named.

DERIVED: `0` is the excluded rank in `hN` and the sign of `b`. -/
theorem boxFamily_check (hN : N ≠ 0) {β γ : ℝ} {n : ℕ} (h : BoxPatchGap hN β n γ) :
    ∃ S : ∀ j : ℕ, WilsonHeatBath hN β j, ∀ᶠ j in Filter.atTop,
      0 < (S j).b ∧ boxKnabe n γ ≤ (S j).toPatchSystem.knabeConst γ ∧
        (S j).toPatchSystem.LocalGap γ := by
  obtain ⟨hn2, _, hloc⟩ := h
  have hn1 : 1 ≤ n := by omega
  refine ⟨boxFamily hN β n hn1, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨n, fun j hj => ?_⟩
  have hj' : n ≤ j + 1 := by omega
  rw [boxFamily_eq hN β n hn1 j hj']
  refine ⟨bR_pos hn2, le_of_eq (knabeConst_box hN β n j hn1 hj' γ).symm, ?_⟩
  intro k x
  exact hloc j hj' k x

#print axioms boxFamily_check

/-- **The box check gives the finite check.** `BoxPatchGap hN β n γ → PatchGapCheck hN β γ`, with
the family `boxFamily` and `c₀ = boxKnabe n γ > 0` (`boxKnabe_pos_iff`, `knabe_box_eq`, `bR_pos`):
from `j ≥ n` on the family is `boxHeatBath`, whose Knabe constant is `c₀` exactly and whose patch gap
is `BoxLocalGap` at `j`.

DERIVED: `0` is the excluded rank in `hN`. -/
theorem patchGapCheck_of_boxPatchGap (hN : N ≠ 0) {β γ : ℝ} {n : ℕ}
    (h : BoxPatchGap hN β n γ) : PatchGapCheck hN β γ := by
  obtain ⟨S, hS⟩ := boxFamily_check hN h
  exact ⟨S, boxKnabe n γ, (boxKnabe_pos_iff h.1 γ).mpr h.2.1, hS⟩

#print axioms patchGapCheck_of_boxPatchGap

end Build

end MassGap.BoxPatch
