import Mathlib
import MassGap.PeriodicStrongCoupling

/-!
# MassGap.StrongCouplingSharp — the strong-coupling interval, recounted

`StrongCoupling.wilsonCorrConnObs_abs_le_core_sum` bounds a connected correlation by the core sum

    ∑_{c ∈ corePairsF bd a Ao Bo} |pairTermObs c| · e^{4β · touchDeg · |span c|}.

The existing assembly (`StrongCoupling.corePairsF_sum_le_of_bound`) bounds that sum by counting the
cores whose span has `m` plaquettes by `(4 (K + 1)²)^m` — `((K + 1)²)^m` touch-connected spans from
`card_connSets_le`, whose walk pays `K + 1` per step and two steps per plaquette, times `4^m` ordered
splits of a span into the pair `(c.1, c.2)` — and weighting every one of them by
`(e^{2β} − 1)^{m − u}`. Its rate is `coreRate K β = 4 (K + 1)² (e^{2β} − 1) e^{4βK}`.

This file bounds the same core sum by a different count:

* **Spans** (`card_connSets_le_four`): a touch-connected set of `m` plaquettes containing `p₀` is the
  entry set of a tour (`IsTour`) — a closed depth-first traversal of a spanning tree, built from
  `[p₀]` by the same detours `StrongCoupling.isWalk_detour` inserts (`isTour_insert`,
  `exists_tour_cover`). A tour with `e` branches is fixed by a Catalan shape and one neighbour choice
  per branch (`tourSet`, `card_tourSet_le`), so there are at most `K^{m−1} · catalan (m − 1) ≤
  (4K)^{m−1}` spans, against `(K + 1)^{2m}` from the walk count.
* **Splits** (`pairCover_le`): the pairs `(X, Y)` of subsets of a span `S` covering `S ∖ (Ao ∪ Bo)`
  are summed with their weights `q^{|X|+|Y|}`, `q = e^{2β} − 1`, rather than counted: each plaquette
  outside the anchors contributes `2q + q² = (1 + q)² − 1 = e^{4β} − 1`, each anchor plaquette
  `(1 + q)² = e^{4β}`, against `4q` and `4` from the count.

The hard-core factor `e^{4βK}` per plaquette and the per-term constant `2 c₁ c₂` are the existing
ones. The resulting rate is

    coreRate' K β = 4K · (e^{4β} − 1) · e^{4βK},

and `wilsonCorrConnObs_abs_le_of_not_mem_ball'` is `StrongCoupling.wilsonCorrConnObs_abs_le_of_not_mem_ball`
with `coreRate'` and `coreConst'` in place of `coreRate` and `coreConstG`.

The periodic chain of `PeriodicStrongCoupling` is re-derived on it (`torusState_connected_abs_le_of_cubes'`,
`periodic_connected_shift_abs_le_obs'`, `decay_of_orth_of_conn_rate`, `periodic_gapAt_of_coreRate'`).
`periodic_gapAt_strong_coupling'` is the headline, and `periodic_gap_interval_exceeds_old` states that
the interval it supplies is more than twenty times any interval on which the old rate stays below one.
-/

namespace MassGap.StrongCouplingSharp

open MassGap MassGap.StrongCoupling

/-! ## 1. Tours: closed traversals of spanning trees, and their Catalan count -/

section Tour

variable {Lk Pq : Type} [Fintype Lk] [DecidableEq Lk] [Fintype Pq] [DecidableEq Pq]

/-- `IsTour bd p e t`: `t` is a closed traversal starting at `p` with `e` branches. `[p]` is a tour
with no branch; if `x` touches `p`, `t₁` is a tour from `x` with `i` branches and `t₂` a tour from
`p` with `j` branches, then `p :: (t₁ ++ t₂)` — step into `x`, traverse `t₁`, return, traverse `t₂` —
is a tour from `p` with `i + j + 1` branches.

DERIVED: the `0` is the branch count of the one-entry tour; the `1` is the branch the step into `x`
adds. -/
inductive IsTour (bd : Pq → List (Lk × Bool)) : Pq → ℕ → List Pq → Prop
  | single (p : Pq) : IsTour bd p 0 [p]
  | branch {p x : Pq} {i j : ℕ} {t₁ t₂ : List Pq} (hx : x ∈ touchNbrs bd p)
      (h₁ : IsTour bd x i t₁) (h₂ : IsTour bd p j t₂) :
      IsTour bd p (i + j + 1) (p :: (t₁ ++ t₂))

/-- `IsTour` transported along equalities of its branch count and its list.

DERIVED: no numeral. -/
theorem IsTour.of_eq {bd : Pq → List (Lk × Bool)} {p : Pq} {e e' : ℕ} {t t' : List Pq}
    (h : IsTour bd p e t) (he : e = e') (ht : t = t') : IsTour bd p e' t' := by
  subst he
  subst ht
  exact h

#print axioms IsTour.of_eq

/-- **A tour from `p` contains `p`**: its first entry is `p`.

DERIVED: no numeral. -/
theorem IsTour.head_mem {bd : Pq → List (Lk × Bool)} {p : Pq} {e : ℕ} {t : List Pq}
    (h : IsTour bd p e t) : p ∈ t := by
  cases h <;> simp

#print axioms IsTour.head_mem

/-- The tours from `p` with `e` branches, as a `Finset`, by recursion on `e`: `{[p]}` at `0`, and at
`e + 1` the lists `p :: (t₁ ++ t₂)` with `x ∈ touchNbrs bd p`, `t₁` from `x` with `i` branches and `t₂`
from `p` with `e − i` branches, `i ≤ e`. The recursion is the one `catalan` is defined by.

DERIVED: the `0` and the `1` are the recursion's base and step; `e + 1` indexes `i` over `0, …, e`. -/
noncomputable def tourSet (bd : Pq → List (Lk × Bool)) : ℕ → Pq → Finset (List Pq)
  | 0, p => {[p]}
  | e + 1, p => (touchNbrs bd p).biUnion (fun x =>
      (Finset.univ : Finset (Fin (e + 1))).biUnion (fun i =>
        (tourSet bd (i : ℕ) x ×ˢ tourSet bd (e - (i : ℕ)) p).image
          (fun tt => p :: (tt.1 ++ tt.2))))

/-- The base case of `tourSet`.

DERIVED: the `0` is the branch count. -/
theorem tourSet_zero (bd : Pq → List (Lk × Bool)) (p : Pq) : tourSet bd 0 p = {[p]} := by
  rw [tourSet]

#print axioms tourSet_zero

/-- The step of `tourSet`.

DERIVED: the `1` is the branch the step adds. -/
theorem tourSet_succ (bd : Pq → List (Lk × Bool)) (e : ℕ) (p : Pq) :
    tourSet bd (e + 1) p = (touchNbrs bd p).biUnion (fun x =>
      (Finset.univ : Finset (Fin (e + 1))).biUnion (fun i =>
        (tourSet bd (i : ℕ) x ×ˢ tourSet bd (e - (i : ℕ)) p).image
          (fun tt => p :: (tt.1 ++ tt.2)))) := by
  rw [tourSet]

#print axioms tourSet_succ

/-- **Every tour is counted**: `IsTour bd p e t` gives `t ∈ tourSet bd e p`. Induction on the tour.

DERIVED: no numeral. -/
theorem mem_tourSet_of_isTour (bd : Pq → List (Lk × Bool)) {p : Pq} {e : ℕ} {t : List Pq}
    (h : IsTour bd p e t) : t ∈ tourSet bd e p := by
  induction h with
  | single q =>
    rw [tourSet_zero]
    exact Finset.mem_singleton_self _
  | @branch q x i j t₁ t₂ hx h₁ h₂ ih₁ ih₂ =>
    rw [tourSet_succ]
    refine Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_biUnion.mpr ⟨⟨i, by omega⟩,
      Finset.mem_univ _, Finset.mem_image.mpr ⟨(t₁, t₂), Finset.mem_product.mpr ⟨ih₁, ?_⟩, rfl⟩⟩⟩
    show t₂ ∈ tourSet bd (i + j - i) q
    rw [Nat.add_sub_cancel_left]
    exact ih₂

#print axioms mem_tourSet_of_isTour

/-- **At most `touchDeg bd ^ e · catalan e` tours from `p` have `e` branches.** Strong induction on
`e`: a tour with `e + 1` branches chooses its first neighbour among at most `touchDeg bd`, and splits
the remaining `e` branches as `i` inside the first subtree and `e − i` after it; the number of splits
weighted by the counts below is `∑ᵢ catalan i · catalan (e − i) = catalan (e + 1)` (`catalan_succ`).

DERIVED: no numeral beyond the branch count `e`; `catalan` is Mathlib's. -/
theorem card_tourSet_le (bd : Pq → List (Lk × Bool)) (e : ℕ) :
    ∀ p : Pq, (tourSet bd e p).card ≤ touchDeg bd ^ e * catalan e := by
  induction e using Nat.strongRecOn with
  | ind e ih =>
    rcases e with _ | d
    · intro p
      rw [tourSet_zero]
      simp
    · intro p
      rw [tourSet_succ]
      have hx : ∀ x ∈ touchNbrs bd p,
          ((Finset.univ : Finset (Fin (d + 1))).biUnion (fun i =>
            (tourSet bd (i : ℕ) x ×ˢ tourSet bd (d - (i : ℕ)) p).image
              (fun tt => p :: (tt.1 ++ tt.2)))).card
            ≤ touchDeg bd ^ d * catalan (d + 1) := by
        intro x _
        have hc : catalan (d + 1) = ∑ i : Fin (d + 1), catalan i * catalan (d - i) :=
          catalan_succ d
        calc _ ≤ ∑ i : Fin (d + 1), ((tourSet bd (i : ℕ) x ×ˢ tourSet bd (d - (i : ℕ)) p).image
                (fun tt => p :: (tt.1 ++ tt.2))).card := Finset.card_biUnion_le
          _ ≤ ∑ i : Fin (d + 1),
                (tourSet bd (i : ℕ) x).card * (tourSet bd (d - (i : ℕ)) p).card := by
              refine Finset.sum_le_sum (fun i _ => ?_)
              exact le_trans Finset.card_image_le (le_of_eq (Finset.card_product _ _))
          _ ≤ ∑ i : Fin (d + 1), (touchDeg bd ^ (i : ℕ) * catalan i)
                * (touchDeg bd ^ (d - (i : ℕ)) * catalan (d - i)) := by
              refine Finset.sum_le_sum (fun i _ => Nat.mul_le_mul
                (ih (i : ℕ) i.isLt x) (ih (d - (i : ℕ)) (by omega) p))
          _ = ∑ i : Fin (d + 1), touchDeg bd ^ d * (catalan i * catalan (d - i)) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              have hpow : touchDeg bd ^ (i : ℕ) * touchDeg bd ^ (d - (i : ℕ))
                  = touchDeg bd ^ d := by
                rw [← pow_add, Nat.add_sub_of_le (Fin.is_le i)]
              calc touchDeg bd ^ (i : ℕ) * catalan i
                    * (touchDeg bd ^ (d - (i : ℕ)) * catalan (d - i))
                  = (touchDeg bd ^ (i : ℕ) * touchDeg bd ^ (d - (i : ℕ)))
                    * (catalan i * catalan (d - i)) := by ring
                _ = touchDeg bd ^ d * (catalan i * catalan (d - i)) := by rw [hpow]
          _ = touchDeg bd ^ d * catalan (d + 1) := by rw [hc, Finset.mul_sum]
      calc _ ≤ ∑ x ∈ touchNbrs bd p,
              ((Finset.univ : Finset (Fin (d + 1))).biUnion (fun i =>
                (tourSet bd (i : ℕ) x ×ˢ tourSet bd (d - (i : ℕ)) p).image
                  (fun tt => p :: (tt.1 ++ tt.2)))).card := Finset.card_biUnion_le
        _ ≤ ∑ _x ∈ touchNbrs bd p, touchDeg bd ^ d * catalan (d + 1) := Finset.sum_le_sum hx
        _ = (touchNbrs bd p).card * (touchDeg bd ^ d * catalan (d + 1)) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ touchDeg bd * (touchDeg bd ^ d * catalan (d + 1)) :=
            Nat.mul_le_mul_right _ (touchNbrs_card_le_touchDeg bd p)
        _ = touchDeg bd ^ (d + 1) * catalan (d + 1) := by ring

#print axioms card_tourSet_le

/-- **`catalan n ≤ 4 ^ n`.** `(n + 1) · catalan n` is the central binomial coefficient
(`succ_mul_catalan_eq_centralBinom`), which is at most `4 ^ n` (`Nat.centralBinom_le_four_pow`).

DERIVED: the `4` is `Nat.centralBinom_le_four_pow`'s, `(1 + 1)^{2n}` bounding `(2n choose n)`. -/
theorem catalan_le_four_pow' (n : ℕ) : catalan n ≤ 4 ^ n :=
  calc catalan n ≤ (n + 1) * catalan n := Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
    _ = n.centralBinom := succ_mul_catalan_eq_centralBinom n
    _ ≤ 4 ^ n := Nat.centralBinom_le_four_pow n

#print axioms catalan_le_four_pow'

/-- **Inserting a detour keeps a tour a tour.** If `t = a ++ y :: b` is a tour from `p` with `e`
branches and `x` touches `y`, then `a ++ y :: x :: y :: b` is a tour from `p` with `e + 1` branches.
Induction on the tour, splitting the occurrence of `y` between the head, the first subtree and the
rest (`List.append_eq_append_iff`).

DERIVED: the `1` is the branch the detour adds. -/
theorem isTour_insert (bd : Pq → List (Lk × Bool)) {y x : Pq} (hx : x ∈ touchNbrs bd y)
    {p : Pq} {e : ℕ} {t : List Pq} (h : IsTour bd p e t) :
    ∀ a b : List Pq, t = a ++ y :: b → IsTour bd p (e + 1) (a ++ y :: x :: y :: b) := by
  induction h with
  | single q =>
    intro a b hab
    rcases a with _ | ⟨u, a'⟩
    · simp only [List.nil_append, List.cons.injEq] at hab
      obtain ⟨hq, hb⟩ := hab
      subst hq
      subst hb
      exact IsTour.of_eq (IsTour.branch hx (IsTour.single x) (IsTour.single _)) (by omega)
        (by simp)
    · simp at hab
  | @branch q x' i j t₁ t₂ hx' h₁ h₂ ih₁ ih₂ =>
    intro a b hab
    rcases a with _ | ⟨u, a'⟩
    · simp only [List.nil_append, List.cons.injEq] at hab
      obtain ⟨hq, hb⟩ := hab
      subst hq
      subst hb
      exact IsTour.of_eq (IsTour.branch hx (IsTour.single x) (IsTour.branch hx' h₁ h₂))
        (by omega) (by simp)
    · simp only [List.cons_append, List.cons.injEq] at hab
      obtain ⟨hq, hab'⟩ := hab
      subst hq
      rcases List.append_eq_append_iff.mp hab' with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩
      · -- `a' = t₁ ++ c`, `t₂ = c ++ y :: b`: the occurrence lies in the rest
        have h2' := ih₂ c b hc2
        subst hc1
        exact IsTour.of_eq (IsTour.branch hx' h₁ h2') (by omega) (by simp)
      · -- `t₁ = a' ++ c`, `y :: b = c ++ t₂`
        rcases c with _ | ⟨v, c'⟩
        · -- the occurrence is the head of the rest
          simp only [List.append_nil, List.nil_append] at hc1 hc2
          have h2' := ih₂ [] b hc2.symm
          subst hc1
          exact IsTour.of_eq (IsTour.branch hx' h₁ h2') (by omega) (by simp)
        · -- the occurrence lies in the first subtree
          simp only [List.cons_append, List.cons.injEq] at hc2
          obtain ⟨hv, hb⟩ := hc2
          subst hv
          subst hb
          have h1' := ih₁ a' c' hc1
          exact IsTour.of_eq (IsTour.branch hx' h1' h₂) (by omega) (by simp)

#print axioms isTour_insert

/-- **One new plaquette costs one branch.** A tour from `p` with `e` branches visiting `y`, and `x`
touching `y`, give a tour from `p` with `e + 1` branches whose entry set is that of the first with
`x` inserted.

DERIVED: the `1` is the branch `isTour_insert` adds. -/
theorem isTour_detour (bd : Pq → List (Lk × Bool)) {p : Pq} {e : ℕ} {t : List Pq}
    (h : IsTour bd p e t) {y x : Pq} (hy : y ∈ t) (hx : x ∈ touchNbrs bd y) :
    ∃ t', IsTour bd p (e + 1) t' ∧ t'.toFinset = insert x t.toFinset := by
  obtain ⟨a, b, rfl⟩ := List.append_of_mem hy
  refine ⟨a ++ y :: x :: y :: b, isTour_insert bd hx h a b rfl, ?_⟩
  ext u
  simp only [List.toFinset_append, List.toFinset_cons, Finset.mem_union, Finset.mem_insert]
  tauto

#print axioms isTour_detour

/-- **A tour inside a connected `S` extends to one covering `S`, one branch per new plaquette.**
Given `S` touch-connected from `p₀` and a tour `t` from `p₀` with `e` branches, `e + 1` distinct
entries, all in `S`, and `S.card ≤ t.toFinset.card + j`, there is a tour from `p₀` with
`S.card − 1` branches whose entry set is `S`. Induction on the fuel `j`, as in
`StrongCoupling.exists_walk_cover`.

DERIVED: the `1`s are the root entry, which costs no branch. -/
theorem exists_tour_cover (bd : Pq → List (Lk × Bool)) (S : Finset Pq) (p₀ : Pq)
    (hconn : ∀ q ∈ S, Reach bd S p₀ q) :
    ∀ (j e : ℕ) (t : List Pq), IsTour bd p₀ e t → t.toFinset ⊆ S →
      e + 1 = t.toFinset.card → S.card ≤ t.toFinset.card + j →
      ∃ t', IsTour bd p₀ (S.card - 1) t' ∧ t'.toFinset = S := by
  intro j
  induction j with
  | zero =>
    intro e t ht hsub he hcard
    have hEq : t.toFinset = S := Finset.eq_of_subset_of_card_le hsub (by omega)
    exact ⟨t, IsTour.of_eq ht (by rw [← hEq]; omega) rfl, hEq⟩
  | succ j ih =>
    intro e t ht hsub he hcard
    by_cases hfull : t.toFinset = S
    · exact ⟨t, IsTour.of_eq ht (by rw [← hfull]; omega) rfl, hfull⟩
    · obtain ⟨z, hzS, hzW⟩ : ∃ z ∈ S, z ∉ t.toFinset := by
        by_contra hcon
        refine hfull (Finset.Subset.antisymm hsub (fun u hu => ?_))
        by_contra hu2
        exact hcon ⟨u, hu, hu2⟩
      have hp0 : p₀ ∈ t.toFinset := List.mem_toFinset.mpr ht.head_mem
      rcases exists_boundary_of_reach bd S t.toFinset p₀ hp0 (hconn z hzS) with
        hz | ⟨y, hyW, x, hxS, hxW, htc⟩
      · exact absurd hz hzW
      · obtain ⟨t₁, ht₁, hf₁⟩ :=
          isTour_detour bd ht (List.mem_toFinset.mp hyW) (mem_touchNbrs.mpr htc)
        have hcard₁ : t₁.toFinset.card = t.toFinset.card + 1 := by
          rw [hf₁, Finset.card_insert_of_notMem hxW]
        have hsub₁ : t₁.toFinset ⊆ S := by
          rw [hf₁]
          exact Finset.insert_subset_iff.mpr ⟨hxS, hsub⟩
        exact ih (e + 1) t₁ ht₁ hsub₁ (by omega) (by omega)

#print axioms exists_tour_cover

/-- **`(connSets bd p₀ m).card ≤ touchDeg bd ^ (m − 1) · catalan (m − 1)`.** Every touch-connected
set of size `m` containing `p₀` is the entry set of a tour from `p₀` with `m − 1` branches
(`exists_tour_cover` from `[p₀]`), so the sets inject into `tourSet bd (m − 1) p₀` under
`List.toFinset`, and `card_tourSet_le` counts those. `m = 0` holds because `connSets` is empty there.

DERIVED: the `1` subtracted is the root, which costs no branch. -/
theorem card_connSets_le_tour (bd : Pq → List (Lk × Bool)) (p₀ : Pq) (m : ℕ) :
    (connSets bd p₀ m).card ≤ touchDeg bd ^ (m - 1) * catalan (m - 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | _
  · have hempty : connSets bd p₀ 0 = ∅ := by
      ext S
      constructor
      · intro hS
        obtain ⟨h0, -, hc⟩ := mem_connSets.mp hS
        rw [Finset.card_eq_zero] at hc
        subst hc
        exact absurd h0 (Finset.notMem_empty p₀)
      · intro hS
        exact absurd hS (Finset.notMem_empty S)
    rw [hempty]
    simp
  · have hsub : connSets bd p₀ m ⊆ (tourSet bd (m - 1) p₀).image List.toFinset := by
      intro S hS
      obtain ⟨h0, hconn, hcard⟩ := mem_connSets.mp hS
      have hone : ([p₀] : List Pq).toFinset = {p₀} := by simp
      obtain ⟨t, ht, htS⟩ := exists_tour_cover bd S p₀ hconn S.card 0 [p₀] (IsTour.single p₀)
        (by rw [hone]; exact Finset.singleton_subset_iff.mpr h0) (by rw [hone]; simp)
        (by omega)
      refine Finset.mem_image.mpr ⟨t, ?_, htS⟩
      rw [← hcard]
      exact mem_tourSet_of_isTour bd ht
    calc (connSets bd p₀ m).card
        ≤ ((tourSet bd (m - 1) p₀).image List.toFinset).card := Finset.card_le_card hsub
      _ ≤ (tourSet bd (m - 1) p₀).card := Finset.card_image_le
      _ ≤ touchDeg bd ^ (m - 1) * catalan (m - 1) := card_tourSet_le bd (m - 1) p₀

#print axioms card_connSets_le_tour

/-- **`(connSets bd p₀ m).card ≤ (4 · touchDeg bd) ^ (m − 1)`.** `card_connSets_le_tour` with
`catalan_le_four_pow'`. `StrongCoupling.card_connSets_le` gives `((touchDeg bd + 1) ^ 2) ^ m`.

DERIVED: the `4` is `catalan_le_four_pow'`'s; the `1` subtracted is the root. -/
theorem card_connSets_le_four (bd : Pq → List (Lk × Bool)) (p₀ : Pq) (m : ℕ) :
    (connSets bd p₀ m).card ≤ (4 * touchDeg bd) ^ (m - 1) := by
  refine le_trans (card_connSets_le_tour bd p₀ m) ?_
  calc touchDeg bd ^ (m - 1) * catalan (m - 1) ≤ touchDeg bd ^ (m - 1) * 4 ^ (m - 1) :=
        Nat.mul_le_mul_left _ (catalan_le_four_pow' (m - 1))
    _ = (4 * touchDeg bd) ^ (m - 1) := by rw [mul_pow]; ring

#print axioms card_connSets_le_four

end Tour

/-! ## 2. The weighted count of pairs covering a set -/

section PairCover

variable {α : Type*} [DecidableEq α]

/-- The weight `q^{|X| + |Y|}` of a pair `(X, Y)` if it covers `T`, and `0` otherwise.

DERIVED: the `0` is the excluded pair's weight. -/
noncomputable def pcTerm (q : ℝ) (T X Y : Finset α) : ℝ :=
  if T ⊆ X ∪ Y then q ^ (X.card + Y.card) else 0

/-- The weighted count of pairs of subsets of `S` covering `T`:
`∑_{X, Y ⊆ S, T ⊆ X ∪ Y} q^{|X| + |Y|}`.

DERIVED: no numeral. -/
noncomputable def pairCover (q : ℝ) (S T : Finset α) : ℝ :=
  ∑ X ∈ S.powerset, ∑ Y ∈ S.powerset, pcTerm q T X Y

/-- Adding `s ∉ Y` to the second set multiplies the weight by `q` and removes `s` from the
constraint.

DERIVED: no numeral beyond the one added element. -/
theorem pcTerm_insert_right (q : ℝ) {s : α} {T X Y : Finset α} (hY : s ∉ Y) :
    pcTerm q T X (insert s Y) = q * pcTerm q (T.erase s) X Y := by
  unfold pcTerm
  have hc : (insert s Y).card = Y.card + 1 := Finset.card_insert_of_notMem hY
  have hiff : T ⊆ X ∪ insert s Y ↔ T.erase s ⊆ X ∪ Y := by
    rw [Finset.union_insert, Finset.subset_insert_iff]
  by_cases h : T.erase s ⊆ X ∪ Y
  · rw [if_pos (hiff.mpr h), if_pos h, hc]
    ring
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
    ring

#print axioms pcTerm_insert_right

/-- Adding `s ∉ X` to the first set multiplies the weight by `q` and removes `s` from the constraint.

DERIVED: no numeral beyond the one added element. -/
theorem pcTerm_insert_left (q : ℝ) {s : α} {T X Y : Finset α} (hX : s ∉ X) :
    pcTerm q T (insert s X) Y = q * pcTerm q (T.erase s) X Y := by
  unfold pcTerm
  have hc : (insert s X).card = X.card + 1 := Finset.card_insert_of_notMem hX
  have hiff : T ⊆ insert s X ∪ Y ↔ T.erase s ⊆ X ∪ Y := by
    rw [Finset.insert_union, Finset.subset_insert_iff]
  by_cases h : T.erase s ⊆ X ∪ Y
  · rw [if_pos (hiff.mpr h), if_pos h, hc]
    ring
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
    ring

#print axioms pcTerm_insert_left

/-- Adding `s` to both sets multiplies the weight by `q²` and removes `s` from the constraint.

DERIVED: the `2` is the two sets `s` is added to. -/
theorem pcTerm_insert_both (q : ℝ) {s : α} {T X Y : Finset α} (hX : s ∉ X) (hY : s ∉ Y) :
    pcTerm q T (insert s X) (insert s Y) = q ^ 2 * pcTerm q (T.erase s) X Y := by
  unfold pcTerm
  have hcX : (insert s X).card = X.card + 1 := Finset.card_insert_of_notMem hX
  have hcY : (insert s Y).card = Y.card + 1 := Finset.card_insert_of_notMem hY
  have hiff : T ⊆ insert s X ∪ insert s Y ↔ T.erase s ⊆ X ∪ Y := by
    rw [Finset.insert_union, Finset.union_insert,
      Finset.insert_eq_of_mem (Finset.mem_insert_self s (X ∪ Y)), Finset.subset_insert_iff]
  by_cases h : T.erase s ⊆ X ∪ Y
  · rw [if_pos (hiff.mpr h), if_pos h, hcX, hcY]
    ring
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
    ring

#print axioms pcTerm_insert_both

/-- A pair avoiding a member `s` of `T` does not cover `T`.

DERIVED: the `0` is the excluded pair's weight. -/
theorem pcTerm_eq_zero_of_mem (q : ℝ) {s : α} {T X Y : Finset α} (hsT : s ∈ T) (hX : s ∉ X)
    (hY : s ∉ Y) : pcTerm q T X Y = 0 := by
  unfold pcTerm
  refine if_neg (fun h => ?_)
  rcases Finset.mem_union.mp (h hsT) with h1 | h1
  · exact hX h1
  · exact hY h1

#print axioms pcTerm_eq_zero_of_mem

/-- **The recursion of `pairCover` in the ground set.** For `s ∉ S`,
`pairCover q (insert s S) T = pairCover q S T + (2q + q²) · pairCover q S (T.erase s)`: the pairs
omitting `s` from both sets, and the three ways of containing it.

DERIVED: the `2` is the two sets that may contain `s` alone; the square is the pair containing it in
both. -/
theorem pairCover_insert (q : ℝ) {s : α} {S : Finset α} (hs : s ∉ S) (T : Finset α) :
    pairCover q (insert s S) T
      = pairCover q S T + (2 * q + q ^ 2) * pairCover q S (T.erase s) := by
  have hinner : ∀ X : Finset α, ∑ Y ∈ (insert s S).powerset, pcTerm q T X Y
      = ∑ Y ∈ S.powerset, pcTerm q T X Y + ∑ Y ∈ S.powerset, pcTerm q T X (insert s Y) :=
    fun X => Finset.sum_powerset_insert hs (pcTerm q T X)
  have hR : ∑ X ∈ S.powerset, ∑ Y ∈ S.powerset, pcTerm q T X (insert s Y)
      = q * pairCover q S (T.erase s) := by
    unfold pairCover
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun X _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Y hY => ?_)
    exact pcTerm_insert_right q (fun h => hs (Finset.mem_powerset.mp hY h))
  have hL : ∑ X ∈ S.powerset, ∑ Y ∈ S.powerset, pcTerm q T (insert s X) Y
      = q * pairCover q S (T.erase s) := by
    unfold pairCover
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun X hX => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Y _ => ?_)
    exact pcTerm_insert_left q (fun h => hs (Finset.mem_powerset.mp hX h))
  have hB : ∑ X ∈ S.powerset, ∑ Y ∈ S.powerset, pcTerm q T (insert s X) (insert s Y)
      = q ^ 2 * pairCover q S (T.erase s) := by
    unfold pairCover
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun X hX => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Y hY => ?_)
    exact pcTerm_insert_both q (fun h => hs (Finset.mem_powerset.mp hX h))
      (fun h => hs (Finset.mem_powerset.mp hY h))
  have hA : ∑ X ∈ S.powerset, ∑ Y ∈ S.powerset, pcTerm q T X Y = pairCover q S T := rfl
  calc pairCover q (insert s S) T
      = ∑ X ∈ (insert s S).powerset, ∑ Y ∈ (insert s S).powerset, pcTerm q T X Y := rfl
    _ = ∑ X ∈ (insert s S).powerset,
          (∑ Y ∈ S.powerset, pcTerm q T X Y + ∑ Y ∈ S.powerset, pcTerm q T X (insert s Y)) :=
        Finset.sum_congr rfl (fun X _ => hinner X)
    _ = ∑ X ∈ S.powerset,
          (∑ Y ∈ S.powerset, pcTerm q T X Y + ∑ Y ∈ S.powerset, pcTerm q T X (insert s Y))
        + ∑ X ∈ S.powerset,
          (∑ Y ∈ S.powerset, pcTerm q T (insert s X) Y
            + ∑ Y ∈ S.powerset, pcTerm q T (insert s X) (insert s Y)) :=
        Finset.sum_powerset_insert hs _
    _ = pairCover q S T + q * pairCover q S (T.erase s)
          + (q * pairCover q S (T.erase s) + q ^ 2 * pairCover q S (T.erase s)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hR, hL, hB, hA]
    _ = pairCover q S T + (2 * q + q ^ 2) * pairCover q S (T.erase s) := by ring

#print axioms pairCover_insert

/-- **The weighted pair count covering `T ⊆ S`.** For `0 ≤ q`,

    ∑_{X, Y ⊆ S, T ⊆ X ∪ Y} q^{|X| + |Y|}  ≤  ((1 + q)² − 1)^{|T|} · ((1 + q)²)^{|S| − |T|}.

Each element of `T` lies in `X`, in `Y` or in both, weight `2q + q² = (1 + q)² − 1`; each element of
`S ∖ T` may also lie in neither, weight `(1 + q)²`. Induction on `S` through `pairCover_insert`.

DERIVED: `0` is the lower end of `q`; the `1` is the weight of an element in neither set; the `2` is
the two sets. -/
theorem pairCover_le (q : ℝ) (hq : 0 ≤ q) (S : Finset α) :
    ∀ T : Finset α, T ⊆ S →
      pairCover q S T ≤ ((1 + q) ^ 2 - 1) ^ T.card * ((1 + q) ^ 2) ^ (S.card - T.card) := by
  induction S using Finset.induction_on with
  | empty =>
    intro T hT
    have hT' : T = ∅ := Finset.subset_empty.mp hT
    subst hT'
    simp [pairCover, pcTerm]
  | insert s S hs ih =>
    intro T hT
    rw [pairCover_insert q hs T]
    have hq2 : 0 ≤ 2 * q + q ^ 2 := add_nonneg (by linarith) (sq_nonneg q)
    have hw : (1 + q) ^ 2 - 1 = 2 * q + q ^ 2 := by ring
    have hTe : T.erase s ⊆ S := Finset.subset_insert_iff.mp hT
    have hSc : (insert s S).card = S.card + 1 := Finset.card_insert_of_notMem hs
    by_cases hsT : s ∈ T
    · have h0 : pairCover q S T = 0 := by
        unfold pairCover
        refine Finset.sum_eq_zero (fun X hX => Finset.sum_eq_zero (fun Y hY => ?_))
        exact pcTerm_eq_zero_of_mem q hsT (fun h => hs (Finset.mem_powerset.mp hX h))
          (fun h => hs (Finset.mem_powerset.mp hY h))
      have hTc : T.card = (T.erase s).card + 1 := by
        rw [Finset.card_erase_of_mem hsT]
        have := Finset.card_pos.mpr ⟨s, hsT⟩
        omega
      have ih' := ih (T.erase s) hTe
      rw [hw] at ih'
      rw [h0, zero_add, hSc, hTc, hw,
        show S.card + 1 - ((T.erase s).card + 1) = S.card - (T.erase s).card by omega]
      calc (2 * q + q ^ 2) * pairCover q S (T.erase s)
          ≤ (2 * q + q ^ 2) * ((2 * q + q ^ 2) ^ (T.erase s).card
              * ((1 + q) ^ 2) ^ (S.card - (T.erase s).card)) :=
            mul_le_mul_of_nonneg_left ih' hq2
        _ = (2 * q + q ^ 2) ^ ((T.erase s).card + 1)
              * ((1 + q) ^ 2) ^ (S.card - (T.erase s).card) := by
            rw [pow_succ (2 * q + q ^ 2) (T.erase s).card]
            ring
    · have he : T.erase s = T := Finset.erase_eq_of_notMem hsT
      have hTS : T ⊆ S := by rw [← he]; exact hTe
      have hle : T.card ≤ S.card := Finset.card_le_card hTS
      have ih' := ih T hTS
      rw [he, hSc, show S.card + 1 - T.card = (S.card - T.card) + 1 by omega]
      calc pairCover q S T + (2 * q + q ^ 2) * pairCover q S T
          = (1 + q) ^ 2 * pairCover q S T := by ring
        _ ≤ (1 + q) ^ 2 * (((1 + q) ^ 2 - 1) ^ T.card * ((1 + q) ^ 2) ^ (S.card - T.card)) :=
            mul_le_mul_of_nonneg_left ih' (sq_nonneg _)
        _ = ((1 + q) ^ 2 - 1) ^ T.card * ((1 + q) ^ 2) ^ (S.card - T.card + 1) := by
            rw [pow_succ ((1 + q) ^ 2) (S.card - T.card)]
            ring

#print axioms pairCover_le

/-- The weighted pair count, read as a sum over a filtered product.

DERIVED: no numeral. -/
theorem sum_filter_eq_pairCover (q : ℝ) (S T : Finset α) :
    ∑ c ∈ (S.powerset ×ˢ S.powerset).filter (fun c => T ⊆ c.1 ∪ c.2), q ^ (c.1.card + c.2.card)
      = pairCover q S T := by
  rw [Finset.sum_filter, Finset.sum_product]
  rfl

#print axioms sum_filter_eq_pairCover

end PairCover

/-! ## 3. The rate, the prefactor, and the core sum -/

/-- The recounted per-plaquette rate: `coreRate' K β = 4K · (e^{4β} − 1) · e^{4βK}`.

DERIVED: the leading `4` is `catalan_le_four_pow'`'s bound on a tour's Catalan shape; `K` is the
touch-degree bound, one neighbour choice per branch (`card_connSets_le_four`). `e^{4β} − 1` is
`(1 + q)² − 1` at `q = e^{2β} − 1` (`pairCover_le`): the `2` in `e^{2β}` is the upper end of
`wilsonDensity`'s range, doubled to `4` by the two activated sets of a core pair; the `1` subtracted is
a plaquette in neither set. The `4` in `e^{4βK}` is `hard_core_outside_sq_div_partition_sq_le`'s. -/
noncomputable def coreRate' (K : ℕ) (β : ℝ) : ℝ :=
  4 * (K : ℝ) * (Real.exp (4 * β) - 1) * Real.exp (4 * β * (K : ℝ))

/-- The prefactor for anchors of total size `u` at per-term constant `C`:
`corePrefactor' C K β u = C · (4K)^{u − 1} · (e^{4β})^u · (e^{4βK})^u`. The span count pays
`(4K)^{m − 1}` at `m = n + u`, the anchor plaquettes `e^{4β}` each in `pairCover_le` and the hard core
`e^{4βK}` each; what the geometric series in `n` does not absorb sits here.

DERIVED: the `1` subtracted is the root of the tour; the `4`s are `coreRate'`'s. -/
noncomputable def corePrefactor' (C : ℝ) (K : ℕ) (β : ℝ) (u : ℕ) : ℝ :=
  C * (4 * (K : ℝ)) ^ (u - 1) * Real.exp (4 * β) ^ u * Real.exp (4 * β * (K : ℝ)) ^ u

/-- The constant: `corePrefactor' C K β u / (1 − coreRate' K β)`.

DERIVED: the `1` is the geometric series' denominator. -/
noncomputable def coreConst' (C : ℝ) (K : ℕ) (β : ℝ) (u : ℕ) : ℝ :=
  corePrefactor' C K β u / (1 - coreRate' K β)

/-- `0 ≤ coreRate' K β` at `0 ≤ β`.

DERIVED: the `0`s are the sign hypothesis and the bound. -/
theorem coreRate'_nonneg (K : ℕ) {β : ℝ} (hβ : 0 ≤ β) : 0 ≤ coreRate' K β := by
  unfold coreRate'
  have hE : (0 : ℝ) ≤ Real.exp (4 * β) - 1 := by
    have := Real.one_le_exp (x := 4 * β) (by linarith)
    linarith
  exact mul_nonneg (mul_nonneg (by positivity) hE) (Real.exp_pos _).le

#print axioms coreRate'_nonneg

/-- `0 < coreRate' K β` at `0 < K` and `0 < β`.

DERIVED: the `0`s are the lower ends. -/
theorem coreRate'_pos {K : ℕ} (hK : 0 < K) {β : ℝ} (hβ : 0 < β) : 0 < coreRate' K β := by
  unfold coreRate'
  have hE : (0 : ℝ) < Real.exp (4 * β) - 1 := by
    have := Real.add_one_le_exp (4 * β)
    linarith
  have hKr : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK
  exact mul_pos (mul_pos (mul_pos (by norm_num) hKr) hE) (Real.exp_pos _)

#print axioms coreRate'_pos

/-- `0 ≤ corePrefactor' C K β u` at `0 ≤ C`.

DERIVED: the `0`s are the sign hypothesis and the bound. -/
theorem corePrefactor'_nonneg {C : ℝ} (hC : 0 ≤ C) (K : ℕ) (β : ℝ) (u : ℕ) :
    0 ≤ corePrefactor' C K β u := by
  unfold corePrefactor'
  exact mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (by positivity)) (by positivity)

#print axioms corePrefactor'_nonneg

/-- `0 ≤ coreConst' C K β u` at `0 ≤ C` and `coreRate' K β < 1`.

DERIVED: the `0`s are the sign hypothesis and the bound; the `1` is the geometric threshold. -/
theorem coreConst'_nonneg {C : ℝ} (hC : 0 ≤ C) {K : ℕ} {β : ℝ} (hr : coreRate' K β < 1)
    (u : ℕ) : 0 ≤ coreConst' C K β u := by
  unfold coreConst'
  exact div_nonneg (corePrefactor'_nonneg hC K β u) (by linarith)

#print axioms coreConst'_nonneg

/-- `coreConst'` is monotone in its per-term constant, below the geometric threshold.

DERIVED: the `1` is the geometric threshold. -/
theorem coreConst'_mono_C {C C' : ℝ} (h : C ≤ C') {K : ℕ} {β : ℝ} (hr : coreRate' K β < 1)
    (u : ℕ) : coreConst' C K β u ≤ coreConst' C' K β u := by
  unfold coreConst' corePrefactor'
  have hd : (0 : ℝ) ≤ (1 - coreRate' K β)⁻¹ := inv_nonneg.mpr (by linarith)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ hd
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h (by positivity)) (by positivity)) (by positivity)

#print axioms coreConst'_mono_C

/-- `coreConst'` is monotone in the anchor size `u`, at `0 ≤ C`, `0 ≤ β`, `1 ≤ K` and
`coreRate' K β < 1`.

DERIVED: the `1` bounding `K` makes `4K ≥ 1`; the `0`s are the sign hypotheses; the `1` bounding the
rate is the geometric threshold. -/
theorem coreConst'_le_of_le {C : ℝ} (hC : 0 ≤ C) {β : ℝ} (hβ : 0 ≤ β) {K : ℕ} (hK1 : 1 ≤ K)
    (hr : coreRate' K β < 1) {u U : ℕ} (h : u ≤ U) :
    coreConst' C K β u ≤ coreConst' C K β U := by
  unfold coreConst' corePrefactor'
  have hd : (0 : ℝ) ≤ (1 - coreRate' K β)⁻¹ := inv_nonneg.mpr (by linarith)
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
  have hA : (1 : ℝ) ≤ 4 * (K : ℝ) := by linarith
  have hE4 : (1 : ℝ) ≤ Real.exp (4 * β) := Real.one_le_exp (by linarith)
  have hW : (1 : ℝ) ≤ Real.exp (4 * β * (K : ℝ)) :=
    Real.one_le_exp (mul_nonneg (by linarith) (Nat.cast_nonneg K))
  have h1 : (4 * (K : ℝ)) ^ (u - 1) ≤ (4 * (K : ℝ)) ^ (U - 1) :=
    pow_le_pow_right₀ hA (Nat.sub_le_sub_right h 1)
  have h2 : Real.exp (4 * β) ^ u ≤ Real.exp (4 * β) ^ U := pow_le_pow_right₀ hE4 h
  have h3 : Real.exp (4 * β * (K : ℝ)) ^ u ≤ Real.exp (4 * β * (K : ℝ)) ^ U :=
    pow_le_pow_right₀ hW h
  rw [div_eq_mul_inv, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ hd
  exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left h1 hC) h2 (by positivity)
      (mul_nonneg hC (by positivity))) h3 (by positivity)
    (mul_nonneg (mul_nonneg hC (by positivity)) (by positivity))

#print axioms coreConst'_le_of_le

section CoreSum

variable {Nc : ℕ} {Lk Pq : Type} [Fintype Lk] [DecidableEq Lk] [Fintype Pq] [DecidableEq Pq]

/-- **One fibre of the core sum, recounted.** Given `a ∈ Ao`, `0 ≤ β`, `touchDeg bd ≤ K`, `0 ≤ C`
and `|g c| ≤ C · (e^{2β} − 1)^{|c.1| + |c.2|}` for every pair, the cores whose span has
`n + |Ao ∪ Bo|` plaquettes contribute

    ∑ |g c| · e^{4β · touchDeg · |span c|}  ≤  corePrefactor' C K β |Ao ∪ Bo| · coreRate' K β ^ n.

The cores are grouped by their span `S` (`Finset.sum_fiberwise_of_maps_to`), a touch-connected set of
`m = n + |Ao ∪ Bo|` plaquettes containing `a` (`coreSpanF_mem_connSets`), of which there are at most
`(4K)^{m − 1}` (`card_connSets_le_four`). The cores with span `S` are pairs of subsets of `S` covering
`S ∖ (Ao ∪ Bo)`, whose weights sum to at most `(e^{4β} − 1)^n · (e^{4β})^{|Ao ∪ Bo|}`
(`pairCover_le`). The hard-core factor is at most `e^{4βK m}`.

DERIVED: the `2` in `e^{2β}` and the `1` subtracted are `subset_weight_bound`'s; the `4`s are
`coreRate'`'s and `hard_core_outside_sq_div_partition_sq_le`'s; the `0`s are the sign hypotheses. -/
theorem coreFiber_le' (bd : Pq → List (Lk × Bool)) {a : Pq} {Ao Bo : Finset Pq} (ha : a ∈ Ao)
    {β : ℝ} (hβ : 0 ≤ β) {K : ℕ} (hK : touchDeg bd ≤ K) {C : ℝ} (hC : 0 ≤ C)
    (g : Finset Pq × Finset Pq → ℝ)
    (hg : ∀ c, |g c| ≤ C * (Real.exp (2 * β) - 1) ^ (c.1.card + c.2.card)) (n : ℕ) :
    ∑ c ∈ (corePairsF bd a Ao Bo).filter
        (fun c => (coreSpanF Ao Bo c).card = n + (Ao ∪ Bo).card),
      |g c| * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ))
      ≤ corePrefactor' C K β (Ao ∪ Bo).card * coreRate' K β ^ n := by
  have hq0 : (0 : ℝ) ≤ Real.exp (2 * β) - 1 := by
    have := Real.one_le_exp (x := 2 * β) (by linarith)
    linarith
  have hW0 : (0 : ℝ) ≤ Real.exp (4 * β * (K : ℝ)) := (Real.exp_pos _).le
  have hE0 : (0 : ℝ) ≤ Real.exp (4 * β) - 1 := by
    have := Real.one_le_exp (x := 4 * β) (by linarith)
    linarith
  have hU1 : 1 ≤ (Ao ∪ Bo).card := by
    have := Finset.card_pos.mpr ⟨a, Finset.mem_union_left Bo ha⟩
    omega
  have hw4 : (1 + (Real.exp (2 * β) - 1)) ^ 2 = Real.exp (4 * β) := by
    rw [show 1 + (Real.exp (2 * β) - 1) = Real.exp (2 * β) by ring, sq, ← Real.exp_add]
    congr 1
    ring
  -- the per-core bound
  have hpt : ∀ c ∈ (corePairsF bd a Ao Bo).filter
      (fun c => (coreSpanF Ao Bo c).card = n + (Ao ∪ Bo).card),
      |g c| * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ))
        ≤ C * Real.exp (4 * β * (K : ℝ)) ^ (n + (Ao ∪ Bo).card)
          * (Real.exp (2 * β) - 1) ^ (c.1.card + c.2.card) := by
    intro c hc
    have hm : (coreSpanF Ao Bo c).card = n + (Ao ∪ Bo).card := (Finset.mem_filter.mp hc).2
    have hexp : Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ))
        ≤ Real.exp (4 * β * (K : ℝ)) ^ (n + (Ao ∪ Bo).card) := by
      rw [hm, ← exp_mul_nat_asm]
      apply Real.exp_le_exp.mpr
      have hKr : (touchDeg bd : ℝ) ≤ (K : ℝ) := Nat.cast_le.mpr hK
      have hs : (0 : ℝ) ≤ ((n + (Ao ∪ Bo).card : ℕ) : ℝ) := Nat.cast_nonneg _
      have h1 : 4 * β * (touchDeg bd : ℝ) ≤ 4 * β * (K : ℝ) :=
        mul_le_mul_of_nonneg_left hKr (by linarith)
      have h2 := mul_le_mul_of_nonneg_right h1 hs
      calc 4 * β * ((touchDeg bd * (n + (Ao ∪ Bo).card) : ℕ) : ℝ)
          = 4 * β * (touchDeg bd : ℝ) * ((n + (Ao ∪ Bo).card : ℕ) : ℝ) := by push_cast; ring
        _ ≤ 4 * β * (K : ℝ) * ((n + (Ao ∪ Bo).card : ℕ) : ℝ) := h2
    calc |g c| * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ))
        ≤ (C * (Real.exp (2 * β) - 1) ^ (c.1.card + c.2.card))
          * Real.exp (4 * β * (K : ℝ)) ^ (n + (Ao ∪ Bo).card) :=
          mul_le_mul (hg c) hexp (Real.exp_pos _).le (mul_nonneg hC (pow_nonneg hq0 _))
      _ = C * Real.exp (4 * β * (K : ℝ)) ^ (n + (Ao ∪ Bo).card)
          * (Real.exp (2 * β) - 1) ^ (c.1.card + c.2.card) := by ring
  -- regroup by span
  have hmaps : ∀ c ∈ (corePairsF bd a Ao Bo).filter
      (fun c => (coreSpanF Ao Bo c).card = n + (Ao ∪ Bo).card),
      coreSpanF Ao Bo c ∈ connSets bd a (n + (Ao ∪ Bo).card) := by
    intro c hc
    have hcp : c ∈ corePairsF bd a Ao Bo := (Finset.mem_filter.mp hc).1
    have hm : (coreSpanF Ao Bo c).card = n + (Ao ∪ Bo).card := (Finset.mem_filter.mp hc).2
    have h := coreSpanF_mem_connSets bd ha (mem_corePairsF.mp hcp)
    rwa [hm] at h
  have hfib := (Finset.sum_fiberwise_of_maps_to hmaps
    (fun c => |g c| * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ)))).symm
  rw [hfib]
  have hB : (0 : ℝ) ≤ C * Real.exp (4 * β * (K : ℝ)) ^ (n + (Ao ∪ Bo).card)
      * ((Real.exp (4 * β) - 1) ^ n * Real.exp (4 * β) ^ (Ao ∪ Bo).card) :=
    mul_nonneg (mul_nonneg hC (pow_nonneg hW0 _))
      (mul_nonneg (pow_nonneg hE0 _) (pow_nonneg (Real.exp_pos _).le _))
  refine le_trans (Finset.sum_le_sum (g := fun _ => C * Real.exp (4 * β * (K : ℝ))
      ^ (n + (Ao ∪ Bo).card) * ((Real.exp (4 * β) - 1) ^ n * Real.exp (4 * β) ^ (Ao ∪ Bo).card))
    (fun S hS => ?_)) ?_
  · -- one span
    by_cases hUS : Ao ∪ Bo ⊆ S
    · have hScard : S.card = n + (Ao ∪ Bo).card := (mem_connSets.mp hS).2.2
      have hsd : (S \ (Ao ∪ Bo)).card = n := by
        rw [Finset.card_sdiff_of_subset hUS, hScard]
        omega
      have hrest : S.card - (S \ (Ao ∪ Bo)).card = (Ao ∪ Bo).card := by
        rw [hsd, hScard]
        omega
      refine le_trans (Finset.sum_le_sum (fun c hc => hpt c (Finset.mem_filter.mp hc).1)) ?_
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
        (t := (S.powerset ×ˢ S.powerset).filter (fun c => S \ (Ao ∪ Bo) ⊆ c.1 ∪ c.2))
        (fun c hc => ?_)
        (fun c _ _ => mul_nonneg (mul_nonneg hC (pow_nonneg hW0 _)) (pow_nonneg hq0 _))) ?_
      · have hspan : coreSpanF Ao Bo c = S := (Finset.mem_filter.mp hc).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_powerset.mpr ?_, Finset.mem_powerset.mpr ?_⟩, ?_⟩
        · rw [← hspan]
          exact fst_subset_coreSpanF Ao Bo c
        · rw [← hspan]
          exact snd_subset_coreSpanF Ao Bo c
        · intro x hx
          have hxS : x ∈ S := (Finset.mem_sdiff.mp hx).1
          have hxU : x ∉ Ao ∪ Bo := (Finset.mem_sdiff.mp hx).2
          rw [← hspan] at hxS
          unfold coreSpanF at hxS
          rcases Finset.mem_union.mp hxS with h | h
          · exact h
          · exact absurd h hxU
      · rw [← Finset.mul_sum, sum_filter_eq_pairCover]
        refine le_trans (mul_le_mul_of_nonneg_left
          (pairCover_le (Real.exp (2 * β) - 1) hq0 S (S \ (Ao ∪ Bo)) Finset.sdiff_subset)
          (mul_nonneg hC (pow_nonneg hW0 _))) (le_of_eq ?_)
        rw [hrest, hsd, hw4]
    · -- a span omitting an anchor carries no core
      refine le_trans (le_of_eq (Finset.sum_eq_zero (fun c hc => ?_))) hB
      exfalso
      apply hUS
      have hspan : coreSpanF Ao Bo c = S := (Finset.mem_filter.mp hc).2
      rw [← hspan]
      intro x hx
      unfold coreSpanF
      exact Finset.mem_union_right _ hx
  · -- the spans
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((connSets bd a (n + (Ao ∪ Bo).card)).card : ℝ)
        ≤ (4 * (K : ℝ)) ^ (n + ((Ao ∪ Bo).card - 1)) := by
      have h1 := card_connSets_le_four bd a (n + (Ao ∪ Bo).card)
      have h3 : n + (Ao ∪ Bo).card - 1 = n + ((Ao ∪ Bo).card - 1) := by omega
      rw [h3] at h1
      have h2 : (4 * touchDeg bd) ^ (n + ((Ao ∪ Bo).card - 1))
          ≤ (4 * K) ^ (n + ((Ao ∪ Bo).card - 1)) := Nat.pow_le_pow_left (by omega) _
      exact_mod_cast le_trans h1 h2
    have hrate : (4 * (K : ℝ) * (Real.exp (4 * β) - 1) * Real.exp (4 * β * (K : ℝ))) ^ n
        = (4 * (K : ℝ)) ^ n * (Real.exp (4 * β) - 1) ^ n * Real.exp (4 * β * (K : ℝ)) ^ n := by
      simp only [mul_pow]
    calc _ ≤ (4 * (K : ℝ)) ^ (n + ((Ao ∪ Bo).card - 1))
          * (C * Real.exp (4 * β * (K : ℝ)) ^ (n + (Ao ∪ Bo).card)
            * ((Real.exp (4 * β) - 1) ^ n * Real.exp (4 * β) ^ (Ao ∪ Bo).card)) :=
          mul_le_mul_of_nonneg_right hcard hB
      _ = corePrefactor' C K β (Ao ∪ Bo).card * coreRate' K β ^ n := by
          unfold corePrefactor' coreRate'
          rw [hrate, pow_add, pow_add]
          ring

#print axioms coreFiber_le'

/-- **The core sum, recounted.** Given `a ∈ Ao`, `0 ≤ β`, `touchDeg bd ≤ K`,
`coreRate' K β < 1`, `0 ≤ C`, the per-term bound, `|Ao ∪ Bo| ≤ k + 2`, and every core with `g c ≠ 0`
spanning at least `k + 2` plaquettes,

    ∑_{c ∈ corePairsF bd a Ao Bo} |g c| · e^{4β · touchDeg · |span c|}
      ≤ coreConst' C K β |Ao ∪ Bo| · coreRate' K β ^ (k + 2 − |Ao ∪ Bo|).

`StrongCoupling.corePairsF_sum_le_of_bound`'s fibre decomposition with `coreFiber_le'` in place of
`corePairsF_fiber_sum_le_of_bound`.

DERIVED: the `2` in `k + 2` is the two anchors every core contains; the `2` in `e^{2β}` and the `1`
subtracted are `subset_weight_bound`'s; the `4` is the hard-core exponent; the `0`s are the sign
hypotheses; the `1` bounding the rate is the geometric threshold. -/
theorem corePairsF_sum_le' (bd : Pq → List (Lk × Bool)) {a : Pq} {Ao Bo : Finset Pq}
    (ha : a ∈ Ao) {β : ℝ} (hβ : 0 ≤ β) {K : ℕ} (hK : touchDeg bd ≤ K)
    (hr : coreRate' K β < 1) {C : ℝ} (hC : 0 ≤ C) (g : Finset Pq × Finset Pq → ℝ)
    (hg : ∀ c, |g c| ≤ C * (Real.exp (2 * β) - 1) ^ (c.1.card + c.2.card)) (k : ℕ)
    (hu : (Ao ∪ Bo).card ≤ k + 2)
    (hlow : ∀ c ∈ corePairsF bd a Ao Bo, g c ≠ 0 → k + 2 ≤ (coreSpanF Ao Bo c).card) :
    ∑ c ∈ corePairsF bd a Ao Bo, |g c|
        * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ))
      ≤ coreConst' C K β (Ao ∪ Bo).card * coreRate' K β ^ (k + 2 - (Ao ∪ Bo).card) := by
  have hr0 : 0 ≤ coreRate' K β := coreRate'_nonneg K hβ
  have hmaps : ∀ c ∈ corePairsF bd a Ao Bo,
      (coreSpanF Ao Bo c).card - (k + 2) ∈ Finset.range (Fintype.card Pq + 1) := by
    intro c _
    rw [Finset.mem_range]
    have h : (coreSpanF Ao Bo c).card ≤ (Finset.univ : Finset Pq).card :=
      Finset.card_le_card (Finset.subset_univ _)
    rw [Finset.card_univ] at h
    omega
  have hfib := (Finset.sum_fiberwise_of_maps_to hmaps
    (fun c => |g c|
      * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ)))).symm
  rw [hfib]
  have hstep : ∀ j ∈ Finset.range (Fintype.card Pq + 1),
      ∑ c ∈ (corePairsF bd a Ao Bo).filter
        (fun c => (coreSpanF Ao Bo c).card - (k + 2) = j),
        |g c|
          * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ))
      ≤ (corePrefactor' C K β (Ao ∪ Bo).card * coreRate' K β ^ (k + 2 - (Ao ∪ Bo).card))
          * coreRate' K β ^ j := by
    intro j _
    have hsub : (((corePairsF bd a Ao Bo).filter
        (fun c => (coreSpanF Ao Bo c).card - (k + 2) = j)).filter (fun c => g c ≠ 0))
        ⊆ (corePairsF bd a Ao Bo).filter
          (fun c => (coreSpanF Ao Bo c).card
            = (k + 2 - (Ao ∪ Bo).card + j) + (Ao ∪ Bo).card) := by
      intro c hc
      simp only [Finset.mem_filter] at hc ⊢
      refine ⟨hc.1.1, ?_⟩
      have h1 := hlow c hc.1.1 hc.2
      have h2 := hc.1.2
      omega
    have hmono : ∑ c ∈ (corePairsF bd a Ao Bo).filter
          (fun c => (coreSpanF Ao Bo c).card - (k + 2) = j),
          |g c|
            * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ))
        ≤ ∑ c ∈ (corePairsF bd a Ao Bo).filter
            (fun c => (coreSpanF Ao Bo c).card
              = (k + 2 - (Ao ∪ Bo).card + j) + (Ao ∪ Bo).card),
            |g c|
              * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ)) := by
      rw [← Finset.sum_filter_of_ne (p := fun c => g c ≠ 0) (fun c _ hf hg0 => hf (by
        rw [hg0, abs_zero, zero_mul]))]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun c _ _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
    have h := coreFiber_le' (Bo := Bo) bd ha hβ hK hC g hg (k + 2 - (Ao ∪ Bo).card + j)
    rw [pow_add] at h
    calc ∑ c ∈ (corePairsF bd a Ao Bo).filter
          (fun c => (coreSpanF Ao Bo c).card - (k + 2) = j),
          |g c|
            * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ))
        ≤ ∑ c ∈ (corePairsF bd a Ao Bo).filter
            (fun c => (coreSpanF Ao Bo c).card
              = (k + 2 - (Ao ∪ Bo).card + j) + (Ao ∪ Bo).card),
            |g c|
              * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ)) := hmono
      _ ≤ corePrefactor' C K β (Ao ∪ Bo).card
            * (coreRate' K β ^ (k + 2 - (Ao ∪ Bo).card) * coreRate' K β ^ j) := h
      _ = (corePrefactor' C K β (Ao ∪ Bo).card * coreRate' K β ^ (k + 2 - (Ao ∪ Bo).card))
            * coreRate' K β ^ j := by ring
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  have hpre : 0 ≤ corePrefactor' C K β (Ao ∪ Bo).card * coreRate' K β ^ (k + 2 - (Ao ∪ Bo).card) :=
    mul_nonneg (corePrefactor'_nonneg hC K β _) (pow_nonneg hr0 _)
  have hgeom := geom_sum_le_inv_one_sub_asm hr0 hr (Fintype.card Pq + 1)
  calc (corePrefactor' C K β (Ao ∪ Bo).card * coreRate' K β ^ (k + 2 - (Ao ∪ Bo).card))
        * ∑ j ∈ Finset.range (Fintype.card Pq + 1), coreRate' K β ^ j
      ≤ (corePrefactor' C K β (Ao ∪ Bo).card * coreRate' K β ^ (k + 2 - (Ao ∪ Bo).card))
          * (1 - coreRate' K β)⁻¹ := mul_le_mul_of_nonneg_left hgeom hpre
    _ = coreConst' C K β (Ao ∪ Bo).card * coreRate' K β ^ (k + 2 - (Ao ∪ Bo).card) := by
        unfold coreConst'
        rw [div_eq_mul_inv]
        ring

#print axioms corePairsF_sum_le'

/-- **The cluster bound for two bounded local observables, at the recounted rate.** Two bounded
local observables on disjoint supports, with anchor sets `Ao ⊇ linkHalo Sa`, `Bo ⊇ linkHalo Sb`
touch-connected from base points `a`, `b`, `b` outside the `k`-ball of `a`, and anchors of total size
`u ≤ k + 2`, satisfy, for every `K ≥ touchDeg bd` with `coreRate' K β < 1`,

    |wilsonCorrConnObs bd O₁ O₂ β| ≤ coreConst' (2 c₁ c₂) K β u · coreRate' K β ^ (k + 2 − u),

`u = |Ao ∪ Bo|`. `StrongCoupling.wilsonCorrConnObs_abs_le_core_sum` and `corePairsF_sum_le'` at
`pairTermObs` with `C = 2 c₁ c₂` (`pairTermObs_abs_le`); every core spans at least `k + 2` plaquettes
(`coreSpanF_card_ge_of_not_mem_ball`).

DERIVED: the `2` in `2 c₁ c₂` is `pairTermObs_abs_le`'s two products; the `2` in `k + 2` is the two
base points; the `0`s are `Nc ≠ 0` and `0 ≤ β`; the `1` is the geometric threshold. -/
theorem wilsonCorrConnObs_abs_le_of_not_mem_ball' (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool))
    {O₁ O₂ : (Lk → MassGap.SUN.SU Nc) → ℝ} {Sa Sb : Finset Lk} (hab : Disjoint Sa Sb)
    (h₁ : LocalOnLinks (Nc := Nc) Sa O₁) (h₂ : LocalOnLinks (Nc := Nc) Sb O₂)
    {c₁ c₂ : ℝ} (hc₁ : ∀ U, |O₁ U| ≤ c₁) (hc₂ : ∀ U, |O₂ U| ≤ c₂)
    {Ao Bo : Finset Pq} (hAo : linkHalo bd Sa ⊆ Ao) (hBo : linkHalo bd Sb ⊆ Bo)
    {a b : Pq} (ha : a ∈ Ao) (hb : b ∈ Bo)
    (hconnA : ∀ p ∈ Ao, Reach bd Ao a p) (hconnB : ∀ p ∈ Bo, Reach bd Bo b p)
    {β : ℝ} (hβ : 0 ≤ β) (K : ℕ) (hK : touchDeg bd ≤ K) (hr : coreRate' K β < 1) (k : ℕ)
    (hk : b ∉ StrongCoupling.ball bd a k) (hu : (Ao ∪ Bo).card ≤ k + 2) :
    |wilsonCorrConnObs (Nc := Nc) bd O₁ O₂ β|
      ≤ coreConst' (2 * (c₁ * c₂)) K β (Ao ∪ Bo).card
        * coreRate' K β ^ (k + 2 - (Ao ∪ Bo).card) := by
  have hne : a ≠ b := fun h => hk (h ▸ StrongCoupling.self_mem_ball bd a k)
  have h0₁ : 0 ≤ c₁ := (abs_nonneg _).trans (hc₁ (fun _ => 1))
  have h0₂ : 0 ≤ c₂ := (abs_nonneg _).trans (hc₂ (fun _ => 1))
  have hC : (0 : ℝ) ≤ 2 * (c₁ * c₂) := mul_nonneg zero_le_two (mul_nonneg h0₁ h0₂)
  refine le_trans (wilsonCorrConnObs_abs_le_core_sum hN bd hab h₁ h₂ hc₁ hc₂ hAo hBo ha hb hne
    hconnA hconnB hβ) ?_
  exact corePairsF_sum_le' bd ha hβ hK hr hC (pairTermObs (Nc := Nc) bd O₁ O₂ β)
    (fun c => by
      have h := pairTermObs_abs_le hN bd hc₁ hc₂ β c
      rwa [abs_of_nonneg hβ] at h) k hu
    (fun c hc _ => coreSpanF_card_ge_of_not_mem_ball bd ha hb hne k hk (mem_corePairsF.mp hc))

#print axioms wilsonCorrConnObs_abs_le_of_not_mem_ball'

end CoreSum

/-! ## 4. The interval at `K = 16 · 4`, against the old one -/

section Interval

/-- **`coreRate' 64 β < 1` for `0 ≤ β ≤ 1/1400`.** `e^x ≤ 1/(1 − x)` on `[0, 1)`
(`Real.exp_bound_div_one_sub_of_interval`) gives `e^{4β} − 1 ≤ 1/349` and `e^{256β} ≤ 175/143`,
and `256 · (1/349) · (175/143) < 1`.

CHOSEN: `1/1400` is a round coupling at which the product `256 · (1/349) · (175/143) ≈ 0.898` stays
below one; the rate first reaches one near `β ≈ 7.95 · 10⁻⁴`. DERIVED: `16 * 4` is the periodic
touch-degree bound (`StrongCoupling.touchDeg_bd_le` at dimension `4`); the `0` is the lower end; the
`1` is the geometric threshold. -/
theorem coreRate'_lt_one_of_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 1400) :
    coreRate' (16 * 4) β < 1 := by
  unfold coreRate'
  have hc : ((16 * 4 : ℕ) : ℝ) = 64 := by norm_num
  rw [hc]
  have hx1 : 4 * β < 1 := by linarith
  have hy1 : 4 * β * 64 < 1 := by linarith
  have hE := Real.exp_bound_div_one_sub_of_interval (by linarith : (0 : ℝ) ≤ 4 * β) hx1
  have hW := Real.exp_bound_div_one_sub_of_interval (by linarith : (0 : ℝ) ≤ 4 * β * 64) hy1
  have hpx : (0 : ℝ) < 1 - 4 * β := by linarith
  have hpy : (0 : ℝ) < 1 - 4 * β * 64 := by linarith
  rw [le_div_iff₀ hpx] at hE
  rw [le_div_iff₀ hpy] at hW
  have hE0 : (0 : ℝ) ≤ Real.exp (4 * β) := (Real.exp_pos _).le
  have hW0 : (0 : ℝ) ≤ Real.exp (4 * β * 64) := (Real.exp_pos _).le
  have hE' : Real.exp (4 * β) * (1 - 1 / 350) ≤ Real.exp (4 * β) * (1 - 4 * β) :=
    mul_le_mul_of_nonneg_left (by linarith) hE0
  have hW' : Real.exp (4 * β * 64) * (1 - 32 / 175) ≤ Real.exp (4 * β * 64) * (1 - 4 * β * 64) :=
    mul_le_mul_of_nonneg_left (by linarith) hW0
  have hEb : Real.exp (4 * β) - 1 ≤ 1 / 349 := by linarith
  have hWb : Real.exp (4 * β * 64) ≤ 175 / 143 := by linarith
  have hprod : (Real.exp (4 * β) - 1) * Real.exp (4 * β * 64) ≤ (1 / 349) * (175 / 143) :=
    mul_le_mul hEb hWb hW0 (by norm_num)
  linarith

#print axioms coreRate'_lt_one_of_le

/-- **The old rate is at least one at every `β ≥ 1/33800`.** `coreRate 64 β ≥ 16900 · (e^{2β} − 1) ≥ 33800 β`,
from `e^x ≥ 1 + x` and `e^{256β} ≥ 1`.

DERIVED: `33800 = 2 · 16900 = 2 · 4 · 65²` is `coreRate`'s count `4 (K + 1)²` at `K = 64` times the
`2` of `e^{2β} − 1 ≥ 2β`; `16 * 4` is the touch-degree bound; the `1` is the geometric threshold. -/
theorem coreRate_ge_one_of_ge {β : ℝ} (hβ : 1 / 33800 ≤ β) :
    1 ≤ StrongCoupling.coreRate (16 * 4) β := by
  unfold StrongCoupling.coreRate
  have hc : ((16 * 4 : ℕ) : ℝ) = 64 := by norm_num
  rw [hc]
  have hA : 2 * β ≤ Real.exp (2 * β) - 1 := by linarith [Real.add_one_le_exp (2 * β)]
  have hW : (1 : ℝ) ≤ Real.exp (4 * β * 64) := Real.one_le_exp (by linarith)
  have hA0 : (0 : ℝ) ≤ Real.exp (2 * β) - 1 := by linarith
  have h1 : Real.exp (2 * β) - 1 ≤ (Real.exp (2 * β) - 1) * Real.exp (4 * β * 64) :=
    le_mul_of_one_le_right hA0 hW
  linarith

#print axioms coreRate_ge_one_of_ge

/-- **Any interval on which the old rate stays below one ends by `1/33800`.** If
`coreRate 64 β < 1` for every `0 < β < β₀`, then `β₀ ≤ 1/33800`: otherwise `β = 1/33800` lies in the
interval, where `coreRate_ge_one_of_ge` puts the rate at one or above.

DERIVED: `33800` is `coreRate_ge_one_of_ge`'s; `16 * 4` is the touch-degree bound; the `0` is the
lower end; the `1` is the geometric threshold. -/
theorem old_interval_le (β₀ : ℝ)
    (h : ∀ β : ℝ, 0 < β → β < β₀ → StrongCoupling.coreRate (16 * 4) β < 1) :
    β₀ ≤ 1 / 33800 := by
  by_contra hcon
  push_neg at hcon
  have h1 := h (1 / 33800) (by norm_num) hcon
  have h2 := coreRate_ge_one_of_ge (le_refl (1 / 33800 : ℝ))
  linarith

#print axioms old_interval_le

end Interval

/-! ## 5. The periodic chain at the recounted rate -/

section Periodic

variable {N : ℕ}

/-- **The periodic cluster bound anchored on cubes, at the recounted rate.** The hypotheses of
`PeriodicStrongCoupling.torusState_connected_abs_le_of_cubes` with `coreRate' 64 β < 1` in place of
`coreRate 64 β < 1`; the conclusion with `coreConst'` and `coreRate'`:

    |⟨f g⟩ − ⟨f⟩⟨g⟩|  ≤  coreConst' (2 ‖f‖ ‖g‖) 64 β U · coreRate' 64 β ^ (k + 2 − U),
    U = 32 (R + 1)⁴,

independent of the extent `M + 1`. The proof is that lemma's with
`wilsonCorrConnObs_abs_le_of_not_mem_ball'` as the cluster bound and `coreConst'_le_of_le` carrying it
to `U`.

DERIVED: `16 * 4` is the periodic touch-degree bound (`StrongCoupling.touchDeg_bd_le` at dimension
`4`), and the `4` in `Fin 4` is that dimension; `32 = 2 · 16` is two cubes of at most `16 (R + 1)⁴`
plaquettes (`card_torusCube_le`), with the exponent `4` the dimension; the `2` in `2 ‖f‖ ‖g‖` is `pairTermObs_abs_le`'s two products; the
`2` in `k + 2` is the two base plaquettes; the `2` in `2 * (y₀ τ − x₀ τ)` is the two ways round the
circle; `0` is the excluded rank and the sign of `β`; `1` is the geometric threshold, the strict-inside
margin, the successor writing the extent, and in `R + 1` the offset zero. -/
theorem torusState_connected_abs_le_of_cubes' (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (M : ℕ)
    (f g : C(GibbsSpec.IConf (SUN.SU N), ℝ)) {Sf Sg : Finset InfiniteLattice.ILink}
    (hfl : InfiniteLattice.IsLocalOn Sf (f : GibbsSpec.IConf (SUN.SU N) → ℝ))
    (hgl : InfiniteLattice.IsLocalOn Sg (g : GibbsSpec.IConf (SUN.SU N) → ℝ))
    {x₀ y₀ : InfiniteLattice.ISite} {R : ℕ}
    (hcf : ∀ l ∈ Sf, ∀ i : Fin 4, x₀ i + 1 ≤ l.2 i ∧ l.2 i ≤ x₀ i + R)
    (hcg : ∀ l ∈ Sg, ∀ i : Fin 4, y₀ i + 1 ≤ l.2 i ∧ l.2 i ≤ y₀ i + R)
    (hr : coreRate' (16 * 4) β < 1) (τ : Fin 4) (k : ℕ)
    (hk : (k : ℤ) < y₀ τ - x₀ τ) (hM : 2 * (y₀ τ - x₀ τ) ≤ (M : ℤ) + 1)
    (hu : 32 * (R + 1) ^ 4 ≤ k + 2) :
    |PeriodicState.torusState hN M β (f * g)
        - PeriodicState.torusState hN M β f * PeriodicState.torusState hN M β g|
      ≤ coreConst' (2 * (‖f‖ * ‖g‖)) (16 * 4) β (32 * (R + 1) ^ 4)
        * coreRate' (16 * 4) β ^ (k + 2 - 32 * (R + 1) ^ 4) := by
  classical
  have hpow : R + 1 ≤ (R + 1) ^ 4 := Nat.le_self_pow (by norm_num) (R + 1)
  have hkR : R ≤ k := by omega
  have hRM : (R : ℤ) < (M : ℤ) + 1 := by omega
  have hconv : PeriodicState.torusState hN M β (f * g)
        - PeriodicState.torusState hN M β f * PeriodicState.torusState hN M β g
      = StrongCoupling.wilsonCorrConnObs (Nc := N) (WilsonHypercubic.bd (d := 4) (n := M + 1))
          (PeriodicState.torusObs M f) (PeriodicState.torusObs M g) β := rfl
  rw [hconv]
  have hab : Disjoint (Sf.image (InfiniteLattice.linkMod M))
      (Sg.image (InfiniteLattice.linkMod M)) := by
    rw [Finset.disjoint_left]
    intro t htf htg
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp htf
    obtain ⟨l', hl', he⟩ := Finset.mem_image.mp htg
    have hτ : InfiniteLattice.finMod M (l'.2 τ) = InfiniteLattice.finMod M (l.2 τ) :=
      congrFun (congrArg Prod.snd he) τ
    have h0 : InfiniteLattice.finMod M (l'.2 τ - l.2 τ) = 0 := by
      rw [PeriodicState.finMod_sub, hτ, sub_self]
    have hv0 : ((InfiniteLattice.finMod M (l'.2 τ - l.2 τ) : Fin (M + 1)) : ℕ) = 0 := by
      simp [h0]
    have hb := hcf l hl τ
    have hb' := hcg l' hl' τ
    have hv := PeriodicStrongCoupling.val_finMod_of_lt M (l'.2 τ - l.2 τ) (by omega) (by omega)
    omega
  have ha : ((τ, τ), InfiniteLattice.siteMod M x₀)
      ∈ PeriodicStrongCoupling.torusCube (InfiniteLattice.siteMod M x₀) R :=
    PeriodicStrongCoupling.mem_torusCube_base _ R τ τ
  have hb : ((τ, τ), InfiniteLattice.siteMod M y₀)
      ∈ PeriodicStrongCoupling.torusCube (InfiniteLattice.siteMod M y₀) R :=
    PeriodicStrongCoupling.mem_torusCube_base _ R τ τ
  have hAo := PeriodicStrongCoupling.linkHalo_subset_torusCube M x₀ R hRM Sf hcf
  have hBo := PeriodicStrongCoupling.linkHalo_subset_torusCube M y₀ R hRM Sg hcg
  have hconnA : ∀ q ∈ PeriodicStrongCoupling.torusCube (InfiniteLattice.siteMod M x₀) R,
      StrongCoupling.Reach (WilsonHypercubic.bd (d := 4) (n := M + 1))
        (PeriodicStrongCoupling.torusCube (InfiniteLattice.siteMod M x₀) R)
        ((τ, τ), InfiniteLattice.siteMod M x₀) q :=
    fun q hq => PeriodicStrongCoupling.torus_reach_from_base _ R τ _ q hq rfl
  have hconnB : ∀ q ∈ PeriodicStrongCoupling.torusCube (InfiniteLattice.siteMod M y₀) R,
      StrongCoupling.Reach (WilsonHypercubic.bd (d := 4) (n := M + 1))
        (PeriodicStrongCoupling.torusCube (InfiniteLattice.siteMod M y₀) R)
        ((τ, τ), InfiniteLattice.siteMod M y₀) q :=
    fun q hq => PeriodicStrongCoupling.torus_reach_from_base _ R τ _ q hq rfl
  have hkb := PeriodicStrongCoupling.torus_not_mem_ball M x₀ y₀ τ τ τ τ k hk hM
  have hcard : (PeriodicStrongCoupling.torusCube (InfiniteLattice.siteMod M x₀) R
      ∪ PeriodicStrongCoupling.torusCube (InfiniteLattice.siteMod M y₀) R).card
        ≤ 32 * (R + 1) ^ 4 := by
    have h1 := PeriodicStrongCoupling.card_torusCube_le (InfiniteLattice.siteMod M x₀) R
    have h2 := PeriodicStrongCoupling.card_torusCube_le (InfiniteLattice.siteMod M y₀) R
    have h3 := Finset.card_union_le
      (PeriodicStrongCoupling.torusCube (InfiniteLattice.siteMod M x₀) R)
      (PeriodicStrongCoupling.torusCube (InfiniteLattice.siteMod M y₀) R)
    omega
  have hbase := wilsonCorrConnObs_abs_le_of_not_mem_ball' hN
    (WilsonHypercubic.bd (d := 4) (n := M + 1)) hab
    (PeriodicStrongCoupling.localOnLinks_torusObs M f hfl)
    (PeriodicStrongCoupling.localOnLinks_torusObs M g hgl)
    (PeriodicStrongCoupling.abs_torusObs_le M f) (PeriodicStrongCoupling.abs_torusObs_le M g)
    hAo hBo ha hb hconnA hconnB hβ (16 * 4)
    (StrongCoupling.touchDeg_bd_le (dim := 4) (n := M + 1)) hr k hkb (le_trans hcard hu)
  refine le_trans hbase ?_
  have hC : (0 : ℝ) ≤ 2 * (‖f‖ * ‖g‖) := by positivity
  have hr0 : 0 ≤ coreRate' (16 * 4) β := coreRate'_nonneg _ hβ
  have hCC := coreConst'_le_of_le hC hβ (by norm_num) hr hcard
  have hpow' := StrongCoupling.pow_le_pow_of_le_one_asm hr0 hr.le
    (Nat.sub_le_sub_left hcard (k + 2))
  have hCK : (0 : ℝ) ≤ coreConst' (2 * (‖f‖ * ‖g‖)) (16 * 4) β (32 * (R + 1) ^ 4) :=
    coreConst'_nonneg hC hr _
  exact mul_le_mul hCC hpow' (pow_nonneg hr0 _) hCK

#print axioms torusState_connected_abs_le_of_cubes'

/-- **The connected reflected-shifted pairing decays in `periodicState hN β` at the recounted rate.**
For `x` continuous and local on a finite `S ⊆ posHalf τ p` there is a `U` depending on `S` alone such
that for every `m` with `U ≤ m + 2`, at `0 ≤ β` with `coreRate' 64 β < 1`,

    |ν(θx · Sᵐx) − ν(θx) ν(Sᵐx)|  ≤  coreConst' (2 ‖x‖²) 64 β U · coreRate' 64 β ^ (m + 2 − U),

`ν = periodicState hN β`. `PeriodicStrongCoupling.periodic_connected_shift_abs_le_obs` with
`torusState_connected_abs_le_of_cubes'` as the box bound.

DERIVED: `16 * 4` is the periodic touch-degree bound; the `4` in `Fin 4` is the spacetime dimension;
`2` in `2 * p` is the reflection plane's doubling and in `2 ‖x‖²` the two products of
`pairTermObs_abs_le`; the `2` in `m + 2` is the two base plaquettes; `0` is the sign hypothesis and
the excluded rank; `1` is the geometric threshold. -/
theorem periodic_connected_shift_abs_le_obs' (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (τ : Fin 4)
    (p : ℤ) (hr : coreRate' (16 * 4) β < 1)
    (x : C(GibbsSpec.IConf (SUN.SU N), ℝ)) {S : Finset InfiniteLattice.ILink}
    (hS : (S : Set InfiniteLattice.ILink) ⊆ HalfSpaceAlgebra.posHalf τ p)
    (hx : InfiniteLattice.IsLocalOn S (x : GibbsSpec.IConf (SUN.SU N) → ℝ)) :
    ∃ U : ℕ, ∀ m : ℕ, U ≤ m + 2 →
      |PeriodicState.periodicState hN β (LatticeReflection.ireflObs τ (2 * p) x
            * (⇑(ReflectionShift.ishiftObsL τ))^[m] x)
        - PeriodicState.periodicState hN β (LatticeReflection.ireflObs τ (2 * p) x)
          * PeriodicState.periodicState hN β ((⇑(ReflectionShift.ishiftObsL τ))^[m] x)|
        ≤ coreConst' (2 * (‖x‖ * ‖x‖)) (16 * 4) β U
          * coreRate' (16 * 4) β ^ (m + 2 - U) := by
  classical
  obtain ⟨x₀, R, hx₀τ, hR, hin⟩ := GeneralDecay.exists_cube_posHalf τ p S hS
  refine ⟨32 * (R + 1 + 1) ^ 4, fun m hm => ?_⟩
  set Sf := S.image (LatticeReflection.ireflLink τ (2 * p)) with hSfdef
  set Sg := S.image (InfiniteShift.ishiftLink τ)^[m] with hSgdef
  let xr : GibbsSpec.ISite := Function.update x₀ τ (p - 1 - R)
  let yr : GibbsSpec.ISite := Function.update x₀ τ (p - 1 + m)
  have hpow : 1 ≤ (R + 1 + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hcf : ∀ l ∈ Sf, ∀ i : Fin 4, xr i + 1 ≤ l.2 i ∧ l.2 i ≤ xr i + (R + 1 : ℕ) := by
    intro l hl i
    obtain ⟨l₀, hl₀, rfl⟩ := Finset.mem_image.mp hl
    have hc := (GeneralDecay.ireflLink_coord τ (2 * p) l₀).2 i
    have hb := hin l₀ hl₀ i
    have hbτ := hin l₀ hl₀ τ
    rw [hc]
    by_cases hi : i = τ
    · subst hi
      simp only [xr, Function.update_self, if_true]
      split <;> push_cast <;> constructor <;> omega
    · simp only [xr, Function.update_of_ne hi, hi, if_false]
      push_cast; constructor <;> omega
  have hcg : ∀ l ∈ Sg, ∀ i : Fin 4, yr i + 1 ≤ l.2 i ∧ l.2 i ≤ yr i + (R + 1 : ℕ) := by
    intro l hl i
    obtain ⟨l₀, hl₀, rfl⟩ := Finset.mem_image.mp hl
    have hc := (GeneralDecay.iterate_ishiftLink_coord τ m l₀).2 i
    have hb := hin l₀ hl₀ i
    rw [hc]
    by_cases hi : i = τ
    · subst hi
      simp only [yr, Function.update_self, if_true]
      push_cast; constructor <;> omega
    · simp only [yr, Function.update_of_ne hi, hi, if_false]
      push_cast; constructor <;> omega
  have hfl : InfiniteLattice.IsLocalOn Sf
      (LatticeReflection.ireflObs τ (2 * p) x : GibbsSpec.IConf (SUN.SU N) → ℝ) :=
    HalfSpaceAlgebra.isLocalOn_ireflObs τ (2 * p) hx
  have hgl := GeneralDecay.isLocalOn_iterate_ishiftObsL τ x hx m
  have hxy : yr τ - xr τ = (m : ℤ) + R := by
    simp only [xr, yr, Function.update_self]; omega
  have hk : ((m : ℕ) : ℤ) < yr τ - xr τ := by rw [hxy]; omega
  have hr0 : 0 ≤ coreRate' (16 * 4) β := coreRate'_nonneg _ hβ
  have hev : ∀ᶠ j : ℕ in Filter.atTop,
      |PeriodicReduce.torusConn τ p hN β j x m|
        ≤ coreConst' (2 * (‖x‖ * ‖x‖)) (16 * 4) β (32 * (R + 1 + 1) ^ 4)
          * coreRate' (16 * 4) β ^ (m + 2 - 32 * (R + 1 + 1) ^ 4) := by
    refine Filter.eventually_atTop.mpr ⟨m + R, fun j hj => ?_⟩
    have hM : 2 * (yr τ - xr τ) ≤ ((2 * j + 1 : ℕ) : ℤ) + 1 := by
      rw [hxy]; push_cast; omega
    have hbox := torusState_connected_abs_le_of_cubes' hN hβ (2 * j + 1)
      (LatticeReflection.ireflObs τ (2 * p) x) ((⇑(ReflectionShift.ishiftObsL τ))^[m] x)
      hfl hgl hcf hcg hr τ m hk hM hm
    refine le_trans hbox (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hr0 _))
    refine coreConst'_mono_C ?_ hr _
    have hf := WilsonTransferReduction.norm_ireflObs_le τ (2 * p) x
    have hg := GeneralDecay.norm_iterate_ishiftObsL_le τ x m
    have hx0 : 0 ≤ ‖x‖ := norm_nonneg _
    have := mul_le_mul hf hg (norm_nonneg _) hx0
    linarith
  haveI : ((PeriodicState.periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ).NeBot :=
    (PeriodicState.periodicUltra hN β).neBot'
  exact le_of_tendsto (PeriodicReduce.tendsto_torusConn τ p hN β x m).abs
    (hev.filter_mono (PeriodicState.periodicUltra_le hN β))

#print axioms periodic_connected_shift_abs_le_obs'

end Periodic

section Contraction

open MassGap.Transfer MassGap.GNSHilbert

variable {N : ℕ}

/-- **Every vector orthogonal to the vacuum decays at any rate the pairing bound carries.** For a
state `ν` with reflection invariance, reflection positivity and shift invariance, and `0 < ρ ≤ 1`, if
every local `x` in the positive half has a `U` and a `Cx` with
`|ν(θx · Sᵐx) − ν(θx) ν(Sᵐx)| ≤ Cx · ρ^{m + 2 − U}` for all `m` with `U ≤ m + 2`, then every `y`
orthogonal to the vacuum has `‖Tqⁿ y‖ ≤ K ρⁿ` for some `K`. `PeriodicStrongCoupling.decay_of_orth_of_conn`
with the rate and the per-vector constant made parameters; the proof is that one's.

DERIVED: the `4` in `Fin 4` is the spacetime dimension; `2` is the reflection plane's doubling in
`2 * p` and the `2` of `m + 2`; `0` is the rate's lower end and the vacuum pairing; `1` bounds the
rate. -/
theorem decay_of_orth_of_conn_rate (τ : Fin 4) (p : ℤ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (ν : DLRLimit.State (GibbsSpec.IConf (SUN.SU N)))
    (hinv : InfiniteReflection.IsReflectionInvariant
      (LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hpos : InfiniteReflection.ReflPositiveOn
      (LatticeReflection.latticeReflection τ (2 * p))
      (HalfSpaceAlgebra.halfSpaceAlg (G := SUN.SU N) τ p) ν)
    (hnu : ∀ f : C(GibbsSpec.IConf (SUN.SU N), ℝ), ν (ReflectionShift.ishiftObsL τ f) = ν f)
    (hconn : ∀ (x : C(GibbsSpec.IConf (SUN.SU N), ℝ)) (S : Finset InfiniteLattice.ILink),
      (S : Set InfiniteLattice.ILink) ⊆ HalfSpaceAlgebra.posHalf τ p →
      InfiniteLattice.IsLocalOn S (x : GibbsSpec.IConf (SUN.SU N) → ℝ) →
      ∃ U : ℕ, ∃ Cx : ℝ, ∀ m : ℕ, U ≤ m + 2 →
        |ν (LatticeReflection.ireflObs τ (2 * p) x * (⇑(ReflectionShift.ishiftObsL τ))^[m] x)
          - ν (LatticeReflection.ireflObs τ (2 * p) x)
            * ν ((⇑(ReflectionShift.ishiftObsL τ))^[m] x)|
          ≤ Cx * ρ ^ (m + 2 - U))
    (y : GNS (StrongCouplingGap.Dg τ p ν hinv hpos hnu).toReflForm)
    (hy : (inner ℝ (StrongCouplingGap.Dg τ p ν hinv hpos hnu).vacGNS y : ℝ) = 0) :
    ∃ K : ℝ, ∀ n : ℕ, ‖((StrongCouplingGap.Dg τ p ν hinv hpos hnu).Tq ^ n) y‖ ≤ K * ρ ^ n := by
  classical
  obtain ⟨a, rfl⟩ : ∃ a, GNS.mk (StrongCouplingGap.Dg τ p ν hinv hpos hnu).toReflForm a = y :=
    Submodule.Quotient.mk_surjective _ y
  have hmean : ν (a : C(GibbsSpec.IConf (SUN.SU N), ℝ)) = 0 := by
    rw [← StrongCouplingGap.inner_vacGNS_mk_gaugeInv τ p ν hinv hpos hnu a]; exact hy
  obtain ⟨S, hS, hloc⟩ := (Submodule.mem_inf.mp a.2).1
  obtain ⟨U, Cx, hU⟩ := hconn (a : C(GibbsSpec.IConf (SUN.SU N), ℝ)) S hS hloc
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, Cm = max Cx
      (‖(a : C(GibbsSpec.IConf (SUN.SU N), ℝ))‖
        * ‖(a : C(GibbsSpec.IConf (SUN.SU N), ℝ))‖) := ⟨_, rfl⟩
  have hC : 0 ≤ Cm := by
    rw [hCm]; exact le_trans (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (le_max_right _ _)
  refine ClayCapstone.absolute_decay_of_form_decay (StrongCouplingGap.Dg τ p ν hinv hpos hnu) a
    hρ0.le (K := Cm / ρ ^ U) (fun n => ?_)
  have hform := GaugeInvariantAlgebra.gaugeInv_form_pow τ p ν hinv hpos hnu a (2 * n)
  have hshift : ν ((⇑(ReflectionShift.ishiftObsL τ))^[2 * n]
      (a : C(GibbsSpec.IConf (SUN.SU N), ℝ))) = 0 := by
    rw [GaugeInvariantAlgebra.state_iterate_shift_eq ν τ hnu]; exact hmean
  rw [hform]
  refine StrongCouplingGap.le_div_pow_mul_pow hρ0 hρ1 hC (fun hj => ?_) ?_
  · have h := hU (2 * n) hj
    rw [hshift, mul_zero, sub_zero] at h
    exact le_trans (le_abs_self _) (le_trans h
      (mul_le_mul_of_nonneg_right (hCm ▸ le_max_left _ _) (pow_nonneg hρ0.le _)))
  · refine le_trans (le_abs_self _) (le_trans (ν.abs_le_norm _) ?_)
    refine le_trans (norm_mul_le _ _) (le_trans ?_ (hCm ▸ le_max_right _ _))
    exact mul_le_mul (WilsonTransferReduction.norm_ireflObs_le τ (2 * p) _)
      (GeneralDecay.norm_iterate_ishiftObsL_le τ _ (2 * n)) (norm_nonneg _) (norm_nonneg _)

#print axioms decay_of_orth_of_conn_rate

/-- **Every vector orthogonal to the vacuum of the periodic data decays at rate `coreRate' 64 β`**,
at `0 < β` with `coreRate' 64 β < 1`. `decay_of_orth_of_conn_rate` at `periodicState hN β`, its three
state facts from `PeriodicState`, and the pairing bound `periodic_connected_shift_abs_le_obs'`.

DERIVED: `16 * 4` is the touch-degree bound; the `4` in `Fin 4` is the spacetime dimension; `0` is
the excluded rank, the coupling's lower end and the vacuum pairing; `1` is the geometric threshold. -/
theorem periodic_decay_of_orth' (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β)
    (hr : coreRate' (16 * 4) β < 1)
    (y : GNS (PeriodicState.periodicGaugeInvData τ p hN β).toReflForm)
    (hy : (inner ℝ (PeriodicState.periodicGaugeInvData τ p hN β).vacGNS y : ℝ) = 0) :
    ∃ K : ℝ, ∀ n : ℕ, ‖((PeriodicState.periodicGaugeInvData τ p hN β).Tq ^ n) y‖
      ≤ K * coreRate' (16 * 4) β ^ n :=
  decay_of_orth_of_conn_rate τ p (coreRate'_pos (by norm_num) hβ) hr.le
    (PeriodicState.periodicState hN β)
    (PeriodicState.periodicState_reflInvariant hN β τ (2 * p))
    (PeriodicState.periodicState_reflPositive hN β τ p)
    (PeriodicState.periodicState_shift hN β τ)
    (fun x _S hS hx => by
      obtain ⟨U, hU⟩ := periodic_connected_shift_abs_le_obs' hN hβ.le τ p hr x hS hx
      exact ⟨U, _, hU⟩) y hy

#print axioms periodic_decay_of_orth'

/-- **One transfer step contracts the vacuum complement of the periodic data by `coreRate' 64 β`**:
`‖Tq y‖ ≤ coreRate' 64 β · ‖y‖`. `periodic_decay_of_orth'` and
`SecondEigenvalue.norm_le_of_absolute_iterate_bound`.

DERIVED: `16 * 4` is the touch-degree bound; the `4` in `Fin 4` is the spacetime dimension; `0` is
the excluded rank, the coupling's lower end and the vacuum pairing; `1` is the geometric threshold. -/
theorem periodic_norm_Tq_le_of_orth' (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β)
    (hr : coreRate' (16 * 4) β < 1)
    (y : GNS (PeriodicState.periodicGaugeInvData τ p hN β).toReflForm)
    (hy : (inner ℝ (PeriodicState.periodicGaugeInvData τ p hN β).vacGNS y : ℝ) = 0) :
    ‖(PeriodicState.periodicGaugeInvData τ p hN β).Tq y‖ ≤ coreRate' (16 * 4) β * ‖y‖ := by
  obtain ⟨K, hK⟩ := periodic_decay_of_orth' τ p hN hβ hr y hy
  exact SecondEigenvalue.norm_le_of_absolute_iterate_bound
    (PeriodicState.periodicGaugeInvData τ p hN β).Tq
    (PeriodicState.periodicGaugeInvData τ p hN β).Tq_isSymmetric
    (coreRate'_pos (by norm_num) hβ).le hK

#print axioms periodic_norm_Tq_le_of_orth'

/-- **`GapAt` at the periodic data at rate `coreRate' 64 β`**, at every `0 < β` with
`coreRate' 64 β < 1`: `periodic_norm_Tq_le_of_orth'` and `GNSCompare.gapAt_of_tq_contracts`.

DERIVED: `16 * 4` is the touch-degree bound; the `4` in `Fin 4` is the spacetime dimension; `0` is
the excluded rank and the coupling's lower end; `1` is the geometric threshold. -/
theorem periodic_gapAt_of_coreRate' (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β)
    (hr : coreRate' (16 * 4) β < 1) :
    TransferGap.GapAt (PeriodicState.periodicGaugeInvData τ p hN β) (coreRate' (16 * 4) β) :=
  GNSCompare.gapAt_of_tq_contracts _ (coreRate'_pos (by norm_num) hβ).le
    (fun y hy => periodic_norm_Tq_le_of_orth' τ p hN hβ hr y hy)

#print axioms periodic_gapAt_of_coreRate'

end Contraction

/-! ## 6. The headline -/

section Headline

variable {N : ℕ}

/-- **The transfer gap at the periodic state on the recounted interval.** There is `β₁ > 0` such that
at every `0 < β < β₁` the rate `r = coreRate' 64 β` satisfies `0 < r < 1` and
`TransferGap.GapAt (periodicGaugeInvData τ p hN β) r`. The witness is `β₁ = 1/1400`
(`coreRate'_lt_one_of_le`).

DERIVED: `16 * 4` is the periodic touch-degree bound (`StrongCoupling.touchDeg_bd_le` at dimension
`4`); the `4` in `Fin 4` is the spacetime dimension; `0` is the excluded rank and the lower end of
`β₁`, `β` and the rate; `1` is the geometric threshold. -/
theorem periodic_gapAt_strong_coupling' (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) :
    ∃ β₁ > 0, ∀ β : ℝ, 0 < β → β < β₁ →
      0 < coreRate' (16 * 4) β ∧ coreRate' (16 * 4) β < 1
        ∧ TransferGap.GapAt (PeriodicState.periodicGaugeInvData τ p hN β)
            (coreRate' (16 * 4) β) := by
  refine ⟨1 / 1400, by norm_num, fun β hβ hβ₁ => ?_⟩
  have hr := coreRate'_lt_one_of_le hβ.le hβ₁.le
  exact ⟨coreRate'_pos (by norm_num) hβ, hr, periodic_gapAt_of_coreRate' τ p hN hβ hr⟩

#print axioms periodic_gapAt_strong_coupling'

/-- **The recounted interval exceeds the old one twentyfold.** There is `β₁ > 0` on which
`coreRate' 64 β < 1` and `GapAt (periodicGaugeInvData τ p hN β) (coreRate' 64 β)` hold at every
`0 < β < β₁`, and every `β₀` such that `StrongCoupling.coreRate 64 β < 1` on `0 < β < β₀` — every
interval the rate of `PeriodicStrongCoupling.periodic_gapAt_strong_coupling` can supply — satisfies
`20 · β₀ < β₁`. The witness is `β₁ = 1/1400` (`coreRate'_lt_one_of_le`) against `β₀ ≤ 1/33800`
(`old_interval_le`).

CHOSEN: `20` is a round factor below the proved ratio `33800 / 1400 ≈ 24.1`. DERIVED: `16 * 4` is the
touch-degree bound; the `4` in `Fin 4` is the spacetime dimension; `0` is the excluded rank and the
lower end of the couplings; `1` is the geometric threshold. -/
theorem periodic_gap_interval_exceeds_old (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) :
    ∃ β₁ > 0, (∀ β : ℝ, 0 < β → β < β₁ →
        coreRate' (16 * 4) β < 1
          ∧ TransferGap.GapAt (PeriodicState.periodicGaugeInvData τ p hN β)
              (coreRate' (16 * 4) β))
      ∧ ∀ β₀ : ℝ, (∀ β : ℝ, 0 < β → β < β₀ → StrongCoupling.coreRate (16 * 4) β < 1) →
          20 * β₀ < β₁ := by
  refine ⟨1 / 1400, by norm_num, fun β hβ hβ₁ => ?_, fun β₀ hβ₀ => ?_⟩
  · have hr := coreRate'_lt_one_of_le hβ.le hβ₁.le
    exact ⟨hr, periodic_gapAt_of_coreRate' τ p hN hβ hr⟩
  · have hle := old_interval_le β₀ hβ₀
    linarith

#print axioms periodic_gap_interval_exceeds_old

end Headline

end MassGap.StrongCouplingSharp
