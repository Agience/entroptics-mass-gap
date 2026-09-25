import Mathlib
import MassGap.StrongCoupling

/-!
# Two restrictions of one Wilson system agree near an observable

For a finite Wilson system and two plaquette sets `P`, `P'`, the Gibbs means of a local observable
with the action restricted to `P` and to `P'` differ by at most `coreConstG · coreRate^(k+2−u)` when the
`k`-ball around the observable's anchor lies in both (`meanR_sub_abs_le`). This is what makes the free
box states converge: a box's plaquettes are a restriction of a larger box's.

The expansion. Both means expand over plaquette subsets (`meanR`), and their difference has numerator
`∑ diffTerm` (`meanR_sub_eq`), with `diffTerm (E, F) = zw_{P'}(O, E) zw_P(1, F) − zw_P(O, F) zw_{P'}(1, E)`.
Each term factors through the component of the observable's anchor (`diffTerm_fac`), so the sum
regroups by core (`StrongCoupling.bridging_sum_eq_core_sum_of_fac` with two outside weights). A core
inside `P ∩ P'` sees both restrictions as the same, and exchanging its two halves negates its term,
so those cores sum to zero (`sum_core_inside_eq_zero`). What is left spans from the anchor out of
`P ∩ P'`, and `StrongCoupling.corePairsF_sum_le_of_bound` counts it.
-/

namespace MassGap.BoxCompare

open MeasureTheory MassGap.StrongCoupling MassGap.WilsonReal MassGap.WilsonLattice
open MassGap.WilsonAction MassGap.CompactGauge MassGap.LatticeGauge

variable {Nc : ℕ} {Lk Pq : Type} [Fintype Lk] [DecidableEq Lk] [Fintype Pq] [DecidableEq Pq]

/-! ## Restricted terms -/

open scoped Classical in
/-- The subset-expansion term restricted to `P`: `zwFull O E` when `E ⊆ P`, zero otherwise. Summing it
over all `E` expands the Gibbs weight with the action restricted to `P`.

DERIVED: the `0` is the restriction's value off `P`. -/
noncomputable def zwR (bd : Pq → List (Lk × Bool)) (β : ℝ) (P : Finset Pq)
    (O : (Lk → MassGap.SUN.SU Nc) → ℝ) (E : Finset Pq) : ℝ :=
  if E ⊆ P then zwFull (Nc := Nc) bd β O E else 0

open scoped Classical in
/-- **A term splits at a set of plaquettes whose two sides read disjoint links.** For `X` local on
`S` and `W` whose plaquettes in `A` read `S` and outside `A` read `T`, with `S`, `T` disjoint,
`zwFull X W = zwFull X (W ∩ A) · zwFull 1 (W \ A)`. `StrongCoupling.zwFull_split` against the constant
observable.

DERIVED: the `1` is the constant observable. -/
theorem zwFull_core_split (bd : Pq → List (Lk × Bool)) (β : ℝ) {S T : Finset Lk}
    (hST : Disjoint S T) {X : (Lk → MassGap.SUN.SU Nc) → ℝ} (hX : LocalOnLinks (Nc := Nc) S X)
    (W A : Finset Pq)
    (hin : ∀ p ∈ W ∩ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hout : ∀ p ∈ W \ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ T) :
    zwFull (Nc := Nc) bd β X W
      = zwFull (Nc := Nc) bd β X (W ∩ A) * zwFull (Nc := Nc) bd β (fun _ => (1 : ℝ)) (W \ A) := by
  classical
  have hEu : W = (W ∩ A) ∪ (W \ A) := by
    ext x; by_cases hx : x ∈ A <;> simp [hx]
  have hEd : Disjoint (W ∩ A) (W \ A) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).2
  rw [zwFull_congr (Nc := Nc) bd β
    (O' := fun U => X U * (fun _ : Lk → MassGap.SUN.SU Nc => (1 : ℝ)) U)
    (fun U => (mul_one (X U)).symm) W]
  exact zwFull_split (Nc := Nc) bd β W (W ∩ A) (W \ A) S T hST hX (localOnLinks_one T)
    hEu hEd hin hout

#print axioms zwFull_core_split

open scoped Classical in
/-- **The restricted term splits the same way**: `W ⊆ P` exactly when both halves are, and otherwise
one factor vanishes.

DERIVED: the `1` is the constant observable. -/
theorem zwR_core_split (bd : Pq → List (Lk × Bool)) (β : ℝ) (P : Finset Pq) {S T : Finset Lk}
    (hST : Disjoint S T) {X : (Lk → MassGap.SUN.SU Nc) → ℝ} (hX : LocalOnLinks (Nc := Nc) S X)
    (W A : Finset Pq)
    (hin : ∀ p ∈ W ∩ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hout : ∀ p ∈ W \ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ T) :
    zwR (Nc := Nc) bd β P X W
      = zwR (Nc := Nc) bd β P X (W ∩ A) * zwR (Nc := Nc) bd β P (fun _ => (1 : ℝ)) (W \ A) := by
  classical
  unfold zwR
  by_cases hW : W ⊆ P
  · have h1 : W ∩ A ⊆ P := fun x hx => hW (Finset.mem_inter.mp hx).1
    have h2 : W \ A ⊆ P := fun x hx => hW (Finset.mem_sdiff.mp hx).1
    rw [if_pos hW, if_pos h1, if_pos h2]
    exact zwFull_core_split bd β hST hX W A hin hout
  · rw [if_neg hW]
    by_cases h1 : W ∩ A ⊆ P
    · have h2 : ¬ W \ A ⊆ P := by
        intro h2
        apply hW
        intro x hx
        by_cases hxA : x ∈ A
        · exact h1 (Finset.mem_inter.mpr ⟨hx, hxA⟩)
        · exact h2 (Finset.mem_sdiff.mpr ⟨hx, hxA⟩)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

#print axioms zwR_core_split

/-- The difference term of two restrictions `P'` and `P`:
`zw_{P'}(O, E) · zw_P(1, F) − zw_P(O, F) · zw_{P'}(1, E)`.

DERIVED: the `1` is the constant observable; the `1` and `2` in `q.1`, `q.2` are projections. -/
noncomputable def diffTerm (bd : Pq → List (Lk × Bool)) (β : ℝ) (P' P : Finset Pq)
    (O : (Lk → MassGap.SUN.SU Nc) → ℝ) (q : Finset Pq × Finset Pq) : ℝ :=
  zwR (Nc := Nc) bd β P' O q.1 * zwR (Nc := Nc) bd β P (fun _ => (1 : ℝ)) q.2
    - zwR (Nc := Nc) bd β P O q.2 * zwR (Nc := Nc) bd β P' (fun _ => (1 : ℝ)) q.1

open scoped Classical in
/-- **The difference term factors through any core containing the anchor.** With `O` local on `Sa`,
`Ao ⊇ linkHalo Sa`, `A ⊇ Ao ∪ Bo`, and no touch across `A` inside `E ∪ F ∪ (Ao ∪ Bo)`,

    diffTerm (E, F) = diffTerm (E ∩ A, F ∩ A) · (zw_{P'}(1, E \ A) · zw_P(1, F \ A)).

A plaquette outside `A` is outside the halo, so it reads no link of `Sa`; the two sides of `A` read
disjoint links, and `zwFull_core_split`, `zwR_core_split` split each of the four terms.

DERIVED: the `1` is the constant observable. -/
theorem diffTerm_fac (bd : Pq → List (Lk × Bool)) (β : ℝ) (P' P : Finset Pq)
    {O : (Lk → MassGap.SUN.SU Nc) → ℝ} {Sa : Finset Lk} (h : LocalOnLinks (Nc := Nc) Sa O)
    {Ao Bo : Finset Pq} (hAo : linkHalo bd Sa ⊆ Ao) (E F A : Finset Pq)
    (hclosed : ∀ p ∈ (E ∪ F ∪ (Ao ∪ Bo)) ∩ A, ∀ r ∈ (E ∪ F ∪ (Ao ∪ Bo)) \ A, ¬ Touch bd p r)
    (hA : Ao ∪ Bo ⊆ A) :
    diffTerm (Nc := Nc) bd β P' P O (E, F)
      = diffTerm (Nc := Nc) bd β P' P O (E ∩ A, F ∩ A)
        * (zwR (Nc := Nc) bd β P' (fun _ => (1 : ℝ)) (E \ A)
          * zwR (Nc := Nc) bd β P (fun _ => (1 : ℝ)) (F \ A)) := by
  classical
  set S : Finset Lk := ((E ∪ F) ∩ A).biUnion (linkSupp bd) ∪ Sa with hS
  set T : Finset Lk := ((E ∪ F) \ A).biUnion (linkSupp bd) with hT
  have hST : Disjoint S T := by
    rw [hS, hT, Finset.disjoint_left]
    intro l hl hl'
    obtain ⟨r, hr, hlr⟩ := Finset.mem_biUnion.mp hl'
    have hr' : r ∈ (E ∪ F ∪ (Ao ∪ Bo)) \ A := by
      simp only [Finset.mem_sdiff, Finset.mem_union] at hr ⊢
      tauto
    rcases Finset.mem_union.mp hl with hl | hl
    · obtain ⟨p, hp, hlp⟩ := Finset.mem_biUnion.mp hl
      have hp' : p ∈ (E ∪ F ∪ (Ao ∪ Bo)) ∩ A := by
        simp only [Finset.mem_inter, Finset.mem_union] at hp ⊢
        tauto
      exact hclosed p hp' r hr' ⟨l, hlp, hlr⟩
    · exact (Finset.mem_sdiff.mp hr).2
        (hA (Finset.mem_union_left _ (hAo (mem_linkHalo.mpr ⟨l, hlr, hl⟩))))
  have hSa : Sa ⊆ S := by rw [hS]; exact Finset.subset_union_right
  have hO : LocalOnLinks (Nc := Nc) S O := localOnLinks_mono bd hSa h
  have h1 : LocalOnLinks (Nc := Nc) S (fun _ => (1 : ℝ)) := localOnLinks_one S
  have hin : ∀ W : Finset Pq, W ⊆ E ∪ F → ∀ p ∈ W ∩ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ S := by
    intro W hW p hp l hl
    have hp' : p ∈ (E ∪ F) ∩ A :=
      Finset.mem_inter.mpr ⟨hW (Finset.mem_inter.mp hp).1, (Finset.mem_inter.mp hp).2⟩
    rw [hS]
    exact Finset.mem_union_left _ (supp_subset_biUnion bd _ p hp' l hl)
  have hout : ∀ W : Finset Pq, W ⊆ E ∪ F → ∀ p ∈ W \ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ T := by
    intro W hW p hp l hl
    have hp' : p ∈ (E ∪ F) \ A :=
      Finset.mem_sdiff.mpr ⟨hW (Finset.mem_sdiff.mp hp).1, (Finset.mem_sdiff.mp hp).2⟩
    rw [hT]
    exact supp_subset_biUnion bd _ p hp' l hl
  have hE : E ⊆ E ∪ F := Finset.subset_union_left
  have hF : F ⊆ E ∪ F := Finset.subset_union_right
  have e1 := zwR_core_split bd β P' hST hO E A (hin E hE) (hout E hE)
  have e2 := zwR_core_split bd β P hST h1 F A (hin F hF) (hout F hF)
  have e3 := zwR_core_split bd β P hST hO F A (hin F hF) (hout F hF)
  have e4 := zwR_core_split bd β P' hST h1 E A (hin E hE) (hout E hE)
  simp only [diffTerm]
  rw [e1, e2, e3, e4]
  ring

#print axioms diffTerm_fac

/-! ## The means and their difference -/

/-- The partition function of the action restricted to `P`, as a subset expansion.

DERIVED: the `1` is the constant observable. -/
noncomputable def Zr (bd : Pq → List (Lk × Bool)) (β : ℝ) (P : Finset Pq) : ℝ :=
  ∑ E : Finset Pq, zwR (Nc := Nc) bd β P (fun _ => (1 : ℝ)) E

/-- The Gibbs mean of `O` with the action restricted to `P`, as a ratio of subset expansions.

DERIVED: no numeral. -/
noncomputable def meanR (bd : Pq → List (Lk × Bool)) (β : ℝ) (P : Finset Pq)
    (O : (Lk → MassGap.SUN.SU Nc) → ℝ) : ℝ :=
  (∑ E : Finset Pq, zwR (Nc := Nc) bd β P O E) / Zr (Nc := Nc) bd β P

open scoped Classical in
/-- **The restricted constant sums over a set's subsets to the partition function of the restriction
to the set and `P`**: `∑_{E ⊆ W} zw_P(1, E) = subPart (W ∩ P)`.

DERIVED: the `0` is `hN`; the `1` is the constant observable. -/
theorem sum_zwR_one_eq_subPart (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (P W : Finset Pq) :
    ∑ E ∈ W.powerset, zwR (Nc := Nc) bd β P (fun _ => (1 : ℝ)) E
      = subPart (Nc := Nc) bd β (W ∩ P) := by
  classical
  have hfil : W.powerset.filter (fun E => E ⊆ P) = (W ∩ P).powerset := by
    ext E
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_inter_iff]
  simp only [zwR, zwFull_one_eq_zw_empty]
  rw [← Finset.sum_filter, hfil, subset_sum_eq_subPart hN bd β (W ∩ P)]

#print axioms sum_zwR_one_eq_subPart

/-- `Zr P = subPart P`.

DERIVED: the `0` is `hN`. -/
theorem Zr_eq_subPart (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ) (P : Finset Pq) :
    Zr (Nc := Nc) bd β P = subPart (Nc := Nc) bd β P := by
  have h := sum_zwR_one_eq_subPart hN bd β P Finset.univ
  rw [Finset.powerset_univ, Finset.univ_inter] at h
  exact h

#print axioms Zr_eq_subPart

/-- The restricted partition function is positive.

DERIVED: the `0` is `hN` and the bound. -/
theorem Zr_pos (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ) (P : Finset Pq) :
    0 < Zr (Nc := Nc) bd β P := by
  rw [Zr_eq_subPart hN bd β P]
  exact subPart_pos hN bd β P

#print axioms Zr_pos

/-- **The difference of two restricted means is the sum of the difference terms over the product of
the two partition functions.**

DERIVED: the `0` is `hN`; the `1` is the constant observable. -/
theorem meanR_sub_eq (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ) (P' P : Finset Pq)
    (O : (Lk → MassGap.SUN.SU Nc) → ℝ) :
    meanR (Nc := Nc) bd β P' O - meanR (Nc := Nc) bd β P O
      = (∑ q : Finset Pq × Finset Pq, diffTerm (Nc := Nc) bd β P' P O q)
        / (Zr (Nc := Nc) bd β P' * Zr (Nc := Nc) bd β P) := by
  have hZ' := (Zr_pos hN bd β P').ne'
  have hZ := (Zr_pos hN bd β P).ne'
  have hsum : (∑ q : Finset Pq × Finset Pq, diffTerm (Nc := Nc) bd β P' P O q)
      = (∑ E : Finset Pq, zwR (Nc := Nc) bd β P' O E) * Zr (Nc := Nc) bd β P
        - (∑ F : Finset Pq, zwR (Nc := Nc) bd β P O F) * Zr (Nc := Nc) bd β P' := by
    unfold Zr
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum,
      Finset.sum_comm (f := fun F E => zwR (Nc := Nc) bd β P O F
        * zwR (Nc := Nc) bd β P' (fun _ => (1 : ℝ)) E),
      ← Finset.sum_sub_distrib, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun E _ => ?_)
    rw [← Finset.sum_sub_distrib]
    rfl
  unfold meanR
  rw [hsum]
  field_simp

#print axioms meanR_sub_eq

/-! ## Cores inside both restrictions cancel -/

/-- The core span is the same for a pair and its swap.

DERIVED: the `1` and `2` are projections. -/
theorem coreSpanF_swap (A B : Finset Pq) (c : Finset Pq × Finset Pq) :
    coreSpanF A B (c.2, c.1) = coreSpanF A B c := by
  unfold coreSpanF
  simp only [Finset.union_comm c.2 c.1]

#print axioms coreSpanF_swap

open scoped Classical in
/-- Swapping the two halves keeps a core pair with a span inside `Q` a core pair with a span inside
`Q`.

DERIVED: the `1` and `2` are projections. -/
theorem swap_mem_filter_corePairsF (bd : Pq → List (Lk × Bool)) (a : Pq) (Ao Bo Q : Finset Pq)
    {c : Finset Pq × Finset Pq}
    (hc : c ∈ (corePairsF bd a Ao Bo).filter (fun c => coreSpanF Ao Bo c ⊆ Q)) :
    (c.2, c.1) ∈ (corePairsF bd a Ao Bo).filter (fun c => coreSpanF Ao Bo c ⊆ Q) := by
  have hc' := Finset.mem_filter.mp hc
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · have h := mem_corePairsF.mp hc'.1
    apply mem_corePairsF.mpr
    unfold IsCorePairF at h ⊢
    rw [coreSpanF_swap]
    exact h
  · rw [coreSpanF_swap]
    exact hc'.2

#print axioms swap_mem_filter_corePairsF

open scoped Classical in
/-- **The cores inside both restrictions sum to zero.** For any weight `w` of the span, swapping the
two halves of a core pair keeps it a core pair with the same span (`swap_mem_filter_corePairsF`); on a
span inside `P ∩ P'` both restrictions read `zwFull`, so the swap negates `diffTerm`, and a pair equal
to its swap has `diffTerm = 0`. `Finset.sum_involution`.

DERIVED: the `0` is the cancelled sum; the `1` and `2` are projections. -/
theorem sum_core_inside_eq_zero (bd : Pq → List (Lk × Bool)) (β : ℝ) (P' P : Finset Pq)
    (O : (Lk → MassGap.SUN.SU Nc) → ℝ) (a : Pq) (Ao Bo : Finset Pq) (w : Finset Pq → ℝ) :
    ∑ c ∈ (corePairsF bd a Ao Bo).filter (fun c => coreSpanF Ao Bo c ⊆ P ∩ P'),
      diffTerm (Nc := Nc) bd β P' P O c * w (coreSpanF Ao Bo c) = 0 := by
  classical
  have hval : ∀ c ∈ (corePairsF bd a Ao Bo).filter (fun c => coreSpanF Ao Bo c ⊆ P ∩ P'),
      diffTerm (Nc := Nc) bd β P' P O c
        = zwFull (Nc := Nc) bd β O c.1 * zwFull (Nc := Nc) bd β (fun _ => (1 : ℝ)) c.2
          - zwFull (Nc := Nc) bd β O c.2 * zwFull (Nc := Nc) bd β (fun _ => (1 : ℝ)) c.1 := by
    intro c hc
    have hs := (Finset.mem_filter.mp hc).2
    have h1 : c.1 ⊆ coreSpanF Ao Bo c := fst_subset_coreSpanF Ao Bo c
    have h2 : c.2 ⊆ coreSpanF Ao Bo c := snd_subset_coreSpanF Ao Bo c
    have h1P : c.1 ⊆ P := fun x hx => (Finset.mem_inter.mp (hs (h1 hx))).1
    have h1P' : c.1 ⊆ P' := fun x hx => (Finset.mem_inter.mp (hs (h1 hx))).2
    have h2P : c.2 ⊆ P := fun x hx => (Finset.mem_inter.mp (hs (h2 hx))).1
    have h2P' : c.2 ⊆ P' := fun x hx => (Finset.mem_inter.mp (hs (h2 hx))).2
    simp only [diffTerm, zwR, if_pos h1P, if_pos h1P', if_pos h2P, if_pos h2P']
  refine Finset.sum_involution (fun c _ => (c.2, c.1)) (fun c hc => ?_) (fun c hc hne => ?_)
    (fun c hc => swap_mem_filter_corePairsF bd a Ao Bo (P ∩ P') hc) (fun c _ => rfl)
  · rw [hval c hc, hval (c.2, c.1) (swap_mem_filter_corePairsF bd a Ao Bo (P ∩ P') hc),
      coreSpanF_swap]
    dsimp only
    ring
  · intro heq
    apply hne
    have h12 : c.1 = c.2 := (Prod.ext_iff.mp heq).1.symm
    rw [hval c hc, h12]
    ring

#print axioms sum_core_inside_eq_zero

/-! ## Bounds -/

/-- `|zw_P(X, E)| ≤ c · (e^{2|β|} − 1)^|E|` for `X` bounded by `c`. `StrongCoupling.zwFull_abs_le`,
and zero off `P`.

DERIVED: the `0` is `hN` and the value off `P`; the `2` and `1` are `subset_weight_bound`'s. -/
theorem zwR_abs_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ) (P : Finset Pq)
    {X : (Lk → MassGap.SUN.SU Nc) → ℝ} {c : ℝ} (hc : ∀ U, |X U| ≤ c) (E : Finset Pq) :
    |zwR (Nc := Nc) bd β P X E| ≤ c * (Real.exp (2 * |β|) - 1) ^ E.card := by
  classical
  unfold zwR
  split
  · exact zwFull_abs_le hN bd β hc E
  · rw [abs_zero]
    have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc (fun _ => 1))
    have hq : (0 : ℝ) ≤ Real.exp (2 * |β|) - 1 := by
      have := Real.one_le_exp (x := 2 * |β|) (by positivity); linarith
    exact mul_nonneg hc0 (pow_nonneg hq _)

#print axioms zwR_abs_le

/-- **`|diffTerm| ≤ 2c · (e^{2|β|} − 1)^(|E| + |F|)`** for `O` bounded by `c`.

DERIVED: the `0` is `hN`; the leading `2` counts the two products; the `2` and `1` in the
exponential are `subset_weight_bound`'s. -/
theorem diffTerm_abs_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ) (P' P : Finset Pq)
    {O : (Lk → MassGap.SUN.SU Nc) → ℝ} {c : ℝ} (hc : ∀ U, |O U| ≤ c)
    (q : Finset Pq × Finset Pq) :
    |diffTerm (Nc := Nc) bd β P' P O q|
      ≤ 2 * c * (Real.exp (2 * |β|) - 1) ^ (q.1.card + q.2.card) := by
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc (fun _ => 1))
  have hq : (0 : ℝ) ≤ Real.exp (2 * |β|) - 1 := by
    have := Real.one_le_exp (x := 2 * |β|) (by positivity); linarith
  have h1 : ∀ U : Lk → MassGap.SUN.SU Nc, |(fun _ => (1 : ℝ)) U| ≤ 1 := fun U => by simp
  have e1 := zwR_abs_le hN bd β P' hc q.1
  have e2 := zwR_abs_le hN bd β P h1 q.2
  have e3 := zwR_abs_le hN bd β P hc q.2
  have e4 := zwR_abs_le hN bd β P' h1 q.1
  have key := abs_sub_mul_le_crs e1 e2 e3 e4 (mul_nonneg hc0 (pow_nonneg hq _))
    (mul_nonneg hc0 (pow_nonneg hq _))
  unfold diffTerm
  calc _ ≤ c * (Real.exp (2 * |β|) - 1) ^ q.1.card * (1 * (Real.exp (2 * |β|) - 1) ^ q.2.card)
        + c * (Real.exp (2 * |β|) - 1) ^ q.2.card * (1 * (Real.exp (2 * |β|) - 1) ^ q.1.card) := key
    _ = 2 * c * (Real.exp (2 * |β|) - 1) ^ (q.1.card + q.2.card) := by rw [pow_add]; ring

#print axioms diffTerm_abs_le

/-- **The restricted outside sum over the restricted partition function is at most
`exp (2β · touchDeg · |A|)`.** `∑_{E ⊆ outsideOf A} zw_P(1, E) = subPart (outsideOf A ∩ P)`, and
`StrongCoupling.subPart_le_mul` compares it with `subPart P`, which exceeds it by at most the
plaquettes touching `A` (`StrongCoupling.card_compl_outsideOf_le`).

DERIVED: the `0` is `hN` and the sign of `β`; the `2` is the density's ceiling; the `1` is the
constant observable. -/
theorem outside_div_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) {β : ℝ} (hβ : 0 ≤ β)
    (P A : Finset Pq) :
    (∑ E ∈ (outsideOf bd A).powerset, zwR (Nc := Nc) bd β P (fun _ => (1 : ℝ)) E)
        / Zr (Nc := Nc) bd β P
      ≤ Real.exp (2 * β * ((touchDeg bd * A.card : ℕ) : ℝ)) := by
  classical
  have hZ := Zr_pos hN bd β P
  rw [sum_zwR_one_eq_subPart hN bd β P (outsideOf bd A), div_le_iff₀ hZ, Zr_eq_subPart hN bd β P]
  have hsub : outsideOf bd A ∩ P ⊆ P := Finset.inter_subset_right
  have hle := subPart_le_mul hN bd hβ (W := outsideOf bd A ∩ P) (W' := P) hsub
  have hcard : ((P \ (outsideOf bd A ∩ P)).card : ℝ) ≤ ((touchDeg bd * A.card : ℕ) : ℝ) := by
    have h1 : P \ (outsideOf bd A ∩ P) ⊆ (outsideOf bd A)ᶜ := by
      intro x hx
      rw [Finset.mem_compl]
      intro hxo
      exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_inter.mpr ⟨hxo, (Finset.mem_sdiff.mp hx).1⟩)
    exact_mod_cast le_trans (Finset.card_le_card h1) (card_compl_outsideOf_le bd A)
  have hexp : Real.exp (2 * β * ((P \ (outsideOf bd A ∩ P)).card : ℝ))
      ≤ Real.exp (2 * β * ((touchDeg bd * A.card : ℕ) : ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc subPart (Nc := Nc) bd β (outsideOf bd A ∩ P)
      ≤ Real.exp (2 * β * ((P \ (outsideOf bd A ∩ P)).card : ℝ)) * subPart (Nc := Nc) bd β P := hle
    _ ≤ Real.exp (2 * β * ((touchDeg bd * A.card : ℕ) : ℝ)) * subPart (Nc := Nc) bd β P :=
        mul_le_mul_of_nonneg_right hexp (subPart_pos hN bd β P).le

#print axioms outside_div_le

/-- The restricted outside sum is nonnegative (it is a partition function).

DERIVED: the `0` is `hN` and the bound; the `1` is the constant observable. -/
theorem outside_nonneg (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ) (P A : Finset Pq) :
    0 ≤ ∑ E ∈ (outsideOf bd A).powerset, zwR (Nc := Nc) bd β P (fun _ => (1 : ℝ)) E := by
  rw [sum_zwR_one_eq_subPart hN bd β P]
  exact (subPart_pos hN bd β _).le

#print axioms outside_nonneg

/-- **A core leaving `Q` spans at least `k + 2` plaquettes when the `k`-ball of its base lies in `Q`.**
It contains its base `a` and a plaquette outside `Q`, joined inside the span.

DERIVED: the `2` counts the base and the outside plaquette. -/
theorem coreSpanF_card_ge_of_not_subset (bd : Pq → List (Lk × Bool)) {a : Pq} {Ao Bo : Finset Pq}
    (ha : a ∈ Ao) (Q : Finset Pq) (k : ℕ) (hball : ∀ p ∈ ball bd a k, p ∈ Q)
    {c : Finset Pq × Finset Pq} (hc : IsCorePairF bd a Ao Bo c) (hout : ¬ coreSpanF Ao Bo c ⊆ Q) :
    k + 2 ≤ (coreSpanF Ao Bo c).card := by
  classical
  obtain ⟨b, hb, hbQ⟩ := Finset.not_subset.mp hout
  have h0 : a ∈ coreSpanF Ao Bo c := mem_coreSpanF_left ha Bo c
  have hreach : Reach bd (coreSpanF Ao Bo c) a b := by
    have hm : b ∈ compOf bd (coreSpanF Ao Bo c) a := by rw [hc]; exact hb
    exact (mem_compOf.mp hm).2
  have hnb : b ∉ ball bd a k := fun h => hbQ (hball b h)
  have hne : a ≠ b := fun h => hnb (h ▸ self_mem_ball bd a k)
  have hex : ∃ n, b ∈ ball bd a n := exists_mem_ball_of_reach bd hreach
  have hlt : k < touchLvl bd a b := lt_touchLvl_of_not_mem_ball bd a b k hex hnb
  have hcore := card_ge_of_reach_of_lvl bd (coreSpanF Ao Bo c) (touchLvl bd a) a b k
    (touchLvl_lipschitz bd a) (touchLvl_self bd a) hlt hreach
  have hd' : b ∈ (coreSpanF Ao Bo c).erase a := Finset.mem_erase.mpr ⟨Ne.symm hne, hb⟩
  have hc1 : ((coreSpanF Ao Bo c).erase a).card = (coreSpanF Ao Bo c).card - 1 :=
    Finset.card_erase_of_mem h0
  have hc2 : (((coreSpanF Ao Bo c).erase a).erase b).card
      = ((coreSpanF Ao Bo c).erase a).card - 1 := Finset.card_erase_of_mem hd'
  have h2 : 1 ≤ ((coreSpanF Ao Bo c).erase a).card := Finset.card_pos.mpr ⟨b, hd'⟩
  omega

#print axioms coreSpanF_card_ge_of_not_subset

/-! ## The comparison -/

/-- The weight a core carries in the difference: its two restricted outside sums.

DERIVED: the `1` is the constant observable. -/
noncomputable def outW (bd : Pq → List (Lk × Bool)) (β : ℝ) (P' P : Finset Pq) (A : Finset Pq) : ℝ :=
  (∑ E ∈ (outsideOf bd A).powerset, zwR (Nc := Nc) bd β P' (fun _ => (1 : ℝ)) E)
    * ∑ F ∈ (outsideOf bd A).powerset, zwR (Nc := Nc) bd β P (fun _ => (1 : ℝ)) F

open scoped Classical in
/-- The difference term with the cores inside `Q` removed.

DERIVED: the `0` is the removed value. -/
noncomputable def gCut (bd : Pq → List (Lk × Bool)) (β : ℝ) (P' P : Finset Pq)
    (O : (Lk → MassGap.SUN.SU Nc) → ℝ) (Ao Q : Finset Pq) (c : Finset Pq × Finset Pq) : ℝ :=
  if coreSpanF Ao Ao c ⊆ Q then 0 else diffTerm (Nc := Nc) bd β P' P O c

open scoped Classical in
/-- **Two restrictions of one Wilson system agree near a bounded local observable.** For `O` local on
`Sa` and bounded by `c`, an anchor `Ao ⊇ linkHalo Sa` touch-connected from `a`, a second member
`b ≠ a` of `Ao`, `0 ≤ β` with `coreRate (touchDeg bd) β < 1`, `|Ao| ≤ k + 2`, and the `k`-ball of `a`
inside both `P` and `P'`,

    |meanR P' O − meanR P O|  ≤  coreConstG (2c) (touchDeg bd) β |Ao| · coreRate (touchDeg bd) β ^ (k + 2 − |Ao|).

`meanR_sub_eq` writes the difference as the difference terms over both partition functions; the
resummation (`StrongCoupling.bridging_sum_eq_core_sum_of_fac`, both anchors `Ao`) regroups them by
core; `sum_core_inside_eq_zero` removes the cores inside `P ∩ P'`; `outside_div_le` cancels the two
partition functions core by core; `StrongCoupling.corePairsF_sum_le_of_bound` counts the rest, each
spanning at least `k + 2` plaquettes (`coreSpanF_card_ge_of_not_subset`).

DERIVED: the `0` is `hN` and the sign of `β`; the `1` is the geometric threshold; the `2` in `2c` is
`diffTerm_abs_le`'s two products and in `k + 2` the base and the outside plaquette. -/
theorem meanR_sub_abs_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) {β : ℝ} (hβ : 0 ≤ β)
    (P' P : Finset Pq) {O : (Lk → MassGap.SUN.SU Nc) → ℝ} {Sa : Finset Lk}
    (h : LocalOnLinks (Nc := Nc) Sa O) {c : ℝ} (hc : ∀ U, |O U| ≤ c)
    {Ao : Finset Pq} (hAo : linkHalo bd Sa ⊆ Ao) {a b : Pq} (ha : a ∈ Ao) (hb : b ∈ Ao)
    (hne : a ≠ b) (hconnA : ∀ p ∈ Ao, Reach bd Ao a p)
    (hr : coreRate (touchDeg bd) β < 1) (k : ℕ) (hu : Ao.card ≤ k + 2)
    (hball : ∀ p ∈ ball bd a k, p ∈ P ∩ P') :
    |meanR (Nc := Nc) bd β P' O - meanR (Nc := Nc) bd β P O|
      ≤ coreConstG (2 * c) (touchDeg bd) β Ao.card
        * coreRate (touchDeg bd) β ^ (k + 2 - Ao.card) := by
  classical
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc (fun _ => 1))
  have hZ' := Zr_pos hN bd β P'
  have hZ := Zr_pos hN bd β P
  have hZZ : 0 < Zr (Nc := Nc) bd β P' * Zr (Nc := Nc) bd β P := mul_pos hZ' hZ
  -- every pair is in the resummation's filter: the anchor is connected
  have hall : ∀ q : Finset Pq × Finset Pq,
      ∀ p ∈ Ao ∪ Ao, Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Ao)) a p := by
    intro q p hp
    rw [Finset.union_self] at hp ⊢
    exact reach_mono_crs bd Finset.subset_union_right (hconnA p hp)
  have hres := bridging_sum_eq_core_sum_of_fac bd Ao Ao ha hb hne
    (zwR (Nc := Nc) bd β P' (fun _ => (1 : ℝ))) (zwR (Nc := Nc) bd β P (fun _ => (1 : ℝ)))
    (diffTerm (Nc := Nc) bd β P' P O)
    (fun E F A h1 h2 => diffTerm_fac bd β P' P h hAo E F A h1 h2)
  rw [Finset.filter_true_of_mem (fun q _ => hall q)] at hres
  have hres' : (∑ q : Finset Pq × Finset Pq, diffTerm (Nc := Nc) bd β P' P O q)
      = ∑ c ∈ corePairsF bd a Ao Ao,
          diffTerm (Nc := Nc) bd β P' P O c * outW (Nc := Nc) bd β P' P (coreSpanF Ao Ao c) := hres
  have hz := sum_core_inside_eq_zero bd β P' P O a Ao Ao (outW (Nc := Nc) bd β P' P)
  have h0 : ∑ c ∈ (corePairsF bd a Ao Ao).filter (fun c => coreSpanF Ao Ao c ⊆ P ∩ P'),
      gCut (Nc := Nc) bd β P' P O Ao (P ∩ P') c * outW (Nc := Nc) bd β P' P (coreSpanF Ao Ao c)
        = 0 :=
    Finset.sum_eq_zero (fun c hc => by
      rw [gCut, if_pos (Finset.mem_filter.mp hc).2, zero_mul])
  have hsplit : (∑ q : Finset Pq × Finset Pq, diffTerm (Nc := Nc) bd β P' P O q)
      = ∑ c ∈ corePairsF bd a Ao Ao,
          gCut (Nc := Nc) bd β P' P O Ao (P ∩ P') c
            * outW (Nc := Nc) bd β P' P (coreSpanF Ao Ao c) := by
    rw [hres', ← Finset.sum_filter_add_sum_filter_not (corePairsF bd a Ao Ao)
        (fun c => coreSpanF Ao Ao c ⊆ P ∩ P')
        (fun c => diffTerm (Nc := Nc) bd β P' P O c
          * outW (Nc := Nc) bd β P' P (coreSpanF Ao Ao c)),
      hz, zero_add, ← Finset.sum_filter_add_sum_filter_not (corePairsF bd a Ao Ao)
        (fun c => coreSpanF Ao Ao c ⊆ P ∩ P')
        (fun c => gCut (Nc := Nc) bd β P' P O Ao (P ∩ P') c
          * outW (Nc := Nc) bd β P' P (coreSpanF Ao Ao c)),
      h0, zero_add]
    exact Finset.sum_congr rfl (fun c hc => by rw [gCut, if_neg (Finset.mem_filter.mp hc).2])
  -- the bound on each core
  have hcore : ∀ c ∈ corePairsF bd a Ao Ao,
      |gCut (Nc := Nc) bd β P' P O Ao (P ∩ P') c
          * outW (Nc := Nc) bd β P' P (coreSpanF Ao Ao c)|
        / (Zr (Nc := Nc) bd β P' * Zr (Nc := Nc) bd β P)
        ≤ |gCut (Nc := Nc) bd β P' P O Ao (P ∩ P') c|
          * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Ao c).card : ℕ) : ℝ)) := by
    intro c _
    have h1 := outside_div_le hN bd hβ P' (coreSpanF Ao Ao c)
    have h2 := outside_div_le hN bd hβ P (coreSpanF Ao Ao c)
    have n1 := outside_nonneg hN bd β P' (coreSpanF Ao Ao c)
    have n2 := outside_nonneg hN bd β P (coreSpanF Ao Ao c)
    have hW0 : 0 ≤ outW (Nc := Nc) bd β P' P (coreSpanF Ao Ao c) := mul_nonneg n1 n2
    have hexp : Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Ao c).card : ℕ) : ℝ))
        = Real.exp (2 * β * ((touchDeg bd * (coreSpanF Ao Ao c).card : ℕ) : ℝ))
          * Real.exp (2 * β * ((touchDeg bd * (coreSpanF Ao Ao c).card : ℕ) : ℝ)) := by
      rw [← Real.exp_add]; ring_nf
    have hsplitW : outW (Nc := Nc) bd β P' P (coreSpanF Ao Ao c)
          / (Zr (Nc := Nc) bd β P' * Zr (Nc := Nc) bd β P)
        = ((∑ E ∈ (outsideOf bd (coreSpanF Ao Ao c)).powerset,
              zwR (Nc := Nc) bd β P' (fun _ => (1 : ℝ)) E) / Zr (Nc := Nc) bd β P')
          * ((∑ F ∈ (outsideOf bd (coreSpanF Ao Ao c)).powerset,
              zwR (Nc := Nc) bd β P (fun _ => (1 : ℝ)) F) / Zr (Nc := Nc) bd β P) := by
      unfold outW
      rw [div_mul_div_comm]
    rw [abs_mul, abs_of_nonneg hW0, mul_div_assoc, hexp, hsplitW]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul h1 h2 (div_nonneg n2 hZ.le) (Real.exp_pos _).le) (abs_nonneg _)
  have hq : (0 : ℝ) ≤ Real.exp (2 * β) - 1 := by
    have := Real.one_le_exp (x := 2 * β) (by linarith); linarith
  have hbound := corePairsF_sum_le_of_bound bd ha hβ hr (mul_nonneg zero_le_two hc0)
    (gCut (Nc := Nc) bd β P' P O Ao (P ∩ P'))
    (fun q => by
      rw [gCut]
      split
      · rw [abs_zero]
        exact mul_nonneg (mul_nonneg zero_le_two hc0) (pow_nonneg hq _)
      · have h := diffTerm_abs_le hN bd β P' P hc q
        rwa [abs_of_nonneg hβ] at h)
    k (by rw [Finset.union_self]; exact hu)
    (fun c hc hg0 => by
      have hout : ¬ coreSpanF Ao Ao c ⊆ P ∩ P' := by
        intro hin; apply hg0; rw [gCut, if_pos hin]
      exact coreSpanF_card_ge_of_not_subset bd ha (P ∩ P') k hball (mem_corePairsF.mp hc) hout)
  rw [Finset.union_self] at hbound
  rw [meanR_sub_eq hN bd β P' P O, hsplit, abs_div, abs_of_pos hZZ]
  calc |∑ c ∈ corePairsF bd a Ao Ao, gCut (Nc := Nc) bd β P' P O Ao (P ∩ P') c
          * outW (Nc := Nc) bd β P' P (coreSpanF Ao Ao c)|
        / (Zr (Nc := Nc) bd β P' * Zr (Nc := Nc) bd β P)
      ≤ (∑ c ∈ corePairsF bd a Ao Ao, |gCut (Nc := Nc) bd β P' P O Ao (P ∩ P') c
          * outW (Nc := Nc) bd β P' P (coreSpanF Ao Ao c)|)
        / (Zr (Nc := Nc) bd β P' * Zr (Nc := Nc) bd β P) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr hZZ.le)
    _ = ∑ c ∈ corePairsF bd a Ao Ao, |gCut (Nc := Nc) bd β P' P O Ao (P ∩ P') c
          * outW (Nc := Nc) bd β P' P (coreSpanF Ao Ao c)|
        / (Zr (Nc := Nc) bd β P' * Zr (Nc := Nc) bd β P) := Finset.sum_div _ _ _
    _ ≤ ∑ c ∈ corePairsF bd a Ao Ao, |gCut (Nc := Nc) bd β P' P O Ao (P ∩ P') c|
          * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Ao c).card : ℕ) : ℝ)) :=
        Finset.sum_le_sum (fun c hc => hcore c hc)
    _ ≤ _ := hbound

#print axioms meanR_sub_abs_le

/-! ## The restricted means as Gibbs expectations -/

open scoped Classical in
/-- **The restricted expansion sums to the integral against the restricted Boltzmann weight**:
`∑_E zw_P(O, E) = ∫ O · subBoltz P`, for `O` measurable and bounded. The subsets of `P` expand
`∏_{p ∈ P} e^{−βφ_p} = ∏_{p ∈ P} ((e^{−βφ_p} − 1) + 1)`; `StrongCoupling.subset_sum_eq_subPart` is the
case `O = 1`.

DERIVED: the `0` is `hN`; the `1` is the unit added back to each activated weight. -/
theorem sum_zwR_eq_integral (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ) (P : Finset Pq)
    {O : (Lk → MassGap.SUN.SU Nc) → ℝ} (hm : Measurable O) {c : ℝ} (hc : ∀ U, |O U| ≤ c) :
    ∑ E : Finset Pq, zwR (Nc := Nc) bd β P O E
      = ∫ U, O U * subBoltz (Nc := Nc) bd β P U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := by
  classical
  have hfil : (Finset.univ : Finset (Finset Pq)).filter (fun E => E ⊆ P) = P.powerset := by
    ext E; simp
  have hsum : ∑ E : Finset Pq, zwR (Nc := Nc) bd β P O E
      = ∑ E ∈ P.powerset, zwFull (Nc := Nc) bd β O E := by
    simp only [zwR]
    rw [← Finset.sum_filter, hfil]
  rw [hsum]
  unfold zwFull
  simp only [wfun_apply]
  rw [← integral_finsetSum _ (fun E _ => integrable_obsFull_mul_wprod hN bd β hm hc E)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
  simp only
  rw [← Finset.mul_sum]
  congr 1
  unfold subBoltz
  have hone : ∀ p : Pq, Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U)))
      = (Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1) + 1 := by
    intro p; ring
  rw [Finset.prod_congr rfl (fun p _ => hone p), Finset.prod_add]
  exact Finset.sum_congr rfl (fun E _ => by simp)

#print axioms sum_zwR_eq_integral

/-- **`meanR P O` is the Gibbs expectation of `O` with the action restricted to `P`**:
`(∫ O · subBoltz P) / (∫ subBoltz P)`.

DERIVED: the `0` is `hN`. -/
theorem meanR_eq_integral (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ) (P : Finset Pq)
    {O : (Lk → MassGap.SUN.SU Nc) → ℝ} (hm : Measurable O) {c : ℝ} (hc : ∀ U, |O U| ≤ c) :
    meanR (Nc := Nc) bd β P O
      = (∫ U, O U * subBoltz (Nc := Nc) bd β P U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        / ∫ U, subBoltz (Nc := Nc) bd β P U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := by
  unfold meanR
  rw [sum_zwR_eq_integral hN bd β P hm hc, Zr_eq_subPart hN bd β P]
  rfl

#print axioms meanR_eq_integral

end MassGap.BoxCompare
