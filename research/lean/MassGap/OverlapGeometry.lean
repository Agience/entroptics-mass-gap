import Mathlib
import MassGap.TileGeometry

noncomputable section

/-!
# MassGap.OverlapGeometry — an 81-colour cover of every periodic lattice by overlapping boxes

The non-overlapping tiling of `TileGeometry` has a block gap that falls like `a/ℓ` at fixed physical box size
(the slow modes sit on the box interfaces). Overlapping boxes keep the gap: each box here is the product of
two cyclically consecutive cells per direction, so neighbouring boxes share a full cell.

Each direction of the circle of length `L ≥ 3n` is cut into `q = 3⌊L/3n⌋` cells (a multiple of three): cell
`k < q − 1` is `[kn, kn + n)`, the last cell takes the rest, `[(q − 1)n, L)`, of length `n` to `4n − 1`. The
box `K` holds the links whose base site lies, in every direction `μ`, in cell `K μ` or in cell
`(K μ + 1) mod q`; the box with `K μ = q − 1` wraps around the circle. Its colour is `K mod 3` in each
direction (81 colours).

## What it gives

1. **Cells** (`qO`, `cellO`): `three_le_qO`, `qO_mod`, `cellO_lt`, `cellO_window` (`cellO·n ≤ x < cellO·n + 4n`),
   `cellO_succ`, `lt_of_cellO_eq_zero`; links sharing a plaquette have related cells
   (`cellRelO_of_sharePlaq`, with `TileGeometry.CellRel`).
2. **Offsets as integers** (`COff`): `b ≡ a + t (mod q)` written as three linear alternatives, so that every
   cyclic statement is decided by `omega`. A cell of box `K` and a related cell of box `K'` put `K' μ` within
   `±2` of `K μ` (`pair_offset`); with `K μ ≡ K' μ (mod 3)`, `K μ ≠ K' μ` and `3 ∣ q` that is impossible
   (`not_coff_of_mod`).
3. **Boxes** (`ovBox`, `ocol`): distinct boxes of one colour share no link and no plaquette
   (`not_near_of_ocol`, `ovBox_disjoint_of_ocol`); every box shares a link or a plaquette with at most
   `624 = 5⁴ − 1` others (`card_oadj_le`, `card_oadj_le'`).
4. **The potential across a box**: a potential moving by at most one per cyclic unit step moves by at most
   `d` along `d` cyclic steps (`cyc_path`, no wrap excluded); the two cells of a box lie on one cyclic run of
   fewer than `5n` sites from `kn` (`pair_start`, the wrapping box included), so the potential moves by less
   than `5n` inside a box (`psi_pair`) and `psiL` rises by at most `5n` from a box to any link sharing a
   plaquette with it (`psiL_ov_le`).

No divisibility of the extent is needed: the bounds hold at every extent `L ≥ 3n`.

DERIVED (module-wide): `4` the spacetime dimension; `3` the colour count per direction, the factor making
the cell count a multiple of three, and the least cell count; `4` also the bound on the last cell's length in
units of `n` (`L < (q + 3) n`); `5 = 1 + 4` the cells' joint length bound and the five offsets `−2 … 2`;
`624 = 5⁴ − 1`; `1` the unit step and the successor writing the extent; `2` the offset bound.
-/

namespace MassGap.OverlapGeometry

open MassGap MassGap.HeatBath MassGap.KnabeCriterion MassGap.HeatBathLocal MassGap.TileGeometry

/-! ## 1. Cells of a circle -/

/-- **The number of cells** on a circle of length `L` at side `n`: `3⌊L/3n⌋`.

DERIVED: `3`. -/
def qO (n L : ℕ) : ℕ := 3 * (L / (3 * n))

/-- **The cell of a coordinate** `x ∈ [0, L)`: `min(⌊x/n⌋, q − 1)`.

DERIVED: `1` the last index. -/
def cellO (n L x : ℕ) : ℕ := min (x / n) (qO n L - 1)

/-- DERIVED: `3` the least cell count; `1` the least side. -/
theorem three_le_qO {n L : ℕ} (hn : 1 ≤ n) (hL : 3 * n ≤ L) : 3 ≤ qO n L := by
  have : 1 ≤ L / (3 * n) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  unfold qO
  generalize L / (3 * n) = a at *
  omega

#print axioms three_le_qO

/-- DERIVED: `3` the colour modulus. -/
theorem qO_mod (n L : ℕ) : qO n L % 3 = 0 := Nat.mul_mod_right 3 _

#print axioms qO_mod

/-- `q n ≤ L`.

DERIVED: no numeral. -/
theorem qO_mul_le (n L : ℕ) : qO n L * n ≤ L := by
  unfold qO
  have h := Nat.div_mul_le_self L (3 * n)
  calc 3 * (L / (3 * n)) * n = L / (3 * n) * (3 * n) := by ring
    _ ≤ L := h

#print axioms qO_mul_le

/-- `L < (q + 3) n`.

DERIVED: `3` the cell count's factor. -/
theorem lt_qO_add (n L : ℕ) (hn : 1 ≤ n) : L < (qO n L + 3) * n := by
  unfold qO
  have h1 := Nat.div_add_mod L (3 * n)
  have h2 := Nat.mod_lt L (show 0 < 3 * n by omega)
  nlinarith

#print axioms lt_qO_add

/-- DERIVED: `1` the last index; `3` the least cell count (`3n ≤ L`). -/
theorem cellO_lt{n L : ℕ} (hn : 1 ≤ n) (hL : 3 * n ≤ L) (x : ℕ) : cellO n L x < qO n L := by
  have := three_le_qO hn hL
  have := min_le_right (x / n) (qO n L - 1)
  unfold cellO
  omega

#print axioms cellO_lt

/-- **The cell's window**: `cellO·n ≤ x < cellO·n + 4n` for `x < L`.

DERIVED: `4` the last cell's length bound; `3` the least cell count (`3n ≤ L`). -/
theorem cellO_window{n L : ℕ} (hn : 1 ≤ n) (hL : 3 * n ≤ L) {x : ℕ} (hx : x < L) :
    cellO n L x * n ≤ x ∧ x < cellO n L x * n + 4 * n := by
  have hq := three_le_qO hn hL
  have hlt := lt_qO_add n L hn
  have h1 := Nat.mul_div_le x n
  have h2 := Nat.lt_mul_div_succ x (show 0 < n by omega)
  obtain ⟨q', hq'⟩ : ∃ q', qO n L = q' + 1 := ⟨qO n L - 1, by omega⟩
  rw [hq'] at hlt
  unfold cellO
  rw [hq', show q' + 1 - 1 = q' by omega]
  rcases le_total (x / n) q' with h | h
  · rw [min_eq_left h]
    constructor <;> nlinarith
  · rw [min_eq_right h]
    have h3 : q' * n ≤ x / n * n := Nat.mul_le_mul_right n h
    constructor <;> nlinarith

#print axioms cellO_window

/-- **One step moves the cell by `0` or `+1`** (cyclically).

DERIVED: `1` the step; `2` in the decomposition of the cell count; `3` the least cell count (`3n ≤ L`). -/
theorem cellO_succ{n L : ℕ} (hn : 1 ≤ n) (hL : 3 * n ≤ L) {x : ℕ} (_hx : x + 1 < L) :
    cellO n L (x + 1) = cellO n L x ∨ cellO n L (x + 1) = (cellO n L x + 1) % qO n L := by
  have hq := three_le_qO hn hL
  have hs := Nat.succ_div (a := x) (b := n)
  have hmono : x / n ≤ (x + 1) / n := Nat.div_le_div_right (by omega)
  obtain ⟨q', hq'⟩ : ∃ q', qO n L = q' + 2 := ⟨qO n L - 2, by omega⟩
  unfold cellO
  rw [hq', show q' + 2 - 1 = q' + 1 by omega]
  rcases le_total (q' + 1) (x / n) with h | h
  · left
    rw [min_eq_right h, min_eq_right (h.trans hmono)]
  · rw [min_eq_left h]
    split_ifs at hs with hd
    · by_cases hlast : x / n = q' + 1
      · left
        rw [min_eq_right (show q' + 1 ≤ (x + 1) / n by omega), hlast]
      · right
        rw [min_eq_left (show (x + 1) / n ≤ q' + 1 by omega), hs, Nat.mod_eq_of_lt (by omega)]
    · left
      rw [hs, add_zero, min_eq_left h]

#print axioms cellO_succ

/-- The last coordinate is in the last cell.

DERIVED: `1` the last coordinate and the last index; `2` in the decomposition; `3` the least cell count
(`3n ≤ L`). -/
theorem cellO_last{n L : ℕ} (hn : 1 ≤ n) (hL : 3 * n ≤ L) : cellO n L (L - 1) = qO n L - 1 := by
  have hq := three_le_qO hn hL
  have hle := qO_mul_le n L
  unfold cellO
  apply min_eq_right
  rw [Nat.le_div_iff_mul_le (by omega)]
  obtain ⟨q', hq'⟩ : ∃ q', qO n L = q' + 2 := ⟨qO n L - 2, by omega⟩
  rw [hq'] at hle ⊢
  rw [show q' + 2 - 1 = q' + 1 by omega]
  have : (q' + 1) * n + 1 ≤ L := by nlinarith
  omega

#print axioms cellO_last

/-- DERIVED: `0` the first cell. -/
theorem cellO_zero (n L : ℕ) : cellO n L 0 = 0 := by
  unfold cellO
  simp

#print axioms cellO_zero

/-- **The first cell has length `n`**: a coordinate in cell `0` is below `n` (the cell count is at least
three, so cell `0` is not the last).

DERIVED: `0` the first cell; `1` the successor; `3` the least cell count (`3n ≤ L`). -/
theorem lt_of_cellO_eq_zero{n L x : ℕ} (hn : 1 ≤ n) (hL : 3 * n ≤ L) (h : cellO n L x = 0) : x < n := by
  have hq := three_le_qO hn hL
  unfold cellO at h
  have hx : x / n = 0 := by
    rcases le_total (x / n) (qO n L - 1) with h' | h'
    · rwa [min_eq_left h'] at h
    · rw [min_eq_right h'] at h
      omega
  have h2 := Nat.lt_mul_div_succ x (show 0 < n by omega)
  rw [hx, zero_add, mul_one] at h2
  exact h2

#print axioms lt_of_cellO_eq_zero

/-- A cyclic unit step of torus coordinates keeps the cells related.

DERIVED: `1` the step and the successor writing the extent; `3` the least cell count (`3n ≤ M + 1`). -/
theorem cellRelO_step{n M : ℕ} (hn : 1 ≤ n) (hL : 3 * n ≤ M + 1) (s : Fin (M + 1)) :
    CellRel (qO n (M + 1)) (cellO n (M + 1) s) (cellO n (M + 1) ((s + 1 : Fin (M + 1)) : ℕ)) := by
  rcases val_add_one_cases s with h | ⟨hsM, h0⟩
  · rw [h]
    have hx : (s : ℕ) + 1 < M + 1 := by
      have := ((s + 1 : Fin (M + 1))).isLt
      omega
    rcases cellO_succ hn hL hx with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rw [h0, cellO_zero, hsM]
    have hl := cellO_last hn hL
    rw [show M + 1 - 1 = M by omega] at hl
    rw [hl]
    have hq := three_le_qO hn hL
    right; left
    rw [show qO n (M + 1) - 1 + 1 = qO n (M + 1) by omega, Nat.mod_self]

#print axioms cellRelO_step

/-- **Links sharing a plaquette have related cells in every direction.**

DERIVED: `0`, `1`, `−1` the coordinate steps; `3` the least cell count (`3n ≤ M + 1`). -/
theorem cellRelO_of_sharePlaq{n M : ℕ} (hn : 1 ≤ n) (hL : 3 * n ≤ M + 1)
    {l l' : WilsonHypercubic.Link 4 (M + 1)} (h : SharePlaq (bdT M) l l') (μ : Fin 4) :
    CellRel (qO n (M + 1)) (cellO n (M + 1) (l.2 μ)) (cellO n (M + 1) (l'.2 μ)) := by
  obtain ⟨_, _, _, hd⟩ := BoxPatch.sharePlaq_disp h
  have hdμ := hd μ
  simp only [Pi.sub_apply] at hdμ
  rcases hdμ with h0 | h1 | h2
  · rw [sub_eq_zero.mp h0]
    exact Or.inl rfl
  · have e : l'.2 μ = l.2 μ + 1 := by rw [← h1]; abel
    rw [e]
    exact cellRelO_step hn hL (l.2 μ)
  · have e : l.2 μ = l'.2 μ + 1 := by
      have : l'.2 μ = -1 + l.2 μ := sub_eq_iff_eq_add.mp h2
      rw [this]; abel
    rw [e]
    exact (cellRelO_step hn hL (l'.2 μ)).symm

#print axioms cellRelO_of_sharePlaq

/-! ## 2. Cyclic offsets as linear alternatives -/

/-- **`b ≡ a + t (mod q)`** for `a, b < q` and `|t| < q`, as three linear alternatives.

DERIVED: no numeral. -/
def COff (q a b : ℕ) (t : ℤ) : Prop :=
  (b : ℤ) = a + t ∨ (b : ℤ) = a + t - q ∨ (b : ℤ) = a + t + q

/-- The cyclic successor below `q`.

DERIVED: `1` the step; `0` the wrap value. -/
theorem succ_mod_cases {a q : ℕ} (h : a < q) :
    ((a + 1) % q = a + 1 ∧ a + 1 < q) ∨ ((a + 1) % q = 0 ∧ a + 1 = q) := by
  rcases Nat.lt_or_ge (a + 1) q with h' | h'
  · exact Or.inl ⟨Nat.mod_eq_of_lt h', h'⟩
  · have e : a + 1 = q := by omega
    exact Or.inr ⟨by rw [e, Nat.mod_self], e⟩

#print axioms succ_mod_cases

/-- Related cells differ by `−1`, `0` or `1` cyclically.

DERIVED: `1` the step. -/
theorem coff_of_cellRel {q a b : ℕ} (ha : a < q) (hb : b < q) (h : CellRel q a b) :
    ∃ t : ℤ, -1 ≤ t ∧ t ≤ 1 ∧ COff q a b t := by
  rcases h with h | h | h
  · exact ⟨0, by norm_num, by norm_num, Or.inl (by omega)⟩
  · refine ⟨1, by norm_num, le_rfl, ?_⟩
    unfold COff
    rcases succ_mod_cases ha with ⟨e, e'⟩ | ⟨e, e'⟩ <;> rw [e] at h <;> omega
  · refine ⟨-1, le_rfl, by norm_num, ?_⟩
    unfold COff
    rcases succ_mod_cases hb with ⟨e, e'⟩ | ⟨e, e'⟩ <;> rw [e] at h <;> omega

#print axioms coff_of_cellRel

/-- **A cell of the pair starting at `k`**: `k` itself or its cyclic successor.

DERIVED: `1` the step. -/
def InPair (q k c : ℕ) : Prop := c = k ∨ c = (k + 1) % q

/-- DERIVED: `0`, `1` the two offsets. -/
theorem coff_of_inPair {q k c : ℕ} (hk : k < q) (h : InPair q k c) :
    ∃ u : ℤ, 0 ≤ u ∧ u ≤ 1 ∧ COff q k c u := by
  rcases h with h | h
  · exact ⟨0, le_rfl, by norm_num, Or.inl (by omega)⟩
  · refine ⟨1, by norm_num, le_rfl, ?_⟩
    unfold COff
    rcases succ_mod_cases hk with ⟨e, e'⟩ | ⟨e, e'⟩ <;> rw [e] at h <;> omega

#print axioms coff_of_inPair

/-- **Two pairs with related cells start within `±2`.**

DERIVED: `2 = 1 + 1` the offset bound; `3` the least cell count. -/
theorem pair_offset {q k k' c c' : ℕ} (hq : 3 ≤ q) (hk : k < q) (hk' : k' < q) (hc : c < q)
    (hc' : c' < q) (h : InPair q k c) (h' : InPair q k' c') (hr : CellRel q c c') :
    ∃ t : ℤ, -2 ≤ t ∧ t ≤ 2 ∧ COff q k k' t := by
  obtain ⟨u, hu0, hu1, hu⟩ := coff_of_inPair hk h
  obtain ⟨u', hu0', hu1', hu'⟩ := coff_of_inPair hk' h'
  obtain ⟨r, hr0, hr1, hrr⟩ := coff_of_cellRel hc hc' hr
  refine ⟨u + r - u', by omega, by omega, ?_⟩
  unfold COff at *
  omega

#print axioms pair_offset

/-- **Equal residues mod three, distinct, at most two apart: impossible** when `3 ∣ q`.

DERIVED: `3` the colour modulus; `2` the offset bound. -/
theorem not_coff_of_mod {q k k' : ℕ} (hq : q % 3 = 0) (hk : k < q) (hk' : k' < q) (hne : k ≠ k')
    (hm : k % 3 = k' % 3) {t : ℤ} (ht0 : -2 ≤ t) (ht1 : t ≤ 2) : ¬ COff q k k' t := by
  unfold COff
  omega

#print axioms not_coff_of_mod

/-! ## 3. Boxes and colours -/

variable {n M : ℕ}

/-- **The box** starting at cells `K`: the links whose base site lies, in every direction, in cell `K μ` or
in the next cell (cyclically).

DERIVED: `4` the dimension; `1` the successor writing the extent and the next cell. -/
def ovBox (n M : ℕ) (K : Fin 4 → Fin (qO n (M + 1))) : Finset (WilsonHypercubic.Link 4 (M + 1)) :=
  Finset.univ.filter (fun l => ∀ μ, cellO n (M + 1) (l.2 μ) = (K μ : ℕ) ∨
    cellO n (M + 1) (l.2 μ) = ((K μ : ℕ) + 1) % qO n (M + 1))

/-- DERIVED: no numeral. -/
theorem mem_ovBox {K : Fin 4 → Fin (qO n (M + 1))} {l : WilsonHypercubic.Link 4 (M + 1)} :
    l ∈ ovBox n M K ↔ ∀ μ, InPair (qO n (M + 1)) (K μ) (cellO n (M + 1) (l.2 μ)) := by
  unfold ovBox InPair
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

#print axioms mem_ovBox

/-- **The colour of a box**: its starting cells mod three.

DERIVED: `3` the colour modulus. -/
def ocol (K : Fin 4 → Fin (qO n (M + 1))) : Fin 4 → Fin 3 :=
  fun μ => ⟨(K μ : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩

/-- Equal or plaquette-sharing links have related cells.

DERIVED: `3` the least cell count (`3n ≤ M + 1`). -/
theorem cellRel_of_near(hn : 1 ≤ n) (hL : 3 * n ≤ M + 1) {l l' : WilsonHypercubic.Link 4 (M + 1)}
    (h : l = l' ∨ SharePlaq (bdT M) l l') (μ : Fin 4) :
    CellRel (qO n (M + 1)) (cellO n (M + 1) (l.2 μ)) (cellO n (M + 1) (l'.2 μ)) := by
  rcases h with h | h
  · subst h
    exact Or.inl rfl
  · exact cellRelO_of_sharePlaq hn hL h μ

#print axioms cellRel_of_near

/-- **Boxes holding equal or plaquette-sharing links start within `±2` in every direction.**

DERIVED: `2` the offset bound; `3` the least cell count (`3n ≤ M + 1`). -/
theorem offset_of_near(hn : 1 ≤ n) (hL : 3 * n ≤ M + 1) {K K' : Fin 4 → Fin (qO n (M + 1))}
    {l l' : WilsonHypercubic.Link 4 (M + 1)} (hl : l ∈ ovBox n M K) (hl' : l' ∈ ovBox n M K')
    (h : l = l' ∨ SharePlaq (bdT M) l l') (μ : Fin 4) :
    ∃ t : ℤ, -2 ≤ t ∧ t ≤ 2 ∧ COff (qO n (M + 1)) (K μ) (K' μ) t :=
  pair_offset (three_le_qO hn hL) (K μ).isLt (K' μ).isLt (cellO_lt hn hL _) (cellO_lt hn hL _)
    ((mem_ovBox.mp hl) μ) ((mem_ovBox.mp hl') μ) (cellRel_of_near hn hL h μ)

#print axioms offset_of_near

/-- **Distinct boxes of one colour share no link and no plaquette.**

DERIVED: `3` the colour modulus. -/
theorem not_near_of_ocol (hn : 1 ≤ n) (hL : 3 * n ≤ M + 1) {K K' : Fin 4 → Fin (qO n (M + 1))}
    (hne : K ≠ K') (hc : ocol K = ocol K') {l l' : WilsonHypercubic.Link 4 (M + 1)}
    (hl : l ∈ ovBox n M K) (hl' : l' ∈ ovBox n M K') : ¬ (l = l' ∨ SharePlaq (bdT M) l l') := by
  intro h
  apply hne
  funext μ
  apply Fin.ext
  by_contra hμ
  obtain ⟨t, ht0, ht1, hoff⟩ := offset_of_near hn hL hl hl' h μ
  have hp : (K μ : ℕ) % 3 = (K' μ : ℕ) % 3 := congrArg Fin.val (congrFun hc μ)
  exact not_coff_of_mod (qO_mod n (M + 1)) (K μ).isLt (K' μ).isLt hμ hp ht0 ht1 hoff

#print axioms not_near_of_ocol

/-- **Distinct boxes of one colour are disjoint.**

DERIVED: `3` the least cell count (`3n ≤ M + 1`). -/
theorem ovBox_disjoint_of_ocol(hn : 1 ≤ n) (hL : 3 * n ≤ M + 1) {K K' : Fin 4 → Fin (qO n (M + 1))}
    (hne : K ≠ K') (hc : ocol K = ocol K') : Disjoint (ovBox n M K) (ovBox n M K') := by
  rw [Finset.disjoint_left]
  intro l hl hl'
  exact not_near_of_ocol hn hL hne hc hl hl' (Or.inl rfl)

#print axioms ovBox_disjoint_of_ocol

/-- **Adjacent boxes**: distinct, with a link of one equal to, or sharing a plaquette with, a link of the
other.

DERIVED: no numeral. -/
def OAdj (n M : ℕ) (K K' : Fin 4 → Fin (qO n (M + 1))) : Prop :=
  K' ≠ K ∧ ∃ l ∈ ovBox n M K, ∃ l' ∈ ovBox n M K', l = l' ∨ SharePlaq (bdT M) l l'

instance (K : Fin 4 → Fin (qO n (M + 1))) : DecidablePred (OAdj n M K) := by
  classical
  exact fun _ => inferInstance

/-- Adjacency is symmetric.

DERIVED: no numeral. -/
theorem oadj_symm {K K' : Fin 4 → Fin (qO n (M + 1))} (h : OAdj n M K K') : OAdj n M K' K := by
  obtain ⟨hne, l, hl, l', hl', h⟩ := h
  refine ⟨fun e => hne e.symm, l', hl', l, hl, ?_⟩
  rcases h with h | ⟨p, h1, h2⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨p, h2, h1⟩

#print axioms oadj_symm

/-- The offset of an adjacent box in one direction, as a member of `Fin 5` (`e − 2 ∈ [−2, 2]`).

DERIVED: `5` the offsets; `2` the shift; `3` the least cell count (`3n ≤ M + 1`). -/
theorem exists_off5(hn : 1 ≤ n) (hL : 3 * n ≤ M + 1) {K K' : Fin 4 → Fin (qO n (M + 1))}
    (h : OAdj n M K K') (μ : Fin 4) :
    ∃ e : Fin 5, COff (qO n (M + 1)) (K μ) (K' μ) (((e : ℕ) : ℤ) - 2) := by
  obtain ⟨_, l, hl, l', hl', hr⟩ := h
  obtain ⟨t, ht0, ht1, hoff⟩ := offset_of_near hn hL hl hl' hr μ
  have h2 := Int.toNat_of_nonneg (show 0 ≤ t + 2 by omega)
  refine ⟨⟨(t + 2).toNat, by omega⟩, ?_⟩
  have e : (((t + 2).toNat : ℕ) : ℤ) - 2 = t := by omega
  show COff _ _ _ ((((t + 2).toNat : ℕ) : ℤ) - 2)
  rw [e]
  exact hoff

#print axioms exists_off5

/-- **Each box is adjacent to at most `624` others** (`5⁴ − 1`).

DERIVED: `624 = 5⁴ − 1`; `5` the offsets; `4` the dimension; `2` the zero offset; `3` the least cell
count (`3n ≤ M + 1`). -/
theorem card_oadj_le(hn : 1 ≤ n) (hL : 3 * n ≤ M + 1) (K : Fin 4 → Fin (qO n (M + 1))) :
    (Finset.univ.filter (OAdj n M K)).card ≤ 624 := by
  classical
  have hex := fun K' (h : OAdj n M K K') μ => exists_off5 hn hL h μ
  let f : (Fin 4 → Fin (qO n (M + 1))) → (Fin 4 → Fin 5) := fun K' =>
    if h : OAdj n M K K' then fun μ => Classical.choose (hex K' h μ) else fun _ => 2
  have hf : ∀ K' (h : OAdj n M K K') μ,
      COff (qO n (M + 1)) (K μ) (K' μ) ((((f K' μ : Fin 5) : ℕ) : ℤ) - 2) := by
    intro K' h μ
    have e : f K' = fun μ => Classical.choose (hex K' h μ) := dif_pos h
    rw [e]
    exact Classical.choose_spec (hex K' h μ)
  have h2 : ((2 : Fin 5) : ℕ) = 2 := rfl
  calc (Finset.univ.filter (OAdj n M K)).card
      ≤ ((Finset.univ : Finset (Fin 4 → Fin 5)).erase (fun _ => 2)).card := by
        refine Finset.card_le_card_of_injOn f (fun K' hK' => ?_) (fun K₁ hK₁ K₂ hK₂ h12 => ?_)
        · have hK'a := (Finset.mem_filter.mp (Finset.mem_coe.mp hK')).2
          refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨fun hfe => hK'a.1 ?_, Finset.mem_univ _⟩)
          funext μ
          apply Fin.ext
          have h1 := hf K' hK'a μ
          have hμ : f K' μ = 2 := congrFun hfe μ
          rw [hμ, h2] at h1
          have hk := (K μ).isLt
          have hk' := (K' μ).isLt
          unfold COff at h1
          omega
        · have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hK₁)).2
          have h2' := (Finset.mem_filter.mp (Finset.mem_coe.mp hK₂)).2
          funext μ
          apply Fin.ext
          have e1 := hf K₁ h1 μ
          have e2 := hf K₂ h2' μ
          rw [h12] at e1
          have hk := (K μ).isLt
          have hk1 := (K₁ μ).isLt
          have hk2 := (K₂ μ).isLt
          unfold COff at e1 e2
          omega
    _ = 624 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
        simp

#print axioms card_oadj_le

/-- The column count: at most `624` boxes are adjacent to a given one, in the second argument.

DERIVED: `624`; `3` the least cell count (`3n ≤ M + 1`). -/
theorem card_oadj_le'(hn : 1 ≤ n) (hL : 3 * n ≤ M + 1) (K' : Fin 4 → Fin (qO n (M + 1))) :
    (Finset.univ.filter (fun K => OAdj n M K K')).card ≤ 624 := by
  classical
  have e : Finset.univ.filter (fun K => OAdj n M K K') = Finset.univ.filter (OAdj n M K') := by
    ext K
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨oadj_symm, oadj_symm⟩
  rw [e]
  exact card_oadj_le hn hL K'

#print axioms card_oadj_le'

/-! ## 4. The potential across a box -/

open Fin.NatCast in
/-- **The cyclic path lemma.** A potential moving by at most one per cyclic unit step (the wrap from the
last site to `0` included) moves by at most `d` along `d` cyclic steps.

DERIVED: `1` the unit step. -/
theorem cyc_path {M : ℕ} (φ : Fin (M + 1) → ℕ)
    (hφ : ∀ s : Fin (M + 1), φ (s + 1) ≤ φ s + 1 ∧ φ s ≤ φ (s + 1) + 1) :
    ∀ d : ℕ, ∀ x : Fin (M + 1),
      φ (x + (d : Fin (M + 1))) ≤ φ x + d ∧ φ x ≤ φ (x + (d : Fin (M + 1))) + d := by
  intro d
  induction d with
  | zero =>
    intro x
    simp
  | succ d ih =>
    intro x
    have e : x + ((d + 1 : ℕ) : Fin (M + 1)) = (x + (d : Fin (M + 1))) + 1 := by
      rw [Nat.cast_succ, add_assoc]
    rw [e]
    have h1 := ih x
    have h2 := hφ (x + (d : Fin (M + 1)))
    omega

#print axioms cyc_path

open Fin.NatCast in
/-- **The two cells of a box lie on one cyclic run of fewer than `5n` sites from `kn`**, the wrapping box
(`k = q − 1`, whose second cell is cell `0`) included.

DERIVED: `5 = 1 + 4` the run length; `4` the last cell's bound; `1` the next cell; `3` the least cell
count (`3n ≤ M + 1`). -/
theorem pair_start(hn : 1 ≤ n) (hL : 3 * n ≤ M + 1) {k : ℕ} (hk : k < qO n (M + 1))
    {x : Fin (M + 1)} (hx : InPair (qO n (M + 1)) k (cellO n (M + 1) x)) :
    ∃ d : ℕ, d < 5 * n ∧ x = ((k * n : ℕ) : Fin (M + 1)) + ((d : ℕ) : Fin (M + 1)) := by
  have hq := three_le_qO hn hL
  have hlt := lt_qO_add n (M + 1) hn
  have hle := qO_mul_le n (M + 1)
  have hxL := x.isLt
  have w := cellO_window hn hL hxL
  have hcast : ∀ m : ℕ, m = (x : ℕ) → ((m : ℕ) : Fin (M + 1)) = x := by
    rintro m rfl
    exact Fin.cast_val_eq_self x
  have hkn : (k + 1) * n = k * n + n := by ring
  rcases hx with h | h
  · rw [h] at w
    refine ⟨(x : ℕ) - k * n, by omega, ?_⟩
    rw [← Nat.cast_add]
    exact (hcast _ (by omega)).symm
  · rcases succ_mod_cases hk with ⟨e, e'⟩ | ⟨e, e'⟩
    · rw [h, e] at w
      refine ⟨(x : ℕ) - k * n, by omega, ?_⟩
      rw [← Nat.cast_add]
      exact (hcast _ (by omega)).symm
    · rw [e] at h
      have hx0 : (x : ℕ) < n := lt_of_cellO_eq_zero hn hL h
      have h4 : (qO n (M + 1) + 3) * n = k * n + 4 * n := by rw [← e']; ring
      have hkM : k * n ≤ M + 1 := by
        have : k * n ≤ qO n (M + 1) * n := Nat.mul_le_mul_right n (by omega)
        omega
      refine ⟨M + 1 - k * n + x, by omega, ?_⟩
      rw [← Nat.cast_add]
      apply Fin.ext
      rw [Fin.val_natCast, show k * n + (M + 1 - k * n + (x : ℕ)) = (M + 1) + (x : ℕ) by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt hxL]

#print axioms pair_start

open Fin.NatCast in
/-- **Inside one box a step-Lipschitz potential moves by less than `5n`.**

DERIVED: `5` the run length; `1` the step; `3` the least cell count (`3n ≤ M + 1`). -/
theorem psi_pair(hn : 1 ≤ n) (hL : 3 * n ≤ M + 1) (φ : Fin (M + 1) → ℕ)
    (hφ : ∀ s : Fin (M + 1), φ (s + 1) ≤ φ s + 1 ∧ φ s ≤ φ (s + 1) + 1)
    {k : ℕ} (hk : k < qO n (M + 1)) {x y : Fin (M + 1)}
    (hx : InPair (qO n (M + 1)) k (cellO n (M + 1) x))
    (hy : InPair (qO n (M + 1)) k (cellO n (M + 1) y)) :
    φ y + 1 ≤ φ x + 5 * n := by
  obtain ⟨dx, hdx, ex⟩ := pair_start hn hL hk hx
  obtain ⟨dy, hdy, ey⟩ := pair_start hn hL hk hy
  rcases le_total dx dy with h | h
  · have e : y = x + ((dy - dx : ℕ) : Fin (M + 1)) := by
      rw [ey, ex, add_assoc, ← Nat.cast_add dx, Nat.add_sub_of_le h]
    have := (cyc_path φ hφ (dy - dx) x).1
    rw [← e] at this
    omega
  · have e : x = y + ((dx - dy : ℕ) : Fin (M + 1)) := by
      rw [ey, ex, add_assoc, ← Nat.cast_add dy, Nat.add_sub_of_le h]
    have := (cyc_path φ hφ (dx - dy) y).2
    rw [← e] at this
    omega

#print axioms psi_pair

/-- **`psiL` rises by at most `5n` from a box to a link sharing a plaquette with it.**

DERIVED: `5` the run length; `1` the plaquette step; `2 * j + 1` the index of the even-extent family;
`3` the least cell count (`3n ≤ 2j + 2`). -/
theorem psiL_ov_le{j : ℕ} (hn : 1 ≤ n) (hL : 3 * n ≤ 2 * j + 1 + 1) (τ : Fin 4) (a0 : ℤ) (R : ℕ)
    {K : Fin 4 → Fin (qO n (2 * j + 1 + 1))} {l l'' l' : WilsonHypercubic.Link 4 (2 * j + 1 + 1)}
    (hl : l ∈ ovBox n (2 * j + 1) K) (hl'' : l'' ∈ ovBox n (2 * j + 1) K)
    (hl' : l'' = l' ∨ SharePlaq (bdT (2 * j + 1)) l'' l') :
    psiL j τ a0 R l' ≤ psiL j τ a0 R l + 5 * n := by
  have hw := psi_pair hn hL
    (fun s => psiT R (2 * j + 1) ((s - InfiniteLattice.finMod (2 * j + 1) a0 : Fin (2 * j + 1 + 1)) : ℕ))
    (fun s => psiT_step R (2 * j + 1) _ s) (K τ).isLt ((mem_ovBox.mp hl) τ) ((mem_ovBox.mp hl'') τ)
  have hstep : psiL j τ a0 R l' ≤ psiL j τ a0 R l'' + 1 := by
    rcases hl' with e | hs
    · rw [e]; omega
    · exact psiL_lip j τ a0 R l' l'' ((mem_nbT j l' l'').mpr (Or.inr (by
        obtain ⟨p, h1, h2⟩ := hs
        exact ⟨p, h2, h1⟩)))
  have : psiL j τ a0 R l'' + 1 ≤ psiL j τ a0 R l + 5 * n := hw
  omega

#print axioms psiL_ov_le

end MassGap.OverlapGeometry
