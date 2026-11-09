import Mathlib
import MassGap.HeatBathLocal

noncomputable section

/-!
# MassGap.TileGeometry — a 16-colour tiling of every periodic lattice by boxes of side `n` to `3n − 1`

The block sweep needs boxes in colour classes whose members share no plaquette, at every torus extent
(`HeatBathGapDecay.TorusClusterAt` asks for all large extents, not a subsequence). Each direction of the
circle of length `L ≥ 2n` is cut into `q = 2⌊L/2n⌋` cells (an even number): cell `k < q − 1` is
`[kn, kn + n)`, the last cell takes the rest, `[(q − 1)n, L)`, of length `n` to `3n − 1`. A box is a product
of four cells; its colour is the parity of its four cell indices.

## What it gives

1. **Cells** (`qT`, `cell`): `two_le_qT`, `qT_even`, `cell_lt`, `cell_window` (`cell·n ≤ x < cell·n + 3n`),
   `cell_succ` (a unit step moves the cell by `0` or `+1` cyclically).
2. **Neighbouring links** (`CellRel`): links sharing a plaquette have cell indices equal or cyclically
   adjacent in every direction (`cellRel_of_sharePlaq`); with equal parities, equal
   (`eq_of_cellRel_parity`, the cell count being even).
3. **Boxes** (`tileBox`, `tcol`): distinct boxes are disjoint (`tileBox_disjoint`); distinct boxes of one
   colour share no plaquette (`not_sharePlaq_of_col`); every box shares a plaquette with at most `80` others
   (`card_adj_le`, `3⁴ − 1`).
4. **The potential across a box** (`psi_window`): a potential moving by at most one per cyclic unit step
   moves by at most `3n − 1` inside one cell; with the plaquette step (`HeatBathLocal.psiL_lip`),
   `psiL` rises by at most `3n` from a box to any link sharing a plaquette with it (`psiL_nb_le`).

DERIVED (module-wide): `4` the spacetime dimension; `2` the colour count per direction (parity) and the
factor making the cell count even; `3` the bound on the last cell's length in units of `n` and the
three cyclic offsets `0, +1, −1`; `80 = 3⁴ − 1`; `1` the unit step and the successor writing the extent.
-/

namespace MassGap.TileGeometry

open MassGap MassGap.HeatBath MassGap.KnabeCriterion MassGap.HeatBathLocal

/-! ## 1. Cells of a circle -/

/-- **The number of cells** on a circle of length `L` at side `n`: `2⌊L/2n⌋`, even.

DERIVED: `2`. -/
def qT (n L : ℕ) : ℕ := 2 * (L / (2 * n))

/-- **The cell of a coordinate** `x ∈ [0, L)`: `min(⌊x/n⌋, q − 1)`.

DERIVED: `1` the last index. -/
def cell (n L x : ℕ) : ℕ := min (x / n) (qT n L - 1)

/-- DERIVED: `2` the least cell count; `1` the least side. -/
theorem two_le_qT {n L : ℕ} (hn : 1 ≤ n) (hL : 2 * n ≤ L) : 2 ≤ qT n L := by
  have : 1 ≤ L / (2 * n) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  unfold qT
  generalize L / (2 * n) = a at *
  omega

#print axioms two_le_qT

/-- DERIVED: `2` the parity. -/
theorem qT_even (n L : ℕ) : qT n L % 2 = 0 := Nat.mul_mod_right 2 _

#print axioms qT_even

/-- `q n ≤ L`.

DERIVED: no numeral. -/
theorem qT_mul_le (n L : ℕ) : qT n L * n ≤ L := by
  unfold qT
  have h := Nat.div_mul_le_self L (2 * n)
  calc 2 * (L / (2 * n)) * n = L / (2 * n) * (2 * n) := by ring
    _ ≤ L := h

#print axioms qT_mul_le

/-- `L < (q + 2) n`.

DERIVED: `2` the cell count's factor. -/
theorem lt_qT_add (n L : ℕ) (hn : 1 ≤ n) : L < (qT n L + 2) * n := by
  unfold qT
  have h1 := Nat.div_add_mod L (2 * n)
  have h2 := Nat.mod_lt L (show 0 < 2 * n by omega)
  nlinarith

#print axioms lt_qT_add

/-- DERIVED: `1` the last index. -/
theorem cell_lt {n L : ℕ} (hn : 1 ≤ n) (hL : 2 * n ≤ L) (x : ℕ) : cell n L x < qT n L := by
  have := two_le_qT hn hL
  have := min_le_right (x / n) (qT n L - 1)
  unfold cell
  omega

#print axioms cell_lt

/-- **The cell's window**: `cell·n ≤ x < cell·n + 3n` for `x < L`.

DERIVED: `3` the last cell's length bound. -/
theorem cell_window {n L : ℕ} (hn : 1 ≤ n) (hL : 2 * n ≤ L) {x : ℕ} (hx : x < L) :
    cell n L x * n ≤ x ∧ x < cell n L x * n + 3 * n := by
  have hq := two_le_qT hn hL
  have hlt := lt_qT_add n L hn
  have h1 := Nat.mul_div_le x n
  have h2 := Nat.lt_mul_div_succ x (show 0 < n by omega)
  obtain ⟨q', hq'⟩ : ∃ q', qT n L = q' + 2 := ⟨qT n L - 2, by omega⟩
  rw [hq'] at hlt
  unfold cell
  rw [hq', show q' + 2 - 1 = q' + 1 by omega]
  rcases le_total (x / n) (q' + 1) with h | h
  · rw [min_eq_left h]
    constructor <;> nlinarith
  · rw [min_eq_right h]
    have h3 : (q' + 1) * n ≤ x / n * n := Nat.mul_le_mul_right n h
    constructor <;> nlinarith

#print axioms cell_window

/-- **One step moves the cell by `0` or `+1`**: the cell of `x + 1` is the cell of `x` or the next one
(cyclically). The bound `x + 1 < L` is not used: past the last cell start the cap keeps the cell at `q − 1`. The
wrap from `L − 1` to `0` is `cell_last` with `cell_zero`.

DERIVED: `1` the step; `0` the first cell. -/
theorem cell_succ {n L : ℕ} (hn : 1 ≤ n) (hL : 2 * n ≤ L) {x : ℕ} (_hx : x + 1 < L) :
    cell n L (x + 1) = cell n L x ∨ cell n L (x + 1) = (cell n L x + 1) % qT n L := by
  have hq := two_le_qT hn hL
  have hs := Nat.succ_div (a := x) (b := n)
  have hmono : x / n ≤ (x + 1) / n := Nat.div_le_div_right (by omega)
  obtain ⟨q', hq'⟩ : ∃ q', qT n L = q' + 2 := ⟨qT n L - 2, by omega⟩
  unfold cell
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

#print axioms cell_succ

/-- At the end of the circle: the last coordinate is in the last cell.

DERIVED: `1` the last coordinate and the last index. -/
theorem cell_last {n L : ℕ} (hn : 1 ≤ n) (hL : 2 * n ≤ L) : cell n L (L - 1) = qT n L - 1 := by
  have hq := two_le_qT hn hL
  have hle := qT_mul_le n L
  unfold cell
  apply min_eq_right
  rw [Nat.le_div_iff_mul_le (by omega)]
  obtain ⟨q', hq'⟩ : ∃ q', qT n L = q' + 2 := ⟨qT n L - 2, by omega⟩
  rw [hq'] at hle ⊢
  rw [show q' + 2 - 1 = q' + 1 by omega]
  have : (q' + 1) * n + 1 ≤ L := by nlinarith
  omega

#print axioms cell_last

/-- DERIVED: `0` the first cell. -/
theorem cell_zero (n L : ℕ) : cell n L 0 = 0 := by
  unfold cell
  simp

#print axioms cell_zero

/-! ## 2. Cyclic adjacency of cells -/

/-- **Cells equal or cyclically adjacent.**

DERIVED: `1` the step. -/
def CellRel (q a b : ℕ) : Prop := b = a ∨ b = (a + 1) % q ∨ a = (b + 1) % q

/-- A cyclic unit step of torus coordinates keeps the cells related.

DERIVED: `1` the step and the successor writing the extent. -/
theorem cellRel_step {n M : ℕ} (hn : 1 ≤ n) (hL : 2 * n ≤ M + 1) (s : Fin (M + 1)) :
    CellRel (qT n (M + 1)) (cell n (M + 1) s) (cell n (M + 1) ((s + 1 : Fin (M + 1)) : ℕ)) := by
  rcases val_add_one_cases s with h | ⟨hsM, h0⟩
  · rw [h]
    have hx : (s : ℕ) + 1 < M + 1 := by
      have := ((s + 1 : Fin (M + 1))).isLt
      omega
    rcases cell_succ hn hL hx with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rw [h0, cell_zero, hsM]
    have hl := cell_last hn hL
    rw [show M + 1 - 1 = M by omega] at hl
    rw [hl]
    have hq := two_le_qT hn hL
    right; left
    rw [show qT n (M + 1) - 1 + 1 = qT n (M + 1) by omega, Nat.mod_self]

#print axioms cellRel_step

/-- `CellRel` is symmetric.

DERIVED: no numeral. -/
theorem CellRel.symm {q a b : ℕ} (h : CellRel q a b) : CellRel q b a := by
  rcases h with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

#print axioms CellRel.symm

/-- **Links sharing a plaquette have related cells in every direction** (`BoxPatch.sharePlaq_disp`).

DERIVED: `0`, `1`, `−1` the coordinate steps. -/
theorem cellRel_of_sharePlaq {n M : ℕ} (hn : 1 ≤ n) (hL : 2 * n ≤ M + 1)
    {l l' : WilsonHypercubic.Link 4 (M + 1)} (h : SharePlaq (bdT M) l l') (μ : Fin 4) :
    CellRel (qT n (M + 1)) (cell n (M + 1) (l.2 μ)) (cell n (M + 1) (l'.2 μ)) := by
  obtain ⟨_, _, _, hd⟩ := BoxPatch.sharePlaq_disp h
  have hdμ := hd μ
  simp only [Pi.sub_apply] at hdμ
  rcases hdμ with h0 | h1 | h2
  · rw [sub_eq_zero.mp h0]
    exact Or.inl rfl
  · have e : l'.2 μ = l.2 μ + 1 := by rw [← h1]; abel
    rw [e]
    exact cellRel_step hn hL (l.2 μ)
  · have e : l.2 μ = l'.2 μ + 1 := by
      have : l'.2 μ = -1 + l.2 μ := sub_eq_iff_eq_add.mp h2
      rw [this]; abel
    rw [e]
    exact (cellRel_step hn hL (l'.2 μ)).symm

#print axioms cellRel_of_sharePlaq

/-- **Related cells of equal parity are equal** (the cell count is even).

DERIVED: `2` the parity; `1` the step. -/
theorem eq_of_cellRel_parity {q a b : ℕ} (hq : q % 2 = 0) (ha : a < q) (hb : b < q)
    (h : CellRel q a b) (hp : a % 2 = b % 2) : a = b := by
  rcases h with h | h | h
  · exact h.symm
  · rcases Nat.lt_or_ge (a + 1) q with h' | h'
    · rw [Nat.mod_eq_of_lt h'] at h
      omega
    · have e : a + 1 = q := by omega
      rw [e, Nat.mod_self] at h
      omega
  · rcases Nat.lt_or_ge (b + 1) q with h' | h'
    · rw [Nat.mod_eq_of_lt h'] at h
      omega
    · have e : b + 1 = q := by omega
      rw [e, Nat.mod_self] at h
      omega

#print axioms eq_of_cellRel_parity

/-- **The three cyclic offsets** `0`, `+1`, `−1` of a cell.

DERIVED: `0`, `1`, `2` the three offsets' labels; `1` the step; `3` the offsets `0`, `+1`, `−1` of a
nearest-neighbour cyclic step (`CellRel`). -/
def shiftCell (q a : ℕ) (e : Fin 3) : ℕ :=
  if e = 0 then a else if e = 1 then (a + 1) % q else (a + q - 1) % q

/-- DERIVED: `3` the offsets of `shiftCell`. -/
theorem shiftCell_lt {q a : ℕ} (ha : a < q) (e : Fin 3) : shiftCell q a e < q := by
  unfold shiftCell
  split_ifs
  · exact ha
  · exact Nat.mod_lt _ (by omega)
  · exact Nat.mod_lt _ (by omega)

#print axioms shiftCell_lt

/-- A related cell is one of the three offsets.

DERIVED: `0`, `1`, `2` the offsets' labels; `1` the step; `3` the offsets of `shiftCell`. -/
theorem exists_shiftCell {q a b : ℕ} (ha : a < q) (hb : b < q) (h : CellRel q a b) :
    ∃ e : Fin 3, b = shiftCell q a e := by
  rcases h with h | h | h
  · exact ⟨0, by simp [shiftCell, h]⟩
  · exact ⟨1, by simp [shiftCell, h]⟩
  · refine ⟨2, ?_⟩
    simp only [shiftCell, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, if_false]
    rcases Nat.lt_or_ge (b + 1) q with h' | h'
    · rw [Nat.mod_eq_of_lt h'] at h
      rw [h, show b + 1 + q - 1 = b + q by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hb]
    · have e : b + 1 = q := by omega
      rw [e, Nat.mod_self] at h
      rw [h, show 0 + q - 1 = q - 1 by omega, Nat.mod_eq_of_lt (by omega)]
      omega

#print axioms exists_shiftCell

/-! ## 3. Boxes and colours -/

variable {n M : ℕ}

/-- **The box** with cell indices `K`: the links whose base site lies in cell `K μ` in every direction.

DERIVED: `4` the dimension; `1` the successor writing the extent. -/
def tileBox (n M : ℕ) (K : Fin 4 → Fin (qT n (M + 1))) : Finset (WilsonHypercubic.Link 4 (M + 1)) :=
  Finset.univ.filter (fun l => ∀ μ, cell n (M + 1) (l.2 μ) = (K μ : ℕ))

/-- DERIVED: no numeral. -/
theorem mem_tileBox {K : Fin 4 → Fin (qT n (M + 1))} {l : WilsonHypercubic.Link 4 (M + 1)} :
    l ∈ tileBox n M K ↔ ∀ μ, cell n (M + 1) (l.2 μ) = (K μ : ℕ) := by
  unfold tileBox
  simp

#print axioms mem_tileBox

/-- **The colour of a box**: the parities of its cell indices.

DERIVED: `2` the parity. -/
def tcol (K : Fin 4 → Fin (qT n (M + 1))) : Fin 4 → Fin 2 :=
  fun μ => ⟨(K μ : ℕ) % 2, Nat.mod_lt _ (by norm_num)⟩

/-- **Distinct boxes are disjoint.**

DERIVED: no numeral. -/
theorem tileBox_disjoint {K K' : Fin 4 → Fin (qT n (M + 1))} (h : K ≠ K') :
    Disjoint (tileBox n M K) (tileBox n M K') := by
  rw [Finset.disjoint_left]
  intro l hl hl'
  apply h
  funext μ
  apply Fin.ext
  rw [← (mem_tileBox.mp hl) μ, ← (mem_tileBox.mp hl') μ]

#print axioms tileBox_disjoint

/-- **Boxes touching through a plaquette have related cells.**

DERIVED: no numeral. -/
theorem cellRel_of_touch (hn : 1 ≤ n) (hL : 2 * n ≤ M + 1) {K K' : Fin 4 → Fin (qT n (M + 1))}
    {l l' : WilsonHypercubic.Link 4 (M + 1)} (hl : l ∈ tileBox n M K) (hl' : l' ∈ tileBox n M K')
    (h : SharePlaq (bdT M) l l') (μ : Fin 4) : CellRel (qT n (M + 1)) (K μ) (K' μ) := by
  have e := cellRel_of_sharePlaq hn hL h μ
  rwa [(mem_tileBox.mp hl) μ, (mem_tileBox.mp hl') μ] at e

#print axioms cellRel_of_touch

/-- **Distinct boxes of one colour share no plaquette.**

DERIVED: `2` the parity. -/
theorem not_sharePlaq_of_col (hn : 1 ≤ n) (hL : 2 * n ≤ M + 1) {K K' : Fin 4 → Fin (qT n (M + 1))}
    (hne : K ≠ K') (hc : tcol K = tcol K') {l l' : WilsonHypercubic.Link 4 (M + 1)}
    (hl : l ∈ tileBox n M K) (hl' : l' ∈ tileBox n M K') : ¬ SharePlaq (bdT M) l l' := by
  intro h
  apply hne
  funext μ
  apply Fin.ext
  have hp : (K μ : ℕ) % 2 = (K' μ : ℕ) % 2 := congrArg Fin.val (congrFun hc μ)
  exact eq_of_cellRel_parity (qT_even n (M + 1)) (K μ).isLt (K' μ).isLt
    (cellRel_of_touch hn hL hl hl' h μ) hp

#print axioms not_sharePlaq_of_col

/-- **Adjacent boxes**: distinct, with a link of one sharing a plaquette with a link of the other.

DERIVED: no numeral. -/
def TAdj (n M : ℕ) (K K' : Fin 4 → Fin (qT n (M + 1))) : Prop :=
  K' ≠ K ∧ ∃ l ∈ tileBox n M K, ∃ l' ∈ tileBox n M K', SharePlaq (bdT M) l l'

instance (K : Fin 4 → Fin (qT n (M + 1))) : DecidablePred (TAdj n M K) := by
  classical
  exact fun _ => inferInstance

/-- Adjacency is symmetric.

DERIVED: no numeral. -/
theorem tadj_symm {K K' : Fin 4 → Fin (qT n (M + 1))} (h : TAdj n M K K') : TAdj n M K' K := by
  obtain ⟨hne, l, hl, l', hl', p, h1, h2⟩ := h
  exact ⟨fun e => hne e.symm, l', hl', l, hl, p, h2, h1⟩

#print axioms tadj_symm

/-- **Each box is adjacent to at most `80` others** (`3⁴ − 1`).

DERIVED: `80 = 3⁴ − 1`; `3` the offsets; `4` the dimension. -/
theorem card_adj_le (hn : 1 ≤ n) (hL : 2 * n ≤ M + 1) (K : Fin 4 → Fin (qT n (M + 1))) :
    (Finset.univ.filter (TAdj n M K)).card ≤ 80 := by
  classical
  let f : (Fin 4 → Fin 3) → (Fin 4 → Fin (qT n (M + 1))) :=
    fun e μ => ⟨shiftCell (qT n (M + 1)) (K μ) (e μ), shiftCell_lt (K μ).isLt (e μ)⟩
  have hK : K ∈ Finset.univ.image f := by
    refine Finset.mem_image.mpr ⟨fun _ => 0, Finset.mem_univ _, ?_⟩
    funext μ
    apply Fin.ext
    simp [f, shiftCell]
  have hsub : Finset.univ.filter (TAdj n M K) ⊆ (Finset.univ.image f).erase K := by
    intro K' hK'
    obtain ⟨hne, l, hl, l', hl', hs⟩ := (Finset.mem_filter.mp hK').2
    refine Finset.mem_erase.mpr ⟨hne, Finset.mem_image.mpr ?_⟩
    have hex : ∀ μ, ∃ e : Fin 3, (K' μ : ℕ) = shiftCell (qT n (M + 1)) (K μ) e := fun μ =>
      exists_shiftCell (K μ).isLt (K' μ).isLt (cellRel_of_touch hn hL hl hl' hs μ)
    choose e he using hex
    refine ⟨e, Finset.mem_univ _, ?_⟩
    funext μ
    apply Fin.ext
    exact (he μ).symm
  have h81 : (Finset.univ.image f).card ≤ 81 := by
    refine (Finset.card_image_le).trans ?_
    simp
  calc (Finset.univ.filter (TAdj n M K)).card ≤ ((Finset.univ.image f).erase K).card :=
        Finset.card_le_card hsub
    _ = (Finset.univ.image f).card - 1 := Finset.card_erase_of_mem hK
    _ ≤ 80 := by omega

#print axioms card_adj_le

/-- The column count: at most `80` boxes are adjacent to a given one, in the second argument.

DERIVED: `80`. -/
theorem card_adj_le' (hn : 1 ≤ n) (hL : 2 * n ≤ M + 1) (K' : Fin 4 → Fin (qT n (M + 1))) :
    (Finset.univ.filter (fun K => TAdj n M K K')).card ≤ 80 := by
  classical
  have e : Finset.univ.filter (fun K => TAdj n M K K') = Finset.univ.filter (TAdj n M K') := by
    ext K
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨tadj_symm, tadj_symm⟩
  rw [e]
  exact card_adj_le hn hL K'

#print axioms card_adj_le'

/-! ## 4. The potential across a box -/

/-- **A potential moving by at most one per cyclic unit step moves by at most the distance along a
non-wrapping path.**

DERIVED: `1` the unit step. -/
theorem path_le {L : ℕ} [NeZero L] (φ : Fin L → ℕ)
    (hφ : ∀ s : Fin L, (s : ℕ) + 1 < L → φ (s + 1) ≤ φ s + 1 ∧ φ s ≤ φ (s + 1) + 1) :
    ∀ d : ℕ, ∀ x y : Fin L, (y : ℕ) = x + d → φ y ≤ φ x + d ∧ φ x ≤ φ y + d := by
  intro d
  induction d with
  | zero =>
    intro x y h
    have : y = x := Fin.ext (by omega)
    subst this
    omega
  | succ d ih =>
    intro x y h
    have hy := y.isLt
    let y' : Fin L := ⟨(x : ℕ) + d, by omega⟩
    have h1 := ih x y' rfl
    have hy'1 : y' + 1 = y := by
      apply Fin.ext
      rw [Fin.val_add_one_of_lt' (by simp only [y']; omega)]
      simp only [y']
      omega
    have h2 := hφ y' (by simp only [y']; omega)
    rw [hy'1] at h2
    omega

#print axioms path_le

/-- **Inside one cell a step-Lipschitz potential moves by less than `3n`.**

DERIVED: `3` the cell length bound; `1` the step. -/
theorem psi_window (hn : 1 ≤ n) (hL : 2 * n ≤ M + 1) (φ : Fin (M + 1) → ℕ)
    (hφ : ∀ s : Fin (M + 1), (s : ℕ) + 1 < M + 1 → φ (s + 1) ≤ φ s + 1 ∧ φ s ≤ φ (s + 1) + 1)
    {x y : Fin (M + 1)} (h : cell n (M + 1) x = cell n (M + 1) y) : φ y + 1 ≤ φ x + 3 * n := by
  have wx := cell_window hn hL x.isLt
  have wy := cell_window hn hL y.isLt
  rw [h] at wx
  rcases le_total (x : ℕ) y with hxy | hxy
  · have := (path_le φ hφ ((y : ℕ) - x) x y (by omega)).1
    omega
  · have := (path_le φ hφ ((x : ℕ) - y) y x (by omega)).2
    omega

#print axioms psi_window

/-- The cyclic step bound of the offset potential behind `HeatBathLocal.psiL`.

DERIVED: `1` the step. -/
theorem psiT_step (R M : ℕ) (c0 : Fin (M + 1)) (s : Fin (M + 1)) :
    psiT R M ((s + 1 - c0 : Fin (M + 1)) : ℕ) ≤ psiT R M ((s - c0 : Fin (M + 1)) : ℕ) + 1 ∧
      psiT R M ((s - c0 : Fin (M + 1)) : ℕ) ≤ psiT R M ((s + 1 - c0 : Fin (M + 1)) : ℕ) + 1 := by
  have e : s + 1 - c0 = (s - c0) + 1 := add_sub_right_comm s 1 c0
  rw [e]
  have hb := (s - c0).isLt
  have hb' := ((s - c0) + 1).isLt
  have h := psiT_lip (R := R) (by omega) (by omega) (val_add_one_cases (s - c0))
  exact ⟨h.2, h.1⟩

#print axioms psiT_step

/-- **`psiL` rises by at most `3n` from a box to a link sharing a plaquette with it.**

DERIVED: `3` the cell length bound; `1` the plaquette step; `2 * j + 1` the index of the even-extent
family. -/
theorem psiL_nb_le {j : ℕ} (hn : 1 ≤ n) (hL : 2 * n ≤ 2 * j + 1 + 1) (τ : Fin 4) (a0 : ℤ) (R : ℕ)
    {K : Fin 4 → Fin (qT n (2 * j + 1 + 1))} {l l'' l' : WilsonHypercubic.Link 4 (2 * j + 1 + 1)}
    (hl : l ∈ tileBox n (2 * j + 1) K) (hl'' : l'' ∈ tileBox n (2 * j + 1) K)
    (hl' : l'' = l' ∨ SharePlaq (bdT (2 * j + 1)) l'' l') :
    psiL j τ a0 R l' ≤ psiL j τ a0 R l + 3 * n := by
  have hc : cell n (2 * j + 1 + 1) (l.2 τ) = cell n (2 * j + 1 + 1) (l''.2 τ) := by
    rw [(mem_tileBox.mp hl) τ, (mem_tileBox.mp hl'') τ]
  have hw := psi_window hn hL
    (fun s => psiT R (2 * j + 1) ((s - InfiniteLattice.finMod (2 * j + 1) a0 : Fin (2 * j + 1 + 1)) : ℕ))
    (fun s _ => psiT_step R (2 * j + 1) _ s) hc
  have hstep : psiL j τ a0 R l' ≤ psiL j τ a0 R l'' + 1 := by
    rcases hl' with e | hs
    · rw [e]; omega
    · exact psiL_lip j τ a0 R l' l'' ((mem_nbT j l' l'').mpr (Or.inr (by
        obtain ⟨p, h1, h2⟩ := hs
        exact ⟨p, h2, h1⟩)))
  have : psiL j τ a0 R l'' + 1 ≤ psiL j τ a0 R l + 3 * n := hw
  omega

#print axioms psiL_nb_le

end MassGap.TileGeometry
