import Mathlib
import MassGap.MixEqui

/-!
# MassGap.MixExpand — the expansion in the mixed coupling around the decoupled planes

At `t = β_⊥ = 0` the weight `e^{−β S_in}` reads only the two families of planes, `(0,1)` and `(2,3)`. This module
computes the first nontrivial term of the expansion of the mixed variance in `t` there, and names what an expansion
to all orders would need. Declarations are in `MassGap.MixExpand`.

## 1. The third cumulant at the decoupled end (proved)

`∂_t Var_n(S_mix) = −κ₃_n(S_mix)` at every `t` (`hasDerivAt_varMix`), with
`κ₃ = ⟨S³⟩ − 3 ⟨S⟩⟨S²⟩ + 2 ⟨S⟩³` (`cum3`). At `t = 0`, on an even extent `n ≥ 3`:

  `κ₃_n(S_mix)(β, 0) = 32 n⁴ κ₃^Haar(φ)`  (`cum3_zero`),

with `κ₃^Haar(φ) = ∫ (φ − ⟨φ⟩)³ dHaar` (`haarCum3`). The centred mixed action is `Σ_q X_q`, `X_q = φ_q − ⟨φ⟩_Haar` over
the `8 n⁴` ordered mixed plaquettes, and `∫ X_a X_b X_c e^{−β S_in}` is `κ₃^Haar Z` when `a, b, c` are one plaquette up
to orientation and `0` otherwise (`integral_term`). Each ordered plaquette has two partners (itself and its reverse,
`tw_sum`), so the triple sum is `8 n⁴ · 2 · 2 · κ₃^Haar` (`triple_sum`).

The vanishing off the diagonal is a private-corner argument. The layer rotation `MixCut.gT` at one site `z` moves the
holonomy of every mixed plaquette cornered at `z` (four corner reads: the base, `psiI`, `psiJ`, and `psiK` at
`y + i + j`) and fixes every other plaquette and `S_in`. So if `z` is a corner of `p` and of neither of the two other
plaquettes, `∫ X_p G e^{−β S_in} = 0` (`cent_factor`). The corners of a normal mixed plaquette are a product of an edge
of the `(0,1)` torus and an edge of the `(2,3)` torus (`corner_iff`); on an even extent each edge has one endpoint of
each parity (`col_shiftA`, `col_shiftB`), so the corners are indexed by a pair of parities, `(aD i y s, bD j y t)`.
Two different normal plaquettes have different edge data (`data_inj`, extent `≥ 3`), and a pure covering argument
(`cover_pair`) gives: of two different plaquettes in a triple, one has a corner that neither other plaquette has
(`exists_private`). Extent `3` is excluded: three plaquettes stacked around a cycle of length `3` cover each other's
corners.

`hasDerivAt_varGap_zero`: for windows `w ≥ 2`, `∂_t (16 Var_n − Var_{2n}) = 0` at `t = 0`, from
`16 · 32 n⁴ − 32 (2n)⁴ = 0`.

## 2. The cumulants as derivatives of `log Z` (stated; `k = 2, 3` proved)

`kappa N β k n = (−1)^k ∂_t^k log Z_n(β, t)|_{t=0}`, the order-`k` cumulant of `S_mix` at `t = 0`.
`LocalCumulant N β k`: some constant `c` and window `w₀` with `kappa k (2^w) = c (2^w)⁴` for every `w ≥ w₀`.
Proved: `localCumulant_two` (`c = 16 Var_Haar(φ)`, from `MixEqui.varMix_zero`) and `localCumulant_three`
(`c = 32 κ₃^Haar(φ)`). The general pattern, `AllLocalCumulants N β := ∀ k, LocalCumulant N β k`, is a named input,
not proved here: an order-`k` cumulant at `t = 0` sees only connected clusters of at most `k` mixed plaquettes, of
bounded diameter, and once the extent exceeds that diameter the count of clusters is `n⁴` times a constant.

## 3. The doubling combination and the radius (the radius is a named input)

`kappa_doubling`: `LocalCumulant N β k` gives `16 κ_k(n) − κ_k(2n) = 0` past its window. This is a statement about
Taylor coefficients at `t = 0`: a formal-power-series statement. A bound on `[0, t₁]` needs a radius of convergence
that does not shrink with the window. `WindowUniformRadius N β t₁`: constants `C`, `ρ > t₁` and, for every window
`w ≥ 1`, coefficients `a_k(w)` with `|a_k(w)| ≤ C ρ^{−k}` whose power series sums to `16 Var_n(t) − Var_{2n}(t)` on
`[0, t₁]`. `varGapOn_of_radius` proves `VarGapOn N β t₁` from it, with `K = C (1 − t₁/ρ)⁻¹`, and
`varGap_of_radius` gives `MixCutTest.VarGap N β` at `t₁ = β`. The bound uses the radius alone; the vanishing of the
low coefficients does not enter it.

DERIVED (module-wide): `3` the cube and the least extent on which two steps move; `2` the parity, the square, the
two orientations of one plaquette and the doubling; `32 = 8 · 2 · 2` the mixed ordered orientations per site times
the two partners of each of the two other factors; `16 = 2⁴` the copies; `4` the dimension and the exponent of `n`;
`8` the mixed ordered orientations per site (`MixCut.sum_mixed`); `1` the least window and the geometric ratio bound;
`0` the decoupled end and the axis; `−1` the sign of `∂_t` on `e^{−t S}`. Inherited: none beyond `MixEqui`, `MixCut`,
`MixCutTest`.

## What does not follow

Nothing here bounds `16 Var_n − Var_{2n}` at any `t > 0`. `cum3_zero` and `hasDerivAt_varGap_zero` are statements at
the single point `t = 0`, on even extents `n ≥ 4` in the windows (`w ≥ 2`). `AllLocalCumulants N β` is not proved
for `k ≥ 4`, and even all of it would give only the formal power series of the defect at `t = 0`: the window
threshold `w_k` may grow with `k`, so no fixed window has every coefficient vanishing. `WindowUniformRadius N β t₁`
is not proved for any `t₁ > 0`: it is a window-uniform convergent cluster expansion in `t` around the decoupled
planes, and it is the whole content of `VarGapOn` there. `varGap_of_radius` therefore restates `MixCutTest.VarGap`
as `WindowUniformRadius N β β`; it does not discharge it. `MixCutTest.VarGap`, `MixCut.MixCutBound`,
`MixEqui.MixEquiUp` and `MixPlane.NoStallOnSegment` stay open at every `β > 0`. Nothing in this module cites
`LayerSplit.TwoDCharacter`; the decoupled-end vanishing it supplied is proved in `TwoDVanish`.
-/

namespace MassGap.MixExpand

open MeasureTheory Filter Topology Set MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.MixCut
  MassGap.MixEqui

variable {N : ℕ}

/-! ## 1. Edge data of a mixed plaquette -/

/-- Sites of the side-`n` torus. No numeral. -/
abbrev St (n : ℕ) : Type := RSite (fun _ : Fin 4 => n)

/-- The `(0,1)` part of a site. DERIVED: `0`, `1` the first block. -/
def apart {n : ℕ} (c : St n) : Fin n × Fin n := (c 0, c 1)

/-- The `(2,3)` part of a site. DERIVED: `2`, `3` the second block. -/
def bpart {n : ℕ} (c : St n) : Fin n × Fin n := (c 2, c 3)

/-- The parity of a point of a two-dimensional torus. DERIVED: `2` the parity; `0` the even class. -/
def colr {n : ℕ} (u : Fin n × Fin n) : Bool := decide ((u.1.val + u.2.val) % 2 = 0)

/-- The site with given parts. DERIVED: `4` the dimension. -/
def mkS {n : ℕ} (u v : Fin n × Fin n) : St n := ![u.1, u.2, v.1, v.2]

theorem apart_mkS {n : ℕ} (u v : Fin n × Fin n) : apart (mkS u v) = u := by
  simp [apart, mkS]

theorem bpart_mkS {n : ℕ} (u v : Fin n × Fin n) : bpart (mkS u v) = v := by
  simp [bpart, mkS]

/-- DERIVED: `2`, `0`, `1` the first block. -/
theorem blockA : ∀ i : Fin 4, i.val / 2 = 0 → i = 0 ∨ i = 1 := by decide

/-- DERIVED: `2`, `0`, `3` the second block. -/
theorem blockB : ∀ j : Fin 4, ¬ j.val / 2 = 0 → j = 2 ∨ j = 3 := by decide

theorem bool_ne : ∀ b : Bool, b ≠ !b := by decide

theorem bool_of_ne : ∀ a b : Bool, ¬ a = b → a = !b := by decide

/-- A site is fixed by its two parts. DERIVED: `4` the coordinates. -/
theorem site_ext {n : ℕ} {c c' : St n} (ha : apart c = apart c') (hb : bpart c = bpart c') : c = c' := by
  simp only [apart, bpart, Prod.mk.injEq] at ha hb
  funext k
  have hk : ∀ k : Fin 4, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by decide
  rcases hk k with rfl | rfl | rfl | rfl
  exacts [ha.1, ha.2, hb.1, hb.2]

theorem pA {n : ℕ} {i : Fin 4} (hi : i.val / 2 = 0) (c c' : St n) (h : apart c = apart c') : c i = c' i := by
  simp only [apart, Prod.mk.injEq] at h
  rcases blockA i hi with rfl | rfl
  · exact h.1
  · exact h.2

theorem pB {n : ℕ} {j : Fin 4} (hj : ¬ j.val / 2 = 0) (c c' : St n) (h : bpart c = bpart c') : c j = c' j := by
  simp only [bpart, Prod.mk.injEq] at h
  rcases blockB j hj with rfl | rfl
  · exact h.1
  · exact h.2

/-- A step in the second block leaves the first part. No numeral. -/
theorem apart_shiftB {n : ℕ} {j : Fin 4} (hj : ¬ j.val / 2 = 0) (c : St n) :
    apart (rshift (fun _ => n) j c) = apart c := by
  rcases blockB j hj with rfl | rfl <;> simp [apart, rshift_apply]

/-- A step in the first block leaves the second part. No numeral. -/
theorem bpart_shiftA {n : ℕ} {i : Fin 4} (hi : i.val / 2 = 0) (c : St n) :
    bpart (rshift (fun _ => n) i c) = bpart c := by
  rcases blockA i hi with rfl | rfl <;> simp [bpart, rshift_apply]

/-- **One step flips the parity of a coordinate** on an even extent. DERIVED: `2` the parity and the least
extent; `1` the odd class. -/
theorem rot_val {n : ℕ} (he : n % 2 = 0) (hn : 2 ≤ n) (a : Fin n) : ((finRotate n a).val + a.val) % 2 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [finRotate_succ_apply]
  have e := Fin.val_add_one a
  split_ifs at e with c
  · simp only [Fin.ext_iff, Fin.val_last] at c
    rw [e]; omega
  · rw [e]; omega

theorem colr_rot_left {n : ℕ} (he : n % 2 = 0) (hn : 2 ≤ n) (a b : Fin n) :
    colr (finRotate n a, b) = !colr (a, b) := by
  have h := rot_val he hn a
  unfold colr
  show decide (((finRotate n a).val + b.val) % 2 = 0) = !decide ((a.val + b.val) % 2 = 0)
  by_cases h2 : (a.val + b.val) % 2 = 0
  · have h3 : ¬ ((finRotate n a).val + b.val) % 2 = 0 := by omega
    rw [decide_eq_false h3, decide_eq_true h2]; rfl
  · have h3 : ((finRotate n a).val + b.val) % 2 = 0 := by omega
    rw [decide_eq_true h3, decide_eq_false h2]; rfl

theorem colr_rot_right {n : ℕ} (he : n % 2 = 0) (hn : 2 ≤ n) (a b : Fin n) :
    colr (a, finRotate n b) = !colr (a, b) := by
  have h := rot_val he hn b
  unfold colr
  show decide ((a.val + (finRotate n b).val) % 2 = 0) = !decide ((a.val + b.val) % 2 = 0)
  by_cases h2 : (a.val + b.val) % 2 = 0
  · have h3 : ¬ (a.val + (finRotate n b).val) % 2 = 0 := by omega
    rw [decide_eq_false h3, decide_eq_true h2]; rfl
  · have h3 : (a.val + (finRotate n b).val) % 2 = 0 := by omega
    rw [decide_eq_true h3, decide_eq_false h2]; rfl

/-- **A first-block step flips the first-part parity** on an even extent. DERIVED: `2` the parity. -/
theorem col_shiftA {n : ℕ} (he : n % 2 = 0) (hn : 2 ≤ n) {i : Fin 4} (hi : i.val / 2 = 0) (c : St n) :
    colr (apart (rshift (fun _ => n) i c)) = !colr (apart c) := by
  rcases blockA i hi with rfl | rfl
  · have e : apart (rshift (fun _ => n) 0 c) = (finRotate n (c 0), c 1) := by simp [apart, rshift_apply]
    rw [e, colr_rot_left he hn]; rfl
  · have e : apart (rshift (fun _ => n) 1 c) = (c 0, finRotate n (c 1)) := by simp [apart, rshift_apply]
    rw [e, colr_rot_right he hn]; rfl

/-- **A second-block step flips the second-part parity** on an even extent. DERIVED: `2` the parity. -/
theorem col_shiftB {n : ℕ} (he : n % 2 = 0) (hn : 2 ≤ n) {j : Fin 4} (hj : ¬ j.val / 2 = 0) (c : St n) :
    colr (bpart (rshift (fun _ => n) j c)) = !colr (bpart c) := by
  rcases blockB j hj with rfl | rfl
  · have e : bpart (rshift (fun _ => n) 2 c) = (finRotate n (c 2), c 3) := by simp [bpart, rshift_apply]
    rw [e, colr_rot_left he hn]; rfl
  · have e : bpart (rshift (fun _ => n) 3 c) = (c 2, finRotate n (c 3)) := by simp [bpart, rshift_apply]
    rw [e, colr_rot_right he hn]; rfl

/-- **The first-block edge of `((i, j), y)`, indexed by parity.** No numeral. -/
def aD {n : ℕ} (i : Fin 4) (y : St n) (s : Bool) : Fin n × Fin n :=
  if colr (apart y) = s then apart y else apart (rshift (fun _ => n) i y)

/-- **The second-block edge of `((i, j), y)`, indexed by parity.** No numeral. -/
def bD {n : ℕ} (j : Fin 4) (y : St n) (t : Bool) : Fin n × Fin n :=
  if colr (bpart y) = t then bpart y else bpart (rshift (fun _ => n) j y)

theorem col_aD {n : ℕ} (he : n % 2 = 0) (hn : 2 ≤ n) {i : Fin 4} (hi : i.val / 2 = 0) (y : St n) (s : Bool) :
    colr (aD i y s) = s := by
  unfold aD
  by_cases h : colr (apart y) = s
  · rw [if_pos h, h]
  · rw [if_neg h, col_shiftA he hn hi]
    have := bool_of_ne _ _ h
    rw [this]; cases s <;> rfl

theorem col_bD {n : ℕ} (he : n % 2 = 0) (hn : 2 ≤ n) {j : Fin 4} (hj : ¬ j.val / 2 = 0) (y : St n) (t : Bool) :
    colr (bD j y t) = t := by
  unfold bD
  by_cases h : colr (bpart y) = t
  · rw [if_pos h, h]
  · rw [if_neg h, col_shiftB he hn hj]
    have := bool_of_ne _ _ h
    rw [this]; cases t <;> rfl

theorem aD_mem {n : ℕ} (he : n % 2 = 0) (hn : 2 ≤ n) {i : Fin 4} (hi : i.val / 2 = 0) (y c : St n) :
    apart c = aD i y (colr (apart c)) ↔ (apart c = apart y ∨ apart c = apart (rshift (fun _ => n) i y)) := by
  constructor
  · intro h
    unfold aD at h
    split_ifs at h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h) <;> rw [h] <;> unfold aD
    · rw [if_pos rfl]
    · rw [col_shiftA he hn hi, if_neg (bool_ne _)]

theorem bD_mem {n : ℕ} (he : n % 2 = 0) (hn : 2 ≤ n) {j : Fin 4} (hj : ¬ j.val / 2 = 0) (y c : St n) :
    bpart c = bD j y (colr (bpart c)) ↔ (bpart c = bpart y ∨ bpart c = bpart (rshift (fun _ => n) j y)) := by
  constructor
  · intro h
    unfold bD at h
    split_ifs at h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h) <;> rw [h] <;> unfold bD
    · rw [if_pos rfl]
    · rw [col_shiftB he hn hj, if_neg (bool_ne _)]

/-- **The corners of a normal mixed plaquette are a product of two edges**, read through parities, on an even
extent. No numeral. -/
theorem corner_iff {n : ℕ} (he : n % 2 = 0) (hn : 2 ≤ n) {i j : Fin 4} (hi : i.val / 2 = 0)
    (hj : ¬ j.val / 2 = 0) (y c : St n) :
    IsCorner n i j y c ↔ apart c = aD i y (colr (apart c)) ∧ bpart c = bD j y (colr (bpart c)) := by
  rw [aD_mem he hn hi, bD_mem he hn hj]
  have hA : apart (rshift (fun _ => n) i (rshift (fun _ => n) j y)) = apart (rshift (fun _ => n) i y) := by
    rw [rshift_comm (fun _ => n) i j y, apart_shiftB hj]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · exact ⟨Or.inr rfl, Or.inl (bpart_shiftA hi y)⟩
    · exact ⟨Or.inl (apart_shiftB hj y), Or.inr rfl⟩
    · exact ⟨Or.inr hA, Or.inr (bpart_shiftA hi _)⟩
  · rintro ⟨ha | ha, hb | hb⟩
    · exact Or.inl (site_ext ha hb)
    · exact Or.inr (Or.inr (Or.inl (site_ext (ha.trans (apart_shiftB hj y).symm) hb)))
    · exact Or.inr (Or.inl (site_ext ha (hb.trans (bpart_shiftA hi y).symm)))
    · exact Or.inr (Or.inr (Or.inr (site_ext (ha.trans hA.symm) (hb.trans (bpart_shiftA hi _).symm))))

/-- **An edge is fixed by its parity-indexed endpoints** on extent `≥ 3`: direction and base. DERIVED: `3` the
least extent on which two steps move; `2` the least extent. -/
theorem edge_inj {n : ℕ} (hn : 3 ≤ n) {X : Type*} (P : St n → X) (cl : X → Bool) {i i' : Fin 4} {y y' : St n}
    (hPi : ∀ c c' : St n, P c = P c' → c i = c' i) (hPi' : ∀ c c' : St n, P c = P c' → c i' = c' i')
    (h : (fun s => if cl (P y) = s then P y else P (rshift (fun _ => n) i y))
      = (fun s => if cl (P y') = s then P y' else P (rshift (fun _ => n) i' y'))) :
    i = i' ∧ P y = P y' := by
  have hn2 : 2 ≤ n := by omega
  have h1 : (if cl (P y) = cl (P y) then P y else P (rshift (fun _ => n) i y))
      = (if cl (P y') = cl (P y) then P y' else P (rshift (fun _ => n) i' y')) := congrFun h _
  have h2 : (if cl (P y) = !cl (P y) then P y else P (rshift (fun _ => n) i y))
      = (if cl (P y') = !cl (P y) then P y' else P (rshift (fun _ => n) i' y')) := congrFun h _
  rw [if_pos rfl] at h1
  rw [if_neg (bool_ne _)] at h2
  by_cases hc : cl (P y') = cl (P y)
  · have hc2 : ¬ cl (P y') = !cl (P y) := by rw [hc]; exact bool_ne _
    rw [if_pos hc] at h1
    rw [if_neg hc2] at h2
    refine ⟨?_, h1⟩
    by_contra hii
    have a1 := hPi _ _ h1
    have a2 := hPi _ _ h2
    rw [rshift_apply, if_pos rfl, rshift_apply, if_neg hii] at a2
    rw [← a1] at a2
    exact WindowRead.finRotate_ne hn2 _ a2
  · have hc' : cl (P y') = !cl (P y) := bool_of_ne _ _ hc
    rw [if_neg hc] at h1
    rw [if_pos hc'] at h2
    exfalso
    have b1 := hPi' _ _ h1
    have b2 := hPi' _ _ h2
    rw [rshift_apply, if_pos rfl] at b1
    by_cases hii : i' = i
    · subst hii
      rw [rshift_apply, if_pos rfl, b1] at b2
      exact finRotate2_ne hn _ b2
    · rw [rshift_apply, if_neg hii] at b2
      rw [b2] at b1
      exact WindowRead.finRotate_ne hn2 _ b1.symm

/-- **Different normal mixed plaquettes have different edge data** on extent `≥ 3`. DERIVED: `3` as in
`edge_inj`. -/
theorem data_inj {n : ℕ} (hn : 3 ≤ n) {i j i' j' : Fin 4} (hi : i.val / 2 = 0) (hj : ¬ j.val / 2 = 0)
    (hi' : i'.val / 2 = 0) (hj' : ¬ j'.val / 2 = 0) {y y' : St n}
    (ha : aD i y = aD i' y') (hb : bD j y = bD j' y') : i = i' ∧ j = j' ∧ y = y' := by
  obtain ⟨h1, h2⟩ := edge_inj hn apart colr (pA hi) (pA hi') ha
  obtain ⟨h3, h4⟩ := edge_inj hn bpart colr (pB hj) (pB hj') hb
  exact ⟨h1, h3, site_ext h2 h4⟩

theorem data_ne {n : ℕ} (hn : 3 ≤ n) {i j i' j' : Fin 4} (hi : i.val / 2 = 0) (hj : ¬ j.val / 2 = 0)
    (hi' : i'.val / 2 = 0) (hj' : ¬ j'.val / 2 = 0) {y y' : St n}
    (h : (((i, j), y) : Pq n) ≠ ((i', j'), y')) : ¬ (aD i y = aD i' y' ∧ bD j y = bD j' y') := by
  rintro ⟨ha, hb⟩
  obtain ⟨rfl, rfl, rfl⟩ := data_inj hn hi hj hi' hj' ha hb
  exact h rfl

/-- **The covering lemma**: for product cells indexed by `Bool × Bool`, if the data of `p` and `q` differ, then
`p` or `q` has a cell that neither of the two others has. No numeral. -/
theorem cover_pair {α β : Type*} (ap aq ar : Bool → α) (bp bq br : Bool → β) (hpq : ¬ (ap = aq ∧ bp = bq)) :
    (∃ s t, ¬ (ap s = aq s ∧ bp t = bq t) ∧ ¬ (ap s = ar s ∧ bp t = br t)) ∨
      (∃ s t, ¬ (aq s = ap s ∧ bq t = bp t) ∧ ¬ (aq s = ar s ∧ bq t = br t)) := by
  by_contra H
  have hP : ∀ s t, (ap s = aq s ∧ bp t = bq t) ∨ (ap s = ar s ∧ bp t = br t) := fun s t => by
    by_contra h
    exact H (Or.inl ⟨s, t, fun h1 => h (Or.inl h1), fun h2 => h (Or.inr h2)⟩)
  have hQ : ∀ s t, (aq s = ap s ∧ bq t = bp t) ∨ (aq s = ar s ∧ bq t = br t) := fun s t => by
    by_contra h
    exact H (Or.inr ⟨s, t, fun h1 => h (Or.inl h1), fun h2 => h (Or.inr h2)⟩)
  have hdiff : (∃ s, ap s ≠ aq s) ∨ (∃ t, bp t ≠ bq t) := by
    by_contra h
    push_neg at h
    exact hpq ⟨funext h.1, funext h.2⟩
  rcases hdiff with ⟨s, hs⟩ | ⟨t, ht⟩
  · have hr : ap s = ar s := by
      rcases hP s true with h | h
      · exact absurd h.1 hs
      · exact h.1
    rcases hQ s true with h | h
    · exact hs h.1.symm
    · exact hs (hr.trans h.1.symm)
  · have hr : bp t = br t := by
      rcases hP true t with h | h
      · exact absurd h.2 ht
      · exact h.2
    rcases hQ true t with h | h
    · exact ht h.2.symm
    · exact ht (hr.trans h.2.symm)

theorem priv_site {n : ℕ} (he : n % 2 = 0) (hn : 2 ≤ n) {i j i' j' i'' j'' : Fin 4} (hi : i.val / 2 = 0)
    (hj : ¬ j.val / 2 = 0) (hi' : i'.val / 2 = 0) (hj' : ¬ j'.val / 2 = 0) (hi'' : i''.val / 2 = 0)
    (hj'' : ¬ j''.val / 2 = 0) (y y' y'' : St n) (s t : Bool)
    (h1 : ¬ (aD i y s = aD i' y' s ∧ bD j y t = bD j' y' t))
    (h2 : ¬ (aD i y s = aD i'' y'' s ∧ bD j y t = bD j'' y'' t)) :
    IsCorner n i j y (mkS (aD i y s) (bD j y t)) ∧ ¬ IsCorner n i' j' y' (mkS (aD i y s) (bD j y t)) ∧
      ¬ IsCorner n i'' j'' y'' (mkS (aD i y s) (bD j y t)) := by
  refine ⟨(corner_iff he hn hi hj y _).mpr ⟨?_, ?_⟩, fun hc => h1 ?_, fun hc => h2 ?_⟩
  · rw [apart_mkS, col_aD he hn hi]
  · rw [bpart_mkS, col_bD he hn hj]
  · obtain ⟨ha, hb⟩ := (corner_iff he hn hi' hj' y' _).mp hc
    rw [apart_mkS, col_aD he hn hi] at ha
    rw [bpart_mkS, col_bD he hn hj] at hb
    exact ⟨ha, hb⟩
  · obtain ⟨ha, hb⟩ := (corner_iff he hn hi'' hj'' y'' _).mp hc
    rw [apart_mkS, col_aD he hn hi] at ha
    rw [bpart_mkS, col_bD he hn hj] at hb
    exact ⟨ha, hb⟩

/-- **A private corner**: of three normal mixed plaquettes on an even extent `≥ 3`, not all one plaquette, one has
a corner that is a corner of neither of the other two. DERIVED: `3` the least extent; `2` the parity. -/
theorem exists_private {n : ℕ} (hn : 3 ≤ n) (he : n % 2 = 0) {i j i' j' i'' j'' : Fin 4}
    (hi : i.val / 2 = 0) (hj : ¬ j.val / 2 = 0) (hi' : i'.val / 2 = 0) (hj' : ¬ j'.val / 2 = 0)
    (hi'' : i''.val / 2 = 0) (hj'' : ¬ j''.val / 2 = 0) (y y' y'' : St n)
    (hne : ¬ ((((i, j), y) : Pq n) = ((i', j'), y') ∧ (((i', j'), y') : Pq n) = ((i'', j''), y''))) :
    ∃ z, (IsCorner n i j y z ∧ ¬ IsCorner n i' j' y' z ∧ ¬ IsCorner n i'' j'' y'' z) ∨
      (IsCorner n i' j' y' z ∧ ¬ IsCorner n i j y z ∧ ¬ IsCorner n i'' j'' y'' z) ∨
      (IsCorner n i'' j'' y'' z ∧ ¬ IsCorner n i j y z ∧ ¬ IsCorner n i' j' y' z) := by
  have hn2 : 2 ≤ n := by omega
  by_cases hpq : (((i, j), y) : Pq n) = ((i', j'), y')
  · have hqr : (((i', j'), y') : Pq n) ≠ ((i'', j''), y'') := fun h => hne ⟨hpq, h⟩
    rcases cover_pair (aD i'' y'') (aD i' y') (aD i y) (bD j'' y'') (bD j' y') (bD j y)
      (data_ne hn hi'' hj'' hi' hj' (Ne.symm hqr)) with ⟨s, t, h1, h2⟩ | ⟨s, t, h1, h2⟩
    · obtain ⟨c1, c2, c3⟩ := priv_site he hn2 hi'' hj'' hi' hj' hi hj y'' y' y s t h1 h2
      exact ⟨_, Or.inr (Or.inr ⟨c1, c3, c2⟩)⟩
    · simp only [Prod.mk.injEq] at hpq
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hpq
      exact absurd ⟨rfl, rfl⟩ h2
  · rcases cover_pair (aD i y) (aD i' y') (aD i'' y'') (bD j y) (bD j' y') (bD j'' y'')
      (data_ne hn hi hj hi' hj' hpq) with ⟨s, t, h1, h2⟩ | ⟨s, t, h1, h2⟩
    · obtain ⟨c1, c2, c3⟩ := priv_site he hn2 hi hj hi' hj' hi'' hj'' y y' y'' s t h1 h2
      exact ⟨_, Or.inl ⟨c1, c2, c3⟩⟩
    · obtain ⟨c1, c2, c3⟩ := priv_site he hn2 hi' hj' hi hj hi'' hj'' y' y y'' s t h1 h2
      exact ⟨_, Or.inr (Or.inl ⟨c1, c2, c3⟩)⟩

/-! ## 2. The rotation at a private corner -/

/-- The holonomy of `((i, j), y)` read from the corner `y + i + j`. No numeral. -/
noncomputable def psiK {n : ℕ} (i j : Fin 4) (y : St n) (U : Lk n → SUN.SU N) : SUN.SU N :=
  (U (i, rshift (fun _ => n) j y))⁻¹ * (U (j, y))⁻¹ * U (i, y) * U (j, rshift (fun _ => n) i y)

theorem continuous_psiK {n : ℕ} (i j : Fin 4) (y : St n) : Continuous (psiK (N := N) i j y) := by
  unfold psiK; fun_prop

theorem plaq_eq_psiK {n : ℕ} (i j : Fin 4) (y : St n) (U : Lk n → SUN.SU N) :
    plaq N n ((i, j), y) U = WilsonAction.wilsonDensity (psiK i j y U) := by
  unfold plaq
  rw [show psiK i j y U = (U (i, y) * U (j, rshift (fun _ => n) i y))⁻¹ * (sysR (fun _ => n) N).hol ((i, j), y) U
      * ((U (i, y) * U (j, rshift (fun _ => n) i y))⁻¹)⁻¹ by
    unfold psiK; rw [hol_eq]; group, WilsonAction.wilsonDensity_conj]

/-- **The rotation at the far corner `y + i + j` left-translates the holonomy read there.** DERIVED: `2` the least
extent; `2`, `0` as in `MixCut.gT`. -/
theorem psiK_gT {n : ℕ} (hn : 2 ≤ n) {i j : Fin 4} (hi : i.val / 2 = 0) (hj : ¬ j.val / 2 = 0) (y : St n)
    (a : SUN.SU N) (U : Lk n → SUN.SU N) :
    psiK i j y (gT (fun _ => n) (siteG (fun _ => n) (rshift (fun _ => n) i (rshift (fun _ => n) j y)) a) U)
      = a * psiK i j y U := by
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  have h0 : y ≠ rshift (fun _ => n) i (rshift (fun _ => n) j y) :=
    (rshift2_ne (fun _ => n) hij hn y).symm
  have h1 : rshift (fun _ => n) i y ≠ rshift (fun _ => n) i (rshift (fun _ => n) j y) :=
    (ne_of_rot hn (k := j) (by simp [rshift_apply, Ne.symm hij])).symm
  have h2 : rshift (fun _ => n) j y ≠ rshift (fun _ => n) i (rshift (fun _ => n) j y) :=
    (WindowRead.rshift_ne _ hn _).symm
  unfold psiK
  simp only [gT, siteG, if_pos hi, if_neg hj, if_neg h0, if_neg h1, if_neg h2, ↓reduceIte, inv_one,
    mul_one, one_mul]
  group

/-- **The centring lemma**: a corner read `Φ` of `p` moved by a translation under the rotation at `z`, and a
continuous `G` fixed by it, give `∫ (φ_p − ⟨φ⟩) G e^{−β S_in} = 0`. DERIVED: `0` the decoupled end and the
centred mean. -/
theorem cent_move {n : ℕ} (β : ℝ) (p : Pq n) (z : St n) (G : (Lk n → SUN.SU N) → ℝ) (hG : Continuous G)
    (hGz : ∀ a U, G (gT (fun _ => n) (siteG (fun _ => n) z a) U) = G U)
    (Φ : (Lk n → SUN.SU N) → SUN.SU N) (hΦ : Continuous Φ)
    (hφ : ∀ U, plaq N n p U = WilsonAction.wilsonDensity (Φ U))
    (σ : SUN.SU N → SUN.SU N) (mf : SUN.SU N → SUN.SU N → SUN.SU N)
    (hm : Continuous fun pr : SUN.SU N × SUN.SU N => mf pr.1 pr.2)
    (hmΦ : ∀ g U, Φ (gT (fun _ => n) (siteG (fun _ => n) z (σ g)) U) = mf g (Φ U))
    (hmH : ∀ (f : SUN.SU N → ℝ) (k : SUN.SU N),
      ∫ g, f (mf g k) ∂(probHaar (SUN.SU N)) = ∫ g, f g ∂(probHaar (SUN.SU N))) :
    ∫ U, (plaq N n p U - WindowRead.haarMeanN N) * G U * Real.exp (-(β * sinR N n U)) ∂piH N n = 0 := by
  have hE : Continuous fun U : Lk n → SUN.SU N => G U * Real.exp (-(β * sinR N n U)) :=
    hG.mul (Real.continuous_exp.comp (continuous_const.mul (continuous_sinR n)).neg)
  have hf : Continuous fun g : SUN.SU N => WilsonAction.wilsonDensity g - WindowRead.haarMeanN N :=
    WilsonAction.continuous_wilsonDensity.sub continuous_const
  have key := integral_avg_gen (L := fun _ => n)
    (fun g => WilsonAction.wilsonDensity g - WindowRead.haarMeanN N) hf
    (fun g U => gT (fun _ => n) (siteG (fun _ => n) z (σ g)) U)
    (fun g F hF => integral_gT (fun _ => n) _ F hF) Φ hΦ
    (fun U => G U * Real.exp (-(β * sinR N n U))) hE mf hm hmΦ
    (fun g U => by simp only [hGz, sinR_gT])
    (fun k => hmH (fun g => WilsonAction.wilsonDensity g - WindowRead.haarMeanN N) k)
  have h0 : ∫ g, (WilsonAction.wilsonDensity g - WindowRead.haarMeanN N) ∂(probHaar (SUN.SU N)) = 0 := by
    rw [integral_sub (WilsonAction.continuous_wilsonDensity.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (integrable_const _), ContactFloor.integral_const_prob]
    unfold WindowRead.haarMeanN
    exact sub_self _
  rw [h0, zero_mul] at key
  refine (integral_congr_ae (Eventually.of_forall fun U => ?_)).trans key
  simp only [hφ U]
  ring

/-- **A corner of `p` that the rest of the integrand does not see centres it out.** DERIVED: `2` the least extent;
`0` the decoupled end. -/
theorem cent_factor {n : ℕ} (hn : 2 ≤ n) (β : ℝ) {i j : Fin 4} (hi : i.val / 2 = 0) (hj : ¬ j.val / 2 = 0)
    (y z : St n) (hz : IsCorner n i j y z) (G : (Lk n → SUN.SU N) → ℝ) (hG : Continuous G)
    (hGz : ∀ a U, G (gT (fun _ => n) (siteG (fun _ => n) z a) U) = G U) :
    ∫ U, (plaq N n ((i, j), y) U - WindowRead.haarMeanN N) * G U * Real.exp (-(β * sinR N n U)) ∂piH N n
      = 0 := by
  have hL : ∀ k : Fin 4, 2 ≤ (fun _ : Fin 4 => n) k := fun _ => hn
  rcases hz with h | h | h | h <;> rw [h] at hGz
  · exact cent_move β _ y G hG hGz (fun U => (sysR (fun _ => n) N).hol ((i, j), y) U)
      (MixAnchor.continuous_hol _) (fun U => rfl) (fun g => g) (fun g k => g * k) continuous_mul
      (fun g U => hol_gT_mixA (fun _ => n) hL g U hi hj y)
      (fun f k => integral_mul_right_eq_self (μ := probHaar (SUN.SU N)) f k)
  · exact cent_move β _ _ G hG hGz (psiI i j y) (continuous_psiI i j y) (plaq_eq_psiI i j y)
      (fun g => g⁻¹) (fun g k => k * g) (continuous_snd.mul continuous_fst)
      (fun g U => by rw [psiI_gT hn hi hj y g⁻¹ U, inv_inv])
      (fun f k => integral_mul_left_eq_self (μ := probHaar (SUN.SU N)) f k)
  · exact cent_move β _ _ G hG hGz (psiJ i j y) (continuous_psiJ i j y) (plaq_eq_psiJ i j y)
      (fun g => g⁻¹) (fun g k => k * g) (continuous_snd.mul continuous_fst)
      (fun g U => by rw [psiJ_gT hn hi hj y g⁻¹ U, inv_inv])
      (fun f k => integral_mul_left_eq_self (μ := probHaar (SUN.SU N)) f k)
  · exact cent_move β _ _ G hG hGz (psiK i j y) (continuous_psiK i j y) (plaq_eq_psiK i j y)
      (fun g => g) (fun g k => g * k) continuous_mul (fun g U => psiK_gT hn hi hj y g U)
      (fun f k => integral_mul_right_eq_self (μ := probHaar (SUN.SU N)) f k)

theorem plaq_gT_off {n : ℕ} {a b : Fin 4} (ha : a.val / 2 = 0) (hb : ¬ b.val / 2 = 0) (w z : St n)
    (g : SUN.SU N) (U : Lk n → SUN.SU N) (hz : ¬ IsCorner n a b w z) :
    plaq N n ((a, b), w) (gT (fun _ => n) (siteG (fun _ => n) z g) U) = plaq N n ((a, b), w) U := by
  unfold plaq
  rw [hol_gT_off ha hb w z g U hz]

/-! ## 3. Triple integrals at the decoupled end -/

/-- **The Haar third central moment of the plaquette density**, `κ₃^Haar(φ) = ∫ (φ − ⟨φ⟩)³ dHaar`. DERIVED: `3`
the cube. -/
noncomputable def haarCum3 (N : ℕ) : ℝ :=
  ∫ g, (WilsonAction.wilsonDensity (N := N) g - WindowRead.haarMeanN N) ^ 3 ∂(probHaar (SUN.SU N))

/-- **Three different-or-partly-equal normal mixed plaquettes average to zero** at the decoupled end, on an even
extent `≥ 3`, unless all three are one plaquette. DERIVED: `3` the least extent; `2` the parity. -/
theorem triple_ne {n : ℕ} (hn : 3 ≤ n) (he : n % 2 = 0) (β : ℝ) (p q r : Pq n)
    (hp : p.1.1.val / 2 = 0) (hp' : ¬ p.1.2.val / 2 = 0) (hq : q.1.1.val / 2 = 0) (hq' : ¬ q.1.2.val / 2 = 0)
    (hr : r.1.1.val / 2 = 0) (hr' : ¬ r.1.2.val / 2 = 0) (hne : ¬ (p = q ∧ q = r)) :
    ∫ U, (plaq N n p U - WindowRead.haarMeanN N) * (plaq N n q U - WindowRead.haarMeanN N)
      * (plaq N n r U - WindowRead.haarMeanN N) * Real.exp (-(β * sinR N n U)) ∂piH N n = 0 := by
  obtain ⟨⟨i, j⟩, y⟩ := p
  obtain ⟨⟨i', j'⟩, y'⟩ := q
  obtain ⟨⟨i'', j''⟩, y''⟩ := r
  replace hp : i.val / 2 = 0 := hp
  replace hp' : ¬ j.val / 2 = 0 := hp'
  replace hq : i'.val / 2 = 0 := hq
  replace hq' : ¬ j'.val / 2 = 0 := hq'
  replace hr : i''.val / 2 = 0 := hr
  replace hr' : ¬ j''.val / 2 = 0 := hr'
  have hn2 : 2 ≤ n := by omega
  have hc : ∀ s : Pq n, Continuous fun U : Lk n → SUN.SU N => plaq N n s U - WindowRead.haarMeanN N :=
    fun s => (continuous_plaq n s).sub continuous_const
  obtain ⟨z, h | h | h⟩ := exists_private hn he hp hp' hq hq' hr hr' y y' y'' hne
  · obtain ⟨h1, h2, h3⟩ := h
    have key := cent_factor (N := N) hn2 β hp hp' y z h1
      (fun U => (plaq N n ((i', j'), y') U - WindowRead.haarMeanN N)
        * (plaq N n ((i'', j''), y'') U - WindowRead.haarMeanN N)) ((hc _).mul (hc _))
      (fun g U => by simp only [plaq_gT_off hq hq' y' z g U h2, plaq_gT_off hr hr' y'' z g U h3])
    refine (integral_congr_ae (Eventually.of_forall fun U => ?_)).trans key
    try simp only
    ring
  · obtain ⟨h1, h2, h3⟩ := h
    have key := cent_factor (N := N) hn2 β hq hq' y' z h1
      (fun U => (plaq N n ((i, j), y) U - WindowRead.haarMeanN N)
        * (plaq N n ((i'', j''), y'') U - WindowRead.haarMeanN N)) ((hc _).mul (hc _))
      (fun g U => by simp only [plaq_gT_off hp hp' y z g U h2, plaq_gT_off hr hr' y'' z g U h3])
    refine (integral_congr_ae (Eventually.of_forall fun U => ?_)).trans key
    try simp only
    ring
  · obtain ⟨h1, h2, h3⟩ := h
    have key := cent_factor (N := N) hn2 β hr hr' y'' z h1
      (fun U => (plaq N n ((i, j), y) U - WindowRead.haarMeanN N)
        * (plaq N n ((i', j'), y') U - WindowRead.haarMeanN N)) ((hc _).mul (hc _))
      (fun g U => by simp only [plaq_gT_off hp hp' y z g U h2, plaq_gT_off hq hq' y' z g U h3])
    refine (integral_congr_ae (Eventually.of_forall fun U => ?_)).trans key
    try simp only
    ring

/-- **One mixed plaquette cubed and centred averages to `κ₃^Haar`** at the decoupled end. DERIVED: `2` the least
extent; `3` the cube; `0` the decoupled end. -/
theorem integral_cube {n : ℕ} (hn : 2 ≤ n) (β : ℝ) (p : Pq n) (hp : p.1.1.val / 2 = 0)
    (hp' : ¬ p.1.2.val / 2 = 0) :
    ∫ U, (plaq N n p U - WindowRead.haarMeanN N) * (plaq N n p U - WindowRead.haarMeanN N)
      * (plaq N n p U - WindowRead.haarMeanN N) * Real.exp (-(β * sinR N n U)) ∂piH N n
      = haarCum3 N * ∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n := by
  obtain ⟨⟨i, j⟩, y⟩ := p
  replace hp : i.val / 2 = 0 := hp
  replace hp' : ¬ j.val / 2 = 0 := hp'
  have hL : ∀ k : Fin 4, 2 ≤ (fun _ : Fin 4 => n) k := fun _ => hn
  have hE : Continuous fun U : Lk n → SUN.SU N => Real.exp (-(β * sinR N n U)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_sinR n)).neg
  have key := integral_avg_gen (L := fun _ => n)
    (fun g => (WilsonAction.wilsonDensity g - WindowRead.haarMeanN N) ^ 3)
    ((WilsonAction.continuous_wilsonDensity.sub continuous_const).pow 3)
    (fun g U => gT (fun _ => n) (siteG (fun _ => n) y g) U)
    (fun g F hF => integral_gT (fun _ => n) _ F hF)
    (fun U => (sysR (fun _ => n) N).hol ((i, j), y) U) (MixAnchor.continuous_hol _)
    (fun U => Real.exp (-(β * sinR N n U))) hE (fun g k => g * k) continuous_mul
    (fun g U => hol_gT_mixA (fun _ => n) hL g U hp hp' y) (fun g U => by simp only [sinR_gT])
    (fun k => integral_mul_right_eq_self (μ := probHaar (SUN.SU N))
      (fun g => (WilsonAction.wilsonDensity g - WindowRead.haarMeanN N) ^ 3) k)
  refine (integral_congr_ae (Eventually.of_forall fun U => ?_)).trans key
  simp only [plaq]
  ring

/-- The centred mixed term of one ordered plaquette. No numeral. -/
noncomputable def xm (N n : ℕ) (q : Pq n) (U : Lk n → SUN.SU N) : ℝ :=
  if AnisoTorus.inPlane q.1 then 0 else plaq N n q U - WindowRead.haarMeanN N

theorem continuous_xm (n : ℕ) (q : Pq n) : Continuous (xm N n q) := by
  unfold xm
  exact continuous_if_const _ (fun _ => continuous_const) (fun _ => (continuous_plaq n q).sub continuous_const)

/-- The partner indicator: `1` when `q'` is mixed and is `q` up to orientation. DERIVED: `1`, `0` the
indicator. -/
noncomputable def tw {n : ℕ} (q q' : Pq n) : ℝ :=
  if AnisoTorus.inPlane q'.1 then 0 else if onf q'.1 = onf q.1 ∧ q'.2 = q.2 then 1 else 0

/-- **Each mixed plaquette has two partners**: itself and its reverse. DERIVED: `2` the orientations. -/
theorem tw_sum (n : ℕ) (q : Pq n) (hq : ¬ AnisoTorus.inPlane q.1 = true) : ∑ q' : Pq n, tw q q' = 2 := by
  have hsw : ((q.1.swap, q.2) : Pq n) ≠ q := fun h => swap_ne q.1 hq (congrArg Prod.fst h)
  have hpt : ∀ q' : Pq n, tw q q'
      = (if q' = q then (1 : ℝ) else 0) + (if q' = (q.1.swap, q.2) then (1 : ℝ) else 0) := by
    intro q'
    by_cases hq' : AnisoTorus.inPlane q'.1 = true
    · have h1 : q' ≠ q := fun h => hq (h ▸ hq')
      have h2 : q' ≠ (q.1.swap, q.2) := fun h => hq (by
        have := congrArg (fun r : Pq n => AnisoTorus.inPlane r.1) h
        simp only [inPlane_swap'] at this
        rw [← this]; exact hq')
      simp only [tw, hq', if_true, if_neg h1, if_neg h2, add_zero]
    · have hiff := onf_iff q.1 q'.1 hq hq'
      simp only [tw, hq', Bool.false_eq_true, if_false]
      by_cases e1 : q' = q
      · subst e1
        simp [hsw.symm]
      · by_cases e2 : q' = (q.1.swap, q.2)
        · subst e2
          have ho : onf q.1.swap = onf q.1 :=
            (onf_iff q.1 q.1.swap hq (by rw [inPlane_swap']; exact hq)).mpr (Or.inr rfl)
          rw [if_pos ⟨ho, rfl⟩, if_neg hsw, if_pos rfl]
          norm_num
        · have hc : ¬ (onf q'.1 = onf q.1 ∧ q'.2 = q.2) := by
            rintro ⟨ho, hy⟩
            rcases hiff.mp ho with h | h
            · exact e1 (Prod.ext h hy)
            · exact e2 (Prod.ext h hy)
          rw [if_neg hc, if_neg e1, if_neg e2]
          norm_num
  rw [Finset.sum_congr rfl (fun q' _ => hpt q'), Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  norm_num

/-- **The triple integral of three ordered plaquettes** at the decoupled end, even extent `≥ 3`: `κ₃^Haar` when all
three are one mixed plaquette up to orientation, `0` otherwise. DERIVED: `3` the least extent; `2` the parity. -/
theorem integral_term {n : ℕ} (hn : 3 ≤ n) (he : n % 2 = 0) (β : ℝ) (q1 q2 q3 : Pq n) :
    ∫ U, xm N n q1 U * xm N n q2 U * xm N n q3 U * Real.exp (-(β * sinR N n U)) ∂piH N n
      = (if AnisoTorus.inPlane q1.1 then 0 else tw q1 q2 * tw q1 q3 * haarCum3 N)
        * ∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n := by
  by_cases h1 : AnisoTorus.inPlane q1.1 = true
  · simp [xm, h1]
  by_cases h2 : AnisoTorus.inPlane q2.1 = true
  · simp [xm, tw, h1, h2]
  by_cases h3 : AnisoTorus.inPlane q3.1 = true
  · simp [xm, tw, h1, h3]
  obtain ⟨a1, b1⟩ := onf_low q1.1 h1
  obtain ⟨a2, b2⟩ := onf_low q2.1 h2
  obtain ⟨a3, b3⟩ := onf_low q3.1 h3
  have e : ∀ U : Lk n → SUN.SU N, xm N n q1 U * xm N n q2 U * xm N n q3 U * Real.exp (-(β * sinR N n U))
      = (plaq N n (onf q1.1, q1.2) U - WindowRead.haarMeanN N)
        * (plaq N n (onf q2.1, q2.2) U - WindowRead.haarMeanN N)
        * (plaq N n (onf q3.1, q3.2) U - WindowRead.haarMeanN N) * Real.exp (-(β * sinR N n U)) := by
    intro U
    simp only [xm, h1, h2, h3, Bool.false_eq_true, if_false, plaq_onf]
  refine (integral_congr_ae (Eventually.of_forall e)).trans ?_
  rw [if_neg h1]
  by_cases hs : (onf q2.1 = onf q1.1 ∧ q2.2 = q1.2) ∧ (onf q3.1 = onf q1.1 ∧ q3.2 = q1.2)
  · have t2 : tw q1 q2 = 1 := by unfold tw; rw [if_neg h2, if_pos hs.1]
    have t3 : tw q1 q3 = 1 := by unfold tw; rw [if_neg h3, if_pos hs.2]
    have p2 : ((onf q2.1, q2.2) : Pq n) = (onf q1.1, q1.2) := Prod.ext hs.1.1 hs.1.2
    have p3 : ((onf q3.1, q3.2) : Pq n) = (onf q1.1, q1.2) := Prod.ext hs.2.1 hs.2.2
    rw [t2, t3, one_mul, one_mul, p2, p3]
    exact integral_cube (by omega) β _ a1 b1
  · have t : tw q1 q2 * tw q1 q3 = 0 := by
      unfold tw
      rw [if_neg h2, if_neg h3]
      rcases not_and_or.mp hs with h | h
      · rw [if_neg h, zero_mul]
      · rw [if_neg h, mul_zero]
    rw [t, zero_mul, zero_mul]
    refine triple_ne hn he β _ _ _ a1 b1 a2 b2 a3 b3 ?_
    rintro ⟨e12, e23⟩
    exact hs ⟨⟨(congrArg Prod.fst e12).symm, (congrArg Prod.snd e12).symm⟩,
      ⟨(congrArg Prod.fst (e12.trans e23)).symm, (congrArg Prod.snd (e12.trans e23)).symm⟩⟩

/-- **The triple count**: `8 n⁴` mixed plaquettes, two partners for each of the two other factors. DERIVED:
`32 = 8 · 2 · 2`; `8`, `4` as in `MixCut.sum_mixed`; `2` the partners. -/
theorem triple_sum (n : ℕ) (κ Z : ℝ) :
    ∑ a : Pq n, ∑ b : Pq n, ∑ c : Pq n,
      (if AnisoTorus.inPlane a.1 then 0 else tw a b * tw a c * κ) * Z = 32 * (n : ℝ) ^ 4 * κ * Z := by
  have hrow : ∀ a : Pq n, ∑ b : Pq n, ∑ c : Pq n,
      (if AnisoTorus.inPlane a.1 then 0 else tw a b * tw a c * κ) * Z
        = (if AnisoTorus.inPlane a.1 then (0 : ℝ) else 4 * κ) * Z := by
    intro a
    by_cases ha : AnisoTorus.inPlane a.1 = true
    · simp only [ha, if_true, zero_mul, Finset.sum_const_zero]
    · simp only [ha, Bool.false_eq_true, if_false]
      have hs : ∑ b : Pq n, ∑ c : Pq n, tw a b * tw a c * κ * Z
          = (∑ b : Pq n, tw a b) * (∑ c : Pq n, tw a c) * κ * Z := by
        rw [Finset.sum_mul_sum]
        simp only [Finset.sum_mul]
      rw [hs, tw_sum n a ha]
      ring
  rw [Finset.sum_congr rfl fun a _ => hrow a, ← Finset.sum_mul, sum_mixed]
  ring

/-- Integrals of a triple sum of continuous functions split. No numeral. -/
theorem integral_sum3 {n : ℕ} (F : Pq n → Pq n → Pq n → (Lk n → SUN.SU N) → ℝ)
    (hF : ∀ a b c, Continuous (F a b c)) :
    ∫ U, ∑ a : Pq n, ∑ b : Pq n, ∑ c : Pq n, F a b c U ∂piH N n
      = ∑ a : Pq n, ∑ b : Pq n, ∑ c : Pq n, ∫ U, F a b c U ∂piH N n := by
  have hI : ∀ G : (Lk n → SUN.SU N) → ℝ, Continuous G → Integrable G (piH N n) :=
    fun G hG => hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (f := fun a U => ∑ b : Pq n, ∑ c : Pq n, F a b c U)
    (fun a _ => hI _ (continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun c _ => hF a b c))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ (f := fun b U => ∑ c : Pq n, F a b c U)
    (fun b _ => hI _ (continuous_finsetSum _ fun c _ => hF a b c))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_finsetSum _ (f := fun c U => F a b c U) (fun c _ => hI _ (hF a b c))]

/-- **The centred mixed cube at the decoupled end**, even extent `n ≥ 3`:
`∫ (S_mix − 8 n⁴ ⟨φ⟩)³ e^{−β S_in} = 32 n⁴ κ₃^Haar ∫ e^{−β S_in}`. DERIVED: `32`, `8`, `4` as in `triple_sum`;
`3` the cube and the least extent; `2` the parity. -/
theorem cube_zero {n : ℕ} (hn : 3 ≤ n) (he : n % 2 = 0) (β : ℝ) :
    ∫ U, (smixR N n U - 8 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N) ^ 3 * Real.exp (-(β * sinR N n U)) ∂piH N n
      = 32 * (n : ℝ) ^ 4 * haarCum3 N * ∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n := by
  have hE : Continuous fun U : Lk n → SUN.SU N => Real.exp (-(β * sinR N n U)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_sinR n)).neg
  have hx : ∀ U, smixR N n U - 8 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N = ∑ q : Pq n, xm N n q U := by
    intro U
    unfold smixR
    rw [← sum_mixed n (WindowRead.haarMeanN N), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold xm
    split_ifs <;> ring
  have hpt : ∀ U, (smixR N n U - 8 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N) ^ 3 * Real.exp (-(β * sinR N n U))
      = ∑ a : Pq n, ∑ b : Pq n, ∑ c : Pq n,
          xm N n a U * xm N n b U * xm N n c U * Real.exp (-(β * sinR N n U)) := by
    intro U
    rw [hx U, pow_three, Finset.sum_mul_sum, Finset.sum_mul_sum]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  refine (integral_congr_ae (Eventually.of_forall hpt)).trans ?_
  rw [integral_sum3 (fun a b c U => xm N n a U * xm N n b U * xm N n c U * Real.exp (-(β * sinR N n U)))
    (fun a b c => (((continuous_xm n a).mul (continuous_xm n b)).mul (continuous_xm n c)).mul hE)]
  simp only [integral_term hn he β]
  exact triple_sum n _ _

/-! ## 4. The third cumulant and the slope of the variance -/

/-- The unnormalized third moment `∫ S_mix³ e^{−(β S_in + β_⊥ S_mix)}`. DERIVED: `3` the cube. -/
noncomputable def mixCube (N : ℕ) (β βp : ℝ) (n : ℕ) : ℝ :=
  ∫ U, smixR N n U * smixR N n U * smixR N n U * Real.exp (-(β * sinR N n U + βp * smixR N n U)) ∂piH N n

/-- **The third cumulant of the mixed action** `κ₃ = ⟨S³⟩ − 3 ⟨S⟩⟨S²⟩ + 2 ⟨S⟩³`. DERIVED: `3`, `2` the cumulant
coefficients of the third order. -/
noncomputable def cum3 (N : ℕ) (β βp : ℝ) (n : ℕ) : ℝ :=
  mixCube N β βp n / AnisoTorus.ZA N β βp n
    - 3 * meanMix N β βp n * (MixCutTest.mixSq N β βp n / AnisoTorus.ZA N β βp n) + 2 * meanMix N β βp n ^ 3

/-- `∂_{β_⊥} mixSq = −mixCube`. No numeral. -/
theorem hasDerivAt_mixSq (β t : ℝ) (n : ℕ) :
    HasDerivAt (fun x => MixCutTest.mixSq N β x n) (-mixCube N β t n) t :=
  MixCutTest.hasDerivAt_integral_mul_exp_lin (piH N n) (A := fun U => β * sinR N n U)
    (continuous_const.mul (continuous_sinR n)) (continuous_smixR n)
    ((continuous_smixR n).mul (continuous_smixR n)) t

/-- **`∂_{β_⊥} Var_n(S_mix) = −κ₃_n(S_mix)`**, at every `(β, β_⊥)`. DERIVED: `2` the square. -/
theorem hasDerivAt_varMix (β t : ℝ) (n : ℕ) :
    HasDerivAt (fun x => MixCutTest.varMix N β x n) (-cum3 N β t n) t := by
  have hZ := (ZA_pos (N := N) β t n).ne'
  have h := ((hasDerivAt_mixSq (N := N) β t n).div (hasDerivAt_ZA (N := N) β t n) hZ).sub
    ((MixCutTest.hasDerivAt_meanMix (N := N) β t n).pow 2)
  refine h.congr_deriv ?_
  unfold cum3 MixCutTest.varMix meanMix
  try simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
  field_simp
  ring

/-- **The centred cube expands into moments.** DERIVED: `3` the cube and its binomial coefficients. -/
theorem centred_cube (β βp : ℝ) (n : ℕ) (c : ℝ) :
    ∫ U, (smixR N n U - c) ^ 3 * Real.exp (-(β * sinR N n U + βp * smixR N n U)) ∂piH N n
      = mixCube N β βp n - 3 * c * MixCutTest.mixSq N β βp n + 3 * c ^ 2 * mixNum N β βp n
        - c ^ 3 * AnisoTorus.ZA N β βp n := by
  rw [ZA_eq_int]
  unfold mixCube MixCutTest.mixSq mixNum
  have hS := continuous_smixR (N := N) n
  have hI := continuous_sinR (N := N) n
  have hint : ∀ F : (Lk n → SUN.SU N) → ℝ, Continuous F → Integrable F (piH N n) :=
    fun F hF => hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_sub, ← integral_add,
    ← integral_sub]
  · refine integral_congr_ae (Eventually.of_forall fun U => ?_)
    try simp only
    ring
  all_goals exact hint _ (by fun_prop)

/-- **The third cumulant at the decoupled end is extensive and exact**: `κ₃_n(S_mix)(β, 0) = 32 n⁴ κ₃^Haar(φ)` on an
even extent `n ≥ 3`. DERIVED: `32`, `8`, `4` as in `triple_sum`; `3` the least extent; `2` the parity; `0` the
decoupled end. -/
theorem cum3_zero {n : ℕ} (hn : 3 ≤ n) (he : n % 2 = 0) (β : ℝ) :
    cum3 N β 0 n = 32 * (n : ℝ) ^ 4 * haarCum3 N := by
  have hZ0 : AnisoTorus.ZA N β 0 n = ∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n := by
    rw [ZA_eq_int]; simp only [zero_mul, add_zero]
  have hZne := (ZA_pos (N := N) β 0 n).ne'
  have hM := meanMix_zero (N := N) (show 2 ≤ n by omega) β
  have hnum : mixNum N β 0 n = 8 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N * AnisoTorus.ZA N β 0 n := by
    rw [← hM]; unfold meanMix; rw [div_mul_cancel₀ _ hZne]
  have hexp := centred_cube (N := N) β 0 n (8 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N)
  simp only [zero_mul, add_zero] at hexp
  rw [cube_zero hn he β, ← hZ0, hnum] at hexp
  have hcube : mixCube N β 0 n = 32 * (n : ℝ) ^ 4 * haarCum3 N * AnisoTorus.ZA N β 0 n
      + 3 * (8 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N) * MixCutTest.mixSq N β 0 n
      - 2 * (8 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N) ^ 3 * AnisoTorus.ZA N β 0 n := by
    linear_combination -hexp
  unfold cum3
  rw [hM, hcube]
  field_simp
  ring

/-- **The slope of the mixed variance at the decoupled end**: `∂_t Var_n(S_mix) = −32 n⁴ κ₃^Haar(φ)` at `t = 0`,
even extent `n ≥ 3`. DERIVED: as in `cum3_zero`; `32 = 8 · 2 · 2` as in `triple_sum`. -/
theorem hasDerivAt_varMix_zero {n : ℕ} (hn : 3 ≤ n) (he : n % 2 = 0) (β : ℝ) :
    HasDerivAt (fun x => MixCutTest.varMix N β x n) (-(32 * (n : ℝ) ^ 4 * haarCum3 N)) 0 := by
  have h := hasDerivAt_varMix (N := N) β 0 n
  rwa [cum3_zero hn he] at h

theorem three_le {w : ℕ} (hw : 2 ≤ w) : 3 ≤ 2 ^ w :=
  le_trans (by norm_num : 3 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hw)

theorem two_pow_mod {w : ℕ} (hw : 1 ≤ w) : 2 ^ w % 2 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  rw [pow_succ]
  omega

/-- **The variance difference is stationary at the decoupled end** for windows `w ≥ 2`:
`∂_t (16 Var_n − Var_{2n}) = 16 · (−32 n⁴ κ₃^Haar) + 32 (2n)⁴ κ₃^Haar = 0` at `t = 0`. DERIVED: `16 = 2⁴` the copies;
`2` the doubling and the least window with extent `≥ 3`; `0` the decoupled end. -/
theorem hasDerivAt_varGap_zero (β : ℝ) {w : ℕ} (hw : 2 ≤ w) :
    HasDerivAt (fun x => 16 * MixCutTest.varMix N β x (2 ^ w) - MixCutTest.varMix N β x (2 ^ (w + 1))) 0 0 := by
  have h1 := hasDerivAt_varMix_zero (N := N) (three_le hw) (two_pow_mod (by omega)) β
  have h2 := hasDerivAt_varMix_zero (N := N) (three_le (show 2 ≤ w + 1 by omega)) (two_pow_mod (by omega)) β
  refine ((h1.const_mul 16).sub h2).congr_deriv ?_
  push_cast
  ring

/-! ## 5. The cumulants as derivatives of `log Z`, and the doubling -/

/-- **The order-`k` cumulant of `S_mix` at the decoupled end**, `(−1)^k ∂_t^k log Z_n(β, t)` at `t = 0`.
DERIVED: `−1` the sign of `∂_t` on `e^{−t S}`; `0` the decoupled end. -/
noncomputable def kappa (N : ℕ) (β : ℝ) (k n : ℕ) : ℝ :=
  (-1) ^ k * iteratedDeriv k (fun t => AnisoTorus.logZA N β t n) 0

theorem deriv_logZA (β : ℝ) (n : ℕ) :
    deriv (fun t => AnisoTorus.logZA N β t n) = fun t => -meanMix N β t n :=
  funext fun t => (hasDerivAt_logZA β t n).deriv

theorem deriv_negMean (β : ℝ) (n : ℕ) :
    deriv (fun t => -meanMix N β t n) = fun t => MixCutTest.varMix N β t n :=
  funext fun t => by
    have h := ((MixCutTest.hasDerivAt_meanMix (N := N) β t n).neg).deriv
    rw [neg_neg] at h
    exact h

theorem deriv_varMix (β : ℝ) (n : ℕ) :
    deriv (fun t => MixCutTest.varMix N β t n) = fun t => -cum3 N β t n :=
  funext fun t => (hasDerivAt_varMix β t n).deriv

/-- `κ₂ = Var` at the decoupled end. DERIVED: `2` the order. -/
theorem kappa_two (β : ℝ) (n : ℕ) : kappa N β 2 n = MixCutTest.varMix N β 0 n := by
  unfold kappa
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_logZA, deriv_negMean]
  norm_num

/-- `κ₃ = cum3` at the decoupled end. DERIVED: `3` the order. -/
theorem kappa_three (β : ℝ) (n : ℕ) : kappa N β 3 n = cum3 N β 0 n := by
  unfold kappa
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, deriv_logZA, deriv_negMean, deriv_varMix]
  norm_num

/-- **`LocalCumulant N β k`, the order-`k` locality pattern**: the order-`k` cumulant at the decoupled end is
`c · n⁴` on every window past some `w₀`. DERIVED: `4` the dimension; `2` the doubling. -/
def LocalCumulant (N : ℕ) (β : ℝ) (k : ℕ) : Prop :=
  ∃ c : ℝ, ∃ w₀ : ℕ, ∀ w : ℕ, w₀ ≤ w → kappa N β k (2 ^ w) = c * ((2 ^ w : ℕ) : ℝ) ^ 4

/-- **`AllLocalCumulants N β`, a named input (not proved)**: the locality pattern at every order. No numeral. -/
def AllLocalCumulants (N : ℕ) (β : ℝ) : Prop := ∀ k : ℕ, LocalCumulant N β k

/-- **Order 2 is local**: `κ₂ = 16 n⁴ Var_Haar(φ)` past `w = 2`. DERIVED: `16`, `4` as in `MixEqui.varMix_zero`;
`2` the least window with extent `≥ 3`. -/
theorem localCumulant_two (β : ℝ) : LocalCumulant N β 2 :=
  ⟨16 * haarVar N, 2, fun w hw => by rw [kappa_two, varMix_zero (three_le hw)]; ring⟩

/-- **Order 3 is local**: `κ₃ = 32 n⁴ κ₃^Haar(φ)` past `w = 2`. DERIVED: as in `cum3_zero`. -/
theorem localCumulant_three (β : ℝ) : LocalCumulant N β 3 :=
  ⟨32 * haarCum3 N, 2, fun w hw => by
    rw [kappa_three, cum3_zero (three_le hw) (two_pow_mod (by omega))]; ring⟩

/-- **A local cumulant cancels in the doubling combination**: `16 c n⁴ − c (2n)⁴ = 0`. DERIVED: `16 = 2⁴` the
copies; `2` the doubling; `1` the next window. -/
theorem kappa_doubling (β : ℝ) {k : ℕ} (h : LocalCumulant N β k) :
    ∃ w₀ : ℕ, ∀ w : ℕ, w₀ ≤ w → 16 * kappa N β k (2 ^ w) - kappa N β k (2 ^ (w + 1)) = 0 := by
  obtain ⟨c, w₀, hc⟩ := h
  exact ⟨w₀, fun w hw => by rw [hc w hw, hc (w + 1) (by omega)]; push_cast; ring⟩

/-! ## 6. The window-uniform radius (a named input) -/

/-- **`VarGapOn N β t₁`**: `MixCutTest.VarGap` on the segment `[0, t₁]`. DERIVED: `16`, `2`, `1` as in
`MixCutTest.VarGap`; `0` the axis. -/
def VarGapOn (N : ℕ) (β t₁ : ℝ) : Prop :=
  ∃ K : ℝ, ∀ w : ℕ, 1 ≤ w → ∀ t : ℝ, 0 ≤ t → t ≤ t₁ →
    16 * MixCutTest.varMix N β t (2 ^ w) - MixCutTest.varMix N β t (2 ^ (w + 1)) ≤ K

/-- **`WindowUniformRadius N β t₁`, a named input (not proved)**: a convergent expansion of the variance difference
in `t` around the decoupled planes with a radius `ρ > t₁` and a coefficient bound `|a_k(w)| ≤ C ρ^{−k}` that do not
depend on the window `w`. DERIVED: `16`, `2`, `1` as in `MixCutTest.VarGap`; `0` the axis and the centre of the
expansion. -/
def WindowUniformRadius (N : ℕ) (β t₁ : ℝ) : Prop :=
  ∃ C ρ : ℝ, 0 < ρ ∧ t₁ < ρ ∧ ∀ w : ℕ, 1 ≤ w → ∃ a : ℕ → ℝ, (∀ k, |a k| ≤ C / ρ ^ k) ∧
    ∀ t : ℝ, 0 ≤ t → t ≤ t₁ → HasSum (fun k => a k * t ^ k)
      (16 * MixCutTest.varMix N β t (2 ^ w) - MixCutTest.varMix N β t (2 ^ (w + 1)))

/-- **A window-uniform radius bounds the variance difference on `[0, t₁]`**, with `K = C (1 − t₁/ρ)⁻¹`, by
comparison with the geometric series. DERIVED: `1` the geometric sum; `0` the floor of the terms. -/
theorem varGapOn_of_radius {β t₁ : ℝ} (h : WindowUniformRadius N β t₁) : VarGapOn N β t₁ := by
  obtain ⟨C, ρ, hρ, hρt, hw⟩ := h
  refine ⟨C * (1 - t₁ / ρ)⁻¹, fun w hw1 t ht0 ht1 => ?_⟩
  obtain ⟨a, ha, hs⟩ := hw w hw1
  have hr0 : 0 ≤ t₁ / ρ := div_nonneg (ht0.trans ht1) hρ.le
  have hr1 : t₁ / ρ < 1 := (div_lt_one hρ).mpr hρt
  have hg : HasSum (fun k => C * (t₁ / ρ) ^ k) (C * (1 - t₁ / ρ)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 hr1).mul_left C
  refine hasSum_le (fun k => ?_) (hs t ht0 ht1) hg
  have hk := ha k
  have htk : t ^ k ≤ t₁ ^ k := pow_le_pow_left₀ ht0 ht1 k
  calc a k * t ^ k ≤ |a k| * t ^ k := mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg ht0 k)
    _ ≤ C / ρ ^ k * t ^ k := mul_le_mul_of_nonneg_right hk (pow_nonneg ht0 k)
    _ ≤ C / ρ ^ k * t₁ ^ k := mul_le_mul_of_nonneg_left htk ((abs_nonneg _).trans hk)
    _ = C * (t₁ / ρ) ^ k := by rw [div_pow]; ring

/-- **`WindowUniformRadius N β β ⇒ MixCutTest.VarGap N β`.** A restatement of `VarGap` as a radius statement; it
discharges nothing. No numeral. -/
theorem varGap_of_radius {β : ℝ} (h : WindowUniformRadius N β β) : MixCutTest.VarGap N β :=
  varGapOn_of_radius h

end MassGap.MixExpand

#print axioms MassGap.MixExpand.apart_mkS
#print axioms MassGap.MixExpand.bpart_mkS
#print axioms MassGap.MixExpand.blockA
#print axioms MassGap.MixExpand.blockB
#print axioms MassGap.MixExpand.bool_ne
#print axioms MassGap.MixExpand.bool_of_ne
#print axioms MassGap.MixExpand.site_ext
#print axioms MassGap.MixExpand.pA
#print axioms MassGap.MixExpand.pB
#print axioms MassGap.MixExpand.apart_shiftB
#print axioms MassGap.MixExpand.bpart_shiftA
#print axioms MassGap.MixExpand.rot_val
#print axioms MassGap.MixExpand.colr_rot_left
#print axioms MassGap.MixExpand.colr_rot_right
#print axioms MassGap.MixExpand.col_shiftA
#print axioms MassGap.MixExpand.col_shiftB
#print axioms MassGap.MixExpand.col_aD
#print axioms MassGap.MixExpand.col_bD
#print axioms MassGap.MixExpand.aD_mem
#print axioms MassGap.MixExpand.bD_mem
#print axioms MassGap.MixExpand.corner_iff
#print axioms MassGap.MixExpand.edge_inj
#print axioms MassGap.MixExpand.data_inj
#print axioms MassGap.MixExpand.data_ne
#print axioms MassGap.MixExpand.cover_pair
#print axioms MassGap.MixExpand.priv_site
#print axioms MassGap.MixExpand.exists_private
#print axioms MassGap.MixExpand.continuous_psiK
#print axioms MassGap.MixExpand.plaq_eq_psiK
#print axioms MassGap.MixExpand.psiK_gT
#print axioms MassGap.MixExpand.cent_move
#print axioms MassGap.MixExpand.cent_factor
#print axioms MassGap.MixExpand.plaq_gT_off
#print axioms MassGap.MixExpand.triple_ne
#print axioms MassGap.MixExpand.integral_cube
#print axioms MassGap.MixExpand.continuous_xm
#print axioms MassGap.MixExpand.tw_sum
#print axioms MassGap.MixExpand.integral_term
#print axioms MassGap.MixExpand.triple_sum
#print axioms MassGap.MixExpand.integral_sum3
#print axioms MassGap.MixExpand.cube_zero
#print axioms MassGap.MixExpand.hasDerivAt_mixSq
#print axioms MassGap.MixExpand.hasDerivAt_varMix
#print axioms MassGap.MixExpand.centred_cube
#print axioms MassGap.MixExpand.cum3_zero
#print axioms MassGap.MixExpand.hasDerivAt_varMix_zero
#print axioms MassGap.MixExpand.three_le
#print axioms MassGap.MixExpand.two_pow_mod
#print axioms MassGap.MixExpand.hasDerivAt_varGap_zero
#print axioms MassGap.MixExpand.deriv_logZA
#print axioms MassGap.MixExpand.deriv_negMean
#print axioms MassGap.MixExpand.deriv_varMix
#print axioms MassGap.MixExpand.kappa_two
#print axioms MassGap.MixExpand.kappa_three
#print axioms MassGap.MixExpand.localCumulant_two
#print axioms MassGap.MixExpand.localCumulant_three
#print axioms MassGap.MixExpand.kappa_doubling
#print axioms MassGap.MixExpand.varGapOn_of_radius
#print axioms MassGap.MixExpand.varGap_of_radius
