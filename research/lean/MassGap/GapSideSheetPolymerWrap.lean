import Mathlib
import MassGap.GapSideSheetPolymer

/-!
# MassGap.GapSideSheetPolymerWrap — only activated sets of at least `N²` plaquettes see the twist

`GapSideSheetPolymer.ZF_twist_sub_eq` writes `Z^ζ − Z` as a sum over the activated sets that no centre
relabelling clears (`Obstructs`). For the 't Hooft sheet of `SU(2)` in the plane `(a, b)` this module bounds
the size of such a set from below by the number of sheet positions.

* **Strips** (`strip`, `thol_strip`). Flipping by `−1` the `b`-links with `0 < x_a ≤ s`, `x_b = c` has
  coboundary `sheetAt a b 0 c · sheetAt a b s c`: the sheet at `(x_a, x_b) = (0, c)` times the sheet at
  `(s, c)`.
* **Every position is in the class** (`sheet_mul_thol_eq`). Two strips, one along `a` and one along `b`,
  carry the sheet at `(0, 0)` to the sheet at any `(s, t)`: `sheet · dχ = sheetAt a b s t`.
* **Wrapping** (`card_ge_of_obstructs`). An obstructing set meets every one of the `N²` disjoint positioned
  sheets, so it has at least `N²` plaquettes.
* **The twist ratio as a tail** (`ZF_sheet_sub_abs_le`, `ZF_sheet_sub_abs_le_pow`). Hence
  `|Z^tw − Z| ≤ Σ_{|X| ≥ N²} (|act^tw X| + |act X|)`, and with `|e^{−Φ_q} − 1| ≤ r` on every plaquette,
  `|Z^tw − Z| ≤ 2 Σ_{|X| ≥ N²} r^{|X|}`: an identity-level cancellation of every activated set below the
  sheet area, at every coupling.

Scope: the sum is over all activated sets of the torus, not connected ones, and it bounds the
difference `Z^tw − Z`, not the ratio. Dividing by `Z` uniformly in the volume is the connected-cluster
expansion of `log Z`, which this module does not supply.

DERIVED (module-wide): `0` is the base position of the tree's sheet (`x_a = x_b = 0`); `2` in `2 Σ` is the
twisted and untwisted activities; `N²` the positions `(s, t) ∈ Fin N × Fin N`.
-/

noncomputable section

namespace MassGap.GapSideSheetPolymerWrap

open MeasureTheory Set Filter MassGap.CompactGauge MassGap.SUN MassGap.TorusDoubling
  MassGap.HolderBondMoving MassGap.ChainFirstCrossing MassGap.MovedTorusDecimation
  MassGap.GapSideVortexStepSign MassGap.GapSideSheetPolymer
open MassGap.TwistedTraceBound (negOne coe_negOne negOne_mul_self)

variable {d N : ℕ}

/-- **The sheet at position `(u, v)`**: `−1` on the `(a, b)` and `(b, a)` entries at `x_a = u`, `x_b = v`. -/
def sheetAt (a b : Fin d) (u v : ℕ) (q : TPlaq d N) : SU 2 :=
  if (q.1 = (a, b) ∨ q.1 = (b, a)) ∧ (q.2 a).val = u ∧ (q.2 b).val = v then negOne else 1

/-- **A strip**: `−1` on the `b`-links with `0 < x_a ≤ s` and `x_b = c`. -/
def strip (a b : Fin d) (s c : ℕ) (l : TLink d N) : SU 2 :=
  if l.1 = b ∧ 0 < (l.2 a).val ∧ (l.2 a).val ≤ s ∧ (l.2 b).val = c then negOne else 1

theorem sheet_eq_sheetAt (a b : Fin d) :
    (GapSideTwistFlat.sheet a b negOne : TPlaq d N → SU 2) = sheetAt a b 0 0 := rfl

theorem sheetAt_swap (a b : Fin d) (u v : ℕ) :
    (sheetAt b a v u : TPlaq d N → SU 2) = sheetAt a b u v := by
  funext q
  unfold sheetAt
  exact if_congr (by tauto) rfl rfl

theorem sheetAt_mul_self (a b : Fin d) (u v : ℕ) (q : TPlaq d N) :
    sheetAt a b u v q * sheetAt a b u v q = 1 := by
  unfold sheetAt
  split_ifs
  · exact negOne_mul_self
  · exact mul_one 1

theorem strip_central (a b : Fin d) (s c : ℕ) (l : TLink d N) (g : SU 2) :
    strip a b s c l * g = g * strip a b s c l := by
  unfold strip
  split_ifs
  · exact negOne_central g
  · rw [one_mul, mul_one]

theorem rot_val (u : Fin N) :
    ((finRotate N u).val = u.val + 1 ∧ u.val + 1 < N) ∨ ((finRotate N u).val = 0 ∧ u.val + 1 = N) := by
  cases N with
  | zero => exact u.elim0
  | succ n =>
    rw [coe_finRotate]
    split_ifs with h
    · right
      exact ⟨rfl, by rw [h, Fin.val_last]⟩
    · left
      exact ⟨rfl, by have := Fin.val_lt_last h; omega⟩

/-- **The coboundary of a strip** is the sheet at `(0, c)` times the sheet at `(s, c)`. -/
theorem thol_strip {a b : Fin d} (hab : a ≠ b) {s : ℕ} (hs : s < N) (c : ℕ) (q : TPlaq d N) :
    thol q (strip a b s c) = sheetAt a b 0 c q * sheetAt a b s c q := by
  have hz : (negOne : SU 2)⁻¹ = negOne := GapSideTwistFlat.negOne_inv
  have hzz : (negOne : SU 2) * negOne = 1 := negOne_mul_self
  have hba : b ≠ a := Ne.symm hab
  obtain ⟨⟨i, j⟩, x⟩ := q
  have hxa := (x a).isLt
  by_cases hij : i = j
  · subst hij
    rw [thol_diag]
    have hd : ¬ ((i, i) = (a, b) ∨ (i, i) = (b, a)) := by
      rintro (h | h) <;> simp only [Prod.mk.injEq] at h <;> exact hab (by rw [← h.1, ← h.2])
    simp only [sheetAt, hd, false_and, if_false, mul_one]
  by_cases hib : i = b
  · subst hib
    by_cases hja : j = a
    · subst hja
      simp only [thol, strip, sheetAt, tshift_self, tshift_apply_ne hab, tshift_apply_ne hba, hab,
        false_and, if_false, inv_one, mul_one, true_and, or_true]
      rcases rot_val (x j) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] <;> split_ifs <;>
        first | rfl | (simp only [hz, hzz, inv_one, mul_one, one_mul]; done) | (exfalso; omega)
    · have hja' : j ≠ a := hja
      have hjb : j ≠ i := Ne.symm hij
      have hd : ¬ ((i, j) = (a, i) ∨ (i, j) = (i, a)) := by
        rintro (h | h) <;> simp only [Prod.mk.injEq] at h
        · exact hba h.1
        · exact hja' h.2
      simp only [thol, strip, sheetAt, hd, false_and, if_false, mul_one, tshift_apply_ne hja'.symm,
        tshift_apply_ne hjb.symm, hjb, inv_one]
      split_ifs <;> first | rfl | simp only [hz, hzz, inv_one, mul_one]
  · by_cases hjb : j = b
    · subst hjb
      by_cases hia : i = a
      · subst hia
        simp only [thol, strip, sheetAt, tshift_self, tshift_apply_ne hba, tshift_apply_ne hab, hab,
          false_and, if_false, inv_one, mul_one, one_mul, true_and, true_or]
        rcases rot_val (x i) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] <;> split_ifs <;>
          first | rfl | (simp only [hz, hzz, inv_one, mul_one, one_mul]; done) | (exfalso; omega)
      · have hd : ¬ ((i, j) = (a, j) ∨ (i, j) = (j, a)) := by
          rintro (h | h) <;> simp only [Prod.mk.injEq] at h
          · exact hia h.1
          · exact hib h.1
        simp only [thol, strip, sheetAt, hd, false_and, if_false, mul_one, one_mul,
          tshift_apply_ne (Ne.symm hia), tshift_apply_ne (Ne.symm hij), hib, inv_one]
        split_ifs <;> first | rfl | simp only [hz, hzz, inv_one, mul_one]
    · have hd : ¬ ((i, j) = (a, b) ∨ (i, j) = (b, a)) := by
        rintro (h | h) <;> simp only [Prod.mk.injEq] at h
        · exact hjb h.2
        · exact hib h.1
      simp only [thol, strip, sheetAt, hd, hib, hjb, false_and, if_false, mul_one, inv_one]

/-- **Every position of the sheet is in its class**: a centre field `χ` with `sheet · dχ = sheetAt a b s t`. -/
theorem sheet_mul_thol_eq {a b : Fin d} (hab : a ≠ b) (s t : Fin N) :
    ∃ χ : TLink d N → SU 2, (∀ l g, χ l * g = g * χ l) ∧
      ∀ q, GapSideTwistFlat.sheet a b negOne q * thol q χ = sheetAt a b s.val t.val q := by
  refine ⟨fun l => strip a b s.val 0 l * strip b a t.val s.val l, fun l g => ?_, fun q => ?_⟩
  · rw [mul_assoc, strip_central b a t.val s.val l g, ← mul_assoc, strip_central a b s.val 0 l g, mul_assoc]
  · rw [thol_mul_central (strip a b s.val 0) (strip b a t.val s.val) (strip_central a b s.val 0) q,
      thol_strip hab s.isLt 0 q, thol_strip (Ne.symm hab) t.isLt s.val q, sheet_eq_sheetAt,
      sheetAt_swap a b s.val 0, sheetAt_swap a b s.val t.val]
    simp only [mul_assoc]
    rw [← mul_assoc (sheetAt a b 0 0 q) (sheetAt a b 0 0 q), sheetAt_mul_self, one_mul,
      ← mul_assoc (sheetAt a b s.val 0 q) (sheetAt a b s.val 0 q), sheetAt_mul_self, one_mul]

/-- **An obstructing set wraps**: it meets every one of the `N²` positioned sheets, so `N² ≤ |X|`. -/
theorem card_ge_of_obstructs {a b : Fin d} (hab : a ≠ b) {X : Finset (TPlaq d N)}
    (h : Obstructs (GapSideTwistFlat.sheet a b negOne) X) : N ^ 2 ≤ X.card := by
  have key : ∀ p : Fin N × Fin N, ∃ q ∈ X, (q.2 a).val = p.1.val ∧ (q.2 b).val = p.2.val := by
    intro p
    obtain ⟨χ, hχ, hq⟩ := sheet_mul_thol_eq hab p.1 p.2
    obtain ⟨q, hqX, hne⟩ := h χ hχ
    rw [hq q] at hne
    refine ⟨q, hqX, ?_⟩
    unfold sheetAt at hne
    split_ifs at hne with hc
    · exact hc.2
    · exact absurd rfl hne
  choose f hfX hf using key
  have hinj : Set.InjOn f ↑(Finset.univ : Finset (Fin N × Fin N)) := by
    intro p _ p' _ he
    have h1 := (hf p).1
    have h2 := (hf p).2
    rw [he, (hf p').1] at h1
    rw [he, (hf p').2] at h2
    exact Prod.ext (Fin.ext h1.symm) (Fin.ext h2.symm)
  have hc := Finset.card_le_card_of_injOn f (fun p _ => hfX p) hinj
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hc
  rw [sq]
  exact hc

open Classical in
/-- **The twist ratio is a tail over wrapping sets**: `|Z^tw − Z| ≤ Σ_{|X| ≥ N²} (|act^tw X| + |act X|)`. -/
theorem ZF_sheet_sub_abs_le {a b : Fin d} (hab : a ≠ b) (Φ : TPlaq d N → SU 2 → ℝ)
    (hΦ : ∀ q, Continuous (Φ q)) :
    |ZF (probHaar (SU 2)) (fun q g => Φ q (GapSideTwistFlat.sheet a b negOne q * g))
        - ZF (probHaar (SU 2)) (fun q g => Φ q (1 * g))|
      ≤ ∑ X ∈ (Finset.univ : Finset (TPlaq d N)).powerset.filter (fun X => N ^ 2 ≤ X.card),
          (|act Φ (GapSideTwistFlat.sheet a b negOne) X| + |act Φ (fun _ => 1) X|) := by
  rw [ZF_twist_sub_eq Φ hΦ]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun X _ => abs_sub _ _).trans ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun X _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  intro X hX
  rw [Finset.mem_filter] at hX ⊢
  exact ⟨hX.1, card_ge_of_obstructs hab hX.2⟩

/-- **The activity bound**: `|act Φ ζ X| ≤ r^{|X|}` when `|e^{−Φ_q} − 1| ≤ r` everywhere. -/
theorem abs_act_le (Φ : TPlaq d N → SU 2 → ℝ) (ζ : TPlaq d N → SU 2) (X : Finset (TPlaq d N)) {r : ℝ}
    (hr : ∀ q g, |Real.exp (-Φ q g) - 1| ≤ r) : |act Φ ζ X| ≤ r ^ X.card := by
  have hpt : ∀ U : TLink d N → SU 2, ‖∏ q ∈ X, (Real.exp (-Φ q (ζ q * thol q U)) - 1)‖ ≤ r ^ X.card := by
    intro U
    rw [Real.norm_eq_abs, Finset.abs_prod]
    calc ∏ q ∈ X, |Real.exp (-Φ q (ζ q * thol q U)) - 1| ≤ ∏ _q ∈ X, r :=
          Finset.prod_le_prod (fun q _ => abs_nonneg _) (fun q _ => hr q _)
      _ = r ^ X.card := Finset.prod_const r
  have hb : ‖act Φ ζ X‖ ≤ r ^ X.card *
      ((Measure.pi fun _ : TLink d N => probHaar (SU 2)) Set.univ).toReal := by
    unfold act
    exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hpt)
  simpa [Real.norm_eq_abs] using hb

open Classical in
/-- **The sheet tail in the plaquette activity**: `|Z^tw − Z| ≤ 2 Σ_{|X| ≥ N²} r^{|X|}`. -/
theorem ZF_sheet_sub_abs_le_pow {a b : Fin d} (hab : a ≠ b) (Φ : TPlaq d N → SU 2 → ℝ)
    (hΦ : ∀ q, Continuous (Φ q)) {r : ℝ} (hr : ∀ q g, |Real.exp (-Φ q g) - 1| ≤ r) :
    |ZF (probHaar (SU 2)) (fun q g => Φ q (GapSideTwistFlat.sheet a b negOne q * g))
        - ZF (probHaar (SU 2)) (fun q g => Φ q (1 * g))|
      ≤ 2 * ∑ X ∈ (Finset.univ : Finset (TPlaq d N)).powerset.filter (fun X => N ^ 2 ≤ X.card),
          r ^ X.card := by
  refine (ZF_sheet_sub_abs_le hab Φ hΦ).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun X _ => ?_
  have h1 := abs_act_le Φ (GapSideTwistFlat.sheet a b negOne) X hr
  have h2 := abs_act_le Φ (fun _ => 1) X hr
  linarith

#print axioms rot_val
#print axioms thol_strip
#print axioms sheet_mul_thol_eq
#print axioms card_ge_of_obstructs
#print axioms ZF_sheet_sub_abs_le
#print axioms abs_act_le
#print axioms ZF_sheet_sub_abs_le_pow

end MassGap.GapSideSheetPolymerWrap
