import Mathlib
import MassGap.VortexCondense

/-!
# MassGap.TomboulisYaffe — the centre change of variables and the Tomboulis–Yaffe decomposition on the rectangular `SU(2)` torus

`VortexCondense.TYBoundR L a b o β` asks `wloopR L a b m n o β ≤ (1 − zR L a b β)^{mn/(L_a L_b)}` on every
admissible rectangle. This module works at those objects (`wloopR`, `ZRp`, `sheetR`, `zR` of
`GapSideVortexRect` and `VortexCondense`).

## Sources

* Tomboulis and Yaffe, Commun. Math. Phys. 100 (1985) 313.
* Kanazawa, arXiv:0808.3442, §2 (Theorem 1, eq. (4), and the proof of Theorem 2, eqs. (29)–(41)): for
  `SU(2)` the inequality as proved reads `⟨W(C)⟩ ≤ 2 {½ (1 − Z₋/Z)}^{A_C/(L_μ L_ν)}`, with
  `L_μ = 2^p l_μ`, `L_ν = 2^q l_ν` (the Schwarz doubling of the rectangle).

## What is proved

1. **The diagonal** (`not_tyBoundR_diag`): at `a = b`, `0 ≤ β`, `2 ≤ L a`, `TYBoundR L a a o β` is false. The
   rectangle in the plane `(a, a)` has holonomy `1` (`wloopR_diag = 1`), and `0 < zR L a a β ≤ 1`, so the
   right side at the `1 × 1` rectangle is `< 1`. `TYBoundR` is a statement about `a ≠ b` only.
2. **The centre change of variables.** `flipC L S` multiplies the links of `S` by `−1`; it preserves the
   product Haar measure (`flipC_mp`). A word's holonomy picks up `(−1)^{#S ∩ word}` (`wHol_flip`). Hence
   `ZRp_flip`: a plaquette pattern multiplied by the coboundary of `S` has the same partition function, and
   `WN_flip`: the Wilson numerator `WN` of a word changes by `(−1)^{#S ∩ word}`.
3. **Moving a sheet.** `sheetAt L a b pa pb` is the `−1` sheet of the plane `(a, b)` at `x_a = pa`, `x_b = pb`
   (`sheetR = sheetAt 0 0`, `sheetR_eq_sheetAt`). For `a ≠ b`, the sheets at `pa` and at `pa + 1` differ by the
   coboundary of `stepSet` (the `b`-links at `x_a = pa + 1`, `x_b = pb`): `sheet_step`. So every position has
   the same partition function (`ZRp_sheetAt`), and `zAt_eq_zR`.
4. **Crossing the loop.** For `0 < m < L a`, `0 < n < L b`, the `m × n` rectangle at `o` meets `stepSet` at
   `P = x_a(o) + m`, `pb = x_b(o)` in exactly one link (`count_cross`). With `sIn` (the sheet at `x_a = P − 1`,
   inside the rectangle) and `sOut` (at `x_a = P`, outside): `WN_cross`, `WN(sIn) = −WN(sOut)`.
5. **The decomposition** (Kanazawa (29)–(33) at `N = 2`). `ev β X` is the Wilson expectation, `vortexOp` the
   Boltzmann ratio of a pattern, `fluxOp = (1 − vortexOp)/2`. `ev_fluxOp_sheet`: the flux of either sheet
   reads `(1 − zR)/2`. `wloopR_eq_flux`: `wloopR = ev(fluxOp sIn · W) + ev(fluxOp sOut · W)`.
6. **Assembly.** `ChessboardFlux L a b o β` is the one remaining input: on every rectangle with
   `L_a = 2^p m`, `L_b = 2^q n` (`AdmTwo`), `ev(fluxOp s · W) ≤ ev(fluxOp s)^{mn/(L_a L_b)}` for `s = sIn`
   and `s = sOut` — the chessboard estimate of reflection positivity for the twisted plaquette observable.
   `tyTwo_of_chessboard`: it gives `wloopR ≤ 2 ((1 − zR)/2)^{mn/(L_a L_b)}`, the published form.
   `area_two_of_chessboard`: with `0 ≤ 1 − zR ≤ exp(−s L_a L_b)` that is `wloopR ≤ 2 exp(−s mn)`.

## What is not proved

* `ChessboardFlux`. Reflection positivity in the tree (`ReflPosG`, `ReflectPositive`) is on the cubic torus
  `Site d n`; none is on `RectWilson.RSite L` with a plaquette pattern, and no chessboard estimate is in the
  tree.
* `TYBoundR` at `a ≠ b`. The decomposition gives the factor `2 · 2^{−mn/(L_a L_b)} = 2^{1 − mn/(L_a L_b)} > 1`
  over `(1 − zR)^{mn/(L_a L_b)}`: `TYBoundR` is the published bound without that factor, and nothing here
  removes it. The published bound also needs `L_a/m`, `L_b/n` powers of two, which `Adm` does not ask.

DERIVED (module-wide): `2` is `|ℤ₂|` (the halves in `fluxOp` and the factor in front), and the base of the
doubling in `AdmTwo`; `1` the unit rectangle of the diagonal counterexample and the single crossing link.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.TomboulisYaffe

open MeasureTheory MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.GapSideVortexRect
  MassGap.VortexCondense MassGap.MovedTorusDecimation
open MassGap.TwistedTraceBound (negOne coe_negOne negOne_mul_self)

local notation "wd" => WilsonAction.wilsonDensity

/-! ## 1. The centre element -/

theorem negOne_comm (g : SUN.SU 2) : negOne * g = g * negOne :=
  Subtype.ext (by simp [coe_negOne])

theorem negOne_inv' : negOne⁻¹ = negOne := inv_eq_of_mul_eq_one_right negOne_mul_self

/-- The centre element `(−1)^k`. -/
def sg (k : ℕ) : SUN.SU 2 := negOne ^ k

theorem sg_comm (k : ℕ) (g : SUN.SU 2) : sg k * g = g * sg k := by
  have h : Commute negOne g := negOne_comm g
  exact (h.pow_left k).eq

theorem sg_add (j k : ℕ) : sg (j + k) = sg j * sg k := pow_add _ _ _

theorem sg_zero : sg 0 = 1 := pow_zero _

theorem sg_one : sg 1 = negOne := pow_one _

theorem sg_inv (k : ℕ) : (sg k)⁻¹ = sg k := by
  unfold sg
  rw [← inv_pow, negOne_inv']

theorem sg_mod (k : ℕ) : sg k = sg (k % 2) := by
  unfold sg
  conv_lhs => rw [← Nat.div_add_mod k 2]
  rw [pow_add, pow_mul, pow_two, negOne_mul_self, one_pow, one_mul]

theorem sg_congr {j k : ℕ} (h : j % 2 = k % 2) : sg j = sg k := by
  rw [sg_mod j, sg_mod k, h]

theorem sg_shuffle (a c : ℕ) (h P : SUN.SU 2) : sg a * h * (sg c * P) = sg (c + a) * (h * P) := by
  rw [add_comm, sg_add]
  simp only [mul_assoc]
  rw [← mul_assoc h, ← sg_comm c h, mul_assoc]

theorem one_sub_wd_negOne_mul (g : SUN.SU 2) : 1 - wd (negOne * g) = -(1 - wd g) := by
  unfold WilsonAction.wilsonDensity
  have : ((negOne * g : SUN.SU 2) : Matrix (Fin 2) (Fin 2) ℂ) = -(g : Matrix (Fin 2) (Fin 2) ℂ) := by
    show (negOne : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [coe_negOne, neg_one_mul]
  rw [this, Matrix.trace_neg, Complex.neg_re]
  ring

theorem one_sub_wd_sg (k : ℕ) (g : SUN.SU 2) : 1 - wd (sg k * g) = (-1) ^ k * (1 - wd g) := by
  induction k generalizing g with
  | zero => rw [sg_zero, one_mul, pow_zero, one_mul]
  | succ k ih =>
      have : sg (k + 1) * g = sg k * (negOne * g) := by
        rw [sg_add, sg_one, mul_assoc]
      rw [this, ih, one_sub_wd_negOne_mul, pow_succ]
      ring

/-! ## 2. The centre change of variables -/

section Flip

variable (L : Fin 4 → ℕ)

/-- **The centre flip** of the links of `S`: `U_l ↦ −U_l` on `S`. -/
def flipC (S : RLink L → Bool) (U : RLink L → SUN.SU 2) : RLink L → SUN.SU 2 :=
  fun l => sg (S l).toNat * U l

theorem flipC_mp (S : RLink L → Bool) :
    MeasurePreserving (flipC L S) (Measure.pi fun _ : RLink L => probHaar (SUN.SU 2))
      (Measure.pi fun _ : RLink L => probHaar (SUN.SU 2)) :=
  measurePreserving_pi (fun _ => probHaar (SUN.SU 2)) (fun _ => probHaar (SUN.SU 2))
    (fun l => measurePreserving_mul_left (probHaar (SUN.SU 2)) (sg (S l).toNat))

/-- **The flip leaves the integral of a continuous function unchanged.** -/
theorem integral_flipC (S : RLink L → Bool) {g : (RLink L → SUN.SU 2) → ℝ} (hg : Continuous g) :
    ∫ U, g U ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2))
      = ∫ U, g (flipC L S U) ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2)) := by
  have hmp := flipC_mp L S
  conv_lhs => rw [← hmp.map_eq]
  exact integral_map hmp.measurable.aemeasurable hg.aestronglyMeasurable

/-- The ordered holonomy of a word of oriented links. -/
def wHol (w : List (RLink L × Bool)) (U : RLink L → SUN.SU 2) : SUN.SU 2 :=
  (w.map (fun lo => if lo.2 then U lo.1 else (U lo.1)⁻¹)).prod

/-- The number of letters of `w` on links of `S`. -/
def wCount (S : RLink L → Bool) (w : List (RLink L × Bool)) : ℕ := w.countP (fun lo => S lo.1)

theorem continuous_wHol (w : List (RLink L × Bool)) :
    Continuous fun U : RLink L → SUN.SU 2 => wHol L w U := by
  induction w with
  | nil => simpa [wHol] using continuous_const
  | cons x w ih =>
      have hx : Continuous fun U : RLink L → SUN.SU 2 => if x.2 then U x.1 else (U x.1)⁻¹ := by
        by_cases h : x.2
        · simp only [h, if_true]; exact continuous_apply _
        · simp only [h]; exact (continuous_apply _).inv
      have : (fun U : RLink L → SUN.SU 2 => wHol L (x :: w) U)
          = fun U => (if x.2 then U x.1 else (U x.1)⁻¹) * wHol L w U := by
        funext U; simp [wHol]
      rw [this]
      exact hx.mul ih

/-- **A word's holonomy under the flip** picks up `(−1)^{#S ∩ w}`. -/
theorem wHol_flip (S : RLink L → Bool) (w : List (RLink L × Bool)) (U : RLink L → SUN.SU 2) :
    wHol L w (flipC L S U) = sg (wCount L S w) * wHol L w U := by
  induction w with
  | nil => simp [wHol, wCount, sg]
  | cons x w ih =>
      have hx : (if x.2 then flipC L S U x.1 else (flipC L S U x.1)⁻¹)
          = sg (S x.1).toNat * (if x.2 then U x.1 else (U x.1)⁻¹) := by
        unfold flipC
        split_ifs
        · rfl
        · rw [mul_inv_rev, sg_inv, sg_comm]
      have hc : wCount L S (x :: w) = wCount L S w + (S x.1).toNat := by
        unfold wCount
        rw [List.countP_cons]
        cases S x.1 <;> rfl
      have e1 : wHol L (x :: w) (flipC L S U)
          = (if x.2 then flipC L S U x.1 else (flipC L S U x.1)⁻¹) * wHol L w (flipC L S U) := by
        simp [wHol]
      have e2 : wHol L (x :: w) U = (if x.2 then U x.1 else (U x.1)⁻¹) * wHol L w U := by
        simp [wHol]
      rw [e1, e2, ih, hx, sg_shuffle, hc]

/-- The boundary word of a plaquette. -/
def pWord (q : RPlaq L) : List (RLink L × Bool) :=
  [((q.1.1, q.2), true), ((q.1.2, rshift L q.1.1 q.2), true), ((q.1.1, rshift L q.1.2 q.2), false),
    ((q.1.2, q.2), false)]

theorem rhol_eq_wHol (q : RPlaq L) (U : RLink L → SUN.SU 2) : rhol L q U = wHol L (pWord L q) U := by
  simp [rhol, wHol, pWord, mul_assoc]

theorem rhol_flip (S : RLink L → Bool) (q : RPlaq L) (U : RLink L → SUN.SU 2) :
    rhol L q (flipC L S U) = sg (wCount L S (pWord L q)) * rhol L q U := by
  rw [rhol_eq_wHol, rhol_eq_wHol, wHol_flip]

/-- **A pattern changed by the coboundary of `S` has the same partition function.** -/
theorem ZRp_flip (S : RLink L → Bool) (β : ℝ) (ζ ζ' : RPlaq L → SUN.SU 2)
    (h : ∀ q, ζ' q = sg (wCount L S (pWord L q)) * ζ q) : ZRp L β ζ' = ZRp L β ζ := by
  unfold ZRp
  rw [integral_flipC L S (continuous_integrand L β ζ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  dsimp only
  have hs : (∑ q, wd (ζ q * rhol L q (flipC L S U))) = ∑ q, wd (ζ' q * rhol L q U) :=
    Finset.sum_congr rfl fun q _ => by rw [h q, rhol_flip, ← mul_assoc, sg_comm]
  rw [hs]

/-- **The Wilson numerator** of a word in the pattern `ζ`: `∫ (1 − wd(U[w])) e^{−β Σ wd(ζ U_p)}`. -/
def WN (w : List (RLink L × Bool)) (β : ℝ) (ζ : RPlaq L → SUN.SU 2) : ℝ :=
  ∫ U, (1 - wd (wHol L w U)) * Real.exp (-β * ∑ q, wd (ζ q * rhol L q U))
    ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2))

theorem continuous_WN_integrand (w : List (RLink L × Bool)) (β : ℝ) (ζ : RPlaq L → SUN.SU 2) :
    Continuous fun U : RLink L → SUN.SU 2 =>
      (1 - wd (wHol L w U)) * Real.exp (-β * ∑ q, wd (ζ q * rhol L q U)) :=
  (continuous_const.sub (WilsonAction.continuous_wilsonDensity.comp (continuous_wHol L w))).mul
    (continuous_integrand L β ζ)

/-- **The centre change of variables for a Wilson loop**: a pattern changed by the coboundary of `S`
changes the Wilson numerator of `w` by `(−1)^{#S ∩ w}`. -/
theorem WN_flip (S : RLink L → Bool) (w : List (RLink L × Bool)) (β : ℝ) (ζ ζ' : RPlaq L → SUN.SU 2)
    (h : ∀ q, ζ' q = sg (wCount L S (pWord L q)) * ζ q) :
    WN L w β ζ = (-1) ^ (wCount L S w) * WN L w β ζ' := by
  unfold WN
  rw [integral_flipC L S (continuous_WN_integrand L w β ζ), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  dsimp only
  have hs : (∑ q, wd (ζ q * rhol L q (flipC L S U))) = ∑ q, wd (ζ' q * rhol L q U) :=
    Finset.sum_congr rfl fun q _ => by rw [h q, rhol_flip, ← mul_assoc, sg_comm]
  rw [wHol_flip, one_sub_wd_sg, mul_assoc, hs]

end Flip

/-! ## 3. The sheet at any position -/

section Sheet

variable (L : Fin 4 → ℕ)

/-- **The centre sheet of the plane `(a, b)` at `x_a = pa`, `x_b = pb`.** -/
def sheetAt (a b : Fin 4) (pa : Fin (L a)) (pb : Fin (L b)) (q : RPlaq L) : SUN.SU 2 :=
  if (q.1 = (a, b) ∨ q.1 = (b, a)) ∧ q.2 a = pa ∧ q.2 b = pb then negOne else 1

theorem sheetAt_symm (a b : Fin 4) (pa : Fin (L a)) (pb : Fin (L b)) :
    sheetAt L a b pa pb = sheetAt L b a pb pa := by
  funext q
  unfold sheetAt
  exact if_congr (by tauto) rfl rfl

theorem sheetR_eq_sheetAt (a b : Fin 4) (ha : 0 < L a) (hb : 0 < L b) :
    sheetR L a b = sheetAt L a b ⟨0, ha⟩ ⟨0, hb⟩ := by
  funext q
  unfold sheetR sheetAt
  refine if_congr ?_ rfl rfl
  simp only [Fin.ext_iff]

/-- The `b`-links at `x_a = P`, `x_b = pb`: the flip that moves a sheet one step along `a`. -/
def stepSet (a b : Fin 4) (P : Fin (L a)) (pb : Fin (L b)) (l : RLink L) : Bool :=
  decide (l.1 = b ∧ l.2 a = P ∧ l.2 b = pb)

theorem rshift_self' (i : Fin 4) (y : RSite L) : rshift L i y i = finRotate (L i) (y i) := by
  unfold rshift; exact Function.update_self _ _ _

theorem rshift_ne' {i c : Fin 4} (h : c ≠ i) (y : RSite L) : rshift L i y c = y c := by
  unfold rshift; exact Function.update_of_ne h _ _

theorem ite_negOne (c : Prop) [Decidable c] :
    (if c then negOne else (1 : SUN.SU 2)) = sg (if c then 1 else 0) := by
  split_ifs
  · exact sg_one.symm
  · exact sg_zero.symm

/-- **One step of the sheet along `a`.** The sheet at `x_a = P − 1` is the sheet at `x_a = P` times the
coboundary of the `b`-links at `x_a = P`, `x_b = pb`. -/
theorem sheet_step {a b : Fin 4} (hab : a ≠ b) (P : Fin (L a)) (pb : Fin (L b)) (q : RPlaq L) :
    sheetAt L a b ((finRotate (L a)).symm P) pb q
      = sg (wCount L (stepSet L a b P pb) (pWord L q)) * sheetAt L a b P pb q := by
  unfold sheetAt
  rw [ite_negOne, ite_negOne, ← sg_add]
  apply sg_congr
  obtain ⟨⟨i, j⟩, y⟩ := q
  simp only [wCount, pWord, stepSet, List.countP_cons, List.countP_nil, decide_eq_true_eq,
    Equiv.eq_symm_apply]
  have hba : b ≠ a := Ne.symm hab
  rcases (by tauto : (i = b ∧ j = b) ∨ (i = b ∧ j = a) ∨ (i = b ∧ j ≠ a ∧ j ≠ b) ∨
      (i = a ∧ j = b) ∨ (i ≠ a ∧ i ≠ b ∧ j = b) ∨ (i ≠ b ∧ j ≠ b)) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    simp only [Prod.mk.injEq, hba, and_false, false_and, or_self, if_false, true_and,
      rshift_ne' L hab, rshift_self']
    generalize finRotate (L b) (y b) = r
    by_cases e1 : y a = P <;> by_cases e2 : y b = pb <;> by_cases e3 : r = pb <;> simp [e1, e2, e3]
  · rw [h1, h2]
    simp only [Prod.mk.injEq, hab, hba, false_and, false_or, and_self,
      true_and, rshift_self', rshift_ne' L hba]
    generalize finRotate (L a) (y a) = r
    by_cases e1 : y a = P <;> by_cases e2 : y b = pb <;> by_cases e3 : r = P <;> simp [e1, e2, e3]
  · rw [h1]
    have hja : a ≠ j := Ne.symm h2
    have hjb : b ≠ j := Ne.symm h3
    simp only [Prod.mk.injEq, hba, h2, h3, and_false, false_and, or_self, if_false, true_and,
      rshift_ne' L hja, rshift_ne' L hjb]
    by_cases e1 : y a = P <;> by_cases e2 : y b = pb <;> simp [e1, e2]
  · rw [h1, h2]
    simp only [Prod.mk.injEq, hab, hba, false_and, or_false, and_self,
      true_and, rshift_self', rshift_ne' L hba]
    generalize finRotate (L a) (y a) = r
    by_cases e1 : y a = P <;> by_cases e2 : y b = pb <;> by_cases e3 : r = P <;> simp [e1, e2, e3]
  · rw [h3]
    have hia : a ≠ i := Ne.symm h1
    have hib : b ≠ i := Ne.symm h2
    simp only [Prod.mk.injEq, hba, h1, h2, and_false, false_and, or_self, if_false, true_and,
      rshift_ne' L hia, rshift_ne' L hib]
    by_cases e1 : y a = P <;> by_cases e2 : y b = pb <;> simp [e1, e2]
  · simp [h1, h2]

theorem ZRp_sheet_step {a b : Fin 4} (hab : a ≠ b) (P : Fin (L a)) (pb : Fin (L b)) (β : ℝ) :
    ZRp L β (sheetAt L a b ((finRotate (L a)).symm P) pb) = ZRp L β (sheetAt L a b P pb) :=
  ZRp_flip L (stepSet L a b P pb) β _ _ (sheet_step L hab P pb)

/-- Sliding the sheet along `a` to `x_a = 0`. -/
theorem ZRp_sheetAt_slide {a b : Fin 4} (hab : a ≠ b) (ha : 0 < L a) (β : ℝ) (pb : Fin (L b)) :
    ∀ (k : ℕ) (hk : k < L a), ZRp L β (sheetAt L a b ⟨k, hk⟩ pb) = ZRp L β (sheetAt L a b ⟨0, ha⟩ pb) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      have hk' : k < L a := by omega
      have hr : (finRotate (L a)).symm ⟨k + 1, hk⟩ = ⟨k, hk'⟩ := by
        rw [Equiv.symm_apply_eq]
        apply Fin.ext
        rw [val_finRotate]
        exact (Nat.mod_eq_of_lt hk).symm
      rw [← ZRp_sheet_step L hab, hr, ih hk']

/-- **Every position of the sheet has the same partition function as `sheetR`.** -/
theorem ZRp_sheetAt {a b : Fin 4} (hab : a ≠ b) (pa : Fin (L a)) (pb : Fin (L b)) (β : ℝ) :
    ZRp L β (sheetAt L a b pa pb) = ZRp L β (sheetR L a b) := by
  have ha : 0 < L a := lt_of_le_of_lt (Nat.zero_le _) pa.isLt
  have hb : 0 < L b := lt_of_le_of_lt (Nat.zero_le _) pb.isLt
  rw [sheetR_eq_sheetAt L a b ha hb]
  have h1 := ZRp_sheetAt_slide L hab ha β pb pa.val pa.isLt
  have h2 := ZRp_sheetAt_slide L (Ne.symm hab) hb β ⟨0, ha⟩ pb.val pb.isLt
  rw [sheetAt_symm L b a, sheetAt_symm L b a] at h2
  calc ZRp L β (sheetAt L a b pa pb) = ZRp L β (sheetAt L a b ⟨0, ha⟩ pb) := h1
    _ = ZRp L β (sheetAt L a b ⟨0, ha⟩ ⟨0, hb⟩) := h2

theorem zAt_eq_zR {a b : Fin 4} (hab : a ≠ b) (pa : Fin (L a)) (pb : Fin (L b)) (β : ℝ) :
    ZRp L β (sheetAt L a b pa pb) / ZR L 2 β = zR L a b β := by
  rw [ZRp_sheetAt L hab]
  rfl

end Sheet

/-! ## 4. The sheet crosses the rectangle once -/

section Cross

variable (L : Fin 4 → ℕ)

theorem iter_ne {i c : Fin 4} (h : c ≠ i) (t : ℕ) (y : RSite L) : ((rshift L i)^[t] y) c = y c := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', rshift_ne' L h, ih]

theorem iter_self_val (i : Fin 4) (t : ℕ) (y : RSite L) :
    (((rshift L i)^[t] y) i).val = ((y i).val + t) % L i := by
  induction t with
  | zero => exact (Nat.mod_eq_of_lt (y i).isLt).symm
  | succ t ih =>
      rw [Function.iterate_succ_apply', rshift_self', val_finRotate, ih, Nat.mod_add_mod, add_assoc]

theorem add_mod_ne {x m N : ℕ} (hx : x < N) (hm : 0 < m) (hmN : m < N) : (x + m) % N ≠ x := by
  by_cases h : x + m < N
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

/-- The corner of the far `b`-side: `x_a = x_a(o) + m`. -/
def farA (a : Fin 4) (m : ℕ) (o : RSite L) : Fin (L a) := ((rshift L a)^[m] o) a

/-- **The `m × n` rectangle meets the step set at its far `b`-side in exactly one link.** -/
theorem count_cross {a b : Fin 4} (hab : a ≠ b) (o : RSite L) {m n : ℕ} (hm : 0 < m) (hmL : m < L a)
    (hn : 0 < n) (hnL : n < L b) :
    wCount L (stepSet L a b (farA L a m o) (o b)) (VortexCondense.rectWord L a b m n o) = 1 := by
  have hba : b ≠ a := Ne.symm hab
  unfold wCount VortexCondense.rectWord
  simp only [List.countP_append, List.countP_reverse, List.countP_map]
  have hA : ∀ (y : ℕ → RSite L) (k : ℕ) (s : Bool),
      List.countP ((fun lo : RLink L × Bool => stepSet L a b (farA L a m o) (o b) lo.1) ∘
        (fun t => ((a, y t), s))) (List.range k) = 0 := by
    intro y k s
    refine List.countP_eq_zero.2 fun t _ => ?_
    simp [stepSet, hab]
  rw [hA, hA]
  have hD : List.countP ((fun lo : RLink L × Bool => stepSet L a b (farA L a m o) (o b) lo.1) ∘
      (fun t => ((b, (rshift L b)^[t] o), false))) (List.range n) = 0 := by
    refine List.countP_eq_zero.2 fun t _ => ?_
    simp only [Function.comp, stepSet, decide_eq_true_eq, not_and, iter_ne L hab]
    intro _ hP
    have hv := congrArg Fin.val hP
    simp only [farA] at hv
    rw [iter_self_val] at hv
    exact fun _ => add_mod_ne (o a).isLt hm hmL hv.symm
  rw [hD]
  have hB : List.countP ((fun lo : RLink L × Bool => stepSet L a b (farA L a m o) (o b) lo.1) ∘
      (fun t => ((b, (rshift L b)^[t] ((rshift L a)^[m] o)), true))) (List.range n)
      = List.countP (fun t => decide (t = 0)) (List.range n) := by
    refine List.countP_congr fun t ht => ?_
    have htn : t < n := List.mem_range.1 ht
    simp only [Function.comp, stepSet, decide_eq_true_eq, iter_ne L hab, farA, true_and]
    constructor
    · intro hb
      have hv := congrArg Fin.val hb
      rw [iter_self_val, iter_ne L hba] at hv
      by_contra h0
      exact add_mod_ne (o b).isLt (Nat.pos_of_ne_zero h0) (by omega) hv
    · intro h0
      subst h0
      rw [Function.iterate_zero_apply, iter_ne L hba]
  rw [hB]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [List.range_succ_eq_map, List.countP_cons, List.countP_map]
  have : List.countP ((fun t => decide (t = 0)) ∘ Nat.succ) (List.range k) = 0 :=
    List.countP_eq_zero.2 fun t _ => by simp
  rw [this]
  simp

/-- The sheet inside the rectangle, at `x_a = x_a(o) + m − 1`, `x_b = x_b(o)`. -/
def sIn (a b : Fin 4) (m : ℕ) (o : RSite L) : RPlaq L → SUN.SU 2 :=
  sheetAt L a b ((finRotate (L a)).symm (farA L a m o)) (o b)

/-- The sheet outside the rectangle, at `x_a = x_a(o) + m`, `x_b = x_b(o)`. -/
def sOut (a b : Fin 4) (m : ℕ) (o : RSite L) : RPlaq L → SUN.SU 2 :=
  sheetAt L a b (farA L a m o) (o b)

/-- **Moving the sheet across the loop changes the sign of the Wilson numerator.** -/
theorem WN_cross {a b : Fin 4} (hab : a ≠ b) (o : RSite L) {m n : ℕ} (hm : 0 < m) (hmL : m < L a)
    (hn : 0 < n) (hnL : n < L b) (β : ℝ) :
    WN L (VortexCondense.rectWord L a b m n o) β (sOut L a b m o)
      = -WN L (VortexCondense.rectWord L a b m n o) β (sIn L a b m o) := by
  rw [WN_flip L (stepSet L a b (farA L a m o) (o b)) _ β (sOut L a b m o) (sIn L a b m o)
    (sheet_step L hab _ _), count_cross L hab o hm hmL hn hnL]
  ring

end Cross

/-! ## 5. The decomposition -/

section Decomp

variable (L : Fin 4 → ℕ)

/-- **The Wilson expectation** of an observable on the rectangular torus. -/
def ev (β : ℝ) (X : (RLink L → SUN.SU 2) → ℝ) : ℝ :=
  (∫ U, X U * Real.exp (-β * ∑ q, wd (rhol L q U))
    ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2))) / ZRp L β (fun _ => 1)

/-- **The vortex creation operator** of a pattern: the Boltzmann ratio. -/
def vortexOp (β : ℝ) (ζ : RPlaq L → SUN.SU 2) (U : RLink L → SUN.SU 2) : ℝ :=
  Real.exp (-β * ∑ q, (wd (ζ q * rhol L q U) - wd (rhol L q U)))

/-- **The odd electric flux operator** `F^{[1]} = (1 − O)/2`. -/
def fluxOp (β : ℝ) (ζ : RPlaq L → SUN.SU 2) (U : RLink L → SUN.SU 2) : ℝ :=
  (1 - vortexOp L β ζ U) / 2

/-- The Wilson observable `½ Re tr U[w] = 1 − wd(U[w])`. -/
def wObs (w : List (RLink L × Bool)) (U : RLink L → SUN.SU 2) : ℝ := 1 - wd (wHol L w U)

theorem vortexOp_mul (β : ℝ) (ζ : RPlaq L → SUN.SU 2) (U : RLink L → SUN.SU 2) :
    vortexOp L β ζ U * Real.exp (-β * ∑ q, wd (rhol L q U))
      = Real.exp (-β * ∑ q, wd (ζ q * rhol L q U)) := by
  unfold vortexOp
  rw [← Real.exp_add, Finset.sum_sub_distrib]
  congr 1
  ring

theorem boltz_one (β : ℝ) (U : RLink L → SUN.SU 2) :
    Real.exp (-β * ∑ q, wd (rhol L q U)) = Real.exp (-β * ∑ q, wd ((fun _ => (1 : SUN.SU 2)) q * rhol L q U)) := by
  simp only [one_mul]

/-- **The flux operator times the Wilson loop**: `⟨F^{[1]}[ζ] W⟩ = (WN(1) − WN(ζ))/(2Z)`. -/
theorem ev_fluxOp_wObs (w : List (RLink L × Bool)) (β : ℝ) (ζ : RPlaq L → SUN.SU 2) :
    ev L β (fun U => fluxOp L β ζ U * wObs L w U)
      = (WN L w β (fun _ => 1) - WN L w β ζ) / (2 * ZRp L β (fun _ => 1)) := by
  have hpt : ∀ U : RLink L → SUN.SU 2,
      fluxOp L β ζ U * wObs L w U * Real.exp (-β * ∑ q, wd (rhol L q U))
        = ((1 - wd (wHol L w U)) * Real.exp (-β * ∑ q, wd ((fun _ => (1 : SUN.SU 2)) q * rhol L q U))
          - (1 - wd (wHol L w U)) * Real.exp (-β * ∑ q, wd (ζ q * rhol L q U))) / 2 := by
    intro U
    rw [← vortexOp_mul L β ζ U, ← boltz_one L β U]
    unfold fluxOp wObs
    ring
  unfold ev WN
  simp_rw [hpt]
  rw [integral_div, integral_sub (integrable_of_continuous (continuous_WN_integrand L w β _))
    (integrable_of_continuous (continuous_WN_integrand L w β ζ)), div_div]

/-- **The flux of a pattern** `⟨F^{[1]}[ζ]⟩ = (1 − Z_ζ/Z)/2`. -/
theorem ev_fluxOp (β : ℝ) (ζ : RPlaq L → SUN.SU 2) :
    ev L β (fluxOp L β ζ) = (1 - ZRp L β ζ / ZRp L β (fun _ => 1)) / 2 := by
  have hZ := ZRp_pos L β (fun _ => 1)
  have hpt : ∀ U : RLink L → SUN.SU 2,
      fluxOp L β ζ U * Real.exp (-β * ∑ q, wd (rhol L q U))
        = (Real.exp (-β * ∑ q, wd ((fun _ => (1 : SUN.SU 2)) q * rhol L q U))
          - Real.exp (-β * ∑ q, wd (ζ q * rhol L q U))) / 2 := by
    intro U
    rw [← vortexOp_mul L β ζ U, ← boltz_one L β U]
    unfold fluxOp
    ring
  unfold ev
  simp_rw [hpt]
  rw [integral_div, integral_sub (integrable_of_continuous (continuous_integrand L β _))
    (integrable_of_continuous (continuous_integrand L β ζ))]
  change ((ZRp L β (fun _ => 1) - ZRp L β ζ) / 2) / ZRp L β (fun _ => 1) = _
  field_simp

/-- **Both sheets carry the flux `(1 − zR)/2`.** -/
theorem ev_fluxOp_sheet {a b : Fin 4} (hab : a ≠ b) (pa : Fin (L a)) (pb : Fin (L b)) (β : ℝ) :
    ev L β (fluxOp L β (sheetAt L a b pa pb)) = (1 - zR L a b β) / 2 := by
  rw [ev_fluxOp, ← zAt_eq_zR L hab pa pb, ZR_eq_ZRp]

theorem wloopR_eq_WN (a b : Fin 4) (m n : ℕ) (o : RSite L) (β : ℝ) :
    wloopR L a b m n o β = WN L (VortexCondense.rectWord L a b m n o) β (fun _ => 1) / ZRp L β (fun _ => 1) := by
  unfold wloopR WN
  simp only [one_mul]
  rfl

/-- **The Tomboulis–Yaffe decomposition** (Kanazawa (29)–(33) at `N = 2`):
`wloopR = ⟨F^{[1]}[sIn] W⟩ + ⟨F^{[1]}[sOut] W⟩`. -/
theorem wloopR_eq_flux {a b : Fin 4} (hab : a ≠ b) (o : RSite L) {m n : ℕ} (hm : 0 < m) (hmL : m < L a)
    (hn : 0 < n) (hnL : n < L b) (β : ℝ) :
    wloopR L a b m n o β
      = ev L β (fun U => fluxOp L β (sIn L a b m o) U * wObs L (VortexCondense.rectWord L a b m n o) U)
        + ev L β (fun U => fluxOp L β (sOut L a b m o) U * wObs L (VortexCondense.rectWord L a b m n o) U) := by
  have hZ := ZRp_pos L β (fun _ => 1)
  rw [ev_fluxOp_wObs, ev_fluxOp_wObs, WN_cross L hab o hm hmL hn hnL, wloopR_eq_WN]
  field_simp
  ring

end Decomp

/-! ## 6. The diagonal -/

section Diag

variable (L : Fin 4 → ℕ)

theorem rhol_diag (a : Fin 4) (x : RSite L) (U : RLink L → SUN.SU 2) : rhol L ((a, a), x) U = 1 := by
  simp [rhol]

theorem wloopR_diag (a : Fin 4) (o : RSite L) (β : ℝ) : wloopR L a a 1 1 o β = 1 := by
  have hZ := ZRp_pos L β (fun _ => 1)
  have h1 : ∀ U : RLink L → SUN.SU 2, rectHol L a a 1 1 o U = 1 := fun U => by
    simp [rectHol, rectWord]
  unfold ZRp at hZ
  unfold wloopR ZRp
  simp only [h1, WilsonAction.wilsonDensity_one (N := 2) (by norm_num), sub_zero, one_mul] at hZ ⊢
  exact div_self hZ.ne'

theorem zR_diag_le_one (a : Fin 4) {β : ℝ} (hβ : 0 ≤ β) : zR L a a β ≤ 1 := by
  unfold zR
  rw [div_le_one (ZR_pos L β), ZR_eq_ZRp]
  unfold ZRp
  refine integral_mono (integrable_of_continuous (continuous_integrand L β _))
    (integrable_of_continuous (continuous_integrand L β _)) fun U => ?_
  refine Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left (Finset.sum_le_sum fun q _ => ?_) (by linarith))
  unfold sheetR
  split_ifs with h
  · obtain ⟨hq, -, -⟩ := h
    have hq' : q.1 = (a, a) := by tauto
    obtain ⟨⟨i, j⟩, x⟩ := q
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq'
    rw [rhol_diag, one_mul, mul_one, WilsonAction.wilsonDensity_one (N := 2) (by norm_num)]
    exact WilsonAction.wilsonDensity_nonneg (by norm_num) _
  · exact le_refl _

/-- **`TYBoundR` is false on the diagonal**: the rectangle in the plane `(a, a)` reads `1`, and the right
side at the `1 × 1` rectangle is below `1`. -/
theorem not_tyBoundR_diag (a : Fin 4) (o : RSite L) {β : ℝ} (hβ : 0 ≤ β) (h2 : 2 ≤ L a) :
    ¬ TYBoundR L a a o β := by
  intro h
  have hle := h 1 1 ⟨one_dvd _, one_dvd _, by omega, by omega⟩
  dsimp only at hle
  rw [wloopR_diag] at hle
  have hz0 := zR_pos L a a β
  have hz1 := zR_diag_le_one L a hβ
  have hLa : (0 : ℝ) < (L a : ℝ) := by exact_mod_cast (by omega : 0 < L a)
  have hLa1 : (1 : ℝ) < (L a : ℝ) := by exact_mod_cast (by omega : 1 < L a)
  have hx0 : (0 : ℝ) < ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) / ((L a : ℝ) * (L a : ℝ)) := by
    push_cast; positivity
  have hlt : (1 - zR L a a β) ^ (((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) / ((L a : ℝ) * (L a : ℝ))) < 1 :=
    Real.rpow_lt_one (by linarith) (by linarith) hx0
  linarith

end Diag

/-! ## 7. Assembly from the chessboard estimate -/

section Assembly

variable (L : Fin 4 → ℕ)

/-- **The rectangles of the Schwarz doubling**: admissible, and `L_a = 2^p m`, `L_b = 2^q n`. -/
def AdmTwo (La Lb m n : ℕ) : Prop := Adm La Lb m n ∧ (∃ p : ℕ, La = 2 ^ p * m) ∧ ∃ p : ℕ, Lb = 2 ^ p * n

/-- **The remaining input: the chessboard estimate for the twisted plaquette observable.** On every
`AdmTwo` rectangle, for the sheet inside (`sIn`) and the sheet outside (`sOut`),
`⟨F^{[1]}[s] W(C)⟩ ≤ ⟨F^{[1]}[s]⟩^{mn/(L_a L_b)}` in the Wilson measure of the rectangular torus. -/
def ChessboardFlux (a b : Fin 4) (o : RSite L) (β : ℝ) : Prop :=
  ∀ m n, AdmTwo (L a) (L b) m n →
    ev L β (fun U => fluxOp L β (sIn L a b m o) U * wObs L (VortexCondense.rectWord L a b m n o) U)
        ≤ ev L β (fluxOp L β (sIn L a b m o)) ^ (((m : ℝ) * n) / ((L a : ℝ) * L b)) ∧
      ev L β (fun U => fluxOp L β (sOut L a b m o) U * wObs L (VortexCondense.rectWord L a b m n o) U)
        ≤ ev L β (fluxOp L β (sOut L a b m o)) ^ (((m : ℝ) * n) / ((L a : ℝ) * L b))

theorem adm_pos {La Lb m n : ℕ} (h : Adm La Lb m n) : 0 < m ∧ 0 < n := by
  obtain ⟨hm, hn, hmL, hnL⟩ := h
  refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, Nat.pos_of_ne_zero fun h0 => ?_⟩
  · subst h0; rw [zero_dvd_iff] at hm; omega
  · subst h0; rw [zero_dvd_iff] at hn; omega

/-- **The Tomboulis–Yaffe inequality in its published form, from the chessboard estimate**:
`wloopR ≤ 2 ((1 − zR)/2)^{mn/(L_a L_b)}` on every `AdmTwo` rectangle. -/
theorem tyTwo_of_chessboard {a b : Fin 4} (hab : a ≠ b) (o : RSite L) {β : ℝ}
    (hCB : ChessboardFlux L a b o β) {m n : ℕ} (hadm : AdmTwo (L a) (L b) m n) :
    wloopR L a b m n o β ≤ 2 * ((1 - zR L a b β) / 2) ^ (((m : ℝ) * n) / ((L a : ℝ) * L b)) := by
  obtain ⟨hm, hn⟩ := adm_pos hadm.1
  rw [wloopR_eq_flux L hab o hm hadm.1.2.2.1 hn hadm.1.2.2.2 β]
  obtain ⟨h1, h2⟩ := hCB m n hadm
  rw [sIn, ev_fluxOp_sheet L hab] at h1
  rw [sOut, ev_fluxOp_sheet L hab] at h2
  rw [sIn, sOut]
  linarith

/-- **The area law with the prefactor `2`**: the chessboard estimate, `0 ≤ 1 − zR` and
`1 − zR ≤ exp(−s L_a L_b)` give `wloopR ≤ 2 exp(−s mn)` on every `AdmTwo` rectangle. -/
theorem area_two_of_chessboard {a b : Fin 4} (hab : a ≠ b) (o : RSite L) {β s : ℝ}
    (hCB : ChessboardFlux L a b o β) (he0 : 0 ≤ 1 - zR L a b β)
    (he : 1 - zR L a b β ≤ Real.exp (-(s * ((L a : ℝ) * L b)))) {m n : ℕ}
    (hadm : AdmTwo (L a) (L b) m n) :
    wloopR L a b m n o β ≤ 2 * Real.exp (-(s * ((m : ℝ) * n))) := by
  have hTY := tyTwo_of_chessboard L hab o hCB hadm
  have hLa : (0 : ℝ) < L a := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le m) hadm.1.2.2.1
  have hLb : (0 : ℝ) < L b := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le n) hadm.1.2.2.2
  have hA : (0 : ℝ) < (L a : ℝ) * L b := mul_pos hLa hLb
  have hx : 0 ≤ ((m : ℝ) * n) / ((L a : ℝ) * L b) := by positivity
  have h1 : ((1 - zR L a b β) / 2) ^ (((m : ℝ) * n) / ((L a : ℝ) * L b))
      ≤ (1 - zR L a b β) ^ (((m : ℝ) * n) / ((L a : ℝ) * L b)) :=
    Real.rpow_le_rpow (by linarith) (by linarith) hx
  have h2 : (1 - zR L a b β) ^ (((m : ℝ) * n) / ((L a : ℝ) * L b))
      ≤ Real.exp (-(s * ((m : ℝ) * n))) := by
    calc (1 - zR L a b β) ^ (((m : ℝ) * n) / ((L a : ℝ) * L b))
        ≤ (Real.exp (-(s * ((L a : ℝ) * L b)))) ^ (((m : ℝ) * n) / ((L a : ℝ) * L b)) :=
          Real.rpow_le_rpow he0 he hx
      _ = Real.exp (-(s * ((L a : ℝ) * L b)) * (((m : ℝ) * n) / ((L a : ℝ) * L b))) :=
          (Real.exp_mul _ _).symm
      _ = Real.exp (-(s * ((m : ℝ) * n))) := by
          congr 1
          rw [mul_div_assoc', div_eq_iff hA.ne']
          ring
  linarith

end Assembly

#print axioms negOne_comm
#print axioms sg_shuffle
#print axioms one_sub_wd_sg
#print axioms flipC_mp
#print axioms integral_flipC
#print axioms wHol_flip
#print axioms rhol_flip
#print axioms ZRp_flip
#print axioms WN_flip
#print axioms sheet_step
#print axioms ZRp_sheetAt
#print axioms zAt_eq_zR
#print axioms count_cross
#print axioms WN_cross
#print axioms ev_fluxOp_wObs
#print axioms ev_fluxOp
#print axioms ev_fluxOp_sheet
#print axioms wloopR_eq_WN
#print axioms wloopR_eq_flux
#print axioms wloopR_diag
#print axioms zR_diag_le_one
#print axioms not_tyBoundR_diag
#print axioms tyTwo_of_chessboard
#print axioms area_two_of_chessboard

end MassGap.TomboulisYaffe
