import Mathlib
import MassGap.AbelianGen
import MassGap.GaugeE7

/-!
# MassGap.AbelianGenE7 — an abelian generator at `E₇`

`AbelianGen.abelianGenG_of_herm` gives `CompReduceG.AbelianGenG G` from a nonzero Hermitian `H`
whose every real multiple is in `GaugeLie.lieGen`. This module supplies such an `H` at `E₇` and
discharges the `hab` input of `ClayG.clayStatementAtG_GS` there.

## The generator

`GaugeE7.e7Weight`, the diagonal `−3` on `α`, `1` on `A`, `3` on `β`, `−1` on `B` (the `U(1)` of
`E₆ × U(1) ⊂ E₇`), in `lieGen` and nonzero by `GaugeE7.lieGen_e7Weight`.

## Real multiples

`lieGen` of `GaugeE7.instGaugeLieE7` is closed under real multiples (`lieGen_smul_E7`):

* Hermitian by `AbelianGen.herm_smul`, and `M J + J Mᵀ = 0` by `AbelianGen.symp_smul_eq_zero`.
* The derivation of the quartic: `e7Q4` is homogeneous of degree one in each of its four slots
  (`e7Q4_smul₁` … `e7Q4_smul₄`). Each slot enters through the coordinates `ftsAlpha`, `ftsA`,
  `ftsBeta`, `ftsB`, which commute with scalars, and through `dot27`, `N4tri`, `sharp2`, each
  homogeneous of degree one in each argument (the `_smul` lemmas below, slot by slot as
  `GaugeE7`'s `_neg` lemmas). With `(a • M) v = a (M v)` the four-slot sum at `a • M` is `a` times
  the one at `M`.

## The capstone

`clayStatementAtG_GS_E7` is `AbelianGen.clayAtGFromGS_of_abelianGenG` at `abelianGenG_E7`:
`ClayAtGFromGS E7`.

DERIVED (module-wide): no numeral beyond the block sizes `27`, `28` of the triple system.
-/

noncomputable section

namespace MassGap.AbelianGenE7

open MassGap MassGap.CompReduceG MassGap.AbelianGen
open MassGap.GaugeE7 MassGap.GaugeF4 MassGap.GaugeG2
open scoped Matrix

/-- A real multiple of a complex vector is the complex multiple by the same number.
DERIVED: no numeral. -/
theorem real_smul_vec {m : Type} (a : ℝ) (v : m → ℂ) : a • v = (a : ℂ) • v := by
  funext i
  simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]

/-- `(a • M) v = (a : ℂ) • (M v)` for a real `a`. DERIVED: no numeral. -/
theorem real_smul_mulVec {m : Type} [Fintype m] (a : ℝ) (M : Matrix m m ℂ) (v : m → ℂ) :
    (a • M) *ᵥ v = (a : ℂ) • (M *ᵥ v) := by
  rw [Matrix.smul_mulVec, real_smul_vec]

/-! ## Homogeneity, slot by slot -/

section Smul

variable {R : Type} [CommRing R]

theorem jp_smul (c : R) (P : Fin 27 → R) : jp (c • P) = c • jp P := by
  funext i; fin_cases i <;> simp [jp]

theorem jq_smul (c : R) (P : Fin 27 → R) : jq (c • P) = c • jq P := by
  funext i; fin_cases i <;> simp [jq]

theorem js_smul (c : R) (P : Fin 27 → R) : js (c • P) = c • js P := by
  funext i; fin_cases i <;> simp [js]

theorem im7_smul (c : R) (x : Fin 8 → R) : im7 (c • x) = c • im7 x := rfl

theorem dot7_smul_left (c : R) (x y : Fin 7 → R) : dot7 (c • x) y = c * dot7 x y := by
  simp only [dot7, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dot7_smul_right (c : R) (x y : Fin 7 → R) : dot7 x (c • y) = c * dot7 x y := by
  simp only [dot7, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dot8_smul_left (c : R) (x y : Fin 8 → R) : dot8 (c • x) y = c * dot8 x y := by
  simp only [dot8, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dot8_smul_right (c : R) (x y : Fin 8 → R) : dot8 x (c • y) = c * dot8 x y := by
  simp only [dot8, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dot27_smul_left (c : R) (A B : Fin 27 → R) : dot27 (c • A) B = c * dot27 A B := by
  simp only [dot27, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dot27_smul_right (c : R) (A B : Fin 27 → R) : dot27 A (c • B) = c * dot27 A B := by
  simp only [dot27, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem cross_smul_left (c : R) (x y : Fin 7 → R) : cross (c • x) y = c • cross x y := by
  funext k; fin_cases k <;> simp [cross] <;> ring

theorem cross_smul_right (c : R) (x y : Fin 7 → R) : cross x (c • y) = c • cross x y := by
  funext k; fin_cases k <;> simp [cross] <;> ring

theorem octMul_smul_left (c : R) (x y : Fin 8 → R) : octMul (c • x) y = c • octMul x y := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp only [octMul, Fin.cons_zero, im7_smul, dot7_smul_left, Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [octMul, Fin.cons_succ, im7_smul, cross_smul_left, Pi.smul_apply, smul_eq_mul]
    ring

theorem octMul_smul_right (c : R) (x y : Fin 8 → R) : octMul x (c • y) = c • octMul x y := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp only [octMul, Fin.cons_zero, im7_smul, dot7_smul_right, Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [octMul, Fin.cons_succ, im7_smul, cross_smul_right, Pi.smul_apply, smul_eq_mul]
    ring

theorem octConj_smul (c : R) (w : Fin 8 → R) : octConj (c • w) = c • octConj w := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp only [octConj, Fin.cons_zero, Pi.smul_apply, smul_eq_mul]
  · simp only [octConj, Fin.cons_succ, Pi.smul_apply, smul_eq_mul, mul_neg]

theorem octRe3_smul_1 (c : R) (x y z : Fin 8 → R) : octRe3 (c • x) y z = c * octRe3 x y z := by
  simp only [octRe3, dot7, im7, phi3, e3, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_seven]
  ring

theorem octRe3_smul_2 (c : R) (x y z : Fin 8 → R) : octRe3 x (c • y) z = c * octRe3 x y z := by
  simp only [octRe3, dot7, im7, phi3, e3, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_seven]
  ring

theorem octRe3_smul_3 (c : R) (x y z : Fin 8 → R) : octRe3 x y (c • z) = c * octRe3 x y z := by
  simp only [octRe3, dot7, im7, phi3, e3, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_seven]
  ring

theorem N4tri_smul_1 (r c : R) (P Q S : Fin 27 → R) :
    N4tri r (c • P) Q S = c * N4tri r P Q S := by
  simp only [N4tri, Pi.smul_apply, smul_eq_mul, jp_smul, octRe3_smul_1]
  ring

theorem N4tri_smul_2 (r c : R) (P Q S : Fin 27 → R) :
    N4tri r P (c • Q) S = c * N4tri r P Q S := by
  simp only [N4tri, Pi.smul_apply, smul_eq_mul, jp_smul, jq_smul, js_smul, dot8_smul_left,
    octRe3_smul_2]
  ring

theorem N4tri_smul_3 (r c : R) (P Q S : Fin 27 → R) :
    N4tri r P Q (c • S) = c * N4tri r P Q S := by
  simp only [N4tri, Pi.smul_apply, smul_eq_mul, jp_smul, jq_smul, js_smul, dot8_smul_right,
    octRe3_smul_3]
  ring

theorem shOff_smul_tu (r c t : R) (u v w : Fin 8 → R) :
    shOff r (c * t) (c • u) v w = c • shOff r t u v w := by
  funext i
  simp only [shOff, octMul_smul_left, octConj_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem shOff_smul_vw (r c t : R) (u v w : Fin 8 → R) :
    shOff r t u (c • v) (c • w) = c • shOff r t u v w := by
  funext i
  simp only [shOff, octMul_smul_right, octConj_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem sharp2_smul_left (r c : R) (P Q : Fin 27 → R) :
    sharp2 r (c • P) Q = c • sharp2 r P Q := by
  funext k
  fin_cases k <;> simp [sharp2, jp_smul, jq_smul, js_smul, dot8_smul_left, shOff_smul_tu] <;> ring

theorem sharp2_smul_right (r c : R) (P Q : Fin 27 → R) :
    sharp2 r P (c • Q) = c • sharp2 r P Q := by
  funext k
  fin_cases k <;> simp [sharp2, jp_smul, jq_smul, js_smul, dot8_smul_right, shOff_smul_vw] <;> ring

theorem ftsAlpha_smul (c : R) (v : Fin (28 + 28) → R) : ftsAlpha (c • v) = c * ftsAlpha v := by
  simp only [ftsAlpha, Pi.smul_apply, smul_eq_mul]

theorem ftsBeta_smul (c : R) (v : Fin (28 + 28) → R) : ftsBeta (c • v) = c * ftsBeta v := by
  simp only [ftsBeta, Pi.smul_apply, smul_eq_mul]

theorem ftsA_smul (c : R) (v : Fin (28 + 28) → R) : ftsA (c • v) = c • ftsA v := by
  funext k
  simp only [ftsA, Pi.smul_apply]

theorem ftsB_smul (c : R) (v : Fin (28 + 28) → R) : ftsB (c • v) = c • ftsB v := by
  funext k
  simp only [ftsB, Pi.smul_apply]

/-- `e7Q4` is homogeneous of degree one in its first vector. DERIVED: `28 = 1 + 27`, half the
dimension `56` of the triple system. -/
theorem e7Q4_smul₁ (r c : R) (v₁ v₂ v₃ v₄ : Fin (28 + 28) → R) :
    e7Q4 r (c • v₁) v₂ v₃ v₄ = c * e7Q4 r v₁ v₂ v₃ v₄ := by
  simp only [e7Q4, ftsAlpha_smul, ftsBeta_smul, ftsA_smul, dot27_smul_left, sharp2_smul_left]
  ring

/-- `e7Q4` is homogeneous of degree one in its second vector. DERIVED: `28 = 1 + 27`, half the
dimension `56` of the triple system. -/
theorem e7Q4_smul₂ (r c : R) (v₁ v₂ v₃ v₄ : Fin (28 + 28) → R) :
    e7Q4 r v₁ (c • v₂) v₃ v₄ = c * e7Q4 r v₁ v₂ v₃ v₄ := by
  simp only [e7Q4, ftsBeta_smul, ftsA_smul, ftsB_smul, dot27_smul_right, dot27_smul_left,
    N4tri_smul_1, sharp2_smul_right]
  ring

/-- `e7Q4` is homogeneous of degree one in its third vector. DERIVED: `28 = 1 + 27`, half the
dimension `56` of the triple system. -/
theorem e7Q4_smul₃ (r c : R) (v₁ v₂ v₃ v₄ : Fin (28 + 28) → R) :
    e7Q4 r v₁ v₂ (c • v₃) v₄ = c * e7Q4 r v₁ v₂ v₃ v₄ := by
  simp only [e7Q4, ftsAlpha_smul, ftsA_smul, ftsB_smul, dot27_smul_left, dot27_smul_right,
    N4tri_smul_2, sharp2_smul_left]
  ring

/-- `e7Q4` is homogeneous of degree one in its fourth vector. DERIVED: `28 = 1 + 27`, half the
dimension `56` of the triple system. -/
theorem e7Q4_smul₄ (r c : R) (v₁ v₂ v₃ v₄ : Fin (28 + 28) → R) :
    e7Q4 r v₁ v₂ v₃ (c • v₄) = c * e7Q4 r v₁ v₂ v₃ v₄ := by
  simp only [e7Q4, ftsBeta_smul, ftsA_smul, ftsB_smul, dot27_smul_right, N4tri_smul_3,
    sharp2_smul_right]
  ring

end Smul

/-! ## `E₇` -/

/-- **`lieGen` of `E₇` is closed under real multiples**: Hermitian and `M J + J Mᵀ = 0` by
`AbelianGen`, and the four-slot derivation sum of `e7Q4` at `a • M` is `a` times the one at `M`.

DERIVED: `28 = 1 + 27`, half the dimension `56` of the triple system. -/
theorem lieGen_smul_E7 {M : Matrix (Fin (28 + 28)) (Fin (28 + 28)) ℂ}
    (h : MassGap.ClayTreeG.GaugeLie.lieGen (G := E7) M) (a : ℝ) :
    MassGap.ClayTreeG.GaugeLie.lieGen (G := E7) (a • M) := by
  obtain ⟨hH, hS, hD⟩ := h
  refine ⟨herm_smul hH a, symp_smul_eq_zero hS a, fun v => ?_⟩
  have hD' : e7Q4 s2C (M *ᵥ v) v v v + e7Q4 s2C v (M *ᵥ v) v v + e7Q4 s2C v v (M *ᵥ v) v
      + e7Q4 s2C v v v (M *ᵥ v) = 0 := hD v
  show e7Q4 s2C ((a • M) *ᵥ v) v v v + e7Q4 s2C v ((a • M) *ᵥ v) v v
    + e7Q4 s2C v v ((a • M) *ᵥ v) v + e7Q4 s2C v v v ((a • M) *ᵥ v) = 0
  rw [real_smul_mulVec, e7Q4_smul₁, e7Q4_smul₂, e7Q4_smul₃, e7Q4_smul₄]
  linear_combination (a : ℂ) * hD'

/-- **`AbelianGenG E7`** at `H = GaugeE7.e7Weight`: in `lieGen` and nonzero by
`GaugeE7.lieGen_e7Weight`, every real multiple in `lieGen` by `lieGen_smul_E7`.

DERIVED: no numeral. -/
theorem abelianGenG_E7 : AbelianGenG E7 := by
  obtain ⟨hgen, h0⟩ := lieGen_e7Weight
  have hH : e7Weight.IsHermitian := And.left hgen
  exact abelianGenG_of_herm (G := E7) e7Weight hH h0 fun a => lieGen_smul_E7 hgen a

/-- **`ClayG.clayStatementAtG_GS` at `E₇` with `hab` discharged.** DERIVED: no numeral. -/
theorem clayStatementAtG_GS_E7 : ClayAtGFromGS E7 :=
  clayAtGFromGS_of_abelianGenG abelianGenG_E7

end MassGap.AbelianGenE7

end

#print axioms MassGap.AbelianGenE7.real_smul_mulVec
#print axioms MassGap.AbelianGenE7.sharp2_smul_left
#print axioms MassGap.AbelianGenE7.sharp2_smul_right
#print axioms MassGap.AbelianGenE7.e7Q4_smul₁
#print axioms MassGap.AbelianGenE7.e7Q4_smul₂
#print axioms MassGap.AbelianGenE7.e7Q4_smul₃
#print axioms MassGap.AbelianGenE7.e7Q4_smul₄
#print axioms MassGap.AbelianGenE7.lieGen_smul_E7
#print axioms MassGap.AbelianGenE7.abelianGenG_E7
#print axioms MassGap.AbelianGenE7.clayStatementAtG_GS_E7
