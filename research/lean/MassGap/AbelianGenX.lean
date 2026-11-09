import Mathlib
import MassGap.AbelianGen
import MassGap.GaugeF4
import MassGap.GaugeE6
import MassGap.GaugeE8

/-!
# MassGap.AbelianGenX — an abelian generator at `F₄`, `E₆`, `E₈`

`AbelianGen.abelianGenG_of_herm` gives `CompReduceG.AbelianGenG G` from a nonzero Hermitian `H`
whose every real multiple is in `GaugeLie.lieGen`. This module supplies such an `H` at the three
exceptional groups below and discharges the `hab` input of `ClayG.clayStatementAtG_GS` there.

## The generators

* `F₄`: `GaugeF4.cartanF4`, in `lieGen` and nonzero by `GaugeF4.lieGen_cartanF4`.
* `E₆`: `GaugeE6.cartanE6`, in `lieGen` and nonzero by `GaugeE6.lieGen_cartanE6`.
* `E₈`: `GaugeE8.cartanM`, in `lieGen` and nonzero by `GaugeE8.lieGen_cartanM`.

## Real multiples

Each `lieGen` predicate is closed under real multiples. Hermitian, `tr` and `ᵀ` are
`AbelianGen.herm_smul`, `trace_smul_eq_zero`, `transpose_smul_eq_neg`. The derivation conditions:

* `F₄`, `E₆`: `f4Tri`, `e6Tri` are homogeneous of degree one in each slot (`f4Tri_smul₁` …,
  `e6Tri_smul₁` …), and `(a • M) x = a (M x)`, so the condition at `a • M` is `a` times the one
  at `M`.
* `E₈`: `br` is homogeneous of degree one in each slot (`br_smul₁`, `br_smul₂`, from `phiL`
  homogeneous in its first two vectors by induction on the list of codes), so
  `(a • M) [x, y] = a (M [x, y]) = a ([M x, y] + [x, M y]) = [(a • M) x, y] + [x, (a • M) y]`.

## The capstone

`clayStatementAtG_GS_F4`, `_E6`, `_E8` are `AbelianGen.clayAtGFromGS_of_abelianGenG` at the three
`AbelianGenG` theorems: `ClayAtGFromGS G` at each group.

DERIVED (module-wide): no numeral beyond the dimensions `26`, `27`, `248` of the representations.
-/

noncomputable section

namespace MassGap.AbelianGenX

open MassGap MassGap.CompReduceG MassGap.AbelianGen
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

/-! ## 1. `F₄` -/

section F4

open MassGap.GaugeF4 MassGap.GaugeG2

variable {R : Type} [CommRing R]

/-- `f4Tri` is homogeneous of degree one in its first vector. DERIVED: `26` the dimension of the
traceless part of `J₃(𝕆)`, `27 − 1`. -/
theorem f4Tri_smul₁ (s c : R) (p q r : Fin 26 → R) :
    f4Tri s (c • p) q r = c * f4Tri s p q r := by
  simp only [f4Tri, octRe3, dot7, dot8, im7, xo, yo, zo, phi3, e3, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_seven, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val]
  ring

/-- `f4Tri` is homogeneous of degree one in its second vector. DERIVED: `26` the dimension of the
traceless part of `J₃(𝕆)`, `27 − 1`. -/
theorem f4Tri_smul₂ (s c : R) (p q r : Fin 26 → R) :
    f4Tri s p (c • q) r = c * f4Tri s p q r := by
  simp only [f4Tri, octRe3, dot7, dot8, im7, xo, yo, zo, phi3, e3, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_seven, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val]
  ring

/-- `f4Tri` is homogeneous of degree one in its third vector. DERIVED: `26` the dimension of the
traceless part of `J₃(𝕆)`, `27 − 1`. -/
theorem f4Tri_smul₃ (s c : R) (p q r : Fin 26 → R) :
    f4Tri s p q (c • r) = c * f4Tri s p q r := by
  simp only [f4Tri, octRe3, dot7, dot8, im7, xo, yo, zo, phi3, e3, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_seven, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val]
  ring

/-- **`lieGen` of `F₄` is closed under real multiples**: Hermitian and antisymmetric by
`AbelianGen`, and the derivation condition at `a • M` is `a` times the one at `M`.

DERIVED: `26` the dimension of the traceless part of `J₃(𝕆)`, `27 − 1`. -/
theorem lieGen_smul_F4 {M : Matrix (Fin 26) (Fin 26) ℂ}
    (h : MassGap.ClayTreeG.GaugeLie.lieGen (G := F4) M) (a : ℝ) :
    MassGap.ClayTreeG.GaugeLie.lieGen (G := F4) (a • M) := by
  obtain ⟨hH, hT, hD⟩ := h
  refine ⟨herm_smul hH a, transpose_smul_eq_neg hT a, fun x => ?_⟩
  have hD' : f4Tri s3C (M *ᵥ x) x x + f4Tri s3C x (M *ᵥ x) x + f4Tri s3C x x (M *ᵥ x) = 0 :=
    hD x
  show f4Tri s3C ((a • M) *ᵥ x) x x + f4Tri s3C x ((a • M) *ᵥ x) x
    + f4Tri s3C x x ((a • M) *ᵥ x) = 0
  rw [real_smul_mulVec, f4Tri_smul₁, f4Tri_smul₂, f4Tri_smul₃]
  linear_combination (a : ℂ) * hD'

/-- **`AbelianGenG F4`** at `H = GaugeF4.cartanF4`: in `lieGen` and nonzero by
`GaugeF4.lieGen_cartanF4`, every real multiple in `lieGen` by `lieGen_smul_F4`.

DERIVED: no numeral. -/
theorem abelianGenG_F4 : AbelianGenG F4 := by
  obtain ⟨hgen, h0⟩ := lieGen_cartanF4
  have hH : cartanF4.IsHermitian := And.left hgen
  exact abelianGenG_of_herm (G := F4) cartanF4 hH h0 fun a => lieGen_smul_F4 hgen a

/-- **`ClayG.clayStatementAtG_GS` at `F₄` with `hab` discharged.** DERIVED: no numeral. -/
theorem clayStatementAtG_GS_F4 : ClayAtGFromGS F4 :=
  clayAtGFromGS_of_abelianGenG abelianGenG_F4

end F4

/-! ## 2. `E₆` -/

section E6

open MassGap.GaugeE6 MassGap.GaugeG2
open MassGap.GaugeF4 (dot7 dot8 im7 octRe3)

variable {R : Type} [CommRing R]

/-- `e6Tri` is homogeneous of degree one in its first vector. DERIVED: `27` the dimension of
`J₃(𝕆)`, `3 + 3·8`. -/
theorem e6Tri_smul₁ (s c : R) (p q r : Fin 27 → R) :
    e6Tri s (c • p) q r = c * e6Tri s p q r := by
  simp only [e6Tri, octRe3, dot7, dot8, im7, xE, yE, zE, phi3, e3, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_seven, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val]
  ring

/-- `e6Tri` is homogeneous of degree one in its second vector. DERIVED: `27` the dimension of
`J₃(𝕆)`, `3 + 3·8`. -/
theorem e6Tri_smul₂ (s c : R) (p q r : Fin 27 → R) :
    e6Tri s p (c • q) r = c * e6Tri s p q r := by
  simp only [e6Tri, octRe3, dot7, dot8, im7, xE, yE, zE, phi3, e3, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_seven, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val]
  ring

/-- `e6Tri` is homogeneous of degree one in its third vector. DERIVED: `27` the dimension of
`J₃(𝕆)`, `3 + 3·8`. -/
theorem e6Tri_smul₃ (s c : R) (p q r : Fin 27 → R) :
    e6Tri s p q (c • r) = c * e6Tri s p q r := by
  simp only [e6Tri, octRe3, dot7, dot8, im7, xE, yE, zE, phi3, e3, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_seven, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val]
  ring

/-- **`lieGen` of `E₆` is closed under real multiples**: Hermitian and traceless by `AbelianGen`,
and the derivation condition at `a • M` is `a` times the one at `M`.

DERIVED: `27` the dimension of `J₃(𝕆)`, `3 + 3·8`. -/
theorem lieGen_smul_E6 {M : Matrix (Fin 27) (Fin 27) ℂ}
    (h : MassGap.ClayTreeG.GaugeLie.lieGen (G := E6) M) (a : ℝ) :
    MassGap.ClayTreeG.GaugeLie.lieGen (G := E6) (a • M) := by
  obtain ⟨hH, hT, hD⟩ := h
  refine ⟨herm_smul hH a, trace_smul_eq_zero hT a, fun x => ?_⟩
  have hD' : e6Tri s2C (M *ᵥ x) x x + e6Tri s2C x (M *ᵥ x) x + e6Tri s2C x x (M *ᵥ x) = 0 :=
    hD x
  show e6Tri s2C ((a • M) *ᵥ x) x x + e6Tri s2C x ((a • M) *ᵥ x) x
    + e6Tri s2C x x ((a • M) *ᵥ x) = 0
  rw [real_smul_mulVec, e6Tri_smul₁, e6Tri_smul₂, e6Tri_smul₃]
  linear_combination (a : ℂ) * hD'

/-- **`AbelianGenG E6`** at `H = GaugeE6.cartanE6`: in `lieGen` and nonzero by
`GaugeE6.lieGen_cartanE6`, every real multiple in `lieGen` by `lieGen_smul_E6`.

DERIVED: no numeral. -/
theorem abelianGenG_E6 : AbelianGenG E6 := by
  obtain ⟨hgen, h0⟩ := lieGen_cartanE6
  have hH : cartanE6.IsHermitian := And.left hgen
  exact abelianGenG_of_herm (G := E6) cartanE6 hH h0 fun a => lieGen_smul_E6 hgen a

/-- **`ClayG.clayStatementAtG_GS` at `E₆` with `hab` discharged.** DERIVED: no numeral. -/
theorem clayStatementAtG_GS_E6 : ClayAtGFromGS E6 :=
  clayAtGFromGS_of_abelianGenG abelianGenG_E6

end E6

/-! ## 3. `E₈` -/

section E8

open MassGap.GaugeE8

variable {R : Type} [CommRing R]

/-- `getN` commutes with scalar multiplication. DERIVED: `248` the dimension of the adjoint
of `E₈`. -/
theorem getN_smul (c : R) (x : Fin 248 → R) (n : ℕ) : getN (c • x) n = c * getN x n := by
  unfold getN
  split
  · simp only [Pi.smul_apply, smul_eq_mul]
  · rw [mul_zero]

/-- `e3N` is homogeneous of degree one in its first vector. DERIVED: `248` the dimension of
the adjoint of `E₈`. -/
theorem e3N_smul₁ (a b d : ℕ) (c : R) (x y z : Fin 248 → R) :
    e3N a b d (c • x) y z = c * e3N a b d x y z := by
  simp only [e3N, getN_smul]
  ring

/-- `e3N` is homogeneous of degree one in its second vector. DERIVED: `248` the dimension of
the adjoint of `E₈`. -/
theorem e3N_smul₂ (a b d : ℕ) (c : R) (x y z : Fin 248 → R) :
    e3N a b d x (c • y) z = c * e3N a b d x y z := by
  simp only [e3N, getN_smul]
  ring

/-- `phiL` is homogeneous of degree one in its first vector. DERIVED: `248` the dimension of
the adjoint of `E₈`. -/
theorem phiL_smul₁ (L : List ℕ) (c : R) (x y z : Fin 248 → R) :
    phiL L (c • x) y z = c * phiL L x y z := by
  induction L with
  | nil => rw [phiL_nil, phiL_nil, mul_zero]
  | cons t L ih =>
    rw [phiL_cons, phiL_cons, ih, e3N_smul₁]
    ring

/-- `phiL` is homogeneous of degree one in its second vector. DERIVED: `248` the dimension of
the adjoint of `E₈`. -/
theorem phiL_smul₂ (L : List ℕ) (c : R) (x y z : Fin 248 → R) :
    phiL L x (c • y) z = c * phiL L x y z := by
  induction L with
  | nil => rw [phiL_nil, phiL_nil, mul_zero]
  | cons t L ih =>
    rw [phiL_cons, phiL_cons, ih, e3N_smul₂]
    ring

/-- `br` is homogeneous of degree one in its first vector. DERIVED: `248` the dimension of
the adjoint of `E₈`. -/
theorem br_smul₁ (c : R) (x y : Fin 248 → R) : br (c • x) y = c • br x y := by
  funext m
  simp only [br, phiE8, Pi.smul_apply, smul_eq_mul]
  exact phiL_smul₁ _ c x y _

/-- `br` is homogeneous of degree one in its second vector. DERIVED: `248` the dimension of
the adjoint of `E₈`. -/
theorem br_smul₂ (c : R) (x y : Fin 248 → R) : br x (c • y) = c • br x y := by
  funext m
  simp only [br, phiE8, Pi.smul_apply, smul_eq_mul]
  exact phiL_smul₂ _ c x y _

/-- **`lieGen` of `E₈` is closed under real multiples**: Hermitian and antisymmetric by
`AbelianGen`, and the derivation condition `M [x, y] = [M x, y] + [x, M y]` is carried to `a • M`
by `br_smul₁`, `br_smul₂`.

DERIVED: `248` the dimension of the adjoint of `E₈`. -/
theorem lieGen_smul_E8 {M : Matrix (Fin 248) (Fin 248) ℂ}
    (h : MassGap.ClayTreeG.GaugeLie.lieGen (G := E8) M) (a : ℝ) :
    MassGap.ClayTreeG.GaugeLie.lieGen (G := E8) (a • M) := by
  obtain ⟨hH, hT, hD⟩ := h
  refine ⟨herm_smul hH a, transpose_smul_eq_neg hT a, fun x y => ?_⟩
  have hD' : M *ᵥ br x y = br (M *ᵥ x) y + br x (M *ᵥ y) := hD x y
  show (a • M) *ᵥ br x y = br ((a • M) *ᵥ x) y + br x ((a • M) *ᵥ y)
  simp only [real_smul_mulVec]
  rw [br_smul₁, br_smul₂, hD', smul_add]

/-- **`AbelianGenG E8`** at `H = GaugeE8.cartanM`: in `lieGen` and nonzero by
`GaugeE8.lieGen_cartanM`, every real multiple in `lieGen` by `lieGen_smul_E8`.

DERIVED: no numeral. -/
theorem abelianGenG_E8 : AbelianGenG E8 := by
  obtain ⟨hgen, h0⟩ := lieGen_cartanM
  have hH : (cartanM).IsHermitian := And.left hgen
  exact abelianGenG_of_herm (G := E8) cartanM hH h0 fun a => lieGen_smul_E8 hgen a

/-- **`ClayG.clayStatementAtG_GS` at `E₈` with `hab` discharged.** DERIVED: no numeral. -/
theorem clayStatementAtG_GS_E8 : ClayAtGFromGS E8 :=
  clayAtGFromGS_of_abelianGenG abelianGenG_E8

end E8

end MassGap.AbelianGenX

end

#print axioms MassGap.AbelianGenX.real_smul_vec
#print axioms MassGap.AbelianGenX.real_smul_mulVec
#print axioms MassGap.AbelianGenX.f4Tri_smul₁
#print axioms MassGap.AbelianGenX.f4Tri_smul₂
#print axioms MassGap.AbelianGenX.f4Tri_smul₃
#print axioms MassGap.AbelianGenX.lieGen_smul_F4
#print axioms MassGap.AbelianGenX.abelianGenG_F4
#print axioms MassGap.AbelianGenX.clayStatementAtG_GS_F4
#print axioms MassGap.AbelianGenX.e6Tri_smul₁
#print axioms MassGap.AbelianGenX.e6Tri_smul₂
#print axioms MassGap.AbelianGenX.e6Tri_smul₃
#print axioms MassGap.AbelianGenX.lieGen_smul_E6
#print axioms MassGap.AbelianGenX.abelianGenG_E6
#print axioms MassGap.AbelianGenX.clayStatementAtG_GS_E6
#print axioms MassGap.AbelianGenX.getN_smul
#print axioms MassGap.AbelianGenX.e3N_smul₁
#print axioms MassGap.AbelianGenX.e3N_smul₂
#print axioms MassGap.AbelianGenX.phiL_smul₁
#print axioms MassGap.AbelianGenX.phiL_smul₂
#print axioms MassGap.AbelianGenX.br_smul₁
#print axioms MassGap.AbelianGenX.br_smul₂
#print axioms MassGap.AbelianGenX.lieGen_smul_E8
#print axioms MassGap.AbelianGenX.abelianGenG_E8
#print axioms MassGap.AbelianGenX.clayStatementAtG_GS_E8
