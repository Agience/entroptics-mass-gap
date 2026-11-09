import Mathlib
import MassGap.ApertureCount

/-!
# MassGap.ModeHyper — per-mode hypercontractivity of a finite chaos

`ApertureCount.ApertureCountAt` carries H1: every unit eigenvector's mode of the flowed screen has
`ν(e^{2p}) ≤ ((2p)!)^{wickIx j} (C λ)^p` with one `C`. In the free theory a flowed mode of a channel of
canonical dimension `d_j` is a polynomial of degree `q ≤ d_j / 2` in the field (a finite chaos). This module
proves the moment bound of a finite chaos on the compact product of two-point spins, uniformly in the number
of spins, and shows that it is H1's form with a structural constant. Declarations are in the namespace
`MassGap.ModeHyper`.

## 1. The cube and its chaos (proved)

* `avg m g = 2^{−m} ∑_x g x`, the uniform average on `{±1}^m` (`ApertureCount.cubeState` as a plain sum);
  `avg_succ` splits off the first spin.
* `Deg m q f`: `f` is a multilinear polynomial of degree at most `q` in the `m` spins, stated by recursion on
  the first spin: `f(b, x) = sgn(b) D(x) + E(x)` with `D` of degree `q − 1` (zero when `q = 0`) and `E` of
  degree `q`. `deg_const`, `deg_add`, `deg_smul`, `deg_sum`: the degree-`q` functions form a linear space, so
  every linear combination of degree-`q` screen readings is of degree `q`, whatever the coefficients.

## 2. The two-point inequality and Bonami's bound (proved)

* `choose_two_mul_le`: `C(2p, 2j) ≤ C(p, j) (2p − 1)^j` for `j ≤ p`.
* `two_point`: `((−d + e)^{2p} + (d + e)^{2p}) / 2 ≤ ((2p − 1) d² + e²)^p` (the even binomial terms compared
  one by one).
* `avg_mink`: Minkowski's inequality for the cube average in power form.
* `bonami`: every degree-`q` function on `{±1}^m` has
  `avg(f^{2p}) ≤ ((2p − 1)^q)^p avg(f²)^p` for `p ≥ 1`, for every `m`. The proof is the induction on the spins:
  the two-point inequality on the first spin, then Minkowski in `L^p` of the rest. This is the
  hypercontractive bound `‖f‖_{2p} ≤ (2p − 1)^{q/2} ‖f‖₂` of a chaos of order `q`, with Nelson's constant.

## 3. H1's form (proved)

* `wick_const`: `((2p − 1)^q)^p ≤ ((2p)!)^w (e^{2w})^p` when `q ≤ 2w` (`n^n ≤ n! eⁿ`,
  `Real.pow_div_factorial_le_exp`).
* `wick_covers`: a degree `q ≤ d_j / 2` has `q ≤ 2 wickIx j`, `wickIx j = ⌈d_j / 4⌉` (`ZoomFree.wickIx`).
* `state_unitEig_sq`: a unit eigenvector `v` of a screen's Gram matrix at `λ` has
  `ν((∑_y v y • F_y)²) = λ`.
* `cube_H1`: for a screen of degree-`q` readings on the cube, `q ≤ 2w`, every unit eigenvector's mode has
  `ν(e^{2p}) ≤ ((2p)!)^w (e^{2w} λ)^p`, at every order, every screen size and every number of spins:
  H1's statement with `C = e^{2w}`. `cube_H1_channel`: at `w = wickIx j` for a channel of dimension `d_j`
  and degree `q ≤ d_j / 2`.

## 4. The load-bearing test (proved)

`rsum m x = ∑_i sgn(xᵢ)` is of degree `1` (`deg_rsum`) with `avg(rsum²) = m` (`avg_rsum_sq`) and
`avg(rsum^{2m}) ≥ m^{2m} / 2^m` (the all-`+1` spin, `avg_rsum_pow_ge`).

* `wick_needed`: no `C` has `avg(rsum^{2p}) ≤ C^p avg(rsum²)^p` for every `m` and `p` (at `p = m > 2|C|`
  the ratio is at least `(m/2)^m`). So H1 with Wick exponent `0` fails already in degree `1`.
* `rsum_H1`: with the Wick factor at exponent `1` the bound holds with `C = e²` for every `m` and `p`.

## 5. What is not proved here

The cube is a finite product of compact two-point spins. The Gaussian free field is the moment limit of
normalized spin sums (`K^{−1/2} ∑_{r<K} ε_r → N(0, 1)` in every moment), a polynomial of degree `q` in those
sums is of degree at most `q` on the cube (`ε² = 1`), and the bound of `bonami` is uniform in `m`; the
passage to the limit (the moment central limit theorem) is not formalized, so the Gaussian statement is the
limit of `bonami`, argued, not proved. H1 itself is a statement about `ν_k` on the compact `SU(N)` link
configurations, where the modes are not finite chaos.

`h1_of_herbst` is the reduction for the interacting state: a moment bound of Herbst form
`ν(e^{2p}) ≤ (2p)^p (κ L)^p` (what a log-Sobolev inequality `Ent_ν(f²) ≤ κ ν(|∇f|²)` gives for a centred
observable with `|∇e|² ≤ L`; the inequality and the Herbst argument are cited, not proved, and the log-Sobolev
inequality is not stated as a Lean definition) and a gradient-to-variance ratio
`L ≤ R λ` give H1's form at every Wick exponent `w ≥ 1`, `C = e² κ R`. The Bakry–Émery curvature of
`SU(N)` with the Wilson potential is `N/4 − β H` (`CondGap.beConst`); it is positive only for
`β < N/(4H)` (`CondGap.beConst_pos_iff`) and tends to `−∞` as `β → ∞` (`CondGap.beConst_tendsto_atBot`), so
the log-Sobolev route covers the strong-coupling window and not the couplings `βs k → ∞` of the zoom.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the signs, the empty cube and the degree of a constant; `1` the unit, the first
order, the degree of a spin and the floor `p ≥ 1`; `2` the two values of a spin, the even powers, the squares
and the base of the cube's count; `2p − 1` Nelson's constant of order `2p` (from the binomial comparison);
`e^{2w}` the constant of H1 (from `n^n ≤ n! eⁿ` and `q ≤ 2w`); `e²` its value at `w = 1`; `3`, `4` as in
`ZoomFree.wickIx`; `C`, `κ`, `R`, `L` universally quantified.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ModeHyper

open Finset
open MassGap MassGap.ApertureCount MassGap.ApertureModes MassGap.ZoomFree MassGap.MultiScaleAll

/-! ## 1. The cube and its chaos -/

section Cube

/-- **The uniform average on the cube** `{±1}^m`. DERIVED: `2` the two values of a spin. -/
def avg (m : ℕ) (g : (Fin m → Bool) → ℝ) : ℝ := (∑ x, g x) / 2 ^ m

/-- **Splitting off the first spin**. DERIVED: `2` the two values of a spin; `1` the first spin. -/
theorem avg_succ (m : ℕ) (g : (Fin (m + 1) → Bool) → ℝ) :
    avg (m + 1) g = avg m (fun x => (g (Fin.cons true x) + g (Fin.cons false x)) / 2) := by
  have hsplit : ∑ x : Fin (m + 1) → Bool, g x = ∑ y : Bool × (Fin m → Bool), g (Fin.cons y.1 y.2) :=
    (Fintype.sum_equiv (Fin.consEquiv fun _ => Bool) _ _ fun _ => rfl).symm
  unfold avg
  rw [hsplit, Fintype.sum_prod_type, Fintype.sum_bool]
  dsimp only
  rw [add_div, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [pow_succ]
  ring

/-- DERIVED: no numeral. -/
theorem avg_mono {m : ℕ} {g h : (Fin m → Bool) → ℝ} (hgh : ∀ x, g x ≤ h x) : avg m g ≤ avg m h :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => hgh x) (by positivity)

/-- DERIVED: `0` the sign. -/
theorem avg_nonneg {m : ℕ} {g : (Fin m → Bool) → ℝ} (hg : ∀ x, 0 ≤ g x) : 0 ≤ avg m g :=
  div_nonneg (Finset.sum_nonneg fun x _ => hg x) (by positivity)

/-- DERIVED: no numeral. -/
theorem avg_add (m : ℕ) (g h : (Fin m → Bool) → ℝ) :
    avg m (fun x => g x + h x) = avg m g + avg m h := by
  unfold avg
  rw [Finset.sum_add_distrib, add_div]

/-- DERIVED: no numeral. -/
theorem avg_mul (m : ℕ) (c : ℝ) (g : (Fin m → Bool) → ℝ) : avg m (fun x => c * g x) = c * avg m g := by
  unfold avg
  rw [← Finset.mul_sum, mul_div_assoc]

/-- DERIVED: `2` the base of the cube's count. -/
theorem avg_const (m : ℕ) (c : ℝ) : avg m (fun _ => c) = c := by
  unfold avg
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  push_cast
  rw [mul_div_cancel_left₀ _ (by positivity)]

/-- **The cube state is the cube average**. DERIVED: no numeral. -/
theorem cubeState_eq (m : ℕ) (g : C(Fin m → Bool, ℝ)) : cubeState m g = avg m g := rfl

/-- **A multilinear polynomial of degree at most `q` in `m` spins**, by recursion on the first spin:
`f(b, x) = sgn(b) D(x) + E(x)` with `D` of degree `q − 1` (zero when `q = 0`) and `E` of degree `q`.
DERIVED: `0` the empty cube and the degree of a constant; `1` the degree of a spin. -/
def Deg : (m : ℕ) → ℕ → ((Fin m → Bool) → ℝ) → Prop
  | 0, _, _ => True
  | m + 1, q, f => ∃ D E : (Fin m → Bool) → ℝ, (q = 0 → ∀ x, D x = 0) ∧ Deg m (q - 1) D ∧ Deg m q E ∧
      ∀ b x, f (Fin.cons b x) = sgnB b * D x + E x

/-- DERIVED: `0`, `1` as in `Deg`. -/
theorem deg_succ_iff {m q : ℕ} {f : (Fin (m + 1) → Bool) → ℝ} :
    Deg (m + 1) q f ↔ ∃ D E : (Fin m → Bool) → ℝ, (q = 0 → ∀ x, D x = 0) ∧ Deg m (q - 1) D ∧
      Deg m q E ∧ ∀ b x, f (Fin.cons b x) = sgnB b * D x + E x :=
  Iff.rfl

/-- **A constant is of every degree**. DERIVED: `0` the zero coefficient. -/
theorem deg_const : ∀ (m q : ℕ) (c : ℝ), Deg m q (fun _ => c)
  | 0, _, _ => trivial
  | m + 1, q, c => deg_succ_iff.2 ⟨fun _ => 0, fun _ => c, fun _ _ => rfl, deg_const m (q - 1) 0,
      deg_const m q c, fun b x => by simp⟩

/-- **The degree-`q` functions are closed under sums**. DERIVED: `0` as in `Deg`. -/
theorem deg_add : ∀ (m q : ℕ) (f g : (Fin m → Bool) → ℝ), Deg m q f → Deg m q g →
    Deg m q (fun x => f x + g x)
  | 0, _, _, _, _, _ => trivial
  | m + 1, q, f, g, hf, hg => by
    obtain ⟨D₁, E₁, h₀₁, hD₁, hE₁, hf₁⟩ := deg_succ_iff.1 hf
    obtain ⟨D₂, E₂, h₀₂, hD₂, hE₂, hf₂⟩ := deg_succ_iff.1 hg
    refine deg_succ_iff.2 ⟨fun x => D₁ x + D₂ x, fun x => E₁ x + E₂ x, fun hq x => ?_,
      deg_add m (q - 1) D₁ D₂ hD₁ hD₂, deg_add m q E₁ E₂ hE₁ hE₂, fun b x => ?_⟩
    · simp only [h₀₁ hq x, h₀₂ hq x, add_zero]
    · show f (Fin.cons b x) + g (Fin.cons b x) = _
      rw [hf₁, hf₂]
      ring

/-- **The degree-`q` functions are closed under scaling**. DERIVED: `0` as in `Deg`. -/
theorem deg_smul : ∀ (m q : ℕ) (c : ℝ) (f : (Fin m → Bool) → ℝ), Deg m q f → Deg m q (fun x => c * f x)
  | 0, _, _, _, _ => trivial
  | m + 1, q, c, f, hf => by
    obtain ⟨D, E, h₀, hD, hE, hfe⟩ := deg_succ_iff.1 hf
    refine deg_succ_iff.2 ⟨fun x => c * D x, fun x => c * E x, fun hq x => ?_,
      deg_smul m (q - 1) c D hD, deg_smul m q c E hE, fun b x => ?_⟩
    · simp only [h₀ hq x, mul_zero]
    · show c * f (Fin.cons b x) = _
      rw [hfe]
      ring

/-- **Every linear combination of degree-`q` functions is of degree `q`**. DERIVED: no numeral. -/
theorem deg_sum {m q : ℕ} {ι : Type*} (s : Finset ι) (v : ι → ℝ) (F : ι → (Fin m → Bool) → ℝ)
    (hF : ∀ y, Deg m q (F y)) : Deg m q (fun x => ∑ y ∈ s, v y * F y x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact deg_const m q 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact deg_add m q _ _ (deg_smul m q (v a) (F a) (hF a)) ih

end Cube

/-! ## 2. The two-point inequality and Bonami's bound -/

section Bonami

/-- **The binomial coefficients of order `2p` against those of order `p`**: `C(2p, 2j) ≤ C(p, j) (2p − 1)^j`
for `j ≤ p`. DERIVED: `2p − 1` the constant; `1`, `2` the index steps. -/
theorem choose_two_mul_le (p : ℕ) :
    ∀ j : ℕ, j ≤ p → ((2 * p).choose (2 * j) : ℝ) ≤ (p.choose j : ℝ) * (2 * (p : ℝ) - 1) ^ j := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hj' : j ≤ p := by omega
    have ih' := ih hj'
    have h1 := Nat.choose_succ_right_eq (2 * p) (2 * j)
    have h2 := Nat.choose_succ_right_eq (2 * p) (2 * j + 1)
    have h3 := Nat.choose_succ_right_eq p j
    have e1 : ((2 * p - 2 * j : ℕ) : ℝ) = 2 * p - 2 * j := by
      rw [Nat.cast_sub (by omega)]; push_cast; try ring
    have e2 : ((2 * p - (2 * j + 1) : ℕ) : ℝ) = 2 * p - 2 * j - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; try ring
    have e3 : ((p - j : ℕ) : ℝ) = p - j := by rw [Nat.cast_sub hj']
    have r1 : ((2 * p).choose (2 * j + 1) : ℝ) * (2 * j + 1)
        = ((2 * p).choose (2 * j) : ℝ) * (2 * p - 2 * j) := by
      rw [← e1]; exact_mod_cast h1
    have r2 : ((2 * p).choose (2 * j + 1 + 1) : ℝ) * (2 * j + 1 + 1)
        = ((2 * p).choose (2 * j + 1) : ℝ) * (2 * p - 2 * j - 1) := by
      rw [← e2]; exact_mod_cast h2
    have r3 : (p.choose (j + 1) : ℝ) * (j + 1) = (p.choose j : ℝ) * (p - j) := by
      rw [← e3]; exact_mod_cast h3
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
    set a := ((2 * p).choose (2 * j) : ℝ)
    set c := ((2 * p).choose (2 * j + 1) : ℝ)
    set a' := ((2 * p).choose (2 * j + 1 + 1) : ℝ)
    set b := (p.choose j : ℝ)
    set b' := (p.choose (j + 1) : ℝ)
    set M := 2 * (p : ℝ) - 1 with hM
    have hpj : (j : ℝ) + 1 ≤ p := by exact_mod_cast hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hM1 : 1 ≤ M := by rw [hM]; linarith
    have hb' : 0 ≤ b' := Nat.cast_nonneg _
    have hMj : 0 ≤ M ^ j := pow_nonneg (by linarith) j
    have hodd : 0 ≤ 2 * (p : ℝ) - 2 * j - 1 := by linarith
    have hev : 0 ≤ (2 * (p : ℝ) - 2 * j) * (2 * p - 2 * j - 1) := by
      apply mul_nonneg <;> linarith
    have hle : 2 * (p : ℝ) - 2 * j - 1 ≤ M * (2 * j + 1) := by
      rw [hM]; nlinarith [mul_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p) hj0]
    have hpos : (0 : ℝ) < (2 * j + 1 + 1) * (2 * j + 1) := by positivity
    have key : a' * ((2 * j + 1 + 1) * (2 * j + 1)) ≤ b' * M ^ (j + 1) * ((2 * j + 1 + 1) * (2 * j + 1)) :=
      calc a' * ((2 * j + 1 + 1) * (2 * j + 1))
          = a * ((2 * p - 2 * j) * (2 * p - 2 * j - 1)) := by
            linear_combination (2 * (j : ℝ) + 1) * r2 + (2 * (p : ℝ) - 2 * j - 1) * r1
        _ ≤ b * M ^ j * ((2 * p - 2 * j) * (2 * p - 2 * j - 1)) := mul_le_mul_of_nonneg_right ih' hev
        _ = 2 * b' * (j + 1) * M ^ j * (2 * p - 2 * j - 1) := by
            linear_combination (-(2 * M ^ j * (2 * (p : ℝ) - 2 * j - 1))) * r3
        _ ≤ 2 * b' * (j + 1) * M ^ j * (M * (2 * j + 1)) :=
            mul_le_mul_of_nonneg_left hle
              (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb') (by linarith)) hMj)
        _ = b' * M ^ (j + 1) * ((2 * j + 1 + 1) * (2 * j + 1)) := by ring
    exact le_of_mul_le_mul_right key hpos

/-- **The even and odd terms of a sum of order `2p`**. DERIVED: `1`, `2` the parity split. -/
theorem sum_range_even_odd (g : ℕ → ℝ) (p : ℕ) :
    ∑ k ∈ range (2 * p + 1), g k = ∑ j ∈ range (p + 1), g (2 * j) + ∑ j ∈ range p, g (2 * j + 1) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [show 2 * (p + 1) + 1 = 2 * p + 1 + 1 + 1 by ring, Finset.sum_range_succ g (2 * p + 1 + 1),
      Finset.sum_range_succ g (2 * p + 1), ih, Finset.sum_range_succ (fun j => g (2 * j)) (p + 1),
      Finset.sum_range_succ (fun j => g (2 * j + 1)) p, show 2 * p + 1 + 1 = 2 * (p + 1) by ring]
    ring

/-- **The two-point inequality**: `((−d + e)^{2p} + (d + e)^{2p}) / 2 ≤ ((2p − 1) d² + e²)^p`.
DERIVED: `2` the two values of a spin and the squares; `2p − 1` the constant (`choose_two_mul_le`). -/
theorem two_point (d e : ℝ) (p : ℕ) :
    ((-d + e) ^ (2 * p) + (d + e) ^ (2 * p)) / 2 ≤ ((2 * (p : ℝ) - 1) * d ^ 2 + e ^ 2) ^ p := by
  set t : ℕ → ℝ := fun k => ((-d) ^ k + d ^ k) * e ^ (2 * p - k) * ((2 * p).choose k : ℝ) with ht
  have hsum : (-d + e) ^ (2 * p) + (d + e) ^ (2 * p) = ∑ k ∈ range (2 * p + 1), t k := by
    rw [add_pow, add_pow, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by simp only [ht]; ring
  have hodd : ∑ j ∈ range p, t (2 * j + 1) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      simp only [ht]
      rw [Odd.neg_pow ⟨j, rfl⟩]
      ring
  have hev : ∀ j, t (2 * j) = 2 * (d ^ (2 * j) * e ^ (2 * p - 2 * j) * ((2 * p).choose (2 * j) : ℝ)) := by
    intro j
    simp only [ht]
    rw [Even.neg_pow (even_two_mul j)]
    ring
  rw [hsum, sum_range_even_odd t p, hodd, add_zero]
  simp only [hev]
  rw [← Finset.mul_sum, mul_div_cancel_left₀ _ (two_ne_zero), add_pow]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjp : j ≤ p := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hexp : 2 * p - 2 * j = 2 * (p - j) := by omega
  rw [mul_pow, ← pow_mul, ← pow_mul, hexp]
  have h0 : 0 ≤ d ^ (2 * j) * e ^ (2 * (p - j)) :=
    mul_nonneg ((even_two_mul j).pow_nonneg _) ((even_two_mul _).pow_nonneg _)
  calc d ^ (2 * j) * e ^ (2 * (p - j)) * ((2 * p).choose (2 * j) : ℝ)
      ≤ d ^ (2 * j) * e ^ (2 * (p - j)) * ((p.choose j : ℝ) * (2 * (p : ℝ) - 1) ^ j) :=
        mul_le_mul_of_nonneg_left (choose_two_mul_le p j hjp) h0
    _ = (2 * (p : ℝ) - 1) ^ j * d ^ (2 * j) * e ^ (2 * (p - j)) * (p.choose j : ℝ) := by ring

/-- **Minkowski on the cube, in power form**: `avg(u^p) ≤ X^p`, `avg(v^p) ≤ Y^p` give
`avg((u + v)^p) ≤ (X + Y)^p`. DERIVED: `1` the floor `p ≥ 1`; `0` the signs. -/
theorem avg_mink {m p : ℕ} (hp : 1 ≤ p) {u v : (Fin m → Bool) → ℝ} (hu : ∀ x, 0 ≤ u x)
    (hv : ∀ x, 0 ≤ v x) {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hXu : avg m (fun x => u x ^ p) ≤ X ^ p) (hYv : avg m (fun x => v x ^ p) ≤ Y ^ p) :
    avg m (fun x => (u x + v x) ^ p) ≤ (X + Y) ^ p := by
  have hp0 : p ≠ 0 := by omega
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hc : (0 : ℝ) < 2 ^ m := by positivity
  have hmk := Real.Lp_add_le_of_nonneg (Finset.univ : Finset (Fin m → Bool)) (f := u) (g := v) hpR
    (fun x _ => hu x) (fun x _ => hv x)
  simp only [Real.rpow_natCast, one_div] at hmk
  have hSu : ∑ x, u x ^ p ≤ 2 ^ m * X ^ p := by
    unfold avg at hXu; rwa [div_le_iff₀ hc, mul_comm] at hXu
  have hSv : ∑ x, v x ^ p ≤ 2 ^ m * Y ^ p := by
    unfold avg at hYv; rwa [div_le_iff₀ hc, mul_comm] at hYv
  have hroot : ∀ {S Z : ℝ}, 0 ≤ S → 0 ≤ Z → S ≤ 2 ^ m * Z ^ p →
      S ^ ((p : ℝ)⁻¹) ≤ ((2 : ℝ) ^ m) ^ ((p : ℝ)⁻¹) * Z := by
    intro S Z hS hZ h
    calc S ^ ((p : ℝ)⁻¹) ≤ (2 ^ m * Z ^ p) ^ ((p : ℝ)⁻¹) :=
          Real.rpow_le_rpow hS h (by positivity)
      _ = ((2 : ℝ) ^ m) ^ ((p : ℝ)⁻¹) * Z := by
          rw [Real.mul_rpow hc.le (pow_nonneg hZ p), Real.pow_rpow_inv_natCast hZ hp0]
  have hS0 : 0 ≤ ∑ x, (u x + v x) ^ p := Finset.sum_nonneg fun x _ => pow_nonneg (add_nonneg (hu x) (hv x)) p
  have hbound : (∑ x, (u x + v x) ^ p) ^ ((p : ℝ)⁻¹) ≤ ((2 : ℝ) ^ m) ^ ((p : ℝ)⁻¹) * (X + Y) := by
    refine hmk.trans ?_
    rw [mul_add]
    exact add_le_add (hroot (Finset.sum_nonneg fun x _ => pow_nonneg (hu x) p) hX hSu)
      (hroot (Finset.sum_nonneg fun x _ => pow_nonneg (hv x) p) hY hSv)
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hS0 _) hbound p
  rw [Real.rpow_inv_natCast_pow hS0 hp0, mul_pow, Real.rpow_inv_natCast_pow hc.le hp0] at hpow
  unfold avg
  rw [div_le_iff₀ hc, mul_comm]
  exact hpow

/-- **Bonami's bound, uniform in the number of spins**: a degree-`q` function on `{±1}^m` has
`avg(f^{2p}) ≤ ((2p − 1)^q)^p avg(f²)^p` for `p ≥ 1`. DERIVED: `2p − 1` the constant; `2` the even powers;
`1` the floor. -/
theorem bonami : ∀ (m q : ℕ) (f : (Fin m → Bool) → ℝ), Deg m q f → ∀ p : ℕ, 1 ≤ p →
    avg m (fun x => f x ^ (2 * p)) ≤ ((2 * (p : ℝ) - 1) ^ q) ^ p * avg m (fun x => f x ^ 2) ^ p := by
  intro m
  induction m with
  | zero =>
    intro q f _ p hp
    have hM : (1 : ℝ) ≤ ((2 * (p : ℝ) - 1) ^ q) ^ p := by
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp
      exact one_le_pow₀ (one_le_pow₀ (by linarith))
    simp only [avg, Fintype.sum_unique, pow_zero, div_one]
    rw [pow_mul]
    exact le_mul_of_one_le_left (pow_nonneg (sq_nonneg _) _) hM
  | succ m ih =>
    intro q f hf p hp
    obtain ⟨D, E, hD0, hD, hE, hfe⟩ := deg_succ_iff.1 hf
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hM0 : (0 : ℝ) ≤ 2 * (p : ℝ) - 1 := by linarith
    have h2 : avg (m + 1) (fun x => f x ^ 2) = avg m (fun x => D x ^ 2) + avg m (fun x => E x ^ 2) := by
      rw [avg_succ, ← avg_add]
      simp only [hfe, sgnB_true, sgnB_false, neg_one_mul, one_mul]
      congr 1
      funext x
      ring
    have hpt : ∀ x, (f (Fin.cons true x) ^ (2 * p) + f (Fin.cons false x) ^ (2 * p)) / 2
        ≤ ((2 * (p : ℝ) - 1) * D x ^ 2 + E x ^ 2) ^ p := by
      intro x
      rw [hfe, hfe, sgnB_true, sgnB_false, neg_one_mul, one_mul]
      exact two_point (D x) (E x) p
    rw [h2, avg_succ]
    refine (avg_mono hpt).trans ?_
    set δ := avg m (fun x => D x ^ 2) with hδ
    set ε := avg m (fun x => E x ^ 2) with hε
    have hδ0 : 0 ≤ δ := avg_nonneg fun x => sq_nonneg _
    have hε0 : 0 ≤ ε := avg_nonneg fun x => sq_nonneg _
    have hMq : 0 ≤ (2 * (p : ℝ) - 1) ^ q := pow_nonneg hM0 q
    have hEb : avg m (fun x => (E x ^ 2) ^ p) ≤ ((2 * (p : ℝ) - 1) ^ q * ε) ^ p := by
      have := ih q E hE p hp
      simp only [← pow_mul]
      rw [mul_pow]
      exact this
    have hDb : avg m (fun x => ((2 * (p : ℝ) - 1) * D x ^ 2) ^ p) ≤ ((2 * (p : ℝ) - 1) ^ q * δ) ^ p := by
      cases q with
      | zero =>
        have hz : ∀ x, D x = 0 := hD0 rfl
        simp only [hz]
        rw [avg_const]
        have h00 : ((2 * (p : ℝ) - 1) * 0 ^ 2) ^ p = 0 := by
          rw [zero_pow two_ne_zero, mul_zero, zero_pow (by omega)]
        rw [h00]
        exact pow_nonneg (mul_nonneg hMq hδ0) p
      | succ q' =>
        have hD' : Deg m q' D := by simpa using hD
        have := ih q' D hD' p hp
        have hfun : (fun x => ((2 * (p : ℝ) - 1) * D x ^ 2) ^ p)
            = fun x => (2 * (p : ℝ) - 1) ^ p * D x ^ (2 * p) := by
          funext x; rw [mul_pow, ← pow_mul]
        rw [hfun, avg_mul]
        calc (2 * (p : ℝ) - 1) ^ p * avg m (fun x => D x ^ (2 * p))
            ≤ (2 * (p : ℝ) - 1) ^ p * (((2 * (p : ℝ) - 1) ^ q') ^ p * δ ^ p) :=
              mul_le_mul_of_nonneg_left this (pow_nonneg hM0 p)
          _ = ((2 * (p : ℝ) - 1) ^ (q' + 1) * δ) ^ p := by
              generalize (2 * (p : ℝ) - 1) = M
              ring
    have hmk := avg_mink hp (u := fun x => (2 * (p : ℝ) - 1) * D x ^ 2) (v := fun x => E x ^ 2)
      (fun x => mul_nonneg hM0 (sq_nonneg _)) (fun x => sq_nonneg _) (mul_nonneg hMq hδ0)
      (mul_nonneg hMq hε0) hDb hEb
    refine hmk.trans_eq ?_
    rw [← mul_add, mul_pow]

end Bonami

/-! ## 3. H1's form -/

section HOne

/-- **Nelson's constant inside H1's Wick factor**: `((2p − 1)^q)^p ≤ ((2p)!)^w (e^{2w})^p` when `q ≤ 2w`.
DERIVED: `2` the even order and the exponent of `e`; `1` the floor. -/
theorem wick_const {p q w : ℕ} (hp : 1 ≤ p) (hqw : q ≤ 2 * w) :
    ((2 * (p : ℝ) - 1) ^ q) ^ p ≤ ((2 * p).factorial : ℝ) ^ w * Real.exp (2 * w) ^ p := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hM1 : (1 : ℝ) ≤ 2 * p - 1 := by linarith
  have hfac : (0 : ℝ) < ((2 * p).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hn : ((2 * p : ℕ) : ℝ) ^ (2 * p) ≤ ((2 * p).factorial : ℝ) * Real.exp ((2 * p : ℕ) : ℝ) := by
    have := Real.pow_div_factorial_le_exp (x := ((2 * p : ℕ) : ℝ)) (Nat.cast_nonneg _) (2 * p)
    rw [div_le_iff₀ hfac] at this
    exact this.trans_eq (mul_comm _ _)
  push_cast at hn
  calc ((2 * (p : ℝ) - 1) ^ q) ^ p ≤ ((2 * (p : ℝ) - 1) ^ (2 * w)) ^ p :=
        pow_le_pow_left₀ (pow_nonneg (by linarith) q) (pow_le_pow_right₀ hM1 hqw) p
    _ = ((2 * (p : ℝ) - 1) ^ (2 * p)) ^ w := by ring
    _ ≤ ((2 * (p : ℝ)) ^ (2 * p)) ^ w :=
        pow_le_pow_left₀ (pow_nonneg (by linarith) _) (pow_le_pow_left₀ (by linarith) (by linarith) _) w
    _ ≤ (((2 * p).factorial : ℝ) * Real.exp (2 * p)) ^ w := pow_le_pow_left₀ (by positivity) hn w
    _ = ((2 * p).factorial : ℝ) ^ w * Real.exp (2 * w) ^ p := by
        rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 2
        ring

/-- **A degree `q ≤ d_j / 2` is covered by the Wick index**: `q ≤ 2 wickIx j`, `wickIx j = ⌈d_j / 4⌉`.
DERIVED: `2` the factor; `3`, `4` as in `wickIx`. -/
theorem wick_covers (j : MIx) {q : ℕ} (hq : q ≤ mDim j / 2) : q ≤ 2 * wickIx j := by
  unfold wickIx
  omega

/-- **A unit eigenvector's mode has its eigenvalue as second moment**: `ν((∑_y v y • F_y)²) = λ`.
DERIVED: `2` the square; `1` the unit norm. -/
theorem state_unitEig_sq {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : MassGap.DLRLimit.State X)
    {ι : Type*} [Fintype ι] (F : ι → C(X, ℝ)) {lam : ℝ} {v : ι → ℝ} (hv : IsUnitEig (gram ν F) lam v) :
    ν ((∑ y, v y • F y) ^ 2) = lam := by
  obtain ⟨h1, h2⟩ := hv
  have hrow : ∀ y, ∑ z, ν (F y * F z) * v z = lam * v y := fun y => by
    have := congrFun h2 y
    simpa only [Matrix.mulVec, dotProduct, gram, Pi.smul_apply, smul_eq_mul] using this
  rw [sq, Finset.sum_mul_sum]
  simp only [smul_mul_smul_comm, ν.map_sum, ν.map_smul]
  calc ∑ y, ∑ z, v y * v z * ν (F y * F z) = ∑ y, v y * ∑ z, ν (F y * F z) * v z := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
    _ = ∑ y, lam * v y ^ 2 := Finset.sum_congr rfl fun y _ => by rw [hrow]; ring
    _ = lam := by rw [← Finset.mul_sum, h1, mul_one]

/-- **H1 on the cube**: for a screen of degree-`q` readings, `q ≤ 2w`, every unit eigenvector's mode has
`ν(e^{2p}) ≤ ((2p)!)^w (e^{2w} λ)^p`, at every order, screen size and number of spins.
DERIVED: `e^{2w}` the constant (`wick_const`); `2` the even power. -/
theorem cube_H1 {m : ℕ} {ι : Type*} [Fintype ι] (F : ι → C(Fin m → Bool, ℝ)) {q w : ℕ}
    (hqw : q ≤ 2 * w) (hF : ∀ y, Deg m q (F y)) (p : ℕ) {lam : ℝ} {v : ι → ℝ}
    (hv : IsUnitEig (gram (cubeState m) F) lam v) :
    cubeState m ((∑ y, v y • F y) ^ (2 * p)) ≤ ((2 * p).factorial : ℝ) ^ w * (Real.exp (2 * w) * lam) ^ p := by
  set G := ∑ y, v y • F y with hG
  have hcoe : ∀ x, G x = ∑ y, v y * F y x := fun x => by
    simp only [hG, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  have hdeg : Deg m q (fun x => G x) := by
    have := deg_sum Finset.univ v (fun y => (F y : (Fin m → Bool) → ℝ)) hF
    simpa only [← hcoe] using this
  have hvar := state_unitEig_sq (cubeState m) F hv
  rw [← hG] at hvar
  have hlam : 0 ≤ lam := by
    rw [← hvar]
    exact (cubeState m).nonneg _ fun x => by simp only [ContinuousMap.pow_apply]; positivity
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    simp only [mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, mul_one]
    exact le_of_eq (cubeState m).map_one
  have hb := bonami m q (fun x => G x) hdeg p hp
  have h2 : cubeState m (G ^ 2) = avg m (fun x => G x ^ 2) := by
    rw [cubeState_eq]; rfl
  have h2p : cubeState m (G ^ (2 * p)) = avg m (fun x => G x ^ (2 * p)) := by
    rw [cubeState_eq]; rfl
  rw [h2p]
  rw [← h2, hvar] at hb
  calc avg m (fun x => G x ^ (2 * p)) ≤ ((2 * (p : ℝ) - 1) ^ q) ^ p * lam ^ p := hb
    _ ≤ ((2 * p).factorial : ℝ) ^ w * Real.exp (2 * w) ^ p * lam ^ p :=
        mul_le_mul_of_nonneg_right (wick_const hp hqw) (pow_nonneg hlam p)
    _ = ((2 * p).factorial : ℝ) ^ w * (Real.exp (2 * w) * lam) ^ p := by ring

/-- **H1 on the cube at a channel's Wick index**: readings of degree `q ≤ d_j / 2` meet H1's statement at
`wickIx j` with `C = e^{2 wickIx j}`. DERIVED: as in `cube_H1`, `wick_covers`. -/
theorem cube_H1_channel (j : MIx) {m : ℕ} {ι : Type*} [Fintype ι] (F : ι → C(Fin m → Bool, ℝ)) {q : ℕ}
    (hq : q ≤ mDim j / 2) (hF : ∀ y, Deg m q (F y)) (p : ℕ) {lam : ℝ} {v : ι → ℝ}
    (hv : IsUnitEig (gram (cubeState m) F) lam v) :
    cubeState m ((∑ y, v y • F y) ^ (2 * p))
      ≤ ((2 * p).factorial : ℝ) ^ wickIx j * (Real.exp (2 * wickIx j) * lam) ^ p :=
  cube_H1 F (wick_covers j hq) hF p hv

/-- **The Herbst reduction for an interacting state**: a moment bound `mom ≤ (2p)^p (κ L)^p` (Herbst form) and a
gradient-to-variance ratio `L ≤ R λ` give H1's form at every Wick exponent `w ≥ 1` with `C = e² κ R`.
DERIVED: `e²` from `n^n ≤ n! eⁿ`; `1` the floor of `w`; `2` the even order. -/
theorem h1_of_herbst {mom κ L R lam : ℝ} {p w : ℕ} (hw : 1 ≤ w) (hκ : 0 ≤ κ) (hL0 : 0 ≤ L)
    (hmom : mom ≤ (2 * (p : ℝ)) ^ p * (κ * L) ^ p) (hL : L ≤ R * lam) :
    mom ≤ ((2 * p).factorial : ℝ) ^ w * (Real.exp 2 * (κ * R) * lam) ^ p := by
  have hRl : 0 ≤ R * lam := hL0.trans hL
  have hfac1 : (1 : ℝ) ≤ ((2 * p).factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  have hfac : (0 : ℝ) < ((2 * p).factorial : ℝ) := by linarith
  have hpp : (2 * (p : ℝ)) ^ p ≤ ((2 * p).factorial : ℝ) * Real.exp 2 ^ p := by
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp; simp
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hn := Real.pow_div_factorial_le_exp (x := ((2 * p : ℕ) : ℝ)) (Nat.cast_nonneg _) (2 * p)
    rw [div_le_iff₀ hfac] at hn
    push_cast at hn
    calc (2 * (p : ℝ)) ^ p ≤ (2 * (p : ℝ)) ^ (2 * p) := pow_le_pow_right₀ (by linarith) (by omega)
      _ ≤ Real.exp (2 * p) * ((2 * p).factorial : ℝ) := hn
      _ = ((2 * p).factorial : ℝ) * Real.exp 2 ^ p := by
          rw [← Real.exp_nat_mul, mul_comm (Real.exp (2 * (p : ℝ))), mul_comm (p : ℝ) 2]
  have hκL : (κ * L) ^ p ≤ (κ * (R * lam)) ^ p :=
    pow_le_pow_left₀ (mul_nonneg hκ hL0) (mul_le_mul_of_nonneg_left hL hκ) p
  calc mom ≤ (2 * (p : ℝ)) ^ p * (κ * L) ^ p := hmom
    _ ≤ (((2 * p).factorial : ℝ) * Real.exp 2 ^ p) * (κ * (R * lam)) ^ p :=
        mul_le_mul hpp hκL (by positivity) (by positivity)
    _ ≤ ((2 * p).factorial : ℝ) ^ w * Real.exp 2 ^ p * (κ * (R * lam)) ^ p := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
          (pow_nonneg (mul_nonneg hκ hRl) p)
        calc ((2 * p).factorial : ℝ) = ((2 * p).factorial : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ ((2 * p).factorial : ℝ) ^ w := pow_le_pow_right₀ hfac1 hw
    _ = ((2 * p).factorial : ℝ) ^ w * (Real.exp 2 * (κ * R) * lam) ^ p := by ring

end HOne

/-! ## 4. The load-bearing test -/

section Test

/-- **The spin sum** `∑_i sgn(xᵢ)`, a reading of degree `1`. DERIVED: no numeral. -/
def rsum (m : ℕ) (x : Fin m → Bool) : ℝ := ∑ i, sgnB (x i)

/-- DERIVED: no numeral. -/
theorem rsum_succ (m : ℕ) (b : Bool) (x : Fin m → Bool) : rsum (m + 1) (Fin.cons b x) = sgnB b + rsum m x := by
  simp only [rsum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- **The spin sum is of degree `1`**. DERIVED: `1` the degree. -/
theorem deg_rsum : ∀ m : ℕ, Deg m 1 (rsum m)
  | 0 => trivial
  | m + 1 => deg_succ_iff.2 ⟨fun _ => 1, rsum m, fun h => absurd h one_ne_zero, deg_const m 0 1,
      deg_rsum m, fun b x => by simp only [rsum_succ, mul_one]⟩

/-- **The spin sum's variance is the number of spins**. DERIVED: `2` the square. -/
theorem avg_rsum_sq : ∀ m : ℕ, avg m (fun x => rsum m x ^ 2) = m
  | 0 => by simp [avg, rsum]
  | m + 1 => by
    have h : avg (m + 1) (fun x => rsum (m + 1) x ^ 2) = avg m (fun x => 1 + rsum m x ^ 2) := by
      rw [avg_succ]
      congr 1
      funext x
      simp only [rsum_succ, sgnB_true, sgnB_false]
      ring
    rw [h, avg_add m (fun _ => 1) (fun x => rsum m x ^ 2), avg_const, avg_rsum_sq m]
    push_cast
    ring

/-- **The all-`+1` spin bounds the moment from below**: `avg(rsum^{2m}) ≥ m^{2m} / 2^m`. DERIVED: `2` the
even power and the base of the count. -/
theorem avg_rsum_pow_ge (m : ℕ) : (m : ℝ) ^ (2 * m) / 2 ^ m ≤ avg m (fun x => rsum m x ^ (2 * m)) := by
  unfold avg
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have h1 : rsum m (fun _ => false) = m := by simp [rsum, sgnB]
  have := Finset.single_le_sum (f := fun x => rsum m x ^ (2 * m))
    (fun x _ => (even_two_mul m).pow_nonneg _) (Finset.mem_univ (fun _ : Fin m => false))
  simpa only [h1] using this

/-- **The Wick factor is needed**: no `C` has `avg(rsum^{2p}) ≤ C^p avg(rsum²)^p` for every number of spins
`m` and every order `p` (at `p = m > 2|C|` the ratio is at least `(m/2)^m`). DERIVED: `2` the even power and
the factor `2|C|`; `1` the shift. -/
theorem wick_needed :
    ¬ ∃ C : ℝ, ∀ m p : ℕ, avg m (fun x => rsum m x ^ (2 * p)) ≤ C ^ p * avg m (fun x => rsum m x ^ 2) ^ p := by
  rintro ⟨C, hC⟩
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (2 * |C|)
  set m := m₀ + 1 with hm
  have hmR : (m : ℝ) = m₀ + 1 := by rw [hm, Nat.cast_succ]
  have hm0 : (0 : ℝ) < m := by rw [hmR]; positivity
  have hmC : 2 * |C| < m := by rw [hmR]; linarith
  have h := (avg_rsum_pow_ge m).trans (hC m m)
  rw [avg_rsum_sq] at h
  have hCa : C ^ m ≤ |C| ^ m := (le_abs_self _).trans (abs_pow C m).le
  have h' : (m : ℝ) ^ (2 * m) / 2 ^ m ≤ |C| ^ m * (m : ℝ) ^ m :=
    h.trans (mul_le_mul_of_nonneg_right hCa (pow_nonneg hm0.le m))
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  rw [div_le_iff₀ h2m] at h'
  -- `m^{2m} ≤ (2|C|)^m m^m`, so `m^m ≤ (2|C|)^m`
  have hmm : (m : ℝ) ^ m * (m : ℝ) ^ m ≤ (2 * |C|) ^ m * (m : ℝ) ^ m := by
    calc (m : ℝ) ^ m * (m : ℝ) ^ m = (m : ℝ) ^ (2 * m) := by ring
      _ ≤ |C| ^ m * (m : ℝ) ^ m * 2 ^ m := h'
      _ = (2 * |C|) ^ m * (m : ℝ) ^ m := by ring
  have hle := le_of_mul_le_mul_right hmm (pow_pos hm0 m)
  have hlt : (2 * |C|) ^ m < (m : ℝ) ^ m :=
    pow_lt_pow_left₀ hmC (by positivity) (by omega)
  linarith

/-- **With the Wick factor the spin sum meets H1's form with `C = e²`**, for every `m` and `p`.
DERIVED: `e²` the constant at `w = 1`; `1` the degree and the Wick exponent; `2` the even power. -/
theorem rsum_H1 (m p : ℕ) :
    avg m (fun x => rsum m x ^ (2 * p))
      ≤ ((2 * p).factorial : ℝ) ^ 1 * (Real.exp (2 * (1 : ℕ)) * avg m (fun x => rsum m x ^ 2)) ^ p := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp; simp [avg_const]
  have hb := bonami m 1 (rsum m) (deg_rsum m) p hp
  have h0 : 0 ≤ avg m (fun x => rsum m x ^ 2) := avg_nonneg fun x => sq_nonneg _
  calc avg m (fun x => rsum m x ^ (2 * p))
      ≤ ((2 * (p : ℝ) - 1) ^ 1) ^ p * avg m (fun x => rsum m x ^ 2) ^ p := hb
    _ ≤ ((2 * p).factorial : ℝ) ^ 1 * Real.exp (2 * (1 : ℕ)) ^ p * avg m (fun x => rsum m x ^ 2) ^ p :=
        mul_le_mul_of_nonneg_right (wick_const hp (by norm_num)) (pow_nonneg h0 p)
    _ = _ := by ring

end Test

end MassGap.ModeHyper

end

#print axioms MassGap.ModeHyper.avg_succ
#print axioms MassGap.ModeHyper.avg_const
#print axioms MassGap.ModeHyper.deg_sum
#print axioms MassGap.ModeHyper.choose_two_mul_le
#print axioms MassGap.ModeHyper.sum_range_even_odd
#print axioms MassGap.ModeHyper.two_point
#print axioms MassGap.ModeHyper.avg_mink
#print axioms MassGap.ModeHyper.bonami
#print axioms MassGap.ModeHyper.wick_const
#print axioms MassGap.ModeHyper.wick_covers
#print axioms MassGap.ModeHyper.state_unitEig_sq
#print axioms MassGap.ModeHyper.cube_H1
#print axioms MassGap.ModeHyper.cube_H1_channel
#print axioms MassGap.ModeHyper.h1_of_herbst
#print axioms MassGap.ModeHyper.deg_rsum
#print axioms MassGap.ModeHyper.avg_rsum_sq
#print axioms MassGap.ModeHyper.avg_rsum_pow_ge
#print axioms MassGap.ModeHyper.wick_needed
#print axioms MassGap.ModeHyper.rsum_H1
