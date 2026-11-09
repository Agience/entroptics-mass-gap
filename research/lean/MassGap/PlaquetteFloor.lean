import Mathlib
import MassGap.PeriodicStateDLR
import MassGap.FluxTube
import MassGap.ExistenceFlow

/-!
# MassGap.PlaquetteFloor — a `β⁻²` floor on the Wilson plaquette mean, and the identity-flow no-go

For `N ≥ 2`, a plaquette `q` with two distinct directions, and `β ≥ 1`,

  `periodicState hN β (1 − Re tr U_q / N) ≥ e^{−n (16/N + 2)} / (N β²)`,

where `n` is the number of plaquettes reading the first link `l = (q.1.1, q.2)` of `q`
(`(boundaryPlaqs {l}).card`, a number fixed by `q`). This is `periodicState_plaq_ge`; at the
step-`k` state it is `stateK_plaq_ge`, and `not_classMoments_identity` feeds it to
`ExistenceFlow.not_classMoments_identity_poly` at `m = 2`: the identity flow fails `ClassMoments` on
the symmetrised plaquette class at every `t`, `C`, with no floor hypothesis.

## The route: one-link conditioning and a right translation of Haar measure

The state satisfies the DLR equations, so a lower bound on the one-link kernel at every boundary
condition is a lower bound on the state (`PeriodicStateDLR.periodicState_ge_of_kernel_ge`). The
one-link kernel at `l` integrates `u ↦ f(splice u ω) · wt(u)` over Haar measure on the link, with
`wt(u) = e^{−β F(u)}` and `F` the action of the plaquettes reading `l`.

Right translation of the link by a fixed `h ∈ SU(N)` preserves Haar measure, so the numerator
`∫ f w` equals `∫ (f w)(· h)`, and

  `2 ∫ f w = ∫ (f(u) w(u) + f(uh) w(uh))`.

Two pointwise facts bound the integrand below by a multiple of `w(u)`:

* **the target plaquette moves** (`target_ge`): the holonomy of `q` is `U_l R` before and
  `U_l h R` after, and `φ(a b⁻¹) ≤ 2 φ(a) + 2 φ(b)` (`density_mul_inv_le`, the parallelogram law for
  the Frobenius norm, `2N φ(g) = ‖g − 1‖²`) gives `φ(h) ≤ 2 (f(u) + f(uh))`;
* **the action moves little** (`action_le`): each occurrence of `l` in a boundary word inserts a
  conjugate of `h^{±1}`, and `φ(k y) ≤ φ(y) + t φ(k) + 1/(2t)` for every `t > 0`
  (`density_mul_le`, from `2 Re tr(A Bᴴ) ≤ t ‖A‖² + ‖B‖²/t`), so
  `F(uh) ≤ F(u) + 4n (t φ(h) + 1/(2t))`.

Hence `num ≥ e^{−β · 4n(t φ(h) + 1/(2t))} φ(h)/4 · part` (`kernel_ge`). At `t = β` and the torus
element `h = diag(e^{iθ}, e^{−iθ}, 1, …)` with `cos θ = 1 − 2/β²`, `φ(h) = 4/(Nβ²)`
(`density_hTheta`), the exponent is `n (16/N + 2)` and the floor is `e^{−n(16/N+2)}/(Nβ²)`.

No derivative, small-ball estimate or Laplace bound enters: the only measure-theoretic input is the
right invariance of Haar measure (`CompactGauge.isMulRightInvariant_probHaar`).

## Contents

* `ipRe`, `ipRe_eq_sum`, `two_ipRe_le`, `ipRe_self_nonneg` — the real trace pairing.
* `density_mul_le`, `density_mul_inv_le`, `density_mul_comm`, `density_inv` — the density.
* `wordProd`, `word_le`, `action_le`, `target_ge` — the one-link translation on boundary words.
* `kernel_ge` — the one-link kernel floor.
* `hTheta`, `density_hTheta` — the translating element.
* `periodicState_plaq_ge`, `stateK_plaq_ge` — the floor on the state.
* `not_classMoments_identity` — the unconditional identity-flow no-go.
-/

noncomputable section

namespace MassGap.PlaquetteFloor

open MeasureTheory Filter
open MassGap.GibbsSpec
open MassGap.WilsonAction (wilsonDensity wilsonDensity_nonneg wilsonDensity_le_two
  measurable_wilsonDensity wilsonDensity_conj)
open MassGap.CompactGauge (probHaar)
open MassGap.SUN (SU)

variable {N : ℕ}

/-! ## 1. The real trace pairing -/

section Pairing

/-- `Re tr (A Bᴴ)`, the real Frobenius pairing.

DERIVED: no numeral. -/
def ipRe (A B : Matrix (Fin N) (Fin N) ℂ) : ℝ := (Matrix.trace (A * B.conjTranspose)).re

/-- The pairing is the Euclidean inner product of the real coordinates.

DERIVED: no numeral. -/
theorem ipRe_eq_sum (A B : Matrix (Fin N) (Fin N) ℂ) :
    ipRe A B = ∑ p : Fin N × Fin N,
      ((A p.1 p.2).re * (B p.1 p.2).re + (A p.1 p.2).im * (B p.1 p.2).im) := by
  rw [Fintype.sum_prod_type]
  have htr : Matrix.trace (A * B.conjTranspose) = ∑ i : Fin N, (A * B.conjTranspose) i i := rfl
  unfold ipRe
  rw [htr, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.conjTranspose_apply, Complex.mul_re]
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- DERIVED: `2` the cross term; `0` the sign of `t`. -/
theorem two_mul_le_aux (a1 a2 b1 b2 : ℝ) {t : ℝ} (ht : 0 < t) :
    2 * (a1 * b1 + a2 * b2) ≤ t * (a1 * a1 + a2 * a2) + (b1 * b1 + b2 * b2) / t := by
  have key : t * (a1 * a1 + a2 * a2) + (b1 * b1 + b2 * b2) / t - 2 * (a1 * b1 + a2 * b2)
      = ((t * a1 - b1) ^ 2 + (t * a2 - b2) ^ 2) / t := by
    field_simp
    ring
  have : 0 ≤ ((t * a1 - b1) ^ 2 + (t * a2 - b2) ^ 2) / t := by positivity
  linarith

/-- **Polarisation**: `2 Re tr(A Bᴴ) ≤ t Re tr(A Aᴴ) + Re tr(B Bᴴ) / t` for `t > 0`.

DERIVED: `2` the cross term; `0` the sign of `t`. -/
theorem two_ipRe_le (A B : Matrix (Fin N) (Fin N) ℂ) {t : ℝ} (ht : 0 < t) :
    2 * ipRe A B ≤ t * ipRe A A + ipRe B B / t := by
  rw [ipRe_eq_sum, ipRe_eq_sum, ipRe_eq_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_div,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun p _ => two_mul_le_aux _ _ _ _ ht)

/-- DERIVED: `0` the sign. -/
theorem ipRe_self_nonneg (A : Matrix (Fin N) (Fin N) ℂ) : 0 ≤ ipRe A A := by
  rw [ipRe_eq_sum]
  exact Finset.sum_nonneg (fun p _ => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))

/-- DERIVED: no numeral. -/
theorem re_trace_conjTranspose (A : Matrix (Fin N) (Fin N) ℂ) :
    (Matrix.trace A.conjTranspose).re = (Matrix.trace A).re := by
  rw [Matrix.trace_conjTranspose]
  simp

/-- DERIVED: `1` the identity matrix. -/
theorem re_trace_one : (Matrix.trace (1 : Matrix (Fin N) (Fin N) ℂ)).re = N := by
  rw [Matrix.trace_one]
  simp

/-- DERIVED: `1` the identity matrix. -/
theorem coe_mul_conjTranspose (g : SU N) :
    (g : Matrix (Fin N) (Fin N) ℂ) * (g : Matrix (Fin N) (Fin N) ℂ).conjTranspose = 1 := by
  have hu := (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hu
  exact hu

/-- DERIVED: `1` the identity matrix. -/
theorem coe_conjTranspose_mul (g : SU N) :
    (g : Matrix (Fin N) (Fin N) ℂ).conjTranspose * (g : Matrix (Fin N) (Fin N) ℂ) = 1 := by
  have hu := (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
  exact hu

/-- DERIVED: no numeral. -/
theorem coe_inv (g : SU N) :
    ((g⁻¹ : SU N) : Matrix (Fin N) (Fin N) ℂ) = (g : Matrix (Fin N) (Fin N) ℂ).conjTranspose :=
  rfl

/-- DERIVED: no numeral. -/
theorem coe_mul (g k : SU N) :
    ((g * k : SU N) : Matrix (Fin N) (Fin N) ℂ)
      = (g : Matrix (Fin N) (Fin N) ℂ) * (k : Matrix (Fin N) (Fin N) ℂ) :=
  rfl

end Pairing

/-! ## 2. Two inequalities for the density -/

section Density

/-- **The trace moves little under a left factor**, matrix form: for `K Kᴴ = 1`, `Yᴴ Y = 1`, `t > 0`,
`2 (Re tr Y − Re tr (K Y)) ≤ t (2N − 2 Re tr K) + N / t`.

DERIVED: `2` the polarisation; `1` the identity; `0` the sign of `t`. -/
theorem trace_mul_le (K Y : Matrix (Fin N) (Fin N) ℂ) (hK : K * K.conjTranspose = 1)
    (hY : Y.conjTranspose * Y = 1) {t : ℝ} (ht : 0 < t) :
    2 * ((Matrix.trace Y).re - (Matrix.trace (K * Y)).re)
      ≤ t * (2 * N - 2 * (Matrix.trace K).re) + N / t := by
  have h := two_ipRe_le (1 - K) Y.conjTranspose ht
  have e1 : ipRe (1 - K) Y.conjTranspose = (Matrix.trace Y).re - (Matrix.trace (K * Y)).re := by
    unfold ipRe
    rw [Matrix.conjTranspose_conjTranspose, sub_mul, one_mul, Matrix.trace_sub, Complex.sub_re]
  have e2 : ipRe (1 - K) (1 - K) = 2 * N - 2 * (Matrix.trace K).re := by
    unfold ipRe
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
    simp only [sub_mul, mul_sub, one_mul, mul_one, hK, Matrix.trace_sub, Complex.sub_re,
      re_trace_conjTranspose, re_trace_one]
    ring
  have e3 : ipRe Y.conjTranspose Y.conjTranspose = N := by
    unfold ipRe
    rw [Matrix.conjTranspose_conjTranspose, hY, re_trace_one]
  rw [e1, e2, e3] at h
  exact h

/-- **The density moves little under a left factor**: for `k, y ∈ SU(N)` and `t > 0`,
`φ(k y) ≤ φ(y) + t φ(k) + 1/(2t)`.

DERIVED: `2` the polarisation; `1` the density's unit; `0` the excluded colour count and the sign
of `t`. -/
theorem density_mul_le (hN : N ≠ 0) (k y : SU N) {t : ℝ} (ht : 0 < t) :
    wilsonDensity (k * y) ≤ wilsonDensity y + t * wilsonDensity k + 1 / (2 * t) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have h := trace_mul_le (k : Matrix (Fin N) (Fin N) ℂ) (y : Matrix (Fin N) (Fin N) ℂ)
    (coe_mul_conjTranspose k) (coe_conjTranspose_mul y) ht
  unfold wilsonDensity
  rw [coe_mul]
  set a := (Matrix.trace (y : Matrix (Fin N) (Fin N) ℂ)).re
  set b := (Matrix.trace ((k : Matrix (Fin N) (Fin N) ℂ) * (y : Matrix (Fin N) (Fin N) ℂ))).re
  set c := (Matrix.trace (k : Matrix (Fin N) (Fin N) ℂ)).re
  have key : 1 / (N : ℝ) * a - 1 / (N : ℝ) * b ≤ t * (1 - 1 / (N : ℝ) * c) + 1 / (2 * t) := by
    have e : t * (1 - 1 / (N : ℝ) * c) + 1 / (2 * t) - (1 / (N : ℝ) * a - 1 / (N : ℝ) * b)
        = (t * (2 * N - 2 * c) + N / t - 2 * (a - b)) / (2 * N) := by
      field_simp
    have : 0 ≤ (t * (2 * N - 2 * c) + N / t - 2 * (a - b)) / (2 * N) :=
      div_nonneg (by linarith) (by positivity)
    linarith
  linarith

/-- **The parallelogram inequality**, matrix form: for `A Aᴴ = 1`, `B Bᴴ = 1`,
`2 Re tr A + 2 Re tr B − Re tr (A Bᴴ) ≤ 3N`. It is `‖(A − 1) + (B − 1)‖² ≥ 0`.

DERIVED: `2`, `3` the expansion of the square; `1` the identity. -/
theorem trace_parallelogram (A B : Matrix (Fin N) (Fin N) ℂ) (hA : A * A.conjTranspose = 1)
    (hB : B * B.conjTranspose = 1) :
    2 * (Matrix.trace A).re + 2 * (Matrix.trace B).re - (Matrix.trace (A * B.conjTranspose)).re
      ≤ 3 * N := by
  have h := ipRe_self_nonneg (A - 1 + (B - 1))
  unfold ipRe at h
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one] at h
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, hA, hB, Matrix.trace_add,
    Matrix.trace_sub, Complex.add_re, Complex.sub_re, re_trace_conjTranspose, re_trace_one] at h
  have hBA : (Matrix.trace (B * A.conjTranspose)).re = (Matrix.trace (A * B.conjTranspose)).re := by
    rw [← re_trace_conjTranspose (A * B.conjTranspose), Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  linarith

/-- **The quasi-triangle inequality for the density**: `φ(a b⁻¹) ≤ 2 φ(a) + 2 φ(b)` on `SU(N)`.

DERIVED: `2` the parallelogram; `0` the excluded colour count. -/
theorem density_mul_inv_le (hN : N ≠ 0) (a b : SU N) :
    wilsonDensity (a * b⁻¹) ≤ 2 * wilsonDensity a + 2 * wilsonDensity b := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have h := trace_parallelogram (a : Matrix (Fin N) (Fin N) ℂ) (b : Matrix (Fin N) (Fin N) ℂ)
    (coe_mul_conjTranspose a) (coe_mul_conjTranspose b)
  unfold wilsonDensity
  rw [coe_mul, coe_inv]
  set x := (Matrix.trace (a : Matrix (Fin N) (Fin N) ℂ)).re
  set y := (Matrix.trace (b : Matrix (Fin N) (Fin N) ℂ)).re
  set z := (Matrix.trace ((a : Matrix (Fin N) (Fin N) ℂ)
    * (b : Matrix (Fin N) (Fin N) ℂ).conjTranspose)).re
  have e : 2 * (1 - 1 / (N : ℝ) * x) + 2 * (1 - 1 / (N : ℝ) * y) - (1 - 1 / (N : ℝ) * z)
      = (3 * N - (2 * x + 2 * y - z)) / N := by
    field_simp
    ring
  have : 0 ≤ (3 * N - (2 * x + 2 * y - z)) / N := div_nonneg (by linarith) hN'.le
  linarith

/-- The density is a class function: `φ(x y) = φ(y x)`.

DERIVED: no numeral. -/
theorem density_mul_comm (x y : SU N) : wilsonDensity (x * y) = wilsonDensity (y * x) := by
  unfold wilsonDensity
  rw [coe_mul, coe_mul, Matrix.trace_mul_comm]

/-- `φ(x⁻¹) = φ(x)`.

DERIVED: no numeral. -/
theorem density_inv (x : SU N) : wilsonDensity x⁻¹ = wilsonDensity x := by
  unfold wilsonDensity
  rw [coe_inv, re_trace_conjTranspose]

end Density

/-! ## 3. Translating one link -/

section Word

/-- The product along a boundary word.

DERIVED: no numeral. -/
def wordProd (U : IConf (SU N)) (L : List (ILink × Bool)) : SU N :=
  (L.map (fun lo => if lo.2 then U lo.1 else (U lo.1)⁻¹)).prod

/-- DERIVED: no numeral. -/
theorem wordProd_cons (U : IConf (SU N)) (a : ILink × Bool) (L : List (ILink × Bool)) :
    wordProd U (a :: L) = (if a.2 then U a.1 else (U a.1)⁻¹) * wordProd U L := by
  simp only [wordProd, List.map_cons, List.prod_cons]

/-- DERIVED: no numeral. -/
theorem wordProd_nil (U : IConf (SU N)) : wordProd U [] = 1 := by
  simp only [wordProd, List.map_nil, List.prod_nil]

/-- **Right-translating one link moves a word's density by at most one step per letter**: if `U'`
agrees with `U` off `l` and `U' l = U l · h`, then for every word `L`, every `z, w` and `t > 0`,
`φ(z · L(U') · w) ≤ φ(z · L(U) · w) + |L| (t φ(h) + 1/(2t))`.

DERIVED: `1`, `2` from `density_mul_le`; `0` the excluded colour count and the sign of `t`. -/
theorem word_le (hN : N ≠ 0) {U U' : IConf (SU N)} {l : ILink} {h : SU N}
    (hl : U' l = U l * h) (hne : ∀ l', l' ≠ l → U' l' = U l') {t : ℝ} (ht : 0 < t) :
    ∀ (L : List (ILink × Bool)) (z w : SU N),
      wilsonDensity (z * wordProd U' L * w)
        ≤ wilsonDensity (z * wordProd U L * w)
          + L.length * (t * wilsonDensity h + 1 / (2 * t)) := by
  have hε : 0 ≤ t * wilsonDensity h + 1 / (2 * t) :=
    add_nonneg (mul_nonneg ht.le (wilsonDensity_nonneg hN h)) (by positivity)
  intro L
  induction L with
  | nil =>
    intro z w
    simp only [wordProd_nil, List.length_nil, Nat.cast_zero, zero_mul, add_zero, le_refl]
  | cons a L ih =>
    intro z w
    rw [wordProd_cons, wordProd_cons]
    set e := (if a.2 then U a.1 else (U a.1)⁻¹) with he
    set e' := (if a.2 then U' a.1 else (U' a.1)⁻¹) with he'
    have h1 := ih (z * e') w
    have r1 : z * (e' * wordProd U' L) * w = z * e' * wordProd U' L * w := by
      simp only [mul_assoc]
    -- the step at the head letter
    set Y := wordProd U L * w * z with hY
    have rot : ∀ x : SU N, wilsonDensity (z * x * wordProd U L * w) = wilsonDensity (x * Y) := by
      intro x
      rw [show z * x * wordProd U L * w = z * (x * (wordProd U L * w)) by simp only [mul_assoc],
        density_mul_comm, hY]
      simp only [mul_assoc]
    have step : wilsonDensity (z * e' * wordProd U L * w)
        ≤ wilsonDensity (z * e * wordProd U L * w) + (t * wilsonDensity h + 1 / (2 * t)) := by
      rw [rot e', rot e]
      by_cases ha : a.1 = l
      · cases hb : a.2 with
        | true =>
          have : e' = e * h := by
            simp [he', he, hb, ha, hl]
          rw [this, show e * h * Y = e * (h * Y) by simp only [mul_assoc], density_mul_comm,
            show h * Y * e = h * (Y * e) by simp only [mul_assoc], density_mul_comm e Y]
          have := density_mul_le hN h (Y * e) ht
          linarith
        | false =>
          have : e' = h⁻¹ * e := by
            simp [he', he, hb, ha, hl, mul_inv_rev]
          rw [this, mul_assoc]
          have := density_mul_le hN h⁻¹ (e * Y) ht
          rw [density_inv] at this
          linarith
      · have : e' = e := by
          rw [he', he, hne a.1 ha]
        rw [this]
        linarith
    have r2 : z * (e * wordProd U L) * w = z * e * wordProd U L * w := by
      simp only [mul_assoc]
    rw [r1, r2]
    have hlen : ((a :: L).length : ℝ) = L.length + 1 := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [hlen]
    linarith [h1, step]

/-- DERIVED: no numeral. -/
theorem ihol_eq_wordProd (q : IPlaq) (U : IConf (SU N)) : ihol q U = wordProd U (ibd q) := rfl

/-- **The action of the plaquettes reading `l` moves by at most `4n (t φ(h) + 1/(2t))`** under a
right translation of the link `l` by `h`, `n = |boundaryPlaqs {l}|`.

DERIVED: `4` the length of a boundary word; `1`, `2` from `word_le`; `0` the excluded colour count
and the sign of `t`. -/
theorem action_le (hN : N ≠ 0) {U U' : IConf (SU N)} {l : ILink} {h : SU N}
    (hl : U' l = U l * h) (hne : ∀ l', l' ≠ l → U' l' = U l') {t : ℝ} (ht : 0 < t) :
    actionOn wilsonDensity (boundaryPlaqs {l}) U'
      ≤ actionOn wilsonDensity (boundaryPlaqs {l}) U
        + ((boundaryPlaqs {l}).card : ℝ) * (4 * (t * wilsonDensity h + 1 / (2 * t))) := by
  unfold actionOn
  calc ∑ p ∈ boundaryPlaqs {l}, wilsonDensity (ihol p U')
      ≤ ∑ p ∈ boundaryPlaqs {l},
          (wilsonDensity (ihol p U) + 4 * (t * wilsonDensity h + 1 / (2 * t))) := by
        refine Finset.sum_le_sum (fun p _ => ?_)
        have := word_le hN hl hne ht (ibd p) 1 1
        simp only [one_mul, mul_one] at this
        have hlen : ((ibd p).length : ℝ) = 4 := by simp [ibd]
        rw [hlen] at this
        exact this
    _ = ∑ p ∈ boundaryPlaqs {l}, wilsonDensity (ihol p U)
          + ((boundaryPlaqs {l}).card : ℝ) * (4 * (t * wilsonDensity h + 1 / (2 * t))) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]

/-- `ishift μ x ≠ x`.

DERIVED: `1` the unit step. -/
theorem ishift_ne (μ : Fin 4) (x : ISite) : ishift μ x ≠ x := by
  intro hc
  have := congrFun hc μ
  simp only [ishift, Function.update_self] at this
  omega

/-- **The translated plaquette moves**: if `U'` agrees with `U` off the first link
`l = (q.1.1, q.2)` of a plaquette with distinct directions and `U' l = U l · h`, then
`φ(h) ≤ 2 (φ(U'_q) + φ(U_q))`.

DERIVED: `2` from `density_mul_inv_le`; `0` the excluded colour count. -/
theorem target_ge (hN : N ≠ 0) (q : IPlaq) (hq : q.1.1 ≠ q.1.2) {U U' : IConf (SU N)} {h : SU N}
    (hl : U' (q.1.1, q.2) = U (q.1.1, q.2) * h)
    (hne : ∀ l', l' ≠ (q.1.1, q.2) → U' l' = U l') :
    wilsonDensity h ≤ 2 * (wilsonDensity (ihol q U') + wilsonDensity (ihol q U)) := by
  set rest : List (ILink × Bool) :=
    [((q.1.2, ishift q.1.1 q.2), true), ((q.1.1, ishift q.1.2 q.2), false), ((q.1.2, q.2), false)]
    with hrest
  have hibd : ibd q = ((q.1.1, q.2), true) :: rest := rfl
  have hr : wordProd U' rest = wordProd U rest := by
    unfold wordProd
    congr 1
    refine List.map_congr_left (fun a ha => ?_)
    have hne' : a.1 ≠ (q.1.1, q.2) := by
      rw [hrest] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · intro hc
        exact hq (congrArg Prod.fst hc).symm
      · intro hc
        exact ishift_ne q.1.2 q.2 (congrArg Prod.snd hc)
      · intro hc
        exact hq (congrArg Prod.fst hc).symm
    rw [hne a.1 hne']
  have e1 : ihol q U = U (q.1.1, q.2) * wordProd U rest := by
    rw [ihol_eq_wordProd, hibd, wordProd_cons]
    rfl
  have e2 : ihol q U' = U (q.1.1, q.2) * h * wordProd U rest := by
    rw [ihol_eq_wordProd, hibd, wordProd_cons, hr]
    show U' (q.1.1, q.2) * wordProd U rest = _
    rw [hl]
  have hq' := density_mul_inv_le hN (ihol q U') (ihol q U)
  have hconj : ihol q U' * (ihol q U)⁻¹
      = U (q.1.1, q.2) * h * (U (q.1.1, q.2))⁻¹ := by
    rw [e1, e2]
    group
  rw [hconj, wilsonDensity_conj] at hq'
  linarith

end Word

/-! ## 4. The one-link kernel floor -/

section Kernel

/-- **The one-link kernel at the first link of `q` is at least `e^{−β Δ} φ(h)/4`**, at every boundary
condition, every `h ∈ SU(N)`, `t > 0` and `β ≥ 0`, with `Δ = 4n (t φ(h) + 1/(2t))` and
`n = |boundaryPlaqs {l}|`.

DERIVED: `4` the word length and the two halvings; `1`, `2` from `word_le`; `0` the signs. -/
theorem kernel_ge (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (q : IPlaq) (hq : q.1.1 ≠ q.1.2) (h : SU N)
    {t : ℝ} (ht : 0 < t) (ω : IConf (SU N)) :
    Real.exp (-(β * (((boundaryPlaqs {(q.1.1, q.2)}).card : ℝ)
        * (4 * (t * wilsonDensity h + 1 / (2 * t)))))) * wilsonDensity h / 4
      ≤ MassGap.PeriodicStateDLR.wspec hN β {(q.1.1, q.2)}
          (MassGap.ObserverEnergyMoments.plaqField (N := N) q).1 ω := by
  rw [MassGap.PeriodicStateDLR.wspec_apply]
  set l : ILink := (q.1.1, q.2) with hldef
  set Δ : ℝ := ((boundaryPlaqs {l}).card : ℝ) * (4 * (t * wilsonDensity h + 1 / (2 * t))) with hΔ
  set c0 : ℝ := Real.exp (-(β * Δ)) with hc0
  set μ : Measure (SU N) := probHaar (SU N) with hμ
  have hΔ0 : 0 ≤ Δ := mul_nonneg (Nat.cast_nonneg _)
    (by have := wilsonDensity_nonneg hN h; positivity)
  have hc0le : c0 ≤ 1 := by
    rw [hc0, Real.exp_le_one_iff]
    nlinarith
  have hc0pos : 0 < c0 := Real.exp_pos _
  let τ : VConf (SU N) {l} → VConf (SU N) {l} := fun u i => u i * h
  have hτ : MeasurePreserving τ (vol μ {l}) (vol μ {l}) :=
    measurePreserving_pi (fun _ => μ) (fun _ => μ) (fun _ => measurePreserving_mul_right μ h)
  let f : IConf (SU N) → ℝ := fun U => wilsonDensity (ihol q U)
  have hfm : Measurable f := measurable_wilsonDensity.comp (measurable_ihol q)
  have hf0 : ∀ U, 0 ≤ f U := fun U => wilsonDensity_nonneg hN _
  have hf2 : ∀ U, |f U| ≤ 2 := fun U => by
    rw [abs_of_nonneg (hf0 U)]
    exact wilsonDensity_le_two hN _
  let w : VConf (SU N) {l} → ℝ := fun u => wt wilsonDensity β {l} u ω
  let g : VConf (SU N) {l} → ℝ := fun u => f (splice {l} u ω) * w u
  have hwm : Measurable w := measurable_wt_left measurable_wilsonDensity β {l} ω
  have hgm : Measurable g := (hfm.comp (measurable_splice_left {l} ω)).mul hwm
  have hw0 : ∀ u, 0 ≤ w u := fun u => (wt_pos _ _ _ _ _).le
  have hw1 : ∀ u, w u ≤ 1 := fun u =>
    exp_neg_actionOn_le_one (wilsonDensity_nonneg hN) hβ _ _
  have hg2 : ∀ u, |g u| ≤ 2 := fun u => by
    have h1 := hf2 (splice {l} u ω)
    rw [abs_mul, abs_of_nonneg (hw0 u)]
    calc |f (splice {l} u ω)| * w u ≤ 2 * 1 :=
          mul_le_mul h1 (hw1 u) (hw0 u) (by norm_num)
      _ = 2 := by norm_num
  have hg_int : Integrable g (vol μ {l}) := integrable_of_bounded _ hgm hg2
  have hgτ_int : Integrable (fun u => g (τ u)) (vol μ {l}) :=
    integrable_of_bounded _ (hgm.comp hτ.measurable) (fun u => hg2 (τ u))
  have hw_int : Integrable w (vol μ {l}) :=
    integrable_wt measurable_wilsonDensity (wilsonDensity_nonneg hN) (wilsonDensity_le_two hN)
      β {l} μ ω
  have hinv : (∫ u, g (τ u) ∂(vol μ {l})) = ∫ u, g u ∂(vol μ {l}) :=
    integral_comp_of_mp hτ hgm
  -- the pointwise bound
  have hpt : ∀ u, c0 * (wilsonDensity h / 2) * w u ≤ g u + g (τ u) := by
    intro u
    have hlmem : l ∈ ({l} : Finset ILink) := Finset.mem_singleton_self l
    set U := splice {l} u ω with hU
    set U' := splice {l} (τ u) ω with hU'
    have hl : U' l = U l * h := by
      rw [hU, hU', splice_mem hlmem, splice_mem hlmem]
    have hne : ∀ l', l' ≠ l → U' l' = U l' := by
      intro l' hl'
      have hn : l' ∉ ({l} : Finset ILink) := by simpa using hl'
      rw [hU, hU', splice_not_mem hn, splice_not_mem hn]
    have hact := action_le hN hl hne ht
    rw [← hΔ] at hact
    have hwτ : c0 * w u ≤ w (τ u) := by
      show c0 * wt wilsonDensity β {l} u ω ≤ wt wilsonDensity β {l} (τ u) ω
      unfold wt
      rw [hc0, ← Real.exp_add, Real.exp_le_exp]
      have := mul_le_mul_of_nonneg_left hact hβ
      rw [← hU, ← hU']
      nlinarith
    have htar := target_ge hN q hq hl hne
    have hgu : g u = f U * w u := rfl
    have hgτ : g (τ u) = f U' * w (τ u) := rfl
    have hfU : f U = wilsonDensity (ihol q U) := rfl
    have hfU' : f U' = wilsonDensity (ihol q U') := rfl
    rw [hgu, hgτ]
    have hcw : 0 ≤ c0 * w u := mul_nonneg hc0pos.le (hw0 u)
    have i1 : f U * (c0 * w u) ≤ f U * w u :=
      mul_le_mul_of_nonneg_left (by nlinarith [hw0 u]) (hf0 U)
    have i2 : f U' * (c0 * w u) ≤ f U' * w (τ u) := mul_le_mul_of_nonneg_left hwτ (hf0 U')
    have i3 : wilsonDensity h / 2 ≤ f U + f U' := by rw [hfU, hfU']; linarith
    have i4 : (c0 * w u) * (wilsonDensity h / 2) ≤ (c0 * w u) * (f U + f U') :=
      mul_le_mul_of_nonneg_left i3 hcw
    nlinarith
  have hpart := part_pos measurable_wilsonDensity (wilsonDensity_nonneg hN)
    (wilsonDensity_le_two hN) β {l} μ ω
  have hmain : c0 * (wilsonDensity h / 2) * part wilsonDensity β {l} μ ω
      ≤ 2 * num wilsonDensity β {l} μ f ω := by
    unfold part num
    calc c0 * (wilsonDensity h / 2) * ∫ u, wt wilsonDensity β {l} u ω ∂(vol μ {l})
        = ∫ u, c0 * (wilsonDensity h / 2) * w u ∂(vol μ {l}) :=
          (integral_const_mul _ _).symm
      _ ≤ ∫ u, (g u + g (τ u)) ∂(vol μ {l}) :=
          integral_mono (hw_int.const_mul _) (hg_int.add hgτ_int) hpt
      _ = (∫ u, g u ∂(vol μ {l})) + ∫ u, g (τ u) ∂(vol μ {l}) := integral_add hg_int hgτ_int
      _ = 2 * ∫ u, g u ∂(vol μ {l}) := by rw [hinv]; ring
  unfold spec
  rw [le_div_iff₀ hpart]
  have hf_eq : (⇑(MassGap.ObserverEnergyMoments.plaqField (N := N) q).1) = f := rfl
  rw [hf_eq]
  nlinarith

end Kernel

/-! ## 5. The translating element -/

section Element

/-- The angles `(θ, −θ, 0, …, 0)` on `Fin N`, `N ≥ 2`.

DERIVED: `0`, `1` the first two indices; `2` the least colour count holding both. -/
def angles (hN2 : 2 ≤ N) (θ : ℝ) : Fin N → ℝ := fun k =>
  if k = ⟨0, by omega⟩ then θ else if k = ⟨1, by omega⟩ then -θ else 0

/-- DERIVED: `0`, `1` the first two indices; `2` the least colour count. -/
theorem idx_ne (hN2 : 2 ≤ N) : (⟨1, by omega⟩ : Fin N) ≠ ⟨0, by omega⟩ := by
  intro h
  have := congrArg Fin.val h
  simp at this

/-- DERIVED: `0`, `1` the first two indices; `2` the least colour count. -/
theorem sum_angles_fun (hN2 : 2 ≤ N) (θ : ℝ) (F : ℝ → ℝ) (hF : F 0 = 0) :
    ∑ k, F (angles hN2 θ k) = F θ + F (-θ) := by
  rw [Finset.sum_eq_add_of_mem (⟨0, by omega⟩ : Fin N) ⟨1, by omega⟩ (Finset.mem_univ _)
    (Finset.mem_univ _) (idx_ne hN2).symm]
  · simp [angles]
  · intro c _ hc
    simp only [angles, if_neg hc.1, if_neg hc.2, hF]

/-- **The torus element `diag(e^{iθ}, e^{−iθ}, 1, …, 1)` of `SU(N)`.**

DERIVED: `2` the least colour count. -/
def hTheta (hN2 : 2 ≤ N) (θ : ℝ) : SU N :=
  ⟨MassGap.FluxTube.torus (angles hN2 θ), MassGap.FluxTube.torus_mem _ (by
    have := sum_angles_fun hN2 θ id rfl
    simpa using this)⟩

/-- **Its density is `(2 − 2 cos θ)/N`.**

DERIVED: `2` the two moved entries; `1` the unit; `0` the excluded colour count. -/
theorem density_hTheta (hN2 : 2 ≤ N) (θ : ℝ) :
    wilsonDensity (hTheta hN2 θ) = (2 - 2 * Real.cos θ) / N := by
  have hN : N ≠ 0 := by omega
  have h1 : wilsonDensity (hTheta hN2 θ)
      = MassGap.FluxTube.wilson (MassGap.FluxTube.torus (angles hN2 θ)) := by
    unfold wilsonDensity MassGap.FluxTube.wilson
    show 1 - 1 / (N : ℝ) * (Matrix.trace (MassGap.FluxTube.torus (angles hN2 θ))).re = _
    ring
  have hs := sum_angles_fun hN2 θ (fun x => 1 - Real.cos x) (by simp)
  rw [h1, MassGap.FluxTube.wilson_torus hN, hs, Real.cos_neg]
  ring

end Element

/-! ## 6. The floor on the state -/

section State

/-- **The plaquette floor on the periodic Wilson state**: for `N ≥ 2`, `q` with distinct directions
and `β ≥ 1`,
`periodicState hN β (1 − Re tr U_q / N) ≥ e^{−n (16/N + 2)} / (N β²)`,
`n = |boundaryPlaqs {(q.1.1, q.2)}|`.

DERIVED: `16 = 4 · 4`, `2 = 4 · 1/2` from `Δ` at `t = β`, `φ(h) = 4/(Nβ²)`; `1` the least coupling;
`2` the least colour count and the power of `β`. -/
theorem periodicState_plaq_ge (hN2 : 2 ≤ N) (hN : N ≠ 0) {β : ℝ} (hβ : 1 ≤ β) (q : IPlaq)
    (hq : q.1.1 ≠ q.1.2) :
    Real.exp (-(((boundaryPlaqs {(q.1.1, q.2)}).card : ℝ) * (16 / N + 2))) / (N * β ^ 2)
      ≤ MassGap.PeriodicState.periodicState hN β
          (MassGap.ObserverEnergyMoments.plaqField (N := N) q).1 := by
  have hβ0 : 0 < β := by linarith
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hβne : β ≠ 0 := hβ0.ne'
  have hNne : (N : ℝ) ≠ 0 := hN'.ne'
  set x : ℝ := 1 - 2 / β ^ 2 with hx
  have hβ2 : 1 ≤ β ^ 2 := by nlinarith
  have hx1 : -1 ≤ x := by
    rw [hx]
    have : 2 / β ^ 2 ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hx2 : x ≤ 1 := by
    rw [hx]
    have : 0 ≤ 2 / β ^ 2 := by positivity
    linarith
  set h := hTheta hN2 (Real.arccos x) with hh
  have hφ : wilsonDensity h = 4 / (N * β ^ 2) := by
    rw [hh, density_hTheta, Real.cos_arccos hx1 hx2, hx]
    field_simp
    ring
  refine MassGap.PeriodicStateDLR.periodicState_ge_of_kernel_ge hN β {(q.1.1, q.2)} _
    (fun ω => ?_)
  have hk := kernel_ge hN hβ0.le q hq h hβ0 ω
  rw [hφ] at hk
  have e : Real.exp (-(((boundaryPlaqs {(q.1.1, q.2)}).card : ℝ) * (16 / N + 2))) / (N * β ^ 2)
      = Real.exp (-(β * (((boundaryPlaqs {(q.1.1, q.2)}).card : ℝ)
          * (4 * (β * (4 / (N * β ^ 2)) + 1 / (2 * β)))))) * (4 / (N * β ^ 2)) / 4 := by
    have he : β * (((boundaryPlaqs {(q.1.1, q.2)}).card : ℝ)
          * (4 * (β * (4 / (N * β ^ 2)) + 1 / (2 * β))))
        = ((boundaryPlaqs {(q.1.1, q.2)}).card : ℝ) * (16 / N + 2) := by
      field_simp
      ring
    rw [he]
    ring
  rw [e]
  exact hk

/-- **The plaquette floor at step `k`**: `stateK hN k (1 − Re tr U_q / N) ≥ c / β_k²` with
`c = e^{−n (16/N + 2)} / N`, for `N ≥ 2` and `q` with distinct directions.

DERIVED: `16`, `2` from `periodicState_plaq_ge`; `2` the least colour count and the power. -/
theorem stateK_plaq_ge (hN2 : 2 ≤ N) (hN : N ≠ 0) (q : IPlaq) (hq : q.1.1 ≠ q.1.2) (k : ℕ) :
    Real.exp (-(((boundaryPlaqs {(q.1.1, q.2)}).card : ℝ) * (16 / N + 2))) / N
        / MassGap.ContinuumSchwinger.dyBeta (MassGap.ContinuumSchwinger.one_le_of_ne_zero hN) k ^ 2
      ≤ MassGap.ContinuumSchwinger.stateK hN k
          (MassGap.ObserverEnergyMoments.plaqField (N := N) q).1 := by
  rw [div_div]
  exact periodicState_plaq_ge hN2 hN
    (MassGap.ContinuumSchwinger.one_le_dyBeta (MassGap.ContinuumSchwinger.one_le_of_ne_zero hN) k)
    q hq

/-- The plaquette in the `(0, 1)` plane at the origin.

DERIVED: `0`, `1` the two directions; `0` the origin. -/
def qo : IPlaq := (((0 : Fin 4), (1 : Fin 4)), (0 : ISite))

/-- **The identity flow fails `ClassMoments` on the symmetrised plaquette class**, for `N ≥ 2`, at
every `t`, `C`: `ExistenceFlow.not_classMoments_identity_poly` at the plaquette `((0, 1), 0)` and
`m = 2`, with the floor `stateK_plaq_ge`.

DERIVED: `0`, `1` the two directions and the origin; `2` the power of `β` and the least colour
count. -/
theorem not_classMoments_identity (hN2 : 2 ≤ N) (hN : N ≠ 0) (t C : ℝ) :
    ¬ MassGap.ObserverOSEuclidS.ClassMoments hN (MassGap.ContinuumFlow.ConfFlow.identity N)
      (MassGap.ObserverSymField.SymPlaqClass N) t C := by
  have hq : qo.1.1 ≠ qo.1.2 := by decide
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  exact MassGap.ExistenceFlow.not_classMoments_identity_poly hN qo
    (c := Real.exp (-(((boundaryPlaqs {(qo.1.1, qo.2)}).card : ℝ) * (16 / N + 2))) / N)
    (div_pos (Real.exp_pos _) hN') 2
    (Filter.Eventually.of_forall (fun k => stateK_plaq_ge hN2 hN qo hq k)) t C

end State

#print axioms two_ipRe_le
#print axioms density_mul_le
#print axioms density_mul_inv_le
#print axioms word_le
#print axioms action_le
#print axioms target_ge
#print axioms kernel_ge
#print axioms density_hTheta
#print axioms periodicState_plaq_ge
#print axioms stateK_plaq_ge
#print axioms not_classMoments_identity

end MassGap.PlaquetteFloor

end
