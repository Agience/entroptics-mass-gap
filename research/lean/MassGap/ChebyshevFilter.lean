import Mathlib

noncomputable section

/-!
# MassGap.ChebyshevFilter — a Chebyshev filter without the spectral theorem

The first piece of the conversion `BlockGapDef.WilsonConversion`: covariance decay at the square root of a
gap, from a polynomial filter, on a module with a symmetric positive semi-definite bilinear form and a
form-self-adjoint operator `H`, with no completion and no spectral calculus.

## Setting

`B` symmetric, `B x x ≥ 0`; `H` with `B (H x) y = B x (H y)`; the two-sided bound
`c ⟨Hy, y⟩ ≤ ⟨Hy, Hy⟩ ≤ K ⟨Hy, y⟩` at every `y` (the gap `c` and the norm `K` of `H` on its range),
`0 < c < K`. The weighted form `B_H (x, y) = B (H x) y` is symmetric and positive semi-definite.

## What it gives

1. **The moment inequality** (`moment_ineq`): `⟨H³y, y⟩ − (K + c) ⟨H²y, y⟩ + cK ⟨Hy, y⟩ ≤ 0`, i.e.
   `∫ λ (λ − c)(λ − K) ≤ 0`, from the gap at `(K − H) y` and the norm bound at `(H − c) y`, summed.
2. **The contraction** (`weighted_contract`): `M = α − βH`, `α = (K + c)/(K − c)`, `β = 2/(K − c)`, has
   `B_H (M y, M y) ≤ B_H (y, y)`.
3. **Chebyshev polynomials by the Pell recurrence.** `chebPair`: `a₀ = 1`, `b₀ = 0`,
   `aₙ₊₁ = X aₙ + (X² − 1) bₙ`, `bₙ₊₁ = aₙ + X bₙ` (`aₙ = Tₙ`, `bₙ = Uₙ₋₁`). `cheb_pell`:
   `aₙ² − (X² − 1) bₙ² = 1`. `natDegree_chebA`: `deg aₙ ≤ n`. `chebA_eval_ge`: at `x ≥ 1`,
   `aₙ(x) ≥ (x + √(x² − 1))ⁿ / 2`.
4. **The filter bound** (`filter_contract`): `N = aₙ(M)` has `B_H (N y, N y) ≤ B_H (y, y)` — the Pell
   identity `N² = 1 + (M² − 1) W²` and the contraction at `W y`.
5. **Covariance decay** (`chebyshev_cov`): for `f = f₀ + H y` with `H f₀ = 0`, and `g` with
   `B (Hʲ f) g = 0` for `1 ≤ j ≤ d` (a support at distance more than `d`):
   `B (H y) g² ≤ (2 / rᵈ)² · (B (H y) (H y) / c) · B (H g) g`, `r = α + √(α² − 1) > 1`.
   `chebR_eq`: `r = (√K + √c)/(√K − √c)`, and `one_add_two_sqrt_le_chebR`: `r ≥ 1 + 2√(c/K)`: the decay per
   application of `H` is at a rate of order `√(c/K)`, the square root of the gap.

DERIVED (module-wide): `0`, `1` the signs and the units; `2` the form's degree, the Pell factor and the
endpoint factor; `4` = `2²`.
-/

namespace MassGap.ChebyshevFilter

open Polynomial

/-! ## 1. Chebyshev polynomials through the Pell recurrence -/

/-- The pair `(aₙ, bₙ)`.

DERIVED: `1`, `0` the start; `2` the square in `X² − 1`. -/
def chebPair : ℕ → ℝ[X] × ℝ[X]
  | 0 => (1, 0)
  | n + 1 => (X * (chebPair n).1 + (X ^ 2 - 1) * (chebPair n).2, (chebPair n).1 + X * (chebPair n).2)

/-- `aₙ = Tₙ`. DERIVED: no numeral. -/
def chebA (n : ℕ) : ℝ[X] := (chebPair n).1

/-- `bₙ = Uₙ₋₁`. DERIVED: no numeral. -/
def chebB (n : ℕ) : ℝ[X] := (chebPair n).2

/-- **The Pell identity** `aₙ² − (X² − 1) bₙ² = 1`.

DERIVED: `2` the squares; `1` the unit. -/
theorem cheb_pell (n : ℕ) : chebA n ^ 2 - (X ^ 2 - 1) * chebB n ^ 2 = 1 := by
  induction n with
  | zero => simp [chebA, chebB, chebPair]
  | succ n ih =>
    simp only [chebA, chebB, chebPair] at ih ⊢
    linear_combination ih

#print axioms cheb_pell

/-- `deg b ≤ deg (X b)`. DERIVED: `1` the degree of `X`. -/
theorem natDegree_le_X_mul (p : ℝ[X]) : p.natDegree ≤ (X * p).natDegree := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [natDegree_X_mul hp]; omega

#print axioms natDegree_le_X_mul

/-- **Degrees**: `deg aₙ ≤ n` and `deg (X bₙ) ≤ n`.

DERIVED: `1` the step in degree. -/
theorem natDegree_cheb (n : ℕ) :
    (chebA n).natDegree ≤ n ∧ (X * chebB n).natDegree ≤ n := by
  induction n with
  | zero => simp [chebA, chebB, chebPair]
  | succ n ih =>
    obtain ⟨ha, hb⟩ := ih
    have hb' : (chebB n).natDegree ≤ n := (natDegree_le_X_mul _).trans hb
    have hXa : (X * chebA n).natDegree ≤ n + 1 :=
      (natDegree_mul_le).trans (by have := natDegree_X_le (R := ℝ); omega)
    have hXXb : (X * (X * chebB n)).natDegree ≤ n + 1 :=
      (natDegree_mul_le).trans (by have := natDegree_X_le (R := ℝ); omega)
    constructor
    · have e : chebA (n + 1) = X * chebA n + X * (X * chebB n) - chebB n := by
        simp only [chebA, chebB, chebPair]; ring
      rw [e]
      refine (natDegree_sub_le _ _).trans (max_le ((natDegree_add_le _ _).trans
        (max_le hXa hXXb)) (by omega))
    · have e : X * chebB (n + 1) = X * chebA n + X * (X * chebB n) := by
        simp only [chebA, chebB, chebPair]; ring
      rw [e]
      exact (natDegree_add_le _ _).trans (max_le hXa hXXb)

#print axioms natDegree_cheb

/-- `aₙ(x) + s bₙ(x) = (x + s)ⁿ` when `s² = x² − 1`.

DERIVED: `2` the square. -/
theorem cheb_eval_sum {x s : ℝ} (hs : s ^ 2 = x ^ 2 - 1) (n : ℕ) :
    (chebA n).eval x + s * (chebB n).eval x = (x + s) ^ n := by
  induction n with
  | zero => simp [chebA, chebB, chebPair]
  | succ n ih =>
    simp only [chebA, chebB, chebPair, eval_add, eval_mul, eval_X, eval_sub, eval_pow, eval_one]
      at ih ⊢
    linear_combination (x + s) * ih - (chebPair n).2.eval x * hs

#print axioms cheb_eval_sum

/-- **The lower bound** `aₙ(x) ≥ (x + √(x² − 1))ⁿ / 2` at `x ≥ 1`.

DERIVED: `1` the endpoint; `2` the factor of the two exponentials. -/
theorem chebA_eval_ge {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    (x + Real.sqrt (x ^ 2 - 1)) ^ n / 2 ≤ (chebA n).eval x := by
  set s := Real.sqrt (x ^ 2 - 1) with hsdef
  have hs : s ^ 2 = x ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsum := cheb_eval_sum hs n
  have hpell := congrArg (Polynomial.eval x) (cheb_pell n)
  simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_one] at hpell
  set A := (chebA n).eval x
  set Bv := (chebB n).eval x
  have hr : 0 < (x + s) ^ n := pow_pos (by linarith) n
  -- (A − s Bv)(A + s Bv) = 1, so A − s Bv > 0
  have hprod : (A - s * Bv) * (A + s * Bv) = 1 := by
    have : (A - s * Bv) * (A + s * Bv) = A ^ 2 - s ^ 2 * Bv ^ 2 := by ring
    rw [this, hs]; linarith
  have hdiff : 0 < A - s * Bv := by
    rw [hsum] at hprod
    by_contra hneg
    have hneg' := not_lt.mp hneg
    nlinarith
  linarith

#print axioms chebA_eval_ge

/-- The base `r = α + √(α² − 1)` at `α = (K + c)/(K − c)`.

DERIVED: `1`, `2` as in the Pell base. -/
def chebR (c K : ℝ) : ℝ := (K + c) / (K - c) + Real.sqrt (((K + c) / (K - c)) ^ 2 - 1)

/-- `1 ≤ α` at `0 < c < K`. DERIVED: `1` the endpoint. -/
theorem one_le_alpha {c K : ℝ} (hc : 0 < c) (hcK : c < K) : 1 ≤ (K + c) / (K - c) := by
  rw [le_div_iff₀ (by linarith)]; linarith

#print axioms one_le_alpha

/-- **The base in closed form**: `r = (√K + √c)/(√K − √c)` at `0 < c < K`.

DERIVED: `2` the squares; `4` = `2²`. -/
theorem chebR_eq {c K : ℝ} (hc : 0 < c) (hcK : c < K) :
    chebR c K = (Real.sqrt K + Real.sqrt c) / (Real.sqrt K - Real.sqrt c) := by
  have hK : 0 < K := hc.trans hcK
  have hsK := Real.sq_sqrt hK.le
  have hsc := Real.sq_sqrt hc.le
  have hpK := Real.sqrt_pos.mpr hK
  have hpc := Real.sqrt_pos.mpr hc
  have hlt : Real.sqrt c < Real.sqrt K := Real.sqrt_lt_sqrt hc.le hcK
  have hd : 0 < Real.sqrt K - Real.sqrt c := by linarith
  have hKc' : K - c = (Real.sqrt K - Real.sqrt c) * (Real.sqrt K + Real.sqrt c) := by
    nlinarith [hsK, hsc]
  have hKc : 0 < K - c := by linarith
  have hinner : ((K + c) / (K - c)) ^ 2 - 1 = (2 * Real.sqrt K * Real.sqrt c / (K - c)) ^ 2 := by
    rw [div_pow, div_pow, mul_pow, mul_pow, hsK, hsc]
    field_simp
    ring
  have hsq : Real.sqrt (((K + c) / (K - c)) ^ 2 - 1) = 2 * Real.sqrt K * Real.sqrt c / (K - c) := by
    rw [hinner, Real.sqrt_sq (by positivity)]
  unfold chebR
  have hsum : 0 < Real.sqrt K + Real.sqrt c := by linarith
  rw [hsq, ← add_div, hKc', div_eq_div_iff (by positivity) hd.ne']
  nlinarith [hsK, hsc]

#print axioms chebR_eq

/-- **The base grows with the square root of the gap**: `1 + 2√(c/K) ≤ r`.

DERIVED: `1`, `2` from `(1 + t)/(1 − t) ≥ 1 + 2t`. -/
theorem one_add_two_sqrt_le_chebR {c K : ℝ} (hc : 0 < c) (hcK : c < K) :
    1 + 2 * Real.sqrt (c / K) ≤ chebR c K := by
  have hK : 0 < K := hc.trans hcK
  have hpK := Real.sqrt_pos.mpr hK
  have hlt : Real.sqrt c < Real.sqrt K := Real.sqrt_lt_sqrt hc.le hcK
  have hpc := Real.sqrt_pos.mpr hc
  rw [chebR_eq hc hcK, Real.sqrt_div hc.le, le_div_iff₀ (by linarith)]
  set q := Real.sqrt c / Real.sqrt K with hqdef
  have hq : q * Real.sqrt K = Real.sqrt c := by rw [hqdef]; field_simp
  have hq0 : 0 ≤ q := by positivity
  nlinarith [hq, mul_nonneg hq0 hpc.le]

#print axioms one_add_two_sqrt_le_chebR

/-! ## 2. The weighted form and the contraction -/

section Filter

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (H : Module.End ℝ E)

/-- Every polynomial in a self-adjoint `H` is self-adjoint.

DERIVED: no numeral. -/
theorem aeval_selfAdj (hsa : ∀ x y, B (H x) y = B x (H y)) (p : ℝ[X]) (x y : E) :
    B (aeval H p x) y = B x (aeval H p y) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
    congr 1
    induction n generalizing x y with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, ih, hsa, ← Module.End.mul_apply, ← pow_succ',
        pow_succ]

#print axioms aeval_selfAdj

/-- **Moving polynomials across**: `B (p(H) x) (q(H) z) = B x ((p q)(H) z)`.

DERIVED: no numeral. -/
theorem aeval_move (hsa : ∀ x y, B (H x) y = B x (H y)) (p q : ℝ[X]) (x z : E) :
    B (aeval H p x) (aeval H q z) = B x (aeval H (p * q) z) := by
  rw [aeval_selfAdj B H hsa p, map_mul, Module.End.mul_apply]

#print axioms aeval_move

variable {B H}

/-- **The moment inequality** `⟨H³y, y⟩ − (K+c)⟨H²y, y⟩ + cK ⟨Hy, y⟩ ≤ 0`.

DERIVED: `0` the sign. -/
theorem moment_ineq (hsymm : ∀ x y, B x y = B y x) (hsa : ∀ x y, B (H x) y = B x (H y))
    {c K : ℝ} (hK : ∀ y, B (H y) (H y) ≤ K * B (H y) y) (hc : ∀ y, c * B (H y) y ≤ B (H y) (H y))
    (hcK : c < K) (y : E) :
    B (H (H y)) (H y) - (K + c) * B (H y) (H y) + c * K * B (H y) y ≤ 0 := by
  set v0 := y
  set v1 := H y
  set v2 := H (H y)
  have hz1 := hc (K • v0 - v1)
  have hz2 := hK (v1 - c • v0)
  simp only [map_sub, map_smul] at hz1 hz2
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at hz1 hz2
  -- relations from symmetry and self-adjointness
  have s1 : B v0 v1 = B v1 v0 := hsymm _ _
  have s2 : B v0 v2 = B v1 v1 := by rw [hsymm, hsa]
  have s3 : B v2 v0 = B v1 v1 := hsa _ _
  have s4 : B v1 v2 = B v2 v1 := hsymm _ _
  have hKc : 0 < K - c := by linarith
  have key : (K - c) * (B v2 v1 - (K + c) * B v1 v1 + c * K * B v1 v0) ≤ 0 := by
    nlinarith [hz1, hz2, s1, s2, s3, s4]
  by_contra hneg
  have hneg' := lt_of_not_ge hneg
  have := mul_pos hKc hneg'
  linarith

#print axioms moment_ineq

/-- The contraction polynomial `M = α − βX`.

DERIVED: `2` the numerator of `β`. -/
def Mpoly (c K : ℝ) : ℝ[X] := C ((K + c) / (K - c)) - C (2 / (K - c)) * X

/-- **The contraction in the weighted form**: `B_H (M y, M y) ≤ B_H (y, y)`.

DERIVED: `2`, `4` from `α² − 1 = 4cK/(K − c)²`. -/
theorem weighted_contract (hsymm : ∀ x y, B x y = B y x) (hsa : ∀ x y, B (H x) y = B x (H y))
    {c K : ℝ} (hK : ∀ y, B (H y) (H y) ≤ K * B (H y) y) (hc : ∀ y, c * B (H y) y ≤ B (H y) (H y))
    (_hc0 : 0 < c) (hcK : c < K) (y : E) :
    B (H (aeval H (Mpoly c K) y)) (aeval H (Mpoly c K) y) ≤ B (H y) y := by
  have hm := moment_ineq hsymm hsa hK hc hcK y
  have hMy : aeval H (Mpoly c K) y = ((K + c) / (K - c)) • y - (2 / (K - c)) • H y := by
    simp [Mpoly, Module.algebraMap_end_apply]
  rw [hMy]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  have s2 : B (H (H y)) y = B (H y) (H y) := hsa _ _
  have s1 : B (H y) (H y) = B (H y) (H y) := rfl
  have s3 : B (H y) y = B (H y) y := rfl
  have s4 : B (H (H y)) (H y) = B (H (H y)) (H y) := rfl
  have s5 : B (H y) (H y) = B (H y) (H y) := rfl
  have hKc : 0 < K - c := by linarith
  set m1 := B (H y) y
  set m2 := B (H y) (H y)
  set m3 := B (H (H y)) (H y)
  have e2 : B (H (H y)) y = m2 := s2
  rw [e2]
  -- α² m1 − 2αβ m2 + β² m3 − m1 = 4(m3 − (K+c) m2 + cK m1)/(K − c)²
  have hid : (K + c) / (K - c) * ((K + c) / (K - c) * m1 - 2 / (K - c) * m2)
      - 2 / (K - c) * ((K + c) / (K - c) * m2 - 2 / (K - c) * m3) - m1
      = 4 * (m3 - (K + c) * m2 + c * K * m1) / (K - c) ^ 2 := by
    field_simp
    ring
  have hneg : 4 * (m3 - (K + c) * m2 + c * K * m1) / (K - c) ^ 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  linarith [hid]

#print axioms weighted_contract

/-- **The filter contracts in the weighted form**: `N = aₙ(M)`, `B_H (N y, N y) ≤ B_H (y, y)`.

DERIVED: `2` the squares of the Pell identity. -/
theorem filter_contract (hsymm : ∀ x y, B x y = B y x) (hsa : ∀ x y, B (H x) y = B x (H y))
    {c K : ℝ} (hK : ∀ y, B (H y) (H y) ≤ K * B (H y) y) (hc : ∀ y, c * B (H y) y ≤ B (H y) (H y))
    (hc0 : 0 < c) (hcK : c < K) (n : ℕ) (y : E) :
    B (H (aeval H ((chebA n).comp (Mpoly c K)) y)) (aeval H ((chebA n).comp (Mpoly c K)) y)
      ≤ B (H y) y := by
  set Np := (chebA n).comp (Mpoly c K)
  set Wp := (chebB n).comp (Mpoly c K)
  set Mp := Mpoly c K
  have hpell : Np ^ 2 = 1 + (Mp ^ 2 - 1) * Wp ^ 2 := by
    have h := congrArg (fun p => p.comp Mp) (cheb_pell n)
    simp only [sub_comp, mul_comp, pow_comp, X_comp, one_comp] at h
    linear_combination h
  have hHa : ∀ (p : ℝ[X]) (u : E), H (aeval H p u) = aeval H (X * p) u := by
    intro p u
    rw [map_mul, aeval_X, Module.End.mul_apply]
  have hcompa : ∀ (p q : ℝ[X]) (u : E), aeval H p (aeval H q u) = aeval H (p * q) u := by
    intro p q u
    rw [map_mul, Module.End.mul_apply]
  set w := aeval H Wp y
  have e1 : B (H (aeval H Np y)) (aeval H Np y) = B y (aeval H (X * Np * Np) y) := by
    rw [hHa, aeval_move B H hsa]
  have e2 : B (H y) y = B y (aeval H (X : ℝ[X]) y) := by rw [hsa, aeval_X]
  have e3 : B (H (aeval H Mp w)) (aeval H Mp w) = B y (aeval H (X * (Mp * Wp) * (Mp * Wp)) y) := by
    rw [show w = aeval H Wp y from rfl, hcompa, hHa, aeval_move B H hsa]
  have e4 : B (H w) w = B y (aeval H (X * Wp * Wp) y) := by
    rw [show w = aeval H Wp y from rfl, hHa, aeval_move B H hsa]
  have hpoly : X * Np * Np = X + X * (Mp * Wp) * (Mp * Wp) - X * Wp * Wp := by
    linear_combination (X : ℝ[X]) * hpell
  have hcon := weighted_contract hsymm hsa hK hc hc0 hcK w
  rw [e1, hpoly, map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.map_sub,
    LinearMap.map_add, ← e2, ← e3, ← e4]
  linarith

#print axioms filter_contract

/-- Cauchy–Schwarz for a symmetric positive semi-definite bilinear form.

DERIVED: `2` the square; `4` the discriminant. -/
theorem form_cs (B' : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B' x y = B' y x) (hpsd : ∀ x, 0 ≤ B' x x)
    (u v : E) : B' u v ^ 2 ≤ B' u u * B' v v := by
  have hq : ∀ t : ℝ, 0 ≤ B' u u * (t * t) + (2 * B' u v) * t + B' v v := by
    intro t
    have h := hpsd (t • u + v)
    simp only [LinearMap.map_add, LinearMap.map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul] at h
    rw [hsymm v u] at h
    nlinarith [h]
  have hd := discrim_le_zero hq
  simp only [discrim] at hd
  nlinarith [hd]

#print axioms form_cs

/-- **The filter polynomial** `p = aₙ(M)/aₙ(α)`, `p(0) = 1`.

DERIVED: `1` the normalisation. -/
def filterPoly (c K : ℝ) (d : ℕ) : ℝ[X] :=
  C (1 / (chebA d).eval ((K + c) / (K - c))) * (chebA d).comp (Mpoly c K)

/-- `p(0) = 1`. DERIVED: `0`, `1`. -/
theorem filterPoly_eval_zero {c K : ℝ} (hc : 0 < c) (hcK : c < K) (d : ℕ) :
    (filterPoly c K d).eval 0 = 1 := by
  have hα1 := one_le_alpha hc hcK
  have hAge := chebA_eval_ge hα1 d
  have hApos : 0 < (chebA d).eval ((K + c) / (K - c)) :=
    lt_of_lt_of_le (by positivity) hAge
  simp only [filterPoly, eval_mul, eval_C, eval_comp, Mpoly, eval_sub, eval_X, mul_zero, sub_zero]
  field_simp

#print axioms filterPoly_eval_zero

/-- `deg p ≤ d`. DERIVED: `1` the degree of `M`. -/
theorem natDegree_filterPoly (c K : ℝ) (d : ℕ) : (filterPoly c K d).natDegree ≤ d := by
  have hdegA := (natDegree_cheb d).1
  have hdegM : (Mpoly c K).natDegree ≤ 1 := by
    unfold Mpoly
    refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
    exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  have hdegN : ((chebA d).comp (Mpoly c K)).natDegree ≤ d :=
    natDegree_comp_le.trans (by nlinarith)
  exact (natDegree_C_mul_le _ _).trans hdegN

#print axioms natDegree_filterPoly

/-- **Covariance decay at the square root of the gap.** See the module docstring, item 5.

DERIVED: `2` the endpoint factor and the squares; `1` the lower end of `j`. -/
theorem chebyshev_cov (hsymm : ∀ x y, B x y = B y x) (hpsd : ∀ x, 0 ≤ B x x)
    (hsa : ∀ x y, B (H x) y = B x (H y))
    {c K : ℝ} (hK : ∀ y, B (H y) (H y) ≤ K * B (H y) y) (hc : ∀ y, c * B (H y) y ≤ B (H y) (H y))
    (hc0 : 0 < c) (hcK : c < K) (d : ℕ) {f f₀ y g : E} (hfy : f = f₀ + H y) (hf₀ : H f₀ = 0)
    (hloc : ∀ j, 1 ≤ j → j ≤ d → B ((H ^ j) f) g = 0) :
    B (H y) g ^ 2 ≤ (2 / chebR c K ^ d) ^ 2 * (B (H y) (H y) / c) * B (H g) g := by
  have hα1 := one_le_alpha hc0 hcK
  have hAge := chebA_eval_ge hα1 d
  obtain ⟨A, hA⟩ : ∃ A, A = (chebA d).eval ((K + c) / (K - c)) := ⟨_, rfl⟩
  rw [← hA] at hAge
  have hAge' : chebR c K ^ d / 2 ≤ A := hAge
  have hr : 0 < chebR c K := by unfold chebR; positivity
  have hApos : 0 < A := lt_of_lt_of_le (by positivity) hAge'
  have hP0 := filterPoly_eval_zero hc0 hcK d
  have hcoeff : (1 - filterPoly c K d).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, eval_sub, eval_one, hP0, sub_self]
  have hdeg1P : (1 - filterPoly c K d).natDegree ≤ d :=
    (natDegree_sub_le _ _).trans (max_le (by simp) (natDegree_filterPoly c K d))
  have hloc1 : B (aeval H (1 - filterPoly c K d) f) g = 0 := by
    rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hdeg1P)]
    simp only [LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul, smul_eq_mul]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0, hcoeff, zero_mul]
    · rw [hloc j hpos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)), mul_zero]
  obtain ⟨Q, hQ⟩ := X_dvd_iff.mpr hcoeff
  have hkill : aeval H (1 - filterPoly c K d) f₀ = 0 := by
    rw [hQ, mul_comm, map_mul, Module.End.mul_apply, aeval_X, hf₀, map_zero]
  have hHy : H y = f - f₀ := by rw [hfy]; abel
  have hsplit : B (H y) g = B (aeval H (filterPoly c K d) (H y)) g := by
    have h1 : aeval H (1 - filterPoly c K d) (H y) = aeval H (1 - filterPoly c K d) f := by
      rw [hHy, map_sub, hkill, sub_zero]
    have h3 : H y = aeval H (filterPoly c K d) (H y) + aeval H (1 - filterPoly c K d) (H y) := by
      rw [map_sub, map_one, LinearMap.sub_apply, Module.End.one_apply]; abel
    calc B (H y) g
        = B (aeval H (filterPoly c K d) (H y) + aeval H (1 - filterPoly c K d) (H y)) g := by
          rw [← h3]
      _ = B (aeval H (filterPoly c K d) (H y)) g + B (aeval H (1 - filterPoly c K d) f) g := by
          rw [LinearMap.map_add, LinearMap.add_apply, h1]
      _ = B (aeval H (filterPoly c K d) (H y)) g := by rw [hloc1, add_zero]
  have hcomm : aeval H (filterPoly c K d) (H y) = H (aeval H (filterPoly c K d) y) := by
    have e : aeval H (filterPoly c K d * X) = aeval H (X * filterPoly c K d) := by rw [mul_comm]
    have h := congrArg (fun F : Module.End ℝ E => F y) e
    simp only [map_mul, aeval_X, Module.End.mul_apply] at h
    exact h
  let BH : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := B.comp H
  have hBH : ∀ x z, BH x z = B (H x) z := fun _ _ => rfl
  have hBHsymm : ∀ x z, BH x z = BH z x := by
    intro x z; rw [hBH, hBH, hsa, hsymm]
  have hBHpsd : ∀ x, 0 ≤ BH x x := by
    intro x
    rw [hBH]
    have h1 := hK x
    have h2 := hpsd (H x)
    have hK0 : 0 < K := hc0.trans hcK
    by_contra hneg
    have hneg' := lt_of_not_ge hneg
    nlinarith
  have hcs := form_cs BH hBHsymm hBHpsd (aeval H (filterPoly c K d) y) g
  rw [hBH, hBH, hBH] at hcs
  have huN : aeval H (filterPoly c K d) y = (1 / A) • aeval H ((chebA d).comp (Mpoly c K)) y := by
    rw [filterPoly, map_mul, aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply, ← hA]
  have hBu : B (H (aeval H (filterPoly c K d) y)) (aeval H (filterPoly c K d) y)
      = (1 / A) ^ 2 * B (H (aeval H ((chebA d).comp (Mpoly c K)) y))
          (aeval H ((chebA d).comp (Mpoly c K)) y) := by
    rw [huN]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hfc := filter_contract hsymm hsa hK hc hc0 hcK d y
  have hgap : B (H y) y ≤ B (H y) (H y) / c := by
    rw [le_div_iff₀ hc0, mul_comm]; exact hc y
  have hinvA : 1 / A ≤ 2 / chebR c K ^ d := by
    rw [div_le_div_iff₀ hApos (by positivity)]
    linarith [hAge']
  have hinvA0 : 0 ≤ 1 / A := by positivity
  have hsq : (1 / A) ^ 2 ≤ (2 / chebR c K ^ d) ^ 2 := pow_le_pow_left₀ hinvA0 hinvA 2
  have hg0 : 0 ≤ B (H g) g := hBHpsd g
  have hy0 : 0 ≤ B (H y) y := hBHpsd y
  rw [hsplit, hcomm]
  calc B (H (aeval H (filterPoly c K d) y)) g ^ 2
      ≤ B (H (aeval H (filterPoly c K d) y)) (aeval H (filterPoly c K d) y) * B (H g) g := hcs
    _ = (1 / A) ^ 2 * B (H (aeval H ((chebA d).comp (Mpoly c K)) y))
          (aeval H ((chebA d).comp (Mpoly c K)) y) * B (H g) g := by rw [hBu]
    _ ≤ (1 / A) ^ 2 * B (H y) y * B (H g) g := by gcongr
    _ ≤ (2 / chebR c K ^ d) ^ 2 * (B (H y) (H y) / c) * B (H g) g := by gcongr

#print axioms chebyshev_cov

end Filter

end MassGap.ChebyshevFilter
