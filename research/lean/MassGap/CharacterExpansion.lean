import Mathlib
import MassGap.ActionSplit

/-!
# MassGap.CharacterExpansion — paired expansion of the Wilson plaquette weight

This module expands `exp (β * Re tr (A Bᴴ))` into a sum of terms each of which is a function of `A`
times the same function of `B`, and derives from that expansion a positivity statement for a
reflection that inverts the gauge variable on the links whose direction it fixes.

## The expansion

`hsRe A B = Re tr (A Bᴴ)`. `hsRe_eq_sum` identifies it with the Euclidean inner product of the real
coordinate vectors of `A` and `B`, indexed by `Coord N = Fin N × Fin N × Bool`. `hsRe_pow` raises
that to a power: `hsRe A B ^ k` is the sum, over functions `α : Fin k → Coord N`, of
`mono α A * mono α B`, where `mono α` is the product of the coordinates `α` names. Each summand is a
function of `A` times the same function of `B`, and the sum carries no coefficients.

`hasSum_wilsonWeight_paired` sums those orders against `wilsonCoef β k = β ^ k / k !`, giving
`exp (β * hsRe A B)` as a `HasSum` over the paired expansion. `wilsonCoef_nonneg` gives the
coefficients a sign from `0 ≤ β`; `wilsonCoef_neg_of_neg` shows the order-one coefficient is negative
when `β < 0`.

Everything in this section is stated for arbitrary complex `N × N` matrices. No group, no Haar
measure and no representation theory enters: the monomial index `α` stands where the irreducible
characters would, and Peter-Weyl and Schur orthogonality are not used anywhere in this file.

## Positive semidefiniteness

`quadform_pow_eq_sum_sq` rewrites the order-`k` quadratic form `∑ᵢⱼ zᵢ zⱼ (hsRe Aᵢ Aⱼ) ^ k` as
`∑_α (∑ᵢ zᵢ * mono α Aᵢ) ^ 2`. `wilson_kernel_nonneg` sums the orders and concludes
`0 ≤ ∑ᵢⱼ zᵢ zⱼ exp (β * hsRe Aᵢ Aⱼ)` for `0 ≤ β`, for any finite family of matrices and any real
weights. It too is stated for arbitrary matrices; membership in a group is never used.

## Negative control

`NegControl` fixes two diagonal matrices, the identity and `diag(1, -1, -1)`, proves both lie in
`Matrix.specialUnitaryGroup (Fin 3) ℂ` (`cA_mem_SU`), and evaluates the quadratic form on them at the
weights `(1, -1)`: `su3_quadform` gives `2 * (exp (3 * β) - exp (-β))`, and `su3_kernel_nonneg_iff`
turns that into an equivalence with `0 ≤ β`. `su3_kernel_neg_of_neg` is the strict form at `β < 0`.
So the hypothesis `0 ≤ β` of `wilson_kernel_nonneg` cannot be dropped.

## Reflections that invert

`ReflectionPositivity.pairing_with_reflection_nonneg` and
`ReflectionPositivity.reflection_positive_of_expansion` are stated for a relabelling `U ∘ θ`.
`Reflect.reflConf` is not a relabelling: it is `ActionSplit.twist (reflLinkPerm τ c) (axisDagger τ)`
(`ActionSplit.reflConf_eq_twist`), which also inverts the gauge variable on every link running along
the reflection axis. `twisted_pairing_eq_sq` and `twisted_reflection_positive_of_expansion` restate
those two lemmas with `ActionSplit.twist θ σ` in place of `U ∘ θ`, using
`ActionSplit.twist_measurePreserving`.

## The two together

`crossweight_pairing_nonneg` pairs an observable `O` of one side `S` with its twisted reflection
against the weight `exp (β * hsRe (X (U|S)) (X ((twist θ σ U)|S)))`, where `X` is a matrix-valued
function of the configuration on `S` whose real coordinates are measurable and bounded by one. That
weight reads both sides at once, so it is not of the form a factorised weld consumes. The conclusion
is that the integral against `cvol ι μ` is nonnegative, for `0 ≤ β`.
`wilson_crossweight_pairing_nonneg` is the same statement at `ι = Link d n`,
`μ = probHaar (SUN.SU N)`, with `reflConf τ cst` as the reflection.

`odd_lag_straddling_plaq_two_fixed_axis_links` exhibits, at even extent and odd lag, a plaquette in a
`(τ, ν)` plane two of whose boundary links are distinct axis links that `reflLink τ c` fixes.
`plaqReflPositive_of_pairing_nonneg` divides the un-normalised pairing integral by the partition
function, positive by `WilsonReal.wilsonSystem_partition_pos` when `N ≠ 0`, to obtain
`ReflectPositive.PlaqReflPositive`.

Foundational footprint only (`#print axioms` at the end).
Build: `python code/lean_build.py build MassGap.CharacterExpansion`.
-/

namespace MassGap.CharacterExpansion

open MeasureTheory
open MassGap MassGap.ActionSplit MassGap.WilsonAction MassGap.WilsonLattice
open MassGap.WilsonHypercubic MassGap.CompactGauge MassGap.Reflect

/-! ## `Re tr (A Bᴴ)` is a real inner product

`hsRe A B = Re tr (A Bᴴ)`, which for unitary `B` is `Re tr (A B⁻¹)` — the form a plaquette holonomy
takes when its boundary word is cut into a factor `A` and a factor `B`. `hsRe_eq_sum` identifies it
with the Euclidean inner product on the real coordinates of a complex matrix, and `hsRe_pow` uses
that to split every power into paired monomials. -/

/-- A real coordinate of a complex `N × N` matrix: a row index, a column index, and a `Bool`
selecting the real or the imaginary part. The type has `2 * N ^ 2` elements.

DERIVED: no numeral appears in the statement. -/
abbrev Coord (N : ℕ) : Type := Fin N × Fin N × Bool

/-- The value of that coordinate: the real part of the entry when the `Bool` is `true`, the
imaginary part when it is `false`.

DERIVED: the digits in `p.1`, `p.2.1` and `p.2.2` are projections out of the triple `Coord N`,
selecting the row index, the column index and the part flag. No other numeral appears. -/
noncomputable def coord {N : ℕ} (p : Coord N) (A : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  if p.2.2 then (A p.1 p.2.1).re else (A p.1 p.2.1).im

/-- The cross form `Re tr (A Bᴴ)`. For `A` and `B` unitary, `Bᴴ = B⁻¹`, so this is the real part of
the trace of the word `A B⁻¹`.

DERIVED: no numeral appears in the statement. -/
noncomputable def hsRe {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (Matrix.trace (A * Matrix.conjTranspose B)).re

/-- `Re tr (A Bᴴ)` is the sum over `Coord N` of the product of the two matrices' coordinates.

`tr (A Bᴴ) = ∑ᵢⱼ Aᵢⱼ · conj Bᵢⱼ`, whose real part is `∑ᵢⱼ (Re Aᵢⱼ Re Bᵢⱼ + Im Aᵢⱼ Im Bᵢⱼ)`: the
Euclidean inner product of the coordinate vectors. This is what makes every power of `hsRe` split
into products of a function of `A` with the same function of `B`.

DERIVED: no numeral appears in the statement. -/
theorem hsRe_eq_sum {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) :
    hsRe A B = ∑ p : Coord N, coord p A * coord p B := by
  have hL : hsRe A B = ∑ i : Fin N, ∑ j : Fin N,
      ((A i j).re * (B i j).re + (A i j).im * (B i j).im) := by
    have htr : Matrix.trace (A * Matrix.conjTranspose B)
        = ∑ i : Fin N, (A * Matrix.conjTranspose B) i i := rfl
    unfold hsRe
    rw [htr, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Matrix.conjTranspose_apply, Complex.mul_re]
    simp only [Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have hR : (∑ p : Coord N, coord p A * coord p B)
      = ∑ i : Fin N, ∑ j : Fin N,
        ((A i j).re * (B i j).re + (A i j).im * (B i j).im) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Fintype.sum_bool]
    simp [coord]
  rw [hL, hR]

/-- A degree-`k` monomial in the real coordinates of a matrix: the product, over `t : Fin k`, of the
coordinate `α t`.

DERIVED: no numeral appears in the statement. -/
noncomputable def mono {N k : ℕ} (α : Fin k → Coord N) (A : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ∏ t, coord (α t) A

/-- The `k`-th power of `hsRe A B`, expanded: it is the sum over functions `α : Fin k → Coord N` of
`mono α A * mono α B`.

Every summand is a function of `A` times the same function of `B`, and the index ranges over a
`Fintype`, so the sum is finite. Proved from `hsRe_eq_sum` by `Fintype.sum_pow`, which is where the
index `α` comes from.

DERIVED: no numeral appears in the statement; the exponent is the variable `k`. -/
theorem hsRe_pow {N : ℕ} (k : ℕ) (A B : Matrix (Fin N) (Fin N) ℂ) :
    hsRe A B ^ k = ∑ α : Fin k → Coord N, mono α A * mono α B := by
  rw [hsRe_eq_sum, Fintype.sum_pow]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  unfold mono
  rw [← Finset.prod_mul_distrib]

/-! ## The Wilson weight, and its coefficients -/

/-- The exponential series, as a `HasSum`: `fun k => x ^ k / k !` sums to `Real.exp x`. Restated
from `NormedSpace.expSeries_div_hasSum_exp`.

DERIVED: no numeral appears in the statement. -/
theorem hasSum_exp_div (x : ℝ) :
    HasSum (fun k : ℕ => x ^ k / (Nat.factorial k : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

/-- The coefficient carried at order `k`: `β ^ k / k !`.

DERIVED: no numeral appears in the statement. -/
noncomputable def wilsonCoef (β : ℝ) (k : ℕ) : ℝ := β ^ k / (Nat.factorial k : ℝ)

/-- For `0 ≤ β` every coefficient is nonnegative.

DERIVED: both numerals are the `0` of a sign condition — one in the hypothesis on `β`, one in the
conclusion about `wilsonCoef β k`. Neither is a magnitude. -/
theorem wilsonCoef_nonneg {β : ℝ} (hβ : 0 ≤ β) (k : ℕ) : 0 ≤ wilsonCoef β k :=
  div_nonneg (pow_nonneg hβ k) (Nat.cast_nonneg _)

/-- At `β < 0` the order-one coefficient is negative, so the hypothesis of `wilsonCoef_nonneg` is
not vacuous.

DERIVED: the two `0`s are sign conditions, on `β` and on the coefficient. The `1` is the order at
which the coefficient is read — an index into the series, and the lowest order at which `β` occurs to
an odd power. -/
theorem wilsonCoef_neg_of_neg {β : ℝ} (hβ : β < 0) : wilsonCoef β 1 < 0 := by
  unfold wilsonCoef
  simpa using hβ

/-- The Wilson weight is the sum of its own paired expansion:

    exp (β · Re tr (A Bᴴ))  =  ∑ₖ  (β^k / k!) · ∑_α  mono α A · mono α B.

Each order is `hsRe_pow`; the series is `hasSum_exp_div` at `β * hsRe A B`. Stated for arbitrary
complex matrices `A` and `B`, with no hypothesis on `β` — the sign of the coefficients is
`wilsonCoef_nonneg`, which needs `0 ≤ β`. This is the shape
`ReflectionPositivity.reflection_positive_of_expansion` and
`twisted_reflection_positive_of_expansion` consume.

DERIVED: no numeral appears in the statement. -/
theorem hasSum_wilsonWeight_paired {N : ℕ} (β : ℝ) (A B : Matrix (Fin N) (Fin N) ℂ) :
    HasSum (fun k : ℕ => wilsonCoef β k * ∑ α : Fin k → Coord N, mono α A * mono α B)
      (Real.exp (β * hsRe A B)) := by
  have heq : (fun k : ℕ => wilsonCoef β k * ∑ α : Fin k → Coord N, mono α A * mono α B)
      = fun k : ℕ => (β * hsRe A B) ^ k / (Nat.factorial k : ℝ) := by
    funext k
    rw [← hsRe_pow, wilsonCoef, mul_pow]
    ring
  rw [heq]
  exact hasSum_exp_div (β * hsRe A B)

/-! ## Positive semidefiniteness

`quadform_pow_eq_sum_sq` writes the order-`k` quadratic form as an explicit sum of squares, and
`wilson_kernel_nonneg` sums the orders against the coefficients. -/

/-- The order-`k` quadratic form is a sum of squares:

    ∑_α ( ∑ᵢ zᵢ · mono α Aᵢ )²  =  ∑ᵢⱼ zᵢ zⱼ (Re tr (Aᵢ Aⱼᴴ))^k

`A` is a family of `m` matrices and `z` a family of `m` reals. The proof expands each square by
`Finset.sum_mul_sum`, exchanges the sums so that `α` is innermost, and applies `hsRe_pow`.

DERIVED: the `2` is the exponent of the square on the left. `k` and `m` are variables, not
numerals. -/
theorem quadform_pow_eq_sum_sq {N : ℕ} (k m : ℕ) (A : Fin m → Matrix (Fin N) (Fin N) ℂ)
    (z : Fin m → ℝ) :
    (∑ α : Fin k → Coord N, (∑ i, z i * mono α (A i)) ^ 2)
      = ∑ i, ∑ j, z i * z j * hsRe (A i) (A j) ^ k := by
  have hR : ∀ α : Fin k → Coord N, (∑ i, z i * mono α (A i)) ^ 2
      = ∑ i, ∑ j, (z i * mono α (A i)) * (z j * mono α (A j)) := by
    intro α
    rw [sq, Finset.sum_mul_sum]
  calc (∑ α : Fin k → Coord N, (∑ i, z i * mono α (A i)) ^ 2)
      = ∑ α : Fin k → Coord N, ∑ i, ∑ j, (z i * mono α (A i)) * (z j * mono α (A j)) :=
        Finset.sum_congr rfl (fun α _ => hR α)
    _ = ∑ i, ∑ α : Fin k → Coord N, ∑ j, (z i * mono α (A i)) * (z j * mono α (A j)) :=
        Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ α : Fin k → Coord N, (z i * mono α (A i)) * (z j * mono α (A j)) :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ i, ∑ j, z i * z j * hsRe (A i) (A j) ^ k := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [hsRe_pow, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun α _ => by ring)

/-- For `0 ≤ β`, `0 ≤ ∑ᵢⱼ zᵢ zⱼ exp (β · Re tr (Aᵢ Aⱼᴴ))` for any finite family of matrices `A`
and any real weights `z`.

Each order of the series is a nonnegative coefficient (`wilsonCoef_nonneg`) times a sum of squares
(`quadform_pow_eq_sum_sq`); `hasSum_exp_div` sums the orders and `tsum_nonneg` concludes.

Stated for arbitrary complex `N × N` matrices — no group membership is assumed or used — so it
applies in particular to elements of `specialUnitaryGroup` and to words built from them. The only
hypothesis is `0 ≤ β`, and `NegControl.su3_kernel_nonneg_iff` shows it cannot be dropped.

DERIVED: both numerals are the `0` of a sign condition — the hypothesis `0 ≤ β` and the conclusion
`0 ≤ ∑ …`. Neither is a magnitude. -/
theorem wilson_kernel_nonneg {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) {m : ℕ}
    (A : Fin m → Matrix (Fin N) (Fin N) ℂ) (z : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, z i * z j * Real.exp (β * hsRe (A i) (A j)) := by
  have hterm : ∀ i j, HasSum
      (fun k : ℕ => wilsonCoef β k * (z i * z j * hsRe (A i) (A j) ^ k))
      (z i * z j * Real.exp (β * hsRe (A i) (A j))) := by
    intro i j
    have heq : (fun k : ℕ => wilsonCoef β k * (z i * z j * hsRe (A i) (A j) ^ k))
        = fun k : ℕ => (z i * z j) * ((β * hsRe (A i) (A j)) ^ k / (Nat.factorial k : ℝ)) := by
      funext k
      rw [wilsonCoef, mul_pow]
      ring
    rw [heq]
    exact (hasSum_exp_div (β * hsRe (A i) (A j))).mul_left (z i * z j)
  have hsum : HasSum
      (fun k : ℕ => ∑ i, ∑ j, wilsonCoef β k * (z i * z j * hsRe (A i) (A j) ^ k))
      (∑ i, ∑ j, z i * z j * Real.exp (β * hsRe (A i) (A j))) :=
    hasSum_sum (fun i _ => hasSum_sum (fun j _ => hterm i j))
  have hnn : ∀ k : ℕ,
      0 ≤ ∑ i, ∑ j, wilsonCoef β k * (z i * z j * hsRe (A i) (A j) ^ k) := by
    intro k
    have h1 : (∑ i, ∑ j, wilsonCoef β k * (z i * z j * hsRe (A i) (A j) ^ k))
        = wilsonCoef β k * ∑ i, ∑ j, z i * z j * hsRe (A i) (A j) ^ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
    rw [h1, ← quadform_pow_eq_sum_sq]
    exact mul_nonneg (wilsonCoef_nonneg hβ k)
      (Finset.sum_nonneg (fun α _ => sq_nonneg _))
  rw [← hsum.tsum_eq]
  exact tsum_nonneg hnn

#print axioms hsRe_eq_sum
#print axioms hsRe_pow
#print axioms hasSum_wilsonWeight_paired
#print axioms quadform_pow_eq_sum_sq
#print axioms wilson_kernel_nonneg

/-! ## Negative control

The lemmas above would read the same for any weight of the form `exp (β · ⟨A, B⟩)`. What the sign of
`β` decides is computed here on two explicit elements of `Matrix.specialUnitaryGroup (Fin 3) ℂ`: the
quadratic form is nonnegative exactly when `0 ≤ β`, and strictly negative below it. -/

namespace NegControl

/-- A diagonal matrix whose entries satisfy `d i * star (d i) = 1` and whose entries multiply to `1`
lies in `Matrix.specialUnitaryGroup (Fin N) ℂ`. The first hypothesis gives unitarity through
`Matrix.diagonal_mul_diagonal`, the second gives determinant one through `Matrix.det_diagonal`.

DERIVED: both numerals are `1`. The first is the unit of `ℂ` in the unit-modulus condition on each
entry; the second is the unit determinant that distinguishes `SU` from `U`. -/
theorem diagonal_mem_SU {N : ℕ} (d : Fin N → ℂ)
    (h1 : ∀ i, d i * star (d i) = 1) (h2 : ∏ i, d i = 1) :
    Matrix.diagonal d ∈ Matrix.specialUnitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    have hfun : (fun i => d i * (star d : Fin N → ℂ) i) = (1 : Fin N → ℂ) := by
      funext i
      rw [Pi.star_apply]
      exact h1 i
    rw [hfun]
    simp
  · rw [Matrix.det_diagonal, h2]

/-- `hsRe` of two diagonal matrices is the sum over the diagonal of `Re (d i * conj (e i))`.

DERIVED: no numeral appears in the statement. -/
theorem hsRe_diagonal {N : ℕ} (d e : Fin N → ℂ) :
    hsRe (Matrix.diagonal d) (Matrix.diagonal e) = ∑ i, (d i * (starRingEnd ℂ) (e i)).re := by
  unfold hsRe
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,
    Complex.re_sum]
  rfl

/-- The two diagonal vectors of the control: the constant vector `1`, and `(1, -1, -1)`. Membership
in `SU(3)` is not asserted here — `cA_mem_SU` proves it, by feeding these entries to
`diagonal_mem_SU`.

DERIVED: `2` is the number of control elements, indexing the outer vector; `3` is the matrix size,
indexing each inner vector. The entries `1` and `-1` are unit-modulus complex numbers whose product
along each row is `1`, which is the determinant condition; the second row is the shortest entry
pattern over `{1, -1}` that satisfies it and is not the identity. -/
noncomputable def dvec : Fin 2 → (Fin 3 → ℂ) := ![![1, 1, 1], ![1, -1, -1]]

/-- The two control matrices, diagonal over `dvec`.

DERIVED: `2` indexes the two control elements and `3` is the matrix size, both carried over from
`dvec`. -/
noncomputable def cA (i : Fin 2) : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (dvec i)

/-- Both control matrices lie in `Matrix.specialUnitaryGroup (Fin 3) ℂ`, by `diagonal_mem_SU` with
the two conditions discharged by `fin_cases` on both indices.

DERIVED: `2` indexes the two control elements; `3` is the matrix size, the same one as in `cA`. -/
theorem cA_mem_SU (i : Fin 2) : cA i ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  refine diagonal_mem_SU (dvec i) ?_ ?_
  · intro j
    fin_cases i <;> fin_cases j <;> norm_num [dvec]
  · fin_cases i <;> norm_num [dvec, Fin.prod_univ_succ]

/-- The weights of the control vector: `1` on the first element, `-1` on the second.

DERIVED: `2` is the number of elements being weighted. The entries `1` and `-1` are the two signs; a
pair of opposite signs is what a quadratic form has to survive, and these are the units of `ℝ`. -/
def zc : Fin 2 → ℝ := ![1, -1]

theorem hsRe_cA_zero_zero : hsRe (cA 0) (cA 0) = 3 := by
  simp only [cA, hsRe_diagonal]
  norm_num [dvec, Fin.sum_univ_succ]

theorem hsRe_cA_zero_one : hsRe (cA 0) (cA 1) = -1 := by
  simp only [cA, hsRe_diagonal]
  norm_num [dvec, Fin.sum_univ_succ]

theorem hsRe_cA_one_zero : hsRe (cA 1) (cA 0) = -1 := by
  simp only [cA, hsRe_diagonal]
  norm_num [dvec, Fin.sum_univ_succ]

theorem hsRe_cA_one_one : hsRe (cA 1) (cA 1) = 3 := by
  simp only [cA, hsRe_diagonal]
  norm_num [dvec, Fin.sum_univ_succ]

/-- The quadratic form on the two control matrices at the weights `zc`, evaluated:
`2 * (exp (3 * β) - exp (-β))`. The four values of `hsRe` it rests on are `hsRe_cA_zero_zero`,
`hsRe_cA_zero_one`, `hsRe_cA_one_zero` and `hsRe_cA_one_one`.

DERIVED: the leading `2` is a multiplicity — the two diagonal terms are equal and so are the two
off-diagonal ones. The `3` inside the first exponential is the common value of `hsRe (cA i) (cA i)`,
the trace of a `3 × 3` identity. -/
theorem su3_quadform (β : ℝ) :
    (∑ i, ∑ j, zc i * zc j * Real.exp (β * hsRe (cA i) (cA j)))
      = 2 * (Real.exp (3 * β) - Real.exp (-β)) := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  rw [hsRe_cA_zero_zero, hsRe_cA_zero_one, hsRe_cA_one_zero, hsRe_cA_one_one]
  simp only [zc, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show β * (3 : ℝ) = 3 * β by ring, show β * (-1 : ℝ) = -β by ring]
  ring

/-- On the two control matrices the quadratic form is nonnegative if and only if `0 ≤ β`. Both
directions go through `Real.exp_le_exp` applied to `su3_quadform`.

So the hypothesis `0 ≤ β` of `wilson_kernel_nonneg` is load-bearing: at `β < 0` the same weight on
the same two group elements with the same weights gives a negative value, and the order-one
coefficient is negative (`wilsonCoef_neg_of_neg`).

DERIVED: both numerals are the `0` of a sign condition — one on the quadratic form, one on `β`. -/
theorem su3_kernel_nonneg_iff (β : ℝ) :
    0 ≤ (∑ i, ∑ j, zc i * zc j * Real.exp (β * hsRe (cA i) (cA j))) ↔ 0 ≤ β := by
  rw [su3_quadform]
  constructor
  · intro h
    have h1 : Real.exp (-β) ≤ Real.exp (3 * β) := by linarith
    have h2 : -β ≤ 3 * β := Real.exp_le_exp.mp h1
    linarith
  · intro h
    have h2 : -β ≤ 3 * β := by linarith
    have h1 : Real.exp (-β) ≤ Real.exp (3 * β) := Real.exp_le_exp.mpr h2
    linarith

/-- The strict form: at `β < 0` the quadratic form on the two control matrices is strictly negative.

DERIVED: both numerals are the `0` of a sign condition, one on `β` and one on the form. -/
theorem su3_kernel_neg_of_neg {β : ℝ} (hβ : β < 0) :
    (∑ i, ∑ j, zc i * zc j * Real.exp (β * hsRe (cA i) (cA j))) < 0 := by
  by_contra h
  exact absurd ((su3_kernel_nonneg_iff β).mp (not_lt.mp h)) (not_le.mpr hβ)

#print axioms cA_mem_SU
#print axioms su3_quadform
#print axioms su3_kernel_nonneg_iff
#print axioms su3_kernel_neg_of_neg

end NegControl

/-! ## The same two lemmas, for a twist

`ReflectionPositivity.pairing_with_reflection_nonneg` and
`ReflectionPositivity.reflection_positive_of_expansion` are stated for the relabelling `U ∘ θ`.
`Reflect.reflConf` is `ActionSplit.twist (reflLinkPerm τ c) (axisDagger τ)`
(`ActionSplit.reflConf_eq_twist`), which also inverts the gauge variable on every link running along
the reflection axis, so neither lemma applies to it as stated.

The two statements below are those lemmas with `ActionSplit.twist θ σ` in place of `U ∘ θ`. The
argument is unchanged: `ActionSplit.twist_measurePreserving` supplies coordinatewise measure
preservation, which is what the mirror step uses. -/

section Twisted

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- A function of the coordinates in `S`, paired with its value on the twisted configuration,
integrates to the square of its own integral.

`S` and `T` are disjoint and `θ` carries `S` into `T`, so the two factors read disjoint coordinates
and `block_factor` splits the integral. Each `σ i` is measure-preserving, so the mirrored factor has
the same integral as the original. `h` is required measurable; no bound on it is needed, since the
measure is a probability measure.

DERIVED: the `2` is the exponent of the square on the right-hand side. -/
theorem twisted_pairing_eq_sq
    (S T : Finset ι) (hST : Disjoint S T) (θ : Equiv.Perm ι) (σ : ι → Ω → Ω)
    (hσ : ∀ i, MeasurePreserving (σ i) μ μ) (hθST : ∀ i ∈ S, θ i ∈ T)
    (h : (S → Ω) → ℝ) (hm : Measurable h) :
    (∫ U, h (fun i : S => U (i : ι)) * h (fun i : S => twist θ σ U (i : ι)) ∂(cvol ι μ))
      = (∫ U, h (fun i : S => U (i : ι)) ∂(cvol ι μ)) ^ 2 := by
  set ψ : (T → Ω) → ℝ :=
    fun v => h (fun i : S => σ (i : ι) (v ⟨θ (i : ι), hθST (i : ι) i.2⟩)) with hψ
  have hψm : Measurable ψ := by
    refine hm.comp (measurable_pi_lambda _ (fun i => ?_))
    exact (hσ (i : ι)).measurable.comp (measurable_pi_apply _)
  have hrw : ∀ U : ι → Ω,
      h (fun i : S => twist θ σ U (i : ι)) = ψ (fun i : T => U (i : ι)) := fun _ => rfl
  have hgm : Measurable (fun U : ι → Ω => h (fun i : S => U (i : ι))) :=
    hm.comp (measurable_pi_lambda _ (fun i => measurable_pi_apply (i : ι)))
  have hmp := twist_measurePreserving μ θ σ hσ
  have hmap : (∫ U, h (fun i : S => U (i : ι)) ∂(Measure.map (twist θ σ) (cvol ι μ)))
      = ∫ U, h (fun i : S => twist θ σ U (i : ι)) ∂(cvol ι μ) :=
    MeasureTheory.integral_map hmp.measurable.aemeasurable
      (by rw [hmp.map_eq]; exact hgm.aestronglyMeasurable)
  rw [hmp.map_eq] at hmap
  have hmirror : (∫ U, ψ (fun i : T => U (i : ι)) ∂(cvol ι μ))
      = ∫ U, h (fun i : S => U (i : ι)) ∂(cvol ι μ) := by
    calc (∫ U, ψ (fun i : T => U (i : ι)) ∂(cvol ι μ))
        = ∫ U, h (fun i : S => twist θ σ U (i : ι)) ∂(cvol ι μ) :=
          integral_congr_ae (Filter.Eventually.of_forall (fun U => (hrw U).symm))
      _ = ∫ U, h (fun i : S => U (i : ι)) ∂(cvol ι μ) := hmap.symm
  have hfac := block_factor μ S T hST h ψ hm hψm
  calc (∫ U, h (fun i : S => U (i : ι)) * h (fun i : S => twist θ σ U (i : ι)) ∂(cvol ι μ))
      = ∫ U, h (fun i : S => U (i : ι)) * ψ (fun i : T => U (i : ι)) ∂(cvol ι μ) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun U => by simp only [hrw U]))
    _ = (∫ U, h (fun i : S => U (i : ι)) ∂(cvol ι μ))
          * (∫ U, ψ (fun i : T => U (i : ι)) ∂(cvol ι μ)) := hfac
    _ = (∫ U, h (fun i : S => U (i : ι)) ∂(cvol ι μ)) ^ 2 := by rw [hmirror]; ring

/-- A finite expansion into paired products with nonnegative coefficients integrates to something
nonnegative, under a twisted reflection.

`hF` supplies `F` as `∑ k, c k * (g k (U|S) * g k ((twist θ σ U)|S))` over a `Fintype` index `K`,
with `0 ≤ c k` and each term integrable. Each term's integral is a square by
`twisted_pairing_eq_sq`, so the sum is nonnegative. This is
`ReflectionPositivity.reflection_positive_of_expansion` with the twist in place of the relabelling,
and it is the shape `hasSum_wilsonWeight_paired` produces order by order.

DERIVED: both numerals are the `0` of a sign condition — the hypothesis `0 ≤ c k` on every
coefficient and the conclusion `0 ≤ ∫ …`. -/
theorem twisted_reflection_positive_of_expansion
    (S T : Finset ι) (hST : Disjoint S T) (θ : Equiv.Perm ι) (σ : ι → Ω → Ω)
    (hσ : ∀ i, MeasurePreserving (σ i) μ μ) (hθST : ∀ i ∈ S, θ i ∈ T)
    {K : Type} [Fintype K] (c : K → ℝ) (hc : ∀ k, 0 ≤ c k)
    (g : K → (S → Ω) → ℝ) (hg : ∀ k, Measurable (g k))
    (hint : ∀ k, Integrable
      (fun U => g k (fun i : S => U (i : ι)) * g k (fun i : S => twist θ σ U (i : ι)))
      (cvol ι μ))
    (F : (ι → Ω) → ℝ)
    (hF : ∀ U, F U = ∑ k, c k *
      (g k (fun i : S => U (i : ι)) * g k (fun i : S => twist θ σ U (i : ι)))) :
    0 ≤ ∫ U, F U ∂(cvol ι μ) := by
  have hrw : (∫ U, F U ∂(cvol ι μ))
      = ∑ k, c k * ∫ U, g k (fun i : S => U (i : ι))
          * g k (fun i : S => twist θ σ U (i : ι)) ∂(cvol ι μ) := by
    simp_rw [hF]
    rw [integral_finset_sum _ (fun k _ => (hint k).const_mul (c k))]
    exact Finset.sum_congr rfl (fun k _ => integral_const_mul _ _)
  rw [hrw]
  refine Finset.sum_nonneg (fun k _ => mul_nonneg (hc k) ?_)
  rw [twisted_pairing_eq_sq μ S T hST θ σ hσ hθST (g k) (hg k)]
  exact sq_nonneg _

end Twisted

/-! ## A cross weight that reads both sides

A weld that conditions on the reflection plane needs the weight to factor into a function of one
side, a function of the other and a function of the plane. `crossweight_pairing_nonneg` allows a
weight that does not: `exp (β · Re tr (X₊ · X₋ᴴ))` with `X₋` the value of the same word on the
reflected configuration. The proof expands the weight order by order into paired monomials with
nonnegative coefficients (`hasSum_wilsonWeight_paired`), makes each order a square
(`twisted_pairing_eq_sq`), and sums the orders by dominated convergence against a bound that does not
depend on the configuration. -/

/-- A monomial in the coordinates of a matrix-valued function is measurable when each coordinate is:
`mono` is a finite product, so `Finset.measurable_prod` applies.

DERIVED: no numeral appears in the statement. -/
theorem measurable_mono {N k : ℕ} {γ : Type} [MeasurableSpace γ]
    (X : γ → Matrix (Fin N) (Fin N) ℂ)
    (hX : ∀ p : Coord N, Measurable (fun v => coord p (X v))) (α : Fin k → Coord N) :
    Measurable (fun v => mono α (X v)) := by
  unfold mono
  exact Finset.measurable_prod _ (fun t _ => hX (α t))

/-- A monomial in coordinates of absolute value at most one has absolute value at most one. `mono`
is a product over `Fin k`, bounded termwise by `Finset.prod_le_prod`. For a matrix in `SU N` the
hypothesis is supplied by `SUN.unitary_entry_norm_le_one`.

DERIVED: both numerals are the `1` bounding an absolute value — the hypothesis on each coordinate and
the conclusion on the monomial. The two are the same bound, because a product of factors bounded by
one is bounded by one, whatever the degree `k`. -/
theorem abs_mono_le_one {N k : ℕ} {γ : Type} (X : γ → Matrix (Fin N) (Fin N) ℂ)
    (hXb : ∀ (p : Coord N) (v : γ), |coord p (X v)| ≤ 1) (α : Fin k → Coord N) (v : γ) :
    |mono α (X v)| ≤ 1 := by
  unfold mono
  rw [Finset.abs_prod]
  calc (∏ t, |coord (α t) (X v)|) ≤ ∏ _t : Fin k, (1 : ℝ) :=
        Finset.prod_le_prod (fun t _ => abs_nonneg _) (fun t _ => hXb (α t) v)
    _ = 1 := by simp

/-- The observable of one side times a monomial of that side's matrix word. These are the functions
`twisted_reflection_positive_of_expansion` takes as its `g k`, and they read the coordinates in `S`
alone.

DERIVED: no numeral appears in the statement. -/
noncomputable def halfFun {N k : ℕ} {γ : Type} (O : γ → ℝ)
    (X : γ → Matrix (Fin N) (Fin N) ℂ) (α : Fin k → Coord N) : γ → ℝ :=
  fun v => O v * mono α (X v)

theorem measurable_halfFun {N k : ℕ} {γ : Type} [MeasurableSpace γ] {O : γ → ℝ}
    (hOm : Measurable O) {X : γ → Matrix (Fin N) (Fin N) ℂ}
    (hXm : ∀ p : Coord N, Measurable (fun v => coord p (X v))) (α : Fin k → Coord N) :
    Measurable (halfFun O X α) :=
  hOm.mul (measurable_mono X hXm α)

theorem abs_halfFun_le {N k : ℕ} {γ : Type} {O : γ → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hCb : ∀ v, |O v| ≤ C) {X : γ → Matrix (Fin N) (Fin N) ℂ}
    (hXb : ∀ (p : Coord N) (v : γ), |coord p (X v)| ≤ 1) (α : Fin k → Coord N) (v : γ) :
    |halfFun O X α v| ≤ C := by
  unfold halfFun
  rw [abs_mul]
  calc |O v| * |mono α (X v)| ≤ C * 1 :=
        mul_le_mul (hCb v) (abs_mono_le_one X hXb α v) (abs_nonneg _) hC0
    _ = C := by ring

section CrossWeight

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Reflection positivity with a cross weight that reads both sides.

`O` is a measurable observable of the coordinates in `S`, bounded in absolute value by `C`; `X` is a
matrix-valued function of the same coordinates whose real coordinates are measurable and bounded in
absolute value by one. The integrand is `O (U|S) * O ((twist θ σ U)|S)` times

    exp (β · Re tr ( X(U|S) · X((twist θ σ U)|S)ᴴ ))

which is a function of both sides at once. The conclusion is that its integral against `cvol ι μ` is
nonnegative.

`C` is bound before the integral and is a hypothesis, not a construction: it is what makes the
dominating series summable. `S` and `T` must be disjoint and `θ` must carry `S` into `T`, as in
`twisted_pairing_eq_sq`. The matrix size `N` of `X` is independent of everything else in the
statement. `NegControl.su3_kernel_nonneg_iff` shows `0 ≤ β` cannot be dropped.

DERIVED: the `1` bounds a real coordinate of `X`, which is what a unitary entry satisfies. The three
`0`s are sign conditions — on the bound `C`, on the coupling `β`, and on the integral in the
conclusion. -/
theorem crossweight_pairing_nonneg
    (S T : Finset ι) (hST : Disjoint S T) (θ : Equiv.Perm ι) (σ : ι → Ω → Ω)
    (hσ : ∀ i, MeasurePreserving (σ i) μ μ) (hθST : ∀ i ∈ S, θ i ∈ T)
    {N : ℕ} (X : (S → Ω) → Matrix (Fin N) (Fin N) ℂ)
    (hXm : ∀ p : Coord N, Measurable (fun v => coord p (X v)))
    (hXb : ∀ (p : Coord N) (v : S → Ω), |coord p (X v)| ≤ 1)
    (O : (S → Ω) → ℝ) (hOm : Measurable O) (C : ℝ) (hC0 : 0 ≤ C) (hCb : ∀ v, |O v| ≤ C)
    (β : ℝ) (hβ : 0 ≤ β) :
    0 ≤ ∫ U, O (fun i : S => U (i : ι)) * O (fun i : S => twist θ σ U (i : ι))
        * Real.exp (β * hsRe (X (fun i : S => U (i : ι)))
            (X (fun i : S => twist θ σ U (i : ι)))) ∂(cvol ι μ) := by
  classical
  -- the two restriction maps, and measurability of anything read through them
  have hvm : Measurable (fun U : ι → Ω => (fun i : S => U (i : ι))) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (i : ι))
  have hwm : Measurable (fun U : ι → Ω => (fun i : S => twist θ σ U (i : ι))) :=
    measurable_pi_lambda _
      (fun i => (hσ (i : ι)).measurable.comp (measurable_pi_apply (θ (i : ι))))
  have hαm : ∀ {k : ℕ} (α : Fin k → Coord N), Measurable (halfFun O X α) :=
    fun α => measurable_halfFun hOm hXm α
  have hαb : ∀ {k : ℕ} (α : Fin k → Coord N) (v : S → Ω), |halfFun O X α v| ≤ C :=
    fun α v => abs_halfFun_le hC0 hCb hXb α v
  -- the order-k term, as a function on configurations
  set Fk : ℕ → (ι → Ω) → ℝ := fun k U => wilsonCoef β k *
    ∑ α : Fin k → Coord N,
      halfFun O X α (fun i : S => U (i : ι))
        * halfFun O X α (fun i : S => twist θ σ U (i : ι)) with hFk
  have hFkm : ∀ k, Measurable (Fk k) := by
    intro k
    rw [hFk]
    refine Measurable.const_mul ?_ _
    exact Finset.measurable_sum _ (fun α _ => ((hαm α).comp hvm).mul ((hαm α).comp hwm))
  -- each order integrates to a nonnegative number: a nonnegative coefficient times squares
  have hint : ∀ {k : ℕ} (α : Fin k → Coord N), Integrable
      (fun U : ι → Ω => halfFun O X α (fun i : S => U (i : ι))
        * halfFun O X α (fun i : S => twist θ σ U (i : ι))) (cvol ι μ) := by
    intro k α
    refine integrable_of_bounded (cvol ι μ) (((hαm α).comp hvm).mul ((hαm α).comp hwm))
      (C := C * C) (fun U => ?_)
    rw [abs_mul]
    exact mul_le_mul (hαb α _) (hαb α _) (abs_nonneg _) hC0
  have hFknn : ∀ k, 0 ≤ ∫ U, Fk k U ∂(cvol ι μ) := by
    intro k
    have hsplit : (∫ U, Fk k U ∂(cvol ι μ))
        = wilsonCoef β k * ∑ α : Fin k → Coord N,
            ∫ U, halfFun O X α (fun i : S => U (i : ι))
              * halfFun O X α (fun i : S => twist θ σ U (i : ι)) ∂(cvol ι μ) := by
      rw [hFk]
      rw [integral_const_mul, integral_finset_sum _ (fun α _ => hint α)]
    rw [hsplit]
    refine mul_nonneg (wilsonCoef_nonneg hβ k) (Finset.sum_nonneg (fun α _ => ?_))
    rw [twisted_pairing_eq_sq μ S T hST θ σ hσ hθST (halfFun O X α) (hαm α)]
    exact sq_nonneg _
  -- the pointwise expansion of the integrand
  have hlim : ∀ U : ι → Ω, HasSum (fun k => Fk k U)
      (O (fun i : S => U (i : ι)) * O (fun i : S => twist θ σ U (i : ι))
        * Real.exp (β * hsRe (X (fun i : S => U (i : ι)))
            (X (fun i : S => twist θ σ U (i : ι))))) := by
    intro U
    have hbase := (hasSum_wilsonWeight_paired (N := N) β
      (X (fun i : S => U (i : ι))) (X (fun i : S => twist θ σ U (i : ι)))).mul_left
      (O (fun i : S => U (i : ι)) * O (fun i : S => twist θ σ U (i : ι)))
    have heq : (fun k : ℕ => (O (fun i : S => U (i : ι))
          * O (fun i : S => twist θ σ U (i : ι))) *
        (wilsonCoef β k * ∑ α : Fin k → Coord N,
          mono α (X (fun i : S => U (i : ι)))
            * mono α (X (fun i : S => twist θ σ U (i : ι)))))
        = fun k : ℕ => Fk k U := by
      funext k
      rw [hFk]
      simp only [halfFun]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun α _ => by ring)
    rw [heq] at hbase
    exact hbase
  -- dominated convergence, with a bound that does not depend on the configuration
  have hD0 : (0 : ℝ) ≤ (Fintype.card (Coord N) : ℝ) := Nat.cast_nonneg _
  have hcard : ∀ k : ℕ,
      (Finset.univ : Finset (Fin k → Coord N)).card = (Fintype.card (Coord N)) ^ k := by
    intro k
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  have hbd : ∀ (k : ℕ) (U : ι → Ω),
      ‖Fk k U‖ ≤ C * C * (((Fintype.card (Coord N) : ℝ) * β) ^ k / (Nat.factorial k : ℝ)) := by
    intro k U
    rw [Real.norm_eq_abs, hFk]
    simp only
    rw [abs_mul, abs_of_nonneg (wilsonCoef_nonneg hβ k)]
    have hs : |∑ α : Fin k → Coord N,
        halfFun O X α (fun i : S => U (i : ι))
          * halfFun O X α (fun i : S => twist θ σ U (i : ι))|
        ≤ ((Fintype.card (Coord N) : ℝ) ^ k) * (C * C) := by
      calc |∑ α : Fin k → Coord N,
            halfFun O X α (fun i : S => U (i : ι))
              * halfFun O X α (fun i : S => twist θ σ U (i : ι))|
          ≤ ∑ α : Fin k → Coord N,
              |halfFun O X α (fun i : S => U (i : ι))
                * halfFun O X α (fun i : S => twist θ σ U (i : ι))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _α : Fin k → Coord N, C * C := by
            refine Finset.sum_le_sum (fun α _ => ?_)
            rw [abs_mul]
            exact mul_le_mul (hαb α _) (hαb α _) (abs_nonneg _) hC0
        _ = ((Fintype.card (Coord N) : ℝ) ^ k) * (C * C) := by
            rw [Finset.sum_const, nsmul_eq_mul, hcard k]
            push_cast
            ring
    calc wilsonCoef β k * |∑ α : Fin k → Coord N,
          halfFun O X α (fun i : S => U (i : ι))
            * halfFun O X α (fun i : S => twist θ σ U (i : ι))|
        ≤ wilsonCoef β k * (((Fintype.card (Coord N) : ℝ) ^ k) * (C * C)) :=
          mul_le_mul_of_nonneg_left hs (wilsonCoef_nonneg hβ k)
      _ = C * C * (((Fintype.card (Coord N) : ℝ) * β) ^ k / (Nat.factorial k : ℝ)) := by
          rw [wilsonCoef, mul_pow]
          have hfac : (0 : ℝ) < (Nat.factorial k : ℝ) := by
            exact_mod_cast Nat.factorial_pos k
          field_simp
  have hsummable : Summable
      (fun k : ℕ => C * C * (((Fintype.card (Coord N) : ℝ) * β) ^ k / (Nat.factorial k : ℝ))) :=
    (Real.summable_pow_div_factorial ((Fintype.card (Coord N) : ℝ) * β)).mul_left (C * C)
  have hdct := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := cvol ι μ) (F := Fk)
    (fun k (_ : ι → Ω) =>
      C * C * (((Fintype.card (Coord N) : ℝ) * β) ^ k / (Nat.factorial k : ℝ)))
    (fun k => (hFkm k).aestronglyMeasurable)
    (fun k => Filter.Eventually.of_forall (fun U => hbd k U))
    (Filter.Eventually.of_forall (fun _ => hsummable))
    (integrable_const _)
    (Filter.Eventually.of_forall hlim)
  rw [← hdct.tsum_eq]
  exact tsum_nonneg hFknn

end CrossWeight

/-! ## On the Wilson lattice, and the connector to `PlaqReflPositive` -/

section Wilson

variable {N d n : ℕ}

/-- `crossweight_pairing_nonneg` on the Wilson lattice, with `Reflect.reflConf` as the reflection.

`reflConf` is the twist `ActionSplit.twist (reflLinkPerm τ cst) (axisDagger τ)`
(`ActionSplit.reflConf_eq_twist`), and `ActionSplit.axisDagger_measurePreserving` gives each
component map the measure preservation the twisted lemmas want, so `crossweight_pairing_nonneg`
applies directly at `ι = Link d n` and `μ = probHaar (SUN.SU N)`.

`S` and `T` are supplied by the caller. That they are disjoint and that `reflLink τ cst` carries `S`
into `T` are hypotheses, not consequences: nothing in the statement ties `S` to a side of the
reflection plane. The matrix size `Nc` of `X` is a separate parameter from the gauge group's `N`; the
statement relates them only through the coordinate bound.

DERIVED: the `1` bounds a real coordinate of `X`. The three `0`s are sign conditions — on the bound
`C`, on the coupling `β`, and on the integral in the conclusion. -/
theorem wilson_crossweight_pairing_nonneg [NeZero n] (τ : Fin d) (cst : Fin n)
    (S T : Finset (Link d n)) (hST : Disjoint S T)
    (hSmap : ∀ l ∈ S, reflLink τ cst l ∈ T)
    {Nc : ℕ} (X : (S → MassGap.SUN.SU N) → Matrix (Fin Nc) (Fin Nc) ℂ)
    (hXm : ∀ p : Coord Nc, Measurable (fun v => coord p (X v)))
    (hXb : ∀ (p : Coord Nc) (v : S → MassGap.SUN.SU N), |coord p (X v)| ≤ 1)
    (O : (S → MassGap.SUN.SU N) → ℝ) (hOm : Measurable O) (C : ℝ) (hC0 : 0 ≤ C)
    (hCb : ∀ v, |O v| ≤ C) (β : ℝ) (hβ : 0 ≤ β) :
    0 ≤ ∫ U, O (fun l : S => U (l : Link d n))
        * O (fun l : S => reflConf τ cst U (l : Link d n))
        * Real.exp (β * hsRe (X (fun l : S => U (l : Link d n)))
            (X (fun l : S => reflConf τ cst U (l : Link d n))))
        ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N))) :=
  crossweight_pairing_nonneg (probHaar (MassGap.SUN.SU N)) S T hST
    (reflLinkPerm τ cst) (axisDagger (N := N) τ)
    (fun l => axisDagger_measurePreserving τ l)
    (fun l hl => hSmap l hl) X hXm hXb O hOm C hC0 hCb β hβ

/-- At even extent and odd lag, a plaquette in a `(τ, ν)` plane has two distinct axis links in its
boundary word, both fixed by `reflLink τ c`.

The site comes from `exists_fixed_site` applied to `even_sub_one_of_odd`, which consumes `Even n`,
`2 ≤ n` and `¬ Even c.val`. The conclusion names the links `(τ, x)` and `(τ, shift ν x)` and gives
five facts about them: they are distinct, each lies in `(bd ((τ, ν), x)).map Prod.fst`, and
`reflLink τ c` fixes each. `hν : ν ≠ τ` is what makes the plane nondegenerate; the site is
constructed as `Function.update (fun _ => 0) τ y`, so only the axis coordinate is moved.

A word of the form `G · F · G'⁻¹ · (ΘF)⁻¹` with `G ≠ G'` is not `X · (ΘX)ᴴ` for any `X`, so
`crossweight_pairing_nonneg` does not apply to a weight built from such a word.

DERIVED: `2` is the hypothesis `2 ≤ n` on the extent — a step in a transverse direction has to move
the site, which it does not at extent one. It is the only numeral in the statement; the `0` in the
constructed site appears in the proof term, where it is the site coordinate in every non-axis
direction. -/
theorem odd_lag_straddling_plaq_two_fixed_axis_links [NeZero n] (hn : Even n) (h2 : 2 ≤ n)
    {τ ν : Fin d} (hν : ν ≠ τ) {c : Fin n} (hc : ¬ Even c.val) :
    ∃ x : Site d n, ((τ, x) : Link d n) ≠ (τ, WilsonHypercubic.shift ν x)
      ∧ ((τ, x) : Link d n) ∈ (bd (((τ, ν), x) : Plaq d n)).map Prod.fst
      ∧ ((τ, WilsonHypercubic.shift ν x) : Link d n)
          ∈ (bd (((τ, ν), x) : Plaq d n)).map Prod.fst
      ∧ reflLink τ c ((τ, x) : Link d n) = (τ, x)
      ∧ reflLink τ c ((τ, WilsonHypercubic.shift ν x) : Link d n)
          = (τ, WilsonHypercubic.shift ν x) := by
  obtain ⟨y, hy⟩ := exists_fixed_site (even_sub_one_of_odd hn h2 hc)
  refine ⟨Function.update (fun _ => 0) τ y, ?_, ?_, ?_, ?_, ?_⟩
  · intro hcon
    have h1 : Function.update (fun _ => (0 : Fin n)) τ y
        = WilsonHypercubic.shift ν (Function.update (fun _ => 0) τ y) :=
      congrArg Prod.snd hcon
    have h2' : (Function.update (fun _ => (0 : Fin n)) τ y) ν
        = (Function.update (fun _ => (0 : Fin n)) τ y) ν + 1 := by
      have h3 := congrFun h1 ν
      rwa [WilsonHypercubic.shift, Function.update_self] at h3
    have h4 : (0 : Fin n) = 1 := by
      have h5 : (Function.update (fun _ => (0 : Fin n)) τ y) ν + 0
          = (Function.update (fun _ => (0 : Fin n)) τ y) ν + 1 := by simpa using h2'
      exact add_left_cancel h5
    have hv : ((1 : Fin n) : ℕ) = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt h2
    have h6 : ((0 : Fin n) : ℕ) = ((1 : Fin n) : ℕ) := congrArg Fin.val h4
    rw [Fin.val_zero, hv] at h6
    exact absurd h6 (by norm_num)
  · simp [bd]
  · simp [bd]
  · refine (reflLink_fixed_iff_axis c _ rfl).mpr ?_
    simpa using hy.symm
  · refine (reflLink_fixed_iff_axis c _ rfl).mpr ?_
    have hsτ : (WilsonHypercubic.shift ν (Function.update (fun _ => (0 : Fin n)) τ y)) τ
        = (Function.update (fun _ => (0 : Fin n)) τ y) τ := by
      simp [WilsonHypercubic.shift, Function.update_of_ne (Ne.symm hν)]
    show c - 1 = (WilsonHypercubic.shift ν (Function.update (fun _ => (0 : Fin n)) τ y)) τ
      + (WilsonHypercubic.shift ν (Function.update (fun _ => (0 : Fin n)) τ y)) τ
    rw [hsτ]
    simpa using hy.symm

/-- `ReflectPositive.PlaqReflPositive N τ cst β q₀` follows from nonnegativity of the un-normalised
pairing integral at every subtraction constant `aC`.

`PlaqReflPositive` is the pairing inequality for the Gibbs expectation; between it and the integral
in `hpair` stands only the partition function, which `WilsonReal.wilsonSystem_partition_pos` shows is
positive when `N ≠ 0`. `div_nonneg` then gives the conclusion. The hypothesis quantifies over `aC`
because the conclusion does, and it is stated at one plaquette `q₀` and one lag `cst`, not over all
of them.

DERIVED: the `0` in `N ≠ 0` excludes the empty matrix size, which is what the partition-function
positivity lemma requires; the `0` in `0 ≤ ∫ …` is the sign condition the hypothesis asserts. -/
theorem plaqReflPositive_of_pairing_nonneg [NeZero n] (hN : N ≠ 0)
    (τ : Fin d) (cst : Fin n) (β : ℝ) (q₀ : Plaq d n)
    (hpair : ∀ aC : ℝ, 0 ≤ ∫ U,
      (wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ U) - aC)
        * (wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ (reflConf τ cst U)) - aC)
        * (sysWilson N d n).boltz β U ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N)))) :
    MassGap.ReflectPositive.PlaqReflPositive N τ cst β q₀ := by
  intro aC
  have hZ : 0 < (sysWilson N d n).partition (probHaar (MassGap.SUN.SU N)) β :=
    MassGap.WilsonReal.wilsonSystem_partition_pos hN (bd (d := d) (n := n)) β
  exact div_nonneg (hpair aC) (le_of_lt hZ)

end Wilson

section Audit
#print axioms twisted_pairing_eq_sq
#print axioms twisted_reflection_positive_of_expansion
#print axioms measurable_mono
#print axioms abs_mono_le_one
#print axioms crossweight_pairing_nonneg
#print axioms wilson_crossweight_pairing_nonneg
#print axioms odd_lag_straddling_plaq_two_fixed_axis_links
#print axioms plaqReflPositive_of_pairing_nonneg
end Audit

end MassGap.CharacterExpansion
