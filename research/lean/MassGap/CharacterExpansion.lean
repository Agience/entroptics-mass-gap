import Mathlib
import MassGap.ActionSplit

/-!
# MassGap.CharacterExpansion — the Wilson weight's expansion coefficients are NONNEGATIVE

`ReflectionPositivity.reflection_positive_of_expansion` proves that a finite expansion into paired
products with nonnegative coefficients integrates to something nonnegative, and `ActionSplit` proves
the conditional weld that discharges the pairing inequality at even extent and even lag. What neither
supplies is the expansion itself: a way to handle a term that COUPLES the two halves of the
reflection, which is what the plaquettes straddling a link-reflection plane produce.

That coupling is the Osterwalder-Seiler character expansion, and the content of it is a sign. This
file proves the sign.

## What is proved

**The expansion, exactly, at every order.** Write `hsRe A B = Re tr (A Bᴴ)` — the `Re tr` of a word
with `A` on one side of the plane and `B` on the other, which is the Wilson plaquette energy's own
functional form. `hsRe` is a real inner product in the `2N²` real coordinates of a complex `N × N`
matrix (`hsRe_eq_sum`), so its `k`-th power expands with NO cross terms between the two arguments:

    hsRe A B ^ k = ∑ over degree-k monomials α of  mono α A * mono α B      (`hsRe_pow`)

— a FINITE sum of PAIRED products, one factor reading `A` and one reading `B`, with coefficient `1`.
The Wilson weight `exp (β * hsRe A B)` is then the sum over `k` of these with coefficient `β^k / k!`,
which is nonnegative exactly when `β` is (`hasSum_wilsonWeight_paired`).

That is the CONTENT of "the character expansion has nonnegative coefficients", and it needs no
representation theory: the coefficients are nonnegative because they are multiplicities in a tensor
power, and the tensor power is written out here as the monomial index `α`. What is NOT formalised is
the DICTIONARY — that a class function on a compact group is positive-definite exactly when its
coefficients against the irreducible characters are nonnegative. That dictionary is Peter-Weyl, it is
not in this development, and nothing below uses it: the paired expansion is produced directly, in the
form the pairing mechanism consumes, so the irreducible characters never have to be named.

**Positive definiteness**, the operational form of the same statement: the Wilson weight is a
positive-semidefinite kernel on matrices (`wilson_kernel_nonneg`). Its proof is the identity
`quadform_pow_eq_sum_sq`, which turns the order-`k` quadratic form into an explicit SUM OF SQUARES.

**The mechanism, for a reflection that DAGGERS.** `ReflectionPositivity.reflection_positive_of_expansion`
is stated for a bare relabelling `U ∘ θ`, and the Osterwalder-Seiler time reflection is not one: it
inverts the gauge variable on every link running along the reflection axis. `twisted_pairing_eq_sq`
and `twisted_reflection_positive_of_expansion` are the same statements for
`ActionSplit.twist θ σ`, which `Reflect.reflConf` IS (`ActionSplit.reflConf_eq_twist`). Without them
the expansion mechanism cannot be pointed at the actual Wilson reflection at all.

**The two put together.** `crossweight_pairing_nonneg` is reflection positivity for an observable
paired against a cross weight `exp (β * hsRe (X (U|₊)) (X ((ΘU)|₊)))` that genuinely COUPLES the two
halves — the first statement in this development that allows any coupling across the plane.
`ActionSplit`'s weld cannot: it requires every plaquette to read one side or the plane alone.

## The negative control

`NegControl.su3_kernel_nonneg_iff` computes the quadratic form on two honest `SU(3)` elements — the
identity and `diag(1, −1, −1)`, both shown to lie in `specialUnitaryGroup` — and finds it equal to
`2 (e^{3β} − e^{−β})`, which is nonnegative IF AND ONLY IF `β ≥ 0`. So the nonnegativity is a
property of the sign of the Wilson coupling and not of the machinery: at negative coupling the same
weight, on the same group, with the same observable, has a negative expansion coefficient
(`wilsonCoef_neg_of_neg`) and fails positive definiteness outright.

## What this does NOT discharge, and why

`ReflectPositive.corrClay_rp_of` needs `PlaqReflPositive` at EVERY lag. `ActionSplit` covers the even
lags. An ODD lag at even extent is a LINK reflection, and two things go wrong there, only one of
which this file fixes:

* the reflection inverts a SHARED axis link (`ActionSplit.reflConf_inverts_fixed_axis_link`) — the
  twist, which `twisted_pairing_eq_sq` handles for links the reflection MOVES, but not for a link it
  FIXES and inverts; and
* a plaquette straddling a link-reflection plane reads TWO DISTINCT fixed axis links, so its word is
  `G · F · G'⁻¹ · (ΘF)⁻¹` with `G ≠ G'` both inverted by `Θ`. That is not `X · (ΘX)ᴴ` for any `X`,
  so `crossweight_pairing_nonneg` does not apply to it and neither does any paired-word hypothesis.
  Osterwalder-Seiler close that case by expanding the straddling weight into matrix elements and
  integrating the crossing links against them, where Schur orthogonality supplies a Gram matrix.

`plaqReflPositive_of_pairing_nonneg` is the connector that says exactly which integral inequality is
left: nonnegativity of the un-normalised pairing integral at that lag. Everything between it and the
character coefficients is here; the crossing-link integration is not.

Foundational footprint only (`#print axioms` at the end).
Build: `python code/lean_build.py build MassGap.CharacterExpansion`.
-/

namespace MassGap.CharacterExpansion

open MeasureTheory
open MassGap MassGap.ActionSplit MassGap.WilsonAction MassGap.WilsonLattice
open MassGap.WilsonHypercubic MassGap.CompactGauge MassGap.Reflect

/-! ## `Re tr (A Bᴴ)` is a real inner product

The Wilson plaquette energy is `1 − (1/N) Re tr g`, and a plaquette straddling a reflection plane has
`g` a word containing one link on each side. `hsRe` is the bilinear shell of that: `Re tr (A Bᴴ)`,
which for unitary `B` is `Re tr (A B⁻¹)`. The point of this section is that it is the STANDARD REAL
INNER PRODUCT on the `2N²` real coordinates of a complex matrix, so every power of it splits into
paired monomials with no cross terms. -/

/-- A real coordinate of a complex `N × N` matrix: an entry `(i, j)` and a choice of real or
imaginary part. There are `2N²` of them.

DERIVED: nothing numeric. The `Bool` is the two parts of a complex number, not a chosen cut. -/
abbrev Coord (N : ℕ) : Type := Fin N × Fin N × Bool

/-- The value of that coordinate. -/
noncomputable def coord {N : ℕ} (p : Coord N) (A : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  if p.2.2 then (A p.1 p.2.1).re else (A p.1 p.2.1).im

/-- **The Wilson cross form** `Re tr (A Bᴴ)`. For `A` and `B` in `SU(N)`, `Bᴴ = B⁻¹`, so this is the
`Re tr` of the word the straddling plaquette contributes, with `A` read on one side of the reflection
plane and `B` on the other. -/
noncomputable def hsRe {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (Matrix.trace (A * Matrix.conjTranspose B)).re

/-- **`Re tr (A Bᴴ)` is the real inner product of the coordinate vectors.**

`tr (A Bᴴ) = ∑ᵢⱼ Aᵢⱼ · conj Bᵢⱼ`, whose real part is `∑ᵢⱼ (Re Aᵢⱼ Re Bᵢⱼ + Im Aᵢⱼ Im Bᵢⱼ)`. That is
the Euclidean inner product on `ℝ^{2N²}` — the one fact this whole file runs on, because it is what
makes every power of `hsRe` split into products of a function of `A` with the SAME function of `B`.

DERIVED: no numeral. `2N²` is the count of real coordinates of a complex `N × N` matrix. -/
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

/-- A degree-`k` monomial in the real coordinates of a matrix, indexed by the `k` coordinates it
multiplies. These are the `g_k` of the expansion. -/
noncomputable def mono {N k : ℕ} (α : Fin k → Coord N) (A : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ∏ t, coord (α t) A

/-- **THE EXPANSION, EXACTLY, AT EVERY ORDER.**

    (Re tr (A Bᴴ))^k  =  ∑ over degree-k monomials α of  mono α A * mono α B

A FINITE sum of PAIRED products — each term a function of `A` times the SAME function of `B` — with
every coefficient equal to `1`. This is the whole reason the character expansion of the Wilson weight
has nonnegative coefficients: the coefficients are the multiplicities with which an irreducible
occurs in a tensor power, and the tensor power is written out here as the index `α`. No
representation theory is used or needed.

DERIVED: the `1` coefficients are not chosen; they are what multiplying out a power of a sum gives. -/
theorem hsRe_pow {N : ℕ} (k : ℕ) (A B : Matrix (Fin N) (Fin N) ℂ) :
    hsRe A B ^ k = ∑ α : Fin k → Coord N, mono α A * mono α B := by
  rw [hsRe_eq_sum, Fintype.sum_pow]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  unfold mono
  rw [← Finset.prod_mul_distrib]

/-! ## The Wilson weight, and its coefficients -/

/-- The exponential series, as a `HasSum`. -/
theorem hasSum_exp_div (x : ℝ) :
    HasSum (fun k : ℕ => x ^ k / (Nat.factorial k : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

/-- The coefficient the Wilson weight carries at order `k`. -/
noncomputable def wilsonCoef (β : ℝ) (k : ℕ) : ℝ := β ^ k / (Nat.factorial k : ℝ)

/-- **THE COEFFICIENTS ARE NONNEGATIVE — for `β ≥ 0`.** -/
theorem wilsonCoef_nonneg {β : ℝ} (hβ : 0 ≤ β) (k : ℕ) : 0 ≤ wilsonCoef β k :=
  div_nonneg (pow_nonneg hβ k) (Nat.cast_nonneg _)

/-- **NEGATIVE CONTROL, at the coefficient.** At negative coupling the order-one coefficient is
negative, so `wilsonCoef_nonneg`'s hypothesis is doing work rather than decorating. -/
theorem wilsonCoef_neg_of_neg {β : ℝ} (hβ : β < 0) : wilsonCoef β 1 < 0 := by
  unfold wilsonCoef
  simpa using hβ

/-- **THE WILSON WEIGHT IS ITS OWN PAIRED EXPANSION**, with the coefficients above:

    exp (β · Re tr (A Bᴴ))  =  ∑ₖ  (β^k / k!) · ∑_α  mono α A · mono α B.

Each order is a finite sum of paired products (`hsRe_pow`); the coefficient of order `k` is
`β^k / k!`, nonnegative for `β ≥ 0` (`wilsonCoef_nonneg`). That is the statement
`ReflectionPositivity.reflection_positive_of_expansion` was written to consume, for the `SU(N)`
Wilson plaquette weight and hence for `SU(3)`. -/
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

/-! ## Positive definiteness: the same statement, in the form a referee checks

A class function on a compact group has nonnegative character coefficients exactly when it is a
positive-definite function. `quadform_pow_eq_sum_sq` is that equivalence made explicit at each order
— the order-`k` quadratic form IS a sum of squares — and `wilson_kernel_nonneg` sums it. -/

/-- **THE ORDER-`k` QUADRATIC FORM IS A SUM OF SQUARES.**

    ∑ᵢⱼ zᵢ zⱼ (Re tr (Aᵢ Aⱼᴴ))^k  =  ∑_α ( ∑ᵢ zᵢ · mono α Aᵢ )²

Immediate from `hsRe_pow` once the sums are exchanged: the monomial index `α` is common to both
factors, so the double sum over `(i, j)` collapses into a square for each `α`. -/
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

/-- **THE `SU(N)` WILSON PLAQUETTE WEIGHT IS A POSITIVE-SEMIDEFINITE KERNEL**, for `β ≥ 0`.

    0 ≤ ∑ᵢⱼ zᵢ zⱼ exp (β · Re tr (Aᵢ Aⱼᴴ))   for any finite family of matrices and any real weights.

This is exactly "the character expansion of the Wilson weight has nonnegative coefficients", stated
without the words: the order-`k` contribution is `β^k/k!` times a sum of squares
(`quadform_pow_eq_sum_sq`), and the series converges to the weight (`hasSum_exp_div`).

Stated for arbitrary matrices, so it holds in particular for `SU(3)` elements and for the specific
words a straddling plaquette builds out of them. The only hypothesis is `0 ≤ β`, and
`NegControl.su3_kernel_nonneg_iff` shows it cannot be dropped.

DERIVED: the only numeral is the `0` of `0 ≤ …`, which IS positive semidefiniteness. -/
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

/-! ## MANDATORY NEGATIVE CONTROL: the sign of the coupling is what carries it

The machinery above would produce the same shape for any weight of the form `exp (β · ⟨A, B⟩)`. What
makes the conclusion a property of the `SU(3)` WILSON weight rather than of the machinery is the sign
of `β`. Computed on two honest `SU(3)` elements, the quadratic form is nonnegative IF AND ONLY IF
`β ≥ 0`: at negative coupling the same weight, the same group and the same observable give a strictly
negative value. -/

namespace NegControl

/-- A diagonal matrix whose entries have modulus one and product one lies in `SU(N)`. -/
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

/-- `Re tr` of a product of diagonals, entrywise. -/
theorem hsRe_diagonal {N : ℕ} (d e : Fin N → ℂ) :
    hsRe (Matrix.diagonal d) (Matrix.diagonal e) = ∑ i, (d i * (starRingEnd ℂ) (e i)).re := by
  unfold hsRe
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,
    Complex.re_sum]
  rfl

/-- The two diagonal vectors: the identity, and the centre-like element `diag(1, −1, −1)`. Both have
determinant one and unit-modulus entries, so both are genuine `SU(3)` elements.

DERIVED: the entries of two explicit SU(3) elements. `1` is the identity's diagonal and `-1` the sign that makes the second a non-identity involution; `3` is the rank and `2` the number of elements the control needs. Determinant 1 forces the pattern, so nothing here is chosen. -/
noncomputable def dvec : Fin 2 → (Fin 3 → ℂ) := ![![1, 1, 1], ![1, -1, -1]]

/-- The two `SU(3)` matrices.

DERIVED: `3` is SU(3)'s rank and `2` indexes the two control elements. Both are the ambient type's. -/
noncomputable def cA (i : Fin 2) : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (dvec i)

/-- **Both control matrices really are in `SU(3)`.** -/
theorem cA_mem_SU (i : Fin 2) : cA i ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  refine diagonal_mem_SU (dvec i) ?_ ?_
  · intro j
    fin_cases i <;> fin_cases j <;> norm_num [dvec]
  · fin_cases i <;> norm_num [dvec, Fin.prod_univ_succ]

/-- The weights of the control vector: `+1` on the identity, `−1` on the other element.

DERIVED: the weights `(1, -1)` of the negative control. Any pair with opposite signs exhibits the indefiniteness; these are the smallest, and `2` is the number of elements being paired. -/
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

/-- The quadratic form on the two control elements, evaluated. -/
theorem su3_quadform (β : ℝ) :
    (∑ i, ∑ j, zc i * zc j * Real.exp (β * hsRe (cA i) (cA j)))
      = 2 * (Real.exp (3 * β) - Real.exp (-β)) := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  rw [hsRe_cA_zero_zero, hsRe_cA_zero_one, hsRe_cA_one_zero, hsRe_cA_one_one]
  simp only [zc, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show β * (3 : ℝ) = 3 * β by ring, show β * (-1 : ℝ) = -β by ring]
  ring

/-- **THE NEGATIVE CONTROL.** On two genuine `SU(3)` elements the Wilson quadratic form is
nonnegative IF AND ONLY IF the coupling is nonnegative.

So `wilson_kernel_nonneg`'s hypothesis `0 ≤ β` is load-bearing and the positivity is a property of
the `SU(3)` Wilson weight at physical coupling, not an artifact of the expansion machinery: run the
same expansion at `β < 0` and the coefficients alternate (`wilsonCoef_neg_of_neg`) and the kernel is
indefinite. -/
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

/-- The same, as a strict failure: at negative coupling the form is strictly negative. -/
theorem su3_kernel_neg_of_neg {β : ℝ} (hβ : β < 0) :
    (∑ i, ∑ j, zc i * zc j * Real.exp (β * hsRe (cA i) (cA j))) < 0 := by
  by_contra h
  exact absurd ((su3_kernel_nonneg_iff β).mp (not_lt.mp h)) (not_le.mpr hβ)

#print axioms cA_mem_SU
#print axioms su3_quadform
#print axioms su3_kernel_nonneg_iff
#print axioms su3_kernel_neg_of_neg

end NegControl

/-! ## The mechanism, for a reflection that DAGGERS

`ReflectionPositivity.pairing_with_reflection_nonneg` and
`ReflectionPositivity.reflection_positive_of_expansion` are stated for a bare relabelling `U ∘ θ`.
The Osterwalder-Seiler reflection is not one: `Reflect.reflConf` INVERTS the gauge variable on every
link running along the reflection axis, and is `ActionSplit.twist (reflLinkPerm τ c) (axisDagger τ)`
(`ActionSplit.reflConf_eq_twist`). So neither lemma can be pointed at the actual Wilson reflection.

The two statements below are those lemmas for a twist. Nothing about the argument changes — the twist
preserves the product measure coordinate by coordinate (`ActionSplit.twist_measurePreserving`), which
is all the mirror step ever used — but without them the expansion has no mechanism to feed. -/

section Twisted

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- **A half-supported function paired with its TWISTED reflection integrates to a square.**

The twisted form of `ReflectionPositivity.pairing_with_reflection_nonneg`. `S` and `T` are disjoint
and `θ` carries `S` into `T`, so the two factors read disjoint coordinates and the integral
factorises; the twist is measure-preserving coordinatewise, so the two factors are equal.

DERIVED: no numeric content. -/
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

/-- **A finite expansion into paired products with nonnegative coefficients integrates to something
nonnegative — under a TWISTED reflection.**

`ReflectionPositivity.reflection_positive_of_expansion` for `ActionSplit.twist`. This is the
statement that `hasSum_wilsonWeight_paired` was proved to feed. -/
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

/-! ## The two put together: a cross weight that COUPLES the two halves

`ActionSplit`'s conditional weld needs the Boltzmann weight to split into a function of one side, a
function of the other, and a function of the plane. It cannot touch a term that reads BOTH sides at
once, and that is exactly what a plaquette straddling a reflection plane contributes.

`crossweight_pairing_nonneg` is the first statement here that allows one. The cross weight is
`exp (β · Re tr (X₊ · X₋ᴴ))` with `X₋` the reflection of `X₊` — a genuine coupling — and the
conclusion is still nonnegativity, for every observable of the positive half. The proof is the
character expansion: order by order the coupling separates into paired monomials with nonnegative
coefficients (`hasSum_wilsonWeight_paired`), each order is a square by `twisted_pairing_eq_sq`, and
dominated convergence sums them. -/

/-- A monomial in the coordinates of a matrix-valued function is measurable. -/
theorem measurable_mono {N k : ℕ} {γ : Type} [MeasurableSpace γ]
    (X : γ → Matrix (Fin N) (Fin N) ℂ)
    (hX : ∀ p : Coord N, Measurable (fun v => coord p (X v))) (α : Fin k → Coord N) :
    Measurable (fun v => mono α (X v)) := by
  unfold mono
  exact Finset.measurable_prod _ (fun t _ => hX (α t))

/-- A monomial in coordinates of modulus at most one has modulus at most one. For `SU(N)` every
entry has norm `≤ 1` (`SUN.unitary_entry_norm_le_one`), so this applies to the words the lattice
builds. -/
theorem abs_mono_le_one {N k : ℕ} {γ : Type} (X : γ → Matrix (Fin N) (Fin N) ℂ)
    (hXb : ∀ (p : Coord N) (v : γ), |coord p (X v)| ≤ 1) (α : Fin k → Coord N) (v : γ) :
    |mono α (X v)| ≤ 1 := by
  unfold mono
  rw [Finset.abs_prod]
  calc (∏ t, |coord (α t) (X v)|) ≤ ∏ _t : Fin k, (1 : ℝ) :=
        Finset.prod_le_prod (fun t _ => abs_nonneg _) (fun t _ => hXb (α t) v)
    _ = 1 := by simp

/-- **The half-function of the expansion at monomial `α`**: the observable of the positive half times
that monomial of the half's matrix word. These are the `g_k` that
`twisted_reflection_positive_of_expansion` consumes, and they read the positive half alone. -/
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

/-- **REFLECTION POSITIVITY WITH A CROSS WEIGHT THAT COUPLES THE TWO HALVES.**

`O` is an observable of the positive half `S`; `X` is a matrix-valued word of the positive half —
in the application, the product of link variables a straddling plaquette reads there. The weight

    exp (β · Re tr ( X(U|₊) · X((ΘU)|₊)ᴴ ))

couples the two halves, which is precisely what `ActionSplit`'s weld forbids. The conclusion is
nonnegativity of the pairing anyway, for every `β ≥ 0`.

The hypotheses on `X` are that its coordinates are measurable and bounded by one — both automatic
for a word in `SU(N)` link variables, whose entries have norm at most one.

`NegControl.su3_kernel_nonneg_iff` shows `0 ≤ β` cannot be dropped.

DERIVED: the only numerals are the `0` of `0 ≤ …`, which IS the property, and the `1` bounding a
unitary matrix entry, which is unitarity and not a choice. -/
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

/-! ## Pointed at the actual Wilson reflection, and the connector to `PlaqReflPositive` -/

section Wilson

variable {N d n : ℕ}

/-- **The cross-weight pairing inequality, on the Wilson lattice, for `Reflect.reflConf`.**

`reflConf` IS the twist (`ActionSplit.reflConf_eq_twist`) and the axis dagger preserves Haar
(`ActionSplit.axisDagger_measurePreserving`), so `crossweight_pairing_nonneg` applies to it directly.
`S` is one side of the reflection plane and `T` its mirror; the reflection must carry `S` into `T`
and the two must be disjoint, which is the locality side condition `ReflectPositive.plaq_link_ne_refl`
checks for the observable used in this development. -/
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

/-- **THE OBSTRUCTION AT AN ODD LAG, as a positive statement about the geometry.**

`ActionSplit.odd_lag_has_fixed_axis_link` produces ONE fixed axis link and
`ActionSplit.reflConf_inverts_fixed_axis_link` shows the reflection inverts it. The sharper fact,
and the one that rules out the paired-word route, is that a plaquette spanning the axis and a
transverse direction reads TWO DISTINCT fixed axis links: its boundary word
`U_τ(x) · U_ν(x+τ̂) · U_τ(x+ν̂)⁻¹ · U_ν(x)⁻¹` has `U_τ(x)` and `U_τ(x+ν̂)` at the SAME axis
coordinate, so they are fixed together, and the reflection inverts both.

A word of the form `G · F · G'⁻¹ · (ΘF)⁻¹` with `G ≠ G'` is not `X · (ΘX)ᴴ` for any `X`, so
`crossweight_pairing_nonneg` cannot be pointed at it — not for want of a proof, but because the
paired form is absent. Osterwalder-Seiler close that case by expanding the straddling weight into
matrix elements and integrating the two crossing links against them.

DERIVED: nothing numeric. `2 ≤ n` is what makes a step in a transverse direction move the site. -/
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

/-- **THE CONNECTOR: what is left to prove at a lag.**

`ReflectPositive.PlaqReflPositive` is the Gibbs pairing inequality; the only thing between it and the
un-normalised integral is the partition function, which is positive. So the whole remaining content
at any lag — even or odd — is nonnegativity of the integral below. `ActionSplit` supplies it at even
extent and even lag by conditioning on the plane; this file supplies the character expansion the odd
lags need but not the geometry that would put the odd-lag integrand into the shape above. -/
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
