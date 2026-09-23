import Mathlib

/-!
# MassGap.ColourGeneral — the parity arithmetic behind `SU(N)` analogues of three `SU(3)` elements

`ContactValue` evaluates the zero-coupling contact value on `SU(3)` by invariant projection on
explicit group elements, Mathlib at this pin having neither Peter–Weyl nor Schur orthogonality:
translating by a fixed `h` multiplies the integrand by a fixed scalar `λ`, and `c = λc` with `λ ≠ 1`
forces `c = 0`. Three elements carry that file: the central `ω·1`, the diagonal
`diag(1, ω, ω²)`, and the three-cycle permutation matrix, which lies in `SU(3)` because a
three-cycle is an even permutation.

This module contains five arithmetic facts that bear on whether the analogous elements can be formed
at general `N`. Every statement here is about natural numbers or complex numbers; no matrix, no
determinant, no permutation and no Haar integral occurs in any statement, and no group element is
constructed.

## What the declarations state

Write `ζ` for a primitive `N`-th root of unity, so that
`det diag(1, ζ, …, ζ^{N-1}) = ζ^{0+1+⋯+(N-1)}` and the determinant is `1` exactly when
`N ∣ ∑_{i < N} i`.

* `diag_det_exponent_two` states `(∑ i : Fin N, i) * 2 = N * (N - 1)`, Gauss's sum with the division
  cleared.
* `diag_in_SU_of_odd` states `N ∣ ∑ i : Fin N, i` for odd `N`.
* `diag_not_in_SU_of_even` states the negation for even `N` with `2 ≤ N`. The hypothesis `2 ≤ N` is
  needed: at `N = 0` the sum is `0` and `0 ∣ 0` holds.
* `cycle_even_iff_odd` states `Even (N - 1) ↔ Odd N` for `1 ≤ N`. An `N`-cycle has sign
  `(-1)^{N-1}`, so this is the exponent's parity; the sign itself is not formalised here.
* `unit_scalar_cancels_in_ratio` states that for `c : ℂ` with `c * star c = 1`,
  `(c * z) * star (c * w) = z * star w` in `ℂ`. The invariant projection sees its element only
  through products of the form `g_{ii} * conj(g_{kk})`, so a scalar inserted to fix a determinant
  leaves every such product unchanged, whatever its value.

Two facts about the centre element are described in this comment but are not declared in this file:
that `∫χ = 0` whenever `ζ ≠ 1`, and that `∫χ² = 0` whenever `ζ² ≠ 1`, the latter requiring `N ≥ 3`.
At `N = 2` the centre is `{±1}`, its square is `1`, and the projection argument is vacuous; the
tree's `SU(2)` contact value (`HaarMoments.haar_su2_second_moment`) is obtained by another route.

DERIVED: `2` is the multiplier that clears the division in `N(N-1)/2`, and the lower bound on `N`
that excludes `N = 0` from the even case; `1` is the value `star`-multiplication is pinned to, the
`N - 1` offset in Gauss's sum and in the cycle's sign exponent, and the lower bound on `N` in
`cycle_even_iff_odd`. No numeral in any statement is a magnitude.
-/

namespace MassGap.ColourGeneral

/-! ## 1. The determinant exponent -/

/-- Gauss's sum on `Fin N`, doubled so that no division appears:
`(∑ i : Fin N, (i : ℕ)) * 2 = N * (N - 1)`. Proved by transporting the sum to `Finset.range N` and
applying `Finset.sum_range_id_mul_two`. The subtraction is truncated natural subtraction, so the
statement also holds at `N = 0`.

This sum is the exponent in `det diag(1, ζ, …, ζ^{N-1}) = ζ^{∑ i}`, but no determinant appears in
the statement.

DERIVED: `2` is the doubling that clears the division in `N(N-1)/2`; `1` is the offset in the
largest index, `N - 1`. -/
theorem diag_det_exponent_two (N : ℕ) : (∑ i : Fin N, (i : ℕ)) * 2 = N * (N - 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N]
  exact Finset.sum_range_id_mul_two N

#print axioms diag_det_exponent_two

/-- For odd `N`, `N` divides `∑ i : Fin N, (i : ℕ)`. Writing `N = 2k + 1`, `diag_det_exponent_two`
gives `(∑ i) * 2 = N * 2k`, so `∑ i = N * k`. Since `ζ^{∑ i}` is the determinant of
`diag(1, ζ, …, ζ^{N-1})`, divisibility here is what makes that determinant `1`; the statement
itself is a divisibility fact about naturals and mentions no matrix.

Holds at `N = 1` as well, where the sum is `0`.

DERIVED: no numeral appears in the statement. -/
theorem diag_in_SU_of_odd {N : ℕ} (hodd : Odd N) : N ∣ ∑ i : Fin N, (i : ℕ) := by
  obtain ⟨k, hk⟩ := hodd
  have h2 := diag_det_exponent_two N
  have hN1 : N - 1 = 2 * k := by omega
  refine ⟨k, ?_⟩
  have h3 : (∑ i : Fin N, (i : ℕ)) * 2 = 2 * (N * k) := by
    rw [h2, hN1]; ring
  omega

#print axioms diag_in_SU_of_odd

/-- For even `N` with `2 ≤ N`, `N` does not divide `∑ i : Fin N, (i : ℕ)`. A divisor `m` would give
`m * 2 = N - 1` through `diag_det_exponent_two`, which `omega` refutes because `N - 1` is odd.

The hypothesis `2 ≤ N` is required and not decorative: `Even 0` holds, the sum over `Fin 0` is `0`,
and `0 ∣ 0`. Combined with `diag_in_SU_of_odd`, divisibility of the index sum by `N` is exactly the
odd case among `N ≥ 1`.

DERIVED: `2` is the lower bound on `N` that excludes the degenerate case `N = 0`. -/
theorem diag_not_in_SU_of_even {N : ℕ} (hev : Even N) (hN : 2 ≤ N) :
    ¬ N ∣ ∑ i : Fin N, (i : ℕ) := by
  obtain ⟨k, hk⟩ := hev
  have h2 := diag_det_exponent_two N
  rintro ⟨m, hm⟩
  rw [hm] at h2
  have hNpos : 0 < N := by omega
  have h2' : N * (m * 2) = N * (N - 1) := by rw [← mul_assoc]; exact h2
  have h3 : m * 2 = N - 1 := Nat.eq_of_mul_eq_mul_left hNpos h2'
  omega

#print axioms diag_not_in_SU_of_even

/-- `Even (N - 1) ↔ Odd N` for `1 ≤ N`, by `omega` in both directions on the witness. An `N`-cycle
has sign `(-1)^{N-1}`, so this is the parity of that exponent; neither the permutation nor its sign
occurs in the statement, which is arithmetic on naturals.

The hypothesis `1 ≤ N` is required: at `N = 0`, truncated subtraction makes `N - 1 = 0`, so the left
side holds while `Odd 0` does not.

DERIVED: `1` is the offset in the sign exponent `N - 1`, and the lower bound on `N` that excludes
`N = 0`. -/
theorem cycle_even_iff_odd (N : ℕ) (hN : 1 ≤ N) : Even (N - 1) ↔ Odd N := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩

#print axioms cycle_even_iff_odd

/-! ## 2. Why the repair at even `N` is free -/

/-- A unit-modulus scalar cancels out of a product of the form `z · conj w`. For `c : ℂ` with
`c * star c = 1` and any `z w : ℂ`, `(c * z) * star (c * w) = z * star w`. Proved by regrouping with
`star_mul` and `ring`, then rewriting by the hypothesis.

The invariant projection sees its translating element only through products `g_{ii} * conj(g_{kk})`,
so this says a scalar inserted to fix a determinant leaves every such product, and hence the phases
`ζ^{i-k}` the argument runs on, unchanged. The statement quantifies over all `z` and `w` in `ℂ` and
involves no matrix or group.

DERIVED: `1` is the value `c * star c` is pinned to — the unit-modulus condition, not a
magnitude. -/
theorem unit_scalar_cancels_in_ratio {c : ℂ} (hc : c * star c = 1) (z w : ℂ) :
    (c * z) * star (c * w) = z * star w := by
  have h : (c * z) * star (c * w) = (c * star c) * (z * star w) := by
    rw [star_mul]
    ring
  rw [h, hc, one_mul]

#print axioms unit_scalar_cancels_in_ratio

/-! ### Scope of the scalar lemma

`unit_scalar_cancels_in_ratio` is stated for an arbitrary `c : ℂ` satisfying `c * star c = 1`. No
such `c` is constructed anywhere in this module, and in particular the existence of `N`-th roots of
a unit-modulus complex number is not formalised here. Nothing above depends on it, since the lemma
is universally quantified over `c`.
-/

end MassGap.ColourGeneral
