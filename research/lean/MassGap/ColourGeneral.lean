import Mathlib

/-!
# MassGap.ColourGeneral — whether `ContactValue`'s method reaches `SU(N)`

`ContactValue` evaluates the zero-coupling contact value on `SU(3)` by **invariant projection on
explicit group elements**, because Mathlib at this pin has no Peter–Weyl and no Schur orthogonality:
translating by a fixed `h` multiplies the integrand by a fixed scalar `λ`, and `c = λc` with `λ ≠ 1`
forces `c = 0`. Three elements carry that file:

* `Zg = ω·1`, central, in the group because `ω³ = 1`;
* `Dg = diag(1, ω, ω²)`;
* `Pg`, the three-cycle permutation matrix, in `SU(3)` **because a three-cycle is EVEN**.

The question C3 turns on is whether those three have `SU(N)` analogues. This file settles the
arithmetic half of it, which is the half that decides whether the elements EXIST.

## What the arithmetic says

Write `ζ` for a primitive `N`-th root of unity.

**The centre element works for every `N ≥ 3` and fails at `N = 2`.** `χ(ζU) = ζχ(U)` gives
`∫χ = ζ∫χ`, hence `∫χ = 0` whenever `ζ ≠ 1`; and `∫χ² = ζ²∫χ²` gives `∫χ² = 0` whenever `ζ² ≠ 1`,
which is exactly `N ≥ 3`. At `N = 2` the centre is `{±1}`, the square is `1`, the projection is
vacuous, and `∫χ² = 1` rather than `0` — which is why `SU(2)` and `SU(3)` have genuinely different
answers and not merely different bookkeeping.

**The diagonal element is in `SU(N)` exactly when `N` is ODD.**
`det diag(1, ζ, …, ζ^{N-1}) = ζ^{0+1+⋯+(N-1)} = ζ^{N(N-1)/2}`, so it lies in `SU(N)` iff
`N ∣ N(N-1)/2`. `diag_in_SU_of_odd` and `diag_not_in_SU_of_even` below prove that is odd `N` exactly.

**The `N`-cycle is an even permutation exactly when `N` is ODD**, its sign being `(-1)^{N-1}` — the
same parity condition, and the reason `ContactValue` can say "a three-cycle is EVEN".

**So for odd `N ≥ 3` all three elements exist unchanged, and for even `N` two of them need a unit
scalar correction.** That correction is FREE, and `unit_scalar_cancels_in_ratio` is why: the
projection only ever sees `g_{ii}·conj(g_{kk})`, and multiplying the element by a unit scalar `c`
sends that to `|c|²·g_{ii}·conj(g_{kk})`, which is the same number. So a scalar chosen purely to fix
the determinant cannot disturb the projection it is inserted into.

## What this does and does not settle

It settles that the ELEMENTS exist at every `N ≥ 3`, with the parity obstruction identified and its
repair shown harmless. It does NOT carry `ContactValue`'s 134 pinnings across, nor the 176 in the
other eleven modules, and it does not evaluate any Haar integral at `N ≠ 3`. **The correction to
record is that `SU(N)` is reachable by this method for every `N ≥ 3`, not out of its reach** — what
it costs is the per-`N` work, not a new idea.

`N = 2` stays genuinely outside: the centre argument is vacuous there, and the tree's `SU(2)` answer
(`HaarMoments.haar_su2_second_moment`) was obtained by a different route for that reason.

DERIVED: no numeral is a magnitude. `2` is the order the centre argument needs `ζ` to exceed and the
divisor in `N(N-1)/2`; `1` is the determinant `SU` asks for; `3` is `SU(3)`, the instance the tree
has done.
-/

namespace MassGap.ColourGeneral

/-! ## 1. The determinant exponent -/

/-- The exponent in `det diag(1, ζ, …, ζ^{N-1}) = ζ^{∑ i}`, doubled so no division appears.
Gauss's sum, on `Fin N`. -/
theorem diag_det_exponent_two (N : ℕ) : (∑ i : Fin N, (i : ℕ)) * 2 = N * (N - 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N]
  exact Finset.sum_range_id_mul_two N

#print axioms diag_det_exponent_two

/-- **THE DIAGONAL ELEMENT IS IN `SU(N)` WHEN `N` IS ODD.** `N ∣ ∑ i`, so the determinant
`ζ^{∑ i}` is `1`. At `N = 2k+1` the sum is `(2k+1)k`, visibly a multiple of `N`. -/
theorem diag_in_SU_of_odd {N : ℕ} (hodd : Odd N) : N ∣ ∑ i : Fin N, (i : ℕ) := by
  obtain ⟨k, hk⟩ := hodd
  have h2 := diag_det_exponent_two N
  have hN1 : N - 1 = 2 * k := by omega
  refine ⟨k, ?_⟩
  have h3 : (∑ i : Fin N, (i : ℕ)) * 2 = 2 * (N * k) := by
    rw [h2, hN1]; ring
  omega

#print axioms diag_in_SU_of_odd

/-- **AND IT IS NOT, WHEN `N` IS EVEN.** At `N = 2k` with `k ≥ 1` the sum is `k(2k-1)`, and
`2k ∤ k(2k-1)` because `2k-1` is odd. So the natural diagonal element has determinant `ζ^{N/2} ≠ 1`
and a unit scalar correction is needed — which `unit_scalar_cancels_in_ratio` shows is free. -/
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

/-- The same parity governs the permutation: an `N`-cycle has sign `(-1)^{N-1}`, so it is EVEN
exactly when `N` is odd. Stated on the exponent, which is the part that decides it. -/
theorem cycle_even_iff_odd (N : ℕ) (hN : 1 ≤ N) : Even (N - 1) ↔ Odd N := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩

#print axioms cycle_even_iff_odd

/-! ## 2. Why the repair at even `N` is free -/

/-- **A UNIT SCALAR CANCELS IN THE PROJECTION'S RATIO.**

The invariant projection only ever sees `g_{ii} · conj(g_{kk})`. Multiplying the translating element
by a scalar `c` with `c · conj c = 1` sends that to `(c g_{ii}) · conj(c g_{kk}) = g_{ii} conj(g_{kk})`
— the same number. So the scalar chosen purely to fix a determinant at even `N` cannot disturb the
projection it is inserted into, and the phases `ζ^{i-k}` the argument runs on are unchanged.

DERIVED: `1` is the unit-modulus condition, not a magnitude. -/
theorem unit_scalar_cancels_in_ratio {c : ℂ} (hc : c * star c = 1) (z w : ℂ) :
    (c * z) * star (c * w) = z * star w := by
  have h : (c * z) * star (c * w) = (c * star c) * (z * star w) := by
    rw [star_mul]
    ring
  rw [h, hc, one_mul]

#print axioms unit_scalar_cancels_in_ratio

/-! ### One step deliberately not taken

The existence of the correcting scalar itself — every unit-modulus complex number has `N`-th roots —
is standard and is NOT proved here. Nothing above needs it: `unit_scalar_cancels_in_ratio` already
shows that ANY such scalar is harmless to the projection, so the repair's soundness does not depend
on exhibiting one. Recorded so the omission is deliberate rather than overlooked.
-/

end MassGap.ColourGeneral
