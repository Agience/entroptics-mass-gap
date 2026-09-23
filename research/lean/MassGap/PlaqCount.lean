import Mathlib
import MassGap.WilsonHypercubic

/-!
# MassGap.PlaqCount — the ordered plaquette type and the factor of two in the coupling

`WilsonHypercubic.Plaq d n = (Fin d × Fin d) × Site d n` carries an ordered pair of directions, so
`((μ,ν),x)` and `((ν,μ),x)` are distinct elements and `System.action` — a sum over
`Finset.univ : Finset (Plaq d n)` — visits both. This module proves that the two contribute equally
and that the diagonal contributes nothing, so the sum over the ordered type is twice the sum over
`μ < ν`.

The chain: `hol_word` writes the plaquette holonomy as the explicit four-letter product;
`hol_swap` shows the swapped ordering gives the inverse word; `coe_inv_eq_conjTranspose` and
`re_trace_inv` show `Re tr` is unchanged by inversion on `SU(N)`; `wilsonDensity_hol_swap` combines
them. `hol_diag` and `wilsonDensity_hol_diag` handle `μ = ν`. `sum_pair_eq_two_mul_lt` is the
`Finset` combinatorics for any symmetric function vanishing on the diagonal, and
`plaq_ordered_double_counts` applies it.

The consequence for the Boltzmann weight is `boltz_eq_std`:

    (sysWilson N d n).boltz β U = exp (-(2β) · Σ_{μ<ν} φ_W)

so the `β` this system carries stands where a source summing each plane once writes `2β`. The
conversion is a theorem here rather than an inference, so a number quoted against the once-per-plane
normalisation can be moved without re-deriving it.

Scope: `wilsonDensity_hol_diag` and everything downstream of it require `N ≠ 0`. Nothing here
constrains `d`, `n` or `β`, and `boltz_eq_std` holds at every real coupling including negative ones.

Build: `python research/code/lean_build.py build MassGap.PlaqCount`.
-/

namespace MassGap.PlaqCount

open MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonHypercubic
open MassGap.WilsonAction

variable {d n N : ℕ} [NeZero n]

/-! ### The boundary word, and what swapping the two directions does to it -/

/-- The holonomy of the hypercubic plaquette `((μ, ν), x)` written out:
`U (μ, x) * U (ν, shift μ x) * (U (μ, shift ν x))⁻¹ * (U (ν, x))⁻¹`. The boundary word `bd` has four
letters, so unfolding `wilsonHol` gives this product up to associativity and the trailing unit, which
`group` clears.

Holds for every `μ`, `ν` including `μ = ν`, and for every site and configuration.

DERIVED: no numeral. The `⁻¹` is the group inverse of `SU N`. -/
theorem hol_word (μ ν : Fin d) (x : Site d n) (U : Link d n → MassGap.SUN.SU N) :
    wilsonHol (bd (d := d) (n := n)) (((μ, ν), x) : Plaq d n) U
      = U (μ, x) * U (ν, shift μ x) * (U (μ, shift ν x))⁻¹ * (U (ν, x))⁻¹ := by
  have h : wilsonHol (bd (d := d) (n := n)) (((μ, ν), x) : Plaq d n) U
      = U (μ, x) * (U (ν, shift μ x) * ((U (μ, shift ν x))⁻¹ * ((U (ν, x))⁻¹ * 1))) := rfl
  rw [h]
  group

/-- The holonomy at `((ν, μ), x)` is the group inverse of the holonomy at `((μ, ν), x)`: swapping the
two directions reverses the order of the four letters and flips each orientation. Both sides are
expanded by `hol_word` and the identity is closed by `group`.

DERIVED: no numeral. The `⁻¹` is the group inverse. -/
theorem hol_swap (μ ν : Fin d) (x : Site d n) (U : Link d n → MassGap.SUN.SU N) :
    wilsonHol (bd (d := d) (n := n)) (((ν, μ), x) : Plaq d n) U
      = (wilsonHol (bd (d := d) (n := n)) (((μ, ν), x) : Plaq d n) U)⁻¹ := by
  rw [hol_word, hol_word]
  group

/-- The holonomy of a degenerate plaquette `((μ, μ), x)` is the group identity: the four-letter word
becomes `U (μ, x) * U (μ, shift μ x) * (U (μ, shift μ x))⁻¹ * (U (μ, x))⁻¹`, which cancels.

DERIVED: `1` is the identity element of `SU N`, the value the holonomy takes; it is a group element
and not a number. -/
theorem hol_diag (μ : Fin d) (x : Site d n) (U : Link d n → MassGap.SUN.SU N) :
    wilsonHol (bd (d := d) (n := n)) (((μ, μ), x) : Plaq d n) U = 1 := by
  rw [hol_word]
  group

/-- The matrix underlying `u⁻¹`, for `u : SU N`, is the conjugate transpose of the matrix underlying
`u`. Membership in `specialUnitaryGroup` gives membership in `unitaryGroup`, hence both one-sided
identities `uᴴu = 1` and `uuᴴ = 1`; the inverse is then pinned by associativity.

DERIVED: no numeral. `N` is the section variable and `Fin N` the matrix index type; the statement has
no literal. -/
theorem coe_inv_eq_conjTranspose (u : MassGap.SUN.SU N) :
    ((u⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
      = Matrix.conjTranspose (u : Matrix (Fin N) (Fin N) ℂ) := by
  have hu : (u : Matrix (Fin N) (Fin N) ℂ) ∈ Matrix.unitaryGroup (Fin N) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp u.2).1
  have h1 : Matrix.conjTranspose (u : Matrix (Fin N) (Fin N) ℂ)
      * (u : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hu
    rwa [Matrix.star_eq_conjTranspose] at this
  have h2 : ((u⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
      * (u : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel]
    exact Submonoid.coe_one _
  have h3 : (u : Matrix (Fin N) (Fin N) ℂ)
      * Matrix.conjTranspose (u : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hu
    rwa [Matrix.star_eq_conjTranspose] at this
  calc ((u⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
      = ((u⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) * 1 := by rw [Matrix.mul_one]
    _ = ((u⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
          * ((u : Matrix (Fin N) (Fin N) ℂ)
            * Matrix.conjTranspose (u : Matrix (Fin N) (Fin N) ℂ)) := by rw [h3]
    _ = (((u⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
          * (u : Matrix (Fin N) (Fin N) ℂ))
          * Matrix.conjTranspose (u : Matrix (Fin N) (Fin N) ℂ) := by rw [Matrix.mul_assoc]
    _ = Matrix.conjTranspose (u : Matrix (Fin N) (Fin N) ℂ) := by rw [h2, Matrix.one_mul]

/-- The real part of the trace is unchanged by inversion on `SU N`:
`(tr u⁻¹).re = (tr u).re`. By `coe_inv_eq_conjTranspose` and `Matrix.trace_conjTranspose`, the trace
of the inverse is the complex conjugate of the trace, and conjugation fixes the real part.

The imaginary parts differ by a sign; the statement is about the real part only.

DERIVED: no numeral. -/
theorem re_trace_inv (u : MassGap.SUN.SU N) :
    (Matrix.trace ((u⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re
      = (Matrix.trace ((u : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re := by
  rw [coe_inv_eq_conjTranspose, Matrix.trace_conjTranspose]
  simp

/-- The Wilson density at `((ν, μ), x)` equals the Wilson density at `((μ, ν), x)`: `hol_swap` turns
one holonomy into the inverse of the other, and `re_trace_inv` shows `wilsonDensity`, which reads
only the real part of the trace, cannot tell them apart.

So the two orderings of a plane carry the same energy, which is what makes the ordered type a
repetition rather than a different action.

DERIVED: no numeral. -/
theorem wilsonDensity_hol_swap (μ ν : Fin d) (x : Site d n)
    (U : Link d n → MassGap.SUN.SU N) :
    wilsonDensity (wilsonHol (bd (d := d) (n := n)) (((ν, μ), x) : Plaq d n) U)
      = wilsonDensity (wilsonHol (bd (d := d) (n := n)) (((μ, ν), x) : Plaq d n) U) := by
  rw [hol_swap]
  unfold wilsonDensity
  rw [re_trace_inv]

/-- The Wilson density at a degenerate plaquette `((μ, μ), x)` is `0`, for `N ≠ 0`: `hol_diag` sends
the holonomy to the identity and `wilsonDensity_one` evaluates the density there.

`N ≠ 0` is required because `wilsonDensity` normalises by `N`, so the value at the identity is only
`0` when there is a colour index to divide by.

DERIVED: `0` is the value `N` is required to differ from in `hN`, and the value of the density on the
diagonal — which is what makes the diagonal inert in a sum. -/
theorem wilsonDensity_hol_diag (hN : N ≠ 0) (μ : Fin d) (x : Site d n)
    (U : Link d n → MassGap.SUN.SU N) :
    wilsonDensity (wilsonHol (bd (d := d) (n := n)) (((μ, μ), x) : Plaq d n) U) = 0 := by
  rw [hol_diag]
  exact wilsonDensity_one hN

/-! ### The double count, as a statement about sums -/

/-- For `g : Fin d × Fin d → ℝ` invariant under `Prod.swap` and vanishing on the diagonal, the sum
over all ordered pairs equals twice the sum over the pairs with `p.1 < p.2`.

`Finset` combinatorics only: `Prod.swap` is an injection from `{p.1 < p.2}` onto `{p.2 < p.1}`, and
the complement of `{p.1 < p.2}` is `{p.2 < p.1}` together with a diagonal on which `g` is `0`.
Nothing about a lattice, a group or a holonomy enters; `g` is any real function with those two
properties.

DERIVED: `0` is the value `g` takes on the diagonal, which is what lets the two strict halves be
compared without a correction. `2` is the number of ordered pairs lying over each unordered pair
`{μ, ν}` with `μ ≠ ν`, so it is the size of the `Prod.swap` orbit and not a chosen coefficient. -/
theorem sum_pair_eq_two_mul_lt {d : ℕ} (g : Fin d × Fin d → ℝ)
    (hsymm : ∀ p : Fin d × Fin d, g p.swap = g p)
    (hdiag : ∀ a : Fin d, g (a, a) = 0) :
    ∑ p : Fin d × Fin d, g p
      = 2 * ∑ p ∈ Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2), g p := by
  classical
  have hTS : ∑ p ∈ Finset.univ.filter (fun p : Fin d × Fin d => p.2 < p.1), g p
      = ∑ p ∈ Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2), g p := by
    have himg : (Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2)).image Prod.swap
        = Finset.univ.filter (fun p : Fin d × Fin d => p.2 < p.1) := by
      ext p
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact hq
      · intro hp
        exact ⟨p.swap, hp, Prod.swap_swap p⟩
    have hinj : ∀ a ∈ Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2),
        ∀ b ∈ Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2),
        Prod.swap a = Prod.swap b → a = b := by
      intro a _ b _ h
      simpa using congrArg Prod.swap h
    rw [← himg, Finset.sum_image hinj]
    exact Finset.sum_congr rfl (fun p _ => hsymm p)
  have hnot : ∑ p ∈ Finset.univ.filter (fun p : Fin d × Fin d => ¬ p.1 < p.2), g p
      = ∑ p ∈ Finset.univ.filter (fun p : Fin d × Fin d => p.2 < p.1), g p := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact not_lt.mpr (le_of_lt hp)
    · intro p hp hpT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hpT
      obtain ⟨a, b⟩ := p
      have hab : a = b := le_antisymm (not_lt.mp hpT) (not_lt.mp hp)
      subst hab
      exact hdiag a
  have hsplit : ∑ p ∈ Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2), g p
      + ∑ p ∈ Finset.univ.filter (fun p : Fin d × Fin d => ¬ p.1 < p.2), g p
      = ∑ p : Fin d × Fin d, g p :=
    Finset.sum_filter_add_sum_filter_not Finset.univ _ g
  rw [← hsplit, hnot, hTS]
  ring

/-- For `N ≠ 0`, the Wilson density summed over all of `Plaq d n` is twice its sum over the
plaquettes with `q.1.1 < q.1.2`. The filtered set factors as a product of the direction filter with
all of `Site d n`, so the statement reduces by `Finset.sum_product` to `sum_pair_eq_two_mul_lt` at
the site-summed density, whose symmetry and diagonal-vanishing are `wilsonDensity_hol_swap` and
`wilsonDensity_hol_diag`.

The `<` is the order on `Fin d`, so the filtered range is the planes counted once each.

DERIVED: `0` is the value `N` is required to differ from in `hN`, inherited from
`wilsonDensity_hol_diag`. `2` is `sum_pair_eq_two_mul_lt`'s, the number of orderings of a plane. -/
theorem plaq_ordered_double_counts (hN : N ≠ 0) (U : Link d n → MassGap.SUN.SU N) :
    ∑ q : Plaq d n, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)
      = 2 * ∑ q ∈ Finset.univ.filter (fun q : Plaq d n => q.1.1 < q.1.2),
          wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U) := by
  classical
  have hfil : Finset.univ.filter (fun q : Plaq d n => q.1.1 < q.1.2)
      = (Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2))
        ×ˢ (Finset.univ : Finset (Site d n)) := by
    ext q
    simp [Finset.mem_filter, Finset.mem_product]
  rw [hfil, Finset.sum_product, Fintype.sum_prod_type]
  exact sum_pair_eq_two_mul_lt
    (fun p => ∑ x : Site d n, wilsonDensity (wilsonHol (bd (d := d) (n := n)) (p, x) U))
    (fun p => Finset.sum_congr rfl (fun x _ => wilsonDensity_hol_swap p.1 p.2 x U))
    (fun a => Finset.sum_eq_zero (fun x _ => wilsonDensity_hol_diag hN a x U))

/-- `(sysWilson N d n).action U` unfolds definitionally to the sum of `wilsonDensity` over the whole
ordered plaquette type `Plaq d n`. Proved by `rfl`; it records which range `System.action` sums over.

DERIVED: no numeral. -/
theorem sysWilson_action (U : Link d n → MassGap.SUN.SU N) :
    (sysWilson N d n).action U
      = ∑ q : Plaq d n, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U) := rfl

/-- For `N ≠ 0`, `(sysWilson N d n).action U` equals twice the Wilson density summed over the
plaquettes with `q.1.1 < q.1.2`. `sysWilson_action` followed by `plaq_ordered_double_counts`.

DERIVED: `0` is the value `N` is required to differ from in `hN`; `2` is the number of orderings of a
plane, carried from `plaq_ordered_double_counts`. -/
theorem sysWilson_action_eq_two_mul (hN : N ≠ 0) (U : Link d n → MassGap.SUN.SU N) :
    (sysWilson N d n).action U
      = 2 * ∑ q ∈ Finset.univ.filter (fun q : Plaq d n => q.1.1 < q.1.2),
          wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U) := by
  rw [sysWilson_action, plaq_ordered_double_counts hN U]

/-- For `N ≠ 0` and any real `β`, the Boltzmann weight of `sysWilson N d n` at coupling `β` is
`exp (-(2 * β) * Σ_{q.1.1 < q.1.2} wilsonDensity …)` — the weight built from the once-per-plane sum,
but at coupling `2 * β`. Unfolds `System.boltz` and rewrites by `sysWilson_action_eq_two_mul`.

The conversion as an equation: where this system writes `β`, a formulation summing each plane once
writes `2 * β`. `β` is unrestricted in sign.

DERIVED: `0` is the value `N` is required to differ from in `hN`. `2` is the number of orderings of a
plane, carried from `sysWilson_action_eq_two_mul` and appearing here inside the exponent, where it
multiplies `β`. -/
theorem boltz_eq_std (hN : N ≠ 0) (β : ℝ) (U : Link d n → MassGap.SUN.SU N) :
    (sysWilson N d n).boltz β U
      = Real.exp (-(2 * β) * ∑ q ∈ Finset.univ.filter (fun q : Plaq d n => q.1.1 < q.1.2),
          wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)) := by
  unfold System.boltz
  rw [sysWilson_action_eq_two_mul hN U]
  congr 1
  ring

#print axioms hol_word
#print axioms hol_swap
#print axioms hol_diag
#print axioms coe_inv_eq_conjTranspose
#print axioms re_trace_inv
#print axioms wilsonDensity_hol_swap
#print axioms wilsonDensity_hol_diag
#print axioms sum_pair_eq_two_mul_lt
#print axioms plaq_ordered_double_counts
#print axioms sysWilson_action
#print axioms sysWilson_action_eq_two_mul
#print axioms boltz_eq_std

end MassGap.PlaqCount
