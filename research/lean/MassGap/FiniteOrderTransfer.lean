import Mathlib
import MassGap.ClayAssembly

/-!
# MassGap.FiniteOrderTransfer — a POSITIVE finite-order transfer operator is the identity

`ClayAssembly.TransferMovesSomething` is the open item behind C1's Hamiltonian: an operator on
`GNSHilbert.ymH` that is not the identity. `ym_target_discharged_trivially` shows every operator the
tree can currently build fails it, and `GNSHilbert.shiftSlab_eq_id` shows the slab shift IS the
identity on `SlabShiftStable`'s own premise. Both are findings about particular constructions.

**This file gives the general reason, and it is not a fact about those constructions.**

## The statement

Let `T` be self-adjoint for the reflection form, contractive, of finite order (`T^n = 1`), and
POSITIVE in the operator sense `0 ≤ form (T x) x`. Then `T x = x` for every `x`, in the form — so it
is the identity on the GNS space and `TransferMovesSomething` fails.

## Why each hypothesis is there, and which one is the physics

* **finite order** is what a periodic lattice gives: translation by one step in a direction of
  extent `n` has `T^n = 1` on the nose. It is not an approximation and not a choice of boundary
  condition that could be dropped — a torus is a torus.
* **contractive** and **self-adjoint** are `TransferData`'s own fields.
* **positive** is the physics: `T = e^{-H}` with `H` self-adjoint is EQUIVALENT to `T` positive, and
  a Hamiltonian is what C1 asks for. Without it the argument still gives `T² = 1` — a self-adjoint
  involution, spectrum in `{±1}` — and `-log T` does not exist on the `-1` part. So dropping
  positivity does not rescue a Hamiltonian; it only changes the failure from `H = 0` to `H`
  undefined.

## The proof, which is three lines of algebra

`finite_order_contraction_is_isometry` squeezes the contraction chain and gives
`form (T x) (T x) = form x x`. Polarising that gives `form (T x) (T y) = form x y`, and with
`T_symm` that is `form (T² x) y = form x y` — `T² = 1` in the form. Then put `z = T x - x`:

    form (T z) z = form (T²x - Tx) (Tx - x) = form (x - Tx) (Tx - x) = - form z z

and positivity forces `form z z ≤ 0`, while `form_nonneg` forces `form z z ≥ 0`.

**The vector `z = T x - x` is the whole of it.** Positivity is applied not to `x` but to the
DISPLACEMENT, where the involution turns the form's sign around.

## What this does to the plan

`LatticeTranslNoGo` puts C2 (infinite volume) strictly before C6. This puts it before C1's
Hamiltonian as well, and for the same cause: a finite periodic lattice has finite-order translations,
and a finite-order symmetry cannot carry a spectrum. So C2 gates C1, C5 and C6 — three of the nine
rows — and is the single gate rather than one of several.

DERIVED: no numeral here is a magnitude. `1` in `1 ≤ n` is the smallest order for which the chain
has a step to squeeze, `0` is the positivity bound, and `2` counts the cross terms a symmetric form
produces. `n` is a variable.
-/

namespace MassGap.FiniteOrderTransfer

open MassGap

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-! ## 0. Subtraction in the form

`Transfer.PreForm` carries `form_add_left`, `form_add_right`, `form_smul_left` and
`form_smul_right`, and no subtraction lemma. Both are one rewrite from what is there, and the
displacement `T x - x` is the only vector this file cares about, so they are needed immediately. -/

theorem form_sub_left (P : Transfer.PreForm A) (x y z : A) :
    P.form (x - y) z = P.form x z - P.form y z := by
  have h : x - y = x + (-1 : ℝ) • y := by rw [neg_one_smul]; abel
  rw [h, P.form_add_left, P.form_smul_left]
  ring

#print axioms form_sub_left

theorem form_sub_right (P : Transfer.PreForm A) (x y z : A) :
    P.form x (y - z) = P.form x y - P.form x z := by
  rw [P.form_symm x (y - z), form_sub_left, P.form_symm y x, P.form_symm z x]

#print axioms form_sub_right

/-! ## 1. Polarisation: an isometry of the form preserves it off the diagonal -/

/-- **A map preserving the diagonal of a symmetric bilinear form preserves the form.** Standard
polarisation, stated for `D.T` because that is the only map it is used on. -/
theorem form_polarise (D : Transfer.TransferData A) (n : ℕ) (hn : 1 ≤ n)
    (hper : ∀ y : A, (fun z => D.T z)^[n] y = y) (x y : A) :
    D.form (D.T x) (D.T y) = D.form x y := by
  have hx := MassGap.ClayAssembly.finite_order_contraction_is_isometry D n hn hper x
  have hy := MassGap.ClayAssembly.finite_order_contraction_is_isometry D n hn hper y
  have hxy := MassGap.ClayAssembly.finite_order_contraction_is_isometry D n hn hper (x + y)
  have hTadd : D.T (x + y) = D.T x + D.T y := map_add _ _ _
  rw [hTadd] at hxy
  have e1 : D.form (D.T x + D.T y) (D.T x + D.T y)
      = D.form (D.T x) (D.T x) + 2 * D.form (D.T x) (D.T y) + D.form (D.T y) (D.T y) := by
    rw [D.toPreForm.form_add_left, D.toPreForm.form_add_right, D.toPreForm.form_add_right,
      D.toPreForm.form_symm (D.T y) (D.T x)]
    ring
  have e2 : D.form (x + y) (x + y)
      = D.form x x + 2 * D.form x y + D.form y y := by
    rw [D.toPreForm.form_add_left, D.toPreForm.form_add_right, D.toPreForm.form_add_right,
      D.toPreForm.form_symm y x]
    ring
  rw [e1, e2] at hxy
  linarith

#print axioms form_polarise

/-- **AND THEREFORE `T² = 1` IN THE FORM.** `T_symm` moves one `T` across, polarisation cancels the
pair. No positivity is used here, so this holds of any finite-order contraction — the operator is a
self-adjoint INVOLUTION, spectrum in `{±1}`. -/
theorem T_sq_eq (D : Transfer.TransferData A) (n : ℕ) (hn : 1 ≤ n)
    (hper : ∀ y : A, (fun z => D.T z)^[n] y = y) (x y : A) :
    D.form (D.T (D.T x)) y = D.form x y := by
  rw [D.T_symm (D.T x) y]
  exact form_polarise D n hn hper x y

#print axioms T_sq_eq

/-! ## 2. Positivity closes it -/

/-- **A POSITIVE FINITE-ORDER TRANSFER OPERATOR IS THE IDENTITY**, in the form.

`form (T x - x) (T x - x) = 0` says `T x - x` is in the reflection form's null space, so `T` descends
to the identity on the GNS space and `ClayAssembly.TransferMovesSomething` fails for it.

The positivity hypothesis `0 ≤ form (T z) z` is the operator-positivity that makes `T = e^{-H}` with
`H` self-adjoint; it is NOT `ReflForm.form_nonneg`, which is positivity of the form and is already a
field. Applying it to the DISPLACEMENT `z = T x - x` rather than to `x` is the whole argument. -/
theorem positive_finite_order_transfer_is_identity (D : Transfer.TransferData A) (n : ℕ)
    (hn : 1 ≤ n) (hper : ∀ y : A, (fun z => D.T z)^[n] y = y)
    (hpos : ∀ z : A, 0 ≤ D.form (D.T z) z) (x : A) :
    D.form (D.T x - x) (D.T x - x) = 0 := by
  set z : A := D.T x - x with hz
  have hTz : D.T z = D.T (D.T x) - D.T x := by
    rw [hz, map_sub]
  have hiso := MassGap.ClayAssembly.finite_order_contraction_is_isometry D n hn hper x
  have hsq1 := T_sq_eq D n hn hper x (D.T x)
  have hsq2 := T_sq_eq D n hn hper x x
  -- expand  form (T z) z  and  form z z  in the four scalars the form takes on `x` and `T x`
  have hexp : D.form (D.T z) z
      = D.form (D.T (D.T x)) (D.T x) - D.form (D.T (D.T x)) x
        - D.form (D.T x) (D.T x) + D.form (D.T x) x := by
    rw [hTz, hz, form_sub_left D.toPreForm, form_sub_right D.toPreForm,
      form_sub_right D.toPreForm]
    ring
  have hzz : D.form z z
      = D.form (D.T x) (D.T x) - 2 * D.form (D.T x) x + D.form x x := by
    rw [hz, form_sub_left D.toPreForm, form_sub_right D.toPreForm, form_sub_right D.toPreForm,
      D.toPreForm.form_symm x (D.T x)]
    ring
  have hsym : D.form x (D.T x) = D.form (D.T x) x := D.toPreForm.form_symm x (D.T x)
  have hkey : D.form (D.T z) z = - D.form z z := by
    rw [hexp, hzz, hsq1, hsq2, hiso, hsym]
    ring
  have h1 := hpos z
  have h2 := D.form_nonneg z
  rw [hkey] at h1
  linarith

#print axioms positive_finite_order_transfer_is_identity

/-- **SO `TransferMovesSomething` FAILS FOR EVERY POSITIVE FINITE-ORDER TRANSFER**, stated on the
form so it does not depend on how the completion is built.

This is the general form of `GNSHilbert.shiftSlab_eq_id` and of what
`ClayAssembly.ym_target_discharged_trivially` observes: the triviality is not an artifact of the slab
construction or of a particular premise, it is forced by the period of the lattice. -/
theorem no_motion_of_positive_finite_order (D : Transfer.TransferData A) (n : ℕ)
    (hn : 1 ≤ n) (hper : ∀ y : A, (fun z => D.T z)^[n] y = y)
    (hpos : ∀ z : A, 0 ≤ D.form (D.T z) z) :
    ∀ x : A, D.form (D.T x - x) (D.T x - x) = 0 :=
  fun x => positive_finite_order_transfer_is_identity D n hn hper hpos x

#print axioms no_motion_of_positive_finite_order

/-- **AND WITHOUT POSITIVITY THERE IS STILL NO HAMILTONIAN**, which is why dropping the hypothesis
does not open a route. `T_sq_eq` gives `T² = 1` from finite order and contractivity alone, so the
spectrum lies in `{±1}`; `-log T` is `0` on the `+1` part and undefined on the `-1` part. Recorded as
a theorem so the horn is not mistaken for an opening: the square of the displacement map vanishes
identically in the form. -/
theorem involution_without_positivity (D : Transfer.TransferData A) (n : ℕ)
    (hn : 1 ≤ n) (hper : ∀ y : A, (fun z => D.T z)^[n] y = y) (x y : A) :
    D.form (D.T (D.T x) - x) y = 0 := by
  rw [form_sub_left D.toPreForm]
  rw [T_sq_eq D n hn hper x y]
  ring

#print axioms involution_without_positivity

/-- **WHAT AN `I4` WITNESS MUST BE, stated as the obligation rather than as a prohibition.**

The contrapositive of `positive_finite_order_transfer_is_identity`: a POSITIVE transfer that moves
something has INFINITE order. That is the checkable criterion a candidate must meet, and it is the
precise scope of this file -- the no-go is about order, not about being built on a lattice.

**`ClayAssembly`'s scoping is the one to keep:** `HalfLineTransfer.shiftObs_pow_period` proves
`(shiftObs τ)ⁿ = id` on every observable of the periodic lattice with no hypothesis, so any
`TransferData` whose `T` is ASSEMBLED FROM LATTICE TRANSLATIONS has finite order and is caught.
An operator that is not so assembled is not caught, and the tree has one:
`SliceTransferSelfAdjoint.transferCLM` is an integral operator on `L²` of a single slice, bounded
(`norm_transferCLM_le`), self-adjoint (`isSelfAdjoint_transferCLM`) and nonzero
(`transferCLM_ne_zero`), and nothing makes it a translation. **So this file does not close C1's
Hamiltonian; it closes the translation route to it.** `transferCLM` has since acquired POSITIVITY
(`TransferGaussian.transferKernel_posDef`) and INJECTIVITY
(`TransferGaussian.transferCLM_injective`); what it still lacks for C1 is `0 ∉ spectrum` and a carrier
on `ymH`.

**And there is now a SECOND, independent route to this no-go.** `TransferGap.finite_order_fails_gap`
reaches the same conclusion from a spectral GAP instead of from operator positivity, assuming no
positivity at all. `TransferGap.gap_moves_something` goes further: a gap IMPLIES
`TransferMovesSomething`, so the open item is a consequence of the gap rather than a separate
obligation beside it.

DERIVED: `1 ≤ n` is the smallest order the squeeze has a step for. -/
theorem moves_something_forces_infinite_order (D : Transfer.TransferData A)
    (hpos : ∀ z : A, 0 ≤ D.form (D.T z) z)
    (hmoves : ∃ x : A, D.form (D.T x - x) (D.T x - x) ≠ 0) :
    ¬ ∃ n : ℕ, 1 ≤ n ∧ ∀ y : A, (fun z => D.T z)^[n] y = y := by
  rintro ⟨n, hn, hper⟩
  obtain ⟨x, hx⟩ := hmoves
  exact hx (positive_finite_order_transfer_is_identity D n hn hper hpos x)

#print axioms moves_something_forces_infinite_order

end MassGap.FiniteOrderTransfer
