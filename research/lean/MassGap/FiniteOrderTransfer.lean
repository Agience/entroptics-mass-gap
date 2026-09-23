import Mathlib
import MassGap.ClayAssembly

/-!
# MassGap.FiniteOrderTransfer — finite-order transfer operators on a `Transfer.TransferData`

Five theorems about a `D : Transfer.TransferData A` whose operator `D.T` has finite order in the
sense `(fun z => D.T z)^[n] y = y` for all `y`, with `1 ≤ n`. All conclusions are equations or
inequalities in `D.form`; nothing here builds a Hilbert space or takes a quotient.

* `form_sub_left`, `form_sub_right` — subtraction on either side of a `Transfer.PreForm`, obtained
  from the additive and scalar laws it carries.
* `form_polarise` — if `D.T` preserves the diagonal of the form (which
  `ClayAssembly.finite_order_contraction_is_isometry` supplies from finite order and contractivity),
  it preserves the form off the diagonal: `form (T x) (T y) = form x y`.
* `T_sq_eq` — moving one `T` across with `D.T_symm` turns that into `form (T (T x)) y = form x y`,
  so `T` squares to the identity as seen by the form. No positivity is used.
* `positive_finite_order_transfer_is_identity` and its `∀ x` restatement
  `no_motion_of_positive_finite_order` — adding operator positivity `0 ≤ form (T z) z`,
  `form (T x - x) (T x - x) = 0`: the displacement lies in the form's null cone. The argument applies
  positivity to the displacement `z = T x - x`, where `T_sq_eq` makes `form (T z) z = - form z z`,
  and `D.form_nonneg` supplies the opposite inequality.
* `involution_without_positivity` — `form (T (T x) - x) y = 0` without any positivity hypothesis.
* `moves_something_forces_infinite_order` — the contrapositive: a positive `D.T` with a displacement
  outside the null cone satisfies no `(fun z => D.T z)^[n] = id` with `1 ≤ n`.

Scope: `A` is any `ℝ`-module; the hypothesis `hpos` is operator positivity `0 ≤ form (T z) z`, which
is distinct from `ReflForm.form_nonneg`, already a field of the structure. The conclusions are
statements in the form — `form (T x - x) (T x - x) = 0` — not equalities of vectors, so they say
`T x - x` is null for the form rather than zero in `A`. Finite order is a hypothesis; no statement
here derives it from a lattice.

DERIVED across the file: `1` appears only as the lower bound in `1 ≤ n`, the smallest order for
which the contraction chain has a step; `0` appears as the lower bound of operator positivity and as
the value the form takes on the displacement. `n` is a variable.
-/

namespace MassGap.FiniteOrderTransfer

open MassGap

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-! ## 0. Subtraction in the form

`Transfer.PreForm` carries `form_add_left`, `form_add_right`, `form_smul_left` and
`form_smul_right`, and no subtraction lemma. `form_sub_left` rewrites `x - y` as `x + (-1 : ℝ) • y`
and applies the additive and scalar laws; `form_sub_right` transports it through `form_symm`. Both
hold for any `Transfer.PreForm A` and any three vectors, with no hypothesis.

DERIVED: no numeral appears in either statement. -/

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

/-! ## 1. Polarisation, and `T` squaring to the identity in the form -/

/-- For a `Transfer.TransferData A` whose operator has order `n` with `1 ≤ n`,
`D.form (D.T x) (D.T y) = D.form x y` at every pair `x`, `y`.

The proof invokes `ClayAssembly.finite_order_contraction_is_isometry` at `x`, `y` and `x + y`,
expands both `form (u + v) (u + v)` sides with the additive laws and `form_symm`, and cancels by
`linarith`. This is polarisation, stated for `D.T` because that is the only map it is applied to.

Scope: the finite-order hypothesis is `(fun z => D.T z)^[n] y = y` for every `y` — surjectivity of
the iterate is not enough. Contractivity and symmetry come from `TransferData`'s own fields, via the
isometry lemma.

DERIVED: `1` is the lower bound on the order `n`, the smallest order for which the contraction chain
has a step to squeeze. No other numeral appears in the statement. -/
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

/-- `D.form (D.T (D.T x)) y = D.form x y` at every pair `x`, `y`, for a `D.T` of order `n` with
`1 ≤ n`. `D.T_symm` moves one `D.T` onto the right argument and `form_polarise` cancels the pair.

Scope: no positivity hypothesis is used, so this holds of any finite-order contraction on the
structure. The conclusion is an identity in the form, not `D.T (D.T x) = x` in `A`: it says
`D.T (D.T x) - x` pairs to zero against everything, which is weaker unless the form is definite.

DERIVED: `1` is the lower bound on the order `n`. No other numeral appears in the statement. -/
theorem T_sq_eq (D : Transfer.TransferData A) (n : ℕ) (hn : 1 ≤ n)
    (hper : ∀ y : A, (fun z => D.T z)^[n] y = y) (x y : A) :
    D.form (D.T (D.T x)) y = D.form x y := by
  rw [D.T_symm (D.T x) y]
  exact form_polarise D n hn hper x y

#print axioms T_sq_eq

/-! ## 2. Adding operator positivity -/

/-- For a `D : Transfer.TransferData A` whose operator has order `n` with `1 ≤ n` and satisfies
operator positivity `0 ≤ D.form (D.T z) z` at every `z`, the displacement is null for the form:
`D.form (D.T x - x) (D.T x - x) = 0`, at every `x`.

The proof sets `z := D.T x - x`, expands `form (D.T z) z` and `form z z` in the four scalars the
form takes on `x` and `D.T x`, and uses `T_sq_eq` twice together with the isometry identity to get
`form (D.T z) z = - form z z`. Positivity then gives `form z z ≤ 0` and `D.form_nonneg` gives
`0 ≤ form z z`.

Scope: `hpos` is operator positivity, applied to the displacement rather than to `x`; it is a
separate hypothesis from `ReflForm.form_nonneg`, which is already a field. The conclusion places
`D.T x - x` in the form's null cone, which is equality to zero in `A` only when the form is
definite.

DERIVED: `1` is the lower bound on the order `n`; `0` occurs twice, as the lower bound in the
positivity hypothesis and as the value of the form on the displacement. -/
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

/-- `positive_finite_order_transfer_is_identity` with the vector `x` moved into the conclusion:
under the same hypotheses, `∀ x : A, D.form (D.T x - x) (D.T x - x) = 0`. The proof is that theorem
applied pointwise, so this adds no content beyond the quantifier placement.

Scope: stated on `D.form`, so it does not depend on how any completion of `A` is built.

DERIVED: `1` is the lower bound on the order `n`; `0` occurs twice, as the lower bound in the
positivity hypothesis and as the value of the form on each displacement. -/
theorem no_motion_of_positive_finite_order (D : Transfer.TransferData A) (n : ℕ)
    (hn : 1 ≤ n) (hper : ∀ y : A, (fun z => D.T z)^[n] y = y)
    (hpos : ∀ z : A, 0 ≤ D.form (D.T z) z) :
    ∀ x : A, D.form (D.T x - x) (D.T x - x) = 0 :=
  fun x => positive_finite_order_transfer_is_identity D n hn hper hpos x

#print axioms no_motion_of_positive_finite_order

/-- `D.form (D.T (D.T x) - x) y = 0` at every pair `x`, `y`, for a `D.T` of order `n` with `1 ≤ n`.
`form_sub_left` splits the left argument and `T_sq_eq` equates the two halves.

Scope: no positivity hypothesis is used here. The conclusion pairs `D.T (D.T x) - x` to zero against
every `y`, which is the form-level statement that `D.T` squares to the identity; it is not an
equation in `A`.

DERIVED: `1` is the lower bound on the order `n`; `0` is the value of the form. -/
theorem involution_without_positivity (D : Transfer.TransferData A) (n : ℕ)
    (hn : 1 ≤ n) (hper : ∀ y : A, (fun z => D.T z)^[n] y = y) (x y : A) :
    D.form (D.T (D.T x) - x) y = 0 := by
  rw [form_sub_left D.toPreForm]
  rw [T_sq_eq D n hn hper x y]
  ring

#print axioms involution_without_positivity

/-- The contrapositive of `positive_finite_order_transfer_is_identity`. If `D.T` satisfies operator
positivity `0 ≤ D.form (D.T z) z` at every `z`, and some `x` has
`D.form (D.T x - x) (D.T x - x) ≠ 0`, then there is no `n` with `1 ≤ n` and
`(fun z => D.T z)^[n] y = y` for all `y`.

The proof takes such an `n`, applies the forward theorem at the witness `x`, and contradicts `hx`.

Scope: the conclusion rules out finite order, not any other property. It applies to any
`TransferData` meeting `hpos`, whether or not `D.T` comes from a lattice translation; conversely it
says nothing about an operator that fails `hpos`.

DERIVED: `0` occurs twice, as the lower bound in the positivity hypothesis and as the value the
displacement's form is assumed to differ from; `1` is the lower bound on the order `n` inside the
negated existential. -/
theorem moves_something_forces_infinite_order (D : Transfer.TransferData A)
    (hpos : ∀ z : A, 0 ≤ D.form (D.T z) z)
    (hmoves : ∃ x : A, D.form (D.T x - x) (D.T x - x) ≠ 0) :
    ¬ ∃ n : ℕ, 1 ≤ n ∧ ∀ y : A, (fun z => D.T z)^[n] y = y := by
  rintro ⟨n, hn, hper⟩
  obtain ⟨x, hx⟩ := hmoves
  exact hx (positive_finite_order_transfer_is_identity D n hn hper hpos x)

#print axioms moves_something_forces_infinite_order

end MassGap.FiniteOrderTransfer
