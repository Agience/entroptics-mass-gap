import Mathlib
import MassGap.Transfer

/-!
# MassGap.FiniteOrderTransfer — finite-order transfer operators on a `Transfer.TransferData`

Two theorems about a `Transfer.PreForm A` on any `ℝ`-module `A`:

* `form_sub_left`, `form_sub_right` — subtraction on either side of a `Transfer.PreForm`, obtained
  from the additive and scalar laws it carries.
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

end MassGap.FiniteOrderTransfer
