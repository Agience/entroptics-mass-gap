import MassGap.CellPivot
import MassGap.CellPerturb

/-!
# Spending the pivot certificate: eigenvalue transport across `HcellR = HcellRr`

`CellPivot` certifies 61 couplings — 17 by the absolute route, 44 by the relative one — and **nothing
in the tree consumes a single one of them.** It is imported by the aggregate `MassGap.lean` and by
nothing else, and no declaration anywhere mentions `cell_gap_*` or `rel_cell_gap_*`. It is also the
most expensive module in the tree (~15GB to elaborate) and the one that OOM-killed a whole build.

**WHY THEY WERE UNSPENDABLE, stated correctly.** It is NOT that the rational cell and the real cell
were never identified: `CellPerturb.HcellR_eq_HcellRr` proves `HcellR jmax (q : ℚ) = HcellRr jmax (q : ℝ)`
and `CellCover` already rewrites along it nineteen times. What is missing is one step further on.
`CellPivot`'s theorems are not about the MATRIX, they are about its EIGENVALUES, and
`Matrix.IsHermitian.eigenvalues` takes the Hermiticity PROOF as an argument. Two proofs about
propositionally-equal matrices do not give definitionally-equal eigenvalue functions, so an equation
between the matrices does not by itself rewrite `(HcellR_isHermitian …).eigenvalues` into
`(HcellRr_isHermitian …).eigenvalues`. Nothing in the tree bridged that, so the certificates sat in a
module that imported into the aggregate and fed nothing.

`eigenvalues_congr` bridges it, in one line: substituting the matrix equality makes the two Hermiticity
proofs inhabit the same `Prop`, and proof irrelevance is definitional in Lean 4.

**WHAT SPENDING THEM IS WORTH.** `CellCover.cell_gap_on_range` carries
`757…173/2756…200 = 0.27465307` — the entropy floor `¼ log 3` — uniformly across `λ ∈ [4/25, 169/25]`,
because it is an INTERVAL statement and must hold at its worst point. The relative anchors already
proved far more pointwise, and the numbers were sitting unused: at `λ = 203/100` the certified gap is
`484/225 = 2.1511`, which is **7.83×** the covered value. `cell_gap_big_at_203_100` spends it.

**WHAT THIS DOES AND DOES NOT DO.** It transports existing certificates onto the operator the rest of
the tree speaks about; it proves no new spectral bound. The INTERVAL statement is NOT improved by it —
covering `[4/25, 169/25]` uniformly at a larger value still needs the radii re-earned at the larger
shifts, which is generated-file work in `CellCover`. What it removes is the reason that work looked
unavailable.
-/

namespace MassGap.CellBridge

open MassGap.CellEnclosure

/-- **Eigenvalues transport across an equality of Hermitian matrices.**

`Matrix.IsHermitian.eigenvalues` takes the Hermiticity PROOF as an argument, so two proofs about
propositionally-equal matrices do not give definitionally-equal eigenvalue functions. Substituting the
equality makes the two proofs inhabit the same `Prop`, and proof irrelevance is definitional in Lean 4,
so `rfl` closes it.

This is the step that was missing. The matrix equality it is applied to below already existed
(`CellPerturb.HcellR_eq_HcellRr`, used throughout `CellCover`); what did not exist was any way to carry
a statement about EIGENVALUES across it, which is the only form `CellPivot`'s certificates come in. -/
theorem eigenvalues_congr {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B) :
    hA.eigenvalues = hB.eigenvalues := by
  subst h
  rfl

/-- The Hermiticity proofs the rational and real cells carry give the same eigenvalue function.

The matrix equality is `CellPerturb.HcellR_eq_HcellRr`; this adds only the transport. -/
theorem eigenvalues_HcellR_eq (jmax : ℕ) (lam : ℚ) :
    (HcellR_isHermitian jmax lam).eigenvalues
      = (HcellRr_isHermitian jmax (lam : ℝ)).eigenvalues :=
  eigenvalues_congr _ _ (HcellR_eq_HcellRr jmax lam)

/-- **SPENDING A PIVOT CERTIFICATE.** Any `CellPivot` gap statement — absolute or relative, they share
this shape once the ground-state clause is dropped — becomes a `CellGapAtLeastR` about the operator the
rest of the development uses. -/
theorem cellGapAtLeastR_of_pivot {jmax : ℕ} {lam : ℚ} {g : ℝ}
    (h : ∃ i₀, ∀ i, i ≠ i₀ →
      (HcellR_isHermitian jmax lam).eigenvalues i₀ + g
        ≤ (HcellR_isHermitian jmax lam).eigenvalues i) :
    CellGapAtLeastR jmax (lam : ℝ) g := by
  rw [eigenvalues_HcellR_eq] at h
  exact h

/-- **THE ABSOLUTE ROUTE, SPENT.** `CellPivot.cell_gap_4_25` at the bottom of the covered range.

`lam` is passed EXPLICITLY. Left implicit, Lean must solve `((?lam : ℚ) : ℝ) =?= (4/25 : ℝ)` — a
unification through the `ℚ → ℝ` coercion — and that times out at `isDefEq` on a 17-dimensional cell
rather than failing fast. Naming the rational makes both sides the same term by construction. -/
theorem cell_gap_at_4_25 :
    CellGapAtLeastR 8 (((4 / 25 : ℚ) : ℝ)) (2747 / 10000) :=
  cellGapAtLeastR_of_pivot (jmax := 8) (lam := (4 / 25 : ℚ)) (g := (2747 / 10000 : ℝ))
    ⟨(CellPivot.cell_gap_4_25).choose, (CellPivot.cell_gap_4_25).choose_spec.2⟩

/-- **THE RELATIVE ROUTE, SPENT — AND IT IS 7.83× THE COVERED VALUE.**

`CellCover.cell_gap_on_range` certifies `0.27465307` uniformly on `[4/25, 169/25]`. At `λ = 203/100`
the pivot certificate proves `484/225 = 2.15111` for the same operator. The interval statement is not
wrong; it is uniform, and uniformity over a range where the gap grows monotonically costs everything
above the left endpoint. -/
theorem cell_gap_big_at_203_100 :
    CellGapAtLeastR 8 (((203 / 100 : ℚ) : ℝ)) (484 / 225) :=
  cellGapAtLeastR_of_pivot (jmax := 8) (lam := (203 / 100 : ℚ)) (g := (484 / 225 : ℝ))
    ⟨(CellPivot.rel_cell_gap_203_100).choose,
      (CellPivot.rel_cell_gap_203_100).choose_spec.2⟩

/-- **AND IT STRICTLY EXCEEDS THE ENTROPY FLOOR THE COVER CARRIES**, stated so the improvement is a
theorem rather than a comparison of decimals in a comment. -/
theorem cell_gap_203_100_gt_floor :
    (757208153840462049843660207489122776833562120275247490173 /
      2756962257389109957235490077421880340994208596975891251200 : ℝ) < 484 / 225 := by
  norm_num

#print axioms eigenvalues_congr
#print axioms eigenvalues_HcellR_eq
#print axioms cellGapAtLeastR_of_pivot
#print axioms cell_gap_at_4_25
#print axioms cell_gap_big_at_203_100
#print axioms cell_gap_203_100_gt_floor

end MassGap.CellBridge
