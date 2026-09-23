import MassGap.CellPivot
import MassGap.CellPerturb

/-!
# MassGap.CellBridge — carrying eigenvalue certificates from the rational cell to the real cell

`CellPivot` certifies eigenvalue gaps for the rational cell operator `HcellR jmax (q : ℚ)`. The rest
of the development states its cell bounds as `CellGapAtLeastR jmax (lam : ℝ) g`, which is about
`HcellRr jmax (lam : ℝ)`. `CellPerturb.HcellR_eq_HcellRr` equates the two matrices, and `CellCover`
rewrites along that equality.

An equality of matrices does not by itself move a statement about eigenvalues.
`Matrix.IsHermitian.eigenvalues` takes the Hermiticity proof as an argument, so
`(HcellR_isHermitian …).eigenvalues` and `(HcellRr_isHermitian …).eigenvalues` are two different
functions even once the matrices are known equal. `eigenvalues_congr` supplies the transport:
substituting the matrix equality puts both Hermiticity proofs in the same `Prop`, where proof
irrelevance is definitional in Lean 4.

On top of that the module exports `cellGapAtLeastR_of_pivot`, which turns a `CellPivot`-shaped gap
statement into a `CellGapAtLeastR`, and two instantiations of it at `jmax = 8` — one from the
absolute route at `λ = 4/25`, one from the relative route at `λ = 203/100` — together with a `norm_num`
comparison of the relative value against the constant `CellCover.cell_gap_on_range` carries.

Scope: everything here is transport of certificates that already exist. No new spectral bound is
proved, and the interval statement `CellCover.cell_gap_on_range` is unchanged — it is uniform on
`[4/25, 169/25]` and so is set by its worst point, which the pointwise statements below do not
address.
-/

namespace MassGap.CellBridge

open MassGap.CellEnclosure

/-- Equal Hermitian matrices have equal eigenvalue functions: given `h : A = B` and Hermiticity proofs
`hA` of `A` and `hB` of `B`, `hA.eigenvalues = hB.eigenvalues`.

`Matrix.IsHermitian.eigenvalues` is indexed by the Hermiticity proof, so the two sides are not the
same term before the substitution. After `subst h` both proofs inhabit `A.IsHermitian`, proof
irrelevance is definitional in Lean 4, and `rfl` closes it.

Scope: stated for real square matrices `Matrix (Fin n) (Fin n) ℝ` at arbitrary `n`, with `n` implicit;
it is not specific to the cell operators. -/
theorem eigenvalues_congr {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B) :
    hA.eigenvalues = hB.eigenvalues := by
  subst h
  rfl

/-- The rational cell and the real cell at the coerced coupling have the same eigenvalue function:
`(HcellR_isHermitian jmax lam).eigenvalues = (HcellRr_isHermitian jmax (lam : ℝ)).eigenvalues`, for
every `jmax : ℕ` and every rational `lam`.

`eigenvalues_congr` applied to `CellPerturb.HcellR_eq_HcellRr`. The coupling on the right is the image
of `lam` under the `ℚ → ℝ` coercion, not an arbitrary real. -/
theorem eigenvalues_HcellR_eq (jmax : ℕ) (lam : ℚ) :
    (HcellR_isHermitian jmax lam).eigenvalues
      = (HcellRr_isHermitian jmax (lam : ℝ)).eigenvalues :=
  eigenvalues_congr _ _ (HcellR_eq_HcellRr jmax lam)

/-- A gap statement about the rational cell's eigenvalues becomes one about the real cell.

The hypothesis is the shape both `CellPivot` routes produce once the ground-state clause is dropped:
some index `i₀` such that every other eigenvalue of `HcellR jmax lam` exceeds the `i₀`-th by at least
`g`. The conclusion is `CellGapAtLeastR jmax (lam : ℝ) g`. The proof is a rewrite by
`eigenvalues_HcellR_eq`, so the two carry identical content.

Scope: `i₀` is not required to index the smallest eigenvalue, and `g` is not required to be positive;
the coupling is a rational coerced into `ℝ`. -/
theorem cellGapAtLeastR_of_pivot {jmax : ℕ} {lam : ℚ} {g : ℝ}
    (h : ∃ i₀, ∀ i, i ≠ i₀ →
      (HcellR_isHermitian jmax lam).eigenvalues i₀ + g
        ≤ (HcellR_isHermitian jmax lam).eigenvalues i) :
    CellGapAtLeastR jmax (lam : ℝ) g := by
  rw [eigenvalues_HcellR_eq] at h
  exact h

/-- `CellGapAtLeastR 8 ((4 / 25 : ℚ) : ℝ) (2747 / 10000)`, obtained by transporting
`CellPivot.cell_gap_4_25` onto the real cell.

`lam` is passed explicitly to `cellGapAtLeastR_of_pivot`. Left implicit, unification has to solve
`((?lam : ℚ) : ℝ) =?= (4 / 25 : ℝ)` through the `ℚ → ℝ` coercion, which on a cell of this dimension
does not fail fast. Naming the rational makes both sides the same term by construction.

DERIVED: `8` is `jmax`, the cell truncation level the certificate was produced at. `4 / 25` is the
coupling, the left endpoint of the range `CellCover` covers. `2747 / 10000` is the gap value
`CellPivot.cell_gap_4_25` carries. All three are read off that certificate; none is chosen here. -/
theorem cell_gap_at_4_25 :
    CellGapAtLeastR 8 (((4 / 25 : ℚ) : ℝ)) (2747 / 10000) :=
  cellGapAtLeastR_of_pivot (jmax := 8) (lam := (4 / 25 : ℚ)) (g := (2747 / 10000 : ℝ))
    ⟨(CellPivot.cell_gap_4_25).choose, (CellPivot.cell_gap_4_25).choose_spec.2⟩

/-- `CellGapAtLeastR 8 ((203 / 100 : ℚ) : ℝ) (484 / 225)`, obtained by transporting
`CellPivot.rel_cell_gap_203_100` onto the real cell.

This is a statement at one coupling. `CellCover.cell_gap_on_range` is an interval statement holding
uniformly on `[4/25, 169/25]`, so its constant is set at the worst point of that range; the two are
bounds of different kinds, and `cell_gap_203_100_gt_floor` compares the numbers.

DERIVED: `8` is `jmax`, the cell truncation level. `203 / 100` is the coupling the relative route was
certified at. `484 / 225` is the gap `CellPivot.rel_cell_gap_203_100` carries. All three come from
that certificate. -/
theorem cell_gap_big_at_203_100 :
    CellGapAtLeastR 8 (((203 / 100 : ℚ) : ℝ)) (484 / 225) :=
  cellGapAtLeastR_of_pivot (jmax := 8) (lam := (203 / 100 : ℚ)) (g := (484 / 225 : ℝ))
    ⟨(CellPivot.rel_cell_gap_203_100).choose,
      (CellPivot.rel_cell_gap_203_100).choose_spec.2⟩

/-- The exact rational constant `CellCover.cell_gap_on_range` carries is strictly less than
`484 / 225`.

A `norm_num` comparison of two rationals, stated so that the relation between the uniform interval
constant and the pointwise value above is a theorem rather than a comparison of decimals in a comment.
It says nothing about either quantity being a gap; that content is in the two statements it names.

DERIVED: the fraction
`757208153840462049843660207489122776833562120275247490173 / 2756962257389109957235490077421880340994208596975891251200`
is the exact constant certified by `CellCover.cell_gap_on_range`, transcribed. `484 / 225` is the gap
value transported just above. Neither is chosen here. -/
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
