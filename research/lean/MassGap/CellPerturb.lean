import MassGap.CellSpectrum

/-!
# MassGap.CellPerturb — the cell's quadratic form is Lipschitz in the coupling

## What this file supplies

`certify/cell_pivot_certificate.py` covers `λ ∈ [4/25, 169/25]` continuously: each of its 61
certified couplings carries a neighbourhood of radius `(certified gap − κ₀)/4`, and the
neighbourhoods overlap. `MassGap.CellPivot` transcribes the certified POINTS; lifting a grid to an
interval looks like it needs eigenvalue perturbation, and Mathlib has no Weyl inequality for
Hermitian matrices (it has Gershgorin, which is a different statement).

The two spectral facts the certificate is built from are stated in terms of QUADRATIC FORMS rather
than eigenvalues:

* `CellSpectrum.exists_eigenvalue_le_of_form` takes `ψ ⬝ᵥ (A *ᵥ ψ) ≤ r * (ψ ⬝ᵥ ψ)` and returns an
  eigenvalue `≤ r`;
* `CellSpectrum.atMostOne_eigenvalue_lt` takes `∀ x ∈ W, μ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)` on a subspace
  of corank at most one and returns "at most one eigenvalue `< μ`".

So the perturbation moves the FORM rather than an eigenvalue, and the form moves by an elementary
amount, proved here from the definition of `CellSpectrum.Hcell` and AM–GM. Feeding the moved form
back into the same two lemmas reproduces the gap at a neighbouring coupling.

## Where the constant 4 comes from

`Hcell` depends on `λ` only through its nearest-neighbour off-diagonal, which is `-λ`. So

    HcellR jmax lam - HcellR jmax lam' = (lam' - lam) • Adj jmax

with `Adj` the 0/1 nearest-neighbour adjacency matrix (`HcellR_sub_smul_adj`). Every row and every
column of `Adj` has at most two nonzero entries, so AM–GM gives
`|v ⬝ᵥ (Adj *ᵥ v)| ≤ 2 * (v ⬝ᵥ v)` (`adj_form_bound`), and the form moves by at most
`2|Δλ| (v ⬝ᵥ v)` (`HcellR_form_lipschitz`).

The certificate's `LIPSCHITZ = 4` is twice that because the gap is a DIFFERENCE of two eigenvalues:
the upper one moves down by at most `2|Δλ|` and the lower one moves up by at most `2|Δλ|`, so the
gap moves by at most `4|Δλ|`. The two halves are `cell_form_ge_of_form_ge` and
`cell_form_le_of_form_le` below, one per eigenvalue.
-/

namespace MassGap.CellEnclosure

open scoped Matrix
open Matrix

/-- The 0/1 nearest-neighbour adjacency matrix on the cell index set `Fin (dim jmax)` — the entire
`λ`-dependence of `CellSpectrum.Hcell`, with the coupling divided out.

DERIVED: the entries are not free. `Hcell` is `d i` on the diagonal, `-lam` where `|i-j| = 1`, and
`0` elsewhere, and `d i` does not contain `lam`. So `(Hcell lam - Hcell lam') / (lam' - lam)` is `0`
on the diagonal, `1` on the nearest-neighbour band and `0` off it — this matrix. That quotient is
`HcellR_sub_smul_adj`, an equation rather than an estimate, so a wrong entry or a scaling error here
would not typecheck there. -/
noncomputable def Adj (jmax : ℕ) : Matrix (Fin (dim jmax)) (Fin (dim jmax)) ℝ :=
  Matrix.of fun i j =>
    if i = j then 0 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0

/-- Every entry of `Adj` is nonnegative, which is what lets `adj_form_bound` drop an absolute value
entrywise.

DERIVED: `0` is the entry `Adj` takes off the nearest-neighbour band and on the diagonal; the only
other entry it takes is one. -/
theorem Adj_nonneg (jmax : ℕ) (i j : Fin (dim jmax)) : 0 ≤ Adj jmax i j := by
  unfold Adj
  simp only [Matrix.of_apply]
  split_ifs <;> norm_num

/-- `Adj` is symmetric: the band predicate `i.val + 1 = j.val ∨ j.val + 1 = i.val` is symmetric in
its two arguments, and the diagonal case is equal by reflexivity. -/
theorem Adj_symm (jmax : ℕ) (i j : Fin (dim jmax)) : Adj jmax i j = Adj jmax j i := by
  unfold Adj
  simp only [Matrix.of_apply]
  rcases eq_or_ne i j with h | h
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]
    exact if_congr or_comm rfl rfl

/-- An indicator over `Fin N` whose predicate pins `j.val` to a single value sums to at most `1`.
`hP` is that pinning: any two indices satisfying `P` are equal, so the filtered set has at most one
element.

DERIVED: `1` is that cardinality bound, and `0` is the indicator's other value; both come from the
summand `if P j.val then (1 : ℝ) else 0`. -/
private theorem sum_indicator_le_one {N : ℕ} (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ a b : Fin N, P a.val → P b.val → a = b) :
    (∑ j : Fin N, if P j.val then (1 : ℝ) else 0) ≤ 1 := by
  have h : (∑ j : Fin N, if P j.val then (1 : ℝ) else 0)
      = ((Finset.univ.filter (fun j : Fin N => P j.val)).card : ℝ) := by
    simp
  rw [h]
  have hc : (Finset.univ.filter (fun j : Fin N => P j.val)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact hP a b ha hb
  exact_mod_cast hc

/-- Every row of `Adj` sums to at most `2` — the index `i` has at most the two neighbours `i-1` and
`i+1`. The proof dominates the row by two indicators and applies `sum_indicator_le_one` to each.
This is the only structural fact the form bound needs.

DERIVED: `2` is those two neighbours, one indicator each. -/
theorem Adj_row_sum_le (jmax : ℕ) (i : Fin (dim jmax)) : ∑ j, Adj jmax i j ≤ 2 := by
  have hb : ∀ j : Fin (dim jmax), Adj jmax i j
      ≤ (if j.val = i.val + 1 then (1 : ℝ) else 0)
        + (if j.val + 1 = i.val then (1 : ℝ) else 0) := by
    intro j
    have hz : ∀ (c : Prop) [Decidable c], (0 : ℝ) ≤ if c then (1 : ℝ) else 0 := by
      intro c _; split_ifs <;> norm_num
    unfold Adj
    simp only [Matrix.of_apply]
    by_cases hij : i = j
    · subst hij
      have h1 : ¬ (i.val = i.val + 1) := by omega
      have h2 : ¬ (i.val + 1 = i.val) := by omega
      rw [if_pos rfl, if_neg h1, if_neg h2]
      norm_num
    · rw [if_neg hij]
      by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val
      · rw [if_pos hadj]
        rcases hadj with h | h
        · rw [if_pos h.symm]
          have := hz (j.val + 1 = i.val)
          linarith
        · rw [if_pos h]
          have := hz (j.val = i.val + 1)
          linarith
      · have h1 : ¬ (j.val = i.val + 1) := fun h => hadj (Or.inl h.symm)
        have h2 : ¬ (j.val + 1 = i.val) := fun h => hadj (Or.inr h)
        rw [if_neg hadj, if_neg h1, if_neg h2]
        norm_num
  calc ∑ j, Adj jmax i j
      ≤ ∑ j : Fin (dim jmax), ((if j.val = i.val + 1 then (1 : ℝ) else 0)
          + (if j.val + 1 = i.val then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum (fun j _ => hb j)
    _ = (∑ j : Fin (dim jmax), if j.val = i.val + 1 then (1 : ℝ) else 0)
          + (∑ j : Fin (dim jmax), if j.val + 1 = i.val then (1 : ℝ) else 0) :=
        Finset.sum_add_distrib
    _ ≤ 1 + 1 := by
        -- the predicates are given explicitly: `fun n => n + 1 = i.val` is not something
        -- higher-order unification recovers from the `ite` it appears in.
        refine add_le_add
          (sum_indicator_le_one (fun n => n = i.val + 1)
            (fun a b ha hb => Fin.val_injective (ha.trans hb.symm)))
          (sum_indicator_le_one (fun n => n + 1 = i.val)
            (fun a b ha hb => Fin.val_injective (by omega)))
    _ = 2 := by norm_num

/-- Every column of `Adj` sums to at most `2`, by `Adj_symm` and `Adj_row_sum_le`.

DERIVED: `2` is `Adj_row_sum_le`'s bound, carried across the transpose. -/
theorem Adj_col_sum_le (jmax : ℕ) (j : Fin (dim jmax)) : ∑ i, Adj jmax i j ≤ 2 := by
  have : ∑ i, Adj jmax i j = ∑ i, Adj jmax j i :=
    Finset.sum_congr rfl (fun i _ => Adj_symm jmax i j)
  rw [this]
  exact Adj_row_sum_le jmax j

/-- The adjacency form is bounded by twice the norm: `|v ⬝ᵥ (Adj jmax *ᵥ v)| ≤ 2 * (v ⬝ᵥ v)` for
every real `v`. AM–GM entrywise, against `Adj_row_sum_le` and `Adj_col_sum_le`. No spectral input,
so it holds at every `jmax` with no certificate behind it.

DERIVED: `2` is one factor from the row sum and one from the column sum — AM–GM halves each `v i v j`
into `(v i ^ 2 + v j ^ 2) / 2`, and the two halves add back to twice the norm. -/
theorem adj_form_bound (jmax : ℕ) (v : Fin (dim jmax) → ℝ) :
    |v ⬝ᵥ (Adj jmax *ᵥ v)| ≤ 2 * (v ⬝ᵥ v) := by
  have hvv : (v ⬝ᵥ v) = ∑ i, v i ^ 2 := by
    simp [dotProduct, sq]
  have hexp : v ⬝ᵥ (Adj jmax *ᵥ v) = ∑ i, ∑ j, Adj jmax i j * (v i * v j) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  rw [hexp]
  have habs : |∑ i, ∑ j, Adj jmax i j * (v i * v j)|
      ≤ ∑ i, ∑ j, Adj jmax i j * ((v i ^ 2 + v j ^ 2) / 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    rw [abs_mul, abs_of_nonneg (Adj_nonneg jmax i j)]
    refine mul_le_mul_of_nonneg_left ?_ (Adj_nonneg jmax i j)
    rw [abs_mul]
    nlinarith [sq_nonneg (|v i| - |v j|), abs_nonneg (v i), abs_nonneg (v j),
      sq_abs (v i), sq_abs (v j)]
  refine habs.trans ?_
  have hsplit : ∑ i, ∑ j, Adj jmax i j * ((v i ^ 2 + v j ^ 2) / 2)
      = (∑ i, ∑ j, Adj jmax i j * v i ^ 2 / 2)
        + (∑ i, ∑ j, Adj jmax i j * v j ^ 2 / 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hsplit, hvv]
  have hrow : (∑ i, ∑ j, Adj jmax i j * v i ^ 2 / 2) ≤ ∑ i, v i ^ 2 := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    have he : ∑ j, Adj jmax i j * v i ^ 2 / 2 = (v i ^ 2 / 2) * ∑ j, Adj jmax i j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [he]
    nlinarith [Adj_row_sum_le jmax i, sq_nonneg (v i)]
  have hcol : (∑ i, ∑ j, Adj jmax i j * v j ^ 2 / 2) ≤ ∑ i, v i ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have he : ∑ i, Adj jmax i j * v j ^ 2 / 2 = (v j ^ 2 / 2) * ∑ i, Adj jmax i j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [he]
    nlinarith [Adj_col_sum_le jmax j, sq_nonneg (v j)]
  linarith

/-- The coupling enters `HcellR` only through the adjacency:
`HcellR jmax lam - HcellR jmax lam' = ((lam' : ℝ) - (lam : ℝ)) • Adj jmax`, for rational `lam` and
`lam'`. An equation, entry by entry. -/
theorem HcellR_sub_smul_adj (jmax : ℕ) (lam lam' : ℚ) :
    HcellR jmax lam - HcellR jmax lam' = ((lam' : ℝ) - (lam : ℝ)) • Adj jmax := by
  ext i j
  have hL : ∀ l : ℚ, HcellR jmax l i j
      = if i = j then ((i.val : ℝ) * ((i.val : ℝ) + 2)) / 4
        else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -(l : ℝ) else 0 := by
    intro l
    simp only [HcellR, Matrix.map_apply, Hcell, Matrix.of_apply]
    split_ifs <;> push_cast <;> ring
  rw [Matrix.sub_apply, hL, hL, Matrix.smul_apply, smul_eq_mul, Adj, Matrix.of_apply]
  split_ifs <;> ring

/-- The cell's quadratic form is Lipschitz in the coupling with constant `2`:
`|v ⬝ᵥ (HcellR jmax lam *ᵥ v) - v ⬝ᵥ (HcellR jmax lam' *ᵥ v)| ≤ 2 * |lam - lam'| * (v ⬝ᵥ v)`.
`HcellR_sub_smul_adj` pulls the coupling difference out as a scalar and `adj_form_bound` bounds what
is left. No eigenvalue is mentioned.

DERIVED: `2` is `adj_form_bound`'s constant, the two neighbours of a site. -/
theorem HcellR_form_lipschitz (jmax : ℕ) (lam lam' : ℚ) (v : Fin (dim jmax) → ℝ) :
    |v ⬝ᵥ (HcellR jmax lam *ᵥ v) - v ⬝ᵥ (HcellR jmax lam' *ᵥ v)|
      ≤ 2 * |(lam : ℝ) - (lam' : ℝ)| * (v ⬝ᵥ v) := by
  have hvv : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  -- the scalar pulls out of the form by hand: three lines of `Finset` algebra, inline rather than
  -- through a Mathlib name for `(c • A) *ᵥ v`.
  have hsm : ∀ (c : ℝ) (A : Matrix (Fin (dim jmax)) (Fin (dim jmax)) ℝ),
      v ⬝ᵥ ((c • A) *ᵥ v) = c * (v ⬝ᵥ (A *ᵥ v)) := by
    intro c A
    simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have hd : v ⬝ᵥ (HcellR jmax lam *ᵥ v) - v ⬝ᵥ (HcellR jmax lam' *ᵥ v)
      = ((lam' : ℝ) - (lam : ℝ)) * (v ⬝ᵥ (Adj jmax *ᵥ v)) := by
    rw [← dotProduct_sub, ← Matrix.sub_mulVec, HcellR_sub_smul_adj, hsm]
  rw [hd, abs_mul, abs_sub_comm ((lam' : ℝ))]
  have hb := adj_form_bound jmax v
  have ha : 0 ≤ |(lam : ℝ) - (lam' : ℝ)| := abs_nonneg _
  nlinarith [abs_nonneg (v ⬝ᵥ (Adj jmax *ᵥ v))]

/-- Transport of a GROUND-STATE form bound. If `v ⬝ᵥ (HcellR jmax lam' *ᵥ v) ≤ r * (v ⬝ᵥ v)` at
`lam'`, then at `lam` the same `v` gives `≤ (r + 2 * |lam - lam'|) * (v ⬝ᵥ v)`. The shape is what
`CellSpectrum.exists_eigenvalue_le_of_form` consumes, so a trial vector certified at `lam'` is still
one at `lam`, weakened by `2|Δλ|`.

DERIVED: `2` is `HcellR_form_lipschitz`'s constant, the form's Lipschitz constant in the
coupling. -/
theorem cell_form_le_of_form_le (jmax : ℕ) (lam lam' : ℚ) (v : Fin (dim jmax) → ℝ) (r : ℝ)
    (h : v ⬝ᵥ (HcellR jmax lam' *ᵥ v) ≤ r * (v ⬝ᵥ v)) :
    v ⬝ᵥ (HcellR jmax lam *ᵥ v) ≤ (r + 2 * |(lam : ℝ) - (lam' : ℝ)|) * (v ⬝ᵥ v) := by
  have hL := HcellR_form_lipschitz jmax lam lam' v
  have h1 : v ⬝ᵥ (HcellR jmax lam *ᵥ v) - v ⬝ᵥ (HcellR jmax lam' *ᵥ v)
      ≤ 2 * |(lam : ℝ) - (lam' : ℝ)| * (v ⬝ᵥ v) := (abs_le.mp hL).2
  nlinarith

/-- Transport of an INERTIA form bound. If `t * (v ⬝ᵥ v) ≤ v ⬝ᵥ (HcellR jmax lam' *ᵥ v)` at `lam'`,
then at `lam` the shift drops to `t - 2 * |lam - lam'|`. The shape is what
`CellSpectrum.atMostOne_eigenvalue_lt` consumes.

With `cell_form_le_of_form_le` this is where the certificate's Lipschitz constant of `4` comes from:
the upper eigenvalue drops by at most `2|Δλ|` and the lower one rises by at most `2|Δλ|`.

DERIVED: `2` is `HcellR_form_lipschitz`'s constant. The `4` named above is twice it and does not
appear in this statement. -/
theorem cell_form_ge_of_form_ge (jmax : ℕ) (lam lam' : ℚ) (v : Fin (dim jmax) → ℝ) (t : ℝ)
    (h : t * (v ⬝ᵥ v) ≤ v ⬝ᵥ (HcellR jmax lam' *ᵥ v)) :
    (t - 2 * |(lam : ℝ) - (lam' : ℝ)|) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (HcellR jmax lam *ᵥ v) := by
  have hL := HcellR_form_lipschitz jmax lam lam' v
  have h1 : -(2 * |(lam : ℝ) - (lam' : ℝ)| * (v ⬝ᵥ v))
      ≤ v ⬝ᵥ (HcellR jmax lam *ᵥ v) - v ⬝ᵥ (HcellR jmax lam' *ᵥ v) := (abs_le.mp hL).1
  nlinarith

/-- One certificate covers a BALL of rational couplings, relative route.
`CellPivot.HcellR_gap_of_certificate_rel` consumes a pivot certificate at `lam0` and concludes at
`lam0`; this consumes the same certificate and concludes at every `lam` within `r` of it, with the
certified gap reduced by `4 * r`. That is where the cover's radius `(gap - kappa_0)/4` comes from.

Both hypotheses move by the transports above:

* the trial vector's Rayleigh quotient rises by at most `2 * r` (`cell_form_le_of_form_le`), so the
  ground state is still at or below `t - μ + 2 * r`;
* the corank-one form bound falls by at most `2 * r` (`cell_form_ge_of_form_ge`), so there is still
  at most one eigenvalue below `t - 2 * r`.

No eigenvalue perturbation theorem is used: `CellSpectrum.atMostOne_eigenvalue_lt` and
`CellSpectrum.exists_eigenvalue_le_of_form` consume forms, and the form is what moved.
`CellSpectrum.form_ge_convex` extends a form bound across an interval from its endpoints with no
loss, but it needs one subspace `W` valid at both ends, and `ldlKer (Lbi e) m` here is built from the
certificate at `lam0`.

Stated for rational `lam0` and `lam`; `cellGapAtLeastR_of_ball` is the same statement with `lam`
real.

DERIVED: `4 * r` is the two eigenvalues' `2 * r` each, `2` being `HcellR_form_lipschitz`'s constant.
The `/ 4` and the `i.val + 2` in `hrecD` are the SU(2) Casimir `j(j+2)/4` on the cell diagonal, and
the `i.val + 1` in `hrecD` and `hrecO` is the nearest-neighbour band. `0 ≤ p k` away from the index
`m` is the LDL pivot sign condition, and `v ≠ 0` is what keeps the Rayleigh quotient defined. -/
theorem HcellR_gap_of_certificate_ball (jmax : ℕ) (lam0 lam : ℚ) (r t μ : ℝ)
    -- there is no `0 ≤ r` hypothesis: it follows from `hclose` and `abs_nonneg`, so carrying it
    -- would be a binder the proof never uses.
    (hμ : 4 * r < μ)
    (hclose : |(lam : ℝ) - (lam0 : ℝ)| ≤ r)
    (p e : Fin (dim jmax) → ℝ) (m : Fin (dim jmax))
    (hp : ∀ k, k ≠ m → 0 ≤ p k)
    (hrecD : ∀ i : Fin (dim jmax),
      (i.val * (i.val + 2) : ℝ) / 4 - t = p i + ∑ k, if k.val = i.val + 1 then e k * (p k * e k) else 0)
    (hrecO : ∀ i j : Fin (dim jmax), j.val = i.val + 1 → -(lam0 : ℝ) = e j * p j)
    (v : Fin (dim jmax) → ℝ) (hv : v ≠ 0)
    (hray : v ⬝ᵥ (HcellR jmax lam0 *ᵥ v) ≤ (t - μ) * (v ⬝ᵥ v)) :
    ∃ i₀, (HcellR_isHermitian jmax lam).eigenvalues i₀ ≤ t - μ + 2 * r ∧
      ∀ i, i ≠ i₀ → (HcellR_isHermitian jmax lam).eigenvalues i₀ + (μ - 4 * r)
        ≤ (HcellR_isHermitian jmax lam).eigenvalues i := by
  have hvv : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  -- the ground state, transported
  have hray' := cell_form_le_of_form_le jmax lam lam0 v (t - μ) hray
  have hray2 : v ⬝ᵥ (HcellR jmax lam *ᵥ v) ≤ (t - μ + 2 * r) * (v ⬝ᵥ v) := by
    refine hray'.trans ?_
    have : (t - μ) + 2 * |(lam : ℝ) - (lam0 : ℝ)| ≤ t - μ + 2 * r := by linarith
    exact mul_le_mul_of_nonneg_right this hvv
  obtain ⟨i₀, hi₀⟩ := exists_eigenvalue_le_of_form (HcellR_isHermitian jmax lam) hv hray2
  refine ⟨i₀, hi₀, fun i hi => ?_⟩
  -- the inertia bound, transported on the same kernel
  have hrec : HcellR jmax lam0 - t • 1 = (Lbi e)ᵀ * Matrix.diagonal p * (Lbi e) :=
    tridiag_ldl_of_recurrence (fun i => (i.val * (i.val + 2) : ℝ) / 4 - t) (fun _ => -(lam0 : ℝ)) p e _
      (fun i => HcellR_sub_diag jmax lam0 t i)
      (fun i j h => HcellR_sub_super jmax lam0 t i j h)
      (fun i j h => HcellR_sub_sub jmax lam0 t i j h)
      (fun i j hij h1 h2 => HcellR_sub_far jmax lam0 t i j hij h1 h2)
      hrecD hrecO
  have hform : ∀ x ∈ ldlKer (Lbi e) m, (t - 2 * r) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (HcellR jmax lam *ᵥ x) := by
    intro x hx
    rw [ldlKer_mem] at hx
    have h0 : t * (x ⬝ᵥ x) ≤ x ⬝ᵥ (HcellR jmax lam0 *ᵥ x) :=
      ldl_form_ge_on_kernel (HcellR jmax lam0) (Lbi e) p m t hp hrec x hx
    have hxx : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
    have ht := cell_form_ge_of_form_ge jmax lam lam0 x t h0
    refine le_trans ?_ ht
    have : t - 2 * r ≤ t - 2 * |(lam : ℝ) - (lam0 : ℝ)| := by linarith
    exact mul_le_mul_of_nonneg_right this hxx
  have hcard := atMostOne_eigenvalue_lt (HcellR_isHermitian jmax lam) (ldlKer (Lbi e) m)
    (ldlKer_corank (Lbi e) m) hform
  have hi0lt : (HcellR_isHermitian jmax lam).eigenvalues i₀ < t - 2 * r := by linarith
  by_contra h
  push Not at h
  have hilt : (HcellR_isHermitian jmax lam).eigenvalues i < t - 2 * r := by linarith
  set S := Finset.univ.filter
    (fun k => (HcellR_isHermitian jmax lam).eigenvalues k < t - 2 * r) with hS
  have hi0mem : i₀ ∈ S := by
    rw [hS]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi0lt
  have himem : i ∈ S := by
    rw [hS]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hilt
  have h2 : 1 < S.card := Finset.one_lt_card.mpr ⟨i, himem, i₀, hi0mem, hi⟩
  omega

/-- The ABSOLUTE route on a ball, losing `2 * r` rather than `4 * r`.

The relative ball above transports both of its bounds. This one transports only the inertia bound:
`CellSpectrum.cell_exists_eigenvalue_le_zero` gives an eigenvalue `≤ 0` at every coupling, because
the `j = 0` state has zero Casimir, so `H₀₀ = 0` and the matrix is never positive definite. The
conclusion is that eigenvalue together with a gap of `μ - 2 * r` above it, at every rational `lam`
within `r` of `lam0`.

There is no trial vector and no Sturm shift here: `hrecD` is stated at `μ` directly, so the
certificate is the LDL factorisation of `HcellR jmax lam0 - μ • 1` alone.

DERIVED: `2 * r` is the one transported bound, `2` being `HcellR_form_lipschitz`'s constant; the
relative route's `4` does not enter the conclusion. `0` is the ground eigenvalue bound and the pivot
sign condition `0 ≤ p k`. The `/ 4` and `i.val + 2` in `hrecD` are the SU(2) Casimir `j(j+2)/4` on
the diagonal, and `i.val + 1` is the nearest-neighbour band. -/
theorem HcellR_gap_of_certificate_ball_abs (jmax : ℕ) (lam0 lam : ℚ) (r μ : ℝ)
    (hμ : 2 * r < μ)
    (hclose : |(lam : ℝ) - (lam0 : ℝ)| ≤ r)
    (p e : Fin (dim jmax) → ℝ) (m : Fin (dim jmax))
    (hp : ∀ k, k ≠ m → 0 ≤ p k)
    (hrecD : ∀ i : Fin (dim jmax),
      (i.val * (i.val + 2) : ℝ) / 4 - μ = p i + ∑ k, if k.val = i.val + 1 then e k * (p k * e k) else 0)
    (hrecO : ∀ i j : Fin (dim jmax), j.val = i.val + 1 → -(lam0 : ℝ) = e j * p j) :
    ∃ i₀, (HcellR_isHermitian jmax lam).eigenvalues i₀ ≤ 0 ∧
      ∀ i, i ≠ i₀ → (HcellR_isHermitian jmax lam).eigenvalues i₀ + (μ - 2 * r)
        ≤ (HcellR_isHermitian jmax lam).eigenvalues i := by
  obtain ⟨i₀, hi₀⟩ := cell_exists_eigenvalue_le_zero jmax lam
  refine ⟨i₀, hi₀, fun i hi => ?_⟩
  have hrec : HcellR jmax lam0 - μ • 1 = (Lbi e)ᵀ * Matrix.diagonal p * (Lbi e) :=
    tridiag_ldl_of_recurrence (fun i => (i.val * (i.val + 2) : ℝ) / 4 - μ) (fun _ => -(lam0 : ℝ)) p e _
      (fun i => HcellR_sub_diag jmax lam0 μ i)
      (fun i j h => HcellR_sub_super jmax lam0 μ i j h)
      (fun i j h => HcellR_sub_sub jmax lam0 μ i j h)
      (fun i j hij h1 h2 => HcellR_sub_far jmax lam0 μ i j hij h1 h2)
      hrecD hrecO
  have hform : ∀ x ∈ ldlKer (Lbi e) m, (μ - 2 * r) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (HcellR jmax lam *ᵥ x) := by
    intro x hx
    rw [ldlKer_mem] at hx
    have h0 : μ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (HcellR jmax lam0 *ᵥ x) :=
      ldl_form_ge_on_kernel (HcellR jmax lam0) (Lbi e) p m μ hp hrec x hx
    have hxx : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
    have ht := cell_form_ge_of_form_ge jmax lam lam0 x μ h0
    refine le_trans ?_ ht
    have : μ - 2 * r ≤ μ - 2 * |(lam : ℝ) - (lam0 : ℝ)| := by linarith
    exact mul_le_mul_of_nonneg_right this hxx
  have hcard := atMostOne_eigenvalue_lt (HcellR_isHermitian jmax lam) (ldlKer (Lbi e) m)
    (ldlKer_corank (Lbi e) m) hform
  have hi0lt : (HcellR_isHermitian jmax lam).eigenvalues i₀ < μ - 2 * r := by linarith
  by_contra h
  push Not at h
  have hilt : (HcellR_isHermitian jmax lam).eigenvalues i < μ - 2 * r := by linarith
  set S := Finset.univ.filter
    (fun k => (HcellR_isHermitian jmax lam).eigenvalues k < μ - 2 * r) with hS
  have hi0mem : i₀ ∈ S := by
    rw [hS]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi0lt
  have himem : i ∈ S := by
    rw [hS]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hilt
  have h2 : 1 < S.card := Finset.one_lt_card.mpr ⟨i, himem, i₀, hi0mem, hi⟩
  omega

/-- The two cells in this development are the same matrix at a rational coupling.

`CellEnclosure.HcellR jmax (lam : ℚ)` casts the exact-rational `CellSpectrum.Hcell` into `ℝ`;
`CellSpectrum.HcellRr jmax (lam : ℝ)` is `diagonal(Casimir) − lam • adjM` over real `lam`. They are
built independently, and this identifies them entrywise.

It is what carries `CellPivot`'s point theorems and the ball reductions above — all stated at
rational coupling — to `HcellRr`, which `CellSpectrum.HcellRr_gap_strong_window` is stated about.
The physical coupling is real. -/
theorem HcellR_eq_HcellRr (jmax : ℕ) (lam : ℚ) :
    HcellR jmax lam = HcellRr jmax (lam : ℝ) := by
  ext i j
  simp only [HcellR, Matrix.map_apply, Hcell, HcellRr, Matrix.sub_apply, Matrix.diagonal_apply,
    Matrix.smul_apply, adjM, Matrix.of_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    have h1 : ¬ (i.val + 1 = i.val ∨ i.val + 1 = i.val) := by omega
    rw [if_pos rfl, if_pos rfl, if_neg h1]
    push_cast; ring
  · rw [if_neg hij, if_neg hij]
    by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · rw [if_pos hadj, if_pos hadj]; push_cast; ring
    · rw [if_neg hadj, if_neg hadj]; push_cast; ring

/-- The adjacency this file bounds is the one `CellSpectrum.HcellRr` is built from:
`Adj jmax = adjM (dim jmax)`. Stated so the bound below is visibly about the same matrix rather than
about a second definition of it. -/
theorem Adj_eq_adjM (jmax : ℕ) : Adj jmax = adjM (dim jmax) := by
  ext i j
  simp only [Adj, adjM, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij
    have h1 : ¬ (i.val + 1 = i.val ∨ i.val + 1 = i.val) := by omega
    rw [if_pos rfl, if_neg h1]
  · rw [if_neg hij]

/-! ### The same transport at real coupling

Everything above is stated for `HcellR jmax (lam : ℚ)`, which is what the exact-rational certificate
produces. `HcellRr` is the same cell over `ℝ` (`HcellR_eq_HcellRr`), built from the same adjacency
(`Adj_eq_adjM`), so the form bound — which comes from row and column sums and does not mention the
coupling's type — transports. The three lemmas below are the ones above with `ℚ` replaced by `ℝ`. -/

/-- The real-coupling cell's dependence on the coupling, as an equation:
`HcellRr jmax a - HcellRr jmax b = (b - a) • adjM (dim jmax)`. -/
theorem HcellRr_sub_smul_adjM (jmax : ℕ) (a b : ℝ) :
    HcellRr jmax a - HcellRr jmax b = (b - a) • adjM (dim jmax) := by
  simp only [HcellRr]
  match_scalars <;> ring

/-- `adj_form_bound` restated for `adjM (dim jmax)`, through `Adj_eq_adjM`:
`|v ⬝ᵥ (adjM (dim jmax) *ᵥ v)| ≤ 2 * (v ⬝ᵥ v)`.

DERIVED: `2` is `adj_form_bound`'s constant, the two neighbours of a site, carried across the
rewrite. -/
theorem adjM_form_bound (jmax : ℕ) (v : Fin (dim jmax) → ℝ) :
    |v ⬝ᵥ (adjM (dim jmax) *ᵥ v)| ≤ 2 * (v ⬝ᵥ v) := by
  rw [← Adj_eq_adjM]
  exact adj_form_bound jmax v

/-- The real-coupling cell's form is Lipschitz with the same constant:
`|v ⬝ᵥ (HcellRr jmax a *ᵥ v) - v ⬝ᵥ (HcellRr jmax b *ᵥ v)| ≤ 2 * |a - b| * (v ⬝ᵥ v)`, for real `a`
and `b`.

DERIVED: `2` is `adjM_form_bound`'s constant, which is `adj_form_bound`'s under `Adj_eq_adjM`. -/
theorem HcellRr_form_lipschitz (jmax : ℕ) (a b : ℝ) (v : Fin (dim jmax) → ℝ) :
    |v ⬝ᵥ (HcellRr jmax a *ᵥ v) - v ⬝ᵥ (HcellRr jmax b *ᵥ v)| ≤ 2 * |a - b| * (v ⬝ᵥ v) := by
  have hvv : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  have hsm : ∀ (c : ℝ) (A : Matrix (Fin (dim jmax)) (Fin (dim jmax)) ℝ),
      v ⬝ᵥ ((c • A) *ᵥ v) = c * (v ⬝ᵥ (A *ᵥ v)) := by
    intro c A
    simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have hd : v ⬝ᵥ (HcellRr jmax a *ᵥ v) - v ⬝ᵥ (HcellRr jmax b *ᵥ v)
      = (b - a) * (v ⬝ᵥ (adjM (dim jmax) *ᵥ v)) := by
    rw [← dotProduct_sub, ← Matrix.sub_mulVec, HcellRr_sub_smul_adjM, hsm]
  rw [hd, abs_mul, abs_sub_comm b]
  have hb := adjM_form_bound jmax v
  nlinarith [abs_nonneg (v ⬝ᵥ (adjM (dim jmax) *ᵥ v)), abs_nonneg (a - b)]

/-- Transport of a GROUND-state form bound at real coupling: `cell_form_le_of_form_le` with `ℝ` in
place of `ℚ`.

DERIVED: `2` is `HcellRr_form_lipschitz`'s constant. -/
theorem cellRr_form_le_of_form_le (jmax : ℕ) (a b : ℝ) (v : Fin (dim jmax) → ℝ) (r : ℝ)
    (h : v ⬝ᵥ (HcellRr jmax b *ᵥ v) ≤ r * (v ⬝ᵥ v)) :
    v ⬝ᵥ (HcellRr jmax a *ᵥ v) ≤ (r + 2 * |a - b|) * (v ⬝ᵥ v) := by
  have hL := HcellRr_form_lipschitz jmax a b v
  have h1 : v ⬝ᵥ (HcellRr jmax a *ᵥ v) - v ⬝ᵥ (HcellRr jmax b *ᵥ v)
      ≤ 2 * |a - b| * (v ⬝ᵥ v) := (abs_le.mp hL).2
  nlinarith

/-- Transport of an INERTIA form bound at real coupling: `cell_form_ge_of_form_ge` with `ℝ` in place
of `ℚ`.

DERIVED: `2` is `HcellRr_form_lipschitz`'s constant. -/
theorem cellRr_form_ge_of_form_ge (jmax : ℕ) (a b : ℝ) (v : Fin (dim jmax) → ℝ) (t : ℝ)
    (h : t * (v ⬝ᵥ v) ≤ v ⬝ᵥ (HcellRr jmax b *ᵥ v)) :
    (t - 2 * |a - b|) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (HcellRr jmax a *ᵥ v) := by
  have hL := HcellRr_form_lipschitz jmax a b v
  have h1 : -(2 * |a - b| * (v ⬝ᵥ v))
      ≤ v ⬝ᵥ (HcellRr jmax a *ᵥ v) - v ⬝ᵥ (HcellRr jmax b *ᵥ v) := (abs_le.mp hL).1
  nlinarith

/-! ### The cover at real coupling

The anchors stay RATIONAL — the certificate produces rational pivots — while the ball around each
one ranges over the REALS, which is the coupling the problem is about.

The LDL factorisation is established for `HcellR` at the rational anchor and carried across by
`HcellR_eq_HcellRr`; the form moves by `cellRr_form_le_of_form_le` and `cellRr_form_ge_of_form_ge`;
and the two spectral lemmas are generic in the matrix. -/

/-- The composable gap statement at real coupling: there is an index `i₀` such that every other
eigenvalue of `HcellRr_isHermitian jmax lam` is at least `g` above the one at `i₀`. -/
def CellGapAtLeastR (jmax : ℕ) (lam : ℝ) (g : ℝ) : Prop :=
  ∃ i₀, ∀ i, i ≠ i₀ →
    (HcellRr_isHermitian jmax lam).eigenvalues i₀ + g ≤ (HcellRr_isHermitian jmax lam).eigenvalues i

/-- A gap certified as `g` may be reported as any smaller `g'`, at the same index `i₀`. -/
theorem cellGapAtLeastR_mono {jmax : ℕ} {lam g g' : ℝ} (hg : g' ≤ g)
    (h : CellGapAtLeastR jmax lam g) : CellGapAtLeastR jmax lam g' := by
  obtain ⟨i₀, h⟩ := h
  exact ⟨i₀, fun i hi => by linarith [h i hi]⟩

/-- A rational certificate covers a ball of REAL couplings, relative route.

`lam0` is rational, `lam` is real, and `hclose` is `|lam - lam0| ≤ r`. The conclusion is
`CellGapAtLeastR jmax lam (μ - 4 * r)`. The LDL factorisation is proved for `HcellR` at the rational
anchor and carried to `HcellRr` by `HcellR_eq_HcellRr`; the form moves by
`cellRr_form_le_of_form_le` and `cellRr_form_ge_of_form_ge`.

DERIVED: `4 * r` is the two eigenvalues' `2 * r` each, `2` being `HcellRr_form_lipschitz`'s
constant. The `/ 4` and `i.val + 2` in `hrecD` are the SU(2) Casimir `j(j+2)/4` on the diagonal, and
`i.val + 1` is the nearest-neighbour band. `0 ≤ p k` away from `m` is the LDL pivot sign condition,
and `v ≠ 0` keeps the Rayleigh quotient defined. -/
theorem cellGapAtLeastR_of_ball (jmax : ℕ) (lam0 : ℚ) (lam : ℝ) (r t μ : ℝ)
    (hμ : 4 * r < μ) (hclose : |lam - (lam0 : ℝ)| ≤ r)
    (p e : Fin (dim jmax) → ℝ) (m : Fin (dim jmax))
    (hp : ∀ k, k ≠ m → 0 ≤ p k)
    (hrecD : ∀ i : Fin (dim jmax),
      (i.val * (i.val + 2) : ℝ) / 4 - t = p i + ∑ k, if k.val = i.val + 1 then e k * (p k * e k) else 0)
    (hrecO : ∀ i j : Fin (dim jmax), j.val = i.val + 1 → -(lam0 : ℝ) = e j * p j)
    (v : Fin (dim jmax) → ℝ) (hv : v ≠ 0)
    (hray : v ⬝ᵥ (HcellRr jmax (lam0 : ℝ) *ᵥ v) ≤ (t - μ) * (v ⬝ᵥ v)) :
    CellGapAtLeastR jmax lam (μ - 4 * r) := by
  have hvv : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  -- the ground state, transported to `lam`
  have hray' := cellRr_form_le_of_form_le jmax lam (lam0 : ℝ) v (t - μ) hray
  have hray2 : v ⬝ᵥ (HcellRr jmax lam *ᵥ v) ≤ (t - μ + 2 * r) * (v ⬝ᵥ v) := by
    refine hray'.trans ?_
    have : (t - μ) + 2 * |lam - (lam0 : ℝ)| ≤ t - μ + 2 * r := by linarith
    exact mul_le_mul_of_nonneg_right this hvv
  obtain ⟨i₀, hi₀⟩ := exists_eigenvalue_le_of_form (HcellRr_isHermitian jmax lam) hv hray2
  refine ⟨i₀, fun i hi => ?_⟩
  -- the LDL is proved for `HcellR` and carried across; the two are the same matrix
  have hrecQ : HcellR jmax lam0 - t • 1 = (Lbi e)ᵀ * Matrix.diagonal p * (Lbi e) :=
    tridiag_ldl_of_recurrence (fun i => (i.val * (i.val + 2) : ℝ) / 4 - t) (fun _ => -(lam0 : ℝ)) p e _
      (fun i => HcellR_sub_diag jmax lam0 t i)
      (fun i j h => HcellR_sub_super jmax lam0 t i j h)
      (fun i j h => HcellR_sub_sub jmax lam0 t i j h)
      (fun i j hij h1 h2 => HcellR_sub_far jmax lam0 t i j hij h1 h2)
      hrecD hrecO
  have hrec : HcellRr jmax (lam0 : ℝ) - t • 1 = (Lbi e)ᵀ * Matrix.diagonal p * (Lbi e) := by
    rw [← HcellR_eq_HcellRr]; exact hrecQ
  have hform : ∀ x ∈ ldlKer (Lbi e) m, (t - 2 * r) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (HcellRr jmax lam *ᵥ x) := by
    intro x hx
    rw [ldlKer_mem] at hx
    have h0 : t * (x ⬝ᵥ x) ≤ x ⬝ᵥ (HcellRr jmax (lam0 : ℝ) *ᵥ x) :=
      ldl_form_ge_on_kernel (HcellRr jmax (lam0 : ℝ)) (Lbi e) p m t hp hrec x hx
    have hxx : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
    have ht := cellRr_form_ge_of_form_ge jmax lam (lam0 : ℝ) x t h0
    refine le_trans ?_ ht
    have : t - 2 * r ≤ t - 2 * |lam - (lam0 : ℝ)| := by linarith
    exact mul_le_mul_of_nonneg_right this hxx
  have hcard := atMostOne_eigenvalue_lt (HcellRr_isHermitian jmax lam) (ldlKer (Lbi e) m)
    (ldlKer_corank (Lbi e) m) hform
  have hi0lt : (HcellRr_isHermitian jmax lam).eigenvalues i₀ < t - 2 * r := by linarith
  by_contra h
  push Not at h
  have hilt : (HcellRr_isHermitian jmax lam).eigenvalues i < t - 2 * r := by linarith
  set S := Finset.univ.filter
    (fun k => (HcellRr_isHermitian jmax lam).eigenvalues k < t - 2 * r) with hS
  have hi0mem : i₀ ∈ S := by
    rw [hS]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi0lt
  have himem : i ∈ S := by
    rw [hS]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hilt
  have h2 : 1 < S.card := Finset.one_lt_card.mpr ⟨i, himem, i₀, hi0mem, hi⟩
  omega

/-- The same at real coupling, ABSOLUTE route, losing `2 * r` instead of `4 * r`. The
ground-eigenvalue bound needs no transport: `CellSpectrum.HcellRr_zero_zero` gives `H₀₀ = 0` at
every real `λ`, and `exists_eigenvalue_le_zero_of_diag` reads a nonpositive eigenvalue off it. Only
the inertia bound moves. There is no trial vector and no Sturm shift; `hrecD` is stated at `μ`.

DERIVED: `2 * r` is the one transported bound, `2` being `HcellRr_form_lipschitz`'s constant; the
relative route's `4` does not enter. The `/ 4` and `i.val + 2` in `hrecD` are the SU(2) Casimir
`j(j+2)/4`, `i.val + 1` is the nearest-neighbour band, and `0 ≤ p k` away from `m` is the LDL pivot
sign condition. -/
theorem cellGapAtLeastR_of_ball_abs (jmax : ℕ) (lam0 : ℚ) (lam : ℝ) (r μ : ℝ)
    (hμ : 2 * r < μ) (hclose : |lam - (lam0 : ℝ)| ≤ r)
    (p e : Fin (dim jmax) → ℝ) (m : Fin (dim jmax))
    (hp : ∀ k, k ≠ m → 0 ≤ p k)
    (hrecD : ∀ i : Fin (dim jmax),
      (i.val * (i.val + 2) : ℝ) / 4 - μ = p i + ∑ k, if k.val = i.val + 1 then e k * (p k * e k) else 0)
    (hrecO : ∀ i j : Fin (dim jmax), j.val = i.val + 1 → -(lam0 : ℝ) = e j * p j) :
    CellGapAtLeastR jmax lam (μ - 2 * r) := by
  obtain ⟨i₀, hi₀⟩ := exists_eigenvalue_le_zero_of_diag (HcellRr_isHermitian jmax lam) 0
    (HcellRr_zero_zero jmax lam)
  refine ⟨i₀, fun i hi => ?_⟩
  have hrecQ : HcellR jmax lam0 - μ • 1 = (Lbi e)ᵀ * Matrix.diagonal p * (Lbi e) :=
    tridiag_ldl_of_recurrence (fun i => (i.val * (i.val + 2) : ℝ) / 4 - μ) (fun _ => -(lam0 : ℝ)) p e _
      (fun i => HcellR_sub_diag jmax lam0 μ i)
      (fun i j h => HcellR_sub_super jmax lam0 μ i j h)
      (fun i j h => HcellR_sub_sub jmax lam0 μ i j h)
      (fun i j hij h1 h2 => HcellR_sub_far jmax lam0 μ i j hij h1 h2)
      hrecD hrecO
  have hrec : HcellRr jmax (lam0 : ℝ) - μ • 1 = (Lbi e)ᵀ * Matrix.diagonal p * (Lbi e) := by
    rw [← HcellR_eq_HcellRr]; exact hrecQ
  have hform : ∀ x ∈ ldlKer (Lbi e) m, (μ - 2 * r) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (HcellRr jmax lam *ᵥ x) := by
    intro x hx
    rw [ldlKer_mem] at hx
    have h0 : μ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (HcellRr jmax (lam0 : ℝ) *ᵥ x) :=
      ldl_form_ge_on_kernel (HcellRr jmax (lam0 : ℝ)) (Lbi e) p m μ hp hrec x hx
    have hxx : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
    have ht := cellRr_form_ge_of_form_ge jmax lam (lam0 : ℝ) x μ h0
    refine le_trans ?_ ht
    have : μ - 2 * r ≤ μ - 2 * |lam - (lam0 : ℝ)| := by linarith
    exact mul_le_mul_of_nonneg_right this hxx
  have hcard := atMostOne_eigenvalue_lt (HcellRr_isHermitian jmax lam) (ldlKer (Lbi e) m)
    (ldlKer_corank (Lbi e) m) hform
  have hi0lt : (HcellRr_isHermitian jmax lam).eigenvalues i₀ < μ - 2 * r := by linarith
  by_contra h
  push Not at h
  have hilt : (HcellRr_isHermitian jmax lam).eigenvalues i < μ - 2 * r := by linarith
  set S := Finset.univ.filter
    (fun k => (HcellRr_isHermitian jmax lam).eigenvalues k < μ - 2 * r) with hS
  have hi0mem : i₀ ∈ S := by
    rw [hS]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi0lt
  have himem : i ∈ S := by
    rw [hS]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hilt
  have h2 : 1 < S.card := Finset.one_lt_card.mpr ⟨i, himem, i₀, hi0mem, hi⟩
  omega

/-- The statement the cover composes, at rational coupling: there is an index `i₀` such that every
other eigenvalue of `HcellR_isHermitian jmax lam` is at least `g` above the one at `i₀`.

The two routes certify different things on the way in — the absolute one bounds `E₁` outright, the
relative one bounds `E₁ − E₀` — and they bound `E₀` differently too. Neither difference appears
here, which is what lets a chain across an interval be built from anchors of both kinds. -/
def CellGapAtLeast (jmax : ℕ) (lam : ℚ) (g : ℝ) : Prop :=
  ∃ i₀, ∀ i, i ≠ i₀ →
    (HcellR_isHermitian jmax lam).eigenvalues i₀ + g ≤ (HcellR_isHermitian jmax lam).eigenvalues i

/-- A relative-route anchor covers its ball, in the composable form:
`HcellR_gap_of_certificate_ball` with the ground-eigenvalue clause dropped, leaving
`CellGapAtLeast jmax lam (μ - 4 * r)` at rational `lam`.

DERIVED: `4 * r` is the two eigenvalues' `2 * r` each, from `HcellR_form_lipschitz`'s constant `2`.
The `/ 4` and `i.val + 2` in `hrecD` are the SU(2) Casimir `j(j+2)/4`, `i.val + 1` is the
nearest-neighbour band, `0 ≤ p k` away from `m` is the LDL pivot sign condition, and `v ≠ 0` keeps
the Rayleigh quotient defined. -/
theorem cellGapAtLeast_of_ball (jmax : ℕ) (lam0 lam : ℚ) (r t μ : ℝ)
    (hμ : 4 * r < μ) (hclose : |(lam : ℝ) - (lam0 : ℝ)| ≤ r)
    (p e : Fin (dim jmax) → ℝ) (m : Fin (dim jmax))
    (hp : ∀ k, k ≠ m → 0 ≤ p k)
    (hrecD : ∀ i : Fin (dim jmax),
      (i.val * (i.val + 2) : ℝ) / 4 - t = p i + ∑ k, if k.val = i.val + 1 then e k * (p k * e k) else 0)
    (hrecO : ∀ i j : Fin (dim jmax), j.val = i.val + 1 → -(lam0 : ℝ) = e j * p j)
    (v : Fin (dim jmax) → ℝ) (hv : v ≠ 0)
    (hray : v ⬝ᵥ (HcellR jmax lam0 *ᵥ v) ≤ (t - μ) * (v ⬝ᵥ v)) :
    CellGapAtLeast jmax lam (μ - 4 * r) := by
  obtain ⟨i₀, _, h⟩ := HcellR_gap_of_certificate_ball jmax lam0 lam r t μ hμ hclose p e m hp
    hrecD hrecO v hv hray
  exact ⟨i₀, h⟩

/-- An absolute-route anchor covers its ball, in the composable form:
`HcellR_gap_of_certificate_ball_abs` with the `E₀ ≤ 0` clause dropped, leaving
`CellGapAtLeast jmax lam (μ - 2 * r)` at rational `lam`.

DERIVED: `2 * r` is the one transported bound, from `HcellR_form_lipschitz`'s constant `2`; the
relative route's `4` does not enter. The `/ 4` and `i.val + 2` in `hrecD` are the SU(2) Casimir
`j(j+2)/4`, `i.val + 1` is the nearest-neighbour band, and `0 ≤ p k` away from `m` is the LDL pivot
sign condition. -/
theorem cellGapAtLeast_of_ball_abs (jmax : ℕ) (lam0 lam : ℚ) (r μ : ℝ)
    (hμ : 2 * r < μ) (hclose : |(lam : ℝ) - (lam0 : ℝ)| ≤ r)
    (p e : Fin (dim jmax) → ℝ) (m : Fin (dim jmax))
    (hp : ∀ k, k ≠ m → 0 ≤ p k)
    (hrecD : ∀ i : Fin (dim jmax),
      (i.val * (i.val + 2) : ℝ) / 4 - μ = p i + ∑ k, if k.val = i.val + 1 then e k * (p k * e k) else 0)
    (hrecO : ∀ i j : Fin (dim jmax), j.val = i.val + 1 → -(lam0 : ℝ) = e j * p j) :
    CellGapAtLeast jmax lam (μ - 2 * r) := by
  obtain ⟨i₀, _, h⟩ := HcellR_gap_of_certificate_ball_abs jmax lam0 lam r μ hμ hclose p e m hp
    hrecD hrecO
  exact ⟨i₀, h⟩

/-- A certified gap may be reported as a smaller one, at the same index `i₀`. That is what lets
anchors with different certified gaps chain into one statement about an interval. -/
theorem cellGapAtLeast_mono {jmax : ℕ} {lam : ℚ} {g g' : ℝ} (hg : g' ≤ g)
    (h : CellGapAtLeast jmax lam g) : CellGapAtLeast jmax lam g' := by
  obtain ⟨i₀, h⟩ := h
  exact ⟨i₀, fun i hi => by linarith [h i hi]⟩

#print axioms CellGapAtLeastR
#print axioms cellGapAtLeastR_mono
#print axioms cellGapAtLeastR_of_ball
#print axioms cellGapAtLeastR_of_ball_abs
#print axioms HcellRr_sub_smul_adjM
#print axioms adjM_form_bound
#print axioms HcellRr_form_lipschitz
#print axioms cellRr_form_le_of_form_le
#print axioms cellRr_form_ge_of_form_ge
#print axioms HcellR_eq_HcellRr
#print axioms Adj_eq_adjM
#print axioms HcellR_gap_of_certificate_ball
#print axioms HcellR_gap_of_certificate_ball_abs
#print axioms cellGapAtLeast_of_ball
#print axioms cellGapAtLeast_of_ball_abs
#print axioms cellGapAtLeast_mono
#print axioms Adj_nonneg
#print axioms Adj_symm
#print axioms Adj_row_sum_le
#print axioms Adj_col_sum_le
#print axioms adj_form_bound
#print axioms HcellR_sub_smul_adj
#print axioms HcellR_form_lipschitz
#print axioms cell_form_le_of_form_le
#print axioms cell_form_ge_of_form_ge

end MassGap.CellEnclosure
