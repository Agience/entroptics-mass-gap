import MassGap.CellSpectrum

/-!
# MassGap.CellPerturb — the cell form is Lipschitz in the coupling, with NO Weyl inequality

## Why this file exists

The numeric certificate covers `λ ∈ [0.16, 6.76]` CONTINUOUSLY: each certified coupling carries a
Weyl neighbourhood of radius `(margin)/4`, and the neighbourhoods overlap. The Lean development,
until this file, carried only the 61 certified POINTS (`MassGap.CellPivot`), because lifting a grid
to an interval looks like it needs eigenvalue perturbation — and Mathlib has no Weyl inequality for
Hermitian matrices (it has Gershgorin, which is a different statement and not enough).

**It does not need one.** The two spectral facts the certificate is built from are already stated in
terms of QUADRATIC FORMS, not eigenvalue perturbation:

* `exists_eigenvalue_le_of_form` takes `ψ ⬝ᵥ (A *ᵥ ψ) ≤ r * (ψ ⬝ᵥ ψ)` and returns an eigenvalue `≤ r`;
* `atMostOne_eigenvalue_lt` takes `∀ x ∈ W, μ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)` on a codimension-≤1
  subspace and returns "at most one eigenvalue `< μ`".

So the perturbation never has to touch an eigenvalue. It only has to move the FORM, and the form moves
by an elementary amount, proved here from the definition of `Hcell` and AM–GM. Feeding the moved form
back into the same two lemmas reproduces the gap at the neighbouring coupling.

## The constant 4 is derived here, not chosen

`Hcell` depends on `λ` only through its nearest-neighbour off-diagonal, which is `-λ`. So

    HcellR jmax lam - HcellR jmax lam' = (lam' - lam) • Adj jmax

with `Adj` the 0/1 nearest-neighbour adjacency matrix (`HcellR_sub_smul_adj`), and the whole question
is how large `v ⬝ᵥ (Adj *ᵥ v)` can be. Every row and every column of `Adj` has at most two nonzero
entries, so AM–GM gives `|v ⬝ᵥ (Adj *ᵥ v)| ≤ 2 * (v ⬝ᵥ v)` (`adj_form_bound`) — and the form therefore
moves by at most `2|Δλ| (v ⬝ᵥ v)` (`HcellR_form_lipschitz`).

That `2` is where the certificate's `LIPSCHITZ = 4` comes from, and the factor of two between them is
not slack: the gap is a DIFFERENCE of two eigenvalues, the upper one moves down by at most `2|Δλ|`
and the lower one moves up by at most `2|Δλ|`, so the gap moves by at most `4|Δλ|`. The two halves
are `cell_form_ge_of_form_ge` and `cell_form_le_of_form_le` below, one per eigenvalue.
-/

namespace MassGap.CellEnclosure

open scoped Matrix
open Matrix

/-- The 0/1 nearest-neighbour adjacency matrix on the cell index set — the entire `λ`-dependence of
`Hcell`, with the coupling divided out.

DERIVED: the entries are not free. `Hcell` is `d i` on the diagonal, `-lam` where `|i-j| = 1`, and `0`
elsewhere, and `d i` does not contain `lam`. So `(Hcell lam - Hcell lam') / (lam' - lam)` is `0` on the
diagonal, `1` on the nearest-neighbour band and `0` off it — this matrix, and no other. That quotient
is the content of `HcellR_sub_smul_adj`, which is an EQUATION and therefore fails if either entry here
is wrong; a scaling error could not survive it. -/
noncomputable def Adj (jmax : ℕ) : Matrix (Fin (dim jmax)) (Fin (dim jmax)) ℝ :=
  Matrix.of fun i j =>
    if i = j then 0 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0

theorem Adj_nonneg (jmax : ℕ) (i j : Fin (dim jmax)) : 0 ≤ Adj jmax i j := by
  unfold Adj
  simp only [Matrix.of_apply]
  split_ifs <;> norm_num

theorem Adj_symm (jmax : ℕ) (i j : Fin (dim jmax)) : Adj jmax i j = Adj jmax j i := by
  unfold Adj
  simp only [Matrix.of_apply]
  rcases eq_or_ne i j with h | h
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]
    exact if_congr or_comm rfl rfl

/-- An indicator over `Fin N` whose predicate pins `j.val` to a single value sums to at most `1`. -/
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

/-- **Every row of `Adj` sums to at most `2`** — the index `i` has at most the two neighbours
`i-1` and `i+1`. This is the only structural fact the form bound needs. -/
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
        -- the predicates are given EXPLICITLY: `fun n => n + 1 = i.val` is not something
        -- higher-order unification recovers from the `ite` it appears in.
        refine add_le_add
          (sum_indicator_le_one (fun n => n = i.val + 1)
            (fun a b ha hb => Fin.val_injective (ha.trans hb.symm)))
          (sum_indicator_le_one (fun n => n + 1 = i.val)
            (fun a b ha hb => Fin.val_injective (by omega)))
    _ = 2 := by norm_num

theorem Adj_col_sum_le (jmax : ℕ) (j : Fin (dim jmax)) : ∑ i, Adj jmax i j ≤ 2 := by
  have : ∑ i, Adj jmax i j = ∑ i, Adj jmax j i :=
    Finset.sum_congr rfl (fun i _ => Adj_symm jmax i j)
  rw [this]
  exact Adj_row_sum_le jmax j

/-- **The adjacency form is bounded by twice the norm.** Pure AM–GM against the row and column
sums — no spectral input, so this holds at every `jmax` with no certificate behind it. -/
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

/-- **The coupling enters `Hcell` only through the adjacency.** -/
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

/-- **The cell's quadratic form is Lipschitz in the coupling, constant `2`.**

This is the whole content of the interval cover, and it is elementary: no eigenvalue is mentioned, so
Mathlib's missing Weyl inequality is not missing from this argument. -/
theorem HcellR_form_lipschitz (jmax : ℕ) (lam lam' : ℚ) (v : Fin (dim jmax) → ℝ) :
    |v ⬝ᵥ (HcellR jmax lam *ᵥ v) - v ⬝ᵥ (HcellR jmax lam' *ᵥ v)|
      ≤ 2 * |(lam : ℝ) - (lam' : ℝ)| * (v ⬝ᵥ v) := by
  have hvv : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  -- the scalar pulls out of the form by hand: the Mathlib spelling of `(c • A) *ᵥ v` has moved
  -- around, and this is three lines of `Finset` algebra rather than a name to guess.
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

/-- **Transport of the GROUND-STATE bound.** A trial vector certified at `lam'` certifies at `lam`,
weakened by `2|Δλ|`. Feeds `exists_eigenvalue_le_of_form` unchanged. -/
theorem cell_form_le_of_form_le (jmax : ℕ) (lam lam' : ℚ) (v : Fin (dim jmax) → ℝ) (r : ℝ)
    (h : v ⬝ᵥ (HcellR jmax lam' *ᵥ v) ≤ r * (v ⬝ᵥ v)) :
    v ⬝ᵥ (HcellR jmax lam *ᵥ v) ≤ (r + 2 * |(lam : ℝ) - (lam' : ℝ)|) * (v ⬝ᵥ v) := by
  have hL := HcellR_form_lipschitz jmax lam lam' v
  have h1 : v ⬝ᵥ (HcellR jmax lam *ᵥ v) - v ⬝ᵥ (HcellR jmax lam' *ᵥ v)
      ≤ 2 * |(lam : ℝ) - (lam' : ℝ)| * (v ⬝ᵥ v) := (abs_le.mp hL).2
  nlinarith

/-- **Transport of the INERTIA bound.** A form bound certified at `lam'` holds at `lam` with the
shift lowered by `2|Δλ|`. Feeds `atMostOne_eigenvalue_lt` unchanged.

Together with `cell_form_le_of_form_le` this is why the certificate's Lipschitz constant is `4`: the
upper eigenvalue drops by at most `2|Δλ|` and the lower one rises by at most `2|Δλ|`. -/
theorem cell_form_ge_of_form_ge (jmax : ℕ) (lam lam' : ℚ) (v : Fin (dim jmax) → ℝ) (t : ℝ)
    (h : t * (v ⬝ᵥ v) ≤ v ⬝ᵥ (HcellR jmax lam' *ᵥ v)) :
    (t - 2 * |(lam : ℝ) - (lam' : ℝ)|) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (HcellR jmax lam *ᵥ v) := by
  have hL := HcellR_form_lipschitz jmax lam lam' v
  have h1 : -(2 * |(lam : ℝ) - (lam' : ℝ)| * (v ⬝ᵥ v))
      ≤ v ⬝ᵥ (HcellR jmax lam *ᵥ v) - v ⬝ᵥ (HcellR jmax lam' *ᵥ v) := (abs_le.mp hL).1
  nlinarith

/-- **One certificate, a whole BALL of couplings.** The point reduction
`HcellR_gap_of_certificate_rel` consumes a pivot certificate at `lam0` and concludes at `lam0`. This
consumes the SAME certificate and concludes at every `lam` within `r`, with the certified gap reduced
by `4r` — which is where the cover's radius `(gap - kappa_0)/4` comes from.

Both hypotheses move by the transports above and nothing else happens:

* the trial vector's Rayleigh quotient rises by at most `2r` (`cell_form_le_of_form_le`), so the
  ground state is still at or below `t - mu + 2r`;
* the codimension-1 form bound falls by at most `2r` (`cell_form_ge_of_form_ge`), so there is still
  at most one eigenvalue below `t - 2r`.

The two `2r`s are the two eigenvalues, and their sum is the `4r`. No eigenvalue perturbation theorem
is used — `atMostOne_eigenvalue_lt` and `exists_eigenvalue_le_of_form` consume forms, and forms are
what moved.

NOTE on the alternative. `form_ge_convex` extends a form bound across an interval from its ENDPOINTS
with no loss at all, which is strictly better where it applies — `HcellR` is affine in `lam`, so a
convex combination of the endpoints IS the intermediate coupling. It does not apply here because it
needs one subspace `W` valid at both ends, and `ldlKer (Lbi e) m` is built from the certificate at
`lam0`; carrying that same kernel to the far endpoint costs exactly the `2r` this proof already pays.
So the two routes agree and this one needs only one certificate. -/
theorem HcellR_gap_of_certificate_ball (jmax : ℕ) (lam0 lam : ℚ) (r t μ : ℝ)
    -- NO `0 ≤ r` hypothesis: it follows from `hclose` and `abs_nonneg`, and carrying it would be a
    -- binder the proof never uses — which is how a statement drifts from what it looks like.
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
  -- the GROUND state, transported
  have hray' := cell_form_le_of_form_le jmax lam lam0 v (t - μ) hray
  have hray2 : v ⬝ᵥ (HcellR jmax lam *ᵥ v) ≤ (t - μ + 2 * r) * (v ⬝ᵥ v) := by
    refine hray'.trans ?_
    have : (t - μ) + 2 * |(lam : ℝ) - (lam0 : ℝ)| ≤ t - μ + 2 * r := by linarith
    exact mul_le_mul_of_nonneg_right this hvv
  obtain ⟨i₀, hi₀⟩ := exists_eigenvalue_le_of_form (HcellR_isHermitian jmax lam) hv hray2
  refine ⟨i₀, hi₀, fun i hi => ?_⟩
  -- the INERTIA bound, transported on the same kernel
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

/-- **The ABSOLUTE route on a ball, and it loses only `2r` rather than `4r`.**

The relative ball above pays `2r` per eigenvalue because BOTH of its bounds are transported. The
absolute route does not need to transport its ground-state bound at all: `E₀ ≤ 0` holds at EVERY
coupling by `cell_exists_eigenvalue_le_zero` — the `j = 0` state has zero Casimir, so `H₀₀ = 0` and
the matrix is never positive definite, for any `λ`. Only the inertia bound moves.

So the certified gap on the ball is `μ − 2r`, and the cover's radius for an absolute anchor could be
`(μ_max − κ₀)/2` rather than `(μ_max − κ₀)/4`. That is a factor of two more reach per anchor. The
certificate currently uses `/4` for both routes, which is sound and conservative; this theorem is what
would justify tightening it, and the tightening is not done here because the cover already closes. -/
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

/-- **The two cells in this development are the SAME cell.**

`CellEnclosure.HcellR jmax (lam : ℚ)` and `CellSpectrum.HcellRr jmax (lam : ℝ)` are both "the physical
SU(2) cell", built independently: the first by casting the exact-rational `Hcell` into `ℝ`, the second
as `diagonal(Casimir) − lam • adjM` over real `lam`. **Nothing connected them.** So the 61 point
theorems of `CellPivot`, the ball reductions above and the whole cover were statements about the cell
at RATIONAL coupling, while `HcellRr_gap_strong_window` — the exact convexity result that closes
`[0.16, 0.237]` over the reals with no Lipschitz loss — was about a different object as far as the
kernel was concerned.

The physical coupling is real, so this is not bookkeeping: without it the rational line does not reach
the statement the problem is about. The proof is the obvious one, and that it was never written is the
point. -/
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

/-- The adjacency this file bounds IS the one `HcellRr` is built from. Stated so the bound below is
visibly about the same matrix, rather than about a second definition of it. -/
theorem Adj_eq_adjM (jmax : ℕ) : Adj jmax = adjM (dim jmax) := by
  ext i j
  simp only [Adj, adjM, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij
    have h1 : ¬ (i.val + 1 = i.val ∨ i.val + 1 = i.val) := by omega
    rw [if_pos rfl, if_neg h1]
  · rw [if_neg hij]

/-! ### The same transport at REAL coupling

Everything above is stated for `HcellR jmax (lam : ℚ)`, because that is what the exact-rational
certificate produces. The physical coupling is real. `HcellRr` is the same cell over `ℝ`
(`HcellR_eq_HcellRr`) and is built from the same adjacency (`Adj_eq_adjM`), so the form bound —
which came from row and column sums and knows nothing about the coupling's type — transports
verbatim. Nothing here is new mathematics; it is the same three lemmas with `ℚ` replaced by `ℝ`. -/

theorem HcellRr_sub_smul_adjM (jmax : ℕ) (a b : ℝ) :
    HcellRr jmax a - HcellRr jmax b = (b - a) • adjM (dim jmax) := by
  simp only [HcellRr]
  match_scalars <;> ring

theorem adjM_form_bound (jmax : ℕ) (v : Fin (dim jmax) → ℝ) :
    |v ⬝ᵥ (adjM (dim jmax) *ᵥ v)| ≤ 2 * (v ⬝ᵥ v) := by
  rw [← Adj_eq_adjM]
  exact adj_form_bound jmax v

/-- **The real-coupling cell's form is Lipschitz, same constant.** -/
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

/-- Transport of the GROUND-state bound at real coupling. -/
theorem cellRr_form_le_of_form_le (jmax : ℕ) (a b : ℝ) (v : Fin (dim jmax) → ℝ) (r : ℝ)
    (h : v ⬝ᵥ (HcellRr jmax b *ᵥ v) ≤ r * (v ⬝ᵥ v)) :
    v ⬝ᵥ (HcellRr jmax a *ᵥ v) ≤ (r + 2 * |a - b|) * (v ⬝ᵥ v) := by
  have hL := HcellRr_form_lipschitz jmax a b v
  have h1 : v ⬝ᵥ (HcellRr jmax a *ᵥ v) - v ⬝ᵥ (HcellRr jmax b *ᵥ v)
      ≤ 2 * |a - b| * (v ⬝ᵥ v) := (abs_le.mp hL).2
  nlinarith

/-- Transport of the INERTIA bound at real coupling. -/
theorem cellRr_form_ge_of_form_ge (jmax : ℕ) (a b : ℝ) (v : Fin (dim jmax) → ℝ) (t : ℝ)
    (h : t * (v ⬝ᵥ v) ≤ v ⬝ᵥ (HcellRr jmax b *ᵥ v)) :
    (t - 2 * |a - b|) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (HcellRr jmax a *ᵥ v) := by
  have hL := HcellRr_form_lipschitz jmax a b v
  have h1 : -(2 * |a - b| * (v ⬝ᵥ v))
      ≤ v ⬝ᵥ (HcellRr jmax a *ᵥ v) - v ⬝ᵥ (HcellRr jmax b *ᵥ v) := (abs_le.mp hL).1
  nlinarith

/-! ### The cover at REAL coupling

The anchors stay RATIONAL — the certificate produces rational pivots and there is no reason to want
otherwise — but the ball around each one now ranges over the REALS. That is the statement the problem
is about: `λ` is a physical coupling, not a rational.

Everything needed is already proved. The LDL factorisation is established for `HcellR` at the
rational anchor and carried across by `HcellR_eq_HcellRr`; the form moves by `cellRr_form_*`; and the
two spectral lemmas are generic in the matrix. -/

/-- The composable gap statement at real coupling. -/
def CellGapAtLeastR (jmax : ℕ) (lam : ℝ) (g : ℝ) : Prop :=
  ∃ i₀, ∀ i, i ≠ i₀ →
    (HcellRr_isHermitian jmax lam).eigenvalues i₀ + g ≤ (HcellRr_isHermitian jmax lam).eigenvalues i

theorem cellGapAtLeastR_mono {jmax : ℕ} {lam g g' : ℝ} (hg : g' ≤ g)
    (h : CellGapAtLeastR jmax lam g) : CellGapAtLeastR jmax lam g' := by
  obtain ⟨i₀, h⟩ := h
  exact ⟨i₀, fun i hi => by linarith [h i hi]⟩

/-- **A rational certificate covers a ball of REAL couplings — relative route.** -/
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
  -- ground state, transported to `lam`
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

/-- **The same at real coupling, ABSOLUTE route** — losing `2r`, because `E₀ ≤ 0` needs no transport:
`HcellRr_zero_zero` gives `H₀₀ = 0` at EVERY real `λ`. -/
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

/-- **The statement the cover composes.** "The cell at `lam` has a spectral gap of at least `g`":
some index carries the ground energy and every other eigenvalue is at least `g` above it.

The two routes certify different things on the way in — the absolute one bounds `E₁` outright, the
relative one bounds `E₁ − E₀` — and they bound `E₀` differently too. Neither difference survives into
this, and it has to be that way: an interval is covered by anchors of BOTH kinds, so a chain across it
can only be built out of a statement both produce. -/
def CellGapAtLeast (jmax : ℕ) (lam : ℚ) (g : ℝ) : Prop :=
  ∃ i₀, ∀ i, i ≠ i₀ →
    (HcellR_isHermitian jmax lam).eigenvalues i₀ + g ≤ (HcellR_isHermitian jmax lam).eigenvalues i

/-- A relative-route anchor covers its ball, in the composable form. -/
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

/-- An absolute-route anchor covers its ball, in the composable form. -/
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

/-- **A certified gap may always be reported as a smaller one**, which is what lets anchors with
different certified gaps chain into one statement about the whole interval. -/
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
