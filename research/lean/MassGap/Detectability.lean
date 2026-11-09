import Mathlib
import MassGap.SweepFilter

noncomputable section

/-!
# MassGap.Detectability — the detectability lemma for a product of form-orthogonal projections

`SweepFilter.sweep_cov` needs a symmetrised sweep `S = R*R` with a gap in second-moment form. This module
proves that gap from the Poincaré gap of the projections, with no spectral theorem and no completion, on a
module with a symmetric positive semi-definite bilinear form `B`.

## Setting

`P i` (`i` in a finite type) `B`-self-adjoint idempotents; `Qᵢ = 1 − Pᵢ`. A relation `adj` such that
`Pᵢ` and `Pⱼ` commute whenever `j ≠ i` and not `adj i j`; at most `g` indices adjacent to each index, in
both arguments. `seqLin P l` applies the projections of the list `l` in order, head first.

## What it gives

1. `pyth`: `B(x, x) = B(Px, Px) + B(x − Px, x − Px)`; `tele_eq`: along a list,
   `B(u, u) = B(Ru, Ru) + Σₖ B(Qₖ φₖ₋₁, Qₖ φₖ₋₁)`, `φₖ` the partial products (telescoping).
2. `step_bound_mem`: for `i` in the list, `‖Qᵢ R u‖ ≤ Σ_{j adj i} cⱼ`, `cⱼ = ‖Qⱼ φ_{before j}‖`. The proof
   follows `aₜ = ‖Qᵢ φₜ‖` one projection at a time: `aₜ = 0` right after `Pᵢ`; a projection commuting with
   `Pᵢ` does not increase it (`Qᵢ Pⱼ = Pⱼ Qᵢ`, `Pⱼ` contracts); an adjacent one adds at most
   `‖Qⱼ φₜ₋₁‖` (`Qᵢ Pⱼ u = Qᵢ u − Qᵢ Qⱼ u`). No layer structure is used.
3. `detect`: for a list without repetition containing every index,
   `Σᵢ B(QᵢRu, QᵢRu) ≤ g² (B(u, u) − B(Ru, Ru))` (Cauchy–Schwarz over the at most `g` adjacent indices,
   then each `j` counted by at most `g` indices `i`).
4. `detect_gap`: with a vector `vac` fixed by every `Pᵢ` and the Poincaré gap
   `c B(v, v) ≤ Σᵢ B(Qᵢv, Qᵢv)` on the `B`-complement of `vac`: `(c + g²) B(Ru, Ru) ≤ g² B(u, u)` for `u ⊥ vac`.
   This is the detectability lemma (A. Anshu, I. Arad, T. Vidick, "Simple proof of the detectability lemma
   and spectral gap amplification", Phys. Rev. B 93, 205142 (2016)), in the form
   `‖Ru‖² ≤ ‖u‖²/(1 + c/g²)`.
5. `sweep_gap`: for `S = seqLin P (l ++ l.reverse) = R*R`, `B(Su, Su) ≤ (1 − δ) B(Su, u)` for `u ⊥ vac`,
   `δ = c/(g² + c)`: the hypothesis `hgap` of `SweepFilter.sweep_cov`. `seqLin_selfAdj`: `S` is
   `B`-self-adjoint; `seqLin_vac`: `S vac = vac`.

DERIVED (module-wide): `0` the empty product, the signs and the null value; `1` the identity in `1 − δ`;
`2` the squares.
-/

namespace MassGap.Detectability

open Finset

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {ι : Type*}

/-! ## 1. Products along a list -/

/-- **The product along a list**, head applied first: `seqLin P [i₁, …, iₘ] = P iₘ ∘ ⋯ ∘ P i₁`.

DERIVED: no numeral. -/
def seqLin (P : ι → E →ₗ[ℝ] E) : List ι → E →ₗ[ℝ] E
  | [] => LinearMap.id
  | i :: l => seqLin P l ∘ₗ P i

/-- DERIVED: no numeral. -/
@[simp] theorem seqLin_nil (P : ι → E →ₗ[ℝ] E) (x : E) : seqLin P [] x = x := rfl

/-- DERIVED: no numeral. -/
@[simp] theorem seqLin_cons (P : ι → E →ₗ[ℝ] E) (i : ι) (l : List ι) (x : E) :
    seqLin P (i :: l) x = seqLin P l (P i x) := rfl

/-- Concatenation applies the first list first.

DERIVED: no numeral. -/
theorem seqLin_append (P : ι → E →ₗ[ℝ] E) (l₁ l₂ : List ι) (x : E) :
    seqLin P (l₁ ++ l₂) x = seqLin P l₂ (seqLin P l₁ x) := by
  induction l₁ generalizing x with
  | nil => rfl
  | cons i l ih => exact ih (P i x)

#print axioms seqLin_append

/-- **The adjoint of a product is the reversed product.**

DERIVED: no numeral. -/
theorem seqLin_adj (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (P : ι → E →ₗ[ℝ] E)
    (hsa : ∀ i x y, B (P i x) y = B x (P i y)) (l : List ι) (x y : E) :
    B (seqLin P l x) y = B x (seqLin P l.reverse y) := by
  induction l generalizing x y with
  | nil => rfl
  | cons i l ih =>
    rw [seqLin_cons, ih, hsa, List.reverse_cons, seqLin_append, seqLin_cons, seqLin_nil]

#print axioms seqLin_adj

/-- A vector fixed by every projection is fixed by every product.

DERIVED: no numeral. -/
theorem seqLin_vac (P : ι → E →ₗ[ℝ] E) {vac : E} (hvac : ∀ i, P i vac = vac) (l : List ι) :
    seqLin P l vac = vac := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [seqLin_cons, hvac, ih]

#print axioms seqLin_vac

/-- **The symmetrised sweep is self-adjoint**: `seqLin P (l ++ l.reverse)` is its own adjoint.

DERIVED: no numeral. -/
theorem seqLin_selfAdj (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (P : ι → E →ₗ[ℝ] E)
    (hsa : ∀ i x y, B (P i x) y = B x (P i y)) (l : List ι) (x y : E) :
    B (seqLin P (l ++ l.reverse) x) y = B x (seqLin P (l ++ l.reverse) y) := by
  rw [seqLin_adj B P hsa, List.reverse_append, List.reverse_reverse]

#print axioms seqLin_selfAdj

/-! ## 2. One projection -/

section Proj

variable {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ}

/-- **The seminorm** `√B(x, x)`.

DERIVED: no numeral. -/
def nrm (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x : E) : ℝ := Real.sqrt (B x x)

/-- DERIVED: `0` the sign. -/
theorem nrm_nonneg (x : E) : 0 ≤ nrm B x := Real.sqrt_nonneg _

#print axioms nrm_nonneg

/-- DERIVED: `2` the square. -/
theorem nrm_sq (hpsd : ∀ x, 0 ≤ B x x) (x : E) : nrm B x ^ 2 = B x x := Real.sq_sqrt (hpsd x)

#print axioms nrm_sq

/-- DERIVED: `0` the null vector. -/
theorem nrm_zero : nrm B (0 : E) = 0 := by
  simp [nrm]

#print axioms nrm_zero

/-- **The triangle inequality for the seminorm**, in difference form.

DERIVED: `2` the cross term and the square. -/
theorem nrm_sub_le (hsymm : ∀ x y, B x y = B y x) (hpsd : ∀ x, 0 ≤ B x x) (x y : E) :
    nrm B (x - y) ≤ nrm B x + nrm B y := by
  unfold nrm
  have hx := hpsd x
  have hy := hpsd y
  have hcs := ChebyshevFilter.form_cs B hsymm hpsd x y
  have hsx := Real.sq_sqrt hx
  have hsy := Real.sq_sqrt hy
  have hab : |B x y| ≤ Real.sqrt (B x x) * Real.sqrt (B y y) := by
    rw [← Real.sqrt_mul hx]
    exact Real.abs_le_sqrt hcs
  have hexp : B (x - y) (x - y) = B x x - 2 * B x y + B y y := by
    simp only [map_sub, LinearMap.sub_apply]
    rw [hsymm y x]
    ring
  have hle : B (x - y) (x - y) ≤ (Real.sqrt (B x x) + Real.sqrt (B y y)) ^ 2 := by
    have e : (Real.sqrt (B x x) + Real.sqrt (B y y)) ^ 2
        = Real.sqrt (B x x) ^ 2 + 2 * (Real.sqrt (B x x) * Real.sqrt (B y y))
          + Real.sqrt (B y y) ^ 2 := by ring
    rw [hexp, e, hsx, hsy]
    linarith [neg_abs_le (B x y)]
  calc Real.sqrt (B (x - y) (x - y))
      ≤ Real.sqrt ((Real.sqrt (B x x) + Real.sqrt (B y y)) ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt (B x x) + Real.sqrt (B y y) :=
        Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

#print axioms nrm_sub_le

variable {Pr : E →ₗ[ℝ] E}

/-- **Pythagoras for a form-orthogonal projection**: `B(x, x) = B(Px, Px) + B(x − Px, x − Px)`.

DERIVED: no numeral. -/
theorem pyth (hsymm : ∀ x y, B x y = B y x) (hsa : ∀ x y, B (Pr x) y = B x (Pr y))
    (hid : ∀ x, Pr (Pr x) = Pr x) (x : E) :
    B x x = B (Pr x) (Pr x) + B (x - Pr x) (x - Pr x) := by
  have h1 : B (Pr x) (Pr x) = B x (Pr x) := by rw [hsa, hid]
  have h2 : B (Pr x) x = B x (Pr x) := hsymm _ _
  simp only [map_sub, LinearMap.sub_apply]
  linarith

#print axioms pyth

/-- The projection contracts the seminorm.

DERIVED: no numeral. -/
theorem nrm_proj_le (hsymm : ∀ x y, B x y = B y x) (hpsd : ∀ x, 0 ≤ B x x)
    (hsa : ∀ x y, B (Pr x) y = B x (Pr y)) (hid : ∀ x, Pr (Pr x) = Pr x) (x : E) :
    nrm B (Pr x) ≤ nrm B x := by
  unfold nrm
  apply Real.sqrt_le_sqrt
  have := pyth hsymm hsa hid x
  linarith [hpsd (x - Pr x)]

#print axioms nrm_proj_le

/-- The complementary projection contracts the seminorm.

DERIVED: no numeral. -/
theorem nrm_compl_le (hsymm : ∀ x y, B x y = B y x) (hpsd : ∀ x, 0 ≤ B x x)
    (hsa : ∀ x y, B (Pr x) y = B x (Pr y)) (hid : ∀ x, Pr (Pr x) = Pr x) (x : E) :
    nrm B (x - Pr x) ≤ nrm B x := by
  unfold nrm
  apply Real.sqrt_le_sqrt
  have := pyth hsymm hsa hid x
  linarith [hpsd (Pr x)]

#print axioms nrm_compl_le

end Proj

/-! ## 3. Telescoping and the step bound -/

section Steps

variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (P : ι → E →ₗ[ℝ] E)

/-- **The telescoping sum** `Σₖ B(Qₖ φₖ₋₁, Qₖ φₖ₋₁)` along a list.

DERIVED: `0` the empty sum. -/
def tele : List ι → E → ℝ
  | [], _ => 0
  | j :: l, u => B (u - P j u) (u - P j u) + tele l (P j u)

/-- **Telescoping**: `B(u, u) = B(Ru, Ru) + tele`.

DERIVED: no numeral. -/
theorem tele_eq (hsymm : ∀ x y, B x y = B y x) (hsa : ∀ i x y, B (P i x) y = B x (P i y))
    (hid : ∀ i x, P i (P i x) = P i x) (l : List ι) (u : E) :
    B u u = B (seqLin P l u) (seqLin P l u) + tele B P l u := by
  induction l generalizing u with
  | nil => simp [tele]
  | cons j l ih =>
    rw [seqLin_cons, tele, pyth hsymm (hsa j) (hid j) u, ih (P j u)]
    ring

#print axioms tele_eq

variable [DecidableEq ι]

/-- **The step norms** `‖Qⱼ φ_{before j}‖`, placed at `j`.

DERIVED: `0` the empty list's value. -/
def cvec : List ι → E → ι → ℝ
  | [], _ => 0
  | j :: l, u => Pi.single j (nrm B (u - P j u)) + cvec l (P j u)

/-- DERIVED: `0` the sign. -/
theorem cvec_nonneg (l : List ι) (u : E) (k : ι) : 0 ≤ cvec B P l u k := by
  induction l generalizing u with
  | nil => simp [cvec]
  | cons j l ih =>
    simp only [cvec, Pi.add_apply]
    refine add_nonneg ?_ (ih _)
    rw [Pi.single_apply]
    split_ifs
    · exact nrm_nonneg _
    · exact le_rfl

#print axioms cvec_nonneg

/-- An index not in the list carries no step.

DERIVED: `0` the value. -/
theorem cvec_not_mem (l : List ι) (u : E) {k : ι} (hk : k ∉ l) : cvec B P l u k = 0 := by
  induction l generalizing u with
  | nil => simp [cvec]
  | cons j l ih =>
    simp only [cvec, Pi.add_apply]
    have hkj : k ≠ j := fun h => hk (List.mem_cons.mpr (Or.inl h))
    have hkl : k ∉ l := fun h => hk (List.mem_cons.mpr (Or.inr h))
    rw [Pi.single_apply, if_neg hkj, ih _ hkl, add_zero]

#print axioms cvec_not_mem

/-- **The squared steps add up to the telescoping sum** along a list without repetition.

DERIVED: `2` the square. -/
theorem sum_cvec_sq [Fintype ι] (hpsd : ∀ x, 0 ≤ B x x) (l : List ι) (hnd : l.Nodup) (u : E) :
    ∑ k, cvec B P l u k ^ 2 = tele B P l u := by
  induction l generalizing u with
  | nil => simp [cvec, tele]
  | cons j l ih =>
    have hjl : j ∉ l := (List.nodup_cons.mp hnd).1
    have hnd' : l.Nodup := (List.nodup_cons.mp hnd).2
    simp only [cvec, tele, Pi.add_apply]
    have hsplit : ∀ k, ((Pi.single j (nrm B (u - P j u)) : ι → ℝ) k + cvec B P l (P j u) k) ^ 2
        = ((Pi.single j (nrm B (u - P j u)) : ι → ℝ) k) ^ 2 + cvec B P l (P j u) k ^ 2 := by
      intro k
      by_cases hk : k = j
      · rw [hk, cvec_not_mem B P l _ hjl]
        ring
      · rw [Pi.single_apply, if_neg hk]
        ring
    rw [Finset.sum_congr rfl (fun k _ => hsplit k), Finset.sum_add_distrib, ih hnd' (P j u)]
    congr 1
    rw [Finset.sum_eq_single j (fun k _ hk => by rw [Pi.single_apply, if_neg hk]; ring)
      (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, nrm_sq hpsd]

#print axioms sum_cvec_sq

variable (adj : ι → ι → Prop) [DecidableRel adj]

/-- **One projection moves `‖Qᵢ ·‖` by at most the adjacent step.**

DERIVED: `0` the non-adjacent increment. -/
theorem one_step (hsymm : ∀ x y, B x y = B y x) (hpsd : ∀ x, 0 ≤ B x x)
    (hsa : ∀ i x y, B (P i x) y = B x (P i y)) (hid : ∀ i x, P i (P i x) = P i x)
    (hcomm : ∀ i j, j ≠ i → ¬ adj i j → ∀ x, P i (P j x) = P j (P i x)) (i j : ι) (u : E) :
    nrm B (P j u - P i (P j u))
      ≤ nrm B (u - P i u) + (if adj i j then nrm B (u - P j u) else 0) := by
  have hn0 : 0 ≤ nrm B (u - P j u) := nrm_nonneg _
  by_cases hji : j = i
  · rw [hji, hid, sub_self, nrm_zero]
    split_ifs <;> linarith [nrm_nonneg (B := B) (u - P i u)]
  · by_cases ha : adj i j
    · rw [if_pos ha]
      have e : P j u - P i (P j u) = (u - P i u) - ((u - P j u) - P i (u - P j u)) := by
        rw [map_sub]; abel
      rw [e]
      calc nrm B ((u - P i u) - ((u - P j u) - P i (u - P j u)))
          ≤ nrm B (u - P i u) + nrm B ((u - P j u) - P i (u - P j u)) :=
            nrm_sub_le hsymm hpsd _ _
        _ ≤ nrm B (u - P i u) + nrm B (u - P j u) := by
            gcongr
            exact nrm_compl_le hsymm hpsd (hsa i) (hid i) _
    · rw [if_neg ha, add_zero]
      have e : P j u - P i (P j u) = P j (u - P i u) := by
        rw [hcomm i j hji ha, map_sub]
      rw [e]
      exact nrm_proj_le hsymm hpsd (hsa j) (hid j) _

#print axioms one_step

variable [Fintype ι]

/-- **The step bound along a list**: `‖Qᵢ R u‖ ≤ ‖Qᵢ u‖ + Σ_{j adj i} cⱼ`.

DERIVED: no numeral. -/
theorem step_bound (hsymm : ∀ x y, B x y = B y x) (hpsd : ∀ x, 0 ≤ B x x)
    (hsa : ∀ i x y, B (P i x) y = B x (P i y)) (hid : ∀ i x, P i (P i x) = P i x)
    (hcomm : ∀ i j, j ≠ i → ¬ adj i j → ∀ x, P i (P j x) = P j (P i x)) (i : ι) (l : List ι)
    (u : E) :
    nrm B (seqLin P l u - P i (seqLin P l u))
      ≤ nrm B (u - P i u) + ∑ j ∈ univ.filter (adj i), cvec B P l u j := by
  induction l generalizing u with
  | nil => simp [cvec]
  | cons j l ih =>
    rw [seqLin_cons]
    have h1 := ih (P j u)
    have h2 := one_step B P adj hsymm hpsd hsa hid hcomm i j u
    have hsum : ∑ k ∈ univ.filter (adj i), cvec B P (j :: l) u k
        = (if adj i j then nrm B (u - P j u) else 0)
          + ∑ k ∈ univ.filter (adj i), cvec B P l (P j u) k := by
      simp only [cvec, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single',
        Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hsum]
    linarith

#print axioms step_bound

/-- **The step bound for an index of the list**: `‖Qᵢ R u‖ ≤ Σ_{j adj i} cⱼ`.

DERIVED: `0` the value of `Qᵢ` right after `Pᵢ`. -/
theorem step_bound_mem (hsymm : ∀ x y, B x y = B y x) (hpsd : ∀ x, 0 ≤ B x x)
    (hsa : ∀ i x y, B (P i x) y = B x (P i y)) (hid : ∀ i x, P i (P i x) = P i x)
    (hcomm : ∀ i j, j ≠ i → ¬ adj i j → ∀ x, P i (P j x) = P j (P i x)) (i : ι) (l : List ι)
    (hi : i ∈ l) (u : E) :
    nrm B (seqLin P l u - P i (seqLin P l u)) ≤ ∑ j ∈ univ.filter (adj i), cvec B P l u j := by
  induction l generalizing u with
  | nil => simp at hi
  | cons j l ih =>
    rw [seqLin_cons]
    have hsum : ∑ k ∈ univ.filter (adj i), cvec B P (j :: l) u k
        = (if adj i j then nrm B (u - P j u) else 0)
          + ∑ k ∈ univ.filter (adj i), cvec B P l (P j u) k := by
      simp only [cvec, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single',
        Finset.mem_filter, Finset.mem_univ, true_and]
    have hif : 0 ≤ (if adj i j then nrm B (u - P j u) else 0) := by
      split_ifs
      · exact nrm_nonneg _
      · exact le_rfl
    rw [hsum]
    by_cases hji : j = i
    · rw [← hji] at hif ⊢
      have h := step_bound B P adj hsymm hpsd hsa hid hcomm j l (P j u)
      rw [hid, sub_self, nrm_zero, zero_add] at h
      linarith
    · have hil : i ∈ l := by
        rcases List.mem_cons.mp hi with h | h
        · exact absurd h.symm hji
        · exact h
      have h := ih hil (P j u)
      linarith

#print axioms step_bound_mem

/-! ## 4. The detectability lemma -/

/-- **The detectability lemma, local form.** For a list without repetition containing every index,
`Σᵢ B(QᵢRu, QᵢRu) ≤ g² (B(u, u) − B(Ru, Ru))`.

DERIVED: `2` the squares. -/
theorem detect (hsymm : ∀ x y, B x y = B y x) (hpsd : ∀ x, 0 ≤ B x x)
    (hsa : ∀ i x y, B (P i x) y = B x (P i y)) (hid : ∀ i x, P i (P i x) = P i x)
    (hcomm : ∀ i j, j ≠ i → ¬ adj i j → ∀ x, P i (P j x) = P j (P i x)) (g : ℕ)
    (hdeg : ∀ i, (univ.filter (adj i)).card ≤ g)
    (hdeg' : ∀ j, (univ.filter (fun i => adj i j)).card ≤ g)
    (l : List ι) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) (u : E) :
    ∑ i, B (seqLin P l u - P i (seqLin P l u)) (seqLin P l u - P i (seqLin P l u))
      ≤ (g : ℝ) ^ 2 * (B u u - B (seqLin P l u) (seqLin P l u)) := by
  have htel := tele_eq B P hsymm hsa hid l u
  have hsq := sum_cvec_sq B P hpsd l hnd u
  set c := cvec B P l u with hc
  have hc0 : ∀ k, 0 ≤ c k := cvec_nonneg B P l u
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  -- per index
  have hi : ∀ i, B (seqLin P l u - P i (seqLin P l u)) (seqLin P l u - P i (seqLin P l u))
      ≤ (g : ℝ) * ∑ j ∈ univ.filter (adj i), c j ^ 2 := by
    intro i
    have hb := step_bound_mem B P adj hsymm hpsd hsa hid hcomm i l (hall i) u
    rw [← nrm_sq hpsd]
    calc nrm B (seqLin P l u - P i (seqLin P l u)) ^ 2
        ≤ (∑ j ∈ univ.filter (adj i), c j) ^ 2 := pow_le_pow_left₀ (nrm_nonneg _) hb 2
      _ ≤ ((univ.filter (adj i)).card : ℝ) * ∑ j ∈ univ.filter (adj i), c j ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ (g : ℝ) * ∑ j ∈ univ.filter (adj i), c j ^ 2 :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg i)
            (Finset.sum_nonneg (fun j _ => sq_nonneg _))
  -- each step counted at most g times
  have hswap : ∑ i, ∑ j ∈ univ.filter (adj i), c j ^ 2
      = ∑ j, ((univ.filter (fun i => adj i j)).card : ℝ) * c j ^ 2 := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcount : ∑ j, ((univ.filter (fun i => adj i j)).card : ℝ) * c j ^ 2
      ≤ (g : ℝ) * ∑ j, c j ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    gcongr
    exact_mod_cast hdeg' j
  calc ∑ i, B (seqLin P l u - P i (seqLin P l u)) (seqLin P l u - P i (seqLin P l u))
      ≤ ∑ i, (g : ℝ) * ∑ j ∈ univ.filter (adj i), c j ^ 2 := Finset.sum_le_sum (fun i _ => hi i)
    _ = (g : ℝ) * ∑ j, ((univ.filter (fun i => adj i j)).card : ℝ) * c j ^ 2 := by
        rw [← Finset.mul_sum, hswap]
    _ ≤ (g : ℝ) * ((g : ℝ) * ∑ j, c j ^ 2) := by gcongr
    _ = (g : ℝ) ^ 2 * (B u u - B (seqLin P l u) (seqLin P l u)) := by
        rw [hsq, show tele B P l u = B u u - B (seqLin P l u) (seqLin P l u) by linarith [htel]]
        ring

#print axioms detect

/-- **The detectability lemma.** With `vac` fixed by every projection and the Poincaré gap
`c B(v, v) ≤ Σᵢ B(Qᵢv, Qᵢv)` on the complement of `vac`: `(c + g²) B(Ru, Ru) ≤ g² B(u, u)` for every
`u ⊥ vac`.

DERIVED: `2` the squares; `0` orthogonality. -/
theorem detect_gap (hsymm : ∀ x y, B x y = B y x) (hpsd : ∀ x, 0 ≤ B x x)
    (hsa : ∀ i x y, B (P i x) y = B x (P i y)) (hid : ∀ i x, P i (P i x) = P i x)
    (hcomm : ∀ i j, j ≠ i → ¬ adj i j → ∀ x, P i (P j x) = P j (P i x)) (g : ℕ)
    (hdeg : ∀ i, (univ.filter (adj i)).card ≤ g)
    (hdeg' : ∀ j, (univ.filter (fun i => adj i j)).card ≤ g)
    {vac : E} (hvac : ∀ i, P i vac = vac) {c : ℝ}
    (hpoin : ∀ v, B v vac = 0 → c * B v v ≤ ∑ i, B (v - P i v) (v - P i v))
    (l : List ι) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {u : E} (hu : B u vac = 0) :
    (c + (g : ℝ) ^ 2) * B (seqLin P l u) (seqLin P l u) ≤ (g : ℝ) ^ 2 * B u u := by
  have hRu : B (seqLin P l u) vac = 0 := by
    rw [seqLin_adj B P hsa, seqLin_vac P hvac]
    exact hu
  have h1 := hpoin _ hRu
  have h2 := detect B P adj hsymm hpsd hsa hid hcomm g hdeg hdeg' l hnd hall u
  linarith

#print axioms detect_gap

/-- **The symmetrised sweep has the second-moment gap** of `SweepFilter.sweep_cov`: for
`S = seqLin P (l ++ l.reverse)` and `u ⊥ vac`, `B(Su, Su) ≤ (1 − δ) B(Su, u)`, `δ = c/(g² + c)`.

DERIVED: `1` the whole; `2` the squares; `0` orthogonality and the sign of `g² + c`. -/
theorem sweep_gap (hsymm : ∀ x y, B x y = B y x) (hpsd : ∀ x, 0 ≤ B x x)
    (hsa : ∀ i x y, B (P i x) y = B x (P i y)) (hid : ∀ i x, P i (P i x) = P i x)
    (hcomm : ∀ i j, j ≠ i → ¬ adj i j → ∀ x, P i (P j x) = P j (P i x)) (g : ℕ)
    (hdeg : ∀ i, (univ.filter (adj i)).card ≤ g)
    (hdeg' : ∀ j, (univ.filter (fun i => adj i j)).card ≤ g)
    {vac : E} (hvac : ∀ i, P i vac = vac) {c : ℝ}
    (hpoin : ∀ v, B v vac = 0 → c * B v v ≤ ∑ i, B (v - P i v) (v - P i v))
    (hpos : 0 < (g : ℝ) ^ 2 + c)
    (l : List ι) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) (u : E) (hu : B u vac = 0) :
    B (seqLin P (l ++ l.reverse) u) (seqLin P (l ++ l.reverse) u)
      ≤ (1 - c / ((g : ℝ) ^ 2 + c)) * B (seqLin P (l ++ l.reverse) u) u := by
  have hSu : B (seqLin P (l ++ l.reverse) u) u = B (seqLin P l u) (seqLin P l u) := by
    rw [seqLin_append, seqLin_adj B P hsa, List.reverse_reverse]
  have hRu : B (seqLin P l u) vac = 0 := by
    rw [seqLin_adj B P hsa, seqLin_vac P hvac]
    exact hu
  have hdl := detect_gap B P adj hsymm hpsd hsa hid hcomm g hdeg hdeg' hvac hpoin l.reverse
    (List.nodup_reverse.mpr hnd) (fun i => List.mem_reverse.mpr (hall i)) hRu
  rw [hSu, seqLin_append]
  have e : 1 - c / ((g : ℝ) ^ 2 + c) = (g : ℝ) ^ 2 / ((g : ℝ) ^ 2 + c) := by
    rw [one_sub_div hpos.ne', add_sub_cancel_right]
  rw [e, div_mul_eq_mul_div, le_div_iff₀ hpos]
  linarith

#print axioms sweep_gap

end Steps

end MassGap.Detectability
