import Mathlib

/-!
# MassGap.KnabeEngine — Knabe's finite-size bound on a module with a non-negative form

The algebra of Knabe's argument, on any real module `E` with a symmetric non-negative bilinear form `B`.
Declarations are in the namespace `MassGap.KnabeCriterion`. Nothing here reads a lattice, a coupling or a
measure; `MassGap.KnabeWindow` places it against the slice transfer.

## What it gives (proved)

1. `knabe_bound`: for `B`-self-adjoint idempotents `hᵢ` and patch weights `c k i` (a patch `k` is
   `A_k = Σᵢ c k i • hᵢ`), with every `hᵢ` covered with total weight `a₁` and squared weight `a₂`, every pair
   `i ≠ j` either commuting with pair weight at most `b`, or with pair weight within `w i j` of `b`, and excess
   weights `w ≥ 0` of row and column sum at most `e`: a patch gap `γ · B(A_k x, x) ≤ B(A_k x, A_k x)` at every
   patch gives, for the whole sum `H = Σᵢ hᵢ`,

       (γ·a₁ − a₂ + b − e) · B(H x, x)  ≤  b · B(H x, H x).

   The bound reads the patch gap and the multiplicities, not the number of terms.
2. `knabe_commuting`: pairwise commuting projections with one-term patches give `B(Hx, x) ≤ B(Hx, Hx)`.
3. `selfAdj_id_sub`, `idem_id_sub`, `comm_id_sub`: complements of self-adjoint idempotents are self-adjoint
   idempotents, and complements of commuting maps commute.
4. `PatchSystem` packs the data and the hypotheses; `PatchSystem.globalGap_of_localGap` is `knabe_bound` on it,
   with `LocalGap γ` the patch gap and `GlobalGap c` the bound `c · B(Hx, x) ≤ B(Hx, Hx)`.

## Proved, argued, assumed

* Proved: every declaration, with standard axioms only.
* Argued: with `0/1` weights of `n − 1` consecutive terms on a ring (`a₁ = a₂ = n − 1`, `b = n − 2`, `e = 0`)
  the bound is Knabe's `(n−1)/(n−2)·(γ − 1/(n−1))` (S. Knabe, J. Stat. Phys. 52 (1988) 627–638); not
  instantiated here.
* Assumed: nothing.

## Frustration-freeness

`GlobalGap c` with `c > 0` says the spectrum of `H` lies in `{0} ∪ [c, ∞)`. It is a gap above a zero ground
energy only when the terms have a common null vector (the sum is frustration-free); for a frustrated sum it
bounds the lowest eigenvalue from below and is not a gap statement.

## Parameters

| argument | where | status |
|---|---|---|
| `E`, `B` | every statement | chosen: the module and its symmetric non-negative form |
| `ι`, `h` | the engine, `PatchSystem` | chosen: the terms, `B`-self-adjoint idempotents |
| `κ`, `c` | the engine, `PatchSystem` | chosen: the patches and their weights |
| `a₁`, `a₂`, `b`, `e`, `w` | `knabe_bound`, `PatchSystem` | the multiplicity data, fixed by the patch geometry |
| `γ` | `LocalGap`, `knabe_bound` | the patch gap |
| `c` (in `GlobalGap`) | `PatchSystem` | the gap of the whole sum |

DERIVED (module-wide): `0` the sign of the form and of the excess weights; `1` the indicator value; `2` the
halving in the pair bound.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.KnabeCriterion


/-! ## 1. Weights -/

section Weights

variable {ι κ : Type*} [Fintype κ]

/-- The pair weight `Σ_k c k i · c k j` of two terms: with `0/1` weights, the number of patches
containing both (`pairWeight_indicator`).

DERIVED: no numeral. -/
def pairWeight (c : κ → ι → ℝ) (i j : ι) : ℝ := ∑ k, c k i * c k j

/-- With the indicator weights of patches `S k`, the pair weight of `i` and `j` is the number of
patches containing both (`Finset.sum_boole`).

DERIVED: `1` and `0` are the indicator's values. -/
theorem pairWeight_indicator [DecidableEq ι] (S : κ → Finset ι) (i j : ι) :
    pairWeight (fun k l => if l ∈ S k then (1 : ℝ) else 0) i j
      = ((Finset.univ.filter (fun k => i ∈ S k ∧ j ∈ S k)).card : ℝ) := by
  rw [← Finset.sum_boole]
  unfold pairWeight
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hi : i ∈ S k <;> by_cases hj : j ∈ S k <;> simp [hi, hj]


end Weights

/-! ## 2. The finite-size engine -/

section Engine

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The whole sum `H = Σᵢ hᵢ`.

DERIVED: no numeral. -/
def totalOp (h : ι → E →ₗ[ℝ] E) : E →ₗ[ℝ] E := ∑ i, h i

/-- The patch operator `A_k = Σᵢ c k i • hᵢ`.

DERIVED: no numeral. -/
def patchOp (c : κ → ι → ℝ) (h : ι → E →ₗ[ℝ] E) (k : κ) : E →ₗ[ℝ] E := ∑ i, c k i • h i

/-- `H x = Σᵢ hᵢ x` (`LinearMap.sum_apply`).

DERIVED: no numeral. -/
theorem totalOp_apply (h : ι → E →ₗ[ℝ] E) (x : E) : totalOp h x = ∑ i, h i x := by
  simp only [totalOp, LinearMap.sum_apply]


/-- `A_k x = Σᵢ c k i • hᵢ x` (`LinearMap.sum_apply`, `LinearMap.smul_apply`).

DERIVED: no numeral. -/
theorem patchOp_apply (c : κ → ι → ℝ) (h : ι → E →ₗ[ℝ] E) (k : κ) (x : E) :
    patchOp c h k x = ∑ i, c k i • h i x := by
  simp only [patchOp, LinearMap.sum_apply, LinearMap.smul_apply]


/-- A bilinear form on two finite sums is the double sum of its values (`map_sum`,
`LinearMap.sum_apply`).

DERIVED: no numeral. -/
theorem form_sum_sum (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (u v : ι → E) :
    B (∑ i, u i) (∑ j, v j) = ∑ i, ∑ j, B (u i) (v j) := by
  have h1 : B (∑ i, u i) = ∑ i, B (u i) := map_sum B u Finset.univ
  rw [h1, LinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => map_sum (B (u i)) v Finset.univ)


/-- For a `B`-self-adjoint idempotent `p`: `B(p x, x) = B(p x, p x)`.

DERIVED: no numeral. -/
theorem form_proj_self (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : E →ₗ[ℝ] E)
    (hsa : ∀ x y, B (p x) y = B x (p y)) (hid : ∀ x, p (p x) = p x) (x : E) :
    B (p x) x = B (p x) (p x) := by
  rw [hsa x (p x), hid x]
  exact hsa x x


/-- **Two commuting projections pair non-negatively.** For `B`-self-adjoint idempotents `p`, `q`
that commute, and `B` non-negative: `0 ≤ B(p x, q x)`, since `B(p x, q x) = B(pq x, pq x)`.

DERIVED: `0` is the sign of the form. -/
theorem form_comm_nonneg (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hnn : ∀ x, 0 ≤ B x x) (p q : E →ₗ[ℝ] E)
    (hsp : ∀ x y, B (p x) y = B x (p y)) (hsq : ∀ x y, B (q x) y = B x (q y))
    (hip : ∀ x, p (p x) = p x) (hiq : ∀ x, q (q x) = q x)
    (hcomm : ∀ x, p (q x) = q (p x)) (x : E) :
    0 ≤ B (p x) (q x) := by
  have key : B (p (q x)) (p (q x)) = B (p x) (q x) := by
    rw [hsp (q x) (p (q x)), hip (q x), hcomm x, hsq x (q (p x)), hiq (p x), ← hcomm x,
      ← hsp x (q x)]
  rw [← key]
  exact hnn _


/-- **The pair bound.** For a symmetric non-negative `B`: `|B(u, v)| ≤ (B(u, u) + B(v, v))/2`, from
`B(u − v, u − v) ≥ 0` and `B(u + v, u + v) ≥ 0`.

DERIVED: `0` is the sign of the form; `2` is the halving of the arithmetic–geometric mean. -/
theorem abs_form_le (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (u v : E) :
    |B u v| ≤ (B u u + B v v) / 2 := by
  have h1 := hnn (u - v)
  have h2 := hnn (u + v)
  simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply] at h1 h2
  rw [hsymm v u] at h1 h2
  rw [abs_le]
  constructor <;> linarith


/-- **The finite-size bound (Knabe's argument, weighted, with excess).** On a module with a
symmetric non-negative bilinear form `B`, let `hᵢ` be `B`-self-adjoint idempotents and
`A_k = Σᵢ c k i • hᵢ`. Suppose every `i` has cover weight `Σ_k c k i = a₁` and squared weight
`pairWeight c i i = a₂`; every pair `i ≠ j` either commutes with `pairWeight c i j ≤ b`, or has
`|pairWeight c i j − b| ≤ w i j`; `w ≥ 0` with row and column sums at most `e`; and every patch has
the gap `γ · B(A_k x, x) ≤ B(A_k x, A_k x)`. Then, for `H = Σᵢ hᵢ` and every `x`,
`(γ·a₁ − a₂ + b − e) · B(Hx, x) ≤ b · B(Hx, Hx)`.

The proof sums the patch gaps: `Σ_k B(A_k x, x) = a₁ · B(Hx, x)` and
`Σ_k B(A_k x, A_k x) = Σ_{i,j} pairWeight c i j · B(hᵢx, hⱼx)`; each pair term is at most
`b · B(hᵢx, hⱼx)` plus `(a₂ − b) · B(hᵢx, hᵢx)` on the diagonal plus
`w i j · (B(hᵢx, hᵢx) + B(hⱼx, hⱼx))/2` (`form_comm_nonneg`, `abs_form_le`), and the three sums are
`b · B(Hx, Hx)`, `(a₂ − b) · B(Hx, x)` and at most `e · B(Hx, x)`.

DERIVED: `0` is the sign of the form and of the excess weights. -/
theorem knabe_bound (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (h : ι → E →ₗ[ℝ] E)
    (hsa : ∀ i x y, B (h i x) y = B x (h i y)) (hid : ∀ i x, h i (h i x) = h i x)
    (c : κ → ι → ℝ) (w : ι → ι → ℝ) {a₁ a₂ b e γ : ℝ}
    (hcov : ∀ i, ∑ k, c k i = a₁) (hcov2 : ∀ i, pairWeight c i i = a₂)
    (hpair : ∀ i j, i ≠ j →
      ((∀ x, h i (h j x) = h j (h i x)) ∧ pairWeight c i j ≤ b) ∨ |pairWeight c i j - b| ≤ w i j)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j ≤ e) (hcol : ∀ j, ∑ i, w i j ≤ e)
    (hloc : ∀ k x, γ * B (patchOp c h k x) x ≤ B (patchOp c h k x) (patchOp c h k x)) (x : E) :
    (γ * a₁ - a₂ + b - e) * B (totalOp h x) x ≤ b * B (totalOp h x) (totalOp h x) := by
  classical
  -- the whole sum
  have hD : B (totalOp h x) x = ∑ i, B (h i x) (h i x) := by
    rw [totalOp_apply, map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun i _ => form_proj_self B (h i) (hsa i) (hid i) x)
  have hHH : B (totalOp h x) (totalOp h x) = ∑ i, ∑ j, B (h i x) (h j x) := by
    rw [totalOp_apply]
    exact form_sum_sum B (fun i => h i x) (fun j => h j x)
  -- the patches
  have hA : ∀ k, B (patchOp c h k x) (patchOp c h k x)
      = ∑ i, ∑ j, c k i * c k j * B (h i x) (h j x) := by
    intro k
    rw [patchOp_apply, form_sum_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hAx : ∀ k, B (patchOp c h k x) x = ∑ i, c k i * B (h i x) (h i x) := by
    intro k
    rw [patchOp_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [form_proj_self B (h i) (hsa i) (hid i) x]
  have hsumA : ∑ k, B (patchOp c h k x) (patchOp c h k x)
      = ∑ i, ∑ j, pairWeight c i j * B (h i x) (h j x) := by
    simp only [hA]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [pairWeight, Finset.sum_mul]
  have hsumAx : ∑ k, B (patchOp c h k x) x = a₁ * ∑ i, B (h i x) (h i x) := by
    simp only [hAx]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_mul, hcov i]
  -- the patch gaps, summed
  have hlocsum : γ * (a₁ * ∑ i, B (h i x) (h i x))
      ≤ ∑ k, B (patchOp c h k x) (patchOp c h k x) := by
    rw [← hsumAx, Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => hloc k x)
  rw [hsumA] at hlocsum
  -- each pair term
  have hterm : ∀ i j, pairWeight c i j * B (h i x) (h j x)
      ≤ b * B (h i x) (h j x) + ((if i = j then (a₂ - b) * B (h i x) (h i x) else 0)
        + w i j * (B (h i x) (h i x) + B (h j x) (h j x)) / 2) := by
    intro i j
    have hii := hnn (h i x)
    have hjj := hnn (h j x)
    have hwP : 0 ≤ w i j * (B (h i x) (h i x) + B (h j x) (h j x)) / 2 :=
      div_nonneg (mul_nonneg (hw i j) (add_nonneg hii hjj)) zero_le_two
    rcases eq_or_ne i j with rfl | hij
    · rw [if_pos rfl, hcov2 _]
      linarith
    · rw [if_neg hij]
      rcases hpair i j hij with ⟨hcomm, hle⟩ | hex
      · have hP0 : 0 ≤ B (h i x) (h j x) :=
          form_comm_nonneg B hnn (h i) (h j) (hsa i) (hsa j) (hid i) (hid j) hcomm x
        have hm := mul_le_mul_of_nonneg_right hle hP0
        linarith
      · have habs : |B (h i x) (h j x)| ≤ (B (h i x) (h i x) + B (h j x) (h j x)) / 2 :=
          abs_form_le B hsymm hnn (h i x) (h j x)
        have h1 : (pairWeight c i j - b) * B (h i x) (h j x)
            ≤ w i j * ((B (h i x) (h i x) + B (h j x) (h j x)) / 2) := by
          calc (pairWeight c i j - b) * B (h i x) (h j x)
              ≤ |(pairWeight c i j - b) * B (h i x) (h j x)| := le_abs_self _
            _ = |pairWeight c i j - b| * |B (h i x) (h j x)| := abs_mul _ _
            _ ≤ w i j * ((B (h i x) (h i x) + B (h j x) (h j x)) / 2) :=
                mul_le_mul hex habs (abs_nonneg _) (hw i j)
        linarith
  -- the three sums
  have hdiag : ∑ i, ∑ j, (if i = j then (a₂ - b) * B (h i x) (h i x) else 0)
      = (a₂ - b) * ∑ i, B (h i x) (h i x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
  have hwsplit : ∑ i, ∑ j, w i j * (B (h i x) (h i x) + B (h j x) (h j x)) / 2
      = (∑ i, ∑ j, w i j * B (h i x) (h i x) + ∑ i, ∑ j, w i j * B (h j x) (h j x)) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hrowb : ∑ i, ∑ j, w i j * B (h i x) (h i x) ≤ e * ∑ i, B (h i x) (h i x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow i) (hnn (h i x))
  have hcolb : ∑ i, ∑ j, w i j * B (h j x) (h j x) ≤ e * ∑ j, B (h j x) (h j x) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hcol j) (hnn (h j x))
  have hsumT : ∑ i, ∑ j, pairWeight c i j * B (h i x) (h j x)
      ≤ b * ∑ i, ∑ j, B (h i x) (h j x) + ((a₂ - b) * ∑ i, B (h i x) (h i x)
        + (∑ i, ∑ j, w i j * B (h i x) (h i x) + ∑ i, ∑ j, w i j * B (h j x) (h j x)) / 2) := by
    calc ∑ i, ∑ j, pairWeight c i j * B (h i x) (h j x)
        ≤ ∑ i, ∑ j, (b * B (h i x) (h j x)
            + ((if i = j then (a₂ - b) * B (h i x) (h i x) else 0)
              + w i j * (B (h i x) (h i x) + B (h j x) (h j x)) / 2)) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
      _ = b * ∑ i, ∑ j, B (h i x) (h j x)
            + (∑ i, ∑ j, (if i = j then (a₂ - b) * B (h i x) (h i x) else 0)
              + ∑ i, ∑ j, w i j * (B (h i x) (h i x) + B (h j x) (h j x)) / 2) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ = _ := by rw [hdiag, hwsplit]
  rw [hD, hHH]
  linarith


/-- **Positive control: commuting projections.** If every two `hᵢ` commute, the one-term patches
(`κ = ι`, `c k i = 1` at `k = i` and `0` otherwise) have `a₁ = a₂ = 1`, pair weight `0` off the
diagonal and patch gap `1` (`form_proj_self`), and `knabe_bound` at `b = 1`, `e = 0` gives
`B(Hx, x) ≤ B(Hx, Hx)`: the gap bound `1` of a sum of commuting projections.

DERIVED: `0` is the sign of the form. CHOSEN: `b = 1` in the proof; every `b > 0` gives the same
constant `(1 − 1 + b)/b = 1`. -/
theorem knabe_commuting (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (h : ι → E →ₗ[ℝ] E)
    (hsa : ∀ i x y, B (h i x) y = B x (h i y)) (hid : ∀ i x, h i (h i x) = h i x)
    (hcomm : ∀ i j x, h i (h j x) = h j (h i x)) (x : E) :
    B (totalOp h x) x ≤ B (totalOp h x) (totalOp h x) := by
  classical
  have hprod : ∀ k i j : ι, (if k = i then (1 : ℝ) else 0) * (if k = j then 1 else 0)
      = if k = i ∧ k = j then 1 else 0 := by
    intro k i j
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp [hki, hkj]
  have hcov : ∀ i, ∑ k, (fun (k l : ι) => if k = l then (1 : ℝ) else 0) k i = 1 := by
    intro i
    show ∑ k, (if k = i then (1 : ℝ) else 0) = 1
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ i)]
  have hcov2 : ∀ i, pairWeight (fun (k l : ι) => if k = l then (1 : ℝ) else 0) i i = 1 := by
    intro i
    have hsq : ∀ k : ι, (if k = i then (1 : ℝ) else 0) * (if k = i then 1 else 0)
        = if k = i then 1 else 0 := by
      intro k
      split_ifs <;> norm_num
    show ∑ k, (if k = i then (1 : ℝ) else 0) * (if k = i then 1 else 0) = 1
    rw [Finset.sum_congr rfl (fun k _ => hsq k), Finset.sum_ite_eq', if_pos (Finset.mem_univ i)]
  have hpair : ∀ i j, i ≠ j →
      ((∀ y, h i (h j y) = h j (h i y))
        ∧ pairWeight (fun (k l : ι) => if k = l then (1 : ℝ) else 0) i j ≤ 1)
      ∨ |pairWeight (fun (k l : ι) => if k = l then (1 : ℝ) else 0) i j - 1|
          ≤ (fun _ _ => (0 : ℝ)) i j := by
    intro i j hij
    refine Or.inl ⟨hcomm i j, ?_⟩
    simp only [pairWeight, hprod]
    have hz : ∀ k ∈ (Finset.univ : Finset ι), (if k = i ∧ k = j then (1 : ℝ) else 0) = 0 :=
      fun k _ => if_neg (fun hk => hij (hk.1.symm.trans hk.2))
    rw [Finset.sum_eq_zero hz]
    norm_num
  have hAk : ∀ k y, patchOp (fun (k l : ι) => if k = l then (1 : ℝ) else 0) h k y = h k y := by
    intro k y
    rw [patchOp_apply, Finset.sum_eq_single k]
    · show (if k = k then (1 : ℝ) else 0) • h k y = h k y
      rw [if_pos rfl, one_smul]
    · intro i _ hik
      show (if k = i then (1 : ℝ) else 0) • h i y = 0
      rw [if_neg (fun hki => hik hki.symm), zero_smul]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  have hk := knabe_bound (κ := ι) B hsymm hnn h hsa hid
    (fun (k l : ι) => if k = l then (1 : ℝ) else 0) (fun _ _ => (0 : ℝ))
    (a₁ := 1) (a₂ := 1) (b := 1) (e := 0) (γ := 1)
    hcov hcov2 hpair (fun _ _ => le_rfl) (fun _ => by simp) (fun _ => by simp)
    (fun k y => by
      rw [hAk k y, one_mul]
      exact (form_proj_self B (h k) (hsa k) (hid k) y).le) x
  linarith


/-- `B(Hx, x) ≥ 0` for a sum of `B`-self-adjoint idempotents: each term is `B(hᵢx, hᵢx)`.

DERIVED: `0` is the sign of the form. -/
theorem totalOp_form_nonneg (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hnn : ∀ x, 0 ≤ B x x)
    (h : ι → E →ₗ[ℝ] E) (hsa : ∀ i x y, B (h i x) y = B x (h i y))
    (hid : ∀ i x, h i (h i x) = h i x) (x : E) :
    0 ≤ B (totalOp h x) x := by
  rw [totalOp_apply, map_sum, LinearMap.sum_apply]
  refine Finset.sum_nonneg (fun i _ => ?_)
  rw [form_proj_self B (h i) (hsa i) (hid i) x]
  exact hnn (h i x)


/-- The complement of a `B`-self-adjoint map is `B`-self-adjoint.

DERIVED: no numeral. -/
theorem selfAdj_id_sub (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (P : E →ₗ[ℝ] E)
    (hsa : ∀ x y, B (P x) y = B x (P y)) (x y : E) :
    B (((LinearMap.id : E →ₗ[ℝ] E) - P) x) y = B x (((LinearMap.id : E →ₗ[ℝ] E) - P) y) := by
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hsa]


/-- The complement of an idempotent is idempotent.

DERIVED: no numeral. -/
theorem idem_id_sub (P : E →ₗ[ℝ] E) (hid : ∀ x, P (P x) = P x) (x : E) :
    ((LinearMap.id : E →ₗ[ℝ] E) - P) (((LinearMap.id : E →ₗ[ℝ] E) - P) x) = ((LinearMap.id : E →ₗ[ℝ] E) - P) x := by
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hid, sub_self, sub_zero]


/-- Complements of commuting maps commute.

DERIVED: no numeral. -/
theorem comm_id_sub (P Q : E →ₗ[ℝ] E) (hcomm : ∀ x, P (Q x) = Q (P x)) (x : E) :
    ((LinearMap.id : E →ₗ[ℝ] E) - P) (((LinearMap.id : E →ₗ[ℝ] E) - Q) x) = ((LinearMap.id : E →ₗ[ℝ] E) - Q) (((LinearMap.id : E →ₗ[ℝ] E) - P) x) := by
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hcomm]
  abel


end Engine

/-! ## 3. The bundle -/

/-- **A patch system**: a module with a symmetric non-negative bilinear form, a finite family of
self-adjoint idempotents, patch weights and the multiplicity hypotheses of `knabe_bound`: cover
weight `a₁`, squared weight `a₂`, every pair `i ≠ j` commuting with pair weight at most `b` or within
`w i j` of `b`, and `w ≥ 0` with row and column sums at most `e`.

DERIVED: `0` is the sign of the form and of the excess weights. -/
structure PatchSystem where
  E : Type
  [acg : AddCommGroup E]
  [mod : Module ℝ E]
  ι : Type
  [fι : Fintype ι]
  κ : Type
  [fκ : Fintype κ]
  B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ
  symm : ∀ x y, B x y = B y x
  nonneg : ∀ x, 0 ≤ B x x
  h : ι → E →ₗ[ℝ] E
  selfAdj : ∀ i x y, B (h i x) y = B x (h i y)
  idem : ∀ i x, h i (h i x) = h i x
  c : κ → ι → ℝ
  w : ι → ι → ℝ
  a₁ : ℝ
  a₂ : ℝ
  b : ℝ
  e : ℝ
  cover : ∀ i, ∑ k, c k i = a₁
  cover2 : ∀ i, pairWeight c i i = a₂
  pair : ∀ i j, i ≠ j →
    ((∀ x, h i (h j x) = h j (h i x)) ∧ pairWeight c i j ≤ b) ∨ |pairWeight c i j - b| ≤ w i j
  w_nonneg : ∀ i j, 0 ≤ w i j
  row : ∀ i, ∑ j, w i j ≤ e
  col : ∀ j, ∑ i, w i j ≤ e

attribute [instance] PatchSystem.acg PatchSystem.mod PatchSystem.fι PatchSystem.fκ

namespace PatchSystem

/-- The whole sum `H = Σᵢ hᵢ` of a patch system.

DERIVED: no numeral. -/
def H (S : PatchSystem) : S.E →ₗ[ℝ] S.E := totalOp S.h

/-- The patch operator `A_k` of a patch system.

DERIVED: no numeral. -/
def A (S : PatchSystem) (k : S.κ) : S.E →ₗ[ℝ] S.E := patchOp S.c S.h k

/-- **The patch gap** `γ`: `γ · B(A_k x, x) ≤ B(A_k x, A_k x)` at every patch `k` and every `x`.

DERIVED: no numeral. -/
def LocalGap (S : PatchSystem) (γ : ℝ) : Prop :=
  ∀ k x, γ * S.B (S.A k x) x ≤ S.B (S.A k x) (S.A k x)

/-- **The gap of the whole sum** `c`: `c · B(Hx, x) ≤ B(Hx, Hx)` at every `x`.

DERIVED: no numeral. -/
def GlobalGap (S : PatchSystem) (c : ℝ) : Prop :=
  ∀ x, c * S.B (S.H x) x ≤ S.B (S.H x) (S.H x)

/-- The Knabe constant `(γ·a₁ − a₂ + b − e)/b` of a patch system at patch gap `γ`.

DERIVED: no numeral. -/
def knabeConst (S : PatchSystem) (γ : ℝ) : ℝ := (γ * S.a₁ - S.a₂ + S.b - S.e) / S.b

/-- **The patch gap gives the gap of the whole sum.** At `0 < b`, `LocalGap γ` gives
`GlobalGap (knabeConst γ)` (`knabe_bound`, divided by `b`).

DERIVED: `0` is the sign of `b`. -/
theorem globalGap_of_localGap (S : PatchSystem) {γ : ℝ} (hb : 0 < S.b) (hloc : S.LocalGap γ) :
    S.GlobalGap (S.knabeConst γ) := by
  intro x
  have hk := knabe_bound S.B S.symm S.nonneg S.h S.selfAdj S.idem S.c S.w S.cover S.cover2
    S.pair S.w_nonneg S.row S.col hloc x
  have hH : S.H x = totalOp S.h x := rfl
  rw [hH]
  unfold PatchSystem.knabeConst
  rw [div_mul_eq_mul_div, div_le_iff₀ hb]
  linarith


/-- `B(Hx, x) ≥ 0` in a patch system (`totalOp_form_nonneg`).

DERIVED: `0` is the sign of the form. -/
theorem H_form_nonneg (S : PatchSystem) (x : S.E) : 0 ≤ S.B (S.H x) x :=
  totalOp_form_nonneg S.B S.nonneg S.h S.selfAdj S.idem x


/-- `GlobalGap` is inherited downward: `c ≤ c'` and `GlobalGap c'` give `GlobalGap c`
(`H_form_nonneg`).

DERIVED: no numeral. -/
theorem globalGap_mono (S : PatchSystem) {c c' : ℝ} (hcc : c ≤ c') (hg : S.GlobalGap c') :
    S.GlobalGap c := by
  intro x
  have h1 := mul_le_mul_of_nonneg_right hcc (S.H_form_nonneg x)
  linarith [hg x]


end PatchSystem

end MassGap.KnabeCriterion

end

#print axioms MassGap.KnabeCriterion.pairWeight
#print axioms MassGap.KnabeCriterion.pairWeight_indicator
#print axioms MassGap.KnabeCriterion.totalOp
#print axioms MassGap.KnabeCriterion.patchOp
#print axioms MassGap.KnabeCriterion.totalOp_apply
#print axioms MassGap.KnabeCriterion.patchOp_apply
#print axioms MassGap.KnabeCriterion.form_sum_sum
#print axioms MassGap.KnabeCriterion.form_proj_self
#print axioms MassGap.KnabeCriterion.form_comm_nonneg
#print axioms MassGap.KnabeCriterion.abs_form_le
#print axioms MassGap.KnabeCriterion.knabe_bound
#print axioms MassGap.KnabeCriterion.knabe_commuting
#print axioms MassGap.KnabeCriterion.totalOp_form_nonneg
#print axioms MassGap.KnabeCriterion.selfAdj_id_sub
#print axioms MassGap.KnabeCriterion.idem_id_sub
#print axioms MassGap.KnabeCriterion.comm_id_sub
#print axioms MassGap.KnabeCriterion.PatchSystem.H
#print axioms MassGap.KnabeCriterion.PatchSystem.A
#print axioms MassGap.KnabeCriterion.PatchSystem.LocalGap
#print axioms MassGap.KnabeCriterion.PatchSystem.GlobalGap
#print axioms MassGap.KnabeCriterion.PatchSystem.knabeConst
#print axioms MassGap.KnabeCriterion.PatchSystem.globalGap_of_localGap
#print axioms MassGap.KnabeCriterion.PatchSystem.H_form_nonneg
#print axioms MassGap.KnabeCriterion.PatchSystem.globalGap_mono
