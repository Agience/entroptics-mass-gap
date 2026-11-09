import Mathlib
import MassGap.KnabeCriterion
import MassGap.HeatBathGapDecay

noncomputable section

/-!
# MassGap.WeightedKnabe — the finite-size criterion with weighted patches and the unweighted box gap

`KnabeCriterion.knabe_bound` sums a gap of each weighted patch operator `A_k = Σᵢ c k i • hᵢ`. With
weights that vanish smoothly at the patch edge, the pair weights of neighbouring terms differ from
the largest pair weight only at second order, which is what brings the local-gap threshold from
order `1/n` to order `1/n²` (Gosset–Mozgunov; Lemm–Xiang for every dimension). A weighted patch has
a small gap of its own, because its edge weights are small. This module replaces the weighted patch
gap by the gap of the unweighted patch `F_k = Σᵢ s k i • hᵢ`, through an averaging over the patches
(Cauchy–Schwarz on the patch sums, in place of Lemm–Xiang's translation-eigenvector Lemma 3.2, so no
eigenvector and no translation symmetry is used).

## What it gives

1. `knabe_upper`: under the pair hypotheses of `knabe_bound`, for every `x`,
   `Σ_k B(A_k x, A_k x) ≤ b · B(Hx, Hx) + (a₂ − b + e) · B(Hx, x)`.
2. `patch_sum_lower`: if every patch has the ratio gap
   `γ · B(A_k x, x)² ≤ B(A_k x, A_k x) · B(F_k x, x)`, the weights are non-negative with cover
   weight `a₁`, and the unweighted weights have cover weight `N > 0`, then
   `γ · a₁² / N · B(Hx, x) ≤ Σ_k B(A_k x, A_k x)`.
3. `ratio_of_split`: the ratio gap follows from a gap of `F_k` on a complement of a common null
   part: if `x = y + z` with `A_k z = 0`, `F_k z = 0` and `γ · B(y, y) ≤ B(F_k y, y)`, then the ratio
   gap holds at `x`. This is the box gap `BoxFibreGap` in the form the averaging needs.
4. `weighted_gap`: the two composed,
   `(γ · a₁² / N − a₂ + b − e) · B(Hx, x) ≤ b · B(Hx, Hx)`: the whole sum has gap
   `(γ a₁²/N − a₂ + b − e)/b`, positive once `γ > (a₂ − b + e) · N / a₁²`.

## Scope

Everything here is the algebra on a module with a symmetric non-negative form; no Hilbert
completion, no spectral theorem. The threshold `(a₂ − b + e) N / a₁²` is a number fixed by the
weights and the interaction geometry. For the Wilson heat bath (single-link conditional
expectations, two links interacting when they share a plaquette) with product sine weights on the
box `[0, l]⁴` it reads `0.10` at `l = 10` and `0.038` at `l = 20` (`research/code/lab/
lx_threshold.py`, computed, not proved here); the weights are not instantiated in this module.
-/

namespace MassGap.WeightedKnabe

open MassGap.KnabeCriterion

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **The upper half of Knabe's argument, on its own.** Under the cover, squared-cover and pair
hypotheses of `KnabeCriterion.knabe_bound`, for every `x`:
`Σ_k B(A_k x, A_k x) ≤ b · B(Hx, Hx) + (a₂ − b + e) · B(Hx, x)`.

DERIVED: `0` is the sign of the form and of the excess weights; `2` is the halving of the pair
bound. -/
theorem knabe_upper (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (h : ι → E →ₗ[ℝ] E)
    (hsa : ∀ i x y, B (h i x) y = B x (h i y)) (hid : ∀ i x, h i (h i x) = h i x)
    (c : κ → ι → ℝ) (w : ι → ι → ℝ) {a₂ b e : ℝ}
    (hcov2 : ∀ i, pairWeight c i i = a₂)
    (hpair : ∀ i j, i ≠ j →
      ((∀ x, h i (h j x) = h j (h i x)) ∧ pairWeight c i j ≤ b) ∨ |pairWeight c i j - b| ≤ w i j)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j ≤ e) (hcol : ∀ j, ∑ i, w i j ≤ e) (x : E) :
    ∑ k, B (patchOp c h k x) (patchOp c h k x)
      ≤ b * B (totalOp h x) (totalOp h x) + (a₂ - b + e) * B (totalOp h x) x := by
  classical
  have hD : B (totalOp h x) x = ∑ i, B (h i x) (h i x) := by
    rw [totalOp_apply, map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun i _ => form_proj_self B (h i) (hsa i) (hid i) x)
  have hHH : B (totalOp h x) (totalOp h x) = ∑ i, ∑ j, B (h i x) (h j x) := by
    rw [totalOp_apply]
    exact form_sum_sum B (fun i => h i x) (fun j => h j x)
  have hA : ∀ k, B (patchOp c h k x) (patchOp c h k x)
      = ∑ i, ∑ j, c k i * c k j * B (h i x) (h j x) := by
    intro k
    rw [patchOp_apply, form_sum_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hsumA : ∑ k, B (patchOp c h k x) (patchOp c h k x)
      = ∑ i, ∑ j, pairWeight c i j * B (h i x) (h j x) := by
    simp only [hA]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [pairWeight, Finset.sum_mul]
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
  rw [hsumA, hD, hHH]
  linarith

#print axioms knabe_upper

/-- **A patch reading of a non-negative weighting is non-negative, and the patch readings sum to
the cover weight times the whole reading.** `B(A_k x, x) = Σᵢ c k i · B(hᵢx, hᵢx)`; with
`Σ_k c k i = a` for every `i`, `Σ_k B(A_k x, x) = a · B(Hx, x)`.

DERIVED: no numeral. -/
theorem patch_reading_sum (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (h : ι → E →ₗ[ℝ] E)
    (hsa : ∀ i x y, B (h i x) y = B x (h i y)) (hid : ∀ i x, h i (h i x) = h i x)
    (c : κ → ι → ℝ) {a : ℝ} (hcov : ∀ i, ∑ k, c k i = a) (x : E) :
    ∑ k, B (patchOp c h k x) x = a * B (totalOp h x) x := by
  have hAx : ∀ k, B (patchOp c h k x) x = ∑ i, c k i * B (h i x) (h i x) := by
    intro k
    rw [patchOp_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [form_proj_self B (h i) (hsa i) (hid i) x]
  have hD : B (totalOp h x) x = ∑ i, B (h i x) (h i x) := by
    rw [totalOp_apply, map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun i _ => form_proj_self B (h i) (hsa i) (hid i) x)
  simp only [hAx]
  rw [Finset.sum_comm, hD, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_mul, hcov i]

#print axioms patch_reading_sum

/-- `0 ≤ B(A_k x, x)` for non-negative weights.

DERIVED: `0` is the sign of the weights and of the form. -/
theorem patch_reading_nonneg (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hnn : ∀ x, 0 ≤ B x x)
    (h : ι → E →ₗ[ℝ] E)
    (hsa : ∀ i x y, B (h i x) y = B x (h i y)) (hid : ∀ i x, h i (h i x) = h i x)
    (c : κ → ι → ℝ) (hc : ∀ k i, 0 ≤ c k i) (k : κ) (x : E) :
    0 ≤ B (patchOp c h k x) x := by
  rw [patchOp_apply, map_sum, LinearMap.sum_apply]
  refine Finset.sum_nonneg (fun i _ => ?_)
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [form_proj_self B (h i) (hsa i) (hid i) x]
  exact mul_nonneg (hc k i) (hnn _)

#print axioms patch_reading_nonneg

/-- **The patch squares from the unweighted patch gaps, by averaging.** Non-negative weights `c`
with cover weight `a₁`, unweighted weights `s` with cover weight `N > 0` and non-negative, `0 ≤ γ`,
and at every patch the ratio gap `γ · B(A_k x, x)² ≤ B(A_k x, A_k x) · B(F_k x, x)`
(`A = patchOp c h`, `F = patchOp s h`). Then `γ · a₁² / N · B(Hx, x) ≤ Σ_k B(A_k x, A_k x)`.

The proof: `√γ · B(A_k x, x) ≤ √B(A_k x, A_k x) · √B(F_k x, x)`, summed and squared with
Cauchy–Schwarz on the sums, `γ (a₁ D)² ≤ (Σ_k B(A_k x, A_k x)) · N D` with `D = B(Hx, x)`.

DERIVED: `0` is the sign of the weights, of `γ` and of the form; `2` is the square of
Cauchy–Schwarz. -/
theorem patch_sum_lower (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hnn : ∀ x, 0 ≤ B x x)
    (h : ι → E →ₗ[ℝ] E)
    (hsa : ∀ i x y, B (h i x) y = B x (h i y)) (hid : ∀ i x, h i (h i x) = h i x)
    (c s : κ → ι → ℝ) (hc : ∀ k i, 0 ≤ c k i) (hs : ∀ k i, 0 ≤ s k i) {a₁ N γ : ℝ}
    (hcov : ∀ i, ∑ k, c k i = a₁) (hcovs : ∀ i, ∑ k, s k i = N) (hN : 0 < N) (hγ : 0 ≤ γ)
    (hratio : ∀ k x, γ * B (patchOp c h k x) x ^ 2
      ≤ B (patchOp c h k x) (patchOp c h k x) * B (patchOp s h k x) x) (x : E) :
    γ * a₁ ^ 2 / N * B (totalOp h x) x ≤ ∑ k, B (patchOp c h k x) (patchOp c h k x) := by
  set u : κ → ℝ := fun k => B (patchOp c h k x) x with hu
  set q : κ → ℝ := fun k => B (patchOp c h k x) (patchOp c h k x) with hq
  set v : κ → ℝ := fun k => B (patchOp s h k x) x with hv
  set D := B (totalOp h x) x with hDdef
  have hu0 : ∀ k, 0 ≤ u k := fun k => patch_reading_nonneg B hnn h hsa hid c hc k x
  have hv0 : ∀ k, 0 ≤ v k := fun k => patch_reading_nonneg B hnn h hsa hid s hs k x
  have hq0 : ∀ k, 0 ≤ q k := fun k => hnn _
  have hsumu : ∑ k, u k = a₁ * D := patch_reading_sum B h hsa hid c hcov x
  have hsumv : ∑ k, v k = N * D := patch_reading_sum B h hsa hid s hcovs x
  have hD0 : 0 ≤ D := by
    have hsv : 0 ≤ ∑ k, v k := Finset.sum_nonneg (fun k _ => hv0 k)
    rw [hsumv] at hsv
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_pos_of_neg hN hneg
    linarith
  -- per patch: √γ u ≤ √q √v
  have hper : ∀ k, Real.sqrt γ * u k ≤ Real.sqrt (q k) * Real.sqrt (v k) := by
    intro k
    rw [← Real.sqrt_mul (hq0 k)]
    have h1 : Real.sqrt γ * u k = Real.sqrt (γ * u k ^ 2) := by
      rw [Real.sqrt_mul hγ, Real.sqrt_sq (hu0 k)]
    rw [h1]
    exact Real.sqrt_le_sqrt (hratio k x)
  have hsum1 : Real.sqrt γ * ∑ k, u k ≤ ∑ k, Real.sqrt (q k) * Real.sqrt (v k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => hper k)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => Real.sqrt (q k))
    (fun k => Real.sqrt (v k))
  have hsq_q : ∑ k, Real.sqrt (q k) ^ 2 = ∑ k, q k :=
    Finset.sum_congr rfl (fun k _ => Real.sq_sqrt (hq0 k))
  have hsq_v : ∑ k, Real.sqrt (v k) ^ 2 = ∑ k, v k :=
    Finset.sum_congr rfl (fun k _ => Real.sq_sqrt (hv0 k))
  rw [hsq_q, hsq_v] at hcs
  have hlhs0 : 0 ≤ Real.sqrt γ * ∑ k, u k :=
    mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg (fun k _ => hu0 k))
  have hkey : γ * (∑ k, u k) ^ 2 ≤ (∑ k, q k) * ∑ k, v k := by
    have h2 : (Real.sqrt γ * ∑ k, u k) ^ 2 ≤ (∑ k, Real.sqrt (q k) * Real.sqrt (v k)) ^ 2 :=
      pow_le_pow_left₀ hlhs0 hsum1 2
    rw [mul_pow, Real.sq_sqrt hγ] at h2
    linarith
  rw [hsumu, hsumv] at hkey
  -- γ (a₁ D)² ≤ Q · N D  ⇒  γ a₁²/N · D ≤ Q
  set Q := ∑ k, q k with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun k _ => hq0 k)
  rcases eq_or_lt_of_le hD0 with hz | hpos
  · rw [← hz, mul_zero]; exact hQ0
  · have : γ * a₁ ^ 2 / N * D * (N * D) ≤ Q * (N * D) := by
      have he : γ * a₁ ^ 2 / N * D * (N * D) = γ * (a₁ * D) ^ 2 := by
        field_simp
      rw [he]; linarith
    exact le_of_mul_le_mul_right this (mul_pos hN hpos)

#print axioms patch_sum_lower

/-- **The ratio gap from a gap off a common null part.** If `x = y + z` with `A z = 0` and
`F z = 0` (the part of `x` neither patch operator sees), `B` symmetric, `A`, `F` self-adjoint for
`B`, and `γ · B(y, y) ≤ B(F y, y)`, then `γ · B(A x, x)² ≤ B(A x, A x) · B(F x, x)`. Cauchy–Schwarz
for the form (`HeatBathGapDecay.form_sq_le_mul`) gives `B(A y, y)² ≤ B(A y, A y) · B(y, y)`.

DERIVED: `0` is the null part and the sign of `γ`; `2` is the square of Cauchy–Schwarz. -/
theorem ratio_of_split (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (A F : E →ₗ[ℝ] E)
    (hsA : ∀ x y, B (A x) y = B x (A y)) (hsF : ∀ x y, B (F x) y = B x (F y))
    {γ : ℝ} (hγ : 0 ≤ γ) (x y z : E) (hxyz : x = y + z) (hAz : A z = 0) (hFz : F z = 0)
    (hgap : γ * B y y ≤ B (F y) y) :
    γ * B (A x) x ^ 2 ≤ B (A x) (A x) * B (F x) x := by
  have hAx : A x = A y := by rw [hxyz, map_add, hAz, add_zero]
  have hFx : F x = F y := by rw [hxyz, map_add, hFz, add_zero]
  have hAxx : B (A x) x = B (A y) y := by
    rw [hAx, hxyz, map_add, hsA y z, hAz, map_zero, add_zero]
  have hFxx : B (F x) x = B (F y) y := by
    rw [hFx, hxyz, map_add, hsF y z, hFz, map_zero, add_zero]
  rw [hAxx, hFxx, hAx]
  have hcs := MassGap.HeatBathGapDecay.form_sq_le_mul B hsymm hnn (A y) y
  have hAA := hnn (A y)
  calc γ * B (A y) y ^ 2 ≤ γ * (B (A y) (A y) * B y y) := mul_le_mul_of_nonneg_left hcs hγ
    _ = B (A y) (A y) * (γ * B y y) := by ring
    _ ≤ B (A y) (A y) * B (F y) y := mul_le_mul_of_nonneg_left hgap hAA

#print axioms ratio_of_split

/-- **The weighted finite-size criterion with the unweighted patch gap.** Under the pair
hypotheses of `knabe_bound` (pair weights of the weights `c`, excess `w` with row and column sums
`≤ e`), non-negative weights `c`, `s` with cover weights `a₁`, `N > 0`, `0 ≤ γ`, and the ratio gap
at every patch: `(γ · a₁² / N − a₂ + b − e) · B(Hx, x) ≤ b · B(Hx, Hx)`. The gap of the whole sum is
`(γ a₁²/N − a₂ + b − e)/b`, positive once `γ > (a₂ − b + e) · N / a₁²`, a threshold the weights fix.

DERIVED: `0` is the sign of the weights and of `γ`. -/
theorem weighted_gap (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (h : ι → E →ₗ[ℝ] E)
    (hsa : ∀ i x y, B (h i x) y = B x (h i y)) (hid : ∀ i x, h i (h i x) = h i x)
    (c s : κ → ι → ℝ) (w : ι → ι → ℝ) (hc : ∀ k i, 0 ≤ c k i) (hs : ∀ k i, 0 ≤ s k i)
    {a₁ a₂ b e N γ : ℝ}
    (hcov : ∀ i, ∑ k, c k i = a₁) (hcovs : ∀ i, ∑ k, s k i = N) (hN : 0 < N) (hγ : 0 ≤ γ)
    (hcov2 : ∀ i, pairWeight c i i = a₂)
    (hpair : ∀ i j, i ≠ j →
      ((∀ x, h i (h j x) = h j (h i x)) ∧ pairWeight c i j ≤ b) ∨ |pairWeight c i j - b| ≤ w i j)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j ≤ e) (hcol : ∀ j, ∑ i, w i j ≤ e)
    (hratio : ∀ k x, γ * B (patchOp c h k x) x ^ 2
      ≤ B (patchOp c h k x) (patchOp c h k x) * B (patchOp s h k x) x) (x : E) :
    (γ * a₁ ^ 2 / N - a₂ + b - e) * B (totalOp h x) x ≤ b * B (totalOp h x) (totalOp h x) := by
  have hlo := patch_sum_lower B hnn h hsa hid c s hc hs hcov hcovs hN hγ hratio x
  have hup := knabe_upper B hsymm hnn h hsa hid c w hcov2 hpair hw hrow hcol x
  linarith

#print axioms weighted_gap

end MassGap.WeightedKnabe
