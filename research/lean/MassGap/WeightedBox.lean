import Mathlib
import MassGap.WeightedBridge
import MassGap.HeatBathLocal
import MassGap.ClayRoutes
import MassGap.BoxGap
import MassGap.RestoreShimsClay

noncomputable section

/-!
# MassGap.WeightedBox — the weighted finite-size criterion at the tree's box, to the Clay statement

`WeightedBridge.weighted_gap_of_patch_gap` turns the unweighted patch gap (the tree's
`BoxPatch.BoxLocalGap`, supplied by `BoxGap.BoxFibreGap`) into a gap of the whole heat-bath sum, once
weights `c` with the pair multiplicities `a₁, a₂, b, e` are given. This module supplies the two
remaining operator bounds, packs the weights for the Wilson heat bath, and carries the result to the
IR gap and to `ClayRoutes.ClayContinuum`.

## What it gives

1. `patch_form_le_cover`: `B(F x, F x) ≤ (Σᵢ s k i) · B(F x, x)` for `F = patchOp s h k`, `s ≥ 0`
   (Cauchy–Schwarz on the patch sum).
2. `patch_dom`: `0 ≤ c ≤ cm · s` gives `B(A x, A x) ≤ (Σᵢ c k i) · cm · B(F x, x)`.
3. `WeightedFamilyAt hN β n j a₁ a₂ b e`: weights on the links of the torus of extent `2(j + 1)`, one
   patch per site, non-negative and at most `cm` times the box indicator `BoxPatch.boxWeight n`, with
   cover `a₁`, squared cover `a₂`, and every pair of distinct links either sharing no plaquette with
   pair weight `≤ b`, or within `w` of `b`, `w ≥ 0` with row and column sums `≤ e`.
   `WeightedFamilyAt.toHB` is its `KnabeCriterion.WilsonHeatBath` (the conditional expectations
   `torusCondExp`).
4. `globalGap_weighted`: `BoxPatch.BoxLocalGap hN β n γ`, `0 < γ`, `0 < b`, `1 ≤ n ≤ j + 1`:
   `GlobalGap ((γ a₁²/n⁴ − a₂ + b − e)/b)` at the heat-bath system.
5. `weightedConst`, `weightedRate`, `irGapAt_weightedBox`: the IR gap at the explicit rate
   `−log(clusterRate 21 c₀)/aRun N β₀`, `c₀ = weightedConst`, from the box and a weight family at
   every large `j` with fixed `a₁, a₂, b, e` and `γ > (a₂ − b + e) n⁴/a₁²`.
6. `clay_continuum_of_weightedBox`: `ClayContinuum` from `BoxGap.BoxFibreGap` at that threshold, the
   weights, the UV step below the rate, and E, N, Y, exactly as `RestoreShimsClay.clay_continuum_of_boxPatchGap`
   with the box at the weighted threshold in place of `(40n − 36)/n²`.

## What it does not give

The weights are a hypothesis: a `WeightedFamilyAt` at every large `j` with fixed `a₁, a₂, b, e`. The
product sine weights at the link midpoints, supported on the links with both ends in the box, give
`(a₂ − b + e) n⁴/a₁² = t_lx(n − 1) · n/(n − 1)` with `t_lx` the threshold computed in
`research/code/lab/lx_threshold.py` (`0.31` at `n = 4`, `0.12` at `n = 8`, `0.050` at `n = 15`);
their pair arithmetic on the torus is not proved here.
-/

namespace MassGap.WeightedBox

open MassGap MassGap.HeatBath MassGap.KnabeCriterion MassGap.HeatBathGapDecay MassGap.HeatBathLocal
open MassGap.PeriodicState (torusObs)
open Filter

/-! ## 1. Two operator bounds on patch operators -/

section Bounds

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Cauchy–Schwarz on a non-negative patch sum.** For `s ≥ 0`:
`B(Σᵢ sᵢ hᵢ x, Σᵢ sᵢ hᵢ x) ≤ (Σᵢ sᵢ) · Σᵢ sᵢ B(hᵢ x, hᵢ x)`.

DERIVED: `0` is the sign of the weights and of the form; `2` is the halving of the pair bound. -/
theorem weighted_cs (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i) (v : ι → E) :
    B (∑ i, s i • v i) (∑ i, s i • v i) ≤ (∑ i, s i) * ∑ i, s i * B (v i) (v i) := by
  rw [form_sum_sum]
  have hterm : ∀ i j, B (s i • v i) (s j • v j)
      ≤ s i * s j * ((B (v i) (v i) + B (v j) (v j)) / 2) := by
    intro i j
    have e : B (s i • v i) (s j • v j) = s i * s j * B (v i) (v j) := by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    have h1 := abs_form_le B hsymm hnn (v i) (v j)
    have h2 : B (v i) (v j) ≤ (B (v i) (v i) + B (v j) (v j)) / 2 := (le_abs_self _).trans h1
    have h3 : 0 ≤ s i * s j := mul_nonneg (hs i) (hs j)
    rw [e]
    exact mul_le_mul_of_nonneg_left h2 h3
  have hsum : ∑ i, ∑ j, s i * s j * ((B (v i) (v i) + B (v j) (v j)) / 2)
      = (∑ i, s i) * ∑ i, s i * B (v i) (v i) := by
    have e1 : ∑ i, ∑ j, s i * s j * ((B (v i) (v i) + B (v j) (v j)) / 2)
        = ((∑ i, s i * B (v i) (v i)) * (∑ j, s j) + (∑ i, s i) * (∑ j, s j * B (v j) (v j))) / 2 := by
      rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [e1]
    ring
  calc ∑ i, ∑ j, B (s i • v i) (s j • v j)
      ≤ ∑ i, ∑ j, s i * s j * ((B (v i) (v i) + B (v j) (v j)) / 2) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = _ := hsum

#print axioms weighted_cs

/-- `B(patchOp s h k x, x) = Σᵢ s k i · B(hᵢ x, hᵢ x)`.

DERIVED: no numeral. -/
theorem patch_reading_eq (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (h : ι → E →ₗ[ℝ] E)
    (hsa : ∀ i x y, B (h i x) y = B x (h i y)) (hid : ∀ i x, h i (h i x) = h i x)
    (s : κ → ι → ℝ) (k : κ) (x : E) :
    B (patchOp s h k x) x = ∑ i, s k i * B (h i x) (h i x) := by
  rw [patchOp_apply, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [form_proj_self B (h i) (hsa i) (hid i) x]

#print axioms patch_reading_eq

/-- **The patch operator is bounded by its total weight.** For `s ≥ 0`:
`B(F x, F x) ≤ (Σᵢ s k i) · B(F x, x)`, `F = patchOp s h k`.

DERIVED: `0` is the sign of the weights. -/
theorem patch_form_le_cover (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (h : ι → E →ₗ[ℝ] E)
    (hsa : ∀ i x y, B (h i x) y = B x (h i y)) (hid : ∀ i x, h i (h i x) = h i x)
    (s : κ → ι → ℝ) (hs : ∀ k i, 0 ≤ s k i) (k : κ) (x : E) :
    B (patchOp s h k x) (patchOp s h k x) ≤ (∑ i, s k i) * B (patchOp s h k x) x := by
  rw [patch_reading_eq B h hsa hid s k x, patchOp_apply]
  exact weighted_cs B hsymm hnn (s k) (hs k) (fun i => h i x)

#print axioms patch_form_le_cover

/-- **A dominated weighting.** For `0 ≤ c k i ≤ cm · s k i`:
`B(A x, A x) ≤ (Σᵢ c k i) · cm · B(F x, x)`, `A = patchOp c h k`, `F = patchOp s h k`.

DERIVED: `0` is the sign of the weights and of the form. -/
theorem patch_dom (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (h : ι → E →ₗ[ℝ] E)
    (hsa : ∀ i x y, B (h i x) y = B x (h i y)) (hid : ∀ i x, h i (h i x) = h i x)
    (c s : κ → ι → ℝ) (hc : ∀ k i, 0 ≤ c k i) {cm : ℝ} (hle : ∀ k i, c k i ≤ cm * s k i)
    (k : κ) (x : E) :
    B (patchOp c h k x) (patchOp c h k x) ≤ (∑ i, c k i) * cm * B (patchOp s h k x) x := by
  have h1 := patch_form_le_cover B hsymm hnn h hsa hid c hc k x
  rw [patch_reading_eq B h hsa hid c k x] at h1
  rw [patch_reading_eq B h hsa hid s k x]
  have hC : 0 ≤ ∑ i, c k i := Finset.sum_nonneg (fun i _ => hc k i)
  have h2 : ∑ i, c k i * B (h i x) (h i x) ≤ cm * ∑ i, s k i * B (h i x) (h i x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have := mul_le_mul_of_nonneg_right (hle k i) (hnn (h i x))
    linarith
  calc B (patchOp c h k x) (patchOp c h k x) ≤ (∑ i, c k i) * ∑ i, c k i * B (h i x) (h i x) := h1
    _ ≤ (∑ i, c k i) * (cm * ∑ i, s k i * B (h i x) (h i x)) := mul_le_mul_of_nonneg_left h2 hC
    _ = (∑ i, c k i) * cm * ∑ i, s k i * B (h i x) (h i x) := by ring

#print axioms patch_dom

end Bounds

/-! ## 2. Weights for the Wilson heat bath -/

section Wilson

variable {N : ℕ}

/-- **A weight family at one torus.** Weights on the links of the torus of extent `2(j + 1)`, one patch
per site, non-negative and at most `cm` times the box indicator of side `n`, with cover `a₁`, squared
cover `a₂`, and every pair of distinct links either sharing no plaquette with pair weight `≤ b`, or
within `w` of `b`, `w ≥ 0` with row and column sums `≤ e`.

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `0` is the sign of the weights and of the excess. -/
structure WeightedFamilyAt (hN : N ≠ 0) (β : ℝ) (n j : ℕ) (a₁ a₂ b e : ℝ) where
  c : WilsonHypercubic.Site 4 (2 * j + 1 + 1) → WilsonHypercubic.Link 4 (2 * j + 1 + 1) → ℝ
  w : WilsonHypercubic.Link 4 (2 * j + 1 + 1) → WilsonHypercubic.Link 4 (2 * j + 1 + 1) → ℝ
  cm : ℝ
  cm_nonneg : 0 ≤ cm
  c_nonneg : ∀ k l, 0 ≤ c k l
  c_le : ∀ k l, c k l ≤ cm * BoxPatch.boxWeight n k l
  cover : ∀ l, ∑ k, c k l = a₁
  cover2 : ∀ l, pairWeight c l l = a₂
  pair : ∀ l l', l ≠ l' →
    (¬ SharePlaq (bdT (2 * j + 1)) l l' ∧ pairWeight c l l' ≤ b) ∨ |pairWeight c l l' - b| ≤ w l l'
  w_nonneg : ∀ l l', 0 ≤ w l l'
  row : ∀ l, ∑ l', w l l' ≤ e
  col : ∀ l', ∑ l, w l l' ≤ e

/-- **The heat-bath system of a weight family**: the conditional expectations `torusCondExp` with
the family's weights.

DERIVED: `2 * j + 1` is the index of the even-extent family. -/
def WeightedFamilyAt.toHB {hN : N ≠ 0} {β : ℝ} {n j : ℕ} {a₁ a₂ b e : ℝ}
    (W : WeightedFamilyAt hN β n j a₁ a₂ b e) : WilsonHeatBath hN β j where
  κ := WilsonHypercubic.Site 4 (2 * j + 1 + 1)
  condExp := torusCondExp β (2 * j + 1)
  selfAdj := torusCondExp_selfAdj hN β j
  idem := torusCondExp_idem β (2 * j + 1)
  reads_not := torusCondExp_readsNot β j
  keeps := torusCondExp_keeps β j
  c := W.c
  w := W.w
  a₁ := a₁
  a₂ := a₂
  b := b
  e := e
  cover := W.cover
  cover2 := W.cover2
  pair := fun l l' hll => (W.pair l l' hll).imp_left
    (fun h => ⟨fun x => torusCondExp_comm β (2 * j + 1) hll h.1 x, h.2⟩)
  w_nonneg := W.w_nonneg
  row := W.row
  col := W.col

/-- The box indicator is `0` or `1`.

DERIVED: `0`, `1` are the indicator's values. -/
theorem boxWeight_nonneg {M : ℕ} (n : ℕ) (k : WilsonHypercubic.Site 4 (M + 1))
    (l : WilsonHypercubic.Link 4 (M + 1)) : 0 ≤ BoxPatch.boxWeight n k l := by
  unfold BoxPatch.boxWeight; split_ifs <;> norm_num

#print axioms boxWeight_nonneg

theorem boxWeight_le_one {M : ℕ} (n : ℕ) (k : WilsonHypercubic.Site 4 (M + 1))
    (l : WilsonHypercubic.Link 4 (M + 1)) : BoxPatch.boxWeight n k l ≤ 1 := by
  unfold BoxPatch.boxWeight; split_ifs <;> norm_num

#print axioms boxWeight_le_one

/-- The weighted Knabe constant `(γ a₁²/n⁴ − a₂ + b − e)/b`.

DERIVED: `4` is the dimension of the box's cover `n⁴`; `2` the square of the cover. -/
def weightedConst (n : ℕ) (a₁ a₂ b e γ : ℝ) : ℝ :=
  (γ * a₁ ^ 2 / (n : ℝ) ^ 4 - a₂ + b - e) / b

/-- **The gap of the heat-bath sum from the box and the weights.** At `1 ≤ n ≤ j + 1`, `0 < γ`,
`0 < b`, `BoxPatch.BoxLocalGap hN β n γ` and a weight family at `j`: `GlobalGap (weightedConst …)`
at the family's heat-bath system (`WeightedBridge.weighted_gap_of_patch_gap`, with the patch gap of
`boxOp`, the bound `patch_form_le_cover` at the number of links, and `patch_dom`).

DERIVED: `4` is the spacetime dimension; `1` the least box side and the successor in `j + 1`;
`0` the excluded rank and the sign of `γ` and `b`. -/
theorem globalGap_weighted (hN : N ≠ 0) {β γ a₁ a₂ b e : ℝ} {n j : ℕ} (hn : 1 ≤ n)
    (hnj : n ≤ j + 1) (hbox : BoxPatch.BoxLocalGap hN β n γ) (hγ : 0 < γ) (hb : 0 < b)
    (W : WeightedFamilyAt hN β n j a₁ a₂ b e) :
    W.toHB.toPatchSystem.GlobalGap (weightedConst n a₁ a₂ b e γ) := by
  classical
  let B := torusForm hN β j
  let h : WilsonHypercubic.Link 4 (2 * j + 1 + 1) →
      ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)) →ₗ[ℝ]
        ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)) :=
    fun l => (LinearMap.id : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)) →ₗ[ℝ]
      ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) - torusCondExp β (2 * j + 1) l
  have hsymm : ∀ x y, B x y = B y x := torusForm_symm hN β j
  have hnn : ∀ x, 0 ≤ B x x := torusForm_nonneg hN β j
  have hsa : ∀ l x y, B (h l x) y = B x (h l y) := fun l =>
    selfAdj_id_sub B (torusCondExp β (2 * j + 1) l) (torusCondExp_selfAdj hN β j l)
  have hid : ∀ l x, h l (h l x) = h l x := fun l =>
    idem_id_sub (torusCondExp β (2 * j + 1) l) (torusCondExp_idem β (2 * j + 1) l)
  have hpair : ∀ l l', l ≠ l' →
      ((∀ x, h l (h l' x) = h l' (h l x)) ∧ pairWeight W.c l l' ≤ b)
        ∨ |pairWeight W.c l l' - b| ≤ W.w l l' := fun l l' hll =>
    (W.pair l l' hll).imp_left (fun hc => ⟨fun x => comm_id_sub (torusCondExp β (2 * j + 1) l)
      (torusCondExp β (2 * j + 1) l') (fun y => torusCondExp_comm β (2 * j + 1) hll hc.1 y) x,
      hc.2⟩)
  let L : ℝ := (Fintype.card (WilsonHypercubic.Link 4 (2 * j + 1 + 1)) : ℝ)
  let s : WilsonHypercubic.Site 4 (2 * j + 1 + 1) → WilsonHypercubic.Link 4 (2 * j + 1 + 1) → ℝ :=
    fun k l => BoxPatch.boxWeight n k l
  have hs0 : ∀ k l, 0 ≤ s k l := fun k l => boxWeight_nonneg n k l
  have hsum_s : ∀ k, ∑ l, s k l ≤ L := by
    intro k
    calc ∑ l, s k l ≤ ∑ _l : WilsonHypercubic.Link 4 (2 * j + 1 + 1), (1 : ℝ) :=
          Finset.sum_le_sum (fun l _ => boxWeight_le_one n k l)
      _ = L := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hsum_c : ∀ k, ∑ l, W.c k l ≤ W.cm * L := by
    intro k
    calc ∑ l, W.c k l ≤ ∑ l, W.cm * s k l := Finset.sum_le_sum (fun l _ => W.c_le k l)
      _ = W.cm * ∑ l, s k l := by rw [Finset.mul_sum]
      _ ≤ W.cm * L := mul_le_mul_of_nonneg_left (hsum_s k) W.cm_nonneg
  let K := max L γ
  have hK0 : 0 < K := lt_of_lt_of_le hγ (le_max_right _ _)
  have hγK : γ ≤ K := le_max_right _ _
  have hn4 : (0 : ℝ) < (n : ℝ) ^ 4 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have hcovs : ∀ l, ∑ k, s k l = (n : ℝ) ^ 4 := fun l => BoxPatch.box_cover n (by omega) l
  have hgap : ∀ k x, γ * B (patchOp s h k x) x ≤ B (patchOp s h k x) (patchOp s h k x) :=
    fun k x => hbox j hnj k x
  have hFnn : ∀ k x, 0 ≤ B (patchOp s h k x) x := by
    intro k x
    calc (0 : ℝ) ≤ ∑ i, s k i * B (h i x) (h i x) :=
          Finset.sum_nonneg (fun i _ => mul_nonneg (hs0 k i) (hnn _))
      _ = B (patchOp s h k x) x := (patch_reading_eq B h hsa hid s k x).symm
  have hKb : ∀ k x, B (patchOp s h k x) (patchOp s h k x) ≤ K * B (patchOp s h k x) x := by
    intro k x
    have h1 := patch_form_le_cover B hsymm hnn h hsa hid s hs0 k x
    have h2 : (∑ i, s k i) * B (patchOp s h k x) x ≤ K * B (patchOp s h k x) x :=
      mul_le_mul_of_nonneg_right ((hsum_s k).trans (le_max_left _ _)) (hFnn k x)
    linarith
  have hAF : ∀ k z, B (patchOp W.c h k z) (patchOp W.c h k z)
      ≤ (W.cm * L * W.cm) * B (patchOp s h k z) z := by
    intro k z
    have h1 := patch_dom B hsymm hnn h hsa hid W.c s W.c_nonneg W.c_le k z
    have h2 : (∑ i, W.c k i) * W.cm * B (patchOp s h k z) z
        ≤ (W.cm * L * W.cm) * B (patchOp s h k z) z :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hsum_c k) W.cm_nonneg) (hFnn k z)
    linarith
  intro x
  have hmain := MassGap.WeightedBridge.weighted_gap_of_patch_gap B hsymm hnn h hsa hid
    W.c s W.w W.c_nonneg hs0 W.cover hcovs hn4 hγ hK0 hγK W.cover2 hpair W.w_nonneg
    W.row W.col hgap hKb hAF x
  show weightedConst n a₁ a₂ b e γ * B (totalOp h x) x ≤ B (totalOp h x) (totalOp h x)
  unfold weightedConst
  rw [div_mul_eq_mul_div, div_le_iff₀ hb]
  linarith

#print axioms globalGap_weighted

/-- `weightedConst > 0` exactly when `γ` is above the weighted threshold `(a₂ − b + e) n⁴/a₁²`.

DERIVED: `0` is the sign of `b`, `a₁`, `n`; `4`, `2` as in `weightedConst`. -/
theorem weightedConst_pos {n : ℕ} (hn : 1 ≤ n) {a₁ a₂ b e γ : ℝ} (ha₁ : a₁ ≠ 0) (hb : 0 < b)
    (hthr : (a₂ - b + e) * (n : ℝ) ^ 4 / a₁ ^ 2 < γ) : 0 < weightedConst n a₁ a₂ b e γ := by
  unfold weightedConst
  have hn4 : (0 : ℝ) < (n : ℝ) ^ 4 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have ha2 : 0 < a₁ ^ 2 := by positivity
  apply div_pos _ hb
  rw [div_lt_iff₀ ha2] at hthr
  have : (a₂ - b + e) * (n : ℝ) ^ 4 < γ * a₁ ^ 2 := hthr
  have h2 : a₂ - b + e < γ * a₁ ^ 2 / (n : ℝ) ^ 4 := by
    rw [lt_div_iff₀ hn4]; linarith
  linarith

#print axioms weightedConst_pos

/-- The family: the weight family's system from `n ≤ j + 1` on, the one-patch system below.

DERIVED: `1` is the successor in `j + 1`; `0` is the excluded rank. -/
def weightedFamily (hN : N ≠ 0) (β : ℝ) (n : ℕ) {a₁ a₂ b e : ℝ}
    (W : ∀ j, n ≤ j + 1 → WeightedFamilyAt hN β n j a₁ a₂ b e) : ∀ j : ℕ, WilsonHeatBath hN β j :=
  fun j => if h : n ≤ j + 1 then (W j h).toHB else BoxPatch.onePatch hN β j

/-- The IR rate of the weighted box: `−log(clusterRate 21 c₀)/aRun N β₀`.

DERIVED: `21` is `card_nbT_le`'s bound. -/
def weightedRate (N : ℕ) (β₀ c₀ : ℝ) : ℝ :=
  -Real.log (clusterRate 21 c₀) / MassGap.AsymptoticScaling.aRun N β₀

/-- **The IR gap from the weighted box.** At `1 ≤ N`, `0 < β₀`, `1 ≤ n`, `0 < γ`, `0 < b`, `a₁ ≠ 0`,
`γ > (a₂ − b + e) n⁴/a₁²`, `BoxPatch.BoxLocalGap hN β₀ n γ` and a weight family at every `j ≥ n − 1`:
`0 < weightedRate` and `UVIRSplit.IRGapAt τ p hN β₀ (weightedRate N β₀ (weightedConst n a₁ a₂ b e γ))`.

DERIVED: `4` is the spacetime dimension; `21` is `card_nbT_le`'s bound; `1` is the least colour count
and box side; `0` the excluded rank and the signs. -/
theorem irGapAt_weightedBox (τ : Fin 4) (p : ℤ) (hN1 : 1 ≤ N) (hN : N ≠ 0) {β₀ γ a₁ a₂ b e : ℝ}
    {n : ℕ} (hβ₀ : 0 < β₀) (hn : 1 ≤ n) (hγ : 0 < γ) (hb : 0 < b) (ha₁ : a₁ ≠ 0)
    (hthr : (a₂ - b + e) * (n : ℝ) ^ 4 / a₁ ^ 2 < γ) (hbox : BoxPatch.BoxLocalGap hN β₀ n γ)
    (W : ∀ j, n ≤ j + 1 → WeightedFamilyAt hN β₀ n j a₁ a₂ b e) :
    0 < weightedRate N β₀ (weightedConst n a₁ a₂ b e γ)
      ∧ UVIRSplit.IRGapAt τ p hN β₀ (weightedRate N β₀ (weightedConst n a₁ a₂ b e γ)) := by
  set S := weightedFamily hN β₀ n W with hS
  have hc₀ := weightedConst_pos hn ha₁ hb hthr
  have hG : ∀ᶠ j in Filter.atTop, (S j).toPatchSystem.GlobalGap (weightedConst n a₁ a₂ b e γ) := by
    refine Filter.eventually_atTop.mpr ⟨n, fun j hj => ?_⟩
    have hnj : n ≤ j + 1 := by omega
    have hSj : S j = (W j hnj).toHB := by
      rw [hS]; unfold weightedFamily; exact dif_pos hnj
    rw [hSj]
    exact globalGap_weighted hN hn hnj hbox hγ hb (W j hnj)
  obtain ⟨hr0, hr1, hcl⟩ :=
    torusClusterAt_of_localityAt τ p hN β₀ (localityAt_holds τ p hN β₀ S) hc₀ hG
  have hg := gapAt_of_torusClusterAt τ p hN β₀ hr0.le hcl
  have ha : 0 < MassGap.AsymptoticScaling.aRun N β₀ := MassGap.AsymptoticScaling.aRun_pos hN1 hβ₀
  refine ⟨div_pos (neg_pos.mpr (Real.log_neg hr0 hr1)) ha, ?_⟩
  unfold UVIRSplit.IRGapAt weightedRate
  rw [div_mul_cancel₀ _ ha.ne', neg_neg, Real.exp_log hr0]
  exact hg

#print axioms irGapAt_weightedBox

open MassGap.ContinuumField MassGap.ContinuumSchwinger in
/-- **The continuum Clay statement from one box at the weighted threshold.** At `2 ≤ N`, `0 < L`,
`0 < β₀`, `βUV ≤ β₀`, `1 ≤ n`:
* the box check `BoxGap.BoxFibreGap hN β₀ n γ` with `0 < γ` and `γ > (a₂ − b + e) n⁴/a₁²`;
* a weight family `WeightedFamilyAt hN β₀ n j a₁ a₂ b e` at every `j ≥ n − 1`, `0 < b`, `a₁ ≠ 0`;
* the UV step below the box's rate, `RestoreShimsClay.UVBelowIR τ 0 hN β₀ βUV (weightedRate …)`;
* E (`hB`), the kernel convergence `hconv` and the short-distance input `hY`, as in
  `RestoreShimsClay.clay_continuum_of_boxPatchGap`;
give `ClayRoutes.ClayContinuum hN Z τ hZ hB L`.

DERIVED: `2` is the least rank with a non-zero Haar variance; `0` is the excluded colour count, the
reflection plane and the lower ends; `4` in `Fin 4` is the spacetime dimension; `1` the least colour
count and box side. -/
theorem clay_continuum_of_weightedBox (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {β₀ βUV γ a₁ a₂ b e : ℝ} {n : ℕ} (hβ₀ : 0 < β₀) (hUVβ₀ : βUV ≤ β₀) (hn : 1 ≤ n)
    (hγ : 0 < γ) (hb : 0 < b) (ha₁ : a₁ ≠ 0) (hthr : (a₂ - b + e) * (n : ℝ) ^ 4 / a₁ ^ 2 < γ)
    (hbox : BoxGap.BoxFibreGap hN β₀ n γ)
    (W : ∀ j, n ≤ j + 1 → WeightedFamilyAt hN β₀ n j a₁ a₂ b e)
    (huv : ClayRoutes.UVBelowIR τ 0 hN β₀ βUV (weightedRate N β₀ (weightedConst n a₁ a₂ b e γ)))
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum hN Z τ hZ hB L :=
  ClayRoutes.clay_continuum_of_irGap hN2 hN Z τ hZ hB hL hβ₀ hUVβ₀
    (irGapAt_weightedBox τ 0 (by omega) hN hβ₀ hn hγ hb ha₁ hthr
      (BoxGap.boxLocalGap_of_fibreGap hN hbox) W).2 huv O G hconv hY

#print axioms clay_continuum_of_weightedBox

end Wilson

end MassGap.WeightedBox
