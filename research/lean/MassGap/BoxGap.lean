import Mathlib
import MassGap.BoxPatch

noncomputable section

/-!
# MassGap.BoxGap — the box-patch gap as one box under every boundary, at `β = 0`, and its routes

## What it gives

1. **The patch gap from pair defects.** `patch_gap_of_defect`: on a module with a non-negative
   bilinear form `B`, `B`-self-adjoint idempotents `hᵢ` and a patch `A = Σᵢ cᵢ • hᵢ` with `0/1`
   weights, if every pair `i ≠ j` of the patch has `B(hᵢx, hⱼx) ≥ −δᵢⱼ(B(hᵢx, hᵢx) + B(hⱼx, hⱼx))/2`
   for a non-negative matrix `δ` of row and column sums at most `Δ` (`DefectMatrix`), then
   `(1 − Δ)·B(Ax, x) ≤ B(Ax, Ax)`. The bound reads the defect row sums, not the size of the patch.
   `patch_gap_one_of_comm`: commuting pairs have defect `0`, so the patch gap is `1`.
2. **Two projections.** `pair_defect_of_corr`: for `B`-self-adjoint idempotents `P`, `Q` and
   `0 ≤ r ≤ 1`, `B(Pf, Qf) ≤ r·(B(Pf, Pf) + B(Qf, Qf))/2` gives
   `B(f − Pf, f − Qf) ≥ −r·(B(f − Pf, f − Pf) + B(f − Qf, f − Qf))/2` (from
   `B((1 + r)f − Pf − Qf, ·) ≥ 0`). `corr_zero_of_comm`: for commuting `P`, `Q` the correlation of
   `x − PQx` is `0`.
3. **The threshold.** `threshold_lt_of_ge`: `40/γ ≤ m` gives `(40m − 36)/m² < γ`.
   `threshold_lt_one_iff`: at `γ = 1` the threshold holds exactly from `n = 40` on.
4. **`β = 0`.** At `β = 0` the local weight is `1` (`locW_zero`), the heat bath is the Haar average
   over the link (`heatAvg_zero`), and any two heat baths commute (`heatAvg_comm_zero`,
   `torusCondExp_comm_zero`). So every box patch has local gap `1` (`boxLocalGap_zero`) and
   `BoxPatch.BoxPatchGap hN 0 n 1` holds for every `n ≥ 40` (`boxPatchGap_zero`).
5. **The pair route.** `BoxPairDefect hN β Δ`: at every extent a defect matrix of row and column
   sums at most `Δ` bounds the pair terms of the complements `x − E_l x`; it gives the local gap
   `1 − Δ` at every box side (`boxLocalGap_of_pairDefect`), and `BoxPatchGap` at side `80` for
   `Δ ≤ 1/2` and at side `⌈40/(1 − Δ)⌉ + 2` for `Δ < 1`. `BoxPairCorr hN β Δ` asks the same, with entries at most `1`,
   of the two-link correlations `B(E_l f, E_m f)` of the vector `f = x − y` with `y` fixed by both
   (`pairDefectAt_of_pairCorrAt`); it holds at `β = 0` with `Δ = 0` (`boxPairCorr_zero`).
   `PairCorrLinear hN C β₁`: `BoxPairCorr hN β (Cβ)` on `[0, β₁]`; it gives `BoxPatchGap` at side
   `80` and gap `1 − Cβ` for `β ≤ min(β₁, 1/(2C))` (`boxPatchGap_of_pairCorrLinear`).
6. **One box under every boundary.** `glue S W V` reads `V` on the links of `S` and `W` elsewhere;
   `measurePreserving_glue` and `integral_eq_integral_glue` integrate out the links of `S` with the
   rest frozen. `torusForm_eq_integral` writes `torusForm` as the Gibbs integral. The heat bath at a
   link of `S` acts inside the fibre (`heatAvg_glue`), the box patch operator is
   `Σ_{l ∈ box} (x − E_l x)` (`boxOp_apply`), and the fibre weight factors into the weight of the
   plaquettes meeting `S` times a constant of the boundary (`wt_glue`, `fibre_iff_local`).
   `BoxFibreGap hN β n γ`: for every boundary configuration `W`, the fibre integral over the box's
   links with the local weight satisfies the local-gap inequality; it gives `BoxLocalGap`
   (`boxLocalGap_of_fibreGap`) and, with the threshold, `BoxPatchGap` (`boxPatchGap_of_fibreGap`).
7. **Relaxation.** `gap_of_relax`: a contraction `‖(K − A)u‖ ≤ ρK‖u‖` on the complement of the
   kernel of a `B`-self-adjoint `A` gives the local gap `K(1 − ρ)`. `boxOp_selfAdj`: the box patch
   operator is `torusForm`-self-adjoint.
-/

namespace MassGap.BoxGap

open MeasureTheory
open MassGap MassGap.HeatBath MassGap.KnabeCriterion MassGap.BoxPatch
open MassGap.SUN (SU)
open MassGap.CompactGauge (probHaar)
open MassGap.PeriodicState (torusObs torusState)
open MassGap.WilsonLattice (wilsonSystem wilsonHol)
open MassGap.WilsonAction (wilsonDensity)

/-! ## 1. The patch gap from pair defects -/

section Engine

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **A defect matrix**: `δ ≥ 0` with every row sum and every column sum at most `Δ`.

DERIVED: `0` is the sign of the entries. -/
def DefectMatrix (δ : ι → ι → ℝ) (Δ : ℝ) : Prop :=
  (∀ i j, 0 ≤ δ i j) ∧ (∀ i, ∑ j, δ i j ≤ Δ) ∧ ∀ j, ∑ i, δ i j ≤ Δ

/-- **The patch gap from pair defects.** For a non-negative bilinear form `B`, `B`-self-adjoint
idempotents `hᵢ`, a patch `A = patchOp c h k` whose weights `c k i` are `0` or `1`, and a defect
matrix `δ` with row and column sums at most `Δ`: if every pair `i ≠ j` in the patch has
`−δᵢⱼ(B(hᵢx, hᵢx) + B(hⱼx, hⱼx))/2 ≤ B(hᵢx, hⱼx)`, then `(1 − Δ)·B(Ax, x) ≤ B(Ax, Ax)`.

`B(Ax, Ax) = Σᵢⱼ cᵢcⱼ B(hᵢx, hⱼx)` and `B(Ax, x) = Σᵢ cᵢ B(hᵢx, hᵢx)` (`form_proj_self`); the
diagonal gives `B(Ax, x)` since `cᵢ² = cᵢ`, and the off-diagonal terms lose at most
`Σᵢ cᵢ B(hᵢx, hᵢx)·(row sum + column sum)/2 ≤ Δ·B(Ax, x)`.

DERIVED: `1` is the gap at zero defect; `0` and `1` are the weight values; `2` is the halving of the
pair bound. -/
theorem patch_gap_of_defect (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hnn : ∀ x, 0 ≤ B x x)
    (h : ι → E →ₗ[ℝ] E) (hsa : ∀ i x y, B (h i x) y = B x (h i y))
    (hid : ∀ i x, h i (h i x) = h i x) (c : κ → ι → ℝ) (k : κ)
    (hc : ∀ i, c k i = 0 ∨ c k i = 1) (δ : ι → ι → ℝ) {Δ : ℝ} (hδ : DefectMatrix δ Δ) (x : E)
    (hpair : ∀ i j, i ≠ j → c k i = 1 → c k j = 1 →
      -(δ i j * (B (h i x) (h i x) + B (h j x) (h j x)) / 2) ≤ B (h i x) (h j x)) :
    (1 - Δ) * B (patchOp c h k x) x ≤ B (patchOp c h k x) (patchOp c h k x) := by
  classical
  obtain ⟨hδ0, hrow, hcol⟩ := hδ
  have hA : B (patchOp c h k x) (patchOp c h k x)
      = ∑ i, ∑ j, c k i * c k j * B (h i x) (h j x) := by
    rw [patchOp_apply, form_sum_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hAx : B (patchOp c h k x) x = ∑ i, c k i * B (h i x) (h i x) := by
    rw [patchOp_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [form_proj_self B (h i) (hsa i) (hid i) x]
  have hc0 : ∀ i, 0 ≤ c k i := by
    intro i
    rcases hc i with h0 | h1
    · simp [h0]
    · simp [h1]
  have hc1 : ∀ i, c k i ≤ 1 := by
    intro i
    rcases hc i with h0 | h1
    · simp [h0]
    · simp [h1]
  have hcc : ∀ i, c k i * c k i = c k i := by
    intro i
    rcases hc i with h0 | h1
    · simp [h0]
    · simp [h1]
  -- each pair term
  have hterm : ∀ i j, (if i = j then c k i * B (h i x) (h i x) else 0)
      - c k i * c k j * δ i j * (B (h i x) (h i x) + B (h j x) (h j x)) / 2
      ≤ c k i * c k j * B (h i x) (h j x) := by
    intro i j
    have hii := hnn (h i x)
    have hjj := hnn (h j x)
    rcases eq_or_ne i j with rfl | hij
    · rw [if_pos rfl, hcc i]
      have hnd : 0 ≤ c k i * δ i i * (B (h i x) (h i x) + B (h i x) (h i x)) / 2 :=
        div_nonneg (mul_nonneg (mul_nonneg (hc0 i) (hδ0 i i)) (add_nonneg hii hii)) zero_le_two
      linarith
    · rw [if_neg hij]
      rcases hc i with hi0 | hi1
      · rw [hi0]
        simp
      · rcases hc j with hj0 | hj1
        · rw [hj0]
          simp
        · have hp := hpair i j hij hi1 hj1
          rw [hi1, hj1]
          linarith
  -- the diagonal and the split of the defect sum
  have hdiag : ∑ i, ∑ j, (if i = j then c k i * B (h i x) (h i x) else 0)
      = ∑ i, c k i * B (h i x) (h i x) :=
    Finset.sum_congr rfl (fun i _ => by rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i)])
  have hsplit : ∑ i, ∑ j, c k i * c k j * δ i j * (B (h i x) (h i x) + B (h j x) (h j x)) / 2
      = (∑ i, ∑ j, c k i * c k j * δ i j * B (h i x) (h i x)
        + ∑ i, ∑ j, c k i * c k j * δ i j * B (h j x) (h j x)) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  -- the row and column bounds
  have hD1 : ∑ i, ∑ j, c k i * c k j * δ i j * B (h i x) (h i x)
      ≤ Δ * ∑ i, c k i * B (h i x) (h i x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have hX : 0 ≤ c k i * B (h i x) (h i x) := mul_nonneg (hc0 i) (hnn (h i x))
    calc ∑ j, c k i * c k j * δ i j * B (h i x) (h i x)
        ≤ ∑ j, c k i * B (h i x) (h i x) * δ i j := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          have hm := mul_le_mul_of_nonneg_right (hc1 j) (mul_nonneg hX (hδ0 i j))
          calc c k i * c k j * δ i j * B (h i x) (h i x)
              = c k j * (c k i * B (h i x) (h i x) * δ i j) := by ring
            _ ≤ 1 * (c k i * B (h i x) (h i x) * δ i j) := hm
            _ = c k i * B (h i x) (h i x) * δ i j := one_mul _
      _ = c k i * B (h i x) (h i x) * ∑ j, δ i j := (Finset.mul_sum _ _ _).symm
      _ ≤ c k i * B (h i x) (h i x) * Δ := mul_le_mul_of_nonneg_left (hrow i) hX
      _ = Δ * (c k i * B (h i x) (h i x)) := mul_comm _ _
  have hD2 : ∑ i, ∑ j, c k i * c k j * δ i j * B (h j x) (h j x)
      ≤ Δ * ∑ j, c k j * B (h j x) (h j x) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have hX : 0 ≤ c k j * B (h j x) (h j x) := mul_nonneg (hc0 j) (hnn (h j x))
    calc ∑ i, c k i * c k j * δ i j * B (h j x) (h j x)
        ≤ ∑ i, c k j * B (h j x) (h j x) * δ i j := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have hm := mul_le_mul_of_nonneg_right (hc1 i) (mul_nonneg hX (hδ0 i j))
          calc c k i * c k j * δ i j * B (h j x) (h j x)
              = c k i * (c k j * B (h j x) (h j x) * δ i j) := by ring
            _ ≤ 1 * (c k j * B (h j x) (h j x) * δ i j) := hm
            _ = c k j * B (h j x) (h j x) * δ i j := one_mul _
      _ = c k j * B (h j x) (h j x) * ∑ i, δ i j := (Finset.mul_sum _ _ _).symm
      _ ≤ c k j * B (h j x) (h j x) * Δ := mul_le_mul_of_nonneg_left (hcol j) hX
      _ = Δ * (c k j * B (h j x) (h j x)) := mul_comm _ _
  -- the pair terms summed
  have hkey : ∑ i, c k i * B (h i x) (h i x)
      - (∑ i, ∑ j, c k i * c k j * δ i j * B (h i x) (h i x)
        + ∑ i, ∑ j, c k i * c k j * δ i j * B (h j x) (h j x)) / 2
      ≤ ∑ i, ∑ j, c k i * c k j * B (h i x) (h j x) := by
    rw [← hdiag, ← hsplit, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun j _ => hterm i j)
  rw [hA, hAx]
  linarith

#print axioms patch_gap_of_defect

/-- **Commuting pairs give patch gap `1`.** With `0/1` weights, if every two terms of the patch
commute, `B(Ax, x) ≤ B(Ax, Ax)`: `patch_gap_of_defect` at `δ = 0`, the pair terms being non-negative
(`form_comm_nonneg`).

DERIVED: `0` and `1` are the weight values; `0` is the defect. -/
theorem patch_gap_one_of_comm (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hnn : ∀ x, 0 ≤ B x x)
    (h : ι → E →ₗ[ℝ] E) (hsa : ∀ i x y, B (h i x) y = B x (h i y))
    (hid : ∀ i x, h i (h i x) = h i x) (c : κ → ι → ℝ) (k : κ)
    (hc : ∀ i, c k i = 0 ∨ c k i = 1)
    (hcomm : ∀ i j, i ≠ j → c k i = 1 → c k j = 1 → ∀ y, h i (h j y) = h j (h i y)) (x : E) :
    B (patchOp c h k x) x ≤ B (patchOp c h k x) (patchOp c h k x) := by
  have hδ : DefectMatrix (fun _ _ : ι => (0 : ℝ)) 0 :=
    ⟨fun _ _ => le_refl 0, fun _ => by simp, fun _ => by simp⟩
  have key := patch_gap_of_defect B hnn h hsa hid c k hc (fun _ _ => 0) hδ x
    (fun i j hij hi hj => by
      have h0 := form_comm_nonneg B hnn (h i) (h j) (hsa i) (hsa j) (hid i) (hid j)
        (hcomm i j hij hi hj) x
      simp only [zero_mul, zero_div, neg_zero]
      exact h0)
  rw [sub_zero, one_mul] at key
  exact key

#print axioms patch_gap_one_of_comm

/-- **Two projections: the pair defect from the correlation.** For a symmetric non-negative `B`,
`B`-self-adjoint idempotents `P`, `Q`, `0 ≤ r ≤ 1` and a vector `f` with
`B(Pf, Qf) ≤ r·(B(Pf, Pf) + B(Qf, Qf))/2`:
`−r·(B(f − Pf, f − Pf) + B(f − Qf, f − Qf))/2 ≤ B(f − Pf, f − Qf)`.

With `F = B(f, f)`, `a = B(Pf, Pf)`, `c = B(Qf, Qf)`, `X = B(Pf, Qf)`, the claim is
`(1 + r)F − (1 + r/2)(a + c) + X ≥ 0`; times `1 + r` it is
`B((1 + r)f − Pf − Qf, (1 + r)f − Pf − Qf) + (1 − r)(r(a + c)/2 − X)`.

DERIVED: `0` and `1` bound `r`; `2` is the halving of the pair bound; `1 + r` is the multiplier. -/
theorem pair_defect_of_corr (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (P Q : E →ₗ[ℝ] E)
    (hsP : ∀ x y, B (P x) y = B x (P y)) (hsQ : ∀ x y, B (Q x) y = B x (Q y))
    (hiP : ∀ x, P (P x) = P x) (hiQ : ∀ x, Q (Q x) = Q x) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (f : E) (hcorr : B (P f) (Q f) ≤ r * (B (P f) (P f) + B (Q f) (Q f)) / 2) :
    -(r * (B (f - P f) (f - P f) + B (f - Q f) (f - Q f)) / 2) ≤ B (f - P f) (f - Q f) := by
  have e1 : B f (P f) = B (P f) (P f) := by
    rw [← hsP f f]
    exact form_proj_self B P hsP hiP f
  have e2 : B (P f) f = B (P f) (P f) := form_proj_self B P hsP hiP f
  have e3 : B f (Q f) = B (Q f) (Q f) := by
    rw [← hsQ f f]
    exact form_proj_self B Q hsQ hiQ f
  have e4 : B (Q f) f = B (Q f) (Q f) := form_proj_self B Q hsQ hiQ f
  have e5 : B (Q f) (P f) = B (P f) (Q f) := hsymm _ _
  have hq := hnn ((1 + r) • f - (P f + Q f))
  simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul] at hq
  rw [e1, e2, e3, e4, e5] at hq
  simp only [map_sub, LinearMap.sub_apply]
  rw [e1, e2, e3, e4]
  have h2 : 0 ≤ (1 - r) * (r * (B (P f) (P f) + B (Q f) (Q f)) / 2 - B (P f) (Q f)) :=
    mul_nonneg (by linarith) (by linarith)
  have h3 : 0 ≤ (1 + r) * ((1 + r) * B f f - (1 + r / 2) * (B (P f) (P f) + B (Q f) (Q f))
      + B (P f) (Q f)) := by
    nlinarith [hq, h2]
  have h4 := (mul_nonneg_iff_of_pos_left (by linarith : (0 : ℝ) < 1 + r)).mp h3
  nlinarith [h4]

#print axioms pair_defect_of_corr

/-- **Commuting projections have zero correlation off their common range.** For `B`-self-adjoint
idempotents `P`, `Q` that commute: `B(P(x − PQx), Q(x − PQx)) = 0`.

DERIVED: `0` is the value asserted. -/
theorem corr_zero_of_comm (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (P Q : E →ₗ[ℝ] E)
    (hsP : ∀ x y, B (P x) y = B x (P y)) (hsQ : ∀ x y, B (Q x) y = B x (Q y))
    (hiP : ∀ x, P (P x) = P x) (hiQ : ∀ x, Q (Q x) = Q x)
    (hcomm : ∀ x, P (Q x) = Q (P x)) (x : E) :
    B (P (x - P (Q x))) (Q (x - P (Q x))) = 0 := by
  have hu1 : P (x - P (Q x)) = P x - P (Q x) := by rw [map_sub, hiP (Q x)]
  have hu2 : Q (x - P (Q x)) = Q x - P (Q x) := by rw [map_sub, ← hcomm (Q x), hiQ x]
  have t1 : B (P x) (P (Q x)) = B (P x) (Q x) := by
    rw [hsP x (P (Q x)), hiP (Q x), ← hsP x (Q x)]
  have t2 : B (P (Q x)) (Q x) = B (P x) (Q x) := by
    rw [hcomm x, hsQ (P x) (Q x), hiQ x]
  have t3 : B (P (Q x)) (P (Q x)) = B (P x) (Q x) := by
    rw [← form_proj_self B P hsP hiP (Q x)]
    exact t2
  rw [hu1, hu2]
  simp only [map_sub, LinearMap.sub_apply]
  rw [t1, t2, t3]
  ring

#print axioms corr_zero_of_comm

/-- **The local gap from a contraction of the relaxed operator.** For a symmetric non-negative `B`,
any `A`, `0 < ρ ≤ 1` and a vector `u` with `B(Ku − Au, Ku − Au) ≤ (ρK)²·B(u, u)`:
`K(1 − ρ)·B(Au, u) ≤ B(Au, Au)`.

With `a₁ = B(u, u)`, `a₂ = B(Au, u)`, `a₃ = B(Au, Au)` and `Q = B((1 − ρ)Ku − Au, ·) ≥ 0`:
`2ρ(ρK²a₁ − K²a₁ + Ka₂) = Q + (ρ²K²a₁ − B(Ku − Au, Ku − Au)) ≥ 0`, and
`a₃ − K(1 − ρ)a₂ = Q + (1 − ρ)(ρK²a₁ − K²a₁ + Ka₂)`.

DERIVED: `0` and `1` bound `ρ`; `2` is the exponent of the contraction. -/
theorem gap_of_relax_core (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (A : E →ₗ[ℝ] E) {K ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (u : E)
    (hcon : B (K • u - A u) (K • u - A u) ≤ (ρ * K) ^ 2 * B u u) :
    K * (1 - ρ) * B (A u) u ≤ B (A u) (A u) := by
  have hs : B u (A u) = B (A u) u := hsymm u (A u)
  have hQ := hnn (((1 - ρ) * K) • u - A u)
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    at hQ hcon
  rw [hs] at hQ hcon
  have hD : 0 ≤ ρ * (ρ * K ^ 2 * B u u - K ^ 2 * B u u + K * B (A u) u) := by
    nlinarith [hQ, hcon]
  have hD' := (mul_nonneg_iff_of_pos_left hρ0).mp hD
  nlinarith [hQ, mul_nonneg (sub_nonneg.mpr hρ1) hD']

#print axioms gap_of_relax_core

/-- **The local gap from a contraction on the complement of the kernel.** For a symmetric
non-negative `B`, a `B`-self-adjoint `A`, `0 < ρ ≤ 1`, and `x`, `y` with `Ay = 0` and
`B(K(x − y) − A(x − y), ·) ≤ (ρK)²·B(x − y, x − y)`: `K(1 − ρ)·B(Ax, x) ≤ B(Ax, Ax)`
(`gap_of_relax_core` at `u = x − y`, with `A(x − y) = Ax` and `B(Ax, x − y) = B(Ax, x)`).

DERIVED: `0` and `1` bound `ρ`; `0` is the kernel condition; `2` is the exponent of the
contraction. -/
theorem gap_of_relax (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (A : E →ₗ[ℝ] E) (hsa : ∀ x y, B (A x) y = B x (A y)) {K ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (x y : E) (hy : A y = 0)
    (hcon : B (K • (x - y) - A (x - y)) (K • (x - y) - A (x - y))
      ≤ (ρ * K) ^ 2 * B (x - y) (x - y)) :
    K * (1 - ρ) * B (A x) x ≤ B (A x) (A x) := by
  have hAu : A (x - y) = A x := by rw [map_sub, hy, sub_zero]
  have hB : B (A x) (x - y) = B (A x) x := by rw [map_sub, hsa x y, hy, map_zero, sub_zero]
  have key := gap_of_relax_core B hsymm hnn A hρ0 hρ1 (x - y) hcon
  rw [hAu, hB] at key
  exact key

#print axioms gap_of_relax

/-- A patch operator of `B`-self-adjoint terms with real weights is `B`-self-adjoint.

DERIVED: no numeral. -/
theorem patchOp_selfAdj (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (h : ι → E →ₗ[ℝ] E)
    (hsa : ∀ i x y, B (h i x) y = B x (h i y)) (c : κ → ι → ℝ) (k : κ) (x y : E) :
    B (patchOp c h k x) y = B x (patchOp c h k y) := by
  rw [patchOp_apply, patchOp_apply, map_sum, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hsa i x y]

#print axioms patchOp_selfAdj

end Engine

/-! ## 2. The threshold -/

section Threshold

/-- **The threshold from a side at least `40/γ`.** For `0 < γ` and `40/γ ≤ m`:
`(40m − 36)/m² < γ`.

DERIVED: `40`, `36` are the threshold's coefficients (`BoxPatch.boxKnabe`); `2` is the exponent;
`0` is the sign of `γ`. -/
theorem threshold_lt_of_ge {m γ : ℝ} (hγ : 0 < γ) (hm : 40 / γ ≤ m) :
    (40 * m - 36) / m ^ 2 < γ := by
  have hm0 : 0 < m := lt_of_lt_of_le (div_pos (by norm_num) hγ) hm
  have h40 : 40 ≤ m * γ := (div_le_iff₀ hγ).mp hm
  rw [div_lt_iff₀ (pow_pos hm0 2)]
  nlinarith [mul_le_mul_of_nonneg_left h40 hm0.le]

#print axioms threshold_lt_of_ge

/-- **At patch gap `1` the threshold holds exactly from side `40` on.** For `1 ≤ n`:
`(40n − 36)/n² < 1 ↔ 40 ≤ n` (`n² − 40n + 36 = (n − 1)(n − 39) − 3`).

DERIVED: `40`, `36` are the threshold's coefficients; `2` is the exponent; `1` is the patch gap
and the least side; `39` is the largest side below the threshold. -/
theorem threshold_lt_one_iff {n : ℕ} (hn : 1 ≤ n) :
    (40 * (n : ℝ) - 36) / (n : ℝ) ^ 2 < 1 ↔ 40 ≤ n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_lt_one (pow_pos (by linarith) 2)]
  constructor
  · intro h
    by_contra hlt
    have h39 : (n : ℝ) ≤ 39 := by exact_mod_cast (by omega : n ≤ 39)
    nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sub_nonneg.mpr h39)]
  · intro h
    have h40 : (40 : ℝ) ≤ n := by exact_mod_cast h
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ n) (sub_nonneg.mpr h40)]

#print axioms threshold_lt_one_iff

end Threshold

/-! ## 3. The heat bath at `β = 0` -/

section HeatBathZero

variable {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq] [DecidableEq Lk]

/-- At `β = 0` the local weight is `1`.

DERIVED: `0` is the coupling; `1` is `e⁰`. -/
theorem locW_zero (bd : Pq → List (Lk × Bool)) (l : Lk) (W : Lk → SU N) :
    locW bd 0 l W = 1 := by
  unfold locW
  rw [neg_zero, zero_mul, Real.exp_zero]

#print axioms locW_zero

/-- **At `β = 0` the heat bath is the Haar average over the link**
(`heatAvg_eq_loc`, `locW_zero`, `probReal_univ`).

DERIVED: `0` is the coupling. -/
theorem heatAvg_zero (bd : Pq → List (Lk × Bool)) (l : Lk) (f : (Lk → SU N) → ℝ)
    (W : Lk → SU N) :
    heatAvg bd 0 l f W = ∫ g, f (Function.update W l g) ∂(probHaar (SU N)) := by
  rw [heatAvg_eq_loc]
  simp [locW_zero, integral_const]

#print axioms heatAvg_zero

/-- **At `β = 0` any two heat baths commute** on continuous functions: both are the double Haar
average (`heatAvg_zero`, `Function.update_comm`, `integral_integral_swap`).

DERIVED: `0` is the coupling. -/
theorem heatAvg_comm_zero (bd : Pq → List (Lk × Bool)) {l l' : Lk} (hll : l ≠ l')
    {f : (Lk → SU N) → ℝ} (hf : Continuous f) (W : Lk → SU N) :
    heatAvg bd 0 l (heatAvg bd 0 l' f) W = heatAvg bd 0 l' (heatAvg bd 0 l f) W := by
  simp only [heatAvg_zero]
  have hu2 : Continuous (fun p : SU N × SU N =>
      Function.update (Function.update W l p.1) l' p.2) :=
    ((continuous_const : Continuous fun _ : SU N × SU N => W).update l continuous_fst).update l'
      continuous_snd
  obtain ⟨C, hC⟩ := exists_abs_le (hf.comp hu2)
  have hint : Integrable (Function.uncurry fun g h =>
      f (Function.update (Function.update W l g) l' h))
      ((probHaar (SU N)).prod (probHaar (SU N))) :=
    integrable_of_abs_le _ (hf.comp hu2).measurable hC
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun h => ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun g => ?_))
  show f (Function.update (Function.update W l g) l' h)
    = f (Function.update (Function.update W l' h) l g)
  rw [Function.update_comm hll g h W]

#print axioms heatAvg_comm_zero

end HeatBathZero

/-! ## 4. The box patches at `β = 0` -/

section BoxZero

variable {N : ℕ}

/-- **At `β = 0` any two torus conditional expectations commute** (`heatAvg_comm_zero`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent; `0` is the
coupling. -/
theorem torusCondExp_comm_zero (M : ℕ) {l l' : WilsonHypercubic.Link 4 (M + 1)} (hll : l ≠ l')
    (x : ↥(periodicGaugeInvSubmodule (N := N) M)) :
    torusCondExp 0 M l (torusCondExp 0 M l' x) = torusCondExp 0 M l' (torusCondExp 0 M l x) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro U
  show heatAvg (bdT M) 0 l (torusObs M (heatLift 0 M l' (x : C(GibbsSpec.IConf (SU N), ℝ))))
      (restrictConf M U)
    = heatAvg (bdT M) 0 l' (torusObs M (heatLift 0 M l (x : C(GibbsSpec.IConf (SU N), ℝ))))
      (restrictConf M U)
  rw [torusObs_heatLift, torusObs_heatLift]
  exact heatAvg_comm_zero (bdT M) hll (continuous_torusObs M _) _

#print axioms torusCondExp_comm_zero

/-- The box weights are `0` or `1`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent; `0` and `1` are
the indicator's values. -/
theorem boxWeight_cases {M : ℕ} (n : ℕ) (k : WilsonHypercubic.Site 4 (M + 1))
    (l : WilsonHypercubic.Link 4 (M + 1)) : boxWeight n k l = 0 ∨ boxWeight n k l = 1 := by
  unfold boxWeight
  by_cases h : InBox n (l.2 - k)
  · right
    exact if_pos h
  · left
    exact if_neg h

#print axioms boxWeight_cases

/-- **Every box patch has local gap `1` at `β = 0`** (`patch_gap_one_of_comm` with
`torusCondExp_comm_zero` and `KnabeCriterion.comm_id_sub`).

DERIVED: `0` is the coupling; `1` is the patch gap; `0` is the excluded rank in `hN`. -/
theorem boxLocalGap_zero (hN : N ≠ 0) (n : ℕ) : BoxLocalGap hN 0 n 1 := by
  intro j _ k x
  have h := patch_gap_one_of_comm (torusForm hN 0 j) (torusForm_nonneg hN 0 j)
    (fun l => (LinearMap.id : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))
      →ₗ[ℝ] ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) - torusCondExp 0 (2 * j + 1) l)
    (fun l => selfAdj_id_sub (torusForm hN 0 j) (torusCondExp 0 (2 * j + 1) l)
      (torusCondExp_selfAdj hN 0 j l))
    (fun l => idem_id_sub (torusCondExp 0 (2 * j + 1) l) (torusCondExp_idem 0 (2 * j + 1) l))
    (boxWeight n) k (fun l => boxWeight_cases n k l)
    (fun l m hlm _ _ y => comm_id_sub (torusCondExp 0 (2 * j + 1) l)
      (torusCondExp 0 (2 * j + 1) m) (fun z => torusCondExp_comm_zero (2 * j + 1) hlm z) y) x
  rw [one_mul]
  exact h

#print axioms boxLocalGap_zero

/-- **The box check at `β = 0`.** `BoxPatch.BoxPatchGap hN 0 n 1` for every `n ≥ 40`
(`boxLocalGap_zero`, `threshold_lt_one_iff`); `40` is the least side at gap `1`.

DERIVED: `0` is the coupling; `1` is the patch gap; `40` is the least side with
`(40n − 36)/n² < 1` (`threshold_lt_one_iff`); `0` is the excluded rank in `hN`. -/
theorem boxPatchGap_zero (hN : N ≠ 0) {n : ℕ} (hn : 40 ≤ n) : BoxPatchGap hN 0 n 1 :=
  ⟨by omega, (threshold_lt_one_iff (by omega)).mpr hn, boxLocalGap_zero hN n⟩

#print axioms boxPatchGap_zero

end BoxZero

/-! ## 5. The pair route -/

section PairRoute

variable {N : ℕ}

/-- **The pair defect at extent index `j`**: for every two links `l ≠ m` and every periodic
gauge-invariant `x`, the complements `x − E_l x`, `x − E_m x` of the torus conditional expectations
satisfy `−δ l m·(‖x − E_l x‖² + ‖x − E_m x‖²)/2 ≤ ⟨x − E_l x, x − E_m x⟩` in `torusForm`.

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `2` is the halving of the pair bound; `0` is the excluded
rank in `hN`. -/
def PairDefectAt (hN : N ≠ 0) (β : ℝ) (j : ℕ)
    (δ : WilsonHypercubic.Link 4 (2 * j + 1 + 1) → WilsonHypercubic.Link 4 (2 * j + 1 + 1) → ℝ) :
    Prop :=
  ∀ l m, l ≠ m → ∀ x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)),
    -(δ l m * (torusForm hN β j (x - torusCondExp β (2 * j + 1) l x)
          (x - torusCondExp β (2 * j + 1) l x)
        + torusForm hN β j (x - torusCondExp β (2 * j + 1) m x)
          (x - torusCondExp β (2 * j + 1) m x)) / 2)
      ≤ torusForm hN β j (x - torusCondExp β (2 * j + 1) l x) (x - torusCondExp β (2 * j + 1) m x)

/-- **The pair defect of the box heat bath**: at every extent index a defect matrix with row and
column sums at most `Δ` satisfies `PairDefectAt`.

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `0` is the excluded rank in `hN`. -/
def BoxPairDefect (hN : N ≠ 0) (β Δ : ℝ) : Prop :=
  ∀ j : ℕ, ∃ δ : WilsonHypercubic.Link 4 (2 * j + 1 + 1) → WilsonHypercubic.Link 4 (2 * j + 1 + 1) → ℝ,
    DefectMatrix δ Δ ∧ PairDefectAt hN β j δ

/-- **The pair defect gives the local gap `1 − Δ` at every box side** (`patch_gap_of_defect`).

DERIVED: `1` is the gap at zero defect; `0` is the excluded rank in `hN`. -/
theorem boxLocalGap_of_pairDefect (hN : N ≠ 0) {β Δ : ℝ} (n : ℕ) (h : BoxPairDefect hN β Δ) :
    BoxLocalGap hN β n (1 - Δ) := by
  intro j _ k x
  obtain ⟨δ, hδ, hpd⟩ := h j
  exact patch_gap_of_defect (torusForm hN β j) (torusForm_nonneg hN β j)
    (fun l => (LinearMap.id : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))
      →ₗ[ℝ] ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) - torusCondExp β (2 * j + 1) l)
    (fun l => selfAdj_id_sub (torusForm hN β j) (torusCondExp β (2 * j + 1) l)
      (torusCondExp_selfAdj hN β j l))
    (fun l => idem_id_sub (torusCondExp β (2 * j + 1) l) (torusCondExp_idem β (2 * j + 1) l))
    (boxWeight n) k (fun l => boxWeight_cases n k l) δ hδ x
    (fun l m hlm _ _ => hpd l m hlm x)

#print axioms boxLocalGap_of_pairDefect

/-- **The box check at defect at most `1/2`**: side `80`, gap `1 − Δ`
(`(40·80 − 36)/80² = 791/1600 < 1/2`).

DERIVED: `80` is the side with `40/(1/2) ≤ 80`; `1/2` is the defect bound; `1` is the gap at zero
defect; `0` is the excluded rank in `hN`. -/
theorem boxPatchGap_of_pairDefect_half (hN : N ≠ 0) {β Δ : ℝ} (h : BoxPairDefect hN β Δ)
    (hΔ : Δ ≤ 1 / 2) : BoxPatchGap hN β 80 (1 - Δ) :=
  ⟨by norm_num,
    threshold_lt_of_ge (by linarith) (by
      rw [div_le_iff₀ (by linarith)]
      push_cast
      linarith),
    boxLocalGap_of_pairDefect hN 80 h⟩

#print axioms boxPatchGap_of_pairDefect_half

/-- **The box check at any defect below `1`**: side `⌈40/(1 − Δ)⌉ + 2`, gap `1 − Δ`
(`threshold_lt_of_ge`, `Nat.le_ceil`).

DERIVED: `40` is the threshold's leading coefficient; `1` is the gap at zero defect; `0` is the
excluded rank in `hN`. CHOSEN: `+ 2` pads the side so that `2 ≤ n` holds by `omega`; the ceiling alone
is already at least `40` when `0 ≤ Δ`. -/
theorem boxPatchGap_of_pairDefect (hN : N ≠ 0) {β Δ : ℝ} (h : BoxPairDefect hN β Δ)
    (hΔ : Δ < 1) : BoxPatchGap hN β (⌈40 / (1 - Δ)⌉₊ + 2) (1 - Δ) := by
  have hγ : 0 < 1 - Δ := by linarith
  refine ⟨by omega, threshold_lt_of_ge hγ ?_, boxLocalGap_of_pairDefect hN _ h⟩
  push_cast
  linarith [Nat.le_ceil (40 / (1 - Δ))]

#print axioms boxPatchGap_of_pairDefect

/-- **The two-link correlation at extent index `j`**: for every two links `l ≠ m` and every `x`,
some `y` fixed by `E_l` and `E_m` has, for `f = x − y`,
`⟨E_l f, E_m f⟩ ≤ δ l m·(‖E_l f‖² + ‖E_m f‖²)/2` in `torusForm`. With `y` the conditional
expectation given every link but `l` and `m`, it is a bound on the correlation of the two link
variables under their joint conditional law.

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `2` is the halving; `0` is the excluded rank in `hN`. -/
def PairCorrAt (hN : N ≠ 0) (β : ℝ) (j : ℕ)
    (δ : WilsonHypercubic.Link 4 (2 * j + 1 + 1) → WilsonHypercubic.Link 4 (2 * j + 1 + 1) → ℝ) :
    Prop :=
  ∀ l m, l ≠ m → ∀ x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)),
    ∃ y : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)),
      torusCondExp β (2 * j + 1) l y = y ∧ torusCondExp β (2 * j + 1) m y = y ∧
      torusForm hN β j (torusCondExp β (2 * j + 1) l (x - y)) (torusCondExp β (2 * j + 1) m (x - y))
        ≤ δ l m * (torusForm hN β j (torusCondExp β (2 * j + 1) l (x - y))
              (torusCondExp β (2 * j + 1) l (x - y))
            + torusForm hN β j (torusCondExp β (2 * j + 1) m (x - y))
              (torusCondExp β (2 * j + 1) m (x - y))) / 2

/-- **The correlation bound gives the pair defect** (`pair_defect_of_corr` at `f = x − y`, with
`f − E_l f = x − E_l x`).

DERIVED: `0` and `1` bound the entries of `δ`; `0` is the excluded rank in `hN`; `2 * j + 1` is the odd torus
side and `+ 1` the link-index offset; `4` in `Link 4` is the spacetime dimension. -/
theorem pairDefectAt_of_pairCorrAt (hN : N ≠ 0) (β : ℝ) (j : ℕ)
    (δ : WilsonHypercubic.Link 4 (2 * j + 1 + 1) → WilsonHypercubic.Link 4 (2 * j + 1 + 1) → ℝ)
    (hδ0 : ∀ l m, 0 ≤ δ l m) (hδ1 : ∀ l m, δ l m ≤ 1) (h : PairCorrAt hN β j δ) :
    PairDefectAt hN β j δ := by
  intro l m hlm x
  obtain ⟨y, hyl, hym, hc⟩ := h l m hlm x
  have key := pair_defect_of_corr (torusForm hN β j) (torusForm_symm hN β j)
    (torusForm_nonneg hN β j) (torusCondExp β (2 * j + 1) l) (torusCondExp β (2 * j + 1) m)
    (torusCondExp_selfAdj hN β j l) (torusCondExp_selfAdj hN β j m)
    (torusCondExp_idem β (2 * j + 1) l) (torusCondExp_idem β (2 * j + 1) m)
    (hδ0 l m) (hδ1 l m) (x - y) hc
  have e1 : x - y - torusCondExp β (2 * j + 1) l (x - y) = x - torusCondExp β (2 * j + 1) l x := by
    rw [map_sub, hyl]
    abel
  have e2 : x - y - torusCondExp β (2 * j + 1) m (x - y) = x - torusCondExp β (2 * j + 1) m x := by
    rw [map_sub, hym]
    abel
  rw [e1, e2] at key
  exact key

#print axioms pairDefectAt_of_pairCorrAt

/-- **The two-link correlation of the box heat bath**: at every extent index a defect matrix with
row and column sums at most `Δ` and entries at most `1` satisfies `PairCorrAt`.

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family; `1`
bounds the entries; `0` is the excluded rank in `hN`. -/
def BoxPairCorr (hN : N ≠ 0) (β Δ : ℝ) : Prop :=
  ∀ j : ℕ, ∃ δ : WilsonHypercubic.Link 4 (2 * j + 1 + 1) → WilsonHypercubic.Link 4 (2 * j + 1 + 1) → ℝ,
    DefectMatrix δ Δ ∧ (∀ l m, δ l m ≤ 1) ∧ PairCorrAt hN β j δ

/-- `BoxPairCorr` gives `BoxPairDefect` (`pairDefectAt_of_pairCorrAt`).

DERIVED: `0` is the excluded rank in `hN`. -/
theorem boxPairDefect_of_pairCorr (hN : N ≠ 0) {β Δ : ℝ} (h : BoxPairCorr hN β Δ) :
    BoxPairDefect hN β Δ := by
  intro j
  obtain ⟨δ, hδ, h1, hc⟩ := h j
  exact ⟨δ, hδ, pairDefectAt_of_pairCorrAt hN β j δ hδ.1 h1 hc⟩

#print axioms boxPairDefect_of_pairCorr

/-- **At `β = 0` the two-link correlations vanish**: `PairCorrAt hN 0 j 0`, with `y = E_l E_m x`
(`torusCondExp_comm_zero`, `corr_zero_of_comm`).

DERIVED: `0` is the coupling and the defect; `0` is the excluded rank in `hN`. -/
theorem pairCorrAt_zero (hN : N ≠ 0) (j : ℕ) : PairCorrAt hN 0 j (fun _ _ => 0) := by
  intro l m hlm x
  refine ⟨torusCondExp 0 (2 * j + 1) l (torusCondExp 0 (2 * j + 1) m x),
    torusCondExp_idem 0 (2 * j + 1) l _, ?_, ?_⟩
  · rw [← torusCondExp_comm_zero (2 * j + 1) hlm (torusCondExp 0 (2 * j + 1) m x),
      torusCondExp_idem 0 (2 * j + 1) m x]
  · have h0 := corr_zero_of_comm (torusForm hN 0 j) (torusCondExp 0 (2 * j + 1) l)
      (torusCondExp 0 (2 * j + 1) m) (torusCondExp_selfAdj hN 0 j l)
      (torusCondExp_selfAdj hN 0 j m) (torusCondExp_idem 0 (2 * j + 1) l)
      (torusCondExp_idem 0 (2 * j + 1) m) (fun z => torusCondExp_comm_zero (2 * j + 1) hlm z) x
    rw [h0]
    simp

#print axioms pairCorrAt_zero

/-- **`BoxPairCorr` holds at `β = 0` with `Δ = 0`** (`pairCorrAt_zero`).

DERIVED: `0` is the coupling and the defect; `1` bounds the entries; `0` is the excluded rank in
`hN`. -/
theorem boxPairCorr_zero (hN : N ≠ 0) : BoxPairCorr hN 0 0 := fun j =>
  ⟨fun _ _ => 0, ⟨fun _ _ => le_refl 0, fun _ => by simp, fun _ => by simp⟩,
    fun _ _ => zero_le_one, pairCorrAt_zero hN j⟩

#print axioms boxPairCorr_zero

/-- **The two-link correlation linear in the coupling**: `BoxPairCorr hN β (C·β)` for every
`0 ≤ β ≤ β₁`.

DERIVED: `0` is the lower end of `β`; `0` is the excluded rank in `hN`. -/
def PairCorrLinear (hN : N ≠ 0) (C β₁ : ℝ) : Prop :=
  ∀ β : ℝ, 0 ≤ β → β ≤ β₁ → BoxPairCorr hN β (C * β)

/-- **The box check at small coupling from the linear correlation bound.** Under
`PairCorrLinear hN C β₁` with `0 < C`: for `0 ≤ β ≤ β₁` and `β ≤ 1/(2C)`,
`BoxPatchGap hN β 80 (1 − Cβ)` (`boxPairDefect_of_pairCorr`, `boxPatchGap_of_pairDefect_half`).

DERIVED: `80` is the side at defect at most `1/2`; `2` in `1/(2C)` puts `Cβ ≤ 1/2`; `1` is the gap
at zero defect; `0` is the sign of `C`, the lower end of `β` and the excluded rank in `hN`. -/
theorem boxPatchGap_of_pairCorrLinear (hN : N ≠ 0) {C β₁ β : ℝ} (h : PairCorrLinear hN C β₁)
    (hC : 0 < C) (hβ0 : 0 ≤ β) (hβ1 : β ≤ β₁) (hβC : β ≤ 1 / (2 * C)) :
    BoxPatchGap hN β 80 (1 - C * β) := by
  have h2 : β * (2 * C) ≤ 1 := (le_div_iff₀ (by linarith)).mp hβC
  exact boxPatchGap_of_pairDefect_half hN (boxPairDefect_of_pairCorr hN (h β hβ0 hβ1))
    (by nlinarith)

#print axioms boxPatchGap_of_pairCorrLinear

end PairRoute

/-! ## 6. One box under every boundary configuration -/

section Glue

variable {ι Ω : Type} [DecidableEq ι]

/-- **Gluing**: `V` on the links of `S`, `W` elsewhere.

DERIVED: no numeral. -/
def glue (S : Finset ι) (W V : ι → Ω) (i : ι) : Ω := if i ∈ S then V i else W i

/-- On `S` the glued configuration reads `V`.

DERIVED: no numeral. -/
theorem glue_of_mem {S : Finset ι} {W V : ι → Ω} {i : ι} (h : i ∈ S) : glue S W V i = V i :=
  if_pos h

#print axioms glue_of_mem

/-- Off `S` the glued configuration reads `W`.

DERIVED: no numeral. -/
theorem glue_of_not_mem {S : Finset ι} {W V : ι → Ω} {i : ι} (h : i ∉ S) : glue S W V i = W i :=
  if_neg h

#print axioms glue_of_not_mem

/-- **Updating a link of `S` stays in the fibre**: `glue S W (V[l ↦ g]) = (glue S W V)[l ↦ g]` for
`l ∈ S`.

DERIVED: no numeral. -/
theorem glue_update_of_mem (S : Finset ι) (W V : ι → Ω) {l : ι} (hl : l ∈ S) (g : Ω) :
    glue S W (Function.update V l g) = Function.update (glue S W V) l g := by
  funext i
  by_cases hi : i = l
  · subst hi
    rw [Function.update_self, glue_of_mem hl, Function.update_self]
  · rw [Function.update_of_ne hi]
    by_cases hS : i ∈ S
    · rw [glue_of_mem hS, glue_of_mem hS, Function.update_of_ne hi]
    · rw [glue_of_not_mem hS, glue_of_not_mem hS]

#print axioms glue_update_of_mem

end Glue

section GlueMeasure

variable {ι Ω : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

/-- Gluing is measurable in the pair.

DERIVED: no numeral. -/
theorem measurable_glue (S : Finset ι) :
    Measurable (fun p : (ι → Ω) × (ι → Ω) => glue S p.1 p.2) := by
  refine measurable_pi_lambda _ (fun i => ?_)
  show Measurable (fun p : (ι → Ω) × (ι → Ω) => glue S p.1 p.2 i)
  by_cases hi : i ∈ S
  · have e : (fun p : (ι → Ω) × (ι → Ω) => glue S p.1 p.2 i) = fun p => p.2 i :=
      funext fun p => glue_of_mem hi
    rw [e]
    exact (measurable_pi_apply i).comp measurable_snd
  · have e : (fun p : (ι → Ω) × (ι → Ω) => glue S p.1 p.2 i) = fun p => p.1 i :=
      funext fun p => glue_of_not_mem hi
    rw [e]
    exact (measurable_pi_apply i).comp measurable_fst

#print axioms measurable_glue

/-- **Gluing preserves the product measure.** For a probability measure `μ`, `(W, V) ↦ glue S W V`
carries `(Π μ) ⊗ (Π μ)` to `Π μ`: the preimage of a box `Π s_i` is the box with `univ` on `S`, times
the box with `univ` off `S` (`Measure.pi_eq`).

DERIVED: no numeral. -/
theorem measurePreserving_glue (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Finset ι) :
    MeasurePreserving (fun p : (ι → Ω) × (ι → Ω) => glue S p.1 p.2)
      ((Measure.pi fun _ : ι => μ).prod (Measure.pi fun _ : ι => μ))
      (Measure.pi fun _ : ι => μ) := by
  refine ⟨measurable_glue S, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hpre : (fun p : (ι → Ω) × (ι → Ω) => glue S p.1 p.2) ⁻¹' (Set.univ.pi s)
      = (Set.univ.pi (fun i => if i ∈ S then Set.univ else s i))
        ×ˢ (Set.univ.pi (fun i => if i ∈ S then s i else Set.univ)) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩
      · by_cases hi : i ∈ S
        · rw [if_pos hi]
          exact Set.mem_univ _
        · rw [if_neg hi]
          have h' := h i
          rwa [glue_of_not_mem hi] at h'
      · by_cases hi : i ∈ S
        · rw [if_pos hi]
          have h' := h i
          rwa [glue_of_mem hi] at h'
        · rw [if_neg hi]
          exact Set.mem_univ _
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i ∈ S
      · rw [glue_of_mem hi]
        have h' := h2 i
        rwa [if_pos hi] at h'
      · rw [glue_of_not_mem hi]
        have h' := h1 i
        rwa [if_neg hi] at h'
  rw [Measure.map_apply (measurable_glue S) (MeasurableSet.univ_pi hs), hpre, Measure.prod_prod,
    Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  by_cases hi : i ∈ S
  · rw [if_pos hi, if_pos hi, measure_univ, one_mul]
  · rw [if_neg hi, if_neg hi, measure_univ, mul_one]

#print axioms measurePreserving_glue

/-- **Integrating out the links of `S` with the rest frozen.** For a probability measure `μ` and a
bounded measurable `F`: `∫ F d(Π μ) = ∫ W, ∫ V, F (glue S W V) d(Π μ) d(Π μ)`
(`measurePreserving_glue`, `integral_map`, Fubini).

DERIVED: no numeral. -/
theorem integral_eq_integral_glue (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Finset ι)
    (F : (ι → Ω) → ℝ) (hF : Measurable F) {C : ℝ} (hC : ∀ W, |F W| ≤ C) :
    ∫ W, F W ∂(Measure.pi fun _ : ι => μ)
      = ∫ W, ∫ V, F (glue S W V) ∂(Measure.pi fun _ : ι => μ) ∂(Measure.pi fun _ : ι => μ) := by
  have hmp := measurePreserving_glue μ S
  have hint : Integrable (fun p : (ι → Ω) × (ι → Ω) => F (glue S p.1 p.2))
      ((Measure.pi fun _ : ι => μ).prod (Measure.pi fun _ : ι => μ)) :=
    integrable_of_abs_le _ (hF.comp (measurable_glue S)) (fun p => hC _)
  calc ∫ W, F W ∂(Measure.pi fun _ : ι => μ)
      = ∫ W, F W ∂(Measure.map (fun p : (ι → Ω) × (ι → Ω) => glue S p.1 p.2)
          ((Measure.pi fun _ : ι => μ).prod (Measure.pi fun _ : ι => μ))) := by rw [hmp.map_eq]
    _ = ∫ p, F (glue S p.1 p.2)
          ∂((Measure.pi fun _ : ι => μ).prod (Measure.pi fun _ : ι => μ)) :=
        integral_map hmp.measurable.aemeasurable hF.aestronglyMeasurable
    _ = ∫ W, ∫ V, F (glue S W V) ∂(Measure.pi fun _ : ι => μ) ∂(Measure.pi fun _ : ι => μ) :=
        integral_prod _ hint

#print axioms integral_eq_integral_glue

end GlueMeasure

section LocalWeight

variable {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq] [DecidableEq Lk]

/-- **The heat bath at a link of `S` acts in the fibre**: at `glue S W V` it averages over the
variable at `l` inside the fibre over `W` (`glue_update_of_mem`).

DERIVED: no numeral. -/
theorem heatAvg_glue (bd : Pq → List (Lk × Bool)) (β : ℝ) {S : Finset Lk} {l : Lk} (hl : l ∈ S)
    (f : (Lk → SU N) → ℝ) (W V : Lk → SU N) :
    heatAvg bd β l f (glue S W V)
      = (∫ g, f (glue S W (Function.update V l g)) * wt bd β (glue S W (Function.update V l g))
            ∂(probHaar (SU N)))
        / ∫ g, wt bd β (glue S W (Function.update V l g)) ∂(probHaar (SU N)) := by
  unfold heatAvg heatNum heatPart
  simp only [glue_update_of_mem S W V hl]

#print axioms heatAvg_glue

/-- The action of the plaquettes whose boundary word visits a link of `S`.

DERIVED: no numeral. -/
def boxLocSum (bd : Pq → List (Lk × Bool)) (S : Finset Lk) (W : Lk → SU N) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p => ∃ l ∈ S, l ∈ (bd p).map Prod.fst),
    wilsonDensity (wilsonHol bd p W)

/-- The action of the plaquettes whose boundary word visits no link of `S`.

DERIVED: no numeral. -/
def boxRestSum (bd : Pq → List (Lk × Bool)) (S : Finset Lk) (W : Lk → SU N) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p => ¬ ∃ l ∈ S, l ∈ (bd p).map Prod.fst),
    wilsonDensity (wilsonHol bd p W)

/-- **The local weight of `S`**: `e^{−β · boxLocSum}`, the weight of the plaquettes meeting `S`.

DERIVED: no numeral. -/
def locWt (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk) (W : Lk → SU N) : ℝ :=
  Real.exp (-β * boxLocSum bd S W)

/-- The action splits at `S` (`Finset.sum_filter_add_sum_filter_not`).

DERIVED: no numeral. -/
theorem action_split_set (bd : Pq → List (Lk × Bool)) (S : Finset Lk) (W : Lk → SU N) :
    (wilsonSystem bd (wilsonDensity (N := N))).action W = boxLocSum bd S W + boxRestSum bd S W := by
  show ∑ p, wilsonDensity (wilsonHol bd p W) = _
  unfold boxLocSum boxRestSum
  exact (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm

#print axioms action_split_set

/-- A plaquette meeting no link of `S` has the same holonomy at `glue S W V` as at `W`.

DERIVED: no numeral. -/
theorem wilsonHol_glue (bd : Pq → List (Lk × Bool)) (p : Pq) {S : Finset Lk}
    (hp : ¬ ∃ l ∈ S, l ∈ (bd p).map Prod.fst) (W V : Lk → SU N) :
    wilsonHol bd p (glue S W V) = wilsonHol bd p W := by
  unfold wilsonHol
  congr 1
  apply List.map_congr_left
  intro lo hlo
  have hne : lo.1 ∉ S := fun h => hp ⟨lo.1, h, List.mem_map.mpr ⟨lo, hlo, rfl⟩⟩
  simp only [glue_of_not_mem hne]

#print axioms wilsonHol_glue

/-- The rest of the action does not read the links of `S` (`wilsonHol_glue`).

DERIVED: no numeral. -/
theorem boxRestSum_glue (bd : Pq → List (Lk × Bool)) (S : Finset Lk) (W V : Lk → SU N) :
    boxRestSum bd S (glue S W V) = boxRestSum bd S W := by
  unfold boxRestSum
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [wilsonHol_glue bd p (Finset.mem_filter.mp hp).2 W V]

#print axioms boxRestSum_glue

/-- **The fibre weight factors**: `wt (glue S W V) = locWt S (glue S W V) · e^{−β · boxRestSum S W}`,
the second factor a constant of the boundary `W`.

DERIVED: no numeral. -/
theorem wt_glue (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk) (W V : Lk → SU N) :
    wt bd β (glue S W V) = locWt bd β S (glue S W V) * Real.exp (-β * boxRestSum bd S W) := by
  unfold wt locWt
  show Real.exp (-β * (wilsonSystem bd (wilsonDensity (N := N))).action (glue S W V : Lk → SU N)) = _
  rw [action_split_set bd S (glue S W V), mul_add, Real.exp_add, boxRestSum_glue bd S W V]

#print axioms wt_glue

/-- **The fibre inequality reads only the plaquettes meeting `S`.** For every boundary `W`, the
local-gap inequality between fibre integrals with the full weight holds exactly when it holds with
the local weight `locWt S` (`wt_glue`; the boundary factor is positive).

DERIVED: no numeral. -/
theorem fibre_iff_local (bd : Pq → List (Lk × Bool)) (β γ : ℝ) (S : Finset Lk)
    (F₁ F₂ : (Lk → SU N) → ℝ) (W : Lk → SU N) :
    (γ * ∫ V, F₁ (glue S W V) * wt bd β (glue S W V) ∂(Measure.pi fun _ : Lk => probHaar (SU N))
        ≤ ∫ V, F₂ (glue S W V) * wt bd β (glue S W V) ∂(Measure.pi fun _ : Lk => probHaar (SU N)))
      ↔ (γ * ∫ V, F₁ (glue S W V) * locWt bd β S (glue S W V)
            ∂(Measure.pi fun _ : Lk => probHaar (SU N))
        ≤ ∫ V, F₂ (glue S W V) * locWt bd β S (glue S W V)
            ∂(Measure.pi fun _ : Lk => probHaar (SU N))) := by
  have hint : ∀ F : (Lk → SU N) → ℝ,
      ∫ V, F (glue S W V) * wt bd β (glue S W V) ∂(Measure.pi fun _ : Lk => probHaar (SU N))
        = (∫ V, F (glue S W V) * locWt bd β S (glue S W V)
            ∂(Measure.pi fun _ : Lk => probHaar (SU N)))
          * Real.exp (-β * boxRestSum bd S W) := by
    intro F
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun V => ?_))
    show F (glue S W V) * wt bd β (glue S W V)
      = F (glue S W V) * locWt bd β S (glue S W V) * Real.exp (-β * boxRestSum bd S W)
    rw [wt_glue bd β S W V, mul_assoc]
  rw [hint F₁, hint F₂, ← mul_assoc]
  exact mul_le_mul_iff_of_pos_right (Real.exp_pos _)

#print axioms fibre_iff_local

end LocalWeight

section Fibre

variable {N : ℕ}

/-- **`torusForm` is the Gibbs integral** of the product of the torus readings, over the partition
function, by definition.

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `0` is the excluded rank in `hN`. -/
theorem torusForm_eq_integral (hN : N ≠ 0) (β : ℝ) (j : ℕ)
    (x y : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) :
    torusForm hN β j x y
      = (∫ W, torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) W
            * torusObs (2 * j + 1) (y : C(GibbsSpec.IConf (SU N), ℝ)) W
            * wt (bdT (2 * j + 1)) β W
          ∂(Measure.pi fun _ : WilsonHypercubic.Link 4 (2 * j + 1 + 1) => probHaar (SU N)))
        / (wilsonSystem (bdT (2 * j + 1)) (wilsonDensity (N := N))).partition
            (probHaar (SU N)) β :=
  rfl

#print axioms torusForm_eq_integral

/-- **The fibre inequality integrates.** For continuous `F₁`, `F₂` on the torus configurations and
a set of links `S`: if at every boundary `W` the fibre integrals over the links of `S` satisfy
`γ ∫ F₁ wt ≤ ∫ F₂ wt`, then so do the full Gibbs integrals (`integral_eq_integral_glue`,
`integral_mono`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem form_le_of_fibre {M : ℕ} (S : Finset (WilsonHypercubic.Link 4 (M + 1))) (β γ : ℝ)
    {F₁ F₂ : (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ} (h1 : Continuous F₁)
    (h2 : Continuous F₂)
    (hfib : ∀ W, γ * ∫ V, F₁ (glue S W V) * wt (bdT M) β (glue S W V)
          ∂(Measure.pi fun _ : WilsonHypercubic.Link 4 (M + 1) => probHaar (SU N))
        ≤ ∫ V, F₂ (glue S W V) * wt (bdT M) β (glue S W V)
          ∂(Measure.pi fun _ : WilsonHypercubic.Link 4 (M + 1) => probHaar (SU N))) :
    γ * ∫ W, F₁ W * wt (bdT M) β W
        ∂(Measure.pi fun _ : WilsonHypercubic.Link 4 (M + 1) => probHaar (SU N))
      ≤ ∫ W, F₂ W * wt (bdT M) β W
        ∂(Measure.pi fun _ : WilsonHypercubic.Link 4 (M + 1) => probHaar (SU N)) := by
  have hc1 : Continuous (fun W => F₁ W * wt (bdT M) β W) := h1.mul (continuous_wt (bdT M) β)
  have hc2 : Continuous (fun W => F₂ W * wt (bdT M) β W) := h2.mul (continuous_wt (bdT M) β)
  obtain ⟨C1, hC1⟩ := exists_abs_le hc1
  obtain ⟨C2, hC2⟩ := exists_abs_le hc2
  have hi1 : Integrable (fun p : (WilsonHypercubic.Link 4 (M + 1) → SU N)
        × (WilsonHypercubic.Link 4 (M + 1) → SU N) =>
      F₁ (glue S p.1 p.2) * wt (bdT M) β (glue S p.1 p.2))
      ((Measure.pi fun _ : WilsonHypercubic.Link 4 (M + 1) => probHaar (SU N)).prod
        (Measure.pi fun _ : WilsonHypercubic.Link 4 (M + 1) => probHaar (SU N))) :=
    integrable_of_abs_le _ (hc1.measurable.comp (measurable_glue S)) (fun p => hC1 _)
  have hi2 : Integrable (fun p : (WilsonHypercubic.Link 4 (M + 1) → SU N)
        × (WilsonHypercubic.Link 4 (M + 1) → SU N) =>
      F₂ (glue S p.1 p.2) * wt (bdT M) β (glue S p.1 p.2))
      ((Measure.pi fun _ : WilsonHypercubic.Link 4 (M + 1) => probHaar (SU N)).prod
        (Measure.pi fun _ : WilsonHypercubic.Link 4 (M + 1) => probHaar (SU N))) :=
    integrable_of_abs_le _ (hc2.measurable.comp (measurable_glue S)) (fun p => hC2 _)
  rw [integral_eq_integral_glue (probHaar (SU N)) S _ hc1.measurable hC1,
    integral_eq_integral_glue (probHaar (SU N)) S _ hc2.measurable hC2, ← integral_const_mul]
  exact integral_mono (hi1.integral_prod_left.const_mul γ) hi2.integral_prod_left
    (fun W => hfib W)

#print axioms form_le_of_fibre

/-- **The links of the box of side `n` at the corner `k`**: base site in the box.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
def boxLinks {M : ℕ} (n : ℕ) (k : WilsonHypercubic.Site 4 (M + 1)) :
    Finset (WilsonHypercubic.Link 4 (M + 1)) :=
  Finset.univ.filter (fun l => InBox n (l.2 - k))

/-- A link lies in `boxLinks n k` exactly when its box weight is `1`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent and the weight
value. -/
theorem mem_boxLinks_iff {M : ℕ} (n : ℕ) (k : WilsonHypercubic.Site 4 (M + 1))
    (l : WilsonHypercubic.Link 4 (M + 1)) : l ∈ boxLinks n k ↔ boxWeight n k l = 1 := by
  unfold boxLinks boxWeight
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨_, h⟩
    exact if_pos h
  · intro h
    refine ⟨Finset.mem_univ l, ?_⟩
    by_contra hn
    rw [if_neg hn] at h
    exact zero_ne_one h

#print axioms mem_boxLinks_iff

/-- **The box patch operator is the sum over the box's links** of `x − E_l x`.

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent. -/
theorem boxOp_apply (β : ℝ) (n j : ℕ) (k : WilsonHypercubic.Site 4 (2 * j + 1 + 1))
    (x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) :
    boxOp β n j k x = ∑ l ∈ boxLinks n k, (x - torusCondExp β (2 * j + 1) l x) := by
  unfold boxOp
  rw [patchOp_apply, boxLinks, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  unfold boxWeight
  split_ifs with h
  · rw [one_smul]
    rfl
  · rw [zero_smul]

#print axioms boxOp_apply

/-- **THE BOX CHECK AS ONE BOX UNDER EVERY BOUNDARY.** At every extent index `j` with `n ≤ j + 1`,
every corner `k`, every periodic gauge-invariant `x` and every boundary configuration `W`: with `V`
running over the configurations of the box's links (the rest frozen at `W`) and the weight of the
plaquettes meeting the box,
`γ ∫ (Ax)(x) locWt ≤ ∫ (Ax)(Ax) locWt`, `A = boxOp β n j k`, all read at `glue (boxLinks n k) W V`.

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `1` is the successor in `j + 1`; `0` is the excluded rank in
`hN`. -/
def BoxFibreGap (hN : N ≠ 0) (β : ℝ) (n : ℕ) (γ : ℝ) : Prop :=
  ∀ j : ℕ, n ≤ j + 1 → ∀ (k : WilsonHypercubic.Site 4 (2 * j + 1 + 1))
    (x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
    (W : WilsonHypercubic.Link 4 (2 * j + 1 + 1) → SU N),
    γ * ∫ V, torusObs (2 * j + 1)
          ((boxOp β n j k x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
            : C(GibbsSpec.IConf (SU N), ℝ)) (glue (boxLinks n k) W V)
        * torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) (glue (boxLinks n k) W V)
        * locWt (bdT (2 * j + 1)) β (boxLinks n k) (glue (boxLinks n k) W V)
        ∂(Measure.pi fun _ : WilsonHypercubic.Link 4 (2 * j + 1 + 1) => probHaar (SU N))
      ≤ ∫ V, torusObs (2 * j + 1)
          ((boxOp β n j k x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
            : C(GibbsSpec.IConf (SU N), ℝ)) (glue (boxLinks n k) W V)
        * torusObs (2 * j + 1)
          ((boxOp β n j k x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
            : C(GibbsSpec.IConf (SU N), ℝ)) (glue (boxLinks n k) W V)
        * locWt (bdT (2 * j + 1)) β (boxLinks n k) (glue (boxLinks n k) W V)
        ∂(Measure.pi fun _ : WilsonHypercubic.Link 4 (2 * j + 1 + 1) => probHaar (SU N))

/-- **The one-box check gives the box-patch local gap** (`torusForm_eq_integral`,
`fibre_iff_local`, `form_le_of_fibre`, `WilsonReal.wilsonSystem_partition_pos`).

DERIVED: `0` is the excluded rank in `hN` and the sign of the partition function. -/
theorem boxLocalGap_of_fibreGap (hN : N ≠ 0) {β : ℝ} {n : ℕ} {γ : ℝ}
    (h : BoxFibreGap hN β n γ) : BoxLocalGap hN β n γ := by
  intro j hj k x
  have hZ := MassGap.WilsonReal.wilsonSystem_partition_pos hN (bdT (2 * j + 1)) β
  rw [torusForm_eq_integral, torusForm_eq_integral, ← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ hZ.le
  refine form_le_of_fibre (boxLinks n k) β γ
    (F₁ := fun W => torusObs (2 * j + 1)
      ((boxOp β n j k x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
        : C(GibbsSpec.IConf (SU N), ℝ)) W
      * torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) W)
    (F₂ := fun W => torusObs (2 * j + 1)
      ((boxOp β n j k x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
        : C(GibbsSpec.IConf (SU N), ℝ)) W
      * torusObs (2 * j + 1)
        ((boxOp β n j k x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
          : C(GibbsSpec.IConf (SU N), ℝ)) W)
    ((continuous_torusObs _ _).mul (continuous_torusObs _ _))
    ((continuous_torusObs _ _).mul (continuous_torusObs _ _)) (fun W => ?_)
  exact (fibre_iff_local (bdT (2 * j + 1)) β γ (boxLinks n k)
    (fun W => torusObs (2 * j + 1)
      ((boxOp β n j k x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
        : C(GibbsSpec.IConf (SU N), ℝ)) W
      * torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) W)
    (fun W => torusObs (2 * j + 1)
      ((boxOp β n j k x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
        : C(GibbsSpec.IConf (SU N), ℝ)) W
      * torusObs (2 * j + 1)
        ((boxOp β n j k x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
          : C(GibbsSpec.IConf (SU N), ℝ)) W) W).mpr (h j hj k x W)

#print axioms boxLocalGap_of_fibreGap

/-- **The box check from one box under every boundary**: `2 ≤ n`, `γ > (40n − 36)/n²` and
`BoxFibreGap hN β n γ` give `BoxPatch.BoxPatchGap hN β n γ`.

DERIVED: `2` is the least side with `b > 0` and the exponent; `40`, `36` are the threshold's
coefficients; `0` is the excluded rank in `hN`. -/
theorem boxPatchGap_of_fibreGap (hN : N ≠ 0) {β : ℝ} {n : ℕ} {γ : ℝ} (hn : 2 ≤ n)
    (hγ : (40 * (n : ℝ) - 36) / (n : ℝ) ^ 2 < γ) (h : BoxFibreGap hN β n γ) :
    BoxPatchGap hN β n γ :=
  ⟨hn, hγ, boxLocalGap_of_fibreGap hN h⟩

#print axioms boxPatchGap_of_fibreGap

end Fibre

/-! ## 7. Self-adjointness of the box operator -/

section ReadBox

variable {N : ℕ}

/-- The box patch operator is `torusForm`-self-adjoint (`patchOp_selfAdj`).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `0` is the excluded rank in `hN`. -/
theorem boxOp_selfAdj (hN : N ≠ 0) (β : ℝ) (n j : ℕ) (k : WilsonHypercubic.Site 4 (2 * j + 1 + 1))
    (x y : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) :
    torusForm hN β j (boxOp β n j k x) y = torusForm hN β j x (boxOp β n j k y) :=
  patchOp_selfAdj (torusForm hN β j)
    (fun l => (LinearMap.id : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))
      →ₗ[ℝ] ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) - torusCondExp β (2 * j + 1) l)
    (fun l => selfAdj_id_sub (torusForm hN β j) (torusCondExp β (2 * j + 1) l)
      (torusCondExp_selfAdj hN β j l))
    (boxWeight n) k x y

#print axioms boxOp_selfAdj

end ReadBox

end MassGap.BoxGap
