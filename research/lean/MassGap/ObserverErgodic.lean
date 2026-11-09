import Mathlib
import MassGap.PotKnabe
import MassGap.WeightedErgodic

noncomputable section

/-!
# MassGap.ObserverErgodic — clustering of the observer theories with the ergodic limit discharged

`ObserverKnabe.obs_cluster` and `PotKnabe.pot_cluster` take the ergodic limit of the lazy heat bath
as a hypothesis. `WeightedErgodic.wTorus_poincare` gives the finite-volume Poincaré inequality of
any torus weight, and `RestoreShims.ergodicLimit_of_poincare` then identifies the limit as the
product of the means (`obs_ergodic`, `pot_ergodic`), as `HeatBathLocal.ergodicLimit_wilson` does for
Wilson. The clustering bounds follow with no hypothesis beyond the coupling box
(`obs_cluster_full`, `pot_cluster_full`): the deviation of `B(f, g)` from `μ(f) μ(g)`.
-/

namespace MassGap.ObserverErgodic

open Filter
open MassGap.KnabeCriterion (PatchSystem)
open MassGap.HeatBathGapDecay (ErgodicLimit Kc Far nrm cov_bound_exp H_form_le_card)
open MassGap.HeatBathErgodic (ergodicLimit_of_poincare form_H_eq_sum form_H_left_zero)
open MassGap.WeightedErgodic (oneW wTorus_poincare_H wForm_one_one wCondExp_one)
open MassGap.WeightedTorus (wForm)
open MassGap.ObserverBox (adjWeight)
open MassGap.ObserverKnabe (obsSys obsNb obs_globalGap adj_hcomm card_near2_le Near2)
open MassGap.LocalPotential (LocalPotFam potWeight)
open MassGap.PotKnabe (potSys pot_globalGap pot_globalGap_wide pot_hcomm)

set_option maxHeartbeats 1000000 in
/-- **The ergodic limit of the observer theory's heat bath**: `B(Tᴹ f, g) → μ(f) μ(g)` at
`K = |ι| + 1`, with `μ(x) = wForm(x, 1)`.

DERIVED: `2` is the rank; `100000` is the box side; `1` is the constant. -/
theorem obs_ergodic (β lam : ℝ) (j : ℕ) (hj : 100000 ≤ j + 1) (f g : (obsSys β lam j hj).E) :
    ErgodicLimit (obsSys β lam j hj) f g
      ((obsSys β lam j hj).B f (oneW j) * (obsSys β lam j hj).B g (oneW j)) := by
  obtain ⟨C, hC0, hC⟩ := wTorus_poincare_H (adjWeight (N := 2) β lam) j
  refine ergodicLimit_of_poincare (obsSys β lam j hj) (oneW j) (wForm_one_one _ j)
    (fun v => form_H_left_zero (obsSys β lam j hj) (oneW j) (fun l => ?_) v) hC0 (fun v => ?_) f g rfl
  · show wForm (adjWeight β lam) j (oneW j - _) (oneW j - _) = 0
    rw [wCondExp_one, sub_self, map_zero]
  · rw [form_H_eq_sum]
    exact hC v

#print axioms obs_ergodic

set_option maxHeartbeats 1000000 in
/-- **The ergodic limit of Wilson times a local potential.**

DERIVED: as `obs_ergodic`, at box side `300000`. -/
theorem pot_ergodic (β : ℝ) (F : LocalPotFam 2)
    (hdiam : ∀ M X a b, a ∈ (F.P M).supp X → b ∈ (F.P M).supp X → Near2 (b.2 - a.2))
    (j : ℕ) (hj : 300000 ≤ j + 1) (f g : (potSys β F hdiam j hj).E) :
    ErgodicLimit (potSys β F hdiam j hj) f g
      ((potSys β F hdiam j hj).B f (oneW j) * (potSys β F hdiam j hj).B g (oneW j)) := by
  obtain ⟨C, hC0, hC⟩ := wTorus_poincare_H (potWeight (N := 2) β F) j
  refine ergodicLimit_of_poincare (potSys β F hdiam j hj) (oneW j) (wForm_one_one _ j)
    (fun v => form_H_left_zero (potSys β F hdiam j hj) (oneW j) (fun l => ?_) v) hC0 (fun v => ?_)
    f g rfl
  · show wForm (potWeight β F) j (oneW j - _) (oneW j - _) = 0
    rw [wCondExp_one, sub_self, map_zero]
  · rw [form_H_eq_sum]
    exact hC v

#print axioms pot_ergodic

/-- The Lipschitz bound of `H` at `K = |ι| + 1` (`HeatBathGapDecay.H_form_le_card`).

DERIVED: `1` is the shift. -/
theorem H_form_le_Kc (S : PatchSystem) (v : S.E) :
    S.B (S.H v) (S.H v) ≤ ((Kc S : ℕ) : ℝ) * S.B (S.H v) v := by
  have h1 := H_form_le_card S v
  have h2 := S.H_form_nonneg v
  have e : ((Kc S : ℕ) : ℝ) = (Fintype.card S.ι : ℝ) + 1 := by
    unfold Kc
    exact Nat.cast_succ _
  rw [e]
  nlinarith

#print axioms H_form_le_Kc

set_option maxHeartbeats 1000000 in
/-- **Exponential clustering of the observer theory, unconditional**: SU(2), `β ≤ 1/200`,
`|λ| ≤ 1/20000`; for `f` read on `A`, `g` read on `C` at neighbour level `k`,
`|⟨f g⟩ − ⟨f⟩⟨g⟩| ≤ s |C| ‖f‖ y⁻ᵏ e^{2 · 5184 y s} ‖g‖ + 20 e^{−s/20} |A| ‖f‖ ‖g‖`
(`HeatBathGapDecay.cov_bound_exp` at `K = |ι| + 1`, `obs_globalGap`, `obs_ergodic`).

DERIVED: `5184` is `card_near2_le`'s bound; `1/10` is the gap; `100000` is the box side; `2` is
the rank; Inherited: `1/200`, `1/20000` the coupling bounds of `ObserverKnabe.obs_globalGap`. -/
theorem obs_cluster_full {β lam : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 200) (hl : |lam| ≤ 1 / 20000)
    (j : ℕ) (hj : 100000 ≤ j + 1)
    (A C : Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1))) (f g : (obsSys β lam j hj).E)
    (hf : ∀ l, l ∉ A → (obsSys β lam j hj).B ((obsSys β lam j hj).h l f)
      ((obsSys β lam j hj).h l f) = 0)
    (hg : ∀ l, l ∉ C → (obsSys β lam j hj).B ((obsSys β lam j hj).h l g)
      ((obsSys β lam j hj).h l g) = 0)
    (k : ℕ) (hfar : ∀ l ∈ C, Far (obsNb (2 * j + 1)) A k l) {y : ℝ} (hy : 1 ≤ y) (s : ℕ) :
    |(obsSys β lam j hj).B f g
        - (obsSys β lam j hj).B f (oneW j) * (obsSys β lam j hj).B g (oneW j)|
      ≤ s * C.card * (nrm (obsSys β lam j hj) f
          * ((y⁻¹) ^ k * Real.exp (2 * (5184 : ℕ) * y * s))) * nrm (obsSys β lam j hj) g
        + 2 / (1 / 10) * Real.exp (-(1 / 10 * s / 2))
          * (A.card * nrm (obsSys β lam j hj) f) * nrm (obsSys β lam j hj) g := by
  have hKn : 0 < Kc (obsSys β lam j hj) := Nat.succ_pos _
  have hc1 : (1 / 10 : ℝ) ≤ ((Kc (obsSys β lam j hj) : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((Kc (obsSys β lam j hj) : ℕ) : ℝ) := by exact_mod_cast hKn
    linarith
  exact cov_bound_exp _ hKn (H_form_le_Kc _) (by norm_num) hc1 (obs_globalGap hβ0 hβ hl j hj)
    (obsNb (2 * j + 1)) (fun l => card_near2_le l) (adj_hcomm β lam j hj) hy A C f g hf hg k hfar
    (obs_ergodic β lam j hj f g) s

#print axioms obs_cluster_full

set_option maxHeartbeats 1000000 in
/-- **Exponential clustering of Wilson times a local potential, unconditional**: SU(2), `β ≤ 1/200`,
local norm `≤ 1/5`, supports within two steps (`cov_bound_exp`, `pot_globalGap`, `pot_ergodic`).

DERIVED: as `obs_cluster_full`, at box side `300000`; Inherited: `1/200`, `1/5` the coupling and
local-norm bounds of `PotKnabe.pot_globalGap`. -/
theorem pot_cluster_full {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 200) (F : LocalPotFam 2)
    (hν : ∀ M l, (F.P M).norm l ≤ 1 / 5)
    (hdiam : ∀ M X a b, a ∈ (F.P M).supp X → b ∈ (F.P M).supp X → Near2 (b.2 - a.2))
    (j : ℕ) (hj : 300000 ≤ j + 1)
    (A C : Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1))) (f g : (potSys β F hdiam j hj).E)
    (hf : ∀ l, l ∉ A → (potSys β F hdiam j hj).B ((potSys β F hdiam j hj).h l f)
      ((potSys β F hdiam j hj).h l f) = 0)
    (hg : ∀ l, l ∉ C → (potSys β F hdiam j hj).B ((potSys β F hdiam j hj).h l g)
      ((potSys β F hdiam j hj).h l g) = 0)
    (k : ℕ) (hfar : ∀ l ∈ C, Far (obsNb (2 * j + 1)) A k l) {y : ℝ} (hy : 1 ≤ y) (s : ℕ) :
    |(potSys β F hdiam j hj).B f g
        - (potSys β F hdiam j hj).B f (oneW j) * (potSys β F hdiam j hj).B g (oneW j)|
      ≤ s * C.card * (nrm (potSys β F hdiam j hj) f
          * ((y⁻¹) ^ k * Real.exp (2 * (5184 : ℕ) * y * s))) * nrm (potSys β F hdiam j hj) g
        + 2 / (1 / 10) * Real.exp (-(1 / 10 * s / 2))
          * (A.card * nrm (potSys β F hdiam j hj) f) * nrm (potSys β F hdiam j hj) g := by
  have hKn : 0 < Kc (potSys β F hdiam j hj) := Nat.succ_pos _
  have hc1 : (1 / 10 : ℝ) ≤ ((Kc (potSys β F hdiam j hj) : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((Kc (potSys β F hdiam j hj) : ℕ) : ℝ) := by exact_mod_cast hKn
    linarith
  exact cov_bound_exp _ hKn (H_form_le_Kc _) (by norm_num) hc1
    (pot_globalGap hβ0 hβ F hν hdiam j hj) (obsNb (2 * j + 1)) (fun l => card_near2_le l)
    (pot_hcomm β F hdiam j hj) hy A C f g hf hg k hfar (pot_ergodic β F hdiam j hj f g) s

#print axioms pot_cluster_full

set_option maxHeartbeats 1000000 in
/-- **Exponential clustering on the wide box, unconditional**: SU(2), `β ≤ 1/40`,
local norm `≤ 1/8`, supports within two steps (`cov_bound_exp`, `pot_globalGap`, `pot_ergodic`).

DERIVED: as `obs_cluster_full`, at box side `300000`; Inherited: `1/40`, `1/8` the coupling and
local-norm bounds of `PotKnabe.pot_globalGap_wide`. -/
theorem pot_cluster_full_wide {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 40) (F : LocalPotFam 2)
    (hν : ∀ M l, (F.P M).norm l ≤ 1 / 8)
    (hdiam : ∀ M X a b, a ∈ (F.P M).supp X → b ∈ (F.P M).supp X → Near2 (b.2 - a.2))
    (j : ℕ) (hj : 300000 ≤ j + 1)
    (A C : Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1))) (f g : (potSys β F hdiam j hj).E)
    (hf : ∀ l, l ∉ A → (potSys β F hdiam j hj).B ((potSys β F hdiam j hj).h l f)
      ((potSys β F hdiam j hj).h l f) = 0)
    (hg : ∀ l, l ∉ C → (potSys β F hdiam j hj).B ((potSys β F hdiam j hj).h l g)
      ((potSys β F hdiam j hj).h l g) = 0)
    (k : ℕ) (hfar : ∀ l ∈ C, Far (obsNb (2 * j + 1)) A k l) {y : ℝ} (hy : 1 ≤ y) (s : ℕ) :
    |(potSys β F hdiam j hj).B f g
        - (potSys β F hdiam j hj).B f (oneW j) * (potSys β F hdiam j hj).B g (oneW j)|
      ≤ s * C.card * (nrm (potSys β F hdiam j hj) f
          * ((y⁻¹) ^ k * Real.exp (2 * (5184 : ℕ) * y * s))) * nrm (potSys β F hdiam j hj) g
        + 2 / (1 / 10) * Real.exp (-(1 / 10 * s / 2))
          * (A.card * nrm (potSys β F hdiam j hj) f) * nrm (potSys β F hdiam j hj) g := by
  have hKn : 0 < Kc (potSys β F hdiam j hj) := Nat.succ_pos _
  have hc1 : (1 / 10 : ℝ) ≤ ((Kc (potSys β F hdiam j hj) : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((Kc (potSys β F hdiam j hj) : ℕ) : ℝ) := by exact_mod_cast hKn
    linarith
  exact cov_bound_exp _ hKn (H_form_le_Kc _) (by norm_num) hc1
    (pot_globalGap_wide hβ0 hβ F hν hdiam j hj) (obsNb (2 * j + 1)) (fun l => card_near2_le l)
    (pot_hcomm β F hdiam j hj) hy A C f g hf hg k hfar (pot_ergodic β F hdiam j hj f g) s

#print axioms pot_cluster_full_wide

end MassGap.ObserverErgodic
