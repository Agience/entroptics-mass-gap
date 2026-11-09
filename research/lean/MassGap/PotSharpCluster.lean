import Mathlib
import MassGap.LocalPotentialSharp
import MassGap.ObserverErgodic

/-!
# MassGap.PotSharpCluster — the global gap and clustering on the sharp potential box

`LocalPotentialSharp.potBox_localGap_sharp` gives Wilson at `β ≤ 1/20` (`β_std ≤ 1/10`) times a local
potential of local norm `≤ 1/16` the local gap `213/1000`. On the box patch system of side `300000`
(`PotKnabe.potSys`) the Knabe criterion turns it into the global gap `7/100` (`pot_globalGap_sharp`),
and with the ergodic limit (`ObserverErgodic.pot_ergodic`) into exponential clustering, uniform in the
volume, with no hypothesis beyond the box (`pot_cluster_full_sharp`).
-/

namespace MassGap.PotSharpCluster

open MassGap.KnabeCriterion (PatchSystem)
open MassGap.HeatBathGapDecay (Kc Far nrm cov_bound_exp)
open MassGap.WeightedErgodic (oneW)
open MassGap.ObserverKnabe (obsNb card_near2_le Near2)
open MassGap.LocalPotential (LocalPotFam)
open MassGap.PotKnabe (potSys potPatchSystem two_le_potSide pot_hcomm)
open MassGap.ObserverErgodic (pot_ergodic H_form_le_Kc)
open MassGap.BoxPatch (bR bR_pos)

/-- **The global gap on the sharp box**: `SU(2)`, `β ≤ 1/20`, local norm `≤ 1/16`, supports within two
steps. At box side `300000` and every extent index `j` with `300000 ≤ j + 1` the heat-bath dynamics has
global gap `7/100` (Knabe constant `0.07475…`, `PatchSystem.globalGap_of_localGap`).

DERIVED: `2` is the rank; `300000` the box side; `5184` the two-step window count
(`ObserverKnabe.card_near2_le`); `213/1000` the local gap; `7/100` rounds `0.07475…` down; `1/20`,
`1/16` the coupling and local-norm box of `LocalPotentialSharp.potBox_localGap_sharp`. -/
theorem pot_globalGap_sharp {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 20) (F : LocalPotFam 2)
    (hν : ∀ M l, (F.P M).norm l ≤ 1 / 16)
    (hdiam : ∀ M X a b, a ∈ (F.P M).supp X → b ∈ (F.P M).supp X → Near2 (b.2 - a.2))
    (j : ℕ) (hj : 300000 ≤ j + 1) :
    (potPatchSystem (N := 2) β F hdiam 300000 j two_le_potSide hj).GlobalGap (7 / 100) := by
  have hb : 0 < (potPatchSystem (N := 2) β F hdiam 300000 j two_le_potSide hj).b := bR_pos (by norm_num)
  have hloc : (potPatchSystem (N := 2) β F hdiam 300000 j two_le_potSide hj).LocalGap (213 / 1000) :=
    fun k x => MassGap.LocalPotentialSharp.potBox_localGap_sharp hβ0 hβ F hν 300000 j hj k x
  refine (potPatchSystem (N := 2) β F hdiam 300000 j two_le_potSide hj).globalGap_mono ?_
    ((potPatchSystem (N := 2) β F hdiam 300000 j two_le_potSide hj).globalGap_of_localGap hb hloc)
  show (7 : ℝ) / 100 ≤ (213 / 1000 * ((300000 : ℕ) : ℝ) ^ 4 - ((300000 : ℕ) : ℝ) ^ 4 + bR 300000
    - 5184 * (((300000 : ℕ) : ℝ) ^ 4 - (((300000 : ℕ) : ℝ) - 2) ^ 4)) / bR 300000
  unfold bR
  norm_num

#print axioms pot_globalGap_sharp

set_option maxHeartbeats 1000000 in
/-- **Exponential clustering on the sharp box, unconditional**: `SU(2)`, `β ≤ 1/20` (`β_std ≤ 1/10`),
local norm `≤ 1/16`, supports within two steps (`HeatBathGapDecay.cov_bound_exp`,
`pot_globalGap_sharp`, `ObserverErgodic.pot_ergodic`). Uniform in the volume.

DERIVED: as `ObserverErgodic.pot_cluster_full_wide`, at global gap `7/100`; `5184` the window count;
`2` from `cov_bound_exp`; `300000` the box side, `1/20`, `1/16` the box, as in `pot_globalGap_sharp`. -/
theorem pot_cluster_full_sharp {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 20) (F : LocalPotFam 2)
    (hν : ∀ M l, (F.P M).norm l ≤ 1 / 16)
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
        + 2 / (7 / 100) * Real.exp (-(7 / 100 * s / 2))
          * (A.card * nrm (potSys β F hdiam j hj) f) * nrm (potSys β F hdiam j hj) g := by
  have hKn : 0 < Kc (potSys β F hdiam j hj) := Nat.succ_pos _
  have hc1 : (7 / 100 : ℝ) ≤ ((Kc (potSys β F hdiam j hj) : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((Kc (potSys β F hdiam j hj) : ℕ) : ℝ) := by exact_mod_cast hKn
    linarith
  exact cov_bound_exp _ hKn (H_form_le_Kc _) (by norm_num) hc1
    (pot_globalGap_sharp hβ0 hβ F hν hdiam j hj) (obsNb (2 * j + 1)) (fun l => card_near2_le l)
    (pot_hcomm β F hdiam j hj) hy A C f g hf hg k hfar (pot_ergodic β F hdiam j hj f g) s

#print axioms pot_cluster_full_sharp

end MassGap.PotSharpCluster
