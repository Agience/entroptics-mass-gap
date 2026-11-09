import Mathlib
import MassGap.HeatBathErgodic
import MassGap.WeightedTorus

noncomputable section

/-!
# MassGap.WeightedErgodic — the finite-volume Poincaré inequality of a bounded positive weight

`HeatBathErgodic.heat_poincare` for an arbitrary continuous weight `Φ` with `wlo ≤ Φ ≤ whi`,
`0 < wlo`: the proof reads the Wilson weight only through those bounds (`wt_bounds`), so the same
comparison with the product Haar measure and the same sweep give
`⟨φ²⟩_Φ − ⟨φ⟩_Φ² ≤ C Σ_l ⟨(φ − wAvg Φ l φ)²⟩_Φ` with `C = 2^{|L|+1} whi/wlo` (`w_poincare`). With
`RestoreShims.ergodicLimit_of_poincare` it identifies the ergodic limit of the heat bath of any
such weight, as `HeatBathLocal` does for Wilson.
-/

namespace MassGap.WeightedErgodic

open MeasureTheory Filter
open MassGap.SUN (SU)
open MassGap.CompactGauge (probHaar)
open MassGap.HeatBathErgodic (piHaar haar_integrable havg sweep sweep_readsNot eq_of_readsNot_all
  integral_sweep sweep_energy havg_integral_min var_le_of chain_le)
open MassGap.WeightedHeatBath (wAvg wAvg_update continuous_wAvg)
open MassGap.WeightedTorus (wExpect integral_pos_weight)

variable {N : ℕ} {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- **The Poincaré inequality of a bounded positive weight**: for continuous `Φ` with
`wlo ≤ Φ ≤ whi`, `0 < wlo`, there is `C ≥ 0` with
`⟨φ²⟩ − ⟨φ⟩² ≤ C Σ_l ⟨(φ − wAvg Φ l φ)²⟩` for every continuous `φ` (the proof of
`HeatBathErgodic.heat_poincare` with the bounds as hypotheses).

DERIVED: `0` is the sign of `C` and of `wlo`; `2` is the square and the base of the sweep
constant; `1` is the sweep's extra factor. -/
theorem w_poincare {Φ : (Lk → SU N) → ℝ} (hcont : Continuous Φ) {wlo whi : ℝ} (hwlo0 : 0 < wlo)
    (hwb : ∀ W : Lk → SU N, wlo ≤ Φ W ∧ Φ W ≤ whi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : (Lk → SU N) → ℝ, Continuous φ →
      wExpect Φ (fun W => φ W * φ W) - wExpect Φ φ ^ 2
        ≤ C * ∑ l, wExpect Φ (fun W => (φ W - wAvg Φ l φ W) ^ 2) := by
  have hpos : ∀ W, 0 < Φ W := fun W => lt_of_lt_of_le hwlo0 (hwb W).1
  have hwhi0 : 0 < whi := lt_of_lt_of_le (hpos fun _ => 1) (hwb fun _ => 1).2
  obtain ⟨L0, hL0⟩ : ∃ L : List Lk, L = (Finset.univ : Finset Lk).toList := ⟨_, rfl⟩
  have hmem : ∀ l, l ∈ L0 := fun l => by
    rw [hL0]
    exact Finset.mem_toList.mpr (Finset.mem_univ l)
  obtain ⟨K2, hK2⟩ : ∃ K : ℝ, K = (2 : ℝ) ^ (L0.length + 1) := ⟨_, rfl⟩
  have hK20 : 0 ≤ K2 := by
    rw [hK2]
    positivity
  refine ⟨K2 * (whi / wlo), mul_nonneg hK20 (div_nonneg hwhi0.le hwlo0.le), fun φ hφ => ?_⟩
  have hZ : 0 < ∫ W, Φ W ∂(piHaar N Lk) :=
    integral_pos_weight hpos hcont
  have hE : ∀ O : (Lk → SU N) → ℝ,
      wExpect Φ O
        = (∫ W, O W * Φ W ∂(piHaar N Lk)) / ∫ W, Φ W ∂(piHaar N Lk) :=
    fun O => rfl
  have hcw : Continuous (Φ) := hcont
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∫ W, φ W ∂(piHaar N Lk) := ⟨_, rfl⟩
  -- (a) the variance against the centred square
  have iφ : Integrable (fun W => φ W * Φ W) (piHaar N Lk) :=
    haar_integrable (hφ.mul hcw)
  have iφφ : Integrable (fun W => φ W * φ W * Φ W) (piHaar N Lk) :=
    haar_integrable ((hφ.mul hφ).mul hcw)
  have iw : Integrable (fun W => Φ W) (piHaar N Lk) := haar_integrable hcw
  have i2c : Integrable (fun W => 2 * c * (φ W * Φ W)) (piHaar N Lk) :=
    iφ.const_mul (2 * c)
  have i1 : Integrable (fun W => φ W * φ W * Φ W - 2 * c * (φ W * Φ W))
      (piHaar N Lk) := iφφ.sub i2c
  have icw : Integrable (fun W => c ^ 2 * Φ W) (piHaar N Lk) := iw.const_mul (c ^ 2)
  have hA : ∫ W, (φ W - c) ^ 2 * Φ W ∂(piHaar N Lk)
      = ∫ W, φ W * φ W * Φ W ∂(piHaar N Lk)
          - 2 * c * ∫ W, φ W * Φ W ∂(piHaar N Lk)
        + c ^ 2 * ∫ W, Φ W ∂(piHaar N Lk) := by
    have e : (fun W => (φ W - c) ^ 2 * Φ W)
        = fun W => (φ W * φ W * Φ W - 2 * c * (φ W * Φ W)) + c ^ 2 * Φ W := by
      funext W
      ring
    rw [e, integral_add i1 icw, integral_sub iφφ i2c, integral_const_mul, integral_const_mul]
  have hVar : wExpect Φ
        (fun W => φ W * φ W)
        - wExpect Φ φ ^ 2
      ≤ (∫ W, (φ W - c) ^ 2 * Φ W ∂(piHaar N Lk)) / ∫ W, Φ W ∂(piHaar N Lk) := by
    rw [hE, hE]
    exact var_le_of hZ hA
  -- (b) the weight against the Haar measure, from above
  have hB : ∫ W, (φ W - c) ^ 2 * Φ W ∂(piHaar N Lk)
      ≤ whi * ∫ W, (φ W - c) ^ 2 ∂(piHaar N Lk) := by
    rw [← integral_const_mul]
    refine integral_mono (haar_integrable (((hφ.sub continuous_const).pow 2).mul hcw))
      (haar_integrable (continuous_const.mul ((hφ.sub continuous_const).pow 2)))
      (fun W => ?_)
    have h1 := (hwb W).2
    have h2 := sq_nonneg (φ W - c)
    show (φ W - c) ^ 2 * Φ W ≤ whi * (φ W - c) ^ 2
    nlinarith
  -- (c) the sweep
  have hread : ∀ l W g, sweep L0 φ (Function.update W l g) = sweep L0 φ W :=
    fun l => sweep_readsNot φ L0 l (hmem l)
  have hconst : ∀ W, sweep L0 φ W = c := by
    intro W
    have h1 : ∫ V, sweep L0 φ V ∂(piHaar N Lk) = ∫ _V, sweep L0 φ W ∂(piHaar N Lk) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun V => eq_of_readsNot_all hread V W))
    rw [integral_const, probReal_univ, one_smul, integral_sweep hφ L0, ← hc] at h1
    exact h1.symm
  have hJ : ∫ W, (φ W - c) ^ 2 ∂(piHaar N Lk)
      ≤ K2 * ∑ l, ∫ W, (φ W - havg l φ W) ^ 2 ∂(piHaar N Lk) := by
    have hS := sweep_energy hφ L0
    have hS0 : 0 ≤ ∑ l, ∫ W, (φ W - havg l φ W) ^ 2 ∂(piHaar N Lk) :=
      Finset.sum_nonneg (fun l _ => integral_nonneg (fun W => sq_nonneg _))
    have e : (fun W => (φ W - c) ^ 2) = fun W => (φ W - sweep L0 φ W) ^ 2 := by
      funext W
      rw [hconst W]
    rw [e, hK2]
    nlinarith [hS, hS0]
  -- (d) the Haar defect against the heat-bath defect
  have hD : ∀ l, ∫ W, (φ W - havg l φ W) ^ 2 ∂(piHaar N Lk)
      ≤ ∫ W, (φ W - wAvg Φ l φ W) ^ 2 ∂(piHaar N Lk) :=
    fun l => havg_integral_min l hφ (continuous_wAvg hpos hcont l hφ)
      (fun W g => wAvg_update Φ l φ W g)
  -- (e) the Haar measure against the weight, from below
  have hF : ∀ l, wlo * ∫ W, (φ W - wAvg Φ l φ W) ^ 2 ∂(piHaar N Lk)
      ≤ ∫ W, (φ W - wAvg Φ l φ W) ^ 2 * Φ W ∂(piHaar N Lk) := by
    intro l
    have hcont : Continuous (fun W => (φ W - wAvg Φ l φ W) ^ 2) :=
      (hφ.sub (continuous_wAvg hpos hcont l hφ)).pow 2
    rw [← integral_const_mul]
    refine integral_mono (haar_integrable (continuous_const.mul hcont))
      (haar_integrable (hcont.mul hcw)) (fun W => ?_)
    have h1 := (hwb W).1
    have h2 := sq_nonneg (φ W - wAvg Φ l φ W)
    show wlo * (φ W - wAvg Φ l φ W) ^ 2 ≤ (φ W - wAvg Φ l φ W) ^ 2 * Φ W
    nlinarith
  -- (f) the chain
  have hsumD : ∑ l, ∫ W, (φ W - havg l φ W) ^ 2 ∂(piHaar N Lk)
      ≤ ∑ l, ∫ W, (φ W - wAvg Φ l φ W) ^ 2 ∂(piHaar N Lk) :=
    Finset.sum_le_sum (fun l _ => hD l)
  have hsumF : wlo * ∑ l, ∫ W, (φ W - wAvg Φ l φ W) ^ 2 ∂(piHaar N Lk)
      ≤ ∑ l, ∫ W, (φ W - wAvg Φ l φ W) ^ 2 * Φ W ∂(piHaar N Lk) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun l _ => hF l)
  have hgoal := chain_le hZ hwhi0.le hK20 hwlo0 hVar hB hJ hsumD hsumF
  have hsumE : ∑ l, wExpect Φ
        (fun W => (φ W - wAvg Φ l φ W) ^ 2)
      = (∑ l, ∫ W, (φ W - wAvg Φ l φ W) ^ 2 * Φ W ∂(piHaar N Lk))
        / ∫ W, Φ W ∂(piHaar N Lk) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun l _ => hE _)
  rw [hsumE]
  exact hgoal

#print axioms w_poincare

/-! ## On the periodic lattice -/

section Torus

open MassGap.PeriodicState (torusObs)
open MassGap.KnabeCriterion (periodicGaugeInvSubmodule PeriodicGaugeInv)
open MassGap.HeatBath (continuous_torusObs exists_abs_le)
open MassGap.WeightedTorus (TorusWeight wForm wCondExp wLift torusObs_wLift wTorusState)

variable {N : ℕ}

/-- The constant observable `1` in the periodic gauge-invariant observables.

DERIVED: `1` is the constant; `2 * j + 1` is the index of the even-extent family. -/
def oneW (j : ℕ) : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)) :=
  ⟨1, show PeriodicGaugeInv (2 * j + 1) (1 : C(GibbsSpec.IConf (SU N), ℝ)) from fun _ _ => rfl⟩

/-- A positive continuous weight on a finite configuration lies between two positive constants.

DERIVED: `0` is the sign. -/
theorem weight_bounds {Lk : Type} [Fintype Lk] {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W)
    (hcont : Continuous Φ) : ∃ wlo whi : ℝ, 0 < wlo ∧ ∀ W, wlo ≤ Φ W ∧ Φ W ≤ whi := by
  obtain ⟨W0, -, hW0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hcont.continuousOn
  obtain ⟨C, hC⟩ := exists_abs_le hcont
  exact ⟨Φ W0, C, hpos W0, fun W => ⟨hW0 (Set.mem_univ W), (le_abs_self _).trans (hC W)⟩⟩

#print axioms weight_bounds

/-- **The Poincaré inequality of a torus weight at every extent**: some `C ≥ 0` has
`wForm(v, v) − wForm(v, 1)² ≤ C Σ_l wForm(v − Eₗv, v − Eₗv)` (`w_poincare` at the torus reading,
`WeightedTorus.torusObs_wLift`).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family; `0` is
the sign of `C`; `2` is the square. -/
theorem wTorus_poincare (Ψ : TorusWeight N) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)),
      wForm Ψ j v v - wForm Ψ j v (oneW j) ^ 2
        ≤ C * ∑ l, wForm Ψ j (v - wCondExp Ψ (2 * j + 1) l v) (v - wCondExp Ψ (2 * j + 1) l v) := by
  obtain ⟨wlo, whi, hwlo, hwb⟩ := weight_bounds (Ψ.pos (2 * j + 1)) (Ψ.cont (2 * j + 1))
  obtain ⟨C, hC0, hC⟩ := w_poincare (Ψ.cont (2 * j + 1)) hwlo hwb
  refine ⟨C, hC0, fun v => ?_⟩
  have h := hC _ (continuous_torusObs (2 * j + 1) (v : C(GibbsSpec.IConf (SU N), ℝ)))
  have e1 : wForm Ψ j v v = wExpect (Ψ.Φ (2 * j + 1))
      (fun W => torusObs (2 * j + 1) (v : C(GibbsSpec.IConf (SU N), ℝ)) W
        * torusObs (2 * j + 1) (v : C(GibbsSpec.IConf (SU N), ℝ)) W) := rfl
  have e2 : wForm Ψ j v (oneW j) = wExpect (Ψ.Φ (2 * j + 1))
      (torusObs (2 * j + 1) (v : C(GibbsSpec.IConf (SU N), ℝ))) := by
    show wExpect (Ψ.Φ (2 * j + 1)) (fun W => torusObs (2 * j + 1) (v : C(GibbsSpec.IConf (SU N), ℝ)) W
      * 1) = _
    simp only [mul_one]
  have e3 : ∀ l, wForm Ψ j (v - wCondExp Ψ (2 * j + 1) l v) (v - wCondExp Ψ (2 * j + 1) l v)
      = wExpect (Ψ.Φ (2 * j + 1))
          (fun W => (torusObs (2 * j + 1) (v : C(GibbsSpec.IConf (SU N), ℝ)) W
            - wAvg (Ψ.Φ (2 * j + 1)) l
                (torusObs (2 * j + 1) (v : C(GibbsSpec.IConf (SU N), ℝ))) W) ^ 2) := by
    intro l
    have hW : ∀ W, torusObs (2 * j + 1)
        ((v - wCondExp Ψ (2 * j + 1) l v : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
          : C(GibbsSpec.IConf (SU N), ℝ)) W
        = torusObs (2 * j + 1) (v : C(GibbsSpec.IConf (SU N), ℝ)) W
          - wAvg (Ψ.Φ (2 * j + 1)) l (torusObs (2 * j + 1) (v : C(GibbsSpec.IConf (SU N), ℝ))) W := by
      intro W
      exact congrArg (fun t => torusObs (2 * j + 1) (v : C(GibbsSpec.IConf (SU N), ℝ)) W - t)
        (congrFun (torusObs_wLift Ψ (2 * j + 1) l (v : C(GibbsSpec.IConf (SU N), ℝ))) W)
    show wExpect (Ψ.Φ (2 * j + 1)) (fun W => torusObs (2 * j + 1)
          ((v - wCondExp Ψ (2 * j + 1) l v : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
            : C(GibbsSpec.IConf (SU N), ℝ)) W
        * torusObs (2 * j + 1)
          ((v - wCondExp Ψ (2 * j + 1) l v : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
            : C(GibbsSpec.IConf (SU N), ℝ)) W) = _
    congr 1
    funext W
    rw [hW W, sq]
  rw [e1, e2, Finset.sum_congr rfl (fun l _ => e3 l)]
  exact h

#print axioms wTorus_poincare

/-- `wForm(1, 1) = 1` (`DLRLimit.State.map_one`).

DERIVED: `1` is the constant and its value. -/
theorem wForm_one_one (Ψ : TorusWeight N) (j : ℕ) : wForm Ψ j (oneW (N := N) j) (oneW j) = 1 := by
  show wTorusState Ψ (2 * j + 1) ((1 : C(GibbsSpec.IConf (SU N), ℝ)) * 1) = 1
  rw [mul_one]
  exact DLRLimit.State.map_one _

#print axioms wForm_one_one

/-- `Eₗ 1 = 1` (`WeightedHeatBath.wAvg_of_readsNot`).

DERIVED: `1` is the constant. -/
theorem wCondExp_one (Ψ : TorusWeight N) (j : ℕ) (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1)) :
    wCondExp Ψ (2 * j + 1) l (oneW (N := N) j) = oneW j := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro U
  show wAvg (Ψ.Φ (2 * j + 1)) l (torusObs (2 * j + 1) (1 : C(GibbsSpec.IConf (SU N), ℝ)))
    (MassGap.HeatBath.restrictConf (2 * j + 1) U) = 1
  exact MassGap.WeightedHeatBath.wAvg_of_readsNot (Ψ.pos _) (Ψ.cont _) l (fun _ _ => rfl) _

#print axioms wCondExp_one

/-- The complement `id − Eₗ` of a conditional expectation of `Ψ`. -/
def wH (Ψ : TorusWeight N) (j : ℕ) (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1)) :
    ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)) →ₗ[ℝ] ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)) :=
  (LinearMap.id : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))
    →ₗ[ℝ] ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) - wCondExp Ψ (2 * j + 1) l

/-- **`wTorus_poincare` in the form of a patch system's `hₗ = id − Eₗ`.**

DERIVED: as `wTorus_poincare`. -/
theorem wTorus_poincare_H (Ψ : TorusWeight N) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)),
      wForm Ψ j v v - wForm Ψ j v (oneW j) ^ 2 ≤ C * ∑ l, wForm Ψ j (wH Ψ j l v) (wH Ψ j l v) := by
  obtain ⟨C, hC0, hC⟩ := wTorus_poincare Ψ j
  exact ⟨C, hC0, fun v => by
    simpa only [wH, LinearMap.sub_apply, LinearMap.id_apply] using hC v⟩

#print axioms wTorus_poincare_H

end Torus

end MassGap.WeightedErgodic
