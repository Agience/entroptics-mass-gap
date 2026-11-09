import Mathlib
import MassGap.LocalPotential
import MassGap.ObserverKnabe

noncomputable section

/-!
# MassGap.PotKnabe — the global gap of Wilson times a local potential

The Knabe step of `ObserverKnabe` for Wilson times a gauge-invariant local potential whose term
supports lie within two steps per coordinate. Two links interact when they share a plaquette or a
support (`RPot`); such links are within the two-step window (`near2_of_RPot`), so the excess weight
and its row sums are those of `ObserverKnabe`. `potLocal` is the local-weight structure that gives the
commutation of conditional expectations off `RPot` (`wCondExp_comm_pot`), and `pot_globalGap` is the
global gap.
-/

namespace MassGap.PotKnabe

open MeasureTheory
open MassGap.SUN (SU)
open MassGap.HeatBath (bdT wt SharePlaq not_sharePlaq_symm locW restSum wt_split restSum_update
  locW_update_other continuous_locW)
open MassGap.LocalPotential (LocalPot LocalPotFam wtV potWeight potBox_localGap)
open MassGap.WeightedHeatBath (LocalWeight)
open MassGap.ObserverKnabe (Near2 near2_add near2_of_zero_or_unit adjExcess adjExcess_nonneg adj_row
  adj_col)
open MassGap.BoxPatch (disp_cases bd_site sharePlaq_disp UnitStep prod_le_of_not_unit pairWeight_box)

variable {N : ℕ}

/-- **Two links interact under Wilson times a potential**: a common plaquette or a common support. -/
def RPot {M : ℕ} (P : LocalPot N M) (l l' : WilsonHypercubic.Link 4 (M + 1)) : Prop :=
  SharePlaq (bdT M) l l' ∨ ∃ X, l ∈ P.supp X ∧ l' ∈ P.supp X

/-- **Wilson times a local potential as a local weight**: at `l`, the plaquettes and terms through
`l`, against the rest.

DERIVED: no numeral. -/
def potLocal {M : ℕ} (β : ℝ) (P : LocalPot N M) : LocalWeight N (WilsonHypercubic.Link 4 (M + 1)) where
  Φ := wtV β P
  loc := fun l W => locW (bdT M) β l W
    * Real.exp (∑ X ∈ Finset.univ.filter (fun X => l ∈ P.supp X), P.V X W)
  rest := fun l W => Real.exp (-β * restSum (bdT M) l W)
    * Real.exp (∑ X ∈ Finset.univ.filter (fun X => ¬ l ∈ P.supp X), P.V X W)
  R := RPot P
  split := fun l W => by
    unfold wtV LocalPot.tot
    rw [wt_split (bdT M) β l W, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun X => l ∈ P.supp X), Real.exp_add]
    ring
  rest_update := fun l W g => by
    rw [restSum_update]
    congr 2
    exact Finset.sum_congr rfl fun X hX => P.reads X W l g (Finset.mem_filter.mp hX).2
  rest_ne := fun _ _ => (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne'
  loc_cont := fun l => (continuous_locW (bdT M) β l).mul
    (Real.continuous_exp.comp (continuous_finset_sum _ fun X _ => P.cont X))
  R_symm := fun l l' h hr => h (by
    rcases hr with hs | ⟨X, h1, h2⟩
    · exact Or.inl (by
        by_contra hn
        exact not_sharePlaq_symm hn hs)
    · exact Or.inr ⟨X, h2, h1⟩)
  loc_update_other := fun l l' h W g => by
    have hs : ¬ SharePlaq (bdT M) l l' := fun hs => h (Or.inl hs)
    rw [locW_update_other (bdT M) β hs W g]
    congr 2
    exact Finset.sum_congr rfl fun X hX =>
      P.reads X W l' g (fun hl' => h (Or.inr ⟨X, (Finset.mem_filter.mp hX).2, hl'⟩))

/-- **Interacting links are within two steps** when every support lies within two steps per
coordinate.

DERIVED: `0`, `1` are the zero and unit steps; `4` is the spacetime dimension; `1` is the successor
writing the extent. -/
theorem near2_of_RPot {M : ℕ} (P : LocalPot N M)
    (hdiam : ∀ X a b, a ∈ P.supp X → b ∈ P.supp X → Near2 (b.2 - a.2))
    {l l' : WilsonHypercubic.Link 4 (M + 1)} (h : RPot P l l') : Near2 (l'.2 - l.2) := by
  rcases h with ⟨r, hl, hl'⟩ | ⟨X, hl, hl'⟩
  · intro i
    have := near2_add (disp_cases (bd_site r hl) (bd_site r hl') i)
      (Or.inl rfl : (0 : Fin (M + 1)) = 0 ∨ (0 : Fin (M + 1)) = 1 ∨ (0 : Fin (M + 1)) = -1)
    simpa using this
  · exact hdiam X l l' hl hl'

#print axioms near2_of_RPot

open MassGap.KnabeCriterion (PatchSystem periodicGaugeInvSubmodule selfAdj_id_sub idem_id_sub
  comm_id_sub pairWeight)
open MassGap.BoxPatch (bR bR_pos box_cover box_cover2 boxWeight)
open MassGap.HeatBath (restrictConf continuous_torusObs)
open MassGap.PeriodicState (torusObs)
open MassGap.WeightedTorus (TorusWeight wCondExp wForm wForm_symm wForm_nonneg wCondExp_selfAdj
  wCondExp_idem wLift torusObs_wLift)

/-- **Conditional expectations commute at links not interacting under the potential**
(`WeightedHeatBath.wAvg_comm` for `potLocal`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem wCondExp_comm_pot (β : ℝ) (F : LocalPotFam N) (M : ℕ)
    {l l' : WilsonHypercubic.Link 4 (M + 1)} (hll : l ≠ l') (hs : ¬ RPot (F.P M) l l')
    (x : ↥(periodicGaugeInvSubmodule (N := N) M)) :
    wCondExp (potWeight β F) M l (wCondExp (potWeight β F) M l' x)
      = wCondExp (potWeight β F) M l' (wCondExp (potWeight β F) M l x) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro U
  show MassGap.WeightedHeatBath.wAvg ((potWeight (N := N) β F).Φ M) l
      (torusObs M (wLift (potWeight β F) M l' (x : C(GibbsSpec.IConf (SU N), ℝ))))
      (restrictConf M U)
    = MassGap.WeightedHeatBath.wAvg ((potWeight (N := N) β F).Φ M) l'
      (torusObs M (wLift (potWeight β F) M l (x : C(GibbsSpec.IConf (SU N), ℝ))))
      (restrictConf M U)
  rw [torusObs_wLift, torusObs_wLift]
  exact MassGap.WeightedHeatBath.wAvg_comm (potLocal (N := N) β (F.P M)) hll hs
    (continuous_torusObs M _) _

#print axioms wCondExp_comm_pot

/-- **The pair condition for the potential** (as `ObserverKnabe.adj_pair_cond`, with `RPot`).

DERIVED: `1` is the least box side; `2` is the two windows fitting in the circle; `4` is the
spacetime dimension. -/
theorem pot_pair_cond {M : ℕ} (P : LocalPot N M)
    (hdiam : ∀ X a b, a ∈ P.supp X → b ∈ P.supp X → Near2 (b.2 - a.2))
    (n : ℕ) (hn : 1 ≤ n) (hL : 2 * n ≤ M + 1)
    {l l' : WilsonHypercubic.Link 4 (M + 1)} (hll : l ≠ l') {Q : Prop} (hQ : ¬ RPot P l l' → Q) :
    (Q ∧ pairWeight (boxWeight (M := M) n) l l' ≤ bR n)
      ∨ |pairWeight (boxWeight (M := M) n) l l' - bR n| ≤ adjExcess (M := M) n l l' := by
  by_cases hN : Near2 (l'.2 - l.2)
  · right
    unfold adjExcess
    rw [if_neg hll, if_pos hN]
  · left
    refine ⟨hQ fun hR => hN (near2_of_RPot P hdiam hR), ?_⟩
    have h0 : l'.2 - l.2 ≠ 0 := fun h => hN (near2_of_zero_or_unit (Or.inl h))
    have hu : ¬ UnitStep (l'.2 - l.2) := fun h => hN (near2_of_zero_or_unit (Or.inr h))
    have hle := prod_le_of_not_unit n hn hL h0 hu
    have hbN : ((((n - 1) ^ 2 * n ^ 2 : ℕ)) : ℝ) = bR n := by
      unfold bR
      push_cast [Nat.cast_sub hn]
      ring
    rw [pairWeight_box, ← hbN]
    exact_mod_cast hle

#print axioms pot_pair_cond

/-- **The box patch system of Wilson times a local potential.**

DERIVED: as `ObserverKnabe.adjPatchSystem`. -/
def potPatchSystem (β : ℝ) (F : LocalPotFam N)
    (hdiam : ∀ M X a b, a ∈ (F.P M).supp X → b ∈ (F.P M).supp X → Near2 (b.2 - a.2))
    (n j : ℕ) (hn : 2 ≤ n) (hj : n ≤ j + 1) : PatchSystem where
  E := ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))
  ι := WilsonHypercubic.Link 4 (2 * j + 1 + 1)
  κ := WilsonHypercubic.Site 4 (2 * j + 1 + 1)
  B := wForm (potWeight β F) j
  symm := wForm_symm (potWeight β F) j
  nonneg := wForm_nonneg (potWeight β F) j
  h := fun l => (LinearMap.id : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))
      →ₗ[ℝ] ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) - wCondExp (potWeight β F) (2 * j + 1) l
  selfAdj := fun l => selfAdj_id_sub _ _ (wCondExp_selfAdj (potWeight β F) j l)
  idem := fun l => idem_id_sub _ (wCondExp_idem (potWeight β F) (2 * j + 1) l)
  c := boxWeight n
  w := adjExcess n
  a₁ := (n : ℝ) ^ 4
  a₂ := (n : ℝ) ^ 4
  b := bR n
  e := 5184 * ((n : ℝ) ^ 4 - ((n : ℝ) - 2) ^ 4)
  cover := box_cover n (by omega)
  cover2 := box_cover2 n (by omega)
  pair := fun l l' hll => pot_pair_cond (F.P (2 * j + 1)) (hdiam _) n (by omega) (by omega) hll
    (fun hs x => comm_id_sub _ _ (fun y => wCondExp_comm_pot β F (2 * j + 1) hll hs y) x)
  w_nonneg := adjExcess_nonneg n
  row := adj_row n hn (by omega)
  col := adj_col n hn (by omega)

/-- The potential box side is at least `2`.

DERIVED: `2` is the least side; `300000` is the box side. -/
theorem two_le_potSide : 2 ≤ 300000 := by norm_num

/-- **The global gap of Wilson times a local potential**: `SU(2)`, `β ≤ 1/200`, a gauge-invariant
local potential of local norm at most `1/5` with supports within two steps per coordinate. At box
side `300000` and every extent index `j` with `300000 ≤ j + 1`, the heat-bath dynamics has global
gap `1/10` (`LocalPotential.potBox_localGap`, `KnabeCriterion.globalGap_of_localGap`).

DERIVED: `300000` is the box side; `1/10` is below the Knabe constant at `γ = 57/200`
(`(γ n⁴ − n⁴ + b − e)/b = 0.146…`); `2` is the rank; `1/200` and `1/5` are the coupling and
potential-norm bounds of `LocalPotential.potBox_localGap`. -/
theorem pot_globalGap {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 200) (F : LocalPotFam 2)
    (hν : ∀ M l, (F.P M).norm l ≤ 1 / 5)
    (hdiam : ∀ M X a b, a ∈ (F.P M).supp X → b ∈ (F.P M).supp X → Near2 (b.2 - a.2))
    (j : ℕ) (hj : 300000 ≤ j + 1) :
    (potPatchSystem (N := 2) β F hdiam 300000 j two_le_potSide hj).GlobalGap (1 / 10) := by
  have hb : 0 < (potPatchSystem (N := 2) β F hdiam 300000 j two_le_potSide hj).b := bR_pos (by norm_num)
  have hloc : (potPatchSystem (N := 2) β F hdiam 300000 j two_le_potSide hj).LocalGap (57 / 200) :=
    fun k x => potBox_localGap hβ0 hβ F hν 300000 j hj k x
  refine (potPatchSystem (N := 2) β F hdiam 300000 j two_le_potSide hj).globalGap_mono ?_
    ((potPatchSystem (N := 2) β F hdiam 300000 j two_le_potSide hj).globalGap_of_localGap hb hloc)
  show (1 : ℝ) / 10 ≤ (57 / 200 * ((300000 : ℕ) : ℝ) ^ 4 - ((300000 : ℕ) : ℝ) ^ 4 + bR 300000
    - 5184 * (((300000 : ℕ) : ℝ) ^ 4 - (((300000 : ℕ) : ℝ) - 2) ^ 4)) / bR 300000
  unfold bR
  norm_num

#print axioms pot_globalGap

/-- **The global gap on the wide box**: `SU(2)`, `β ≤ 1/40` (`β_std ≤ 1/20`), local norm `≤ 1/8`,
supports within two steps; box side `300000`, global gap `1/10` at every extent
(`LocalPotential.potBox_localGap_wide`).

DERIVED: `300000` is the box side; `1/10` is below the Knabe constant at `γ = 299/1000`
(`0.161…`); `2` is the rank; `1/40` and `1/8` are the coupling and potential-norm bounds of
`LocalPotential.potBox_localGap_wide`. -/
theorem pot_globalGap_wide {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 40) (F : LocalPotFam 2)
    (hν : ∀ M l, (F.P M).norm l ≤ 1 / 8)
    (hdiam : ∀ M X a b, a ∈ (F.P M).supp X → b ∈ (F.P M).supp X → Near2 (b.2 - a.2))
    (j : ℕ) (hj : 300000 ≤ j + 1) :
    (potPatchSystem (N := 2) β F hdiam 300000 j two_le_potSide hj).GlobalGap (1 / 10) := by
  have hb : 0 < (potPatchSystem (N := 2) β F hdiam 300000 j two_le_potSide hj).b := bR_pos (by norm_num)
  have hloc : (potPatchSystem (N := 2) β F hdiam 300000 j two_le_potSide hj).LocalGap (299 / 1000) :=
    fun k x => MassGap.LocalPotential.potBox_localGap_wide hβ0 hβ F hν 300000 j hj k x
  refine (potPatchSystem (N := 2) β F hdiam 300000 j two_le_potSide hj).globalGap_mono ?_
    ((potPatchSystem (N := 2) β F hdiam 300000 j two_le_potSide hj).globalGap_of_localGap hb hloc)
  show (1 : ℝ) / 10 ≤ (299 / 1000 * ((300000 : ℕ) : ℝ) ^ 4 - ((300000 : ℕ) : ℝ) ^ 4 + bR 300000
    - 5184 * (((300000 : ℕ) : ℝ) ^ 4 - (((300000 : ℕ) : ℝ) - 2) ^ 4)) / bR 300000
  unfold bR
  norm_num

#print axioms pot_globalGap_wide

/-! ## Clustering -/

open MassGap.HeatBathGapDecay (Far nrm Titer cov_bound_exp H_form_le_card)
open MassGap.ObserverKnabe (obsNb card_near2_le)

/-- **The potential patch system at box side `300000`.**

DERIVED: `2` is the rank; `300000` is the box side. -/
def potSys (β : ℝ) (F : LocalPotFam 2)
    (hdiam : ∀ M X a b, a ∈ (F.P M).supp X → b ∈ (F.P M).supp X → Near2 (b.2 - a.2))
    (j : ℕ) (hj : 300000 ≤ j + 1) : PatchSystem :=
  potPatchSystem (N := 2) β F hdiam 300000 j two_le_potSide hj

/-- **The `hₗ` of the potential patch system commute off the two-step neighbours.**

DERIVED: `300000` is the box side; `2` is the rank. -/
theorem pot_hcomm (β : ℝ) (F : LocalPotFam 2)
    (hdiam : ∀ M X a b, a ∈ (F.P M).supp X → b ∈ (F.P M).supp X → Near2 (b.2 - a.2))
    (j : ℕ) (hj : 300000 ≤ j + 1) (l l' : WilsonHypercubic.Link 4 (2 * j + 1 + 1))
    (hl' : l' ∉ obsNb (2 * j + 1) l) (u : (potSys β F hdiam j hj).E) :
    (potSys β F hdiam j hj).B
      ((potSys β F hdiam j hj).h l' ((potSys β F hdiam j hj).h l u)
        - (potSys β F hdiam j hj).h l ((potSys β F hdiam j hj).h l' u))
      ((potSys β F hdiam j hj).h l' ((potSys β F hdiam j hj).h l u)
        - (potSys β F hdiam j hj).h l ((potSys β F hdiam j hj).h l' u)) = 0 := by
  have hN : ¬ Near2 (l'.2 - l.2) := fun h => hl' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hll : l ≠ l' := fun h => hN (by rw [h, sub_self]; exact near2_of_zero_or_unit (Or.inl rfl))
  have hR : ¬ RPot (F.P (2 * j + 1)) l l' := fun h => hN (near2_of_RPot _ (hdiam _) h)
  have e := comm_id_sub _ _ (fun y => wCondExp_comm_pot (N := 2) β F (2 * j + 1) hll hR y) u
  have e' : (potSys β F hdiam j hj).h l' ((potSys β F hdiam j hj).h l u)
      - (potSys β F hdiam j hj).h l ((potSys β F hdiam j hj).h l' u) = 0 := by
    rw [sub_eq_zero]
    exact e.symm
  rw [e']
  simp

#print axioms pot_hcomm

set_option maxHeartbeats 1000000 in
/-- **Exponential clustering of Wilson times a local potential, at fixed separation level**
(`HeatBathGapDecay.cov_bound_exp` on `potSys`; the ergodic limit `herg` is the hypothesis, as in the
Wilson chain).

DERIVED: `5184` is `card_near2_le`'s bound; `1/10` is `pot_globalGap`'s gap; `300000` is the box
side; `2` is the rank; `1/200` and `1/5` are the coupling and potential-norm bounds of
`LocalPotential.potBox_localGap`. -/
theorem pot_cluster {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 200) (F : LocalPotFam 2)
    (hν : ∀ M l, (F.P M).norm l ≤ 1 / 5)
    (hdiam : ∀ M X a b, a ∈ (F.P M).supp X → b ∈ (F.P M).supp X → Near2 (b.2 - a.2))
    (j : ℕ) (hj : 300000 ≤ j + 1)
    (A C : Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1))) (f g : (potSys β F hdiam j hj).E)
    (hf : ∀ l, l ∉ A → (potSys β F hdiam j hj).B ((potSys β F hdiam j hj).h l f)
      ((potSys β F hdiam j hj).h l f) = 0)
    (hg : ∀ l, l ∉ C → (potSys β F hdiam j hj).B ((potSys β F hdiam j hj).h l g)
      ((potSys β F hdiam j hj).h l g) = 0)
    (k : ℕ) (hfar : ∀ l ∈ C, Far (obsNb (2 * j + 1)) A k l) {L : ℝ}
    (herg : Filter.Tendsto (fun M => (potSys β F hdiam j hj).B
      (Titer (potSys β F hdiam j hj)
        (Fintype.card (WilsonHypercubic.Link 4 (2 * j + 1 + 1)) : ℝ) M f) g)
      Filter.atTop (nhds L))
    {y : ℝ} (hy : 1 ≤ y) (s : ℕ) :
    |(potSys β F hdiam j hj).B f g - L|
      ≤ s * C.card * (nrm (potSys β F hdiam j hj) f
          * ((y⁻¹) ^ k * Real.exp (2 * (5184 : ℕ) * y * s))) * nrm (potSys β F hdiam j hj) g
        + 2 / (1 / 10) * Real.exp (-(1 / 10 * s / 2))
          * (A.card * nrm (potSys β F hdiam j hj) f) * nrm (potSys β F hdiam j hj) g := by
  have hcard : 0 < Fintype.card (WilsonHypercubic.Link 4 (2 * j + 1 + 1)) := Fintype.card_pos
  have hc1 : (1 / 10 : ℝ) ≤ (Fintype.card (WilsonHypercubic.Link 4 (2 * j + 1 + 1)) : ℝ) := by
    have : (1 : ℝ) ≤ Fintype.card (WilsonHypercubic.Link 4 (2 * j + 1 + 1)) := by exact_mod_cast hcard
    linarith
  exact cov_bound_exp _ hcard (H_form_le_card _) (by norm_num) hc1
    (pot_globalGap hβ0 hβ F hν hdiam j hj) (obsNb (2 * j + 1)) (fun l => card_near2_le l)
    (pot_hcomm β F hdiam j hj) hy A C f g hf hg k hfar herg s

#print axioms pot_cluster

end MassGap.PotKnabe
