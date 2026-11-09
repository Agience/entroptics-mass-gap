import Mathlib
import MassGap.ObserverOSG
import MassGap.AxisInvG

/-!
# MassGap.ObserverLinkedG — the observer's linked Euclidean data over `G`, and the capstone

`ObserverOSLinked.observerOSDataSLinked` extends the `SU(N)` observer's `OSDataS` by the Schwinger
functional `schwSFM` on families of fields and decaying functions, the vectors `vecD` of decaying
margin monomials with `⟪vecD P, vecD Q⟫ = schwSFM(θP ∪ Q)`, the compact vectors `gvecT`, and the
closure identity. This module builds the same `ClayTreeG.OSDataSLinkedG G D τ r` for every
`GaugeGroup G` over a schedule `S` with `FlowG.SchedOS S` and `ObserverOSG.SchedShiftInv S`, then
reads it at `canonSched G` and `D = SymPlaqClassG G` (`obsXG`) and feeds it to
`AxisInvG.clayStatementAtG_of_inputsG''''`.

| `SU(N)` | here (any `G`, any `S`) |
|---|---|
| `ObserverOSEuclidS.ClassMoments`, `abs_latSF_le_M`, `abs_latSF_sub_le_M`, `tendsto_latSF_M` | `ClassMomentsG`, `abs_latSFG_le_M`, `abs_latSFG_sub_le_M`, `tendsto_latSFG_M` |
| `abs_contSF_sub_le_M`, `tendsto_schwSFM`, `tendsto_contSF_approx`, `schwSF_eq_schwSFM` | `abs_contSFG_sub_le_M`, `tendsto_schwSFMG`, `tendsto_contSFG_approx`, `schwSFG_eq_schwSFMG` |
| `cutM`, `kernS`, `pairFam_cutM` | `cutMG`, `kernSG`, `pairFamG_cutMG` |
| `ObserverOSLinked.pairFam_cutM2`, `exists_kern_cauchy`, `tendsto_kernF_cutM` | `pairFamG_cutMG2`, `exists_kern_cauchyG`, `tendsto_kernFG_cutMG` |
| `pairFields_mem`, `inner_gvecT_eq`, `cauchySeq_cutVec`, `vecD`, `tendsto_vecD`, `inner_vecD` | `pairFieldsG_mem`, `inner_gvecTG_eq`, `cauchySeq_cutVecG`, `vecDG`, `tendsto_vecDG`, `inner_vecDG` |
| `eventually_cutM_ofMarginD`, `vecD_ofMarginD`, `closure_range_vecD` | `eventually_cutMG_ofMarginDG`, `vecDG_ofMarginDG`, `closure_range_vecDG` |
| `observerOSDataSLinked`, `observerOSDataSLinked_inner` | `observerOSDataSLinkedG`, `observerOSDataSLinkedG_inner` |
| `ClayWiring.obsX`, `obsX_SM`, `obsX_O`, `obsX_gap` | `obsXG`, `obsXG_SM`, `obsXG_O`, `obsXG_gap`; `obsXG_sa` (the generator) |
| `ClayFull.observer_generator_isSelfAdjoint` | `ObserverOSG.observer_generator_isSelfAdjointG` |

`ClayTreeG` already states the decaying monomials and the linked structure over `G` (`DMonoG`,
`DMarginMonoG`, `DMarginMonoDG`, `MarginMonoDG`, `pairFieldsG`, `pairFunsG`, `ofMarginDG`,
`schwSFMG`, `OSDataSLinkedG`); they are used as they are. So are the group-free parts of
`ObserverOSEuclidS` (`chi`, `cut`, `decayBound_cut`, `decayBound_of_vanish`, `cut_sub_le`, `cN`,
`tendsto_lip_bound`, `decRefl`, `chi_reflR`) and of `ObserverOSLinked` (`decOfTest`), and
`ClayFull.hamiltonianGap_of_selfAdjoint` on `OSDataS`.

## Where the gap comes from

`obsXG` does not produce the transfer gap: it takes `hg : TransferGap.GapAt (transferNG …) ρ` with
`0 < ρ < 1`, the gap input of `observerOSDataSLinkedG`, as a hypothesis. (At `SU(N)`,
`ClayWiring.obsX` obtains it from `WDeltaRun.RunSeed N` through `ClayWiring.gapEx`; no `G` form of
that is stated here.)

## The capstone

`clayStatementAtG_of_observer` is `AxisInvG.clayStatementAtG_of_inputsG''''` at `τ = 0` with
`X := obsXG …`, and with the inputs `hSM` (`obsXG_SM`), `hsa` (`obsXG_sa`), `hXO` (`obsXG_O`) and
`hCut` (`tendsto_schwSFMG` under `ClassMomentsG`) discharged. In their place it takes the observer
inputs: `ClassMomentsG` on the class (`ht`, `hC0`, `hU`), `UnitCubeExpBoundG` for the field
`symG (plaqFieldG q0)` (`hUE`), a physical range (`hphys`), `FlowConnectedNonzeroG` (`hNT`) and the
transfer gap (`hρ0`, `hρ1`, `hg`). `hW` and `hcube` are inputs of both.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `4` the dimension; `0` the plane `τ = 0`, the reference step and the signs;
`1` the top of `ρ` and the window `L = 1`; `5`, `6`, `8192` the orders and the gauge of
`ObserverOSSchwartz`; `2`, `3` the square and the three kernel differences of the Cauchy estimate.
-/

noncomputable section

namespace MassGap.ObserverLinkedG

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ObserverOS MassGap.ObserverOSGrowth MassGap.ObserverOSSchwartz
  MassGap.ObserverOSTempered MassGap.ObserverEnergyBox MassGap.ObserverOSEuclidS
  MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked MassGap.ClayTreeG MassGap.ClayWiringG
  MassGap.FlowG MassGap.TimeGroupG MassGap.EnergyBoundG MassGap.ObserverOSG Filter
open scoped Topology

/-! ## 1. The Lipschitz estimate for families of fields -/

section Lipschitz

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **Cube moments uniform over the class**, over a schedule: one `t > 0`, `C ≥ 0` with
`CubeMomentsAtG` for every field of `D`.

DERIVED: no numeral of its own. -/
def ClassMomentsG (S : Sched G) (W : ConfFlowG G) (D : Set (LField G)) (t C : ℝ) : Prop :=
  ∀ O ∈ D, CubeMomentsAtG S W O t C

/-- **One step, a family of fields**: `|latSFG| ≤ (1 + n c) ∏ᵢ 8192 (Aᵢ + ε)`.

DERIVED: `0` the signs; `8192` is `sum_shellWeight_le`'s; `1`, `2` are `abs_state_prod_le`'s; `5` the
weight's exponent of `ObserverOSSchwartz.abs_le_sum_shell`, one above the dimension `4`. -/
theorem abs_latSFG_le_M (S : Sched G) (W : ConfFlowG G) {D : Set (LField G)}
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {ι : Type} [Fintype ι] (O : ι → LField G)
    (hO : ∀ i, O i ∈ D) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C) {k : ℕ}
    (hk : ∀ i, ∀ R : ℝ, 0 ≤ R → ∀ p : ℕ,
      S.ν k (cubeSumG (S.a k) R (W.fieldMap k (O i)).1 ^ (2 * p))
        ≤ ((2 * R + 1) ^ 4) ^ (2 * p) * (((2 * p).factorial : ℝ) / t ^ (2 * p) * C))
    (f : ι → TestFn) (A : ι → ℝ) (hA : ∀ i, DecayBound 5 (f i).1 (A i)) {ε : ℝ} (hε : 0 < ε) :
    |latSFG S (energyMapG S W D) k (fun i => (O i, f i))|
      ≤ (1 + Fintype.card ι * cN t C (Fintype.card ι)) * ∏ i, 8192 * (A i + ε) := by
  have hc0 := cN_nonneg ht hC0 (Fintype.card ι)
  have hb := abs_state_prod_le (S.ν k)
    (fun i => smear (S.a k) (energyMapG S W D k (O i)).1 (f i))
    (fun i => 8192 * (A i + ε))
    (fun i => mul_pos (by norm_num) (by linarith [(hA i).nonneg]))
    (c := cN t C (Fintype.card ι))
    (fun i => (moment_smear_decay_leG S W hpos (hO i) k (f i) (hA i) hc0 _
        (Fintype.card_pos_iff.mpr ⟨i⟩).ne' (fun R hR => hk i R hR _)).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg (by norm_num) (hA i).nonneg) (by linarith) _) hc0))
  exact hb

/-- **One step of the Lipschitz estimate, a family of fields.**

DERIVED: `0` the signs; `8192` is `sum_shellWeight_le`'s; `-1` the coefficient of the subtracted
test function; `1`, `2` are `abs_state_prod_le`'s; `5` the weight's exponent of
`ObserverOSSchwartz.abs_le_sum_shell`, one above the dimension `4`. -/
theorem abs_latSFG_sub_le_M (S : Sched G) (W : ConfFlowG G) {D : Set (LField G)}
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : ι → LField G) (hO : ∀ i, O i ∈ D) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C) {k : ℕ}
    (hk : ∀ i, ∀ R : ℝ, 0 ≤ R → ∀ p : ℕ,
      S.ν k (cubeSumG (S.a k) R (W.fieldMap k (O i)).1 ^ (2 * p))
        ≤ ((2 * R + 1) ^ 4) ^ (2 * p) * (((2 * p).factorial : ℝ) / t ^ (2 * p) * C))
    (f f' : ι → TestFn) (B δ : ι → ℝ) (hB : ∀ i, DecayBound 5 (f i).1 (B i))
    (hB' : ∀ i, DecayBound 5 (f' i).1 (B i))
    (hδ : ∀ i y, (1 + ‖y‖) ^ 5 * |(f' i).1 y - (f i).1 y| ≤ δ i) {ε : ℝ} (hε : 0 < ε) :
    |latSFG S (energyMapG S W D) k (fun i => (O i, f' i))
        - latSFG S (energyMapG S W D) k (fun i => (O i, f i))|
      ≤ (1 + Fintype.card ι * cN t C (Fintype.card ι))
        * ∑ a, 8192 * (δ a + ε) * ∏ i ∈ Finset.univ \ {a}, 8192 * (B i + ε) := by
  have hc0 := cN_nonneg ht hC0 (Fintype.card ι)
  have ha := S.a_pos k
  have hmom : ∀ i (g : TestFn) (A : ℝ), DecayBound 5 g.1 A →
      S.ν k (smear (S.a k) (energyMapG S W D k (O i)).1 g ^ (2 * Fintype.card ι))
        ≤ cN t C (Fintype.card ι) * (8192 * (A + ε)) ^ (2 * Fintype.card ι) :=
    fun i g A hA' =>
      (moment_smear_decay_leG S W hpos (hO i) k g hA' hc0 _
        (Fintype.card_pos_iff.mpr ⟨i⟩).ne' (fun R hR => hk i R hR _)).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg (by norm_num) hA'.nonneg) (by linarith) _) hc0)
  have hdec : ∀ i, DecayBound 5 (testAdd (f' i) (testSmul (-1) (f i))).1 (δ i) := fun i y => by
    show (1 + ‖y‖) ^ 5 * |(f' i).1 y + -1 * (f i).1 y| ≤ δ i
    rw [neg_one_mul, ← sub_eq_add_neg]
    exact hδ i y
  have hb := abs_state_prod_sub_le (S.ν k)
    (fun i => smear (S.a k) (energyMapG S W D k (O i)).1 (f i))
    (fun i => smear (S.a k) (energyMapG S W D k (O i)).1 (f' i))
    (fun i => 8192 * (B i + ε)) (fun i => 8192 * (δ i + ε))
    (fun i => mul_pos (by norm_num) (by linarith [(hB i).nonneg]))
    (fun i => mul_pos (by norm_num) (by linarith [(hdec i).nonneg]))
    (c := cN t C (Fintype.card ι))
    (fun i => hmom i _ _ (hB i)) (fun i => hmom i _ _ (hB' i))
    (fun i => by
      show S.ν k ((smear (S.a k) (energyMapG S W D k (O i)).1 (f' i)
          - smear (S.a k) (energyMapG S W D k (O i)).1 (f i)) ^ (2 * Fintype.card ι)) ≤ _
      rw [← smear_tailG ha]
      exact hmom i _ _ (hdec i))
  exact hb

/-- **A family of fields converges along the ultrafilter**, under the class moments.

DERIVED: `1` the choice `ε = 1`; `5` the weight's exponent of `ObserverOSSchwartz.abs_le_sum_shell`,
one above the dimension `4`. -/
theorem tendsto_latSFG_M (S : Sched G) (W : ConfFlowG G) {D : Set (LField G)}
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMomentsG S W D t C) {ι : Type} [Fintype ι] (O : ι → LField G)
    (hO : ∀ i, O i ∈ D) (f : ι → TestFn) (A : ι → ℝ) (hA : ∀ i, DecayBound 5 (f i).1 (A i)) :
    Tendsto (fun k => latSFG S (energyMapG S W D) k (fun i => (O i, f i))) (ultra : Filter ℕ)
      (𝓝 (contSFG S (energyMapG S W D) (fun i => (O i, f i)))) := by
  have hstep : ∀ᶠ k in atTop, |latSFG S (energyMapG S W D) k (fun i => (O i, f i))|
      ≤ (1 + Fintype.card ι * cN t C (Fintype.card ι)) * ∏ i, 8192 * (A i + 1) :=
    (Filter.eventually_all.mpr (fun i => hU (O i) (hO i))).mono
      (fun k hk => abs_latSFG_le_M S W hpos O hO ht hC0 hk f A hA one_pos)
  obtain ⟨x, hx⟩ := exists_tendsto_ultra _ _ hstep
  exact tendsto_nhds_limUnder ⟨x, hx⟩

/-- **The Lipschitz estimate in `‖·‖₅` for a family of fields**, over a schedule:
`|S(f') − S(f)| ≤ (1 + n c) ∑ₐ 8192 δₐ ∏_{i ≠ a} 8192 Bᵢ`.

DERIVED: `0` the signs and the limit point; `8192`, `5` as in `abs_latSFG_sub_le_M`; `1`, `2` are
`abs_state_prod_le`'s. -/
theorem abs_contSFG_sub_le_M (S : Sched G) (W : ConfFlowG G) {D : Set (LField G)}
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMomentsG S W D t C) {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : ι → LField G) (hO : ∀ i, O i ∈ D)
    (f f' : ι → TestFn) (B δ : ι → ℝ) (hB : ∀ i, DecayBound 5 (f i).1 (B i))
    (hB' : ∀ i, DecayBound 5 (f' i).1 (B i))
    (hδ : ∀ i y, (1 + ‖y‖) ^ 5 * |(f' i).1 y - (f i).1 y| ≤ δ i) :
    |contSFG S (energyMapG S W D) (fun i => (O i, f' i))
        - contSFG S (energyMapG S W D) (fun i => (O i, f i))|
      ≤ (1 + Fintype.card ι * cN t C (Fintype.card ι))
        * ∑ a, 8192 * δ a * ∏ i ∈ Finset.univ \ {a}, 8192 * B i := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hT' := tendsto_latSFG_M S W hpos ht hC0 hU O hO f' B hB'
  have hT := tendsto_latSFG_M S W hpos ht hC0 hU O hO f B hB
  have hcont : Continuous (fun ε : ℝ => (1 + Fintype.card ι * cN t C (Fintype.card ι))
      * ∑ a, 8192 * (δ a + ε) * ∏ i ∈ Finset.univ \ {a}, 8192 * (B i + ε)) :=
    continuous_const.mul (continuous_finsetSum _ (fun a _ =>
      (continuous_const.mul (continuous_const.add continuous_id)).mul
        (continuous_finsetProd _
          (fun i _ => continuous_const.mul (continuous_const.add continuous_id)))))
  have h := le_of_forall_pos_continuous hcont (fun ε hε => by
    have hstep : ∀ᶠ k in atTop,
        |latSFG S (energyMapG S W D) k (fun i => (O i, f' i))
          - latSFG S (energyMapG S W D) k (fun i => (O i, f i))|
        ≤ (1 + Fintype.card ι * cN t C (Fintype.card ι))
          * ∑ a, 8192 * (δ a + ε) * ∏ i ∈ Finset.univ \ {a}, 8192 * (B i + ε) :=
      (Filter.eventually_all.mpr (fun i => hU (O i) (hO i))).mono
        (fun k hk => abs_latSFG_sub_le_M S W hpos O hO ht hC0 hk f f' B δ hB hB' hδ hε)
    exact le_of_tendsto (hT'.sub hT).abs (hstep.filter_mono ultra_le))
  simpa only [add_zero] using h

end Lipschitz

/-! ## 2. The extension to families of fields -/

section Extension

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The cut-off Schwinger functions converge**: `S(Oᵢ, cut gᵢ R) → schwSFMG O g`, under the
class moments.

DERIVED: `0` the sign of `ε`; `6`, `5` the orders; `1` the shift. -/
theorem tendsto_schwSFMG (S : Sched G) (W : ConfFlowG G) {D : Set (LField G)}
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMomentsG S W D t C) {ι : Type} [Fintype ι] (O : ι → LField G)
    (hO : ∀ i, O i ∈ D) (g : ι → Decaying) :
    Tendsto (fun R : ℕ => contSFG S (energyMapG S W D) (fun i => (O i, cut (g i) R))) atTop
      (𝓝 (schwSFMG S W D O g)) := by
  classical
  have hex : ∀ i, ∃ B : ℝ, DecayBound 6 (g i).1 B := fun i => (g i).2
  choose B hB using hex
  have hB5 : ∀ (R₁ : ℕ) i, DecayBound 5 (cut (g i) R₁).1 (B i) :=
    fun R₁ i => decayBound_cut ((hB i).mono (by norm_num)) R₁
  set b : ℕ → ℝ := fun R => (1 + Fintype.card ι * cN t C (Fintype.card ι))
    * ∑ a, 8192 * (0 + B a / ((R : ℝ) + 1)) * ∏ i ∈ Finset.univ \ {a}, 8192 * B i with hbdef
  have hb : Tendsto b atTop (𝓝 0) := tendsto_lip_bound _ B _ tendsto_const_nhds
  have hdist : ∀ M m : ℕ, M ≤ m →
      dist (contSFG S (energyMapG S W D) (fun i => (O i, cut (g i) m)))
        (contSFG S (energyMapG S W D) (fun i => (O i, cut (g i) M))) ≤ b M := by
    intro M m hMm
    rw [Real.dist_eq]
    refine (abs_contSFG_sub_le_M S W hpos ht hC0 hU O hO (fun i => cut (g i) M)
      (fun i => cut (g i) m) B (fun i => B i / ((M : ℝ) + 1)) (fun i => hB5 M i)
      (fun i => hB5 m i) (fun i y => ?_)).trans (le_of_eq ?_)
    · refine decayBound_of_vanish (h := fun y => chi m y * (g i).1 y - chi M y * (g i).1 y)
        (hB i) (Nat.cast_nonneg M) (fun y hy => ?_) (fun y => ?_) y
      · have h1 := chi_eq_one hy
        have h2 : chi m y = 1 := chi_eq_one (hy.trans (by exact_mod_cast hMm))
        simp only [h1, h2, sub_self]
      · show |chi m y * (g i).1 y - chi M y * (g i).1 y| ≤ |(g i).1 y|
        rw [← sub_mul, abs_mul]
        refine mul_le_of_le_one_left (abs_nonneg _) ?_
        rw [abs_le]
        constructor <;> linarith [chi_le_one m y, chi_nonneg m y, chi_le_one M y, chi_nonneg M y]
    · simp only [hbdef, zero_add]
  have hcs : CauchySeq
      (fun R : ℕ => contSFG S (energyMapG S W D) (fun i => (O i, cut (g i) R))) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨M, hM⟩ := (hb.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
    exact ⟨M, fun m hm => (hdist M m hm).trans_lt (hM M le_rfl)⟩
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcs
  exact tendsto_nhds_limUnder ⟨x, hx⟩

/-- **Every approximation converges to the extension**: test functions `h R i`, uniformly bounded in
`‖·‖₅`, with `‖h R i − gᵢ‖₅ ≤ η R → 0`, have `S(Oᵢ, h R i) → schwSFMG O g`.

DERIVED: `0` the limit; `5`, `6` the orders; `1` the shift; `8192` the gauge. -/
theorem tendsto_contSFG_approx (S : Sched G) (W : ConfFlowG G) {D : Set (LField G)}
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMomentsG S W D t C) {ι : Type} [Fintype ι] (O : ι → LField G)
    (hO : ∀ i, O i ∈ D) (g : ι → Decaying) (h : ℕ → ι → TestFn) (B' : ι → ℝ)
    (hhB : ∀ R i, DecayBound 5 (h R i).1 (B' i)) (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hh : ∀ R i y, (1 + ‖y‖) ^ 5 * |(h R i).1 y - (g i).1 y| ≤ η R) :
    Tendsto (fun R : ℕ => contSFG S (energyMapG S W D) (fun i => (O i, h R i))) atTop
      (𝓝 (schwSFMG S W D O g)) := by
  classical
  have hex : ∀ i, ∃ B : ℝ, DecayBound 6 (g i).1 B := fun i => (g i).2
  choose B hB using hex
  have hS := tendsto_schwSFMG S W hpos ht hC0 hU O hO g
  have hBB : ∀ R i, DecayBound 5 (cut (g i) R).1 (B i + B' i) := fun R i y =>
    ((decayBound_cut ((hB i).mono (by norm_num)) R) y).trans (by linarith [(hhB R i).nonneg])
  have hBB' : ∀ R i, DecayBound 5 (h R i).1 (B i + B' i) := fun R i y =>
    ((hhB R i) y).trans (by linarith [(hB i).nonneg])
  have hdiff : ∀ R : ℕ,
      |contSFG S (energyMapG S W D) (fun i => (O i, h R i))
        - contSFG S (energyMapG S W D) (fun i => (O i, cut (g i) R))|
      ≤ (1 + Fintype.card ι * cN t C (Fintype.card ι))
        * ∑ a, 8192 * (η R + B a / ((R : ℝ) + 1))
          * ∏ i ∈ Finset.univ \ {a}, 8192 * (B i + B' i) := fun R =>
    abs_contSFG_sub_le_M S W hpos ht hC0 hU O hO (fun i => cut (g i) R) (fun i => h R i)
      (fun i => B i + B' i) (fun i => η R + B i / ((R : ℝ) + 1)) (hBB R) (hBB' R)
      (fun i y => by
        have h1 := hh R i y
        have h2 := cut_sub_le (hB i) R y
        have hp : 0 ≤ (1 + ‖y‖) ^ 5 := pow_nonneg (by linarith [norm_nonneg y]) 5
        show (1 + ‖y‖) ^ 5 * |(h R i).1 y - chi R y * (g i).1 y| ≤ _
        have h3 : |(h R i).1 y - chi R y * (g i).1 y|
            ≤ |(h R i).1 y - (g i).1 y| + |chi R y * (g i).1 y - (g i).1 y| := by
          have := abs_sub_le ((h R i).1 y) ((g i).1 y) (chi R y * (g i).1 y)
          rwa [abs_sub_comm ((g i).1 y)] at this
        calc (1 + ‖y‖) ^ 5 * |(h R i).1 y - chi R y * (g i).1 y|
            ≤ (1 + ‖y‖) ^ 5 * (|(h R i).1 y - (g i).1 y| + |chi R y * (g i).1 y - (g i).1 y|) :=
              mul_le_mul_of_nonneg_left h3 hp
          _ ≤ η R + B i / ((R : ℝ) + 1) := by rw [mul_add]; linarith)
  have hlim := tendsto_lip_bound (1 + Fintype.card ι * cN t C (Fintype.card ι)) B
    (fun a => ∏ i ∈ Finset.univ \ {a}, 8192 * (B i + B' i)) hη
  have hsub : Tendsto (fun R : ℕ => contSFG S (energyMapG S W D) (fun i => (O i, h R i))
      - contSFG S (energyMapG S W D) (fun i => (O i, cut (g i) R))) atTop (𝓝 0) :=
    squeeze_zero_norm (fun R => by rw [Real.norm_eq_abs]; exact hdiff R) hlim
  have := hsub.add hS
  simp only [sub_add_cancel, zero_add] at this
  exact this

/-- **The one-field extension of `ObserverOSG` is this one**: `schwSFG O g = schwSFMG (O, …, O) g`
(cube truncations approximate in `‖·‖₅`).

DERIVED: `5`, `6` the orders; `1` the indicator on the cube; `0` the sign. -/
theorem schwSFG_eq_schwSFMG (S : Sched G) (W : ConfFlowG G) {D : Set (LField G)}
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMomentsG S W D t C) {O : LField G} (hO : O ∈ D) {n : ℕ}
    (g : Fin n → Decaying) :
    schwSFG S W D O g = schwSFMG S W D (fun _ => O) g := by
  have hex : ∀ i, ∃ B : ℝ, DecayBound 6 (g i).1 B := fun i => (g i).2
  choose B hB using hex
  have hB0 : ∀ i, 0 ≤ B i := fun i => (hB i).nonneg
  have hT := tendsto_contSFG_approx S W hpos ht hC0 hU (fun _ => O) (fun _ => hO) g
    (fun R i => trunc (g i) R) B (fun R i => decayBound_trunc ((hB i).mono (by norm_num)) R)
    (fun R => (∑ i, B i) / ((R : ℝ) + 1))
    (by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (∑ i, B i)
      rw [mul_zero] at h
      exact h.congr (fun R => by rw [mul_one_div]))
    (fun R i y => by
      have h1 := decayBound_of_vanish (h := fun y => cubeInd (R : ℝ) y * (g i).1 y - (g i).1 y)
        (hB i) (Nat.cast_nonneg R)
        (fun y hy => by
          have hin : ∀ j, |y j| ≤ (R : ℝ) := fun j => by
            have := norm_le_pi_norm y j
            rw [Real.norm_eq_abs] at this
            linarith
          show cubeInd (R : ℝ) y * (g i).1 y - (g i).1 y = 0
          unfold cubeInd
          rw [if_pos hin, one_mul, sub_self])
        (fun y => by
          show |cubeInd (R : ℝ) y * (g i).1 y - (g i).1 y| ≤ |(g i).1 y|
          unfold cubeInd
          split_ifs <;> simp) y
      refine h1.trans (div_le_div_of_nonneg_right ?_ (by positivity))
      exact Finset.single_le_sum (f := B) (fun i _ => hB0 i) (Finset.mem_univ i))
  exact hT.limUnder_eq

end Extension

/-! ## 3. Cut-off monomials and the kernel -/

section Kernel

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The cut-off margin monomial** over `G`: the cut-off keeps the support.

DERIVED: `0` the vanishing value. -/
def cutMG {τ : Fin 4} {r : ℝ} (R : ℕ) (P : DMarginMonoG G τ r) : MarginMonoG G τ r :=
  ⟨⟨P.1.1, fun i => ((P.1.2 i).1, cut (P.1.2 i).2 R)⟩, by
    obtain ⟨d, hd, hrd, hP⟩ := P.2
    exact ⟨d, hd, hrd, fun i y hy => hP i y (fun h0 => hy (by
      show chi R y * (P.1.2 i).2.1 y = 0
      rw [h0, mul_zero]))⟩⟩

/-- **The reflected-pair kernel on decaying monomials over a schedule**: `schwSFMG(θP ∪ Q)`.

DERIVED: `4` the dimension. -/
def kernSG (S : Sched G) (W : ConfFlowG G) (D : Set (LField G)) (τ : Fin 4) (P Q : DMonoG G) :
    ℝ :=
  schwSFMG S W D (pairFieldsG τ P Q) (pairFunsG τ P Q)

/-- The reflected pair of cut-off monomials is the cut-off of the reflected pair (`chi` is reflection
invariant).

DERIVED: no numeral. -/
theorem pairFamG_cutMG {τ : Fin 4} {r : ℝ} (R : ℕ) (P Q : DMarginMonoG G τ r) :
    pairFamG τ (cutMG R P).1 (cutMG R Q).1
      = fun x => (pairFieldsG τ P.1 Q.1 x, cut (pairFunsG τ P.1 Q.1 x) R) := by
  funext x
  cases x with
  | inl i =>
    refine Prod.ext rfl (Subtype.ext (funext (fun y => ?_)))
    show chi R (reflR τ y) * (P.1.2 i).2.1 (reflR τ y) = chi R y * (P.1.2 i).2.1 (reflR τ y)
    rw [chi_reflR]
  | inr j => rfl

/-- The reflected pair of cut-off monomials at two radii.

DERIVED: no numeral. -/
theorem pairFamG_cutMG2 {τ : Fin 4} {r : ℝ} (R R' : ℕ) (P Q : DMarginMonoG G τ r) :
    pairFamG τ (cutMG R P).1 (cutMG R' Q).1
      = fun x => (pairFieldsG τ P.1 Q.1 x,
          cut (pairFunsG τ P.1 Q.1 x) (Sum.elim (fun _ => R) (fun _ => R') x)) := by
  funext x
  cases x with
  | inl i =>
    refine Prod.ext rfl (Subtype.ext (funext (fun y => ?_)))
    show chi R (reflR τ y) * (P.1.2 i).2.1 (reflR τ y) = chi R y * (P.1.2 i).2.1 (reflR τ y)
    rw [chi_reflR]
  | inr j => rfl

/-- **The kernel converges along the cut-offs, uniformly in two radii**: there is `b(M) → 0` with
`|k(R, R') − k(M, M)| ≤ b(M)` for `R, R' ≥ M`.

DERIVED: `0` the limit; `5`, `6` the orders; `1` the shift; `8192` the gauge. -/
theorem exists_kern_cauchyG (S : Sched G) (W : ConfFlowG G) {D : Set (LField G)}
    (hD : ∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMomentsG S W D t C) {τ : Fin 4} {r : ℝ} (P Q : DMarginMonoG G τ r)
    (hPQ : ∀ x, pairFieldsG τ P.1 Q.1 x ∈ D) :
    ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝 0) ∧ ∀ M R R' : ℕ, M ≤ R → M ≤ R' →
      |kernFG S (energy0G S W D hD) τ (cutMG R P).1 (cutMG R' Q).1
        - kernFG S (energy0G S W D hD) τ (cutMG M P).1 (cutMG M Q).1| ≤ b M := by
  classical
  have hex : ∀ x, ∃ B : ℝ, DecayBound 6 (pairFunsG τ P.1 Q.1 x).1 B :=
    fun x => (pairFunsG τ P.1 Q.1 x).2
  choose B hB using hex
  have hB5 : ∀ (R₁ : ℕ) x, DecayBound 5 (cut (pairFunsG τ P.1 Q.1 x) R₁).1 (B x) :=
    fun R₁ x => decayBound_cut ((hB x).mono (by norm_num)) R₁
  refine ⟨fun M => (1 + Fintype.card (Fin P.1.1 ⊕ Fin Q.1.1)
      * cN t C (Fintype.card (Fin P.1.1 ⊕ Fin Q.1.1)))
      * ∑ a, 8192 * (0 + B a / ((M : ℝ) + 1)) * ∏ i ∈ Finset.univ \ {a}, 8192 * B i,
    tendsto_lip_bound _ B _ tendsto_const_nhds, fun M R R' hMR hMS => ?_⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Fin P.1.1 ⊕ Fin Q.1.1 → ℕ, ρ = Sum.elim (fun _ => R) (fun _ => R') :=
    ⟨_, rfl⟩
  have hρM : ∀ x, M ≤ ρ x := by
    intro x
    cases x with
    | inl i => rw [hρ]; exact hMR
    | inr j => rw [hρ]; exact hMS
  show |contSFG S (energyMapG S W D) (pairFamG τ (cutMG R P).1 (cutMG R' Q).1)
    - contSFG S (energyMapG S W D) (pairFamG τ (cutMG M P).1 (cutMG M Q).1)| ≤ _
  rw [pairFamG_cutMG2, pairFamG_cutMG, ← hρ]
  refine (abs_contSFG_sub_le_M S W hpos ht hC0 hU (pairFieldsG τ P.1 Q.1) hPQ
    (fun x => cut (pairFunsG τ P.1 Q.1 x) M) (fun x => cut (pairFunsG τ P.1 Q.1 x) (ρ x)) B
    (fun x => B x / ((M : ℝ) + 1)) (fun x => hB5 M x) (fun x => hB5 (ρ x) x)
    (fun x y => ?_)).trans (le_of_eq ?_)
  · refine decayBound_of_vanish
      (h := fun y => chi (ρ x) y * (pairFunsG τ P.1 Q.1 x).1 y
        - chi M y * (pairFunsG τ P.1 Q.1 x).1 y)
      (hB x) (Nat.cast_nonneg M) (fun y hy => ?_) (fun y => ?_) y
    · have h1 := chi_eq_one hy
      have h2 : chi (ρ x) y = 1 := chi_eq_one (hy.trans (by exact_mod_cast hρM x))
      simp only [h1, h2, sub_self]
    · show |chi (ρ x) y * (pairFunsG τ P.1 Q.1 x).1 y - chi M y * (pairFunsG τ P.1 Q.1 x).1 y|
        ≤ |(pairFunsG τ P.1 Q.1 x).1 y|
      rw [← sub_mul, abs_mul]
      refine mul_le_of_le_one_left (abs_nonneg _) ?_
      rw [abs_le]
      constructor <;> linarith [chi_le_one (ρ x) y, chi_nonneg (ρ x) y, chi_le_one M y,
        chi_nonneg M y]
  · simp only [zero_add]

/-- **The kernel entries of the cut-offs converge to the extended kernel**:
`k(R, R) → kernSG P Q`.

DERIVED: no numeral. -/
theorem tendsto_kernFG_cutMG (S : Sched G) (W : ConfFlowG G) {D : Set (LField G)}
    (hD : ∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMomentsG S W D t C) {τ : Fin 4} {r : ℝ} (P Q : DMarginMonoG G τ r)
    (hPQ : ∀ x, pairFieldsG τ P.1 Q.1 x ∈ D) :
    Tendsto (fun R : ℕ => kernFG S (energy0G S W D hD) τ (cutMG R P).1 (cutMG R Q).1) atTop
      (𝓝 (kernSG S W D τ P.1 Q.1)) := by
  refine (tendsto_schwSFMG S W hpos ht hC0 hU (pairFieldsG τ P.1 Q.1) hPQ
    (pairFunsG τ P.1 Q.1)).congr (fun R => ?_)
  show contSFG S (energyMapG S W D)
      (fun i => (pairFieldsG τ P.1 Q.1 i, cut (pairFunsG τ P.1 Q.1 i) R))
    = contSFG S (energyMapG S W D) (pairFamG τ (cutMG R P).1 (cutMG R Q).1)
  exact congrArg (contSFG S (energyMapG S W D)) (pairFamG_cutMG R P Q).symm

end Kernel

/-! ## 4. The vectors -/

section Vectors

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- The fields of a reflected pair of monomials with fields in `D` lie in `D`.

DERIVED: no numeral. -/
theorem pairFieldsG_mem {D : Set (LField G)}
    (hD : ∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ D ↔ O ∈ D) {τ : Fin 4}
    {r : ℝ} (P Q : DMarginMonoDG G D τ r) (x : Fin P.1.1.1 ⊕ Fin Q.1.1.1) :
    pairFieldsG τ P.1.1 Q.1.1 x ∈ D := by
  cases x with
  | inl i => exact (hD τ _).mpr (P.2 i)
  | inr j => exact Q.2 j

/-- The reconstruction over `G` reads the kernel on compact margin monomials
(`FlowG.flow_reconstructionG` at step `0`).

DERIVED: `0` the reference step. -/
theorem inner_gvecTG_eq (S : Sched G) (hS : SchedOS S) (Φ : GFlow G) (hB : UniformBoundFG S Φ.map)
    (τ : Fin 4) {r : ℝ} (hpp : Φ.PosPreserving S τ r) (A B : MarginMonoG G τ r) :
    inner ℂ (gvecTG S hS Φ hB τ hpp A) (gvecTG S hS Φ hB τ hpp B) = (kernFG S Φ τ A.1 B.1 : ℂ) :=
  (flow_reconstructionG S hS Φ hB τ hpp 0).2 A B

/-- **The flowed reconstruction over `G` is generated by its monomials**: the vectors `gvecTG P`
have the observer's flowed Schwinger functions of the reflected pairs as inner products
(`inner_gvecTG_eq`), are carried by `timeTG (a_m)` to the vectors of the shifted monomials
(`timeTG_dyadic` at `n = 1`, `stepTG_gvecTG`), and have closed span all of `FlowHG`
(`ClayStatement.span_single_dense`). With `v Q = cvec Q` by definition, this is
`ClayStatementG.ObsGenG` at every observer whose Hilbert space is `FlowHG`.

DERIVED: `1` one step. -/
theorem obsGenG_flow (S : Sched G) (hS : SchedOS S) (W : ConfFlowG G) {D : Set (LField G)}
    (hD : ∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ D ↔ O ∈ D)
    (hB : UniformBoundFG S (energy0G S W D hD).map) (τ : Fin 4) {r : ℝ}
    (hpp : (energy0G S W D hD).PosPreserving S τ r) :
    (∀ P Q : MarginMonoG G τ r,
      inner ℂ (gvecTG S hS (energy0G S W D hD) hB τ hpp P)
          (gvecTG S hS (energy0G S W D hD) hB τ hpp Q)
        = (contSFG S (energyMapG S W D)
            (Sum.elim (fun i => ((P.1.2 i).1.refl τ, (P.1.2 i).2.reflect τ)) Q.1.2) : ℂ))
    ∧ (∀ (m : ℕ) (P Q : MarginMonoG G τ r),
      Q.1 = ⟨P.1.1, fun i => ((P.1.2 i).1, (P.1.2 i).2.translate (timeVecG S m τ 1))⟩ →
        gvecTG S hS (energy0G S W D hD) hB τ hpp Q
          = timeTG S hS (energy0G S W D hD) hB τ hpp (S.a m)
              (gvecTG S hS (energy0G S W D hD) hB τ hpp P))
    ∧ (Submodule.span ℂ (Set.range (gvecTG S hS (energy0G S W D hD) hB τ hpp))).topologicalClosure
      = ⊤ := by
  refine ⟨fun P Q => inner_gvecTG_eq S hS (energy0G S W D hD) hB τ hpp P Q,
    fun m P Q hQ => ?_, MassGap.ClayStatement.span_single_dense _⟩
  have e : Q = marginShiftG S τ m P := Subtype.ext hQ
  have ht := timeTG_dyadic S hS (energy0G S W D hD) hB τ hpp m 1
  rw [Nat.cast_one, one_mul, pow_one] at ht
  rw [e, ht, stepTG_gvecTG]

/-- **The vectors of the cut-offs are Cauchy**: `‖gvecTG (cutMG R P) − gvecTG (cutMG M P)‖² ≤ 3 b(M)`
for `R ≥ M`.

DERIVED: `2` the square and the cross term; `3` collects the three kernel differences; `0` the
sign of `ε`. -/
theorem cauchySeq_cutVecG (S : Sched G) (hS : SchedOS S) (W : ConfFlowG G) {D : Set (LField G)}
    (hD : ∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBoundG S W O) {t C : ℝ}
    (ht : 0 < t) (hC0 : 0 ≤ C) (hU : ClassMomentsG S W D t C) (τ : Fin 4) {r : ℝ}
    (hphys : (energy0G S W D hD).PhysRange S r) (P : DMarginMonoDG G D τ r) :
    CauchySeq (fun R : ℕ => gvecTG S hS (energy0G S W D hD)
      (uniformBoundFG_energy0G S hS W hD hpos hcube) τ
      (posPreserving_of_physRangeG S (energy0G S W D hD) hphys τ) (cutMG R P.1)) := by
  obtain ⟨b, hb, hbd⟩ := exists_kern_cauchyG S W hD hpos ht hC0 hU P.1 P.1
    (pairFieldsG_mem hD P P)
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have hε2 : (3 : ℝ) * 0 < ε ^ 2 := by rw [mul_zero]; positivity
  obtain ⟨M, hM⟩ := ((hb.const_mul 3).eventually (gt_mem_nhds hε2)).exists_forall_of_atTop
  refine ⟨M, fun R hR => ?_⟩
  rw [dist_eq_norm]
  set u := fun R₁ : ℕ => gvecTG S hS (energy0G S W D hD)
    (uniformBoundFG_energy0G S hS W hD hpos hcube) τ
    (posPreserving_of_physRangeG S (energy0G S W D hD) hphys τ) (cutMG R₁ P.1) with hudef
  have hin : ∀ R₁ R₂ : ℕ, inner ℂ (u R₁) (u R₂)
      = (kernFG S (energy0G S W D hD) τ (cutMG R₁ P.1).1 (cutMG R₂ P.1).1 : ℂ) := fun R₁ R₂ =>
    inner_gvecTG_eq S hS _ _ τ _ _ _
  have e : ‖u R - u M‖ ^ 2 = kernFG S (energy0G S W D hD) τ (cutMG R P.1).1 (cutMG R P.1).1
      - 2 * kernFG S (energy0G S W D hD) τ (cutMG R P.1).1 (cutMG M P.1).1
      + kernFG S (energy0G S W D hD) τ (cutMG M P.1).1 (cutMG M P.1).1 := by
    rw [norm_sub_sq (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
      hin, hin, hin]
    simp
  have h1 := hbd M R R hR hR
  have h2 := hbd M R M hR le_rfl
  have hsq : ‖u R - u M‖ ^ 2 ≤ 3 * b M := by
    rw [e]
    rw [abs_le] at h1 h2
    linarith [h1.1, h1.2, h2.1, h2.2]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le (hsq.trans_lt (hM M le_rfl))

/-- **The vector of a decaying margin monomial** over `G`: the limit of the vectors of its cut-offs.

DERIVED: no numeral. -/
def vecDG (S : Sched G) (hS : SchedOS S) (W : ConfFlowG G) {D : Set (LField G)}
    (hD : ∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBoundG S W O) (τ : Fin 4)
    {r : ℝ} (hphys : (energy0G S W D hD).PhysRange S r) (P : DMarginMonoDG G D τ r) :
    FlowHG S hS (energy0G S W D hD) (uniformBoundFG_energy0G S hS W hD hpos hcube) τ
      (posPreserving_of_physRangeG S (energy0G S W D hD) hphys τ) :=
  limUnder atTop (fun R : ℕ => gvecTG S hS (energy0G S W D hD)
    (uniformBoundFG_energy0G S hS W hD hpos hcube) τ
    (posPreserving_of_physRangeG S (energy0G S W D hD) hphys τ) (cutMG R P.1))

/-- DERIVED: no numeral. -/
theorem tendsto_vecDG (S : Sched G) (hS : SchedOS S) (W : ConfFlowG G) {D : Set (LField G)}
    (hD : ∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBoundG S W O) {t C : ℝ}
    (ht : 0 < t) (hC0 : 0 ≤ C) (hU : ClassMomentsG S W D t C) (τ : Fin 4) {r : ℝ}
    (hphys : (energy0G S W D hD).PhysRange S r) (P : DMarginMonoDG G D τ r) :
    Tendsto (fun R : ℕ => gvecTG S hS (energy0G S W D hD)
      (uniformBoundFG_energy0G S hS W hD hpos hcube) τ
      (posPreserving_of_physRangeG S (energy0G S W D hD) hphys τ) (cutMG R P.1)) atTop
      (𝓝 (vecDG S hS W hD hpos hcube τ hphys P)) := by
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_cutVecG S hS W hD hpos hcube ht hC0 hU τ hphys P)
  exact tendsto_nhds_limUnder ⟨x, hx⟩

/-- **The reconstruction over `G` reads the extended kernel**: `⟪vecDG P, vecDG Q⟫ = kernSG P Q`.

DERIVED: no numeral. -/
theorem inner_vecDG (S : Sched G) (hS : SchedOS S) (W : ConfFlowG G) {D : Set (LField G)}
    (hD : ∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBoundG S W O) {t C : ℝ}
    (ht : 0 < t) (hC0 : 0 ≤ C) (hU : ClassMomentsG S W D t C) (τ : Fin 4) {r : ℝ}
    (hphys : (energy0G S W D hD).PhysRange S r) (P Q : DMarginMonoDG G D τ r) :
    inner ℂ (vecDG S hS W hD hpos hcube τ hphys P) (vecDG S hS W hD hpos hcube τ hphys Q)
      = (kernSG S W D τ P.1.1 Q.1.1 : ℂ) := by
  have hT := (tendsto_vecDG S hS W hD hpos hcube ht hC0 hU τ hphys P).inner
    (tendsto_vecDG S hS W hD hpos hcube ht hC0 hU τ hphys Q) (𝕜 := ℂ)
  have hK := (Complex.continuous_ofReal.tendsto _).comp
    (tendsto_kernFG_cutMG S W hD hpos ht hC0 hU P.1 Q.1 (pairFieldsG_mem hD P Q))
  refine tendsto_nhds_unique hT (hK.congr (fun R => ?_))
  exact (inner_gvecTG_eq S hS _ _ τ _ _ _).symm

end Vectors

/-! ## 5. Compact monomials and density -/

section Compact

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The cut-offs of a compact monomial are eventually the monomial itself.**

DERIVED: `1` the cut-off on the ball. -/
theorem eventually_cutMG_ofMarginDG {D : Set (LField G)} {τ : Fin 4} {r : ℝ}
    (Q : MarginMonoDG G D τ r) : ∀ᶠ R : ℕ in atTop, cutMG R (ofMarginDG Q).1 = Q.1 := by
  have hex : ∀ i, ∃ R M : ℝ, IsTest (Q.1.1.2 i).2.1 R M := fun i => (Q.1.1.2 i).2.2
  choose R0 M hRM using hex
  filter_upwards [Filter.eventually_ge_atTop ⌈∑ i, R0 i⌉₊] with R hR
  refine Subtype.ext (Sigma.ext rfl (heq_of_eq (funext (fun i => ?_))))
  refine Prod.ext rfl (Subtype.ext (funext (fun y => ?_)))
  show chi R y * (Q.1.1.2 i).2.1 y = (Q.1.1.2 i).2.1 y
  by_cases h0 : (Q.1.1.2 i).2.1 y = 0
  · rw [h0, mul_zero]
  · have hy : ‖y‖ ≤ R := by
      refine (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg R)).mpr (fun j => ?_)
      rw [Real.norm_eq_abs]
      have h1 := (hRM i).2.2 y h0 j
      have h2 : R0 i ≤ ∑ i, R0 i :=
        Finset.single_le_sum (f := R0) (fun i _ => (hRM i).1) (Finset.mem_univ i)
      have h3 : ∑ i, R0 i ≤ (⌈∑ i, R0 i⌉₊ : ℝ) := Nat.le_ceil _
      have h4 : (⌈∑ i, R0 i⌉₊ : ℝ) ≤ R := by exact_mod_cast hR
      linarith
    rw [chi_eq_one hy, one_mul]

/-- **A compact monomial's vector is its reconstructed vector**: `vecDG (ofMarginDG Q) = gvecTG Q`.

DERIVED: no numeral. -/
theorem vecDG_ofMarginDG (S : Sched G) (hS : SchedOS S) (W : ConfFlowG G) {D : Set (LField G)}
    (hD : ∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBoundG S W O) {t C : ℝ}
    (ht : 0 < t) (hC0 : 0 ≤ C) (hU : ClassMomentsG S W D t C) (τ : Fin 4) {r : ℝ}
    (hphys : (energy0G S W D hD).PhysRange S r) (Q : MarginMonoDG G D τ r) :
    vecDG S hS W hD hpos hcube τ hphys (ofMarginDG Q)
      = gvecTG S hS (energy0G S W D hD) (uniformBoundFG_energy0G S hS W hD hpos hcube) τ
          (posPreserving_of_physRangeG S (energy0G S W D hD) hphys τ) Q.1 :=
  tendsto_nhds_unique (tendsto_vecDG S hS W hD hpos hcube ht hC0 hU τ hphys (ofMarginDG Q))
    (tendsto_const_nhds.congr' ((eventually_cutMG_ofMarginDG Q).mono (fun _ hR =>
      (congrArg (gvecTG S hS (energy0G S W D hD) (uniformBoundFG_energy0G S hS W hD hpos hcube) τ
        (posPreserving_of_physRangeG S (energy0G S W D hD) hphys τ)) hR).symm)))

/-- **The decaying vectors and the compact vectors have the same closure.**

DERIVED: no numeral. -/
theorem closure_range_vecDG (S : Sched G) (hS : SchedOS S) (W : ConfFlowG G) {D : Set (LField G)}
    (hD : ∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBoundG S W O) {t C : ℝ}
    (ht : 0 < t) (hC0 : 0 ≤ C) (hU : ClassMomentsG S W D t C) (τ : Fin 4) {r : ℝ}
    (hphys : (energy0G S W D hD).PhysRange S r) :
    closure (Set.range (vecDG S hS W hD hpos hcube τ hphys))
      = closure (Set.range (fun Q : MarginMonoDG G D τ r =>
          gvecTG S hS (energy0G S W D hD) (uniformBoundFG_energy0G S hS W hD hpos hcube) τ
            (posPreserving_of_physRangeG S (energy0G S W D hD) hphys τ) Q.1)) := by
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨P, rfl⟩
    refine mem_closure_of_tendsto (tendsto_vecDG S hS W hD hpos hcube ht hC0 hU τ hphys P)
      (Eventually.of_forall (fun R => ⟨⟨cutMG R P.1, fun i => P.2 i⟩, rfl⟩))
  · rintro _ ⟨Q, rfl⟩
    exact ⟨ofMarginDG Q, vecDG_ofMarginDG S hS W hD hpos hcube ht hC0 hU τ hphys Q⟩

end Compact

/-! ## 6. The linked structure over a schedule -/

section Linked

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The observer over a schedule of `G` inhabits `OSDataSLinkedG`.** Inputs: those of
`ObserverOSG.observerOSDataSG` and the class moments. `SM = schwSFMG`, `vec = vecDG`,
`cvec = gvecTG`.

DERIVED: `0` the signs and the reference step; `1` the top of `ρ`; `4` the dimension. -/
def observerOSDataSLinkedG (S : Sched G) (hS : SchedOS S) (hsh : SchedShiftInv S)
    (W : ConfFlowG G) {D : Set (LField G)}
    (hD : ∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBoundG S W O) {t C : ℝ}
    (ht : 0 < t) (hC0 : 0 ≤ C) (hU : ClassMomentsG S W D t C)
    {O : LField G} (hO : O ∈ D) (h : UnitCubeExpBoundG S W O) (τ : Fin 4)
    {r : ℝ} (hphys : (energy0G S W D hD).PhysRange S r) (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG S hS (energy0G S W D hD)
      (uniformBoundFG_energy0G S hS W hD hpos hcube) τ hphys m0) ρ)
    (hNT : FlowConnectedNonzeroG S (energy0G S W D hD) τ r) : OSDataSLinkedG G D τ r where
  base := observerOSDataSG S hS hsh W hD hpos hcube hO h τ hphys m0 hL hρ0 hρ1 hg hNT
  SM := fun O g => schwSFMG S W D O g
  O := O
  S_eq := fun n φ => by
    show schwCMLG S hsh W hpos hO h n φ
      = schwSFMG S W D (fun _ : Fin n => O) (fun i => ofE4 (φ i))
    rw [schwCMLG_apply]
    exact schwSFG_eq_schwSFMG S W hpos ht hC0 hU hO _
  vec := vecDG S hS W hD hpos hcube τ hphys
  inner_vec := inner_vecDG S hS W hD hpos hcube ht hC0 hU τ hphys
  cvec := fun Q => gvecTG S hS (energy0G S W D hD) (uniformBoundFG_energy0G S hS W hD hpos hcube) τ
    (posPreserving_of_physRangeG S (energy0G S W D hD) hphys τ) Q.1
  vec_compact := vecDG_ofMarginDG S hS W hD hpos hcube ht hC0 hU τ hphys
  closure_eq := closure_range_vecDG S hS W hD hpos hcube ht hC0 hU τ hphys

/-- The observer's linked data over `G`: the inner products of the decaying vectors are the
extended kernel of the reflected pairs.

DERIVED: no numeral. -/
theorem observerOSDataSLinkedG_inner (S : Sched G) (hS : SchedOS S) (hsh : SchedShiftInv S)
    (W : ConfFlowG G) {D : Set (LField G)}
    (hD : ∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBoundG S W O) {t C : ℝ}
    (ht : 0 < t) (hC0 : 0 ≤ C) (hU : ClassMomentsG S W D t C)
    {O : LField G} (hO : O ∈ D) (h : UnitCubeExpBoundG S W O) (τ : Fin 4)
    {r : ℝ} (hphys : (energy0G S W D hD).PhysRange S r) (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG S hS (energy0G S W D hD)
      (uniformBoundFG_energy0G S hS W hD hpos hcube) τ hphys m0) ρ)
    (hNT : FlowConnectedNonzeroG S (energy0G S W D hD) τ r) (P Q : DMarginMonoDG G D τ r) :
    let X := observerOSDataSLinkedG S hS hsh W hD hpos hcube ht hC0 hU hO h τ hphys m0 hL hρ0 hρ1
      hg hNT
    inner ℂ (X.vec P) (X.vec Q) = (kernSG S W D τ P.1.1 Q.1.1 : ℂ) :=
  (observerOSDataSLinkedG S hS hsh W hD hpos hcube ht hC0 hU hO h τ hphys m0 hL hρ0 hρ1 hg
    hNT).inner_vec P Q

end Linked

/-! ## 7. The observer at the symmetrised plaquette field, at the canonical schedule -/

section Observer

open MassGap.SymPlaqG

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  [GaugeSimple G]

/-- (E) on the symmetrised class at the canonical schedule, from (E) on the plaquette class and an
axis-covariant flow (`SymPlaqG.symPlaqG_cube`, `AxisInvG.schedAxisInv_canonSched`).

DERIVED: no numeral. -/
theorem symPlaqG_cube_canon (W : ConfFlowG G)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : IConf G),
      W.V k (MassGap.ContinuumHypercubic.iaxisConf e U)
        = MassGap.ContinuumHypercubic.iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClassG G, CubeMomentBoundG (canonSched G) W O) :
    ∀ O ∈ SymPlaqClassG G, CubeMomentBoundG (canonSched G) W O :=
  symPlaqG_cube (canonSched G) MassGap.AxisInvG.schedAxisInv_canonSched W hW hcube

/-- **The observer over `G` at the field `symG (plaqFieldG q0)`**, at `canonSched G`, the plane
`τ = 0` and the step `0`, with the transfer gap `hg` at a rate `0 < ρ < 1` as an input.

DERIVED: `0` the plane and the step; `1` the window. -/
def obsXG (W : ConfFlowG G)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : IConf G),
      W.V k (MassGap.ContinuumHypercubic.iaxisConf e U)
        = MassGap.ContinuumHypercubic.iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClassG G, CubeMomentBoundG (canonSched G) W O) {t C : ℝ} (ht : 0 < t)
    (hC0 : 0 ≤ C) (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C)
    (hUE : UnitCubeExpBoundG (canonSched G) W (symG (plaqFieldG ObserverEnergyMoments.q0)))
    {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    (hNT : FlowConnectedNonzeroG (canonSched G)
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)) 0 r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (uniformBoundFG_energy0G (canonSched G) schedOS_canonSched W (symPlaqG_refl G)
        symPlaqG_nonneg (symPlaqG_cube_canon W hW hcube)) 0 hphys 0) ρ) :
    OSDataSLinkedG G (SymPlaqClassG G) 0 r :=
  observerOSDataSLinkedG (canonSched G) schedOS_canonSched schedShiftInv_canonSched W
    (symPlaqG_refl G) symPlaqG_nonneg (symPlaqG_cube_canon W hW hcube) ht hC0 hU symPlaqG_q0 hUE
    0 hphys 0 one_pos hρ0 hρ1 hg hNT

/-- **The observer's functional is `schwSFMG`**, by definition.

DERIVED: no numeral. -/
theorem obsXG_SM (W : ConfFlowG G)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : IConf G),
      W.V k (MassGap.ContinuumHypercubic.iaxisConf e U)
        = MassGap.ContinuumHypercubic.iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClassG G, CubeMomentBoundG (canonSched G) W O) {t C : ℝ} (ht : 0 < t)
    (hC0 : 0 ≤ C) (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C)
    (hUE : UnitCubeExpBoundG (canonSched G) W (symG (plaqFieldG ObserverEnergyMoments.q0)))
    {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    (hNT : FlowConnectedNonzeroG (canonSched G)
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)) 0 r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (uniformBoundFG_energy0G (canonSched G) schedOS_canonSched W (symPlaqG_refl G)
        symPlaqG_nonneg (symPlaqG_cube_canon W hW hcube)) 0 hphys 0) ρ) :
    ∀ (ι : Type) [Fintype ι] (O : ι → LField G) (g : ι → Decaying),
      (obsXG W hW hcube ht hC0 hU hUE hphys hNT hρ0 hρ1 hg).SM O g
        = schwSFMG (canonSched G) W (SymPlaqClassG G) O g :=
  fun _ _ _ _ => rfl

/-- **The observer carries its Hilbert space**: `v = gvecTG` (`obsGenG_flow`).

DERIVED: `0` the plane. -/
theorem obsXG_obsGen (W : ConfFlowG G)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : IConf G),
      W.V k (MassGap.ContinuumHypercubic.iaxisConf e U)
        = MassGap.ContinuumHypercubic.iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClassG G, CubeMomentBoundG (canonSched G) W O) {t C : ℝ} (ht : 0 < t)
    (hC0 : 0 ≤ C) (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C)
    (hUE : UnitCubeExpBoundG (canonSched G) W (symG (plaqFieldG ObserverEnergyMoments.q0)))
    {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    (hNT : FlowConnectedNonzeroG (canonSched G)
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)) 0 r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (uniformBoundFG_energy0G (canonSched G) schedOS_canonSched W (symPlaqG_refl G)
        symPlaqG_nonneg (symPlaqG_cube_canon W hW hcube)) 0 hphys 0) ρ) :
    MassGap.ClayStatementG.ObsGenG (canonSched G) W (SymPlaqClassG G)
      (obsXG W hW hcube ht hC0 hU hUE hphys hNT hρ0 hρ1 hg) :=
  ⟨gvecTG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (uniformBoundFG_energy0G (canonSched G) schedOS_canonSched W (symPlaqG_refl G)
        symPlaqG_nonneg (symPlaqG_cube_canon W hW hcube)) 0
      (posPreserving_of_physRangeG (canonSched G)
        (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)) hphys 0),
    fun _ => rfl, obsGenG_flow (canonSched G) schedOS_canonSched W (symPlaqG_refl G)
      (uniformBoundFG_energy0G (canonSched G) schedOS_canonSched W (symPlaqG_refl G)
        symPlaqG_nonneg (symPlaqG_cube_canon W hW hcube)) 0
      (posPreserving_of_physRangeG (canonSched G)
        (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)) hphys 0)⟩

/-- **The observer's field is `symG (plaqFieldG q0)`**, by definition.

DERIVED: no numeral. -/
theorem obsXG_O (W : ConfFlowG G)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : IConf G),
      W.V k (MassGap.ContinuumHypercubic.iaxisConf e U)
        = MassGap.ContinuumHypercubic.iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClassG G, CubeMomentBoundG (canonSched G) W O) {t C : ℝ} (ht : 0 < t)
    (hC0 : 0 ≤ C) (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C)
    (hUE : UnitCubeExpBoundG (canonSched G) W (symG (plaqFieldG ObserverEnergyMoments.q0)))
    {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    (hNT : FlowConnectedNonzeroG (canonSched G)
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)) 0 r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (uniformBoundFG_energy0G (canonSched G) schedOS_canonSched W (symPlaqG_refl G)
        symPlaqG_nonneg (symPlaqG_cube_canon W hW hcube)) 0 hphys 0) ρ) :
    (obsXG W hW hcube ht hC0 hU hUE hphys hNT hρ0 hρ1 hg).O
      = symG (plaqFieldG ObserverEnergyMoments.q0) :=
  rfl

/-- **The observer's time translations have a self-adjoint generator**
(`ObserverOSG.observerOSDataSG_isSelfAdjoint`).

DERIVED: `0` the plane and the reference step. -/
theorem obsXG_sa (W : ConfFlowG G)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : IConf G),
      W.V k (MassGap.ContinuumHypercubic.iaxisConf e U)
        = MassGap.ContinuumHypercubic.iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClassG G, CubeMomentBoundG (canonSched G) W O) {t C : ℝ} (ht : 0 < t)
    (hC0 : 0 ≤ C) (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C)
    (hUE : UnitCubeExpBoundG (canonSched G) W (symG (plaqFieldG ObserverEnergyMoments.q0)))
    {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    (hNT : FlowConnectedNonzeroG (canonSched G)
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)) 0 r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (uniformBoundFG_energy0G (canonSched G) schedOS_canonSched W (symPlaqG_refl G)
        symPlaqG_nonneg (symPlaqG_cube_canon W hW hcube)) 0 hphys 0) ρ) :
    IsSelfAdjoint (ClassHamiltonian.generator
      (obsXG W hW hcube ht hC0 hU hUE hphys hNT hρ0 hρ1 hg).base.time) :=
  observerOSDataSG_isSelfAdjoint (canonSched G) schedOS_canonSched schedShiftInv_canonSched W
    (symPlaqG_refl G) symPlaqG_nonneg (symPlaqG_cube_canon W hW hcube) symPlaqG_q0 hUE 0 hphys 0
    one_pos hρ0 hρ1 hg hNT

/-- **The Hamiltonian gap of the observer over `G`**, from its self-adjoint generator
(`ClayFull.hamiltonianGap_of_selfAdjoint`).

DERIVED: `0` the plane. -/
theorem obsXG_gap (W : ConfFlowG G)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : IConf G),
      W.V k (MassGap.ContinuumHypercubic.iaxisConf e U)
        = MassGap.ContinuumHypercubic.iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClassG G, CubeMomentBoundG (canonSched G) W O) {t C : ℝ} (ht : 0 < t)
    (hC0 : 0 ≤ C) (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C)
    (hUE : UnitCubeExpBoundG (canonSched G) W (symG (plaqFieldG ObserverEnergyMoments.q0)))
    {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    (hNT : FlowConnectedNonzeroG (canonSched G)
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)) 0 r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (uniformBoundFG_energy0G (canonSched G) schedOS_canonSched W (symPlaqG_refl G)
        symPlaqG_nonneg (symPlaqG_cube_canon W hW hcube)) 0 hphys 0) ρ) :
    MassGap.ClayFull.HamiltonianGap (obsXG W hW hcube ht hC0 hU hUE hphys hNT hρ0 hρ1 hg).base :=
  MassGap.ClayFull.hamiltonianGap_of_selfAdjoint _
    (obsXG_sa W hW hcube ht hC0 hU hUE hphys hNT hρ0 hρ1 hg)

end Observer

/-! ## 8. The capstone -/

section Capstone

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayTreeG
  MassGap.ClayStatementG MassGap.ClayWiring MassGap.ClayWiringG MassGap.EnergyBoundG
  MassGap.SymPlaqG Filter
open scoped Topology Matrix

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  [GaugeSimple G] [GaugeLie G]

/-- **`ClayStatementAtG G W (SymPlaqClassG G)` from the observer over `G`.**
`AxisInvG.clayStatementAtG_of_inputsG''''` at `τ = 0` with `X := obsXG …`; its inputs `hSM`
(`obsXG_SM`), `hsa` (`obsXG_sa`), `hXO` (`obsXG_O`), `hGen` (`obsXG_obsGen`) and `hCut`
(`tendsto_schwSFMG` under `hU`) are discharged. In their place: the class moments (`ht`, `hC0`, `hU`), one exponential moment of the
unit cube for `symG (plaqFieldG q0)` (`hUE`), a physical range (`hphys`), `FlowConnectedNonzeroG`
(`hNT`) and the transfer gap at step `0` (`hρ0`, `hρ1`, `hg`). Every other hypothesis is that of
`clayStatementAtG_of_inputsG''''`, with `X` read as `obsXG …`.

DERIVED: `0` the plane. -/
theorem clayStatementAtG_of_observer (W : ConfFlowG G)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : IConf G),
      W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClassG G, CubeMomentBoundG (canonSched G) W O) {t C₀ : ℝ} (ht : 0 < t)
    (hC0 : 0 ≤ C₀) (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C₀)
    (hUE : UnitCubeExpBoundG (canonSched G) W (symG (plaqFieldG ObserverEnergyMoments.q0)))
    {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    (hNT : FlowConnectedNonzeroG (canonSched G)
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)) 0 r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (uniformBoundFG_energy0G (canonSched G) schedOS_canonSched W (symPlaqG_refl G)
        symPlaqG_nonneg (symPlaqG_cube_canon W hW hcube)) 0 hphys 0) ρ)
    {B : Type} [Fintype B] [DecidableEq B] (op : B → LField G) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField G → ℝ) (hBC : BasisConvG (canonSched G) op Z)
    (hRie : CoefRiemann m) (b0 : B) (κ : ℝ) (htr : ∀ b, coefC m trC b = if b = b0 then κ else 0)
    (hop : op b0 = symG (plaqFieldG ObserverEnergyMoments.q0))
    (hZtie : Tendsto (fun k => κ * Z k (op b0) * (canonSched G).a k ^ 4) atTop
      (𝓝 (constsG G).cTr))
    (h0 : OS0OwnG (canonSched G) op Z)
    (hTC : TransContTG (canonSched G) (mixOfZG B op m Z))
    (hCov : TensorCovG (canonSched G) (mixOfZG B op m Z))
    (Gk : ℝ → ℝ) (hK : TwoPointKernelG (canonSched G) (mixOfZG B op m Z) Gk)
    (hAF : AFCoefficientG (constsG G) Gk)
    (hNG : NonGaussianTG (canonSched G) (mixOfZG B op m Z))
    (hND : TensorNondegG (canonSched G) (mixOfZG B op m Z))
    (w : TSep 0 → (obsXG W hW hcube ht hC0 hU hUE hphys hNT hρ0 hρ1 hg).base.H)
    (hL : LinkHSG (canonSched G) W (SymPlaqClassG G)
      (obsXG W hW hcube ht hC0 hU hUE hphys hNT hρ0 hρ1 hg) (mixOfZG B op m Z) w)
    (hnt : ∃ u ∈ HLsG (obsXG W hW hcube ht hC0 hU hUE hphys hNT hρ0 hρ1 hg) w,
      inner ℂ (obsXG W hW hcube ht hC0 hU hUE hphys hNT hρ0 hρ1 hg).base.vac u = 0 ∧ u ≠ 0)
    (C : CompositesG G)
    (wC : TSepG C.Ix 0 → (obsXG W hW hcube ht hC0 hU hUE hphys hNT hρ0 hρ1 hg).base.H)
    (hCT : ∃ (Mb : Idx4 → B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTieG (mixOfZG B op m Z) Mb Zc ∧ TopNormG (canonSched G) (constsG G) Zc)
    (hWard : WardTG (canonSched G) (mixOfZG B op m Z)) (hCD : CompDataG C)
    (hCO : CompOSG (canonSched G) C)
    (hLC : LinkCG (canonSched G) (obsXG W hW hcube ht hC0 hU hUE hphys hNT hρ0 hρ1 hg) C wC)
    (hTI : TInG (mixOfZG B op m Z) C (obsXG W hW hcube ht hC0 hU hUE hphys hNT hρ0 hρ1 hg) w
      wC) :
    ClayStatementAtG G W (SymPlaqClassG G) :=
  MassGap.AxisInvG.clayStatementAtG_of_inputsG'''' W
    (obsXG W hW hcube ht hC0 hU hUE hphys hNT hρ0 hρ1 hg)
    (obsXG_SM W hW hcube ht hC0 hU hUE hphys hNT hρ0 hρ1 hg)
    (obsXG_sa W hW hcube ht hC0 hU hUE hphys hNT hρ0 hρ1 hg)
    (obsXG_O W hW hcube ht hC0 hU hUE hphys hNT hρ0 hρ1 hg)
    op m Z hBC hRie b0 κ htr hop hZtie h0 hTC hCov Gk hK hAF hNG hND hW hcube
    (by
      intro ι _ O hO g
      exact tendsto_schwSFMG (canonSched G) W symPlaqG_nonneg ht hC0 hU O hO g)
    w hL hnt C wC hCT hWard hCD hCO hLC hTI
    (obsXG_obsGen W hW hcube ht hC0 hU hUE hphys hNT hρ0 hρ1 hg)

end Capstone

end MassGap.ObserverLinkedG

end

#print axioms MassGap.ObserverLinkedG.abs_contSFG_sub_le_M
#print axioms MassGap.ObserverLinkedG.tendsto_schwSFMG
#print axioms MassGap.ObserverLinkedG.tendsto_contSFG_approx
#print axioms MassGap.ObserverLinkedG.schwSFG_eq_schwSFMG
#print axioms MassGap.ObserverLinkedG.pairFamG_cutMG
#print axioms MassGap.ObserverLinkedG.exists_kern_cauchyG
#print axioms MassGap.ObserverLinkedG.tendsto_kernFG_cutMG
#print axioms MassGap.ObserverLinkedG.inner_gvecTG_eq
#print axioms MassGap.ObserverLinkedG.cauchySeq_cutVecG
#print axioms MassGap.ObserverLinkedG.tendsto_vecDG
#print axioms MassGap.ObserverLinkedG.inner_vecDG
#print axioms MassGap.ObserverLinkedG.vecDG_ofMarginDG
#print axioms MassGap.ObserverLinkedG.closure_range_vecDG
#print axioms MassGap.ObserverLinkedG.observerOSDataSLinkedG
#print axioms MassGap.ObserverLinkedG.observerOSDataSLinkedG_inner
#print axioms MassGap.ObserverLinkedG.symPlaqG_cube_canon
#print axioms MassGap.ObserverLinkedG.obsXG
#print axioms MassGap.ObserverLinkedG.obsXG_SM
#print axioms MassGap.ObserverLinkedG.obsXG_O
#print axioms MassGap.ObserverLinkedG.obsXG_sa
#print axioms MassGap.ObserverLinkedG.obsXG_gap
#print axioms MassGap.ObserverLinkedG.clayStatementAtG_of_observer
